-- Prove2me | solution 1 for syracuse_descends_range_1433536_1435536
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:42:10.930851+00:00
-- url     : https://prove2.me/submissions/676d5c45-6f30-498b-a867-70a378eb5d23

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


theorem B4841477 : Blo 1433536 4841477 := bbase (se 4 (by rfl) ⟨453888, by rfl⟩ : syracuseStep 4841477 = 907777) (by norm_num)
theorem B3227669 : Blo 1433536 3227669 := bbase (se 6 (by rfl) ⟨75648, by rfl⟩ : syracuseStep 3227669 = 151297) (by norm_num)
theorem B1613857 : Blo 1433536 1613857 := bbase (se 2 (by rfl) ⟨605196, by rfl⟩ : syracuseStep 1613857 = 1210393) (by norm_num)
theorem B1613893 : Blo 1433536 1613893 := bbase (se 4 (by rfl) ⟨151302, by rfl⟩ : syracuseStep 1613893 = 302605) (by norm_num)
theorem B3227741 : Blo 1433536 3227741 := bbase (se 3 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 3227741 = 1210403) (by norm_num)
theorem B1613929 : Blo 1433536 1613929 := bbase (se 2 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 1613929 = 1210447) (by norm_num)
theorem B1613965 : Blo 1433536 1613965 := bbase (se 3 (by rfl) ⟨302618, by rfl⟩ : syracuseStep 1613965 = 605237) (by norm_num)
theorem B1532045 : Blo 1433536 1532045 := bbase (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) (by norm_num)
theorem B3227813 : Blo 1433536 3227813 := bbase (se 4 (by rfl) ⟨302607, by rfl⟩ : syracuseStep 3227813 = 605215) (by norm_num)
theorem B1614001 : Blo 1433536 1614001 := bbase (se 2 (by rfl) ⟨605250, by rfl⟩ : syracuseStep 1614001 = 1210501) (by norm_num)
theorem B8282293 : Blo 1433536 8282293 := bbase (se 5 (by rfl) ⟨388232, by rfl⟩ : syracuseStep 8282293 = 776465) (by norm_num)
theorem B3629245 : Blo 1433536 3629245 := bbase (se 3 (by rfl) ⟨680483, by rfl⟩ : syracuseStep 3629245 = 1360967) (by norm_num)
theorem B11043029 : Blo 1433536 11043029 := bbase (se 7 (by rfl) ⟨129410, by rfl⟩ : syracuseStep 11043029 = 258821) (by norm_num)
theorem B1614037 : Blo 1433536 1614037 := bbase (se 7 (by rfl) ⟨18914, by rfl⟩ : syracuseStep 1614037 = 37829) (by norm_num)
theorem B3227885 : Blo 1433536 3227885 := bbase (se 3 (by rfl) ⟨605228, by rfl⟩ : syracuseStep 3227885 = 1210457) (by norm_num)
theorem B1614073 : Blo 1433536 1614073 := bbase (se 2 (by rfl) ⟨605277, by rfl⟩ : syracuseStep 1614073 = 1210555) (by norm_num)
theorem B3449101 : Blo 1433536 3449101 := bbase (se 3 (by rfl) ⟨646706, by rfl⟩ : syracuseStep 3449101 = 1293413) (by norm_num)
theorem B1614109 : Blo 1433536 1614109 := bbase (se 3 (by rfl) ⟨302645, by rfl⟩ : syracuseStep 1614109 = 605291) (by norm_num)
theorem B3629357 : Blo 1433536 3629357 := bbase (se 3 (by rfl) ⟨680504, by rfl⟩ : syracuseStep 3629357 = 1361009) (by norm_num)
theorem B3227957 : Blo 1433536 3227957 := bbase (se 5 (by rfl) ⟨151310, by rfl⟩ : syracuseStep 3227957 = 302621) (by norm_num)
theorem B1614145 : Blo 1433536 1614145 := bbase (se 2 (by rfl) ⟨605304, by rfl⟩ : syracuseStep 1614145 = 1210609) (by norm_num)
theorem B1532233 : Blo 1433536 1532233 := bbase (se 2 (by rfl) ⟨574587, by rfl⟩ : syracuseStep 1532233 = 1149175) (by norm_num)
theorem B1614181 : Blo 1433536 1614181 := bbase (se 4 (by rfl) ⟨151329, by rfl⟩ : syracuseStep 1614181 = 302659) (by norm_num)
theorem B1573237 : Blo 1433536 1573237 := bbase (se 5 (by rfl) ⟨73745, by rfl⟩ : syracuseStep 1573237 = 147491) (by norm_num)
theorem B3228029 : Blo 1433536 3228029 := bbase (se 3 (by rfl) ⟨605255, by rfl⟩ : syracuseStep 3228029 = 1210511) (by norm_num)
theorem B1614217 : Blo 1433536 1614217 := bbase (se 2 (by rfl) ⟨605331, by rfl⟩ : syracuseStep 1614217 = 1210663) (by norm_num)
theorem B1614253 : Blo 1433536 1614253 := bbase (se 3 (by rfl) ⟨302672, by rfl⟩ : syracuseStep 1614253 = 605345) (by norm_num)
theorem B4841909 : Blo 1433536 4841909 := bbase (se 5 (by rfl) ⟨226964, by rfl⟩ : syracuseStep 4841909 = 453929) (by norm_num)
theorem B3228101 : Blo 1433536 3228101 := bbase (se 4 (by rfl) ⟨302634, by rfl⟩ : syracuseStep 3228101 = 605269) (by norm_num)
theorem B1614289 : Blo 1433536 1614289 := bbase (se 2 (by rfl) ⟨605358, by rfl⟩ : syracuseStep 1614289 = 1210717) (by norm_num)
theorem B5816789 : Blo 1433536 5816789 := bbase (se 7 (by rfl) ⟨68165, by rfl⟩ : syracuseStep 5816789 = 136331) (by norm_num)
theorem B3629549 : Blo 1433536 3629549 := bbase (se 3 (by rfl) ⟨680540, by rfl⟩ : syracuseStep 3629549 = 1361081) (by norm_num)
theorem B5448181 : Blo 1433536 5448181 := bbase (se 5 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 5448181 = 510767) (by norm_num)
theorem B1614325 : Blo 1433536 1614325 := bbase (se 5 (by rfl) ⟨75671, by rfl⟩ : syracuseStep 1614325 = 151343) (by norm_num)
theorem B3228173 : Blo 1433536 3228173 := bbase (se 3 (by rfl) ⟨605282, by rfl⟩ : syracuseStep 3228173 = 1210565) (by norm_num)
theorem B1614361 : Blo 1433536 1614361 := bbase (se 2 (by rfl) ⟨605385, by rfl⟩ : syracuseStep 1614361 = 1210771) (by norm_num)
theorem B4596277 : Blo 1433536 4596277 := bbase (se 5 (by rfl) ⟨215450, by rfl⟩ : syracuseStep 4596277 = 430901) (by norm_num)
theorem B1614397 : Blo 1433536 1614397 := bbase (se 3 (by rfl) ⟨302699, by rfl⟩ : syracuseStep 1614397 = 605399) (by norm_num)
theorem B3064397 : Blo 1433536 3064397 := bbase (se 3 (by rfl) ⟨574574, by rfl⟩ : syracuseStep 3064397 = 1149149) (by norm_num)
theorem B3228245 : Blo 1433536 3228245 := bbase (se 8 (by rfl) ⟨18915, by rfl⟩ : syracuseStep 3228245 = 37831) (by norm_num)
theorem B1614433 : Blo 1433536 1614433 := bbase (se 2 (by rfl) ⟨605412, by rfl⟩ : syracuseStep 1614433 = 1210825) (by norm_num)
theorem B6898277 : Blo 1433536 6898277 := bbase (se 4 (by rfl) ⟨646713, by rfl⟩ : syracuseStep 6898277 = 1293427) (by norm_num)
theorem B1614469 : Blo 1433536 1614469 := bbase (se 4 (by rfl) ⟨151356, by rfl⟩ : syracuseStep 1614469 = 302713) (by norm_num)
theorem B3228317 : Blo 1433536 3228317 := bbase (se 3 (by rfl) ⟨605309, by rfl⟩ : syracuseStep 3228317 = 1210619) (by norm_num)
theorem B1614505 : Blo 1433536 1614505 := bbase (se 2 (by rfl) ⟨605439, by rfl⟩ : syracuseStep 1614505 = 1210879) (by norm_num)
theorem B10338997 : Blo 1433536 10338997 := bbase (se 5 (by rfl) ⟨484640, by rfl⟩ : syracuseStep 10338997 = 969281) (by norm_num)
theorem B1614541 : Blo 1433536 1614541 := bbase (se 3 (by rfl) ⟨302726, by rfl⟩ : syracuseStep 1614541 = 605453) (by norm_num)
theorem B7865045 : Blo 1433536 7865045 := bbase (se 7 (by rfl) ⟨92168, by rfl⟩ : syracuseStep 7865045 = 184337) (by norm_num)
theorem B2179813 : Blo 1433536 2179813 := bbase (se 4 (by rfl) ⟨204357, by rfl⟩ : syracuseStep 2179813 = 408715) (by norm_num)
theorem B3228389 : Blo 1433536 3228389 := bbase (se 4 (by rfl) ⟨302661, by rfl⟩ : syracuseStep 3228389 = 605323) (by norm_num)
theorem B1614577 : Blo 1433536 1614577 := bbase (se 2 (by rfl) ⟨605466, by rfl⟩ : syracuseStep 1614577 = 1210933) (by norm_num)
theorem B1614613 : Blo 1433536 1614613 := bbase (se 6 (by rfl) ⟨37842, by rfl⟩ : syracuseStep 1614613 = 75685) (by norm_num)
theorem B5448485 : Blo 1433536 5448485 := bbase (se 4 (by rfl) ⟨510795, by rfl⟩ : syracuseStep 5448485 = 1021591) (by norm_num)
theorem B3228461 : Blo 1433536 3228461 := bbase (se 3 (by rfl) ⟨605336, by rfl⟩ : syracuseStep 3228461 = 1210673) (by norm_num)
theorem B1614649 : Blo 1433536 1614649 := bbase (se 2 (by rfl) ⟨605493, by rfl⟩ : syracuseStep 1614649 = 1210987) (by norm_num)
theorem B3064637 : Blo 1433536 3064637 := bbase (se 3 (by rfl) ⟨574619, by rfl⟩ : syracuseStep 3064637 = 1149239) (by norm_num)
theorem B3629893 : Blo 1433536 3629893 := bbase (se 4 (by rfl) ⟨340302, by rfl⟩ : syracuseStep 3629893 = 680605) (by norm_num)
theorem B6128453 : Blo 1433536 6128453 := bbase (se 4 (by rfl) ⟨574542, by rfl⟩ : syracuseStep 6128453 = 1149085) (by norm_num)
theorem B7267157 : Blo 1433536 7267157 := bbase (se 9 (by rfl) ⟨21290, by rfl⟩ : syracuseStep 7267157 = 42581) (by norm_num)
theorem B1614685 : Blo 1433536 1614685 := bbase (se 3 (by rfl) ⟨302753, by rfl⟩ : syracuseStep 1614685 = 605507) (by norm_num)
theorem B4842341 : Blo 1433536 4842341 := bbase (se 4 (by rfl) ⟨453969, by rfl⟩ : syracuseStep 4842341 = 907939) (by norm_num)
theorem B8168309 : Blo 1433536 8168309 := bbase (se 5 (by rfl) ⟨382889, by rfl⟩ : syracuseStep 8168309 = 765779) (by norm_num)
theorem B3228533 : Blo 1433536 3228533 := bbase (se 5 (by rfl) ⟨151337, by rfl⟩ : syracuseStep 3228533 = 302675) (by norm_num)
theorem B1614721 : Blo 1433536 1614721 := bbase (se 2 (by rfl) ⟨605520, by rfl⟩ : syracuseStep 1614721 = 1211041) (by norm_num)
theorem B1614757 : Blo 1433536 1614757 := bbase (se 4 (by rfl) ⟨151383, by rfl⟩ : syracuseStep 1614757 = 302767) (by norm_num)
theorem B3630005 : Blo 1433536 3630005 := bbase (se 5 (by rfl) ⟨170156, by rfl⟩ : syracuseStep 3630005 = 340313) (by norm_num)
theorem B3228605 : Blo 1433536 3228605 := bbase (se 3 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 3228605 = 1210727) (by norm_num)
theorem B2909125 : Blo 1433536 2909125 := bbase (se 4 (by rfl) ⟨272730, by rfl⟩ : syracuseStep 2909125 = 545461) (by norm_num)
theorem B1614793 : Blo 1433536 1614793 := bbase (se 2 (by rfl) ⟨605547, by rfl⟩ : syracuseStep 1614793 = 1211095) (by norm_num)
theorem B15516629 : Blo 1433536 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B1614829 : Blo 1433536 1614829 := bbase (se 3 (by rfl) ⟨302780, by rfl⟩ : syracuseStep 1614829 = 605561) (by norm_num)
theorem B4596725 : Blo 1433536 4596725 := bbase (se 5 (by rfl) ⟨215471, by rfl⟩ : syracuseStep 4596725 = 430943) (by norm_num)
theorem B3228677 : Blo 1433536 3228677 := bbase (se 4 (by rfl) ⟨302688, by rfl⟩ : syracuseStep 3228677 = 605377) (by norm_num)
theorem B1614865 : Blo 1433536 1614865 := bbase (se 2 (by rfl) ⟨605574, by rfl⟩ : syracuseStep 1614865 = 1211149) (by norm_num)
theorem B6128693 : Blo 1433536 6128693 := bbase (se 5 (by rfl) ⟨287282, by rfl⟩ : syracuseStep 6128693 = 574565) (by norm_num)
theorem B1614901 : Blo 1433536 1614901 := bbase (se 5 (by rfl) ⟨75698, by rfl⟩ : syracuseStep 1614901 = 151397) (by norm_num)
theorem B3228749 : Blo 1433536 3228749 := bbase (se 3 (by rfl) ⟨605390, by rfl⟩ : syracuseStep 3228749 = 1210781) (by norm_num)
theorem B1614937 : Blo 1433536 1614937 := bbase (se 2 (by rfl) ⟨605601, by rfl⟩ : syracuseStep 1614937 = 1211203) (by norm_num)
theorem B3630197 : Blo 1433536 3630197 := bbase (se 5 (by rfl) ⟨170165, by rfl⟩ : syracuseStep 3630197 = 340331) (by norm_num)
theorem B1614973 : Blo 1433536 1614973 := bbase (se 3 (by rfl) ⟨302807, by rfl⟩ : syracuseStep 1614973 = 605615) (by norm_num)
theorem B6890629 : Blo 1433536 6890629 := bbase (se 4 (by rfl) ⟨645996, by rfl⟩ : syracuseStep 6890629 = 1291993) (by norm_num)
theorem B3228821 : Blo 1433536 3228821 := bbase (se 6 (by rfl) ⟨75675, by rfl⟩ : syracuseStep 3228821 = 151351) (by norm_num)
theorem B9192629 : Blo 1433536 9192629 := bbase (se 5 (by rfl) ⟨430904, by rfl⟩ : syracuseStep 9192629 = 861809) (by norm_num)
theorem B3228893 : Blo 1433536 3228893 := bbase (se 3 (by rfl) ⟨605417, by rfl⟩ : syracuseStep 3228893 = 1210835) (by norm_num)
theorem B7259381 : Blo 1433536 7259381 := bbase (se 5 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 7259381 = 680567) (by norm_num)
theorem B4842773 : Blo 1433536 4842773 := bbase (se 6 (by rfl) ⟨113502, by rfl⟩ : syracuseStep 4842773 = 227005) (by norm_num)
theorem B3228965 : Blo 1433536 3228965 := bbase (se 4 (by rfl) ⟨302715, by rfl⟩ : syracuseStep 3228965 = 605431) (by norm_num)
theorem B3065141 : Blo 1433536 3065141 := bbase (se 5 (by rfl) ⟨143678, by rfl⟩ : syracuseStep 3065141 = 287357) (by norm_num)
theorem B3065149 : Blo 1433536 3065149 := bbase (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) (by norm_num)
theorem B3229037 : Blo 1433536 3229037 := bbase (se 3 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 3229037 = 1210889) (by norm_num)
theorem B4973989 : Blo 1433536 4973989 := bbase (se 4 (by rfl) ⟨466311, by rfl⟩ : syracuseStep 4973989 = 932623) (by norm_num)
theorem B3229109 : Blo 1433536 3229109 := bbase (se 5 (by rfl) ⟨151364, by rfl⟩ : syracuseStep 3229109 = 302729) (by norm_num)
theorem B2909621 : Blo 1433536 2909621 := bbase (se 5 (by rfl) ⟨136388, by rfl⟩ : syracuseStep 2909621 = 272777) (by norm_num)
theorem B3630541 : Blo 1433536 3630541 := bbase (se 3 (by rfl) ⟨680726, by rfl⟩ : syracuseStep 3630541 = 1361453) (by norm_num)
theorem B3229181 : Blo 1433536 3229181 := bbase (se 3 (by rfl) ⟨605471, by rfl⟩ : syracuseStep 3229181 = 1210943) (by norm_num)
theorem B14714389 : Blo 1433536 14714389 := bbase (se 6 (by rfl) ⟨344868, by rfl⟩ : syracuseStep 14714389 = 689737) (by norm_num)
theorem B3630653 : Blo 1433536 3630653 := bbase (se 3 (by rfl) ⟨680747, by rfl⟩ : syracuseStep 3630653 = 1361495) (by norm_num)
theorem B3229253 : Blo 1433536 3229253 := bbase (se 4 (by rfl) ⟨302742, by rfl⟩ : syracuseStep 3229253 = 605485) (by norm_num)
theorem B3229325 : Blo 1433536 3229325 := bbase (se 3 (by rfl) ⟨605498, by rfl⟩ : syracuseStep 3229325 = 1210997) (by norm_num)
theorem B2762381 : Blo 1433536 2762381 := bbase (se 3 (by rfl) ⟨517946, by rfl⟩ : syracuseStep 2762381 = 1035893) (by norm_num)
theorem B4843205 : Blo 1433536 4843205 := bbase (se 4 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 4843205 = 908101) (by norm_num)
theorem B3229397 : Blo 1433536 3229397 := bbase (se 7 (by rfl) ⟨37844, by rfl⟩ : syracuseStep 3229397 = 75689) (by norm_num)
theorem B16574165 : Blo 1433536 16574165 := bbase (se 7 (by rfl) ⟨194228, by rfl⟩ : syracuseStep 16574165 = 388457) (by norm_num)
theorem B2721509 : Blo 1433536 2721509 := bbase (se 4 (by rfl) ⟨255141, by rfl⟩ : syracuseStep 2721509 = 510283) (by norm_num)
theorem B3630845 : Blo 1433536 3630845 := bbase (se 3 (by rfl) ⟨680783, by rfl⟩ : syracuseStep 3630845 = 1361567) (by norm_num)
theorem B3229469 : Blo 1433536 3229469 := bbase (se 3 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 3229469 = 1211051) (by norm_num)
theorem B3229541 : Blo 1433536 3229541 := bbase (se 4 (by rfl) ⟨302769, by rfl⟩ : syracuseStep 3229541 = 605539) (by norm_num)
theorem B3229613 : Blo 1433536 3229613 := bbase (se 3 (by rfl) ⟨605552, by rfl⟩ : syracuseStep 3229613 = 1211105) (by norm_num)
theorem B3229685 : Blo 1433536 3229685 := bbase (se 5 (by rfl) ⟨151391, by rfl⟩ : syracuseStep 3229685 = 302783) (by norm_num)
theorem B2041861 : Blo 1433536 2041861 := bbase (se 4 (by rfl) ⟨191424, by rfl⟩ : syracuseStep 2041861 = 382849) (by norm_num)
theorem B3229757 : Blo 1433536 3229757 := bbase (se 3 (by rfl) ⟨605579, by rfl⟩ : syracuseStep 3229757 = 1211159) (by norm_num)
theorem B3631189 : Blo 1433536 3631189 := bbase (se 8 (by rfl) ⟨21276, by rfl⟩ : syracuseStep 3631189 = 42553) (by norm_num)
theorem B33138773 : Blo 1433536 33138773 := bbase (se 8 (by rfl) ⟨194172, by rfl⟩ : syracuseStep 33138773 = 388345) (by norm_num)
theorem B4843637 : Blo 1433536 4843637 := bbase (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) (by norm_num)
theorem B3229829 : Blo 1433536 3229829 := bbase (se 4 (by rfl) ⟨302796, by rfl⟩ : syracuseStep 3229829 = 605593) (by norm_num)
theorem B3631301 : Blo 1433536 3631301 := bbase (se 4 (by rfl) ⟨340434, by rfl⟩ : syracuseStep 3631301 = 680869) (by norm_num)
theorem B3229901 : Blo 1433536 3229901 := bbase (se 3 (by rfl) ⟨605606, by rfl⟩ : syracuseStep 3229901 = 1211213) (by norm_num)
theorem B8726741 : Blo 1433536 8726741 := bbase (se 7 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 8726741 = 204533) (by norm_num)
theorem B3680549 : Blo 1433536 3680549 := bbase (se 4 (by rfl) ⟨345051, by rfl⟩ : syracuseStep 3680549 = 690103) (by norm_num)
theorem B3631493 : Blo 1433536 3631493 := bbase (se 4 (by rfl) ⟨340452, by rfl⟩ : syracuseStep 3631493 = 680905) (by norm_num)
theorem B2394541 : Blo 1433536 2394541 := bbase (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) (by norm_num)
theorem B2722261 : Blo 1433536 2722261 := bbase (se 7 (by rfl) ⟨31901, by rfl⟩ : syracuseStep 2722261 = 63803) (by norm_num)
theorem B7260677 : Blo 1433536 7260677 := bbase (se 4 (by rfl) ⟨680688, by rfl⟩ : syracuseStep 7260677 = 1361377) (by norm_num)
theorem B2296325 : Blo 1433536 2296325 := bbase (se 4 (by rfl) ⟨215280, by rfl⟩ : syracuseStep 2296325 = 430561) (by norm_num)
theorem B2419213 : Blo 1433536 2419213 := bbase (se 3 (by rfl) ⟨453602, by rfl⟩ : syracuseStep 2419213 = 907205) (by norm_num)
theorem B4844069 : Blo 1433536 4844069 := bbase (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) (by norm_num)
theorem B2042453 : Blo 1433536 2042453 := bbase (se 8 (by rfl) ⟨11967, by rfl⟩ : syracuseStep 2042453 = 23935) (by norm_num)
theorem B2419301 : Blo 1433536 2419301 := bbase (se 4 (by rfl) ⟨226809, by rfl⟩ : syracuseStep 2419301 = 453619) (by norm_num)
theorem B2722405 : Blo 1433536 2722405 := bbase (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) (by norm_num)
theorem B1722989 : Blo 1433536 1722989 := bbase (se 3 (by rfl) ⟨323060, by rfl⟩ : syracuseStep 1722989 = 646121) (by norm_num)
theorem B4082309 : Blo 1433536 4082309 := bbase (se 4 (by rfl) ⟨382716, by rfl⟩ : syracuseStep 4082309 = 765433) (by norm_num)
theorem B2296453 : Blo 1433536 2296453 := bbase (se 4 (by rfl) ⟨215292, by rfl⟩ : syracuseStep 2296453 = 430585) (by norm_num)
theorem B2042533 : Blo 1433536 2042533 := bbase (se 4 (by rfl) ⟨191487, by rfl⟩ : syracuseStep 2042533 = 382975) (by norm_num)
theorem B2296517 : Blo 1433536 2296517 := bbase (se 4 (by rfl) ⟨215298, by rfl⟩ : syracuseStep 2296517 = 430597) (by norm_num)
theorem B3631837 : Blo 1433536 3631837 := bbase (se 3 (by rfl) ⟨680969, by rfl⟩ : syracuseStep 3631837 = 1361939) (by norm_num)
theorem B2419429 : Blo 1433536 2419429 := bbase (se 4 (by rfl) ⟨226821, by rfl⟩ : syracuseStep 2419429 = 453643) (by norm_num)
theorem B2722565 : Blo 1433536 2722565 := bbase (se 4 (by rfl) ⟨255240, by rfl⟩ : syracuseStep 2722565 = 510481) (by norm_num)
theorem B2042653 : Blo 1433536 2042653 := bbase (se 3 (by rfl) ⟨382997, by rfl⟩ : syracuseStep 2042653 = 765995) (by norm_num)
theorem B2419517 : Blo 1433536 2419517 := bbase (se 3 (by rfl) ⟨453659, by rfl⟩ : syracuseStep 2419517 = 907319) (by norm_num)
theorem B3631949 : Blo 1433536 3631949 := bbase (se 3 (by rfl) ⟨680990, by rfl⟩ : syracuseStep 3631949 = 1361981) (by norm_num)
theorem B2583389 : Blo 1433536 2583389 := bbase (se 3 (by rfl) ⟨484385, by rfl⟩ : syracuseStep 2583389 = 968771) (by norm_num)
theorem B2042749 : Blo 1433536 2042749 := bbase (se 3 (by rfl) ⟨383015, by rfl⟩ : syracuseStep 2042749 = 766031) (by norm_num)
theorem B2722709 : Blo 1433536 2722709 := bbase (se 6 (by rfl) ⟨63813, by rfl⟩ : syracuseStep 2722709 = 127627) (by norm_num)
theorem B1723297 : Blo 1433536 1723297 := bbase (se 2 (by rfl) ⟨646236, by rfl⟩ : syracuseStep 1723297 = 1292473) (by norm_num)
theorem B2419645 : Blo 1433536 2419645 := bbase (se 3 (by rfl) ⟨453683, by rfl⟩ : syracuseStep 2419645 = 907367) (by norm_num)
theorem B4844501 : Blo 1433536 4844501 := bbase (se 7 (by rfl) ⟨56771, by rfl⟩ : syracuseStep 4844501 = 113543) (by norm_num)
theorem B1657849 : Blo 1433536 1657849 := bbase (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) (by norm_num)
theorem B3632141 : Blo 1433536 3632141 := bbase (se 3 (by rfl) ⟨681026, by rfl⟩ : syracuseStep 3632141 = 1362053) (by norm_num)
theorem B2419733 : Blo 1433536 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B10898549 : Blo 1433536 10898549 := bbase (se 5 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 10898549 = 1021739) (by norm_num)
theorem B2583677 : Blo 1433536 2583677 := bbase (se 3 (by rfl) ⟨484439, by rfl⟩ : syracuseStep 2583677 = 968879) (by norm_num)
theorem B2329733 : Blo 1433536 2329733 := bbase (se 4 (by rfl) ⟨218412, by rfl⟩ : syracuseStep 2329733 = 436825) (by norm_num)
theorem B2419861 : Blo 1433536 2419861 := bbase (se 6 (by rfl) ⟨56715, by rfl⟩ : syracuseStep 2419861 = 113431) (by norm_num)
theorem B2722997 : Blo 1433536 2722997 := bbase (se 5 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 2722997 = 255281) (by norm_num)
theorem B1453253 : Blo 1433536 1453253 := bbase (se 4 (by rfl) ⟨136242, by rfl⟩ : syracuseStep 1453253 = 272485) (by norm_num)
theorem B2419949 : Blo 1433536 2419949 := bbase (se 3 (by rfl) ⟨453740, by rfl⟩ : syracuseStep 2419949 = 907481) (by norm_num)
theorem B1723681 : Blo 1433536 1723681 := bbase (se 2 (by rfl) ⟨646380, by rfl⟩ : syracuseStep 1723681 = 1292761) (by norm_num)
theorem B1723685 : Blo 1433536 1723685 := bbase (se 4 (by rfl) ⟨161595, by rfl⟩ : syracuseStep 1723685 = 323191) (by norm_num)
theorem B6130981 : Blo 1433536 6130981 := bbase (se 4 (by rfl) ⟨574779, by rfl⟩ : syracuseStep 6130981 = 1149559) (by norm_num)
theorem B2723149 : Blo 1433536 2723149 := bbase (se 3 (by rfl) ⟨510590, by rfl⟩ : syracuseStep 2723149 = 1021181) (by norm_num)
theorem B3632485 : Blo 1433536 3632485 := bbase (se 4 (by rfl) ⟨340545, by rfl⟩ : syracuseStep 3632485 = 681091) (by norm_num)
theorem B2420077 : Blo 1433536 2420077 := bbase (se 3 (by rfl) ⟨453764, by rfl⟩ : syracuseStep 2420077 = 907529) (by norm_num)
theorem B2043245 : Blo 1433536 2043245 := bbase (se 3 (by rfl) ⟨383108, by rfl⟩ : syracuseStep 2043245 = 766217) (by norm_num)
theorem B4083061 : Blo 1433536 4083061 := bbase (se 5 (by rfl) ⟨191393, by rfl⟩ : syracuseStep 4083061 = 382787) (by norm_num)
theorem B6540677 : Blo 1433536 6540677 := bbase (se 4 (by rfl) ⟨613188, by rfl⟩ : syracuseStep 6540677 = 1226377) (by norm_num)
theorem B4844933 : Blo 1433536 4844933 := bbase (se 4 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 4844933 = 908425) (by norm_num)
theorem B4656533 : Blo 1433536 4656533 := bbase (se 6 (by rfl) ⟨109137, by rfl⟩ : syracuseStep 4656533 = 218275) (by norm_num)
theorem B2420165 : Blo 1433536 2420165 := bbase (se 4 (by rfl) ⟨226890, by rfl⟩ : syracuseStep 2420165 = 453781) (by norm_num)
theorem B3632597 : Blo 1433536 3632597 := bbase (se 7 (by rfl) ⟨42569, by rfl⟩ : syracuseStep 3632597 = 85139) (by norm_num)
theorem B10890773 : Blo 1433536 10890773 := bbase (se 6 (by rfl) ⟨255252, by rfl⟩ : syracuseStep 10890773 = 510505) (by norm_num)
theorem B5443109 : Blo 1433536 5443109 := bbase (se 4 (by rfl) ⟨510291, by rfl⟩ : syracuseStep 5443109 = 1020583) (by norm_num)
theorem B2420293 : Blo 1433536 2420293 := bbase (se 4 (by rfl) ⟨226902, by rfl⟩ : syracuseStep 2420293 = 453805) (by norm_num)
theorem B10333781 : Blo 1433536 10333781 := bbase (se 8 (by rfl) ⟨60549, by rfl⟩ : syracuseStep 10333781 = 121099) (by norm_num)
theorem B2723453 : Blo 1433536 2723453 := bbase (se 3 (by rfl) ⟨510647, by rfl⟩ : syracuseStep 2723453 = 1021295) (by norm_num)
theorem B3632789 : Blo 1433536 3632789 := bbase (se 6 (by rfl) ⟨85143, by rfl⟩ : syracuseStep 3632789 = 170287) (by norm_num)
theorem B2420381 : Blo 1433536 2420381 := bbase (se 3 (by rfl) ⟨453821, by rfl⟩ : syracuseStep 2420381 = 907643) (by norm_num)
theorem B1724089 : Blo 1433536 1724089 := bbase (se 2 (by rfl) ⟨646533, by rfl⟩ : syracuseStep 1724089 = 1293067) (by norm_num)
theorem B1453837 : Blo 1433536 1453837 := bbase (se 3 (by rfl) ⟨272594, by rfl⟩ : syracuseStep 1453837 = 545189) (by norm_num)
theorem B7261973 : Blo 1433536 7261973 := bbase (se 6 (by rfl) ⟨170202, by rfl⟩ : syracuseStep 7261973 = 340405) (by norm_num)
theorem B2420509 : Blo 1433536 2420509 := bbase (se 3 (by rfl) ⟨453845, by rfl⟩ : syracuseStep 2420509 = 907691) (by norm_num)
theorem B1453873 : Blo 1433536 1453873 := bbase (se 2 (by rfl) ⟨545202, by rfl⟩ : syracuseStep 1453873 = 1090405) (by norm_num)
theorem B1814329 : Blo 1433536 1814329 := bbase (se 2 (by rfl) ⟨680373, by rfl⟩ : syracuseStep 1814329 = 1360747) (by norm_num)
theorem B4140869 : Blo 1433536 4140869 := bbase (se 4 (by rfl) ⟨388206, by rfl⟩ : syracuseStep 4140869 = 776413) (by norm_num)
theorem B3878725 : Blo 1433536 3878725 := bbase (se 4 (by rfl) ⟨363630, by rfl⟩ : syracuseStep 3878725 = 727261) (by norm_num)
theorem B13782869 : Blo 1433536 13782869 := bbase (se 9 (by rfl) ⟨40379, by rfl⟩ : syracuseStep 13782869 = 80759) (by norm_num)
theorem B2420597 : Blo 1433536 2420597 := bbase (se 5 (by rfl) ⟨113465, by rfl⟩ : syracuseStep 2420597 = 226931) (by norm_num)
theorem B2043797 : Blo 1433536 2043797 := bbase (se 6 (by rfl) ⟨47901, by rfl⟩ : syracuseStep 2043797 = 95803) (by norm_num)
theorem B2150309 : Blo 1433536 2150309 := bbase (se 4 (by rfl) ⟨201591, by rfl⟩ : syracuseStep 2150309 = 403183) (by norm_num)
theorem B2150333 : Blo 1433536 2150333 := bbase (se 3 (by rfl) ⟨403187, by rfl⟩ : syracuseStep 2150333 = 806375) (by norm_num)
theorem B2150357 : Blo 1433536 2150357 := bbase (se 7 (by rfl) ⟨25199, by rfl⟩ : syracuseStep 2150357 = 50399) (by norm_num)
theorem B11636693 : Blo 1433536 11636693 := bbase (se 7 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 11636693 = 272735) (by norm_num)
theorem B1814501 : Blo 1433536 1814501 := bbase (se 4 (by rfl) ⟨170109, by rfl⟩ : syracuseStep 1814501 = 340219) (by norm_num)
theorem B2150381 : Blo 1433536 2150381 := bbase (se 3 (by rfl) ⟨403196, by rfl⟩ : syracuseStep 2150381 = 806393) (by norm_num)
theorem B2297837 : Blo 1433536 2297837 := bbase (se 3 (by rfl) ⟨430844, by rfl⟩ : syracuseStep 2297837 = 861689) (by norm_num)
theorem B3633133 : Blo 1433536 3633133 := bbase (se 3 (by rfl) ⟨681212, by rfl⟩ : syracuseStep 3633133 = 1362425) (by norm_num)
theorem B2420725 : Blo 1433536 2420725 := bbase (se 5 (by rfl) ⟨113471, by rfl⟩ : syracuseStep 2420725 = 226943) (by norm_num)
theorem B2150405 : Blo 1433536 2150405 := bbase (se 4 (by rfl) ⟨201600, by rfl⟩ : syracuseStep 2150405 = 403201) (by norm_num)
theorem B2150429 : Blo 1433536 2150429 := bbase (se 3 (by rfl) ⟨403205, by rfl⟩ : syracuseStep 2150429 = 806411) (by norm_num)
theorem B1814557 : Blo 1433536 1814557 := bbase (se 3 (by rfl) ⟨340229, by rfl⟩ : syracuseStep 1814557 = 680459) (by norm_num)
theorem B1617961 : Blo 1433536 1617961 := bbase (se 2 (by rfl) ⟨606735, by rfl⟩ : syracuseStep 1617961 = 1213471) (by norm_num)
theorem B2150453 : Blo 1433536 2150453 := bbase (se 5 (by rfl) ⟨100802, by rfl⟩ : syracuseStep 2150453 = 201605) (by norm_num)
theorem B2150477 : Blo 1433536 2150477 := bbase (se 3 (by rfl) ⟨403214, by rfl⟩ : syracuseStep 2150477 = 806429) (by norm_num)
theorem B2420813 : Blo 1433536 2420813 := bbase (se 3 (by rfl) ⟨453902, by rfl⟩ : syracuseStep 2420813 = 907805) (by norm_num)
theorem B3633245 : Blo 1433536 3633245 := bbase (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) (by norm_num)
theorem B2150501 : Blo 1433536 2150501 := bbase (se 4 (by rfl) ⟨201609, by rfl⟩ : syracuseStep 2150501 = 403219) (by norm_num)
theorem B2297965 : Blo 1433536 2297965 := bbase (se 3 (by rfl) ⟨430868, by rfl⟩ : syracuseStep 2297965 = 861737) (by norm_num)
theorem B2150525 : Blo 1433536 2150525 := bbase (se 3 (by rfl) ⟨403223, by rfl⟩ : syracuseStep 2150525 = 806447) (by norm_num)
theorem B1814653 : Blo 1433536 1814653 := bbase (se 3 (by rfl) ⟨340247, by rfl⟩ : syracuseStep 1814653 = 680495) (by norm_num)
theorem B2150549 : Blo 1433536 2150549 := bbase (se 6 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 2150549 = 100807) (by norm_num)
theorem B2150573 : Blo 1433536 2150573 := bbase (se 3 (by rfl) ⟨403232, by rfl⟩ : syracuseStep 2150573 = 806465) (by norm_num)
theorem B2150597 : Blo 1433536 2150597 := bbase (se 4 (by rfl) ⟨201618, by rfl⟩ : syracuseStep 2150597 = 403237) (by norm_num)
theorem B2420941 : Blo 1433536 2420941 := bbase (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) (by norm_num)
theorem B2150621 : Blo 1433536 2150621 := bbase (se 3 (by rfl) ⟨403241, by rfl⟩ : syracuseStep 2150621 = 806483) (by norm_num)
theorem B2150645 : Blo 1433536 2150645 := bbase (se 5 (by rfl) ⟨100811, by rfl⟩ : syracuseStep 2150645 = 201623) (by norm_num)
theorem B2584829 : Blo 1433536 2584829 := bbase (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) (by norm_num)
theorem B2150669 : Blo 1433536 2150669 := bbase (se 3 (by rfl) ⟨403250, by rfl⟩ : syracuseStep 2150669 = 806501) (by norm_num)
theorem B3633437 : Blo 1433536 3633437 := bbase (se 3 (by rfl) ⟨681269, by rfl⟩ : syracuseStep 3633437 = 1362539) (by norm_num)
theorem B2150693 : Blo 1433536 2150693 := bbase (se 4 (by rfl) ⟨201627, by rfl⟩ : syracuseStep 2150693 = 403255) (by norm_num)
theorem B2421029 : Blo 1433536 2421029 := bbase (se 4 (by rfl) ⟨226971, by rfl⟩ : syracuseStep 2421029 = 453943) (by norm_num)
theorem B1814825 : Blo 1433536 1814825 := bbase (se 2 (by rfl) ⟨680559, by rfl⟩ : syracuseStep 1814825 = 1361119) (by norm_num)
theorem B2150717 : Blo 1433536 2150717 := bbase (se 3 (by rfl) ⟨403259, by rfl⟩ : syracuseStep 2150717 = 806519) (by norm_num)
theorem B2584909 : Blo 1433536 2584909 := bbase (se 3 (by rfl) ⟨484670, by rfl⟩ : syracuseStep 2584909 = 969341) (by norm_num)
theorem B2150741 : Blo 1433536 2150741 := bbase (se 10 (by rfl) ⟨3150, by rfl⟩ : syracuseStep 2150741 = 6301) (by norm_num)
theorem B1814881 : Blo 1433536 1814881 := bbase (se 2 (by rfl) ⟨680580, by rfl⟩ : syracuseStep 1814881 = 1361161) (by norm_num)
theorem B2150765 : Blo 1433536 2150765 := bbase (se 3 (by rfl) ⟨403268, by rfl⟩ : syracuseStep 2150765 = 806537) (by norm_num)
theorem B2724205 : Blo 1433536 2724205 := bbase (se 3 (by rfl) ⟨510788, by rfl⟩ : syracuseStep 2724205 = 1021577) (by norm_num)
theorem B2150789 : Blo 1433536 2150789 := bbase (se 4 (by rfl) ⟨201636, by rfl⟩ : syracuseStep 2150789 = 403273) (by norm_num)
theorem B2150813 : Blo 1433536 2150813 := bbase (se 3 (by rfl) ⟨403277, by rfl⟩ : syracuseStep 2150813 = 806555) (by norm_num)
theorem B2421157 : Blo 1433536 2421157 := bbase (se 4 (by rfl) ⟨226983, by rfl⟩ : syracuseStep 2421157 = 453967) (by norm_num)
theorem B2150837 : Blo 1433536 2150837 := bbase (se 5 (by rfl) ⟨100820, by rfl⟩ : syracuseStep 2150837 = 201641) (by norm_num)
theorem B1814977 : Blo 1433536 1814977 := bbase (se 2 (by rfl) ⟨680616, by rfl⟩ : syracuseStep 1814977 = 1361233) (by norm_num)
theorem B6631877 : Blo 1433536 6631877 := bbase (se 4 (by rfl) ⟨621738, by rfl⟩ : syracuseStep 6631877 = 1243477) (by norm_num)
theorem B2150861 : Blo 1433536 2150861 := bbase (se 3 (by rfl) ⟨403286, by rfl⟩ : syracuseStep 2150861 = 806573) (by norm_num)
theorem B38302165 : Blo 1433536 38302165 := bbase (se 7 (by rfl) ⟨448853, by rfl⟩ : syracuseStep 38302165 = 897707) (by norm_num)
theorem B2150885 : Blo 1433536 2150885 := bbase (se 4 (by rfl) ⟨201645, by rfl⟩ : syracuseStep 2150885 = 403291) (by norm_num)
theorem B2150909 : Blo 1433536 2150909 := bbase (se 3 (by rfl) ⟨403295, by rfl⟩ : syracuseStep 2150909 = 806591) (by norm_num)
theorem B2421245 : Blo 1433536 2421245 := bbase (se 3 (by rfl) ⟨453983, by rfl⟩ : syracuseStep 2421245 = 907967) (by norm_num)
theorem B2724349 : Blo 1433536 2724349 := bbase (se 3 (by rfl) ⟨510815, by rfl⟩ : syracuseStep 2724349 = 1021631) (by norm_num)
theorem B2150933 : Blo 1433536 2150933 := bbase (se 6 (by rfl) ⟨50412, by rfl⟩ : syracuseStep 2150933 = 100825) (by norm_num)
theorem B2150957 : Blo 1433536 2150957 := bbase (se 3 (by rfl) ⟨403304, by rfl⟩ : syracuseStep 2150957 = 806609) (by norm_num)
theorem B2150981 : Blo 1433536 2150981 := bbase (se 4 (by rfl) ⟨201654, by rfl⟩ : syracuseStep 2150981 = 403309) (by norm_num)
theorem B24498773 : Blo 1433536 24498773 := bbase (se 8 (by rfl) ⟨143547, by rfl⟩ : syracuseStep 24498773 = 287095) (by norm_num)
theorem B2151005 : Blo 1433536 2151005 := bbase (se 3 (by rfl) ⟨403313, by rfl⟩ : syracuseStep 2151005 = 806627) (by norm_num)
theorem B1815149 : Blo 1433536 1815149 := bbase (se 3 (by rfl) ⟨340340, by rfl⟩ : syracuseStep 1815149 = 680681) (by norm_num)
theorem B2151029 : Blo 1433536 2151029 := bbase (se 5 (by rfl) ⟨100829, by rfl⟩ : syracuseStep 2151029 = 201659) (by norm_num)
theorem B2421373 : Blo 1433536 2421373 := bbase (se 3 (by rfl) ⟨454007, by rfl⟩ : syracuseStep 2421373 = 908015) (by norm_num)
theorem B2151053 : Blo 1433536 2151053 := bbase (se 3 (by rfl) ⟨403322, by rfl⟩ : syracuseStep 2151053 = 806645) (by norm_num)
theorem B2724509 : Blo 1433536 2724509 := bbase (se 3 (by rfl) ⟨510845, by rfl⟩ : syracuseStep 2724509 = 1021691) (by norm_num)
theorem B2151077 : Blo 1433536 2151077 := bbase (se 4 (by rfl) ⟨201663, by rfl⟩ : syracuseStep 2151077 = 403327) (by norm_num)
theorem B1815205 : Blo 1433536 1815205 := bbase (se 4 (by rfl) ⟨170175, by rfl⟩ : syracuseStep 1815205 = 340351) (by norm_num)
theorem B2151101 : Blo 1433536 2151101 := bbase (se 3 (by rfl) ⟨403331, by rfl⟩ : syracuseStep 2151101 = 806663) (by norm_num)
theorem B5444293 : Blo 1433536 5444293 := bbase (se 4 (by rfl) ⟨510402, by rfl⟩ : syracuseStep 5444293 = 1020805) (by norm_num)
theorem B2151125 : Blo 1433536 2151125 := bbase (se 7 (by rfl) ⟨25208, by rfl⟩ : syracuseStep 2151125 = 50417) (by norm_num)
theorem B2421461 : Blo 1433536 2421461 := bbase (se 7 (by rfl) ⟨28376, by rfl⟩ : syracuseStep 2421461 = 56753) (by norm_num)
theorem B2151149 : Blo 1433536 2151149 := bbase (se 3 (by rfl) ⟨403340, by rfl⟩ : syracuseStep 2151149 = 806681) (by norm_num)
theorem B1635061 : Blo 1433536 1635061 := bbase (se 5 (by rfl) ⟨76643, by rfl⟩ : syracuseStep 1635061 = 153287) (by norm_num)
theorem B2151173 : Blo 1433536 2151173 := bbase (se 4 (by rfl) ⟨201672, by rfl⟩ : syracuseStep 2151173 = 403345) (by norm_num)
theorem B1815301 : Blo 1433536 1815301 := bbase (se 4 (by rfl) ⟨170184, by rfl⟩ : syracuseStep 1815301 = 340369) (by norm_num)
theorem B3445517 : Blo 1433536 3445517 := bbase (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) (by norm_num)
theorem B3445525 : Blo 1433536 3445525 := bbase (se 6 (by rfl) ⟨80754, by rfl⟩ : syracuseStep 3445525 = 161509) (by norm_num)
theorem B2151197 : Blo 1433536 2151197 := bbase (se 3 (by rfl) ⟨403349, by rfl⟩ : syracuseStep 2151197 = 806699) (by norm_num)
theorem B2724653 : Blo 1433536 2724653 := bbase (se 3 (by rfl) ⟨510872, by rfl⟩ : syracuseStep 2724653 = 1021745) (by norm_num)
theorem B2151221 : Blo 1433536 2151221 := bbase (se 5 (by rfl) ⟨100838, by rfl⟩ : syracuseStep 2151221 = 201677) (by norm_num)
theorem B2151245 : Blo 1433536 2151245 := bbase (se 3 (by rfl) ⟨403358, by rfl⟩ : syracuseStep 2151245 = 806717) (by norm_num)
theorem B2421589 : Blo 1433536 2421589 := bbase (se 9 (by rfl) ⟨7094, by rfl⟩ : syracuseStep 2421589 = 14189) (by norm_num)
theorem B2151269 : Blo 1433536 2151269 := bbase (se 4 (by rfl) ⟨201681, by rfl⟩ : syracuseStep 2151269 = 403363) (by norm_num)
theorem B2151293 : Blo 1433536 2151293 := bbase (se 3 (by rfl) ⟨403367, by rfl⟩ : syracuseStep 2151293 = 806735) (by norm_num)
theorem B2151317 : Blo 1433536 2151317 := bbase (se 6 (by rfl) ⟨50421, by rfl⟩ : syracuseStep 2151317 = 100843) (by norm_num)
theorem B2298773 : Blo 1433536 2298773 := bbase (se 6 (by rfl) ⟨53877, by rfl⟩ : syracuseStep 2298773 = 107755) (by norm_num)
theorem B2151341 : Blo 1433536 2151341 := bbase (se 3 (by rfl) ⟨403376, by rfl⟩ : syracuseStep 2151341 = 806753) (by norm_num)
theorem B2421677 : Blo 1433536 2421677 := bbase (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) (by norm_num)
theorem B1815473 : Blo 1433536 1815473 := bbase (se 2 (by rfl) ⟨680802, by rfl⟩ : syracuseStep 1815473 = 1361605) (by norm_num)
theorem B2151365 : Blo 1433536 2151365 := bbase (se 4 (by rfl) ⟨201690, by rfl⟩ : syracuseStep 2151365 = 403381) (by norm_num)
theorem B31011797 : Blo 1433536 31011797 := bbase (se 7 (by rfl) ⟨363419, by rfl⟩ : syracuseStep 31011797 = 726839) (by norm_num)
theorem B3879893 : Blo 1433536 3879893 := bbase (se 7 (by rfl) ⟨45467, by rfl⟩ : syracuseStep 3879893 = 90935) (by norm_num)
theorem B2151389 : Blo 1433536 2151389 := bbase (se 3 (by rfl) ⟨403385, by rfl⟩ : syracuseStep 2151389 = 806771) (by norm_num)
theorem B1815529 : Blo 1433536 1815529 := bbase (se 2 (by rfl) ⟨680823, by rfl⟩ : syracuseStep 1815529 = 1361647) (by norm_num)
theorem B5444597 : Blo 1433536 5444597 := bbase (se 5 (by rfl) ⟨255215, by rfl⟩ : syracuseStep 5444597 = 510431) (by norm_num)
theorem B2151413 : Blo 1433536 2151413 := bbase (se 5 (by rfl) ⟨100847, by rfl⟩ : syracuseStep 2151413 = 201695) (by norm_num)
theorem B2151437 : Blo 1433536 2151437 := bbase (se 3 (by rfl) ⟨403394, by rfl⟩ : syracuseStep 2151437 = 806789) (by norm_num)
theorem B2151461 : Blo 1433536 2151461 := bbase (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) (by norm_num)
theorem B7263269 : Blo 1433536 7263269 := bbase (se 4 (by rfl) ⟨680931, by rfl⟩ : syracuseStep 7263269 = 1361863) (by norm_num)
theorem B2421805 : Blo 1433536 2421805 := bbase (se 3 (by rfl) ⟨454088, by rfl⟩ : syracuseStep 2421805 = 908177) (by norm_num)
theorem B4838453 : Blo 1433536 4838453 := bbase (se 5 (by rfl) ⟨226802, by rfl⟩ : syracuseStep 4838453 = 453605) (by norm_num)
theorem B2151485 : Blo 1433536 2151485 := bbase (se 3 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 2151485 = 806807) (by norm_num)
theorem B1815625 : Blo 1433536 1815625 := bbase (se 2 (by rfl) ⟨680859, by rfl⟩ : syracuseStep 1815625 = 1361719) (by norm_num)
theorem B2724941 : Blo 1433536 2724941 := bbase (se 3 (by rfl) ⟨510926, by rfl⟩ : syracuseStep 2724941 = 1021853) (by norm_num)
theorem B2151509 : Blo 1433536 2151509 := bbase (se 8 (by rfl) ⟨12606, by rfl⟩ : syracuseStep 2151509 = 25213) (by norm_num)
theorem B2151533 : Blo 1433536 2151533 := bbase (se 3 (by rfl) ⟨403412, by rfl⟩ : syracuseStep 2151533 = 806825) (by norm_num)
theorem B2151557 : Blo 1433536 2151557 := bbase (se 4 (by rfl) ⟨201708, by rfl⟩ : syracuseStep 2151557 = 403417) (by norm_num)
theorem B2421893 : Blo 1433536 2421893 := bbase (se 4 (by rfl) ⟨227052, by rfl⟩ : syracuseStep 2421893 = 454105) (by norm_num)
theorem B2151581 : Blo 1433536 2151581 := bbase (se 3 (by rfl) ⟨403421, by rfl⟩ : syracuseStep 2151581 = 806843) (by norm_num)
theorem B2151605 : Blo 1433536 2151605 := bbase (se 5 (by rfl) ⟨100856, by rfl⟩ : syracuseStep 2151605 = 201713) (by norm_num)
theorem B2299061 : Blo 1433536 2299061 := bbase (se 5 (by rfl) ⟨107768, by rfl⟩ : syracuseStep 2299061 = 215537) (by norm_num)
theorem B3880133 : Blo 1433536 3880133 := bbase (se 4 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 3880133 = 727525) (by norm_num)
theorem B2151629 : Blo 1433536 2151629 := bbase (se 3 (by rfl) ⟨403430, by rfl⟩ : syracuseStep 2151629 = 806861) (by norm_num)
theorem B2151653 : Blo 1433536 2151653 := bbase (se 4 (by rfl) ⟨201717, by rfl⟩ : syracuseStep 2151653 = 403435) (by norm_num)
theorem B2725093 : Blo 1433536 2725093 := bbase (se 4 (by rfl) ⟨255477, by rfl⟩ : syracuseStep 2725093 = 510955) (by norm_num)
theorem B1815797 : Blo 1433536 1815797 := bbase (se 5 (by rfl) ⟨85115, by rfl⟩ : syracuseStep 1815797 = 170231) (by norm_num)
theorem B2151677 : Blo 1433536 2151677 := bbase (se 3 (by rfl) ⟨403439, by rfl⟩ : syracuseStep 2151677 = 806879) (by norm_num)
theorem B2422021 : Blo 1433536 2422021 := bbase (se 4 (by rfl) ⟨227064, by rfl⟩ : syracuseStep 2422021 = 454129) (by norm_num)
theorem B2151701 : Blo 1433536 2151701 := bbase (se 6 (by rfl) ⟨50430, by rfl⟩ : syracuseStep 2151701 = 100861) (by norm_num)
theorem B4592933 : Blo 1433536 4592933 := bbase (se 4 (by rfl) ⟨430587, by rfl⟩ : syracuseStep 4592933 = 861175) (by norm_num)
theorem B2151725 : Blo 1433536 2151725 := bbase (se 3 (by rfl) ⟨403448, by rfl⟩ : syracuseStep 2151725 = 806897) (by norm_num)
theorem B1815853 : Blo 1433536 1815853 := bbase (se 3 (by rfl) ⟨340472, by rfl⟩ : syracuseStep 1815853 = 680945) (by norm_num)
theorem B1938757 : Blo 1433536 1938757 := bbase (se 4 (by rfl) ⟨181758, by rfl⟩ : syracuseStep 1938757 = 363517) (by norm_num)
theorem B2151749 : Blo 1433536 2151749 := bbase (se 4 (by rfl) ⟨201726, by rfl⟩ : syracuseStep 2151749 = 403453) (by norm_num)
theorem B13079893 : Blo 1433536 13079893 := bbase (se 14 (by rfl) ⟨1197, by rfl⟩ : syracuseStep 13079893 = 2395) (by norm_num)
theorem B2151773 : Blo 1433536 2151773 := bbase (se 3 (by rfl) ⟨403457, by rfl⟩ : syracuseStep 2151773 = 806915) (by norm_num)
theorem B2692445 : Blo 1433536 2692445 := bbase (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) (by norm_num)
theorem B2422109 : Blo 1433536 2422109 := bbase (se 3 (by rfl) ⟨454145, by rfl⟩ : syracuseStep 2422109 = 908291) (by norm_num)
theorem B2151797 : Blo 1433536 2151797 := bbase (se 5 (by rfl) ⟨100865, by rfl⟩ : syracuseStep 2151797 = 201731) (by norm_num)
theorem B2585989 : Blo 1433536 2585989 := bbase (se 4 (by rfl) ⟨242436, by rfl⟩ : syracuseStep 2585989 = 484873) (by norm_num)
theorem B2151821 : Blo 1433536 2151821 := bbase (se 3 (by rfl) ⟨403466, by rfl⟩ : syracuseStep 2151821 = 806933) (by norm_num)
theorem B1815949 : Blo 1433536 1815949 := bbase (se 3 (by rfl) ⟨340490, by rfl⟩ : syracuseStep 1815949 = 680981) (by norm_num)
theorem B2151845 : Blo 1433536 2151845 := bbase (se 4 (by rfl) ⟨201735, by rfl⟩ : syracuseStep 2151845 = 403471) (by norm_num)
theorem B2151869 : Blo 1433536 2151869 := bbase (se 3 (by rfl) ⟨403475, by rfl⟩ : syracuseStep 2151869 = 806951) (by norm_num)
theorem B8721877 : Blo 1433536 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B2151893 : Blo 1433536 2151893 := bbase (se 7 (by rfl) ⟨25217, by rfl⟩ : syracuseStep 2151893 = 50435) (by norm_num)
theorem B2586077 : Blo 1433536 2586077 := bbase (se 3 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 2586077 = 969779) (by norm_num)
theorem B2422237 : Blo 1433536 2422237 := bbase (se 3 (by rfl) ⟨454169, by rfl⟩ : syracuseStep 2422237 = 908339) (by norm_num)
theorem B4838885 : Blo 1433536 4838885 := bbase (se 4 (by rfl) ⟨453645, by rfl⟩ : syracuseStep 4838885 = 907291) (by norm_num)
theorem B2151917 : Blo 1433536 2151917 := bbase (se 3 (by rfl) ⟨403484, by rfl⟩ : syracuseStep 2151917 = 806969) (by norm_num)
theorem B2151941 : Blo 1433536 2151941 := bbase (se 4 (by rfl) ⟨201744, by rfl⟩ : syracuseStep 2151941 = 403489) (by norm_num)
theorem B2151965 : Blo 1433536 2151965 := bbase (se 3 (by rfl) ⟨403493, by rfl⟩ : syracuseStep 2151965 = 806987) (by norm_num)
theorem B2151989 : Blo 1433536 2151989 := bbase (se 5 (by rfl) ⟨100874, by rfl⟩ : syracuseStep 2151989 = 201749) (by norm_num)
theorem B2422325 : Blo 1433536 2422325 := bbase (se 5 (by rfl) ⟨113546, by rfl⟩ : syracuseStep 2422325 = 227093) (by norm_num)
theorem B1816121 : Blo 1433536 1816121 := bbase (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) (by norm_num)
theorem B2152013 : Blo 1433536 2152013 := bbase (se 3 (by rfl) ⟨403502, by rfl⟩ : syracuseStep 2152013 = 807005) (by norm_num)
theorem B2152037 : Blo 1433536 2152037 := bbase (se 4 (by rfl) ⟨201753, by rfl⟩ : syracuseStep 2152037 = 403507) (by norm_num)
theorem B1816177 : Blo 1433536 1816177 := bbase (se 2 (by rfl) ⟨681066, by rfl⟩ : syracuseStep 1816177 = 1362133) (by norm_num)
theorem B2152061 : Blo 1433536 2152061 := bbase (se 3 (by rfl) ⟨403511, by rfl⟩ : syracuseStep 2152061 = 807023) (by norm_num)
theorem B2152085 : Blo 1433536 2152085 := bbase (se 6 (by rfl) ⟨50439, by rfl⟩ : syracuseStep 2152085 = 100879) (by norm_num)
theorem B2152109 : Blo 1433536 2152109 := bbase (se 3 (by rfl) ⟨403520, by rfl⟩ : syracuseStep 2152109 = 807041) (by norm_num)
theorem B2422453 : Blo 1433536 2422453 := bbase (se 5 (by rfl) ⟨113552, by rfl⟩ : syracuseStep 2422453 = 227105) (by norm_num)
theorem B2152133 : Blo 1433536 2152133 := bbase (se 4 (by rfl) ⟨201762, by rfl⟩ : syracuseStep 2152133 = 403525) (by norm_num)
theorem B1816273 : Blo 1433536 1816273 := bbase (se 2 (by rfl) ⟨681102, by rfl⟩ : syracuseStep 1816273 = 1362205) (by norm_num)
theorem B2152157 : Blo 1433536 2152157 := bbase (se 3 (by rfl) ⟨403529, by rfl⟩ : syracuseStep 2152157 = 807059) (by norm_num)
theorem B3495653 : Blo 1433536 3495653 := bbase (se 4 (by rfl) ⟨327717, by rfl⟩ : syracuseStep 3495653 = 655435) (by norm_num)
theorem B2152181 : Blo 1433536 2152181 := bbase (se 5 (by rfl) ⟨100883, by rfl⟩ : syracuseStep 2152181 = 201767) (by norm_num)
theorem B3446525 : Blo 1433536 3446525 := bbase (se 3 (by rfl) ⟨646223, by rfl⟩ : syracuseStep 3446525 = 1292447) (by norm_num)
theorem B2152205 : Blo 1433536 2152205 := bbase (se 3 (by rfl) ⟨403538, by rfl⟩ : syracuseStep 2152205 = 807077) (by norm_num)
theorem B2152229 : Blo 1433536 2152229 := bbase (se 4 (by rfl) ⟨201771, by rfl⟩ : syracuseStep 2152229 = 403543) (by norm_num)
theorem B2152253 : Blo 1433536 2152253 := bbase (se 3 (by rfl) ⟨403547, by rfl⟩ : syracuseStep 2152253 = 807095) (by norm_num)
theorem B2152277 : Blo 1433536 2152277 := bbase (se 9 (by rfl) ⟨6305, by rfl⟩ : syracuseStep 2152277 = 12611) (by norm_num)
theorem B2152301 : Blo 1433536 2152301 := bbase (se 3 (by rfl) ⟨403556, by rfl⟩ : syracuseStep 2152301 = 807113) (by norm_num)
theorem B1816445 : Blo 1433536 1816445 := bbase (se 3 (by rfl) ⟨340583, by rfl⟩ : syracuseStep 1816445 = 681167) (by norm_num)
theorem B2152325 : Blo 1433536 2152325 := bbase (se 4 (by rfl) ⟨201780, by rfl⟩ : syracuseStep 2152325 = 403561) (by norm_num)
theorem B4839317 : Blo 1433536 4839317 := bbase (se 6 (by rfl) ⟨113421, by rfl⟩ : syracuseStep 4839317 = 226843) (by norm_num)
theorem B2152349 : Blo 1433536 2152349 := bbase (se 3 (by rfl) ⟨403565, by rfl⟩ : syracuseStep 2152349 = 807131) (by norm_num)
theorem B3225509 : Blo 1433536 3225509 := bbase (se 4 (by rfl) ⟨302391, by rfl⟩ : syracuseStep 3225509 = 604783) (by norm_num)
theorem B2152373 : Blo 1433536 2152373 := bbase (se 5 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 2152373 = 201785) (by norm_num)
theorem B1816501 : Blo 1433536 1816501 := bbase (se 5 (by rfl) ⟨85148, by rfl⟩ : syracuseStep 1816501 = 170297) (by norm_num)
theorem B2152397 : Blo 1433536 2152397 := bbase (se 3 (by rfl) ⟨403574, by rfl⟩ : syracuseStep 2152397 = 807149) (by norm_num)
theorem B2586581 : Blo 1433536 2586581 := bbase (se 7 (by rfl) ⟨30311, by rfl⟩ : syracuseStep 2586581 = 60623) (by norm_num)
theorem B2152421 : Blo 1433536 2152421 := bbase (se 4 (by rfl) ⟨201789, by rfl⟩ : syracuseStep 2152421 = 403579) (by norm_num)
theorem B3225581 : Blo 1433536 3225581 := bbase (se 3 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 3225581 = 1209593) (by norm_num)
theorem B2152445 : Blo 1433536 2152445 := bbase (se 3 (by rfl) ⟨403583, by rfl⟩ : syracuseStep 2152445 = 807167) (by norm_num)
theorem B2152469 : Blo 1433536 2152469 := bbase (se 6 (by rfl) ⟨50448, by rfl⟩ : syracuseStep 2152469 = 100897) (by norm_num)
theorem B1816597 : Blo 1433536 1816597 := bbase (se 6 (by rfl) ⟨42576, by rfl⟩ : syracuseStep 1816597 = 85153) (by norm_num)
theorem B2152493 : Blo 1433536 2152493 := bbase (se 3 (by rfl) ⟨403592, by rfl⟩ : syracuseStep 2152493 = 807185) (by norm_num)
theorem B3225653 : Blo 1433536 3225653 := bbase (se 5 (by rfl) ⟨151202, by rfl⟩ : syracuseStep 3225653 = 302405) (by norm_num)
theorem B2619461 : Blo 1433536 2619461 := bbase (se 4 (by rfl) ⟨245574, by rfl⟩ : syracuseStep 2619461 = 491149) (by norm_num)
theorem B2152517 : Blo 1433536 2152517 := bbase (se 4 (by rfl) ⟨201798, by rfl⟩ : syracuseStep 2152517 = 403597) (by norm_num)
theorem B2152541 : Blo 1433536 2152541 := bbase (se 3 (by rfl) ⟨403601, by rfl⟩ : syracuseStep 2152541 = 807203) (by norm_num)
theorem B2152565 : Blo 1433536 2152565 := bbase (se 5 (by rfl) ⟨100901, by rfl⟩ : syracuseStep 2152565 = 201803) (by norm_num)
theorem B3225725 : Blo 1433536 3225725 := bbase (se 3 (by rfl) ⟨604823, by rfl⟩ : syracuseStep 3225725 = 1209647) (by norm_num)
theorem B2152589 : Blo 1433536 2152589 := bbase (se 3 (by rfl) ⟨403610, by rfl⟩ : syracuseStep 2152589 = 807221) (by norm_num)
theorem B4085909 : Blo 1433536 4085909 := bbase (se 6 (by rfl) ⟨95763, by rfl⟩ : syracuseStep 4085909 = 191527) (by norm_num)
theorem B2152613 : Blo 1433536 2152613 := bbase (se 4 (by rfl) ⟨201807, by rfl⟩ : syracuseStep 2152613 = 403615) (by norm_num)
theorem B2152637 : Blo 1433536 2152637 := bbase (se 3 (by rfl) ⟨403619, by rfl⟩ : syracuseStep 2152637 = 807239) (by norm_num)
theorem B1816769 : Blo 1433536 1816769 := bbase (se 2 (by rfl) ⟨681288, by rfl⟩ : syracuseStep 1816769 = 1362577) (by norm_num)
theorem B3225797 : Blo 1433536 3225797 := bbase (se 4 (by rfl) ⟨302418, by rfl⟩ : syracuseStep 3225797 = 604837) (by norm_num)
theorem B2152661 : Blo 1433536 2152661 := bbase (se 7 (by rfl) ⟨25226, by rfl⟩ : syracuseStep 2152661 = 50453) (by norm_num)
theorem B2152685 : Blo 1433536 2152685 := bbase (se 3 (by rfl) ⟨403628, by rfl⟩ : syracuseStep 2152685 = 807257) (by norm_num)
theorem B1816825 : Blo 1433536 1816825 := bbase (se 2 (by rfl) ⟨681309, by rfl⟩ : syracuseStep 1816825 = 1362619) (by norm_num)
theorem B5519621 : Blo 1433536 5519621 := bbase (se 4 (by rfl) ⟨517464, by rfl⟩ : syracuseStep 5519621 = 1034929) (by norm_num)
theorem B2152709 : Blo 1433536 2152709 := bbase (se 4 (by rfl) ⟨201816, by rfl⟩ : syracuseStep 2152709 = 403633) (by norm_num)
theorem B3225869 : Blo 1433536 3225869 := bbase (se 3 (by rfl) ⟨604850, by rfl⟩ : syracuseStep 3225869 = 1209701) (by norm_num)
theorem B2152733 : Blo 1433536 2152733 := bbase (se 3 (by rfl) ⟨403637, by rfl⟩ : syracuseStep 2152733 = 807275) (by norm_num)
theorem B7264565 : Blo 1433536 7264565 := bbase (se 5 (by rfl) ⟨340526, by rfl⟩ : syracuseStep 7264565 = 681053) (by norm_num)
theorem B2152757 : Blo 1433536 2152757 := bbase (se 5 (by rfl) ⟨100910, by rfl⟩ : syracuseStep 2152757 = 201821) (by norm_num)
theorem B2758981 : Blo 1433536 2758981 := bbase (se 4 (by rfl) ⟨258654, by rfl⟩ : syracuseStep 2758981 = 517309) (by norm_num)
theorem B4839749 : Blo 1433536 4839749 := bbase (se 4 (by rfl) ⟨453726, by rfl⟩ : syracuseStep 4839749 = 907453) (by norm_num)
theorem B2152781 : Blo 1433536 2152781 := bbase (se 3 (by rfl) ⟨403646, by rfl⟩ : syracuseStep 2152781 = 807293) (by norm_num)
theorem B3225941 : Blo 1433536 3225941 := bbase (se 10 (by rfl) ⟨4725, by rfl⟩ : syracuseStep 3225941 = 9451) (by norm_num)
theorem B2152805 : Blo 1433536 2152805 := bbase (se 4 (by rfl) ⟨201825, by rfl⟩ : syracuseStep 2152805 = 403651) (by norm_num)
theorem B2070893 : Blo 1433536 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B2152829 : Blo 1433536 2152829 := bbase (se 3 (by rfl) ⟨403655, by rfl⟩ : syracuseStep 2152829 = 807311) (by norm_num)
theorem B6207877 : Blo 1433536 6207877 := bbase (se 4 (by rfl) ⟨581988, by rfl⟩ : syracuseStep 6207877 = 1163977) (by norm_num)
theorem B2152853 : Blo 1433536 2152853 := bbase (se 6 (by rfl) ⟨50457, by rfl⟩ : syracuseStep 2152853 = 100915) (by norm_num)
theorem B3226013 : Blo 1433536 3226013 := bbase (se 3 (by rfl) ⟨604877, by rfl⟩ : syracuseStep 3226013 = 1209755) (by norm_num)
theorem B2152877 : Blo 1433536 2152877 := bbase (se 3 (by rfl) ⟨403664, by rfl⟩ : syracuseStep 2152877 = 807329) (by norm_num)
theorem B2152901 : Blo 1433536 2152901 := bbase (se 4 (by rfl) ⟨201834, by rfl⟩ : syracuseStep 2152901 = 403669) (by norm_num)
theorem B2152925 : Blo 1433536 2152925 := bbase (se 3 (by rfl) ⟨403673, by rfl⟩ : syracuseStep 2152925 = 807347) (by norm_num)
theorem B3062245 : Blo 1433536 3062245 := bbase (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) (by norm_num)
theorem B3226085 : Blo 1433536 3226085 := bbase (se 4 (by rfl) ⟨302445, by rfl⟩ : syracuseStep 3226085 = 604891) (by norm_num)
theorem B2152949 : Blo 1433536 2152949 := bbase (se 5 (by rfl) ⟨100919, by rfl⟩ : syracuseStep 2152949 = 201839) (by norm_num)
theorem B3447293 : Blo 1433536 3447293 := bbase (se 3 (by rfl) ⟨646367, by rfl⟩ : syracuseStep 3447293 = 1292735) (by norm_num)
theorem B2152973 : Blo 1433536 2152973 := bbase (se 3 (by rfl) ⟨403682, by rfl⟩ : syracuseStep 2152973 = 807365) (by norm_num)
theorem B2759197 : Blo 1433536 2759197 := bbase (se 3 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 2759197 = 1034699) (by norm_num)
theorem B2152997 : Blo 1433536 2152997 := bbase (se 4 (by rfl) ⟨201843, by rfl⟩ : syracuseStep 2152997 = 403687) (by norm_num)
theorem B3226157 : Blo 1433536 3226157 := bbase (se 3 (by rfl) ⟨604904, by rfl⟩ : syracuseStep 3226157 = 1209809) (by norm_num)
theorem B2153021 : Blo 1433536 2153021 := bbase (se 3 (by rfl) ⟨403691, by rfl⟩ : syracuseStep 2153021 = 807383) (by norm_num)
theorem B2153045 : Blo 1433536 2153045 := bbase (se 8 (by rfl) ⟨12615, by rfl⟩ : syracuseStep 2153045 = 25231) (by norm_num)
theorem B2153069 : Blo 1433536 2153069 := bbase (se 3 (by rfl) ⟨403700, by rfl⟩ : syracuseStep 2153069 = 807401) (by norm_num)
theorem B3226229 : Blo 1433536 3226229 := bbase (se 5 (by rfl) ⟨151229, by rfl⟩ : syracuseStep 3226229 = 302459) (by norm_num)
theorem B2153093 : Blo 1433536 2153093 := bbase (se 4 (by rfl) ⟨201852, by rfl⟩ : syracuseStep 2153093 = 403705) (by norm_num)
theorem B2153117 : Blo 1433536 2153117 := bbase (se 3 (by rfl) ⟨403709, by rfl⟩ : syracuseStep 2153117 = 807419) (by norm_num)
theorem B2153141 : Blo 1433536 2153141 := bbase (se 5 (by rfl) ⟨100928, by rfl⟩ : syracuseStep 2153141 = 201857) (by norm_num)
theorem B3226301 : Blo 1433536 3226301 := bbase (se 3 (by rfl) ⟨604931, by rfl⟩ : syracuseStep 3226301 = 1209863) (by norm_num)
theorem B5167813 : Blo 1433536 5167813 := bbase (se 4 (by rfl) ⟨484482, by rfl⟩ : syracuseStep 5167813 = 968965) (by norm_num)
theorem B2153165 : Blo 1433536 2153165 := bbase (se 3 (by rfl) ⟨403718, by rfl⟩ : syracuseStep 2153165 = 807437) (by norm_num)
theorem B4365013 : Blo 1433536 4365013 := bbase (se 7 (by rfl) ⟨51152, by rfl⟩ : syracuseStep 4365013 = 102305) (by norm_num)
theorem B2153189 : Blo 1433536 2153189 := bbase (se 4 (by rfl) ⟨201861, by rfl⟩ : syracuseStep 2153189 = 403723) (by norm_num)
theorem B4840181 : Blo 1433536 4840181 := bbase (se 5 (by rfl) ⟨226883, by rfl⟩ : syracuseStep 4840181 = 453767) (by norm_num)
theorem B2153213 : Blo 1433536 2153213 := bbase (se 3 (by rfl) ⟨403727, by rfl⟩ : syracuseStep 2153213 = 807455) (by norm_num)
theorem B3226373 : Blo 1433536 3226373 := bbase (se 4 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 3226373 = 604945) (by norm_num)
theorem B7363333 : Blo 1433536 7363333 := bbase (se 4 (by rfl) ⟨690312, by rfl⟩ : syracuseStep 7363333 = 1380625) (by norm_num)
theorem B2153237 : Blo 1433536 2153237 := bbase (se 6 (by rfl) ⟨50466, by rfl⟩ : syracuseStep 2153237 = 100933) (by norm_num)
theorem B2153261 : Blo 1433536 2153261 := bbase (se 3 (by rfl) ⟨403736, by rfl⟩ : syracuseStep 2153261 = 807473) (by norm_num)
theorem B2153285 : Blo 1433536 2153285 := bbase (se 4 (by rfl) ⟨201870, by rfl⟩ : syracuseStep 2153285 = 403741) (by norm_num)
theorem B3226445 : Blo 1433536 3226445 := bbase (se 3 (by rfl) ⟨604958, by rfl⟩ : syracuseStep 3226445 = 1209917) (by norm_num)
theorem B3103573 : Blo 1433536 3103573 := bbase (se 9 (by rfl) ⟨9092, by rfl⟩ : syracuseStep 3103573 = 18185) (by norm_num)
theorem B3226517 : Blo 1433536 3226517 := bbase (se 6 (by rfl) ⟨75621, by rfl⟩ : syracuseStep 3226517 = 151243) (by norm_num)
theorem B1612741 : Blo 1433536 1612741 := bbase (se 4 (by rfl) ⟨151194, by rfl⟩ : syracuseStep 1612741 = 302389) (by norm_num)
theorem B3226589 : Blo 1433536 3226589 := bbase (se 3 (by rfl) ⟨604985, by rfl⟩ : syracuseStep 3226589 = 1209971) (by norm_num)
theorem B1612777 : Blo 1433536 1612777 := bbase (se 2 (by rfl) ⟨604791, by rfl⟩ : syracuseStep 1612777 = 1209583) (by norm_num)
theorem B1612813 : Blo 1433536 1612813 := bbase (se 3 (by rfl) ⟨302402, by rfl⟩ : syracuseStep 1612813 = 604805) (by norm_num)
theorem B3226661 : Blo 1433536 3226661 := bbase (se 4 (by rfl) ⟨302499, by rfl⟩ : syracuseStep 3226661 = 604999) (by norm_num)
theorem B1612849 : Blo 1433536 1612849 := bbase (se 2 (by rfl) ⟨604818, by rfl⟩ : syracuseStep 1612849 = 1209637) (by norm_num)
theorem B5446709 : Blo 1433536 5446709 := bbase (se 5 (by rfl) ⟨255314, by rfl⟩ : syracuseStep 5446709 = 510629) (by norm_num)
theorem B1612885 : Blo 1433536 1612885 := bbase (se 8 (by rfl) ⟨9450, by rfl⟩ : syracuseStep 1612885 = 18901) (by norm_num)
theorem B6126677 : Blo 1433536 6126677 := bbase (se 8 (by rfl) ⟨35898, by rfl⟩ : syracuseStep 6126677 = 71797) (by norm_num)
theorem B3226733 : Blo 1433536 3226733 := bbase (se 3 (by rfl) ⟨605012, by rfl⟩ : syracuseStep 3226733 = 1210025) (by norm_num)
theorem B1612921 : Blo 1433536 1612921 := bbase (se 2 (by rfl) ⟨604845, by rfl⟩ : syracuseStep 1612921 = 1209691) (by norm_num)
theorem B16333973 : Blo 1433536 16333973 := bbase (se 6 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 16333973 = 765655) (by norm_num)
theorem B1612957 : Blo 1433536 1612957 := bbase (se 3 (by rfl) ⟨302429, by rfl⟩ : syracuseStep 1612957 = 604859) (by norm_num)
theorem B4840613 : Blo 1433536 4840613 := bbase (se 4 (by rfl) ⟨453807, by rfl⟩ : syracuseStep 4840613 = 907615) (by norm_num)
theorem B4594853 : Blo 1433536 4594853 := bbase (se 4 (by rfl) ⟨430767, by rfl⟩ : syracuseStep 4594853 = 861535) (by norm_num)
theorem B3226805 : Blo 1433536 3226805 := bbase (se 5 (by rfl) ⟨151256, by rfl⟩ : syracuseStep 3226805 = 302513) (by norm_num)
theorem B1612993 : Blo 1433536 1612993 := bbase (se 2 (by rfl) ⟨604872, by rfl⟩ : syracuseStep 1612993 = 1209745) (by norm_num)
theorem B55934165 : Blo 1433536 55934165 := bbase (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) (by norm_num)
theorem B1531105 : Blo 1433536 1531105 := bbase (se 2 (by rfl) ⟨574164, by rfl⟩ : syracuseStep 1531105 = 1148329) (by norm_num)
theorem B1613029 : Blo 1433536 1613029 := bbase (se 4 (by rfl) ⟨151221, by rfl⟩ : syracuseStep 1613029 = 302443) (by norm_num)
theorem B3226877 : Blo 1433536 3226877 := bbase (se 3 (by rfl) ⟨605039, by rfl⟩ : syracuseStep 3226877 = 1210079) (by norm_num)
theorem B1613065 : Blo 1433536 1613065 := bbase (se 2 (by rfl) ⟨604899, by rfl⟩ : syracuseStep 1613065 = 1209799) (by norm_num)
theorem B6896933 : Blo 1433536 6896933 := bbase (se 4 (by rfl) ⟨646587, by rfl⟩ : syracuseStep 6896933 = 1293175) (by norm_num)
theorem B1613101 : Blo 1433536 1613101 := bbase (se 3 (by rfl) ⟨302456, by rfl⟩ : syracuseStep 1613101 = 604913) (by norm_num)
theorem B4087093 : Blo 1433536 4087093 := bbase (se 5 (by rfl) ⟨191582, by rfl⟩ : syracuseStep 4087093 = 383165) (by norm_num)
theorem B3226949 : Blo 1433536 3226949 := bbase (se 4 (by rfl) ⟨302526, by rfl⟩ : syracuseStep 3226949 = 605053) (by norm_num)
theorem B1613137 : Blo 1433536 1613137 := bbase (se 2 (by rfl) ⟨604926, by rfl⟩ : syracuseStep 1613137 = 1209853) (by norm_num)
theorem B5446997 : Blo 1433536 5446997 := bbase (se 11 (by rfl) ⟨3989, by rfl⟩ : syracuseStep 5446997 = 7979) (by norm_num)
theorem B1531225 : Blo 1433536 1531225 := bbase (se 2 (by rfl) ⟨574209, by rfl⟩ : syracuseStep 1531225 = 1148419) (by norm_num)
theorem B3063133 : Blo 1433536 3063133 := bbase (se 3 (by rfl) ⟨574337, by rfl⟩ : syracuseStep 3063133 = 1148675) (by norm_num)
theorem B1613173 : Blo 1433536 1613173 := bbase (se 5 (by rfl) ⟨75617, by rfl⟩ : syracuseStep 1613173 = 151235) (by norm_num)
theorem B3227021 : Blo 1433536 3227021 := bbase (se 3 (by rfl) ⟨605066, by rfl⟩ : syracuseStep 3227021 = 1210133) (by norm_num)
theorem B1613209 : Blo 1433536 1613209 := bbase (se 2 (by rfl) ⟨604953, by rfl⟩ : syracuseStep 1613209 = 1209907) (by norm_num)
theorem B5168549 : Blo 1433536 5168549 := bbase (se 4 (by rfl) ⟨484551, by rfl⟩ : syracuseStep 5168549 = 969103) (by norm_num)
theorem B1965485 : Blo 1433536 1965485 := bbase (se 3 (by rfl) ⟨368528, by rfl⟩ : syracuseStep 1965485 = 737057) (by norm_num)
theorem B1613245 : Blo 1433536 1613245 := bbase (se 3 (by rfl) ⟨302483, by rfl⟩ : syracuseStep 1613245 = 604967) (by norm_num)
theorem B3227093 : Blo 1433536 3227093 := bbase (se 7 (by rfl) ⟨37817, by rfl⟩ : syracuseStep 3227093 = 75635) (by norm_num)
theorem B3063253 : Blo 1433536 3063253 := bbase (se 7 (by rfl) ⟨35897, by rfl⟩ : syracuseStep 3063253 = 71795) (by norm_num)
theorem B4087253 : Blo 1433536 4087253 := bbase (se 7 (by rfl) ⟨47897, by rfl⟩ : syracuseStep 4087253 = 95795) (by norm_num)
theorem B1613281 : Blo 1433536 1613281 := bbase (se 2 (by rfl) ⟨604980, by rfl⟩ : syracuseStep 1613281 = 1209961) (by norm_num)
theorem B1613317 : Blo 1433536 1613317 := bbase (se 4 (by rfl) ⟨151248, by rfl⟩ : syracuseStep 1613317 = 302497) (by norm_num)
theorem B2760205 : Blo 1433536 2760205 := bbase (se 3 (by rfl) ⟨517538, by rfl⟩ : syracuseStep 2760205 = 1035077) (by norm_num)
theorem B3227165 : Blo 1433536 3227165 := bbase (se 3 (by rfl) ⟨605093, by rfl⟩ : syracuseStep 3227165 = 1210187) (by norm_num)
theorem B1613353 : Blo 1433536 1613353 := bbase (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) (by norm_num)
theorem B7265861 : Blo 1433536 7265861 := bbase (se 4 (by rfl) ⟨681174, by rfl⟩ : syracuseStep 7265861 = 1362349) (by norm_num)
theorem B1613389 : Blo 1433536 1613389 := bbase (se 3 (by rfl) ⟨302510, by rfl⟩ : syracuseStep 1613389 = 605021) (by norm_num)
theorem B1531477 : Blo 1433536 1531477 := bbase (se 8 (by rfl) ⟨8973, by rfl⟩ : syracuseStep 1531477 = 17947) (by norm_num)
theorem B4841045 : Blo 1433536 4841045 := bbase (se 8 (by rfl) ⟨28365, by rfl⟩ : syracuseStep 4841045 = 56731) (by norm_num)
theorem B1531481 : Blo 1433536 1531481 := bbase (se 2 (by rfl) ⟨574305, by rfl⟩ : syracuseStep 1531481 = 1148611) (by norm_num)
theorem B3227237 : Blo 1433536 3227237 := bbase (se 4 (by rfl) ⟨302553, by rfl⟩ : syracuseStep 3227237 = 605107) (by norm_num)
theorem B1613425 : Blo 1433536 1613425 := bbase (se 2 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 1613425 = 1210069) (by norm_num)
theorem B1613461 : Blo 1433536 1613461 := bbase (se 6 (by rfl) ⟨37815, by rfl⟩ : syracuseStep 1613461 = 75631) (by norm_num)
theorem B3628709 : Blo 1433536 3628709 := bbase (se 4 (by rfl) ⟨340191, by rfl⟩ : syracuseStep 3628709 = 680383) (by norm_num)
theorem B3227309 : Blo 1433536 3227309 := bbase (se 3 (by rfl) ⟨605120, by rfl⟩ : syracuseStep 3227309 = 1210241) (by norm_num)
theorem B1613497 : Blo 1433536 1613497 := bbase (se 2 (by rfl) ⟨605061, by rfl⟩ : syracuseStep 1613497 = 1210123) (by norm_num)
theorem B4087493 : Blo 1433536 4087493 := bbase (se 4 (by rfl) ⟨383202, by rfl⟩ : syracuseStep 4087493 = 766405) (by norm_num)
theorem B3063509 : Blo 1433536 3063509 := bbase (se 7 (by rfl) ⟨35900, by rfl⟩ : syracuseStep 3063509 = 71801) (by norm_num)
theorem B1613533 : Blo 1433536 1613533 := bbase (se 3 (by rfl) ⟨302537, by rfl⟩ : syracuseStep 1613533 = 605075) (by norm_num)
theorem B6889205 : Blo 1433536 6889205 := bbase (se 5 (by rfl) ⟨322931, by rfl⟩ : syracuseStep 6889205 = 645863) (by norm_num)
theorem B3227381 : Blo 1433536 3227381 := bbase (se 5 (by rfl) ⟨151283, by rfl⟩ : syracuseStep 3227381 = 302567) (by norm_num)
theorem B1613569 : Blo 1433536 1613569 := bbase (se 2 (by rfl) ⟨605088, by rfl⟩ : syracuseStep 1613569 = 1210177) (by norm_num)
theorem B1613605 : Blo 1433536 1613605 := bbase (se 4 (by rfl) ⟨151275, by rfl⟩ : syracuseStep 1613605 = 302551) (by norm_num)
theorem B3227453 : Blo 1433536 3227453 := bbase (se 3 (by rfl) ⟨605147, by rfl⟩ : syracuseStep 3227453 = 1210295) (by norm_num)
theorem B1613641 : Blo 1433536 1613641 := bbase (se 2 (by rfl) ⟨605115, by rfl⟩ : syracuseStep 1613641 = 1210231) (by norm_num)
theorem B3628901 : Blo 1433536 3628901 := bbase (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) (by norm_num)
theorem B1613677 : Blo 1433536 1613677 := bbase (se 3 (by rfl) ⟨302564, by rfl⟩ : syracuseStep 1613677 = 605129) (by norm_num)
theorem B3227525 : Blo 1433536 3227525 := bbase (se 4 (by rfl) ⟨302580, by rfl⟩ : syracuseStep 3227525 = 605161) (by norm_num)
theorem B4087685 : Blo 1433536 4087685 := bbase (se 4 (by rfl) ⟨383220, by rfl⟩ : syracuseStep 4087685 = 766441) (by norm_num)
theorem B1613713 : Blo 1433536 1613713 := bbase (se 2 (by rfl) ⟨605142, by rfl⟩ : syracuseStep 1613713 = 1210285) (by norm_num)
theorem B7364501 : Blo 1433536 7364501 := bbase (se 6 (by rfl) ⟨172605, by rfl⟩ : syracuseStep 7364501 = 345211) (by norm_num)
theorem B1613749 : Blo 1433536 1613749 := bbase (se 5 (by rfl) ⟨75644, by rfl⟩ : syracuseStep 1613749 = 151289) (by norm_num)
theorem B3227597 : Blo 1433536 3227597 := bbase (se 3 (by rfl) ⟨605174, by rfl⟩ : syracuseStep 3227597 = 1210349) (by norm_num)
theorem B1613785 : Blo 1433536 1613785 := bbase (se 2 (by rfl) ⟨605169, by rfl⟩ : syracuseStep 1613785 = 1210339) (by norm_num)
theorem B7258085 : Blo 1433536 7258085 := bbase (se 4 (by rfl) ⟨680445, by rfl⟩ : syracuseStep 7258085 = 1360891) (by norm_num)
theorem B1613821 : Blo 1433536 1613821 := bbase (se 3 (by rfl) ⟨302591, by rfl⟩ : syracuseStep 1613821 = 605183) (by norm_num)
theorem B1433603 : Blo 1433536 1433603 := bstep (se 1 (by rfl) ⟨1075202, by rfl⟩ : syracuseStep 1433603 = 2150405) B2150405
theorem B3227651 : Blo 1433536 3227651 := bstep (se 1 (by rfl) ⟨2420738, by rfl⟩ : syracuseStep 3227651 = 4841477) B4841477
theorem B1433619 : Blo 1433536 1433619 := bstep (se 1 (by rfl) ⟨1075214, by rfl⟩ : syracuseStep 1433619 = 2150429) B2150429
theorem B1433635 : Blo 1433536 1433635 := bstep (se 1 (by rfl) ⟨1075226, by rfl⟩ : syracuseStep 1433635 = 2150453) B2150453
theorem B1433651 : Blo 1433536 1433651 := bstep (se 1 (by rfl) ⟨1075238, by rfl⟩ : syracuseStep 1433651 = 2150477) B2150477
theorem B1613875 : Blo 1433536 1613875 := bstep (se 1 (by rfl) ⟨1210406, by rfl⟩ : syracuseStep 1613875 = 2420813) B2420813
theorem B1433667 : Blo 1433536 1433667 := bstep (se 1 (by rfl) ⟨1075250, by rfl⟩ : syracuseStep 1433667 = 2150501) B2150501
theorem B1433683 : Blo 1433536 1433683 := bstep (se 1 (by rfl) ⟨1075262, by rfl⟩ : syracuseStep 1433683 = 2150525) B2150525
theorem B1433699 : Blo 1433536 1433699 := bstep (se 1 (by rfl) ⟨1075274, by rfl⟩ : syracuseStep 1433699 = 2150549) B2150549
theorem B4841585 : Blo 1433536 4841585 := bstep (se 2 (by rfl) ⟨1815594, by rfl⟩ : syracuseStep 4841585 = 3631189) B3631189
theorem B1433715 : Blo 1433536 1433715 := bstep (se 1 (by rfl) ⟨1075286, by rfl⟩ : syracuseStep 1433715 = 2150573) B2150573
theorem B1433731 : Blo 1433536 1433731 := bstep (se 1 (by rfl) ⟨1075298, by rfl⟩ : syracuseStep 1433731 = 2150597) B2150597
theorem B3063953 : Blo 1433536 3063953 := bstep (se 2 (by rfl) ⟨1148982, by rfl⟩ : syracuseStep 3063953 = 2297965) B2297965
theorem B1433747 : Blo 1433536 1433747 := bstep (se 1 (by rfl) ⟨1075310, by rfl⟩ : syracuseStep 1433747 = 2150621) B2150621
theorem B1433763 : Blo 1433536 1433763 := bstep (se 1 (by rfl) ⟨1075322, by rfl⟩ : syracuseStep 1433763 = 2150645) B2150645
theorem B1433779 : Blo 1433536 1433779 := bstep (se 1 (by rfl) ⟨1075334, by rfl⟩ : syracuseStep 1433779 = 2150669) B2150669
theorem B1433795 : Blo 1433536 1433795 := bstep (se 1 (by rfl) ⟨1075346, by rfl⟩ : syracuseStep 1433795 = 2150693) B2150693
theorem B1614019 : Blo 1433536 1614019 := bstep (se 1 (by rfl) ⟨1210514, by rfl⟩ : syracuseStep 1614019 = 2421029) B2421029
theorem B7266509 : Blo 1433536 7266509 := bstep (se 3 (by rfl) ⟨1362470, by rfl⟩ : syracuseStep 7266509 = 2724941) B2724941
theorem B1433811 : Blo 1433536 1433811 := bstep (se 1 (by rfl) ⟨1075358, by rfl⟩ : syracuseStep 1433811 = 2150717) B2150717
theorem B1433827 : Blo 1433536 1433827 := bstep (se 1 (by rfl) ⟨1075370, by rfl⟩ : syracuseStep 1433827 = 2150741) B2150741
theorem B1433843 : Blo 1433536 1433843 := bstep (se 1 (by rfl) ⟨1075382, by rfl⟩ : syracuseStep 1433843 = 2150765) B2150765
theorem B1433859 : Blo 1433536 1433859 := bstep (se 1 (by rfl) ⟨1075394, by rfl⟩ : syracuseStep 1433859 = 2150789) B2150789
theorem B3227921 : Blo 1433536 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B1433875 : Blo 1433536 1433875 := bstep (se 1 (by rfl) ⟨1075406, by rfl⟩ : syracuseStep 1433875 = 2150813) B2150813
theorem B1433891 : Blo 1433536 1433891 := bstep (se 1 (by rfl) ⟨1075418, by rfl⟩ : syracuseStep 1433891 = 2150837) B2150837
theorem B3227939 : Blo 1433536 3227939 := bstep (se 1 (by rfl) ⟨2420954, by rfl⟩ : syracuseStep 3227939 = 4841909) B4841909
theorem B1433907 : Blo 1433536 1433907 := bstep (se 1 (by rfl) ⟨1075430, by rfl⟩ : syracuseStep 1433907 = 2150861) B2150861
theorem B1433923 : Blo 1433536 1433923 := bstep (se 1 (by rfl) ⟨1075442, by rfl⟩ : syracuseStep 1433923 = 2150885) B2150885
theorem B1433939 : Blo 1433536 1433939 := bstep (se 1 (by rfl) ⟨1075454, by rfl⟩ : syracuseStep 1433939 = 2150909) B2150909
theorem B1614163 : Blo 1433536 1614163 := bstep (se 1 (by rfl) ⟨1210622, by rfl⟩ : syracuseStep 1614163 = 2421245) B2421245
theorem B1433955 : Blo 1433536 1433955 := bstep (se 1 (by rfl) ⟨1075466, by rfl⟩ : syracuseStep 1433955 = 2150933) B2150933
theorem B1433971 : Blo 1433536 1433971 := bstep (se 1 (by rfl) ⟨1075478, by rfl⟩ : syracuseStep 1433971 = 2150957) B2150957
theorem B1433987 : Blo 1433536 1433987 := bstep (se 1 (by rfl) ⟨1075490, by rfl⟩ : syracuseStep 1433987 = 2150981) B2150981
theorem B1434003 : Blo 1433536 1434003 := bstep (se 1 (by rfl) ⟨1075502, by rfl⟩ : syracuseStep 1434003 = 2151005) B2151005
theorem B1434019 : Blo 1433536 1434019 := bstep (se 1 (by rfl) ⟨1075514, by rfl⟩ : syracuseStep 1434019 = 2151029) B2151029
theorem B3678641 : Blo 1433536 3678641 := bstep (se 2 (by rfl) ⟨1379490, by rfl⟩ : syracuseStep 3678641 = 2758981) B2758981
theorem B1434035 : Blo 1433536 1434035 := bstep (se 1 (by rfl) ⟨1075526, by rfl⟩ : syracuseStep 1434035 = 2151053) B2151053
theorem B1434051 : Blo 1433536 1434051 := bstep (se 1 (by rfl) ⟨1075538, by rfl⟩ : syracuseStep 1434051 = 2151077) B2151077
theorem B8167877 : Blo 1433536 8167877 := bstep (se 4 (by rfl) ⟨765738, by rfl⟩ : syracuseStep 8167877 = 1531477) B1531477
theorem B1434067 : Blo 1433536 1434067 := bstep (se 1 (by rfl) ⟨1075550, by rfl⟩ : syracuseStep 1434067 = 2151101) B2151101
theorem B1434083 : Blo 1433536 1434083 := bstep (se 1 (by rfl) ⟨1075562, by rfl⟩ : syracuseStep 1434083 = 2151125) B2151125
theorem B1614307 : Blo 1433536 1614307 := bstep (se 1 (by rfl) ⟨1210730, by rfl⟩ : syracuseStep 1614307 = 2421461) B2421461
theorem B5243363 : Blo 1433536 5243363 := bstep (se 1 (by rfl) ⟨3932522, by rfl⟩ : syracuseStep 5243363 = 7865045) B7865045
theorem B2097649 : Blo 1433536 2097649 := bstep (se 2 (by rfl) ⟨786618, by rfl⟩ : syracuseStep 2097649 = 1573237) B1573237
theorem B1434099 : Blo 1433536 1434099 := bstep (se 1 (by rfl) ⟨1075574, by rfl⟩ : syracuseStep 1434099 = 2151149) B2151149
theorem B1434115 : Blo 1433536 1434115 := bstep (se 1 (by rfl) ⟨1075586, by rfl⟩ : syracuseStep 1434115 = 2151173) B2151173
theorem B1434131 : Blo 1433536 1434131 := bstep (se 1 (by rfl) ⟨1075598, by rfl⟩ : syracuseStep 1434131 = 2151197) B2151197
theorem B1434147 : Blo 1433536 1434147 := bstep (se 1 (by rfl) ⟨1075610, by rfl⟩ : syracuseStep 1434147 = 2151221) B2151221
theorem B3228209 : Blo 1433536 3228209 := bstep (se 2 (by rfl) ⟨1210578, by rfl⟩ : syracuseStep 3228209 = 2421157) B2421157
theorem B1434163 : Blo 1433536 1434163 := bstep (se 1 (by rfl) ⟨1075622, by rfl⟩ : syracuseStep 1434163 = 2151245) B2151245
theorem B1434179 : Blo 1433536 1434179 := bstep (se 1 (by rfl) ⟨1075634, by rfl⟩ : syracuseStep 1434179 = 2151269) B2151269
theorem B3228227 : Blo 1433536 3228227 := bstep (se 1 (by rfl) ⟨2421170, by rfl⟩ : syracuseStep 3228227 = 4842341) B4842341
theorem B1434195 : Blo 1433536 1434195 := bstep (se 1 (by rfl) ⟨1075646, by rfl⟩ : syracuseStep 1434195 = 2151293) B2151293
theorem B1434211 : Blo 1433536 1434211 := bstep (se 1 (by rfl) ⟨1075658, by rfl⟩ : syracuseStep 1434211 = 2151317) B2151317
theorem B1532515 : Blo 1433536 1532515 := bstep (se 1 (by rfl) ⟨1149386, by rfl⟩ : syracuseStep 1532515 = 2298773) B2298773
theorem B3629681 : Blo 1433536 3629681 := bstep (se 2 (by rfl) ⟨1361130, by rfl⟩ : syracuseStep 3629681 = 2722261) B2722261
theorem B51069553 : Blo 1433536 51069553 := bstep (se 2 (by rfl) ⟨19151082, by rfl⟩ : syracuseStep 51069553 = 38302165) B38302165
theorem B1434227 : Blo 1433536 1434227 := bstep (se 1 (by rfl) ⟨1075670, by rfl⟩ : syracuseStep 1434227 = 2151341) B2151341
theorem B1614451 : Blo 1433536 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B1434243 : Blo 1433536 1434243 := bstep (se 1 (by rfl) ⟨1075682, by rfl⟩ : syracuseStep 1434243 = 2151365) B2151365
theorem B4842125 : Blo 1433536 4842125 := bstep (se 3 (by rfl) ⟨907898, by rfl⟩ : syracuseStep 4842125 = 1815797) B1815797
theorem B1434259 : Blo 1433536 1434259 := bstep (se 1 (by rfl) ⟨1075694, by rfl⟩ : syracuseStep 1434259 = 2151389) B2151389
theorem B3629731 : Blo 1433536 3629731 := bstep (se 1 (by rfl) ⟨2722298, by rfl⟩ : syracuseStep 3629731 = 5444597) B5444597
theorem B1434275 : Blo 1433536 1434275 := bstep (se 1 (by rfl) ⟨1075706, by rfl⟩ : syracuseStep 1434275 = 2151413) B2151413
theorem B3064483 : Blo 1433536 3064483 := bstep (se 1 (by rfl) ⟨2298362, by rfl⟩ : syracuseStep 3064483 = 4596725) B4596725
theorem B1434291 : Blo 1433536 1434291 := bstep (se 1 (by rfl) ⟨1075718, by rfl⟩ : syracuseStep 1434291 = 2151437) B2151437
theorem B1434307 : Blo 1433536 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B4842179 : Blo 1433536 4842179 := bstep (se 1 (by rfl) ⟨3631634, by rfl⟩ : syracuseStep 4842179 = 7263269) B7263269
theorem B3678929 : Blo 1433536 3678929 := bstep (se 2 (by rfl) ⟨1379598, by rfl⟩ : syracuseStep 3678929 = 2759197) B2759197
theorem B1434323 : Blo 1433536 1434323 := bstep (se 1 (by rfl) ⟨1075742, by rfl⟩ : syracuseStep 1434323 = 2151485) B2151485
theorem B1434339 : Blo 1433536 1434339 := bstep (se 1 (by rfl) ⟨1075754, by rfl⟩ : syracuseStep 1434339 = 2151509) B2151509
theorem B6128369 : Blo 1433536 6128369 := bstep (se 2 (by rfl) ⟨2298138, by rfl⟩ : syracuseStep 6128369 = 4596277) B4596277
theorem B1434355 : Blo 1433536 1434355 := bstep (se 1 (by rfl) ⟨1075766, by rfl⟩ : syracuseStep 1434355 = 2151533) B2151533
theorem B1434371 : Blo 1433536 1434371 := bstep (se 1 (by rfl) ⟨1075778, by rfl⟩ : syracuseStep 1434371 = 2151557) B2151557
theorem B1614595 : Blo 1433536 1614595 := bstep (se 1 (by rfl) ⟨1210946, by rfl⟩ : syracuseStep 1614595 = 2421893) B2421893
theorem B1434387 : Blo 1433536 1434387 := bstep (se 1 (by rfl) ⟨1075790, by rfl⟩ : syracuseStep 1434387 = 2151581) B2151581
theorem B1434403 : Blo 1433536 1434403 := bstep (se 1 (by rfl) ⟨1075802, by rfl⟩ : syracuseStep 1434403 = 2151605) B2151605
theorem B6128419 : Blo 1433536 6128419 := bstep (se 1 (by rfl) ⟨4596314, by rfl⟩ : syracuseStep 6128419 = 9192629) B9192629
theorem B3629873 : Blo 1433536 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B1434419 : Blo 1433536 1434419 := bstep (se 1 (by rfl) ⟨1075814, by rfl⟩ : syracuseStep 1434419 = 2151629) B2151629
theorem B1434435 : Blo 1433536 1434435 := bstep (se 1 (by rfl) ⟨1075826, by rfl⟩ : syracuseStep 1434435 = 2151653) B2151653
theorem B3228497 : Blo 1433536 3228497 := bstep (se 2 (by rfl) ⟨1210686, by rfl⟩ : syracuseStep 3228497 = 2421373) B2421373
theorem B1434451 : Blo 1433536 1434451 := bstep (se 1 (by rfl) ⟨1075838, by rfl⟩ : syracuseStep 1434451 = 2151677) B2151677
theorem B1434467 : Blo 1433536 1434467 := bstep (se 1 (by rfl) ⟨1075850, by rfl⟩ : syracuseStep 1434467 = 2151701) B2151701
theorem B3228515 : Blo 1433536 3228515 := bstep (se 1 (by rfl) ⟨2421386, by rfl⟩ : syracuseStep 3228515 = 4842773) B4842773
theorem B1434483 : Blo 1433536 1434483 := bstep (se 1 (by rfl) ⟨1075862, by rfl⟩ : syracuseStep 1434483 = 2151725) B2151725
theorem B1434499 : Blo 1433536 1434499 := bstep (se 1 (by rfl) ⟨1075874, by rfl⟩ : syracuseStep 1434499 = 2151749) B2151749
theorem B1434515 : Blo 1433536 1434515 := bstep (se 1 (by rfl) ⟨1075886, by rfl⟩ : syracuseStep 1434515 = 2151773) B2151773
theorem B1614739 : Blo 1433536 1614739 := bstep (se 1 (by rfl) ⟨1211054, by rfl⟩ : syracuseStep 1614739 = 2422109) B2422109
theorem B1434531 : Blo 1433536 1434531 := bstep (se 1 (by rfl) ⟨1075898, by rfl⟩ : syracuseStep 1434531 = 2151797) B2151797
theorem B6890417 : Blo 1433536 6890417 := bstep (se 2 (by rfl) ⟨2583906, by rfl⟩ : syracuseStep 6890417 = 5167813) B5167813
theorem B7259057 : Blo 1433536 7259057 := bstep (se 2 (by rfl) ⟨2722146, by rfl⟩ : syracuseStep 7259057 = 5444293) B5444293
theorem B1434547 : Blo 1433536 1434547 := bstep (se 1 (by rfl) ⟨1075910, by rfl⟩ : syracuseStep 1434547 = 2151821) B2151821
theorem B1434563 : Blo 1433536 1434563 := bstep (se 1 (by rfl) ⟨1075922, by rfl⟩ : syracuseStep 1434563 = 2151845) B2151845
theorem B44172229 : Blo 1433536 44172229 := bstep (se 4 (by rfl) ⟨4141146, by rfl⟩ : syracuseStep 44172229 = 8282293) B8282293
theorem B5522381 : Blo 1433536 5522381 := bstep (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) B2070893
theorem B5448653 : Blo 1433536 5448653 := bstep (se 3 (by rfl) ⟨1021622, by rfl⟩ : syracuseStep 5448653 = 2043245) B2043245
theorem B4842449 : Blo 1433536 4842449 := bstep (se 2 (by rfl) ⟨1815918, by rfl⟩ : syracuseStep 4842449 = 3631837) B3631837
theorem B1434579 : Blo 1433536 1434579 := bstep (se 1 (by rfl) ⟨1075934, by rfl⟩ : syracuseStep 1434579 = 2151869) B2151869
theorem B1434595 : Blo 1433536 1434595 := bstep (se 1 (by rfl) ⟨1075946, by rfl⟩ : syracuseStep 1434595 = 2151893) B2151893
theorem B2180081 : Blo 1433536 2180081 := bstep (se 2 (by rfl) ⟨817530, by rfl⟩ : syracuseStep 2180081 = 1635061) B1635061
theorem B1434611 : Blo 1433536 1434611 := bstep (se 1 (by rfl) ⟨1075958, by rfl⟩ : syracuseStep 1434611 = 2151917) B2151917
theorem B1434627 : Blo 1433536 1434627 := bstep (se 1 (by rfl) ⟨1075970, by rfl⟩ : syracuseStep 1434627 = 2151941) B2151941
theorem B1434643 : Blo 1433536 1434643 := bstep (se 1 (by rfl) ⟨1075982, by rfl⟩ : syracuseStep 1434643 = 2151965) B2151965
theorem B1434659 : Blo 1433536 1434659 := bstep (se 1 (by rfl) ⟨1075994, by rfl⟩ : syracuseStep 1434659 = 2151989) B2151989
theorem B1614883 : Blo 1433536 1614883 := bstep (se 1 (by rfl) ⟨1211162, by rfl⟩ : syracuseStep 1614883 = 2422325) B2422325
theorem B1434675 : Blo 1433536 1434675 := bstep (se 1 (by rfl) ⟨1076006, by rfl⟩ : syracuseStep 1434675 = 2152013) B2152013
theorem B1434691 : Blo 1433536 1434691 := bstep (se 1 (by rfl) ⟨1076018, by rfl⟩ : syracuseStep 1434691 = 2152037) B2152037
theorem B1434707 : Blo 1433536 1434707 := bstep (se 1 (by rfl) ⟨1076030, by rfl⟩ : syracuseStep 1434707 = 2152061) B2152061
theorem B1434723 : Blo 1433536 1434723 := bstep (se 1 (by rfl) ⟨1076042, by rfl⟩ : syracuseStep 1434723 = 2152085) B2152085
theorem B3228785 : Blo 1433536 3228785 := bstep (se 2 (by rfl) ⟨1210794, by rfl⟩ : syracuseStep 3228785 = 2421589) B2421589
theorem B1434739 : Blo 1433536 1434739 := bstep (se 1 (by rfl) ⟨1076054, by rfl⟩ : syracuseStep 1434739 = 2152109) B2152109
theorem B1434755 : Blo 1433536 1434755 := bstep (se 1 (by rfl) ⟨1076066, by rfl⟩ : syracuseStep 1434755 = 2152133) B2152133
theorem B3228803 : Blo 1433536 3228803 := bstep (se 1 (by rfl) ⟨2421602, by rfl⟩ : syracuseStep 3228803 = 4843205) B4843205
theorem B7758989 : Blo 1433536 7758989 := bstep (se 3 (by rfl) ⟨1454810, by rfl⟩ : syracuseStep 7758989 = 2909621) B2909621
theorem B1434771 : Blo 1433536 1434771 := bstep (se 1 (by rfl) ⟨1076078, by rfl⟩ : syracuseStep 1434771 = 2152157) B2152157
theorem B1434787 : Blo 1433536 1434787 := bstep (se 1 (by rfl) ⟨1076090, by rfl⟩ : syracuseStep 1434787 = 2152181) B2152181
theorem B1434803 : Blo 1433536 1434803 := bstep (se 1 (by rfl) ⟨1076102, by rfl⟩ : syracuseStep 1434803 = 2152205) B2152205
theorem B1434819 : Blo 1433536 1434819 := bstep (se 1 (by rfl) ⟨1076114, by rfl⟩ : syracuseStep 1434819 = 2152229) B2152229
theorem B1434835 : Blo 1433536 1434835 := bstep (se 1 (by rfl) ⟨1076126, by rfl⟩ : syracuseStep 1434835 = 2152253) B2152253
theorem B1434851 : Blo 1433536 1434851 := bstep (se 1 (by rfl) ⟨1076138, by rfl⟩ : syracuseStep 1434851 = 2152277) B2152277
theorem B1434867 : Blo 1433536 1434867 := bstep (se 1 (by rfl) ⟨1076150, by rfl⟩ : syracuseStep 1434867 = 2152301) B2152301
theorem B1434883 : Blo 1433536 1434883 := bstep (se 1 (by rfl) ⟨1076162, by rfl⟩ : syracuseStep 1434883 = 2152325) B2152325
theorem B1434899 : Blo 1433536 1434899 := bstep (se 1 (by rfl) ⟨1076174, by rfl⟩ : syracuseStep 1434899 = 2152349) B2152349
theorem B1434915 : Blo 1433536 1434915 := bstep (se 1 (by rfl) ⟨1076186, by rfl⟩ : syracuseStep 1434915 = 2152373) B2152373
theorem B1434931 : Blo 1433536 1434931 := bstep (se 1 (by rfl) ⟨1076198, by rfl⟩ : syracuseStep 1434931 = 2152397) B2152397
theorem B1434947 : Blo 1433536 1434947 := bstep (se 1 (by rfl) ⟨1076210, by rfl⟩ : syracuseStep 1434947 = 2152421) B2152421
theorem B9192781 : Blo 1433536 9192781 := bstep (se 3 (by rfl) ⟨1723646, by rfl⟩ : syracuseStep 9192781 = 3447293) B3447293
theorem B1434963 : Blo 1433536 1434963 := bstep (se 1 (by rfl) ⟨1076222, by rfl⟩ : syracuseStep 1434963 = 2152445) B2152445
theorem B1434979 : Blo 1433536 1434979 := bstep (se 1 (by rfl) ⟨1076234, by rfl⟩ : syracuseStep 1434979 = 2152469) B2152469
theorem B1434995 : Blo 1433536 1434995 := bstep (se 1 (by rfl) ⟨1076246, by rfl⟩ : syracuseStep 1434995 = 2152493) B2152493
theorem B1746307 : Blo 1433536 1746307 := bstep (se 1 (by rfl) ⟨1309730, by rfl⟩ : syracuseStep 1746307 = 2619461) B2619461
theorem B1435011 : Blo 1433536 1435011 := bstep (se 1 (by rfl) ⟨1076258, by rfl⟩ : syracuseStep 1435011 = 2152517) B2152517
theorem B3229073 : Blo 1433536 3229073 := bstep (se 2 (by rfl) ⟨1210902, by rfl⟩ : syracuseStep 3229073 = 2421805) B2421805
theorem B1435027 : Blo 1433536 1435027 := bstep (se 1 (by rfl) ⟨1076270, by rfl⟩ : syracuseStep 1435027 = 2152541) B2152541
theorem B1435043 : Blo 1433536 1435043 := bstep (se 1 (by rfl) ⟨1076282, by rfl⟩ : syracuseStep 1435043 = 2152565) B2152565
theorem B3229091 : Blo 1433536 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B1435059 : Blo 1433536 1435059 := bstep (se 1 (by rfl) ⟨1076294, by rfl⟩ : syracuseStep 1435059 = 2152589) B2152589
theorem B1435075 : Blo 1433536 1435075 := bstep (se 1 (by rfl) ⟨1076306, by rfl⟩ : syracuseStep 1435075 = 2152613) B2152613
theorem B1435091 : Blo 1433536 1435091 := bstep (se 1 (by rfl) ⟨1076318, by rfl⟩ : syracuseStep 1435091 = 2152637) B2152637
theorem B5817827 : Blo 1433536 5817827 := bstep (se 1 (by rfl) ⟨4363370, by rfl⟩ : syracuseStep 5817827 = 8726741) B8726741
theorem B1435107 : Blo 1433536 1435107 := bstep (se 1 (by rfl) ⟨1076330, by rfl⟩ : syracuseStep 1435107 = 2152661) B2152661
theorem B4842989 : Blo 1433536 4842989 := bstep (se 3 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 4842989 = 1816121) B1816121
theorem B1435123 : Blo 1433536 1435123 := bstep (se 1 (by rfl) ⟨1076342, by rfl⟩ : syracuseStep 1435123 = 2152685) B2152685
theorem B1435139 : Blo 1433536 1435139 := bstep (se 1 (by rfl) ⟨1076354, by rfl⟩ : syracuseStep 1435139 = 2152709) B2152709
theorem B1435155 : Blo 1433536 1435155 := bstep (se 1 (by rfl) ⟨1076366, by rfl⟩ : syracuseStep 1435155 = 2152733) B2152733
theorem B4843043 : Blo 1433536 4843043 := bstep (se 1 (by rfl) ⟨3632282, by rfl⟩ : syracuseStep 4843043 = 7264565) B7264565
theorem B1435171 : Blo 1433536 1435171 := bstep (se 1 (by rfl) ⟨1076378, by rfl⟩ : syracuseStep 1435171 = 2152757) B2152757
theorem B1435187 : Blo 1433536 1435187 := bstep (se 1 (by rfl) ⟨1076390, by rfl⟩ : syracuseStep 1435187 = 2152781) B2152781
theorem B1435203 : Blo 1433536 1435203 := bstep (se 1 (by rfl) ⟨1076402, by rfl⟩ : syracuseStep 1435203 = 2152805) B2152805
theorem B1435219 : Blo 1433536 1435219 := bstep (se 1 (by rfl) ⟨1076414, by rfl⟩ : syracuseStep 1435219 = 2152829) B2152829
theorem B1435235 : Blo 1433536 1435235 := bstep (se 1 (by rfl) ⟨1076426, by rfl⟩ : syracuseStep 1435235 = 2152853) B2152853
theorem B1435251 : Blo 1433536 1435251 := bstep (se 1 (by rfl) ⟨1076438, by rfl⟩ : syracuseStep 1435251 = 2152877) B2152877
theorem B1435267 : Blo 1433536 1435267 := bstep (se 1 (by rfl) ⟨1076450, by rfl⟩ : syracuseStep 1435267 = 2152901) B2152901
theorem B1435283 : Blo 1433536 1435283 := bstep (se 1 (by rfl) ⟨1076462, by rfl⟩ : syracuseStep 1435283 = 2152925) B2152925
theorem B1435299 : Blo 1433536 1435299 := bstep (se 1 (by rfl) ⟨1076474, by rfl⟩ : syracuseStep 1435299 = 2152949) B2152949
theorem B3229361 : Blo 1433536 3229361 := bstep (se 2 (by rfl) ⟨1211010, by rfl⟩ : syracuseStep 3229361 = 2422021) B2422021
theorem B1435315 : Blo 1433536 1435315 := bstep (se 1 (by rfl) ⟨1076486, by rfl⟩ : syracuseStep 1435315 = 2152973) B2152973
theorem B3229379 : Blo 1433536 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B1435331 : Blo 1433536 1435331 := bstep (se 1 (by rfl) ⟨1076498, by rfl⟩ : syracuseStep 1435331 = 2152997) B2152997
theorem B7366349 : Blo 1433536 7366349 := bstep (se 3 (by rfl) ⟨1381190, by rfl⟩ : syracuseStep 7366349 = 2762381) B2762381
theorem B1435347 : Blo 1433536 1435347 := bstep (se 1 (by rfl) ⟨1076510, by rfl⟩ : syracuseStep 1435347 = 2153021) B2153021
theorem B1435363 : Blo 1433536 1435363 := bstep (se 1 (by rfl) ⟨1076522, by rfl⟩ : syracuseStep 1435363 = 2153045) B2153045
theorem B5449457 : Blo 1433536 5449457 := bstep (se 2 (by rfl) ⟨2043546, by rfl⟩ : syracuseStep 5449457 = 4087093) B4087093
theorem B1435379 : Blo 1433536 1435379 := bstep (se 1 (by rfl) ⟨1076534, by rfl⟩ : syracuseStep 1435379 = 2153069) B2153069
theorem B2721539 : Blo 1433536 2721539 := bstep (se 1 (by rfl) ⟨2041154, by rfl⟩ : syracuseStep 2721539 = 4082309) B4082309
theorem B1435395 : Blo 1433536 1435395 := bstep (se 1 (by rfl) ⟨1076546, by rfl⟩ : syracuseStep 1435395 = 2153093) B2153093
theorem B3630865 : Blo 1433536 3630865 := bstep (se 2 (by rfl) ⟨1361574, by rfl⟩ : syracuseStep 3630865 = 2723149) B2723149
theorem B1435411 : Blo 1433536 1435411 := bstep (se 1 (by rfl) ⟨1076558, by rfl⟩ : syracuseStep 1435411 = 2153117) B2153117
theorem B66209557 : Blo 1433536 66209557 := bstep (se 6 (by rfl) ⟨1551786, by rfl⟩ : syracuseStep 66209557 = 3103573) B3103573
theorem B2041633 : Blo 1433536 2041633 := bstep (se 2 (by rfl) ⟨765612, by rfl⟩ : syracuseStep 2041633 = 1531225) B1531225
theorem B1435427 : Blo 1433536 1435427 := bstep (se 1 (by rfl) ⟨1076570, by rfl⟩ : syracuseStep 1435427 = 2153141) B2153141
theorem B4843313 : Blo 1433536 4843313 := bstep (se 2 (by rfl) ⟨1816242, by rfl⟩ : syracuseStep 4843313 = 3632485) B3632485
theorem B1435443 : Blo 1433536 1435443 := bstep (se 1 (by rfl) ⟨1076582, by rfl⟩ : syracuseStep 1435443 = 2153165) B2153165
theorem B1435459 : Blo 1433536 1435459 := bstep (se 1 (by rfl) ⟨1076594, by rfl⟩ : syracuseStep 1435459 = 2153189) B2153189
theorem B1435475 : Blo 1433536 1435475 := bstep (se 1 (by rfl) ⟨1076606, by rfl⟩ : syracuseStep 1435475 = 2153213) B2153213
theorem B1435491 : Blo 1433536 1435491 := bstep (se 1 (by rfl) ⟨1076618, by rfl⟩ : syracuseStep 1435491 = 2153237) B2153237
theorem B1435507 : Blo 1433536 1435507 := bstep (se 1 (by rfl) ⟨1076630, by rfl⟩ : syracuseStep 1435507 = 2153261) B2153261
theorem B1435523 : Blo 1433536 1435523 := bstep (se 1 (by rfl) ⟨1076642, by rfl⟩ : syracuseStep 1435523 = 2153285) B2153285
theorem B1722259 : Blo 1433536 1722259 := bstep (se 1 (by rfl) ⟨1291694, by rfl⟩ : syracuseStep 1722259 = 2583389) B2583389
theorem B3229649 : Blo 1433536 3229649 := bstep (se 2 (by rfl) ⟨1211118, by rfl⟩ : syracuseStep 3229649 = 2422237) B2422237
theorem B3229667 : Blo 1433536 3229667 := bstep (se 1 (by rfl) ⟨2422250, by rfl⟩ : syracuseStep 3229667 = 4844501) B4844501
theorem B3680273 : Blo 1433536 3680273 := bstep (se 2 (by rfl) ⟨1380102, by rfl⟩ : syracuseStep 3680273 = 2760205) B2760205
theorem B3631139 : Blo 1433536 3631139 := bstep (se 1 (by rfl) ⟨2723354, by rfl⟩ : syracuseStep 3631139 = 5446709) B5446709
theorem B15501365 : Blo 1433536 15501365 := bstep (se 5 (by rfl) ⟨726626, by rfl⟩ : syracuseStep 15501365 = 1453253) B1453253
theorem B1722451 : Blo 1433536 1722451 := bstep (se 1 (by rfl) ⟨1291838, by rfl⟩ : syracuseStep 1722451 = 2583677) B2583677
theorem B10889315 : Blo 1433536 10889315 := bstep (se 1 (by rfl) ⟨8166986, by rfl⟩ : syracuseStep 10889315 = 16333973) B16333973
theorem B4597955 : Blo 1433536 4597955 := bstep (se 1 (by rfl) ⟨3448466, by rfl⟩ : syracuseStep 4597955 = 6896933) B6896933
theorem B3631331 : Blo 1433536 3631331 := bstep (se 1 (by rfl) ⟨2723498, by rfl⟩ : syracuseStep 3631331 = 5446997) B5446997
theorem B3229937 : Blo 1433536 3229937 := bstep (se 2 (by rfl) ⟨1211226, by rfl⟩ : syracuseStep 3229937 = 2422453) B2422453
theorem B4360451 : Blo 1433536 4360451 := bstep (se 1 (by rfl) ⟨3270338, by rfl⟩ : syracuseStep 4360451 = 6540677) B6540677
theorem B3229955 : Blo 1433536 3229955 := bstep (se 1 (by rfl) ⟨2422466, by rfl⟩ : syracuseStep 3229955 = 4844933) B4844933
theorem B4843853 : Blo 1433536 4843853 := bstep (se 3 (by rfl) ⟨908222, by rfl⟩ : syracuseStep 4843853 = 1816445) B1816445
theorem B7260515 : Blo 1433536 7260515 := bstep (se 1 (by rfl) ⟨5445386, by rfl⟩ : syracuseStep 7260515 = 10890773) B10890773
theorem B4843907 : Blo 1433536 4843907 := bstep (se 1 (by rfl) ⟨3632930, by rfl⟩ : syracuseStep 4843907 = 7265861) B7265861
theorem B5450125 : Blo 1433536 5450125 := bstep (se 3 (by rfl) ⟨1021898, by rfl⟩ : syracuseStep 5450125 = 2043797) B2043797
theorem B2419105 : Blo 1433536 2419105 := bstep (se 2 (by rfl) ⟨907164, by rfl⟩ : syracuseStep 2419105 = 1814329) B1814329
theorem B5171633 : Blo 1433536 5171633 := bstep (se 2 (by rfl) ⟨1939362, by rfl⟩ : syracuseStep 5171633 = 3878725) B3878725
theorem B2419139 : Blo 1433536 2419139 := bstep (se 1 (by rfl) ⟨1814354, by rfl⟩ : syracuseStep 2419139 = 3628709) B3628709
theorem B2042339 : Blo 1433536 2042339 := bstep (se 1 (by rfl) ⟨1531754, by rfl⟩ : syracuseStep 2042339 = 3063509) B3063509
theorem B2419267 : Blo 1433536 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B4909667 : Blo 1433536 4909667 := bstep (se 1 (by rfl) ⟨3682250, by rfl⟩ : syracuseStep 4909667 = 7364501) B7364501
theorem B4844177 : Blo 1433536 4844177 := bstep (se 2 (by rfl) ⟨1816566, by rfl⟩ : syracuseStep 4844177 = 3633133) B3633133
theorem B2722481 : Blo 1433536 2722481 := bstep (se 2 (by rfl) ⟨1020930, by rfl⟩ : syracuseStep 2722481 = 2041861) B2041861
theorem B2419409 : Blo 1433536 2419409 := bstep (se 2 (by rfl) ⟨907278, by rfl⟩ : syracuseStep 2419409 = 1814557) B1814557
theorem B2157281 : Blo 1433536 2157281 := bstep (se 2 (by rfl) ⟨808980, by rfl⟩ : syracuseStep 2157281 = 1617961) B1617961
theorem B2419537 : Blo 1433536 2419537 := bstep (se 2 (by rfl) ⟨907326, by rfl⟩ : syracuseStep 2419537 = 1814653) B1814653
theorem B2419571 : Blo 1433536 2419571 := bstep (se 1 (by rfl) ⟨1814678, by rfl⟩ : syracuseStep 2419571 = 3629357) B3629357
theorem B3877859 : Blo 1433536 3877859 := bstep (se 1 (by rfl) ⟨2908394, by rfl⟩ : syracuseStep 3877859 = 5816789) B5816789
theorem B2419699 : Blo 1433536 2419699 := bstep (se 1 (by rfl) ⟨1814774, by rfl⟩ : syracuseStep 2419699 = 3629549) B3629549
theorem B6212621 : Blo 1433536 6212621 := bstep (se 3 (by rfl) ⟨1164866, by rfl⟩ : syracuseStep 6212621 = 2329733) B2329733
theorem B4598801 : Blo 1433536 4598801 := bstep (se 2 (by rfl) ⟨1724550, by rfl⟩ : syracuseStep 4598801 = 3449101) B3449101
theorem B18385973 : Blo 1433536 18385973 := bstep (se 5 (by rfl) ⟨861842, by rfl⟩ : syracuseStep 18385973 = 1723685) B1723685
theorem B4598851 : Blo 1433536 4598851 := bstep (se 1 (by rfl) ⟨3449138, by rfl⟩ : syracuseStep 4598851 = 6898277) B6898277
theorem B2042977 : Blo 1433536 2042977 := bstep (se 2 (by rfl) ⟨766116, by rfl⟩ : syracuseStep 2042977 = 1532233) B1532233
theorem B2419841 : Blo 1433536 2419841 := bstep (se 2 (by rfl) ⟨907440, by rfl⟩ : syracuseStep 2419841 = 1814881) B1814881
theorem B7261325 : Blo 1433536 7261325 := bstep (se 3 (by rfl) ⟨1361498, by rfl⟩ : syracuseStep 7261325 = 2722997) B2722997
theorem B6130829 : Blo 1433536 6130829 := bstep (se 3 (by rfl) ⟨1149530, by rfl⟩ : syracuseStep 6130829 = 2299061) B2299061
theorem B3632273 : Blo 1433536 3632273 := bstep (se 2 (by rfl) ⟨1362102, by rfl⟩ : syracuseStep 3632273 = 2724205) B2724205
theorem B4844717 : Blo 1433536 4844717 := bstep (se 3 (by rfl) ⟨908384, by rfl⟩ : syracuseStep 4844717 = 1816769) B1816769
theorem B8277169 : Blo 1433536 8277169 := bstep (se 2 (by rfl) ⟨3103938, by rfl⟩ : syracuseStep 8277169 = 6207877) B6207877
theorem B2297011 : Blo 1433536 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B3632323 : Blo 1433536 3632323 := bstep (se 1 (by rfl) ⟨2724242, by rfl⟩ : syracuseStep 3632323 = 5448485) B5448485
theorem B2043091 : Blo 1433536 2043091 := bstep (se 1 (by rfl) ⟨1532318, by rfl⟩ : syracuseStep 2043091 = 3064637) B3064637
theorem B4844771 : Blo 1433536 4844771 := bstep (se 1 (by rfl) ⟨3633578, by rfl⟩ : syracuseStep 4844771 = 7267157) B7267157
theorem B2419969 : Blo 1433536 2419969 := bstep (se 2 (by rfl) ⟨907488, by rfl⟩ : syracuseStep 2419969 = 1814977) B1814977
theorem B2420003 : Blo 1433536 2420003 := bstep (se 1 (by rfl) ⟨1815002, by rfl⟩ : syracuseStep 2420003 = 3630005) B3630005
theorem B4082993 : Blo 1433536 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B6892877 : Blo 1433536 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B3632465 : Blo 1433536 3632465 := bstep (se 2 (by rfl) ⟨1362174, by rfl⟩ : syracuseStep 3632465 = 2724349) B2724349
theorem B2420131 : Blo 1433536 2420131 := bstep (se 1 (by rfl) ⟨1815098, by rfl⟩ : syracuseStep 2420131 = 3630197) B3630197
theorem B2420273 : Blo 1433536 2420273 := bstep (se 2 (by rfl) ⟨907602, by rfl⟩ : syracuseStep 2420273 = 1815205) B1815205
theorem B2723377 : Blo 1433536 2723377 := bstep (se 2 (by rfl) ⟨1021266, by rfl⟩ : syracuseStep 2723377 = 2042533) B2042533
theorem B7179853 : Blo 1433536 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B5820017 : Blo 1433536 5820017 := bstep (se 2 (by rfl) ⟨2182506, by rfl⟩ : syracuseStep 5820017 = 4365013) B4365013
theorem B1724051 : Blo 1433536 1724051 := bstep (se 1 (by rfl) ⟨1293038, by rfl⟩ : syracuseStep 1724051 = 2586077) B2586077
theorem B2420401 : Blo 1433536 2420401 := bstep (se 2 (by rfl) ⟨907650, by rfl⟩ : syracuseStep 2420401 = 1815301) B1815301
theorem B9817777 : Blo 1433536 9817777 := bstep (se 2 (by rfl) ⟨3681666, by rfl⟩ : syracuseStep 9817777 = 7363333) B7363333
theorem B2723537 : Blo 1433536 2723537 := bstep (se 2 (by rfl) ⟨1021326, by rfl⟩ : syracuseStep 2723537 = 2042653) B2042653
theorem B2420435 : Blo 1433536 2420435 := bstep (se 1 (by rfl) ⟨1815326, by rfl⟩ : syracuseStep 2420435 = 3630653) B3630653
theorem B1814339 : Blo 1433536 1814339 := bstep (se 1 (by rfl) ⟨1360754, by rfl⟩ : syracuseStep 1814339 = 2721509) B2721509
theorem B2330435 : Blo 1433536 2330435 := bstep (se 1 (by rfl) ⟨1747826, by rfl⟩ : syracuseStep 2330435 = 3495653) B3495653
theorem B2420563 : Blo 1433536 2420563 := bstep (se 1 (by rfl) ⟨1815422, by rfl⟩ : syracuseStep 2420563 = 3630845) B3630845
theorem B2297683 : Blo 1433536 2297683 := bstep (se 1 (by rfl) ⟨1723262, by rfl⟩ : syracuseStep 2297683 = 3446525) B3446525
theorem B2297729 : Blo 1433536 2297729 := bstep (se 2 (by rfl) ⟨861648, by rfl⟩ : syracuseStep 2297729 = 1723297) B1723297
theorem B2150321 : Blo 1433536 2150321 := bstep (se 2 (by rfl) ⟨806370, by rfl⟩ : syracuseStep 2150321 = 1612741) B1612741
theorem B3878833 : Blo 1433536 3878833 := bstep (se 2 (by rfl) ⟨1454562, by rfl⟩ : syracuseStep 3878833 = 2909125) B2909125
theorem B2150339 : Blo 1433536 2150339 := bstep (se 1 (by rfl) ⟨1612754, by rfl⟩ : syracuseStep 2150339 = 3225509) B3225509
theorem B2150369 : Blo 1433536 2150369 := bstep (se 2 (by rfl) ⟨806388, by rfl⟩ : syracuseStep 2150369 = 1612777) B1612777
theorem B2420705 : Blo 1433536 2420705 := bstep (se 2 (by rfl) ⟨907764, by rfl⟩ : syracuseStep 2420705 = 1815529) B1815529
theorem B1724387 : Blo 1433536 1724387 := bstep (se 1 (by rfl) ⟨1293290, by rfl⟩ : syracuseStep 1724387 = 2586581) B2586581
theorem B2150387 : Blo 1433536 2150387 := bstep (se 1 (by rfl) ⟨1612790, by rfl⟩ : syracuseStep 2150387 = 3225581) B3225581
theorem B2150417 : Blo 1433536 2150417 := bstep (se 2 (by rfl) ⟨806406, by rfl⟩ : syracuseStep 2150417 = 1612813) B1612813
theorem B2150435 : Blo 1433536 2150435 := bstep (se 1 (by rfl) ⟨1612826, by rfl⟩ : syracuseStep 2150435 = 3225653) B3225653
theorem B2150465 : Blo 1433536 2150465 := bstep (se 2 (by rfl) ⟨806424, by rfl⟩ : syracuseStep 2150465 = 1612849) B1612849
theorem B2150483 : Blo 1433536 2150483 := bstep (se 1 (by rfl) ⟨1612862, by rfl⟩ : syracuseStep 2150483 = 3225725) B3225725
theorem B2420833 : Blo 1433536 2420833 := bstep (se 2 (by rfl) ⟨907812, by rfl⟩ : syracuseStep 2420833 = 1815625) B1815625
theorem B2723939 : Blo 1433536 2723939 := bstep (se 1 (by rfl) ⟨2042954, by rfl⟩ : syracuseStep 2723939 = 4085909) B4085909
theorem B2150513 : Blo 1433536 2150513 := bstep (se 2 (by rfl) ⟨806442, by rfl⟩ : syracuseStep 2150513 = 1612885) B1612885
theorem B2150531 : Blo 1433536 2150531 := bstep (se 1 (by rfl) ⟨1612898, by rfl⟩ : syracuseStep 2150531 = 3225797) B3225797
theorem B2420867 : Blo 1433536 2420867 := bstep (se 1 (by rfl) ⟨1815650, by rfl⟩ : syracuseStep 2420867 = 3631301) B3631301
theorem B2150561 : Blo 1433536 2150561 := bstep (se 2 (by rfl) ⟨806460, by rfl⟩ : syracuseStep 2150561 = 1612921) B1612921
theorem B9187505 : Blo 1433536 9187505 := bstep (se 2 (by rfl) ⟨3445314, by rfl⟩ : syracuseStep 9187505 = 6890629) B6890629
theorem B2150579 : Blo 1433536 2150579 := bstep (se 1 (by rfl) ⟨1612934, by rfl⟩ : syracuseStep 2150579 = 3225869) B3225869
theorem B2453699 : Blo 1433536 2453699 := bstep (se 1 (by rfl) ⟨1840274, by rfl⟩ : syracuseStep 2453699 = 3680549) B3680549
theorem B8171725 : Blo 1433536 8171725 := bstep (se 3 (by rfl) ⟨1532198, by rfl⟩ : syracuseStep 8171725 = 3064397) B3064397
theorem B2150609 : Blo 1433536 2150609 := bstep (se 2 (by rfl) ⟨806478, by rfl⟩ : syracuseStep 2150609 = 1612957) B1612957
theorem B2150627 : Blo 1433536 2150627 := bstep (se 1 (by rfl) ⟨1612970, by rfl⟩ : syracuseStep 2150627 = 3225941) B3225941
theorem B4083949 : Blo 1433536 4083949 := bstep (se 3 (by rfl) ⟨765740, by rfl⟩ : syracuseStep 4083949 = 1531481) B1531481
theorem B2150657 : Blo 1433536 2150657 := bstep (se 2 (by rfl) ⟨806496, by rfl⟩ : syracuseStep 2150657 = 1612993) B1612993
theorem B2420995 : Blo 1433536 2420995 := bstep (se 1 (by rfl) ⟨1815746, by rfl⟩ : syracuseStep 2420995 = 3631493) B3631493
theorem B2150675 : Blo 1433536 2150675 := bstep (se 1 (by rfl) ⟨1613006, by rfl⟩ : syracuseStep 2150675 = 3226013) B3226013
theorem B2150705 : Blo 1433536 2150705 := bstep (se 2 (by rfl) ⟨806514, by rfl⟩ : syracuseStep 2150705 = 1613029) B1613029
theorem B3633457 : Blo 1433536 3633457 := bstep (se 2 (by rfl) ⟨1362546, by rfl⟩ : syracuseStep 3633457 = 2725093) B2725093
theorem B2150723 : Blo 1433536 2150723 := bstep (se 1 (by rfl) ⟨1613042, by rfl⟩ : syracuseStep 2150723 = 3226085) B3226085
theorem B2150753 : Blo 1433536 2150753 := bstep (se 2 (by rfl) ⟨806532, by rfl⟩ : syracuseStep 2150753 = 1613065) B1613065
theorem B2150771 : Blo 1433536 2150771 := bstep (se 1 (by rfl) ⟨1613078, by rfl⟩ : syracuseStep 2150771 = 3226157) B3226157
theorem B2298241 : Blo 1433536 2298241 := bstep (se 2 (by rfl) ⟨861840, by rfl⟩ : syracuseStep 2298241 = 1723681) B1723681
theorem B2150801 : Blo 1433536 2150801 := bstep (se 2 (by rfl) ⟨806550, by rfl⟩ : syracuseStep 2150801 = 1613101) B1613101
theorem B2421137 : Blo 1433536 2421137 := bstep (se 2 (by rfl) ⟨907926, by rfl⟩ : syracuseStep 2421137 = 1815853) B1815853
theorem B2150819 : Blo 1433536 2150819 := bstep (se 1 (by rfl) ⟨1613114, by rfl⟩ : syracuseStep 2150819 = 3226229) B3226229
theorem B2585009 : Blo 1433536 2585009 := bstep (se 2 (by rfl) ⟨969378, by rfl⟩ : syracuseStep 2585009 = 1938757) B1938757
theorem B2150849 : Blo 1433536 2150849 := bstep (se 2 (by rfl) ⟨806568, by rfl⟩ : syracuseStep 2150849 = 1613137) B1613137
theorem B4084177 : Blo 1433536 4084177 := bstep (se 2 (by rfl) ⟨1531566, by rfl⟩ : syracuseStep 4084177 = 3063133) B3063133
theorem B2150867 : Blo 1433536 2150867 := bstep (se 1 (by rfl) ⟨1613150, by rfl⟩ : syracuseStep 2150867 = 3226301) B3226301
theorem B5444081 : Blo 1433536 5444081 := bstep (se 2 (by rfl) ⟨2041530, by rfl⟩ : syracuseStep 5444081 = 4083061) B4083061
theorem B2150897 : Blo 1433536 2150897 := bstep (se 2 (by rfl) ⟨806586, by rfl⟩ : syracuseStep 2150897 = 1613173) B1613173
theorem B2150915 : Blo 1433536 2150915 := bstep (se 1 (by rfl) ⟨1613186, by rfl⟩ : syracuseStep 2150915 = 3226373) B3226373
theorem B1815043 : Blo 1433536 1815043 := bstep (se 1 (by rfl) ⟨1361282, by rfl⟩ : syracuseStep 1815043 = 2722565) B2722565
theorem B6124045 : Blo 1433536 6124045 := bstep (se 3 (by rfl) ⟨1148258, by rfl⟩ : syracuseStep 6124045 = 2296517) B2296517
theorem B2421265 : Blo 1433536 2421265 := bstep (se 2 (by rfl) ⟨907974, by rfl⟩ : syracuseStep 2421265 = 1815949) B1815949
theorem B2150945 : Blo 1433536 2150945 := bstep (se 2 (by rfl) ⟨806604, by rfl⟩ : syracuseStep 2150945 = 1613209) B1613209
theorem B6631985 : Blo 1433536 6631985 := bstep (se 2 (by rfl) ⟨2486994, by rfl⟩ : syracuseStep 6631985 = 4973989) B4973989
theorem B2150963 : Blo 1433536 2150963 := bstep (se 1 (by rfl) ⟨1613222, by rfl⟩ : syracuseStep 2150963 = 3226445) B3226445
theorem B2421299 : Blo 1433536 2421299 := bstep (se 1 (by rfl) ⟨1815974, by rfl⟩ : syracuseStep 2421299 = 3631949) B3631949
theorem B2150993 : Blo 1433536 2150993 := bstep (se 2 (by rfl) ⟨806622, by rfl⟩ : syracuseStep 2150993 = 1613245) B1613245
theorem B2151011 : Blo 1433536 2151011 := bstep (se 1 (by rfl) ⟨1613258, by rfl⟩ : syracuseStep 2151011 = 3226517) B3226517
theorem B1815139 : Blo 1433536 1815139 := bstep (se 1 (by rfl) ⟨1361354, by rfl⟩ : syracuseStep 1815139 = 2722709) B2722709
theorem B11629169 : Blo 1433536 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B4084337 : Blo 1433536 4084337 := bstep (se 2 (by rfl) ⟨1531626, by rfl⟩ : syracuseStep 4084337 = 3063253) B3063253
theorem B2151041 : Blo 1433536 2151041 := bstep (se 2 (by rfl) ⟨806640, by rfl⟩ : syracuseStep 2151041 = 1613281) B1613281
theorem B2151059 : Blo 1433536 2151059 := bstep (se 1 (by rfl) ⟨1613294, by rfl⟩ : syracuseStep 2151059 = 3226589) B3226589
theorem B2151089 : Blo 1433536 2151089 := bstep (se 2 (by rfl) ⟨806658, by rfl⟩ : syracuseStep 2151089 = 1613317) B1613317
theorem B2421427 : Blo 1433536 2421427 := bstep (se 1 (by rfl) ⟨1816070, by rfl⟩ : syracuseStep 2421427 = 3632141) B3632141
theorem B2151107 : Blo 1433536 2151107 := bstep (se 1 (by rfl) ⟨1613330, by rfl⟩ : syracuseStep 2151107 = 3226661) B3226661
theorem B13791941 : Blo 1433536 13791941 := bstep (se 4 (by rfl) ⟨1292994, by rfl⟩ : syracuseStep 13791941 = 2585989) B2585989
theorem B2151137 : Blo 1433536 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B4084451 : Blo 1433536 4084451 := bstep (se 1 (by rfl) ⟨3063338, by rfl⟩ : syracuseStep 4084451 = 6126677) B6126677
theorem B2151155 : Blo 1433536 2151155 := bstep (se 1 (by rfl) ⟨1613366, by rfl⟩ : syracuseStep 2151155 = 3226733) B3226733
theorem B2151185 : Blo 1433536 2151185 := bstep (se 2 (by rfl) ⟨806694, by rfl⟩ : syracuseStep 2151185 = 1613389) B1613389
theorem B2151203 : Blo 1433536 2151203 := bstep (se 1 (by rfl) ⟨1613402, by rfl⟩ : syracuseStep 2151203 = 3226805) B3226805
theorem B2151233 : Blo 1433536 2151233 := bstep (se 2 (by rfl) ⟨806712, by rfl⟩ : syracuseStep 2151233 = 1613425) B1613425
theorem B2421569 : Blo 1433536 2421569 := bstep (se 2 (by rfl) ⟨908088, by rfl⟩ : syracuseStep 2421569 = 1816177) B1816177
theorem B2151251 : Blo 1433536 2151251 := bstep (se 1 (by rfl) ⟨1613438, by rfl⟩ : syracuseStep 2151251 = 3226877) B3226877
theorem B2151281 : Blo 1433536 2151281 := bstep (se 2 (by rfl) ⟨806730, by rfl⟩ : syracuseStep 2151281 = 1613461) B1613461
theorem B2151299 : Blo 1433536 2151299 := bstep (se 1 (by rfl) ⟨1613474, by rfl⟩ : syracuseStep 2151299 = 3226949) B3226949
theorem B2151329 : Blo 1433536 2151329 := bstep (se 2 (by rfl) ⟨806748, by rfl⟩ : syracuseStep 2151329 = 1613497) B1613497
theorem B2298785 : Blo 1433536 2298785 := bstep (se 2 (by rfl) ⟨862044, by rfl⟩ : syracuseStep 2298785 = 1724089) B1724089
theorem B2151347 : Blo 1433536 2151347 := bstep (se 1 (by rfl) ⟨1613510, by rfl⟩ : syracuseStep 2151347 = 3227021) B3227021
theorem B2421697 : Blo 1433536 2421697 := bstep (se 2 (by rfl) ⟨908136, by rfl⟩ : syracuseStep 2421697 = 1816273) B1816273
theorem B3445699 : Blo 1433536 3445699 := bstep (se 1 (by rfl) ⟨2584274, by rfl⟩ : syracuseStep 3445699 = 5168549) B5168549
theorem B2151377 : Blo 1433536 2151377 := bstep (se 2 (by rfl) ⟨806766, by rfl⟩ : syracuseStep 2151377 = 1613533) B1613533
theorem B2151395 : Blo 1433536 2151395 := bstep (se 1 (by rfl) ⟨1613546, by rfl⟩ : syracuseStep 2151395 = 3227093) B3227093
theorem B2421731 : Blo 1433536 2421731 := bstep (se 1 (by rfl) ⟨1816298, by rfl⟩ : syracuseStep 2421731 = 3632597) B3632597
theorem B2724835 : Blo 1433536 2724835 := bstep (se 1 (by rfl) ⟨2043626, by rfl⟩ : syracuseStep 2724835 = 4087253) B4087253
theorem B2151425 : Blo 1433536 2151425 := bstep (se 2 (by rfl) ⟨806784, by rfl⟩ : syracuseStep 2151425 = 1613569) B1613569
theorem B10900493 : Blo 1433536 10900493 := bstep (se 3 (by rfl) ⟨2043842, by rfl⟩ : syracuseStep 10900493 = 4087685) B4087685
theorem B1938449 : Blo 1433536 1938449 := bstep (se 2 (by rfl) ⟨726918, by rfl⟩ : syracuseStep 1938449 = 1453837) B1453837
theorem B2151443 : Blo 1433536 2151443 := bstep (se 1 (by rfl) ⟨1613582, by rfl⟩ : syracuseStep 2151443 = 3227165) B3227165
theorem B2151473 : Blo 1433536 2151473 := bstep (se 2 (by rfl) ⟨806802, by rfl⟩ : syracuseStep 2151473 = 1613605) B1613605
theorem B1938497 : Blo 1433536 1938497 := bstep (se 2 (by rfl) ⟨726936, by rfl⟩ : syracuseStep 1938497 = 1453873) B1453873
theorem B2151491 : Blo 1433536 2151491 := bstep (se 1 (by rfl) ⟨1613618, by rfl⟩ : syracuseStep 2151491 = 3227237) B3227237
theorem B1815635 : Blo 1433536 1815635 := bstep (se 1 (by rfl) ⟨1361726, by rfl⟩ : syracuseStep 1815635 = 2723453) B2723453
theorem B2151521 : Blo 1433536 2151521 := bstep (se 2 (by rfl) ⟨806820, by rfl⟩ : syracuseStep 2151521 = 1613641) B1613641
theorem B2421859 : Blo 1433536 2421859 := bstep (se 1 (by rfl) ⟨1816394, by rfl⟩ : syracuseStep 2421859 = 3632789) B3632789
theorem B2151539 : Blo 1433536 2151539 := bstep (se 1 (by rfl) ⟨1613654, by rfl⟩ : syracuseStep 2151539 = 3227309) B3227309
theorem B2724995 : Blo 1433536 2724995 := bstep (se 1 (by rfl) ⟨2043746, by rfl⟩ : syracuseStep 2724995 = 4087493) B4087493
theorem B2151569 : Blo 1433536 2151569 := bstep (se 2 (by rfl) ⟨806838, by rfl⟩ : syracuseStep 2151569 = 1613677) B1613677
theorem B4592803 : Blo 1433536 4592803 := bstep (se 1 (by rfl) ⟨3444602, by rfl⟩ : syracuseStep 4592803 = 6889205) B6889205
theorem B2151587 : Blo 1433536 2151587 := bstep (se 1 (by rfl) ⟨1613690, by rfl⟩ : syracuseStep 2151587 = 3227381) B3227381
theorem B2151617 : Blo 1433536 2151617 := bstep (se 2 (by rfl) ⟨806856, by rfl⟩ : syracuseStep 2151617 = 1613713) B1613713
theorem B2151635 : Blo 1433536 2151635 := bstep (se 1 (by rfl) ⟨1613726, by rfl⟩ : syracuseStep 2151635 = 3227453) B3227453
theorem B9188579 : Blo 1433536 9188579 := bstep (se 1 (by rfl) ⟨6891434, by rfl⟩ : syracuseStep 9188579 = 13782869) B13782869
theorem B2151665 : Blo 1433536 2151665 := bstep (se 2 (by rfl) ⟨806874, by rfl⟩ : syracuseStep 2151665 = 1613749) B1613749
theorem B2422001 : Blo 1433536 2422001 := bstep (se 2 (by rfl) ⟨908250, by rfl⟩ : syracuseStep 2422001 = 1816501) B1816501
theorem B2151683 : Blo 1433536 2151683 := bstep (se 1 (by rfl) ⟨1613762, by rfl⟩ : syracuseStep 2151683 = 3227525) B3227525
theorem B4838669 : Blo 1433536 4838669 := bstep (se 3 (by rfl) ⟨907250, by rfl⟩ : syracuseStep 4838669 = 1814501) B1814501
theorem B2151713 : Blo 1433536 2151713 := bstep (se 2 (by rfl) ⟨806892, by rfl⟩ : syracuseStep 2151713 = 1613785) B1613785
theorem B2151731 : Blo 1433536 2151731 := bstep (se 1 (by rfl) ⟨1613798, by rfl⟩ : syracuseStep 2151731 = 3227597) B3227597
theorem B4838723 : Blo 1433536 4838723 := bstep (se 1 (by rfl) ⟨3629042, by rfl⟩ : syracuseStep 4838723 = 7258085) B7258085
theorem B2151761 : Blo 1433536 2151761 := bstep (se 2 (by rfl) ⟨806910, by rfl⟩ : syracuseStep 2151761 = 1613821) B1613821
theorem B2151779 : Blo 1433536 2151779 := bstep (se 1 (by rfl) ⟨1613834, by rfl⟩ : syracuseStep 2151779 = 3227669) B3227669
theorem B2422129 : Blo 1433536 2422129 := bstep (se 2 (by rfl) ⟨908298, by rfl⟩ : syracuseStep 2422129 = 1816597) B1816597
theorem B2151809 : Blo 1433536 2151809 := bstep (se 2 (by rfl) ⟨806928, by rfl⟩ : syracuseStep 2151809 = 1613857) B1613857
theorem B2151827 : Blo 1433536 2151827 := bstep (se 1 (by rfl) ⟨1613870, by rfl⟩ : syracuseStep 2151827 = 3227741) B3227741
theorem B2422163 : Blo 1433536 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B2151857 : Blo 1433536 2151857 := bstep (se 2 (by rfl) ⟨806946, by rfl⟩ : syracuseStep 2151857 = 1613893) B1613893
theorem B2151875 : Blo 1433536 2151875 := bstep (se 1 (by rfl) ⟨1613906, by rfl⟩ : syracuseStep 2151875 = 3227813) B3227813
theorem B2151905 : Blo 1433536 2151905 := bstep (se 2 (by rfl) ⟨806964, by rfl⟩ : syracuseStep 2151905 = 1613929) B1613929
theorem B7362019 : Blo 1433536 7362019 := bstep (se 1 (by rfl) ⟨5521514, by rfl⟩ : syracuseStep 7362019 = 11043029) B11043029
theorem B2151923 : Blo 1433536 2151923 := bstep (se 1 (by rfl) ⟨1613942, by rfl⟩ : syracuseStep 2151923 = 3227885) B3227885
theorem B2151953 : Blo 1433536 2151953 := bstep (se 2 (by rfl) ⟨806982, by rfl⟩ : syracuseStep 2151953 = 1613965) B1613965
theorem B2422291 : Blo 1433536 2422291 := bstep (se 1 (by rfl) ⟨1816718, by rfl⟩ : syracuseStep 2422291 = 3633437) B3633437
theorem B2151971 : Blo 1433536 2151971 := bstep (se 1 (by rfl) ⟨1613978, by rfl⟩ : syracuseStep 2151971 = 3227957) B3227957
theorem B2152001 : Blo 1433536 2152001 := bstep (se 2 (by rfl) ⟨807000, by rfl⟩ : syracuseStep 2152001 = 1614001) B1614001
theorem B4838993 : Blo 1433536 4838993 := bstep (se 2 (by rfl) ⟨1814622, by rfl⟩ : syracuseStep 4838993 = 3629245) B3629245
theorem B2152019 : Blo 1433536 2152019 := bstep (se 1 (by rfl) ⟨1614014, by rfl⟩ : syracuseStep 2152019 = 3228029) B3228029
theorem B2152049 : Blo 1433536 2152049 := bstep (se 2 (by rfl) ⟨807018, by rfl⟩ : syracuseStep 2152049 = 1614037) B1614037
theorem B4421251 : Blo 1433536 4421251 := bstep (se 1 (by rfl) ⟨3315938, by rfl⟩ : syracuseStep 4421251 = 6631877) B6631877
theorem B2152067 : Blo 1433536 2152067 := bstep (se 1 (by rfl) ⟨1614050, by rfl⟩ : syracuseStep 2152067 = 3228101) B3228101
theorem B2152097 : Blo 1433536 2152097 := bstep (se 2 (by rfl) ⟨807036, by rfl⟩ : syracuseStep 2152097 = 1614073) B1614073
theorem B2422433 : Blo 1433536 2422433 := bstep (se 2 (by rfl) ⟨908412, by rfl⟩ : syracuseStep 2422433 = 1816825) B1816825
theorem B2152115 : Blo 1433536 2152115 := bstep (se 1 (by rfl) ⟨1614086, by rfl⟩ : syracuseStep 2152115 = 3228173) B3228173
theorem B4085453 : Blo 1433536 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B2152145 : Blo 1433536 2152145 := bstep (se 2 (by rfl) ⟨807054, by rfl⟩ : syracuseStep 2152145 = 1614109) B1614109
theorem B16332515 : Blo 1433536 16332515 := bstep (se 1 (by rfl) ⟨12249386, by rfl⟩ : syracuseStep 16332515 = 24498773) B24498773
theorem B2152163 : Blo 1433536 2152163 := bstep (se 1 (by rfl) ⟨1614122, by rfl⟩ : syracuseStep 2152163 = 3228245) B3228245
theorem B2152193 : Blo 1433536 2152193 := bstep (se 2 (by rfl) ⟨807072, by rfl⟩ : syracuseStep 2152193 = 1614145) B1614145
theorem B12252941 : Blo 1433536 12252941 := bstep (se 3 (by rfl) ⟨2297426, by rfl⟩ : syracuseStep 12252941 = 4594853) B4594853
theorem B3446545 : Blo 1433536 3446545 := bstep (se 2 (by rfl) ⟨1292454, by rfl⟩ : syracuseStep 3446545 = 2584909) B2584909
theorem B2152211 : Blo 1433536 2152211 := bstep (se 1 (by rfl) ⟨1614158, by rfl⟩ : syracuseStep 2152211 = 3228317) B3228317
theorem B1816339 : Blo 1433536 1816339 := bstep (se 1 (by rfl) ⟨1362254, by rfl⟩ : syracuseStep 1816339 = 2724509) B2724509
theorem B2152241 : Blo 1433536 2152241 := bstep (se 2 (by rfl) ⟨807090, by rfl⟩ : syracuseStep 2152241 = 1614181) B1614181
theorem B2152259 : Blo 1433536 2152259 := bstep (se 1 (by rfl) ⟨1614194, by rfl⟩ : syracuseStep 2152259 = 3228389) B3228389
theorem B2152289 : Blo 1433536 2152289 := bstep (se 2 (by rfl) ⟨807108, by rfl⟩ : syracuseStep 2152289 = 1614217) B1614217
theorem B2152307 : Blo 1433536 2152307 := bstep (se 1 (by rfl) ⟨1614230, by rfl⟩ : syracuseStep 2152307 = 3228461) B3228461
theorem B1816435 : Blo 1433536 1816435 := bstep (se 1 (by rfl) ⟨1362326, by rfl⟩ : syracuseStep 1816435 = 2724653) B2724653
theorem B4085635 : Blo 1433536 4085635 := bstep (se 1 (by rfl) ⟨3064226, by rfl⟩ : syracuseStep 4085635 = 6128453) B6128453
theorem B149157773 : Blo 1433536 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B2152337 : Blo 1433536 2152337 := bstep (se 2 (by rfl) ⟨807126, by rfl⟩ : syracuseStep 2152337 = 1614253) B1614253
theorem B3192721 : Blo 1433536 3192721 := bstep (se 2 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 3192721 = 2394541) B2394541
theorem B5445539 : Blo 1433536 5445539 := bstep (se 1 (by rfl) ⟨4084154, by rfl⟩ : syracuseStep 5445539 = 8168309) B8168309
theorem B2152355 : Blo 1433536 2152355 := bstep (se 1 (by rfl) ⟨1614266, by rfl⟩ : syracuseStep 2152355 = 3228533) B3228533
theorem B2152385 : Blo 1433536 2152385 := bstep (se 2 (by rfl) ⟨807144, by rfl⟩ : syracuseStep 2152385 = 1614289) B1614289
theorem B2152403 : Blo 1433536 2152403 := bstep (se 1 (by rfl) ⟨1614302, by rfl⟩ : syracuseStep 2152403 = 3228605) B3228605
theorem B20674531 : Blo 1433536 20674531 := bstep (se 1 (by rfl) ⟨15505898, by rfl⟩ : syracuseStep 20674531 = 31011797) B31011797
theorem B10344419 : Blo 1433536 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B2586595 : Blo 1433536 2586595 := bstep (se 1 (by rfl) ⟨1939946, by rfl⟩ : syracuseStep 2586595 = 3879893) B3879893
theorem B7264241 : Blo 1433536 7264241 := bstep (se 2 (by rfl) ⟨2724090, by rfl⟩ : syracuseStep 7264241 = 5448181) B5448181
theorem B2152433 : Blo 1433536 2152433 := bstep (se 2 (by rfl) ⟨807162, by rfl⟩ : syracuseStep 2152433 = 1614325) B1614325
theorem B2152451 : Blo 1433536 2152451 := bstep (se 1 (by rfl) ⟨1614338, by rfl⟩ : syracuseStep 2152451 = 3228677) B3228677
theorem B14718989 : Blo 1433536 14718989 := bstep (se 3 (by rfl) ⟨2759810, by rfl⟩ : syracuseStep 14718989 = 5519621) B5519621
theorem B3225617 : Blo 1433536 3225617 := bstep (se 2 (by rfl) ⟨1209606, by rfl⟩ : syracuseStep 3225617 = 2419213) B2419213
theorem B2152481 : Blo 1433536 2152481 := bstep (se 2 (by rfl) ⟨807180, by rfl⟩ : syracuseStep 2152481 = 1614361) B1614361
theorem B3225635 : Blo 1433536 3225635 := bstep (se 1 (by rfl) ⟨2419226, by rfl⟩ : syracuseStep 3225635 = 4838453) B4838453
theorem B4085795 : Blo 1433536 4085795 := bstep (se 1 (by rfl) ⟨3064346, by rfl⟩ : syracuseStep 4085795 = 6128693) B6128693
theorem B2152499 : Blo 1433536 2152499 := bstep (se 1 (by rfl) ⟨1614374, by rfl⟩ : syracuseStep 2152499 = 3228749) B3228749
theorem B2152529 : Blo 1433536 2152529 := bstep (se 2 (by rfl) ⟨807198, by rfl⟩ : syracuseStep 2152529 = 1614397) B1614397
theorem B2152547 : Blo 1433536 2152547 := bstep (se 1 (by rfl) ⟨1614410, by rfl⟩ : syracuseStep 2152547 = 3228821) B3228821
theorem B4839533 : Blo 1433536 4839533 := bstep (se 3 (by rfl) ⟨907412, by rfl⟩ : syracuseStep 4839533 = 1814825) B1814825
theorem B2152577 : Blo 1433536 2152577 := bstep (se 2 (by rfl) ⟨807216, by rfl⟩ : syracuseStep 2152577 = 1614433) B1614433
theorem B2586755 : Blo 1433536 2586755 := bstep (se 1 (by rfl) ⟨1940066, by rfl⟩ : syracuseStep 2586755 = 3880133) B3880133
theorem B8173709 : Blo 1433536 8173709 := bstep (se 3 (by rfl) ⟨1532570, by rfl⟩ : syracuseStep 8173709 = 3065141) B3065141
theorem B2152595 : Blo 1433536 2152595 := bstep (se 1 (by rfl) ⟨1614446, by rfl⟩ : syracuseStep 2152595 = 3228893) B3228893
theorem B4839587 : Blo 1433536 4839587 := bstep (se 1 (by rfl) ⟨3629690, by rfl⟩ : syracuseStep 4839587 = 7259381) B7259381
theorem B3061937 : Blo 1433536 3061937 := bstep (se 2 (by rfl) ⟨1148226, by rfl⟩ : syracuseStep 3061937 = 2296453) B2296453
theorem B2152625 : Blo 1433536 2152625 := bstep (se 2 (by rfl) ⟨807234, by rfl⟩ : syracuseStep 2152625 = 1614469) B1614469
theorem B3061955 : Blo 1433536 3061955 := bstep (se 1 (by rfl) ⟨2296466, by rfl⟩ : syracuseStep 3061955 = 4592933) B4592933
theorem B2152643 : Blo 1433536 2152643 := bstep (se 1 (by rfl) ⟨1614482, by rfl⟩ : syracuseStep 2152643 = 3228965) B3228965
theorem B2152673 : Blo 1433536 2152673 := bstep (se 2 (by rfl) ⟨807252, by rfl⟩ : syracuseStep 2152673 = 1614505) B1614505
theorem B13785329 : Blo 1433536 13785329 := bstep (se 2 (by rfl) ⟨5169498, by rfl⟩ : syracuseStep 13785329 = 10338997) B10338997
theorem B2152691 : Blo 1433536 2152691 := bstep (se 1 (by rfl) ⟨1614518, by rfl⟩ : syracuseStep 2152691 = 3229037) B3229037
theorem B2152721 : Blo 1433536 2152721 := bstep (se 2 (by rfl) ⟨807270, by rfl⟩ : syracuseStep 2152721 = 1614541) B1614541
theorem B2152739 : Blo 1433536 2152739 := bstep (se 1 (by rfl) ⟨1614554, by rfl⟩ : syracuseStep 2152739 = 3229109) B3229109
theorem B2906417 : Blo 1433536 2906417 := bstep (se 2 (by rfl) ⟨1089906, by rfl⟩ : syracuseStep 2906417 = 2179813) B2179813
theorem B3225905 : Blo 1433536 3225905 := bstep (se 2 (by rfl) ⟨1209714, by rfl⟩ : syracuseStep 3225905 = 2419429) B2419429
theorem B2152769 : Blo 1433536 2152769 := bstep (se 2 (by rfl) ⟨807288, by rfl⟩ : syracuseStep 2152769 = 1614577) B1614577
theorem B3225923 : Blo 1433536 3225923 := bstep (se 1 (by rfl) ⟨2419442, by rfl⟩ : syracuseStep 3225923 = 4838885) B4838885
theorem B2152787 : Blo 1433536 2152787 := bstep (se 1 (by rfl) ⟨1614590, by rfl⟩ : syracuseStep 2152787 = 3229181) B3229181
theorem B4594033 : Blo 1433536 4594033 := bstep (se 2 (by rfl) ⟨1722762, by rfl⟩ : syracuseStep 4594033 = 3445525) B3445525
theorem B2152817 : Blo 1433536 2152817 := bstep (se 2 (by rfl) ⟨807306, by rfl⟩ : syracuseStep 2152817 = 1614613) B1614613
theorem B2152835 : Blo 1433536 2152835 := bstep (se 1 (by rfl) ⟨1614626, by rfl⟩ : syracuseStep 2152835 = 3229253) B3229253
theorem B12417421 : Blo 1433536 12417421 := bstep (se 3 (by rfl) ⟨2328266, by rfl⟩ : syracuseStep 12417421 = 4656533) B4656533
theorem B2152865 : Blo 1433536 2152865 := bstep (se 2 (by rfl) ⟨807324, by rfl⟩ : syracuseStep 2152865 = 1614649) B1614649
theorem B4839857 : Blo 1433536 4839857 := bstep (se 2 (by rfl) ⟨1814946, by rfl⟩ : syracuseStep 4839857 = 3629893) B3629893
theorem B2152883 : Blo 1433536 2152883 := bstep (se 1 (by rfl) ⟨1614662, by rfl⟩ : syracuseStep 2152883 = 3229325) B3229325
theorem B5241293 : Blo 1433536 5241293 := bstep (se 3 (by rfl) ⟨982742, by rfl⟩ : syracuseStep 5241293 = 1965485) B1965485
theorem B2152913 : Blo 1433536 2152913 := bstep (se 2 (by rfl) ⟨807342, by rfl⟩ : syracuseStep 2152913 = 1614685) B1614685
theorem B2152931 : Blo 1433536 2152931 := bstep (se 1 (by rfl) ⟨1614698, by rfl⟩ : syracuseStep 2152931 = 3229397) B3229397
theorem B11049443 : Blo 1433536 11049443 := bstep (se 1 (by rfl) ⟨8287082, by rfl⟩ : syracuseStep 11049443 = 16574165) B16574165
theorem B2152961 : Blo 1433536 2152961 := bstep (se 2 (by rfl) ⟨807360, by rfl⟩ : syracuseStep 2152961 = 1614721) B1614721
theorem B8165893 : Blo 1433536 8165893 := bstep (se 4 (by rfl) ⟨765552, by rfl⟩ : syracuseStep 8165893 = 1531105) B1531105
theorem B2152979 : Blo 1433536 2152979 := bstep (se 1 (by rfl) ⟨1614734, by rfl⟩ : syracuseStep 2152979 = 3229469) B3229469
theorem B2153009 : Blo 1433536 2153009 := bstep (se 2 (by rfl) ⟨807378, by rfl⟩ : syracuseStep 2153009 = 1614757) B1614757
theorem B2153027 : Blo 1433536 2153027 := bstep (se 1 (by rfl) ⟨1614770, by rfl⟩ : syracuseStep 2153027 = 3229541) B3229541
theorem B3226193 : Blo 1433536 3226193 := bstep (se 2 (by rfl) ⟨1209822, by rfl⟩ : syracuseStep 3226193 = 2419645) B2419645
theorem B2153057 : Blo 1433536 2153057 := bstep (se 2 (by rfl) ⟨807396, by rfl⟩ : syracuseStep 2153057 = 1614793) B1614793
theorem B3226211 : Blo 1433536 3226211 := bstep (se 1 (by rfl) ⟨2419658, by rfl⟩ : syracuseStep 3226211 = 4839317) B4839317
theorem B2153075 : Blo 1433536 2153075 := bstep (se 1 (by rfl) ⟨1614806, by rfl⟩ : syracuseStep 2153075 = 3229613) B3229613
theorem B2153105 : Blo 1433536 2153105 := bstep (se 2 (by rfl) ⟨807414, by rfl⟩ : syracuseStep 2153105 = 1614829) B1614829
theorem B2210465 : Blo 1433536 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B2153123 : Blo 1433536 2153123 := bstep (se 1 (by rfl) ⟨1614842, by rfl⟩ : syracuseStep 2153123 = 3229685) B3229685
theorem B2153153 : Blo 1433536 2153153 := bstep (se 2 (by rfl) ⟨807432, by rfl⟩ : syracuseStep 2153153 = 1614865) B1614865
theorem B2153171 : Blo 1433536 2153171 := bstep (se 1 (by rfl) ⟨1614878, by rfl⟩ : syracuseStep 2153171 = 3229757) B3229757
theorem B22092515 : Blo 1433536 22092515 := bstep (se 1 (by rfl) ⟨16569386, by rfl⟩ : syracuseStep 22092515 = 33138773) B33138773
theorem B2153201 : Blo 1433536 2153201 := bstep (se 2 (by rfl) ⟨807450, by rfl⟩ : syracuseStep 2153201 = 1614901) B1614901
theorem B2153219 : Blo 1433536 2153219 := bstep (se 1 (by rfl) ⟨1614914, by rfl⟩ : syracuseStep 2153219 = 3229829) B3229829
theorem B2153249 : Blo 1433536 2153249 := bstep (se 2 (by rfl) ⟨807468, by rfl⟩ : syracuseStep 2153249 = 1614937) B1614937
theorem B2153267 : Blo 1433536 2153267 := bstep (se 1 (by rfl) ⟨1614950, by rfl⟩ : syracuseStep 2153267 = 3229901) B3229901
theorem B2153297 : Blo 1433536 2153297 := bstep (se 2 (by rfl) ⟨807486, by rfl⟩ : syracuseStep 2153297 = 1614973) B1614973
theorem B3226481 : Blo 1433536 3226481 := bstep (se 2 (by rfl) ⟨1209930, by rfl⟩ : syracuseStep 3226481 = 2419861) B2419861
theorem B3226499 : Blo 1433536 3226499 := bstep (se 1 (by rfl) ⟨2419874, by rfl⟩ : syracuseStep 3226499 = 4839749) B4839749
theorem B5446541 : Blo 1433536 5446541 := bstep (se 3 (by rfl) ⟨1021226, by rfl⟩ : syracuseStep 5446541 = 2042453) B2042453
theorem B4840397 : Blo 1433536 4840397 := bstep (se 3 (by rfl) ⟨907574, by rfl⟩ : syracuseStep 4840397 = 1815149) B1815149
theorem B4594637 : Blo 1433536 4594637 := bstep (se 3 (by rfl) ⟨861494, by rfl⟩ : syracuseStep 4594637 = 1722989) B1722989
theorem B1530883 : Blo 1433536 1530883 := bstep (se 1 (by rfl) ⟨1148162, by rfl⟩ : syracuseStep 1530883 = 2296325) B2296325
theorem B4840451 : Blo 1433536 4840451 := bstep (se 1 (by rfl) ⟨3630338, by rfl⟩ : syracuseStep 4840451 = 7260677) B7260677
theorem B8174641 : Blo 1433536 8174641 := bstep (se 2 (by rfl) ⟨3065490, by rfl⟩ : syracuseStep 8174641 = 6130981) B6130981
theorem B1612867 : Blo 1433536 1612867 := bstep (se 1 (by rfl) ⟨1209650, by rfl⟩ : syracuseStep 1612867 = 2419301) B2419301
theorem B4086865 : Blo 1433536 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B17439857 : Blo 1433536 17439857 := bstep (se 2 (by rfl) ⟨6539946, by rfl⟩ : syracuseStep 17439857 = 13079893) B13079893
theorem B3226769 : Blo 1433536 3226769 := bstep (se 2 (by rfl) ⟨1210038, by rfl⟩ : syracuseStep 3226769 = 2420077) B2420077
theorem B3226787 : Blo 1433536 3226787 := bstep (se 1 (by rfl) ⟨2420090, by rfl⟩ : syracuseStep 3226787 = 4840181) B4840181
theorem B1613011 : Blo 1433536 1613011 := bstep (se 1 (by rfl) ⟨1209758, by rfl⟩ : syracuseStep 1613011 = 2419517) B2419517
theorem B4840721 : Blo 1433536 4840721 := bstep (se 2 (by rfl) ⟨1815270, by rfl⟩ : syracuseStep 4840721 = 3630541) B3630541
theorem B10894661 : Blo 1433536 10894661 := bstep (se 4 (by rfl) ⟨1021374, by rfl⟩ : syracuseStep 10894661 = 2042749) B2042749
theorem B1613155 : Blo 1433536 1613155 := bstep (se 1 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 1613155 = 2419733) B2419733
theorem B19619185 : Blo 1433536 19619185 := bstep (se 2 (by rfl) ⟨7357194, by rfl⟩ : syracuseStep 19619185 = 14714389) B14714389
theorem B7265699 : Blo 1433536 7265699 := bstep (se 1 (by rfl) ⟨5449274, by rfl⟩ : syracuseStep 7265699 = 10898549) B10898549
theorem B3227057 : Blo 1433536 3227057 := bstep (se 2 (by rfl) ⟨1210146, by rfl⟩ : syracuseStep 3227057 = 2420293) B2420293
theorem B3227075 : Blo 1433536 3227075 := bstep (se 1 (by rfl) ⟨2420306, by rfl⟩ : syracuseStep 3227075 = 4840613) B4840613
theorem B1613299 : Blo 1433536 1613299 := bstep (se 1 (by rfl) ⟨1209974, by rfl⟩ : syracuseStep 1613299 = 2419949) B2419949
theorem B11042317 : Blo 1433536 11042317 := bstep (se 3 (by rfl) ⟨2070434, by rfl⟩ : syracuseStep 11042317 = 4140869) B4140869
theorem B1613443 : Blo 1433536 1613443 := bstep (se 1 (by rfl) ⟨1210082, by rfl⟩ : syracuseStep 1613443 = 2420165) B2420165
theorem B3628739 : Blo 1433536 3628739 := bstep (se 1 (by rfl) ⟨2721554, by rfl⟩ : syracuseStep 3628739 = 5443109) B5443109
theorem B3227345 : Blo 1433536 3227345 := bstep (se 2 (by rfl) ⟨1210254, by rfl⟩ : syracuseStep 3227345 = 2420509) B2420509
theorem B6889187 : Blo 1433536 6889187 := bstep (se 1 (by rfl) ⟨5166890, by rfl⟩ : syracuseStep 6889187 = 10333781) B10333781
theorem B3227363 : Blo 1433536 3227363 := bstep (se 1 (by rfl) ⟨2420522, by rfl⟩ : syracuseStep 3227363 = 4841045) B4841045
theorem B1613587 : Blo 1433536 1613587 := bstep (se 1 (by rfl) ⟨1210190, by rfl⟩ : syracuseStep 1613587 = 2420381) B2420381
theorem B4841261 : Blo 1433536 4841261 := bstep (se 3 (by rfl) ⟨907736, by rfl⟩ : syracuseStep 4841261 = 1815473) B1815473
theorem B4841315 : Blo 1433536 4841315 := bstep (se 1 (by rfl) ⟨3630986, by rfl⟩ : syracuseStep 4841315 = 7261973) B7261973
theorem B1613731 : Blo 1433536 1613731 := bstep (se 1 (by rfl) ⟨1210298, by rfl⟩ : syracuseStep 1613731 = 2420597) B2420597
theorem B1433539 : Blo 1433536 1433539 := bstep (se 1 (by rfl) ⟨1075154, by rfl⟩ : syracuseStep 1433539 = 2150309) B2150309
theorem B1433555 : Blo 1433536 1433555 := bstep (se 1 (by rfl) ⟨1075166, by rfl⟩ : syracuseStep 1433555 = 2150333) B2150333
theorem B1433571 : Blo 1433536 1433571 := bstep (se 1 (by rfl) ⟨1075178, by rfl⟩ : syracuseStep 1433571 = 2150357) B2150357
theorem B7757795 : Blo 1433536 7757795 := bstep (se 1 (by rfl) ⟨5818346, by rfl⟩ : syracuseStep 7757795 = 11636693) B11636693
theorem B3227633 : Blo 1433536 3227633 := bstep (se 2 (by rfl) ⟨1210362, by rfl⟩ : syracuseStep 3227633 = 2420725) B2420725
theorem B1433587 : Blo 1433536 1433587 := bstep (se 1 (by rfl) ⟨1075190, by rfl⟩ : syracuseStep 1433587 = 2150381) B2150381
theorem B1531891 : Blo 1433536 1531891 := bstep (se 1 (by rfl) ⟨1148918, by rfl⟩ : syracuseStep 1531891 = 2297837) B2297837
theorem B1433611 : Blo 1433536 1433611 := bstep (se 1 (by rfl) ⟨1075208, by rfl⟩ : syracuseStep 1433611 = 2150417) B2150417
theorem B1433623 : Blo 1433536 1433623 := bstep (se 1 (by rfl) ⟨1075217, by rfl⟩ : syracuseStep 1433623 = 2150435) B2150435
theorem B1433643 : Blo 1433536 1433643 := bstep (se 1 (by rfl) ⟨1075232, by rfl⟩ : syracuseStep 1433643 = 2150465) B2150465
theorem B5169197 : Blo 1433536 5169197 := bstep (se 3 (by rfl) ⟨969224, by rfl⟩ : syracuseStep 5169197 = 1938449) B1938449
theorem B9814061 : Blo 1433536 9814061 := bstep (se 3 (by rfl) ⟨1840136, by rfl⟩ : syracuseStep 9814061 = 3680273) B3680273
theorem B1433655 : Blo 1433536 1433655 := bstep (se 1 (by rfl) ⟨1075241, by rfl⟩ : syracuseStep 1433655 = 2150483) B2150483
theorem B1433675 : Blo 1433536 1433675 := bstep (se 1 (by rfl) ⟨1075256, by rfl⟩ : syracuseStep 1433675 = 2150513) B2150513
theorem B3227723 : Blo 1433536 3227723 := bstep (se 1 (by rfl) ⟨2420792, by rfl⟩ : syracuseStep 3227723 = 4841585) B4841585
theorem B1433687 : Blo 1433536 1433687 := bstep (se 1 (by rfl) ⟨1075265, by rfl⟩ : syracuseStep 1433687 = 2150531) B2150531
theorem B1613911 : Blo 1433536 1613911 := bstep (se 1 (by rfl) ⟨1210433, by rfl⟩ : syracuseStep 1613911 = 2420867) B2420867
theorem B1433707 : Blo 1433536 1433707 := bstep (se 1 (by rfl) ⟨1075280, by rfl⟩ : syracuseStep 1433707 = 2150561) B2150561
theorem B1433719 : Blo 1433536 1433719 := bstep (se 1 (by rfl) ⟨1075289, by rfl⟩ : syracuseStep 1433719 = 2150579) B2150579
theorem B3227777 : Blo 1433536 3227777 := bstep (se 2 (by rfl) ⟨1210416, by rfl⟩ : syracuseStep 3227777 = 2420833) B2420833
theorem B1433739 : Blo 1433536 1433739 := bstep (se 1 (by rfl) ⟨1075304, by rfl⟩ : syracuseStep 1433739 = 2150609) B2150609
theorem B1433751 : Blo 1433536 1433751 := bstep (se 1 (by rfl) ⟨1075313, by rfl⟩ : syracuseStep 1433751 = 2150627) B2150627
theorem B1433771 : Blo 1433536 1433771 := bstep (se 1 (by rfl) ⟨1075328, by rfl⟩ : syracuseStep 1433771 = 2150657) B2150657
theorem B1433783 : Blo 1433536 1433783 := bstep (se 1 (by rfl) ⟨1075337, by rfl⟩ : syracuseStep 1433783 = 2150675) B2150675
theorem B1433803 : Blo 1433536 1433803 := bstep (se 1 (by rfl) ⟨1075352, by rfl⟩ : syracuseStep 1433803 = 2150705) B2150705
theorem B1433815 : Blo 1433536 1433815 := bstep (se 1 (by rfl) ⟨1075361, by rfl⟩ : syracuseStep 1433815 = 2150723) B2150723
theorem B4841693 : Blo 1433536 4841693 := bstep (se 3 (by rfl) ⟨907817, by rfl⟩ : syracuseStep 4841693 = 1815635) B1815635
theorem B1433835 : Blo 1433536 1433835 := bstep (se 1 (by rfl) ⟨1075376, by rfl⟩ : syracuseStep 1433835 = 2150753) B2150753
theorem B1433847 : Blo 1433536 1433847 := bstep (se 1 (by rfl) ⟨1075385, by rfl⟩ : syracuseStep 1433847 = 2150771) B2150771
theorem B1433867 : Blo 1433536 1433867 := bstep (se 1 (by rfl) ⟨1075400, by rfl⟩ : syracuseStep 1433867 = 2150801) B2150801
theorem B1614091 : Blo 1433536 1614091 := bstep (se 1 (by rfl) ⟨1210568, by rfl⟩ : syracuseStep 1614091 = 2421137) B2421137
theorem B10895633 : Blo 1433536 10895633 := bstep (se 2 (by rfl) ⟨4085862, by rfl⟩ : syracuseStep 10895633 = 8171725) B8171725
theorem B1433879 : Blo 1433536 1433879 := bstep (se 1 (by rfl) ⟨1075409, by rfl⟩ : syracuseStep 1433879 = 2150819) B2150819
theorem B1433899 : Blo 1433536 1433899 := bstep (se 1 (by rfl) ⟨1075424, by rfl⟩ : syracuseStep 1433899 = 2150849) B2150849
theorem B1433911 : Blo 1433536 1433911 := bstep (se 1 (by rfl) ⟨1075433, by rfl⟩ : syracuseStep 1433911 = 2150867) B2150867
theorem B3629387 : Blo 1433536 3629387 := bstep (se 1 (by rfl) ⟨2722040, by rfl⟩ : syracuseStep 3629387 = 5444081) B5444081
theorem B1433931 : Blo 1433536 1433931 := bstep (se 1 (by rfl) ⟨1075448, by rfl⟩ : syracuseStep 1433931 = 2150897) B2150897
theorem B1433943 : Blo 1433536 1433943 := bstep (se 1 (by rfl) ⟨1075457, by rfl⟩ : syracuseStep 1433943 = 2150915) B2150915
theorem B3227993 : Blo 1433536 3227993 := bstep (se 2 (by rfl) ⟨1210497, by rfl⟩ : syracuseStep 3227993 = 2420995) B2420995
theorem B1433963 : Blo 1433536 1433963 := bstep (se 1 (by rfl) ⟨1075472, by rfl⟩ : syracuseStep 1433963 = 2150945) B2150945
theorem B1433975 : Blo 1433536 1433975 := bstep (se 1 (by rfl) ⟨1075481, by rfl⟩ : syracuseStep 1433975 = 2150963) B2150963
theorem B1614199 : Blo 1433536 1614199 := bstep (se 1 (by rfl) ⟨1210649, by rfl⟩ : syracuseStep 1614199 = 2421299) B2421299
theorem B1433995 : Blo 1433536 1433995 := bstep (se 1 (by rfl) ⟨1075496, by rfl⟩ : syracuseStep 1433995 = 2150993) B2150993
theorem B1434007 : Blo 1433536 1434007 := bstep (se 1 (by rfl) ⟨1075505, by rfl⟩ : syracuseStep 1434007 = 2151011) B2151011
theorem B1434027 : Blo 1433536 1434027 := bstep (se 1 (by rfl) ⟨1075520, by rfl⟩ : syracuseStep 1434027 = 2151041) B2151041
theorem B3228083 : Blo 1433536 3228083 := bstep (se 1 (by rfl) ⟨2421062, by rfl⟩ : syracuseStep 3228083 = 4842125) B4842125
theorem B1434039 : Blo 1433536 1434039 := bstep (se 1 (by rfl) ⟨1075529, by rfl⟩ : syracuseStep 1434039 = 2151059) B2151059
theorem B1434059 : Blo 1433536 1434059 := bstep (se 1 (by rfl) ⟨1075544, by rfl⟩ : syracuseStep 1434059 = 2151089) B2151089
theorem B1434071 : Blo 1433536 1434071 := bstep (se 1 (by rfl) ⟨1075553, by rfl⟩ : syracuseStep 1434071 = 2151107) B2151107
theorem B3228119 : Blo 1433536 3228119 := bstep (se 1 (by rfl) ⟨2421089, by rfl⟩ : syracuseStep 3228119 = 4842179) B4842179
theorem B1434091 : Blo 1433536 1434091 := bstep (se 1 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 1434091 = 2151137) B2151137
theorem B1434103 : Blo 1433536 1434103 := bstep (se 1 (by rfl) ⟨1075577, by rfl⟩ : syracuseStep 1434103 = 2151155) B2151155
theorem B3064321 : Blo 1433536 3064321 := bstep (se 2 (by rfl) ⟨1149120, by rfl⟩ : syracuseStep 3064321 = 2298241) B2298241
theorem B1434123 : Blo 1433536 1434123 := bstep (se 1 (by rfl) ⟨1075592, by rfl⟩ : syracuseStep 1434123 = 2151185) B2151185
theorem B16556561 : Blo 1433536 16556561 := bstep (se 2 (by rfl) ⟨6208710, by rfl⟩ : syracuseStep 16556561 = 12417421) B12417421
theorem B7266833 : Blo 1433536 7266833 := bstep (se 2 (by rfl) ⟨2725062, by rfl⟩ : syracuseStep 7266833 = 5450125) B5450125
theorem B1434135 : Blo 1433536 1434135 := bstep (se 1 (by rfl) ⟨1075601, by rfl⟩ : syracuseStep 1434135 = 2151203) B2151203
theorem B1434155 : Blo 1433536 1434155 := bstep (se 1 (by rfl) ⟨1075616, by rfl⟩ : syracuseStep 1434155 = 2151233) B2151233
theorem B1614379 : Blo 1433536 1614379 := bstep (se 1 (by rfl) ⟨1210784, by rfl⟩ : syracuseStep 1614379 = 2421569) B2421569
theorem B1434167 : Blo 1433536 1434167 := bstep (se 1 (by rfl) ⟨1075625, by rfl⟩ : syracuseStep 1434167 = 2151251) B2151251
theorem B1434187 : Blo 1433536 1434187 := bstep (se 1 (by rfl) ⟨1075640, by rfl⟩ : syracuseStep 1434187 = 2151281) B2151281
theorem B1434199 : Blo 1433536 1434199 := bstep (se 1 (by rfl) ⟨1075649, by rfl⟩ : syracuseStep 1434199 = 2151299) B2151299
theorem B1434219 : Blo 1433536 1434219 := bstep (se 1 (by rfl) ⟨1075664, by rfl⟩ : syracuseStep 1434219 = 2151329) B2151329
theorem B1434231 : Blo 1433536 1434231 := bstep (se 1 (by rfl) ⟨1075673, by rfl⟩ : syracuseStep 1434231 = 2151347) B2151347
theorem B1434251 : Blo 1433536 1434251 := bstep (se 1 (by rfl) ⟨1075688, by rfl⟩ : syracuseStep 1434251 = 2151377) B2151377
theorem B3228299 : Blo 1433536 3228299 := bstep (se 1 (by rfl) ⟨2421224, by rfl⟩ : syracuseStep 3228299 = 4842449) B4842449
theorem B1434263 : Blo 1433536 1434263 := bstep (se 1 (by rfl) ⟨1075697, by rfl⟩ : syracuseStep 1434263 = 2151395) B2151395
theorem B1614487 : Blo 1433536 1614487 := bstep (se 1 (by rfl) ⟨1210865, by rfl⟩ : syracuseStep 1614487 = 2421731) B2421731
theorem B1434283 : Blo 1433536 1434283 := bstep (se 1 (by rfl) ⟨1075712, by rfl⟩ : syracuseStep 1434283 = 2151425) B2151425
theorem B10887857 : Blo 1433536 10887857 := bstep (se 2 (by rfl) ⟨4082946, by rfl⟩ : syracuseStep 10887857 = 8165893) B8165893
theorem B7266995 : Blo 1433536 7266995 := bstep (se 1 (by rfl) ⟨5450246, by rfl⟩ : syracuseStep 7266995 = 10900493) B10900493
theorem B20677301 : Blo 1433536 20677301 := bstep (se 5 (by rfl) ⟨969248, by rfl⟩ : syracuseStep 20677301 = 1938497) B1938497
theorem B1434295 : Blo 1433536 1434295 := bstep (se 1 (by rfl) ⟨1075721, by rfl⟩ : syracuseStep 1434295 = 2151443) B2151443
theorem B3228353 : Blo 1433536 3228353 := bstep (se 2 (by rfl) ⟨1210632, by rfl⟩ : syracuseStep 3228353 = 2421265) B2421265
theorem B1434315 : Blo 1433536 1434315 := bstep (se 1 (by rfl) ⟨1075736, by rfl⟩ : syracuseStep 1434315 = 2151473) B2151473
theorem B1434327 : Blo 1433536 1434327 := bstep (se 1 (by rfl) ⟨1075745, by rfl⟩ : syracuseStep 1434327 = 2151491) B2151491
theorem B1434347 : Blo 1433536 1434347 := bstep (se 1 (by rfl) ⟨1075760, by rfl⟩ : syracuseStep 1434347 = 2151521) B2151521
theorem B1434359 : Blo 1433536 1434359 := bstep (se 1 (by rfl) ⟨1075769, by rfl⟩ : syracuseStep 1434359 = 2151539) B2151539
theorem B1434379 : Blo 1433536 1434379 := bstep (se 1 (by rfl) ⟨1075784, by rfl⟩ : syracuseStep 1434379 = 2151569) B2151569
theorem B1434391 : Blo 1433536 1434391 := bstep (se 1 (by rfl) ⟨1075793, by rfl⟩ : syracuseStep 1434391 = 2151587) B2151587
theorem B1434411 : Blo 1433536 1434411 := bstep (se 1 (by rfl) ⟨1075808, by rfl⟩ : syracuseStep 1434411 = 2151617) B2151617
theorem B1434423 : Blo 1433536 1434423 := bstep (se 1 (by rfl) ⟨1075817, by rfl⟩ : syracuseStep 1434423 = 2151635) B2151635
theorem B1434443 : Blo 1433536 1434443 := bstep (se 1 (by rfl) ⟨1075832, by rfl⟩ : syracuseStep 1434443 = 2151665) B2151665
theorem B1614667 : Blo 1433536 1614667 := bstep (se 1 (by rfl) ⟨1211000, by rfl⟩ : syracuseStep 1614667 = 2422001) B2422001
theorem B1434455 : Blo 1433536 1434455 := bstep (se 1 (by rfl) ⟨1075841, by rfl⟩ : syracuseStep 1434455 = 2151683) B2151683
theorem B1434475 : Blo 1433536 1434475 := bstep (se 1 (by rfl) ⟨1075856, by rfl⟩ : syracuseStep 1434475 = 2151713) B2151713
theorem B1434487 : Blo 1433536 1434487 := bstep (se 1 (by rfl) ⟨1075865, by rfl⟩ : syracuseStep 1434487 = 2151731) B2151731
theorem B1434507 : Blo 1433536 1434507 := bstep (se 1 (by rfl) ⟨1075880, by rfl⟩ : syracuseStep 1434507 = 2151761) B2151761
theorem B1434519 : Blo 1433536 1434519 := bstep (se 1 (by rfl) ⟨1075889, by rfl⟩ : syracuseStep 1434519 = 2151779) B2151779
theorem B3228569 : Blo 1433536 3228569 := bstep (se 2 (by rfl) ⟨1210713, by rfl⟩ : syracuseStep 3228569 = 2421427) B2421427
theorem B1434539 : Blo 1433536 1434539 := bstep (se 1 (by rfl) ⟨1075904, by rfl⟩ : syracuseStep 1434539 = 2151809) B2151809
theorem B1434551 : Blo 1433536 1434551 := bstep (se 1 (by rfl) ⟨1075913, by rfl⟩ : syracuseStep 1434551 = 2151827) B2151827
theorem B1614775 : Blo 1433536 1614775 := bstep (se 1 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 1614775 = 2422163) B2422163
theorem B1434571 : Blo 1433536 1434571 := bstep (se 1 (by rfl) ⟨1075928, by rfl⟩ : syracuseStep 1434571 = 2151857) B2151857
theorem B1434583 : Blo 1433536 1434583 := bstep (se 1 (by rfl) ⟨1075937, by rfl⟩ : syracuseStep 1434583 = 2151875) B2151875
theorem B1434603 : Blo 1433536 1434603 := bstep (se 1 (by rfl) ⟨1075952, by rfl⟩ : syracuseStep 1434603 = 2151905) B2151905
theorem B3228659 : Blo 1433536 3228659 := bstep (se 1 (by rfl) ⟨2421494, by rfl⟩ : syracuseStep 3228659 = 4842989) B4842989
theorem B1434615 : Blo 1433536 1434615 := bstep (se 1 (by rfl) ⟨1075961, by rfl⟩ : syracuseStep 1434615 = 2151923) B2151923
theorem B1434635 : Blo 1433536 1434635 := bstep (se 1 (by rfl) ⟨1075976, by rfl⟩ : syracuseStep 1434635 = 2151953) B2151953
theorem B1434647 : Blo 1433536 1434647 := bstep (se 1 (by rfl) ⟨1075985, by rfl⟩ : syracuseStep 1434647 = 2151971) B2151971
theorem B3228695 : Blo 1433536 3228695 := bstep (se 1 (by rfl) ⟨2421521, by rfl⟩ : syracuseStep 3228695 = 4843043) B4843043
theorem B1434667 : Blo 1433536 1434667 := bstep (se 1 (by rfl) ⟨1076000, by rfl⟩ : syracuseStep 1434667 = 2152001) B2152001
theorem B1434679 : Blo 1433536 1434679 := bstep (se 1 (by rfl) ⟨1076009, by rfl⟩ : syracuseStep 1434679 = 2152019) B2152019
theorem B1434699 : Blo 1433536 1434699 := bstep (se 1 (by rfl) ⟨1076024, by rfl⟩ : syracuseStep 1434699 = 2152049) B2152049
theorem B1434711 : Blo 1433536 1434711 := bstep (se 1 (by rfl) ⟨1076033, by rfl⟩ : syracuseStep 1434711 = 2152067) B2152067
theorem B1434731 : Blo 1433536 1434731 := bstep (se 1 (by rfl) ⟨1076048, by rfl⟩ : syracuseStep 1434731 = 2152097) B2152097
theorem B1614955 : Blo 1433536 1614955 := bstep (se 1 (by rfl) ⟨1211216, by rfl⟩ : syracuseStep 1614955 = 2422433) B2422433
theorem B1434743 : Blo 1433536 1434743 := bstep (se 1 (by rfl) ⟨1076057, by rfl⟩ : syracuseStep 1434743 = 2152115) B2152115
theorem B1434763 : Blo 1433536 1434763 := bstep (se 1 (by rfl) ⟨1076072, by rfl⟩ : syracuseStep 1434763 = 2152145) B2152145
theorem B10888343 : Blo 1433536 10888343 := bstep (se 1 (by rfl) ⟨8166257, by rfl⟩ : syracuseStep 10888343 = 16332515) B16332515
theorem B1434775 : Blo 1433536 1434775 := bstep (se 1 (by rfl) ⟨1076081, by rfl⟩ : syracuseStep 1434775 = 2152163) B2152163
theorem B1434795 : Blo 1433536 1434795 := bstep (se 1 (by rfl) ⟨1076096, by rfl⟩ : syracuseStep 1434795 = 2152193) B2152193
theorem B8168627 : Blo 1433536 8168627 := bstep (se 1 (by rfl) ⟨6126470, by rfl⟩ : syracuseStep 8168627 = 12252941) B12252941
theorem B62080181 : Blo 1433536 62080181 := bstep (se 5 (by rfl) ⟨2910008, by rfl⟩ : syracuseStep 62080181 = 5820017) B5820017
theorem B1434807 : Blo 1433536 1434807 := bstep (se 1 (by rfl) ⟨1076105, by rfl⟩ : syracuseStep 1434807 = 2152211) B2152211
theorem B1434827 : Blo 1433536 1434827 := bstep (se 1 (by rfl) ⟨1076120, by rfl⟩ : syracuseStep 1434827 = 2152241) B2152241
theorem B3228875 : Blo 1433536 3228875 := bstep (se 1 (by rfl) ⟨2421656, by rfl⟩ : syracuseStep 3228875 = 4843313) B4843313
theorem B1434839 : Blo 1433536 1434839 := bstep (se 1 (by rfl) ⟨1076129, by rfl⟩ : syracuseStep 1434839 = 2152259) B2152259
theorem B1434859 : Blo 1433536 1434859 := bstep (se 1 (by rfl) ⟨1076144, by rfl⟩ : syracuseStep 1434859 = 2152289) B2152289
theorem B1434871 : Blo 1433536 1434871 := bstep (se 1 (by rfl) ⟨1076153, by rfl⟩ : syracuseStep 1434871 = 2152307) B2152307
theorem B3228929 : Blo 1433536 3228929 := bstep (se 2 (by rfl) ⟨1210848, by rfl⟩ : syracuseStep 3228929 = 2421697) B2421697
theorem B1434891 : Blo 1433536 1434891 := bstep (se 1 (by rfl) ⟨1076168, by rfl⟩ : syracuseStep 1434891 = 2152337) B2152337
theorem B3630359 : Blo 1433536 3630359 := bstep (se 1 (by rfl) ⟨2722769, by rfl⟩ : syracuseStep 3630359 = 5445539) B5445539
theorem B1434903 : Blo 1433536 1434903 := bstep (se 1 (by rfl) ⟨1076177, by rfl⟩ : syracuseStep 1434903 = 2152355) B2152355
theorem B1434923 : Blo 1433536 1434923 := bstep (se 1 (by rfl) ⟨1076192, by rfl⟩ : syracuseStep 1434923 = 2152385) B2152385
theorem B1434935 : Blo 1433536 1434935 := bstep (se 1 (by rfl) ⟨1076201, by rfl⟩ : syracuseStep 1434935 = 2152403) B2152403
theorem B4842827 : Blo 1433536 4842827 := bstep (se 1 (by rfl) ⟨3632120, by rfl⟩ : syracuseStep 4842827 = 7264241) B7264241
theorem B1434955 : Blo 1433536 1434955 := bstep (se 1 (by rfl) ⟨1076216, by rfl⟩ : syracuseStep 1434955 = 2152433) B2152433
theorem B1434967 : Blo 1433536 1434967 := bstep (se 1 (by rfl) ⟨1076225, by rfl⟩ : syracuseStep 1434967 = 2152451) B2152451
theorem B1434987 : Blo 1433536 1434987 := bstep (se 1 (by rfl) ⟨1076240, by rfl⟩ : syracuseStep 1434987 = 2152481) B2152481
theorem B1434999 : Blo 1433536 1434999 := bstep (se 1 (by rfl) ⟨1076249, by rfl⟩ : syracuseStep 1434999 = 2152499) B2152499
theorem B1435019 : Blo 1433536 1435019 := bstep (se 1 (by rfl) ⟨1076264, by rfl⟩ : syracuseStep 1435019 = 2152529) B2152529
theorem B7259543 : Blo 1433536 7259543 := bstep (se 1 (by rfl) ⟨5444657, by rfl⟩ : syracuseStep 7259543 = 10889315) B10889315
theorem B1435031 : Blo 1433536 1435031 := bstep (se 1 (by rfl) ⟨1076273, by rfl⟩ : syracuseStep 1435031 = 2152547) B2152547
theorem B1435051 : Blo 1433536 1435051 := bstep (se 1 (by rfl) ⟨1076288, by rfl⟩ : syracuseStep 1435051 = 2152577) B2152577
theorem B5449139 : Blo 1433536 5449139 := bstep (se 1 (by rfl) ⟨4086854, by rfl⟩ : syracuseStep 5449139 = 8173709) B8173709
theorem B1435063 : Blo 1433536 1435063 := bstep (se 1 (by rfl) ⟨1076297, by rfl⟩ : syracuseStep 1435063 = 2152595) B2152595
theorem B5449153 : Blo 1433536 5449153 := bstep (se 2 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 5449153 = 4086865) B4086865
theorem B2041291 : Blo 1433536 2041291 := bstep (se 1 (by rfl) ⟨1530968, by rfl⟩ : syracuseStep 2041291 = 3061937) B3061937
theorem B1435083 : Blo 1433536 1435083 := bstep (se 1 (by rfl) ⟨1076312, by rfl⟩ : syracuseStep 1435083 = 2152625) B2152625
theorem B2041303 : Blo 1433536 2041303 := bstep (se 1 (by rfl) ⟨1530977, by rfl⟩ : syracuseStep 2041303 = 3061955) B3061955
theorem B1435095 : Blo 1433536 1435095 := bstep (se 1 (by rfl) ⟨1076321, by rfl⟩ : syracuseStep 1435095 = 2152643) B2152643
theorem B3229145 : Blo 1433536 3229145 := bstep (se 2 (by rfl) ⟨1210929, by rfl⟩ : syracuseStep 3229145 = 2421859) B2421859
theorem B3065303 : Blo 1433536 3065303 := bstep (se 1 (by rfl) ⟨2298977, by rfl⟩ : syracuseStep 3065303 = 4597955) B4597955
theorem B1435115 : Blo 1433536 1435115 := bstep (se 1 (by rfl) ⟨1076336, by rfl⟩ : syracuseStep 1435115 = 2152673) B2152673
theorem B1435127 : Blo 1433536 1435127 := bstep (se 1 (by rfl) ⟨1076345, by rfl⟩ : syracuseStep 1435127 = 2152691) B2152691
theorem B1435147 : Blo 1433536 1435147 := bstep (se 1 (by rfl) ⟨1076360, by rfl⟩ : syracuseStep 1435147 = 2152721) B2152721
theorem B1435159 : Blo 1433536 1435159 := bstep (se 1 (by rfl) ⟨1076369, by rfl⟩ : syracuseStep 1435159 = 2152739) B2152739
theorem B1435179 : Blo 1433536 1435179 := bstep (se 1 (by rfl) ⟨1076384, by rfl⟩ : syracuseStep 1435179 = 2152769) B2152769
theorem B3229235 : Blo 1433536 3229235 := bstep (se 1 (by rfl) ⟨2421926, by rfl⟩ : syracuseStep 3229235 = 4843853) B4843853
theorem B1435191 : Blo 1433536 1435191 := bstep (se 1 (by rfl) ⟨1076393, by rfl⟩ : syracuseStep 1435191 = 2152787) B2152787
theorem B11036225 : Blo 1433536 11036225 := bstep (se 2 (by rfl) ⟨4138584, by rfl⟩ : syracuseStep 11036225 = 8277169) B8277169
theorem B1435211 : Blo 1433536 1435211 := bstep (se 1 (by rfl) ⟨1076408, by rfl⟩ : syracuseStep 1435211 = 2152817) B2152817
theorem B1435223 : Blo 1433536 1435223 := bstep (se 1 (by rfl) ⟨1076417, by rfl⟩ : syracuseStep 1435223 = 2152835) B2152835
theorem B3229271 : Blo 1433536 3229271 := bstep (se 1 (by rfl) ⟨2421953, by rfl⟩ : syracuseStep 3229271 = 4843907) B4843907
theorem B4843097 : Blo 1433536 4843097 := bstep (se 2 (by rfl) ⟨1816161, by rfl⟩ : syracuseStep 4843097 = 3632323) B3632323
theorem B13092445 : Blo 1433536 13092445 := bstep (se 3 (by rfl) ⟨2454833, by rfl⟩ : syracuseStep 13092445 = 4909667) B4909667
theorem B1435243 : Blo 1433536 1435243 := bstep (se 1 (by rfl) ⟨1076432, by rfl⟩ : syracuseStep 1435243 = 2152865) B2152865
theorem B1435255 : Blo 1433536 1435255 := bstep (se 1 (by rfl) ⟨1076441, by rfl⟩ : syracuseStep 1435255 = 2152883) B2152883
theorem B1435275 : Blo 1433536 1435275 := bstep (se 1 (by rfl) ⟨1076456, by rfl⟩ : syracuseStep 1435275 = 2152913) B2152913
theorem B1435287 : Blo 1433536 1435287 := bstep (se 1 (by rfl) ⟨1076465, by rfl⟩ : syracuseStep 1435287 = 2152931) B2152931
theorem B7366295 : Blo 1433536 7366295 := bstep (se 1 (by rfl) ⟨5524721, by rfl⟩ : syracuseStep 7366295 = 11049443) B11049443
theorem B1435307 : Blo 1433536 1435307 := bstep (se 1 (by rfl) ⟨1076480, by rfl⟩ : syracuseStep 1435307 = 2152961) B2152961
theorem B1435319 : Blo 1433536 1435319 := bstep (se 1 (by rfl) ⟨1076489, by rfl⟩ : syracuseStep 1435319 = 2152979) B2152979
theorem B1435339 : Blo 1433536 1435339 := bstep (se 1 (by rfl) ⟨1076504, by rfl⟩ : syracuseStep 1435339 = 2153009) B2153009
theorem B1435351 : Blo 1433536 1435351 := bstep (se 1 (by rfl) ⟨1076513, by rfl⟩ : syracuseStep 1435351 = 2153027) B2153027
theorem B4597469 : Blo 1433536 4597469 := bstep (se 3 (by rfl) ⟨862025, by rfl⟩ : syracuseStep 4597469 = 1724051) B1724051
theorem B1435371 : Blo 1433536 1435371 := bstep (se 1 (by rfl) ⟨1076528, by rfl⟩ : syracuseStep 1435371 = 2153057) B2153057
theorem B1435383 : Blo 1433536 1435383 := bstep (se 1 (by rfl) ⟨1076537, by rfl⟩ : syracuseStep 1435383 = 2153075) B2153075
theorem B3229451 : Blo 1433536 3229451 := bstep (se 1 (by rfl) ⟨2422088, by rfl⟩ : syracuseStep 3229451 = 4844177) B4844177
theorem B1435403 : Blo 1433536 1435403 := bstep (se 1 (by rfl) ⟨1076552, by rfl⟩ : syracuseStep 1435403 = 2153105) B2153105
theorem B12257041 : Blo 1433536 12257041 := bstep (se 2 (by rfl) ⟨4596390, by rfl⟩ : syracuseStep 12257041 = 9192781) B9192781
theorem B1435415 : Blo 1433536 1435415 := bstep (se 1 (by rfl) ⟨1076561, by rfl⟩ : syracuseStep 1435415 = 2153123) B2153123
theorem B1435435 : Blo 1433536 1435435 := bstep (se 1 (by rfl) ⟨1076576, by rfl⟩ : syracuseStep 1435435 = 2153153) B2153153
theorem B1435447 : Blo 1433536 1435447 := bstep (se 1 (by rfl) ⟨1076585, by rfl⟩ : syracuseStep 1435447 = 2153171) B2153171
theorem B26158913 : Blo 1433536 26158913 := bstep (se 2 (by rfl) ⟨9809592, by rfl⟩ : syracuseStep 26158913 = 19619185) B19619185
theorem B3229505 : Blo 1433536 3229505 := bstep (se 2 (by rfl) ⟨1211064, by rfl⟩ : syracuseStep 3229505 = 2422129) B2422129
theorem B1435467 : Blo 1433536 1435467 := bstep (se 1 (by rfl) ⟨1076600, by rfl⟩ : syracuseStep 1435467 = 2153201) B2153201
theorem B1435479 : Blo 1433536 1435479 := bstep (se 1 (by rfl) ⟨1076609, by rfl⟩ : syracuseStep 1435479 = 2153219) B2153219
theorem B2328409 : Blo 1433536 2328409 := bstep (se 2 (by rfl) ⟨873153, by rfl⟩ : syracuseStep 2328409 = 1746307) B1746307
theorem B1435499 : Blo 1433536 1435499 := bstep (se 1 (by rfl) ⟨1076624, by rfl⟩ : syracuseStep 1435499 = 2153249) B2153249
theorem B1435511 : Blo 1433536 1435511 := bstep (se 1 (by rfl) ⟨1076633, by rfl⟩ : syracuseStep 1435511 = 2153267) B2153267
theorem B1435531 : Blo 1433536 1435531 := bstep (se 1 (by rfl) ⟨1076648, by rfl⟩ : syracuseStep 1435531 = 2153297) B2153297
theorem B3631027 : Blo 1433536 3631027 := bstep (se 1 (by rfl) ⟨2723270, by rfl⟩ : syracuseStep 3631027 = 5446541) B5446541
theorem B3065867 : Blo 1433536 3065867 := bstep (se 1 (by rfl) ⟨2299400, by rfl⟩ : syracuseStep 3065867 = 4598801) B4598801
theorem B14723089 : Blo 1433536 14723089 := bstep (se 2 (by rfl) ⟨5521158, by rfl⟩ : syracuseStep 14723089 = 11042317) B11042317
theorem B3229721 : Blo 1433536 3229721 := bstep (se 2 (by rfl) ⟨1211145, by rfl⟩ : syracuseStep 3229721 = 2422291) B2422291
theorem B12257315 : Blo 1433536 12257315 := bstep (se 1 (by rfl) ⟨9192986, by rfl⟩ : syracuseStep 12257315 = 18385973) B18385973
theorem B3631169 : Blo 1433536 3631169 := bstep (se 2 (by rfl) ⟨1361688, by rfl⟩ : syracuseStep 3631169 = 2723377) B2723377
theorem B11626571 : Blo 1433536 11626571 := bstep (se 1 (by rfl) ⟨8719928, by rfl⟩ : syracuseStep 11626571 = 17439857) B17439857
theorem B3229811 : Blo 1433536 3229811 := bstep (se 1 (by rfl) ⟨2422358, by rfl⟩ : syracuseStep 3229811 = 4844717) B4844717
theorem B3229847 : Blo 1433536 3229847 := bstep (se 1 (by rfl) ⟨2422385, by rfl⟩ : syracuseStep 3229847 = 4844771) B4844771
theorem B2721995 : Blo 1433536 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B4843799 : Blo 1433536 4843799 := bstep (se 1 (by rfl) ⟨3632849, by rfl⟩ : syracuseStep 4843799 = 7265699) B7265699
theorem B88279409 : Blo 1433536 88279409 := bstep (se 2 (by rfl) ⟨33104778, by rfl⟩ : syracuseStep 88279409 = 66209557) B66209557
theorem B2722177 : Blo 1433536 2722177 := bstep (se 2 (by rfl) ⟨1020816, by rfl⟩ : syracuseStep 2722177 = 2041633) B2041633
theorem B6130093 : Blo 1433536 6130093 := bstep (se 3 (by rfl) ⟨1149392, by rfl⟩ : syracuseStep 6130093 = 2298785) B2298785
theorem B2419159 : Blo 1433536 2419159 := bstep (se 1 (by rfl) ⟨1814369, by rfl⟩ : syracuseStep 2419159 = 3628739) B3628739
theorem B2296345 : Blo 1433536 2296345 := bstep (se 2 (by rfl) ⟨861129, by rfl⟩ : syracuseStep 2296345 = 1722259) B1722259
theorem B5171777 : Blo 1433536 5171777 := bstep (se 2 (by rfl) ⟨1939416, by rfl⟩ : syracuseStep 5171777 = 3878833) B3878833
theorem B4598365 : Blo 1433536 4598365 := bstep (se 3 (by rfl) ⟨862193, by rfl⟩ : syracuseStep 4598365 = 1724387) B1724387
theorem B8170085 : Blo 1433536 8170085 := bstep (se 4 (by rfl) ⟨765945, by rfl⟩ : syracuseStep 8170085 = 1531891) B1531891
theorem B5171863 : Blo 1433536 5171863 := bstep (se 1 (by rfl) ⟨3878897, by rfl⟩ : syracuseStep 5171863 = 7757795) B7757795
theorem B2296601 : Blo 1433536 2296601 := bstep (se 2 (by rfl) ⟨861225, by rfl⟩ : syracuseStep 2296601 = 1722451) B1722451
theorem B4844339 : Blo 1433536 4844339 := bstep (se 1 (by rfl) ⟨3633254, by rfl⟩ : syracuseStep 4844339 = 7266509) B7266509
theorem B2452427 : Blo 1433536 2452427 := bstep (se 1 (by rfl) ⟨1839320, by rfl⟩ : syracuseStep 2452427 = 3678641) B3678641
theorem B1723339 : Blo 1433536 1723339 := bstep (se 1 (by rfl) ⟨1292504, by rfl⟩ : syracuseStep 1723339 = 2585009) B2585009
theorem B68111381 : Blo 1433536 68111381 := bstep (se 6 (by rfl) ⟨1596360, by rfl⟩ : syracuseStep 68111381 = 3192721) B3192721
theorem B8170541 : Blo 1433536 8170541 := bstep (se 3 (by rfl) ⟨1531976, by rfl⟩ : syracuseStep 8170541 = 3063953) B3063953
theorem B4844609 : Blo 1433536 4844609 := bstep (se 2 (by rfl) ⟨1816728, by rfl⟩ : syracuseStep 4844609 = 3633457) B3633457
theorem B2419787 : Blo 1433536 2419787 := bstep (se 1 (by rfl) ⟨1814840, by rfl⟩ : syracuseStep 2419787 = 3629681) B3629681
theorem B7752779 : Blo 1433536 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B2722891 : Blo 1433536 2722891 := bstep (se 1 (by rfl) ⟨2042168, by rfl⟩ : syracuseStep 2722891 = 4084337) B4084337
theorem B9194627 : Blo 1433536 9194627 := bstep (se 1 (by rfl) ⟨6895970, by rfl⟩ : syracuseStep 9194627 = 13791941) B13791941
theorem B2452619 : Blo 1433536 2452619 := bstep (se 1 (by rfl) ⟨1839464, by rfl⟩ : syracuseStep 2452619 = 3678929) B3678929
theorem B2722967 : Blo 1433536 2722967 := bstep (se 1 (by rfl) ⟨2042225, by rfl⟩ : syracuseStep 2722967 = 4084451) B4084451
theorem B2419915 : Blo 1433536 2419915 := bstep (se 1 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 2419915 = 3629873) B3629873
theorem B3681587 : Blo 1433536 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B3632435 : Blo 1433536 3632435 := bstep (se 1 (by rfl) ⟨2724326, by rfl⟩ : syracuseStep 3632435 = 5448653) B5448653
theorem B2796865 : Blo 1433536 2796865 := bstep (se 2 (by rfl) ⟨1048824, by rfl⟩ : syracuseStep 2796865 = 2097649) B2097649
theorem B1453387 : Blo 1433536 1453387 := bstep (se 1 (by rfl) ⟨1090040, by rfl⟩ : syracuseStep 1453387 = 2180081) B2180081
theorem B2420057 : Blo 1433536 2420057 := bstep (se 2 (by rfl) ⟨907521, by rfl⟩ : syracuseStep 2420057 = 1815043) B1815043
theorem B11627869 : Blo 1433536 11627869 := bstep (se 3 (by rfl) ⟨2180225, by rfl⟩ : syracuseStep 11627869 = 4360451) B4360451
theorem B5172659 : Blo 1433536 5172659 := bstep (se 1 (by rfl) ⟨3879494, by rfl⟩ : syracuseStep 5172659 = 7758989) B7758989
theorem B2420185 : Blo 1433536 2420185 := bstep (se 2 (by rfl) ⟨907569, by rfl⟩ : syracuseStep 2420185 = 1815139) B1815139
theorem B2043353 : Blo 1433536 2043353 := bstep (se 2 (by rfl) ⟨766257, by rfl⟩ : syracuseStep 2043353 = 1532515) B1532515
theorem B3878551 : Blo 1433536 3878551 := bstep (se 1 (by rfl) ⟨2908913, by rfl⟩ : syracuseStep 3878551 = 5817827) B5817827
theorem B8171225 : Blo 1433536 8171225 := bstep (se 2 (by rfl) ⟨3064209, by rfl⟩ : syracuseStep 8171225 = 6128419) B6128419
theorem B2723635 : Blo 1433536 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B3632971 : Blo 1433536 3632971 := bstep (se 1 (by rfl) ⟨2724728, by rfl⟩ : syracuseStep 3632971 = 5449457) B5449457
theorem B58896305 : Blo 1433536 58896305 := bstep (se 2 (by rfl) ⟨22086114, by rfl⟩ : syracuseStep 58896305 = 44172229) B44172229
theorem B99438515 : Blo 1433536 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B3633113 : Blo 1433536 3633113 := bstep (se 2 (by rfl) ⟨1362417, by rfl⟩ : syracuseStep 3633113 = 2724835) B2724835
theorem B2150411 : Blo 1433536 2150411 := bstep (se 1 (by rfl) ⟨1612808, by rfl⟩ : syracuseStep 2150411 = 3225617) B3225617
theorem B2150423 : Blo 1433536 2150423 := bstep (se 1 (by rfl) ⟨1612817, by rfl⟩ : syracuseStep 2150423 = 3225635) B3225635
theorem B2420759 : Blo 1433536 2420759 := bstep (se 1 (by rfl) ⟨1815569, by rfl⟩ : syracuseStep 2420759 = 3631139) B3631139
theorem B2723863 : Blo 1433536 2723863 := bstep (se 1 (by rfl) ⟨2042897, by rfl⟩ : syracuseStep 2723863 = 4085795) B4085795
theorem B10334243 : Blo 1433536 10334243 := bstep (se 1 (by rfl) ⟨7750682, by rfl⟩ : syracuseStep 10334243 = 15501365) B15501365
theorem B10899521 : Blo 1433536 10899521 := bstep (se 2 (by rfl) ⟨4087320, by rfl⟩ : syracuseStep 10899521 = 8174641) B8174641
theorem B1724503 : Blo 1433536 1724503 := bstep (se 1 (by rfl) ⟨1293377, by rfl⟩ : syracuseStep 1724503 = 2586755) B2586755
theorem B2150489 : Blo 1433536 2150489 := bstep (se 2 (by rfl) ⟨806433, by rfl⟩ : syracuseStep 2150489 = 1612867) B1612867
theorem B6131801 : Blo 1433536 6131801 := bstep (se 2 (by rfl) ⟨2299425, by rfl⟩ : syracuseStep 6131801 = 4598851) B4598851
theorem B2723969 : Blo 1433536 2723969 := bstep (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) B2042977
theorem B2420887 : Blo 1433536 2420887 := bstep (se 1 (by rfl) ⟨1815665, by rfl⟩ : syracuseStep 2420887 = 3631331) B3631331
theorem B1937611 : Blo 1433536 1937611 := bstep (se 1 (by rfl) ⟨1453208, by rfl⟩ : syracuseStep 1937611 = 2906417) B2906417
theorem B2150603 : Blo 1433536 2150603 := bstep (se 1 (by rfl) ⟨1612952, by rfl⟩ : syracuseStep 2150603 = 3225905) B3225905
theorem B2150615 : Blo 1433536 2150615 := bstep (se 1 (by rfl) ⟨1612961, by rfl⟩ : syracuseStep 2150615 = 3225923) B3225923
theorem B6123737 : Blo 1433536 6123737 := bstep (se 2 (by rfl) ⟨2296401, by rfl⟩ : syracuseStep 6123737 = 4592803) B4592803
theorem B2150681 : Blo 1433536 2150681 := bstep (se 2 (by rfl) ⟨806505, by rfl⟩ : syracuseStep 2150681 = 1613011) B1613011
theorem B2724121 : Blo 1433536 2724121 := bstep (se 2 (by rfl) ⟨1021545, by rfl⟩ : syracuseStep 2724121 = 2043091) B2043091
theorem B3494195 : Blo 1433536 3494195 := bstep (se 1 (by rfl) ⟨2620646, by rfl⟩ : syracuseStep 3494195 = 5241293) B5241293
theorem B2150795 : Blo 1433536 2150795 := bstep (se 1 (by rfl) ⟨1613096, by rfl⟩ : syracuseStep 2150795 = 3226193) B3226193
theorem B2150807 : Blo 1433536 2150807 := bstep (se 1 (by rfl) ⟨1613105, by rfl⟩ : syracuseStep 2150807 = 3226211) B3226211
theorem B1814987 : Blo 1433536 1814987 := bstep (se 1 (by rfl) ⟨1361240, by rfl⟩ : syracuseStep 1814987 = 2722481) B2722481
theorem B2150873 : Blo 1433536 2150873 := bstep (se 2 (by rfl) ⟨806577, by rfl⟩ : syracuseStep 2150873 = 1613155) B1613155
theorem B1438187 : Blo 1433536 1438187 := bstep (se 1 (by rfl) ⟨1078640, by rfl⟩ : syracuseStep 1438187 = 2157281) B2157281
theorem B2150987 : Blo 1433536 2150987 := bstep (se 1 (by rfl) ⟨1613240, by rfl⟩ : syracuseStep 2150987 = 3226481) B3226481
theorem B2150999 : Blo 1433536 2150999 := bstep (se 1 (by rfl) ⟨1613249, by rfl⟩ : syracuseStep 2150999 = 3226499) B3226499
theorem B2585239 : Blo 1433536 2585239 := bstep (se 1 (by rfl) ⟨1938929, by rfl⟩ : syracuseStep 2585239 = 3877859) B3877859
theorem B2151065 : Blo 1433536 2151065 := bstep (se 2 (by rfl) ⟨806649, by rfl⟩ : syracuseStep 2151065 = 1613299) B1613299
theorem B4141747 : Blo 1433536 4141747 := bstep (se 1 (by rfl) ⟨3106310, by rfl⟩ : syracuseStep 4141747 = 6212621) B6212621
theorem B2151179 : Blo 1433536 2151179 := bstep (se 1 (by rfl) ⟨1613384, by rfl⟩ : syracuseStep 2151179 = 3226769) B3226769
theorem B2421515 : Blo 1433536 2421515 := bstep (se 1 (by rfl) ⟨1816136, by rfl⟩ : syracuseStep 2421515 = 3632273) B3632273
theorem B9573137 : Blo 1433536 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B2151191 : Blo 1433536 2151191 := bstep (se 1 (by rfl) ⟨1613393, by rfl⟩ : syracuseStep 2151191 = 3226787) B3226787
theorem B2151257 : Blo 1433536 2151257 := bstep (se 2 (by rfl) ⟨806721, by rfl⟩ : syracuseStep 2151257 = 1613443) B1613443
theorem B5895001 : Blo 1433536 5895001 := bstep (se 2 (by rfl) ⟨2210625, by rfl⟩ : syracuseStep 5895001 = 4421251) B4421251
theorem B4838237 : Blo 1433536 4838237 := bstep (se 3 (by rfl) ⟨907169, by rfl⟩ : syracuseStep 4838237 = 1814339) B1814339
theorem B7263107 : Blo 1433536 7263107 := bstep (se 1 (by rfl) ⟨5447330, by rfl⟩ : syracuseStep 7263107 = 10894661) B10894661
theorem B2421643 : Blo 1433536 2421643 := bstep (se 1 (by rfl) ⟨1816232, by rfl⟩ : syracuseStep 2421643 = 3632465) B3632465
theorem B2151371 : Blo 1433536 2151371 := bstep (se 1 (by rfl) ⟨1613528, by rfl⟩ : syracuseStep 2151371 = 3227057) B3227057
theorem B2151383 : Blo 1433536 2151383 := bstep (se 1 (by rfl) ⟨1613537, by rfl⟩ : syracuseStep 2151383 = 3227075) B3227075
theorem B1089483797 : Blo 1433536 1089483797 := bstep (se 6 (by rfl) ⟨25534776, by rfl⟩ : syracuseStep 1089483797 = 51069553) B51069553
theorem B2151449 : Blo 1433536 2151449 := bstep (se 2 (by rfl) ⟨806793, by rfl⟩ : syracuseStep 2151449 = 1613587) B1613587
theorem B2421785 : Blo 1433536 2421785 := bstep (se 2 (by rfl) ⟨908169, by rfl⟩ : syracuseStep 2421785 = 1816339) B1816339
theorem B2151563 : Blo 1433536 2151563 := bstep (se 1 (by rfl) ⟨1613672, by rfl⟩ : syracuseStep 2151563 = 3227345) B3227345
theorem B1815691 : Blo 1433536 1815691 := bstep (se 1 (by rfl) ⟨1361768, by rfl⟩ : syracuseStep 1815691 = 2723537) B2723537
theorem B4592791 : Blo 1433536 4592791 := bstep (se 1 (by rfl) ⟨3444593, by rfl⟩ : syracuseStep 4592791 = 6889187) B6889187
theorem B2151575 : Blo 1433536 2151575 := bstep (se 1 (by rfl) ⟨1613681, by rfl⟩ : syracuseStep 2151575 = 3227363) B3227363
theorem B2421913 : Blo 1433536 2421913 := bstep (se 2 (by rfl) ⟨908217, by rfl⟩ : syracuseStep 2421913 = 1816435) B1816435
theorem B2151641 : Blo 1433536 2151641 := bstep (se 2 (by rfl) ⟨806865, by rfl⟩ : syracuseStep 2151641 = 1613731) B1613731
theorem B1553623 : Blo 1433536 1553623 := bstep (se 1 (by rfl) ⟨1165217, by rfl⟩ : syracuseStep 1553623 = 2330435) B2330435
theorem B2151755 : Blo 1433536 2151755 := bstep (se 1 (by rfl) ⟨1613816, by rfl⟩ : syracuseStep 2151755 = 3227633) B3227633
theorem B2151767 : Blo 1433536 2151767 := bstep (se 1 (by rfl) ⟨1613825, by rfl⟩ : syracuseStep 2151767 = 3227651) B3227651
theorem B8164709 : Blo 1433536 8164709 := bstep (se 4 (by rfl) ⟨765441, by rfl⟩ : syracuseStep 8164709 = 1530883) B1530883
theorem B1815959 : Blo 1433536 1815959 := bstep (se 1 (by rfl) ⟨1361969, by rfl⟩ : syracuseStep 1815959 = 2723939) B2723939
theorem B2151833 : Blo 1433536 2151833 := bstep (se 2 (by rfl) ⟨806937, by rfl⟩ : syracuseStep 2151833 = 1613875) B1613875
theorem B6125003 : Blo 1433536 6125003 := bstep (se 1 (by rfl) ⟨4593752, by rfl⟩ : syracuseStep 6125003 = 9187505) B9187505
theorem B1635799 : Blo 1433536 1635799 := bstep (se 1 (by rfl) ⟨1226849, by rfl⟩ : syracuseStep 1635799 = 2453699) B2453699
theorem B2151947 : Blo 1433536 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B2151959 : Blo 1433536 2151959 := bstep (se 1 (by rfl) ⟨1613969, by rfl⟩ : syracuseStep 2151959 = 3227939) B3227939
theorem B2152025 : Blo 1433536 2152025 := bstep (se 2 (by rfl) ⟨807009, by rfl⟩ : syracuseStep 2152025 = 1614019) B1614019
theorem B5445251 : Blo 1433536 5445251 := bstep (se 1 (by rfl) ⟨4083938, by rfl⟩ : syracuseStep 5445251 = 8167877) B8167877
theorem B5445265 : Blo 1433536 5445265 := bstep (se 2 (by rfl) ⟨2041974, by rfl⟩ : syracuseStep 5445265 = 4083949) B4083949
theorem B3495575 : Blo 1433536 3495575 := bstep (se 1 (by rfl) ⟨2621681, by rfl⟩ : syracuseStep 3495575 = 5243363) B5243363
theorem B4421323 : Blo 1433536 4421323 := bstep (se 1 (by rfl) ⟨3315992, by rfl⟩ : syracuseStep 4421323 = 6631985) B6631985
theorem B2152139 : Blo 1433536 2152139 := bstep (se 1 (by rfl) ⟨1614104, by rfl⟩ : syracuseStep 2152139 = 3228209) B3228209
theorem B2152151 : Blo 1433536 2152151 := bstep (se 1 (by rfl) ⟨1614113, by rfl⟩ : syracuseStep 2152151 = 3228227) B3228227
theorem B2152217 : Blo 1433536 2152217 := bstep (se 2 (by rfl) ⟨807081, by rfl⟩ : syracuseStep 2152217 = 1614163) B1614163
theorem B6125377 : Blo 1433536 6125377 := bstep (se 2 (by rfl) ⟨2297016, by rfl⟩ : syracuseStep 6125377 = 4594033) B4594033
theorem B4085579 : Blo 1433536 4085579 := bstep (se 1 (by rfl) ⟨3064184, by rfl⟩ : syracuseStep 4085579 = 6128369) B6128369
theorem B3225473 : Blo 1433536 3225473 := bstep (se 2 (by rfl) ⟨1209552, by rfl⟩ : syracuseStep 3225473 = 2419105) B2419105
theorem B2152331 : Blo 1433536 2152331 := bstep (se 1 (by rfl) ⟨1614248, by rfl⟩ : syracuseStep 2152331 = 3228497) B3228497
theorem B2152343 : Blo 1433536 2152343 := bstep (se 1 (by rfl) ⟨1614257, by rfl⟩ : syracuseStep 2152343 = 3228515) B3228515
theorem B5445569 : Blo 1433536 5445569 := bstep (se 2 (by rfl) ⟨2042088, by rfl⟩ : syracuseStep 5445569 = 4084177) B4084177
theorem B4593611 : Blo 1433536 4593611 := bstep (se 1 (by rfl) ⟨3445208, by rfl⟩ : syracuseStep 4593611 = 6890417) B6890417
theorem B4839371 : Blo 1433536 4839371 := bstep (se 1 (by rfl) ⟨3629528, by rfl⟩ : syracuseStep 4839371 = 7259057) B7259057
theorem B2152409 : Blo 1433536 2152409 := bstep (se 2 (by rfl) ⟨807153, by rfl⟩ : syracuseStep 2152409 = 1614307) B1614307
theorem B8165393 : Blo 1433536 8165393 := bstep (se 2 (by rfl) ⟨3062022, by rfl⟩ : syracuseStep 8165393 = 6124045) B6124045
theorem B2152523 : Blo 1433536 2152523 := bstep (se 1 (by rfl) ⟨1614392, by rfl⟩ : syracuseStep 2152523 = 3228785) B3228785
theorem B2152535 : Blo 1433536 2152535 := bstep (se 1 (by rfl) ⟨1614401, by rfl⟩ : syracuseStep 2152535 = 3228803) B3228803
theorem B1816663 : Blo 1433536 1816663 := bstep (se 1 (by rfl) ⟨1362497, by rfl⟩ : syracuseStep 1816663 = 2724995) B2724995
theorem B3225689 : Blo 1433536 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B6125719 : Blo 1433536 6125719 := bstep (se 1 (by rfl) ⟨4594289, by rfl⟩ : syracuseStep 6125719 = 9188579) B9188579
theorem B2152601 : Blo 1433536 2152601 := bstep (se 2 (by rfl) ⟨807225, by rfl⟩ : syracuseStep 2152601 = 1614451) B1614451
theorem B3225779 : Blo 1433536 3225779 := bstep (se 1 (by rfl) ⟨2419334, by rfl⟩ : syracuseStep 3225779 = 4838669) B4838669
theorem B18381005 : Blo 1433536 18381005 := bstep (se 3 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 18381005 = 6892877) B6892877
theorem B3225815 : Blo 1433536 3225815 := bstep (se 1 (by rfl) ⟨2419361, by rfl⟩ : syracuseStep 3225815 = 4838723) B4838723
theorem B4839641 : Blo 1433536 4839641 := bstep (se 2 (by rfl) ⟨1814865, by rfl⟩ : syracuseStep 4839641 = 3629731) B3629731
theorem B4085977 : Blo 1433536 4085977 := bstep (se 2 (by rfl) ⟨1532241, by rfl⟩ : syracuseStep 4085977 = 3064483) B3064483
theorem B2152715 : Blo 1433536 2152715 := bstep (se 1 (by rfl) ⟨1614536, by rfl⟩ : syracuseStep 2152715 = 3229073) B3229073
theorem B2152727 : Blo 1433536 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B2152793 : Blo 1433536 2152793 := bstep (se 2 (by rfl) ⟨807297, by rfl⟩ : syracuseStep 2152793 = 1614595) B1614595
theorem B3225995 : Blo 1433536 3225995 := bstep (se 1 (by rfl) ⟨2419496, by rfl⟩ : syracuseStep 3225995 = 4838993) B4838993
theorem B3226049 : Blo 1433536 3226049 := bstep (se 2 (by rfl) ⟨1209768, by rfl⟩ : syracuseStep 3226049 = 2419537) B2419537
theorem B2152907 : Blo 1433536 2152907 := bstep (se 1 (by rfl) ⟨1614680, by rfl⟩ : syracuseStep 2152907 = 3229361) B3229361
theorem B2152919 : Blo 1433536 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B2152985 : Blo 1433536 2152985 := bstep (se 2 (by rfl) ⟨807369, by rfl⟩ : syracuseStep 2152985 = 1614739) B1614739
theorem B4594265 : Blo 1433536 4594265 := bstep (se 2 (by rfl) ⟨1722849, by rfl⟩ : syracuseStep 4594265 = 3445699) B3445699
theorem B5446237 : Blo 1433536 5446237 := bstep (se 3 (by rfl) ⟨1021169, by rfl⟩ : syracuseStep 5446237 = 2042339) B2042339
theorem B2153099 : Blo 1433536 2153099 := bstep (se 1 (by rfl) ⟨1614824, by rfl⟩ : syracuseStep 2153099 = 3229649) B3229649
theorem B6896279 : Blo 1433536 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B2153111 : Blo 1433536 2153111 := bstep (se 1 (by rfl) ⟨1614833, by rfl⟩ : syracuseStep 2153111 = 3229667) B3229667
theorem B3226265 : Blo 1433536 3226265 := bstep (se 2 (by rfl) ⟨1209849, by rfl⟩ : syracuseStep 3226265 = 2419699) B2419699
theorem B9812659 : Blo 1433536 9812659 := bstep (se 1 (by rfl) ⟨7359494, by rfl⟩ : syracuseStep 9812659 = 14718989) B14718989
theorem B2153177 : Blo 1433536 2153177 := bstep (se 2 (by rfl) ⟨807441, by rfl⟩ : syracuseStep 2153177 = 1614883) B1614883
theorem B3226355 : Blo 1433536 3226355 := bstep (se 1 (by rfl) ⟨2419766, by rfl⟩ : syracuseStep 3226355 = 4839533) B4839533
theorem B3226391 : Blo 1433536 3226391 := bstep (se 1 (by rfl) ⟨2419793, by rfl⟩ : syracuseStep 3226391 = 4839587) B4839587
theorem B9190219 : Blo 1433536 9190219 := bstep (se 1 (by rfl) ⟨6892664, by rfl⟩ : syracuseStep 9190219 = 13785329) B13785329
theorem B2153291 : Blo 1433536 2153291 := bstep (se 1 (by rfl) ⟨1614968, by rfl⟩ : syracuseStep 2153291 = 3229937) B3229937
theorem B2153303 : Blo 1433536 2153303 := bstep (se 1 (by rfl) ⟨1614977, by rfl⟩ : syracuseStep 2153303 = 3229955) B3229955
theorem B4840343 : Blo 1433536 4840343 := bstep (se 1 (by rfl) ⟨3630257, by rfl⟩ : syracuseStep 4840343 = 7260515) B7260515
theorem B3062681 : Blo 1433536 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B3226571 : Blo 1433536 3226571 := bstep (se 1 (by rfl) ⟨2419928, by rfl⟩ : syracuseStep 3226571 = 4839857) B4839857
theorem B3447755 : Blo 1433536 3447755 := bstep (se 1 (by rfl) ⟨2585816, by rfl⟩ : syracuseStep 3447755 = 5171633) B5171633
theorem B1612759 : Blo 1433536 1612759 := bstep (se 1 (by rfl) ⟨1209569, by rfl⟩ : syracuseStep 1612759 = 2419139) B2419139
theorem B3226625 : Blo 1433536 3226625 := bstep (se 2 (by rfl) ⟨1209984, by rfl⟩ : syracuseStep 3226625 = 2419969) B2419969
theorem B1473643 : Blo 1433536 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B1612939 : Blo 1433536 1612939 := bstep (se 1 (by rfl) ⟨1209704, by rfl⟩ : syracuseStep 1612939 = 2419409) B2419409
theorem B14728343 : Blo 1433536 14728343 := bstep (se 1 (by rfl) ⟨11046257, by rfl⟩ : syracuseStep 14728343 = 22092515) B22092515
theorem B19643597 : Blo 1433536 19643597 := bstep (se 3 (by rfl) ⟨3683174, by rfl⟩ : syracuseStep 19643597 = 7366349) B7366349
theorem B3226841 : Blo 1433536 3226841 := bstep (se 2 (by rfl) ⟨1210065, by rfl⟩ : syracuseStep 3226841 = 2420131) B2420131
theorem B1613047 : Blo 1433536 1613047 := bstep (se 1 (by rfl) ⟨1209785, by rfl⟩ : syracuseStep 1613047 = 2419571) B2419571
theorem B3226931 : Blo 1433536 3226931 := bstep (se 1 (by rfl) ⟨2420198, by rfl⟩ : syracuseStep 3226931 = 4840397) B4840397
theorem B3063091 : Blo 1433536 3063091 := bstep (se 1 (by rfl) ⟨2297318, by rfl⟩ : syracuseStep 3063091 = 4594637) B4594637
theorem B3226967 : Blo 1433536 3226967 := bstep (se 1 (by rfl) ⟨2420225, by rfl⟩ : syracuseStep 3226967 = 4840451) B4840451
theorem B7257437 : Blo 1433536 7257437 := bstep (se 3 (by rfl) ⟨1360769, by rfl⟩ : syracuseStep 7257437 = 2721539) B2721539
theorem B1613227 : Blo 1433536 1613227 := bstep (se 1 (by rfl) ⟨1209920, by rfl⟩ : syracuseStep 1613227 = 2419841) B2419841
theorem B4840883 : Blo 1433536 4840883 := bstep (se 1 (by rfl) ⟨3630662, by rfl⟩ : syracuseStep 4840883 = 7261325) B7261325
theorem B4087219 : Blo 1433536 4087219 := bstep (se 1 (by rfl) ⟨3065414, by rfl⟩ : syracuseStep 4087219 = 6130829) B6130829
theorem B3227147 : Blo 1433536 3227147 := bstep (se 1 (by rfl) ⟨2420360, by rfl⟩ : syracuseStep 3227147 = 4840721) B4840721
theorem B1613335 : Blo 1433536 1613335 := bstep (se 1 (by rfl) ⟨1210001, by rfl⟩ : syracuseStep 1613335 = 2420003) B2420003
theorem B3227201 : Blo 1433536 3227201 := bstep (se 2 (by rfl) ⟨1210200, by rfl⟩ : syracuseStep 3227201 = 2420401) B2420401
theorem B13090369 : Blo 1433536 13090369 := bstep (se 2 (by rfl) ⟨4908888, by rfl⟩ : syracuseStep 13090369 = 9817777) B9817777
theorem B4841153 : Blo 1433536 4841153 := bstep (se 2 (by rfl) ⟨1815432, by rfl⟩ : syracuseStep 4841153 = 3630865) B3630865
theorem B4595393 : Blo 1433536 4595393 := bstep (se 2 (by rfl) ⟨1723272, by rfl⟩ : syracuseStep 4595393 = 3446545) B3446545
theorem B1613515 : Blo 1433536 1613515 := bstep (se 1 (by rfl) ⟨1210136, by rfl⟩ : syracuseStep 1613515 = 2420273) B2420273
theorem B3227417 : Blo 1433536 3227417 := bstep (se 2 (by rfl) ⟨1210281, by rfl⟩ : syracuseStep 3227417 = 2420563) B2420563
theorem B3063577 : Blo 1433536 3063577 := bstep (se 2 (by rfl) ⟨1148841, by rfl⟩ : syracuseStep 3063577 = 2297683) B2297683
theorem B1613623 : Blo 1433536 1613623 := bstep (se 1 (by rfl) ⟨1210217, by rfl⟩ : syracuseStep 1613623 = 2420435) B2420435
theorem B5447513 : Blo 1433536 5447513 := bstep (se 2 (by rfl) ⟨2042817, by rfl⟩ : syracuseStep 5447513 = 4085635) B4085635
theorem B39264101 : Blo 1433536 39264101 := bstep (se 4 (by rfl) ⟨3681009, by rfl⟩ : syracuseStep 39264101 = 7362019) B7362019
theorem B3227507 : Blo 1433536 3227507 := bstep (se 1 (by rfl) ⟨2420630, by rfl⟩ : syracuseStep 3227507 = 4841261) B4841261
theorem B3227543 : Blo 1433536 3227543 := bstep (se 1 (by rfl) ⟨2420657, by rfl⟩ : syracuseStep 3227543 = 4841315) B4841315
theorem B1531819 : Blo 1433536 1531819 := bstep (se 1 (by rfl) ⟨1148864, by rfl⟩ : syracuseStep 1531819 = 2297729) B2297729
theorem B1433547 : Blo 1433536 1433547 := bstep (se 1 (by rfl) ⟨1075160, by rfl⟩ : syracuseStep 1433547 = 2150321) B2150321
theorem B1433559 : Blo 1433536 1433559 := bstep (se 1 (by rfl) ⟨1075169, by rfl⟩ : syracuseStep 1433559 = 2150339) B2150339
theorem B27566041 : Blo 1433536 27566041 := bstep (se 2 (by rfl) ⟨10337265, by rfl⟩ : syracuseStep 27566041 = 20674531) B20674531
theorem B3448793 : Blo 1433536 3448793 := bstep (se 2 (by rfl) ⟨1293297, by rfl⟩ : syracuseStep 3448793 = 2586595) B2586595
theorem B1433579 : Blo 1433536 1433579 := bstep (se 1 (by rfl) ⟨1075184, by rfl⟩ : syracuseStep 1433579 = 2150369) B2150369
theorem B1613803 : Blo 1433536 1613803 := bstep (se 1 (by rfl) ⟨1210352, by rfl⟩ : syracuseStep 1613803 = 2420705) B2420705
theorem B1433591 : Blo 1433536 1433591 := bstep (se 1 (by rfl) ⟨1075193, by rfl⟩ : syracuseStep 1433591 = 2150387) B2150387
theorem B1433607 : Blo 1433536 1433607 := bstep (se 1 (by rfl) ⟨1075205, by rfl⟩ : syracuseStep 1433607 = 2150411) B2150411
theorem B1433615 : Blo 1433536 1433615 := bstep (se 1 (by rfl) ⟨1075211, by rfl⟩ : syracuseStep 1433615 = 2150423) B2150423
theorem B1613839 : Blo 1433536 1613839 := bstep (se 1 (by rfl) ⟨1210379, by rfl⟩ : syracuseStep 1613839 = 2420759) B2420759
theorem B6889495 : Blo 1433536 6889495 := bstep (se 1 (by rfl) ⟨5167121, by rfl⟩ : syracuseStep 6889495 = 10334243) B10334243
theorem B7266347 : Blo 1433536 7266347 := bstep (se 1 (by rfl) ⟨5449760, by rfl⟩ : syracuseStep 7266347 = 10899521) B10899521
theorem B1433659 : Blo 1433536 1433659 := bstep (se 1 (by rfl) ⟨1075244, by rfl⟩ : syracuseStep 1433659 = 2150489) B2150489
theorem B1433735 : Blo 1433536 1433735 := bstep (se 1 (by rfl) ⟨1075301, by rfl⟩ : syracuseStep 1433735 = 2150603) B2150603
theorem B1433743 : Blo 1433536 1433743 := bstep (se 1 (by rfl) ⟨1075307, by rfl⟩ : syracuseStep 1433743 = 2150615) B2150615
theorem B3227795 : Blo 1433536 3227795 := bstep (se 1 (by rfl) ⟨2420846, by rfl⟩ : syracuseStep 3227795 = 4841693) B4841693
theorem B1433787 : Blo 1433536 1433787 := bstep (se 1 (by rfl) ⟨1075340, by rfl⟩ : syracuseStep 1433787 = 2150681) B2150681
theorem B8167625 : Blo 1433536 8167625 := bstep (se 2 (by rfl) ⟨3062859, by rfl⟩ : syracuseStep 8167625 = 6125719) B6125719
theorem B3227849 : Blo 1433536 3227849 := bstep (se 2 (by rfl) ⟨1210443, by rfl⟩ : syracuseStep 3227849 = 2420887) B2420887
theorem B16351469 : Blo 1433536 16351469 := bstep (se 3 (by rfl) ⟨3065900, by rfl⟩ : syracuseStep 16351469 = 6131801) B6131801
theorem B1433863 : Blo 1433536 1433863 := bstep (se 1 (by rfl) ⟨1075397, by rfl⟩ : syracuseStep 1433863 = 2150795) B2150795
theorem B1433871 : Blo 1433536 1433871 := bstep (se 1 (by rfl) ⟨1075403, by rfl⟩ : syracuseStep 1433871 = 2150807) B2150807
theorem B5447969 : Blo 1433536 5447969 := bstep (se 2 (by rfl) ⟨2042988, by rfl⟩ : syracuseStep 5447969 = 4085977) B4085977
theorem B1433915 : Blo 1433536 1433915 := bstep (se 1 (by rfl) ⟨1075436, by rfl⟩ : syracuseStep 1433915 = 2150873) B2150873
theorem B1433991 : Blo 1433536 1433991 := bstep (se 1 (by rfl) ⟨1075493, by rfl⟩ : syracuseStep 1433991 = 2150987) B2150987
theorem B1433999 : Blo 1433536 1433999 := bstep (se 1 (by rfl) ⟨1075499, by rfl⟩ : syracuseStep 1433999 = 2150999) B2150999
theorem B1434043 : Blo 1433536 1434043 := bstep (se 1 (by rfl) ⟨1075532, by rfl⟩ : syracuseStep 1434043 = 2151065) B2151065
theorem B7258571 : Blo 1433536 7258571 := bstep (se 1 (by rfl) ⟨5443928, by rfl⟩ : syracuseStep 7258571 = 10887857) B10887857
theorem B3629569 : Blo 1433536 3629569 := bstep (se 2 (by rfl) ⟨1361088, by rfl⟩ : syracuseStep 3629569 = 2722177) B2722177
theorem B1434119 : Blo 1433536 1434119 := bstep (se 1 (by rfl) ⟨1075589, by rfl⟩ : syracuseStep 1434119 = 2151179) B2151179
theorem B1614343 : Blo 1433536 1614343 := bstep (se 1 (by rfl) ⟨1210757, by rfl⟩ : syracuseStep 1614343 = 2421515) B2421515
theorem B6382091 : Blo 1433536 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B1434127 : Blo 1433536 1434127 := bstep (se 1 (by rfl) ⟨1075595, by rfl⟩ : syracuseStep 1434127 = 2151191) B2151191
theorem B1434171 : Blo 1433536 1434171 := bstep (se 1 (by rfl) ⟨1075628, by rfl⟩ : syracuseStep 1434171 = 2151257) B2151257
theorem B4842071 : Blo 1433536 4842071 := bstep (se 1 (by rfl) ⟨3631553, by rfl⟩ : syracuseStep 4842071 = 7263107) B7263107
theorem B1434247 : Blo 1433536 1434247 := bstep (se 1 (by rfl) ⟨1075685, by rfl⟩ : syracuseStep 1434247 = 2151371) B2151371
theorem B1434255 : Blo 1433536 1434255 := bstep (se 1 (by rfl) ⟨1075691, by rfl⟩ : syracuseStep 1434255 = 2151383) B2151383
theorem B1434299 : Blo 1433536 1434299 := bstep (se 1 (by rfl) ⟨1075724, by rfl⟩ : syracuseStep 1434299 = 2151449) B2151449
theorem B1614523 : Blo 1433536 1614523 := bstep (se 1 (by rfl) ⟨1210892, by rfl⟩ : syracuseStep 1614523 = 2421785) B2421785
theorem B1434375 : Blo 1433536 1434375 := bstep (se 1 (by rfl) ⟨1075781, by rfl⟩ : syracuseStep 1434375 = 2151563) B2151563
theorem B7258895 : Blo 1433536 7258895 := bstep (se 1 (by rfl) ⟨5444171, by rfl⟩ : syracuseStep 7258895 = 10888343) B10888343
theorem B1434383 : Blo 1433536 1434383 := bstep (se 1 (by rfl) ⟨1075787, by rfl⟩ : syracuseStep 1434383 = 2151575) B2151575
theorem B41386787 : Blo 1433536 41386787 := bstep (se 1 (by rfl) ⟨31040090, by rfl⟩ : syracuseStep 41386787 = 62080181) B62080181
theorem B1434427 : Blo 1433536 1434427 := bstep (se 1 (by rfl) ⟨1075820, by rfl⟩ : syracuseStep 1434427 = 2151641) B2151641
theorem B1434503 : Blo 1433536 1434503 := bstep (se 1 (by rfl) ⟨1075877, by rfl⟩ : syracuseStep 1434503 = 2151755) B2151755
theorem B3228551 : Blo 1433536 3228551 := bstep (se 1 (by rfl) ⟨2421413, by rfl⟩ : syracuseStep 3228551 = 4842827) B4842827
theorem B1434511 : Blo 1433536 1434511 := bstep (se 1 (by rfl) ⟨1075883, by rfl⟩ : syracuseStep 1434511 = 2151767) B2151767
theorem B13083545 : Blo 1433536 13083545 := bstep (se 2 (by rfl) ⟨4906329, by rfl⟩ : syracuseStep 13083545 = 9812659) B9812659
theorem B5522329 : Blo 1433536 5522329 := bstep (se 2 (by rfl) ⟨2070873, by rfl⟩ : syracuseStep 5522329 = 4141747) B4141747
theorem B1434555 : Blo 1433536 1434555 := bstep (se 1 (by rfl) ⟨1075916, by rfl⟩ : syracuseStep 1434555 = 2151833) B2151833
theorem B1434631 : Blo 1433536 1434631 := bstep (se 1 (by rfl) ⟨1075973, by rfl⟩ : syracuseStep 1434631 = 2151947) B2151947
theorem B1434639 : Blo 1433536 1434639 := bstep (se 1 (by rfl) ⟨1075979, by rfl⟩ : syracuseStep 1434639 = 2151959) B2151959
theorem B7357483 : Blo 1433536 7357483 := bstep (se 1 (by rfl) ⟨5518112, by rfl⟩ : syracuseStep 7357483 = 11036225) B11036225
theorem B1434683 : Blo 1433536 1434683 := bstep (se 1 (by rfl) ⟨1076012, by rfl⟩ : syracuseStep 1434683 = 2152025) B2152025
theorem B3228731 : Blo 1433536 3228731 := bstep (se 1 (by rfl) ⟨2421548, by rfl⟩ : syracuseStep 3228731 = 4843097) B4843097
theorem B4842557 : Blo 1433536 4842557 := bstep (se 3 (by rfl) ⟨907979, by rfl⟩ : syracuseStep 4842557 = 1815959) B1815959
theorem B3630167 : Blo 1433536 3630167 := bstep (se 1 (by rfl) ⟨2722625, by rfl⟩ : syracuseStep 3630167 = 5445251) B5445251
theorem B1434759 : Blo 1433536 1434759 := bstep (se 1 (by rfl) ⟨1076069, by rfl⟩ : syracuseStep 1434759 = 2152139) B2152139
theorem B1434767 : Blo 1433536 1434767 := bstep (se 1 (by rfl) ⟨1076075, by rfl⟩ : syracuseStep 1434767 = 2152151) B2152151
theorem B3064979 : Blo 1433536 3064979 := bstep (se 1 (by rfl) ⟨2298734, by rfl⟩ : syracuseStep 3064979 = 4597469) B4597469
theorem B3228857 : Blo 1433536 3228857 := bstep (se 2 (by rfl) ⟨1210821, by rfl⟩ : syracuseStep 3228857 = 2421643) B2421643
theorem B1434811 : Blo 1433536 1434811 := bstep (se 1 (by rfl) ⟨1076108, by rfl⟩ : syracuseStep 1434811 = 2152217) B2152217
theorem B5448941 : Blo 1433536 5448941 := bstep (se 3 (by rfl) ⟨1021676, by rfl⟩ : syracuseStep 5448941 = 2043353) B2043353
theorem B1434887 : Blo 1433536 1434887 := bstep (se 1 (by rfl) ⟨1076165, by rfl⟩ : syracuseStep 1434887 = 2152331) B2152331
theorem B1434895 : Blo 1433536 1434895 := bstep (se 1 (by rfl) ⟨1076171, by rfl⟩ : syracuseStep 1434895 = 2152343) B2152343
theorem B3630379 : Blo 1433536 3630379 := bstep (se 1 (by rfl) ⟨2722784, by rfl⟩ : syracuseStep 3630379 = 5445569) B5445569
theorem B1434939 : Blo 1433536 1434939 := bstep (se 1 (by rfl) ⟨1076204, by rfl⟩ : syracuseStep 1434939 = 2152409) B2152409
theorem B7751047 : Blo 1433536 7751047 := bstep (se 1 (by rfl) ⟨5813285, by rfl⟩ : syracuseStep 7751047 = 11626571) B11626571
theorem B1435015 : Blo 1433536 1435015 := bstep (se 1 (by rfl) ⟨1076261, by rfl⟩ : syracuseStep 1435015 = 2152523) B2152523
theorem B1435023 : Blo 1433536 1435023 := bstep (se 1 (by rfl) ⟨1076267, by rfl⟩ : syracuseStep 1435023 = 2152535) B2152535
theorem B3630521 : Blo 1433536 3630521 := bstep (se 2 (by rfl) ⟨1361445, by rfl⟩ : syracuseStep 3630521 = 2722891) B2722891
theorem B1435067 : Blo 1433536 1435067 := bstep (se 1 (by rfl) ⟨1076300, by rfl⟩ : syracuseStep 1435067 = 2152601) B2152601
theorem B1435143 : Blo 1433536 1435143 := bstep (se 1 (by rfl) ⟨1076357, by rfl⟩ : syracuseStep 1435143 = 2152715) B2152715
theorem B1435151 : Blo 1433536 1435151 := bstep (se 1 (by rfl) ⟨1076363, by rfl⟩ : syracuseStep 1435151 = 2152727) B2152727
theorem B3229199 : Blo 1433536 3229199 := bstep (se 1 (by rfl) ⟨2421899, by rfl⟩ : syracuseStep 3229199 = 4843799) B4843799
theorem B3229217 : Blo 1433536 3229217 := bstep (se 2 (by rfl) ⟨1210956, by rfl⟩ : syracuseStep 3229217 = 2421913) B2421913
theorem B1435195 : Blo 1433536 1435195 := bstep (se 1 (by rfl) ⟨1076396, by rfl⟩ : syracuseStep 1435195 = 2152793) B2152793
theorem B1435271 : Blo 1433536 1435271 := bstep (se 1 (by rfl) ⟨1076453, by rfl⟩ : syracuseStep 1435271 = 2152907) B2152907
theorem B1435279 : Blo 1433536 1435279 := bstep (se 1 (by rfl) ⟨1076459, by rfl⟩ : syracuseStep 1435279 = 2152919) B2152919
theorem B1435323 : Blo 1433536 1435323 := bstep (se 1 (by rfl) ⟨1076492, by rfl⟩ : syracuseStep 1435323 = 2152985) B2152985
theorem B1435399 : Blo 1433536 1435399 := bstep (se 1 (by rfl) ⟨1076549, by rfl⟩ : syracuseStep 1435399 = 2153099) B2153099
theorem B4597519 : Blo 1433536 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B1435407 : Blo 1433536 1435407 := bstep (se 1 (by rfl) ⟨1076555, by rfl⟩ : syracuseStep 1435407 = 2153111) B2153111
theorem B1435451 : Blo 1433536 1435451 := bstep (se 1 (by rfl) ⟨1076588, by rfl⟩ : syracuseStep 1435451 = 2153177) B2153177
theorem B3229559 : Blo 1433536 3229559 := bstep (se 1 (by rfl) ⟨2422169, by rfl⟩ : syracuseStep 3229559 = 4844339) B4844339
theorem B1435527 : Blo 1433536 1435527 := bstep (se 1 (by rfl) ⟨1076645, by rfl⟩ : syracuseStep 1435527 = 2153291) B2153291
theorem B1435535 : Blo 1433536 1435535 := bstep (se 1 (by rfl) ⟨1076651, by rfl⟩ : syracuseStep 1435535 = 2153303) B2153303
theorem B5449625 : Blo 1433536 5449625 := bstep (se 2 (by rfl) ⟨2043609, by rfl⟩ : syracuseStep 5449625 = 4087219) B4087219
theorem B2041787 : Blo 1433536 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B2721737 : Blo 1433536 2721737 := bstep (se 2 (by rfl) ⟨1020651, by rfl⟩ : syracuseStep 2721737 = 2041303) B2041303
theorem B2181065 : Blo 1433536 2181065 := bstep (se 2 (by rfl) ⟨817899, by rfl⟩ : syracuseStep 2181065 = 1635799) B1635799
theorem B3229739 : Blo 1433536 3229739 := bstep (se 1 (by rfl) ⟨2422304, by rfl⟩ : syracuseStep 3229739 = 4844609) B4844609
theorem B6129751 : Blo 1433536 6129751 := bstep (se 1 (by rfl) ⟨4597313, by rfl⟩ : syracuseStep 6129751 = 9194627) B9194627
theorem B7260353 : Blo 1433536 7260353 := bstep (se 2 (by rfl) ⟨2722632, by rfl⟩ : syracuseStep 7260353 = 5445265) B5445265
theorem B5171401 : Blo 1433536 5171401 := bstep (se 2 (by rfl) ⟨1939275, by rfl⟩ : syracuseStep 5171401 = 3878551) B3878551
theorem B3631513 : Blo 1433536 3631513 := bstep (se 2 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 3631513 = 2723635) B2723635
theorem B4843961 : Blo 1433536 4843961 := bstep (se 2 (by rfl) ⟨1816485, by rfl⟩ : syracuseStep 4843961 = 3632971) B3632971
theorem B12249629 : Blo 1433536 12249629 := bstep (se 3 (by rfl) ⟨2296805, by rfl⟩ : syracuseStep 12249629 = 4593611) B4593611
theorem B2042425 : Blo 1433536 2042425 := bstep (se 2 (by rfl) ⟨765909, by rfl⟩ : syracuseStep 2042425 = 1531819) B1531819
theorem B3631675 : Blo 1433536 3631675 := bstep (se 1 (by rfl) ⟨2723756, by rfl⟩ : syracuseStep 3631675 = 5447513) B5447513
theorem B26176067 : Blo 1433536 26176067 := bstep (se 1 (by rfl) ⟨19632050, by rfl⟩ : syracuseStep 26176067 = 39264101) B39264101
theorem B66292343 : Blo 1433536 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B3631817 : Blo 1433536 3631817 := bstep (se 2 (by rfl) ⟨1361931, by rfl⟩ : syracuseStep 3631817 = 2723863) B2723863
theorem B78523141 : Blo 1433536 78523141 := bstep (se 4 (by rfl) ⟨7361544, by rfl⟩ : syracuseStep 78523141 = 14723089) B14723089
theorem B4082491 : Blo 1433536 4082491 := bstep (se 1 (by rfl) ⟨3061868, by rfl⟩ : syracuseStep 4082491 = 6123737) B6123737
theorem B2329463 : Blo 1433536 2329463 := bstep (se 1 (by rfl) ⟨1747097, by rfl⟩ : syracuseStep 2329463 = 3494195) B3494195
theorem B2419591 : Blo 1433536 2419591 := bstep (se 1 (by rfl) ⟨1814693, by rfl⟩ : syracuseStep 2419591 = 3629387) B3629387
theorem B11037707 : Blo 1433536 11037707 := bstep (se 1 (by rfl) ⟨8278280, by rfl⟩ : syracuseStep 11037707 = 16556561) B16556561
theorem B4844555 : Blo 1433536 4844555 := bstep (se 1 (by rfl) ⟨3633416, by rfl⟩ : syracuseStep 4844555 = 7266833) B7266833
theorem B3632161 : Blo 1433536 3632161 := bstep (se 2 (by rfl) ⟨1362060, by rfl⟩ : syracuseStep 3632161 = 2724121) B2724121
theorem B4844663 : Blo 1433536 4844663 := bstep (se 1 (by rfl) ⟨3633497, by rfl⟩ : syracuseStep 4844663 = 7266995) B7266995
theorem B55151765 : Blo 1433536 55151765 := bstep (se 6 (by rfl) ⟨1292619, by rfl⟩ : syracuseStep 55151765 = 2585239) B2585239
theorem B7859429 : Blo 1433536 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B7261649 : Blo 1433536 7261649 := bstep (se 2 (by rfl) ⟨2723118, by rfl⟩ : syracuseStep 7261649 = 5446237) B5446237
theorem B6131153 : Blo 1433536 6131153 := bstep (se 2 (by rfl) ⟨2299182, by rfl⟩ : syracuseStep 6131153 = 4598365) B4598365
theorem B2420239 : Blo 1433536 2420239 := bstep (se 1 (by rfl) ⟨1815179, by rfl⟩ : syracuseStep 2420239 = 3630359) B3630359
theorem B5443139 : Blo 1433536 5443139 := bstep (se 1 (by rfl) ⟨4082354, by rfl⟩ : syracuseStep 5443139 = 8164709) B8164709
theorem B3632759 : Blo 1433536 3632759 := bstep (se 1 (by rfl) ⟨2724569, by rfl⟩ : syracuseStep 3632759 = 5449139) B5449139
theorem B4083335 : Blo 1433536 4083335 := bstep (se 1 (by rfl) ⟨3062501, by rfl⟩ : syracuseStep 4083335 = 6125003) B6125003
theorem B10333925 : Blo 1433536 10333925 := bstep (se 4 (by rfl) ⟨968805, by rfl⟩ : syracuseStep 10333925 = 1937611) B1937611
theorem B23580389 : Blo 1433536 23580389 := bstep (se 4 (by rfl) ⟨2210661, by rfl⟩ : syracuseStep 23580389 = 4421323) B4421323
theorem B2330383 : Blo 1433536 2330383 := bstep (se 1 (by rfl) ⟨1747787, by rfl⟩ : syracuseStep 2330383 = 3495575) B3495575
theorem B4910863 : Blo 1433536 4910863 := bstep (se 1 (by rfl) ⟨3683147, by rfl⟩ : syracuseStep 4910863 = 7366295) B7366295
theorem B8285989 : Blo 1433536 8285989 := bstep (se 4 (by rfl) ⟨776811, by rfl⟩ : syracuseStep 8285989 = 1553623) B1553623
theorem B2723719 : Blo 1433536 2723719 := bstep (se 1 (by rfl) ⟨2042789, by rfl⟩ : syracuseStep 2723719 = 4085579) B4085579
theorem B2150315 : Blo 1433536 2150315 := bstep (se 1 (by rfl) ⟨1612736, by rfl⟩ : syracuseStep 2150315 = 3225473) B3225473
theorem B2150345 : Blo 1433536 2150345 := bstep (se 2 (by rfl) ⟨806379, by rfl⟩ : syracuseStep 2150345 = 1612759) B1612759
theorem B2043911 : Blo 1433536 2043911 := bstep (se 1 (by rfl) ⟨1532933, by rfl⟩ : syracuseStep 2043911 = 3065867) B3065867
theorem B5443595 : Blo 1433536 5443595 := bstep (se 1 (by rfl) ⟨4082696, by rfl⟩ : syracuseStep 5443595 = 8165393) B8165393
theorem B59666453 : Blo 1433536 59666453 := bstep (se 6 (by rfl) ⟨1398432, by rfl⟩ : syracuseStep 59666453 = 2796865) B2796865
theorem B8171543 : Blo 1433536 8171543 := bstep (se 1 (by rfl) ⟨6128657, by rfl⟩ : syracuseStep 8171543 = 12257315) B12257315
theorem B2420779 : Blo 1433536 2420779 := bstep (se 1 (by rfl) ⟨1815584, by rfl⟩ : syracuseStep 2420779 = 3631169) B3631169
theorem B2150459 : Blo 1433536 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B2150519 : Blo 1433536 2150519 := bstep (se 1 (by rfl) ⟨1612889, by rfl⟩ : syracuseStep 2150519 = 3225779) B3225779
theorem B1814663 : Blo 1433536 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B2150543 : Blo 1433536 2150543 := bstep (se 1 (by rfl) ⟨1612907, by rfl⟩ : syracuseStep 2150543 = 3225815) B3225815
theorem B2150585 : Blo 1433536 2150585 := bstep (se 2 (by rfl) ⟨806469, by rfl⟩ : syracuseStep 2150585 = 1612939) B1612939
theorem B2420921 : Blo 1433536 2420921 := bstep (se 2 (by rfl) ⟨907845, by rfl⟩ : syracuseStep 2420921 = 1815691) B1815691
theorem B6123721 : Blo 1433536 6123721 := bstep (se 2 (by rfl) ⟨2296395, by rfl⟩ : syracuseStep 6123721 = 4592791) B4592791
theorem B157102325 : Blo 1433536 157102325 := bstep (se 5 (by rfl) ⟨7364171, by rfl⟩ : syracuseStep 157102325 = 14728343) B14728343
theorem B2150663 : Blo 1433536 2150663 := bstep (se 1 (by rfl) ⟨1612997, by rfl⟩ : syracuseStep 2150663 = 3225995) B3225995
theorem B2150699 : Blo 1433536 2150699 := bstep (se 1 (by rfl) ⟨1613024, by rfl⟩ : syracuseStep 2150699 = 3226049) B3226049
theorem B2150729 : Blo 1433536 2150729 := bstep (se 2 (by rfl) ⟨806523, by rfl⟩ : syracuseStep 2150729 = 1613047) B1613047
theorem B4084121 : Blo 1433536 4084121 := bstep (se 2 (by rfl) ⟨1531545, by rfl⟩ : syracuseStep 4084121 = 3063091) B3063091
theorem B1937849 : Blo 1433536 1937849 := bstep (se 2 (by rfl) ⟨726693, by rfl⟩ : syracuseStep 1937849 = 1453387) B1453387
theorem B2150843 : Blo 1433536 2150843 := bstep (se 1 (by rfl) ⟨1613132, by rfl⟩ : syracuseStep 2150843 = 3226265) B3226265
theorem B15503825 : Blo 1433536 15503825 := bstep (se 2 (by rfl) ⟨5813934, by rfl⟩ : syracuseStep 15503825 = 11627869) B11627869
theorem B2150903 : Blo 1433536 2150903 := bstep (se 1 (by rfl) ⟨1613177, by rfl⟩ : syracuseStep 2150903 = 3226355) B3226355
theorem B2150927 : Blo 1433536 2150927 := bstep (se 1 (by rfl) ⟨1613195, by rfl⟩ : syracuseStep 2150927 = 3226391) B3226391
theorem B2150969 : Blo 1433536 2150969 := bstep (se 2 (by rfl) ⟨806613, by rfl⟩ : syracuseStep 2150969 = 1613227) B1613227
theorem B1634951 : Blo 1433536 1634951 := bstep (se 1 (by rfl) ⟨1226213, by rfl⟩ : syracuseStep 1634951 = 2452427) B2452427
theorem B2151047 : Blo 1433536 2151047 := bstep (se 1 (by rfl) ⟨1613285, by rfl⟩ : syracuseStep 2151047 = 3226571) B3226571
theorem B2298503 : Blo 1433536 2298503 := bstep (se 1 (by rfl) ⟨1723877, by rfl⟩ : syracuseStep 2298503 = 3447755) B3447755
theorem B2151083 : Blo 1433536 2151083 := bstep (se 1 (by rfl) ⟨1613312, by rfl⟩ : syracuseStep 2151083 = 3226625) B3226625
theorem B2151113 : Blo 1433536 2151113 := bstep (se 2 (by rfl) ⟨806667, by rfl⟩ : syracuseStep 2151113 = 1613335) B1613335
theorem B17453825 : Blo 1433536 17453825 := bstep (se 2 (by rfl) ⟨6545184, by rfl⟩ : syracuseStep 17453825 = 13090369) B13090369
theorem B1635079 : Blo 1433536 1635079 := bstep (se 1 (by rfl) ⟨1226309, by rfl⟩ : syracuseStep 1635079 = 2452619) B2452619
theorem B1815311 : Blo 1433536 1815311 := bstep (se 1 (by rfl) ⟨1361483, by rfl⟩ : syracuseStep 1815311 = 2722967) B2722967
theorem B13095731 : Blo 1433536 13095731 := bstep (se 1 (by rfl) ⟨9821798, by rfl⟩ : syracuseStep 13095731 = 19643597) B19643597
theorem B2151227 : Blo 1433536 2151227 := bstep (se 1 (by rfl) ⟨1613420, by rfl⟩ : syracuseStep 2151227 = 3226841) B3226841
theorem B2151287 : Blo 1433536 2151287 := bstep (se 1 (by rfl) ⟨1613465, by rfl⟩ : syracuseStep 2151287 = 3226931) B3226931
theorem B2454391 : Blo 1433536 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B2421623 : Blo 1433536 2421623 := bstep (se 1 (by rfl) ⟨1816217, by rfl⟩ : syracuseStep 2421623 = 3632435) B3632435
theorem B2151311 : Blo 1433536 2151311 := bstep (se 1 (by rfl) ⟨1613483, by rfl⟩ : syracuseStep 2151311 = 3226967) B3226967
theorem B4838291 : Blo 1433536 4838291 := bstep (se 1 (by rfl) ⟨3628718, by rfl⟩ : syracuseStep 4838291 = 7257437) B7257437
theorem B2151353 : Blo 1433536 2151353 := bstep (se 2 (by rfl) ⟨806757, by rfl⟩ : syracuseStep 2151353 = 1613515) B1613515
theorem B2151431 : Blo 1433536 2151431 := bstep (se 1 (by rfl) ⟨1613573, by rfl⟩ : syracuseStep 2151431 = 3227147) B3227147
theorem B4084769 : Blo 1433536 4084769 := bstep (se 2 (by rfl) ⟨1531788, by rfl⟩ : syracuseStep 4084769 = 3063577) B3063577
theorem B2151467 : Blo 1433536 2151467 := bstep (se 1 (by rfl) ⟨1613600, by rfl⟩ : syracuseStep 2151467 = 3227201) B3227201
theorem B2151497 : Blo 1433536 2151497 := bstep (se 2 (by rfl) ⟨806811, by rfl⟩ : syracuseStep 2151497 = 1613623) B1613623
theorem B15340661 : Blo 1433536 15340661 := bstep (se 5 (by rfl) ⟨719093, by rfl⟩ : syracuseStep 15340661 = 1438187) B1438187
theorem B2151611 : Blo 1433536 2151611 := bstep (se 1 (by rfl) ⟨1613708, by rfl⟩ : syracuseStep 2151611 = 3227417) B3227417
theorem B2151671 : Blo 1433536 2151671 := bstep (se 1 (by rfl) ⟨1613753, by rfl⟩ : syracuseStep 2151671 = 3227507) B3227507
theorem B2151695 : Blo 1433536 2151695 := bstep (se 1 (by rfl) ⟨1613771, by rfl⟩ : syracuseStep 2151695 = 3227543) B3227543
theorem B36754721 : Blo 1433536 36754721 := bstep (se 2 (by rfl) ⟨13783020, by rfl⟩ : syracuseStep 36754721 = 27566041) B27566041
theorem B2151737 : Blo 1433536 2151737 := bstep (se 2 (by rfl) ⟨806901, by rfl⟩ : syracuseStep 2151737 = 1613803) B1613803
theorem B2422075 : Blo 1433536 2422075 := bstep (se 1 (by rfl) ⟨1816556, by rfl⟩ : syracuseStep 2422075 = 3633113) B3633113
theorem B2299195 : Blo 1433536 2299195 := bstep (se 1 (by rfl) ⟨1724396, by rfl⟩ : syracuseStep 2299195 = 3448793) B3448793
theorem B6542707 : Blo 1433536 6542707 := bstep (se 1 (by rfl) ⟨4907030, by rfl⟩ : syracuseStep 6542707 = 9814061) B9814061
theorem B2151815 : Blo 1433536 2151815 := bstep (se 1 (by rfl) ⟨1613861, by rfl⟩ : syracuseStep 2151815 = 3227723) B3227723
theorem B2905290125 : Blo 1433536 2905290125 := bstep (se 3 (by rfl) ⟨544741898, by rfl⟩ : syracuseStep 2905290125 = 1089483797) B1089483797
theorem B181630349 : Blo 1433536 181630349 := bstep (se 3 (by rfl) ⟨34055690, by rfl⟩ : syracuseStep 181630349 = 68111381) B68111381
theorem B2151851 : Blo 1433536 2151851 := bstep (se 1 (by rfl) ⟨1613888, by rfl⟩ : syracuseStep 2151851 = 3227777) B3227777
theorem B2151881 : Blo 1433536 2151881 := bstep (se 2 (by rfl) ⟨806955, by rfl⟩ : syracuseStep 2151881 = 1613911) B1613911
theorem B2422217 : Blo 1433536 2422217 := bstep (se 2 (by rfl) ⟨908331, by rfl⟩ : syracuseStep 2422217 = 1816663) B1816663
theorem B13784525 : Blo 1433536 13784525 := bstep (se 3 (by rfl) ⟨2584598, by rfl⟩ : syracuseStep 13784525 = 5169197) B5169197
theorem B2299337 : Blo 1433536 2299337 := bstep (se 2 (by rfl) ⟨862251, by rfl⟩ : syracuseStep 2299337 = 1724503) B1724503
theorem B7263755 : Blo 1433536 7263755 := bstep (se 1 (by rfl) ⟨5447816, by rfl⟩ : syracuseStep 7263755 = 10895633) B10895633
theorem B2151995 : Blo 1433536 2151995 := bstep (se 1 (by rfl) ⟨1613996, by rfl⟩ : syracuseStep 2151995 = 3227993) B3227993
theorem B2152055 : Blo 1433536 2152055 := bstep (se 1 (by rfl) ⟨1614041, by rfl⟩ : syracuseStep 2152055 = 3228083) B3228083
theorem B2152079 : Blo 1433536 2152079 := bstep (se 1 (by rfl) ⟨1614059, by rfl⟩ : syracuseStep 2152079 = 3228119) B3228119
theorem B7263917 : Blo 1433536 7263917 := bstep (se 3 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 7263917 = 2723969) B2723969
theorem B2152121 : Blo 1433536 2152121 := bstep (se 2 (by rfl) ⟨807045, by rfl⟩ : syracuseStep 2152121 = 1614091) B1614091
theorem B2152199 : Blo 1433536 2152199 := bstep (se 1 (by rfl) ⟨1614149, by rfl⟩ : syracuseStep 2152199 = 3228299) B3228299
theorem B13784867 : Blo 1433536 13784867 := bstep (se 1 (by rfl) ⟨10338650, by rfl⟩ : syracuseStep 13784867 = 20677301) B20677301
theorem B2152235 : Blo 1433536 2152235 := bstep (se 1 (by rfl) ⟨1614176, by rfl⟩ : syracuseStep 2152235 = 3228353) B3228353
theorem B2152265 : Blo 1433536 2152265 := bstep (se 2 (by rfl) ⟨807099, by rfl⟩ : syracuseStep 2152265 = 1614199) B1614199
theorem B8173457 : Blo 1433536 8173457 := bstep (se 2 (by rfl) ⟨3065046, by rfl⟩ : syracuseStep 8173457 = 6130093) B6130093
theorem B3225491 : Blo 1433536 3225491 := bstep (se 1 (by rfl) ⟨2419118, by rfl⟩ : syracuseStep 3225491 = 4838237) B4838237
theorem B2152379 : Blo 1433536 2152379 := bstep (se 1 (by rfl) ⟨1614284, by rfl⟩ : syracuseStep 2152379 = 3228569) B3228569
theorem B3225545 : Blo 1433536 3225545 := bstep (se 2 (by rfl) ⟨1209579, by rfl⟩ : syracuseStep 3225545 = 2419159) B2419159
theorem B2152439 : Blo 1433536 2152439 := bstep (se 1 (by rfl) ⟨1614329, by rfl⟩ : syracuseStep 2152439 = 3228659) B3228659
theorem B4085761 : Blo 1433536 4085761 := bstep (se 2 (by rfl) ⟨1532160, by rfl⟩ : syracuseStep 4085761 = 3064321) B3064321
theorem B2152463 : Blo 1433536 2152463 := bstep (se 1 (by rfl) ⟨1614347, by rfl⟩ : syracuseStep 2152463 = 3228695) B3228695
theorem B3061793 : Blo 1433536 3061793 := bstep (se 2 (by rfl) ⟨1148172, by rfl⟩ : syracuseStep 3061793 = 2296345) B2296345
theorem B2152505 : Blo 1433536 2152505 := bstep (se 2 (by rfl) ⟨807189, by rfl⟩ : syracuseStep 2152505 = 1614379) B1614379
theorem B5445751 : Blo 1433536 5445751 := bstep (se 1 (by rfl) ⟨4084313, by rfl⟩ : syracuseStep 5445751 = 8168627) B8168627
theorem B2152583 : Blo 1433536 2152583 := bstep (se 1 (by rfl) ⟨1614437, by rfl⟩ : syracuseStep 2152583 = 3228875) B3228875
theorem B2152619 : Blo 1433536 2152619 := bstep (se 1 (by rfl) ⟨1614464, by rfl⟩ : syracuseStep 2152619 = 3228929) B3228929
theorem B6895817 : Blo 1433536 6895817 := bstep (se 2 (by rfl) ⟨2585931, by rfl⟩ : syracuseStep 6895817 = 5171863) B5171863
theorem B2152649 : Blo 1433536 2152649 := bstep (se 2 (by rfl) ⟨807243, by rfl⟩ : syracuseStep 2152649 = 1614487) B1614487
theorem B4839695 : Blo 1433536 4839695 := bstep (se 1 (by rfl) ⟨3629771, by rfl⟩ : syracuseStep 4839695 = 7259543) B7259543
theorem B235411757 : Blo 1433536 235411757 := bstep (se 3 (by rfl) ⟨44139704, by rfl⟩ : syracuseStep 235411757 = 88279409) B88279409
theorem B2152763 : Blo 1433536 2152763 := bstep (se 1 (by rfl) ⟨1614572, by rfl⟩ : syracuseStep 2152763 = 3229145) B3229145
theorem B2152823 : Blo 1433536 2152823 := bstep (se 1 (by rfl) ⟨1614617, by rfl⟩ : syracuseStep 2152823 = 3229235) B3229235
theorem B2152847 : Blo 1433536 2152847 := bstep (se 1 (by rfl) ⟨1614635, by rfl⟩ : syracuseStep 2152847 = 3229271) B3229271
theorem B12253625 : Blo 1433536 12253625 := bstep (se 2 (by rfl) ⟨4595109, by rfl⟩ : syracuseStep 12253625 = 9190219) B9190219
theorem B2152889 : Blo 1433536 2152889 := bstep (se 2 (by rfl) ⟨807333, by rfl⟩ : syracuseStep 2152889 = 1614667) B1614667
theorem B2152967 : Blo 1433536 2152967 := bstep (se 1 (by rfl) ⟨1614725, by rfl⟩ : syracuseStep 2152967 = 3229451) B3229451
theorem B4839965 : Blo 1433536 4839965 := bstep (se 3 (by rfl) ⟨907493, by rfl⟩ : syracuseStep 4839965 = 1814987) B1814987
theorem B17439275 : Blo 1433536 17439275 := bstep (se 1 (by rfl) ⟨13079456, by rfl⟩ : syracuseStep 17439275 = 26158913) B26158913
theorem B2153003 : Blo 1433536 2153003 := bstep (se 1 (by rfl) ⟨1614752, by rfl⟩ : syracuseStep 2153003 = 3229505) B3229505
theorem B8174141 : Blo 1433536 8174141 := bstep (se 3 (by rfl) ⟨1532651, by rfl⟩ : syracuseStep 8174141 = 3065303) B3065303
theorem B2153033 : Blo 1433536 2153033 := bstep (se 2 (by rfl) ⟨807387, by rfl⟩ : syracuseStep 2153033 = 1614775) B1614775
theorem B3226247 : Blo 1433536 3226247 := bstep (se 1 (by rfl) ⟨2419685, by rfl⟩ : syracuseStep 3226247 = 4839371) B4839371
theorem B2153147 : Blo 1433536 2153147 := bstep (se 1 (by rfl) ⟨1614860, by rfl⟩ : syracuseStep 2153147 = 3229721) B3229721
theorem B2153207 : Blo 1433536 2153207 := bstep (se 1 (by rfl) ⟨1614905, by rfl⟩ : syracuseStep 2153207 = 3229811) B3229811
theorem B2153231 : Blo 1433536 2153231 := bstep (se 1 (by rfl) ⟨1614923, by rfl⟩ : syracuseStep 2153231 = 3229847) B3229847
theorem B12254003 : Blo 1433536 12254003 := bstep (se 1 (by rfl) ⟨9190502, by rfl⟩ : syracuseStep 12254003 = 18381005) B18381005
theorem B2153273 : Blo 1433536 2153273 := bstep (se 2 (by rfl) ⟨807477, by rfl⟩ : syracuseStep 2153273 = 1614955) B1614955
theorem B3226427 : Blo 1433536 3226427 := bstep (se 1 (by rfl) ⟨2419820, by rfl⟩ : syracuseStep 3226427 = 4839641) B4839641
theorem B3226553 : Blo 1433536 3226553 := bstep (se 2 (by rfl) ⟨1209957, by rfl⟩ : syracuseStep 3226553 = 2419915) B2419915
theorem B3447851 : Blo 1433536 3447851 := bstep (se 1 (by rfl) ⟨2585888, by rfl⟩ : syracuseStep 3447851 = 5171777) B5171777
theorem B3062843 : Blo 1433536 3062843 := bstep (se 1 (by rfl) ⟨2297132, by rfl⟩ : syracuseStep 3062843 = 4594265) B4594265
theorem B5446723 : Blo 1433536 5446723 := bstep (se 1 (by rfl) ⟨4085042, by rfl⟩ : syracuseStep 5446723 = 8170085) B8170085
theorem B12418181 : Blo 1433536 12418181 := bstep (se 4 (by rfl) ⟨1164204, by rfl⟩ : syracuseStep 12418181 = 2328409) B2328409
theorem B31440005 : Blo 1433536 31440005 := bstep (se 4 (by rfl) ⟨2947500, by rfl⟩ : syracuseStep 31440005 = 5895001) B5895001
theorem B1531067 : Blo 1433536 1531067 := bstep (se 1 (by rfl) ⟨1148300, by rfl⟩ : syracuseStep 1531067 = 2296601) B2296601
theorem B7265537 : Blo 1433536 7265537 := bstep (se 2 (by rfl) ⟨2724576, by rfl⟩ : syracuseStep 7265537 = 5449153) B5449153
theorem B3226895 : Blo 1433536 3226895 := bstep (se 1 (by rfl) ⟨2420171, by rfl⟩ : syracuseStep 3226895 = 4840343) B4840343
theorem B3226913 : Blo 1433536 3226913 := bstep (se 2 (by rfl) ⟨1210092, by rfl⟩ : syracuseStep 3226913 = 2420185) B2420185
theorem B5447027 : Blo 1433536 5447027 := bstep (se 1 (by rfl) ⟨4085270, by rfl⟩ : syracuseStep 5447027 = 8170541) B8170541
theorem B1613191 : Blo 1433536 1613191 := bstep (se 1 (by rfl) ⟨1209893, by rfl⟩ : syracuseStep 1613191 = 2419787) B2419787
theorem B5168519 : Blo 1433536 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B17456593 : Blo 1433536 17456593 := bstep (se 2 (by rfl) ⟨6546222, by rfl⟩ : syracuseStep 17456593 = 13092445) B13092445
theorem B1613371 : Blo 1433536 1613371 := bstep (se 1 (by rfl) ⟨1210028, by rfl⟩ : syracuseStep 1613371 = 2420057) B2420057
theorem B3227255 : Blo 1433536 3227255 := bstep (se 1 (by rfl) ⟨2420441, by rfl⟩ : syracuseStep 3227255 = 4840883) B4840883
theorem B3448439 : Blo 1433536 3448439 := bstep (se 1 (by rfl) ⟨2586329, by rfl⟩ : syracuseStep 3448439 = 5172659) B5172659
theorem B16342721 : Blo 1433536 16342721 := bstep (se 2 (by rfl) ⟨6128520, by rfl⟩ : syracuseStep 16342721 = 12257041) B12257041
theorem B10886885 : Blo 1433536 10886885 := bstep (se 4 (by rfl) ⟨1020645, by rfl⟩ : syracuseStep 10886885 = 2041291) B2041291
theorem B9191141 : Blo 1433536 9191141 := bstep (se 4 (by rfl) ⟨861669, by rfl⟩ : syracuseStep 9191141 = 1723339) B1723339
theorem B8167169 : Blo 1433536 8167169 := bstep (se 2 (by rfl) ⟨3062688, by rfl⟩ : syracuseStep 8167169 = 6125377) B6125377
theorem B3227435 : Blo 1433536 3227435 := bstep (se 1 (by rfl) ⟨2420576, by rfl⟩ : syracuseStep 3227435 = 4841153) B4841153
theorem B3063595 : Blo 1433536 3063595 := bstep (se 1 (by rfl) ⟨2297696, by rfl⟩ : syracuseStep 3063595 = 4595393) B4595393
theorem B5447483 : Blo 1433536 5447483 := bstep (se 1 (by rfl) ⟨4085612, by rfl⟩ : syracuseStep 5447483 = 8171225) B8171225
theorem B4841369 : Blo 1433536 4841369 := bstep (se 2 (by rfl) ⟨1815513, by rfl⟩ : syracuseStep 4841369 = 3631027) B3631027
theorem B39264203 : Blo 1433536 39264203 := bstep (se 1 (by rfl) ⟨29448152, by rfl⟩ : syracuseStep 39264203 = 58896305) B58896305
theorem B5447681 : Blo 1433536 5447681 := bstep (se 2 (by rfl) ⟨2042880, by rfl⟩ : syracuseStep 5447681 = 4085761) B4085761
theorem B3629063 : Blo 1433536 3629063 := bstep (se 1 (by rfl) ⟨2721797, by rfl⟩ : syracuseStep 3629063 = 5443595) B5443595
theorem B5447695 : Blo 1433536 5447695 := bstep (se 1 (by rfl) ⟨4085771, by rfl⟩ : syracuseStep 5447695 = 8171543) B8171543
theorem B1433639 : Blo 1433536 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B3227705 : Blo 1433536 3227705 := bstep (se 2 (by rfl) ⟨1210389, by rfl⟩ : syracuseStep 3227705 = 2420779) B2420779
theorem B1433679 : Blo 1433536 1433679 := bstep (se 1 (by rfl) ⟨1075259, by rfl⟩ : syracuseStep 1433679 = 2150519) B2150519
theorem B1433695 : Blo 1433536 1433695 := bstep (se 1 (by rfl) ⟨1075271, by rfl⟩ : syracuseStep 1433695 = 2150543) B2150543
theorem B1433723 : Blo 1433536 1433723 := bstep (se 1 (by rfl) ⟨1075292, by rfl⟩ : syracuseStep 1433723 = 2150585) B2150585
theorem B1613947 : Blo 1433536 1613947 := bstep (se 1 (by rfl) ⟨1210460, by rfl⟩ : syracuseStep 1613947 = 2420921) B2420921
theorem B104734883 : Blo 1433536 104734883 := bstep (se 1 (by rfl) ⟨78551162, by rfl⟩ : syracuseStep 104734883 = 157102325) B157102325
theorem B1433775 : Blo 1433536 1433775 := bstep (se 1 (by rfl) ⟨1075331, by rfl⟩ : syracuseStep 1433775 = 2150663) B2150663
theorem B1433799 : Blo 1433536 1433799 := bstep (se 1 (by rfl) ⟨1075349, by rfl⟩ : syracuseStep 1433799 = 2150699) B2150699
theorem B1433819 : Blo 1433536 1433819 := bstep (se 1 (by rfl) ⟨1075364, by rfl⟩ : syracuseStep 1433819 = 2150729) B2150729
theorem B1433895 : Blo 1433536 1433895 := bstep (se 1 (by rfl) ⟨1075421, by rfl⟩ : syracuseStep 1433895 = 2150843) B2150843
theorem B1433935 : Blo 1433536 1433935 := bstep (se 1 (by rfl) ⟨1075451, by rfl⟩ : syracuseStep 1433935 = 2150903) B2150903
theorem B1433951 : Blo 1433536 1433951 := bstep (se 1 (by rfl) ⟨1075463, by rfl⟩ : syracuseStep 1433951 = 2150927) B2150927
theorem B1433979 : Blo 1433536 1433979 := bstep (se 1 (by rfl) ⟨1075484, by rfl⟩ : syracuseStep 1433979 = 2150969) B2150969
theorem B3228047 : Blo 1433536 3228047 := bstep (se 1 (by rfl) ⟨2421035, by rfl⟩ : syracuseStep 3228047 = 4842071) B4842071
theorem B1434031 : Blo 1433536 1434031 := bstep (se 1 (by rfl) ⟨1075523, by rfl⟩ : syracuseStep 1434031 = 2151047) B2151047
theorem B1434055 : Blo 1433536 1434055 := bstep (se 1 (by rfl) ⟨1075541, by rfl⟩ : syracuseStep 1434055 = 2151083) B2151083
theorem B1434075 : Blo 1433536 1434075 := bstep (se 1 (by rfl) ⟨1075556, by rfl⟩ : syracuseStep 1434075 = 2151113) B2151113
theorem B27591191 : Blo 1433536 27591191 := bstep (se 1 (by rfl) ⟨20693393, by rfl⟩ : syracuseStep 27591191 = 41386787) B41386787
theorem B4842017 : Blo 1433536 4842017 := bstep (se 2 (by rfl) ⟨1815756, by rfl⟩ : syracuseStep 4842017 = 3631513) B3631513
theorem B1434151 : Blo 1433536 1434151 := bstep (se 1 (by rfl) ⟨1075613, by rfl⟩ : syracuseStep 1434151 = 2151227) B2151227
theorem B1434191 : Blo 1433536 1434191 := bstep (se 1 (by rfl) ⟨1075643, by rfl⟩ : syracuseStep 1434191 = 2151287) B2151287
theorem B1614415 : Blo 1433536 1614415 := bstep (se 1 (by rfl) ⟨1210811, by rfl⟩ : syracuseStep 1614415 = 2421623) B2421623
theorem B1434207 : Blo 1433536 1434207 := bstep (se 1 (by rfl) ⟨1075655, by rfl⟩ : syracuseStep 1434207 = 2151311) B2151311
theorem B1434235 : Blo 1433536 1434235 := bstep (se 1 (by rfl) ⟨1075676, by rfl⟩ : syracuseStep 1434235 = 2151353) B2151353
theorem B1434287 : Blo 1433536 1434287 := bstep (se 1 (by rfl) ⟨1075715, by rfl⟩ : syracuseStep 1434287 = 2151431) B2151431
theorem B1434311 : Blo 1433536 1434311 := bstep (se 1 (by rfl) ⟨1075733, by rfl⟩ : syracuseStep 1434311 = 2151467) B2151467
theorem B3228371 : Blo 1433536 3228371 := bstep (se 1 (by rfl) ⟨2421278, by rfl⟩ : syracuseStep 3228371 = 4842557) B4842557
theorem B1434331 : Blo 1433536 1434331 := bstep (se 1 (by rfl) ⟨1075748, by rfl⟩ : syracuseStep 1434331 = 2151497) B2151497
theorem B4842233 : Blo 1433536 4842233 := bstep (se 2 (by rfl) ⟨1815837, by rfl⟩ : syracuseStep 4842233 = 3631675) B3631675
theorem B1434407 : Blo 1433536 1434407 := bstep (se 1 (by rfl) ⟨1075805, by rfl⟩ : syracuseStep 1434407 = 2151611) B2151611
theorem B1434447 : Blo 1433536 1434447 := bstep (se 1 (by rfl) ⟨1075835, by rfl⟩ : syracuseStep 1434447 = 2151671) B2151671
theorem B1434463 : Blo 1433536 1434463 := bstep (se 1 (by rfl) ⟨1075847, by rfl⟩ : syracuseStep 1434463 = 2151695) B2151695
theorem B24503147 : Blo 1433536 24503147 := bstep (se 1 (by rfl) ⟨18377360, by rfl⟩ : syracuseStep 24503147 = 36754721) B36754721
theorem B1434491 : Blo 1433536 1434491 := bstep (se 1 (by rfl) ⟨1075868, by rfl⟩ : syracuseStep 1434491 = 2151737) B2151737
theorem B1434543 : Blo 1433536 1434543 := bstep (se 1 (by rfl) ⟨1075907, by rfl⟩ : syracuseStep 1434543 = 2151815) B2151815
theorem B1936860083 : Blo 1433536 1936860083 := bstep (se 1 (by rfl) ⟨1452645062, by rfl⟩ : syracuseStep 1936860083 = 2905290125) B2905290125
theorem B121086899 : Blo 1433536 121086899 := bstep (se 1 (by rfl) ⟨90815174, by rfl⟩ : syracuseStep 121086899 = 181630349) B181630349
theorem B1434567 : Blo 1433536 1434567 := bstep (se 1 (by rfl) ⟨1075925, by rfl⟩ : syracuseStep 1434567 = 2151851) B2151851
theorem B1434587 : Blo 1433536 1434587 := bstep (se 1 (by rfl) ⟨1075940, by rfl⟩ : syracuseStep 1434587 = 2151881) B2151881
theorem B1614811 : Blo 1433536 1614811 := bstep (se 1 (by rfl) ⟨1211108, by rfl⟩ : syracuseStep 1614811 = 2422217) B2422217
theorem B1532891 : Blo 1433536 1532891 := bstep (se 1 (by rfl) ⟨1149668, by rfl⟩ : syracuseStep 1532891 = 2299337) B2299337
theorem B4842503 : Blo 1433536 4842503 := bstep (se 1 (by rfl) ⟨3631877, by rfl⟩ : syracuseStep 4842503 = 7263755) B7263755
theorem B2180105 : Blo 1433536 2180105 := bstep (se 2 (by rfl) ⟨817539, by rfl⟩ : syracuseStep 2180105 = 1635079) B1635079
theorem B1434663 : Blo 1433536 1434663 := bstep (se 1 (by rfl) ⟨1075997, by rfl⟩ : syracuseStep 1434663 = 2151995) B2151995
theorem B1434703 : Blo 1433536 1434703 := bstep (se 1 (by rfl) ⟨1076027, by rfl⟩ : syracuseStep 1434703 = 2152055) B2152055
theorem B1434719 : Blo 1433536 1434719 := bstep (se 1 (by rfl) ⟨1076039, by rfl⟩ : syracuseStep 1434719 = 2152079) B2152079
theorem B4842611 : Blo 1433536 4842611 := bstep (se 1 (by rfl) ⟨3631958, by rfl⟩ : syracuseStep 4842611 = 7263917) B7263917
theorem B1434747 : Blo 1433536 1434747 := bstep (se 1 (by rfl) ⟨1076060, by rfl⟩ : syracuseStep 1434747 = 2152121) B2152121
theorem B1434799 : Blo 1433536 1434799 := bstep (se 1 (by rfl) ⟨1076099, by rfl⟩ : syracuseStep 1434799 = 2152199) B2152199
theorem B1434823 : Blo 1433536 1434823 := bstep (se 1 (by rfl) ⟨1076117, by rfl⟩ : syracuseStep 1434823 = 2152235) B2152235
theorem B1434843 : Blo 1433536 1434843 := bstep (se 1 (by rfl) ⟨1076132, by rfl⟩ : syracuseStep 1434843 = 2152265) B2152265
theorem B5448971 : Blo 1433536 5448971 := bstep (se 1 (by rfl) ⟨4086728, by rfl⟩ : syracuseStep 5448971 = 8173457) B8173457
theorem B1434919 : Blo 1433536 1434919 := bstep (se 1 (by rfl) ⟨1076189, by rfl⟩ : syracuseStep 1434919 = 2152379) B2152379
theorem B1434959 : Blo 1433536 1434959 := bstep (se 1 (by rfl) ⟨1076219, by rfl⟩ : syracuseStep 1434959 = 2152439) B2152439
theorem B1434975 : Blo 1433536 1434975 := bstep (se 1 (by rfl) ⟨1076231, by rfl⟩ : syracuseStep 1434975 = 2152463) B2152463
theorem B2041195 : Blo 1433536 2041195 := bstep (se 1 (by rfl) ⟨1530896, by rfl⟩ : syracuseStep 2041195 = 3061793) B3061793
theorem B1435003 : Blo 1433536 1435003 := bstep (se 1 (by rfl) ⟨1076252, by rfl⟩ : syracuseStep 1435003 = 2152505) B2152505
theorem B4842881 : Blo 1433536 4842881 := bstep (se 2 (by rfl) ⟨1816080, by rfl⟩ : syracuseStep 4842881 = 3632161) B3632161
theorem B1435055 : Blo 1433536 1435055 := bstep (se 1 (by rfl) ⟨1076291, by rfl⟩ : syracuseStep 1435055 = 2152583) B2152583
theorem B1435079 : Blo 1433536 1435079 := bstep (se 1 (by rfl) ⟨1076309, by rfl⟩ : syracuseStep 1435079 = 2152619) B2152619
theorem B4597211 : Blo 1433536 4597211 := bstep (se 1 (by rfl) ⟨3447908, by rfl⟩ : syracuseStep 4597211 = 6895817) B6895817
theorem B1435099 : Blo 1433536 1435099 := bstep (se 1 (by rfl) ⟨1076324, by rfl⟩ : syracuseStep 1435099 = 2152649) B2152649
theorem B1435175 : Blo 1433536 1435175 := bstep (se 1 (by rfl) ⟨1076381, by rfl⟩ : syracuseStep 1435175 = 2152763) B2152763
theorem B1435215 : Blo 1433536 1435215 := bstep (se 1 (by rfl) ⟨1076411, by rfl⟩ : syracuseStep 1435215 = 2152823) B2152823
theorem B1435231 : Blo 1433536 1435231 := bstep (se 1 (by rfl) ⟨1076423, by rfl⟩ : syracuseStep 1435231 = 2152847) B2152847
theorem B8169083 : Blo 1433536 8169083 := bstep (se 1 (by rfl) ⟨6126812, by rfl⟩ : syracuseStep 8169083 = 12253625) B12253625
theorem B3229307 : Blo 1433536 3229307 := bstep (se 1 (by rfl) ⟨2421980, by rfl⟩ : syracuseStep 3229307 = 4843961) B4843961
theorem B1435259 : Blo 1433536 1435259 := bstep (se 1 (by rfl) ⟨1076444, by rfl⟩ : syracuseStep 1435259 = 2152889) B2152889
theorem B1435311 : Blo 1433536 1435311 := bstep (se 1 (by rfl) ⟨1076483, by rfl⟩ : syracuseStep 1435311 = 2152967) B2152967
theorem B4359869 : Blo 1433536 4359869 := bstep (se 3 (by rfl) ⟨817475, by rfl⟩ : syracuseStep 4359869 = 1634951) B1634951
theorem B6129341 : Blo 1433536 6129341 := bstep (se 3 (by rfl) ⟨1149251, by rfl⟩ : syracuseStep 6129341 = 2298503) B2298503
theorem B11626183 : Blo 1433536 11626183 := bstep (se 1 (by rfl) ⟨8719637, by rfl⟩ : syracuseStep 11626183 = 17439275) B17439275
theorem B1435335 : Blo 1433536 1435335 := bstep (se 1 (by rfl) ⟨1076501, by rfl⟩ : syracuseStep 1435335 = 2153003) B2153003
theorem B5449427 : Blo 1433536 5449427 := bstep (se 1 (by rfl) ⟨4087070, by rfl⟩ : syracuseStep 5449427 = 8174141) B8174141
theorem B17450711 : Blo 1433536 17450711 := bstep (se 1 (by rfl) ⟨13088033, by rfl⟩ : syracuseStep 17450711 = 26176067) B26176067
theorem B1435355 : Blo 1433536 1435355 := bstep (se 1 (by rfl) ⟨1076516, by rfl⟩ : syracuseStep 1435355 = 2153033) B2153033
theorem B3229433 : Blo 1433536 3229433 := bstep (se 2 (by rfl) ⟨1211037, by rfl⟩ : syracuseStep 3229433 = 2422075) B2422075
theorem B1435431 : Blo 1433536 1435431 := bstep (se 1 (by rfl) ⟨1076573, by rfl⟩ : syracuseStep 1435431 = 2153147) B2153147
theorem B1435471 : Blo 1433536 1435471 := bstep (se 1 (by rfl) ⟨1076603, by rfl⟩ : syracuseStep 1435471 = 2153207) B2153207
theorem B1435487 : Blo 1433536 1435487 := bstep (se 1 (by rfl) ⟨1076615, by rfl⟩ : syracuseStep 1435487 = 2153231) B2153231
theorem B8169335 : Blo 1433536 8169335 := bstep (se 1 (by rfl) ⟨6127001, by rfl⟩ : syracuseStep 8169335 = 12254003) B12254003
theorem B1435515 : Blo 1433536 1435515 := bstep (se 1 (by rfl) ⟨1076636, by rfl⟩ : syracuseStep 1435515 = 2153273) B2153273
theorem B23275457 : Blo 1433536 23275457 := bstep (se 2 (by rfl) ⟨8728296, by rfl⟩ : syracuseStep 23275457 = 17456593) B17456593
theorem B7358471 : Blo 1433536 7358471 := bstep (se 1 (by rfl) ⟨5518853, by rfl⟩ : syracuseStep 7358471 = 11037707) B11037707
theorem B3229703 : Blo 1433536 3229703 := bstep (se 1 (by rfl) ⟨2422277, by rfl⟩ : syracuseStep 3229703 = 4844555) B4844555
theorem B2041895 : Blo 1433536 2041895 := bstep (se 1 (by rfl) ⟨1531421, by rfl⟩ : syracuseStep 2041895 = 3062843) B3062843
theorem B3229775 : Blo 1433536 3229775 := bstep (se 1 (by rfl) ⟨2422331, by rfl⟩ : syracuseStep 3229775 = 4844663) B4844663
theorem B36767843 : Blo 1433536 36767843 := bstep (se 1 (by rfl) ⟨27575882, by rfl⟩ : syracuseStep 36767843 = 55151765) B55151765
theorem B4843691 : Blo 1433536 4843691 := bstep (se 1 (by rfl) ⟨3632768, by rfl⟩ : syracuseStep 4843691 = 7265537) B7265537
theorem B3631351 : Blo 1433536 3631351 := bstep (se 1 (by rfl) ⟨2723513, by rfl⟩ : syracuseStep 3631351 = 5447027) B5447027
theorem B6130025 : Blo 1433536 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B3107177 : Blo 1433536 3107177 := bstep (se 2 (by rfl) ⟨1165191, by rfl⟩ : syracuseStep 3107177 = 2330383) B2330383
theorem B6547817 : Blo 1433536 6547817 := bstep (se 2 (by rfl) ⟨2455431, by rfl⟩ : syracuseStep 6547817 = 4910863) B4910863
theorem B2722223 : Blo 1433536 2722223 := bstep (se 1 (by rfl) ⟨2041667, by rfl⟩ : syracuseStep 2722223 = 4083335) B4083335
theorem B3631625 : Blo 1433536 3631625 := bstep (se 2 (by rfl) ⟨1361859, by rfl⟩ : syracuseStep 3631625 = 2723719) B2723719
theorem B3631655 : Blo 1433536 3631655 := bstep (se 1 (by rfl) ⟨2723741, by rfl⟩ : syracuseStep 3631655 = 5447483) B5447483
theorem B26176135 : Blo 1433536 26176135 := bstep (se 1 (by rfl) ⟨19632101, by rfl⟩ : syracuseStep 26176135 = 39264203) B39264203
theorem B5450429 : Blo 1433536 5450429 := bstep (se 3 (by rfl) ⟨1021955, by rfl⟩ : syracuseStep 5450429 = 2043911) B2043911
theorem B4844231 : Blo 1433536 4844231 := bstep (se 1 (by rfl) ⟨3633173, by rfl⟩ : syracuseStep 4844231 = 7266347) B7266347
theorem B9185993 : Blo 1433536 9185993 := bstep (se 2 (by rfl) ⟨3444747, by rfl⟩ : syracuseStep 9185993 = 6889495) B6889495
theorem B9194269 : Blo 1433536 9194269 := bstep (se 3 (by rfl) ⟨1723925, by rfl⟩ : syracuseStep 9194269 = 3447851) B3447851
theorem B7261001 : Blo 1433536 7261001 := bstep (se 2 (by rfl) ⟨2722875, by rfl⟩ : syracuseStep 7261001 = 5445751) B5445751
theorem B3631979 : Blo 1433536 3631979 := bstep (se 1 (by rfl) ⟨2723984, by rfl⟩ : syracuseStep 3631979 = 5447969) B5447969
theorem B2722747 : Blo 1433536 2722747 := bstep (se 1 (by rfl) ⟨2042060, by rfl⟩ : syracuseStep 2722747 = 4084121) B4084121
theorem B4082845 : Blo 1433536 4082845 := bstep (se 3 (by rfl) ⟨765533, by rfl⟩ : syracuseStep 4082845 = 1531067) B1531067
theorem B11635883 : Blo 1433536 11635883 := bstep (se 1 (by rfl) ⟨8726912, by rfl⟩ : syracuseStep 11635883 = 17453825) B17453825
theorem B2420111 : Blo 1433536 2420111 := bstep (se 1 (by rfl) ⟨1815083, by rfl⟩ : syracuseStep 2420111 = 3630167) B3630167
theorem B2723233 : Blo 1433536 2723233 := bstep (se 2 (by rfl) ⟨1021212, by rfl⟩ : syracuseStep 2723233 = 2042425) B2042425
theorem B10227107 : Blo 1433536 10227107 := bstep (se 1 (by rfl) ⟨7670330, by rfl⟩ : syracuseStep 10227107 = 15340661) B15340661
theorem B2043319 : Blo 1433536 2043319 := bstep (se 1 (by rfl) ⟨1532489, by rfl⟩ : syracuseStep 2043319 = 3064979) B3064979
theorem B3632627 : Blo 1433536 3632627 := bstep (se 1 (by rfl) ⟨2724470, by rfl⟩ : syracuseStep 3632627 = 5448941) B5448941
theorem B2420347 : Blo 1433536 2420347 := bstep (se 1 (by rfl) ⟨1815260, by rfl⟩ : syracuseStep 2420347 = 3630521) B3630521
theorem B104697521 : Blo 1433536 104697521 := bstep (se 2 (by rfl) ⟨39261570, by rfl⟩ : syracuseStep 104697521 = 78523141) B78523141
theorem B5443321 : Blo 1433536 5443321 := bstep (se 2 (by rfl) ⟨2041245, by rfl⟩ : syracuseStep 5443321 = 4082491) B4082491
theorem B2150327 : Blo 1433536 2150327 := bstep (se 1 (by rfl) ⟨1612745, by rfl⟩ : syracuseStep 2150327 = 3225491) B3225491
theorem B3633083 : Blo 1433536 3633083 := bstep (se 1 (by rfl) ⟨2724812, by rfl⟩ : syracuseStep 3633083 = 5449625) B5449625
theorem B2150363 : Blo 1433536 2150363 := bstep (se 1 (by rfl) ⟨1612772, by rfl⟩ : syracuseStep 2150363 = 3225545) B3225545
theorem B1814491 : Blo 1433536 1814491 := bstep (se 1 (by rfl) ⟨1360868, by rfl⟩ : syracuseStep 1814491 = 2721737) B2721737
theorem B17018909 : Blo 1433536 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B9809977 : Blo 1433536 9809977 := bstep (se 2 (by rfl) ⟨3678741, by rfl⟩ : syracuseStep 9809977 = 7357483) B7357483
theorem B7262297 : Blo 1433536 7262297 := bstep (se 2 (by rfl) ⟨2723361, by rfl⟩ : syracuseStep 7262297 = 5446723) B5446723
theorem B2150831 : Blo 1433536 2150831 := bstep (se 1 (by rfl) ⟨1613123, by rfl⟩ : syracuseStep 2150831 = 3226247) B3226247
theorem B2421211 : Blo 1433536 2421211 := bstep (se 1 (by rfl) ⟨1815908, by rfl⟩ : syracuseStep 2421211 = 3631817) B3631817
theorem B10334729 : Blo 1433536 10334729 := bstep (se 2 (by rfl) ⟨3875523, by rfl⟩ : syracuseStep 10334729 = 7751047) B7751047
theorem B2150921 : Blo 1433536 2150921 := bstep (se 2 (by rfl) ⟨806595, by rfl⟩ : syracuseStep 2150921 = 1613191) B1613191
theorem B2150951 : Blo 1433536 2150951 := bstep (se 1 (by rfl) ⟨1613213, by rfl⟩ : syracuseStep 2150951 = 3226427) B3226427
theorem B1552975 : Blo 1433536 1552975 := bstep (se 1 (by rfl) ⟨1164731, by rfl⟩ : syracuseStep 1552975 = 2329463) B2329463
theorem B2151035 : Blo 1433536 2151035 := bstep (se 1 (by rfl) ⟨1613276, by rfl⟩ : syracuseStep 2151035 = 3226553) B3226553
theorem B2151161 : Blo 1433536 2151161 := bstep (se 2 (by rfl) ⟨806685, by rfl⟩ : syracuseStep 2151161 = 1613371) B1613371
theorem B8278787 : Blo 1433536 8278787 := bstep (se 1 (by rfl) ⟨6209090, by rfl⟩ : syracuseStep 8278787 = 12418181) B12418181
theorem B20960003 : Blo 1433536 20960003 := bstep (se 1 (by rfl) ⟨15720002, by rfl⟩ : syracuseStep 20960003 = 31440005) B31440005
theorem B5239619 : Blo 1433536 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B2151263 : Blo 1433536 2151263 := bstep (se 1 (by rfl) ⟨1613447, by rfl⟩ : syracuseStep 2151263 = 3226895) B3226895
theorem B2151275 : Blo 1433536 2151275 := bstep (se 1 (by rfl) ⟨1613456, by rfl⟩ : syracuseStep 2151275 = 3226913) B3226913
theorem B3445679 : Blo 1433536 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B11047985 : Blo 1433536 11047985 := bstep (se 2 (by rfl) ⟨4142994, by rfl⟩ : syracuseStep 11047985 = 8285989) B8285989
theorem B4084793 : Blo 1433536 4084793 := bstep (se 2 (by rfl) ⟨1531797, by rfl⟩ : syracuseStep 4084793 = 3063595) B3063595
theorem B2151503 : Blo 1433536 2151503 := bstep (se 1 (by rfl) ⟨1613627, by rfl⟩ : syracuseStep 2151503 = 3227255) B3227255
theorem B2421839 : Blo 1433536 2421839 := bstep (se 1 (by rfl) ⟨1816379, by rfl⟩ : syracuseStep 2421839 = 3632759) B3632759
theorem B2298959 : Blo 1433536 2298959 := bstep (se 1 (by rfl) ⟨1724219, by rfl⟩ : syracuseStep 2298959 = 3448439) B3448439
theorem B5444765 : Blo 1433536 5444765 := bstep (se 3 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 5444765 = 2041787) B2041787
theorem B5444779 : Blo 1433536 5444779 := bstep (se 1 (by rfl) ⟨4083584, by rfl⟩ : syracuseStep 5444779 = 8167169) B8167169
theorem B2151623 : Blo 1433536 2151623 := bstep (se 1 (by rfl) ⟨1613717, by rfl⟩ : syracuseStep 2151623 = 3227435) B3227435
theorem B39777635 : Blo 1433536 39777635 := bstep (se 1 (by rfl) ⟨29833226, by rfl⟩ : syracuseStep 39777635 = 59666453) B59666453
theorem B2151785 : Blo 1433536 2151785 := bstep (se 2 (by rfl) ⟨806919, by rfl⟩ : syracuseStep 2151785 = 1613839) B1613839
theorem B10892717 : Blo 1433536 10892717 := bstep (se 3 (by rfl) ⟨2042384, by rfl⟩ : syracuseStep 10892717 = 4084769) B4084769
theorem B2151863 : Blo 1433536 2151863 := bstep (se 1 (by rfl) ⟨1613897, by rfl⟩ : syracuseStep 2151863 = 3227795) B3227795
theorem B8173001 : Blo 1433536 8173001 := bstep (se 2 (by rfl) ⟨3064875, by rfl⟩ : syracuseStep 8173001 = 6129751) B6129751
theorem B5445083 : Blo 1433536 5445083 := bstep (se 1 (by rfl) ⟨4083812, by rfl⟩ : syracuseStep 5445083 = 8167625) B8167625
theorem B2151899 : Blo 1433536 2151899 := bstep (se 1 (by rfl) ⟨1613924, by rfl⟩ : syracuseStep 2151899 = 3227849) B3227849
theorem B10900979 : Blo 1433536 10900979 := bstep (se 1 (by rfl) ⟨8175734, by rfl⟩ : syracuseStep 10900979 = 16351469) B16351469
theorem B8164961 : Blo 1433536 8164961 := bstep (se 2 (by rfl) ⟨3061860, by rfl⟩ : syracuseStep 8164961 = 6123721) B6123721
theorem B6895201 : Blo 1433536 6895201 := bstep (se 2 (by rfl) ⟨2585700, by rfl⟩ : syracuseStep 6895201 = 5171401) B5171401
theorem B4839047 : Blo 1433536 4839047 := bstep (se 1 (by rfl) ⟨3629285, by rfl⟩ : syracuseStep 4839047 = 7258571) B7258571
theorem B10335883 : Blo 1433536 10335883 := bstep (se 1 (by rfl) ⟨7751912, by rfl⟩ : syracuseStep 10335883 = 15503825) B15503825
theorem B4839101 : Blo 1433536 4839101 := bstep (se 3 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 4839101 = 1814663) B1814663
theorem B4839263 : Blo 1433536 4839263 := bstep (se 1 (by rfl) ⟨3629447, by rfl⟩ : syracuseStep 4839263 = 7258895) B7258895
theorem B8730487 : Blo 1433536 8730487 := bstep (se 1 (by rfl) ⟨6547865, by rfl⟩ : syracuseStep 8730487 = 13095731) B13095731
theorem B2152367 : Blo 1433536 2152367 := bstep (se 1 (by rfl) ⟨1614275, by rfl⟩ : syracuseStep 2152367 = 3228551) B3228551
theorem B3225527 : Blo 1433536 3225527 := bstep (se 1 (by rfl) ⟨2419145, by rfl⟩ : syracuseStep 3225527 = 4838291) B4838291
theorem B4839425 : Blo 1433536 4839425 := bstep (se 2 (by rfl) ⟨1814784, by rfl⟩ : syracuseStep 4839425 = 3629569) B3629569
theorem B2152457 : Blo 1433536 2152457 := bstep (se 2 (by rfl) ⟨807171, by rfl⟩ : syracuseStep 2152457 = 1614343) B1614343
theorem B2152487 : Blo 1433536 2152487 := bstep (se 1 (by rfl) ⟨1614365, by rfl⟩ : syracuseStep 2152487 = 3228731) B3228731
theorem B2152571 : Blo 1433536 2152571 := bstep (se 1 (by rfl) ⟨1614428, by rfl⟩ : syracuseStep 2152571 = 3228857) B3228857
theorem B2152697 : Blo 1433536 2152697 := bstep (se 2 (by rfl) ⟨807261, by rfl⟩ : syracuseStep 2152697 = 1614523) B1614523
theorem B9189683 : Blo 1433536 9189683 := bstep (se 1 (by rfl) ⟨6892262, by rfl⟩ : syracuseStep 9189683 = 13784525) B13784525
theorem B2152799 : Blo 1433536 2152799 := bstep (se 1 (by rfl) ⟨1614599, by rfl⟩ : syracuseStep 2152799 = 3229199) B3229199
theorem B2152811 : Blo 1433536 2152811 := bstep (se 1 (by rfl) ⟨1614608, by rfl⟩ : syracuseStep 2152811 = 3229217) B3229217
theorem B5167597 : Blo 1433536 5167597 := bstep (se 3 (by rfl) ⟨968924, by rfl⟩ : syracuseStep 5167597 = 1937849) B1937849
theorem B3226121 : Blo 1433536 3226121 := bstep (se 2 (by rfl) ⟨1209795, by rfl⟩ : syracuseStep 3226121 = 2419591) B2419591
theorem B9189911 : Blo 1433536 9189911 := bstep (se 1 (by rfl) ⟨6892433, by rfl⟩ : syracuseStep 9189911 = 13784867) B13784867
theorem B7363105 : Blo 1433536 7363105 := bstep (se 2 (by rfl) ⟨2761164, by rfl⟩ : syracuseStep 7363105 = 5522329) B5522329
theorem B2153039 : Blo 1433536 2153039 := bstep (se 1 (by rfl) ⟨1614779, by rfl⟩ : syracuseStep 2153039 = 3229559) B3229559
theorem B2153159 : Blo 1433536 2153159 := bstep (se 1 (by rfl) ⟨1614869, by rfl⟩ : syracuseStep 2153159 = 3229739) B3229739
theorem B4840235 : Blo 1433536 4840235 := bstep (se 1 (by rfl) ⟨3630176, by rfl⟩ : syracuseStep 4840235 = 7260353) B7260353
theorem B3226463 : Blo 1433536 3226463 := bstep (se 1 (by rfl) ⟨2419847, by rfl⟩ : syracuseStep 3226463 = 4839695) B4839695
theorem B156941171 : Blo 1433536 156941171 := bstep (se 1 (by rfl) ⟨117705878, by rfl⟩ : syracuseStep 156941171 = 235411757) B235411757
theorem B12262373 : Blo 1433536 12262373 := bstep (se 4 (by rfl) ⟨1149597, by rfl⟩ : syracuseStep 12262373 = 2299195) B2299195
theorem B8166419 : Blo 1433536 8166419 := bstep (se 1 (by rfl) ⟨6124814, by rfl⟩ : syracuseStep 8166419 = 12249629) B12249629
theorem B3226643 : Blo 1433536 3226643 := bstep (se 1 (by rfl) ⟨2419982, by rfl⟩ : syracuseStep 3226643 = 4839965) B4839965
theorem B4840505 : Blo 1433536 4840505 := bstep (se 2 (by rfl) ⟨1815189, by rfl⟩ : syracuseStep 4840505 = 3630379) B3630379
theorem B44194895 : Blo 1433536 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B8723609 : Blo 1433536 8723609 := bstep (se 2 (by rfl) ⟨3271353, by rfl⟩ : syracuseStep 8723609 = 6542707) B6542707
theorem B13090085 : Blo 1433536 13090085 := bstep (se 4 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 13090085 = 2454391) B2454391
theorem B3226985 : Blo 1433536 3226985 := bstep (se 2 (by rfl) ⟨1210119, by rfl⟩ : syracuseStep 3226985 = 2420239) B2420239
theorem B4840829 : Blo 1433536 4840829 := bstep (se 3 (by rfl) ⟨907655, by rfl⟩ : syracuseStep 4840829 = 1815311) B1815311
theorem B4841099 : Blo 1433536 4841099 := bstep (se 1 (by rfl) ⟨3630824, by rfl⟩ : syracuseStep 4841099 = 7261649) B7261649
theorem B4087435 : Blo 1433536 4087435 := bstep (se 1 (by rfl) ⟨3065576, by rfl⟩ : syracuseStep 4087435 = 6131153) B6131153
theorem B3628759 : Blo 1433536 3628759 := bstep (se 1 (by rfl) ⟨2721569, by rfl⟩ : syracuseStep 3628759 = 5443139) B5443139
theorem B34889453 : Blo 1433536 34889453 := bstep (se 3 (by rfl) ⟨6541772, by rfl⟩ : syracuseStep 34889453 = 13083545) B13083545
theorem B10895147 : Blo 1433536 10895147 := bstep (se 1 (by rfl) ⟨8171360, by rfl⟩ : syracuseStep 10895147 = 16342721) B16342721
theorem B6889283 : Blo 1433536 6889283 := bstep (se 1 (by rfl) ⟨5166962, by rfl⟩ : syracuseStep 6889283 = 10333925) B10333925
theorem B7257923 : Blo 1433536 7257923 := bstep (se 1 (by rfl) ⟨5443442, by rfl⟩ : syracuseStep 7257923 = 10886885) B10886885
theorem B15720259 : Blo 1433536 15720259 := bstep (se 1 (by rfl) ⟨11790194, by rfl⟩ : syracuseStep 15720259 = 23580389) B23580389
theorem B6127427 : Blo 1433536 6127427 := bstep (se 1 (by rfl) ⟨4595570, by rfl⟩ : syracuseStep 6127427 = 9191141) B9191141
theorem B5816173 : Blo 1433536 5816173 := bstep (se 3 (by rfl) ⟨1090532, by rfl⟩ : syracuseStep 5816173 = 2181065) B2181065
theorem B3227579 : Blo 1433536 3227579 := bstep (se 1 (by rfl) ⟨2420684, by rfl⟩ : syracuseStep 3227579 = 4841369) B4841369
theorem B1433543 : Blo 1433536 1433543 := bstep (se 1 (by rfl) ⟨1075157, by rfl⟩ : syracuseStep 1433543 = 2150315) B2150315
theorem B1433563 : Blo 1433536 1433563 := bstep (se 1 (by rfl) ⟨1075172, by rfl⟩ : syracuseStep 1433563 = 2150345) B2150345
theorem B11345939 : Blo 1433536 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B4841531 : Blo 1433536 4841531 := bstep (se 1 (by rfl) ⟨3631148, by rfl⟩ : syracuseStep 4841531 = 7262297) B7262297
theorem B1433887 : Blo 1433536 1433887 := bstep (se 1 (by rfl) ⟨1075415, by rfl⟩ : syracuseStep 1433887 = 2150831) B2150831
theorem B4841801 : Blo 1433536 4841801 := bstep (se 2 (by rfl) ⟨1815675, by rfl⟩ : syracuseStep 4841801 = 3631351) B3631351
theorem B1433947 : Blo 1433536 1433947 := bstep (se 1 (by rfl) ⟨1075460, by rfl⟩ : syracuseStep 1433947 = 2150921) B2150921
theorem B3228011 : Blo 1433536 3228011 := bstep (se 1 (by rfl) ⟨2421008, by rfl⟩ : syracuseStep 3228011 = 4842017) B4842017
theorem B1433967 : Blo 1433536 1433967 := bstep (se 1 (by rfl) ⟨1075475, by rfl⟩ : syracuseStep 1433967 = 2150951) B2150951
theorem B1434023 : Blo 1433536 1434023 := bstep (se 1 (by rfl) ⟨1075517, by rfl⟩ : syracuseStep 1434023 = 2151035) B2151035
theorem B1434107 : Blo 1433536 1434107 := bstep (se 1 (by rfl) ⟨1075580, by rfl⟩ : syracuseStep 1434107 = 2151161) B2151161
theorem B3228155 : Blo 1433536 3228155 := bstep (se 1 (by rfl) ⟨2421116, by rfl⟩ : syracuseStep 3228155 = 4842233) B4842233
theorem B1434175 : Blo 1433536 1434175 := bstep (se 1 (by rfl) ⟨1075631, by rfl⟩ : syracuseStep 1434175 = 2151263) B2151263
theorem B16335431 : Blo 1433536 16335431 := bstep (se 1 (by rfl) ⟨12251573, by rfl⟩ : syracuseStep 16335431 = 24503147) B24503147
theorem B1434183 : Blo 1433536 1434183 := bstep (se 1 (by rfl) ⟨1075637, by rfl⟩ : syracuseStep 1434183 = 2151275) B2151275
theorem B1291240055 : Blo 1433536 1291240055 := bstep (se 1 (by rfl) ⟨968430041, by rfl⟩ : syracuseStep 1291240055 = 1936860083) B1936860083
theorem B3228281 : Blo 1433536 3228281 := bstep (se 2 (by rfl) ⟨1210605, by rfl⟩ : syracuseStep 3228281 = 2421211) B2421211
theorem B80724599 : Blo 1433536 80724599 := bstep (se 1 (by rfl) ⟨60543449, by rfl⟩ : syracuseStep 80724599 = 121086899) B121086899
theorem B6890129 : Blo 1433536 6890129 := bstep (se 2 (by rfl) ⟨2583798, by rfl⟩ : syracuseStep 6890129 = 5167597) B5167597
theorem B3228335 : Blo 1433536 3228335 := bstep (se 1 (by rfl) ⟨2421251, by rfl⟩ : syracuseStep 3228335 = 4842503) B4842503
theorem B7365323 : Blo 1433536 7365323 := bstep (se 1 (by rfl) ⟨5523992, by rfl⟩ : syracuseStep 7365323 = 11047985) B11047985
theorem B1434335 : Blo 1433536 1434335 := bstep (se 1 (by rfl) ⟨1075751, by rfl⟩ : syracuseStep 1434335 = 2151503) B2151503
theorem B1614559 : Blo 1433536 1614559 := bstep (se 1 (by rfl) ⟨1210919, by rfl⟩ : syracuseStep 1614559 = 2421839) B2421839
theorem B1532639 : Blo 1433536 1532639 := bstep (se 1 (by rfl) ⟨1149479, by rfl⟩ : syracuseStep 1532639 = 2298959) B2298959
theorem B3228407 : Blo 1433536 3228407 := bstep (se 1 (by rfl) ⟨2421305, by rfl⟩ : syracuseStep 3228407 = 4842611) B4842611
theorem B3629843 : Blo 1433536 3629843 := bstep (se 1 (by rfl) ⟨2722382, by rfl⟩ : syracuseStep 3629843 = 5444765) B5444765
theorem B1434415 : Blo 1433536 1434415 := bstep (se 1 (by rfl) ⟨1075811, by rfl⟩ : syracuseStep 1434415 = 2151623) B2151623
theorem B26518423 : Blo 1433536 26518423 := bstep (se 1 (by rfl) ⟨19888817, by rfl⟩ : syracuseStep 26518423 = 39777635) B39777635
theorem B1434523 : Blo 1433536 1434523 := bstep (se 1 (by rfl) ⟨1075892, by rfl⟩ : syracuseStep 1434523 = 2151785) B2151785
theorem B3228587 : Blo 1433536 3228587 := bstep (se 1 (by rfl) ⟨2421440, by rfl⟩ : syracuseStep 3228587 = 4842881) B4842881
theorem B1434575 : Blo 1433536 1434575 := bstep (se 1 (by rfl) ⟨1075931, by rfl⟩ : syracuseStep 1434575 = 2151863) B2151863
theorem B5448667 : Blo 1433536 5448667 := bstep (se 1 (by rfl) ⟨4086500, by rfl⟩ : syracuseStep 5448667 = 8173001) B8173001
theorem B3630055 : Blo 1433536 3630055 := bstep (se 1 (by rfl) ⟨2722541, by rfl⟩ : syracuseStep 3630055 = 5445083) B5445083
theorem B1434599 : Blo 1433536 1434599 := bstep (se 1 (by rfl) ⟨1075949, by rfl⟩ : syracuseStep 1434599 = 2151899) B2151899
theorem B3064807 : Blo 1433536 3064807 := bstep (se 1 (by rfl) ⟨2298605, by rfl⟩ : syracuseStep 3064807 = 4597211) B4597211
theorem B7267319 : Blo 1433536 7267319 := bstep (se 1 (by rfl) ⟨5450489, by rfl⟩ : syracuseStep 7267319 = 10900979) B10900979
theorem B27272285 : Blo 1433536 27272285 := bstep (se 3 (by rfl) ⟨5113553, by rfl⟩ : syracuseStep 27272285 = 10227107) B10227107
theorem B11633807 : Blo 1433536 11633807 := bstep (se 1 (by rfl) ⟨8725355, by rfl⟩ : syracuseStep 11633807 = 17450711) B17450711
theorem B3630329 : Blo 1433536 3630329 := bstep (se 2 (by rfl) ⟨1361373, by rfl⟩ : syracuseStep 3630329 = 2722747) B2722747
theorem B1434911 : Blo 1433536 1434911 := bstep (se 1 (by rfl) ⟨1076183, by rfl⟩ : syracuseStep 1434911 = 2152367) B2152367
theorem B15516971 : Blo 1433536 15516971 := bstep (se 1 (by rfl) ⟨11637728, by rfl⟩ : syracuseStep 15516971 = 23275457) B23275457
theorem B1434971 : Blo 1433536 1434971 := bstep (se 1 (by rfl) ⟨1076228, by rfl⟩ : syracuseStep 1434971 = 2152457) B2152457
theorem B27559277 : Blo 1433536 27559277 := bstep (se 3 (by rfl) ⟨5167364, by rfl⟩ : syracuseStep 27559277 = 10334729) B10334729
theorem B1434991 : Blo 1433536 1434991 := bstep (se 1 (by rfl) ⟨1076243, by rfl⟩ : syracuseStep 1434991 = 2152487) B2152487
theorem B24511895 : Blo 1433536 24511895 := bstep (se 1 (by rfl) ⟨18383921, by rfl⟩ : syracuseStep 24511895 = 36767843) B36767843
theorem B1435047 : Blo 1433536 1435047 := bstep (se 1 (by rfl) ⟨1076285, by rfl⟩ : syracuseStep 1435047 = 2152571) B2152571
theorem B3229127 : Blo 1433536 3229127 := bstep (se 1 (by rfl) ⟨2421845, by rfl⟩ : syracuseStep 3229127 = 4843691) B4843691
theorem B1435131 : Blo 1433536 1435131 := bstep (se 1 (by rfl) ⟨1076348, by rfl⟩ : syracuseStep 1435131 = 2152697) B2152697
theorem B7259705 : Blo 1433536 7259705 := bstep (se 2 (by rfl) ⟨2722389, by rfl⟩ : syracuseStep 7259705 = 5444779) B5444779
theorem B1435199 : Blo 1433536 1435199 := bstep (se 1 (by rfl) ⟨1076399, by rfl⟩ : syracuseStep 1435199 = 2152799) B2152799
theorem B1435207 : Blo 1433536 1435207 := bstep (se 1 (by rfl) ⟨1076405, by rfl⟩ : syracuseStep 1435207 = 2152811) B2152811
theorem B33130133 : Blo 1433536 33130133 := bstep (se 6 (by rfl) ⟨776487, by rfl⟩ : syracuseStep 33130133 = 1552975) B1552975
theorem B1435359 : Blo 1433536 1435359 := bstep (se 1 (by rfl) ⟨1076519, by rfl⟩ : syracuseStep 1435359 = 2153039) B2153039
theorem B3229487 : Blo 1433536 3229487 := bstep (se 1 (by rfl) ⟨2422115, by rfl⟩ : syracuseStep 3229487 = 4844231) B4844231
theorem B1435439 : Blo 1433536 1435439 := bstep (se 1 (by rfl) ⟨1076579, by rfl⟩ : syracuseStep 1435439 = 2153159) B2153159
theorem B2721593 : Blo 1433536 2721593 := bstep (se 2 (by rfl) ⟨1020597, by rfl⟩ : syracuseStep 2721593 = 2041195) B2041195
theorem B3630977 : Blo 1433536 3630977 := bstep (se 2 (by rfl) ⟨1361616, by rfl⟩ : syracuseStep 3630977 = 2723233) B2723233
theorem B9193601 : Blo 1433536 9193601 := bstep (se 2 (by rfl) ⟨3447600, by rfl⟩ : syracuseStep 9193601 = 6895201) B6895201
theorem B13781177 : Blo 1433536 13781177 := bstep (se 2 (by rfl) ⟨5167941, by rfl⟩ : syracuseStep 13781177 = 10335883) B10335883
theorem B5449913 : Blo 1433536 5449913 := bstep (se 2 (by rfl) ⟨2043717, by rfl⟩ : syracuseStep 5449913 = 4087435) B4087435
theorem B8726723 : Blo 1433536 8726723 := bstep (se 1 (by rfl) ⟨6545042, by rfl⟩ : syracuseStep 8726723 = 13090085) B13090085
theorem B15501577 : Blo 1433536 15501577 := bstep (se 2 (by rfl) ⟨5813091, by rfl⟩ : syracuseStep 15501577 = 11626183) B11626183
theorem B69798347 : Blo 1433536 69798347 := bstep (se 1 (by rfl) ⟨52348760, by rfl⟩ : syracuseStep 69798347 = 104697521) B104697521
theorem B23259635 : Blo 1433536 23259635 := bstep (se 1 (by rfl) ⟨17444726, by rfl⟩ : syracuseStep 23259635 = 34889453) B34889453
theorem B2419321 : Blo 1433536 2419321 := bstep (se 2 (by rfl) ⟨907245, by rfl⟩ : syracuseStep 2419321 = 1814491) B1814491
theorem B3631787 : Blo 1433536 3631787 := bstep (se 1 (by rfl) ⟨2723840, by rfl⟩ : syracuseStep 3631787 = 5447681) B5447681
theorem B2419375 : Blo 1433536 2419375 := bstep (se 1 (by rfl) ⟨1814531, by rfl⟩ : syracuseStep 2419375 = 3629063) B3629063
theorem B69823255 : Blo 1433536 69823255 := bstep (se 1 (by rfl) ⟨52367441, by rfl⟩ : syracuseStep 69823255 = 104734883) B104734883
theorem B18394127 : Blo 1433536 18394127 := bstep (se 1 (by rfl) ⟨13795595, by rfl⟩ : syracuseStep 18394127 = 27591191) B27591191
theorem B3493079 : Blo 1433536 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B1453403 : Blo 1433536 1453403 := bstep (se 1 (by rfl) ⟨1090052, by rfl⟩ : syracuseStep 1453403 = 2180105) B2180105
theorem B2723195 : Blo 1433536 2723195 := bstep (se 1 (by rfl) ⟨2042396, by rfl⟩ : syracuseStep 2723195 = 4084793) B4084793
theorem B3632647 : Blo 1433536 3632647 := bstep (se 1 (by rfl) ⟨2724485, by rfl⟩ : syracuseStep 3632647 = 5448971) B5448971
theorem B34901513 : Blo 1433536 34901513 := bstep (se 2 (by rfl) ⟨13088067, by rfl⟩ : syracuseStep 34901513 = 26176135) B26176135
theorem B7261811 : Blo 1433536 7261811 := bstep (se 1 (by rfl) ⟨5446358, by rfl⟩ : syracuseStep 7261811 = 10892717) B10892717
theorem B12259025 : Blo 1433536 12259025 := bstep (se 2 (by rfl) ⟨4597134, by rfl⟩ : syracuseStep 12259025 = 9194269) B9194269
theorem B5443307 : Blo 1433536 5443307 := bstep (se 1 (by rfl) ⟨4082480, by rfl⟩ : syracuseStep 5443307 = 8164961) B8164961
theorem B3632951 : Blo 1433536 3632951 := bstep (se 1 (by rfl) ⟨2724713, by rfl⟩ : syracuseStep 3632951 = 5449427) B5449427
theorem B2150351 : Blo 1433536 2150351 := bstep (se 1 (by rfl) ⟨1612763, by rfl⟩ : syracuseStep 2150351 = 3225527) B3225527
theorem B5443793 : Blo 1433536 5443793 := bstep (se 2 (by rfl) ⟨2041422, by rfl⟩ : syracuseStep 5443793 = 4082845) B4082845
theorem B1814815 : Blo 1433536 1814815 := bstep (se 1 (by rfl) ⟨1361111, by rfl⟩ : syracuseStep 1814815 = 2722223) B2722223
theorem B2150747 : Blo 1433536 2150747 := bstep (se 1 (by rfl) ⟨1613060, by rfl⟩ : syracuseStep 2150747 = 3226121) B3226121
theorem B2421083 : Blo 1433536 2421083 := bstep (se 1 (by rfl) ⟨1815812, by rfl⟩ : syracuseStep 2421083 = 3631625) B3631625
theorem B2421103 : Blo 1433536 2421103 := bstep (se 1 (by rfl) ⟨1815827, by rfl⟩ : syracuseStep 2421103 = 3631655) B3631655
theorem B3633619 : Blo 1433536 3633619 := bstep (se 1 (by rfl) ⟨2725214, by rfl⟩ : syracuseStep 3633619 = 5450429) B5450429
theorem B6123995 : Blo 1433536 6123995 := bstep (se 1 (by rfl) ⟨4592996, by rfl⟩ : syracuseStep 6123995 = 9185993) B9185993
theorem B2150975 : Blo 1433536 2150975 := bstep (se 1 (by rfl) ⟨1613231, by rfl⟩ : syracuseStep 2150975 = 3226463) B3226463
theorem B2421319 : Blo 1433536 2421319 := bstep (se 1 (by rfl) ⟨1815989, by rfl⟩ : syracuseStep 2421319 = 3631979) B3631979
theorem B2724425 : Blo 1433536 2724425 := bstep (se 2 (by rfl) ⟨1021659, by rfl⟩ : syracuseStep 2724425 = 2043319) B2043319
theorem B5444279 : Blo 1433536 5444279 := bstep (se 1 (by rfl) ⟨4083209, by rfl⟩ : syracuseStep 5444279 = 8166419) B8166419
theorem B2151095 : Blo 1433536 2151095 := bstep (se 1 (by rfl) ⟨1613321, by rfl⟩ : syracuseStep 2151095 = 3226643) B3226643
theorem B29463263 : Blo 1433536 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B16339805 : Blo 1433536 16339805 := bstep (se 3 (by rfl) ⟨3063713, by rfl⟩ : syracuseStep 16339805 = 6127427) B6127427
theorem B2151323 : Blo 1433536 2151323 := bstep (se 1 (by rfl) ⟨1613492, by rfl⟩ : syracuseStep 2151323 = 3226985) B3226985
theorem B4838345 : Blo 1433536 4838345 := bstep (se 2 (by rfl) ⟨1814379, by rfl⟩ : syracuseStep 4838345 = 3628759) B3628759
theorem B2421751 : Blo 1433536 2421751 := bstep (se 1 (by rfl) ⟨1816313, by rfl⟩ : syracuseStep 2421751 = 3632627) B3632627
theorem B20960345 : Blo 1433536 20960345 := bstep (se 2 (by rfl) ⟨7860129, by rfl⟩ : syracuseStep 20960345 = 15720259) B15720259
theorem B9188477 : Blo 1433536 9188477 := bstep (se 3 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 9188477 = 3445679) B3445679
theorem B7754897 : Blo 1433536 7754897 := bstep (se 2 (by rfl) ⟨2908086, by rfl⟩ : syracuseStep 7754897 = 5816173) B5816173
theorem B7263431 : Blo 1433536 7263431 := bstep (se 1 (by rfl) ⟨5447573, by rfl⟩ : syracuseStep 7263431 = 10895147) B10895147
theorem B4592855 : Blo 1433536 4592855 := bstep (se 1 (by rfl) ⟨3444641, by rfl⟩ : syracuseStep 4592855 = 6889283) B6889283
theorem B4838615 : Blo 1433536 4838615 := bstep (se 1 (by rfl) ⟨3628961, by rfl⟩ : syracuseStep 4838615 = 7257923) B7257923
theorem B2151719 : Blo 1433536 2151719 := bstep (se 1 (by rfl) ⟨1613789, by rfl⟩ : syracuseStep 2151719 = 3227579) B3227579
theorem B2422055 : Blo 1433536 2422055 := bstep (se 1 (by rfl) ⟨1816541, by rfl⟩ : syracuseStep 2422055 = 3633083) B3633083
theorem B7263593 : Blo 1433536 7263593 := bstep (se 2 (by rfl) ⟨2723847, by rfl⟩ : syracuseStep 7263593 = 5447695) B5447695
theorem B2151803 : Blo 1433536 2151803 := bstep (se 1 (by rfl) ⟨1613852, by rfl⟩ : syracuseStep 2151803 = 3227705) B3227705
theorem B13079969 : Blo 1433536 13079969 := bstep (se 2 (by rfl) ⟨4904988, by rfl⟩ : syracuseStep 13079969 = 9809977) B9809977
theorem B5445053 : Blo 1433536 5445053 := bstep (se 3 (by rfl) ⟨1020947, by rfl⟩ : syracuseStep 5445053 = 2041895) B2041895
theorem B2151929 : Blo 1433536 2151929 := bstep (se 2 (by rfl) ⟨806973, by rfl⟩ : syracuseStep 2151929 = 1613947) B1613947
theorem B39269893 : Blo 1433536 39269893 := bstep (se 4 (by rfl) ⟨3681552, by rfl⟩ : syracuseStep 39269893 = 7363105) B7363105
theorem B2152031 : Blo 1433536 2152031 := bstep (se 1 (by rfl) ⟨1614023, by rfl⟩ : syracuseStep 2152031 = 3228047) B3228047
theorem B2152247 : Blo 1433536 2152247 := bstep (se 1 (by rfl) ⟨1614185, by rfl⟩ : syracuseStep 2152247 = 3228371) B3228371
theorem B5519191 : Blo 1433536 5519191 := bstep (se 1 (by rfl) ⟨4139393, by rfl⟩ : syracuseStep 5519191 = 8278787) B8278787
theorem B2152553 : Blo 1433536 2152553 := bstep (se 2 (by rfl) ⟨807207, by rfl⟩ : syracuseStep 2152553 = 1614415) B1614415
theorem B5446055 : Blo 1433536 5446055 := bstep (se 1 (by rfl) ⟨4084541, by rfl⟩ : syracuseStep 5446055 = 8169083) B8169083
theorem B2152871 : Blo 1433536 2152871 := bstep (se 1 (by rfl) ⟨1614653, by rfl⟩ : syracuseStep 2152871 = 3229307) B3229307
theorem B3226031 : Blo 1433536 3226031 := bstep (se 1 (by rfl) ⟨2419523, by rfl⟩ : syracuseStep 3226031 = 4839047) B4839047
theorem B2906579 : Blo 1433536 2906579 := bstep (se 1 (by rfl) ⟨2179934, by rfl⟩ : syracuseStep 2906579 = 4359869) B4359869
theorem B3226067 : Blo 1433536 3226067 := bstep (se 1 (by rfl) ⟨2419550, by rfl⟩ : syracuseStep 3226067 = 4839101) B4839101
theorem B4086227 : Blo 1433536 4086227 := bstep (se 1 (by rfl) ⟨3064670, by rfl⟩ : syracuseStep 4086227 = 6129341) B6129341
theorem B2152955 : Blo 1433536 2152955 := bstep (se 1 (by rfl) ⟨1614716, by rfl⟩ : syracuseStep 2152955 = 3229433) B3229433
theorem B3226175 : Blo 1433536 3226175 := bstep (se 1 (by rfl) ⟨2419631, by rfl⟩ : syracuseStep 3226175 = 4839263) B4839263
theorem B5446223 : Blo 1433536 5446223 := bstep (se 1 (by rfl) ⟨4084667, by rfl⟩ : syracuseStep 5446223 = 8169335) B8169335
theorem B2153081 : Blo 1433536 2153081 := bstep (se 2 (by rfl) ⟨807405, by rfl⟩ : syracuseStep 2153081 = 1614811) B1614811
theorem B3226283 : Blo 1433536 3226283 := bstep (se 1 (by rfl) ⟨2419712, by rfl⟩ : syracuseStep 3226283 = 4839425) B4839425
theorem B4905647 : Blo 1433536 4905647 := bstep (se 1 (by rfl) ⟨3679235, by rfl⟩ : syracuseStep 4905647 = 7358471) B7358471
theorem B2153135 : Blo 1433536 2153135 := bstep (se 1 (by rfl) ⟨1614851, by rfl⟩ : syracuseStep 2153135 = 3229703) B3229703
theorem B2153183 : Blo 1433536 2153183 := bstep (se 1 (by rfl) ⟨1614887, by rfl⟩ : syracuseStep 2153183 = 3229775) B3229775
theorem B6126455 : Blo 1433536 6126455 := bstep (se 1 (by rfl) ⟨4594841, by rfl⟩ : syracuseStep 6126455 = 9189683) B9189683
theorem B4086683 : Blo 1433536 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B2071451 : Blo 1433536 2071451 := bstep (se 1 (by rfl) ⟨1553588, by rfl⟩ : syracuseStep 2071451 = 3107177) B3107177
theorem B4365211 : Blo 1433536 4365211 := bstep (se 1 (by rfl) ⟨3273908, by rfl⟩ : syracuseStep 4365211 = 6547817) B6547817
theorem B6126607 : Blo 1433536 6126607 := bstep (se 1 (by rfl) ⟨4594955, by rfl⟩ : syracuseStep 6126607 = 9189911) B9189911
theorem B3226823 : Blo 1433536 3226823 := bstep (se 1 (by rfl) ⟨2420117, by rfl⟩ : syracuseStep 3226823 = 4840235) B4840235
theorem B4840667 : Blo 1433536 4840667 := bstep (se 1 (by rfl) ⟨3630500, by rfl⟩ : syracuseStep 4840667 = 7261001) B7261001
theorem B104627447 : Blo 1433536 104627447 := bstep (se 1 (by rfl) ⟨78470585, by rfl⟩ : syracuseStep 104627447 = 156941171) B156941171
theorem B46562597 : Blo 1433536 46562597 := bstep (se 4 (by rfl) ⟨4365243, by rfl⟩ : syracuseStep 46562597 = 8730487) B8730487
theorem B8174915 : Blo 1433536 8174915 := bstep (se 1 (by rfl) ⟨6131186, by rfl⟩ : syracuseStep 8174915 = 12262373) B12262373
theorem B55893341 : Blo 1433536 55893341 := bstep (se 3 (by rfl) ⟨10480001, by rfl⟩ : syracuseStep 55893341 = 20960003) B20960003
theorem B3227003 : Blo 1433536 3227003 := bstep (se 1 (by rfl) ⟨2420252, by rfl⟩ : syracuseStep 3227003 = 4840505) B4840505
theorem B5815739 : Blo 1433536 5815739 := bstep (se 1 (by rfl) ⟨4361804, by rfl⟩ : syracuseStep 5815739 = 8723609) B8723609
theorem B7757255 : Blo 1433536 7757255 := bstep (se 1 (by rfl) ⟨5817941, by rfl⟩ : syracuseStep 7757255 = 11635883) B11635883
theorem B3227129 : Blo 1433536 3227129 := bstep (se 2 (by rfl) ⟨1210173, by rfl⟩ : syracuseStep 3227129 = 2420347) B2420347
theorem B3227219 : Blo 1433536 3227219 := bstep (se 1 (by rfl) ⟨2420414, by rfl⟩ : syracuseStep 3227219 = 4840829) B4840829
theorem B1613407 : Blo 1433536 1613407 := bstep (se 1 (by rfl) ⟨1210055, by rfl⟩ : syracuseStep 1613407 = 2420111) B2420111
theorem B7257761 : Blo 1433536 7257761 := bstep (se 2 (by rfl) ⟨2721660, by rfl⟩ : syracuseStep 7257761 = 5443321) B5443321
theorem B3227399 : Blo 1433536 3227399 := bstep (se 1 (by rfl) ⟨2420549, by rfl⟩ : syracuseStep 3227399 = 4841099) B4841099
theorem B4087709 : Blo 1433536 4087709 := bstep (se 3 (by rfl) ⟨766445, by rfl⟩ : syracuseStep 4087709 = 1532891) B1532891
theorem B1433551 : Blo 1433536 1433551 := bstep (se 1 (by rfl) ⟨1075163, by rfl⟩ : syracuseStep 1433551 = 2150327) B2150327
theorem B1433575 : Blo 1433536 1433575 := bstep (se 1 (by rfl) ⟨1075181, by rfl⟩ : syracuseStep 1433575 = 2150363) B2150363
theorem B3227687 : Blo 1433536 3227687 := bstep (se 1 (by rfl) ⟨2420765, by rfl⟩ : syracuseStep 3227687 = 4841531) B4841531
theorem B3629195 : Blo 1433536 3629195 := bstep (se 1 (by rfl) ⟨2721896, by rfl⟩ : syracuseStep 3629195 = 5443793) B5443793
theorem B3227867 : Blo 1433536 3227867 := bstep (se 1 (by rfl) ⟨2420900, by rfl⟩ : syracuseStep 3227867 = 4841801) B4841801
theorem B1433831 : Blo 1433536 1433831 := bstep (se 1 (by rfl) ⟨1075373, by rfl⟩ : syracuseStep 1433831 = 2150747) B2150747
theorem B1614055 : Blo 1433536 1614055 := bstep (se 1 (by rfl) ⟨1210541, by rfl⟩ : syracuseStep 1614055 = 2421083) B2421083
theorem B20668769 : Blo 1433536 20668769 := bstep (se 2 (by rfl) ⟨7750788, by rfl⟩ : syracuseStep 20668769 = 15501577) B15501577
theorem B31023485 : Blo 1433536 31023485 := bstep (se 3 (by rfl) ⟨5816903, by rfl⟩ : syracuseStep 31023485 = 11633807) B11633807
theorem B1433983 : Blo 1433536 1433983 := bstep (se 1 (by rfl) ⟨1075487, by rfl⟩ : syracuseStep 1433983 = 2150975) B2150975
theorem B3629519 : Blo 1433536 3629519 := bstep (se 1 (by rfl) ⟨2722139, by rfl⟩ : syracuseStep 3629519 = 5444279) B5444279
theorem B1434063 : Blo 1433536 1434063 := bstep (se 1 (by rfl) ⟨1075547, by rfl⟩ : syracuseStep 1434063 = 2151095) B2151095
theorem B3228137 : Blo 1433536 3228137 := bstep (se 2 (by rfl) ⟨1210551, by rfl⟩ : syracuseStep 3228137 = 2421103) B2421103
theorem B1434215 : Blo 1433536 1434215 := bstep (se 1 (by rfl) ⟨1075661, by rfl⟩ : syracuseStep 1434215 = 2151323) B2151323
theorem B3228425 : Blo 1433536 3228425 := bstep (se 2 (by rfl) ⟨1210659, by rfl⟩ : syracuseStep 3228425 = 2421319) B2421319
theorem B4842287 : Blo 1433536 4842287 := bstep (se 1 (by rfl) ⟨3631715, by rfl⟩ : syracuseStep 4842287 = 7263431) B7263431
theorem B1434479 : Blo 1433536 1434479 := bstep (se 1 (by rfl) ⟨1075859, by rfl⟩ : syracuseStep 1434479 = 2151719) B2151719
theorem B1614703 : Blo 1433536 1614703 := bstep (se 1 (by rfl) ⟨1211027, by rfl⟩ : syracuseStep 1614703 = 2422055) B2422055
theorem B4842395 : Blo 1433536 4842395 := bstep (se 1 (by rfl) ⟨3631796, by rfl⟩ : syracuseStep 4842395 = 7263593) B7263593
theorem B3875741 : Blo 1433536 3875741 := bstep (se 3 (by rfl) ⟨726701, by rfl⟩ : syracuseStep 3875741 = 1453403) B1453403
theorem B1434535 : Blo 1433536 1434535 := bstep (se 1 (by rfl) ⟨1075901, by rfl⟩ : syracuseStep 1434535 = 2151803) B2151803
theorem B3630035 : Blo 1433536 3630035 := bstep (se 1 (by rfl) ⟨2722526, by rfl⟩ : syracuseStep 3630035 = 5445053) B5445053
theorem B1434619 : Blo 1433536 1434619 := bstep (se 1 (by rfl) ⟨1075964, by rfl⟩ : syracuseStep 1434619 = 2151929) B2151929
theorem B1434687 : Blo 1433536 1434687 := bstep (se 1 (by rfl) ⟨1076015, by rfl⟩ : syracuseStep 1434687 = 2152031) B2152031
theorem B22086755 : Blo 1433536 22086755 := bstep (se 1 (by rfl) ⟨16565066, by rfl⟩ : syracuseStep 22086755 = 33130133) B33130133
theorem B20686013 : Blo 1433536 20686013 := bstep (se 3 (by rfl) ⟨3878627, by rfl⟩ : syracuseStep 20686013 = 7757255) B7757255
theorem B35357897 : Blo 1433536 35357897 := bstep (se 2 (by rfl) ⟨13259211, by rfl⟩ : syracuseStep 35357897 = 26518423) B26518423
theorem B1434831 : Blo 1433536 1434831 := bstep (se 1 (by rfl) ⟨1076123, by rfl⟩ : syracuseStep 1434831 = 2152247) B2152247
theorem B10896605 : Blo 1433536 10896605 := bstep (se 3 (by rfl) ⟨2043113, by rfl⟩ : syracuseStep 10896605 = 4086227) B4086227
theorem B3229001 : Blo 1433536 3229001 := bstep (se 2 (by rfl) ⟨1210875, by rfl⟩ : syracuseStep 3229001 = 2421751) B2421751
theorem B8168809 : Blo 1433536 8168809 := bstep (se 2 (by rfl) ⟨3063303, by rfl⟩ : syracuseStep 8168809 = 6126607) B6126607
theorem B1435035 : Blo 1433536 1435035 := bstep (se 1 (by rfl) ⟨1076276, by rfl⟩ : syracuseStep 1435035 = 2152553) B2152553
theorem B5817815 : Blo 1433536 5817815 := bstep (se 1 (by rfl) ⟨4363361, by rfl⟩ : syracuseStep 5817815 = 8726723) B8726723
theorem B3630703 : Blo 1433536 3630703 := bstep (se 1 (by rfl) ⟨2723027, by rfl⟩ : syracuseStep 3630703 = 5446055) B5446055
theorem B1435247 : Blo 1433536 1435247 := bstep (se 1 (by rfl) ⟨1076435, by rfl⟩ : syracuseStep 1435247 = 2152871) B2152871
theorem B46532231 : Blo 1433536 46532231 := bstep (se 1 (by rfl) ⟨34899173, by rfl⟩ : syracuseStep 46532231 = 69798347) B69798347
theorem B1435303 : Blo 1433536 1435303 := bstep (se 1 (by rfl) ⟨1076477, by rfl⟩ : syracuseStep 1435303 = 2152955) B2152955
theorem B3630815 : Blo 1433536 3630815 := bstep (se 1 (by rfl) ⟨2723111, by rfl⟩ : syracuseStep 3630815 = 5446223) B5446223
theorem B1435387 : Blo 1433536 1435387 := bstep (se 1 (by rfl) ⟨1076540, by rfl⟩ : syracuseStep 1435387 = 2153081) B2153081
theorem B3270431 : Blo 1433536 3270431 := bstep (se 1 (by rfl) ⟨2452823, by rfl⟩ : syracuseStep 3270431 = 4905647) B4905647
theorem B1435423 : Blo 1433536 1435423 := bstep (se 1 (by rfl) ⟨1076567, by rfl⟩ : syracuseStep 1435423 = 2153135) B2153135
theorem B1435455 : Blo 1433536 1435455 := bstep (se 1 (by rfl) ⟨1076591, by rfl⟩ : syracuseStep 1435455 = 2153183) B2153183
theorem B4843529 : Blo 1433536 4843529 := bstep (se 2 (by rfl) ⟨1816323, by rfl⟩ : syracuseStep 4843529 = 3632647) B3632647
theorem B31041731 : Blo 1433536 31041731 := bstep (se 1 (by rfl) ⟨23281298, by rfl⟩ : syracuseStep 31041731 = 46562597) B46562597
theorem B5449943 : Blo 1433536 5449943 := bstep (se 1 (by rfl) ⟨4087457, by rfl⟩ : syracuseStep 5449943 = 8174915) B8174915
theorem B37259509 : Blo 1433536 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B3877159 : Blo 1433536 3877159 := bstep (se 1 (by rfl) ⟨2907869, by rfl⟩ : syracuseStep 3877159 = 5815739) B5815739
theorem B23267675 : Blo 1433536 23267675 := bstep (se 1 (by rfl) ⟨17450756, by rfl⟩ : syracuseStep 23267675 = 34901513) B34901513
theorem B5523869 : Blo 1433536 5523869 := bstep (se 3 (by rfl) ⟨1035725, by rfl⟩ : syracuseStep 5523869 = 2071451) B2071451
theorem B7358921 : Blo 1433536 7358921 := bstep (se 2 (by rfl) ⟨2759595, by rfl⟩ : syracuseStep 7358921 = 5519191) B5519191
theorem B16345637 : Blo 1433536 16345637 := bstep (se 4 (by rfl) ⟨1532403, by rfl⟩ : syracuseStep 16345637 = 3064807) B3064807
theorem B7563959 : Blo 1433536 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B4082663 : Blo 1433536 4082663 := bstep (se 1 (by rfl) ⟨3061997, by rfl⟩ : syracuseStep 4082663 = 6123995) B6123995
theorem B2419753 : Blo 1433536 2419753 := bstep (se 2 (by rfl) ⟨907407, by rfl⟩ : syracuseStep 2419753 = 1814815) B1814815
theorem B20679725 : Blo 1433536 20679725 := bstep (se 3 (by rfl) ⟨3877448, by rfl⟩ : syracuseStep 20679725 = 7754897) B7754897
theorem B10890287 : Blo 1433536 10890287 := bstep (se 1 (by rfl) ⟨8167715, by rfl⟩ : syracuseStep 10890287 = 16335431) B16335431
theorem B860826703 : Blo 1433536 860826703 := bstep (se 1 (by rfl) ⟨645620027, by rfl⟩ : syracuseStep 860826703 = 1291240055) B1291240055
theorem B53816399 : Blo 1433536 53816399 := bstep (se 1 (by rfl) ⟨40362299, by rfl⟩ : syracuseStep 53816399 = 80724599) B80724599
theorem B4910215 : Blo 1433536 4910215 := bstep (se 1 (by rfl) ⟨3682661, by rfl⟩ : syracuseStep 4910215 = 7365323) B7365323
theorem B2419895 : Blo 1433536 2419895 := bstep (se 1 (by rfl) ⟨1814921, by rfl⟩ : syracuseStep 2419895 = 3629843) B3629843
theorem B4844825 : Blo 1433536 4844825 := bstep (se 2 (by rfl) ⟨1816809, by rfl⟩ : syracuseStep 4844825 = 3633619) B3633619
theorem B4844879 : Blo 1433536 4844879 := bstep (se 1 (by rfl) ⟨3633659, by rfl⟩ : syracuseStep 4844879 = 7267319) B7267319
theorem B18181523 : Blo 1433536 18181523 := bstep (se 1 (by rfl) ⟨13636142, by rfl⟩ : syracuseStep 18181523 = 27272285) B27272285
theorem B2420219 : Blo 1433536 2420219 := bstep (se 1 (by rfl) ⟨1815164, by rfl⟩ : syracuseStep 2420219 = 3630329) B3630329
theorem B8719979 : Blo 1433536 8719979 := bstep (se 1 (by rfl) ⟨6539984, by rfl⟩ : syracuseStep 8719979 = 13079969) B13079969
theorem B93097673 : Blo 1433536 93097673 := bstep (se 2 (by rfl) ⟨34911627, by rfl⟩ : syracuseStep 93097673 = 69823255) B69823255
theorem B5820281 : Blo 1433536 5820281 := bstep (se 2 (by rfl) ⟨2182605, by rfl⟩ : syracuseStep 5820281 = 4365211) B4365211
theorem B1814395 : Blo 1433536 1814395 := bstep (se 1 (by rfl) ⟨1360796, by rfl⟩ : syracuseStep 1814395 = 2721593) B2721593
theorem B2420651 : Blo 1433536 2420651 := bstep (se 1 (by rfl) ⟨1815488, by rfl⟩ : syracuseStep 2420651 = 3630977) B3630977
theorem B9187451 : Blo 1433536 9187451 := bstep (se 1 (by rfl) ⟨6890588, by rfl⟩ : syracuseStep 9187451 = 13781177) B13781177
theorem B3633275 : Blo 1433536 3633275 := bstep (se 1 (by rfl) ⟨2724956, by rfl⟩ : syracuseStep 3633275 = 5449913) B5449913
theorem B2150687 : Blo 1433536 2150687 := bstep (se 1 (by rfl) ⟨1613015, by rfl⟩ : syracuseStep 2150687 = 3226031) B3226031
theorem B1937719 : Blo 1433536 1937719 := bstep (se 1 (by rfl) ⟨1453289, by rfl⟩ : syracuseStep 1937719 = 2906579) B2906579
theorem B2150711 : Blo 1433536 2150711 := bstep (se 1 (by rfl) ⟨1613033, by rfl⟩ : syracuseStep 2150711 = 3226067) B3226067
theorem B2150783 : Blo 1433536 2150783 := bstep (se 1 (by rfl) ⟨1613087, by rfl⟩ : syracuseStep 2150783 = 3226175) B3226175
theorem B2150855 : Blo 1433536 2150855 := bstep (se 1 (by rfl) ⟨1613141, by rfl⟩ : syracuseStep 2150855 = 3226283) B3226283
theorem B2421191 : Blo 1433536 2421191 := bstep (se 1 (by rfl) ⟨1815893, by rfl⟩ : syracuseStep 2421191 = 3631787) B3631787
theorem B4084303 : Blo 1433536 4084303 := bstep (se 1 (by rfl) ⟨3063227, by rfl⟩ : syracuseStep 4084303 = 6126455) B6126455
theorem B2724455 : Blo 1433536 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B52359857 : Blo 1433536 52359857 := bstep (se 2 (by rfl) ⟨19634946, by rfl⟩ : syracuseStep 52359857 = 39269893) B39269893
theorem B2151209 : Blo 1433536 2151209 := bstep (se 2 (by rfl) ⟨806703, by rfl⟩ : syracuseStep 2151209 = 1613407) B1613407
theorem B2151215 : Blo 1433536 2151215 := bstep (se 1 (by rfl) ⟨1613411, by rfl⟩ : syracuseStep 2151215 = 3226823) B3226823
theorem B69751631 : Blo 1433536 69751631 := bstep (se 1 (by rfl) ⟨52313723, by rfl⟩ : syracuseStep 69751631 = 104627447) B104627447
theorem B37262227 : Blo 1433536 37262227 := bstep (se 1 (by rfl) ⟨27946670, by rfl⟩ : syracuseStep 37262227 = 55893341) B55893341
theorem B2151335 : Blo 1433536 2151335 := bstep (se 1 (by rfl) ⟨1613501, by rfl⟩ : syracuseStep 2151335 = 3227003) B3227003
theorem B1815463 : Blo 1433536 1815463 := bstep (se 1 (by rfl) ⟨1361597, by rfl⟩ : syracuseStep 1815463 = 2723195) B2723195
theorem B2151419 : Blo 1433536 2151419 := bstep (se 1 (by rfl) ⟨1613564, by rfl⟩ : syracuseStep 2151419 = 3227129) B3227129
theorem B2151479 : Blo 1433536 2151479 := bstep (se 1 (by rfl) ⟨1613609, by rfl⟩ : syracuseStep 2151479 = 3227219) B3227219
theorem B4838507 : Blo 1433536 4838507 := bstep (se 1 (by rfl) ⟨3628880, by rfl⟩ : syracuseStep 4838507 = 7257761) B7257761
theorem B8172683 : Blo 1433536 8172683 := bstep (se 1 (by rfl) ⟨6129512, by rfl⟩ : syracuseStep 8172683 = 12259025) B12259025
theorem B2151599 : Blo 1433536 2151599 := bstep (se 1 (by rfl) ⟨1613699, by rfl⟩ : syracuseStep 2151599 = 3227399) B3227399
theorem B2421967 : Blo 1433536 2421967 := bstep (se 1 (by rfl) ⟨1816475, by rfl⟩ : syracuseStep 2421967 = 3632951) B3632951
theorem B2725139 : Blo 1433536 2725139 := bstep (se 1 (by rfl) ⟨2043854, by rfl⟩ : syracuseStep 2725139 = 4087709) B4087709
theorem B2152007 : Blo 1433536 2152007 := bstep (se 1 (by rfl) ⟨1614005, by rfl⟩ : syracuseStep 2152007 = 3228011) B3228011
theorem B2152103 : Blo 1433536 2152103 := bstep (se 1 (by rfl) ⟨1614077, by rfl⟩ : syracuseStep 2152103 = 3228155) B3228155
theorem B24516269 : Blo 1433536 24516269 := bstep (se 3 (by rfl) ⟨4596800, by rfl⟩ : syracuseStep 24516269 = 9193601) B9193601
theorem B1816283 : Blo 1433536 1816283 := bstep (se 1 (by rfl) ⟨1362212, by rfl⟩ : syracuseStep 1816283 = 2724425) B2724425
theorem B2152187 : Blo 1433536 2152187 := bstep (se 1 (by rfl) ⟨1614140, by rfl⟩ : syracuseStep 2152187 = 3228281) B3228281
theorem B4593419 : Blo 1433536 4593419 := bstep (se 1 (by rfl) ⟨3445064, by rfl⟩ : syracuseStep 4593419 = 6890129) B6890129
theorem B2152223 : Blo 1433536 2152223 := bstep (se 1 (by rfl) ⟨1614167, by rfl⟩ : syracuseStep 2152223 = 3228335) B3228335
theorem B19642175 : Blo 1433536 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B2152271 : Blo 1433536 2152271 := bstep (se 1 (by rfl) ⟨1614203, by rfl⟩ : syracuseStep 2152271 = 3228407) B3228407
theorem B10893203 : Blo 1433536 10893203 := bstep (se 1 (by rfl) ⟨8169902, by rfl⟩ : syracuseStep 10893203 = 16339805) B16339805
theorem B2152391 : Blo 1433536 2152391 := bstep (se 1 (by rfl) ⟨1614293, by rfl⟩ : syracuseStep 2152391 = 3228587) B3228587
theorem B3225563 : Blo 1433536 3225563 := bstep (se 1 (by rfl) ⟨2419172, by rfl⟩ : syracuseStep 3225563 = 4838345) B4838345
theorem B13973563 : Blo 1433536 13973563 := bstep (se 1 (by rfl) ⟨10480172, by rfl⟩ : syracuseStep 13973563 = 20960345) B20960345
theorem B6125651 : Blo 1433536 6125651 := bstep (se 1 (by rfl) ⟨4594238, by rfl⟩ : syracuseStep 6125651 = 9188477) B9188477
theorem B3061903 : Blo 1433536 3061903 := bstep (se 1 (by rfl) ⟨2296427, by rfl⟩ : syracuseStep 3061903 = 4592855) B4592855
theorem B3225743 : Blo 1433536 3225743 := bstep (se 1 (by rfl) ⟨2419307, by rfl⟩ : syracuseStep 3225743 = 4838615) B4838615
theorem B3225761 : Blo 1433536 3225761 := bstep (se 2 (by rfl) ⟨1209660, by rfl⟩ : syracuseStep 3225761 = 2419321) B2419321
theorem B10344647 : Blo 1433536 10344647 := bstep (se 1 (by rfl) ⟨7758485, by rfl⟩ : syracuseStep 10344647 = 15516971) B15516971
theorem B3225833 : Blo 1433536 3225833 := bstep (se 2 (by rfl) ⟨1209687, by rfl⟩ : syracuseStep 3225833 = 2419375) B2419375
theorem B18372851 : Blo 1433536 18372851 := bstep (se 1 (by rfl) ⟨13779638, by rfl⟩ : syracuseStep 18372851 = 27559277) B27559277
theorem B16341263 : Blo 1433536 16341263 := bstep (se 1 (by rfl) ⟨12255947, by rfl⟩ : syracuseStep 16341263 = 24511895) B24511895
theorem B2152745 : Blo 1433536 2152745 := bstep (se 2 (by rfl) ⟨807279, by rfl⟩ : syracuseStep 2152745 = 1614559) B1614559
theorem B2152751 : Blo 1433536 2152751 := bstep (se 1 (by rfl) ⟨1614563, by rfl⟩ : syracuseStep 2152751 = 3229127) B3229127
theorem B4839803 : Blo 1433536 4839803 := bstep (se 1 (by rfl) ⟨3629852, by rfl⟩ : syracuseStep 4839803 = 7259705) B7259705
theorem B2152991 : Blo 1433536 2152991 := bstep (se 1 (by rfl) ⟨1614743, by rfl⟩ : syracuseStep 2152991 = 3229487) B3229487
theorem B7264889 : Blo 1433536 7264889 := bstep (se 2 (by rfl) ⟨2724333, by rfl⟩ : syracuseStep 7264889 = 5448667) B5448667
theorem B4840073 : Blo 1433536 4840073 := bstep (se 2 (by rfl) ⟨1815027, by rfl⟩ : syracuseStep 4840073 = 3630055) B3630055
theorem B15506423 : Blo 1433536 15506423 := bstep (se 1 (by rfl) ⟨11629817, by rfl⟩ : syracuseStep 15506423 = 23259635) B23259635
theorem B4087037 : Blo 1433536 4087037 := bstep (se 3 (by rfl) ⟨766319, by rfl⟩ : syracuseStep 4087037 = 1532639) B1532639
theorem B12262751 : Blo 1433536 12262751 := bstep (se 1 (by rfl) ⟨9197063, by rfl⟩ : syracuseStep 12262751 = 18394127) B18394127
theorem B3227111 : Blo 1433536 3227111 := bstep (se 1 (by rfl) ⟨2420333, by rfl⟩ : syracuseStep 3227111 = 4840667) B4840667
theorem B4841207 : Blo 1433536 4841207 := bstep (se 1 (by rfl) ⟨3630905, by rfl⟩ : syracuseStep 4841207 = 7261811) B7261811
theorem B3628871 : Blo 1433536 3628871 := bstep (se 1 (by rfl) ⟨2721653, by rfl⟩ : syracuseStep 3628871 = 5443307) B5443307
theorem B1433567 : Blo 1433536 1433567 := bstep (se 1 (by rfl) ⟨1075175, by rfl⟩ : syracuseStep 1433567 = 2150351) B2150351
theorem B1433791 : Blo 1433536 1433791 := bstep (se 1 (by rfl) ⟨1075343, by rfl⟩ : syracuseStep 1433791 = 2150687) B2150687
theorem B1433807 : Blo 1433536 1433807 := bstep (se 1 (by rfl) ⟨1075355, by rfl⟩ : syracuseStep 1433807 = 2150711) B2150711
theorem B13779179 : Blo 1433536 13779179 := bstep (se 1 (by rfl) ⟨10334384, by rfl⟩ : syracuseStep 13779179 = 20668769) B20668769
theorem B1433855 : Blo 1433536 1433855 := bstep (se 1 (by rfl) ⟨1075391, by rfl⟩ : syracuseStep 1433855 = 2150783) B2150783
theorem B1433903 : Blo 1433536 1433903 := bstep (se 1 (by rfl) ⟨1075427, by rfl⟩ : syracuseStep 1433903 = 2150855) B2150855
theorem B1614127 : Blo 1433536 1614127 := bstep (se 1 (by rfl) ⟨1210595, by rfl⟩ : syracuseStep 1614127 = 2421191) B2421191
theorem B5169545 : Blo 1433536 5169545 := bstep (se 2 (by rfl) ⟨1938579, by rfl⟩ : syracuseStep 5169545 = 3877159) B3877159
theorem B34906571 : Blo 1433536 34906571 := bstep (se 1 (by rfl) ⟨26179928, by rfl⟩ : syracuseStep 34906571 = 52359857) B52359857
theorem B1434139 : Blo 1433536 1434139 := bstep (se 1 (by rfl) ⟨1075604, by rfl⟩ : syracuseStep 1434139 = 2151209) B2151209
theorem B1434143 : Blo 1433536 1434143 := bstep (se 1 (by rfl) ⟨1075607, by rfl⟩ : syracuseStep 1434143 = 2151215) B2151215
theorem B3228191 : Blo 1433536 3228191 := bstep (se 1 (by rfl) ⟨2421143, by rfl⟩ : syracuseStep 3228191 = 4842287) B4842287
theorem B3228263 : Blo 1433536 3228263 := bstep (se 1 (by rfl) ⟨2421197, by rfl⟩ : syracuseStep 3228263 = 4842395) B4842395
theorem B1434223 : Blo 1433536 1434223 := bstep (se 1 (by rfl) ⟨1075667, by rfl⟩ : syracuseStep 1434223 = 2151335) B2151335
theorem B1434279 : Blo 1433536 1434279 := bstep (se 1 (by rfl) ⟨1075709, by rfl⟩ : syracuseStep 1434279 = 2151419) B2151419
theorem B1434319 : Blo 1433536 1434319 := bstep (se 1 (by rfl) ⟨1075739, by rfl⟩ : syracuseStep 1434319 = 2151479) B2151479
theorem B5448455 : Blo 1433536 5448455 := bstep (se 1 (by rfl) ⟨4086341, by rfl⟩ : syracuseStep 5448455 = 8172683) B8172683
theorem B1434399 : Blo 1433536 1434399 := bstep (se 1 (by rfl) ⟨1075799, by rfl⟩ : syracuseStep 1434399 = 2151599) B2151599
theorem B1434671 : Blo 1433536 1434671 := bstep (se 1 (by rfl) ⟨1076003, by rfl⟩ : syracuseStep 1434671 = 2152007) B2152007
theorem B1434735 : Blo 1433536 1434735 := bstep (se 1 (by rfl) ⟨1076051, by rfl⟩ : syracuseStep 1434735 = 2152103) B2152103
theorem B16344179 : Blo 1433536 16344179 := bstep (se 1 (by rfl) ⟨12258134, by rfl⟩ : syracuseStep 16344179 = 24516269) B24516269
theorem B1434791 : Blo 1433536 1434791 := bstep (se 1 (by rfl) ⟨1076093, by rfl⟩ : syracuseStep 1434791 = 2152187) B2152187
theorem B2180287 : Blo 1433536 2180287 := bstep (se 1 (by rfl) ⟨1635215, by rfl⟩ : syracuseStep 2180287 = 3270431) B3270431
theorem B1434815 : Blo 1433536 1434815 := bstep (se 1 (by rfl) ⟨1076111, by rfl⟩ : syracuseStep 1434815 = 2152223) B2152223
theorem B1434847 : Blo 1433536 1434847 := bstep (se 1 (by rfl) ⟨1076135, by rfl⟩ : syracuseStep 1434847 = 2152271) B2152271
theorem B1434927 : Blo 1433536 1434927 := bstep (se 1 (by rfl) ⟨1076195, by rfl⟩ : syracuseStep 1434927 = 2152391) B2152391
theorem B3229019 : Blo 1433536 3229019 := bstep (se 1 (by rfl) ⟨2421764, by rfl⟩ : syracuseStep 3229019 = 4843529) B4843529
theorem B20694487 : Blo 1433536 20694487 := bstep (se 1 (by rfl) ⟨15520865, by rfl⟩ : syracuseStep 20694487 = 31041731) B31041731
theorem B12248567 : Blo 1433536 12248567 := bstep (se 1 (by rfl) ⟨9186425, by rfl⟩ : syracuseStep 12248567 = 18372851) B18372851
theorem B6546953 : Blo 1433536 6546953 := bstep (se 2 (by rfl) ⟨2455107, by rfl⟩ : syracuseStep 6546953 = 4910215) B4910215
theorem B1435163 : Blo 1433536 1435163 := bstep (se 1 (by rfl) ⟨1076372, by rfl⟩ : syracuseStep 1435163 = 2152745) B2152745
theorem B1435167 : Blo 1433536 1435167 := bstep (se 1 (by rfl) ⟨1076375, by rfl⟩ : syracuseStep 1435167 = 2152751) B2152751
theorem B3229289 : Blo 1433536 3229289 := bstep (se 2 (by rfl) ⟨1210983, by rfl⟩ : syracuseStep 3229289 = 2421967) B2421967
theorem B1435327 : Blo 1433536 1435327 := bstep (se 1 (by rfl) ⟨1076495, by rfl⟩ : syracuseStep 1435327 = 2152991) B2152991
theorem B10897091 : Blo 1433536 10897091 := bstep (se 1 (by rfl) ⟨8172818, by rfl⟩ : syracuseStep 10897091 = 16345637) B16345637
theorem B4843259 : Blo 1433536 4843259 := bstep (se 1 (by rfl) ⟨3632444, by rfl⟩ : syracuseStep 4843259 = 7264889) B7264889
theorem B4843421 : Blo 1433536 4843421 := bstep (se 3 (by rfl) ⟨908141, by rfl⟩ : syracuseStep 4843421 = 1816283) B1816283
theorem B2721775 : Blo 1433536 2721775 := bstep (se 1 (by rfl) ⟨2041331, by rfl⟩ : syracuseStep 2721775 = 4082663) B4082663
theorem B7260191 : Blo 1433536 7260191 := bstep (se 1 (by rfl) ⟨5445143, by rfl⟩ : syracuseStep 7260191 = 10890287) B10890287
theorem B3229883 : Blo 1433536 3229883 := bstep (se 1 (by rfl) ⟨2422412, by rfl⟩ : syracuseStep 3229883 = 4844825) B4844825
theorem B3229919 : Blo 1433536 3229919 := bstep (se 1 (by rfl) ⟨2422439, by rfl⟩ : syracuseStep 3229919 = 4844879) B4844879
theorem B62065115 : Blo 1433536 62065115 := bstep (se 1 (by rfl) ⟨46548836, by rfl⟩ : syracuseStep 62065115 = 93097673) B93097673
theorem B2419193 : Blo 1433536 2419193 := bstep (se 2 (by rfl) ⟨907197, by rfl⟩ : syracuseStep 2419193 = 1814395) B1814395
theorem B2419247 : Blo 1433536 2419247 := bstep (se 1 (by rfl) ⟨1814435, by rfl⟩ : syracuseStep 2419247 = 3628871) B3628871
theorem B2419463 : Blo 1433536 2419463 := bstep (se 1 (by rfl) ⟨1814597, by rfl⟩ : syracuseStep 2419463 = 3629195) B3629195
theorem B4082537 : Blo 1433536 4082537 := bstep (se 2 (by rfl) ⟨1530951, by rfl⟩ : syracuseStep 4082537 = 3061903) B3061903
theorem B2419679 : Blo 1433536 2419679 := bstep (se 1 (by rfl) ⟨1814759, by rfl⟩ : syracuseStep 2419679 = 3629519) B3629519
theorem B74525669 : Blo 1433536 74525669 := bstep (se 4 (by rfl) ⟨6986781, by rfl⟩ : syracuseStep 74525669 = 13973563) B13973563
theorem B49679345 : Blo 1433536 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B2583625 : Blo 1433536 2583625 := bstep (se 2 (by rfl) ⟨968859, by rfl⟩ : syracuseStep 2583625 = 1937719) B1937719
theorem B2583827 : Blo 1433536 2583827 := bstep (se 1 (by rfl) ⟨1937870, by rfl⟩ : syracuseStep 2583827 = 3875741) B3875741
theorem B2420023 : Blo 1433536 2420023 := bstep (se 1 (by rfl) ⟨1815017, by rfl⟩ : syracuseStep 2420023 = 3630035) B3630035
theorem B14724503 : Blo 1433536 14724503 := bstep (se 1 (by rfl) ⟨11043377, by rfl⟩ : syracuseStep 14724503 = 22086755) B22086755
theorem B13790675 : Blo 1433536 13790675 := bstep (se 1 (by rfl) ⟨10343006, by rfl⟩ : syracuseStep 13790675 = 20686013) B20686013
theorem B23571931 : Blo 1433536 23571931 := bstep (se 1 (by rfl) ⟨17678948, by rfl⟩ : syracuseStep 23571931 = 35357897) B35357897
theorem B3878543 : Blo 1433536 3878543 := bstep (se 1 (by rfl) ⟨2908907, by rfl⟩ : syracuseStep 3878543 = 5817815) B5817815
theorem B2420543 : Blo 1433536 2420543 := bstep (se 1 (by rfl) ⟨1815407, by rfl⟩ : syracuseStep 2420543 = 3630815) B3630815
theorem B13094783 : Blo 1433536 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B2420617 : Blo 1433536 2420617 := bstep (se 2 (by rfl) ⟨907731, by rfl⟩ : syracuseStep 2420617 = 1815463) B1815463
theorem B7262135 : Blo 1433536 7262135 := bstep (se 1 (by rfl) ⟨5446601, by rfl⟩ : syracuseStep 7262135 = 10893203) B10893203
theorem B2150375 : Blo 1433536 2150375 := bstep (se 1 (by rfl) ⟨1612781, by rfl⟩ : syracuseStep 2150375 = 3225563) B3225563
theorem B4083767 : Blo 1433536 4083767 := bstep (se 1 (by rfl) ⟨3062825, by rfl⟩ : syracuseStep 4083767 = 6125651) B6125651
theorem B2150495 : Blo 1433536 2150495 := bstep (se 1 (by rfl) ⟨1612871, by rfl⟩ : syracuseStep 2150495 = 3225743) B3225743
theorem B1147768937 : Blo 1433536 1147768937 := bstep (se 2 (by rfl) ⟨430413351, by rfl⟩ : syracuseStep 1147768937 = 860826703) B860826703
theorem B2150507 : Blo 1433536 2150507 := bstep (se 1 (by rfl) ⟨1612880, by rfl⟩ : syracuseStep 2150507 = 3225761) B3225761
theorem B3633295 : Blo 1433536 3633295 := bstep (se 1 (by rfl) ⟨2724971, by rfl⟩ : syracuseStep 3633295 = 5449943) B5449943
theorem B2150555 : Blo 1433536 2150555 := bstep (se 1 (by rfl) ⟨1612916, by rfl⟩ : syracuseStep 2150555 = 3225833) B3225833
theorem B15511783 : Blo 1433536 15511783 := bstep (se 1 (by rfl) ⟨11633837, by rfl⟩ : syracuseStep 15511783 = 23267675) B23267675
theorem B3682579 : Blo 1433536 3682579 := bstep (se 1 (by rfl) ⟨2761934, by rfl⟩ : syracuseStep 3682579 = 5523869) B5523869
theorem B23253277 : Blo 1433536 23253277 := bstep (se 3 (by rfl) ⟨4359989, by rfl⟩ : syracuseStep 23253277 = 8719979) B8719979
theorem B5042639 : Blo 1433536 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B10891745 : Blo 1433536 10891745 := bstep (se 2 (by rfl) ⟨4084404, by rfl⟩ : syracuseStep 10891745 = 8168809) B8168809
theorem B35877599 : Blo 1433536 35877599 := bstep (se 1 (by rfl) ⟨26908199, by rfl⟩ : syracuseStep 35877599 = 53816399) B53816399
theorem B2724691 : Blo 1433536 2724691 := bstep (se 1 (by rfl) ⟨2043518, by rfl⟩ : syracuseStep 2724691 = 4087037) B4087037
theorem B186004349 : Blo 1433536 186004349 := bstep (se 3 (by rfl) ⟨34875815, by rfl⟩ : syracuseStep 186004349 = 69751631) B69751631
theorem B12121015 : Blo 1433536 12121015 := bstep (se 1 (by rfl) ⟨9090761, by rfl⟩ : syracuseStep 12121015 = 18181523) B18181523
theorem B2151407 : Blo 1433536 2151407 := bstep (se 1 (by rfl) ⟨1613555, by rfl⟩ : syracuseStep 2151407 = 3227111) B3227111
theorem B3880187 : Blo 1433536 3880187 := bstep (se 1 (by rfl) ⟨2910140, by rfl⟩ : syracuseStep 3880187 = 5820281) B5820281
theorem B2151791 : Blo 1433536 2151791 := bstep (se 1 (by rfl) ⟨1613843, by rfl⟩ : syracuseStep 2151791 = 3227687) B3227687
theorem B6124967 : Blo 1433536 6124967 := bstep (se 1 (by rfl) ⟨4593725, by rfl⟩ : syracuseStep 6124967 = 9187451) B9187451
theorem B2422183 : Blo 1433536 2422183 := bstep (se 1 (by rfl) ⟨1816637, by rfl⟩ : syracuseStep 2422183 = 3633275) B3633275
theorem B2151911 : Blo 1433536 2151911 := bstep (se 1 (by rfl) ⟨1613933, by rfl⟩ : syracuseStep 2151911 = 3227867) B3227867
theorem B20682323 : Blo 1433536 20682323 := bstep (se 1 (by rfl) ⟨15511742, by rfl⟩ : syracuseStep 20682323 = 31023485) B31023485
theorem B2152073 : Blo 1433536 2152073 := bstep (se 2 (by rfl) ⟨807027, by rfl⟩ : syracuseStep 2152073 = 1614055) B1614055
theorem B2152091 : Blo 1433536 2152091 := bstep (se 1 (by rfl) ⟨1614068, by rfl⟩ : syracuseStep 2152091 = 3228137) B3228137
theorem B2152283 : Blo 1433536 2152283 := bstep (se 1 (by rfl) ⟨1614212, by rfl⟩ : syracuseStep 2152283 = 3228425) B3228425
theorem B3225671 : Blo 1433536 3225671 := bstep (se 1 (by rfl) ⟨2419253, by rfl⟩ : syracuseStep 3225671 = 4838507) B4838507
theorem B5445737 : Blo 1433536 5445737 := bstep (se 2 (by rfl) ⟨2042151, by rfl⟩ : syracuseStep 5445737 = 4084303) B4084303
theorem B7264403 : Blo 1433536 7264403 := bstep (se 1 (by rfl) ⟨5448302, by rfl⟩ : syracuseStep 7264403 = 10896605) B10896605
theorem B1816759 : Blo 1433536 1816759 := bstep (se 1 (by rfl) ⟨1362569, by rfl⟩ : syracuseStep 1816759 = 2725139) B2725139
theorem B2152667 : Blo 1433536 2152667 := bstep (se 1 (by rfl) ⟨1614500, by rfl⟩ : syracuseStep 2152667 = 3229001) B3229001
theorem B31021487 : Blo 1433536 31021487 := bstep (se 1 (by rfl) ⟨23266115, by rfl⟩ : syracuseStep 31021487 = 46532231) B46532231
theorem B2152937 : Blo 1433536 2152937 := bstep (se 2 (by rfl) ⟨807351, by rfl⟩ : syracuseStep 2152937 = 1614703) B1614703
theorem B3062279 : Blo 1433536 3062279 := bstep (se 1 (by rfl) ⟨2296709, by rfl⟩ : syracuseStep 3062279 = 4593419) B4593419
theorem B49682969 : Blo 1433536 49682969 := bstep (se 2 (by rfl) ⟨18631113, by rfl⟩ : syracuseStep 49682969 = 37262227) B37262227
theorem B3226337 : Blo 1433536 3226337 := bstep (se 2 (by rfl) ⟨1209876, by rfl⟩ : syracuseStep 3226337 = 2419753) B2419753
theorem B6896431 : Blo 1433536 6896431 := bstep (se 1 (by rfl) ⟨5172323, by rfl⟩ : syracuseStep 6896431 = 10344647) B10344647
theorem B10894175 : Blo 1433536 10894175 := bstep (se 1 (by rfl) ⟨8170631, by rfl⟩ : syracuseStep 10894175 = 16341263) B16341263
theorem B3226535 : Blo 1433536 3226535 := bstep (se 1 (by rfl) ⟨2419901, by rfl⟩ : syracuseStep 3226535 = 4839803) B4839803
theorem B7265213 : Blo 1433536 7265213 := bstep (se 3 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 7265213 = 2724455) B2724455
theorem B4905947 : Blo 1433536 4905947 := bstep (se 1 (by rfl) ⟨3679460, by rfl⟩ : syracuseStep 4905947 = 7358921) B7358921
theorem B3226715 : Blo 1433536 3226715 := bstep (se 1 (by rfl) ⟨2420036, by rfl⟩ : syracuseStep 3226715 = 4840073) B4840073
theorem B10337615 : Blo 1433536 10337615 := bstep (se 1 (by rfl) ⟨7753211, by rfl⟩ : syracuseStep 10337615 = 15506423) B15506423
theorem B13786483 : Blo 1433536 13786483 := bstep (se 1 (by rfl) ⟨10339862, by rfl⟩ : syracuseStep 13786483 = 20679725) B20679725
theorem B1613263 : Blo 1433536 1613263 := bstep (se 1 (by rfl) ⟨1209947, by rfl⟩ : syracuseStep 1613263 = 2419895) B2419895
theorem B4840937 : Blo 1433536 4840937 := bstep (se 2 (by rfl) ⟨1815351, by rfl⟩ : syracuseStep 4840937 = 3630703) B3630703
theorem B8175167 : Blo 1433536 8175167 := bstep (se 1 (by rfl) ⟨6131375, by rfl⟩ : syracuseStep 8175167 = 12262751) B12262751
theorem B1613479 : Blo 1433536 1613479 := bstep (se 1 (by rfl) ⟨1210109, by rfl⟩ : syracuseStep 1613479 = 2420219) B2420219
theorem B3227471 : Blo 1433536 3227471 := bstep (se 1 (by rfl) ⟨2420603, by rfl⟩ : syracuseStep 3227471 = 4841207) B4841207
theorem B1613767 : Blo 1433536 1613767 := bstep (se 1 (by rfl) ⟨1210325, by rfl⟩ : syracuseStep 1613767 = 2420651) B2420651
theorem B1433663 : Blo 1433536 1433663 := bstep (se 1 (by rfl) ⟨1075247, by rfl⟩ : syracuseStep 1433663 = 2150495) B2150495
theorem B1433671 : Blo 1433536 1433671 := bstep (se 1 (by rfl) ⟨1075253, by rfl⟩ : syracuseStep 1433671 = 2150507) B2150507
theorem B1433703 : Blo 1433536 1433703 := bstep (se 1 (by rfl) ⟨1075277, by rfl⟩ : syracuseStep 1433703 = 2150555) B2150555
theorem B124002899 : Blo 1433536 124002899 := bstep (se 1 (by rfl) ⟨93002174, by rfl⟩ : syracuseStep 124002899 = 186004349) B186004349
theorem B1434271 : Blo 1433536 1434271 := bstep (se 1 (by rfl) ⟨1075703, by rfl⟩ : syracuseStep 1434271 = 2151407) B2151407
theorem B10896119 : Blo 1433536 10896119 := bstep (se 1 (by rfl) ⟨8172089, by rfl⟩ : syracuseStep 10896119 = 16344179) B16344179
theorem B1434527 : Blo 1433536 1434527 := bstep (se 1 (by rfl) ⟨1075895, by rfl⟩ : syracuseStep 1434527 = 2151791) B2151791
theorem B1434607 : Blo 1433536 1434607 := bstep (se 1 (by rfl) ⟨1075955, by rfl⟩ : syracuseStep 1434607 = 2151911) B2151911
theorem B13788215 : Blo 1433536 13788215 := bstep (se 1 (by rfl) ⟨10341161, by rfl⟩ : syracuseStep 13788215 = 20682323) B20682323
theorem B1434715 : Blo 1433536 1434715 := bstep (se 1 (by rfl) ⟨1076036, by rfl⟩ : syracuseStep 1434715 = 2152073) B2152073
theorem B1434727 : Blo 1433536 1434727 := bstep (se 1 (by rfl) ⟨1076045, by rfl⟩ : syracuseStep 1434727 = 2152091) B2152091
theorem B3228839 : Blo 1433536 3228839 := bstep (se 1 (by rfl) ⟨2421629, by rfl⟩ : syracuseStep 3228839 = 4843259) B4843259
theorem B1434855 : Blo 1433536 1434855 := bstep (se 1 (by rfl) ⟨1076141, by rfl⟩ : syracuseStep 1434855 = 2152283) B2152283
theorem B3228947 : Blo 1433536 3228947 := bstep (se 1 (by rfl) ⟨2421710, by rfl⟩ : syracuseStep 3228947 = 4843421) B4843421
theorem B17458541 : Blo 1433536 17458541 := bstep (se 3 (by rfl) ⟨3273476, by rfl⟩ : syracuseStep 17458541 = 6546953) B6546953
theorem B3630491 : Blo 1433536 3630491 := bstep (se 1 (by rfl) ⟨2722868, by rfl⟩ : syracuseStep 3630491 = 5445737) B5445737
theorem B4842935 : Blo 1433536 4842935 := bstep (se 1 (by rfl) ⟨3632201, by rfl⟩ : syracuseStep 4842935 = 7264403) B7264403
theorem B1435111 : Blo 1433536 1435111 := bstep (se 1 (by rfl) ⟨1076333, by rfl⟩ : syracuseStep 1435111 = 2152667) B2152667
theorem B1435291 : Blo 1433536 1435291 := bstep (se 1 (by rfl) ⟨1076468, by rfl⟩ : syracuseStep 1435291 = 2152937) B2152937
theorem B2041519 : Blo 1433536 2041519 := bstep (se 1 (by rfl) ⟨1531139, by rfl⟩ : syracuseStep 2041519 = 3062279) B3062279
theorem B33121979 : Blo 1433536 33121979 := bstep (se 1 (by rfl) ⟨24841484, by rfl⟩ : syracuseStep 33121979 = 49682969) B49682969
theorem B3229577 : Blo 1433536 3229577 := bstep (se 2 (by rfl) ⟨1211091, by rfl⟩ : syracuseStep 3229577 = 2422183) B2422183
theorem B2721691 : Blo 1433536 2721691 := bstep (se 1 (by rfl) ⟨2041268, by rfl⟩ : syracuseStep 2721691 = 4082537) B4082537
theorem B27592649 : Blo 1433536 27592649 := bstep (se 2 (by rfl) ⟨10347243, by rfl⟩ : syracuseStep 27592649 = 20694487) B20694487
theorem B4843475 : Blo 1433536 4843475 := bstep (se 1 (by rfl) ⟨3632606, by rfl⟩ : syracuseStep 4843475 = 7265213) B7265213
theorem B3270631 : Blo 1433536 3270631 := bstep (se 1 (by rfl) ⟨2452973, by rfl⟩ : syracuseStep 3270631 = 4905947) B4905947
theorem B1722551 : Blo 1433536 1722551 := bstep (se 1 (by rfl) ⟨1291913, by rfl⟩ : syracuseStep 1722551 = 2583827) B2583827
theorem B6891743 : Blo 1433536 6891743 := bstep (se 1 (by rfl) ⟨5168807, by rfl⟩ : syracuseStep 6891743 = 10337615) B10337615
theorem B9816335 : Blo 1433536 9816335 := bstep (se 1 (by rfl) ⟨7362251, by rfl⟩ : syracuseStep 9816335 = 14724503) B14724503
theorem B9193783 : Blo 1433536 9193783 := bstep (se 1 (by rfl) ⟨6895337, by rfl⟩ : syracuseStep 9193783 = 13790675) B13790675
theorem B5450111 : Blo 1433536 5450111 := bstep (se 1 (by rfl) ⟨4087583, by rfl⟩ : syracuseStep 5450111 = 8175167) B8175167
theorem B2722511 : Blo 1433536 2722511 := bstep (se 1 (by rfl) ⟨2041883, by rfl⟩ : syracuseStep 2722511 = 4083767) B4083767
theorem B9186119 : Blo 1433536 9186119 := bstep (se 1 (by rfl) ⟨6889589, by rfl⟩ : syracuseStep 9186119 = 13779179) B13779179
theorem B4844393 : Blo 1433536 4844393 := bstep (se 2 (by rfl) ⟨1816647, by rfl⟩ : syracuseStep 4844393 = 3633295) B3633295
theorem B7261163 : Blo 1433536 7261163 := bstep (se 1 (by rfl) ⟨5445872, by rfl⟩ : syracuseStep 7261163 = 10891745) B10891745
theorem B4910105 : Blo 1433536 4910105 := bstep (se 2 (by rfl) ⟨1841289, by rfl⟩ : syracuseStep 4910105 = 3682579) B3682579
theorem B3632303 : Blo 1433536 3632303 := bstep (se 1 (by rfl) ⟨2724227, by rfl⟩ : syracuseStep 3632303 = 5448455) B5448455
theorem B4083311 : Blo 1433536 4083311 := bstep (se 1 (by rfl) ⟨3062483, by rfl⟩ : syracuseStep 4083311 = 6124967) B6124967
theorem B11628197 : Blo 1433536 11628197 := bstep (se 4 (by rfl) ⟨1090143, by rfl⟩ : syracuseStep 11628197 = 2180287) B2180287
theorem B3632921 : Blo 1433536 3632921 := bstep (se 2 (by rfl) ⟨1362345, by rfl⟩ : syracuseStep 3632921 = 2724691) B2724691
theorem B13447037 : Blo 1433536 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B2150447 : Blo 1433536 2150447 := bstep (se 1 (by rfl) ⟨1612835, by rfl⟩ : syracuseStep 2150447 = 3225671) B3225671
theorem B3444833 : Blo 1433536 3444833 := bstep (se 2 (by rfl) ⟨1291812, by rfl⟩ : syracuseStep 3444833 = 2583625) B2583625
theorem B20680991 : Blo 1433536 20680991 := bstep (se 1 (by rfl) ⟨15510743, by rfl⟩ : syracuseStep 20680991 = 31021487) B31021487
theorem B2150891 : Blo 1433536 2150891 := bstep (se 1 (by rfl) ⟨1613168, by rfl⟩ : syracuseStep 2150891 = 3226337) B3226337
theorem B7262783 : Blo 1433536 7262783 := bstep (se 1 (by rfl) ⟨5447087, by rfl⟩ : syracuseStep 7262783 = 10894175) B10894175
theorem B2151017 : Blo 1433536 2151017 := bstep (se 2 (by rfl) ⟨806631, by rfl⟩ : syracuseStep 2151017 = 1613263) B1613263
theorem B2151023 : Blo 1433536 2151023 := bstep (se 1 (by rfl) ⟨1613267, by rfl⟩ : syracuseStep 2151023 = 3226535) B3226535
theorem B31429241 : Blo 1433536 31429241 := bstep (se 2 (by rfl) ⟨11785965, by rfl⟩ : syracuseStep 31429241 = 23571931) B23571931
theorem B2151143 : Blo 1433536 2151143 := bstep (se 1 (by rfl) ⟨1613357, by rfl⟩ : syracuseStep 2151143 = 3226715) B3226715
theorem B2151305 : Blo 1433536 2151305 := bstep (se 2 (by rfl) ⟨806739, by rfl⟩ : syracuseStep 2151305 = 1613479) B1613479
theorem B2585695 : Blo 1433536 2585695 := bstep (se 1 (by rfl) ⟨1939271, by rfl⟩ : syracuseStep 2585695 = 3878543) B3878543
theorem B2151647 : Blo 1433536 2151647 := bstep (se 1 (by rfl) ⟨1613735, by rfl⟩ : syracuseStep 2151647 = 3227471) B3227471
theorem B8729855 : Blo 1433536 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B2151689 : Blo 1433536 2151689 := bstep (se 2 (by rfl) ⟨806883, by rfl⟩ : syracuseStep 2151689 = 1613767) B1613767
theorem B765179291 : Blo 1433536 765179291 := bstep (se 1 (by rfl) ⟨573884468, by rfl⟩ : syracuseStep 765179291 = 1147768937) B1147768937
theorem B2422345 : Blo 1433536 2422345 := bstep (se 2 (by rfl) ⟨908379, by rfl⟩ : syracuseStep 2422345 = 1816759) B1816759
theorem B3446363 : Blo 1433536 3446363 := bstep (se 1 (by rfl) ⟨2584772, by rfl⟩ : syracuseStep 3446363 = 5169545) B5169545
theorem B23271047 : Blo 1433536 23271047 := bstep (se 1 (by rfl) ⟨17453285, by rfl⟩ : syracuseStep 23271047 = 34906571) B34906571
theorem B20682377 : Blo 1433536 20682377 := bstep (se 2 (by rfl) ⟨7755891, by rfl⟩ : syracuseStep 20682377 = 15511783) B15511783
theorem B2152127 : Blo 1433536 2152127 := bstep (se 1 (by rfl) ⟨1614095, by rfl⟩ : syracuseStep 2152127 = 3228191) B3228191
theorem B31004369 : Blo 1433536 31004369 := bstep (se 2 (by rfl) ⟨11626638, by rfl⟩ : syracuseStep 31004369 = 23253277) B23253277
theorem B2152169 : Blo 1433536 2152169 := bstep (se 2 (by rfl) ⟨807063, by rfl⟩ : syracuseStep 2152169 = 1614127) B1614127
theorem B2152175 : Blo 1433536 2152175 := bstep (se 1 (by rfl) ⟨1614131, by rfl⟩ : syracuseStep 2152175 = 3228263) B3228263
theorem B23918399 : Blo 1433536 23918399 := bstep (se 1 (by rfl) ⟨17938799, by rfl⟩ : syracuseStep 23918399 = 35877599) B35877599
theorem B2586791 : Blo 1433536 2586791 := bstep (se 1 (by rfl) ⟨1940093, by rfl⟩ : syracuseStep 2586791 = 3880187) B3880187
theorem B2152679 : Blo 1433536 2152679 := bstep (se 1 (by rfl) ⟨1614509, by rfl⟩ : syracuseStep 2152679 = 3229019) B3229019
theorem B8165711 : Blo 1433536 8165711 := bstep (se 1 (by rfl) ⟨6124283, by rfl⟩ : syracuseStep 8165711 = 12248567) B12248567
theorem B2152859 : Blo 1433536 2152859 := bstep (se 1 (by rfl) ⟨1614644, by rfl⟩ : syracuseStep 2152859 = 3229289) B3229289
theorem B7264727 : Blo 1433536 7264727 := bstep (se 1 (by rfl) ⟨5448545, by rfl⟩ : syracuseStep 7264727 = 10897091) B10897091
theorem B16161353 : Blo 1433536 16161353 := bstep (se 2 (by rfl) ⟨6060507, by rfl⟩ : syracuseStep 16161353 = 12121015) B12121015
theorem B4840127 : Blo 1433536 4840127 := bstep (se 1 (by rfl) ⟨3630095, by rfl⟩ : syracuseStep 4840127 = 7260191) B7260191
theorem B2153255 : Blo 1433536 2153255 := bstep (se 1 (by rfl) ⟨1614941, by rfl⟩ : syracuseStep 2153255 = 3229883) B3229883
theorem B2153279 : Blo 1433536 2153279 := bstep (se 1 (by rfl) ⟨1614959, by rfl⟩ : syracuseStep 2153279 = 3229919) B3229919
theorem B36780965 : Blo 1433536 36780965 := bstep (se 4 (by rfl) ⟨3448215, by rfl⟩ : syracuseStep 36780965 = 6896431) B6896431
theorem B41376743 : Blo 1433536 41376743 := bstep (se 1 (by rfl) ⟨31032557, by rfl⟩ : syracuseStep 41376743 = 62065115) B62065115
theorem B1612795 : Blo 1433536 1612795 := bstep (se 1 (by rfl) ⟨1209596, by rfl⟩ : syracuseStep 1612795 = 2419193) B2419193
theorem B1612831 : Blo 1433536 1612831 := bstep (se 1 (by rfl) ⟨1209623, by rfl⟩ : syracuseStep 1612831 = 2419247) B2419247
theorem B3226697 : Blo 1433536 3226697 := bstep (se 2 (by rfl) ⟨1210011, by rfl⟩ : syracuseStep 3226697 = 2420023) B2420023
theorem B18381977 : Blo 1433536 18381977 := bstep (se 2 (by rfl) ⟨6893241, by rfl⟩ : syracuseStep 18381977 = 13786483) B13786483
theorem B1612975 : Blo 1433536 1612975 := bstep (se 1 (by rfl) ⟨1209731, by rfl⟩ : syracuseStep 1612975 = 2419463) B2419463
theorem B1613119 : Blo 1433536 1613119 := bstep (se 1 (by rfl) ⟨1209839, by rfl⟩ : syracuseStep 1613119 = 2419679) B2419679
theorem B49683779 : Blo 1433536 49683779 := bstep (se 1 (by rfl) ⟨37262834, by rfl⟩ : syracuseStep 49683779 = 74525669) B74525669
theorem B33119563 : Blo 1433536 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B3227291 : Blo 1433536 3227291 := bstep (se 1 (by rfl) ⟨2420468, by rfl⟩ : syracuseStep 3227291 = 4840937) B4840937
theorem B3227489 : Blo 1433536 3227489 := bstep (se 2 (by rfl) ⟨1210308, by rfl⟩ : syracuseStep 3227489 = 2420617) B2420617
theorem B1613695 : Blo 1433536 1613695 := bstep (se 1 (by rfl) ⟨1210271, by rfl⟩ : syracuseStep 1613695 = 2420543) B2420543
theorem B4841423 : Blo 1433536 4841423 := bstep (se 1 (by rfl) ⟨3631067, by rfl⟩ : syracuseStep 4841423 = 7262135) B7262135
theorem B3629033 : Blo 1433536 3629033 := bstep (se 2 (by rfl) ⟨1360887, by rfl⟩ : syracuseStep 3629033 = 2721775) B2721775
theorem B1433583 : Blo 1433536 1433583 := bstep (se 1 (by rfl) ⟨1075187, by rfl⟩ : syracuseStep 1433583 = 2150375) B2150375
theorem B1433631 : Blo 1433536 1433631 := bstep (se 1 (by rfl) ⟨1075223, by rfl⟩ : syracuseStep 1433631 = 2150447) B2150447
theorem B13787327 : Blo 1433536 13787327 := bstep (se 1 (by rfl) ⟨10340495, by rfl⟩ : syracuseStep 13787327 = 20680991) B20680991
theorem B1433927 : Blo 1433536 1433927 := bstep (se 1 (by rfl) ⟨1075445, by rfl⟩ : syracuseStep 1433927 = 2150891) B2150891
theorem B4841855 : Blo 1433536 4841855 := bstep (se 1 (by rfl) ⟨3631391, by rfl⟩ : syracuseStep 4841855 = 7262783) B7262783
theorem B1434011 : Blo 1433536 1434011 := bstep (se 1 (by rfl) ⟨1075508, by rfl⟩ : syracuseStep 1434011 = 2151017) B2151017
theorem B1434015 : Blo 1433536 1434015 := bstep (se 1 (by rfl) ⟨1075511, by rfl⟩ : syracuseStep 1434015 = 2151023) B2151023
theorem B1434095 : Blo 1433536 1434095 := bstep (se 1 (by rfl) ⟨1075571, by rfl⟩ : syracuseStep 1434095 = 2151143) B2151143
theorem B1434203 : Blo 1433536 1434203 := bstep (se 1 (by rfl) ⟨1075652, by rfl⟩ : syracuseStep 1434203 = 2151305) B2151305
theorem B9192143 : Blo 1433536 9192143 := bstep (se 1 (by rfl) ⟨6894107, by rfl⟩ : syracuseStep 9192143 = 13788215) B13788215
theorem B1434431 : Blo 1433536 1434431 := bstep (se 1 (by rfl) ⟨1075823, by rfl⟩ : syracuseStep 1434431 = 2151647) B2151647
theorem B1434459 : Blo 1433536 1434459 := bstep (se 1 (by rfl) ⟨1075844, by rfl⟩ : syracuseStep 1434459 = 2151689) B2151689
theorem B3228623 : Blo 1433536 3228623 := bstep (se 1 (by rfl) ⟨2421467, by rfl⟩ : syracuseStep 3228623 = 4842935) B4842935
theorem B13788251 : Blo 1433536 13788251 := bstep (se 1 (by rfl) ⟨10341188, by rfl⟩ : syracuseStep 13788251 = 20682377) B20682377
theorem B1434751 : Blo 1433536 1434751 := bstep (se 1 (by rfl) ⟨1076063, by rfl⟩ : syracuseStep 1434751 = 2152127) B2152127
theorem B20669579 : Blo 1433536 20669579 := bstep (se 1 (by rfl) ⟨15502184, by rfl⟩ : syracuseStep 20669579 = 31004369) B31004369
theorem B1434779 : Blo 1433536 1434779 := bstep (se 1 (by rfl) ⟨1076084, by rfl⟩ : syracuseStep 1434779 = 2152169) B2152169
theorem B1434783 : Blo 1433536 1434783 := bstep (se 1 (by rfl) ⟨1076087, by rfl⟩ : syracuseStep 1434783 = 2152175) B2152175
theorem B3228983 : Blo 1433536 3228983 := bstep (se 1 (by rfl) ⟨2421737, by rfl⟩ : syracuseStep 3228983 = 4843475) B4843475
theorem B1435119 : Blo 1433536 1435119 := bstep (se 1 (by rfl) ⟨1076339, by rfl⟩ : syracuseStep 1435119 = 2152679) B2152679
theorem B1435239 : Blo 1433536 1435239 := bstep (se 1 (by rfl) ⟨1076429, by rfl⟩ : syracuseStep 1435239 = 2152859) B2152859
theorem B10888829 : Blo 1433536 10888829 := bstep (se 3 (by rfl) ⟨2041655, by rfl⟩ : syracuseStep 10888829 = 4083311) B4083311
theorem B4843151 : Blo 1433536 4843151 := bstep (se 1 (by rfl) ⟨3632363, by rfl⟩ : syracuseStep 4843151 = 7264727) B7264727
theorem B10774235 : Blo 1433536 10774235 := bstep (se 1 (by rfl) ⟨8080676, by rfl⟩ : syracuseStep 10774235 = 16161353) B16161353
theorem B1435503 : Blo 1433536 1435503 := bstep (se 1 (by rfl) ⟨1076627, by rfl⟩ : syracuseStep 1435503 = 2153255) B2153255
theorem B7260029 : Blo 1433536 7260029 := bstep (se 3 (by rfl) ⟨1361255, by rfl⟩ : syracuseStep 7260029 = 2722511) B2722511
theorem B1435519 : Blo 1433536 1435519 := bstep (se 1 (by rfl) ⟨1076639, by rfl⟩ : syracuseStep 1435519 = 2153279) B2153279
theorem B3229595 : Blo 1433536 3229595 := bstep (se 1 (by rfl) ⟨2422196, by rfl⟩ : syracuseStep 3229595 = 4844393) B4844393
theorem B24520643 : Blo 1433536 24520643 := bstep (se 1 (by rfl) ⟨18390482, by rfl⟩ : syracuseStep 24520643 = 36780965) B36780965
theorem B27584495 : Blo 1433536 27584495 := bstep (se 1 (by rfl) ⟨20688371, by rfl⟩ : syracuseStep 27584495 = 41376743) B41376743
theorem B3229793 : Blo 1433536 3229793 := bstep (se 2 (by rfl) ⟨1211172, by rfl⟩ : syracuseStep 3229793 = 2422345) B2422345
theorem B33122519 : Blo 1433536 33122519 := bstep (se 1 (by rfl) ⟨24841889, by rfl⟩ : syracuseStep 33122519 = 49683779) B49683779
theorem B2722025 : Blo 1433536 2722025 := bstep (se 2 (by rfl) ⟨1020759, by rfl⟩ : syracuseStep 2722025 = 2041519) B2041519
theorem B35858765 : Blo 1433536 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B7752131 : Blo 1433536 7752131 := bstep (se 1 (by rfl) ⟨5814098, by rfl⟩ : syracuseStep 7752131 = 11628197) B11628197
theorem B4360841 : Blo 1433536 4360841 := bstep (se 2 (by rfl) ⟨1635315, by rfl⟩ : syracuseStep 4360841 = 3270631) B3270631
theorem B2419355 : Blo 1433536 2419355 := bstep (se 1 (by rfl) ⟨1814516, by rfl⟩ : syracuseStep 2419355 = 3629033) B3629033
theorem B2296555 : Blo 1433536 2296555 := bstep (se 1 (by rfl) ⟨1722416, by rfl⟩ : syracuseStep 2296555 = 3444833) B3444833
theorem B13093613 : Blo 1433536 13093613 := bstep (se 3 (by rfl) ⟨2455052, by rfl⟩ : syracuseStep 13093613 = 4910105) B4910105
theorem B82668599 : Blo 1433536 82668599 := bstep (se 1 (by rfl) ⟨62001449, by rfl⟩ : syracuseStep 82668599 = 124002899) B124002899
theorem B12258377 : Blo 1433536 12258377 := bstep (se 2 (by rfl) ⟨4596891, by rfl⟩ : syracuseStep 12258377 = 9193783) B9193783
theorem B5819903 : Blo 1433536 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B2420327 : Blo 1433536 2420327 := bstep (se 1 (by rfl) ⟨1815245, by rfl⟩ : syracuseStep 2420327 = 3630491) B3630491
theorem B510119527 : Blo 1433536 510119527 := bstep (se 1 (by rfl) ⟨382589645, by rfl⟩ : syracuseStep 510119527 = 765179291) B765179291
theorem B2297575 : Blo 1433536 2297575 := bstep (se 1 (by rfl) ⟨1723181, by rfl⟩ : syracuseStep 2297575 = 3446363) B3446363
theorem B22081319 : Blo 1433536 22081319 := bstep (se 1 (by rfl) ⟨16560989, by rfl⟩ : syracuseStep 22081319 = 33121979) B33121979
theorem B15945599 : Blo 1433536 15945599 := bstep (se 1 (by rfl) ⟨11959199, by rfl⟩ : syracuseStep 15945599 = 23918399) B23918399
theorem B18395099 : Blo 1433536 18395099 := bstep (se 1 (by rfl) ⟨13796324, by rfl⟩ : syracuseStep 18395099 = 27592649) B27592649
theorem B2150393 : Blo 1433536 2150393 := bstep (se 2 (by rfl) ⟨806397, by rfl⟩ : syracuseStep 2150393 = 1612795) B1612795
theorem B2150441 : Blo 1433536 2150441 := bstep (se 2 (by rfl) ⟨806415, by rfl⟩ : syracuseStep 2150441 = 1612831) B1612831
theorem B1724527 : Blo 1433536 1724527 := bstep (se 1 (by rfl) ⟨1293395, by rfl⟩ : syracuseStep 1724527 = 2586791) B2586791
theorem B5443807 : Blo 1433536 5443807 := bstep (se 1 (by rfl) ⟨4082855, by rfl⟩ : syracuseStep 5443807 = 8165711) B8165711
theorem B2150633 : Blo 1433536 2150633 := bstep (se 2 (by rfl) ⟨806487, by rfl⟩ : syracuseStep 2150633 = 1612975) B1612975
theorem B3633407 : Blo 1433536 3633407 := bstep (se 1 (by rfl) ⟨2725055, by rfl⟩ : syracuseStep 3633407 = 5450111) B5450111
theorem B2150825 : Blo 1433536 2150825 := bstep (se 2 (by rfl) ⟨806559, by rfl⟩ : syracuseStep 2150825 = 1613119) B1613119
theorem B44159417 : Blo 1433536 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B6124079 : Blo 1433536 6124079 := bstep (se 1 (by rfl) ⟨4593059, by rfl⟩ : syracuseStep 6124079 = 9186119) B9186119
theorem B2151131 : Blo 1433536 2151131 := bstep (se 1 (by rfl) ⟨1613348, by rfl⟩ : syracuseStep 2151131 = 3226697) B3226697
theorem B2421535 : Blo 1433536 2421535 := bstep (se 1 (by rfl) ⟨1816151, by rfl⟩ : syracuseStep 2421535 = 3632303) B3632303
theorem B2151527 : Blo 1433536 2151527 := bstep (se 1 (by rfl) ⟨1613645, by rfl⟩ : syracuseStep 2151527 = 3227291) B3227291
theorem B2151593 : Blo 1433536 2151593 := bstep (se 2 (by rfl) ⟨806847, by rfl⟩ : syracuseStep 2151593 = 1613695) B1613695
theorem B2421947 : Blo 1433536 2421947 := bstep (se 1 (by rfl) ⟨1816460, by rfl⟩ : syracuseStep 2421947 = 3632921) B3632921
theorem B2151659 : Blo 1433536 2151659 := bstep (se 1 (by rfl) ⟨1613744, by rfl⟩ : syracuseStep 2151659 = 3227489) B3227489
theorem B20952827 : Blo 1433536 20952827 := bstep (se 1 (by rfl) ⟨15714620, by rfl⟩ : syracuseStep 20952827 = 31429241) B31429241
theorem B7264079 : Blo 1433536 7264079 := bstep (se 1 (by rfl) ⟨5448059, by rfl⟩ : syracuseStep 7264079 = 10896119) B10896119
theorem B2152559 : Blo 1433536 2152559 := bstep (se 1 (by rfl) ⟨1614419, by rfl⟩ : syracuseStep 2152559 = 3228839) B3228839
theorem B2152631 : Blo 1433536 2152631 := bstep (se 1 (by rfl) ⟨1614473, by rfl⟩ : syracuseStep 2152631 = 3228947) B3228947
theorem B11639027 : Blo 1433536 11639027 := bstep (se 1 (by rfl) ⟨8729270, by rfl⟩ : syracuseStep 11639027 = 17458541) B17458541
theorem B15514031 : Blo 1433536 15514031 := bstep (se 1 (by rfl) ⟨11635523, by rfl⟩ : syracuseStep 15514031 = 23271047) B23271047
theorem B2153051 : Blo 1433536 2153051 := bstep (se 1 (by rfl) ⟨1614788, by rfl⟩ : syracuseStep 2153051 = 3229577) B3229577
theorem B3447593 : Blo 1433536 3447593 := bstep (se 2 (by rfl) ⟨1292847, by rfl⟩ : syracuseStep 3447593 = 2585695) B2585695
theorem B4594495 : Blo 1433536 4594495 := bstep (se 1 (by rfl) ⟨3445871, by rfl⟩ : syracuseStep 4594495 = 6891743) B6891743
theorem B6544223 : Blo 1433536 6544223 := bstep (se 1 (by rfl) ⟨4908167, by rfl⟩ : syracuseStep 6544223 = 9816335) B9816335
theorem B3226751 : Blo 1433536 3226751 := bstep (se 1 (by rfl) ⟨2420063, by rfl⟩ : syracuseStep 3226751 = 4840127) B4840127
theorem B18373877 : Blo 1433536 18373877 := bstep (se 5 (by rfl) ⟨861275, by rfl⟩ : syracuseStep 18373877 = 1722551) B1722551
theorem B4840775 : Blo 1433536 4840775 := bstep (se 1 (by rfl) ⟨3630581, by rfl⟩ : syracuseStep 4840775 = 7261163) B7261163
theorem B12254651 : Blo 1433536 12254651 := bstep (se 1 (by rfl) ⟨9190988, by rfl⟩ : syracuseStep 12254651 = 18381977) B18381977
theorem B3628921 : Blo 1433536 3628921 := bstep (se 2 (by rfl) ⟨1360845, by rfl⟩ : syracuseStep 3628921 = 2721691) B2721691
theorem B3227615 : Blo 1433536 3227615 := bstep (se 1 (by rfl) ⟨2420711, by rfl⟩ : syracuseStep 3227615 = 4841423) B4841423
theorem B1433627 : Blo 1433536 1433627 := bstep (se 1 (by rfl) ⟨1075220, by rfl⟩ : syracuseStep 1433627 = 2150441) B2150441
theorem B9191551 : Blo 1433536 9191551 := bstep (se 1 (by rfl) ⟨6893663, by rfl⟩ : syracuseStep 9191551 = 13787327) B13787327
theorem B1433755 : Blo 1433536 1433755 := bstep (se 1 (by rfl) ⟨1075316, by rfl⟩ : syracuseStep 1433755 = 2150633) B2150633
theorem B3227903 : Blo 1433536 3227903 := bstep (se 1 (by rfl) ⟨2420927, by rfl⟩ : syracuseStep 3227903 = 4841855) B4841855
theorem B1433883 : Blo 1433536 1433883 := bstep (se 1 (by rfl) ⟨1075412, by rfl⟩ : syracuseStep 1433883 = 2150825) B2150825
theorem B7258409 : Blo 1433536 7258409 := bstep (se 2 (by rfl) ⟨2721903, by rfl⟩ : syracuseStep 7258409 = 5443807) B5443807
theorem B6128095 : Blo 1433536 6128095 := bstep (se 1 (by rfl) ⟨4596071, by rfl⟩ : syracuseStep 6128095 = 9192143) B9192143
theorem B1434087 : Blo 1433536 1434087 := bstep (se 1 (by rfl) ⟨1075565, by rfl⟩ : syracuseStep 1434087 = 2151131) B2151131
theorem B7258733 : Blo 1433536 7258733 := bstep (se 3 (by rfl) ⟨1361012, by rfl⟩ : syracuseStep 7258733 = 2722025) B2722025
theorem B9192167 : Blo 1433536 9192167 := bstep (se 1 (by rfl) ⟨6894125, by rfl⟩ : syracuseStep 9192167 = 13788251) B13788251
theorem B1434351 : Blo 1433536 1434351 := bstep (se 1 (by rfl) ⟨1075763, by rfl⟩ : syracuseStep 1434351 = 2151527) B2151527
theorem B13779719 : Blo 1433536 13779719 := bstep (se 1 (by rfl) ⟨10334789, by rfl⟩ : syracuseStep 13779719 = 20669579) B20669579
theorem B1434395 : Blo 1433536 1434395 := bstep (se 1 (by rfl) ⟨1075796, by rfl⟩ : syracuseStep 1434395 = 2151593) B2151593
theorem B1614631 : Blo 1433536 1614631 := bstep (se 1 (by rfl) ⟨1210973, by rfl⟩ : syracuseStep 1614631 = 2421947) B2421947
theorem B1434439 : Blo 1433536 1434439 := bstep (se 1 (by rfl) ⟨1075829, by rfl⟩ : syracuseStep 1434439 = 2151659) B2151659
theorem B3228713 : Blo 1433536 3228713 := bstep (se 2 (by rfl) ⟨1210767, by rfl⟩ : syracuseStep 3228713 = 2421535) B2421535
theorem B7259219 : Blo 1433536 7259219 := bstep (se 1 (by rfl) ⟨5444414, by rfl⟩ : syracuseStep 7259219 = 10888829) B10888829
theorem B3228767 : Blo 1433536 3228767 := bstep (se 1 (by rfl) ⟨2421575, by rfl⟩ : syracuseStep 3228767 = 4843151) B4843151
theorem B41370749 : Blo 1433536 41370749 := bstep (se 3 (by rfl) ⟨7757015, by rfl⟩ : syracuseStep 41370749 = 15514031) B15514031
theorem B13968551 : Blo 1433536 13968551 := bstep (se 1 (by rfl) ⟨10476413, by rfl⟩ : syracuseStep 13968551 = 20952827) B20952827
theorem B4842719 : Blo 1433536 4842719 := bstep (se 1 (by rfl) ⟨3632039, by rfl⟩ : syracuseStep 4842719 = 7264079) B7264079
theorem B12248293 : Blo 1433536 12248293 := bstep (se 4 (by rfl) ⟨1148277, by rfl⟩ : syracuseStep 12248293 = 2296555) B2296555
theorem B1435039 : Blo 1433536 1435039 := bstep (se 1 (by rfl) ⟨1076279, by rfl⟩ : syracuseStep 1435039 = 2152559) B2152559
theorem B1435087 : Blo 1433536 1435087 := bstep (se 1 (by rfl) ⟨1076315, by rfl⟩ : syracuseStep 1435087 = 2152631) B2152631
theorem B7759351 : Blo 1433536 7759351 := bstep (se 1 (by rfl) ⟨5819513, by rfl⟩ : syracuseStep 7759351 = 11639027) B11639027
theorem B23905843 : Blo 1433536 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B1435367 : Blo 1433536 1435367 := bstep (se 1 (by rfl) ⟨1076525, by rfl⟩ : syracuseStep 1435367 = 2153051) B2153051
theorem B28731293 : Blo 1433536 28731293 := bstep (se 3 (by rfl) ⟨5387117, by rfl⟩ : syracuseStep 28731293 = 10774235) B10774235
theorem B680159369 : Blo 1433536 680159369 := bstep (se 2 (by rfl) ⟨255059763, by rfl⟩ : syracuseStep 680159369 = 510119527) B510119527
theorem B12249251 : Blo 1433536 12249251 := bstep (se 1 (by rfl) ⟨9186938, by rfl⟩ : syracuseStep 12249251 = 18373877) B18373877
theorem B8169767 : Blo 1433536 8169767 := bstep (se 1 (by rfl) ⟨6127325, by rfl⟩ : syracuseStep 8169767 = 12254651) B12254651
theorem B4082719 : Blo 1433536 4082719 := bstep (se 1 (by rfl) ⟨3062039, by rfl⟩ : syracuseStep 4082719 = 6124079) B6124079
theorem B16347095 : Blo 1433536 16347095 := bstep (se 1 (by rfl) ⟨12260321, by rfl⟩ : syracuseStep 16347095 = 24520643) B24520643
theorem B22081679 : Blo 1433536 22081679 := bstep (se 1 (by rfl) ⟨16561259, by rfl⟩ : syracuseStep 22081679 = 33122519) B33122519
theorem B8729075 : Blo 1433536 8729075 := bstep (se 1 (by rfl) ⟨6546806, by rfl⟩ : syracuseStep 8729075 = 13093613) B13093613
theorem B2298395 : Blo 1433536 2298395 := bstep (se 1 (by rfl) ⟨1723796, by rfl⟩ : syracuseStep 2298395 = 3447593) B3447593
theorem B4362815 : Blo 1433536 4362815 := bstep (se 1 (by rfl) ⟨3272111, by rfl⟩ : syracuseStep 4362815 = 6544223) B6544223
theorem B55112399 : Blo 1433536 55112399 := bstep (se 1 (by rfl) ⟨41334299, by rfl⟩ : syracuseStep 55112399 = 82668599) B82668599
theorem B8172251 : Blo 1433536 8172251 := bstep (se 1 (by rfl) ⟨6129188, by rfl⟩ : syracuseStep 8172251 = 12258377) B12258377
theorem B2151167 : Blo 1433536 2151167 := bstep (se 1 (by rfl) ⟨1613375, by rfl⟩ : syracuseStep 2151167 = 3226751) B3226751
theorem B3879935 : Blo 1433536 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B4838561 : Blo 1433536 4838561 := bstep (se 2 (by rfl) ⟨1814460, by rfl⟩ : syracuseStep 4838561 = 3628921) B3628921
theorem B10630399 : Blo 1433536 10630399 := bstep (se 1 (by rfl) ⟨7972799, by rfl⟩ : syracuseStep 10630399 = 15945599) B15945599
theorem B2151743 : Blo 1433536 2151743 := bstep (se 1 (by rfl) ⟨1613807, by rfl⟩ : syracuseStep 2151743 = 3227615) B3227615
theorem B2299369 : Blo 1433536 2299369 := bstep (se 2 (by rfl) ⟨862263, by rfl⟩ : syracuseStep 2299369 = 1724527) B1724527
theorem B2422271 : Blo 1433536 2422271 := bstep (se 1 (by rfl) ⟨1816703, by rfl⟩ : syracuseStep 2422271 = 3633407) B3633407
theorem B29439611 : Blo 1433536 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B2152415 : Blo 1433536 2152415 := bstep (se 1 (by rfl) ⟨1614311, by rfl⟩ : syracuseStep 2152415 = 3228623) B3228623
theorem B2152655 : Blo 1433536 2152655 := bstep (se 1 (by rfl) ⟨1614491, by rfl⟩ : syracuseStep 2152655 = 3228983) B3228983
theorem B6125993 : Blo 1433536 6125993 := bstep (se 2 (by rfl) ⟨2297247, by rfl⟩ : syracuseStep 6125993 = 4594495) B4594495
theorem B4840019 : Blo 1433536 4840019 := bstep (se 1 (by rfl) ⟨3630014, by rfl⟩ : syracuseStep 4840019 = 7260029) B7260029
theorem B2153063 : Blo 1433536 2153063 := bstep (se 1 (by rfl) ⟨1614797, by rfl⟩ : syracuseStep 2153063 = 3229595) B3229595
theorem B18389663 : Blo 1433536 18389663 := bstep (se 1 (by rfl) ⟨13792247, by rfl⟩ : syracuseStep 18389663 = 27584495) B27584495
theorem B2153195 : Blo 1433536 2153195 := bstep (se 1 (by rfl) ⟨1614896, by rfl⟩ : syracuseStep 2153195 = 3229793) B3229793
theorem B5168087 : Blo 1433536 5168087 := bstep (se 1 (by rfl) ⟨3876065, by rfl⟩ : syracuseStep 5168087 = 7752131) B7752131
theorem B2907227 : Blo 1433536 2907227 := bstep (se 1 (by rfl) ⟨2180420, by rfl⟩ : syracuseStep 2907227 = 4360841) B4360841
theorem B1612903 : Blo 1433536 1612903 := bstep (se 1 (by rfl) ⟨1209677, by rfl⟩ : syracuseStep 1612903 = 2419355) B2419355
theorem B3227183 : Blo 1433536 3227183 := bstep (se 1 (by rfl) ⟨2420387, by rfl⟩ : syracuseStep 3227183 = 4840775) B4840775
theorem B3063433 : Blo 1433536 3063433 := bstep (se 2 (by rfl) ⟨1148787, by rfl⟩ : syracuseStep 3063433 = 2297575) B2297575
theorem B1613551 : Blo 1433536 1613551 := bstep (se 1 (by rfl) ⟨1210163, by rfl⟩ : syracuseStep 1613551 = 2420327) B2420327
theorem B14720879 : Blo 1433536 14720879 := bstep (se 1 (by rfl) ⟨11040659, by rfl⟩ : syracuseStep 14720879 = 22081319) B22081319
theorem B12263399 : Blo 1433536 12263399 := bstep (se 1 (by rfl) ⟨9197549, by rfl⟩ : syracuseStep 12263399 = 18395099) B18395099
theorem B1433595 : Blo 1433536 1433595 := bstep (se 1 (by rfl) ⟨1075196, by rfl⟩ : syracuseStep 1433595 = 2150393) B2150393
theorem B14721119 : Blo 1433536 14721119 := bstep (se 1 (by rfl) ⟨11040839, by rfl⟩ : syracuseStep 14721119 = 22081679) B22081679
theorem B12255401 : Blo 1433536 12255401 := bstep (se 2 (by rfl) ⟨4595775, by rfl⟩ : syracuseStep 12255401 = 9191551) B9191551
theorem B2908543 : Blo 1433536 2908543 := bstep (se 1 (by rfl) ⟨2181407, by rfl⟩ : syracuseStep 2908543 = 4362815) B4362815
theorem B36741599 : Blo 1433536 36741599 := bstep (se 1 (by rfl) ⟨27556199, by rfl⟩ : syracuseStep 36741599 = 55112399) B55112399
theorem B5448167 : Blo 1433536 5448167 := bstep (se 1 (by rfl) ⟨4086125, by rfl⟩ : syracuseStep 5448167 = 8172251) B8172251
theorem B6128111 : Blo 1433536 6128111 := bstep (se 1 (by rfl) ⟨4596083, by rfl⟩ : syracuseStep 6128111 = 9192167) B9192167
theorem B1434111 : Blo 1433536 1434111 := bstep (se 1 (by rfl) ⟨1075583, by rfl⟩ : syracuseStep 1434111 = 2151167) B2151167
theorem B3228479 : Blo 1433536 3228479 := bstep (se 1 (by rfl) ⟨2421359, by rfl⟩ : syracuseStep 3228479 = 4842719) B4842719
theorem B1434495 : Blo 1433536 1434495 := bstep (se 1 (by rfl) ⟨1075871, by rfl⟩ : syracuseStep 1434495 = 2151743) B2151743
theorem B1614847 : Blo 1433536 1614847 := bstep (se 1 (by rfl) ⟨1211135, by rfl⟩ : syracuseStep 1614847 = 2422271) B2422271
theorem B19154195 : Blo 1433536 19154195 := bstep (se 1 (by rfl) ⟨14365646, by rfl⟩ : syracuseStep 19154195 = 28731293) B28731293
theorem B1434943 : Blo 1433536 1434943 := bstep (se 1 (by rfl) ⟨1076207, by rfl⟩ : syracuseStep 1434943 = 2152415) B2152415
theorem B6129053 : Blo 1433536 6129053 := bstep (se 3 (by rfl) ⟨1149197, by rfl⟩ : syracuseStep 6129053 = 2298395) B2298395
theorem B1435103 : Blo 1433536 1435103 := bstep (se 1 (by rfl) ⟨1076327, by rfl⟩ : syracuseStep 1435103 = 2152655) B2152655
theorem B14173865 : Blo 1433536 14173865 := bstep (se 2 (by rfl) ⟨5315199, by rfl⟩ : syracuseStep 14173865 = 10630399) B10630399
theorem B1435375 : Blo 1433536 1435375 := bstep (se 1 (by rfl) ⟨1076531, by rfl⟩ : syracuseStep 1435375 = 2153063) B2153063
theorem B1435463 : Blo 1433536 1435463 := bstep (se 1 (by rfl) ⟨1076597, by rfl⟩ : syracuseStep 1435463 = 2153195) B2153195
theorem B3065825 : Blo 1433536 3065825 := bstep (se 2 (by rfl) ⟨1149684, by rfl⟩ : syracuseStep 3065825 = 2299369) B2299369
theorem B10898063 : Blo 1433536 10898063 := bstep (se 1 (by rfl) ⟨8173547, by rfl⟩ : syracuseStep 10898063 = 16347095) B16347095
theorem B5819383 : Blo 1433536 5819383 := bstep (se 1 (by rfl) ⟨4364537, by rfl⟩ : syracuseStep 5819383 = 8729075) B8729075
theorem B9186479 : Blo 1433536 9186479 := bstep (se 1 (by rfl) ⟨6889859, by rfl⟩ : syracuseStep 9186479 = 13779719) B13779719
theorem B8170793 : Blo 1433536 8170793 := bstep (se 2 (by rfl) ⟨3064047, by rfl⟩ : syracuseStep 8170793 = 6128095) B6128095
theorem B5443625 : Blo 1433536 5443625 := bstep (se 2 (by rfl) ⟨2041359, by rfl⟩ : syracuseStep 5443625 = 4082719) B4082719
theorem B453439579 : Blo 1433536 453439579 := bstep (se 1 (by rfl) ⟨340079684, by rfl⟩ : syracuseStep 453439579 = 680159369) B680159369
theorem B2150537 : Blo 1433536 2150537 := bstep (se 2 (by rfl) ⟨806451, by rfl⟩ : syracuseStep 2150537 = 1612903) B1612903
theorem B4083995 : Blo 1433536 4083995 := bstep (se 1 (by rfl) ⟨3062996, by rfl⟩ : syracuseStep 4083995 = 6125993) B6125993
theorem B16331057 : Blo 1433536 16331057 := bstep (se 2 (by rfl) ⟨6124146, by rfl⟩ : syracuseStep 16331057 = 12248293) B12248293
theorem B12259775 : Blo 1433536 12259775 := bstep (se 1 (by rfl) ⟨9194831, by rfl⟩ : syracuseStep 12259775 = 18389663) B18389663
theorem B3445391 : Blo 1433536 3445391 := bstep (se 1 (by rfl) ⟨2584043, by rfl⟩ : syracuseStep 3445391 = 5168087) B5168087
theorem B1938151 : Blo 1433536 1938151 := bstep (se 1 (by rfl) ⟨1453613, by rfl⟩ : syracuseStep 1938151 = 2907227) B2907227
theorem B4084577 : Blo 1433536 4084577 := bstep (se 2 (by rfl) ⟨1531716, by rfl⟩ : syracuseStep 4084577 = 3063433) B3063433
theorem B2151401 : Blo 1433536 2151401 := bstep (se 2 (by rfl) ⟨806775, by rfl⟩ : syracuseStep 2151401 = 1613551) B1613551
theorem B2151455 : Blo 1433536 2151455 := bstep (se 1 (by rfl) ⟨1613591, by rfl⟩ : syracuseStep 2151455 = 3227183) B3227183
theorem B2151935 : Blo 1433536 2151935 := bstep (se 1 (by rfl) ⟨1613951, by rfl⟩ : syracuseStep 2151935 = 3227903) B3227903
theorem B4838939 : Blo 1433536 4838939 := bstep (se 1 (by rfl) ⟨3629204, by rfl⟩ : syracuseStep 4838939 = 7258409) B7258409
theorem B127497829 : Blo 1433536 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B4839155 : Blo 1433536 4839155 := bstep (se 1 (by rfl) ⟨3629366, by rfl⟩ : syracuseStep 4839155 = 7258733) B7258733
theorem B2586623 : Blo 1433536 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B2152475 : Blo 1433536 2152475 := bstep (se 1 (by rfl) ⟨1614356, by rfl⟩ : syracuseStep 2152475 = 3228713) B3228713
theorem B4839479 : Blo 1433536 4839479 := bstep (se 1 (by rfl) ⟨3629609, by rfl⟩ : syracuseStep 4839479 = 7259219) B7259219
theorem B2152511 : Blo 1433536 2152511 := bstep (se 1 (by rfl) ⟨1614383, by rfl⟩ : syracuseStep 2152511 = 3228767) B3228767
theorem B27580499 : Blo 1433536 27580499 := bstep (se 1 (by rfl) ⟨20685374, by rfl⟩ : syracuseStep 27580499 = 41370749) B41370749
theorem B3225707 : Blo 1433536 3225707 := bstep (se 1 (by rfl) ⟨2419280, by rfl⟩ : syracuseStep 3225707 = 4838561) B4838561
theorem B9312367 : Blo 1433536 9312367 := bstep (se 1 (by rfl) ⟨6984275, by rfl⟩ : syracuseStep 9312367 = 13968551) B13968551
theorem B2152841 : Blo 1433536 2152841 := bstep (se 2 (by rfl) ⟨807315, by rfl⟩ : syracuseStep 2152841 = 1614631) B1614631
theorem B19626407 : Blo 1433536 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B8166167 : Blo 1433536 8166167 := bstep (se 1 (by rfl) ⟨6124625, by rfl⟩ : syracuseStep 8166167 = 12249251) B12249251
theorem B5446511 : Blo 1433536 5446511 := bstep (se 1 (by rfl) ⟨4084883, by rfl⟩ : syracuseStep 5446511 = 8169767) B8169767
theorem B3226679 : Blo 1433536 3226679 := bstep (se 1 (by rfl) ⟨2420009, by rfl⟩ : syracuseStep 3226679 = 4840019) B4840019
theorem B10345801 : Blo 1433536 10345801 := bstep (se 2 (by rfl) ⟨3879675, by rfl⟩ : syracuseStep 10345801 = 7759351) B7759351
theorem B9813919 : Blo 1433536 9813919 := bstep (se 1 (by rfl) ⟨7360439, by rfl⟩ : syracuseStep 9813919 = 14720879) B14720879
theorem B8175599 : Blo 1433536 8175599 := bstep (se 1 (by rfl) ⟨6131699, by rfl⟩ : syracuseStep 8175599 = 12263399) B12263399
theorem B3629083 : Blo 1433536 3629083 := bstep (se 1 (by rfl) ⟨2721812, by rfl⟩ : syracuseStep 3629083 = 5443625) B5443625
theorem B9814079 : Blo 1433536 9814079 := bstep (se 1 (by rfl) ⟨7360559, by rfl⟩ : syracuseStep 9814079 = 14721119) B14721119
theorem B1433691 : Blo 1433536 1433691 := bstep (se 1 (by rfl) ⟨1075268, by rfl⟩ : syracuseStep 1433691 = 2150537) B2150537
theorem B604586105 : Blo 1433536 604586105 := bstep (se 2 (by rfl) ⟨226719789, by rfl⟩ : syracuseStep 604586105 = 453439579) B453439579
theorem B10887371 : Blo 1433536 10887371 := bstep (se 1 (by rfl) ⟨8165528, by rfl⟩ : syracuseStep 10887371 = 16331057) B16331057
theorem B24494399 : Blo 1433536 24494399 := bstep (se 1 (by rfl) ⟨18370799, by rfl⟩ : syracuseStep 24494399 = 36741599) B36741599
theorem B1434267 : Blo 1433536 1434267 := bstep (se 1 (by rfl) ⟨1075700, by rfl⟩ : syracuseStep 1434267 = 2151401) B2151401
theorem B1434303 : Blo 1433536 1434303 := bstep (se 1 (by rfl) ⟨1075727, by rfl⟩ : syracuseStep 1434303 = 2151455) B2151455
theorem B1434623 : Blo 1433536 1434623 := bstep (se 1 (by rfl) ⟨1075967, by rfl⟩ : syracuseStep 1434623 = 2151935) B2151935
theorem B1434983 : Blo 1433536 1434983 := bstep (se 1 (by rfl) ⟨1076237, by rfl⟩ : syracuseStep 1434983 = 2152475) B2152475
theorem B1435007 : Blo 1433536 1435007 := bstep (se 1 (by rfl) ⟨1076255, by rfl⟩ : syracuseStep 1435007 = 2152511) B2152511
theorem B1435227 : Blo 1433536 1435227 := bstep (se 1 (by rfl) ⟨1076420, by rfl⟩ : syracuseStep 1435227 = 2152841) B2152841
theorem B13084271 : Blo 1433536 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B3631007 : Blo 1433536 3631007 := bstep (se 1 (by rfl) ⟨2723255, by rfl⟩ : syracuseStep 3631007 = 5446511) B5446511
theorem B13085225 : Blo 1433536 13085225 := bstep (se 2 (by rfl) ⟨4906959, by rfl⟩ : syracuseStep 13085225 = 9813919) B9813919
theorem B5450399 : Blo 1433536 5450399 := bstep (se 1 (by rfl) ⟨4087799, by rfl⟩ : syracuseStep 5450399 = 8175599) B8175599
theorem B8170267 : Blo 1433536 8170267 := bstep (se 1 (by rfl) ⟨6127700, by rfl⟩ : syracuseStep 8170267 = 12255401) B12255401
theorem B2722663 : Blo 1433536 2722663 := bstep (se 1 (by rfl) ⟨2041997, by rfl⟩ : syracuseStep 2722663 = 4083995) B4083995
theorem B3632111 : Blo 1433536 3632111 := bstep (se 1 (by rfl) ⟨2724083, by rfl⟩ : syracuseStep 3632111 = 5448167) B5448167
theorem B2296927 : Blo 1433536 2296927 := bstep (se 1 (by rfl) ⟨1722695, by rfl⟩ : syracuseStep 2296927 = 3445391) B3445391
theorem B3878057 : Blo 1433536 3878057 := bstep (se 2 (by rfl) ⟨1454271, by rfl⟩ : syracuseStep 3878057 = 2908543) B2908543
theorem B2723051 : Blo 1433536 2723051 := bstep (se 1 (by rfl) ⟨2042288, by rfl⟩ : syracuseStep 2723051 = 4084577) B4084577
theorem B9449243 : Blo 1433536 9449243 := bstep (se 1 (by rfl) ⟨7086932, by rfl⟩ : syracuseStep 9449243 = 14173865) B14173865
theorem B2043883 : Blo 1433536 2043883 := bstep (se 1 (by rfl) ⟨1532912, by rfl⟩ : syracuseStep 2043883 = 3065825) B3065825
theorem B18386999 : Blo 1433536 18386999 := bstep (se 1 (by rfl) ⟨13790249, by rfl⟩ : syracuseStep 18386999 = 27580499) B27580499
theorem B2150471 : Blo 1433536 2150471 := bstep (se 1 (by rfl) ⟨1612853, by rfl⟩ : syracuseStep 2150471 = 3225707) B3225707
theorem B5444111 : Blo 1433536 5444111 := bstep (se 1 (by rfl) ⟨4083083, by rfl⟩ : syracuseStep 5444111 = 8166167) B8166167
theorem B2151119 : Blo 1433536 2151119 := bstep (se 1 (by rfl) ⟨1613339, by rfl⟩ : syracuseStep 2151119 = 3226679) B3226679
theorem B6124319 : Blo 1433536 6124319 := bstep (se 1 (by rfl) ⟨4593239, by rfl⟩ : syracuseStep 6124319 = 9186479) B9186479
theorem B169997105 : Blo 1433536 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B31036709 : Blo 1433536 31036709 := bstep (se 4 (by rfl) ⟨2909691, by rfl⟩ : syracuseStep 31036709 = 5819383) B5819383
theorem B12416489 : Blo 1433536 12416489 := bstep (se 2 (by rfl) ⟨4656183, by rfl⟩ : syracuseStep 12416489 = 9312367) B9312367
theorem B8173183 : Blo 1433536 8173183 := bstep (se 1 (by rfl) ⟨6129887, by rfl⟩ : syracuseStep 8173183 = 12259775) B12259775
theorem B4085407 : Blo 1433536 4085407 := bstep (se 1 (by rfl) ⟨3064055, by rfl⟩ : syracuseStep 4085407 = 6128111) B6128111
theorem B2152319 : Blo 1433536 2152319 := bstep (se 1 (by rfl) ⟨1614239, by rfl⟩ : syracuseStep 2152319 = 3228479) B3228479
theorem B12769463 : Blo 1433536 12769463 := bstep (se 1 (by rfl) ⟨9577097, by rfl⟩ : syracuseStep 12769463 = 19154195) B19154195
theorem B4086035 : Blo 1433536 4086035 := bstep (se 1 (by rfl) ⟨3064526, by rfl⟩ : syracuseStep 4086035 = 6129053) B6129053
theorem B3225959 : Blo 1433536 3225959 := bstep (se 1 (by rfl) ⟨2419469, by rfl⟩ : syracuseStep 3225959 = 4838939) B4838939
theorem B3226103 : Blo 1433536 3226103 := bstep (se 1 (by rfl) ⟨2419577, by rfl⟩ : syracuseStep 3226103 = 4839155) B4839155
theorem B10336805 : Blo 1433536 10336805 := bstep (se 4 (by rfl) ⟨969075, by rfl⟩ : syracuseStep 10336805 = 1938151) B1938151
theorem B2153129 : Blo 1433536 2153129 := bstep (se 2 (by rfl) ⟨807423, by rfl⟩ : syracuseStep 2153129 = 1614847) B1614847
theorem B3226319 : Blo 1433536 3226319 := bstep (se 1 (by rfl) ⟨2419739, by rfl⟩ : syracuseStep 3226319 = 4839479) B4839479
theorem B7265375 : Blo 1433536 7265375 := bstep (se 1 (by rfl) ⟨5449031, by rfl⟩ : syracuseStep 7265375 = 10898063) B10898063
theorem B13794401 : Blo 1433536 13794401 := bstep (se 2 (by rfl) ⟨5172900, by rfl⟩ : syracuseStep 13794401 = 10345801) B10345801
theorem B5447195 : Blo 1433536 5447195 := bstep (se 1 (by rfl) ⟨4085396, by rfl⟩ : syracuseStep 5447195 = 8170793) B8170793
theorem B27590645 : Blo 1433536 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B1433647 : Blo 1433536 1433647 := bstep (se 1 (by rfl) ⟨1075235, by rfl⟩ : syracuseStep 1433647 = 2150471) B2150471
theorem B7258247 : Blo 1433536 7258247 := bstep (se 1 (by rfl) ⟨5443685, by rfl⟩ : syracuseStep 7258247 = 10887371) B10887371
theorem B3629407 : Blo 1433536 3629407 := bstep (se 1 (by rfl) ⟨2722055, by rfl⟩ : syracuseStep 3629407 = 5444111) B5444111
theorem B1434079 : Blo 1433536 1434079 := bstep (se 1 (by rfl) ⟨1075559, by rfl⟩ : syracuseStep 1434079 = 2151119) B2151119
theorem B3630217 : Blo 1433536 3630217 := bstep (se 2 (by rfl) ⟨1361331, by rfl⟩ : syracuseStep 3630217 = 2722663) B2722663
theorem B1434879 : Blo 1433536 1434879 := bstep (se 1 (by rfl) ⟨1076159, by rfl⟩ : syracuseStep 1434879 = 2152319) B2152319
theorem B8512975 : Blo 1433536 8512975 := bstep (se 1 (by rfl) ⟨6384731, by rfl⟩ : syracuseStep 8512975 = 12769463) B12769463
theorem B6891203 : Blo 1433536 6891203 := bstep (se 1 (by rfl) ⟨5168402, by rfl⟩ : syracuseStep 6891203 = 10336805) B10336805
theorem B1435419 : Blo 1433536 1435419 := bstep (se 1 (by rfl) ⟨1076564, by rfl⟩ : syracuseStep 1435419 = 2153129) B2153129
theorem B4843583 : Blo 1433536 4843583 := bstep (se 1 (by rfl) ⟨3632687, by rfl⟩ : syracuseStep 4843583 = 7265375) B7265375
theorem B10897577 : Blo 1433536 10897577 := bstep (se 2 (by rfl) ⟨4086591, by rfl⟩ : syracuseStep 10897577 = 8173183) B8173183
theorem B3631463 : Blo 1433536 3631463 := bstep (se 1 (by rfl) ⟨2723597, by rfl⟩ : syracuseStep 3631463 = 5447195) B5447195
theorem B18393763 : Blo 1433536 18393763 := bstep (se 1 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 18393763 = 27590645) B27590645
theorem B12257999 : Blo 1433536 12257999 := bstep (se 1 (by rfl) ⟨9193499, by rfl⟩ : syracuseStep 12257999 = 18386999) B18386999
theorem B403057403 : Blo 1433536 403057403 := bstep (se 1 (by rfl) ⟨302293052, by rfl⟩ : syracuseStep 403057403 = 604586105) B604586105
theorem B16329599 : Blo 1433536 16329599 := bstep (se 1 (by rfl) ⟨12247199, by rfl⟩ : syracuseStep 16329599 = 24494399) B24494399
theorem B12250277 : Blo 1433536 12250277 := bstep (se 4 (by rfl) ⟨1148463, by rfl⟩ : syracuseStep 12250277 = 2296927) B2296927
theorem B4082879 : Blo 1433536 4082879 := bstep (se 1 (by rfl) ⟨3062159, by rfl⟩ : syracuseStep 4082879 = 6124319) B6124319
theorem B113331403 : Blo 1433536 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B8277659 : Blo 1433536 8277659 := bstep (se 1 (by rfl) ⟨6208244, by rfl⟩ : syracuseStep 8277659 = 12416489) B12416489
theorem B2420671 : Blo 1433536 2420671 := bstep (se 1 (by rfl) ⟨1815503, by rfl⟩ : syracuseStep 2420671 = 3631007) B3631007
theorem B2724023 : Blo 1433536 2724023 := bstep (se 1 (by rfl) ⟨2043017, by rfl⟩ : syracuseStep 2724023 = 4086035) B4086035
theorem B2150639 : Blo 1433536 2150639 := bstep (se 1 (by rfl) ⟨1612979, by rfl⟩ : syracuseStep 2150639 = 3225959) B3225959
theorem B2150735 : Blo 1433536 2150735 := bstep (se 1 (by rfl) ⟨1613051, by rfl⟩ : syracuseStep 2150735 = 3226103) B3226103
theorem B3633599 : Blo 1433536 3633599 := bstep (se 1 (by rfl) ⟨2725199, by rfl⟩ : syracuseStep 3633599 = 5450399) B5450399
theorem B2150879 : Blo 1433536 2150879 := bstep (se 1 (by rfl) ⟨1613159, by rfl⟩ : syracuseStep 2150879 = 3226319) B3226319
theorem B2421407 : Blo 1433536 2421407 := bstep (se 1 (by rfl) ⟨1816055, by rfl⟩ : syracuseStep 2421407 = 3632111) B3632111
theorem B9196267 : Blo 1433536 9196267 := bstep (se 1 (by rfl) ⟨6897200, by rfl⟩ : syracuseStep 9196267 = 13794401) B13794401
theorem B2585371 : Blo 1433536 2585371 := bstep (se 1 (by rfl) ⟨1939028, by rfl⟩ : syracuseStep 2585371 = 3878057) B3878057
theorem B1815367 : Blo 1433536 1815367 := bstep (se 1 (by rfl) ⟨1361525, by rfl⟩ : syracuseStep 1815367 = 2723051) B2723051
theorem B2725177 : Blo 1433536 2725177 := bstep (se 2 (by rfl) ⟨1021941, by rfl⟩ : syracuseStep 2725177 = 2043883) B2043883
theorem B4838777 : Blo 1433536 4838777 := bstep (se 2 (by rfl) ⟨1814541, by rfl⟩ : syracuseStep 4838777 = 3629083) B3629083
theorem B26170877 : Blo 1433536 26170877 := bstep (se 3 (by rfl) ⟨4907039, by rfl⟩ : syracuseStep 26170877 = 9814079) B9814079
theorem B20691139 : Blo 1433536 20691139 := bstep (se 1 (by rfl) ⟨15518354, by rfl⟩ : syracuseStep 20691139 = 31036709) B31036709
theorem B10893689 : Blo 1433536 10893689 := bstep (se 2 (by rfl) ⟨4085133, by rfl⟩ : syracuseStep 10893689 = 8170267) B8170267
theorem B8722847 : Blo 1433536 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B8723483 : Blo 1433536 8723483 := bstep (se 1 (by rfl) ⟨6542612, by rfl⟩ : syracuseStep 8723483 = 13085225) B13085225
theorem B5447209 : Blo 1433536 5447209 := bstep (se 2 (by rfl) ⟨2042703, by rfl⟩ : syracuseStep 5447209 = 4085407) B4085407
theorem B6299495 : Blo 1433536 6299495 := bstep (se 1 (by rfl) ⟨4724621, by rfl⟩ : syracuseStep 6299495 = 9449243) B9449243
theorem B1433759 : Blo 1433536 1433759 := bstep (se 1 (by rfl) ⟨1075319, by rfl⟩ : syracuseStep 1433759 = 2150639) B2150639
theorem B1433823 : Blo 1433536 1433823 := bstep (se 1 (by rfl) ⟨1075367, by rfl⟩ : syracuseStep 1433823 = 2150735) B2150735
theorem B1433919 : Blo 1433536 1433919 := bstep (se 1 (by rfl) ⟨1075439, by rfl⟩ : syracuseStep 1433919 = 2150879) B2150879
theorem B1614271 : Blo 1433536 1614271 := bstep (se 1 (by rfl) ⟨1210703, by rfl⟩ : syracuseStep 1614271 = 2421407) B2421407
theorem B3229055 : Blo 1433536 3229055 := bstep (se 1 (by rfl) ⟨2421791, by rfl⟩ : syracuseStep 3229055 = 4843583) B4843583
theorem B18376541 : Blo 1433536 18376541 := bstep (se 3 (by rfl) ⟨3445601, by rfl⟩ : syracuseStep 18376541 = 6891203) B6891203
theorem B2721919 : Blo 1433536 2721919 := bstep (se 1 (by rfl) ⟨2041439, by rfl⟩ : syracuseStep 2721919 = 4082879) B4082879
theorem B23260925 : Blo 1433536 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B2420489 : Blo 1433536 2420489 := bstep (se 2 (by rfl) ⟨907683, by rfl⟩ : syracuseStep 2420489 = 1815367) B1815367
theorem B2420975 : Blo 1433536 2420975 := bstep (se 1 (by rfl) ⟨1815731, by rfl⟩ : syracuseStep 2420975 = 3631463) B3631463
theorem B7262459 : Blo 1433536 7262459 := bstep (se 1 (by rfl) ⟨5446844, by rfl⟩ : syracuseStep 7262459 = 10893689) B10893689
theorem B3633569 : Blo 1433536 3633569 := bstep (se 2 (by rfl) ⟨1362588, by rfl⟩ : syracuseStep 3633569 = 2725177) B2725177
theorem B8171999 : Blo 1433536 8171999 := bstep (se 1 (by rfl) ⟨6128999, by rfl⟩ : syracuseStep 8171999 = 12257999) B12257999
theorem B11350633 : Blo 1433536 11350633 := bstep (se 2 (by rfl) ⟨4256487, by rfl⟩ : syracuseStep 11350633 = 8512975) B8512975
theorem B7262945 : Blo 1433536 7262945 := bstep (se 2 (by rfl) ⟨2723604, by rfl⟩ : syracuseStep 7262945 = 5447209) B5447209
theorem B5518439 : Blo 1433536 5518439 := bstep (se 1 (by rfl) ⟨4138829, by rfl⟩ : syracuseStep 5518439 = 8277659) B8277659
theorem B4199663 : Blo 1433536 4199663 := bstep (se 1 (by rfl) ⟨3149747, by rfl⟩ : syracuseStep 4199663 = 6299495) B6299495
theorem B4838831 : Blo 1433536 4838831 := bstep (se 1 (by rfl) ⟨3629123, by rfl⟩ : syracuseStep 4838831 = 7258247) B7258247
theorem B1816015 : Blo 1433536 1816015 := bstep (se 1 (by rfl) ⟨1362011, by rfl⟩ : syracuseStep 1816015 = 2724023) B2724023
theorem B27588185 : Blo 1433536 27588185 := bstep (se 2 (by rfl) ⟨10345569, by rfl⟩ : syracuseStep 27588185 = 20691139) B20691139
theorem B2422399 : Blo 1433536 2422399 := bstep (se 1 (by rfl) ⟨1816799, by rfl⟩ : syracuseStep 2422399 = 3633599) B3633599
theorem B4839209 : Blo 1433536 4839209 := bstep (se 2 (by rfl) ⟨1814703, by rfl⟩ : syracuseStep 4839209 = 3629407) B3629407
theorem B24525017 : Blo 1433536 24525017 := bstep (se 2 (by rfl) ⟨9196881, by rfl⟩ : syracuseStep 24525017 = 18393763) B18393763
theorem B3225851 : Blo 1433536 3225851 := bstep (se 1 (by rfl) ⟨2419388, by rfl⟩ : syracuseStep 3225851 = 4838777) B4838777
theorem B12261689 : Blo 1433536 12261689 := bstep (se 2 (by rfl) ⟨4598133, by rfl⟩ : syracuseStep 12261689 = 9196267) B9196267
theorem B17447251 : Blo 1433536 17447251 := bstep (se 1 (by rfl) ⟨13085438, by rfl⟩ : syracuseStep 17447251 = 26170877) B26170877
theorem B3447161 : Blo 1433536 3447161 := bstep (se 2 (by rfl) ⟨1292685, by rfl⟩ : syracuseStep 3447161 = 2585371) B2585371
theorem B7265051 : Blo 1433536 7265051 := bstep (se 1 (by rfl) ⟨5448788, by rfl⟩ : syracuseStep 7265051 = 10897577) B10897577
theorem B4840289 : Blo 1433536 4840289 := bstep (se 2 (by rfl) ⟨1815108, by rfl⟩ : syracuseStep 4840289 = 3630217) B3630217
theorem B151108537 : Blo 1433536 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B268704935 : Blo 1433536 268704935 := bstep (se 1 (by rfl) ⟨201528701, by rfl⟩ : syracuseStep 268704935 = 403057403) B403057403
theorem B10886399 : Blo 1433536 10886399 := bstep (se 1 (by rfl) ⟨8164799, by rfl⟩ : syracuseStep 10886399 = 16329599) B16329599
theorem B5815655 : Blo 1433536 5815655 := bstep (se 1 (by rfl) ⟨4361741, by rfl⟩ : syracuseStep 5815655 = 8723483) B8723483
theorem B8166851 : Blo 1433536 8166851 := bstep (se 1 (by rfl) ⟨6125138, by rfl⟩ : syracuseStep 8166851 = 12250277) B12250277
theorem B3227561 : Blo 1433536 3227561 := bstep (se 2 (by rfl) ⟨1210335, by rfl⟩ : syracuseStep 3227561 = 2420671) B2420671
theorem B1613983 : Blo 1433536 1613983 := bstep (se 1 (by rfl) ⟨1210487, by rfl⟩ : syracuseStep 1613983 = 2420975) B2420975
theorem B4841639 : Blo 1433536 4841639 := bstep (se 1 (by rfl) ⟨3631229, by rfl⟩ : syracuseStep 4841639 = 7262459) B7262459
theorem B3629225 : Blo 1433536 3629225 := bstep (se 2 (by rfl) ⟨1360959, by rfl⟩ : syracuseStep 3629225 = 2721919) B2721919
theorem B5447999 : Blo 1433536 5447999 := bstep (se 1 (by rfl) ⟨4085999, by rfl⟩ : syracuseStep 5447999 = 8171999) B8171999
theorem B4841963 : Blo 1433536 4841963 := bstep (se 1 (by rfl) ⟨3631472, by rfl⟩ : syracuseStep 4841963 = 7262945) B7262945
theorem B3678959 : Blo 1433536 3678959 := bstep (se 1 (by rfl) ⟨2759219, by rfl⟩ : syracuseStep 3678959 = 5518439) B5518439
theorem B18392123 : Blo 1433536 18392123 := bstep (se 1 (by rfl) ⟨13794092, by rfl⟩ : syracuseStep 18392123 = 27588185) B27588185
theorem B4843367 : Blo 1433536 4843367 := bstep (se 1 (by rfl) ⟨3632525, by rfl⟩ : syracuseStep 4843367 = 7265051) B7265051
theorem B179136623 : Blo 1433536 179136623 := bstep (se 1 (by rfl) ⟨134352467, by rfl⟩ : syracuseStep 179136623 = 268704935) B268704935
theorem B3229865 : Blo 1433536 3229865 := bstep (se 2 (by rfl) ⟨1211199, by rfl⟩ : syracuseStep 3229865 = 2422399) B2422399
theorem B3877103 : Blo 1433536 3877103 := bstep (se 1 (by rfl) ⟨2907827, by rfl⟩ : syracuseStep 3877103 = 5815655) B5815655
theorem B15134177 : Blo 1433536 15134177 := bstep (se 2 (by rfl) ⟨5675316, by rfl⟩ : syracuseStep 15134177 = 11350633) B11350633
theorem B12251027 : Blo 1433536 12251027 := bstep (se 1 (by rfl) ⟨9188270, by rfl⟩ : syracuseStep 12251027 = 18376541) B18376541
theorem B201478049 : Blo 1433536 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B2150567 : Blo 1433536 2150567 := bstep (se 1 (by rfl) ⟨1612925, by rfl⟩ : syracuseStep 2150567 = 3225851) B3225851
theorem B2298107 : Blo 1433536 2298107 := bstep (se 1 (by rfl) ⟨1723580, by rfl⟩ : syracuseStep 2298107 = 3447161) B3447161
theorem B2421353 : Blo 1433536 2421353 := bstep (se 2 (by rfl) ⟨908007, by rfl⟩ : syracuseStep 2421353 = 1816015) B1816015
theorem B5444567 : Blo 1433536 5444567 := bstep (se 1 (by rfl) ⟨4083425, by rfl⟩ : syracuseStep 5444567 = 8166851) B8166851
theorem B2151707 : Blo 1433536 2151707 := bstep (se 1 (by rfl) ⟨1613780, by rfl⟩ : syracuseStep 2151707 = 3227561) B3227561
theorem B2422379 : Blo 1433536 2422379 := bstep (se 1 (by rfl) ⟨1816784, by rfl⟩ : syracuseStep 2422379 = 3633569) B3633569
theorem B23263001 : Blo 1433536 23263001 := bstep (se 2 (by rfl) ⟨8723625, by rfl⟩ : syracuseStep 23263001 = 17447251) B17447251
theorem B2152361 : Blo 1433536 2152361 := bstep (se 2 (by rfl) ⟨807135, by rfl⟩ : syracuseStep 2152361 = 1614271) B1614271
theorem B2799775 : Blo 1433536 2799775 := bstep (se 1 (by rfl) ⟨2099831, by rfl⟩ : syracuseStep 2799775 = 4199663) B4199663
theorem B2152703 : Blo 1433536 2152703 := bstep (se 1 (by rfl) ⟨1614527, by rfl⟩ : syracuseStep 2152703 = 3229055) B3229055
theorem B3225887 : Blo 1433536 3225887 := bstep (se 1 (by rfl) ⟨2419415, by rfl⟩ : syracuseStep 3225887 = 4838831) B4838831
theorem B3226139 : Blo 1433536 3226139 := bstep (se 1 (by rfl) ⟨2419604, by rfl⟩ : syracuseStep 3226139 = 4839209) B4839209
theorem B16350011 : Blo 1433536 16350011 := bstep (se 1 (by rfl) ⟨12262508, by rfl⟩ : syracuseStep 16350011 = 24525017) B24525017
theorem B8174459 : Blo 1433536 8174459 := bstep (se 1 (by rfl) ⟨6130844, by rfl⟩ : syracuseStep 8174459 = 12261689) B12261689
theorem B3226859 : Blo 1433536 3226859 := bstep (se 1 (by rfl) ⟨2420144, by rfl⟩ : syracuseStep 3226859 = 4840289) B4840289
theorem B7257599 : Blo 1433536 7257599 := bstep (se 1 (by rfl) ⟨5443199, by rfl⟩ : syracuseStep 7257599 = 10886399) B10886399
theorem B15507283 : Blo 1433536 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B1613659 : Blo 1433536 1613659 := bstep (se 1 (by rfl) ⟨1210244, by rfl⟩ : syracuseStep 1613659 = 2420489) B2420489
theorem B1433711 : Blo 1433536 1433711 := bstep (se 1 (by rfl) ⟨1075283, by rfl⟩ : syracuseStep 1433711 = 2150567) B2150567
theorem B3227759 : Blo 1433536 3227759 := bstep (se 1 (by rfl) ⟨2420819, by rfl⟩ : syracuseStep 3227759 = 4841639) B4841639
theorem B1532071 : Blo 1433536 1532071 := bstep (se 1 (by rfl) ⟨1149053, by rfl⟩ : syracuseStep 1532071 = 2298107) B2298107
theorem B3227975 : Blo 1433536 3227975 := bstep (se 1 (by rfl) ⟨2420981, by rfl⟩ : syracuseStep 3227975 = 4841963) B4841963
theorem B1614235 : Blo 1433536 1614235 := bstep (se 1 (by rfl) ⟨1210676, by rfl⟩ : syracuseStep 1614235 = 2421353) B2421353
theorem B10338941 : Blo 1433536 10338941 := bstep (se 3 (by rfl) ⟨1938551, by rfl⟩ : syracuseStep 10338941 = 3877103) B3877103
theorem B3629711 : Blo 1433536 3629711 := bstep (se 1 (by rfl) ⟨2722283, by rfl⟩ : syracuseStep 3629711 = 5444567) B5444567
theorem B1434471 : Blo 1433536 1434471 := bstep (se 1 (by rfl) ⟨1075853, by rfl⟩ : syracuseStep 1434471 = 2151707) B2151707
theorem B1614919 : Blo 1433536 1614919 := bstep (se 1 (by rfl) ⟨1211189, by rfl⟩ : syracuseStep 1614919 = 2422379) B2422379
theorem B15508667 : Blo 1433536 15508667 := bstep (se 1 (by rfl) ⟨11631500, by rfl⟩ : syracuseStep 15508667 = 23263001) B23263001
theorem B3228911 : Blo 1433536 3228911 := bstep (se 1 (by rfl) ⟨2421683, by rfl⟩ : syracuseStep 3228911 = 4843367) B4843367
theorem B1434907 : Blo 1433536 1434907 := bstep (se 1 (by rfl) ⟨1076180, by rfl⟩ : syracuseStep 1434907 = 2152361) B2152361
theorem B119424415 : Blo 1433536 119424415 := bstep (se 1 (by rfl) ⟨89568311, by rfl⟩ : syracuseStep 119424415 = 179136623) B179136623
theorem B1435135 : Blo 1433536 1435135 := bstep (se 1 (by rfl) ⟨1076351, by rfl⟩ : syracuseStep 1435135 = 2152703) B2152703
theorem B5449639 : Blo 1433536 5449639 := bstep (se 1 (by rfl) ⟨4087229, by rfl⟩ : syracuseStep 5449639 = 8174459) B8174459
theorem B134318699 : Blo 1433536 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B2419483 : Blo 1433536 2419483 := bstep (se 1 (by rfl) ⟨1814612, by rfl⟩ : syracuseStep 2419483 = 3629225) B3629225
theorem B3631999 : Blo 1433536 3631999 := bstep (se 1 (by rfl) ⟨2723999, by rfl⟩ : syracuseStep 3631999 = 5447999) B5447999
theorem B2150591 : Blo 1433536 2150591 := bstep (se 1 (by rfl) ⟨1612943, by rfl⟩ : syracuseStep 2150591 = 3225887) B3225887
theorem B2150759 : Blo 1433536 2150759 := bstep (se 1 (by rfl) ⟨1613069, by rfl⟩ : syracuseStep 2150759 = 3226139) B3226139
theorem B10900007 : Blo 1433536 10900007 := bstep (se 1 (by rfl) ⟨8175005, by rfl⟩ : syracuseStep 10900007 = 16350011) B16350011
theorem B9810557 : Blo 1433536 9810557 := bstep (se 3 (by rfl) ⟨1839479, by rfl⟩ : syracuseStep 9810557 = 3678959) B3678959
theorem B2151239 : Blo 1433536 2151239 := bstep (se 1 (by rfl) ⟨1613429, by rfl⟩ : syracuseStep 2151239 = 3226859) B3226859
theorem B10089451 : Blo 1433536 10089451 := bstep (se 1 (by rfl) ⟨7567088, by rfl⟩ : syracuseStep 10089451 = 15134177) B15134177
theorem B4838399 : Blo 1433536 4838399 := bstep (se 1 (by rfl) ⟨3628799, by rfl⟩ : syracuseStep 4838399 = 7257599) B7257599
theorem B2151545 : Blo 1433536 2151545 := bstep (se 2 (by rfl) ⟨806829, by rfl⟩ : syracuseStep 2151545 = 1613659) B1613659
theorem B2151977 : Blo 1433536 2151977 := bstep (se 2 (by rfl) ⟨806991, by rfl⟩ : syracuseStep 2151977 = 1613983) B1613983
theorem B3733033 : Blo 1433536 3733033 := bstep (se 2 (by rfl) ⟨1399887, by rfl⟩ : syracuseStep 3733033 = 2799775) B2799775
theorem B12261415 : Blo 1433536 12261415 := bstep (se 1 (by rfl) ⟨9196061, by rfl⟩ : syracuseStep 12261415 = 18392123) B18392123
theorem B2153243 : Blo 1433536 2153243 := bstep (se 1 (by rfl) ⟨1614932, by rfl⟩ : syracuseStep 2153243 = 3229865) B3229865
theorem B20676377 : Blo 1433536 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B8167351 : Blo 1433536 8167351 := bstep (se 1 (by rfl) ⟨6125513, by rfl⟩ : syracuseStep 8167351 = 12251027) B12251027
theorem B1433727 : Blo 1433536 1433727 := bstep (se 1 (by rfl) ⟨1075295, by rfl⟩ : syracuseStep 1433727 = 2150591) B2150591
theorem B1433839 : Blo 1433536 1433839 := bstep (se 1 (by rfl) ⟨1075379, by rfl⟩ : syracuseStep 1433839 = 2150759) B2150759
theorem B7266671 : Blo 1433536 7266671 := bstep (se 1 (by rfl) ⟨5450003, by rfl⟩ : syracuseStep 7266671 = 10900007) B10900007
theorem B1434159 : Blo 1433536 1434159 := bstep (se 1 (by rfl) ⟨1075619, by rfl⟩ : syracuseStep 1434159 = 2151239) B2151239
theorem B1434363 : Blo 1433536 1434363 := bstep (se 1 (by rfl) ⟨1075772, by rfl⟩ : syracuseStep 1434363 = 2151545) B2151545
theorem B10339111 : Blo 1433536 10339111 := bstep (se 1 (by rfl) ⟨7754333, by rfl⟩ : syracuseStep 10339111 = 15508667) B15508667
theorem B1434651 : Blo 1433536 1434651 := bstep (se 1 (by rfl) ⟨1075988, by rfl⟩ : syracuseStep 1434651 = 2151977) B2151977
theorem B4842665 : Blo 1433536 4842665 := bstep (se 2 (by rfl) ⟨1815999, by rfl⟩ : syracuseStep 4842665 = 3631999) B3631999
theorem B1435495 : Blo 1433536 1435495 := bstep (se 1 (by rfl) ⟨1076621, by rfl⟩ : syracuseStep 1435495 = 2153243) B2153243
theorem B10889801 : Blo 1433536 10889801 := bstep (se 2 (by rfl) ⟨4083675, by rfl⟩ : syracuseStep 10889801 = 8167351) B8167351
theorem B2042761 : Blo 1433536 2042761 := bstep (se 2 (by rfl) ⟨766035, by rfl⟩ : syracuseStep 2042761 = 1532071) B1532071
theorem B6540371 : Blo 1433536 6540371 := bstep (se 1 (by rfl) ⟨4905278, by rfl⟩ : syracuseStep 6540371 = 9810557) B9810557
theorem B6892627 : Blo 1433536 6892627 := bstep (se 1 (by rfl) ⟨5169470, by rfl⟩ : syracuseStep 6892627 = 10338941) B10338941
theorem B2419807 : Blo 1433536 2419807 := bstep (se 1 (by rfl) ⟨1814855, by rfl⟩ : syracuseStep 2419807 = 3629711) B3629711
theorem B159232553 : Blo 1433536 159232553 := bstep (se 2 (by rfl) ⟨59712207, by rfl⟩ : syracuseStep 159232553 = 119424415) B119424415
theorem B4977377 : Blo 1433536 4977377 := bstep (se 2 (by rfl) ⟨1866516, by rfl⟩ : syracuseStep 4977377 = 3733033) B3733033
theorem B13784251 : Blo 1433536 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B53810405 : Blo 1433536 53810405 := bstep (se 4 (by rfl) ⟨5044725, by rfl⟩ : syracuseStep 53810405 = 10089451) B10089451
theorem B16348553 : Blo 1433536 16348553 := bstep (se 2 (by rfl) ⟨6130707, by rfl⟩ : syracuseStep 16348553 = 12261415) B12261415
theorem B2151839 : Blo 1433536 2151839 := bstep (se 1 (by rfl) ⟨1613879, by rfl⟩ : syracuseStep 2151839 = 3227759) B3227759
theorem B2151983 : Blo 1433536 2151983 := bstep (se 1 (by rfl) ⟨1613987, by rfl⟩ : syracuseStep 2151983 = 3227975) B3227975
theorem B2152313 : Blo 1433536 2152313 := bstep (se 2 (by rfl) ⟨807117, by rfl⟩ : syracuseStep 2152313 = 1614235) B1614235
theorem B3225599 : Blo 1433536 3225599 := bstep (se 1 (by rfl) ⟨2419199, by rfl⟩ : syracuseStep 3225599 = 4838399) B4838399
theorem B2152607 : Blo 1433536 2152607 := bstep (se 1 (by rfl) ⟨1614455, by rfl⟩ : syracuseStep 2152607 = 3228911) B3228911
theorem B3225977 : Blo 1433536 3225977 := bstep (se 2 (by rfl) ⟨1209741, by rfl⟩ : syracuseStep 3225977 = 2419483) B2419483
theorem B2153225 : Blo 1433536 2153225 := bstep (se 2 (by rfl) ⟨807459, by rfl⟩ : syracuseStep 2153225 = 1614919) B1614919
theorem B89545799 : Blo 1433536 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B7266185 : Blo 1433536 7266185 := bstep (se 2 (by rfl) ⟨2724819, by rfl⟩ : syracuseStep 7266185 = 5449639) B5449639
theorem B3318251 : Blo 1433536 3318251 := bstep (se 1 (by rfl) ⟨2488688, by rfl⟩ : syracuseStep 3318251 = 4977377) B4977377
theorem B3228443 : Blo 1433536 3228443 := bstep (se 1 (by rfl) ⟨2421332, by rfl⟩ : syracuseStep 3228443 = 4842665) B4842665
theorem B35873603 : Blo 1433536 35873603 := bstep (se 1 (by rfl) ⟨26905202, by rfl⟩ : syracuseStep 35873603 = 53810405) B53810405
theorem B1434559 : Blo 1433536 1434559 := bstep (se 1 (by rfl) ⟨1075919, by rfl⟩ : syracuseStep 1434559 = 2151839) B2151839
theorem B1434655 : Blo 1433536 1434655 := bstep (se 1 (by rfl) ⟨1075991, by rfl⟩ : syracuseStep 1434655 = 2151983) B2151983
theorem B1434875 : Blo 1433536 1434875 := bstep (se 1 (by rfl) ⟨1076156, by rfl⟩ : syracuseStep 1434875 = 2152313) B2152313
theorem B1435071 : Blo 1433536 1435071 := bstep (se 1 (by rfl) ⟨1076303, by rfl⟩ : syracuseStep 1435071 = 2152607) B2152607
theorem B7259867 : Blo 1433536 7259867 := bstep (se 1 (by rfl) ⟨5444900, by rfl⟩ : syracuseStep 7259867 = 10889801) B10889801
theorem B1435483 : Blo 1433536 1435483 := bstep (se 1 (by rfl) ⟨1076612, by rfl⟩ : syracuseStep 1435483 = 2153225) B2153225
theorem B59697199 : Blo 1433536 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B4360247 : Blo 1433536 4360247 := bstep (se 1 (by rfl) ⟨3270185, by rfl⟩ : syracuseStep 4360247 = 6540371) B6540371
theorem B4844123 : Blo 1433536 4844123 := bstep (se 1 (by rfl) ⟨3633092, by rfl⟩ : syracuseStep 4844123 = 7266185) B7266185
theorem B4844447 : Blo 1433536 4844447 := bstep (se 1 (by rfl) ⟨3633335, by rfl⟩ : syracuseStep 4844447 = 7266671) B7266671
theorem B106155035 : Blo 1433536 106155035 := bstep (se 1 (by rfl) ⟨79616276, by rfl⟩ : syracuseStep 106155035 = 159232553) B159232553
theorem B10899035 : Blo 1433536 10899035 := bstep (se 1 (by rfl) ⟨8174276, by rfl⟩ : syracuseStep 10899035 = 16348553) B16348553
theorem B2723681 : Blo 1433536 2723681 := bstep (se 2 (by rfl) ⟨1021380, by rfl⟩ : syracuseStep 2723681 = 2042761) B2042761
theorem B2150399 : Blo 1433536 2150399 := bstep (se 1 (by rfl) ⟨1612799, by rfl⟩ : syracuseStep 2150399 = 3225599) B3225599
theorem B18379001 : Blo 1433536 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B2150651 : Blo 1433536 2150651 := bstep (se 1 (by rfl) ⟨1612988, by rfl⟩ : syracuseStep 2150651 = 3225977) B3225977
theorem B13785481 : Blo 1433536 13785481 := bstep (se 2 (by rfl) ⟨5169555, by rfl⟩ : syracuseStep 13785481 = 10339111) B10339111
theorem B9190169 : Blo 1433536 9190169 := bstep (se 2 (by rfl) ⟨3446313, by rfl⟩ : syracuseStep 9190169 = 6892627) B6892627
theorem B3226409 : Blo 1433536 3226409 := bstep (se 2 (by rfl) ⟨1209903, by rfl⟩ : syracuseStep 3226409 = 2419807) B2419807
theorem B1433767 : Blo 1433536 1433767 := bstep (se 1 (by rfl) ⟨1075325, by rfl⟩ : syracuseStep 1433767 = 2150651) B2150651
theorem B8848669 : Blo 1433536 8848669 := bstep (se 3 (by rfl) ⟨1659125, by rfl⟩ : syracuseStep 8848669 = 3318251) B3318251
theorem B3229415 : Blo 1433536 3229415 := bstep (se 1 (by rfl) ⟨2422061, by rfl⟩ : syracuseStep 3229415 = 4844123) B4844123
theorem B3229631 : Blo 1433536 3229631 := bstep (se 1 (by rfl) ⟨2422223, by rfl⟩ : syracuseStep 3229631 = 4844447) B4844447
theorem B79596265 : Blo 1433536 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B23915735 : Blo 1433536 23915735 := bstep (se 1 (by rfl) ⟨17936801, by rfl⟩ : syracuseStep 23915735 = 35873603) B35873603
theorem B2150939 : Blo 1433536 2150939 := bstep (se 1 (by rfl) ⟨1613204, by rfl⟩ : syracuseStep 2150939 = 3226409) B3226409
theorem B1815787 : Blo 1433536 1815787 := bstep (se 1 (by rfl) ⟨1361840, by rfl⟩ : syracuseStep 1815787 = 2723681) B2723681
theorem B12252667 : Blo 1433536 12252667 := bstep (se 1 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 12252667 = 18379001) B18379001
theorem B18380641 : Blo 1433536 18380641 := bstep (se 2 (by rfl) ⟨6892740, by rfl⟩ : syracuseStep 18380641 = 13785481) B13785481
theorem B2152295 : Blo 1433536 2152295 := bstep (se 1 (by rfl) ⟨1614221, by rfl⟩ : syracuseStep 2152295 = 3228443) B3228443
theorem B4839911 : Blo 1433536 4839911 := bstep (se 1 (by rfl) ⟨3629933, by rfl⟩ : syracuseStep 4839911 = 7259867) B7259867
theorem B2906831 : Blo 1433536 2906831 := bstep (se 1 (by rfl) ⟨2180123, by rfl⟩ : syracuseStep 2906831 = 4360247) B4360247
theorem B6126779 : Blo 1433536 6126779 := bstep (se 1 (by rfl) ⟨4595084, by rfl⟩ : syracuseStep 6126779 = 9190169) B9190169
theorem B70770023 : Blo 1433536 70770023 := bstep (se 1 (by rfl) ⟨53077517, by rfl⟩ : syracuseStep 70770023 = 106155035) B106155035
theorem B7266023 : Blo 1433536 7266023 := bstep (se 1 (by rfl) ⟨5449517, by rfl⟩ : syracuseStep 7266023 = 10899035) B10899035
theorem B1433599 : Blo 1433536 1433599 := bstep (se 1 (by rfl) ⟨1075199, by rfl⟩ : syracuseStep 1433599 = 2150399) B2150399
theorem B1433959 : Blo 1433536 1433959 := bstep (se 1 (by rfl) ⟨1075469, by rfl⟩ : syracuseStep 1433959 = 2150939) B2150939
theorem B106128353 : Blo 1433536 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B1434863 : Blo 1433536 1434863 := bstep (se 1 (by rfl) ⟨1076147, by rfl⟩ : syracuseStep 1434863 = 2152295) B2152295
theorem B11798225 : Blo 1433536 11798225 := bstep (se 2 (by rfl) ⟨4424334, by rfl⟩ : syracuseStep 11798225 = 8848669) B8848669
theorem B16336889 : Blo 1433536 16336889 := bstep (se 2 (by rfl) ⟨6126333, by rfl⟩ : syracuseStep 16336889 = 12252667) B12252667
theorem B15943823 : Blo 1433536 15943823 := bstep (se 1 (by rfl) ⟨11957867, by rfl⟩ : syracuseStep 15943823 = 23915735) B23915735
theorem B47180015 : Blo 1433536 47180015 := bstep (se 1 (by rfl) ⟨35385011, by rfl⟩ : syracuseStep 47180015 = 70770023) B70770023
theorem B4844015 : Blo 1433536 4844015 := bstep (se 1 (by rfl) ⟨3633011, by rfl⟩ : syracuseStep 4844015 = 7266023) B7266023
theorem B2421049 : Blo 1433536 2421049 := bstep (se 2 (by rfl) ⟨907893, by rfl⟩ : syracuseStep 2421049 = 1815787) B1815787
theorem B1937887 : Blo 1433536 1937887 := bstep (se 1 (by rfl) ⟨1453415, by rfl⟩ : syracuseStep 1937887 = 2906831) B2906831
theorem B4084519 : Blo 1433536 4084519 := bstep (se 1 (by rfl) ⟨3063389, by rfl⟩ : syracuseStep 4084519 = 6126779) B6126779
theorem B24507521 : Blo 1433536 24507521 := bstep (se 2 (by rfl) ⟨9190320, by rfl⟩ : syracuseStep 24507521 = 18380641) B18380641
theorem B2152943 : Blo 1433536 2152943 := bstep (se 1 (by rfl) ⟨1614707, by rfl⟩ : syracuseStep 2152943 = 3229415) B3229415
theorem B2153087 : Blo 1433536 2153087 := bstep (se 1 (by rfl) ⟨1614815, by rfl⟩ : syracuseStep 2153087 = 3229631) B3229631
theorem B3226607 : Blo 1433536 3226607 := bstep (se 1 (by rfl) ⟨2419955, by rfl⟩ : syracuseStep 3226607 = 4839911) B4839911
theorem B3228065 : Blo 1433536 3228065 := bstep (se 2 (by rfl) ⟨1210524, by rfl⟩ : syracuseStep 3228065 = 2421049) B2421049
theorem B7865483 : Blo 1433536 7865483 := bstep (se 1 (by rfl) ⟨5899112, by rfl⟩ : syracuseStep 7865483 = 11798225) B11798225
theorem B3229343 : Blo 1433536 3229343 := bstep (se 1 (by rfl) ⟨2422007, by rfl⟩ : syracuseStep 3229343 = 4844015) B4844015
theorem B1435295 : Blo 1433536 1435295 := bstep (se 1 (by rfl) ⟨1076471, by rfl⟩ : syracuseStep 1435295 = 2152943) B2152943
theorem B1435391 : Blo 1433536 1435391 := bstep (se 1 (by rfl) ⟨1076543, by rfl⟩ : syracuseStep 1435391 = 2153087) B2153087
theorem B16338347 : Blo 1433536 16338347 := bstep (se 1 (by rfl) ⟨12253760, by rfl⟩ : syracuseStep 16338347 = 24507521) B24507521
theorem B10891259 : Blo 1433536 10891259 := bstep (se 1 (by rfl) ⟨8168444, by rfl⟩ : syracuseStep 10891259 = 16336889) B16336889
theorem B10629215 : Blo 1433536 10629215 := bstep (se 1 (by rfl) ⟨7971911, by rfl⟩ : syracuseStep 10629215 = 15943823) B15943823
theorem B31453343 : Blo 1433536 31453343 := bstep (se 1 (by rfl) ⟨23590007, by rfl⟩ : syracuseStep 31453343 = 47180015) B47180015
theorem B2151071 : Blo 1433536 2151071 := bstep (se 1 (by rfl) ⟨1613303, by rfl⟩ : syracuseStep 2151071 = 3226607) B3226607
theorem B10335397 : Blo 1433536 10335397 := bstep (se 4 (by rfl) ⟨968943, by rfl⟩ : syracuseStep 10335397 = 1937887) B1937887
theorem B5446025 : Blo 1433536 5446025 := bstep (se 2 (by rfl) ⟨2042259, by rfl⟩ : syracuseStep 5446025 = 4084519) B4084519
theorem B283008941 : Blo 1433536 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B7086143 : Blo 1433536 7086143 := bstep (se 1 (by rfl) ⟨5314607, by rfl⟩ : syracuseStep 7086143 = 10629215) B10629215
theorem B1434047 : Blo 1433536 1434047 := bstep (se 1 (by rfl) ⟨1075535, by rfl⟩ : syracuseStep 1434047 = 2151071) B2151071
theorem B13780529 : Blo 1433536 13780529 := bstep (se 2 (by rfl) ⟨5167698, by rfl⟩ : syracuseStep 13780529 = 10335397) B10335397
theorem B3630683 : Blo 1433536 3630683 := bstep (se 1 (by rfl) ⟨2723012, by rfl⟩ : syracuseStep 3630683 = 5446025) B5446025
theorem B188672627 : Blo 1433536 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B7260839 : Blo 1433536 7260839 := bstep (se 1 (by rfl) ⟨5445629, by rfl⟩ : syracuseStep 7260839 = 10891259) B10891259
theorem B20974621 : Blo 1433536 20974621 := bstep (se 3 (by rfl) ⟨3932741, by rfl⟩ : syracuseStep 20974621 = 7865483) B7865483
theorem B10892231 : Blo 1433536 10892231 := bstep (se 1 (by rfl) ⟨8169173, by rfl⟩ : syracuseStep 10892231 = 16338347) B16338347
theorem B20968895 : Blo 1433536 20968895 := bstep (se 1 (by rfl) ⟨15726671, by rfl⟩ : syracuseStep 20968895 = 31453343) B31453343
theorem B2152043 : Blo 1433536 2152043 := bstep (se 1 (by rfl) ⟨1614032, by rfl⟩ : syracuseStep 2152043 = 3228065) B3228065
theorem B2152895 : Blo 1433536 2152895 := bstep (se 1 (by rfl) ⟨1614671, by rfl⟩ : syracuseStep 2152895 = 3229343) B3229343
theorem B1434695 : Blo 1433536 1434695 := bstep (se 1 (by rfl) ⟨1076021, by rfl⟩ : syracuseStep 1434695 = 2152043) B2152043
theorem B1435263 : Blo 1433536 1435263 := bstep (se 1 (by rfl) ⟨1076447, by rfl⟩ : syracuseStep 1435263 = 2152895) B2152895
theorem B125781751 : Blo 1433536 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B7261487 : Blo 1433536 7261487 := bstep (se 1 (by rfl) ⟨5446115, by rfl⟩ : syracuseStep 7261487 = 10892231) B10892231
theorem B13979263 : Blo 1433536 13979263 := bstep (se 1 (by rfl) ⟨10484447, by rfl⟩ : syracuseStep 13979263 = 20968895) B20968895
theorem B9187019 : Blo 1433536 9187019 := bstep (se 1 (by rfl) ⟨6890264, by rfl⟩ : syracuseStep 9187019 = 13780529) B13780529
theorem B2420455 : Blo 1433536 2420455 := bstep (se 1 (by rfl) ⟨1815341, by rfl⟩ : syracuseStep 2420455 = 3630683) B3630683
theorem B4724095 : Blo 1433536 4724095 := bstep (se 1 (by rfl) ⟨3543071, by rfl⟩ : syracuseStep 4724095 = 7086143) B7086143
theorem B27966161 : Blo 1433536 27966161 := bstep (se 2 (by rfl) ⟨10487310, by rfl⟩ : syracuseStep 27966161 = 20974621) B20974621
theorem B4840559 : Blo 1433536 4840559 := bstep (se 1 (by rfl) ⟨3630419, by rfl⟩ : syracuseStep 4840559 = 7260839) B7260839
theorem B18639017 : Blo 1433536 18639017 := bstep (se 2 (by rfl) ⟨6989631, by rfl⟩ : syracuseStep 18639017 = 13979263) B13979263
theorem B167709001 : Blo 1433536 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B6124679 : Blo 1433536 6124679 := bstep (se 1 (by rfl) ⟨4593509, by rfl⟩ : syracuseStep 6124679 = 9187019) B9187019
theorem B18644107 : Blo 1433536 18644107 := bstep (se 1 (by rfl) ⟨13983080, by rfl⟩ : syracuseStep 18644107 = 27966161) B27966161
theorem B6298793 : Blo 1433536 6298793 := bstep (se 2 (by rfl) ⟨2362047, by rfl⟩ : syracuseStep 6298793 = 4724095) B4724095
theorem B3227039 : Blo 1433536 3227039 := bstep (se 1 (by rfl) ⟨2420279, by rfl⟩ : syracuseStep 3227039 = 4840559) B4840559
theorem B4840991 : Blo 1433536 4840991 := bstep (se 1 (by rfl) ⟨3630743, by rfl⟩ : syracuseStep 4840991 = 7261487) B7261487
theorem B3227273 : Blo 1433536 3227273 := bstep (se 2 (by rfl) ⟨1210227, by rfl⟩ : syracuseStep 3227273 = 2420455) B2420455
theorem B223612001 : Blo 1433536 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B4083119 : Blo 1433536 4083119 := bstep (se 1 (by rfl) ⟨3062339, by rfl⟩ : syracuseStep 4083119 = 6124679) B6124679
theorem B24858809 : Blo 1433536 24858809 := bstep (se 2 (by rfl) ⟨9322053, by rfl⟩ : syracuseStep 24858809 = 18644107) B18644107
theorem B4199195 : Blo 1433536 4199195 := bstep (se 1 (by rfl) ⟨3149396, by rfl⟩ : syracuseStep 4199195 = 6298793) B6298793
theorem B2151359 : Blo 1433536 2151359 := bstep (se 1 (by rfl) ⟨1613519, by rfl⟩ : syracuseStep 2151359 = 3227039) B3227039
theorem B2151515 : Blo 1433536 2151515 := bstep (se 1 (by rfl) ⟨1613636, by rfl⟩ : syracuseStep 2151515 = 3227273) B3227273
theorem B12426011 : Blo 1433536 12426011 := bstep (se 1 (by rfl) ⟨9319508, by rfl⟩ : syracuseStep 12426011 = 18639017) B18639017
theorem B3227327 : Blo 1433536 3227327 := bstep (se 1 (by rfl) ⟨2420495, by rfl⟩ : syracuseStep 3227327 = 4840991) B4840991
theorem B16572539 : Blo 1433536 16572539 := bstep (se 1 (by rfl) ⟨12429404, by rfl⟩ : syracuseStep 16572539 = 24858809) B24858809
theorem B1434239 : Blo 1433536 1434239 := bstep (se 1 (by rfl) ⟨1075679, by rfl⟩ : syracuseStep 1434239 = 2151359) B2151359
theorem B1434343 : Blo 1433536 1434343 := bstep (se 1 (by rfl) ⟨1075757, by rfl⟩ : syracuseStep 1434343 = 2151515) B2151515
theorem B8284007 : Blo 1433536 8284007 := bstep (se 1 (by rfl) ⟨6213005, by rfl⟩ : syracuseStep 8284007 = 12426011) B12426011
theorem B2722079 : Blo 1433536 2722079 := bstep (se 1 (by rfl) ⟨2041559, by rfl⟩ : syracuseStep 2722079 = 4083119) B4083119
theorem B149074667 : Blo 1433536 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B2151551 : Blo 1433536 2151551 := bstep (se 1 (by rfl) ⟨1613663, by rfl⟩ : syracuseStep 2151551 = 3227327) B3227327
theorem B2799463 : Blo 1433536 2799463 := bstep (se 1 (by rfl) ⟨2099597, by rfl⟩ : syracuseStep 2799463 = 4199195) B4199195
theorem B1434367 : Blo 1433536 1434367 := bstep (se 1 (by rfl) ⟨1075775, by rfl⟩ : syracuseStep 1434367 = 2151551) B2151551
theorem B5522671 : Blo 1433536 5522671 := bstep (se 1 (by rfl) ⟨4142003, by rfl⟩ : syracuseStep 5522671 = 8284007) B8284007
theorem B1814719 : Blo 1433536 1814719 := bstep (se 1 (by rfl) ⟨1361039, by rfl⟩ : syracuseStep 1814719 = 2722079) B2722079
theorem B3732617 : Blo 1433536 3732617 := bstep (se 2 (by rfl) ⟨1399731, by rfl⟩ : syracuseStep 3732617 = 2799463) B2799463
theorem B11048359 : Blo 1433536 11048359 := bstep (se 1 (by rfl) ⟨8286269, by rfl⟩ : syracuseStep 11048359 = 16572539) B16572539
theorem B99383111 : Blo 1433536 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B14731145 : Blo 1433536 14731145 := bstep (se 2 (by rfl) ⟨5524179, by rfl⟩ : syracuseStep 14731145 = 11048359) B11048359
theorem B2419625 : Blo 1433536 2419625 := bstep (se 2 (by rfl) ⟨907359, by rfl⟩ : syracuseStep 2419625 = 1814719) B1814719
theorem B2488411 : Blo 1433536 2488411 := bstep (se 1 (by rfl) ⟨1866308, by rfl⟩ : syracuseStep 2488411 = 3732617) B3732617
theorem B66255407 : Blo 1433536 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B7363561 : Blo 1433536 7363561 := bstep (se 2 (by rfl) ⟨2761335, by rfl⟩ : syracuseStep 7363561 = 5522671) B5522671
theorem B3317881 : Blo 1433536 3317881 := bstep (se 2 (by rfl) ⟨1244205, by rfl⟩ : syracuseStep 3317881 = 2488411) B2488411
theorem B9818081 : Blo 1433536 9818081 := bstep (se 2 (by rfl) ⟨3681780, by rfl⟩ : syracuseStep 9818081 = 7363561) B7363561
theorem B9820763 : Blo 1433536 9820763 := bstep (se 1 (by rfl) ⟨7365572, by rfl⟩ : syracuseStep 9820763 = 14731145) B14731145
theorem B44170271 : Blo 1433536 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B1613083 : Blo 1433536 1613083 := bstep (se 1 (by rfl) ⟨1209812, by rfl⟩ : syracuseStep 1613083 = 2419625) B2419625
theorem B4423841 : Blo 1433536 4423841 := bstep (se 2 (by rfl) ⟨1658940, by rfl⟩ : syracuseStep 4423841 = 3317881) B3317881
theorem B6547175 : Blo 1433536 6547175 := bstep (se 1 (by rfl) ⟨4910381, by rfl⟩ : syracuseStep 6547175 = 9820763) B9820763
theorem B2150777 : Blo 1433536 2150777 := bstep (se 2 (by rfl) ⟨806541, by rfl⟩ : syracuseStep 2150777 = 1613083) B1613083
theorem B29446847 : Blo 1433536 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B6545387 : Blo 1433536 6545387 := bstep (se 1 (by rfl) ⟨4909040, by rfl⟩ : syracuseStep 6545387 = 9818081) B9818081
theorem B2949227 : Blo 1433536 2949227 := bstep (se 1 (by rfl) ⟨2211920, by rfl⟩ : syracuseStep 2949227 = 4423841) B4423841
theorem B1433851 : Blo 1433536 1433851 := bstep (se 1 (by rfl) ⟨1075388, by rfl⟩ : syracuseStep 1433851 = 2150777) B2150777
theorem B19631231 : Blo 1433536 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B17454365 : Blo 1433536 17454365 := bstep (se 3 (by rfl) ⟨3272693, by rfl⟩ : syracuseStep 17454365 = 6545387) B6545387
theorem B4364783 : Blo 1433536 4364783 := bstep (se 1 (by rfl) ⟨3273587, by rfl⟩ : syracuseStep 4364783 = 6547175) B6547175
theorem B1966151 : Blo 1433536 1966151 := bstep (se 1 (by rfl) ⟨1474613, by rfl⟩ : syracuseStep 1966151 = 2949227) B2949227
theorem B2909855 : Blo 1433536 2909855 := bstep (se 1 (by rfl) ⟨2182391, by rfl⟩ : syracuseStep 2909855 = 4364783) B4364783
theorem B11636243 : Blo 1433536 11636243 := bstep (se 1 (by rfl) ⟨8727182, by rfl⟩ : syracuseStep 11636243 = 17454365) B17454365
theorem B13087487 : Blo 1433536 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B5243069 : Blo 1433536 5243069 := bstep (se 3 (by rfl) ⟨983075, by rfl⟩ : syracuseStep 5243069 = 1966151) B1966151
theorem B8724991 : Blo 1433536 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B7759613 : Blo 1433536 7759613 := bstep (se 3 (by rfl) ⟨1454927, by rfl⟩ : syracuseStep 7759613 = 2909855) B2909855
theorem B7757495 : Blo 1433536 7757495 := bstep (se 1 (by rfl) ⟨5818121, by rfl⟩ : syracuseStep 7757495 = 11636243) B11636243
theorem B11633321 : Blo 1433536 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B5171663 : Blo 1433536 5171663 := bstep (se 1 (by rfl) ⟨3878747, by rfl⟩ : syracuseStep 5171663 = 7757495) B7757495
theorem B5173075 : Blo 1433536 5173075 := bstep (se 1 (by rfl) ⟨3879806, by rfl⟩ : syracuseStep 5173075 = 7759613) B7759613
theorem B13981517 : Blo 1433536 13981517 := bstep (se 3 (by rfl) ⟨2621534, by rfl⟩ : syracuseStep 13981517 = 5243069) B5243069
theorem B7755547 : Blo 1433536 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B9321011 : Blo 1433536 9321011 := bstep (se 1 (by rfl) ⟨6990758, by rfl⟩ : syracuseStep 9321011 = 13981517) B13981517
theorem B3447775 : Blo 1433536 3447775 := bstep (se 1 (by rfl) ⟨2585831, by rfl⟩ : syracuseStep 3447775 = 5171663) B5171663
theorem B6897433 : Blo 1433536 6897433 := bstep (se 2 (by rfl) ⟨2586537, by rfl⟩ : syracuseStep 6897433 = 5173075) B5173075
theorem B4597033 : Blo 1433536 4597033 := bstep (se 2 (by rfl) ⟨1723887, by rfl⟩ : syracuseStep 4597033 = 3447775) B3447775
theorem B10340729 : Blo 1433536 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B6214007 : Blo 1433536 6214007 := bstep (se 1 (by rfl) ⟨4660505, by rfl⟩ : syracuseStep 6214007 = 9321011) B9321011
theorem B9196577 : Blo 1433536 9196577 := bstep (se 2 (by rfl) ⟨3448716, by rfl⟩ : syracuseStep 9196577 = 6897433) B6897433
theorem B6129377 : Blo 1433536 6129377 := bstep (se 2 (by rfl) ⟨2298516, by rfl⟩ : syracuseStep 6129377 = 4597033) B4597033
theorem B6131051 : Blo 1433536 6131051 := bstep (se 1 (by rfl) ⟨4598288, by rfl⟩ : syracuseStep 6131051 = 9196577) B9196577
theorem B6893819 : Blo 1433536 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B4142671 : Blo 1433536 4142671 := bstep (se 1 (by rfl) ⟨3107003, by rfl⟩ : syracuseStep 4142671 = 6214007) B6214007
theorem B4595879 : Blo 1433536 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B22094245 : Blo 1433536 22094245 := bstep (se 4 (by rfl) ⟨2071335, by rfl⟩ : syracuseStep 22094245 = 4142671) B4142671
theorem B4086251 : Blo 1433536 4086251 := bstep (se 1 (by rfl) ⟨3064688, by rfl⟩ : syracuseStep 4086251 = 6129377) B6129377
theorem B4087367 : Blo 1433536 4087367 := bstep (se 1 (by rfl) ⟨3065525, by rfl⟩ : syracuseStep 4087367 = 6131051) B6131051
theorem B3063919 : Blo 1433536 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B29458993 : Blo 1433536 29458993 := bstep (se 2 (by rfl) ⟨11047122, by rfl⟩ : syracuseStep 29458993 = 22094245) B22094245
theorem B2724167 : Blo 1433536 2724167 := bstep (se 1 (by rfl) ⟨2043125, by rfl⟩ : syracuseStep 2724167 = 4086251) B4086251
theorem B2724911 : Blo 1433536 2724911 := bstep (se 1 (by rfl) ⟨2043683, by rfl⟩ : syracuseStep 2724911 = 4087367) B4087367
theorem B4085225 : Blo 1433536 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B1816111 : Blo 1433536 1816111 := bstep (se 1 (by rfl) ⟨1362083, by rfl⟩ : syracuseStep 1816111 = 2724167) B2724167
theorem B1816607 : Blo 1433536 1816607 := bstep (se 1 (by rfl) ⟨1362455, by rfl⟩ : syracuseStep 1816607 = 2724911) B2724911
theorem B39278657 : Blo 1433536 39278657 := bstep (se 2 (by rfl) ⟨14729496, by rfl⟩ : syracuseStep 39278657 = 29458993) B29458993
theorem B4844285 : Blo 1433536 4844285 := bstep (se 3 (by rfl) ⟨908303, by rfl⟩ : syracuseStep 4844285 = 1816607) B1816607
theorem B2723483 : Blo 1433536 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B26185771 : Blo 1433536 26185771 := bstep (se 1 (by rfl) ⟨19639328, by rfl⟩ : syracuseStep 26185771 = 39278657) B39278657
theorem B2421481 : Blo 1433536 2421481 := bstep (se 2 (by rfl) ⟨908055, by rfl⟩ : syracuseStep 2421481 = 1816111) B1816111
theorem B34914361 : Blo 1433536 34914361 := bstep (se 2 (by rfl) ⟨13092885, by rfl⟩ : syracuseStep 34914361 = 26185771) B26185771
theorem B3228641 : Blo 1433536 3228641 := bstep (se 2 (by rfl) ⟨1210740, by rfl⟩ : syracuseStep 3228641 = 2421481) B2421481
theorem B3229523 : Blo 1433536 3229523 := bstep (se 1 (by rfl) ⟨2422142, by rfl⟩ : syracuseStep 3229523 = 4844285) B4844285
theorem B7262621 : Blo 1433536 7262621 := bstep (se 3 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 7262621 = 2723483) B2723483
theorem B4841747 : Blo 1433536 4841747 := bstep (se 1 (by rfl) ⟨3631310, by rfl⟩ : syracuseStep 4841747 = 7262621) B7262621
theorem B46552481 : Blo 1433536 46552481 := bstep (se 2 (by rfl) ⟨17457180, by rfl⟩ : syracuseStep 46552481 = 34914361) B34914361
theorem B2152427 : Blo 1433536 2152427 := bstep (se 1 (by rfl) ⟨1614320, by rfl⟩ : syracuseStep 2152427 = 3228641) B3228641
theorem B2153015 : Blo 1433536 2153015 := bstep (se 1 (by rfl) ⟨1614761, by rfl⟩ : syracuseStep 2153015 = 3229523) B3229523
theorem B3227831 : Blo 1433536 3227831 := bstep (se 1 (by rfl) ⟨2420873, by rfl⟩ : syracuseStep 3227831 = 4841747) B4841747
theorem B1434951 : Blo 1433536 1434951 := bstep (se 1 (by rfl) ⟨1076213, by rfl⟩ : syracuseStep 1434951 = 2152427) B2152427
theorem B1435343 : Blo 1433536 1435343 := bstep (se 1 (by rfl) ⟨1076507, by rfl⟩ : syracuseStep 1435343 = 2153015) B2153015
theorem B31034987 : Blo 1433536 31034987 := bstep (se 1 (by rfl) ⟨23276240, by rfl⟩ : syracuseStep 31034987 = 46552481) B46552481
theorem B20689991 : Blo 1433536 20689991 := bstep (se 1 (by rfl) ⟨15517493, by rfl⟩ : syracuseStep 20689991 = 31034987) B31034987
theorem B2151887 : Blo 1433536 2151887 := bstep (se 1 (by rfl) ⟨1613915, by rfl⟩ : syracuseStep 2151887 = 3227831) B3227831
theorem B1434591 : Blo 1433536 1434591 := bstep (se 1 (by rfl) ⟨1075943, by rfl⟩ : syracuseStep 1434591 = 2151887) B2151887
theorem B13793327 : Blo 1433536 13793327 := bstep (se 1 (by rfl) ⟨10344995, by rfl⟩ : syracuseStep 13793327 = 20689991) B20689991
theorem B9195551 : Blo 1433536 9195551 := bstep (se 1 (by rfl) ⟨6896663, by rfl⟩ : syracuseStep 9195551 = 13793327) B13793327
theorem B6130367 : Blo 1433536 6130367 := bstep (se 1 (by rfl) ⟨4597775, by rfl⟩ : syracuseStep 6130367 = 9195551) B9195551
theorem B4086911 : Blo 1433536 4086911 := bstep (se 1 (by rfl) ⟨3065183, by rfl⟩ : syracuseStep 4086911 = 6130367) B6130367
theorem B2724607 : Blo 1433536 2724607 := bstep (se 1 (by rfl) ⟨2043455, by rfl⟩ : syracuseStep 2724607 = 4086911) B4086911
theorem B3632809 : Blo 1433536 3632809 := bstep (se 2 (by rfl) ⟨1362303, by rfl⟩ : syracuseStep 3632809 = 2724607) B2724607
theorem B4843745 : Blo 1433536 4843745 := bstep (se 2 (by rfl) ⟨1816404, by rfl⟩ : syracuseStep 4843745 = 3632809) B3632809
theorem B3229163 : Blo 1433536 3229163 := bstep (se 1 (by rfl) ⟨2421872, by rfl⟩ : syracuseStep 3229163 = 4843745) B4843745
theorem B2152775 : Blo 1433536 2152775 := bstep (se 1 (by rfl) ⟨1614581, by rfl⟩ : syracuseStep 2152775 = 3229163) B3229163
theorem B1435183 : Blo 1433536 1435183 := bstep (se 1 (by rfl) ⟨1076387, by rfl⟩ : syracuseStep 1435183 = 2152775) B2152775

theorem C0 (j : ℕ) (h1 : 358384 ≤ j) (h2 : j ≤ 358883) : Blo 1433536 (4 * j + 3) := by
  interval_cases j
  · exact B1433539
  · exact B1433543
  · exact B1433547
  · exact B1433551
  · exact B1433555
  · exact B1433559
  · exact B1433563
  · exact B1433567
  · exact B1433571
  · exact B1433575
  · exact B1433579
  · exact B1433583
  · exact B1433587
  · exact B1433591
  · exact B1433595
  · exact B1433599
  · exact B1433603
  · exact B1433607
  · exact B1433611
  · exact B1433615
  · exact B1433619
  · exact B1433623
  · exact B1433627
  · exact B1433631
  · exact B1433635
  · exact B1433639
  · exact B1433643
  · exact B1433647
  · exact B1433651
  · exact B1433655
  · exact B1433659
  · exact B1433663
  · exact B1433667
  · exact B1433671
  · exact B1433675
  · exact B1433679
  · exact B1433683
  · exact B1433687
  · exact B1433691
  · exact B1433695
  · exact B1433699
  · exact B1433703
  · exact B1433707
  · exact B1433711
  · exact B1433715
  · exact B1433719
  · exact B1433723
  · exact B1433727
  · exact B1433731
  · exact B1433735
  · exact B1433739
  · exact B1433743
  · exact B1433747
  · exact B1433751
  · exact B1433755
  · exact B1433759
  · exact B1433763
  · exact B1433767
  · exact B1433771
  · exact B1433775
  · exact B1433779
  · exact B1433783
  · exact B1433787
  · exact B1433791
  · exact B1433795
  · exact B1433799
  · exact B1433803
  · exact B1433807
  · exact B1433811
  · exact B1433815
  · exact B1433819
  · exact B1433823
  · exact B1433827
  · exact B1433831
  · exact B1433835
  · exact B1433839
  · exact B1433843
  · exact B1433847
  · exact B1433851
  · exact B1433855
  · exact B1433859
  · exact B1433863
  · exact B1433867
  · exact B1433871
  · exact B1433875
  · exact B1433879
  · exact B1433883
  · exact B1433887
  · exact B1433891
  · exact B1433895
  · exact B1433899
  · exact B1433903
  · exact B1433907
  · exact B1433911
  · exact B1433915
  · exact B1433919
  · exact B1433923
  · exact B1433927
  · exact B1433931
  · exact B1433935
  · exact B1433939
  · exact B1433943
  · exact B1433947
  · exact B1433951
  · exact B1433955
  · exact B1433959
  · exact B1433963
  · exact B1433967
  · exact B1433971
  · exact B1433975
  · exact B1433979
  · exact B1433983
  · exact B1433987
  · exact B1433991
  · exact B1433995
  · exact B1433999
  · exact B1434003
  · exact B1434007
  · exact B1434011
  · exact B1434015
  · exact B1434019
  · exact B1434023
  · exact B1434027
  · exact B1434031
  · exact B1434035
  · exact B1434039
  · exact B1434043
  · exact B1434047
  · exact B1434051
  · exact B1434055
  · exact B1434059
  · exact B1434063
  · exact B1434067
  · exact B1434071
  · exact B1434075
  · exact B1434079
  · exact B1434083
  · exact B1434087
  · exact B1434091
  · exact B1434095
  · exact B1434099
  · exact B1434103
  · exact B1434107
  · exact B1434111
  · exact B1434115
  · exact B1434119
  · exact B1434123
  · exact B1434127
  · exact B1434131
  · exact B1434135
  · exact B1434139
  · exact B1434143
  · exact B1434147
  · exact B1434151
  · exact B1434155
  · exact B1434159
  · exact B1434163
  · exact B1434167
  · exact B1434171
  · exact B1434175
  · exact B1434179
  · exact B1434183
  · exact B1434187
  · exact B1434191
  · exact B1434195
  · exact B1434199
  · exact B1434203
  · exact B1434207
  · exact B1434211
  · exact B1434215
  · exact B1434219
  · exact B1434223
  · exact B1434227
  · exact B1434231
  · exact B1434235
  · exact B1434239
  · exact B1434243
  · exact B1434247
  · exact B1434251
  · exact B1434255
  · exact B1434259
  · exact B1434263
  · exact B1434267
  · exact B1434271
  · exact B1434275
  · exact B1434279
  · exact B1434283
  · exact B1434287
  · exact B1434291
  · exact B1434295
  · exact B1434299
  · exact B1434303
  · exact B1434307
  · exact B1434311
  · exact B1434315
  · exact B1434319
  · exact B1434323
  · exact B1434327
  · exact B1434331
  · exact B1434335
  · exact B1434339
  · exact B1434343
  · exact B1434347
  · exact B1434351
  · exact B1434355
  · exact B1434359
  · exact B1434363
  · exact B1434367
  · exact B1434371
  · exact B1434375
  · exact B1434379
  · exact B1434383
  · exact B1434387
  · exact B1434391
  · exact B1434395
  · exact B1434399
  · exact B1434403
  · exact B1434407
  · exact B1434411
  · exact B1434415
  · exact B1434419
  · exact B1434423
  · exact B1434427
  · exact B1434431
  · exact B1434435
  · exact B1434439
  · exact B1434443
  · exact B1434447
  · exact B1434451
  · exact B1434455
  · exact B1434459
  · exact B1434463
  · exact B1434467
  · exact B1434471
  · exact B1434475
  · exact B1434479
  · exact B1434483
  · exact B1434487
  · exact B1434491
  · exact B1434495
  · exact B1434499
  · exact B1434503
  · exact B1434507
  · exact B1434511
  · exact B1434515
  · exact B1434519
  · exact B1434523
  · exact B1434527
  · exact B1434531
  · exact B1434535
  · exact B1434539
  · exact B1434543
  · exact B1434547
  · exact B1434551
  · exact B1434555
  · exact B1434559
  · exact B1434563
  · exact B1434567
  · exact B1434571
  · exact B1434575
  · exact B1434579
  · exact B1434583
  · exact B1434587
  · exact B1434591
  · exact B1434595
  · exact B1434599
  · exact B1434603
  · exact B1434607
  · exact B1434611
  · exact B1434615
  · exact B1434619
  · exact B1434623
  · exact B1434627
  · exact B1434631
  · exact B1434635
  · exact B1434639
  · exact B1434643
  · exact B1434647
  · exact B1434651
  · exact B1434655
  · exact B1434659
  · exact B1434663
  · exact B1434667
  · exact B1434671
  · exact B1434675
  · exact B1434679
  · exact B1434683
  · exact B1434687
  · exact B1434691
  · exact B1434695
  · exact B1434699
  · exact B1434703
  · exact B1434707
  · exact B1434711
  · exact B1434715
  · exact B1434719
  · exact B1434723
  · exact B1434727
  · exact B1434731
  · exact B1434735
  · exact B1434739
  · exact B1434743
  · exact B1434747
  · exact B1434751
  · exact B1434755
  · exact B1434759
  · exact B1434763
  · exact B1434767
  · exact B1434771
  · exact B1434775
  · exact B1434779
  · exact B1434783
  · exact B1434787
  · exact B1434791
  · exact B1434795
  · exact B1434799
  · exact B1434803
  · exact B1434807
  · exact B1434811
  · exact B1434815
  · exact B1434819
  · exact B1434823
  · exact B1434827
  · exact B1434831
  · exact B1434835
  · exact B1434839
  · exact B1434843
  · exact B1434847
  · exact B1434851
  · exact B1434855
  · exact B1434859
  · exact B1434863
  · exact B1434867
  · exact B1434871
  · exact B1434875
  · exact B1434879
  · exact B1434883
  · exact B1434887
  · exact B1434891
  · exact B1434895
  · exact B1434899
  · exact B1434903
  · exact B1434907
  · exact B1434911
  · exact B1434915
  · exact B1434919
  · exact B1434923
  · exact B1434927
  · exact B1434931
  · exact B1434935
  · exact B1434939
  · exact B1434943
  · exact B1434947
  · exact B1434951
  · exact B1434955
  · exact B1434959
  · exact B1434963
  · exact B1434967
  · exact B1434971
  · exact B1434975
  · exact B1434979
  · exact B1434983
  · exact B1434987
  · exact B1434991
  · exact B1434995
  · exact B1434999
  · exact B1435003
  · exact B1435007
  · exact B1435011
  · exact B1435015
  · exact B1435019
  · exact B1435023
  · exact B1435027
  · exact B1435031
  · exact B1435035
  · exact B1435039
  · exact B1435043
  · exact B1435047
  · exact B1435051
  · exact B1435055
  · exact B1435059
  · exact B1435063
  · exact B1435067
  · exact B1435071
  · exact B1435075
  · exact B1435079
  · exact B1435083
  · exact B1435087
  · exact B1435091
  · exact B1435095
  · exact B1435099
  · exact B1435103
  · exact B1435107
  · exact B1435111
  · exact B1435115
  · exact B1435119
  · exact B1435123
  · exact B1435127
  · exact B1435131
  · exact B1435135
  · exact B1435139
  · exact B1435143
  · exact B1435147
  · exact B1435151
  · exact B1435155
  · exact B1435159
  · exact B1435163
  · exact B1435167
  · exact B1435171
  · exact B1435175
  · exact B1435179
  · exact B1435183
  · exact B1435187
  · exact B1435191
  · exact B1435195
  · exact B1435199
  · exact B1435203
  · exact B1435207
  · exact B1435211
  · exact B1435215
  · exact B1435219
  · exact B1435223
  · exact B1435227
  · exact B1435231
  · exact B1435235
  · exact B1435239
  · exact B1435243
  · exact B1435247
  · exact B1435251
  · exact B1435255
  · exact B1435259
  · exact B1435263
  · exact B1435267
  · exact B1435271
  · exact B1435275
  · exact B1435279
  · exact B1435283
  · exact B1435287
  · exact B1435291
  · exact B1435295
  · exact B1435299
  · exact B1435303
  · exact B1435307
  · exact B1435311
  · exact B1435315
  · exact B1435319
  · exact B1435323
  · exact B1435327
  · exact B1435331
  · exact B1435335
  · exact B1435339
  · exact B1435343
  · exact B1435347
  · exact B1435351
  · exact B1435355
  · exact B1435359
  · exact B1435363
  · exact B1435367
  · exact B1435371
  · exact B1435375
  · exact B1435379
  · exact B1435383
  · exact B1435387
  · exact B1435391
  · exact B1435395
  · exact B1435399
  · exact B1435403
  · exact B1435407
  · exact B1435411
  · exact B1435415
  · exact B1435419
  · exact B1435423
  · exact B1435427
  · exact B1435431
  · exact B1435435
  · exact B1435439
  · exact B1435443
  · exact B1435447
  · exact B1435451
  · exact B1435455
  · exact B1435459
  · exact B1435463
  · exact B1435467
  · exact B1435471
  · exact B1435475
  · exact B1435479
  · exact B1435483
  · exact B1435487
  · exact B1435491
  · exact B1435495
  · exact B1435499
  · exact B1435503
  · exact B1435507
  · exact B1435511
  · exact B1435515
  · exact B1435519
  · exact B1435523
  · exact B1435527
  · exact B1435531
  · exact B1435535

theorem solution (m : ℕ) (hlo : 1433536 ≤ m) (hhi : m ≤ 1435536) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 358384 ≤ j := by omega
    have hj2 : j ≤ 358883 := by omega
    have hb : Blo 1433536 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
