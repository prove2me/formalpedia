-- Prove2me | solution 1 for syracuse_descends_range_1360499_1362499
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:55.848501+00:00
-- url     : https://prove2.me/submissions/bfe38edf-9622-4b0b-8393-2bd56d7f29b3

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


theorem B1531921 : Blo 1360499 1531921 := bbase (se 2 (by rfl) ⟨574470, by rfl⟩ : syracuseStep 1531921 = 1148941) (by norm_num)
theorem B1531957 : Blo 1360499 1531957 := bbase (se 5 (by rfl) ⟨71810, by rfl⟩ : syracuseStep 1531957 = 143621) (by norm_num)
theorem B3063869 : Blo 1360499 3063869 := bbase (se 3 (by rfl) ⟨574475, by rfl⟩ : syracuseStep 3063869 = 1148951) (by norm_num)
theorem B1531993 : Blo 1360499 1531993 := bbase (se 2 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 1531993 = 1148995) (by norm_num)
theorem B1532029 : Blo 1360499 1532029 := bbase (se 3 (by rfl) ⟨287255, by rfl⟩ : syracuseStep 1532029 = 574511) (by norm_num)
theorem B3063941 : Blo 1360499 3063941 := bbase (se 4 (by rfl) ⟨287244, by rfl⟩ : syracuseStep 3063941 = 574489) (by norm_num)
theorem B1532065 : Blo 1360499 1532065 := bbase (se 2 (by rfl) ⟨574524, by rfl⟩ : syracuseStep 1532065 = 1149049) (by norm_num)
theorem B1532101 : Blo 1360499 1532101 := bbase (se 4 (by rfl) ⟨143634, by rfl⟩ : syracuseStep 1532101 = 287269) (by norm_num)
theorem B3064013 : Blo 1360499 3064013 := bbase (se 3 (by rfl) ⟨574502, by rfl⟩ : syracuseStep 3064013 = 1149005) (by norm_num)
theorem B3236069 : Blo 1360499 3236069 := bbase (se 4 (by rfl) ⟨303381, by rfl⟩ : syracuseStep 3236069 = 606763) (by norm_num)
theorem B1532137 : Blo 1360499 1532137 := bbase (se 2 (by rfl) ⟨574551, by rfl⟩ : syracuseStep 1532137 = 1149103) (by norm_num)
theorem B1532173 : Blo 1360499 1532173 := bbase (se 3 (by rfl) ⟨287282, by rfl⟩ : syracuseStep 1532173 = 574565) (by norm_num)
theorem B3064085 : Blo 1360499 3064085 := bbase (se 6 (by rfl) ⟨71814, by rfl⟩ : syracuseStep 3064085 = 143629) (by norm_num)
theorem B1532209 : Blo 1360499 1532209 := bbase (se 2 (by rfl) ⟨574578, by rfl⟩ : syracuseStep 1532209 = 1149157) (by norm_num)
theorem B1532245 : Blo 1360499 1532245 := bbase (se 10 (by rfl) ⟨2244, by rfl⟩ : syracuseStep 1532245 = 4489) (by norm_num)
theorem B3064157 : Blo 1360499 3064157 := bbase (se 3 (by rfl) ⟨574529, by rfl⟩ : syracuseStep 3064157 = 1149059) (by norm_num)
theorem B10338677 : Blo 1360499 10338677 := bbase (se 5 (by rfl) ⟨484625, by rfl⟩ : syracuseStep 10338677 = 969251) (by norm_num)
theorem B1532281 : Blo 1360499 1532281 := bbase (se 2 (by rfl) ⟨574605, by rfl⟩ : syracuseStep 1532281 = 1149211) (by norm_num)
theorem B4596101 : Blo 1360499 4596101 := bbase (se 4 (by rfl) ⟨430884, by rfl⟩ : syracuseStep 4596101 = 861769) (by norm_num)
theorem B2179477 : Blo 1360499 2179477 := bbase (se 6 (by rfl) ⟨51081, by rfl⟩ : syracuseStep 2179477 = 102163) (by norm_num)
theorem B1532317 : Blo 1360499 1532317 := bbase (se 3 (by rfl) ⟨287309, by rfl⟩ : syracuseStep 1532317 = 574619) (by norm_num)
theorem B3064229 : Blo 1360499 3064229 := bbase (se 4 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 3064229 = 574543) (by norm_num)
theorem B2761133 : Blo 1360499 2761133 := bbase (se 3 (by rfl) ⟨517712, by rfl⟩ : syracuseStep 2761133 = 1035425) (by norm_num)
theorem B1532353 : Blo 1360499 1532353 := bbase (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) (by norm_num)
theorem B1532389 : Blo 1360499 1532389 := bbase (se 4 (by rfl) ⟨143661, by rfl⟩ : syracuseStep 1532389 = 287323) (by norm_num)
theorem B3064301 : Blo 1360499 3064301 := bbase (se 3 (by rfl) ⟨574556, by rfl⟩ : syracuseStep 3064301 = 1149113) (by norm_num)
theorem B1532425 : Blo 1360499 1532425 := bbase (se 2 (by rfl) ⟨574659, by rfl⟩ : syracuseStep 1532425 = 1149319) (by norm_num)
theorem B6291989 : Blo 1360499 6291989 := bbase (se 6 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 6291989 = 294937) (by norm_num)
theorem B6890021 : Blo 1360499 6890021 := bbase (se 4 (by rfl) ⟨645939, by rfl⟩ : syracuseStep 6890021 = 1291879) (by norm_num)
theorem B1532461 : Blo 1360499 1532461 := bbase (se 3 (by rfl) ⟨287336, by rfl⟩ : syracuseStep 1532461 = 574673) (by norm_num)
theorem B3064373 : Blo 1360499 3064373 := bbase (se 5 (by rfl) ⟨143642, by rfl⟩ : syracuseStep 3064373 = 287285) (by norm_num)
theorem B1745473 : Blo 1360499 1745473 := bbase (se 2 (by rfl) ⟨654552, by rfl⟩ : syracuseStep 1745473 = 1309105) (by norm_num)
theorem B1532497 : Blo 1360499 1532497 := bbase (se 2 (by rfl) ⟨574686, by rfl⟩ : syracuseStep 1532497 = 1149373) (by norm_num)
theorem B1532533 : Blo 1360499 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B3064445 : Blo 1360499 3064445 := bbase (se 3 (by rfl) ⟨574583, by rfl⟩ : syracuseStep 3064445 = 1149167) (by norm_num)
theorem B2908813 : Blo 1360499 2908813 := bbase (se 3 (by rfl) ⟨545402, by rfl⟩ : syracuseStep 2908813 = 1090805) (by norm_num)
theorem B7365269 : Blo 1360499 7365269 := bbase (se 6 (by rfl) ⟨172623, by rfl⟩ : syracuseStep 7365269 = 345247) (by norm_num)
theorem B1532569 : Blo 1360499 1532569 := bbase (se 2 (by rfl) ⟨574713, by rfl⟩ : syracuseStep 1532569 = 1149427) (by norm_num)
theorem B9814709 : Blo 1360499 9814709 := bbase (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) (by norm_num)
theorem B1532605 : Blo 1360499 1532605 := bbase (se 3 (by rfl) ⟨287363, by rfl⟩ : syracuseStep 1532605 = 574727) (by norm_num)
theorem B3064517 : Blo 1360499 3064517 := bbase (se 4 (by rfl) ⟨287298, by rfl⟩ : syracuseStep 3064517 = 574597) (by norm_num)
theorem B1532641 : Blo 1360499 1532641 := bbase (se 2 (by rfl) ⟨574740, by rfl⟩ : syracuseStep 1532641 = 1149481) (by norm_num)
theorem B1532677 : Blo 1360499 1532677 := bbase (se 4 (by rfl) ⟨143688, by rfl⟩ : syracuseStep 1532677 = 287377) (by norm_num)
theorem B3064589 : Blo 1360499 3064589 := bbase (se 3 (by rfl) ⟨574610, by rfl⟩ : syracuseStep 3064589 = 1149221) (by norm_num)
theorem B1532713 : Blo 1360499 1532713 := bbase (se 2 (by rfl) ⟨574767, by rfl⟩ : syracuseStep 1532713 = 1149535) (by norm_num)
theorem B4596533 : Blo 1360499 4596533 := bbase (se 5 (by rfl) ⟨215462, by rfl⟩ : syracuseStep 4596533 = 430925) (by norm_num)
theorem B1532749 : Blo 1360499 1532749 := bbase (se 3 (by rfl) ⟨287390, by rfl⟩ : syracuseStep 1532749 = 574781) (by norm_num)
theorem B4907861 : Blo 1360499 4907861 := bbase (se 9 (by rfl) ⟨14378, by rfl⟩ : syracuseStep 4907861 = 28757) (by norm_num)
theorem B3064661 : Blo 1360499 3064661 := bbase (se 9 (by rfl) ⟨8978, by rfl⟩ : syracuseStep 3064661 = 17957) (by norm_num)
theorem B1532785 : Blo 1360499 1532785 := bbase (se 2 (by rfl) ⟨574794, by rfl⟩ : syracuseStep 1532785 = 1149589) (by norm_num)
theorem B3064733 : Blo 1360499 3064733 := bbase (se 3 (by rfl) ⟨574637, by rfl⟩ : syracuseStep 3064733 = 1149275) (by norm_num)
theorem B2040749 : Blo 1360499 2040749 := bbase (se 3 (by rfl) ⟨382640, by rfl⟩ : syracuseStep 2040749 = 765281) (by norm_num)
theorem B2040773 : Blo 1360499 2040773 := bbase (se 4 (by rfl) ⟨191322, by rfl⟩ : syracuseStep 2040773 = 382645) (by norm_num)
theorem B3490781 : Blo 1360499 3490781 := bbase (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) (by norm_num)
theorem B2040797 : Blo 1360499 2040797 := bbase (se 3 (by rfl) ⟨382649, by rfl⟩ : syracuseStep 2040797 = 765299) (by norm_num)
theorem B3064805 : Blo 1360499 3064805 := bbase (se 4 (by rfl) ⟨287325, by rfl⟩ : syracuseStep 3064805 = 574651) (by norm_num)
theorem B2040821 : Blo 1360499 2040821 := bbase (se 5 (by rfl) ⟨95663, by rfl⟩ : syracuseStep 2040821 = 191327) (by norm_num)
theorem B2909189 : Blo 1360499 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B2761733 : Blo 1360499 2761733 := bbase (se 4 (by rfl) ⟨258912, by rfl⟩ : syracuseStep 2761733 = 517825) (by norm_num)
theorem B2040845 : Blo 1360499 2040845 := bbase (se 3 (by rfl) ⟨382658, by rfl⟩ : syracuseStep 2040845 = 765317) (by norm_num)
theorem B3679253 : Blo 1360499 3679253 := bbase (se 6 (by rfl) ⟨86232, by rfl⟩ : syracuseStep 3679253 = 172465) (by norm_num)
theorem B2040869 : Blo 1360499 2040869 := bbase (se 4 (by rfl) ⟨191331, by rfl⟩ : syracuseStep 2040869 = 382663) (by norm_num)
theorem B3064877 : Blo 1360499 3064877 := bbase (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) (by norm_num)
theorem B2040893 : Blo 1360499 2040893 := bbase (se 3 (by rfl) ⟨382667, by rfl⟩ : syracuseStep 2040893 = 765335) (by norm_num)
theorem B2040917 : Blo 1360499 2040917 := bbase (se 8 (by rfl) ⟨11958, by rfl⟩ : syracuseStep 2040917 = 23917) (by norm_num)
theorem B2040941 : Blo 1360499 2040941 := bbase (se 3 (by rfl) ⟨382676, by rfl⟩ : syracuseStep 2040941 = 765353) (by norm_num)
theorem B3875957 : Blo 1360499 3875957 := bbase (se 5 (by rfl) ⟨181685, by rfl⟩ : syracuseStep 3875957 = 363371) (by norm_num)
theorem B3064949 : Blo 1360499 3064949 := bbase (se 5 (by rfl) ⟨143669, by rfl⟩ : syracuseStep 3064949 = 287339) (by norm_num)
theorem B2040965 : Blo 1360499 2040965 := bbase (se 4 (by rfl) ⟨191340, by rfl⟩ : syracuseStep 2040965 = 382681) (by norm_num)
theorem B6546581 : Blo 1360499 6546581 := bbase (se 6 (by rfl) ⟨153435, by rfl⟩ : syracuseStep 6546581 = 306871) (by norm_num)
theorem B2040989 : Blo 1360499 2040989 := bbase (se 3 (by rfl) ⟨382685, by rfl⟩ : syracuseStep 2040989 = 765371) (by norm_num)
theorem B1746085 : Blo 1360499 1746085 := bbase (se 4 (by rfl) ⟨163695, by rfl⟩ : syracuseStep 1746085 = 327391) (by norm_num)
theorem B2041013 : Blo 1360499 2041013 := bbase (se 5 (by rfl) ⟨95672, by rfl⟩ : syracuseStep 2041013 = 191345) (by norm_num)
theorem B3065021 : Blo 1360499 3065021 := bbase (se 3 (by rfl) ⟨574691, by rfl⟩ : syracuseStep 3065021 = 1149383) (by norm_num)
theorem B5817541 : Blo 1360499 5817541 := bbase (se 4 (by rfl) ⟨545394, by rfl⟩ : syracuseStep 5817541 = 1090789) (by norm_num)
theorem B2041037 : Blo 1360499 2041037 := bbase (se 3 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 2041037 = 765389) (by norm_num)
theorem B5817557 : Blo 1360499 5817557 := bbase (se 7 (by rfl) ⟨68174, by rfl⟩ : syracuseStep 5817557 = 136349) (by norm_num)
theorem B2041061 : Blo 1360499 2041061 := bbase (se 4 (by rfl) ⟨191349, by rfl⟩ : syracuseStep 2041061 = 382699) (by norm_num)
theorem B4596965 : Blo 1360499 4596965 := bbase (se 4 (by rfl) ⟨430965, by rfl⟩ : syracuseStep 4596965 = 861931) (by norm_num)
theorem B2041085 : Blo 1360499 2041085 := bbase (se 3 (by rfl) ⟨382703, by rfl⟩ : syracuseStep 2041085 = 765407) (by norm_num)
theorem B3065093 : Blo 1360499 3065093 := bbase (se 4 (by rfl) ⟨287352, by rfl⟩ : syracuseStep 3065093 = 574705) (by norm_num)
theorem B2041109 : Blo 1360499 2041109 := bbase (se 6 (by rfl) ⟨47838, by rfl⟩ : syracuseStep 2041109 = 95677) (by norm_num)
theorem B2041133 : Blo 1360499 2041133 := bbase (se 3 (by rfl) ⟨382712, by rfl⟩ : syracuseStep 2041133 = 765425) (by norm_num)
theorem B2180405 : Blo 1360499 2180405 := bbase (se 5 (by rfl) ⟨102206, by rfl⟩ : syracuseStep 2180405 = 204413) (by norm_num)
theorem B2041157 : Blo 1360499 2041157 := bbase (se 4 (by rfl) ⟨191358, by rfl⟩ : syracuseStep 2041157 = 382717) (by norm_num)
theorem B3065165 : Blo 1360499 3065165 := bbase (se 3 (by rfl) ⟨574718, by rfl⟩ : syracuseStep 3065165 = 1149437) (by norm_num)
theorem B2041181 : Blo 1360499 2041181 := bbase (se 3 (by rfl) ⟨382721, by rfl⟩ : syracuseStep 2041181 = 765443) (by norm_num)
theorem B2041205 : Blo 1360499 2041205 := bbase (se 5 (by rfl) ⟨95681, by rfl⟩ : syracuseStep 2041205 = 191363) (by norm_num)
theorem B2041229 : Blo 1360499 2041229 := bbase (se 3 (by rfl) ⟨382730, by rfl⟩ : syracuseStep 2041229 = 765461) (by norm_num)
theorem B3065237 : Blo 1360499 3065237 := bbase (se 6 (by rfl) ⟨71841, by rfl⟩ : syracuseStep 3065237 = 143683) (by norm_num)
theorem B2041253 : Blo 1360499 2041253 := bbase (se 4 (by rfl) ⟨191367, by rfl⟩ : syracuseStep 2041253 = 382735) (by norm_num)
theorem B3270061 : Blo 1360499 3270061 := bbase (se 3 (by rfl) ⟨613136, by rfl⟩ : syracuseStep 3270061 = 1226273) (by norm_num)
theorem B2041277 : Blo 1360499 2041277 := bbase (se 3 (by rfl) ⟨382739, by rfl⟩ : syracuseStep 2041277 = 765479) (by norm_num)
theorem B2041301 : Blo 1360499 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B3065309 : Blo 1360499 3065309 := bbase (se 3 (by rfl) ⟨574745, by rfl⟩ : syracuseStep 3065309 = 1149491) (by norm_num)
theorem B5170661 : Blo 1360499 5170661 := bbase (se 4 (by rfl) ⟨484749, by rfl⟩ : syracuseStep 5170661 = 969499) (by norm_num)
theorem B2041325 : Blo 1360499 2041325 := bbase (se 3 (by rfl) ⟨382748, by rfl⟩ : syracuseStep 2041325 = 765497) (by norm_num)
theorem B2041349 : Blo 1360499 2041349 := bbase (se 4 (by rfl) ⟨191376, by rfl⟩ : syracuseStep 2041349 = 382753) (by norm_num)
theorem B2041373 : Blo 1360499 2041373 := bbase (se 3 (by rfl) ⟨382757, by rfl⟩ : syracuseStep 2041373 = 765515) (by norm_num)
theorem B1721893 : Blo 1360499 1721893 := bbase (se 4 (by rfl) ⟨161427, by rfl⟩ : syracuseStep 1721893 = 322855) (by norm_num)
theorem B3065381 : Blo 1360499 3065381 := bbase (se 4 (by rfl) ⟨287379, by rfl⟩ : syracuseStep 3065381 = 574759) (by norm_num)
theorem B2041397 : Blo 1360499 2041397 := bbase (se 5 (by rfl) ⟨95690, by rfl⟩ : syracuseStep 2041397 = 191381) (by norm_num)
theorem B5891653 : Blo 1360499 5891653 := bbase (se 4 (by rfl) ⟨552342, by rfl⟩ : syracuseStep 5891653 = 1104685) (by norm_num)
theorem B2041421 : Blo 1360499 2041421 := bbase (se 3 (by rfl) ⟨382766, by rfl⟩ : syracuseStep 2041421 = 765533) (by norm_num)
theorem B2041445 : Blo 1360499 2041445 := bbase (se 4 (by rfl) ⟨191385, by rfl⟩ : syracuseStep 2041445 = 382771) (by norm_num)
theorem B3065453 : Blo 1360499 3065453 := bbase (se 3 (by rfl) ⟨574772, by rfl⟩ : syracuseStep 3065453 = 1149545) (by norm_num)
theorem B11634293 : Blo 1360499 11634293 := bbase (se 5 (by rfl) ⟨545357, by rfl⟩ : syracuseStep 11634293 = 1090715) (by norm_num)
theorem B3106421 : Blo 1360499 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B2041469 : Blo 1360499 2041469 := bbase (se 3 (by rfl) ⟨382775, by rfl⟩ : syracuseStep 2041469 = 765551) (by norm_num)
theorem B1721989 : Blo 1360499 1721989 := bbase (se 4 (by rfl) ⟨161436, by rfl⟩ : syracuseStep 1721989 = 322873) (by norm_num)
theorem B2041493 : Blo 1360499 2041493 := bbase (se 6 (by rfl) ⟨47847, by rfl⟩ : syracuseStep 2041493 = 95695) (by norm_num)
theorem B4597397 : Blo 1360499 4597397 := bbase (se 6 (by rfl) ⟨107751, by rfl⟩ : syracuseStep 4597397 = 215503) (by norm_num)
theorem B2041517 : Blo 1360499 2041517 := bbase (se 3 (by rfl) ⟨382784, by rfl⟩ : syracuseStep 2041517 = 765569) (by norm_num)
theorem B3147437 : Blo 1360499 3147437 := bbase (se 3 (by rfl) ⟨590144, by rfl⟩ : syracuseStep 3147437 = 1180289) (by norm_num)
theorem B3065525 : Blo 1360499 3065525 := bbase (se 5 (by rfl) ⟨143696, by rfl⟩ : syracuseStep 3065525 = 287393) (by norm_num)
theorem B2041541 : Blo 1360499 2041541 := bbase (se 4 (by rfl) ⟨191394, by rfl⟩ : syracuseStep 2041541 = 382789) (by norm_num)
theorem B14714581 : Blo 1360499 14714581 := bbase (se 7 (by rfl) ⟨172436, by rfl⟩ : syracuseStep 14714581 = 344873) (by norm_num)
theorem B2041565 : Blo 1360499 2041565 := bbase (se 3 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 2041565 = 765587) (by norm_num)
theorem B7079653 : Blo 1360499 7079653 := bbase (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) (by norm_num)
theorem B2041589 : Blo 1360499 2041589 := bbase (se 5 (by rfl) ⟨95699, by rfl⟩ : syracuseStep 2041589 = 191399) (by norm_num)
theorem B3270397 : Blo 1360499 3270397 := bbase (se 3 (by rfl) ⟨613199, by rfl⟩ : syracuseStep 3270397 = 1226399) (by norm_num)
theorem B2180861 : Blo 1360499 2180861 := bbase (se 3 (by rfl) ⟨408911, by rfl⟩ : syracuseStep 2180861 = 817823) (by norm_num)
theorem B3065597 : Blo 1360499 3065597 := bbase (se 3 (by rfl) ⟨574799, by rfl⟩ : syracuseStep 3065597 = 1149599) (by norm_num)
theorem B5170949 : Blo 1360499 5170949 := bbase (se 4 (by rfl) ⟨484776, by rfl⟩ : syracuseStep 5170949 = 969553) (by norm_num)
theorem B2041613 : Blo 1360499 2041613 := bbase (se 3 (by rfl) ⟨382802, by rfl⟩ : syracuseStep 2041613 = 765605) (by norm_num)
theorem B7759637 : Blo 1360499 7759637 := bbase (se 6 (by rfl) ⟨181866, by rfl⟩ : syracuseStep 7759637 = 363733) (by norm_num)
theorem B2041637 : Blo 1360499 2041637 := bbase (se 4 (by rfl) ⟨191403, by rfl⟩ : syracuseStep 2041637 = 382807) (by norm_num)
theorem B1722161 : Blo 1360499 1722161 := bbase (se 2 (by rfl) ⟨645810, by rfl⟩ : syracuseStep 1722161 = 1291621) (by norm_num)
theorem B6891317 : Blo 1360499 6891317 := bbase (se 5 (by rfl) ⟨323030, by rfl⟩ : syracuseStep 6891317 = 646061) (by norm_num)
theorem B4908853 : Blo 1360499 4908853 := bbase (se 5 (by rfl) ⟨230102, by rfl⟩ : syracuseStep 4908853 = 460205) (by norm_num)
theorem B2041661 : Blo 1360499 2041661 := bbase (se 3 (by rfl) ⟨382811, by rfl⟩ : syracuseStep 2041661 = 765623) (by norm_num)
theorem B2041685 : Blo 1360499 2041685 := bbase (se 9 (by rfl) ⟨5981, by rfl⟩ : syracuseStep 2041685 = 11963) (by norm_num)
theorem B1722217 : Blo 1360499 1722217 := bbase (se 2 (by rfl) ⟨645831, by rfl⟩ : syracuseStep 1722217 = 1291663) (by norm_num)
theorem B2041709 : Blo 1360499 2041709 := bbase (se 3 (by rfl) ⟨382820, by rfl⟩ : syracuseStep 2041709 = 765641) (by norm_num)
theorem B2041733 : Blo 1360499 2041733 := bbase (se 4 (by rfl) ⟨191412, by rfl⟩ : syracuseStep 2041733 = 382825) (by norm_num)
theorem B2041757 : Blo 1360499 2041757 := bbase (se 3 (by rfl) ⟨382829, by rfl⟩ : syracuseStep 2041757 = 765659) (by norm_num)
theorem B2041781 : Blo 1360499 2041781 := bbase (se 5 (by rfl) ⟨95708, by rfl⟩ : syracuseStep 2041781 = 191417) (by norm_num)
theorem B1574845 : Blo 1360499 1574845 := bbase (se 3 (by rfl) ⟨295283, by rfl⟩ : syracuseStep 1574845 = 590567) (by norm_num)
theorem B1722313 : Blo 1360499 1722313 := bbase (se 2 (by rfl) ⟨645867, by rfl⟩ : syracuseStep 1722313 = 1291735) (by norm_num)
theorem B2041805 : Blo 1360499 2041805 := bbase (se 3 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 2041805 = 765677) (by norm_num)
theorem B16779221 : Blo 1360499 16779221 := bbase (se 7 (by rfl) ⟨196631, by rfl⟩ : syracuseStep 16779221 = 393263) (by norm_num)
theorem B2041829 : Blo 1360499 2041829 := bbase (se 4 (by rfl) ⟨191421, by rfl⟩ : syracuseStep 2041829 = 382843) (by norm_num)
theorem B2041853 : Blo 1360499 2041853 := bbase (se 3 (by rfl) ⟨382847, by rfl⟩ : syracuseStep 2041853 = 765695) (by norm_num)
theorem B2041877 : Blo 1360499 2041877 := bbase (se 6 (by rfl) ⟨47856, by rfl⟩ : syracuseStep 2041877 = 95713) (by norm_num)
theorem B2041901 : Blo 1360499 2041901 := bbase (se 3 (by rfl) ⟨382856, by rfl⟩ : syracuseStep 2041901 = 765713) (by norm_num)
theorem B2295877 : Blo 1360499 2295877 := bbase (se 4 (by rfl) ⟨215238, by rfl⟩ : syracuseStep 2295877 = 430477) (by norm_num)
theorem B2041925 : Blo 1360499 2041925 := bbase (se 4 (by rfl) ⟨191430, by rfl⟩ : syracuseStep 2041925 = 382861) (by norm_num)
theorem B4597829 : Blo 1360499 4597829 := bbase (se 4 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 4597829 = 862093) (by norm_num)
theorem B2041949 : Blo 1360499 2041949 := bbase (se 3 (by rfl) ⟨382865, by rfl⟩ : syracuseStep 2041949 = 765731) (by norm_num)
theorem B6383717 : Blo 1360499 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B1722485 : Blo 1360499 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B2041973 : Blo 1360499 2041973 := bbase (se 5 (by rfl) ⟨95717, by rfl⟩ : syracuseStep 2041973 = 191435) (by norm_num)
theorem B2041997 : Blo 1360499 2041997 := bbase (se 3 (by rfl) ⟨382874, by rfl⟩ : syracuseStep 2041997 = 765749) (by norm_num)
theorem B2295965 : Blo 1360499 2295965 := bbase (se 3 (by rfl) ⟨430493, by rfl⟩ : syracuseStep 2295965 = 860987) (by norm_num)
theorem B2042021 : Blo 1360499 2042021 := bbase (se 4 (by rfl) ⟨191439, by rfl⟩ : syracuseStep 2042021 = 382879) (by norm_num)
theorem B1722541 : Blo 1360499 1722541 := bbase (se 3 (by rfl) ⟨322976, by rfl⟩ : syracuseStep 1722541 = 645953) (by norm_num)
theorem B2042045 : Blo 1360499 2042045 := bbase (se 3 (by rfl) ⟨382883, by rfl⟩ : syracuseStep 2042045 = 765767) (by norm_num)
theorem B2042069 : Blo 1360499 2042069 := bbase (se 7 (by rfl) ⟨23930, by rfl⟩ : syracuseStep 2042069 = 47861) (by norm_num)
theorem B2042093 : Blo 1360499 2042093 := bbase (se 3 (by rfl) ⟨382892, by rfl⟩ : syracuseStep 2042093 = 765785) (by norm_num)
theorem B6539525 : Blo 1360499 6539525 := bbase (se 4 (by rfl) ⟨613080, by rfl⟩ : syracuseStep 6539525 = 1226161) (by norm_num)
theorem B2042117 : Blo 1360499 2042117 := bbase (se 4 (by rfl) ⟨191448, by rfl⟩ : syracuseStep 2042117 = 382897) (by norm_num)
theorem B1722637 : Blo 1360499 1722637 := bbase (se 3 (by rfl) ⟨322994, by rfl⟩ : syracuseStep 1722637 = 645989) (by norm_num)
theorem B3877141 : Blo 1360499 3877141 := bbase (se 6 (by rfl) ⟨90870, by rfl⟩ : syracuseStep 3877141 = 181741) (by norm_num)
theorem B2296093 : Blo 1360499 2296093 := bbase (se 3 (by rfl) ⟨430517, by rfl⟩ : syracuseStep 2296093 = 861035) (by norm_num)
theorem B2042141 : Blo 1360499 2042141 := bbase (se 3 (by rfl) ⟨382901, by rfl⟩ : syracuseStep 2042141 = 765803) (by norm_num)
theorem B2042165 : Blo 1360499 2042165 := bbase (se 5 (by rfl) ⟨95726, by rfl⟩ : syracuseStep 2042165 = 191453) (by norm_num)
theorem B3680581 : Blo 1360499 3680581 := bbase (se 4 (by rfl) ⟨345054, by rfl⟩ : syracuseStep 3680581 = 690109) (by norm_num)
theorem B2042189 : Blo 1360499 2042189 := bbase (se 3 (by rfl) ⟨382910, by rfl⟩ : syracuseStep 2042189 = 765821) (by norm_num)
theorem B3271013 : Blo 1360499 3271013 := bbase (se 4 (by rfl) ⟨306657, by rfl⟩ : syracuseStep 3271013 = 613315) (by norm_num)
theorem B2042213 : Blo 1360499 2042213 := bbase (se 4 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 2042213 = 382915) (by norm_num)
theorem B2296181 : Blo 1360499 2296181 := bbase (se 5 (by rfl) ⟨107633, by rfl⟩ : syracuseStep 2296181 = 215267) (by norm_num)
theorem B2042237 : Blo 1360499 2042237 := bbase (se 3 (by rfl) ⟨382919, by rfl⟩ : syracuseStep 2042237 = 765839) (by norm_num)
theorem B2042261 : Blo 1360499 2042261 := bbase (se 6 (by rfl) ⟨47865, by rfl⟩ : syracuseStep 2042261 = 95731) (by norm_num)
theorem B2042285 : Blo 1360499 2042285 := bbase (se 3 (by rfl) ⟨382928, by rfl⟩ : syracuseStep 2042285 = 765857) (by norm_num)
theorem B3877301 : Blo 1360499 3877301 := bbase (se 5 (by rfl) ⟨181748, by rfl⟩ : syracuseStep 3877301 = 363497) (by norm_num)
theorem B1722809 : Blo 1360499 1722809 := bbase (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) (by norm_num)
theorem B3107261 : Blo 1360499 3107261 := bbase (se 3 (by rfl) ⟨582611, by rfl⟩ : syracuseStep 3107261 = 1165223) (by norm_num)
theorem B2042309 : Blo 1360499 2042309 := bbase (se 4 (by rfl) ⟨191466, by rfl⟩ : syracuseStep 2042309 = 382933) (by norm_num)
theorem B2042333 : Blo 1360499 2042333 := bbase (se 3 (by rfl) ⟨382937, by rfl⟩ : syracuseStep 2042333 = 765875) (by norm_num)
theorem B1722865 : Blo 1360499 1722865 := bbase (se 2 (by rfl) ⟨646074, by rfl⟩ : syracuseStep 1722865 = 1292149) (by norm_num)
theorem B2583029 : Blo 1360499 2583029 := bbase (se 5 (by rfl) ⟨121079, by rfl⟩ : syracuseStep 2583029 = 242159) (by norm_num)
theorem B2296309 : Blo 1360499 2296309 := bbase (se 5 (by rfl) ⟨107639, by rfl⟩ : syracuseStep 2296309 = 215279) (by norm_num)
theorem B2042357 : Blo 1360499 2042357 := bbase (se 5 (by rfl) ⟨95735, by rfl⟩ : syracuseStep 2042357 = 191471) (by norm_num)
theorem B4598261 : Blo 1360499 4598261 := bbase (se 5 (by rfl) ⟨215543, by rfl⟩ : syracuseStep 4598261 = 431087) (by norm_num)
theorem B2042381 : Blo 1360499 2042381 := bbase (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) (by norm_num)
theorem B2042405 : Blo 1360499 2042405 := bbase (se 4 (by rfl) ⟨191475, by rfl⟩ : syracuseStep 2042405 = 382951) (by norm_num)
theorem B1747505 : Blo 1360499 1747505 := bbase (se 2 (by rfl) ⟨655314, by rfl⟩ : syracuseStep 1747505 = 1310629) (by norm_num)
theorem B2042429 : Blo 1360499 2042429 := bbase (se 3 (by rfl) ⟨382955, by rfl⟩ : syracuseStep 2042429 = 765911) (by norm_num)
theorem B2296397 : Blo 1360499 2296397 := bbase (se 3 (by rfl) ⟨430574, by rfl⟩ : syracuseStep 2296397 = 861149) (by norm_num)
theorem B1722961 : Blo 1360499 1722961 := bbase (se 2 (by rfl) ⟨646110, by rfl⟩ : syracuseStep 1722961 = 1292221) (by norm_num)
theorem B2042453 : Blo 1360499 2042453 := bbase (se 8 (by rfl) ⟨11967, by rfl⟩ : syracuseStep 2042453 = 23935) (by norm_num)
theorem B2042477 : Blo 1360499 2042477 := bbase (se 3 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 2042477 = 765929) (by norm_num)
theorem B4360837 : Blo 1360499 4360837 := bbase (se 4 (by rfl) ⟨408828, by rfl⟩ : syracuseStep 4360837 = 817657) (by norm_num)
theorem B2042501 : Blo 1360499 2042501 := bbase (se 4 (by rfl) ⟨191484, by rfl⟩ : syracuseStep 2042501 = 382969) (by norm_num)
theorem B2583181 : Blo 1360499 2583181 := bbase (se 3 (by rfl) ⟨484346, by rfl⟩ : syracuseStep 2583181 = 968693) (by norm_num)
theorem B2042525 : Blo 1360499 2042525 := bbase (se 3 (by rfl) ⟨382973, by rfl⟩ : syracuseStep 2042525 = 765947) (by norm_num)
theorem B3877541 : Blo 1360499 3877541 := bbase (se 4 (by rfl) ⟨363519, by rfl⟩ : syracuseStep 3877541 = 727039) (by norm_num)
theorem B2042549 : Blo 1360499 2042549 := bbase (se 5 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 2042549 = 191489) (by norm_num)
theorem B2296525 : Blo 1360499 2296525 := bbase (se 3 (by rfl) ⟨430598, by rfl⟩ : syracuseStep 2296525 = 861197) (by norm_num)
theorem B2042573 : Blo 1360499 2042573 := bbase (se 3 (by rfl) ⟨382982, by rfl⟩ : syracuseStep 2042573 = 765965) (by norm_num)
theorem B2042597 : Blo 1360499 2042597 := bbase (se 4 (by rfl) ⟨191493, by rfl⟩ : syracuseStep 2042597 = 382987) (by norm_num)
theorem B1723133 : Blo 1360499 1723133 := bbase (se 3 (by rfl) ⟨323087, by rfl⟩ : syracuseStep 1723133 = 646175) (by norm_num)
theorem B2042621 : Blo 1360499 2042621 := bbase (se 3 (by rfl) ⟨382991, by rfl⟩ : syracuseStep 2042621 = 765983) (by norm_num)
theorem B3271445 : Blo 1360499 3271445 := bbase (se 6 (by rfl) ⟨76674, by rfl⟩ : syracuseStep 3271445 = 153349) (by norm_num)
theorem B2042645 : Blo 1360499 2042645 := bbase (se 6 (by rfl) ⟨47874, by rfl⟩ : syracuseStep 2042645 = 95749) (by norm_num)
theorem B2296613 : Blo 1360499 2296613 := bbase (se 4 (by rfl) ⟨215307, by rfl⟩ : syracuseStep 2296613 = 430615) (by norm_num)
theorem B2042669 : Blo 1360499 2042669 := bbase (se 3 (by rfl) ⟨383000, by rfl⟩ : syracuseStep 2042669 = 766001) (by norm_num)
theorem B1723189 : Blo 1360499 1723189 := bbase (se 5 (by rfl) ⟨80774, by rfl⟩ : syracuseStep 1723189 = 161549) (by norm_num)
theorem B2042693 : Blo 1360499 2042693 := bbase (se 4 (by rfl) ⟨191502, by rfl⟩ : syracuseStep 2042693 = 383005) (by norm_num)
theorem B2796373 : Blo 1360499 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B2042717 : Blo 1360499 2042717 := bbase (se 3 (by rfl) ⟨383009, by rfl⟩ : syracuseStep 2042717 = 766019) (by norm_num)
theorem B3877733 : Blo 1360499 3877733 := bbase (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) (by norm_num)
theorem B2042741 : Blo 1360499 2042741 := bbase (se 5 (by rfl) ⟨95753, by rfl⟩ : syracuseStep 2042741 = 191507) (by norm_num)
theorem B2042765 : Blo 1360499 2042765 := bbase (se 3 (by rfl) ⟨383018, by rfl⟩ : syracuseStep 2042765 = 766037) (by norm_num)
theorem B1723285 : Blo 1360499 1723285 := bbase (se 6 (by rfl) ⟨40389, by rfl⟩ : syracuseStep 1723285 = 80779) (by norm_num)
theorem B2296741 : Blo 1360499 2296741 := bbase (se 4 (by rfl) ⟨215319, by rfl⟩ : syracuseStep 2296741 = 430639) (by norm_num)
theorem B2042789 : Blo 1360499 2042789 := bbase (se 4 (by rfl) ⟨191511, by rfl⟩ : syracuseStep 2042789 = 383023) (by norm_num)
theorem B5172133 : Blo 1360499 5172133 := bbase (se 4 (by rfl) ⟨484887, by rfl⟩ : syracuseStep 5172133 = 969775) (by norm_num)
theorem B2583485 : Blo 1360499 2583485 := bbase (se 3 (by rfl) ⟨484403, by rfl⟩ : syracuseStep 2583485 = 968807) (by norm_num)
theorem B2042813 : Blo 1360499 2042813 := bbase (se 3 (by rfl) ⟨383027, by rfl⟩ : syracuseStep 2042813 = 766055) (by norm_num)
theorem B2042837 : Blo 1360499 2042837 := bbase (se 7 (by rfl) ⟨23939, by rfl⟩ : syracuseStep 2042837 = 47879) (by norm_num)
theorem B2042861 : Blo 1360499 2042861 := bbase (se 3 (by rfl) ⟨383036, by rfl⟩ : syracuseStep 2042861 = 766073) (by norm_num)
theorem B2296829 : Blo 1360499 2296829 := bbase (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) (by norm_num)
theorem B2042885 : Blo 1360499 2042885 := bbase (se 4 (by rfl) ⟨191520, by rfl⟩ : syracuseStep 2042885 = 383041) (by norm_num)
theorem B2042909 : Blo 1360499 2042909 := bbase (se 3 (by rfl) ⟨383045, by rfl⟩ : syracuseStep 2042909 = 766091) (by norm_num)
theorem B12414005 : Blo 1360499 12414005 := bbase (se 5 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 12414005 = 1163813) (by norm_num)
theorem B2042933 : Blo 1360499 2042933 := bbase (se 5 (by rfl) ⟨95762, by rfl⟩ : syracuseStep 2042933 = 191525) (by norm_num)
theorem B1723457 : Blo 1360499 1723457 := bbase (se 2 (by rfl) ⟨646296, by rfl⟩ : syracuseStep 1723457 = 1292593) (by norm_num)
theorem B6892613 : Blo 1360499 6892613 := bbase (se 4 (by rfl) ⟨646182, by rfl⟩ : syracuseStep 6892613 = 1292365) (by norm_num)
theorem B2042957 : Blo 1360499 2042957 := bbase (se 3 (by rfl) ⟨383054, by rfl⟩ : syracuseStep 2042957 = 766109) (by norm_num)
theorem B2042981 : Blo 1360499 2042981 := bbase (se 4 (by rfl) ⟨191529, by rfl⟩ : syracuseStep 2042981 = 383059) (by norm_num)
theorem B13085813 : Blo 1360499 13085813 := bbase (se 5 (by rfl) ⟨613397, by rfl⟩ : syracuseStep 13085813 = 1226795) (by norm_num)
theorem B1723513 : Blo 1360499 1723513 := bbase (se 2 (by rfl) ⟨646317, by rfl⟩ : syracuseStep 1723513 = 1292635) (by norm_num)
theorem B2296957 : Blo 1360499 2296957 := bbase (se 3 (by rfl) ⟨430679, by rfl⟩ : syracuseStep 2296957 = 861359) (by norm_num)
theorem B2043005 : Blo 1360499 2043005 := bbase (se 3 (by rfl) ⟨383063, by rfl⟩ : syracuseStep 2043005 = 766127) (by norm_num)
theorem B2182277 : Blo 1360499 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B2043029 : Blo 1360499 2043029 := bbase (se 6 (by rfl) ⟨47883, by rfl⟩ : syracuseStep 2043029 = 95767) (by norm_num)
theorem B2043053 : Blo 1360499 2043053 := bbase (se 3 (by rfl) ⟨383072, by rfl⟩ : syracuseStep 2043053 = 766145) (by norm_num)
theorem B2043077 : Blo 1360499 2043077 := bbase (se 4 (by rfl) ⟨191538, by rfl⟩ : syracuseStep 2043077 = 383077) (by norm_num)
theorem B3443917 : Blo 1360499 3443917 := bbase (se 3 (by rfl) ⟨645734, by rfl⟩ : syracuseStep 3443917 = 1291469) (by norm_num)
theorem B2297045 : Blo 1360499 2297045 := bbase (se 7 (by rfl) ⟨26918, by rfl⟩ : syracuseStep 2297045 = 53837) (by norm_num)
theorem B5172437 : Blo 1360499 5172437 := bbase (se 7 (by rfl) ⟨60614, by rfl⟩ : syracuseStep 5172437 = 121229) (by norm_num)
theorem B1723609 : Blo 1360499 1723609 := bbase (se 2 (by rfl) ⟨646353, by rfl⟩ : syracuseStep 1723609 = 1292707) (by norm_num)
theorem B2043101 : Blo 1360499 2043101 := bbase (se 3 (by rfl) ⟨383081, by rfl⟩ : syracuseStep 2043101 = 766163) (by norm_num)
theorem B2043125 : Blo 1360499 2043125 := bbase (se 5 (by rfl) ⟨95771, by rfl⟩ : syracuseStep 2043125 = 191543) (by norm_num)
theorem B1453313 : Blo 1360499 1453313 := bbase (se 2 (by rfl) ⟨544992, by rfl⟩ : syracuseStep 1453313 = 1089985) (by norm_num)
theorem B2043149 : Blo 1360499 2043149 := bbase (se 3 (by rfl) ⟨383090, by rfl⟩ : syracuseStep 2043149 = 766181) (by norm_num)
theorem B1551637 : Blo 1360499 1551637 := bbase (se 6 (by rfl) ⟨36366, by rfl⟩ : syracuseStep 1551637 = 72733) (by norm_num)
theorem B2043173 : Blo 1360499 2043173 := bbase (se 4 (by rfl) ⟨191547, by rfl⟩ : syracuseStep 2043173 = 383095) (by norm_num)
theorem B3444029 : Blo 1360499 3444029 := bbase (se 3 (by rfl) ⟨645755, by rfl⟩ : syracuseStep 3444029 = 1291511) (by norm_num)
theorem B2043197 : Blo 1360499 2043197 := bbase (se 3 (by rfl) ⟨383099, by rfl⟩ : syracuseStep 2043197 = 766199) (by norm_num)
theorem B2297173 : Blo 1360499 2297173 := bbase (se 11 (by rfl) ⟨1682, by rfl⟩ : syracuseStep 2297173 = 3365) (by norm_num)
theorem B2043221 : Blo 1360499 2043221 := bbase (se 11 (by rfl) ⟨1496, by rfl⟩ : syracuseStep 2043221 = 2993) (by norm_num)
theorem B2043245 : Blo 1360499 2043245 := bbase (se 3 (by rfl) ⟨383108, by rfl⟩ : syracuseStep 2043245 = 766217) (by norm_num)
theorem B3272069 : Blo 1360499 3272069 := bbase (se 4 (by rfl) ⟨306756, by rfl⟩ : syracuseStep 3272069 = 613513) (by norm_num)
theorem B1723781 : Blo 1360499 1723781 := bbase (se 4 (by rfl) ⟨161604, by rfl⟩ : syracuseStep 1723781 = 323209) (by norm_num)
theorem B2043269 : Blo 1360499 2043269 := bbase (se 4 (by rfl) ⟨191556, by rfl⟩ : syracuseStep 2043269 = 383113) (by norm_num)
theorem B2043293 : Blo 1360499 2043293 := bbase (se 3 (by rfl) ⟨383117, by rfl⟩ : syracuseStep 2043293 = 766235) (by norm_num)
theorem B5819813 : Blo 1360499 5819813 := bbase (se 4 (by rfl) ⟨545607, by rfl⟩ : syracuseStep 5819813 = 1091215) (by norm_num)
theorem B2297261 : Blo 1360499 2297261 := bbase (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) (by norm_num)
theorem B4656565 : Blo 1360499 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B2043317 : Blo 1360499 2043317 := bbase (se 5 (by rfl) ⟨95780, by rfl⟩ : syracuseStep 2043317 = 191561) (by norm_num)
theorem B1453501 : Blo 1360499 1453501 := bbase (se 3 (by rfl) ⟨272531, by rfl⟩ : syracuseStep 1453501 = 545063) (by norm_num)
theorem B1723837 : Blo 1360499 1723837 := bbase (se 3 (by rfl) ⟨323219, by rfl⟩ : syracuseStep 1723837 = 646439) (by norm_num)
theorem B2043341 : Blo 1360499 2043341 := bbase (se 3 (by rfl) ⟨383126, by rfl⟩ : syracuseStep 2043341 = 766253) (by norm_num)
theorem B2043365 : Blo 1360499 2043365 := bbase (se 4 (by rfl) ⟨191565, by rfl⟩ : syracuseStep 2043365 = 383131) (by norm_num)
theorem B3444221 : Blo 1360499 3444221 := bbase (se 3 (by rfl) ⟨645791, by rfl⟩ : syracuseStep 3444221 = 1291583) (by norm_num)
theorem B2043389 : Blo 1360499 2043389 := bbase (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) (by norm_num)
theorem B2797061 : Blo 1360499 2797061 := bbase (se 4 (by rfl) ⟨262224, by rfl⟩ : syracuseStep 2797061 = 524449) (by norm_num)
theorem B2043413 : Blo 1360499 2043413 := bbase (se 6 (by rfl) ⟨47892, by rfl⟩ : syracuseStep 2043413 = 95785) (by norm_num)
theorem B1723933 : Blo 1360499 1723933 := bbase (se 3 (by rfl) ⟨323237, by rfl⟩ : syracuseStep 1723933 = 646475) (by norm_num)
theorem B5811749 : Blo 1360499 5811749 := bbase (se 4 (by rfl) ⟨544851, by rfl⟩ : syracuseStep 5811749 = 1089703) (by norm_num)
theorem B1379885 : Blo 1360499 1379885 := bbase (se 3 (by rfl) ⟨258728, by rfl⟩ : syracuseStep 1379885 = 517457) (by norm_num)
theorem B2297389 : Blo 1360499 2297389 := bbase (se 3 (by rfl) ⟨430760, by rfl⟩ : syracuseStep 2297389 = 861521) (by norm_num)
theorem B2043437 : Blo 1360499 2043437 := bbase (se 3 (by rfl) ⟨383144, by rfl⟩ : syracuseStep 2043437 = 766289) (by norm_num)
theorem B2043461 : Blo 1360499 2043461 := bbase (se 4 (by rfl) ⟨191574, by rfl⟩ : syracuseStep 2043461 = 383149) (by norm_num)
theorem B2043485 : Blo 1360499 2043485 := bbase (se 3 (by rfl) ⟨383153, by rfl⟩ : syracuseStep 2043485 = 766307) (by norm_num)
theorem B8728181 : Blo 1360499 8728181 := bbase (se 5 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 8728181 = 818267) (by norm_num)
theorem B2043509 : Blo 1360499 2043509 := bbase (se 5 (by rfl) ⟨95789, by rfl⟩ : syracuseStep 2043509 = 191579) (by norm_num)
theorem B2297477 : Blo 1360499 2297477 := bbase (se 4 (by rfl) ⟨215388, by rfl⟩ : syracuseStep 2297477 = 430777) (by norm_num)
theorem B2043533 : Blo 1360499 2043533 := bbase (se 3 (by rfl) ⟨383162, by rfl⟩ : syracuseStep 2043533 = 766325) (by norm_num)
theorem B2043557 : Blo 1360499 2043557 := bbase (se 4 (by rfl) ⟨191583, by rfl⟩ : syracuseStep 2043557 = 383167) (by norm_num)
theorem B2584237 : Blo 1360499 2584237 := bbase (se 3 (by rfl) ⟨484544, by rfl⟩ : syracuseStep 2584237 = 969089) (by norm_num)
theorem B4140725 : Blo 1360499 4140725 := bbase (se 5 (by rfl) ⟨194096, by rfl⟩ : syracuseStep 4140725 = 388193) (by norm_num)
theorem B2043581 : Blo 1360499 2043581 := bbase (se 3 (by rfl) ⟨383171, by rfl⟩ : syracuseStep 2043581 = 766343) (by norm_num)
theorem B4419269 : Blo 1360499 4419269 := bbase (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) (by norm_num)
theorem B2330309 : Blo 1360499 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B1724105 : Blo 1360499 1724105 := bbase (se 2 (by rfl) ⟨646539, by rfl⟩ : syracuseStep 1724105 = 1293079) (by norm_num)
theorem B2043605 : Blo 1360499 2043605 := bbase (se 7 (by rfl) ⟨23948, by rfl⟩ : syracuseStep 2043605 = 47897) (by norm_num)
theorem B2043629 : Blo 1360499 2043629 := bbase (se 3 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 2043629 = 766361) (by norm_num)
theorem B1724161 : Blo 1360499 1724161 := bbase (se 2 (by rfl) ⟨646560, by rfl⟩ : syracuseStep 1724161 = 1293121) (by norm_num)
theorem B2297605 : Blo 1360499 2297605 := bbase (se 4 (by rfl) ⟨215400, by rfl⟩ : syracuseStep 2297605 = 430801) (by norm_num)
theorem B2043653 : Blo 1360499 2043653 := bbase (se 4 (by rfl) ⟨191592, by rfl⟩ : syracuseStep 2043653 = 383185) (by norm_num)
theorem B10481429 : Blo 1360499 10481429 := bbase (se 6 (by rfl) ⟨245658, by rfl⟩ : syracuseStep 10481429 = 491317) (by norm_num)
theorem B2043677 : Blo 1360499 2043677 := bbase (se 3 (by rfl) ⟨383189, by rfl⟩ : syracuseStep 2043677 = 766379) (by norm_num)
theorem B2043701 : Blo 1360499 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B2584381 : Blo 1360499 2584381 := bbase (se 3 (by rfl) ⟨484571, by rfl⟩ : syracuseStep 2584381 = 969143) (by norm_num)
theorem B1838917 : Blo 1360499 1838917 := bbase (se 4 (by rfl) ⟨172398, by rfl⟩ : syracuseStep 1838917 = 344797) (by norm_num)
theorem B3878725 : Blo 1360499 3878725 := bbase (se 4 (by rfl) ⟨363630, by rfl⟩ : syracuseStep 3878725 = 727261) (by norm_num)
theorem B2043725 : Blo 1360499 2043725 := bbase (se 3 (by rfl) ⟨383198, by rfl⟩ : syracuseStep 2043725 = 766397) (by norm_num)
theorem B3444565 : Blo 1360499 3444565 := bbase (se 9 (by rfl) ⟨10091, by rfl⟩ : syracuseStep 3444565 = 20183) (by norm_num)
theorem B2297693 : Blo 1360499 2297693 := bbase (se 3 (by rfl) ⟨430817, by rfl⟩ : syracuseStep 2297693 = 861635) (by norm_num)
theorem B1724257 : Blo 1360499 1724257 := bbase (se 2 (by rfl) ⟨646596, by rfl⟩ : syracuseStep 1724257 = 1293193) (by norm_num)
theorem B2043749 : Blo 1360499 2043749 := bbase (se 4 (by rfl) ⟨191601, by rfl⟩ : syracuseStep 2043749 = 383203) (by norm_num)
theorem B1839037 : Blo 1360499 1839037 := bbase (se 3 (by rfl) ⟨344819, by rfl⟩ : syracuseStep 1839037 = 689639) (by norm_num)
theorem B3444677 : Blo 1360499 3444677 := bbase (se 4 (by rfl) ⟨322938, by rfl⟩ : syracuseStep 3444677 = 645877) (by norm_num)
theorem B2584541 : Blo 1360499 2584541 := bbase (se 3 (by rfl) ⟨484601, by rfl⟩ : syracuseStep 2584541 = 969203) (by norm_num)
theorem B2297821 : Blo 1360499 2297821 := bbase (se 3 (by rfl) ⟨430841, by rfl⟩ : syracuseStep 2297821 = 861683) (by norm_num)
theorem B1658873 : Blo 1360499 1658873 := bbase (se 2 (by rfl) ⟨622077, by rfl⟩ : syracuseStep 1658873 = 1244155) (by norm_num)
theorem B2297909 : Blo 1360499 2297909 := bbase (se 5 (by rfl) ⟨107714, by rfl⟩ : syracuseStep 2297909 = 215429) (by norm_num)
theorem B1380413 : Blo 1360499 1380413 := bbase (se 3 (by rfl) ⟨258827, by rfl⟩ : syracuseStep 1380413 = 517655) (by norm_num)
theorem B1937477 : Blo 1360499 1937477 := bbase (se 4 (by rfl) ⟨181638, by rfl⟩ : syracuseStep 1937477 = 363277) (by norm_num)
theorem B2584685 : Blo 1360499 2584685 := bbase (se 3 (by rfl) ⟨484628, by rfl⟩ : syracuseStep 2584685 = 969257) (by norm_num)
theorem B3444869 : Blo 1360499 3444869 := bbase (se 4 (by rfl) ⟨322956, by rfl⟩ : syracuseStep 3444869 = 645913) (by norm_num)
theorem B1937557 : Blo 1360499 1937557 := bbase (se 6 (by rfl) ⟨45411, by rfl⟩ : syracuseStep 1937557 = 90823) (by norm_num)
theorem B4591781 : Blo 1360499 4591781 := bbase (se 4 (by rfl) ⟨430479, by rfl⟩ : syracuseStep 4591781 = 860959) (by norm_num)
theorem B2068661 : Blo 1360499 2068661 := bbase (se 5 (by rfl) ⟨96968, by rfl⟩ : syracuseStep 2068661 = 193937) (by norm_num)
theorem B4657333 : Blo 1360499 4657333 := bbase (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) (by norm_num)
theorem B2298037 : Blo 1360499 2298037 := bbase (se 5 (by rfl) ⟨107720, by rfl⟩ : syracuseStep 2298037 = 215441) (by norm_num)
theorem B1454321 : Blo 1360499 1454321 := bbase (se 2 (by rfl) ⟨545370, by rfl⟩ : syracuseStep 1454321 = 1090741) (by norm_num)
theorem B1937677 : Blo 1360499 1937677 := bbase (se 3 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 1937677 = 726629) (by norm_num)
theorem B2298125 : Blo 1360499 2298125 := bbase (se 3 (by rfl) ⟨430898, by rfl⟩ : syracuseStep 2298125 = 861797) (by norm_num)
theorem B6893909 : Blo 1360499 6893909 := bbase (se 10 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 6893909 = 20197) (by norm_num)
theorem B1937773 : Blo 1360499 1937773 := bbase (se 3 (by rfl) ⟨363332, by rfl⟩ : syracuseStep 1937773 = 726665) (by norm_num)
theorem B1634689 : Blo 1360499 1634689 := bbase (se 2 (by rfl) ⟨613008, by rfl⟩ : syracuseStep 1634689 = 1226017) (by norm_num)
theorem B2584973 : Blo 1360499 2584973 := bbase (se 3 (by rfl) ⟨484682, by rfl⟩ : syracuseStep 2584973 = 969365) (by norm_num)
theorem B2298253 : Blo 1360499 2298253 := bbase (se 3 (by rfl) ⟨430922, by rfl⟩ : syracuseStep 2298253 = 861845) (by norm_num)
theorem B3445213 : Blo 1360499 3445213 := bbase (se 3 (by rfl) ⟨645977, by rfl⟩ : syracuseStep 3445213 = 1291955) (by norm_num)
theorem B2298341 : Blo 1360499 2298341 := bbase (se 4 (by rfl) ⟨215469, by rfl⟩ : syracuseStep 2298341 = 430939) (by norm_num)
theorem B11637269 : Blo 1360499 11637269 := bbase (se 6 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 11637269 = 545497) (by norm_num)
theorem B2585125 : Blo 1360499 2585125 := bbase (se 4 (by rfl) ⟨242355, by rfl⟩ : syracuseStep 2585125 = 484711) (by norm_num)
theorem B3445325 : Blo 1360499 3445325 := bbase (se 3 (by rfl) ⟨645998, by rfl⟩ : syracuseStep 3445325 = 1291997) (by norm_num)
theorem B4592213 : Blo 1360499 4592213 := bbase (se 8 (by rfl) ⟨26907, by rfl⟩ : syracuseStep 4592213 = 53815) (by norm_num)
theorem B2298469 : Blo 1360499 2298469 := bbase (se 4 (by rfl) ⟨215481, by rfl⟩ : syracuseStep 2298469 = 430963) (by norm_num)
theorem B1380997 : Blo 1360499 1380997 := bbase (se 4 (by rfl) ⟨129468, by rfl⟩ : syracuseStep 1380997 = 258937) (by norm_num)
theorem B1454765 : Blo 1360499 1454765 := bbase (se 3 (by rfl) ⟨272768, by rfl⟩ : syracuseStep 1454765 = 545537) (by norm_num)
theorem B2486965 : Blo 1360499 2486965 := bbase (se 5 (by rfl) ⟨116576, by rfl⟩ : syracuseStep 2486965 = 233153) (by norm_num)
theorem B2298557 : Blo 1360499 2298557 := bbase (se 3 (by rfl) ⟨430979, by rfl⟩ : syracuseStep 2298557 = 861959) (by norm_num)
theorem B1635073 : Blo 1360499 1635073 := bbase (se 2 (by rfl) ⟨613152, by rfl⟩ : syracuseStep 1635073 = 1226305) (by norm_num)
theorem B3445517 : Blo 1360499 3445517 := bbase (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) (by norm_num)
theorem B2618141 : Blo 1360499 2618141 := bbase (se 3 (by rfl) ⟨490901, by rfl⟩ : syracuseStep 2618141 = 981803) (by norm_num)
theorem B2298685 : Blo 1360499 2298685 := bbase (se 3 (by rfl) ⟨431003, by rfl⟩ : syracuseStep 2298685 = 862007) (by norm_num)
theorem B2585429 : Blo 1360499 2585429 := bbase (se 9 (by rfl) ⟨7574, by rfl⟩ : syracuseStep 2585429 = 15149) (by norm_num)
theorem B1938269 : Blo 1360499 1938269 := bbase (se 3 (by rfl) ⟨363425, by rfl⟩ : syracuseStep 1938269 = 726851) (by norm_num)
theorem B2298773 : Blo 1360499 2298773 := bbase (se 6 (by rfl) ⟨53877, by rfl⟩ : syracuseStep 2298773 = 107755) (by norm_num)
theorem B3879829 : Blo 1360499 3879829 := bbase (se 6 (by rfl) ⟨90933, by rfl⟩ : syracuseStep 3879829 = 181867) (by norm_num)
theorem B5518277 : Blo 1360499 5518277 := bbase (se 4 (by rfl) ⟨517338, by rfl⟩ : syracuseStep 5518277 = 1034677) (by norm_num)
theorem B2618333 : Blo 1360499 2618333 := bbase (se 3 (by rfl) ⟨490937, by rfl⟩ : syracuseStep 2618333 = 981875) (by norm_num)
theorem B4592645 : Blo 1360499 4592645 := bbase (se 4 (by rfl) ⟨430560, by rfl⟩ : syracuseStep 4592645 = 861121) (by norm_num)
theorem B2298901 : Blo 1360499 2298901 := bbase (se 6 (by rfl) ⟨53880, by rfl⟩ : syracuseStep 2298901 = 107761) (by norm_num)
theorem B3445861 : Blo 1360499 3445861 := bbase (se 4 (by rfl) ⟨323049, by rfl⟩ : syracuseStep 3445861 = 646099) (by norm_num)
theorem B2298989 : Blo 1360499 2298989 := bbase (se 3 (by rfl) ⟨431060, by rfl⟩ : syracuseStep 2298989 = 862121) (by norm_num)
theorem B3445973 : Blo 1360499 3445973 := bbase (se 7 (by rfl) ⟨40382, by rfl⟩ : syracuseStep 3445973 = 80765) (by norm_num)
theorem B2299117 : Blo 1360499 2299117 := bbase (se 3 (by rfl) ⟨431084, by rfl⟩ : syracuseStep 2299117 = 862169) (by norm_num)
theorem B5813525 : Blo 1360499 5813525 := bbase (se 6 (by rfl) ⟨136254, by rfl⟩ : syracuseStep 5813525 = 272509) (by norm_num)
theorem B1840421 : Blo 1360499 1840421 := bbase (se 4 (by rfl) ⟨172539, by rfl⟩ : syracuseStep 1840421 = 345079) (by norm_num)
theorem B2299205 : Blo 1360499 2299205 := bbase (se 4 (by rfl) ⟨215550, by rfl⟩ : syracuseStep 2299205 = 431101) (by norm_num)
theorem B1938821 : Blo 1360499 1938821 := bbase (se 4 (by rfl) ⟨181764, by rfl⟩ : syracuseStep 1938821 = 363529) (by norm_num)
theorem B3061133 : Blo 1360499 3061133 := bbase (se 3 (by rfl) ⟨573962, by rfl⟩ : syracuseStep 3061133 = 1147925) (by norm_num)
theorem B3446165 : Blo 1360499 3446165 := bbase (se 6 (by rfl) ⟨80769, by rfl⟩ : syracuseStep 3446165 = 161539) (by norm_num)
theorem B4593077 : Blo 1360499 4593077 := bbase (se 5 (by rfl) ⟨215300, by rfl⟩ : syracuseStep 4593077 = 430601) (by norm_num)
theorem B3061205 : Blo 1360499 3061205 := bbase (se 7 (by rfl) ⟨35873, by rfl⟩ : syracuseStep 3061205 = 71747) (by norm_num)
theorem B8721877 : Blo 1360499 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B4363733 : Blo 1360499 4363733 := bbase (se 7 (by rfl) ⟨51137, by rfl⟩ : syracuseStep 4363733 = 102275) (by norm_num)
theorem B5813765 : Blo 1360499 5813765 := bbase (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) (by norm_num)
theorem B3061277 : Blo 1360499 3061277 := bbase (se 3 (by rfl) ⟨573989, by rfl⟩ : syracuseStep 3061277 = 1147979) (by norm_num)
theorem B2586181 : Blo 1360499 2586181 := bbase (se 4 (by rfl) ⟨242454, by rfl⟩ : syracuseStep 2586181 = 484909) (by norm_num)
theorem B2487901 : Blo 1360499 2487901 := bbase (se 3 (by rfl) ⟨466481, by rfl⟩ : syracuseStep 2487901 = 932963) (by norm_num)
theorem B3061349 : Blo 1360499 3061349 := bbase (se 4 (by rfl) ⟨287001, by rfl⟩ : syracuseStep 3061349 = 574003) (by norm_num)
theorem B6895205 : Blo 1360499 6895205 := bbase (se 4 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 6895205 = 1292851) (by norm_num)
theorem B3929717 : Blo 1360499 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B1635977 : Blo 1360499 1635977 := bbase (se 2 (by rfl) ⟨613491, by rfl⟩ : syracuseStep 1635977 = 1226983) (by norm_num)
theorem B3061421 : Blo 1360499 3061421 := bbase (se 3 (by rfl) ⟨574016, by rfl⟩ : syracuseStep 3061421 = 1148033) (by norm_num)
theorem B5166773 : Blo 1360499 5166773 := bbase (se 5 (by rfl) ⟨242192, by rfl⟩ : syracuseStep 5166773 = 484385) (by norm_num)
theorem B2905789 : Blo 1360499 2905789 := bbase (se 3 (by rfl) ⟨544835, by rfl⟩ : syracuseStep 2905789 = 1089671) (by norm_num)
theorem B2586325 : Blo 1360499 2586325 := bbase (se 7 (by rfl) ⟨30308, by rfl⟩ : syracuseStep 2586325 = 60617) (by norm_num)
theorem B3446509 : Blo 1360499 3446509 := bbase (se 3 (by rfl) ⟨646220, by rfl⟩ : syracuseStep 3446509 = 1292441) (by norm_num)
theorem B3061493 : Blo 1360499 3061493 := bbase (se 5 (by rfl) ⟨143507, by rfl⟩ : syracuseStep 3061493 = 287015) (by norm_num)
theorem B3061565 : Blo 1360499 3061565 := bbase (se 3 (by rfl) ⟨574043, by rfl⟩ : syracuseStep 3061565 = 1148087) (by norm_num)
theorem B14169941 : Blo 1360499 14169941 := bbase (se 9 (by rfl) ⟨41513, by rfl⟩ : syracuseStep 14169941 = 83027) (by norm_num)
theorem B3446621 : Blo 1360499 3446621 := bbase (se 3 (by rfl) ⟨646241, by rfl⟩ : syracuseStep 3446621 = 1292483) (by norm_num)
theorem B4593509 : Blo 1360499 4593509 := bbase (se 4 (by rfl) ⟨430641, by rfl⟩ : syracuseStep 4593509 = 861283) (by norm_num)
theorem B2586485 : Blo 1360499 2586485 := bbase (se 5 (by rfl) ⟨121241, by rfl⟩ : syracuseStep 2586485 = 242483) (by norm_num)
theorem B3061637 : Blo 1360499 3061637 := bbase (se 4 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 3061637 = 574057) (by norm_num)
theorem B1636237 : Blo 1360499 1636237 := bbase (se 3 (by rfl) ⟨306794, by rfl⟩ : syracuseStep 1636237 = 613589) (by norm_num)
theorem B2906045 : Blo 1360499 2906045 := bbase (se 3 (by rfl) ⟨544883, by rfl⟩ : syracuseStep 2906045 = 1089767) (by norm_num)
theorem B3061709 : Blo 1360499 3061709 := bbase (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) (by norm_num)
theorem B5167061 : Blo 1360499 5167061 := bbase (se 7 (by rfl) ⟨60551, by rfl⟩ : syracuseStep 5167061 = 121103) (by norm_num)
theorem B3061781 : Blo 1360499 3061781 := bbase (se 6 (by rfl) ⟨71760, by rfl⟩ : syracuseStep 3061781 = 143521) (by norm_num)
theorem B3446813 : Blo 1360499 3446813 := bbase (se 3 (by rfl) ⟨646277, by rfl⟩ : syracuseStep 3446813 = 1292555) (by norm_num)
theorem B1636429 : Blo 1360499 1636429 := bbase (se 3 (by rfl) ⟨306830, by rfl⟩ : syracuseStep 1636429 = 613661) (by norm_num)
theorem B18626645 : Blo 1360499 18626645 := bbase (se 8 (by rfl) ⟨109140, by rfl⟩ : syracuseStep 18626645 = 218281) (by norm_num)
theorem B3061853 : Blo 1360499 3061853 := bbase (se 3 (by rfl) ⟨574097, by rfl⟩ : syracuseStep 3061853 = 1148195) (by norm_num)
theorem B1636453 : Blo 1360499 1636453 := bbase (se 4 (by rfl) ⟨153417, by rfl⟩ : syracuseStep 1636453 = 306835) (by norm_num)
theorem B1636457 : Blo 1360499 1636457 := bbase (se 2 (by rfl) ⟨613671, by rfl⟩ : syracuseStep 1636457 = 1227343) (by norm_num)
theorem B1939573 : Blo 1360499 1939573 := bbase (se 5 (by rfl) ⟨90917, by rfl⟩ : syracuseStep 1939573 = 181835) (by norm_num)
theorem B1964165 : Blo 1360499 1964165 := bbase (se 4 (by rfl) ⟨184140, by rfl⟩ : syracuseStep 1964165 = 368281) (by norm_num)
theorem B3061925 : Blo 1360499 3061925 := bbase (se 4 (by rfl) ⟨287055, by rfl⟩ : syracuseStep 3061925 = 574111) (by norm_num)
theorem B3061997 : Blo 1360499 3061997 := bbase (se 3 (by rfl) ⟨574124, by rfl⟩ : syracuseStep 3061997 = 1148249) (by norm_num)
theorem B4593941 : Blo 1360499 4593941 := bbase (se 6 (by rfl) ⟨107670, by rfl⟩ : syracuseStep 4593941 = 215341) (by norm_num)
theorem B3062069 : Blo 1360499 3062069 := bbase (se 5 (by rfl) ⟨143534, by rfl⟩ : syracuseStep 3062069 = 287069) (by norm_num)
theorem B5519669 : Blo 1360499 5519669 := bbase (se 5 (by rfl) ⟨258734, by rfl⟩ : syracuseStep 5519669 = 517469) (by norm_num)
theorem B2070893 : Blo 1360499 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B3447157 : Blo 1360499 3447157 := bbase (se 5 (by rfl) ⟨161585, by rfl⟩ : syracuseStep 3447157 = 323171) (by norm_num)
theorem B3062141 : Blo 1360499 3062141 := bbase (se 3 (by rfl) ⟨574151, by rfl⟩ : syracuseStep 3062141 = 1148303) (by norm_num)
theorem B1399205 : Blo 1360499 1399205 := bbase (se 4 (by rfl) ⟨131175, by rfl⟩ : syracuseStep 1399205 = 262351) (by norm_num)
theorem B3062213 : Blo 1360499 3062213 := bbase (se 4 (by rfl) ⟨287082, by rfl⟩ : syracuseStep 3062213 = 574165) (by norm_num)
theorem B3447269 : Blo 1360499 3447269 := bbase (se 4 (by rfl) ⟨323181, by rfl⟩ : syracuseStep 3447269 = 646363) (by norm_num)
theorem B3062285 : Blo 1360499 3062285 := bbase (se 3 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 3062285 = 1148357) (by norm_num)
theorem B3062357 : Blo 1360499 3062357 := bbase (se 8 (by rfl) ⟨17943, by rfl⟩ : syracuseStep 3062357 = 35887) (by norm_num)
theorem B5896789 : Blo 1360499 5896789 := bbase (se 8 (by rfl) ⟨34551, by rfl⟩ : syracuseStep 5896789 = 69103) (by norm_num)
theorem B3062429 : Blo 1360499 3062429 := bbase (se 3 (by rfl) ⟨574205, by rfl⟩ : syracuseStep 3062429 = 1148411) (by norm_num)
theorem B3447461 : Blo 1360499 3447461 := bbase (se 4 (by rfl) ⟨323199, by rfl⟩ : syracuseStep 3447461 = 646399) (by norm_num)
theorem B7756469 : Blo 1360499 7756469 := bbase (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) (by norm_num)
theorem B4594373 : Blo 1360499 4594373 := bbase (se 4 (by rfl) ⟨430722, by rfl⟩ : syracuseStep 4594373 = 861445) (by norm_num)
theorem B1530589 : Blo 1360499 1530589 := bbase (se 3 (by rfl) ⟨286985, by rfl⟩ : syracuseStep 1530589 = 573971) (by norm_num)
theorem B3062501 : Blo 1360499 3062501 := bbase (se 4 (by rfl) ⟨287109, by rfl⟩ : syracuseStep 3062501 = 574219) (by norm_num)
theorem B1530625 : Blo 1360499 1530625 := bbase (se 2 (by rfl) ⟨573984, by rfl⟩ : syracuseStep 1530625 = 1147969) (by norm_num)
theorem B1530661 : Blo 1360499 1530661 := bbase (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) (by norm_num)
theorem B3062573 : Blo 1360499 3062573 := bbase (se 3 (by rfl) ⟨574232, by rfl⟩ : syracuseStep 3062573 = 1148465) (by norm_num)
theorem B2906933 : Blo 1360499 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B1530697 : Blo 1360499 1530697 := bbase (se 2 (by rfl) ⟨574011, by rfl⟩ : syracuseStep 1530697 = 1148023) (by norm_num)
theorem B1456985 : Blo 1360499 1456985 := bbase (se 2 (by rfl) ⟨546369, by rfl⟩ : syracuseStep 1456985 = 1092739) (by norm_num)
theorem B1530733 : Blo 1360499 1530733 := bbase (se 3 (by rfl) ⟨287012, by rfl⟩ : syracuseStep 1530733 = 574025) (by norm_num)
theorem B3062645 : Blo 1360499 3062645 := bbase (se 5 (by rfl) ⟨143561, by rfl⟩ : syracuseStep 3062645 = 287123) (by norm_num)
theorem B6896501 : Blo 1360499 6896501 := bbase (se 5 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 6896501 = 646547) (by norm_num)
theorem B1530769 : Blo 1360499 1530769 := bbase (se 2 (by rfl) ⟨574038, by rfl⟩ : syracuseStep 1530769 = 1148077) (by norm_num)
theorem B1530805 : Blo 1360499 1530805 := bbase (se 5 (by rfl) ⟨71756, by rfl⟩ : syracuseStep 1530805 = 143513) (by norm_num)
theorem B3062717 : Blo 1360499 3062717 := bbase (se 3 (by rfl) ⟨574259, by rfl⟩ : syracuseStep 3062717 = 1148519) (by norm_num)
theorem B1530841 : Blo 1360499 1530841 := bbase (se 2 (by rfl) ⟨574065, by rfl⟩ : syracuseStep 1530841 = 1148131) (by norm_num)
theorem B2948069 : Blo 1360499 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B1530877 : Blo 1360499 1530877 := bbase (se 3 (by rfl) ⟨287039, by rfl⟩ : syracuseStep 1530877 = 574079) (by norm_num)
theorem B3447805 : Blo 1360499 3447805 := bbase (se 3 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 3447805 = 1292927) (by norm_num)
theorem B3062789 : Blo 1360499 3062789 := bbase (se 4 (by rfl) ⟨287136, by rfl⟩ : syracuseStep 3062789 = 574273) (by norm_num)
theorem B1530913 : Blo 1360499 1530913 := bbase (se 2 (by rfl) ⟨574092, by rfl⟩ : syracuseStep 1530913 = 1148185) (by norm_num)
theorem B2907173 : Blo 1360499 2907173 := bbase (se 4 (by rfl) ⟨272547, by rfl⟩ : syracuseStep 2907173 = 545095) (by norm_num)
theorem B1530949 : Blo 1360499 1530949 := bbase (se 4 (by rfl) ⟨143526, by rfl⟩ : syracuseStep 1530949 = 287053) (by norm_num)
theorem B3062861 : Blo 1360499 3062861 := bbase (se 3 (by rfl) ⟨574286, by rfl⟩ : syracuseStep 3062861 = 1148573) (by norm_num)
theorem B1530985 : Blo 1360499 1530985 := bbase (se 2 (by rfl) ⟨574119, by rfl⟩ : syracuseStep 1530985 = 1148239) (by norm_num)
theorem B3447917 : Blo 1360499 3447917 := bbase (se 3 (by rfl) ⟨646484, by rfl⟩ : syracuseStep 3447917 = 1292969) (by norm_num)
theorem B5168245 : Blo 1360499 5168245 := bbase (se 5 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 5168245 = 484523) (by norm_num)
theorem B4594805 : Blo 1360499 4594805 := bbase (se 5 (by rfl) ⟨215381, by rfl⟩ : syracuseStep 4594805 = 430763) (by norm_num)
theorem B1531021 : Blo 1360499 1531021 := bbase (se 3 (by rfl) ⟨287066, by rfl⟩ : syracuseStep 1531021 = 574133) (by norm_num)
theorem B3062933 : Blo 1360499 3062933 := bbase (se 6 (by rfl) ⟨71787, by rfl⟩ : syracuseStep 3062933 = 143575) (by norm_num)
theorem B1531057 : Blo 1360499 1531057 := bbase (se 2 (by rfl) ⟨574146, by rfl⟩ : syracuseStep 1531057 = 1148293) (by norm_num)
theorem B2759869 : Blo 1360499 2759869 := bbase (se 3 (by rfl) ⟨517475, by rfl⟩ : syracuseStep 2759869 = 1034951) (by norm_num)
theorem B14351573 : Blo 1360499 14351573 := bbase (se 7 (by rfl) ⟨168182, by rfl⟩ : syracuseStep 14351573 = 336365) (by norm_num)
theorem B1531093 : Blo 1360499 1531093 := bbase (se 7 (by rfl) ⟨17942, by rfl⟩ : syracuseStep 1531093 = 35885) (by norm_num)
theorem B3063005 : Blo 1360499 3063005 := bbase (se 3 (by rfl) ⟨574313, by rfl⟩ : syracuseStep 3063005 = 1148627) (by norm_num)
theorem B1531129 : Blo 1360499 1531129 := bbase (se 2 (by rfl) ⟨574173, by rfl⟩ : syracuseStep 1531129 = 1148347) (by norm_num)
theorem B2759933 : Blo 1360499 2759933 := bbase (se 3 (by rfl) ⟨517487, by rfl⟩ : syracuseStep 2759933 = 1034975) (by norm_num)
theorem B6888725 : Blo 1360499 6888725 := bbase (se 6 (by rfl) ⟨161454, by rfl⟩ : syracuseStep 6888725 = 322909) (by norm_num)
theorem B1531165 : Blo 1360499 1531165 := bbase (se 3 (by rfl) ⟨287093, by rfl⟩ : syracuseStep 1531165 = 574187) (by norm_num)
theorem B3063077 : Blo 1360499 3063077 := bbase (se 4 (by rfl) ⟨287163, by rfl⟩ : syracuseStep 3063077 = 574327) (by norm_num)
theorem B3448109 : Blo 1360499 3448109 := bbase (se 3 (by rfl) ⟨646520, by rfl⟩ : syracuseStep 3448109 = 1293041) (by norm_num)
theorem B1531201 : Blo 1360499 1531201 := bbase (se 2 (by rfl) ⟨574200, by rfl⟩ : syracuseStep 1531201 = 1148401) (by norm_num)
theorem B1531237 : Blo 1360499 1531237 := bbase (se 4 (by rfl) ⟨143553, by rfl⟩ : syracuseStep 1531237 = 287107) (by norm_num)
theorem B3063149 : Blo 1360499 3063149 := bbase (se 3 (by rfl) ⟨574340, by rfl⟩ : syracuseStep 3063149 = 1148681) (by norm_num)
theorem B1531273 : Blo 1360499 1531273 := bbase (se 2 (by rfl) ⟨574227, by rfl⟩ : syracuseStep 1531273 = 1148455) (by norm_num)
theorem B5168549 : Blo 1360499 5168549 := bbase (se 4 (by rfl) ⟨484551, by rfl⟩ : syracuseStep 5168549 = 969103) (by norm_num)
theorem B1531309 : Blo 1360499 1531309 := bbase (se 3 (by rfl) ⟨287120, by rfl⟩ : syracuseStep 1531309 = 574241) (by norm_num)
theorem B3063221 : Blo 1360499 3063221 := bbase (se 5 (by rfl) ⟨143588, by rfl⟩ : syracuseStep 3063221 = 287177) (by norm_num)
theorem B1531345 : Blo 1360499 1531345 := bbase (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) (by norm_num)
theorem B2211293 : Blo 1360499 2211293 := bbase (se 3 (by rfl) ⟨414617, by rfl⟩ : syracuseStep 2211293 = 829235) (by norm_num)
theorem B1531381 : Blo 1360499 1531381 := bbase (se 5 (by rfl) ⟨71783, by rfl⟩ : syracuseStep 1531381 = 143567) (by norm_num)
theorem B3063293 : Blo 1360499 3063293 := bbase (se 3 (by rfl) ⟨574367, by rfl⟩ : syracuseStep 3063293 = 1148735) (by norm_num)
theorem B1531417 : Blo 1360499 1531417 := bbase (se 2 (by rfl) ⟨574281, by rfl⟩ : syracuseStep 1531417 = 1148563) (by norm_num)
theorem B2907677 : Blo 1360499 2907677 := bbase (se 3 (by rfl) ⟨545189, by rfl⟩ : syracuseStep 2907677 = 1090379) (by norm_num)
theorem B2907685 : Blo 1360499 2907685 := bbase (se 4 (by rfl) ⟨272595, by rfl⟩ : syracuseStep 2907685 = 545191) (by norm_num)
theorem B4595237 : Blo 1360499 4595237 := bbase (se 4 (by rfl) ⟨430803, by rfl⟩ : syracuseStep 4595237 = 861607) (by norm_num)
theorem B1531453 : Blo 1360499 1531453 := bbase (se 3 (by rfl) ⟨287147, by rfl⟩ : syracuseStep 1531453 = 574295) (by norm_num)
theorem B3063365 : Blo 1360499 3063365 := bbase (se 4 (by rfl) ⟨287190, by rfl⟩ : syracuseStep 3063365 = 574381) (by norm_num)
theorem B1531489 : Blo 1360499 1531489 := bbase (se 2 (by rfl) ⟨574308, by rfl⟩ : syracuseStep 1531489 = 1148617) (by norm_num)
theorem B3677813 : Blo 1360499 3677813 := bbase (se 5 (by rfl) ⟨172397, by rfl⟩ : syracuseStep 3677813 = 344795) (by norm_num)
theorem B1531525 : Blo 1360499 1531525 := bbase (se 4 (by rfl) ⟨143580, by rfl⟩ : syracuseStep 1531525 = 287161) (by norm_num)
theorem B6987397 : Blo 1360499 6987397 := bbase (se 4 (by rfl) ⟨655068, by rfl⟩ : syracuseStep 6987397 = 1310137) (by norm_num)
theorem B3448453 : Blo 1360499 3448453 := bbase (se 4 (by rfl) ⟨323292, by rfl⟩ : syracuseStep 3448453 = 646585) (by norm_num)
theorem B3063437 : Blo 1360499 3063437 := bbase (se 3 (by rfl) ⟨574394, by rfl⟩ : syracuseStep 3063437 = 1148789) (by norm_num)
theorem B1531561 : Blo 1360499 1531561 := bbase (se 2 (by rfl) ⟨574335, by rfl⟩ : syracuseStep 1531561 = 1148671) (by norm_num)
theorem B1531597 : Blo 1360499 1531597 := bbase (se 3 (by rfl) ⟨287174, by rfl⟩ : syracuseStep 1531597 = 574349) (by norm_num)
theorem B22068949 : Blo 1360499 22068949 := bbase (se 7 (by rfl) ⟨258620, by rfl⟩ : syracuseStep 22068949 = 517241) (by norm_num)
theorem B3063509 : Blo 1360499 3063509 := bbase (se 7 (by rfl) ⟨35900, by rfl⟩ : syracuseStep 3063509 = 71801) (by norm_num)
theorem B1531633 : Blo 1360499 1531633 := bbase (se 2 (by rfl) ⟨574362, by rfl⟩ : syracuseStep 1531633 = 1148725) (by norm_num)
theorem B5816053 : Blo 1360499 5816053 := bbase (se 5 (by rfl) ⟨272627, by rfl⟩ : syracuseStep 5816053 = 545255) (by norm_num)
theorem B3448565 : Blo 1360499 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B1531669 : Blo 1360499 1531669 := bbase (se 6 (by rfl) ⟨35898, by rfl⟩ : syracuseStep 1531669 = 71797) (by norm_num)
theorem B3063581 : Blo 1360499 3063581 := bbase (se 3 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 3063581 = 1148843) (by norm_num)
theorem B1531705 : Blo 1360499 1531705 := bbase (se 2 (by rfl) ⟨574389, by rfl⟩ : syracuseStep 1531705 = 1148779) (by norm_num)
theorem B7757653 : Blo 1360499 7757653 := bbase (se 9 (by rfl) ⟨22727, by rfl⟩ : syracuseStep 7757653 = 45455) (by norm_num)
theorem B1531741 : Blo 1360499 1531741 := bbase (se 3 (by rfl) ⟨287201, by rfl⟩ : syracuseStep 1531741 = 574403) (by norm_num)
theorem B3063653 : Blo 1360499 3063653 := bbase (se 4 (by rfl) ⟨287217, by rfl⟩ : syracuseStep 3063653 = 574435) (by norm_num)
theorem B1531777 : Blo 1360499 1531777 := bbase (se 2 (by rfl) ⟨574416, by rfl⟩ : syracuseStep 1531777 = 1148833) (by norm_num)
theorem B3104669 : Blo 1360499 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B1531813 : Blo 1360499 1531813 := bbase (se 4 (by rfl) ⟨143607, by rfl⟩ : syracuseStep 1531813 = 287215) (by norm_num)
theorem B3063725 : Blo 1360499 3063725 := bbase (se 3 (by rfl) ⟨574448, by rfl⟩ : syracuseStep 3063725 = 1148897) (by norm_num)
theorem B3448757 : Blo 1360499 3448757 := bbase (se 5 (by rfl) ⟨161660, by rfl⟩ : syracuseStep 3448757 = 323321) (by norm_num)
theorem B1531849 : Blo 1360499 1531849 := bbase (se 2 (by rfl) ⟨574443, by rfl⟩ : syracuseStep 1531849 = 1148887) (by norm_num)
theorem B4595669 : Blo 1360499 4595669 := bbase (se 7 (by rfl) ⟨53855, by rfl⟩ : syracuseStep 4595669 = 107711) (by norm_num)
theorem B10346453 : Blo 1360499 10346453 := bbase (se 7 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 10346453 = 242495) (by norm_num)
theorem B1531885 : Blo 1360499 1531885 := bbase (se 3 (by rfl) ⟨287228, by rfl⟩ : syracuseStep 1531885 = 574457) (by norm_num)
theorem B3063797 : Blo 1360499 3063797 := bbase (se 5 (by rfl) ⟨143615, by rfl⟩ : syracuseStep 3063797 = 287231) (by norm_num)
theorem B7364621 : Blo 1360499 7364621 := bstep (se 3 (by rfl) ⟨1380866, by rfl⟩ : syracuseStep 7364621 = 2761733) B2761733
theorem B1531939 : Blo 1360499 1531939 := bstep (se 1 (by rfl) ⟨1148954, by rfl⟩ : syracuseStep 1531939 = 2297909) B2297909
theorem B29835317 : Blo 1360499 29835317 := bstep (se 5 (by rfl) ⟨1398530, by rfl⟩ : syracuseStep 29835317 = 2797061) B2797061
theorem B4595885 : Blo 1360499 4595885 := bstep (se 3 (by rfl) ⟨861728, by rfl⟩ : syracuseStep 4595885 = 1723457) B1723457
theorem B1532083 : Blo 1360499 1532083 := bstep (se 1 (by rfl) ⟨1149062, by rfl⟩ : syracuseStep 1532083 = 2298125) B2298125
theorem B4595939 : Blo 1360499 4595939 := bstep (se 1 (by rfl) ⟨3446954, by rfl⟩ : syracuseStep 4595939 = 6893909) B6893909
theorem B6209777 : Blo 1360499 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B3064049 : Blo 1360499 3064049 := bstep (se 2 (by rfl) ⟨1149018, by rfl⟩ : syracuseStep 3064049 = 2298037) B2298037
theorem B3064067 : Blo 1360499 3064067 := bstep (se 1 (by rfl) ⟨2298050, by rfl⟩ : syracuseStep 3064067 = 4596101) B4596101
theorem B1532227 : Blo 1360499 1532227 := bstep (se 1 (by rfl) ⟨1149170, by rfl⟩ : syracuseStep 1532227 = 2298341) B2298341
theorem B4194659 : Blo 1360499 4194659 := bstep (se 1 (by rfl) ⟨3145994, by rfl⟩ : syracuseStep 4194659 = 6291989) B6291989
theorem B7758179 : Blo 1360499 7758179 := bstep (se 1 (by rfl) ⟨5818634, by rfl⟩ : syracuseStep 7758179 = 11637269) B11637269
theorem B5169521 : Blo 1360499 5169521 := bstep (se 2 (by rfl) ⟨1938570, by rfl⟩ : syracuseStep 5169521 = 3877141) B3877141
theorem B4907441 : Blo 1360499 4907441 := bstep (se 2 (by rfl) ⟨1840290, by rfl⟩ : syracuseStep 4907441 = 3680581) B3680581
theorem B31449541 : Blo 1360499 31449541 := bstep (se 4 (by rfl) ⟨2948394, by rfl⟩ : syracuseStep 31449541 = 5896789) B5896789
theorem B1532371 : Blo 1360499 1532371 := bstep (se 1 (by rfl) ⟨1149278, by rfl⟩ : syracuseStep 1532371 = 2298557) B2298557
theorem B4596209 : Blo 1360499 4596209 := bstep (se 2 (by rfl) ⟨1723578, by rfl⟩ : syracuseStep 4596209 = 3447157) B3447157
theorem B2179585 : Blo 1360499 2179585 := bstep (se 2 (by rfl) ⟨817344, by rfl⟩ : syracuseStep 2179585 = 1634689) B1634689
theorem B3064337 : Blo 1360499 3064337 := bstep (se 2 (by rfl) ⟨1149126, by rfl⟩ : syracuseStep 3064337 = 2298253) B2298253
theorem B3064355 : Blo 1360499 3064355 := bstep (se 1 (by rfl) ⟨2298266, by rfl⟩ : syracuseStep 3064355 = 4596533) B4596533
theorem B58876469 : Blo 1360499 58876469 := bstep (se 5 (by rfl) ⟨2759834, by rfl⟩ : syracuseStep 58876469 = 5519669) B5519669
theorem B1532515 : Blo 1360499 1532515 := bstep (se 1 (by rfl) ⟨1149386, by rfl⟩ : syracuseStep 1532515 = 2298773) B2298773
theorem B1360499 : Blo 1360499 1360499 := bstep (se 1 (by rfl) ⟨1020374, by rfl⟩ : syracuseStep 1360499 = 2040749) B2040749
theorem B1360515 : Blo 1360499 1360515 := bstep (se 1 (by rfl) ⟨1020386, by rfl⟩ : syracuseStep 1360515 = 2040773) B2040773
theorem B3678851 : Blo 1360499 3678851 := bstep (se 1 (by rfl) ⟨2759138, by rfl⟩ : syracuseStep 3678851 = 5518277) B5518277
theorem B1360531 : Blo 1360499 1360531 := bstep (se 1 (by rfl) ⟨1020398, by rfl⟩ : syracuseStep 1360531 = 2040797) B2040797
theorem B1745555 : Blo 1360499 1745555 := bstep (se 1 (by rfl) ⟨1309166, by rfl⟩ : syracuseStep 1745555 = 2618333) B2618333
theorem B1360547 : Blo 1360499 1360547 := bstep (se 1 (by rfl) ⟨1020410, by rfl⟩ : syracuseStep 1360547 = 2040821) B2040821
theorem B3875501 : Blo 1360499 3875501 := bstep (se 3 (by rfl) ⟨726656, by rfl⟩ : syracuseStep 3875501 = 1453313) B1453313
theorem B1360563 : Blo 1360499 1360563 := bstep (se 1 (by rfl) ⟨1020422, by rfl⟩ : syracuseStep 1360563 = 2040845) B2040845
theorem B1360579 : Blo 1360499 1360579 := bstep (se 1 (by rfl) ⟨1020434, by rfl⟩ : syracuseStep 1360579 = 2040869) B2040869
theorem B1360595 : Blo 1360499 1360595 := bstep (se 1 (by rfl) ⟨1020446, by rfl⟩ : syracuseStep 1360595 = 2040893) B2040893
theorem B1360611 : Blo 1360499 1360611 := bstep (se 1 (by rfl) ⟨1020458, by rfl⟩ : syracuseStep 1360611 = 2040917) B2040917
theorem B1360627 : Blo 1360499 1360627 := bstep (se 1 (by rfl) ⟨1020470, by rfl⟩ : syracuseStep 1360627 = 2040941) B2040941
theorem B1532659 : Blo 1360499 1532659 := bstep (se 1 (by rfl) ⟨1149494, by rfl⟩ : syracuseStep 1532659 = 2298989) B2298989
theorem B2327297 : Blo 1360499 2327297 := bstep (se 2 (by rfl) ⟨872736, by rfl⟩ : syracuseStep 2327297 = 1745473) B1745473
theorem B1360643 : Blo 1360499 1360643 := bstep (se 1 (by rfl) ⟨1020482, by rfl⟩ : syracuseStep 1360643 = 2040965) B2040965
theorem B4907789 : Blo 1360499 4907789 := bstep (se 3 (by rfl) ⟨920210, by rfl⟩ : syracuseStep 4907789 = 1840421) B1840421
theorem B1360659 : Blo 1360499 1360659 := bstep (se 1 (by rfl) ⟨1020494, by rfl⟩ : syracuseStep 1360659 = 2040989) B2040989
theorem B1360675 : Blo 1360499 1360675 := bstep (se 1 (by rfl) ⟨1020506, by rfl⟩ : syracuseStep 1360675 = 2041013) B2041013
theorem B3064625 : Blo 1360499 3064625 := bstep (se 2 (by rfl) ⟨1149234, by rfl⟩ : syracuseStep 3064625 = 2298469) B2298469
theorem B1360691 : Blo 1360499 1360691 := bstep (se 1 (by rfl) ⟨1020518, by rfl⟩ : syracuseStep 1360691 = 2041037) B2041037
theorem B1360707 : Blo 1360499 1360707 := bstep (se 1 (by rfl) ⟨1020530, by rfl⟩ : syracuseStep 1360707 = 2041061) B2041061
theorem B3064643 : Blo 1360499 3064643 := bstep (se 1 (by rfl) ⟨2298482, by rfl⟩ : syracuseStep 3064643 = 4596965) B4596965
theorem B1360723 : Blo 1360499 1360723 := bstep (se 1 (by rfl) ⟨1020542, by rfl⟩ : syracuseStep 1360723 = 2041085) B2041085
theorem B1360739 : Blo 1360499 1360739 := bstep (se 1 (by rfl) ⟨1020554, by rfl⟩ : syracuseStep 1360739 = 2041109) B2041109
theorem B3875683 : Blo 1360499 3875683 := bstep (se 1 (by rfl) ⟨2906762, by rfl⟩ : syracuseStep 3875683 = 5813525) B5813525
theorem B1360755 : Blo 1360499 1360755 := bstep (se 1 (by rfl) ⟨1020566, by rfl⟩ : syracuseStep 1360755 = 2041133) B2041133
theorem B1360771 : Blo 1360499 1360771 := bstep (se 1 (by rfl) ⟨1020578, by rfl⟩ : syracuseStep 1360771 = 2041157) B2041157
theorem B1532803 : Blo 1360499 1532803 := bstep (se 1 (by rfl) ⟨1149602, by rfl⟩ : syracuseStep 1532803 = 2299205) B2299205
theorem B1360787 : Blo 1360499 1360787 := bstep (se 1 (by rfl) ⟨1020590, by rfl⟩ : syracuseStep 1360787 = 2041181) B2041181
theorem B1360803 : Blo 1360499 1360803 := bstep (se 1 (by rfl) ⟨1020602, by rfl⟩ : syracuseStep 1360803 = 2041205) B2041205
theorem B2040755 : Blo 1360499 2040755 := bstep (se 1 (by rfl) ⟨1530566, by rfl⟩ : syracuseStep 2040755 = 3061133) B3061133
theorem B1360819 : Blo 1360499 1360819 := bstep (se 1 (by rfl) ⟨1020614, by rfl⟩ : syracuseStep 1360819 = 2041229) B2041229
theorem B1360835 : Blo 1360499 1360835 := bstep (se 1 (by rfl) ⟨1020626, by rfl⟩ : syracuseStep 1360835 = 2041253) B2041253
theorem B5522381 : Blo 1360499 5522381 := bstep (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) B2070893
theorem B2040785 : Blo 1360499 2040785 := bstep (se 2 (by rfl) ⟨765294, by rfl⟩ : syracuseStep 2040785 = 1530589) B1530589
theorem B1360851 : Blo 1360499 1360851 := bstep (se 1 (by rfl) ⟨1020638, by rfl⟩ : syracuseStep 1360851 = 2041277) B2041277
theorem B2040803 : Blo 1360499 2040803 := bstep (se 1 (by rfl) ⟨1530602, by rfl⟩ : syracuseStep 2040803 = 3061205) B3061205
theorem B1360867 : Blo 1360499 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B2909155 : Blo 1360499 2909155 := bstep (se 1 (by rfl) ⟨2181866, by rfl⟩ : syracuseStep 2909155 = 4363733) B4363733
theorem B1360883 : Blo 1360499 1360883 := bstep (se 1 (by rfl) ⟨1020662, by rfl⟩ : syracuseStep 1360883 = 2041325) B2041325
theorem B2040833 : Blo 1360499 2040833 := bstep (se 2 (by rfl) ⟨765312, by rfl⟩ : syracuseStep 2040833 = 1530625) B1530625
theorem B1360899 : Blo 1360499 1360899 := bstep (se 1 (by rfl) ⟨1020674, by rfl⟩ : syracuseStep 1360899 = 2041349) B2041349
theorem B3875843 : Blo 1360499 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B5170189 : Blo 1360499 5170189 := bstep (se 3 (by rfl) ⟨969410, by rfl⟩ : syracuseStep 5170189 = 1938821) B1938821
theorem B4596749 : Blo 1360499 4596749 := bstep (se 3 (by rfl) ⟨861890, by rfl⟩ : syracuseStep 4596749 = 1723781) B1723781
theorem B2040851 : Blo 1360499 2040851 := bstep (se 1 (by rfl) ⟨1530638, by rfl⟩ : syracuseStep 2040851 = 3061277) B3061277
theorem B1360915 : Blo 1360499 1360915 := bstep (se 1 (by rfl) ⟨1020686, by rfl⟩ : syracuseStep 1360915 = 2041373) B2041373
theorem B1360931 : Blo 1360499 1360931 := bstep (se 1 (by rfl) ⟨1020698, by rfl⟩ : syracuseStep 1360931 = 2041397) B2041397
theorem B2040881 : Blo 1360499 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B1360947 : Blo 1360499 1360947 := bstep (se 1 (by rfl) ⟨1020710, by rfl⟩ : syracuseStep 1360947 = 2041421) B2041421
theorem B2040899 : Blo 1360499 2040899 := bstep (se 1 (by rfl) ⟨1530674, by rfl⟩ : syracuseStep 2040899 = 3061349) B3061349
theorem B1360963 : Blo 1360499 1360963 := bstep (se 1 (by rfl) ⟨1020722, by rfl⟩ : syracuseStep 1360963 = 2041445) B2041445
theorem B4596803 : Blo 1360499 4596803 := bstep (se 1 (by rfl) ⟨3447602, by rfl⟩ : syracuseStep 4596803 = 6895205) B6895205
theorem B3064913 : Blo 1360499 3064913 := bstep (se 2 (by rfl) ⟨1149342, by rfl⟩ : syracuseStep 3064913 = 2298685) B2298685
theorem B1360979 : Blo 1360499 1360979 := bstep (se 1 (by rfl) ⟨1020734, by rfl⟩ : syracuseStep 1360979 = 2041469) B2041469
theorem B2040929 : Blo 1360499 2040929 := bstep (se 2 (by rfl) ⟨765348, by rfl⟩ : syracuseStep 2040929 = 1530697) B1530697
theorem B1360995 : Blo 1360499 1360995 := bstep (se 1 (by rfl) ⟨1020746, by rfl⟩ : syracuseStep 1360995 = 2041493) B2041493
theorem B3064931 : Blo 1360499 3064931 := bstep (se 1 (by rfl) ⟨2298698, by rfl⟩ : syracuseStep 3064931 = 4597397) B4597397
theorem B2040947 : Blo 1360499 2040947 := bstep (se 1 (by rfl) ⟨1530710, by rfl⟩ : syracuseStep 2040947 = 3061421) B3061421
theorem B1361011 : Blo 1360499 1361011 := bstep (se 1 (by rfl) ⟨1020758, by rfl⟩ : syracuseStep 1361011 = 2041517) B2041517
theorem B1361027 : Blo 1360499 1361027 := bstep (se 1 (by rfl) ⟨1020770, by rfl⟩ : syracuseStep 1361027 = 2041541) B2041541
theorem B2040977 : Blo 1360499 2040977 := bstep (se 2 (by rfl) ⟨765366, by rfl⟩ : syracuseStep 2040977 = 1530733) B1530733
theorem B1361043 : Blo 1360499 1361043 := bstep (se 1 (by rfl) ⟨1020782, by rfl⟩ : syracuseStep 1361043 = 2041565) B2041565
theorem B2040995 : Blo 1360499 2040995 := bstep (se 1 (by rfl) ⟨1530746, by rfl⟩ : syracuseStep 2040995 = 3061493) B3061493
theorem B1361059 : Blo 1360499 1361059 := bstep (se 1 (by rfl) ⟨1020794, by rfl⟩ : syracuseStep 1361059 = 2041589) B2041589
theorem B1361075 : Blo 1360499 1361075 := bstep (se 1 (by rfl) ⟨1020806, by rfl⟩ : syracuseStep 1361075 = 2041613) B2041613
theorem B2041025 : Blo 1360499 2041025 := bstep (se 2 (by rfl) ⟨765384, by rfl⟩ : syracuseStep 2041025 = 1530769) B1530769
theorem B1361091 : Blo 1360499 1361091 := bstep (se 1 (by rfl) ⟨1020818, by rfl⟩ : syracuseStep 1361091 = 2041637) B2041637
theorem B2041043 : Blo 1360499 2041043 := bstep (se 1 (by rfl) ⟨1530782, by rfl⟩ : syracuseStep 2041043 = 3061565) B3061565
theorem B1361107 : Blo 1360499 1361107 := bstep (se 1 (by rfl) ⟨1020830, by rfl⟩ : syracuseStep 1361107 = 2041661) B2041661
theorem B1361123 : Blo 1360499 1361123 := bstep (se 1 (by rfl) ⟨1020842, by rfl⟩ : syracuseStep 1361123 = 2041685) B2041685
theorem B9446627 : Blo 1360499 9446627 := bstep (se 1 (by rfl) ⟨7084970, by rfl⟩ : syracuseStep 9446627 = 14169941) B14169941
theorem B2041073 : Blo 1360499 2041073 := bstep (se 2 (by rfl) ⟨765402, by rfl⟩ : syracuseStep 2041073 = 1530805) B1530805
theorem B1361139 : Blo 1360499 1361139 := bstep (se 1 (by rfl) ⟨1020854, by rfl⟩ : syracuseStep 1361139 = 2041709) B2041709
theorem B2041091 : Blo 1360499 2041091 := bstep (se 1 (by rfl) ⟨1530818, by rfl⟩ : syracuseStep 2041091 = 3061637) B3061637
theorem B1361155 : Blo 1360499 1361155 := bstep (se 1 (by rfl) ⟨1020866, by rfl⟩ : syracuseStep 1361155 = 2041733) B2041733
theorem B1361171 : Blo 1360499 1361171 := bstep (se 1 (by rfl) ⟨1020878, by rfl⟩ : syracuseStep 1361171 = 2041757) B2041757
theorem B33596693 : Blo 1360499 33596693 := bstep (se 6 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 33596693 = 1574845) B1574845
theorem B2041121 : Blo 1360499 2041121 := bstep (se 2 (by rfl) ⟨765420, by rfl⟩ : syracuseStep 2041121 = 1530841) B1530841
theorem B1361187 : Blo 1360499 1361187 := bstep (se 1 (by rfl) ⟨1020890, by rfl⟩ : syracuseStep 1361187 = 2041781) B2041781
theorem B2041139 : Blo 1360499 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B1361203 : Blo 1360499 1361203 := bstep (se 1 (by rfl) ⟨1020902, by rfl⟩ : syracuseStep 1361203 = 2041805) B2041805
theorem B1361219 : Blo 1360499 1361219 := bstep (se 1 (by rfl) ⟨1020914, by rfl⟩ : syracuseStep 1361219 = 2041829) B2041829
theorem B2041169 : Blo 1360499 2041169 := bstep (se 2 (by rfl) ⟨765438, by rfl⟩ : syracuseStep 2041169 = 1530877) B1530877
theorem B4597073 : Blo 1360499 4597073 := bstep (se 2 (by rfl) ⟨1723902, by rfl⟩ : syracuseStep 4597073 = 3447805) B3447805
theorem B1361235 : Blo 1360499 1361235 := bstep (se 1 (by rfl) ⟨1020926, by rfl⟩ : syracuseStep 1361235 = 2041853) B2041853
theorem B2041187 : Blo 1360499 2041187 := bstep (se 1 (by rfl) ⟨1530890, by rfl⟩ : syracuseStep 2041187 = 3061781) B3061781
theorem B1361251 : Blo 1360499 1361251 := bstep (se 1 (by rfl) ⟨1020938, by rfl⟩ : syracuseStep 1361251 = 2041877) B2041877
theorem B3065201 : Blo 1360499 3065201 := bstep (se 2 (by rfl) ⟨1149450, by rfl⟩ : syracuseStep 3065201 = 2298901) B2298901
theorem B1361267 : Blo 1360499 1361267 := bstep (se 1 (by rfl) ⟨1020950, by rfl⟩ : syracuseStep 1361267 = 2041901) B2041901
theorem B2041217 : Blo 1360499 2041217 := bstep (se 2 (by rfl) ⟨765456, by rfl⟩ : syracuseStep 2041217 = 1530913) B1530913
theorem B1361283 : Blo 1360499 1361283 := bstep (se 1 (by rfl) ⟨1020962, by rfl⟩ : syracuseStep 1361283 = 2041925) B2041925
theorem B3065219 : Blo 1360499 3065219 := bstep (se 1 (by rfl) ⟨2298914, by rfl⟩ : syracuseStep 3065219 = 4597829) B4597829
theorem B2041235 : Blo 1360499 2041235 := bstep (se 1 (by rfl) ⟨1530926, by rfl⟩ : syracuseStep 2041235 = 3061853) B3061853
theorem B1361299 : Blo 1360499 1361299 := bstep (se 1 (by rfl) ⟨1020974, by rfl⟩ : syracuseStep 1361299 = 2041949) B2041949
theorem B1361315 : Blo 1360499 1361315 := bstep (se 1 (by rfl) ⟨1020986, by rfl⟩ : syracuseStep 1361315 = 2041973) B2041973
theorem B2041265 : Blo 1360499 2041265 := bstep (se 2 (by rfl) ⟨765474, by rfl⟩ : syracuseStep 2041265 = 1530949) B1530949
theorem B1361331 : Blo 1360499 1361331 := bstep (se 1 (by rfl) ⟨1020998, by rfl⟩ : syracuseStep 1361331 = 2041997) B2041997
theorem B2041283 : Blo 1360499 2041283 := bstep (se 1 (by rfl) ⟨1530962, by rfl⟩ : syracuseStep 2041283 = 3061925) B3061925
theorem B1361347 : Blo 1360499 1361347 := bstep (se 1 (by rfl) ⟨1021010, by rfl⟩ : syracuseStep 1361347 = 2042021) B2042021
theorem B1361363 : Blo 1360499 1361363 := bstep (se 1 (by rfl) ⟨1021022, by rfl⟩ : syracuseStep 1361363 = 2042045) B2042045
theorem B2041313 : Blo 1360499 2041313 := bstep (se 2 (by rfl) ⟨765492, by rfl⟩ : syracuseStep 2041313 = 1530985) B1530985
theorem B1361379 : Blo 1360499 1361379 := bstep (se 1 (by rfl) ⟨1021034, by rfl⟩ : syracuseStep 1361379 = 2042069) B2042069
theorem B6890993 : Blo 1360499 6890993 := bstep (se 2 (by rfl) ⟨2584122, by rfl⟩ : syracuseStep 6890993 = 5168245) B5168245
theorem B2041331 : Blo 1360499 2041331 := bstep (se 1 (by rfl) ⟨1530998, by rfl⟩ : syracuseStep 2041331 = 3061997) B3061997
theorem B1361395 : Blo 1360499 1361395 := bstep (se 1 (by rfl) ⟨1021046, by rfl⟩ : syracuseStep 1361395 = 2042093) B2042093
theorem B4359683 : Blo 1360499 4359683 := bstep (se 1 (by rfl) ⟨3269762, by rfl⟩ : syracuseStep 4359683 = 6539525) B6539525
theorem B1361411 : Blo 1360499 1361411 := bstep (se 1 (by rfl) ⟨1021058, by rfl⟩ : syracuseStep 1361411 = 2042117) B2042117
theorem B2041361 : Blo 1360499 2041361 := bstep (se 2 (by rfl) ⟨765510, by rfl⟩ : syracuseStep 2041361 = 1531021) B1531021
theorem B1361427 : Blo 1360499 1361427 := bstep (se 1 (by rfl) ⟨1021070, by rfl⟩ : syracuseStep 1361427 = 2042141) B2042141
theorem B2041379 : Blo 1360499 2041379 := bstep (se 1 (by rfl) ⟨1531034, by rfl⟩ : syracuseStep 2041379 = 3062069) B3062069
theorem B1361443 : Blo 1360499 1361443 := bstep (se 1 (by rfl) ⟨1021082, by rfl⟩ : syracuseStep 1361443 = 2042165) B2042165
theorem B2328113 : Blo 1360499 2328113 := bstep (se 2 (by rfl) ⟨873042, by rfl⟩ : syracuseStep 2328113 = 1746085) B1746085
theorem B1361459 : Blo 1360499 1361459 := bstep (se 1 (by rfl) ⟨1021094, by rfl⟩ : syracuseStep 1361459 = 2042189) B2042189
theorem B2041409 : Blo 1360499 2041409 := bstep (se 2 (by rfl) ⟨765528, by rfl⟩ : syracuseStep 2041409 = 1531057) B1531057
theorem B2180675 : Blo 1360499 2180675 := bstep (se 1 (by rfl) ⟨1635506, by rfl⟩ : syracuseStep 2180675 = 3271013) B3271013
theorem B1361475 : Blo 1360499 1361475 := bstep (se 1 (by rfl) ⟨1021106, by rfl⟩ : syracuseStep 1361475 = 2042213) B2042213
theorem B3679825 : Blo 1360499 3679825 := bstep (se 2 (by rfl) ⟨1379934, by rfl⟩ : syracuseStep 3679825 = 2759869) B2759869
theorem B2041427 : Blo 1360499 2041427 := bstep (se 1 (by rfl) ⟨1531070, by rfl⟩ : syracuseStep 2041427 = 3062141) B3062141
theorem B1361491 : Blo 1360499 1361491 := bstep (se 1 (by rfl) ⟨1021118, by rfl⟩ : syracuseStep 1361491 = 2042237) B2042237
theorem B1361507 : Blo 1360499 1361507 := bstep (se 1 (by rfl) ⟨1021130, by rfl⟩ : syracuseStep 1361507 = 2042261) B2042261
theorem B2041457 : Blo 1360499 2041457 := bstep (se 2 (by rfl) ⟨765546, by rfl⟩ : syracuseStep 2041457 = 1531093) B1531093
theorem B1361523 : Blo 1360499 1361523 := bstep (se 1 (by rfl) ⟨1021142, by rfl⟩ : syracuseStep 1361523 = 2042285) B2042285
theorem B2041475 : Blo 1360499 2041475 := bstep (se 1 (by rfl) ⟨1531106, by rfl⟩ : syracuseStep 2041475 = 3062213) B3062213
theorem B1361539 : Blo 1360499 1361539 := bstep (se 1 (by rfl) ⟨1021154, by rfl⟩ : syracuseStep 1361539 = 2042309) B2042309
theorem B3065489 : Blo 1360499 3065489 := bstep (se 2 (by rfl) ⟨1149558, by rfl⟩ : syracuseStep 3065489 = 2299117) B2299117
theorem B1361555 : Blo 1360499 1361555 := bstep (se 1 (by rfl) ⟨1021166, by rfl⟩ : syracuseStep 1361555 = 2042333) B2042333
theorem B2041505 : Blo 1360499 2041505 := bstep (se 2 (by rfl) ⟨765564, by rfl⟩ : syracuseStep 2041505 = 1531129) B1531129
theorem B1361571 : Blo 1360499 1361571 := bstep (se 1 (by rfl) ⟨1021178, by rfl⟩ : syracuseStep 1361571 = 2042357) B2042357
theorem B3065507 : Blo 1360499 3065507 := bstep (se 1 (by rfl) ⟨2299130, by rfl⟩ : syracuseStep 3065507 = 4598261) B4598261
theorem B2041523 : Blo 1360499 2041523 := bstep (se 1 (by rfl) ⟨1531142, by rfl⟩ : syracuseStep 2041523 = 3062285) B3062285
theorem B1361587 : Blo 1360499 1361587 := bstep (se 1 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 1361587 = 2042381) B2042381
theorem B1361603 : Blo 1360499 1361603 := bstep (se 1 (by rfl) ⟨1021202, by rfl⟩ : syracuseStep 1361603 = 2042405) B2042405
theorem B2041553 : Blo 1360499 2041553 := bstep (se 2 (by rfl) ⟨765582, by rfl⟩ : syracuseStep 2041553 = 1531165) B1531165
theorem B1361619 : Blo 1360499 1361619 := bstep (se 1 (by rfl) ⟨1021214, by rfl⟩ : syracuseStep 1361619 = 2042429) B2042429
theorem B2041571 : Blo 1360499 2041571 := bstep (se 1 (by rfl) ⟨1531178, by rfl⟩ : syracuseStep 2041571 = 3062357) B3062357
theorem B1361635 : Blo 1360499 1361635 := bstep (se 1 (by rfl) ⟨1021226, by rfl⟩ : syracuseStep 1361635 = 2042453) B2042453
theorem B1361651 : Blo 1360499 1361651 := bstep (se 1 (by rfl) ⟨1021238, by rfl⟩ : syracuseStep 1361651 = 2042477) B2042477
theorem B2041601 : Blo 1360499 2041601 := bstep (se 2 (by rfl) ⟨765600, by rfl⟩ : syracuseStep 2041601 = 1531201) B1531201
theorem B1361667 : Blo 1360499 1361667 := bstep (se 1 (by rfl) ⟨1021250, by rfl⟩ : syracuseStep 1361667 = 2042501) B2042501
theorem B2041619 : Blo 1360499 2041619 := bstep (se 1 (by rfl) ⟨1531214, by rfl⟩ : syracuseStep 2041619 = 3062429) B3062429
theorem B1361683 : Blo 1360499 1361683 := bstep (se 1 (by rfl) ⟨1021262, by rfl⟩ : syracuseStep 1361683 = 2042525) B2042525
theorem B1361699 : Blo 1360499 1361699 := bstep (se 1 (by rfl) ⟨1021274, by rfl⟩ : syracuseStep 1361699 = 2042549) B2042549
theorem B5170979 : Blo 1360499 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B2041649 : Blo 1360499 2041649 := bstep (se 2 (by rfl) ⟨765618, by rfl⟩ : syracuseStep 2041649 = 1531237) B1531237
theorem B1361715 : Blo 1360499 1361715 := bstep (se 1 (by rfl) ⟨1021286, by rfl⟩ : syracuseStep 1361715 = 2042573) B2042573
theorem B2041667 : Blo 1360499 2041667 := bstep (se 1 (by rfl) ⟨1531250, by rfl⟩ : syracuseStep 2041667 = 3062501) B3062501
theorem B1361731 : Blo 1360499 1361731 := bstep (se 1 (by rfl) ⟨1021298, by rfl⟩ : syracuseStep 1361731 = 2042597) B2042597
theorem B1361747 : Blo 1360499 1361747 := bstep (se 1 (by rfl) ⟨1021310, by rfl⟩ : syracuseStep 1361747 = 2042621) B2042621
theorem B2041697 : Blo 1360499 2041697 := bstep (se 2 (by rfl) ⟨765636, by rfl⟩ : syracuseStep 2041697 = 1531273) B1531273
theorem B2180963 : Blo 1360499 2180963 := bstep (se 1 (by rfl) ⟨1635722, by rfl⟩ : syracuseStep 2180963 = 3271445) B3271445
theorem B1361763 : Blo 1360499 1361763 := bstep (se 1 (by rfl) ⟨1021322, by rfl⟩ : syracuseStep 1361763 = 2042645) B2042645
theorem B4597613 : Blo 1360499 4597613 := bstep (se 3 (by rfl) ⟨862052, by rfl⟩ : syracuseStep 4597613 = 1724105) B1724105
theorem B2041715 : Blo 1360499 2041715 := bstep (se 1 (by rfl) ⟨1531286, by rfl⟩ : syracuseStep 2041715 = 3062573) B3062573
theorem B1361779 : Blo 1360499 1361779 := bstep (se 1 (by rfl) ⟨1021334, by rfl⟩ : syracuseStep 1361779 = 2042669) B2042669
theorem B1361795 : Blo 1360499 1361795 := bstep (se 1 (by rfl) ⟨1021346, by rfl⟩ : syracuseStep 1361795 = 2042693) B2042693
theorem B4360081 : Blo 1360499 4360081 := bstep (se 2 (by rfl) ⟨1635030, by rfl⟩ : syracuseStep 4360081 = 3270061) B3270061
theorem B2041745 : Blo 1360499 2041745 := bstep (se 2 (by rfl) ⟨765654, by rfl⟩ : syracuseStep 2041745 = 1531309) B1531309
theorem B1361811 : Blo 1360499 1361811 := bstep (se 1 (by rfl) ⟨1021358, by rfl⟩ : syracuseStep 1361811 = 2042717) B2042717
theorem B2041763 : Blo 1360499 2041763 := bstep (se 1 (by rfl) ⟨1531322, by rfl⟩ : syracuseStep 2041763 = 3062645) B3062645
theorem B1361827 : Blo 1360499 1361827 := bstep (se 1 (by rfl) ⟨1021370, by rfl⟩ : syracuseStep 1361827 = 2042741) B2042741
theorem B4597667 : Blo 1360499 4597667 := bstep (se 1 (by rfl) ⟨3448250, by rfl⟩ : syracuseStep 4597667 = 6896501) B6896501
theorem B1361843 : Blo 1360499 1361843 := bstep (se 1 (by rfl) ⟨1021382, by rfl⟩ : syracuseStep 1361843 = 2042765) B2042765
theorem B2041793 : Blo 1360499 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B1361859 : Blo 1360499 1361859 := bstep (se 1 (by rfl) ⟨1021394, by rfl⟩ : syracuseStep 1361859 = 2042789) B2042789
theorem B1722323 : Blo 1360499 1722323 := bstep (se 1 (by rfl) ⟨1291742, by rfl⟩ : syracuseStep 1722323 = 2583485) B2583485
theorem B2041811 : Blo 1360499 2041811 := bstep (se 1 (by rfl) ⟨1531358, by rfl⟩ : syracuseStep 2041811 = 3062717) B3062717
theorem B1361875 : Blo 1360499 1361875 := bstep (se 1 (by rfl) ⟨1021406, by rfl⟩ : syracuseStep 1361875 = 2042813) B2042813
theorem B1361891 : Blo 1360499 1361891 := bstep (se 1 (by rfl) ⟨1021418, by rfl⟩ : syracuseStep 1361891 = 2042837) B2042837
theorem B2041841 : Blo 1360499 2041841 := bstep (se 2 (by rfl) ⟨765690, by rfl⟩ : syracuseStep 2041841 = 1531381) B1531381
theorem B1361907 : Blo 1360499 1361907 := bstep (se 1 (by rfl) ⟨1021430, by rfl⟩ : syracuseStep 1361907 = 2042861) B2042861
theorem B2041859 : Blo 1360499 2041859 := bstep (se 1 (by rfl) ⟨1531394, by rfl⟩ : syracuseStep 2041859 = 3062789) B3062789
theorem B1361923 : Blo 1360499 1361923 := bstep (se 1 (by rfl) ⟨1021442, by rfl⟩ : syracuseStep 1361923 = 2042885) B2042885
theorem B1361939 : Blo 1360499 1361939 := bstep (se 1 (by rfl) ⟨1021454, by rfl⟩ : syracuseStep 1361939 = 2042909) B2042909
theorem B2041889 : Blo 1360499 2041889 := bstep (se 2 (by rfl) ⟨765708, by rfl⟩ : syracuseStep 2041889 = 1531417) B1531417
theorem B8276003 : Blo 1360499 8276003 := bstep (se 1 (by rfl) ⟨6207002, by rfl⟩ : syracuseStep 8276003 = 12414005) B12414005
theorem B1361955 : Blo 1360499 1361955 := bstep (se 1 (by rfl) ⟨1021466, by rfl⟩ : syracuseStep 1361955 = 2042933) B2042933
theorem B2295857 : Blo 1360499 2295857 := bstep (se 2 (by rfl) ⟨860946, by rfl⟩ : syracuseStep 2295857 = 1721893) B1721893
theorem B3876913 : Blo 1360499 3876913 := bstep (se 2 (by rfl) ⟨1453842, by rfl⟩ : syracuseStep 3876913 = 2907685) B2907685
theorem B2041907 : Blo 1360499 2041907 := bstep (se 1 (by rfl) ⟨1531430, by rfl⟩ : syracuseStep 2041907 = 3062861) B3062861
theorem B1361971 : Blo 1360499 1361971 := bstep (se 1 (by rfl) ⟨1021478, by rfl⟩ : syracuseStep 1361971 = 2042957) B2042957
theorem B1361987 : Blo 1360499 1361987 := bstep (se 1 (by rfl) ⟨1021490, by rfl⟩ : syracuseStep 1361987 = 2042981) B2042981
theorem B6981709 : Blo 1360499 6981709 := bstep (se 3 (by rfl) ⟨1309070, by rfl⟩ : syracuseStep 6981709 = 2618141) B2618141
theorem B2041937 : Blo 1360499 2041937 := bstep (se 2 (by rfl) ⟨765726, by rfl⟩ : syracuseStep 2041937 = 1531453) B1531453
theorem B1362003 : Blo 1360499 1362003 := bstep (se 1 (by rfl) ⟨1021502, by rfl⟩ : syracuseStep 1362003 = 2043005) B2043005
theorem B2041955 : Blo 1360499 2041955 := bstep (se 1 (by rfl) ⟨1531466, by rfl⟩ : syracuseStep 2041955 = 3062933) B3062933
theorem B1362019 : Blo 1360499 1362019 := bstep (se 1 (by rfl) ⟨1021514, by rfl⟩ : syracuseStep 1362019 = 2043029) B2043029
theorem B1362035 : Blo 1360499 1362035 := bstep (se 1 (by rfl) ⟨1021526, by rfl⟩ : syracuseStep 1362035 = 2043053) B2043053
theorem B2041985 : Blo 1360499 2041985 := bstep (se 2 (by rfl) ⟨765744, by rfl⟩ : syracuseStep 2041985 = 1531489) B1531489
theorem B1362051 : Blo 1360499 1362051 := bstep (se 1 (by rfl) ⟨1021538, by rfl⟩ : syracuseStep 1362051 = 2043077) B2043077
theorem B7751821 : Blo 1360499 7751821 := bstep (se 3 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 7751821 = 2906933) B2906933
theorem B2042003 : Blo 1360499 2042003 := bstep (se 1 (by rfl) ⟨1531502, by rfl⟩ : syracuseStep 2042003 = 3063005) B3063005
theorem B1362067 : Blo 1360499 1362067 := bstep (se 1 (by rfl) ⟨1021550, by rfl⟩ : syracuseStep 1362067 = 2043101) B2043101
theorem B1362083 : Blo 1360499 1362083 := bstep (se 1 (by rfl) ⟨1021562, by rfl⟩ : syracuseStep 1362083 = 2043125) B2043125
theorem B2295985 : Blo 1360499 2295985 := bstep (se 2 (by rfl) ⟨860994, by rfl⟩ : syracuseStep 2295985 = 1721989) B1721989
theorem B2042033 : Blo 1360499 2042033 := bstep (se 2 (by rfl) ⟨765762, by rfl⟩ : syracuseStep 2042033 = 1531525) B1531525
theorem B9316529 : Blo 1360499 9316529 := bstep (se 2 (by rfl) ⟨3493698, by rfl⟩ : syracuseStep 9316529 = 6987397) B6987397
theorem B1362099 : Blo 1360499 1362099 := bstep (se 1 (by rfl) ⟨1021574, by rfl⟩ : syracuseStep 1362099 = 2043149) B2043149
theorem B4597937 : Blo 1360499 4597937 := bstep (se 2 (by rfl) ⟨1724226, by rfl⟩ : syracuseStep 4597937 = 3448453) B3448453
theorem B2042051 : Blo 1360499 2042051 := bstep (se 1 (by rfl) ⟨1531538, by rfl⟩ : syracuseStep 2042051 = 3063077) B3063077
theorem B1362115 : Blo 1360499 1362115 := bstep (se 1 (by rfl) ⟨1021586, by rfl⟩ : syracuseStep 1362115 = 2043173) B2043173
theorem B2296019 : Blo 1360499 2296019 := bstep (se 1 (by rfl) ⟨1722014, by rfl⟩ : syracuseStep 2296019 = 3444029) B3444029
theorem B1362131 : Blo 1360499 1362131 := bstep (se 1 (by rfl) ⟨1021598, by rfl⟩ : syracuseStep 1362131 = 2043197) B2043197
theorem B2042081 : Blo 1360499 2042081 := bstep (se 2 (by rfl) ⟨765780, by rfl⟩ : syracuseStep 2042081 = 1531561) B1531561
theorem B1362147 : Blo 1360499 1362147 := bstep (se 1 (by rfl) ⟨1021610, by rfl⟩ : syracuseStep 1362147 = 2043221) B2043221
theorem B3885293 : Blo 1360499 3885293 := bstep (se 3 (by rfl) ⟨728492, by rfl⟩ : syracuseStep 3885293 = 1456985) B1456985
theorem B2042099 : Blo 1360499 2042099 := bstep (se 1 (by rfl) ⟨1531574, by rfl⟩ : syracuseStep 2042099 = 3063149) B3063149
theorem B1362163 : Blo 1360499 1362163 := bstep (se 1 (by rfl) ⟨1021622, by rfl⟩ : syracuseStep 1362163 = 2043245) B2043245
theorem B2181379 : Blo 1360499 2181379 := bstep (se 1 (by rfl) ⟨1636034, by rfl⟩ : syracuseStep 2181379 = 3272069) B3272069
theorem B1362179 : Blo 1360499 1362179 := bstep (se 1 (by rfl) ⟨1021634, by rfl⟩ : syracuseStep 1362179 = 2043269) B2043269
theorem B10340621 : Blo 1360499 10340621 := bstep (se 3 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 10340621 = 3877733) B3877733
theorem B2042129 : Blo 1360499 2042129 := bstep (se 2 (by rfl) ⟨765798, by rfl⟩ : syracuseStep 2042129 = 1531597) B1531597
theorem B1362195 : Blo 1360499 1362195 := bstep (se 1 (by rfl) ⟨1021646, by rfl⟩ : syracuseStep 1362195 = 2043293) B2043293
theorem B2042147 : Blo 1360499 2042147 := bstep (se 1 (by rfl) ⟨1531610, by rfl⟩ : syracuseStep 2042147 = 3063221) B3063221
theorem B1362211 : Blo 1360499 1362211 := bstep (se 1 (by rfl) ⟨1021658, by rfl⟩ : syracuseStep 1362211 = 2043317) B2043317
theorem B9439537 : Blo 1360499 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B1362227 : Blo 1360499 1362227 := bstep (se 1 (by rfl) ⟨1021670, by rfl⟩ : syracuseStep 1362227 = 2043341) B2043341
theorem B37234997 : Blo 1360499 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B2042177 : Blo 1360499 2042177 := bstep (se 2 (by rfl) ⟨765816, by rfl⟩ : syracuseStep 2042177 = 1531633) B1531633
theorem B1362243 : Blo 1360499 1362243 := bstep (se 1 (by rfl) ⟨1021682, by rfl⟩ : syracuseStep 1362243 = 2043365) B2043365
theorem B4360529 : Blo 1360499 4360529 := bstep (se 2 (by rfl) ⟨1635198, by rfl⟩ : syracuseStep 4360529 = 3270397) B3270397
theorem B2296147 : Blo 1360499 2296147 := bstep (se 1 (by rfl) ⟨1722110, by rfl⟩ : syracuseStep 2296147 = 3444221) B3444221
theorem B2042195 : Blo 1360499 2042195 := bstep (se 1 (by rfl) ⟨1531646, by rfl⟩ : syracuseStep 2042195 = 3063293) B3063293
theorem B1362259 : Blo 1360499 1362259 := bstep (se 1 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 1362259 = 2043389) B2043389
theorem B1362275 : Blo 1360499 1362275 := bstep (se 1 (by rfl) ⟨1021706, by rfl⟩ : syracuseStep 1362275 = 2043413) B2043413
theorem B2042225 : Blo 1360499 2042225 := bstep (se 2 (by rfl) ⟨765834, by rfl⟩ : syracuseStep 2042225 = 1531669) B1531669
theorem B1362291 : Blo 1360499 1362291 := bstep (se 1 (by rfl) ⟨1021718, by rfl⟩ : syracuseStep 1362291 = 2043437) B2043437
theorem B2042243 : Blo 1360499 2042243 := bstep (se 1 (by rfl) ⟨1531682, by rfl⟩ : syracuseStep 2042243 = 3063365) B3063365
theorem B1362307 : Blo 1360499 1362307 := bstep (se 1 (by rfl) ⟨1021730, by rfl⟩ : syracuseStep 1362307 = 2043461) B2043461
theorem B1362323 : Blo 1360499 1362323 := bstep (se 1 (by rfl) ⟨1021742, by rfl⟩ : syracuseStep 1362323 = 2043485) B2043485
theorem B2042273 : Blo 1360499 2042273 := bstep (se 2 (by rfl) ⟨765852, by rfl⟩ : syracuseStep 2042273 = 1531705) B1531705
theorem B2451875 : Blo 1360499 2451875 := bstep (se 1 (by rfl) ⟨1838906, by rfl⟩ : syracuseStep 2451875 = 3677813) B3677813
theorem B5818787 : Blo 1360499 5818787 := bstep (se 1 (by rfl) ⟨4364090, by rfl⟩ : syracuseStep 5818787 = 8728181) B8728181
theorem B1362339 : Blo 1360499 1362339 := bstep (se 1 (by rfl) ⟨1021754, by rfl⟩ : syracuseStep 1362339 = 2043509) B2043509
theorem B2451889 : Blo 1360499 2451889 := bstep (se 2 (by rfl) ⟨919458, by rfl⟩ : syracuseStep 2451889 = 1838917) B1838917
theorem B5171633 : Blo 1360499 5171633 := bstep (se 2 (by rfl) ⟨1939362, by rfl⟩ : syracuseStep 5171633 = 3878725) B3878725
theorem B2042291 : Blo 1360499 2042291 := bstep (se 1 (by rfl) ⟨1531718, by rfl⟩ : syracuseStep 2042291 = 3063437) B3063437
theorem B1362355 : Blo 1360499 1362355 := bstep (se 1 (by rfl) ⟨1021766, by rfl⟩ : syracuseStep 1362355 = 2043533) B2043533
theorem B1362371 : Blo 1360499 1362371 := bstep (se 1 (by rfl) ⟨1021778, by rfl⟩ : syracuseStep 1362371 = 2043557) B2043557
theorem B2042321 : Blo 1360499 2042321 := bstep (se 2 (by rfl) ⟨765870, by rfl⟩ : syracuseStep 2042321 = 1531741) B1531741
theorem B1362387 : Blo 1360499 1362387 := bstep (se 1 (by rfl) ⟨1021790, by rfl⟩ : syracuseStep 1362387 = 2043581) B2043581
theorem B2296289 : Blo 1360499 2296289 := bstep (se 2 (by rfl) ⟨861108, by rfl⟩ : syracuseStep 2296289 = 1722217) B1722217
theorem B2042339 : Blo 1360499 2042339 := bstep (se 1 (by rfl) ⟨1531754, by rfl⟩ : syracuseStep 2042339 = 3063509) B3063509
theorem B1362403 : Blo 1360499 1362403 := bstep (se 1 (by rfl) ⟨1021802, by rfl⟩ : syracuseStep 1362403 = 2043605) B2043605
theorem B1362419 : Blo 1360499 1362419 := bstep (se 1 (by rfl) ⟨1021814, by rfl⟩ : syracuseStep 1362419 = 2043629) B2043629
theorem B2042369 : Blo 1360499 2042369 := bstep (se 2 (by rfl) ⟨765888, by rfl⟩ : syracuseStep 2042369 = 1531777) B1531777
theorem B1362435 : Blo 1360499 1362435 := bstep (se 1 (by rfl) ⟨1021826, by rfl⟩ : syracuseStep 1362435 = 2043653) B2043653
theorem B2181649 : Blo 1360499 2181649 := bstep (se 2 (by rfl) ⟨818118, by rfl⟩ : syracuseStep 2181649 = 1636237) B1636237
theorem B2042387 : Blo 1360499 2042387 := bstep (se 1 (by rfl) ⟨1531790, by rfl⟩ : syracuseStep 2042387 = 3063581) B3063581
theorem B1362451 : Blo 1360499 1362451 := bstep (se 1 (by rfl) ⟨1021838, by rfl⟩ : syracuseStep 1362451 = 2043677) B2043677
theorem B1362467 : Blo 1360499 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B2042417 : Blo 1360499 2042417 := bstep (se 2 (by rfl) ⟨765906, by rfl⟩ : syracuseStep 2042417 = 1531813) B1531813
theorem B1362483 : Blo 1360499 1362483 := bstep (se 1 (by rfl) ⟨1021862, by rfl⟩ : syracuseStep 1362483 = 2043725) B2043725
theorem B2042435 : Blo 1360499 2042435 := bstep (se 1 (by rfl) ⟨1531826, by rfl⟩ : syracuseStep 2042435 = 3063653) B3063653
theorem B15517493 : Blo 1360499 15517493 := bstep (se 5 (by rfl) ⟨727382, by rfl⟩ : syracuseStep 15517493 = 1454765) B1454765
theorem B1362499 : Blo 1360499 1362499 := bstep (se 1 (by rfl) ⟨1021874, by rfl⟩ : syracuseStep 1362499 = 2043749) B2043749
theorem B2452049 : Blo 1360499 2452049 := bstep (se 2 (by rfl) ⟨919518, by rfl⟩ : syracuseStep 2452049 = 1839037) B1839037
theorem B2296417 : Blo 1360499 2296417 := bstep (se 2 (by rfl) ⟨861156, by rfl⟩ : syracuseStep 2296417 = 1722313) B1722313
theorem B2042465 : Blo 1360499 2042465 := bstep (se 2 (by rfl) ⟨765924, by rfl⟩ : syracuseStep 2042465 = 1531849) B1531849
theorem B2042483 : Blo 1360499 2042483 := bstep (se 1 (by rfl) ⟨1531862, by rfl⟩ : syracuseStep 2042483 = 3063725) B3063725
theorem B2296451 : Blo 1360499 2296451 := bstep (se 1 (by rfl) ⟨1722338, by rfl⟩ : syracuseStep 2296451 = 3444677) B3444677
theorem B2042513 : Blo 1360499 2042513 := bstep (se 2 (by rfl) ⟨765942, by rfl⟩ : syracuseStep 2042513 = 1531885) B1531885
theorem B1723027 : Blo 1360499 1723027 := bstep (se 1 (by rfl) ⟨1292270, by rfl⟩ : syracuseStep 1723027 = 2584541) B2584541
theorem B2042531 : Blo 1360499 2042531 := bstep (se 1 (by rfl) ⟨1531898, by rfl⟩ : syracuseStep 2042531 = 3063797) B3063797
theorem B2042561 : Blo 1360499 2042561 := bstep (se 2 (by rfl) ⟨765960, by rfl⟩ : syracuseStep 2042561 = 1531921) B1531921
theorem B2042579 : Blo 1360499 2042579 := bstep (se 1 (by rfl) ⟨1531934, by rfl⟩ : syracuseStep 2042579 = 3063869) B3063869
theorem B2042609 : Blo 1360499 2042609 := bstep (se 2 (by rfl) ⟨765978, by rfl⟩ : syracuseStep 2042609 = 1531957) B1531957
theorem B1723123 : Blo 1360499 1723123 := bstep (se 1 (by rfl) ⟨1292342, by rfl⟩ : syracuseStep 1723123 = 2584685) B2584685
theorem B2296579 : Blo 1360499 2296579 := bstep (se 1 (by rfl) ⟨1722434, by rfl⟩ : syracuseStep 2296579 = 3444869) B3444869
theorem B2042627 : Blo 1360499 2042627 := bstep (se 1 (by rfl) ⟨1531970, by rfl⟩ : syracuseStep 2042627 = 3063941) B3063941
theorem B2181905 : Blo 1360499 2181905 := bstep (se 2 (by rfl) ⟨818214, by rfl⟩ : syracuseStep 2181905 = 1636429) B1636429
theorem B2042657 : Blo 1360499 2042657 := bstep (se 2 (by rfl) ⟨765996, by rfl⟩ : syracuseStep 2042657 = 1531993) B1531993
theorem B1379107 : Blo 1360499 1379107 := bstep (se 1 (by rfl) ⟨1034330, by rfl⟩ : syracuseStep 1379107 = 2068661) B2068661
theorem B2042675 : Blo 1360499 2042675 := bstep (se 1 (by rfl) ⟨1532006, by rfl⟩ : syracuseStep 2042675 = 3064013) B3064013
theorem B3681101 : Blo 1360499 3681101 := bstep (se 3 (by rfl) ⟨690206, by rfl⟩ : syracuseStep 3681101 = 1380413) B1380413
theorem B2042705 : Blo 1360499 2042705 := bstep (se 2 (by rfl) ⟨766014, by rfl⟩ : syracuseStep 2042705 = 1532029) B1532029
theorem B2042723 : Blo 1360499 2042723 := bstep (se 1 (by rfl) ⟨1532042, by rfl⟩ : syracuseStep 2042723 = 3064085) B3064085
theorem B2583409 : Blo 1360499 2583409 := bstep (se 2 (by rfl) ⟨968778, by rfl⟩ : syracuseStep 2583409 = 1937557) B1937557
theorem B2042753 : Blo 1360499 2042753 := bstep (se 2 (by rfl) ⟨766032, by rfl⟩ : syracuseStep 2042753 = 1532065) B1532065
theorem B49671053 : Blo 1360499 49671053 := bstep (se 3 (by rfl) ⟨9313322, by rfl⟩ : syracuseStep 49671053 = 18626645) B18626645
theorem B2296721 : Blo 1360499 2296721 := bstep (se 2 (by rfl) ⟨861270, by rfl⟩ : syracuseStep 2296721 = 1722541) B1722541
theorem B2042771 : Blo 1360499 2042771 := bstep (se 1 (by rfl) ⟨1532078, by rfl⟩ : syracuseStep 2042771 = 3064157) B3064157
theorem B6892451 : Blo 1360499 6892451 := bstep (se 1 (by rfl) ⟨5169338, by rfl⟩ : syracuseStep 6892451 = 10338677) B10338677
theorem B2042801 : Blo 1360499 2042801 := bstep (se 2 (by rfl) ⟨766050, by rfl⟩ : syracuseStep 2042801 = 1532101) B1532101
theorem B2042819 : Blo 1360499 2042819 := bstep (se 1 (by rfl) ⟨1532114, by rfl⟩ : syracuseStep 2042819 = 3064229) B3064229
theorem B2042849 : Blo 1360499 2042849 := bstep (se 2 (by rfl) ⟨766068, by rfl⟩ : syracuseStep 2042849 = 1532137) B1532137
theorem B2042867 : Blo 1360499 2042867 := bstep (se 1 (by rfl) ⟨1532150, by rfl⟩ : syracuseStep 2042867 = 3064301) B3064301
theorem B2583569 : Blo 1360499 2583569 := bstep (se 2 (by rfl) ⟨968838, by rfl⟩ : syracuseStep 2583569 = 1937677) B1937677
theorem B2296849 : Blo 1360499 2296849 := bstep (se 2 (by rfl) ⟨861318, by rfl⟩ : syracuseStep 2296849 = 1722637) B1722637
theorem B2042897 : Blo 1360499 2042897 := bstep (se 2 (by rfl) ⟨766086, by rfl⟩ : syracuseStep 2042897 = 1532173) B1532173
theorem B2042915 : Blo 1360499 2042915 := bstep (se 1 (by rfl) ⟨1532186, by rfl⟩ : syracuseStep 2042915 = 3064373) B3064373
theorem B2296883 : Blo 1360499 2296883 := bstep (se 1 (by rfl) ⟨1722662, by rfl⟩ : syracuseStep 2296883 = 3445325) B3445325
theorem B2042945 : Blo 1360499 2042945 := bstep (se 2 (by rfl) ⟨766104, by rfl⟩ : syracuseStep 2042945 = 1532209) B1532209
theorem B2042963 : Blo 1360499 2042963 := bstep (se 1 (by rfl) ⟨1532222, by rfl⟩ : syracuseStep 2042963 = 3064445) B3064445
theorem B2042993 : Blo 1360499 2042993 := bstep (se 2 (by rfl) ⟨766122, by rfl⟩ : syracuseStep 2042993 = 1532245) B1532245
theorem B2043011 : Blo 1360499 2043011 := bstep (se 1 (by rfl) ⟨1532258, by rfl⟩ : syracuseStep 2043011 = 3064517) B3064517
theorem B2043041 : Blo 1360499 2043041 := bstep (se 2 (by rfl) ⟨766140, by rfl⟩ : syracuseStep 2043041 = 1532281) B1532281
theorem B2297011 : Blo 1360499 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B2043059 : Blo 1360499 2043059 := bstep (se 1 (by rfl) ⟨1532294, by rfl⟩ : syracuseStep 2043059 = 3064589) B3064589
theorem B8727749 : Blo 1360499 8727749 := bstep (se 4 (by rfl) ⟨818226, by rfl⟩ : syracuseStep 8727749 = 1636453) B1636453
theorem B2043089 : Blo 1360499 2043089 := bstep (se 2 (by rfl) ⟨766158, by rfl⟩ : syracuseStep 2043089 = 1532317) B1532317
theorem B3271907 : Blo 1360499 3271907 := bstep (se 1 (by rfl) ⟨2453930, by rfl⟩ : syracuseStep 3271907 = 4907861) B4907861
theorem B1723619 : Blo 1360499 1723619 := bstep (se 1 (by rfl) ⟨1292714, by rfl⟩ : syracuseStep 1723619 = 2585429) B2585429
theorem B2043107 : Blo 1360499 2043107 := bstep (se 1 (by rfl) ⟨1532330, by rfl⟩ : syracuseStep 2043107 = 3064661) B3064661
theorem B2043137 : Blo 1360499 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B8629517 : Blo 1360499 8629517 := bstep (se 3 (by rfl) ⟨1618034, by rfl⟩ : syracuseStep 8629517 = 3236069) B3236069
theorem B2043155 : Blo 1360499 2043155 := bstep (se 1 (by rfl) ⟨1532366, by rfl⟩ : syracuseStep 2043155 = 3064733) B3064733
theorem B3878189 : Blo 1360499 3878189 := bstep (se 3 (by rfl) ⟨727160, by rfl⟩ : syracuseStep 3878189 = 1454321) B1454321
theorem B2043185 : Blo 1360499 2043185 := bstep (se 2 (by rfl) ⟨766194, by rfl⟩ : syracuseStep 2043185 = 1532389) B1532389
theorem B2297153 : Blo 1360499 2297153 := bstep (se 2 (by rfl) ⟨861432, by rfl⟩ : syracuseStep 2297153 = 1722865) B1722865
theorem B2043203 : Blo 1360499 2043203 := bstep (se 1 (by rfl) ⟨1532402, by rfl⟩ : syracuseStep 2043203 = 3064805) B3064805
theorem B7359821 : Blo 1360499 7359821 := bstep (se 3 (by rfl) ⟨1379966, by rfl⟩ : syracuseStep 7359821 = 2759933) B2759933
theorem B2043233 : Blo 1360499 2043233 := bstep (se 2 (by rfl) ⟨766212, by rfl⟩ : syracuseStep 2043233 = 1532425) B1532425
theorem B2452835 : Blo 1360499 2452835 := bstep (se 1 (by rfl) ⟨1839626, by rfl⟩ : syracuseStep 2452835 = 3679253) B3679253
theorem B2043251 : Blo 1360499 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B2043281 : Blo 1360499 2043281 := bstep (se 2 (by rfl) ⟨766230, by rfl⟩ : syracuseStep 2043281 = 1532461) B1532461
theorem B2583971 : Blo 1360499 2583971 := bstep (se 1 (by rfl) ⟨1937978, by rfl⟩ : syracuseStep 2583971 = 3875957) B3875957
theorem B2043299 : Blo 1360499 2043299 := bstep (se 1 (by rfl) ⟨1532474, by rfl⟩ : syracuseStep 2043299 = 3064949) B3064949
theorem B2297281 : Blo 1360499 2297281 := bstep (se 2 (by rfl) ⟨861480, by rfl⟩ : syracuseStep 2297281 = 1722961) B1722961
theorem B2043329 : Blo 1360499 2043329 := bstep (se 2 (by rfl) ⟨766248, by rfl⟩ : syracuseStep 2043329 = 1532497) B1532497
theorem B2043347 : Blo 1360499 2043347 := bstep (se 1 (by rfl) ⟨1532510, by rfl⟩ : syracuseStep 2043347 = 3065021) B3065021
theorem B2297315 : Blo 1360499 2297315 := bstep (se 1 (by rfl) ⟨1722986, by rfl⟩ : syracuseStep 2297315 = 3445973) B3445973
theorem B3878371 : Blo 1360499 3878371 := bstep (se 1 (by rfl) ⟨2908778, by rfl⟩ : syracuseStep 3878371 = 5817557) B5817557
theorem B2043377 : Blo 1360499 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B2043395 : Blo 1360499 2043395 := bstep (se 1 (by rfl) ⟨1532546, by rfl⟩ : syracuseStep 2043395 = 3065093) B3065093
theorem B3444241 : Blo 1360499 3444241 := bstep (se 2 (by rfl) ⟨1291590, by rfl⟩ : syracuseStep 3444241 = 2583181) B2583181
theorem B3878417 : Blo 1360499 3878417 := bstep (se 2 (by rfl) ⟨1454406, by rfl⟩ : syracuseStep 3878417 = 2908813) B2908813
theorem B2043425 : Blo 1360499 2043425 := bstep (se 2 (by rfl) ⟨766284, by rfl⟩ : syracuseStep 2043425 = 1532569) B1532569
theorem B2043443 : Blo 1360499 2043443 := bstep (se 1 (by rfl) ⟨1532582, by rfl⟩ : syracuseStep 2043443 = 3065165) B3065165
theorem B2043473 : Blo 1360499 2043473 := bstep (se 2 (by rfl) ⟨766302, by rfl⟩ : syracuseStep 2043473 = 1532605) B1532605
theorem B2297443 : Blo 1360499 2297443 := bstep (se 1 (by rfl) ⟨1723082, by rfl⟩ : syracuseStep 2297443 = 3446165) B3446165
theorem B2043491 : Blo 1360499 2043491 := bstep (se 1 (by rfl) ⟨1532618, by rfl⟩ : syracuseStep 2043491 = 3065237) B3065237
theorem B2043521 : Blo 1360499 2043521 := bstep (se 2 (by rfl) ⟨766320, by rfl⟩ : syracuseStep 2043521 = 1532641) B1532641
theorem B2043539 : Blo 1360499 2043539 := bstep (se 1 (by rfl) ⟨1532654, by rfl⟩ : syracuseStep 2043539 = 3065309) B3065309
theorem B2043569 : Blo 1360499 2043569 := bstep (se 2 (by rfl) ⟨766338, by rfl⟩ : syracuseStep 2043569 = 1532677) B1532677
theorem B2043587 : Blo 1360499 2043587 := bstep (se 1 (by rfl) ⟨1532690, by rfl⟩ : syracuseStep 2043587 = 3065381) B3065381
theorem B6893261 : Blo 1360499 6893261 := bstep (se 3 (by rfl) ⟨1292486, by rfl⟩ : syracuseStep 6893261 = 2584973) B2584973
theorem B2043617 : Blo 1360499 2043617 := bstep (se 2 (by rfl) ⟨766356, by rfl⟩ : syracuseStep 2043617 = 1532713) B1532713
theorem B2297585 : Blo 1360499 2297585 := bstep (se 2 (by rfl) ⟨861594, by rfl⟩ : syracuseStep 2297585 = 1723189) B1723189
theorem B2043635 : Blo 1360499 2043635 := bstep (se 1 (by rfl) ⟨1532726, by rfl⟩ : syracuseStep 2043635 = 3065453) B3065453
theorem B3731213 : Blo 1360499 3731213 := bstep (se 3 (by rfl) ⟨699602, by rfl⟩ : syracuseStep 3731213 = 1399205) B1399205
theorem B2043665 : Blo 1360499 2043665 := bstep (se 2 (by rfl) ⟨766374, by rfl⟩ : syracuseStep 2043665 = 1532749) B1532749
theorem B3444515 : Blo 1360499 3444515 := bstep (se 1 (by rfl) ⟨2583386, by rfl⟩ : syracuseStep 3444515 = 5166773) B5166773
theorem B2043683 : Blo 1360499 2043683 := bstep (se 1 (by rfl) ⟨1532762, by rfl⟩ : syracuseStep 2043683 = 3065525) B3065525
theorem B2043713 : Blo 1360499 2043713 := bstep (se 2 (by rfl) ⟨766392, by rfl⟩ : syracuseStep 2043713 = 1532785) B1532785
theorem B1453907 : Blo 1360499 1453907 := bstep (se 1 (by rfl) ⟨1090430, by rfl⟩ : syracuseStep 1453907 = 2180861) B2180861
theorem B2043731 : Blo 1360499 2043731 := bstep (se 1 (by rfl) ⟨1532798, by rfl⟩ : syracuseStep 2043731 = 3065597) B3065597
theorem B5173091 : Blo 1360499 5173091 := bstep (se 1 (by rfl) ⟨3879818, by rfl⟩ : syracuseStep 5173091 = 7759637) B7759637
theorem B2297713 : Blo 1360499 2297713 := bstep (se 2 (by rfl) ⟨861642, by rfl⟩ : syracuseStep 2297713 = 1723285) B1723285
theorem B5173105 : Blo 1360499 5173105 := bstep (se 2 (by rfl) ⟨1939914, by rfl⟩ : syracuseStep 5173105 = 3879829) B3879829
theorem B2297747 : Blo 1360499 2297747 := bstep (se 1 (by rfl) ⟨1723310, by rfl⟩ : syracuseStep 2297747 = 3446621) B3446621
theorem B1724323 : Blo 1360499 1724323 := bstep (se 1 (by rfl) ⟨1293242, by rfl⟩ : syracuseStep 1724323 = 2586485) B2586485
theorem B1937363 : Blo 1360499 1937363 := bstep (se 1 (by rfl) ⟨1453022, by rfl⟩ : syracuseStep 1937363 = 2906045) B2906045
theorem B3444707 : Blo 1360499 3444707 := bstep (se 1 (by rfl) ⟨2583530, by rfl⟩ : syracuseStep 3444707 = 5167061) B5167061
theorem B11186147 : Blo 1360499 11186147 := bstep (se 1 (by rfl) ⟨8389610, by rfl⟩ : syracuseStep 11186147 = 16779221) B16779221
theorem B8720389 : Blo 1360499 8720389 := bstep (se 4 (by rfl) ⟨817536, by rfl⟩ : syracuseStep 8720389 = 1635073) B1635073
theorem B2297875 : Blo 1360499 2297875 := bstep (se 1 (by rfl) ⟨1723406, by rfl⟩ : syracuseStep 2297875 = 3446813) B3446813
theorem B20951093 : Blo 1360499 20951093 := bstep (se 5 (by rfl) ⟨982082, by rfl⟩ : syracuseStep 20951093 = 1964165) B1964165
theorem B4255811 : Blo 1360499 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B7753805 : Blo 1360499 7753805 := bstep (se 3 (by rfl) ⟨1453838, by rfl⟩ : syracuseStep 7753805 = 2907677) B2907677
theorem B2298017 : Blo 1360499 2298017 := bstep (se 2 (by rfl) ⟨861756, by rfl⟩ : syracuseStep 2298017 = 1723513) B1723513
theorem B4591889 : Blo 1360499 4591889 := bstep (se 2 (by rfl) ⟨1721958, by rfl⟩ : syracuseStep 4591889 = 3443917) B3443917
theorem B2298145 : Blo 1360499 2298145 := bstep (se 2 (by rfl) ⟨861804, by rfl⟩ : syracuseStep 2298145 = 1723609) B1723609
theorem B2584867 : Blo 1360499 2584867 := bstep (se 1 (by rfl) ⟨1938650, by rfl⟩ : syracuseStep 2584867 = 3877301) B3877301
theorem B2298179 : Blo 1360499 2298179 := bstep (se 1 (by rfl) ⟨1723634, by rfl⟩ : syracuseStep 2298179 = 3447269) B3447269
theorem B4362605 : Blo 1360499 4362605 := bstep (se 3 (by rfl) ⟨817988, by rfl⟩ : syracuseStep 4362605 = 1635977) B1635977
theorem B2068849 : Blo 1360499 2068849 := bstep (se 2 (by rfl) ⟨775818, by rfl⟩ : syracuseStep 2068849 = 1551637) B1551637
theorem B19640717 : Blo 1360499 19640717 := bstep (se 3 (by rfl) ⟨3682634, by rfl⟩ : syracuseStep 19640717 = 7365269) B7365269
theorem B2585027 : Blo 1360499 2585027 := bstep (se 1 (by rfl) ⟨1938770, by rfl⟩ : syracuseStep 2585027 = 3877541) B3877541
theorem B2298307 : Blo 1360499 2298307 := bstep (se 1 (by rfl) ⟨1723730, by rfl⟩ : syracuseStep 2298307 = 3447461) B3447461
theorem B14913989 : Blo 1360499 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B8393165 : Blo 1360499 8393165 := bstep (se 3 (by rfl) ⟨1573718, by rfl⟩ : syracuseStep 8393165 = 3147437) B3147437
theorem B6214157 : Blo 1360499 6214157 := bstep (se 3 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 6214157 = 2330309) B2330309
theorem B10334789 : Blo 1360499 10334789 := bstep (se 4 (by rfl) ⟨968886, by rfl⟩ : syracuseStep 10334789 = 1937773) B1937773
theorem B1938001 : Blo 1360499 1938001 := bstep (se 2 (by rfl) ⟨726750, by rfl⟩ : syracuseStep 1938001 = 1453501) B1453501
theorem B2298449 : Blo 1360499 2298449 := bstep (se 2 (by rfl) ⟨861918, by rfl⟩ : syracuseStep 2298449 = 1723837) B1723837
theorem B11629169 : Blo 1360499 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B1938115 : Blo 1360499 1938115 := bstep (se 1 (by rfl) ⟨1453586, by rfl⟩ : syracuseStep 1938115 = 2907173) B2907173
theorem B2298577 : Blo 1360499 2298577 := bstep (se 2 (by rfl) ⟨861966, by rfl⟩ : syracuseStep 2298577 = 1723933) B1723933
theorem B2298611 : Blo 1360499 2298611 := bstep (se 1 (by rfl) ⟨1723958, by rfl⟩ : syracuseStep 2298611 = 3447917) B3447917
theorem B1454851 : Blo 1360499 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B4592429 : Blo 1360499 4592429 := bstep (se 3 (by rfl) ⟨861080, by rfl⟩ : syracuseStep 4592429 = 1722161) B1722161
theorem B4592483 : Blo 1360499 4592483 := bstep (se 1 (by rfl) ⟨3444362, by rfl⟩ : syracuseStep 4592483 = 6888725) B6888725
theorem B2298739 : Blo 1360499 2298739 := bstep (se 1 (by rfl) ⟨1724054, by rfl⟩ : syracuseStep 2298739 = 3448109) B3448109
theorem B3445649 : Blo 1360499 3445649 := bstep (se 2 (by rfl) ⟨1292118, by rfl⟩ : syracuseStep 3445649 = 2584237) B2584237
theorem B3445699 : Blo 1360499 3445699 := bstep (se 1 (by rfl) ⟨2584274, by rfl⟩ : syracuseStep 3445699 = 5168549) B5168549
theorem B3879875 : Blo 1360499 3879875 := bstep (se 1 (by rfl) ⟨2909906, by rfl⟩ : syracuseStep 3879875 = 5819813) B5819813
theorem B7754737 : Blo 1360499 7754737 := bstep (se 2 (by rfl) ⟨2908026, by rfl⟩ : syracuseStep 7754737 = 5816053) B5816053
theorem B2298881 : Blo 1360499 2298881 := bstep (se 2 (by rfl) ⟨862080, by rfl⟩ : syracuseStep 2298881 = 1724161) B1724161
theorem B8279117 : Blo 1360499 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B3445841 : Blo 1360499 3445841 := bstep (se 2 (by rfl) ⟨1292190, by rfl⟩ : syracuseStep 3445841 = 2584381) B2584381
theorem B4592753 : Blo 1360499 4592753 := bstep (se 2 (by rfl) ⟨1722282, by rfl⟩ : syracuseStep 4592753 = 3444565) B3444565
theorem B10343537 : Blo 1360499 10343537 := bstep (se 2 (by rfl) ⟨3878826, by rfl⟩ : syracuseStep 10343537 = 7757653) B7757653
theorem B2299009 : Blo 1360499 2299009 := bstep (se 2 (by rfl) ⟨862128, by rfl⟩ : syracuseStep 2299009 = 1724257) B1724257
theorem B2946179 : Blo 1360499 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B2299043 : Blo 1360499 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B2299171 : Blo 1360499 2299171 := bstep (se 1 (by rfl) ⟨1724378, by rfl⟩ : syracuseStep 2299171 = 3448757) B3448757
theorem B3061169 : Blo 1360499 3061169 := bstep (se 2 (by rfl) ⟨1147938, by rfl⟩ : syracuseStep 3061169 = 2295877) B2295877
theorem B3061187 : Blo 1360499 3061187 := bstep (se 1 (by rfl) ⟨2295890, by rfl⟩ : syracuseStep 3061187 = 4591781) B4591781
theorem B2586097 : Blo 1360499 2586097 := bstep (se 2 (by rfl) ⟨969786, by rfl⟩ : syracuseStep 2586097 = 1939573) B1939573
theorem B5166605 : Blo 1360499 5166605 := bstep (se 3 (by rfl) ⟨968738, by rfl⟩ : syracuseStep 5166605 = 1937477) B1937477
theorem B4363885 : Blo 1360499 4363885 := bstep (se 3 (by rfl) ⟨818228, by rfl⟩ : syracuseStep 4363885 = 1636457) B1636457
theorem B4593293 : Blo 1360499 4593293 := bstep (se 3 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 4593293 = 1722485) B1722485
theorem B4593347 : Blo 1360499 4593347 := bstep (se 1 (by rfl) ⟨3445010, by rfl⟩ : syracuseStep 4593347 = 6890021) B6890021
theorem B3061457 : Blo 1360499 3061457 := bstep (se 2 (by rfl) ⟨1148046, by rfl⟩ : syracuseStep 3061457 = 2296093) B2296093
theorem B3061475 : Blo 1360499 3061475 := bstep (se 1 (by rfl) ⟨2296106, by rfl⟩ : syracuseStep 3061475 = 4592213) B4592213
theorem B6543139 : Blo 1360499 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B14718773 : Blo 1360499 14718773 := bstep (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) B1379885
theorem B2905969 : Blo 1360499 2905969 := bstep (se 2 (by rfl) ⟨1089738, by rfl⟩ : syracuseStep 2905969 = 2179477) B2179477
theorem B4593617 : Blo 1360499 4593617 := bstep (se 2 (by rfl) ⟨1722606, by rfl⟩ : syracuseStep 4593617 = 3445213) B3445213
theorem B3061745 : Blo 1360499 3061745 := bstep (se 2 (by rfl) ⟨1148154, by rfl⟩ : syracuseStep 3061745 = 2296309) B2296309
theorem B3061763 : Blo 1360499 3061763 := bstep (se 1 (by rfl) ⟨2296322, by rfl⟩ : syracuseStep 3061763 = 4592645) B4592645
theorem B1939459 : Blo 1360499 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B3446833 : Blo 1360499 3446833 := bstep (se 2 (by rfl) ⟨1292562, by rfl⟩ : syracuseStep 3446833 = 2585125) B2585125
theorem B4364387 : Blo 1360499 4364387 := bstep (se 1 (by rfl) ⟨3273290, by rfl⟩ : syracuseStep 4364387 = 6546581) B6546581
theorem B5814413 : Blo 1360499 5814413 := bstep (se 3 (by rfl) ⟨1090202, by rfl⟩ : syracuseStep 5814413 = 2180405) B2180405
theorem B5814449 : Blo 1360499 5814449 := bstep (se 2 (by rfl) ⟨2180418, by rfl⟩ : syracuseStep 5814449 = 4360837) B4360837
theorem B1841329 : Blo 1360499 1841329 := bstep (se 2 (by rfl) ⟨690498, by rfl⟩ : syracuseStep 1841329 = 1380997) B1380997
theorem B3315953 : Blo 1360499 3315953 := bstep (se 2 (by rfl) ⟨1243482, by rfl⟩ : syracuseStep 3315953 = 2486965) B2486965
theorem B3062033 : Blo 1360499 3062033 := bstep (se 2 (by rfl) ⟨1148262, by rfl⟩ : syracuseStep 3062033 = 2296525) B2296525
theorem B3062051 : Blo 1360499 3062051 := bstep (se 1 (by rfl) ⟨2296538, by rfl⟩ : syracuseStep 3062051 = 4593077) B4593077
theorem B3447107 : Blo 1360499 3447107 := bstep (se 1 (by rfl) ⟨2585330, by rfl⟩ : syracuseStep 3447107 = 5170661) B5170661
theorem B2619811 : Blo 1360499 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B7756195 : Blo 1360499 7756195 := bstep (se 1 (by rfl) ⟨5817146, by rfl⟩ : syracuseStep 7756195 = 11634293) B11634293
theorem B2070947 : Blo 1360499 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B7363021 : Blo 1360499 7363021 := bstep (se 3 (by rfl) ⟨1380566, by rfl⟩ : syracuseStep 7363021 = 2761133) B2761133
theorem B4594157 : Blo 1360499 4594157 := bstep (se 3 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 4594157 = 1722809) B1722809
theorem B3447299 : Blo 1360499 3447299 := bstep (se 1 (by rfl) ⟨2585474, by rfl⟩ : syracuseStep 3447299 = 5170949) B5170949
theorem B4594211 : Blo 1360499 4594211 := bstep (se 1 (by rfl) ⟨3445658, by rfl⟩ : syracuseStep 4594211 = 6891317) B6891317
theorem B3062321 : Blo 1360499 3062321 := bstep (se 2 (by rfl) ⟨1148370, by rfl⟩ : syracuseStep 3062321 = 2296741) B2296741
theorem B6896177 : Blo 1360499 6896177 := bstep (se 2 (by rfl) ⟨2586066, by rfl⟩ : syracuseStep 6896177 = 5172133) B5172133
theorem B3062339 : Blo 1360499 3062339 := bstep (se 1 (by rfl) ⟨2296754, by rfl⟩ : syracuseStep 3062339 = 4593509) B4593509
theorem B6888077 : Blo 1360499 6888077 := bstep (se 3 (by rfl) ⟨1291514, by rfl⟩ : syracuseStep 6888077 = 2583029) B2583029
theorem B1530643 : Blo 1360499 1530643 := bstep (se 1 (by rfl) ⟨1147982, by rfl⟩ : syracuseStep 1530643 = 2295965) B2295965
theorem B4660013 : Blo 1360499 4660013 := bstep (se 3 (by rfl) ⟨873752, by rfl⟩ : syracuseStep 4660013 = 1747505) B1747505
theorem B4594481 : Blo 1360499 4594481 := bstep (se 2 (by rfl) ⟨1722930, by rfl⟩ : syracuseStep 4594481 = 3445861) B3445861
theorem B3062609 : Blo 1360499 3062609 := bstep (se 2 (by rfl) ⟨1148478, by rfl⟩ : syracuseStep 3062609 = 2296957) B2296957
theorem B3062627 : Blo 1360499 3062627 := bstep (se 1 (by rfl) ⟨2296970, by rfl⟩ : syracuseStep 3062627 = 4593941) B4593941
theorem B1530787 : Blo 1360499 1530787 := bstep (se 1 (by rfl) ⟨1148090, by rfl⟩ : syracuseStep 1530787 = 2296181) B2296181
theorem B7756721 : Blo 1360499 7756721 := bstep (se 2 (by rfl) ⟨2908770, by rfl⟩ : syracuseStep 7756721 = 5817541) B5817541
theorem B2071507 : Blo 1360499 2071507 := bstep (se 1 (by rfl) ⟨1553630, by rfl⟩ : syracuseStep 2071507 = 3107261) B3107261
theorem B1530931 : Blo 1360499 1530931 := bstep (se 1 (by rfl) ⟨1148198, by rfl⟩ : syracuseStep 1530931 = 2296397) B2296397
theorem B3062897 : Blo 1360499 3062897 := bstep (se 2 (by rfl) ⟨1148586, by rfl⟩ : syracuseStep 3062897 = 2297173) B2297173
theorem B3062915 : Blo 1360499 3062915 := bstep (se 1 (by rfl) ⟨2297186, by rfl⟩ : syracuseStep 3062915 = 4594373) B4594373
theorem B11041933 : Blo 1360499 11041933 := bstep (se 3 (by rfl) ⟨2070362, by rfl⟩ : syracuseStep 11041933 = 4140725) B4140725
theorem B1531075 : Blo 1360499 1531075 := bstep (se 1 (by rfl) ⟨1148306, by rfl⟩ : syracuseStep 1531075 = 2296613) B2296613
theorem B6208753 : Blo 1360499 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B1965379 : Blo 1360499 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B4595021 : Blo 1360499 4595021 := bstep (se 3 (by rfl) ⟨861566, by rfl⟩ : syracuseStep 4595021 = 1723133) B1723133
theorem B1531219 : Blo 1360499 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B4595075 : Blo 1360499 4595075 := bstep (se 1 (by rfl) ⟨3446306, by rfl⟩ : syracuseStep 4595075 = 6892613) B6892613
theorem B3063185 : Blo 1360499 3063185 := bstep (se 2 (by rfl) ⟨1148694, by rfl⟩ : syracuseStep 3063185 = 2297389) B2297389
theorem B3063203 : Blo 1360499 3063203 := bstep (se 1 (by rfl) ⟨2297402, by rfl⟩ : syracuseStep 3063203 = 4594805) B4594805
theorem B8723875 : Blo 1360499 8723875 := bstep (se 1 (by rfl) ⟨6542906, by rfl⟩ : syracuseStep 8723875 = 13085813) B13085813
theorem B7855537 : Blo 1360499 7855537 := bstep (se 2 (by rfl) ⟨2945826, by rfl⟩ : syracuseStep 7855537 = 5891653) B5891653
theorem B3448241 : Blo 1360499 3448241 := bstep (se 2 (by rfl) ⟨1293090, by rfl⟩ : syracuseStep 3448241 = 2586181) B2586181
theorem B3317201 : Blo 1360499 3317201 := bstep (se 2 (by rfl) ⟨1243950, by rfl⟩ : syracuseStep 3317201 = 2487901) B2487901
theorem B9567715 : Blo 1360499 9567715 := bstep (se 1 (by rfl) ⟨7175786, by rfl⟩ : syracuseStep 9567715 = 14351573) B14351573
theorem B1531363 : Blo 1360499 1531363 := bstep (se 1 (by rfl) ⟨1148522, by rfl⟩ : syracuseStep 1531363 = 2297045) B2297045
theorem B3448291 : Blo 1360499 3448291 := bstep (se 1 (by rfl) ⟨2586218, by rfl⟩ : syracuseStep 3448291 = 5172437) B5172437
theorem B5168717 : Blo 1360499 5168717 := bstep (se 3 (by rfl) ⟨969134, by rfl⟩ : syracuseStep 5168717 = 1938269) B1938269
theorem B3874385 : Blo 1360499 3874385 := bstep (se 2 (by rfl) ⟨1452894, by rfl⟩ : syracuseStep 3874385 = 2905789) B2905789
theorem B29425265 : Blo 1360499 29425265 := bstep (se 2 (by rfl) ⟨11034474, by rfl⟩ : syracuseStep 29425265 = 22068949) B22068949
theorem B19619441 : Blo 1360499 19619441 := bstep (se 2 (by rfl) ⟨7357290, by rfl⟩ : syracuseStep 19619441 = 14714581) B14714581
theorem B1531507 : Blo 1360499 1531507 := bstep (se 1 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 1531507 = 2297261) B2297261
theorem B3448433 : Blo 1360499 3448433 := bstep (se 2 (by rfl) ⟨1293162, by rfl⟩ : syracuseStep 3448433 = 2586325) B2586325
theorem B4595345 : Blo 1360499 4595345 := bstep (se 2 (by rfl) ⟨1723254, by rfl⟩ : syracuseStep 4595345 = 3446509) B3446509
theorem B1474195 : Blo 1360499 1474195 := bstep (se 1 (by rfl) ⟨1105646, by rfl⟩ : syracuseStep 1474195 = 2211293) B2211293
theorem B3063473 : Blo 1360499 3063473 := bstep (se 2 (by rfl) ⟨1148802, by rfl⟩ : syracuseStep 3063473 = 2297605) B2297605
theorem B3874499 : Blo 1360499 3874499 := bstep (se 1 (by rfl) ⟨2905874, by rfl⟩ : syracuseStep 3874499 = 5811749) B5811749
theorem B3063491 : Blo 1360499 3063491 := bstep (se 1 (by rfl) ⟨2297618, by rfl⟩ : syracuseStep 3063491 = 4595237) B4595237
theorem B6545137 : Blo 1360499 6545137 := bstep (se 2 (by rfl) ⟨2454426, by rfl⟩ : syracuseStep 6545137 = 4908853) B4908853
theorem B1531651 : Blo 1360499 1531651 := bstep (se 1 (by rfl) ⟨1148738, by rfl⟩ : syracuseStep 1531651 = 2297477) B2297477
theorem B6987619 : Blo 1360499 6987619 := bstep (se 1 (by rfl) ⟨5240714, by rfl⟩ : syracuseStep 6987619 = 10481429) B10481429
theorem B1531795 : Blo 1360499 1531795 := bstep (se 1 (by rfl) ⟨1148846, by rfl⟩ : syracuseStep 1531795 = 2297693) B2297693
theorem B3063761 : Blo 1360499 3063761 := bstep (se 2 (by rfl) ⟨1148910, by rfl⟩ : syracuseStep 3063761 = 2297821) B2297821
theorem B3063779 : Blo 1360499 3063779 := bstep (se 1 (by rfl) ⟨2297834, by rfl⟩ : syracuseStep 3063779 = 4595669) B4595669
theorem B6897635 : Blo 1360499 6897635 := bstep (se 1 (by rfl) ⟨5173226, by rfl⟩ : syracuseStep 6897635 = 10346453) B10346453
theorem B4423661 : Blo 1360499 4423661 := bstep (se 3 (by rfl) ⟨829436, by rfl⟩ : syracuseStep 4423661 = 1658873) B1658873
theorem B3063833 : Blo 1360499 3063833 := bstep (se 2 (by rfl) ⟨1148937, by rfl⟩ : syracuseStep 3063833 = 2297875) B2297875
theorem B19890211 : Blo 1360499 19890211 := bstep (se 1 (by rfl) ⟨14917658, by rfl⟩ : syracuseStep 19890211 = 29835317) B29835317
theorem B5169203 : Blo 1360499 5169203 := bstep (se 1 (by rfl) ⟨3876902, by rfl⟩ : syracuseStep 5169203 = 7753805) B7753805
theorem B5169217 : Blo 1360499 5169217 := bstep (se 2 (by rfl) ⟨1938456, by rfl⟩ : syracuseStep 5169217 = 3876913) B3876913
theorem B4595777 : Blo 1360499 4595777 := bstep (se 2 (by rfl) ⟨1723416, by rfl⟩ : syracuseStep 4595777 = 3446833) B3446833
theorem B1532011 : Blo 1360499 1532011 := bstep (se 1 (by rfl) ⟨1149008, by rfl⟩ : syracuseStep 1532011 = 2298017) B2298017
theorem B3063923 : Blo 1360499 3063923 := bstep (se 1 (by rfl) ⟨2297942, by rfl⟩ : syracuseStep 3063923 = 4595885) B4595885
theorem B55869581 : Blo 1360499 55869581 := bstep (se 3 (by rfl) ⟨10475546, by rfl⟩ : syracuseStep 55869581 = 20951093) B20951093
theorem B3063959 : Blo 1360499 3063959 := bstep (se 1 (by rfl) ⟨2297969, by rfl⟩ : syracuseStep 3063959 = 4595939) B4595939
theorem B1532119 : Blo 1360499 1532119 := bstep (se 1 (by rfl) ⟨1149089, by rfl⟩ : syracuseStep 1532119 = 2298179) B2298179
theorem B2908403 : Blo 1360499 2908403 := bstep (se 1 (by rfl) ⟨2181302, by rfl⟩ : syracuseStep 2908403 = 4362605) B4362605
theorem B5595443 : Blo 1360499 5595443 := bstep (se 1 (by rfl) ⟨4196582, by rfl⟩ : syracuseStep 5595443 = 8393165) B8393165
theorem B3064139 : Blo 1360499 3064139 := bstep (se 1 (by rfl) ⟨2298104, by rfl⟩ : syracuseStep 3064139 = 4596209) B4596209
theorem B2908505 : Blo 1360499 2908505 := bstep (se 2 (by rfl) ⟨1090689, by rfl⟩ : syracuseStep 2908505 = 2181379) B2181379
theorem B6889859 : Blo 1360499 6889859 := bstep (se 1 (by rfl) ⟨5167394, by rfl⟩ : syracuseStep 6889859 = 10334789) B10334789
theorem B3064193 : Blo 1360499 3064193 := bstep (se 2 (by rfl) ⟨1149072, by rfl⟩ : syracuseStep 3064193 = 2298145) B2298145
theorem B1532299 : Blo 1360499 1532299 := bstep (se 1 (by rfl) ⟨1149224, by rfl⟩ : syracuseStep 1532299 = 2298449) B2298449
theorem B1532407 : Blo 1360499 1532407 := bstep (se 1 (by rfl) ⟨1149305, by rfl⟩ : syracuseStep 1532407 = 2298611) B2298611
theorem B23274053 : Blo 1360499 23274053 := bstep (se 4 (by rfl) ⟨2181942, by rfl⟩ : syracuseStep 23274053 = 4363885) B4363885
theorem B3064409 : Blo 1360499 3064409 := bstep (se 2 (by rfl) ⟨1149153, by rfl⟩ : syracuseStep 3064409 = 2298307) B2298307
theorem B4596317 : Blo 1360499 4596317 := bstep (se 3 (by rfl) ⟨861809, by rfl⟩ : syracuseStep 4596317 = 1723619) B1723619
theorem B25191005 : Blo 1360499 25191005 := bstep (se 3 (by rfl) ⟨4723313, by rfl⟩ : syracuseStep 25191005 = 9446627) B9446627
theorem B1360503 : Blo 1360499 1360503 := bstep (se 1 (by rfl) ⟨1020377, by rfl⟩ : syracuseStep 1360503 = 2040755) B2040755
theorem B1360523 : Blo 1360499 1360523 := bstep (se 1 (by rfl) ⟨1020392, by rfl⟩ : syracuseStep 1360523 = 2040785) B2040785
theorem B1360535 : Blo 1360499 1360535 := bstep (se 1 (by rfl) ⟨1020401, by rfl⟩ : syracuseStep 1360535 = 2040803) B2040803
theorem B1360555 : Blo 1360499 1360555 := bstep (se 1 (by rfl) ⟨1020416, by rfl⟩ : syracuseStep 1360555 = 2040833) B2040833
theorem B1532587 : Blo 1360499 1532587 := bstep (se 1 (by rfl) ⟨1149440, by rfl⟩ : syracuseStep 1532587 = 2298881) B2298881
theorem B3064499 : Blo 1360499 3064499 := bstep (se 1 (by rfl) ⟨2298374, by rfl⟩ : syracuseStep 3064499 = 4596749) B4596749
theorem B1360567 : Blo 1360499 1360567 := bstep (se 1 (by rfl) ⟨1020425, by rfl⟩ : syracuseStep 1360567 = 2040851) B2040851
theorem B2908865 : Blo 1360499 2908865 := bstep (se 2 (by rfl) ⟨1090824, by rfl⟩ : syracuseStep 2908865 = 2181649) B2181649
theorem B1360587 : Blo 1360499 1360587 := bstep (se 1 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 1360587 = 2040881) B2040881
theorem B23012045 : Blo 1360499 23012045 := bstep (se 3 (by rfl) ⟨4314758, by rfl⟩ : syracuseStep 23012045 = 8629517) B8629517
theorem B1360599 : Blo 1360499 1360599 := bstep (se 1 (by rfl) ⟨1020449, by rfl⟩ : syracuseStep 1360599 = 2040899) B2040899
theorem B3064535 : Blo 1360499 3064535 := bstep (se 1 (by rfl) ⟨2298401, by rfl⟩ : syracuseStep 3064535 = 4596803) B4596803
theorem B1360619 : Blo 1360499 1360619 := bstep (se 1 (by rfl) ⟨1020464, by rfl⟩ : syracuseStep 1360619 = 2040929) B2040929
theorem B1360631 : Blo 1360499 1360631 := bstep (se 1 (by rfl) ⟨1020473, by rfl⟩ : syracuseStep 1360631 = 2040947) B2040947
theorem B1360651 : Blo 1360499 1360651 := bstep (se 1 (by rfl) ⟨1020488, by rfl⟩ : syracuseStep 1360651 = 2040977) B2040977
theorem B1360663 : Blo 1360499 1360663 := bstep (se 1 (by rfl) ⟨1020497, by rfl⟩ : syracuseStep 1360663 = 2040995) B2040995
theorem B1532695 : Blo 1360499 1532695 := bstep (se 1 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 1532695 = 2299043) B2299043
theorem B1360683 : Blo 1360499 1360683 := bstep (se 1 (by rfl) ⟨1020512, by rfl⟩ : syracuseStep 1360683 = 2041025) B2041025
theorem B1360695 : Blo 1360499 1360695 := bstep (se 1 (by rfl) ⟨1020521, by rfl⟩ : syracuseStep 1360695 = 2041043) B2041043
theorem B1360715 : Blo 1360499 1360715 := bstep (se 1 (by rfl) ⟨1020536, by rfl⟩ : syracuseStep 1360715 = 2041073) B2041073
theorem B1360727 : Blo 1360499 1360727 := bstep (se 1 (by rfl) ⟨1020545, by rfl⟩ : syracuseStep 1360727 = 2041091) B2041091
theorem B22397795 : Blo 1360499 22397795 := bstep (se 1 (by rfl) ⟨16798346, by rfl⟩ : syracuseStep 22397795 = 33596693) B33596693
theorem B1360747 : Blo 1360499 1360747 := bstep (se 1 (by rfl) ⟨1020560, by rfl⟩ : syracuseStep 1360747 = 2041121) B2041121
theorem B1360759 : Blo 1360499 1360759 := bstep (se 1 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 1360759 = 2041139) B2041139
theorem B1360779 : Blo 1360499 1360779 := bstep (se 1 (by rfl) ⟨1020584, by rfl⟩ : syracuseStep 1360779 = 2041169) B2041169
theorem B3064715 : Blo 1360499 3064715 := bstep (se 1 (by rfl) ⟨2298536, by rfl⟩ : syracuseStep 3064715 = 4597073) B4597073
theorem B1360791 : Blo 1360499 1360791 := bstep (se 1 (by rfl) ⟨1020593, by rfl⟩ : syracuseStep 1360791 = 2041187) B2041187
theorem B1360811 : Blo 1360499 1360811 := bstep (se 1 (by rfl) ⟨1020608, by rfl⟩ : syracuseStep 1360811 = 2041217) B2041217
theorem B1360823 : Blo 1360499 1360823 := bstep (se 1 (by rfl) ⟨1020617, by rfl⟩ : syracuseStep 1360823 = 2041235) B2041235
theorem B3064769 : Blo 1360499 3064769 := bstep (se 2 (by rfl) ⟨1149288, by rfl⟩ : syracuseStep 3064769 = 2298577) B2298577
theorem B2040779 : Blo 1360499 2040779 := bstep (se 1 (by rfl) ⟨1530584, by rfl⟩ : syracuseStep 2040779 = 3061169) B3061169
theorem B1360843 : Blo 1360499 1360843 := bstep (se 1 (by rfl) ⟨1020632, by rfl⟩ : syracuseStep 1360843 = 2041265) B2041265
theorem B2040791 : Blo 1360499 2040791 := bstep (se 1 (by rfl) ⟨1530593, by rfl⟩ : syracuseStep 2040791 = 3061187) B3061187
theorem B1360855 : Blo 1360499 1360855 := bstep (se 1 (by rfl) ⟨1020641, by rfl⟩ : syracuseStep 1360855 = 2041283) B2041283
theorem B1360875 : Blo 1360499 1360875 := bstep (se 1 (by rfl) ⟨1020656, by rfl⟩ : syracuseStep 1360875 = 2041313) B2041313
theorem B1360887 : Blo 1360499 1360887 := bstep (se 1 (by rfl) ⟨1020665, by rfl⟩ : syracuseStep 1360887 = 2041331) B2041331
theorem B1360907 : Blo 1360499 1360907 := bstep (se 1 (by rfl) ⟨1020680, by rfl⟩ : syracuseStep 1360907 = 2041361) B2041361
theorem B1360919 : Blo 1360499 1360919 := bstep (se 1 (by rfl) ⟨1020689, by rfl⟩ : syracuseStep 1360919 = 2041379) B2041379
theorem B2040857 : Blo 1360499 2040857 := bstep (se 2 (by rfl) ⟨765321, by rfl⟩ : syracuseStep 2040857 = 1530643) B1530643
theorem B1360939 : Blo 1360499 1360939 := bstep (se 1 (by rfl) ⟨1020704, by rfl⟩ : syracuseStep 1360939 = 2041409) B2041409
theorem B1360951 : Blo 1360499 1360951 := bstep (se 1 (by rfl) ⟨1020713, by rfl⟩ : syracuseStep 1360951 = 2041427) B2041427
theorem B1360971 : Blo 1360499 1360971 := bstep (se 1 (by rfl) ⟨1020728, by rfl⟩ : syracuseStep 1360971 = 2041457) B2041457
theorem B1360983 : Blo 1360499 1360983 := bstep (se 1 (by rfl) ⟨1020737, by rfl⟩ : syracuseStep 1360983 = 2041475) B2041475
theorem B6538333 : Blo 1360499 6538333 := bstep (se 3 (by rfl) ⟨1225937, by rfl⟩ : syracuseStep 6538333 = 2451875) B2451875
theorem B5522525 : Blo 1360499 5522525 := bstep (se 3 (by rfl) ⟨1035473, by rfl⟩ : syracuseStep 5522525 = 2070947) B2070947
theorem B1361003 : Blo 1360499 1361003 := bstep (se 1 (by rfl) ⟨1020752, by rfl⟩ : syracuseStep 1361003 = 2041505) B2041505
theorem B1361015 : Blo 1360499 1361015 := bstep (se 1 (by rfl) ⟨1020761, by rfl⟩ : syracuseStep 1361015 = 2041523) B2041523
theorem B2040971 : Blo 1360499 2040971 := bstep (se 1 (by rfl) ⟨1530728, by rfl⟩ : syracuseStep 2040971 = 3061457) B3061457
theorem B1361035 : Blo 1360499 1361035 := bstep (se 1 (by rfl) ⟨1020776, by rfl⟩ : syracuseStep 1361035 = 2041553) B2041553
theorem B2040983 : Blo 1360499 2040983 := bstep (se 1 (by rfl) ⟨1530737, by rfl⟩ : syracuseStep 2040983 = 3061475) B3061475
theorem B1361047 : Blo 1360499 1361047 := bstep (se 1 (by rfl) ⟨1020785, by rfl⟩ : syracuseStep 1361047 = 2041571) B2041571
theorem B3064985 : Blo 1360499 3064985 := bstep (se 2 (by rfl) ⟨1149369, by rfl⟩ : syracuseStep 3064985 = 2298739) B2298739
theorem B1361067 : Blo 1360499 1361067 := bstep (se 1 (by rfl) ⟨1020800, by rfl⟩ : syracuseStep 1361067 = 2041601) B2041601
theorem B1361079 : Blo 1360499 1361079 := bstep (se 1 (by rfl) ⟨1020809, by rfl⟩ : syracuseStep 1361079 = 2041619) B2041619
theorem B1361099 : Blo 1360499 1361099 := bstep (se 1 (by rfl) ⟨1020824, by rfl⟩ : syracuseStep 1361099 = 2041649) B2041649
theorem B1361111 : Blo 1360499 1361111 := bstep (se 1 (by rfl) ⟨1020833, by rfl⟩ : syracuseStep 1361111 = 2041667) B2041667
theorem B2041049 : Blo 1360499 2041049 := bstep (se 2 (by rfl) ⟨765393, by rfl⟩ : syracuseStep 2041049 = 1530787) B1530787
theorem B1361131 : Blo 1360499 1361131 := bstep (se 1 (by rfl) ⟨1020848, by rfl⟩ : syracuseStep 1361131 = 2041697) B2041697
theorem B3065075 : Blo 1360499 3065075 := bstep (se 1 (by rfl) ⟨2298806, by rfl⟩ : syracuseStep 3065075 = 4597613) B4597613
theorem B1361143 : Blo 1360499 1361143 := bstep (se 1 (by rfl) ⟨1020857, by rfl⟩ : syracuseStep 1361143 = 2041715) B2041715
theorem B1361163 : Blo 1360499 1361163 := bstep (se 1 (by rfl) ⟨1020872, by rfl⟩ : syracuseStep 1361163 = 2041745) B2041745
theorem B1361175 : Blo 1360499 1361175 := bstep (se 1 (by rfl) ⟨1020881, by rfl⟩ : syracuseStep 1361175 = 2041763) B2041763
theorem B3065111 : Blo 1360499 3065111 := bstep (se 1 (by rfl) ⟨2298833, by rfl⟩ : syracuseStep 3065111 = 4597667) B4597667
theorem B2762009 : Blo 1360499 2762009 := bstep (se 2 (by rfl) ⟨1035753, by rfl⟩ : syracuseStep 2762009 = 2071507) B2071507
theorem B1361195 : Blo 1360499 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B1361207 : Blo 1360499 1361207 := bstep (se 1 (by rfl) ⟨1020905, by rfl⟩ : syracuseStep 1361207 = 2041811) B2041811
theorem B10339649 : Blo 1360499 10339649 := bstep (se 2 (by rfl) ⟨3877368, by rfl⟩ : syracuseStep 10339649 = 7754737) B7754737
theorem B2041163 : Blo 1360499 2041163 := bstep (se 1 (by rfl) ⟨1530872, by rfl⟩ : syracuseStep 2041163 = 3061745) B3061745
theorem B1361227 : Blo 1360499 1361227 := bstep (se 1 (by rfl) ⟨1020920, by rfl⟩ : syracuseStep 1361227 = 2041841) B2041841
theorem B2041175 : Blo 1360499 2041175 := bstep (se 1 (by rfl) ⟨1530881, by rfl⟩ : syracuseStep 2041175 = 3061763) B3061763
theorem B1361239 : Blo 1360499 1361239 := bstep (se 1 (by rfl) ⟨1020929, by rfl⟩ : syracuseStep 1361239 = 2041859) B2041859
theorem B1361259 : Blo 1360499 1361259 := bstep (se 1 (by rfl) ⟨1020944, by rfl⟩ : syracuseStep 1361259 = 2041889) B2041889
theorem B1361271 : Blo 1360499 1361271 := bstep (se 1 (by rfl) ⟨1020953, by rfl⟩ : syracuseStep 1361271 = 2041907) B2041907
theorem B1361291 : Blo 1360499 1361291 := bstep (se 1 (by rfl) ⟨1020968, by rfl⟩ : syracuseStep 1361291 = 2041937) B2041937
theorem B1361303 : Blo 1360499 1361303 := bstep (se 1 (by rfl) ⟨1020977, by rfl⟩ : syracuseStep 1361303 = 2041955) B2041955
theorem B2909591 : Blo 1360499 2909591 := bstep (se 1 (by rfl) ⟨2182193, by rfl⟩ : syracuseStep 2909591 = 4364387) B4364387
theorem B2041241 : Blo 1360499 2041241 := bstep (se 2 (by rfl) ⟨765465, by rfl⟩ : syracuseStep 2041241 = 1530931) B1530931
theorem B1361323 : Blo 1360499 1361323 := bstep (se 1 (by rfl) ⟨1020992, by rfl⟩ : syracuseStep 1361323 = 2041985) B2041985
theorem B3876275 : Blo 1360499 3876275 := bstep (se 1 (by rfl) ⟨2907206, by rfl⟩ : syracuseStep 3876275 = 5814413) B5814413
theorem B1361335 : Blo 1360499 1361335 := bstep (se 1 (by rfl) ⟨1021001, by rfl⟩ : syracuseStep 1361335 = 2042003) B2042003
theorem B3876299 : Blo 1360499 3876299 := bstep (se 1 (by rfl) ⟨2907224, by rfl⟩ : syracuseStep 3876299 = 5814449) B5814449
theorem B1361355 : Blo 1360499 1361355 := bstep (se 1 (by rfl) ⟨1021016, by rfl⟩ : syracuseStep 1361355 = 2042033) B2042033
theorem B6211019 : Blo 1360499 6211019 := bstep (se 1 (by rfl) ⟨4658264, by rfl⟩ : syracuseStep 6211019 = 9316529) B9316529
theorem B3065291 : Blo 1360499 3065291 := bstep (se 1 (by rfl) ⟨2298968, by rfl⟩ : syracuseStep 3065291 = 4597937) B4597937
theorem B1361367 : Blo 1360499 1361367 := bstep (se 1 (by rfl) ⟨1021025, by rfl⟩ : syracuseStep 1361367 = 2042051) B2042051
theorem B1361387 : Blo 1360499 1361387 := bstep (se 1 (by rfl) ⟨1021040, by rfl⟩ : syracuseStep 1361387 = 2042081) B2042081
theorem B1361399 : Blo 1360499 1361399 := bstep (se 1 (by rfl) ⟨1021049, by rfl⟩ : syracuseStep 1361399 = 2042099) B2042099
theorem B3065345 : Blo 1360499 3065345 := bstep (se 2 (by rfl) ⟨1149504, by rfl⟩ : syracuseStep 3065345 = 2299009) B2299009
theorem B2041355 : Blo 1360499 2041355 := bstep (se 1 (by rfl) ⟨1531016, by rfl⟩ : syracuseStep 2041355 = 3062033) B3062033
theorem B1361419 : Blo 1360499 1361419 := bstep (se 1 (by rfl) ⟨1021064, by rfl⟩ : syracuseStep 1361419 = 2042129) B2042129
theorem B14722577 : Blo 1360499 14722577 := bstep (se 2 (by rfl) ⟨5520966, by rfl⟩ : syracuseStep 14722577 = 11041933) B11041933
theorem B2041367 : Blo 1360499 2041367 := bstep (se 1 (by rfl) ⟨1531025, by rfl⟩ : syracuseStep 2041367 = 3062051) B3062051
theorem B1361431 : Blo 1360499 1361431 := bstep (se 1 (by rfl) ⟨1021073, by rfl⟩ : syracuseStep 1361431 = 2042147) B2042147
theorem B24823331 : Blo 1360499 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B1361451 : Blo 1360499 1361451 := bstep (se 1 (by rfl) ⟨1021088, by rfl⟩ : syracuseStep 1361451 = 2042177) B2042177
theorem B1361463 : Blo 1360499 1361463 := bstep (se 1 (by rfl) ⟨1021097, by rfl⟩ : syracuseStep 1361463 = 2042195) B2042195
theorem B1361483 : Blo 1360499 1361483 := bstep (se 1 (by rfl) ⟨1021112, by rfl⟩ : syracuseStep 1361483 = 2042225) B2042225
theorem B1361495 : Blo 1360499 1361495 := bstep (se 1 (by rfl) ⟨1021121, by rfl⟩ : syracuseStep 1361495 = 2042243) B2042243
theorem B2041433 : Blo 1360499 2041433 := bstep (se 2 (by rfl) ⟨765537, by rfl⟩ : syracuseStep 2041433 = 1531075) B1531075
theorem B1361515 : Blo 1360499 1361515 := bstep (se 1 (by rfl) ⟨1021136, by rfl⟩ : syracuseStep 1361515 = 2042273) B2042273
theorem B1361527 : Blo 1360499 1361527 := bstep (se 1 (by rfl) ⟨1021145, by rfl⟩ : syracuseStep 1361527 = 2042291) B2042291
theorem B1361547 : Blo 1360499 1361547 := bstep (se 1 (by rfl) ⟨1021160, by rfl⟩ : syracuseStep 1361547 = 2042321) B2042321
theorem B1361559 : Blo 1360499 1361559 := bstep (se 1 (by rfl) ⟨1021169, by rfl⟩ : syracuseStep 1361559 = 2042339) B2042339
theorem B1361579 : Blo 1360499 1361579 := bstep (se 1 (by rfl) ⟨1021184, by rfl⟩ : syracuseStep 1361579 = 2042369) B2042369
theorem B1361591 : Blo 1360499 1361591 := bstep (se 1 (by rfl) ⟨1021193, by rfl⟩ : syracuseStep 1361591 = 2042387) B2042387
theorem B2041547 : Blo 1360499 2041547 := bstep (se 1 (by rfl) ⟨1531160, by rfl⟩ : syracuseStep 2041547 = 3062321) B3062321
theorem B1361611 : Blo 1360499 1361611 := bstep (se 1 (by rfl) ⟨1021208, by rfl⟩ : syracuseStep 1361611 = 2042417) B2042417
theorem B4597451 : Blo 1360499 4597451 := bstep (se 1 (by rfl) ⟨3448088, by rfl⟩ : syracuseStep 4597451 = 6896177) B6896177
theorem B2041559 : Blo 1360499 2041559 := bstep (se 1 (by rfl) ⟨1531169, by rfl⟩ : syracuseStep 2041559 = 3062339) B3062339
theorem B1361623 : Blo 1360499 1361623 := bstep (se 1 (by rfl) ⟨1021217, by rfl⟩ : syracuseStep 1361623 = 2042435) B2042435
theorem B3065561 : Blo 1360499 3065561 := bstep (se 2 (by rfl) ⟨1149585, by rfl⟩ : syracuseStep 3065561 = 2299171) B2299171
theorem B1361643 : Blo 1360499 1361643 := bstep (se 1 (by rfl) ⟨1021232, by rfl⟩ : syracuseStep 1361643 = 2042465) B2042465
theorem B1361655 : Blo 1360499 1361655 := bstep (se 1 (by rfl) ⟨1021241, by rfl⟩ : syracuseStep 1361655 = 2042483) B2042483
theorem B1361675 : Blo 1360499 1361675 := bstep (se 1 (by rfl) ⟨1021256, by rfl⟩ : syracuseStep 1361675 = 2042513) B2042513
theorem B1361687 : Blo 1360499 1361687 := bstep (se 1 (by rfl) ⟨1021265, by rfl⟩ : syracuseStep 1361687 = 2042531) B2042531
theorem B2041625 : Blo 1360499 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B1361707 : Blo 1360499 1361707 := bstep (se 1 (by rfl) ⟨1021280, by rfl⟩ : syracuseStep 1361707 = 2042561) B2042561
theorem B1361719 : Blo 1360499 1361719 := bstep (se 1 (by rfl) ⟨1021289, by rfl⟩ : syracuseStep 1361719 = 2042579) B2042579
theorem B1361739 : Blo 1360499 1361739 := bstep (se 1 (by rfl) ⟨1021304, by rfl⟩ : syracuseStep 1361739 = 2042609) B2042609
theorem B1361751 : Blo 1360499 1361751 := bstep (se 1 (by rfl) ⟨1021313, by rfl⟩ : syracuseStep 1361751 = 2042627) B2042627
theorem B1361771 : Blo 1360499 1361771 := bstep (se 1 (by rfl) ⟨1021328, by rfl⟩ : syracuseStep 1361771 = 2042657) B2042657
theorem B1361783 : Blo 1360499 1361783 := bstep (se 1 (by rfl) ⟨1021337, by rfl⟩ : syracuseStep 1361783 = 2042675) B2042675
theorem B2041739 : Blo 1360499 2041739 := bstep (se 1 (by rfl) ⟨1531304, by rfl⟩ : syracuseStep 2041739 = 3062609) B3062609
theorem B1361803 : Blo 1360499 1361803 := bstep (se 1 (by rfl) ⟨1021352, by rfl⟩ : syracuseStep 1361803 = 2042705) B2042705
theorem B2041751 : Blo 1360499 2041751 := bstep (se 1 (by rfl) ⟨1531313, by rfl⟩ : syracuseStep 2041751 = 3062627) B3062627
theorem B1361815 : Blo 1360499 1361815 := bstep (se 1 (by rfl) ⟨1021361, by rfl⟩ : syracuseStep 1361815 = 2042723) B2042723
theorem B1361835 : Blo 1360499 1361835 := bstep (se 1 (by rfl) ⟨1021376, by rfl⟩ : syracuseStep 1361835 = 2042753) B2042753
theorem B33114035 : Blo 1360499 33114035 := bstep (se 1 (by rfl) ⟨24835526, by rfl⟩ : syracuseStep 33114035 = 49671053) B49671053
theorem B1361847 : Blo 1360499 1361847 := bstep (se 1 (by rfl) ⟨1021385, by rfl⟩ : syracuseStep 1361847 = 2042771) B2042771
theorem B1361867 : Blo 1360499 1361867 := bstep (se 1 (by rfl) ⟨1021400, by rfl⟩ : syracuseStep 1361867 = 2042801) B2042801
theorem B5171147 : Blo 1360499 5171147 := bstep (se 1 (by rfl) ⟨3878360, by rfl⟩ : syracuseStep 5171147 = 7756721) B7756721
theorem B12756953 : Blo 1360499 12756953 := bstep (se 2 (by rfl) ⟨4783857, by rfl⟩ : syracuseStep 12756953 = 9567715) B9567715
theorem B2041817 : Blo 1360499 2041817 := bstep (se 2 (by rfl) ⟨765681, by rfl⟩ : syracuseStep 2041817 = 1531363) B1531363
theorem B1361879 : Blo 1360499 1361879 := bstep (se 1 (by rfl) ⟨1021409, by rfl⟩ : syracuseStep 1361879 = 2042819) B2042819
theorem B5171161 : Blo 1360499 5171161 := bstep (se 2 (by rfl) ⟨1939185, by rfl⟩ : syracuseStep 5171161 = 3878371) B3878371
theorem B4597721 : Blo 1360499 4597721 := bstep (se 2 (by rfl) ⟨1724145, by rfl⟩ : syracuseStep 4597721 = 3448291) B3448291
theorem B1361899 : Blo 1360499 1361899 := bstep (se 1 (by rfl) ⟨1021424, by rfl⟩ : syracuseStep 1361899 = 2042849) B2042849
theorem B1361911 : Blo 1360499 1361911 := bstep (se 1 (by rfl) ⟨1021433, by rfl⟩ : syracuseStep 1361911 = 2042867) B2042867
theorem B1722379 : Blo 1360499 1722379 := bstep (se 1 (by rfl) ⟨1291784, by rfl⟩ : syracuseStep 1722379 = 2583569) B2583569
theorem B1361931 : Blo 1360499 1361931 := bstep (se 1 (by rfl) ⟨1021448, by rfl⟩ : syracuseStep 1361931 = 2042897) B2042897
theorem B1361943 : Blo 1360499 1361943 := bstep (se 1 (by rfl) ⟨1021457, by rfl⟩ : syracuseStep 1361943 = 2042915) B2042915
theorem B1361963 : Blo 1360499 1361963 := bstep (se 1 (by rfl) ⟨1021472, by rfl⟩ : syracuseStep 1361963 = 2042945) B2042945
theorem B1361975 : Blo 1360499 1361975 := bstep (se 1 (by rfl) ⟨1021481, by rfl⟩ : syracuseStep 1361975 = 2042963) B2042963
theorem B2041931 : Blo 1360499 2041931 := bstep (se 1 (by rfl) ⟨1531448, by rfl⟩ : syracuseStep 2041931 = 3062897) B3062897
theorem B1361995 : Blo 1360499 1361995 := bstep (se 1 (by rfl) ⟨1021496, by rfl⟩ : syracuseStep 1361995 = 2042993) B2042993
theorem B2041943 : Blo 1360499 2041943 := bstep (se 1 (by rfl) ⟨1531457, by rfl⟩ : syracuseStep 2041943 = 3062915) B3062915
theorem B1362007 : Blo 1360499 1362007 := bstep (se 1 (by rfl) ⟨1021505, by rfl⟩ : syracuseStep 1362007 = 2043011) B2043011
theorem B1362027 : Blo 1360499 1362027 := bstep (se 1 (by rfl) ⟨1021520, by rfl⟩ : syracuseStep 1362027 = 2043041) B2043041
theorem B1362039 : Blo 1360499 1362039 := bstep (se 1 (by rfl) ⟨1021529, by rfl⟩ : syracuseStep 1362039 = 2043059) B2043059
theorem B5818499 : Blo 1360499 5818499 := bstep (se 1 (by rfl) ⟨4363874, by rfl⟩ : syracuseStep 5818499 = 8727749) B8727749
theorem B1362059 : Blo 1360499 1362059 := bstep (se 1 (by rfl) ⟨1021544, by rfl⟩ : syracuseStep 1362059 = 2043089) B2043089
theorem B2181271 : Blo 1360499 2181271 := bstep (se 1 (by rfl) ⟨1635953, by rfl⟩ : syracuseStep 2181271 = 3271907) B3271907
theorem B1362071 : Blo 1360499 1362071 := bstep (se 1 (by rfl) ⟨1021553, by rfl⟩ : syracuseStep 1362071 = 2043107) B2043107
theorem B2042009 : Blo 1360499 2042009 := bstep (se 2 (by rfl) ⟨765753, by rfl⟩ : syracuseStep 2042009 = 1531507) B1531507
theorem B1362091 : Blo 1360499 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B1362103 : Blo 1360499 1362103 := bstep (se 1 (by rfl) ⟨1021577, by rfl⟩ : syracuseStep 1362103 = 2043155) B2043155
theorem B1362123 : Blo 1360499 1362123 := bstep (se 1 (by rfl) ⟨1021592, by rfl⟩ : syracuseStep 1362123 = 2043185) B2043185
theorem B1362135 : Blo 1360499 1362135 := bstep (se 1 (by rfl) ⟨1021601, by rfl⟩ : syracuseStep 1362135 = 2043203) B2043203
theorem B3877085 : Blo 1360499 3877085 := bstep (se 3 (by rfl) ⟨726953, by rfl⟩ : syracuseStep 3877085 = 1453907) B1453907
theorem B1362155 : Blo 1360499 1362155 := bstep (se 1 (by rfl) ⟨1021616, by rfl⟩ : syracuseStep 1362155 = 2043233) B2043233
theorem B1362167 : Blo 1360499 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B13076741 : Blo 1360499 13076741 := bstep (se 4 (by rfl) ⟨1225944, by rfl⟩ : syracuseStep 13076741 = 2451889) B2451889
theorem B2042123 : Blo 1360499 2042123 := bstep (se 1 (by rfl) ⟨1531592, by rfl⟩ : syracuseStep 2042123 = 3063185) B3063185
theorem B1362187 : Blo 1360499 1362187 := bstep (se 1 (by rfl) ⟨1021640, by rfl⟩ : syracuseStep 1362187 = 2043281) B2043281
theorem B1722647 : Blo 1360499 1722647 := bstep (se 1 (by rfl) ⟨1291985, by rfl⟩ : syracuseStep 1722647 = 2583971) B2583971
theorem B2042135 : Blo 1360499 2042135 := bstep (se 1 (by rfl) ⟨1531601, by rfl⟩ : syracuseStep 2042135 = 3063203) B3063203
theorem B1362199 : Blo 1360499 1362199 := bstep (se 1 (by rfl) ⟨1021649, by rfl⟩ : syracuseStep 1362199 = 2043299) B2043299
theorem B1362219 : Blo 1360499 1362219 := bstep (se 1 (by rfl) ⟨1021664, by rfl⟩ : syracuseStep 1362219 = 2043329) B2043329
theorem B1362231 : Blo 1360499 1362231 := bstep (se 1 (by rfl) ⟨1021673, by rfl⟩ : syracuseStep 1362231 = 2043347) B2043347
theorem B8726849 : Blo 1360499 8726849 := bstep (se 2 (by rfl) ⟨3272568, by rfl⟩ : syracuseStep 8726849 = 6545137) B6545137
theorem B1362251 : Blo 1360499 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B1362263 : Blo 1360499 1362263 := bstep (se 1 (by rfl) ⟨1021697, by rfl⟩ : syracuseStep 1362263 = 2043395) B2043395
theorem B2042201 : Blo 1360499 2042201 := bstep (se 2 (by rfl) ⟨765825, by rfl⟩ : syracuseStep 2042201 = 1531651) B1531651
theorem B1362283 : Blo 1360499 1362283 := bstep (se 1 (by rfl) ⟨1021712, by rfl⟩ : syracuseStep 1362283 = 2043425) B2043425
theorem B1362295 : Blo 1360499 1362295 := bstep (se 1 (by rfl) ⟨1021721, by rfl⟩ : syracuseStep 1362295 = 2043443) B2043443
theorem B2582923 : Blo 1360499 2582923 := bstep (se 1 (by rfl) ⟨1937192, by rfl⟩ : syracuseStep 2582923 = 3874385) B3874385
theorem B1362315 : Blo 1360499 1362315 := bstep (se 1 (by rfl) ⟨1021736, by rfl⟩ : syracuseStep 1362315 = 2043473) B2043473
theorem B1362327 : Blo 1360499 1362327 := bstep (se 1 (by rfl) ⟨1021745, by rfl⟩ : syracuseStep 1362327 = 2043491) B2043491
theorem B1362347 : Blo 1360499 1362347 := bstep (se 1 (by rfl) ⟨1021760, by rfl⟩ : syracuseStep 1362347 = 2043521) B2043521
theorem B1362359 : Blo 1360499 1362359 := bstep (se 1 (by rfl) ⟨1021769, by rfl⟩ : syracuseStep 1362359 = 2043539) B2043539
theorem B2042315 : Blo 1360499 2042315 := bstep (se 1 (by rfl) ⟨1531736, by rfl⟩ : syracuseStep 2042315 = 3063473) B3063473
theorem B1362379 : Blo 1360499 1362379 := bstep (se 1 (by rfl) ⟨1021784, by rfl⟩ : syracuseStep 1362379 = 2043569) B2043569
theorem B2582999 : Blo 1360499 2582999 := bstep (se 1 (by rfl) ⟨1937249, by rfl⟩ : syracuseStep 2582999 = 3874499) B3874499
theorem B2042327 : Blo 1360499 2042327 := bstep (se 1 (by rfl) ⟨1531745, by rfl⟩ : syracuseStep 2042327 = 3063491) B3063491
theorem B9316825 : Blo 1360499 9316825 := bstep (se 2 (by rfl) ⟨3493809, by rfl⟩ : syracuseStep 9316825 = 6987619) B6987619
theorem B1362391 : Blo 1360499 1362391 := bstep (se 1 (by rfl) ⟨1021793, by rfl⟩ : syracuseStep 1362391 = 2043587) B2043587
theorem B1362411 : Blo 1360499 1362411 := bstep (se 1 (by rfl) ⟨1021808, by rfl⟩ : syracuseStep 1362411 = 2043617) B2043617
theorem B1362423 : Blo 1360499 1362423 := bstep (se 1 (by rfl) ⟨1021817, by rfl⟩ : syracuseStep 1362423 = 2043635) B2043635
theorem B1362443 : Blo 1360499 1362443 := bstep (se 1 (by rfl) ⟨1021832, by rfl⟩ : syracuseStep 1362443 = 2043665) B2043665
theorem B2296343 : Blo 1360499 2296343 := bstep (se 1 (by rfl) ⟨1722257, by rfl⟩ : syracuseStep 2296343 = 3444515) B3444515
theorem B1362455 : Blo 1360499 1362455 := bstep (se 1 (by rfl) ⟨1021841, by rfl⟩ : syracuseStep 1362455 = 2043683) B2043683
theorem B2042393 : Blo 1360499 2042393 := bstep (se 2 (by rfl) ⟨765897, by rfl⟩ : syracuseStep 2042393 = 1531795) B1531795
theorem B1362475 : Blo 1360499 1362475 := bstep (se 1 (by rfl) ⟨1021856, by rfl⟩ : syracuseStep 1362475 = 2043713) B2043713
theorem B1362487 : Blo 1360499 1362487 := bstep (se 1 (by rfl) ⟨1021865, by rfl⟩ : syracuseStep 1362487 = 2043731) B2043731
theorem B2042507 : Blo 1360499 2042507 := bstep (se 1 (by rfl) ⟨1531880, by rfl⟩ : syracuseStep 2042507 = 3063761) B3063761
theorem B2296471 : Blo 1360499 2296471 := bstep (se 1 (by rfl) ⟨1722353, by rfl⟩ : syracuseStep 2296471 = 3444707) B3444707
theorem B7457431 : Blo 1360499 7457431 := bstep (se 1 (by rfl) ⟨5593073, by rfl⟩ : syracuseStep 7457431 = 11186147) B11186147
theorem B2042519 : Blo 1360499 2042519 := bstep (se 1 (by rfl) ⟨1531889, by rfl⟩ : syracuseStep 2042519 = 3063779) B3063779
theorem B4598423 : Blo 1360499 4598423 := bstep (se 1 (by rfl) ⟨3448817, by rfl⟩ : syracuseStep 4598423 = 6897635) B6897635
theorem B11627185 : Blo 1360499 11627185 := bstep (se 2 (by rfl) ⟨4360194, by rfl⟩ : syracuseStep 11627185 = 8720389) B8720389
theorem B4909747 : Blo 1360499 4909747 := bstep (se 1 (by rfl) ⟨3682310, by rfl⟩ : syracuseStep 4909747 = 7364621) B7364621
theorem B24824501 : Blo 1360499 24824501 := bstep (se 5 (by rfl) ⟨1163648, by rfl⟩ : syracuseStep 24824501 = 2327297) B2327297
theorem B2837207 : Blo 1360499 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B2042585 : Blo 1360499 2042585 := bstep (se 2 (by rfl) ⟨765969, by rfl⟩ : syracuseStep 2042585 = 1531939) B1531939
theorem B9308945 : Blo 1360499 9308945 := bstep (se 2 (by rfl) ⟨3490854, by rfl⟩ : syracuseStep 9308945 = 6981709) B6981709
theorem B4139851 : Blo 1360499 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B2042699 : Blo 1360499 2042699 := bstep (se 1 (by rfl) ⟨1532024, by rfl⟩ : syracuseStep 2042699 = 3064049) B3064049
theorem B2042711 : Blo 1360499 2042711 := bstep (se 1 (by rfl) ⟨1532033, by rfl⟩ : syracuseStep 2042711 = 3064067) B3064067
theorem B2796439 : Blo 1360499 2796439 := bstep (se 1 (by rfl) ⟨2097329, by rfl⟩ : syracuseStep 2796439 = 4194659) B4194659
theorem B2042777 : Blo 1360499 2042777 := bstep (se 2 (by rfl) ⟨766041, by rfl⟩ : syracuseStep 2042777 = 1532083) B1532083
theorem B5172119 : Blo 1360499 5172119 := bstep (se 1 (by rfl) ⟨3879089, by rfl⟩ : syracuseStep 5172119 = 7758179) B7758179
theorem B13093811 : Blo 1360499 13093811 := bstep (se 1 (by rfl) ⟨9820358, by rfl⟩ : syracuseStep 13093811 = 19640717) B19640717
theorem B3271627 : Blo 1360499 3271627 := bstep (se 1 (by rfl) ⟨2453720, by rfl⟩ : syracuseStep 3271627 = 4907441) B4907441
theorem B1723351 : Blo 1360499 1723351 := bstep (se 1 (by rfl) ⟨1292513, by rfl⟩ : syracuseStep 1723351 = 2585027) B2585027
theorem B2042891 : Blo 1360499 2042891 := bstep (se 1 (by rfl) ⟨1532168, by rfl⟩ : syracuseStep 2042891 = 3064337) B3064337
theorem B2042903 : Blo 1360499 2042903 := bstep (se 1 (by rfl) ⟨1532177, by rfl⟩ : syracuseStep 2042903 = 3064355) B3064355
theorem B39250979 : Blo 1360499 39250979 := bstep (se 1 (by rfl) ⟨29438234, by rfl⟩ : syracuseStep 39250979 = 58876469) B58876469
theorem B12586049 : Blo 1360499 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B7752779 : Blo 1360499 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B2452567 : Blo 1360499 2452567 := bstep (se 1 (by rfl) ⟨1839425, by rfl⟩ : syracuseStep 2452567 = 3678851) B3678851
theorem B2042969 : Blo 1360499 2042969 := bstep (se 2 (by rfl) ⟨766113, by rfl⟩ : syracuseStep 2042969 = 1532227) B1532227
theorem B2583667 : Blo 1360499 2583667 := bstep (se 1 (by rfl) ⟨1937750, by rfl⟩ : syracuseStep 2583667 = 3875501) B3875501
theorem B3271859 : Blo 1360499 3271859 := bstep (se 1 (by rfl) ⟨2453894, by rfl⟩ : syracuseStep 3271859 = 4907789) B4907789
theorem B2043083 : Blo 1360499 2043083 := bstep (se 1 (by rfl) ⟨1532312, by rfl⟩ : syracuseStep 2043083 = 3064625) B3064625
theorem B2043095 : Blo 1360499 2043095 := bstep (se 1 (by rfl) ⟨1532321, by rfl⟩ : syracuseStep 2043095 = 3064643) B3064643
theorem B3493081 : Blo 1360499 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B10341593 : Blo 1360499 10341593 := bstep (se 2 (by rfl) ⟨3878097, by rfl⟩ : syracuseStep 10341593 = 7756195) B7756195
theorem B2297099 : Blo 1360499 2297099 := bstep (se 1 (by rfl) ⟨1722824, by rfl⟩ : syracuseStep 2297099 = 3445649) B3445649
theorem B9817361 : Blo 1360499 9817361 := bstep (se 2 (by rfl) ⟨3681510, by rfl⟩ : syracuseStep 9817361 = 7363021) B7363021
theorem B2043161 : Blo 1360499 2043161 := bstep (se 2 (by rfl) ⟨766185, by rfl⟩ : syracuseStep 2043161 = 1532371) B1532371
theorem B3681587 : Blo 1360499 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B2583895 : Blo 1360499 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B2297227 : Blo 1360499 2297227 := bstep (se 1 (by rfl) ⟨1722920, by rfl⟩ : syracuseStep 2297227 = 3445841) B3445841
theorem B2043275 : Blo 1360499 2043275 := bstep (se 1 (by rfl) ⟨1532456, by rfl⟩ : syracuseStep 2043275 = 3064913) B3064913
theorem B2043287 : Blo 1360499 2043287 := bstep (se 1 (by rfl) ⟨1532465, by rfl⟩ : syracuseStep 2043287 = 3064931) B3064931
theorem B2584001 : Blo 1360499 2584001 := bstep (se 2 (by rfl) ⟨969000, by rfl⟩ : syracuseStep 2584001 = 1938001) B1938001
theorem B2043353 : Blo 1360499 2043353 := bstep (se 2 (by rfl) ⟨766257, by rfl⟩ : syracuseStep 2043353 = 1532515) B1532515
theorem B2297369 : Blo 1360499 2297369 := bstep (se 2 (by rfl) ⟨861513, by rfl⟩ : syracuseStep 2297369 = 1723027) B1723027
theorem B2043467 : Blo 1360499 2043467 := bstep (se 1 (by rfl) ⟨1532600, by rfl⟩ : syracuseStep 2043467 = 3065201) B3065201
theorem B2043479 : Blo 1360499 2043479 := bstep (se 1 (by rfl) ⟨1532609, by rfl⟩ : syracuseStep 2043479 = 3065219) B3065219
theorem B2584153 : Blo 1360499 2584153 := bstep (se 2 (by rfl) ⟨969057, by rfl⟩ : syracuseStep 2584153 = 1938115) B1938115
theorem B2297497 : Blo 1360499 2297497 := bstep (se 2 (by rfl) ⟨861561, by rfl⟩ : syracuseStep 2297497 = 1723123) B1723123
theorem B2043545 : Blo 1360499 2043545 := bstep (se 2 (by rfl) ⟨766329, by rfl⟩ : syracuseStep 2043545 = 1532659) B1532659
theorem B3444403 : Blo 1360499 3444403 := bstep (se 1 (by rfl) ⟨2583302, by rfl⟩ : syracuseStep 3444403 = 5166605) B5166605
theorem B1453783 : Blo 1360499 1453783 := bstep (se 1 (by rfl) ⟨1090337, by rfl⟩ : syracuseStep 1453783 = 2180675) B2180675
theorem B1838809 : Blo 1360499 1838809 := bstep (se 2 (by rfl) ⟨689553, by rfl⟩ : syracuseStep 1838809 = 1379107) B1379107
theorem B2043659 : Blo 1360499 2043659 := bstep (se 1 (by rfl) ⟨1532744, by rfl⟩ : syracuseStep 2043659 = 3065489) B3065489
theorem B2043671 : Blo 1360499 2043671 := bstep (se 1 (by rfl) ⟨1532753, by rfl⟩ : syracuseStep 2043671 = 3065507) B3065507
theorem B3444545 : Blo 1360499 3444545 := bstep (se 2 (by rfl) ⟨1291704, by rfl⟩ : syracuseStep 3444545 = 2583409) B2583409
theorem B2043737 : Blo 1360499 2043737 := bstep (se 2 (by rfl) ⟨766401, by rfl⟩ : syracuseStep 2043737 = 1532803) B1532803
theorem B3878873 : Blo 1360499 3878873 := bstep (se 2 (by rfl) ⟨1454577, by rfl⟩ : syracuseStep 3878873 = 2909155) B2909155
theorem B6893585 : Blo 1360499 6893585 := bstep (se 2 (by rfl) ⟨2585094, by rfl⟩ : syracuseStep 6893585 = 5170189) B5170189
theorem B5517335 : Blo 1360499 5517335 := bstep (se 1 (by rfl) ⟨4138001, by rfl⟩ : syracuseStep 5517335 = 8276003) B8276003
theorem B6893747 : Blo 1360499 6893747 := bstep (se 1 (by rfl) ⟨5170310, by rfl⟩ : syracuseStep 6893747 = 10340621) B10340621
theorem B2298071 : Blo 1360499 2298071 := bstep (se 1 (by rfl) ⟨1723553, by rfl⟩ : syracuseStep 2298071 = 3447107) B3447107
theorem B3879191 : Blo 1360499 3879191 := bstep (se 1 (by rfl) ⟨2909393, by rfl⟩ : syracuseStep 3879191 = 5818787) B5818787
theorem B8278337 : Blo 1360499 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B2298199 : Blo 1360499 2298199 := bstep (se 1 (by rfl) ⟨1723649, by rfl⟩ : syracuseStep 2298199 = 3447299) B3447299
theorem B1634699 : Blo 1360499 1634699 := bstep (se 1 (by rfl) ⟨1226024, by rfl⟩ : syracuseStep 1634699 = 2452049) B2452049
theorem B4592051 : Blo 1360499 4592051 := bstep (se 1 (by rfl) ⟨3444038, by rfl⟩ : syracuseStep 4592051 = 6888077) B6888077
theorem B1454603 : Blo 1360499 1454603 := bstep (se 1 (by rfl) ⟨1090952, by rfl⟩ : syracuseStep 1454603 = 2181905) B2181905
theorem B2454067 : Blo 1360499 2454067 := bstep (se 1 (by rfl) ⟨1840550, by rfl⟩ : syracuseStep 2454067 = 3681101) B3681101
theorem B10474049 : Blo 1360499 10474049 := bstep (se 2 (by rfl) ⟨3927768, by rfl⟩ : syracuseStep 10474049 = 7855537) B7855537
theorem B4592321 : Blo 1360499 4592321 := bstep (se 2 (by rfl) ⟨1722120, by rfl⟩ : syracuseStep 4592321 = 3444241) B3444241
theorem B2585459 : Blo 1360499 2585459 := bstep (se 1 (by rfl) ⟨1939094, by rfl⟩ : syracuseStep 2585459 = 3878189) B3878189
theorem B1635223 : Blo 1360499 1635223 := bstep (se 1 (by rfl) ⟨1226417, by rfl⟩ : syracuseStep 1635223 = 2452835) B2452835
theorem B2298827 : Blo 1360499 2298827 := bstep (se 1 (by rfl) ⟨1724120, by rfl⟩ : syracuseStep 2298827 = 3448241) B3448241
theorem B2585611 : Blo 1360499 2585611 := bstep (se 1 (by rfl) ⟨1939208, by rfl⟩ : syracuseStep 2585611 = 3878417) B3878417
theorem B3445811 : Blo 1360499 3445811 := bstep (se 1 (by rfl) ⟨2584358, by rfl⟩ : syracuseStep 3445811 = 5168717) B5168717
theorem B19616843 : Blo 1360499 19616843 := bstep (se 1 (by rfl) ⟨14712632, by rfl⟩ : syracuseStep 19616843 = 29425265) B29425265
theorem B13079627 : Blo 1360499 13079627 := bstep (se 1 (by rfl) ⟨9809720, by rfl⟩ : syracuseStep 13079627 = 19619441) B19619441
theorem B2298955 : Blo 1360499 2298955 := bstep (se 1 (by rfl) ⟨1724216, by rfl⟩ : syracuseStep 2298955 = 3448433) B3448433
theorem B2487475 : Blo 1360499 2487475 := bstep (se 1 (by rfl) ⟨1865606, by rfl⟩ : syracuseStep 2487475 = 3731213) B3731213
theorem B5813441 : Blo 1360499 5813441 := bstep (se 2 (by rfl) ⟨2180040, by rfl⟩ : syracuseStep 5813441 = 4360081) B4360081
theorem B2299097 : Blo 1360499 2299097 := bstep (se 2 (by rfl) ⟨862161, by rfl⟩ : syracuseStep 2299097 = 1724323) B1724323
theorem B5166301 : Blo 1360499 5166301 := bstep (se 3 (by rfl) ⟨968681, by rfl⟩ : syracuseStep 5166301 = 1937363) B1937363
theorem B4592861 : Blo 1360499 4592861 := bstep (se 3 (by rfl) ⟨861161, by rfl⟩ : syracuseStep 4592861 = 1722323) B1722323
theorem B2585945 : Blo 1360499 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B3061259 : Blo 1360499 3061259 := bstep (se 1 (by rfl) ⟨2295944, by rfl⟩ : syracuseStep 3061259 = 4591889) B4591889
theorem B10335761 : Blo 1360499 10335761 := bstep (se 2 (by rfl) ⟨3875910, by rfl⟩ : syracuseStep 10335761 = 7751821) B7751821
theorem B3061313 : Blo 1360499 3061313 := bstep (se 2 (by rfl) ⟨1147992, by rfl⟩ : syracuseStep 3061313 = 2295985) B2295985
theorem B2455105 : Blo 1360499 2455105 := bstep (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) B1841329
theorem B3446347 : Blo 1360499 3446347 := bstep (se 1 (by rfl) ⟨2584760, by rfl⟩ : syracuseStep 3446347 = 5169521) B5169521
theorem B9942659 : Blo 1360499 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B4142771 : Blo 1360499 4142771 := bstep (se 1 (by rfl) ⟨3107078, by rfl⟩ : syracuseStep 4142771 = 6214157) B6214157
theorem B3446489 : Blo 1360499 3446489 := bstep (se 2 (by rfl) ⟨1292433, by rfl⟩ : syracuseStep 3446489 = 2584867) B2584867
theorem B3061529 : Blo 1360499 3061529 := bstep (se 2 (by rfl) ⟨1148073, by rfl⟩ : syracuseStep 3061529 = 2296147) B2296147
theorem B2758465 : Blo 1360499 2758465 := bstep (se 2 (by rfl) ⟨1034424, by rfl⟩ : syracuseStep 2758465 = 2068849) B2068849
theorem B3061619 : Blo 1360499 3061619 := bstep (se 1 (by rfl) ⟨2296214, by rfl⟩ : syracuseStep 3061619 = 4592429) B4592429
theorem B3061655 : Blo 1360499 3061655 := bstep (se 1 (by rfl) ⟨2296241, by rfl⟩ : syracuseStep 3061655 = 4592483) B4592483
theorem B41932721 : Blo 1360499 41932721 := bstep (se 2 (by rfl) ⟨15724770, by rfl⟩ : syracuseStep 41932721 = 31449541) B31449541
theorem B10360781 : Blo 1360499 10360781 := bstep (se 3 (by rfl) ⟨1942646, by rfl⟩ : syracuseStep 10360781 = 3885293) B3885293
theorem B2586583 : Blo 1360499 2586583 := bstep (se 1 (by rfl) ⟨1939937, by rfl⟩ : syracuseStep 2586583 = 3879875) B3879875
theorem B2906113 : Blo 1360499 2906113 := bstep (se 2 (by rfl) ⟨1089792, by rfl⟩ : syracuseStep 2906113 = 2179585) B2179585
theorem B5519411 : Blo 1360499 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B3061835 : Blo 1360499 3061835 := bstep (se 1 (by rfl) ⟨2296376, by rfl⟩ : syracuseStep 3061835 = 4592753) B4592753
theorem B6895691 : Blo 1360499 6895691 := bstep (se 1 (by rfl) ⟨5171768, by rfl⟩ : syracuseStep 6895691 = 10343537) B10343537
theorem B1964119 : Blo 1360499 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B3061889 : Blo 1360499 3061889 := bstep (se 2 (by rfl) ⟨1148208, by rfl⟩ : syracuseStep 3061889 = 2296417) B2296417
theorem B4593995 : Blo 1360499 4593995 := bstep (se 1 (by rfl) ⟨3445496, by rfl⟩ : syracuseStep 4593995 = 6890993) B6890993
theorem B2906455 : Blo 1360499 2906455 := bstep (se 1 (by rfl) ⟨2179841, by rfl⟩ : syracuseStep 2906455 = 4359683) B4359683
theorem B3062105 : Blo 1360499 3062105 := bstep (se 2 (by rfl) ⟨1148289, by rfl⟩ : syracuseStep 3062105 = 2296579) B2296579
theorem B1939801 : Blo 1360499 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B3062195 : Blo 1360499 3062195 := bstep (se 1 (by rfl) ⟨2296646, by rfl⟩ : syracuseStep 3062195 = 4593293) B4593293
theorem B3062231 : Blo 1360499 3062231 := bstep (se 1 (by rfl) ⟨2296673, by rfl⟩ : syracuseStep 3062231 = 4593347) B4593347
theorem B5167577 : Blo 1360499 5167577 := bstep (se 2 (by rfl) ⟨1937841, by rfl⟩ : syracuseStep 5167577 = 3875683) B3875683
theorem B3447319 : Blo 1360499 3447319 := bstep (se 1 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 3447319 = 5170979) B5170979
theorem B9812515 : Blo 1360499 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B10344995 : Blo 1360499 10344995 := bstep (se 1 (by rfl) ⟨7758746, by rfl⟩ : syracuseStep 10344995 = 15517493) B15517493
theorem B4594265 : Blo 1360499 4594265 := bstep (se 2 (by rfl) ⟨1722849, by rfl⟩ : syracuseStep 4594265 = 3445699) B3445699
theorem B3062411 : Blo 1360499 3062411 := bstep (se 1 (by rfl) ⟨2296808, by rfl⟩ : syracuseStep 3062411 = 4593617) B4593617
theorem B3062465 : Blo 1360499 3062465 := bstep (se 2 (by rfl) ⟨1148424, by rfl⟩ : syracuseStep 3062465 = 2296849) B2296849
theorem B1530571 : Blo 1360499 1530571 := bstep (se 1 (by rfl) ⟨1147928, by rfl⟩ : syracuseStep 1530571 = 2295857) B2295857
theorem B6208301 : Blo 1360499 6208301 := bstep (se 3 (by rfl) ⟨1164056, by rfl⟩ : syracuseStep 6208301 = 2328113) B2328113
theorem B1530679 : Blo 1360499 1530679 := bstep (se 1 (by rfl) ⟨1148009, by rfl⟩ : syracuseStep 1530679 = 2296019) B2296019
theorem B2210635 : Blo 1360499 2210635 := bstep (se 1 (by rfl) ⟨1657976, by rfl⟩ : syracuseStep 2210635 = 3315953) B3315953
theorem B18619253 : Blo 1360499 18619253 := bstep (se 5 (by rfl) ⟨872777, by rfl⟩ : syracuseStep 18619253 = 1745555) B1745555
theorem B2907019 : Blo 1360499 2907019 := bstep (se 1 (by rfl) ⟨2180264, by rfl⟩ : syracuseStep 2907019 = 4360529) B4360529
theorem B3062681 : Blo 1360499 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B3447755 : Blo 1360499 3447755 := bstep (se 1 (by rfl) ⟨2585816, by rfl⟩ : syracuseStep 3447755 = 5171633) B5171633
theorem B1530859 : Blo 1360499 1530859 := bstep (se 1 (by rfl) ⟨1148144, by rfl⟩ : syracuseStep 1530859 = 2296289) B2296289
theorem B3062771 : Blo 1360499 3062771 := bstep (se 1 (by rfl) ⟨2297078, by rfl⟩ : syracuseStep 3062771 = 4594157) B4594157
theorem B3062807 : Blo 1360499 3062807 := bstep (se 1 (by rfl) ⟨2297105, by rfl⟩ : syracuseStep 3062807 = 4594211) B4594211
theorem B1530967 : Blo 1360499 1530967 := bstep (se 1 (by rfl) ⟨1148225, by rfl⟩ : syracuseStep 1530967 = 2296451) B2296451
theorem B2620505 : Blo 1360499 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B3062987 : Blo 1360499 3062987 := bstep (se 1 (by rfl) ⟨2297240, by rfl⟩ : syracuseStep 3062987 = 4594481) B4594481
theorem B11631833 : Blo 1360499 11631833 := bstep (se 2 (by rfl) ⟨4361937, by rfl⟩ : syracuseStep 11631833 = 8723875) B8723875
theorem B3063041 : Blo 1360499 3063041 := bstep (se 2 (by rfl) ⟨1148640, by rfl⟩ : syracuseStep 3063041 = 2297281) B2297281
theorem B1531147 : Blo 1360499 1531147 := bstep (se 1 (by rfl) ⟨1148360, by rfl⟩ : syracuseStep 1531147 = 2296721) B2296721
theorem B4594967 : Blo 1360499 4594967 := bstep (se 1 (by rfl) ⟨3446225, by rfl⟩ : syracuseStep 4594967 = 6892451) B6892451
theorem B3448129 : Blo 1360499 3448129 := bstep (se 2 (by rfl) ⟨1293048, by rfl⟩ : syracuseStep 3448129 = 2586097) B2586097
theorem B1531255 : Blo 1360499 1531255 := bstep (se 1 (by rfl) ⟨1148441, by rfl⟩ : syracuseStep 1531255 = 2296883) B2296883
theorem B4906433 : Blo 1360499 4906433 := bstep (se 2 (by rfl) ⟨1839912, by rfl⟩ : syracuseStep 4906433 = 3679825) B3679825
theorem B12426701 : Blo 1360499 12426701 := bstep (se 3 (by rfl) ⟨2330006, by rfl⟩ : syracuseStep 12426701 = 4660013) B4660013
theorem B3063257 : Blo 1360499 3063257 := bstep (se 2 (by rfl) ⟨1148721, by rfl⟩ : syracuseStep 3063257 = 2297443) B2297443
theorem B1965593 : Blo 1360499 1965593 := bstep (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) B1474195
theorem B1531435 : Blo 1360499 1531435 := bstep (se 1 (by rfl) ⟨1148576, by rfl⟩ : syracuseStep 1531435 = 2297153) B2297153
theorem B4906547 : Blo 1360499 4906547 := bstep (se 1 (by rfl) ⟨3679910, by rfl⟩ : syracuseStep 4906547 = 7359821) B7359821
theorem B3063347 : Blo 1360499 3063347 := bstep (se 1 (by rfl) ⟨2297510, by rfl⟩ : syracuseStep 3063347 = 4595021) B4595021
theorem B3063383 : Blo 1360499 3063383 := bstep (se 1 (by rfl) ⟨2297537, by rfl⟩ : syracuseStep 3063383 = 4595075) B4595075
theorem B5815901 : Blo 1360499 5815901 := bstep (se 3 (by rfl) ⟨1090481, by rfl⟩ : syracuseStep 5815901 = 2180963) B2180963
theorem B2211467 : Blo 1360499 2211467 := bstep (se 1 (by rfl) ⟨1658600, by rfl⟩ : syracuseStep 2211467 = 3317201) B3317201
theorem B1531543 : Blo 1360499 1531543 := bstep (se 1 (by rfl) ⟨1148657, by rfl⟩ : syracuseStep 1531543 = 2297315) B2297315
theorem B8724185 : Blo 1360499 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B3063563 : Blo 1360499 3063563 := bstep (se 1 (by rfl) ⟨2297672, by rfl⟩ : syracuseStep 3063563 = 4595345) B4595345
theorem B4595507 : Blo 1360499 4595507 := bstep (se 1 (by rfl) ⟨3446630, by rfl⟩ : syracuseStep 4595507 = 6893261) B6893261
theorem B3874625 : Blo 1360499 3874625 := bstep (se 2 (by rfl) ⟨1452984, by rfl⟩ : syracuseStep 3874625 = 2905969) B2905969
theorem B3063617 : Blo 1360499 3063617 := bstep (se 2 (by rfl) ⟨1148856, by rfl⟩ : syracuseStep 3063617 = 2297713) B2297713
theorem B6897473 : Blo 1360499 6897473 := bstep (se 2 (by rfl) ⟨2586552, by rfl⟩ : syracuseStep 6897473 = 5173105) B5173105
theorem B1531723 : Blo 1360499 1531723 := bstep (se 1 (by rfl) ⟨1148792, by rfl⟩ : syracuseStep 1531723 = 2297585) B2297585
theorem B3448727 : Blo 1360499 3448727 := bstep (se 1 (by rfl) ⟨2586545, by rfl⟩ : syracuseStep 3448727 = 5173091) B5173091
theorem B1531831 : Blo 1360499 1531831 := bstep (se 1 (by rfl) ⟨1148873, by rfl⟩ : syracuseStep 1531831 = 2297747) B2297747
theorem B2949107 : Blo 1360499 2949107 := bstep (se 1 (by rfl) ⟨2211830, by rfl⟩ : syracuseStep 2949107 = 4423661) B4423661
theorem B3874817 : Blo 1360499 3874817 := bstep (se 2 (by rfl) ⟨1453056, by rfl⟩ : syracuseStep 3874817 = 2906113) B2906113
theorem B4595723 : Blo 1360499 4595723 := bstep (se 1 (by rfl) ⟨3446792, by rfl⟩ : syracuseStep 4595723 = 6893585) B6893585
theorem B3678223 : Blo 1360499 3678223 := bstep (se 1 (by rfl) ⟨2758667, by rfl⟩ : syracuseStep 3678223 = 5517335) B5517335
theorem B3063851 : Blo 1360499 3063851 := bstep (se 1 (by rfl) ⟨2297888, by rfl⟩ : syracuseStep 3063851 = 4595777) B4595777
theorem B4595831 : Blo 1360499 4595831 := bstep (se 1 (by rfl) ⟨3446873, by rfl⟩ : syracuseStep 4595831 = 6893747) B6893747
theorem B1532047 : Blo 1360499 1532047 := bstep (se 1 (by rfl) ⟨1149035, by rfl⟩ : syracuseStep 1532047 = 2298071) B2298071
theorem B2908361 : Blo 1360499 2908361 := bstep (se 2 (by rfl) ⟨1090635, by rfl⟩ : syracuseStep 2908361 = 2181271) B2181271
theorem B15516035 : Blo 1360499 15516035 := bstep (se 1 (by rfl) ⟨11637026, by rfl⟩ : syracuseStep 15516035 = 23274053) B23274053
theorem B3064211 : Blo 1360499 3064211 := bstep (se 1 (by rfl) ⟨2298158, by rfl⟩ : syracuseStep 3064211 = 4596317) B4596317
theorem B3875273 : Blo 1360499 3875273 := bstep (se 2 (by rfl) ⟨1453227, by rfl⟩ : syracuseStep 3875273 = 2906455) B2906455
theorem B3064265 : Blo 1360499 3064265 := bstep (se 2 (by rfl) ⟨1149099, by rfl⟩ : syracuseStep 3064265 = 2298199) B2298199
theorem B1360519 : Blo 1360499 1360519 := bstep (se 1 (by rfl) ⟨1020389, by rfl⟩ : syracuseStep 1360519 = 2040779) B2040779
theorem B1532551 : Blo 1360499 1532551 := bstep (se 1 (by rfl) ⟨1149413, by rfl⟩ : syracuseStep 1532551 = 2298827) B2298827
theorem B1360527 : Blo 1360499 1360527 := bstep (se 1 (by rfl) ⟨1020395, by rfl⟩ : syracuseStep 1360527 = 2040791) B2040791
theorem B1360571 : Blo 1360499 1360571 := bstep (se 1 (by rfl) ⟨1020428, by rfl⟩ : syracuseStep 1360571 = 2040857) B2040857
theorem B4596425 : Blo 1360499 4596425 := bstep (se 2 (by rfl) ⟨1723659, by rfl⟩ : syracuseStep 4596425 = 3447319) B3447319
theorem B13083353 : Blo 1360499 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B1360647 : Blo 1360499 1360647 := bstep (se 1 (by rfl) ⟨1020485, by rfl⟩ : syracuseStep 1360647 = 2040971) B2040971
theorem B1360655 : Blo 1360499 1360655 := bstep (se 1 (by rfl) ⟨1020491, by rfl⟩ : syracuseStep 1360655 = 2040983) B2040983
theorem B3875627 : Blo 1360499 3875627 := bstep (se 1 (by rfl) ⟨2906720, by rfl⟩ : syracuseStep 3875627 = 5813441) B5813441
theorem B1360699 : Blo 1360499 1360699 := bstep (se 1 (by rfl) ⟨1020524, by rfl⟩ : syracuseStep 1360699 = 2041049) B2041049
theorem B1532731 : Blo 1360499 1532731 := bstep (se 1 (by rfl) ⟨1149548, by rfl⟩ : syracuseStep 1532731 = 2299097) B2299097
theorem B1360775 : Blo 1360499 1360775 := bstep (se 1 (by rfl) ⟨1020581, by rfl⟩ : syracuseStep 1360775 = 2041163) B2041163
theorem B1360783 : Blo 1360499 1360783 := bstep (se 1 (by rfl) ⟨1020587, by rfl⟩ : syracuseStep 1360783 = 2041175) B2041175
theorem B6546329 : Blo 1360499 6546329 := bstep (se 2 (by rfl) ⟨2454873, by rfl⟩ : syracuseStep 6546329 = 4909747) B4909747
theorem B2040761 : Blo 1360499 2040761 := bstep (se 2 (by rfl) ⟨765285, by rfl⟩ : syracuseStep 2040761 = 1530571) B1530571
theorem B1360827 : Blo 1360499 1360827 := bstep (se 1 (by rfl) ⟨1020620, by rfl⟩ : syracuseStep 1360827 = 2041241) B2041241
theorem B2040839 : Blo 1360499 2040839 := bstep (se 1 (by rfl) ⟨1530629, by rfl⟩ : syracuseStep 2040839 = 3061259) B3061259
theorem B1360903 : Blo 1360499 1360903 := bstep (se 1 (by rfl) ⟨1020677, by rfl⟩ : syracuseStep 1360903 = 2041355) B2041355
theorem B6890507 : Blo 1360499 6890507 := bstep (se 1 (by rfl) ⟨5167880, by rfl⟩ : syracuseStep 6890507 = 10335761) B10335761
theorem B9815051 : Blo 1360499 9815051 := bstep (se 1 (by rfl) ⟨7361288, by rfl⟩ : syracuseStep 9815051 = 14722577) B14722577
theorem B1360911 : Blo 1360499 1360911 := bstep (se 1 (by rfl) ⟨1020683, by rfl⟩ : syracuseStep 1360911 = 2041367) B2041367
theorem B16548887 : Blo 1360499 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B4359197 : Blo 1360499 4359197 := bstep (se 3 (by rfl) ⟨817349, by rfl⟩ : syracuseStep 4359197 = 1634699) B1634699
theorem B2040875 : Blo 1360499 2040875 := bstep (se 1 (by rfl) ⟨1530656, by rfl⟩ : syracuseStep 2040875 = 3061313) B3061313
theorem B1360955 : Blo 1360499 1360955 := bstep (se 1 (by rfl) ⟨1020716, by rfl⟩ : syracuseStep 1360955 = 2041433) B2041433
theorem B2040905 : Blo 1360499 2040905 := bstep (se 2 (by rfl) ⟨765339, by rfl⟩ : syracuseStep 2040905 = 1530679) B1530679
theorem B6628439 : Blo 1360499 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B2761847 : Blo 1360499 2761847 := bstep (se 1 (by rfl) ⟨2071385, by rfl⟩ : syracuseStep 2761847 = 4142771) B4142771
theorem B1361031 : Blo 1360499 1361031 := bstep (se 1 (by rfl) ⟨1020773, by rfl⟩ : syracuseStep 1361031 = 2041547) B2041547
theorem B3064967 : Blo 1360499 3064967 := bstep (se 1 (by rfl) ⟨2298725, by rfl⟩ : syracuseStep 3064967 = 4597451) B4597451
theorem B1361039 : Blo 1360499 1361039 := bstep (se 1 (by rfl) ⟨1020779, by rfl⟩ : syracuseStep 1361039 = 2041559) B2041559
theorem B6890669 : Blo 1360499 6890669 := bstep (se 3 (by rfl) ⟨1292000, by rfl⟩ : syracuseStep 6890669 = 2584001) B2584001
theorem B3876025 : Blo 1360499 3876025 := bstep (se 2 (by rfl) ⟨1453509, by rfl⟩ : syracuseStep 3876025 = 2907019) B2907019
theorem B2041019 : Blo 1360499 2041019 := bstep (se 1 (by rfl) ⟨1530764, by rfl⟩ : syracuseStep 2041019 = 3061529) B3061529
theorem B1361083 : Blo 1360499 1361083 := bstep (se 1 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 1361083 = 2041625) B2041625
theorem B3728585 : Blo 1360499 3728585 := bstep (se 2 (by rfl) ⟨1398219, by rfl⟩ : syracuseStep 3728585 = 2796439) B2796439
theorem B2180297 : Blo 1360499 2180297 := bstep (se 2 (by rfl) ⟨817611, by rfl⟩ : syracuseStep 2180297 = 1635223) B1635223
theorem B33137869 : Blo 1360499 33137869 := bstep (se 3 (by rfl) ⟨6213350, by rfl⟩ : syracuseStep 33137869 = 12426701) B12426701
theorem B2041079 : Blo 1360499 2041079 := bstep (se 1 (by rfl) ⟨1530809, by rfl⟩ : syracuseStep 2041079 = 3061619) B3061619
theorem B1361159 : Blo 1360499 1361159 := bstep (se 1 (by rfl) ⟨1020869, by rfl⟩ : syracuseStep 1361159 = 2041739) B2041739
theorem B2041103 : Blo 1360499 2041103 := bstep (se 1 (by rfl) ⟨1530827, by rfl⟩ : syracuseStep 2041103 = 3061655) B3061655
theorem B1361167 : Blo 1360499 1361167 := bstep (se 1 (by rfl) ⟨1020875, by rfl⟩ : syracuseStep 1361167 = 2041751) B2041751
theorem B6907187 : Blo 1360499 6907187 := bstep (se 1 (by rfl) ⟨5180390, by rfl⟩ : syracuseStep 6907187 = 10360781) B10360781
theorem B2041145 : Blo 1360499 2041145 := bstep (se 2 (by rfl) ⟨765429, by rfl⟩ : syracuseStep 2041145 = 1530859) B1530859
theorem B8504635 : Blo 1360499 8504635 := bstep (se 1 (by rfl) ⟨6378476, by rfl⟩ : syracuseStep 8504635 = 12756953) B12756953
theorem B1361211 : Blo 1360499 1361211 := bstep (se 1 (by rfl) ⟨1020908, by rfl⟩ : syracuseStep 1361211 = 2041817) B2041817
theorem B3065147 : Blo 1360499 3065147 := bstep (se 1 (by rfl) ⟨2298860, by rfl⟩ : syracuseStep 3065147 = 4597721) B4597721
theorem B3679607 : Blo 1360499 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B2041223 : Blo 1360499 2041223 := bstep (se 1 (by rfl) ⟨1530917, by rfl⟩ : syracuseStep 2041223 = 3061835) B3061835
theorem B1361287 : Blo 1360499 1361287 := bstep (se 1 (by rfl) ⟨1020965, by rfl⟩ : syracuseStep 1361287 = 2041931) B2041931
theorem B4597127 : Blo 1360499 4597127 := bstep (se 1 (by rfl) ⟨3447845, by rfl⟩ : syracuseStep 4597127 = 6895691) B6895691
theorem B1361295 : Blo 1360499 1361295 := bstep (se 1 (by rfl) ⟨1020971, by rfl⟩ : syracuseStep 1361295 = 2041943) B2041943
theorem B2041259 : Blo 1360499 2041259 := bstep (se 1 (by rfl) ⟨1530944, by rfl⟩ : syracuseStep 2041259 = 3061889) B3061889
theorem B3065273 : Blo 1360499 3065273 := bstep (se 2 (by rfl) ⟨1149477, by rfl⟩ : syracuseStep 3065273 = 2298955) B2298955
theorem B1361339 : Blo 1360499 1361339 := bstep (se 1 (by rfl) ⟨1021004, by rfl⟩ : syracuseStep 1361339 = 2042009) B2042009
theorem B2041289 : Blo 1360499 2041289 := bstep (se 2 (by rfl) ⟨765483, by rfl⟩ : syracuseStep 2041289 = 1530967) B1530967
theorem B3270089 : Blo 1360499 3270089 := bstep (se 2 (by rfl) ⟨1226283, by rfl⟩ : syracuseStep 3270089 = 2452567) B2452567
theorem B8717777 : Blo 1360499 8717777 := bstep (se 2 (by rfl) ⟨3269166, by rfl⟩ : syracuseStep 8717777 = 6538333) B6538333
theorem B8717827 : Blo 1360499 8717827 := bstep (se 1 (by rfl) ⟨6538370, by rfl⟩ : syracuseStep 8717827 = 13076741) B13076741
theorem B1361415 : Blo 1360499 1361415 := bstep (se 1 (by rfl) ⟨1021061, by rfl⟩ : syracuseStep 1361415 = 2042123) B2042123
theorem B1361423 : Blo 1360499 1361423 := bstep (se 1 (by rfl) ⟨1021067, by rfl⟩ : syracuseStep 1361423 = 2042135) B2042135
theorem B5817899 : Blo 1360499 5817899 := bstep (se 1 (by rfl) ⟨4363424, by rfl⟩ : syracuseStep 5817899 = 8726849) B8726849
theorem B2041403 : Blo 1360499 2041403 := bstep (se 1 (by rfl) ⟨1531052, by rfl⟩ : syracuseStep 2041403 = 3062105) B3062105
theorem B1361467 : Blo 1360499 1361467 := bstep (se 1 (by rfl) ⟨1021100, by rfl⟩ : syracuseStep 1361467 = 2042201) B2042201
theorem B67176013 : Blo 1360499 67176013 := bstep (se 3 (by rfl) ⟨12595502, by rfl⟩ : syracuseStep 67176013 = 25191005) B25191005
theorem B2041463 : Blo 1360499 2041463 := bstep (se 1 (by rfl) ⟨1531097, by rfl⟩ : syracuseStep 2041463 = 3062195) B3062195
theorem B1361543 : Blo 1360499 1361543 := bstep (se 1 (by rfl) ⟨1021157, by rfl⟩ : syracuseStep 1361543 = 2042315) B2042315
theorem B1721999 : Blo 1360499 1721999 := bstep (se 1 (by rfl) ⟨1291499, by rfl⟩ : syracuseStep 1721999 = 2582999) B2582999
theorem B2041487 : Blo 1360499 2041487 := bstep (se 1 (by rfl) ⟨1531115, by rfl⟩ : syracuseStep 2041487 = 3062231) B3062231
theorem B1361551 : Blo 1360499 1361551 := bstep (se 1 (by rfl) ⟨1021163, by rfl⟩ : syracuseStep 1361551 = 2042327) B2042327
theorem B2041529 : Blo 1360499 2041529 := bstep (se 2 (by rfl) ⟨765573, by rfl⟩ : syracuseStep 2041529 = 1531147) B1531147
theorem B1361595 : Blo 1360499 1361595 := bstep (se 1 (by rfl) ⟨1021196, by rfl⟩ : syracuseStep 1361595 = 2042393) B2042393
theorem B4597505 : Blo 1360499 4597505 := bstep (se 2 (by rfl) ⟨1724064, by rfl⟩ : syracuseStep 4597505 = 3448129) B3448129
theorem B2041607 : Blo 1360499 2041607 := bstep (se 1 (by rfl) ⟨1531205, by rfl⟩ : syracuseStep 2041607 = 3062411) B3062411
theorem B1361671 : Blo 1360499 1361671 := bstep (se 1 (by rfl) ⟨1021253, by rfl⟩ : syracuseStep 1361671 = 2042507) B2042507
theorem B1361679 : Blo 1360499 1361679 := bstep (se 1 (by rfl) ⟨1021259, by rfl⟩ : syracuseStep 1361679 = 2042519) B2042519
theorem B3065615 : Blo 1360499 3065615 := bstep (se 1 (by rfl) ⟨2299211, by rfl⟩ : syracuseStep 3065615 = 4598423) B4598423
theorem B16549667 : Blo 1360499 16549667 := bstep (se 1 (by rfl) ⟨12412250, by rfl⟩ : syracuseStep 16549667 = 24824501) B24824501
theorem B2041643 : Blo 1360499 2041643 := bstep (se 1 (by rfl) ⟨1531232, by rfl⟩ : syracuseStep 2041643 = 3062465) B3062465
theorem B1361723 : Blo 1360499 1361723 := bstep (se 1 (by rfl) ⟨1021292, by rfl⟩ : syracuseStep 1361723 = 2042585) B2042585
theorem B2041673 : Blo 1360499 2041673 := bstep (se 2 (by rfl) ⟨765627, by rfl⟩ : syracuseStep 2041673 = 1531255) B1531255
theorem B4138867 : Blo 1360499 4138867 := bstep (se 1 (by rfl) ⟨3104150, by rfl⟩ : syracuseStep 4138867 = 6208301) B6208301
theorem B1361799 : Blo 1360499 1361799 := bstep (se 1 (by rfl) ⟨1021349, by rfl⟩ : syracuseStep 1361799 = 2042699) B2042699
theorem B1361807 : Blo 1360499 1361807 := bstep (se 1 (by rfl) ⟨1021355, by rfl⟩ : syracuseStep 1361807 = 2042711) B2042711
theorem B12412835 : Blo 1360499 12412835 := bstep (se 1 (by rfl) ⟨9309626, by rfl⟩ : syracuseStep 12412835 = 18619253) B18619253
theorem B2041787 : Blo 1360499 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B1361851 : Blo 1360499 1361851 := bstep (se 1 (by rfl) ⟨1021388, by rfl⟩ : syracuseStep 1361851 = 2042777) B2042777
theorem B2041847 : Blo 1360499 2041847 := bstep (se 1 (by rfl) ⟨1531385, by rfl⟩ : syracuseStep 2041847 = 3062771) B3062771
theorem B1361927 : Blo 1360499 1361927 := bstep (se 1 (by rfl) ⟨1021445, by rfl⟩ : syracuseStep 1361927 = 2042891) B2042891
theorem B2041871 : Blo 1360499 2041871 := bstep (se 1 (by rfl) ⟨1531403, by rfl⟩ : syracuseStep 2041871 = 3062807) B3062807
theorem B1361935 : Blo 1360499 1361935 := bstep (se 1 (by rfl) ⟨1021451, by rfl⟩ : syracuseStep 1361935 = 2042903) B2042903
theorem B26167319 : Blo 1360499 26167319 := bstep (se 1 (by rfl) ⟨19625489, by rfl⟩ : syracuseStep 26167319 = 39250979) B39250979
theorem B8390699 : Blo 1360499 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B24823853 : Blo 1360499 24823853 := bstep (se 3 (by rfl) ⟨4654472, by rfl⟩ : syracuseStep 24823853 = 9308945) B9308945
theorem B2041913 : Blo 1360499 2041913 := bstep (se 2 (by rfl) ⟨765717, by rfl⟩ : syracuseStep 2041913 = 1531435) B1531435
theorem B1747003 : Blo 1360499 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B1361979 : Blo 1360499 1361979 := bstep (se 1 (by rfl) ⟨1021484, by rfl⟩ : syracuseStep 1361979 = 2042969) B2042969
theorem B2181239 : Blo 1360499 2181239 := bstep (se 1 (by rfl) ⟨1635929, by rfl⟩ : syracuseStep 2181239 = 3271859) B3271859
theorem B2041991 : Blo 1360499 2041991 := bstep (se 1 (by rfl) ⟨1531493, by rfl⟩ : syracuseStep 2041991 = 3062987) B3062987
theorem B1362055 : Blo 1360499 1362055 := bstep (se 1 (by rfl) ⟨1021541, by rfl⟩ : syracuseStep 1362055 = 2043083) B2043083
theorem B1362063 : Blo 1360499 1362063 := bstep (se 1 (by rfl) ⟨1021547, by rfl⟩ : syracuseStep 1362063 = 2043095) B2043095
theorem B2042027 : Blo 1360499 2042027 := bstep (se 1 (by rfl) ⟨1531520, by rfl⟩ : syracuseStep 2042027 = 3063041) B3063041
theorem B1362107 : Blo 1360499 1362107 := bstep (se 1 (by rfl) ⟨1021580, by rfl⟩ : syracuseStep 1362107 = 2043161) B2043161
theorem B2042057 : Blo 1360499 2042057 := bstep (se 2 (by rfl) ⟨765771, by rfl⟩ : syracuseStep 2042057 = 1531543) B1531543
theorem B1362183 : Blo 1360499 1362183 := bstep (se 1 (by rfl) ⟨1021637, by rfl⟩ : syracuseStep 1362183 = 2043275) B2043275
theorem B1362191 : Blo 1360499 1362191 := bstep (se 1 (by rfl) ⟨1021643, by rfl⟩ : syracuseStep 1362191 = 2043287) B2043287
theorem B2451745 : Blo 1360499 2451745 := bstep (se 2 (by rfl) ⟨919404, by rfl⟩ : syracuseStep 2451745 = 1838809) B1838809
theorem B3270955 : Blo 1360499 3270955 := bstep (se 1 (by rfl) ⟨2453216, by rfl⟩ : syracuseStep 3270955 = 4906433) B4906433
theorem B2042171 : Blo 1360499 2042171 := bstep (se 1 (by rfl) ⟨1531628, by rfl⟩ : syracuseStep 2042171 = 3063257) B3063257
theorem B1362235 : Blo 1360499 1362235 := bstep (se 1 (by rfl) ⟨1021676, by rfl⟩ : syracuseStep 1362235 = 2043353) B2043353
theorem B3271031 : Blo 1360499 3271031 := bstep (se 1 (by rfl) ⟨2453273, by rfl⟩ : syracuseStep 3271031 = 4906547) B4906547
theorem B2042231 : Blo 1360499 2042231 := bstep (se 1 (by rfl) ⟨1531673, by rfl⟩ : syracuseStep 2042231 = 3063347) B3063347
theorem B1362311 : Blo 1360499 1362311 := bstep (se 1 (by rfl) ⟨1021733, by rfl⟩ : syracuseStep 1362311 = 2043467) B2043467
theorem B2042255 : Blo 1360499 2042255 := bstep (se 1 (by rfl) ⟨1531691, by rfl⟩ : syracuseStep 2042255 = 3063383) B3063383
theorem B1362319 : Blo 1360499 1362319 := bstep (se 1 (by rfl) ⟨1021739, by rfl⟩ : syracuseStep 1362319 = 2043479) B2043479
theorem B3877267 : Blo 1360499 3877267 := bstep (se 1 (by rfl) ⟨2907950, by rfl⟩ : syracuseStep 3877267 = 5815901) B5815901
theorem B2042297 : Blo 1360499 2042297 := bstep (se 2 (by rfl) ⟨765861, by rfl⟩ : syracuseStep 2042297 = 1531723) B1531723
theorem B1362363 : Blo 1360499 1362363 := bstep (se 1 (by rfl) ⟨1021772, by rfl⟩ : syracuseStep 1362363 = 2043545) B2043545
theorem B2042375 : Blo 1360499 2042375 := bstep (se 1 (by rfl) ⟨1531781, by rfl⟩ : syracuseStep 2042375 = 3063563) B3063563
theorem B1362439 : Blo 1360499 1362439 := bstep (se 1 (by rfl) ⟨1021829, by rfl⟩ : syracuseStep 1362439 = 2043659) B2043659
theorem B1362447 : Blo 1360499 1362447 := bstep (se 1 (by rfl) ⟨1021835, by rfl⟩ : syracuseStep 1362447 = 2043671) B2043671
theorem B2583083 : Blo 1360499 2583083 := bstep (se 1 (by rfl) ⟨1937312, by rfl⟩ : syracuseStep 2583083 = 3874625) B3874625
theorem B2296363 : Blo 1360499 2296363 := bstep (se 1 (by rfl) ⟨1722272, by rfl⟩ : syracuseStep 2296363 = 3444545) B3444545
theorem B2042411 : Blo 1360499 2042411 := bstep (se 1 (by rfl) ⟨1531808, by rfl⟩ : syracuseStep 2042411 = 3063617) B3063617
theorem B4598315 : Blo 1360499 4598315 := bstep (se 1 (by rfl) ⟨3448736, by rfl⟩ : syracuseStep 4598315 = 6897473) B6897473
theorem B1362491 : Blo 1360499 1362491 := bstep (se 1 (by rfl) ⟨1021868, by rfl⟩ : syracuseStep 1362491 = 2043737) B2043737
theorem B2042441 : Blo 1360499 2042441 := bstep (se 2 (by rfl) ⟨765915, by rfl⟩ : syracuseStep 2042441 = 1531831) B1531831
theorem B2296505 : Blo 1360499 2296505 := bstep (se 2 (by rfl) ⟨861189, by rfl⟩ : syracuseStep 2296505 = 1722379) B1722379
theorem B2042555 : Blo 1360499 2042555 := bstep (se 1 (by rfl) ⟨1531916, by rfl⟩ : syracuseStep 2042555 = 3063833) B3063833
theorem B26520281 : Blo 1360499 26520281 := bstep (se 2 (by rfl) ⟨9945105, by rfl⟩ : syracuseStep 26520281 = 19890211) B19890211
theorem B2042615 : Blo 1360499 2042615 := bstep (se 1 (by rfl) ⟨1531961, by rfl⟩ : syracuseStep 2042615 = 3063923) B3063923
theorem B6892289 : Blo 1360499 6892289 := bstep (se 2 (by rfl) ⟨2584608, by rfl⟩ : syracuseStep 6892289 = 5169217) B5169217
theorem B2042639 : Blo 1360499 2042639 := bstep (se 1 (by rfl) ⟨1531979, by rfl⟩ : syracuseStep 2042639 = 3063959) B3063959
theorem B2042681 : Blo 1360499 2042681 := bstep (se 2 (by rfl) ⟨766005, by rfl⟩ : syracuseStep 2042681 = 1532011) B1532011
theorem B3730295 : Blo 1360499 3730295 := bstep (se 1 (by rfl) ⟨2797721, by rfl⟩ : syracuseStep 3730295 = 5595443) B5595443
theorem B2042759 : Blo 1360499 2042759 := bstep (se 1 (by rfl) ⟨1532069, by rfl⟩ : syracuseStep 2042759 = 3064139) B3064139
theorem B2042795 : Blo 1360499 2042795 := bstep (se 1 (by rfl) ⟨1532096, by rfl⟩ : syracuseStep 2042795 = 3064193) B3064193
theorem B2042825 : Blo 1360499 2042825 := bstep (se 2 (by rfl) ⟨766059, by rfl⟩ : syracuseStep 2042825 = 1532119) B1532119
theorem B6982699 : Blo 1360499 6982699 := bstep (se 1 (by rfl) ⟨5237024, by rfl⟩ : syracuseStep 6982699 = 10474049) B10474049
theorem B2042939 : Blo 1360499 2042939 := bstep (se 1 (by rfl) ⟨1532204, by rfl⟩ : syracuseStep 2042939 = 3064409) B3064409
theorem B2042999 : Blo 1360499 2042999 := bstep (se 1 (by rfl) ⟨1532249, by rfl⟩ : syracuseStep 2042999 = 3064499) B3064499
theorem B2043023 : Blo 1360499 2043023 := bstep (se 1 (by rfl) ⟨1532267, by rfl⟩ : syracuseStep 2043023 = 3064535) B3064535
theorem B3443897 : Blo 1360499 3443897 := bstep (se 2 (by rfl) ⟨1291461, by rfl⟩ : syracuseStep 3443897 = 2582923) B2582923
theorem B2043065 : Blo 1360499 2043065 := bstep (se 2 (by rfl) ⟨766149, by rfl⟩ : syracuseStep 2043065 = 1532299) B1532299
theorem B2043143 : Blo 1360499 2043143 := bstep (se 1 (by rfl) ⟨1532357, by rfl⟩ : syracuseStep 2043143 = 3064715) B3064715
theorem B2043179 : Blo 1360499 2043179 := bstep (se 1 (by rfl) ⟨1532384, by rfl⟩ : syracuseStep 2043179 = 3064769) B3064769
theorem B2043209 : Blo 1360499 2043209 := bstep (se 2 (by rfl) ⟨766203, by rfl⟩ : syracuseStep 2043209 = 1532407) B1532407
theorem B2297207 : Blo 1360499 2297207 := bstep (se 1 (by rfl) ⟨1722905, by rfl⟩ : syracuseStep 2297207 = 3445811) B3445811
theorem B13077895 : Blo 1360499 13077895 := bstep (se 1 (by rfl) ⟨9808421, by rfl⟩ : syracuseStep 13077895 = 19616843) B19616843
theorem B8719751 : Blo 1360499 8719751 := bstep (se 1 (by rfl) ⟨6539813, by rfl⟩ : syracuseStep 8719751 = 13079627) B13079627
theorem B3681683 : Blo 1360499 3681683 := bstep (se 1 (by rfl) ⟨2761262, by rfl⟩ : syracuseStep 3681683 = 5522525) B5522525
theorem B3272089 : Blo 1360499 3272089 := bstep (se 2 (by rfl) ⟨1227033, by rfl⟩ : syracuseStep 3272089 = 2454067) B2454067
theorem B2043323 : Blo 1360499 2043323 := bstep (se 1 (by rfl) ⟨1532492, by rfl⟩ : syracuseStep 2043323 = 3064985) B3064985
theorem B2043383 : Blo 1360499 2043383 := bstep (se 1 (by rfl) ⟨1532537, by rfl⟩ : syracuseStep 2043383 = 3065075) B3065075
theorem B2043407 : Blo 1360499 2043407 := bstep (se 1 (by rfl) ⟨1532555, by rfl⟩ : syracuseStep 2043407 = 3065111) B3065111
theorem B6893099 : Blo 1360499 6893099 := bstep (se 1 (by rfl) ⟨5169824, by rfl⟩ : syracuseStep 6893099 = 10339649) B10339649
theorem B2043449 : Blo 1360499 2043449 := bstep (se 2 (by rfl) ⟨766293, by rfl⟩ : syracuseStep 2043449 = 1532587) B1532587
theorem B15502913 : Blo 1360499 15502913 := bstep (se 2 (by rfl) ⟨5813592, by rfl⟩ : syracuseStep 15502913 = 11627185) B11627185
theorem B2584199 : Blo 1360499 2584199 := bstep (se 1 (by rfl) ⟨1938149, by rfl⟩ : syracuseStep 2584199 = 3876299) B3876299
theorem B4140679 : Blo 1360499 4140679 := bstep (se 1 (by rfl) ⟨3105509, by rfl⟩ : syracuseStep 4140679 = 6211019) B6211019
theorem B2043527 : Blo 1360499 2043527 := bstep (se 1 (by rfl) ⟨1532645, by rfl⟩ : syracuseStep 2043527 = 3065291) B3065291
theorem B2043563 : Blo 1360499 2043563 := bstep (se 1 (by rfl) ⟨1532672, by rfl⟩ : syracuseStep 2043563 = 3065345) B3065345
theorem B2043593 : Blo 1360499 2043593 := bstep (se 2 (by rfl) ⟨766347, by rfl⟩ : syracuseStep 2043593 = 1532695) B1532695
theorem B2297659 : Blo 1360499 2297659 := bstep (se 1 (by rfl) ⟨1723244, by rfl⟩ : syracuseStep 2297659 = 3446489) B3446489
theorem B2043707 : Blo 1360499 2043707 := bstep (se 1 (by rfl) ⟨1532780, by rfl⟩ : syracuseStep 2043707 = 3065561) B3065561
theorem B4362169 : Blo 1360499 4362169 := bstep (se 2 (by rfl) ⟨1635813, by rfl⟩ : syracuseStep 4362169 = 3271627) B3271627
theorem B2297801 : Blo 1360499 2297801 := bstep (se 2 (by rfl) ⟨861675, by rfl⟩ : syracuseStep 2297801 = 1723351) B1723351
theorem B27955147 : Blo 1360499 27955147 := bstep (se 1 (by rfl) ⟨20966360, by rfl⟩ : syracuseStep 27955147 = 41932721) B41932721
theorem B3878941 : Blo 1360499 3878941 := bstep (se 3 (by rfl) ⟨727301, by rfl⟩ : syracuseStep 3878941 = 1454603) B1454603
theorem B3878999 : Blo 1360499 3878999 := bstep (se 1 (by rfl) ⟨2909249, by rfl⟩ : syracuseStep 3878999 = 5818499) B5818499
theorem B23588981 : Blo 1360499 23588981 := bstep (se 5 (by rfl) ⟨1105733, by rfl⟩ : syracuseStep 23588981 = 2211467) B2211467
theorem B2584723 : Blo 1360499 2584723 := bstep (se 1 (by rfl) ⟨1938542, by rfl⟩ : syracuseStep 2584723 = 3877085) B3877085
theorem B3444889 : Blo 1360499 3444889 := bstep (se 2 (by rfl) ⟨1291833, by rfl⟩ : syracuseStep 3444889 = 2583667) B2583667
theorem B4657441 : Blo 1360499 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B3445051 : Blo 1360499 3445051 := bstep (se 1 (by rfl) ⟨2583788, by rfl⟩ : syracuseStep 3445051 = 5167577) B5167577
theorem B3445193 : Blo 1360499 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B198758933 : Blo 1360499 198758933 := bstep (se 6 (by rfl) ⟨4658412, by rfl⟩ : syracuseStep 198758933 = 9316825) B9316825
theorem B7565885 : Blo 1360499 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B8729207 : Blo 1360499 8729207 := bstep (se 1 (by rfl) ⟨6546905, by rfl⟩ : syracuseStep 8729207 = 13093811) B13093811
theorem B2298503 : Blo 1360499 2298503 := bstep (se 1 (by rfl) ⟨1723877, by rfl⟩ : syracuseStep 2298503 = 3447755) B3447755
theorem B3273473 : Blo 1360499 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B3445537 : Blo 1360499 3445537 := bstep (se 2 (by rfl) ⟨1292076, by rfl⟩ : syracuseStep 3445537 = 2584153) B2584153
theorem B7754555 : Blo 1360499 7754555 := bstep (se 1 (by rfl) ⟨5815916, by rfl⟩ : syracuseStep 7754555 = 11631833) B11631833
theorem B6894395 : Blo 1360499 6894395 := bstep (se 1 (by rfl) ⟨5170796, by rfl⟩ : syracuseStep 6894395 = 10341593) B10341593
theorem B2454391 : Blo 1360499 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B4592537 : Blo 1360499 4592537 := bstep (se 2 (by rfl) ⟨1722201, by rfl⟩ : syracuseStep 4592537 = 3444403) B3444403
theorem B1938377 : Blo 1360499 1938377 := bstep (se 2 (by rfl) ⟨726891, by rfl⟩ : syracuseStep 1938377 = 1453783) B1453783
theorem B6894557 : Blo 1360499 6894557 := bstep (se 3 (by rfl) ⟨1292729, by rfl⟩ : syracuseStep 6894557 = 2585459) B2585459
theorem B2299151 : Blo 1360499 2299151 := bstep (se 1 (by rfl) ⟨1724363, by rfl⟩ : syracuseStep 2299151 = 3448727) B3448727
theorem B6894881 : Blo 1360499 6894881 := bstep (se 2 (by rfl) ⟨2585580, by rfl⟩ : syracuseStep 6894881 = 5171161) B5171161
theorem B2585915 : Blo 1360499 2585915 := bstep (se 1 (by rfl) ⟨1939436, by rfl⟩ : syracuseStep 2585915 = 3878873) B3878873
theorem B3446135 : Blo 1360499 3446135 := bstep (se 1 (by rfl) ⟨2584601, by rfl⟩ : syracuseStep 3446135 = 5169203) B5169203
theorem B37246387 : Blo 1360499 37246387 := bstep (se 1 (by rfl) ⟨27934790, by rfl⟩ : syracuseStep 37246387 = 55869581) B55869581
theorem B2618825 : Blo 1360499 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B1938935 : Blo 1360499 1938935 := bstep (se 1 (by rfl) ⟨1454201, by rfl⟩ : syracuseStep 1938935 = 2908403) B2908403
theorem B5518891 : Blo 1360499 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B4593239 : Blo 1360499 4593239 := bstep (se 1 (by rfl) ⟨3444929, by rfl⟩ : syracuseStep 4593239 = 6889859) B6889859
theorem B3061367 : Blo 1360499 3061367 := bstep (se 1 (by rfl) ⟨2296025, by rfl⟩ : syracuseStep 3061367 = 4592051) B4592051
theorem B2586401 : Blo 1360499 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B3061547 : Blo 1360499 3061547 := bstep (se 1 (by rfl) ⟨2296160, by rfl⟩ : syracuseStep 3061547 = 4592321) B4592321
theorem B1939243 : Blo 1360499 1939243 := bstep (se 1 (by rfl) ⟨1454432, by rfl⟩ : syracuseStep 1939243 = 2908865) B2908865
theorem B15341363 : Blo 1360499 15341363 := bstep (se 1 (by rfl) ⟨11506022, by rfl⟩ : syracuseStep 15341363 = 23012045) B23012045
theorem B14931863 : Blo 1360499 14931863 := bstep (se 1 (by rfl) ⟨11198897, by rfl⟩ : syracuseStep 14931863 = 22397795) B22397795
theorem B4593725 : Blo 1360499 4593725 := bstep (se 3 (by rfl) ⟨861323, by rfl⟩ : syracuseStep 4593725 = 1722647) B1722647
theorem B10344509 : Blo 1360499 10344509 := bstep (se 3 (by rfl) ⟨1939595, by rfl⟩ : syracuseStep 10344509 = 3879191) B3879191
theorem B3061907 : Blo 1360499 3061907 := bstep (se 1 (by rfl) ⟨2296430, by rfl⟩ : syracuseStep 3061907 = 4592861) B4592861
theorem B1841339 : Blo 1360499 1841339 := bstep (se 1 (by rfl) ⟨1381004, by rfl⟩ : syracuseStep 1841339 = 2762009) B2762009
theorem B3061961 : Blo 1360499 3061961 := bstep (se 2 (by rfl) ⟨1148235, by rfl⟩ : syracuseStep 3061961 = 2296471) B2296471
theorem B9943241 : Blo 1360499 9943241 := bstep (se 2 (by rfl) ⟨3728715, by rfl⟩ : syracuseStep 9943241 = 7457431) B7457431
theorem B7756013 : Blo 1360499 7756013 := bstep (se 3 (by rfl) ⟨1454252, by rfl⟩ : syracuseStep 7756013 = 2908505) B2908505
theorem B6895853 : Blo 1360499 6895853 := bstep (se 3 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 6895853 = 2585945) B2585945
theorem B1939727 : Blo 1360499 1939727 := bstep (se 1 (by rfl) ⟨1454795, by rfl⟩ : syracuseStep 1939727 = 2909591) B2909591
theorem B5519801 : Blo 1360499 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B2947513 : Blo 1360499 2947513 := bstep (se 2 (by rfl) ⟨1105317, by rfl⟩ : syracuseStep 2947513 = 2210635) B2210635
theorem B10336733 : Blo 1360499 10336733 := bstep (se 3 (by rfl) ⟨1938137, by rfl⟩ : syracuseStep 10336733 = 3876275) B3876275
theorem B22076023 : Blo 1360499 22076023 := bstep (se 1 (by rfl) ⟨16557017, by rfl⟩ : syracuseStep 22076023 = 33114035) B33114035
theorem B3447431 : Blo 1360499 3447431 := bstep (se 1 (by rfl) ⟨2585573, by rfl⟩ : syracuseStep 3447431 = 5171147) B5171147
theorem B3447481 : Blo 1360499 3447481 := bstep (se 2 (by rfl) ⟨1292805, by rfl⟩ : syracuseStep 3447481 = 2585611) B2585611
theorem B5241581 : Blo 1360499 5241581 := bstep (se 3 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 5241581 = 1965593) B1965593
theorem B3062663 : Blo 1360499 3062663 := bstep (se 1 (by rfl) ⟨2296997, by rfl⟩ : syracuseStep 3062663 = 4593995) B4593995
theorem B3316633 : Blo 1360499 3316633 := bstep (se 2 (by rfl) ⟨1243737, by rfl⟩ : syracuseStep 3316633 = 2487475) B2487475
theorem B6888401 : Blo 1360499 6888401 := bstep (se 2 (by rfl) ⟨2583150, by rfl⟩ : syracuseStep 6888401 = 5166301) B5166301
theorem B14711813 : Blo 1360499 14711813 := bstep (se 4 (by rfl) ⟨1379232, by rfl⟩ : syracuseStep 14711813 = 2758465) B2758465
theorem B1530895 : Blo 1360499 1530895 := bstep (se 1 (by rfl) ⟨1148171, by rfl⟩ : syracuseStep 1530895 = 2296343) B2296343
theorem B6896663 : Blo 1360499 6896663 := bstep (se 1 (by rfl) ⟨5172497, by rfl⟩ : syracuseStep 6896663 = 10344995) B10344995
theorem B3062843 : Blo 1360499 3062843 := bstep (se 1 (by rfl) ⟨2297132, by rfl⟩ : syracuseStep 3062843 = 4594265) B4594265
theorem B3062969 : Blo 1360499 3062969 := bstep (se 2 (by rfl) ⟨1148613, by rfl⟩ : syracuseStep 3062969 = 2297227) B2297227
theorem B3448079 : Blo 1360499 3448079 := bstep (se 1 (by rfl) ⟨2586059, by rfl⟩ : syracuseStep 3448079 = 5172119) B5172119
theorem B5168519 : Blo 1360499 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B4595129 : Blo 1360499 4595129 := bstep (se 2 (by rfl) ⟨1723173, by rfl⟩ : syracuseStep 4595129 = 3446347) B3446347
theorem B1531399 : Blo 1360499 1531399 := bstep (se 1 (by rfl) ⟨1148549, by rfl⟩ : syracuseStep 1531399 = 2297099) B2297099
theorem B6544907 : Blo 1360499 6544907 := bstep (se 1 (by rfl) ⟨4908680, by rfl⟩ : syracuseStep 6544907 = 9817361) B9817361
theorem B3063311 : Blo 1360499 3063311 := bstep (se 1 (by rfl) ⟨2297483, by rfl⟩ : syracuseStep 3063311 = 4594967) B4594967
theorem B3063329 : Blo 1360499 3063329 := bstep (se 2 (by rfl) ⟨1148748, by rfl⟩ : syracuseStep 3063329 = 2297497) B2297497
theorem B1531579 : Blo 1360499 1531579 := bstep (se 1 (by rfl) ⟨1148684, by rfl⟩ : syracuseStep 1531579 = 2297369) B2297369
theorem B5816123 : Blo 1360499 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B3063671 : Blo 1360499 3063671 := bstep (se 1 (by rfl) ⟨2297753, by rfl⟩ : syracuseStep 3063671 = 4595507) B4595507
theorem B3448777 : Blo 1360499 3448777 := bstep (se 2 (by rfl) ⟨1293291, by rfl⟩ : syracuseStep 3448777 = 2586583) B2586583
theorem B7864285 : Blo 1360499 7864285 := bstep (se 3 (by rfl) ⟨1474553, by rfl⟩ : syracuseStep 7864285 = 2949107) B2949107
theorem B3063815 : Blo 1360499 3063815 := bstep (se 1 (by rfl) ⟨2297861, by rfl⟩ : syracuseStep 3063815 = 4595723) B4595723
theorem B26173469 : Blo 1360499 26173469 := bstep (se 3 (by rfl) ⟨4907525, by rfl⟩ : syracuseStep 26173469 = 9815051) B9815051
theorem B44130365 : Blo 1360499 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B3063887 : Blo 1360499 3063887 := bstep (se 1 (by rfl) ⟨2297915, by rfl⟩ : syracuseStep 3063887 = 4595831) B4595831
theorem B132505955 : Blo 1360499 132505955 := bstep (se 1 (by rfl) ⟨99379466, by rfl⟩ : syracuseStep 132505955 = 198758933) B198758933
theorem B3268993 : Blo 1360499 3268993 := bstep (se 2 (by rfl) ⟨1225872, by rfl⟩ : syracuseStep 3268993 = 2451745) B2451745
theorem B6209921 : Blo 1360499 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B1532335 : Blo 1360499 1532335 := bstep (se 1 (by rfl) ⟨1149251, by rfl⟩ : syracuseStep 1532335 = 2298503) B2298503
theorem B3064283 : Blo 1360499 3064283 := bstep (se 1 (by rfl) ⟨2298212, by rfl⟩ : syracuseStep 3064283 = 4596425) B4596425
theorem B5169689 : Blo 1360499 5169689 := bstep (se 2 (by rfl) ⟨1938633, by rfl⟩ : syracuseStep 5169689 = 3877267) B3877267
theorem B5169703 : Blo 1360499 5169703 := bstep (se 1 (by rfl) ⟨3877277, by rfl⟩ : syracuseStep 5169703 = 7754555) B7754555
theorem B4596263 : Blo 1360499 4596263 := bstep (se 1 (by rfl) ⟨3447197, by rfl⟩ : syracuseStep 4596263 = 6894395) B6894395
theorem B1360507 : Blo 1360499 1360507 := bstep (se 1 (by rfl) ⟨1020380, by rfl⟩ : syracuseStep 1360507 = 2040761) B2040761
theorem B4596371 : Blo 1360499 4596371 := bstep (se 1 (by rfl) ⟨3447278, by rfl⟩ : syracuseStep 4596371 = 6894557) B6894557
theorem B1360559 : Blo 1360499 1360559 := bstep (se 1 (by rfl) ⟨1020419, by rfl⟩ : syracuseStep 1360559 = 2040839) B2040839
theorem B1360583 : Blo 1360499 1360583 := bstep (se 1 (by rfl) ⟨1020437, by rfl⟩ : syracuseStep 1360583 = 2040875) B2040875
theorem B1360603 : Blo 1360499 1360603 := bstep (se 1 (by rfl) ⟨1020452, by rfl⟩ : syracuseStep 1360603 = 2040905) B2040905
theorem B1360679 : Blo 1360499 1360679 := bstep (se 1 (by rfl) ⟨1020509, by rfl⟩ : syracuseStep 1360679 = 2041019) B2041019
theorem B29434697 : Blo 1360499 29434697 := bstep (se 2 (by rfl) ⟨11038011, by rfl⟩ : syracuseStep 29434697 = 22076023) B22076023
theorem B1360719 : Blo 1360499 1360719 := bstep (se 1 (by rfl) ⟨1020539, by rfl⟩ : syracuseStep 1360719 = 2041079) B2041079
theorem B1360735 : Blo 1360499 1360735 := bstep (se 1 (by rfl) ⟨1020551, by rfl⟩ : syracuseStep 1360735 = 2041103) B2041103
theorem B1532767 : Blo 1360499 1532767 := bstep (se 1 (by rfl) ⟨1149575, by rfl⟩ : syracuseStep 1532767 = 2299151) B2299151
theorem B4596587 : Blo 1360499 4596587 := bstep (se 1 (by rfl) ⟨3447440, by rfl⟩ : syracuseStep 4596587 = 6894881) B6894881
theorem B1360763 : Blo 1360499 1360763 := bstep (se 1 (by rfl) ⟨1020572, by rfl⟩ : syracuseStep 1360763 = 2041145) B2041145
theorem B4596641 : Blo 1360499 4596641 := bstep (se 2 (by rfl) ⟨1723740, by rfl⟩ : syracuseStep 4596641 = 3447481) B3447481
theorem B1360815 : Blo 1360499 1360815 := bstep (se 1 (by rfl) ⟨1020611, by rfl⟩ : syracuseStep 1360815 = 2041223) B2041223
theorem B3064751 : Blo 1360499 3064751 := bstep (se 1 (by rfl) ⟨2298563, by rfl⟩ : syracuseStep 3064751 = 4597127) B4597127
theorem B1360839 : Blo 1360499 1360839 := bstep (se 1 (by rfl) ⟨1020629, by rfl⟩ : syracuseStep 1360839 = 2041259) B2041259
theorem B1360859 : Blo 1360499 1360859 := bstep (se 1 (by rfl) ⟨1020644, by rfl⟩ : syracuseStep 1360859 = 2041289) B2041289
theorem B1360935 : Blo 1360499 1360935 := bstep (se 1 (by rfl) ⟨1020701, by rfl⟩ : syracuseStep 1360935 = 2041403) B2041403
theorem B2040911 : Blo 1360499 2040911 := bstep (se 1 (by rfl) ⟨1530683, by rfl⟩ : syracuseStep 2040911 = 3061367) B3061367
theorem B1360975 : Blo 1360499 1360975 := bstep (se 1 (by rfl) ⟨1020731, by rfl⟩ : syracuseStep 1360975 = 2041463) B2041463
theorem B1360991 : Blo 1360499 1360991 := bstep (se 1 (by rfl) ⟨1020743, by rfl⟩ : syracuseStep 1360991 = 2041487) B2041487
theorem B1361019 : Blo 1360499 1361019 := bstep (se 1 (by rfl) ⟨1020764, by rfl⟩ : syracuseStep 1361019 = 2041529) B2041529
theorem B3065003 : Blo 1360499 3065003 := bstep (se 1 (by rfl) ⟨2298752, by rfl⟩ : syracuseStep 3065003 = 4597505) B4597505
theorem B1361071 : Blo 1360499 1361071 := bstep (se 1 (by rfl) ⟨1020803, by rfl⟩ : syracuseStep 1361071 = 2041607) B2041607
theorem B2041031 : Blo 1360499 2041031 := bstep (se 1 (by rfl) ⟨1530773, by rfl⟩ : syracuseStep 2041031 = 3061547) B3061547
theorem B1361095 : Blo 1360499 1361095 := bstep (se 1 (by rfl) ⟨1020821, by rfl⟩ : syracuseStep 1361095 = 2041643) B2041643
theorem B1361115 : Blo 1360499 1361115 := bstep (se 1 (by rfl) ⟨1020836, by rfl⟩ : syracuseStep 1361115 = 2041673) B2041673
theorem B9954575 : Blo 1360499 9954575 := bstep (se 1 (by rfl) ⟨7465931, by rfl⟩ : syracuseStep 9954575 = 14931863) B14931863
theorem B8275223 : Blo 1360499 8275223 := bstep (se 1 (by rfl) ⟨6206417, by rfl⟩ : syracuseStep 8275223 = 12412835) B12412835
theorem B1361191 : Blo 1360499 1361191 := bstep (se 1 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 1361191 = 2041787) B2041787
theorem B5170493 : Blo 1360499 5170493 := bstep (se 3 (by rfl) ⟨969467, by rfl⟩ : syracuseStep 5170493 = 1938935) B1938935
theorem B1361231 : Blo 1360499 1361231 := bstep (se 1 (by rfl) ⟨1020923, by rfl⟩ : syracuseStep 1361231 = 2041847) B2041847
theorem B1361247 : Blo 1360499 1361247 := bstep (se 1 (by rfl) ⟨1020935, by rfl⟩ : syracuseStep 1361247 = 2041871) B2041871
theorem B2041193 : Blo 1360499 2041193 := bstep (se 2 (by rfl) ⟨765447, by rfl⟩ : syracuseStep 2041193 = 1530895) B1530895
theorem B16549235 : Blo 1360499 16549235 := bstep (se 1 (by rfl) ⟨12411926, by rfl⟩ : syracuseStep 16549235 = 24823853) B24823853
theorem B1361275 : Blo 1360499 1361275 := bstep (se 1 (by rfl) ⟨1020956, by rfl⟩ : syracuseStep 1361275 = 2041913) B2041913
theorem B1361327 : Blo 1360499 1361327 := bstep (se 1 (by rfl) ⟨1020995, by rfl⟩ : syracuseStep 1361327 = 2041991) B2041991
theorem B2041271 : Blo 1360499 2041271 := bstep (se 1 (by rfl) ⟨1530953, by rfl⟩ : syracuseStep 2041271 = 3061907) B3061907
theorem B1361351 : Blo 1360499 1361351 := bstep (se 1 (by rfl) ⟨1021013, by rfl⟩ : syracuseStep 1361351 = 2042027) B2042027
theorem B2041307 : Blo 1360499 2041307 := bstep (se 1 (by rfl) ⟨1530980, by rfl⟩ : syracuseStep 2041307 = 3061961) B3061961
theorem B1361371 : Blo 1360499 1361371 := bstep (se 1 (by rfl) ⟨1021028, by rfl⟩ : syracuseStep 1361371 = 2042057) B2042057
theorem B5170675 : Blo 1360499 5170675 := bstep (se 1 (by rfl) ⟨3878006, by rfl⟩ : syracuseStep 5170675 = 7756013) B7756013
theorem B4597235 : Blo 1360499 4597235 := bstep (se 1 (by rfl) ⟨3447926, by rfl⟩ : syracuseStep 4597235 = 6895853) B6895853
theorem B1361447 : Blo 1360499 1361447 := bstep (se 1 (by rfl) ⟨1021085, by rfl⟩ : syracuseStep 1361447 = 2042171) B2042171
theorem B2180687 : Blo 1360499 2180687 := bstep (se 1 (by rfl) ⟨1635515, by rfl⟩ : syracuseStep 2180687 = 3271031) B3271031
theorem B1361487 : Blo 1360499 1361487 := bstep (se 1 (by rfl) ⟨1021115, by rfl⟩ : syracuseStep 1361487 = 2042231) B2042231
theorem B1361503 : Blo 1360499 1361503 := bstep (se 1 (by rfl) ⟨1021127, by rfl⟩ : syracuseStep 1361503 = 2042255) B2042255
theorem B3679867 : Blo 1360499 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B1361531 : Blo 1360499 1361531 := bstep (se 1 (by rfl) ⟨1021148, by rfl⟩ : syracuseStep 1361531 = 2042297) B2042297
theorem B6891155 : Blo 1360499 6891155 := bstep (se 1 (by rfl) ⟨5168366, by rfl⟩ : syracuseStep 6891155 = 10336733) B10336733
theorem B1361583 : Blo 1360499 1361583 := bstep (se 1 (by rfl) ⟨1021187, by rfl⟩ : syracuseStep 1361583 = 2042375) B2042375
theorem B1722055 : Blo 1360499 1722055 := bstep (se 1 (by rfl) ⟨1291541, by rfl⟩ : syracuseStep 1722055 = 2583083) B2583083
theorem B1361607 : Blo 1360499 1361607 := bstep (se 1 (by rfl) ⟨1021205, by rfl⟩ : syracuseStep 1361607 = 2042411) B2042411
theorem B3065543 : Blo 1360499 3065543 := bstep (se 1 (by rfl) ⟨2299157, by rfl⟩ : syracuseStep 3065543 = 4598315) B4598315
theorem B1361627 : Blo 1360499 1361627 := bstep (se 1 (by rfl) ⟨1021220, by rfl⟩ : syracuseStep 1361627 = 2042441) B2042441
theorem B11339513 : Blo 1360499 11339513 := bstep (se 2 (by rfl) ⟨4252317, by rfl⟩ : syracuseStep 11339513 = 8504635) B8504635
theorem B1361703 : Blo 1360499 1361703 := bstep (se 1 (by rfl) ⟨1021277, by rfl⟩ : syracuseStep 1361703 = 2042555) B2042555
theorem B17680187 : Blo 1360499 17680187 := bstep (se 1 (by rfl) ⟨13260140, by rfl⟩ : syracuseStep 17680187 = 26520281) B26520281
theorem B1361743 : Blo 1360499 1361743 := bstep (se 1 (by rfl) ⟨1021307, by rfl⟩ : syracuseStep 1361743 = 2042615) B2042615
theorem B1361759 : Blo 1360499 1361759 := bstep (se 1 (by rfl) ⟨1021319, by rfl⟩ : syracuseStep 1361759 = 2042639) B2042639
theorem B1361787 : Blo 1360499 1361787 := bstep (se 1 (by rfl) ⟨1021340, by rfl⟩ : syracuseStep 1361787 = 2042681) B2042681
theorem B49661849 : Blo 1360499 49661849 := bstep (se 2 (by rfl) ⟨18623193, by rfl⟩ : syracuseStep 49661849 = 37246387) B37246387
theorem B2041775 : Blo 1360499 2041775 := bstep (se 1 (by rfl) ⟨1531331, by rfl⟩ : syracuseStep 2041775 = 3062663) B3062663
theorem B1361839 : Blo 1360499 1361839 := bstep (se 1 (by rfl) ⟨1021379, by rfl⟩ : syracuseStep 1361839 = 2042759) B2042759
theorem B1361863 : Blo 1360499 1361863 := bstep (se 1 (by rfl) ⟨1021397, by rfl⟩ : syracuseStep 1361863 = 2042795) B2042795
theorem B1361883 : Blo 1360499 1361883 := bstep (se 1 (by rfl) ⟨1021412, by rfl⟩ : syracuseStep 1361883 = 2042825) B2042825
theorem B9807875 : Blo 1360499 9807875 := bstep (se 1 (by rfl) ⟨7355906, by rfl⟩ : syracuseStep 9807875 = 14711813) B14711813
theorem B2041865 : Blo 1360499 2041865 := bstep (se 2 (by rfl) ⟨765699, by rfl⟩ : syracuseStep 2041865 = 1531399) B1531399
theorem B4597775 : Blo 1360499 4597775 := bstep (se 1 (by rfl) ⟨3448331, by rfl⟩ : syracuseStep 4597775 = 6896663) B6896663
theorem B2041895 : Blo 1360499 2041895 := bstep (se 1 (by rfl) ⟨1531421, by rfl⟩ : syracuseStep 2041895 = 3062843) B3062843
theorem B1361959 : Blo 1360499 1361959 := bstep (se 1 (by rfl) ⟨1021469, by rfl⟩ : syracuseStep 1361959 = 2042939) B2042939
theorem B7358521 : Blo 1360499 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B1361999 : Blo 1360499 1361999 := bstep (se 1 (by rfl) ⟨1021499, by rfl⟩ : syracuseStep 1361999 = 2042999) B2042999
theorem B1362015 : Blo 1360499 1362015 := bstep (se 1 (by rfl) ⟨1021511, by rfl⟩ : syracuseStep 1362015 = 2043023) B2043023
theorem B2295931 : Blo 1360499 2295931 := bstep (se 1 (by rfl) ⟨1721948, by rfl⟩ : syracuseStep 2295931 = 3443897) B3443897
theorem B2041979 : Blo 1360499 2041979 := bstep (se 1 (by rfl) ⟨1531484, by rfl⟩ : syracuseStep 2041979 = 3062969) B3062969
theorem B1362043 : Blo 1360499 1362043 := bstep (se 1 (by rfl) ⟨1021532, by rfl⟩ : syracuseStep 1362043 = 2043065) B2043065
theorem B17688709 : Blo 1360499 17688709 := bstep (se 4 (by rfl) ⟨1658316, by rfl⟩ : syracuseStep 17688709 = 3316633) B3316633
theorem B1362095 : Blo 1360499 1362095 := bstep (se 1 (by rfl) ⟨1021571, by rfl⟩ : syracuseStep 1362095 = 2043143) B2043143
theorem B1362119 : Blo 1360499 1362119 := bstep (se 1 (by rfl) ⟨1021589, by rfl⟩ : syracuseStep 1362119 = 2043179) B2043179
theorem B1362139 : Blo 1360499 1362139 := bstep (se 1 (by rfl) ⟨1021604, by rfl⟩ : syracuseStep 1362139 = 2043209) B2043209
theorem B2042105 : Blo 1360499 2042105 := bstep (se 2 (by rfl) ⟨765789, by rfl⟩ : syracuseStep 2042105 = 1531579) B1531579
theorem B1362215 : Blo 1360499 1362215 := bstep (se 1 (by rfl) ⟨1021661, by rfl⟩ : syracuseStep 1362215 = 2043323) B2043323
theorem B1362255 : Blo 1360499 1362255 := bstep (se 1 (by rfl) ⟨1021691, by rfl⟩ : syracuseStep 1362255 = 2043383) B2043383
theorem B2042207 : Blo 1360499 2042207 := bstep (se 1 (by rfl) ⟨1531655, by rfl⟩ : syracuseStep 2042207 = 3063311) B3063311
theorem B1362271 : Blo 1360499 1362271 := bstep (se 1 (by rfl) ⟨1021703, by rfl⟩ : syracuseStep 1362271 = 2043407) B2043407
theorem B2042219 : Blo 1360499 2042219 := bstep (se 1 (by rfl) ⟨1531664, by rfl⟩ : syracuseStep 2042219 = 3063329) B3063329
theorem B1362299 : Blo 1360499 1362299 := bstep (se 1 (by rfl) ⟨1021724, by rfl⟩ : syracuseStep 1362299 = 2043449) B2043449
theorem B1722799 : Blo 1360499 1722799 := bstep (se 1 (by rfl) ⟨1292099, by rfl⟩ : syracuseStep 1722799 = 2584199) B2584199
theorem B1362351 : Blo 1360499 1362351 := bstep (se 1 (by rfl) ⟨1021763, by rfl⟩ : syracuseStep 1362351 = 2043527) B2043527
theorem B1362375 : Blo 1360499 1362375 := bstep (se 1 (by rfl) ⟨1021781, by rfl⟩ : syracuseStep 1362375 = 2043563) B2043563
theorem B1362395 : Blo 1360499 1362395 := bstep (se 1 (by rfl) ⟨1021796, by rfl⟩ : syracuseStep 1362395 = 2043593) B2043593
theorem B3877415 : Blo 1360499 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B1362471 : Blo 1360499 1362471 := bstep (se 1 (by rfl) ⟨1021853, by rfl⟩ : syracuseStep 1362471 = 2043707) B2043707
theorem B2042447 : Blo 1360499 2042447 := bstep (se 1 (by rfl) ⟨1531835, by rfl⟩ : syracuseStep 2042447 = 3063671) B3063671
theorem B4598369 : Blo 1360499 4598369 := bstep (se 2 (by rfl) ⟨1724388, by rfl⟩ : syracuseStep 4598369 = 3448777) B3448777
theorem B10332845 : Blo 1360499 10332845 := bstep (se 3 (by rfl) ⟨1937408, by rfl⟩ : syracuseStep 10332845 = 3874817) B3874817
theorem B2042567 : Blo 1360499 2042567 := bstep (se 1 (by rfl) ⟨1531925, by rfl⟩ : syracuseStep 2042567 = 3063851) B3063851
theorem B5171921 : Blo 1360499 5171921 := bstep (se 2 (by rfl) ⟨1939470, by rfl⟩ : syracuseStep 5171921 = 3878941) B3878941
theorem B2329337 : Blo 1360499 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B2042729 : Blo 1360499 2042729 := bstep (se 2 (by rfl) ⟨766023, by rfl⟩ : syracuseStep 2042729 = 1532047) B1532047
theorem B2042807 : Blo 1360499 2042807 := bstep (se 1 (by rfl) ⟨1532105, by rfl⟩ : syracuseStep 2042807 = 3064211) B3064211
theorem B2583515 : Blo 1360499 2583515 := bstep (se 1 (by rfl) ⟨1937636, by rfl⟩ : syracuseStep 2583515 = 3875273) B3875273
theorem B2296795 : Blo 1360499 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B2042843 : Blo 1360499 2042843 := bstep (se 1 (by rfl) ⟨1532132, by rfl⟩ : syracuseStep 2042843 = 3064265) B3064265
theorem B4361273 : Blo 1360499 4361273 := bstep (se 2 (by rfl) ⟨1635477, by rfl⟩ : syracuseStep 4361273 = 3270955) B3270955
theorem B5819471 : Blo 1360499 5819471 := bstep (se 1 (by rfl) ⟨4364603, by rfl⟩ : syracuseStep 5819471 = 8729207) B8729207
theorem B4910237 : Blo 1360499 4910237 := bstep (se 3 (by rfl) ⟨920669, by rfl⟩ : syracuseStep 4910237 = 1841339) B1841339
theorem B2182315 : Blo 1360499 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B2583751 : Blo 1360499 2583751 := bstep (se 1 (by rfl) ⟨1937813, by rfl⟩ : syracuseStep 2583751 = 3875627) B3875627
theorem B5172605 : Blo 1360499 5172605 := bstep (se 3 (by rfl) ⟨969863, by rfl⟩ : syracuseStep 5172605 = 1939727) B1939727
theorem B4418959 : Blo 1360499 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B2043311 : Blo 1360499 2043311 := bstep (se 1 (by rfl) ⟨1532483, by rfl⟩ : syracuseStep 2043311 = 3064967) B3064967
theorem B2485723 : Blo 1360499 2485723 := bstep (se 1 (by rfl) ⟨1864292, by rfl⟩ : syracuseStep 2485723 = 3728585) B3728585
theorem B18419165 : Blo 1360499 18419165 := bstep (se 3 (by rfl) ⟨3453593, by rfl⟩ : syracuseStep 18419165 = 6907187) B6907187
theorem B2043401 : Blo 1360499 2043401 := bstep (se 2 (by rfl) ⟨766275, by rfl⟩ : syracuseStep 2043401 = 1532551) B1532551
theorem B1723943 : Blo 1360499 1723943 := bstep (se 1 (by rfl) ⟨1292957, by rfl⟩ : syracuseStep 1723943 = 2585915) B2585915
theorem B2043431 : Blo 1360499 2043431 := bstep (se 1 (by rfl) ⟨1532573, by rfl⟩ : syracuseStep 2043431 = 3065147) B3065147
theorem B2297423 : Blo 1360499 2297423 := bstep (se 1 (by rfl) ⟨1723067, by rfl⟩ : syracuseStep 2297423 = 3446135) B3446135
theorem B2043515 : Blo 1360499 2043515 := bstep (se 1 (by rfl) ⟨1532636, by rfl⟩ : syracuseStep 2043515 = 3065273) B3065273
theorem B5811851 : Blo 1360499 5811851 := bstep (se 1 (by rfl) ⟨4358888, by rfl⟩ : syracuseStep 5811851 = 8717777) B8717777
theorem B3878599 : Blo 1360499 3878599 := bstep (se 1 (by rfl) ⟨2908949, by rfl⟩ : syracuseStep 3878599 = 5817899) B5817899
theorem B2043641 : Blo 1360499 2043641 := bstep (se 2 (by rfl) ⟨766365, by rfl⟩ : syracuseStep 2043641 = 1532731) B1532731
theorem B2043743 : Blo 1360499 2043743 := bstep (se 1 (by rfl) ⟨1532807, by rfl⟩ : syracuseStep 2043743 = 3065615) B3065615
theorem B1724267 : Blo 1360499 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B6983533 : Blo 1360499 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B8720237 : Blo 1360499 8720237 := bstep (se 3 (by rfl) ⟨1635044, by rfl⟩ : syracuseStep 8720237 = 3270089) B3270089
theorem B10227575 : Blo 1360499 10227575 := bstep (se 1 (by rfl) ⟨7670681, by rfl⟩ : syracuseStep 10227575 = 15341363) B15341363
theorem B17444879 : Blo 1360499 17444879 := bstep (se 1 (by rfl) ⟨13083659, by rfl⟩ : syracuseStep 17444879 = 26167319) B26167319
theorem B9310265 : Blo 1360499 9310265 := bstep (se 2 (by rfl) ⟨3491349, by rfl⟩ : syracuseStep 9310265 = 6982699) B6982699
theorem B1454159 : Blo 1360499 1454159 := bstep (se 1 (by rfl) ⟨1090619, by rfl⟩ : syracuseStep 1454159 = 2181239) B2181239
theorem B44183825 : Blo 1360499 44183825 := bstep (se 2 (by rfl) ⟨16568934, by rfl⟩ : syracuseStep 44183825 = 33137869) B33137869
theorem B4591997 : Blo 1360499 4591997 := bstep (se 3 (by rfl) ⟨860999, by rfl⟩ : syracuseStep 4591997 = 1721999) B1721999
theorem B2298287 : Blo 1360499 2298287 := bstep (se 1 (by rfl) ⟨1723715, by rfl⟩ : syracuseStep 2298287 = 3447431) B3447431
theorem B3494387 : Blo 1360499 3494387 := bstep (se 1 (by rfl) ⟨2620790, by rfl⟩ : syracuseStep 3494387 = 5241581) B5241581
theorem B17437193 : Blo 1360499 17437193 := bstep (se 2 (by rfl) ⟨6538947, by rfl⟩ : syracuseStep 17437193 = 13077895) B13077895
theorem B4362785 : Blo 1360499 4362785 := bstep (se 2 (by rfl) ⟨1636044, by rfl⟩ : syracuseStep 4362785 = 3272089) B3272089
theorem B2486863 : Blo 1360499 2486863 := bstep (se 1 (by rfl) ⟨1865147, by rfl⟩ : syracuseStep 2486863 = 3730295) B3730295
theorem B4592267 : Blo 1360499 4592267 := bstep (se 1 (by rfl) ⟨3444200, by rfl⟩ : syracuseStep 4592267 = 6888401) B6888401
theorem B89568017 : Blo 1360499 89568017 := bstep (se 2 (by rfl) ⟨33588006, by rfl⟩ : syracuseStep 89568017 = 67176013) B67176013
theorem B2298719 : Blo 1360499 2298719 := bstep (se 1 (by rfl) ⟨1724039, by rfl⟩ : syracuseStep 2298719 = 3448079) B3448079
theorem B5813167 : Blo 1360499 5813167 := bstep (se 1 (by rfl) ⟨4359875, by rfl⟩ : syracuseStep 5813167 = 8719751) B8719751
theorem B3445679 : Blo 1360499 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B2454455 : Blo 1360499 2454455 := bstep (se 1 (by rfl) ⟨1840841, by rfl⟩ : syracuseStep 2454455 = 3681683) B3681683
theorem B4363271 : Blo 1360499 4363271 := bstep (se 1 (by rfl) ⟨3272453, by rfl⟩ : syracuseStep 4363271 = 6544907) B6544907
theorem B10335275 : Blo 1360499 10335275 := bstep (se 1 (by rfl) ⟨7751456, by rfl⟩ : syracuseStep 10335275 = 15502913) B15502913
theorem B2585657 : Blo 1360499 2585657 := bstep (se 2 (by rfl) ⟨969621, by rfl⟩ : syracuseStep 2585657 = 1939243) B1939243
theorem B5518489 : Blo 1360499 5518489 := bstep (se 2 (by rfl) ⟨2069433, by rfl⟩ : syracuseStep 5518489 = 4138867) B4138867
theorem B4904297 : Blo 1360499 4904297 := bstep (se 2 (by rfl) ⟨1839111, by rfl⟩ : syracuseStep 4904297 = 3678223) B3678223
theorem B2585999 : Blo 1360499 2585999 := bstep (se 1 (by rfl) ⟨1939499, by rfl⟩ : syracuseStep 2585999 = 3878999) B3878999
theorem B15725987 : Blo 1360499 15725987 := bstep (se 1 (by rfl) ⟨11794490, by rfl⟩ : syracuseStep 15725987 = 23588981) B23588981
theorem B1938907 : Blo 1360499 1938907 := bstep (se 1 (by rfl) ⟨1454180, by rfl⟩ : syracuseStep 1938907 = 2908361) B2908361
theorem B3446297 : Blo 1360499 3446297 := bstep (se 2 (by rfl) ⟨1292361, by rfl⟩ : syracuseStep 3446297 = 2584723) B2584723
theorem B4593185 : Blo 1360499 4593185 := bstep (se 2 (by rfl) ⟨1722444, by rfl⟩ : syracuseStep 4593185 = 3444889) B3444889
theorem B10344023 : Blo 1360499 10344023 := bstep (se 1 (by rfl) ⟨7758017, by rfl⟩ : syracuseStep 10344023 = 15516035) B15516035
theorem B5043923 : Blo 1360499 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B4593401 : Blo 1360499 4593401 := bstep (se 2 (by rfl) ⟨1722525, by rfl⟩ : syracuseStep 4593401 = 3445051) B3445051
theorem B8722235 : Blo 1360499 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B26515309 : Blo 1360499 26515309 := bstep (se 3 (by rfl) ⟨4971620, by rfl⟩ : syracuseStep 26515309 = 9943241) B9943241
theorem B5814125 : Blo 1360499 5814125 := bstep (se 3 (by rfl) ⟨1090148, by rfl⟩ : syracuseStep 5814125 = 2180297) B2180297
theorem B3930017 : Blo 1360499 3930017 := bstep (se 2 (by rfl) ⟨1473756, by rfl⟩ : syracuseStep 3930017 = 2947513) B2947513
theorem B3061691 : Blo 1360499 3061691 := bstep (se 1 (by rfl) ⟨2296268, by rfl⟩ : syracuseStep 3061691 = 4592537) B4592537
theorem B4364219 : Blo 1360499 4364219 := bstep (se 1 (by rfl) ⟨3273164, by rfl⟩ : syracuseStep 4364219 = 6546329) B6546329
theorem B4593671 : Blo 1360499 4593671 := bstep (se 1 (by rfl) ⟨3445253, by rfl⟩ : syracuseStep 4593671 = 6890507) B6890507
theorem B2906131 : Blo 1360499 2906131 := bstep (se 1 (by rfl) ⟨2179598, by rfl⟩ : syracuseStep 2906131 = 4359197) B4359197
theorem B3061817 : Blo 1360499 3061817 := bstep (se 2 (by rfl) ⟨1148181, by rfl⟩ : syracuseStep 3061817 = 2296363) B2296363
theorem B1841231 : Blo 1360499 1841231 := bstep (se 1 (by rfl) ⟨1380923, by rfl⟩ : syracuseStep 1841231 = 2761847) B2761847
theorem B4593779 : Blo 1360499 4593779 := bstep (se 1 (by rfl) ⟨3445334, by rfl⟩ : syracuseStep 4593779 = 6890669) B6890669
theorem B9812285 : Blo 1360499 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B4594049 : Blo 1360499 4594049 := bstep (se 2 (by rfl) ⟨1722768, by rfl⟩ : syracuseStep 4594049 = 3445537) B3445537
theorem B3062159 : Blo 1360499 3062159 := bstep (se 1 (by rfl) ⟨2296619, by rfl⟩ : syracuseStep 3062159 = 4593239) B4593239
theorem B11033111 : Blo 1360499 11033111 := bstep (se 1 (by rfl) ⟨8274833, by rfl⟩ : syracuseStep 11033111 = 16549667) B16549667
theorem B5593799 : Blo 1360499 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B3062483 : Blo 1360499 3062483 := bstep (se 1 (by rfl) ⟨2296862, by rfl⟩ : syracuseStep 3062483 = 4593725) B4593725
theorem B6896339 : Blo 1360499 6896339 := bstep (se 1 (by rfl) ⟨5172254, by rfl⟩ : syracuseStep 6896339 = 10344509) B10344509
theorem B5168033 : Blo 1360499 5168033 := bstep (se 2 (by rfl) ⟨1938012, by rfl⟩ : syracuseStep 5168033 = 3876025) B3876025
theorem B1531003 : Blo 1360499 1531003 := bstep (se 1 (by rfl) ⟨1148252, by rfl⟩ : syracuseStep 1531003 = 2296505) B2296505
theorem B4594859 : Blo 1360499 4594859 := bstep (se 1 (by rfl) ⟨3446144, by rfl⟩ : syracuseStep 4594859 = 6892289) B6892289
theorem B13090085 : Blo 1360499 13090085 := bstep (se 4 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 13090085 = 2454391) B2454391
theorem B11623769 : Blo 1360499 11623769 := bstep (se 2 (by rfl) ⟨4358913, by rfl⟩ : syracuseStep 11623769 = 8717827) B8717827
theorem B5520905 : Blo 1360499 5520905 := bstep (se 2 (by rfl) ⟨2070339, by rfl⟩ : syracuseStep 5520905 = 4140679) B4140679
theorem B1531471 : Blo 1360499 1531471 := bstep (se 1 (by rfl) ⟨1148603, by rfl⟩ : syracuseStep 1531471 = 2297207) B2297207
theorem B3063419 : Blo 1360499 3063419 := bstep (se 1 (by rfl) ⟨2297564, by rfl⟩ : syracuseStep 3063419 = 4595129) B4595129
theorem B4595399 : Blo 1360499 4595399 := bstep (se 1 (by rfl) ⟨3446549, by rfl⟩ : syracuseStep 4595399 = 6893099) B6893099
theorem B3063545 : Blo 1360499 3063545 := bstep (se 2 (by rfl) ⟨1148829, by rfl⟩ : syracuseStep 3063545 = 2297659) B2297659
theorem B5169005 : Blo 1360499 5169005 := bstep (se 3 (by rfl) ⟨969188, by rfl⟩ : syracuseStep 5169005 = 1938377) B1938377
theorem B5816225 : Blo 1360499 5816225 := bstep (se 2 (by rfl) ⟨2181084, by rfl⟩ : syracuseStep 5816225 = 4362169) B4362169
theorem B37273529 : Blo 1360499 37273529 := bstep (se 2 (by rfl) ⟨13977573, by rfl⟩ : syracuseStep 37273529 = 27955147) B27955147
theorem B10485713 : Blo 1360499 10485713 := bstep (se 2 (by rfl) ⟨3932142, by rfl⟩ : syracuseStep 10485713 = 7864285) B7864285
theorem B1531867 : Blo 1360499 1531867 := bstep (se 1 (by rfl) ⟨1148900, by rfl⟩ : syracuseStep 1531867 = 2297801) B2297801
theorem B17448979 : Blo 1360499 17448979 := bstep (se 1 (by rfl) ⟨13086734, by rfl⟩ : syracuseStep 17448979 = 26173469) B26173469
theorem B3874841 : Blo 1360499 3874841 := bstep (se 2 (by rfl) ⟨1453065, by rfl⟩ : syracuseStep 3874841 = 2906131) B2906131
theorem B23584945 : Blo 1360499 23584945 := bstep (se 2 (by rfl) ⟨8844354, by rfl⟩ : syracuseStep 23584945 = 17688709) B17688709
theorem B1532191 : Blo 1360499 1532191 := bstep (se 1 (by rfl) ⟨1149143, by rfl⟩ : syracuseStep 1532191 = 2298287) B2298287
theorem B11624795 : Blo 1360499 11624795 := bstep (se 1 (by rfl) ⟨8718596, by rfl⟩ : syracuseStep 11624795 = 17437193) B17437193
theorem B2908523 : Blo 1360499 2908523 := bstep (se 1 (by rfl) ⟨2181392, by rfl⟩ : syracuseStep 2908523 = 4362785) B4362785
theorem B3064175 : Blo 1360499 3064175 := bstep (se 1 (by rfl) ⟨2298131, by rfl⟩ : syracuseStep 3064175 = 4596263) B4596263
theorem B3064247 : Blo 1360499 3064247 := bstep (se 1 (by rfl) ⟨2298185, by rfl⟩ : syracuseStep 3064247 = 4596371) B4596371
theorem B4358657 : Blo 1360499 4358657 := bstep (se 2 (by rfl) ⟨1634496, by rfl⟩ : syracuseStep 4358657 = 3268993) B3268993
theorem B59712011 : Blo 1360499 59712011 := bstep (se 1 (by rfl) ⟨44784008, by rfl⟩ : syracuseStep 59712011 = 89568017) B89568017
theorem B1532479 : Blo 1360499 1532479 := bstep (se 1 (by rfl) ⟨1149359, by rfl⟩ : syracuseStep 1532479 = 2298719) B2298719
theorem B3064391 : Blo 1360499 3064391 := bstep (se 1 (by rfl) ⟨2298293, by rfl⟩ : syracuseStep 3064391 = 4596587) B4596587
theorem B3064427 : Blo 1360499 3064427 := bstep (se 1 (by rfl) ⟨2298320, by rfl⟩ : syracuseStep 3064427 = 4596641) B4596641
theorem B2908847 : Blo 1360499 2908847 := bstep (se 1 (by rfl) ⟨2181635, by rfl⟩ : syracuseStep 2908847 = 4363271) B4363271
theorem B6890183 : Blo 1360499 6890183 := bstep (se 1 (by rfl) ⟨5167637, by rfl⟩ : syracuseStep 6890183 = 10335275) B10335275
theorem B1360607 : Blo 1360499 1360607 := bstep (se 1 (by rfl) ⟨1020455, by rfl⟩ : syracuseStep 1360607 = 2040911) B2040911
theorem B1360687 : Blo 1360499 1360687 := bstep (se 1 (by rfl) ⟨1020515, by rfl⟩ : syracuseStep 1360687 = 2041031) B2041031
theorem B6636383 : Blo 1360499 6636383 := bstep (se 1 (by rfl) ⟨4977287, by rfl⟩ : syracuseStep 6636383 = 9954575) B9954575
theorem B3269531 : Blo 1360499 3269531 := bstep (se 1 (by rfl) ⟨2452148, by rfl⟩ : syracuseStep 3269531 = 4904297) B4904297
theorem B1360795 : Blo 1360499 1360795 := bstep (se 1 (by rfl) ⟨1020596, by rfl⟩ : syracuseStep 1360795 = 2041193) B2041193
theorem B1360847 : Blo 1360499 1360847 := bstep (se 1 (by rfl) ⟨1020635, by rfl⟩ : syracuseStep 1360847 = 2041271) B2041271
theorem B1360871 : Blo 1360499 1360871 := bstep (se 1 (by rfl) ⟨1020653, by rfl⟩ : syracuseStep 1360871 = 2041307) B2041307
theorem B3064823 : Blo 1360499 3064823 := bstep (se 1 (by rfl) ⟨2298617, by rfl⟩ : syracuseStep 3064823 = 4597235) B4597235
theorem B7750889 : Blo 1360499 7750889 := bstep (se 2 (by rfl) ⟨2906583, by rfl⟩ : syracuseStep 7750889 = 5813167) B5813167
theorem B3876083 : Blo 1360499 3876083 := bstep (se 1 (by rfl) ⟨2907062, by rfl⟩ : syracuseStep 3876083 = 5814125) B5814125
theorem B1361183 : Blo 1360499 1361183 := bstep (se 1 (by rfl) ⟨1020887, by rfl⟩ : syracuseStep 1361183 = 2041775) B2041775
theorem B2041127 : Blo 1360499 2041127 := bstep (se 1 (by rfl) ⟨1530845, by rfl⟩ : syracuseStep 2041127 = 3061691) B3061691
theorem B6538583 : Blo 1360499 6538583 := bstep (se 1 (by rfl) ⟨4903937, by rfl⟩ : syracuseStep 6538583 = 9807875) B9807875
theorem B1361243 : Blo 1360499 1361243 := bstep (se 1 (by rfl) ⟨1020932, by rfl⟩ : syracuseStep 1361243 = 2041865) B2041865
theorem B3065183 : Blo 1360499 3065183 := bstep (se 1 (by rfl) ⟨2298887, by rfl⟩ : syracuseStep 3065183 = 4597775) B4597775
theorem B1361263 : Blo 1360499 1361263 := bstep (se 1 (by rfl) ⟨1020947, by rfl⟩ : syracuseStep 1361263 = 2041895) B2041895
theorem B2041211 : Blo 1360499 2041211 := bstep (se 1 (by rfl) ⟨1530908, by rfl⟩ : syracuseStep 2041211 = 3061817) B3061817
theorem B1361319 : Blo 1360499 1361319 := bstep (se 1 (by rfl) ⟨1020989, by rfl⟩ : syracuseStep 1361319 = 2041979) B2041979
theorem B4597181 : Blo 1360499 4597181 := bstep (se 3 (by rfl) ⟨861971, by rfl⟩ : syracuseStep 4597181 = 1723943) B1723943
theorem B2041337 : Blo 1360499 2041337 := bstep (se 2 (by rfl) ⟨765501, by rfl⟩ : syracuseStep 2041337 = 1531003) B1531003
theorem B1361403 : Blo 1360499 1361403 := bstep (se 1 (by rfl) ⟨1021052, by rfl⟩ : syracuseStep 1361403 = 2042105) B2042105
theorem B7357985 : Blo 1360499 7357985 := bstep (se 2 (by rfl) ⟨2759244, by rfl⟩ : syracuseStep 7357985 = 5518489) B5518489
theorem B2909753 : Blo 1360499 2909753 := bstep (se 2 (by rfl) ⟨1091157, by rfl⟩ : syracuseStep 2909753 = 2182315) B2182315
theorem B1361471 : Blo 1360499 1361471 := bstep (se 1 (by rfl) ⟨1021103, by rfl⟩ : syracuseStep 1361471 = 2042207) B2042207
theorem B1361479 : Blo 1360499 1361479 := bstep (se 1 (by rfl) ⟨1021109, by rfl⟩ : syracuseStep 1361479 = 2042219) B2042219
theorem B2041439 : Blo 1360499 2041439 := bstep (se 1 (by rfl) ⟨1531079, by rfl⟩ : syracuseStep 2041439 = 3062159) B3062159
theorem B1361631 : Blo 1360499 1361631 := bstep (se 1 (by rfl) ⟨1021223, by rfl⟩ : syracuseStep 1361631 = 2042447) B2042447
theorem B3065579 : Blo 1360499 3065579 := bstep (se 1 (by rfl) ⟨2299184, by rfl⟩ : syracuseStep 3065579 = 4598369) B4598369
theorem B1361711 : Blo 1360499 1361711 := bstep (se 1 (by rfl) ⟨1021283, by rfl⟩ : syracuseStep 1361711 = 2042567) B2042567
theorem B2041655 : Blo 1360499 2041655 := bstep (se 1 (by rfl) ⟨1531241, by rfl⟩ : syracuseStep 2041655 = 3062483) B3062483
theorem B4597559 : Blo 1360499 4597559 := bstep (se 1 (by rfl) ⟨3448169, by rfl⟩ : syracuseStep 4597559 = 6896339) B6896339
theorem B5891945 : Blo 1360499 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B1361819 : Blo 1360499 1361819 := bstep (se 1 (by rfl) ⟨1021364, by rfl⟩ : syracuseStep 1361819 = 2042729) B2042729
theorem B1361871 : Blo 1360499 1361871 := bstep (se 1 (by rfl) ⟨1021403, by rfl⟩ : syracuseStep 1361871 = 2042807) B2042807
theorem B1361895 : Blo 1360499 1361895 := bstep (se 1 (by rfl) ⟨1021421, by rfl⟩ : syracuseStep 1361895 = 2042843) B2042843
theorem B6211565 : Blo 1360499 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B2041961 : Blo 1360499 2041961 := bstep (se 2 (by rfl) ⟨765735, by rfl⟩ : syracuseStep 2041961 = 1531471) B1531471
theorem B8726723 : Blo 1360499 8726723 := bstep (se 1 (by rfl) ⟨6545042, by rfl⟩ : syracuseStep 8726723 = 13090085) B13090085
theorem B2296073 : Blo 1360499 2296073 := bstep (se 2 (by rfl) ⟨861027, by rfl⟩ : syracuseStep 2296073 = 1722055) B1722055
theorem B5171465 : Blo 1360499 5171465 := bstep (se 2 (by rfl) ⟨1939299, by rfl⟩ : syracuseStep 5171465 = 3878599) B3878599
theorem B1362207 : Blo 1360499 1362207 := bstep (se 1 (by rfl) ⟨1021655, by rfl⟩ : syracuseStep 1362207 = 2043311) B2043311
theorem B4598045 : Blo 1360499 4598045 := bstep (se 3 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 4598045 = 1724267) B1724267
theorem B3680603 : Blo 1360499 3680603 := bstep (se 1 (by rfl) ⟨2760452, by rfl⟩ : syracuseStep 3680603 = 5520905) B5520905
theorem B1362267 : Blo 1360499 1362267 := bstep (se 1 (by rfl) ⟨1021700, by rfl⟩ : syracuseStep 1362267 = 2043401) B2043401
theorem B1362287 : Blo 1360499 1362287 := bstep (se 1 (by rfl) ⟨1021715, by rfl⟩ : syracuseStep 1362287 = 2043431) B2043431
theorem B2042279 : Blo 1360499 2042279 := bstep (se 1 (by rfl) ⟨1531709, by rfl⟩ : syracuseStep 2042279 = 3063419) B3063419
theorem B1362343 : Blo 1360499 1362343 := bstep (se 1 (by rfl) ⟨1021757, by rfl⟩ : syracuseStep 1362343 = 2043515) B2043515
theorem B10480045 : Blo 1360499 10480045 := bstep (se 3 (by rfl) ⟨1965008, by rfl⟩ : syracuseStep 10480045 = 3930017) B3930017
theorem B2042363 : Blo 1360499 2042363 := bstep (se 1 (by rfl) ⟨1531772, by rfl⟩ : syracuseStep 2042363 = 3063545) B3063545
theorem B1362427 : Blo 1360499 1362427 := bstep (se 1 (by rfl) ⟨1021820, by rfl⟩ : syracuseStep 1362427 = 2043641) B2043641
theorem B1362495 : Blo 1360499 1362495 := bstep (se 1 (by rfl) ⟨1021871, by rfl⟩ : syracuseStep 1362495 = 2043743) B2043743
theorem B6818383 : Blo 1360499 6818383 := bstep (se 1 (by rfl) ⟨5113787, by rfl⟩ : syracuseStep 6818383 = 10227575) B10227575
theorem B3877483 : Blo 1360499 3877483 := bstep (se 1 (by rfl) ⟨2908112, by rfl⟩ : syracuseStep 3877483 = 5816225) B5816225
theorem B2042489 : Blo 1360499 2042489 := bstep (se 2 (by rfl) ⟨765933, by rfl⟩ : syracuseStep 2042489 = 1531867) B1531867
theorem B24849019 : Blo 1360499 24849019 := bstep (se 1 (by rfl) ⟨18636764, by rfl⟩ : syracuseStep 24849019 = 37273529) B37273529
theorem B6990475 : Blo 1360499 6990475 := bstep (se 1 (by rfl) ⟨5242856, by rfl⟩ : syracuseStep 6990475 = 10485713) B10485713
theorem B2042543 : Blo 1360499 2042543 := bstep (se 1 (by rfl) ⟨1531907, by rfl⟩ : syracuseStep 2042543 = 3063815) B3063815
theorem B29420243 : Blo 1360499 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B2042591 : Blo 1360499 2042591 := bstep (se 1 (by rfl) ⟨1531943, by rfl⟩ : syracuseStep 2042591 = 3063887) B3063887
theorem B3877757 : Blo 1360499 3877757 := bstep (se 3 (by rfl) ⟨727079, by rfl⟩ : syracuseStep 3877757 = 1454159) B1454159
theorem B4909949 : Blo 1360499 4909949 := bstep (se 3 (by rfl) ⟨920615, by rfl⟩ : syracuseStep 4909949 = 1841231) B1841231
theorem B88337303 : Blo 1360499 88337303 := bstep (se 1 (by rfl) ⟨66252977, by rfl⟩ : syracuseStep 88337303 = 132505955) B132505955
theorem B4139947 : Blo 1360499 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B2042855 : Blo 1360499 2042855 := bstep (se 1 (by rfl) ⟨1532141, by rfl⟩ : syracuseStep 2042855 = 3064283) B3064283
theorem B2329591 : Blo 1360499 2329591 := bstep (se 1 (by rfl) ⟨1747193, by rfl⟩ : syracuseStep 2329591 = 3494387) B3494387
theorem B19623131 : Blo 1360499 19623131 := bstep (se 1 (by rfl) ⟨14717348, by rfl⟩ : syracuseStep 19623131 = 29434697) B29434697
theorem B2297065 : Blo 1360499 2297065 := bstep (se 2 (by rfl) ⟨861399, by rfl⟩ : syracuseStep 2297065 = 1722799) B1722799
theorem B2043113 : Blo 1360499 2043113 := bstep (se 2 (by rfl) ⟨766167, by rfl⟩ : syracuseStep 2043113 = 1532335) B1532335
theorem B2297119 : Blo 1360499 2297119 := bstep (se 1 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 2297119 = 3445679) B3445679
theorem B2043167 : Blo 1360499 2043167 := bstep (se 1 (by rfl) ⟨1532375, by rfl⟩ : syracuseStep 2043167 = 3064751) B3064751
theorem B1723771 : Blo 1360499 1723771 := bstep (se 1 (by rfl) ⟨1292828, by rfl⟩ : syracuseStep 1723771 = 2585657) B2585657
theorem B6892937 : Blo 1360499 6892937 := bstep (se 2 (by rfl) ⟨2584851, by rfl⟩ : syracuseStep 6892937 = 5169703) B5169703
theorem B2043335 : Blo 1360499 2043335 := bstep (se 1 (by rfl) ⟨1532501, by rfl⟩ : syracuseStep 2043335 = 3065003) B3065003
theorem B5516815 : Blo 1360499 5516815 := bstep (se 1 (by rfl) ⟨4137611, by rfl⟩ : syracuseStep 5516815 = 8275223) B8275223
theorem B1723999 : Blo 1360499 1723999 := bstep (se 1 (by rfl) ⟨1292999, by rfl⟩ : syracuseStep 1723999 = 2585999) B2585999
theorem B2297531 : Blo 1360499 2297531 := bstep (se 1 (by rfl) ⟨1723148, by rfl⟩ : syracuseStep 2297531 = 3446297) B3446297
theorem B2043689 : Blo 1360499 2043689 := bstep (se 2 (by rfl) ⟨766383, by rfl⟩ : syracuseStep 2043689 = 1532767) B1532767
theorem B2043695 : Blo 1360499 2043695 := bstep (se 1 (by rfl) ⟨1532771, by rfl⟩ : syracuseStep 2043695 = 3065543) B3065543
theorem B3362615 : Blo 1360499 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B33107899 : Blo 1360499 33107899 := bstep (se 1 (by rfl) ⟨24830924, by rfl⟩ : syracuseStep 33107899 = 49661849) B49661849
theorem B29421629 : Blo 1360499 29421629 := bstep (se 3 (by rfl) ⟨5516555, by rfl⟩ : syracuseStep 29421629 = 11033111) B11033111
theorem B6541523 : Blo 1360499 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B3445001 : Blo 1360499 3445001 := bstep (se 2 (by rfl) ⟨1291875, by rfl⟩ : syracuseStep 3445001 = 2583751) B2583751
theorem B2584943 : Blo 1360499 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B3445355 : Blo 1360499 3445355 := bstep (se 1 (by rfl) ⟨2584016, by rfl⟩ : syracuseStep 3445355 = 5168033) B5168033
theorem B3314297 : Blo 1360499 3314297 := bstep (se 2 (by rfl) ⟨1242861, by rfl⟩ : syracuseStep 3314297 = 2485723) B2485723
theorem B2585209 : Blo 1360499 2585209 := bstep (se 2 (by rfl) ⟨969453, by rfl⟩ : syracuseStep 2585209 = 1938907) B1938907
theorem B6894233 : Blo 1360499 6894233 := bstep (se 2 (by rfl) ⟨2585337, by rfl⟩ : syracuseStep 6894233 = 5170675) B5170675
theorem B3879647 : Blo 1360499 3879647 := bstep (se 1 (by rfl) ⟨2909735, by rfl⟩ : syracuseStep 3879647 = 5819471) B5819471
theorem B3273491 : Blo 1360499 3273491 := bstep (se 1 (by rfl) ⟨2455118, by rfl⟩ : syracuseStep 3273491 = 4910237) B4910237
theorem B35353745 : Blo 1360499 35353745 := bstep (se 2 (by rfl) ⟨13257654, by rfl⟩ : syracuseStep 35353745 = 26515309) B26515309
theorem B9311377 : Blo 1360499 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B11637917 : Blo 1360499 11637917 := bstep (se 3 (by rfl) ⟨2182109, by rfl⟩ : syracuseStep 11637917 = 4364219) B4364219
theorem B5813491 : Blo 1360499 5813491 := bstep (se 1 (by rfl) ⟨4360118, by rfl⟩ : syracuseStep 5813491 = 8720237) B8720237
theorem B3446003 : Blo 1360499 3446003 := bstep (se 1 (by rfl) ⟨2584502, by rfl⟩ : syracuseStep 3446003 = 5169005) B5169005
theorem B11629919 : Blo 1360499 11629919 := bstep (se 1 (by rfl) ⟨8722439, by rfl⟩ : syracuseStep 11629919 = 17444879) B17444879
theorem B6206843 : Blo 1360499 6206843 := bstep (se 1 (by rfl) ⟨4655132, by rfl⟩ : syracuseStep 6206843 = 9310265) B9310265
theorem B9811361 : Blo 1360499 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B3061241 : Blo 1360499 3061241 := bstep (se 2 (by rfl) ⟨1147965, by rfl⟩ : syracuseStep 3061241 = 2295931) B2295931
theorem B29455883 : Blo 1360499 29455883 := bstep (se 1 (by rfl) ⟨22091912, by rfl⟩ : syracuseStep 29455883 = 44183825) B44183825
theorem B3061331 : Blo 1360499 3061331 := bstep (se 1 (by rfl) ⟨2295998, by rfl⟩ : syracuseStep 3061331 = 4591997) B4591997
theorem B3446459 : Blo 1360499 3446459 := bstep (se 1 (by rfl) ⟨2584844, by rfl⟩ : syracuseStep 3446459 = 5169689) B5169689
theorem B3061511 : Blo 1360499 3061511 := bstep (se 1 (by rfl) ⟨2296133, by rfl⟩ : syracuseStep 3061511 = 4592267) B4592267
theorem B3315817 : Blo 1360499 3315817 := bstep (se 2 (by rfl) ⟨1243431, by rfl⟩ : syracuseStep 3315817 = 2486863) B2486863
theorem B3446995 : Blo 1360499 3446995 := bstep (se 1 (by rfl) ⟨2585246, by rfl⟩ : syracuseStep 3446995 = 5170493) B5170493
theorem B11032823 : Blo 1360499 11032823 := bstep (se 1 (by rfl) ⟨8274617, by rfl⟩ : syracuseStep 11032823 = 16549235) B16549235
theorem B10483991 : Blo 1360499 10483991 := bstep (se 1 (by rfl) ⟨7862993, by rfl⟩ : syracuseStep 10483991 = 15725987) B15725987
theorem B3062123 : Blo 1360499 3062123 := bstep (se 1 (by rfl) ⟨2296592, by rfl⟩ : syracuseStep 3062123 = 4593185) B4593185
theorem B6896015 : Blo 1360499 6896015 := bstep (se 1 (by rfl) ⟨5172011, by rfl⟩ : syracuseStep 6896015 = 10344023) B10344023
theorem B4594103 : Blo 1360499 4594103 := bstep (se 1 (by rfl) ⟨3445577, by rfl⟩ : syracuseStep 4594103 = 6891155) B6891155
theorem B7559675 : Blo 1360499 7559675 := bstep (se 1 (by rfl) ⟨5669756, by rfl⟩ : syracuseStep 7559675 = 11339513) B11339513
theorem B3062267 : Blo 1360499 3062267 := bstep (se 1 (by rfl) ⟨2296700, by rfl⟩ : syracuseStep 3062267 = 4593401) B4593401
theorem B11786791 : Blo 1360499 11786791 := bstep (se 1 (by rfl) ⟨8840093, by rfl⟩ : syracuseStep 11786791 = 17680187) B17680187
theorem B5814823 : Blo 1360499 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B3062393 : Blo 1360499 3062393 := bstep (se 2 (by rfl) ⟨1148397, by rfl⟩ : syracuseStep 3062393 = 2296795) B2296795
theorem B3062447 : Blo 1360499 3062447 := bstep (se 1 (by rfl) ⟨2296835, by rfl⟩ : syracuseStep 3062447 = 4593671) B4593671
theorem B3062519 : Blo 1360499 3062519 := bstep (se 1 (by rfl) ⟨2296889, by rfl⟩ : syracuseStep 3062519 = 4593779) B4593779
theorem B5815165 : Blo 1360499 5815165 := bstep (se 3 (by rfl) ⟨1090343, by rfl⟩ : syracuseStep 5815165 = 2180687) B2180687
theorem B3062699 : Blo 1360499 3062699 := bstep (se 1 (by rfl) ⟨2297024, by rfl⟩ : syracuseStep 3062699 = 4594049) B4594049
theorem B6888563 : Blo 1360499 6888563 := bstep (se 1 (by rfl) ⟨5166422, by rfl⟩ : syracuseStep 6888563 = 10332845) B10332845
theorem B3447947 : Blo 1360499 3447947 := bstep (se 1 (by rfl) ⟨2585960, by rfl⟩ : syracuseStep 3447947 = 5171921) B5171921
theorem B14916797 : Blo 1360499 14916797 := bstep (se 3 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 14916797 = 5593799) B5593799
theorem B2907515 : Blo 1360499 2907515 := bstep (se 1 (by rfl) ⟨2180636, by rfl⟩ : syracuseStep 2907515 = 4361273) B4361273
theorem B3063239 : Blo 1360499 3063239 := bstep (se 1 (by rfl) ⟨2297429, by rfl⟩ : syracuseStep 3063239 = 4594859) B4594859
theorem B4906489 : Blo 1360499 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B7749179 : Blo 1360499 7749179 := bstep (se 1 (by rfl) ⟨5811884, by rfl⟩ : syracuseStep 7749179 = 11623769) B11623769
theorem B3448403 : Blo 1360499 3448403 := bstep (se 1 (by rfl) ⟨2586302, by rfl⟩ : syracuseStep 3448403 = 5172605) B5172605
theorem B12279443 : Blo 1360499 12279443 := bstep (se 1 (by rfl) ⟨9209582, by rfl⟩ : syracuseStep 12279443 = 18419165) B18419165
theorem B1531615 : Blo 1360499 1531615 := bstep (se 1 (by rfl) ⟨1148711, by rfl⟩ : syracuseStep 1531615 = 2297423) B2297423
theorem B3874567 : Blo 1360499 3874567 := bstep (se 1 (by rfl) ⟨2905925, by rfl⟩ : syracuseStep 3874567 = 5811851) B5811851
theorem B3063599 : Blo 1360499 3063599 := bstep (se 1 (by rfl) ⟨2297699, by rfl⟩ : syracuseStep 3063599 = 4595399) B4595399
theorem B6545213 : Blo 1360499 6545213 := bstep (se 3 (by rfl) ⟨1227227, by rfl⟩ : syracuseStep 6545213 = 2454455) B2454455
theorem B6889373 : Blo 1360499 6889373 := bstep (se 3 (by rfl) ⟨1291757, by rfl⟩ : syracuseStep 6889373 = 2583515) B2583515
theorem B23265305 : Blo 1360499 23265305 := bstep (se 2 (by rfl) ⟨8724489, by rfl⟩ : syracuseStep 23265305 = 17448979) B17448979
theorem B7749863 : Blo 1360499 7749863 := bstep (se 1 (by rfl) ⟨5812397, by rfl⟩ : syracuseStep 7749863 = 11624795) B11624795
theorem B4595993 : Blo 1360499 4595993 := bstep (se 2 (by rfl) ⟨1723497, by rfl⟩ : syracuseStep 4595993 = 3446995) B3446995
theorem B4596155 : Blo 1360499 4596155 := bstep (se 1 (by rfl) ⟨3447116, by rfl⟩ : syracuseStep 4596155 = 6894233) B6894233
theorem B4424255 : Blo 1360499 4424255 := bstep (se 1 (by rfl) ⟨3318191, by rfl⟩ : syracuseStep 4424255 = 6636383) B6636383
theorem B23569163 : Blo 1360499 23569163 := bstep (se 1 (by rfl) ⟨17676872, by rfl⟩ : syracuseStep 23569163 = 35353745) B35353745
theorem B7758611 : Blo 1360499 7758611 := bstep (se 1 (by rfl) ⟨5818958, by rfl⟩ : syracuseStep 7758611 = 11637917) B11637917
theorem B5169977 : Blo 1360499 5169977 := bstep (se 2 (by rfl) ⟨1938741, by rfl⟩ : syracuseStep 5169977 = 3877483) B3877483
theorem B1360751 : Blo 1360499 1360751 := bstep (se 1 (by rfl) ⟨1020563, by rfl⟩ : syracuseStep 1360751 = 2041127) B2041127
theorem B4137895 : Blo 1360499 4137895 := bstep (se 1 (by rfl) ⟨3103421, by rfl⟩ : syracuseStep 4137895 = 6206843) B6206843
theorem B1360807 : Blo 1360499 1360807 := bstep (se 1 (by rfl) ⟨1020605, by rfl⟩ : syracuseStep 1360807 = 2041211) B2041211
theorem B3064787 : Blo 1360499 3064787 := bstep (se 1 (by rfl) ⟨2298590, by rfl⟩ : syracuseStep 3064787 = 4597181) B4597181
theorem B2040827 : Blo 1360499 2040827 := bstep (se 1 (by rfl) ⟨1530620, by rfl⟩ : syracuseStep 2040827 = 3061241) B3061241
theorem B1360891 : Blo 1360499 1360891 := bstep (se 1 (by rfl) ⟨1020668, by rfl⟩ : syracuseStep 1360891 = 2041337) B2041337
theorem B19637255 : Blo 1360499 19637255 := bstep (se 1 (by rfl) ⟨14727941, by rfl⟩ : syracuseStep 19637255 = 29455883) B29455883
theorem B2040887 : Blo 1360499 2040887 := bstep (se 1 (by rfl) ⟨1530665, by rfl⟩ : syracuseStep 2040887 = 3061331) B3061331
theorem B1360959 : Blo 1360499 1360959 := bstep (se 1 (by rfl) ⟨1020719, by rfl⟩ : syracuseStep 1360959 = 2041439) B2041439
theorem B2041007 : Blo 1360499 2041007 := bstep (se 1 (by rfl) ⟨1530755, by rfl⟩ : syracuseStep 2041007 = 3061511) B3061511
theorem B1361103 : Blo 1360499 1361103 := bstep (se 1 (by rfl) ⟨1020827, by rfl⟩ : syracuseStep 1361103 = 2041655) B2041655
theorem B3065039 : Blo 1360499 3065039 := bstep (se 1 (by rfl) ⟨2298779, by rfl⟩ : syracuseStep 3065039 = 4597559) B4597559
theorem B3106121 : Blo 1360499 3106121 := bstep (se 2 (by rfl) ⟨1164795, by rfl⟩ : syracuseStep 3106121 = 2329591) B2329591
theorem B1361307 : Blo 1360499 1361307 := bstep (se 1 (by rfl) ⟨1020980, by rfl⟩ : syracuseStep 1361307 = 2041961) B2041961
theorem B5817815 : Blo 1360499 5817815 := bstep (se 1 (by rfl) ⟨4363361, by rfl⟩ : syracuseStep 5817815 = 8726723) B8726723
theorem B6989327 : Blo 1360499 6989327 := bstep (se 1 (by rfl) ⟨5241995, by rfl⟩ : syracuseStep 6989327 = 10483991) B10483991
theorem B3065363 : Blo 1360499 3065363 := bstep (se 1 (by rfl) ⟨2299022, by rfl⟩ : syracuseStep 3065363 = 4598045) B4598045
theorem B2041415 : Blo 1360499 2041415 := bstep (se 1 (by rfl) ⟨1531061, by rfl⟩ : syracuseStep 2041415 = 3062123) B3062123
theorem B4597343 : Blo 1360499 4597343 := bstep (se 1 (by rfl) ⟨3448007, by rfl⟩ : syracuseStep 4597343 = 6896015) B6896015
theorem B1361519 : Blo 1360499 1361519 := bstep (se 1 (by rfl) ⟨1021139, by rfl⟩ : syracuseStep 1361519 = 2042279) B2042279
theorem B7751321 : Blo 1360499 7751321 := bstep (se 2 (by rfl) ⟨2906745, by rfl⟩ : syracuseStep 7751321 = 5813491) B5813491
theorem B5039783 : Blo 1360499 5039783 := bstep (se 1 (by rfl) ⟨3779837, by rfl⟩ : syracuseStep 5039783 = 7559675) B7559675
theorem B2041511 : Blo 1360499 2041511 := bstep (se 1 (by rfl) ⟨1531133, by rfl⟩ : syracuseStep 2041511 = 3062267) B3062267
theorem B1361575 : Blo 1360499 1361575 := bstep (se 1 (by rfl) ⟨1021181, by rfl⟩ : syracuseStep 1361575 = 2042363) B2042363
theorem B32745181 : Blo 1360499 32745181 := bstep (se 3 (by rfl) ⟨6139721, by rfl⟩ : syracuseStep 32745181 = 12279443) B12279443
theorem B2041595 : Blo 1360499 2041595 := bstep (se 1 (by rfl) ⟨1531196, by rfl⟩ : syracuseStep 2041595 = 3062393) B3062393
theorem B1361659 : Blo 1360499 1361659 := bstep (se 1 (by rfl) ⟨1021244, by rfl⟩ : syracuseStep 1361659 = 2042489) B2042489
theorem B2041631 : Blo 1360499 2041631 := bstep (se 1 (by rfl) ⟨1531223, by rfl⟩ : syracuseStep 2041631 = 3062447) B3062447
theorem B1361695 : Blo 1360499 1361695 := bstep (se 1 (by rfl) ⟨1021271, by rfl⟩ : syracuseStep 1361695 = 2042543) B2042543
theorem B19613495 : Blo 1360499 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B1361727 : Blo 1360499 1361727 := bstep (se 1 (by rfl) ⟨1021295, by rfl⟩ : syracuseStep 1361727 = 2042591) B2042591
theorem B2041679 : Blo 1360499 2041679 := bstep (se 1 (by rfl) ⟨1531259, by rfl⟩ : syracuseStep 2041679 = 3062519) B3062519
theorem B2041799 : Blo 1360499 2041799 := bstep (se 1 (by rfl) ⟨1531349, by rfl⟩ : syracuseStep 2041799 = 3062699) B3062699
theorem B1361903 : Blo 1360499 1361903 := bstep (se 1 (by rfl) ⟨1021427, by rfl⟩ : syracuseStep 1361903 = 2042855) B2042855
theorem B1362075 : Blo 1360499 1362075 := bstep (se 1 (by rfl) ⟨1021556, by rfl⟩ : syracuseStep 1362075 = 2043113) B2043113
theorem B1362111 : Blo 1360499 1362111 := bstep (se 1 (by rfl) ⟨1021583, by rfl⟩ : syracuseStep 1362111 = 2043167) B2043167
theorem B2042153 : Blo 1360499 2042153 := bstep (se 2 (by rfl) ⟨765807, by rfl⟩ : syracuseStep 2042153 = 1531615) B1531615
theorem B2042159 : Blo 1360499 2042159 := bstep (se 1 (by rfl) ⟨1531619, by rfl⟩ : syracuseStep 2042159 = 3063239) B3063239
theorem B1362223 : Blo 1360499 1362223 := bstep (se 1 (by rfl) ⟨1021667, by rfl⟩ : syracuseStep 1362223 = 2043335) B2043335
theorem B8718749 : Blo 1360499 8718749 := bstep (se 3 (by rfl) ⟨1634765, by rfl⟩ : syracuseStep 8718749 = 3269531) B3269531
theorem B1362459 : Blo 1360499 1362459 := bstep (se 1 (by rfl) ⟨1021844, by rfl⟩ : syracuseStep 1362459 = 2043689) B2043689
theorem B2042399 : Blo 1360499 2042399 := bstep (se 1 (by rfl) ⟨1531799, by rfl⟩ : syracuseStep 2042399 = 3063599) B3063599
theorem B1362463 : Blo 1360499 1362463 := bstep (se 1 (by rfl) ⟨1021847, by rfl⟩ : syracuseStep 1362463 = 2043695) B2043695
theorem B2583227 : Blo 1360499 2583227 := bstep (se 1 (by rfl) ⟨1937420, by rfl⟩ : syracuseStep 2583227 = 3874841) B3874841
theorem B19614419 : Blo 1360499 19614419 := bstep (se 1 (by rfl) ⟨14710814, by rfl⟩ : syracuseStep 19614419 = 29421629) B29421629
theorem B4361015 : Blo 1360499 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B2296667 : Blo 1360499 2296667 := bstep (se 1 (by rfl) ⟨1722500, by rfl⟩ : syracuseStep 2296667 = 3445001) B3445001
theorem B1723295 : Blo 1360499 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B2042783 : Blo 1360499 2042783 := bstep (se 1 (by rfl) ⟨1532087, by rfl⟩ : syracuseStep 2042783 = 3064175) B3064175
theorem B2042831 : Blo 1360499 2042831 := bstep (se 1 (by rfl) ⟨1532123, by rfl⟩ : syracuseStep 2042831 = 3064247) B3064247
theorem B39808007 : Blo 1360499 39808007 := bstep (se 1 (by rfl) ⟨29856005, by rfl⟩ : syracuseStep 39808007 = 59712011) B59712011
theorem B2042921 : Blo 1360499 2042921 := bstep (se 2 (by rfl) ⟨766095, by rfl⟩ : syracuseStep 2042921 = 1532191) B1532191
theorem B2042927 : Blo 1360499 2042927 := bstep (se 1 (by rfl) ⟨1532195, by rfl⟩ : syracuseStep 2042927 = 3064391) B3064391
theorem B2296903 : Blo 1360499 2296903 := bstep (se 1 (by rfl) ⟨1722677, by rfl⟩ : syracuseStep 2296903 = 3445355) B3445355
theorem B2042951 : Blo 1360499 2042951 := bstep (se 1 (by rfl) ⟨1532213, by rfl⟩ : syracuseStep 2042951 = 3064427) B3064427
theorem B2043215 : Blo 1360499 2043215 := bstep (se 1 (by rfl) ⟨1532411, by rfl⟩ : syracuseStep 2043215 = 3064823) B3064823
theorem B15715721 : Blo 1360499 15715721 := bstep (se 2 (by rfl) ⟨5893395, by rfl⟩ : syracuseStep 15715721 = 11786791) B11786791
theorem B7753097 : Blo 1360499 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B2043305 : Blo 1360499 2043305 := bstep (se 2 (by rfl) ⟨766239, by rfl⟩ : syracuseStep 2043305 = 1532479) B1532479
theorem B2584055 : Blo 1360499 2584055 := bstep (se 1 (by rfl) ⟨1938041, by rfl⟩ : syracuseStep 2584055 = 3876083) B3876083
theorem B2297335 : Blo 1360499 2297335 := bstep (se 1 (by rfl) ⟨1723001, by rfl⟩ : syracuseStep 2297335 = 3446003) B3446003
theorem B33132025 : Blo 1360499 33132025 := bstep (se 2 (by rfl) ⟨12424509, by rfl⟩ : syracuseStep 33132025 = 24849019) B24849019
theorem B17436221 : Blo 1360499 17436221 := bstep (se 3 (by rfl) ⟨3269291, by rfl⟩ : syracuseStep 17436221 = 6538583) B6538583
theorem B7753279 : Blo 1360499 7753279 := bstep (se 1 (by rfl) ⟨5814959, by rfl⟩ : syracuseStep 7753279 = 11629919) B11629919
theorem B2043455 : Blo 1360499 2043455 := bstep (se 1 (by rfl) ⟨1532591, by rfl⟩ : syracuseStep 2043455 = 3065183) B3065183
theorem B6540907 : Blo 1360499 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B2297639 : Blo 1360499 2297639 := bstep (se 1 (by rfl) ⟨1723229, by rfl⟩ : syracuseStep 2297639 = 3446459) B3446459
theorem B2043719 : Blo 1360499 2043719 := bstep (se 1 (by rfl) ⟨1532789, by rfl⟩ : syracuseStep 2043719 = 3065579) B3065579
theorem B7753553 : Blo 1360499 7753553 := bstep (se 2 (by rfl) ⟨2907582, by rfl⟩ : syracuseStep 7753553 = 5815165) B5815165
theorem B4141043 : Blo 1360499 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B12415169 : Blo 1360499 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B2453735 : Blo 1360499 2453735 := bstep (se 1 (by rfl) ⟨1840301, by rfl⟩ : syracuseStep 2453735 = 3680603) B3680603
theorem B2298361 : Blo 1360499 2298361 := bstep (se 2 (by rfl) ⟨861885, by rfl⟩ : syracuseStep 2298361 = 1723771) B1723771
theorem B2585171 : Blo 1360499 2585171 := bstep (se 1 (by rfl) ⟨1938878, by rfl⟩ : syracuseStep 2585171 = 3877757) B3877757
theorem B3273299 : Blo 1360499 3273299 := bstep (se 1 (by rfl) ⟨2454974, by rfl⟩ : syracuseStep 3273299 = 4909949) B4909949
theorem B6541985 : Blo 1360499 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B8729309 : Blo 1360499 8729309 := bstep (se 3 (by rfl) ⟨1636745, by rfl⟩ : syracuseStep 8729309 = 3273491) B3273491
theorem B4592375 : Blo 1360499 4592375 := bstep (se 1 (by rfl) ⟨3444281, by rfl⟩ : syracuseStep 4592375 = 6888563) B6888563
theorem B2298631 : Blo 1360499 2298631 := bstep (se 1 (by rfl) ⟨1723973, by rfl⟩ : syracuseStep 2298631 = 3447947) B3447947
theorem B2298665 : Blo 1360499 2298665 := bstep (se 2 (by rfl) ⟨861999, by rfl⟩ : syracuseStep 2298665 = 1723999) B1723999
theorem B1938343 : Blo 1360499 1938343 := bstep (se 1 (by rfl) ⟨1453757, by rfl⟩ : syracuseStep 1938343 = 2907515) B2907515
theorem B5166089 : Blo 1360499 5166089 := bstep (se 2 (by rfl) ⟨1937283, by rfl⟩ : syracuseStep 5166089 = 3874567) B3874567
theorem B5166119 : Blo 1360499 5166119 := bstep (se 1 (by rfl) ⟨3874589, by rfl⟩ : syracuseStep 5166119 = 7749179) B7749179
theorem B2298935 : Blo 1360499 2298935 := bstep (se 1 (by rfl) ⟨1724201, by rfl⟩ : syracuseStep 2298935 = 3448403) B3448403
theorem B2241743 : Blo 1360499 2241743 := bstep (se 1 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 2241743 = 3362615) B3362615
theorem B4363475 : Blo 1360499 4363475 := bstep (se 1 (by rfl) ⟨3272606, by rfl⟩ : syracuseStep 4363475 = 6545213) B6545213
theorem B44143865 : Blo 1360499 44143865 := bstep (se 2 (by rfl) ⟨16553949, by rfl⟩ : syracuseStep 44143865 = 33107899) B33107899
theorem B4592915 : Blo 1360499 4592915 := bstep (se 1 (by rfl) ⟨3444686, by rfl⟩ : syracuseStep 4592915 = 6889373) B6889373
theorem B4421089 : Blo 1360499 4421089 := bstep (se 2 (by rfl) ⟨1657908, by rfl⟩ : syracuseStep 4421089 = 3315817) B3315817
theorem B31446593 : Blo 1360499 31446593 := bstep (se 2 (by rfl) ⟨11792472, by rfl⟩ : syracuseStep 31446593 = 23584945) B23584945
theorem B1939015 : Blo 1360499 1939015 := bstep (se 1 (by rfl) ⟨1454261, by rfl⟩ : syracuseStep 1939015 = 2908523) B2908523
theorem B2209531 : Blo 1360499 2209531 := bstep (se 1 (by rfl) ⟨1657148, by rfl⟩ : syracuseStep 2209531 = 3314297) B3314297
theorem B1939231 : Blo 1360499 1939231 := bstep (se 1 (by rfl) ⟨1454423, by rfl⟩ : syracuseStep 1939231 = 2908847) B2908847
theorem B4593455 : Blo 1360499 4593455 := bstep (se 1 (by rfl) ⟨3445091, by rfl⟩ : syracuseStep 4593455 = 6890183) B6890183
theorem B2586431 : Blo 1360499 2586431 := bstep (se 1 (by rfl) ⟨1939823, by rfl⟩ : syracuseStep 2586431 = 3879647) B3879647
theorem B13973393 : Blo 1360499 13973393 := bstep (se 2 (by rfl) ⟨5240022, by rfl⟩ : syracuseStep 13973393 = 10480045) B10480045
theorem B9091177 : Blo 1360499 9091177 := bstep (se 2 (by rfl) ⟨3409191, by rfl⟩ : syracuseStep 9091177 = 6818383) B6818383
theorem B5167259 : Blo 1360499 5167259 := bstep (se 1 (by rfl) ⟨3875444, by rfl⟩ : syracuseStep 5167259 = 7750889) B7750889
theorem B3446945 : Blo 1360499 3446945 := bstep (se 2 (by rfl) ⟨1292604, by rfl⟩ : syracuseStep 3446945 = 2585209) B2585209
theorem B9320633 : Blo 1360499 9320633 := bstep (se 2 (by rfl) ⟨3495237, by rfl⟩ : syracuseStep 9320633 = 6990475) B6990475
theorem B4905323 : Blo 1360499 4905323 := bstep (se 1 (by rfl) ⟨3678992, by rfl⟩ : syracuseStep 4905323 = 7357985) B7357985
theorem B1939835 : Blo 1360499 1939835 := bstep (se 1 (by rfl) ⟨1454876, by rfl⟩ : syracuseStep 1939835 = 2909753) B2909753
theorem B5519929 : Blo 1360499 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B11623085 : Blo 1360499 11623085 := bstep (se 3 (by rfl) ⟨2179328, by rfl⟩ : syracuseStep 11623085 = 4358657) B4358657
theorem B7355215 : Blo 1360499 7355215 := bstep (se 1 (by rfl) ⟨5516411, by rfl⟩ : syracuseStep 7355215 = 11032823) B11032823
theorem B1530715 : Blo 1360499 1530715 := bstep (se 1 (by rfl) ⟨1148036, by rfl⟩ : syracuseStep 1530715 = 2296073) B2296073
theorem B3447643 : Blo 1360499 3447643 := bstep (se 1 (by rfl) ⟨2585732, by rfl⟩ : syracuseStep 3447643 = 5171465) B5171465
theorem B3062735 : Blo 1360499 3062735 := bstep (se 1 (by rfl) ⟨2297051, by rfl⟩ : syracuseStep 3062735 = 4594103) B4594103
theorem B3062753 : Blo 1360499 3062753 := bstep (se 2 (by rfl) ⟨1148532, by rfl⟩ : syracuseStep 3062753 = 2297065) B2297065
theorem B3062825 : Blo 1360499 3062825 := bstep (se 2 (by rfl) ⟨1148559, by rfl⟩ : syracuseStep 3062825 = 2297119) B2297119
theorem B58891535 : Blo 1360499 58891535 := bstep (se 1 (by rfl) ⟨44168651, by rfl⟩ : syracuseStep 58891535 = 88337303) B88337303
theorem B7355753 : Blo 1360499 7355753 := bstep (se 2 (by rfl) ⟨2758407, by rfl⟩ : syracuseStep 7355753 = 5516815) B5516815
theorem B9944531 : Blo 1360499 9944531 := bstep (se 1 (by rfl) ⟨7458398, by rfl⟩ : syracuseStep 9944531 = 14916797) B14916797
theorem B13082087 : Blo 1360499 13082087 := bstep (se 1 (by rfl) ⟨9811565, by rfl⟩ : syracuseStep 13082087 = 19623131) B19623131
theorem B4595291 : Blo 1360499 4595291 := bstep (se 1 (by rfl) ⟨3446468, by rfl⟩ : syracuseStep 4595291 = 6892937) B6892937
theorem B15711853 : Blo 1360499 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B1531687 : Blo 1360499 1531687 := bstep (se 1 (by rfl) ⟨1148765, by rfl⟩ : syracuseStep 1531687 = 2297531) B2297531
theorem B3063995 : Blo 1360499 3063995 := bstep (se 1 (by rfl) ⟨2297996, by rfl⟩ : syracuseStep 3063995 = 4595993) B4595993
theorem B3064103 : Blo 1360499 3064103 := bstep (se 1 (by rfl) ⟨2298077, by rfl⟩ : syracuseStep 3064103 = 4596155) B4596155
theorem B2949503 : Blo 1360499 2949503 := bstep (se 1 (by rfl) ⟨2212127, by rfl⟩ : syracuseStep 2949503 = 4424255) B4424255
theorem B15712775 : Blo 1360499 15712775 := bstep (se 1 (by rfl) ⟨11784581, by rfl⟩ : syracuseStep 15712775 = 23569163) B23569163
theorem B1532443 : Blo 1360499 1532443 := bstep (se 1 (by rfl) ⟨1149332, by rfl⟩ : syracuseStep 1532443 = 2298665) B2298665
theorem B3064481 : Blo 1360499 3064481 := bstep (se 2 (by rfl) ⟨1149180, by rfl⟩ : syracuseStep 3064481 = 2298361) B2298361
theorem B1360551 : Blo 1360499 1360551 := bstep (se 1 (by rfl) ⟨1020413, by rfl⟩ : syracuseStep 1360551 = 2040827) B2040827
theorem B13091503 : Blo 1360499 13091503 := bstep (se 1 (by rfl) ⟨9818627, by rfl⟩ : syracuseStep 13091503 = 19637255) B19637255
theorem B1360591 : Blo 1360499 1360591 := bstep (se 1 (by rfl) ⟨1020443, by rfl⟩ : syracuseStep 1360591 = 2040887) B2040887
theorem B1532623 : Blo 1360499 1532623 := bstep (se 1 (by rfl) ⟨1149467, by rfl⟩ : syracuseStep 1532623 = 2298935) B2298935
theorem B1360671 : Blo 1360499 1360671 := bstep (se 1 (by rfl) ⟨1020503, by rfl⟩ : syracuseStep 1360671 = 2041007) B2041007
theorem B8282989 : Blo 1360499 8282989 := bstep (se 3 (by rfl) ⟨1553060, by rfl⟩ : syracuseStep 8282989 = 3106121) B3106121
theorem B3064841 : Blo 1360499 3064841 := bstep (se 2 (by rfl) ⟨1149315, by rfl⟩ : syracuseStep 3064841 = 2298631) B2298631
theorem B20964395 : Blo 1360499 20964395 := bstep (se 1 (by rfl) ⟨15723296, by rfl⟩ : syracuseStep 20964395 = 31446593) B31446593
theorem B1360943 : Blo 1360499 1360943 := bstep (se 1 (by rfl) ⟨1020707, by rfl⟩ : syracuseStep 1360943 = 2041415) B2041415
theorem B3064895 : Blo 1360499 3064895 := bstep (se 1 (by rfl) ⟨2298671, by rfl⟩ : syracuseStep 3064895 = 4597343) B4597343
theorem B9806953 : Blo 1360499 9806953 := bstep (se 2 (by rfl) ⟨3677607, by rfl⟩ : syracuseStep 9806953 = 7355215) B7355215
theorem B3359855 : Blo 1360499 3359855 := bstep (se 1 (by rfl) ⟨2519891, by rfl⟩ : syracuseStep 3359855 = 5039783) B5039783
theorem B1361007 : Blo 1360499 1361007 := bstep (se 1 (by rfl) ⟨1020755, by rfl⟩ : syracuseStep 1361007 = 2041511) B2041511
theorem B2040953 : Blo 1360499 2040953 := bstep (se 2 (by rfl) ⟨765357, by rfl⟩ : syracuseStep 2040953 = 1530715) B1530715
theorem B4596857 : Blo 1360499 4596857 := bstep (se 2 (by rfl) ⟨1723821, by rfl⟩ : syracuseStep 4596857 = 3447643) B3447643
theorem B1361063 : Blo 1360499 1361063 := bstep (se 1 (by rfl) ⟨1020797, by rfl⟩ : syracuseStep 1361063 = 2041595) B2041595
theorem B1361087 : Blo 1360499 1361087 := bstep (se 1 (by rfl) ⟨1020815, by rfl⟩ : syracuseStep 1361087 = 2041631) B2041631
theorem B13075663 : Blo 1360499 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B1361119 : Blo 1360499 1361119 := bstep (se 1 (by rfl) ⟨1020839, by rfl⟩ : syracuseStep 1361119 = 2041679) B2041679
theorem B9315595 : Blo 1360499 9315595 := bstep (se 1 (by rfl) ⟨6986696, by rfl⟩ : syracuseStep 9315595 = 13973393) B13973393
theorem B1361199 : Blo 1360499 1361199 := bstep (se 1 (by rfl) ⟨1020899, by rfl⟩ : syracuseStep 1361199 = 2041799) B2041799
theorem B1361435 : Blo 1360499 1361435 := bstep (se 1 (by rfl) ⟨1021076, by rfl⟩ : syracuseStep 1361435 = 2042153) B2042153
theorem B1361439 : Blo 1360499 1361439 := bstep (se 1 (by rfl) ⟨1021079, by rfl⟩ : syracuseStep 1361439 = 2042159) B2042159
theorem B3270215 : Blo 1360499 3270215 := bstep (se 1 (by rfl) ⟨2452661, by rfl⟩ : syracuseStep 3270215 = 4905323) B4905323
theorem B1361599 : Blo 1360499 1361599 := bstep (se 1 (by rfl) ⟨1021199, by rfl⟩ : syracuseStep 1361599 = 2042399) B2042399
theorem B1722151 : Blo 1360499 1722151 := bstep (se 1 (by rfl) ⟨1291613, by rfl⟩ : syracuseStep 1722151 = 2583227) B2583227
theorem B13076279 : Blo 1360499 13076279 := bstep (se 1 (by rfl) ⟨9807209, by rfl⟩ : syracuseStep 13076279 = 19614419) B19614419
theorem B1361855 : Blo 1360499 1361855 := bstep (se 1 (by rfl) ⟨1021391, by rfl⟩ : syracuseStep 1361855 = 2042783) B2042783
theorem B2041823 : Blo 1360499 2041823 := bstep (se 1 (by rfl) ⟨1531367, by rfl⟩ : syracuseStep 2041823 = 3062735) B3062735
theorem B1361887 : Blo 1360499 1361887 := bstep (se 1 (by rfl) ⟨1021415, by rfl⟩ : syracuseStep 1361887 = 2042831) B2042831
theorem B2041835 : Blo 1360499 2041835 := bstep (se 1 (by rfl) ⟨1531376, by rfl⟩ : syracuseStep 2041835 = 3062753) B3062753
theorem B2041883 : Blo 1360499 2041883 := bstep (se 1 (by rfl) ⟨1531412, by rfl⟩ : syracuseStep 2041883 = 3062825) B3062825
theorem B1361947 : Blo 1360499 1361947 := bstep (se 1 (by rfl) ⟨1021460, by rfl⟩ : syracuseStep 1361947 = 2042921) B2042921
theorem B1361951 : Blo 1360499 1361951 := bstep (se 1 (by rfl) ⟨1021463, by rfl⟩ : syracuseStep 1361951 = 2042927) B2042927
theorem B1361967 : Blo 1360499 1361967 := bstep (se 1 (by rfl) ⟨1021475, by rfl⟩ : syracuseStep 1361967 = 2042951) B2042951
theorem B20949137 : Blo 1360499 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B1362143 : Blo 1360499 1362143 := bstep (se 1 (by rfl) ⟨1021607, by rfl⟩ : syracuseStep 1362143 = 2043215) B2043215
theorem B1362203 : Blo 1360499 1362203 := bstep (se 1 (by rfl) ⟨1021652, by rfl⟩ : syracuseStep 1362203 = 2043305) B2043305
theorem B6629687 : Blo 1360499 6629687 := bstep (se 1 (by rfl) ⟨4972265, by rfl⟩ : syracuseStep 6629687 = 9944531) B9944531
theorem B1722703 : Blo 1360499 1722703 := bstep (se 1 (by rfl) ⟨1292027, by rfl⟩ : syracuseStep 1722703 = 2584055) B2584055
theorem B1362303 : Blo 1360499 1362303 := bstep (se 1 (by rfl) ⟨1021727, by rfl⟩ : syracuseStep 1362303 = 2043455) B2043455
theorem B2042249 : Blo 1360499 2042249 := bstep (se 2 (by rfl) ⟨765843, by rfl⟩ : syracuseStep 2042249 = 1531687) B1531687
theorem B1362479 : Blo 1360499 1362479 := bstep (se 1 (by rfl) ⟨1021859, by rfl⟩ : syracuseStep 1362479 = 2043719) B2043719
theorem B15510203 : Blo 1360499 15510203 := bstep (se 1 (by rfl) ⟨11632652, by rfl⟩ : syracuseStep 15510203 = 23265305) B23265305
theorem B8276779 : Blo 1360499 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B1723447 : Blo 1360499 1723447 := bstep (se 1 (by rfl) ⟨1292585, by rfl⟩ : syracuseStep 1723447 = 2585171) B2585171
theorem B2182199 : Blo 1360499 2182199 := bstep (se 1 (by rfl) ⟨1636649, by rfl⟩ : syracuseStep 2182199 = 3273299) B3273299
theorem B4361323 : Blo 1360499 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B5819539 : Blo 1360499 5819539 := bstep (se 1 (by rfl) ⟨4364654, by rfl⟩ : syracuseStep 5819539 = 8729309) B8729309
theorem B5172407 : Blo 1360499 5172407 := bstep (se 1 (by rfl) ⟨3879305, by rfl⟩ : syracuseStep 5172407 = 7758611) B7758611
theorem B11635933 : Blo 1360499 11635933 := bstep (se 3 (by rfl) ⟨2181737, by rfl⟩ : syracuseStep 11635933 = 4363475) B4363475
theorem B2043191 : Blo 1360499 2043191 := bstep (se 1 (by rfl) ⟨1532393, by rfl⟩ : syracuseStep 2043191 = 3064787) B3064787
theorem B3444059 : Blo 1360499 3444059 := bstep (se 1 (by rfl) ⟨2583044, by rfl⟩ : syracuseStep 3444059 = 5166089) B5166089
theorem B3444079 : Blo 1360499 3444079 := bstep (se 1 (by rfl) ⟨2583059, by rfl⟩ : syracuseStep 3444079 = 5166119) B5166119
theorem B7359905 : Blo 1360499 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B2043359 : Blo 1360499 2043359 := bstep (se 1 (by rfl) ⟨1532519, by rfl⟩ : syracuseStep 2043359 = 3065039) B3065039
theorem B29429243 : Blo 1360499 29429243 := bstep (se 1 (by rfl) ⟨22071932, by rfl⟩ : syracuseStep 29429243 = 44143865) B44143865
theorem B3878543 : Blo 1360499 3878543 := bstep (se 1 (by rfl) ⟨2908907, by rfl⟩ : syracuseStep 3878543 = 5817815) B5817815
theorem B5172893 : Blo 1360499 5172893 := bstep (se 3 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 5172893 = 1939835) B1939835
theorem B2043575 : Blo 1360499 2043575 := bstep (se 1 (by rfl) ⟨1532681, by rfl⟩ : syracuseStep 2043575 = 3065363) B3065363
theorem B5517193 : Blo 1360499 5517193 := bstep (se 2 (by rfl) ⟨2068947, by rfl⟩ : syracuseStep 5517193 = 4137895) B4137895
theorem B2584457 : Blo 1360499 2584457 := bstep (se 2 (by rfl) ⟨969171, by rfl⟩ : syracuseStep 2584457 = 1938343) B1938343
theorem B3444839 : Blo 1360499 3444839 := bstep (se 1 (by rfl) ⟨2583629, by rfl⟩ : syracuseStep 3444839 = 5167259) B5167259
theorem B2297963 : Blo 1360499 2297963 := bstep (se 1 (by rfl) ⟨1723472, by rfl⟩ : syracuseStep 2297963 = 3446945) B3446945
theorem B6213755 : Blo 1360499 6213755 := bstep (se 1 (by rfl) ⟨4660316, by rfl⟩ : syracuseStep 6213755 = 9320633) B9320633
theorem B10342565 : Blo 1360499 10342565 := bstep (se 4 (by rfl) ⟨969615, by rfl⟩ : syracuseStep 10342565 = 1939231) B1939231
theorem B5812499 : Blo 1360499 5812499 := bstep (se 1 (by rfl) ⟨4359374, by rfl⟩ : syracuseStep 5812499 = 8718749) B8718749
theorem B5894785 : Blo 1360499 5894785 := bstep (se 2 (by rfl) ⟨2210544, by rfl⟩ : syracuseStep 5894785 = 4421089) B4421089
theorem B44176033 : Blo 1360499 44176033 := bstep (se 2 (by rfl) ⟨16566012, by rfl⟩ : syracuseStep 44176033 = 33132025) B33132025
theorem B26538671 : Blo 1360499 26538671 := bstep (se 1 (by rfl) ⟨19904003, by rfl⟩ : syracuseStep 26538671 = 39808007) B39808007
theorem B2585353 : Blo 1360499 2585353 := bstep (se 2 (by rfl) ⟨969507, by rfl⟩ : syracuseStep 2585353 = 1939015) B1939015
theorem B8721209 : Blo 1360499 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B39261023 : Blo 1360499 39261023 := bstep (se 1 (by rfl) ⟨29445767, by rfl⟩ : syracuseStep 39261023 = 58891535) B58891535
theorem B4903835 : Blo 1360499 4903835 := bstep (se 1 (by rfl) ⟨3677876, by rfl⟩ : syracuseStep 4903835 = 7355753) B7355753
theorem B43660241 : Blo 1360499 43660241 := bstep (se 2 (by rfl) ⟨16372590, by rfl⟩ : syracuseStep 43660241 = 32745181) B32745181
theorem B8721391 : Blo 1360499 8721391 := bstep (se 1 (by rfl) ⟨6541043, by rfl⟩ : syracuseStep 8721391 = 13082087) B13082087
theorem B2946041 : Blo 1360499 2946041 := bstep (se 2 (by rfl) ⟨1104765, by rfl⟩ : syracuseStep 2946041 = 2209531) B2209531
theorem B5166575 : Blo 1360499 5166575 := bstep (se 1 (by rfl) ⟨3874931, by rfl⟩ : syracuseStep 5166575 = 7749863) B7749863
theorem B1635823 : Blo 1360499 1635823 := bstep (se 1 (by rfl) ⟨1226867, by rfl⟩ : syracuseStep 1635823 = 2453735) B2453735
theorem B3061583 : Blo 1360499 3061583 := bstep (se 1 (by rfl) ⟨2296187, by rfl⟩ : syracuseStep 3061583 = 4592375) B4592375
theorem B3446651 : Blo 1360499 3446651 := bstep (se 1 (by rfl) ⟨2584988, by rfl⟩ : syracuseStep 3446651 = 5169977) B5169977
theorem B5977981 : Blo 1360499 5977981 := bstep (se 3 (by rfl) ⟨1120871, by rfl⟩ : syracuseStep 5977981 = 2241743) B2241743
theorem B48486277 : Blo 1360499 48486277 := bstep (se 4 (by rfl) ⟨4545588, by rfl⟩ : syracuseStep 48486277 = 9091177) B9091177
theorem B3061943 : Blo 1360499 3061943 := bstep (se 1 (by rfl) ⟨2296457, by rfl⟩ : syracuseStep 3061943 = 4592915) B4592915
theorem B4659551 : Blo 1360499 4659551 := bstep (se 1 (by rfl) ⟨3494663, by rfl⟩ : syracuseStep 4659551 = 6989327) B6989327
theorem B41908589 : Blo 1360499 41908589 := bstep (se 3 (by rfl) ⟨7857860, by rfl⟩ : syracuseStep 41908589 = 15715721) B15715721
theorem B5167547 : Blo 1360499 5167547 := bstep (se 1 (by rfl) ⟨3875660, by rfl⟩ : syracuseStep 5167547 = 7751321) B7751321
theorem B3062303 : Blo 1360499 3062303 := bstep (se 1 (by rfl) ⟨2296727, by rfl⟩ : syracuseStep 3062303 = 4593455) B4593455
theorem B3062537 : Blo 1360499 3062537 := bstep (se 2 (by rfl) ⟨1148451, by rfl⟩ : syracuseStep 3062537 = 2296903) B2296903
theorem B7748723 : Blo 1360499 7748723 := bstep (se 1 (by rfl) ⟨5811542, by rfl⟩ : syracuseStep 7748723 = 11623085) B11623085
theorem B2907343 : Blo 1360499 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B1531111 : Blo 1360499 1531111 := bstep (se 1 (by rfl) ⟨1148333, by rfl⟩ : syracuseStep 1531111 = 2296667) B2296667
theorem B3063113 : Blo 1360499 3063113 := bstep (se 2 (by rfl) ⟨1148667, by rfl⟩ : syracuseStep 3063113 = 2297335) B2297335
theorem B10337705 : Blo 1360499 10337705 := bstep (se 2 (by rfl) ⟨3876639, by rfl⟩ : syracuseStep 10337705 = 7753279) B7753279
theorem B6897149 : Blo 1360499 6897149 := bstep (se 3 (by rfl) ⟨1293215, by rfl⟩ : syracuseStep 6897149 = 2586431) B2586431
theorem B5168731 : Blo 1360499 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B11624147 : Blo 1360499 11624147 := bstep (se 1 (by rfl) ⟨8718110, by rfl⟩ : syracuseStep 11624147 = 17436221) B17436221
theorem B3063527 : Blo 1360499 3063527 := bstep (se 1 (by rfl) ⟨2297645, by rfl⟩ : syracuseStep 3063527 = 4595291) B4595291
theorem B4595453 : Blo 1360499 4595453 := bstep (se 3 (by rfl) ⟨861647, by rfl⟩ : syracuseStep 4595453 = 1723295) B1723295
theorem B1531759 : Blo 1360499 1531759 := bstep (se 1 (by rfl) ⟨1148819, by rfl⟩ : syracuseStep 1531759 = 2297639) B2297639
theorem B5169035 : Blo 1360499 5169035 := bstep (se 1 (by rfl) ⟨3876776, by rfl⟩ : syracuseStep 5169035 = 7753553) B7753553
theorem B2760695 : Blo 1360499 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B1531975 : Blo 1360499 1531975 := bstep (se 1 (by rfl) ⟨1148981, by rfl⟩ : syracuseStep 1531975 = 2297963) B2297963
theorem B26174015 : Blo 1360499 26174015 := bstep (se 1 (by rfl) ⟨19630511, by rfl⟩ : syracuseStep 26174015 = 39261023) B39261023
theorem B29106827 : Blo 1360499 29106827 := bstep (se 1 (by rfl) ⟨21830120, by rfl⟩ : syracuseStep 29106827 = 43660241) B43660241
theorem B13976263 : Blo 1360499 13976263 := bstep (se 1 (by rfl) ⟨10482197, by rfl⟩ : syracuseStep 13976263 = 20964395) B20964395
theorem B15499997 : Blo 1360499 15499997 := bstep (se 3 (by rfl) ⟨2906249, by rfl⟩ : syracuseStep 15499997 = 5812499) B5812499
theorem B1360635 : Blo 1360499 1360635 := bstep (se 1 (by rfl) ⟨1020476, by rfl⟩ : syracuseStep 1360635 = 2040953) B2040953
theorem B3064571 : Blo 1360499 3064571 := bstep (se 1 (by rfl) ⟨2298428, by rfl⟩ : syracuseStep 3064571 = 4596857) B4596857
theorem B58901377 : Blo 1360499 58901377 := bstep (se 2 (by rfl) ⟨22088016, by rfl⟩ : syracuseStep 58901377 = 44176033) B44176033
theorem B2180143 : Blo 1360499 2180143 := bstep (se 1 (by rfl) ⟨1635107, by rfl⟩ : syracuseStep 2180143 = 3270215) B3270215
theorem B11035705 : Blo 1360499 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B11043985 : Blo 1360499 11043985 := bstep (se 2 (by rfl) ⟨4141494, by rfl⟩ : syracuseStep 11043985 = 8282989) B8282989
theorem B8717519 : Blo 1360499 8717519 := bstep (se 1 (by rfl) ⟨6538139, by rfl⟩ : syracuseStep 8717519 = 13076279) B13076279
theorem B2041055 : Blo 1360499 2041055 := bstep (se 1 (by rfl) ⟨1530791, by rfl⟩ : syracuseStep 2041055 = 3061583) B3061583
theorem B1361215 : Blo 1360499 1361215 := bstep (se 1 (by rfl) ⟨1020911, by rfl⟩ : syracuseStep 1361215 = 2041823) B2041823
theorem B1361223 : Blo 1360499 1361223 := bstep (se 1 (by rfl) ⟨1020917, by rfl⟩ : syracuseStep 1361223 = 2041835) B2041835
theorem B1361255 : Blo 1360499 1361255 := bstep (se 1 (by rfl) ⟨1020941, by rfl⟩ : syracuseStep 1361255 = 2041883) B2041883
theorem B2041295 : Blo 1360499 2041295 := bstep (se 1 (by rfl) ⟨1530971, by rfl⟩ : syracuseStep 2041295 = 3061943) B3061943
theorem B13075937 : Blo 1360499 13075937 := bstep (se 2 (by rfl) ⟨4903476, by rfl⟩ : syracuseStep 13075937 = 9806953) B9806953
theorem B7759385 : Blo 1360499 7759385 := bstep (se 2 (by rfl) ⟨2909769, by rfl⟩ : syracuseStep 7759385 = 5819539) B5819539
theorem B3106367 : Blo 1360499 3106367 := bstep (se 1 (by rfl) ⟨2329775, by rfl⟩ : syracuseStep 3106367 = 4659551) B4659551
theorem B1361499 : Blo 1360499 1361499 := bstep (se 1 (by rfl) ⟨1021124, by rfl⟩ : syracuseStep 1361499 = 2042249) B2042249
theorem B17434217 : Blo 1360499 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B2041481 : Blo 1360499 2041481 := bstep (se 2 (by rfl) ⟨765555, by rfl⟩ : syracuseStep 2041481 = 1531111) B1531111
theorem B12420793 : Blo 1360499 12420793 := bstep (se 2 (by rfl) ⟨4657797, by rfl⟩ : syracuseStep 12420793 = 9315595) B9315595
theorem B2041535 : Blo 1360499 2041535 := bstep (se 1 (by rfl) ⟨1531151, by rfl⟩ : syracuseStep 2041535 = 3062303) B3062303
theorem B10340135 : Blo 1360499 10340135 := bstep (se 1 (by rfl) ⟨7755101, by rfl⟩ : syracuseStep 10340135 = 15510203) B15510203
theorem B2041691 : Blo 1360499 2041691 := bstep (se 1 (by rfl) ⟨1531268, by rfl⟩ : syracuseStep 2041691 = 3062537) B3062537
theorem B2181097 : Blo 1360499 2181097 := bstep (se 2 (by rfl) ⟨817911, by rfl⟩ : syracuseStep 2181097 = 1635823) B1635823
theorem B6891641 : Blo 1360499 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B1362127 : Blo 1360499 1362127 := bstep (se 1 (by rfl) ⟨1021595, by rfl⟩ : syracuseStep 1362127 = 2043191) B2043191
theorem B2042075 : Blo 1360499 2042075 := bstep (se 1 (by rfl) ⟨1531556, by rfl⟩ : syracuseStep 2042075 = 3063113) B3063113
theorem B2296039 : Blo 1360499 2296039 := bstep (se 1 (by rfl) ⟨1722029, by rfl⟩ : syracuseStep 2296039 = 3444059) B3444059
theorem B6891803 : Blo 1360499 6891803 := bstep (se 1 (by rfl) ⟨5168852, by rfl⟩ : syracuseStep 6891803 = 10337705) B10337705
theorem B1362239 : Blo 1360499 1362239 := bstep (se 1 (by rfl) ⟨1021679, by rfl⟩ : syracuseStep 1362239 = 2043359) B2043359
theorem B4598099 : Blo 1360499 4598099 := bstep (se 1 (by rfl) ⟨3448574, by rfl⟩ : syracuseStep 4598099 = 6897149) B6897149
theorem B2296201 : Blo 1360499 2296201 := bstep (se 2 (by rfl) ⟨861075, by rfl⟩ : syracuseStep 2296201 = 1722151) B1722151
theorem B13076893 : Blo 1360499 13076893 := bstep (se 3 (by rfl) ⟨2451917, by rfl⟩ : syracuseStep 13076893 = 4903835) B4903835
theorem B1362383 : Blo 1360499 1362383 := bstep (se 1 (by rfl) ⟨1021787, by rfl⟩ : syracuseStep 1362383 = 2043575) B2043575
theorem B2042345 : Blo 1360499 2042345 := bstep (se 2 (by rfl) ⟨765879, by rfl⟩ : syracuseStep 2042345 = 1531759) B1531759
theorem B2042351 : Blo 1360499 2042351 := bstep (se 1 (by rfl) ⟨1531763, by rfl⟩ : syracuseStep 2042351 = 3063527) B3063527
theorem B1722971 : Blo 1360499 1722971 := bstep (se 1 (by rfl) ⟨1292228, by rfl⟩ : syracuseStep 1722971 = 2584457) B2584457
theorem B2296559 : Blo 1360499 2296559 := bstep (se 1 (by rfl) ⟨1722419, by rfl⟩ : syracuseStep 2296559 = 3444839) B3444839
theorem B2042663 : Blo 1360499 2042663 := bstep (se 1 (by rfl) ⟨1531997, by rfl⟩ : syracuseStep 2042663 = 3063995) B3063995
theorem B5819197 : Blo 1360499 5819197 := bstep (se 3 (by rfl) ⟨1091099, by rfl⟩ : syracuseStep 5819197 = 2182199) B2182199
theorem B2042735 : Blo 1360499 2042735 := bstep (se 1 (by rfl) ⟨1532051, by rfl⟩ : syracuseStep 2042735 = 3064103) B3064103
theorem B2296937 : Blo 1360499 2296937 := bstep (se 2 (by rfl) ⟨861351, by rfl⟩ : syracuseStep 2296937 = 1722703) B1722703
theorem B2042987 : Blo 1360499 2042987 := bstep (se 1 (by rfl) ⟨1532240, by rfl⟩ : syracuseStep 2042987 = 3064481) B3064481
theorem B2043227 : Blo 1360499 2043227 := bstep (se 1 (by rfl) ⟨1532420, by rfl⟩ : syracuseStep 2043227 = 3064841) B3064841
theorem B2043257 : Blo 1360499 2043257 := bstep (se 2 (by rfl) ⟨766221, by rfl⟩ : syracuseStep 2043257 = 1532443) B1532443
theorem B2043263 : Blo 1360499 2043263 := bstep (se 1 (by rfl) ⟨1532447, by rfl⟩ : syracuseStep 2043263 = 3064895) B3064895
theorem B2239903 : Blo 1360499 2239903 := bstep (se 1 (by rfl) ⟨1679927, by rfl⟩ : syracuseStep 2239903 = 3359855) B3359855
theorem B7859713 : Blo 1360499 7859713 := bstep (se 2 (by rfl) ⟨2947392, by rfl⟩ : syracuseStep 7859713 = 5894785) B5894785
theorem B2043497 : Blo 1360499 2043497 := bstep (se 2 (by rfl) ⟨766311, by rfl⟩ : syracuseStep 2043497 = 1532623) B1532623
theorem B3444383 : Blo 1360499 3444383 := bstep (se 1 (by rfl) ⟨2583287, by rfl⟩ : syracuseStep 3444383 = 5166575) B5166575
theorem B2297767 : Blo 1360499 2297767 := bstep (se 1 (by rfl) ⟨1723325, by rfl⟩ : syracuseStep 2297767 = 3446651) B3446651
theorem B11628521 : Blo 1360499 11628521 := bstep (se 2 (by rfl) ⟨4360695, by rfl⟩ : syracuseStep 11628521 = 8721391) B8721391
theorem B31461365 : Blo 1360499 31461365 := bstep (se 5 (by rfl) ⟨1474751, by rfl⟩ : syracuseStep 31461365 = 2949503) B2949503
theorem B2297929 : Blo 1360499 2297929 := bstep (se 2 (by rfl) ⟨861723, by rfl⟩ : syracuseStep 2297929 = 1723447) B1723447
theorem B4419791 : Blo 1360499 4419791 := bstep (se 1 (by rfl) ⟨3314843, by rfl⟩ : syracuseStep 4419791 = 6629687) B6629687
theorem B27939059 : Blo 1360499 27939059 := bstep (se 1 (by rfl) ⟨20954294, by rfl⟩ : syracuseStep 27939059 = 41908589) B41908589
theorem B3445031 : Blo 1360499 3445031 := bstep (se 1 (by rfl) ⟨2583773, by rfl⟩ : syracuseStep 3445031 = 5167547) B5167547
theorem B4592105 : Blo 1360499 4592105 := bstep (se 2 (by rfl) ⟨1722039, by rfl⟩ : syracuseStep 4592105 = 3444079) B3444079
theorem B258593477 : Blo 1360499 258593477 := bstep (se 4 (by rfl) ⟨24243138, by rfl⟩ : syracuseStep 258593477 = 48486277) B48486277
theorem B5165815 : Blo 1360499 5165815 := bstep (se 1 (by rfl) ⟨3874361, by rfl⟩ : syracuseStep 5165815 = 7748723) B7748723
theorem B2585695 : Blo 1360499 2585695 := bstep (se 1 (by rfl) ⟨1939271, by rfl⟩ : syracuseStep 2585695 = 3878543) B3878543
theorem B3446023 : Blo 1360499 3446023 := bstep (se 1 (by rfl) ⟨2584517, by rfl⟩ : syracuseStep 3446023 = 5169035) B5169035
theorem B1840463 : Blo 1360499 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B4142503 : Blo 1360499 4142503 := bstep (se 1 (by rfl) ⟨3106877, by rfl⟩ : syracuseStep 4142503 = 6213755) B6213755
theorem B6895043 : Blo 1360499 6895043 := bstep (se 1 (by rfl) ⟨5171282, by rfl⟩ : syracuseStep 6895043 = 10342565) B10342565
theorem B10475183 : Blo 1360499 10475183 := bstep (se 1 (by rfl) ⟨7856387, by rfl⟩ : syracuseStep 10475183 = 15712775) B15712775
theorem B17692447 : Blo 1360499 17692447 := bstep (se 1 (by rfl) ⟨13269335, by rfl⟩ : syracuseStep 17692447 = 26538671) B26538671
theorem B1964027 : Blo 1360499 1964027 := bstep (se 1 (by rfl) ⟨1473020, by rfl⟩ : syracuseStep 1964027 = 2946041) B2946041
theorem B17455337 : Blo 1360499 17455337 := bstep (se 2 (by rfl) ⟨6545751, by rfl⟩ : syracuseStep 17455337 = 13091503) B13091503
theorem B3447137 : Blo 1360499 3447137 := bstep (se 2 (by rfl) ⟨1292676, by rfl⟩ : syracuseStep 3447137 = 2585353) B2585353
theorem B15505829 : Blo 1360499 15505829 := bstep (se 4 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 15505829 = 2907343) B2907343
theorem B13966091 : Blo 1360499 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B5815097 : Blo 1360499 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B15514577 : Blo 1360499 15514577 := bstep (se 2 (by rfl) ⟨5817966, by rfl⟩ : syracuseStep 15514577 = 11635933) B11635933
theorem B31882565 : Blo 1360499 31882565 := bstep (se 4 (by rfl) ⟨2988990, by rfl⟩ : syracuseStep 31882565 = 5977981) B5977981
theorem B3448271 : Blo 1360499 3448271 := bstep (se 1 (by rfl) ⟨2586203, by rfl⟩ : syracuseStep 3448271 = 5172407) B5172407
theorem B23256557 : Blo 1360499 23256557 := bstep (se 3 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 23256557 = 8721209) B8721209
theorem B4906603 : Blo 1360499 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B19619495 : Blo 1360499 19619495 := bstep (se 1 (by rfl) ⟨14714621, by rfl⟩ : syracuseStep 19619495 = 29429243) B29429243
theorem B3448595 : Blo 1360499 3448595 := bstep (se 1 (by rfl) ⟨2586446, by rfl⟩ : syracuseStep 3448595 = 5172893) B5172893
theorem B7749431 : Blo 1360499 7749431 := bstep (se 1 (by rfl) ⟨5812073, by rfl⟩ : syracuseStep 7749431 = 11624147) B11624147
theorem B3063635 : Blo 1360499 3063635 := bstep (se 1 (by rfl) ⟨2297726, by rfl⟩ : syracuseStep 3063635 = 4595453) B4595453
theorem B7356257 : Blo 1360499 7356257 := bstep (se 2 (by rfl) ⟨2758596, by rfl⟩ : syracuseStep 7356257 = 5517193) B5517193
theorem B3063905 : Blo 1360499 3063905 := bstep (se 2 (by rfl) ⟨1148964, by rfl⟩ : syracuseStep 3063905 = 2297929) B2297929
theorem B17449343 : Blo 1360499 17449343 := bstep (se 1 (by rfl) ⟨13087007, by rfl⟩ : syracuseStep 17449343 = 26174015) B26174015
theorem B1360703 : Blo 1360499 1360703 := bstep (se 1 (by rfl) ⟨1020527, by rfl⟩ : syracuseStep 1360703 = 2041055) B2041055
theorem B4596695 : Blo 1360499 4596695 := bstep (se 1 (by rfl) ⟨3447521, by rfl⟩ : syracuseStep 4596695 = 6895043) B6895043
theorem B1360863 : Blo 1360499 1360863 := bstep (se 1 (by rfl) ⟨1020647, by rfl⟩ : syracuseStep 1360863 = 2041295) B2041295
theorem B8717291 : Blo 1360499 8717291 := bstep (se 1 (by rfl) ⟨6537968, by rfl⟩ : syracuseStep 8717291 = 13075937) B13075937
theorem B7758929 : Blo 1360499 7758929 := bstep (se 2 (by rfl) ⟨2909598, by rfl⟩ : syracuseStep 7758929 = 5819197) B5819197
theorem B1360987 : Blo 1360499 1360987 := bstep (se 1 (by rfl) ⟨1020740, by rfl⟩ : syracuseStep 1360987 = 2041481) B2041481
theorem B1361023 : Blo 1360499 1361023 := bstep (se 1 (by rfl) ⟨1020767, by rfl⟩ : syracuseStep 1361023 = 2041535) B2041535
theorem B1361127 : Blo 1360499 1361127 := bstep (se 1 (by rfl) ⟨1020845, by rfl⟩ : syracuseStep 1361127 = 2041691) B2041691
theorem B14714273 : Blo 1360499 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B1361383 : Blo 1360499 1361383 := bstep (se 1 (by rfl) ⟨1021037, by rfl⟩ : syracuseStep 1361383 = 2042075) B2042075
theorem B3065399 : Blo 1360499 3065399 := bstep (se 1 (by rfl) ⟨2299049, by rfl⟩ : syracuseStep 3065399 = 4598099) B4598099
theorem B1361563 : Blo 1360499 1361563 := bstep (se 1 (by rfl) ⟨1021172, by rfl⟩ : syracuseStep 1361563 = 2042345) B2042345
theorem B1361567 : Blo 1360499 1361567 := bstep (se 1 (by rfl) ⟨1021175, by rfl⟩ : syracuseStep 1361567 = 2042351) B2042351
theorem B1361775 : Blo 1360499 1361775 := bstep (se 1 (by rfl) ⟨1021331, by rfl⟩ : syracuseStep 1361775 = 2042663) B2042663
theorem B3876731 : Blo 1360499 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B5523337 : Blo 1360499 5523337 := bstep (se 2 (by rfl) ⟨2071251, by rfl⟩ : syracuseStep 5523337 = 4142503) B4142503
theorem B1361823 : Blo 1360499 1361823 := bstep (se 1 (by rfl) ⟨1021367, by rfl⟩ : syracuseStep 1361823 = 2042735) B2042735
theorem B10479617 : Blo 1360499 10479617 := bstep (se 2 (by rfl) ⟨3929856, by rfl⟩ : syracuseStep 10479617 = 7859713) B7859713
theorem B1361991 : Blo 1360499 1361991 := bstep (se 1 (by rfl) ⟨1021493, by rfl⟩ : syracuseStep 1361991 = 2042987) B2042987
theorem B1362151 : Blo 1360499 1362151 := bstep (se 1 (by rfl) ⟨1021613, by rfl⟩ : syracuseStep 1362151 = 2043227) B2043227
theorem B1362171 : Blo 1360499 1362171 := bstep (se 1 (by rfl) ⟨1021628, by rfl⟩ : syracuseStep 1362171 = 2043257) B2043257
theorem B1362175 : Blo 1360499 1362175 := bstep (se 1 (by rfl) ⟨1021631, by rfl⟩ : syracuseStep 1362175 = 2043263) B2043263
theorem B1362331 : Blo 1360499 1362331 := bstep (se 1 (by rfl) ⟨1021748, by rfl⟩ : syracuseStep 1362331 = 2043497) B2043497
theorem B2296255 : Blo 1360499 2296255 := bstep (se 1 (by rfl) ⟨1722191, by rfl⟩ : syracuseStep 2296255 = 3444383) B3444383
theorem B2042423 : Blo 1360499 2042423 := bstep (se 1 (by rfl) ⟨1531817, by rfl⟩ : syracuseStep 2042423 = 3063635) B3063635
theorem B7752347 : Blo 1360499 7752347 := bstep (se 1 (by rfl) ⟨5814260, by rfl⟩ : syracuseStep 7752347 = 11628521) B11628521
theorem B5237405 : Blo 1360499 5237405 := bstep (se 3 (by rfl) ⟨982013, by rfl⟩ : syracuseStep 5237405 = 1964027) B1964027
theorem B20974243 : Blo 1360499 20974243 := bstep (se 1 (by rfl) ⟨15730682, by rfl⟩ : syracuseStep 20974243 = 31461365) B31461365
theorem B2042633 : Blo 1360499 2042633 := bstep (se 2 (by rfl) ⟨765987, by rfl⟩ : syracuseStep 2042633 = 1531975) B1531975
theorem B2296687 : Blo 1360499 2296687 := bstep (se 1 (by rfl) ⟨1722515, by rfl⟩ : syracuseStep 2296687 = 3445031) B3445031
theorem B10333331 : Blo 1360499 10333331 := bstep (se 1 (by rfl) ⟨7749998, by rfl⟩ : syracuseStep 10333331 = 15499997) B15499997
theorem B2043047 : Blo 1360499 2043047 := bstep (se 1 (by rfl) ⟨1532285, by rfl⟩ : syracuseStep 2043047 = 3064571) B3064571
theorem B17435857 : Blo 1360499 17435857 := bstep (se 2 (by rfl) ⟨6538446, by rfl⟩ : syracuseStep 17435857 = 13076893) B13076893
theorem B5811679 : Blo 1360499 5811679 := bstep (se 1 (by rfl) ⟨4358759, by rfl⟩ : syracuseStep 5811679 = 8717519) B8717519
theorem B19631605 : Blo 1360499 19631605 := bstep (se 5 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 19631605 = 1840463) B1840463
theorem B5172923 : Blo 1360499 5172923 := bstep (se 1 (by rfl) ⟨3879692, by rfl⟩ : syracuseStep 5172923 = 7759385) B7759385
theorem B6893423 : Blo 1360499 6893423 := bstep (se 1 (by rfl) ⟨5170067, by rfl⟩ : syracuseStep 6893423 = 10340135) B10340135
theorem B11636891 : Blo 1360499 11636891 := bstep (se 1 (by rfl) ⟨8727668, by rfl⟩ : syracuseStep 11636891 = 17455337) B17455337
theorem B14725313 : Blo 1360499 14725313 := bstep (se 2 (by rfl) ⟨5521992, by rfl⟩ : syracuseStep 14725313 = 11043985) B11043985
theorem B2298091 : Blo 1360499 2298091 := bstep (se 1 (by rfl) ⟨1723568, by rfl⟩ : syracuseStep 2298091 = 3447137) B3447137
theorem B9310727 : Blo 1360499 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B689582605 : Blo 1360499 689582605 := bstep (se 3 (by rfl) ⟨129296738, by rfl⟩ : syracuseStep 689582605 = 258593477) B258593477
theorem B2986537 : Blo 1360499 2986537 := bstep (se 2 (by rfl) ⟨1119951, by rfl⟩ : syracuseStep 2986537 = 2239903) B2239903
theorem B10343051 : Blo 1360499 10343051 := bstep (se 1 (by rfl) ⟨7757288, by rfl⟩ : syracuseStep 10343051 = 15514577) B15514577
theorem B6542137 : Blo 1360499 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B21255043 : Blo 1360499 21255043 := bstep (se 1 (by rfl) ⟨15941282, by rfl⟩ : syracuseStep 21255043 = 31882565) B31882565
theorem B16561057 : Blo 1360499 16561057 := bstep (se 2 (by rfl) ⟨6210396, by rfl⟩ : syracuseStep 16561057 = 12420793) B12420793
theorem B2298847 : Blo 1360499 2298847 := bstep (se 1 (by rfl) ⟨1724135, by rfl⟩ : syracuseStep 2298847 = 3448271) B3448271
theorem B15504371 : Blo 1360499 15504371 := bstep (se 1 (by rfl) ⟨11628278, by rfl⟩ : syracuseStep 15504371 = 23256557) B23256557
theorem B23589929 : Blo 1360499 23589929 := bstep (se 2 (by rfl) ⟨8846223, by rfl⟩ : syracuseStep 23589929 = 17692447) B17692447
theorem B13079663 : Blo 1360499 13079663 := bstep (se 1 (by rfl) ⟨9809747, by rfl⟩ : syracuseStep 13079663 = 19619495) B19619495
theorem B2299063 : Blo 1360499 2299063 := bstep (se 1 (by rfl) ⟨1724297, by rfl⟩ : syracuseStep 2299063 = 3448595) B3448595
theorem B5166287 : Blo 1360499 5166287 := bstep (se 1 (by rfl) ⟨3874715, by rfl⟩ : syracuseStep 5166287 = 7749431) B7749431
theorem B4904171 : Blo 1360499 4904171 := bstep (se 1 (by rfl) ⟨3678128, by rfl⟩ : syracuseStep 4904171 = 7356257) B7356257
theorem B2946527 : Blo 1360499 2946527 := bstep (se 1 (by rfl) ⟨2209895, by rfl⟩ : syracuseStep 2946527 = 4419791) B4419791
theorem B18626039 : Blo 1360499 18626039 := bstep (se 1 (by rfl) ⟨13969529, by rfl⟩ : syracuseStep 18626039 = 27939059) B27939059
theorem B3061385 : Blo 1360499 3061385 := bstep (se 2 (by rfl) ⟨1148019, by rfl⟩ : syracuseStep 3061385 = 2296039) B2296039
theorem B3061403 : Blo 1360499 3061403 := bstep (se 1 (by rfl) ⟨2296052, by rfl⟩ : syracuseStep 3061403 = 4592105) B4592105
theorem B19404551 : Blo 1360499 19404551 := bstep (se 1 (by rfl) ⟨14553413, by rfl⟩ : syracuseStep 19404551 = 29106827) B29106827
theorem B3061601 : Blo 1360499 3061601 := bstep (se 2 (by rfl) ⟨1148100, by rfl⟩ : syracuseStep 3061601 = 2296201) B2296201
theorem B18635017 : Blo 1360499 18635017 := bstep (se 2 (by rfl) ⟨6988131, by rfl⟩ : syracuseStep 18635017 = 13976263) B13976263
theorem B6887753 : Blo 1360499 6887753 := bstep (se 2 (by rfl) ⟨2582907, by rfl⟩ : syracuseStep 6887753 = 5165815) B5165815
theorem B2070911 : Blo 1360499 2070911 := bstep (se 1 (by rfl) ⟨1553183, by rfl⟩ : syracuseStep 2070911 = 3106367) B3106367
theorem B11622811 : Blo 1360499 11622811 := bstep (se 1 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 11622811 = 17434217) B17434217
theorem B78535169 : Blo 1360499 78535169 := bstep (se 2 (by rfl) ⟨29450688, by rfl⟩ : syracuseStep 78535169 = 58901377) B58901377
theorem B2906857 : Blo 1360499 2906857 := bstep (se 2 (by rfl) ⟨1090071, by rfl⟩ : syracuseStep 2906857 = 2180143) B2180143
theorem B4594427 : Blo 1360499 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B3447593 : Blo 1360499 3447593 := bstep (se 2 (by rfl) ⟨1292847, by rfl⟩ : syracuseStep 3447593 = 2585695) B2585695
theorem B4594535 : Blo 1360499 4594535 := bstep (se 1 (by rfl) ⟨3445901, by rfl⟩ : syracuseStep 4594535 = 6891803) B6891803
theorem B4594589 : Blo 1360499 4594589 := bstep (se 3 (by rfl) ⟨861485, by rfl⟩ : syracuseStep 4594589 = 1722971) B1722971
theorem B10337219 : Blo 1360499 10337219 := bstep (se 1 (by rfl) ⟨7752914, by rfl⟩ : syracuseStep 10337219 = 15505829) B15505829
theorem B4594697 : Blo 1360499 4594697 := bstep (se 2 (by rfl) ⟨1723011, by rfl⟩ : syracuseStep 4594697 = 3446023) B3446023
theorem B27933821 : Blo 1360499 27933821 := bstep (se 3 (by rfl) ⟨5237591, by rfl⟩ : syracuseStep 27933821 = 10475183) B10475183
theorem B1531039 : Blo 1360499 1531039 := bstep (se 1 (by rfl) ⟨1148279, by rfl⟩ : syracuseStep 1531039 = 2296559) B2296559
theorem B1531291 : Blo 1360499 1531291 := bstep (se 1 (by rfl) ⟨1148468, by rfl⟩ : syracuseStep 1531291 = 2296937) B2296937
theorem B11632517 : Blo 1360499 11632517 := bstep (se 4 (by rfl) ⟨1090548, by rfl⟩ : syracuseStep 11632517 = 2181097) B2181097
theorem B3063689 : Blo 1360499 3063689 := bstep (se 2 (by rfl) ⟨1148883, by rfl⟩ : syracuseStep 3063689 = 2297767) B2297767
theorem B7757927 : Blo 1360499 7757927 := bstep (se 1 (by rfl) ⟨5818445, by rfl⟩ : syracuseStep 7757927 = 11636891) B11636891
theorem B11632895 : Blo 1360499 11632895 := bstep (se 1 (by rfl) ⟨8724671, by rfl⟩ : syracuseStep 11632895 = 17449343) B17449343
theorem B3064121 : Blo 1360499 3064121 := bstep (se 2 (by rfl) ⟨1149045, by rfl⟩ : syracuseStep 3064121 = 2298091) B2298091
theorem B24846689 : Blo 1360499 24846689 := bstep (se 2 (by rfl) ⟨9317508, by rfl⟩ : syracuseStep 24846689 = 18635017) B18635017
theorem B3064463 : Blo 1360499 3064463 := bstep (se 1 (by rfl) ⟨2298347, by rfl⟩ : syracuseStep 3064463 = 4596695) B4596695
theorem B3982049 : Blo 1360499 3982049 := bstep (se 2 (by rfl) ⟨1493268, by rfl⟩ : syracuseStep 3982049 = 2986537) B2986537
theorem B3269447 : Blo 1360499 3269447 := bstep (se 1 (by rfl) ⟨2452085, by rfl⟩ : syracuseStep 3269447 = 4904171) B4904171
theorem B3875809 : Blo 1360499 3875809 := bstep (se 2 (by rfl) ⟨1453428, by rfl⟩ : syracuseStep 3875809 = 2906857) B2906857
theorem B2040923 : Blo 1360499 2040923 := bstep (se 1 (by rfl) ⟨1530692, by rfl⟩ : syracuseStep 2040923 = 3061385) B3061385
theorem B2040935 : Blo 1360499 2040935 := bstep (se 1 (by rfl) ⟨1530701, by rfl⟩ : syracuseStep 2040935 = 3061403) B3061403
theorem B12936367 : Blo 1360499 12936367 := bstep (se 1 (by rfl) ⟨9702275, by rfl⟩ : syracuseStep 12936367 = 19404551) B19404551
theorem B2041067 : Blo 1360499 2041067 := bstep (se 1 (by rfl) ⟨1530800, by rfl⟩ : syracuseStep 2041067 = 3061601) B3061601
theorem B3065129 : Blo 1360499 3065129 := bstep (se 2 (by rfl) ⟨1149423, by rfl⟩ : syracuseStep 3065129 = 2298847) B2298847
theorem B2041385 : Blo 1360499 2041385 := bstep (se 2 (by rfl) ⟨765519, by rfl⟩ : syracuseStep 2041385 = 1531039) B1531039
theorem B3065417 : Blo 1360499 3065417 := bstep (se 2 (by rfl) ⟨1149531, by rfl⟩ : syracuseStep 3065417 = 2299063) B2299063
theorem B34891397 : Blo 1360499 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B52356779 : Blo 1360499 52356779 := bstep (se 1 (by rfl) ⟨39267584, by rfl⟩ : syracuseStep 52356779 = 78535169) B78535169
theorem B1361615 : Blo 1360499 1361615 := bstep (se 1 (by rfl) ⟨1021211, by rfl⟩ : syracuseStep 1361615 = 2042423) B2042423
theorem B3491603 : Blo 1360499 3491603 := bstep (se 1 (by rfl) ⟨2618702, by rfl⟩ : syracuseStep 3491603 = 5237405) B5237405
theorem B1361755 : Blo 1360499 1361755 := bstep (se 1 (by rfl) ⟨1021316, by rfl⟩ : syracuseStep 1361755 = 2042633) B2042633
theorem B2041721 : Blo 1360499 2041721 := bstep (se 2 (by rfl) ⟨765645, by rfl⟩ : syracuseStep 2041721 = 1531291) B1531291
theorem B6891479 : Blo 1360499 6891479 := bstep (se 1 (by rfl) ⟨5168609, by rfl⟩ : syracuseStep 6891479 = 10337219) B10337219
theorem B26175473 : Blo 1360499 26175473 := bstep (se 2 (by rfl) ⟨9815802, by rfl⟩ : syracuseStep 26175473 = 19631605) B19631605
theorem B18622547 : Blo 1360499 18622547 := bstep (se 1 (by rfl) ⟨13966910, by rfl⟩ : syracuseStep 18622547 = 27933821) B27933821
theorem B1362031 : Blo 1360499 1362031 := bstep (se 1 (by rfl) ⟨1021523, by rfl⟩ : syracuseStep 1362031 = 2043047) B2043047
theorem B2042459 : Blo 1360499 2042459 := bstep (se 1 (by rfl) ⟨1531844, by rfl⟩ : syracuseStep 2042459 = 3063689) B3063689
theorem B2042603 : Blo 1360499 2042603 := bstep (se 1 (by rfl) ⟨1531952, by rfl⟩ : syracuseStep 2042603 = 3063905) B3063905
theorem B9816875 : Blo 1360499 9816875 := bstep (se 1 (by rfl) ⟨7362656, by rfl⟩ : syracuseStep 9816875 = 14725313) B14725313
theorem B5811527 : Blo 1360499 5811527 := bstep (se 1 (by rfl) ⟨4358645, by rfl⟩ : syracuseStep 5811527 = 8717291) B8717291
theorem B5172619 : Blo 1360499 5172619 := bstep (se 1 (by rfl) ⟨3879464, by rfl⟩ : syracuseStep 5172619 = 7758929) B7758929
theorem B8719775 : Blo 1360499 8719775 := bstep (se 1 (by rfl) ⟨6539831, by rfl⟩ : syracuseStep 8719775 = 13079663) B13079663
theorem B3444191 : Blo 1360499 3444191 := bstep (se 1 (by rfl) ⟨2583143, by rfl⟩ : syracuseStep 3444191 = 5166287) B5166287
theorem B9809515 : Blo 1360499 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B2043599 : Blo 1360499 2043599 := bstep (se 1 (by rfl) ⟨1532699, by rfl⟩ : syracuseStep 2043599 = 3065399) B3065399
theorem B28340057 : Blo 1360499 28340057 := bstep (se 2 (by rfl) ⟨10627521, by rfl⟩ : syracuseStep 28340057 = 21255043) B21255043
theorem B22081409 : Blo 1360499 22081409 := bstep (se 2 (by rfl) ⟨8280528, by rfl⟩ : syracuseStep 22081409 = 16561057) B16561057
theorem B2584487 : Blo 1360499 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B4591835 : Blo 1360499 4591835 := bstep (se 1 (by rfl) ⟨3443876, by rfl⟩ : syracuseStep 4591835 = 6887753) B6887753
theorem B1380607 : Blo 1360499 1380607 := bstep (se 1 (by rfl) ⟨1035455, by rfl⟩ : syracuseStep 1380607 = 2070911) B2070911
theorem B2298395 : Blo 1360499 2298395 := bstep (se 1 (by rfl) ⟨1723796, by rfl⟩ : syracuseStep 2298395 = 3447593) B3447593
theorem B7755011 : Blo 1360499 7755011 := bstep (se 1 (by rfl) ⟨5816258, by rfl⟩ : syracuseStep 7755011 = 11632517) B11632517
theorem B6207151 : Blo 1360499 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B6895367 : Blo 1360499 6895367 := bstep (se 1 (by rfl) ⟨5171525, by rfl⟩ : syracuseStep 6895367 = 10343051) B10343051
theorem B15497081 : Blo 1360499 15497081 := bstep (se 2 (by rfl) ⟨5811405, by rfl⟩ : syracuseStep 15497081 = 11622811) B11622811
theorem B3061673 : Blo 1360499 3061673 := bstep (se 2 (by rfl) ⟨1148127, by rfl⟩ : syracuseStep 3061673 = 2296255) B2296255
theorem B10336247 : Blo 1360499 10336247 := bstep (se 1 (by rfl) ⟨7752185, by rfl⟩ : syracuseStep 10336247 = 15504371) B15504371
theorem B919443473 : Blo 1360499 919443473 := bstep (se 2 (by rfl) ⟨344791302, by rfl⟩ : syracuseStep 919443473 = 689582605) B689582605
theorem B15726619 : Blo 1360499 15726619 := bstep (se 1 (by rfl) ⟨11794964, by rfl⟩ : syracuseStep 15726619 = 23589929) B23589929
theorem B27965657 : Blo 1360499 27965657 := bstep (se 2 (by rfl) ⟨10487121, by rfl⟩ : syracuseStep 27965657 = 20974243) B20974243
theorem B1964351 : Blo 1360499 1964351 := bstep (se 1 (by rfl) ⟨1473263, by rfl⟩ : syracuseStep 1964351 = 2946527) B2946527
theorem B12417359 : Blo 1360499 12417359 := bstep (se 1 (by rfl) ⟨9313019, by rfl⟩ : syracuseStep 12417359 = 18626039) B18626039
theorem B3062249 : Blo 1360499 3062249 := bstep (se 2 (by rfl) ⟨1148343, by rfl⟩ : syracuseStep 3062249 = 2296687) B2296687
theorem B6986411 : Blo 1360499 6986411 := bstep (se 1 (by rfl) ⟨5239808, by rfl⟩ : syracuseStep 6986411 = 10479617) B10479617
theorem B23247809 : Blo 1360499 23247809 := bstep (se 2 (by rfl) ⟨8717928, by rfl⟩ : syracuseStep 23247809 = 17435857) B17435857
theorem B5168231 : Blo 1360499 5168231 := bstep (se 1 (by rfl) ⟨3876173, by rfl⟩ : syracuseStep 5168231 = 7752347) B7752347
theorem B3062951 : Blo 1360499 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B3063023 : Blo 1360499 3063023 := bstep (se 1 (by rfl) ⟨2297267, by rfl⟩ : syracuseStep 3063023 = 4594535) B4594535
theorem B3063059 : Blo 1360499 3063059 := bstep (se 1 (by rfl) ⟨2297294, by rfl⟩ : syracuseStep 3063059 = 4594589) B4594589
theorem B7748905 : Blo 1360499 7748905 := bstep (se 2 (by rfl) ⟨2905839, by rfl⟩ : syracuseStep 7748905 = 5811679) B5811679
theorem B3063131 : Blo 1360499 3063131 := bstep (se 1 (by rfl) ⟨2297348, by rfl⟩ : syracuseStep 3063131 = 4594697) B4594697
theorem B6888887 : Blo 1360499 6888887 := bstep (se 1 (by rfl) ⟨5166665, by rfl⟩ : syracuseStep 6888887 = 10333331) B10333331
theorem B3448615 : Blo 1360499 3448615 := bstep (se 1 (by rfl) ⟨2586461, by rfl⟩ : syracuseStep 3448615 = 5172923) B5172923
theorem B7364449 : Blo 1360499 7364449 := bstep (se 2 (by rfl) ⟨2761668, by rfl⟩ : syracuseStep 7364449 = 5523337) B5523337
theorem B4595615 : Blo 1360499 4595615 := bstep (se 1 (by rfl) ⟨3446711, by rfl⟩ : syracuseStep 4595615 = 6893423) B6893423
theorem B16564459 : Blo 1360499 16564459 := bstep (se 1 (by rfl) ⟨12423344, by rfl⟩ : syracuseStep 16564459 = 24846689) B24846689
theorem B1532263 : Blo 1360499 1532263 := bstep (se 1 (by rfl) ⟨1149197, by rfl⟩ : syracuseStep 1532263 = 2298395) B2298395
theorem B2654699 : Blo 1360499 2654699 := bstep (se 1 (by rfl) ⟨1991024, by rfl⟩ : syracuseStep 2654699 = 3982049) B3982049
theorem B2179631 : Blo 1360499 2179631 := bstep (se 1 (by rfl) ⟨1634723, by rfl⟩ : syracuseStep 2179631 = 3269447) B3269447
theorem B1360615 : Blo 1360499 1360615 := bstep (se 1 (by rfl) ⟨1020461, by rfl⟩ : syracuseStep 1360615 = 2040923) B2040923
theorem B1360623 : Blo 1360499 1360623 := bstep (se 1 (by rfl) ⟨1020467, by rfl⟩ : syracuseStep 1360623 = 2040935) B2040935
theorem B1360711 : Blo 1360499 1360711 := bstep (se 1 (by rfl) ⟨1020533, by rfl⟩ : syracuseStep 1360711 = 2041067) B2041067
theorem B5170007 : Blo 1360499 5170007 := bstep (se 1 (by rfl) ⟨3877505, by rfl⟩ : syracuseStep 5170007 = 7755011) B7755011
theorem B33112957 : Blo 1360499 33112957 := bstep (se 3 (by rfl) ⟨6208679, by rfl⟩ : syracuseStep 33112957 = 12417359) B12417359
theorem B68993957 : Blo 1360499 68993957 := bstep (se 4 (by rfl) ⟨6468183, by rfl⟩ : syracuseStep 68993957 = 12936367) B12936367
theorem B1360923 : Blo 1360499 1360923 := bstep (se 1 (by rfl) ⟨1020692, by rfl⟩ : syracuseStep 1360923 = 2041385) B2041385
theorem B4596911 : Blo 1360499 4596911 := bstep (se 1 (by rfl) ⟨3447683, by rfl⟩ : syracuseStep 4596911 = 6895367) B6895367
theorem B2327735 : Blo 1360499 2327735 := bstep (se 1 (by rfl) ⟨1745801, by rfl⟩ : syracuseStep 2327735 = 3491603) B3491603
theorem B10331387 : Blo 1360499 10331387 := bstep (se 1 (by rfl) ⟨7748540, by rfl⟩ : syracuseStep 10331387 = 15497081) B15497081
theorem B1361147 : Blo 1360499 1361147 := bstep (se 1 (by rfl) ⟨1020860, by rfl⟩ : syracuseStep 1361147 = 2041721) B2041721
theorem B2041115 : Blo 1360499 2041115 := bstep (se 1 (by rfl) ⟨1530836, by rfl⟩ : syracuseStep 2041115 = 3061673) B3061673
theorem B17450315 : Blo 1360499 17450315 := bstep (se 1 (by rfl) ⟨13087736, by rfl⟩ : syracuseStep 17450315 = 26175473) B26175473
theorem B6890831 : Blo 1360499 6890831 := bstep (se 1 (by rfl) ⟨5168123, by rfl⟩ : syracuseStep 6890831 = 10336247) B10336247
theorem B2041499 : Blo 1360499 2041499 := bstep (se 1 (by rfl) ⟨1531124, by rfl⟩ : syracuseStep 2041499 = 3062249) B3062249
theorem B10331873 : Blo 1360499 10331873 := bstep (se 2 (by rfl) ⟨3874452, by rfl⟩ : syracuseStep 10331873 = 7748905) B7748905
theorem B1361639 : Blo 1360499 1361639 := bstep (se 1 (by rfl) ⟨1021229, by rfl⟩ : syracuseStep 1361639 = 2042459) B2042459
theorem B1361735 : Blo 1360499 1361735 := bstep (se 1 (by rfl) ⟨1021301, by rfl⟩ : syracuseStep 1361735 = 2042603) B2042603
theorem B2041967 : Blo 1360499 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B2042015 : Blo 1360499 2042015 := bstep (se 1 (by rfl) ⟨1531511, by rfl⟩ : syracuseStep 2042015 = 3063023) B3063023
theorem B2042039 : Blo 1360499 2042039 := bstep (se 1 (by rfl) ⟨1531529, by rfl⟩ : syracuseStep 2042039 = 3063059) B3063059
theorem B2042087 : Blo 1360499 2042087 := bstep (se 1 (by rfl) ⟨1531565, by rfl⟩ : syracuseStep 2042087 = 3063131) B3063131
theorem B8276201 : Blo 1360499 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B2296127 : Blo 1360499 2296127 := bstep (se 1 (by rfl) ⟨1722095, by rfl⟩ : syracuseStep 2296127 = 3444191) B3444191
theorem B4598153 : Blo 1360499 4598153 := bstep (se 2 (by rfl) ⟨1724307, by rfl⟩ : syracuseStep 4598153 = 3448615) B3448615
theorem B6891965 : Blo 1360499 6891965 := bstep (se 3 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 6891965 = 2584487) B2584487
theorem B1362399 : Blo 1360499 1362399 := bstep (se 1 (by rfl) ⟨1021799, by rfl⟩ : syracuseStep 1362399 = 2043599) B2043599
theorem B18893371 : Blo 1360499 18893371 := bstep (se 1 (by rfl) ⟨14170028, by rfl⟩ : syracuseStep 18893371 = 28340057) B28340057
theorem B5171951 : Blo 1360499 5171951 := bstep (se 1 (by rfl) ⟨3878963, by rfl⟩ : syracuseStep 5171951 = 7757927) B7757927
theorem B2042747 : Blo 1360499 2042747 := bstep (se 1 (by rfl) ⟨1532060, by rfl⟩ : syracuseStep 2042747 = 3064121) B3064121
theorem B2042975 : Blo 1360499 2042975 := bstep (se 1 (by rfl) ⟨1532231, by rfl⟩ : syracuseStep 2042975 = 3064463) B3064463
theorem B52317413 : Blo 1360499 52317413 := bstep (se 4 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 52317413 = 9809515) B9809515
theorem B5238269 : Blo 1360499 5238269 := bstep (se 3 (by rfl) ⟨982175, by rfl⟩ : syracuseStep 5238269 = 1964351) B1964351
theorem B2043419 : Blo 1360499 2043419 := bstep (se 1 (by rfl) ⟨1532564, by rfl⟩ : syracuseStep 2043419 = 3065129) B3065129
theorem B2043611 : Blo 1360499 2043611 := bstep (se 1 (by rfl) ⟨1532708, by rfl⟩ : syracuseStep 2043611 = 3065417) B3065417
theorem B23260931 : Blo 1360499 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B612962315 : Blo 1360499 612962315 := bstep (se 1 (by rfl) ⟨459721736, by rfl⟩ : syracuseStep 612962315 = 919443473) B919443473
theorem B12415031 : Blo 1360499 12415031 := bstep (se 1 (by rfl) ⟨9311273, by rfl⟩ : syracuseStep 12415031 = 18622547) B18622547
theorem B4657607 : Blo 1360499 4657607 := bstep (se 1 (by rfl) ⟨3493205, by rfl⟩ : syracuseStep 4657607 = 6986411) B6986411
theorem B3445487 : Blo 1360499 3445487 := bstep (se 1 (by rfl) ⟨2584115, by rfl⟩ : syracuseStep 3445487 = 5168231) B5168231
theorem B5813183 : Blo 1360499 5813183 := bstep (se 1 (by rfl) ⟨4359887, by rfl⟩ : syracuseStep 5813183 = 8719775) B8719775
theorem B4592591 : Blo 1360499 4592591 := bstep (se 1 (by rfl) ⟨3444443, by rfl⟩ : syracuseStep 4592591 = 6888887) B6888887
theorem B9819265 : Blo 1360499 9819265 := bstep (se 2 (by rfl) ⟨3682224, by rfl⟩ : syracuseStep 9819265 = 7364449) B7364449
theorem B83875301 : Blo 1360499 83875301 := bstep (se 4 (by rfl) ⟨7863309, by rfl⟩ : syracuseStep 83875301 = 15726619) B15726619
theorem B3061223 : Blo 1360499 3061223 := bstep (se 1 (by rfl) ⟨2295917, by rfl⟩ : syracuseStep 3061223 = 4591835) B4591835
theorem B7755263 : Blo 1360499 7755263 := bstep (se 1 (by rfl) ⟨5816447, by rfl⟩ : syracuseStep 7755263 = 11632895) B11632895
theorem B34904519 : Blo 1360499 34904519 := bstep (se 1 (by rfl) ⟨26178389, by rfl⟩ : syracuseStep 34904519 = 52356779) B52356779
theorem B5167745 : Blo 1360499 5167745 := bstep (se 2 (by rfl) ⟨1937904, by rfl⟩ : syracuseStep 5167745 = 3875809) B3875809
theorem B4594319 : Blo 1360499 4594319 := bstep (se 1 (by rfl) ⟨3445739, by rfl⟩ : syracuseStep 4594319 = 6891479) B6891479
theorem B7363237 : Blo 1360499 7363237 := bstep (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) B1380607
theorem B18643771 : Blo 1360499 18643771 := bstep (se 1 (by rfl) ⟨13982828, by rfl⟩ : syracuseStep 18643771 = 27965657) B27965657
theorem B6896825 : Blo 1360499 6896825 := bstep (se 2 (by rfl) ⟨2586309, by rfl⟩ : syracuseStep 6896825 = 5172619) B5172619
theorem B6544583 : Blo 1360499 6544583 := bstep (se 1 (by rfl) ⟨4908437, by rfl⟩ : syracuseStep 6544583 = 9816875) B9816875
theorem B15498539 : Blo 1360499 15498539 := bstep (se 1 (by rfl) ⟨11623904, by rfl⟩ : syracuseStep 15498539 = 23247809) B23247809
theorem B3874351 : Blo 1360499 3874351 := bstep (se 1 (by rfl) ⟨2905763, by rfl⟩ : syracuseStep 3874351 = 5811527) B5811527
theorem B14720939 : Blo 1360499 14720939 := bstep (se 1 (by rfl) ⟨11040704, by rfl⟩ : syracuseStep 14720939 = 22081409) B22081409
theorem B3063743 : Blo 1360499 3063743 := bstep (se 1 (by rfl) ⟨2297807, by rfl⟩ : syracuseStep 3063743 = 4595615) B4595615
theorem B408641543 : Blo 1360499 408641543 := bstep (se 1 (by rfl) ⟨306481157, by rfl⟩ : syracuseStep 408641543 = 612962315) B612962315
theorem B3105071 : Blo 1360499 3105071 := bstep (se 1 (by rfl) ⟨2328803, by rfl⟩ : syracuseStep 3105071 = 4657607) B4657607
theorem B22085945 : Blo 1360499 22085945 := bstep (se 2 (by rfl) ⟨8282229, by rfl⟩ : syracuseStep 22085945 = 16564459) B16564459
theorem B3875455 : Blo 1360499 3875455 := bstep (se 1 (by rfl) ⟨2906591, by rfl⟩ : syracuseStep 3875455 = 5813183) B5813183
theorem B25191161 : Blo 1360499 25191161 := bstep (se 2 (by rfl) ⟨9446685, by rfl⟩ : syracuseStep 25191161 = 18893371) B18893371
theorem B3064607 : Blo 1360499 3064607 := bstep (se 1 (by rfl) ⟨2298455, by rfl⟩ : syracuseStep 3064607 = 4596911) B4596911
theorem B1360743 : Blo 1360499 1360743 := bstep (se 1 (by rfl) ⟨1020557, by rfl⟩ : syracuseStep 1360743 = 2041115) B2041115
theorem B11633543 : Blo 1360499 11633543 := bstep (se 1 (by rfl) ⟨8725157, by rfl⟩ : syracuseStep 11633543 = 17450315) B17450315
theorem B2040815 : Blo 1360499 2040815 := bstep (se 1 (by rfl) ⟨1530611, by rfl⟩ : syracuseStep 2040815 = 3061223) B3061223
theorem B5170175 : Blo 1360499 5170175 := bstep (se 1 (by rfl) ⟨3877631, by rfl⟩ : syracuseStep 5170175 = 7755263) B7755263
theorem B1360999 : Blo 1360499 1360999 := bstep (se 1 (by rfl) ⟨1020749, by rfl⟩ : syracuseStep 1360999 = 2041499) B2041499
theorem B1361311 : Blo 1360499 1361311 := bstep (se 1 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 1361311 = 2041967) B2041967
theorem B1361343 : Blo 1360499 1361343 := bstep (se 1 (by rfl) ⟨1021007, by rfl⟩ : syracuseStep 1361343 = 2042015) B2042015
theorem B1361359 : Blo 1360499 1361359 := bstep (se 1 (by rfl) ⟨1021019, by rfl⟩ : syracuseStep 1361359 = 2042039) B2042039
theorem B1361391 : Blo 1360499 1361391 := bstep (se 1 (by rfl) ⟨1021043, by rfl⟩ : syracuseStep 1361391 = 2042087) B2042087
theorem B13092353 : Blo 1360499 13092353 := bstep (se 2 (by rfl) ⟨4909632, by rfl⟩ : syracuseStep 13092353 = 9819265) B9819265
theorem B3065435 : Blo 1360499 3065435 := bstep (se 1 (by rfl) ⟨2299076, by rfl⟩ : syracuseStep 3065435 = 4598153) B4598153
theorem B1361831 : Blo 1360499 1361831 := bstep (se 1 (by rfl) ⟨1021373, by rfl⟩ : syracuseStep 1361831 = 2042747) B2042747
theorem B1361983 : Blo 1360499 1361983 := bstep (se 1 (by rfl) ⟨1021487, by rfl⟩ : syracuseStep 1361983 = 2042975) B2042975
theorem B4597883 : Blo 1360499 4597883 := bstep (se 1 (by rfl) ⟨3448412, by rfl⟩ : syracuseStep 4597883 = 6896825) B6896825
theorem B10332359 : Blo 1360499 10332359 := bstep (se 1 (by rfl) ⟨7749269, by rfl⟩ : syracuseStep 10332359 = 15498539) B15498539
theorem B3492179 : Blo 1360499 3492179 := bstep (se 1 (by rfl) ⟨2619134, by rfl⟩ : syracuseStep 3492179 = 5238269) B5238269
theorem B1362279 : Blo 1360499 1362279 := bstep (se 1 (by rfl) ⟨1021709, by rfl⟩ : syracuseStep 1362279 = 2043419) B2043419
theorem B1362407 : Blo 1360499 1362407 := bstep (se 1 (by rfl) ⟨1021805, by rfl⟩ : syracuseStep 1362407 = 2043611) B2043611
theorem B2042495 : Blo 1360499 2042495 := bstep (se 1 (by rfl) ⟨1531871, by rfl⟩ : syracuseStep 2042495 = 3063743) B3063743
theorem B8276687 : Blo 1360499 8276687 := bstep (se 1 (by rfl) ⟨6207515, by rfl⟩ : syracuseStep 8276687 = 12415031) B12415031
theorem B1453087 : Blo 1360499 1453087 := bstep (se 1 (by rfl) ⟨1089815, by rfl⟩ : syracuseStep 1453087 = 2179631) B2179631
theorem B2043017 : Blo 1360499 2043017 := bstep (se 2 (by rfl) ⟨766131, by rfl⟩ : syracuseStep 2043017 = 1532263) B1532263
theorem B2296991 : Blo 1360499 2296991 := bstep (se 1 (by rfl) ⟨1722743, by rfl⟩ : syracuseStep 2296991 = 3445487) B3445487
theorem B9817649 : Blo 1360499 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B24858361 : Blo 1360499 24858361 := bstep (se 2 (by rfl) ⟨9321885, by rfl⟩ : syracuseStep 24858361 = 18643771) B18643771
theorem B44150609 : Blo 1360499 44150609 := bstep (se 2 (by rfl) ⟨16556478, by rfl⟩ : syracuseStep 44150609 = 33112957) B33112957
theorem B5517467 : Blo 1360499 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B23269679 : Blo 1360499 23269679 := bstep (se 1 (by rfl) ⟨17452259, by rfl⟩ : syracuseStep 23269679 = 34904519) B34904519
theorem B3445163 : Blo 1360499 3445163 := bstep (se 1 (by rfl) ⟨2583872, by rfl⟩ : syracuseStep 3445163 = 5167745) B5167745
theorem B5165801 : Blo 1360499 5165801 := bstep (se 2 (by rfl) ⟨1937175, by rfl⟩ : syracuseStep 5165801 = 3874351) B3874351
theorem B4363055 : Blo 1360499 4363055 := bstep (se 1 (by rfl) ⟨3272291, by rfl⟩ : syracuseStep 4363055 = 6544583) B6544583
theorem B34878275 : Blo 1360499 34878275 := bstep (se 1 (by rfl) ⟨26158706, by rfl⟩ : syracuseStep 34878275 = 52317413) B52317413
theorem B28316789 : Blo 1360499 28316789 := bstep (se 5 (by rfl) ⟨1327349, by rfl⟩ : syracuseStep 28316789 = 2654699) B2654699
theorem B6207293 : Blo 1360499 6207293 := bstep (se 3 (by rfl) ⟨1163867, by rfl⟩ : syracuseStep 6207293 = 2327735) B2327735
theorem B3446671 : Blo 1360499 3446671 := bstep (se 1 (by rfl) ⟨2585003, by rfl⟩ : syracuseStep 3446671 = 5170007) B5170007
theorem B45995971 : Blo 1360499 45995971 := bstep (se 1 (by rfl) ⟨34496978, by rfl⟩ : syracuseStep 45995971 = 68993957) B68993957
theorem B3061727 : Blo 1360499 3061727 := bstep (se 1 (by rfl) ⟨2296295, by rfl⟩ : syracuseStep 3061727 = 4592591) B4592591
theorem B6887591 : Blo 1360499 6887591 := bstep (se 1 (by rfl) ⟨5165693, by rfl⟩ : syracuseStep 6887591 = 10331387) B10331387
theorem B4593887 : Blo 1360499 4593887 := bstep (se 1 (by rfl) ⟨3445415, by rfl⟩ : syracuseStep 4593887 = 6890831) B6890831
theorem B55916867 : Blo 1360499 55916867 := bstep (se 1 (by rfl) ⟨41937650, by rfl⟩ : syracuseStep 55916867 = 83875301) B83875301
theorem B6887915 : Blo 1360499 6887915 := bstep (se 1 (by rfl) ⟨5165936, by rfl⟩ : syracuseStep 6887915 = 10331873) B10331873
theorem B1530751 : Blo 1360499 1530751 := bstep (se 1 (by rfl) ⟨1148063, by rfl⟩ : syracuseStep 1530751 = 2296127) B2296127
theorem B4594643 : Blo 1360499 4594643 := bstep (se 1 (by rfl) ⟨3445982, by rfl⟩ : syracuseStep 4594643 = 6891965) B6891965
theorem B3062879 : Blo 1360499 3062879 := bstep (se 1 (by rfl) ⟨2297159, by rfl⟩ : syracuseStep 3062879 = 4594319) B4594319
theorem B3447967 : Blo 1360499 3447967 := bstep (se 1 (by rfl) ⟨2585975, by rfl⟩ : syracuseStep 3447967 = 5171951) B5171951
theorem B15507287 : Blo 1360499 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B9813959 : Blo 1360499 9813959 := bstep (se 1 (by rfl) ⟨7360469, by rfl⟩ : syracuseStep 9813959 = 14720939) B14720939
theorem B3678311 : Blo 1360499 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B16794107 : Blo 1360499 16794107 := bstep (se 1 (by rfl) ⟨12595580, by rfl⟩ : syracuseStep 16794107 = 25191161) B25191161
theorem B2908703 : Blo 1360499 2908703 := bstep (se 1 (by rfl) ⟨2181527, by rfl⟩ : syracuseStep 2908703 = 4363055) B4363055
theorem B1360543 : Blo 1360499 1360543 := bstep (se 1 (by rfl) ⟨1020407, by rfl⟩ : syracuseStep 1360543 = 2040815) B2040815
theorem B2041001 : Blo 1360499 2041001 := bstep (se 2 (by rfl) ⟨765375, by rfl⟩ : syracuseStep 2041001 = 1530751) B1530751
theorem B2041151 : Blo 1360499 2041151 := bstep (se 1 (by rfl) ⟨1530863, by rfl⟩ : syracuseStep 2041151 = 3061727) B3061727
theorem B3065255 : Blo 1360499 3065255 := bstep (se 1 (by rfl) ⟨2298941, by rfl⟩ : syracuseStep 3065255 = 4597883) B4597883
theorem B4597289 : Blo 1360499 4597289 := bstep (se 2 (by rfl) ⟨1723983, by rfl⟩ : syracuseStep 4597289 = 3447967) B3447967
theorem B2328119 : Blo 1360499 2328119 := bstep (se 1 (by rfl) ⟨1746089, by rfl⟩ : syracuseStep 2328119 = 3492179) B3492179
theorem B1361663 : Blo 1360499 1361663 := bstep (se 1 (by rfl) ⟨1021247, by rfl⟩ : syracuseStep 1361663 = 2042495) B2042495
theorem B2041919 : Blo 1360499 2041919 := bstep (se 1 (by rfl) ⟨1531439, by rfl⟩ : syracuseStep 2041919 = 3062879) B3062879
theorem B1362011 : Blo 1360499 1362011 := bstep (se 1 (by rfl) ⟨1021508, by rfl⟩ : syracuseStep 1362011 = 2043017) B2043017
theorem B61327961 : Blo 1360499 61327961 := bstep (se 2 (by rfl) ⟨22997985, by rfl⟩ : syracuseStep 61327961 = 45995971) B45995971
theorem B272427695 : Blo 1360499 272427695 := bstep (se 1 (by rfl) ⟨204320771, by rfl⟩ : syracuseStep 272427695 = 408641543) B408641543
theorem B14723963 : Blo 1360499 14723963 := bstep (se 1 (by rfl) ⟨11042972, by rfl⟩ : syracuseStep 14723963 = 22085945) B22085945
theorem B2296775 : Blo 1360499 2296775 := bstep (se 1 (by rfl) ⟨1722581, by rfl⟩ : syracuseStep 2296775 = 3445163) B3445163
theorem B3443867 : Blo 1360499 3443867 := bstep (se 1 (by rfl) ⟨2582900, by rfl⟩ : syracuseStep 3443867 = 5165801) B5165801
theorem B2043071 : Blo 1360499 2043071 := bstep (se 1 (by rfl) ⟨1532303, by rfl⟩ : syracuseStep 2043071 = 3064607) B3064607
theorem B23252183 : Blo 1360499 23252183 := bstep (se 1 (by rfl) ⟨17439137, by rfl⟩ : syracuseStep 23252183 = 34878275) B34878275
theorem B18877859 : Blo 1360499 18877859 := bstep (se 1 (by rfl) ⟨14158394, by rfl⟩ : syracuseStep 18877859 = 28316789) B28316789
theorem B8728235 : Blo 1360499 8728235 := bstep (se 1 (by rfl) ⟨6546176, by rfl⟩ : syracuseStep 8728235 = 13092353) B13092353
theorem B2043623 : Blo 1360499 2043623 := bstep (se 1 (by rfl) ⟨1532717, by rfl⟩ : syracuseStep 2043623 = 3065435) B3065435
theorem B1937449 : Blo 1360499 1937449 := bstep (se 2 (by rfl) ⟨726543, by rfl⟩ : syracuseStep 1937449 = 1453087) B1453087
theorem B4591727 : Blo 1360499 4591727 := bstep (se 1 (by rfl) ⟨3443795, by rfl⟩ : syracuseStep 4591727 = 6887591) B6887591
theorem B37277911 : Blo 1360499 37277911 := bstep (se 1 (by rfl) ⟨27958433, by rfl⟩ : syracuseStep 37277911 = 55916867) B55916867
theorem B4591943 : Blo 1360499 4591943 := bstep (se 1 (by rfl) ⟨3443957, by rfl⟩ : syracuseStep 4591943 = 6887915) B6887915
theorem B5517791 : Blo 1360499 5517791 := bstep (se 1 (by rfl) ⟨4138343, by rfl⟩ : syracuseStep 5517791 = 8276687) B8276687
theorem B16552781 : Blo 1360499 16552781 := bstep (se 3 (by rfl) ⟨3103646, by rfl⟩ : syracuseStep 16552781 = 6207293) B6207293
theorem B6542639 : Blo 1360499 6542639 := bstep (se 1 (by rfl) ⟨4906979, by rfl⟩ : syracuseStep 6542639 = 9813959) B9813959
theorem B2070047 : Blo 1360499 2070047 := bstep (se 1 (by rfl) ⟨1552535, by rfl⟩ : syracuseStep 2070047 = 3105071) B3105071
theorem B15513119 : Blo 1360499 15513119 := bstep (se 1 (by rfl) ⟨11634839, by rfl⟩ : syracuseStep 15513119 = 23269679) B23269679
theorem B7755695 : Blo 1360499 7755695 := bstep (se 1 (by rfl) ⟨5816771, by rfl⟩ : syracuseStep 7755695 = 11633543) B11633543
theorem B3446783 : Blo 1360499 3446783 := bstep (se 1 (by rfl) ⟨2585087, by rfl⟩ : syracuseStep 3446783 = 5170175) B5170175
theorem B5167273 : Blo 1360499 5167273 := bstep (se 2 (by rfl) ⟨1937727, by rfl⟩ : syracuseStep 5167273 = 3875455) B3875455
theorem B6888239 : Blo 1360499 6888239 := bstep (se 1 (by rfl) ⟨5166179, by rfl⟩ : syracuseStep 6888239 = 10332359) B10332359
theorem B3062591 : Blo 1360499 3062591 := bstep (se 1 (by rfl) ⟨2296943, by rfl⟩ : syracuseStep 3062591 = 4593887) B4593887
theorem B3063095 : Blo 1360499 3063095 := bstep (se 1 (by rfl) ⟨2297321, by rfl⟩ : syracuseStep 3063095 = 4594643) B4594643
theorem B1531327 : Blo 1360499 1531327 := bstep (se 1 (by rfl) ⟨1148495, by rfl⟩ : syracuseStep 1531327 = 2296991) B2296991
theorem B33144481 : Blo 1360499 33144481 := bstep (se 2 (by rfl) ⟨12429180, by rfl⟩ : syracuseStep 33144481 = 24858361) B24858361
theorem B6545099 : Blo 1360499 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B4595561 : Blo 1360499 4595561 := bstep (se 2 (by rfl) ⟨1723335, by rfl⟩ : syracuseStep 4595561 = 3446671) B3446671
theorem B29433739 : Blo 1360499 29433739 := bstep (se 1 (by rfl) ⟨22075304, by rfl⟩ : syracuseStep 29433739 = 44150609) B44150609
theorem B10338191 : Blo 1360499 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B6889697 : Blo 1360499 6889697 := bstep (se 2 (by rfl) ⟨2583636, by rfl⟩ : syracuseStep 6889697 = 5167273) B5167273
theorem B3678527 : Blo 1360499 3678527 := bstep (se 1 (by rfl) ⟨2758895, by rfl⟩ : syracuseStep 3678527 = 5517791) B5517791
theorem B11035187 : Blo 1360499 11035187 := bstep (se 1 (by rfl) ⟨8276390, by rfl⟩ : syracuseStep 11035187 = 16552781) B16552781
theorem B1360667 : Blo 1360499 1360667 := bstep (se 1 (by rfl) ⟨1020500, by rfl⟩ : syracuseStep 1360667 = 2041001) B2041001
theorem B1360767 : Blo 1360499 1360767 := bstep (se 1 (by rfl) ⟨1020575, by rfl⟩ : syracuseStep 1360767 = 2041151) B2041151
theorem B3064859 : Blo 1360499 3064859 := bstep (se 1 (by rfl) ⟨2298644, by rfl⟩ : syracuseStep 3064859 = 4597289) B4597289
theorem B5170463 : Blo 1360499 5170463 := bstep (se 1 (by rfl) ⟨3877847, by rfl⟩ : syracuseStep 5170463 = 7755695) B7755695
theorem B1361279 : Blo 1360499 1361279 := bstep (se 1 (by rfl) ⟨1020959, by rfl⟩ : syracuseStep 1361279 = 2041919) B2041919
theorem B181618463 : Blo 1360499 181618463 := bstep (se 1 (by rfl) ⟨136213847, by rfl⟩ : syracuseStep 181618463 = 272427695) B272427695
theorem B2041727 : Blo 1360499 2041727 := bstep (se 1 (by rfl) ⟨1531295, by rfl⟩ : syracuseStep 2041727 = 3062591) B3062591
theorem B9815975 : Blo 1360499 9815975 := bstep (se 1 (by rfl) ⟨7361981, by rfl⟩ : syracuseStep 9815975 = 14723963) B14723963
theorem B2041769 : Blo 1360499 2041769 := bstep (se 2 (by rfl) ⟨765663, by rfl⟩ : syracuseStep 2041769 = 1531327) B1531327
theorem B2295911 : Blo 1360499 2295911 := bstep (se 1 (by rfl) ⟨1721933, by rfl⟩ : syracuseStep 2295911 = 3443867) B3443867
theorem B1362047 : Blo 1360499 1362047 := bstep (se 1 (by rfl) ⟨1021535, by rfl⟩ : syracuseStep 1362047 = 2043071) B2043071
theorem B15501455 : Blo 1360499 15501455 := bstep (se 1 (by rfl) ⟨11626091, by rfl⟩ : syracuseStep 15501455 = 23252183) B23252183
theorem B2042063 : Blo 1360499 2042063 := bstep (se 1 (by rfl) ⟨1531547, by rfl⟩ : syracuseStep 2042063 = 3063095) B3063095
theorem B12585239 : Blo 1360499 12585239 := bstep (se 1 (by rfl) ⟨9438929, by rfl⟩ : syracuseStep 12585239 = 18877859) B18877859
theorem B5818823 : Blo 1360499 5818823 := bstep (se 1 (by rfl) ⟨4364117, by rfl⟩ : syracuseStep 5818823 = 8728235) B8728235
theorem B1362415 : Blo 1360499 1362415 := bstep (se 1 (by rfl) ⟨1021811, by rfl⟩ : syracuseStep 1362415 = 2043623) B2043623
theorem B6892127 : Blo 1360499 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B2583265 : Blo 1360499 2583265 := bstep (se 2 (by rfl) ⟨968724, by rfl⟩ : syracuseStep 2583265 = 1937449) B1937449
theorem B2452207 : Blo 1360499 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B49703881 : Blo 1360499 49703881 := bstep (se 2 (by rfl) ⟨18638955, by rfl⟩ : syracuseStep 49703881 = 37277911) B37277911
theorem B4361759 : Blo 1360499 4361759 := bstep (se 1 (by rfl) ⟨3271319, by rfl⟩ : syracuseStep 4361759 = 6542639) B6542639
theorem B2043503 : Blo 1360499 2043503 := bstep (se 1 (by rfl) ⟨1532627, by rfl⟩ : syracuseStep 2043503 = 3065255) B3065255
theorem B10342079 : Blo 1360499 10342079 := bstep (se 1 (by rfl) ⟨7756559, by rfl⟩ : syracuseStep 10342079 = 15513119) B15513119
theorem B1552079 : Blo 1360499 1552079 := bstep (se 1 (by rfl) ⟨1164059, by rfl⟩ : syracuseStep 1552079 = 2328119) B2328119
theorem B2297855 : Blo 1360499 2297855 := bstep (se 1 (by rfl) ⟨1723391, by rfl⟩ : syracuseStep 2297855 = 3446783) B3446783
theorem B4592159 : Blo 1360499 4592159 := bstep (se 1 (by rfl) ⟨3444119, by rfl⟩ : syracuseStep 4592159 = 6888239) B6888239
theorem B44192641 : Blo 1360499 44192641 := bstep (se 2 (by rfl) ⟨16572240, by rfl⟩ : syracuseStep 44192641 = 33144481) B33144481
theorem B4363399 : Blo 1360499 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B39244985 : Blo 1360499 39244985 := bstep (se 2 (by rfl) ⟨14716869, by rfl⟩ : syracuseStep 39244985 = 29433739) B29433739
theorem B3061151 : Blo 1360499 3061151 := bstep (se 1 (by rfl) ⟨2295863, by rfl⟩ : syracuseStep 3061151 = 4591727) B4591727
theorem B3061295 : Blo 1360499 3061295 := bstep (se 1 (by rfl) ⟨2295971, by rfl⟩ : syracuseStep 3061295 = 4591943) B4591943
theorem B11196071 : Blo 1360499 11196071 := bstep (se 1 (by rfl) ⟨8397053, by rfl⟩ : syracuseStep 11196071 = 16794107) B16794107
theorem B1939135 : Blo 1360499 1939135 := bstep (se 1 (by rfl) ⟨1454351, by rfl⟩ : syracuseStep 1939135 = 2908703) B2908703
theorem B5520125 : Blo 1360499 5520125 := bstep (se 3 (by rfl) ⟨1035023, by rfl⟩ : syracuseStep 5520125 = 2070047) B2070047
theorem B40885307 : Blo 1360499 40885307 := bstep (se 1 (by rfl) ⟨30663980, by rfl⟩ : syracuseStep 40885307 = 61327961) B61327961
theorem B1531183 : Blo 1360499 1531183 := bstep (se 1 (by rfl) ⟨1148387, by rfl⟩ : syracuseStep 1531183 = 2296775) B2296775
theorem B3063707 : Blo 1360499 3063707 := bstep (se 1 (by rfl) ⟨2297780, by rfl⟩ : syracuseStep 3063707 = 4595561) B4595561
theorem B7356791 : Blo 1360499 7356791 := bstep (se 1 (by rfl) ⟨5517593, by rfl⟩ : syracuseStep 7356791 = 11035187) B11035187
theorem B2040767 : Blo 1360499 2040767 := bstep (se 1 (by rfl) ⟨1530575, by rfl⟩ : syracuseStep 2040767 = 3061151) B3061151
theorem B3269609 : Blo 1360499 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B2040863 : Blo 1360499 2040863 := bstep (se 1 (by rfl) ⟨1530647, by rfl⟩ : syracuseStep 2040863 = 3061295) B3061295
theorem B1361151 : Blo 1360499 1361151 := bstep (se 1 (by rfl) ⟨1020863, by rfl⟩ : syracuseStep 1361151 = 2041727) B2041727
theorem B1361179 : Blo 1360499 1361179 := bstep (se 1 (by rfl) ⟨1020884, by rfl⟩ : syracuseStep 1361179 = 2041769) B2041769
theorem B1361375 : Blo 1360499 1361375 := bstep (se 1 (by rfl) ⟨1021031, by rfl⟩ : syracuseStep 1361375 = 2042063) B2042063
theorem B5817865 : Blo 1360499 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B8390159 : Blo 1360499 8390159 := bstep (se 1 (by rfl) ⟨6292619, by rfl⟩ : syracuseStep 8390159 = 12585239) B12585239
theorem B2041577 : Blo 1360499 2041577 := bstep (se 2 (by rfl) ⟨765591, by rfl⟩ : syracuseStep 2041577 = 1531183) B1531183
theorem B3680083 : Blo 1360499 3680083 := bstep (se 1 (by rfl) ⟨2760062, by rfl⟩ : syracuseStep 3680083 = 5520125) B5520125
theorem B4138877 : Blo 1360499 4138877 := bstep (se 3 (by rfl) ⟨776039, by rfl⟩ : syracuseStep 4138877 = 1552079) B1552079
theorem B27256871 : Blo 1360499 27256871 := bstep (se 1 (by rfl) ⟨20442653, by rfl⟩ : syracuseStep 27256871 = 40885307) B40885307
theorem B1362335 : Blo 1360499 1362335 := bstep (se 1 (by rfl) ⟨1021751, by rfl⟩ : syracuseStep 1362335 = 2043503) B2043503
theorem B2042471 : Blo 1360499 2042471 := bstep (se 1 (by rfl) ⟨1531853, by rfl⟩ : syracuseStep 2042471 = 3063707) B3063707
theorem B2452351 : Blo 1360499 2452351 := bstep (se 1 (by rfl) ⟨1839263, by rfl⟩ : syracuseStep 2452351 = 3678527) B3678527
theorem B2043239 : Blo 1360499 2043239 := bstep (se 1 (by rfl) ⟨1532429, by rfl⟩ : syracuseStep 2043239 = 3064859) B3064859
theorem B3444353 : Blo 1360499 3444353 := bstep (se 2 (by rfl) ⟨1291632, by rfl⟩ : syracuseStep 3444353 = 2583265) B2583265
theorem B10334303 : Blo 1360499 10334303 := bstep (se 1 (by rfl) ⟨7750727, by rfl⟩ : syracuseStep 10334303 = 15501455) B15501455
theorem B3879215 : Blo 1360499 3879215 := bstep (se 1 (by rfl) ⟨2909411, by rfl⟩ : syracuseStep 3879215 = 5818823) B5818823
theorem B484315901 : Blo 1360499 484315901 := bstep (se 3 (by rfl) ⟨90809231, by rfl⟩ : syracuseStep 484315901 = 181618463) B181618463
theorem B2585513 : Blo 1360499 2585513 := bstep (se 2 (by rfl) ⟨969567, by rfl⟩ : syracuseStep 2585513 = 1939135) B1939135
theorem B6894719 : Blo 1360499 6894719 := bstep (se 1 (by rfl) ⟨5171039, by rfl⟩ : syracuseStep 6894719 = 10342079) B10342079
theorem B4593131 : Blo 1360499 4593131 := bstep (se 1 (by rfl) ⟨3444848, by rfl⟩ : syracuseStep 4593131 = 6889697) B6889697
theorem B3061439 : Blo 1360499 3061439 := bstep (se 1 (by rfl) ⟨2296079, by rfl⟩ : syracuseStep 3061439 = 4592159) B4592159
theorem B26163323 : Blo 1360499 26163323 := bstep (se 1 (by rfl) ⟨19622492, by rfl⟩ : syracuseStep 26163323 = 39244985) B39244985
theorem B3446975 : Blo 1360499 3446975 := bstep (se 1 (by rfl) ⟨2585231, by rfl⟩ : syracuseStep 3446975 = 5170463) B5170463
theorem B58923521 : Blo 1360499 58923521 := bstep (se 2 (by rfl) ⟨22096320, by rfl⟩ : syracuseStep 58923521 = 44192641) B44192641
theorem B66271841 : Blo 1360499 66271841 := bstep (se 2 (by rfl) ⟨24851940, by rfl⟩ : syracuseStep 66271841 = 49703881) B49703881
theorem B6543983 : Blo 1360499 6543983 := bstep (se 1 (by rfl) ⟨4907987, by rfl⟩ : syracuseStep 6543983 = 9815975) B9815975
theorem B1530607 : Blo 1360499 1530607 := bstep (se 1 (by rfl) ⟨1147955, by rfl⟩ : syracuseStep 1530607 = 2295911) B2295911
theorem B477699029 : Blo 1360499 477699029 := bstep (se 7 (by rfl) ⟨5598035, by rfl⟩ : syracuseStep 477699029 = 11196071) B11196071
theorem B4594751 : Blo 1360499 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B2907839 : Blo 1360499 2907839 := bstep (se 1 (by rfl) ⟨2180879, by rfl⟩ : syracuseStep 2907839 = 4361759) B4361759
theorem B1531903 : Blo 1360499 1531903 := bstep (se 1 (by rfl) ⟨1148927, by rfl⟩ : syracuseStep 1531903 = 2297855) B2297855
theorem B6889535 : Blo 1360499 6889535 := bstep (se 1 (by rfl) ⟨5167151, by rfl⟩ : syracuseStep 6889535 = 10334303) B10334303
theorem B1360511 : Blo 1360499 1360511 := bstep (se 1 (by rfl) ⟨1020383, by rfl⟩ : syracuseStep 1360511 = 2040767) B2040767
theorem B2179739 : Blo 1360499 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B1360575 : Blo 1360499 1360575 := bstep (se 1 (by rfl) ⟨1020431, by rfl⟩ : syracuseStep 1360575 = 2040863) B2040863
theorem B4596479 : Blo 1360499 4596479 := bstep (se 1 (by rfl) ⟨3447359, by rfl⟩ : syracuseStep 4596479 = 6894719) B6894719
theorem B2040809 : Blo 1360499 2040809 := bstep (se 2 (by rfl) ⟨765303, by rfl⟩ : syracuseStep 2040809 = 1530607) B1530607
theorem B2040959 : Blo 1360499 2040959 := bstep (se 1 (by rfl) ⟨1530719, by rfl⟩ : syracuseStep 2040959 = 3061439) B3061439
theorem B1361051 : Blo 1360499 1361051 := bstep (se 1 (by rfl) ⟨1020788, by rfl⟩ : syracuseStep 1361051 = 2041577) B2041577
theorem B3269801 : Blo 1360499 3269801 := bstep (se 2 (by rfl) ⟨1226175, by rfl⟩ : syracuseStep 3269801 = 2452351) B2452351
theorem B17442215 : Blo 1360499 17442215 := bstep (se 1 (by rfl) ⟨13081661, by rfl⟩ : syracuseStep 17442215 = 26163323) B26163323
theorem B39282347 : Blo 1360499 39282347 := bstep (se 1 (by rfl) ⟨29461760, by rfl⟩ : syracuseStep 39282347 = 58923521) B58923521
theorem B44181227 : Blo 1360499 44181227 := bstep (se 1 (by rfl) ⟨33135920, by rfl⟩ : syracuseStep 44181227 = 66271841) B66271841
theorem B1361647 : Blo 1360499 1361647 := bstep (se 1 (by rfl) ⟨1021235, by rfl⟩ : syracuseStep 1361647 = 2042471) B2042471
theorem B318466019 : Blo 1360499 318466019 := bstep (se 1 (by rfl) ⟨238849514, by rfl⟩ : syracuseStep 318466019 = 477699029) B477699029
theorem B1362159 : Blo 1360499 1362159 := bstep (se 1 (by rfl) ⟨1021619, by rfl⟩ : syracuseStep 1362159 = 2043239) B2043239
theorem B11037005 : Blo 1360499 11037005 := bstep (se 3 (by rfl) ⟨2069438, by rfl⟩ : syracuseStep 11037005 = 4138877) B4138877
theorem B2296235 : Blo 1360499 2296235 := bstep (se 1 (by rfl) ⟨1722176, by rfl⟩ : syracuseStep 2296235 = 3444353) B3444353
theorem B2042537 : Blo 1360499 2042537 := bstep (se 2 (by rfl) ⟨765951, by rfl⟩ : syracuseStep 2042537 = 1531903) B1531903
theorem B1723675 : Blo 1360499 1723675 := bstep (se 1 (by rfl) ⟨1292756, by rfl⟩ : syracuseStep 1723675 = 2585513) B2585513
theorem B2297983 : Blo 1360499 2297983 := bstep (se 1 (by rfl) ⟨1723487, by rfl⟩ : syracuseStep 2297983 = 3446975) B3446975
theorem B4362655 : Blo 1360499 4362655 := bstep (se 1 (by rfl) ⟨3271991, by rfl⟩ : syracuseStep 4362655 = 6543983) B6543983
theorem B7754237 : Blo 1360499 7754237 := bstep (se 3 (by rfl) ⟨1453919, by rfl⟩ : syracuseStep 7754237 = 2907839) B2907839
theorem B72684989 : Blo 1360499 72684989 := bstep (se 3 (by rfl) ⟨13628435, by rfl⟩ : syracuseStep 72684989 = 27256871) B27256871
theorem B2586143 : Blo 1360499 2586143 := bstep (se 1 (by rfl) ⟨1939607, by rfl⟩ : syracuseStep 2586143 = 3879215) B3879215
theorem B322877267 : Blo 1360499 322877267 := bstep (se 1 (by rfl) ⟨242157950, by rfl⟩ : syracuseStep 322877267 = 484315901) B484315901
theorem B19618109 : Blo 1360499 19618109 := bstep (se 3 (by rfl) ⟨3678395, by rfl⟩ : syracuseStep 19618109 = 7356791) B7356791
theorem B3062087 : Blo 1360499 3062087 := bstep (se 1 (by rfl) ⟨2296565, by rfl⟩ : syracuseStep 3062087 = 4593131) B4593131
theorem B5593439 : Blo 1360499 5593439 := bstep (se 1 (by rfl) ⟨4195079, by rfl⟩ : syracuseStep 5593439 = 8390159) B8390159
theorem B19627109 : Blo 1360499 19627109 := bstep (se 4 (by rfl) ⟨1840041, by rfl⟩ : syracuseStep 19627109 = 3680083) B3680083
theorem B7757153 : Blo 1360499 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B3063167 : Blo 1360499 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B3063977 : Blo 1360499 3063977 := bstep (se 2 (by rfl) ⟨1148991, by rfl⟩ : syracuseStep 3063977 = 2297983) B2297983
theorem B5169491 : Blo 1360499 5169491 := bstep (se 1 (by rfl) ⟨3877118, by rfl⟩ : syracuseStep 5169491 = 7754237) B7754237
theorem B3064319 : Blo 1360499 3064319 := bstep (se 1 (by rfl) ⟨2298239, by rfl⟩ : syracuseStep 3064319 = 4596479) B4596479
theorem B5816873 : Blo 1360499 5816873 := bstep (se 2 (by rfl) ⟨2181327, by rfl⟩ : syracuseStep 5816873 = 4362655) B4362655
theorem B1360539 : Blo 1360499 1360539 := bstep (se 1 (by rfl) ⟨1020404, by rfl⟩ : syracuseStep 1360539 = 2040809) B2040809
theorem B1360639 : Blo 1360499 1360639 := bstep (se 1 (by rfl) ⟨1020479, by rfl⟩ : syracuseStep 1360639 = 2040959) B2040959
theorem B2179867 : Blo 1360499 2179867 := bstep (se 1 (by rfl) ⟨1634900, by rfl⟩ : syracuseStep 2179867 = 3269801) B3269801
theorem B48456659 : Blo 1360499 48456659 := bstep (se 1 (by rfl) ⟨36342494, by rfl⟩ : syracuseStep 48456659 = 72684989) B72684989
theorem B2041391 : Blo 1360499 2041391 := bstep (se 1 (by rfl) ⟨1531043, by rfl⟩ : syracuseStep 2041391 = 3062087) B3062087
theorem B7358003 : Blo 1360499 7358003 := bstep (se 1 (by rfl) ⟨5518502, by rfl⟩ : syracuseStep 7358003 = 11037005) B11037005
theorem B3728959 : Blo 1360499 3728959 := bstep (se 1 (by rfl) ⟨2796719, by rfl⟩ : syracuseStep 3728959 = 5593439) B5593439
theorem B1361691 : Blo 1360499 1361691 := bstep (se 1 (by rfl) ⟨1021268, by rfl⟩ : syracuseStep 1361691 = 2042537) B2042537
theorem B13084739 : Blo 1360499 13084739 := bstep (se 1 (by rfl) ⟨9813554, by rfl⟩ : syracuseStep 13084739 = 19627109) B19627109
theorem B5171435 : Blo 1360499 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B2042111 : Blo 1360499 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B849242717 : Blo 1360499 849242717 := bstep (se 3 (by rfl) ⟨159233009, by rfl⟩ : syracuseStep 849242717 = 318466019) B318466019
theorem B1453159 : Blo 1360499 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B11628143 : Blo 1360499 11628143 := bstep (se 1 (by rfl) ⟨8721107, by rfl⟩ : syracuseStep 11628143 = 17442215) B17442215
theorem B1724095 : Blo 1360499 1724095 := bstep (se 1 (by rfl) ⟨1293071, by rfl⟩ : syracuseStep 1724095 = 2586143) B2586143
theorem B29454151 : Blo 1360499 29454151 := bstep (se 1 (by rfl) ⟨22090613, by rfl⟩ : syracuseStep 29454151 = 44181227) B44181227
theorem B13078739 : Blo 1360499 13078739 := bstep (se 1 (by rfl) ⟨9809054, by rfl⟩ : syracuseStep 13078739 = 19618109) B19618109
theorem B2298233 : Blo 1360499 2298233 := bstep (se 2 (by rfl) ⟨861837, by rfl⟩ : syracuseStep 2298233 = 1723675) B1723675
theorem B4593023 : Blo 1360499 4593023 := bstep (se 1 (by rfl) ⟨3444767, by rfl⟩ : syracuseStep 4593023 = 6889535) B6889535
theorem B26188231 : Blo 1360499 26188231 := bstep (se 1 (by rfl) ⟨19641173, by rfl⟩ : syracuseStep 26188231 = 39282347) B39282347
theorem B215251511 : Blo 1360499 215251511 := bstep (se 1 (by rfl) ⟨161438633, by rfl⟩ : syracuseStep 215251511 = 322877267) B322877267
theorem B1530823 : Blo 1360499 1530823 := bstep (se 1 (by rfl) ⟨1148117, by rfl⟩ : syracuseStep 1530823 = 2296235) B2296235
theorem B1532155 : Blo 1360499 1532155 := bstep (se 1 (by rfl) ⟨1149116, by rfl⟩ : syracuseStep 1532155 = 2298233) B2298233
theorem B7750181 : Blo 1360499 7750181 := bstep (se 4 (by rfl) ⟨726579, by rfl⟩ : syracuseStep 7750181 = 1453159) B1453159
theorem B1360927 : Blo 1360499 1360927 := bstep (se 1 (by rfl) ⟨1020695, by rfl⟩ : syracuseStep 1360927 = 2041391) B2041391
theorem B2041097 : Blo 1360499 2041097 := bstep (se 2 (by rfl) ⟨765411, by rfl⟩ : syracuseStep 2041097 = 1530823) B1530823
theorem B1361407 : Blo 1360499 1361407 := bstep (se 1 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 1361407 = 2042111) B2042111
theorem B7752095 : Blo 1360499 7752095 := bstep (se 1 (by rfl) ⟨5814071, by rfl⟩ : syracuseStep 7752095 = 11628143) B11628143
theorem B2042651 : Blo 1360499 2042651 := bstep (se 1 (by rfl) ⟨1531988, by rfl⟩ : syracuseStep 2042651 = 3063977) B3063977
theorem B8719159 : Blo 1360499 8719159 := bstep (se 1 (by rfl) ⟨6539369, by rfl⟩ : syracuseStep 8719159 = 13078739) B13078739
theorem B2042879 : Blo 1360499 2042879 := bstep (se 1 (by rfl) ⟨1532159, by rfl⟩ : syracuseStep 2042879 = 3064319) B3064319
theorem B34917641 : Blo 1360499 34917641 := bstep (se 2 (by rfl) ⟨13094115, by rfl⟩ : syracuseStep 34917641 = 26188231) B26188231
theorem B32304439 : Blo 1360499 32304439 := bstep (se 1 (by rfl) ⟨24228329, by rfl⟩ : syracuseStep 32304439 = 48456659) B48456659
theorem B15511661 : Blo 1360499 15511661 := bstep (se 3 (by rfl) ⟨2908436, by rfl⟩ : syracuseStep 15511661 = 5816873) B5816873
theorem B566161811 : Blo 1360499 566161811 := bstep (se 1 (by rfl) ⟨424621358, by rfl⟩ : syracuseStep 566161811 = 849242717) B849242717
theorem B2298793 : Blo 1360499 2298793 := bstep (se 2 (by rfl) ⟨862047, by rfl⟩ : syracuseStep 2298793 = 1724095) B1724095
theorem B3446327 : Blo 1360499 3446327 := bstep (se 1 (by rfl) ⟨2584745, by rfl⟩ : syracuseStep 3446327 = 5169491) B5169491
theorem B19887781 : Blo 1360499 19887781 := bstep (se 4 (by rfl) ⟨1864479, by rfl⟩ : syracuseStep 19887781 = 3728959) B3728959
theorem B3062015 : Blo 1360499 3062015 := bstep (se 1 (by rfl) ⟨2296511, by rfl⟩ : syracuseStep 3062015 = 4593023) B4593023
theorem B4905335 : Blo 1360499 4905335 := bstep (se 1 (by rfl) ⟨3679001, by rfl⟩ : syracuseStep 4905335 = 7358003) B7358003
theorem B2906489 : Blo 1360499 2906489 := bstep (se 2 (by rfl) ⟨1089933, by rfl⟩ : syracuseStep 2906489 = 2179867) B2179867
theorem B8723159 : Blo 1360499 8723159 := bstep (se 1 (by rfl) ⟨6542369, by rfl⟩ : syracuseStep 8723159 = 13084739) B13084739
theorem B574004029 : Blo 1360499 574004029 := bstep (se 3 (by rfl) ⟨107625755, by rfl⟩ : syracuseStep 574004029 = 215251511) B215251511
theorem B3447623 : Blo 1360499 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B39272201 : Blo 1360499 39272201 := bstep (se 2 (by rfl) ⟨14727075, by rfl⟩ : syracuseStep 39272201 = 29454151) B29454151
theorem B1360731 : Blo 1360499 1360731 := bstep (se 1 (by rfl) ⟨1020548, by rfl⟩ : syracuseStep 1360731 = 2041097) B2041097
theorem B7750637 : Blo 1360499 7750637 := bstep (se 3 (by rfl) ⟨1453244, by rfl⟩ : syracuseStep 7750637 = 2906489) B2906489
theorem B11625545 : Blo 1360499 11625545 := bstep (se 2 (by rfl) ⟨4359579, by rfl⟩ : syracuseStep 11625545 = 8719159) B8719159
theorem B765338705 : Blo 1360499 765338705 := bstep (se 2 (by rfl) ⟨287002014, by rfl⟩ : syracuseStep 765338705 = 574004029) B574004029
theorem B3065057 : Blo 1360499 3065057 := bstep (se 2 (by rfl) ⟨1149396, by rfl⟩ : syracuseStep 3065057 = 2298793) B2298793
theorem B2041343 : Blo 1360499 2041343 := bstep (se 1 (by rfl) ⟨1531007, by rfl⟩ : syracuseStep 2041343 = 3062015) B3062015
theorem B3270223 : Blo 1360499 3270223 := bstep (se 1 (by rfl) ⟨2452667, by rfl⟩ : syracuseStep 3270223 = 4905335) B4905335
theorem B1361767 : Blo 1360499 1361767 := bstep (se 1 (by rfl) ⟨1021325, by rfl⟩ : syracuseStep 1361767 = 2042651) B2042651
theorem B1361919 : Blo 1360499 1361919 := bstep (se 1 (by rfl) ⟨1021439, by rfl⟩ : syracuseStep 1361919 = 2042879) B2042879
theorem B10341107 : Blo 1360499 10341107 := bstep (se 1 (by rfl) ⟨7755830, by rfl⟩ : syracuseStep 10341107 = 15511661) B15511661
theorem B377441207 : Blo 1360499 377441207 := bstep (se 1 (by rfl) ⟨283080905, by rfl⟩ : syracuseStep 377441207 = 566161811) B566161811
theorem B2042873 : Blo 1360499 2042873 := bstep (se 2 (by rfl) ⟨766077, by rfl⟩ : syracuseStep 2042873 = 1532155) B1532155
theorem B2297551 : Blo 1360499 2297551 := bstep (se 1 (by rfl) ⟨1723163, by rfl⟩ : syracuseStep 2297551 = 3446327) B3446327
theorem B172290341 : Blo 1360499 172290341 := bstep (se 4 (by rfl) ⟨16152219, by rfl⟩ : syracuseStep 172290341 = 32304439) B32304439
theorem B2298415 : Blo 1360499 2298415 := bstep (se 1 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 2298415 = 3447623) B3447623
theorem B23278427 : Blo 1360499 23278427 := bstep (se 1 (by rfl) ⟨17458820, by rfl⟩ : syracuseStep 23278427 = 34917641) B34917641
theorem B5166787 : Blo 1360499 5166787 := bstep (se 1 (by rfl) ⟨3875090, by rfl⟩ : syracuseStep 5166787 = 7750181) B7750181
theorem B5168063 : Blo 1360499 5168063 := bstep (se 1 (by rfl) ⟨3876047, by rfl⟩ : syracuseStep 5168063 = 7752095) B7752095
theorem B5815439 : Blo 1360499 5815439 := bstep (se 1 (by rfl) ⟨4361579, by rfl⟩ : syracuseStep 5815439 = 8723159) B8723159
theorem B26517041 : Blo 1360499 26517041 := bstep (se 2 (by rfl) ⟨9943890, by rfl⟩ : syracuseStep 26517041 = 19887781) B19887781
theorem B26181467 : Blo 1360499 26181467 := bstep (se 1 (by rfl) ⟨19636100, by rfl⟩ : syracuseStep 26181467 = 39272201) B39272201
theorem B114860227 : Blo 1360499 114860227 := bstep (se 1 (by rfl) ⟨86145170, by rfl⟩ : syracuseStep 114860227 = 172290341) B172290341
theorem B17441189 : Blo 1360499 17441189 := bstep (se 4 (by rfl) ⟨1635111, by rfl⟩ : syracuseStep 17441189 = 3270223) B3270223
theorem B7750363 : Blo 1360499 7750363 := bstep (se 1 (by rfl) ⟨5812772, by rfl⟩ : syracuseStep 7750363 = 11625545) B11625545
theorem B3064553 : Blo 1360499 3064553 := bstep (se 2 (by rfl) ⟨1149207, by rfl⟩ : syracuseStep 3064553 = 2298415) B2298415
theorem B1360895 : Blo 1360499 1360895 := bstep (se 1 (by rfl) ⟨1020671, by rfl⟩ : syracuseStep 1360895 = 2041343) B2041343
theorem B251627471 : Blo 1360499 251627471 := bstep (se 1 (by rfl) ⟨188720603, by rfl⟩ : syracuseStep 251627471 = 377441207) B377441207
theorem B1361915 : Blo 1360499 1361915 := bstep (se 1 (by rfl) ⟨1021436, by rfl⟩ : syracuseStep 1361915 = 2042873) B2042873
theorem B3876959 : Blo 1360499 3876959 := bstep (se 1 (by rfl) ⟨2907719, by rfl⟩ : syracuseStep 3876959 = 5815439) B5815439
theorem B15518951 : Blo 1360499 15518951 := bstep (se 1 (by rfl) ⟨11639213, by rfl⟩ : syracuseStep 15518951 = 23278427) B23278427
theorem B510225803 : Blo 1360499 510225803 := bstep (se 1 (by rfl) ⟨382669352, by rfl⟩ : syracuseStep 510225803 = 765338705) B765338705
theorem B2043371 : Blo 1360499 2043371 := bstep (se 1 (by rfl) ⟨1532528, by rfl⟩ : syracuseStep 2043371 = 3065057) B3065057
theorem B6894071 : Blo 1360499 6894071 := bstep (se 1 (by rfl) ⟨5170553, by rfl⟩ : syracuseStep 6894071 = 10341107) B10341107
theorem B3445375 : Blo 1360499 3445375 := bstep (se 1 (by rfl) ⟨2584031, by rfl⟩ : syracuseStep 3445375 = 5168063) B5168063
theorem B17454311 : Blo 1360499 17454311 := bstep (se 1 (by rfl) ⟨13090733, by rfl⟩ : syracuseStep 17454311 = 26181467) B26181467
theorem B5167091 : Blo 1360499 5167091 := bstep (se 1 (by rfl) ⟨3875318, by rfl⟩ : syracuseStep 5167091 = 7750637) B7750637
theorem B6889049 : Blo 1360499 6889049 := bstep (se 2 (by rfl) ⟨2583393, by rfl⟩ : syracuseStep 6889049 = 5166787) B5166787
theorem B3063401 : Blo 1360499 3063401 := bstep (se 2 (by rfl) ⟨1148775, by rfl⟩ : syracuseStep 3063401 = 2297551) B2297551
theorem B17678027 : Blo 1360499 17678027 := bstep (se 1 (by rfl) ⟨13258520, by rfl⟩ : syracuseStep 17678027 = 26517041) B26517041
theorem B4596047 : Blo 1360499 4596047 := bstep (se 1 (by rfl) ⟨3447035, by rfl⟩ : syracuseStep 4596047 = 6894071) B6894071
theorem B340150535 : Blo 1360499 340150535 := bstep (se 1 (by rfl) ⟨255112901, by rfl⟩ : syracuseStep 340150535 = 510225803) B510225803
theorem B1362247 : Blo 1360499 1362247 := bstep (se 1 (by rfl) ⟨1021685, by rfl⟩ : syracuseStep 1362247 = 2043371) B2043371
theorem B2042267 : Blo 1360499 2042267 := bstep (se 1 (by rfl) ⟨1531700, by rfl⟩ : syracuseStep 2042267 = 3063401) B3063401
theorem B11627459 : Blo 1360499 11627459 := bstep (se 1 (by rfl) ⟨8720594, by rfl⟩ : syracuseStep 11627459 = 17441189) B17441189
theorem B2043035 : Blo 1360499 2043035 := bstep (se 1 (by rfl) ⟨1532276, by rfl⟩ : syracuseStep 2043035 = 3064553) B3064553
theorem B11636207 : Blo 1360499 11636207 := bstep (se 1 (by rfl) ⟨8727155, by rfl⟩ : syracuseStep 11636207 = 17454311) B17454311
theorem B10333817 : Blo 1360499 10333817 := bstep (se 2 (by rfl) ⟨3875181, by rfl⟩ : syracuseStep 10333817 = 7750363) B7750363
theorem B167751647 : Blo 1360499 167751647 := bstep (se 1 (by rfl) ⟨125813735, by rfl⟩ : syracuseStep 167751647 = 251627471) B251627471
theorem B3444727 : Blo 1360499 3444727 := bstep (se 1 (by rfl) ⟨2583545, by rfl⟩ : syracuseStep 3444727 = 5167091) B5167091
theorem B2584639 : Blo 1360499 2584639 := bstep (se 1 (by rfl) ⟨1938479, by rfl⟩ : syracuseStep 2584639 = 3876959) B3876959
theorem B4592699 : Blo 1360499 4592699 := bstep (se 1 (by rfl) ⟨3444524, by rfl⟩ : syracuseStep 4592699 = 6889049) B6889049
theorem B11785351 : Blo 1360499 11785351 := bstep (se 1 (by rfl) ⟨8839013, by rfl⟩ : syracuseStep 11785351 = 17678027) B17678027
theorem B153146969 : Blo 1360499 153146969 := bstep (se 2 (by rfl) ⟨57430113, by rfl⟩ : syracuseStep 153146969 = 114860227) B114860227
theorem B4593833 : Blo 1360499 4593833 := bstep (se 2 (by rfl) ⟨1722687, by rfl⟩ : syracuseStep 4593833 = 3445375) B3445375
theorem B10345967 : Blo 1360499 10345967 := bstep (se 1 (by rfl) ⟨7759475, by rfl⟩ : syracuseStep 10345967 = 15518951) B15518951
theorem B3064031 : Blo 1360499 3064031 := bstep (se 1 (by rfl) ⟨2298023, by rfl⟩ : syracuseStep 3064031 = 4596047) B4596047
theorem B102097979 : Blo 1360499 102097979 := bstep (se 1 (by rfl) ⟨76573484, by rfl⟩ : syracuseStep 102097979 = 153146969) B153146969
theorem B15713801 : Blo 1360499 15713801 := bstep (se 2 (by rfl) ⟨5892675, by rfl⟩ : syracuseStep 15713801 = 11785351) B11785351
theorem B1361511 : Blo 1360499 1361511 := bstep (se 1 (by rfl) ⟨1021133, by rfl⟩ : syracuseStep 1361511 = 2042267) B2042267
theorem B7751639 : Blo 1360499 7751639 := bstep (se 1 (by rfl) ⟨5813729, by rfl⟩ : syracuseStep 7751639 = 11627459) B11627459
theorem B1362023 : Blo 1360499 1362023 := bstep (se 1 (by rfl) ⟨1021517, by rfl⟩ : syracuseStep 1362023 = 2043035) B2043035
theorem B226767023 : Blo 1360499 226767023 := bstep (se 1 (by rfl) ⟨170075267, by rfl⟩ : syracuseStep 226767023 = 340150535) B340150535
theorem B111834431 : Blo 1360499 111834431 := bstep (se 1 (by rfl) ⟨83875823, by rfl⟩ : syracuseStep 111834431 = 167751647) B167751647
theorem B4592969 : Blo 1360499 4592969 := bstep (se 2 (by rfl) ⟨1722363, by rfl⟩ : syracuseStep 4592969 = 3444727) B3444727
theorem B3446185 : Blo 1360499 3446185 := bstep (se 2 (by rfl) ⟨1292319, by rfl⟩ : syracuseStep 3446185 = 2584639) B2584639
theorem B3061799 : Blo 1360499 3061799 := bstep (se 1 (by rfl) ⟨2296349, by rfl⟩ : syracuseStep 3061799 = 4592699) B4592699
theorem B3062555 : Blo 1360499 3062555 := bstep (se 1 (by rfl) ⟨2296916, by rfl⟩ : syracuseStep 3062555 = 4593833) B4593833
theorem B7757471 : Blo 1360499 7757471 := bstep (se 1 (by rfl) ⟨5818103, by rfl⟩ : syracuseStep 7757471 = 11636207) B11636207
theorem B6897311 : Blo 1360499 6897311 := bstep (se 1 (by rfl) ⟨5172983, by rfl⟩ : syracuseStep 6897311 = 10345967) B10345967
theorem B6889211 : Blo 1360499 6889211 := bstep (se 1 (by rfl) ⟨5166908, by rfl⟩ : syracuseStep 6889211 = 10333817) B10333817
theorem B74556287 : Blo 1360499 74556287 := bstep (se 1 (by rfl) ⟨55917215, by rfl⟩ : syracuseStep 74556287 = 111834431) B111834431
theorem B2041199 : Blo 1360499 2041199 := bstep (se 1 (by rfl) ⟨1530899, by rfl⟩ : syracuseStep 2041199 = 3061799) B3061799
theorem B2041703 : Blo 1360499 2041703 := bstep (se 1 (by rfl) ⟨1531277, by rfl⟩ : syracuseStep 2041703 = 3062555) B3062555
theorem B5171647 : Blo 1360499 5171647 := bstep (se 1 (by rfl) ⟨3878735, by rfl⟩ : syracuseStep 5171647 = 7757471) B7757471
theorem B4598207 : Blo 1360499 4598207 := bstep (se 1 (by rfl) ⟨3448655, by rfl⟩ : syracuseStep 4598207 = 6897311) B6897311
theorem B151178015 : Blo 1360499 151178015 := bstep (se 1 (by rfl) ⟨113383511, by rfl⟩ : syracuseStep 151178015 = 226767023) B226767023
theorem B2042687 : Blo 1360499 2042687 := bstep (se 1 (by rfl) ⟨1532015, by rfl⟩ : syracuseStep 2042687 = 3064031) B3064031
theorem B4592807 : Blo 1360499 4592807 := bstep (se 1 (by rfl) ⟨3444605, by rfl⟩ : syracuseStep 4592807 = 6889211) B6889211
theorem B68065319 : Blo 1360499 68065319 := bstep (se 1 (by rfl) ⟨51048989, by rfl⟩ : syracuseStep 68065319 = 102097979) B102097979
theorem B3061979 : Blo 1360499 3061979 := bstep (se 1 (by rfl) ⟨2296484, by rfl⟩ : syracuseStep 3061979 = 4592969) B4592969
theorem B10475867 : Blo 1360499 10475867 := bstep (se 1 (by rfl) ⟨7856900, by rfl⟩ : syracuseStep 10475867 = 15713801) B15713801
theorem B5167759 : Blo 1360499 5167759 := bstep (se 1 (by rfl) ⟨3875819, by rfl⟩ : syracuseStep 5167759 = 7751639) B7751639
theorem B4594913 : Blo 1360499 4594913 := bstep (se 2 (by rfl) ⟨1723092, by rfl⟩ : syracuseStep 4594913 = 3446185) B3446185
theorem B6890345 : Blo 1360499 6890345 := bstep (se 2 (by rfl) ⟨2583879, by rfl⟩ : syracuseStep 6890345 = 5167759) B5167759
theorem B1360799 : Blo 1360499 1360799 := bstep (se 1 (by rfl) ⟨1020599, by rfl⟩ : syracuseStep 1360799 = 2041199) B2041199
theorem B1361135 : Blo 1360499 1361135 := bstep (se 1 (by rfl) ⟨1020851, by rfl⟩ : syracuseStep 1361135 = 2041703) B2041703
theorem B2041319 : Blo 1360499 2041319 := bstep (se 1 (by rfl) ⟨1530989, by rfl⟩ : syracuseStep 2041319 = 3061979) B3061979
theorem B3065471 : Blo 1360499 3065471 := bstep (se 1 (by rfl) ⟨2299103, by rfl⟩ : syracuseStep 3065471 = 4598207) B4598207
theorem B1361791 : Blo 1360499 1361791 := bstep (se 1 (by rfl) ⟨1021343, by rfl⟩ : syracuseStep 1361791 = 2042687) B2042687
theorem B49704191 : Blo 1360499 49704191 := bstep (se 1 (by rfl) ⟨37278143, by rfl⟩ : syracuseStep 49704191 = 74556287) B74556287
theorem B6983911 : Blo 1360499 6983911 := bstep (se 1 (by rfl) ⟨5237933, by rfl⟩ : syracuseStep 6983911 = 10475867) B10475867
theorem B181507517 : Blo 1360499 181507517 := bstep (se 3 (by rfl) ⟨34032659, by rfl⟩ : syracuseStep 181507517 = 68065319) B68065319
theorem B6895529 : Blo 1360499 6895529 := bstep (se 2 (by rfl) ⟨2585823, by rfl⟩ : syracuseStep 6895529 = 5171647) B5171647
theorem B3061871 : Blo 1360499 3061871 := bstep (se 1 (by rfl) ⟨2296403, by rfl⟩ : syracuseStep 3061871 = 4592807) B4592807
theorem B100785343 : Blo 1360499 100785343 := bstep (se 1 (by rfl) ⟨75589007, by rfl⟩ : syracuseStep 100785343 = 151178015) B151178015
theorem B3063275 : Blo 1360499 3063275 := bstep (se 1 (by rfl) ⟨2297456, by rfl⟩ : syracuseStep 3063275 = 4594913) B4594913
theorem B121005011 : Blo 1360499 121005011 := bstep (se 1 (by rfl) ⟨90753758, by rfl⟩ : syracuseStep 121005011 = 181507517) B181507517
theorem B1360879 : Blo 1360499 1360879 := bstep (se 1 (by rfl) ⟨1020659, by rfl⟩ : syracuseStep 1360879 = 2041319) B2041319
theorem B4597019 : Blo 1360499 4597019 := bstep (se 1 (by rfl) ⟨3447764, by rfl⟩ : syracuseStep 4597019 = 6895529) B6895529
theorem B2041247 : Blo 1360499 2041247 := bstep (se 1 (by rfl) ⟨1530935, by rfl⟩ : syracuseStep 2041247 = 3061871) B3061871
theorem B2042183 : Blo 1360499 2042183 := bstep (se 1 (by rfl) ⟨1531637, by rfl⟩ : syracuseStep 2042183 = 3063275) B3063275
theorem B2043647 : Blo 1360499 2043647 := bstep (se 1 (by rfl) ⟨1532735, by rfl⟩ : syracuseStep 2043647 = 3065471) B3065471
theorem B9311881 : Blo 1360499 9311881 := bstep (se 2 (by rfl) ⟨3491955, by rfl⟩ : syracuseStep 9311881 = 6983911) B6983911
theorem B4593563 : Blo 1360499 4593563 := bstep (se 1 (by rfl) ⟨3445172, by rfl⟩ : syracuseStep 4593563 = 6890345) B6890345
theorem B134380457 : Blo 1360499 134380457 := bstep (se 2 (by rfl) ⟨50392671, by rfl⟩ : syracuseStep 134380457 = 100785343) B100785343
theorem B33136127 : Blo 1360499 33136127 := bstep (se 1 (by rfl) ⟨24852095, by rfl⟩ : syracuseStep 33136127 = 49704191) B49704191
theorem B3064679 : Blo 1360499 3064679 := bstep (se 1 (by rfl) ⟨2298509, by rfl⟩ : syracuseStep 3064679 = 4597019) B4597019
theorem B1360831 : Blo 1360499 1360831 := bstep (se 1 (by rfl) ⟨1020623, by rfl⟩ : syracuseStep 1360831 = 2041247) B2041247
theorem B1361455 : Blo 1360499 1361455 := bstep (se 1 (by rfl) ⟨1021091, by rfl⟩ : syracuseStep 1361455 = 2042183) B2042183
theorem B1362431 : Blo 1360499 1362431 := bstep (se 1 (by rfl) ⟨1021823, by rfl⟩ : syracuseStep 1362431 = 2043647) B2043647
theorem B80670007 : Blo 1360499 80670007 := bstep (se 1 (by rfl) ⟨60502505, by rfl⟩ : syracuseStep 80670007 = 121005011) B121005011
theorem B12415841 : Blo 1360499 12415841 := bstep (se 2 (by rfl) ⟨4655940, by rfl⟩ : syracuseStep 12415841 = 9311881) B9311881
theorem B22090751 : Blo 1360499 22090751 := bstep (se 1 (by rfl) ⟨16568063, by rfl⟩ : syracuseStep 22090751 = 33136127) B33136127
theorem B3062375 : Blo 1360499 3062375 := bstep (se 1 (by rfl) ⟨2296781, by rfl⟩ : syracuseStep 3062375 = 4593563) B4593563
theorem B89586971 : Blo 1360499 89586971 := bstep (se 1 (by rfl) ⟨67190228, by rfl⟩ : syracuseStep 89586971 = 134380457) B134380457
theorem B2041583 : Blo 1360499 2041583 := bstep (se 1 (by rfl) ⟨1531187, by rfl⟩ : syracuseStep 2041583 = 3062375) B3062375
theorem B8277227 : Blo 1360499 8277227 := bstep (se 1 (by rfl) ⟨6207920, by rfl⟩ : syracuseStep 8277227 = 12415841) B12415841
theorem B2043119 : Blo 1360499 2043119 := bstep (se 1 (by rfl) ⟨1532339, by rfl⟩ : syracuseStep 2043119 = 3064679) B3064679
theorem B59724647 : Blo 1360499 59724647 := bstep (se 1 (by rfl) ⟨44793485, by rfl⟩ : syracuseStep 59724647 = 89586971) B89586971
theorem B14727167 : Blo 1360499 14727167 := bstep (se 1 (by rfl) ⟨11045375, by rfl⟩ : syracuseStep 14727167 = 22090751) B22090751
theorem B107560009 : Blo 1360499 107560009 := bstep (se 2 (by rfl) ⟨40335003, by rfl⟩ : syracuseStep 107560009 = 80670007) B80670007
theorem B1361055 : Blo 1360499 1361055 := bstep (se 1 (by rfl) ⟨1020791, by rfl⟩ : syracuseStep 1361055 = 2041583) B2041583
theorem B1362079 : Blo 1360499 1362079 := bstep (se 1 (by rfl) ⟨1021559, by rfl⟩ : syracuseStep 1362079 = 2043119) B2043119
theorem B39816431 : Blo 1360499 39816431 := bstep (se 1 (by rfl) ⟨29862323, by rfl⟩ : syracuseStep 39816431 = 59724647) B59724647
theorem B9818111 : Blo 1360499 9818111 := bstep (se 1 (by rfl) ⟨7363583, by rfl⟩ : syracuseStep 9818111 = 14727167) B14727167
theorem B143413345 : Blo 1360499 143413345 := bstep (se 2 (by rfl) ⟨53780004, by rfl⟩ : syracuseStep 143413345 = 107560009) B107560009
theorem B5518151 : Blo 1360499 5518151 := bstep (se 1 (by rfl) ⟨4138613, by rfl⟩ : syracuseStep 5518151 = 8277227) B8277227
theorem B191217793 : Blo 1360499 191217793 := bstep (se 2 (by rfl) ⟨71706672, by rfl⟩ : syracuseStep 191217793 = 143413345) B143413345
theorem B3678767 : Blo 1360499 3678767 := bstep (se 1 (by rfl) ⟨2759075, by rfl⟩ : syracuseStep 3678767 = 5518151) B5518151
theorem B26544287 : Blo 1360499 26544287 := bstep (se 1 (by rfl) ⟨19908215, by rfl⟩ : syracuseStep 26544287 = 39816431) B39816431
theorem B6545407 : Blo 1360499 6545407 := bstep (se 1 (by rfl) ⟨4909055, by rfl⟩ : syracuseStep 6545407 = 9818111) B9818111
theorem B17696191 : Blo 1360499 17696191 := bstep (se 1 (by rfl) ⟨13272143, by rfl⟩ : syracuseStep 17696191 = 26544287) B26544287
theorem B8727209 : Blo 1360499 8727209 := bstep (se 2 (by rfl) ⟨3272703, by rfl⟩ : syracuseStep 8727209 = 6545407) B6545407
theorem B2452511 : Blo 1360499 2452511 := bstep (se 1 (by rfl) ⟨1839383, by rfl⟩ : syracuseStep 2452511 = 3678767) B3678767
theorem B254957057 : Blo 1360499 254957057 := bstep (se 2 (by rfl) ⟨95608896, by rfl⟩ : syracuseStep 254957057 = 191217793) B191217793
theorem B5818139 : Blo 1360499 5818139 := bstep (se 1 (by rfl) ⟨4363604, by rfl⟩ : syracuseStep 5818139 = 8727209) B8727209
theorem B23594921 : Blo 1360499 23594921 := bstep (se 2 (by rfl) ⟨8848095, by rfl⟩ : syracuseStep 23594921 = 17696191) B17696191
theorem B169971371 : Blo 1360499 169971371 := bstep (se 1 (by rfl) ⟨127478528, by rfl⟩ : syracuseStep 169971371 = 254957057) B254957057
theorem B1635007 : Blo 1360499 1635007 := bstep (se 1 (by rfl) ⟨1226255, by rfl⟩ : syracuseStep 1635007 = 2452511) B2452511
theorem B2180009 : Blo 1360499 2180009 := bstep (se 2 (by rfl) ⟨817503, by rfl⟩ : syracuseStep 2180009 = 1635007) B1635007
theorem B15729947 : Blo 1360499 15729947 := bstep (se 1 (by rfl) ⟨11797460, by rfl⟩ : syracuseStep 15729947 = 23594921) B23594921
theorem B113314247 : Blo 1360499 113314247 := bstep (se 1 (by rfl) ⟨84985685, by rfl⟩ : syracuseStep 113314247 = 169971371) B169971371
theorem B3878759 : Blo 1360499 3878759 := bstep (se 1 (by rfl) ⟨2909069, by rfl⟩ : syracuseStep 3878759 = 5818139) B5818139
theorem B10486631 : Blo 1360499 10486631 := bstep (se 1 (by rfl) ⟨7864973, by rfl⟩ : syracuseStep 10486631 = 15729947) B15729947
theorem B1453339 : Blo 1360499 1453339 := bstep (se 1 (by rfl) ⟨1090004, by rfl⟩ : syracuseStep 1453339 = 2180009) B2180009
theorem B75542831 : Blo 1360499 75542831 := bstep (se 1 (by rfl) ⟨56657123, by rfl⟩ : syracuseStep 75542831 = 113314247) B113314247
theorem B2585839 : Blo 1360499 2585839 := bstep (se 1 (by rfl) ⟨1939379, by rfl⟩ : syracuseStep 2585839 = 3878759) B3878759
theorem B1937785 : Blo 1360499 1937785 := bstep (se 2 (by rfl) ⟨726669, by rfl⟩ : syracuseStep 1937785 = 1453339) B1453339
theorem B27964349 : Blo 1360499 27964349 := bstep (se 3 (by rfl) ⟨5243315, by rfl⟩ : syracuseStep 27964349 = 10486631) B10486631
theorem B50361887 : Blo 1360499 50361887 := bstep (se 1 (by rfl) ⟨37771415, by rfl⟩ : syracuseStep 50361887 = 75542831) B75542831
theorem B3447785 : Blo 1360499 3447785 := bstep (se 2 (by rfl) ⟨1292919, by rfl⟩ : syracuseStep 3447785 = 2585839) B2585839
theorem B2583713 : Blo 1360499 2583713 := bstep (se 2 (by rfl) ⟨968892, by rfl⟩ : syracuseStep 2583713 = 1937785) B1937785
theorem B33574591 : Blo 1360499 33574591 := bstep (se 1 (by rfl) ⟨25180943, by rfl⟩ : syracuseStep 33574591 = 50361887) B50361887
theorem B2298523 : Blo 1360499 2298523 := bstep (se 1 (by rfl) ⟨1723892, by rfl⟩ : syracuseStep 2298523 = 3447785) B3447785
theorem B18642899 : Blo 1360499 18642899 := bstep (se 1 (by rfl) ⟨13982174, by rfl⟩ : syracuseStep 18642899 = 27964349) B27964349
theorem B3064697 : Blo 1360499 3064697 := bstep (se 2 (by rfl) ⟨1149261, by rfl⟩ : syracuseStep 3064697 = 2298523) B2298523
theorem B12428599 : Blo 1360499 12428599 := bstep (se 1 (by rfl) ⟨9321449, by rfl⟩ : syracuseStep 12428599 = 18642899) B18642899
theorem B1722475 : Blo 1360499 1722475 := bstep (se 1 (by rfl) ⟨1291856, by rfl⟩ : syracuseStep 1722475 = 2583713) B2583713
theorem B44766121 : Blo 1360499 44766121 := bstep (se 2 (by rfl) ⟨16787295, by rfl⟩ : syracuseStep 44766121 = 33574591) B33574591
theorem B59688161 : Blo 1360499 59688161 := bstep (se 2 (by rfl) ⟨22383060, by rfl⟩ : syracuseStep 59688161 = 44766121) B44766121
theorem B2296633 : Blo 1360499 2296633 := bstep (se 2 (by rfl) ⟨861237, by rfl⟩ : syracuseStep 2296633 = 1722475) B1722475
theorem B2043131 : Blo 1360499 2043131 := bstep (se 1 (by rfl) ⟨1532348, by rfl⟩ : syracuseStep 2043131 = 3064697) B3064697
theorem B16571465 : Blo 1360499 16571465 := bstep (se 2 (by rfl) ⟨6214299, by rfl⟩ : syracuseStep 16571465 = 12428599) B12428599
theorem B1362087 : Blo 1360499 1362087 := bstep (se 1 (by rfl) ⟨1021565, by rfl⟩ : syracuseStep 1362087 = 2043131) B2043131
theorem B39792107 : Blo 1360499 39792107 := bstep (se 1 (by rfl) ⟨29844080, by rfl⟩ : syracuseStep 39792107 = 59688161) B59688161
theorem B11047643 : Blo 1360499 11047643 := bstep (se 1 (by rfl) ⟨8285732, by rfl⟩ : syracuseStep 11047643 = 16571465) B16571465
theorem B3062177 : Blo 1360499 3062177 := bstep (se 2 (by rfl) ⟨1148316, by rfl⟩ : syracuseStep 3062177 = 2296633) B2296633
theorem B7365095 : Blo 1360499 7365095 := bstep (se 1 (by rfl) ⟨5523821, by rfl⟩ : syracuseStep 7365095 = 11047643) B11047643
theorem B2041451 : Blo 1360499 2041451 := bstep (se 1 (by rfl) ⟨1531088, by rfl⟩ : syracuseStep 2041451 = 3062177) B3062177
theorem B26528071 : Blo 1360499 26528071 := bstep (se 1 (by rfl) ⟨19896053, by rfl⟩ : syracuseStep 26528071 = 39792107) B39792107
theorem B1360967 : Blo 1360499 1360967 := bstep (se 1 (by rfl) ⟨1020725, by rfl⟩ : syracuseStep 1360967 = 2041451) B2041451
theorem B4910063 : Blo 1360499 4910063 := bstep (se 1 (by rfl) ⟨3682547, by rfl⟩ : syracuseStep 4910063 = 7365095) B7365095
theorem B35370761 : Blo 1360499 35370761 := bstep (se 2 (by rfl) ⟨13264035, by rfl⟩ : syracuseStep 35370761 = 26528071) B26528071
theorem B13093501 : Blo 1360499 13093501 := bstep (se 3 (by rfl) ⟨2455031, by rfl⟩ : syracuseStep 13093501 = 4910063) B4910063
theorem B94322029 : Blo 1360499 94322029 := bstep (se 3 (by rfl) ⟨17685380, by rfl⟩ : syracuseStep 94322029 = 35370761) B35370761
theorem B17458001 : Blo 1360499 17458001 := bstep (se 2 (by rfl) ⟨6546750, by rfl⟩ : syracuseStep 17458001 = 13093501) B13093501
theorem B125762705 : Blo 1360499 125762705 := bstep (se 2 (by rfl) ⟨47161014, by rfl⟩ : syracuseStep 125762705 = 94322029) B94322029
theorem B83841803 : Blo 1360499 83841803 := bstep (se 1 (by rfl) ⟨62881352, by rfl⟩ : syracuseStep 83841803 = 125762705) B125762705
theorem B11638667 : Blo 1360499 11638667 := bstep (se 1 (by rfl) ⟨8729000, by rfl⟩ : syracuseStep 11638667 = 17458001) B17458001
theorem B55894535 : Blo 1360499 55894535 := bstep (se 1 (by rfl) ⟨41920901, by rfl⟩ : syracuseStep 55894535 = 83841803) B83841803
theorem B7759111 : Blo 1360499 7759111 := bstep (se 1 (by rfl) ⟨5819333, by rfl⟩ : syracuseStep 7759111 = 11638667) B11638667
theorem B37263023 : Blo 1360499 37263023 := bstep (se 1 (by rfl) ⟨27947267, by rfl⟩ : syracuseStep 37263023 = 55894535) B55894535
theorem B10345481 : Blo 1360499 10345481 := bstep (se 2 (by rfl) ⟨3879555, by rfl⟩ : syracuseStep 10345481 = 7759111) B7759111
theorem B24842015 : Blo 1360499 24842015 := bstep (se 1 (by rfl) ⟨18631511, by rfl⟩ : syracuseStep 24842015 = 37263023) B37263023
theorem B6896987 : Blo 1360499 6896987 := bstep (se 1 (by rfl) ⟨5172740, by rfl⟩ : syracuseStep 6896987 = 10345481) B10345481
theorem B4597991 : Blo 1360499 4597991 := bstep (se 1 (by rfl) ⟨3448493, by rfl⟩ : syracuseStep 4597991 = 6896987) B6896987
theorem B16561343 : Blo 1360499 16561343 := bstep (se 1 (by rfl) ⟨12421007, by rfl⟩ : syracuseStep 16561343 = 24842015) B24842015
theorem B3065327 : Blo 1360499 3065327 := bstep (se 1 (by rfl) ⟨2298995, by rfl⟩ : syracuseStep 3065327 = 4597991) B4597991
theorem B11040895 : Blo 1360499 11040895 := bstep (se 1 (by rfl) ⟨8280671, by rfl⟩ : syracuseStep 11040895 = 16561343) B16561343
theorem B14721193 : Blo 1360499 14721193 := bstep (se 2 (by rfl) ⟨5520447, by rfl⟩ : syracuseStep 14721193 = 11040895) B11040895
theorem B2043551 : Blo 1360499 2043551 := bstep (se 1 (by rfl) ⟨1532663, by rfl⟩ : syracuseStep 2043551 = 3065327) B3065327
theorem B19628257 : Blo 1360499 19628257 := bstep (se 2 (by rfl) ⟨7360596, by rfl⟩ : syracuseStep 19628257 = 14721193) B14721193
theorem B1362367 : Blo 1360499 1362367 := bstep (se 1 (by rfl) ⟨1021775, by rfl⟩ : syracuseStep 1362367 = 2043551) B2043551
theorem B26171009 : Blo 1360499 26171009 := bstep (se 2 (by rfl) ⟨9814128, by rfl⟩ : syracuseStep 26171009 = 19628257) B19628257
theorem B17447339 : Blo 1360499 17447339 := bstep (se 1 (by rfl) ⟨13085504, by rfl⟩ : syracuseStep 17447339 = 26171009) B26171009
theorem B11631559 : Blo 1360499 11631559 := bstep (se 1 (by rfl) ⟨8723669, by rfl⟩ : syracuseStep 11631559 = 17447339) B17447339
theorem B15508745 : Blo 1360499 15508745 := bstep (se 2 (by rfl) ⟨5815779, by rfl⟩ : syracuseStep 15508745 = 11631559) B11631559
theorem B10339163 : Blo 1360499 10339163 := bstep (se 1 (by rfl) ⟨7754372, by rfl⟩ : syracuseStep 10339163 = 15508745) B15508745
theorem B6892775 : Blo 1360499 6892775 := bstep (se 1 (by rfl) ⟨5169581, by rfl⟩ : syracuseStep 6892775 = 10339163) B10339163
theorem B4595183 : Blo 1360499 4595183 := bstep (se 1 (by rfl) ⟨3446387, by rfl⟩ : syracuseStep 4595183 = 6892775) B6892775
theorem B3063455 : Blo 1360499 3063455 := bstep (se 1 (by rfl) ⟨2297591, by rfl⟩ : syracuseStep 3063455 = 4595183) B4595183
theorem B2042303 : Blo 1360499 2042303 := bstep (se 1 (by rfl) ⟨1531727, by rfl⟩ : syracuseStep 2042303 = 3063455) B3063455
theorem B1361535 : Blo 1360499 1361535 := bstep (se 1 (by rfl) ⟨1021151, by rfl⟩ : syracuseStep 1361535 = 2042303) B2042303

theorem C0 (j : ℕ) (h1 : 340124 ≤ j) (h2 : j ≤ 340624) : Blo 1360499 (4 * j + 3) := by
  interval_cases j
  · exact B1360499
  · exact B1360503
  · exact B1360507
  · exact B1360511
  · exact B1360515
  · exact B1360519
  · exact B1360523
  · exact B1360527
  · exact B1360531
  · exact B1360535
  · exact B1360539
  · exact B1360543
  · exact B1360547
  · exact B1360551
  · exact B1360555
  · exact B1360559
  · exact B1360563
  · exact B1360567
  · exact B1360571
  · exact B1360575
  · exact B1360579
  · exact B1360583
  · exact B1360587
  · exact B1360591
  · exact B1360595
  · exact B1360599
  · exact B1360603
  · exact B1360607
  · exact B1360611
  · exact B1360615
  · exact B1360619
  · exact B1360623
  · exact B1360627
  · exact B1360631
  · exact B1360635
  · exact B1360639
  · exact B1360643
  · exact B1360647
  · exact B1360651
  · exact B1360655
  · exact B1360659
  · exact B1360663
  · exact B1360667
  · exact B1360671
  · exact B1360675
  · exact B1360679
  · exact B1360683
  · exact B1360687
  · exact B1360691
  · exact B1360695
  · exact B1360699
  · exact B1360703
  · exact B1360707
  · exact B1360711
  · exact B1360715
  · exact B1360719
  · exact B1360723
  · exact B1360727
  · exact B1360731
  · exact B1360735
  · exact B1360739
  · exact B1360743
  · exact B1360747
  · exact B1360751
  · exact B1360755
  · exact B1360759
  · exact B1360763
  · exact B1360767
  · exact B1360771
  · exact B1360775
  · exact B1360779
  · exact B1360783
  · exact B1360787
  · exact B1360791
  · exact B1360795
  · exact B1360799
  · exact B1360803
  · exact B1360807
  · exact B1360811
  · exact B1360815
  · exact B1360819
  · exact B1360823
  · exact B1360827
  · exact B1360831
  · exact B1360835
  · exact B1360839
  · exact B1360843
  · exact B1360847
  · exact B1360851
  · exact B1360855
  · exact B1360859
  · exact B1360863
  · exact B1360867
  · exact B1360871
  · exact B1360875
  · exact B1360879
  · exact B1360883
  · exact B1360887
  · exact B1360891
  · exact B1360895
  · exact B1360899
  · exact B1360903
  · exact B1360907
  · exact B1360911
  · exact B1360915
  · exact B1360919
  · exact B1360923
  · exact B1360927
  · exact B1360931
  · exact B1360935
  · exact B1360939
  · exact B1360943
  · exact B1360947
  · exact B1360951
  · exact B1360955
  · exact B1360959
  · exact B1360963
  · exact B1360967
  · exact B1360971
  · exact B1360975
  · exact B1360979
  · exact B1360983
  · exact B1360987
  · exact B1360991
  · exact B1360995
  · exact B1360999
  · exact B1361003
  · exact B1361007
  · exact B1361011
  · exact B1361015
  · exact B1361019
  · exact B1361023
  · exact B1361027
  · exact B1361031
  · exact B1361035
  · exact B1361039
  · exact B1361043
  · exact B1361047
  · exact B1361051
  · exact B1361055
  · exact B1361059
  · exact B1361063
  · exact B1361067
  · exact B1361071
  · exact B1361075
  · exact B1361079
  · exact B1361083
  · exact B1361087
  · exact B1361091
  · exact B1361095
  · exact B1361099
  · exact B1361103
  · exact B1361107
  · exact B1361111
  · exact B1361115
  · exact B1361119
  · exact B1361123
  · exact B1361127
  · exact B1361131
  · exact B1361135
  · exact B1361139
  · exact B1361143
  · exact B1361147
  · exact B1361151
  · exact B1361155
  · exact B1361159
  · exact B1361163
  · exact B1361167
  · exact B1361171
  · exact B1361175
  · exact B1361179
  · exact B1361183
  · exact B1361187
  · exact B1361191
  · exact B1361195
  · exact B1361199
  · exact B1361203
  · exact B1361207
  · exact B1361211
  · exact B1361215
  · exact B1361219
  · exact B1361223
  · exact B1361227
  · exact B1361231
  · exact B1361235
  · exact B1361239
  · exact B1361243
  · exact B1361247
  · exact B1361251
  · exact B1361255
  · exact B1361259
  · exact B1361263
  · exact B1361267
  · exact B1361271
  · exact B1361275
  · exact B1361279
  · exact B1361283
  · exact B1361287
  · exact B1361291
  · exact B1361295
  · exact B1361299
  · exact B1361303
  · exact B1361307
  · exact B1361311
  · exact B1361315
  · exact B1361319
  · exact B1361323
  · exact B1361327
  · exact B1361331
  · exact B1361335
  · exact B1361339
  · exact B1361343
  · exact B1361347
  · exact B1361351
  · exact B1361355
  · exact B1361359
  · exact B1361363
  · exact B1361367
  · exact B1361371
  · exact B1361375
  · exact B1361379
  · exact B1361383
  · exact B1361387
  · exact B1361391
  · exact B1361395
  · exact B1361399
  · exact B1361403
  · exact B1361407
  · exact B1361411
  · exact B1361415
  · exact B1361419
  · exact B1361423
  · exact B1361427
  · exact B1361431
  · exact B1361435
  · exact B1361439
  · exact B1361443
  · exact B1361447
  · exact B1361451
  · exact B1361455
  · exact B1361459
  · exact B1361463
  · exact B1361467
  · exact B1361471
  · exact B1361475
  · exact B1361479
  · exact B1361483
  · exact B1361487
  · exact B1361491
  · exact B1361495
  · exact B1361499
  · exact B1361503
  · exact B1361507
  · exact B1361511
  · exact B1361515
  · exact B1361519
  · exact B1361523
  · exact B1361527
  · exact B1361531
  · exact B1361535
  · exact B1361539
  · exact B1361543
  · exact B1361547
  · exact B1361551
  · exact B1361555
  · exact B1361559
  · exact B1361563
  · exact B1361567
  · exact B1361571
  · exact B1361575
  · exact B1361579
  · exact B1361583
  · exact B1361587
  · exact B1361591
  · exact B1361595
  · exact B1361599
  · exact B1361603
  · exact B1361607
  · exact B1361611
  · exact B1361615
  · exact B1361619
  · exact B1361623
  · exact B1361627
  · exact B1361631
  · exact B1361635
  · exact B1361639
  · exact B1361643
  · exact B1361647
  · exact B1361651
  · exact B1361655
  · exact B1361659
  · exact B1361663
  · exact B1361667
  · exact B1361671
  · exact B1361675
  · exact B1361679
  · exact B1361683
  · exact B1361687
  · exact B1361691
  · exact B1361695
  · exact B1361699
  · exact B1361703
  · exact B1361707
  · exact B1361711
  · exact B1361715
  · exact B1361719
  · exact B1361723
  · exact B1361727
  · exact B1361731
  · exact B1361735
  · exact B1361739
  · exact B1361743
  · exact B1361747
  · exact B1361751
  · exact B1361755
  · exact B1361759
  · exact B1361763
  · exact B1361767
  · exact B1361771
  · exact B1361775
  · exact B1361779
  · exact B1361783
  · exact B1361787
  · exact B1361791
  · exact B1361795
  · exact B1361799
  · exact B1361803
  · exact B1361807
  · exact B1361811
  · exact B1361815
  · exact B1361819
  · exact B1361823
  · exact B1361827
  · exact B1361831
  · exact B1361835
  · exact B1361839
  · exact B1361843
  · exact B1361847
  · exact B1361851
  · exact B1361855
  · exact B1361859
  · exact B1361863
  · exact B1361867
  · exact B1361871
  · exact B1361875
  · exact B1361879
  · exact B1361883
  · exact B1361887
  · exact B1361891
  · exact B1361895
  · exact B1361899
  · exact B1361903
  · exact B1361907
  · exact B1361911
  · exact B1361915
  · exact B1361919
  · exact B1361923
  · exact B1361927
  · exact B1361931
  · exact B1361935
  · exact B1361939
  · exact B1361943
  · exact B1361947
  · exact B1361951
  · exact B1361955
  · exact B1361959
  · exact B1361963
  · exact B1361967
  · exact B1361971
  · exact B1361975
  · exact B1361979
  · exact B1361983
  · exact B1361987
  · exact B1361991
  · exact B1361995
  · exact B1361999
  · exact B1362003
  · exact B1362007
  · exact B1362011
  · exact B1362015
  · exact B1362019
  · exact B1362023
  · exact B1362027
  · exact B1362031
  · exact B1362035
  · exact B1362039
  · exact B1362043
  · exact B1362047
  · exact B1362051
  · exact B1362055
  · exact B1362059
  · exact B1362063
  · exact B1362067
  · exact B1362071
  · exact B1362075
  · exact B1362079
  · exact B1362083
  · exact B1362087
  · exact B1362091
  · exact B1362095
  · exact B1362099
  · exact B1362103
  · exact B1362107
  · exact B1362111
  · exact B1362115
  · exact B1362119
  · exact B1362123
  · exact B1362127
  · exact B1362131
  · exact B1362135
  · exact B1362139
  · exact B1362143
  · exact B1362147
  · exact B1362151
  · exact B1362155
  · exact B1362159
  · exact B1362163
  · exact B1362167
  · exact B1362171
  · exact B1362175
  · exact B1362179
  · exact B1362183
  · exact B1362187
  · exact B1362191
  · exact B1362195
  · exact B1362199
  · exact B1362203
  · exact B1362207
  · exact B1362211
  · exact B1362215
  · exact B1362219
  · exact B1362223
  · exact B1362227
  · exact B1362231
  · exact B1362235
  · exact B1362239
  · exact B1362243
  · exact B1362247
  · exact B1362251
  · exact B1362255
  · exact B1362259
  · exact B1362263
  · exact B1362267
  · exact B1362271
  · exact B1362275
  · exact B1362279
  · exact B1362283
  · exact B1362287
  · exact B1362291
  · exact B1362295
  · exact B1362299
  · exact B1362303
  · exact B1362307
  · exact B1362311
  · exact B1362315
  · exact B1362319
  · exact B1362323
  · exact B1362327
  · exact B1362331
  · exact B1362335
  · exact B1362339
  · exact B1362343
  · exact B1362347
  · exact B1362351
  · exact B1362355
  · exact B1362359
  · exact B1362363
  · exact B1362367
  · exact B1362371
  · exact B1362375
  · exact B1362379
  · exact B1362383
  · exact B1362387
  · exact B1362391
  · exact B1362395
  · exact B1362399
  · exact B1362403
  · exact B1362407
  · exact B1362411
  · exact B1362415
  · exact B1362419
  · exact B1362423
  · exact B1362427
  · exact B1362431
  · exact B1362435
  · exact B1362439
  · exact B1362443
  · exact B1362447
  · exact B1362451
  · exact B1362455
  · exact B1362459
  · exact B1362463
  · exact B1362467
  · exact B1362471
  · exact B1362475
  · exact B1362479
  · exact B1362483
  · exact B1362487
  · exact B1362491
  · exact B1362495
  · exact B1362499

theorem solution (m : ℕ) (hlo : 1360499 ≤ m) (hhi : m ≤ 1362499) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 340124 ≤ j := by omega
    have hj2 : j ≤ 340624 := by omega
    have hb : Blo 1360499 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
