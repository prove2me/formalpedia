-- Prove2me | solution 1 for syracuse_descends_range_1052612_1056612
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:26.926301+00:00
-- url     : https://prove2.me/submissions/67a83495-7957-46ad-ae7a-f34cf97ef5c9

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


theorem B5341301 : Blo 1052612 5341301 := bbase (se 5 (by rfl) ⟨250373, by rfl⟩ : syracuseStep 5341301 = 500747) (by norm_num)
theorem B3801269 : Blo 1052612 3801269 := bbase (se 5 (by rfl) ⟨178184, by rfl⟩ : syracuseStep 3801269 = 356369) (by norm_num)
theorem B22839509 : Blo 1052612 22839509 := bbase (se 7 (by rfl) ⟨267650, by rfl⟩ : syracuseStep 22839509 = 535301) (by norm_num)
theorem B1999093 : Blo 1052612 1999093 := bbase (se 5 (by rfl) ⟨93707, by rfl⟩ : syracuseStep 1999093 = 187415) (by norm_num)
theorem B3997957 : Blo 1052612 3997957 := bbase (se 4 (by rfl) ⟨374808, by rfl⟩ : syracuseStep 3997957 = 749617) (by norm_num)
theorem B1999237 : Blo 1052612 1999237 := bbase (se 4 (by rfl) ⟨187428, by rfl⟩ : syracuseStep 1999237 = 374857) (by norm_num)
theorem B1901045 : Blo 1052612 1901045 := bbase (se 5 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 1901045 = 178223) (by norm_num)
theorem B1999397 : Blo 1052612 1999397 := bbase (se 4 (by rfl) ⟨187443, by rfl⟩ : syracuseStep 1999397 = 374887) (by norm_num)
theorem B2163245 : Blo 1052612 2163245 := bbase (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) (by norm_num)
theorem B3998261 : Blo 1052612 3998261 := bbase (se 5 (by rfl) ⟨187418, by rfl⟩ : syracuseStep 3998261 = 374837) (by norm_num)
theorem B6095477 : Blo 1052612 6095477 := bbase (se 5 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 6095477 = 571451) (by norm_num)
theorem B1999541 : Blo 1052612 1999541 := bbase (se 5 (by rfl) ⟨93728, by rfl⟩ : syracuseStep 1999541 = 187457) (by norm_num)
theorem B7701205 : Blo 1052612 7701205 := bbase (se 7 (by rfl) ⟨90248, by rfl⟩ : syracuseStep 7701205 = 180497) (by norm_num)
theorem B1901333 : Blo 1052612 1901333 := bbase (se 6 (by rfl) ⟨44562, by rfl⟩ : syracuseStep 1901333 = 89125) (by norm_num)
theorem B3212149 : Blo 1052612 3212149 := bbase (se 5 (by rfl) ⟨150569, by rfl⟩ : syracuseStep 3212149 = 301139) (by norm_num)
theorem B1999829 : Blo 1052612 1999829 := bbase (se 7 (by rfl) ⟨23435, by rfl⟩ : syracuseStep 1999829 = 46871) (by norm_num)
theorem B6947893 : Blo 1052612 6947893 := bbase (se 5 (by rfl) ⟨325682, by rfl⟩ : syracuseStep 6947893 = 651365) (by norm_num)
theorem B1999981 : Blo 1052612 1999981 := bbase (se 3 (by rfl) ⟨374996, by rfl⟩ : syracuseStep 1999981 = 749993) (by norm_num)
theorem B1901765 : Blo 1052612 1901765 := bbase (se 4 (by rfl) ⟨178290, by rfl⟩ : syracuseStep 1901765 = 356581) (by norm_num)
theorem B1901909 : Blo 1052612 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B5342597 : Blo 1052612 5342597 := bbase (se 4 (by rfl) ⟨500868, by rfl⟩ : syracuseStep 5342597 = 1001737) (by norm_num)
theorem B2000285 : Blo 1052612 2000285 := bbase (se 3 (by rfl) ⟨375053, by rfl⟩ : syracuseStep 2000285 = 750107) (by norm_num)
theorem B2164205 : Blo 1052612 2164205 := bbase (se 3 (by rfl) ⟨405788, by rfl⟩ : syracuseStep 2164205 = 811577) (by norm_num)
theorem B5408309 : Blo 1052612 5408309 := bbase (se 5 (by rfl) ⟨253514, by rfl⟩ : syracuseStep 5408309 = 507029) (by norm_num)
theorem B2164429 : Blo 1052612 2164429 := bbase (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) (by norm_num)
theorem B11994965 : Blo 1052612 11994965 := bbase (se 9 (by rfl) ⟨35141, by rfl⟩ : syracuseStep 11994965 = 70283) (by norm_num)
theorem B3377173 : Blo 1052612 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B9635861 : Blo 1052612 9635861 := bbase (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) (by norm_num)
theorem B1804397 : Blo 1052612 1804397 := bbase (se 3 (by rfl) ⟨338324, by rfl⟩ : syracuseStep 1804397 = 676649) (by norm_num)
theorem B3049589 : Blo 1052612 3049589 := bbase (se 5 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 3049589 = 285899) (by norm_num)
theorem B2001037 : Blo 1052612 2001037 := bbase (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) (by norm_num)
theorem B1083541 : Blo 1052612 1083541 := bbase (se 6 (by rfl) ⟨25395, by rfl⟩ : syracuseStep 1083541 = 50791) (by norm_num)
theorem B7604405 : Blo 1052612 7604405 := bbase (se 5 (by rfl) ⟨356456, by rfl⟩ : syracuseStep 7604405 = 712913) (by norm_num)
theorem B5998805 : Blo 1052612 5998805 := bbase (se 7 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 5998805 = 140597) (by norm_num)
theorem B2001181 : Blo 1052612 2001181 := bbase (se 3 (by rfl) ⟨375221, by rfl⟩ : syracuseStep 2001181 = 750443) (by norm_num)
theorem B1902941 : Blo 1052612 1902941 := bbase (se 3 (by rfl) ⟨356801, by rfl⟩ : syracuseStep 1902941 = 713603) (by norm_num)
theorem B2001341 : Blo 1052612 2001341 := bbase (se 3 (by rfl) ⟨375251, by rfl⟩ : syracuseStep 2001341 = 750503) (by norm_num)
theorem B2001485 : Blo 1052612 2001485 := bbase (se 3 (by rfl) ⟨375278, by rfl⟩ : syracuseStep 2001485 = 750557) (by norm_num)
theorem B4000373 : Blo 1052612 4000373 := bbase (se 5 (by rfl) ⟨187517, by rfl⟩ : syracuseStep 4000373 = 375035) (by norm_num)
theorem B7998101 : Blo 1052612 7998101 := bbase (se 6 (by rfl) ⟨187455, by rfl⟩ : syracuseStep 7998101 = 374911) (by norm_num)
theorem B5343893 : Blo 1052612 5343893 := bbase (se 6 (by rfl) ⟨125247, by rfl⟩ : syracuseStep 5343893 = 250495) (by norm_num)
theorem B2001773 : Blo 1052612 2001773 := bbase (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) (by norm_num)
theorem B4000661 : Blo 1052612 4000661 := bbase (se 6 (by rfl) ⟨93765, by rfl⟩ : syracuseStep 4000661 = 187531) (by norm_num)
theorem B2001925 : Blo 1052612 2001925 := bbase (se 4 (by rfl) ⟨187680, by rfl⟩ : syracuseStep 2001925 = 375361) (by norm_num)
theorem B1608773 : Blo 1052612 1608773 := bbase (se 4 (by rfl) ⟨150822, by rfl⟩ : syracuseStep 1608773 = 301645) (by norm_num)
theorem B2002229 : Blo 1052612 2002229 := bbase (se 5 (by rfl) ⟨93854, by rfl⟩ : syracuseStep 2002229 = 187709) (by norm_num)
theorem B1806149 : Blo 1052612 1806149 := bbase (se 4 (by rfl) ⟨169326, by rfl⟩ : syracuseStep 1806149 = 338653) (by norm_num)
theorem B5345189 : Blo 1052612 5345189 := bbase (se 4 (by rfl) ⟨501111, by rfl⟩ : syracuseStep 5345189 = 1002223) (by norm_num)
theorem B2854853 : Blo 1052612 2854853 := bbase (se 4 (by rfl) ⟨267642, by rfl⟩ : syracuseStep 2854853 = 535285) (by norm_num)
theorem B2002981 : Blo 1052612 2002981 := bbase (se 4 (by rfl) ⟨187779, by rfl⟩ : syracuseStep 2002981 = 375559) (by norm_num)
theorem B4001845 : Blo 1052612 4001845 := bbase (se 5 (by rfl) ⟨187586, by rfl⟩ : syracuseStep 4001845 = 375173) (by norm_num)
theorem B2003125 : Blo 1052612 2003125 := bbase (se 5 (by rfl) ⟨93896, by rfl⟩ : syracuseStep 2003125 = 187793) (by norm_num)
theorem B2855189 : Blo 1052612 2855189 := bbase (se 6 (by rfl) ⟨66918, by rfl⟩ : syracuseStep 2855189 = 133837) (by norm_num)
theorem B2003285 : Blo 1052612 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B4002149 : Blo 1052612 4002149 := bbase (se 4 (by rfl) ⟨375201, by rfl⟩ : syracuseStep 4002149 = 750403) (by norm_num)
theorem B1216921 : Blo 1052612 1216921 := bbase (se 2 (by rfl) ⟨456345, by rfl⟩ : syracuseStep 1216921 = 912691) (by norm_num)
theorem B1184197 : Blo 1052612 1184197 := bbase (se 4 (by rfl) ⟨111018, by rfl⟩ : syracuseStep 1184197 = 222037) (by norm_num)
theorem B2003429 : Blo 1052612 2003429 := bbase (se 4 (by rfl) ⟨187821, by rfl⟩ : syracuseStep 2003429 = 375643) (by norm_num)
theorem B1184233 : Blo 1052612 1184233 := bbase (se 2 (by rfl) ⟨444087, by rfl⟩ : syracuseStep 1184233 = 888175) (by norm_num)
theorem B1184269 : Blo 1052612 1184269 := bbase (se 3 (by rfl) ⟨222050, by rfl⟩ : syracuseStep 1184269 = 444101) (by norm_num)
theorem B1184305 : Blo 1052612 1184305 := bbase (se 2 (by rfl) ⟨444114, by rfl⟩ : syracuseStep 1184305 = 888229) (by norm_num)
theorem B1184341 : Blo 1052612 1184341 := bbase (se 8 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 1184341 = 13879) (by norm_num)
theorem B1184377 : Blo 1052612 1184377 := bbase (se 2 (by rfl) ⟨444141, by rfl⟩ : syracuseStep 1184377 = 888283) (by norm_num)
theorem B1217173 : Blo 1052612 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B1184413 : Blo 1052612 1184413 := bbase (se 3 (by rfl) ⟨222077, by rfl⟩ : syracuseStep 1184413 = 444155) (by norm_num)
theorem B2134717 : Blo 1052612 2134717 := bbase (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) (by norm_num)
theorem B1184449 : Blo 1052612 1184449 := bbase (se 2 (by rfl) ⟨444168, by rfl⟩ : syracuseStep 1184449 = 888337) (by norm_num)
theorem B1184485 : Blo 1052612 1184485 := bbase (se 4 (by rfl) ⟨111045, by rfl⟩ : syracuseStep 1184485 = 222091) (by norm_num)
theorem B2003717 : Blo 1052612 2003717 := bbase (se 4 (by rfl) ⟨187848, by rfl⟩ : syracuseStep 2003717 = 375697) (by norm_num)
theorem B1184521 : Blo 1052612 1184521 := bbase (se 2 (by rfl) ⟨444195, by rfl⟩ : syracuseStep 1184521 = 888391) (by norm_num)
theorem B1184557 : Blo 1052612 1184557 := bbase (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) (by norm_num)
theorem B1184593 : Blo 1052612 1184593 := bbase (se 2 (by rfl) ⟨444222, by rfl⟩ : syracuseStep 1184593 = 888445) (by norm_num)
theorem B3380069 : Blo 1052612 3380069 := bbase (se 4 (by rfl) ⟨316881, by rfl⟩ : syracuseStep 3380069 = 633763) (by norm_num)
theorem B1184629 : Blo 1052612 1184629 := bbase (se 5 (by rfl) ⟨55529, by rfl⟩ : syracuseStep 1184629 = 111059) (by norm_num)
theorem B9016181 : Blo 1052612 9016181 := bbase (se 5 (by rfl) ⟨422633, by rfl⟩ : syracuseStep 9016181 = 845267) (by norm_num)
theorem B5411717 : Blo 1052612 5411717 := bbase (se 4 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 5411717 = 1014697) (by norm_num)
theorem B1807237 : Blo 1052612 1807237 := bbase (se 4 (by rfl) ⟨169428, by rfl⟩ : syracuseStep 1807237 = 338857) (by norm_num)
theorem B1184665 : Blo 1052612 1184665 := bbase (se 2 (by rfl) ⟨444249, by rfl⟩ : syracuseStep 1184665 = 888499) (by norm_num)
theorem B2003869 : Blo 1052612 2003869 := bbase (se 3 (by rfl) ⟨375725, by rfl⟩ : syracuseStep 2003869 = 751451) (by norm_num)
theorem B1184701 : Blo 1052612 1184701 := bbase (se 3 (by rfl) ⟨222131, by rfl⟩ : syracuseStep 1184701 = 444263) (by norm_num)
theorem B1184737 : Blo 1052612 1184737 := bbase (se 2 (by rfl) ⟨444276, by rfl⟩ : syracuseStep 1184737 = 888553) (by norm_num)
theorem B1184773 : Blo 1052612 1184773 := bbase (se 4 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 1184773 = 222145) (by norm_num)
theorem B1184809 : Blo 1052612 1184809 := bbase (se 2 (by rfl) ⟨444303, by rfl⟩ : syracuseStep 1184809 = 888607) (by norm_num)
theorem B1184845 : Blo 1052612 1184845 := bbase (se 3 (by rfl) ⟨222158, by rfl⟩ : syracuseStep 1184845 = 444317) (by norm_num)
theorem B1184881 : Blo 1052612 1184881 := bbase (se 2 (by rfl) ⟨444330, by rfl⟩ : syracuseStep 1184881 = 888661) (by norm_num)
theorem B2135173 : Blo 1052612 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B1184917 : Blo 1052612 1184917 := bbase (se 6 (by rfl) ⟨27771, by rfl⟩ : syracuseStep 1184917 = 55543) (by norm_num)
theorem B5346485 : Blo 1052612 5346485 := bbase (se 5 (by rfl) ⟨250616, by rfl⟩ : syracuseStep 5346485 = 501233) (by norm_num)
theorem B1184953 : Blo 1052612 1184953 := bbase (se 2 (by rfl) ⟨444357, by rfl⟩ : syracuseStep 1184953 = 888715) (by norm_num)
theorem B2004173 : Blo 1052612 2004173 := bbase (se 3 (by rfl) ⟨375782, by rfl⟩ : syracuseStep 2004173 = 751565) (by norm_num)
theorem B1184989 : Blo 1052612 1184989 := bbase (se 3 (by rfl) ⟨222185, by rfl⟩ : syracuseStep 1184989 = 444371) (by norm_num)
theorem B1185025 : Blo 1052612 1185025 := bbase (se 2 (by rfl) ⟨444384, by rfl⟩ : syracuseStep 1185025 = 888769) (by norm_num)
theorem B1185061 : Blo 1052612 1185061 := bbase (se 4 (by rfl) ⟨111099, by rfl⟩ : syracuseStep 1185061 = 222199) (by norm_num)
theorem B1185097 : Blo 1052612 1185097 := bbase (se 2 (by rfl) ⟨444411, by rfl⟩ : syracuseStep 1185097 = 888823) (by norm_num)
theorem B1185133 : Blo 1052612 1185133 := bbase (se 3 (by rfl) ⟨222212, by rfl⟩ : syracuseStep 1185133 = 444425) (by norm_num)
theorem B1185169 : Blo 1052612 1185169 := bbase (se 2 (by rfl) ⟨444438, by rfl⟩ : syracuseStep 1185169 = 888877) (by norm_num)
theorem B1185205 : Blo 1052612 1185205 := bbase (se 5 (by rfl) ⟨55556, by rfl⟩ : syracuseStep 1185205 = 111113) (by norm_num)
theorem B1185241 : Blo 1052612 1185241 := bbase (se 2 (by rfl) ⟨444465, by rfl⟩ : syracuseStep 1185241 = 888931) (by norm_num)
theorem B1185277 : Blo 1052612 1185277 := bbase (se 3 (by rfl) ⟨222239, by rfl⟩ : syracuseStep 1185277 = 444479) (by norm_num)
theorem B1185313 : Blo 1052612 1185313 := bbase (se 2 (by rfl) ⟨444492, by rfl⟩ : syracuseStep 1185313 = 888985) (by norm_num)
theorem B1185349 : Blo 1052612 1185349 := bbase (se 4 (by rfl) ⟨111126, by rfl⟩ : syracuseStep 1185349 = 222253) (by norm_num)
theorem B1185385 : Blo 1052612 1185385 := bbase (se 2 (by rfl) ⟨444519, by rfl⟩ : syracuseStep 1185385 = 889039) (by norm_num)
theorem B1185421 : Blo 1052612 1185421 := bbase (se 3 (by rfl) ⟨222266, by rfl⟩ : syracuseStep 1185421 = 444533) (by norm_num)
theorem B7214741 : Blo 1052612 7214741 := bbase (se 6 (by rfl) ⟨169095, by rfl⟩ : syracuseStep 7214741 = 338191) (by norm_num)
theorem B1185457 : Blo 1052612 1185457 := bbase (se 2 (by rfl) ⟨444546, by rfl⟩ : syracuseStep 1185457 = 889093) (by norm_num)
theorem B1185493 : Blo 1052612 1185493 := bbase (se 7 (by rfl) ⟨13892, by rfl⟩ : syracuseStep 1185493 = 27785) (by norm_num)
theorem B1185529 : Blo 1052612 1185529 := bbase (se 2 (by rfl) ⟨444573, by rfl⟩ : syracuseStep 1185529 = 889147) (by norm_num)
theorem B2135837 : Blo 1052612 2135837 := bbase (se 3 (by rfl) ⟨400469, by rfl⟩ : syracuseStep 2135837 = 800939) (by norm_num)
theorem B1185565 : Blo 1052612 1185565 := bbase (se 3 (by rfl) ⟨222293, by rfl⟩ : syracuseStep 1185565 = 444587) (by norm_num)
theorem B1185601 : Blo 1052612 1185601 := bbase (se 2 (by rfl) ⟨444600, by rfl⟩ : syracuseStep 1185601 = 889201) (by norm_num)
theorem B1185637 : Blo 1052612 1185637 := bbase (se 4 (by rfl) ⟨111153, by rfl⟩ : syracuseStep 1185637 = 222307) (by norm_num)
theorem B1185673 : Blo 1052612 1185673 := bbase (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) (by norm_num)
theorem B1185709 : Blo 1052612 1185709 := bbase (se 3 (by rfl) ⟨222320, by rfl⟩ : syracuseStep 1185709 = 444641) (by norm_num)
theorem B1578941 : Blo 1052612 1578941 := bbase (se 3 (by rfl) ⟨296051, by rfl⟩ : syracuseStep 1578941 = 592103) (by norm_num)
theorem B2004925 : Blo 1052612 2004925 := bbase (se 3 (by rfl) ⟨375923, by rfl⟩ : syracuseStep 2004925 = 751847) (by norm_num)
theorem B1185745 : Blo 1052612 1185745 := bbase (se 2 (by rfl) ⟨444654, by rfl⟩ : syracuseStep 1185745 = 889309) (by norm_num)
theorem B1578965 : Blo 1052612 1578965 := bbase (se 7 (by rfl) ⟨18503, by rfl⟩ : syracuseStep 1578965 = 37007) (by norm_num)
theorem B1578989 : Blo 1052612 1578989 := bbase (se 3 (by rfl) ⟨296060, by rfl⟩ : syracuseStep 1578989 = 592121) (by norm_num)
theorem B1185781 : Blo 1052612 1185781 := bbase (se 5 (by rfl) ⟨55583, by rfl⟩ : syracuseStep 1185781 = 111167) (by norm_num)
theorem B1579013 : Blo 1052612 1579013 := bbase (se 4 (by rfl) ⟨148032, by rfl⟩ : syracuseStep 1579013 = 296065) (by norm_num)
theorem B1185817 : Blo 1052612 1185817 := bbase (se 2 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 1185817 = 889363) (by norm_num)
theorem B1579037 : Blo 1052612 1579037 := bbase (se 3 (by rfl) ⟨296069, by rfl⟩ : syracuseStep 1579037 = 592139) (by norm_num)
theorem B1579061 : Blo 1052612 1579061 := bbase (se 5 (by rfl) ⟨74018, by rfl⟩ : syracuseStep 1579061 = 148037) (by norm_num)
theorem B1185853 : Blo 1052612 1185853 := bbase (se 3 (by rfl) ⟨222347, by rfl⟩ : syracuseStep 1185853 = 444695) (by norm_num)
theorem B1579085 : Blo 1052612 1579085 := bbase (se 3 (by rfl) ⟨296078, by rfl⟩ : syracuseStep 1579085 = 592157) (by norm_num)
theorem B2005069 : Blo 1052612 2005069 := bbase (se 3 (by rfl) ⟨375950, by rfl⟩ : syracuseStep 2005069 = 751901) (by norm_num)
theorem B1185889 : Blo 1052612 1185889 := bbase (se 2 (by rfl) ⟨444708, by rfl⟩ : syracuseStep 1185889 = 889417) (by norm_num)
theorem B1579109 : Blo 1052612 1579109 := bbase (se 4 (by rfl) ⟨148041, by rfl⟩ : syracuseStep 1579109 = 296083) (by norm_num)
theorem B3381365 : Blo 1052612 3381365 := bbase (se 5 (by rfl) ⟨158501, by rfl⟩ : syracuseStep 3381365 = 317003) (by norm_num)
theorem B1579133 : Blo 1052612 1579133 := bbase (se 3 (by rfl) ⟨296087, by rfl⟩ : syracuseStep 1579133 = 592175) (by norm_num)
theorem B1185925 : Blo 1052612 1185925 := bbase (se 4 (by rfl) ⟨111180, by rfl⟩ : syracuseStep 1185925 = 222361) (by norm_num)
theorem B1579157 : Blo 1052612 1579157 := bbase (se 6 (by rfl) ⟨37011, by rfl⟩ : syracuseStep 1579157 = 74023) (by norm_num)
theorem B1185961 : Blo 1052612 1185961 := bbase (se 2 (by rfl) ⟨444735, by rfl⟩ : syracuseStep 1185961 = 889471) (by norm_num)
theorem B1579181 : Blo 1052612 1579181 := bbase (se 3 (by rfl) ⟨296096, by rfl⟩ : syracuseStep 1579181 = 592193) (by norm_num)
theorem B1579205 : Blo 1052612 1579205 := bbase (se 4 (by rfl) ⟨148050, by rfl⟩ : syracuseStep 1579205 = 296101) (by norm_num)
theorem B1185997 : Blo 1052612 1185997 := bbase (se 3 (by rfl) ⟨222374, by rfl⟩ : syracuseStep 1185997 = 444749) (by norm_num)
theorem B1579229 : Blo 1052612 1579229 := bbase (se 3 (by rfl) ⟨296105, by rfl⟩ : syracuseStep 1579229 = 592211) (by norm_num)
theorem B2005229 : Blo 1052612 2005229 := bbase (se 3 (by rfl) ⟨375980, by rfl⟩ : syracuseStep 2005229 = 751961) (by norm_num)
theorem B1186033 : Blo 1052612 1186033 := bbase (se 2 (by rfl) ⟨444762, by rfl⟩ : syracuseStep 1186033 = 889525) (by norm_num)
theorem B1579253 : Blo 1052612 1579253 := bbase (se 5 (by rfl) ⟨74027, by rfl⟩ : syracuseStep 1579253 = 148055) (by norm_num)
theorem B1579277 : Blo 1052612 1579277 := bbase (se 3 (by rfl) ⟨296114, by rfl⟩ : syracuseStep 1579277 = 592229) (by norm_num)
theorem B1186069 : Blo 1052612 1186069 := bbase (se 6 (by rfl) ⟨27798, by rfl⟩ : syracuseStep 1186069 = 55597) (by norm_num)
theorem B1579301 : Blo 1052612 1579301 := bbase (se 4 (by rfl) ⟨148059, by rfl⟩ : syracuseStep 1579301 = 296119) (by norm_num)
theorem B1186105 : Blo 1052612 1186105 := bbase (se 2 (by rfl) ⟨444789, by rfl⟩ : syracuseStep 1186105 = 889579) (by norm_num)
theorem B1579325 : Blo 1052612 1579325 := bbase (se 3 (by rfl) ⟨296123, by rfl⟩ : syracuseStep 1579325 = 592247) (by norm_num)
theorem B1579349 : Blo 1052612 1579349 := bbase (se 10 (by rfl) ⟨2313, by rfl⟩ : syracuseStep 1579349 = 4627) (by norm_num)
theorem B1186141 : Blo 1052612 1186141 := bbase (se 3 (by rfl) ⟨222401, by rfl⟩ : syracuseStep 1186141 = 444803) (by norm_num)
theorem B1579373 : Blo 1052612 1579373 := bbase (se 3 (by rfl) ⟨296132, by rfl⟩ : syracuseStep 1579373 = 592265) (by norm_num)
theorem B2005373 : Blo 1052612 2005373 := bbase (se 3 (by rfl) ⟨376007, by rfl⟩ : syracuseStep 2005373 = 752015) (by norm_num)
theorem B1186177 : Blo 1052612 1186177 := bbase (se 2 (by rfl) ⟨444816, by rfl⟩ : syracuseStep 1186177 = 889633) (by norm_num)
theorem B1579397 : Blo 1052612 1579397 := bbase (se 4 (by rfl) ⟨148068, by rfl⟩ : syracuseStep 1579397 = 296137) (by norm_num)
theorem B2136469 : Blo 1052612 2136469 := bbase (se 6 (by rfl) ⟨50073, by rfl⟩ : syracuseStep 2136469 = 100147) (by norm_num)
theorem B1579421 : Blo 1052612 1579421 := bbase (se 3 (by rfl) ⟨296141, by rfl⟩ : syracuseStep 1579421 = 592283) (by norm_num)
theorem B1186213 : Blo 1052612 1186213 := bbase (se 4 (by rfl) ⟨111207, by rfl⟩ : syracuseStep 1186213 = 222415) (by norm_num)
theorem B4004261 : Blo 1052612 4004261 := bbase (se 4 (by rfl) ⟨375399, by rfl⟩ : syracuseStep 4004261 = 750799) (by norm_num)
theorem B1579445 : Blo 1052612 1579445 := bbase (se 5 (by rfl) ⟨74036, by rfl⟩ : syracuseStep 1579445 = 148073) (by norm_num)
theorem B5347781 : Blo 1052612 5347781 := bbase (se 4 (by rfl) ⟨501354, by rfl⟩ : syracuseStep 5347781 = 1002709) (by norm_num)
theorem B1186249 : Blo 1052612 1186249 := bbase (se 2 (by rfl) ⟨444843, by rfl⟩ : syracuseStep 1186249 = 889687) (by norm_num)
theorem B1579469 : Blo 1052612 1579469 := bbase (se 3 (by rfl) ⟨296150, by rfl⟩ : syracuseStep 1579469 = 592301) (by norm_num)
theorem B1579493 : Blo 1052612 1579493 := bbase (se 4 (by rfl) ⟨148077, by rfl⟩ : syracuseStep 1579493 = 296155) (by norm_num)
theorem B1186285 : Blo 1052612 1186285 := bbase (se 3 (by rfl) ⟨222428, by rfl⟩ : syracuseStep 1186285 = 444857) (by norm_num)
theorem B1579517 : Blo 1052612 1579517 := bbase (se 3 (by rfl) ⟨296159, by rfl⟩ : syracuseStep 1579517 = 592319) (by norm_num)
theorem B2529805 : Blo 1052612 2529805 := bbase (se 3 (by rfl) ⟨474338, by rfl⟩ : syracuseStep 2529805 = 948677) (by norm_num)
theorem B1186321 : Blo 1052612 1186321 := bbase (se 2 (by rfl) ⟨444870, by rfl⟩ : syracuseStep 1186321 = 889741) (by norm_num)
theorem B1579541 : Blo 1052612 1579541 := bbase (se 6 (by rfl) ⟨37020, by rfl⟩ : syracuseStep 1579541 = 74041) (by norm_num)
theorem B1579565 : Blo 1052612 1579565 := bbase (se 3 (by rfl) ⟨296168, by rfl⟩ : syracuseStep 1579565 = 592337) (by norm_num)
theorem B1186357 : Blo 1052612 1186357 := bbase (se 5 (by rfl) ⟨55610, by rfl⟩ : syracuseStep 1186357 = 111221) (by norm_num)
theorem B1579589 : Blo 1052612 1579589 := bbase (se 4 (by rfl) ⟨148086, by rfl⟩ : syracuseStep 1579589 = 296173) (by norm_num)
theorem B1186393 : Blo 1052612 1186393 := bbase (se 2 (by rfl) ⟨444897, by rfl⟩ : syracuseStep 1186393 = 889795) (by norm_num)
theorem B1579613 : Blo 1052612 1579613 := bbase (se 3 (by rfl) ⟨296177, by rfl⟩ : syracuseStep 1579613 = 592355) (by norm_num)
theorem B1579637 : Blo 1052612 1579637 := bbase (se 5 (by rfl) ⟨74045, by rfl⟩ : syracuseStep 1579637 = 148091) (by norm_num)
theorem B1186429 : Blo 1052612 1186429 := bbase (se 3 (by rfl) ⟨222455, by rfl⟩ : syracuseStep 1186429 = 444911) (by norm_num)
theorem B1579661 : Blo 1052612 1579661 := bbase (se 3 (by rfl) ⟨296186, by rfl⟩ : syracuseStep 1579661 = 592373) (by norm_num)
theorem B2529949 : Blo 1052612 2529949 := bbase (se 3 (by rfl) ⟨474365, by rfl⟩ : syracuseStep 2529949 = 948731) (by norm_num)
theorem B2005661 : Blo 1052612 2005661 := bbase (se 3 (by rfl) ⟨376061, by rfl⟩ : syracuseStep 2005661 = 752123) (by norm_num)
theorem B1186465 : Blo 1052612 1186465 := bbase (se 2 (by rfl) ⟨444924, by rfl⟩ : syracuseStep 1186465 = 889849) (by norm_num)
theorem B1579685 : Blo 1052612 1579685 := bbase (se 4 (by rfl) ⟨148095, by rfl⟩ : syracuseStep 1579685 = 296191) (by norm_num)
theorem B1579709 : Blo 1052612 1579709 := bbase (se 3 (by rfl) ⟨296195, by rfl⟩ : syracuseStep 1579709 = 592391) (by norm_num)
theorem B1186501 : Blo 1052612 1186501 := bbase (se 4 (by rfl) ⟨111234, by rfl⟩ : syracuseStep 1186501 = 222469) (by norm_num)
theorem B4004549 : Blo 1052612 4004549 := bbase (se 4 (by rfl) ⟨375426, by rfl⟩ : syracuseStep 4004549 = 750853) (by norm_num)
theorem B1579733 : Blo 1052612 1579733 := bbase (se 7 (by rfl) ⟨18512, by rfl⟩ : syracuseStep 1579733 = 37025) (by norm_num)
theorem B1186537 : Blo 1052612 1186537 := bbase (se 2 (by rfl) ⟨444951, by rfl⟩ : syracuseStep 1186537 = 889903) (by norm_num)
theorem B1579757 : Blo 1052612 1579757 := bbase (se 3 (by rfl) ⟨296204, by rfl⟩ : syracuseStep 1579757 = 592409) (by norm_num)
theorem B4692725 : Blo 1052612 4692725 := bbase (se 5 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 4692725 = 439943) (by norm_num)
theorem B1579781 : Blo 1052612 1579781 := bbase (se 4 (by rfl) ⟨148104, by rfl⟩ : syracuseStep 1579781 = 296209) (by norm_num)
theorem B1776397 : Blo 1052612 1776397 := bbase (se 3 (by rfl) ⟨333074, by rfl⟩ : syracuseStep 1776397 = 666149) (by norm_num)
theorem B1645325 : Blo 1052612 1645325 := bbase (se 3 (by rfl) ⟨308498, by rfl⟩ : syracuseStep 1645325 = 616997) (by norm_num)
theorem B1186573 : Blo 1052612 1186573 := bbase (se 3 (by rfl) ⟨222482, by rfl⟩ : syracuseStep 1186573 = 444965) (by norm_num)
theorem B1579805 : Blo 1052612 1579805 := bbase (se 3 (by rfl) ⟨296213, by rfl⟩ : syracuseStep 1579805 = 592427) (by norm_num)
theorem B1186609 : Blo 1052612 1186609 := bbase (se 2 (by rfl) ⟨444978, by rfl⟩ : syracuseStep 1186609 = 889957) (by norm_num)
theorem B1579829 : Blo 1052612 1579829 := bbase (se 5 (by rfl) ⟨74054, by rfl⟩ : syracuseStep 1579829 = 148109) (by norm_num)
theorem B2005813 : Blo 1052612 2005813 := bbase (se 5 (by rfl) ⟨94022, by rfl⟩ : syracuseStep 2005813 = 188045) (by norm_num)
theorem B1579853 : Blo 1052612 1579853 := bbase (se 3 (by rfl) ⟨296222, by rfl⟩ : syracuseStep 1579853 = 592445) (by norm_num)
theorem B1186645 : Blo 1052612 1186645 := bbase (se 9 (by rfl) ⟨3476, by rfl⟩ : syracuseStep 1186645 = 6953) (by norm_num)
theorem B1776485 : Blo 1052612 1776485 := bbase (se 4 (by rfl) ⟨166545, by rfl⟩ : syracuseStep 1776485 = 333091) (by norm_num)
theorem B1579877 : Blo 1052612 1579877 := bbase (se 4 (by rfl) ⟨148113, by rfl⟩ : syracuseStep 1579877 = 296227) (by norm_num)
theorem B1186681 : Blo 1052612 1186681 := bbase (se 2 (by rfl) ⟨445005, by rfl⟩ : syracuseStep 1186681 = 890011) (by norm_num)
theorem B1579901 : Blo 1052612 1579901 := bbase (se 3 (by rfl) ⟨296231, by rfl⟩ : syracuseStep 1579901 = 592463) (by norm_num)
theorem B1579925 : Blo 1052612 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B1186717 : Blo 1052612 1186717 := bbase (se 3 (by rfl) ⟨222509, by rfl⟩ : syracuseStep 1186717 = 445019) (by norm_num)
theorem B1579949 : Blo 1052612 1579949 := bbase (se 3 (by rfl) ⟨296240, by rfl⟩ : syracuseStep 1579949 = 592481) (by norm_num)
theorem B1186753 : Blo 1052612 1186753 := bbase (se 2 (by rfl) ⟨445032, by rfl⟩ : syracuseStep 1186753 = 890065) (by norm_num)
theorem B1579973 : Blo 1052612 1579973 := bbase (se 4 (by rfl) ⟨148122, by rfl⟩ : syracuseStep 1579973 = 296245) (by norm_num)
theorem B1579997 : Blo 1052612 1579997 := bbase (se 3 (by rfl) ⟨296249, by rfl⟩ : syracuseStep 1579997 = 592499) (by norm_num)
theorem B2169821 : Blo 1052612 2169821 := bbase (se 3 (by rfl) ⟨406841, by rfl⟩ : syracuseStep 2169821 = 813683) (by norm_num)
theorem B1776613 : Blo 1052612 1776613 := bbase (se 4 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 1776613 = 333115) (by norm_num)
theorem B1186789 : Blo 1052612 1186789 := bbase (se 4 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 1186789 = 222523) (by norm_num)
theorem B1580021 : Blo 1052612 1580021 := bbase (se 5 (by rfl) ⟨74063, by rfl⟩ : syracuseStep 1580021 = 148127) (by norm_num)
theorem B1186825 : Blo 1052612 1186825 := bbase (se 2 (by rfl) ⟨445059, by rfl⟩ : syracuseStep 1186825 = 890119) (by norm_num)
theorem B1580045 : Blo 1052612 1580045 := bbase (se 3 (by rfl) ⟨296258, by rfl⟩ : syracuseStep 1580045 = 592517) (by norm_num)
theorem B1580069 : Blo 1052612 1580069 := bbase (se 4 (by rfl) ⟨148131, by rfl⟩ : syracuseStep 1580069 = 296263) (by norm_num)
theorem B1186861 : Blo 1052612 1186861 := bbase (se 3 (by rfl) ⟨222536, by rfl⟩ : syracuseStep 1186861 = 445073) (by norm_num)
theorem B1776701 : Blo 1052612 1776701 := bbase (se 3 (by rfl) ⟨333131, by rfl⟩ : syracuseStep 1776701 = 666263) (by norm_num)
theorem B1580093 : Blo 1052612 1580093 := bbase (se 3 (by rfl) ⟨296267, by rfl⟩ : syracuseStep 1580093 = 592535) (by norm_num)
theorem B1186897 : Blo 1052612 1186897 := bbase (se 2 (by rfl) ⟨445086, by rfl⟩ : syracuseStep 1186897 = 890173) (by norm_num)
theorem B1580117 : Blo 1052612 1580117 := bbase (se 8 (by rfl) ⟨9258, by rfl⟩ : syracuseStep 1580117 = 18517) (by norm_num)
theorem B1580141 : Blo 1052612 1580141 := bbase (se 3 (by rfl) ⟨296276, by rfl⟩ : syracuseStep 1580141 = 592553) (by norm_num)
theorem B1186933 : Blo 1052612 1186933 := bbase (se 5 (by rfl) ⟨55637, by rfl⟩ : syracuseStep 1186933 = 111275) (by norm_num)
theorem B1580165 : Blo 1052612 1580165 := bbase (se 4 (by rfl) ⟨148140, by rfl⟩ : syracuseStep 1580165 = 296281) (by norm_num)
theorem B1186969 : Blo 1052612 1186969 := bbase (se 2 (by rfl) ⟨445113, by rfl⟩ : syracuseStep 1186969 = 890227) (by norm_num)
theorem B1580189 : Blo 1052612 1580189 := bbase (se 3 (by rfl) ⟨296285, by rfl⟩ : syracuseStep 1580189 = 592571) (by norm_num)
theorem B1580213 : Blo 1052612 1580213 := bbase (se 5 (by rfl) ⟨74072, by rfl⟩ : syracuseStep 1580213 = 148145) (by norm_num)
theorem B1776829 : Blo 1052612 1776829 := bbase (se 3 (by rfl) ⟨333155, by rfl⟩ : syracuseStep 1776829 = 666311) (by norm_num)
theorem B1187005 : Blo 1052612 1187005 := bbase (se 3 (by rfl) ⟨222563, by rfl⟩ : syracuseStep 1187005 = 445127) (by norm_num)
theorem B1580237 : Blo 1052612 1580237 := bbase (se 3 (by rfl) ⟨296294, by rfl⟩ : syracuseStep 1580237 = 592589) (by norm_num)
theorem B1187041 : Blo 1052612 1187041 := bbase (se 2 (by rfl) ⟨445140, by rfl⟩ : syracuseStep 1187041 = 890281) (by norm_num)
theorem B1580261 : Blo 1052612 1580261 := bbase (se 4 (by rfl) ⟨148149, by rfl⟩ : syracuseStep 1580261 = 296299) (by norm_num)
theorem B1580285 : Blo 1052612 1580285 := bbase (se 3 (by rfl) ⟨296303, by rfl⟩ : syracuseStep 1580285 = 592607) (by norm_num)
theorem B2530565 : Blo 1052612 2530565 := bbase (se 4 (by rfl) ⟨237240, by rfl⟩ : syracuseStep 2530565 = 474481) (by norm_num)
theorem B1187077 : Blo 1052612 1187077 := bbase (se 4 (by rfl) ⟨111288, by rfl⟩ : syracuseStep 1187077 = 222577) (by norm_num)
theorem B1776917 : Blo 1052612 1776917 := bbase (se 6 (by rfl) ⟨41646, by rfl⟩ : syracuseStep 1776917 = 83293) (by norm_num)
theorem B1580309 : Blo 1052612 1580309 := bbase (se 6 (by rfl) ⟨37038, by rfl⟩ : syracuseStep 1580309 = 74077) (by norm_num)
theorem B1187113 : Blo 1052612 1187113 := bbase (se 2 (by rfl) ⟨445167, by rfl⟩ : syracuseStep 1187113 = 890335) (by norm_num)
theorem B1580333 : Blo 1052612 1580333 := bbase (se 3 (by rfl) ⟨296312, by rfl⟩ : syracuseStep 1580333 = 592625) (by norm_num)
theorem B1580357 : Blo 1052612 1580357 := bbase (se 4 (by rfl) ⟨148158, by rfl⟩ : syracuseStep 1580357 = 296317) (by norm_num)
theorem B1187149 : Blo 1052612 1187149 := bbase (se 3 (by rfl) ⟨222590, by rfl⟩ : syracuseStep 1187149 = 445181) (by norm_num)
theorem B1580381 : Blo 1052612 1580381 := bbase (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) (by norm_num)
theorem B1187185 : Blo 1052612 1187185 := bbase (se 2 (by rfl) ⟨445194, by rfl⟩ : syracuseStep 1187185 = 890389) (by norm_num)
theorem B1580405 : Blo 1052612 1580405 := bbase (se 5 (by rfl) ⟨74081, by rfl⟩ : syracuseStep 1580405 = 148163) (by norm_num)
theorem B1580429 : Blo 1052612 1580429 := bbase (se 3 (by rfl) ⟨296330, by rfl⟩ : syracuseStep 1580429 = 592661) (by norm_num)
theorem B1777045 : Blo 1052612 1777045 := bbase (se 6 (by rfl) ⟨41649, by rfl⟩ : syracuseStep 1777045 = 83299) (by norm_num)
theorem B1187221 : Blo 1052612 1187221 := bbase (se 6 (by rfl) ⟨27825, by rfl⟩ : syracuseStep 1187221 = 55651) (by norm_num)
theorem B1580453 : Blo 1052612 1580453 := bbase (se 4 (by rfl) ⟨148167, by rfl⟩ : syracuseStep 1580453 = 296335) (by norm_num)
theorem B1187257 : Blo 1052612 1187257 := bbase (se 2 (by rfl) ⟨445221, by rfl⟩ : syracuseStep 1187257 = 890443) (by norm_num)
theorem B1580477 : Blo 1052612 1580477 := bbase (se 3 (by rfl) ⟨296339, by rfl⟩ : syracuseStep 1580477 = 592679) (by norm_num)
theorem B1580501 : Blo 1052612 1580501 := bbase (se 7 (by rfl) ⟨18521, by rfl⟩ : syracuseStep 1580501 = 37043) (by norm_num)
theorem B1187293 : Blo 1052612 1187293 := bbase (se 3 (by rfl) ⟨222617, by rfl⟩ : syracuseStep 1187293 = 445235) (by norm_num)
theorem B1777133 : Blo 1052612 1777133 := bbase (se 3 (by rfl) ⟨333212, by rfl⟩ : syracuseStep 1777133 = 666425) (by norm_num)
theorem B1580525 : Blo 1052612 1580525 := bbase (se 3 (by rfl) ⟨296348, by rfl⟩ : syracuseStep 1580525 = 592697) (by norm_num)
theorem B1187329 : Blo 1052612 1187329 := bbase (se 2 (by rfl) ⟨445248, by rfl⟩ : syracuseStep 1187329 = 890497) (by norm_num)
theorem B1580549 : Blo 1052612 1580549 := bbase (se 4 (by rfl) ⟨148176, by rfl⟩ : syracuseStep 1580549 = 296353) (by norm_num)
theorem B4496917 : Blo 1052612 4496917 := bbase (se 6 (by rfl) ⟨105396, by rfl⟩ : syracuseStep 4496917 = 210793) (by norm_num)
theorem B1580573 : Blo 1052612 1580573 := bbase (se 3 (by rfl) ⟨296357, by rfl⟩ : syracuseStep 1580573 = 592715) (by norm_num)
theorem B1187365 : Blo 1052612 1187365 := bbase (se 4 (by rfl) ⟨111315, by rfl⟩ : syracuseStep 1187365 = 222631) (by norm_num)
theorem B1580597 : Blo 1052612 1580597 := bbase (se 5 (by rfl) ⟨74090, by rfl⟩ : syracuseStep 1580597 = 148181) (by norm_num)
theorem B1187401 : Blo 1052612 1187401 := bbase (se 2 (by rfl) ⟨445275, by rfl⟩ : syracuseStep 1187401 = 890551) (by norm_num)
theorem B1580621 : Blo 1052612 1580621 := bbase (se 3 (by rfl) ⟨296366, by rfl⟩ : syracuseStep 1580621 = 592733) (by norm_num)
theorem B2530901 : Blo 1052612 2530901 := bbase (se 8 (by rfl) ⟨14829, by rfl⟩ : syracuseStep 2530901 = 29659) (by norm_num)
theorem B1580645 : Blo 1052612 1580645 := bbase (se 4 (by rfl) ⟨148185, by rfl⟩ : syracuseStep 1580645 = 296371) (by norm_num)
theorem B1777261 : Blo 1052612 1777261 := bbase (se 3 (by rfl) ⟨333236, by rfl⟩ : syracuseStep 1777261 = 666473) (by norm_num)
theorem B1187437 : Blo 1052612 1187437 := bbase (se 3 (by rfl) ⟨222644, by rfl⟩ : syracuseStep 1187437 = 445289) (by norm_num)
theorem B1580669 : Blo 1052612 1580669 := bbase (se 3 (by rfl) ⟨296375, by rfl⟩ : syracuseStep 1580669 = 592751) (by norm_num)
theorem B1187473 : Blo 1052612 1187473 := bbase (se 2 (by rfl) ⟨445302, by rfl⟩ : syracuseStep 1187473 = 890605) (by norm_num)
theorem B1580693 : Blo 1052612 1580693 := bbase (se 6 (by rfl) ⟨37047, by rfl⟩ : syracuseStep 1580693 = 74095) (by norm_num)
theorem B1580717 : Blo 1052612 1580717 := bbase (se 3 (by rfl) ⟨296384, by rfl⟩ : syracuseStep 1580717 = 592769) (by norm_num)
theorem B2530997 : Blo 1052612 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B1187509 : Blo 1052612 1187509 := bbase (se 5 (by rfl) ⟨55664, by rfl⟩ : syracuseStep 1187509 = 111329) (by norm_num)
theorem B1777349 : Blo 1052612 1777349 := bbase (se 4 (by rfl) ⟨166626, by rfl⟩ : syracuseStep 1777349 = 333253) (by norm_num)
theorem B1580741 : Blo 1052612 1580741 := bbase (se 4 (by rfl) ⟨148194, by rfl⟩ : syracuseStep 1580741 = 296389) (by norm_num)
theorem B5349077 : Blo 1052612 5349077 := bbase (se 7 (by rfl) ⟨62684, by rfl⟩ : syracuseStep 5349077 = 125369) (by norm_num)
theorem B1187545 : Blo 1052612 1187545 := bbase (se 2 (by rfl) ⟨445329, by rfl⟩ : syracuseStep 1187545 = 890659) (by norm_num)
theorem B1580765 : Blo 1052612 1580765 := bbase (se 3 (by rfl) ⟨296393, by rfl⟩ : syracuseStep 1580765 = 592787) (by norm_num)
theorem B1580789 : Blo 1052612 1580789 := bbase (se 5 (by rfl) ⟨74099, by rfl⟩ : syracuseStep 1580789 = 148199) (by norm_num)
theorem B1187581 : Blo 1052612 1187581 := bbase (se 3 (by rfl) ⟨222671, by rfl⟩ : syracuseStep 1187581 = 445343) (by norm_num)
theorem B1580813 : Blo 1052612 1580813 := bbase (se 3 (by rfl) ⟨296402, by rfl⟩ : syracuseStep 1580813 = 592805) (by norm_num)
theorem B1187617 : Blo 1052612 1187617 := bbase (se 2 (by rfl) ⟨445356, by rfl⟩ : syracuseStep 1187617 = 890713) (by norm_num)
theorem B1580837 : Blo 1052612 1580837 := bbase (se 4 (by rfl) ⟨148203, by rfl⟩ : syracuseStep 1580837 = 296407) (by norm_num)
theorem B1580861 : Blo 1052612 1580861 := bbase (se 3 (by rfl) ⟨296411, by rfl⟩ : syracuseStep 1580861 = 592823) (by norm_num)
theorem B1777477 : Blo 1052612 1777477 := bbase (se 4 (by rfl) ⟨166638, by rfl⟩ : syracuseStep 1777477 = 333277) (by norm_num)
theorem B1187653 : Blo 1052612 1187653 := bbase (se 4 (by rfl) ⟨111342, by rfl⟩ : syracuseStep 1187653 = 222685) (by norm_num)
theorem B1580885 : Blo 1052612 1580885 := bbase (se 9 (by rfl) ⟨4631, by rfl⟩ : syracuseStep 1580885 = 9263) (by norm_num)
theorem B4005733 : Blo 1052612 4005733 := bbase (se 4 (by rfl) ⟨375537, by rfl⟩ : syracuseStep 4005733 = 751075) (by norm_num)
theorem B1187689 : Blo 1052612 1187689 := bbase (se 2 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 1187689 = 890767) (by norm_num)
theorem B1580909 : Blo 1052612 1580909 := bbase (se 3 (by rfl) ⟨296420, by rfl⟩ : syracuseStep 1580909 = 592841) (by norm_num)
theorem B2531189 : Blo 1052612 2531189 := bbase (se 5 (by rfl) ⟨118649, by rfl⟩ : syracuseStep 2531189 = 237299) (by norm_num)
theorem B1580933 : Blo 1052612 1580933 := bbase (se 4 (by rfl) ⟨148212, by rfl⟩ : syracuseStep 1580933 = 296425) (by norm_num)
theorem B1187725 : Blo 1052612 1187725 := bbase (se 3 (by rfl) ⟨222698, by rfl⟩ : syracuseStep 1187725 = 445397) (by norm_num)
theorem B4398997 : Blo 1052612 4398997 := bbase (se 6 (by rfl) ⟨103101, by rfl⟩ : syracuseStep 4398997 = 206203) (by norm_num)
theorem B1777565 : Blo 1052612 1777565 := bbase (se 3 (by rfl) ⟨333293, by rfl⟩ : syracuseStep 1777565 = 666587) (by norm_num)
theorem B1580957 : Blo 1052612 1580957 := bbase (se 3 (by rfl) ⟨296429, by rfl⟩ : syracuseStep 1580957 = 592859) (by norm_num)
theorem B1187761 : Blo 1052612 1187761 := bbase (se 2 (by rfl) ⟨445410, by rfl⟩ : syracuseStep 1187761 = 890821) (by norm_num)
theorem B1580981 : Blo 1052612 1580981 := bbase (se 5 (by rfl) ⟨74108, by rfl⟩ : syracuseStep 1580981 = 148217) (by norm_num)
theorem B3383221 : Blo 1052612 3383221 := bbase (se 5 (by rfl) ⟨158588, by rfl⟩ : syracuseStep 3383221 = 317177) (by norm_num)
theorem B1581005 : Blo 1052612 1581005 := bbase (se 3 (by rfl) ⟨296438, by rfl⟩ : syracuseStep 1581005 = 592877) (by norm_num)
theorem B1187797 : Blo 1052612 1187797 := bbase (se 7 (by rfl) ⟨13919, by rfl⟩ : syracuseStep 1187797 = 27839) (by norm_num)
theorem B1581029 : Blo 1052612 1581029 := bbase (se 4 (by rfl) ⟨148221, by rfl⟩ : syracuseStep 1581029 = 296443) (by norm_num)
theorem B1187833 : Blo 1052612 1187833 := bbase (se 2 (by rfl) ⟨445437, by rfl⟩ : syracuseStep 1187833 = 890875) (by norm_num)
theorem B1581053 : Blo 1052612 1581053 := bbase (se 3 (by rfl) ⟨296447, by rfl⟩ : syracuseStep 1581053 = 592895) (by norm_num)
theorem B1581077 : Blo 1052612 1581077 := bbase (se 6 (by rfl) ⟨37056, by rfl⟩ : syracuseStep 1581077 = 74113) (by norm_num)
theorem B1777693 : Blo 1052612 1777693 := bbase (se 3 (by rfl) ⟨333317, by rfl⟩ : syracuseStep 1777693 = 666635) (by norm_num)
theorem B1187869 : Blo 1052612 1187869 := bbase (se 3 (by rfl) ⟨222725, by rfl⟩ : syracuseStep 1187869 = 445451) (by norm_num)
theorem B1581101 : Blo 1052612 1581101 := bbase (se 3 (by rfl) ⟨296456, by rfl⟩ : syracuseStep 1581101 = 592913) (by norm_num)
theorem B1187905 : Blo 1052612 1187905 := bbase (se 2 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 1187905 = 890929) (by norm_num)
theorem B1581125 : Blo 1052612 1581125 := bbase (se 4 (by rfl) ⟨148230, by rfl⟩ : syracuseStep 1581125 = 296461) (by norm_num)
theorem B1581149 : Blo 1052612 1581149 := bbase (se 3 (by rfl) ⟨296465, by rfl⟩ : syracuseStep 1581149 = 592931) (by norm_num)
theorem B1187941 : Blo 1052612 1187941 := bbase (se 4 (by rfl) ⟨111369, by rfl⟩ : syracuseStep 1187941 = 222739) (by norm_num)
theorem B1777781 : Blo 1052612 1777781 := bbase (se 5 (by rfl) ⟨83333, by rfl⟩ : syracuseStep 1777781 = 166667) (by norm_num)
theorem B1581173 : Blo 1052612 1581173 := bbase (se 5 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 1581173 = 148235) (by norm_num)
theorem B1187977 : Blo 1052612 1187977 := bbase (se 2 (by rfl) ⟨445491, by rfl⟩ : syracuseStep 1187977 = 890983) (by norm_num)
theorem B1581197 : Blo 1052612 1581197 := bbase (se 3 (by rfl) ⟨296474, by rfl⟩ : syracuseStep 1581197 = 592949) (by norm_num)
theorem B17080469 : Blo 1052612 17080469 := bbase (se 6 (by rfl) ⟨400323, by rfl⟩ : syracuseStep 17080469 = 800647) (by norm_num)
theorem B6758549 : Blo 1052612 6758549 := bbase (se 6 (by rfl) ⟨158403, by rfl⟩ : syracuseStep 6758549 = 316807) (by norm_num)
theorem B4006037 : Blo 1052612 4006037 := bbase (se 6 (by rfl) ⟨93891, by rfl⟩ : syracuseStep 4006037 = 187783) (by norm_num)
theorem B1581221 : Blo 1052612 1581221 := bbase (se 4 (by rfl) ⟨148239, by rfl⟩ : syracuseStep 1581221 = 296479) (by norm_num)
theorem B1188013 : Blo 1052612 1188013 := bbase (se 3 (by rfl) ⟨222752, by rfl⟩ : syracuseStep 1188013 = 445505) (by norm_num)
theorem B1581245 : Blo 1052612 1581245 := bbase (se 3 (by rfl) ⟨296483, by rfl⟩ : syracuseStep 1581245 = 592967) (by norm_num)
theorem B1188049 : Blo 1052612 1188049 := bbase (se 2 (by rfl) ⟨445518, by rfl⟩ : syracuseStep 1188049 = 891037) (by norm_num)
theorem B1581269 : Blo 1052612 1581269 := bbase (se 7 (by rfl) ⟨18530, by rfl⟩ : syracuseStep 1581269 = 37061) (by norm_num)
theorem B1581293 : Blo 1052612 1581293 := bbase (se 3 (by rfl) ⟨296492, by rfl⟩ : syracuseStep 1581293 = 592985) (by norm_num)
theorem B1777909 : Blo 1052612 1777909 := bbase (se 5 (by rfl) ⟨83339, by rfl⟩ : syracuseStep 1777909 = 166679) (by norm_num)
theorem B1188085 : Blo 1052612 1188085 := bbase (se 5 (by rfl) ⟨55691, by rfl⟩ : syracuseStep 1188085 = 111383) (by norm_num)
theorem B1581317 : Blo 1052612 1581317 := bbase (se 4 (by rfl) ⟨148248, by rfl⟩ : syracuseStep 1581317 = 296497) (by norm_num)
theorem B1188121 : Blo 1052612 1188121 := bbase (se 2 (by rfl) ⟨445545, by rfl⟩ : syracuseStep 1188121 = 891091) (by norm_num)
theorem B1581341 : Blo 1052612 1581341 := bbase (se 3 (by rfl) ⟨296501, by rfl⟩ : syracuseStep 1581341 = 593003) (by norm_num)
theorem B1581365 : Blo 1052612 1581365 := bbase (se 5 (by rfl) ⟨74126, by rfl⟩ : syracuseStep 1581365 = 148253) (by norm_num)
theorem B1188157 : Blo 1052612 1188157 := bbase (se 3 (by rfl) ⟨222779, by rfl⟩ : syracuseStep 1188157 = 445559) (by norm_num)
theorem B1777997 : Blo 1052612 1777997 := bbase (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) (by norm_num)
theorem B1581389 : Blo 1052612 1581389 := bbase (se 3 (by rfl) ⟨296510, by rfl⟩ : syracuseStep 1581389 = 593021) (by norm_num)
theorem B1188193 : Blo 1052612 1188193 := bbase (se 2 (by rfl) ⟨445572, by rfl⟩ : syracuseStep 1188193 = 891145) (by norm_num)
theorem B1581413 : Blo 1052612 1581413 := bbase (se 4 (by rfl) ⟨148257, by rfl⟩ : syracuseStep 1581413 = 296515) (by norm_num)
theorem B1581437 : Blo 1052612 1581437 := bbase (se 3 (by rfl) ⟨296519, by rfl⟩ : syracuseStep 1581437 = 593039) (by norm_num)
theorem B1188229 : Blo 1052612 1188229 := bbase (se 4 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 1188229 = 222793) (by norm_num)
theorem B1581461 : Blo 1052612 1581461 := bbase (se 6 (by rfl) ⟨37065, by rfl⟩ : syracuseStep 1581461 = 74131) (by norm_num)
theorem B1188265 : Blo 1052612 1188265 := bbase (se 2 (by rfl) ⟨445599, by rfl⟩ : syracuseStep 1188265 = 891199) (by norm_num)
theorem B1581485 : Blo 1052612 1581485 := bbase (se 3 (by rfl) ⟨296528, by rfl⟩ : syracuseStep 1581485 = 593057) (by norm_num)
theorem B1581509 : Blo 1052612 1581509 := bbase (se 4 (by rfl) ⟨148266, by rfl⟩ : syracuseStep 1581509 = 296533) (by norm_num)
theorem B1778125 : Blo 1052612 1778125 := bbase (se 3 (by rfl) ⟨333398, by rfl⟩ : syracuseStep 1778125 = 666797) (by norm_num)
theorem B1188301 : Blo 1052612 1188301 := bbase (se 3 (by rfl) ⟨222806, by rfl⟩ : syracuseStep 1188301 = 445613) (by norm_num)
theorem B1581533 : Blo 1052612 1581533 := bbase (se 3 (by rfl) ⟨296537, by rfl⟩ : syracuseStep 1581533 = 593075) (by norm_num)
theorem B1188337 : Blo 1052612 1188337 := bbase (se 2 (by rfl) ⟨445626, by rfl⟩ : syracuseStep 1188337 = 891253) (by norm_num)
theorem B1581557 : Blo 1052612 1581557 := bbase (se 5 (by rfl) ⟨74135, by rfl⟩ : syracuseStep 1581557 = 148271) (by norm_num)
theorem B1581581 : Blo 1052612 1581581 := bbase (se 3 (by rfl) ⟨296546, by rfl⟩ : syracuseStep 1581581 = 593093) (by norm_num)
theorem B1188373 : Blo 1052612 1188373 := bbase (se 6 (by rfl) ⟨27852, by rfl⟩ : syracuseStep 1188373 = 55705) (by norm_num)
theorem B1778213 : Blo 1052612 1778213 := bbase (se 4 (by rfl) ⟨166707, by rfl⟩ : syracuseStep 1778213 = 333415) (by norm_num)
theorem B1581605 : Blo 1052612 1581605 := bbase (se 4 (by rfl) ⟨148275, by rfl⟩ : syracuseStep 1581605 = 296551) (by norm_num)
theorem B1188409 : Blo 1052612 1188409 := bbase (se 2 (by rfl) ⟨445653, by rfl⟩ : syracuseStep 1188409 = 891307) (by norm_num)
theorem B1581629 : Blo 1052612 1581629 := bbase (se 3 (by rfl) ⟨296555, by rfl⟩ : syracuseStep 1581629 = 593111) (by norm_num)
theorem B1581653 : Blo 1052612 1581653 := bbase (se 8 (by rfl) ⟨9267, by rfl⟩ : syracuseStep 1581653 = 18535) (by norm_num)
theorem B1188445 : Blo 1052612 1188445 := bbase (se 3 (by rfl) ⟨222833, by rfl⟩ : syracuseStep 1188445 = 445667) (by norm_num)
theorem B1581677 : Blo 1052612 1581677 := bbase (se 3 (by rfl) ⟨296564, by rfl⟩ : syracuseStep 1581677 = 593129) (by norm_num)
theorem B1188481 : Blo 1052612 1188481 := bbase (se 2 (by rfl) ⟨445680, by rfl⟩ : syracuseStep 1188481 = 891361) (by norm_num)
theorem B1581701 : Blo 1052612 1581701 := bbase (se 4 (by rfl) ⟨148284, by rfl⟩ : syracuseStep 1581701 = 296569) (by norm_num)
theorem B1581725 : Blo 1052612 1581725 := bbase (se 3 (by rfl) ⟨296573, by rfl⟩ : syracuseStep 1581725 = 593147) (by norm_num)
theorem B1778341 : Blo 1052612 1778341 := bbase (se 4 (by rfl) ⟨166719, by rfl⟩ : syracuseStep 1778341 = 333439) (by norm_num)
theorem B1188517 : Blo 1052612 1188517 := bbase (se 4 (by rfl) ⟨111423, by rfl⟩ : syracuseStep 1188517 = 222847) (by norm_num)
theorem B1581749 : Blo 1052612 1581749 := bbase (se 5 (by rfl) ⟨74144, by rfl⟩ : syracuseStep 1581749 = 148289) (by norm_num)
theorem B1188553 : Blo 1052612 1188553 := bbase (se 2 (by rfl) ⟨445707, by rfl⟩ : syracuseStep 1188553 = 891415) (by norm_num)
theorem B1581773 : Blo 1052612 1581773 := bbase (se 3 (by rfl) ⟨296582, by rfl⟩ : syracuseStep 1581773 = 593165) (by norm_num)
theorem B1581797 : Blo 1052612 1581797 := bbase (se 4 (by rfl) ⟨148293, by rfl⟩ : syracuseStep 1581797 = 296587) (by norm_num)
theorem B1188589 : Blo 1052612 1188589 := bbase (se 3 (by rfl) ⟨222860, by rfl⟩ : syracuseStep 1188589 = 445721) (by norm_num)
theorem B2138869 : Blo 1052612 2138869 := bbase (se 5 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 2138869 = 200519) (by norm_num)
theorem B1778429 : Blo 1052612 1778429 := bbase (se 3 (by rfl) ⟨333455, by rfl⟩ : syracuseStep 1778429 = 666911) (by norm_num)
theorem B1581821 : Blo 1052612 1581821 := bbase (se 3 (by rfl) ⟨296591, by rfl⟩ : syracuseStep 1581821 = 593183) (by norm_num)
theorem B1188625 : Blo 1052612 1188625 := bbase (se 2 (by rfl) ⟨445734, by rfl⟩ : syracuseStep 1188625 = 891469) (by norm_num)
theorem B1581845 : Blo 1052612 1581845 := bbase (se 6 (by rfl) ⟨37074, by rfl⟩ : syracuseStep 1581845 = 74149) (by norm_num)
theorem B1581869 : Blo 1052612 1581869 := bbase (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) (by norm_num)
theorem B1188661 : Blo 1052612 1188661 := bbase (se 5 (by rfl) ⟨55718, by rfl⟩ : syracuseStep 1188661 = 111437) (by norm_num)
theorem B1581893 : Blo 1052612 1581893 := bbase (se 4 (by rfl) ⟨148302, by rfl⟩ : syracuseStep 1581893 = 296605) (by norm_num)
theorem B1581917 : Blo 1052612 1581917 := bbase (se 3 (by rfl) ⟨296609, by rfl⟩ : syracuseStep 1581917 = 593219) (by norm_num)
theorem B1581941 : Blo 1052612 1581941 := bbase (se 5 (by rfl) ⟨74153, by rfl⟩ : syracuseStep 1581941 = 148307) (by norm_num)
theorem B1778557 : Blo 1052612 1778557 := bbase (se 3 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 1778557 = 666959) (by norm_num)
theorem B1581965 : Blo 1052612 1581965 := bbase (se 3 (by rfl) ⟨296618, by rfl⟩ : syracuseStep 1581965 = 593237) (by norm_num)
theorem B2368421 : Blo 1052612 2368421 := bbase (se 4 (by rfl) ⟨222039, by rfl⟩ : syracuseStep 2368421 = 444079) (by norm_num)
theorem B1581989 : Blo 1052612 1581989 := bbase (se 4 (by rfl) ⟨148311, by rfl⟩ : syracuseStep 1581989 = 296623) (by norm_num)
theorem B1582013 : Blo 1052612 1582013 := bbase (se 3 (by rfl) ⟨296627, by rfl⟩ : syracuseStep 1582013 = 593255) (by norm_num)
theorem B1778645 : Blo 1052612 1778645 := bbase (se 7 (by rfl) ⟨20843, by rfl⟩ : syracuseStep 1778645 = 41687) (by norm_num)
theorem B1582037 : Blo 1052612 1582037 := bbase (se 7 (by rfl) ⟨18539, by rfl⟩ : syracuseStep 1582037 = 37079) (by norm_num)
theorem B2368493 : Blo 1052612 2368493 := bbase (se 3 (by rfl) ⟨444092, by rfl⟩ : syracuseStep 2368493 = 888185) (by norm_num)
theorem B1582061 : Blo 1052612 1582061 := bbase (se 3 (by rfl) ⟨296636, by rfl⟩ : syracuseStep 1582061 = 593273) (by norm_num)
theorem B2532341 : Blo 1052612 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B1582085 : Blo 1052612 1582085 := bbase (se 4 (by rfl) ⟨148320, by rfl⟩ : syracuseStep 1582085 = 296641) (by norm_num)
theorem B1582109 : Blo 1052612 1582109 := bbase (se 3 (by rfl) ⟨296645, by rfl⟩ : syracuseStep 1582109 = 593291) (by norm_num)
theorem B2368565 : Blo 1052612 2368565 := bbase (se 5 (by rfl) ⟨111026, by rfl⟩ : syracuseStep 2368565 = 222053) (by norm_num)
theorem B1582133 : Blo 1052612 1582133 := bbase (se 5 (by rfl) ⟨74162, by rfl⟩ : syracuseStep 1582133 = 148325) (by norm_num)
theorem B1582157 : Blo 1052612 1582157 := bbase (se 3 (by rfl) ⟨296654, by rfl⟩ : syracuseStep 1582157 = 593309) (by norm_num)
theorem B1778773 : Blo 1052612 1778773 := bbase (se 8 (by rfl) ⟨10422, by rfl⟩ : syracuseStep 1778773 = 20845) (by norm_num)
theorem B1582181 : Blo 1052612 1582181 := bbase (se 4 (by rfl) ⟨148329, by rfl⟩ : syracuseStep 1582181 = 296659) (by norm_num)
theorem B2368637 : Blo 1052612 2368637 := bbase (se 3 (by rfl) ⟨444119, by rfl⟩ : syracuseStep 2368637 = 888239) (by norm_num)
theorem B1582205 : Blo 1052612 1582205 := bbase (se 3 (by rfl) ⟨296663, by rfl⟩ : syracuseStep 1582205 = 593327) (by norm_num)
theorem B1582229 : Blo 1052612 1582229 := bbase (se 6 (by rfl) ⟨37083, by rfl⟩ : syracuseStep 1582229 = 74167) (by norm_num)
theorem B2925733 : Blo 1052612 2925733 := bbase (se 4 (by rfl) ⟨274287, by rfl⟩ : syracuseStep 2925733 = 548575) (by norm_num)
theorem B1778861 : Blo 1052612 1778861 := bbase (se 3 (by rfl) ⟨333536, by rfl⟩ : syracuseStep 1778861 = 667073) (by norm_num)
theorem B1582253 : Blo 1052612 1582253 := bbase (se 3 (by rfl) ⟨296672, by rfl⟩ : syracuseStep 1582253 = 593345) (by norm_num)
theorem B2368709 : Blo 1052612 2368709 := bbase (se 4 (by rfl) ⟨222066, by rfl⟩ : syracuseStep 2368709 = 444133) (by norm_num)
theorem B1582277 : Blo 1052612 1582277 := bbase (se 4 (by rfl) ⟨148338, by rfl⟩ : syracuseStep 1582277 = 296677) (by norm_num)
theorem B1582301 : Blo 1052612 1582301 := bbase (se 3 (by rfl) ⟨296681, by rfl⟩ : syracuseStep 1582301 = 593363) (by norm_num)
theorem B1582325 : Blo 1052612 1582325 := bbase (se 5 (by rfl) ⟨74171, by rfl⟩ : syracuseStep 1582325 = 148343) (by norm_num)
theorem B2368781 : Blo 1052612 2368781 := bbase (se 3 (by rfl) ⟨444146, by rfl⟩ : syracuseStep 2368781 = 888293) (by norm_num)
theorem B1582349 : Blo 1052612 1582349 := bbase (se 3 (by rfl) ⟨296690, by rfl⟩ : syracuseStep 1582349 = 593381) (by norm_num)
theorem B1582373 : Blo 1052612 1582373 := bbase (se 4 (by rfl) ⟨148347, by rfl⟩ : syracuseStep 1582373 = 296695) (by norm_num)
theorem B1778989 : Blo 1052612 1778989 := bbase (se 3 (by rfl) ⟨333560, by rfl⟩ : syracuseStep 1778989 = 667121) (by norm_num)
theorem B1582397 : Blo 1052612 1582397 := bbase (se 3 (by rfl) ⟨296699, by rfl⟩ : syracuseStep 1582397 = 593399) (by norm_num)
theorem B2368853 : Blo 1052612 2368853 := bbase (se 12 (by rfl) ⟨867, by rfl⟩ : syracuseStep 2368853 = 1735) (by norm_num)
theorem B1582421 : Blo 1052612 1582421 := bbase (se 12 (by rfl) ⟨579, by rfl⟩ : syracuseStep 1582421 = 1159) (by norm_num)
theorem B1582445 : Blo 1052612 1582445 := bbase (se 3 (by rfl) ⟨296708, by rfl⟩ : syracuseStep 1582445 = 593417) (by norm_num)
theorem B1779077 : Blo 1052612 1779077 := bbase (se 4 (by rfl) ⟨166788, by rfl⟩ : syracuseStep 1779077 = 333577) (by norm_num)
theorem B1582469 : Blo 1052612 1582469 := bbase (se 4 (by rfl) ⟨148356, by rfl⟩ : syracuseStep 1582469 = 296713) (by norm_num)
theorem B2368925 : Blo 1052612 2368925 := bbase (se 3 (by rfl) ⟨444173, by rfl⟩ : syracuseStep 2368925 = 888347) (by norm_num)
theorem B1582493 : Blo 1052612 1582493 := bbase (se 3 (by rfl) ⟨296717, by rfl⟩ : syracuseStep 1582493 = 593435) (by norm_num)
theorem B1582517 : Blo 1052612 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B1582541 : Blo 1052612 1582541 := bbase (se 3 (by rfl) ⟨296726, by rfl⟩ : syracuseStep 1582541 = 593453) (by norm_num)
theorem B1713613 : Blo 1052612 1713613 := bbase (se 3 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 1713613 = 642605) (by norm_num)
theorem B2368997 : Blo 1052612 2368997 := bbase (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) (by norm_num)
theorem B1582565 : Blo 1052612 1582565 := bbase (se 4 (by rfl) ⟨148365, by rfl⟩ : syracuseStep 1582565 = 296731) (by norm_num)
theorem B1582589 : Blo 1052612 1582589 := bbase (se 3 (by rfl) ⟨296735, by rfl⟩ : syracuseStep 1582589 = 593471) (by norm_num)
theorem B1779205 : Blo 1052612 1779205 := bbase (se 4 (by rfl) ⟨166800, by rfl⟩ : syracuseStep 1779205 = 333601) (by norm_num)
theorem B1582613 : Blo 1052612 1582613 := bbase (se 6 (by rfl) ⟨37092, by rfl⟩ : syracuseStep 1582613 = 74185) (by norm_num)
theorem B2369069 : Blo 1052612 2369069 := bbase (se 3 (by rfl) ⟨444200, by rfl⟩ : syracuseStep 2369069 = 888401) (by norm_num)
theorem B1582637 : Blo 1052612 1582637 := bbase (se 3 (by rfl) ⟨296744, by rfl⟩ : syracuseStep 1582637 = 593489) (by norm_num)
theorem B1582661 : Blo 1052612 1582661 := bbase (se 4 (by rfl) ⟨148374, by rfl⟩ : syracuseStep 1582661 = 296749) (by norm_num)
theorem B1779293 : Blo 1052612 1779293 := bbase (se 3 (by rfl) ⟨333617, by rfl⟩ : syracuseStep 1779293 = 667235) (by norm_num)
theorem B1582685 : Blo 1052612 1582685 := bbase (se 3 (by rfl) ⟨296753, by rfl⟩ : syracuseStep 1582685 = 593507) (by norm_num)
theorem B2369141 : Blo 1052612 2369141 := bbase (se 5 (by rfl) ⟨111053, by rfl⟩ : syracuseStep 2369141 = 222107) (by norm_num)
theorem B1582709 : Blo 1052612 1582709 := bbase (se 5 (by rfl) ⟨74189, by rfl⟩ : syracuseStep 1582709 = 148379) (by norm_num)
theorem B1582733 : Blo 1052612 1582733 := bbase (se 3 (by rfl) ⟨296762, by rfl⟩ : syracuseStep 1582733 = 593525) (by norm_num)
theorem B1582757 : Blo 1052612 1582757 := bbase (se 4 (by rfl) ⟨148383, by rfl⟩ : syracuseStep 1582757 = 296767) (by norm_num)
theorem B2369213 : Blo 1052612 2369213 := bbase (se 3 (by rfl) ⟨444227, by rfl⟩ : syracuseStep 2369213 = 888455) (by norm_num)
theorem B1582781 : Blo 1052612 1582781 := bbase (se 3 (by rfl) ⟨296771, by rfl⟩ : syracuseStep 1582781 = 593543) (by norm_num)
theorem B1582805 : Blo 1052612 1582805 := bbase (se 7 (by rfl) ⟨18548, by rfl⟩ : syracuseStep 1582805 = 37097) (by norm_num)
theorem B1779421 : Blo 1052612 1779421 := bbase (se 3 (by rfl) ⟨333641, by rfl⟩ : syracuseStep 1779421 = 667283) (by norm_num)
theorem B1582829 : Blo 1052612 1582829 := bbase (se 3 (by rfl) ⟨296780, by rfl⟩ : syracuseStep 1582829 = 593561) (by norm_num)
theorem B1124101 : Blo 1052612 1124101 := bbase (se 4 (by rfl) ⟨105384, by rfl⟩ : syracuseStep 1124101 = 210769) (by norm_num)
theorem B2369285 : Blo 1052612 2369285 := bbase (se 4 (by rfl) ⟨222120, by rfl⟩ : syracuseStep 2369285 = 444241) (by norm_num)
theorem B1582853 : Blo 1052612 1582853 := bbase (se 4 (by rfl) ⟨148392, by rfl⟩ : syracuseStep 1582853 = 296785) (by norm_num)
theorem B1582877 : Blo 1052612 1582877 := bbase (se 3 (by rfl) ⟨296789, by rfl⟩ : syracuseStep 1582877 = 593579) (by norm_num)
theorem B1779509 : Blo 1052612 1779509 := bbase (se 5 (by rfl) ⟨83414, by rfl⟩ : syracuseStep 1779509 = 166829) (by norm_num)
theorem B1582901 : Blo 1052612 1582901 := bbase (se 5 (by rfl) ⟨74198, by rfl⟩ : syracuseStep 1582901 = 148397) (by norm_num)
theorem B2369357 : Blo 1052612 2369357 := bbase (se 3 (by rfl) ⟨444254, by rfl⟩ : syracuseStep 2369357 = 888509) (by norm_num)
theorem B1582925 : Blo 1052612 1582925 := bbase (se 3 (by rfl) ⟨296798, by rfl⟩ : syracuseStep 1582925 = 593597) (by norm_num)
theorem B1582949 : Blo 1052612 1582949 := bbase (se 4 (by rfl) ⟨148401, by rfl⟩ : syracuseStep 1582949 = 296803) (by norm_num)
theorem B1582973 : Blo 1052612 1582973 := bbase (se 3 (by rfl) ⟨296807, by rfl⟩ : syracuseStep 1582973 = 593615) (by norm_num)
theorem B2140037 : Blo 1052612 2140037 := bbase (se 4 (by rfl) ⟨200628, by rfl⟩ : syracuseStep 2140037 = 401257) (by norm_num)
theorem B2369429 : Blo 1052612 2369429 := bbase (se 6 (by rfl) ⟨55533, by rfl⟩ : syracuseStep 2369429 = 111067) (by norm_num)
theorem B1582997 : Blo 1052612 1582997 := bbase (se 6 (by rfl) ⟨37101, by rfl⟩ : syracuseStep 1582997 = 74203) (by norm_num)
theorem B1583021 : Blo 1052612 1583021 := bbase (se 3 (by rfl) ⟨296816, by rfl⟩ : syracuseStep 1583021 = 593633) (by norm_num)
theorem B1779637 : Blo 1052612 1779637 := bbase (se 5 (by rfl) ⟨83420, by rfl⟩ : syracuseStep 1779637 = 166841) (by norm_num)
theorem B1124285 : Blo 1052612 1124285 := bbase (se 3 (by rfl) ⟨210803, by rfl⟩ : syracuseStep 1124285 = 421607) (by norm_num)
theorem B1583045 : Blo 1052612 1583045 := bbase (se 4 (by rfl) ⟨148410, by rfl⟩ : syracuseStep 1583045 = 296821) (by norm_num)
theorem B2369501 : Blo 1052612 2369501 := bbase (se 3 (by rfl) ⟨444281, by rfl⟩ : syracuseStep 2369501 = 888563) (by norm_num)
theorem B1583069 : Blo 1052612 1583069 := bbase (se 3 (by rfl) ⟨296825, by rfl⟩ : syracuseStep 1583069 = 593651) (by norm_num)
theorem B1583093 : Blo 1052612 1583093 := bbase (se 5 (by rfl) ⟨74207, by rfl⟩ : syracuseStep 1583093 = 148415) (by norm_num)
theorem B1779725 : Blo 1052612 1779725 := bbase (se 3 (by rfl) ⟨333698, by rfl⟩ : syracuseStep 1779725 = 667397) (by norm_num)
theorem B1583117 : Blo 1052612 1583117 := bbase (se 3 (by rfl) ⟨296834, by rfl⟩ : syracuseStep 1583117 = 593669) (by norm_num)
theorem B2664485 : Blo 1052612 2664485 := bbase (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) (by norm_num)
theorem B2369573 : Blo 1052612 2369573 := bbase (se 4 (by rfl) ⟨222147, by rfl⟩ : syracuseStep 2369573 = 444295) (by norm_num)
theorem B1583141 : Blo 1052612 1583141 := bbase (se 4 (by rfl) ⟨148419, by rfl⟩ : syracuseStep 1583141 = 296839) (by norm_num)
theorem B1583165 : Blo 1052612 1583165 := bbase (se 3 (by rfl) ⟨296843, by rfl⟩ : syracuseStep 1583165 = 593687) (by norm_num)
theorem B6006869 : Blo 1052612 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B1583189 : Blo 1052612 1583189 := bbase (se 8 (by rfl) ⟨9276, by rfl⟩ : syracuseStep 1583189 = 18553) (by norm_num)
theorem B5711957 : Blo 1052612 5711957 := bbase (se 8 (by rfl) ⟨33468, by rfl⟩ : syracuseStep 5711957 = 66937) (by norm_num)
theorem B2369645 : Blo 1052612 2369645 := bbase (se 3 (by rfl) ⟨444308, by rfl⟩ : syracuseStep 2369645 = 888617) (by norm_num)
theorem B1583213 : Blo 1052612 1583213 := bbase (se 3 (by rfl) ⟨296852, by rfl⟩ : syracuseStep 1583213 = 593705) (by norm_num)
theorem B1583237 : Blo 1052612 1583237 := bbase (se 4 (by rfl) ⟨148428, by rfl⟩ : syracuseStep 1583237 = 296857) (by norm_num)
theorem B1779853 : Blo 1052612 1779853 := bbase (se 3 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 1779853 = 667445) (by norm_num)
theorem B1583261 : Blo 1052612 1583261 := bbase (se 3 (by rfl) ⟨296861, by rfl⟩ : syracuseStep 1583261 = 593723) (by norm_num)
theorem B2369717 : Blo 1052612 2369717 := bbase (se 5 (by rfl) ⟨111080, by rfl⟩ : syracuseStep 2369717 = 222161) (by norm_num)
theorem B1583285 : Blo 1052612 1583285 := bbase (se 5 (by rfl) ⟨74216, by rfl⟩ : syracuseStep 1583285 = 148433) (by norm_num)
theorem B1583309 : Blo 1052612 1583309 := bbase (se 3 (by rfl) ⟨296870, by rfl⟩ : syracuseStep 1583309 = 593741) (by norm_num)
theorem B4008149 : Blo 1052612 4008149 := bbase (se 7 (by rfl) ⟨46970, by rfl⟩ : syracuseStep 4008149 = 93941) (by norm_num)
theorem B2664677 : Blo 1052612 2664677 := bbase (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) (by norm_num)
theorem B1779941 : Blo 1052612 1779941 := bbase (se 4 (by rfl) ⟨166869, by rfl⟩ : syracuseStep 1779941 = 333739) (by norm_num)
theorem B1583333 : Blo 1052612 1583333 := bbase (se 4 (by rfl) ⟨148437, by rfl⟩ : syracuseStep 1583333 = 296875) (by norm_num)
theorem B8005877 : Blo 1052612 8005877 := bbase (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) (by norm_num)
theorem B2894069 : Blo 1052612 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B2369789 : Blo 1052612 2369789 := bbase (se 3 (by rfl) ⟨444335, by rfl⟩ : syracuseStep 2369789 = 888671) (by norm_num)
theorem B1583357 : Blo 1052612 1583357 := bbase (se 3 (by rfl) ⟨296879, by rfl⟩ : syracuseStep 1583357 = 593759) (by norm_num)
theorem B1583381 : Blo 1052612 1583381 := bbase (se 6 (by rfl) ⟨37110, by rfl⟩ : syracuseStep 1583381 = 74221) (by norm_num)
theorem B1583405 : Blo 1052612 1583405 := bbase (se 3 (by rfl) ⟨296888, by rfl⟩ : syracuseStep 1583405 = 593777) (by norm_num)
theorem B2369861 : Blo 1052612 2369861 := bbase (se 4 (by rfl) ⟨222174, by rfl⟩ : syracuseStep 2369861 = 444349) (by norm_num)
theorem B1583429 : Blo 1052612 1583429 := bbase (se 4 (by rfl) ⟨148446, by rfl⟩ : syracuseStep 1583429 = 296893) (by norm_num)
theorem B1583453 : Blo 1052612 1583453 := bbase (se 3 (by rfl) ⟨296897, by rfl⟩ : syracuseStep 1583453 = 593795) (by norm_num)
theorem B1780069 : Blo 1052612 1780069 := bbase (se 4 (by rfl) ⟨166881, by rfl⟩ : syracuseStep 1780069 = 333763) (by norm_num)
theorem B1583477 : Blo 1052612 1583477 := bbase (se 5 (by rfl) ⟨74225, by rfl⟩ : syracuseStep 1583477 = 148451) (by norm_num)
theorem B2369933 : Blo 1052612 2369933 := bbase (se 3 (by rfl) ⟨444362, by rfl⟩ : syracuseStep 2369933 = 888725) (by norm_num)
theorem B1583501 : Blo 1052612 1583501 := bbase (se 3 (by rfl) ⟨296906, by rfl⟩ : syracuseStep 1583501 = 593813) (by norm_num)
theorem B1583525 : Blo 1052612 1583525 := bbase (se 4 (by rfl) ⟨148455, by rfl⟩ : syracuseStep 1583525 = 296911) (by norm_num)
theorem B1780157 : Blo 1052612 1780157 := bbase (se 3 (by rfl) ⟨333779, by rfl⟩ : syracuseStep 1780157 = 667559) (by norm_num)
theorem B1583549 : Blo 1052612 1583549 := bbase (se 3 (by rfl) ⟨296915, by rfl⟩ : syracuseStep 1583549 = 593831) (by norm_num)
theorem B2370005 : Blo 1052612 2370005 := bbase (se 7 (by rfl) ⟨27773, by rfl⟩ : syracuseStep 2370005 = 55547) (by norm_num)
theorem B1583573 : Blo 1052612 1583573 := bbase (se 7 (by rfl) ⟨18557, by rfl⟩ : syracuseStep 1583573 = 37115) (by norm_num)
theorem B1157609 : Blo 1052612 1157609 := bbase (se 2 (by rfl) ⟨434103, by rfl⟩ : syracuseStep 1157609 = 868207) (by norm_num)
theorem B1583597 : Blo 1052612 1583597 := bbase (se 3 (by rfl) ⟨296924, by rfl⟩ : syracuseStep 1583597 = 593849) (by norm_num)
theorem B4008437 : Blo 1052612 4008437 := bbase (se 5 (by rfl) ⟨187895, by rfl⟩ : syracuseStep 4008437 = 375791) (by norm_num)
theorem B1583621 : Blo 1052612 1583621 := bbase (se 4 (by rfl) ⟨148464, by rfl⟩ : syracuseStep 1583621 = 296929) (by norm_num)
theorem B2370077 : Blo 1052612 2370077 := bbase (se 3 (by rfl) ⟨444389, by rfl⟩ : syracuseStep 2370077 = 888779) (by norm_num)
theorem B1583645 : Blo 1052612 1583645 := bbase (se 3 (by rfl) ⟨296933, by rfl⟩ : syracuseStep 1583645 = 593867) (by norm_num)
theorem B1583669 : Blo 1052612 1583669 := bbase (se 5 (by rfl) ⟨74234, by rfl⟩ : syracuseStep 1583669 = 148469) (by norm_num)
theorem B2665021 : Blo 1052612 2665021 := bbase (se 3 (by rfl) ⟨499691, by rfl⟩ : syracuseStep 2665021 = 999383) (by norm_num)
theorem B1780285 : Blo 1052612 1780285 := bbase (se 3 (by rfl) ⟨333803, by rfl⟩ : syracuseStep 1780285 = 667607) (by norm_num)
theorem B1583693 : Blo 1052612 1583693 := bbase (se 3 (by rfl) ⟨296942, by rfl⟩ : syracuseStep 1583693 = 593885) (by norm_num)
theorem B2370149 : Blo 1052612 2370149 := bbase (se 4 (by rfl) ⟨222201, by rfl⟩ : syracuseStep 2370149 = 444403) (by norm_num)
theorem B1583717 : Blo 1052612 1583717 := bbase (se 4 (by rfl) ⟨148473, by rfl⟩ : syracuseStep 1583717 = 296947) (by norm_num)
theorem B1583741 : Blo 1052612 1583741 := bbase (se 3 (by rfl) ⟨296951, by rfl⟩ : syracuseStep 1583741 = 593903) (by norm_num)
theorem B1780373 : Blo 1052612 1780373 := bbase (se 6 (by rfl) ⟨41727, by rfl⟩ : syracuseStep 1780373 = 83455) (by norm_num)
theorem B1583765 : Blo 1052612 1583765 := bbase (se 6 (by rfl) ⟨37119, by rfl⟩ : syracuseStep 1583765 = 74239) (by norm_num)
theorem B2665133 : Blo 1052612 2665133 := bbase (se 3 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 2665133 = 999425) (by norm_num)
theorem B2370221 : Blo 1052612 2370221 := bbase (se 3 (by rfl) ⟨444416, by rfl⟩ : syracuseStep 2370221 = 888833) (by norm_num)
theorem B1125037 : Blo 1052612 1125037 := bbase (se 3 (by rfl) ⟨210944, by rfl⟩ : syracuseStep 1125037 = 421889) (by norm_num)
theorem B1583789 : Blo 1052612 1583789 := bbase (se 3 (by rfl) ⟨296960, by rfl⟩ : syracuseStep 1583789 = 593921) (by norm_num)
theorem B1583813 : Blo 1052612 1583813 := bbase (se 4 (by rfl) ⟨148482, by rfl⟩ : syracuseStep 1583813 = 296965) (by norm_num)
theorem B25701077 : Blo 1052612 25701077 := bbase (se 7 (by rfl) ⟨301184, by rfl⟩ : syracuseStep 25701077 = 602369) (by norm_num)
theorem B1583837 : Blo 1052612 1583837 := bbase (se 3 (by rfl) ⟨296969, by rfl⟩ : syracuseStep 1583837 = 593939) (by norm_num)
theorem B2370293 : Blo 1052612 2370293 := bbase (se 5 (by rfl) ⟨111107, by rfl⟩ : syracuseStep 2370293 = 222215) (by norm_num)
theorem B1125109 : Blo 1052612 1125109 := bbase (se 5 (by rfl) ⟨52739, by rfl⟩ : syracuseStep 1125109 = 105479) (by norm_num)
theorem B1583861 : Blo 1052612 1583861 := bbase (se 5 (by rfl) ⟨74243, by rfl⟩ : syracuseStep 1583861 = 148487) (by norm_num)
theorem B1583885 : Blo 1052612 1583885 := bbase (se 3 (by rfl) ⟨296978, by rfl⟩ : syracuseStep 1583885 = 593957) (by norm_num)
theorem B1780501 : Blo 1052612 1780501 := bbase (se 6 (by rfl) ⟨41730, by rfl⟩ : syracuseStep 1780501 = 83461) (by norm_num)
theorem B1583909 : Blo 1052612 1583909 := bbase (se 4 (by rfl) ⟨148491, by rfl⟩ : syracuseStep 1583909 = 296983) (by norm_num)
theorem B2370365 : Blo 1052612 2370365 := bbase (se 3 (by rfl) ⟨444443, by rfl⟩ : syracuseStep 2370365 = 888887) (by norm_num)
theorem B1583933 : Blo 1052612 1583933 := bbase (se 3 (by rfl) ⟨296987, by rfl⟩ : syracuseStep 1583933 = 593975) (by norm_num)
theorem B1583957 : Blo 1052612 1583957 := bbase (se 9 (by rfl) ⟨4640, by rfl⟩ : syracuseStep 1583957 = 9281) (by norm_num)
theorem B2665325 : Blo 1052612 2665325 := bbase (se 3 (by rfl) ⟨499748, by rfl⟩ : syracuseStep 2665325 = 999497) (by norm_num)
theorem B1780589 : Blo 1052612 1780589 := bbase (se 3 (by rfl) ⟨333860, by rfl⟩ : syracuseStep 1780589 = 667721) (by norm_num)
theorem B1583981 : Blo 1052612 1583981 := bbase (se 3 (by rfl) ⟨296996, by rfl⟩ : syracuseStep 1583981 = 593993) (by norm_num)
theorem B2370437 : Blo 1052612 2370437 := bbase (se 4 (by rfl) ⟨222228, by rfl⟩ : syracuseStep 2370437 = 444457) (by norm_num)
theorem B1584005 : Blo 1052612 1584005 := bbase (se 4 (by rfl) ⟨148500, by rfl⟩ : syracuseStep 1584005 = 297001) (by norm_num)
theorem B1584029 : Blo 1052612 1584029 := bbase (se 3 (by rfl) ⟨297005, by rfl⟩ : syracuseStep 1584029 = 594011) (by norm_num)
theorem B1125289 : Blo 1052612 1125289 := bbase (se 2 (by rfl) ⟨421983, by rfl⟩ : syracuseStep 1125289 = 843967) (by norm_num)
theorem B1584053 : Blo 1052612 1584053 := bbase (se 5 (by rfl) ⟨74252, by rfl⟩ : syracuseStep 1584053 = 148505) (by norm_num)
theorem B2534341 : Blo 1052612 2534341 := bbase (se 4 (by rfl) ⟨237594, by rfl⟩ : syracuseStep 2534341 = 475189) (by norm_num)
theorem B2370509 : Blo 1052612 2370509 := bbase (se 3 (by rfl) ⟨444470, by rfl⟩ : syracuseStep 2370509 = 888941) (by norm_num)
theorem B1584077 : Blo 1052612 1584077 := bbase (se 3 (by rfl) ⟨297014, by rfl⟩ : syracuseStep 1584077 = 594029) (by norm_num)
theorem B1584101 : Blo 1052612 1584101 := bbase (se 4 (by rfl) ⟨148509, by rfl⟩ : syracuseStep 1584101 = 297019) (by norm_num)
theorem B1780717 : Blo 1052612 1780717 := bbase (se 3 (by rfl) ⟨333884, by rfl⟩ : syracuseStep 1780717 = 667769) (by norm_num)
theorem B1584125 : Blo 1052612 1584125 := bbase (se 3 (by rfl) ⟨297023, by rfl⟩ : syracuseStep 1584125 = 594047) (by norm_num)
theorem B2370581 : Blo 1052612 2370581 := bbase (se 6 (by rfl) ⟨55560, by rfl⟩ : syracuseStep 2370581 = 111121) (by norm_num)
theorem B1584149 : Blo 1052612 1584149 := bbase (se 6 (by rfl) ⟨37128, by rfl⟩ : syracuseStep 1584149 = 74257) (by norm_num)
theorem B3124261 : Blo 1052612 3124261 := bbase (se 4 (by rfl) ⟨292899, by rfl⟩ : syracuseStep 3124261 = 585799) (by norm_num)
theorem B2534437 : Blo 1052612 2534437 := bbase (se 4 (by rfl) ⟨237603, by rfl⟩ : syracuseStep 2534437 = 475207) (by norm_num)
theorem B1584173 : Blo 1052612 1584173 := bbase (se 3 (by rfl) ⟨297032, by rfl⟩ : syracuseStep 1584173 = 594065) (by norm_num)
theorem B1780805 : Blo 1052612 1780805 := bbase (se 4 (by rfl) ⟨166950, by rfl⟩ : syracuseStep 1780805 = 333901) (by norm_num)
theorem B1584197 : Blo 1052612 1584197 := bbase (se 4 (by rfl) ⟨148518, by rfl⟩ : syracuseStep 1584197 = 297037) (by norm_num)
theorem B2370653 : Blo 1052612 2370653 := bbase (se 3 (by rfl) ⟨444497, by rfl⟩ : syracuseStep 2370653 = 888995) (by norm_num)
theorem B1584221 : Blo 1052612 1584221 := bbase (se 3 (by rfl) ⟨297041, by rfl⟩ : syracuseStep 1584221 = 594083) (by norm_num)
theorem B1584245 : Blo 1052612 1584245 := bbase (se 5 (by rfl) ⟨74261, by rfl⟩ : syracuseStep 1584245 = 148523) (by norm_num)
theorem B1584269 : Blo 1052612 1584269 := bbase (se 3 (by rfl) ⟨297050, by rfl⟩ : syracuseStep 1584269 = 594101) (by norm_num)
theorem B2370725 : Blo 1052612 2370725 := bbase (se 4 (by rfl) ⟨222255, by rfl⟩ : syracuseStep 2370725 = 444511) (by norm_num)
theorem B1584293 : Blo 1052612 1584293 := bbase (se 4 (by rfl) ⟨148527, by rfl⟩ : syracuseStep 1584293 = 297055) (by norm_num)
theorem B1584317 : Blo 1052612 1584317 := bbase (se 3 (by rfl) ⟨297059, by rfl⟩ : syracuseStep 1584317 = 594119) (by norm_num)
theorem B2665669 : Blo 1052612 2665669 := bbase (se 4 (by rfl) ⟨249906, by rfl⟩ : syracuseStep 2665669 = 499813) (by norm_num)
theorem B1780933 : Blo 1052612 1780933 := bbase (se 4 (by rfl) ⟨166962, by rfl⟩ : syracuseStep 1780933 = 333925) (by norm_num)
theorem B1584341 : Blo 1052612 1584341 := bbase (se 7 (by rfl) ⟨18566, by rfl⟩ : syracuseStep 1584341 = 37133) (by norm_num)
theorem B2370797 : Blo 1052612 2370797 := bbase (se 3 (by rfl) ⟨444524, by rfl⟩ : syracuseStep 2370797 = 889049) (by norm_num)
theorem B1584365 : Blo 1052612 1584365 := bbase (se 3 (by rfl) ⟨297068, by rfl⟩ : syracuseStep 1584365 = 594137) (by norm_num)
theorem B6008053 : Blo 1052612 6008053 := bbase (se 5 (by rfl) ⟨281627, by rfl⟩ : syracuseStep 6008053 = 563255) (by norm_num)
theorem B1584389 : Blo 1052612 1584389 := bbase (se 4 (by rfl) ⟨148536, by rfl⟩ : syracuseStep 1584389 = 297073) (by norm_num)
theorem B1781021 : Blo 1052612 1781021 := bbase (se 3 (by rfl) ⟨333941, by rfl⟩ : syracuseStep 1781021 = 667883) (by norm_num)
theorem B1584413 : Blo 1052612 1584413 := bbase (se 3 (by rfl) ⟨297077, by rfl⟩ : syracuseStep 1584413 = 594155) (by norm_num)
theorem B2665781 : Blo 1052612 2665781 := bbase (se 5 (by rfl) ⟨124958, by rfl⟩ : syracuseStep 2665781 = 249917) (by norm_num)
theorem B2370869 : Blo 1052612 2370869 := bbase (se 5 (by rfl) ⟨111134, by rfl⟩ : syracuseStep 2370869 = 222269) (by norm_num)
theorem B1584437 : Blo 1052612 1584437 := bbase (se 5 (by rfl) ⟨74270, by rfl⟩ : syracuseStep 1584437 = 148541) (by norm_num)
theorem B1584461 : Blo 1052612 1584461 := bbase (se 3 (by rfl) ⟨297086, by rfl⟩ : syracuseStep 1584461 = 594173) (by norm_num)
theorem B1125733 : Blo 1052612 1125733 := bbase (se 4 (by rfl) ⟨105537, by rfl⟩ : syracuseStep 1125733 = 211075) (by norm_num)
theorem B1584485 : Blo 1052612 1584485 := bbase (se 4 (by rfl) ⟨148545, by rfl⟩ : syracuseStep 1584485 = 297091) (by norm_num)
theorem B2370941 : Blo 1052612 2370941 := bbase (se 3 (by rfl) ⟨444551, by rfl⟩ : syracuseStep 2370941 = 889103) (by norm_num)
theorem B1584509 : Blo 1052612 1584509 := bbase (se 3 (by rfl) ⟨297095, by rfl⟩ : syracuseStep 1584509 = 594191) (by norm_num)
theorem B1584533 : Blo 1052612 1584533 := bbase (se 6 (by rfl) ⟨37137, by rfl⟩ : syracuseStep 1584533 = 74275) (by norm_num)
theorem B1781149 : Blo 1052612 1781149 := bbase (se 3 (by rfl) ⟨333965, by rfl⟩ : syracuseStep 1781149 = 667931) (by norm_num)
theorem B1584557 : Blo 1052612 1584557 := bbase (se 3 (by rfl) ⟨297104, by rfl⟩ : syracuseStep 1584557 = 594209) (by norm_num)
theorem B2371013 : Blo 1052612 2371013 := bbase (se 4 (by rfl) ⟨222282, by rfl⟩ : syracuseStep 2371013 = 444565) (by norm_num)
theorem B1584581 : Blo 1052612 1584581 := bbase (se 4 (by rfl) ⟨148554, by rfl⟩ : syracuseStep 1584581 = 297109) (by norm_num)
theorem B1584605 : Blo 1052612 1584605 := bbase (se 3 (by rfl) ⟨297113, by rfl⟩ : syracuseStep 1584605 = 594227) (by norm_num)
theorem B1125857 : Blo 1052612 1125857 := bbase (se 2 (by rfl) ⟨422196, by rfl⟩ : syracuseStep 1125857 = 844393) (by norm_num)
theorem B2665973 : Blo 1052612 2665973 := bbase (se 5 (by rfl) ⟨124967, by rfl⟩ : syracuseStep 2665973 = 249935) (by norm_num)
theorem B1781237 : Blo 1052612 1781237 := bbase (se 5 (by rfl) ⟨83495, by rfl⟩ : syracuseStep 1781237 = 166991) (by norm_num)
theorem B1584629 : Blo 1052612 1584629 := bbase (se 5 (by rfl) ⟨74279, by rfl⟩ : syracuseStep 1584629 = 148559) (by norm_num)
theorem B2371085 : Blo 1052612 2371085 := bbase (se 3 (by rfl) ⟨444578, by rfl⟩ : syracuseStep 2371085 = 889157) (by norm_num)
theorem B1584653 : Blo 1052612 1584653 := bbase (se 3 (by rfl) ⟨297122, by rfl⟩ : syracuseStep 1584653 = 594245) (by norm_num)
theorem B1584677 : Blo 1052612 1584677 := bbase (se 4 (by rfl) ⟨148563, by rfl⟩ : syracuseStep 1584677 = 297127) (by norm_num)
theorem B1584701 : Blo 1052612 1584701 := bbase (se 3 (by rfl) ⟨297131, by rfl⟩ : syracuseStep 1584701 = 594263) (by norm_num)
theorem B2371157 : Blo 1052612 2371157 := bbase (se 8 (by rfl) ⟨13893, by rfl⟩ : syracuseStep 2371157 = 27787) (by norm_num)
theorem B1584725 : Blo 1052612 1584725 := bbase (se 8 (by rfl) ⟨9285, by rfl⟩ : syracuseStep 1584725 = 18571) (by norm_num)
theorem B1584749 : Blo 1052612 1584749 := bbase (se 3 (by rfl) ⟨297140, by rfl⟩ : syracuseStep 1584749 = 594281) (by norm_num)
theorem B1781365 : Blo 1052612 1781365 := bbase (se 5 (by rfl) ⟨83501, by rfl⟩ : syracuseStep 1781365 = 167003) (by norm_num)
theorem B1584773 : Blo 1052612 1584773 := bbase (se 4 (by rfl) ⟨148572, by rfl⟩ : syracuseStep 1584773 = 297145) (by norm_num)
theorem B4009621 : Blo 1052612 4009621 := bbase (se 6 (by rfl) ⟨93975, by rfl⟩ : syracuseStep 4009621 = 187951) (by norm_num)
theorem B2371229 : Blo 1052612 2371229 := bbase (se 3 (by rfl) ⟨444605, by rfl⟩ : syracuseStep 2371229 = 889211) (by norm_num)
theorem B1584797 : Blo 1052612 1584797 := bbase (se 3 (by rfl) ⟨297149, by rfl⟩ : syracuseStep 1584797 = 594299) (by norm_num)
theorem B1584821 : Blo 1052612 1584821 := bbase (se 5 (by rfl) ⟨74288, by rfl⟩ : syracuseStep 1584821 = 148577) (by norm_num)
theorem B1781453 : Blo 1052612 1781453 := bbase (se 3 (by rfl) ⟨334022, by rfl⟩ : syracuseStep 1781453 = 668045) (by norm_num)
theorem B1584845 : Blo 1052612 1584845 := bbase (se 3 (by rfl) ⟨297158, by rfl⟩ : syracuseStep 1584845 = 594317) (by norm_num)
theorem B1126109 : Blo 1052612 1126109 := bbase (se 3 (by rfl) ⟨211145, by rfl⟩ : syracuseStep 1126109 = 422291) (by norm_num)
theorem B2371301 : Blo 1052612 2371301 := bbase (se 4 (by rfl) ⟨222309, by rfl⟩ : syracuseStep 2371301 = 444619) (by norm_num)
theorem B1584869 : Blo 1052612 1584869 := bbase (se 4 (by rfl) ⟨148581, by rfl⟩ : syracuseStep 1584869 = 297163) (by norm_num)
theorem B1584893 : Blo 1052612 1584893 := bbase (se 3 (by rfl) ⟨297167, by rfl⟩ : syracuseStep 1584893 = 594335) (by norm_num)
theorem B1584917 : Blo 1052612 1584917 := bbase (se 6 (by rfl) ⟨37146, by rfl⟩ : syracuseStep 1584917 = 74293) (by norm_num)
theorem B2371373 : Blo 1052612 2371373 := bbase (se 3 (by rfl) ⟨444632, by rfl⟩ : syracuseStep 2371373 = 889265) (by norm_num)
theorem B2666317 : Blo 1052612 2666317 := bbase (se 3 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 2666317 = 999869) (by norm_num)
theorem B1781581 : Blo 1052612 1781581 := bbase (se 3 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 1781581 = 668093) (by norm_num)
theorem B2371445 : Blo 1052612 2371445 := bbase (se 5 (by rfl) ⟨111161, by rfl⟩ : syracuseStep 2371445 = 222323) (by norm_num)
theorem B1519517 : Blo 1052612 1519517 := bbase (se 3 (by rfl) ⟨284909, by rfl⟩ : syracuseStep 1519517 = 569819) (by norm_num)
theorem B1781669 : Blo 1052612 1781669 := bbase (se 4 (by rfl) ⟨167031, by rfl⟩ : syracuseStep 1781669 = 334063) (by norm_num)
theorem B2666429 : Blo 1052612 2666429 := bbase (se 3 (by rfl) ⟨499955, by rfl⟩ : syracuseStep 2666429 = 999911) (by norm_num)
theorem B2371517 : Blo 1052612 2371517 := bbase (se 3 (by rfl) ⟨444659, by rfl⟩ : syracuseStep 2371517 = 889319) (by norm_num)
theorem B4009925 : Blo 1052612 4009925 := bbase (se 4 (by rfl) ⟨375930, by rfl⟩ : syracuseStep 4009925 = 751861) (by norm_num)
theorem B2371589 : Blo 1052612 2371589 := bbase (se 4 (by rfl) ⟨222336, by rfl⟩ : syracuseStep 2371589 = 444673) (by norm_num)
theorem B1781797 : Blo 1052612 1781797 := bbase (se 4 (by rfl) ⟨167043, by rfl⟩ : syracuseStep 1781797 = 334087) (by norm_num)
theorem B2404397 : Blo 1052612 2404397 := bbase (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) (by norm_num)
theorem B2371661 : Blo 1052612 2371661 := bbase (se 3 (by rfl) ⟨444686, by rfl⟩ : syracuseStep 2371661 = 889373) (by norm_num)
theorem B2535533 : Blo 1052612 2535533 := bbase (se 3 (by rfl) ⟨475412, by rfl⟩ : syracuseStep 2535533 = 950825) (by norm_num)
theorem B2666621 : Blo 1052612 2666621 := bbase (se 3 (by rfl) ⟨499991, by rfl⟩ : syracuseStep 2666621 = 999983) (by norm_num)
theorem B1781885 : Blo 1052612 1781885 := bbase (se 3 (by rfl) ⟨334103, by rfl⟩ : syracuseStep 1781885 = 668207) (by norm_num)
theorem B2371733 : Blo 1052612 2371733 := bbase (se 6 (by rfl) ⟨55587, by rfl⟩ : syracuseStep 2371733 = 111175) (by norm_num)
theorem B1126553 : Blo 1052612 1126553 := bbase (se 2 (by rfl) ⟨422457, by rfl⟩ : syracuseStep 1126553 = 844915) (by norm_num)
theorem B2371805 : Blo 1052612 2371805 := bbase (se 3 (by rfl) ⟨444713, by rfl⟩ : syracuseStep 2371805 = 889427) (by norm_num)
theorem B1782013 : Blo 1052612 1782013 := bbase (se 3 (by rfl) ⟨334127, by rfl⟩ : syracuseStep 1782013 = 668255) (by norm_num)
theorem B2371877 : Blo 1052612 2371877 := bbase (se 4 (by rfl) ⟨222363, by rfl⟩ : syracuseStep 2371877 = 444727) (by norm_num)
theorem B3256613 : Blo 1052612 3256613 := bbase (se 4 (by rfl) ⟨305307, by rfl⟩ : syracuseStep 3256613 = 610615) (by norm_num)
theorem B13873493 : Blo 1052612 13873493 := bbase (se 10 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 13873493 = 40645) (by norm_num)
theorem B1782101 : Blo 1052612 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B2371949 : Blo 1052612 2371949 := bbase (se 3 (by rfl) ⟨444740, by rfl⟩ : syracuseStep 2371949 = 889481) (by norm_num)
theorem B1126801 : Blo 1052612 1126801 := bbase (se 2 (by rfl) ⟨422550, by rfl⟩ : syracuseStep 1126801 = 845101) (by norm_num)
theorem B4501925 : Blo 1052612 4501925 := bbase (se 4 (by rfl) ⟨422055, by rfl⟩ : syracuseStep 4501925 = 844111) (by norm_num)
theorem B2372021 : Blo 1052612 2372021 := bbase (se 5 (by rfl) ⟨111188, by rfl⟩ : syracuseStep 2372021 = 222377) (by norm_num)
theorem B2666965 : Blo 1052612 2666965 := bbase (se 7 (by rfl) ⟨31253, by rfl⟩ : syracuseStep 2666965 = 62507) (by norm_num)
theorem B1782229 : Blo 1052612 1782229 := bbase (se 7 (by rfl) ⟨20885, by rfl⟩ : syracuseStep 1782229 = 41771) (by norm_num)
theorem B2372093 : Blo 1052612 2372093 := bbase (se 3 (by rfl) ⟨444767, by rfl⟩ : syracuseStep 2372093 = 889535) (by norm_num)
theorem B1782317 : Blo 1052612 1782317 := bbase (se 3 (by rfl) ⟨334184, by rfl⟩ : syracuseStep 1782317 = 668369) (by norm_num)
theorem B2667077 : Blo 1052612 2667077 := bbase (se 4 (by rfl) ⟨250038, by rfl⟩ : syracuseStep 2667077 = 500077) (by norm_num)
theorem B2372165 : Blo 1052612 2372165 := bbase (se 4 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 2372165 = 444781) (by norm_num)
theorem B2372237 : Blo 1052612 2372237 := bbase (se 3 (by rfl) ⟨444794, by rfl⟩ : syracuseStep 2372237 = 889589) (by norm_num)
theorem B1782445 : Blo 1052612 1782445 := bbase (se 3 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 1782445 = 668417) (by norm_num)
theorem B4502213 : Blo 1052612 4502213 := bbase (se 4 (by rfl) ⟨422082, by rfl⟩ : syracuseStep 4502213 = 844165) (by norm_num)
theorem B2372309 : Blo 1052612 2372309 := bbase (se 7 (by rfl) ⟨27800, by rfl⟩ : syracuseStep 2372309 = 55601) (by norm_num)
theorem B2667269 : Blo 1052612 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B1782533 : Blo 1052612 1782533 := bbase (se 4 (by rfl) ⟨167112, by rfl⟩ : syracuseStep 1782533 = 334225) (by norm_num)
theorem B2372381 : Blo 1052612 2372381 := bbase (se 3 (by rfl) ⟨444821, by rfl⟩ : syracuseStep 2372381 = 889643) (by norm_num)
theorem B1127245 : Blo 1052612 1127245 := bbase (se 3 (by rfl) ⟨211358, by rfl⟩ : syracuseStep 1127245 = 422717) (by norm_num)
theorem B2372453 : Blo 1052612 2372453 := bbase (se 4 (by rfl) ⟨222417, by rfl⟩ : syracuseStep 2372453 = 444835) (by norm_num)
theorem B1782661 : Blo 1052612 1782661 := bbase (se 4 (by rfl) ⟨167124, by rfl⟩ : syracuseStep 1782661 = 334249) (by norm_num)
theorem B1127305 : Blo 1052612 1127305 := bbase (se 2 (by rfl) ⟨422739, by rfl⟩ : syracuseStep 1127305 = 845479) (by norm_num)
theorem B2372525 : Blo 1052612 2372525 := bbase (se 3 (by rfl) ⟨444848, by rfl⟩ : syracuseStep 2372525 = 889697) (by norm_num)
theorem B1782749 : Blo 1052612 1782749 := bbase (se 3 (by rfl) ⟨334265, by rfl⟩ : syracuseStep 1782749 = 668531) (by norm_num)
theorem B2372597 : Blo 1052612 2372597 := bbase (se 5 (by rfl) ⟨111215, by rfl⟩ : syracuseStep 2372597 = 222431) (by norm_num)
theorem B2536493 : Blo 1052612 2536493 := bbase (se 3 (by rfl) ⟨475592, by rfl⟩ : syracuseStep 2536493 = 951185) (by norm_num)
theorem B2372669 : Blo 1052612 2372669 := bbase (se 3 (by rfl) ⟨444875, by rfl⟩ : syracuseStep 2372669 = 889751) (by norm_num)
theorem B2667613 : Blo 1052612 2667613 := bbase (se 3 (by rfl) ⟨500177, by rfl⟩ : syracuseStep 2667613 = 1000355) (by norm_num)
theorem B1782877 : Blo 1052612 1782877 := bbase (se 3 (by rfl) ⟨334289, by rfl⟩ : syracuseStep 1782877 = 668579) (by norm_num)
theorem B5059685 : Blo 1052612 5059685 := bbase (se 4 (by rfl) ⟨474345, by rfl⟩ : syracuseStep 5059685 = 948691) (by norm_num)
theorem B2372741 : Blo 1052612 2372741 := bbase (se 4 (by rfl) ⟨222444, by rfl⟩ : syracuseStep 2372741 = 444889) (by norm_num)
theorem B6010037 : Blo 1052612 6010037 := bbase (se 5 (by rfl) ⟨281720, by rfl⟩ : syracuseStep 6010037 = 563441) (by norm_num)
theorem B1782965 : Blo 1052612 1782965 := bbase (se 5 (by rfl) ⟨83576, by rfl⟩ : syracuseStep 1782965 = 167153) (by norm_num)
theorem B1127621 : Blo 1052612 1127621 := bbase (se 4 (by rfl) ⟨105714, by rfl⟩ : syracuseStep 1127621 = 211429) (by norm_num)
theorem B2667725 : Blo 1052612 2667725 := bbase (se 3 (by rfl) ⟨500198, by rfl⟩ : syracuseStep 2667725 = 1000397) (by norm_num)
theorem B2372813 : Blo 1052612 2372813 := bbase (se 3 (by rfl) ⟨444902, by rfl⟩ : syracuseStep 2372813 = 889805) (by norm_num)
theorem B2372885 : Blo 1052612 2372885 := bbase (se 6 (by rfl) ⟨55614, by rfl⟩ : syracuseStep 2372885 = 111229) (by norm_num)
theorem B2372957 : Blo 1052612 2372957 := bbase (se 3 (by rfl) ⟨444929, by rfl⟩ : syracuseStep 2372957 = 889859) (by norm_num)
theorem B2667917 : Blo 1052612 2667917 := bbase (se 3 (by rfl) ⟨500234, by rfl⟩ : syracuseStep 2667917 = 1000469) (by norm_num)
theorem B2373029 : Blo 1052612 2373029 := bbase (se 4 (by rfl) ⟨222471, by rfl⟩ : syracuseStep 2373029 = 444943) (by norm_num)
theorem B4502965 : Blo 1052612 4502965 := bbase (se 5 (by rfl) ⟨211076, by rfl⟩ : syracuseStep 4502965 = 422153) (by norm_num)
theorem B2373101 : Blo 1052612 2373101 := bbase (se 3 (by rfl) ⟨444956, by rfl⟩ : syracuseStep 2373101 = 889913) (by norm_num)
theorem B3552821 : Blo 1052612 3552821 := bbase (se 5 (by rfl) ⟨166538, by rfl⟩ : syracuseStep 3552821 = 333077) (by norm_num)
theorem B2373173 : Blo 1052612 2373173 := bbase (se 5 (by rfl) ⟨111242, by rfl⟩ : syracuseStep 2373173 = 222485) (by norm_num)
theorem B73021013 : Blo 1052612 73021013 := bbase (se 8 (by rfl) ⟨427857, by rfl⟩ : syracuseStep 73021013 = 855715) (by norm_num)
theorem B2373245 : Blo 1052612 2373245 := bbase (se 3 (by rfl) ⟨444983, by rfl⟩ : syracuseStep 2373245 = 889967) (by norm_num)
theorem B1128065 : Blo 1052612 1128065 := bbase (se 2 (by rfl) ⟨423024, by rfl⟩ : syracuseStep 1128065 = 846049) (by norm_num)
theorem B1128125 : Blo 1052612 1128125 := bbase (se 3 (by rfl) ⟨211523, by rfl⟩ : syracuseStep 1128125 = 423047) (by norm_num)
theorem B2373317 : Blo 1052612 2373317 := bbase (se 4 (by rfl) ⟨222498, by rfl⟩ : syracuseStep 2373317 = 444997) (by norm_num)
theorem B2668261 : Blo 1052612 2668261 := bbase (se 4 (by rfl) ⟨250149, by rfl⟩ : syracuseStep 2668261 = 500299) (by norm_num)
theorem B2406149 : Blo 1052612 2406149 := bbase (se 4 (by rfl) ⟨225576, by rfl⟩ : syracuseStep 2406149 = 451153) (by norm_num)
theorem B2373389 : Blo 1052612 2373389 := bbase (se 3 (by rfl) ⟨445010, by rfl⟩ : syracuseStep 2373389 = 890021) (by norm_num)
theorem B1128253 : Blo 1052612 1128253 := bbase (se 3 (by rfl) ⟨211547, by rfl⟩ : syracuseStep 1128253 = 423095) (by norm_num)
theorem B2668373 : Blo 1052612 2668373 := bbase (se 9 (by rfl) ⟨7817, by rfl⟩ : syracuseStep 2668373 = 15635) (by norm_num)
theorem B2373461 : Blo 1052612 2373461 := bbase (se 9 (by rfl) ⟨6953, by rfl⟩ : syracuseStep 2373461 = 13907) (by norm_num)
theorem B2373533 : Blo 1052612 2373533 := bbase (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) (by norm_num)
theorem B3553253 : Blo 1052612 3553253 := bbase (se 4 (by rfl) ⟨333117, by rfl⟩ : syracuseStep 3553253 = 666235) (by norm_num)
theorem B2373605 : Blo 1052612 2373605 := bbase (se 4 (by rfl) ⟨222525, by rfl⟩ : syracuseStep 2373605 = 445051) (by norm_num)
theorem B2668565 : Blo 1052612 2668565 := bbase (se 6 (by rfl) ⟨62544, by rfl⟩ : syracuseStep 2668565 = 125089) (by norm_num)
theorem B2373677 : Blo 1052612 2373677 := bbase (se 3 (by rfl) ⟨445064, by rfl⟩ : syracuseStep 2373677 = 890129) (by norm_num)
theorem B6764597 : Blo 1052612 6764597 := bbase (se 5 (by rfl) ⟨317090, by rfl⟩ : syracuseStep 6764597 = 634181) (by norm_num)
theorem B2373749 : Blo 1052612 2373749 := bbase (se 5 (by rfl) ⟨111269, by rfl⟩ : syracuseStep 2373749 = 222539) (by norm_num)
theorem B4503701 : Blo 1052612 4503701 := bbase (se 6 (by rfl) ⟨105555, by rfl⟩ : syracuseStep 4503701 = 211111) (by norm_num)
theorem B2373821 : Blo 1052612 2373821 := bbase (se 3 (by rfl) ⟨445091, by rfl⟩ : syracuseStep 2373821 = 890183) (by norm_num)
theorem B2373893 : Blo 1052612 2373893 := bbase (se 4 (by rfl) ⟨222552, by rfl⟩ : syracuseStep 2373893 = 445105) (by norm_num)
theorem B2373965 : Blo 1052612 2373965 := bbase (se 3 (by rfl) ⟨445118, by rfl⟩ : syracuseStep 2373965 = 890237) (by norm_num)
theorem B2668909 : Blo 1052612 2668909 := bbase (se 3 (by rfl) ⟨500420, by rfl⟩ : syracuseStep 2668909 = 1000841) (by norm_num)
theorem B3553685 : Blo 1052612 3553685 := bbase (se 6 (by rfl) ⟨83289, by rfl⟩ : syracuseStep 3553685 = 166579) (by norm_num)
theorem B2374037 : Blo 1052612 2374037 := bbase (se 6 (by rfl) ⟨55641, by rfl⟩ : syracuseStep 2374037 = 111283) (by norm_num)
theorem B2669021 : Blo 1052612 2669021 := bbase (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) (by norm_num)
theorem B2374109 : Blo 1052612 2374109 := bbase (se 3 (by rfl) ⟨445145, by rfl⟩ : syracuseStep 2374109 = 890291) (by norm_num)
theorem B2374181 : Blo 1052612 2374181 := bbase (se 4 (by rfl) ⟨222579, by rfl⟩ : syracuseStep 2374181 = 445159) (by norm_num)
theorem B1522229 : Blo 1052612 1522229 := bbase (se 5 (by rfl) ⟨71354, by rfl⟩ : syracuseStep 1522229 = 142709) (by norm_num)
theorem B2374253 : Blo 1052612 2374253 := bbase (se 3 (by rfl) ⟨445172, by rfl⟩ : syracuseStep 2374253 = 890345) (by norm_num)
theorem B2669213 : Blo 1052612 2669213 := bbase (se 3 (by rfl) ⟨500477, by rfl⟩ : syracuseStep 2669213 = 1000955) (by norm_num)
theorem B2374325 : Blo 1052612 2374325 := bbase (se 5 (by rfl) ⟨111296, by rfl⟩ : syracuseStep 2374325 = 222593) (by norm_num)
theorem B2407141 : Blo 1052612 2407141 := bbase (se 4 (by rfl) ⟨225669, by rfl⟩ : syracuseStep 2407141 = 451339) (by norm_num)
theorem B2374397 : Blo 1052612 2374397 := bbase (se 3 (by rfl) ⟨445199, by rfl⟩ : syracuseStep 2374397 = 890399) (by norm_num)
theorem B2538253 : Blo 1052612 2538253 := bbase (se 3 (by rfl) ⟨475922, by rfl⟩ : syracuseStep 2538253 = 951845) (by norm_num)
theorem B3554117 : Blo 1052612 3554117 := bbase (se 4 (by rfl) ⟨333198, by rfl⟩ : syracuseStep 3554117 = 666397) (by norm_num)
theorem B4275013 : Blo 1052612 4275013 := bbase (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) (by norm_num)
theorem B2374469 : Blo 1052612 2374469 := bbase (se 4 (by rfl) ⟨222606, by rfl⟩ : syracuseStep 2374469 = 445213) (by norm_num)
theorem B1424237 : Blo 1052612 1424237 := bbase (se 3 (by rfl) ⟨267044, by rfl⟩ : syracuseStep 1424237 = 534089) (by norm_num)
theorem B1424269 : Blo 1052612 1424269 := bbase (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) (by norm_num)
theorem B2374541 : Blo 1052612 2374541 := bbase (se 3 (by rfl) ⟨445226, by rfl⟩ : syracuseStep 2374541 = 890453) (by norm_num)
theorem B9124757 : Blo 1052612 9124757 := bbase (se 6 (by rfl) ⟨213861, by rfl⟩ : syracuseStep 9124757 = 427723) (by norm_num)
theorem B1686485 : Blo 1052612 1686485 := bbase (se 7 (by rfl) ⟨19763, by rfl⟩ : syracuseStep 1686485 = 39527) (by norm_num)
theorem B2374613 : Blo 1052612 2374613 := bbase (se 7 (by rfl) ⟨27827, by rfl⟩ : syracuseStep 2374613 = 55655) (by norm_num)
theorem B2669557 : Blo 1052612 2669557 := bbase (se 5 (by rfl) ⟨125135, by rfl⟩ : syracuseStep 2669557 = 250271) (by norm_num)
theorem B2538485 : Blo 1052612 2538485 := bbase (se 5 (by rfl) ⟨118991, by rfl⟩ : syracuseStep 2538485 = 237983) (by norm_num)
theorem B2374685 : Blo 1052612 2374685 := bbase (se 3 (by rfl) ⟨445253, by rfl⟩ : syracuseStep 2374685 = 890507) (by norm_num)
theorem B2669669 : Blo 1052612 2669669 := bbase (se 4 (by rfl) ⟨250281, by rfl⟩ : syracuseStep 2669669 = 500563) (by norm_num)
theorem B2374757 : Blo 1052612 2374757 := bbase (se 4 (by rfl) ⟨222633, by rfl⟩ : syracuseStep 2374757 = 445267) (by norm_num)
theorem B2374829 : Blo 1052612 2374829 := bbase (se 3 (by rfl) ⟨445280, by rfl⟩ : syracuseStep 2374829 = 890561) (by norm_num)
theorem B8994037 : Blo 1052612 8994037 := bbase (se 5 (by rfl) ⟨421595, by rfl⟩ : syracuseStep 8994037 = 843191) (by norm_num)
theorem B3554549 : Blo 1052612 3554549 := bbase (se 5 (by rfl) ⟨166619, by rfl⟩ : syracuseStep 3554549 = 333239) (by norm_num)
theorem B2374901 : Blo 1052612 2374901 := bbase (se 5 (by rfl) ⟨111323, by rfl⟩ : syracuseStep 2374901 = 222647) (by norm_num)
theorem B2669861 : Blo 1052612 2669861 := bbase (se 4 (by rfl) ⟨250299, by rfl⟩ : syracuseStep 2669861 = 500599) (by norm_num)
theorem B2997557 : Blo 1052612 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B2374973 : Blo 1052612 2374973 := bbase (se 3 (by rfl) ⟨445307, by rfl⟩ : syracuseStep 2374973 = 890615) (by norm_num)
theorem B1097045 : Blo 1052612 1097045 := bbase (se 11 (by rfl) ⟨803, by rfl⟩ : syracuseStep 1097045 = 1607) (by norm_num)
theorem B6012245 : Blo 1052612 6012245 := bbase (se 11 (by rfl) ⟨4403, by rfl⟩ : syracuseStep 6012245 = 8807) (by norm_num)
theorem B2375045 : Blo 1052612 2375045 := bbase (se 4 (by rfl) ⟨222660, by rfl⟩ : syracuseStep 2375045 = 445321) (by norm_num)
theorem B2375117 : Blo 1052612 2375117 := bbase (se 3 (by rfl) ⟨445334, by rfl⟩ : syracuseStep 2375117 = 890669) (by norm_num)
theorem B2375189 : Blo 1052612 2375189 := bbase (se 6 (by rfl) ⟨55668, by rfl⟩ : syracuseStep 2375189 = 111337) (by norm_num)
theorem B2375261 : Blo 1052612 2375261 := bbase (se 3 (by rfl) ⟨445361, by rfl⟩ : syracuseStep 2375261 = 890723) (by norm_num)
theorem B2670205 : Blo 1052612 2670205 := bbase (se 3 (by rfl) ⟨500663, by rfl⟩ : syracuseStep 2670205 = 1001327) (by norm_num)
theorem B3554981 : Blo 1052612 3554981 := bbase (se 4 (by rfl) ⟨333279, by rfl⟩ : syracuseStep 3554981 = 666559) (by norm_num)
theorem B2375333 : Blo 1052612 2375333 := bbase (se 4 (by rfl) ⟨222687, by rfl⟩ : syracuseStep 2375333 = 445375) (by norm_num)
theorem B2670317 : Blo 1052612 2670317 := bbase (se 3 (by rfl) ⟨500684, by rfl⟩ : syracuseStep 2670317 = 1001369) (by norm_num)
theorem B2375405 : Blo 1052612 2375405 := bbase (se 3 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 2375405 = 890777) (by norm_num)
theorem B2375477 : Blo 1052612 2375477 := bbase (se 5 (by rfl) ⟨111350, by rfl⟩ : syracuseStep 2375477 = 222701) (by norm_num)
theorem B2375549 : Blo 1052612 2375549 := bbase (se 3 (by rfl) ⟨445415, by rfl⟩ : syracuseStep 2375549 = 890831) (by norm_num)
theorem B2670509 : Blo 1052612 2670509 := bbase (se 3 (by rfl) ⟨500720, by rfl⟩ : syracuseStep 2670509 = 1001441) (by norm_num)
theorem B2408381 : Blo 1052612 2408381 := bbase (se 3 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 2408381 = 903143) (by norm_num)
theorem B2375621 : Blo 1052612 2375621 := bbase (se 4 (by rfl) ⟨222714, by rfl⟩ : syracuseStep 2375621 = 445429) (by norm_num)
theorem B2375693 : Blo 1052612 2375693 := bbase (se 3 (by rfl) ⟨445442, by rfl⟩ : syracuseStep 2375693 = 890885) (by norm_num)
theorem B3424277 : Blo 1052612 3424277 := bbase (se 6 (by rfl) ⟨80256, by rfl⟩ : syracuseStep 3424277 = 160513) (by norm_num)
theorem B2998309 : Blo 1052612 2998309 := bbase (se 4 (by rfl) ⟨281091, by rfl⟩ : syracuseStep 2998309 = 562183) (by norm_num)
theorem B3555413 : Blo 1052612 3555413 := bbase (se 8 (by rfl) ⟨20832, by rfl⟩ : syracuseStep 3555413 = 41665) (by norm_num)
theorem B2375765 : Blo 1052612 2375765 := bbase (se 8 (by rfl) ⟨13920, by rfl⟩ : syracuseStep 2375765 = 27841) (by norm_num)
theorem B2375837 : Blo 1052612 2375837 := bbase (se 3 (by rfl) ⟨445469, by rfl⟩ : syracuseStep 2375837 = 890939) (by norm_num)
theorem B5062837 : Blo 1052612 5062837 := bbase (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) (by norm_num)
theorem B1425605 : Blo 1052612 1425605 := bbase (se 4 (by rfl) ⟨133650, by rfl⟩ : syracuseStep 1425605 = 267301) (by norm_num)
theorem B2375909 : Blo 1052612 2375909 := bbase (se 4 (by rfl) ⟨222741, by rfl⟩ : syracuseStep 2375909 = 445483) (by norm_num)
theorem B2670853 : Blo 1052612 2670853 := bbase (se 4 (by rfl) ⟨250392, by rfl⟩ : syracuseStep 2670853 = 500785) (by norm_num)
theorem B2375981 : Blo 1052612 2375981 := bbase (se 3 (by rfl) ⟨445496, by rfl⟩ : syracuseStep 2375981 = 890993) (by norm_num)
theorem B2670965 : Blo 1052612 2670965 := bbase (se 5 (by rfl) ⟨125201, by rfl⟩ : syracuseStep 2670965 = 250403) (by norm_num)
theorem B2376053 : Blo 1052612 2376053 := bbase (se 5 (by rfl) ⟨111377, by rfl⟩ : syracuseStep 2376053 = 222755) (by norm_num)
theorem B1687997 : Blo 1052612 1687997 := bbase (se 3 (by rfl) ⟨316499, by rfl⟩ : syracuseStep 1687997 = 632999) (by norm_num)
theorem B2376125 : Blo 1052612 2376125 := bbase (se 3 (by rfl) ⟨445523, by rfl⟩ : syracuseStep 2376125 = 891047) (by norm_num)
theorem B3555845 : Blo 1052612 3555845 := bbase (se 4 (by rfl) ⟨333360, by rfl⟩ : syracuseStep 3555845 = 666721) (by norm_num)
theorem B2376197 : Blo 1052612 2376197 := bbase (se 4 (by rfl) ⟨222768, by rfl⟩ : syracuseStep 2376197 = 445537) (by norm_num)
theorem B2671157 : Blo 1052612 2671157 := bbase (se 5 (by rfl) ⟨125210, by rfl⟩ : syracuseStep 2671157 = 250421) (by norm_num)
theorem B1688125 : Blo 1052612 1688125 := bbase (se 3 (by rfl) ⟨316523, by rfl⟩ : syracuseStep 1688125 = 633047) (by norm_num)
theorem B2376269 : Blo 1052612 2376269 := bbase (se 3 (by rfl) ⟨445550, by rfl⟩ : syracuseStep 2376269 = 891101) (by norm_num)
theorem B2605709 : Blo 1052612 2605709 := bbase (se 3 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 2605709 = 977141) (by norm_num)
theorem B2376341 : Blo 1052612 2376341 := bbase (se 6 (by rfl) ⟨55695, by rfl⟩ : syracuseStep 2376341 = 111391) (by norm_num)
theorem B2376413 : Blo 1052612 2376413 := bbase (se 3 (by rfl) ⟨445577, by rfl⟩ : syracuseStep 2376413 = 891155) (by norm_num)
theorem B2376485 : Blo 1052612 2376485 := bbase (se 4 (by rfl) ⟨222795, by rfl⟩ : syracuseStep 2376485 = 445591) (by norm_num)
theorem B2409293 : Blo 1052612 2409293 := bbase (se 3 (by rfl) ⟨451742, by rfl⟩ : syracuseStep 2409293 = 903485) (by norm_num)
theorem B2376557 : Blo 1052612 2376557 := bbase (se 3 (by rfl) ⟨445604, by rfl⟩ : syracuseStep 2376557 = 891209) (by norm_num)
theorem B2671501 : Blo 1052612 2671501 := bbase (se 3 (by rfl) ⟨500906, by rfl⟩ : syracuseStep 2671501 = 1001813) (by norm_num)
theorem B3556277 : Blo 1052612 3556277 := bbase (se 5 (by rfl) ⟨166700, by rfl⟩ : syracuseStep 3556277 = 333401) (by norm_num)
theorem B2376629 : Blo 1052612 2376629 := bbase (se 5 (by rfl) ⟨111404, by rfl⟩ : syracuseStep 2376629 = 222809) (by norm_num)
theorem B27018197 : Blo 1052612 27018197 := bbase (se 7 (by rfl) ⟨316619, by rfl⟩ : syracuseStep 27018197 = 633239) (by norm_num)
theorem B2671613 : Blo 1052612 2671613 := bbase (se 3 (by rfl) ⟨500927, by rfl⟩ : syracuseStep 2671613 = 1001855) (by norm_num)
theorem B2376701 : Blo 1052612 2376701 := bbase (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) (by norm_num)
theorem B2376773 : Blo 1052612 2376773 := bbase (se 4 (by rfl) ⟨222822, by rfl⟩ : syracuseStep 2376773 = 445645) (by norm_num)
theorem B2376845 : Blo 1052612 2376845 := bbase (se 3 (by rfl) ⟨445658, by rfl⟩ : syracuseStep 2376845 = 891317) (by norm_num)
theorem B8996021 : Blo 1052612 8996021 := bbase (se 5 (by rfl) ⟨421688, by rfl⟩ : syracuseStep 8996021 = 843377) (by norm_num)
theorem B2671805 : Blo 1052612 2671805 := bbase (se 3 (by rfl) ⟨500963, by rfl⟩ : syracuseStep 2671805 = 1001927) (by norm_num)
theorem B2376917 : Blo 1052612 2376917 := bbase (se 7 (by rfl) ⟨27854, by rfl⟩ : syracuseStep 2376917 = 55709) (by norm_num)
theorem B2376989 : Blo 1052612 2376989 := bbase (se 3 (by rfl) ⟨445685, by rfl⟩ : syracuseStep 2376989 = 891371) (by norm_num)
theorem B2409797 : Blo 1052612 2409797 := bbase (se 4 (by rfl) ⟨225918, by rfl⟩ : syracuseStep 2409797 = 451837) (by norm_num)
theorem B3556709 : Blo 1052612 3556709 := bbase (se 4 (by rfl) ⟨333441, by rfl⟩ : syracuseStep 3556709 = 666883) (by norm_num)
theorem B2377061 : Blo 1052612 2377061 := bbase (se 4 (by rfl) ⟨222849, by rfl⟩ : syracuseStep 2377061 = 445699) (by norm_num)
theorem B4506997 : Blo 1052612 4506997 := bbase (se 5 (by rfl) ⟨211265, by rfl⟩ : syracuseStep 4506997 = 422531) (by norm_num)
theorem B2377133 : Blo 1052612 2377133 := bbase (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) (by norm_num)
theorem B2377205 : Blo 1052612 2377205 := bbase (se 5 (by rfl) ⟨111431, by rfl⟩ : syracuseStep 2377205 = 222863) (by norm_num)
theorem B2672149 : Blo 1052612 2672149 := bbase (se 6 (by rfl) ⟨62628, by rfl⟩ : syracuseStep 2672149 = 125257) (by norm_num)
theorem B1427005 : Blo 1052612 1427005 := bbase (se 3 (by rfl) ⟨267563, by rfl⟩ : syracuseStep 1427005 = 535127) (by norm_num)
theorem B2377277 : Blo 1052612 2377277 := bbase (se 3 (by rfl) ⟨445739, by rfl⟩ : syracuseStep 2377277 = 891479) (by norm_num)
theorem B2737781 : Blo 1052612 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B2672261 : Blo 1052612 2672261 := bbase (se 4 (by rfl) ⟨250524, by rfl⟩ : syracuseStep 2672261 = 501049) (by norm_num)
theorem B2377349 : Blo 1052612 2377349 := bbase (se 4 (by rfl) ⟨222876, by rfl⟩ : syracuseStep 2377349 = 445753) (by norm_num)
theorem B3557141 : Blo 1052612 3557141 := bbase (se 6 (by rfl) ⟨83370, by rfl⟩ : syracuseStep 3557141 = 166741) (by norm_num)
theorem B2672453 : Blo 1052612 2672453 := bbase (se 4 (by rfl) ⟨250542, by rfl⟩ : syracuseStep 2672453 = 501085) (by norm_num)
theorem B8013653 : Blo 1052612 8013653 := bbase (se 9 (by rfl) ⟨23477, by rfl⟩ : syracuseStep 8013653 = 46955) (by norm_num)
theorem B1689509 : Blo 1052612 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B2672797 : Blo 1052612 2672797 := bbase (se 3 (by rfl) ⟨501149, by rfl⟩ : syracuseStep 2672797 = 1002299) (by norm_num)
theorem B3557573 : Blo 1052612 3557573 := bbase (se 4 (by rfl) ⟨333522, by rfl⟩ : syracuseStep 3557573 = 667045) (by norm_num)
theorem B2672909 : Blo 1052612 2672909 := bbase (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) (by norm_num)
theorem B6408629 : Blo 1052612 6408629 := bbase (se 5 (by rfl) ⟨300404, by rfl⟩ : syracuseStep 6408629 = 600809) (by norm_num)
theorem B2673101 : Blo 1052612 2673101 := bbase (se 3 (by rfl) ⟨501206, by rfl⟩ : syracuseStep 2673101 = 1002413) (by norm_num)
theorem B3558005 : Blo 1052612 3558005 := bbase (se 5 (by rfl) ⟨166781, by rfl⟩ : syracuseStep 3558005 = 333563) (by norm_num)
theorem B1067789 : Blo 1052612 1067789 := bbase (se 3 (by rfl) ⟨200210, by rfl⟩ : syracuseStep 1067789 = 400421) (by norm_num)
theorem B2673445 : Blo 1052612 2673445 := bbase (se 4 (by rfl) ⟨250635, by rfl⟩ : syracuseStep 2673445 = 501271) (by norm_num)
theorem B3001157 : Blo 1052612 3001157 := bbase (se 4 (by rfl) ⟨281358, by rfl⟩ : syracuseStep 3001157 = 562717) (by norm_num)
theorem B1690445 : Blo 1052612 1690445 := bbase (se 3 (by rfl) ⟨316958, by rfl⟩ : syracuseStep 1690445 = 633917) (by norm_num)
theorem B2673557 : Blo 1052612 2673557 := bbase (se 6 (by rfl) ⟨62661, by rfl⟩ : syracuseStep 2673557 = 125323) (by norm_num)
theorem B5065685 : Blo 1052612 5065685 := bbase (se 7 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 5065685 = 118727) (by norm_num)
theorem B3558437 : Blo 1052612 3558437 := bbase (se 4 (by rfl) ⟨333603, by rfl⟩ : syracuseStep 3558437 = 667207) (by norm_num)
theorem B2673749 : Blo 1052612 2673749 := bbase (se 8 (by rfl) ⟨15666, by rfl⟩ : syracuseStep 2673749 = 31333) (by norm_num)
theorem B2674093 : Blo 1052612 2674093 := bbase (se 3 (by rfl) ⟨501392, by rfl⟩ : syracuseStep 2674093 = 1002785) (by norm_num)
theorem B3558869 : Blo 1052612 3558869 := bbase (se 7 (by rfl) ⟨41705, by rfl⟩ : syracuseStep 3558869 = 83411) (by norm_num)
theorem B1691093 : Blo 1052612 1691093 := bbase (se 7 (by rfl) ⟨19817, by rfl⟩ : syracuseStep 1691093 = 39635) (by norm_num)
theorem B2674205 : Blo 1052612 2674205 := bbase (se 3 (by rfl) ⟨501413, by rfl⟩ : syracuseStep 2674205 = 1002827) (by norm_num)
theorem B2248229 : Blo 1052612 2248229 := bbase (se 4 (by rfl) ⟨210771, by rfl⟩ : syracuseStep 2248229 = 421543) (by norm_num)
theorem B1068697 : Blo 1052612 1068697 := bbase (se 2 (by rfl) ⟨400761, by rfl⟩ : syracuseStep 1068697 = 801523) (by norm_num)
theorem B2248373 : Blo 1052612 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B8113877 : Blo 1052612 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B2674397 : Blo 1052612 2674397 := bbase (se 3 (by rfl) ⟨501449, by rfl⟩ : syracuseStep 2674397 = 1002899) (by norm_num)
theorem B3559301 : Blo 1052612 3559301 := bbase (se 4 (by rfl) ⟨333684, by rfl⟩ : syracuseStep 3559301 = 667369) (by norm_num)
theorem B3002341 : Blo 1052612 3002341 := bbase (se 4 (by rfl) ⟨281469, by rfl⟩ : syracuseStep 3002341 = 562939) (by norm_num)
theorem B3002501 : Blo 1052612 3002501 := bbase (se 4 (by rfl) ⟨281484, by rfl⟩ : syracuseStep 3002501 = 562969) (by norm_num)
theorem B1265825 : Blo 1052612 1265825 := bbase (se 2 (by rfl) ⟨474684, by rfl⟩ : syracuseStep 1265825 = 949369) (by norm_num)
theorem B5067029 : Blo 1052612 5067029 := bbase (se 6 (by rfl) ⟨118758, by rfl⟩ : syracuseStep 5067029 = 237517) (by norm_num)
theorem B4509989 : Blo 1052612 4509989 := bbase (se 4 (by rfl) ⟨422811, by rfl⟩ : syracuseStep 4509989 = 845623) (by norm_num)
theorem B3559733 : Blo 1052612 3559733 := bbase (se 5 (by rfl) ⟨166862, by rfl⟩ : syracuseStep 3559733 = 333725) (by norm_num)
theorem B3002741 : Blo 1052612 3002741 := bbase (se 5 (by rfl) ⟨140753, by rfl⟩ : syracuseStep 3002741 = 281507) (by norm_num)
theorem B2249117 : Blo 1052612 2249117 := bbase (se 3 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 2249117 = 843419) (by norm_num)
theorem B1692085 : Blo 1052612 1692085 := bbase (se 5 (by rfl) ⟨79316, by rfl⟩ : syracuseStep 1692085 = 158633) (by norm_num)
theorem B1266133 : Blo 1052612 1266133 := bbase (se 7 (by rfl) ⟨14837, by rfl⟩ : syracuseStep 1266133 = 29675) (by norm_num)
theorem B1069597 : Blo 1052612 1069597 := bbase (se 3 (by rfl) ⟨200549, by rfl⟩ : syracuseStep 1069597 = 401099) (by norm_num)
theorem B1266229 : Blo 1052612 1266229 := bbase (se 5 (by rfl) ⟨59354, by rfl⟩ : syracuseStep 1266229 = 118709) (by norm_num)
theorem B3002933 : Blo 1052612 3002933 := bbase (se 5 (by rfl) ⟨140762, by rfl⟩ : syracuseStep 3002933 = 281525) (by norm_num)
theorem B2708117 : Blo 1052612 2708117 := bbase (se 6 (by rfl) ⟨63471, by rfl⟩ : syracuseStep 2708117 = 126943) (by norm_num)
theorem B5329637 : Blo 1052612 5329637 := bbase (se 4 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 5329637 = 999307) (by norm_num)
theorem B3560165 : Blo 1052612 3560165 := bbase (se 4 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 3560165 = 667531) (by norm_num)
theorem B1266517 : Blo 1052612 1266517 := bbase (se 9 (by rfl) ⟨3710, by rfl⟩ : syracuseStep 1266517 = 7421) (by norm_num)
theorem B1332217 : Blo 1052612 1332217 := bbase (se 2 (by rfl) ⟨499581, by rfl⟩ : syracuseStep 1332217 = 999163) (by norm_num)
theorem B1266709 : Blo 1052612 1266709 := bbase (se 6 (by rfl) ⟨29688, by rfl⟩ : syracuseStep 1266709 = 59377) (by norm_num)
theorem B1070177 : Blo 1052612 1070177 := bbase (se 2 (by rfl) ⟨401316, by rfl⟩ : syracuseStep 1070177 = 802633) (by norm_num)
theorem B2249869 : Blo 1052612 2249869 := bbase (se 3 (by rfl) ⟨421850, by rfl⟩ : syracuseStep 2249869 = 843701) (by norm_num)
theorem B3560597 : Blo 1052612 3560597 := bbase (se 6 (by rfl) ⟨83451, by rfl⟩ : syracuseStep 3560597 = 166903) (by norm_num)
theorem B1332389 : Blo 1052612 1332389 := bbase (se 4 (by rfl) ⟨124911, by rfl⟩ : syracuseStep 1332389 = 249823) (by norm_num)
theorem B1332445 : Blo 1052612 1332445 := bbase (se 3 (by rfl) ⟨249833, by rfl⟩ : syracuseStep 1332445 = 499667) (by norm_num)
theorem B4510997 : Blo 1052612 4510997 := bbase (se 6 (by rfl) ⟨105726, by rfl⟩ : syracuseStep 4510997 = 211453) (by norm_num)
theorem B2250013 : Blo 1052612 2250013 := bbase (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) (by norm_num)
theorem B1332541 : Blo 1052612 1332541 := bbase (se 3 (by rfl) ⟨249851, by rfl⟩ : syracuseStep 1332541 = 499703) (by norm_num)
theorem B2315621 : Blo 1052612 2315621 := bbase (se 4 (by rfl) ⟨217089, by rfl⟩ : syracuseStep 2315621 = 434179) (by norm_num)
theorem B1332713 : Blo 1052612 1332713 := bbase (se 2 (by rfl) ⟨499767, by rfl⟩ : syracuseStep 1332713 = 999535) (by norm_num)
theorem B3003925 : Blo 1052612 3003925 := bbase (se 6 (by rfl) ⟨70404, by rfl⟩ : syracuseStep 3003925 = 140809) (by norm_num)
theorem B1332769 : Blo 1052612 1332769 := bbase (se 2 (by rfl) ⟨499788, by rfl⟩ : syracuseStep 1332769 = 999577) (by norm_num)
theorem B3561029 : Blo 1052612 3561029 := bbase (se 4 (by rfl) ⟨333846, by rfl⟩ : syracuseStep 3561029 = 667693) (by norm_num)
theorem B1332865 : Blo 1052612 1332865 := bbase (se 2 (by rfl) ⟨499824, by rfl⟩ : syracuseStep 1332865 = 999649) (by norm_num)
theorem B2250389 : Blo 1052612 2250389 := bbase (se 6 (by rfl) ⟨52743, by rfl⟩ : syracuseStep 2250389 = 105487) (by norm_num)
theorem B2709245 : Blo 1052612 2709245 := bbase (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) (by norm_num)
theorem B1333037 : Blo 1052612 1333037 := bbase (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) (by norm_num)
theorem B1333093 : Blo 1052612 1333093 := bbase (se 4 (by rfl) ⟨124977, by rfl⟩ : syracuseStep 1333093 = 249955) (by norm_num)
theorem B1267589 : Blo 1052612 1267589 := bbase (se 4 (by rfl) ⟨118836, by rfl⟩ : syracuseStep 1267589 = 237673) (by norm_num)
theorem B1333189 : Blo 1052612 1333189 := bbase (se 4 (by rfl) ⟨124986, by rfl⟩ : syracuseStep 1333189 = 249973) (by norm_num)
theorem B2709469 : Blo 1052612 2709469 := bbase (se 3 (by rfl) ⟨508025, by rfl⟩ : syracuseStep 2709469 = 1016051) (by norm_num)
theorem B5330933 : Blo 1052612 5330933 := bbase (se 5 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 5330933 = 499775) (by norm_num)
theorem B3561461 : Blo 1052612 3561461 := bbase (se 5 (by rfl) ⟨166943, by rfl⟩ : syracuseStep 3561461 = 333887) (by norm_num)
theorem B2250757 : Blo 1052612 2250757 := bbase (se 4 (by rfl) ⟨211008, by rfl⟩ : syracuseStep 2250757 = 422017) (by norm_num)
theorem B1333361 : Blo 1052612 1333361 := bbase (se 2 (by rfl) ⟨500010, by rfl⟩ : syracuseStep 1333361 = 1000021) (by norm_num)
theorem B1333417 : Blo 1052612 1333417 := bbase (se 2 (by rfl) ⟨500031, by rfl⟩ : syracuseStep 1333417 = 1000063) (by norm_num)
theorem B2775221 : Blo 1052612 2775221 := bbase (se 5 (by rfl) ⟨130088, by rfl⟩ : syracuseStep 2775221 = 260177) (by norm_num)
theorem B2283709 : Blo 1052612 2283709 := bbase (se 3 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 2283709 = 856391) (by norm_num)
theorem B1333513 : Blo 1052612 1333513 := bbase (se 2 (by rfl) ⟨500067, by rfl⟩ : syracuseStep 1333513 = 1000135) (by norm_num)
theorem B1268093 : Blo 1052612 1268093 := bbase (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) (by norm_num)
theorem B3561893 : Blo 1052612 3561893 := bbase (se 4 (by rfl) ⟨333927, by rfl⟩ : syracuseStep 3561893 = 667855) (by norm_num)
theorem B1268141 : Blo 1052612 1268141 := bbase (se 3 (by rfl) ⟨237776, by rfl⟩ : syracuseStep 1268141 = 475553) (by norm_num)
theorem B1333685 : Blo 1052612 1333685 := bbase (se 5 (by rfl) ⟨62516, by rfl⟩ : syracuseStep 1333685 = 125033) (by norm_num)
theorem B1333741 : Blo 1052612 1333741 := bbase (se 3 (by rfl) ⟨250076, by rfl⟩ : syracuseStep 1333741 = 500153) (by norm_num)
theorem B3201589 : Blo 1052612 3201589 := bbase (se 5 (by rfl) ⟨150074, by rfl⟩ : syracuseStep 3201589 = 300149) (by norm_num)
theorem B1333837 : Blo 1052612 1333837 := bbase (se 3 (by rfl) ⟨250094, by rfl⟩ : syracuseStep 1333837 = 500189) (by norm_num)
theorem B3005029 : Blo 1052612 3005029 := bbase (se 4 (by rfl) ⟨281721, by rfl⟩ : syracuseStep 3005029 = 563443) (by norm_num)
theorem B1268401 : Blo 1052612 1268401 := bbase (se 2 (by rfl) ⟨475650, by rfl⟩ : syracuseStep 1268401 = 951301) (by norm_num)
theorem B1334009 : Blo 1052612 1334009 := bbase (se 2 (by rfl) ⟨500253, by rfl⟩ : syracuseStep 1334009 = 1000507) (by norm_num)
theorem B1334065 : Blo 1052612 1334065 := bbase (se 2 (by rfl) ⟨500274, by rfl⟩ : syracuseStep 1334065 = 1000549) (by norm_num)
theorem B3562325 : Blo 1052612 3562325 := bbase (se 9 (by rfl) ⟨10436, by rfl⟩ : syracuseStep 3562325 = 20873) (by norm_num)
theorem B1334161 : Blo 1052612 1334161 := bbase (se 2 (by rfl) ⟨500310, by rfl⟩ : syracuseStep 1334161 = 1000621) (by norm_num)
theorem B13523861 : Blo 1052612 13523861 := bbase (se 6 (by rfl) ⟨316965, by rfl⟩ : syracuseStep 13523861 = 633931) (by norm_num)
theorem B4283317 : Blo 1052612 4283317 := bbase (se 5 (by rfl) ⟨200780, by rfl⟩ : syracuseStep 4283317 = 401561) (by norm_num)
theorem B1268665 : Blo 1052612 1268665 := bbase (se 2 (by rfl) ⟨475749, by rfl⟩ : syracuseStep 1268665 = 951499) (by norm_num)
theorem B4512773 : Blo 1052612 4512773 := bbase (se 4 (by rfl) ⟨423072, by rfl⟩ : syracuseStep 4512773 = 846145) (by norm_num)
theorem B1268785 : Blo 1052612 1268785 := bbase (se 2 (by rfl) ⟨475794, by rfl⟩ : syracuseStep 1268785 = 951589) (by norm_num)
theorem B1334333 : Blo 1052612 1334333 := bbase (se 3 (by rfl) ⟨250187, by rfl⟩ : syracuseStep 1334333 = 500375) (by norm_num)
theorem B1334389 : Blo 1052612 1334389 := bbase (se 5 (by rfl) ⟨62549, by rfl⟩ : syracuseStep 1334389 = 125099) (by norm_num)
theorem B1334485 : Blo 1052612 1334485 := bbase (se 7 (by rfl) ⟨15638, by rfl⟩ : syracuseStep 1334485 = 31277) (by norm_num)
theorem B5332229 : Blo 1052612 5332229 := bbase (se 4 (by rfl) ⟨499896, by rfl⟩ : syracuseStep 5332229 = 999793) (by norm_num)
theorem B3562757 : Blo 1052612 3562757 := bbase (se 4 (by rfl) ⟨334008, by rfl⟩ : syracuseStep 3562757 = 668017) (by norm_num)
theorem B5135653 : Blo 1052612 5135653 := bbase (se 4 (by rfl) ⟨481467, by rfl⟩ : syracuseStep 5135653 = 962935) (by norm_num)
theorem B1334657 : Blo 1052612 1334657 := bbase (se 2 (by rfl) ⟨500496, by rfl⟩ : syracuseStep 1334657 = 1000993) (by norm_num)
theorem B1334713 : Blo 1052612 1334713 := bbase (se 2 (by rfl) ⟨500517, by rfl⟩ : syracuseStep 1334713 = 1001035) (by norm_num)
theorem B2252261 : Blo 1052612 2252261 := bbase (se 4 (by rfl) ⟨211149, by rfl⟩ : syracuseStep 2252261 = 422299) (by norm_num)
theorem B1334809 : Blo 1052612 1334809 := bbase (se 2 (by rfl) ⟨500553, by rfl⟩ : syracuseStep 1334809 = 1001107) (by norm_num)
theorem B2252405 : Blo 1052612 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B1203881 : Blo 1052612 1203881 := bbase (se 2 (by rfl) ⟨451455, by rfl⟩ : syracuseStep 1203881 = 902911) (by norm_num)
theorem B3563189 : Blo 1052612 3563189 := bbase (se 5 (by rfl) ⟨167024, by rfl⟩ : syracuseStep 3563189 = 334049) (by norm_num)
theorem B1334981 : Blo 1052612 1334981 := bbase (se 4 (by rfl) ⟨125154, by rfl⟩ : syracuseStep 1334981 = 250309) (by norm_num)
theorem B1335037 : Blo 1052612 1335037 := bbase (se 3 (by rfl) ⟨250319, by rfl⟩ : syracuseStep 1335037 = 500639) (by norm_num)
theorem B1335133 : Blo 1052612 1335133 := bbase (se 3 (by rfl) ⟨250337, by rfl⟩ : syracuseStep 1335133 = 500675) (by norm_num)
theorem B5070757 : Blo 1052612 5070757 := bbase (se 4 (by rfl) ⟨475383, by rfl⟩ : syracuseStep 5070757 = 950767) (by norm_num)
theorem B2252765 : Blo 1052612 2252765 := bbase (se 3 (by rfl) ⟨422393, by rfl⟩ : syracuseStep 2252765 = 844787) (by norm_num)
theorem B1335305 : Blo 1052612 1335305 := bbase (se 2 (by rfl) ⟨500739, by rfl⟩ : syracuseStep 1335305 = 1001479) (by norm_num)
theorem B1925141 : Blo 1052612 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B4055093 : Blo 1052612 4055093 := bbase (se 5 (by rfl) ⟨190082, by rfl⟩ : syracuseStep 4055093 = 380165) (by norm_num)
theorem B1335361 : Blo 1052612 1335361 := bbase (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) (by norm_num)
theorem B3006533 : Blo 1052612 3006533 := bbase (se 4 (by rfl) ⟨281862, by rfl⟩ : syracuseStep 3006533 = 563725) (by norm_num)
theorem B3563621 : Blo 1052612 3563621 := bbase (se 4 (by rfl) ⟨334089, by rfl⟩ : syracuseStep 3563621 = 668179) (by norm_num)
theorem B1335457 : Blo 1052612 1335457 := bbase (se 2 (by rfl) ⟨500796, by rfl⟩ : syracuseStep 1335457 = 1001593) (by norm_num)
theorem B1204465 : Blo 1052612 1204465 := bbase (se 2 (by rfl) ⟨451674, by rfl⟩ : syracuseStep 1204465 = 903349) (by norm_num)
theorem B1335629 : Blo 1052612 1335629 := bbase (se 3 (by rfl) ⟨250430, by rfl⟩ : syracuseStep 1335629 = 500861) (by norm_num)
theorem B1499485 : Blo 1052612 1499485 := bbase (se 3 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 1499485 = 562307) (by norm_num)
theorem B1335685 : Blo 1052612 1335685 := bbase (se 4 (by rfl) ⟨125220, by rfl⟩ : syracuseStep 1335685 = 250441) (by norm_num)
theorem B3203525 : Blo 1052612 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B1335781 : Blo 1052612 1335781 := bbase (se 4 (by rfl) ⟨125229, by rfl⟩ : syracuseStep 1335781 = 250459) (by norm_num)
theorem B5333525 : Blo 1052612 5333525 := bbase (se 6 (by rfl) ⟨125004, by rfl⟩ : syracuseStep 5333525 = 250009) (by norm_num)
theorem B3564053 : Blo 1052612 3564053 := bbase (se 6 (by rfl) ⟨83532, by rfl⟩ : syracuseStep 3564053 = 167065) (by norm_num)
theorem B1335953 : Blo 1052612 1335953 := bbase (se 2 (by rfl) ⟨500982, by rfl⟩ : syracuseStep 1335953 = 1001965) (by norm_num)
theorem B1336009 : Blo 1052612 1336009 := bbase (se 2 (by rfl) ⟨501003, by rfl⟩ : syracuseStep 1336009 = 1002007) (by norm_num)
theorem B2286341 : Blo 1052612 2286341 := bbase (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) (by norm_num)
theorem B1336105 : Blo 1052612 1336105 := bbase (se 2 (by rfl) ⟨501039, by rfl⟩ : syracuseStep 1336105 = 1002079) (by norm_num)
theorem B2253653 : Blo 1052612 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B1500077 : Blo 1052612 1500077 := bbase (se 3 (by rfl) ⟨281264, by rfl⟩ : syracuseStep 1500077 = 562529) (by norm_num)
theorem B3564485 : Blo 1052612 3564485 := bbase (se 4 (by rfl) ⟨334170, by rfl⟩ : syracuseStep 3564485 = 668341) (by norm_num)
theorem B1336277 : Blo 1052612 1336277 := bbase (se 7 (by rfl) ⟨15659, by rfl⟩ : syracuseStep 1336277 = 31319) (by norm_num)
theorem B1500157 : Blo 1052612 1500157 := bbase (se 3 (by rfl) ⟨281279, by rfl⟩ : syracuseStep 1500157 = 562559) (by norm_num)
theorem B1336333 : Blo 1052612 1336333 := bbase (se 3 (by rfl) ⟨250562, by rfl⟩ : syracuseStep 1336333 = 501125) (by norm_num)
theorem B1139729 : Blo 1052612 1139729 := bbase (se 2 (by rfl) ⟨427398, by rfl⟩ : syracuseStep 1139729 = 854797) (by norm_num)
theorem B6939701 : Blo 1052612 6939701 := bbase (se 5 (by rfl) ⟨325298, by rfl⟩ : syracuseStep 6939701 = 650597) (by norm_num)
theorem B2253901 : Blo 1052612 2253901 := bbase (se 3 (by rfl) ⟨422606, by rfl⟩ : syracuseStep 2253901 = 845213) (by norm_num)
theorem B1336429 : Blo 1052612 1336429 := bbase (se 3 (by rfl) ⟨250580, by rfl⟩ : syracuseStep 1336429 = 501161) (by norm_num)
theorem B1500277 : Blo 1052612 1500277 := bbase (se 5 (by rfl) ⟨70325, by rfl⟩ : syracuseStep 1500277 = 140651) (by norm_num)
theorem B1500373 : Blo 1052612 1500373 := bbase (se 7 (by rfl) ⟨17582, by rfl⟩ : syracuseStep 1500373 = 35165) (by norm_num)
theorem B1336601 : Blo 1052612 1336601 := bbase (se 2 (by rfl) ⟨501225, by rfl⟩ : syracuseStep 1336601 = 1002451) (by norm_num)
theorem B1336657 : Blo 1052612 1336657 := bbase (se 2 (by rfl) ⟨501246, by rfl⟩ : syracuseStep 1336657 = 1002493) (by norm_num)
theorem B38495573 : Blo 1052612 38495573 := bbase (se 12 (by rfl) ⟨14097, by rfl⟩ : syracuseStep 38495573 = 28195) (by norm_num)
theorem B3564917 : Blo 1052612 3564917 := bbase (se 5 (by rfl) ⟨167105, by rfl⟩ : syracuseStep 3564917 = 334211) (by norm_num)
theorem B1336753 : Blo 1052612 1336753 := bbase (se 2 (by rfl) ⟨501282, by rfl⟩ : syracuseStep 1336753 = 1002565) (by norm_num)
theorem B8021429 : Blo 1052612 8021429 := bbase (se 5 (by rfl) ⟨376004, by rfl⟩ : syracuseStep 8021429 = 752009) (by norm_num)
theorem B2254405 : Blo 1052612 2254405 := bbase (se 4 (by rfl) ⟨211350, by rfl⟩ : syracuseStep 2254405 = 422701) (by norm_num)
theorem B1336925 : Blo 1052612 1336925 := bbase (se 3 (by rfl) ⟨250673, by rfl⟩ : syracuseStep 1336925 = 501347) (by norm_num)
theorem B3008117 : Blo 1052612 3008117 := bbase (se 5 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 3008117 = 282011) (by norm_num)
theorem B1336981 : Blo 1052612 1336981 := bbase (se 6 (by rfl) ⟨31335, by rfl⟩ : syracuseStep 1336981 = 62671) (by norm_num)
theorem B1500869 : Blo 1052612 1500869 := bbase (se 4 (by rfl) ⟨140706, by rfl⟩ : syracuseStep 1500869 = 281413) (by norm_num)
theorem B1337077 : Blo 1052612 1337077 := bbase (se 5 (by rfl) ⟨62675, by rfl⟩ : syracuseStep 1337077 = 125351) (by norm_num)
theorem B5334821 : Blo 1052612 5334821 := bbase (se 4 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 5334821 = 1000279) (by norm_num)
theorem B3565349 : Blo 1052612 3565349 := bbase (se 4 (by rfl) ⟨334251, by rfl⟩ : syracuseStep 3565349 = 668503) (by norm_num)
theorem B10282805 : Blo 1052612 10282805 := bbase (se 5 (by rfl) ⟨482006, by rfl⟩ : syracuseStep 10282805 = 964013) (by norm_num)
theorem B1337249 : Blo 1052612 1337249 := bbase (se 2 (by rfl) ⟨501468, by rfl⟩ : syracuseStep 1337249 = 1002937) (by norm_num)
theorem B4810853 : Blo 1052612 4810853 := bbase (se 4 (by rfl) ⟨451017, by rfl⟩ : syracuseStep 4810853 = 902035) (by norm_num)
theorem B3565781 : Blo 1052612 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B1501421 : Blo 1052612 1501421 := bbase (se 3 (by rfl) ⟨281516, by rfl⟩ : syracuseStep 1501421 = 563033) (by norm_num)
theorem B3008789 : Blo 1052612 3008789 := bbase (se 6 (by rfl) ⟨70518, by rfl⟩ : syracuseStep 3008789 = 141037) (by norm_num)
theorem B2255293 : Blo 1052612 2255293 := bbase (se 3 (by rfl) ⟨422867, by rfl⟩ : syracuseStep 2255293 = 845735) (by norm_num)
theorem B2255789 : Blo 1052612 2255789 := bbase (se 3 (by rfl) ⟨422960, by rfl⟩ : syracuseStep 2255789 = 845921) (by norm_num)
theorem B2845621 : Blo 1052612 2845621 := bbase (se 5 (by rfl) ⟨133388, by rfl⟩ : syracuseStep 2845621 = 266777) (by norm_num)
theorem B1502173 : Blo 1052612 1502173 := bbase (se 3 (by rfl) ⟨281657, by rfl⟩ : syracuseStep 1502173 = 563315) (by norm_num)
theorem B3435509 : Blo 1052612 3435509 := bbase (se 5 (by rfl) ⟨161039, by rfl⟩ : syracuseStep 3435509 = 322079) (by norm_num)
theorem B5336117 : Blo 1052612 5336117 := bbase (se 5 (by rfl) ⟨250130, by rfl⟩ : syracuseStep 5336117 = 500261) (by norm_num)
theorem B1174637 : Blo 1052612 1174637 := bbase (se 3 (by rfl) ⟨220244, by rfl⟩ : syracuseStep 1174637 = 440489) (by norm_num)
theorem B1141933 : Blo 1052612 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B6745301 : Blo 1052612 6745301 := bbase (se 7 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 6745301 = 158093) (by norm_num)
theorem B3042613 : Blo 1052612 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B5696885 : Blo 1052612 5696885 := bbase (se 5 (by rfl) ⟨267041, by rfl⟩ : syracuseStep 5696885 = 534083) (by norm_num)
theorem B4812149 : Blo 1052612 4812149 := bbase (se 5 (by rfl) ⟨225569, by rfl⟩ : syracuseStep 4812149 = 451139) (by norm_num)
theorem B2026901 : Blo 1052612 2026901 := bbase (se 6 (by rfl) ⟨47505, by rfl⟩ : syracuseStep 2026901 = 95011) (by norm_num)
theorem B2846117 : Blo 1052612 2846117 := bbase (se 4 (by rfl) ⟨266823, by rfl⟩ : syracuseStep 2846117 = 533647) (by norm_num)
theorem B1371593 : Blo 1052612 1371593 := bbase (se 2 (by rfl) ⟨514347, by rfl⟩ : syracuseStep 1371593 = 1028695) (by norm_num)
theorem B7302869 : Blo 1052612 7302869 := bbase (se 7 (by rfl) ⟨85580, by rfl⟩ : syracuseStep 7302869 = 171161) (by norm_num)
theorem B1502965 : Blo 1052612 1502965 := bbase (se 5 (by rfl) ⟨70451, by rfl⟩ : syracuseStep 1502965 = 140903) (by norm_num)
theorem B5074757 : Blo 1052612 5074757 := bbase (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) (by norm_num)
theorem B2846549 : Blo 1052612 2846549 := bbase (se 9 (by rfl) ⟨8339, by rfl⟩ : syracuseStep 2846549 = 16679) (by norm_num)
theorem B1601525 : Blo 1052612 1601525 := bbase (se 5 (by rfl) ⟨75071, by rfl⟩ : syracuseStep 1601525 = 150143) (by norm_num)
theorem B1503301 : Blo 1052612 1503301 := bbase (se 4 (by rfl) ⟨140934, by rfl⟩ : syracuseStep 1503301 = 281869) (by norm_num)
theorem B1503517 : Blo 1052612 1503517 := bbase (se 3 (by rfl) ⟨281909, by rfl⟩ : syracuseStep 1503517 = 563819) (by norm_num)
theorem B5402933 : Blo 1052612 5402933 := bbase (se 5 (by rfl) ⟨253262, by rfl⟩ : syracuseStep 5402933 = 506525) (by norm_num)
theorem B5337413 : Blo 1052612 5337413 := bbase (se 4 (by rfl) ⟨500382, by rfl⟩ : syracuseStep 5337413 = 1000765) (by norm_num)
theorem B1897037 : Blo 1052612 1897037 := bbase (se 3 (by rfl) ⟨355694, by rfl⟩ : syracuseStep 1897037 = 711389) (by norm_num)
theorem B1503893 : Blo 1052612 1503893 := bbase (se 6 (by rfl) ⟨35247, by rfl⟩ : syracuseStep 1503893 = 70495) (by norm_num)
theorem B3797765 : Blo 1052612 3797765 := bbase (se 4 (by rfl) ⟨356040, by rfl⟩ : syracuseStep 3797765 = 712081) (by norm_num)
theorem B5075909 : Blo 1052612 5075909 := bbase (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) (by norm_num)
theorem B1602541 : Blo 1052612 1602541 := bbase (se 3 (by rfl) ⟨300476, by rfl⟩ : syracuseStep 1602541 = 600953) (by norm_num)
theorem B9008117 : Blo 1052612 9008117 := bbase (se 5 (by rfl) ⟨422255, by rfl⟩ : syracuseStep 9008117 = 844511) (by norm_num)
theorem B3798197 : Blo 1052612 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B1897757 : Blo 1052612 1897757 := bbase (se 3 (by rfl) ⟨355829, by rfl⟩ : syracuseStep 1897757 = 711659) (by norm_num)
theorem B5862709 : Blo 1052612 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B5338709 : Blo 1052612 5338709 := bbase (se 8 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 5338709 = 62563) (by norm_num)
theorem B5404325 : Blo 1052612 5404325 := bbase (se 4 (by rfl) ⟨506655, by rfl⟩ : syracuseStep 5404325 = 1013311) (by norm_num)
theorem B5076677 : Blo 1052612 5076677 := bbase (se 4 (by rfl) ⟨475938, by rfl⟩ : syracuseStep 5076677 = 951877) (by norm_num)
theorem B5699413 : Blo 1052612 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B9140309 : Blo 1052612 9140309 := bbase (se 8 (by rfl) ⟨53556, by rfl⟩ : syracuseStep 9140309 = 107113) (by norm_num)
theorem B2029733 : Blo 1052612 2029733 := bbase (se 4 (by rfl) ⟨190287, by rfl⟩ : syracuseStep 2029733 = 380575) (by norm_num)
theorem B10123829 : Blo 1052612 10123829 := bbase (se 5 (by rfl) ⟨474554, by rfl⟩ : syracuseStep 10123829 = 949109) (by norm_num)
theorem B5340005 : Blo 1052612 5340005 := bbase (se 4 (by rfl) ⟨500625, by rfl⟩ : syracuseStep 5340005 = 1001251) (by norm_num)
theorem B2030501 : Blo 1052612 2030501 := bbase (se 4 (by rfl) ⟨190359, by rfl⟩ : syracuseStep 2030501 = 380719) (by norm_num)
theorem B3374149 : Blo 1052612 3374149 := bbase (se 4 (by rfl) ⟨316326, by rfl⟩ : syracuseStep 3374149 = 632653) (by norm_num)
theorem B3603541 : Blo 1052612 3603541 := bbase (se 8 (by rfl) ⟨21114, by rfl⟩ : syracuseStep 3603541 = 42229) (by norm_num)
theorem B3996773 : Blo 1052612 3996773 := bbase (se 4 (by rfl) ⟨374697, by rfl⟩ : syracuseStep 3996773 = 749395) (by norm_num)
theorem B7601525 : Blo 1052612 7601525 := bbase (se 5 (by rfl) ⟨356321, by rfl⟩ : syracuseStep 7601525 = 712643) (by norm_num)
theorem B1998341 : Blo 1052612 1998341 := bbase (se 4 (by rfl) ⟨187344, by rfl⟩ : syracuseStep 1998341 = 374689) (by norm_num)
theorem B1900093 : Blo 1052612 1900093 := bbase (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) (by norm_num)
theorem B3604117 : Blo 1052612 3604117 := bbase (se 6 (by rfl) ⟨84471, by rfl⟩ : syracuseStep 3604117 = 168943) (by norm_num)
theorem B3800965 : Blo 1052612 3800965 := bbase (se 4 (by rfl) ⟨356340, by rfl⟩ : syracuseStep 3800965 = 712681) (by norm_num)
theorem B2031581 : Blo 1052612 2031581 := bbase (se 3 (by rfl) ⟨380921, by rfl⟩ : syracuseStep 2031581 = 761843) (by norm_num)
theorem B1900525 : Blo 1052612 1900525 := bbase (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) (by norm_num)
theorem B3997745 : Blo 1052612 3997745 := bstep (se 2 (by rfl) ⟨1499154, by rfl⟩ : syracuseStep 3997745 = 2998309) B2998309
theorem B6750449 : Blo 1052612 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B1605953 : Blo 1052612 1605953 := bstep (se 2 (by rfl) ⟨602232, by rfl⟩ : syracuseStep 1605953 = 1204465) B1204465
theorem B4063651 : Blo 1052612 4063651 := bstep (se 1 (by rfl) ⟨3047738, by rfl⟩ : syracuseStep 4063651 = 6095477) B6095477
theorem B3375533 : Blo 1052612 3375533 := bstep (se 3 (by rfl) ⟨632912, by rfl⟩ : syracuseStep 3375533 = 1265825) B1265825
theorem B1737139 : Blo 1052612 1737139 := bstep (se 1 (by rfl) ⟨1302854, by rfl⟩ : syracuseStep 1737139 = 2605709) B2605709
theorem B1999313 : Blo 1052612 1999313 := bstep (se 2 (by rfl) ⟨749742, by rfl⟩ : syracuseStep 1999313 = 1499485) B1499485
theorem B1606195 : Blo 1052612 1606195 := bstep (se 1 (by rfl) ⟨1204646, by rfl⟩ : syracuseStep 1606195 = 2409293) B2409293
theorem B5997347 : Blo 1052612 5997347 := bstep (se 1 (by rfl) ⟨4498010, by rfl⟩ : syracuseStep 5997347 = 8996021) B8996021
theorem B7996643 : Blo 1052612 7996643 := bstep (se 1 (by rfl) ⟨5997482, by rfl⟩ : syracuseStep 7996643 = 11994965) B11994965
theorem B5342435 : Blo 1052612 5342435 := bstep (se 1 (by rfl) ⟨4006826, by rfl⟩ : syracuseStep 5342435 = 8013653) B8013653
theorem B2000209 : Blo 1052612 2000209 := bstep (se 2 (by rfl) ⟨750078, by rfl⟩ : syracuseStep 2000209 = 1500157) B1500157
theorem B6423907 : Blo 1052612 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B5768653 : Blo 1052612 5768653 := bstep (se 3 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 5768653 = 2163245) B2163245
theorem B3999203 : Blo 1052612 3999203 := bstep (se 1 (by rfl) ⟨2999402, by rfl⟩ : syracuseStep 3999203 = 5998805) B5998805
theorem B2000369 : Blo 1052612 2000369 := bstep (se 2 (by rfl) ⟨750138, by rfl⟩ : syracuseStep 2000369 = 1500277) B1500277
theorem B3900977 : Blo 1052612 3900977 := bstep (se 2 (by rfl) ⟨1462866, by rfl⟩ : syracuseStep 3900977 = 2925733) B2925733
theorem B2000771 : Blo 1052612 2000771 := bstep (se 1 (by rfl) ⟨1500578, by rfl⟩ : syracuseStep 2000771 = 3001157) B3001157
theorem B3377123 : Blo 1052612 3377123 := bstep (se 1 (by rfl) ⟨2532842, by rfl⟩ : syracuseStep 3377123 = 5065685) B5065685
theorem B5343245 : Blo 1052612 5343245 := bstep (se 3 (by rfl) ⟨1001858, by rfl⟩ : syracuseStep 5343245 = 2003717) B2003717
theorem B15206453 : Blo 1052612 15206453 := bstep (se 5 (by rfl) ⟨712802, by rfl⟩ : syracuseStep 15206453 = 1425605) B1425605
theorem B1902673 : Blo 1052612 1902673 := bstep (se 2 (by rfl) ⟨713502, by rfl⟩ : syracuseStep 1902673 = 1427005) B1427005
theorem B9013517 : Blo 1052612 9013517 := bstep (se 3 (by rfl) ⟨1690034, by rfl⟩ : syracuseStep 9013517 = 3380069) B3380069
theorem B2885905 : Blo 1052612 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B4000205 : Blo 1052612 4000205 := bstep (se 3 (by rfl) ⟨750038, by rfl⟩ : syracuseStep 4000205 = 1500077) B1500077
theorem B5409251 : Blo 1052612 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B1903235 : Blo 1052612 1903235 := bstep (se 1 (by rfl) ⟨1427426, by rfl⟩ : syracuseStep 1903235 = 2854853) B2854853
theorem B6752909 : Blo 1052612 6752909 := bstep (se 3 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 6752909 = 2532341) B2532341
theorem B2001667 : Blo 1052612 2001667 := bstep (se 1 (by rfl) ⟨1501250, by rfl⟩ : syracuseStep 2001667 = 3002501) B3002501
theorem B3378019 : Blo 1052612 3378019 := bstep (se 1 (by rfl) ⟨2533514, by rfl⟩ : syracuseStep 3378019 = 5067029) B5067029
theorem B1444721 : Blo 1052612 1444721 := bstep (se 2 (by rfl) ⟨541770, by rfl⟩ : syracuseStep 1444721 = 1083541) B1083541
theorem B2001827 : Blo 1052612 2001827 := bstep (se 1 (by rfl) ⟨1501370, by rfl⟩ : syracuseStep 2001827 = 3002741) B3002741
theorem B2853805 : Blo 1052612 2853805 := bstep (se 3 (by rfl) ⟨535088, by rfl⟩ : syracuseStep 2853805 = 1070177) B1070177
theorem B1805411 : Blo 1052612 1805411 := bstep (se 1 (by rfl) ⟨1354058, by rfl⟩ : syracuseStep 1805411 = 2708117) B2708117
theorem B3607811 : Blo 1052612 3607811 := bstep (se 1 (by rfl) ⟨2705858, by rfl⟩ : syracuseStep 3607811 = 5411717) B5411717
theorem B6426125 : Blo 1052612 6426125 := bstep (se 3 (by rfl) ⟨1204898, by rfl⟩ : syracuseStep 6426125 = 2409797) B2409797
theorem B1543747 : Blo 1052612 1543747 := bstep (se 1 (by rfl) ⟨1157810, by rfl⟩ : syracuseStep 1543747 = 2315621) B2315621
theorem B3379121 : Blo 1052612 3379121 := bstep (se 2 (by rfl) ⟨1267170, by rfl⟩ : syracuseStep 3379121 = 2534341) B2534341
theorem B6000581 : Blo 1052612 6000581 := bstep (se 4 (by rfl) ⟨562554, by rfl⟩ : syracuseStep 6000581 = 1125109) B1125109
theorem B11407301 : Blo 1052612 11407301 := bstep (se 4 (by rfl) ⟨1069434, by rfl⟩ : syracuseStep 11407301 = 2138869) B2138869
theorem B5771213 : Blo 1052612 5771213 := bstep (se 3 (by rfl) ⟨1082102, by rfl⟩ : syracuseStep 5771213 = 2164205) B2164205
theorem B2002897 : Blo 1052612 2002897 := bstep (se 2 (by rfl) ⟨751086, by rfl⟩ : syracuseStep 2002897 = 1502173) B1502173
theorem B1052627 : Blo 1052612 1052627 := bstep (se 1 (by rfl) ⟨789470, by rfl⟩ : syracuseStep 1052627 = 1578941) B1578941
theorem B1052643 : Blo 1052612 1052643 := bstep (se 1 (by rfl) ⟨789482, by rfl⟩ : syracuseStep 1052643 = 1578965) B1578965
theorem B1052659 : Blo 1052612 1052659 := bstep (se 1 (by rfl) ⟨789494, by rfl⟩ : syracuseStep 1052659 = 1578989) B1578989
theorem B1052675 : Blo 1052612 1052675 := bstep (se 1 (by rfl) ⟨789506, by rfl⟩ : syracuseStep 1052675 = 1579013) B1579013
theorem B1052691 : Blo 1052612 1052691 := bstep (se 1 (by rfl) ⟨789518, by rfl⟩ : syracuseStep 1052691 = 1579037) B1579037
theorem B1052707 : Blo 1052612 1052707 := bstep (se 1 (by rfl) ⟨789530, by rfl⟩ : syracuseStep 1052707 = 1579061) B1579061
theorem B4165681 : Blo 1052612 4165681 := bstep (se 2 (by rfl) ⟨1562130, by rfl⟩ : syracuseStep 4165681 = 3124261) B3124261
theorem B3379249 : Blo 1052612 3379249 := bstep (se 2 (by rfl) ⟨1267218, by rfl⟩ : syracuseStep 3379249 = 2534437) B2534437
theorem B1052723 : Blo 1052612 1052723 := bstep (se 1 (by rfl) ⟨789542, by rfl⟩ : syracuseStep 1052723 = 1579085) B1579085
theorem B1052739 : Blo 1052612 1052739 := bstep (se 1 (by rfl) ⟨789554, by rfl⟩ : syracuseStep 1052739 = 1579109) B1579109
theorem B1052755 : Blo 1052612 1052755 := bstep (se 1 (by rfl) ⟨789566, by rfl⟩ : syracuseStep 1052755 = 1579133) B1579133
theorem B1052771 : Blo 1052612 1052771 := bstep (se 1 (by rfl) ⟨789578, by rfl⟩ : syracuseStep 1052771 = 1579157) B1579157
theorem B1052787 : Blo 1052612 1052787 := bstep (se 1 (by rfl) ⟨789590, by rfl⟩ : syracuseStep 1052787 = 1579181) B1579181
theorem B1052803 : Blo 1052612 1052803 := bstep (se 1 (by rfl) ⟨789602, by rfl⟩ : syracuseStep 1052803 = 1579205) B1579205
theorem B14422157 : Blo 1052612 14422157 := bstep (se 3 (by rfl) ⟨2704154, by rfl⟩ : syracuseStep 14422157 = 5408309) B5408309
theorem B1052819 : Blo 1052612 1052819 := bstep (se 1 (by rfl) ⟨789614, by rfl⟩ : syracuseStep 1052819 = 1579229) B1579229
theorem B1052835 : Blo 1052612 1052835 := bstep (se 1 (by rfl) ⟨789626, by rfl⟩ : syracuseStep 1052835 = 1579253) B1579253
theorem B1052851 : Blo 1052612 1052851 := bstep (se 1 (by rfl) ⟨789638, by rfl⟩ : syracuseStep 1052851 = 1579277) B1579277
theorem B1052867 : Blo 1052612 1052867 := bstep (se 1 (by rfl) ⟨789650, by rfl⟩ : syracuseStep 1052867 = 1579301) B1579301
theorem B1052883 : Blo 1052612 1052883 := bstep (se 1 (by rfl) ⟨789662, by rfl⟩ : syracuseStep 1052883 = 1579325) B1579325
theorem B1052899 : Blo 1052612 1052899 := bstep (se 1 (by rfl) ⟨789674, by rfl⟩ : syracuseStep 1052899 = 1579349) B1579349
theorem B1052915 : Blo 1052612 1052915 := bstep (se 1 (by rfl) ⟨789686, by rfl⟩ : syracuseStep 1052915 = 1579373) B1579373
theorem B1052931 : Blo 1052612 1052931 := bstep (se 1 (by rfl) ⟨789698, by rfl⟩ : syracuseStep 1052931 = 1579397) B1579397
theorem B1052947 : Blo 1052612 1052947 := bstep (se 1 (by rfl) ⟨789710, by rfl⟩ : syracuseStep 1052947 = 1579421) B1579421
theorem B1052963 : Blo 1052612 1052963 := bstep (se 1 (by rfl) ⟨789722, by rfl⟩ : syracuseStep 1052963 = 1579445) B1579445
theorem B1052979 : Blo 1052612 1052979 := bstep (se 1 (by rfl) ⟨789734, by rfl⟩ : syracuseStep 1052979 = 1579469) B1579469
theorem B1052995 : Blo 1052612 1052995 := bstep (se 1 (by rfl) ⟨789746, by rfl⟩ : syracuseStep 1052995 = 1579493) B1579493
theorem B1053011 : Blo 1052612 1053011 := bstep (se 1 (by rfl) ⟨789758, by rfl⟩ : syracuseStep 1053011 = 1579517) B1579517
theorem B1053027 : Blo 1052612 1053027 := bstep (se 1 (by rfl) ⟨789770, by rfl⟩ : syracuseStep 1053027 = 1579541) B1579541
theorem B1053043 : Blo 1052612 1053043 := bstep (se 1 (by rfl) ⟨789782, by rfl⟩ : syracuseStep 1053043 = 1579565) B1579565
theorem B1053059 : Blo 1052612 1053059 := bstep (se 1 (by rfl) ⟨789794, by rfl⟩ : syracuseStep 1053059 = 1579589) B1579589
theorem B6001037 : Blo 1052612 6001037 := bstep (se 3 (by rfl) ⟨1125194, by rfl⟩ : syracuseStep 6001037 = 2250389) B2250389
theorem B1053075 : Blo 1052612 1053075 := bstep (se 1 (by rfl) ⟨789806, by rfl⟩ : syracuseStep 1053075 = 1579613) B1579613
theorem B1053091 : Blo 1052612 1053091 := bstep (se 1 (by rfl) ⟨789818, by rfl⟩ : syracuseStep 1053091 = 1579637) B1579637
theorem B1053107 : Blo 1052612 1053107 := bstep (se 1 (by rfl) ⟨789830, by rfl⟩ : syracuseStep 1053107 = 1579661) B1579661
theorem B1053123 : Blo 1052612 1053123 := bstep (se 1 (by rfl) ⟨789842, by rfl⟩ : syracuseStep 1053123 = 1579685) B1579685
theorem B1053139 : Blo 1052612 1053139 := bstep (se 1 (by rfl) ⟨789854, by rfl⟩ : syracuseStep 1053139 = 1579709) B1579709
theorem B1053155 : Blo 1052612 1053155 := bstep (se 1 (by rfl) ⟨789866, by rfl⟩ : syracuseStep 1053155 = 1579733) B1579733
theorem B1053171 : Blo 1052612 1053171 := bstep (se 1 (by rfl) ⟨789878, by rfl⟩ : syracuseStep 1053171 = 1579757) B1579757
theorem B1053187 : Blo 1052612 1053187 := bstep (se 1 (by rfl) ⟨789890, by rfl⟩ : syracuseStep 1053187 = 1579781) B1579781
theorem B4002317 : Blo 1052612 4002317 := bstep (se 3 (by rfl) ⟨750434, by rfl⟩ : syracuseStep 4002317 = 1500869) B1500869
theorem B1053203 : Blo 1052612 1053203 := bstep (se 1 (by rfl) ⟨789902, by rfl⟩ : syracuseStep 1053203 = 1579805) B1579805
theorem B1053219 : Blo 1052612 1053219 := bstep (se 1 (by rfl) ⟨789914, by rfl⟩ : syracuseStep 1053219 = 1579829) B1579829
theorem B1053235 : Blo 1052612 1053235 := bstep (se 1 (by rfl) ⟨789926, by rfl⟩ : syracuseStep 1053235 = 1579853) B1579853
theorem B1184323 : Blo 1052612 1184323 := bstep (se 1 (by rfl) ⟨888242, by rfl⟩ : syracuseStep 1184323 = 1776485) B1776485
theorem B1053251 : Blo 1052612 1053251 := bstep (se 1 (by rfl) ⟨789938, by rfl⟩ : syracuseStep 1053251 = 1579877) B1579877
theorem B1053267 : Blo 1052612 1053267 := bstep (se 1 (by rfl) ⟨789950, by rfl⟩ : syracuseStep 1053267 = 1579901) B1579901
theorem B1053283 : Blo 1052612 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B9015907 : Blo 1052612 9015907 := bstep (se 1 (by rfl) ⟨6761930, by rfl⟩ : syracuseStep 9015907 = 13523861) B13523861
theorem B1053299 : Blo 1052612 1053299 := bstep (se 1 (by rfl) ⟨789974, by rfl⟩ : syracuseStep 1053299 = 1579949) B1579949
theorem B1053315 : Blo 1052612 1053315 := bstep (se 1 (by rfl) ⟨789986, by rfl⟩ : syracuseStep 1053315 = 1579973) B1579973
theorem B1053331 : Blo 1052612 1053331 := bstep (se 1 (by rfl) ⟨789998, by rfl⟩ : syracuseStep 1053331 = 1579997) B1579997
theorem B1446547 : Blo 1052612 1446547 := bstep (se 1 (by rfl) ⟨1084910, by rfl⟩ : syracuseStep 1446547 = 2169821) B2169821
theorem B1053347 : Blo 1052612 1053347 := bstep (se 1 (by rfl) ⟨790010, by rfl⟩ : syracuseStep 1053347 = 1580021) B1580021
theorem B1053363 : Blo 1052612 1053363 := bstep (se 1 (by rfl) ⟨790022, by rfl⟩ : syracuseStep 1053363 = 1580045) B1580045
theorem B1053379 : Blo 1052612 1053379 := bstep (se 1 (by rfl) ⟨790034, by rfl⟩ : syracuseStep 1053379 = 1580069) B1580069
theorem B9638597 : Blo 1052612 9638597 := bstep (se 4 (by rfl) ⟨903618, by rfl⟩ : syracuseStep 9638597 = 1807237) B1807237
theorem B1184467 : Blo 1052612 1184467 := bstep (se 1 (by rfl) ⟨888350, by rfl⟩ : syracuseStep 1184467 = 1776701) B1776701
theorem B1053395 : Blo 1052612 1053395 := bstep (se 1 (by rfl) ⟨790046, by rfl⟩ : syracuseStep 1053395 = 1580093) B1580093
theorem B1053411 : Blo 1052612 1053411 := bstep (se 1 (by rfl) ⟨790058, by rfl⟩ : syracuseStep 1053411 = 1580117) B1580117
theorem B1053427 : Blo 1052612 1053427 := bstep (se 1 (by rfl) ⟨790070, by rfl⟩ : syracuseStep 1053427 = 1580141) B1580141
theorem B1053443 : Blo 1052612 1053443 := bstep (se 1 (by rfl) ⟨790082, by rfl⟩ : syracuseStep 1053443 = 1580165) B1580165
theorem B1053459 : Blo 1052612 1053459 := bstep (se 1 (by rfl) ⟨790094, by rfl⟩ : syracuseStep 1053459 = 1580189) B1580189
theorem B1053475 : Blo 1052612 1053475 := bstep (se 1 (by rfl) ⟨790106, by rfl⟩ : syracuseStep 1053475 = 1580213) B1580213
theorem B1053491 : Blo 1052612 1053491 := bstep (se 1 (by rfl) ⟨790118, by rfl⟩ : syracuseStep 1053491 = 1580237) B1580237
theorem B1053507 : Blo 1052612 1053507 := bstep (se 1 (by rfl) ⟨790130, by rfl⟩ : syracuseStep 1053507 = 1580261) B1580261
theorem B1053523 : Blo 1052612 1053523 := bstep (se 1 (by rfl) ⟨790142, by rfl⟩ : syracuseStep 1053523 = 1580285) B1580285
theorem B1184611 : Blo 1052612 1184611 := bstep (se 1 (by rfl) ⟨888458, by rfl⟩ : syracuseStep 1184611 = 1776917) B1776917
theorem B1053539 : Blo 1052612 1053539 := bstep (se 1 (by rfl) ⟨790154, by rfl⟩ : syracuseStep 1053539 = 1580309) B1580309
theorem B5346161 : Blo 1052612 5346161 := bstep (se 2 (by rfl) ⟨2004810, by rfl⟩ : syracuseStep 5346161 = 4009621) B4009621
theorem B1053555 : Blo 1052612 1053555 := bstep (se 1 (by rfl) ⟨790166, by rfl⟩ : syracuseStep 1053555 = 1580333) B1580333
theorem B1053571 : Blo 1052612 1053571 := bstep (se 1 (by rfl) ⟨790178, by rfl⟩ : syracuseStep 1053571 = 1580357) B1580357
theorem B1053587 : Blo 1052612 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B1053603 : Blo 1052612 1053603 := bstep (se 1 (by rfl) ⟨790202, by rfl⟩ : syracuseStep 1053603 = 1580405) B1580405
theorem B1053619 : Blo 1052612 1053619 := bstep (se 1 (by rfl) ⟨790214, by rfl⟩ : syracuseStep 1053619 = 1580429) B1580429
theorem B1053635 : Blo 1052612 1053635 := bstep (se 1 (by rfl) ⟨790226, by rfl⟩ : syracuseStep 1053635 = 1580453) B1580453
theorem B1053651 : Blo 1052612 1053651 := bstep (se 1 (by rfl) ⟨790238, by rfl⟩ : syracuseStep 1053651 = 1580477) B1580477
theorem B1053667 : Blo 1052612 1053667 := bstep (se 1 (by rfl) ⟨790250, by rfl⟩ : syracuseStep 1053667 = 1580501) B1580501
theorem B2003953 : Blo 1052612 2003953 := bstep (se 2 (by rfl) ⟨751482, by rfl⟩ : syracuseStep 2003953 = 1502965) B1502965
theorem B1184755 : Blo 1052612 1184755 := bstep (se 1 (by rfl) ⟨888566, by rfl⟩ : syracuseStep 1184755 = 1777133) B1777133
theorem B1053683 : Blo 1052612 1053683 := bstep (se 1 (by rfl) ⟨790262, by rfl⟩ : syracuseStep 1053683 = 1580525) B1580525
theorem B1053699 : Blo 1052612 1053699 := bstep (se 1 (by rfl) ⟨790274, by rfl⟩ : syracuseStep 1053699 = 1580549) B1580549
theorem B3380237 : Blo 1052612 3380237 := bstep (se 3 (by rfl) ⟨633794, by rfl⟩ : syracuseStep 3380237 = 1267589) B1267589
theorem B1053715 : Blo 1052612 1053715 := bstep (se 1 (by rfl) ⟨790286, by rfl⟩ : syracuseStep 1053715 = 1580573) B1580573
theorem B1053731 : Blo 1052612 1053731 := bstep (se 1 (by rfl) ⟨790298, by rfl⟩ : syracuseStep 1053731 = 1580597) B1580597
theorem B1053747 : Blo 1052612 1053747 := bstep (se 1 (by rfl) ⟨790310, by rfl⟩ : syracuseStep 1053747 = 1580621) B1580621
theorem B1053763 : Blo 1052612 1053763 := bstep (se 1 (by rfl) ⟨790322, by rfl⟩ : syracuseStep 1053763 = 1580645) B1580645
theorem B1053779 : Blo 1052612 1053779 := bstep (se 1 (by rfl) ⟨790334, by rfl⟩ : syracuseStep 1053779 = 1580669) B1580669
theorem B1053795 : Blo 1052612 1053795 := bstep (se 1 (by rfl) ⟨790346, by rfl⟩ : syracuseStep 1053795 = 1580693) B1580693
theorem B1053811 : Blo 1052612 1053811 := bstep (se 1 (by rfl) ⟨790358, by rfl⟩ : syracuseStep 1053811 = 1580717) B1580717
theorem B1184899 : Blo 1052612 1184899 := bstep (se 1 (by rfl) ⟨888674, by rfl⟩ : syracuseStep 1184899 = 1777349) B1777349
theorem B1053827 : Blo 1052612 1053827 := bstep (se 1 (by rfl) ⟨790370, by rfl⟩ : syracuseStep 1053827 = 1580741) B1580741
theorem B1053843 : Blo 1052612 1053843 := bstep (se 1 (by rfl) ⟨790382, by rfl⟩ : syracuseStep 1053843 = 1580765) B1580765
theorem B1053859 : Blo 1052612 1053859 := bstep (se 1 (by rfl) ⟨790394, by rfl⟩ : syracuseStep 1053859 = 1580789) B1580789
theorem B1053875 : Blo 1052612 1053875 := bstep (se 1 (by rfl) ⟨790406, by rfl⟩ : syracuseStep 1053875 = 1580813) B1580813
theorem B1053891 : Blo 1052612 1053891 := bstep (se 1 (by rfl) ⟨790418, by rfl⟩ : syracuseStep 1053891 = 1580837) B1580837
theorem B1053907 : Blo 1052612 1053907 := bstep (se 1 (by rfl) ⟨790430, by rfl⟩ : syracuseStep 1053907 = 1580861) B1580861
theorem B1053923 : Blo 1052612 1053923 := bstep (se 1 (by rfl) ⟨790442, by rfl⟩ : syracuseStep 1053923 = 1580885) B1580885
theorem B1053939 : Blo 1052612 1053939 := bstep (se 1 (by rfl) ⟨790454, by rfl⟩ : syracuseStep 1053939 = 1580909) B1580909
theorem B1053955 : Blo 1052612 1053955 := bstep (se 1 (by rfl) ⟨790466, by rfl⟩ : syracuseStep 1053955 = 1580933) B1580933
theorem B1185043 : Blo 1052612 1185043 := bstep (se 1 (by rfl) ⟨888782, by rfl⟩ : syracuseStep 1185043 = 1777565) B1777565
theorem B1053971 : Blo 1052612 1053971 := bstep (se 1 (by rfl) ⟨790478, by rfl⟩ : syracuseStep 1053971 = 1580957) B1580957
theorem B1053987 : Blo 1052612 1053987 := bstep (se 1 (by rfl) ⟨790490, by rfl⟩ : syracuseStep 1053987 = 1580981) B1580981
theorem B4003121 : Blo 1052612 4003121 := bstep (se 2 (by rfl) ⟨1501170, by rfl⟩ : syracuseStep 4003121 = 3002341) B3002341
theorem B1054003 : Blo 1052612 1054003 := bstep (se 1 (by rfl) ⟨790502, by rfl⟩ : syracuseStep 1054003 = 1581005) B1581005
theorem B1054019 : Blo 1052612 1054019 := bstep (se 1 (by rfl) ⟨790514, by rfl⟩ : syracuseStep 1054019 = 1581029) B1581029
theorem B1054035 : Blo 1052612 1054035 := bstep (se 1 (by rfl) ⟨790526, by rfl⟩ : syracuseStep 1054035 = 1581053) B1581053
theorem B1054051 : Blo 1052612 1054051 := bstep (se 1 (by rfl) ⟨790538, by rfl⟩ : syracuseStep 1054051 = 1581077) B1581077
theorem B1054067 : Blo 1052612 1054067 := bstep (se 1 (by rfl) ⟨790550, by rfl⟩ : syracuseStep 1054067 = 1581101) B1581101
theorem B1054083 : Blo 1052612 1054083 := bstep (se 1 (by rfl) ⟨790562, by rfl⟩ : syracuseStep 1054083 = 1581125) B1581125
theorem B2004355 : Blo 1052612 2004355 := bstep (se 1 (by rfl) ⟨1503266, by rfl⟩ : syracuseStep 2004355 = 3006533) B3006533
theorem B1054099 : Blo 1052612 1054099 := bstep (se 1 (by rfl) ⟨790574, by rfl⟩ : syracuseStep 1054099 = 1581149) B1581149
theorem B1185187 : Blo 1052612 1185187 := bstep (se 1 (by rfl) ⟨888890, by rfl⟩ : syracuseStep 1185187 = 1777781) B1777781
theorem B1054115 : Blo 1052612 1054115 := bstep (se 1 (by rfl) ⟨790586, by rfl⟩ : syracuseStep 1054115 = 1581173) B1581173
theorem B2004401 : Blo 1052612 2004401 := bstep (se 2 (by rfl) ⟨751650, by rfl⟩ : syracuseStep 2004401 = 1503301) B1503301
theorem B1054131 : Blo 1052612 1054131 := bstep (se 1 (by rfl) ⟨790598, by rfl⟩ : syracuseStep 1054131 = 1581197) B1581197
theorem B1054147 : Blo 1052612 1054147 := bstep (se 1 (by rfl) ⟨790610, by rfl⟩ : syracuseStep 1054147 = 1581221) B1581221
theorem B1054163 : Blo 1052612 1054163 := bstep (se 1 (by rfl) ⟨790622, by rfl⟩ : syracuseStep 1054163 = 1581245) B1581245
theorem B1054179 : Blo 1052612 1054179 := bstep (se 1 (by rfl) ⟨790634, by rfl⟩ : syracuseStep 1054179 = 1581269) B1581269
theorem B1054195 : Blo 1052612 1054195 := bstep (se 1 (by rfl) ⟨790646, by rfl⟩ : syracuseStep 1054195 = 1581293) B1581293
theorem B1054211 : Blo 1052612 1054211 := bstep (se 1 (by rfl) ⟨790658, by rfl⟩ : syracuseStep 1054211 = 1581317) B1581317
theorem B1054227 : Blo 1052612 1054227 := bstep (se 1 (by rfl) ⟨790670, by rfl⟩ : syracuseStep 1054227 = 1581341) B1581341
theorem B1054243 : Blo 1052612 1054243 := bstep (se 1 (by rfl) ⟨790682, by rfl⟩ : syracuseStep 1054243 = 1581365) B1581365
theorem B1185331 : Blo 1052612 1185331 := bstep (se 1 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 1185331 = 1777997) B1777997
theorem B1054259 : Blo 1052612 1054259 := bstep (se 1 (by rfl) ⟨790694, by rfl⟩ : syracuseStep 1054259 = 1581389) B1581389
theorem B1054275 : Blo 1052612 1054275 := bstep (se 1 (by rfl) ⟨790706, by rfl⟩ : syracuseStep 1054275 = 1581413) B1581413
theorem B1054291 : Blo 1052612 1054291 := bstep (se 1 (by rfl) ⟨790718, by rfl⟩ : syracuseStep 1054291 = 1581437) B1581437
theorem B1054307 : Blo 1052612 1054307 := bstep (se 1 (by rfl) ⟨790730, by rfl⟩ : syracuseStep 1054307 = 1581461) B1581461
theorem B1054323 : Blo 1052612 1054323 := bstep (se 1 (by rfl) ⟨790742, by rfl⟩ : syracuseStep 1054323 = 1581485) B1581485
theorem B2135683 : Blo 1052612 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B1054339 : Blo 1052612 1054339 := bstep (se 1 (by rfl) ⟨790754, by rfl⟩ : syracuseStep 1054339 = 1581509) B1581509
theorem B8132237 : Blo 1052612 8132237 := bstep (se 3 (by rfl) ⟨1524794, by rfl⟩ : syracuseStep 8132237 = 3049589) B3049589
theorem B1054355 : Blo 1052612 1054355 := bstep (se 1 (by rfl) ⟨790766, by rfl⟩ : syracuseStep 1054355 = 1581533) B1581533
theorem B1054371 : Blo 1052612 1054371 := bstep (se 1 (by rfl) ⟨790778, by rfl⟩ : syracuseStep 1054371 = 1581557) B1581557
theorem B1054387 : Blo 1052612 1054387 := bstep (se 1 (by rfl) ⟨790790, by rfl⟩ : syracuseStep 1054387 = 1581581) B1581581
theorem B1185475 : Blo 1052612 1185475 := bstep (se 1 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 1185475 = 1778213) B1778213
theorem B1054403 : Blo 1052612 1054403 := bstep (se 1 (by rfl) ⟨790802, by rfl⟩ : syracuseStep 1054403 = 1581605) B1581605
theorem B2004689 : Blo 1052612 2004689 := bstep (se 2 (by rfl) ⟨751758, by rfl⟩ : syracuseStep 2004689 = 1503517) B1503517
theorem B1054419 : Blo 1052612 1054419 := bstep (se 1 (by rfl) ⟨790814, by rfl⟩ : syracuseStep 1054419 = 1581629) B1581629
theorem B1054435 : Blo 1052612 1054435 := bstep (se 1 (by rfl) ⟨790826, by rfl⟩ : syracuseStep 1054435 = 1581653) B1581653
theorem B1054451 : Blo 1052612 1054451 := bstep (se 1 (by rfl) ⟨790838, by rfl⟩ : syracuseStep 1054451 = 1581677) B1581677
theorem B1054467 : Blo 1052612 1054467 := bstep (se 1 (by rfl) ⟨790850, by rfl⟩ : syracuseStep 1054467 = 1581701) B1581701
theorem B1054483 : Blo 1052612 1054483 := bstep (se 1 (by rfl) ⟨790862, by rfl⟩ : syracuseStep 1054483 = 1581725) B1581725
theorem B1054499 : Blo 1052612 1054499 := bstep (se 1 (by rfl) ⟨790874, by rfl⟩ : syracuseStep 1054499 = 1581749) B1581749
theorem B1054515 : Blo 1052612 1054515 := bstep (se 1 (by rfl) ⟨790886, by rfl⟩ : syracuseStep 1054515 = 1581773) B1581773
theorem B1054531 : Blo 1052612 1054531 := bstep (se 1 (by rfl) ⟨790898, by rfl⟩ : syracuseStep 1054531 = 1581797) B1581797
theorem B1185619 : Blo 1052612 1185619 := bstep (se 1 (by rfl) ⟨889214, by rfl⟩ : syracuseStep 1185619 = 1778429) B1778429
theorem B1054547 : Blo 1052612 1054547 := bstep (se 1 (by rfl) ⟨790910, by rfl⟩ : syracuseStep 1054547 = 1581821) B1581821
theorem B1054563 : Blo 1052612 1054563 := bstep (se 1 (by rfl) ⟨790922, by rfl⟩ : syracuseStep 1054563 = 1581845) B1581845
theorem B1054579 : Blo 1052612 1054579 := bstep (se 1 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 1054579 = 1581869) B1581869
theorem B1054595 : Blo 1052612 1054595 := bstep (se 1 (by rfl) ⟨790946, by rfl⟩ : syracuseStep 1054595 = 1581893) B1581893
theorem B1054611 : Blo 1052612 1054611 := bstep (se 1 (by rfl) ⟨790958, by rfl⟩ : syracuseStep 1054611 = 1581917) B1581917
theorem B1054627 : Blo 1052612 1054627 := bstep (se 1 (by rfl) ⟨790970, by rfl⟩ : syracuseStep 1054627 = 1581941) B1581941
theorem B1578929 : Blo 1052612 1578929 := bstep (se 2 (by rfl) ⟨592098, by rfl⟩ : syracuseStep 1578929 = 1184197) B1184197
theorem B1054643 : Blo 1052612 1054643 := bstep (se 1 (by rfl) ⟨790982, by rfl⟩ : syracuseStep 1054643 = 1581965) B1581965
theorem B1578947 : Blo 1052612 1578947 := bstep (se 1 (by rfl) ⟨1184210, by rfl⟩ : syracuseStep 1578947 = 2368421) B2368421
theorem B1054659 : Blo 1052612 1054659 := bstep (se 1 (by rfl) ⟨790994, by rfl⟩ : syracuseStep 1054659 = 1581989) B1581989
theorem B4003789 : Blo 1052612 4003789 := bstep (se 3 (by rfl) ⟨750710, by rfl⟩ : syracuseStep 4003789 = 1501421) B1501421
theorem B1054675 : Blo 1052612 1054675 := bstep (se 1 (by rfl) ⟨791006, by rfl⟩ : syracuseStep 1054675 = 1582013) B1582013
theorem B1578977 : Blo 1052612 1578977 := bstep (se 2 (by rfl) ⟨592116, by rfl⟩ : syracuseStep 1578977 = 1184233) B1184233
theorem B1185763 : Blo 1052612 1185763 := bstep (se 1 (by rfl) ⟨889322, by rfl⟩ : syracuseStep 1185763 = 1778645) B1778645
theorem B1054691 : Blo 1052612 1054691 := bstep (se 1 (by rfl) ⟨791018, by rfl⟩ : syracuseStep 1054691 = 1582037) B1582037
theorem B1578995 : Blo 1052612 1578995 := bstep (se 1 (by rfl) ⟨1184246, by rfl⟩ : syracuseStep 1578995 = 2368493) B2368493
theorem B1054707 : Blo 1052612 1054707 := bstep (se 1 (by rfl) ⟨791030, by rfl⟩ : syracuseStep 1054707 = 1582061) B1582061
theorem B1054723 : Blo 1052612 1054723 := bstep (se 1 (by rfl) ⟨791042, by rfl⟩ : syracuseStep 1054723 = 1582085) B1582085
theorem B1579025 : Blo 1052612 1579025 := bstep (se 2 (by rfl) ⟨592134, by rfl⟩ : syracuseStep 1579025 = 1184269) B1184269
theorem B1054739 : Blo 1052612 1054739 := bstep (se 1 (by rfl) ⟨791054, by rfl⟩ : syracuseStep 1054739 = 1582109) B1582109
theorem B1579043 : Blo 1052612 1579043 := bstep (se 1 (by rfl) ⟨1184282, by rfl⟩ : syracuseStep 1579043 = 2368565) B2368565
theorem B4626467 : Blo 1052612 4626467 := bstep (se 1 (by rfl) ⟨3469850, by rfl⟩ : syracuseStep 4626467 = 6939701) B6939701
theorem B1054755 : Blo 1052612 1054755 := bstep (se 1 (by rfl) ⟨791066, by rfl⟩ : syracuseStep 1054755 = 1582133) B1582133
theorem B1054771 : Blo 1052612 1054771 := bstep (se 1 (by rfl) ⟨791078, by rfl⟩ : syracuseStep 1054771 = 1582157) B1582157
theorem B1579073 : Blo 1052612 1579073 := bstep (se 2 (by rfl) ⟨592152, by rfl⟩ : syracuseStep 1579073 = 1184305) B1184305
theorem B1054787 : Blo 1052612 1054787 := bstep (se 1 (by rfl) ⟨791090, by rfl⟩ : syracuseStep 1054787 = 1582181) B1582181
theorem B1579091 : Blo 1052612 1579091 := bstep (se 1 (by rfl) ⟨1184318, by rfl⟩ : syracuseStep 1579091 = 2368637) B2368637
theorem B1054803 : Blo 1052612 1054803 := bstep (se 1 (by rfl) ⟨791102, by rfl⟩ : syracuseStep 1054803 = 1582205) B1582205
theorem B1054819 : Blo 1052612 1054819 := bstep (se 1 (by rfl) ⟨791114, by rfl⟩ : syracuseStep 1054819 = 1582229) B1582229
theorem B1579121 : Blo 1052612 1579121 := bstep (se 2 (by rfl) ⟨592170, by rfl⟩ : syracuseStep 1579121 = 1184341) B1184341
theorem B1185907 : Blo 1052612 1185907 := bstep (se 1 (by rfl) ⟨889430, by rfl⟩ : syracuseStep 1185907 = 1778861) B1778861
theorem B1054835 : Blo 1052612 1054835 := bstep (se 1 (by rfl) ⟨791126, by rfl⟩ : syracuseStep 1054835 = 1582253) B1582253
theorem B1579139 : Blo 1052612 1579139 := bstep (se 1 (by rfl) ⟨1184354, by rfl⟩ : syracuseStep 1579139 = 2368709) B2368709
theorem B1054851 : Blo 1052612 1054851 := bstep (se 1 (by rfl) ⟨791138, by rfl⟩ : syracuseStep 1054851 = 1582277) B1582277
theorem B1054867 : Blo 1052612 1054867 := bstep (se 1 (by rfl) ⟨791150, by rfl⟩ : syracuseStep 1054867 = 1582301) B1582301
theorem B1579169 : Blo 1052612 1579169 := bstep (se 2 (by rfl) ⟨592188, by rfl⟩ : syracuseStep 1579169 = 1184377) B1184377
theorem B1054883 : Blo 1052612 1054883 := bstep (se 1 (by rfl) ⟨791162, by rfl⟩ : syracuseStep 1054883 = 1582325) B1582325
theorem B1579187 : Blo 1052612 1579187 := bstep (se 1 (by rfl) ⟨1184390, by rfl⟩ : syracuseStep 1579187 = 2368781) B2368781
theorem B1054899 : Blo 1052612 1054899 := bstep (se 1 (by rfl) ⟨791174, by rfl⟩ : syracuseStep 1054899 = 1582349) B1582349
theorem B1054915 : Blo 1052612 1054915 := bstep (se 1 (by rfl) ⟨791186, by rfl⟩ : syracuseStep 1054915 = 1582373) B1582373
theorem B1579217 : Blo 1052612 1579217 := bstep (se 2 (by rfl) ⟨592206, by rfl⟩ : syracuseStep 1579217 = 1184413) B1184413
theorem B1054931 : Blo 1052612 1054931 := bstep (se 1 (by rfl) ⟨791198, by rfl⟩ : syracuseStep 1054931 = 1582397) B1582397
theorem B1579235 : Blo 1052612 1579235 := bstep (se 1 (by rfl) ⟨1184426, by rfl⟩ : syracuseStep 1579235 = 2368853) B2368853
theorem B25663715 : Blo 1052612 25663715 := bstep (se 1 (by rfl) ⟨19247786, by rfl⟩ : syracuseStep 25663715 = 38495573) B38495573
theorem B1054947 : Blo 1052612 1054947 := bstep (se 1 (by rfl) ⟨791210, by rfl⟩ : syracuseStep 1054947 = 1582421) B1582421
theorem B1054963 : Blo 1052612 1054963 := bstep (se 1 (by rfl) ⟨791222, by rfl⟩ : syracuseStep 1054963 = 1582445) B1582445
theorem B1579265 : Blo 1052612 1579265 := bstep (se 2 (by rfl) ⟨592224, by rfl⟩ : syracuseStep 1579265 = 1184449) B1184449
theorem B1186051 : Blo 1052612 1186051 := bstep (se 1 (by rfl) ⟨889538, by rfl⟩ : syracuseStep 1186051 = 1779077) B1779077
theorem B1054979 : Blo 1052612 1054979 := bstep (se 1 (by rfl) ⟨791234, by rfl⟩ : syracuseStep 1054979 = 1582469) B1582469
theorem B1579283 : Blo 1052612 1579283 := bstep (se 1 (by rfl) ⟨1184462, by rfl⟩ : syracuseStep 1579283 = 2368925) B2368925
theorem B1054995 : Blo 1052612 1054995 := bstep (se 1 (by rfl) ⟨791246, by rfl⟩ : syracuseStep 1054995 = 1582493) B1582493
theorem B1055011 : Blo 1052612 1055011 := bstep (se 1 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 1055011 = 1582517) B1582517
theorem B5347619 : Blo 1052612 5347619 := bstep (se 1 (by rfl) ⟨4010714, by rfl⟩ : syracuseStep 5347619 = 8021429) B8021429
theorem B1579313 : Blo 1052612 1579313 := bstep (se 2 (by rfl) ⟨592242, by rfl⟩ : syracuseStep 1579313 = 1184485) B1184485
theorem B1055027 : Blo 1052612 1055027 := bstep (se 1 (by rfl) ⟨791270, by rfl⟩ : syracuseStep 1055027 = 1582541) B1582541
theorem B1579331 : Blo 1052612 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B1055043 : Blo 1052612 1055043 := bstep (se 1 (by rfl) ⟨791282, by rfl⟩ : syracuseStep 1055043 = 1582565) B1582565
theorem B3381581 : Blo 1052612 3381581 := bstep (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) B1268093
theorem B1055059 : Blo 1052612 1055059 := bstep (se 1 (by rfl) ⟨791294, by rfl⟩ : syracuseStep 1055059 = 1582589) B1582589
theorem B1579361 : Blo 1052612 1579361 := bstep (se 2 (by rfl) ⟨592260, by rfl⟩ : syracuseStep 1579361 = 1184521) B1184521
theorem B1055075 : Blo 1052612 1055075 := bstep (se 1 (by rfl) ⟨791306, by rfl⟩ : syracuseStep 1055075 = 1582613) B1582613
theorem B1579379 : Blo 1052612 1579379 := bstep (se 1 (by rfl) ⟨1184534, by rfl⟩ : syracuseStep 1579379 = 2369069) B2369069
theorem B1055091 : Blo 1052612 1055091 := bstep (se 1 (by rfl) ⟨791318, by rfl⟩ : syracuseStep 1055091 = 1582637) B1582637
theorem B1055107 : Blo 1052612 1055107 := bstep (se 1 (by rfl) ⟨791330, by rfl⟩ : syracuseStep 1055107 = 1582661) B1582661
theorem B1579409 : Blo 1052612 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B1186195 : Blo 1052612 1186195 := bstep (se 1 (by rfl) ⟨889646, by rfl⟩ : syracuseStep 1186195 = 1779293) B1779293
theorem B1055123 : Blo 1052612 1055123 := bstep (se 1 (by rfl) ⟨791342, by rfl⟩ : syracuseStep 1055123 = 1582685) B1582685
theorem B1579427 : Blo 1052612 1579427 := bstep (se 1 (by rfl) ⟨1184570, by rfl⟩ : syracuseStep 1579427 = 2369141) B2369141
theorem B1055139 : Blo 1052612 1055139 := bstep (se 1 (by rfl) ⟨791354, by rfl⟩ : syracuseStep 1055139 = 1582709) B1582709
theorem B2005411 : Blo 1052612 2005411 := bstep (se 1 (by rfl) ⟨1504058, by rfl⟩ : syracuseStep 2005411 = 3008117) B3008117
theorem B1055155 : Blo 1052612 1055155 := bstep (se 1 (by rfl) ⟨791366, by rfl⟩ : syracuseStep 1055155 = 1582733) B1582733
theorem B1579457 : Blo 1052612 1579457 := bstep (se 2 (by rfl) ⟨592296, by rfl⟩ : syracuseStep 1579457 = 1184593) B1184593
theorem B1055171 : Blo 1052612 1055171 := bstep (se 1 (by rfl) ⟨791378, by rfl⟩ : syracuseStep 1055171 = 1582757) B1582757
theorem B8001989 : Blo 1052612 8001989 := bstep (se 4 (by rfl) ⟨750186, by rfl⟩ : syracuseStep 8001989 = 1500373) B1500373
theorem B1579475 : Blo 1052612 1579475 := bstep (se 1 (by rfl) ⟨1184606, by rfl⟩ : syracuseStep 1579475 = 2369213) B2369213
theorem B1055187 : Blo 1052612 1055187 := bstep (se 1 (by rfl) ⟨791390, by rfl⟩ : syracuseStep 1055187 = 1582781) B1582781
theorem B1055203 : Blo 1052612 1055203 := bstep (se 1 (by rfl) ⟨791402, by rfl⟩ : syracuseStep 1055203 = 1582805) B1582805
theorem B1579505 : Blo 1052612 1579505 := bstep (se 2 (by rfl) ⟨592314, by rfl⟩ : syracuseStep 1579505 = 1184629) B1184629
theorem B1055219 : Blo 1052612 1055219 := bstep (se 1 (by rfl) ⟨791414, by rfl⟩ : syracuseStep 1055219 = 1582829) B1582829
theorem B1579523 : Blo 1052612 1579523 := bstep (se 1 (by rfl) ⟨1184642, by rfl⟩ : syracuseStep 1579523 = 2369285) B2369285
theorem B1055235 : Blo 1052612 1055235 := bstep (se 1 (by rfl) ⟨791426, by rfl⟩ : syracuseStep 1055235 = 1582853) B1582853
theorem B1055251 : Blo 1052612 1055251 := bstep (se 1 (by rfl) ⟨791438, by rfl⟩ : syracuseStep 1055251 = 1582877) B1582877
theorem B1579553 : Blo 1052612 1579553 := bstep (se 2 (by rfl) ⟨592332, by rfl⟩ : syracuseStep 1579553 = 1184665) B1184665
theorem B1186339 : Blo 1052612 1186339 := bstep (se 1 (by rfl) ⟨889754, by rfl⟩ : syracuseStep 1186339 = 1779509) B1779509
theorem B1055267 : Blo 1052612 1055267 := bstep (se 1 (by rfl) ⟨791450, by rfl⟩ : syracuseStep 1055267 = 1582901) B1582901
theorem B6855203 : Blo 1052612 6855203 := bstep (se 1 (by rfl) ⟨5141402, by rfl⟩ : syracuseStep 6855203 = 10282805) B10282805
theorem B1579571 : Blo 1052612 1579571 := bstep (se 1 (by rfl) ⟨1184678, by rfl⟩ : syracuseStep 1579571 = 2369357) B2369357
theorem B1055283 : Blo 1052612 1055283 := bstep (se 1 (by rfl) ⟨791462, by rfl⟩ : syracuseStep 1055283 = 1582925) B1582925
theorem B1055299 : Blo 1052612 1055299 := bstep (se 1 (by rfl) ⟨791474, by rfl⟩ : syracuseStep 1055299 = 1582949) B1582949
theorem B1579601 : Blo 1052612 1579601 := bstep (se 2 (by rfl) ⟨592350, by rfl⟩ : syracuseStep 1579601 = 1184701) B1184701
theorem B1055315 : Blo 1052612 1055315 := bstep (se 1 (by rfl) ⟨791486, by rfl⟩ : syracuseStep 1055315 = 1582973) B1582973
theorem B1579619 : Blo 1052612 1579619 := bstep (se 1 (by rfl) ⟨1184714, by rfl⟩ : syracuseStep 1579619 = 2369429) B2369429
theorem B1055331 : Blo 1052612 1055331 := bstep (se 1 (by rfl) ⟨791498, by rfl⟩ : syracuseStep 1055331 = 1582997) B1582997
theorem B3086957 : Blo 1052612 3086957 := bstep (se 3 (by rfl) ⟨578804, by rfl⟩ : syracuseStep 3086957 = 1157609) B1157609
theorem B1055347 : Blo 1052612 1055347 := bstep (se 1 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 1055347 = 1583021) B1583021
theorem B1579649 : Blo 1052612 1579649 := bstep (se 2 (by rfl) ⟨592368, by rfl⟩ : syracuseStep 1579649 = 1184737) B1184737
theorem B1055363 : Blo 1052612 1055363 := bstep (se 1 (by rfl) ⟨791522, by rfl⟩ : syracuseStep 1055363 = 1583045) B1583045
theorem B2136721 : Blo 1052612 2136721 := bstep (se 2 (by rfl) ⟨801270, by rfl⟩ : syracuseStep 2136721 = 1602541) B1602541
theorem B1579667 : Blo 1052612 1579667 := bstep (se 1 (by rfl) ⟨1184750, by rfl⟩ : syracuseStep 1579667 = 2369501) B2369501
theorem B1055379 : Blo 1052612 1055379 := bstep (se 1 (by rfl) ⟨791534, by rfl⟩ : syracuseStep 1055379 = 1583069) B1583069
theorem B1776289 : Blo 1052612 1776289 := bstep (se 2 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 1776289 = 1332217) B1332217
theorem B1055395 : Blo 1052612 1055395 := bstep (se 1 (by rfl) ⟨791546, by rfl⟩ : syracuseStep 1055395 = 1583093) B1583093
theorem B1579697 : Blo 1052612 1579697 := bstep (se 2 (by rfl) ⟨592386, by rfl⟩ : syracuseStep 1579697 = 1184773) B1184773
theorem B1186483 : Blo 1052612 1186483 := bstep (se 1 (by rfl) ⟨889862, by rfl⟩ : syracuseStep 1186483 = 1779725) B1779725
theorem B1055411 : Blo 1052612 1055411 := bstep (se 1 (by rfl) ⟨791558, by rfl⟩ : syracuseStep 1055411 = 1583117) B1583117
theorem B1776323 : Blo 1052612 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B1579715 : Blo 1052612 1579715 := bstep (se 1 (by rfl) ⟨1184786, by rfl⟩ : syracuseStep 1579715 = 2369573) B2369573
theorem B1055427 : Blo 1052612 1055427 := bstep (se 1 (by rfl) ⟨791570, by rfl⟩ : syracuseStep 1055427 = 1583141) B1583141
theorem B1055443 : Blo 1052612 1055443 := bstep (se 1 (by rfl) ⟨791582, by rfl⟩ : syracuseStep 1055443 = 1583165) B1583165
theorem B1579745 : Blo 1052612 1579745 := bstep (se 2 (by rfl) ⟨592404, by rfl⟩ : syracuseStep 1579745 = 1184809) B1184809
theorem B4004579 : Blo 1052612 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B1055459 : Blo 1052612 1055459 := bstep (se 1 (by rfl) ⟨791594, by rfl⟩ : syracuseStep 1055459 = 1583189) B1583189
theorem B3807971 : Blo 1052612 3807971 := bstep (se 1 (by rfl) ⟨2855978, by rfl⟩ : syracuseStep 3807971 = 5711957) B5711957
theorem B1579763 : Blo 1052612 1579763 := bstep (se 1 (by rfl) ⟨1184822, by rfl⟩ : syracuseStep 1579763 = 2369645) B2369645
theorem B1055475 : Blo 1052612 1055475 := bstep (se 1 (by rfl) ⟨791606, by rfl⟩ : syracuseStep 1055475 = 1583213) B1583213
theorem B1055491 : Blo 1052612 1055491 := bstep (se 1 (by rfl) ⟨791618, by rfl⟩ : syracuseStep 1055491 = 1583237) B1583237
theorem B1579793 : Blo 1052612 1579793 := bstep (se 2 (by rfl) ⟨592422, by rfl⟩ : syracuseStep 1579793 = 1184845) B1184845
theorem B1055507 : Blo 1052612 1055507 := bstep (se 1 (by rfl) ⟨791630, by rfl⟩ : syracuseStep 1055507 = 1583261) B1583261
theorem B1579811 : Blo 1052612 1579811 := bstep (se 1 (by rfl) ⟨1184858, by rfl⟩ : syracuseStep 1579811 = 2369717) B2369717
theorem B1055523 : Blo 1052612 1055523 := bstep (se 1 (by rfl) ⟨791642, by rfl⟩ : syracuseStep 1055523 = 1583285) B1583285
theorem B1055539 : Blo 1052612 1055539 := bstep (se 1 (by rfl) ⟨791654, by rfl⟩ : syracuseStep 1055539 = 1583309) B1583309
theorem B1579841 : Blo 1052612 1579841 := bstep (se 2 (by rfl) ⟨592440, by rfl⟩ : syracuseStep 1579841 = 1184881) B1184881
theorem B1776451 : Blo 1052612 1776451 := bstep (se 1 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 1776451 = 2664677) B2664677
theorem B1186627 : Blo 1052612 1186627 := bstep (se 1 (by rfl) ⟨889970, by rfl⟩ : syracuseStep 1186627 = 1779941) B1779941
theorem B1055555 : Blo 1052612 1055555 := bstep (se 1 (by rfl) ⟨791666, by rfl⟩ : syracuseStep 1055555 = 1583333) B1583333
theorem B1579859 : Blo 1052612 1579859 := bstep (se 1 (by rfl) ⟨1184894, by rfl⟩ : syracuseStep 1579859 = 2369789) B2369789
theorem B1055571 : Blo 1052612 1055571 := bstep (se 1 (by rfl) ⟨791678, by rfl⟩ : syracuseStep 1055571 = 1583357) B1583357
theorem B1055587 : Blo 1052612 1055587 := bstep (se 1 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 1055587 = 1583381) B1583381
theorem B2005859 : Blo 1052612 2005859 := bstep (se 1 (by rfl) ⟨1504394, by rfl⟩ : syracuseStep 2005859 = 3008789) B3008789
theorem B1579889 : Blo 1052612 1579889 := bstep (se 2 (by rfl) ⟨592458, by rfl⟩ : syracuseStep 1579889 = 1184917) B1184917
theorem B1055603 : Blo 1052612 1055603 := bstep (se 1 (by rfl) ⟨791702, by rfl⟩ : syracuseStep 1055603 = 1583405) B1583405
theorem B1579907 : Blo 1052612 1579907 := bstep (se 1 (by rfl) ⟨1184930, by rfl⟩ : syracuseStep 1579907 = 2369861) B2369861
theorem B1055619 : Blo 1052612 1055619 := bstep (se 1 (by rfl) ⟨791714, by rfl⟩ : syracuseStep 1055619 = 1583429) B1583429
theorem B1055635 : Blo 1052612 1055635 := bstep (se 1 (by rfl) ⟨791726, by rfl⟩ : syracuseStep 1055635 = 1583453) B1583453
theorem B1579937 : Blo 1052612 1579937 := bstep (se 2 (by rfl) ⟨592476, by rfl⟩ : syracuseStep 1579937 = 1184953) B1184953
theorem B1055651 : Blo 1052612 1055651 := bstep (se 1 (by rfl) ⟨791738, by rfl⟩ : syracuseStep 1055651 = 1583477) B1583477
theorem B1579955 : Blo 1052612 1579955 := bstep (se 1 (by rfl) ⟨1184966, by rfl⟩ : syracuseStep 1579955 = 2369933) B2369933
theorem B1055667 : Blo 1052612 1055667 := bstep (se 1 (by rfl) ⟨791750, by rfl⟩ : syracuseStep 1055667 = 1583501) B1583501
theorem B1055683 : Blo 1052612 1055683 := bstep (se 1 (by rfl) ⟨791762, by rfl⟩ : syracuseStep 1055683 = 1583525) B1583525
theorem B31267781 : Blo 1052612 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B1776593 : Blo 1052612 1776593 := bstep (se 2 (by rfl) ⟨666222, by rfl⟩ : syracuseStep 1776593 = 1332445) B1332445
theorem B1579985 : Blo 1052612 1579985 := bstep (se 2 (by rfl) ⟨592494, by rfl⟩ : syracuseStep 1579985 = 1184989) B1184989
theorem B1186771 : Blo 1052612 1186771 := bstep (se 1 (by rfl) ⟨890078, by rfl⟩ : syracuseStep 1186771 = 1780157) B1780157
theorem B1055699 : Blo 1052612 1055699 := bstep (se 1 (by rfl) ⟨791774, by rfl⟩ : syracuseStep 1055699 = 1583549) B1583549
theorem B1580003 : Blo 1052612 1580003 := bstep (se 1 (by rfl) ⟨1185002, by rfl⟩ : syracuseStep 1580003 = 2370005) B2370005
theorem B1055715 : Blo 1052612 1055715 := bstep (se 1 (by rfl) ⟨791786, by rfl⟩ : syracuseStep 1055715 = 1583573) B1583573
theorem B1055731 : Blo 1052612 1055731 := bstep (se 1 (by rfl) ⟨791798, by rfl⟩ : syracuseStep 1055731 = 1583597) B1583597
theorem B1580033 : Blo 1052612 1580033 := bstep (se 2 (by rfl) ⟨592512, by rfl⟩ : syracuseStep 1580033 = 1185025) B1185025
theorem B1055747 : Blo 1052612 1055747 := bstep (se 1 (by rfl) ⟨791810, by rfl⟩ : syracuseStep 1055747 = 1583621) B1583621
theorem B1580051 : Blo 1052612 1580051 := bstep (se 1 (by rfl) ⟨1185038, by rfl⟩ : syracuseStep 1580051 = 2370077) B2370077
theorem B1055763 : Blo 1052612 1055763 := bstep (se 1 (by rfl) ⟨791822, by rfl⟩ : syracuseStep 1055763 = 1583645) B1583645
theorem B1055779 : Blo 1052612 1055779 := bstep (se 1 (by rfl) ⟨791834, by rfl⟩ : syracuseStep 1055779 = 1583669) B1583669
theorem B1580081 : Blo 1052612 1580081 := bstep (se 2 (by rfl) ⟨592530, by rfl⟩ : syracuseStep 1580081 = 1185061) B1185061
theorem B1055795 : Blo 1052612 1055795 := bstep (se 1 (by rfl) ⟨791846, by rfl⟩ : syracuseStep 1055795 = 1583693) B1583693
theorem B1580099 : Blo 1052612 1580099 := bstep (se 1 (by rfl) ⟨1185074, by rfl⟩ : syracuseStep 1580099 = 2370149) B2370149
theorem B1055811 : Blo 1052612 1055811 := bstep (se 1 (by rfl) ⟨791858, by rfl⟩ : syracuseStep 1055811 = 1583717) B1583717
theorem B5348429 : Blo 1052612 5348429 := bstep (se 3 (by rfl) ⟨1002830, by rfl⟩ : syracuseStep 5348429 = 2005661) B2005661
theorem B1776721 : Blo 1052612 1776721 := bstep (se 2 (by rfl) ⟨666270, by rfl⟩ : syracuseStep 1776721 = 1332541) B1332541
theorem B1055827 : Blo 1052612 1055827 := bstep (se 1 (by rfl) ⟨791870, by rfl⟩ : syracuseStep 1055827 = 1583741) B1583741
theorem B1580129 : Blo 1052612 1580129 := bstep (se 2 (by rfl) ⟨592548, by rfl⟩ : syracuseStep 1580129 = 1185097) B1185097
theorem B1186915 : Blo 1052612 1186915 := bstep (se 1 (by rfl) ⟨890186, by rfl⟩ : syracuseStep 1186915 = 1780373) B1780373
theorem B1055843 : Blo 1052612 1055843 := bstep (se 1 (by rfl) ⟨791882, by rfl⟩ : syracuseStep 1055843 = 1583765) B1583765
theorem B1776755 : Blo 1052612 1776755 := bstep (se 1 (by rfl) ⟨1332566, by rfl⟩ : syracuseStep 1776755 = 2665133) B2665133
theorem B1580147 : Blo 1052612 1580147 := bstep (se 1 (by rfl) ⟨1185110, by rfl⟩ : syracuseStep 1580147 = 2370221) B2370221
theorem B1055859 : Blo 1052612 1055859 := bstep (se 1 (by rfl) ⟨791894, by rfl⟩ : syracuseStep 1055859 = 1583789) B1583789
theorem B1055875 : Blo 1052612 1055875 := bstep (se 1 (by rfl) ⟨791906, by rfl⟩ : syracuseStep 1055875 = 1583813) B1583813
theorem B1580177 : Blo 1052612 1580177 := bstep (se 2 (by rfl) ⟨592566, by rfl⟩ : syracuseStep 1580177 = 1185133) B1185133
theorem B1055891 : Blo 1052612 1055891 := bstep (se 1 (by rfl) ⟨791918, by rfl⟩ : syracuseStep 1055891 = 1583837) B1583837
theorem B1580195 : Blo 1052612 1580195 := bstep (se 1 (by rfl) ⟨1185146, by rfl⟩ : syracuseStep 1580195 = 2370293) B2370293
theorem B1055907 : Blo 1052612 1055907 := bstep (se 1 (by rfl) ⟨791930, by rfl⟩ : syracuseStep 1055907 = 1583861) B1583861
theorem B1055923 : Blo 1052612 1055923 := bstep (se 1 (by rfl) ⟨791942, by rfl⟩ : syracuseStep 1055923 = 1583885) B1583885
theorem B1580225 : Blo 1052612 1580225 := bstep (se 2 (by rfl) ⟨592584, by rfl⟩ : syracuseStep 1580225 = 1185169) B1185169
theorem B1055939 : Blo 1052612 1055939 := bstep (se 1 (by rfl) ⟨791954, by rfl⟩ : syracuseStep 1055939 = 1583909) B1583909
theorem B1580243 : Blo 1052612 1580243 := bstep (se 1 (by rfl) ⟨1185182, by rfl⟩ : syracuseStep 1580243 = 2370365) B2370365
theorem B1055955 : Blo 1052612 1055955 := bstep (se 1 (by rfl) ⟨791966, by rfl⟩ : syracuseStep 1055955 = 1583933) B1583933
theorem B1055971 : Blo 1052612 1055971 := bstep (se 1 (by rfl) ⟨791978, by rfl⟩ : syracuseStep 1055971 = 1583957) B1583957
theorem B1580273 : Blo 1052612 1580273 := bstep (se 2 (by rfl) ⟨592602, by rfl⟩ : syracuseStep 1580273 = 1185205) B1185205
theorem B6003953 : Blo 1052612 6003953 := bstep (se 2 (by rfl) ⟨2251482, by rfl⟩ : syracuseStep 6003953 = 4502965) B4502965
theorem B1776883 : Blo 1052612 1776883 := bstep (se 1 (by rfl) ⟨1332662, by rfl⟩ : syracuseStep 1776883 = 2665325) B2665325
theorem B1187059 : Blo 1052612 1187059 := bstep (se 1 (by rfl) ⟨890294, by rfl⟩ : syracuseStep 1187059 = 1780589) B1780589
theorem B1055987 : Blo 1052612 1055987 := bstep (se 1 (by rfl) ⟨791990, by rfl⟩ : syracuseStep 1055987 = 1583981) B1583981
theorem B1580291 : Blo 1052612 1580291 := bstep (se 1 (by rfl) ⟨1185218, by rfl⟩ : syracuseStep 1580291 = 2370437) B2370437
theorem B1056003 : Blo 1052612 1056003 := bstep (se 1 (by rfl) ⟨792002, by rfl⟩ : syracuseStep 1056003 = 1584005) B1584005
theorem B1056019 : Blo 1052612 1056019 := bstep (se 1 (by rfl) ⟨792014, by rfl⟩ : syracuseStep 1056019 = 1584029) B1584029
theorem B1580321 : Blo 1052612 1580321 := bstep (se 2 (by rfl) ⟨592620, by rfl⟩ : syracuseStep 1580321 = 1185241) B1185241
theorem B1056035 : Blo 1052612 1056035 := bstep (se 1 (by rfl) ⟨792026, by rfl⟩ : syracuseStep 1056035 = 1584053) B1584053
theorem B1580339 : Blo 1052612 1580339 := bstep (se 1 (by rfl) ⟨1185254, by rfl⟩ : syracuseStep 1580339 = 2370509) B2370509
theorem B1056051 : Blo 1052612 1056051 := bstep (se 1 (by rfl) ⟨792038, by rfl⟩ : syracuseStep 1056051 = 1584077) B1584077
theorem B1056067 : Blo 1052612 1056067 := bstep (se 1 (by rfl) ⟨792050, by rfl⟩ : syracuseStep 1056067 = 1584101) B1584101
theorem B1580369 : Blo 1052612 1580369 := bstep (se 2 (by rfl) ⟨592638, by rfl⟩ : syracuseStep 1580369 = 1185277) B1185277
theorem B1056083 : Blo 1052612 1056083 := bstep (se 1 (by rfl) ⟨792062, by rfl⟩ : syracuseStep 1056083 = 1584125) B1584125
theorem B1580387 : Blo 1052612 1580387 := bstep (se 1 (by rfl) ⟨1185290, by rfl⟩ : syracuseStep 1580387 = 2370581) B2370581
theorem B1056099 : Blo 1052612 1056099 := bstep (se 1 (by rfl) ⟨792074, by rfl⟩ : syracuseStep 1056099 = 1584149) B1584149
theorem B4005233 : Blo 1052612 4005233 := bstep (se 2 (by rfl) ⟨1501962, by rfl⟩ : syracuseStep 4005233 = 3003925) B3003925
theorem B1056115 : Blo 1052612 1056115 := bstep (se 1 (by rfl) ⟨792086, by rfl⟩ : syracuseStep 1056115 = 1584173) B1584173
theorem B1777025 : Blo 1052612 1777025 := bstep (se 2 (by rfl) ⟨666384, by rfl⟩ : syracuseStep 1777025 = 1332769) B1332769
theorem B1580417 : Blo 1052612 1580417 := bstep (se 2 (by rfl) ⟨592656, by rfl⟩ : syracuseStep 1580417 = 1185313) B1185313
theorem B1187203 : Blo 1052612 1187203 := bstep (se 1 (by rfl) ⟨890402, by rfl⟩ : syracuseStep 1187203 = 1780805) B1780805
theorem B1056131 : Blo 1052612 1056131 := bstep (se 1 (by rfl) ⟨792098, by rfl⟩ : syracuseStep 1056131 = 1584197) B1584197
theorem B1580435 : Blo 1052612 1580435 := bstep (se 1 (by rfl) ⟨1185326, by rfl⟩ : syracuseStep 1580435 = 2370653) B2370653
theorem B1056147 : Blo 1052612 1056147 := bstep (se 1 (by rfl) ⟨792110, by rfl⟩ : syracuseStep 1056147 = 1584221) B1584221
theorem B1056163 : Blo 1052612 1056163 := bstep (se 1 (by rfl) ⟨792122, by rfl⟩ : syracuseStep 1056163 = 1584245) B1584245
theorem B1580465 : Blo 1052612 1580465 := bstep (se 2 (by rfl) ⟨592674, by rfl⟩ : syracuseStep 1580465 = 1185349) B1185349
theorem B1056179 : Blo 1052612 1056179 := bstep (se 1 (by rfl) ⟨792134, by rfl⟩ : syracuseStep 1056179 = 1584269) B1584269
theorem B1580483 : Blo 1052612 1580483 := bstep (se 1 (by rfl) ⟨1185362, by rfl⟩ : syracuseStep 1580483 = 2370725) B2370725
theorem B1056195 : Blo 1052612 1056195 := bstep (se 1 (by rfl) ⟨792146, by rfl⟩ : syracuseStep 1056195 = 1584293) B1584293
theorem B1056211 : Blo 1052612 1056211 := bstep (se 1 (by rfl) ⟨792158, by rfl⟩ : syracuseStep 1056211 = 1584317) B1584317
theorem B1580513 : Blo 1052612 1580513 := bstep (se 2 (by rfl) ⟨592692, by rfl⟩ : syracuseStep 1580513 = 1185385) B1185385
theorem B4496867 : Blo 1052612 4496867 := bstep (se 1 (by rfl) ⟨3372650, by rfl⟩ : syracuseStep 4496867 = 6745301) B6745301
theorem B1056227 : Blo 1052612 1056227 := bstep (se 1 (by rfl) ⟨792170, by rfl⟩ : syracuseStep 1056227 = 1584341) B1584341
theorem B1580531 : Blo 1052612 1580531 := bstep (se 1 (by rfl) ⟨1185398, by rfl⟩ : syracuseStep 1580531 = 2370797) B2370797
theorem B1056243 : Blo 1052612 1056243 := bstep (se 1 (by rfl) ⟨792182, by rfl⟩ : syracuseStep 1056243 = 1584365) B1584365
theorem B1777153 : Blo 1052612 1777153 := bstep (se 2 (by rfl) ⟨666432, by rfl⟩ : syracuseStep 1777153 = 1332865) B1332865
theorem B1056259 : Blo 1052612 1056259 := bstep (se 1 (by rfl) ⟨792194, by rfl⟩ : syracuseStep 1056259 = 1584389) B1584389
theorem B1580561 : Blo 1052612 1580561 := bstep (se 2 (by rfl) ⟨592710, by rfl⟩ : syracuseStep 1580561 = 1185421) B1185421
theorem B1187347 : Blo 1052612 1187347 := bstep (se 1 (by rfl) ⟨890510, by rfl⟩ : syracuseStep 1187347 = 1781021) B1781021
theorem B1056275 : Blo 1052612 1056275 := bstep (se 1 (by rfl) ⟨792206, by rfl⟩ : syracuseStep 1056275 = 1584413) B1584413
theorem B1777187 : Blo 1052612 1777187 := bstep (se 1 (by rfl) ⟨1332890, by rfl⟩ : syracuseStep 1777187 = 2665781) B2665781
theorem B1580579 : Blo 1052612 1580579 := bstep (se 1 (by rfl) ⟨1185434, by rfl⟩ : syracuseStep 1580579 = 2370869) B2370869
theorem B1056291 : Blo 1052612 1056291 := bstep (se 1 (by rfl) ⟨792218, by rfl⟩ : syracuseStep 1056291 = 1584437) B1584437
theorem B1056307 : Blo 1052612 1056307 := bstep (se 1 (by rfl) ⟨792230, by rfl⟩ : syracuseStep 1056307 = 1584461) B1584461
theorem B1580609 : Blo 1052612 1580609 := bstep (se 2 (by rfl) ⟨592728, by rfl⟩ : syracuseStep 1580609 = 1185457) B1185457
theorem B1056323 : Blo 1052612 1056323 := bstep (se 1 (by rfl) ⟨792242, by rfl⟩ : syracuseStep 1056323 = 1584485) B1584485
theorem B1580627 : Blo 1052612 1580627 := bstep (se 1 (by rfl) ⟨1185470, by rfl⟩ : syracuseStep 1580627 = 2370941) B2370941
theorem B1056339 : Blo 1052612 1056339 := bstep (se 1 (by rfl) ⟨792254, by rfl⟩ : syracuseStep 1056339 = 1584509) B1584509
theorem B1056355 : Blo 1052612 1056355 := bstep (se 1 (by rfl) ⟨792266, by rfl⟩ : syracuseStep 1056355 = 1584533) B1584533
theorem B1580657 : Blo 1052612 1580657 := bstep (se 2 (by rfl) ⟨592746, by rfl⟩ : syracuseStep 1580657 = 1185493) B1185493
theorem B1056371 : Blo 1052612 1056371 := bstep (se 1 (by rfl) ⟨792278, by rfl⟩ : syracuseStep 1056371 = 1584557) B1584557
theorem B1580675 : Blo 1052612 1580675 := bstep (se 1 (by rfl) ⟨1185506, by rfl⟩ : syracuseStep 1580675 = 2371013) B2371013
theorem B1056387 : Blo 1052612 1056387 := bstep (se 1 (by rfl) ⟨792290, by rfl⟩ : syracuseStep 1056387 = 1584581) B1584581
theorem B1056403 : Blo 1052612 1056403 := bstep (se 1 (by rfl) ⟨792302, by rfl⟩ : syracuseStep 1056403 = 1584605) B1584605
theorem B1580705 : Blo 1052612 1580705 := bstep (se 2 (by rfl) ⟨592764, by rfl⟩ : syracuseStep 1580705 = 1185529) B1185529
theorem B1777315 : Blo 1052612 1777315 := bstep (se 1 (by rfl) ⟨1332986, by rfl⟩ : syracuseStep 1777315 = 2665973) B2665973
theorem B1187491 : Blo 1052612 1187491 := bstep (se 1 (by rfl) ⟨890618, by rfl⟩ : syracuseStep 1187491 = 1781237) B1781237
theorem B1056419 : Blo 1052612 1056419 := bstep (se 1 (by rfl) ⟨792314, by rfl⟩ : syracuseStep 1056419 = 1584629) B1584629
theorem B1580723 : Blo 1052612 1580723 := bstep (se 1 (by rfl) ⟨1185542, by rfl⟩ : syracuseStep 1580723 = 2371085) B2371085
theorem B1056435 : Blo 1052612 1056435 := bstep (se 1 (by rfl) ⟨792326, by rfl⟩ : syracuseStep 1056435 = 1584653) B1584653
theorem B1056451 : Blo 1052612 1056451 := bstep (se 1 (by rfl) ⟨792338, by rfl⟩ : syracuseStep 1056451 = 1584677) B1584677
theorem B1580753 : Blo 1052612 1580753 := bstep (se 2 (by rfl) ⟨592782, by rfl⟩ : syracuseStep 1580753 = 1185565) B1185565
theorem B1056467 : Blo 1052612 1056467 := bstep (se 1 (by rfl) ⟨792350, by rfl⟩ : syracuseStep 1056467 = 1584701) B1584701
theorem B1580771 : Blo 1052612 1580771 := bstep (se 1 (by rfl) ⟨1185578, by rfl⟩ : syracuseStep 1580771 = 2371157) B2371157
theorem B1056483 : Blo 1052612 1056483 := bstep (se 1 (by rfl) ⟨792362, by rfl⟩ : syracuseStep 1056483 = 1584725) B1584725
theorem B1056499 : Blo 1052612 1056499 := bstep (se 1 (by rfl) ⟨792374, by rfl⟩ : syracuseStep 1056499 = 1584749) B1584749
theorem B1580801 : Blo 1052612 1580801 := bstep (se 2 (by rfl) ⟨592800, by rfl⟩ : syracuseStep 1580801 = 1185601) B1185601
theorem B1056515 : Blo 1052612 1056515 := bstep (se 1 (by rfl) ⟨792386, by rfl⟩ : syracuseStep 1056515 = 1584773) B1584773
theorem B5414669 : Blo 1052612 5414669 := bstep (se 3 (by rfl) ⟨1015250, by rfl⟩ : syracuseStep 5414669 = 2030501) B2030501
theorem B1580819 : Blo 1052612 1580819 := bstep (se 1 (by rfl) ⟨1185614, by rfl⟩ : syracuseStep 1580819 = 2371229) B2371229
theorem B1056531 : Blo 1052612 1056531 := bstep (se 1 (by rfl) ⟨792398, by rfl⟩ : syracuseStep 1056531 = 1584797) B1584797
theorem B1056547 : Blo 1052612 1056547 := bstep (se 1 (by rfl) ⟨792410, by rfl⟩ : syracuseStep 1056547 = 1584821) B1584821
theorem B1777457 : Blo 1052612 1777457 := bstep (se 2 (by rfl) ⟨666546, by rfl⟩ : syracuseStep 1777457 = 1333093) B1333093
theorem B1580849 : Blo 1052612 1580849 := bstep (se 2 (by rfl) ⟨592818, by rfl⟩ : syracuseStep 1580849 = 1185637) B1185637
theorem B1187635 : Blo 1052612 1187635 := bstep (se 1 (by rfl) ⟨890726, by rfl⟩ : syracuseStep 1187635 = 1781453) B1781453
theorem B1056563 : Blo 1052612 1056563 := bstep (se 1 (by rfl) ⟨792422, by rfl⟩ : syracuseStep 1056563 = 1584845) B1584845
theorem B1580867 : Blo 1052612 1580867 := bstep (se 1 (by rfl) ⟨1185650, by rfl⟩ : syracuseStep 1580867 = 2371301) B2371301
theorem B1056579 : Blo 1052612 1056579 := bstep (se 1 (by rfl) ⟨792434, by rfl⟩ : syracuseStep 1056579 = 1584869) B1584869
theorem B1056595 : Blo 1052612 1056595 := bstep (se 1 (by rfl) ⟨792446, by rfl⟩ : syracuseStep 1056595 = 1584893) B1584893
theorem B1580897 : Blo 1052612 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B1056611 : Blo 1052612 1056611 := bstep (se 1 (by rfl) ⟨792458, by rfl⟩ : syracuseStep 1056611 = 1584917) B1584917
theorem B1580915 : Blo 1052612 1580915 := bstep (se 1 (by rfl) ⟨1185686, by rfl⟩ : syracuseStep 1580915 = 2371373) B2371373
theorem B3383171 : Blo 1052612 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B1580945 : Blo 1052612 1580945 := bstep (se 2 (by rfl) ⟨592854, by rfl⟩ : syracuseStep 1580945 = 1185709) B1185709
theorem B1580963 : Blo 1052612 1580963 := bstep (se 1 (by rfl) ⟨1185722, by rfl⟩ : syracuseStep 1580963 = 2371445) B2371445
theorem B1777585 : Blo 1052612 1777585 := bstep (se 2 (by rfl) ⟨666594, by rfl⟩ : syracuseStep 1777585 = 1333189) B1333189
theorem B1580993 : Blo 1052612 1580993 := bstep (se 2 (by rfl) ⟨592872, by rfl⟩ : syracuseStep 1580993 = 1185745) B1185745
theorem B1187779 : Blo 1052612 1187779 := bstep (se 1 (by rfl) ⟨890834, by rfl⟩ : syracuseStep 1187779 = 1781669) B1781669
theorem B1777619 : Blo 1052612 1777619 := bstep (se 1 (by rfl) ⟨1333214, by rfl⟩ : syracuseStep 1777619 = 2666429) B2666429
theorem B1581011 : Blo 1052612 1581011 := bstep (se 1 (by rfl) ⟨1185758, by rfl⟩ : syracuseStep 1581011 = 2371517) B2371517
theorem B1581041 : Blo 1052612 1581041 := bstep (se 2 (by rfl) ⟨592890, by rfl⟩ : syracuseStep 1581041 = 1185781) B1185781
theorem B1581059 : Blo 1052612 1581059 := bstep (se 1 (by rfl) ⟨1185794, by rfl⟩ : syracuseStep 1581059 = 2371589) B2371589
theorem B1581089 : Blo 1052612 1581089 := bstep (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) B1185817
theorem B1581107 : Blo 1052612 1581107 := bstep (se 1 (by rfl) ⟨1185830, by rfl⟩ : syracuseStep 1581107 = 2371661) B2371661
theorem B1581137 : Blo 1052612 1581137 := bstep (se 2 (by rfl) ⟨592926, by rfl⟩ : syracuseStep 1581137 = 1185853) B1185853
theorem B1777747 : Blo 1052612 1777747 := bstep (se 1 (by rfl) ⟨1333310, by rfl⟩ : syracuseStep 1777747 = 2666621) B2666621
theorem B1187923 : Blo 1052612 1187923 := bstep (se 1 (by rfl) ⟨890942, by rfl⟩ : syracuseStep 1187923 = 1781885) B1781885
theorem B1581155 : Blo 1052612 1581155 := bstep (se 1 (by rfl) ⟨1185866, by rfl⟩ : syracuseStep 1581155 = 2371733) B2371733
theorem B1581185 : Blo 1052612 1581185 := bstep (se 2 (by rfl) ⟨592944, by rfl⟩ : syracuseStep 1581185 = 1185889) B1185889
theorem B1581203 : Blo 1052612 1581203 := bstep (se 1 (by rfl) ⟨1185902, by rfl⟩ : syracuseStep 1581203 = 2371805) B2371805
theorem B1581233 : Blo 1052612 1581233 := bstep (se 2 (by rfl) ⟨592962, by rfl⟩ : syracuseStep 1581233 = 1185925) B1185925
theorem B1581251 : Blo 1052612 1581251 := bstep (se 1 (by rfl) ⟨1185938, by rfl⟩ : syracuseStep 1581251 = 2371877) B2371877
theorem B2171075 : Blo 1052612 2171075 := bstep (se 1 (by rfl) ⟨1628306, by rfl⟩ : syracuseStep 2171075 = 3256613) B3256613
theorem B1777889 : Blo 1052612 1777889 := bstep (se 2 (by rfl) ⟨666708, by rfl⟩ : syracuseStep 1777889 = 1333417) B1333417
theorem B1581281 : Blo 1052612 1581281 := bstep (se 2 (by rfl) ⟨592980, by rfl⟩ : syracuseStep 1581281 = 1185961) B1185961
theorem B9248995 : Blo 1052612 9248995 := bstep (se 1 (by rfl) ⟨6936746, by rfl⟩ : syracuseStep 9248995 = 13873493) B13873493
theorem B1188067 : Blo 1052612 1188067 := bstep (se 1 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 1188067 = 1782101) B1782101
theorem B1581299 : Blo 1052612 1581299 := bstep (se 1 (by rfl) ⟨1185974, by rfl⟩ : syracuseStep 1581299 = 2371949) B2371949
theorem B1581329 : Blo 1052612 1581329 := bstep (se 2 (by rfl) ⟨592998, by rfl⟩ : syracuseStep 1581329 = 1185997) B1185997
theorem B1581347 : Blo 1052612 1581347 := bstep (se 1 (by rfl) ⟨1186010, by rfl⟩ : syracuseStep 1581347 = 2372021) B2372021
theorem B1581377 : Blo 1052612 1581377 := bstep (se 2 (by rfl) ⟨593016, by rfl⟩ : syracuseStep 1581377 = 1186033) B1186033
theorem B1581395 : Blo 1052612 1581395 := bstep (se 1 (by rfl) ⟨1186046, by rfl⟩ : syracuseStep 1581395 = 2372093) B2372093
theorem B1778017 : Blo 1052612 1778017 := bstep (se 2 (by rfl) ⟨666756, by rfl⟩ : syracuseStep 1778017 = 1333513) B1333513
theorem B1581425 : Blo 1052612 1581425 := bstep (se 2 (by rfl) ⟨593034, by rfl⟩ : syracuseStep 1581425 = 1186069) B1186069
theorem B1188211 : Blo 1052612 1188211 := bstep (se 1 (by rfl) ⟨891158, by rfl⟩ : syracuseStep 1188211 = 1782317) B1782317
theorem B1778051 : Blo 1052612 1778051 := bstep (se 1 (by rfl) ⟨1333538, by rfl⟩ : syracuseStep 1778051 = 2667077) B2667077
theorem B1581443 : Blo 1052612 1581443 := bstep (se 1 (by rfl) ⟨1186082, by rfl⟩ : syracuseStep 1581443 = 2372165) B2372165
theorem B1581473 : Blo 1052612 1581473 := bstep (se 2 (by rfl) ⟨593052, by rfl⟩ : syracuseStep 1581473 = 1186105) B1186105
theorem B1581491 : Blo 1052612 1581491 := bstep (se 1 (by rfl) ⟨1186118, by rfl⟩ : syracuseStep 1581491 = 2372237) B2372237
theorem B1581521 : Blo 1052612 1581521 := bstep (se 2 (by rfl) ⟨593070, by rfl⟩ : syracuseStep 1581521 = 1186141) B1186141
theorem B1581539 : Blo 1052612 1581539 := bstep (se 1 (by rfl) ⟨1186154, by rfl⟩ : syracuseStep 1581539 = 2372309) B2372309
theorem B1581569 : Blo 1052612 1581569 := bstep (se 2 (by rfl) ⟨593088, by rfl⟩ : syracuseStep 1581569 = 1186177) B1186177
theorem B1778179 : Blo 1052612 1778179 := bstep (se 1 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 1778179 = 2667269) B2667269
theorem B2531843 : Blo 1052612 2531843 := bstep (se 1 (by rfl) ⟨1898882, by rfl⟩ : syracuseStep 2531843 = 3797765) B3797765
theorem B1188355 : Blo 1052612 1188355 := bstep (se 1 (by rfl) ⟨891266, by rfl⟩ : syracuseStep 1188355 = 1782533) B1782533
theorem B1581587 : Blo 1052612 1581587 := bstep (se 1 (by rfl) ⟨1186190, by rfl⟩ : syracuseStep 1581587 = 2372381) B2372381
theorem B25960981 : Blo 1052612 25960981 := bstep (se 6 (by rfl) ⟨608460, by rfl⟩ : syracuseStep 25960981 = 1216921) B1216921
theorem B1581617 : Blo 1052612 1581617 := bstep (se 2 (by rfl) ⟨593106, by rfl⟩ : syracuseStep 1581617 = 1186213) B1186213
theorem B1581635 : Blo 1052612 1581635 := bstep (se 1 (by rfl) ⟨1186226, by rfl⟩ : syracuseStep 1581635 = 2372453) B2372453
theorem B1581665 : Blo 1052612 1581665 := bstep (se 2 (by rfl) ⟨593124, by rfl⟩ : syracuseStep 1581665 = 1186249) B1186249
theorem B1581683 : Blo 1052612 1581683 := bstep (se 1 (by rfl) ⟨1186262, by rfl⟩ : syracuseStep 1581683 = 2372525) B2372525
theorem B3383939 : Blo 1052612 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B1778321 : Blo 1052612 1778321 := bstep (se 2 (by rfl) ⟨666870, by rfl⟩ : syracuseStep 1778321 = 1333741) B1333741
theorem B1581713 : Blo 1052612 1581713 := bstep (se 2 (by rfl) ⟨593142, by rfl⟩ : syracuseStep 1581713 = 1186285) B1186285
theorem B1188499 : Blo 1052612 1188499 := bstep (se 1 (by rfl) ⟨891374, by rfl⟩ : syracuseStep 1188499 = 1782749) B1782749
theorem B6005411 : Blo 1052612 6005411 := bstep (se 1 (by rfl) ⟨4504058, by rfl⟩ : syracuseStep 6005411 = 9008117) B9008117
theorem B1581731 : Blo 1052612 1581731 := bstep (se 1 (by rfl) ⟨1186298, by rfl⟩ : syracuseStep 1581731 = 2372597) B2372597
theorem B1581761 : Blo 1052612 1581761 := bstep (se 2 (by rfl) ⟨593160, by rfl⟩ : syracuseStep 1581761 = 1186321) B1186321
theorem B1581779 : Blo 1052612 1581779 := bstep (se 1 (by rfl) ⟨1186334, by rfl⟩ : syracuseStep 1581779 = 2372669) B2372669
theorem B4268785 : Blo 1052612 4268785 := bstep (se 2 (by rfl) ⟨1600794, by rfl⟩ : syracuseStep 4268785 = 3201589) B3201589
theorem B1581809 : Blo 1052612 1581809 := bstep (se 2 (by rfl) ⟨593178, by rfl⟩ : syracuseStep 1581809 = 1186357) B1186357
theorem B1581827 : Blo 1052612 1581827 := bstep (se 1 (by rfl) ⟨1186370, by rfl⟩ : syracuseStep 1581827 = 2372741) B2372741
theorem B1778449 : Blo 1052612 1778449 := bstep (se 2 (by rfl) ⟨666918, by rfl⟩ : syracuseStep 1778449 = 1333837) B1333837
theorem B1581857 : Blo 1052612 1581857 := bstep (se 2 (by rfl) ⟨593196, by rfl⟩ : syracuseStep 1581857 = 1186393) B1186393
theorem B2532131 : Blo 1052612 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B4006691 : Blo 1052612 4006691 := bstep (se 1 (by rfl) ⟨3005018, by rfl⟩ : syracuseStep 4006691 = 6010037) B6010037
theorem B1188643 : Blo 1052612 1188643 := bstep (se 1 (by rfl) ⟨891482, by rfl⟩ : syracuseStep 1188643 = 1782965) B1782965
theorem B4006705 : Blo 1052612 4006705 := bstep (se 2 (by rfl) ⟨1502514, by rfl⟩ : syracuseStep 4006705 = 3005029) B3005029
theorem B1778483 : Blo 1052612 1778483 := bstep (se 1 (by rfl) ⟨1333862, by rfl⟩ : syracuseStep 1778483 = 2667725) B2667725
theorem B1581875 : Blo 1052612 1581875 := bstep (se 1 (by rfl) ⟨1186406, by rfl⟩ : syracuseStep 1581875 = 2372813) B2372813
theorem B1581905 : Blo 1052612 1581905 := bstep (se 2 (by rfl) ⟨593214, by rfl⟩ : syracuseStep 1581905 = 1186429) B1186429
theorem B1581923 : Blo 1052612 1581923 := bstep (se 1 (by rfl) ⟨1186442, by rfl⟩ : syracuseStep 1581923 = 2372885) B2372885
theorem B1581953 : Blo 1052612 1581953 := bstep (se 2 (by rfl) ⟨593232, by rfl⟩ : syracuseStep 1581953 = 1186465) B1186465
theorem B1581971 : Blo 1052612 1581971 := bstep (se 1 (by rfl) ⟨1186478, by rfl⟩ : syracuseStep 1581971 = 2372957) B2372957
theorem B1582001 : Blo 1052612 1582001 := bstep (se 2 (by rfl) ⟨593250, by rfl⟩ : syracuseStep 1582001 = 1186501) B1186501
theorem B1778611 : Blo 1052612 1778611 := bstep (se 1 (by rfl) ⟨1333958, by rfl⟩ : syracuseStep 1778611 = 2667917) B2667917
theorem B1582019 : Blo 1052612 1582019 := bstep (se 1 (by rfl) ⟨1186514, by rfl⟩ : syracuseStep 1582019 = 2373029) B2373029
theorem B1582049 : Blo 1052612 1582049 := bstep (se 2 (by rfl) ⟨593268, by rfl⟩ : syracuseStep 1582049 = 1186537) B1186537
theorem B1582067 : Blo 1052612 1582067 := bstep (se 1 (by rfl) ⟨1186550, by rfl⟩ : syracuseStep 1582067 = 2373101) B2373101
theorem B2368529 : Blo 1052612 2368529 := bstep (se 2 (by rfl) ⟨888198, by rfl⟩ : syracuseStep 2368529 = 1776397) B1776397
theorem B1582097 : Blo 1052612 1582097 := bstep (se 2 (by rfl) ⟨593286, by rfl⟩ : syracuseStep 1582097 = 1186573) B1186573
theorem B3384337 : Blo 1052612 3384337 := bstep (se 2 (by rfl) ⟨1269126, by rfl⟩ : syracuseStep 3384337 = 2538253) B2538253
theorem B2368547 : Blo 1052612 2368547 := bstep (se 1 (by rfl) ⟨1776410, by rfl⟩ : syracuseStep 2368547 = 3552821) B3552821
theorem B1582115 : Blo 1052612 1582115 := bstep (se 1 (by rfl) ⟨1186586, by rfl⟩ : syracuseStep 1582115 = 2373173) B2373173
theorem B1778753 : Blo 1052612 1778753 := bstep (se 2 (by rfl) ⟨667032, by rfl⟩ : syracuseStep 1778753 = 1334065) B1334065
theorem B1582145 : Blo 1052612 1582145 := bstep (se 2 (by rfl) ⟨593304, by rfl⟩ : syracuseStep 1582145 = 1186609) B1186609
theorem B1582163 : Blo 1052612 1582163 := bstep (se 1 (by rfl) ⟨1186622, by rfl⟩ : syracuseStep 1582163 = 2373245) B2373245
theorem B1582193 : Blo 1052612 1582193 := bstep (se 2 (by rfl) ⟨593322, by rfl⟩ : syracuseStep 1582193 = 1186645) B1186645
theorem B1582211 : Blo 1052612 1582211 := bstep (se 1 (by rfl) ⟨1186658, by rfl⟩ : syracuseStep 1582211 = 2373317) B2373317
theorem B3384451 : Blo 1052612 3384451 := bstep (se 1 (by rfl) ⟨2538338, by rfl⟩ : syracuseStep 3384451 = 5076677) B5076677
theorem B1582241 : Blo 1052612 1582241 := bstep (se 2 (by rfl) ⟨593340, by rfl⟩ : syracuseStep 1582241 = 1186681) B1186681
theorem B1582259 : Blo 1052612 1582259 := bstep (se 1 (by rfl) ⟨1186694, by rfl⟩ : syracuseStep 1582259 = 2373389) B2373389
theorem B1778881 : Blo 1052612 1778881 := bstep (se 2 (by rfl) ⟨667080, by rfl⟩ : syracuseStep 1778881 = 1334161) B1334161
theorem B1582289 : Blo 1052612 1582289 := bstep (se 2 (by rfl) ⟨593358, by rfl⟩ : syracuseStep 1582289 = 1186717) B1186717
theorem B1778915 : Blo 1052612 1778915 := bstep (se 1 (by rfl) ⟨1334186, by rfl⟩ : syracuseStep 1778915 = 2668373) B2668373
theorem B1582307 : Blo 1052612 1582307 := bstep (se 1 (by rfl) ⟨1186730, by rfl⟩ : syracuseStep 1582307 = 2373461) B2373461
theorem B5711089 : Blo 1052612 5711089 := bstep (se 2 (by rfl) ⟨2141658, by rfl⟩ : syracuseStep 5711089 = 4283317) B4283317
theorem B1582337 : Blo 1052612 1582337 := bstep (se 2 (by rfl) ⟨593376, by rfl⟩ : syracuseStep 1582337 = 1186753) B1186753
theorem B1582355 : Blo 1052612 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B2368817 : Blo 1052612 2368817 := bstep (se 2 (by rfl) ⟨888306, by rfl⟩ : syracuseStep 2368817 = 1776613) B1776613
theorem B1582385 : Blo 1052612 1582385 := bstep (se 2 (by rfl) ⟨593394, by rfl⟩ : syracuseStep 1582385 = 1186789) B1186789
theorem B2368835 : Blo 1052612 2368835 := bstep (se 1 (by rfl) ⟨1776626, by rfl⟩ : syracuseStep 2368835 = 3553253) B3553253
theorem B1582403 : Blo 1052612 1582403 := bstep (se 1 (by rfl) ⟨1186802, by rfl⟩ : syracuseStep 1582403 = 2373605) B2373605
theorem B1582433 : Blo 1052612 1582433 := bstep (se 2 (by rfl) ⟨593412, by rfl⟩ : syracuseStep 1582433 = 1186825) B1186825
theorem B1779043 : Blo 1052612 1779043 := bstep (se 1 (by rfl) ⟨1334282, by rfl⟩ : syracuseStep 1779043 = 2668565) B2668565
theorem B1582451 : Blo 1052612 1582451 := bstep (se 1 (by rfl) ⟨1186838, by rfl⟩ : syracuseStep 1582451 = 2373677) B2373677
theorem B1582481 : Blo 1052612 1582481 := bstep (se 2 (by rfl) ⟨593430, by rfl⟩ : syracuseStep 1582481 = 1186861) B1186861
theorem B1582499 : Blo 1052612 1582499 := bstep (se 1 (by rfl) ⟨1186874, by rfl⟩ : syracuseStep 1582499 = 2373749) B2373749
theorem B4498865 : Blo 1052612 4498865 := bstep (se 2 (by rfl) ⟨1687074, by rfl⟩ : syracuseStep 4498865 = 3374149) B3374149
theorem B1582529 : Blo 1052612 1582529 := bstep (se 2 (by rfl) ⟨593448, by rfl⟩ : syracuseStep 1582529 = 1186897) B1186897
theorem B1353155 : Blo 1052612 1353155 := bstep (se 1 (by rfl) ⟨1014866, by rfl⟩ : syracuseStep 1353155 = 2029733) B2029733
theorem B1582547 : Blo 1052612 1582547 := bstep (se 1 (by rfl) ⟨1186910, by rfl⟩ : syracuseStep 1582547 = 2373821) B2373821
theorem B1779185 : Blo 1052612 1779185 := bstep (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) B1334389
theorem B1582577 : Blo 1052612 1582577 := bstep (se 2 (by rfl) ⟨593466, by rfl⟩ : syracuseStep 1582577 = 1186933) B1186933
theorem B1582595 : Blo 1052612 1582595 := bstep (se 1 (by rfl) ⟨1186946, by rfl⟩ : syracuseStep 1582595 = 2373893) B2373893
theorem B1582625 : Blo 1052612 1582625 := bstep (se 2 (by rfl) ⟨593484, by rfl⟩ : syracuseStep 1582625 = 1186969) B1186969
theorem B1582643 : Blo 1052612 1582643 := bstep (se 1 (by rfl) ⟨1186982, by rfl⟩ : syracuseStep 1582643 = 2373965) B2373965
theorem B2369105 : Blo 1052612 2369105 := bstep (se 2 (by rfl) ⟨888414, by rfl⟩ : syracuseStep 2369105 = 1776829) B1776829
theorem B1582673 : Blo 1052612 1582673 := bstep (se 2 (by rfl) ⟨593502, by rfl⟩ : syracuseStep 1582673 = 1187005) B1187005
theorem B2369123 : Blo 1052612 2369123 := bstep (se 1 (by rfl) ⟨1776842, by rfl⟩ : syracuseStep 2369123 = 3553685) B3553685
theorem B1582691 : Blo 1052612 1582691 := bstep (se 1 (by rfl) ⟨1187018, by rfl⟩ : syracuseStep 1582691 = 2374037) B2374037
theorem B1779313 : Blo 1052612 1779313 := bstep (se 2 (by rfl) ⟨667242, by rfl⟩ : syracuseStep 1779313 = 1334485) B1334485
theorem B1582721 : Blo 1052612 1582721 := bstep (se 2 (by rfl) ⟨593520, by rfl⟩ : syracuseStep 1582721 = 1187041) B1187041
theorem B6006413 : Blo 1052612 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B1779347 : Blo 1052612 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B1582739 : Blo 1052612 1582739 := bstep (se 1 (by rfl) ⟨1187054, by rfl⟩ : syracuseStep 1582739 = 2374109) B2374109
theorem B1582769 : Blo 1052612 1582769 := bstep (se 2 (by rfl) ⟨593538, by rfl⟩ : syracuseStep 1582769 = 1187077) B1187077
theorem B1582787 : Blo 1052612 1582787 := bstep (se 1 (by rfl) ⟨1187090, by rfl⟩ : syracuseStep 1582787 = 2374181) B2374181
theorem B1582817 : Blo 1052612 1582817 := bstep (se 2 (by rfl) ⟨593556, by rfl⟩ : syracuseStep 1582817 = 1187113) B1187113
theorem B1582835 : Blo 1052612 1582835 := bstep (se 1 (by rfl) ⟨1187126, by rfl⟩ : syracuseStep 1582835 = 2374253) B2374253
theorem B1582865 : Blo 1052612 1582865 := bstep (se 2 (by rfl) ⟨593574, by rfl⟩ : syracuseStep 1582865 = 1187149) B1187149
theorem B1779475 : Blo 1052612 1779475 := bstep (se 1 (by rfl) ⟨1334606, by rfl⟩ : syracuseStep 1779475 = 2669213) B2669213
theorem B1582883 : Blo 1052612 1582883 := bstep (se 1 (by rfl) ⟨1187162, by rfl⟩ : syracuseStep 1582883 = 2374325) B2374325
theorem B1582913 : Blo 1052612 1582913 := bstep (se 2 (by rfl) ⟨593592, by rfl⟩ : syracuseStep 1582913 = 1187185) B1187185
theorem B1582931 : Blo 1052612 1582931 := bstep (se 1 (by rfl) ⟨1187198, by rfl⟩ : syracuseStep 1582931 = 2374397) B2374397
theorem B2369393 : Blo 1052612 2369393 := bstep (se 2 (by rfl) ⟨888522, by rfl⟩ : syracuseStep 2369393 = 1777045) B1777045
theorem B1582961 : Blo 1052612 1582961 := bstep (se 2 (by rfl) ⟨593610, by rfl⟩ : syracuseStep 1582961 = 1187221) B1187221
theorem B2369411 : Blo 1052612 2369411 := bstep (se 1 (by rfl) ⟨1777058, by rfl⟩ : syracuseStep 2369411 = 3554117) B3554117
theorem B1582979 : Blo 1052612 1582979 := bstep (se 1 (by rfl) ⟨1187234, by rfl⟩ : syracuseStep 1582979 = 2374469) B2374469
theorem B1779617 : Blo 1052612 1779617 := bstep (se 2 (by rfl) ⟨667356, by rfl⟩ : syracuseStep 1779617 = 1334713) B1334713
theorem B1583009 : Blo 1052612 1583009 := bstep (se 2 (by rfl) ⟨593628, by rfl⟩ : syracuseStep 1583009 = 1187257) B1187257
theorem B1583027 : Blo 1052612 1583027 := bstep (se 1 (by rfl) ⟨1187270, by rfl⟩ : syracuseStep 1583027 = 2374541) B2374541
theorem B1583057 : Blo 1052612 1583057 := bstep (se 2 (by rfl) ⟨593646, by rfl⟩ : syracuseStep 1583057 = 1187293) B1187293
theorem B1124323 : Blo 1052612 1124323 := bstep (se 1 (by rfl) ⟨843242, by rfl⟩ : syracuseStep 1124323 = 1686485) B1686485
theorem B1583075 : Blo 1052612 1583075 := bstep (se 1 (by rfl) ⟨1187306, by rfl⟩ : syracuseStep 1583075 = 2374613) B2374613
theorem B1583105 : Blo 1052612 1583105 := bstep (se 2 (by rfl) ⟨593664, by rfl⟩ : syracuseStep 1583105 = 1187329) B1187329
theorem B1583123 : Blo 1052612 1583123 := bstep (se 1 (by rfl) ⟨1187342, by rfl⟩ : syracuseStep 1583123 = 2374685) B2374685
theorem B1779745 : Blo 1052612 1779745 := bstep (se 2 (by rfl) ⟨667404, by rfl⟩ : syracuseStep 1779745 = 1334809) B1334809
theorem B1583153 : Blo 1052612 1583153 := bstep (se 2 (by rfl) ⟨593682, by rfl⟩ : syracuseStep 1583153 = 1187365) B1187365
theorem B2664515 : Blo 1052612 2664515 := bstep (se 1 (by rfl) ⟨1998386, by rfl⟩ : syracuseStep 2664515 = 3996773) B3996773
theorem B1779779 : Blo 1052612 1779779 := bstep (se 1 (by rfl) ⟨1334834, by rfl⟩ : syracuseStep 1779779 = 2669669) B2669669
theorem B1583171 : Blo 1052612 1583171 := bstep (se 1 (by rfl) ⟨1187378, by rfl⟩ : syracuseStep 1583171 = 2374757) B2374757
theorem B2533457 : Blo 1052612 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B1583201 : Blo 1052612 1583201 := bstep (se 2 (by rfl) ⟨593700, by rfl⟩ : syracuseStep 1583201 = 1187401) B1187401
theorem B1583219 : Blo 1052612 1583219 := bstep (se 1 (by rfl) ⟨1187414, by rfl⟩ : syracuseStep 1583219 = 2374829) B2374829
theorem B2369681 : Blo 1052612 2369681 := bstep (se 2 (by rfl) ⟨888630, by rfl⟩ : syracuseStep 2369681 = 1777261) B1777261
theorem B1583249 : Blo 1052612 1583249 := bstep (se 2 (by rfl) ⟨593718, by rfl⟩ : syracuseStep 1583249 = 1187437) B1187437
theorem B2369699 : Blo 1052612 2369699 := bstep (se 1 (by rfl) ⟨1777274, by rfl⟩ : syracuseStep 2369699 = 3554549) B3554549
theorem B1583267 : Blo 1052612 1583267 := bstep (se 1 (by rfl) ⟨1187450, by rfl⟩ : syracuseStep 1583267 = 2374901) B2374901
theorem B1583297 : Blo 1052612 1583297 := bstep (se 2 (by rfl) ⟨593736, by rfl⟩ : syracuseStep 1583297 = 1187473) B1187473
theorem B1779907 : Blo 1052612 1779907 := bstep (se 1 (by rfl) ⟨1334930, by rfl⟩ : syracuseStep 1779907 = 2669861) B2669861
theorem B1583315 : Blo 1052612 1583315 := bstep (se 1 (by rfl) ⟨1187486, by rfl⟩ : syracuseStep 1583315 = 2374973) B2374973
theorem B4008163 : Blo 1052612 4008163 := bstep (se 1 (by rfl) ⟨3006122, by rfl⟩ : syracuseStep 4008163 = 6012245) B6012245
theorem B1583345 : Blo 1052612 1583345 := bstep (se 2 (by rfl) ⟨593754, by rfl⟩ : syracuseStep 1583345 = 1187509) B1187509
theorem B1583363 : Blo 1052612 1583363 := bstep (se 1 (by rfl) ⟨1187522, by rfl⟩ : syracuseStep 1583363 = 2375045) B2375045
theorem B1583393 : Blo 1052612 1583393 := bstep (se 2 (by rfl) ⟨593772, by rfl⟩ : syracuseStep 1583393 = 1187545) B1187545
theorem B1583411 : Blo 1052612 1583411 := bstep (se 1 (by rfl) ⟨1187558, by rfl⟩ : syracuseStep 1583411 = 2375117) B2375117
theorem B1780049 : Blo 1052612 1780049 := bstep (se 2 (by rfl) ⟨667518, by rfl⟩ : syracuseStep 1780049 = 1335037) B1335037
theorem B1583441 : Blo 1052612 1583441 := bstep (se 2 (by rfl) ⟨593790, by rfl⟩ : syracuseStep 1583441 = 1187581) B1187581
theorem B1583459 : Blo 1052612 1583459 := bstep (se 1 (by rfl) ⟨1187594, by rfl⟩ : syracuseStep 1583459 = 2375189) B2375189
theorem B1583489 : Blo 1052612 1583489 := bstep (se 2 (by rfl) ⟨593808, by rfl⟩ : syracuseStep 1583489 = 1187617) B1187617
theorem B1583507 : Blo 1052612 1583507 := bstep (se 1 (by rfl) ⟨1187630, by rfl⟩ : syracuseStep 1583507 = 2375261) B2375261
theorem B2369969 : Blo 1052612 2369969 := bstep (se 2 (by rfl) ⟨888738, by rfl⟩ : syracuseStep 2369969 = 1777477) B1777477
theorem B1583537 : Blo 1052612 1583537 := bstep (se 2 (by rfl) ⟨593826, by rfl⟩ : syracuseStep 1583537 = 1187653) B1187653
theorem B2369987 : Blo 1052612 2369987 := bstep (se 1 (by rfl) ⟨1777490, by rfl⟩ : syracuseStep 2369987 = 3554981) B3554981
theorem B1583555 : Blo 1052612 1583555 := bstep (se 1 (by rfl) ⟨1187666, by rfl⟩ : syracuseStep 1583555 = 2375333) B2375333
theorem B1780177 : Blo 1052612 1780177 := bstep (se 2 (by rfl) ⟨667566, by rfl⟩ : syracuseStep 1780177 = 1335133) B1335133
theorem B1583585 : Blo 1052612 1583585 := bstep (se 2 (by rfl) ⟨593844, by rfl⟩ : syracuseStep 1583585 = 1187689) B1187689
theorem B1780211 : Blo 1052612 1780211 := bstep (se 1 (by rfl) ⟨1335158, by rfl⟩ : syracuseStep 1780211 = 2670317) B2670317
theorem B1583603 : Blo 1052612 1583603 := bstep (se 1 (by rfl) ⟨1187702, by rfl⟩ : syracuseStep 1583603 = 2375405) B2375405
theorem B1583633 : Blo 1052612 1583633 := bstep (se 2 (by rfl) ⟨593862, by rfl⟩ : syracuseStep 1583633 = 1187725) B1187725
theorem B1583651 : Blo 1052612 1583651 := bstep (se 1 (by rfl) ⟨1187738, by rfl⟩ : syracuseStep 1583651 = 2375477) B2375477
theorem B6761009 : Blo 1052612 6761009 := bstep (se 2 (by rfl) ⟨2535378, by rfl⟩ : syracuseStep 6761009 = 5070757) B5070757
theorem B1583681 : Blo 1052612 1583681 := bstep (se 2 (by rfl) ⟨593880, by rfl⟩ : syracuseStep 1583681 = 1187761) B1187761
theorem B5417549 : Blo 1052612 5417549 := bstep (se 3 (by rfl) ⟨1015790, by rfl⟩ : syracuseStep 5417549 = 2031581) B2031581
theorem B1583699 : Blo 1052612 1583699 := bstep (se 1 (by rfl) ⟨1187774, by rfl⟩ : syracuseStep 1583699 = 2375549) B2375549
theorem B1583729 : Blo 1052612 1583729 := bstep (se 2 (by rfl) ⟨593898, by rfl⟩ : syracuseStep 1583729 = 1187797) B1187797
theorem B1780339 : Blo 1052612 1780339 := bstep (se 1 (by rfl) ⟨1335254, by rfl⟩ : syracuseStep 1780339 = 2670509) B2670509
theorem B1583747 : Blo 1052612 1583747 := bstep (se 1 (by rfl) ⟨1187810, by rfl⟩ : syracuseStep 1583747 = 2375621) B2375621
theorem B2534033 : Blo 1052612 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B1583777 : Blo 1052612 1583777 := bstep (se 2 (by rfl) ⟨593916, by rfl⟩ : syracuseStep 1583777 = 1187833) B1187833
theorem B1583795 : Blo 1052612 1583795 := bstep (se 1 (by rfl) ⟨1187846, by rfl⟩ : syracuseStep 1583795 = 2375693) B2375693
theorem B2370257 : Blo 1052612 2370257 := bstep (se 2 (by rfl) ⟨888846, by rfl⟩ : syracuseStep 2370257 = 1777693) B1777693
theorem B1583825 : Blo 1052612 1583825 := bstep (se 2 (by rfl) ⟨593934, by rfl⟩ : syracuseStep 1583825 = 1187869) B1187869
theorem B2370275 : Blo 1052612 2370275 := bstep (se 1 (by rfl) ⟨1777706, by rfl⟩ : syracuseStep 2370275 = 3555413) B3555413
theorem B1583843 : Blo 1052612 1583843 := bstep (se 1 (by rfl) ⟨1187882, by rfl⟩ : syracuseStep 1583843 = 2375765) B2375765
theorem B1780481 : Blo 1052612 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B1583873 : Blo 1052612 1583873 := bstep (se 2 (by rfl) ⟨593952, by rfl⟩ : syracuseStep 1583873 = 1187905) B1187905
theorem B1583891 : Blo 1052612 1583891 := bstep (se 1 (by rfl) ⟨1187918, by rfl⟩ : syracuseStep 1583891 = 2375837) B2375837
theorem B2534179 : Blo 1052612 2534179 := bstep (se 1 (by rfl) ⟨1900634, by rfl⟩ : syracuseStep 2534179 = 3801269) B3801269
theorem B1583921 : Blo 1052612 1583921 := bstep (se 2 (by rfl) ⟨593970, by rfl⟩ : syracuseStep 1583921 = 1187941) B1187941
theorem B1583939 : Blo 1052612 1583939 := bstep (se 1 (by rfl) ⟨1187954, by rfl⟩ : syracuseStep 1583939 = 2375909) B2375909
theorem B1583969 : Blo 1052612 1583969 := bstep (se 2 (by rfl) ⟨593988, by rfl⟩ : syracuseStep 1583969 = 1187977) B1187977
theorem B1583987 : Blo 1052612 1583987 := bstep (se 1 (by rfl) ⟨1187990, by rfl⟩ : syracuseStep 1583987 = 2375981) B2375981
theorem B1780609 : Blo 1052612 1780609 := bstep (se 2 (by rfl) ⟨667728, by rfl⟩ : syracuseStep 1780609 = 1335457) B1335457
theorem B1584017 : Blo 1052612 1584017 := bstep (se 2 (by rfl) ⟨594006, by rfl⟩ : syracuseStep 1584017 = 1188013) B1188013
theorem B1780643 : Blo 1052612 1780643 := bstep (se 1 (by rfl) ⟨1335482, by rfl⟩ : syracuseStep 1780643 = 2670965) B2670965
theorem B1584035 : Blo 1052612 1584035 := bstep (se 1 (by rfl) ⟨1188026, by rfl⟩ : syracuseStep 1584035 = 2376053) B2376053
theorem B1584065 : Blo 1052612 1584065 := bstep (se 2 (by rfl) ⟨594024, by rfl⟩ : syracuseStep 1584065 = 1188049) B1188049
theorem B1584083 : Blo 1052612 1584083 := bstep (se 1 (by rfl) ⟨1188062, by rfl⟩ : syracuseStep 1584083 = 2376125) B2376125
theorem B2665457 : Blo 1052612 2665457 := bstep (se 2 (by rfl) ⟨999546, by rfl⟩ : syracuseStep 2665457 = 1999093) B1999093
theorem B2370545 : Blo 1052612 2370545 := bstep (se 2 (by rfl) ⟨888954, by rfl⟩ : syracuseStep 2370545 = 1777909) B1777909
theorem B1584113 : Blo 1052612 1584113 := bstep (se 2 (by rfl) ⟨594042, by rfl⟩ : syracuseStep 1584113 = 1188085) B1188085
theorem B2370563 : Blo 1052612 2370563 := bstep (se 1 (by rfl) ⟨1777922, by rfl⟩ : syracuseStep 2370563 = 3555845) B3555845
theorem B1584131 : Blo 1052612 1584131 := bstep (se 1 (by rfl) ⟨1188098, by rfl⟩ : syracuseStep 1584131 = 2376197) B2376197
theorem B1584161 : Blo 1052612 1584161 := bstep (se 2 (by rfl) ⟨594060, by rfl⟩ : syracuseStep 1584161 = 1188121) B1188121
theorem B2665507 : Blo 1052612 2665507 := bstep (se 1 (by rfl) ⟨1999130, by rfl⟩ : syracuseStep 2665507 = 3998261) B3998261
theorem B1780771 : Blo 1052612 1780771 := bstep (se 1 (by rfl) ⟨1335578, by rfl⟩ : syracuseStep 1780771 = 2671157) B2671157
theorem B1584179 : Blo 1052612 1584179 := bstep (se 1 (by rfl) ⟨1188134, by rfl⟩ : syracuseStep 1584179 = 2376269) B2376269
theorem B1584209 : Blo 1052612 1584209 := bstep (se 2 (by rfl) ⟨594078, by rfl⟩ : syracuseStep 1584209 = 1188157) B1188157
theorem B1584227 : Blo 1052612 1584227 := bstep (se 1 (by rfl) ⟨1188170, by rfl⟩ : syracuseStep 1584227 = 2376341) B2376341
theorem B1584257 : Blo 1052612 1584257 := bstep (se 2 (by rfl) ⟨594096, by rfl⟩ : syracuseStep 1584257 = 1188193) B1188193
theorem B1584275 : Blo 1052612 1584275 := bstep (se 1 (by rfl) ⟨1188206, by rfl⟩ : syracuseStep 1584275 = 2376413) B2376413
theorem B2665649 : Blo 1052612 2665649 := bstep (se 2 (by rfl) ⟨999618, by rfl⟩ : syracuseStep 2665649 = 1999237) B1999237
theorem B1780913 : Blo 1052612 1780913 := bstep (se 2 (by rfl) ⟨667842, by rfl⟩ : syracuseStep 1780913 = 1335685) B1335685
theorem B1584305 : Blo 1052612 1584305 := bstep (se 2 (by rfl) ⟨594114, by rfl⟩ : syracuseStep 1584305 = 1188229) B1188229
theorem B1584323 : Blo 1052612 1584323 := bstep (se 1 (by rfl) ⟨1188242, by rfl⟩ : syracuseStep 1584323 = 2376485) B2376485
theorem B1584353 : Blo 1052612 1584353 := bstep (se 2 (by rfl) ⟨594132, by rfl⟩ : syracuseStep 1584353 = 1188265) B1188265
theorem B1584371 : Blo 1052612 1584371 := bstep (se 1 (by rfl) ⟨1188278, by rfl⟩ : syracuseStep 1584371 = 2376557) B2376557
theorem B2370833 : Blo 1052612 2370833 := bstep (se 2 (by rfl) ⟨889062, by rfl⟩ : syracuseStep 2370833 = 1778125) B1778125
theorem B1584401 : Blo 1052612 1584401 := bstep (se 2 (by rfl) ⟨594150, by rfl⟩ : syracuseStep 1584401 = 1188301) B1188301
theorem B2370851 : Blo 1052612 2370851 := bstep (se 1 (by rfl) ⟨1778138, by rfl⟩ : syracuseStep 2370851 = 3556277) B3556277
theorem B1584419 : Blo 1052612 1584419 := bstep (se 1 (by rfl) ⟨1188314, by rfl⟩ : syracuseStep 1584419 = 2376629) B2376629
theorem B1781041 : Blo 1052612 1781041 := bstep (se 2 (by rfl) ⟨667890, by rfl⟩ : syracuseStep 1781041 = 1335781) B1335781
theorem B1584449 : Blo 1052612 1584449 := bstep (se 2 (by rfl) ⟨594168, by rfl⟩ : syracuseStep 1584449 = 1188337) B1188337
theorem B1781075 : Blo 1052612 1781075 := bstep (se 1 (by rfl) ⟨1335806, by rfl⟩ : syracuseStep 1781075 = 2671613) B2671613
theorem B1584467 : Blo 1052612 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B1584497 : Blo 1052612 1584497 := bstep (se 2 (by rfl) ⟨594186, by rfl⟩ : syracuseStep 1584497 = 1188373) B1188373
theorem B1584515 : Blo 1052612 1584515 := bstep (se 1 (by rfl) ⟨1188386, by rfl⟩ : syracuseStep 1584515 = 2376773) B2376773
theorem B7613837 : Blo 1052612 7613837 := bstep (se 3 (by rfl) ⟨1427594, by rfl⟩ : syracuseStep 7613837 = 2855189) B2855189
theorem B1584545 : Blo 1052612 1584545 := bstep (se 2 (by rfl) ⟨594204, by rfl⟩ : syracuseStep 1584545 = 1188409) B1188409
theorem B1584563 : Blo 1052612 1584563 := bstep (se 1 (by rfl) ⟨1188422, by rfl⟩ : syracuseStep 1584563 = 2376845) B2376845
theorem B1584593 : Blo 1052612 1584593 := bstep (se 2 (by rfl) ⟨594222, by rfl⟩ : syracuseStep 1584593 = 1188445) B1188445
theorem B1781203 : Blo 1052612 1781203 := bstep (se 1 (by rfl) ⟨1335902, by rfl⟩ : syracuseStep 1781203 = 2671805) B2671805
theorem B1584611 : Blo 1052612 1584611 := bstep (se 1 (by rfl) ⟨1188458, by rfl⟩ : syracuseStep 1584611 = 2376917) B2376917
theorem B1584641 : Blo 1052612 1584641 := bstep (se 2 (by rfl) ⟨594240, by rfl⟩ : syracuseStep 1584641 = 1188481) B1188481
theorem B1584659 : Blo 1052612 1584659 := bstep (se 1 (by rfl) ⟨1188494, by rfl⟩ : syracuseStep 1584659 = 2376989) B2376989
theorem B2371121 : Blo 1052612 2371121 := bstep (se 2 (by rfl) ⟨889170, by rfl⟩ : syracuseStep 2371121 = 1778341) B1778341
theorem B1584689 : Blo 1052612 1584689 := bstep (se 2 (by rfl) ⟨594258, by rfl⟩ : syracuseStep 1584689 = 1188517) B1188517
theorem B2371139 : Blo 1052612 2371139 := bstep (se 1 (by rfl) ⟨1778354, by rfl⟩ : syracuseStep 2371139 = 3556709) B3556709
theorem B1584707 : Blo 1052612 1584707 := bstep (se 1 (by rfl) ⟨1188530, by rfl⟩ : syracuseStep 1584707 = 2377061) B2377061
theorem B1781345 : Blo 1052612 1781345 := bstep (se 2 (by rfl) ⟨668004, by rfl⟩ : syracuseStep 1781345 = 1336009) B1336009
theorem B1584737 : Blo 1052612 1584737 := bstep (se 2 (by rfl) ⟨594276, by rfl⟩ : syracuseStep 1584737 = 1188553) B1188553
theorem B10268273 : Blo 1052612 10268273 := bstep (se 2 (by rfl) ⟨3850602, by rfl⟩ : syracuseStep 10268273 = 7701205) B7701205
theorem B1584755 : Blo 1052612 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B1584785 : Blo 1052612 1584785 := bstep (se 2 (by rfl) ⟨594294, by rfl⟩ : syracuseStep 1584785 = 1188589) B1188589
theorem B1584803 : Blo 1052612 1584803 := bstep (se 1 (by rfl) ⟨1188602, by rfl⟩ : syracuseStep 1584803 = 2377205) B2377205
theorem B1584833 : Blo 1052612 1584833 := bstep (se 2 (by rfl) ⟨594312, by rfl⟩ : syracuseStep 1584833 = 1188625) B1188625
theorem B1584851 : Blo 1052612 1584851 := bstep (se 1 (by rfl) ⟨1188638, by rfl⟩ : syracuseStep 1584851 = 2377277) B2377277
theorem B1781473 : Blo 1052612 1781473 := bstep (se 2 (by rfl) ⟨668052, by rfl⟩ : syracuseStep 1781473 = 1336105) B1336105
theorem B1584881 : Blo 1052612 1584881 := bstep (se 2 (by rfl) ⟨594330, by rfl⟩ : syracuseStep 1584881 = 1188661) B1188661
theorem B1781507 : Blo 1052612 1781507 := bstep (se 1 (by rfl) ⟨1336130, by rfl⟩ : syracuseStep 1781507 = 2672261) B2672261
theorem B1584899 : Blo 1052612 1584899 := bstep (se 1 (by rfl) ⟨1188674, by rfl⟩ : syracuseStep 1584899 = 2377349) B2377349
theorem B4501325 : Blo 1052612 4501325 := bstep (se 3 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 4501325 = 1687997) B1687997
theorem B2371409 : Blo 1052612 2371409 := bstep (se 2 (by rfl) ⟨889278, by rfl⟩ : syracuseStep 2371409 = 1778557) B1778557
theorem B2371427 : Blo 1052612 2371427 := bstep (se 1 (by rfl) ⟨1778570, by rfl⟩ : syracuseStep 2371427 = 3557141) B3557141
theorem B1781635 : Blo 1052612 1781635 := bstep (se 1 (by rfl) ⟨1336226, by rfl⟩ : syracuseStep 1781635 = 2672453) B2672453
theorem B1781777 : Blo 1052612 1781777 := bstep (se 2 (by rfl) ⟨668166, by rfl⟩ : syracuseStep 1781777 = 1336333) B1336333
theorem B2371697 : Blo 1052612 2371697 := bstep (se 2 (by rfl) ⟨889386, by rfl⟩ : syracuseStep 2371697 = 1778773) B1778773
theorem B2371715 : Blo 1052612 2371715 := bstep (se 1 (by rfl) ⟨1778786, by rfl⟩ : syracuseStep 2371715 = 3557573) B3557573
theorem B8007821 : Blo 1052612 8007821 := bstep (se 3 (by rfl) ⟨1501466, by rfl⟩ : syracuseStep 8007821 = 3002933) B3002933
theorem B2666641 : Blo 1052612 2666641 := bstep (se 2 (by rfl) ⟨999990, by rfl⟩ : syracuseStep 2666641 = 1999981) B1999981
theorem B1781905 : Blo 1052612 1781905 := bstep (se 2 (by rfl) ⟨668214, by rfl⟩ : syracuseStep 1781905 = 1336429) B1336429
theorem B1781939 : Blo 1052612 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B4272419 : Blo 1052612 4272419 := bstep (se 1 (by rfl) ⟨3204314, by rfl⟩ : syracuseStep 4272419 = 6408629) B6408629
theorem B1782067 : Blo 1052612 1782067 := bstep (se 1 (by rfl) ⟨1336550, by rfl⟩ : syracuseStep 1782067 = 2673101) B2673101
theorem B4010381 : Blo 1052612 4010381 := bstep (se 3 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 4010381 = 1503893) B1503893
theorem B2371985 : Blo 1052612 2371985 := bstep (se 2 (by rfl) ⟨889494, by rfl⟩ : syracuseStep 2371985 = 1778989) B1778989
theorem B2666915 : Blo 1052612 2666915 := bstep (se 1 (by rfl) ⟨2000186, by rfl⟩ : syracuseStep 2666915 = 4000373) B4000373
theorem B2372003 : Blo 1052612 2372003 := bstep (se 1 (by rfl) ⟨1779002, by rfl⟩ : syracuseStep 2372003 = 3558005) B3558005
theorem B1782209 : Blo 1052612 1782209 := bstep (se 2 (by rfl) ⟨668328, by rfl⟩ : syracuseStep 1782209 = 1336657) B1336657
theorem B6009329 : Blo 1052612 6009329 := bstep (se 2 (by rfl) ⟨2253498, by rfl⟩ : syracuseStep 6009329 = 4506997) B4506997
theorem B1126963 : Blo 1052612 1126963 := bstep (se 1 (by rfl) ⟨845222, by rfl⟩ : syracuseStep 1126963 = 1690445) B1690445
theorem B1782337 : Blo 1052612 1782337 := bstep (se 2 (by rfl) ⟨668376, by rfl⟩ : syracuseStep 1782337 = 1336753) B1336753
theorem B2667107 : Blo 1052612 2667107 := bstep (se 1 (by rfl) ⟨2000330, by rfl⟩ : syracuseStep 2667107 = 4000661) B4000661
theorem B1782371 : Blo 1052612 1782371 := bstep (se 1 (by rfl) ⟨1336778, by rfl⟩ : syracuseStep 1782371 = 2673557) B2673557
theorem B2372273 : Blo 1052612 2372273 := bstep (se 2 (by rfl) ⟨889602, by rfl⟩ : syracuseStep 2372273 = 1779205) B1779205
theorem B2372291 : Blo 1052612 2372291 := bstep (se 1 (by rfl) ⟨1779218, by rfl⟩ : syracuseStep 2372291 = 3558437) B3558437
theorem B1782499 : Blo 1052612 1782499 := bstep (se 1 (by rfl) ⟨1336874, by rfl⟩ : syracuseStep 1782499 = 2673749) B2673749
theorem B1782641 : Blo 1052612 1782641 := bstep (se 2 (by rfl) ⟨668490, by rfl⟩ : syracuseStep 1782641 = 1336981) B1336981
theorem B2372561 : Blo 1052612 2372561 := bstep (se 2 (by rfl) ⟨889710, by rfl⟩ : syracuseStep 2372561 = 1779421) B1779421
theorem B2372579 : Blo 1052612 2372579 := bstep (se 1 (by rfl) ⟨1779434, by rfl⟩ : syracuseStep 2372579 = 3558869) B3558869
theorem B1127395 : Blo 1052612 1127395 := bstep (se 1 (by rfl) ⟨845546, by rfl⟩ : syracuseStep 1127395 = 1691093) B1691093
theorem B1782769 : Blo 1052612 1782769 := bstep (se 2 (by rfl) ⟨668538, by rfl⟩ : syracuseStep 1782769 = 1337077) B1337077
theorem B1782803 : Blo 1052612 1782803 := bstep (se 1 (by rfl) ⟨1337102, by rfl⟩ : syracuseStep 1782803 = 2674205) B2674205
theorem B1782931 : Blo 1052612 1782931 := bstep (se 1 (by rfl) ⟨1337198, by rfl⟩ : syracuseStep 1782931 = 2674397) B2674397
theorem B2372849 : Blo 1052612 2372849 := bstep (se 2 (by rfl) ⟨889818, by rfl⟩ : syracuseStep 2372849 = 1779637) B1779637
theorem B2372867 : Blo 1052612 2372867 := bstep (se 1 (by rfl) ⟨1779650, by rfl⟩ : syracuseStep 2372867 = 3559301) B3559301
theorem B4502897 : Blo 1052612 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B6763981 : Blo 1052612 6763981 := bstep (se 3 (by rfl) ⟨1268246, by rfl⟩ : syracuseStep 6763981 = 2536493) B2536493
theorem B2668049 : Blo 1052612 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B2373137 : Blo 1052612 2373137 := bstep (se 2 (by rfl) ⟨889926, by rfl⟩ : syracuseStep 2373137 = 1779853) B1779853
theorem B2373155 : Blo 1052612 2373155 := bstep (se 1 (by rfl) ⟨1779866, by rfl⟩ : syracuseStep 2373155 = 3559733) B3559733
theorem B2668099 : Blo 1052612 2668099 := bstep (se 1 (by rfl) ⟨2001074, by rfl⟩ : syracuseStep 2668099 = 4002149) B4002149
theorem B2668241 : Blo 1052612 2668241 := bstep (se 2 (by rfl) ⟨1000590, by rfl⟩ : syracuseStep 2668241 = 2001181) B2001181
theorem B3553037 : Blo 1052612 3553037 := bstep (se 3 (by rfl) ⟨666194, by rfl⟩ : syracuseStep 3553037 = 1332389) B1332389
theorem B2373425 : Blo 1052612 2373425 := bstep (se 2 (by rfl) ⟨890034, by rfl⟩ : syracuseStep 2373425 = 1780069) B1780069
theorem B3553091 : Blo 1052612 3553091 := bstep (se 1 (by rfl) ⟨2664818, by rfl⟩ : syracuseStep 3553091 = 5329637) B5329637
theorem B2373443 : Blo 1052612 2373443 := bstep (se 1 (by rfl) ⟨1780082, by rfl⟩ : syracuseStep 2373443 = 3560165) B3560165
theorem B6010787 : Blo 1052612 6010787 := bstep (se 1 (by rfl) ⟨4508090, by rfl⟩ : syracuseStep 6010787 = 9016181) B9016181
theorem B3553361 : Blo 1052612 3553361 := bstep (se 2 (by rfl) ⟨1332510, by rfl⟩ : syracuseStep 3553361 = 2665021) B2665021
theorem B2373713 : Blo 1052612 2373713 := bstep (se 2 (by rfl) ⟨890142, by rfl⟩ : syracuseStep 2373713 = 1780285) B1780285
theorem B2373731 : Blo 1052612 2373731 := bstep (se 1 (by rfl) ⟨1780298, by rfl⟩ : syracuseStep 2373731 = 3560597) B3560597
theorem B46807253 : Blo 1052612 46807253 := bstep (se 7 (by rfl) ⟨548522, by rfl⟩ : syracuseStep 46807253 = 1097045) B1097045
theorem B11385157 : Blo 1052612 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B2374001 : Blo 1052612 2374001 := bstep (se 2 (by rfl) ⟨890250, by rfl⟩ : syracuseStep 2374001 = 1780501) B1780501
theorem B2374019 : Blo 1052612 2374019 := bstep (se 1 (by rfl) ⟨1780514, by rfl⟩ : syracuseStep 2374019 = 3561029) B3561029
theorem B1423891 : Blo 1052612 1423891 := bstep (se 1 (by rfl) ⟨1067918, by rfl⟩ : syracuseStep 1423891 = 2135837) B2135837
theorem B3553901 : Blo 1052612 3553901 := bstep (se 3 (by rfl) ⟨666356, by rfl⟩ : syracuseStep 3553901 = 1332713) B1332713
theorem B2374289 : Blo 1052612 2374289 := bstep (se 2 (by rfl) ⟨890358, by rfl⟩ : syracuseStep 2374289 = 1780717) B1780717
theorem B3553955 : Blo 1052612 3553955 := bstep (se 1 (by rfl) ⟨2665466, by rfl⟩ : syracuseStep 3553955 = 5330933) B5330933
theorem B2374307 : Blo 1052612 2374307 := bstep (se 1 (by rfl) ⟨1780730, by rfl⟩ : syracuseStep 2374307 = 3561461) B3561461
theorem B2669233 : Blo 1052612 2669233 := bstep (se 2 (by rfl) ⟨1000962, by rfl⟩ : syracuseStep 2669233 = 2001925) B2001925
theorem B1850147 : Blo 1052612 1850147 := bstep (se 1 (by rfl) ⟨1387610, by rfl⟩ : syracuseStep 1850147 = 2775221) B2775221
theorem B1522577 : Blo 1052612 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B3554225 : Blo 1052612 3554225 := bstep (se 2 (by rfl) ⟨1332834, by rfl⟩ : syracuseStep 3554225 = 2665669) B2665669
theorem B2374577 : Blo 1052612 2374577 := bstep (se 2 (by rfl) ⟨890466, by rfl⟩ : syracuseStep 2374577 = 1780933) B1780933
theorem B2669507 : Blo 1052612 2669507 := bstep (se 1 (by rfl) ⟨2002130, by rfl⟩ : syracuseStep 2669507 = 4004261) B4004261
theorem B2374595 : Blo 1052612 2374595 := bstep (se 1 (by rfl) ⟨1780946, by rfl⟩ : syracuseStep 2374595 = 3561893) B3561893
theorem B8010737 : Blo 1052612 8010737 := bstep (se 2 (by rfl) ⟨3004026, by rfl⟩ : syracuseStep 8010737 = 6008053) B6008053
theorem B2669699 : Blo 1052612 2669699 := bstep (se 1 (by rfl) ⟨2002274, by rfl⟩ : syracuseStep 2669699 = 4004549) B4004549
theorem B3128483 : Blo 1052612 3128483 := bstep (se 1 (by rfl) ⟨2346362, by rfl⟩ : syracuseStep 3128483 = 4692725) B4692725
theorem B1096883 : Blo 1052612 1096883 := bstep (se 1 (by rfl) ⟨822662, by rfl⟩ : syracuseStep 1096883 = 1645325) B1645325
theorem B2374865 : Blo 1052612 2374865 := bstep (se 2 (by rfl) ⟨890574, by rfl⟩ : syracuseStep 2374865 = 1781149) B1781149
theorem B2374883 : Blo 1052612 2374883 := bstep (se 1 (by rfl) ⟨1781162, by rfl⟩ : syracuseStep 2374883 = 3562325) B3562325
theorem B7224653 : Blo 1052612 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B3554765 : Blo 1052612 3554765 := bstep (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) B1333037
theorem B2375153 : Blo 1052612 2375153 := bstep (se 2 (by rfl) ⟨890682, by rfl⟩ : syracuseStep 2375153 = 1781365) B1781365
theorem B1687043 : Blo 1052612 1687043 := bstep (se 1 (by rfl) ⟨1265282, by rfl⟩ : syracuseStep 1687043 = 2530565) B2530565
theorem B3554819 : Blo 1052612 3554819 := bstep (se 1 (by rfl) ⟨2666114, by rfl⟩ : syracuseStep 3554819 = 5332229) B5332229
theorem B2375171 : Blo 1052612 2375171 := bstep (se 1 (by rfl) ⟨1781378, by rfl⟩ : syracuseStep 2375171 = 3562757) B3562757
theorem B6766213 : Blo 1052612 6766213 := bstep (se 4 (by rfl) ⟨634332, by rfl⟩ : syracuseStep 6766213 = 1268665) B1268665
theorem B1687267 : Blo 1052612 1687267 := bstep (se 1 (by rfl) ⟨1265450, by rfl⟩ : syracuseStep 1687267 = 2530901) B2530901
theorem B4505357 : Blo 1052612 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B3555089 : Blo 1052612 3555089 := bstep (se 2 (by rfl) ⟨1333158, by rfl⟩ : syracuseStep 3555089 = 2666317) B2666317
theorem B2375441 : Blo 1052612 2375441 := bstep (se 2 (by rfl) ⟨890790, by rfl⟩ : syracuseStep 2375441 = 1781581) B1781581
theorem B1687331 : Blo 1052612 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B2375459 : Blo 1052612 2375459 := bstep (se 1 (by rfl) ⟨1781594, by rfl⟩ : syracuseStep 2375459 = 3563189) B3563189
theorem B2998093 : Blo 1052612 2998093 := bstep (se 3 (by rfl) ⟨562142, by rfl⟩ : syracuseStep 2998093 = 1124285) B1124285
theorem B1687459 : Blo 1052612 1687459 := bstep (se 1 (by rfl) ⟨1265594, by rfl⟩ : syracuseStep 1687459 = 2531189) B2531189
theorem B2703395 : Blo 1052612 2703395 := bstep (se 1 (by rfl) ⟨2027546, by rfl⟩ : syracuseStep 2703395 = 4055093) B4055093
theorem B2670641 : Blo 1052612 2670641 := bstep (se 2 (by rfl) ⟨1001490, by rfl⟩ : syracuseStep 2670641 = 2002981) B2002981
theorem B2375729 : Blo 1052612 2375729 := bstep (se 2 (by rfl) ⟨890898, by rfl⟩ : syracuseStep 2375729 = 1781797) B1781797
theorem B2375747 : Blo 1052612 2375747 := bstep (se 1 (by rfl) ⟨1781810, by rfl⟩ : syracuseStep 2375747 = 3563621) B3563621
theorem B11386979 : Blo 1052612 11386979 := bstep (se 1 (by rfl) ⟨8540234, by rfl⟩ : syracuseStep 11386979 = 17080469) B17080469
theorem B4505699 : Blo 1052612 4505699 := bstep (se 1 (by rfl) ⟨3379274, by rfl⟩ : syracuseStep 4505699 = 6758549) B6758549
theorem B2670691 : Blo 1052612 2670691 := bstep (se 1 (by rfl) ⟨2003018, by rfl⟩ : syracuseStep 2670691 = 4006037) B4006037
theorem B2670833 : Blo 1052612 2670833 := bstep (se 2 (by rfl) ⟨1001562, by rfl⟩ : syracuseStep 2670833 = 2003125) B2003125
theorem B12828941 : Blo 1052612 12828941 := bstep (se 3 (by rfl) ⟨2405426, by rfl⟩ : syracuseStep 12828941 = 4810853) B4810853
theorem B3555629 : Blo 1052612 3555629 := bstep (se 3 (by rfl) ⟨666680, by rfl⟩ : syracuseStep 3555629 = 1333361) B1333361
theorem B2376017 : Blo 1052612 2376017 := bstep (se 2 (by rfl) ⟨891006, by rfl⟩ : syracuseStep 2376017 = 1782013) B1782013
theorem B3555683 : Blo 1052612 3555683 := bstep (se 1 (by rfl) ⟨2666762, by rfl⟩ : syracuseStep 3555683 = 5333525) B5333525
theorem B2376035 : Blo 1052612 2376035 := bstep (se 1 (by rfl) ⟨1782026, by rfl⟩ : syracuseStep 2376035 = 3564053) B3564053
theorem B1524227 : Blo 1052612 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B3555953 : Blo 1052612 3555953 := bstep (se 2 (by rfl) ⟨1333482, by rfl⟩ : syracuseStep 3555953 = 2666965) B2666965
theorem B1688177 : Blo 1052612 1688177 := bstep (se 2 (by rfl) ⟨633066, by rfl⟩ : syracuseStep 1688177 = 1266133) B1266133
theorem B2376305 : Blo 1052612 2376305 := bstep (se 2 (by rfl) ⟨891114, by rfl⟩ : syracuseStep 2376305 = 1782229) B1782229
theorem B2376323 : Blo 1052612 2376323 := bstep (se 1 (by rfl) ⟨1782242, by rfl⟩ : syracuseStep 2376323 = 3564485) B3564485
theorem B1426129 : Blo 1052612 1426129 := bstep (se 2 (by rfl) ⟨534798, by rfl⟩ : syracuseStep 1426129 = 1069597) B1069597
theorem B1688305 : Blo 1052612 1688305 := bstep (se 2 (by rfl) ⟨633114, by rfl⟩ : syracuseStep 1688305 = 1266229) B1266229
theorem B1622897 : Blo 1052612 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B2376593 : Blo 1052612 2376593 := bstep (se 2 (by rfl) ⟨891222, by rfl⟩ : syracuseStep 2376593 = 1782445) B1782445
theorem B2376611 : Blo 1052612 2376611 := bstep (se 1 (by rfl) ⟨1782458, by rfl⟩ : syracuseStep 2376611 = 3564917) B3564917
theorem B1688689 : Blo 1052612 1688689 := bstep (se 2 (by rfl) ⟨633258, by rfl⟩ : syracuseStep 1688689 = 1266517) B1266517
theorem B3556493 : Blo 1052612 3556493 := bstep (se 3 (by rfl) ⟨666842, by rfl⟩ : syracuseStep 3556493 = 1333685) B1333685
theorem B2376881 : Blo 1052612 2376881 := bstep (se 2 (by rfl) ⟨891330, by rfl⟩ : syracuseStep 2376881 = 1782661) B1782661
theorem B3556547 : Blo 1052612 3556547 := bstep (se 1 (by rfl) ⟨2667410, by rfl⟩ : syracuseStep 3556547 = 5334821) B5334821
theorem B2376899 : Blo 1052612 2376899 := bstep (se 1 (by rfl) ⟨1782674, by rfl⟩ : syracuseStep 2376899 = 3565349) B3565349
theorem B2671825 : Blo 1052612 2671825 := bstep (se 2 (by rfl) ⟨1001934, by rfl⟩ : syracuseStep 2671825 = 2003869) B2003869
theorem B1426691 : Blo 1052612 1426691 := bstep (se 1 (by rfl) ⟨1070018, by rfl⟩ : syracuseStep 1426691 = 2140037) B2140037
theorem B1688945 : Blo 1052612 1688945 := bstep (se 2 (by rfl) ⟨633354, by rfl⟩ : syracuseStep 1688945 = 1266709) B1266709
theorem B3556817 : Blo 1052612 3556817 := bstep (se 2 (by rfl) ⟨1333806, by rfl⟩ : syracuseStep 3556817 = 2667613) B2667613
theorem B2377169 : Blo 1052612 2377169 := bstep (se 2 (by rfl) ⟨891438, by rfl⟩ : syracuseStep 2377169 = 1782877) B1782877
theorem B2672099 : Blo 1052612 2672099 := bstep (se 1 (by rfl) ⟨2004074, by rfl⟩ : syracuseStep 2672099 = 4008149) B4008149
theorem B2377187 : Blo 1052612 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B2999825 : Blo 1052612 2999825 := bstep (se 2 (by rfl) ⟨1124934, by rfl⟩ : syracuseStep 2999825 = 2249869) B2249869
theorem B2672291 : Blo 1052612 2672291 := bstep (se 1 (by rfl) ⟨2004218, by rfl⟩ : syracuseStep 2672291 = 4008437) B4008437
theorem B3000017 : Blo 1052612 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B3557357 : Blo 1052612 3557357 := bstep (se 3 (by rfl) ⟨667004, by rfl⟩ : syracuseStep 3557357 = 1334009) B1334009
theorem B3557411 : Blo 1052612 3557411 := bstep (se 1 (by rfl) ⟨2668058, by rfl⟩ : syracuseStep 3557411 = 5336117) B5336117
theorem B3557681 : Blo 1052612 3557681 := bstep (se 2 (by rfl) ⟨1334130, by rfl⟩ : syracuseStep 3557681 = 2668261) B2668261
theorem B4868579 : Blo 1052612 4868579 := bstep (se 1 (by rfl) ⟨3651434, by rfl⟩ : syracuseStep 4868579 = 7302869) B7302869
theorem B2673233 : Blo 1052612 2673233 := bstep (se 2 (by rfl) ⟨1002462, by rfl⟩ : syracuseStep 2673233 = 2004925) B2004925
theorem B2673283 : Blo 1052612 2673283 := bstep (se 1 (by rfl) ⟨2004962, by rfl⟩ : syracuseStep 2673283 = 4009925) B4009925
theorem B1067683 : Blo 1052612 1067683 := bstep (se 1 (by rfl) ⟨800762, by rfl⟩ : syracuseStep 1067683 = 1601525) B1601525
theorem B3001009 : Blo 1052612 3001009 := bstep (se 2 (by rfl) ⟨1125378, by rfl⟩ : syracuseStep 3001009 = 2250757) B2250757
theorem B1690355 : Blo 1052612 1690355 := bstep (se 1 (by rfl) ⟨1267766, by rfl⟩ : syracuseStep 1690355 = 2535533) B2535533
theorem B2673425 : Blo 1052612 2673425 := bstep (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) B2005069
theorem B3558221 : Blo 1052612 3558221 := bstep (se 3 (by rfl) ⟨667166, by rfl⟩ : syracuseStep 3558221 = 1334333) B1334333
theorem B3558275 : Blo 1052612 3558275 := bstep (se 1 (by rfl) ⟨2668706, by rfl⟩ : syracuseStep 3558275 = 5337413) B5337413
theorem B3001283 : Blo 1052612 3001283 := bstep (se 1 (by rfl) ⟨2250962, by rfl⟩ : syracuseStep 3001283 = 4501925) B4501925
theorem B3132365 : Blo 1052612 3132365 := bstep (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) B1174637
theorem B1264691 : Blo 1052612 1264691 := bstep (se 1 (by rfl) ⟨948518, by rfl⟩ : syracuseStep 1264691 = 1897037) B1897037
theorem B3001475 : Blo 1052612 3001475 := bstep (se 1 (by rfl) ⟨2251106, by rfl⟩ : syracuseStep 3001475 = 4502213) B4502213
theorem B3558545 : Blo 1052612 3558545 := bstep (se 2 (by rfl) ⟨1334454, by rfl⟩ : syracuseStep 3558545 = 2668909) B2668909
theorem B1265171 : Blo 1052612 1265171 := bstep (se 1 (by rfl) ⟨948878, by rfl⟩ : syracuseStep 1265171 = 1897757) B1897757
theorem B1691201 : Blo 1052612 1691201 := bstep (se 2 (by rfl) ⟨634200, by rfl⟩ : syracuseStep 1691201 = 1268401) B1268401
theorem B3559085 : Blo 1052612 3559085 := bstep (se 3 (by rfl) ⟨667328, by rfl⟩ : syracuseStep 3559085 = 1334657) B1334657
theorem B48680675 : Blo 1052612 48680675 := bstep (se 1 (by rfl) ⟨36510506, by rfl⟩ : syracuseStep 48680675 = 73021013) B73021013
theorem B3559139 : Blo 1052612 3559139 := bstep (se 1 (by rfl) ⟨2669354, by rfl⟩ : syracuseStep 3559139 = 5338709) B5338709
theorem B2674417 : Blo 1052612 2674417 := bstep (se 2 (by rfl) ⟨1002906, by rfl⟩ : syracuseStep 2674417 = 2005813) B2005813
theorem B3657581 : Blo 1052612 3657581 := bstep (se 3 (by rfl) ⟨685796, by rfl⟩ : syracuseStep 3657581 = 1371593) B1371593
theorem B3002285 : Blo 1052612 3002285 := bstep (se 3 (by rfl) ⟨562928, by rfl⟩ : syracuseStep 3002285 = 1125857) B1125857
theorem B3559409 : Blo 1052612 3559409 := bstep (se 2 (by rfl) ⟨1334778, by rfl⟩ : syracuseStep 3559409 = 2669557) B2669557
theorem B4509731 : Blo 1052612 4509731 := bstep (se 1 (by rfl) ⟨3382298, by rfl⟩ : syracuseStep 4509731 = 6764597) B6764597
theorem B1691713 : Blo 1052612 1691713 := bstep (se 2 (by rfl) ⟨634392, by rfl⟩ : syracuseStep 1691713 = 1268785) B1268785
theorem B3002467 : Blo 1052612 3002467 := bstep (se 1 (by rfl) ⟨2251850, by rfl⟩ : syracuseStep 3002467 = 4503701) B4503701
theorem B4804721 : Blo 1052612 4804721 := bstep (se 2 (by rfl) ⟨1801770, by rfl⟩ : syracuseStep 4804721 = 3603541) B3603541
theorem B3559949 : Blo 1052612 3559949 := bstep (se 3 (by rfl) ⟨667490, by rfl⟩ : syracuseStep 3559949 = 1334981) B1334981
theorem B3560003 : Blo 1052612 3560003 := bstep (se 1 (by rfl) ⟨2670002, by rfl⟩ : syracuseStep 3560003 = 5340005) B5340005
theorem B3002957 : Blo 1052612 3002957 := bstep (se 3 (by rfl) ⟨563054, by rfl⟩ : syracuseStep 3002957 = 1126109) B1126109
theorem B6083171 : Blo 1052612 6083171 := bstep (se 1 (by rfl) ⟨4562378, by rfl⟩ : syracuseStep 6083171 = 9124757) B9124757
theorem B1692323 : Blo 1052612 1692323 := bstep (se 1 (by rfl) ⟨1269242, by rfl⟩ : syracuseStep 1692323 = 2538485) B2538485
theorem B3560273 : Blo 1052612 3560273 := bstep (se 2 (by rfl) ⟨1335102, by rfl⟩ : syracuseStep 3560273 = 2670205) B2670205
theorem B4805489 : Blo 1052612 4805489 := bstep (se 2 (by rfl) ⟨1802058, by rfl⟩ : syracuseStep 4805489 = 3604117) B3604117
theorem B7590797 : Blo 1052612 7590797 := bstep (se 3 (by rfl) ⟨1423274, by rfl⟩ : syracuseStep 7590797 = 2846549) B2846549
theorem B5067683 : Blo 1052612 5067683 := bstep (se 1 (by rfl) ⟨3800762, by rfl⟩ : syracuseStep 5067683 = 7601525) B7601525
theorem B1332227 : Blo 1052612 1332227 := bstep (se 1 (by rfl) ⟨999170, by rfl⟩ : syracuseStep 1332227 = 1998341) B1998341
theorem B4052045 : Blo 1052612 4052045 := bstep (se 3 (by rfl) ⟨759758, by rfl⟩ : syracuseStep 4052045 = 1519517) B1519517
theorem B5067953 : Blo 1052612 5067953 := bstep (se 2 (by rfl) ⟨1900482, by rfl⟩ : syracuseStep 5067953 = 3800965) B3800965
theorem B4510961 : Blo 1052612 4510961 := bstep (se 2 (by rfl) ⟨1691610, by rfl⟩ : syracuseStep 4510961 = 3383221) B3383221
theorem B2282851 : Blo 1052612 2282851 := bstep (se 1 (by rfl) ⟨1712138, by rfl⟩ : syracuseStep 2282851 = 3424277) B3424277
theorem B3560813 : Blo 1052612 3560813 := bstep (se 3 (by rfl) ⟨667652, by rfl⟩ : syracuseStep 3560813 = 1335305) B1335305
theorem B5133709 : Blo 1052612 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B3560867 : Blo 1052612 3560867 := bstep (se 1 (by rfl) ⟨2670650, by rfl⟩ : syracuseStep 3560867 = 5341301) B5341301
theorem B15226339 : Blo 1052612 15226339 := bstep (se 1 (by rfl) ⟨11419754, by rfl⟩ : syracuseStep 15226339 = 22839509) B22839509
theorem B1267363 : Blo 1052612 1267363 := bstep (se 1 (by rfl) ⟨950522, by rfl⟩ : syracuseStep 1267363 = 1901045) B1901045
theorem B5330609 : Blo 1052612 5330609 := bstep (se 2 (by rfl) ⟨1998978, by rfl⟩ : syracuseStep 5330609 = 3997957) B3997957
theorem B3561137 : Blo 1052612 3561137 := bstep (se 2 (by rfl) ⟨1335426, by rfl⟩ : syracuseStep 3561137 = 2670853) B2670853
theorem B1332931 : Blo 1052612 1332931 := bstep (se 1 (by rfl) ⟨999698, by rfl⟩ : syracuseStep 1332931 = 1999397) B1999397
theorem B3004141 : Blo 1052612 3004141 := bstep (se 3 (by rfl) ⟨563276, by rfl⟩ : syracuseStep 3004141 = 1126553) B1126553
theorem B1333027 : Blo 1052612 1333027 := bstep (se 1 (by rfl) ⟨999770, by rfl⟩ : syracuseStep 1333027 = 1999541) B1999541
theorem B1267555 : Blo 1052612 1267555 := bstep (se 1 (by rfl) ⟨950666, by rfl⟩ : syracuseStep 1267555 = 1901333) B1901333
theorem B18012131 : Blo 1052612 18012131 := bstep (se 1 (by rfl) ⟨13509098, by rfl⟩ : syracuseStep 18012131 = 27018197) B27018197
theorem B2250833 : Blo 1052612 2250833 := bstep (se 2 (by rfl) ⟨844062, by rfl⟩ : syracuseStep 2250833 = 1688125) B1688125
theorem B3561677 : Blo 1052612 3561677 := bstep (se 3 (by rfl) ⟨667814, by rfl⟩ : syracuseStep 3561677 = 1335629) B1335629
theorem B1267939 : Blo 1052612 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B3561731 : Blo 1052612 3561731 := bstep (se 1 (by rfl) ⟨2671298, by rfl⟩ : syracuseStep 3561731 = 5342597) B5342597
theorem B1333523 : Blo 1052612 1333523 := bstep (se 1 (by rfl) ⟨1000142, by rfl⟩ : syracuseStep 1333523 = 2000285) B2000285
theorem B1825187 : Blo 1052612 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B4282865 : Blo 1052612 4282865 := bstep (se 2 (by rfl) ⟨1606074, by rfl⟩ : syracuseStep 4282865 = 3212149) B3212149
theorem B3562001 : Blo 1052612 3562001 := bstep (se 2 (by rfl) ⟨1335750, by rfl⟩ : syracuseStep 3562001 = 2671501) B2671501
theorem B9263857 : Blo 1052612 9263857 := bstep (se 2 (by rfl) ⟨3473946, by rfl⟩ : syracuseStep 9263857 = 6947893) B6947893
theorem B3005201 : Blo 1052612 3005201 := bstep (se 2 (by rfl) ⟨1126950, by rfl⟩ : syracuseStep 3005201 = 2253901) B2253901
theorem B5069603 : Blo 1052612 5069603 := bstep (se 1 (by rfl) ⟨3802202, by rfl⟩ : syracuseStep 5069603 = 7604405) B7604405
theorem B1268627 : Blo 1052612 1268627 := bstep (se 1 (by rfl) ⟨951470, by rfl⟩ : syracuseStep 1268627 = 1902941) B1902941
theorem B1334227 : Blo 1052612 1334227 := bstep (se 1 (by rfl) ⟨1000670, by rfl⟩ : syracuseStep 1334227 = 2001341) B2001341
theorem B3562541 : Blo 1052612 3562541 := bstep (se 3 (by rfl) ⟨667976, by rfl⟩ : syracuseStep 3562541 = 1335953) B1335953
theorem B1334323 : Blo 1052612 1334323 := bstep (se 1 (by rfl) ⟨1000742, by rfl⟩ : syracuseStep 1334323 = 2001485) B2001485
theorem B5332067 : Blo 1052612 5332067 := bstep (se 1 (by rfl) ⟨3999050, by rfl⟩ : syracuseStep 5332067 = 7998101) B7998101
theorem B3562595 : Blo 1052612 3562595 := bstep (se 1 (by rfl) ⟨2671946, by rfl⟩ : syracuseStep 3562595 = 5343893) B5343893
theorem B2284817 : Blo 1052612 2284817 := bstep (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) B1713613
theorem B3562865 : Blo 1052612 3562865 := bstep (se 2 (by rfl) ⟨1336074, by rfl⟩ : syracuseStep 3562865 = 2672149) B2672149
theorem B3005873 : Blo 1052612 3005873 := bstep (se 2 (by rfl) ⟨1127202, by rfl⟩ : syracuseStep 3005873 = 2254405) B2254405
theorem B1334819 : Blo 1052612 1334819 := bstep (se 1 (by rfl) ⟨1001114, by rfl⟩ : syracuseStep 1334819 = 2002229) B2002229
theorem B1498819 : Blo 1052612 1498819 := bstep (se 1 (by rfl) ⟨1124114, by rfl⟩ : syracuseStep 1498819 = 2248229) B2248229
theorem B1498915 : Blo 1052612 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B5332877 : Blo 1052612 5332877 := bstep (se 3 (by rfl) ⟨999914, by rfl⟩ : syracuseStep 5332877 = 1999829) B1999829
theorem B3563405 : Blo 1052612 3563405 := bstep (se 3 (by rfl) ⟨668138, by rfl⟩ : syracuseStep 3563405 = 1336277) B1336277
theorem B3563459 : Blo 1052612 3563459 := bstep (se 1 (by rfl) ⟨2672594, by rfl⟩ : syracuseStep 3563459 = 5345189) B5345189
theorem B3039277 : Blo 1052612 3039277 := bstep (se 3 (by rfl) ⟨569864, by rfl⟩ : syracuseStep 3039277 = 1139729) B1139729
theorem B3006659 : Blo 1052612 3006659 := bstep (se 1 (by rfl) ⟨2254994, by rfl⟩ : syracuseStep 3006659 = 4509989) B4509989
theorem B3563729 : Blo 1052612 3563729 := bstep (se 2 (by rfl) ⟨1336398, by rfl⟩ : syracuseStep 3563729 = 2672797) B2672797
theorem B1335523 : Blo 1052612 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B13492493 : Blo 1052612 13492493 := bstep (se 3 (by rfl) ⟨2529842, by rfl⟩ : syracuseStep 13492493 = 5059685) B5059685
theorem B1499411 : Blo 1052612 1499411 := bstep (se 1 (by rfl) ⟨1124558, by rfl⟩ : syracuseStep 1499411 = 2249117) B2249117
theorem B1335619 : Blo 1052612 1335619 := bstep (se 1 (by rfl) ⟨1001714, by rfl⟩ : syracuseStep 1335619 = 2003429) B2003429
theorem B5071373 : Blo 1052612 5071373 := bstep (se 3 (by rfl) ⟨950882, by rfl⟩ : syracuseStep 5071373 = 1901765) B1901765
theorem B3006989 : Blo 1052612 3006989 := bstep (se 3 (by rfl) ⟨563810, by rfl⟩ : syracuseStep 3006989 = 1127621) B1127621
theorem B3007057 : Blo 1052612 3007057 := bstep (se 2 (by rfl) ⟨1127646, by rfl⟩ : syracuseStep 3007057 = 2255293) B2255293
theorem B3564269 : Blo 1052612 3564269 := bstep (se 3 (by rfl) ⟨668300, by rfl⟩ : syracuseStep 3564269 = 1336601) B1336601
theorem B3564323 : Blo 1052612 3564323 := bstep (se 1 (by rfl) ⟨2673242, by rfl⟩ : syracuseStep 3564323 = 5346485) B5346485
theorem B1336115 : Blo 1052612 1336115 := bstep (se 1 (by rfl) ⟨1002086, by rfl⟩ : syracuseStep 1336115 = 2004173) B2004173
theorem B3007331 : Blo 1052612 3007331 := bstep (se 1 (by rfl) ⟨2255498, by rfl⟩ : syracuseStep 3007331 = 4510997) B4510997
theorem B1500049 : Blo 1052612 1500049 := bstep (se 2 (by rfl) ⟨562518, by rfl⟩ : syracuseStep 1500049 = 1125037) B1125037
theorem B3564593 : Blo 1052612 3564593 := bstep (se 2 (by rfl) ⟨1336722, by rfl⟩ : syracuseStep 3564593 = 2673445) B2673445
theorem B4809827 : Blo 1052612 4809827 := bstep (se 1 (by rfl) ⟨3607370, by rfl⟩ : syracuseStep 4809827 = 7214741) B7214741
theorem B12838085 : Blo 1052612 12838085 := bstep (se 4 (by rfl) ⟨1203570, by rfl⟩ : syracuseStep 12838085 = 2407141) B2407141
theorem B1500385 : Blo 1052612 1500385 := bstep (se 2 (by rfl) ⟨562644, by rfl⟩ : syracuseStep 1500385 = 1125289) B1125289
theorem B3794161 : Blo 1052612 3794161 := bstep (se 2 (by rfl) ⟨1422810, by rfl⟩ : syracuseStep 3794161 = 2845621) B2845621
theorem B2254243 : Blo 1052612 2254243 := bstep (se 1 (by rfl) ⟨1690682, by rfl⟩ : syracuseStep 2254243 = 3381365) B3381365
theorem B1336819 : Blo 1052612 1336819 := bstep (se 1 (by rfl) ⟨1002614, by rfl⟩ : syracuseStep 1336819 = 2005229) B2005229
theorem B3565133 : Blo 1052612 3565133 := bstep (se 3 (by rfl) ⟨668462, by rfl⟩ : syracuseStep 3565133 = 1336925) B1336925
theorem B1336915 : Blo 1052612 1336915 := bstep (se 1 (by rfl) ⟨1002686, by rfl⟩ : syracuseStep 1336915 = 2005373) B2005373
theorem B3565187 : Blo 1052612 3565187 := bstep (se 1 (by rfl) ⟨2673890, by rfl⟩ : syracuseStep 3565187 = 5347781) B5347781
theorem B3008173 : Blo 1052612 3008173 := bstep (se 3 (by rfl) ⟨564032, by rfl⟩ : syracuseStep 3008173 = 1128065) B1128065
theorem B4056817 : Blo 1052612 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B14411533 : Blo 1052612 14411533 := bstep (se 3 (by rfl) ⟨2702162, by rfl⟩ : syracuseStep 14411533 = 5404325) B5404325
theorem B1500977 : Blo 1052612 1500977 := bstep (se 2 (by rfl) ⟨562866, by rfl⟩ : syracuseStep 1500977 = 1125733) B1125733
theorem B13526837 : Blo 1052612 13526837 := bstep (se 5 (by rfl) ⟨634070, by rfl⟩ : syracuseStep 13526837 = 1268141) B1268141
theorem B3008333 : Blo 1052612 3008333 := bstep (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) B1128125
theorem B3565457 : Blo 1052612 3565457 := bstep (se 2 (by rfl) ⟨1337046, by rfl⟩ : syracuseStep 3565457 = 2674093) B2674093
theorem B3008515 : Blo 1052612 3008515 := bstep (se 1 (by rfl) ⟨2256386, by rfl⟩ : syracuseStep 3008515 = 4512773) B4512773
theorem B7596101 : Blo 1052612 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B1501507 : Blo 1052612 1501507 := bstep (se 1 (by rfl) ⟨1126130, by rfl⟩ : syracuseStep 1501507 = 2252261) B2252261
theorem B3565997 : Blo 1052612 3565997 := bstep (se 3 (by rfl) ⟨668624, by rfl⟩ : syracuseStep 3565997 = 1337249) B1337249
theorem B3566051 : Blo 1052612 3566051 := bstep (se 1 (by rfl) ⟨2674538, by rfl⟩ : syracuseStep 3566051 = 5349077) B5349077
theorem B1501843 : Blo 1052612 1501843 := bstep (se 1 (by rfl) ⟨1126382, by rfl⟩ : syracuseStep 1501843 = 2252765) B2252765
theorem B5335793 : Blo 1052612 5335793 := bstep (se 2 (by rfl) ⟨2000922, by rfl⟩ : syracuseStep 5335793 = 4001845) B4001845
theorem B4811725 : Blo 1052612 4811725 := bstep (se 3 (by rfl) ⟨902198, by rfl⟩ : syracuseStep 4811725 = 1804397) B1804397
theorem B1502401 : Blo 1052612 1502401 := bstep (se 2 (by rfl) ⟨563400, by rfl⟩ : syracuseStep 1502401 = 1126801) B1126801
theorem B1502435 : Blo 1052612 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B2256113 : Blo 1052612 2256113 := bstep (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) B1692085
theorem B1502993 : Blo 1052612 1502993 := bstep (se 2 (by rfl) ⟨563622, by rfl⟩ : syracuseStep 1502993 = 1127245) B1127245
theorem B1503073 : Blo 1052612 1503073 := bstep (se 2 (by rfl) ⟨563652, by rfl⟩ : syracuseStep 1503073 = 1127305) B1127305
theorem B4059277 : Blo 1052612 4059277 := bstep (se 3 (by rfl) ⟨761114, by rfl⟩ : syracuseStep 4059277 = 1522229) B1522229
theorem B5337251 : Blo 1052612 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B1929379 : Blo 1052612 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B2846897 : Blo 1052612 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B27390149 : Blo 1052612 27390149 := bstep (se 4 (by rfl) ⟨2567826, by rfl⟩ : syracuseStep 27390149 = 5135653) B5135653
theorem B17134051 : Blo 1052612 17134051 := bstep (se 1 (by rfl) ⟨12850538, by rfl⟩ : syracuseStep 17134051 = 25701077) B25701077
theorem B1503859 : Blo 1052612 1503859 := bstep (se 1 (by rfl) ⟨1127894, by rfl⟩ : syracuseStep 1503859 = 2255789) B2255789
theorem B2290339 : Blo 1052612 2290339 := bstep (se 1 (by rfl) ⟨1717754, by rfl⟩ : syracuseStep 2290339 = 3435509) B3435509
theorem B2847437 : Blo 1052612 2847437 := bstep (se 3 (by rfl) ⟨533894, by rfl⟩ : syracuseStep 2847437 = 1067789) B1067789
theorem B3797923 : Blo 1052612 3797923 := bstep (se 1 (by rfl) ⟨2848442, by rfl⟩ : syracuseStep 3797923 = 5696885) B5696885
theorem B3208099 : Blo 1052612 3208099 := bstep (se 1 (by rfl) ⟨2406074, by rfl⟩ : syracuseStep 3208099 = 4812149) B4812149
theorem B1897411 : Blo 1052612 1897411 := bstep (se 1 (by rfl) ⟨1423058, by rfl⟩ : syracuseStep 1897411 = 2846117) B2846117
theorem B3797965 : Blo 1052612 3797965 := bstep (se 3 (by rfl) ⟨712118, by rfl⟩ : syracuseStep 3797965 = 1424237) B1424237
theorem B5338061 : Blo 1052612 5338061 := bstep (se 3 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 5338061 = 2001773) B2001773
theorem B1504337 : Blo 1052612 1504337 := bstep (se 2 (by rfl) ⟨564126, by rfl⟩ : syracuseStep 1504337 = 1128253) B1128253
theorem B7599217 : Blo 1052612 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B1602931 : Blo 1052612 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B4290061 : Blo 1052612 4290061 := bstep (se 3 (by rfl) ⟨804386, by rfl⟩ : syracuseStep 4290061 = 1608773) B1608773
theorem B3601955 : Blo 1052612 3601955 := bstep (se 1 (by rfl) ⟨2701466, by rfl⟩ : syracuseStep 3601955 = 5402933) B5402933
theorem B3044945 : Blo 1052612 3044945 := bstep (se 2 (by rfl) ⟨1141854, by rfl⟩ : syracuseStep 3044945 = 2283709) B2283709
theorem B2848625 : Blo 1052612 2848625 := bstep (se 2 (by rfl) ⟨1068234, by rfl⟩ : syracuseStep 2848625 = 2136469) B2136469
theorem B3373073 : Blo 1052612 3373073 := bstep (se 2 (by rfl) ⟨1264902, by rfl⟩ : syracuseStep 3373073 = 2529805) B2529805
theorem B5699717 : Blo 1052612 5699717 := bstep (se 4 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 5699717 = 1068697) B1068697
theorem B3373265 : Blo 1052612 3373265 := bstep (se 2 (by rfl) ⟨1264974, by rfl⟩ : syracuseStep 3373265 = 2529949) B2529949
theorem B5405069 : Blo 1052612 5405069 := bstep (se 3 (by rfl) ⟨1013450, by rfl⟩ : syracuseStep 5405069 = 2026901) B2026901
theorem B5700017 : Blo 1052612 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B1604099 : Blo 1052612 1604099 := bstep (se 1 (by rfl) ⟨1203074, by rfl⟩ : syracuseStep 1604099 = 2406149) B2406149
theorem B5995205 : Blo 1052612 5995205 := bstep (se 4 (by rfl) ⟨562050, by rfl⟩ : syracuseStep 5995205 = 1124101) B1124101
theorem B6093539 : Blo 1052612 6093539 := bstep (se 1 (by rfl) ⟨4570154, by rfl⟩ : syracuseStep 6093539 = 9140309) B9140309
theorem B11992049 : Blo 1052612 11992049 := bstep (se 2 (by rfl) ⟨4497018, by rfl⟩ : syracuseStep 11992049 = 8994037) B8994037
theorem B6749219 : Blo 1052612 6749219 := bstep (se 1 (by rfl) ⟨5061914, by rfl⟩ : syracuseStep 6749219 = 10123829) B10123829
theorem B3210349 : Blo 1052612 3210349 := bstep (se 3 (by rfl) ⟨601940, by rfl⟩ : syracuseStep 3210349 = 1203881) B1203881
theorem B5995889 : Blo 1052612 5995889 := bstep (se 2 (by rfl) ⟨2248458, by rfl⟩ : syracuseStep 5995889 = 4496917) B4496917
theorem B4816397 : Blo 1052612 4816397 := bstep (se 3 (by rfl) ⟨903074, by rfl⟩ : syracuseStep 4816397 = 1806149) B1806149
theorem B1998371 : Blo 1052612 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B5340977 : Blo 1052612 5340977 := bstep (se 2 (by rfl) ⟨2002866, by rfl⟩ : syracuseStep 5340977 = 4005733) B4005733
theorem B14450501 : Blo 1052612 14450501 := bstep (se 4 (by rfl) ⟨1354734, by rfl⟩ : syracuseStep 14450501 = 2709469) B2709469
theorem B5865329 : Blo 1052612 5865329 := bstep (se 2 (by rfl) ⟨2199498, by rfl⟩ : syracuseStep 5865329 = 4398997) B4398997
theorem B1605587 : Blo 1052612 1605587 := bstep (se 1 (by rfl) ⟨1204190, by rfl⟩ : syracuseStep 1605587 = 2408381) B2408381
theorem B1802263 : Blo 1052612 1802263 := bstep (se 1 (by rfl) ⟨1351697, by rfl⟩ : syracuseStep 1802263 = 2703395) B2703395
theorem B8552627 : Blo 1052612 8552627 := bstep (se 1 (by rfl) ⟨6414470, by rfl⟩ : syracuseStep 8552627 = 12828941) B12828941
theorem B3998231 : Blo 1052612 3998231 := bstep (se 1 (by rfl) ⟨2998673, by rfl⟩ : syracuseStep 3998231 = 5997347) B5997347
theorem B1081931 : Blo 1052612 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B3998429 : Blo 1052612 3998429 := bstep (se 3 (by rfl) ⟨749705, by rfl⟩ : syracuseStep 3998429 = 1499411) B1499411
theorem B1999883 : Blo 1052612 1999883 := bstep (se 1 (by rfl) ⟨1499912, by rfl⟩ : syracuseStep 1999883 = 2999825) B2999825
theorem B5342273 : Blo 1052612 5342273 := bstep (se 2 (by rfl) ⟨2003352, by rfl⟩ : syracuseStep 5342273 = 4006705) B4006705
theorem B2000065 : Blo 1052612 2000065 := bstep (se 2 (by rfl) ⟨750024, by rfl⟩ : syracuseStep 2000065 = 1500049) B1500049
theorem B2000513 : Blo 1052612 2000513 := bstep (se 2 (by rfl) ⟨750192, by rfl⟩ : syracuseStep 2000513 = 1500385) B1500385
theorem B3245719 : Blo 1052612 3245719 := bstep (se 1 (by rfl) ⟨2434289, by rfl⟩ : syracuseStep 3245719 = 4868579) B4868579
theorem B3606167 : Blo 1052612 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B11700085 : Blo 1052612 11700085 := bstep (se 5 (by rfl) ⟨548441, by rfl⟩ : syracuseStep 11700085 = 1096883) B1096883
theorem B2000855 : Blo 1052612 2000855 := bstep (se 1 (by rfl) ⟨1500641, by rfl⟩ : syracuseStep 2000855 = 3001283) B3001283
theorem B5409089 : Blo 1052612 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B2001523 : Blo 1052612 2001523 := bstep (se 1 (by rfl) ⟨1501142, by rfl⟩ : syracuseStep 2001523 = 3002285) B3002285
theorem B4000387 : Blo 1052612 4000387 := bstep (se 1 (by rfl) ⟨3000290, by rfl⟩ : syracuseStep 4000387 = 6000581) B6000581
theorem B7604867 : Blo 1052612 7604867 := bstep (se 1 (by rfl) ⟨5703650, by rfl⟩ : syracuseStep 7604867 = 11407301) B11407301
theorem B4000691 : Blo 1052612 4000691 := bstep (se 1 (by rfl) ⟨3000518, by rfl⟩ : syracuseStep 4000691 = 6001037) B6001037
theorem B5344217 : Blo 1052612 5344217 := bstep (se 2 (by rfl) ⟨2004081, by rfl⟩ : syracuseStep 5344217 = 4008163) B4008163
theorem B2001971 : Blo 1052612 2001971 := bstep (se 1 (by rfl) ⟨1501478, by rfl⟩ : syracuseStep 2001971 = 3002957) B3002957
theorem B2002009 : Blo 1052612 2002009 := bstep (se 2 (by rfl) ⟨750753, by rfl⟩ : syracuseStep 2002009 = 1501507) B1501507
theorem B6425731 : Blo 1052612 6425731 := bstep (se 1 (by rfl) ⟨4819298, by rfl⟩ : syracuseStep 6425731 = 9638597) B9638597
theorem B3378455 : Blo 1052612 3378455 := bstep (se 1 (by rfl) ⟨2533841, by rfl⟩ : syracuseStep 3378455 = 5067683) B5067683
theorem B3804509 : Blo 1052612 3804509 := bstep (se 3 (by rfl) ⟨713345, by rfl⟩ : syracuseStep 3804509 = 1426691) B1426691
theorem B3378635 : Blo 1052612 3378635 := bstep (se 1 (by rfl) ⟨2533976, by rfl⟩ : syracuseStep 3378635 = 5067953) B5067953
theorem B2002457 : Blo 1052612 2002457 := bstep (se 2 (by rfl) ⟨750921, by rfl⟩ : syracuseStep 2002457 = 1501843) B1501843
theorem B4001345 : Blo 1052612 4001345 := bstep (se 2 (by rfl) ⟨1500504, by rfl⟩ : syracuseStep 4001345 = 3001009) B3001009
theorem B3378905 : Blo 1052612 3378905 := bstep (se 2 (by rfl) ⟨1267089, by rfl⟩ : syracuseStep 3378905 = 2534179) B2534179
theorem B7606021 : Blo 1052612 7606021 := bstep (se 4 (by rfl) ⟨713064, by rfl⟩ : syracuseStep 7606021 = 1426129) B1426129
theorem B3805073 : Blo 1052612 3805073 := bstep (se 2 (by rfl) ⟨1426902, by rfl⟩ : syracuseStep 3805073 = 2853805) B2853805
theorem B1052619 : Blo 1052612 1052619 := bstep (se 1 (by rfl) ⟨789464, by rfl⟩ : syracuseStep 1052619 = 1578929) B1578929
theorem B1052631 : Blo 1052612 1052631 := bstep (se 1 (by rfl) ⟨789473, by rfl⟩ : syracuseStep 1052631 = 1578947) B1578947
theorem B1052651 : Blo 1052612 1052651 := bstep (se 1 (by rfl) ⟨789488, by rfl⟩ : syracuseStep 1052651 = 1578977) B1578977
theorem B1052663 : Blo 1052612 1052663 := bstep (se 1 (by rfl) ⟨789497, by rfl⟩ : syracuseStep 1052663 = 1578995) B1578995
theorem B1052683 : Blo 1052612 1052683 := bstep (se 1 (by rfl) ⟨789512, by rfl⟩ : syracuseStep 1052683 = 1579025) B1579025
theorem B1052695 : Blo 1052612 1052695 := bstep (se 1 (by rfl) ⟨789521, by rfl⟩ : syracuseStep 1052695 = 1579043) B1579043
theorem B3084311 : Blo 1052612 3084311 := bstep (se 1 (by rfl) ⟨2313233, by rfl⟩ : syracuseStep 3084311 = 4626467) B4626467
theorem B1052715 : Blo 1052612 1052715 := bstep (se 1 (by rfl) ⟨789536, by rfl⟩ : syracuseStep 1052715 = 1579073) B1579073
theorem B1052727 : Blo 1052612 1052727 := bstep (se 1 (by rfl) ⟨789545, by rfl⟩ : syracuseStep 1052727 = 1579091) B1579091
theorem B1052747 : Blo 1052612 1052747 := bstep (se 1 (by rfl) ⟨789560, by rfl⟩ : syracuseStep 1052747 = 1579121) B1579121
theorem B1052759 : Blo 1052612 1052759 := bstep (se 1 (by rfl) ⟨789569, by rfl⟩ : syracuseStep 1052759 = 1579139) B1579139
theorem B9605213 : Blo 1052612 9605213 := bstep (se 3 (by rfl) ⟨1800977, by rfl⟩ : syracuseStep 9605213 = 3601955) B3601955
theorem B1052779 : Blo 1052612 1052779 := bstep (se 1 (by rfl) ⟨789584, by rfl⟩ : syracuseStep 1052779 = 1579169) B1579169
theorem B1052791 : Blo 1052612 1052791 := bstep (se 1 (by rfl) ⟨789593, by rfl⟩ : syracuseStep 1052791 = 1579187) B1579187
theorem B1052811 : Blo 1052612 1052811 := bstep (se 1 (by rfl) ⟨789608, by rfl⟩ : syracuseStep 1052811 = 1579217) B1579217
theorem B1052823 : Blo 1052612 1052823 := bstep (se 1 (by rfl) ⟨789617, by rfl⟩ : syracuseStep 1052823 = 1579235) B1579235
theorem B17109143 : Blo 1052612 17109143 := bstep (se 1 (by rfl) ⟨12831857, by rfl⟩ : syracuseStep 17109143 = 25663715) B25663715
theorem B1052843 : Blo 1052612 1052843 := bstep (se 1 (by rfl) ⟨789632, by rfl⟩ : syracuseStep 1052843 = 1579265) B1579265
theorem B1052855 : Blo 1052612 1052855 := bstep (se 1 (by rfl) ⟨789641, by rfl⟩ : syracuseStep 1052855 = 1579283) B1579283
theorem B1052875 : Blo 1052612 1052875 := bstep (se 1 (by rfl) ⟨789656, by rfl⟩ : syracuseStep 1052875 = 1579313) B1579313
theorem B1052887 : Blo 1052612 1052887 := bstep (se 1 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 1052887 = 1579331) B1579331
theorem B1052907 : Blo 1052612 1052907 := bstep (se 1 (by rfl) ⟨789680, by rfl⟩ : syracuseStep 1052907 = 1579361) B1579361
theorem B1052919 : Blo 1052612 1052919 := bstep (se 1 (by rfl) ⟨789689, by rfl⟩ : syracuseStep 1052919 = 1579379) B1579379
theorem B2003201 : Blo 1052612 2003201 := bstep (se 2 (by rfl) ⟨751200, by rfl⟩ : syracuseStep 2003201 = 1502401) B1502401
theorem B1052939 : Blo 1052612 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B1052951 : Blo 1052612 1052951 := bstep (se 1 (by rfl) ⟨789713, by rfl⟩ : syracuseStep 1052951 = 1579427) B1579427
theorem B1052971 : Blo 1052612 1052971 := bstep (se 1 (by rfl) ⟨789728, by rfl⟩ : syracuseStep 1052971 = 1579457) B1579457
theorem B1052983 : Blo 1052612 1052983 := bstep (se 1 (by rfl) ⟨789737, by rfl⟩ : syracuseStep 1052983 = 1579475) B1579475
theorem B1053003 : Blo 1052612 1053003 := bstep (se 1 (by rfl) ⟨789752, by rfl⟩ : syracuseStep 1053003 = 1579505) B1579505
theorem B2855243 : Blo 1052612 2855243 := bstep (se 1 (by rfl) ⟨2141432, by rfl⟩ : syracuseStep 2855243 = 4282865) B4282865
theorem B1053015 : Blo 1052612 1053015 := bstep (se 1 (by rfl) ⟨789761, by rfl⟩ : syracuseStep 1053015 = 1579523) B1579523
theorem B1053035 : Blo 1052612 1053035 := bstep (se 1 (by rfl) ⟨789776, by rfl⟩ : syracuseStep 1053035 = 1579553) B1579553
theorem B1053047 : Blo 1052612 1053047 := bstep (se 1 (by rfl) ⟨789785, by rfl⟩ : syracuseStep 1053047 = 1579571) B1579571
theorem B1053067 : Blo 1052612 1053067 := bstep (se 1 (by rfl) ⟨789800, by rfl⟩ : syracuseStep 1053067 = 1579601) B1579601
theorem B1053079 : Blo 1052612 1053079 := bstep (se 1 (by rfl) ⟨789809, by rfl⟩ : syracuseStep 1053079 = 1579619) B1579619
theorem B1053099 : Blo 1052612 1053099 := bstep (se 1 (by rfl) ⟨789824, by rfl⟩ : syracuseStep 1053099 = 1579649) B1579649
theorem B1053111 : Blo 1052612 1053111 := bstep (se 1 (by rfl) ⟨789833, by rfl⟩ : syracuseStep 1053111 = 1579667) B1579667
theorem B1053131 : Blo 1052612 1053131 := bstep (se 1 (by rfl) ⟨789848, by rfl⟩ : syracuseStep 1053131 = 1579697) B1579697
theorem B1184215 : Blo 1052612 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B1053143 : Blo 1052612 1053143 := bstep (se 1 (by rfl) ⟨789857, by rfl⟩ : syracuseStep 1053143 = 1579715) B1579715
theorem B1053163 : Blo 1052612 1053163 := bstep (se 1 (by rfl) ⟨789872, by rfl⟩ : syracuseStep 1053163 = 1579745) B1579745
theorem B1053175 : Blo 1052612 1053175 := bstep (se 1 (by rfl) ⟨789881, by rfl⟩ : syracuseStep 1053175 = 1579763) B1579763
theorem B1053195 : Blo 1052612 1053195 := bstep (se 1 (by rfl) ⟨789896, by rfl⟩ : syracuseStep 1053195 = 1579793) B1579793
theorem B2003467 : Blo 1052612 2003467 := bstep (se 1 (by rfl) ⟨1502600, by rfl⟩ : syracuseStep 2003467 = 3005201) B3005201
theorem B1053207 : Blo 1052612 1053207 := bstep (se 1 (by rfl) ⟨789905, by rfl⟩ : syracuseStep 1053207 = 1579811) B1579811
theorem B3379735 : Blo 1052612 3379735 := bstep (se 1 (by rfl) ⟨2534801, by rfl⟩ : syracuseStep 3379735 = 5069603) B5069603
theorem B1053227 : Blo 1052612 1053227 := bstep (se 1 (by rfl) ⟨789920, by rfl⟩ : syracuseStep 1053227 = 1579841) B1579841
theorem B8000045 : Blo 1052612 8000045 := bstep (se 3 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 8000045 = 3000017) B3000017
theorem B5345837 : Blo 1052612 5345837 := bstep (se 3 (by rfl) ⟨1002344, by rfl⟩ : syracuseStep 5345837 = 2004689) B2004689
theorem B1053239 : Blo 1052612 1053239 := bstep (se 1 (by rfl) ⟨789929, by rfl⟩ : syracuseStep 1053239 = 1579859) B1579859
theorem B1053259 : Blo 1052612 1053259 := bstep (se 1 (by rfl) ⟨789944, by rfl⟩ : syracuseStep 1053259 = 1579889) B1579889
theorem B1053271 : Blo 1052612 1053271 := bstep (se 1 (by rfl) ⟨789953, by rfl⟩ : syracuseStep 1053271 = 1579907) B1579907
theorem B1053291 : Blo 1052612 1053291 := bstep (se 1 (by rfl) ⟨789968, by rfl⟩ : syracuseStep 1053291 = 1579937) B1579937
theorem B1053303 : Blo 1052612 1053303 := bstep (se 1 (by rfl) ⟨789977, by rfl⟩ : syracuseStep 1053303 = 1579955) B1579955
theorem B20845187 : Blo 1052612 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B1184395 : Blo 1052612 1184395 := bstep (se 1 (by rfl) ⟨888296, by rfl⟩ : syracuseStep 1184395 = 1776593) B1776593
theorem B1053323 : Blo 1052612 1053323 := bstep (se 1 (by rfl) ⟨789992, by rfl⟩ : syracuseStep 1053323 = 1579985) B1579985
theorem B1053335 : Blo 1052612 1053335 := bstep (se 1 (by rfl) ⟨790001, by rfl⟩ : syracuseStep 1053335 = 1580003) B1580003
theorem B1053355 : Blo 1052612 1053355 := bstep (se 1 (by rfl) ⟨790016, by rfl⟩ : syracuseStep 1053355 = 1580033) B1580033
theorem B1053367 : Blo 1052612 1053367 := bstep (se 1 (by rfl) ⟨790025, by rfl⟩ : syracuseStep 1053367 = 1580051) B1580051
theorem B1053387 : Blo 1052612 1053387 := bstep (se 1 (by rfl) ⟨790040, by rfl⟩ : syracuseStep 1053387 = 1580081) B1580081
theorem B1053399 : Blo 1052612 1053399 := bstep (se 1 (by rfl) ⟨790049, by rfl⟩ : syracuseStep 1053399 = 1580099) B1580099
theorem B1053419 : Blo 1052612 1053419 := bstep (se 1 (by rfl) ⟨790064, by rfl⟩ : syracuseStep 1053419 = 1580129) B1580129
theorem B1184503 : Blo 1052612 1184503 := bstep (se 1 (by rfl) ⟨888377, by rfl⟩ : syracuseStep 1184503 = 1776755) B1776755
theorem B1053431 : Blo 1052612 1053431 := bstep (se 1 (by rfl) ⟨790073, by rfl⟩ : syracuseStep 1053431 = 1580147) B1580147
theorem B1053451 : Blo 1052612 1053451 := bstep (se 1 (by rfl) ⟨790088, by rfl⟩ : syracuseStep 1053451 = 1580177) B1580177
theorem B1053463 : Blo 1052612 1053463 := bstep (se 1 (by rfl) ⟨790097, by rfl⟩ : syracuseStep 1053463 = 1580195) B1580195
theorem B1053483 : Blo 1052612 1053483 := bstep (se 1 (by rfl) ⟨790112, by rfl⟩ : syracuseStep 1053483 = 1580225) B1580225
theorem B4002605 : Blo 1052612 4002605 := bstep (se 3 (by rfl) ⟨750488, by rfl⟩ : syracuseStep 4002605 = 1500977) B1500977
theorem B1053495 : Blo 1052612 1053495 := bstep (se 1 (by rfl) ⟨790121, by rfl⟩ : syracuseStep 1053495 = 1580243) B1580243
theorem B1053515 : Blo 1052612 1053515 := bstep (se 1 (by rfl) ⟨790136, by rfl⟩ : syracuseStep 1053515 = 1580273) B1580273
theorem B4002635 : Blo 1052612 4002635 := bstep (se 1 (by rfl) ⟨3001976, by rfl⟩ : syracuseStep 4002635 = 6003953) B6003953
theorem B1053527 : Blo 1052612 1053527 := bstep (se 1 (by rfl) ⟨790145, by rfl⟩ : syracuseStep 1053527 = 1580291) B1580291
theorem B1053547 : Blo 1052612 1053547 := bstep (se 1 (by rfl) ⟨790160, by rfl⟩ : syracuseStep 1053547 = 1580321) B1580321
theorem B1053559 : Blo 1052612 1053559 := bstep (se 1 (by rfl) ⟨790169, by rfl⟩ : syracuseStep 1053559 = 1580339) B1580339
theorem B1053579 : Blo 1052612 1053579 := bstep (se 1 (by rfl) ⟨790184, by rfl⟩ : syracuseStep 1053579 = 1580369) B1580369
theorem B1053591 : Blo 1052612 1053591 := bstep (se 1 (by rfl) ⟨790193, by rfl⟩ : syracuseStep 1053591 = 1580387) B1580387
theorem B1184683 : Blo 1052612 1184683 := bstep (se 1 (by rfl) ⟨888512, by rfl⟩ : syracuseStep 1184683 = 1777025) B1777025
theorem B1053611 : Blo 1052612 1053611 := bstep (se 1 (by rfl) ⟨790208, by rfl⟩ : syracuseStep 1053611 = 1580417) B1580417
theorem B1053623 : Blo 1052612 1053623 := bstep (se 1 (by rfl) ⟨790217, by rfl⟩ : syracuseStep 1053623 = 1580435) B1580435
theorem B1053643 : Blo 1052612 1053643 := bstep (se 1 (by rfl) ⟨790232, by rfl⟩ : syracuseStep 1053643 = 1580465) B1580465
theorem B2003915 : Blo 1052612 2003915 := bstep (se 1 (by rfl) ⟨1502936, by rfl⟩ : syracuseStep 2003915 = 3005873) B3005873
theorem B1053655 : Blo 1052612 1053655 := bstep (se 1 (by rfl) ⟨790241, by rfl⟩ : syracuseStep 1053655 = 1580483) B1580483
theorem B1053675 : Blo 1052612 1053675 := bstep (se 1 (by rfl) ⟨790256, by rfl⟩ : syracuseStep 1053675 = 1580513) B1580513
theorem B1053687 : Blo 1052612 1053687 := bstep (se 1 (by rfl) ⟨790265, by rfl⟩ : syracuseStep 1053687 = 1580531) B1580531
theorem B1053707 : Blo 1052612 1053707 := bstep (se 1 (by rfl) ⟨790280, by rfl⟩ : syracuseStep 1053707 = 1580561) B1580561
theorem B1184791 : Blo 1052612 1184791 := bstep (se 1 (by rfl) ⟨888593, by rfl⟩ : syracuseStep 1184791 = 1777187) B1777187
theorem B1053719 : Blo 1052612 1053719 := bstep (se 1 (by rfl) ⟨790289, by rfl⟩ : syracuseStep 1053719 = 1580579) B1580579
theorem B1053739 : Blo 1052612 1053739 := bstep (se 1 (by rfl) ⟨790304, by rfl⟩ : syracuseStep 1053739 = 1580609) B1580609
theorem B1053751 : Blo 1052612 1053751 := bstep (se 1 (by rfl) ⟨790313, by rfl⟩ : syracuseStep 1053751 = 1580627) B1580627
theorem B1053771 : Blo 1052612 1053771 := bstep (se 1 (by rfl) ⟨790328, by rfl⟩ : syracuseStep 1053771 = 1580657) B1580657
theorem B1053783 : Blo 1052612 1053783 := bstep (se 1 (by rfl) ⟨790337, by rfl⟩ : syracuseStep 1053783 = 1580675) B1580675
theorem B1053803 : Blo 1052612 1053803 := bstep (se 1 (by rfl) ⟨790352, by rfl⟩ : syracuseStep 1053803 = 1580705) B1580705
theorem B1053815 : Blo 1052612 1053815 := bstep (se 1 (by rfl) ⟨790361, by rfl⟩ : syracuseStep 1053815 = 1580723) B1580723
theorem B2004097 : Blo 1052612 2004097 := bstep (se 2 (by rfl) ⟨751536, by rfl⟩ : syracuseStep 2004097 = 1503073) B1503073
theorem B1053835 : Blo 1052612 1053835 := bstep (se 1 (by rfl) ⟨790376, by rfl⟩ : syracuseStep 1053835 = 1580753) B1580753
theorem B1053847 : Blo 1052612 1053847 := bstep (se 1 (by rfl) ⟨790385, by rfl⟩ : syracuseStep 1053847 = 1580771) B1580771
theorem B1053867 : Blo 1052612 1053867 := bstep (se 1 (by rfl) ⟨790400, by rfl⟩ : syracuseStep 1053867 = 1580801) B1580801
theorem B3609779 : Blo 1052612 3609779 := bstep (se 1 (by rfl) ⟨2707334, by rfl⟩ : syracuseStep 3609779 = 5414669) B5414669
theorem B1053879 : Blo 1052612 1053879 := bstep (se 1 (by rfl) ⟨790409, by rfl⟩ : syracuseStep 1053879 = 1580819) B1580819
theorem B1184971 : Blo 1052612 1184971 := bstep (se 1 (by rfl) ⟨888728, by rfl⟩ : syracuseStep 1184971 = 1777457) B1777457
theorem B1053899 : Blo 1052612 1053899 := bstep (se 1 (by rfl) ⟨790424, by rfl⟩ : syracuseStep 1053899 = 1580849) B1580849
theorem B1053911 : Blo 1052612 1053911 := bstep (se 1 (by rfl) ⟨790433, by rfl⟩ : syracuseStep 1053911 = 1580867) B1580867
theorem B1053931 : Blo 1052612 1053931 := bstep (se 1 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 1053931 = 1580897) B1580897
theorem B1053943 : Blo 1052612 1053943 := bstep (se 1 (by rfl) ⟨790457, by rfl⟩ : syracuseStep 1053943 = 1580915) B1580915
theorem B1053963 : Blo 1052612 1053963 := bstep (se 1 (by rfl) ⟨790472, by rfl⟩ : syracuseStep 1053963 = 1580945) B1580945
theorem B1053975 : Blo 1052612 1053975 := bstep (se 1 (by rfl) ⟨790481, by rfl⟩ : syracuseStep 1053975 = 1580963) B1580963
theorem B1053995 : Blo 1052612 1053995 := bstep (se 1 (by rfl) ⟨790496, by rfl⟩ : syracuseStep 1053995 = 1580993) B1580993
theorem B1185079 : Blo 1052612 1185079 := bstep (se 1 (by rfl) ⟨888809, by rfl⟩ : syracuseStep 1185079 = 1777619) B1777619
theorem B1054007 : Blo 1052612 1054007 := bstep (se 1 (by rfl) ⟨790505, by rfl⟩ : syracuseStep 1054007 = 1581011) B1581011
theorem B1054027 : Blo 1052612 1054027 := bstep (se 1 (by rfl) ⟨790520, by rfl⟩ : syracuseStep 1054027 = 1581041) B1581041
theorem B1054039 : Blo 1052612 1054039 := bstep (se 1 (by rfl) ⟨790529, by rfl⟩ : syracuseStep 1054039 = 1581059) B1581059
theorem B1054059 : Blo 1052612 1054059 := bstep (se 1 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 1054059 = 1581089) B1581089
theorem B16258421 : Blo 1052612 16258421 := bstep (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) B1524227
theorem B1054071 : Blo 1052612 1054071 := bstep (se 1 (by rfl) ⟨790553, by rfl⟩ : syracuseStep 1054071 = 1581107) B1581107
theorem B1054091 : Blo 1052612 1054091 := bstep (se 1 (by rfl) ⟨790568, by rfl⟩ : syracuseStep 1054091 = 1581137) B1581137
theorem B1054103 : Blo 1052612 1054103 := bstep (se 1 (by rfl) ⟨790577, by rfl⟩ : syracuseStep 1054103 = 1581155) B1581155
theorem B1054123 : Blo 1052612 1054123 := bstep (se 1 (by rfl) ⟨790592, by rfl⟩ : syracuseStep 1054123 = 1581185) B1581185
theorem B1054135 : Blo 1052612 1054135 := bstep (se 1 (by rfl) ⟨790601, by rfl⟩ : syracuseStep 1054135 = 1581203) B1581203
theorem B1054155 : Blo 1052612 1054155 := bstep (se 1 (by rfl) ⟨790616, by rfl⟩ : syracuseStep 1054155 = 1581233) B1581233
theorem B2004439 : Blo 1052612 2004439 := bstep (se 1 (by rfl) ⟨1503329, by rfl⟩ : syracuseStep 2004439 = 3006659) B3006659
theorem B1054167 : Blo 1052612 1054167 := bstep (se 1 (by rfl) ⟨790625, by rfl⟩ : syracuseStep 1054167 = 1581251) B1581251
theorem B4003289 : Blo 1052612 4003289 := bstep (se 2 (by rfl) ⟨1501233, by rfl⟩ : syracuseStep 4003289 = 3002467) B3002467
theorem B1185259 : Blo 1052612 1185259 := bstep (se 1 (by rfl) ⟨888944, by rfl⟩ : syracuseStep 1185259 = 1777889) B1777889
theorem B1054187 : Blo 1052612 1054187 := bstep (se 1 (by rfl) ⟨790640, by rfl⟩ : syracuseStep 1054187 = 1581281) B1581281
theorem B1054199 : Blo 1052612 1054199 := bstep (se 1 (by rfl) ⟨790649, by rfl⟩ : syracuseStep 1054199 = 1581299) B1581299
theorem B1054219 : Blo 1052612 1054219 := bstep (se 1 (by rfl) ⟨790664, by rfl⟩ : syracuseStep 1054219 = 1581329) B1581329
theorem B1054231 : Blo 1052612 1054231 := bstep (se 1 (by rfl) ⟨790673, by rfl⟩ : syracuseStep 1054231 = 1581347) B1581347
theorem B1054251 : Blo 1052612 1054251 := bstep (se 1 (by rfl) ⟨790688, by rfl⟩ : syracuseStep 1054251 = 1581377) B1581377
theorem B6002221 : Blo 1052612 6002221 := bstep (se 3 (by rfl) ⟨1125416, by rfl⟩ : syracuseStep 6002221 = 2250833) B2250833
theorem B6755885 : Blo 1052612 6755885 := bstep (se 3 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 6755885 = 2533457) B2533457
theorem B1054263 : Blo 1052612 1054263 := bstep (se 1 (by rfl) ⟨790697, by rfl⟩ : syracuseStep 1054263 = 1581395) B1581395
theorem B1054283 : Blo 1052612 1054283 := bstep (se 1 (by rfl) ⟨790712, by rfl⟩ : syracuseStep 1054283 = 1581425) B1581425
theorem B1185367 : Blo 1052612 1185367 := bstep (se 1 (by rfl) ⟨889025, by rfl⟩ : syracuseStep 1185367 = 1778051) B1778051
theorem B1054295 : Blo 1052612 1054295 := bstep (se 1 (by rfl) ⟨790721, by rfl⟩ : syracuseStep 1054295 = 1581443) B1581443
theorem B1054315 : Blo 1052612 1054315 := bstep (se 1 (by rfl) ⟨790736, by rfl⟩ : syracuseStep 1054315 = 1581473) B1581473
theorem B1054327 : Blo 1052612 1054327 := bstep (se 1 (by rfl) ⟨790745, by rfl⟩ : syracuseStep 1054327 = 1581491) B1581491
theorem B1054347 : Blo 1052612 1054347 := bstep (se 1 (by rfl) ⟨790760, by rfl⟩ : syracuseStep 1054347 = 1581521) B1581521
theorem B1054359 : Blo 1052612 1054359 := bstep (se 1 (by rfl) ⟨790769, by rfl⟩ : syracuseStep 1054359 = 1581539) B1581539
theorem B1054379 : Blo 1052612 1054379 := bstep (se 1 (by rfl) ⟨790784, by rfl⟩ : syracuseStep 1054379 = 1581569) B1581569
theorem B3380915 : Blo 1052612 3380915 := bstep (se 1 (by rfl) ⟨2535686, by rfl⟩ : syracuseStep 3380915 = 5071373) B5071373
theorem B2004659 : Blo 1052612 2004659 := bstep (se 1 (by rfl) ⟨1503494, by rfl⟩ : syracuseStep 2004659 = 3006989) B3006989
theorem B1054391 : Blo 1052612 1054391 := bstep (se 1 (by rfl) ⟨790793, by rfl⟩ : syracuseStep 1054391 = 1581587) B1581587
theorem B1054411 : Blo 1052612 1054411 := bstep (se 1 (by rfl) ⟨790808, by rfl⟩ : syracuseStep 1054411 = 1581617) B1581617
theorem B1054423 : Blo 1052612 1054423 := bstep (se 1 (by rfl) ⟨790817, by rfl⟩ : syracuseStep 1054423 = 1581635) B1581635
theorem B1054443 : Blo 1052612 1054443 := bstep (se 1 (by rfl) ⟨790832, by rfl⟩ : syracuseStep 1054443 = 1581665) B1581665
theorem B1054455 : Blo 1052612 1054455 := bstep (se 1 (by rfl) ⟨790841, by rfl⟩ : syracuseStep 1054455 = 1581683) B1581683
theorem B1185547 : Blo 1052612 1185547 := bstep (se 1 (by rfl) ⟨889160, by rfl⟩ : syracuseStep 1185547 = 1778321) B1778321
theorem B1054475 : Blo 1052612 1054475 := bstep (se 1 (by rfl) ⟨790856, by rfl⟩ : syracuseStep 1054475 = 1581713) B1581713
theorem B4003607 : Blo 1052612 4003607 := bstep (se 1 (by rfl) ⟨3002705, by rfl⟩ : syracuseStep 4003607 = 6005411) B6005411
theorem B1054487 : Blo 1052612 1054487 := bstep (se 1 (by rfl) ⟨790865, by rfl⟩ : syracuseStep 1054487 = 1581731) B1581731
theorem B1054507 : Blo 1052612 1054507 := bstep (se 1 (by rfl) ⟨790880, by rfl⟩ : syracuseStep 1054507 = 1581761) B1581761
theorem B1054519 : Blo 1052612 1054519 := bstep (se 1 (by rfl) ⟨790889, by rfl⟩ : syracuseStep 1054519 = 1581779) B1581779
theorem B1054539 : Blo 1052612 1054539 := bstep (se 1 (by rfl) ⟨790904, by rfl⟩ : syracuseStep 1054539 = 1581809) B1581809
theorem B1054551 : Blo 1052612 1054551 := bstep (se 1 (by rfl) ⟨790913, by rfl⟩ : syracuseStep 1054551 = 1581827) B1581827
theorem B1054571 : Blo 1052612 1054571 := bstep (se 1 (by rfl) ⟨790928, by rfl⟩ : syracuseStep 1054571 = 1581857) B1581857
theorem B1185655 : Blo 1052612 1185655 := bstep (se 1 (by rfl) ⟨889241, by rfl⟩ : syracuseStep 1185655 = 1778483) B1778483
theorem B1054583 : Blo 1052612 1054583 := bstep (se 1 (by rfl) ⟨790937, by rfl⟩ : syracuseStep 1054583 = 1581875) B1581875
theorem B1054603 : Blo 1052612 1054603 := bstep (se 1 (by rfl) ⟨790952, by rfl⟩ : syracuseStep 1054603 = 1581905) B1581905
theorem B1054615 : Blo 1052612 1054615 := bstep (se 1 (by rfl) ⟨790961, by rfl⟩ : syracuseStep 1054615 = 1581923) B1581923
theorem B2004887 : Blo 1052612 2004887 := bstep (se 1 (by rfl) ⟨1503665, by rfl⟩ : syracuseStep 2004887 = 3007331) B3007331
theorem B1054635 : Blo 1052612 1054635 := bstep (se 1 (by rfl) ⟨790976, by rfl⟩ : syracuseStep 1054635 = 1581953) B1581953
theorem B1054647 : Blo 1052612 1054647 := bstep (se 1 (by rfl) ⟨790985, by rfl⟩ : syracuseStep 1054647 = 1581971) B1581971
theorem B1054667 : Blo 1052612 1054667 := bstep (se 1 (by rfl) ⟨791000, by rfl⟩ : syracuseStep 1054667 = 1582001) B1582001
theorem B1054679 : Blo 1052612 1054679 := bstep (se 1 (by rfl) ⟨791009, by rfl⟩ : syracuseStep 1054679 = 1582019) B1582019
theorem B22845401 : Blo 1052612 22845401 := bstep (se 2 (by rfl) ⟨8567025, by rfl⟩ : syracuseStep 22845401 = 17134051) B17134051
theorem B1054699 : Blo 1052612 1054699 := bstep (se 1 (by rfl) ⟨791024, by rfl⟩ : syracuseStep 1054699 = 1582049) B1582049
theorem B1054711 : Blo 1052612 1054711 := bstep (se 1 (by rfl) ⟨791033, by rfl⟩ : syracuseStep 1054711 = 1582067) B1582067
theorem B1579019 : Blo 1052612 1579019 := bstep (se 1 (by rfl) ⟨1184264, by rfl⟩ : syracuseStep 1579019 = 2368529) B2368529
theorem B1054731 : Blo 1052612 1054731 := bstep (se 1 (by rfl) ⟨791048, by rfl⟩ : syracuseStep 1054731 = 1582097) B1582097
theorem B1579031 : Blo 1052612 1579031 := bstep (se 1 (by rfl) ⟨1184273, by rfl⟩ : syracuseStep 1579031 = 2368547) B2368547
theorem B1054743 : Blo 1052612 1054743 := bstep (se 1 (by rfl) ⟨791057, by rfl⟩ : syracuseStep 1054743 = 1582115) B1582115
theorem B1185835 : Blo 1052612 1185835 := bstep (se 1 (by rfl) ⟨889376, by rfl⟩ : syracuseStep 1185835 = 1778753) B1778753
theorem B1054763 : Blo 1052612 1054763 := bstep (se 1 (by rfl) ⟨791072, by rfl⟩ : syracuseStep 1054763 = 1582145) B1582145
theorem B1054775 : Blo 1052612 1054775 := bstep (se 1 (by rfl) ⟨791081, by rfl⟩ : syracuseStep 1054775 = 1582163) B1582163
theorem B1054795 : Blo 1052612 1054795 := bstep (se 1 (by rfl) ⟨791096, by rfl⟩ : syracuseStep 1054795 = 1582193) B1582193
theorem B1054807 : Blo 1052612 1054807 := bstep (se 1 (by rfl) ⟨791105, by rfl⟩ : syracuseStep 1054807 = 1582211) B1582211
theorem B1579097 : Blo 1052612 1579097 := bstep (se 2 (by rfl) ⟨592161, by rfl⟩ : syracuseStep 1579097 = 1184323) B1184323
theorem B1054827 : Blo 1052612 1054827 := bstep (se 1 (by rfl) ⟨791120, by rfl⟩ : syracuseStep 1054827 = 1582241) B1582241
theorem B1054839 : Blo 1052612 1054839 := bstep (se 1 (by rfl) ⟨791129, by rfl⟩ : syracuseStep 1054839 = 1582259) B1582259
theorem B8558723 : Blo 1052612 8558723 := bstep (se 1 (by rfl) ⟨6419042, by rfl⟩ : syracuseStep 8558723 = 12838085) B12838085
theorem B1054859 : Blo 1052612 1054859 := bstep (se 1 (by rfl) ⟨791144, by rfl⟩ : syracuseStep 1054859 = 1582289) B1582289
theorem B1185943 : Blo 1052612 1185943 := bstep (se 1 (by rfl) ⟨889457, by rfl⟩ : syracuseStep 1185943 = 1778915) B1778915
theorem B1054871 : Blo 1052612 1054871 := bstep (se 1 (by rfl) ⟨791153, by rfl⟩ : syracuseStep 1054871 = 1582307) B1582307
theorem B2005145 : Blo 1052612 2005145 := bstep (se 2 (by rfl) ⟨751929, by rfl⟩ : syracuseStep 2005145 = 1503859) B1503859
theorem B1054891 : Blo 1052612 1054891 := bstep (se 1 (by rfl) ⟨791168, by rfl⟩ : syracuseStep 1054891 = 1582337) B1582337
theorem B1054903 : Blo 1052612 1054903 := bstep (se 1 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 1054903 = 1582355) B1582355
theorem B1579211 : Blo 1052612 1579211 := bstep (se 1 (by rfl) ⟨1184408, by rfl⟩ : syracuseStep 1579211 = 2368817) B2368817
theorem B1054923 : Blo 1052612 1054923 := bstep (se 1 (by rfl) ⟨791192, by rfl⟩ : syracuseStep 1054923 = 1582385) B1582385
theorem B1579223 : Blo 1052612 1579223 := bstep (se 1 (by rfl) ⟨1184417, by rfl⟩ : syracuseStep 1579223 = 2368835) B2368835
theorem B1054935 : Blo 1052612 1054935 := bstep (se 1 (by rfl) ⟨791201, by rfl⟩ : syracuseStep 1054935 = 1582403) B1582403
theorem B3053785 : Blo 1052612 3053785 := bstep (se 2 (by rfl) ⟨1145169, by rfl⟩ : syracuseStep 3053785 = 2290339) B2290339
theorem B1054955 : Blo 1052612 1054955 := bstep (se 1 (by rfl) ⟨791216, by rfl⟩ : syracuseStep 1054955 = 1582433) B1582433
theorem B1054967 : Blo 1052612 1054967 := bstep (se 1 (by rfl) ⟨791225, by rfl⟩ : syracuseStep 1054967 = 1582451) B1582451
theorem B1054987 : Blo 1052612 1054987 := bstep (se 1 (by rfl) ⟨791240, by rfl⟩ : syracuseStep 1054987 = 1582481) B1582481
theorem B1054999 : Blo 1052612 1054999 := bstep (se 1 (by rfl) ⟨791249, by rfl⟩ : syracuseStep 1054999 = 1582499) B1582499
theorem B1579289 : Blo 1052612 1579289 := bstep (se 2 (by rfl) ⟨592233, by rfl⟩ : syracuseStep 1579289 = 1184467) B1184467
theorem B1055019 : Blo 1052612 1055019 := bstep (se 1 (by rfl) ⟨791264, by rfl⟩ : syracuseStep 1055019 = 1582529) B1582529
theorem B1055031 : Blo 1052612 1055031 := bstep (se 1 (by rfl) ⟨791273, by rfl⟩ : syracuseStep 1055031 = 1582547) B1582547
theorem B1186123 : Blo 1052612 1186123 := bstep (se 1 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 1186123 = 1779185) B1779185
theorem B1055051 : Blo 1052612 1055051 := bstep (se 1 (by rfl) ⟨791288, by rfl⟩ : syracuseStep 1055051 = 1582577) B1582577
theorem B1055063 : Blo 1052612 1055063 := bstep (se 1 (by rfl) ⟨791297, by rfl⟩ : syracuseStep 1055063 = 1582595) B1582595
theorem B1055083 : Blo 1052612 1055083 := bstep (se 1 (by rfl) ⟨791312, by rfl⟩ : syracuseStep 1055083 = 1582625) B1582625
theorem B1055095 : Blo 1052612 1055095 := bstep (se 1 (by rfl) ⟨791321, by rfl⟩ : syracuseStep 1055095 = 1582643) B1582643
theorem B1579403 : Blo 1052612 1579403 := bstep (se 1 (by rfl) ⟨1184552, by rfl⟩ : syracuseStep 1579403 = 2369105) B2369105
theorem B1055115 : Blo 1052612 1055115 := bstep (se 1 (by rfl) ⟨791336, by rfl⟩ : syracuseStep 1055115 = 1582673) B1582673
theorem B1579415 : Blo 1052612 1579415 := bstep (se 1 (by rfl) ⟨1184561, by rfl⟩ : syracuseStep 1579415 = 2369123) B2369123
theorem B1055127 : Blo 1052612 1055127 := bstep (se 1 (by rfl) ⟨791345, by rfl⟩ : syracuseStep 1055127 = 1582691) B1582691
theorem B1055147 : Blo 1052612 1055147 := bstep (se 1 (by rfl) ⟨791360, by rfl⟩ : syracuseStep 1055147 = 1582721) B1582721
theorem B4004275 : Blo 1052612 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B1186231 : Blo 1052612 1186231 := bstep (se 1 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 1186231 = 1779347) B1779347
theorem B1055159 : Blo 1052612 1055159 := bstep (se 1 (by rfl) ⟨791369, by rfl⟩ : syracuseStep 1055159 = 1582739) B1582739
theorem B1055179 : Blo 1052612 1055179 := bstep (se 1 (by rfl) ⟨791384, by rfl⟩ : syracuseStep 1055179 = 1582769) B1582769
theorem B1055191 : Blo 1052612 1055191 := bstep (se 1 (by rfl) ⟨791393, by rfl⟩ : syracuseStep 1055191 = 1582787) B1582787
theorem B1579481 : Blo 1052612 1579481 := bstep (se 2 (by rfl) ⟨592305, by rfl⟩ : syracuseStep 1579481 = 1184611) B1184611
theorem B1055211 : Blo 1052612 1055211 := bstep (se 1 (by rfl) ⟨791408, by rfl⟩ : syracuseStep 1055211 = 1582817) B1582817
theorem B1055223 : Blo 1052612 1055223 := bstep (se 1 (by rfl) ⟨791417, by rfl⟩ : syracuseStep 1055223 = 1582835) B1582835
theorem B1055243 : Blo 1052612 1055243 := bstep (se 1 (by rfl) ⟨791432, by rfl⟩ : syracuseStep 1055243 = 1582865) B1582865
theorem B1055255 : Blo 1052612 1055255 := bstep (se 1 (by rfl) ⟨791441, by rfl⟩ : syracuseStep 1055255 = 1582883) B1582883
theorem B9017891 : Blo 1052612 9017891 := bstep (se 1 (by rfl) ⟨6763418, by rfl⟩ : syracuseStep 9017891 = 13526837) B13526837
theorem B1055275 : Blo 1052612 1055275 := bstep (se 1 (by rfl) ⟨791456, by rfl⟩ : syracuseStep 1055275 = 1582913) B1582913
theorem B2005555 : Blo 1052612 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B1055287 : Blo 1052612 1055287 := bstep (se 1 (by rfl) ⟨791465, by rfl⟩ : syracuseStep 1055287 = 1582931) B1582931
theorem B1579595 : Blo 1052612 1579595 := bstep (se 1 (by rfl) ⟨1184696, by rfl⟩ : syracuseStep 1579595 = 2369393) B2369393
theorem B1055307 : Blo 1052612 1055307 := bstep (se 1 (by rfl) ⟨791480, by rfl⟩ : syracuseStep 1055307 = 1582961) B1582961
theorem B1579607 : Blo 1052612 1579607 := bstep (se 1 (by rfl) ⟨1184705, by rfl⟩ : syracuseStep 1579607 = 2369411) B2369411
theorem B1055319 : Blo 1052612 1055319 := bstep (se 1 (by rfl) ⟨791489, by rfl⟩ : syracuseStep 1055319 = 1582979) B1582979
theorem B2529881 : Blo 1052612 2529881 := bstep (se 2 (by rfl) ⟨948705, by rfl⟩ : syracuseStep 2529881 = 1897411) B1897411
theorem B1186411 : Blo 1052612 1186411 := bstep (se 1 (by rfl) ⟨889808, by rfl⟩ : syracuseStep 1186411 = 1779617) B1779617
theorem B1055339 : Blo 1052612 1055339 := bstep (se 1 (by rfl) ⟨791504, by rfl⟩ : syracuseStep 1055339 = 1583009) B1583009
theorem B1055351 : Blo 1052612 1055351 := bstep (se 1 (by rfl) ⟨791513, by rfl⟩ : syracuseStep 1055351 = 1583027) B1583027
theorem B1055371 : Blo 1052612 1055371 := bstep (se 1 (by rfl) ⟨791528, by rfl⟩ : syracuseStep 1055371 = 1583057) B1583057
theorem B1055383 : Blo 1052612 1055383 := bstep (se 1 (by rfl) ⟨791537, by rfl⟩ : syracuseStep 1055383 = 1583075) B1583075
theorem B1579673 : Blo 1052612 1579673 := bstep (se 2 (by rfl) ⟨592377, by rfl⟩ : syracuseStep 1579673 = 1184755) B1184755
theorem B1055403 : Blo 1052612 1055403 := bstep (se 1 (by rfl) ⟨791552, by rfl⟩ : syracuseStep 1055403 = 1583105) B1583105
theorem B1055415 : Blo 1052612 1055415 := bstep (se 1 (by rfl) ⟨791561, by rfl⟩ : syracuseStep 1055415 = 1583123) B1583123
theorem B1055435 : Blo 1052612 1055435 := bstep (se 1 (by rfl) ⟨791576, by rfl⟩ : syracuseStep 1055435 = 1583153) B1583153
theorem B1776343 : Blo 1052612 1776343 := bstep (se 1 (by rfl) ⟨1332257, by rfl⟩ : syracuseStep 1776343 = 2664515) B2664515
theorem B1186519 : Blo 1052612 1186519 := bstep (se 1 (by rfl) ⟨889889, by rfl⟩ : syracuseStep 1186519 = 1779779) B1779779
theorem B1055447 : Blo 1052612 1055447 := bstep (se 1 (by rfl) ⟨791585, by rfl⟩ : syracuseStep 1055447 = 1583171) B1583171
theorem B1055467 : Blo 1052612 1055467 := bstep (se 1 (by rfl) ⟨791600, by rfl⟩ : syracuseStep 1055467 = 1583201) B1583201
theorem B1055479 : Blo 1052612 1055479 := bstep (se 1 (by rfl) ⟨791609, by rfl⟩ : syracuseStep 1055479 = 1583219) B1583219
theorem B1579787 : Blo 1052612 1579787 := bstep (se 1 (by rfl) ⟨1184840, by rfl⟩ : syracuseStep 1579787 = 2369681) B2369681
theorem B1055499 : Blo 1052612 1055499 := bstep (se 1 (by rfl) ⟨791624, by rfl⟩ : syracuseStep 1055499 = 1583249) B1583249
theorem B1579799 : Blo 1052612 1579799 := bstep (se 1 (by rfl) ⟨1184849, by rfl⟩ : syracuseStep 1579799 = 2369699) B2369699
theorem B1055511 : Blo 1052612 1055511 := bstep (se 1 (by rfl) ⟨791633, by rfl⟩ : syracuseStep 1055511 = 1583267) B1583267
theorem B1055531 : Blo 1052612 1055531 := bstep (se 1 (by rfl) ⟨791648, by rfl⟩ : syracuseStep 1055531 = 1583297) B1583297
theorem B1055543 : Blo 1052612 1055543 := bstep (se 1 (by rfl) ⟨791657, by rfl⟩ : syracuseStep 1055543 = 1583315) B1583315
theorem B10132289 : Blo 1052612 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B1055563 : Blo 1052612 1055563 := bstep (se 1 (by rfl) ⟨791672, by rfl⟩ : syracuseStep 1055563 = 1583345) B1583345
theorem B1055575 : Blo 1052612 1055575 := bstep (se 1 (by rfl) ⟨791681, by rfl⟩ : syracuseStep 1055575 = 1583363) B1583363
theorem B1579865 : Blo 1052612 1579865 := bstep (se 2 (by rfl) ⟨592449, by rfl⟩ : syracuseStep 1579865 = 1184899) B1184899
theorem B1055595 : Blo 1052612 1055595 := bstep (se 1 (by rfl) ⟨791696, by rfl⟩ : syracuseStep 1055595 = 1583393) B1583393
theorem B1055607 : Blo 1052612 1055607 := bstep (se 1 (by rfl) ⟨791705, by rfl⟩ : syracuseStep 1055607 = 1583411) B1583411
theorem B1186699 : Blo 1052612 1186699 := bstep (se 1 (by rfl) ⟨890024, by rfl⟩ : syracuseStep 1186699 = 1780049) B1780049
theorem B1055627 : Blo 1052612 1055627 := bstep (se 1 (by rfl) ⟨791720, by rfl⟩ : syracuseStep 1055627 = 1583441) B1583441
theorem B1055639 : Blo 1052612 1055639 := bstep (se 1 (by rfl) ⟨791729, by rfl⟩ : syracuseStep 1055639 = 1583459) B1583459
theorem B1055659 : Blo 1052612 1055659 := bstep (se 1 (by rfl) ⟨791744, by rfl⟩ : syracuseStep 1055659 = 1583489) B1583489
theorem B1055671 : Blo 1052612 1055671 := bstep (se 1 (by rfl) ⟨791753, by rfl⟩ : syracuseStep 1055671 = 1583507) B1583507
theorem B1579979 : Blo 1052612 1579979 := bstep (se 1 (by rfl) ⟨1184984, by rfl⟩ : syracuseStep 1579979 = 2369969) B2369969
theorem B1055691 : Blo 1052612 1055691 := bstep (se 1 (by rfl) ⟨791768, by rfl⟩ : syracuseStep 1055691 = 1583537) B1583537
theorem B1579991 : Blo 1052612 1579991 := bstep (se 1 (by rfl) ⟨1184993, by rfl⟩ : syracuseStep 1579991 = 2369987) B2369987
theorem B1055703 : Blo 1052612 1055703 := bstep (se 1 (by rfl) ⟨791777, by rfl⟩ : syracuseStep 1055703 = 1583555) B1583555
theorem B1055723 : Blo 1052612 1055723 := bstep (se 1 (by rfl) ⟨791792, by rfl⟩ : syracuseStep 1055723 = 1583585) B1583585
theorem B1186807 : Blo 1052612 1186807 := bstep (se 1 (by rfl) ⟨890105, by rfl⟩ : syracuseStep 1186807 = 1780211) B1780211
theorem B1055735 : Blo 1052612 1055735 := bstep (se 1 (by rfl) ⟨791801, by rfl⟩ : syracuseStep 1055735 = 1583603) B1583603
theorem B1055755 : Blo 1052612 1055755 := bstep (se 1 (by rfl) ⟨791816, by rfl⟩ : syracuseStep 1055755 = 1583633) B1583633
theorem B1055767 : Blo 1052612 1055767 := bstep (se 1 (by rfl) ⟨791825, by rfl⟩ : syracuseStep 1055767 = 1583651) B1583651
theorem B1580057 : Blo 1052612 1580057 := bstep (se 2 (by rfl) ⟨592521, by rfl⟩ : syracuseStep 1580057 = 1185043) B1185043
theorem B1055787 : Blo 1052612 1055787 := bstep (se 1 (by rfl) ⟨791840, by rfl⟩ : syracuseStep 1055787 = 1583681) B1583681
theorem B3611699 : Blo 1052612 3611699 := bstep (se 1 (by rfl) ⟨2708774, by rfl⟩ : syracuseStep 3611699 = 5417549) B5417549
theorem B1055799 : Blo 1052612 1055799 := bstep (se 1 (by rfl) ⟨791849, by rfl⟩ : syracuseStep 1055799 = 1583699) B1583699
theorem B1055819 : Blo 1052612 1055819 := bstep (se 1 (by rfl) ⟨791864, by rfl⟩ : syracuseStep 1055819 = 1583729) B1583729
theorem B1055831 : Blo 1052612 1055831 := bstep (se 1 (by rfl) ⟨791873, by rfl⟩ : syracuseStep 1055831 = 1583747) B1583747
theorem B1055851 : Blo 1052612 1055851 := bstep (se 1 (by rfl) ⟨791888, by rfl⟩ : syracuseStep 1055851 = 1583777) B1583777
theorem B1055863 : Blo 1052612 1055863 := bstep (se 1 (by rfl) ⟨791897, by rfl⟩ : syracuseStep 1055863 = 1583795) B1583795
theorem B1580171 : Blo 1052612 1580171 := bstep (se 1 (by rfl) ⟨1185128, by rfl⟩ : syracuseStep 1580171 = 2370257) B2370257
theorem B1055883 : Blo 1052612 1055883 := bstep (se 1 (by rfl) ⟨791912, by rfl⟩ : syracuseStep 1055883 = 1583825) B1583825
theorem B1055895 : Blo 1052612 1055895 := bstep (se 1 (by rfl) ⟨791921, by rfl⟩ : syracuseStep 1055895 = 1583843) B1583843
theorem B1580183 : Blo 1052612 1580183 := bstep (se 1 (by rfl) ⟨1185137, by rfl⟩ : syracuseStep 1580183 = 2370275) B2370275
theorem B2137241 : Blo 1052612 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B1186987 : Blo 1052612 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B1055915 : Blo 1052612 1055915 := bstep (se 1 (by rfl) ⟨791936, by rfl⟩ : syracuseStep 1055915 = 1583873) B1583873
theorem B1055927 : Blo 1052612 1055927 := bstep (se 1 (by rfl) ⟨791945, by rfl⟩ : syracuseStep 1055927 = 1583891) B1583891
theorem B1055947 : Blo 1052612 1055947 := bstep (se 1 (by rfl) ⟨791960, by rfl⟩ : syracuseStep 1055947 = 1583921) B1583921
theorem B1055959 : Blo 1052612 1055959 := bstep (se 1 (by rfl) ⟨791969, by rfl⟩ : syracuseStep 1055959 = 1583939) B1583939
theorem B1580249 : Blo 1052612 1580249 := bstep (se 2 (by rfl) ⟨592593, by rfl⟩ : syracuseStep 1580249 = 1185187) B1185187
theorem B1055979 : Blo 1052612 1055979 := bstep (se 1 (by rfl) ⟨791984, by rfl⟩ : syracuseStep 1055979 = 1583969) B1583969
theorem B1055991 : Blo 1052612 1055991 := bstep (se 1 (by rfl) ⟨791993, by rfl⟩ : syracuseStep 1055991 = 1583987) B1583987
theorem B1056011 : Blo 1052612 1056011 := bstep (se 1 (by rfl) ⟨792008, by rfl⟩ : syracuseStep 1056011 = 1584017) B1584017
theorem B9018641 : Blo 1052612 9018641 := bstep (se 2 (by rfl) ⟨3381990, by rfl⟩ : syracuseStep 9018641 = 6763981) B6763981
theorem B1187095 : Blo 1052612 1187095 := bstep (se 1 (by rfl) ⟨890321, by rfl⟩ : syracuseStep 1187095 = 1780643) B1780643
theorem B1056023 : Blo 1052612 1056023 := bstep (se 1 (by rfl) ⟨792017, by rfl⟩ : syracuseStep 1056023 = 1584035) B1584035
theorem B1056043 : Blo 1052612 1056043 := bstep (se 1 (by rfl) ⟨792032, by rfl⟩ : syracuseStep 1056043 = 1584065) B1584065
theorem B1056055 : Blo 1052612 1056055 := bstep (se 1 (by rfl) ⟨792041, by rfl⟩ : syracuseStep 1056055 = 1584083) B1584083
theorem B1776971 : Blo 1052612 1776971 := bstep (se 1 (by rfl) ⟨1332728, by rfl⟩ : syracuseStep 1776971 = 2665457) B2665457
theorem B1580363 : Blo 1052612 1580363 := bstep (se 1 (by rfl) ⟨1185272, by rfl⟩ : syracuseStep 1580363 = 2370545) B2370545
theorem B1056075 : Blo 1052612 1056075 := bstep (se 1 (by rfl) ⟨792056, by rfl⟩ : syracuseStep 1056075 = 1584113) B1584113
theorem B1580375 : Blo 1052612 1580375 := bstep (se 1 (by rfl) ⟨1185281, by rfl⟩ : syracuseStep 1580375 = 2370563) B2370563
theorem B1056087 : Blo 1052612 1056087 := bstep (se 1 (by rfl) ⟨792065, by rfl⟩ : syracuseStep 1056087 = 1584131) B1584131
theorem B1056107 : Blo 1052612 1056107 := bstep (se 1 (by rfl) ⟨792080, by rfl⟩ : syracuseStep 1056107 = 1584161) B1584161
theorem B1056119 : Blo 1052612 1056119 := bstep (se 1 (by rfl) ⟨792089, by rfl⟩ : syracuseStep 1056119 = 1584179) B1584179
theorem B1056139 : Blo 1052612 1056139 := bstep (se 1 (by rfl) ⟨792104, by rfl⟩ : syracuseStep 1056139 = 1584209) B1584209
theorem B1056151 : Blo 1052612 1056151 := bstep (se 1 (by rfl) ⟨792113, by rfl⟩ : syracuseStep 1056151 = 1584227) B1584227
theorem B1580441 : Blo 1052612 1580441 := bstep (se 2 (by rfl) ⟨592665, by rfl⟩ : syracuseStep 1580441 = 1185331) B1185331
theorem B1056171 : Blo 1052612 1056171 := bstep (se 1 (by rfl) ⟨792128, by rfl⟩ : syracuseStep 1056171 = 1584257) B1584257
theorem B1056183 : Blo 1052612 1056183 := bstep (se 1 (by rfl) ⟨792137, by rfl⟩ : syracuseStep 1056183 = 1584275) B1584275
theorem B1777099 : Blo 1052612 1777099 := bstep (se 1 (by rfl) ⟨1332824, by rfl⟩ : syracuseStep 1777099 = 2665649) B2665649
theorem B1187275 : Blo 1052612 1187275 := bstep (se 1 (by rfl) ⟨890456, by rfl⟩ : syracuseStep 1187275 = 1780913) B1780913
theorem B1056203 : Blo 1052612 1056203 := bstep (se 1 (by rfl) ⟨792152, by rfl⟩ : syracuseStep 1056203 = 1584305) B1584305
theorem B1056215 : Blo 1052612 1056215 := bstep (se 1 (by rfl) ⟨792161, by rfl⟩ : syracuseStep 1056215 = 1584323) B1584323
theorem B1056235 : Blo 1052612 1056235 := bstep (se 1 (by rfl) ⟨792176, by rfl⟩ : syracuseStep 1056235 = 1584353) B1584353
theorem B1056247 : Blo 1052612 1056247 := bstep (se 1 (by rfl) ⟨792185, by rfl⟩ : syracuseStep 1056247 = 1584371) B1584371
theorem B1580555 : Blo 1052612 1580555 := bstep (se 1 (by rfl) ⟨1185416, by rfl⟩ : syracuseStep 1580555 = 2370833) B2370833
theorem B1056267 : Blo 1052612 1056267 := bstep (se 1 (by rfl) ⟨792200, by rfl⟩ : syracuseStep 1056267 = 1584401) B1584401
theorem B1580567 : Blo 1052612 1580567 := bstep (se 1 (by rfl) ⟨1185425, by rfl⟩ : syracuseStep 1580567 = 2370851) B2370851
theorem B1056279 : Blo 1052612 1056279 := bstep (se 1 (by rfl) ⟨792209, by rfl⟩ : syracuseStep 1056279 = 1584419) B1584419
theorem B1056299 : Blo 1052612 1056299 := bstep (se 1 (by rfl) ⟨792224, by rfl⟩ : syracuseStep 1056299 = 1584449) B1584449
theorem B1187383 : Blo 1052612 1187383 := bstep (se 1 (by rfl) ⟨890537, by rfl⟩ : syracuseStep 1187383 = 1781075) B1781075
theorem B1056311 : Blo 1052612 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B1056331 : Blo 1052612 1056331 := bstep (se 1 (by rfl) ⟨792248, by rfl⟩ : syracuseStep 1056331 = 1584497) B1584497
theorem B1056343 : Blo 1052612 1056343 := bstep (se 1 (by rfl) ⟨792257, by rfl⟩ : syracuseStep 1056343 = 1584515) B1584515
theorem B1777241 : Blo 1052612 1777241 := bstep (se 2 (by rfl) ⟨666465, by rfl⟩ : syracuseStep 1777241 = 1332931) B1332931
theorem B1580633 : Blo 1052612 1580633 := bstep (se 2 (by rfl) ⟨592737, by rfl⟩ : syracuseStep 1580633 = 1185475) B1185475
theorem B1056363 : Blo 1052612 1056363 := bstep (se 1 (by rfl) ⟨792272, by rfl⟩ : syracuseStep 1056363 = 1584545) B1584545
theorem B1056375 : Blo 1052612 1056375 := bstep (se 1 (by rfl) ⟨792281, by rfl⟩ : syracuseStep 1056375 = 1584563) B1584563
theorem B1056395 : Blo 1052612 1056395 := bstep (se 1 (by rfl) ⟨792296, by rfl⟩ : syracuseStep 1056395 = 1584593) B1584593
theorem B4005521 : Blo 1052612 4005521 := bstep (se 2 (by rfl) ⟨1502070, by rfl⟩ : syracuseStep 4005521 = 3004141) B3004141
theorem B1056407 : Blo 1052612 1056407 := bstep (se 1 (by rfl) ⟨792305, by rfl⟩ : syracuseStep 1056407 = 1584611) B1584611
theorem B1056427 : Blo 1052612 1056427 := bstep (se 1 (by rfl) ⟨792320, by rfl⟩ : syracuseStep 1056427 = 1584641) B1584641
theorem B1056439 : Blo 1052612 1056439 := bstep (se 1 (by rfl) ⟨792329, by rfl⟩ : syracuseStep 1056439 = 1584659) B1584659
theorem B1580747 : Blo 1052612 1580747 := bstep (se 1 (by rfl) ⟨1185560, by rfl⟩ : syracuseStep 1580747 = 2371121) B2371121
theorem B1056459 : Blo 1052612 1056459 := bstep (se 1 (by rfl) ⟨792344, by rfl⟩ : syracuseStep 1056459 = 1584689) B1584689
theorem B1580759 : Blo 1052612 1580759 := bstep (se 1 (by rfl) ⟨1185569, by rfl⟩ : syracuseStep 1580759 = 2371139) B2371139
theorem B1056471 : Blo 1052612 1056471 := bstep (se 1 (by rfl) ⟨792353, by rfl⟩ : syracuseStep 1056471 = 1584707) B1584707
theorem B1777369 : Blo 1052612 1777369 := bstep (se 2 (by rfl) ⟨666513, by rfl⟩ : syracuseStep 1777369 = 1333027) B1333027
theorem B3383005 : Blo 1052612 3383005 := bstep (se 3 (by rfl) ⟨634313, by rfl⟩ : syracuseStep 3383005 = 1268627) B1268627
theorem B1187563 : Blo 1052612 1187563 := bstep (se 1 (by rfl) ⟨890672, by rfl⟩ : syracuseStep 1187563 = 1781345) B1781345
theorem B1056491 : Blo 1052612 1056491 := bstep (se 1 (by rfl) ⟨792368, by rfl⟩ : syracuseStep 1056491 = 1584737) B1584737
theorem B1056503 : Blo 1052612 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B1056523 : Blo 1052612 1056523 := bstep (se 1 (by rfl) ⟨792392, by rfl⟩ : syracuseStep 1056523 = 1584785) B1584785
theorem B1056535 : Blo 1052612 1056535 := bstep (se 1 (by rfl) ⟨792401, by rfl⟩ : syracuseStep 1056535 = 1584803) B1584803
theorem B1580825 : Blo 1052612 1580825 := bstep (se 2 (by rfl) ⟨592809, by rfl⟩ : syracuseStep 1580825 = 1185619) B1185619
theorem B1056555 : Blo 1052612 1056555 := bstep (se 1 (by rfl) ⟨792416, by rfl⟩ : syracuseStep 1056555 = 1584833) B1584833
theorem B1056567 : Blo 1052612 1056567 := bstep (se 1 (by rfl) ⟨792425, by rfl⟩ : syracuseStep 1056567 = 1584851) B1584851
theorem B1056587 : Blo 1052612 1056587 := bstep (se 1 (by rfl) ⟨792440, by rfl⟩ : syracuseStep 1056587 = 1584881) B1584881
theorem B1187671 : Blo 1052612 1187671 := bstep (se 1 (by rfl) ⟨890753, by rfl⟩ : syracuseStep 1187671 = 1781507) B1781507
theorem B1056599 : Blo 1052612 1056599 := bstep (se 1 (by rfl) ⟨792449, by rfl⟩ : syracuseStep 1056599 = 1584899) B1584899
theorem B1580939 : Blo 1052612 1580939 := bstep (se 1 (by rfl) ⟨1185704, by rfl⟩ : syracuseStep 1580939 = 2371409) B2371409
theorem B1580951 : Blo 1052612 1580951 := bstep (se 1 (by rfl) ⟨1185713, by rfl⟩ : syracuseStep 1580951 = 2371427) B2371427
theorem B1581017 : Blo 1052612 1581017 := bstep (se 2 (by rfl) ⟨592881, by rfl⟩ : syracuseStep 1581017 = 1185763) B1185763
theorem B1187851 : Blo 1052612 1187851 := bstep (se 1 (by rfl) ⟨890888, by rfl⟩ : syracuseStep 1187851 = 1781777) B1781777
theorem B1581131 : Blo 1052612 1581131 := bstep (se 1 (by rfl) ⟨1185848, by rfl⟩ : syracuseStep 1581131 = 2371697) B2371697
theorem B1581143 : Blo 1052612 1581143 := bstep (se 1 (by rfl) ⟨1185857, by rfl⟩ : syracuseStep 1581143 = 2371715) B2371715
theorem B1187959 : Blo 1052612 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B18260099 : Blo 1052612 18260099 := bstep (se 1 (by rfl) ⟨13695074, by rfl⟩ : syracuseStep 18260099 = 27390149) B27390149
theorem B1581209 : Blo 1052612 1581209 := bstep (se 2 (by rfl) ⟨592953, by rfl⟩ : syracuseStep 1581209 = 1185907) B1185907
theorem B1581323 : Blo 1052612 1581323 := bstep (se 1 (by rfl) ⟨1185992, by rfl⟩ : syracuseStep 1581323 = 2371985) B2371985
theorem B1777943 : Blo 1052612 1777943 := bstep (se 1 (by rfl) ⟨1333457, by rfl⟩ : syracuseStep 1777943 = 2666915) B2666915
theorem B1581335 : Blo 1052612 1581335 := bstep (se 1 (by rfl) ⟨1186001, by rfl⟩ : syracuseStep 1581335 = 2372003) B2372003
theorem B1188139 : Blo 1052612 1188139 := bstep (se 1 (by rfl) ⟨891104, by rfl⟩ : syracuseStep 1188139 = 1782209) B1782209
theorem B4006219 : Blo 1052612 4006219 := bstep (se 1 (by rfl) ⟨3004664, by rfl⟩ : syracuseStep 4006219 = 6009329) B6009329
theorem B1581401 : Blo 1052612 1581401 := bstep (se 2 (by rfl) ⟨593025, by rfl⟩ : syracuseStep 1581401 = 1186051) B1186051
theorem B8003933 : Blo 1052612 8003933 := bstep (se 3 (by rfl) ⟨1500737, by rfl⟩ : syracuseStep 8003933 = 3001475) B3001475
theorem B1778071 : Blo 1052612 1778071 := bstep (se 1 (by rfl) ⟨1333553, by rfl⟩ : syracuseStep 1778071 = 2667107) B2667107
theorem B1188247 : Blo 1052612 1188247 := bstep (se 1 (by rfl) ⟨891185, by rfl⟩ : syracuseStep 1188247 = 1782371) B1782371
theorem B15180209 : Blo 1052612 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B1581515 : Blo 1052612 1581515 := bstep (se 1 (by rfl) ⟨1186136, by rfl⟩ : syracuseStep 1581515 = 2372273) B2372273
theorem B1581527 : Blo 1052612 1581527 := bstep (se 1 (by rfl) ⟨1186145, by rfl⟩ : syracuseStep 1581527 = 2372291) B2372291
theorem B1581593 : Blo 1052612 1581593 := bstep (se 2 (by rfl) ⟨593097, by rfl⟩ : syracuseStep 1581593 = 1186195) B1186195
theorem B1188427 : Blo 1052612 1188427 := bstep (se 1 (by rfl) ⟨891320, by rfl⟩ : syracuseStep 1188427 = 1782641) B1782641
theorem B4006493 : Blo 1052612 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B1581707 : Blo 1052612 1581707 := bstep (se 1 (by rfl) ⟨1186280, by rfl⟩ : syracuseStep 1581707 = 2372561) B2372561
theorem B1581719 : Blo 1052612 1581719 := bstep (se 1 (by rfl) ⟨1186289, by rfl⟩ : syracuseStep 1581719 = 2372579) B2372579
theorem B1188535 : Blo 1052612 1188535 := bstep (se 1 (by rfl) ⟨891401, by rfl⟩ : syracuseStep 1188535 = 1782803) B1782803
theorem B1581785 : Blo 1052612 1581785 := bstep (se 2 (by rfl) ⟨593169, by rfl⟩ : syracuseStep 1581785 = 1186339) B1186339
theorem B1581899 : Blo 1052612 1581899 := bstep (se 1 (by rfl) ⟨1186424, by rfl⟩ : syracuseStep 1581899 = 2372849) B2372849
theorem B1581911 : Blo 1052612 1581911 := bstep (se 1 (by rfl) ⟨1186433, by rfl⟩ : syracuseStep 1581911 = 2372867) B2372867
theorem B2368385 : Blo 1052612 2368385 := bstep (se 2 (by rfl) ⟨888144, by rfl⟩ : syracuseStep 2368385 = 1776289) B1776289
theorem B1581977 : Blo 1052612 1581977 := bstep (se 2 (by rfl) ⟨593241, by rfl⟩ : syracuseStep 1581977 = 1186483) B1186483
theorem B1778699 : Blo 1052612 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B1582091 : Blo 1052612 1582091 := bstep (se 1 (by rfl) ⟨1186568, by rfl⟩ : syracuseStep 1582091 = 2373137) B2373137
theorem B1582103 : Blo 1052612 1582103 := bstep (se 1 (by rfl) ⟨1186577, by rfl⟩ : syracuseStep 1582103 = 2373155) B2373155
theorem B2368601 : Blo 1052612 2368601 := bstep (se 2 (by rfl) ⟨888225, by rfl⟩ : syracuseStep 2368601 = 1776451) B1776451
theorem B1582169 : Blo 1052612 1582169 := bstep (se 2 (by rfl) ⟨593313, by rfl⟩ : syracuseStep 1582169 = 1186627) B1186627
theorem B1778827 : Blo 1052612 1778827 := bstep (se 1 (by rfl) ⟨1334120, by rfl⟩ : syracuseStep 1778827 = 2668241) B2668241
theorem B2368691 : Blo 1052612 2368691 := bstep (se 1 (by rfl) ⟨1776518, by rfl⟩ : syracuseStep 2368691 = 3553037) B3553037
theorem B1582283 : Blo 1052612 1582283 := bstep (se 1 (by rfl) ⟨1186712, by rfl⟩ : syracuseStep 1582283 = 2373425) B2373425
theorem B2368727 : Blo 1052612 2368727 := bstep (se 1 (by rfl) ⟨1776545, by rfl⟩ : syracuseStep 2368727 = 3553091) B3553091
theorem B1582295 : Blo 1052612 1582295 := bstep (se 1 (by rfl) ⟨1186721, by rfl⟩ : syracuseStep 1582295 = 2373443) B2373443
theorem B4007191 : Blo 1052612 4007191 := bstep (se 1 (by rfl) ⟨3005393, by rfl⟩ : syracuseStep 4007191 = 6010787) B6010787
theorem B1778969 : Blo 1052612 1778969 := bstep (se 2 (by rfl) ⟨667113, by rfl⟩ : syracuseStep 1778969 = 1334227) B1334227
theorem B1582361 : Blo 1052612 1582361 := bstep (se 2 (by rfl) ⟨593385, by rfl⟩ : syracuseStep 1582361 = 1186771) B1186771
theorem B2368907 : Blo 1052612 2368907 := bstep (se 1 (by rfl) ⟨1776680, by rfl⟩ : syracuseStep 2368907 = 3553361) B3553361
theorem B1582475 : Blo 1052612 1582475 := bstep (se 1 (by rfl) ⟨1186856, by rfl⟩ : syracuseStep 1582475 = 2373713) B2373713
theorem B1582487 : Blo 1052612 1582487 := bstep (se 1 (by rfl) ⟨1186865, by rfl⟩ : syracuseStep 1582487 = 2373731) B2373731
theorem B1779097 : Blo 1052612 1779097 := bstep (se 2 (by rfl) ⟨667161, by rfl⟩ : syracuseStep 1779097 = 1334323) B1334323
theorem B2368961 : Blo 1052612 2368961 := bstep (se 2 (by rfl) ⟨888360, by rfl⟩ : syracuseStep 2368961 = 1776721) B1776721
theorem B1582553 : Blo 1052612 1582553 := bstep (se 2 (by rfl) ⟨593457, by rfl⟩ : syracuseStep 1582553 = 1186915) B1186915
theorem B31204835 : Blo 1052612 31204835 := bstep (se 1 (by rfl) ⟨23403626, by rfl⟩ : syracuseStep 31204835 = 46807253) B46807253
theorem B1582667 : Blo 1052612 1582667 := bstep (se 1 (by rfl) ⟨1187000, by rfl⟩ : syracuseStep 1582667 = 2374001) B2374001
theorem B1582679 : Blo 1052612 1582679 := bstep (se 1 (by rfl) ⟨1187009, by rfl⟩ : syracuseStep 1582679 = 2374019) B2374019
theorem B2369177 : Blo 1052612 2369177 := bstep (se 2 (by rfl) ⟨888441, by rfl⟩ : syracuseStep 2369177 = 1776883) B1776883
theorem B1582745 : Blo 1052612 1582745 := bstep (se 2 (by rfl) ⟨593529, by rfl⟩ : syracuseStep 1582745 = 1187059) B1187059
theorem B2369267 : Blo 1052612 2369267 := bstep (se 1 (by rfl) ⟨1776950, by rfl⟩ : syracuseStep 2369267 = 3553901) B3553901
theorem B1582859 : Blo 1052612 1582859 := bstep (se 1 (by rfl) ⟨1187144, by rfl⟩ : syracuseStep 1582859 = 2374289) B2374289
theorem B2369303 : Blo 1052612 2369303 := bstep (se 1 (by rfl) ⟨1776977, by rfl⟩ : syracuseStep 2369303 = 3553955) B3553955
theorem B1582871 : Blo 1052612 1582871 := bstep (se 1 (by rfl) ⟨1187153, by rfl⟩ : syracuseStep 1582871 = 2374307) B2374307
theorem B1582937 : Blo 1052612 1582937 := bstep (se 2 (by rfl) ⟨593601, by rfl⟩ : syracuseStep 1582937 = 1187203) B1187203
theorem B2369483 : Blo 1052612 2369483 := bstep (se 1 (by rfl) ⟨1777112, by rfl⟩ : syracuseStep 2369483 = 3554225) B3554225
theorem B1583051 : Blo 1052612 1583051 := bstep (se 1 (by rfl) ⟨1187288, by rfl⟩ : syracuseStep 1583051 = 2374577) B2374577
theorem B1779671 : Blo 1052612 1779671 := bstep (se 1 (by rfl) ⟨1334753, by rfl⟩ : syracuseStep 1779671 = 2669507) B2669507
theorem B1583063 : Blo 1052612 1583063 := bstep (se 1 (by rfl) ⟨1187297, by rfl⟩ : syracuseStep 1583063 = 2374595) B2374595
theorem B2369537 : Blo 1052612 2369537 := bstep (se 2 (by rfl) ⟨888576, by rfl⟩ : syracuseStep 2369537 = 1777153) B1777153
theorem B4499479 : Blo 1052612 4499479 := bstep (se 1 (by rfl) ⟨3374609, by rfl⟩ : syracuseStep 4499479 = 6749219) B6749219
theorem B1583129 : Blo 1052612 1583129 := bstep (se 2 (by rfl) ⟨593673, by rfl⟩ : syracuseStep 1583129 = 1187347) B1187347
theorem B4007981 : Blo 1052612 4007981 := bstep (se 3 (by rfl) ⟨751496, by rfl⟩ : syracuseStep 4007981 = 1502993) B1502993
theorem B1779799 : Blo 1052612 1779799 := bstep (se 1 (by rfl) ⟨1334849, by rfl⟩ : syracuseStep 1779799 = 2669699) B2669699
theorem B4499549 : Blo 1052612 4499549 := bstep (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) B1687331
theorem B1583243 : Blo 1052612 1583243 := bstep (se 1 (by rfl) ⟨1187432, by rfl⟩ : syracuseStep 1583243 = 2374865) B2374865
theorem B1583255 : Blo 1052612 1583255 := bstep (se 1 (by rfl) ⟨1187441, by rfl⟩ : syracuseStep 1583255 = 2374883) B2374883
theorem B9021617 : Blo 1052612 9021617 := bstep (se 2 (by rfl) ⟨3383106, by rfl⟩ : syracuseStep 9021617 = 6766213) B6766213
theorem B2369753 : Blo 1052612 2369753 := bstep (se 2 (by rfl) ⟨888657, by rfl⟩ : syracuseStep 2369753 = 1777315) B1777315
theorem B1583321 : Blo 1052612 1583321 := bstep (se 2 (by rfl) ⟨593745, by rfl⟩ : syracuseStep 1583321 = 1187491) B1187491
theorem B15640877 : Blo 1052612 15640877 := bstep (se 3 (by rfl) ⟨2932664, by rfl⟩ : syracuseStep 15640877 = 5865329) B5865329
theorem B2369843 : Blo 1052612 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B1583435 : Blo 1052612 1583435 := bstep (se 1 (by rfl) ⟨1187576, by rfl⟩ : syracuseStep 1583435 = 2375153) B2375153
theorem B1124695 : Blo 1052612 1124695 := bstep (se 1 (by rfl) ⟨843521, by rfl⟩ : syracuseStep 1124695 = 1687043) B1687043
theorem B2369879 : Blo 1052612 2369879 := bstep (se 1 (by rfl) ⟨1777409, by rfl⟩ : syracuseStep 2369879 = 3554819) B3554819
theorem B1583447 : Blo 1052612 1583447 := bstep (se 1 (by rfl) ⟨1187585, by rfl⟩ : syracuseStep 1583447 = 2375171) B2375171
theorem B1583513 : Blo 1052612 1583513 := bstep (se 2 (by rfl) ⟨593817, by rfl⟩ : syracuseStep 1583513 = 1187635) B1187635
theorem B2370059 : Blo 1052612 2370059 := bstep (se 1 (by rfl) ⟨1777544, by rfl⟩ : syracuseStep 2370059 = 3555089) B3555089
theorem B1583627 : Blo 1052612 1583627 := bstep (se 1 (by rfl) ⟨1187720, by rfl⟩ : syracuseStep 1583627 = 2375441) B2375441
theorem B1583639 : Blo 1052612 1583639 := bstep (se 1 (by rfl) ⟨1187729, by rfl⟩ : syracuseStep 1583639 = 2375459) B2375459
theorem B2370113 : Blo 1052612 2370113 := bstep (se 2 (by rfl) ⟨888792, by rfl⟩ : syracuseStep 2370113 = 1777585) B1777585
theorem B1583705 : Blo 1052612 1583705 := bstep (se 2 (by rfl) ⟨593889, by rfl⟩ : syracuseStep 1583705 = 1187779) B1187779
theorem B2665163 : Blo 1052612 2665163 := bstep (se 1 (by rfl) ⟨1998872, by rfl⟩ : syracuseStep 2665163 = 3997745) B3997745
theorem B1780427 : Blo 1052612 1780427 := bstep (se 1 (by rfl) ⟨1335320, by rfl⟩ : syracuseStep 1780427 = 2670641) B2670641
theorem B1583819 : Blo 1052612 1583819 := bstep (se 1 (by rfl) ⟨1187864, by rfl⟩ : syracuseStep 1583819 = 2375729) B2375729
theorem B1583831 : Blo 1052612 1583831 := bstep (se 1 (by rfl) ⟨1187873, by rfl⟩ : syracuseStep 1583831 = 2375747) B2375747
theorem B2370329 : Blo 1052612 2370329 := bstep (se 2 (by rfl) ⟨888873, by rfl⟩ : syracuseStep 2370329 = 1777747) B1777747
theorem B1583897 : Blo 1052612 1583897 := bstep (se 2 (by rfl) ⟨593961, by rfl⟩ : syracuseStep 1583897 = 1187923) B1187923
theorem B4500299 : Blo 1052612 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B1780555 : Blo 1052612 1780555 := bstep (se 1 (by rfl) ⟨1335416, by rfl⟩ : syracuseStep 1780555 = 2670833) B2670833
theorem B2370419 : Blo 1052612 2370419 := bstep (se 1 (by rfl) ⟨1777814, by rfl⟩ : syracuseStep 2370419 = 3555629) B3555629
theorem B1584011 : Blo 1052612 1584011 := bstep (se 1 (by rfl) ⟨1188008, by rfl⟩ : syracuseStep 1584011 = 2376017) B2376017
theorem B2370455 : Blo 1052612 2370455 := bstep (se 1 (by rfl) ⟨1777841, by rfl⟩ : syracuseStep 2370455 = 3555683) B3555683
theorem B1584023 : Blo 1052612 1584023 := bstep (se 1 (by rfl) ⟨1188017, by rfl⟩ : syracuseStep 1584023 = 2376035) B2376035
theorem B12331993 : Blo 1052612 12331993 := bstep (se 2 (by rfl) ⟨4624497, by rfl⟩ : syracuseStep 12331993 = 9248995) B9248995
theorem B1780697 : Blo 1052612 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B1584089 : Blo 1052612 1584089 := bstep (se 2 (by rfl) ⟨594033, by rfl⟩ : syracuseStep 1584089 = 1188067) B1188067
theorem B2370635 : Blo 1052612 2370635 := bstep (se 1 (by rfl) ⟨1777976, by rfl⟩ : syracuseStep 2370635 = 3555953) B3555953
theorem B1125451 : Blo 1052612 1125451 := bstep (se 1 (by rfl) ⟨844088, by rfl⟩ : syracuseStep 1125451 = 1688177) B1688177
theorem B1584203 : Blo 1052612 1584203 := bstep (se 1 (by rfl) ⟨1188152, by rfl⟩ : syracuseStep 1584203 = 2376305) B2376305
theorem B1584215 : Blo 1052612 1584215 := bstep (se 1 (by rfl) ⟨1188161, by rfl⟩ : syracuseStep 1584215 = 2376323) B2376323
theorem B1780825 : Blo 1052612 1780825 := bstep (se 2 (by rfl) ⟨667809, by rfl⟩ : syracuseStep 1780825 = 1335619) B1335619
theorem B2370689 : Blo 1052612 2370689 := bstep (se 2 (by rfl) ⟨889008, by rfl⟩ : syracuseStep 2370689 = 1778017) B1778017
theorem B1584281 : Blo 1052612 1584281 := bstep (se 2 (by rfl) ⟨594105, by rfl⟩ : syracuseStep 1584281 = 1188211) B1188211
theorem B1584395 : Blo 1052612 1584395 := bstep (se 1 (by rfl) ⟨1188296, by rfl⟩ : syracuseStep 1584395 = 2376593) B2376593
theorem B1584407 : Blo 1052612 1584407 := bstep (se 1 (by rfl) ⟨1188305, by rfl⟩ : syracuseStep 1584407 = 2376611) B2376611
theorem B2370905 : Blo 1052612 2370905 := bstep (se 2 (by rfl) ⟨889089, by rfl⟩ : syracuseStep 2370905 = 1778179) B1778179
theorem B1584473 : Blo 1052612 1584473 := bstep (se 2 (by rfl) ⟨594177, by rfl⟩ : syracuseStep 1584473 = 1188355) B1188355
theorem B34614641 : Blo 1052612 34614641 := bstep (se 2 (by rfl) ⟨12980490, by rfl⟩ : syracuseStep 34614641 = 25960981) B25960981
theorem B2370995 : Blo 1052612 2370995 := bstep (se 1 (by rfl) ⟨1778246, by rfl⟩ : syracuseStep 2370995 = 3556493) B3556493
theorem B4009409 : Blo 1052612 4009409 := bstep (se 2 (by rfl) ⟨1503528, by rfl⟩ : syracuseStep 4009409 = 3007057) B3007057
theorem B1584587 : Blo 1052612 1584587 := bstep (se 1 (by rfl) ⟨1188440, by rfl⟩ : syracuseStep 1584587 = 2376881) B2376881
theorem B2371031 : Blo 1052612 2371031 := bstep (se 1 (by rfl) ⟨1778273, by rfl⟩ : syracuseStep 2371031 = 3556547) B3556547
theorem B1584599 : Blo 1052612 1584599 := bstep (se 1 (by rfl) ⟨1188449, by rfl⟩ : syracuseStep 1584599 = 2376899) B2376899
theorem B1584665 : Blo 1052612 1584665 := bstep (se 2 (by rfl) ⟨594249, by rfl⟩ : syracuseStep 1584665 = 1188499) B1188499
theorem B2371211 : Blo 1052612 2371211 := bstep (se 1 (by rfl) ⟨1778408, by rfl⟩ : syracuseStep 2371211 = 3556817) B3556817
theorem B1584779 : Blo 1052612 1584779 := bstep (se 1 (by rfl) ⟨1188584, by rfl⟩ : syracuseStep 1584779 = 2377169) B2377169
theorem B2666135 : Blo 1052612 2666135 := bstep (se 1 (by rfl) ⟨1999601, by rfl⟩ : syracuseStep 2666135 = 3999203) B3999203
theorem B1781399 : Blo 1052612 1781399 := bstep (se 1 (by rfl) ⟨1336049, by rfl⟩ : syracuseStep 1781399 = 2672099) B2672099
theorem B1584791 : Blo 1052612 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B2371265 : Blo 1052612 2371265 := bstep (se 2 (by rfl) ⟨889224, by rfl⟩ : syracuseStep 2371265 = 1778449) B1778449
theorem B2600651 : Blo 1052612 2600651 := bstep (se 1 (by rfl) ⟨1950488, by rfl⟩ : syracuseStep 2600651 = 3900977) B3900977
theorem B1584857 : Blo 1052612 1584857 := bstep (se 2 (by rfl) ⟨594321, by rfl⟩ : syracuseStep 1584857 = 1188643) B1188643
theorem B1781527 : Blo 1052612 1781527 := bstep (se 1 (by rfl) ⟨1336145, by rfl⟩ : syracuseStep 1781527 = 2672291) B2672291
theorem B6762341 : Blo 1052612 6762341 := bstep (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) B1267939
theorem B2371481 : Blo 1052612 2371481 := bstep (se 2 (by rfl) ⟨889305, by rfl⟩ : syracuseStep 2371481 = 1778611) B1778611
theorem B2371571 : Blo 1052612 2371571 := bstep (se 1 (by rfl) ⟨1778678, by rfl⟩ : syracuseStep 2371571 = 3557357) B3557357
theorem B2371607 : Blo 1052612 2371607 := bstep (se 1 (by rfl) ⟨1778705, by rfl⟩ : syracuseStep 2371607 = 3557411) B3557411
theorem B10137635 : Blo 1052612 10137635 := bstep (se 1 (by rfl) ⟨7603226, by rfl⟩ : syracuseStep 10137635 = 15206453) B15206453
theorem B6009011 : Blo 1052612 6009011 := bstep (se 1 (by rfl) ⟨4506758, by rfl⟩ : syracuseStep 6009011 = 9013517) B9013517
theorem B2371787 : Blo 1052612 2371787 := bstep (se 1 (by rfl) ⟨1778840, by rfl⟩ : syracuseStep 2371787 = 3557681) B3557681
theorem B2371841 : Blo 1052612 2371841 := bstep (se 2 (by rfl) ⟨889440, by rfl⟩ : syracuseStep 2371841 = 1778881) B1778881
theorem B2666803 : Blo 1052612 2666803 := bstep (se 1 (by rfl) ⟨2000102, by rfl⟩ : syracuseStep 2666803 = 4000205) B4000205
theorem B5058881 : Blo 1052612 5058881 := bstep (se 2 (by rfl) ⟨1897080, by rfl⟩ : syracuseStep 5058881 = 3794161) B3794161
theorem B7614785 : Blo 1052612 7614785 := bstep (se 2 (by rfl) ⟨2855544, by rfl⟩ : syracuseStep 7614785 = 5711089) B5711089
theorem B1782155 : Blo 1052612 1782155 := bstep (se 1 (by rfl) ⟨1336616, by rfl⟩ : syracuseStep 1782155 = 2673233) B2673233
theorem B2666945 : Blo 1052612 2666945 := bstep (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) B2000209
theorem B2372057 : Blo 1052612 2372057 := bstep (se 2 (by rfl) ⟨889521, by rfl⟩ : syracuseStep 2372057 = 1779043) B1779043
theorem B8565209 : Blo 1052612 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B1782283 : Blo 1052612 1782283 := bstep (se 1 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 1782283 = 2673425) B2673425
theorem B2372147 : Blo 1052612 2372147 := bstep (se 1 (by rfl) ⟨1779110, by rfl⟩ : syracuseStep 2372147 = 3558221) B3558221
theorem B2372183 : Blo 1052612 2372183 := bstep (se 1 (by rfl) ⟨1779137, by rfl⟩ : syracuseStep 2372183 = 3558275) B3558275
theorem B1782425 : Blo 1052612 1782425 := bstep (se 2 (by rfl) ⟨668409, by rfl⟩ : syracuseStep 1782425 = 1336819) B1336819
theorem B2372363 : Blo 1052612 2372363 := bstep (se 1 (by rfl) ⟨1779272, by rfl⟩ : syracuseStep 2372363 = 3558545) B3558545
theorem B1782553 : Blo 1052612 1782553 := bstep (se 2 (by rfl) ⟨668457, by rfl⟩ : syracuseStep 1782553 = 1336915) B1336915
theorem B2372417 : Blo 1052612 2372417 := bstep (se 2 (by rfl) ⟨889656, by rfl⟩ : syracuseStep 2372417 = 1779313) B1779313
theorem B2405207 : Blo 1052612 2405207 := bstep (se 1 (by rfl) ⟨1803905, by rfl⟩ : syracuseStep 2405207 = 3607811) B3607811
theorem B21672805 : Blo 1052612 21672805 := bstep (se 4 (by rfl) ⟨2031825, by rfl⟩ : syracuseStep 21672805 = 4063651) B4063651
theorem B4010897 : Blo 1052612 4010897 := bstep (se 2 (by rfl) ⟨1504086, by rfl⟩ : syracuseStep 4010897 = 3008173) B3008173
theorem B19215377 : Blo 1052612 19215377 := bstep (se 2 (by rfl) ⟨7205766, by rfl⟩ : syracuseStep 19215377 = 14411533) B14411533
theorem B2372633 : Blo 1052612 2372633 := bstep (se 2 (by rfl) ⟨889737, by rfl⟩ : syracuseStep 2372633 = 1779475) B1779475
theorem B1127467 : Blo 1052612 1127467 := bstep (se 1 (by rfl) ⟨845600, by rfl⟩ : syracuseStep 1127467 = 1691201) B1691201
theorem B2372723 : Blo 1052612 2372723 := bstep (se 1 (by rfl) ⟨1779542, by rfl⟩ : syracuseStep 2372723 = 3559085) B3559085
theorem B32453783 : Blo 1052612 32453783 := bstep (se 1 (by rfl) ⟨24340337, by rfl⟩ : syracuseStep 32453783 = 48680675) B48680675
theorem B2372759 : Blo 1052612 2372759 := bstep (se 1 (by rfl) ⟨1779569, by rfl⟩ : syracuseStep 2372759 = 3559139) B3559139
theorem B2438387 : Blo 1052612 2438387 := bstep (se 1 (by rfl) ⟨1828790, by rfl⟩ : syracuseStep 2438387 = 3657581) B3657581
theorem B3847475 : Blo 1052612 3847475 := bstep (se 1 (by rfl) ⟨2885606, by rfl⟩ : syracuseStep 3847475 = 5771213) B5771213
theorem B2372939 : Blo 1052612 2372939 := bstep (se 1 (by rfl) ⟨1779704, by rfl⟩ : syracuseStep 2372939 = 3559409) B3559409
theorem B4011353 : Blo 1052612 4011353 := bstep (se 2 (by rfl) ⟨1504257, by rfl⟩ : syracuseStep 4011353 = 3008515) B3008515
theorem B3552605 : Blo 1052612 3552605 := bstep (se 3 (by rfl) ⟨666113, by rfl⟩ : syracuseStep 3552605 = 1332227) B1332227
theorem B2372993 : Blo 1052612 2372993 := bstep (se 2 (by rfl) ⟨889872, by rfl⟩ : syracuseStep 2372993 = 1779745) B1779745
theorem B9614771 : Blo 1052612 9614771 := bstep (se 1 (by rfl) ⟨7211078, by rfl⟩ : syracuseStep 9614771 = 14422157) B14422157
theorem B4011565 : Blo 1052612 4011565 := bstep (se 3 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 4011565 = 1504337) B1504337
theorem B2373209 : Blo 1052612 2373209 := bstep (se 2 (by rfl) ⟨889953, by rfl⟩ : syracuseStep 2373209 = 1779907) B1779907
theorem B12826205 : Blo 1052612 12826205 := bstep (se 3 (by rfl) ⟨2404913, by rfl⟩ : syracuseStep 12826205 = 4809827) B4809827
theorem B6010469 : Blo 1052612 6010469 := bstep (se 4 (by rfl) ⟨563481, by rfl⟩ : syracuseStep 6010469 = 1126963) B1126963
theorem B8566373 : Blo 1052612 8566373 := bstep (se 4 (by rfl) ⟨803097, by rfl⟩ : syracuseStep 8566373 = 1606195) B1606195
theorem B2668211 : Blo 1052612 2668211 := bstep (se 1 (by rfl) ⟨2001158, by rfl⟩ : syracuseStep 2668211 = 4002317) B4002317
theorem B2373299 : Blo 1052612 2373299 := bstep (se 1 (by rfl) ⟨1779974, by rfl⟩ : syracuseStep 2373299 = 3559949) B3559949
theorem B3847873 : Blo 1052612 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B2373335 : Blo 1052612 2373335 := bstep (se 1 (by rfl) ⟨1780001, by rfl⟩ : syracuseStep 2373335 = 3560003) B3560003
theorem B1128215 : Blo 1052612 1128215 := bstep (se 1 (by rfl) ⟨846161, by rfl⟩ : syracuseStep 1128215 = 1692323) B1692323
theorem B2373515 : Blo 1052612 2373515 := bstep (se 1 (by rfl) ⟨1780136, by rfl⟩ : syracuseStep 2373515 = 3560273) B3560273
theorem B5060531 : Blo 1052612 5060531 := bstep (se 1 (by rfl) ⟨3795398, by rfl⟩ : syracuseStep 5060531 = 7590797) B7590797
theorem B2373569 : Blo 1052612 2373569 := bstep (se 2 (by rfl) ⟨890088, by rfl⟩ : syracuseStep 2373569 = 1780177) B1780177
theorem B2701363 : Blo 1052612 2701363 := bstep (se 1 (by rfl) ⟨2026022, by rfl⟩ : syracuseStep 2701363 = 4052045) B4052045
theorem B2373785 : Blo 1052612 2373785 := bstep (se 2 (by rfl) ⟨890169, by rfl⟩ : syracuseStep 2373785 = 1780339) B1780339
theorem B2668747 : Blo 1052612 2668747 := bstep (se 1 (by rfl) ⟨2001560, by rfl⟩ : syracuseStep 2668747 = 4003121) B4003121
theorem B1423577 : Blo 1052612 1423577 := bstep (se 2 (by rfl) ⟨533841, by rfl⟩ : syracuseStep 1423577 = 1067683) B1067683
theorem B2373875 : Blo 1052612 2373875 := bstep (se 1 (by rfl) ⟨1780406, by rfl⟩ : syracuseStep 2373875 = 3560813) B3560813
theorem B2373911 : Blo 1052612 2373911 := bstep (se 1 (by rfl) ⟨1780433, by rfl⟩ : syracuseStep 2373911 = 3560867) B3560867
theorem B4503853 : Blo 1052612 4503853 := bstep (se 3 (by rfl) ⟨844472, by rfl⟩ : syracuseStep 4503853 = 1688945) B1688945
theorem B2668889 : Blo 1052612 2668889 := bstep (se 2 (by rfl) ⟨1000833, by rfl⟩ : syracuseStep 2668889 = 2001667) B2001667
theorem B5421491 : Blo 1052612 5421491 := bstep (se 1 (by rfl) ⟨4066118, by rfl⟩ : syracuseStep 5421491 = 8132237) B8132237
theorem B3553739 : Blo 1052612 3553739 := bstep (se 1 (by rfl) ⟨2665304, by rfl⟩ : syracuseStep 3553739 = 5330609) B5330609
theorem B2374091 : Blo 1052612 2374091 := bstep (se 1 (by rfl) ⟨1780568, by rfl⟩ : syracuseStep 2374091 = 3561137) B3561137
theorem B4504025 : Blo 1052612 4504025 := bstep (se 2 (by rfl) ⟨1689009, by rfl⟩ : syracuseStep 4504025 = 3378019) B3378019
theorem B2374145 : Blo 1052612 2374145 := bstep (se 2 (by rfl) ⟨890304, by rfl⟩ : syracuseStep 2374145 = 1780609) B1780609
theorem B12008087 : Blo 1052612 12008087 := bstep (se 1 (by rfl) ⟨9006065, by rfl⟩ : syracuseStep 12008087 = 18012131) B18012131
theorem B3554009 : Blo 1052612 3554009 := bstep (se 2 (by rfl) ⟨1332753, by rfl⟩ : syracuseStep 3554009 = 2665507) B2665507
theorem B2374361 : Blo 1052612 2374361 := bstep (se 2 (by rfl) ⟨890385, by rfl⟩ : syracuseStep 2374361 = 1780771) B1780771
theorem B2374451 : Blo 1052612 2374451 := bstep (se 1 (by rfl) ⟨1780838, by rfl⟩ : syracuseStep 2374451 = 3561677) B3561677
theorem B2374487 : Blo 1052612 2374487 := bstep (se 1 (by rfl) ⟨1780865, by rfl⟩ : syracuseStep 2374487 = 3561731) B3561731
theorem B2374667 : Blo 1052612 2374667 := bstep (se 1 (by rfl) ⟨1781000, by rfl⟩ : syracuseStep 2374667 = 3562001) B3562001
theorem B2374721 : Blo 1052612 2374721 := bstep (se 2 (by rfl) ⟨890520, by rfl⟩ : syracuseStep 2374721 = 1781041) B1781041
theorem B2669719 : Blo 1052612 2669719 := bstep (se 1 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 2669719 = 4004579) B4004579
theorem B2538647 : Blo 1052612 2538647 := bstep (se 1 (by rfl) ⟨1903985, by rfl⟩ : syracuseStep 2538647 = 3807971) B3807971
theorem B2374937 : Blo 1052612 2374937 := bstep (se 2 (by rfl) ⟨890601, by rfl⟩ : syracuseStep 2374937 = 1781203) B1781203
theorem B2375027 : Blo 1052612 2375027 := bstep (se 1 (by rfl) ⟨1781270, by rfl⟩ : syracuseStep 2375027 = 3562541) B3562541
theorem B14433653 : Blo 1052612 14433653 := bstep (se 5 (by rfl) ⟨676577, by rfl⟩ : syracuseStep 14433653 = 1353155) B1353155
theorem B3554711 : Blo 1052612 3554711 := bstep (se 1 (by rfl) ⟨2666033, by rfl⟩ : syracuseStep 3554711 = 5332067) B5332067
theorem B2375063 : Blo 1052612 2375063 := bstep (se 1 (by rfl) ⟨1781297, by rfl⟩ : syracuseStep 2375063 = 3562595) B3562595
theorem B2670155 : Blo 1052612 2670155 := bstep (se 1 (by rfl) ⟨2002616, by rfl⟩ : syracuseStep 2670155 = 4005233) B4005233
theorem B2375243 : Blo 1052612 2375243 := bstep (se 1 (by rfl) ⟨1781432, by rfl⟩ : syracuseStep 2375243 = 3562865) B3562865
theorem B2375297 : Blo 1052612 2375297 := bstep (se 2 (by rfl) ⟨890736, by rfl⟩ : syracuseStep 2375297 = 1781473) B1781473
theorem B2997911 : Blo 1052612 2997911 := bstep (se 1 (by rfl) ⟨2248433, by rfl⟩ : syracuseStep 2997911 = 4496867) B4496867
theorem B2375513 : Blo 1052612 2375513 := bstep (se 2 (by rfl) ⟨890817, by rfl⟩ : syracuseStep 2375513 = 1781635) B1781635
theorem B3555251 : Blo 1052612 3555251 := bstep (se 1 (by rfl) ⟨2666438, by rfl⟩ : syracuseStep 3555251 = 5332877) B5332877
theorem B2375603 : Blo 1052612 2375603 := bstep (se 1 (by rfl) ⟨1781702, by rfl⟩ : syracuseStep 2375603 = 3563405) B3563405
theorem B2670529 : Blo 1052612 2670529 := bstep (se 2 (by rfl) ⟨1001448, by rfl⟩ : syracuseStep 2670529 = 2002897) B2002897
theorem B2375639 : Blo 1052612 2375639 := bstep (se 1 (by rfl) ⟨1781729, by rfl⟩ : syracuseStep 2375639 = 3563459) B3563459
theorem B5554241 : Blo 1052612 5554241 := bstep (se 2 (by rfl) ⟨2082840, by rfl⟩ : syracuseStep 5554241 = 4165681) B4165681
theorem B4505665 : Blo 1052612 4505665 := bstep (se 2 (by rfl) ⟨1689624, by rfl⟩ : syracuseStep 4505665 = 3379249) B3379249
theorem B2375819 : Blo 1052612 2375819 := bstep (se 1 (by rfl) ⟨1781864, by rfl⟩ : syracuseStep 2375819 = 3563729) B3563729
theorem B8994995 : Blo 1052612 8994995 := bstep (se 1 (by rfl) ⟨6746246, by rfl⟩ : syracuseStep 8994995 = 13492493) B13492493
theorem B3555521 : Blo 1052612 3555521 := bstep (se 2 (by rfl) ⟨1333320, by rfl⟩ : syracuseStep 3555521 = 2666641) B2666641
theorem B2375873 : Blo 1052612 2375873 := bstep (se 2 (by rfl) ⟨890952, by rfl⟩ : syracuseStep 2375873 = 1781905) B1781905
theorem B2572505 : Blo 1052612 2572505 := bstep (se 2 (by rfl) ⟨964689, by rfl⟩ : syracuseStep 2572505 = 1929379) B1929379
theorem B1687895 : Blo 1052612 1687895 := bstep (se 1 (by rfl) ⟨1265921, by rfl⟩ : syracuseStep 1687895 = 2531843) B2531843
theorem B2376089 : Blo 1052612 2376089 := bstep (se 2 (by rfl) ⟨891033, by rfl⟩ : syracuseStep 2376089 = 1782067) B1782067
theorem B2376179 : Blo 1052612 2376179 := bstep (se 1 (by rfl) ⟨1782134, by rfl⟩ : syracuseStep 2376179 = 3564269) B3564269
theorem B1688087 : Blo 1052612 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B2671127 : Blo 1052612 2671127 := bstep (se 1 (by rfl) ⟨2003345, by rfl⟩ : syracuseStep 2671127 = 4006691) B4006691
theorem B2376215 : Blo 1052612 2376215 := bstep (se 1 (by rfl) ⟨1782161, by rfl⟩ : syracuseStep 2376215 = 3564323) B3564323
theorem B8995373 : Blo 1052612 8995373 := bstep (se 3 (by rfl) ⟨1686632, by rfl⟩ : syracuseStep 8995373 = 3373265) B3373265
theorem B2376395 : Blo 1052612 2376395 := bstep (se 1 (by rfl) ⟨1782296, by rfl⟩ : syracuseStep 2376395 = 3564593) B3564593
theorem B3556061 : Blo 1052612 3556061 := bstep (se 3 (by rfl) ⟨666761, by rfl⟩ : syracuseStep 3556061 = 1333523) B1333523
theorem B2376449 : Blo 1052612 2376449 := bstep (se 2 (by rfl) ⟨891168, by rfl⟩ : syracuseStep 2376449 = 1782337) B1782337
theorem B2999243 : Blo 1052612 2999243 := bstep (se 1 (by rfl) ⟨2249432, by rfl⟩ : syracuseStep 2999243 = 4498865) B4498865
theorem B2376665 : Blo 1052612 2376665 := bstep (se 2 (by rfl) ⟨891249, by rfl⟩ : syracuseStep 2376665 = 1782499) B1782499
theorem B2376755 : Blo 1052612 2376755 := bstep (se 1 (by rfl) ⟨1782566, by rfl⟩ : syracuseStep 2376755 = 3565133) B3565133
theorem B2376791 : Blo 1052612 2376791 := bstep (se 1 (by rfl) ⟨1782593, by rfl⟩ : syracuseStep 2376791 = 3565187) B3565187
theorem B4867165 : Blo 1052612 4867165 := bstep (se 3 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 4867165 = 1825187) B1825187
theorem B5063897 : Blo 1052612 5063897 := bstep (se 2 (by rfl) ⟨1898961, by rfl⟩ : syracuseStep 5063897 = 3797923) B3797923
theorem B4277465 : Blo 1052612 4277465 := bstep (se 2 (by rfl) ⟨1604049, by rfl⟩ : syracuseStep 4277465 = 3208099) B3208099
theorem B2376971 : Blo 1052612 2376971 := bstep (se 1 (by rfl) ⟨1782728, by rfl⟩ : syracuseStep 2376971 = 3565457) B3565457
theorem B5063953 : Blo 1052612 5063953 := bstep (se 2 (by rfl) ⟨1898982, by rfl⟩ : syracuseStep 5063953 = 3797965) B3797965
theorem B2671937 : Blo 1052612 2671937 := bstep (se 2 (by rfl) ⟨1001976, by rfl⟩ : syracuseStep 2671937 = 2003953) B2003953
theorem B2377025 : Blo 1052612 2377025 := bstep (se 2 (by rfl) ⟨891384, by rfl⟩ : syracuseStep 2377025 = 1782769) B1782769
theorem B5064067 : Blo 1052612 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B2377241 : Blo 1052612 2377241 := bstep (se 2 (by rfl) ⟨891465, by rfl⟩ : syracuseStep 2377241 = 1782931) B1782931
theorem B2377331 : Blo 1052612 2377331 := bstep (se 1 (by rfl) ⟨1782998, by rfl⟩ : syracuseStep 2377331 = 3565997) B3565997
theorem B2377367 : Blo 1052612 2377367 := bstep (se 1 (by rfl) ⟨1783025, by rfl⟩ : syracuseStep 2377367 = 3566051) B3566051
theorem B4507339 : Blo 1052612 4507339 := bstep (se 1 (by rfl) ⟨3380504, by rfl⟩ : syracuseStep 4507339 = 6761009) B6761009
theorem B18007757 : Blo 1052612 18007757 := bstep (se 3 (by rfl) ⟨3376454, by rfl⟩ : syracuseStep 18007757 = 6752909) B6752909
theorem B1689355 : Blo 1052612 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B3557195 : Blo 1052612 3557195 := bstep (se 1 (by rfl) ⟨2667896, by rfl⟩ : syracuseStep 3557195 = 5335793) B5335793
theorem B2672473 : Blo 1052612 2672473 := bstep (se 2 (by rfl) ⟨1002177, by rfl⟩ : syracuseStep 2672473 = 2004355) B2004355
theorem B20301785 : Blo 1052612 20301785 := bstep (se 2 (by rfl) ⟨7613169, by rfl⟩ : syracuseStep 20301785 = 15226339) B15226339
theorem B4507613 : Blo 1052612 4507613 := bstep (se 3 (by rfl) ⟨845177, by rfl⟩ : syracuseStep 4507613 = 1690355) B1690355
theorem B5720081 : Blo 1052612 5720081 := bstep (se 2 (by rfl) ⟨2145030, by rfl⟩ : syracuseStep 5720081 = 4290061) B4290061
theorem B3557465 : Blo 1052612 3557465 := bstep (se 2 (by rfl) ⟨1334049, by rfl⟩ : syracuseStep 3557465 = 2668099) B2668099
theorem B1689817 : Blo 1052612 1689817 := bstep (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) B1267363
theorem B3852589 : Blo 1052612 3852589 := bstep (se 3 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 3852589 = 1444721) B1444721
theorem B1690073 : Blo 1052612 1690073 := bstep (se 2 (by rfl) ⟨633777, by rfl⟩ : syracuseStep 1690073 = 1267555) B1267555
theorem B3000883 : Blo 1052612 3000883 := bstep (se 1 (by rfl) ⟨2250662, by rfl⟩ : syracuseStep 3000883 = 4501325) B4501325
theorem B3558167 : Blo 1052612 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B2673587 : Blo 1052612 2673587 := bstep (se 1 (by rfl) ⟨2005190, by rfl⟩ : syracuseStep 2673587 = 4010381) B4010381
theorem B8342621 : Blo 1052612 8342621 := bstep (se 3 (by rfl) ⟨1564241, by rfl⟩ : syracuseStep 8342621 = 3128483) B3128483
theorem B2673881 : Blo 1052612 2673881 := bstep (se 2 (by rfl) ⟨1002705, by rfl⟩ : syracuseStep 2673881 = 2005411) B2005411
theorem B6016301 : Blo 1052612 6016301 := bstep (se 3 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 6016301 = 2256113) B2256113
theorem B3558707 : Blo 1052612 3558707 := bstep (se 1 (by rfl) ⟨2669030, by rfl⟩ : syracuseStep 3558707 = 5338061) B5338061
theorem B3558977 : Blo 1052612 3558977 := bstep (se 2 (by rfl) ⟨1334616, by rfl⟩ : syracuseStep 3558977 = 2669233) B2669233
theorem B3001931 : Blo 1052612 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B2248715 : Blo 1052612 2248715 := bstep (se 1 (by rfl) ⟨1686536, by rfl⟩ : syracuseStep 2248715 = 3373073) B3373073
theorem B5328989 : Blo 1052612 5328989 := bstep (se 3 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 5328989 = 1998371) B1998371
theorem B3559517 : Blo 1052612 3559517 := bstep (se 3 (by rfl) ⟨667409, by rfl⟩ : syracuseStep 3559517 = 1334819) B1334819
theorem B4280465 : Blo 1052612 4280465 := bstep (se 2 (by rfl) ⟨1605174, by rfl⟩ : syracuseStep 4280465 = 3210349) B3210349
theorem B1069399 : Blo 1052612 1069399 := bstep (se 1 (by rfl) ⟨802049, by rfl⟩ : syracuseStep 1069399 = 1604099) B1604099
theorem B1233431 : Blo 1052612 1233431 := bstep (se 1 (by rfl) ⟨925073, by rfl⟩ : syracuseStep 1233431 = 1850147) B1850147
theorem B17126261 : Blo 1052612 17126261 := bstep (se 5 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 17126261 = 1605587) B1605587
theorem B2249689 : Blo 1052612 2249689 := bstep (se 2 (by rfl) ⟨843633, by rfl⟩ : syracuseStep 2249689 = 1687267) B1687267
theorem B3003571 : Blo 1052612 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B3560651 : Blo 1052612 3560651 := bstep (se 1 (by rfl) ⟨2670488, by rfl⟩ : syracuseStep 3560651 = 5340977) B5340977
theorem B2249945 : Blo 1052612 2249945 := bstep (se 2 (by rfl) ⟨843729, by rfl⟩ : syracuseStep 2249945 = 1687459) B1687459
theorem B4052369 : Blo 1052612 4052369 := bstep (se 2 (by rfl) ⟨1519638, by rfl⟩ : syracuseStep 4052369 = 3039277) B3039277
theorem B7591319 : Blo 1052612 7591319 := bstep (se 1 (by rfl) ⟨5693489, by rfl⟩ : syracuseStep 7591319 = 11386979) B11386979
theorem B3003799 : Blo 1052612 3003799 := bstep (se 1 (by rfl) ⟨2252849, by rfl⟩ : syracuseStep 3003799 = 4505699) B4505699
theorem B3560921 : Blo 1052612 3560921 := bstep (se 2 (by rfl) ⟨1335345, by rfl⟩ : syracuseStep 3560921 = 2670691) B2670691
theorem B2250355 : Blo 1052612 2250355 := bstep (se 1 (by rfl) ⟨1687766, by rfl⟩ : syracuseStep 2250355 = 3375533) B3375533
theorem B1332875 : Blo 1052612 1332875 := bstep (se 1 (by rfl) ⟨999656, by rfl⟩ : syracuseStep 1332875 = 1999313) B1999313
theorem B10147589 : Blo 1052612 10147589 := bstep (se 4 (by rfl) ⟨951336, by rfl⟩ : syracuseStep 10147589 = 1902673) B1902673
theorem B2316185 : Blo 1052612 2316185 := bstep (se 2 (by rfl) ⟨868569, by rfl⟩ : syracuseStep 2316185 = 1737139) B1737139
theorem B21649477 : Blo 1052612 21649477 := bstep (se 4 (by rfl) ⟨2029638, by rfl⟩ : syracuseStep 21649477 = 4059277) B4059277
theorem B5331095 : Blo 1052612 5331095 := bstep (se 1 (by rfl) ⟨3998321, by rfl⟩ : syracuseStep 5331095 = 7996643) B7996643
theorem B3561623 : Blo 1052612 3561623 := bstep (se 1 (by rfl) ⟨2671217, by rfl⟩ : syracuseStep 3561623 = 5342435) B5342435
theorem B4282541 : Blo 1052612 4282541 := bstep (se 3 (by rfl) ⟨802976, by rfl⟩ : syracuseStep 4282541 = 1605953) B1605953
theorem B5691713 : Blo 1052612 5691713 := bstep (se 2 (by rfl) ⟨2134392, by rfl⟩ : syracuseStep 5691713 = 4268785) B4268785
theorem B2251073 : Blo 1052612 2251073 := bstep (se 2 (by rfl) ⟨844152, by rfl⟩ : syracuseStep 2251073 = 1688305) B1688305
theorem B1333579 : Blo 1052612 1333579 := bstep (se 1 (by rfl) ⟨1000184, by rfl⟩ : syracuseStep 1333579 = 2000369) B2000369
theorem B1333847 : Blo 1052612 1333847 := bstep (se 1 (by rfl) ⟨1000385, by rfl⟩ : syracuseStep 1333847 = 2000771) B2000771
theorem B2251415 : Blo 1052612 2251415 := bstep (se 1 (by rfl) ⟨1688561, by rfl⟩ : syracuseStep 2251415 = 3377123) B3377123
theorem B3562163 : Blo 1052612 3562163 := bstep (se 1 (by rfl) ⟨2671622, by rfl⟩ : syracuseStep 3562163 = 5343245) B5343245
theorem B4512449 : Blo 1052612 4512449 := bstep (se 2 (by rfl) ⟨1692168, by rfl⟩ : syracuseStep 4512449 = 3384337) B3384337
theorem B2251585 : Blo 1052612 2251585 := bstep (se 2 (by rfl) ⟨844344, by rfl⟩ : syracuseStep 2251585 = 1688689) B1688689
theorem B4512601 : Blo 1052612 4512601 := bstep (se 2 (by rfl) ⟨1692225, by rfl⟩ : syracuseStep 4512601 = 3384451) B3384451
theorem B3562433 : Blo 1052612 3562433 := bstep (se 2 (by rfl) ⟨1335912, by rfl⟩ : syracuseStep 3562433 = 2671825) B2671825
theorem B3005657 : Blo 1052612 3005657 := bstep (se 2 (by rfl) ⟨1127121, by rfl⟩ : syracuseStep 3005657 = 2254243) B2254243
theorem B7691537 : Blo 1052612 7691537 := bstep (se 2 (by rfl) ⟨2884326, by rfl⟩ : syracuseStep 7691537 = 5768653) B5768653
theorem B1334551 : Blo 1052612 1334551 := bstep (se 1 (by rfl) ⟨1000913, by rfl⟩ : syracuseStep 1334551 = 2001827) B2001827
theorem B23158133 : Blo 1052612 23158133 := bstep (se 5 (by rfl) ⟨1085537, by rfl⟩ : syracuseStep 23158133 = 2171075) B2171075
theorem B1203607 : Blo 1052612 1203607 := bstep (se 1 (by rfl) ⟨902705, by rfl⟩ : syracuseStep 1203607 = 1805411) B1805411
theorem B3562973 : Blo 1052612 3562973 := bstep (se 3 (by rfl) ⟨668057, by rfl⟩ : syracuseStep 3562973 = 1336115) B1336115
theorem B4284083 : Blo 1052612 4284083 := bstep (se 1 (by rfl) ⟨3213062, by rfl⟩ : syracuseStep 4284083 = 6426125) B6426125
theorem B2252747 : Blo 1052612 2252747 := bstep (se 1 (by rfl) ⟨1689560, by rfl⟩ : syracuseStep 2252747 = 3379121) B3379121
theorem B3006487 : Blo 1052612 3006487 := bstep (se 1 (by rfl) ⟨2254865, by rfl⟩ : syracuseStep 3006487 = 4509731) B4509731
theorem B3203147 : Blo 1052612 3203147 := bstep (se 1 (by rfl) ⟨2402360, by rfl⟩ : syracuseStep 3203147 = 4804721) B4804721
theorem B24371381 : Blo 1052612 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B4055447 : Blo 1052612 4055447 := bstep (se 1 (by rfl) ⟨3041585, by rfl⟩ : syracuseStep 4055447 = 6083171) B6083171
theorem B3203659 : Blo 1052612 3203659 := bstep (se 1 (by rfl) ⟨2402744, by rfl⟩ : syracuseStep 3203659 = 4805489) B4805489
theorem B3564107 : Blo 1052612 3564107 := bstep (se 1 (by rfl) ⟨2673080, by rfl⟩ : syracuseStep 3564107 = 5346161) B5346161
theorem B2253491 : Blo 1052612 2253491 := bstep (se 1 (by rfl) ⟨1690118, by rfl⟩ : syracuseStep 2253491 = 3380237) B3380237
theorem B3007307 : Blo 1052612 3007307 := bstep (se 1 (by rfl) ⟨2255480, by rfl⟩ : syracuseStep 3007307 = 4510961) B4510961
theorem B3564377 : Blo 1052612 3564377 := bstep (se 2 (by rfl) ⟨1336641, by rfl⟩ : syracuseStep 3564377 = 2673283) B2673283
theorem B1336267 : Blo 1052612 1336267 := bstep (se 1 (by rfl) ⟨1002200, by rfl⟩ : syracuseStep 1336267 = 2004401) B2004401
theorem B6415633 : Blo 1052612 6415633 := bstep (se 2 (by rfl) ⟨2405862, by rfl⟩ : syracuseStep 6415633 = 4811725) B4811725
theorem B3565079 : Blo 1052612 3565079 := bstep (se 1 (by rfl) ⟨2673809, by rfl⟩ : syracuseStep 3565079 = 5347619) B5347619
theorem B8119853 : Blo 1052612 8119853 := bstep (se 3 (by rfl) ⟨1522472, by rfl⟩ : syracuseStep 8119853 = 3044945) B3044945
theorem B2254387 : Blo 1052612 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B5334659 : Blo 1052612 5334659 := bstep (se 1 (by rfl) ⟨4000994, by rfl⟩ : syracuseStep 5334659 = 8001989) B8001989
theorem B2057971 : Blo 1052612 2057971 := bstep (se 1 (by rfl) ⟨1543478, by rfl⟩ : syracuseStep 2057971 = 3086957) B3086957
theorem B1337239 : Blo 1052612 1337239 := bstep (se 1 (by rfl) ⟨1002929, by rfl⟩ : syracuseStep 1337239 = 2005859) B2005859
theorem B3565619 : Blo 1052612 3565619 := bstep (se 1 (by rfl) ⟨2674214, by rfl⟩ : syracuseStep 3565619 = 5348429) B5348429
theorem B2058329 : Blo 1052612 2058329 := bstep (se 2 (by rfl) ⟨771873, by rfl⟩ : syracuseStep 2058329 = 1543747) B1543747
theorem B3565889 : Blo 1052612 3565889 := bstep (se 2 (by rfl) ⟨1337208, by rfl⟩ : syracuseStep 3565889 = 2674417) B2674417
theorem B2255447 : Blo 1052612 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B2255617 : Blo 1052612 2255617 := bstep (se 2 (by rfl) ⟨845856, by rfl⟩ : syracuseStep 2255617 = 1691713) B1691713
theorem B13495157 : Blo 1052612 13495157 := bstep (se 5 (by rfl) ⟨632585, by rfl⟩ : syracuseStep 13495157 = 1265171) B1265171
theorem B2255959 : Blo 1052612 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B12021209 : Blo 1052612 12021209 := bstep (se 2 (by rfl) ⟨4507953, by rfl⟩ : syracuseStep 12021209 = 9015907) B9015907
theorem B1928729 : Blo 1052612 1928729 := bstep (se 2 (by rfl) ⟨723273, by rfl⟩ : syracuseStep 1928729 = 1446547) B1446547
theorem B15200045 : Blo 1052612 15200045 := bstep (se 3 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 15200045 = 5700017) B5700017
theorem B1503193 : Blo 1052612 1503193 := bstep (se 2 (by rfl) ⟨563697, by rfl⟩ : syracuseStep 1503193 = 1127395) B1127395
theorem B18280541 : Blo 1052612 18280541 := bstep (se 3 (by rfl) ⟨3427601, by rfl⟩ : syracuseStep 18280541 = 6855203) B6855203
theorem B5075293 : Blo 1052612 5075293 := bstep (se 3 (by rfl) ⟨951617, by rfl⟩ : syracuseStep 5075293 = 1903235) B1903235
theorem B3043801 : Blo 1052612 3043801 := bstep (se 2 (by rfl) ⟨1141425, by rfl⟩ : syracuseStep 3043801 = 2282851) B2282851
theorem B6844945 : Blo 1052612 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B2847577 : Blo 1052612 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B5075891 : Blo 1052612 5075891 := bstep (se 1 (by rfl) ⟨3806918, by rfl⟩ : syracuseStep 5075891 = 7613837) B7613837
theorem B4060205 : Blo 1052612 4060205 := bstep (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) B1522577
theorem B6845515 : Blo 1052612 6845515 := bstep (se 1 (by rfl) ⟨5134136, by rfl⟩ : syracuseStep 6845515 = 10268273) B10268273
theorem B8352973 : Blo 1052612 8352973 := bstep (se 3 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 8352973 = 3132365) B3132365
theorem B5338385 : Blo 1052612 5338385 := bstep (se 2 (by rfl) ⟨2001894, by rfl⟩ : syracuseStep 5338385 = 4003789) B4003789
theorem B5338547 : Blo 1052612 5338547 := bstep (se 1 (by rfl) ⟨4003910, by rfl⟩ : syracuseStep 5338547 = 8007821) B8007821
theorem B1897931 : Blo 1052612 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B3372509 : Blo 1052612 3372509 := bstep (se 3 (by rfl) ⟨632345, by rfl⟩ : syracuseStep 3372509 = 1264691) B1264691
theorem B2848279 : Blo 1052612 2848279 := bstep (se 1 (by rfl) ⟨2136209, by rfl⟩ : syracuseStep 2848279 = 4272419) B4272419
theorem B1898291 : Blo 1052612 1898291 := bstep (se 1 (by rfl) ⟨1423718, by rfl⟩ : syracuseStep 1898291 = 2847437) B2847437
theorem B1898521 : Blo 1052612 1898521 := bstep (se 2 (by rfl) ⟨711945, by rfl⟩ : syracuseStep 1898521 = 1423891) B1423891
theorem B2848961 : Blo 1052612 2848961 := bstep (se 2 (by rfl) ⟨1068360, by rfl⟩ : syracuseStep 2848961 = 2136721) B2136721
theorem B12351809 : Blo 1052612 12351809 := bstep (se 2 (by rfl) ⟨4631928, by rfl⟩ : syracuseStep 12351809 = 9263857) B9263857
theorem B1899083 : Blo 1052612 1899083 := bstep (se 1 (by rfl) ⟨1424312, by rfl⟩ : syracuseStep 1899083 = 2848625) B2848625
theorem B3799811 : Blo 1052612 3799811 := bstep (se 1 (by rfl) ⟨2849858, by rfl⟩ : syracuseStep 3799811 = 5699717) B5699717
theorem B7994213 : Blo 1052612 7994213 := bstep (se 4 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 7994213 = 1498915) B1498915
theorem B3603379 : Blo 1052612 3603379 := bstep (se 1 (by rfl) ⟨2702534, by rfl⟩ : syracuseStep 3603379 = 5405069) B5405069
theorem B3996803 : Blo 1052612 3996803 := bstep (se 1 (by rfl) ⟨2997602, by rfl⟩ : syracuseStep 3996803 = 5995205) B5995205
theorem B4062359 : Blo 1052612 4062359 := bstep (se 1 (by rfl) ⟨3046769, by rfl⟩ : syracuseStep 4062359 = 6093539) B6093539
theorem B7994699 : Blo 1052612 7994699 := bstep (se 1 (by rfl) ⟨5996024, by rfl⟩ : syracuseStep 7994699 = 11992049) B11992049
theorem B5340491 : Blo 1052612 5340491 := bstep (se 1 (by rfl) ⟨4005368, by rfl⟩ : syracuseStep 5340491 = 8010737) B8010737
theorem B4816435 : Blo 1052612 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B3997259 : Blo 1052612 3997259 := bstep (se 1 (by rfl) ⟨2997944, by rfl⟩ : syracuseStep 3997259 = 5995889) B5995889
theorem B1998425 : Blo 1052612 1998425 := bstep (se 2 (by rfl) ⟨749409, by rfl⟩ : syracuseStep 1998425 = 1498819) B1498819
theorem B3210931 : Blo 1052612 3210931 := bstep (se 1 (by rfl) ⟨2408198, by rfl⟩ : syracuseStep 3210931 = 4816397) B4816397
theorem B3997457 : Blo 1052612 3997457 := bstep (se 2 (by rfl) ⟨1499046, by rfl⟩ : syracuseStep 3997457 = 2998093) B2998093
theorem B5996389 : Blo 1052612 5996389 := bstep (se 4 (by rfl) ⟨562161, by rfl⟩ : syracuseStep 5996389 = 1124323) B1124323
theorem B9633667 : Blo 1052612 9633667 := bstep (se 1 (by rfl) ⟨7225250, by rfl⟩ : syracuseStep 9633667 = 14450501) B14450501
theorem B3702827 : Blo 1052612 3702827 := bstep (se 1 (by rfl) ⟨2777120, by rfl⟩ : syracuseStep 3702827 = 5554241) B5554241
theorem B8224829 : Blo 1052612 8224829 := bstep (se 3 (by rfl) ⟨1542155, by rfl⟩ : syracuseStep 8224829 = 3084311) B3084311
theorem B5996663 : Blo 1052612 5996663 := bstep (se 1 (by rfl) ⟨4497497, by rfl⟩ : syracuseStep 5996663 = 8994995) B8994995
theorem B5701751 : Blo 1052612 5701751 := bstep (se 1 (by rfl) ⟨4276313, by rfl⟩ : syracuseStep 5701751 = 8552627) B8552627
theorem B10125445 : Blo 1052612 10125445 := bstep (se 4 (by rfl) ⟨949260, by rfl⟩ : syracuseStep 10125445 = 1898521) B1898521
theorem B61014197 : Blo 1052612 61014197 := bstep (se 5 (by rfl) ⟨2860040, by rfl⟩ : syracuseStep 61014197 = 5720081) B5720081
theorem B5996915 : Blo 1052612 5996915 := bstep (se 1 (by rfl) ⟨4497686, by rfl⟩ : syracuseStep 5996915 = 8995373) B8995373
theorem B5341625 : Blo 1052612 5341625 := bstep (se 2 (by rfl) ⟨2003109, by rfl⟩ : syracuseStep 5341625 = 4006219) B4006219
theorem B1999495 : Blo 1052612 1999495 := bstep (se 1 (by rfl) ⟨1499621, by rfl⟩ : syracuseStep 1999495 = 2999243) B2999243
theorem B3375931 : Blo 1052612 3375931 := bstep (se 1 (by rfl) ⟨2531948, by rfl⟩ : syracuseStep 3375931 = 5063897) B5063897
theorem B2851643 : Blo 1052612 2851643 := bstep (se 1 (by rfl) ⟨2138732, by rfl⟩ : syracuseStep 2851643 = 4277465) B4277465
theorem B13534523 : Blo 1052612 13534523 := bstep (se 1 (by rfl) ⟨10150892, by rfl⟩ : syracuseStep 13534523 = 20301785) B20301785
theorem B6489553 : Blo 1052612 6489553 := bstep (se 2 (by rfl) ⟨2433582, by rfl⟩ : syracuseStep 6489553 = 4867165) B4867165
theorem B2885149 : Blo 1052612 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B3606059 : Blo 1052612 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B6751937 : Blo 1052612 6751937 := bstep (se 2 (by rfl) ⟨2531976, by rfl⟩ : syracuseStep 6751937 = 5063953) B5063953
theorem B8554177 : Blo 1052612 8554177 := bstep (se 2 (by rfl) ⟨3207816, by rfl⟩ : syracuseStep 8554177 = 6415633) B6415633
theorem B5342921 : Blo 1052612 5342921 := bstep (se 2 (by rfl) ⟨2003595, by rfl⟩ : syracuseStep 5342921 = 4007191) B4007191
theorem B5998373 : Blo 1052612 5998373 := bstep (se 4 (by rfl) ⟨562347, by rfl⟩ : syracuseStep 5998373 = 1124695) B1124695
theorem B6752089 : Blo 1052612 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B4327625 : Blo 1052612 4327625 := bstep (se 2 (by rfl) ⟨1622859, by rfl⟩ : syracuseStep 4327625 = 3245719) B3245719
theorem B2001287 : Blo 1052612 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B15600113 : Blo 1052612 15600113 := bstep (se 2 (by rfl) ⟨5850042, by rfl⟩ : syracuseStep 15600113 = 11700085) B11700085
theorem B5999305 : Blo 1052612 5999305 := bstep (se 2 (by rfl) ⟨2249739, by rfl⟩ : syracuseStep 5999305 = 4499479) B4499479
theorem B2853643 : Blo 1052612 2853643 := bstep (se 1 (by rfl) ⟨2140232, by rfl⟩ : syracuseStep 2853643 = 4280465) B4280465
theorem B11406095 : Blo 1052612 11406095 := bstep (se 1 (by rfl) ⟨8554571, by rfl⟩ : syracuseStep 11406095 = 17109143) B17109143
theorem B18025253 : Blo 1052612 18025253 := bstep (se 4 (by rfl) ⟨1689867, by rfl⟩ : syracuseStep 18025253 = 3379735) B3379735
theorem B1903495 : Blo 1052612 1903495 := bstep (se 1 (by rfl) ⟨1427621, by rfl⟩ : syracuseStep 1903495 = 2855243) B2855243
theorem B13896791 : Blo 1052612 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B4001177 : Blo 1052612 4001177 := bstep (se 2 (by rfl) ⟨1500441, by rfl⟩ : syracuseStep 4001177 = 3000883) B3000883
theorem B1544123 : Blo 1052612 1544123 := bstep (se 1 (by rfl) ⟨1158092, by rfl⟩ : syracuseStep 1544123 = 2316185) B2316185
theorem B12029957 : Blo 1052612 12029957 := bstep (se 4 (by rfl) ⟨1127808, by rfl⟩ : syracuseStep 12029957 = 2255617) B2255617
theorem B1052679 : Blo 1052612 1052679 := bstep (se 1 (by rfl) ⟨789509, by rfl⟩ : syracuseStep 1052679 = 1579019) B1579019
theorem B1052687 : Blo 1052612 1052687 := bstep (se 1 (by rfl) ⟨789515, by rfl⟩ : syracuseStep 1052687 = 1579031) B1579031
theorem B1052731 : Blo 1052612 1052731 := bstep (se 1 (by rfl) ⟨789548, by rfl⟩ : syracuseStep 1052731 = 1579097) B1579097
theorem B5705815 : Blo 1052612 5705815 := bstep (se 1 (by rfl) ⟨4279361, by rfl⟩ : syracuseStep 5705815 = 8558723) B8558723
theorem B2855027 : Blo 1052612 2855027 := bstep (se 1 (by rfl) ⟨2141270, by rfl⟩ : syracuseStep 2855027 = 4282541) B4282541
theorem B1052807 : Blo 1052612 1052807 := bstep (se 1 (by rfl) ⟨789605, by rfl⟩ : syracuseStep 1052807 = 1579211) B1579211
theorem B1052815 : Blo 1052612 1052815 := bstep (se 1 (by rfl) ⟨789611, by rfl⟩ : syracuseStep 1052815 = 1579223) B1579223
theorem B1052859 : Blo 1052612 1052859 := bstep (se 1 (by rfl) ⟨789644, by rfl⟩ : syracuseStep 1052859 = 1579289) B1579289
theorem B1052935 : Blo 1052612 1052935 := bstep (se 1 (by rfl) ⟨789701, by rfl⟩ : syracuseStep 1052935 = 1579403) B1579403
theorem B1052943 : Blo 1052612 1052943 := bstep (se 1 (by rfl) ⟨789707, by rfl⟩ : syracuseStep 1052943 = 1579415) B1579415
theorem B1052987 : Blo 1052612 1052987 := bstep (se 1 (by rfl) ⟨789740, by rfl⟩ : syracuseStep 1052987 = 1579481) B1579481
theorem B1053063 : Blo 1052612 1053063 := bstep (se 1 (by rfl) ⟨789797, by rfl⟩ : syracuseStep 1053063 = 1579595) B1579595
theorem B1053071 : Blo 1052612 1053071 := bstep (se 1 (by rfl) ⟨789803, by rfl⟩ : syracuseStep 1053071 = 1579607) B1579607
theorem B1053115 : Blo 1052612 1053115 := bstep (se 1 (by rfl) ⟨789836, by rfl⟩ : syracuseStep 1053115 = 1579673) B1579673
theorem B1053191 : Blo 1052612 1053191 := bstep (se 1 (by rfl) ⟨789893, by rfl⟩ : syracuseStep 1053191 = 1579787) B1579787
theorem B1053199 : Blo 1052612 1053199 := bstep (se 1 (by rfl) ⟨789899, by rfl⟩ : syracuseStep 1053199 = 1579799) B1579799
theorem B6754859 : Blo 1052612 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B1053243 : Blo 1052612 1053243 := bstep (se 1 (by rfl) ⟨789932, by rfl⟩ : syracuseStep 1053243 = 1579865) B1579865
theorem B1053319 : Blo 1052612 1053319 := bstep (se 1 (by rfl) ⟨789989, by rfl⟩ : syracuseStep 1053319 = 1579979) B1579979
theorem B1053327 : Blo 1052612 1053327 := bstep (se 1 (by rfl) ⟨789995, by rfl⟩ : syracuseStep 1053327 = 1579991) B1579991
theorem B1053371 : Blo 1052612 1053371 := bstep (se 1 (by rfl) ⟨790028, by rfl⟩ : syracuseStep 1053371 = 1580057) B1580057
theorem B1053447 : Blo 1052612 1053447 := bstep (se 1 (by rfl) ⟨790085, by rfl⟩ : syracuseStep 1053447 = 1580171) B1580171
theorem B1053455 : Blo 1052612 1053455 := bstep (se 1 (by rfl) ⟨790091, by rfl⟩ : syracuseStep 1053455 = 1580183) B1580183
theorem B1053499 : Blo 1052612 1053499 := bstep (se 1 (by rfl) ⟨790124, by rfl⟩ : syracuseStep 1053499 = 1580249) B1580249
theorem B2003771 : Blo 1052612 2003771 := bstep (se 1 (by rfl) ⟨1502828, by rfl⟩ : syracuseStep 2003771 = 3005657) B3005657
theorem B1184647 : Blo 1052612 1184647 := bstep (se 1 (by rfl) ⟨888485, by rfl⟩ : syracuseStep 1184647 = 1776971) B1776971
theorem B1053575 : Blo 1052612 1053575 := bstep (se 1 (by rfl) ⟨790181, by rfl⟩ : syracuseStep 1053575 = 1580363) B1580363
theorem B1053583 : Blo 1052612 1053583 := bstep (se 1 (by rfl) ⟨790187, by rfl⟩ : syracuseStep 1053583 = 1580375) B1580375
theorem B15438755 : Blo 1052612 15438755 := bstep (se 1 (by rfl) ⟨11579066, by rfl⟩ : syracuseStep 15438755 = 23158133) B23158133
theorem B1053627 : Blo 1052612 1053627 := bstep (se 1 (by rfl) ⟨790220, by rfl⟩ : syracuseStep 1053627 = 1580441) B1580441
theorem B1053703 : Blo 1052612 1053703 := bstep (se 1 (by rfl) ⟨790277, by rfl⟩ : syracuseStep 1053703 = 1580555) B1580555
theorem B1053711 : Blo 1052612 1053711 := bstep (se 1 (by rfl) ⟨790283, by rfl⟩ : syracuseStep 1053711 = 1580567) B1580567
theorem B1184827 : Blo 1052612 1184827 := bstep (se 1 (by rfl) ⟨888620, by rfl⟩ : syracuseStep 1184827 = 1777241) B1777241
theorem B1053755 : Blo 1052612 1053755 := bstep (se 1 (by rfl) ⟨790316, by rfl⟩ : syracuseStep 1053755 = 1580633) B1580633
theorem B2856055 : Blo 1052612 2856055 := bstep (se 1 (by rfl) ⟨2142041, by rfl⟩ : syracuseStep 2856055 = 4284083) B4284083
theorem B1053831 : Blo 1052612 1053831 := bstep (se 1 (by rfl) ⟨790373, by rfl⟩ : syracuseStep 1053831 = 1580747) B1580747
theorem B1053839 : Blo 1052612 1053839 := bstep (se 1 (by rfl) ⟨790379, by rfl⟩ : syracuseStep 1053839 = 1580759) B1580759
theorem B1053883 : Blo 1052612 1053883 := bstep (se 1 (by rfl) ⟨790412, by rfl⟩ : syracuseStep 1053883 = 1580825) B1580825
theorem B1053959 : Blo 1052612 1053959 := bstep (se 1 (by rfl) ⟨790469, by rfl⟩ : syracuseStep 1053959 = 1580939) B1580939
theorem B1053967 : Blo 1052612 1053967 := bstep (se 1 (by rfl) ⟨790475, by rfl⟩ : syracuseStep 1053967 = 1580951) B1580951
theorem B2004257 : Blo 1052612 2004257 := bstep (se 2 (by rfl) ⟨751596, by rfl⟩ : syracuseStep 2004257 = 1503193) B1503193
theorem B1054011 : Blo 1052612 1054011 := bstep (se 1 (by rfl) ⟨790508, by rfl⟩ : syracuseStep 1054011 = 1581017) B1581017
theorem B2135431 : Blo 1052612 2135431 := bstep (se 1 (by rfl) ⟨1601573, by rfl⟩ : syracuseStep 2135431 = 3203147) B3203147
theorem B1054087 : Blo 1052612 1054087 := bstep (se 1 (by rfl) ⟨790565, by rfl⟩ : syracuseStep 1054087 = 1581131) B1581131
theorem B1054095 : Blo 1052612 1054095 := bstep (se 1 (by rfl) ⟨790571, by rfl⟩ : syracuseStep 1054095 = 1581143) B1581143
theorem B1054139 : Blo 1052612 1054139 := bstep (se 1 (by rfl) ⟨790604, by rfl⟩ : syracuseStep 1054139 = 1581209) B1581209
theorem B1054215 : Blo 1052612 1054215 := bstep (se 1 (by rfl) ⟨790661, by rfl⟩ : syracuseStep 1054215 = 1581323) B1581323
theorem B1185295 : Blo 1052612 1185295 := bstep (se 1 (by rfl) ⟨888971, by rfl⟩ : syracuseStep 1185295 = 1777943) B1777943
theorem B1054223 : Blo 1052612 1054223 := bstep (se 1 (by rfl) ⟨790667, by rfl⟩ : syracuseStep 1054223 = 1581335) B1581335
theorem B1054267 : Blo 1052612 1054267 := bstep (se 1 (by rfl) ⟨790700, by rfl⟩ : syracuseStep 1054267 = 1581401) B1581401
theorem B1054343 : Blo 1052612 1054343 := bstep (se 1 (by rfl) ⟨790757, by rfl⟩ : syracuseStep 1054343 = 1581515) B1581515
theorem B1054351 : Blo 1052612 1054351 := bstep (se 1 (by rfl) ⟨790763, by rfl⟩ : syracuseStep 1054351 = 1581527) B1581527
theorem B1054395 : Blo 1052612 1054395 := bstep (se 1 (by rfl) ⟨790796, by rfl⟩ : syracuseStep 1054395 = 1581593) B1581593
theorem B36509413 : Blo 1052612 36509413 := bstep (se 4 (by rfl) ⟨3422757, by rfl⟩ : syracuseStep 36509413 = 6845515) B6845515
theorem B1054471 : Blo 1052612 1054471 := bstep (se 1 (by rfl) ⟨790853, by rfl⟩ : syracuseStep 1054471 = 1581707) B1581707
theorem B1054479 : Blo 1052612 1054479 := bstep (se 1 (by rfl) ⟨790859, by rfl⟩ : syracuseStep 1054479 = 1581719) B1581719
theorem B1054523 : Blo 1052612 1054523 := bstep (se 1 (by rfl) ⟨790892, by rfl⟩ : syracuseStep 1054523 = 1581785) B1581785
theorem B1054599 : Blo 1052612 1054599 := bstep (se 1 (by rfl) ⟨790949, by rfl⟩ : syracuseStep 1054599 = 1581899) B1581899
theorem B1054607 : Blo 1052612 1054607 := bstep (se 1 (by rfl) ⟨790955, by rfl⟩ : syracuseStep 1054607 = 1581911) B1581911
theorem B1578923 : Blo 1052612 1578923 := bstep (se 1 (by rfl) ⟨1184192, by rfl⟩ : syracuseStep 1578923 = 2368385) B2368385
theorem B1054651 : Blo 1052612 1054651 := bstep (se 1 (by rfl) ⟨790988, by rfl⟩ : syracuseStep 1054651 = 1581977) B1581977
theorem B1578953 : Blo 1052612 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B1185799 : Blo 1052612 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B1054727 : Blo 1052612 1054727 := bstep (se 1 (by rfl) ⟨791045, by rfl⟩ : syracuseStep 1054727 = 1582091) B1582091
theorem B1054735 : Blo 1052612 1054735 := bstep (se 1 (by rfl) ⟨791051, by rfl⟩ : syracuseStep 1054735 = 1582103) B1582103
theorem B1579067 : Blo 1052612 1579067 := bstep (se 1 (by rfl) ⟨1184300, by rfl⟩ : syracuseStep 1579067 = 2368601) B2368601
theorem B1054779 : Blo 1052612 1054779 := bstep (se 1 (by rfl) ⟨791084, by rfl⟩ : syracuseStep 1054779 = 1582169) B1582169
theorem B1579127 : Blo 1052612 1579127 := bstep (se 1 (by rfl) ⟨1184345, by rfl⟩ : syracuseStep 1579127 = 2368691) B2368691
theorem B1054855 : Blo 1052612 1054855 := bstep (se 1 (by rfl) ⟨791141, by rfl⟩ : syracuseStep 1054855 = 1582283) B1582283
theorem B1579151 : Blo 1052612 1579151 := bstep (se 1 (by rfl) ⟨1184363, by rfl⟩ : syracuseStep 1579151 = 2368727) B2368727
theorem B1054863 : Blo 1052612 1054863 := bstep (se 1 (by rfl) ⟨791147, by rfl⟩ : syracuseStep 1054863 = 1582295) B1582295
theorem B15177901 : Blo 1052612 15177901 := bstep (se 3 (by rfl) ⟨2845856, by rfl⟩ : syracuseStep 15177901 = 5691713) B5691713
theorem B32938157 : Blo 1052612 32938157 := bstep (se 3 (by rfl) ⟨6175904, by rfl⟩ : syracuseStep 32938157 = 12351809) B12351809
theorem B1579193 : Blo 1052612 1579193 := bstep (se 2 (by rfl) ⟨592197, by rfl⟩ : syracuseStep 1579193 = 1184395) B1184395
theorem B1185979 : Blo 1052612 1185979 := bstep (se 1 (by rfl) ⟨889484, by rfl⟩ : syracuseStep 1185979 = 1778969) B1778969
theorem B1054907 : Blo 1052612 1054907 := bstep (se 1 (by rfl) ⟨791180, by rfl⟩ : syracuseStep 1054907 = 1582361) B1582361
theorem B1579271 : Blo 1052612 1579271 := bstep (se 1 (by rfl) ⟨1184453, by rfl⟩ : syracuseStep 1579271 = 2368907) B2368907
theorem B1054983 : Blo 1052612 1054983 := bstep (se 1 (by rfl) ⟨791237, by rfl⟩ : syracuseStep 1054983 = 1582475) B1582475
theorem B1054991 : Blo 1052612 1054991 := bstep (se 1 (by rfl) ⟨791243, by rfl⟩ : syracuseStep 1054991 = 1582487) B1582487
theorem B1579307 : Blo 1052612 1579307 := bstep (se 1 (by rfl) ⟨1184480, by rfl⟩ : syracuseStep 1579307 = 2368961) B2368961
theorem B1055035 : Blo 1052612 1055035 := bstep (se 1 (by rfl) ⟨791276, by rfl⟩ : syracuseStep 1055035 = 1582553) B1582553
theorem B1579337 : Blo 1052612 1579337 := bstep (se 2 (by rfl) ⟨592251, by rfl⟩ : syracuseStep 1579337 = 1184503) B1184503
theorem B5413235 : Blo 1052612 5413235 := bstep (se 1 (by rfl) ⟨4059926, by rfl⟩ : syracuseStep 5413235 = 8119853) B8119853
theorem B1055111 : Blo 1052612 1055111 := bstep (se 1 (by rfl) ⟨791333, by rfl⟩ : syracuseStep 1055111 = 1582667) B1582667
theorem B1055119 : Blo 1052612 1055119 := bstep (se 1 (by rfl) ⟨791339, by rfl⟩ : syracuseStep 1055119 = 1582679) B1582679
theorem B1579451 : Blo 1052612 1579451 := bstep (se 1 (by rfl) ⟨1184588, by rfl⟩ : syracuseStep 1579451 = 2369177) B2369177
theorem B1055163 : Blo 1052612 1055163 := bstep (se 1 (by rfl) ⟨791372, by rfl⟩ : syracuseStep 1055163 = 1582745) B1582745
theorem B1579511 : Blo 1052612 1579511 := bstep (se 1 (by rfl) ⟨1184633, by rfl⟩ : syracuseStep 1579511 = 2369267) B2369267
theorem B1055239 : Blo 1052612 1055239 := bstep (se 1 (by rfl) ⟨791429, by rfl⟩ : syracuseStep 1055239 = 1582859) B1582859
theorem B1579535 : Blo 1052612 1579535 := bstep (se 1 (by rfl) ⟨1184651, by rfl⟩ : syracuseStep 1579535 = 2369303) B2369303
theorem B1055247 : Blo 1052612 1055247 := bstep (se 1 (by rfl) ⟨791435, by rfl⟩ : syracuseStep 1055247 = 1582871) B1582871
theorem B1579577 : Blo 1052612 1579577 := bstep (se 2 (by rfl) ⟨592341, by rfl⟩ : syracuseStep 1579577 = 1184683) B1184683
theorem B1055291 : Blo 1052612 1055291 := bstep (se 1 (by rfl) ⟨791468, by rfl⟩ : syracuseStep 1055291 = 1582937) B1582937
theorem B1579655 : Blo 1052612 1579655 := bstep (se 1 (by rfl) ⟨1184741, by rfl⟩ : syracuseStep 1579655 = 2369483) B2369483
theorem B1055367 : Blo 1052612 1055367 := bstep (se 1 (by rfl) ⟨791525, by rfl⟩ : syracuseStep 1055367 = 1583051) B1583051
theorem B1055375 : Blo 1052612 1055375 := bstep (se 1 (by rfl) ⟨791531, by rfl⟩ : syracuseStep 1055375 = 1583063) B1583063
theorem B1186447 : Blo 1052612 1186447 := bstep (se 1 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 1186447 = 1779671) B1779671
theorem B1579691 : Blo 1052612 1579691 := bstep (se 1 (by rfl) ⟨1184768, by rfl⟩ : syracuseStep 1579691 = 2369537) B2369537
theorem B1055419 : Blo 1052612 1055419 := bstep (se 1 (by rfl) ⟨791564, by rfl⟩ : syracuseStep 1055419 = 1583129) B1583129
theorem B1579721 : Blo 1052612 1579721 := bstep (se 2 (by rfl) ⟨592395, by rfl⟩ : syracuseStep 1579721 = 1184791) B1184791
theorem B1055495 : Blo 1052612 1055495 := bstep (se 1 (by rfl) ⟨791621, by rfl⟩ : syracuseStep 1055495 = 1583243) B1583243
theorem B1055503 : Blo 1052612 1055503 := bstep (se 1 (by rfl) ⟨791627, by rfl⟩ : syracuseStep 1055503 = 1583255) B1583255
theorem B1579835 : Blo 1052612 1579835 := bstep (se 1 (by rfl) ⟨1184876, by rfl⟩ : syracuseStep 1579835 = 2369753) B2369753
theorem B1055547 : Blo 1052612 1055547 := bstep (se 1 (by rfl) ⟨791660, by rfl⟩ : syracuseStep 1055547 = 1583321) B1583321
theorem B10427251 : Blo 1052612 10427251 := bstep (se 1 (by rfl) ⟨7820438, by rfl⟩ : syracuseStep 10427251 = 15640877) B15640877
theorem B1579895 : Blo 1052612 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B1055623 : Blo 1052612 1055623 := bstep (se 1 (by rfl) ⟨791717, by rfl⟩ : syracuseStep 1055623 = 1583435) B1583435
theorem B1579919 : Blo 1052612 1579919 := bstep (se 1 (by rfl) ⟨1184939, by rfl⟩ : syracuseStep 1579919 = 2369879) B2369879
theorem B1055631 : Blo 1052612 1055631 := bstep (se 1 (by rfl) ⟨791723, by rfl⟩ : syracuseStep 1055631 = 1583447) B1583447
theorem B4004761 : Blo 1052612 4004761 := bstep (se 2 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 4004761 = 3003571) B3003571
theorem B1579961 : Blo 1052612 1579961 := bstep (se 2 (by rfl) ⟨592485, by rfl⟩ : syracuseStep 1579961 = 1184971) B1184971
theorem B1055675 : Blo 1052612 1055675 := bstep (se 1 (by rfl) ⟨791756, by rfl⟩ : syracuseStep 1055675 = 1583513) B1583513
theorem B1580039 : Blo 1052612 1580039 := bstep (se 1 (by rfl) ⟨1185029, by rfl⟩ : syracuseStep 1580039 = 2370059) B2370059
theorem B1055751 : Blo 1052612 1055751 := bstep (se 1 (by rfl) ⟨791813, by rfl⟩ : syracuseStep 1055751 = 1583627) B1583627
theorem B1055759 : Blo 1052612 1055759 := bstep (se 1 (by rfl) ⟨791819, by rfl⟩ : syracuseStep 1055759 = 1583639) B1583639
theorem B1580075 : Blo 1052612 1580075 := bstep (se 1 (by rfl) ⟨1185056, by rfl⟩ : syracuseStep 1580075 = 2370113) B2370113
theorem B1055803 : Blo 1052612 1055803 := bstep (se 1 (by rfl) ⟨791852, by rfl⟩ : syracuseStep 1055803 = 1583705) B1583705
theorem B1580105 : Blo 1052612 1580105 := bstep (se 2 (by rfl) ⟨592539, by rfl⟩ : syracuseStep 1580105 = 1185079) B1185079
theorem B1776775 : Blo 1052612 1776775 := bstep (se 1 (by rfl) ⟨1332581, by rfl⟩ : syracuseStep 1776775 = 2665163) B2665163
theorem B1186951 : Blo 1052612 1186951 := bstep (se 1 (by rfl) ⟨890213, by rfl⟩ : syracuseStep 1186951 = 1780427) B1780427
theorem B1055879 : Blo 1052612 1055879 := bstep (se 1 (by rfl) ⟨791909, by rfl⟩ : syracuseStep 1055879 = 1583819) B1583819
theorem B1055887 : Blo 1052612 1055887 := bstep (se 1 (by rfl) ⟨791915, by rfl⟩ : syracuseStep 1055887 = 1583831) B1583831
theorem B1580219 : Blo 1052612 1580219 := bstep (se 1 (by rfl) ⟨1185164, by rfl⟩ : syracuseStep 1580219 = 2370329) B2370329
theorem B1055931 : Blo 1052612 1055931 := bstep (se 1 (by rfl) ⟨791948, by rfl⟩ : syracuseStep 1055931 = 1583897) B1583897
theorem B4005065 : Blo 1052612 4005065 := bstep (se 2 (by rfl) ⟨1501899, by rfl⟩ : syracuseStep 4005065 = 3003799) B3003799
theorem B1580279 : Blo 1052612 1580279 := bstep (se 1 (by rfl) ⟨1185209, by rfl⟩ : syracuseStep 1580279 = 2370419) B2370419
theorem B1056007 : Blo 1052612 1056007 := bstep (se 1 (by rfl) ⟨792005, by rfl⟩ : syracuseStep 1056007 = 1584011) B1584011
theorem B1580303 : Blo 1052612 1580303 := bstep (se 1 (by rfl) ⟨1185227, by rfl⟩ : syracuseStep 1580303 = 2370455) B2370455
theorem B1056015 : Blo 1052612 1056015 := bstep (se 1 (by rfl) ⟨792011, by rfl⟩ : syracuseStep 1056015 = 1584023) B1584023
theorem B1580345 : Blo 1052612 1580345 := bstep (se 2 (by rfl) ⟨592629, by rfl⟩ : syracuseStep 1580345 = 1185259) B1185259
theorem B1187131 : Blo 1052612 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B1056059 : Blo 1052612 1056059 := bstep (se 1 (by rfl) ⟨792044, by rfl⟩ : syracuseStep 1056059 = 1584089) B1584089
theorem B1580423 : Blo 1052612 1580423 := bstep (se 1 (by rfl) ⟨1185317, by rfl⟩ : syracuseStep 1580423 = 2370635) B2370635
theorem B1056135 : Blo 1052612 1056135 := bstep (se 1 (by rfl) ⟨792101, by rfl⟩ : syracuseStep 1056135 = 1584203) B1584203
theorem B1056143 : Blo 1052612 1056143 := bstep (se 1 (by rfl) ⟨792107, by rfl⟩ : syracuseStep 1056143 = 1584215) B1584215
theorem B8002961 : Blo 1052612 8002961 := bstep (se 2 (by rfl) ⟨3001110, by rfl⟩ : syracuseStep 8002961 = 6002221) B6002221
theorem B5348753 : Blo 1052612 5348753 := bstep (se 2 (by rfl) ⟨2005782, by rfl⟩ : syracuseStep 5348753 = 4011565) B4011565
theorem B1580459 : Blo 1052612 1580459 := bstep (se 1 (by rfl) ⟨1185344, by rfl⟩ : syracuseStep 1580459 = 2370689) B2370689
theorem B1056187 : Blo 1052612 1056187 := bstep (se 1 (by rfl) ⟨792140, by rfl⟩ : syracuseStep 1056187 = 1584281) B1584281
theorem B1580489 : Blo 1052612 1580489 := bstep (se 2 (by rfl) ⟨592683, by rfl⟩ : syracuseStep 1580489 = 1185367) B1185367
theorem B1056263 : Blo 1052612 1056263 := bstep (se 1 (by rfl) ⟨792197, by rfl⟩ : syracuseStep 1056263 = 1584395) B1584395
theorem B1056271 : Blo 1052612 1056271 := bstep (se 1 (by rfl) ⟨792203, by rfl⟩ : syracuseStep 1056271 = 1584407) B1584407
theorem B12000797 : Blo 1052612 12000797 := bstep (se 3 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 12000797 = 4500299) B4500299
theorem B1580603 : Blo 1052612 1580603 := bstep (se 1 (by rfl) ⟨1185452, by rfl⟩ : syracuseStep 1580603 = 2370905) B2370905
theorem B1056315 : Blo 1052612 1056315 := bstep (se 1 (by rfl) ⟨792236, by rfl⟩ : syracuseStep 1056315 = 1584473) B1584473
theorem B23076427 : Blo 1052612 23076427 := bstep (se 1 (by rfl) ⟨17307320, by rfl⟩ : syracuseStep 23076427 = 34614641) B34614641
theorem B1580663 : Blo 1052612 1580663 := bstep (se 1 (by rfl) ⟨1185497, by rfl⟩ : syracuseStep 1580663 = 2370995) B2370995
theorem B1056391 : Blo 1052612 1056391 := bstep (se 1 (by rfl) ⟨792293, by rfl⟩ : syracuseStep 1056391 = 1584587) B1584587
theorem B1580687 : Blo 1052612 1580687 := bstep (se 1 (by rfl) ⟨1185515, by rfl⟩ : syracuseStep 1580687 = 2371031) B2371031
theorem B1056399 : Blo 1052612 1056399 := bstep (se 1 (by rfl) ⟨792299, by rfl⟩ : syracuseStep 1056399 = 1584599) B1584599
theorem B1580729 : Blo 1052612 1580729 := bstep (se 2 (by rfl) ⟨592773, by rfl⟩ : syracuseStep 1580729 = 1185547) B1185547
theorem B1056443 : Blo 1052612 1056443 := bstep (se 1 (by rfl) ⟨792332, by rfl⟩ : syracuseStep 1056443 = 1584665) B1584665
theorem B1580807 : Blo 1052612 1580807 := bstep (se 1 (by rfl) ⟨1185605, by rfl⟩ : syracuseStep 1580807 = 2371211) B2371211
theorem B1056519 : Blo 1052612 1056519 := bstep (se 1 (by rfl) ⟨792389, by rfl⟩ : syracuseStep 1056519 = 1584779) B1584779
theorem B1777423 : Blo 1052612 1777423 := bstep (se 1 (by rfl) ⟨1333067, by rfl⟩ : syracuseStep 1777423 = 2666135) B2666135
theorem B1187599 : Blo 1052612 1187599 := bstep (se 1 (by rfl) ⟨890699, by rfl⟩ : syracuseStep 1187599 = 1781399) B1781399
theorem B1056527 : Blo 1052612 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B1580843 : Blo 1052612 1580843 := bstep (se 1 (by rfl) ⟨1185632, by rfl⟩ : syracuseStep 1580843 = 2371265) B2371265
theorem B1056571 : Blo 1052612 1056571 := bstep (se 1 (by rfl) ⟨792428, by rfl⟩ : syracuseStep 1056571 = 1584857) B1584857
theorem B1580873 : Blo 1052612 1580873 := bstep (se 2 (by rfl) ⟨592827, by rfl⟩ : syracuseStep 1580873 = 1185655) B1185655
theorem B10133363 : Blo 1052612 10133363 := bstep (se 1 (by rfl) ⟨7600022, by rfl⟩ : syracuseStep 10133363 = 15200045) B15200045
theorem B1580987 : Blo 1052612 1580987 := bstep (se 1 (by rfl) ⟨1185740, by rfl⟩ : syracuseStep 1580987 = 2371481) B2371481
theorem B1581047 : Blo 1052612 1581047 := bstep (se 1 (by rfl) ⟨1185785, by rfl⟩ : syracuseStep 1581047 = 2371571) B2371571
theorem B1581071 : Blo 1052612 1581071 := bstep (se 1 (by rfl) ⟨1185803, by rfl⟩ : syracuseStep 1581071 = 2371607) B2371607
theorem B6758423 : Blo 1052612 6758423 := bstep (se 1 (by rfl) ⟨5068817, by rfl⟩ : syracuseStep 6758423 = 10137635) B10137635
theorem B1581113 : Blo 1052612 1581113 := bstep (se 2 (by rfl) ⟨592917, by rfl⟩ : syracuseStep 1581113 = 1185835) B1185835
theorem B4006007 : Blo 1052612 4006007 := bstep (se 1 (by rfl) ⟨3004505, by rfl⟩ : syracuseStep 4006007 = 6009011) B6009011
theorem B1581191 : Blo 1052612 1581191 := bstep (se 1 (by rfl) ⟨1185893, by rfl⟩ : syracuseStep 1581191 = 2371787) B2371787
theorem B1581227 : Blo 1052612 1581227 := bstep (se 1 (by rfl) ⟨1185920, by rfl⟩ : syracuseStep 1581227 = 2371841) B2371841
theorem B1581257 : Blo 1052612 1581257 := bstep (se 2 (by rfl) ⟨592971, by rfl⟩ : syracuseStep 1581257 = 1185943) B1185943
theorem B1188103 : Blo 1052612 1188103 := bstep (se 1 (by rfl) ⟨891077, by rfl⟩ : syracuseStep 1188103 = 1782155) B1782155
theorem B4071713 : Blo 1052612 4071713 := bstep (se 2 (by rfl) ⟨1526892, by rfl⟩ : syracuseStep 4071713 = 3053785) B3053785
theorem B1777963 : Blo 1052612 1777963 := bstep (se 1 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 1777963 = 2666945) B2666945
theorem B1581371 : Blo 1052612 1581371 := bstep (se 1 (by rfl) ⟨1186028, by rfl⟩ : syracuseStep 1581371 = 2372057) B2372057
theorem B5710139 : Blo 1052612 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B1581431 : Blo 1052612 1581431 := bstep (se 1 (by rfl) ⟨1186073, by rfl⟩ : syracuseStep 1581431 = 2372147) B2372147
theorem B1581455 : Blo 1052612 1581455 := bstep (se 1 (by rfl) ⟨1186091, by rfl⟩ : syracuseStep 1581455 = 2372183) B2372183
theorem B6005137 : Blo 1052612 6005137 := bstep (se 2 (by rfl) ⟨2251926, by rfl⟩ : syracuseStep 6005137 = 4503853) B4503853
theorem B1778105 : Blo 1052612 1778105 := bstep (se 2 (by rfl) ⟨666789, by rfl⟩ : syracuseStep 1778105 = 1333579) B1333579
theorem B1581497 : Blo 1052612 1581497 := bstep (se 2 (by rfl) ⟨593061, by rfl⟩ : syracuseStep 1581497 = 1186123) B1186123
theorem B1188283 : Blo 1052612 1188283 := bstep (se 1 (by rfl) ⟨891212, by rfl⟩ : syracuseStep 1188283 = 1782425) B1782425
theorem B1581575 : Blo 1052612 1581575 := bstep (se 1 (by rfl) ⟨1186181, by rfl⟩ : syracuseStep 1581575 = 2372363) B2372363
theorem B1581611 : Blo 1052612 1581611 := bstep (se 1 (by rfl) ⟨1186208, by rfl⟩ : syracuseStep 1581611 = 2372417) B2372417
theorem B1581641 : Blo 1052612 1581641 := bstep (se 2 (by rfl) ⟨593115, by rfl⟩ : syracuseStep 1581641 = 1186231) B1186231
theorem B3383927 : Blo 1052612 3383927 := bstep (se 1 (by rfl) ⟨2537945, by rfl⟩ : syracuseStep 3383927 = 5075891) B5075891
theorem B1581755 : Blo 1052612 1581755 := bstep (se 1 (by rfl) ⟨1186316, by rfl⟩ : syracuseStep 1581755 = 2372633) B2372633
theorem B1581815 : Blo 1052612 1581815 := bstep (se 1 (by rfl) ⟨1186361, by rfl⟩ : syracuseStep 1581815 = 2372723) B2372723
theorem B21635855 : Blo 1052612 21635855 := bstep (se 1 (by rfl) ⟨16226891, by rfl⟩ : syracuseStep 21635855 = 32453783) B32453783
theorem B1581839 : Blo 1052612 1581839 := bstep (se 1 (by rfl) ⟨1186379, by rfl⟩ : syracuseStep 1581839 = 2372759) B2372759
theorem B1581881 : Blo 1052612 1581881 := bstep (se 2 (by rfl) ⟨593205, by rfl⟩ : syracuseStep 1581881 = 1186411) B1186411
theorem B2564983 : Blo 1052612 2564983 := bstep (se 1 (by rfl) ⟨1923737, by rfl⟩ : syracuseStep 2564983 = 3847475) B3847475
theorem B1581959 : Blo 1052612 1581959 := bstep (se 1 (by rfl) ⟨1186469, by rfl⟩ : syracuseStep 1581959 = 2372939) B2372939
theorem B2368403 : Blo 1052612 2368403 := bstep (se 1 (by rfl) ⟨1776302, by rfl⟩ : syracuseStep 2368403 = 3552605) B3552605
theorem B1581995 : Blo 1052612 1581995 := bstep (se 1 (by rfl) ⟨1186496, by rfl⟩ : syracuseStep 1581995 = 2372993) B2372993
theorem B2368457 : Blo 1052612 2368457 := bstep (se 2 (by rfl) ⟨888171, by rfl⟩ : syracuseStep 2368457 = 1776343) B1776343
theorem B1582025 : Blo 1052612 1582025 := bstep (se 2 (by rfl) ⟨593259, by rfl⟩ : syracuseStep 1582025 = 1186519) B1186519
theorem B1582139 : Blo 1052612 1582139 := bstep (se 1 (by rfl) ⟨1186604, by rfl⟩ : syracuseStep 1582139 = 2373209) B2373209
theorem B4006979 : Blo 1052612 4006979 := bstep (se 1 (by rfl) ⟨3005234, by rfl⟩ : syracuseStep 4006979 = 6010469) B6010469
theorem B5710915 : Blo 1052612 5710915 := bstep (se 1 (by rfl) ⟨4283186, by rfl⟩ : syracuseStep 5710915 = 8566373) B8566373
theorem B1778807 : Blo 1052612 1778807 := bstep (se 1 (by rfl) ⟨1334105, by rfl⟩ : syracuseStep 1778807 = 2668211) B2668211
theorem B1582199 : Blo 1052612 1582199 := bstep (se 1 (by rfl) ⟨1186649, by rfl⟩ : syracuseStep 1582199 = 2373299) B2373299
theorem B1582223 : Blo 1052612 1582223 := bstep (se 1 (by rfl) ⟨1186667, by rfl⟩ : syracuseStep 1582223 = 2373335) B2373335
theorem B1582265 : Blo 1052612 1582265 := bstep (se 2 (by rfl) ⟨593349, by rfl⟩ : syracuseStep 1582265 = 1186699) B1186699
theorem B1582343 : Blo 1052612 1582343 := bstep (se 1 (by rfl) ⟨1186757, by rfl⟩ : syracuseStep 1582343 = 2373515) B2373515
theorem B1582379 : Blo 1052612 1582379 := bstep (se 1 (by rfl) ⟨1186784, by rfl⟩ : syracuseStep 1582379 = 2373569) B2373569
theorem B1582409 : Blo 1052612 1582409 := bstep (se 2 (by rfl) ⟨593403, by rfl⟩ : syracuseStep 1582409 = 1186807) B1186807
theorem B1582523 : Blo 1052612 1582523 := bstep (se 1 (by rfl) ⟨1186892, by rfl⟩ : syracuseStep 1582523 = 2373785) B2373785
theorem B1582583 : Blo 1052612 1582583 := bstep (se 1 (by rfl) ⟨1186937, by rfl⟩ : syracuseStep 1582583 = 2373875) B2373875
theorem B1582607 : Blo 1052612 1582607 := bstep (se 1 (by rfl) ⟨1186955, by rfl⟩ : syracuseStep 1582607 = 2373911) B2373911
theorem B1582649 : Blo 1052612 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B1779259 : Blo 1052612 1779259 := bstep (se 1 (by rfl) ⟨1334444, by rfl⟩ : syracuseStep 1779259 = 2668889) B2668889
theorem B3614327 : Blo 1052612 3614327 := bstep (se 1 (by rfl) ⟨2710745, by rfl⟩ : syracuseStep 3614327 = 5421491) B5421491
theorem B2369159 : Blo 1052612 2369159 := bstep (se 1 (by rfl) ⟨1776869, by rfl⟩ : syracuseStep 2369159 = 3553739) B3553739
theorem B1582727 : Blo 1052612 1582727 := bstep (se 1 (by rfl) ⟨1187045, by rfl⟩ : syracuseStep 1582727 = 2374091) B2374091
theorem B1582763 : Blo 1052612 1582763 := bstep (se 1 (by rfl) ⟨1187072, by rfl⟩ : syracuseStep 1582763 = 2374145) B2374145
theorem B1779401 : Blo 1052612 1779401 := bstep (se 2 (by rfl) ⟨667275, by rfl⟩ : syracuseStep 1779401 = 1334551) B1334551
theorem B1582793 : Blo 1052612 1582793 := bstep (se 2 (by rfl) ⟨593547, by rfl⟩ : syracuseStep 1582793 = 1187095) B1187095
theorem B8005391 : Blo 1052612 8005391 := bstep (se 1 (by rfl) ⟨6004043, by rfl⟩ : syracuseStep 8005391 = 12008087) B12008087
theorem B2369339 : Blo 1052612 2369339 := bstep (se 1 (by rfl) ⟨1777004, by rfl⟩ : syracuseStep 2369339 = 3554009) B3554009
theorem B1582907 : Blo 1052612 1582907 := bstep (se 1 (by rfl) ⟨1187180, by rfl⟩ : syracuseStep 1582907 = 2374361) B2374361
theorem B2533207 : Blo 1052612 2533207 := bstep (se 1 (by rfl) ⟨1899905, by rfl⟩ : syracuseStep 2533207 = 3799811) B3799811
theorem B1582967 : Blo 1052612 1582967 := bstep (se 1 (by rfl) ⟨1187225, by rfl⟩ : syracuseStep 1582967 = 2374451) B2374451
theorem B1582991 : Blo 1052612 1582991 := bstep (se 1 (by rfl) ⟨1187243, by rfl⟩ : syracuseStep 1582991 = 2374487) B2374487
theorem B2369465 : Blo 1052612 2369465 := bstep (se 2 (by rfl) ⟨888549, by rfl⟩ : syracuseStep 2369465 = 1777099) B1777099
theorem B1583033 : Blo 1052612 1583033 := bstep (se 2 (by rfl) ⟨593637, by rfl⟩ : syracuseStep 1583033 = 1187275) B1187275
theorem B1583111 : Blo 1052612 1583111 := bstep (se 1 (by rfl) ⟨1187333, by rfl⟩ : syracuseStep 1583111 = 2374667) B2374667
theorem B1583147 : Blo 1052612 1583147 := bstep (se 1 (by rfl) ⟨1187360, by rfl⟩ : syracuseStep 1583147 = 2374721) B2374721
theorem B1583177 : Blo 1052612 1583177 := bstep (se 2 (by rfl) ⟨593691, by rfl⟩ : syracuseStep 1583177 = 1187383) B1187383
theorem B2664535 : Blo 1052612 2664535 := bstep (se 1 (by rfl) ⟨1998401, by rfl⟩ : syracuseStep 2664535 = 3996803) B3996803
theorem B1583291 : Blo 1052612 1583291 := bstep (se 1 (by rfl) ⟨1187468, by rfl⟩ : syracuseStep 1583291 = 2374937) B2374937
theorem B1583351 : Blo 1052612 1583351 := bstep (se 1 (by rfl) ⟨1187513, by rfl⟩ : syracuseStep 1583351 = 2375027) B2375027
theorem B2369807 : Blo 1052612 2369807 := bstep (se 1 (by rfl) ⟨1777355, by rfl⟩ : syracuseStep 2369807 = 3554711) B3554711
theorem B1583375 : Blo 1052612 1583375 := bstep (se 1 (by rfl) ⟨1187531, by rfl⟩ : syracuseStep 1583375 = 2375063) B2375063
theorem B2369825 : Blo 1052612 2369825 := bstep (se 2 (by rfl) ⟨888684, by rfl⟩ : syracuseStep 2369825 = 1777369) B1777369
theorem B1583417 : Blo 1052612 1583417 := bstep (se 2 (by rfl) ⟨593781, by rfl⟩ : syracuseStep 1583417 = 1187563) B1187563
theorem B2664839 : Blo 1052612 2664839 := bstep (se 1 (by rfl) ⟨1998629, by rfl⟩ : syracuseStep 2664839 = 3997259) B3997259
theorem B1780103 : Blo 1052612 1780103 := bstep (se 1 (by rfl) ⟨1335077, by rfl⟩ : syracuseStep 1780103 = 2670155) B2670155
theorem B1583495 : Blo 1052612 1583495 := bstep (se 1 (by rfl) ⟨1187621, by rfl⟩ : syracuseStep 1583495 = 2375243) B2375243
theorem B1583531 : Blo 1052612 1583531 := bstep (se 1 (by rfl) ⟨1187648, by rfl⟩ : syracuseStep 1583531 = 2375297) B2375297
theorem B1583561 : Blo 1052612 1583561 := bstep (se 2 (by rfl) ⟨593835, by rfl⟩ : syracuseStep 1583561 = 1187671) B1187671
theorem B2664971 : Blo 1052612 2664971 := bstep (se 1 (by rfl) ⟨1998728, by rfl⟩ : syracuseStep 2664971 = 3997457) B3997457
theorem B1583675 : Blo 1052612 1583675 := bstep (se 1 (by rfl) ⟨1187756, by rfl⟩ : syracuseStep 1583675 = 2375513) B2375513
theorem B2370167 : Blo 1052612 2370167 := bstep (se 1 (by rfl) ⟨1777625, by rfl⟩ : syracuseStep 2370167 = 3555251) B3555251
theorem B1583735 : Blo 1052612 1583735 := bstep (se 1 (by rfl) ⟨1187801, by rfl⟩ : syracuseStep 1583735 = 2375603) B2375603
theorem B1583759 : Blo 1052612 1583759 := bstep (se 1 (by rfl) ⟨1187819, by rfl⟩ : syracuseStep 1583759 = 2375639) B2375639
theorem B1583801 : Blo 1052612 1583801 := bstep (se 2 (by rfl) ⟨593925, by rfl⟩ : syracuseStep 1583801 = 1187851) B1187851
theorem B2403017 : Blo 1052612 2403017 := bstep (se 2 (by rfl) ⟨901131, by rfl⟩ : syracuseStep 2403017 = 1802263) B1802263
theorem B4008649 : Blo 1052612 4008649 := bstep (se 2 (by rfl) ⟨1503243, by rfl⟩ : syracuseStep 4008649 = 3006487) B3006487
theorem B6007553 : Blo 1052612 6007553 := bstep (se 2 (by rfl) ⟨2252832, by rfl⟩ : syracuseStep 6007553 = 4505665) B4505665
theorem B1583879 : Blo 1052612 1583879 := bstep (se 1 (by rfl) ⟨1187909, by rfl⟩ : syracuseStep 1583879 = 2375819) B2375819
theorem B2370347 : Blo 1052612 2370347 := bstep (se 1 (by rfl) ⟨1777760, by rfl⟩ : syracuseStep 2370347 = 3555521) B3555521
theorem B1583915 : Blo 1052612 1583915 := bstep (se 1 (by rfl) ⟨1187936, by rfl⟩ : syracuseStep 1583915 = 2375873) B2375873
theorem B1715003 : Blo 1052612 1715003 := bstep (se 1 (by rfl) ⟨1286252, by rfl⟩ : syracuseStep 1715003 = 2572505) B2572505
theorem B1583945 : Blo 1052612 1583945 := bstep (se 2 (by rfl) ⟨593979, by rfl⟩ : syracuseStep 1583945 = 1187959) B1187959
theorem B1125263 : Blo 1052612 1125263 := bstep (se 1 (by rfl) ⟨843947, by rfl⟩ : syracuseStep 1125263 = 1687895) B1687895
theorem B1584059 : Blo 1052612 1584059 := bstep (se 1 (by rfl) ⟨1188044, by rfl⟩ : syracuseStep 1584059 = 2376089) B2376089
theorem B1584119 : Blo 1052612 1584119 := bstep (se 1 (by rfl) ⟨1188089, by rfl⟩ : syracuseStep 1584119 = 2376179) B2376179
theorem B2665487 : Blo 1052612 2665487 := bstep (se 1 (by rfl) ⟨1999115, by rfl⟩ : syracuseStep 2665487 = 3998231) B3998231
theorem B1780751 : Blo 1052612 1780751 := bstep (se 1 (by rfl) ⟨1335563, by rfl⟩ : syracuseStep 1780751 = 2671127) B2671127
theorem B1584143 : Blo 1052612 1584143 := bstep (se 1 (by rfl) ⟨1188107, by rfl⟩ : syracuseStep 1584143 = 2376215) B2376215
theorem B1584185 : Blo 1052612 1584185 := bstep (se 2 (by rfl) ⟨594069, by rfl⟩ : syracuseStep 1584185 = 1188139) B1188139
theorem B1584263 : Blo 1052612 1584263 := bstep (se 1 (by rfl) ⟨1188197, by rfl⟩ : syracuseStep 1584263 = 2376395) B2376395
theorem B64990349 : Blo 1052612 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B2665619 : Blo 1052612 2665619 := bstep (se 1 (by rfl) ⟨1999214, by rfl⟩ : syracuseStep 2665619 = 3998429) B3998429
theorem B2370707 : Blo 1052612 2370707 := bstep (se 1 (by rfl) ⟨1778030, by rfl⟩ : syracuseStep 2370707 = 3556061) B3556061
theorem B1584299 : Blo 1052612 1584299 := bstep (se 1 (by rfl) ⟨1188224, by rfl⟩ : syracuseStep 1584299 = 2376449) B2376449
theorem B2370761 : Blo 1052612 2370761 := bstep (se 2 (by rfl) ⟨889035, by rfl⟩ : syracuseStep 2370761 = 1778071) B1778071
theorem B1584329 : Blo 1052612 1584329 := bstep (se 2 (by rfl) ⟨594123, by rfl⟩ : syracuseStep 1584329 = 1188247) B1188247
theorem B1584443 : Blo 1052612 1584443 := bstep (se 1 (by rfl) ⟨1188332, by rfl⟩ : syracuseStep 1584443 = 2376665) B2376665
theorem B1584503 : Blo 1052612 1584503 := bstep (se 1 (by rfl) ⟨1188377, by rfl⟩ : syracuseStep 1584503 = 2376755) B2376755
theorem B1584527 : Blo 1052612 1584527 := bstep (se 1 (by rfl) ⟨1188395, by rfl⟩ : syracuseStep 1584527 = 2376791) B2376791
theorem B4271545 : Blo 1052612 4271545 := bstep (se 2 (by rfl) ⟨1601829, by rfl⟩ : syracuseStep 4271545 = 3203659) B3203659
theorem B1584569 : Blo 1052612 1584569 := bstep (se 2 (by rfl) ⟨594213, by rfl⟩ : syracuseStep 1584569 = 1188427) B1188427
theorem B1584647 : Blo 1052612 1584647 := bstep (se 1 (by rfl) ⟨1188485, by rfl⟩ : syracuseStep 1584647 = 2376971) B2376971
theorem B1781291 : Blo 1052612 1781291 := bstep (se 1 (by rfl) ⟨1335968, by rfl⟩ : syracuseStep 1781291 = 2671937) B2671937
theorem B1584683 : Blo 1052612 1584683 := bstep (se 1 (by rfl) ⟨1188512, by rfl⟩ : syracuseStep 1584683 = 2377025) B2377025
theorem B1584713 : Blo 1052612 1584713 := bstep (se 2 (by rfl) ⟨594267, by rfl⟩ : syracuseStep 1584713 = 1188535) B1188535
theorem B1584827 : Blo 1052612 1584827 := bstep (se 1 (by rfl) ⟨1188620, by rfl⟩ : syracuseStep 1584827 = 2377241) B2377241
theorem B1584887 : Blo 1052612 1584887 := bstep (se 1 (by rfl) ⟨1188665, by rfl⟩ : syracuseStep 1584887 = 2377331) B2377331
theorem B1584911 : Blo 1052612 1584911 := bstep (se 1 (by rfl) ⟨1188683, by rfl⟩ : syracuseStep 1584911 = 2377367) B2377367
theorem B12005171 : Blo 1052612 12005171 := bstep (se 1 (by rfl) ⟨9003878, by rfl⟩ : syracuseStep 12005171 = 18007757) B18007757
theorem B2371463 : Blo 1052612 2371463 := bstep (se 1 (by rfl) ⟨1778597, by rfl⟩ : syracuseStep 2371463 = 3557195) B3557195
theorem B1781689 : Blo 1052612 1781689 := bstep (se 2 (by rfl) ⟨668133, by rfl⟩ : syracuseStep 1781689 = 1336267) B1336267
theorem B2371643 : Blo 1052612 2371643 := bstep (se 1 (by rfl) ⟨1778732, by rfl⟩ : syracuseStep 2371643 = 3557465) B3557465
theorem B4501565 : Blo 1052612 4501565 := bstep (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) B1688087
theorem B2371769 : Blo 1052612 2371769 := bstep (se 2 (by rfl) ⟨889413, by rfl⟩ : syracuseStep 2371769 = 1778827) B1778827
theorem B2666753 : Blo 1052612 2666753 := bstep (se 2 (by rfl) ⟨1000032, by rfl⟩ : syracuseStep 2666753 = 2000065) B2000065
theorem B1126715 : Blo 1052612 1126715 := bstep (se 1 (by rfl) ⟨845036, by rfl⟩ : syracuseStep 1126715 = 1690073) B1690073
theorem B2372111 : Blo 1052612 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B2372129 : Blo 1052612 2372129 := bstep (se 2 (by rfl) ⟨889548, by rfl⟩ : syracuseStep 2372129 = 1779097) B1779097
theorem B2667127 : Blo 1052612 2667127 := bstep (se 1 (by rfl) ⟨2000345, by rfl⟩ : syracuseStep 2667127 = 4000691) B4000691
theorem B1782391 : Blo 1052612 1782391 := bstep (se 1 (by rfl) ⟨1336793, by rfl⟩ : syracuseStep 1782391 = 2673587) B2673587
theorem B1782587 : Blo 1052612 1782587 := bstep (se 1 (by rfl) ⟨1336940, by rfl⟩ : syracuseStep 1782587 = 2673881) B2673881
theorem B4010867 : Blo 1052612 4010867 := bstep (se 1 (by rfl) ⟨3008150, by rfl⟩ : syracuseStep 4010867 = 6016301) B6016301
theorem B2372471 : Blo 1052612 2372471 := bstep (se 1 (by rfl) ⟨1779353, by rfl⟩ : syracuseStep 2372471 = 3558707) B3558707
theorem B6009785 : Blo 1052612 6009785 := bstep (se 2 (by rfl) ⟨2253669, by rfl⟩ : syracuseStep 6009785 = 4507339) B4507339
theorem B2667563 : Blo 1052612 2667563 := bstep (se 1 (by rfl) ⟨2000672, by rfl⟩ : syracuseStep 2667563 = 4001345) B4001345
theorem B2372651 : Blo 1052612 2372651 := bstep (se 1 (by rfl) ⟨1779488, by rfl⟩ : syracuseStep 2372651 = 3558977) B3558977
theorem B16233605 : Blo 1052612 16233605 := bstep (se 4 (by rfl) ⟨1521900, by rfl⟩ : syracuseStep 16233605 = 3043801) B3043801
theorem B1782985 : Blo 1052612 1782985 := bstep (se 2 (by rfl) ⟨668619, by rfl⟩ : syracuseStep 1782985 = 1337239) B1337239
theorem B2536715 : Blo 1052612 2536715 := bstep (se 1 (by rfl) ⟨1902536, by rfl⟩ : syracuseStep 2536715 = 3805073) B3805073
theorem B3552659 : Blo 1052612 3552659 := bstep (se 1 (by rfl) ⟨2664494, by rfl⟩ : syracuseStep 3552659 = 5328989) B5328989
theorem B6403475 : Blo 1052612 6403475 := bstep (se 1 (by rfl) ⟨4802606, by rfl⟩ : syracuseStep 6403475 = 9605213) B9605213
theorem B2373011 : Blo 1052612 2373011 := bstep (se 1 (by rfl) ⟨1779758, by rfl⟩ : syracuseStep 2373011 = 3559517) B3559517
theorem B2373065 : Blo 1052612 2373065 := bstep (se 2 (by rfl) ⟨889899, by rfl⟩ : syracuseStep 2373065 = 1779799) B1779799
theorem B2668403 : Blo 1052612 2668403 := bstep (se 1 (by rfl) ⟨2001302, by rfl⟩ : syracuseStep 2668403 = 4002605) B4002605
theorem B2668423 : Blo 1052612 2668423 := bstep (se 1 (by rfl) ⟨2001317, by rfl⟩ : syracuseStep 2668423 = 4002635) B4002635
theorem B11417507 : Blo 1052612 11417507 := bstep (se 1 (by rfl) ⟨8563130, by rfl⟩ : syracuseStep 11417507 = 17126261) B17126261
theorem B2373767 : Blo 1052612 2373767 := bstep (se 1 (by rfl) ⟨1780325, by rfl⟩ : syracuseStep 2373767 = 3560651) B3560651
theorem B2668697 : Blo 1052612 2668697 := bstep (se 2 (by rfl) ⟨1000761, by rfl⟩ : syracuseStep 2668697 = 2001523) B2001523
theorem B5060879 : Blo 1052612 5060879 := bstep (se 1 (by rfl) ⟨3795659, by rfl⟩ : syracuseStep 5060879 = 7591319) B7591319
theorem B2668859 : Blo 1052612 2668859 := bstep (se 1 (by rfl) ⟨2001644, by rfl⟩ : syracuseStep 2668859 = 4003289) B4003289
theorem B2373947 : Blo 1052612 2373947 := bstep (se 1 (by rfl) ⟨1780460, by rfl⟩ : syracuseStep 2373947 = 3560921) B3560921
theorem B4503923 : Blo 1052612 4503923 := bstep (se 1 (by rfl) ⟨3377942, by rfl⟩ : syracuseStep 4503923 = 6755885) B6755885
theorem B2374073 : Blo 1052612 2374073 := bstep (se 2 (by rfl) ⟨890277, by rfl⟩ : syracuseStep 2374073 = 1780555) B1780555
theorem B6765059 : Blo 1052612 6765059 := bstep (se 1 (by rfl) ⟨5073794, by rfl⟩ : syracuseStep 6765059 = 10147589) B10147589
theorem B2669071 : Blo 1052612 2669071 := bstep (se 1 (by rfl) ⟨2001803, by rfl⟩ : syracuseStep 2669071 = 4003607) B4003607
theorem B3554063 : Blo 1052612 3554063 := bstep (se 1 (by rfl) ⟨2665547, by rfl⟩ : syracuseStep 3554063 = 5331095) B5331095
theorem B2374415 : Blo 1052612 2374415 := bstep (se 1 (by rfl) ⟨1780811, by rfl⟩ : syracuseStep 2374415 = 3561623) B3561623
theorem B2669345 : Blo 1052612 2669345 := bstep (se 2 (by rfl) ⟨1001004, by rfl⟩ : syracuseStep 2669345 = 2002009) B2002009
theorem B2374433 : Blo 1052612 2374433 := bstep (se 2 (by rfl) ⟨890412, by rfl⟩ : syracuseStep 2374433 = 1780825) B1780825
theorem B8567641 : Blo 1052612 8567641 := bstep (se 2 (by rfl) ⟨3212865, by rfl⟩ : syracuseStep 8567641 = 6425731) B6425731
theorem B6011927 : Blo 1052612 6011927 := bstep (se 1 (by rfl) ⟨4508945, by rfl⟩ : syracuseStep 6011927 = 9017891) B9017891
theorem B3554333 : Blo 1052612 3554333 := bstep (se 3 (by rfl) ⟨666437, by rfl⟩ : syracuseStep 3554333 = 1332875) B1332875
theorem B1686587 : Blo 1052612 1686587 := bstep (se 1 (by rfl) ⟨1264940, by rfl⟩ : syracuseStep 1686587 = 2529881) B2529881
theorem B9616445 : Blo 1052612 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B2374775 : Blo 1052612 2374775 := bstep (se 1 (by rfl) ⟨1781081, by rfl⟩ : syracuseStep 2374775 = 3562163) B3562163
theorem B2374955 : Blo 1052612 2374955 := bstep (se 1 (by rfl) ⟨1781216, by rfl⟩ : syracuseStep 2374955 = 3562433) B3562433
theorem B2407799 : Blo 1052612 2407799 := bstep (se 1 (by rfl) ⟨1805849, by rfl⟩ : syracuseStep 2407799 = 3611699) B3611699
theorem B1424827 : Blo 1052612 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B6012427 : Blo 1052612 6012427 := bstep (se 1 (by rfl) ⟨4509320, by rfl⟩ : syracuseStep 6012427 = 9018641) B9018641
theorem B2375315 : Blo 1052612 2375315 := bstep (se 1 (by rfl) ⟨1781486, by rfl⟩ : syracuseStep 2375315 = 3562973) B3562973
theorem B10141361 : Blo 1052612 10141361 := bstep (se 2 (by rfl) ⟨3803010, by rfl⟩ : syracuseStep 10141361 = 7606021) B7606021
theorem B2375369 : Blo 1052612 2375369 := bstep (se 2 (by rfl) ⟨890763, by rfl⟩ : syracuseStep 2375369 = 1781527) B1781527
theorem B2670347 : Blo 1052612 2670347 := bstep (se 1 (by rfl) ⟨2002760, by rfl⟩ : syracuseStep 2670347 = 4005521) B4005521
theorem B12173399 : Blo 1052612 12173399 := bstep (se 1 (by rfl) ⟨9130049, by rfl⟩ : syracuseStep 12173399 = 18260099) B18260099
theorem B5488877 : Blo 1052612 5488877 := bstep (se 3 (by rfl) ⟨1029164, by rfl⟩ : syracuseStep 5488877 = 2058329) B2058329
theorem B13156597 : Blo 1052612 13156597 := bstep (se 5 (by rfl) ⟨616715, by rfl⟩ : syracuseStep 13156597 = 1233431) B1233431
theorem B2703631 : Blo 1052612 2703631 := bstep (se 1 (by rfl) ⟨2027723, by rfl⟩ : syracuseStep 2703631 = 4055447) B4055447
theorem B2376071 : Blo 1052612 2376071 := bstep (se 1 (by rfl) ⟨1782053, by rfl⟩ : syracuseStep 2376071 = 3564107) B3564107
theorem B2670995 : Blo 1052612 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B3555737 : Blo 1052612 3555737 := bstep (se 2 (by rfl) ⟨1333401, by rfl⟩ : syracuseStep 3555737 = 2666803) B2666803
theorem B1425865 : Blo 1052612 1425865 := bstep (se 2 (by rfl) ⟨534699, by rfl⟩ : syracuseStep 1425865 = 1069399) B1069399
theorem B6767057 : Blo 1052612 6767057 := bstep (se 2 (by rfl) ⟨2537646, by rfl⟩ : syracuseStep 6767057 = 5075293) B5075293
theorem B2376251 : Blo 1052612 2376251 := bstep (se 1 (by rfl) ⟨1782188, by rfl⟩ : syracuseStep 2376251 = 3564377) B3564377
theorem B2671289 : Blo 1052612 2671289 := bstep (se 2 (by rfl) ⟨1001733, by rfl⟩ : syracuseStep 2671289 = 2003467) B2003467
theorem B2376377 : Blo 1052612 2376377 := bstep (se 2 (by rfl) ⟨891141, by rfl⟩ : syracuseStep 2376377 = 1782283) B1782283
theorem B9126593 : Blo 1052612 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B2376719 : Blo 1052612 2376719 := bstep (se 1 (by rfl) ⟨1782539, by rfl⟩ : syracuseStep 2376719 = 3565079) B3565079
theorem B2376737 : Blo 1052612 2376737 := bstep (se 2 (by rfl) ⟨891276, by rfl⟩ : syracuseStep 2376737 = 1782553) B1782553
theorem B3556439 : Blo 1052612 3556439 := bstep (se 1 (by rfl) ⟨2667329, by rfl⟩ : syracuseStep 3556439 = 5334659) B5334659
theorem B2999585 : Blo 1052612 2999585 := bstep (se 2 (by rfl) ⟨1124844, by rfl⟩ : syracuseStep 2999585 = 2249689) B2249689
theorem B2671987 : Blo 1052612 2671987 := bstep (se 1 (by rfl) ⟨2003990, by rfl⟩ : syracuseStep 2671987 = 4007981) B4007981
theorem B2377079 : Blo 1052612 2377079 := bstep (se 1 (by rfl) ⟨1782809, by rfl⟩ : syracuseStep 2377079 = 3565619) B3565619
theorem B2999699 : Blo 1052612 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B6014411 : Blo 1052612 6014411 := bstep (se 1 (by rfl) ⟨4510808, by rfl⟩ : syracuseStep 6014411 = 9021617) B9021617
theorem B2672129 : Blo 1052612 2672129 := bstep (se 2 (by rfl) ⟨1002048, by rfl⟩ : syracuseStep 2672129 = 2004097) B2004097
theorem B5064221 : Blo 1052612 5064221 := bstep (se 3 (by rfl) ⟨949541, by rfl⟩ : syracuseStep 5064221 = 1899083) B1899083
theorem B2377259 : Blo 1052612 2377259 := bstep (se 1 (by rfl) ⟨1782944, by rfl⟩ : syracuseStep 2377259 = 3565889) B3565889
theorem B3556925 : Blo 1052612 3556925 := bstep (se 3 (by rfl) ⟨666923, by rfl⟩ : syracuseStep 3556925 = 1333847) B1333847
theorem B8996771 : Blo 1052612 8996771 := bstep (se 1 (by rfl) ⟨6747578, by rfl⟩ : syracuseStep 8996771 = 13495157) B13495157
theorem B2672585 : Blo 1052612 2672585 := bstep (se 2 (by rfl) ⟨1002219, by rfl⟩ : syracuseStep 2672585 = 2004439) B2004439
theorem B3000473 : Blo 1052612 3000473 := bstep (se 2 (by rfl) ⟨1125177, by rfl⟩ : syracuseStep 3000473 = 2250355) B2250355
theorem B5130497 : Blo 1052612 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B2672939 : Blo 1052612 2672939 := bstep (se 1 (by rfl) ⟨2004704, by rfl⟩ : syracuseStep 2672939 = 4009409) B4009409
theorem B8014139 : Blo 1052612 8014139 := bstep (se 1 (by rfl) ⟨6010604, by rfl⟩ : syracuseStep 8014139 = 12021209) B12021209
theorem B4508227 : Blo 1052612 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B3558329 : Blo 1052612 3558329 := bstep (se 2 (by rfl) ⟨1334373, by rfl⟩ : syracuseStep 3558329 = 2668747) B2668747
theorem B2673931 : Blo 1052612 2673931 := bstep (se 1 (by rfl) ⟨2005448, by rfl⟩ : syracuseStep 2673931 = 4010897) B4010897
theorem B2706803 : Blo 1052612 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B2674073 : Blo 1052612 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B1625591 : Blo 1052612 1625591 := bstep (se 1 (by rfl) ⟨1219193, by rfl⟩ : syracuseStep 1625591 = 2438387) B2438387
theorem B3558923 : Blo 1052612 3558923 := bstep (se 1 (by rfl) ⟨2669192, by rfl⟩ : syracuseStep 3558923 = 5338385) B5338385
theorem B2674235 : Blo 1052612 2674235 := bstep (se 1 (by rfl) ⟨2005676, by rfl⟩ : syracuseStep 2674235 = 4011353) B4011353
theorem B10145357 : Blo 1052612 10145357 := bstep (se 3 (by rfl) ⟨1902254, by rfl⟩ : syracuseStep 10145357 = 3804509) B3804509
theorem B6409847 : Blo 1052612 6409847 := bstep (se 1 (by rfl) ⟨4807385, by rfl⟩ : syracuseStep 6409847 = 9614771) B9614771
theorem B3559031 : Blo 1052612 3559031 := bstep (se 1 (by rfl) ⟨2669273, by rfl⟩ : syracuseStep 3559031 = 5338547) B5338547
theorem B1265287 : Blo 1052612 1265287 := bstep (se 1 (by rfl) ⟨948965, by rfl⟩ : syracuseStep 1265287 = 1897931) B1897931
theorem B2248339 : Blo 1052612 2248339 := bstep (se 1 (by rfl) ⟨1686254, by rfl⟩ : syracuseStep 2248339 = 3372509) B3372509
theorem B3002113 : Blo 1052612 3002113 := bstep (se 2 (by rfl) ⟨1125792, by rfl⟩ : syracuseStep 3002113 = 2251585) B2251585
theorem B6016801 : Blo 1052612 6016801 := bstep (se 2 (by rfl) ⟨2256300, by rfl⟩ : syracuseStep 6016801 = 4512601) B4512601
theorem B1265527 : Blo 1052612 1265527 := bstep (se 1 (by rfl) ⟨949145, by rfl⟩ : syracuseStep 1265527 = 1898291) B1898291
theorem B4804505 : Blo 1052612 4804505 := bstep (se 2 (by rfl) ⟨1801689, by rfl⟩ : syracuseStep 4804505 = 3603379) B3603379
theorem B3559625 : Blo 1052612 3559625 := bstep (se 2 (by rfl) ⟨1334859, by rfl⟩ : syracuseStep 3559625 = 2669719) B2669719
theorem B3002683 : Blo 1052612 3002683 := bstep (se 1 (by rfl) ⟨2252012, by rfl⟩ : syracuseStep 3002683 = 4504025) B4504025
theorem B5329475 : Blo 1052612 5329475 := bstep (se 1 (by rfl) ⟨3997106, by rfl⟩ : syracuseStep 5329475 = 7994213) B7994213
theorem B2708239 : Blo 1052612 2708239 := bstep (se 1 (by rfl) ⟨2031179, by rfl⟩ : syracuseStep 2708239 = 4062359) B4062359
theorem B1692431 : Blo 1052612 1692431 := bstep (se 1 (by rfl) ⟨1269323, by rfl⟩ : syracuseStep 1692431 = 2538647) B2538647
theorem B5329799 : Blo 1052612 5329799 := bstep (se 1 (by rfl) ⟨3997349, by rfl⟩ : syracuseStep 5329799 = 7994699) B7994699
theorem B3560327 : Blo 1052612 3560327 := bstep (se 1 (by rfl) ⟨2670245, by rfl⟩ : syracuseStep 3560327 = 5340491) B5340491
theorem B4281241 : Blo 1052612 4281241 := bstep (se 2 (by rfl) ⟨1605465, by rfl⟩ : syracuseStep 4281241 = 3210931) B3210931
theorem B9622435 : Blo 1052612 9622435 := bstep (se 1 (by rfl) ⟨7216826, by rfl⟩ : syracuseStep 9622435 = 14433653) B14433653
theorem B4510673 : Blo 1052612 4510673 := bstep (se 2 (by rfl) ⟨1691502, by rfl⟩ : syracuseStep 4510673 = 3383005) B3383005
theorem B1332283 : Blo 1052612 1332283 := bstep (se 1 (by rfl) ⟨999212, by rfl⟩ : syracuseStep 1332283 = 1998425) B1998425
theorem B3560705 : Blo 1052612 3560705 := bstep (se 2 (by rfl) ⟨1335264, by rfl⟩ : syracuseStep 3560705 = 2670529) B2670529
theorem B1333255 : Blo 1052612 1333255 := bstep (se 1 (by rfl) ⟨999941, by rfl⟩ : syracuseStep 1333255 = 1999883) B1999883
theorem B3561515 : Blo 1052612 3561515 := bstep (se 1 (by rfl) ⟨2671136, by rfl⟩ : syracuseStep 3561515 = 5342273) B5342273
theorem B1333675 : Blo 1052612 1333675 := bstep (se 1 (by rfl) ⟨1000256, by rfl⟩ : syracuseStep 1333675 = 2000513) B2000513
theorem B1333903 : Blo 1052612 1333903 := bstep (se 1 (by rfl) ⟨1000427, by rfl⟩ : syracuseStep 1333903 = 2000855) B2000855
theorem B3005075 : Blo 1052612 3005075 := bstep (se 1 (by rfl) ⟨2253806, by rfl⟩ : syracuseStep 3005075 = 4507613) B4507613
theorem B5069911 : Blo 1052612 5069911 := bstep (se 1 (by rfl) ⟨3802433, by rfl⟩ : syracuseStep 5069911 = 7604867) B7604867
theorem B3562811 : Blo 1052612 3562811 := bstep (se 1 (by rfl) ⟨2672108, by rfl⟩ : syracuseStep 3562811 = 5344217) B5344217
theorem B1334647 : Blo 1052612 1334647 := bstep (se 1 (by rfl) ⟨1000985, by rfl⟩ : syracuseStep 1334647 = 2001971) B2001971
theorem B5561747 : Blo 1052612 5561747 := bstep (se 1 (by rfl) ⟨4171310, by rfl⟩ : syracuseStep 5561747 = 8342621) B8342621
theorem B3005849 : Blo 1052612 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B2252303 : Blo 1052612 2252303 := bstep (se 1 (by rfl) ⟨1689227, by rfl⟩ : syracuseStep 2252303 = 3378455) B3378455
theorem B8019485 : Blo 1052612 8019485 := bstep (se 3 (by rfl) ⟨1503653, by rfl⟩ : syracuseStep 8019485 = 3007307) B3007307
theorem B2252423 : Blo 1052612 2252423 := bstep (se 1 (by rfl) ⟨1689317, by rfl⟩ : syracuseStep 2252423 = 3378635) B3378635
theorem B2743961 : Blo 1052612 2743961 := bstep (se 2 (by rfl) ⟨1028985, by rfl⟩ : syracuseStep 2743961 = 2057971) B2057971
theorem B1334971 : Blo 1052612 1334971 := bstep (se 1 (by rfl) ⟨1001228, by rfl⟩ : syracuseStep 1334971 = 2002457) B2002457
theorem B3563297 : Blo 1052612 3563297 := bstep (se 2 (by rfl) ⟨1336236, by rfl⟩ : syracuseStep 3563297 = 2672473) B2672473
theorem B2252603 : Blo 1052612 2252603 := bstep (se 1 (by rfl) ⟨1689452, by rfl⟩ : syracuseStep 2252603 = 3378905) B3378905
theorem B1499143 : Blo 1052612 1499143 := bstep (se 1 (by rfl) ⟨1124357, by rfl⟩ : syracuseStep 1499143 = 2248715) B2248715
theorem B1335467 : Blo 1052612 1335467 := bstep (se 1 (by rfl) ⟨1001600, by rfl⟩ : syracuseStep 1335467 = 2003201) B2003201
theorem B2253089 : Blo 1052612 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B5333363 : Blo 1052612 5333363 := bstep (se 1 (by rfl) ⟨4000022, by rfl⟩ : syracuseStep 5333363 = 8000045) B8000045
theorem B3563891 : Blo 1052612 3563891 := bstep (se 1 (by rfl) ⟨2672918, by rfl⟩ : syracuseStep 3563891 = 5345837) B5345837
theorem B5136785 : Blo 1052612 5136785 := bstep (se 2 (by rfl) ⟨1926294, by rfl⟩ : syracuseStep 5136785 = 3852589) B3852589
theorem B9626077 : Blo 1052612 9626077 := bstep (se 3 (by rfl) ⟨1804889, by rfl⟩ : syracuseStep 9626077 = 3609779) B3609779
theorem B1335943 : Blo 1052612 1335943 := bstep (se 1 (by rfl) ⟨1001957, by rfl⟩ : syracuseStep 1335943 = 2003915) B2003915
theorem B1499963 : Blo 1052612 1499963 := bstep (se 1 (by rfl) ⟨1124972, by rfl⟩ : syracuseStep 1499963 = 2249945) B2249945
theorem B5333849 : Blo 1052612 5333849 := bstep (se 2 (by rfl) ⟨2000193, by rfl⟩ : syracuseStep 5333849 = 4000387) B4000387
theorem B10838947 : Blo 1052612 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B10806317 : Blo 1052612 10806317 := bstep (se 3 (by rfl) ⟨2026184, by rfl⟩ : syracuseStep 10806317 = 4052369) B4052369
theorem B2253943 : Blo 1052612 2253943 := bstep (se 1 (by rfl) ⟨1690457, by rfl⟩ : syracuseStep 2253943 = 3380915) B3380915
theorem B1336439 : Blo 1052612 1336439 := bstep (se 1 (by rfl) ⟨1002329, by rfl⟩ : syracuseStep 1336439 = 2004659) B2004659
theorem B1336591 : Blo 1052612 1336591 := bstep (se 1 (by rfl) ⟨1002443, by rfl⟩ : syracuseStep 1336591 = 2004887) B2004887
theorem B16442657 : Blo 1052612 16442657 := bstep (se 2 (by rfl) ⟨6165996, by rfl⟩ : syracuseStep 16442657 = 12331993) B12331993
theorem B15230267 : Blo 1052612 15230267 := bstep (se 1 (by rfl) ⟨11422700, by rfl⟩ : syracuseStep 15230267 = 22845401) B22845401
theorem B1500601 : Blo 1052612 1500601 := bstep (se 2 (by rfl) ⟨562725, by rfl⟩ : syracuseStep 1500601 = 1125451) B1125451
theorem B1336763 : Blo 1052612 1336763 := bstep (se 1 (by rfl) ⟨1002572, by rfl⟩ : syracuseStep 1336763 = 2005145) B2005145
theorem B3007945 : Blo 1052612 3007945 := bstep (se 2 (by rfl) ⟨1127979, by rfl⟩ : syracuseStep 3007945 = 2255959) B2255959
theorem B1500715 : Blo 1052612 1500715 := bstep (se 1 (by rfl) ⟨1125536, by rfl⟩ : syracuseStep 1500715 = 2251073) B2251073
theorem B1500943 : Blo 1052612 1500943 := bstep (se 1 (by rfl) ⟨1125707, by rfl⟩ : syracuseStep 1500943 = 2251415) B2251415
theorem B3008299 : Blo 1052612 3008299 := bstep (se 1 (by rfl) ⟨2256224, by rfl⟩ : syracuseStep 3008299 = 4512449) B4512449
theorem B3008573 : Blo 1052612 3008573 := bstep (se 3 (by rfl) ⟨564107, by rfl⟩ : syracuseStep 3008573 = 1128215) B1128215
theorem B1501831 : Blo 1052612 1501831 := bstep (se 1 (by rfl) ⟨1126373, by rfl⟩ : syracuseStep 1501831 = 2252747) B2252747
theorem B5335955 : Blo 1052612 5335955 := bstep (se 1 (by rfl) ⟨4001966, by rfl⟩ : syracuseStep 5335955 = 8003933) B8003933
theorem B10120139 : Blo 1052612 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B1502327 : Blo 1052612 1502327 := bstep (se 1 (by rfl) ⟨1126745, by rfl⟩ : syracuseStep 1502327 = 2253491) B2253491
theorem B3796205 : Blo 1052612 3796205 := bstep (se 3 (by rfl) ⟨711788, by rfl⟩ : syracuseStep 3796205 = 1423577) B1423577
theorem B20803223 : Blo 1052612 20803223 := bstep (se 1 (by rfl) ⟨15602417, by rfl⟩ : syracuseStep 20803223 = 31204835) B31204835
theorem B3796769 : Blo 1052612 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B28897073 : Blo 1052612 28897073 := bstep (se 2 (by rfl) ⟨10836402, by rfl⟩ : syracuseStep 28897073 = 21672805) B21672805
theorem B1503289 : Blo 1052612 1503289 := bstep (se 2 (by rfl) ⟨563733, by rfl⟩ : syracuseStep 1503289 = 1127467) B1127467
theorem B11137297 : Blo 1052612 11137297 := bstep (se 2 (by rfl) ⟨4176486, by rfl⟩ : syracuseStep 11137297 = 8352973) B8352973
theorem B1503631 : Blo 1052612 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B3797705 : Blo 1052612 3797705 := bstep (se 2 (by rfl) ⟨1424139, by rfl⟩ : syracuseStep 3797705 = 2848279) B2848279
theorem B1733767 : Blo 1052612 1733767 := bstep (se 1 (by rfl) ⟨1300325, by rfl⟩ : syracuseStep 1733767 = 2600651) B2600651
theorem B12187027 : Blo 1052612 12187027 := bstep (se 1 (by rfl) ⟨9140270, by rfl⟩ : syracuseStep 12187027 = 18280541) B18280541
theorem B3601817 : Blo 1052612 3601817 := bstep (se 2 (by rfl) ⟨1350681, by rfl⟩ : syracuseStep 3601817 = 2701363) B2701363
theorem B28865969 : Blo 1052612 28865969 := bstep (se 2 (by rfl) ⟨10824738, by rfl⟩ : syracuseStep 28865969 = 21649477) B21649477
theorem B3372587 : Blo 1052612 3372587 := bstep (se 1 (by rfl) ⟨2529440, by rfl⟩ : syracuseStep 3372587 = 5058881) B5058881
theorem B5076523 : Blo 1052612 5076523 := bstep (se 1 (by rfl) ⟨3807392, by rfl⟩ : syracuseStep 5076523 = 7614785) B7614785
theorem B1603471 : Blo 1052612 1603471 := bstep (se 1 (by rfl) ⟨1202603, by rfl⟩ : syracuseStep 1603471 = 2405207) B2405207
theorem B5339033 : Blo 1052612 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B12810251 : Blo 1052612 12810251 := bstep (se 1 (by rfl) ⟨9607688, by rfl⟩ : syracuseStep 12810251 = 19215377) B19215377
theorem B20510765 : Blo 1052612 20510765 := bstep (se 3 (by rfl) ⟨3845768, by rfl⟩ : syracuseStep 20510765 = 7691537) B7691537
theorem B8550803 : Blo 1052612 8550803 := bstep (se 1 (by rfl) ⟨6413102, by rfl⟩ : syracuseStep 8550803 = 12826205) B12826205
theorem B3373687 : Blo 1052612 3373687 := bstep (se 1 (by rfl) ⟨2530265, by rfl⟩ : syracuseStep 3373687 = 5060531) B5060531
theorem B9009893 : Blo 1052612 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B5143277 : Blo 1052612 5143277 := bstep (se 3 (by rfl) ⟨964364, by rfl⟩ : syracuseStep 5143277 = 1928729) B1928729
theorem B1899307 : Blo 1052612 1899307 := bstep (se 1 (by rfl) ⟨1424480, by rfl⟩ : syracuseStep 1899307 = 2848961) B2848961
theorem B1604809 : Blo 1052612 1604809 := bstep (se 2 (by rfl) ⟨601803, by rfl⟩ : syracuseStep 1604809 = 1203607) B1203607
theorem B6421913 : Blo 1052612 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B1998607 : Blo 1052612 1998607 := bstep (se 1 (by rfl) ⟨1498955, by rfl⟩ : syracuseStep 1998607 = 2997911) B2997911
theorem B7995185 : Blo 1052612 7995185 := bstep (se 2 (by rfl) ⟨2998194, by rfl⟩ : syracuseStep 7995185 = 5996389) B5996389
theorem B12844889 : Blo 1052612 12844889 := bstep (se 2 (by rfl) ⟨4816833, by rfl⟩ : syracuseStep 12844889 = 9633667) B9633667
theorem B1998857 : Blo 1052612 1998857 := bstep (se 2 (by rfl) ⟨749571, by rfl⟩ : syracuseStep 1998857 = 1499143) B1499143
theorem B3997775 : Blo 1052612 3997775 := bstep (se 1 (by rfl) ⟨2998331, by rfl⟩ : syracuseStep 3997775 = 5996663) B5996663
theorem B3801167 : Blo 1052612 3801167 := bstep (se 1 (by rfl) ⟨2850875, by rfl⟩ : syracuseStep 3801167 = 5701751) B5701751
theorem B13500593 : Blo 1052612 13500593 := bstep (se 2 (by rfl) ⟨5062722, by rfl⟩ : syracuseStep 13500593 = 10125445) B10125445
theorem B3997943 : Blo 1052612 3997943 := bstep (se 1 (by rfl) ⟨2998457, by rfl⟩ : syracuseStep 3997943 = 5996915) B5996915
theorem B3604841 : Blo 1052612 3604841 := bstep (se 2 (by rfl) ⟨1351815, by rfl⟩ : syracuseStep 3604841 = 2703631) B2703631
theorem B1901153 : Blo 1052612 1901153 := bstep (se 2 (by rfl) ⟨712932, by rfl⟩ : syracuseStep 1901153 = 1425865) B1425865
theorem B17990261 : Blo 1052612 17990261 := bstep (se 5 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 17990261 = 1686587) B1686587
theorem B1999723 : Blo 1052612 1999723 := bstep (se 1 (by rfl) ⟨1499792, by rfl⟩ : syracuseStep 1999723 = 2999585) B2999585
theorem B1999799 : Blo 1052612 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B3998915 : Blo 1052612 3998915 := bstep (se 1 (by rfl) ⟨2999186, by rfl⟩ : syracuseStep 3998915 = 5998373) B5998373
theorem B14451929 : Blo 1052612 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B5997847 : Blo 1052612 5997847 := bstep (se 1 (by rfl) ⟨4498385, by rfl⟩ : syracuseStep 5997847 = 8996771) B8996771
theorem B2000315 : Blo 1052612 2000315 := bstep (se 1 (by rfl) ⟨1500236, by rfl⟩ : syracuseStep 2000315 = 3000473) B3000473
theorem B5342759 : Blo 1052612 5342759 := bstep (se 1 (by rfl) ⟨4007069, by rfl⟩ : syracuseStep 5342759 = 8014139) B8014139
theorem B7604063 : Blo 1052612 7604063 := bstep (se 1 (by rfl) ⟨5703047, by rfl⟩ : syracuseStep 7604063 = 11406095) B11406095
theorem B10127213 : Blo 1052612 10127213 := bstep (se 3 (by rfl) ⟨1898852, by rfl⟩ : syracuseStep 10127213 = 3797705) B3797705
theorem B2000801 : Blo 1052612 2000801 := bstep (se 2 (by rfl) ⟨750300, by rfl⟩ : syracuseStep 2000801 = 1500601) B1500601
theorem B8652737 : Blo 1052612 8652737 := bstep (se 2 (by rfl) ⟨3244776, by rfl⟩ : syracuseStep 8652737 = 6489553) B6489553
theorem B2000953 : Blo 1052612 2000953 := bstep (se 2 (by rfl) ⟨750357, by rfl⟩ : syracuseStep 2000953 = 1500715) B1500715
theorem B3999901 : Blo 1052612 3999901 := bstep (se 3 (by rfl) ⟨749981, by rfl⟩ : syracuseStep 3999901 = 1499963) B1499963
theorem B7604381 : Blo 1052612 7604381 := bstep (se 3 (by rfl) ⟨1425821, by rfl⟩ : syracuseStep 7604381 = 2851643) B2851643
theorem B1804535 : Blo 1052612 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B1083727 : Blo 1052612 1083727 := bstep (se 1 (by rfl) ⟨812795, by rfl⟩ : syracuseStep 1083727 = 1625591) B1625591
theorem B2001257 : Blo 1052612 2001257 := bstep (se 2 (by rfl) ⟨750471, by rfl⟩ : syracuseStep 2001257 = 1500943) B1500943
theorem B3377609 : Blo 1052612 3377609 := bstep (se 2 (by rfl) ⟨1266603, by rfl⟩ : syracuseStep 3377609 = 2533207) B2533207
theorem B1903351 : Blo 1052612 1903351 := bstep (se 1 (by rfl) ⟨1427513, by rfl⟩ : syracuseStep 1903351 = 2855027) B2855027
theorem B10292503 : Blo 1052612 10292503 := bstep (se 1 (by rfl) ⟨7719377, by rfl⟩ : syracuseStep 10292503 = 15438755) B15438755
theorem B7999073 : Blo 1052612 7999073 := bstep (se 2 (by rfl) ⟨2999652, by rfl⟩ : syracuseStep 7999073 = 5999305) B5999305
theorem B5344865 : Blo 1052612 5344865 := bstep (se 2 (by rfl) ⟨2004324, by rfl⟩ : syracuseStep 5344865 = 4008649) B4008649
theorem B3804857 : Blo 1052612 3804857 := bstep (se 2 (by rfl) ⟨1426821, by rfl⟩ : syracuseStep 3804857 = 2853643) B2853643
theorem B1052615 : Blo 1052612 1052615 := bstep (se 1 (by rfl) ⟨789461, by rfl⟩ : syracuseStep 1052615 = 1578923) B1578923
theorem B1052635 : Blo 1052612 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B1052711 : Blo 1052612 1052711 := bstep (se 1 (by rfl) ⟨789533, by rfl⟩ : syracuseStep 1052711 = 1579067) B1579067
theorem B13504589 : Blo 1052612 13504589 := bstep (se 3 (by rfl) ⟨2532110, by rfl⟩ : syracuseStep 13504589 = 5064221) B5064221
theorem B1052751 : Blo 1052612 1052751 := bstep (se 1 (by rfl) ⟨789563, by rfl⟩ : syracuseStep 1052751 = 1579127) B1579127
theorem B1052767 : Blo 1052612 1052767 := bstep (se 1 (by rfl) ⟨789575, by rfl⟩ : syracuseStep 1052767 = 1579151) B1579151
theorem B21958771 : Blo 1052612 21958771 := bstep (se 1 (by rfl) ⟨16469078, by rfl⟩ : syracuseStep 21958771 = 32938157) B32938157
theorem B1052795 : Blo 1052612 1052795 := bstep (se 1 (by rfl) ⟨789596, by rfl⟩ : syracuseStep 1052795 = 1579193) B1579193
theorem B1052847 : Blo 1052612 1052847 := bstep (se 1 (by rfl) ⟨789635, by rfl⟩ : syracuseStep 1052847 = 1579271) B1579271
theorem B1052871 : Blo 1052612 1052871 := bstep (se 1 (by rfl) ⟨789653, by rfl⟩ : syracuseStep 1052871 = 1579307) B1579307
theorem B1052891 : Blo 1052612 1052891 := bstep (se 1 (by rfl) ⟨789668, by rfl⟩ : syracuseStep 1052891 = 1579337) B1579337
theorem B10129637 : Blo 1052612 10129637 := bstep (se 4 (by rfl) ⟨949653, by rfl⟩ : syracuseStep 10129637 = 1899307) B1899307
theorem B1052967 : Blo 1052612 1052967 := bstep (se 1 (by rfl) ⟨789725, by rfl⟩ : syracuseStep 1052967 = 1579451) B1579451
theorem B1053007 : Blo 1052612 1053007 := bstep (se 1 (by rfl) ⟨789755, by rfl⟩ : syracuseStep 1053007 = 1579511) B1579511
theorem B1053023 : Blo 1052612 1053023 := bstep (se 1 (by rfl) ⟨789767, by rfl⟩ : syracuseStep 1053023 = 1579535) B1579535
theorem B1053051 : Blo 1052612 1053051 := bstep (se 1 (by rfl) ⟨789788, by rfl⟩ : syracuseStep 1053051 = 1579577) B1579577
theorem B1053103 : Blo 1052612 1053103 := bstep (se 1 (by rfl) ⟨789827, by rfl⟩ : syracuseStep 1053103 = 1579655) B1579655
theorem B2003383 : Blo 1052612 2003383 := bstep (se 1 (by rfl) ⟨1502537, by rfl⟩ : syracuseStep 2003383 = 3005075) B3005075
theorem B1053127 : Blo 1052612 1053127 := bstep (se 1 (by rfl) ⟨789845, by rfl⟩ : syracuseStep 1053127 = 1579691) B1579691
theorem B1053147 : Blo 1052612 1053147 := bstep (se 1 (by rfl) ⟨789860, by rfl⟩ : syracuseStep 1053147 = 1579721) B1579721
theorem B1053223 : Blo 1052612 1053223 := bstep (se 1 (by rfl) ⟨789917, by rfl⟩ : syracuseStep 1053223 = 1579835) B1579835
theorem B1053263 : Blo 1052612 1053263 := bstep (se 1 (by rfl) ⟨789947, by rfl⟩ : syracuseStep 1053263 = 1579895) B1579895
theorem B1053279 : Blo 1052612 1053279 := bstep (se 1 (by rfl) ⟨789959, by rfl⟩ : syracuseStep 1053279 = 1579919) B1579919
theorem B1053307 : Blo 1052612 1053307 := bstep (se 1 (by rfl) ⟨789980, by rfl⟩ : syracuseStep 1053307 = 1579961) B1579961
theorem B1053359 : Blo 1052612 1053359 := bstep (se 1 (by rfl) ⟨790019, by rfl⟩ : syracuseStep 1053359 = 1580039) B1580039
theorem B1053383 : Blo 1052612 1053383 := bstep (se 1 (by rfl) ⟨790037, by rfl⟩ : syracuseStep 1053383 = 1580075) B1580075
theorem B1053403 : Blo 1052612 1053403 := bstep (se 1 (by rfl) ⟨790052, by rfl⟩ : syracuseStep 1053403 = 1580105) B1580105
theorem B1053479 : Blo 1052612 1053479 := bstep (se 1 (by rfl) ⟨790109, by rfl⟩ : syracuseStep 1053479 = 1580219) B1580219
theorem B1053519 : Blo 1052612 1053519 := bstep (se 1 (by rfl) ⟨790139, by rfl⟩ : syracuseStep 1053519 = 1580279) B1580279
theorem B1053535 : Blo 1052612 1053535 := bstep (se 1 (by rfl) ⟨790151, by rfl⟩ : syracuseStep 1053535 = 1580303) B1580303
theorem B1053563 : Blo 1052612 1053563 := bstep (se 1 (by rfl) ⟨790172, by rfl⟩ : syracuseStep 1053563 = 1580345) B1580345
theorem B1053615 : Blo 1052612 1053615 := bstep (se 1 (by rfl) ⟨790211, by rfl⟩ : syracuseStep 1053615 = 1580423) B1580423
theorem B3707831 : Blo 1052612 3707831 := bstep (se 1 (by rfl) ⟨2780873, by rfl⟩ : syracuseStep 3707831 = 5561747) B5561747
theorem B1053639 : Blo 1052612 1053639 := bstep (se 1 (by rfl) ⟨790229, by rfl⟩ : syracuseStep 1053639 = 1580459) B1580459
theorem B1053659 : Blo 1052612 1053659 := bstep (se 1 (by rfl) ⟨790244, by rfl⟩ : syracuseStep 1053659 = 1580489) B1580489
theorem B4002817 : Blo 1052612 4002817 := bstep (se 2 (by rfl) ⟨1501056, by rfl⟩ : syracuseStep 4002817 = 3002113) B3002113
theorem B8000531 : Blo 1052612 8000531 := bstep (se 1 (by rfl) ⟨6000398, by rfl⟩ : syracuseStep 8000531 = 12000797) B12000797
theorem B5346323 : Blo 1052612 5346323 := bstep (se 1 (by rfl) ⟨4009742, by rfl⟩ : syracuseStep 5346323 = 8019485) B8019485
theorem B1053735 : Blo 1052612 1053735 := bstep (se 1 (by rfl) ⟨790301, by rfl⟩ : syracuseStep 1053735 = 1580603) B1580603
theorem B1053775 : Blo 1052612 1053775 := bstep (se 1 (by rfl) ⟨790331, by rfl⟩ : syracuseStep 1053775 = 1580663) B1580663
theorem B1053791 : Blo 1052612 1053791 := bstep (se 1 (by rfl) ⟨790343, by rfl⟩ : syracuseStep 1053791 = 1580687) B1580687
theorem B1053819 : Blo 1052612 1053819 := bstep (se 1 (by rfl) ⟨790364, by rfl⟩ : syracuseStep 1053819 = 1580729) B1580729
theorem B1053871 : Blo 1052612 1053871 := bstep (se 1 (by rfl) ⟨790403, by rfl⟩ : syracuseStep 1053871 = 1580807) B1580807
theorem B1053895 : Blo 1052612 1053895 := bstep (se 1 (by rfl) ⟨790421, by rfl⟩ : syracuseStep 1053895 = 1580843) B1580843
theorem B1053915 : Blo 1052612 1053915 := bstep (se 1 (by rfl) ⟨790436, by rfl⟩ : syracuseStep 1053915 = 1580873) B1580873
theorem B6755575 : Blo 1052612 6755575 := bstep (se 1 (by rfl) ⟨5066681, by rfl⟩ : syracuseStep 6755575 = 10133363) B10133363
theorem B1053991 : Blo 1052612 1053991 := bstep (se 1 (by rfl) ⟨790493, by rfl⟩ : syracuseStep 1053991 = 1580987) B1580987
theorem B1054031 : Blo 1052612 1054031 := bstep (se 1 (by rfl) ⟨790523, by rfl⟩ : syracuseStep 1054031 = 1581047) B1581047
theorem B1054047 : Blo 1052612 1054047 := bstep (se 1 (by rfl) ⟨790535, by rfl⟩ : syracuseStep 1054047 = 1581071) B1581071
theorem B1054075 : Blo 1052612 1054075 := bstep (se 1 (by rfl) ⟨790556, by rfl⟩ : syracuseStep 1054075 = 1581113) B1581113
theorem B1054127 : Blo 1052612 1054127 := bstep (se 1 (by rfl) ⟨790595, by rfl⟩ : syracuseStep 1054127 = 1581191) B1581191
theorem B1054151 : Blo 1052612 1054151 := bstep (se 1 (by rfl) ⟨790613, by rfl⟩ : syracuseStep 1054151 = 1581227) B1581227
theorem B7607753 : Blo 1052612 7607753 := bstep (se 2 (by rfl) ⟨2852907, by rfl⟩ : syracuseStep 7607753 = 5705815) B5705815
theorem B1054171 : Blo 1052612 1054171 := bstep (se 1 (by rfl) ⟨790628, by rfl⟩ : syracuseStep 1054171 = 1581257) B1581257
theorem B1054247 : Blo 1052612 1054247 := bstep (se 1 (by rfl) ⟨790685, by rfl⟩ : syracuseStep 1054247 = 1581371) B1581371
theorem B3806759 : Blo 1052612 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B1054287 : Blo 1052612 1054287 := bstep (se 1 (by rfl) ⟨790715, by rfl⟩ : syracuseStep 1054287 = 1581431) B1581431
theorem B1054303 : Blo 1052612 1054303 := bstep (se 1 (by rfl) ⟨790727, by rfl⟩ : syracuseStep 1054303 = 1581455) B1581455
theorem B1185403 : Blo 1052612 1185403 := bstep (se 1 (by rfl) ⟨889052, by rfl⟩ : syracuseStep 1185403 = 1778105) B1778105
theorem B1054331 : Blo 1052612 1054331 := bstep (se 1 (by rfl) ⟨790748, by rfl⟩ : syracuseStep 1054331 = 1581497) B1581497
theorem B1054383 : Blo 1052612 1054383 := bstep (se 1 (by rfl) ⟨790787, by rfl⟩ : syracuseStep 1054383 = 1581575) B1581575
theorem B14849729 : Blo 1052612 14849729 := bstep (se 2 (by rfl) ⟨5568648, by rfl⟩ : syracuseStep 14849729 = 11137297) B11137297
theorem B1054407 : Blo 1052612 1054407 := bstep (se 1 (by rfl) ⟨790805, by rfl⟩ : syracuseStep 1054407 = 1581611) B1581611
theorem B1054427 : Blo 1052612 1054427 := bstep (se 1 (by rfl) ⟨790820, by rfl⟩ : syracuseStep 1054427 = 1581641) B1581641
theorem B4003577 : Blo 1052612 4003577 := bstep (se 2 (by rfl) ⟨1501341, by rfl⟩ : syracuseStep 4003577 = 3002683) B3002683
theorem B1054503 : Blo 1052612 1054503 := bstep (se 1 (by rfl) ⟨790877, by rfl⟩ : syracuseStep 1054503 = 1581755) B1581755
theorem B1054543 : Blo 1052612 1054543 := bstep (se 1 (by rfl) ⟨790907, by rfl⟩ : syracuseStep 1054543 = 1581815) B1581815
theorem B14423903 : Blo 1052612 14423903 := bstep (se 1 (by rfl) ⟨10817927, by rfl⟩ : syracuseStep 14423903 = 21635855) B21635855
theorem B1054559 : Blo 1052612 1054559 := bstep (se 1 (by rfl) ⟨790919, by rfl⟩ : syracuseStep 1054559 = 1581839) B1581839
theorem B2004841 : Blo 1052612 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B11540333 : Blo 1052612 11540333 := bstep (se 3 (by rfl) ⟨2163812, by rfl⟩ : syracuseStep 11540333 = 4327625) B4327625
theorem B1054587 : Blo 1052612 1054587 := bstep (se 1 (by rfl) ⟨790940, by rfl⟩ : syracuseStep 1054587 = 1581881) B1581881
theorem B1054639 : Blo 1052612 1054639 := bstep (se 1 (by rfl) ⟨790979, by rfl⟩ : syracuseStep 1054639 = 1581959) B1581959
theorem B1578935 : Blo 1052612 1578935 := bstep (se 1 (by rfl) ⟨1184201, by rfl⟩ : syracuseStep 1578935 = 2368403) B2368403
theorem B1054663 : Blo 1052612 1054663 := bstep (se 1 (by rfl) ⟨790997, by rfl⟩ : syracuseStep 1054663 = 1581995) B1581995
theorem B1578971 : Blo 1052612 1578971 := bstep (se 1 (by rfl) ⟨1184228, by rfl⟩ : syracuseStep 1578971 = 2368457) B2368457
theorem B1054683 : Blo 1052612 1054683 := bstep (se 1 (by rfl) ⟨791012, by rfl⟩ : syracuseStep 1054683 = 1582025) B1582025
theorem B9246757 : Blo 1052612 9246757 := bstep (se 4 (by rfl) ⟨866883, by rfl⟩ : syracuseStep 9246757 = 1733767) B1733767
theorem B1054759 : Blo 1052612 1054759 := bstep (se 1 (by rfl) ⟨791069, by rfl⟩ : syracuseStep 1054759 = 1582139) B1582139
theorem B1185871 : Blo 1052612 1185871 := bstep (se 1 (by rfl) ⟨889403, by rfl⟩ : syracuseStep 1185871 = 1778807) B1778807
theorem B1054799 : Blo 1052612 1054799 := bstep (se 1 (by rfl) ⟨791099, by rfl⟩ : syracuseStep 1054799 = 1582199) B1582199
theorem B1054815 : Blo 1052612 1054815 := bstep (se 1 (by rfl) ⟨791111, by rfl⟩ : syracuseStep 1054815 = 1582223) B1582223
theorem B1054843 : Blo 1052612 1054843 := bstep (se 1 (by rfl) ⟨791132, by rfl⟩ : syracuseStep 1054843 = 1582265) B1582265
theorem B1054895 : Blo 1052612 1054895 := bstep (se 1 (by rfl) ⟨791171, by rfl⟩ : syracuseStep 1054895 = 1582343) B1582343
theorem B1054919 : Blo 1052612 1054919 := bstep (se 1 (by rfl) ⟨791189, by rfl⟩ : syracuseStep 1054919 = 1582379) B1582379
theorem B1054939 : Blo 1052612 1054939 := bstep (se 1 (by rfl) ⟨791204, by rfl⟩ : syracuseStep 1054939 = 1582409) B1582409
theorem B1055015 : Blo 1052612 1055015 := bstep (se 1 (by rfl) ⟨791261, by rfl⟩ : syracuseStep 1055015 = 1582523) B1582523
theorem B1055055 : Blo 1052612 1055055 := bstep (se 1 (by rfl) ⟨791291, by rfl⟩ : syracuseStep 1055055 = 1582583) B1582583
theorem B1055071 : Blo 1052612 1055071 := bstep (se 1 (by rfl) ⟨791303, by rfl⟩ : syracuseStep 1055071 = 1582607) B1582607
theorem B3610985 : Blo 1052612 3610985 := bstep (se 2 (by rfl) ⟨1354119, by rfl⟩ : syracuseStep 3610985 = 2708239) B2708239
theorem B1055099 : Blo 1052612 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B1579439 : Blo 1052612 1579439 := bstep (se 1 (by rfl) ⟨1184579, by rfl⟩ : syracuseStep 1579439 = 2369159) B2369159
theorem B1055151 : Blo 1052612 1055151 := bstep (se 1 (by rfl) ⟨791363, by rfl⟩ : syracuseStep 1055151 = 1582727) B1582727
theorem B1055175 : Blo 1052612 1055175 := bstep (se 1 (by rfl) ⟨791381, by rfl⟩ : syracuseStep 1055175 = 1582763) B1582763
theorem B1186267 : Blo 1052612 1186267 := bstep (se 1 (by rfl) ⟨889700, by rfl⟩ : syracuseStep 1186267 = 1779401) B1779401
theorem B1055195 : Blo 1052612 1055195 := bstep (se 1 (by rfl) ⟨791396, by rfl⟩ : syracuseStep 1055195 = 1582793) B1582793
theorem B1579529 : Blo 1052612 1579529 := bstep (se 2 (by rfl) ⟨592323, by rfl⟩ : syracuseStep 1579529 = 1184647) B1184647
theorem B5708321 : Blo 1052612 5708321 := bstep (se 2 (by rfl) ⟨2140620, by rfl⟩ : syracuseStep 5708321 = 4281241) B4281241
theorem B1579559 : Blo 1052612 1579559 := bstep (se 1 (by rfl) ⟨1184669, by rfl⟩ : syracuseStep 1579559 = 2369339) B2369339
theorem B1055271 : Blo 1052612 1055271 := bstep (se 1 (by rfl) ⟨791453, by rfl⟩ : syracuseStep 1055271 = 1582907) B1582907
theorem B1055311 : Blo 1052612 1055311 := bstep (se 1 (by rfl) ⟨791483, by rfl⟩ : syracuseStep 1055311 = 1582967) B1582967
theorem B1055327 : Blo 1052612 1055327 := bstep (se 1 (by rfl) ⟨791495, by rfl⟩ : syracuseStep 1055327 = 1582991) B1582991
theorem B1579643 : Blo 1052612 1579643 := bstep (se 1 (by rfl) ⟨1184732, by rfl⟩ : syracuseStep 1579643 = 2369465) B2369465
theorem B1055355 : Blo 1052612 1055355 := bstep (se 1 (by rfl) ⟨791516, by rfl⟩ : syracuseStep 1055355 = 1583033) B1583033
theorem B1055407 : Blo 1052612 1055407 := bstep (se 1 (by rfl) ⟨791555, by rfl⟩ : syracuseStep 1055407 = 1583111) B1583111
theorem B1055431 : Blo 1052612 1055431 := bstep (se 1 (by rfl) ⟨791573, by rfl⟩ : syracuseStep 1055431 = 1583147) B1583147
theorem B2005715 : Blo 1052612 2005715 := bstep (se 1 (by rfl) ⟨1504286, by rfl⟩ : syracuseStep 2005715 = 3008573) B3008573
theorem B1055451 : Blo 1052612 1055451 := bstep (se 1 (by rfl) ⟨791588, by rfl⟩ : syracuseStep 1055451 = 1583177) B1583177
theorem B1776377 : Blo 1052612 1776377 := bstep (se 2 (by rfl) ⟨666141, by rfl⟩ : syracuseStep 1776377 = 1332283) B1332283
theorem B1579769 : Blo 1052612 1579769 := bstep (se 2 (by rfl) ⟨592413, by rfl⟩ : syracuseStep 1579769 = 1184827) B1184827
theorem B1055527 : Blo 1052612 1055527 := bstep (se 1 (by rfl) ⟨791645, by rfl⟩ : syracuseStep 1055527 = 1583291) B1583291
theorem B3808073 : Blo 1052612 3808073 := bstep (se 2 (by rfl) ⟨1428027, by rfl⟩ : syracuseStep 3808073 = 2856055) B2856055
theorem B1055567 : Blo 1052612 1055567 := bstep (se 1 (by rfl) ⟨791675, by rfl⟩ : syracuseStep 1055567 = 1583351) B1583351
theorem B1579871 : Blo 1052612 1579871 := bstep (se 1 (by rfl) ⟨1184903, by rfl⟩ : syracuseStep 1579871 = 2369807) B2369807
theorem B1055583 : Blo 1052612 1055583 := bstep (se 1 (by rfl) ⟨791687, by rfl⟩ : syracuseStep 1055583 = 1583375) B1583375
theorem B1579883 : Blo 1052612 1579883 := bstep (se 1 (by rfl) ⟨1184912, by rfl⟩ : syracuseStep 1579883 = 2369825) B2369825
theorem B1055611 : Blo 1052612 1055611 := bstep (se 1 (by rfl) ⟨791708, by rfl⟩ : syracuseStep 1055611 = 1583417) B1583417
theorem B1776559 : Blo 1052612 1776559 := bstep (se 1 (by rfl) ⟨1332419, by rfl⟩ : syracuseStep 1776559 = 2664839) B2664839
theorem B1186735 : Blo 1052612 1186735 := bstep (se 1 (by rfl) ⟨890051, by rfl⟩ : syracuseStep 1186735 = 1780103) B1780103
theorem B1055663 : Blo 1052612 1055663 := bstep (se 1 (by rfl) ⟨791747, by rfl⟩ : syracuseStep 1055663 = 1583495) B1583495
theorem B1055687 : Blo 1052612 1055687 := bstep (se 1 (by rfl) ⟨791765, by rfl⟩ : syracuseStep 1055687 = 1583531) B1583531
theorem B1055707 : Blo 1052612 1055707 := bstep (se 1 (by rfl) ⟨791780, by rfl⟩ : syracuseStep 1055707 = 1583561) B1583561
theorem B1776647 : Blo 1052612 1776647 := bstep (se 1 (by rfl) ⟨1332485, by rfl⟩ : syracuseStep 1776647 = 2664971) B2664971
theorem B1055783 : Blo 1052612 1055783 := bstep (se 1 (by rfl) ⟨791837, by rfl⟩ : syracuseStep 1055783 = 1583675) B1583675
theorem B1580111 : Blo 1052612 1580111 := bstep (se 1 (by rfl) ⟨1185083, by rfl⟩ : syracuseStep 1580111 = 2370167) B2370167
theorem B1055823 : Blo 1052612 1055823 := bstep (se 1 (by rfl) ⟨791867, by rfl⟩ : syracuseStep 1055823 = 1583735) B1583735
theorem B1055839 : Blo 1052612 1055839 := bstep (se 1 (by rfl) ⟨791879, by rfl⟩ : syracuseStep 1055839 = 1583759) B1583759
theorem B1055867 : Blo 1052612 1055867 := bstep (se 1 (by rfl) ⟨791900, by rfl⟩ : syracuseStep 1055867 = 1583801) B1583801
theorem B4005035 : Blo 1052612 4005035 := bstep (se 1 (by rfl) ⟨3003776, by rfl⟩ : syracuseStep 4005035 = 6007553) B6007553
theorem B1055919 : Blo 1052612 1055919 := bstep (se 1 (by rfl) ⟨791939, by rfl⟩ : syracuseStep 1055919 = 1583879) B1583879
theorem B1580231 : Blo 1052612 1580231 := bstep (se 1 (by rfl) ⟨1185173, by rfl⟩ : syracuseStep 1580231 = 2370347) B2370347
theorem B1055943 : Blo 1052612 1055943 := bstep (se 1 (by rfl) ⟨791957, by rfl⟩ : syracuseStep 1055943 = 1583915) B1583915
theorem B1055963 : Blo 1052612 1055963 := bstep (se 1 (by rfl) ⟨791972, by rfl⟩ : syracuseStep 1055963 = 1583945) B1583945
theorem B1056039 : Blo 1052612 1056039 := bstep (se 1 (by rfl) ⟨792029, by rfl⟩ : syracuseStep 1056039 = 1584059) B1584059
theorem B1056079 : Blo 1052612 1056079 := bstep (se 1 (by rfl) ⟨792059, by rfl⟩ : syracuseStep 1056079 = 1584119) B1584119
theorem B1776991 : Blo 1052612 1776991 := bstep (se 1 (by rfl) ⟨1332743, by rfl⟩ : syracuseStep 1776991 = 2665487) B2665487
theorem B1187167 : Blo 1052612 1187167 := bstep (se 1 (by rfl) ⟨890375, by rfl⟩ : syracuseStep 1187167 = 1780751) B1780751
theorem B1056095 : Blo 1052612 1056095 := bstep (se 1 (by rfl) ⟨792071, by rfl⟩ : syracuseStep 1056095 = 1584143) B1584143
theorem B1580393 : Blo 1052612 1580393 := bstep (se 2 (by rfl) ⟨592647, by rfl⟩ : syracuseStep 1580393 = 1185295) B1185295
theorem B1056123 : Blo 1052612 1056123 := bstep (se 1 (by rfl) ⟨792092, by rfl⟩ : syracuseStep 1056123 = 1584185) B1584185
theorem B1056175 : Blo 1052612 1056175 := bstep (se 1 (by rfl) ⟨792131, by rfl⟩ : syracuseStep 1056175 = 1584263) B1584263
theorem B43326899 : Blo 1052612 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B1777079 : Blo 1052612 1777079 := bstep (se 1 (by rfl) ⟨1332809, by rfl⟩ : syracuseStep 1777079 = 2665619) B2665619
theorem B1580471 : Blo 1052612 1580471 := bstep (se 1 (by rfl) ⟨1185353, by rfl⟩ : syracuseStep 1580471 = 2370707) B2370707
theorem B1056199 : Blo 1052612 1056199 := bstep (se 1 (by rfl) ⟨792149, by rfl⟩ : syracuseStep 1056199 = 1584299) B1584299
theorem B1580507 : Blo 1052612 1580507 := bstep (se 1 (by rfl) ⟨1185380, by rfl⟩ : syracuseStep 1580507 = 2370761) B2370761
theorem B1056219 : Blo 1052612 1056219 := bstep (se 1 (by rfl) ⟨792164, by rfl⟩ : syracuseStep 1056219 = 1584329) B1584329
theorem B1056295 : Blo 1052612 1056295 := bstep (se 1 (by rfl) ⟨792221, by rfl⟩ : syracuseStep 1056295 = 1584443) B1584443
theorem B1056335 : Blo 1052612 1056335 := bstep (se 1 (by rfl) ⟨792251, by rfl⟩ : syracuseStep 1056335 = 1584503) B1584503
theorem B1056351 : Blo 1052612 1056351 := bstep (se 1 (by rfl) ⟨792263, by rfl⟩ : syracuseStep 1056351 = 1584527) B1584527
theorem B1056379 : Blo 1052612 1056379 := bstep (se 1 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 1056379 = 1584569) B1584569
theorem B1056431 : Blo 1052612 1056431 := bstep (se 1 (by rfl) ⟨792323, by rfl⟩ : syracuseStep 1056431 = 1584647) B1584647
theorem B1187527 : Blo 1052612 1187527 := bstep (se 1 (by rfl) ⟨890645, by rfl⟩ : syracuseStep 1187527 = 1781291) B1781291
theorem B1056455 : Blo 1052612 1056455 := bstep (se 1 (by rfl) ⟨792341, by rfl⟩ : syracuseStep 1056455 = 1584683) B1584683
theorem B1056475 : Blo 1052612 1056475 := bstep (se 1 (by rfl) ⟨792356, by rfl⟩ : syracuseStep 1056475 = 1584713) B1584713
theorem B13868815 : Blo 1052612 13868815 := bstep (se 1 (by rfl) ⟨10401611, by rfl⟩ : syracuseStep 13868815 = 20803223) B20803223
theorem B1056551 : Blo 1052612 1056551 := bstep (se 1 (by rfl) ⟨792413, by rfl⟩ : syracuseStep 1056551 = 1584827) B1584827
theorem B1056591 : Blo 1052612 1056591 := bstep (se 1 (by rfl) ⟨792443, by rfl⟩ : syracuseStep 1056591 = 1584887) B1584887
theorem B1056607 : Blo 1052612 1056607 := bstep (se 1 (by rfl) ⟨792455, by rfl⟩ : syracuseStep 1056607 = 1584911) B1584911
theorem B2137961 : Blo 1052612 2137961 := bstep (se 2 (by rfl) ⟨801735, by rfl⟩ : syracuseStep 2137961 = 1603471) B1603471
theorem B2531179 : Blo 1052612 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B8003447 : Blo 1052612 8003447 := bstep (se 1 (by rfl) ⟨6002585, by rfl⟩ : syracuseStep 8003447 = 12005171) B12005171
theorem B1580975 : Blo 1052612 1580975 := bstep (se 1 (by rfl) ⟨1185731, by rfl⟩ : syracuseStep 1580975 = 2371463) B2371463
theorem B1777673 : Blo 1052612 1777673 := bstep (se 2 (by rfl) ⟨666627, by rfl⟩ : syracuseStep 1777673 = 1333255) B1333255
theorem B1581065 : Blo 1052612 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B1581095 : Blo 1052612 1581095 := bstep (se 1 (by rfl) ⟨1185821, by rfl⟩ : syracuseStep 1581095 = 2371643) B2371643
theorem B1581179 : Blo 1052612 1581179 := bstep (se 1 (by rfl) ⟨1185884, by rfl⟩ : syracuseStep 1581179 = 2371769) B2371769
theorem B1777835 : Blo 1052612 1777835 := bstep (se 1 (by rfl) ⟨1333376, by rfl⟩ : syracuseStep 1777835 = 2666753) B2666753
theorem B1581305 : Blo 1052612 1581305 := bstep (se 2 (by rfl) ⟨592989, by rfl⟩ : syracuseStep 1581305 = 1185979) B1185979
theorem B4006205 : Blo 1052612 4006205 := bstep (se 3 (by rfl) ⟨751163, by rfl⟩ : syracuseStep 4006205 = 1502327) B1502327
theorem B1581407 : Blo 1052612 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B1581419 : Blo 1052612 1581419 := bstep (se 1 (by rfl) ⟨1186064, by rfl⟩ : syracuseStep 1581419 = 2372129) B2372129
theorem B1188391 : Blo 1052612 1188391 := bstep (se 1 (by rfl) ⟨891293, by rfl⟩ : syracuseStep 1188391 = 1782587) B1782587
theorem B1778233 : Blo 1052612 1778233 := bstep (se 2 (by rfl) ⟨666837, by rfl⟩ : syracuseStep 1778233 = 1333675) B1333675
theorem B1581647 : Blo 1052612 1581647 := bstep (se 1 (by rfl) ⟨1186235, by rfl⟩ : syracuseStep 1581647 = 2372471) B2372471
theorem B4006523 : Blo 1052612 4006523 := bstep (se 1 (by rfl) ⟨3004892, by rfl⟩ : syracuseStep 4006523 = 6009785) B6009785
theorem B1778375 : Blo 1052612 1778375 := bstep (se 1 (by rfl) ⟨1333781, by rfl⟩ : syracuseStep 1778375 = 2667563) B2667563
theorem B1581767 : Blo 1052612 1581767 := bstep (se 1 (by rfl) ⟨1186325, by rfl⟩ : syracuseStep 1581767 = 2372651) B2372651
theorem B10822403 : Blo 1052612 10822403 := bstep (se 1 (by rfl) ⟨8116802, by rfl⟩ : syracuseStep 10822403 = 16233605) B16233605
theorem B4498249 : Blo 1052612 4498249 := bstep (se 2 (by rfl) ⟨1686843, by rfl⟩ : syracuseStep 4498249 = 3373687) B3373687
theorem B1778537 : Blo 1052612 1778537 := bstep (se 2 (by rfl) ⟨666951, by rfl⟩ : syracuseStep 1778537 = 1333903) B1333903
theorem B1581929 : Blo 1052612 1581929 := bstep (se 2 (by rfl) ⟨593223, by rfl⟩ : syracuseStep 1581929 = 1186447) B1186447
theorem B2368439 : Blo 1052612 2368439 := bstep (se 1 (by rfl) ⟨1776329, by rfl⟩ : syracuseStep 2368439 = 3552659) B3552659
theorem B4268983 : Blo 1052612 4268983 := bstep (se 1 (by rfl) ⟨3201737, by rfl⟩ : syracuseStep 4268983 = 6403475) B6403475
theorem B1582007 : Blo 1052612 1582007 := bstep (se 1 (by rfl) ⟨1186505, by rfl⟩ : syracuseStep 1582007 = 2373011) B2373011
theorem B2401211 : Blo 1052612 2401211 := bstep (se 1 (by rfl) ⟨1800908, by rfl⟩ : syracuseStep 2401211 = 3601817) B3601817
theorem B19243979 : Blo 1052612 19243979 := bstep (se 1 (by rfl) ⟨14432984, by rfl⟩ : syracuseStep 19243979 = 28865969) B28865969
theorem B1582043 : Blo 1052612 1582043 := bstep (se 1 (by rfl) ⟨1186532, by rfl⟩ : syracuseStep 1582043 = 2373065) B2373065
theorem B45622277 : Blo 1052612 45622277 := bstep (se 4 (by rfl) ⟨4277088, by rfl⟩ : syracuseStep 45622277 = 8554177) B8554177
theorem B13903001 : Blo 1052612 13903001 := bstep (se 2 (by rfl) ⟨5213625, by rfl⟩ : syracuseStep 13903001 = 10427251) B10427251
theorem B1778935 : Blo 1052612 1778935 := bstep (se 1 (by rfl) ⟨1334201, by rfl⟩ : syracuseStep 1778935 = 2668403) B2668403
theorem B7611671 : Blo 1052612 7611671 := bstep (se 1 (by rfl) ⟨5708753, by rfl⟩ : syracuseStep 7611671 = 11417507) B11417507
theorem B13673843 : Blo 1052612 13673843 := bstep (se 1 (by rfl) ⟨10255382, by rfl⟩ : syracuseStep 13673843 = 20510765) B20510765
theorem B1582511 : Blo 1052612 1582511 := bstep (se 1 (by rfl) ⟨1186883, by rfl⟩ : syracuseStep 1582511 = 2373767) B2373767
theorem B1779131 : Blo 1052612 1779131 := bstep (se 1 (by rfl) ⟨1334348, by rfl⟩ : syracuseStep 1779131 = 2668697) B2668697
theorem B6759881 : Blo 1052612 6759881 := bstep (se 2 (by rfl) ⟨2534955, by rfl⟩ : syracuseStep 6759881 = 5069911) B5069911
theorem B2369033 : Blo 1052612 2369033 := bstep (se 2 (by rfl) ⟨888387, by rfl⟩ : syracuseStep 2369033 = 1776775) B1776775
theorem B1582601 : Blo 1052612 1582601 := bstep (se 2 (by rfl) ⟨593475, by rfl⟩ : syracuseStep 1582601 = 1186951) B1186951
theorem B1779239 : Blo 1052612 1779239 := bstep (se 1 (by rfl) ⟨1334429, by rfl⟩ : syracuseStep 1779239 = 2668859) B2668859
theorem B1582631 : Blo 1052612 1582631 := bstep (se 1 (by rfl) ⟨1186973, by rfl⟩ : syracuseStep 1582631 = 2373947) B2373947
theorem B2139745 : Blo 1052612 2139745 := bstep (se 2 (by rfl) ⟨802404, by rfl⟩ : syracuseStep 2139745 = 1604809) B1604809
theorem B1582715 : Blo 1052612 1582715 := bstep (se 1 (by rfl) ⟨1187036, by rfl⟩ : syracuseStep 1582715 = 2374073) B2374073
theorem B7317229 : Blo 1052612 7317229 := bstep (se 3 (by rfl) ⟨1371980, by rfl⟩ : syracuseStep 7317229 = 2743961) B2743961
theorem B1582841 : Blo 1052612 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B6006595 : Blo 1052612 6006595 := bstep (se 1 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 6006595 = 9009893) B9009893
theorem B1779529 : Blo 1052612 1779529 := bstep (se 2 (by rfl) ⟨667323, by rfl⟩ : syracuseStep 1779529 = 1334647) B1334647
theorem B2369375 : Blo 1052612 2369375 := bstep (se 1 (by rfl) ⟨1777031, by rfl⟩ : syracuseStep 2369375 = 3554063) B3554063
theorem B1582943 : Blo 1052612 1582943 := bstep (se 1 (by rfl) ⟨1187207, by rfl⟩ : syracuseStep 1582943 = 2374415) B2374415
theorem B1779563 : Blo 1052612 1779563 := bstep (se 1 (by rfl) ⟨1334672, by rfl⟩ : syracuseStep 1779563 = 2669345) B2669345
theorem B1582955 : Blo 1052612 1582955 := bstep (se 1 (by rfl) ⟨1187216, by rfl⟩ : syracuseStep 1582955 = 2374433) B2374433
theorem B4007951 : Blo 1052612 4007951 := bstep (se 1 (by rfl) ⟨3005963, by rfl⟩ : syracuseStep 4007951 = 6011927) B6011927
theorem B2369555 : Blo 1052612 2369555 := bstep (se 1 (by rfl) ⟨1777166, by rfl⟩ : syracuseStep 2369555 = 3554333) B3554333
theorem B1583183 : Blo 1052612 1583183 := bstep (se 1 (by rfl) ⟨1187387, by rfl⟩ : syracuseStep 1583183 = 2374775) B2374775
theorem B1583303 : Blo 1052612 1583303 := bstep (se 1 (by rfl) ⟨1187477, by rfl⟩ : syracuseStep 1583303 = 2374955) B2374955
theorem B1779961 : Blo 1052612 1779961 := bstep (se 2 (by rfl) ⟨667485, by rfl⟩ : syracuseStep 1779961 = 1334971) B1334971
theorem B2664809 : Blo 1052612 2664809 := bstep (se 2 (by rfl) ⟨999303, by rfl⟩ : syracuseStep 2664809 = 1998607) B1998607
theorem B2369897 : Blo 1052612 2369897 := bstep (se 2 (by rfl) ⟨888711, by rfl⟩ : syracuseStep 2369897 = 1777423) B1777423
theorem B1583465 : Blo 1052612 1583465 := bstep (se 2 (by rfl) ⟨593799, by rfl⟩ : syracuseStep 1583465 = 1187599) B1187599
theorem B1583543 : Blo 1052612 1583543 := bstep (se 1 (by rfl) ⟨1187657, by rfl⟩ : syracuseStep 1583543 = 2375315) B2375315
theorem B6760907 : Blo 1052612 6760907 := bstep (se 1 (by rfl) ⟨5070680, by rfl⟩ : syracuseStep 6760907 = 10141361) B10141361
theorem B1583579 : Blo 1052612 1583579 := bstep (se 1 (by rfl) ⟨1187684, by rfl⟩ : syracuseStep 1583579 = 2375369) B2375369
theorem B1780231 : Blo 1052612 1780231 := bstep (se 1 (by rfl) ⟨1335173, by rfl⟩ : syracuseStep 1780231 = 2670347) B2670347
theorem B8563259 : Blo 1052612 8563259 := bstep (se 1 (by rfl) ⟨6422444, by rfl⟩ : syracuseStep 8563259 = 12844889) B12844889
theorem B2468551 : Blo 1052612 2468551 := bstep (se 1 (by rfl) ⟨1851413, by rfl⟩ : syracuseStep 2468551 = 3702827) B3702827
theorem B5483219 : Blo 1052612 5483219 := bstep (se 1 (by rfl) ⟨4112414, by rfl⟩ : syracuseStep 5483219 = 8224829) B8224829
theorem B40676131 : Blo 1052612 40676131 := bstep (se 1 (by rfl) ⟨30507098, by rfl⟩ : syracuseStep 40676131 = 61014197) B61014197
theorem B1584047 : Blo 1052612 1584047 := bstep (se 1 (by rfl) ⟨1188035, by rfl⟩ : syracuseStep 1584047 = 2376071) B2376071
theorem B1780663 : Blo 1052612 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B2370491 : Blo 1052612 2370491 := bstep (se 1 (by rfl) ⟨1777868, by rfl⟩ : syracuseStep 2370491 = 3555737) B3555737
theorem B17542129 : Blo 1052612 17542129 := bstep (se 2 (by rfl) ⟨6578298, by rfl⟩ : syracuseStep 17542129 = 13156597) B13156597
theorem B1584137 : Blo 1052612 1584137 := bstep (se 2 (by rfl) ⟨594051, by rfl⟩ : syracuseStep 1584137 = 1188103) B1188103
theorem B1584167 : Blo 1052612 1584167 := bstep (se 1 (by rfl) ⟨1188125, by rfl⟩ : syracuseStep 1584167 = 2376251) B2376251
theorem B2370617 : Blo 1052612 2370617 := bstep (se 2 (by rfl) ⟨888981, by rfl⟩ : syracuseStep 2370617 = 1777963) B1777963
theorem B1780859 : Blo 1052612 1780859 := bstep (se 1 (by rfl) ⟨1335644, by rfl⟩ : syracuseStep 1780859 = 2671289) B2671289
theorem B1584251 : Blo 1052612 1584251 := bstep (se 1 (by rfl) ⟨1188188, by rfl⟩ : syracuseStep 1584251 = 2376377) B2376377
theorem B8006849 : Blo 1052612 8006849 := bstep (se 2 (by rfl) ⟨3002568, by rfl⟩ : syracuseStep 8006849 = 6005137) B6005137
theorem B1584377 : Blo 1052612 1584377 := bstep (se 2 (by rfl) ⟨594141, by rfl⟩ : syracuseStep 1584377 = 1188283) B1188283
theorem B1584479 : Blo 1052612 1584479 := bstep (se 1 (by rfl) ⟨1188359, by rfl⟩ : syracuseStep 1584479 = 2376719) B2376719
theorem B1584491 : Blo 1052612 1584491 := bstep (se 1 (by rfl) ⟨1188368, by rfl⟩ : syracuseStep 1584491 = 2376737) B2376737
theorem B2370959 : Blo 1052612 2370959 := bstep (se 1 (by rfl) ⟨1778219, by rfl⟩ : syracuseStep 2370959 = 3556439) B3556439
theorem B10857901 : Blo 1052612 10857901 := bstep (se 3 (by rfl) ⟨2035856, by rfl⟩ : syracuseStep 10857901 = 4071713) B4071713
theorem B2665993 : Blo 1052612 2665993 := bstep (se 2 (by rfl) ⟨999747, by rfl⟩ : syracuseStep 2665993 = 1999495) B1999495
theorem B1781257 : Blo 1052612 1781257 := bstep (se 2 (by rfl) ⟨667971, by rfl⟩ : syracuseStep 1781257 = 1335943) B1335943
theorem B9023015 : Blo 1052612 9023015 := bstep (se 1 (by rfl) ⟨6767261, by rfl⟩ : syracuseStep 9023015 = 13534523) B13534523
theorem B1584719 : Blo 1052612 1584719 := bstep (se 1 (by rfl) ⟨1188539, by rfl⟩ : syracuseStep 1584719 = 2377079) B2377079
theorem B4009607 : Blo 1052612 4009607 := bstep (se 1 (by rfl) ⟨3007205, by rfl⟩ : syracuseStep 4009607 = 6014411) B6014411
theorem B1781419 : Blo 1052612 1781419 := bstep (se 1 (by rfl) ⟨1336064, by rfl⟩ : syracuseStep 1781419 = 2672129) B2672129
theorem B1584839 : Blo 1052612 1584839 := bstep (se 1 (by rfl) ⟨1188629, by rfl⟩ : syracuseStep 1584839 = 2377259) B2377259
theorem B2371283 : Blo 1052612 2371283 := bstep (se 1 (by rfl) ⟨1778462, by rfl⟩ : syracuseStep 2371283 = 3556925) B3556925
theorem B4501241 : Blo 1052612 4501241 := bstep (se 2 (by rfl) ⟨1687965, by rfl⟩ : syracuseStep 4501241 = 3375931) B3375931
theorem B4501291 : Blo 1052612 4501291 := bstep (se 1 (by rfl) ⟨3375968, by rfl⟩ : syracuseStep 4501291 = 6751937) B6751937
theorem B3419977 : Blo 1052612 3419977 := bstep (se 2 (by rfl) ⟨1282491, by rfl⟩ : syracuseStep 3419977 = 2564983) B2564983
theorem B1781723 : Blo 1052612 1781723 := bstep (se 1 (by rfl) ⟨1336292, by rfl⟩ : syracuseStep 1781723 = 2672585) B2672585
theorem B1781959 : Blo 1052612 1781959 := bstep (se 1 (by rfl) ⟨1336469, by rfl⟩ : syracuseStep 1781959 = 2672939) B2672939
theorem B10400075 : Blo 1052612 10400075 := bstep (se 1 (by rfl) ⟨7800056, by rfl⟩ : syracuseStep 10400075 = 15600113) B15600113
theorem B1782121 : Blo 1052612 1782121 := bstep (se 2 (by rfl) ⟨668295, by rfl⟩ : syracuseStep 1782121 = 1336591) B1336591
theorem B4010593 : Blo 1052612 4010593 := bstep (se 2 (by rfl) ⟨1503972, by rfl⟩ : syracuseStep 4010593 = 3007945) B3007945
theorem B2372219 : Blo 1052612 2372219 := bstep (se 1 (by rfl) ⟨1779164, by rfl⟩ : syracuseStep 2372219 = 3558329) B3558329
theorem B3846865 : Blo 1052612 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B2372345 : Blo 1052612 2372345 := bstep (se 2 (by rfl) ⟨889629, by rfl⟩ : syracuseStep 2372345 = 1779259) B1779259
theorem B2667451 : Blo 1052612 2667451 := bstep (se 1 (by rfl) ⟨2000588, by rfl⟩ : syracuseStep 2667451 = 4001177) B4001177
theorem B1782715 : Blo 1052612 1782715 := bstep (se 1 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 1782715 = 2674073) B2674073
theorem B2372615 : Blo 1052612 2372615 := bstep (se 1 (by rfl) ⟨1779461, by rfl⟩ : syracuseStep 2372615 = 3558923) B3558923
theorem B1782823 : Blo 1052612 1782823 := bstep (se 1 (by rfl) ⟨1337117, by rfl⟩ : syracuseStep 1782823 = 2674235) B2674235
theorem B6763571 : Blo 1052612 6763571 := bstep (se 1 (by rfl) ⟨5072678, by rfl⟩ : syracuseStep 6763571 = 10145357) B10145357
theorem B4011065 : Blo 1052612 4011065 := bstep (se 2 (by rfl) ⟨1504149, by rfl⟩ : syracuseStep 4011065 = 3008299) B3008299
theorem B4273231 : Blo 1052612 4273231 := bstep (se 1 (by rfl) ⟨3204923, by rfl⟩ : syracuseStep 4273231 = 6409847) B6409847
theorem B2372687 : Blo 1052612 2372687 := bstep (se 1 (by rfl) ⟨1779515, by rfl⟩ : syracuseStep 2372687 = 3559031) B3559031
theorem B3552713 : Blo 1052612 3552713 := bstep (se 2 (by rfl) ⟨1332267, by rfl⟩ : syracuseStep 3552713 = 2664535) B2664535
theorem B2373083 : Blo 1052612 2373083 := bstep (se 1 (by rfl) ⟨1779812, by rfl⟩ : syracuseStep 2373083 = 3559625) B3559625
theorem B4503239 : Blo 1052612 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B3552983 : Blo 1052612 3552983 := bstep (se 1 (by rfl) ⟨2664737, by rfl⟩ : syracuseStep 3552983 = 5329475) B5329475
theorem B1128287 : Blo 1052612 1128287 := bstep (se 1 (by rfl) ⟨846215, by rfl⟩ : syracuseStep 1128287 = 1692431) B1692431
theorem B3553199 : Blo 1052612 3553199 := bstep (se 1 (by rfl) ⟨2664899, by rfl⟩ : syracuseStep 3553199 = 5329799) B5329799
theorem B2373551 : Blo 1052612 2373551 := bstep (se 1 (by rfl) ⟨1780163, by rfl⟩ : syracuseStep 2373551 = 3560327) B3560327
theorem B6764573 : Blo 1052612 6764573 := bstep (se 3 (by rfl) ⟨1268357, by rfl⟩ : syracuseStep 6764573 = 2536715) B2536715
theorem B8009765 : Blo 1052612 8009765 := bstep (se 4 (by rfl) ⟨750915, by rfl⟩ : syracuseStep 8009765 = 1501831) B1501831
theorem B6010969 : Blo 1052612 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B2373803 : Blo 1052612 2373803 := bstep (se 1 (by rfl) ⟨1780352, by rfl⟩ : syracuseStep 2373803 = 3560705) B3560705
theorem B2537993 : Blo 1052612 2537993 := bstep (se 2 (by rfl) ⟨951747, by rfl⟩ : syracuseStep 2537993 = 1903495) B1903495
theorem B2374343 : Blo 1052612 2374343 := bstep (se 1 (by rfl) ⟨1780757, by rfl⟩ : syracuseStep 2374343 = 3561515) B3561515
theorem B9616157 : Blo 1052612 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B2670043 : Blo 1052612 2670043 := bstep (se 1 (by rfl) ⟨2002532, by rfl⟩ : syracuseStep 2670043 = 4005065) B4005065
theorem B1687049 : Blo 1052612 1687049 := bstep (se 2 (by rfl) ⟨632643, by rfl⟩ : syracuseStep 1687049 = 1265287) B1265287
theorem B2997785 : Blo 1052612 2997785 := bstep (se 2 (by rfl) ⟨1124169, by rfl⟩ : syracuseStep 2997785 = 2248339) B2248339
theorem B2375207 : Blo 1052612 2375207 := bstep (se 1 (by rfl) ⟨1781405, by rfl⟩ : syracuseStep 2375207 = 3562811) B3562811
theorem B2375531 : Blo 1052612 2375531 := bstep (se 1 (by rfl) ⟨1781648, by rfl⟩ : syracuseStep 2375531 = 3563297) B3563297
theorem B2375585 : Blo 1052612 2375585 := bstep (se 2 (by rfl) ⟨890844, by rfl⟩ : syracuseStep 2375585 = 1781689) B1781689
theorem B4505615 : Blo 1052612 4505615 := bstep (se 1 (by rfl) ⟨3379211, by rfl⟩ : syracuseStep 4505615 = 6758423) B6758423
theorem B2670671 : Blo 1052612 2670671 := bstep (se 1 (by rfl) ⟨2003003, by rfl⟩ : syracuseStep 2670671 = 4006007) B4006007
theorem B3555575 : Blo 1052612 3555575 := bstep (se 1 (by rfl) ⟨2666681, by rfl⟩ : syracuseStep 3555575 = 5333363) B5333363
theorem B2375927 : Blo 1052612 2375927 := bstep (se 1 (by rfl) ⟨1781945, by rfl⟩ : syracuseStep 2375927 = 3563891) B3563891
theorem B3424523 : Blo 1052612 3424523 := bstep (se 1 (by rfl) ⟨2568392, by rfl⟩ : syracuseStep 3424523 = 5136785) B5136785
theorem B30458213 : Blo 1052612 30458213 := bstep (se 4 (by rfl) ⟨2855457, by rfl⟩ : syracuseStep 30458213 = 5710915) B5710915
theorem B3555899 : Blo 1052612 3555899 := bstep (se 1 (by rfl) ⟨2666924, by rfl⟩ : syracuseStep 3555899 = 5333849) B5333849
theorem B13681325 : Blo 1052612 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B2671319 : Blo 1052612 2671319 := bstep (se 1 (by rfl) ⟨2003489, by rfl⟩ : syracuseStep 2671319 = 4006979) B4006979
theorem B3556169 : Blo 1052612 3556169 := bstep (se 2 (by rfl) ⟨1333563, by rfl⟩ : syracuseStep 3556169 = 2667127) B2667127
theorem B2376521 : Blo 1052612 2376521 := bstep (se 2 (by rfl) ⟨891195, by rfl⟩ : syracuseStep 2376521 = 1782391) B1782391
theorem B10961771 : Blo 1052612 10961771 := bstep (se 1 (by rfl) ⟨8221328, by rfl⟩ : syracuseStep 10961771 = 16442657) B16442657
theorem B14435293 : Blo 1052612 14435293 := bstep (se 3 (by rfl) ⟨2706617, by rfl⟩ : syracuseStep 14435293 = 5413235) B5413235
theorem B2409551 : Blo 1052612 2409551 := bstep (se 1 (by rfl) ⟨1807163, by rfl⟩ : syracuseStep 2409551 = 3614327) B3614327
theorem B12829913 : Blo 1052612 12829913 := bstep (se 2 (by rfl) ⟨4811217, by rfl⟩ : syracuseStep 12829913 = 9622435) B9622435
theorem B2377313 : Blo 1052612 2377313 := bstep (se 2 (by rfl) ⟨891492, by rfl⟩ : syracuseStep 2377313 = 1782985) B1782985
theorem B3557303 : Blo 1052612 3557303 := bstep (se 1 (by rfl) ⟨2667977, by rfl⟩ : syracuseStep 3557303 = 5335955) B5335955
theorem B13715405 : Blo 1052612 13715405 := bstep (se 3 (by rfl) ⟨2571638, by rfl⟩ : syracuseStep 13715405 = 5143277) B5143277
theorem B6768697 : Blo 1052612 6768697 := bstep (se 2 (by rfl) ⟨2538261, by rfl⟩ : syracuseStep 6768697 = 5076523) B5076523
theorem B48679217 : Blo 1052612 48679217 := bstep (se 2 (by rfl) ⟨18254706, by rfl⟩ : syracuseStep 48679217 = 36509413) B36509413
theorem B3000701 : Blo 1052612 3000701 := bstep (se 3 (by rfl) ⟨562631, by rfl⟩ : syracuseStep 3000701 = 1125263) B1125263
theorem B3557897 : Blo 1052612 3557897 := bstep (se 2 (by rfl) ⟨1334211, by rfl⟩ : syracuseStep 3557897 = 2668423) B2668423
theorem B3001043 : Blo 1052612 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B20237201 : Blo 1052612 20237201 := bstep (se 2 (by rfl) ⟨7588950, by rfl⟩ : syracuseStep 20237201 = 15177901) B15177901
theorem B2673911 : Blo 1052612 2673911 := bstep (se 1 (by rfl) ⟨2005433, by rfl⟩ : syracuseStep 2673911 = 4010867) B4010867
theorem B3558761 : Blo 1052612 3558761 := bstep (se 2 (by rfl) ⟨1334535, by rfl⟩ : syracuseStep 3558761 = 2669071) B2669071
theorem B2248391 : Blo 1052612 2248391 := bstep (se 1 (by rfl) ⟨1686293, by rfl⟩ : syracuseStep 2248391 = 3372587) B3372587
theorem B8015597 : Blo 1052612 8015597 := bstep (se 3 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 8015597 = 3005849) B3005849
theorem B11423521 : Blo 1052612 11423521 := bstep (se 2 (by rfl) ⟨4283820, by rfl⟩ : syracuseStep 11423521 = 8567641) B8567641
theorem B3559355 : Blo 1052612 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B8540167 : Blo 1052612 8540167 := bstep (se 1 (by rfl) ⟨6405125, by rfl⟩ : syracuseStep 8540167 = 12810251) B12810251
theorem B3002615 : Blo 1052612 3002615 := bstep (se 1 (by rfl) ⟨2251961, by rfl⟩ : syracuseStep 3002615 = 4503923) B4503923
theorem B4510039 : Blo 1052612 4510039 := bstep (se 1 (by rfl) ⟨3382529, by rfl⟩ : syracuseStep 4510039 = 6765059) B6765059
theorem B8016569 : Blo 1052612 8016569 := bstep (se 2 (by rfl) ⟨3006213, by rfl⟩ : syracuseStep 8016569 = 6012427) B6012427
theorem B6410963 : Blo 1052612 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B4281275 : Blo 1052612 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B4117661 : Blo 1052612 4117661 := bstep (se 3 (by rfl) ⟨772061, by rfl⟩ : syracuseStep 4117661 = 1544123) B1544123
theorem B5330123 : Blo 1052612 5330123 := bstep (se 1 (by rfl) ⟨3997592, by rfl⟩ : syracuseStep 5330123 = 7995185) B7995185
theorem B8115599 : Blo 1052612 8115599 := bstep (se 1 (by rfl) ⟨6086699, by rfl⟩ : syracuseStep 8115599 = 12173399) B12173399
theorem B3659251 : Blo 1052612 3659251 := bstep (se 1 (by rfl) ⟨2744438, by rfl⟩ : syracuseStep 3659251 = 5488877) B5488877
theorem B3561083 : Blo 1052612 3561083 := bstep (se 1 (by rfl) ⟨2670812, by rfl⟩ : syracuseStep 3561083 = 5341625) B5341625
theorem B8017541 : Blo 1052612 8017541 := bstep (se 4 (by rfl) ⟨751644, by rfl⟩ : syracuseStep 8017541 = 1503289) B1503289
theorem B4511371 : Blo 1052612 4511371 := bstep (se 1 (by rfl) ⟨3383528, by rfl⟩ : syracuseStep 4511371 = 6767057) B6767057
theorem B3561245 : Blo 1052612 3561245 := bstep (se 3 (by rfl) ⟨667733, by rfl⟩ : syracuseStep 3561245 = 1335467) B1335467
theorem B6084395 : Blo 1052612 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B12834769 : Blo 1052612 12834769 := bstep (se 2 (by rfl) ⟨4813038, by rfl⟩ : syracuseStep 12834769 = 9626077) B9626077
theorem B3561947 : Blo 1052612 3561947 := bstep (se 1 (by rfl) ⟨2671460, by rfl⟩ : syracuseStep 3561947 = 5342921) B5342921
theorem B3005257 : Blo 1052612 3005257 := bstep (se 2 (by rfl) ⟨1126971, by rfl⟩ : syracuseStep 3005257 = 2253943) B2253943
theorem B3562649 : Blo 1052612 3562649 := bstep (se 2 (by rfl) ⟨1335993, by rfl⟩ : syracuseStep 3562649 = 2671987) B2671987
theorem B12016835 : Blo 1052612 12016835 := bstep (se 1 (by rfl) ⟨9012626, by rfl⟩ : syracuseStep 12016835 = 18025253) B18025253
theorem B9264527 : Blo 1052612 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B9002785 : Blo 1052612 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B3203003 : Blo 1052612 3203003 := bstep (se 1 (by rfl) ⟨2402252, by rfl⟩ : syracuseStep 3203003 = 4804505) B4804505
theorem B8019971 : Blo 1052612 8019971 := bstep (se 1 (by rfl) ⟨6014978, by rfl⟩ : syracuseStep 8019971 = 12029957) B12029957
theorem B3563837 : Blo 1052612 3563837 := bstep (se 3 (by rfl) ⟨668219, by rfl⟩ : syracuseStep 3563837 = 1336439) B1336439
theorem B1335847 : Blo 1052612 1335847 := bstep (se 1 (by rfl) ⟨1001885, by rfl⟩ : syracuseStep 1335847 = 2003771) B2003771
theorem B12018293 : Blo 1052612 12018293 := bstep (se 5 (by rfl) ⟨563357, by rfl⟩ : syracuseStep 12018293 = 1126715) B1126715
theorem B3007115 : Blo 1052612 3007115 := bstep (se 1 (by rfl) ⟨2255336, by rfl⟩ : syracuseStep 3007115 = 4510673) B4510673
theorem B1336171 : Blo 1052612 1336171 := bstep (se 1 (by rfl) ⟨1002128, by rfl⟩ : syracuseStep 1336171 = 2004257) B2004257
theorem B3564701 : Blo 1052612 3564701 := bstep (se 3 (by rfl) ⟨668381, by rfl⟩ : syracuseStep 3564701 = 1336763) B1336763
theorem B3565241 : Blo 1052612 3565241 := bstep (se 2 (by rfl) ⟨1336965, by rfl⟩ : syracuseStep 3565241 = 2673931) B2673931
theorem B5695393 : Blo 1052612 5695393 := bstep (se 2 (by rfl) ⟨2135772, by rfl⟩ : syracuseStep 5695393 = 4271545) B4271545
theorem B5335307 : Blo 1052612 5335307 := bstep (se 1 (by rfl) ⟨4001480, by rfl⟩ : syracuseStep 5335307 = 8002961) B8002961
theorem B3565835 : Blo 1052612 3565835 := bstep (se 1 (by rfl) ⟨2674376, by rfl⟩ : syracuseStep 3565835 = 5348753) B5348753
theorem B1501535 : Blo 1052612 1501535 := bstep (se 1 (by rfl) ⟨1126151, by rfl⟩ : syracuseStep 1501535 = 2252303) B2252303
theorem B8022401 : Blo 1052612 8022401 := bstep (se 2 (by rfl) ⟨3008400, by rfl⟩ : syracuseStep 8022401 = 6016801) B6016801
theorem B1501615 : Blo 1052612 1501615 := bstep (se 1 (by rfl) ⟨1126211, by rfl⟩ : syracuseStep 1501615 = 2252423) B2252423
theorem B1501735 : Blo 1052612 1501735 := bstep (se 1 (by rfl) ⟨1126301, by rfl⟩ : syracuseStep 1501735 = 2252603) B2252603
theorem B1502059 : Blo 1052612 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B2255951 : Blo 1052612 2255951 := bstep (se 1 (by rfl) ⟨1691963, by rfl⟩ : syracuseStep 2255951 = 3383927) B3383927
theorem B7204211 : Blo 1052612 7204211 := bstep (se 1 (by rfl) ⟨5403158, by rfl⟩ : syracuseStep 7204211 = 10806317) B10806317
theorem B10153511 : Blo 1052612 10153511 := bstep (se 1 (by rfl) ⟨7615133, by rfl⟩ : syracuseStep 10153511 = 15230267) B15230267
theorem B5336765 : Blo 1052612 5336765 := bstep (se 3 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 5336765 = 2001287) B2001287
theorem B22802141 : Blo 1052612 22802141 := bstep (se 3 (by rfl) ⟨4275401, by rfl⟩ : syracuseStep 22802141 = 8550803) B8550803
theorem B5336927 : Blo 1052612 5336927 := bstep (se 1 (by rfl) ⟨4002695, by rfl⟩ : syracuseStep 5336927 = 8005391) B8005391
theorem B1602011 : Blo 1052612 1602011 := bstep (se 1 (by rfl) ⟨1201508, by rfl⟩ : syracuseStep 1602011 = 2403017) B2403017
theorem B2847241 : Blo 1052612 2847241 := bstep (se 2 (by rfl) ⟨1067715, by rfl⟩ : syracuseStep 2847241 = 2135431) B2135431
theorem B16249369 : Blo 1052612 16249369 := bstep (se 2 (by rfl) ⟨6093513, by rfl⟩ : syracuseStep 16249369 = 12187027) B12187027
theorem B1143335 : Blo 1052612 1143335 := bstep (se 1 (by rfl) ⟨857501, by rfl⟩ : syracuseStep 1143335 = 1715003) B1715003
theorem B6746759 : Blo 1052612 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B19264715 : Blo 1052612 19264715 := bstep (se 1 (by rfl) ⟨14448536, by rfl⟩ : syracuseStep 19264715 = 28897073) B28897073
theorem B10123213 : Blo 1052612 10123213 := bstep (se 3 (by rfl) ⟨1898102, by rfl⟩ : syracuseStep 10123213 = 3796205) B3796205
theorem B5339681 : Blo 1052612 5339681 := bstep (se 2 (by rfl) ⟨2002380, by rfl⟩ : syracuseStep 5339681 = 4004761) B4004761
theorem B3373919 : Blo 1052612 3373919 := bstep (se 1 (by rfl) ⟨2530439, by rfl⟩ : syracuseStep 3373919 = 5060879) B5060879
theorem B1899769 : Blo 1052612 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B6749477 : Blo 1052612 6749477 := bstep (se 4 (by rfl) ⟨632763, by rfl⟩ : syracuseStep 6749477 = 1265527) B1265527
theorem B30768569 : Blo 1052612 30768569 := bstep (se 2 (by rfl) ⟨11538213, by rfl⟩ : syracuseStep 30768569 = 23076427) B23076427
theorem B1605199 : Blo 1052612 1605199 := bstep (se 1 (by rfl) ⟨1203899, by rfl⟩ : syracuseStep 1605199 = 2407799) B2407799
theorem B11993507 : Blo 1052612 11993507 := bstep (se 1 (by rfl) ⟨8995130, by rfl⟩ : syracuseStep 11993507 = 17990261) B17990261
theorem B1606367 : Blo 1052612 1606367 := bstep (se 1 (by rfl) ⟨1204775, by rfl⟩ : syracuseStep 1606367 = 2409551) B2409551
theorem B8553275 : Blo 1052612 8553275 := bstep (se 1 (by rfl) ⟨6414956, by rfl⟩ : syracuseStep 8553275 = 12829913) B12829913
theorem B9634619 : Blo 1052612 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B5997665 : Blo 1052612 5997665 := bstep (se 2 (by rfl) ⟨2249124, by rfl⟩ : syracuseStep 5997665 = 4498249) B4498249
theorem B6751475 : Blo 1052612 6751475 := bstep (se 1 (by rfl) ⟨5063606, by rfl⟩ : syracuseStep 6751475 = 10127213) B10127213
theorem B5768491 : Blo 1052612 5768491 := bstep (se 1 (by rfl) ⟨4326368, by rfl⟩ : syracuseStep 5768491 = 8652737) B8652737
theorem B9143603 : Blo 1052612 9143603 := bstep (se 1 (by rfl) ⟨6857702, by rfl⟩ : syracuseStep 9143603 = 13715405) B13715405
theorem B3048893 : Blo 1052612 3048893 := bstep (se 3 (by rfl) ⟨571667, by rfl⟩ : syracuseStep 3048893 = 1143335) B1143335
theorem B2000467 : Blo 1052612 2000467 := bstep (se 1 (by rfl) ⟨1500350, by rfl⟩ : syracuseStep 2000467 = 3000701) B3000701
theorem B7997129 : Blo 1052612 7997129 := bstep (se 2 (by rfl) ⟨2998923, by rfl⟩ : syracuseStep 7997129 = 5997847) B5997847
theorem B2000695 : Blo 1052612 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B2852993 : Blo 1052612 2852993 := bstep (se 2 (by rfl) ⟨1069872, by rfl⟩ : syracuseStep 2852993 = 2139745) B2139745
theorem B29231389 : Blo 1052612 29231389 := bstep (se 3 (by rfl) ⟨5480885, by rfl⟩ : syracuseStep 29231389 = 10961771) B10961771
theorem B5343731 : Blo 1052612 5343731 := bstep (se 1 (by rfl) ⟨4007798, by rfl⟩ : syracuseStep 5343731 = 8015597) B8015597
theorem B6753091 : Blo 1052612 6753091 := bstep (se 1 (by rfl) ⟨5064818, by rfl⟩ : syracuseStep 6753091 = 10129637) B10129637
theorem B2001743 : Blo 1052612 2001743 := bstep (se 1 (by rfl) ⟨1501307, by rfl⟩ : syracuseStep 2001743 = 3002615) B3002615
theorem B1444969 : Blo 1052612 1444969 := bstep (se 2 (by rfl) ⟨541863, by rfl⟩ : syracuseStep 1444969 = 1083727) B1083727
theorem B5344379 : Blo 1052612 5344379 := bstep (se 1 (by rfl) ⟨4008284, by rfl⟩ : syracuseStep 5344379 = 8016569) B8016569
theorem B2002153 : Blo 1052612 2002153 := bstep (se 2 (by rfl) ⟨750807, by rfl⟩ : syracuseStep 2002153 = 1501615) B1501615
theorem B2002313 : Blo 1052612 2002313 := bstep (se 2 (by rfl) ⟨750867, by rfl⟩ : syracuseStep 2002313 = 1501735) B1501735
theorem B5410399 : Blo 1052612 5410399 := bstep (se 1 (by rfl) ⟨4057799, by rfl⟩ : syracuseStep 5410399 = 8115599) B8115599
theorem B54234841 : Blo 1052612 54234841 := bstep (se 2 (by rfl) ⟨20338065, by rfl⟩ : syracuseStep 54234841 = 40676131) B40676131
theorem B5345027 : Blo 1052612 5345027 := bstep (se 1 (by rfl) ⟨4008770, by rfl⟩ : syracuseStep 5345027 = 8017541) B8017541
theorem B9899819 : Blo 1052612 9899819 := bstep (se 1 (by rfl) ⟨7424864, by rfl⟩ : syracuseStep 9899819 = 14849729) B14849729
theorem B2002745 : Blo 1052612 2002745 := bstep (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) B1502059
theorem B1052623 : Blo 1052612 1052623 := bstep (se 1 (by rfl) ⟨789467, by rfl⟩ : syracuseStep 1052623 = 1578935) B1578935
theorem B1052647 : Blo 1052612 1052647 := bstep (se 1 (by rfl) ⟨789485, by rfl⟩ : syracuseStep 1052647 = 1578971) B1578971
theorem B1052959 : Blo 1052612 1052959 := bstep (se 1 (by rfl) ⟨789719, by rfl⟩ : syracuseStep 1052959 = 1579439) B1579439
theorem B1053019 : Blo 1052612 1053019 := bstep (se 1 (by rfl) ⟨789764, by rfl⟩ : syracuseStep 1053019 = 1579529) B1579529
theorem B3805547 : Blo 1052612 3805547 := bstep (se 1 (by rfl) ⟨2854160, by rfl⟩ : syracuseStep 3805547 = 5708321) B5708321
theorem B1053039 : Blo 1052612 1053039 := bstep (se 1 (by rfl) ⟨789779, by rfl⟩ : syracuseStep 1053039 = 1579559) B1579559
theorem B1053095 : Blo 1052612 1053095 := bstep (se 1 (by rfl) ⟨789821, by rfl⟩ : syracuseStep 1053095 = 1579643) B1579643
theorem B1184251 : Blo 1052612 1184251 := bstep (se 1 (by rfl) ⟨888188, by rfl⟩ : syracuseStep 1184251 = 1776377) B1776377
theorem B1053179 : Blo 1052612 1053179 := bstep (se 1 (by rfl) ⟨789884, by rfl⟩ : syracuseStep 1053179 = 1579769) B1579769
theorem B1053247 : Blo 1052612 1053247 := bstep (se 1 (by rfl) ⟨789935, by rfl⟩ : syracuseStep 1053247 = 1579871) B1579871
theorem B1053255 : Blo 1052612 1053255 := bstep (se 1 (by rfl) ⟨789941, by rfl⟩ : syracuseStep 1053255 = 1579883) B1579883
theorem B1184431 : Blo 1052612 1184431 := bstep (se 1 (by rfl) ⟨888323, by rfl⟩ : syracuseStep 1184431 = 1776647) B1776647
theorem B1053407 : Blo 1052612 1053407 := bstep (se 1 (by rfl) ⟨790055, by rfl⟩ : syracuseStep 1053407 = 1580111) B1580111
theorem B1053487 : Blo 1052612 1053487 := bstep (se 1 (by rfl) ⟨790115, by rfl⟩ : syracuseStep 1053487 = 1580231) B1580231
theorem B1053595 : Blo 1052612 1053595 := bstep (se 1 (by rfl) ⟨790196, by rfl⟩ : syracuseStep 1053595 = 1580393) B1580393
theorem B1184719 : Blo 1052612 1184719 := bstep (se 1 (by rfl) ⟨888539, by rfl⟩ : syracuseStep 1184719 = 1777079) B1777079
theorem B1053647 : Blo 1052612 1053647 := bstep (se 1 (by rfl) ⟨790235, by rfl⟩ : syracuseStep 1053647 = 1580471) B1580471
theorem B1053671 : Blo 1052612 1053671 := bstep (se 1 (by rfl) ⟨790253, by rfl⟩ : syracuseStep 1053671 = 1580507) B1580507
theorem B6001721 : Blo 1052612 6001721 := bstep (se 2 (by rfl) ⟨2250645, by rfl⟩ : syracuseStep 6001721 = 4501291) B4501291
theorem B4559969 : Blo 1052612 4559969 := bstep (se 2 (by rfl) ⟨1709988, by rfl⟩ : syracuseStep 4559969 = 3419977) B3419977
theorem B1053983 : Blo 1052612 1053983 := bstep (se 1 (by rfl) ⟨790487, by rfl⟩ : syracuseStep 1053983 = 1580975) B1580975
theorem B2135335 : Blo 1052612 2135335 := bstep (se 1 (by rfl) ⟨1601501, by rfl⟩ : syracuseStep 2135335 = 3203003) B3203003
theorem B5346647 : Blo 1052612 5346647 := bstep (se 1 (by rfl) ⟨4009985, by rfl⟩ : syracuseStep 5346647 = 8019971) B8019971
theorem B1185115 : Blo 1052612 1185115 := bstep (se 1 (by rfl) ⟨888836, by rfl⟩ : syracuseStep 1185115 = 1777673) B1777673
theorem B1054043 : Blo 1052612 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B1054063 : Blo 1052612 1054063 := bstep (se 1 (by rfl) ⟨790547, by rfl⟩ : syracuseStep 1054063 = 1581095) B1581095
theorem B1054119 : Blo 1052612 1054119 := bstep (se 1 (by rfl) ⟨790589, by rfl⟩ : syracuseStep 1054119 = 1581179) B1581179
theorem B1185223 : Blo 1052612 1185223 := bstep (se 1 (by rfl) ⟨888917, by rfl⟩ : syracuseStep 1185223 = 1777835) B1777835
theorem B1054203 : Blo 1052612 1054203 := bstep (se 1 (by rfl) ⟨790652, by rfl⟩ : syracuseStep 1054203 = 1581305) B1581305
theorem B1054271 : Blo 1052612 1054271 := bstep (se 1 (by rfl) ⟨790703, by rfl⟩ : syracuseStep 1054271 = 1581407) B1581407
theorem B1054279 : Blo 1052612 1054279 := bstep (se 1 (by rfl) ⟨790709, by rfl⟩ : syracuseStep 1054279 = 1581419) B1581419
theorem B1054431 : Blo 1052612 1054431 := bstep (se 1 (by rfl) ⟨790823, by rfl⟩ : syracuseStep 1054431 = 1581647) B1581647
theorem B2004743 : Blo 1052612 2004743 := bstep (se 1 (by rfl) ⟨1503557, by rfl⟩ : syracuseStep 2004743 = 3007115) B3007115
theorem B1185583 : Blo 1052612 1185583 := bstep (se 1 (by rfl) ⟨889187, by rfl⟩ : syracuseStep 1185583 = 1778375) B1778375
theorem B1054511 : Blo 1052612 1054511 := bstep (se 1 (by rfl) ⟨790883, by rfl⟩ : syracuseStep 1054511 = 1581767) B1581767
theorem B7214935 : Blo 1052612 7214935 := bstep (se 1 (by rfl) ⟨5411201, by rfl⟩ : syracuseStep 7214935 = 10822403) B10822403
theorem B1185691 : Blo 1052612 1185691 := bstep (se 1 (by rfl) ⟨889268, by rfl⟩ : syracuseStep 1185691 = 1778537) B1778537
theorem B1054619 : Blo 1052612 1054619 := bstep (se 1 (by rfl) ⟨790964, by rfl⟩ : syracuseStep 1054619 = 1581929) B1581929
theorem B1578959 : Blo 1052612 1578959 := bstep (se 1 (by rfl) ⟨1184219, by rfl⟩ : syracuseStep 1578959 = 2368439) B2368439
theorem B1054671 : Blo 1052612 1054671 := bstep (se 1 (by rfl) ⟨791003, by rfl⟩ : syracuseStep 1054671 = 1582007) B1582007
theorem B1054695 : Blo 1052612 1054695 := bstep (se 1 (by rfl) ⟨791021, by rfl⟩ : syracuseStep 1054695 = 1582043) B1582043
theorem B30414851 : Blo 1052612 30414851 := bstep (se 1 (by rfl) ⟨22811138, by rfl⟩ : syracuseStep 30414851 = 45622277) B45622277
theorem B21665825 : Blo 1052612 21665825 := bstep (se 2 (by rfl) ⟨8124684, by rfl⟩ : syracuseStep 21665825 = 16249369) B16249369
theorem B5347457 : Blo 1052612 5347457 := bstep (se 2 (by rfl) ⟨2005296, by rfl⟩ : syracuseStep 5347457 = 4010593) B4010593
theorem B9115895 : Blo 1052612 9115895 := bstep (se 1 (by rfl) ⟨6836921, by rfl⟩ : syracuseStep 9115895 = 13673843) B13673843
theorem B4004093 : Blo 1052612 4004093 := bstep (se 3 (by rfl) ⟨750767, by rfl⟩ : syracuseStep 4004093 = 1501535) B1501535
theorem B1055007 : Blo 1052612 1055007 := bstep (se 1 (by rfl) ⟨791255, by rfl⟩ : syracuseStep 1055007 = 1582511) B1582511
theorem B1186087 : Blo 1052612 1186087 := bstep (se 1 (by rfl) ⟨889565, by rfl⟩ : syracuseStep 1186087 = 1779131) B1779131
theorem B1579355 : Blo 1052612 1579355 := bstep (se 1 (by rfl) ⟨1184516, by rfl⟩ : syracuseStep 1579355 = 2369033) B2369033
theorem B1055067 : Blo 1052612 1055067 := bstep (se 1 (by rfl) ⟨791300, by rfl⟩ : syracuseStep 1055067 = 1582601) B1582601
theorem B1186159 : Blo 1052612 1186159 := bstep (se 1 (by rfl) ⟨889619, by rfl⟩ : syracuseStep 1186159 = 1779239) B1779239
theorem B1055087 : Blo 1052612 1055087 := bstep (se 1 (by rfl) ⟨791315, by rfl⟩ : syracuseStep 1055087 = 1582631) B1582631
theorem B1055143 : Blo 1052612 1055143 := bstep (se 1 (by rfl) ⟨791357, by rfl⟩ : syracuseStep 1055143 = 1582715) B1582715
theorem B1055227 : Blo 1052612 1055227 := bstep (se 1 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 1055227 = 1582841) B1582841
theorem B1579583 : Blo 1052612 1579583 := bstep (se 1 (by rfl) ⟨1184687, by rfl⟩ : syracuseStep 1579583 = 2369375) B2369375
theorem B1055295 : Blo 1052612 1055295 := bstep (se 1 (by rfl) ⟨791471, by rfl⟩ : syracuseStep 1055295 = 1582943) B1582943
theorem B1186375 : Blo 1052612 1186375 := bstep (se 1 (by rfl) ⟨889781, by rfl⟩ : syracuseStep 1186375 = 1779563) B1779563
theorem B1055303 : Blo 1052612 1055303 := bstep (se 1 (by rfl) ⟨791477, by rfl⟩ : syracuseStep 1055303 = 1582955) B1582955
theorem B1579703 : Blo 1052612 1579703 := bstep (se 1 (by rfl) ⟨1184777, by rfl⟩ : syracuseStep 1579703 = 2369555) B2369555
theorem B1055455 : Blo 1052612 1055455 := bstep (se 1 (by rfl) ⟨791591, by rfl⟩ : syracuseStep 1055455 = 1583183) B1583183
theorem B1055535 : Blo 1052612 1055535 := bstep (se 1 (by rfl) ⟨791651, by rfl⟩ : syracuseStep 1055535 = 1583303) B1583303
theorem B1776539 : Blo 1052612 1776539 := bstep (se 1 (by rfl) ⟨1332404, by rfl⟩ : syracuseStep 1776539 = 2664809) B2664809
theorem B1579931 : Blo 1052612 1579931 := bstep (se 1 (by rfl) ⟨1184948, by rfl⟩ : syracuseStep 1579931 = 2369897) B2369897
theorem B1055643 : Blo 1052612 1055643 := bstep (se 1 (by rfl) ⟨791732, by rfl⟩ : syracuseStep 1055643 = 1583465) B1583465
theorem B5348267 : Blo 1052612 5348267 := bstep (se 1 (by rfl) ⟨4011200, by rfl⟩ : syracuseStep 5348267 = 8022401) B8022401
theorem B1055695 : Blo 1052612 1055695 := bstep (se 1 (by rfl) ⟨791771, by rfl⟩ : syracuseStep 1055695 = 1583543) B1583543
theorem B1055719 : Blo 1052612 1055719 := bstep (se 1 (by rfl) ⟨791789, by rfl⟩ : syracuseStep 1055719 = 1583579) B1583579
theorem B14621917 : Blo 1052612 14621917 := bstep (se 3 (by rfl) ⟨2741609, by rfl⟩ : syracuseStep 14621917 = 5483219) B5483219
theorem B1056031 : Blo 1052612 1056031 := bstep (se 1 (by rfl) ⟨792023, by rfl⟩ : syracuseStep 1056031 = 1584047) B1584047
theorem B1580327 : Blo 1052612 1580327 := bstep (se 1 (by rfl) ⟨1185245, by rfl⟩ : syracuseStep 1580327 = 2370491) B2370491
theorem B1056091 : Blo 1052612 1056091 := bstep (se 1 (by rfl) ⟨792068, by rfl⟩ : syracuseStep 1056091 = 1584137) B1584137
theorem B1056111 : Blo 1052612 1056111 := bstep (se 1 (by rfl) ⟨792083, by rfl⟩ : syracuseStep 1056111 = 1584167) B1584167
theorem B1580411 : Blo 1052612 1580411 := bstep (se 1 (by rfl) ⟨1185308, by rfl⟩ : syracuseStep 1580411 = 2370617) B2370617
theorem B1187239 : Blo 1052612 1187239 := bstep (se 1 (by rfl) ⟨890429, by rfl⟩ : syracuseStep 1187239 = 1780859) B1780859
theorem B1056167 : Blo 1052612 1056167 := bstep (se 1 (by rfl) ⟨792125, by rfl⟩ : syracuseStep 1056167 = 1584251) B1584251
theorem B1580537 : Blo 1052612 1580537 := bstep (se 2 (by rfl) ⟨592701, by rfl⟩ : syracuseStep 1580537 = 1185403) B1185403
theorem B1056251 : Blo 1052612 1056251 := bstep (se 1 (by rfl) ⟨792188, by rfl⟩ : syracuseStep 1056251 = 1584377) B1584377
theorem B1056319 : Blo 1052612 1056319 := bstep (se 1 (by rfl) ⟨792239, by rfl⟩ : syracuseStep 1056319 = 1584479) B1584479
theorem B1056327 : Blo 1052612 1056327 := bstep (se 1 (by rfl) ⟨792245, by rfl⟩ : syracuseStep 1056327 = 1584491) B1584491
theorem B1580639 : Blo 1052612 1580639 := bstep (se 1 (by rfl) ⟨1185479, by rfl⟩ : syracuseStep 1580639 = 2370959) B2370959
theorem B1056479 : Blo 1052612 1056479 := bstep (se 1 (by rfl) ⟨792359, by rfl⟩ : syracuseStep 1056479 = 1584719) B1584719
theorem B1056559 : Blo 1052612 1056559 := bstep (se 1 (by rfl) ⟨792419, by rfl⟩ : syracuseStep 1056559 = 1584839) B1584839
theorem B1580855 : Blo 1052612 1580855 := bstep (se 1 (by rfl) ⟨1185641, by rfl⟩ : syracuseStep 1580855 = 2371283) B2371283
theorem B17113025 : Blo 1052612 17113025 := bstep (se 2 (by rfl) ⟨6417384, by rfl⟩ : syracuseStep 17113025 = 12834769) B12834769
theorem B1187815 : Blo 1052612 1187815 := bstep (se 1 (by rfl) ⟨890861, by rfl⟩ : syracuseStep 1187815 = 1781723) B1781723
theorem B12329009 : Blo 1052612 12329009 := bstep (se 2 (by rfl) ⟨4623378, by rfl⟩ : syracuseStep 12329009 = 9246757) B9246757
theorem B1581161 : Blo 1052612 1581161 := bstep (se 2 (by rfl) ⟨592935, by rfl⟩ : syracuseStep 1581161 = 1185871) B1185871
theorem B1581479 : Blo 1052612 1581479 := bstep (se 1 (by rfl) ⟨1186109, by rfl⟩ : syracuseStep 1581479 = 2372219) B2372219
theorem B4497839 : Blo 1052612 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B1581563 : Blo 1052612 1581563 := bstep (se 1 (by rfl) ⟨1186172, by rfl⟩ : syracuseStep 1581563 = 2372345) B2372345
theorem B1581689 : Blo 1052612 1581689 := bstep (se 2 (by rfl) ⟨593133, by rfl⟩ : syracuseStep 1581689 = 1186267) B1186267
theorem B1581743 : Blo 1052612 1581743 := bstep (se 1 (by rfl) ⟨1186307, by rfl⟩ : syracuseStep 1581743 = 2372615) B2372615
theorem B1581791 : Blo 1052612 1581791 := bstep (se 1 (by rfl) ⟨1186343, by rfl⟩ : syracuseStep 1581791 = 2372687) B2372687
theorem B2368475 : Blo 1052612 2368475 := bstep (se 1 (by rfl) ⟨1776356, by rfl⟩ : syracuseStep 2368475 = 3552713) B3552713
theorem B1582055 : Blo 1052612 1582055 := bstep (se 1 (by rfl) ⟨1186541, by rfl⟩ : syracuseStep 1582055 = 2373083) B2373083
theorem B4007009 : Blo 1052612 4007009 := bstep (se 2 (by rfl) ⟨1502628, by rfl⟩ : syracuseStep 4007009 = 3005257) B3005257
theorem B2368655 : Blo 1052612 2368655 := bstep (se 1 (by rfl) ⟨1776491, by rfl⟩ : syracuseStep 2368655 = 3552983) B3552983
theorem B2368745 : Blo 1052612 2368745 := bstep (se 2 (by rfl) ⟨888279, by rfl⟩ : syracuseStep 2368745 = 1776559) B1776559
theorem B1582313 : Blo 1052612 1582313 := bstep (se 2 (by rfl) ⟨593367, by rfl⟩ : syracuseStep 1582313 = 1186735) B1186735
theorem B2368799 : Blo 1052612 2368799 := bstep (se 1 (by rfl) ⟨1776599, by rfl⟩ : syracuseStep 2368799 = 3553199) B3553199
theorem B1582367 : Blo 1052612 1582367 := bstep (se 1 (by rfl) ⟨1186775, by rfl⟩ : syracuseStep 1582367 = 2373551) B2373551
theorem B1582535 : Blo 1052612 1582535 := bstep (se 1 (by rfl) ⟨1186901, by rfl⟩ : syracuseStep 1582535 = 2373803) B2373803
theorem B2533025 : Blo 1052612 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B2369321 : Blo 1052612 2369321 := bstep (se 2 (by rfl) ⟨888495, by rfl⟩ : syracuseStep 2369321 = 1776991) B1776991
theorem B1582889 : Blo 1052612 1582889 := bstep (se 2 (by rfl) ⟨593583, by rfl⟩ : syracuseStep 1582889 = 1187167) B1187167
theorem B1582895 : Blo 1052612 1582895 := bstep (se 1 (by rfl) ⟨1187171, by rfl⟩ : syracuseStep 1582895 = 2374343) B2374343
theorem B2140265 : Blo 1052612 2140265 := bstep (se 2 (by rfl) ⟨802599, by rfl⟩ : syracuseStep 2140265 = 1605199) B1605199
theorem B4499651 : Blo 1052612 4499651 := bstep (se 1 (by rfl) ⟨3374738, by rfl⟩ : syracuseStep 4499651 = 6749477) B6749477
theorem B1583369 : Blo 1052612 1583369 := bstep (se 2 (by rfl) ⟨593763, by rfl⟩ : syracuseStep 1583369 = 1187527) B1187527
theorem B1124699 : Blo 1052612 1124699 := bstep (se 1 (by rfl) ⟨843524, by rfl⟩ : syracuseStep 1124699 = 1687049) B1687049
theorem B18491753 : Blo 1052612 18491753 := bstep (se 2 (by rfl) ⟨6934407, by rfl⟩ : syracuseStep 18491753 = 13868815) B13868815
theorem B1583471 : Blo 1052612 1583471 := bstep (se 1 (by rfl) ⟨1187603, by rfl⟩ : syracuseStep 1583471 = 2375207) B2375207
theorem B12003713 : Blo 1052612 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B1583687 : Blo 1052612 1583687 := bstep (se 1 (by rfl) ⟨1187765, by rfl⟩ : syracuseStep 1583687 = 2375531) B2375531
theorem B1583723 : Blo 1052612 1583723 := bstep (se 1 (by rfl) ⟨1187792, by rfl⟩ : syracuseStep 1583723 = 2375585) B2375585
theorem B2665183 : Blo 1052612 2665183 := bstep (se 1 (by rfl) ⟨1998887, by rfl⟩ : syracuseStep 2665183 = 3997775) B3997775
theorem B2534111 : Blo 1052612 2534111 := bstep (se 1 (by rfl) ⟨1900583, by rfl⟩ : syracuseStep 2534111 = 3801167) B3801167
theorem B1780447 : Blo 1052612 1780447 := bstep (se 1 (by rfl) ⟨1335335, by rfl⟩ : syracuseStep 1780447 = 2670671) B2670671
theorem B2665295 : Blo 1052612 2665295 := bstep (se 1 (by rfl) ⟨1998971, by rfl⟩ : syracuseStep 2665295 = 3997943) B3997943
theorem B2370383 : Blo 1052612 2370383 := bstep (se 1 (by rfl) ⟨1777787, by rfl⟩ : syracuseStep 2370383 = 3555575) B3555575
theorem B1583951 : Blo 1052612 1583951 := bstep (se 1 (by rfl) ⟨1187963, by rfl⟩ : syracuseStep 1583951 = 2375927) B2375927
theorem B2403227 : Blo 1052612 2403227 := bstep (se 1 (by rfl) ⟨1802420, by rfl⟩ : syracuseStep 2403227 = 3604841) B3604841
theorem B2370599 : Blo 1052612 2370599 := bstep (se 1 (by rfl) ⟨1777949, by rfl⟩ : syracuseStep 2370599 = 3555899) B3555899
theorem B9120883 : Blo 1052612 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B1780879 : Blo 1052612 1780879 := bstep (se 1 (by rfl) ⟨1335659, by rfl⟩ : syracuseStep 1780879 = 2671319) B2671319
theorem B2370779 : Blo 1052612 2370779 := bstep (se 1 (by rfl) ⟨1778084, by rfl⟩ : syracuseStep 2370779 = 3556169) B3556169
theorem B1584347 : Blo 1052612 1584347 := bstep (se 1 (by rfl) ⟨1188260, by rfl⟩ : syracuseStep 1584347 = 2376521) B2376521
theorem B1781129 : Blo 1052612 1781129 := bstep (se 2 (by rfl) ⟨667923, by rfl⟩ : syracuseStep 1781129 = 1335847) B1335847
theorem B1584521 : Blo 1052612 1584521 := bstep (se 2 (by rfl) ⟨594195, by rfl⟩ : syracuseStep 1584521 = 1188391) B1188391
theorem B2370977 : Blo 1052612 2370977 := bstep (se 2 (by rfl) ⟨889116, by rfl⟩ : syracuseStep 2370977 = 1778233) B1778233
theorem B2665943 : Blo 1052612 2665943 := bstep (se 1 (by rfl) ⟨1999457, by rfl⟩ : syracuseStep 2665943 = 3998915) B3998915
theorem B1584875 : Blo 1052612 1584875 := bstep (se 1 (by rfl) ⟨1188656, by rfl⟩ : syracuseStep 1584875 = 2377313) B2377313
theorem B2666297 : Blo 1052612 2666297 := bstep (se 2 (by rfl) ⟨999861, by rfl⟩ : syracuseStep 2666297 = 1999723) B1999723
theorem B1781561 : Blo 1052612 1781561 := bstep (se 2 (by rfl) ⟨668085, by rfl⟩ : syracuseStep 1781561 = 1336171) B1336171
theorem B4272029 : Blo 1052612 4272029 := bstep (se 3 (by rfl) ⟨801005, by rfl⟩ : syracuseStep 4272029 = 1602011) B1602011
theorem B2371535 : Blo 1052612 2371535 := bstep (se 1 (by rfl) ⟨1778651, by rfl⟩ : syracuseStep 2371535 = 3557303) B3557303
theorem B19247057 : Blo 1052612 19247057 := bstep (se 2 (by rfl) ⟨7217646, by rfl⟩ : syracuseStep 19247057 = 14435293) B14435293
theorem B32452811 : Blo 1052612 32452811 := bstep (se 1 (by rfl) ⟨24339608, by rfl⟩ : syracuseStep 32452811 = 48679217) B48679217
theorem B2371913 : Blo 1052612 2371913 := bstep (se 2 (by rfl) ⟨889467, by rfl⟩ : syracuseStep 2371913 = 1778935) B1778935
theorem B2371931 : Blo 1052612 2371931 := bstep (se 1 (by rfl) ⟨1778948, by rfl⟩ : syracuseStep 2371931 = 3557897) B3557897
theorem B1782607 : Blo 1052612 1782607 := bstep (se 1 (by rfl) ⟨1336955, by rfl⟩ : syracuseStep 1782607 = 2673911) B2673911
theorem B2372507 : Blo 1052612 2372507 := bstep (se 1 (by rfl) ⟨1779380, by rfl⟩ : syracuseStep 2372507 = 3558761) B3558761
theorem B8008793 : Blo 1052612 8008793 := bstep (se 2 (by rfl) ⟨3003297, by rfl⟩ : syracuseStep 8008793 = 6006595) B6006595
theorem B2372705 : Blo 1052612 2372705 := bstep (se 2 (by rfl) ⟨889764, by rfl⟩ : syracuseStep 2372705 = 1779529) B1779529
theorem B2536571 : Blo 1052612 2536571 := bstep (se 1 (by rfl) ⟨1902428, by rfl⟩ : syracuseStep 2536571 = 3804857) B3804857
theorem B6403229 : Blo 1052612 6403229 := bstep (se 3 (by rfl) ⟨1200605, by rfl⟩ : syracuseStep 6403229 = 2401211) B2401211
theorem B11416733 : Blo 1052612 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B2372903 : Blo 1052612 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B2667937 : Blo 1052612 2667937 := bstep (se 2 (by rfl) ⟨1000476, by rfl⟩ : syracuseStep 2667937 = 2000953) B2000953
theorem B9024929 : Blo 1052612 9024929 := bstep (se 2 (by rfl) ⟨3384348, by rfl⟩ : syracuseStep 9024929 = 6768697) B6768697
theorem B2373281 : Blo 1052612 2373281 := bstep (se 2 (by rfl) ⟨889980, by rfl⟩ : syracuseStep 2373281 = 1779961) B1779961
theorem B4273975 : Blo 1052612 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B2471887 : Blo 1052612 2471887 := bstep (se 1 (by rfl) ⟨1853915, by rfl⟩ : syracuseStep 2471887 = 3707831) B3707831
theorem B2373641 : Blo 1052612 2373641 := bstep (se 2 (by rfl) ⟨890115, by rfl⟩ : syracuseStep 2373641 = 1780231) B1780231
theorem B20297789 : Blo 1052612 20297789 := bstep (se 3 (by rfl) ⟨3805835, by rfl⟩ : syracuseStep 20297789 = 7611671) B7611671
theorem B3553415 : Blo 1052612 3553415 := bstep (se 1 (by rfl) ⟨2665061, by rfl⟩ : syracuseStep 3553415 = 5330123) B5330123
theorem B3291401 : Blo 1052612 3291401 := bstep (se 2 (by rfl) ⟨1234275, by rfl⟩ : syracuseStep 3291401 = 2468551) B2468551
theorem B2537801 : Blo 1052612 2537801 := bstep (se 2 (by rfl) ⟨951675, by rfl⟩ : syracuseStep 2537801 = 1903351) B1903351
theorem B2537839 : Blo 1052612 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B2374055 : Blo 1052612 2374055 := bstep (se 1 (by rfl) ⟨1780541, by rfl⟩ : syracuseStep 2374055 = 3561083) B3561083
theorem B2669051 : Blo 1052612 2669051 := bstep (se 1 (by rfl) ⟨2001788, by rfl⟩ : syracuseStep 2669051 = 4003577) B4003577
theorem B2374163 : Blo 1052612 2374163 := bstep (se 1 (by rfl) ⟨1780622, by rfl⟩ : syracuseStep 2374163 = 3561245) B3561245
theorem B9615935 : Blo 1052612 9615935 := bstep (se 1 (by rfl) ⟨7211951, by rfl⟩ : syracuseStep 9615935 = 14423903) B14423903
theorem B2374217 : Blo 1052612 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B2374631 : Blo 1052612 2374631 := bstep (se 1 (by rfl) ⟨1780973, by rfl⟩ : syracuseStep 2374631 = 3561947) B3561947
theorem B2538715 : Blo 1052612 2538715 := bstep (se 1 (by rfl) ⟨1904036, by rfl⟩ : syracuseStep 2538715 = 3808073) B3808073
theorem B3554657 : Blo 1052612 3554657 := bstep (se 2 (by rfl) ⟨1332996, by rfl⟩ : syracuseStep 3554657 = 2665993) B2665993
theorem B2375009 : Blo 1052612 2375009 := bstep (se 2 (by rfl) ⟨890628, by rfl⟩ : syracuseStep 2375009 = 1781257) B1781257
theorem B2375099 : Blo 1052612 2375099 := bstep (se 1 (by rfl) ⟨1781324, by rfl⟩ : syracuseStep 2375099 = 3562649) B3562649
theorem B2670023 : Blo 1052612 2670023 := bstep (se 1 (by rfl) ⟨2002517, by rfl⟩ : syracuseStep 2670023 = 4005035) B4005035
theorem B8011223 : Blo 1052612 8011223 := bstep (se 1 (by rfl) ⟨6008417, by rfl⟩ : syracuseStep 8011223 = 12016835) B12016835
theorem B2375225 : Blo 1052612 2375225 := bstep (se 2 (by rfl) ⟨890709, by rfl⟩ : syracuseStep 2375225 = 1781419) B1781419
theorem B6176351 : Blo 1052612 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B28884599 : Blo 1052612 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B11386889 : Blo 1052612 11386889 := bstep (se 2 (by rfl) ⟨4270083, by rfl⟩ : syracuseStep 11386889 = 8540167) B8540167
theorem B29278361 : Blo 1052612 29278361 := bstep (se 2 (by rfl) ⟨10979385, by rfl⟩ : syracuseStep 29278361 = 21958771) B21958771
theorem B2670803 : Blo 1052612 2670803 := bstep (se 1 (by rfl) ⟨2003102, by rfl⟩ : syracuseStep 2670803 = 4006205) B4006205
theorem B2375891 : Blo 1052612 2375891 := bstep (se 1 (by rfl) ⟨1781918, by rfl⟩ : syracuseStep 2375891 = 3563837) B3563837
theorem B2375945 : Blo 1052612 2375945 := bstep (se 2 (by rfl) ⟨890979, by rfl⟩ : syracuseStep 2375945 = 1781959) B1781959
theorem B8012195 : Blo 1052612 8012195 := bstep (se 1 (by rfl) ⟨6009146, by rfl⟩ : syracuseStep 8012195 = 12018293) B12018293
theorem B2671015 : Blo 1052612 2671015 := bstep (se 1 (by rfl) ⟨2003261, by rfl⟩ : syracuseStep 2671015 = 4006523) B4006523
theorem B6013385 : Blo 1052612 6013385 := bstep (se 2 (by rfl) ⟨2255019, by rfl⟩ : syracuseStep 6013385 = 4510039) B4510039
theorem B2376161 : Blo 1052612 2376161 := bstep (se 2 (by rfl) ⟨891060, by rfl⟩ : syracuseStep 2376161 = 1782121) B1782121
theorem B2671177 : Blo 1052612 2671177 := bstep (se 2 (by rfl) ⟨1001691, by rfl⟩ : syracuseStep 2671177 = 2003383) B2003383
theorem B12829319 : Blo 1052612 12829319 := bstep (se 1 (by rfl) ⟨9621989, by rfl⟩ : syracuseStep 12829319 = 19243979) B19243979
theorem B2376467 : Blo 1052612 2376467 := bstep (se 1 (by rfl) ⟨1782350, by rfl⟩ : syracuseStep 2376467 = 3564701) B3564701
theorem B5129153 : Blo 1052612 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B4506587 : Blo 1052612 4506587 := bstep (se 1 (by rfl) ⟨3379940, by rfl⟩ : syracuseStep 4506587 = 6759881) B6759881
theorem B2376827 : Blo 1052612 2376827 := bstep (se 1 (by rfl) ⟨1782620, by rfl⟩ : syracuseStep 2376827 = 3565241) B3565241
theorem B3556601 : Blo 1052612 3556601 := bstep (se 2 (by rfl) ⟨1333725, by rfl⟩ : syracuseStep 3556601 = 2667451) B2667451
theorem B2376953 : Blo 1052612 2376953 := bstep (se 2 (by rfl) ⟨891357, by rfl⟩ : syracuseStep 2376953 = 1782715) B1782715
theorem B2671967 : Blo 1052612 2671967 := bstep (se 1 (by rfl) ⟨2003975, by rfl⟩ : syracuseStep 2671967 = 4007951) B4007951
theorem B6767981 : Blo 1052612 6767981 := bstep (se 3 (by rfl) ⟨1268996, by rfl⟩ : syracuseStep 6767981 = 2537993) B2537993
theorem B2377097 : Blo 1052612 2377097 := bstep (se 2 (by rfl) ⟨891411, by rfl⟩ : syracuseStep 2377097 = 1782823) B1782823
theorem B3556871 : Blo 1052612 3556871 := bstep (se 1 (by rfl) ⟨2667653, by rfl⟩ : syracuseStep 3556871 = 5335307) B5335307
theorem B2377223 : Blo 1052612 2377223 := bstep (se 1 (by rfl) ⟨1782917, by rfl⟩ : syracuseStep 2377223 = 3565835) B3565835
theorem B4507271 : Blo 1052612 4507271 := bstep (se 1 (by rfl) ⟨3380453, by rfl⟩ : syracuseStep 4507271 = 6760907) B6760907
theorem B6015161 : Blo 1052612 6015161 := bstep (se 2 (by rfl) ⟨2255685, by rfl⟩ : syracuseStep 6015161 = 4511371) B4511371
theorem B4802807 : Blo 1052612 4802807 := bstep (se 1 (by rfl) ⟨3602105, by rfl⟩ : syracuseStep 4802807 = 7204211) B7204211
theorem B6015343 : Blo 1052612 6015343 := bstep (se 1 (by rfl) ⟨4511507, by rfl⟩ : syracuseStep 6015343 = 9023015) B9023015
theorem B6769007 : Blo 1052612 6769007 := bstep (se 1 (by rfl) ⟨5076755, by rfl⟩ : syracuseStep 6769007 = 10153511) B10153511
theorem B2673071 : Blo 1052612 2673071 := bstep (se 1 (by rfl) ⟨2004803, by rfl⟩ : syracuseStep 2673071 = 4009607) B4009607
theorem B3557843 : Blo 1052612 3557843 := bstep (se 1 (by rfl) ⟨2668382, by rfl⟩ : syracuseStep 3557843 = 5336765) B5336765
theorem B2673121 : Blo 1052612 2673121 := bstep (se 2 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 2673121 = 2004841) B2004841
theorem B3000827 : Blo 1052612 3000827 := bstep (se 1 (by rfl) ⟨2250620, by rfl⟩ : syracuseStep 3000827 = 4501241) B4501241
theorem B3557951 : Blo 1052612 3557951 := bstep (se 1 (by rfl) ⟨2668463, by rfl⟩ : syracuseStep 3557951 = 5336927) B5336927
theorem B8014625 : Blo 1052612 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B6015869 : Blo 1052612 6015869 := bstep (se 3 (by rfl) ⟨1127975, by rfl⟩ : syracuseStep 6015869 = 2255951) B2255951
theorem B6933383 : Blo 1052612 6933383 := bstep (se 1 (by rfl) ⟨5200037, by rfl⟩ : syracuseStep 6933383 = 10400075) B10400075
theorem B4509047 : Blo 1052612 4509047 := bstep (se 1 (by rfl) ⟨3381785, by rfl⟩ : syracuseStep 4509047 = 6763571) B6763571
theorem B2674043 : Blo 1052612 2674043 := bstep (se 1 (by rfl) ⟨2005532, by rfl⟩ : syracuseStep 2674043 = 4011065) B4011065
theorem B3002159 : Blo 1052612 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B4509715 : Blo 1052612 4509715 := bstep (se 1 (by rfl) ⟨3382286, by rfl⟩ : syracuseStep 4509715 = 6764573) B6764573
theorem B3559787 : Blo 1052612 3559787 := bstep (se 1 (by rfl) ⟨2669840, by rfl⟩ : syracuseStep 3559787 = 5339681) B5339681
theorem B6410771 : Blo 1052612 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B2249279 : Blo 1052612 2249279 := bstep (se 1 (by rfl) ⟨1686959, by rfl⟩ : syracuseStep 2249279 = 3373919) B3373919
theorem B3560057 : Blo 1052612 3560057 := bstep (se 2 (by rfl) ⟨1335021, by rfl⟩ : syracuseStep 3560057 = 2670043) B2670043
theorem B3003743 : Blo 1052612 3003743 := bstep (se 1 (by rfl) ⟨2252807, by rfl⟩ : syracuseStep 3003743 = 4505615) B4505615
theorem B5330285 : Blo 1052612 5330285 := bstep (se 3 (by rfl) ⟨999428, by rfl⟩ : syracuseStep 5330285 = 1998857) B1998857
theorem B9000395 : Blo 1052612 9000395 := bstep (se 1 (by rfl) ⟨6750296, by rfl⟩ : syracuseStep 9000395 = 13500593) B13500593
theorem B20305475 : Blo 1052612 20305475 := bstep (se 1 (by rfl) ⟨15229106, by rfl⟩ : syracuseStep 20305475 = 30458213) B30458213
theorem B1267435 : Blo 1052612 1267435 := bstep (se 1 (by rfl) ⟨950576, by rfl⟩ : syracuseStep 1267435 = 1901153) B1901153
theorem B1333199 : Blo 1052612 1333199 := bstep (se 1 (by rfl) ⟨999899, by rfl⟩ : syracuseStep 1333199 = 1999799) B1999799
theorem B3561839 : Blo 1052612 3561839 := bstep (se 1 (by rfl) ⟨2671379, by rfl⟩ : syracuseStep 3561839 = 5342759) B5342759
theorem B5069375 : Blo 1052612 5069375 := bstep (se 1 (by rfl) ⟨3802031, by rfl⟩ : syracuseStep 5069375 = 7604063) B7604063
theorem B5691977 : Blo 1052612 5691977 := bstep (se 2 (by rfl) ⟨2134491, by rfl⟩ : syracuseStep 5691977 = 4268983) B4268983
theorem B5069587 : Blo 1052612 5069587 := bstep (se 1 (by rfl) ⟨3802190, by rfl⟩ : syracuseStep 5069587 = 7604381) B7604381
theorem B1203023 : Blo 1052612 1203023 := bstep (se 1 (by rfl) ⟨902267, by rfl⟩ : syracuseStep 1203023 = 1804535) B1804535
theorem B1334171 : Blo 1052612 1334171 := bstep (se 1 (by rfl) ⟨1000628, by rfl⟩ : syracuseStep 1334171 = 2001257) B2001257
theorem B2251739 : Blo 1052612 2251739 := bstep (se 1 (by rfl) ⟨1688804, by rfl⟩ : syracuseStep 2251739 = 3377609) B3377609
theorem B13491467 : Blo 1052612 13491467 := bstep (se 1 (by rfl) ⟨10118600, by rfl⟩ : syracuseStep 13491467 = 20237201) B20237201
theorem B9756305 : Blo 1052612 9756305 := bstep (se 2 (by rfl) ⟨3658614, by rfl⟩ : syracuseStep 9756305 = 7317229) B7317229
theorem B5332715 : Blo 1052612 5332715 := bstep (se 1 (by rfl) ⟨3999536, by rfl⟩ : syracuseStep 5332715 = 7999073) B7999073
theorem B3563243 : Blo 1052612 3563243 := bstep (se 1 (by rfl) ⟨2672432, by rfl⟩ : syracuseStep 3563243 = 5344865) B5344865
theorem B1498927 : Blo 1052612 1498927 := bstep (se 1 (by rfl) ⟨1124195, by rfl⟩ : syracuseStep 1498927 = 2248391) B2248391
theorem B7593857 : Blo 1052612 7593857 := bstep (se 2 (by rfl) ⟨2847696, by rfl⟩ : syracuseStep 7593857 = 5695393) B5695393
theorem B9003059 : Blo 1052612 9003059 := bstep (se 1 (by rfl) ⟨6752294, by rfl⟩ : syracuseStep 9003059 = 13504589) B13504589
theorem B36528245 : Blo 1052612 36528245 := bstep (se 5 (by rfl) ⟨1712261, by rfl⟩ : syracuseStep 36528245 = 3424523) B3424523
theorem B5333201 : Blo 1052612 5333201 := bstep (se 2 (by rfl) ⟨1999950, by rfl⟩ : syracuseStep 5333201 = 3999901) B3999901
theorem B5333687 : Blo 1052612 5333687 := bstep (se 1 (by rfl) ⟨4000265, by rfl⟩ : syracuseStep 5333687 = 8000531) B8000531
theorem B3564215 : Blo 1052612 3564215 := bstep (se 1 (by rfl) ⟨2673161, by rfl⟩ : syracuseStep 3564215 = 5346323) B5346323
theorem B2745107 : Blo 1052612 2745107 := bstep (se 1 (by rfl) ⟨2058830, by rfl⟩ : syracuseStep 2745107 = 4117661) B4117661
theorem B5071835 : Blo 1052612 5071835 := bstep (se 1 (by rfl) ⟨3803876, by rfl⟩ : syracuseStep 5071835 = 7607753) B7607753
theorem B5334173 : Blo 1052612 5334173 := bstep (se 3 (by rfl) ⟨1000157, by rfl⟩ : syracuseStep 5334173 = 2000315) B2000315
theorem B4056263 : Blo 1052612 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B7693555 : Blo 1052612 7693555 := bstep (se 1 (by rfl) ⟨5770166, by rfl⟩ : syracuseStep 7693555 = 11540333) B11540333
theorem B23389505 : Blo 1052612 23389505 := bstep (se 2 (by rfl) ⟨8771064, by rfl⟩ : syracuseStep 23389505 = 17542129) B17542129
theorem B13723337 : Blo 1052612 13723337 := bstep (se 2 (by rfl) ⟨5146251, by rfl⟩ : syracuseStep 13723337 = 10292503) B10292503
theorem B1337143 : Blo 1052612 1337143 := bstep (se 1 (by rfl) ⟨1002857, by rfl⟩ : syracuseStep 1337143 = 2005715) B2005715
theorem B14477201 : Blo 1052612 14477201 := bstep (se 2 (by rfl) ⟨5428950, by rfl⟩ : syracuseStep 14477201 = 10857901) B10857901
theorem B3008765 : Blo 1052612 3008765 := bstep (se 3 (by rfl) ⟨564143, by rfl⟩ : syracuseStep 3008765 = 1128287) B1128287
theorem B15231361 : Blo 1052612 15231361 := bstep (se 2 (by rfl) ⟨5711760, by rfl⟩ : syracuseStep 15231361 = 11423521) B11423521
theorem B5335469 : Blo 1052612 5335469 := bstep (se 3 (by rfl) ⟨1000400, by rfl⟩ : syracuseStep 5335469 = 2000801) B2000801
theorem B5335631 : Blo 1052612 5335631 := bstep (se 1 (by rfl) ⟨4001723, by rfl⟩ : syracuseStep 5335631 = 8003447) B8003447
theorem B3796321 : Blo 1052612 3796321 := bstep (se 2 (by rfl) ⟨1423620, by rfl⟩ : syracuseStep 3796321 = 2847241) B2847241
theorem B9268667 : Blo 1052612 9268667 := bstep (se 1 (by rfl) ⟨6951500, by rfl⟩ : syracuseStep 9268667 = 13903001) B13903001
theorem B9629293 : Blo 1052612 9629293 := bstep (se 3 (by rfl) ⟨1805492, by rfl⟩ : syracuseStep 9629293 = 3610985) B3610985
theorem B5337089 : Blo 1052612 5337089 := bstep (se 2 (by rfl) ⟨2001408, by rfl⟩ : syracuseStep 5337089 = 4002817) B4002817
theorem B5697641 : Blo 1052612 5697641 := bstep (se 2 (by rfl) ⟨2136615, by rfl⟩ : syracuseStep 5697641 = 4273231) B4273231
theorem B22835357 : Blo 1052612 22835357 := bstep (se 3 (by rfl) ⟨4281629, by rfl⟩ : syracuseStep 22835357 = 8563259) B8563259
theorem B9007433 : Blo 1052612 9007433 := bstep (se 2 (by rfl) ⟨3377787, by rfl⟩ : syracuseStep 9007433 = 6755575) B6755575
theorem B4879001 : Blo 1052612 4879001 := bstep (se 2 (by rfl) ⟨1829625, by rfl⟩ : syracuseStep 4879001 = 3659251) B3659251
theorem B5337899 : Blo 1052612 5337899 := bstep (se 1 (by rfl) ⟨4003424, by rfl⟩ : syracuseStep 5337899 = 8006849) B8006849
theorem B15201427 : Blo 1052612 15201427 := bstep (se 1 (by rfl) ⟨11401070, by rfl⟩ : syracuseStep 15201427 = 22802141) B22802141
theorem B13497617 : Blo 1052612 13497617 := bstep (se 2 (by rfl) ⟨5061606, by rfl⟩ : syracuseStep 13497617 = 10123213) B10123213
theorem B12843143 : Blo 1052612 12843143 := bstep (se 1 (by rfl) ⟨9632357, by rfl⟩ : syracuseStep 12843143 = 19264715) B19264715
theorem B5339843 : Blo 1052612 5339843 := bstep (se 1 (by rfl) ⟨4004882, by rfl⟩ : syracuseStep 5339843 = 8009765) B8009765
theorem B13499621 : Blo 1052612 13499621 := bstep (se 4 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 13499621 = 2531179) B2531179
theorem B5701229 : Blo 1052612 5701229 := bstep (se 3 (by rfl) ⟨1068980, by rfl⟩ : syracuseStep 5701229 = 2137961) B2137961
theorem B20512379 : Blo 1052612 20512379 := bstep (se 1 (by rfl) ⟨15384284, by rfl⟩ : syracuseStep 20512379 = 30768569) B30768569
theorem B1998523 : Blo 1052612 1998523 := bstep (se 1 (by rfl) ⟨1498892, by rfl⟩ : syracuseStep 1998523 = 2997785) B2997785
theorem B7995671 : Blo 1052612 7995671 := bstep (se 1 (by rfl) ⟨5996753, by rfl⟩ : syracuseStep 7995671 = 11993507) B11993507
theorem B5341463 : Blo 1052612 5341463 := bstep (se 1 (by rfl) ⟨4006097, by rfl⟩ : syracuseStep 5341463 = 8012195) B8012195
theorem B8552879 : Blo 1052612 8552879 := bstep (se 1 (by rfl) ⟨6414659, by rfl⟩ : syracuseStep 8552879 = 12829319) B12829319
theorem B5702183 : Blo 1052612 5702183 := bstep (se 1 (by rfl) ⟨4276637, by rfl⟩ : syracuseStep 5702183 = 8553275) B8553275
theorem B6423079 : Blo 1052612 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B3998443 : Blo 1052612 3998443 := bstep (se 1 (by rfl) ⟨2998832, by rfl⟩ : syracuseStep 3998443 = 5997665) B5997665
theorem B6095735 : Blo 1052612 6095735 := bstep (se 1 (by rfl) ⟨4571801, by rfl⟩ : syracuseStep 6095735 = 9143603) B9143603
theorem B2032595 : Blo 1052612 2032595 := bstep (se 1 (by rfl) ⟨1524446, by rfl⟩ : syracuseStep 2032595 = 3048893) B3048893
theorem B10258073 : Blo 1052612 10258073 := bstep (se 2 (by rfl) ⟨3846777, by rfl⟩ : syracuseStep 10258073 = 7693555) B7693555
theorem B2000551 : Blo 1052612 2000551 := bstep (se 1 (by rfl) ⟨1500413, by rfl⟩ : syracuseStep 2000551 = 3000827) B3000827
theorem B5343083 : Blo 1052612 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B4622255 : Blo 1052612 4622255 := bstep (se 1 (by rfl) ⟨3466691, by rfl⟩ : syracuseStep 4622255 = 6933383) B6933383
theorem B2001439 : Blo 1052612 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B4001147 : Blo 1052612 4001147 := bstep (se 1 (by rfl) ⟨3000860, by rfl⟩ : syracuseStep 4001147 = 6001721) B6001721
theorem B2002495 : Blo 1052612 2002495 := bstep (se 1 (by rfl) ⟨1501871, by rfl⟩ : syracuseStep 2002495 = 3003743) B3003743
theorem B6000263 : Blo 1052612 6000263 := bstep (se 1 (by rfl) ⟨4500197, by rfl⟩ : syracuseStep 6000263 = 9000395) B9000395
theorem B13536983 : Blo 1052612 13536983 := bstep (se 1 (by rfl) ⟨10152737, by rfl⟩ : syracuseStep 13536983 = 20305475) B20305475
theorem B1052639 : Blo 1052612 1052639 := bstep (se 1 (by rfl) ⟨789479, by rfl⟩ : syracuseStep 1052639 = 1578959) B1578959
theorem B12161177 : Blo 1052612 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B1052903 : Blo 1052612 1052903 := bstep (se 1 (by rfl) ⟨789677, by rfl⟩ : syracuseStep 1052903 = 1579355) B1579355
theorem B1053055 : Blo 1052612 1053055 := bstep (se 1 (by rfl) ⟨789791, by rfl⟩ : syracuseStep 1053055 = 1579583) B1579583
theorem B3379583 : Blo 1052612 3379583 := bstep (se 1 (by rfl) ⟨2534687, by rfl⟩ : syracuseStep 3379583 = 5069375) B5069375
theorem B1053135 : Blo 1052612 1053135 := bstep (se 1 (by rfl) ⟨789851, by rfl⟩ : syracuseStep 1053135 = 1579703) B1579703
theorem B1184359 : Blo 1052612 1184359 := bstep (se 1 (by rfl) ⟨888269, by rfl⟩ : syracuseStep 1184359 = 1776539) B1776539
theorem B1053287 : Blo 1052612 1053287 := bstep (se 1 (by rfl) ⟨789965, by rfl⟩ : syracuseStep 1053287 = 1579931) B1579931
theorem B7213865 : Blo 1052612 7213865 := bstep (se 2 (by rfl) ⟨2705199, by rfl⟩ : syracuseStep 7213865 = 5410399) B5410399
theorem B1053551 : Blo 1052612 1053551 := bstep (se 1 (by rfl) ⟨790163, by rfl⟩ : syracuseStep 1053551 = 1580327) B1580327
theorem B1053607 : Blo 1052612 1053607 := bstep (se 1 (by rfl) ⟨790205, by rfl⟩ : syracuseStep 1053607 = 1580411) B1580411
theorem B1053691 : Blo 1052612 1053691 := bstep (se 1 (by rfl) ⟨790268, by rfl⟩ : syracuseStep 1053691 = 1580537) B1580537
theorem B1053759 : Blo 1052612 1053759 := bstep (se 1 (by rfl) ⟨790319, by rfl⟩ : syracuseStep 1053759 = 1580639) B1580639
theorem B1053903 : Blo 1052612 1053903 := bstep (se 1 (by rfl) ⟨790427, by rfl⟩ : syracuseStep 1053903 = 1580855) B1580855
theorem B11408683 : Blo 1052612 11408683 := bstep (se 1 (by rfl) ⟨8556512, by rfl⟩ : syracuseStep 11408683 = 17113025) B17113025
theorem B6002039 : Blo 1052612 6002039 := bstep (se 1 (by rfl) ⟨4501529, by rfl⟩ : syracuseStep 6002039 = 9003059) B9003059
theorem B1054107 : Blo 1052612 1054107 := bstep (se 1 (by rfl) ⟨790580, by rfl⟩ : syracuseStep 1054107 = 1581161) B1581161
theorem B24352163 : Blo 1052612 24352163 := bstep (se 1 (by rfl) ⟨18264122, by rfl⟩ : syracuseStep 24352163 = 36528245) B36528245
theorem B1054319 : Blo 1052612 1054319 := bstep (se 1 (by rfl) ⟨790739, by rfl⟩ : syracuseStep 1054319 = 1581479) B1581479
theorem B1054375 : Blo 1052612 1054375 := bstep (se 1 (by rfl) ⟨790781, by rfl⟩ : syracuseStep 1054375 = 1581563) B1581563
theorem B7607981 : Blo 1052612 7607981 := bstep (se 3 (by rfl) ⟨1426496, by rfl⟩ : syracuseStep 7607981 = 2852993) B2852993
theorem B1054459 : Blo 1052612 1054459 := bstep (se 1 (by rfl) ⟨790844, by rfl⟩ : syracuseStep 1054459 = 1581689) B1581689
theorem B1054495 : Blo 1052612 1054495 := bstep (se 1 (by rfl) ⟨790871, by rfl⟩ : syracuseStep 1054495 = 1581743) B1581743
theorem B1054527 : Blo 1052612 1054527 := bstep (se 1 (by rfl) ⟨790895, by rfl⟩ : syracuseStep 1054527 = 1581791) B1581791
theorem B7706501 : Blo 1052612 7706501 := bstep (se 4 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 7706501 = 1444969) B1444969
theorem B1578983 : Blo 1052612 1578983 := bstep (se 1 (by rfl) ⟨1184237, by rfl⟩ : syracuseStep 1578983 = 2368475) B2368475
theorem B3381223 : Blo 1052612 3381223 := bstep (se 1 (by rfl) ⟨2535917, by rfl⟩ : syracuseStep 3381223 = 5071835) B5071835
theorem B1054703 : Blo 1052612 1054703 := bstep (se 1 (by rfl) ⟨791027, by rfl⟩ : syracuseStep 1054703 = 1582055) B1582055
theorem B1579001 : Blo 1052612 1579001 := bstep (se 2 (by rfl) ⟨592125, by rfl⟩ : syracuseStep 1579001 = 1184251) B1184251
theorem B1579103 : Blo 1052612 1579103 := bstep (se 1 (by rfl) ⟨1184327, by rfl⟩ : syracuseStep 1579103 = 2368655) B2368655
theorem B1579163 : Blo 1052612 1579163 := bstep (se 1 (by rfl) ⟨1184372, by rfl⟩ : syracuseStep 1579163 = 2368745) B2368745
theorem B1054875 : Blo 1052612 1054875 := bstep (se 1 (by rfl) ⟨791156, by rfl⟩ : syracuseStep 1054875 = 1582313) B1582313
theorem B1579199 : Blo 1052612 1579199 := bstep (se 1 (by rfl) ⟨1184399, by rfl⟩ : syracuseStep 1579199 = 2368799) B2368799
theorem B1054911 : Blo 1052612 1054911 := bstep (se 1 (by rfl) ⟨791183, by rfl⟩ : syracuseStep 1054911 = 1582367) B1582367
theorem B1579241 : Blo 1052612 1579241 := bstep (se 2 (by rfl) ⟨592215, by rfl⟩ : syracuseStep 1579241 = 1184431) B1184431
theorem B1055023 : Blo 1052612 1055023 := bstep (se 1 (by rfl) ⟨791267, by rfl⟩ : syracuseStep 1055023 = 1582535) B1582535
theorem B9148891 : Blo 1052612 9148891 := bstep (se 1 (by rfl) ⟨6861668, by rfl⟩ : syracuseStep 9148891 = 13723337) B13723337
theorem B1579547 : Blo 1052612 1579547 := bstep (se 1 (by rfl) ⟨1184660, by rfl⟩ : syracuseStep 1579547 = 2369321) B2369321
theorem B1055259 : Blo 1052612 1055259 := bstep (se 1 (by rfl) ⟨791444, by rfl⟩ : syracuseStep 1055259 = 1582889) B1582889
theorem B1055263 : Blo 1052612 1055263 := bstep (se 1 (by rfl) ⟨791447, by rfl⟩ : syracuseStep 1055263 = 1582895) B1582895
theorem B1579625 : Blo 1052612 1579625 := bstep (se 2 (by rfl) ⟨592359, by rfl⟩ : syracuseStep 1579625 = 1184719) B1184719
theorem B1055579 : Blo 1052612 1055579 := bstep (se 1 (by rfl) ⟨791684, by rfl⟩ : syracuseStep 1055579 = 1583369) B1583369
theorem B12327835 : Blo 1052612 12327835 := bstep (se 1 (by rfl) ⟨9245876, by rfl⟩ : syracuseStep 12327835 = 18491753) B18491753
theorem B1055647 : Blo 1052612 1055647 := bstep (se 1 (by rfl) ⟨791735, by rfl⟩ : syracuseStep 1055647 = 1583471) B1583471
theorem B8002475 : Blo 1052612 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B1055791 : Blo 1052612 1055791 := bstep (se 1 (by rfl) ⟨791843, by rfl⟩ : syracuseStep 1055791 = 1583687) B1583687
theorem B1055815 : Blo 1052612 1055815 := bstep (se 1 (by rfl) ⟨791861, by rfl⟩ : syracuseStep 1055815 = 1583723) B1583723
theorem B1580153 : Blo 1052612 1580153 := bstep (se 2 (by rfl) ⟨592557, by rfl⟩ : syracuseStep 1580153 = 1185115) B1185115
theorem B1776863 : Blo 1052612 1776863 := bstep (se 1 (by rfl) ⟨1332647, by rfl⟩ : syracuseStep 1776863 = 2665295) B2665295
theorem B1580255 : Blo 1052612 1580255 := bstep (se 1 (by rfl) ⟨1185191, by rfl⟩ : syracuseStep 1580255 = 2370383) B2370383
theorem B1055967 : Blo 1052612 1055967 := bstep (se 1 (by rfl) ⟨791975, by rfl⟩ : syracuseStep 1055967 = 1583951) B1583951
theorem B1580297 : Blo 1052612 1580297 := bstep (se 2 (by rfl) ⟨592611, by rfl⟩ : syracuseStep 1580297 = 1185223) B1185223
theorem B1580399 : Blo 1052612 1580399 := bstep (se 1 (by rfl) ⟨1185299, by rfl⟩ : syracuseStep 1580399 = 2370599) B2370599
theorem B1580519 : Blo 1052612 1580519 := bstep (se 1 (by rfl) ⟨1185389, by rfl⟩ : syracuseStep 1580519 = 2370779) B2370779
theorem B1056231 : Blo 1052612 1056231 := bstep (se 1 (by rfl) ⟨792173, by rfl⟩ : syracuseStep 1056231 = 1584347) B1584347
theorem B1187419 : Blo 1052612 1187419 := bstep (se 1 (by rfl) ⟨890564, by rfl⟩ : syracuseStep 1187419 = 1781129) B1781129
theorem B1056347 : Blo 1052612 1056347 := bstep (se 1 (by rfl) ⟨792260, by rfl⟩ : syracuseStep 1056347 = 1584521) B1584521
theorem B1580651 : Blo 1052612 1580651 := bstep (se 1 (by rfl) ⟨1185488, by rfl⟩ : syracuseStep 1580651 = 2370977) B2370977
theorem B1777295 : Blo 1052612 1777295 := bstep (se 1 (by rfl) ⟨1332971, by rfl⟩ : syracuseStep 1777295 = 2665943) B2665943
theorem B1580777 : Blo 1052612 1580777 := bstep (se 2 (by rfl) ⟨592791, by rfl⟩ : syracuseStep 1580777 = 1185583) B1185583
theorem B1056583 : Blo 1052612 1056583 := bstep (se 1 (by rfl) ⟨792437, by rfl⟩ : syracuseStep 1056583 = 1584875) B1584875
theorem B1580921 : Blo 1052612 1580921 := bstep (se 2 (by rfl) ⟨592845, by rfl⟩ : syracuseStep 1580921 = 1185691) B1185691
theorem B1777531 : Blo 1052612 1777531 := bstep (se 1 (by rfl) ⟨1333148, by rfl⟩ : syracuseStep 1777531 = 2666297) B2666297
theorem B1187707 : Blo 1052612 1187707 := bstep (se 1 (by rfl) ⟨890780, by rfl⟩ : syracuseStep 1187707 = 1781561) B1781561
theorem B6004637 : Blo 1052612 6004637 := bstep (se 3 (by rfl) ⟨1125869, by rfl⟩ : syracuseStep 6004637 = 2251739) B2251739
theorem B1581023 : Blo 1052612 1581023 := bstep (se 1 (by rfl) ⟨1185767, by rfl⟩ : syracuseStep 1581023 = 2371535) B2371535
theorem B21635207 : Blo 1052612 21635207 := bstep (se 1 (by rfl) ⟨16226405, by rfl⟩ : syracuseStep 21635207 = 32452811) B32452811
theorem B1581275 : Blo 1052612 1581275 := bstep (se 1 (by rfl) ⟨1185956, by rfl⟩ : syracuseStep 1581275 = 2371913) B2371913
theorem B6004955 : Blo 1052612 6004955 := bstep (se 1 (by rfl) ⟨4503716, by rfl⟩ : syracuseStep 6004955 = 9007433) B9007433
theorem B1581287 : Blo 1052612 1581287 := bstep (se 1 (by rfl) ⟨1185965, by rfl⟩ : syracuseStep 1581287 = 2371931) B2371931
theorem B1581449 : Blo 1052612 1581449 := bstep (se 2 (by rfl) ⟨593043, by rfl⟩ : syracuseStep 1581449 = 1186087) B1186087
theorem B3252667 : Blo 1052612 3252667 := bstep (se 1 (by rfl) ⟨2439500, by rfl⟩ : syracuseStep 3252667 = 4879001) B4879001
theorem B1581545 : Blo 1052612 1581545 := bstep (se 2 (by rfl) ⟨593079, by rfl⟩ : syracuseStep 1581545 = 1186159) B1186159
theorem B3383785 : Blo 1052612 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B1581671 : Blo 1052612 1581671 := bstep (se 1 (by rfl) ⟨1186253, by rfl⟩ : syracuseStep 1581671 = 2372507) B2372507
theorem B1581803 : Blo 1052612 1581803 := bstep (se 1 (by rfl) ⟨1186352, by rfl⟩ : syracuseStep 1581803 = 2372705) B2372705
theorem B1581833 : Blo 1052612 1581833 := bstep (se 2 (by rfl) ⟨593187, by rfl⟩ : syracuseStep 1581833 = 1186375) B1186375
theorem B4268819 : Blo 1052612 4268819 := bstep (se 1 (by rfl) ⟨3201614, by rfl⟩ : syracuseStep 4268819 = 6403229) B6403229
theorem B7611155 : Blo 1052612 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B1581935 : Blo 1052612 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B6759449 : Blo 1052612 6759449 := bstep (se 2 (by rfl) ⟨2534793, by rfl⟩ : syracuseStep 6759449 = 5069587) B5069587
theorem B1582187 : Blo 1052612 1582187 := bstep (se 1 (by rfl) ⟨1186640, by rfl⟩ : syracuseStep 1582187 = 2373281) B2373281
theorem B1582427 : Blo 1052612 1582427 := bstep (se 1 (by rfl) ⟨1186820, by rfl⟩ : syracuseStep 1582427 = 2373641) B2373641
theorem B2368943 : Blo 1052612 2368943 := bstep (se 1 (by rfl) ⟨1776707, by rfl⟩ : syracuseStep 2368943 = 3553415) B3553415
theorem B8562095 : Blo 1052612 8562095 := bstep (se 1 (by rfl) ⟨6421571, by rfl⟩ : syracuseStep 8562095 = 12843143) B12843143
theorem B1582703 : Blo 1052612 1582703 := bstep (se 1 (by rfl) ⟨1187027, by rfl⟩ : syracuseStep 1582703 = 2374055) B2374055
theorem B3384953 : Blo 1052612 3384953 := bstep (se 2 (by rfl) ⟨1269357, by rfl⟩ : syracuseStep 3384953 = 2538715) B2538715
theorem B1779367 : Blo 1052612 1779367 := bstep (se 1 (by rfl) ⟨1334525, by rfl⟩ : syracuseStep 1779367 = 2669051) B2669051
theorem B1582775 : Blo 1052612 1582775 := bstep (se 1 (by rfl) ⟨1187081, by rfl⟩ : syracuseStep 1582775 = 2374163) B2374163
theorem B1582811 : Blo 1052612 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B1582985 : Blo 1052612 1582985 := bstep (se 2 (by rfl) ⟨593619, by rfl⟩ : syracuseStep 1582985 = 1187239) B1187239
theorem B1583087 : Blo 1052612 1583087 := bstep (se 1 (by rfl) ⟨1187315, by rfl⟩ : syracuseStep 1583087 = 2374631) B2374631
theorem B2369771 : Blo 1052612 2369771 := bstep (se 1 (by rfl) ⟨1777328, by rfl⟩ : syracuseStep 2369771 = 3554657) B3554657
theorem B1583339 : Blo 1052612 1583339 := bstep (se 1 (by rfl) ⟨1187504, by rfl⟩ : syracuseStep 1583339 = 2375009) B2375009
theorem B2664697 : Blo 1052612 2664697 := bstep (se 2 (by rfl) ⟨999261, by rfl⟩ : syracuseStep 2664697 = 1998523) B1998523
theorem B1583399 : Blo 1052612 1583399 := bstep (se 1 (by rfl) ⟨1187549, by rfl⟩ : syracuseStep 1583399 = 2375099) B2375099
theorem B1780015 : Blo 1052612 1780015 := bstep (se 1 (by rfl) ⟨1335011, by rfl⟩ : syracuseStep 1780015 = 2670023) B2670023
theorem B1583483 : Blo 1052612 1583483 := bstep (se 1 (by rfl) ⟨1187612, by rfl⟩ : syracuseStep 1583483 = 2375225) B2375225
theorem B13183397 : Blo 1052612 13183397 := bstep (se 4 (by rfl) ⟨1235943, by rfl⟩ : syracuseStep 13183397 = 2471887) B2471887
theorem B13674919 : Blo 1052612 13674919 := bstep (se 1 (by rfl) ⟨10256189, by rfl⟩ : syracuseStep 13674919 = 20512379) B20512379
theorem B1583753 : Blo 1052612 1583753 := bstep (se 2 (by rfl) ⟨593907, by rfl⟩ : syracuseStep 1583753 = 1187815) B1187815
theorem B1780535 : Blo 1052612 1780535 := bstep (se 1 (by rfl) ⟨1335401, by rfl⟩ : syracuseStep 1780535 = 2670803) B2670803
theorem B1583927 : Blo 1052612 1583927 := bstep (se 1 (by rfl) ⟨1187945, by rfl⟩ : syracuseStep 1583927 = 2375891) B2375891
theorem B1583963 : Blo 1052612 1583963 := bstep (se 1 (by rfl) ⟨1187972, by rfl⟩ : syracuseStep 1583963 = 2375945) B2375945
theorem B4008923 : Blo 1052612 4008923 := bstep (se 1 (by rfl) ⟨3006692, by rfl⟩ : syracuseStep 4008923 = 6013385) B6013385
theorem B1584107 : Blo 1052612 1584107 := bstep (se 1 (by rfl) ⟨1188080, by rfl⟩ : syracuseStep 1584107 = 2376161) B2376161
theorem B1584311 : Blo 1052612 1584311 := bstep (se 1 (by rfl) ⟨1188233, by rfl⟩ : syracuseStep 1584311 = 2376467) B2376467
theorem B3419435 : Blo 1052612 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B1584551 : Blo 1052612 1584551 := bstep (se 1 (by rfl) ⟨1188413, by rfl⟩ : syracuseStep 1584551 = 2376827) B2376827
theorem B4500983 : Blo 1052612 4500983 := bstep (se 1 (by rfl) ⟨3375737, by rfl⟩ : syracuseStep 4500983 = 6751475) B6751475
theorem B2371067 : Blo 1052612 2371067 := bstep (se 1 (by rfl) ⟨1778300, by rfl⟩ : syracuseStep 2371067 = 3556601) B3556601
theorem B1584635 : Blo 1052612 1584635 := bstep (se 1 (by rfl) ⟨1188476, by rfl⟩ : syracuseStep 1584635 = 2376953) B2376953
theorem B1781311 : Blo 1052612 1781311 := bstep (se 1 (by rfl) ⟨1335983, by rfl⟩ : syracuseStep 1781311 = 2671967) B2671967
theorem B1584731 : Blo 1052612 1584731 := bstep (se 1 (by rfl) ⟨1188548, by rfl⟩ : syracuseStep 1584731 = 2377097) B2377097
theorem B2371247 : Blo 1052612 2371247 := bstep (se 1 (by rfl) ⟨1778435, by rfl⟩ : syracuseStep 2371247 = 3556871) B3556871
theorem B1584815 : Blo 1052612 1584815 := bstep (se 1 (by rfl) ⟨1188611, by rfl⟩ : syracuseStep 1584815 = 2377223) B2377223
theorem B4010107 : Blo 1052612 4010107 := bstep (se 1 (by rfl) ⟨3007580, by rfl⟩ : syracuseStep 4010107 = 6015161) B6015161
theorem B1782047 : Blo 1052612 1782047 := bstep (se 1 (by rfl) ⟨1336535, by rfl⟩ : syracuseStep 1782047 = 2673071) B2673071
theorem B2371895 : Blo 1052612 2371895 := bstep (se 1 (by rfl) ⟨1778921, by rfl⟩ : syracuseStep 2371895 = 3557843) B3557843
theorem B2371967 : Blo 1052612 2371967 := bstep (se 1 (by rfl) ⟨1778975, by rfl⟩ : syracuseStep 2371967 = 3557951) B3557951
theorem B4010579 : Blo 1052612 4010579 := bstep (se 1 (by rfl) ⟨3007934, by rfl⟩ : syracuseStep 4010579 = 6015869) B6015869
theorem B2667289 : Blo 1052612 2667289 := bstep (se 2 (by rfl) ⟨1000233, by rfl⟩ : syracuseStep 2667289 = 2000467) B2000467
theorem B1782695 : Blo 1052612 1782695 := bstep (se 1 (by rfl) ⟨1337021, by rfl⟩ : syracuseStep 1782695 = 2674043) B2674043
theorem B2667593 : Blo 1052612 2667593 := bstep (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) B2000695
theorem B1782857 : Blo 1052612 1782857 := bstep (se 2 (by rfl) ⟨668571, by rfl⟩ : syracuseStep 1782857 = 1337143) B1337143
theorem B6599879 : Blo 1052612 6599879 := bstep (se 1 (by rfl) ⟨4949909, by rfl⟩ : syracuseStep 6599879 = 9899819) B9899819
theorem B2373191 : Blo 1052612 2373191 := bstep (se 1 (by rfl) ⟨1779893, by rfl⟩ : syracuseStep 2373191 = 3559787) B3559787
theorem B4273847 : Blo 1052612 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B38975185 : Blo 1052612 38975185 := bstep (se 2 (by rfl) ⟨14615694, by rfl⟩ : syracuseStep 38975185 = 29231389) B29231389
theorem B2373371 : Blo 1052612 2373371 := bstep (se 1 (by rfl) ⟨1780028, by rfl⟩ : syracuseStep 2373371 = 3560057) B3560057
theorem B3553523 : Blo 1052612 3553523 := bstep (se 1 (by rfl) ⟨2665142, by rfl⟩ : syracuseStep 3553523 = 5330285) B5330285
theorem B3553577 : Blo 1052612 3553577 := bstep (se 2 (by rfl) ⟨1332591, by rfl⟩ : syracuseStep 3553577 = 2665183) B2665183
theorem B2373929 : Blo 1052612 2373929 := bstep (se 2 (by rfl) ⟨890223, by rfl⟩ : syracuseStep 2373929 = 1780447) B1780447
theorem B6077263 : Blo 1052612 6077263 := bstep (se 1 (by rfl) ⟨4557947, by rfl⟩ : syracuseStep 6077263 = 9115895) B9115895
theorem B2669395 : Blo 1052612 2669395 := bstep (se 1 (by rfl) ⟨2002046, by rfl⟩ : syracuseStep 2669395 = 4004093) B4004093
theorem B2374505 : Blo 1052612 2374505 := bstep (se 2 (by rfl) ⟨890439, by rfl⟩ : syracuseStep 2374505 = 1780879) B1780879
theorem B2374559 : Blo 1052612 2374559 := bstep (se 1 (by rfl) ⟨1780919, by rfl⟩ : syracuseStep 2374559 = 3561839) B3561839
theorem B2669537 : Blo 1052612 2669537 := bstep (se 2 (by rfl) ⟨1001076, by rfl⟩ : syracuseStep 2669537 = 2002153) B2002153
theorem B5061761 : Blo 1052612 5061761 := bstep (se 2 (by rfl) ⟨1898160, by rfl⟩ : syracuseStep 5061761 = 3796321) B3796321
theorem B8994311 : Blo 1052612 8994311 := bstep (se 1 (by rfl) ⟨6745733, by rfl⟩ : syracuseStep 8994311 = 13491467) B13491467
theorem B6504203 : Blo 1052612 6504203 := bstep (se 1 (by rfl) ⟨4878152, by rfl⟩ : syracuseStep 6504203 = 9756305) B9756305
theorem B3555143 : Blo 1052612 3555143 := bstep (se 1 (by rfl) ⟨2666357, by rfl⟩ : syracuseStep 3555143 = 5332715) B5332715
theorem B2375495 : Blo 1052612 2375495 := bstep (se 1 (by rfl) ⟨1781621, by rfl⟩ : syracuseStep 2375495 = 3563243) B3563243
theorem B3555197 : Blo 1052612 3555197 := bstep (se 3 (by rfl) ⟨666599, by rfl⟩ : syracuseStep 3555197 = 1333199) B1333199
theorem B5062571 : Blo 1052612 5062571 := bstep (se 1 (by rfl) ⟨3796928, by rfl⟩ : syracuseStep 5062571 = 7593857) B7593857
theorem B6012953 : Blo 1052612 6012953 := bstep (se 2 (by rfl) ⟨2254857, by rfl⟩ : syracuseStep 6012953 = 4509715) B4509715
theorem B3555467 : Blo 1052612 3555467 := bstep (se 1 (by rfl) ⟨2666600, by rfl⟩ : syracuseStep 3555467 = 5333201) B5333201
theorem B2998559 : Blo 1052612 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B3555791 : Blo 1052612 3555791 := bstep (se 1 (by rfl) ⟨2666843, by rfl⟩ : syracuseStep 3555791 = 5333687) B5333687
theorem B2376143 : Blo 1052612 2376143 := bstep (se 1 (by rfl) ⟨1782107, by rfl⟩ : syracuseStep 2376143 = 3564215) B3564215
theorem B2671339 : Blo 1052612 2671339 := bstep (se 1 (by rfl) ⟨2003504, by rfl⟩ : syracuseStep 2671339 = 4007009) B4007009
theorem B3556115 : Blo 1052612 3556115 := bstep (se 1 (by rfl) ⟨2667086, by rfl⟩ : syracuseStep 3556115 = 5334173) B5334173
theorem B2704175 : Blo 1052612 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B2999197 : Blo 1052612 2999197 := bstep (se 3 (by rfl) ⟨562349, by rfl⟩ : syracuseStep 2999197 = 1124699) B1124699
theorem B2376809 : Blo 1052612 2376809 := bstep (se 2 (by rfl) ⟨891303, by rfl⟩ : syracuseStep 2376809 = 1782607) B1782607
theorem B1688683 : Blo 1052612 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B9651467 : Blo 1052612 9651467 := bstep (se 1 (by rfl) ⟨7238600, by rfl⟩ : syracuseStep 9651467 = 14477201) B14477201
theorem B1426843 : Blo 1052612 1426843 := bstep (se 1 (by rfl) ⟨1070132, by rfl⟩ : syracuseStep 1426843 = 2140265) B2140265
theorem B2999767 : Blo 1052612 2999767 := bstep (se 1 (by rfl) ⟨2249825, by rfl⟩ : syracuseStep 2999767 = 4499651) B4499651
theorem B25642493 : Blo 1052612 25642493 := bstep (se 3 (by rfl) ⟨4807967, by rfl⟩ : syracuseStep 25642493 = 9615935) B9615935
theorem B20268569 : Blo 1052612 20268569 := bstep (se 2 (by rfl) ⟨7600713, by rfl⟩ : syracuseStep 20268569 = 15201427) B15201427
theorem B3556979 : Blo 1052612 3556979 := bstep (se 1 (by rfl) ⟨2667734, by rfl⟩ : syracuseStep 3556979 = 5335469) B5335469
theorem B3557087 : Blo 1052612 3557087 := bstep (se 1 (by rfl) ⟨2667815, by rfl⟩ : syracuseStep 3557087 = 5335631) B5335631
theorem B1689407 : Blo 1052612 1689407 := bstep (se 1 (by rfl) ⟨1267055, by rfl⟩ : syracuseStep 1689407 = 2534111) B2534111
theorem B3557249 : Blo 1052612 3557249 := bstep (se 2 (by rfl) ⟨1333968, by rfl⟩ : syracuseStep 3557249 = 2667937) B2667937
theorem B6179111 : Blo 1052612 6179111 := bstep (se 1 (by rfl) ⟨4634333, by rfl⟩ : syracuseStep 6179111 = 9268667) B9268667
theorem B1689913 : Blo 1052612 1689913 := bstep (se 2 (by rfl) ⟨633717, by rfl⟩ : syracuseStep 1689913 = 1267435) B1267435
theorem B6408605 : Blo 1052612 6408605 := bstep (se 3 (by rfl) ⟨1201613, by rfl⟩ : syracuseStep 6408605 = 2403227) B2403227
theorem B3557789 : Blo 1052612 3557789 := bstep (se 3 (by rfl) ⟨667085, by rfl⟩ : syracuseStep 3557789 = 1334171) B1334171
theorem B9619913 : Blo 1052612 9619913 := bstep (se 2 (by rfl) ⟨3607467, by rfl⟩ : syracuseStep 9619913 = 7214935) B7214935
theorem B12831371 : Blo 1052612 12831371 := bstep (se 1 (by rfl) ⟨9623528, by rfl⟩ : syracuseStep 12831371 = 19247057) B19247057
theorem B3558059 : Blo 1052612 3558059 := bstep (se 1 (by rfl) ⟨2668544, by rfl⟩ : syracuseStep 3558059 = 5337089) B5337089
theorem B15223571 : Blo 1052612 15223571 := bstep (se 1 (by rfl) ⟨11417678, by rfl⟩ : syracuseStep 15223571 = 22835357) B22835357
theorem B3558599 : Blo 1052612 3558599 := bstep (se 1 (by rfl) ⟨2668949, by rfl⟩ : syracuseStep 3558599 = 5337899) B5337899
theorem B1691047 : Blo 1052612 1691047 := bstep (se 1 (by rfl) ⟨1268285, by rfl⟩ : syracuseStep 1691047 = 2536571) B2536571
theorem B8998411 : Blo 1052612 8998411 := bstep (se 1 (by rfl) ⟨6748808, by rfl⟩ : syracuseStep 8998411 = 13497617) B13497617
theorem B6016619 : Blo 1052612 6016619 := bstep (se 1 (by rfl) ⟨4512464, by rfl⟩ : syracuseStep 6016619 = 9024929) B9024929
theorem B1691867 : Blo 1052612 1691867 := bstep (se 1 (by rfl) ⟨1268900, by rfl⟩ : syracuseStep 1691867 = 2537801) B2537801
theorem B22794533 : Blo 1052612 22794533 := bstep (se 4 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 22794533 = 4273975) B4273975
theorem B3559895 : Blo 1052612 3559895 := bstep (se 1 (by rfl) ⟨2669921, by rfl⟩ : syracuseStep 3559895 = 5339843) B5339843
theorem B8999747 : Blo 1052612 8999747 := bstep (se 1 (by rfl) ⟨6749810, by rfl⟩ : syracuseStep 8999747 = 13499621) B13499621
theorem B4117567 : Blo 1052612 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B19256399 : Blo 1052612 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B7591259 : Blo 1052612 7591259 := bstep (se 1 (by rfl) ⟨5693444, by rfl⟩ : syracuseStep 7591259 = 11386889) B11386889
theorem B19518907 : Blo 1052612 19518907 := bstep (se 1 (by rfl) ⟨14639180, by rfl⟩ : syracuseStep 19518907 = 29278361) B29278361
theorem B1070911 : Blo 1052612 1070911 := bstep (se 1 (by rfl) ⟨803183, by rfl⟩ : syracuseStep 1070911 = 1606367) B1606367
theorem B3561353 : Blo 1052612 3561353 := bstep (se 2 (by rfl) ⟨1335507, by rfl⟩ : syracuseStep 3561353 = 2671015) B2671015
theorem B3004391 : Blo 1052612 3004391 := bstep (se 1 (by rfl) ⟨2253293, by rfl⟩ : syracuseStep 3004391 = 4506587) B4506587
theorem B3561569 : Blo 1052612 3561569 := bstep (se 2 (by rfl) ⟨1335588, by rfl⟩ : syracuseStep 3561569 = 2671177) B2671177
theorem B4511987 : Blo 1052612 4511987 := bstep (se 1 (by rfl) ⟨3383990, by rfl⟩ : syracuseStep 4511987 = 6767981) B6767981
theorem B10148125 : Blo 1052612 10148125 := bstep (se 3 (by rfl) ⟨1902773, by rfl⟩ : syracuseStep 10148125 = 3805547) B3805547
theorem B3004847 : Blo 1052612 3004847 := bstep (se 1 (by rfl) ⟨2253635, by rfl⟩ : syracuseStep 3004847 = 4507271) B4507271
theorem B5331419 : Blo 1052612 5331419 := bstep (se 1 (by rfl) ⟨3998564, by rfl⟩ : syracuseStep 5331419 = 7997129) B7997129
theorem B3201871 : Blo 1052612 3201871 := bstep (se 1 (by rfl) ⟨2401403, by rfl⟩ : syracuseStep 3201871 = 4802807) B4802807
theorem B4512671 : Blo 1052612 4512671 := bstep (se 1 (by rfl) ⟨3384503, by rfl⟩ : syracuseStep 4512671 = 6769007) B6769007
theorem B3562487 : Blo 1052612 3562487 := bstep (se 1 (by rfl) ⟨2671865, by rfl⟩ : syracuseStep 3562487 = 5343731) B5343731
theorem B7691321 : Blo 1052612 7691321 := bstep (se 2 (by rfl) ⟨2884245, by rfl⟩ : syracuseStep 7691321 = 5768491) B5768491
theorem B1334495 : Blo 1052612 1334495 := bstep (se 1 (by rfl) ⟨1000871, by rfl⟩ : syracuseStep 1334495 = 2001743) B2001743
theorem B3562919 : Blo 1052612 3562919 := bstep (se 1 (by rfl) ⟨2672189, by rfl⟩ : syracuseStep 3562919 = 5344379) B5344379
theorem B1334875 : Blo 1052612 1334875 := bstep (se 1 (by rfl) ⟨1001156, by rfl⟩ : syracuseStep 1334875 = 2002313) B2002313
theorem B3563351 : Blo 1052612 3563351 := bstep (se 1 (by rfl) ⟨2672513, by rfl⟩ : syracuseStep 3563351 = 5345027) B5345027
theorem B1499519 : Blo 1052612 1499519 := bstep (se 1 (by rfl) ⟨1124639, by rfl⟩ : syracuseStep 1499519 = 2249279) B2249279
theorem B8020457 : Blo 1052612 8020457 := bstep (se 2 (by rfl) ⟨3007671, by rfl⟩ : syracuseStep 8020457 = 6015343) B6015343
theorem B20308481 : Blo 1052612 20308481 := bstep (se 2 (by rfl) ⟨7615680, by rfl⟩ : syracuseStep 20308481 = 15231361) B15231361
theorem B3564161 : Blo 1052612 3564161 := bstep (se 2 (by rfl) ⟨1336560, by rfl⟩ : syracuseStep 3564161 = 2673121) B2673121
theorem B3039979 : Blo 1052612 3039979 := bstep (se 1 (by rfl) ⟨2279984, by rfl⟩ : syracuseStep 3039979 = 4559969) B4559969
theorem B3564431 : Blo 1052612 3564431 := bstep (se 1 (by rfl) ⟨2673323, by rfl⟩ : syracuseStep 3564431 = 5346647) B5346647
theorem B9004121 : Blo 1052612 9004121 := bstep (se 2 (by rfl) ⟨3376545, by rfl⟩ : syracuseStep 9004121 = 6753091) B6753091
theorem B1336495 : Blo 1052612 1336495 := bstep (se 1 (by rfl) ⟨1002371, by rfl⟩ : syracuseStep 1336495 = 2004743) B2004743
theorem B20276567 : Blo 1052612 20276567 := bstep (se 1 (by rfl) ⟨15207425, by rfl⟩ : syracuseStep 20276567 = 30414851) B30414851
theorem B14443883 : Blo 1052612 14443883 := bstep (se 1 (by rfl) ⟨10832912, by rfl⟩ : syracuseStep 14443883 = 21665825) B21665825
theorem B3564971 : Blo 1052612 3564971 := bstep (se 1 (by rfl) ⟨2673728, by rfl⟩ : syracuseStep 3564971 = 5347457) B5347457
theorem B3794651 : Blo 1052612 3794651 := bstep (se 1 (by rfl) ⟨2845988, by rfl⟩ : syracuseStep 3794651 = 5691977) B5691977
theorem B3565511 : Blo 1052612 3565511 := bstep (se 1 (by rfl) ⟨2674133, by rfl⟩ : syracuseStep 3565511 = 5348267) B5348267
theorem B12839057 : Blo 1052612 12839057 := bstep (se 2 (by rfl) ⟨4814646, by rfl⟩ : syracuseStep 12839057 = 9629293) B9629293
theorem B72313121 : Blo 1052612 72313121 := bstep (se 2 (by rfl) ⟨27117420, by rfl⟩ : syracuseStep 72313121 = 54234841) B54234841
theorem B8219339 : Blo 1052612 8219339 := bstep (se 1 (by rfl) ⟨6164504, by rfl⟩ : syracuseStep 8219339 = 12329009) B12329009
theorem B1830071 : Blo 1052612 1830071 := bstep (se 1 (by rfl) ⟨1372553, by rfl⟩ : syracuseStep 1830071 = 2745107) B2745107
theorem B8023373 : Blo 1052612 8023373 := bstep (se 3 (by rfl) ⟨1504382, by rfl⟩ : syracuseStep 8023373 = 3008765) B3008765
theorem B8777069 : Blo 1052612 8777069 := bstep (se 3 (by rfl) ⟨1645700, by rfl⟩ : syracuseStep 8777069 = 3291401) B3291401
theorem B15593003 : Blo 1052612 15593003 := bstep (se 1 (by rfl) ⟨11694752, by rfl⟩ : syracuseStep 15593003 = 23389505) B23389505
theorem B2847113 : Blo 1052612 2847113 := bstep (se 2 (by rfl) ⟨1067667, by rfl⟩ : syracuseStep 2847113 = 2135335) B2135335
theorem B3208061 : Blo 1052612 3208061 := bstep (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) B1203023
theorem B2848019 : Blo 1052612 2848019 := bstep (se 1 (by rfl) ⟨2136014, by rfl⟩ : syracuseStep 2848019 = 4272029) B4272029
theorem B3798427 : Blo 1052612 3798427 := bstep (se 1 (by rfl) ⟨2848820, by rfl⟩ : syracuseStep 3798427 = 5697641) B5697641
theorem B5339195 : Blo 1052612 5339195 := bstep (se 1 (by rfl) ⟨4004396, by rfl⟩ : syracuseStep 5339195 = 8008793) B8008793
theorem B12024125 : Blo 1052612 12024125 := bstep (se 3 (by rfl) ⟨2254523, by rfl⟩ : syracuseStep 12024125 = 4509047) B4509047
theorem B13531859 : Blo 1052612 13531859 := bstep (se 1 (by rfl) ⟨10148894, by rfl⟩ : syracuseStep 13531859 = 20297789) B20297789
theorem B19495889 : Blo 1052612 19495889 := bstep (se 2 (by rfl) ⟨7310958, by rfl⟩ : syracuseStep 19495889 = 14621917) B14621917
theorem B5340653 : Blo 1052612 5340653 := bstep (se 3 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 5340653 = 2002745) B2002745
theorem B5340815 : Blo 1052612 5340815 := bstep (se 1 (by rfl) ⟨4005611, by rfl⟩ : syracuseStep 5340815 = 8011223) B8011223
theorem B1998569 : Blo 1052612 1998569 := bstep (se 2 (by rfl) ⟨749463, by rfl⟩ : syracuseStep 1998569 = 1498927) B1498927
theorem B3800819 : Blo 1052612 3800819 := bstep (se 1 (by rfl) ⟨2850614, by rfl⟩ : syracuseStep 3800819 = 5701229) B5701229
theorem B5701919 : Blo 1052612 5701919 := bstep (se 1 (by rfl) ⟨4276439, by rfl⟩ : syracuseStep 5701919 = 8552879) B8552879
theorem B3801455 : Blo 1052612 3801455 := bstep (se 1 (by rfl) ⟨2851091, by rfl⟩ : syracuseStep 3801455 = 5702183) B5702183
theorem B1802783 : Blo 1052612 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B4063823 : Blo 1052612 4063823 := bstep (se 1 (by rfl) ⟨3047867, by rfl⟩ : syracuseStep 4063823 = 6095735) B6095735
theorem B7996157 : Blo 1052612 7996157 := bstep (se 3 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 7996157 = 2998559) B2998559
theorem B3998717 : Blo 1052612 3998717 := bstep (se 3 (by rfl) ⟨749759, by rfl⟩ : syracuseStep 3998717 = 1499519) B1499519
theorem B3998929 : Blo 1052612 3998929 := bstep (se 2 (by rfl) ⟨1499598, by rfl⟩ : syracuseStep 3998929 = 2999197) B2999197
theorem B3081503 : Blo 1052612 3081503 := bstep (se 1 (by rfl) ⟨2311127, by rfl⟩ : syracuseStep 3081503 = 4622255) B4622255
theorem B9012869 : Blo 1052612 9012869 := bstep (se 4 (by rfl) ⟨844956, by rfl⟩ : syracuseStep 9012869 = 1689913) B1689913
theorem B8554247 : Blo 1052612 8554247 := bstep (se 1 (by rfl) ⟨6415685, by rfl⟩ : syracuseStep 8554247 = 12831371) B12831371
theorem B1902457 : Blo 1052612 1902457 := bstep (se 2 (by rfl) ⟨713421, by rfl⟩ : syracuseStep 1902457 = 1426843) B1426843
theorem B3999689 : Blo 1052612 3999689 := bstep (se 2 (by rfl) ⟨1499883, by rfl⟩ : syracuseStep 3999689 = 2999767) B2999767
theorem B19236973 : Blo 1052612 19236973 := bstep (se 3 (by rfl) ⟨3606932, by rfl⟩ : syracuseStep 19236973 = 7213865) B7213865
theorem B4000175 : Blo 1052612 4000175 := bstep (se 1 (by rfl) ⟨3000131, by rfl⟩ : syracuseStep 4000175 = 6000263) B6000263
theorem B5999831 : Blo 1052612 5999831 := bstep (se 1 (by rfl) ⟨4499873, by rfl⟩ : syracuseStep 5999831 = 8999747) B8999747
theorem B4001359 : Blo 1052612 4001359 := bstep (se 1 (by rfl) ⟨3001019, by rfl⟩ : syracuseStep 4001359 = 6002039) B6002039
theorem B1052655 : Blo 1052612 1052655 := bstep (se 1 (by rfl) ⟨789491, by rfl⟩ : syracuseStep 1052655 = 1578983) B1578983
theorem B1052667 : Blo 1052612 1052667 := bstep (se 1 (by rfl) ⟨789500, by rfl⟩ : syracuseStep 1052667 = 1579001) B1579001
theorem B1052735 : Blo 1052612 1052735 := bstep (se 1 (by rfl) ⟨789551, by rfl⟩ : syracuseStep 1052735 = 1579103) B1579103
theorem B1052775 : Blo 1052612 1052775 := bstep (se 1 (by rfl) ⟨789581, by rfl⟩ : syracuseStep 1052775 = 1579163) B1579163
theorem B1052799 : Blo 1052612 1052799 := bstep (se 1 (by rfl) ⟨789599, by rfl⟩ : syracuseStep 1052799 = 1579199) B1579199
theorem B1052827 : Blo 1052612 1052827 := bstep (se 1 (by rfl) ⟨789620, by rfl⟩ : syracuseStep 1052827 = 1579241) B1579241
theorem B2003231 : Blo 1052612 2003231 := bstep (se 1 (by rfl) ⟨1502423, by rfl⟩ : syracuseStep 2003231 = 3004847) B3004847
theorem B1053031 : Blo 1052612 1053031 := bstep (se 1 (by rfl) ⟨789773, by rfl⟩ : syracuseStep 1053031 = 1579547) B1579547
theorem B1053083 : Blo 1052612 1053083 := bstep (se 1 (by rfl) ⟨789812, by rfl⟩ : syracuseStep 1053083 = 1579625) B1579625
theorem B11997881 : Blo 1052612 11997881 := bstep (se 2 (by rfl) ⟨4499205, by rfl⟩ : syracuseStep 11997881 = 8998411) B8998411
theorem B1053435 : Blo 1052612 1053435 := bstep (se 1 (by rfl) ⟨790076, by rfl⟩ : syracuseStep 1053435 = 1580153) B1580153
theorem B1184575 : Blo 1052612 1184575 := bstep (se 1 (by rfl) ⟨888431, by rfl⟩ : syracuseStep 1184575 = 1776863) B1776863
theorem B1053503 : Blo 1052612 1053503 := bstep (se 1 (by rfl) ⟨790127, by rfl⟩ : syracuseStep 1053503 = 1580255) B1580255
theorem B1053531 : Blo 1052612 1053531 := bstep (se 1 (by rfl) ⟨790148, by rfl⟩ : syracuseStep 1053531 = 1580297) B1580297
theorem B1053599 : Blo 1052612 1053599 := bstep (se 1 (by rfl) ⟨790199, by rfl⟩ : syracuseStep 1053599 = 1580399) B1580399
theorem B1053679 : Blo 1052612 1053679 := bstep (se 1 (by rfl) ⟨790259, by rfl⟩ : syracuseStep 1053679 = 1580519) B1580519
theorem B1053767 : Blo 1052612 1053767 := bstep (se 1 (by rfl) ⟨790325, by rfl⟩ : syracuseStep 1053767 = 1580651) B1580651
theorem B1184863 : Blo 1052612 1184863 := bstep (se 1 (by rfl) ⟨888647, by rfl⟩ : syracuseStep 1184863 = 1777295) B1777295
theorem B1053851 : Blo 1052612 1053851 := bstep (se 1 (by rfl) ⟨790388, by rfl⟩ : syracuseStep 1053851 = 1580777) B1580777
theorem B1053947 : Blo 1052612 1053947 := bstep (se 1 (by rfl) ⟨790460, by rfl⟩ : syracuseStep 1053947 = 1580921) B1580921
theorem B4003091 : Blo 1052612 4003091 := bstep (se 1 (by rfl) ⟨3002318, by rfl⟩ : syracuseStep 4003091 = 6004637) B6004637
theorem B1054015 : Blo 1052612 1054015 := bstep (se 1 (by rfl) ⟨790511, by rfl⟩ : syracuseStep 1054015 = 1581023) B1581023
theorem B14423471 : Blo 1052612 14423471 := bstep (se 1 (by rfl) ⟨10817603, by rfl⟩ : syracuseStep 14423471 = 21635207) B21635207
theorem B1054183 : Blo 1052612 1054183 := bstep (se 1 (by rfl) ⟨790637, by rfl⟩ : syracuseStep 1054183 = 1581275) B1581275
theorem B4003303 : Blo 1052612 4003303 := bstep (se 1 (by rfl) ⟨3002477, by rfl⟩ : syracuseStep 4003303 = 6004955) B6004955
theorem B1054191 : Blo 1052612 1054191 := bstep (se 1 (by rfl) ⟨790643, by rfl⟩ : syracuseStep 1054191 = 1581287) B1581287
theorem B5346809 : Blo 1052612 5346809 := bstep (se 2 (by rfl) ⟨2005053, by rfl⟩ : syracuseStep 5346809 = 4010107) B4010107
theorem B1054299 : Blo 1052612 1054299 := bstep (se 1 (by rfl) ⟨790724, by rfl⟩ : syracuseStep 1054299 = 1581449) B1581449
theorem B1054363 : Blo 1052612 1054363 := bstep (se 1 (by rfl) ⟨790772, by rfl⟩ : syracuseStep 1054363 = 1581545) B1581545
theorem B5346971 : Blo 1052612 5346971 := bstep (se 1 (by rfl) ⟨4010228, by rfl⟩ : syracuseStep 5346971 = 8020457) B8020457
theorem B13538987 : Blo 1052612 13538987 := bstep (se 1 (by rfl) ⟨10154240, by rfl⟩ : syracuseStep 13538987 = 20308481) B20308481
theorem B1054447 : Blo 1052612 1054447 := bstep (se 1 (by rfl) ⟨790835, by rfl⟩ : syracuseStep 1054447 = 1581671) B1581671
theorem B1054535 : Blo 1052612 1054535 := bstep (se 1 (by rfl) ⟨790901, by rfl⟩ : syracuseStep 1054535 = 1581803) B1581803
theorem B1054555 : Blo 1052612 1054555 := bstep (se 1 (by rfl) ⟨790916, by rfl⟩ : syracuseStep 1054555 = 1581833) B1581833
theorem B1054623 : Blo 1052612 1054623 := bstep (se 1 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 1054623 = 1581935) B1581935
theorem B6002747 : Blo 1052612 6002747 := bstep (se 1 (by rfl) ⟨4502060, by rfl⟩ : syracuseStep 6002747 = 9004121) B9004121
theorem B1054791 : Blo 1052612 1054791 := bstep (se 1 (by rfl) ⟨791093, by rfl⟩ : syracuseStep 1054791 = 1582187) B1582187
theorem B1579145 : Blo 1052612 1579145 := bstep (se 2 (by rfl) ⟨592179, by rfl⟩ : syracuseStep 1579145 = 1184359) B1184359
theorem B1054951 : Blo 1052612 1054951 := bstep (se 1 (by rfl) ⟨791213, by rfl⟩ : syracuseStep 1054951 = 1582427) B1582427
theorem B1579295 : Blo 1052612 1579295 := bstep (se 1 (by rfl) ⟨1184471, by rfl⟩ : syracuseStep 1579295 = 2368943) B2368943
theorem B5708063 : Blo 1052612 5708063 := bstep (se 1 (by rfl) ⟨4281047, by rfl⟩ : syracuseStep 5708063 = 8562095) B8562095
theorem B1055135 : Blo 1052612 1055135 := bstep (se 1 (by rfl) ⟨791351, by rfl⟩ : syracuseStep 1055135 = 1582703) B1582703
theorem B1055183 : Blo 1052612 1055183 := bstep (se 1 (by rfl) ⟨791387, by rfl⟩ : syracuseStep 1055183 = 1582775) B1582775
theorem B2529767 : Blo 1052612 2529767 := bstep (se 1 (by rfl) ⟨1897325, by rfl⟩ : syracuseStep 2529767 = 3794651) B3794651
theorem B1055207 : Blo 1052612 1055207 := bstep (se 1 (by rfl) ⟨791405, by rfl⟩ : syracuseStep 1055207 = 1582811) B1582811
theorem B1055323 : Blo 1052612 1055323 := bstep (se 1 (by rfl) ⟨791492, by rfl⟩ : syracuseStep 1055323 = 1582985) B1582985
theorem B1055391 : Blo 1052612 1055391 := bstep (se 1 (by rfl) ⟨791543, by rfl⟩ : syracuseStep 1055391 = 1583087) B1583087
theorem B8559371 : Blo 1052612 8559371 := bstep (se 1 (by rfl) ⟨6419528, by rfl⟩ : syracuseStep 8559371 = 12839057) B12839057
theorem B1579847 : Blo 1052612 1579847 := bstep (se 1 (by rfl) ⟨1184885, by rfl⟩ : syracuseStep 1579847 = 2369771) B2369771
theorem B1055559 : Blo 1052612 1055559 := bstep (se 1 (by rfl) ⟨791669, by rfl⟩ : syracuseStep 1055559 = 1583339) B1583339
theorem B1055599 : Blo 1052612 1055599 := bstep (se 1 (by rfl) ⟨791699, by rfl⟩ : syracuseStep 1055599 = 1583399) B1583399
theorem B1055655 : Blo 1052612 1055655 := bstep (se 1 (by rfl) ⟨791741, by rfl⟩ : syracuseStep 1055655 = 1583483) B1583483
theorem B8788931 : Blo 1052612 8788931 := bstep (se 1 (by rfl) ⟨6591698, by rfl⟩ : syracuseStep 8788931 = 13183397) B13183397
theorem B15211577 : Blo 1052612 15211577 := bstep (se 2 (by rfl) ⟨5704341, by rfl⟩ : syracuseStep 15211577 = 11408683) B11408683
theorem B1055835 : Blo 1052612 1055835 := bstep (se 1 (by rfl) ⟨791876, by rfl⟩ : syracuseStep 1055835 = 1583753) B1583753
theorem B5479559 : Blo 1052612 5479559 := bstep (se 1 (by rfl) ⟨4109669, by rfl⟩ : syracuseStep 5479559 = 8219339) B8219339
theorem B1187023 : Blo 1052612 1187023 := bstep (se 1 (by rfl) ⟨890267, by rfl⟩ : syracuseStep 1187023 = 1780535) B1780535
theorem B1055951 : Blo 1052612 1055951 := bstep (se 1 (by rfl) ⟨791963, by rfl⟩ : syracuseStep 1055951 = 1583927) B1583927
theorem B1055975 : Blo 1052612 1055975 := bstep (se 1 (by rfl) ⟨791981, by rfl⟩ : syracuseStep 1055975 = 1583963) B1583963
theorem B26025209 : Blo 1052612 26025209 := bstep (se 2 (by rfl) ⟨9759453, by rfl⟩ : syracuseStep 26025209 = 19518907) B19518907
theorem B1056071 : Blo 1052612 1056071 := bstep (se 1 (by rfl) ⟨792053, by rfl⟩ : syracuseStep 1056071 = 1584107) B1584107
theorem B1056207 : Blo 1052612 1056207 := bstep (se 1 (by rfl) ⟨792155, by rfl⟩ : syracuseStep 1056207 = 1584311) B1584311
theorem B5348915 : Blo 1052612 5348915 := bstep (se 1 (by rfl) ⟨4011686, by rfl⟩ : syracuseStep 5348915 = 8023373) B8023373
theorem B1056367 : Blo 1052612 1056367 := bstep (se 1 (by rfl) ⟨792275, by rfl⟩ : syracuseStep 1056367 = 1584551) B1584551
theorem B1580711 : Blo 1052612 1580711 := bstep (se 1 (by rfl) ⟨1185533, by rfl⟩ : syracuseStep 1580711 = 2371067) B2371067
theorem B1056423 : Blo 1052612 1056423 := bstep (se 1 (by rfl) ⟨792317, by rfl⟩ : syracuseStep 1056423 = 1584635) B1584635
theorem B10395335 : Blo 1052612 10395335 := bstep (se 1 (by rfl) ⟨7796501, by rfl⟩ : syracuseStep 10395335 = 15593003) B15593003
theorem B1056487 : Blo 1052612 1056487 := bstep (se 1 (by rfl) ⟨792365, by rfl⟩ : syracuseStep 1056487 = 1584731) B1584731
theorem B1580831 : Blo 1052612 1580831 := bstep (se 1 (by rfl) ⟨1185623, by rfl⟩ : syracuseStep 1580831 = 2371247) B2371247
theorem B1056543 : Blo 1052612 1056543 := bstep (se 1 (by rfl) ⟨792407, by rfl⟩ : syracuseStep 1056543 = 1584815) B1584815
theorem B1188031 : Blo 1052612 1188031 := bstep (se 1 (by rfl) ⟨891023, by rfl⟩ : syracuseStep 1188031 = 1782047) B1782047
theorem B1581263 : Blo 1052612 1581263 := bstep (se 1 (by rfl) ⟨1185947, by rfl⟩ : syracuseStep 1581263 = 2371895) B2371895
theorem B1581311 : Blo 1052612 1581311 := bstep (se 1 (by rfl) ⟨1185983, by rfl⟩ : syracuseStep 1581311 = 2371967) B2371967
theorem B2138707 : Blo 1052612 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B1188463 : Blo 1052612 1188463 := bstep (se 1 (by rfl) ⟨891347, by rfl⟩ : syracuseStep 1188463 = 1782695) B1782695
theorem B12198521 : Blo 1052612 12198521 := bstep (se 2 (by rfl) ⟨4574445, by rfl⟩ : syracuseStep 12198521 = 9148891) B9148891
theorem B1778395 : Blo 1052612 1778395 := bstep (se 1 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 1778395 = 2667593) B2667593
theorem B1188571 : Blo 1052612 1188571 := bstep (se 1 (by rfl) ⟨891428, by rfl⟩ : syracuseStep 1188571 = 1782857) B1782857
theorem B9118493 : Blo 1052612 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B4399919 : Blo 1052612 4399919 := bstep (se 1 (by rfl) ⟨3299939, by rfl⟩ : syracuseStep 4399919 = 6599879) B6599879
theorem B1582127 : Blo 1052612 1582127 := bstep (se 1 (by rfl) ⟨1186595, by rfl⟩ : syracuseStep 1582127 = 2373191) B2373191
theorem B8103017 : Blo 1052612 8103017 := bstep (se 2 (by rfl) ⟨3038631, by rfl⟩ : syracuseStep 8103017 = 6077263) B6077263
theorem B4269161 : Blo 1052612 4269161 := bstep (se 2 (by rfl) ⟨1600935, by rfl⟩ : syracuseStep 4269161 = 3201871) B3201871
theorem B1582247 : Blo 1052612 1582247 := bstep (se 1 (by rfl) ⟨1186685, by rfl⟩ : syracuseStep 1582247 = 2373371) B2373371
theorem B2369015 : Blo 1052612 2369015 := bstep (se 1 (by rfl) ⟨1776761, by rfl⟩ : syracuseStep 2369015 = 3553523) B3553523
theorem B2369051 : Blo 1052612 2369051 := bstep (se 1 (by rfl) ⟨1776788, by rfl⟩ : syracuseStep 2369051 = 3553577) B3553577
theorem B1582619 : Blo 1052612 1582619 := bstep (se 1 (by rfl) ⟨1186964, by rfl⟩ : syracuseStep 1582619 = 2373929) B2373929
theorem B9021239 : Blo 1052612 9021239 := bstep (se 1 (by rfl) ⟨6765929, by rfl⟩ : syracuseStep 9021239 = 13531859) B13531859
theorem B1583003 : Blo 1052612 1583003 := bstep (se 1 (by rfl) ⟨1187252, by rfl⟩ : syracuseStep 1583003 = 2374505) B2374505
theorem B1583039 : Blo 1052612 1583039 := bstep (se 1 (by rfl) ⟨1187279, by rfl⟩ : syracuseStep 1583039 = 2374559) B2374559
theorem B1779691 : Blo 1052612 1779691 := bstep (se 1 (by rfl) ⟨1334768, by rfl⟩ : syracuseStep 1779691 = 2669537) B2669537
theorem B1779833 : Blo 1052612 1779833 := bstep (se 2 (by rfl) ⟨667437, by rfl⟩ : syracuseStep 1779833 = 1334875) B1334875
theorem B1583225 : Blo 1052612 1583225 := bstep (se 2 (by rfl) ⟨593709, by rfl⟩ : syracuseStep 1583225 = 1187419) B1187419
theorem B2533879 : Blo 1052612 2533879 := bstep (se 1 (by rfl) ⟨1900409, by rfl⟩ : syracuseStep 2533879 = 3800819) B3800819
theorem B2370041 : Blo 1052612 2370041 := bstep (se 2 (by rfl) ⟨888765, by rfl⟩ : syracuseStep 2370041 = 1777531) B1777531
theorem B1583609 : Blo 1052612 1583609 := bstep (se 2 (by rfl) ⟨593853, by rfl⟩ : syracuseStep 1583609 = 1187707) B1187707
theorem B4336135 : Blo 1052612 4336135 := bstep (se 1 (by rfl) ⟨3252101, by rfl⟩ : syracuseStep 4336135 = 6504203) B6504203
theorem B2370095 : Blo 1052612 2370095 := bstep (se 1 (by rfl) ⟨1777571, by rfl⟩ : syracuseStep 2370095 = 3555143) B3555143
theorem B1583663 : Blo 1052612 1583663 := bstep (se 1 (by rfl) ⟨1187747, by rfl⟩ : syracuseStep 1583663 = 2375495) B2375495
theorem B2370131 : Blo 1052612 2370131 := bstep (se 1 (by rfl) ⟨1777598, by rfl⟩ : syracuseStep 2370131 = 3555197) B3555197
theorem B4008635 : Blo 1052612 4008635 := bstep (se 1 (by rfl) ⟨3006476, by rfl⟩ : syracuseStep 4008635 = 6012953) B6012953
theorem B2370311 : Blo 1052612 2370311 := bstep (se 1 (by rfl) ⟨1777733, by rfl⟩ : syracuseStep 2370311 = 3555467) B3555467
theorem B2370527 : Blo 1052612 2370527 := bstep (se 1 (by rfl) ⟨1777895, by rfl⟩ : syracuseStep 2370527 = 3555791) B3555791
theorem B1584095 : Blo 1052612 1584095 := bstep (se 1 (by rfl) ⟨1188071, by rfl⟩ : syracuseStep 1584095 = 2376143) B2376143
theorem B2370743 : Blo 1052612 2370743 := bstep (se 1 (by rfl) ⟨1778057, by rfl⟩ : syracuseStep 2370743 = 3556115) B3556115
theorem B1355063 : Blo 1052612 1355063 := bstep (se 1 (by rfl) ⟨1016297, by rfl⟩ : syracuseStep 1355063 = 2032595) B2032595
theorem B8564105 : Blo 1052612 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B1584539 : Blo 1052612 1584539 := bstep (se 1 (by rfl) ⟨1188404, by rfl⟩ : syracuseStep 1584539 = 2376809) B2376809
theorem B6434311 : Blo 1052612 6434311 := bstep (se 1 (by rfl) ⟨4825733, by rfl⟩ : syracuseStep 6434311 = 9651467) B9651467
theorem B13512379 : Blo 1052612 13512379 := bstep (se 1 (by rfl) ⟨10134284, by rfl⟩ : syracuseStep 13512379 = 20268569) B20268569
theorem B2371319 : Blo 1052612 2371319 := bstep (se 1 (by rfl) ⟨1778489, by rfl⟩ : syracuseStep 2371319 = 3556979) B3556979
theorem B2371391 : Blo 1052612 2371391 := bstep (se 1 (by rfl) ⟨1778543, by rfl⟩ : syracuseStep 2371391 = 3557087) B3557087
theorem B1126271 : Blo 1052612 1126271 := bstep (se 1 (by rfl) ⟨844703, by rfl⟩ : syracuseStep 1126271 = 1689407) B1689407
theorem B2371499 : Blo 1052612 2371499 := bstep (se 1 (by rfl) ⟨1778624, by rfl⟩ : syracuseStep 2371499 = 3557249) B3557249
theorem B1781993 : Blo 1052612 1781993 := bstep (se 2 (by rfl) ⟨668247, by rfl⟩ : syracuseStep 1781993 = 1336495) B1336495
theorem B2371859 : Blo 1052612 2371859 := bstep (se 1 (by rfl) ⟨1778894, by rfl⟩ : syracuseStep 2371859 = 3557789) B3557789
theorem B2372039 : Blo 1052612 2372039 := bstep (se 1 (by rfl) ⟨1779029, by rfl⟩ : syracuseStep 2372039 = 3558059) B3558059
theorem B11383517 : Blo 1052612 11383517 := bstep (se 3 (by rfl) ⟨2134409, by rfl⟩ : syracuseStep 11383517 = 4268819) B4268819
theorem B2372399 : Blo 1052612 2372399 := bstep (se 1 (by rfl) ⟨1779299, by rfl⟩ : syracuseStep 2372399 = 3558599) B3558599
theorem B2667401 : Blo 1052612 2667401 := bstep (se 2 (by rfl) ⟨1000275, by rfl⟩ : syracuseStep 2667401 = 2000551) B2000551
theorem B2372489 : Blo 1052612 2372489 := bstep (se 2 (by rfl) ⟨889683, by rfl⟩ : syracuseStep 2372489 = 1779367) B1779367
theorem B2667431 : Blo 1052612 2667431 := bstep (se 1 (by rfl) ⟨2000573, by rfl⟩ : syracuseStep 2667431 = 4001147) B4001147
theorem B4011079 : Blo 1052612 4011079 := bstep (se 1 (by rfl) ⟨3008309, by rfl⟩ : syracuseStep 4011079 = 6016619) B6016619
theorem B9024655 : Blo 1052612 9024655 := bstep (se 1 (by rfl) ⟨6768491, by rfl⟩ : syracuseStep 9024655 = 13536983) B13536983
theorem B8107451 : Blo 1052612 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B2373263 : Blo 1052612 2373263 := bstep (se 1 (by rfl) ⟨1779947, by rfl⟩ : syracuseStep 2373263 = 3559895) B3559895
theorem B3552929 : Blo 1052612 3552929 := bstep (se 2 (by rfl) ⟨1332348, by rfl⟩ : syracuseStep 3552929 = 2664697) B2664697
theorem B2373353 : Blo 1052612 2373353 := bstep (se 2 (by rfl) ⟨890007, by rfl⟩ : syracuseStep 2373353 = 1780015) B1780015
theorem B18233225 : Blo 1052612 18233225 := bstep (se 2 (by rfl) ⟨6837459, by rfl⟩ : syracuseStep 18233225 = 13674919) B13674919
theorem B2668585 : Blo 1052612 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B5060839 : Blo 1052612 5060839 := bstep (se 1 (by rfl) ⟨3795629, by rfl⟩ : syracuseStep 5060839 = 7591259) B7591259
theorem B16234775 : Blo 1052612 16234775 := bstep (se 1 (by rfl) ⟨12176081, by rfl⟩ : syracuseStep 16234775 = 24352163) B24352163
theorem B2374235 : Blo 1052612 2374235 := bstep (se 1 (by rfl) ⟨1780676, by rfl⟩ : syracuseStep 2374235 = 3561353) B3561353
theorem B2374379 : Blo 1052612 2374379 := bstep (se 1 (by rfl) ⟨1780784, by rfl⟩ : syracuseStep 2374379 = 3561569) B3561569
theorem B3554279 : Blo 1052612 3554279 := bstep (se 1 (by rfl) ⟨2665709, by rfl⟩ : syracuseStep 3554279 = 5331419) B5331419
theorem B2374991 : Blo 1052612 2374991 := bstep (se 1 (by rfl) ⟨1781243, by rfl⟩ : syracuseStep 2374991 = 3562487) B3562487
theorem B5127547 : Blo 1052612 5127547 := bstep (se 1 (by rfl) ⟨3845660, by rfl⟩ : syracuseStep 5127547 = 7691321) B7691321
theorem B2669993 : Blo 1052612 2669993 := bstep (se 2 (by rfl) ⟨1001247, by rfl⟩ : syracuseStep 2669993 = 2002495) B2002495
theorem B2375081 : Blo 1052612 2375081 := bstep (se 2 (by rfl) ⟨890655, by rfl⟩ : syracuseStep 2375081 = 1781311) B1781311
theorem B2375279 : Blo 1052612 2375279 := bstep (se 1 (by rfl) ⟨1781459, by rfl⟩ : syracuseStep 2375279 = 3562919) B3562919
theorem B2375567 : Blo 1052612 2375567 := bstep (se 1 (by rfl) ⟨1781675, by rfl⟩ : syracuseStep 2375567 = 3563351) B3563351
theorem B8011709 : Blo 1052612 8011709 := bstep (se 3 (by rfl) ⟨1502195, by rfl⟩ : syracuseStep 8011709 = 3004391) B3004391
theorem B2376107 : Blo 1052612 2376107 := bstep (se 1 (by rfl) ⟨1782080, by rfl⟩ : syracuseStep 2376107 = 3564161) B3564161
theorem B2376287 : Blo 1052612 2376287 := bstep (se 1 (by rfl) ⟨1782215, by rfl⟩ : syracuseStep 2376287 = 3564431) B3564431
theorem B4506299 : Blo 1052612 4506299 := bstep (se 1 (by rfl) ⟨3379724, by rfl⟩ : syracuseStep 4506299 = 6759449) B6759449
theorem B13517711 : Blo 1052612 13517711 := bstep (se 1 (by rfl) ⟨10138283, by rfl⟩ : syracuseStep 13517711 = 20276567) B20276567
theorem B2376647 : Blo 1052612 2376647 := bstep (se 1 (by rfl) ⟨1782485, by rfl⟩ : syracuseStep 2376647 = 3564971) B3564971
theorem B3556385 : Blo 1052612 3556385 := bstep (se 2 (by rfl) ⟨1333644, by rfl⟩ : syracuseStep 3556385 = 2667289) B2667289
theorem B17089613 : Blo 1052612 17089613 := bstep (se 3 (by rfl) ⟨3204302, by rfl⟩ : syracuseStep 17089613 = 6408605) B6408605
theorem B2377007 : Blo 1052612 2377007 := bstep (se 1 (by rfl) ⟨1782755, by rfl⟩ : syracuseStep 2377007 = 3565511) B3565511
theorem B5490089 : Blo 1052612 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B5064569 : Blo 1052612 5064569 := bstep (se 2 (by rfl) ⟨1899213, by rfl⟩ : syracuseStep 5064569 = 3798427) B3798427
theorem B2672615 : Blo 1052612 2672615 := bstep (se 1 (by rfl) ⟨2004461, by rfl⟩ : syracuseStep 2672615 = 4008923) B4008923
theorem B5851379 : Blo 1052612 5851379 := bstep (se 1 (by rfl) ⟨4388534, by rfl⟩ : syracuseStep 5851379 = 8777069) B8777069
theorem B3000655 : Blo 1052612 3000655 := bstep (se 1 (by rfl) ⟨2250491, by rfl⟩ : syracuseStep 3000655 = 4500983) B4500983
theorem B1427881 : Blo 1052612 1427881 := bstep (se 2 (by rfl) ⟨535455, by rfl⟩ : syracuseStep 1427881 = 1070911) B1070911
theorem B4508297 : Blo 1052612 4508297 := bstep (se 2 (by rfl) ⟨1690611, by rfl⟩ : syracuseStep 4508297 = 3381223) B3381223
theorem B2673719 : Blo 1052612 2673719 := bstep (se 1 (by rfl) ⟨2005289, by rfl⟩ : syracuseStep 2673719 = 4010579) B4010579
theorem B3558653 : Blo 1052612 3558653 := bstep (se 3 (by rfl) ⟨667247, by rfl⟩ : syracuseStep 3558653 = 1334495) B1334495
theorem B207867653 : Blo 1052612 207867653 := bstep (se 4 (by rfl) ⟨19487592, by rfl⟩ : syracuseStep 207867653 = 38975185) B38975185
theorem B3559193 : Blo 1052612 3559193 := bstep (se 2 (by rfl) ⟨1334697, by rfl⟩ : syracuseStep 3559193 = 2669395) B2669395
theorem B16437113 : Blo 1052612 16437113 := bstep (se 2 (by rfl) ⟨6163917, by rfl⟩ : syracuseStep 16437113 = 12327835) B12327835
theorem B69390229 : Blo 1052612 69390229 := bstep (se 6 (by rfl) ⟨1626333, by rfl⟩ : syracuseStep 69390229 = 3252667) B3252667
theorem B3559463 : Blo 1052612 3559463 := bstep (se 1 (by rfl) ⟨2669597, by rfl⟩ : syracuseStep 3559463 = 5339195) B5339195
theorem B8016083 : Blo 1052612 8016083 := bstep (se 1 (by rfl) ⟨6012062, by rfl⟩ : syracuseStep 8016083 = 12024125) B12024125
theorem B12997259 : Blo 1052612 12997259 := bstep (se 1 (by rfl) ⟨9747944, by rfl⟩ : syracuseStep 12997259 = 19495889) B19495889
theorem B3560435 : Blo 1052612 3560435 := bstep (se 1 (by rfl) ⟨2670326, by rfl⟩ : syracuseStep 3560435 = 5340653) B5340653
theorem B3560543 : Blo 1052612 3560543 := bstep (se 1 (by rfl) ⟨2670407, by rfl⟩ : syracuseStep 3560543 = 5340815) B5340815
theorem B1332379 : Blo 1052612 1332379 := bstep (se 1 (by rfl) ⟨999284, by rfl⟩ : syracuseStep 1332379 = 1998569) B1998569
theorem B5330447 : Blo 1052612 5330447 := bstep (se 1 (by rfl) ⟨3997835, by rfl⟩ : syracuseStep 5330447 = 7995671) B7995671
theorem B3560975 : Blo 1052612 3560975 := bstep (se 1 (by rfl) ⟨2670731, by rfl⟩ : syracuseStep 3560975 = 5341463) B5341463
theorem B4511645 : Blo 1052612 4511645 := bstep (se 3 (by rfl) ⟨845933, by rfl⟩ : syracuseStep 4511645 = 1691867) B1691867
theorem B4511713 : Blo 1052612 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B3561785 : Blo 1052612 3561785 := bstep (se 2 (by rfl) ⟨1335669, by rfl⟩ : syracuseStep 3561785 = 2671339) B2671339
theorem B5331257 : Blo 1052612 5331257 := bstep (se 2 (by rfl) ⟨1999221, by rfl⟩ : syracuseStep 5331257 = 3998443) B3998443
theorem B4053305 : Blo 1052612 4053305 := bstep (se 2 (by rfl) ⟨1519989, by rfl⟩ : syracuseStep 4053305 = 3039979) B3039979
theorem B17094995 : Blo 1052612 17094995 := bstep (se 1 (by rfl) ⟨12821246, by rfl⟩ : syracuseStep 17094995 = 25642493) B25642493
theorem B6838715 : Blo 1052612 6838715 := bstep (se 1 (by rfl) ⟨5129036, by rfl⟩ : syracuseStep 6838715 = 10258073) B10258073
theorem B3562055 : Blo 1052612 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B2251577 : Blo 1052612 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B4119407 : Blo 1052612 4119407 := bstep (se 1 (by rfl) ⟨3089555, by rfl⟩ : syracuseStep 4119407 = 6179111) B6179111
theorem B6413275 : Blo 1052612 6413275 := bstep (se 1 (by rfl) ⟨4809956, by rfl⟩ : syracuseStep 6413275 = 9619913) B9619913
theorem B10149047 : Blo 1052612 10149047 := bstep (se 1 (by rfl) ⟨7611785, by rfl⟩ : syracuseStep 10149047 = 15223571) B15223571
theorem B15196355 : Blo 1052612 15196355 := bstep (se 1 (by rfl) ⟨11397266, by rfl⟩ : syracuseStep 15196355 = 22794533) B22794533
theorem B2253055 : Blo 1052612 2253055 := bstep (se 1 (by rfl) ⟨1689791, by rfl⟩ : syracuseStep 2253055 = 3379583) B3379583
theorem B7594717 : Blo 1052612 7594717 := bstep (se 3 (by rfl) ⟨1424009, by rfl⟩ : syracuseStep 7594717 = 2848019) B2848019
theorem B12837599 : Blo 1052612 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B5071987 : Blo 1052612 5071987 := bstep (se 1 (by rfl) ⟨3803990, by rfl⟩ : syracuseStep 5071987 = 7607981) B7607981
theorem B5137667 : Blo 1052612 5137667 := bstep (se 1 (by rfl) ⟨3853250, by rfl⟩ : syracuseStep 5137667 = 7706501) B7706501
theorem B3007991 : Blo 1052612 3007991 := bstep (se 1 (by rfl) ⟨2255993, by rfl⟩ : syracuseStep 3007991 = 4511987) B4511987
theorem B2254729 : Blo 1052612 2254729 := bstep (se 2 (by rfl) ⟨845523, by rfl⟩ : syracuseStep 2254729 = 1691047) B1691047
theorem B3008447 : Blo 1052612 3008447 := bstep (se 1 (by rfl) ⟨2256335, by rfl⟩ : syracuseStep 3008447 = 4512671) B4512671
theorem B5334983 : Blo 1052612 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B5074103 : Blo 1052612 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B192834989 : Blo 1052612 192834989 := bstep (se 3 (by rfl) ⟨36156560, by rfl⟩ : syracuseStep 192834989 = 72313121) B72313121
theorem B9629255 : Blo 1052612 9629255 := bstep (se 1 (by rfl) ⟨7221941, by rfl⟩ : syracuseStep 9629255 = 14443883) B14443883
theorem B2256635 : Blo 1052612 2256635 := bstep (se 1 (by rfl) ⟨1692476, by rfl⟩ : syracuseStep 2256635 = 3384953) B3384953
theorem B1898075 : Blo 1052612 1898075 := bstep (se 1 (by rfl) ⟨1423556, by rfl⟩ : syracuseStep 1898075 = 2847113) B2847113
theorem B13530833 : Blo 1052612 13530833 := bstep (se 2 (by rfl) ⟨5074062, by rfl⟩ : syracuseStep 13530833 = 10148125) B10148125
theorem B4880189 : Blo 1052612 4880189 := bstep (se 3 (by rfl) ⟨915035, by rfl⟩ : syracuseStep 4880189 = 1830071) B1830071
theorem B2849231 : Blo 1052612 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B3374507 : Blo 1052612 3374507 := bstep (se 1 (by rfl) ⟨2530880, by rfl⟩ : syracuseStep 3374507 = 5061761) B5061761
theorem B5996207 : Blo 1052612 5996207 := bstep (se 1 (by rfl) ⟨4497155, by rfl⟩ : syracuseStep 5996207 = 8994311) B8994311
theorem B3375047 : Blo 1052612 3375047 := bstep (se 1 (by rfl) ⟨2531285, by rfl⟩ : syracuseStep 3375047 = 5062571) B5062571
theorem B92504213 : Blo 1052612 92504213 := bstep (se 6 (by rfl) ⟨2168067, by rfl⟩ : syracuseStep 92504213 = 4336135) B4336135
theorem B9011807 : Blo 1052612 9011807 := bstep (se 1 (by rfl) ⟨6758855, by rfl⟩ : syracuseStep 9011807 = 13517711) B13517711
theorem B5341949 : Blo 1052612 5341949 := bstep (se 3 (by rfl) ⟨1001615, by rfl⟩ : syracuseStep 5341949 = 2003231) B2003231
theorem B2851609 : Blo 1052612 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B10126289 : Blo 1052612 10126289 := bstep (se 2 (by rfl) ⟨3797358, by rfl⟩ : syracuseStep 10126289 = 7594717) B7594717
theorem B5702831 : Blo 1052612 5702831 := bstep (se 1 (by rfl) ⟨4277123, by rfl⟩ : syracuseStep 5702831 = 8554247) B8554247
theorem B3376379 : Blo 1052612 3376379 := bstep (se 1 (by rfl) ⟨2532284, by rfl⟩ : syracuseStep 3376379 = 5064569) B5064569
theorem B3999887 : Blo 1052612 3999887 := bstep (se 1 (by rfl) ⟨2999915, by rfl⟩ : syracuseStep 3999887 = 5999831) B5999831
theorem B138578435 : Blo 1052612 138578435 := bstep (se 1 (by rfl) ⟨103933826, by rfl⟩ : syracuseStep 138578435 = 207867653) B207867653
theorem B5344055 : Blo 1052612 5344055 := bstep (se 1 (by rfl) ⟨4008041, by rfl⟩ : syracuseStep 5344055 = 8016083) B8016083
theorem B60820469 : Blo 1052612 60820469 := bstep (se 5 (by rfl) ⟨2850959, by rfl⟩ : syracuseStep 60820469 = 5701919) B5701919
theorem B4000873 : Blo 1052612 4000873 := bstep (se 2 (by rfl) ⟨1500327, by rfl⟩ : syracuseStep 4000873 = 3000655) B3000655
theorem B7998587 : Blo 1052612 7998587 := bstep (se 1 (by rfl) ⟨5998940, by rfl⟩ : syracuseStep 7998587 = 11997881) B11997881
theorem B1903841 : Blo 1052612 1903841 := bstep (se 2 (by rfl) ⟨713940, by rfl⟩ : syracuseStep 1903841 = 1427881) B1427881
theorem B3378505 : Blo 1052612 3378505 := bstep (se 2 (by rfl) ⟨1266939, by rfl⟩ : syracuseStep 3378505 = 2533879) B2533879
theorem B4001831 : Blo 1052612 4001831 := bstep (se 1 (by rfl) ⟨3001373, by rfl⟩ : syracuseStep 4001831 = 6002747) B6002747
theorem B1052763 : Blo 1052612 1052763 := bstep (se 1 (by rfl) ⟨789572, by rfl⟩ : syracuseStep 1052763 = 1579145) B1579145
theorem B1052863 : Blo 1052612 1052863 := bstep (se 1 (by rfl) ⟨789647, by rfl⟩ : syracuseStep 1052863 = 1579295) B1579295
theorem B3805375 : Blo 1052612 3805375 := bstep (se 1 (by rfl) ⟨2854031, by rfl⟩ : syracuseStep 3805375 = 5708063) B5708063
theorem B5706247 : Blo 1052612 5706247 := bstep (se 1 (by rfl) ⟨4279685, by rfl⟩ : syracuseStep 5706247 = 8559371) B8559371
theorem B1053231 : Blo 1052612 1053231 := bstep (se 1 (by rfl) ⟨789923, by rfl⟩ : syracuseStep 1053231 = 1579847) B1579847
theorem B1053807 : Blo 1052612 1053807 := bstep (se 1 (by rfl) ⟨790355, by rfl⟩ : syracuseStep 1053807 = 1580711) B1580711
theorem B1053887 : Blo 1052612 1053887 := bstep (se 1 (by rfl) ⟨790415, by rfl⟩ : syracuseStep 1053887 = 1580831) B1580831
theorem B10130903 : Blo 1052612 10130903 := bstep (se 1 (by rfl) ⟨7598177, by rfl⟩ : syracuseStep 10130903 = 15196355) B15196355
theorem B1054175 : Blo 1052612 1054175 := bstep (se 1 (by rfl) ⟨790631, by rfl⟩ : syracuseStep 1054175 = 1581263) B1581263
theorem B1054207 : Blo 1052612 1054207 := bstep (se 1 (by rfl) ⟨790655, by rfl⟩ : syracuseStep 1054207 = 1581311) B1581311
theorem B8132347 : Blo 1052612 8132347 := bstep (se 1 (by rfl) ⟨6099260, by rfl⟩ : syracuseStep 8132347 = 12198521) B12198521
theorem B8558399 : Blo 1052612 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B15603677 : Blo 1052612 15603677 := bstep (se 3 (by rfl) ⟨2925689, by rfl⟩ : syracuseStep 15603677 = 5851379) B5851379
theorem B1054751 : Blo 1052612 1054751 := bstep (se 1 (by rfl) ⟨791063, by rfl⟩ : syracuseStep 1054751 = 1582127) B1582127
theorem B1054831 : Blo 1052612 1054831 := bstep (se 1 (by rfl) ⟨791123, by rfl⟩ : syracuseStep 1054831 = 1582247) B1582247
theorem B1579343 : Blo 1052612 1579343 := bstep (se 1 (by rfl) ⟨1184507, by rfl⟩ : syracuseStep 1579343 = 2369015) B2369015
theorem B2005327 : Blo 1052612 2005327 := bstep (se 1 (by rfl) ⟨1503995, by rfl⟩ : syracuseStep 2005327 = 3007991) B3007991
theorem B1579367 : Blo 1052612 1579367 := bstep (se 1 (by rfl) ⟨1184525, by rfl⟩ : syracuseStep 1579367 = 2369051) B2369051
theorem B1055079 : Blo 1052612 1055079 := bstep (se 1 (by rfl) ⟨791309, by rfl⟩ : syracuseStep 1055079 = 1582619) B1582619
theorem B1579433 : Blo 1052612 1579433 := bstep (se 2 (by rfl) ⟨592287, by rfl⟩ : syracuseStep 1579433 = 1184575) B1184575
theorem B1055335 : Blo 1052612 1055335 := bstep (se 1 (by rfl) ⟨791501, by rfl⟩ : syracuseStep 1055335 = 1583003) B1583003
theorem B1055359 : Blo 1052612 1055359 := bstep (se 1 (by rfl) ⟨791519, by rfl⟩ : syracuseStep 1055359 = 1583039) B1583039
theorem B2005631 : Blo 1052612 2005631 := bstep (se 1 (by rfl) ⟨1504223, by rfl⟩ : syracuseStep 2005631 = 3008447) B3008447
theorem B1186555 : Blo 1052612 1186555 := bstep (se 1 (by rfl) ⟨889916, by rfl⟩ : syracuseStep 1186555 = 1779833) B1779833
theorem B1055483 : Blo 1052612 1055483 := bstep (se 1 (by rfl) ⟨791612, by rfl⟩ : syracuseStep 1055483 = 1583225) B1583225
theorem B5348105 : Blo 1052612 5348105 := bstep (se 2 (by rfl) ⟨2005539, by rfl⟩ : syracuseStep 5348105 = 4011079) B4011079
theorem B1579817 : Blo 1052612 1579817 := bstep (se 2 (by rfl) ⟨592431, by rfl⟩ : syracuseStep 1579817 = 1184863) B1184863
theorem B12032873 : Blo 1052612 12032873 := bstep (se 2 (by rfl) ⟨4512327, by rfl⟩ : syracuseStep 12032873 = 9024655) B9024655
theorem B1776505 : Blo 1052612 1776505 := bstep (se 2 (by rfl) ⟨666189, by rfl⟩ : syracuseStep 1776505 = 1332379) B1332379
theorem B1580027 : Blo 1052612 1580027 := bstep (se 1 (by rfl) ⟨1185020, by rfl⟩ : syracuseStep 1580027 = 2370041) B2370041
theorem B1055739 : Blo 1052612 1055739 := bstep (se 1 (by rfl) ⟨791804, by rfl⟩ : syracuseStep 1055739 = 1583609) B1583609
theorem B1580063 : Blo 1052612 1580063 := bstep (se 1 (by rfl) ⟨1185047, by rfl⟩ : syracuseStep 1580063 = 2370095) B2370095
theorem B1055775 : Blo 1052612 1055775 := bstep (se 1 (by rfl) ⟨791831, by rfl⟩ : syracuseStep 1055775 = 1583663) B1583663
theorem B1580087 : Blo 1052612 1580087 := bstep (se 1 (by rfl) ⟨1185065, by rfl⟩ : syracuseStep 1580087 = 2370131) B2370131
theorem B1580207 : Blo 1052612 1580207 := bstep (se 1 (by rfl) ⟨1185155, by rfl⟩ : syracuseStep 1580207 = 2370311) B2370311
theorem B1580351 : Blo 1052612 1580351 := bstep (se 1 (by rfl) ⟨1185263, by rfl⟩ : syracuseStep 1580351 = 2370527) B2370527
theorem B1056063 : Blo 1052612 1056063 := bstep (se 1 (by rfl) ⟨792047, by rfl⟩ : syracuseStep 1056063 = 1584095) B1584095
theorem B1580495 : Blo 1052612 1580495 := bstep (se 1 (by rfl) ⟨1185371, by rfl⟩ : syracuseStep 1580495 = 2370743) B2370743
theorem B3382735 : Blo 1052612 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B6004205 : Blo 1052612 6004205 := bstep (se 3 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 6004205 = 2251577) B2251577
theorem B5709403 : Blo 1052612 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B1056359 : Blo 1052612 1056359 := bstep (se 1 (by rfl) ⟨792269, by rfl⟩ : syracuseStep 1056359 = 1584539) B1584539
theorem B128556659 : Blo 1052612 128556659 := bstep (se 1 (by rfl) ⟨96417494, by rfl⟩ : syracuseStep 128556659 = 192834989) B192834989
theorem B1580879 : Blo 1052612 1580879 := bstep (se 1 (by rfl) ⟨1185659, by rfl⟩ : syracuseStep 1580879 = 2371319) B2371319
theorem B1580927 : Blo 1052612 1580927 := bstep (se 1 (by rfl) ⟨1185695, by rfl⟩ : syracuseStep 1580927 = 2371391) B2371391
theorem B1580999 : Blo 1052612 1580999 := bstep (se 1 (by rfl) ⟨1185749, by rfl⟩ : syracuseStep 1580999 = 2371499) B2371499
theorem B1187995 : Blo 1052612 1187995 := bstep (se 1 (by rfl) ⟨890996, by rfl⟩ : syracuseStep 1187995 = 1781993) B1781993
theorem B1581239 : Blo 1052612 1581239 := bstep (se 1 (by rfl) ⟨1185929, by rfl⟩ : syracuseStep 1581239 = 2371859) B2371859
theorem B1581359 : Blo 1052612 1581359 := bstep (se 1 (by rfl) ⟨1186019, by rfl⟩ : syracuseStep 1581359 = 2372039) B2372039
theorem B1581599 : Blo 1052612 1581599 := bstep (se 1 (by rfl) ⟨1186199, by rfl⟩ : syracuseStep 1581599 = 2372399) B2372399
theorem B1778267 : Blo 1052612 1778267 := bstep (se 1 (by rfl) ⟨1333700, by rfl⟩ : syracuseStep 1778267 = 2667401) B2667401
theorem B1581659 : Blo 1052612 1581659 := bstep (se 1 (by rfl) ⟨1186244, by rfl⟩ : syracuseStep 1581659 = 2372489) B2372489
theorem B1778287 : Blo 1052612 1778287 := bstep (se 1 (by rfl) ⟨1333715, by rfl⟩ : syracuseStep 1778287 = 2667431) B2667431
theorem B3613501 : Blo 1052612 3613501 := bstep (se 3 (by rfl) ⟨677531, by rfl⟩ : syracuseStep 3613501 = 1355063) B1355063
theorem B1582175 : Blo 1052612 1582175 := bstep (se 1 (by rfl) ⟨1186631, by rfl⟩ : syracuseStep 1582175 = 2373263) B2373263
theorem B2368619 : Blo 1052612 2368619 := bstep (se 1 (by rfl) ⟨1776464, by rfl⟩ : syracuseStep 2368619 = 3552929) B3552929
theorem B9020555 : Blo 1052612 9020555 := bstep (se 1 (by rfl) ⟨6765416, by rfl⟩ : syracuseStep 9020555 = 13530833) B13530833
theorem B1582235 : Blo 1052612 1582235 := bstep (se 1 (by rfl) ⟨1186676, by rfl⟩ : syracuseStep 1582235 = 2373353) B2373353
theorem B3253459 : Blo 1052612 3253459 := bstep (se 1 (by rfl) ⟨2440094, by rfl⟩ : syracuseStep 3253459 = 4880189) B4880189
theorem B10823183 : Blo 1052612 10823183 := bstep (se 1 (by rfl) ⟨8117387, by rfl⟩ : syracuseStep 10823183 = 16234775) B16234775
theorem B1582697 : Blo 1052612 1582697 := bstep (se 2 (by rfl) ⟨593511, by rfl⟩ : syracuseStep 1582697 = 1187023) B1187023
theorem B1582823 : Blo 1052612 1582823 := bstep (se 1 (by rfl) ⟨1187117, by rfl⟩ : syracuseStep 1582823 = 2374235) B2374235
theorem B1582919 : Blo 1052612 1582919 := bstep (se 1 (by rfl) ⟨1187189, by rfl⟩ : syracuseStep 1582919 = 2374379) B2374379
theorem B2369519 : Blo 1052612 2369519 := bstep (se 1 (by rfl) ⟨1777139, by rfl⟩ : syracuseStep 2369519 = 3554279) B3554279
theorem B1583327 : Blo 1052612 1583327 := bstep (se 1 (by rfl) ⟨1187495, by rfl⟩ : syracuseStep 1583327 = 2374991) B2374991
theorem B1779995 : Blo 1052612 1779995 := bstep (se 1 (by rfl) ⟨1334996, by rfl⟩ : syracuseStep 1779995 = 2669993) B2669993
theorem B1583387 : Blo 1052612 1583387 := bstep (se 1 (by rfl) ⟨1187540, by rfl⟩ : syracuseStep 1583387 = 2375081) B2375081
theorem B1583519 : Blo 1052612 1583519 := bstep (se 1 (by rfl) ⟨1187639, by rfl⟩ : syracuseStep 1583519 = 2375279) B2375279
theorem B1583711 : Blo 1052612 1583711 := bstep (se 1 (by rfl) ⟨1187783, by rfl⟩ : syracuseStep 1583711 = 2375567) B2375567
theorem B2534303 : Blo 1052612 2534303 := bstep (se 1 (by rfl) ⟨1900727, by rfl⟩ : syracuseStep 2534303 = 3801455) B3801455
theorem B1584041 : Blo 1052612 1584041 := bstep (se 2 (by rfl) ⟨594015, by rfl⟩ : syracuseStep 1584041 = 1188031) B1188031
theorem B1584071 : Blo 1052612 1584071 := bstep (se 1 (by rfl) ⟨1188053, by rfl⟩ : syracuseStep 1584071 = 2376107) B2376107
theorem B1584191 : Blo 1052612 1584191 := bstep (se 1 (by rfl) ⟨1188143, by rfl⟩ : syracuseStep 1584191 = 2376287) B2376287
theorem B1584431 : Blo 1052612 1584431 := bstep (se 1 (by rfl) ⟨1188323, by rfl⟩ : syracuseStep 1584431 = 2376647) B2376647
theorem B2665811 : Blo 1052612 2665811 := bstep (se 1 (by rfl) ⟨1999358, by rfl⟩ : syracuseStep 2665811 = 3998717) B3998717
theorem B2370923 : Blo 1052612 2370923 := bstep (se 1 (by rfl) ⟨1778192, by rfl⟩ : syracuseStep 2370923 = 3556385) B3556385
theorem B1584617 : Blo 1052612 1584617 := bstep (se 2 (by rfl) ⟨594231, by rfl⟩ : syracuseStep 1584617 = 1188463) B1188463
theorem B1584671 : Blo 1052612 1584671 := bstep (se 1 (by rfl) ⟨1188503, by rfl⟩ : syracuseStep 1584671 = 2377007) B2377007
theorem B2371193 : Blo 1052612 2371193 := bstep (se 2 (by rfl) ⟨889197, by rfl⟩ : syracuseStep 2371193 = 1778395) B1778395
theorem B1584761 : Blo 1052612 1584761 := bstep (se 2 (by rfl) ⟨594285, by rfl⟩ : syracuseStep 1584761 = 1188571) B1188571
theorem B6008579 : Blo 1052612 6008579 := bstep (se 1 (by rfl) ⟨4506434, by rfl⟩ : syracuseStep 6008579 = 9012869) B9012869
theorem B2666459 : Blo 1052612 2666459 := bstep (se 1 (by rfl) ⟨1999844, by rfl⟩ : syracuseStep 2666459 = 3999689) B3999689
theorem B1781743 : Blo 1052612 1781743 := bstep (se 1 (by rfl) ⟨1336307, by rfl⟩ : syracuseStep 1781743 = 2672615) B2672615
theorem B6762649 : Blo 1052612 6762649 := bstep (se 2 (by rfl) ⟨2535993, by rfl⟩ : syracuseStep 6762649 = 5071987) B5071987
theorem B2666783 : Blo 1052612 2666783 := bstep (se 1 (by rfl) ⟨2000087, by rfl⟩ : syracuseStep 2666783 = 4000175) B4000175
theorem B1782479 : Blo 1052612 1782479 := bstep (se 1 (by rfl) ⟨1336859, by rfl⟩ : syracuseStep 1782479 = 2673719) B2673719
theorem B2372435 : Blo 1052612 2372435 := bstep (se 1 (by rfl) ⟨1779326, by rfl⟩ : syracuseStep 2372435 = 3558653) B3558653
theorem B2536609 : Blo 1052612 2536609 := bstep (se 2 (by rfl) ⟨951228, by rfl⟩ : syracuseStep 2536609 = 1902457) B1902457
theorem B2372795 : Blo 1052612 2372795 := bstep (se 1 (by rfl) ⟨1779596, by rfl⟩ : syracuseStep 2372795 = 3559193) B3559193
theorem B10958075 : Blo 1052612 10958075 := bstep (se 1 (by rfl) ⟨8218556, by rfl⟩ : syracuseStep 10958075 = 16437113) B16437113
theorem B2372921 : Blo 1052612 2372921 := bstep (se 2 (by rfl) ⟨889845, by rfl⟩ : syracuseStep 2372921 = 1779691) B1779691
theorem B2372975 : Blo 1052612 2372975 := bstep (se 1 (by rfl) ⟨1779731, by rfl⟩ : syracuseStep 2372975 = 3559463) B3559463
theorem B8664839 : Blo 1052612 8664839 := bstep (se 1 (by rfl) ⟨6498629, by rfl⟩ : syracuseStep 8664839 = 12997259) B12997259
theorem B2373623 : Blo 1052612 2373623 := bstep (se 1 (by rfl) ⟨1780217, by rfl⟩ : syracuseStep 2373623 = 3560435) B3560435
theorem B2373695 : Blo 1052612 2373695 := bstep (se 1 (by rfl) ⟨1780271, by rfl⟩ : syracuseStep 2373695 = 3560543) B3560543
theorem B2668727 : Blo 1052612 2668727 := bstep (se 1 (by rfl) ⟨2001545, by rfl⟩ : syracuseStep 2668727 = 4003091) B4003091
theorem B9615647 : Blo 1052612 9615647 := bstep (se 1 (by rfl) ⟨7211735, by rfl⟩ : syracuseStep 9615647 = 14423471) B14423471
theorem B3553631 : Blo 1052612 3553631 := bstep (se 1 (by rfl) ⟨2665223, by rfl⟩ : syracuseStep 3553631 = 5330447) B5330447
theorem B2373983 : Blo 1052612 2373983 := bstep (se 1 (by rfl) ⟨1780487, by rfl⟩ : syracuseStep 2373983 = 3560975) B3560975
theorem B9025991 : Blo 1052612 9025991 := bstep (se 1 (by rfl) ⟨6769493, by rfl⟩ : syracuseStep 9025991 = 13538987) B13538987
theorem B3554171 : Blo 1052612 3554171 := bstep (se 1 (by rfl) ⟨2665628, by rfl⟩ : syracuseStep 3554171 = 5331257) B5331257
theorem B2702203 : Blo 1052612 2702203 := bstep (se 1 (by rfl) ⟨2026652, by rfl⟩ : syracuseStep 2702203 = 4053305) B4053305
theorem B2374523 : Blo 1052612 2374523 := bstep (se 1 (by rfl) ⟨1780892, by rfl⟩ : syracuseStep 2374523 = 3561785) B3561785
theorem B1686511 : Blo 1052612 1686511 := bstep (se 1 (by rfl) ⟨1264883, by rfl⟩ : syracuseStep 1686511 = 2529767) B2529767
theorem B2374703 : Blo 1052612 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B10141051 : Blo 1052612 10141051 := bstep (se 1 (by rfl) ⟨7605788, by rfl⟩ : syracuseStep 10141051 = 15211577) B15211577
theorem B3653039 : Blo 1052612 3653039 := bstep (se 1 (by rfl) ⟨2739779, by rfl⟩ : syracuseStep 3653039 = 5479559) B5479559
theorem B6766031 : Blo 1052612 6766031 := bstep (se 1 (by rfl) ⟨5074523, by rfl⟩ : syracuseStep 6766031 = 10149047) B10149047
theorem B17350139 : Blo 1052612 17350139 := bstep (se 1 (by rfl) ⟨13012604, by rfl⟩ : syracuseStep 17350139 = 26025209) B26025209
theorem B92520305 : Blo 1052612 92520305 := bstep (se 2 (by rfl) ⟨34695114, by rfl⟩ : syracuseStep 92520305 = 69390229) B69390229
theorem B6078995 : Blo 1052612 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B2933279 : Blo 1052612 2933279 := bstep (se 1 (by rfl) ⟨2199959, by rfl⟩ : syracuseStep 2933279 = 4399919) B4399919
theorem B3425111 : Blo 1052612 3425111 := bstep (se 1 (by rfl) ⟨2568833, by rfl⟩ : syracuseStep 3425111 = 5137667) B5137667
theorem B18236573 : Blo 1052612 18236573 := bstep (se 3 (by rfl) ⟨3419357, by rfl⟩ : syracuseStep 18236573 = 6838715) B6838715
theorem B6014159 : Blo 1052612 6014159 := bstep (se 1 (by rfl) ⟨4510619, by rfl⟩ : syracuseStep 6014159 = 9021239) B9021239
theorem B3556655 : Blo 1052612 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B2672423 : Blo 1052612 2672423 := bstep (se 1 (by rfl) ⟨2004317, by rfl⟩ : syracuseStep 2672423 = 4008635) B4008635
theorem B6015617 : Blo 1052612 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B3558113 : Blo 1052612 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B7589011 : Blo 1052612 7589011 := bstep (se 1 (by rfl) ⟨5691758, by rfl⟩ : syracuseStep 7589011 = 11383517) B11383517
theorem B1265383 : Blo 1052612 1265383 := bstep (se 1 (by rfl) ⟨949037, by rfl⟩ : syracuseStep 1265383 = 1898075) B1898075
theorem B8998685 : Blo 1052612 8998685 := bstep (se 3 (by rfl) ⟨1687253, by rfl⟩ : syracuseStep 8998685 = 3374507) B3374507
theorem B6836729 : Blo 1052612 6836729 := bstep (se 2 (by rfl) ⟨2563773, by rfl⟩ : syracuseStep 6836729 = 5127547) B5127547
theorem B3003389 : Blo 1052612 3003389 := bstep (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) B1126271
theorem B2250031 : Blo 1052612 2250031 := bstep (se 1 (by rfl) ⟨1687523, by rfl⟩ : syracuseStep 2250031 = 3375047) B3375047
theorem B3004073 : Blo 1052612 3004073 := bstep (se 2 (by rfl) ⟨1126527, by rfl⟩ : syracuseStep 3004073 = 2253055) B2253055
theorem B1201855 : Blo 1052612 1201855 := bstep (se 1 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 1201855 = 1802783) B1802783
theorem B2709215 : Blo 1052612 2709215 := bstep (se 1 (by rfl) ⟨2031911, by rfl⟩ : syracuseStep 2709215 = 4063823) B4063823
theorem B3004199 : Blo 1052612 3004199 := bstep (se 1 (by rfl) ⟨2253149, by rfl⟩ : syracuseStep 3004199 = 4506299) B4506299
theorem B5330771 : Blo 1052612 5330771 := bstep (se 1 (by rfl) ⟨3998078, by rfl⟩ : syracuseStep 5330771 = 7996157) B7996157
theorem B11393075 : Blo 1052612 11393075 := bstep (se 1 (by rfl) ⟨8544806, by rfl⟩ : syracuseStep 11393075 = 17089613) B17089613
theorem B2054335 : Blo 1052612 2054335 := bstep (se 1 (by rfl) ⟨1540751, by rfl⟩ : syracuseStep 2054335 = 3081503) B3081503
theorem B3660059 : Blo 1052612 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B5331905 : Blo 1052612 5331905 := bstep (se 2 (by rfl) ⟨1999464, by rfl⟩ : syracuseStep 5331905 = 3998929) B3998929
theorem B3005531 : Blo 1052612 3005531 := bstep (se 1 (by rfl) ⟨2254148, by rfl⟩ : syracuseStep 3005531 = 4508297) B4508297
theorem B3006305 : Blo 1052612 3006305 := bstep (se 2 (by rfl) ⟨1127364, by rfl⟩ : syracuseStep 3006305 = 2254729) B2254729
theorem B25649297 : Blo 1052612 25649297 := bstep (se 2 (by rfl) ⟨9618486, by rfl⟩ : syracuseStep 25649297 = 19236973) B19236973
theorem B3564539 : Blo 1052612 3564539 := bstep (se 1 (by rfl) ⟨2673404, by rfl⟩ : syracuseStep 3564539 = 5346809) B5346809
theorem B3564647 : Blo 1052612 3564647 := bstep (se 1 (by rfl) ⟨2673485, by rfl⟩ : syracuseStep 3564647 = 5346971) B5346971
theorem B3007763 : Blo 1052612 3007763 := bstep (se 1 (by rfl) ⟨2255822, by rfl⟩ : syracuseStep 3007763 = 4511645) B4511645
theorem B11396663 : Blo 1052612 11396663 := bstep (se 1 (by rfl) ⟨8547497, by rfl⟩ : syracuseStep 11396663 = 17094995) B17094995
theorem B2746271 : Blo 1052612 2746271 := bstep (se 1 (by rfl) ⟨2059703, by rfl⟩ : syracuseStep 2746271 = 4119407) B4119407
theorem B5859287 : Blo 1052612 5859287 := bstep (se 1 (by rfl) ⟨4394465, by rfl⟩ : syracuseStep 5859287 = 8788931) B8788931
theorem B8579081 : Blo 1052612 8579081 := bstep (se 2 (by rfl) ⟨3217155, by rfl⟩ : syracuseStep 8579081 = 6434311) B6434311
theorem B5335145 : Blo 1052612 5335145 := bstep (se 2 (by rfl) ⟨2000679, by rfl⟩ : syracuseStep 5335145 = 4001359) B4001359
theorem B18016505 : Blo 1052612 18016505 := bstep (se 2 (by rfl) ⟨6756189, by rfl⟩ : syracuseStep 18016505 = 13512379) B13512379
theorem B3565943 : Blo 1052612 3565943 := bstep (se 1 (by rfl) ⟨2674457, by rfl⟩ : syracuseStep 3565943 = 5348915) B5348915
theorem B34204133 : Blo 1052612 34204133 := bstep (se 4 (by rfl) ⟨3206637, by rfl⟩ : syracuseStep 34204133 = 6413275) B6413275
theorem B5402011 : Blo 1052612 5402011 := bstep (se 1 (by rfl) ⟨4051508, by rfl⟩ : syracuseStep 5402011 = 8103017) B8103017
theorem B2846107 : Blo 1052612 2846107 := bstep (se 1 (by rfl) ⟨2134580, by rfl⟩ : syracuseStep 2846107 = 4269161) B4269161
theorem B5337737 : Blo 1052612 5337737 := bstep (se 2 (by rfl) ⟨2001651, by rfl⟩ : syracuseStep 5337737 = 4003303) B4003303
theorem B6419503 : Blo 1052612 6419503 := bstep (se 1 (by rfl) ⟨4814627, by rfl⟩ : syracuseStep 6419503 = 9629255) B9629255
theorem B1504423 : Blo 1052612 1504423 := bstep (se 1 (by rfl) ⟨1128317, by rfl⟩ : syracuseStep 1504423 = 2256635) B2256635
theorem B6747785 : Blo 1052612 6747785 := bstep (se 2 (by rfl) ⟨2530419, by rfl⟩ : syracuseStep 6747785 = 5060839) B5060839
theorem B5404967 : Blo 1052612 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B12155483 : Blo 1052612 12155483 := bstep (se 1 (by rfl) ⟨9116612, by rfl⟩ : syracuseStep 12155483 = 18233225) B18233225
theorem B1899487 : Blo 1052612 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B27720893 : Blo 1052612 27720893 := bstep (se 3 (by rfl) ⟨5197667, by rfl⟩ : syracuseStep 27720893 = 10395335) B10395335
theorem B3997471 : Blo 1052612 3997471 := bstep (se 1 (by rfl) ⟨2998103, by rfl⟩ : syracuseStep 3997471 = 5996207) B5996207
theorem B5341139 : Blo 1052612 5341139 := bstep (se 1 (by rfl) ⟨4005854, by rfl⟩ : syracuseStep 5341139 = 8011709) B8011709
theorem B61669475 : Blo 1052612 61669475 := bstep (se 1 (by rfl) ⟨46252106, by rfl⟩ : syracuseStep 61669475 = 92504213) B92504213
theorem B6750859 : Blo 1052612 6750859 := bstep (se 1 (by rfl) ⟨5063144, by rfl⟩ : syracuseStep 6750859 = 10126289) B10126289
theorem B12157715 : Blo 1052612 12157715 := bstep (se 1 (by rfl) ⟨9118286, by rfl⟩ : syracuseStep 12157715 = 18236573) B18236573
theorem B3801887 : Blo 1052612 3801887 := bstep (se 1 (by rfl) ⟨2851415, by rfl⟩ : syracuseStep 3801887 = 5702831) B5702831
theorem B3802145 : Blo 1052612 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B5999123 : Blo 1052612 5999123 := bstep (se 1 (by rfl) ⟨4499342, by rfl⟩ : syracuseStep 5999123 = 8998685) B8998685
theorem B2002259 : Blo 1052612 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B6753935 : Blo 1052612 6753935 := bstep (se 1 (by rfl) ⟨5065451, by rfl⟩ : syracuseStep 6753935 = 10130903) B10130903
theorem B2002715 : Blo 1052612 2002715 := bstep (se 1 (by rfl) ⟨1502036, by rfl⟩ : syracuseStep 2002715 = 3004073) B3004073
theorem B1806143 : Blo 1052612 1806143 := bstep (se 1 (by rfl) ⟨1354607, by rfl⟩ : syracuseStep 1806143 = 2709215) B2709215
theorem B2002799 : Blo 1052612 2002799 := bstep (se 1 (by rfl) ⟨1502099, by rfl⟩ : syracuseStep 2002799 = 3004199) B3004199
theorem B5705599 : Blo 1052612 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B1052895 : Blo 1052612 1052895 := bstep (se 1 (by rfl) ⟨789671, by rfl⟩ : syracuseStep 1052895 = 1579343) B1579343
theorem B1052911 : Blo 1052612 1052911 := bstep (se 1 (by rfl) ⟨789683, by rfl⟩ : syracuseStep 1052911 = 1579367) B1579367
theorem B1052955 : Blo 1052612 1052955 := bstep (se 1 (by rfl) ⟨789716, by rfl⟩ : syracuseStep 1052955 = 1579433) B1579433
theorem B19272005 : Blo 1052612 19272005 := bstep (se 4 (by rfl) ⟨1806750, by rfl⟩ : syracuseStep 19272005 = 3613501) B3613501
theorem B1053211 : Blo 1052612 1053211 := bstep (se 1 (by rfl) ⟨789908, by rfl⟩ : syracuseStep 1053211 = 1579817) B1579817
theorem B1053351 : Blo 1052612 1053351 := bstep (se 1 (by rfl) ⟨790013, by rfl⟩ : syracuseStep 1053351 = 1580027) B1580027
theorem B1053375 : Blo 1052612 1053375 := bstep (se 1 (by rfl) ⟨790031, by rfl⟩ : syracuseStep 1053375 = 1580063) B1580063
theorem B1053391 : Blo 1052612 1053391 := bstep (se 1 (by rfl) ⟨790043, by rfl⟩ : syracuseStep 1053391 = 1580087) B1580087
theorem B2003687 : Blo 1052612 2003687 := bstep (se 1 (by rfl) ⟨1502765, by rfl⟩ : syracuseStep 2003687 = 3005531) B3005531
theorem B1053471 : Blo 1052612 1053471 := bstep (se 1 (by rfl) ⟨790103, by rfl⟩ : syracuseStep 1053471 = 1580207) B1580207
theorem B1053567 : Blo 1052612 1053567 := bstep (se 1 (by rfl) ⟨790175, by rfl⟩ : syracuseStep 1053567 = 1580351) B1580351
theorem B1053663 : Blo 1052612 1053663 := bstep (se 1 (by rfl) ⟨790247, by rfl⟩ : syracuseStep 1053663 = 1580495) B1580495
theorem B4002803 : Blo 1052612 4002803 := bstep (se 1 (by rfl) ⟨3002102, by rfl⟩ : syracuseStep 4002803 = 6004205) B6004205
theorem B1053919 : Blo 1052612 1053919 := bstep (se 1 (by rfl) ⟨790439, by rfl⟩ : syracuseStep 1053919 = 1580879) B1580879
theorem B2004203 : Blo 1052612 2004203 := bstep (se 1 (by rfl) ⟨1503152, by rfl⟩ : syracuseStep 2004203 = 3006305) B3006305
theorem B1053951 : Blo 1052612 1053951 := bstep (se 1 (by rfl) ⟨790463, by rfl⟩ : syracuseStep 1053951 = 1580927) B1580927
theorem B1053999 : Blo 1052612 1053999 := bstep (se 1 (by rfl) ⟨790499, by rfl⟩ : syracuseStep 1053999 = 1580999) B1580999
theorem B22877549 : Blo 1052612 22877549 := bstep (se 3 (by rfl) ⟨4289540, by rfl⟩ : syracuseStep 22877549 = 8579081) B8579081
theorem B1054159 : Blo 1052612 1054159 := bstep (se 1 (by rfl) ⟨790619, by rfl⟩ : syracuseStep 1054159 = 1581239) B1581239
theorem B1054239 : Blo 1052612 1054239 := bstep (se 1 (by rfl) ⟨790679, by rfl⟩ : syracuseStep 1054239 = 1581359) B1581359
theorem B9016865 : Blo 1052612 9016865 := bstep (se 2 (by rfl) ⟨3381324, by rfl⟩ : syracuseStep 9016865 = 6762649) B6762649
theorem B1054399 : Blo 1052612 1054399 := bstep (se 1 (by rfl) ⟨790799, by rfl⟩ : syracuseStep 1054399 = 1581599) B1581599
theorem B1185511 : Blo 1052612 1185511 := bstep (se 1 (by rfl) ⟨889133, by rfl⟩ : syracuseStep 1185511 = 1778267) B1778267
theorem B1054439 : Blo 1052612 1054439 := bstep (se 1 (by rfl) ⟨790829, by rfl⟩ : syracuseStep 1054439 = 1581659) B1581659
theorem B7608329 : Blo 1052612 7608329 := bstep (se 2 (by rfl) ⟨2853123, by rfl⟩ : syracuseStep 7608329 = 5706247) B5706247
theorem B1054783 : Blo 1052612 1054783 := bstep (se 1 (by rfl) ⟨791087, by rfl⟩ : syracuseStep 1054783 = 1582175) B1582175
theorem B1579079 : Blo 1052612 1579079 := bstep (se 1 (by rfl) ⟨1184309, by rfl⟩ : syracuseStep 1579079 = 2368619) B2368619
theorem B1054823 : Blo 1052612 1054823 := bstep (se 1 (by rfl) ⟨791117, by rfl⟩ : syracuseStep 1054823 = 1582235) B1582235
theorem B2005175 : Blo 1052612 2005175 := bstep (se 1 (by rfl) ⟨1503881, by rfl⟩ : syracuseStep 2005175 = 3007763) B3007763
theorem B7215455 : Blo 1052612 7215455 := bstep (se 1 (by rfl) ⟨5411591, by rfl⟩ : syracuseStep 7215455 = 10823183) B10823183
theorem B1055131 : Blo 1052612 1055131 := bstep (se 1 (by rfl) ⟨791348, by rfl⟩ : syracuseStep 1055131 = 1582697) B1582697
theorem B1055215 : Blo 1052612 1055215 := bstep (se 1 (by rfl) ⟨791411, by rfl⟩ : syracuseStep 1055215 = 1582823) B1582823
theorem B1055279 : Blo 1052612 1055279 := bstep (se 1 (by rfl) ⟨791459, by rfl⟩ : syracuseStep 1055279 = 1582919) B1582919
theorem B3906191 : Blo 1052612 3906191 := bstep (se 1 (by rfl) ⟨2929643, by rfl⟩ : syracuseStep 3906191 = 5859287) B5859287
theorem B1579679 : Blo 1052612 1579679 := bstep (se 1 (by rfl) ⟨1184759, by rfl⟩ : syracuseStep 1579679 = 2369519) B2369519
theorem B1055551 : Blo 1052612 1055551 := bstep (se 1 (by rfl) ⟨791663, by rfl⟩ : syracuseStep 1055551 = 1583327) B1583327
theorem B1186663 : Blo 1052612 1186663 := bstep (se 1 (by rfl) ⟨889997, by rfl⟩ : syracuseStep 1186663 = 1779995) B1779995
theorem B1055591 : Blo 1052612 1055591 := bstep (se 1 (by rfl) ⟨791693, by rfl⟩ : syracuseStep 1055591 = 1583387) B1583387
theorem B3382145 : Blo 1052612 3382145 := bstep (se 2 (by rfl) ⟨1268304, by rfl⟩ : syracuseStep 3382145 = 2536609) B2536609
theorem B2005897 : Blo 1052612 2005897 := bstep (se 2 (by rfl) ⟨752211, by rfl⟩ : syracuseStep 2005897 = 1504423) B1504423
theorem B1055679 : Blo 1052612 1055679 := bstep (se 1 (by rfl) ⟨791759, by rfl⟩ : syracuseStep 1055679 = 1583519) B1583519
theorem B1055807 : Blo 1052612 1055807 := bstep (se 1 (by rfl) ⟨791855, by rfl⟩ : syracuseStep 1055807 = 1583711) B1583711
theorem B1056027 : Blo 1052612 1056027 := bstep (se 1 (by rfl) ⟨792020, by rfl⟩ : syracuseStep 1056027 = 1584041) B1584041
theorem B1056047 : Blo 1052612 1056047 := bstep (se 1 (by rfl) ⟨792035, by rfl⟩ : syracuseStep 1056047 = 1584071) B1584071
theorem B1056127 : Blo 1052612 1056127 := bstep (se 1 (by rfl) ⟨792095, by rfl⟩ : syracuseStep 1056127 = 1584191) B1584191
theorem B15179237 : Blo 1052612 15179237 := bstep (se 4 (by rfl) ⟨1423053, by rfl⟩ : syracuseStep 15179237 = 2846107) B2846107
theorem B1056287 : Blo 1052612 1056287 := bstep (se 1 (by rfl) ⟨792215, by rfl⟩ : syracuseStep 1056287 = 1584431) B1584431
theorem B1777207 : Blo 1052612 1777207 := bstep (se 1 (by rfl) ⟨1332905, by rfl⟩ : syracuseStep 1777207 = 2665811) B2665811
theorem B1580615 : Blo 1052612 1580615 := bstep (se 1 (by rfl) ⟨1185461, by rfl⟩ : syracuseStep 1580615 = 2370923) B2370923
theorem B1056411 : Blo 1052612 1056411 := bstep (se 1 (by rfl) ⟨792308, by rfl⟩ : syracuseStep 1056411 = 1584617) B1584617
theorem B1056447 : Blo 1052612 1056447 := bstep (se 1 (by rfl) ⟨792335, by rfl⟩ : syracuseStep 1056447 = 1584671) B1584671
theorem B1580795 : Blo 1052612 1580795 := bstep (se 1 (by rfl) ⟨1185596, by rfl⟩ : syracuseStep 1580795 = 2371193) B2371193
theorem B1056507 : Blo 1052612 1056507 := bstep (se 1 (by rfl) ⟨792380, by rfl⟩ : syracuseStep 1056507 = 1584761) B1584761
theorem B4005719 : Blo 1052612 4005719 := bstep (se 1 (by rfl) ⟨3004289, by rfl⟩ : syracuseStep 4005719 = 6008579) B6008579
theorem B57646997 : Blo 1052612 57646997 := bstep (se 6 (by rfl) ⟨1351101, by rfl⟩ : syracuseStep 57646997 = 2702203) B2702203
theorem B1777639 : Blo 1052612 1777639 := bstep (se 1 (by rfl) ⟨1333229, by rfl⟩ : syracuseStep 1777639 = 2666459) B2666459
theorem B1777855 : Blo 1052612 1777855 := bstep (se 1 (by rfl) ⟨1333391, by rfl⟩ : syracuseStep 1777855 = 2666783) B2666783
theorem B1188319 : Blo 1052612 1188319 := bstep (se 1 (by rfl) ⟨891239, by rfl⟩ : syracuseStep 1188319 = 1782479) B1782479
theorem B1581623 : Blo 1052612 1581623 := bstep (se 1 (by rfl) ⟨1186217, by rfl⟩ : syracuseStep 1581623 = 2372435) B2372435
theorem B1581863 : Blo 1052612 1581863 := bstep (se 1 (by rfl) ⟨1186397, by rfl⟩ : syracuseStep 1581863 = 2372795) B2372795
theorem B1581947 : Blo 1052612 1581947 := bstep (se 1 (by rfl) ⟨1186460, by rfl⟩ : syracuseStep 1581947 = 2372921) B2372921
theorem B1581983 : Blo 1052612 1581983 := bstep (se 1 (by rfl) ⟨1186487, by rfl⟩ : syracuseStep 1581983 = 2372975) B2372975
theorem B1582073 : Blo 1052612 1582073 := bstep (se 2 (by rfl) ⟨593277, by rfl⟩ : syracuseStep 1582073 = 1186555) B1186555
theorem B4498523 : Blo 1052612 4498523 := bstep (se 1 (by rfl) ⟨3373892, by rfl⟩ : syracuseStep 4498523 = 6747785) B6747785
theorem B2368673 : Blo 1052612 2368673 := bstep (se 2 (by rfl) ⟨888252, by rfl⟩ : syracuseStep 2368673 = 1776505) B1776505
theorem B5776559 : Blo 1052612 5776559 := bstep (se 1 (by rfl) ⟨4332419, by rfl⟩ : syracuseStep 5776559 = 8664839) B8664839
theorem B2532649 : Blo 1052612 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B1582415 : Blo 1052612 1582415 := bstep (se 1 (by rfl) ⟨1186811, by rfl⟩ : syracuseStep 1582415 = 2373623) B2373623
theorem B1582463 : Blo 1052612 1582463 := bstep (se 1 (by rfl) ⟨1186847, by rfl⟩ : syracuseStep 1582463 = 2373695) B2373695
theorem B1779151 : Blo 1052612 1779151 := bstep (se 1 (by rfl) ⟨1334363, by rfl⟩ : syracuseStep 1779151 = 2668727) B2668727
theorem B2369087 : Blo 1052612 2369087 := bstep (se 1 (by rfl) ⟨1776815, by rfl⟩ : syracuseStep 2369087 = 3553631) B3553631
theorem B1582655 : Blo 1052612 1582655 := bstep (se 1 (by rfl) ⟨1186991, by rfl⟩ : syracuseStep 1582655 = 2373983) B2373983
theorem B8103655 : Blo 1052612 8103655 := bstep (se 1 (by rfl) ⟨6077741, by rfl⟩ : syracuseStep 8103655 = 12155483) B12155483
theorem B2369447 : Blo 1052612 2369447 := bstep (se 1 (by rfl) ⟨1777085, by rfl⟩ : syracuseStep 2369447 = 3554171) B3554171
theorem B1583015 : Blo 1052612 1583015 := bstep (se 1 (by rfl) ⟨1187261, by rfl⟩ : syracuseStep 1583015 = 2374523) B2374523
theorem B1583135 : Blo 1052612 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B7612537 : Blo 1052612 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B2435359 : Blo 1052612 2435359 := bstep (se 1 (by rfl) ⟨1826519, by rfl⟩ : syracuseStep 2435359 = 3653039) B3653039
theorem B61680203 : Blo 1052612 61680203 := bstep (se 1 (by rfl) ⟨46260152, by rfl⟩ : syracuseStep 61680203 = 92520305) B92520305
theorem B1583993 : Blo 1052612 1583993 := bstep (se 2 (by rfl) ⟨593997, by rfl⟩ : syracuseStep 1583993 = 1187995) B1187995
theorem B6007871 : Blo 1052612 6007871 := bstep (se 1 (by rfl) ⟨4505903, by rfl⟩ : syracuseStep 6007871 = 9011807) B9011807
theorem B4009439 : Blo 1052612 4009439 := bstep (se 1 (by rfl) ⟨3007079, by rfl⟩ : syracuseStep 4009439 = 6014159) B6014159
theorem B2371049 : Blo 1052612 2371049 := bstep (se 2 (by rfl) ⟨889143, by rfl⟩ : syracuseStep 2371049 = 1778287) B1778287
theorem B2371103 : Blo 1052612 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B1781615 : Blo 1052612 1781615 := bstep (se 1 (by rfl) ⟨1336211, by rfl⟩ : syracuseStep 1781615 = 2672423) B2672423
theorem B18231277 : Blo 1052612 18231277 := bstep (se 3 (by rfl) ⟨3418364, by rfl⟩ : syracuseStep 18231277 = 6836729) B6836729
theorem B2666591 : Blo 1052612 2666591 := bstep (se 1 (by rfl) ⟨1999943, by rfl⟩ : syracuseStep 2666591 = 3999887) B3999887
theorem B4337945 : Blo 1052612 4337945 := bstep (se 2 (by rfl) ⟨1626729, by rfl⟩ : syracuseStep 4337945 = 3253459) B3253459
theorem B92385623 : Blo 1052612 92385623 := bstep (se 1 (by rfl) ⟨69289217, by rfl⟩ : syracuseStep 92385623 = 138578435) B138578435
theorem B4010411 : Blo 1052612 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B2372075 : Blo 1052612 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B40546979 : Blo 1052612 40546979 := bstep (se 1 (by rfl) ⟨30410234, by rfl⟩ : syracuseStep 40546979 = 60820469) B60820469
theorem B2667887 : Blo 1052612 2667887 := bstep (se 1 (by rfl) ⟨2000915, by rfl⟩ : syracuseStep 2667887 = 4001831) B4001831
theorem B3553847 : Blo 1052612 3553847 := bstep (se 1 (by rfl) ⟨2665385, by rfl⟩ : syracuseStep 3553847 = 5330771) B5330771
theorem B10402451 : Blo 1052612 10402451 := bstep (se 1 (by rfl) ⟨7801838, by rfl⟩ : syracuseStep 10402451 = 15603677) B15603677
theorem B2440039 : Blo 1052612 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B4504673 : Blo 1052612 4504673 := bstep (se 2 (by rfl) ⟨1689252, by rfl⟩ : syracuseStep 4504673 = 3378505) B3378505
theorem B3554603 : Blo 1052612 3554603 := bstep (se 1 (by rfl) ⟨2665952, by rfl⟩ : syracuseStep 3554603 = 5331905) B5331905
theorem B1687177 : Blo 1052612 1687177 := bstep (se 2 (by rfl) ⟨632691, by rfl⟩ : syracuseStep 1687177 = 1265383) B1265383
theorem B2375657 : Blo 1052612 2375657 := bstep (se 2 (by rfl) ⟨890871, by rfl⟩ : syracuseStep 2375657 = 1781743) B1781743
theorem B2376359 : Blo 1052612 2376359 := bstep (se 1 (by rfl) ⟨1782269, by rfl⟩ : syracuseStep 2376359 = 3564539) B3564539
theorem B2376431 : Blo 1052612 2376431 := bstep (se 1 (by rfl) ⟨1782323, by rfl⟩ : syracuseStep 2376431 = 3564647) B3564647
theorem B6013703 : Blo 1052612 6013703 := bstep (se 1 (by rfl) ⟨4510277, by rfl⟩ : syracuseStep 6013703 = 9020555) B9020555
theorem B3556763 : Blo 1052612 3556763 := bstep (se 1 (by rfl) ⟨2667572, by rfl⟩ : syracuseStep 3556763 = 5335145) B5335145
theorem B12011003 : Blo 1052612 12011003 := bstep (se 1 (by rfl) ⟨9008252, by rfl⟩ : syracuseStep 12011003 = 18016505) B18016505
theorem B2377295 : Blo 1052612 2377295 := bstep (se 1 (by rfl) ⟨1782971, by rfl⟩ : syracuseStep 2377295 = 3565943) B3565943
theorem B3000041 : Blo 1052612 3000041 := bstep (se 2 (by rfl) ⟨1125015, by rfl⟩ : syracuseStep 3000041 = 2250031) B2250031
theorem B1689535 : Blo 1052612 1689535 := bstep (se 1 (by rfl) ⟨1267151, by rfl⟩ : syracuseStep 1689535 = 2534303) B2534303
theorem B2739113 : Blo 1052612 2739113 := bstep (se 2 (by rfl) ⟨1027167, by rfl⟩ : syracuseStep 2739113 = 2054335) B2054335
theorem B3558491 : Blo 1052612 3558491 := bstep (se 1 (by rfl) ⟨2668868, by rfl⟩ : syracuseStep 3558491 = 5337737) B5337737
theorem B2673769 : Blo 1052612 2673769 := bstep (se 2 (by rfl) ⟨1002663, by rfl⟩ : syracuseStep 2673769 = 2005327) B2005327
theorem B18042749 : Blo 1052612 18042749 := bstep (se 3 (by rfl) ⟨3383015, by rfl⟩ : syracuseStep 18042749 = 6766031) B6766031
theorem B2248681 : Blo 1052612 2248681 := bstep (se 2 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 2248681 = 1686511) B1686511
theorem B6410431 : Blo 1052612 6410431 := bstep (se 1 (by rfl) ⟨4807823, by rfl⟩ : syracuseStep 6410431 = 9615647) B9615647
theorem B6017327 : Blo 1052612 6017327 := bstep (se 1 (by rfl) ⟨4512995, by rfl⟩ : syracuseStep 6017327 = 9025991) B9025991
theorem B13521401 : Blo 1052612 13521401 := bstep (se 2 (by rfl) ⟨5070525, by rfl⟩ : syracuseStep 13521401 = 10141051) B10141051
theorem B4510313 : Blo 1052612 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B5329961 : Blo 1052612 5329961 := bstep (se 2 (by rfl) ⟨1998735, by rfl⟩ : syracuseStep 5329961 = 3997471) B3997471
theorem B3560759 : Blo 1052612 3560759 := bstep (se 1 (by rfl) ⟨2670569, by rfl⟩ : syracuseStep 3560759 = 5341139) B5341139
theorem B4052663 : Blo 1052612 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B1955519 : Blo 1052612 1955519 := bstep (se 1 (by rfl) ⟨1466639, by rfl⟩ : syracuseStep 1955519 = 2933279) B2933279
theorem B3561299 : Blo 1052612 3561299 := bstep (se 1 (by rfl) ⟨2670974, by rfl⟩ : syracuseStep 3561299 = 5341949) B5341949
theorem B2283407 : Blo 1052612 2283407 := bstep (se 1 (by rfl) ⟨1712555, by rfl⟩ : syracuseStep 2283407 = 3425111) B3425111
theorem B2250919 : Blo 1052612 2250919 := bstep (se 1 (by rfl) ⟨1688189, by rfl⟩ : syracuseStep 2250919 = 3376379) B3376379
theorem B3562703 : Blo 1052612 3562703 := bstep (se 1 (by rfl) ⟨2672027, by rfl⟩ : syracuseStep 3562703 = 5344055) B5344055
theorem B5332391 : Blo 1052612 5332391 := bstep (se 1 (by rfl) ⟨3999293, by rfl⟩ : syracuseStep 5332391 = 7998587) B7998587
theorem B1269227 : Blo 1052612 1269227 := bstep (se 1 (by rfl) ⟨951920, by rfl⟩ : syracuseStep 1269227 = 1903841) B1903841
theorem B7595383 : Blo 1052612 7595383 := bstep (se 1 (by rfl) ⟨5696537, by rfl⟩ : syracuseStep 7595383 = 11393075) B11393075
theorem B5334497 : Blo 1052612 5334497 := bstep (se 2 (by rfl) ⟨2000436, by rfl⟩ : syracuseStep 5334497 = 4000873) B4000873
theorem B10118681 : Blo 1052612 10118681 := bstep (se 2 (by rfl) ⟨3794505, by rfl⟩ : syracuseStep 10118681 = 7589011) B7589011
theorem B1337087 : Blo 1052612 1337087 := bstep (se 1 (by rfl) ⟨1002815, by rfl⟩ : syracuseStep 1337087 = 2005631) B2005631
theorem B3565403 : Blo 1052612 3565403 := bstep (se 1 (by rfl) ⟨2674052, by rfl⟩ : syracuseStep 3565403 = 5348105) B5348105
theorem B7202681 : Blo 1052612 7202681 := bstep (se 2 (by rfl) ⟨2701005, by rfl⟩ : syracuseStep 7202681 = 5402011) B5402011
theorem B8021915 : Blo 1052612 8021915 := bstep (se 1 (by rfl) ⟨6016436, by rfl⟩ : syracuseStep 8021915 = 12032873) B12032873
theorem B17099531 : Blo 1052612 17099531 := bstep (se 1 (by rfl) ⟨12824648, by rfl⟩ : syracuseStep 17099531 = 25649297) B25649297
theorem B34237349 : Blo 1052612 34237349 := bstep (se 4 (by rfl) ⟨3209751, by rfl⟩ : syracuseStep 34237349 = 6419503) B6419503
theorem B5073833 : Blo 1052612 5073833 := bstep (se 2 (by rfl) ⟨1902687, by rfl⟩ : syracuseStep 5073833 = 3805375) B3805375
theorem B7597775 : Blo 1052612 7597775 := bstep (se 1 (by rfl) ⟨5698331, by rfl⟩ : syracuseStep 7597775 = 11396663) B11396663
theorem B1830847 : Blo 1052612 1830847 := bstep (se 1 (by rfl) ⟨1373135, by rfl⟩ : syracuseStep 1830847 = 2746271) B2746271
theorem B22802755 : Blo 1052612 22802755 := bstep (se 1 (by rfl) ⟨17102066, by rfl⟩ : syracuseStep 22802755 = 34204133) B34204133
theorem B1602473 : Blo 1052612 1602473 := bstep (se 2 (by rfl) ⟨600927, by rfl⟩ : syracuseStep 1602473 = 1201855) B1201855
theorem B10843129 : Blo 1052612 10843129 := bstep (se 2 (by rfl) ⟨4066173, by rfl⟩ : syracuseStep 10843129 = 8132347) B8132347
theorem B7305383 : Blo 1052612 7305383 := bstep (se 1 (by rfl) ⟨5479037, by rfl⟩ : syracuseStep 7305383 = 10958075) B10958075
theorem B3603311 : Blo 1052612 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B342817757 : Blo 1052612 342817757 := bstep (se 3 (by rfl) ⟨64278329, by rfl⟩ : syracuseStep 342817757 = 128556659) B128556659
theorem B18480595 : Blo 1052612 18480595 := bstep (se 1 (by rfl) ⟨13860446, by rfl⟩ : syracuseStep 18480595 = 27720893) B27720893
theorem B11566759 : Blo 1052612 11566759 := bstep (se 1 (by rfl) ⟨8675069, by rfl⟩ : syracuseStep 11566759 = 17350139) B17350139
theorem B2000027 : Blo 1052612 2000027 := bstep (se 1 (by rfl) ⟨1500020, by rfl⟩ : syracuseStep 2000027 = 3000041) B3000041
theorem B3999415 : Blo 1052612 3999415 := bstep (se 1 (by rfl) ⟨2999561, by rfl⟩ : syracuseStep 3999415 = 5999123) B5999123
theorem B3376865 : Blo 1052612 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B10127177 : Blo 1052612 10127177 := bstep (se 2 (by rfl) ⟨3797691, by rfl⟩ : syracuseStep 10127177 = 7595383) B7595383
theorem B12028499 : Blo 1052612 12028499 := bstep (se 1 (by rfl) ⟨9021374, by rfl⟩ : syracuseStep 12028499 = 18042749) B18042749
theorem B12848003 : Blo 1052612 12848003 := bstep (se 1 (by rfl) ⟨9636002, by rfl⟩ : syracuseStep 12848003 = 19272005) B19272005
theorem B9014267 : Blo 1052612 9014267 := bstep (se 1 (by rfl) ⟨6760700, by rfl⟩ : syracuseStep 9014267 = 13521401) B13521401
theorem B3247145 : Blo 1052612 3247145 := bstep (se 2 (by rfl) ⟨1217679, by rfl⟩ : syracuseStep 3247145 = 2435359) B2435359
theorem B5344541 : Blo 1052612 5344541 := bstep (se 3 (by rfl) ⟨1002101, by rfl⟩ : syracuseStep 5344541 = 2004203) B2004203
theorem B1052719 : Blo 1052612 1052719 := bstep (se 1 (by rfl) ⟨789539, by rfl⟩ : syracuseStep 1052719 = 1579079) B1579079
theorem B1053119 : Blo 1052612 1053119 := bstep (se 1 (by rfl) ⟨789839, by rfl⟩ : syracuseStep 1053119 = 1579679) B1579679
theorem B1053743 : Blo 1052612 1053743 := bstep (se 1 (by rfl) ⟨790307, by rfl⟩ : syracuseStep 1053743 = 1580615) B1580615
theorem B1053863 : Blo 1052612 1053863 := bstep (se 1 (by rfl) ⟨790397, by rfl⟩ : syracuseStep 1053863 = 1580795) B1580795
theorem B7607465 : Blo 1052612 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B1054415 : Blo 1052612 1054415 := bstep (se 1 (by rfl) ⟨790811, by rfl⟩ : syracuseStep 1054415 = 1581623) B1581623
theorem B5347133 : Blo 1052612 5347133 := bstep (se 3 (by rfl) ⟨1002587, by rfl⟩ : syracuseStep 5347133 = 2005175) B2005175
theorem B1054575 : Blo 1052612 1054575 := bstep (se 1 (by rfl) ⟨790931, by rfl⟩ : syracuseStep 1054575 = 1581863) B1581863
theorem B1054631 : Blo 1052612 1054631 := bstep (se 1 (by rfl) ⟨790973, by rfl⟩ : syracuseStep 1054631 = 1581947) B1581947
theorem B1054655 : Blo 1052612 1054655 := bstep (se 1 (by rfl) ⟨790991, by rfl⟩ : syracuseStep 1054655 = 1581983) B1581983
theorem B1054715 : Blo 1052612 1054715 := bstep (se 1 (by rfl) ⟨791036, by rfl⟩ : syracuseStep 1054715 = 1582073) B1582073
theorem B1579115 : Blo 1052612 1579115 := bstep (se 1 (by rfl) ⟨1184336, by rfl⟩ : syracuseStep 1579115 = 2368673) B2368673
theorem B1054943 : Blo 1052612 1054943 := bstep (se 1 (by rfl) ⟨791207, by rfl⟩ : syracuseStep 1054943 = 1582415) B1582415
theorem B1054975 : Blo 1052612 1054975 := bstep (se 1 (by rfl) ⟨791231, by rfl⟩ : syracuseStep 1054975 = 1582463) B1582463
theorem B1579391 : Blo 1052612 1579391 := bstep (se 1 (by rfl) ⟨1184543, by rfl⟩ : syracuseStep 1579391 = 2369087) B2369087
theorem B1055103 : Blo 1052612 1055103 := bstep (se 1 (by rfl) ⟨791327, by rfl⟩ : syracuseStep 1055103 = 1582655) B1582655
theorem B5347943 : Blo 1052612 5347943 := bstep (se 1 (by rfl) ⟨4010957, by rfl⟩ : syracuseStep 5347943 = 8021915) B8021915
theorem B1579631 : Blo 1052612 1579631 := bstep (se 1 (by rfl) ⟨1184723, by rfl⟩ : syracuseStep 1579631 = 2369447) B2369447
theorem B1055343 : Blo 1052612 1055343 := bstep (se 1 (by rfl) ⟨791507, by rfl⟩ : syracuseStep 1055343 = 1583015) B1583015
theorem B1055423 : Blo 1052612 1055423 := bstep (se 1 (by rfl) ⟨791567, by rfl⟩ : syracuseStep 1055423 = 1583135) B1583135
theorem B1055995 : Blo 1052612 1055995 := bstep (se 1 (by rfl) ⟨791996, by rfl⟩ : syracuseStep 1055995 = 1583993) B1583993
theorem B3382555 : Blo 1052612 3382555 := bstep (se 1 (by rfl) ⟨2536916, by rfl⟩ : syracuseStep 3382555 = 5073833) B5073833
theorem B4005247 : Blo 1052612 4005247 := bstep (se 1 (by rfl) ⟨3003935, by rfl⟩ : syracuseStep 4005247 = 6007871) B6007871
theorem B1580681 : Blo 1052612 1580681 := bstep (se 2 (by rfl) ⟨592755, by rfl⟩ : syracuseStep 1580681 = 1185511) B1185511
theorem B1580699 : Blo 1052612 1580699 := bstep (se 1 (by rfl) ⟨1185524, by rfl⟩ : syracuseStep 1580699 = 2371049) B2371049
theorem B1580735 : Blo 1052612 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B1187743 : Blo 1052612 1187743 := bstep (se 1 (by rfl) ⟨890807, by rfl⟩ : syracuseStep 1187743 = 1781615) B1781615
theorem B1777727 : Blo 1052612 1777727 := bstep (se 1 (by rfl) ⟨1333295, by rfl⟩ : syracuseStep 1777727 = 2666591) B2666591
theorem B2891963 : Blo 1052612 2891963 := bstep (se 1 (by rfl) ⟨2168972, by rfl⟩ : syracuseStep 2891963 = 4337945) B4337945
theorem B1581383 : Blo 1052612 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B1778591 : Blo 1052612 1778591 := bstep (se 1 (by rfl) ⟨1333943, by rfl⟩ : syracuseStep 1778591 = 2667887) B2667887
theorem B1582217 : Blo 1052612 1582217 := bstep (se 2 (by rfl) ⟨593331, by rfl⟩ : syracuseStep 1582217 = 1186663) B1186663
theorem B3253385 : Blo 1052612 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B3384605 : Blo 1052612 3384605 := bstep (se 3 (by rfl) ⟨634613, by rfl⟩ : syracuseStep 3384605 = 1269227) B1269227
theorem B2369231 : Blo 1052612 2369231 := bstep (se 1 (by rfl) ⟨1776923, by rfl⟩ : syracuseStep 2369231 = 3553847) B3553847
theorem B2402207 : Blo 1052612 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B2369609 : Blo 1052612 2369609 := bstep (se 2 (by rfl) ⟨888603, by rfl⟩ : syracuseStep 2369609 = 1777207) B1777207
theorem B2369735 : Blo 1052612 2369735 := bstep (se 1 (by rfl) ⟨1777301, by rfl⟩ : syracuseStep 2369735 = 3554603) B3554603
theorem B2370185 : Blo 1052612 2370185 := bstep (se 2 (by rfl) ⟨888819, by rfl⟩ : syracuseStep 2370185 = 1777639) B1777639
theorem B1583771 : Blo 1052612 1583771 := bstep (se 1 (by rfl) ⟨1187828, by rfl⟩ : syracuseStep 1583771 = 2375657) B2375657
theorem B2370473 : Blo 1052612 2370473 := bstep (se 2 (by rfl) ⟨888927, by rfl⟩ : syracuseStep 2370473 = 1777855) B1777855
theorem B1584239 : Blo 1052612 1584239 := bstep (se 1 (by rfl) ⟨1188179, by rfl⟩ : syracuseStep 1584239 = 2376359) B2376359
theorem B1584287 : Blo 1052612 1584287 := bstep (se 1 (by rfl) ⟨1188215, by rfl⟩ : syracuseStep 1584287 = 2376431) B2376431
theorem B4009135 : Blo 1052612 4009135 := bstep (se 1 (by rfl) ⟨3006851, by rfl⟩ : syracuseStep 4009135 = 6013703) B6013703
theorem B8105143 : Blo 1052612 8105143 := bstep (se 1 (by rfl) ⟨6078857, by rfl⟩ : syracuseStep 8105143 = 12157715) B12157715
theorem B2534591 : Blo 1052612 2534591 := bstep (se 1 (by rfl) ⟨1900943, by rfl⟩ : syracuseStep 2534591 = 3801887) B3801887
theorem B1584425 : Blo 1052612 1584425 := bstep (se 2 (by rfl) ⟨594159, by rfl⟩ : syracuseStep 1584425 = 1188319) B1188319
theorem B2371175 : Blo 1052612 2371175 := bstep (se 1 (by rfl) ⟨1778381, by rfl⟩ : syracuseStep 2371175 = 3556763) B3556763
theorem B8007335 : Blo 1052612 8007335 := bstep (se 1 (by rfl) ⟨6005501, by rfl⟩ : syracuseStep 8007335 = 12011003) B12011003
theorem B1584863 : Blo 1052612 1584863 := bstep (se 1 (by rfl) ⟨1188647, by rfl⟩ : syracuseStep 1584863 = 2377295) B2377295
theorem B2372201 : Blo 1052612 2372201 := bstep (se 2 (by rfl) ⟨889575, by rfl⟩ : syracuseStep 2372201 = 1779151) B1779151
theorem B2372327 : Blo 1052612 2372327 := bstep (se 1 (by rfl) ⟨1779245, by rfl⟩ : syracuseStep 2372327 = 3558491) B3558491
theorem B4502623 : Blo 1052612 4502623 := bstep (se 1 (by rfl) ⟨3376967, by rfl⟩ : syracuseStep 4502623 = 6753935) B6753935
theorem B10139053 : Blo 1052612 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B4011551 : Blo 1052612 4011551 := bstep (se 1 (by rfl) ⟨3008663, by rfl⟩ : syracuseStep 4011551 = 6017327) B6017327
theorem B2668535 : Blo 1052612 2668535 := bstep (se 1 (by rfl) ⟨2001401, by rfl⟩ : syracuseStep 2668535 = 4002803) B4002803
theorem B3553307 : Blo 1052612 3553307 := bstep (se 1 (by rfl) ⟨2664980, by rfl⟩ : syracuseStep 3553307 = 5329961) B5329961
theorem B2373839 : Blo 1052612 2373839 := bstep (se 1 (by rfl) ⟨1780379, by rfl⟩ : syracuseStep 2373839 = 3560759) B3560759
theorem B15251699 : Blo 1052612 15251699 := bstep (se 1 (by rfl) ⟨11438774, by rfl⟩ : syracuseStep 15251699 = 22877549) B22877549
theorem B6011243 : Blo 1052612 6011243 := bstep (se 1 (by rfl) ⟨4508432, by rfl⟩ : syracuseStep 6011243 = 9016865) B9016865
theorem B2701775 : Blo 1052612 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B2374199 : Blo 1052612 2374199 := bstep (se 1 (by rfl) ⟨1780649, by rfl⟩ : syracuseStep 2374199 = 3561299) B3561299
theorem B1522271 : Blo 1052612 1522271 := bstep (se 1 (by rfl) ⟨1141703, by rfl⟩ : syracuseStep 1522271 = 2283407) B2283407
theorem B2375135 : Blo 1052612 2375135 := bstep (se 1 (by rfl) ⟨1781351, by rfl⟩ : syracuseStep 2375135 = 3562703) B3562703
theorem B3554927 : Blo 1052612 3554927 := bstep (se 1 (by rfl) ⟨2666195, by rfl⟩ : syracuseStep 3554927 = 5332391) B5332391
theorem B2670479 : Blo 1052612 2670479 := bstep (se 1 (by rfl) ⟨2002859, by rfl⟩ : syracuseStep 2670479 = 4005719) B4005719
theorem B2441129 : Blo 1052612 2441129 := bstep (se 2 (by rfl) ⟨915423, by rfl⟩ : syracuseStep 2441129 = 1830847) B1830847
theorem B2998241 : Blo 1052612 2998241 := bstep (se 2 (by rfl) ⟨1124340, by rfl⟩ : syracuseStep 2998241 = 2248681) B2248681
theorem B2999015 : Blo 1052612 2999015 := bstep (se 1 (by rfl) ⟨2249261, by rfl⟩ : syracuseStep 2999015 = 4498523) B4498523
theorem B3851039 : Blo 1052612 3851039 := bstep (se 1 (by rfl) ⟨2888279, by rfl⟩ : syracuseStep 3851039 = 5776559) B5776559
theorem B3556331 : Blo 1052612 3556331 := bstep (se 1 (by rfl) ⟨2667248, by rfl⟩ : syracuseStep 3556331 = 5334497) B5334497
theorem B2376935 : Blo 1052612 2376935 := bstep (se 1 (by rfl) ⟨1782701, by rfl⟩ : syracuseStep 2376935 = 3565403) B3565403
theorem B4801787 : Blo 1052612 4801787 := bstep (se 1 (by rfl) ⟨3601340, by rfl⟩ : syracuseStep 4801787 = 7202681) B7202681
theorem B22824899 : Blo 1052612 22824899 := bstep (se 1 (by rfl) ⟨17118674, by rfl⟩ : syracuseStep 22824899 = 34237349) B34237349
theorem B2672959 : Blo 1052612 2672959 := bstep (se 1 (by rfl) ⟨2004719, by rfl⟩ : syracuseStep 2672959 = 4009439) B4009439
theorem B5065183 : Blo 1052612 5065183 := bstep (se 1 (by rfl) ⟨3798887, by rfl⟩ : syracuseStep 5065183 = 7597775) B7597775
theorem B3001225 : Blo 1052612 3001225 := bstep (se 2 (by rfl) ⟨1125459, by rfl⟩ : syracuseStep 3001225 = 2250919) B2250919
theorem B61590415 : Blo 1052612 61590415 := bstep (se 1 (by rfl) ⟨46192811, by rfl⟩ : syracuseStep 61590415 = 92385623) B92385623
theorem B12012461 : Blo 1052612 12012461 := bstep (se 3 (by rfl) ⟨2252336, by rfl⟩ : syracuseStep 12012461 = 4504673) B4504673
theorem B2673607 : Blo 1052612 2673607 := bstep (se 1 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 2673607 = 4010411) B4010411
theorem B2674529 : Blo 1052612 2674529 := bstep (se 2 (by rfl) ⟨1002948, by rfl⟩ : syracuseStep 2674529 = 2005897) B2005897
theorem B4870255 : Blo 1052612 4870255 := bstep (se 1 (by rfl) ⟨3652691, by rfl⟩ : syracuseStep 4870255 = 7305383) B7305383
theorem B17093045 : Blo 1052612 17093045 := bstep (se 5 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 17093045 = 1602473) B1602473
theorem B6934967 : Blo 1052612 6934967 := bstep (se 1 (by rfl) ⟨5201225, by rfl⟩ : syracuseStep 6934967 = 10402451) B10402451
theorem B228545171 : Blo 1052612 228545171 := bstep (se 1 (by rfl) ⟨171408878, by rfl⟩ : syracuseStep 228545171 = 342817757) B342817757
theorem B2249569 : Blo 1052612 2249569 := bstep (se 2 (by rfl) ⟨843588, by rfl⟩ : syracuseStep 2249569 = 1687177) B1687177
theorem B15422345 : Blo 1052612 15422345 := bstep (se 2 (by rfl) ⟨5783379, by rfl⟩ : syracuseStep 15422345 = 11566759) B11566759
theorem B41112983 : Blo 1052612 41112983 := bstep (se 1 (by rfl) ⟨30834737, by rfl⟩ : syracuseStep 41112983 = 61669475) B61669475
theorem B9001145 : Blo 1052612 9001145 := bstep (se 2 (by rfl) ⟨3375429, by rfl⟩ : syracuseStep 9001145 = 6750859) B6750859
theorem B1826075 : Blo 1052612 1826075 := bstep (se 1 (by rfl) ⟨1369556, by rfl⟩ : syracuseStep 1826075 = 2739113) B2739113
theorem B1335143 : Blo 1052612 1335143 := bstep (se 1 (by rfl) ⟨1001357, by rfl⟩ : syracuseStep 1335143 = 2002715) B2002715
theorem B1335199 : Blo 1052612 1335199 := bstep (se 1 (by rfl) ⟨1001399, by rfl⟩ : syracuseStep 1335199 = 2002799) B2002799
theorem B2252713 : Blo 1052612 2252713 := bstep (se 2 (by rfl) ⟨844767, by rfl⟩ : syracuseStep 2252713 = 1689535) B1689535
theorem B10150049 : Blo 1052612 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B3006875 : Blo 1052612 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B1335791 : Blo 1052612 1335791 := bstep (se 1 (by rfl) ⟨1001843, by rfl⟩ : syracuseStep 1335791 = 2003687) B2003687
theorem B1303679 : Blo 1052612 1303679 := bstep (se 1 (by rfl) ⟨977759, by rfl⟩ : syracuseStep 1303679 = 1955519) B1955519
theorem B5072219 : Blo 1052612 5072219 := bstep (se 1 (by rfl) ⟨3804164, by rfl⟩ : syracuseStep 5072219 = 7608329) B7608329
theorem B3565025 : Blo 1052612 3565025 := bstep (se 2 (by rfl) ⟨1336884, by rfl⟩ : syracuseStep 3565025 = 2673769) B2673769
theorem B4810303 : Blo 1052612 4810303 := bstep (se 1 (by rfl) ⟨3607727, by rfl⟩ : syracuseStep 4810303 = 7215455) B7215455
theorem B2254763 : Blo 1052612 2254763 := bstep (se 1 (by rfl) ⟨1691072, by rfl⟩ : syracuseStep 2254763 = 3382145) B3382145
theorem B3565565 : Blo 1052612 3565565 := bstep (se 3 (by rfl) ⟨668543, by rfl⟩ : syracuseStep 3565565 = 1337087) B1337087
theorem B10119491 : Blo 1052612 10119491 := bstep (se 1 (by rfl) ⟨7589618, by rfl⟩ : syracuseStep 10119491 = 15179237) B15179237
theorem B38431331 : Blo 1052612 38431331 := bstep (se 1 (by rfl) ⟨28823498, by rfl⟩ : syracuseStep 38431331 = 57646997) B57646997
theorem B57830021 : Blo 1052612 57830021 := bstep (se 4 (by rfl) ⟨5421564, by rfl⟩ : syracuseStep 57830021 = 10843129) B10843129
theorem B24308369 : Blo 1052612 24308369 := bstep (se 2 (by rfl) ⟨9115638, by rfl⟩ : syracuseStep 24308369 = 18231277) B18231277
theorem B8547241 : Blo 1052612 8547241 := bstep (se 2 (by rfl) ⟨3205215, by rfl⟩ : syracuseStep 8547241 = 6410431) B6410431
theorem B30403673 : Blo 1052612 30403673 := bstep (se 2 (by rfl) ⟨11401377, by rfl⟩ : syracuseStep 30403673 = 22802755) B22802755
theorem B6745787 : Blo 1052612 6745787 := bstep (se 1 (by rfl) ⟨5059340, by rfl⟩ : syracuseStep 6745787 = 10118681) B10118681
theorem B10416509 : Blo 1052612 10416509 := bstep (se 3 (by rfl) ⟨1953095, by rfl⟩ : syracuseStep 10416509 = 3906191) B3906191
theorem B41120135 : Blo 1052612 41120135 := bstep (se 1 (by rfl) ⟨30840101, by rfl⟩ : syracuseStep 41120135 = 61680203) B61680203
theorem B11399687 : Blo 1052612 11399687 := bstep (se 1 (by rfl) ⟨8549765, by rfl⟩ : syracuseStep 11399687 = 17099531) B17099531
theorem B27031319 : Blo 1052612 27031319 := bstep (se 1 (by rfl) ⟨20273489, by rfl⟩ : syracuseStep 27031319 = 40546979) B40546979
theorem B19265525 : Blo 1052612 19265525 := bstep (se 5 (by rfl) ⟨903071, by rfl⟩ : syracuseStep 19265525 = 1806143) B1806143
theorem B5339357 : Blo 1052612 5339357 := bstep (se 3 (by rfl) ⟨1001129, by rfl⟩ : syracuseStep 5339357 = 2002259) B2002259
theorem B43219493 : Blo 1052612 43219493 := bstep (se 4 (by rfl) ⟨4051827, by rfl⟩ : syracuseStep 43219493 = 8103655) B8103655
theorem B24640793 : Blo 1052612 24640793 := bstep (se 2 (by rfl) ⟨9240297, by rfl⟩ : syracuseStep 24640793 = 18480595) B18480595
theorem B1999343 : Blo 1052612 1999343 := bstep (se 1 (by rfl) ⟨1499507, by rfl⟩ : syracuseStep 1999343 = 2999015) B2999015
theorem B45581453 : Blo 1052612 45581453 := bstep (se 3 (by rfl) ⟨8546522, by rfl⟩ : syracuseStep 45581453 = 17093045) B17093045
theorem B6751451 : Blo 1052612 6751451 := bstep (se 1 (by rfl) ⟨5063588, by rfl⟩ : syracuseStep 6751451 = 10127177) B10127177
theorem B2164763 : Blo 1052612 2164763 := bstep (se 1 (by rfl) ⟨1623572, by rfl⟩ : syracuseStep 2164763 = 3247145) B3247145
theorem B4623311 : Blo 1052612 4623311 := bstep (se 1 (by rfl) ⟨3467483, by rfl⟩ : syracuseStep 4623311 = 6934967) B6934967
theorem B3476477 : Blo 1052612 3476477 := bstep (se 3 (by rfl) ⟨651839, by rfl⟩ : syracuseStep 3476477 = 1303679) B1303679
theorem B6753577 : Blo 1052612 6753577 := bstep (se 2 (by rfl) ⟨2532591, by rfl⟩ : syracuseStep 6753577 = 5065183) B5065183
theorem B4001633 : Blo 1052612 4001633 := bstep (se 2 (by rfl) ⟨1500612, by rfl⟩ : syracuseStep 4001633 = 3001225) B3001225
theorem B82120553 : Blo 1052612 82120553 := bstep (se 2 (by rfl) ⟨30795207, by rfl⟩ : syracuseStep 82120553 = 61590415) B61590415
theorem B1052743 : Blo 1052612 1052743 := bstep (se 1 (by rfl) ⟨789557, by rfl⟩ : syracuseStep 1052743 = 1579115) B1579115
theorem B6000763 : Blo 1052612 6000763 := bstep (se 1 (by rfl) ⟨4500572, by rfl⟩ : syracuseStep 6000763 = 9001145) B9001145
theorem B5345513 : Blo 1052612 5345513 := bstep (se 2 (by rfl) ⟨2004567, by rfl⟩ : syracuseStep 5345513 = 4009135) B4009135
theorem B1052927 : Blo 1052612 1052927 := bstep (se 1 (by rfl) ⟨789695, by rfl⟩ : syracuseStep 1052927 = 1579391) B1579391
theorem B1053087 : Blo 1052612 1053087 := bstep (se 1 (by rfl) ⟨789815, by rfl⟩ : syracuseStep 1053087 = 1579631) B1579631
theorem B1053787 : Blo 1052612 1053787 := bstep (se 1 (by rfl) ⟨790340, by rfl⟩ : syracuseStep 1053787 = 1580681) B1580681
theorem B1053799 : Blo 1052612 1053799 := bstep (se 1 (by rfl) ⟨790349, by rfl⟩ : syracuseStep 1053799 = 1580699) B1580699
theorem B1053823 : Blo 1052612 1053823 := bstep (se 1 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 1053823 = 1580735) B1580735
theorem B1185151 : Blo 1052612 1185151 := bstep (se 1 (by rfl) ⟨888863, by rfl⟩ : syracuseStep 1185151 = 1777727) B1777727
theorem B6493673 : Blo 1052612 6493673 := bstep (se 2 (by rfl) ⟨2435127, by rfl⟩ : syracuseStep 6493673 = 4870255) B4870255
theorem B1054255 : Blo 1052612 1054255 := bstep (se 1 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 1054255 = 1581383) B1581383
theorem B2004583 : Blo 1052612 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B1185727 : Blo 1052612 1185727 := bstep (se 1 (by rfl) ⟨889295, by rfl⟩ : syracuseStep 1185727 = 1778591) B1778591
theorem B40671197 : Blo 1052612 40671197 := bstep (se 3 (by rfl) ⟨7625849, by rfl⟩ : syracuseStep 40671197 = 15251699) B15251699
theorem B1054811 : Blo 1052612 1054811 := bstep (se 1 (by rfl) ⟨791108, by rfl⟩ : syracuseStep 1054811 = 1582217) B1582217
theorem B3381479 : Blo 1052612 3381479 := bstep (se 1 (by rfl) ⟨2536109, by rfl⟩ : syracuseStep 3381479 = 5072219) B5072219
theorem B1579487 : Blo 1052612 1579487 := bstep (se 1 (by rfl) ⟨1184615, by rfl⟩ : syracuseStep 1579487 = 2369231) B2369231
theorem B1579739 : Blo 1052612 1579739 := bstep (se 1 (by rfl) ⟨1184804, by rfl⟩ : syracuseStep 1579739 = 2369609) B2369609
theorem B6003497 : Blo 1052612 6003497 := bstep (se 2 (by rfl) ⟨2251311, by rfl⟩ : syracuseStep 6003497 = 4502623) B4502623
theorem B1579823 : Blo 1052612 1579823 := bstep (se 1 (by rfl) ⟨1184867, by rfl⟩ : syracuseStep 1579823 = 2369735) B2369735
theorem B1580123 : Blo 1052612 1580123 := bstep (se 1 (by rfl) ⟨1185092, by rfl⟩ : syracuseStep 1580123 = 2370185) B2370185
theorem B1055847 : Blo 1052612 1055847 := bstep (se 1 (by rfl) ⟨791885, by rfl⟩ : syracuseStep 1055847 = 1583771) B1583771
theorem B1580315 : Blo 1052612 1580315 := bstep (se 1 (by rfl) ⟨1185236, by rfl⟩ : syracuseStep 1580315 = 2370473) B2370473
theorem B1056159 : Blo 1052612 1056159 := bstep (se 1 (by rfl) ⟨792119, by rfl⟩ : syracuseStep 1056159 = 1584239) B1584239
theorem B1056191 : Blo 1052612 1056191 := bstep (se 1 (by rfl) ⟨792143, by rfl⟩ : syracuseStep 1056191 = 1584287) B1584287
theorem B1056283 : Blo 1052612 1056283 := bstep (se 1 (by rfl) ⟨792212, by rfl⟩ : syracuseStep 1056283 = 1584425) B1584425
theorem B1580783 : Blo 1052612 1580783 := bstep (se 1 (by rfl) ⟨1185587, by rfl⟩ : syracuseStep 1580783 = 2371175) B2371175
theorem B4497191 : Blo 1052612 4497191 := bstep (se 1 (by rfl) ⟨3372893, by rfl⟩ : syracuseStep 4497191 = 6745787) B6745787
theorem B1056575 : Blo 1052612 1056575 := bstep (se 1 (by rfl) ⟨792431, by rfl⟩ : syracuseStep 1056575 = 1584863) B1584863
theorem B1581467 : Blo 1052612 1581467 := bstep (se 1 (by rfl) ⟨1186100, by rfl⟩ : syracuseStep 1581467 = 2372201) B2372201
theorem B1581551 : Blo 1052612 1581551 := bstep (se 1 (by rfl) ⟨1186163, by rfl⟩ : syracuseStep 1581551 = 2372327) B2372327
theorem B6758909 : Blo 1052612 6758909 := bstep (se 3 (by rfl) ⟨1267295, by rfl⟩ : syracuseStep 6758909 = 2534591) B2534591
theorem B1779023 : Blo 1052612 1779023 := bstep (se 1 (by rfl) ⟨1334267, by rfl⟩ : syracuseStep 1779023 = 2668535) B2668535
theorem B2368871 : Blo 1052612 2368871 := bstep (se 1 (by rfl) ⟨1776653, by rfl⟩ : syracuseStep 2368871 = 3553307) B3553307
theorem B1582559 : Blo 1052612 1582559 := bstep (se 1 (by rfl) ⟨1186919, by rfl⟩ : syracuseStep 1582559 = 2373839) B2373839
theorem B4007495 : Blo 1052612 4007495 := bstep (se 1 (by rfl) ⟨3005621, by rfl⟩ : syracuseStep 4007495 = 6011243) B6011243
theorem B28812995 : Blo 1052612 28812995 := bstep (se 1 (by rfl) ⟨21609746, by rfl⟩ : syracuseStep 28812995 = 43219493) B43219493
theorem B1582799 : Blo 1052612 1582799 := bstep (se 1 (by rfl) ⟨1187099, by rfl⟩ : syracuseStep 1582799 = 2374199) B2374199
theorem B16427195 : Blo 1052612 16427195 := bstep (se 1 (by rfl) ⟨12320396, by rfl⟩ : syracuseStep 16427195 = 24640793) B24640793
theorem B1583423 : Blo 1052612 1583423 := bstep (se 1 (by rfl) ⟨1187567, by rfl⟩ : syracuseStep 1583423 = 2375135) B2375135
theorem B2369951 : Blo 1052612 2369951 := bstep (se 1 (by rfl) ⟨1777463, by rfl⟩ : syracuseStep 2369951 = 3554927) B3554927
theorem B1780265 : Blo 1052612 1780265 := bstep (se 2 (by rfl) ⟨667599, by rfl⟩ : syracuseStep 1780265 = 1335199) B1335199
theorem B1583657 : Blo 1052612 1583657 := bstep (se 2 (by rfl) ⟨593871, by rfl⟩ : syracuseStep 1583657 = 1187743) B1187743
theorem B1780319 : Blo 1052612 1780319 := bstep (se 1 (by rfl) ⟨1335239, by rfl⟩ : syracuseStep 1780319 = 2670479) B2670479
theorem B2567359 : Blo 1052612 2567359 := bstep (se 1 (by rfl) ⟨1925519, by rfl⟩ : syracuseStep 2567359 = 3851039) B3851039
theorem B2370887 : Blo 1052612 2370887 := bstep (se 1 (by rfl) ⟨1778165, by rfl⟩ : syracuseStep 2370887 = 3556331) B3556331
theorem B1584623 : Blo 1052612 1584623 := bstep (se 1 (by rfl) ⟨1188467, by rfl⟩ : syracuseStep 1584623 = 2376935) B2376935
theorem B15216599 : Blo 1052612 15216599 := bstep (se 1 (by rfl) ⟨11412449, by rfl⟩ : syracuseStep 15216599 = 22824899) B22824899
theorem B8565335 : Blo 1052612 8565335 := bstep (se 1 (by rfl) ⟨6424001, by rfl⟩ : syracuseStep 8565335 = 12848003) B12848003
theorem B8008307 : Blo 1052612 8008307 := bstep (se 1 (by rfl) ⟨6006230, by rfl⟩ : syracuseStep 8008307 = 12012461) B12012461
theorem B6009511 : Blo 1052612 6009511 := bstep (se 1 (by rfl) ⟨4507133, by rfl⟩ : syracuseStep 6009511 = 9014267) B9014267
theorem B1783019 : Blo 1052612 1783019 := bstep (se 1 (by rfl) ⟨1337264, by rfl⟩ : syracuseStep 1783019 = 2674529) B2674529
theorem B9025613 : Blo 1052612 9025613 := bstep (se 3 (by rfl) ⟨1692302, by rfl⟩ : syracuseStep 9025613 = 3384605) B3384605
theorem B27408655 : Blo 1052612 27408655 := bstep (se 1 (by rfl) ⟨20556491, by rfl⟩ : syracuseStep 27408655 = 41112983) B41112983
theorem B6012701 : Blo 1052612 6012701 := bstep (se 3 (by rfl) ⟨1127381, by rfl⟩ : syracuseStep 6012701 = 2254763) B2254763
theorem B6766699 : Blo 1052612 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B2376683 : Blo 1052612 2376683 := bstep (se 1 (by rfl) ⟨1782512, by rfl⟩ : syracuseStep 2376683 = 3565025) B3565025
theorem B2999425 : Blo 1052612 2999425 := bstep (se 2 (by rfl) ⟨1124784, by rfl⟩ : syracuseStep 2999425 = 2249569) B2249569
theorem B2377043 : Blo 1052612 2377043 := bstep (se 1 (by rfl) ⟨1782782, by rfl⟩ : syracuseStep 2377043 = 3565565) B3565565
theorem B38553347 : Blo 1052612 38553347 := bstep (se 1 (by rfl) ⟨28915010, by rfl⟩ : syracuseStep 38553347 = 57830021) B57830021
theorem B16205579 : Blo 1052612 16205579 := bstep (se 1 (by rfl) ⟨12154184, by rfl⟩ : syracuseStep 16205579 = 24308369) B24308369
theorem B13518737 : Blo 1052612 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B20269115 : Blo 1052612 20269115 := bstep (se 1 (by rfl) ⟨15201836, by rfl⟩ : syracuseStep 20269115 = 30403673) B30403673
theorem B27413423 : Blo 1052612 27413423 := bstep (se 1 (by rfl) ⟨20560067, by rfl⟩ : syracuseStep 27413423 = 41120135) B41120135
theorem B4869533 : Blo 1052612 4869533 := bstep (se 3 (by rfl) ⟨913037, by rfl⟩ : syracuseStep 4869533 = 1826075) B1826075
theorem B2674367 : Blo 1052612 2674367 := bstep (se 1 (by rfl) ⟨2005775, by rfl⟩ : syracuseStep 2674367 = 4011551) B4011551
theorem B3559571 : Blo 1052612 3559571 := bstep (se 1 (by rfl) ⟨2669678, by rfl⟩ : syracuseStep 3559571 = 5339357) B5339357
theorem B4510073 : Blo 1052612 4510073 := bstep (se 2 (by rfl) ⟨1691277, by rfl⟩ : syracuseStep 4510073 = 3382555) B3382555
theorem B3560381 : Blo 1052612 3560381 := bstep (se 3 (by rfl) ⟨667571, by rfl⟩ : syracuseStep 3560381 = 1335143) B1335143
theorem B6509677 : Blo 1052612 6509677 := bstep (se 3 (by rfl) ⟨1220564, by rfl⟩ : syracuseStep 6509677 = 2441129) B2441129
theorem B3003617 : Blo 1052612 3003617 := bstep (se 2 (by rfl) ⟨1126356, by rfl⟩ : syracuseStep 3003617 = 2252713) B2252713
theorem B1333351 : Blo 1052612 1333351 := bstep (se 1 (by rfl) ⟨1000013, by rfl⟩ : syracuseStep 1333351 = 2000027) B2000027
theorem B3201191 : Blo 1052612 3201191 := bstep (se 1 (by rfl) ⟨2400893, by rfl⟩ : syracuseStep 3201191 = 4801787) B4801787
theorem B2251243 : Blo 1052612 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B3562109 : Blo 1052612 3562109 := bstep (se 3 (by rfl) ⟨667895, by rfl⟩ : syracuseStep 3562109 = 1335791) B1335791
theorem B8018999 : Blo 1052612 8018999 := bstep (se 1 (by rfl) ⟨6014249, by rfl⟩ : syracuseStep 8018999 = 12028499) B12028499
theorem B6413737 : Blo 1052612 6413737 := bstep (se 2 (by rfl) ⟨2405151, by rfl⟩ : syracuseStep 6413737 = 4810303) B4810303
theorem B3563027 : Blo 1052612 3563027 := bstep (se 1 (by rfl) ⟨2672270, by rfl⟩ : syracuseStep 3563027 = 5344541) B5344541
theorem B5332553 : Blo 1052612 5332553 := bstep (se 2 (by rfl) ⟨1999707, by rfl⟩ : syracuseStep 5332553 = 3999415) B3999415
theorem B8675693 : Blo 1052612 8675693 := bstep (se 3 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 8675693 = 3253385) B3253385
theorem B3563945 : Blo 1052612 3563945 := bstep (se 2 (by rfl) ⟨1336479, by rfl⟩ : syracuseStep 3563945 = 2672959) B2672959
theorem B152363447 : Blo 1052612 152363447 := bstep (se 1 (by rfl) ⟨114272585, by rfl⟩ : syracuseStep 152363447 = 228545171) B228545171
theorem B10281563 : Blo 1052612 10281563 := bstep (se 1 (by rfl) ⟨7711172, by rfl⟩ : syracuseStep 10281563 = 15422345) B15422345
theorem B5071643 : Blo 1052612 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B3564755 : Blo 1052612 3564755 := bstep (se 1 (by rfl) ⟨2673566, by rfl⟩ : syracuseStep 3564755 = 5347133) B5347133
theorem B11396321 : Blo 1052612 11396321 := bstep (se 2 (by rfl) ⟨4273620, by rfl⟩ : syracuseStep 11396321 = 8547241) B8547241
theorem B3564809 : Blo 1052612 3564809 := bstep (se 2 (by rfl) ⟨1336803, by rfl⟩ : syracuseStep 3564809 = 2673607) B2673607
theorem B10806857 : Blo 1052612 10806857 := bstep (se 2 (by rfl) ⟨4052571, by rfl⟩ : syracuseStep 10806857 = 8105143) B8105143
theorem B3565295 : Blo 1052612 3565295 := bstep (se 1 (by rfl) ⟨2673971, by rfl⟩ : syracuseStep 3565295 = 5347943) B5347943
theorem B1927975 : Blo 1052612 1927975 := bstep (se 1 (by rfl) ⟨1445981, by rfl⟩ : syracuseStep 1927975 = 2891963) B2891963
theorem B1601471 : Blo 1052612 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B6746327 : Blo 1052612 6746327 := bstep (se 1 (by rfl) ⟨5059745, by rfl⟩ : syracuseStep 6746327 = 10119491) B10119491
theorem B4059389 : Blo 1052612 4059389 := bstep (se 3 (by rfl) ⟨761135, by rfl⟩ : syracuseStep 4059389 = 1522271) B1522271
theorem B25620887 : Blo 1052612 25620887 := bstep (se 1 (by rfl) ⟨19215665, by rfl⟩ : syracuseStep 25620887 = 38431331) B38431331
theorem B5338223 : Blo 1052612 5338223 := bstep (se 1 (by rfl) ⟨4003667, by rfl⟩ : syracuseStep 5338223 = 8007335) B8007335
theorem B6944339 : Blo 1052612 6944339 := bstep (se 1 (by rfl) ⟨5208254, by rfl⟩ : syracuseStep 6944339 = 10416509) B10416509
theorem B7599791 : Blo 1052612 7599791 := bstep (se 1 (by rfl) ⟨5699843, by rfl⟩ : syracuseStep 7599791 = 11399687) B11399687
theorem B18020879 : Blo 1052612 18020879 := bstep (se 1 (by rfl) ⟨13515659, by rfl⟩ : syracuseStep 18020879 = 27031319) B27031319
theorem B12843683 : Blo 1052612 12843683 := bstep (se 1 (by rfl) ⟨9632762, by rfl⟩ : syracuseStep 12843683 = 19265525) B19265525
theorem B1801183 : Blo 1052612 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B5340329 : Blo 1052612 5340329 := bstep (se 2 (by rfl) ⟨2002623, by rfl⟩ : syracuseStep 5340329 = 4005247) B4005247
theorem B1998827 : Blo 1052612 1998827 := bstep (se 1 (by rfl) ⟨1499120, by rfl⟩ : syracuseStep 1998827 = 2998241) B2998241
theorem B9012491 : Blo 1052612 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B3999233 : Blo 1052612 3999233 := bstep (se 2 (by rfl) ⟨1499712, by rfl⟩ : syracuseStep 3999233 = 2999425) B2999425
theorem B3082207 : Blo 1052612 3082207 := bstep (se 1 (by rfl) ⟨2311655, by rfl⟩ : syracuseStep 3082207 = 4623311) B4623311
theorem B3246355 : Blo 1052612 3246355 := bstep (se 1 (by rfl) ⟨2434766, by rfl⟩ : syracuseStep 3246355 = 4869533) B4869533
theorem B2002411 : Blo 1052612 2002411 := bstep (se 1 (by rfl) ⟨1501808, by rfl⟩ : syracuseStep 2002411 = 3003617) B3003617
theorem B2134127 : Blo 1052612 2134127 := bstep (se 1 (by rfl) ⟨1600595, by rfl⟩ : syracuseStep 2134127 = 3201191) B3201191
theorem B1052991 : Blo 1052612 1052991 := bstep (se 1 (by rfl) ⟨789743, by rfl⟩ : syracuseStep 1052991 = 1579487) B1579487
theorem B1053159 : Blo 1052612 1053159 := bstep (se 1 (by rfl) ⟨789869, by rfl⟩ : syracuseStep 1053159 = 1579739) B1579739
theorem B4002331 : Blo 1052612 4002331 := bstep (se 1 (by rfl) ⟨3001748, by rfl⟩ : syracuseStep 4002331 = 6003497) B6003497
theorem B1053215 : Blo 1052612 1053215 := bstep (se 1 (by rfl) ⟨789911, by rfl⟩ : syracuseStep 1053215 = 1579823) B1579823
theorem B5345999 : Blo 1052612 5345999 := bstep (se 1 (by rfl) ⟨4009499, by rfl⟩ : syracuseStep 5345999 = 8018999) B8018999
theorem B1053415 : Blo 1052612 1053415 := bstep (se 1 (by rfl) ⟨790061, by rfl⟩ : syracuseStep 1053415 = 1580123) B1580123
theorem B1053543 : Blo 1052612 1053543 := bstep (se 1 (by rfl) ⟨790157, by rfl⟩ : syracuseStep 1053543 = 1580315) B1580315
theorem B1053855 : Blo 1052612 1053855 := bstep (se 1 (by rfl) ⟨790391, by rfl⟩ : syracuseStep 1053855 = 1580783) B1580783
theorem B5772701 : Blo 1052612 5772701 := bstep (se 3 (by rfl) ⟨1082381, by rfl⟩ : syracuseStep 5772701 = 2164763) B2164763
theorem B8001017 : Blo 1052612 8001017 := bstep (se 2 (by rfl) ⟨3000381, by rfl⟩ : syracuseStep 8001017 = 6000763) B6000763
theorem B1054311 : Blo 1052612 1054311 := bstep (se 1 (by rfl) ⟨790733, by rfl⟩ : syracuseStep 1054311 = 1581467) B1581467
theorem B1054367 : Blo 1052612 1054367 := bstep (se 1 (by rfl) ⟨790775, by rfl⟩ : syracuseStep 1054367 = 1581551) B1581551
theorem B6854375 : Blo 1052612 6854375 := bstep (se 1 (by rfl) ⟨5140781, by rfl⟩ : syracuseStep 6854375 = 10281563) B10281563
theorem B3381095 : Blo 1052612 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B1186015 : Blo 1052612 1186015 := bstep (se 1 (by rfl) ⟨889511, by rfl⟩ : syracuseStep 1186015 = 1779023) B1779023
theorem B1579247 : Blo 1052612 1579247 := bstep (se 1 (by rfl) ⟨1184435, by rfl⟩ : syracuseStep 1579247 = 2368871) B2368871
theorem B1055039 : Blo 1052612 1055039 := bstep (se 1 (by rfl) ⟨791279, by rfl⟩ : syracuseStep 1055039 = 1582559) B1582559
theorem B19208663 : Blo 1052612 19208663 := bstep (se 1 (by rfl) ⟨14406497, by rfl⟩ : syracuseStep 19208663 = 28812995) B28812995
theorem B1055199 : Blo 1052612 1055199 := bstep (se 1 (by rfl) ⟨791399, by rfl⟩ : syracuseStep 1055199 = 1582799) B1582799
theorem B10951463 : Blo 1052612 10951463 := bstep (se 1 (by rfl) ⟨8213597, by rfl⟩ : syracuseStep 10951463 = 16427195) B16427195
theorem B1055615 : Blo 1052612 1055615 := bstep (se 1 (by rfl) ⟨791711, by rfl⟩ : syracuseStep 1055615 = 1583423) B1583423
theorem B1579967 : Blo 1052612 1579967 := bstep (se 1 (by rfl) ⟨1184975, by rfl⟩ : syracuseStep 1579967 = 2369951) B2369951
theorem B1186843 : Blo 1052612 1186843 := bstep (se 1 (by rfl) ⟨890132, by rfl⟩ : syracuseStep 1186843 = 1780265) B1780265
theorem B1055771 : Blo 1052612 1055771 := bstep (se 1 (by rfl) ⟨791828, by rfl⟩ : syracuseStep 1055771 = 1583657) B1583657
theorem B1186879 : Blo 1052612 1186879 := bstep (se 1 (by rfl) ⟨890159, by rfl⟩ : syracuseStep 1186879 = 1780319) B1780319
theorem B1580201 : Blo 1052612 1580201 := bstep (se 2 (by rfl) ⟨592575, by rfl⟩ : syracuseStep 1580201 = 1185151) B1185151
theorem B1580591 : Blo 1052612 1580591 := bstep (se 1 (by rfl) ⟨1185443, by rfl⟩ : syracuseStep 1580591 = 2370887) B2370887
theorem B1056415 : Blo 1052612 1056415 := bstep (se 1 (by rfl) ⟨792311, by rfl⟩ : syracuseStep 1056415 = 1584623) B1584623
theorem B1580969 : Blo 1052612 1580969 := bstep (se 2 (by rfl) ⟨592863, by rfl⟩ : syracuseStep 1580969 = 1185727) B1185727
theorem B1777801 : Blo 1052612 1777801 := bstep (se 2 (by rfl) ⟨666675, by rfl⟩ : syracuseStep 1777801 = 1333351) B1333351
theorem B4497551 : Blo 1052612 4497551 := bstep (se 1 (by rfl) ⟨3373163, by rfl⟩ : syracuseStep 4497551 = 6746327) B6746327
theorem B17080591 : Blo 1052612 17080591 := bstep (se 1 (by rfl) ⟨12810443, by rfl⟩ : syracuseStep 17080591 = 25620887) B25620887
theorem B36544873 : Blo 1052612 36544873 := bstep (se 2 (by rfl) ⟨13704327, by rfl⟩ : syracuseStep 36544873 = 27408655) B27408655
theorem B5710223 : Blo 1052612 5710223 := bstep (se 1 (by rfl) ⟨4282667, by rfl⟩ : syracuseStep 5710223 = 8565335) B8565335
theorem B1188679 : Blo 1052612 1188679 := bstep (se 1 (by rfl) ⟨891509, by rfl⟩ : syracuseStep 1188679 = 1783019) B1783019
theorem B4629559 : Blo 1052612 4629559 := bstep (se 1 (by rfl) ⟨3472169, by rfl⟩ : syracuseStep 4629559 = 6944339) B6944339
theorem B2401577 : Blo 1052612 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B8562455 : Blo 1052612 8562455 := bstep (se 1 (by rfl) ⟨6421841, by rfl⟩ : syracuseStep 8562455 = 12843683) B12843683
theorem B4270589 : Blo 1052612 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B4008467 : Blo 1052612 4008467 := bstep (se 1 (by rfl) ⟨3006350, by rfl⟩ : syracuseStep 4008467 = 6012701) B6012701
theorem B9022265 : Blo 1052612 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B1584455 : Blo 1052612 1584455 := bstep (se 1 (by rfl) ⟨1188341, by rfl⟩ : syracuseStep 1584455 = 2376683) B2376683
theorem B30387635 : Blo 1052612 30387635 := bstep (se 1 (by rfl) ⟨22790726, by rfl⟩ : syracuseStep 30387635 = 45581453) B45581453
theorem B4500967 : Blo 1052612 4500967 := bstep (se 1 (by rfl) ⟨3375725, by rfl⟩ : syracuseStep 4500967 = 6751451) B6751451
theorem B1584695 : Blo 1052612 1584695 := bstep (se 1 (by rfl) ⟨1188521, by rfl⟩ : syracuseStep 1584695 = 2377043) B2377043
theorem B13512743 : Blo 1052612 13512743 := bstep (se 1 (by rfl) ⟨10134557, by rfl⟩ : syracuseStep 13512743 = 20269115) B20269115
theorem B1782911 : Blo 1052612 1782911 := bstep (se 1 (by rfl) ⟨1337183, by rfl⟩ : syracuseStep 1782911 = 2674367) B2674367
theorem B12006629 : Blo 1052612 12006629 := bstep (se 4 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 12006629 = 2251243) B2251243
theorem B2667755 : Blo 1052612 2667755 := bstep (se 1 (by rfl) ⟨2000816, by rfl⟩ : syracuseStep 2667755 = 4001633) B4001633
theorem B2373047 : Blo 1052612 2373047 := bstep (se 1 (by rfl) ⟨1779785, by rfl⟩ : syracuseStep 2373047 = 3559571) B3559571
theorem B2373587 : Blo 1052612 2373587 := bstep (se 1 (by rfl) ⟨1780190, by rfl⟩ : syracuseStep 2373587 = 3560381) B3560381
theorem B2570633 : Blo 1052612 2570633 := bstep (se 2 (by rfl) ⟨963987, by rfl⟩ : syracuseStep 2570633 = 1927975) B1927975
theorem B17316461 : Blo 1052612 17316461 := bstep (se 3 (by rfl) ⟨3246836, by rfl⟩ : syracuseStep 17316461 = 6493673) B6493673
theorem B27114131 : Blo 1052612 27114131 := bstep (se 1 (by rfl) ⟨20335598, by rfl⟩ : syracuseStep 27114131 = 40671197) B40671197
theorem B3423145 : Blo 1052612 3423145 := bstep (se 2 (by rfl) ⟨1283679, by rfl⟩ : syracuseStep 3423145 = 2567359) B2567359
theorem B2374739 : Blo 1052612 2374739 := bstep (se 1 (by rfl) ⟨1781054, by rfl⟩ : syracuseStep 2374739 = 3562109) B3562109
theorem B20266109 : Blo 1052612 20266109 := bstep (se 3 (by rfl) ⟨3799895, by rfl⟩ : syracuseStep 20266109 = 7599791) B7599791
theorem B102808925 : Blo 1052612 102808925 := bstep (se 3 (by rfl) ⟨19276673, by rfl⟩ : syracuseStep 102808925 = 38553347) B38553347
theorem B2375351 : Blo 1052612 2375351 := bstep (se 1 (by rfl) ⟨1781513, by rfl⟩ : syracuseStep 2375351 = 3563027) B3563027
theorem B3555035 : Blo 1052612 3555035 := bstep (se 1 (by rfl) ⟨2666276, by rfl⟩ : syracuseStep 3555035 = 5332553) B5332553
theorem B2998127 : Blo 1052612 2998127 := bstep (se 1 (by rfl) ⟨2248595, by rfl⟩ : syracuseStep 2998127 = 4497191) B4497191
theorem B5783795 : Blo 1052612 5783795 := bstep (se 1 (by rfl) ⟨4337846, by rfl⟩ : syracuseStep 5783795 = 8675693) B8675693
theorem B2375963 : Blo 1052612 2375963 := bstep (se 1 (by rfl) ⟨1781972, by rfl⟩ : syracuseStep 2375963 = 3563945) B3563945
theorem B4505939 : Blo 1052612 4505939 := bstep (se 1 (by rfl) ⟨3379454, by rfl⟩ : syracuseStep 4505939 = 6758909) B6758909
theorem B2376503 : Blo 1052612 2376503 := bstep (se 1 (by rfl) ⟨1782377, by rfl⟩ : syracuseStep 2376503 = 3564755) B3564755
theorem B2376539 : Blo 1052612 2376539 := bstep (se 1 (by rfl) ⟨1782404, by rfl⟩ : syracuseStep 2376539 = 3564809) B3564809
theorem B8012681 : Blo 1052612 8012681 := bstep (se 2 (by rfl) ⟨3004755, by rfl⟩ : syracuseStep 8012681 = 6009511) B6009511
theorem B2671663 : Blo 1052612 2671663 := bstep (se 1 (by rfl) ⟨2003747, by rfl⟩ : syracuseStep 2671663 = 4007495) B4007495
theorem B2376863 : Blo 1052612 2376863 := bstep (se 1 (by rfl) ⟨1782647, by rfl⟩ : syracuseStep 2376863 = 3565295) B3565295
theorem B2672777 : Blo 1052612 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B10144399 : Blo 1052612 10144399 := bstep (se 1 (by rfl) ⟨7608299, by rfl⟩ : syracuseStep 10144399 = 15216599) B15216599
theorem B2706259 : Blo 1052612 2706259 := bstep (se 1 (by rfl) ⟨2029694, by rfl⟩ : syracuseStep 2706259 = 4059389) B4059389
theorem B3558815 : Blo 1052612 3558815 := bstep (se 1 (by rfl) ⟨2669111, by rfl⟩ : syracuseStep 3558815 = 5338223) B5338223
theorem B6017075 : Blo 1052612 6017075 := bstep (se 1 (by rfl) ⟨4512806, by rfl⟩ : syracuseStep 6017075 = 9025613) B9025613
theorem B12013919 : Blo 1052612 12013919 := bstep (se 1 (by rfl) ⟨9010439, by rfl⟩ : syracuseStep 12013919 = 18020879) B18020879
theorem B3560219 : Blo 1052612 3560219 := bstep (se 1 (by rfl) ⟨2670164, by rfl⟩ : syracuseStep 3560219 = 5340329) B5340329
theorem B1332551 : Blo 1052612 1332551 := bstep (se 1 (by rfl) ⟨999413, by rfl⟩ : syracuseStep 1332551 = 1998827) B1998827
theorem B10803719 : Blo 1052612 10803719 := bstep (se 1 (by rfl) ⟨8102789, by rfl⟩ : syracuseStep 10803719 = 16205579) B16205579
theorem B5331581 : Blo 1052612 5331581 := bstep (se 3 (by rfl) ⟨999671, by rfl⟩ : syracuseStep 5331581 = 1999343) B1999343
theorem B18275615 : Blo 1052612 18275615 := bstep (se 1 (by rfl) ⟨13706711, by rfl⟩ : syracuseStep 18275615 = 27413423) B27413423
theorem B54747035 : Blo 1052612 54747035 := bstep (se 1 (by rfl) ⟨41060276, by rfl⟩ : syracuseStep 54747035 = 82120553) B82120553
theorem B3563675 : Blo 1052612 3563675 := bstep (se 1 (by rfl) ⟨2672756, by rfl⟩ : syracuseStep 3563675 = 5345513) B5345513
theorem B3006715 : Blo 1052612 3006715 := bstep (se 1 (by rfl) ⟨2255036, by rfl⟩ : syracuseStep 3006715 = 4510073) B4510073
theorem B2254319 : Blo 1052612 2254319 := bstep (se 1 (by rfl) ⟨1690739, by rfl⟩ : syracuseStep 2254319 = 3381479) B3381479
theorem B9004769 : Blo 1052612 9004769 := bstep (se 2 (by rfl) ⟨3376788, by rfl⟩ : syracuseStep 9004769 = 6753577) B6753577
theorem B101575631 : Blo 1052612 101575631 := bstep (se 1 (by rfl) ⟨76181723, by rfl⟩ : syracuseStep 101575631 = 152363447) B152363447
theorem B7597547 : Blo 1052612 7597547 := bstep (se 1 (by rfl) ⟨5698160, by rfl⟩ : syracuseStep 7597547 = 11396321) B11396321
theorem B7204571 : Blo 1052612 7204571 := bstep (se 1 (by rfl) ⟨5403428, by rfl⟩ : syracuseStep 7204571 = 10806857) B10806857
theorem B8679569 : Blo 1052612 8679569 := bstep (se 2 (by rfl) ⟨3254838, by rfl⟩ : syracuseStep 8679569 = 6509677) B6509677
theorem B9270605 : Blo 1052612 9270605 := bstep (se 3 (by rfl) ⟨1738238, by rfl⟩ : syracuseStep 9270605 = 3476477) B3476477
theorem B5338871 : Blo 1052612 5338871 := bstep (se 1 (by rfl) ⟨4004153, by rfl⟩ : syracuseStep 5338871 = 8008307) B8008307
theorem B8551649 : Blo 1052612 8551649 := bstep (se 2 (by rfl) ⟨3206868, by rfl⟩ : syracuseStep 8551649 = 6413737) B6413737
theorem B22774121 : Blo 1052612 22774121 := bstep (se 2 (by rfl) ⟨8540295, by rfl⟩ : syracuseStep 22774121 = 17080591) B17080591
theorem B48726497 : Blo 1052612 48726497 := bstep (se 2 (by rfl) ⟨18272436, by rfl⟩ : syracuseStep 48726497 = 36544873) B36544873
theorem B5341787 : Blo 1052612 5341787 := bstep (se 1 (by rfl) ⟨4006340, by rfl⟩ : syracuseStep 5341787 = 8012681) B8012681
theorem B4328473 : Blo 1052612 4328473 := bstep (se 2 (by rfl) ⟨1623177, by rfl⟩ : syracuseStep 4328473 = 3246355) B3246355
theorem B3608345 : Blo 1052612 3608345 := bstep (se 2 (by rfl) ⟨1353129, by rfl⟩ : syracuseStep 3608345 = 2706259) B2706259
theorem B1052831 : Blo 1052612 1052831 := bstep (se 1 (by rfl) ⟨789623, by rfl⟩ : syracuseStep 1052831 = 1579247) B1579247
theorem B1053311 : Blo 1052612 1053311 := bstep (se 1 (by rfl) ⟨789983, by rfl⟩ : syracuseStep 1053311 = 1579967) B1579967
theorem B6001289 : Blo 1052612 6001289 := bstep (se 2 (by rfl) ⟨2250483, by rfl⟩ : syracuseStep 6001289 = 4500967) B4500967
theorem B1053467 : Blo 1052612 1053467 := bstep (se 1 (by rfl) ⟨790100, by rfl⟩ : syracuseStep 1053467 = 1580201) B1580201
theorem B1053727 : Blo 1052612 1053727 := bstep (se 1 (by rfl) ⟨790295, by rfl⟩ : syracuseStep 1053727 = 1580591) B1580591
theorem B1053979 : Blo 1052612 1053979 := bstep (se 1 (by rfl) ⟨790484, by rfl⟩ : syracuseStep 1053979 = 1580969) B1580969
theorem B6003179 : Blo 1052612 6003179 := bstep (se 1 (by rfl) ⟨4502384, by rfl⟩ : syracuseStep 6003179 = 9004769) B9004769
theorem B5708303 : Blo 1052612 5708303 := bstep (se 1 (by rfl) ⟨4281227, by rfl⟩ : syracuseStep 5708303 = 8562455) B8562455
theorem B28809917 : Blo 1052612 28809917 := bstep (se 3 (by rfl) ⟨5401859, by rfl⟩ : syracuseStep 28809917 = 10803719) B10803719
theorem B46177229 : Blo 1052612 46177229 := bstep (se 3 (by rfl) ⟨8658230, by rfl⟩ : syracuseStep 46177229 = 17316461) B17316461
theorem B29203901 : Blo 1052612 29203901 := bstep (se 3 (by rfl) ⟨5475731, by rfl⟩ : syracuseStep 29203901 = 10951463) B10951463
theorem B1056303 : Blo 1052612 1056303 := bstep (se 1 (by rfl) ⟨792227, by rfl⟩ : syracuseStep 1056303 = 1584455) B1584455
theorem B20258423 : Blo 1052612 20258423 := bstep (se 1 (by rfl) ⟨15193817, by rfl⟩ : syracuseStep 20258423 = 30387635) B30387635
theorem B1056463 : Blo 1052612 1056463 := bstep (se 1 (by rfl) ⟨792347, by rfl⟩ : syracuseStep 1056463 = 1584695) B1584695
theorem B1581353 : Blo 1052612 1581353 := bstep (se 2 (by rfl) ⟨593007, by rfl⟩ : syracuseStep 1581353 = 1186015) B1186015
theorem B1188607 : Blo 1052612 1188607 := bstep (se 1 (by rfl) ⟨891455, by rfl⟩ : syracuseStep 1188607 = 1782911) B1782911
theorem B8004419 : Blo 1052612 8004419 := bstep (se 1 (by rfl) ⟨6003314, by rfl⟩ : syracuseStep 8004419 = 12006629) B12006629
theorem B1778503 : Blo 1052612 1778503 := bstep (se 1 (by rfl) ⟨1333877, by rfl⟩ : syracuseStep 1778503 = 2667755) B2667755
theorem B1582031 : Blo 1052612 1582031 := bstep (se 1 (by rfl) ⟨1186523, by rfl⟩ : syracuseStep 1582031 = 2373047) B2373047
theorem B4564193 : Blo 1052612 4564193 := bstep (se 2 (by rfl) ⟨1711572, by rfl⟩ : syracuseStep 4564193 = 3423145) B3423145
theorem B1582391 : Blo 1052612 1582391 := bstep (se 1 (by rfl) ⟨1186793, by rfl⟩ : syracuseStep 1582391 = 2373587) B2373587
theorem B1582457 : Blo 1052612 1582457 := bstep (se 2 (by rfl) ⟨593421, by rfl⟩ : syracuseStep 1582457 = 1186843) B1186843
theorem B1582505 : Blo 1052612 1582505 := bstep (se 2 (by rfl) ⟨593439, by rfl⟩ : syracuseStep 1582505 = 1186879) B1186879
theorem B1713755 : Blo 1052612 1713755 := bstep (se 1 (by rfl) ⟨1285316, by rfl⟩ : syracuseStep 1713755 = 2570633) B2570633
theorem B1583159 : Blo 1052612 1583159 := bstep (se 1 (by rfl) ⟨1187369, by rfl⟩ : syracuseStep 1583159 = 2374739) B2374739
theorem B13510739 : Blo 1052612 13510739 := bstep (se 1 (by rfl) ⟨10133054, by rfl⟩ : syracuseStep 13510739 = 20266109) B20266109
theorem B1583567 : Blo 1052612 1583567 := bstep (se 1 (by rfl) ⟨1187675, by rfl⟩ : syracuseStep 1583567 = 2375351) B2375351
theorem B2370023 : Blo 1052612 2370023 := bstep (se 1 (by rfl) ⟨1777517, by rfl⟩ : syracuseStep 2370023 = 3555035) B3555035
theorem B2370401 : Blo 1052612 2370401 := bstep (se 2 (by rfl) ⟨888900, by rfl⟩ : syracuseStep 2370401 = 1777801) B1777801
theorem B1583975 : Blo 1052612 1583975 := bstep (se 1 (by rfl) ⟨1187981, by rfl⟩ : syracuseStep 1583975 = 2375963) B2375963
theorem B4008953 : Blo 1052612 4008953 := bstep (se 2 (by rfl) ⟨1503357, by rfl⟩ : syracuseStep 4008953 = 3006715) B3006715
theorem B23145517 : Blo 1052612 23145517 := bstep (se 3 (by rfl) ⟨4339784, by rfl⟩ : syracuseStep 23145517 = 8679569) B8679569
theorem B1584335 : Blo 1052612 1584335 := bstep (se 1 (by rfl) ⟨1188251, by rfl⟩ : syracuseStep 1584335 = 2376503) B2376503
theorem B1584359 : Blo 1052612 1584359 := bstep (se 1 (by rfl) ⟨1188269, by rfl⟩ : syracuseStep 1584359 = 2376539) B2376539
theorem B1584575 : Blo 1052612 1584575 := bstep (se 1 (by rfl) ⟨1188431, by rfl⟩ : syracuseStep 1584575 = 2376863) B2376863
theorem B6008327 : Blo 1052612 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B2666155 : Blo 1052612 2666155 := bstep (se 1 (by rfl) ⟨1999616, by rfl⟩ : syracuseStep 2666155 = 3999233) B3999233
theorem B1584905 : Blo 1052612 1584905 := bstep (se 2 (by rfl) ⟨594339, by rfl⟩ : syracuseStep 1584905 = 1188679) B1188679
theorem B6172745 : Blo 1052612 6172745 := bstep (se 2 (by rfl) ⟨2314779, by rfl⟩ : syracuseStep 6172745 = 4629559) B4629559
theorem B1781851 : Blo 1052612 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B2372543 : Blo 1052612 2372543 := bstep (se 1 (by rfl) ⟨1779407, by rfl⟩ : syracuseStep 2372543 = 3558815) B3558815
theorem B4109609 : Blo 1052612 4109609 := bstep (se 2 (by rfl) ⟨1541103, by rfl⟩ : syracuseStep 4109609 = 3082207) B3082207
theorem B4011383 : Blo 1052612 4011383 := bstep (se 1 (by rfl) ⟨3008537, by rfl⟩ : syracuseStep 4011383 = 6017075) B6017075
theorem B1422751 : Blo 1052612 1422751 := bstep (se 1 (by rfl) ⟨1067063, by rfl⟩ : syracuseStep 1422751 = 2134127) B2134127
theorem B8009279 : Blo 1052612 8009279 := bstep (se 1 (by rfl) ⟨6006959, by rfl⟩ : syracuseStep 8009279 = 12013919) B12013919
theorem B2373479 : Blo 1052612 2373479 := bstep (se 1 (by rfl) ⟨1780109, by rfl⟩ : syracuseStep 2373479 = 3560219) B3560219
theorem B3553469 : Blo 1052612 3553469 := bstep (se 3 (by rfl) ⟨666275, by rfl⟩ : syracuseStep 3553469 = 1332551) B1332551
theorem B3848467 : Blo 1052612 3848467 := bstep (se 1 (by rfl) ⟨2886350, by rfl⟩ : syracuseStep 3848467 = 5772701) B5772701
theorem B4569583 : Blo 1052612 4569583 := bstep (se 1 (by rfl) ⟨3427187, by rfl⟩ : syracuseStep 4569583 = 6854375) B6854375
theorem B3554387 : Blo 1052612 3554387 := bstep (se 1 (by rfl) ⟨2665790, by rfl⟩ : syracuseStep 3554387 = 5331581) B5331581
theorem B2669881 : Blo 1052612 2669881 := bstep (se 2 (by rfl) ⟨1001205, by rfl⟩ : syracuseStep 2669881 = 2002411) B2002411
theorem B2998367 : Blo 1052612 2998367 := bstep (se 1 (by rfl) ⟨2248775, by rfl⟩ : syracuseStep 2998367 = 4497551) B4497551
theorem B2375783 : Blo 1052612 2375783 := bstep (se 1 (by rfl) ⟨1781837, by rfl⟩ : syracuseStep 2375783 = 3563675) B3563675
theorem B2672311 : Blo 1052612 2672311 := bstep (se 1 (by rfl) ⟨2004233, by rfl⟩ : syracuseStep 2672311 = 4008467) B4008467
theorem B6014843 : Blo 1052612 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B67717087 : Blo 1052612 67717087 := bstep (se 1 (by rfl) ⟨50787815, by rfl⟩ : syracuseStep 67717087 = 101575631) B101575631
theorem B5065031 : Blo 1052612 5065031 := bstep (se 1 (by rfl) ⟨3798773, by rfl⟩ : syracuseStep 5065031 = 7597547) B7597547
theorem B4803047 : Blo 1052612 4803047 := bstep (se 1 (by rfl) ⟨3602285, by rfl⟩ : syracuseStep 4803047 = 7204571) B7204571
theorem B6180403 : Blo 1052612 6180403 := bstep (se 1 (by rfl) ⟨4635302, by rfl⟩ : syracuseStep 6180403 = 9270605) B9270605
theorem B3559247 : Blo 1052612 3559247 := bstep (se 1 (by rfl) ⟨2669435, by rfl⟩ : syracuseStep 3559247 = 5338871) B5338871
theorem B18076087 : Blo 1052612 18076087 := bstep (se 1 (by rfl) ⟨13557065, by rfl⟩ : syracuseStep 18076087 = 27114131) B27114131
theorem B68539283 : Blo 1052612 68539283 := bstep (se 1 (by rfl) ⟨51404462, by rfl⟩ : syracuseStep 68539283 = 102808925) B102808925
theorem B3855863 : Blo 1052612 3855863 := bstep (se 1 (by rfl) ⟨2891897, by rfl⟩ : syracuseStep 3855863 = 5783795) B5783795
theorem B3003959 : Blo 1052612 3003959 := bstep (se 1 (by rfl) ⟨2252969, by rfl⟩ : syracuseStep 3003959 = 4505939) B4505939
theorem B15227261 : Blo 1052612 15227261 := bstep (se 3 (by rfl) ⟨2855111, by rfl⟩ : syracuseStep 15227261 = 5710223) B5710223
theorem B3562217 : Blo 1052612 3562217 := bstep (se 2 (by rfl) ⟨1335831, by rfl⟩ : syracuseStep 3562217 = 2671663) B2671663
theorem B3563999 : Blo 1052612 3563999 := bstep (se 1 (by rfl) ⟨2672999, by rfl⟩ : syracuseStep 3563999 = 5345999) B5345999
theorem B13525865 : Blo 1052612 13525865 := bstep (se 2 (by rfl) ⟨5072199, by rfl⟩ : syracuseStep 13525865 = 10144399) B10144399
theorem B5334011 : Blo 1052612 5334011 := bstep (se 1 (by rfl) ⟨4000508, by rfl⟩ : syracuseStep 5334011 = 8001017) B8001017
theorem B2254063 : Blo 1052612 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B12805775 : Blo 1052612 12805775 := bstep (se 1 (by rfl) ⟨9604331, by rfl⟩ : syracuseStep 12805775 = 19208663) B19208663
theorem B12183743 : Blo 1052612 12183743 := bstep (se 1 (by rfl) ⟨9137807, by rfl⟩ : syracuseStep 12183743 = 18275615) B18275615
theorem B36498023 : Blo 1052612 36498023 := bstep (se 1 (by rfl) ⟨27373517, by rfl⟩ : syracuseStep 36498023 = 54747035) B54747035
theorem B5336441 : Blo 1052612 5336441 := bstep (se 2 (by rfl) ⟨2001165, by rfl⟩ : syracuseStep 5336441 = 4002331) B4002331
theorem B1601051 : Blo 1052612 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B1502879 : Blo 1052612 1502879 := bstep (se 1 (by rfl) ⟨1127159, by rfl⟩ : syracuseStep 1502879 = 2254319) B2254319
theorem B2847059 : Blo 1052612 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B9008495 : Blo 1052612 9008495 := bstep (se 1 (by rfl) ⟨6756371, by rfl⟩ : syracuseStep 9008495 = 13512743) B13512743
theorem B5701099 : Blo 1052612 5701099 := bstep (se 1 (by rfl) ⟨4275824, by rfl⟩ : syracuseStep 5701099 = 8551649) B8551649
theorem B1998751 : Blo 1052612 1998751 := bstep (se 1 (by rfl) ⟨1499063, by rfl⟩ : syracuseStep 1998751 = 2998127) B2998127
theorem B1998911 : Blo 1052612 1998911 := bstep (se 1 (by rfl) ⟨1499183, by rfl⟩ : syracuseStep 1998911 = 2998367) B2998367
theorem B3376687 : Blo 1052612 3376687 := bstep (se 1 (by rfl) ⟨2532515, by rfl⟩ : syracuseStep 3376687 = 5065031) B5065031
theorem B96405797 : Blo 1052612 96405797 := bstep (se 4 (by rfl) ⟨9038043, by rfl⟩ : syracuseStep 96405797 = 18076087) B18076087
theorem B4000859 : Blo 1052612 4000859 := bstep (se 1 (by rfl) ⟨3000644, by rfl⟩ : syracuseStep 4000859 = 6001289) B6001289
theorem B2002639 : Blo 1052612 2002639 := bstep (se 1 (by rfl) ⟨1501979, by rfl⟩ : syracuseStep 2002639 = 3003959) B3003959
theorem B5771297 : Blo 1052612 5771297 := bstep (se 2 (by rfl) ⟨2164236, by rfl⟩ : syracuseStep 5771297 = 4328473) B4328473
theorem B4002119 : Blo 1052612 4002119 := bstep (se 1 (by rfl) ⟨3001589, by rfl⟩ : syracuseStep 4002119 = 6003179) B6003179
theorem B3805535 : Blo 1052612 3805535 := bstep (se 1 (by rfl) ⟨2854151, by rfl⟩ : syracuseStep 3805535 = 5708303) B5708303
theorem B19206611 : Blo 1052612 19206611 := bstep (se 1 (by rfl) ⟨14404958, by rfl⟩ : syracuseStep 19206611 = 28809917) B28809917
theorem B19469267 : Blo 1052612 19469267 := bstep (se 1 (by rfl) ⟨14601950, by rfl⟩ : syracuseStep 19469267 = 29203901) B29203901
theorem B13505615 : Blo 1052612 13505615 := bstep (se 1 (by rfl) ⟨10129211, by rfl⟩ : syracuseStep 13505615 = 20258423) B20258423
theorem B1054235 : Blo 1052612 1054235 := bstep (se 1 (by rfl) ⟨790676, by rfl⟩ : syracuseStep 1054235 = 1581353) B1581353
theorem B9017243 : Blo 1052612 9017243 := bstep (se 1 (by rfl) ⟨6762932, by rfl⟩ : syracuseStep 9017243 = 13525865) B13525865
theorem B1054687 : Blo 1052612 1054687 := bstep (se 1 (by rfl) ⟨791015, by rfl⟩ : syracuseStep 1054687 = 1582031) B1582031
theorem B1054927 : Blo 1052612 1054927 := bstep (se 1 (by rfl) ⟨791195, by rfl⟩ : syracuseStep 1054927 = 1582391) B1582391
theorem B1054971 : Blo 1052612 1054971 := bstep (se 1 (by rfl) ⟨791228, by rfl⟩ : syracuseStep 1054971 = 1582457) B1582457
theorem B1055003 : Blo 1052612 1055003 := bstep (se 1 (by rfl) ⟨791252, by rfl⟩ : syracuseStep 1055003 = 1582505) B1582505
theorem B1055439 : Blo 1052612 1055439 := bstep (se 1 (by rfl) ⟨791579, by rfl⟩ : syracuseStep 1055439 = 1583159) B1583159
theorem B1055711 : Blo 1052612 1055711 := bstep (se 1 (by rfl) ⟨791783, by rfl⟩ : syracuseStep 1055711 = 1583567) B1583567
theorem B1580015 : Blo 1052612 1580015 := bstep (se 1 (by rfl) ⟨1185011, by rfl⟩ : syracuseStep 1580015 = 2370023) B2370023
theorem B1580267 : Blo 1052612 1580267 := bstep (se 1 (by rfl) ⟨1185200, by rfl⟩ : syracuseStep 1580267 = 2370401) B2370401
theorem B1055983 : Blo 1052612 1055983 := bstep (se 1 (by rfl) ⟨791987, by rfl⟩ : syracuseStep 1055983 = 1583975) B1583975
theorem B1056223 : Blo 1052612 1056223 := bstep (se 1 (by rfl) ⟨792167, by rfl⟩ : syracuseStep 1056223 = 1584335) B1584335
theorem B1056239 : Blo 1052612 1056239 := bstep (se 1 (by rfl) ⟨792179, by rfl⟩ : syracuseStep 1056239 = 1584359) B1584359
theorem B1056383 : Blo 1052612 1056383 := bstep (se 1 (by rfl) ⟨792287, by rfl⟩ : syracuseStep 1056383 = 1584575) B1584575
theorem B4005551 : Blo 1052612 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B1056603 : Blo 1052612 1056603 := bstep (se 1 (by rfl) ⟨792452, by rfl⟩ : syracuseStep 1056603 = 1584905) B1584905
theorem B1581695 : Blo 1052612 1581695 := bstep (se 1 (by rfl) ⟨1186271, by rfl⟩ : syracuseStep 1581695 = 2372543) B2372543
theorem B6005663 : Blo 1052612 6005663 := bstep (se 1 (by rfl) ⟨4504247, by rfl⟩ : syracuseStep 6005663 = 9008495) B9008495
theorem B1582319 : Blo 1052612 1582319 := bstep (se 1 (by rfl) ⟨1186739, by rfl⟩ : syracuseStep 1582319 = 2373479) B2373479
theorem B4269469 : Blo 1052612 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B2368979 : Blo 1052612 2368979 := bstep (se 1 (by rfl) ⟨1776734, by rfl⟩ : syracuseStep 2368979 = 3553469) B3553469
theorem B4007677 : Blo 1052612 4007677 := bstep (se 3 (by rfl) ⟨751439, by rfl⟩ : syracuseStep 4007677 = 1502879) B1502879
theorem B2369591 : Blo 1052612 2369591 := bstep (se 1 (by rfl) ⟨1777193, by rfl⟩ : syracuseStep 2369591 = 3554387) B3554387
theorem B2665001 : Blo 1052612 2665001 := bstep (se 2 (by rfl) ⟨999375, by rfl⟩ : syracuseStep 2665001 = 1998751) B1998751
theorem B1583855 : Blo 1052612 1583855 := bstep (se 1 (by rfl) ⟨1187891, by rfl⟩ : syracuseStep 1583855 = 2375783) B2375783
theorem B16460653 : Blo 1052612 16460653 := bstep (se 3 (by rfl) ⟨3086372, by rfl⟩ : syracuseStep 16460653 = 6172745) B6172745
theorem B15182747 : Blo 1052612 15182747 := bstep (se 1 (by rfl) ⟨11387060, by rfl⟩ : syracuseStep 15182747 = 22774121) B22774121
theorem B32484331 : Blo 1052612 32484331 := bstep (se 1 (by rfl) ⟨24363248, by rfl⟩ : syracuseStep 32484331 = 48726497) B48726497
theorem B1584809 : Blo 1052612 1584809 := bstep (se 2 (by rfl) ⟨594303, by rfl⟩ : syracuseStep 1584809 = 1188607) B1188607
theorem B2371337 : Blo 1052612 2371337 := bstep (se 2 (by rfl) ⟨889251, by rfl⟩ : syracuseStep 2371337 = 1778503) B1778503
theorem B4009895 : Blo 1052612 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B2372831 : Blo 1052612 2372831 := bstep (se 1 (by rfl) ⟨1779623, by rfl⟩ : syracuseStep 2372831 = 3559247) B3559247
theorem B45692855 : Blo 1052612 45692855 := bstep (se 1 (by rfl) ⟨34269641, by rfl⟩ : syracuseStep 45692855 = 68539283) B68539283
theorem B4570013 : Blo 1052612 4570013 := bstep (se 3 (by rfl) ⟨856877, by rfl⟩ : syracuseStep 4570013 = 1713755) B1713755
theorem B2374811 : Blo 1052612 2374811 := bstep (se 1 (by rfl) ⟨1781108, by rfl⟩ : syracuseStep 2374811 = 3562217) B3562217
theorem B8240537 : Blo 1052612 8240537 := bstep (se 2 (by rfl) ⟨3090201, by rfl⟩ : syracuseStep 8240537 = 6180403) B6180403
theorem B3554873 : Blo 1052612 3554873 := bstep (se 2 (by rfl) ⟨1333077, by rfl⟩ : syracuseStep 3554873 = 2666155) B2666155
theorem B2375801 : Blo 1052612 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B2375999 : Blo 1052612 2375999 := bstep (se 1 (by rfl) ⟨1781999, by rfl⟩ : syracuseStep 2375999 = 3563999) B3563999
theorem B32489981 : Blo 1052612 32489981 := bstep (se 3 (by rfl) ⟨6091871, by rfl⟩ : syracuseStep 32489981 = 12183743) B12183743
theorem B3556007 : Blo 1052612 3556007 := bstep (se 1 (by rfl) ⟨2667005, by rfl⟩ : syracuseStep 3556007 = 5334011) B5334011
theorem B8537183 : Blo 1052612 8537183 := bstep (se 1 (by rfl) ⟨6402887, by rfl⟩ : syracuseStep 8537183 = 12805775) B12805775
theorem B24332015 : Blo 1052612 24332015 := bstep (se 1 (by rfl) ⟨18249011, by rfl⟩ : syracuseStep 24332015 = 36498023) B36498023
theorem B2672635 : Blo 1052612 2672635 := bstep (se 1 (by rfl) ⟨2004476, by rfl⟩ : syracuseStep 2672635 = 4008953) B4008953
theorem B3557627 : Blo 1052612 3557627 := bstep (se 1 (by rfl) ⟨2668220, by rfl⟩ : syracuseStep 3557627 = 5336441) B5336441
theorem B5131289 : Blo 1052612 5131289 := bstep (se 2 (by rfl) ⟨1924233, by rfl⟩ : syracuseStep 5131289 = 3848467) B3848467
theorem B2739739 : Blo 1052612 2739739 := bstep (se 1 (by rfl) ⟨2054804, by rfl⟩ : syracuseStep 2739739 = 4109609) B4109609
theorem B2674255 : Blo 1052612 2674255 := bstep (se 1 (by rfl) ⟨2005691, by rfl⟩ : syracuseStep 2674255 = 4011383) B4011383
theorem B3559841 : Blo 1052612 3559841 := bstep (se 2 (by rfl) ⟨1334940, by rfl⟩ : syracuseStep 3559841 = 2669881) B2669881
theorem B9622253 : Blo 1052612 9622253 := bstep (se 3 (by rfl) ⟨1804172, by rfl⟩ : syracuseStep 9622253 = 3608345) B3608345
theorem B361157797 : Blo 1052612 361157797 := bstep (se 4 (by rfl) ⟨33858543, by rfl⟩ : syracuseStep 361157797 = 67717087) B67717087
theorem B3561191 : Blo 1052612 3561191 := bstep (se 1 (by rfl) ⟨2670893, by rfl⟩ : syracuseStep 3561191 = 5341787) B5341787
theorem B3005417 : Blo 1052612 3005417 := bstep (se 2 (by rfl) ⟨1127031, by rfl⟩ : syracuseStep 3005417 = 2254063) B2254063
theorem B3202031 : Blo 1052612 3202031 := bstep (se 1 (by rfl) ⟨2401523, by rfl⟩ : syracuseStep 3202031 = 4803047) B4803047
theorem B3563081 : Blo 1052612 3563081 := bstep (se 2 (by rfl) ⟨1336155, by rfl⟩ : syracuseStep 3563081 = 2672311) B2672311
theorem B48684725 : Blo 1052612 48684725 := bstep (se 5 (by rfl) ⟨2282096, by rfl⟩ : syracuseStep 48684725 = 4564193) B4564193
theorem B10282301 : Blo 1052612 10282301 := bstep (se 3 (by rfl) ⟨1927931, by rfl⟩ : syracuseStep 10282301 = 3855863) B3855863
theorem B30860689 : Blo 1052612 30860689 := bstep (se 2 (by rfl) ⟨11572758, by rfl⟩ : syracuseStep 30860689 = 23145517) B23145517
theorem B10151507 : Blo 1052612 10151507 := bstep (se 1 (by rfl) ⟨7613630, by rfl⟩ : syracuseStep 10151507 = 15227261) B15227261
theorem B5336279 : Blo 1052612 5336279 := bstep (se 1 (by rfl) ⟨4002209, by rfl⟩ : syracuseStep 5336279 = 8004419) B8004419
theorem B9007159 : Blo 1052612 9007159 := bstep (se 1 (by rfl) ⟨6755369, by rfl⟩ : syracuseStep 9007159 = 13510739) B13510739
theorem B1897001 : Blo 1052612 1897001 := bstep (se 2 (by rfl) ⟨711375, by rfl⟩ : syracuseStep 1897001 = 1422751) B1422751
theorem B123139277 : Blo 1052612 123139277 := bstep (se 3 (by rfl) ⟨23088614, by rfl⟩ : syracuseStep 123139277 = 46177229) B46177229
theorem B1898039 : Blo 1052612 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B6092777 : Blo 1052612 6092777 := bstep (se 2 (by rfl) ⟨2284791, by rfl⟩ : syracuseStep 6092777 = 4569583) B4569583
theorem B5339519 : Blo 1052612 5339519 := bstep (se 1 (by rfl) ⟨4004639, by rfl⟩ : syracuseStep 5339519 = 8009279) B8009279
theorem B7601465 : Blo 1052612 7601465 := bstep (se 2 (by rfl) ⟨2850549, by rfl⟩ : syracuseStep 7601465 = 5701099) B5701099
theorem B21659987 : Blo 1052612 21659987 := bstep (se 1 (by rfl) ⟨16244990, by rfl⟩ : syracuseStep 21659987 = 32489981) B32489981
theorem B5343569 : Blo 1052612 5343569 := bstep (se 2 (by rfl) ⟨2003838, by rfl⟩ : syracuseStep 5343569 = 4007677) B4007677
theorem B12979511 : Blo 1052612 12979511 := bstep (se 1 (by rfl) ⟨9734633, by rfl⟩ : syracuseStep 12979511 = 19469267) B19469267
theorem B27070685 : Blo 1052612 27070685 := bstep (se 3 (by rfl) ⟨5075753, by rfl⟩ : syracuseStep 27070685 = 10151507) B10151507
theorem B64885373 : Blo 1052612 64885373 := bstep (se 3 (by rfl) ⟨12166007, by rfl⟩ : syracuseStep 64885373 = 24332015) B24332015
theorem B2003611 : Blo 1052612 2003611 := bstep (se 1 (by rfl) ⟨1502708, by rfl⟩ : syracuseStep 2003611 = 3005417) B3005417
theorem B2134687 : Blo 1052612 2134687 := bstep (se 1 (by rfl) ⟨1601015, by rfl⟩ : syracuseStep 2134687 = 3202031) B3202031
theorem B1053343 : Blo 1052612 1053343 := bstep (se 1 (by rfl) ⟨790007, by rfl⟩ : syracuseStep 1053343 = 1580015) B1580015
theorem B1053511 : Blo 1052612 1053511 := bstep (se 1 (by rfl) ⟨790133, by rfl⟩ : syracuseStep 1053511 = 1580267) B1580267
theorem B173249765 : Blo 1052612 173249765 := bstep (se 4 (by rfl) ⟨16242165, by rfl⟩ : syracuseStep 173249765 = 32484331) B32484331
theorem B1054463 : Blo 1052612 1054463 := bstep (se 1 (by rfl) ⟨790847, by rfl⟩ : syracuseStep 1054463 = 1581695) B1581695
theorem B4003775 : Blo 1052612 4003775 := bstep (se 1 (by rfl) ⟨3002831, by rfl⟩ : syracuseStep 4003775 = 6005663) B6005663
theorem B1054879 : Blo 1052612 1054879 := bstep (se 1 (by rfl) ⟨791159, by rfl⟩ : syracuseStep 1054879 = 1582319) B1582319
theorem B1926174917 : Blo 1052612 1926174917 := bstep (se 4 (by rfl) ⟨180578898, by rfl⟩ : syracuseStep 1926174917 = 361157797) B361157797
theorem B6854867 : Blo 1052612 6854867 := bstep (se 1 (by rfl) ⟨5141150, by rfl⟩ : syracuseStep 6854867 = 10282301) B10282301
theorem B1579319 : Blo 1052612 1579319 := bstep (se 1 (by rfl) ⟨1184489, by rfl⟩ : syracuseStep 1579319 = 2368979) B2368979
theorem B1579727 : Blo 1052612 1579727 := bstep (se 1 (by rfl) ⟨1184795, by rfl⟩ : syracuseStep 1579727 = 2369591) B2369591
theorem B1776667 : Blo 1052612 1776667 := bstep (se 1 (by rfl) ⟨1332500, by rfl⟩ : syracuseStep 1776667 = 2665001) B2665001
theorem B1055903 : Blo 1052612 1055903 := bstep (se 1 (by rfl) ⟨791927, by rfl⟩ : syracuseStep 1055903 = 1583855) B1583855
theorem B1056539 : Blo 1052612 1056539 := bstep (se 1 (by rfl) ⟨792404, by rfl⟩ : syracuseStep 1056539 = 1584809) B1584809
theorem B1580891 : Blo 1052612 1580891 := bstep (se 1 (by rfl) ⟨1185668, by rfl⟩ : syracuseStep 1580891 = 2371337) B2371337
theorem B82092851 : Blo 1052612 82092851 := bstep (se 1 (by rfl) ⟨61569638, by rfl⟩ : syracuseStep 82092851 = 123139277) B123139277
theorem B1581887 : Blo 1052612 1581887 := bstep (se 1 (by rfl) ⟨1186415, by rfl⟩ : syracuseStep 1581887 = 2372831) B2372831
theorem B1583207 : Blo 1052612 1583207 := bstep (se 1 (by rfl) ⟨1187405, by rfl⟩ : syracuseStep 1583207 = 2374811) B2374811
theorem B2369915 : Blo 1052612 2369915 := bstep (se 1 (by rfl) ⟨1777436, by rfl⟩ : syracuseStep 2369915 = 3554873) B3554873
theorem B1583867 : Blo 1052612 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B1583999 : Blo 1052612 1583999 := bstep (se 1 (by rfl) ⟨1187999, by rfl⟩ : syracuseStep 1583999 = 2375999) B2375999
theorem B2370671 : Blo 1052612 2370671 := bstep (se 1 (by rfl) ⟨1778003, by rfl⟩ : syracuseStep 2370671 = 3556007) B3556007
theorem B2371751 : Blo 1052612 2371751 := bstep (se 1 (by rfl) ⟨1778813, by rfl⟩ : syracuseStep 2371751 = 3557627) B3557627
theorem B64270531 : Blo 1052612 64270531 := bstep (se 1 (by rfl) ⟨48202898, by rfl⟩ : syracuseStep 64270531 = 96405797) B96405797
theorem B3420859 : Blo 1052612 3420859 := bstep (se 1 (by rfl) ⟨2565644, by rfl⟩ : syracuseStep 3420859 = 5131289) B5131289
theorem B2667239 : Blo 1052612 2667239 := bstep (se 1 (by rfl) ⟨2000429, by rfl⟩ : syracuseStep 2667239 = 4000859) B4000859
theorem B4502249 : Blo 1052612 4502249 := bstep (se 2 (by rfl) ⟨1688343, by rfl⟩ : syracuseStep 4502249 = 3376687) B3376687
theorem B2668079 : Blo 1052612 2668079 := bstep (se 1 (by rfl) ⟨2001059, by rfl⟩ : syracuseStep 2668079 = 4002119) B4002119
theorem B2537023 : Blo 1052612 2537023 := bstep (se 1 (by rfl) ⟨1902767, by rfl⟩ : syracuseStep 2537023 = 3805535) B3805535
theorem B2373227 : Blo 1052612 2373227 := bstep (se 1 (by rfl) ⟨1779920, by rfl⟩ : syracuseStep 2373227 = 3559841) B3559841
theorem B2374127 : Blo 1052612 2374127 := bstep (se 1 (by rfl) ⟨1780595, by rfl⟩ : syracuseStep 2374127 = 3561191) B3561191
theorem B6011495 : Blo 1052612 6011495 := bstep (se 1 (by rfl) ⟨4508621, by rfl⟩ : syracuseStep 6011495 = 9017243) B9017243
theorem B5061437 : Blo 1052612 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B3652985 : Blo 1052612 3652985 := bstep (se 2 (by rfl) ⟨1369869, by rfl⟩ : syracuseStep 3652985 = 2739739) B2739739
theorem B2670185 : Blo 1052612 2670185 := bstep (se 2 (by rfl) ⟨1001319, by rfl⟩ : syracuseStep 2670185 = 2002639) B2002639
theorem B2375387 : Blo 1052612 2375387 := bstep (se 1 (by rfl) ⟨1781540, by rfl⟩ : syracuseStep 2375387 = 3563081) B3563081
theorem B2670367 : Blo 1052612 2670367 := bstep (se 1 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 2670367 = 4005551) B4005551
theorem B32456483 : Blo 1052612 32456483 := bstep (se 1 (by rfl) ⟨24342362, by rfl⟩ : syracuseStep 32456483 = 48684725) B48684725
theorem B12009545 : Blo 1052612 12009545 := bstep (se 2 (by rfl) ⟨4503579, by rfl⟩ : syracuseStep 12009545 = 9007159) B9007159
theorem B3557519 : Blo 1052612 3557519 := bstep (se 1 (by rfl) ⟨2668139, by rfl⟩ : syracuseStep 3557519 = 5336279) B5336279
theorem B2673263 : Blo 1052612 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B1264667 : Blo 1052612 1264667 := bstep (se 1 (by rfl) ⟨948500, by rfl⟩ : syracuseStep 1264667 = 1897001) B1897001
theorem B20270573 : Blo 1052612 20270573 := bstep (se 3 (by rfl) ⟨3800732, by rfl⟩ : syracuseStep 20270573 = 7601465) B7601465
theorem B30461903 : Blo 1052612 30461903 := bstep (se 1 (by rfl) ⟨22846427, by rfl⟩ : syracuseStep 30461903 = 45692855) B45692855
theorem B3559679 : Blo 1052612 3559679 := bstep (se 1 (by rfl) ⟨2669759, by rfl⟩ : syracuseStep 3559679 = 5339519) B5339519
theorem B5493691 : Blo 1052612 5493691 := bstep (se 1 (by rfl) ⟨4120268, by rfl⟩ : syracuseStep 5493691 = 8240537) B8240537
theorem B1332607 : Blo 1052612 1332607 := bstep (se 1 (by rfl) ⟨999455, by rfl⟩ : syracuseStep 1332607 = 1998911) B1998911
theorem B15390125 : Blo 1052612 15390125 := bstep (se 3 (by rfl) ⟨2885648, by rfl⟩ : syracuseStep 15390125 = 5771297) B5771297
theorem B5691455 : Blo 1052612 5691455 := bstep (se 1 (by rfl) ⟨4268591, by rfl⟩ : syracuseStep 5691455 = 8537183) B8537183
theorem B41147585 : Blo 1052612 41147585 := bstep (se 2 (by rfl) ⟨15430344, by rfl⟩ : syracuseStep 41147585 = 30860689) B30860689
theorem B5692625 : Blo 1052612 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B3563513 : Blo 1052612 3563513 := bstep (se 2 (by rfl) ⟨1336317, by rfl⟩ : syracuseStep 3563513 = 2672635) B2672635
theorem B12804407 : Blo 1052612 12804407 := bstep (se 1 (by rfl) ⟨9603305, by rfl⟩ : syracuseStep 12804407 = 19206611) B19206611
theorem B6414835 : Blo 1052612 6414835 := bstep (se 1 (by rfl) ⟨4811126, by rfl⟩ : syracuseStep 6414835 = 9622253) B9622253
theorem B9003743 : Blo 1052612 9003743 := bstep (se 1 (by rfl) ⟨6752807, by rfl⟩ : syracuseStep 9003743 = 13505615) B13505615
theorem B21947537 : Blo 1052612 21947537 := bstep (se 2 (by rfl) ⟨8230326, by rfl⟩ : syracuseStep 21947537 = 16460653) B16460653
theorem B3565673 : Blo 1052612 3565673 := bstep (se 2 (by rfl) ⟨1337127, by rfl⟩ : syracuseStep 3565673 = 2674255) B2674255
theorem B16247405 : Blo 1052612 16247405 := bstep (se 3 (by rfl) ⟨3046388, by rfl⟩ : syracuseStep 16247405 = 6092777) B6092777
theorem B10121831 : Blo 1052612 10121831 := bstep (se 1 (by rfl) ⟨7591373, by rfl⟩ : syracuseStep 10121831 = 15182747) B15182747
theorem B3046675 : Blo 1052612 3046675 := bstep (se 1 (by rfl) ⟨2285006, by rfl⟩ : syracuseStep 3046675 = 4570013) B4570013
theorem B8553113 : Blo 1052612 8553113 := bstep (se 2 (by rfl) ⟨3207417, by rfl⟩ : syracuseStep 8553113 = 6414835) B6414835
theorem B8653007 : Blo 1052612 8653007 := bstep (se 1 (by rfl) ⟨6489755, by rfl⟩ : syracuseStep 8653007 = 12979511) B12979511
theorem B43256915 : Blo 1052612 43256915 := bstep (se 1 (by rfl) ⟨32442686, by rfl⟩ : syracuseStep 43256915 = 64885373) B64885373
theorem B10260083 : Blo 1052612 10260083 := bstep (se 1 (by rfl) ⟨7695062, by rfl⟩ : syracuseStep 10260083 = 15390125) B15390125
theorem B1284116611 : Blo 1052612 1284116611 := bstep (se 1 (by rfl) ⟨963087458, by rfl⟩ : syracuseStep 1284116611 = 1926174917) B1926174917
theorem B1052879 : Blo 1052612 1052879 := bstep (se 1 (by rfl) ⟨789659, by rfl⟩ : syracuseStep 1052879 = 1579319) B1579319
theorem B1053151 : Blo 1052612 1053151 := bstep (se 1 (by rfl) ⟨789863, by rfl⟩ : syracuseStep 1053151 = 1579727) B1579727
theorem B27431723 : Blo 1052612 27431723 := bstep (se 1 (by rfl) ⟨20573792, by rfl⟩ : syracuseStep 27431723 = 41147585) B41147585
theorem B1053927 : Blo 1052612 1053927 := bstep (se 1 (by rfl) ⟨790445, by rfl⟩ : syracuseStep 1053927 = 1580891) B1580891
theorem B85694041 : Blo 1052612 85694041 := bstep (se 2 (by rfl) ⟨32135265, by rfl⟩ : syracuseStep 85694041 = 64270531) B64270531
theorem B6002495 : Blo 1052612 6002495 := bstep (se 1 (by rfl) ⟨4501871, by rfl⟩ : syracuseStep 6002495 = 9003743) B9003743
theorem B54728567 : Blo 1052612 54728567 := bstep (se 1 (by rfl) ⟨41046425, by rfl⟩ : syracuseStep 54728567 = 82092851) B82092851
theorem B1054591 : Blo 1052612 1054591 := bstep (se 1 (by rfl) ⟨790943, by rfl⟩ : syracuseStep 1054591 = 1581887) B1581887
theorem B4561145 : Blo 1052612 4561145 := bstep (se 2 (by rfl) ⟨1710429, by rfl⟩ : syracuseStep 4561145 = 3420859) B3420859
theorem B1055471 : Blo 1052612 1055471 := bstep (se 1 (by rfl) ⟨791603, by rfl⟩ : syracuseStep 1055471 = 1583207) B1583207
theorem B1579943 : Blo 1052612 1579943 := bstep (se 1 (by rfl) ⟨1184957, by rfl⟩ : syracuseStep 1579943 = 2369915) B2369915
theorem B1055911 : Blo 1052612 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B1776809 : Blo 1052612 1776809 := bstep (se 2 (by rfl) ⟨666303, by rfl⟩ : syracuseStep 1776809 = 1332607) B1332607
theorem B1055999 : Blo 1052612 1055999 := bstep (se 1 (by rfl) ⟨791999, by rfl⟩ : syracuseStep 1055999 = 1583999) B1583999
theorem B1580447 : Blo 1052612 1580447 := bstep (se 1 (by rfl) ⟨1185335, by rfl⟩ : syracuseStep 1580447 = 2370671) B2370671
theorem B3382697 : Blo 1052612 3382697 := bstep (se 2 (by rfl) ⟨1268511, by rfl⟩ : syracuseStep 3382697 = 2537023) B2537023
theorem B1581167 : Blo 1052612 1581167 := bstep (se 1 (by rfl) ⟨1185875, by rfl⟩ : syracuseStep 1581167 = 2371751) B2371751
theorem B1778159 : Blo 1052612 1778159 := bstep (se 1 (by rfl) ⟨1333619, by rfl⟩ : syracuseStep 1778159 = 2667239) B2667239
theorem B1778719 : Blo 1052612 1778719 := bstep (se 1 (by rfl) ⟨1334039, by rfl⟩ : syracuseStep 1778719 = 2668079) B2668079
theorem B1582151 : Blo 1052612 1582151 := bstep (se 1 (by rfl) ⟨1186613, by rfl⟩ : syracuseStep 1582151 = 2373227) B2373227
theorem B2368889 : Blo 1052612 2368889 := bstep (se 2 (by rfl) ⟨888333, by rfl⟩ : syracuseStep 2368889 = 1776667) B1776667
theorem B1582751 : Blo 1052612 1582751 := bstep (se 1 (by rfl) ⟨1187063, by rfl⟩ : syracuseStep 1582751 = 2374127) B2374127
theorem B4007663 : Blo 1052612 4007663 := bstep (se 1 (by rfl) ⟨3005747, by rfl⟩ : syracuseStep 4007663 = 6011495) B6011495
theorem B2435323 : Blo 1052612 2435323 := bstep (se 1 (by rfl) ⟨1826492, by rfl⟩ : syracuseStep 2435323 = 3652985) B3652985
theorem B1780123 : Blo 1052612 1780123 := bstep (se 1 (by rfl) ⟨1335092, by rfl⟩ : syracuseStep 1780123 = 2670185) B2670185
theorem B1583591 : Blo 1052612 1583591 := bstep (se 1 (by rfl) ⟨1187693, by rfl⟩ : syracuseStep 1583591 = 2375387) B2375387
theorem B21637655 : Blo 1052612 21637655 := bstep (se 1 (by rfl) ⟨16228241, by rfl⟩ : syracuseStep 21637655 = 32456483) B32456483
theorem B8006363 : Blo 1052612 8006363 := bstep (se 1 (by rfl) ⟨6004772, by rfl⟩ : syracuseStep 8006363 = 12009545) B12009545
theorem B2371679 : Blo 1052612 2371679 := bstep (se 1 (by rfl) ⟨1778759, by rfl⟩ : syracuseStep 2371679 = 3557519) B3557519
theorem B1782175 : Blo 1052612 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B13513715 : Blo 1052612 13513715 := bstep (se 1 (by rfl) ⟨10135286, by rfl⟩ : syracuseStep 13513715 = 20270573) B20270573
theorem B2373119 : Blo 1052612 2373119 := bstep (se 1 (by rfl) ⟨1779839, by rfl⟩ : syracuseStep 2373119 = 3559679) B3559679
theorem B2669183 : Blo 1052612 2669183 := bstep (se 1 (by rfl) ⟨2001887, by rfl⟩ : syracuseStep 2669183 = 4003775) B4003775
theorem B4569911 : Blo 1052612 4569911 := bstep (se 1 (by rfl) ⟨3427433, by rfl⟩ : syracuseStep 4569911 = 6854867) B6854867
theorem B2375675 : Blo 1052612 2375675 := bstep (se 1 (by rfl) ⟨1781756, by rfl⟩ : syracuseStep 2375675 = 3563513) B3563513
theorem B8536271 : Blo 1052612 8536271 := bstep (se 1 (by rfl) ⟨6402203, by rfl⟩ : syracuseStep 8536271 = 12804407) B12804407
theorem B14631691 : Blo 1052612 14631691 := bstep (se 1 (by rfl) ⟨10973768, by rfl⟩ : syracuseStep 14631691 = 21947537) B21947537
theorem B2671481 : Blo 1052612 2671481 := bstep (se 2 (by rfl) ⟨1001805, by rfl⟩ : syracuseStep 2671481 = 2003611) B2003611
theorem B7324921 : Blo 1052612 7324921 := bstep (se 2 (by rfl) ⟨2746845, by rfl⟩ : syracuseStep 7324921 = 5493691) B5493691
theorem B2377115 : Blo 1052612 2377115 := bstep (se 1 (by rfl) ⟨1782836, by rfl⟩ : syracuseStep 2377115 = 3565673) B3565673
theorem B10831603 : Blo 1052612 10831603 := bstep (se 1 (by rfl) ⟨8123702, by rfl⟩ : syracuseStep 10831603 = 16247405) B16247405
theorem B3001499 : Blo 1052612 3001499 := bstep (se 1 (by rfl) ⟨2251124, by rfl⟩ : syracuseStep 3001499 = 4502249) B4502249
theorem B3560489 : Blo 1052612 3560489 := bstep (se 2 (by rfl) ⟨1335183, by rfl⟩ : syracuseStep 3560489 = 2670367) B2670367
theorem B14439991 : Blo 1052612 14439991 := bstep (se 1 (by rfl) ⟨10829993, by rfl⟩ : syracuseStep 14439991 = 21659987) B21659987
theorem B3562379 : Blo 1052612 3562379 := bstep (se 1 (by rfl) ⟨2671784, by rfl⟩ : syracuseStep 3562379 = 5343569) B5343569
theorem B20307935 : Blo 1052612 20307935 := bstep (se 1 (by rfl) ⟨15230951, by rfl⟩ : syracuseStep 20307935 = 30461903) B30461903
theorem B18047123 : Blo 1052612 18047123 := bstep (se 1 (by rfl) ⟨13535342, by rfl⟩ : syracuseStep 18047123 = 27070685) B27070685
theorem B115499843 : Blo 1052612 115499843 := bstep (se 1 (by rfl) ⟨86624882, by rfl⟩ : syracuseStep 115499843 = 173249765) B173249765
theorem B3794303 : Blo 1052612 3794303 := bstep (se 1 (by rfl) ⟨2845727, by rfl⟩ : syracuseStep 3794303 = 5691455) B5691455
theorem B3795083 : Blo 1052612 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B2846249 : Blo 1052612 2846249 := bstep (se 2 (by rfl) ⟨1067343, by rfl⟩ : syracuseStep 2846249 = 2134687) B2134687
theorem B3372445 : Blo 1052612 3372445 := bstep (se 3 (by rfl) ⟨632333, by rfl⟩ : syracuseStep 3372445 = 1264667) B1264667
theorem B6747887 : Blo 1052612 6747887 := bstep (se 1 (by rfl) ⟨5060915, by rfl⟩ : syracuseStep 6747887 = 10121831) B10121831
theorem B4062233 : Blo 1052612 4062233 := bstep (se 2 (by rfl) ⟨1523337, by rfl⟩ : syracuseStep 4062233 = 3046675) B3046675
theorem B3374291 : Blo 1052612 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B5702075 : Blo 1052612 5702075 := bstep (se 1 (by rfl) ⟨4276556, by rfl⟩ : syracuseStep 5702075 = 8553113) B8553113
theorem B5768671 : Blo 1052612 5768671 := bstep (se 1 (by rfl) ⟨4326503, by rfl⟩ : syracuseStep 5768671 = 8653007) B8653007
theorem B28837943 : Blo 1052612 28837943 := bstep (se 1 (by rfl) ⟨21628457, by rfl⟩ : syracuseStep 28837943 = 43256915) B43256915
theorem B2000999 : Blo 1052612 2000999 := bstep (se 1 (by rfl) ⟨1500749, by rfl⟩ : syracuseStep 2000999 = 3001499) B3001499
theorem B3247097 : Blo 1052612 3247097 := bstep (se 2 (by rfl) ⟨1217661, by rfl⟩ : syracuseStep 3247097 = 2435323) B2435323
theorem B18287815 : Blo 1052612 18287815 := bstep (se 1 (by rfl) ⟨13715861, by rfl⟩ : syracuseStep 18287815 = 27431723) B27431723
theorem B4001663 : Blo 1052612 4001663 := bstep (se 1 (by rfl) ⟨3001247, by rfl⟩ : syracuseStep 4001663 = 6002495) B6002495
theorem B1053295 : Blo 1052612 1053295 := bstep (se 1 (by rfl) ⟨789971, by rfl⟩ : syracuseStep 1053295 = 1579943) B1579943
theorem B1184539 : Blo 1052612 1184539 := bstep (se 1 (by rfl) ⟨888404, by rfl⟩ : syracuseStep 1184539 = 1776809) B1776809
theorem B1053631 : Blo 1052612 1053631 := bstep (se 1 (by rfl) ⟨790223, by rfl⟩ : syracuseStep 1053631 = 1580447) B1580447
theorem B13538623 : Blo 1052612 13538623 := bstep (se 1 (by rfl) ⟨10153967, by rfl⟩ : syracuseStep 13538623 = 20307935) B20307935
theorem B1054111 : Blo 1052612 1054111 := bstep (se 1 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 1054111 = 1581167) B1581167
theorem B12031415 : Blo 1052612 12031415 := bstep (se 1 (by rfl) ⟨9023561, by rfl⟩ : syracuseStep 12031415 = 18047123) B18047123
theorem B1185439 : Blo 1052612 1185439 := bstep (se 1 (by rfl) ⟨889079, by rfl⟩ : syracuseStep 1185439 = 1778159) B1778159
theorem B1054767 : Blo 1052612 1054767 := bstep (se 1 (by rfl) ⟨791075, by rfl⟩ : syracuseStep 1054767 = 1582151) B1582151
theorem B1579259 : Blo 1052612 1579259 := bstep (se 1 (by rfl) ⟨1184444, by rfl⟩ : syracuseStep 1579259 = 2368889) B2368889
theorem B1055167 : Blo 1052612 1055167 := bstep (se 1 (by rfl) ⟨791375, by rfl⟩ : syracuseStep 1055167 = 1582751) B1582751
theorem B39066245 : Blo 1052612 39066245 := bstep (se 4 (by rfl) ⟨3662460, by rfl⟩ : syracuseStep 39066245 = 7324921) B7324921
theorem B2530055 : Blo 1052612 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B1055727 : Blo 1052612 1055727 := bstep (se 1 (by rfl) ⟨791795, by rfl⟩ : syracuseStep 1055727 = 1583591) B1583591
theorem B14425103 : Blo 1052612 14425103 := bstep (se 1 (by rfl) ⟨10818827, by rfl⟩ : syracuseStep 14425103 = 21637655) B21637655
theorem B4496593 : Blo 1052612 4496593 := bstep (se 2 (by rfl) ⟨1686222, by rfl⟩ : syracuseStep 4496593 = 3372445) B3372445
theorem B1581119 : Blo 1052612 1581119 := bstep (se 1 (by rfl) ⟨1185839, by rfl⟩ : syracuseStep 1581119 = 2371679) B2371679
theorem B1582079 : Blo 1052612 1582079 := bstep (se 1 (by rfl) ⟨1186559, by rfl⟩ : syracuseStep 1582079 = 2373119) B2373119
theorem B4498591 : Blo 1052612 4498591 := bstep (se 1 (by rfl) ⟨3373943, by rfl⟩ : syracuseStep 4498591 = 6747887) B6747887
theorem B1779455 : Blo 1052612 1779455 := bstep (se 1 (by rfl) ⟨1334591, by rfl⟩ : syracuseStep 1779455 = 2669183) B2669183
theorem B1583783 : Blo 1052612 1583783 := bstep (se 1 (by rfl) ⟨1187837, by rfl⟩ : syracuseStep 1583783 = 2375675) B2375675
theorem B1780987 : Blo 1052612 1780987 := bstep (se 1 (by rfl) ⟨1335740, by rfl⟩ : syracuseStep 1780987 = 2671481) B2671481
theorem B1584743 : Blo 1052612 1584743 := bstep (se 1 (by rfl) ⟨1188557, by rfl⟩ : syracuseStep 1584743 = 2377115) B2377115
theorem B19508921 : Blo 1052612 19508921 := bstep (se 2 (by rfl) ⟨7315845, by rfl⟩ : syracuseStep 19508921 = 14631691) B14631691
theorem B2371625 : Blo 1052612 2371625 := bstep (se 2 (by rfl) ⟨889359, by rfl⟩ : syracuseStep 2371625 = 1778719) B1778719
theorem B2373497 : Blo 1052612 2373497 := bstep (se 2 (by rfl) ⟨890061, by rfl⟩ : syracuseStep 2373497 = 1780123) B1780123
theorem B2373659 : Blo 1052612 2373659 := bstep (se 1 (by rfl) ⟨1780244, by rfl⟩ : syracuseStep 2373659 = 3560489) B3560489
theorem B36485711 : Blo 1052612 36485711 := bstep (se 1 (by rfl) ⟨27364283, by rfl⟩ : syracuseStep 36485711 = 54728567) B54728567
theorem B2374919 : Blo 1052612 2374919 := bstep (se 1 (by rfl) ⟨1781189, by rfl⟩ : syracuseStep 2374919 = 3562379) B3562379
theorem B2376233 : Blo 1052612 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B2671775 : Blo 1052612 2671775 := bstep (se 1 (by rfl) ⟨2003831, by rfl⟩ : syracuseStep 2671775 = 4007663) B4007663
theorem B19253321 : Blo 1052612 19253321 := bstep (se 2 (by rfl) ⟨7219995, by rfl⟩ : syracuseStep 19253321 = 14439991) B14439991
theorem B10832621 : Blo 1052612 10832621 := bstep (se 3 (by rfl) ⟨2031116, by rfl⟩ : syracuseStep 10832621 = 4062233) B4062233
theorem B457034885 : Blo 1052612 457034885 := bstep (se 4 (by rfl) ⟨42847020, by rfl⟩ : syracuseStep 457034885 = 85694041) B85694041
theorem B2249527 : Blo 1052612 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B91053557 : Blo 1052612 91053557 := bstep (se 5 (by rfl) ⟨4268135, by rfl⟩ : syracuseStep 91053557 = 8536271) B8536271
theorem B14442137 : Blo 1052612 14442137 := bstep (se 2 (by rfl) ⟨5415801, by rfl⟩ : syracuseStep 14442137 = 10831603) B10831603
theorem B6840055 : Blo 1052612 6840055 := bstep (se 1 (by rfl) ⟨5130041, by rfl⟩ : syracuseStep 6840055 = 10260083) B10260083
theorem B10118141 : Blo 1052612 10118141 := bstep (se 3 (by rfl) ⟨1897151, by rfl⟩ : syracuseStep 10118141 = 3794303) B3794303
theorem B3040763 : Blo 1052612 3040763 := bstep (se 1 (by rfl) ⟨2280572, by rfl⟩ : syracuseStep 3040763 = 4561145) B4561145
theorem B2255131 : Blo 1052612 2255131 := bstep (se 1 (by rfl) ⟨1691348, by rfl⟩ : syracuseStep 2255131 = 3382697) B3382697
theorem B1712155481 : Blo 1052612 1712155481 := bstep (se 2 (by rfl) ⟨642058305, by rfl⟩ : syracuseStep 1712155481 = 1284116611) B1284116611
theorem B76999895 : Blo 1052612 76999895 := bstep (se 1 (by rfl) ⟨57749921, by rfl⟩ : syracuseStep 76999895 = 115499843) B115499843
theorem B5337575 : Blo 1052612 5337575 := bstep (se 1 (by rfl) ⟨4003181, by rfl⟩ : syracuseStep 5337575 = 8006363) B8006363
theorem B1897499 : Blo 1052612 1897499 := bstep (se 1 (by rfl) ⟨1423124, by rfl⟩ : syracuseStep 1897499 = 2846249) B2846249
theorem B9009143 : Blo 1052612 9009143 := bstep (se 1 (by rfl) ⟨6756857, by rfl⟩ : syracuseStep 9009143 = 13513715) B13513715
theorem B3046607 : Blo 1052612 3046607 := bstep (se 1 (by rfl) ⟨2284955, by rfl⟩ : syracuseStep 3046607 = 4569911) B4569911
theorem B3801383 : Blo 1052612 3801383 := bstep (se 1 (by rfl) ⟨2851037, by rfl⟩ : syracuseStep 3801383 = 5702075) B5702075
theorem B5998121 : Blo 1052612 5998121 := bstep (se 2 (by rfl) ⟨2249295, by rfl⟩ : syracuseStep 5998121 = 4498591) B4498591
theorem B1052839 : Blo 1052612 1052839 := bstep (se 1 (by rfl) ⟨789629, by rfl⟩ : syracuseStep 1052839 = 1579259) B1579259
theorem B24383753 : Blo 1052612 24383753 := bstep (se 2 (by rfl) ⟨9143907, by rfl⟩ : syracuseStep 24383753 = 18287815) B18287815
theorem B1054079 : Blo 1052612 1054079 := bstep (se 1 (by rfl) ⟨790559, by rfl⟩ : syracuseStep 1054079 = 1581119) B1581119
theorem B1054719 : Blo 1052612 1054719 := bstep (se 1 (by rfl) ⟨791039, by rfl⟩ : syracuseStep 1054719 = 1582079) B1582079
theorem B1579385 : Blo 1052612 1579385 := bstep (se 2 (by rfl) ⟨592269, by rfl⟩ : syracuseStep 1579385 = 1184539) B1184539
theorem B1186303 : Blo 1052612 1186303 := bstep (se 1 (by rfl) ⟨889727, by rfl⟩ : syracuseStep 1186303 = 1779455) B1779455
theorem B1055855 : Blo 1052612 1055855 := bstep (se 1 (by rfl) ⟨791891, by rfl⟩ : syracuseStep 1055855 = 1583783) B1583783
theorem B1580585 : Blo 1052612 1580585 := bstep (se 2 (by rfl) ⟨592719, by rfl⟩ : syracuseStep 1580585 = 1185439) B1185439
theorem B1056495 : Blo 1052612 1056495 := bstep (se 1 (by rfl) ⟨792371, by rfl⟩ : syracuseStep 1056495 = 1584743) B1584743
theorem B1581083 : Blo 1052612 1581083 := bstep (se 1 (by rfl) ⟨1185812, by rfl⟩ : syracuseStep 1581083 = 2371625) B2371625
theorem B1582331 : Blo 1052612 1582331 := bstep (se 1 (by rfl) ⟨1186748, by rfl⟩ : syracuseStep 1582331 = 2373497) B2373497
theorem B6006095 : Blo 1052612 6006095 := bstep (se 1 (by rfl) ⟨4504571, by rfl⟩ : syracuseStep 6006095 = 9009143) B9009143
theorem B1582439 : Blo 1052612 1582439 := bstep (se 1 (by rfl) ⟨1186829, by rfl⟩ : syracuseStep 1582439 = 2373659) B2373659
theorem B24323807 : Blo 1052612 24323807 := bstep (se 1 (by rfl) ⟨18242855, by rfl⟩ : syracuseStep 24323807 = 36485711) B36485711
theorem B1583279 : Blo 1052612 1583279 := bstep (se 1 (by rfl) ⟨1187459, by rfl⟩ : syracuseStep 1583279 = 2374919) B2374919
theorem B9120073 : Blo 1052612 9120073 := bstep (se 2 (by rfl) ⟨3420027, by rfl⟩ : syracuseStep 9120073 = 6840055) B6840055
theorem B1584155 : Blo 1052612 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B1781183 : Blo 1052612 1781183 := bstep (se 1 (by rfl) ⟨1335887, by rfl⟩ : syracuseStep 1781183 = 2671775) B2671775
theorem B304689923 : Blo 1052612 304689923 := bstep (se 1 (by rfl) ⟨228517442, by rfl⟩ : syracuseStep 304689923 = 457034885) B457034885
theorem B2667775 : Blo 1052612 2667775 := bstep (se 1 (by rfl) ⟨2000831, by rfl⟩ : syracuseStep 2667775 = 4001663) B4001663
theorem B2374649 : Blo 1052612 2374649 := bstep (se 2 (by rfl) ⟨890493, by rfl⟩ : syracuseStep 2374649 = 1780987) B1780987
theorem B9616735 : Blo 1052612 9616735 := bstep (se 1 (by rfl) ⟨7212551, by rfl⟩ : syracuseStep 9616735 = 14425103) B14425103
theorem B60702371 : Blo 1052612 60702371 := bstep (se 1 (by rfl) ⟨45526778, by rfl⟩ : syracuseStep 60702371 = 91053557) B91053557
theorem B2999369 : Blo 1052612 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B28886989 : Blo 1052612 28886989 := bstep (se 3 (by rfl) ⟨5416310, by rfl⟩ : syracuseStep 28886989 = 10832621) B10832621
theorem B51333263 : Blo 1052612 51333263 := bstep (se 1 (by rfl) ⟨38499947, by rfl⟩ : syracuseStep 51333263 = 76999895) B76999895
theorem B3558383 : Blo 1052612 3558383 := bstep (se 1 (by rfl) ⟨2668787, by rfl⟩ : syracuseStep 3558383 = 5337575) B5337575
theorem B1264999 : Blo 1052612 1264999 := bstep (se 1 (by rfl) ⟨948749, by rfl⟩ : syracuseStep 1264999 = 1897499) B1897499
theorem B19225295 : Blo 1052612 19225295 := bstep (se 1 (by rfl) ⟨14418971, by rfl⟩ : syracuseStep 19225295 = 28837943) B28837943
theorem B12835547 : Blo 1052612 12835547 := bstep (se 1 (by rfl) ⟨9626660, by rfl⟩ : syracuseStep 12835547 = 19253321) B19253321
theorem B1333999 : Blo 1052612 1333999 := bstep (se 1 (by rfl) ⟨1000499, by rfl⟩ : syracuseStep 1333999 = 2000999) B2000999
theorem B7691561 : Blo 1052612 7691561 := bstep (se 2 (by rfl) ⟨2884335, by rfl⟩ : syracuseStep 7691561 = 5768671) B5768671
theorem B3006841 : Blo 1052612 3006841 := bstep (se 2 (by rfl) ⟨1127565, by rfl⟩ : syracuseStep 3006841 = 2255131) B2255131
theorem B8020943 : Blo 1052612 8020943 := bstep (se 1 (by rfl) ⟨6015707, by rfl⟩ : syracuseStep 8020943 = 12031415) B12031415
theorem B26044163 : Blo 1052612 26044163 := bstep (se 1 (by rfl) ⟨19533122, by rfl⟩ : syracuseStep 26044163 = 39066245) B39066245
theorem B9628091 : Blo 1052612 9628091 := bstep (se 1 (by rfl) ⟨7221068, by rfl⟩ : syracuseStep 9628091 = 14442137) B14442137
theorem B32434805 : Blo 1052612 32434805 := bstep (se 5 (by rfl) ⟨1520381, by rfl⟩ : syracuseStep 32434805 = 3040763) B3040763
theorem B6745427 : Blo 1052612 6745427 := bstep (se 1 (by rfl) ⟨5059070, by rfl⟩ : syracuseStep 6745427 = 10118141) B10118141
theorem B18051497 : Blo 1052612 18051497 := bstep (se 2 (by rfl) ⟨6769311, by rfl⟩ : syracuseStep 18051497 = 13538623) B13538623
theorem B1141436987 : Blo 1052612 1141436987 := bstep (se 1 (by rfl) ⟨856077740, by rfl⟩ : syracuseStep 1141436987 = 1712155481) B1712155481
theorem B6746813 : Blo 1052612 6746813 := bstep (se 3 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 6746813 = 2530055) B2530055
theorem B13005947 : Blo 1052612 13005947 := bstep (se 1 (by rfl) ⟨9754460, by rfl⟩ : syracuseStep 13005947 = 19508921) B19508921
theorem B5995457 : Blo 1052612 5995457 := bstep (se 2 (by rfl) ⟨2248296, by rfl⟩ : syracuseStep 5995457 = 4496593) B4496593
theorem B2031071 : Blo 1052612 2031071 := bstep (se 1 (by rfl) ⟨1523303, by rfl⟩ : syracuseStep 2031071 = 3046607) B3046607
theorem B34635701 : Blo 1052612 34635701 := bstep (se 5 (by rfl) ⟨1623548, by rfl⟩ : syracuseStep 34635701 = 3247097) B3247097
theorem B1999579 : Blo 1052612 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B3998747 : Blo 1052612 3998747 := bstep (se 1 (by rfl) ⟨2999060, by rfl⟩ : syracuseStep 3998747 = 5998121) B5998121
theorem B16255835 : Blo 1052612 16255835 := bstep (se 1 (by rfl) ⟨12191876, by rfl⟩ : syracuseStep 16255835 = 24383753) B24383753
theorem B12160097 : Blo 1052612 12160097 := bstep (se 2 (by rfl) ⟨4560036, by rfl⟩ : syracuseStep 12160097 = 9120073) B9120073
theorem B1052923 : Blo 1052612 1052923 := bstep (se 1 (by rfl) ⟨789692, by rfl⟩ : syracuseStep 1052923 = 1579385) B1579385
theorem B12816863 : Blo 1052612 12816863 := bstep (se 1 (by rfl) ⟨9612647, by rfl⟩ : syracuseStep 12816863 = 19225295) B19225295
theorem B8557031 : Blo 1052612 8557031 := bstep (se 1 (by rfl) ⟨6417773, by rfl⟩ : syracuseStep 8557031 = 12835547) B12835547
theorem B1053723 : Blo 1052612 1053723 := bstep (se 1 (by rfl) ⟨790292, by rfl⟩ : syracuseStep 1053723 = 1580585) B1580585
theorem B1054055 : Blo 1052612 1054055 := bstep (se 1 (by rfl) ⟨790541, by rfl⟩ : syracuseStep 1054055 = 1581083) B1581083
theorem B5347295 : Blo 1052612 5347295 := bstep (se 1 (by rfl) ⟨4010471, by rfl⟩ : syracuseStep 5347295 = 8020943) B8020943
theorem B1054887 : Blo 1052612 1054887 := bstep (se 1 (by rfl) ⟨791165, by rfl⟩ : syracuseStep 1054887 = 1582331) B1582331
theorem B4004063 : Blo 1052612 4004063 := bstep (se 1 (by rfl) ⟨3003047, by rfl⟩ : syracuseStep 4004063 = 6006095) B6006095
theorem B1054959 : Blo 1052612 1054959 := bstep (se 1 (by rfl) ⟨791219, by rfl⟩ : syracuseStep 1054959 = 1582439) B1582439
theorem B1055519 : Blo 1052612 1055519 := bstep (se 1 (by rfl) ⟨791639, by rfl⟩ : syracuseStep 1055519 = 1583279) B1583279
theorem B1056103 : Blo 1052612 1056103 := bstep (se 1 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 1056103 = 1584155) B1584155
theorem B4496951 : Blo 1052612 4496951 := bstep (se 1 (by rfl) ⟨3372713, by rfl⟩ : syracuseStep 4496951 = 6745427) B6745427
theorem B1187455 : Blo 1052612 1187455 := bstep (se 1 (by rfl) ⟨890591, by rfl⟩ : syracuseStep 1187455 = 1781183) B1781183
theorem B12034331 : Blo 1052612 12034331 := bstep (se 1 (by rfl) ⟨9025748, by rfl⟩ : syracuseStep 12034331 = 18051497) B18051497
theorem B4497875 : Blo 1052612 4497875 := bstep (se 1 (by rfl) ⟨3373406, by rfl⟩ : syracuseStep 4497875 = 6746813) B6746813
theorem B1581737 : Blo 1052612 1581737 := bstep (se 2 (by rfl) ⟨593151, by rfl⟩ : syracuseStep 1581737 = 1186303) B1186303
theorem B1778665 : Blo 1052612 1778665 := bstep (se 2 (by rfl) ⟨666999, by rfl⟩ : syracuseStep 1778665 = 1333999) B1333999
theorem B5416189 : Blo 1052612 5416189 := bstep (se 3 (by rfl) ⟨1015535, by rfl⟩ : syracuseStep 5416189 = 2031071) B2031071
theorem B12822313 : Blo 1052612 12822313 := bstep (se 2 (by rfl) ⟨4808367, by rfl⟩ : syracuseStep 12822313 = 9616735) B9616735
theorem B1583099 : Blo 1052612 1583099 := bstep (se 1 (by rfl) ⟨1187324, by rfl⟩ : syracuseStep 1583099 = 2374649) B2374649
theorem B2534255 : Blo 1052612 2534255 := bstep (se 1 (by rfl) ⟨1900691, by rfl⟩ : syracuseStep 2534255 = 3801383) B3801383
theorem B4009121 : Blo 1052612 4009121 := bstep (se 2 (by rfl) ⟨1503420, by rfl⟩ : syracuseStep 4009121 = 3006841) B3006841
theorem B34222175 : Blo 1052612 34222175 := bstep (se 1 (by rfl) ⟨25666631, by rfl⟩ : syracuseStep 34222175 = 51333263) B51333263
theorem B2372255 : Blo 1052612 2372255 := bstep (se 1 (by rfl) ⟨1779191, by rfl⟩ : syracuseStep 2372255 = 3558383) B3558383
theorem B38515985 : Blo 1052612 38515985 := bstep (se 2 (by rfl) ⟨14443494, by rfl⟩ : syracuseStep 38515985 = 28886989) B28886989
theorem B34682525 : Blo 1052612 34682525 := bstep (se 3 (by rfl) ⟨6502973, by rfl⟩ : syracuseStep 34682525 = 13005947) B13005947
theorem B1686665 : Blo 1052612 1686665 := bstep (se 2 (by rfl) ⟨632499, by rfl⟩ : syracuseStep 1686665 = 1264999) B1264999
theorem B5127707 : Blo 1052612 5127707 := bstep (se 1 (by rfl) ⟨3845780, by rfl⟩ : syracuseStep 5127707 = 7691561) B7691561
theorem B3557033 : Blo 1052612 3557033 := bstep (se 2 (by rfl) ⟨1333887, by rfl⟩ : syracuseStep 3557033 = 2667775) B2667775
theorem B760957991 : Blo 1052612 760957991 := bstep (se 1 (by rfl) ⟨570718493, by rfl⟩ : syracuseStep 760957991 = 1141436987) B1141436987
theorem B23090467 : Blo 1052612 23090467 := bstep (se 1 (by rfl) ⟨17317850, by rfl⟩ : syracuseStep 23090467 = 34635701) B34635701
theorem B16215871 : Blo 1052612 16215871 := bstep (se 1 (by rfl) ⟨12161903, by rfl⟩ : syracuseStep 16215871 = 24323807) B24323807
theorem B17362775 : Blo 1052612 17362775 := bstep (se 1 (by rfl) ⟨13022081, by rfl⟩ : syracuseStep 17362775 = 26044163) B26044163
theorem B6418727 : Blo 1052612 6418727 := bstep (se 1 (by rfl) ⟨4814045, by rfl⟩ : syracuseStep 6418727 = 9628091) B9628091
theorem B21623203 : Blo 1052612 21623203 := bstep (se 1 (by rfl) ⟨16217402, by rfl⟩ : syracuseStep 21623203 = 32434805) B32434805
theorem B203126615 : Blo 1052612 203126615 := bstep (se 1 (by rfl) ⟨152344961, by rfl⟩ : syracuseStep 203126615 = 304689923) B304689923
theorem B3996971 : Blo 1052612 3996971 := bstep (se 1 (by rfl) ⟨2997728, by rfl⟩ : syracuseStep 3996971 = 5995457) B5995457
theorem B40468247 : Blo 1052612 40468247 := bstep (se 1 (by rfl) ⟨30351185, by rfl⟩ : syracuseStep 40468247 = 60702371) B60702371
theorem B5704687 : Blo 1052612 5704687 := bstep (se 1 (by rfl) ⟨4278515, by rfl⟩ : syracuseStep 5704687 = 8557031) B8557031
theorem B1054491 : Blo 1052612 1054491 := bstep (se 1 (by rfl) ⟨790868, by rfl⟩ : syracuseStep 1054491 = 1581737) B1581737
theorem B1055399 : Blo 1052612 1055399 := bstep (se 1 (by rfl) ⟨791549, by rfl⟩ : syracuseStep 1055399 = 1583099) B1583099
theorem B11575183 : Blo 1052612 11575183 := bstep (se 1 (by rfl) ⟨8681387, by rfl⟩ : syracuseStep 11575183 = 17362775) B17362775
theorem B22814783 : Blo 1052612 22814783 := bstep (se 1 (by rfl) ⟨17111087, by rfl⟩ : syracuseStep 22814783 = 34222175) B34222175
theorem B1581503 : Blo 1052612 1581503 := bstep (se 1 (by rfl) ⟨1186127, by rfl⟩ : syracuseStep 1581503 = 2372255) B2372255
theorem B1124443 : Blo 1052612 1124443 := bstep (se 1 (by rfl) ⟨843332, by rfl⟩ : syracuseStep 1124443 = 1686665) B1686665
theorem B1583273 : Blo 1052612 1583273 := bstep (se 2 (by rfl) ⟨593727, by rfl⟩ : syracuseStep 1583273 = 1187455) B1187455
theorem B2664647 : Blo 1052612 2664647 := bstep (se 1 (by rfl) ⟨1998485, by rfl⟩ : syracuseStep 2664647 = 3996971) B3996971
theorem B3418471 : Blo 1052612 3418471 := bstep (se 1 (by rfl) ⟨2563853, by rfl⟩ : syracuseStep 3418471 = 5127707) B5127707
theorem B26978831 : Blo 1052612 26978831 := bstep (se 1 (by rfl) ⟨20234123, by rfl⟩ : syracuseStep 26978831 = 40468247) B40468247
theorem B2665831 : Blo 1052612 2665831 := bstep (se 1 (by rfl) ⟨1999373, by rfl⟩ : syracuseStep 2665831 = 3998747) B3998747
theorem B2666105 : Blo 1052612 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B2371355 : Blo 1052612 2371355 := bstep (se 1 (by rfl) ⟨1778516, by rfl⟩ : syracuseStep 2371355 = 3557033) B3557033
theorem B2371553 : Blo 1052612 2371553 := bstep (se 2 (by rfl) ⟨889332, by rfl⟩ : syracuseStep 2371553 = 1778665) B1778665
theorem B8106731 : Blo 1052612 8106731 := bstep (se 1 (by rfl) ⟨6080048, by rfl⟩ : syracuseStep 8106731 = 12160097) B12160097
theorem B2669375 : Blo 1052612 2669375 := bstep (se 1 (by rfl) ⟨2002031, by rfl⟩ : syracuseStep 2669375 = 4004063) B4004063
theorem B2997967 : Blo 1052612 2997967 := bstep (se 1 (by rfl) ⟨2248475, by rfl⟩ : syracuseStep 2997967 = 4496951) B4496951
theorem B2998583 : Blo 1052612 2998583 := bstep (se 1 (by rfl) ⟨2248937, by rfl⟩ : syracuseStep 2998583 = 4497875) B4497875
theorem B28886341 : Blo 1052612 28886341 := bstep (se 4 (by rfl) ⟨2708094, by rfl⟩ : syracuseStep 28886341 = 5416189) B5416189
theorem B30787289 : Blo 1052612 30787289 := bstep (se 2 (by rfl) ⟨11545233, by rfl⟩ : syracuseStep 30787289 = 23090467) B23090467
theorem B1689503 : Blo 1052612 1689503 := bstep (se 1 (by rfl) ⟨1267127, by rfl⟩ : syracuseStep 1689503 = 2534255) B2534255
theorem B2672747 : Blo 1052612 2672747 := bstep (se 1 (by rfl) ⟨2004560, by rfl⟩ : syracuseStep 2672747 = 4009121) B4009121
theorem B4279151 : Blo 1052612 4279151 := bstep (se 1 (by rfl) ⟨3209363, by rfl⟩ : syracuseStep 4279151 = 6418727) B6418727
theorem B25677323 : Blo 1052612 25677323 := bstep (se 1 (by rfl) ⟨19257992, by rfl⟩ : syracuseStep 25677323 = 38515985) B38515985
theorem B23121683 : Blo 1052612 23121683 := bstep (se 1 (by rfl) ⟨17341262, by rfl⟩ : syracuseStep 23121683 = 34682525) B34682525
theorem B135417743 : Blo 1052612 135417743 := bstep (se 1 (by rfl) ⟨101563307, by rfl⟩ : syracuseStep 135417743 = 203126615) B203126615
theorem B10837223 : Blo 1052612 10837223 := bstep (se 1 (by rfl) ⟨8127917, by rfl⟩ : syracuseStep 10837223 = 16255835) B16255835
theorem B507305327 : Blo 1052612 507305327 := bstep (se 1 (by rfl) ⟨380478995, by rfl⟩ : syracuseStep 507305327 = 760957991) B760957991
theorem B17096417 : Blo 1052612 17096417 := bstep (se 2 (by rfl) ⟨6411156, by rfl⟩ : syracuseStep 17096417 = 12822313) B12822313
theorem B8544575 : Blo 1052612 8544575 := bstep (se 1 (by rfl) ⟨6408431, by rfl⟩ : syracuseStep 8544575 = 12816863) B12816863
theorem B3564863 : Blo 1052612 3564863 := bstep (se 1 (by rfl) ⟨2673647, by rfl⟩ : syracuseStep 3564863 = 5347295) B5347295
theorem B21621161 : Blo 1052612 21621161 := bstep (se 2 (by rfl) ⟨8107935, by rfl⟩ : syracuseStep 21621161 = 16215871) B16215871
theorem B8022887 : Blo 1052612 8022887 := bstep (se 1 (by rfl) ⟨6017165, by rfl⟩ : syracuseStep 8022887 = 12034331) B12034331
theorem B28830937 : Blo 1052612 28830937 := bstep (se 2 (by rfl) ⟨10811601, by rfl⟩ : syracuseStep 28830937 = 21623203) B21623203
theorem B1999055 : Blo 1052612 1999055 := bstep (se 1 (by rfl) ⟨1499291, by rfl⟩ : syracuseStep 1999055 = 2998583) B2998583
theorem B2852767 : Blo 1052612 2852767 := bstep (se 1 (by rfl) ⟨2139575, by rfl⟩ : syracuseStep 2852767 = 4279151) B4279151
theorem B90278495 : Blo 1052612 90278495 := bstep (se 1 (by rfl) ⟨67708871, by rfl⟩ : syracuseStep 90278495 = 135417743) B135417743
theorem B4557961 : Blo 1052612 4557961 := bstep (se 2 (by rfl) ⟨1709235, by rfl⟩ : syracuseStep 4557961 = 3418471) B3418471
theorem B38441249 : Blo 1052612 38441249 := bstep (se 2 (by rfl) ⟨14415468, by rfl⟩ : syracuseStep 38441249 = 28830937) B28830937
theorem B15209855 : Blo 1052612 15209855 := bstep (se 1 (by rfl) ⟨11407391, by rfl⟩ : syracuseStep 15209855 = 22814783) B22814783
theorem B1054335 : Blo 1052612 1054335 := bstep (se 1 (by rfl) ⟨790751, by rfl⟩ : syracuseStep 1054335 = 1581503) B1581503
theorem B1055515 : Blo 1052612 1055515 := bstep (se 1 (by rfl) ⟨791636, by rfl⟩ : syracuseStep 1055515 = 1583273) B1583273
theorem B1776431 : Blo 1052612 1776431 := bstep (se 1 (by rfl) ⟨1332323, by rfl⟩ : syracuseStep 1776431 = 2664647) B2664647
theorem B5348591 : Blo 1052612 5348591 := bstep (se 1 (by rfl) ⟨4011443, by rfl⟩ : syracuseStep 5348591 = 8022887) B8022887
theorem B1777403 : Blo 1052612 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B1580903 : Blo 1052612 1580903 := bstep (se 1 (by rfl) ⟨1185677, by rfl⟩ : syracuseStep 1580903 = 2371355) B2371355
theorem B1581035 : Blo 1052612 1581035 := bstep (se 1 (by rfl) ⟨1185776, by rfl⟩ : syracuseStep 1581035 = 2371553) B2371553
theorem B1779583 : Blo 1052612 1779583 := bstep (se 1 (by rfl) ⟨1334687, by rfl⟩ : syracuseStep 1779583 = 2669375) B2669375
theorem B22785533 : Blo 1052612 22785533 := bstep (se 3 (by rfl) ⟨4272287, by rfl⟩ : syracuseStep 22785533 = 8544575) B8544575
theorem B20524859 : Blo 1052612 20524859 := bstep (se 1 (by rfl) ⟨15393644, by rfl⟩ : syracuseStep 20524859 = 30787289) B30787289
theorem B1781831 : Blo 1052612 1781831 := bstep (se 1 (by rfl) ⟨1336373, by rfl⟩ : syracuseStep 1781831 = 2672747) B2672747
theorem B38515121 : Blo 1052612 38515121 := bstep (se 2 (by rfl) ⟨14443170, by rfl⟩ : syracuseStep 38515121 = 28886341) B28886341
theorem B17118215 : Blo 1052612 17118215 := bstep (se 1 (by rfl) ⟨12838661, by rfl⟩ : syracuseStep 17118215 = 25677323) B25677323
theorem B15414455 : Blo 1052612 15414455 := bstep (se 1 (by rfl) ⟨11560841, by rfl⟩ : syracuseStep 15414455 = 23121683) B23121683
theorem B3554441 : Blo 1052612 3554441 := bstep (se 2 (by rfl) ⟨1332915, by rfl⟩ : syracuseStep 3554441 = 2665831) B2665831
theorem B7224815 : Blo 1052612 7224815 := bstep (se 1 (by rfl) ⟨5418611, by rfl⟩ : syracuseStep 7224815 = 10837223) B10837223
theorem B4505341 : Blo 1052612 4505341 := bstep (se 3 (by rfl) ⟨844751, by rfl⟩ : syracuseStep 4505341 = 1689503) B1689503
theorem B30424997 : Blo 1052612 30424997 := bstep (se 4 (by rfl) ⟨2852343, by rfl⟩ : syracuseStep 30424997 = 5704687) B5704687
theorem B2376575 : Blo 1052612 2376575 := bstep (se 1 (by rfl) ⟨1782431, by rfl⟩ : syracuseStep 2376575 = 3564863) B3564863
theorem B1352814205 : Blo 1052612 1352814205 := bstep (se 3 (by rfl) ⟨253652663, by rfl⟩ : syracuseStep 1352814205 = 507305327) B507305327
theorem B1499257 : Blo 1052612 1499257 := bstep (se 2 (by rfl) ⟨562221, by rfl⟩ : syracuseStep 1499257 = 1124443) B1124443
theorem B11397611 : Blo 1052612 11397611 := bstep (se 1 (by rfl) ⟨8548208, by rfl⟩ : syracuseStep 11397611 = 17096417) B17096417
theorem B14414107 : Blo 1052612 14414107 := bstep (se 1 (by rfl) ⟨10810580, by rfl⟩ : syracuseStep 14414107 = 21621161) B21621161
theorem B17985887 : Blo 1052612 17985887 := bstep (se 1 (by rfl) ⟨13489415, by rfl⟩ : syracuseStep 17985887 = 26978831) B26978831
theorem B5404487 : Blo 1052612 5404487 := bstep (se 1 (by rfl) ⟨4053365, by rfl⟩ : syracuseStep 5404487 = 8106731) B8106731
theorem B3997289 : Blo 1052612 3997289 := bstep (se 2 (by rfl) ⟨1498983, by rfl⟩ : syracuseStep 3997289 = 2997967) B2997967
theorem B15433577 : Blo 1052612 15433577 := bstep (se 2 (by rfl) ⟨5787591, by rfl⟩ : syracuseStep 15433577 = 11575183) B11575183
theorem B1999009 : Blo 1052612 1999009 := bstep (se 2 (by rfl) ⟨749628, by rfl⟩ : syracuseStep 1999009 = 1499257) B1499257
theorem B3803689 : Blo 1052612 3803689 := bstep (se 2 (by rfl) ⟨1426383, by rfl⟩ : syracuseStep 3803689 = 2852767) B2852767
theorem B25627499 : Blo 1052612 25627499 := bstep (se 1 (by rfl) ⟨19220624, by rfl⟩ : syracuseStep 25627499 = 38441249) B38441249
theorem B1184287 : Blo 1052612 1184287 := bstep (se 1 (by rfl) ⟨888215, by rfl⟩ : syracuseStep 1184287 = 1776431) B1776431
theorem B1803752273 : Blo 1052612 1803752273 := bstep (se 2 (by rfl) ⟨676407102, by rfl⟩ : syracuseStep 1803752273 = 1352814205) B1352814205
theorem B1184935 : Blo 1052612 1184935 := bstep (se 1 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 1184935 = 1777403) B1777403
theorem B1053935 : Blo 1052612 1053935 := bstep (se 1 (by rfl) ⟨790451, by rfl⟩ : syracuseStep 1053935 = 1580903) B1580903
theorem B1054023 : Blo 1052612 1054023 := bstep (se 1 (by rfl) ⟨790517, by rfl⟩ : syracuseStep 1054023 = 1581035) B1581035
theorem B1187887 : Blo 1052612 1187887 := bstep (se 1 (by rfl) ⟨890915, by rfl⟩ : syracuseStep 1187887 = 1781831) B1781831
theorem B11412143 : Blo 1052612 11412143 := bstep (se 1 (by rfl) ⟨8559107, by rfl⟩ : syracuseStep 11412143 = 17118215) B17118215
theorem B57647861 : Blo 1052612 57647861 := bstep (se 5 (by rfl) ⟨2702243, by rfl⟩ : syracuseStep 57647861 = 5404487) B5404487
theorem B2369627 : Blo 1052612 2369627 := bstep (se 1 (by rfl) ⟨1777220, by rfl⟩ : syracuseStep 2369627 = 3554441) B3554441
theorem B6007121 : Blo 1052612 6007121 := bstep (se 2 (by rfl) ⟨2252670, by rfl⟩ : syracuseStep 6007121 = 4505341) B4505341
theorem B2664859 : Blo 1052612 2664859 := bstep (se 1 (by rfl) ⟨1998644, by rfl⟩ : syracuseStep 2664859 = 3997289) B3997289
theorem B1584383 : Blo 1052612 1584383 := bstep (se 1 (by rfl) ⟨1188287, by rfl⟩ : syracuseStep 1584383 = 2376575) B2376575
theorem B2372777 : Blo 1052612 2372777 := bstep (se 2 (by rfl) ⟨889791, by rfl⟩ : syracuseStep 2372777 = 1779583) B1779583
theorem B10139903 : Blo 1052612 10139903 := bstep (se 1 (by rfl) ⟨7604927, by rfl⟩ : syracuseStep 10139903 = 15209855) B15209855
theorem B6077281 : Blo 1052612 6077281 := bstep (se 2 (by rfl) ⟨2278980, by rfl⟩ : syracuseStep 6077281 = 4557961) B4557961
theorem B19218809 : Blo 1052612 19218809 := bstep (se 2 (by rfl) ⟨7207053, by rfl⟩ : syracuseStep 19218809 = 14414107) B14414107
theorem B30393629 : Blo 1052612 30393629 := bstep (se 3 (by rfl) ⟨5698805, by rfl⟩ : syracuseStep 30393629 = 11397611) B11397611
theorem B15190355 : Blo 1052612 15190355 := bstep (se 1 (by rfl) ⟨11392766, by rfl⟩ : syracuseStep 15190355 = 22785533) B22785533
theorem B13683239 : Blo 1052612 13683239 := bstep (se 1 (by rfl) ⟨10262429, by rfl⟩ : syracuseStep 13683239 = 20524859) B20524859
theorem B25676747 : Blo 1052612 25676747 := bstep (se 1 (by rfl) ⟨19257560, by rfl⟩ : syracuseStep 25676747 = 38515121) B38515121
theorem B10276303 : Blo 1052612 10276303 := bstep (se 1 (by rfl) ⟨7707227, by rfl⟩ : syracuseStep 10276303 = 15414455) B15414455
theorem B1332703 : Blo 1052612 1332703 := bstep (se 1 (by rfl) ⟨999527, by rfl⟩ : syracuseStep 1332703 = 1999055) B1999055
theorem B60185663 : Blo 1052612 60185663 := bstep (se 1 (by rfl) ⟨45139247, by rfl⟩ : syracuseStep 60185663 = 90278495) B90278495
theorem B3565727 : Blo 1052612 3565727 := bstep (se 1 (by rfl) ⟨2674295, by rfl⟩ : syracuseStep 3565727 = 5348591) B5348591
theorem B11990591 : Blo 1052612 11990591 := bstep (se 1 (by rfl) ⟨8992943, by rfl⟩ : syracuseStep 11990591 = 17985887) B17985887
theorem B19266173 : Blo 1052612 19266173 := bstep (se 3 (by rfl) ⟨3612407, by rfl⟩ : syracuseStep 19266173 = 7224815) B7224815
theorem B10289051 : Blo 1052612 10289051 := bstep (se 1 (by rfl) ⟨7716788, by rfl⟩ : syracuseStep 10289051 = 15433577) B15433577
theorem B20283331 : Blo 1052612 20283331 := bstep (se 1 (by rfl) ⟨15212498, by rfl⟩ : syracuseStep 20283331 = 30424997) B30424997
theorem B51250157 : Blo 1052612 51250157 := bstep (se 3 (by rfl) ⟨9609404, by rfl⟩ : syracuseStep 51250157 = 19218809) B19218809
theorem B13701737 : Blo 1052612 13701737 := bstep (se 2 (by rfl) ⟨5138151, by rfl⟩ : syracuseStep 13701737 = 10276303) B10276303
theorem B7608095 : Blo 1052612 7608095 := bstep (se 1 (by rfl) ⟨5706071, by rfl⟩ : syracuseStep 7608095 = 11412143) B11412143
theorem B1579049 : Blo 1052612 1579049 := bstep (se 2 (by rfl) ⟨592143, by rfl⟩ : syracuseStep 1579049 = 1184287) B1184287
theorem B40507613 : Blo 1052612 40507613 := bstep (se 3 (by rfl) ⟨7595177, by rfl⟩ : syracuseStep 40507613 = 15190355) B15190355
theorem B1579751 : Blo 1052612 1579751 := bstep (se 1 (by rfl) ⟨1184813, by rfl⟩ : syracuseStep 1579751 = 2369627) B2369627
theorem B1579913 : Blo 1052612 1579913 := bstep (se 2 (by rfl) ⟨592467, by rfl⟩ : syracuseStep 1579913 = 1184935) B1184935
theorem B4004747 : Blo 1052612 4004747 := bstep (se 1 (by rfl) ⟨3003560, by rfl⟩ : syracuseStep 4004747 = 6007121) B6007121
theorem B1776937 : Blo 1052612 1776937 := bstep (se 2 (by rfl) ⟨666351, by rfl⟩ : syracuseStep 1776937 = 1332703) B1332703
theorem B1056255 : Blo 1052612 1056255 := bstep (se 1 (by rfl) ⟨792191, by rfl⟩ : syracuseStep 1056255 = 1584383) B1584383
theorem B1581851 : Blo 1052612 1581851 := bstep (se 1 (by rfl) ⟨1186388, by rfl⟩ : syracuseStep 1581851 = 2372777) B2372777
theorem B8103041 : Blo 1052612 8103041 := bstep (se 2 (by rfl) ⟨3038640, by rfl⟩ : syracuseStep 8103041 = 6077281) B6077281
theorem B6759935 : Blo 1052612 6759935 := bstep (se 1 (by rfl) ⟨5069951, by rfl⟩ : syracuseStep 6759935 = 10139903) B10139903
theorem B27044441 : Blo 1052612 27044441 := bstep (se 2 (by rfl) ⟨10141665, by rfl⟩ : syracuseStep 27044441 = 20283331) B20283331
theorem B6859367 : Blo 1052612 6859367 := bstep (se 1 (by rfl) ⟨5144525, by rfl⟩ : syracuseStep 6859367 = 10289051) B10289051
theorem B1583849 : Blo 1052612 1583849 := bstep (se 2 (by rfl) ⟨593943, by rfl⟩ : syracuseStep 1583849 = 1187887) B1187887
theorem B2665345 : Blo 1052612 2665345 := bstep (se 2 (by rfl) ⟨999504, by rfl⟩ : syracuseStep 2665345 = 1999009) B1999009
theorem B20262419 : Blo 1052612 20262419 := bstep (se 1 (by rfl) ⟨15196814, by rfl⟩ : syracuseStep 20262419 = 30393629) B30393629
theorem B9122159 : Blo 1052612 9122159 := bstep (se 1 (by rfl) ⟨6841619, by rfl⟩ : syracuseStep 9122159 = 13683239) B13683239
theorem B17084999 : Blo 1052612 17084999 := bstep (se 1 (by rfl) ⟨12813749, by rfl⟩ : syracuseStep 17084999 = 25627499) B25627499
theorem B17117831 : Blo 1052612 17117831 := bstep (se 1 (by rfl) ⟨12838373, by rfl⟩ : syracuseStep 17117831 = 25676747) B25676747
theorem B3553145 : Blo 1052612 3553145 := bstep (se 2 (by rfl) ⟨1332429, by rfl⟩ : syracuseStep 3553145 = 2664859) B2664859
theorem B40123775 : Blo 1052612 40123775 := bstep (se 1 (by rfl) ⟨30092831, by rfl⟩ : syracuseStep 40123775 = 60185663) B60185663
theorem B2377151 : Blo 1052612 2377151 := bstep (se 1 (by rfl) ⟨1782863, by rfl⟩ : syracuseStep 2377151 = 3565727) B3565727
theorem B4810006061 : Blo 1052612 4810006061 := bstep (se 3 (by rfl) ⟨901876136, by rfl⟩ : syracuseStep 4810006061 = 1803752273) B1803752273
theorem B5071585 : Blo 1052612 5071585 := bstep (se 2 (by rfl) ⟨1901844, by rfl⟩ : syracuseStep 5071585 = 3803689) B3803689
theorem B38431907 : Blo 1052612 38431907 := bstep (se 1 (by rfl) ⟨28823930, by rfl⟩ : syracuseStep 38431907 = 57647861) B57647861
theorem B7993727 : Blo 1052612 7993727 := bstep (se 1 (by rfl) ⟨5995295, by rfl⟩ : syracuseStep 7993727 = 11990591) B11990591
theorem B12844115 : Blo 1052612 12844115 := bstep (se 1 (by rfl) ⟨9633086, by rfl⟩ : syracuseStep 12844115 = 19266173) B19266173
theorem B1052699 : Blo 1052612 1052699 := bstep (se 1 (by rfl) ⟨789524, by rfl⟩ : syracuseStep 1052699 = 1579049) B1579049
theorem B27005075 : Blo 1052612 27005075 := bstep (se 1 (by rfl) ⟨20253806, by rfl⟩ : syracuseStep 27005075 = 40507613) B40507613
theorem B1053167 : Blo 1052612 1053167 := bstep (se 1 (by rfl) ⟨789875, by rfl⟩ : syracuseStep 1053167 = 1579751) B1579751
theorem B1053275 : Blo 1052612 1053275 := bstep (se 1 (by rfl) ⟨789956, by rfl⟩ : syracuseStep 1053275 = 1579913) B1579913
theorem B1054567 : Blo 1052612 1054567 := bstep (se 1 (by rfl) ⟨790925, by rfl⟩ : syracuseStep 1054567 = 1581851) B1581851
theorem B18029627 : Blo 1052612 18029627 := bstep (se 1 (by rfl) ⟨13522220, by rfl⟩ : syracuseStep 18029627 = 27044441) B27044441
theorem B1055899 : Blo 1052612 1055899 := bstep (se 1 (by rfl) ⟨791924, by rfl⟩ : syracuseStep 1055899 = 1583849) B1583849
theorem B13508279 : Blo 1052612 13508279 := bstep (se 1 (by rfl) ⟨10131209, by rfl⟩ : syracuseStep 13508279 = 20262419) B20262419
theorem B11411887 : Blo 1052612 11411887 := bstep (se 1 (by rfl) ⟨8558915, by rfl⟩ : syracuseStep 11411887 = 17117831) B17117831
theorem B106996733 : Blo 1052612 106996733 := bstep (se 3 (by rfl) ⟨20061887, by rfl⟩ : syracuseStep 106996733 = 40123775) B40123775
theorem B2368763 : Blo 1052612 2368763 := bstep (se 1 (by rfl) ⟨1776572, by rfl⟩ : syracuseStep 2368763 = 3553145) B3553145
theorem B2369249 : Blo 1052612 2369249 := bstep (se 2 (by rfl) ⟨888468, by rfl⟩ : syracuseStep 2369249 = 1776937) B1776937
theorem B8562743 : Blo 1052612 8562743 := bstep (se 1 (by rfl) ⟨6422057, by rfl⟩ : syracuseStep 8562743 = 12844115) B12844115
theorem B1584767 : Blo 1052612 1584767 := bstep (se 1 (by rfl) ⟨1188575, by rfl⟩ : syracuseStep 1584767 = 2377151) B2377151
theorem B6762113 : Blo 1052612 6762113 := bstep (se 2 (by rfl) ⟨2535792, by rfl⟩ : syracuseStep 6762113 = 5071585) B5071585
theorem B3553793 : Blo 1052612 3553793 := bstep (se 2 (by rfl) ⟨1332672, by rfl⟩ : syracuseStep 3553793 = 2665345) B2665345
theorem B2669831 : Blo 1052612 2669831 := bstep (se 1 (by rfl) ⟨2002373, by rfl⟩ : syracuseStep 2669831 = 4004747) B4004747
theorem B4506623 : Blo 1052612 4506623 := bstep (se 1 (by rfl) ⟨3379967, by rfl⟩ : syracuseStep 4506623 = 6759935) B6759935
theorem B4572911 : Blo 1052612 4572911 := bstep (se 1 (by rfl) ⟨3429683, by rfl⟩ : syracuseStep 4572911 = 6859367) B6859367
theorem B6081439 : Blo 1052612 6081439 := bstep (se 1 (by rfl) ⟨4561079, by rfl⟩ : syracuseStep 6081439 = 9122159) B9122159
theorem B11389999 : Blo 1052612 11389999 := bstep (se 1 (by rfl) ⟨8542499, by rfl⟩ : syracuseStep 11389999 = 17084999) B17084999
theorem B5329151 : Blo 1052612 5329151 := bstep (se 1 (by rfl) ⟨3996863, by rfl⟩ : syracuseStep 5329151 = 7993727) B7993727
theorem B34166771 : Blo 1052612 34166771 := bstep (se 1 (by rfl) ⟨25625078, by rfl⟩ : syracuseStep 34166771 = 51250157) B51250157
theorem B9134491 : Blo 1052612 9134491 := bstep (se 1 (by rfl) ⟨6850868, by rfl⟩ : syracuseStep 9134491 = 13701737) B13701737
theorem B5072063 : Blo 1052612 5072063 := bstep (se 1 (by rfl) ⟨3804047, by rfl⟩ : syracuseStep 5072063 = 7608095) B7608095
theorem B3206670707 : Blo 1052612 3206670707 := bstep (se 1 (by rfl) ⟨2405003030, by rfl⟩ : syracuseStep 3206670707 = 4810006061) B4810006061
theorem B5402027 : Blo 1052612 5402027 := bstep (se 1 (by rfl) ⟨4051520, by rfl⟩ : syracuseStep 5402027 = 8103041) B8103041
theorem B25621271 : Blo 1052612 25621271 := bstep (se 1 (by rfl) ⟨19215953, by rfl⟩ : syracuseStep 25621271 = 38431907) B38431907
theorem B3048607 : Blo 1052612 3048607 := bstep (se 1 (by rfl) ⟨2286455, by rfl⟩ : syracuseStep 3048607 = 4572911) B4572911
theorem B22777847 : Blo 1052612 22777847 := bstep (se 1 (by rfl) ⟨17083385, by rfl⟩ : syracuseStep 22777847 = 34166771) B34166771
theorem B1579175 : Blo 1052612 1579175 := bstep (se 1 (by rfl) ⟨1184381, by rfl⟩ : syracuseStep 1579175 = 2368763) B2368763
theorem B1579499 : Blo 1052612 1579499 := bstep (se 1 (by rfl) ⟨1184624, by rfl⟩ : syracuseStep 1579499 = 2369249) B2369249
theorem B5708495 : Blo 1052612 5708495 := bstep (se 1 (by rfl) ⟨4281371, by rfl⟩ : syracuseStep 5708495 = 8562743) B8562743
theorem B1056511 : Blo 1052612 1056511 := bstep (se 1 (by rfl) ⟨792383, by rfl⟩ : syracuseStep 1056511 = 1584767) B1584767
theorem B17080847 : Blo 1052612 17080847 := bstep (se 1 (by rfl) ⟨12810635, by rfl⟩ : syracuseStep 17080847 = 25621271) B25621271
theorem B2369195 : Blo 1052612 2369195 := bstep (se 1 (by rfl) ⟨1776896, by rfl⟩ : syracuseStep 2369195 = 3553793) B3553793
theorem B1779887 : Blo 1052612 1779887 := bstep (se 1 (by rfl) ⟨1334915, by rfl⟩ : syracuseStep 1779887 = 2669831) B2669831
theorem B15215849 : Blo 1052612 15215849 := bstep (se 2 (by rfl) ⟨5705943, by rfl⟩ : syracuseStep 15215849 = 11411887) B11411887
theorem B18003383 : Blo 1052612 18003383 := bstep (se 1 (by rfl) ⟨13502537, by rfl⟩ : syracuseStep 18003383 = 27005075) B27005075
theorem B3552767 : Blo 1052612 3552767 := bstep (se 1 (by rfl) ⟨2664575, by rfl⟩ : syracuseStep 3552767 = 5329151) B5329151
theorem B8108585 : Blo 1052612 8108585 := bstep (se 2 (by rfl) ⟨3040719, by rfl⟩ : syracuseStep 8108585 = 6081439) B6081439
theorem B15186665 : Blo 1052612 15186665 := bstep (se 2 (by rfl) ⟨5694999, by rfl⟩ : syracuseStep 15186665 = 11389999) B11389999
theorem B4508075 : Blo 1052612 4508075 := bstep (se 1 (by rfl) ⟨3381056, by rfl⟩ : syracuseStep 4508075 = 6762113) B6762113
theorem B12179321 : Blo 1052612 12179321 := bstep (se 2 (by rfl) ⟨4567245, by rfl⟩ : syracuseStep 12179321 = 9134491) B9134491
theorem B3004415 : Blo 1052612 3004415 := bstep (se 1 (by rfl) ⟨2253311, by rfl⟩ : syracuseStep 3004415 = 4506623) B4506623
theorem B13525501 : Blo 1052612 13525501 := bstep (se 3 (by rfl) ⟨2536031, by rfl⟩ : syracuseStep 13525501 = 5072063) B5072063
theorem B12019751 : Blo 1052612 12019751 := bstep (se 1 (by rfl) ⟨9014813, by rfl⟩ : syracuseStep 12019751 = 18029627) B18029627
theorem B9005519 : Blo 1052612 9005519 := bstep (se 1 (by rfl) ⟨6754139, by rfl⟩ : syracuseStep 9005519 = 13508279) B13508279
theorem B71331155 : Blo 1052612 71331155 := bstep (se 1 (by rfl) ⟨53498366, by rfl⟩ : syracuseStep 71331155 = 106996733) B106996733
theorem B2137780471 : Blo 1052612 2137780471 := bstep (se 1 (by rfl) ⟨1603335353, by rfl⟩ : syracuseStep 2137780471 = 3206670707) B3206670707
theorem B3601351 : Blo 1052612 3601351 := bstep (se 1 (by rfl) ⟨2701013, by rfl⟩ : syracuseStep 3601351 = 5402027) B5402027
theorem B2002943 : Blo 1052612 2002943 := bstep (se 1 (by rfl) ⟨1502207, by rfl⟩ : syracuseStep 2002943 = 3004415) B3004415
theorem B1052783 : Blo 1052612 1052783 := bstep (se 1 (by rfl) ⟨789587, by rfl⟩ : syracuseStep 1052783 = 1579175) B1579175
theorem B1052999 : Blo 1052612 1052999 := bstep (se 1 (by rfl) ⟨789749, by rfl⟩ : syracuseStep 1052999 = 1579499) B1579499
theorem B3805663 : Blo 1052612 3805663 := bstep (se 1 (by rfl) ⟨2854247, by rfl⟩ : syracuseStep 3805663 = 5708495) B5708495
theorem B19207205 : Blo 1052612 19207205 := bstep (se 4 (by rfl) ⟨1800675, by rfl⟩ : syracuseStep 19207205 = 3601351) B3601351
theorem B16259237 : Blo 1052612 16259237 := bstep (se 4 (by rfl) ⟨1524303, by rfl⟩ : syracuseStep 16259237 = 3048607) B3048607
theorem B1579463 : Blo 1052612 1579463 := bstep (se 1 (by rfl) ⟨1184597, by rfl⟩ : syracuseStep 1579463 = 2369195) B2369195
theorem B1186591 : Blo 1052612 1186591 := bstep (se 1 (by rfl) ⟨889943, by rfl⟩ : syracuseStep 1186591 = 1779887) B1779887
theorem B6003679 : Blo 1052612 6003679 := bstep (se 1 (by rfl) ⟨4502759, by rfl⟩ : syracuseStep 6003679 = 9005519) B9005519
theorem B47554103 : Blo 1052612 47554103 := bstep (se 1 (by rfl) ⟨35665577, by rfl⟩ : syracuseStep 47554103 = 71331155) B71331155
theorem B12002255 : Blo 1052612 12002255 := bstep (se 1 (by rfl) ⟨9001691, by rfl⟩ : syracuseStep 12002255 = 18003383) B18003383
theorem B2368511 : Blo 1052612 2368511 := bstep (se 1 (by rfl) ⟨1776383, by rfl⟩ : syracuseStep 2368511 = 3552767) B3552767
theorem B18034001 : Blo 1052612 18034001 := bstep (se 2 (by rfl) ⟨6762750, by rfl⟩ : syracuseStep 18034001 = 13525501) B13525501
theorem B15185231 : Blo 1052612 15185231 := bstep (se 1 (by rfl) ⟨11388923, by rfl⟩ : syracuseStep 15185231 = 22777847) B22777847
theorem B2850373961 : Blo 1052612 2850373961 := bstep (se 2 (by rfl) ⟨1068890235, by rfl⟩ : syracuseStep 2850373961 = 2137780471) B2137780471
theorem B11387231 : Blo 1052612 11387231 := bstep (se 1 (by rfl) ⟨8540423, by rfl⟩ : syracuseStep 11387231 = 17080847) B17080847
theorem B8013167 : Blo 1052612 8013167 := bstep (se 1 (by rfl) ⟨6009875, by rfl⟩ : syracuseStep 8013167 = 12019751) B12019751
theorem B10143899 : Blo 1052612 10143899 := bstep (se 1 (by rfl) ⟨7607924, by rfl⟩ : syracuseStep 10143899 = 15215849) B15215849
theorem B3005383 : Blo 1052612 3005383 := bstep (se 1 (by rfl) ⟨2254037, by rfl⟩ : syracuseStep 3005383 = 4508075) B4508075
theorem B8119547 : Blo 1052612 8119547 := bstep (se 1 (by rfl) ⟨6089660, by rfl⟩ : syracuseStep 8119547 = 12179321) B12179321
theorem B5405723 : Blo 1052612 5405723 := bstep (se 1 (by rfl) ⟨4054292, by rfl⟩ : syracuseStep 5405723 = 8108585) B8108585
theorem B10124443 : Blo 1052612 10124443 := bstep (se 1 (by rfl) ⟨7593332, by rfl⟩ : syracuseStep 10124443 = 15186665) B15186665
theorem B1900249307 : Blo 1052612 1900249307 := bstep (se 1 (by rfl) ⟨1425186980, by rfl⟩ : syracuseStep 1900249307 = 2850373961) B2850373961
theorem B5342111 : Blo 1052612 5342111 := bstep (se 1 (by rfl) ⟨4006583, by rfl⟩ : syracuseStep 5342111 = 8013167) B8013167
theorem B1052975 : Blo 1052612 1052975 := bstep (se 1 (by rfl) ⟨789731, by rfl⟩ : syracuseStep 1052975 = 1579463) B1579463
theorem B8001503 : Blo 1052612 8001503 := bstep (se 1 (by rfl) ⟨6001127, by rfl⟩ : syracuseStep 8001503 = 12002255) B12002255
theorem B1579007 : Blo 1052612 1579007 := bstep (se 1 (by rfl) ⟨1184255, by rfl⟩ : syracuseStep 1579007 = 2368511) B2368511
theorem B5413031 : Blo 1052612 5413031 := bstep (se 1 (by rfl) ⟨4059773, by rfl⟩ : syracuseStep 5413031 = 8119547) B8119547
theorem B1582121 : Blo 1052612 1582121 := bstep (se 2 (by rfl) ⟨593295, by rfl⟩ : syracuseStep 1582121 = 1186591) B1186591
theorem B4007177 : Blo 1052612 4007177 := bstep (se 2 (by rfl) ⟨1502691, by rfl⟩ : syracuseStep 4007177 = 3005383) B3005383
theorem B8004905 : Blo 1052612 8004905 := bstep (se 2 (by rfl) ⟨3001839, by rfl⟩ : syracuseStep 8004905 = 6003679) B6003679
theorem B6762599 : Blo 1052612 6762599 := bstep (se 1 (by rfl) ⟨5071949, by rfl⟩ : syracuseStep 6762599 = 10143899) B10143899
theorem B31702735 : Blo 1052612 31702735 := bstep (se 1 (by rfl) ⟨23777051, by rfl⟩ : syracuseStep 31702735 = 47554103) B47554103
theorem B7591487 : Blo 1052612 7591487 := bstep (se 1 (by rfl) ⟨5693615, by rfl⟩ : syracuseStep 7591487 = 11387231) B11387231
theorem B1335295 : Blo 1052612 1335295 := bstep (se 1 (by rfl) ⟨1001471, by rfl⟩ : syracuseStep 1335295 = 2002943) B2002943
theorem B12804803 : Blo 1052612 12804803 := bstep (se 1 (by rfl) ⟨9603602, by rfl⟩ : syracuseStep 12804803 = 19207205) B19207205
theorem B10839491 : Blo 1052612 10839491 := bstep (se 1 (by rfl) ⟨8129618, by rfl⟩ : syracuseStep 10839491 = 16259237) B16259237
theorem B5074217 : Blo 1052612 5074217 := bstep (se 2 (by rfl) ⟨1902831, by rfl⟩ : syracuseStep 5074217 = 3805663) B3805663
theorem B12022667 : Blo 1052612 12022667 := bstep (se 1 (by rfl) ⟨9017000, by rfl⟩ : syracuseStep 12022667 = 18034001) B18034001
theorem B10123487 : Blo 1052612 10123487 := bstep (se 1 (by rfl) ⟨7592615, by rfl⟩ : syracuseStep 10123487 = 15185231) B15185231
theorem B13499257 : Blo 1052612 13499257 := bstep (se 2 (by rfl) ⟨5062221, by rfl⟩ : syracuseStep 13499257 = 10124443) B10124443
theorem B3603815 : Blo 1052612 3603815 := bstep (se 1 (by rfl) ⟨2702861, by rfl⟩ : syracuseStep 3603815 = 5405723) B5405723
theorem B1052671 : Blo 1052612 1052671 := bstep (se 1 (by rfl) ⟨789503, by rfl⟩ : syracuseStep 1052671 = 1579007) B1579007
theorem B3608687 : Blo 1052612 3608687 := bstep (se 1 (by rfl) ⟨2706515, by rfl⟩ : syracuseStep 3608687 = 5413031) B5413031
theorem B1054747 : Blo 1052612 1054747 := bstep (se 1 (by rfl) ⟨791060, by rfl⟩ : syracuseStep 1054747 = 1582121) B1582121
theorem B3382811 : Blo 1052612 3382811 := bstep (se 1 (by rfl) ⟨2537108, by rfl⟩ : syracuseStep 3382811 = 5074217) B5074217
theorem B17999009 : Blo 1052612 17999009 := bstep (se 2 (by rfl) ⟨6749628, by rfl⟩ : syracuseStep 17999009 = 13499257) B13499257
theorem B2402543 : Blo 1052612 2402543 := bstep (se 1 (by rfl) ⟨1801907, by rfl⟩ : syracuseStep 2402543 = 3603815) B3603815
theorem B1780393 : Blo 1052612 1780393 := bstep (se 2 (by rfl) ⟨667647, by rfl⟩ : syracuseStep 1780393 = 1335295) B1335295
theorem B8536535 : Blo 1052612 8536535 := bstep (se 1 (by rfl) ⟨6402401, by rfl⟩ : syracuseStep 8536535 = 12804803) B12804803
theorem B2671451 : Blo 1052612 2671451 := bstep (se 1 (by rfl) ⟨2003588, by rfl⟩ : syracuseStep 2671451 = 4007177) B4007177
theorem B7226327 : Blo 1052612 7226327 := bstep (se 1 (by rfl) ⟨5419745, by rfl⟩ : syracuseStep 7226327 = 10839491) B10839491
theorem B4508399 : Blo 1052612 4508399 := bstep (se 1 (by rfl) ⟨3381299, by rfl⟩ : syracuseStep 4508399 = 6762599) B6762599
theorem B8015111 : Blo 1052612 8015111 := bstep (se 1 (by rfl) ⟨6011333, by rfl⟩ : syracuseStep 8015111 = 12022667) B12022667
theorem B1266832871 : Blo 1052612 1266832871 := bstep (se 1 (by rfl) ⟨950124653, by rfl⟩ : syracuseStep 1266832871 = 1900249307) B1900249307
theorem B3561407 : Blo 1052612 3561407 := bstep (se 1 (by rfl) ⟨2671055, by rfl⟩ : syracuseStep 3561407 = 5342111) B5342111
theorem B5334335 : Blo 1052612 5334335 := bstep (se 1 (by rfl) ⟨4000751, by rfl⟩ : syracuseStep 5334335 = 8001503) B8001503
theorem B20243965 : Blo 1052612 20243965 := bstep (se 3 (by rfl) ⟨3795743, by rfl⟩ : syracuseStep 20243965 = 7591487) B7591487
theorem B5336603 : Blo 1052612 5336603 := bstep (se 1 (by rfl) ⟨4002452, by rfl⟩ : syracuseStep 5336603 = 8004905) B8004905
theorem B169081253 : Blo 1052612 169081253 := bstep (se 4 (by rfl) ⟨15851367, by rfl⟩ : syracuseStep 169081253 = 31702735) B31702735
theorem B6748991 : Blo 1052612 6748991 := bstep (se 1 (by rfl) ⟨5061743, by rfl⟩ : syracuseStep 6748991 = 10123487) B10123487
theorem B4817551 : Blo 1052612 4817551 := bstep (se 1 (by rfl) ⟨3613163, by rfl⟩ : syracuseStep 4817551 = 7226327) B7226327
theorem B5343407 : Blo 1052612 5343407 := bstep (se 1 (by rfl) ⟨4007555, by rfl⟩ : syracuseStep 5343407 = 8015111) B8015111
theorem B11999339 : Blo 1052612 11999339 := bstep (se 1 (by rfl) ⟨8999504, by rfl⟩ : syracuseStep 11999339 = 17999009) B17999009
theorem B4499327 : Blo 1052612 4499327 := bstep (se 1 (by rfl) ⟨3374495, by rfl⟩ : syracuseStep 4499327 = 6748991) B6748991
theorem B1780967 : Blo 1052612 1780967 := bstep (se 1 (by rfl) ⟨1335725, by rfl⟩ : syracuseStep 1780967 = 2671451) B2671451
theorem B2405791 : Blo 1052612 2405791 := bstep (se 1 (by rfl) ⟨1804343, by rfl⟩ : syracuseStep 2405791 = 3608687) B3608687
theorem B2373857 : Blo 1052612 2373857 := bstep (se 2 (by rfl) ⟨890196, by rfl⟩ : syracuseStep 2373857 = 1780393) B1780393
theorem B2374271 : Blo 1052612 2374271 := bstep (se 1 (by rfl) ⟨1780703, by rfl⟩ : syracuseStep 2374271 = 3561407) B3561407
theorem B3556223 : Blo 1052612 3556223 := bstep (se 1 (by rfl) ⟨2667167, by rfl⟩ : syracuseStep 3556223 = 5334335) B5334335
theorem B3557735 : Blo 1052612 3557735 := bstep (se 1 (by rfl) ⟨2668301, by rfl⟩ : syracuseStep 3557735 = 5336603) B5336603
theorem B5691023 : Blo 1052612 5691023 := bstep (se 1 (by rfl) ⟨4268267, by rfl⟩ : syracuseStep 5691023 = 8536535) B8536535
theorem B3005599 : Blo 1052612 3005599 := bstep (se 1 (by rfl) ⟨2254199, by rfl⟩ : syracuseStep 3005599 = 4508399) B4508399
theorem B26991953 : Blo 1052612 26991953 := bstep (se 2 (by rfl) ⟨10121982, by rfl⟩ : syracuseStep 26991953 = 20243965) B20243965
theorem B844555247 : Blo 1052612 844555247 := bstep (se 1 (by rfl) ⟨633416435, by rfl⟩ : syracuseStep 844555247 = 1266832871) B1266832871
theorem B2255207 : Blo 1052612 2255207 := bstep (se 1 (by rfl) ⟨1691405, by rfl⟩ : syracuseStep 2255207 = 3382811) B3382811
theorem B1601695 : Blo 1052612 1601695 := bstep (se 1 (by rfl) ⟨1201271, by rfl⟩ : syracuseStep 1601695 = 2402543) B2402543
theorem B112720835 : Blo 1052612 112720835 := bstep (se 1 (by rfl) ⟨84540626, by rfl⟩ : syracuseStep 112720835 = 169081253) B169081253
theorem B6423401 : Blo 1052612 6423401 := bstep (se 2 (by rfl) ⟨2408775, by rfl⟩ : syracuseStep 6423401 = 4817551) B4817551
theorem B7999559 : Blo 1052612 7999559 := bstep (se 1 (by rfl) ⟨5999669, by rfl⟩ : syracuseStep 7999559 = 11999339) B11999339
theorem B17994635 : Blo 1052612 17994635 := bstep (se 1 (by rfl) ⟨13495976, by rfl⟩ : syracuseStep 17994635 = 26991953) B26991953
theorem B2135593 : Blo 1052612 2135593 := bstep (se 2 (by rfl) ⟨800847, by rfl⟩ : syracuseStep 2135593 = 1601695) B1601695
theorem B1187311 : Blo 1052612 1187311 := bstep (se 1 (by rfl) ⟨890483, by rfl⟩ : syracuseStep 1187311 = 1780967) B1780967
theorem B1582571 : Blo 1052612 1582571 := bstep (se 1 (by rfl) ⟨1186928, by rfl⟩ : syracuseStep 1582571 = 2373857) B2373857
theorem B4007465 : Blo 1052612 4007465 := bstep (se 2 (by rfl) ⟨1502799, by rfl⟩ : syracuseStep 4007465 = 3005599) B3005599
theorem B1582847 : Blo 1052612 1582847 := bstep (se 1 (by rfl) ⟨1187135, by rfl⟩ : syracuseStep 1582847 = 2374271) B2374271
theorem B75147223 : Blo 1052612 75147223 := bstep (se 1 (by rfl) ⟨56360417, by rfl⟩ : syracuseStep 75147223 = 112720835) B112720835
theorem B2370815 : Blo 1052612 2370815 := bstep (se 1 (by rfl) ⟨1778111, by rfl⟩ : syracuseStep 2370815 = 3556223) B3556223
theorem B2371823 : Blo 1052612 2371823 := bstep (se 1 (by rfl) ⟨1778867, by rfl⟩ : syracuseStep 2371823 = 3557735) B3557735
theorem B563036831 : Blo 1052612 563036831 := bstep (se 1 (by rfl) ⟨422277623, by rfl⟩ : syracuseStep 563036831 = 844555247) B844555247
theorem B6013885 : Blo 1052612 6013885 := bstep (se 3 (by rfl) ⟨1127603, by rfl⟩ : syracuseStep 6013885 = 2255207) B2255207
theorem B2999551 : Blo 1052612 2999551 := bstep (se 1 (by rfl) ⟨2249663, by rfl⟩ : syracuseStep 2999551 = 4499327) B4499327
theorem B3562271 : Blo 1052612 3562271 := bstep (se 1 (by rfl) ⟨2671703, by rfl⟩ : syracuseStep 3562271 = 5343407) B5343407
theorem B3794015 : Blo 1052612 3794015 := bstep (se 1 (by rfl) ⟨2845511, by rfl⟩ : syracuseStep 3794015 = 5691023) B5691023
theorem B3207721 : Blo 1052612 3207721 := bstep (se 2 (by rfl) ⟨1202895, by rfl⟩ : syracuseStep 3207721 = 2405791) B2405791
theorem B375357887 : Blo 1052612 375357887 := bstep (se 1 (by rfl) ⟨281518415, by rfl⟩ : syracuseStep 375357887 = 563036831) B563036831
theorem B3999401 : Blo 1052612 3999401 := bstep (se 2 (by rfl) ⟨1499775, by rfl⟩ : syracuseStep 3999401 = 2999551) B2999551
theorem B11996423 : Blo 1052612 11996423 := bstep (se 1 (by rfl) ⟨8997317, by rfl⟩ : syracuseStep 11996423 = 17994635) B17994635
theorem B2529343 : Blo 1052612 2529343 := bstep (se 1 (by rfl) ⟨1897007, by rfl⟩ : syracuseStep 2529343 = 3794015) B3794015
theorem B1055047 : Blo 1052612 1055047 := bstep (se 1 (by rfl) ⟨791285, by rfl⟩ : syracuseStep 1055047 = 1582571) B1582571
theorem B1055231 : Blo 1052612 1055231 := bstep (se 1 (by rfl) ⟨791423, by rfl⟩ : syracuseStep 1055231 = 1582847) B1582847
theorem B1580543 : Blo 1052612 1580543 := bstep (se 1 (by rfl) ⟨1185407, by rfl⟩ : syracuseStep 1580543 = 2370815) B2370815
theorem B1581215 : Blo 1052612 1581215 := bstep (se 1 (by rfl) ⟨1185911, by rfl⟩ : syracuseStep 1581215 = 2371823) B2371823
theorem B1583081 : Blo 1052612 1583081 := bstep (se 2 (by rfl) ⟨593655, by rfl⟩ : syracuseStep 1583081 = 1187311) B1187311
theorem B2374847 : Blo 1052612 2374847 := bstep (se 1 (by rfl) ⟨1781135, by rfl⟩ : syracuseStep 2374847 = 3562271) B3562271
theorem B4276961 : Blo 1052612 4276961 := bstep (se 2 (by rfl) ⟨1603860, by rfl⟩ : syracuseStep 4276961 = 3207721) B3207721
theorem B2671643 : Blo 1052612 2671643 := bstep (se 1 (by rfl) ⟨2003732, by rfl⟩ : syracuseStep 2671643 = 4007465) B4007465
theorem B4282267 : Blo 1052612 4282267 := bstep (se 1 (by rfl) ⟨3211700, by rfl⟩ : syracuseStep 4282267 = 6423401) B6423401
theorem B8018513 : Blo 1052612 8018513 := bstep (se 2 (by rfl) ⟨3006942, by rfl⟩ : syracuseStep 8018513 = 6013885) B6013885
theorem B100196297 : Blo 1052612 100196297 := bstep (se 2 (by rfl) ⟨37573611, by rfl⟩ : syracuseStep 100196297 = 75147223) B75147223
theorem B5333039 : Blo 1052612 5333039 := bstep (se 1 (by rfl) ⟨3999779, by rfl⟩ : syracuseStep 5333039 = 7999559) B7999559
theorem B2847457 : Blo 1052612 2847457 := bstep (se 2 (by rfl) ⟨1067796, by rfl⟩ : syracuseStep 2847457 = 2135593) B2135593
theorem B2851307 : Blo 1052612 2851307 := bstep (se 1 (by rfl) ⟨2138480, by rfl⟩ : syracuseStep 2851307 = 4276961) B4276961
theorem B7997615 : Blo 1052612 7997615 := bstep (se 1 (by rfl) ⟨5998211, by rfl⟩ : syracuseStep 7997615 = 11996423) B11996423
theorem B5345675 : Blo 1052612 5345675 := bstep (se 1 (by rfl) ⟨4009256, by rfl⟩ : syracuseStep 5345675 = 8018513) B8018513
theorem B1053695 : Blo 1052612 1053695 := bstep (se 1 (by rfl) ⟨790271, by rfl⟩ : syracuseStep 1053695 = 1580543) B1580543
theorem B1054143 : Blo 1052612 1054143 := bstep (se 1 (by rfl) ⟨790607, by rfl⟩ : syracuseStep 1054143 = 1581215) B1581215
theorem B1055387 : Blo 1052612 1055387 := bstep (se 1 (by rfl) ⟨791540, by rfl⟩ : syracuseStep 1055387 = 1583081) B1583081
theorem B5709689 : Blo 1052612 5709689 := bstep (se 2 (by rfl) ⟨2141133, by rfl⟩ : syracuseStep 5709689 = 4282267) B4282267
theorem B1583231 : Blo 1052612 1583231 := bstep (se 1 (by rfl) ⟨1187423, by rfl⟩ : syracuseStep 1583231 = 2374847) B2374847
theorem B1781095 : Blo 1052612 1781095 := bstep (se 1 (by rfl) ⟨1335821, by rfl⟩ : syracuseStep 1781095 = 2671643) B2671643
theorem B2666267 : Blo 1052612 2666267 := bstep (se 1 (by rfl) ⟨1999700, by rfl⟩ : syracuseStep 2666267 = 3999401) B3999401
theorem B15186437 : Blo 1052612 15186437 := bstep (se 4 (by rfl) ⟨1423728, by rfl⟩ : syracuseStep 15186437 = 2847457) B2847457
theorem B66797531 : Blo 1052612 66797531 := bstep (se 1 (by rfl) ⟨50098148, by rfl⟩ : syracuseStep 66797531 = 100196297) B100196297
theorem B3555359 : Blo 1052612 3555359 := bstep (se 1 (by rfl) ⟨2666519, by rfl⟩ : syracuseStep 3555359 = 5333039) B5333039
theorem B250238591 : Blo 1052612 250238591 := bstep (se 1 (by rfl) ⟨187678943, by rfl⟩ : syracuseStep 250238591 = 375357887) B375357887
theorem B3372457 : Blo 1052612 3372457 := bstep (se 2 (by rfl) ⟨1264671, by rfl⟩ : syracuseStep 3372457 = 2529343) B2529343
theorem B1900871 : Blo 1052612 1900871 := bstep (se 1 (by rfl) ⟨1425653, by rfl⟩ : syracuseStep 1900871 = 2851307) B2851307
theorem B166825727 : Blo 1052612 166825727 := bstep (se 1 (by rfl) ⟨125119295, by rfl⟩ : syracuseStep 166825727 = 250238591) B250238591
theorem B3806459 : Blo 1052612 3806459 := bstep (se 1 (by rfl) ⟨2854844, by rfl⟩ : syracuseStep 3806459 = 5709689) B5709689
theorem B1055487 : Blo 1052612 1055487 := bstep (se 1 (by rfl) ⟨791615, by rfl⟩ : syracuseStep 1055487 = 1583231) B1583231
theorem B4496609 : Blo 1052612 4496609 := bstep (se 2 (by rfl) ⟨1686228, by rfl⟩ : syracuseStep 4496609 = 3372457) B3372457
theorem B1777511 : Blo 1052612 1777511 := bstep (se 1 (by rfl) ⟨1333133, by rfl⟩ : syracuseStep 1777511 = 2666267) B2666267
theorem B2370239 : Blo 1052612 2370239 := bstep (se 1 (by rfl) ⟨1777679, by rfl⟩ : syracuseStep 2370239 = 3555359) B3555359
theorem B2374793 : Blo 1052612 2374793 := bstep (se 2 (by rfl) ⟨890547, by rfl⟩ : syracuseStep 2374793 = 1781095) B1781095
theorem B5331743 : Blo 1052612 5331743 := bstep (se 1 (by rfl) ⟨3998807, by rfl⟩ : syracuseStep 5331743 = 7997615) B7997615
theorem B3563783 : Blo 1052612 3563783 := bstep (se 1 (by rfl) ⟨2672837, by rfl⟩ : syracuseStep 3563783 = 5345675) B5345675
theorem B10124291 : Blo 1052612 10124291 := bstep (se 1 (by rfl) ⟨7593218, by rfl⟩ : syracuseStep 10124291 = 15186437) B15186437
theorem B44531687 : Blo 1052612 44531687 := bstep (se 1 (by rfl) ⟨33398765, by rfl⟩ : syracuseStep 44531687 = 66797531) B66797531
theorem B111217151 : Blo 1052612 111217151 := bstep (se 1 (by rfl) ⟨83412863, by rfl⟩ : syracuseStep 111217151 = 166825727) B166825727
theorem B1185007 : Blo 1052612 1185007 := bstep (se 1 (by rfl) ⟨888755, by rfl⟩ : syracuseStep 1185007 = 1777511) B1777511
theorem B1580159 : Blo 1052612 1580159 := bstep (se 1 (by rfl) ⟨1185119, by rfl⟩ : syracuseStep 1580159 = 2370239) B2370239
theorem B1583195 : Blo 1052612 1583195 := bstep (se 1 (by rfl) ⟨1187396, by rfl⟩ : syracuseStep 1583195 = 2374793) B2374793
theorem B2537639 : Blo 1052612 2537639 := bstep (se 1 (by rfl) ⟨1903229, by rfl⟩ : syracuseStep 2537639 = 3806459) B3806459
theorem B3554495 : Blo 1052612 3554495 := bstep (se 1 (by rfl) ⟨2665871, by rfl⟩ : syracuseStep 3554495 = 5331743) B5331743
theorem B2997739 : Blo 1052612 2997739 := bstep (se 1 (by rfl) ⟨2248304, by rfl⟩ : syracuseStep 2997739 = 4496609) B4496609
theorem B2375855 : Blo 1052612 2375855 := bstep (se 1 (by rfl) ⟨1781891, by rfl⟩ : syracuseStep 2375855 = 3563783) B3563783
theorem B1267247 : Blo 1052612 1267247 := bstep (se 1 (by rfl) ⟨950435, by rfl⟩ : syracuseStep 1267247 = 1900871) B1900871
theorem B6749527 : Blo 1052612 6749527 := bstep (se 1 (by rfl) ⟨5062145, by rfl⟩ : syracuseStep 6749527 = 10124291) B10124291
theorem B29687791 : Blo 1052612 29687791 := bstep (se 1 (by rfl) ⟨22265843, by rfl⟩ : syracuseStep 29687791 = 44531687) B44531687
theorem B3379325 : Blo 1052612 3379325 := bstep (se 3 (by rfl) ⟨633623, by rfl⟩ : syracuseStep 3379325 = 1267247) B1267247
theorem B1053439 : Blo 1052612 1053439 := bstep (se 1 (by rfl) ⟨790079, by rfl⟩ : syracuseStep 1053439 = 1580159) B1580159
theorem B1055463 : Blo 1052612 1055463 := bstep (se 1 (by rfl) ⟨791597, by rfl⟩ : syracuseStep 1055463 = 1583195) B1583195
theorem B1580009 : Blo 1052612 1580009 := bstep (se 2 (by rfl) ⟨592503, by rfl⟩ : syracuseStep 1580009 = 1185007) B1185007
theorem B2369663 : Blo 1052612 2369663 := bstep (se 1 (by rfl) ⟨1777247, by rfl⟩ : syracuseStep 2369663 = 3554495) B3554495
theorem B1583903 : Blo 1052612 1583903 := bstep (se 1 (by rfl) ⟨1187927, by rfl⟩ : syracuseStep 1583903 = 2375855) B2375855
theorem B1691759 : Blo 1052612 1691759 := bstep (se 1 (by rfl) ⟨1268819, by rfl⟩ : syracuseStep 1691759 = 2537639) B2537639
theorem B8999369 : Blo 1052612 8999369 := bstep (se 2 (by rfl) ⟨3374763, by rfl⟩ : syracuseStep 8999369 = 6749527) B6749527
theorem B296579069 : Blo 1052612 296579069 := bstep (se 3 (by rfl) ⟨55608575, by rfl⟩ : syracuseStep 296579069 = 111217151) B111217151
theorem B3996985 : Blo 1052612 3996985 := bstep (se 2 (by rfl) ⟨1498869, by rfl⟩ : syracuseStep 3996985 = 2997739) B2997739
theorem B39583721 : Blo 1052612 39583721 := bstep (se 2 (by rfl) ⟨14843895, by rfl⟩ : syracuseStep 39583721 = 29687791) B29687791
theorem B9011533 : Blo 1052612 9011533 := bstep (se 3 (by rfl) ⟨1689662, by rfl⟩ : syracuseStep 9011533 = 3379325) B3379325
theorem B5999579 : Blo 1052612 5999579 := bstep (se 1 (by rfl) ⟨4499684, by rfl⟩ : syracuseStep 5999579 = 8999369) B8999369
theorem B1053339 : Blo 1052612 1053339 := bstep (se 1 (by rfl) ⟨790004, by rfl⟩ : syracuseStep 1053339 = 1580009) B1580009
theorem B1579775 : Blo 1052612 1579775 := bstep (se 1 (by rfl) ⟨1184831, by rfl⟩ : syracuseStep 1579775 = 2369663) B2369663
theorem B1055935 : Blo 1052612 1055935 := bstep (se 1 (by rfl) ⟨791951, by rfl⟩ : syracuseStep 1055935 = 1583903) B1583903
theorem B26389147 : Blo 1052612 26389147 := bstep (se 1 (by rfl) ⟨19791860, by rfl⟩ : syracuseStep 26389147 = 39583721) B39583721
theorem B1127839 : Blo 1052612 1127839 := bstep (se 1 (by rfl) ⟨845879, by rfl⟩ : syracuseStep 1127839 = 1691759) B1691759
theorem B5329313 : Blo 1052612 5329313 := bstep (se 2 (by rfl) ⟨1998492, by rfl⟩ : syracuseStep 5329313 = 3996985) B3996985
theorem B197719379 : Blo 1052612 197719379 := bstep (se 1 (by rfl) ⟨148289534, by rfl⟩ : syracuseStep 197719379 = 296579069) B296579069
theorem B3999719 : Blo 1052612 3999719 := bstep (se 1 (by rfl) ⟨2999789, by rfl⟩ : syracuseStep 3999719 = 5999579) B5999579
theorem B1053183 : Blo 1052612 1053183 := bstep (se 1 (by rfl) ⟨789887, by rfl⟩ : syracuseStep 1053183 = 1579775) B1579775
theorem B3552875 : Blo 1052612 3552875 := bstep (se 1 (by rfl) ⟨2664656, by rfl⟩ : syracuseStep 3552875 = 5329313) B5329313
theorem B131812919 : Blo 1052612 131812919 := bstep (se 1 (by rfl) ⟨98859689, by rfl⟩ : syracuseStep 131812919 = 197719379) B197719379
theorem B12015377 : Blo 1052612 12015377 := bstep (se 2 (by rfl) ⟨4505766, by rfl⟩ : syracuseStep 12015377 = 9011533) B9011533
theorem B35185529 : Blo 1052612 35185529 := bstep (se 2 (by rfl) ⟨13194573, by rfl⟩ : syracuseStep 35185529 = 26389147) B26389147
theorem B1503785 : Blo 1052612 1503785 := bstep (se 2 (by rfl) ⟨563919, by rfl⟩ : syracuseStep 1503785 = 1127839) B1127839
theorem B2368583 : Blo 1052612 2368583 := bstep (se 1 (by rfl) ⟨1776437, by rfl⟩ : syracuseStep 2368583 = 3552875) B3552875
theorem B2666479 : Blo 1052612 2666479 := bstep (se 1 (by rfl) ⟨1999859, by rfl⟩ : syracuseStep 2666479 = 3999719) B3999719
theorem B4010093 : Blo 1052612 4010093 := bstep (se 3 (by rfl) ⟨751892, by rfl⟩ : syracuseStep 4010093 = 1503785) B1503785
theorem B93828077 : Blo 1052612 93828077 := bstep (se 3 (by rfl) ⟨17592764, by rfl⟩ : syracuseStep 93828077 = 35185529) B35185529
theorem B8010251 : Blo 1052612 8010251 := bstep (se 1 (by rfl) ⟨6007688, by rfl⟩ : syracuseStep 8010251 = 12015377) B12015377
theorem B87875279 : Blo 1052612 87875279 := bstep (se 1 (by rfl) ⟨65906459, by rfl⟩ : syracuseStep 87875279 = 131812919) B131812919
theorem B1579055 : Blo 1052612 1579055 := bstep (se 1 (by rfl) ⟨1184291, by rfl⟩ : syracuseStep 1579055 = 2368583) B2368583
theorem B3555305 : Blo 1052612 3555305 := bstep (se 2 (by rfl) ⟨1333239, by rfl⟩ : syracuseStep 3555305 = 2666479) B2666479
theorem B2673395 : Blo 1052612 2673395 := bstep (se 1 (by rfl) ⟨2005046, by rfl⟩ : syracuseStep 2673395 = 4010093) B4010093
theorem B58583519 : Blo 1052612 58583519 := bstep (se 1 (by rfl) ⟨43937639, by rfl⟩ : syracuseStep 58583519 = 87875279) B87875279
theorem B62552051 : Blo 1052612 62552051 := bstep (se 1 (by rfl) ⟨46914038, by rfl⟩ : syracuseStep 62552051 = 93828077) B93828077
theorem B5340167 : Blo 1052612 5340167 := bstep (se 1 (by rfl) ⟨4005125, by rfl⟩ : syracuseStep 5340167 = 8010251) B8010251
theorem B1052703 : Blo 1052612 1052703 := bstep (se 1 (by rfl) ⟨789527, by rfl⟩ : syracuseStep 1052703 = 1579055) B1579055
theorem B2370203 : Blo 1052612 2370203 := bstep (se 1 (by rfl) ⟨1777652, by rfl⟩ : syracuseStep 2370203 = 3555305) B3555305
theorem B1782263 : Blo 1052612 1782263 := bstep (se 1 (by rfl) ⟨1336697, by rfl⟩ : syracuseStep 1782263 = 2673395) B2673395
theorem B41701367 : Blo 1052612 41701367 := bstep (se 1 (by rfl) ⟨31276025, by rfl⟩ : syracuseStep 41701367 = 62552051) B62552051
theorem B3560111 : Blo 1052612 3560111 := bstep (se 1 (by rfl) ⟨2670083, by rfl⟩ : syracuseStep 3560111 = 5340167) B5340167
theorem B39055679 : Blo 1052612 39055679 := bstep (se 1 (by rfl) ⟨29291759, by rfl⟩ : syracuseStep 39055679 = 58583519) B58583519
theorem B1580135 : Blo 1052612 1580135 := bstep (se 1 (by rfl) ⟨1185101, by rfl⟩ : syracuseStep 1580135 = 2370203) B2370203
theorem B1188175 : Blo 1052612 1188175 := bstep (se 1 (by rfl) ⟨891131, by rfl⟩ : syracuseStep 1188175 = 1782263) B1782263
theorem B27800911 : Blo 1052612 27800911 := bstep (se 1 (by rfl) ⟨20850683, by rfl⟩ : syracuseStep 27800911 = 41701367) B41701367
theorem B2373407 : Blo 1052612 2373407 := bstep (se 1 (by rfl) ⟨1780055, by rfl⟩ : syracuseStep 2373407 = 3560111) B3560111
theorem B26037119 : Blo 1052612 26037119 := bstep (se 1 (by rfl) ⟨19527839, by rfl⟩ : syracuseStep 26037119 = 39055679) B39055679
theorem B1053423 : Blo 1052612 1053423 := bstep (se 1 (by rfl) ⟨790067, by rfl⟩ : syracuseStep 1053423 = 1580135) B1580135
theorem B37067881 : Blo 1052612 37067881 := bstep (se 2 (by rfl) ⟨13900455, by rfl⟩ : syracuseStep 37067881 = 27800911) B27800911
theorem B1582271 : Blo 1052612 1582271 := bstep (se 1 (by rfl) ⟨1186703, by rfl⟩ : syracuseStep 1582271 = 2373407) B2373407
theorem B1584233 : Blo 1052612 1584233 := bstep (se 2 (by rfl) ⟨594087, by rfl⟩ : syracuseStep 1584233 = 1188175) B1188175
theorem B17358079 : Blo 1052612 17358079 := bstep (se 1 (by rfl) ⟨13018559, by rfl⟩ : syracuseStep 17358079 = 26037119) B26037119
theorem B1054847 : Blo 1052612 1054847 := bstep (se 1 (by rfl) ⟨791135, by rfl⟩ : syracuseStep 1054847 = 1582271) B1582271
theorem B1056155 : Blo 1052612 1056155 := bstep (se 1 (by rfl) ⟨792116, by rfl⟩ : syracuseStep 1056155 = 1584233) B1584233
theorem B49423841 : Blo 1052612 49423841 := bstep (se 2 (by rfl) ⟨18533940, by rfl⟩ : syracuseStep 49423841 = 37067881) B37067881
theorem B23144105 : Blo 1052612 23144105 := bstep (se 2 (by rfl) ⟨8679039, by rfl⟩ : syracuseStep 23144105 = 17358079) B17358079
theorem B32949227 : Blo 1052612 32949227 := bstep (se 1 (by rfl) ⟨24711920, by rfl⟩ : syracuseStep 32949227 = 49423841) B49423841
theorem B15429403 : Blo 1052612 15429403 := bstep (se 1 (by rfl) ⟨11572052, by rfl⟩ : syracuseStep 15429403 = 23144105) B23144105
theorem B87864605 : Blo 1052612 87864605 := bstep (se 3 (by rfl) ⟨16474613, by rfl⟩ : syracuseStep 87864605 = 32949227) B32949227
theorem B20572537 : Blo 1052612 20572537 := bstep (se 2 (by rfl) ⟨7714701, by rfl⟩ : syracuseStep 20572537 = 15429403) B15429403
theorem B27430049 : Blo 1052612 27430049 := bstep (se 2 (by rfl) ⟨10286268, by rfl⟩ : syracuseStep 27430049 = 20572537) B20572537
theorem B58576403 : Blo 1052612 58576403 := bstep (se 1 (by rfl) ⟨43932302, by rfl⟩ : syracuseStep 58576403 = 87864605) B87864605
theorem B73146797 : Blo 1052612 73146797 := bstep (se 3 (by rfl) ⟨13715024, by rfl⟩ : syracuseStep 73146797 = 27430049) B27430049
theorem B156203741 : Blo 1052612 156203741 := bstep (se 3 (by rfl) ⟨29288201, by rfl⟩ : syracuseStep 156203741 = 58576403) B58576403
theorem B48764531 : Blo 1052612 48764531 := bstep (se 1 (by rfl) ⟨36573398, by rfl⟩ : syracuseStep 48764531 = 73146797) B73146797
theorem B104135827 : Blo 1052612 104135827 := bstep (se 1 (by rfl) ⟨78101870, by rfl⟩ : syracuseStep 104135827 = 156203741) B156203741
theorem B32509687 : Blo 1052612 32509687 := bstep (se 1 (by rfl) ⟨24382265, by rfl⟩ : syracuseStep 32509687 = 48764531) B48764531
theorem B138847769 : Blo 1052612 138847769 := bstep (se 2 (by rfl) ⟨52067913, by rfl⟩ : syracuseStep 138847769 = 104135827) B104135827
theorem B43346249 : Blo 1052612 43346249 := bstep (se 2 (by rfl) ⟨16254843, by rfl⟩ : syracuseStep 43346249 = 32509687) B32509687
theorem B92565179 : Blo 1052612 92565179 := bstep (se 1 (by rfl) ⟨69423884, by rfl⟩ : syracuseStep 92565179 = 138847769) B138847769
theorem B61710119 : Blo 1052612 61710119 := bstep (se 1 (by rfl) ⟨46282589, by rfl⟩ : syracuseStep 61710119 = 92565179) B92565179
theorem B28897499 : Blo 1052612 28897499 := bstep (se 1 (by rfl) ⟨21673124, by rfl⟩ : syracuseStep 28897499 = 43346249) B43346249
theorem B41140079 : Blo 1052612 41140079 := bstep (se 1 (by rfl) ⟨30855059, by rfl⟩ : syracuseStep 41140079 = 61710119) B61710119
theorem B19264999 : Blo 1052612 19264999 := bstep (se 1 (by rfl) ⟨14448749, by rfl⟩ : syracuseStep 19264999 = 28897499) B28897499
theorem B25686665 : Blo 1052612 25686665 := bstep (se 2 (by rfl) ⟨9632499, by rfl⟩ : syracuseStep 25686665 = 19264999) B19264999
theorem B27426719 : Blo 1052612 27426719 := bstep (se 1 (by rfl) ⟨20570039, by rfl⟩ : syracuseStep 27426719 = 41140079) B41140079
theorem B17124443 : Blo 1052612 17124443 := bstep (se 1 (by rfl) ⟨12843332, by rfl⟩ : syracuseStep 17124443 = 25686665) B25686665
theorem B73137917 : Blo 1052612 73137917 := bstep (se 3 (by rfl) ⟨13713359, by rfl⟩ : syracuseStep 73137917 = 27426719) B27426719
theorem B11416295 : Blo 1052612 11416295 := bstep (se 1 (by rfl) ⟨8562221, by rfl⟩ : syracuseStep 11416295 = 17124443) B17124443
theorem B48758611 : Blo 1052612 48758611 := bstep (se 1 (by rfl) ⟨36568958, by rfl⟩ : syracuseStep 48758611 = 73137917) B73137917
theorem B7610863 : Blo 1052612 7610863 := bstep (se 1 (by rfl) ⟨5708147, by rfl⟩ : syracuseStep 7610863 = 11416295) B11416295
theorem B65011481 : Blo 1052612 65011481 := bstep (se 2 (by rfl) ⟨24379305, by rfl⟩ : syracuseStep 65011481 = 48758611) B48758611
theorem B43340987 : Blo 1052612 43340987 := bstep (se 1 (by rfl) ⟨32505740, by rfl⟩ : syracuseStep 43340987 = 65011481) B65011481
theorem B10147817 : Blo 1052612 10147817 := bstep (se 2 (by rfl) ⟨3805431, by rfl⟩ : syracuseStep 10147817 = 7610863) B7610863
theorem B6765211 : Blo 1052612 6765211 := bstep (se 1 (by rfl) ⟨5073908, by rfl⟩ : syracuseStep 6765211 = 10147817) B10147817
theorem B28893991 : Blo 1052612 28893991 := bstep (se 1 (by rfl) ⟨21670493, by rfl⟩ : syracuseStep 28893991 = 43340987) B43340987
theorem B9020281 : Blo 1052612 9020281 := bstep (se 2 (by rfl) ⟨3382605, by rfl⟩ : syracuseStep 9020281 = 6765211) B6765211
theorem B38525321 : Blo 1052612 38525321 := bstep (se 2 (by rfl) ⟨14446995, by rfl⟩ : syracuseStep 38525321 = 28893991) B28893991
theorem B12027041 : Blo 1052612 12027041 := bstep (se 2 (by rfl) ⟨4510140, by rfl⟩ : syracuseStep 12027041 = 9020281) B9020281
theorem B102734189 : Blo 1052612 102734189 := bstep (se 3 (by rfl) ⟨19262660, by rfl⟩ : syracuseStep 102734189 = 38525321) B38525321
theorem B68489459 : Blo 1052612 68489459 := bstep (se 1 (by rfl) ⟨51367094, by rfl⟩ : syracuseStep 68489459 = 102734189) B102734189
theorem B8018027 : Blo 1052612 8018027 := bstep (se 1 (by rfl) ⟨6013520, by rfl⟩ : syracuseStep 8018027 = 12027041) B12027041
theorem B5345351 : Blo 1052612 5345351 := bstep (se 1 (by rfl) ⟨4009013, by rfl⟩ : syracuseStep 5345351 = 8018027) B8018027
theorem B45659639 : Blo 1052612 45659639 := bstep (se 1 (by rfl) ⟨34244729, by rfl⟩ : syracuseStep 45659639 = 68489459) B68489459
theorem B3563567 : Blo 1052612 3563567 := bstep (se 1 (by rfl) ⟨2672675, by rfl⟩ : syracuseStep 3563567 = 5345351) B5345351
theorem B30439759 : Blo 1052612 30439759 := bstep (se 1 (by rfl) ⟨22829819, by rfl⟩ : syracuseStep 30439759 = 45659639) B45659639
theorem B2375711 : Blo 1052612 2375711 := bstep (se 1 (by rfl) ⟨1781783, by rfl⟩ : syracuseStep 2375711 = 3563567) B3563567
theorem B40586345 : Blo 1052612 40586345 := bstep (se 2 (by rfl) ⟨15219879, by rfl⟩ : syracuseStep 40586345 = 30439759) B30439759
theorem B1583807 : Blo 1052612 1583807 := bstep (se 1 (by rfl) ⟨1187855, by rfl⟩ : syracuseStep 1583807 = 2375711) B2375711
theorem B27057563 : Blo 1052612 27057563 := bstep (se 1 (by rfl) ⟨20293172, by rfl⟩ : syracuseStep 27057563 = 40586345) B40586345
theorem B1055871 : Blo 1052612 1055871 := bstep (se 1 (by rfl) ⟨791903, by rfl⟩ : syracuseStep 1055871 = 1583807) B1583807
theorem B18038375 : Blo 1052612 18038375 := bstep (se 1 (by rfl) ⟨13528781, by rfl⟩ : syracuseStep 18038375 = 27057563) B27057563
theorem B12025583 : Blo 1052612 12025583 := bstep (se 1 (by rfl) ⟨9019187, by rfl⟩ : syracuseStep 12025583 = 18038375) B18038375
theorem B8017055 : Blo 1052612 8017055 := bstep (se 1 (by rfl) ⟨6012791, by rfl⟩ : syracuseStep 8017055 = 12025583) B12025583
theorem B5344703 : Blo 1052612 5344703 := bstep (se 1 (by rfl) ⟨4008527, by rfl⟩ : syracuseStep 5344703 = 8017055) B8017055
theorem B3563135 : Blo 1052612 3563135 := bstep (se 1 (by rfl) ⟨2672351, by rfl⟩ : syracuseStep 3563135 = 5344703) B5344703
theorem B2375423 : Blo 1052612 2375423 := bstep (se 1 (by rfl) ⟨1781567, by rfl⟩ : syracuseStep 2375423 = 3563135) B3563135
theorem B1583615 : Blo 1052612 1583615 := bstep (se 1 (by rfl) ⟨1187711, by rfl⟩ : syracuseStep 1583615 = 2375423) B2375423
theorem B1055743 : Blo 1052612 1055743 := bstep (se 1 (by rfl) ⟨791807, by rfl⟩ : syracuseStep 1055743 = 1583615) B1583615

theorem C0 (j : ℕ) (h1 : 263153 ≤ j) (h2 : j ≤ 263852) : Blo 1052612 (4 * j + 3) := by
  interval_cases j
  · exact B1052615
  · exact B1052619
  · exact B1052623
  · exact B1052627
  · exact B1052631
  · exact B1052635
  · exact B1052639
  · exact B1052643
  · exact B1052647
  · exact B1052651
  · exact B1052655
  · exact B1052659
  · exact B1052663
  · exact B1052667
  · exact B1052671
  · exact B1052675
  · exact B1052679
  · exact B1052683
  · exact B1052687
  · exact B1052691
  · exact B1052695
  · exact B1052699
  · exact B1052703
  · exact B1052707
  · exact B1052711
  · exact B1052715
  · exact B1052719
  · exact B1052723
  · exact B1052727
  · exact B1052731
  · exact B1052735
  · exact B1052739
  · exact B1052743
  · exact B1052747
  · exact B1052751
  · exact B1052755
  · exact B1052759
  · exact B1052763
  · exact B1052767
  · exact B1052771
  · exact B1052775
  · exact B1052779
  · exact B1052783
  · exact B1052787
  · exact B1052791
  · exact B1052795
  · exact B1052799
  · exact B1052803
  · exact B1052807
  · exact B1052811
  · exact B1052815
  · exact B1052819
  · exact B1052823
  · exact B1052827
  · exact B1052831
  · exact B1052835
  · exact B1052839
  · exact B1052843
  · exact B1052847
  · exact B1052851
  · exact B1052855
  · exact B1052859
  · exact B1052863
  · exact B1052867
  · exact B1052871
  · exact B1052875
  · exact B1052879
  · exact B1052883
  · exact B1052887
  · exact B1052891
  · exact B1052895
  · exact B1052899
  · exact B1052903
  · exact B1052907
  · exact B1052911
  · exact B1052915
  · exact B1052919
  · exact B1052923
  · exact B1052927
  · exact B1052931
  · exact B1052935
  · exact B1052939
  · exact B1052943
  · exact B1052947
  · exact B1052951
  · exact B1052955
  · exact B1052959
  · exact B1052963
  · exact B1052967
  · exact B1052971
  · exact B1052975
  · exact B1052979
  · exact B1052983
  · exact B1052987
  · exact B1052991
  · exact B1052995
  · exact B1052999
  · exact B1053003
  · exact B1053007
  · exact B1053011
  · exact B1053015
  · exact B1053019
  · exact B1053023
  · exact B1053027
  · exact B1053031
  · exact B1053035
  · exact B1053039
  · exact B1053043
  · exact B1053047
  · exact B1053051
  · exact B1053055
  · exact B1053059
  · exact B1053063
  · exact B1053067
  · exact B1053071
  · exact B1053075
  · exact B1053079
  · exact B1053083
  · exact B1053087
  · exact B1053091
  · exact B1053095
  · exact B1053099
  · exact B1053103
  · exact B1053107
  · exact B1053111
  · exact B1053115
  · exact B1053119
  · exact B1053123
  · exact B1053127
  · exact B1053131
  · exact B1053135
  · exact B1053139
  · exact B1053143
  · exact B1053147
  · exact B1053151
  · exact B1053155
  · exact B1053159
  · exact B1053163
  · exact B1053167
  · exact B1053171
  · exact B1053175
  · exact B1053179
  · exact B1053183
  · exact B1053187
  · exact B1053191
  · exact B1053195
  · exact B1053199
  · exact B1053203
  · exact B1053207
  · exact B1053211
  · exact B1053215
  · exact B1053219
  · exact B1053223
  · exact B1053227
  · exact B1053231
  · exact B1053235
  · exact B1053239
  · exact B1053243
  · exact B1053247
  · exact B1053251
  · exact B1053255
  · exact B1053259
  · exact B1053263
  · exact B1053267
  · exact B1053271
  · exact B1053275
  · exact B1053279
  · exact B1053283
  · exact B1053287
  · exact B1053291
  · exact B1053295
  · exact B1053299
  · exact B1053303
  · exact B1053307
  · exact B1053311
  · exact B1053315
  · exact B1053319
  · exact B1053323
  · exact B1053327
  · exact B1053331
  · exact B1053335
  · exact B1053339
  · exact B1053343
  · exact B1053347
  · exact B1053351
  · exact B1053355
  · exact B1053359
  · exact B1053363
  · exact B1053367
  · exact B1053371
  · exact B1053375
  · exact B1053379
  · exact B1053383
  · exact B1053387
  · exact B1053391
  · exact B1053395
  · exact B1053399
  · exact B1053403
  · exact B1053407
  · exact B1053411
  · exact B1053415
  · exact B1053419
  · exact B1053423
  · exact B1053427
  · exact B1053431
  · exact B1053435
  · exact B1053439
  · exact B1053443
  · exact B1053447
  · exact B1053451
  · exact B1053455
  · exact B1053459
  · exact B1053463
  · exact B1053467
  · exact B1053471
  · exact B1053475
  · exact B1053479
  · exact B1053483
  · exact B1053487
  · exact B1053491
  · exact B1053495
  · exact B1053499
  · exact B1053503
  · exact B1053507
  · exact B1053511
  · exact B1053515
  · exact B1053519
  · exact B1053523
  · exact B1053527
  · exact B1053531
  · exact B1053535
  · exact B1053539
  · exact B1053543
  · exact B1053547
  · exact B1053551
  · exact B1053555
  · exact B1053559
  · exact B1053563
  · exact B1053567
  · exact B1053571
  · exact B1053575
  · exact B1053579
  · exact B1053583
  · exact B1053587
  · exact B1053591
  · exact B1053595
  · exact B1053599
  · exact B1053603
  · exact B1053607
  · exact B1053611
  · exact B1053615
  · exact B1053619
  · exact B1053623
  · exact B1053627
  · exact B1053631
  · exact B1053635
  · exact B1053639
  · exact B1053643
  · exact B1053647
  · exact B1053651
  · exact B1053655
  · exact B1053659
  · exact B1053663
  · exact B1053667
  · exact B1053671
  · exact B1053675
  · exact B1053679
  · exact B1053683
  · exact B1053687
  · exact B1053691
  · exact B1053695
  · exact B1053699
  · exact B1053703
  · exact B1053707
  · exact B1053711
  · exact B1053715
  · exact B1053719
  · exact B1053723
  · exact B1053727
  · exact B1053731
  · exact B1053735
  · exact B1053739
  · exact B1053743
  · exact B1053747
  · exact B1053751
  · exact B1053755
  · exact B1053759
  · exact B1053763
  · exact B1053767
  · exact B1053771
  · exact B1053775
  · exact B1053779
  · exact B1053783
  · exact B1053787
  · exact B1053791
  · exact B1053795
  · exact B1053799
  · exact B1053803
  · exact B1053807
  · exact B1053811
  · exact B1053815
  · exact B1053819
  · exact B1053823
  · exact B1053827
  · exact B1053831
  · exact B1053835
  · exact B1053839
  · exact B1053843
  · exact B1053847
  · exact B1053851
  · exact B1053855
  · exact B1053859
  · exact B1053863
  · exact B1053867
  · exact B1053871
  · exact B1053875
  · exact B1053879
  · exact B1053883
  · exact B1053887
  · exact B1053891
  · exact B1053895
  · exact B1053899
  · exact B1053903
  · exact B1053907
  · exact B1053911
  · exact B1053915
  · exact B1053919
  · exact B1053923
  · exact B1053927
  · exact B1053931
  · exact B1053935
  · exact B1053939
  · exact B1053943
  · exact B1053947
  · exact B1053951
  · exact B1053955
  · exact B1053959
  · exact B1053963
  · exact B1053967
  · exact B1053971
  · exact B1053975
  · exact B1053979
  · exact B1053983
  · exact B1053987
  · exact B1053991
  · exact B1053995
  · exact B1053999
  · exact B1054003
  · exact B1054007
  · exact B1054011
  · exact B1054015
  · exact B1054019
  · exact B1054023
  · exact B1054027
  · exact B1054031
  · exact B1054035
  · exact B1054039
  · exact B1054043
  · exact B1054047
  · exact B1054051
  · exact B1054055
  · exact B1054059
  · exact B1054063
  · exact B1054067
  · exact B1054071
  · exact B1054075
  · exact B1054079
  · exact B1054083
  · exact B1054087
  · exact B1054091
  · exact B1054095
  · exact B1054099
  · exact B1054103
  · exact B1054107
  · exact B1054111
  · exact B1054115
  · exact B1054119
  · exact B1054123
  · exact B1054127
  · exact B1054131
  · exact B1054135
  · exact B1054139
  · exact B1054143
  · exact B1054147
  · exact B1054151
  · exact B1054155
  · exact B1054159
  · exact B1054163
  · exact B1054167
  · exact B1054171
  · exact B1054175
  · exact B1054179
  · exact B1054183
  · exact B1054187
  · exact B1054191
  · exact B1054195
  · exact B1054199
  · exact B1054203
  · exact B1054207
  · exact B1054211
  · exact B1054215
  · exact B1054219
  · exact B1054223
  · exact B1054227
  · exact B1054231
  · exact B1054235
  · exact B1054239
  · exact B1054243
  · exact B1054247
  · exact B1054251
  · exact B1054255
  · exact B1054259
  · exact B1054263
  · exact B1054267
  · exact B1054271
  · exact B1054275
  · exact B1054279
  · exact B1054283
  · exact B1054287
  · exact B1054291
  · exact B1054295
  · exact B1054299
  · exact B1054303
  · exact B1054307
  · exact B1054311
  · exact B1054315
  · exact B1054319
  · exact B1054323
  · exact B1054327
  · exact B1054331
  · exact B1054335
  · exact B1054339
  · exact B1054343
  · exact B1054347
  · exact B1054351
  · exact B1054355
  · exact B1054359
  · exact B1054363
  · exact B1054367
  · exact B1054371
  · exact B1054375
  · exact B1054379
  · exact B1054383
  · exact B1054387
  · exact B1054391
  · exact B1054395
  · exact B1054399
  · exact B1054403
  · exact B1054407
  · exact B1054411
  · exact B1054415
  · exact B1054419
  · exact B1054423
  · exact B1054427
  · exact B1054431
  · exact B1054435
  · exact B1054439
  · exact B1054443
  · exact B1054447
  · exact B1054451
  · exact B1054455
  · exact B1054459
  · exact B1054463
  · exact B1054467
  · exact B1054471
  · exact B1054475
  · exact B1054479
  · exact B1054483
  · exact B1054487
  · exact B1054491
  · exact B1054495
  · exact B1054499
  · exact B1054503
  · exact B1054507
  · exact B1054511
  · exact B1054515
  · exact B1054519
  · exact B1054523
  · exact B1054527
  · exact B1054531
  · exact B1054535
  · exact B1054539
  · exact B1054543
  · exact B1054547
  · exact B1054551
  · exact B1054555
  · exact B1054559
  · exact B1054563
  · exact B1054567
  · exact B1054571
  · exact B1054575
  · exact B1054579
  · exact B1054583
  · exact B1054587
  · exact B1054591
  · exact B1054595
  · exact B1054599
  · exact B1054603
  · exact B1054607
  · exact B1054611
  · exact B1054615
  · exact B1054619
  · exact B1054623
  · exact B1054627
  · exact B1054631
  · exact B1054635
  · exact B1054639
  · exact B1054643
  · exact B1054647
  · exact B1054651
  · exact B1054655
  · exact B1054659
  · exact B1054663
  · exact B1054667
  · exact B1054671
  · exact B1054675
  · exact B1054679
  · exact B1054683
  · exact B1054687
  · exact B1054691
  · exact B1054695
  · exact B1054699
  · exact B1054703
  · exact B1054707
  · exact B1054711
  · exact B1054715
  · exact B1054719
  · exact B1054723
  · exact B1054727
  · exact B1054731
  · exact B1054735
  · exact B1054739
  · exact B1054743
  · exact B1054747
  · exact B1054751
  · exact B1054755
  · exact B1054759
  · exact B1054763
  · exact B1054767
  · exact B1054771
  · exact B1054775
  · exact B1054779
  · exact B1054783
  · exact B1054787
  · exact B1054791
  · exact B1054795
  · exact B1054799
  · exact B1054803
  · exact B1054807
  · exact B1054811
  · exact B1054815
  · exact B1054819
  · exact B1054823
  · exact B1054827
  · exact B1054831
  · exact B1054835
  · exact B1054839
  · exact B1054843
  · exact B1054847
  · exact B1054851
  · exact B1054855
  · exact B1054859
  · exact B1054863
  · exact B1054867
  · exact B1054871
  · exact B1054875
  · exact B1054879
  · exact B1054883
  · exact B1054887
  · exact B1054891
  · exact B1054895
  · exact B1054899
  · exact B1054903
  · exact B1054907
  · exact B1054911
  · exact B1054915
  · exact B1054919
  · exact B1054923
  · exact B1054927
  · exact B1054931
  · exact B1054935
  · exact B1054939
  · exact B1054943
  · exact B1054947
  · exact B1054951
  · exact B1054955
  · exact B1054959
  · exact B1054963
  · exact B1054967
  · exact B1054971
  · exact B1054975
  · exact B1054979
  · exact B1054983
  · exact B1054987
  · exact B1054991
  · exact B1054995
  · exact B1054999
  · exact B1055003
  · exact B1055007
  · exact B1055011
  · exact B1055015
  · exact B1055019
  · exact B1055023
  · exact B1055027
  · exact B1055031
  · exact B1055035
  · exact B1055039
  · exact B1055043
  · exact B1055047
  · exact B1055051
  · exact B1055055
  · exact B1055059
  · exact B1055063
  · exact B1055067
  · exact B1055071
  · exact B1055075
  · exact B1055079
  · exact B1055083
  · exact B1055087
  · exact B1055091
  · exact B1055095
  · exact B1055099
  · exact B1055103
  · exact B1055107
  · exact B1055111
  · exact B1055115
  · exact B1055119
  · exact B1055123
  · exact B1055127
  · exact B1055131
  · exact B1055135
  · exact B1055139
  · exact B1055143
  · exact B1055147
  · exact B1055151
  · exact B1055155
  · exact B1055159
  · exact B1055163
  · exact B1055167
  · exact B1055171
  · exact B1055175
  · exact B1055179
  · exact B1055183
  · exact B1055187
  · exact B1055191
  · exact B1055195
  · exact B1055199
  · exact B1055203
  · exact B1055207
  · exact B1055211
  · exact B1055215
  · exact B1055219
  · exact B1055223
  · exact B1055227
  · exact B1055231
  · exact B1055235
  · exact B1055239
  · exact B1055243
  · exact B1055247
  · exact B1055251
  · exact B1055255
  · exact B1055259
  · exact B1055263
  · exact B1055267
  · exact B1055271
  · exact B1055275
  · exact B1055279
  · exact B1055283
  · exact B1055287
  · exact B1055291
  · exact B1055295
  · exact B1055299
  · exact B1055303
  · exact B1055307
  · exact B1055311
  · exact B1055315
  · exact B1055319
  · exact B1055323
  · exact B1055327
  · exact B1055331
  · exact B1055335
  · exact B1055339
  · exact B1055343
  · exact B1055347
  · exact B1055351
  · exact B1055355
  · exact B1055359
  · exact B1055363
  · exact B1055367
  · exact B1055371
  · exact B1055375
  · exact B1055379
  · exact B1055383
  · exact B1055387
  · exact B1055391
  · exact B1055395
  · exact B1055399
  · exact B1055403
  · exact B1055407
  · exact B1055411

theorem C1 (j : ℕ) (h1 : 263853 ≤ j) (h2 : j ≤ 264152) : Blo 1052612 (4 * j + 3) := by
  interval_cases j
  · exact B1055415
  · exact B1055419
  · exact B1055423
  · exact B1055427
  · exact B1055431
  · exact B1055435
  · exact B1055439
  · exact B1055443
  · exact B1055447
  · exact B1055451
  · exact B1055455
  · exact B1055459
  · exact B1055463
  · exact B1055467
  · exact B1055471
  · exact B1055475
  · exact B1055479
  · exact B1055483
  · exact B1055487
  · exact B1055491
  · exact B1055495
  · exact B1055499
  · exact B1055503
  · exact B1055507
  · exact B1055511
  · exact B1055515
  · exact B1055519
  · exact B1055523
  · exact B1055527
  · exact B1055531
  · exact B1055535
  · exact B1055539
  · exact B1055543
  · exact B1055547
  · exact B1055551
  · exact B1055555
  · exact B1055559
  · exact B1055563
  · exact B1055567
  · exact B1055571
  · exact B1055575
  · exact B1055579
  · exact B1055583
  · exact B1055587
  · exact B1055591
  · exact B1055595
  · exact B1055599
  · exact B1055603
  · exact B1055607
  · exact B1055611
  · exact B1055615
  · exact B1055619
  · exact B1055623
  · exact B1055627
  · exact B1055631
  · exact B1055635
  · exact B1055639
  · exact B1055643
  · exact B1055647
  · exact B1055651
  · exact B1055655
  · exact B1055659
  · exact B1055663
  · exact B1055667
  · exact B1055671
  · exact B1055675
  · exact B1055679
  · exact B1055683
  · exact B1055687
  · exact B1055691
  · exact B1055695
  · exact B1055699
  · exact B1055703
  · exact B1055707
  · exact B1055711
  · exact B1055715
  · exact B1055719
  · exact B1055723
  · exact B1055727
  · exact B1055731
  · exact B1055735
  · exact B1055739
  · exact B1055743
  · exact B1055747
  · exact B1055751
  · exact B1055755
  · exact B1055759
  · exact B1055763
  · exact B1055767
  · exact B1055771
  · exact B1055775
  · exact B1055779
  · exact B1055783
  · exact B1055787
  · exact B1055791
  · exact B1055795
  · exact B1055799
  · exact B1055803
  · exact B1055807
  · exact B1055811
  · exact B1055815
  · exact B1055819
  · exact B1055823
  · exact B1055827
  · exact B1055831
  · exact B1055835
  · exact B1055839
  · exact B1055843
  · exact B1055847
  · exact B1055851
  · exact B1055855
  · exact B1055859
  · exact B1055863
  · exact B1055867
  · exact B1055871
  · exact B1055875
  · exact B1055879
  · exact B1055883
  · exact B1055887
  · exact B1055891
  · exact B1055895
  · exact B1055899
  · exact B1055903
  · exact B1055907
  · exact B1055911
  · exact B1055915
  · exact B1055919
  · exact B1055923
  · exact B1055927
  · exact B1055931
  · exact B1055935
  · exact B1055939
  · exact B1055943
  · exact B1055947
  · exact B1055951
  · exact B1055955
  · exact B1055959
  · exact B1055963
  · exact B1055967
  · exact B1055971
  · exact B1055975
  · exact B1055979
  · exact B1055983
  · exact B1055987
  · exact B1055991
  · exact B1055995
  · exact B1055999
  · exact B1056003
  · exact B1056007
  · exact B1056011
  · exact B1056015
  · exact B1056019
  · exact B1056023
  · exact B1056027
  · exact B1056031
  · exact B1056035
  · exact B1056039
  · exact B1056043
  · exact B1056047
  · exact B1056051
  · exact B1056055
  · exact B1056059
  · exact B1056063
  · exact B1056067
  · exact B1056071
  · exact B1056075
  · exact B1056079
  · exact B1056083
  · exact B1056087
  · exact B1056091
  · exact B1056095
  · exact B1056099
  · exact B1056103
  · exact B1056107
  · exact B1056111
  · exact B1056115
  · exact B1056119
  · exact B1056123
  · exact B1056127
  · exact B1056131
  · exact B1056135
  · exact B1056139
  · exact B1056143
  · exact B1056147
  · exact B1056151
  · exact B1056155
  · exact B1056159
  · exact B1056163
  · exact B1056167
  · exact B1056171
  · exact B1056175
  · exact B1056179
  · exact B1056183
  · exact B1056187
  · exact B1056191
  · exact B1056195
  · exact B1056199
  · exact B1056203
  · exact B1056207
  · exact B1056211
  · exact B1056215
  · exact B1056219
  · exact B1056223
  · exact B1056227
  · exact B1056231
  · exact B1056235
  · exact B1056239
  · exact B1056243
  · exact B1056247
  · exact B1056251
  · exact B1056255
  · exact B1056259
  · exact B1056263
  · exact B1056267
  · exact B1056271
  · exact B1056275
  · exact B1056279
  · exact B1056283
  · exact B1056287
  · exact B1056291
  · exact B1056295
  · exact B1056299
  · exact B1056303
  · exact B1056307
  · exact B1056311
  · exact B1056315
  · exact B1056319
  · exact B1056323
  · exact B1056327
  · exact B1056331
  · exact B1056335
  · exact B1056339
  · exact B1056343
  · exact B1056347
  · exact B1056351
  · exact B1056355
  · exact B1056359
  · exact B1056363
  · exact B1056367
  · exact B1056371
  · exact B1056375
  · exact B1056379
  · exact B1056383
  · exact B1056387
  · exact B1056391
  · exact B1056395
  · exact B1056399
  · exact B1056403
  · exact B1056407
  · exact B1056411
  · exact B1056415
  · exact B1056419
  · exact B1056423
  · exact B1056427
  · exact B1056431
  · exact B1056435
  · exact B1056439
  · exact B1056443
  · exact B1056447
  · exact B1056451
  · exact B1056455
  · exact B1056459
  · exact B1056463
  · exact B1056467
  · exact B1056471
  · exact B1056475
  · exact B1056479
  · exact B1056483
  · exact B1056487
  · exact B1056491
  · exact B1056495
  · exact B1056499
  · exact B1056503
  · exact B1056507
  · exact B1056511
  · exact B1056515
  · exact B1056519
  · exact B1056523
  · exact B1056527
  · exact B1056531
  · exact B1056535
  · exact B1056539
  · exact B1056543
  · exact B1056547
  · exact B1056551
  · exact B1056555
  · exact B1056559
  · exact B1056563
  · exact B1056567
  · exact B1056571
  · exact B1056575
  · exact B1056579
  · exact B1056583
  · exact B1056587
  · exact B1056591
  · exact B1056595
  · exact B1056599
  · exact B1056603
  · exact B1056607
  · exact B1056611

theorem solution (m : ℕ) (hlo : 1052612 ≤ m) (hhi : m ≤ 1056612) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 263153 ≤ j := by omega
    have hj2 : j ≤ 264152 := by omega
    have hb : Blo 1052612 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 263853 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
