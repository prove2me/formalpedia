-- Prove2me | solution 1 for syracuse_descends_range_1116628_1120628
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:41.232174+00:00
-- url     : https://prove2.me/submissions/9b9f3ad6-2d24-4856-876a-85e2b5ed6df9

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


theorem B2392229 : Blo 1116628 2392229 := bbase (se 4 (by rfl) ⟨224271, by rfl⟩ : syracuseStep 2392229 = 448543) (by norm_num)
theorem B2687269 : Blo 1116628 2687269 := bbase (se 4 (by rfl) ⟨251931, by rfl⟩ : syracuseStep 2687269 = 503863) (by norm_num)
theorem B2392373 : Blo 1116628 2392373 := bbase (se 5 (by rfl) ⟨112142, by rfl⟩ : syracuseStep 2392373 = 224285) (by norm_num)
theorem B5669189 : Blo 1116628 5669189 := bbase (se 4 (by rfl) ⟨531486, by rfl⟩ : syracuseStep 5669189 = 1062973) (by norm_num)
theorem B10191253 : Blo 1116628 10191253 := bbase (se 6 (by rfl) ⟨238857, by rfl⟩ : syracuseStep 10191253 = 477715) (by norm_num)
theorem B2687413 : Blo 1116628 2687413 := bbase (se 5 (by rfl) ⟨125972, by rfl⟩ : syracuseStep 2687413 = 251945) (by norm_num)
theorem B3768821 : Blo 1116628 3768821 := bbase (se 5 (by rfl) ⟨176663, by rfl⟩ : syracuseStep 3768821 = 353327) (by norm_num)
theorem B5374613 : Blo 1116628 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B2392733 : Blo 1116628 2392733 := bbase (se 3 (by rfl) ⟨448637, by rfl⟩ : syracuseStep 2392733 = 897275) (by norm_num)
theorem B7275253 : Blo 1116628 7275253 := bbase (se 5 (by rfl) ⟨341027, by rfl⟩ : syracuseStep 7275253 = 682055) (by norm_num)
theorem B3769253 : Blo 1116628 3769253 := bbase (se 4 (by rfl) ⟨353367, by rfl⟩ : syracuseStep 3769253 = 706735) (by norm_num)
theorem B1147861 : Blo 1116628 1147861 := bbase (se 7 (by rfl) ⟨13451, by rfl⟩ : syracuseStep 1147861 = 26903) (by norm_num)
theorem B2688029 : Blo 1116628 2688029 := bbase (se 3 (by rfl) ⟨504005, by rfl⟩ : syracuseStep 2688029 = 1008011) (by norm_num)
theorem B1344557 : Blo 1116628 1344557 := bbase (se 3 (by rfl) ⟨252104, by rfl⟩ : syracuseStep 1344557 = 504209) (by norm_num)
theorem B8487989 : Blo 1116628 8487989 := bbase (se 5 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 8487989 = 795749) (by norm_num)
theorem B3769685 : Blo 1116628 3769685 := bbase (se 12 (by rfl) ⟨1380, by rfl⟩ : syracuseStep 3769685 = 2761) (by norm_num)
theorem B1344865 : Blo 1116628 1344865 := bbase (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) (by norm_num)
theorem B2688365 : Blo 1116628 2688365 := bbase (se 3 (by rfl) ⟨504068, by rfl⟩ : syracuseStep 2688365 = 1008137) (by norm_num)
theorem B1344961 : Blo 1116628 1344961 := bbase (se 2 (by rfl) ⟨504360, by rfl⟩ : syracuseStep 1344961 = 1008721) (by norm_num)
theorem B2688461 : Blo 1116628 2688461 := bbase (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) (by norm_num)
theorem B3179989 : Blo 1116628 3179989 := bbase (se 7 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 3179989 = 74531) (by norm_num)
theorem B5670485 : Blo 1116628 5670485 := bbase (se 8 (by rfl) ⟨33225, by rfl⟩ : syracuseStep 5670485 = 66451) (by norm_num)
theorem B2688653 : Blo 1116628 2688653 := bbase (se 3 (by rfl) ⟨504122, by rfl⟩ : syracuseStep 2688653 = 1008245) (by norm_num)
theorem B1345249 : Blo 1116628 1345249 := bbase (se 2 (by rfl) ⟨504468, by rfl⟩ : syracuseStep 1345249 = 1008937) (by norm_num)
theorem B3770117 : Blo 1116628 3770117 := bbase (se 4 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 3770117 = 706897) (by norm_num)
theorem B7767893 : Blo 1116628 7767893 := bbase (se 9 (by rfl) ⟨22757, by rfl⟩ : syracuseStep 7767893 = 45515) (by norm_num)
theorem B1345441 : Blo 1116628 1345441 := bbase (se 2 (by rfl) ⟨504540, by rfl⟩ : syracuseStep 1345441 = 1009081) (by norm_num)
theorem B1574845 : Blo 1116628 1574845 := bbase (se 3 (by rfl) ⟨295283, by rfl⟩ : syracuseStep 1574845 = 590567) (by norm_num)
theorem B4032517 : Blo 1116628 4032517 := bbase (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) (by norm_num)
theorem B3770549 : Blo 1116628 3770549 := bbase (se 5 (by rfl) ⟨176744, by rfl⟩ : syracuseStep 3770549 = 353489) (by norm_num)
theorem B8063189 : Blo 1116628 8063189 := bbase (se 7 (by rfl) ⟨94490, by rfl⟩ : syracuseStep 8063189 = 188981) (by norm_num)
theorem B7178453 : Blo 1116628 7178453 := bbase (se 7 (by rfl) ⟨84122, by rfl⟩ : syracuseStep 7178453 = 168245) (by norm_num)
theorem B4032965 : Blo 1116628 4032965 := bbase (se 4 (by rfl) ⟨378090, by rfl⟩ : syracuseStep 4032965 = 756181) (by norm_num)
theorem B3770981 : Blo 1116628 3770981 := bbase (se 4 (by rfl) ⟨353529, by rfl⟩ : syracuseStep 3770981 = 707059) (by norm_num)
theorem B2689805 : Blo 1116628 2689805 := bbase (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) (by norm_num)
theorem B5671781 : Blo 1116628 5671781 := bbase (se 4 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 5671781 = 1063459) (by norm_num)
theorem B6359957 : Blo 1116628 6359957 := bbase (se 6 (by rfl) ⟨149061, by rfl⟩ : syracuseStep 6359957 = 298123) (by norm_num)
theorem B3181493 : Blo 1116628 3181493 := bbase (se 5 (by rfl) ⟨149132, by rfl⟩ : syracuseStep 3181493 = 298265) (by norm_num)
theorem B3771413 : Blo 1116628 3771413 := bbase (se 6 (by rfl) ⟨88392, by rfl⟩ : syracuseStep 3771413 = 176785) (by norm_num)
theorem B4361285 : Blo 1116628 4361285 := bbase (se 4 (by rfl) ⟨408870, by rfl⟩ : syracuseStep 4361285 = 817741) (by norm_num)
theorem B3771845 : Blo 1116628 3771845 := bbase (se 4 (by rfl) ⟨353610, by rfl⟩ : syracuseStep 3771845 = 707221) (by norm_num)
theorem B1150409 : Blo 1116628 1150409 := bbase (se 2 (by rfl) ⟨431403, by rfl⟩ : syracuseStep 1150409 = 862807) (by norm_num)
theorem B6131285 : Blo 1116628 6131285 := bbase (se 8 (by rfl) ⟨35925, by rfl⟩ : syracuseStep 6131285 = 71851) (by norm_num)
theorem B9178805 : Blo 1116628 9178805 := bbase (se 5 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 9178805 = 860513) (by norm_num)
theorem B1674965 : Blo 1116628 1674965 := bbase (se 7 (by rfl) ⟨19628, by rfl⟩ : syracuseStep 1674965 = 39257) (by norm_num)
theorem B5377765 : Blo 1116628 5377765 := bbase (se 4 (by rfl) ⟨504165, by rfl⟩ : syracuseStep 5377765 = 1008331) (by norm_num)
theorem B1674989 : Blo 1116628 1674989 := bbase (se 3 (by rfl) ⟨314060, by rfl⟩ : syracuseStep 1674989 = 628121) (by norm_num)
theorem B1675013 : Blo 1116628 1675013 := bbase (se 4 (by rfl) ⟨157032, by rfl⟩ : syracuseStep 1675013 = 314065) (by norm_num)
theorem B1675037 : Blo 1116628 1675037 := bbase (se 3 (by rfl) ⟨314069, by rfl⟩ : syracuseStep 1675037 = 628139) (by norm_num)
theorem B1675061 : Blo 1116628 1675061 := bbase (se 5 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 1675061 = 157037) (by norm_num)
theorem B1675085 : Blo 1116628 1675085 := bbase (se 3 (by rfl) ⟨314078, by rfl⟩ : syracuseStep 1675085 = 628157) (by norm_num)
theorem B1675109 : Blo 1116628 1675109 := bbase (se 4 (by rfl) ⟨157041, by rfl⟩ : syracuseStep 1675109 = 314083) (by norm_num)
theorem B3772277 : Blo 1116628 3772277 := bbase (se 5 (by rfl) ⟨176825, by rfl⟩ : syracuseStep 3772277 = 353651) (by norm_num)
theorem B1675133 : Blo 1116628 1675133 := bbase (se 3 (by rfl) ⟨314087, by rfl⟩ : syracuseStep 1675133 = 628175) (by norm_num)
theorem B1675157 : Blo 1116628 1675157 := bbase (se 6 (by rfl) ⟨39261, by rfl⟩ : syracuseStep 1675157 = 78523) (by norm_num)
theorem B1675181 : Blo 1116628 1675181 := bbase (se 3 (by rfl) ⟨314096, by rfl⟩ : syracuseStep 1675181 = 628193) (by norm_num)
theorem B1675205 : Blo 1116628 1675205 := bbase (se 4 (by rfl) ⟨157050, by rfl⟩ : syracuseStep 1675205 = 314101) (by norm_num)
theorem B1675229 : Blo 1116628 1675229 := bbase (se 3 (by rfl) ⟨314105, by rfl⟩ : syracuseStep 1675229 = 628211) (by norm_num)
theorem B1675253 : Blo 1116628 1675253 := bbase (se 5 (by rfl) ⟨78527, by rfl⟩ : syracuseStep 1675253 = 157055) (by norm_num)
theorem B1675277 : Blo 1116628 1675277 := bbase (se 3 (by rfl) ⟨314114, by rfl⟩ : syracuseStep 1675277 = 628229) (by norm_num)
theorem B1675301 : Blo 1116628 1675301 := bbase (se 4 (by rfl) ⟨157059, by rfl⟩ : syracuseStep 1675301 = 314119) (by norm_num)
theorem B1675325 : Blo 1116628 1675325 := bbase (se 3 (by rfl) ⟨314123, by rfl⟩ : syracuseStep 1675325 = 628247) (by norm_num)
theorem B1675349 : Blo 1116628 1675349 := bbase (se 8 (by rfl) ⟨9816, by rfl⟩ : syracuseStep 1675349 = 19633) (by norm_num)
theorem B1675373 : Blo 1116628 1675373 := bbase (se 3 (by rfl) ⟨314132, by rfl⟩ : syracuseStep 1675373 = 628265) (by norm_num)
theorem B5673077 : Blo 1116628 5673077 := bbase (se 5 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 5673077 = 531851) (by norm_num)
theorem B1675397 : Blo 1116628 1675397 := bbase (se 4 (by rfl) ⟨157068, by rfl⟩ : syracuseStep 1675397 = 314137) (by norm_num)
theorem B1675421 : Blo 1116628 1675421 := bbase (se 3 (by rfl) ⟨314141, by rfl⟩ : syracuseStep 1675421 = 628283) (by norm_num)
theorem B1675445 : Blo 1116628 1675445 := bbase (se 5 (by rfl) ⟨78536, by rfl⟩ : syracuseStep 1675445 = 157073) (by norm_num)
theorem B1675469 : Blo 1116628 1675469 := bbase (se 3 (by rfl) ⟨314150, by rfl⟩ : syracuseStep 1675469 = 628301) (by norm_num)
theorem B22974677 : Blo 1116628 22974677 := bbase (se 7 (by rfl) ⟨269234, by rfl⟩ : syracuseStep 22974677 = 538469) (by norm_num)
theorem B1675493 : Blo 1116628 1675493 := bbase (se 4 (by rfl) ⟨157077, by rfl⟩ : syracuseStep 1675493 = 314155) (by norm_num)
theorem B1675517 : Blo 1116628 1675517 := bbase (se 3 (by rfl) ⟨314159, by rfl⟩ : syracuseStep 1675517 = 628319) (by norm_num)
theorem B1413389 : Blo 1116628 1413389 := bbase (se 3 (by rfl) ⟨265010, by rfl⟩ : syracuseStep 1413389 = 530021) (by norm_num)
theorem B1675541 : Blo 1116628 1675541 := bbase (se 6 (by rfl) ⟨39270, by rfl⟩ : syracuseStep 1675541 = 78541) (by norm_num)
theorem B2265365 : Blo 1116628 2265365 := bbase (se 6 (by rfl) ⟨53094, by rfl⟩ : syracuseStep 2265365 = 106189) (by norm_num)
theorem B3772709 : Blo 1116628 3772709 := bbase (se 4 (by rfl) ⟨353691, by rfl⟩ : syracuseStep 3772709 = 707383) (by norm_num)
theorem B1675565 : Blo 1116628 1675565 := bbase (se 3 (by rfl) ⟨314168, by rfl⟩ : syracuseStep 1675565 = 628337) (by norm_num)
theorem B1413445 : Blo 1116628 1413445 := bbase (se 4 (by rfl) ⟨132510, by rfl⟩ : syracuseStep 1413445 = 265021) (by norm_num)
theorem B1675589 : Blo 1116628 1675589 := bbase (se 4 (by rfl) ⟨157086, by rfl⟩ : syracuseStep 1675589 = 314173) (by norm_num)
theorem B1675613 : Blo 1116628 1675613 := bbase (se 3 (by rfl) ⟨314177, by rfl⟩ : syracuseStep 1675613 = 628355) (by norm_num)
theorem B1675637 : Blo 1116628 1675637 := bbase (se 5 (by rfl) ⟨78545, by rfl⟩ : syracuseStep 1675637 = 157091) (by norm_num)
theorem B1675661 : Blo 1116628 1675661 := bbase (se 3 (by rfl) ⟨314186, by rfl⟩ : syracuseStep 1675661 = 628373) (by norm_num)
theorem B1413541 : Blo 1116628 1413541 := bbase (se 4 (by rfl) ⟨132519, by rfl⟩ : syracuseStep 1413541 = 265039) (by norm_num)
theorem B1675685 : Blo 1116628 1675685 := bbase (se 4 (by rfl) ⟨157095, by rfl⟩ : syracuseStep 1675685 = 314191) (by norm_num)
theorem B1675709 : Blo 1116628 1675709 := bbase (se 3 (by rfl) ⟨314195, by rfl⟩ : syracuseStep 1675709 = 628391) (by norm_num)
theorem B1675733 : Blo 1116628 1675733 := bbase (se 7 (by rfl) ⟨19637, by rfl⟩ : syracuseStep 1675733 = 39275) (by norm_num)
theorem B3183077 : Blo 1116628 3183077 := bbase (se 4 (by rfl) ⟨298413, by rfl⟩ : syracuseStep 3183077 = 596827) (by norm_num)
theorem B1675757 : Blo 1116628 1675757 := bbase (se 3 (by rfl) ⟨314204, by rfl⟩ : syracuseStep 1675757 = 628409) (by norm_num)
theorem B1675781 : Blo 1116628 1675781 := bbase (se 4 (by rfl) ⟨157104, by rfl⟩ : syracuseStep 1675781 = 314209) (by norm_num)
theorem B3019285 : Blo 1116628 3019285 := bbase (se 6 (by rfl) ⟨70764, by rfl⟩ : syracuseStep 3019285 = 141529) (by norm_num)
theorem B1675805 : Blo 1116628 1675805 := bbase (se 3 (by rfl) ⟨314213, by rfl⟩ : syracuseStep 1675805 = 628427) (by norm_num)
theorem B1675829 : Blo 1116628 1675829 := bbase (se 5 (by rfl) ⟨78554, by rfl⟩ : syracuseStep 1675829 = 157109) (by norm_num)
theorem B1675853 : Blo 1116628 1675853 := bbase (se 3 (by rfl) ⟨314222, by rfl⟩ : syracuseStep 1675853 = 628445) (by norm_num)
theorem B1413713 : Blo 1116628 1413713 := bbase (se 2 (by rfl) ⟨530142, by rfl⟩ : syracuseStep 1413713 = 1060285) (by norm_num)
theorem B1675877 : Blo 1116628 1675877 := bbase (se 4 (by rfl) ⟨157113, by rfl⟩ : syracuseStep 1675877 = 314227) (by norm_num)
theorem B1675901 : Blo 1116628 1675901 := bbase (se 3 (by rfl) ⟨314231, by rfl⟩ : syracuseStep 1675901 = 628463) (by norm_num)
theorem B1413769 : Blo 1116628 1413769 := bbase (se 2 (by rfl) ⟨530163, by rfl⟩ : syracuseStep 1413769 = 1060327) (by norm_num)
theorem B1675925 : Blo 1116628 1675925 := bbase (se 6 (by rfl) ⟨39279, by rfl⟩ : syracuseStep 1675925 = 78559) (by norm_num)
theorem B1675949 : Blo 1116628 1675949 := bbase (se 3 (by rfl) ⟨314240, by rfl⟩ : syracuseStep 1675949 = 628481) (by norm_num)
theorem B8622773 : Blo 1116628 8622773 := bbase (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) (by norm_num)
theorem B1675973 : Blo 1116628 1675973 := bbase (se 4 (by rfl) ⟨157122, by rfl⟩ : syracuseStep 1675973 = 314245) (by norm_num)
theorem B3773141 : Blo 1116628 3773141 := bbase (se 7 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 3773141 = 88433) (by norm_num)
theorem B1675997 : Blo 1116628 1675997 := bbase (se 3 (by rfl) ⟨314249, by rfl⟩ : syracuseStep 1675997 = 628499) (by norm_num)
theorem B2691805 : Blo 1116628 2691805 := bbase (se 3 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 2691805 = 1009427) (by norm_num)
theorem B1413865 : Blo 1116628 1413865 := bbase (se 2 (by rfl) ⟨530199, by rfl⟩ : syracuseStep 1413865 = 1060399) (by norm_num)
theorem B1676021 : Blo 1116628 1676021 := bbase (se 5 (by rfl) ⟨78563, by rfl⟩ : syracuseStep 1676021 = 157127) (by norm_num)
theorem B1676045 : Blo 1116628 1676045 := bbase (se 3 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 1676045 = 628517) (by norm_num)
theorem B1676069 : Blo 1116628 1676069 := bbase (se 4 (by rfl) ⟨157131, by rfl⟩ : syracuseStep 1676069 = 314263) (by norm_num)
theorem B1676093 : Blo 1116628 1676093 := bbase (se 3 (by rfl) ⟨314267, by rfl⟩ : syracuseStep 1676093 = 628535) (by norm_num)
theorem B2691901 : Blo 1116628 2691901 := bbase (se 3 (by rfl) ⟨504731, by rfl⟩ : syracuseStep 2691901 = 1009463) (by norm_num)
theorem B1676117 : Blo 1116628 1676117 := bbase (se 9 (by rfl) ⟨4910, by rfl⟩ : syracuseStep 1676117 = 9821) (by norm_num)
theorem B1676141 : Blo 1116628 1676141 := bbase (se 3 (by rfl) ⟨314276, by rfl⟩ : syracuseStep 1676141 = 628553) (by norm_num)
theorem B1676165 : Blo 1116628 1676165 := bbase (se 4 (by rfl) ⟨157140, by rfl⟩ : syracuseStep 1676165 = 314281) (by norm_num)
theorem B1414037 : Blo 1116628 1414037 := bbase (se 6 (by rfl) ⟨33141, by rfl⟩ : syracuseStep 1414037 = 66283) (by norm_num)
theorem B1676189 : Blo 1116628 1676189 := bbase (se 3 (by rfl) ⟨314285, by rfl⟩ : syracuseStep 1676189 = 628571) (by norm_num)
theorem B1676213 : Blo 1116628 1676213 := bbase (se 5 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 1676213 = 157145) (by norm_num)
theorem B1414093 : Blo 1116628 1414093 := bbase (se 3 (by rfl) ⟨265142, by rfl⟩ : syracuseStep 1414093 = 530285) (by norm_num)
theorem B1676237 : Blo 1116628 1676237 := bbase (se 3 (by rfl) ⟨314294, by rfl⟩ : syracuseStep 1676237 = 628589) (by norm_num)
theorem B1676261 : Blo 1116628 1676261 := bbase (se 4 (by rfl) ⟨157149, by rfl⟩ : syracuseStep 1676261 = 314299) (by norm_num)
theorem B1676285 : Blo 1116628 1676285 := bbase (se 3 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 1676285 = 628607) (by norm_num)
theorem B1676309 : Blo 1116628 1676309 := bbase (se 6 (by rfl) ⟨39288, by rfl⟩ : syracuseStep 1676309 = 78577) (by norm_num)
theorem B1414189 : Blo 1116628 1414189 := bbase (se 3 (by rfl) ⟨265160, by rfl⟩ : syracuseStep 1414189 = 530321) (by norm_num)
theorem B1676333 : Blo 1116628 1676333 := bbase (se 3 (by rfl) ⟨314312, by rfl⟩ : syracuseStep 1676333 = 628625) (by norm_num)
theorem B6362165 : Blo 1116628 6362165 := bbase (se 5 (by rfl) ⟨298226, by rfl⟩ : syracuseStep 6362165 = 596453) (by norm_num)
theorem B1676357 : Blo 1116628 1676357 := bbase (se 4 (by rfl) ⟨157158, by rfl⟩ : syracuseStep 1676357 = 314317) (by norm_num)
theorem B1676381 : Blo 1116628 1676381 := bbase (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) (by norm_num)
theorem B1676405 : Blo 1116628 1676405 := bbase (se 5 (by rfl) ⟨78581, by rfl⟩ : syracuseStep 1676405 = 157163) (by norm_num)
theorem B3183749 : Blo 1116628 3183749 := bbase (se 4 (by rfl) ⟨298476, by rfl⟩ : syracuseStep 3183749 = 596953) (by norm_num)
theorem B3773573 : Blo 1116628 3773573 := bbase (se 4 (by rfl) ⟨353772, by rfl⟩ : syracuseStep 3773573 = 707545) (by norm_num)
theorem B1676429 : Blo 1116628 1676429 := bbase (se 3 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 1676429 = 628661) (by norm_num)
theorem B1676453 : Blo 1116628 1676453 := bbase (se 4 (by rfl) ⟨157167, by rfl⟩ : syracuseStep 1676453 = 314335) (by norm_num)
theorem B1676477 : Blo 1116628 1676477 := bbase (se 3 (by rfl) ⟨314339, by rfl⟩ : syracuseStep 1676477 = 628679) (by norm_num)
theorem B1676501 : Blo 1116628 1676501 := bbase (se 7 (by rfl) ⟨19646, by rfl⟩ : syracuseStep 1676501 = 39293) (by norm_num)
theorem B1414361 : Blo 1116628 1414361 := bbase (se 2 (by rfl) ⟨530385, by rfl⟩ : syracuseStep 1414361 = 1060771) (by norm_num)
theorem B1676525 : Blo 1116628 1676525 := bbase (se 3 (by rfl) ⟨314348, by rfl⟩ : syracuseStep 1676525 = 628697) (by norm_num)
theorem B1676549 : Blo 1116628 1676549 := bbase (se 4 (by rfl) ⟨157176, by rfl⟩ : syracuseStep 1676549 = 314353) (by norm_num)
theorem B1414417 : Blo 1116628 1414417 := bbase (se 2 (by rfl) ⟨530406, by rfl⟩ : syracuseStep 1414417 = 1060813) (by norm_num)
theorem B1676573 : Blo 1116628 1676573 := bbase (se 3 (by rfl) ⟨314357, by rfl⟩ : syracuseStep 1676573 = 628715) (by norm_num)
theorem B1676597 : Blo 1116628 1676597 := bbase (se 5 (by rfl) ⟨78590, by rfl⟩ : syracuseStep 1676597 = 157181) (by norm_num)
theorem B1676621 : Blo 1116628 1676621 := bbase (se 3 (by rfl) ⟨314366, by rfl⟩ : syracuseStep 1676621 = 628733) (by norm_num)
theorem B1676645 : Blo 1116628 1676645 := bbase (se 4 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 1676645 = 314371) (by norm_num)
theorem B1414513 : Blo 1116628 1414513 := bbase (se 2 (by rfl) ⟨530442, by rfl⟩ : syracuseStep 1414513 = 1060885) (by norm_num)
theorem B3020149 : Blo 1116628 3020149 := bbase (se 5 (by rfl) ⟨141569, by rfl⟩ : syracuseStep 3020149 = 283139) (by norm_num)
theorem B1676669 : Blo 1116628 1676669 := bbase (se 3 (by rfl) ⟨314375, by rfl⟩ : syracuseStep 1676669 = 628751) (by norm_num)
theorem B1676693 : Blo 1116628 1676693 := bbase (se 6 (by rfl) ⟨39297, by rfl⟩ : syracuseStep 1676693 = 78595) (by norm_num)
theorem B1676717 : Blo 1116628 1676717 := bbase (se 3 (by rfl) ⟨314384, by rfl⟩ : syracuseStep 1676717 = 628769) (by norm_num)
theorem B1676741 : Blo 1116628 1676741 := bbase (se 4 (by rfl) ⟨157194, by rfl⟩ : syracuseStep 1676741 = 314389) (by norm_num)
theorem B1676765 : Blo 1116628 1676765 := bbase (se 3 (by rfl) ⟨314393, by rfl⟩ : syracuseStep 1676765 = 628787) (by norm_num)
theorem B1676789 : Blo 1116628 1676789 := bbase (se 5 (by rfl) ⟨78599, by rfl⟩ : syracuseStep 1676789 = 157199) (by norm_num)
theorem B1676813 : Blo 1116628 1676813 := bbase (se 3 (by rfl) ⟨314402, by rfl⟩ : syracuseStep 1676813 = 628805) (by norm_num)
theorem B1414685 : Blo 1116628 1414685 := bbase (se 3 (by rfl) ⟨265253, by rfl⟩ : syracuseStep 1414685 = 530507) (by norm_num)
theorem B1676837 : Blo 1116628 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B3184181 : Blo 1116628 3184181 := bbase (se 5 (by rfl) ⟨149258, by rfl⟩ : syracuseStep 3184181 = 298517) (by norm_num)
theorem B3774005 : Blo 1116628 3774005 := bbase (se 5 (by rfl) ⟨176906, by rfl⟩ : syracuseStep 3774005 = 353813) (by norm_num)
theorem B1676861 : Blo 1116628 1676861 := bbase (se 3 (by rfl) ⟨314411, by rfl⟩ : syracuseStep 1676861 = 628823) (by norm_num)
theorem B1414741 : Blo 1116628 1414741 := bbase (se 8 (by rfl) ⟨8289, by rfl⟩ : syracuseStep 1414741 = 16579) (by norm_num)
theorem B1676885 : Blo 1116628 1676885 := bbase (se 8 (by rfl) ⟨9825, by rfl⟩ : syracuseStep 1676885 = 19651) (by norm_num)
theorem B1676909 : Blo 1116628 1676909 := bbase (se 3 (by rfl) ⟨314420, by rfl⟩ : syracuseStep 1676909 = 628841) (by norm_num)
theorem B1676933 : Blo 1116628 1676933 := bbase (se 4 (by rfl) ⟨157212, by rfl⟩ : syracuseStep 1676933 = 314425) (by norm_num)
theorem B10753685 : Blo 1116628 10753685 := bbase (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) (by norm_num)
theorem B1676957 : Blo 1116628 1676957 := bbase (se 3 (by rfl) ⟨314429, by rfl⟩ : syracuseStep 1676957 = 628859) (by norm_num)
theorem B1414837 : Blo 1116628 1414837 := bbase (se 5 (by rfl) ⟨66320, by rfl⟩ : syracuseStep 1414837 = 132641) (by norm_num)
theorem B1676981 : Blo 1116628 1676981 := bbase (se 5 (by rfl) ⟨78608, by rfl⟩ : syracuseStep 1676981 = 157217) (by norm_num)
theorem B1677005 : Blo 1116628 1677005 := bbase (se 3 (by rfl) ⟨314438, by rfl⟩ : syracuseStep 1677005 = 628877) (by norm_num)
theorem B1677029 : Blo 1116628 1677029 := bbase (se 4 (by rfl) ⟨157221, by rfl⟩ : syracuseStep 1677029 = 314443) (by norm_num)
theorem B1513189 : Blo 1116628 1513189 := bbase (se 4 (by rfl) ⟨141861, by rfl⟩ : syracuseStep 1513189 = 283723) (by norm_num)
theorem B1677053 : Blo 1116628 1677053 := bbase (se 3 (by rfl) ⟨314447, by rfl⟩ : syracuseStep 1677053 = 628895) (by norm_num)
theorem B1677077 : Blo 1116628 1677077 := bbase (se 6 (by rfl) ⟨39306, by rfl⟩ : syracuseStep 1677077 = 78613) (by norm_num)
theorem B1677101 : Blo 1116628 1677101 := bbase (se 3 (by rfl) ⟨314456, by rfl⟩ : syracuseStep 1677101 = 628913) (by norm_num)
theorem B1677125 : Blo 1116628 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B1677149 : Blo 1116628 1677149 := bbase (se 3 (by rfl) ⟨314465, by rfl⟩ : syracuseStep 1677149 = 628931) (by norm_num)
theorem B1415009 : Blo 1116628 1415009 := bbase (se 2 (by rfl) ⟨530628, by rfl⟩ : syracuseStep 1415009 = 1061257) (by norm_num)
theorem B1677173 : Blo 1116628 1677173 := bbase (se 5 (by rfl) ⟨78617, by rfl⟩ : syracuseStep 1677173 = 157235) (by norm_num)
theorem B1677197 : Blo 1116628 1677197 := bbase (se 3 (by rfl) ⟨314474, by rfl⟩ : syracuseStep 1677197 = 628949) (by norm_num)
theorem B1415065 : Blo 1116628 1415065 := bbase (se 2 (by rfl) ⟨530649, by rfl⟩ : syracuseStep 1415065 = 1061299) (by norm_num)
theorem B1677221 : Blo 1116628 1677221 := bbase (se 4 (by rfl) ⟨157239, by rfl⟩ : syracuseStep 1677221 = 314479) (by norm_num)
theorem B7641013 : Blo 1116628 7641013 := bbase (se 5 (by rfl) ⟨358172, by rfl⟩ : syracuseStep 7641013 = 716345) (by norm_num)
theorem B1677245 : Blo 1116628 1677245 := bbase (se 3 (by rfl) ⟨314483, by rfl⟩ : syracuseStep 1677245 = 628967) (by norm_num)
theorem B1677269 : Blo 1116628 1677269 := bbase (se 7 (by rfl) ⟨19655, by rfl⟩ : syracuseStep 1677269 = 39311) (by norm_num)
theorem B3774437 : Blo 1116628 3774437 := bbase (se 4 (by rfl) ⟨353853, by rfl⟩ : syracuseStep 3774437 = 707707) (by norm_num)
theorem B1677293 : Blo 1116628 1677293 := bbase (se 3 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 1677293 = 628985) (by norm_num)
theorem B1415161 : Blo 1116628 1415161 := bbase (se 2 (by rfl) ⟨530685, by rfl⟩ : syracuseStep 1415161 = 1061371) (by norm_num)
theorem B1677317 : Blo 1116628 1677317 := bbase (se 4 (by rfl) ⟨157248, by rfl⟩ : syracuseStep 1677317 = 314497) (by norm_num)
theorem B1677341 : Blo 1116628 1677341 := bbase (se 3 (by rfl) ⟨314501, by rfl⟩ : syracuseStep 1677341 = 629003) (by norm_num)
theorem B1677365 : Blo 1116628 1677365 := bbase (se 5 (by rfl) ⟨78626, by rfl⟩ : syracuseStep 1677365 = 157253) (by norm_num)
theorem B3577925 : Blo 1116628 3577925 := bbase (se 4 (by rfl) ⟨335430, by rfl⟩ : syracuseStep 3577925 = 670861) (by norm_num)
theorem B1677389 : Blo 1116628 1677389 := bbase (se 3 (by rfl) ⟨314510, by rfl⟩ : syracuseStep 1677389 = 629021) (by norm_num)
theorem B1677413 : Blo 1116628 1677413 := bbase (se 4 (by rfl) ⟨157257, by rfl⟩ : syracuseStep 1677413 = 314515) (by norm_num)
theorem B1677437 : Blo 1116628 1677437 := bbase (se 3 (by rfl) ⟨314519, by rfl⟩ : syracuseStep 1677437 = 629039) (by norm_num)
theorem B1677461 : Blo 1116628 1677461 := bbase (se 6 (by rfl) ⟨39315, by rfl⟩ : syracuseStep 1677461 = 78631) (by norm_num)
theorem B1415333 : Blo 1116628 1415333 := bbase (se 4 (by rfl) ⟨132687, by rfl⟩ : syracuseStep 1415333 = 265375) (by norm_num)
theorem B1677485 : Blo 1116628 1677485 := bbase (se 3 (by rfl) ⟨314528, by rfl⟩ : syracuseStep 1677485 = 629057) (by norm_num)
theorem B3578053 : Blo 1116628 3578053 := bbase (se 4 (by rfl) ⟨335442, by rfl⟩ : syracuseStep 3578053 = 670885) (by norm_num)
theorem B1677509 : Blo 1116628 1677509 := bbase (se 4 (by rfl) ⟨157266, by rfl⟩ : syracuseStep 1677509 = 314533) (by norm_num)
theorem B1415389 : Blo 1116628 1415389 := bbase (se 3 (by rfl) ⟨265385, by rfl⟩ : syracuseStep 1415389 = 530771) (by norm_num)
theorem B1677533 : Blo 1116628 1677533 := bbase (se 3 (by rfl) ⟨314537, by rfl⟩ : syracuseStep 1677533 = 629075) (by norm_num)
theorem B3315941 : Blo 1116628 3315941 := bbase (se 4 (by rfl) ⟨310869, by rfl⟩ : syracuseStep 3315941 = 621739) (by norm_num)
theorem B1677557 : Blo 1116628 1677557 := bbase (se 5 (by rfl) ⟨78635, by rfl⟩ : syracuseStep 1677557 = 157271) (by norm_num)
theorem B1677581 : Blo 1116628 1677581 := bbase (se 3 (by rfl) ⟨314546, by rfl⟩ : syracuseStep 1677581 = 629093) (by norm_num)
theorem B1677605 : Blo 1116628 1677605 := bbase (se 4 (by rfl) ⟨157275, by rfl⟩ : syracuseStep 1677605 = 314551) (by norm_num)
theorem B3184933 : Blo 1116628 3184933 := bbase (se 4 (by rfl) ⟨298587, by rfl⟩ : syracuseStep 3184933 = 597175) (by norm_num)
theorem B1415485 : Blo 1116628 1415485 := bbase (se 3 (by rfl) ⟨265403, by rfl⟩ : syracuseStep 1415485 = 530807) (by norm_num)
theorem B1677629 : Blo 1116628 1677629 := bbase (se 3 (by rfl) ⟨314555, by rfl⟩ : syracuseStep 1677629 = 629111) (by norm_num)
theorem B1677653 : Blo 1116628 1677653 := bbase (se 10 (by rfl) ⟨2457, by rfl⟩ : syracuseStep 1677653 = 4915) (by norm_num)
theorem B1677677 : Blo 1116628 1677677 := bbase (se 3 (by rfl) ⟨314564, by rfl⟩ : syracuseStep 1677677 = 629129) (by norm_num)
theorem B1677701 : Blo 1116628 1677701 := bbase (se 4 (by rfl) ⟨157284, by rfl⟩ : syracuseStep 1677701 = 314569) (by norm_num)
theorem B3774869 : Blo 1116628 3774869 := bbase (se 6 (by rfl) ⟨88473, by rfl⟩ : syracuseStep 3774869 = 176947) (by norm_num)
theorem B9083285 : Blo 1116628 9083285 := bbase (se 6 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 9083285 = 425779) (by norm_num)
theorem B1677725 : Blo 1116628 1677725 := bbase (se 3 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 1677725 = 629147) (by norm_num)
theorem B1677749 : Blo 1116628 1677749 := bbase (se 5 (by rfl) ⟨78644, by rfl⟩ : syracuseStep 1677749 = 157289) (by norm_num)
theorem B3578309 : Blo 1116628 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B1677773 : Blo 1116628 1677773 := bbase (se 3 (by rfl) ⟨314582, by rfl⟩ : syracuseStep 1677773 = 629165) (by norm_num)
theorem B1677797 : Blo 1116628 1677797 := bbase (se 4 (by rfl) ⟨157293, by rfl⟩ : syracuseStep 1677797 = 314587) (by norm_num)
theorem B1415657 : Blo 1116628 1415657 := bbase (se 2 (by rfl) ⟨530871, by rfl⟩ : syracuseStep 1415657 = 1061743) (by norm_num)
theorem B1677821 : Blo 1116628 1677821 := bbase (se 3 (by rfl) ⟨314591, by rfl⟩ : syracuseStep 1677821 = 629183) (by norm_num)
theorem B5380613 : Blo 1116628 5380613 := bbase (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) (by norm_num)
theorem B1677845 : Blo 1116628 1677845 := bbase (se 6 (by rfl) ⟨39324, by rfl⟩ : syracuseStep 1677845 = 78649) (by norm_num)
theorem B1415713 : Blo 1116628 1415713 := bbase (se 2 (by rfl) ⟨530892, by rfl⟩ : syracuseStep 1415713 = 1061785) (by norm_num)
theorem B1677869 : Blo 1116628 1677869 := bbase (se 3 (by rfl) ⟨314600, by rfl⟩ : syracuseStep 1677869 = 629201) (by norm_num)
theorem B1677893 : Blo 1116628 1677893 := bbase (se 4 (by rfl) ⟨157302, by rfl⟩ : syracuseStep 1677893 = 314605) (by norm_num)
theorem B1677917 : Blo 1116628 1677917 := bbase (se 3 (by rfl) ⟨314609, by rfl⟩ : syracuseStep 1677917 = 629219) (by norm_num)
theorem B1677941 : Blo 1116628 1677941 := bbase (se 5 (by rfl) ⟨78653, by rfl⟩ : syracuseStep 1677941 = 157307) (by norm_num)
theorem B1415809 : Blo 1116628 1415809 := bbase (se 2 (by rfl) ⟨530928, by rfl⟩ : syracuseStep 1415809 = 1061857) (by norm_num)
theorem B1677965 : Blo 1116628 1677965 := bbase (se 3 (by rfl) ⟨314618, by rfl⟩ : syracuseStep 1677965 = 629237) (by norm_num)
theorem B1677989 : Blo 1116628 1677989 := bbase (se 4 (by rfl) ⟨157311, by rfl⟩ : syracuseStep 1677989 = 314623) (by norm_num)
theorem B1940149 : Blo 1116628 1940149 := bbase (se 5 (by rfl) ⟨90944, by rfl⟩ : syracuseStep 1940149 = 181889) (by norm_num)
theorem B1678013 : Blo 1116628 1678013 := bbase (se 3 (by rfl) ⟨314627, by rfl⟩ : syracuseStep 1678013 = 629255) (by norm_num)
theorem B1678037 : Blo 1116628 1678037 := bbase (se 7 (by rfl) ⟨19664, by rfl⟩ : syracuseStep 1678037 = 39329) (by norm_num)
theorem B1678061 : Blo 1116628 1678061 := bbase (se 3 (by rfl) ⟨314636, by rfl⟩ : syracuseStep 1678061 = 629273) (by norm_num)
theorem B1678085 : Blo 1116628 1678085 := bbase (se 4 (by rfl) ⟨157320, by rfl⟩ : syracuseStep 1678085 = 314641) (by norm_num)
theorem B1678109 : Blo 1116628 1678109 := bbase (se 3 (by rfl) ⟨314645, by rfl⟩ : syracuseStep 1678109 = 629291) (by norm_num)
theorem B1415981 : Blo 1116628 1415981 := bbase (se 3 (by rfl) ⟨265496, by rfl⟩ : syracuseStep 1415981 = 530993) (by norm_num)
theorem B1678133 : Blo 1116628 1678133 := bbase (se 5 (by rfl) ⟨78662, by rfl⟩ : syracuseStep 1678133 = 157325) (by norm_num)
theorem B3775301 : Blo 1116628 3775301 := bbase (se 4 (by rfl) ⟨353934, by rfl⟩ : syracuseStep 3775301 = 707869) (by norm_num)
theorem B1678157 : Blo 1116628 1678157 := bbase (se 3 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 1678157 = 629309) (by norm_num)
theorem B8624981 : Blo 1116628 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B1678181 : Blo 1116628 1678181 := bbase (se 4 (by rfl) ⟨157329, by rfl⟩ : syracuseStep 1678181 = 314659) (by norm_num)
theorem B1416037 : Blo 1116628 1416037 := bbase (se 4 (by rfl) ⟨132753, by rfl⟩ : syracuseStep 1416037 = 265507) (by norm_num)
theorem B1678205 : Blo 1116628 1678205 := bbase (se 3 (by rfl) ⟨314663, by rfl⟩ : syracuseStep 1678205 = 629327) (by norm_num)
theorem B1678229 : Blo 1116628 1678229 := bbase (se 6 (by rfl) ⟨39333, by rfl⟩ : syracuseStep 1678229 = 78667) (by norm_num)
theorem B1678253 : Blo 1116628 1678253 := bbase (se 3 (by rfl) ⟨314672, by rfl⟩ : syracuseStep 1678253 = 629345) (by norm_num)
theorem B1678277 : Blo 1116628 1678277 := bbase (se 4 (by rfl) ⟨157338, by rfl⟩ : syracuseStep 1678277 = 314677) (by norm_num)
theorem B1416133 : Blo 1116628 1416133 := bbase (se 4 (by rfl) ⟨132762, by rfl⟩ : syracuseStep 1416133 = 265525) (by norm_num)
theorem B1678301 : Blo 1116628 1678301 := bbase (se 3 (by rfl) ⟨314681, by rfl⟩ : syracuseStep 1678301 = 629363) (by norm_num)
theorem B1678325 : Blo 1116628 1678325 := bbase (se 5 (by rfl) ⟨78671, by rfl⟩ : syracuseStep 1678325 = 157343) (by norm_num)
theorem B1678349 : Blo 1116628 1678349 := bbase (se 3 (by rfl) ⟨314690, by rfl⟩ : syracuseStep 1678349 = 629381) (by norm_num)
theorem B1678373 : Blo 1116628 1678373 := bbase (se 4 (by rfl) ⟨157347, by rfl⟩ : syracuseStep 1678373 = 314695) (by norm_num)
theorem B1678397 : Blo 1116628 1678397 := bbase (se 3 (by rfl) ⟨314699, by rfl⟩ : syracuseStep 1678397 = 629399) (by norm_num)
theorem B1678421 : Blo 1116628 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B1678445 : Blo 1116628 1678445 := bbase (se 3 (by rfl) ⟨314708, by rfl⟩ : syracuseStep 1678445 = 629417) (by norm_num)
theorem B1416305 : Blo 1116628 1416305 := bbase (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) (by norm_num)
theorem B1678469 : Blo 1116628 1678469 := bbase (se 4 (by rfl) ⟨157356, by rfl⟩ : syracuseStep 1678469 = 314713) (by norm_num)
theorem B1678493 : Blo 1116628 1678493 := bbase (se 3 (by rfl) ⟨314717, by rfl⟩ : syracuseStep 1678493 = 629435) (by norm_num)
theorem B1416361 : Blo 1116628 1416361 := bbase (se 2 (by rfl) ⟨531135, by rfl⟩ : syracuseStep 1416361 = 1062271) (by norm_num)
theorem B1678517 : Blo 1116628 1678517 := bbase (se 5 (by rfl) ⟨78680, by rfl⟩ : syracuseStep 1678517 = 157361) (by norm_num)
theorem B1678541 : Blo 1116628 1678541 := bbase (se 3 (by rfl) ⟨314726, by rfl⟩ : syracuseStep 1678541 = 629453) (by norm_num)
theorem B1613029 : Blo 1116628 1613029 := bbase (se 4 (by rfl) ⟨151221, by rfl⟩ : syracuseStep 1613029 = 302443) (by norm_num)
theorem B1678565 : Blo 1116628 1678565 := bbase (se 4 (by rfl) ⟨157365, by rfl⟩ : syracuseStep 1678565 = 314731) (by norm_num)
theorem B3775733 : Blo 1116628 3775733 := bbase (se 5 (by rfl) ⟨176987, by rfl⟩ : syracuseStep 3775733 = 353975) (by norm_num)
theorem B1678589 : Blo 1116628 1678589 := bbase (se 3 (by rfl) ⟨314735, by rfl⟩ : syracuseStep 1678589 = 629471) (by norm_num)
theorem B1416457 : Blo 1116628 1416457 := bbase (se 2 (by rfl) ⟨531171, by rfl⟩ : syracuseStep 1416457 = 1062343) (by norm_num)
theorem B1678613 : Blo 1116628 1678613 := bbase (se 6 (by rfl) ⟨39342, by rfl⟩ : syracuseStep 1678613 = 78685) (by norm_num)
theorem B1678637 : Blo 1116628 1678637 := bbase (se 3 (by rfl) ⟨314744, by rfl⟩ : syracuseStep 1678637 = 629489) (by norm_num)
theorem B1678661 : Blo 1116628 1678661 := bbase (se 4 (by rfl) ⟨157374, by rfl⟩ : syracuseStep 1678661 = 314749) (by norm_num)
theorem B1678685 : Blo 1116628 1678685 := bbase (se 3 (by rfl) ⟨314753, by rfl⟩ : syracuseStep 1678685 = 629507) (by norm_num)
theorem B1678709 : Blo 1116628 1678709 := bbase (se 5 (by rfl) ⟨78689, by rfl⟩ : syracuseStep 1678709 = 157379) (by norm_num)
theorem B1678733 : Blo 1116628 1678733 := bbase (se 3 (by rfl) ⟨314762, by rfl⟩ : syracuseStep 1678733 = 629525) (by norm_num)
theorem B1678757 : Blo 1116628 1678757 := bbase (se 4 (by rfl) ⟨157383, by rfl⟩ : syracuseStep 1678757 = 314767) (by norm_num)
theorem B1416629 : Blo 1116628 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B1678781 : Blo 1116628 1678781 := bbase (se 3 (by rfl) ⟨314771, by rfl⟩ : syracuseStep 1678781 = 629543) (by norm_num)
theorem B1678805 : Blo 1116628 1678805 := bbase (se 7 (by rfl) ⟨19673, by rfl⟩ : syracuseStep 1678805 = 39347) (by norm_num)
theorem B1678829 : Blo 1116628 1678829 := bbase (se 3 (by rfl) ⟨314780, by rfl⟩ : syracuseStep 1678829 = 629561) (by norm_num)
theorem B1416685 : Blo 1116628 1416685 := bbase (se 3 (by rfl) ⟨265628, by rfl⟩ : syracuseStep 1416685 = 531257) (by norm_num)
theorem B1678853 : Blo 1116628 1678853 := bbase (se 4 (by rfl) ⟨157392, by rfl⟩ : syracuseStep 1678853 = 314785) (by norm_num)
theorem B1678877 : Blo 1116628 1678877 := bbase (se 3 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 1678877 = 629579) (by norm_num)
theorem B1678901 : Blo 1116628 1678901 := bbase (se 5 (by rfl) ⟨78698, by rfl⟩ : syracuseStep 1678901 = 157397) (by norm_num)
theorem B1678925 : Blo 1116628 1678925 := bbase (se 3 (by rfl) ⟨314798, by rfl⟩ : syracuseStep 1678925 = 629597) (by norm_num)
theorem B1416781 : Blo 1116628 1416781 := bbase (se 3 (by rfl) ⟨265646, by rfl⟩ : syracuseStep 1416781 = 531293) (by norm_num)
theorem B1678949 : Blo 1116628 1678949 := bbase (se 4 (by rfl) ⟨157401, by rfl⟩ : syracuseStep 1678949 = 314803) (by norm_num)
theorem B1678973 : Blo 1116628 1678973 := bbase (se 3 (by rfl) ⟨314807, by rfl⟩ : syracuseStep 1678973 = 629615) (by norm_num)
theorem B1678997 : Blo 1116628 1678997 := bbase (se 6 (by rfl) ⟨39351, by rfl⟩ : syracuseStep 1678997 = 78703) (by norm_num)
theorem B3776165 : Blo 1116628 3776165 := bbase (se 4 (by rfl) ⟨354015, by rfl⟩ : syracuseStep 3776165 = 708031) (by norm_num)
theorem B1679021 : Blo 1116628 1679021 := bbase (se 3 (by rfl) ⟨314816, by rfl⟩ : syracuseStep 1679021 = 629633) (by norm_num)
theorem B1679045 : Blo 1116628 1679045 := bbase (se 4 (by rfl) ⟨157410, by rfl⟩ : syracuseStep 1679045 = 314821) (by norm_num)
theorem B4038341 : Blo 1116628 4038341 := bbase (se 4 (by rfl) ⟨378594, by rfl⟩ : syracuseStep 4038341 = 757189) (by norm_num)
theorem B1679069 : Blo 1116628 1679069 := bbase (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) (by norm_num)
theorem B1679093 : Blo 1116628 1679093 := bbase (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) (by norm_num)
theorem B1416953 : Blo 1116628 1416953 := bbase (se 2 (by rfl) ⟨531357, by rfl⟩ : syracuseStep 1416953 = 1062715) (by norm_num)
theorem B1679117 : Blo 1116628 1679117 := bbase (se 3 (by rfl) ⟨314834, by rfl⟩ : syracuseStep 1679117 = 629669) (by norm_num)
theorem B1679141 : Blo 1116628 1679141 := bbase (se 4 (by rfl) ⟨157419, by rfl⟩ : syracuseStep 1679141 = 314839) (by norm_num)
theorem B1417009 : Blo 1116628 1417009 := bbase (se 2 (by rfl) ⟨531378, by rfl⟩ : syracuseStep 1417009 = 1062757) (by norm_num)
theorem B1679165 : Blo 1116628 1679165 := bbase (se 3 (by rfl) ⟨314843, by rfl⟩ : syracuseStep 1679165 = 629687) (by norm_num)
theorem B5381957 : Blo 1116628 5381957 := bbase (se 4 (by rfl) ⟨504558, by rfl⟩ : syracuseStep 5381957 = 1009117) (by norm_num)
theorem B1679189 : Blo 1116628 1679189 := bbase (se 9 (by rfl) ⟨4919, by rfl⟩ : syracuseStep 1679189 = 9839) (by norm_num)
theorem B1679213 : Blo 1116628 1679213 := bbase (se 3 (by rfl) ⟨314852, by rfl⟩ : syracuseStep 1679213 = 629705) (by norm_num)
theorem B1679237 : Blo 1116628 1679237 := bbase (se 4 (by rfl) ⟨157428, by rfl⟩ : syracuseStep 1679237 = 314857) (by norm_num)
theorem B1417105 : Blo 1116628 1417105 := bbase (se 2 (by rfl) ⟨531414, by rfl⟩ : syracuseStep 1417105 = 1062829) (by norm_num)
theorem B1679261 : Blo 1116628 1679261 := bbase (se 3 (by rfl) ⟨314861, by rfl⟩ : syracuseStep 1679261 = 629723) (by norm_num)
theorem B1679285 : Blo 1116628 1679285 := bbase (se 5 (by rfl) ⟨78716, by rfl⟩ : syracuseStep 1679285 = 157433) (by norm_num)
theorem B1679309 : Blo 1116628 1679309 := bbase (se 3 (by rfl) ⟨314870, by rfl⟩ : syracuseStep 1679309 = 629741) (by norm_num)
theorem B1679333 : Blo 1116628 1679333 := bbase (se 4 (by rfl) ⟨157437, by rfl⟩ : syracuseStep 1679333 = 314875) (by norm_num)
theorem B1679357 : Blo 1116628 1679357 := bbase (se 3 (by rfl) ⟨314879, by rfl⟩ : syracuseStep 1679357 = 629759) (by norm_num)
theorem B1679381 : Blo 1116628 1679381 := bbase (se 6 (by rfl) ⟨39360, by rfl⟩ : syracuseStep 1679381 = 78721) (by norm_num)
theorem B1679405 : Blo 1116628 1679405 := bbase (se 3 (by rfl) ⟨314888, by rfl⟩ : syracuseStep 1679405 = 629777) (by norm_num)
theorem B1417277 : Blo 1116628 1417277 := bbase (se 3 (by rfl) ⟨265739, by rfl⟩ : syracuseStep 1417277 = 531479) (by norm_num)
theorem B1679429 : Blo 1116628 1679429 := bbase (se 4 (by rfl) ⟨157446, by rfl⟩ : syracuseStep 1679429 = 314893) (by norm_num)
theorem B3776597 : Blo 1116628 3776597 := bbase (se 8 (by rfl) ⟨22128, by rfl⟩ : syracuseStep 3776597 = 44257) (by norm_num)
theorem B1679453 : Blo 1116628 1679453 := bbase (se 3 (by rfl) ⟨314897, by rfl⟩ : syracuseStep 1679453 = 629795) (by norm_num)
theorem B1679477 : Blo 1116628 1679477 := bbase (se 5 (by rfl) ⟨78725, by rfl⟩ : syracuseStep 1679477 = 157451) (by norm_num)
theorem B1417333 : Blo 1116628 1417333 := bbase (se 5 (by rfl) ⟨66437, by rfl⟩ : syracuseStep 1417333 = 132875) (by norm_num)
theorem B1679501 : Blo 1116628 1679501 := bbase (se 3 (by rfl) ⟨314906, by rfl⟩ : syracuseStep 1679501 = 629813) (by norm_num)
theorem B1679525 : Blo 1116628 1679525 := bbase (se 4 (by rfl) ⟨157455, by rfl⟩ : syracuseStep 1679525 = 314911) (by norm_num)
theorem B6037685 : Blo 1116628 6037685 := bbase (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) (by norm_num)
theorem B1679549 : Blo 1116628 1679549 := bbase (se 3 (by rfl) ⟨314915, by rfl⟩ : syracuseStep 1679549 = 629831) (by norm_num)
theorem B1679573 : Blo 1116628 1679573 := bbase (se 7 (by rfl) ⟨19682, by rfl⟩ : syracuseStep 1679573 = 39365) (by norm_num)
theorem B1417429 : Blo 1116628 1417429 := bbase (se 7 (by rfl) ⟨16610, by rfl⟩ : syracuseStep 1417429 = 33221) (by norm_num)
theorem B1679597 : Blo 1116628 1679597 := bbase (se 3 (by rfl) ⟨314924, by rfl⟩ : syracuseStep 1679597 = 629849) (by norm_num)
theorem B2826485 : Blo 1116628 2826485 := bbase (se 5 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 2826485 = 264983) (by norm_num)
theorem B1679621 : Blo 1116628 1679621 := bbase (se 4 (by rfl) ⟨157464, by rfl⟩ : syracuseStep 1679621 = 314929) (by norm_num)
theorem B1679645 : Blo 1116628 1679645 := bbase (se 3 (by rfl) ⟨314933, by rfl⟩ : syracuseStep 1679645 = 629867) (by norm_num)
theorem B4530485 : Blo 1116628 4530485 := bbase (se 5 (by rfl) ⟨212366, by rfl⟩ : syracuseStep 4530485 = 424733) (by norm_num)
theorem B1679669 : Blo 1116628 1679669 := bbase (se 5 (by rfl) ⟨78734, by rfl⟩ : syracuseStep 1679669 = 157469) (by norm_num)
theorem B1679693 : Blo 1116628 1679693 := bbase (se 3 (by rfl) ⟨314942, by rfl⟩ : syracuseStep 1679693 = 629885) (by norm_num)
theorem B1679717 : Blo 1116628 1679717 := bbase (se 4 (by rfl) ⟨157473, by rfl⟩ : syracuseStep 1679717 = 314947) (by norm_num)
theorem B6037877 : Blo 1116628 6037877 := bbase (se 5 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 6037877 = 566051) (by norm_num)
theorem B1679741 : Blo 1116628 1679741 := bbase (se 3 (by rfl) ⟨314951, by rfl⟩ : syracuseStep 1679741 = 629903) (by norm_num)
theorem B1417601 : Blo 1116628 1417601 := bbase (se 2 (by rfl) ⟨531600, by rfl⟩ : syracuseStep 1417601 = 1063201) (by norm_num)
theorem B1679765 : Blo 1116628 1679765 := bbase (se 6 (by rfl) ⟨39369, by rfl⟩ : syracuseStep 1679765 = 78739) (by norm_num)
theorem B1679789 : Blo 1116628 1679789 := bbase (se 3 (by rfl) ⟨314960, by rfl⟩ : syracuseStep 1679789 = 629921) (by norm_num)
theorem B2826677 : Blo 1116628 2826677 := bbase (se 5 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 2826677 = 265001) (by norm_num)
theorem B1417657 : Blo 1116628 1417657 := bbase (se 2 (by rfl) ⟨531621, by rfl⟩ : syracuseStep 1417657 = 1063243) (by norm_num)
theorem B1679813 : Blo 1116628 1679813 := bbase (se 4 (by rfl) ⟨157482, by rfl⟩ : syracuseStep 1679813 = 314965) (by norm_num)
theorem B1679837 : Blo 1116628 1679837 := bbase (se 3 (by rfl) ⟨314969, by rfl⟩ : syracuseStep 1679837 = 629939) (by norm_num)
theorem B1679861 : Blo 1116628 1679861 := bbase (se 5 (by rfl) ⟨78743, by rfl⟩ : syracuseStep 1679861 = 157487) (by norm_num)
theorem B3777029 : Blo 1116628 3777029 := bbase (se 4 (by rfl) ⟨354096, by rfl⟩ : syracuseStep 3777029 = 708193) (by norm_num)
theorem B1679885 : Blo 1116628 1679885 := bbase (se 3 (by rfl) ⟨314978, by rfl⟩ : syracuseStep 1679885 = 629957) (by norm_num)
theorem B1417753 : Blo 1116628 1417753 := bbase (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) (by norm_num)
theorem B1679909 : Blo 1116628 1679909 := bbase (se 4 (by rfl) ⟨157491, by rfl⟩ : syracuseStep 1679909 = 314983) (by norm_num)
theorem B1679933 : Blo 1116628 1679933 := bbase (se 3 (by rfl) ⟨314987, by rfl⟩ : syracuseStep 1679933 = 629975) (by norm_num)
theorem B1679957 : Blo 1116628 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B1679981 : Blo 1116628 1679981 := bbase (se 3 (by rfl) ⟨314996, by rfl⟩ : syracuseStep 1679981 = 629993) (by norm_num)
theorem B1680005 : Blo 1116628 1680005 := bbase (se 4 (by rfl) ⟨157500, by rfl⟩ : syracuseStep 1680005 = 315001) (by norm_num)
theorem B8495765 : Blo 1116628 8495765 := bbase (se 6 (by rfl) ⟨199119, by rfl⟩ : syracuseStep 8495765 = 398239) (by norm_num)
theorem B1680029 : Blo 1116628 1680029 := bbase (se 3 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 1680029 = 630011) (by norm_num)
theorem B1680053 : Blo 1116628 1680053 := bbase (se 5 (by rfl) ⟨78752, by rfl⟩ : syracuseStep 1680053 = 157505) (by norm_num)
theorem B1417925 : Blo 1116628 1417925 := bbase (se 4 (by rfl) ⟨132930, by rfl⟩ : syracuseStep 1417925 = 265861) (by norm_num)
theorem B1680077 : Blo 1116628 1680077 := bbase (se 3 (by rfl) ⟨315014, by rfl⟩ : syracuseStep 1680077 = 630029) (by norm_num)
theorem B1680101 : Blo 1116628 1680101 := bbase (se 4 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 1680101 = 315019) (by norm_num)
theorem B1680125 : Blo 1116628 1680125 := bbase (se 3 (by rfl) ⟨315023, by rfl⟩ : syracuseStep 1680125 = 630047) (by norm_num)
theorem B1417981 : Blo 1116628 1417981 := bbase (se 3 (by rfl) ⟨265871, by rfl⟩ : syracuseStep 1417981 = 531743) (by norm_num)
theorem B2827021 : Blo 1116628 2827021 := bbase (se 3 (by rfl) ⟨530066, by rfl⟩ : syracuseStep 2827021 = 1060133) (by norm_num)
theorem B1680149 : Blo 1116628 1680149 := bbase (se 6 (by rfl) ⟨39378, by rfl⟩ : syracuseStep 1680149 = 78757) (by norm_num)
theorem B1680173 : Blo 1116628 1680173 := bbase (se 3 (by rfl) ⟨315032, by rfl⟩ : syracuseStep 1680173 = 630065) (by norm_num)
theorem B1680197 : Blo 1116628 1680197 := bbase (se 4 (by rfl) ⟨157518, by rfl⟩ : syracuseStep 1680197 = 315037) (by norm_num)
theorem B3580757 : Blo 1116628 3580757 := bbase (se 9 (by rfl) ⟨10490, by rfl⟩ : syracuseStep 3580757 = 20981) (by norm_num)
theorem B1680221 : Blo 1116628 1680221 := bbase (se 3 (by rfl) ⟨315041, by rfl⟩ : syracuseStep 1680221 = 630083) (by norm_num)
theorem B1418077 : Blo 1116628 1418077 := bbase (se 3 (by rfl) ⟨265889, by rfl⟩ : syracuseStep 1418077 = 531779) (by norm_num)
theorem B1680245 : Blo 1116628 1680245 := bbase (se 5 (by rfl) ⟨78761, by rfl⟩ : syracuseStep 1680245 = 157523) (by norm_num)
theorem B2827133 : Blo 1116628 2827133 := bbase (se 3 (by rfl) ⟨530087, by rfl⟩ : syracuseStep 2827133 = 1060175) (by norm_num)
theorem B1680269 : Blo 1116628 1680269 := bbase (se 3 (by rfl) ⟨315050, by rfl⟩ : syracuseStep 1680269 = 630101) (by norm_num)
theorem B2270101 : Blo 1116628 2270101 := bbase (se 6 (by rfl) ⟨53205, by rfl⟩ : syracuseStep 2270101 = 106411) (by norm_num)
theorem B1680293 : Blo 1116628 1680293 := bbase (se 4 (by rfl) ⟨157527, by rfl⟩ : syracuseStep 1680293 = 315055) (by norm_num)
theorem B3777461 : Blo 1116628 3777461 := bbase (se 5 (by rfl) ⟨177068, by rfl⟩ : syracuseStep 3777461 = 354137) (by norm_num)
theorem B1680317 : Blo 1116628 1680317 := bbase (se 3 (by rfl) ⟨315059, by rfl⟩ : syracuseStep 1680317 = 630119) (by norm_num)
theorem B1680341 : Blo 1116628 1680341 := bbase (se 7 (by rfl) ⟨19691, by rfl⟩ : syracuseStep 1680341 = 39383) (by norm_num)
theorem B1680365 : Blo 1116628 1680365 := bbase (se 3 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 1680365 = 630137) (by norm_num)
theorem B1680389 : Blo 1116628 1680389 := bbase (se 4 (by rfl) ⟨157536, by rfl⟩ : syracuseStep 1680389 = 315073) (by norm_num)
theorem B1418249 : Blo 1116628 1418249 := bbase (se 2 (by rfl) ⟨531843, by rfl⟩ : syracuseStep 1418249 = 1063687) (by norm_num)
theorem B1680413 : Blo 1116628 1680413 := bbase (se 3 (by rfl) ⟨315077, by rfl⟩ : syracuseStep 1680413 = 630155) (by norm_num)
theorem B1680437 : Blo 1116628 1680437 := bbase (se 5 (by rfl) ⟨78770, by rfl⟩ : syracuseStep 1680437 = 157541) (by norm_num)
theorem B2827325 : Blo 1116628 2827325 := bbase (se 3 (by rfl) ⟨530123, by rfl⟩ : syracuseStep 2827325 = 1060247) (by norm_num)
theorem B3187781 : Blo 1116628 3187781 := bbase (se 4 (by rfl) ⟨298854, by rfl⟩ : syracuseStep 3187781 = 597709) (by norm_num)
theorem B1680461 : Blo 1116628 1680461 := bbase (se 3 (by rfl) ⟨315086, by rfl⟩ : syracuseStep 1680461 = 630173) (by norm_num)
theorem B1680485 : Blo 1116628 1680485 := bbase (se 4 (by rfl) ⟨157545, by rfl⟩ : syracuseStep 1680485 = 315091) (by norm_num)
theorem B1680509 : Blo 1116628 1680509 := bbase (se 3 (by rfl) ⟨315095, by rfl⟩ : syracuseStep 1680509 = 630191) (by norm_num)
theorem B16131221 : Blo 1116628 16131221 := bbase (se 6 (by rfl) ⟨378075, by rfl⟩ : syracuseStep 16131221 = 756151) (by norm_num)
theorem B1680533 : Blo 1116628 1680533 := bbase (se 6 (by rfl) ⟨39387, by rfl⟩ : syracuseStep 1680533 = 78775) (by norm_num)
theorem B1680557 : Blo 1116628 1680557 := bbase (se 3 (by rfl) ⟨315104, by rfl⟩ : syracuseStep 1680557 = 630209) (by norm_num)
theorem B1680581 : Blo 1116628 1680581 := bbase (se 4 (by rfl) ⟨157554, by rfl⟩ : syracuseStep 1680581 = 315109) (by norm_num)
theorem B1680605 : Blo 1116628 1680605 := bbase (se 3 (by rfl) ⟨315113, by rfl⟩ : syracuseStep 1680605 = 630227) (by norm_num)
theorem B1680629 : Blo 1116628 1680629 := bbase (se 5 (by rfl) ⟨78779, by rfl⟩ : syracuseStep 1680629 = 157559) (by norm_num)
theorem B1680653 : Blo 1116628 1680653 := bbase (se 3 (by rfl) ⟨315122, by rfl⟩ : syracuseStep 1680653 = 630245) (by norm_num)
theorem B1680677 : Blo 1116628 1680677 := bbase (se 4 (by rfl) ⟨157563, by rfl⟩ : syracuseStep 1680677 = 315127) (by norm_num)
theorem B1680701 : Blo 1116628 1680701 := bbase (se 3 (by rfl) ⟨315131, by rfl⟩ : syracuseStep 1680701 = 630263) (by norm_num)
theorem B1680725 : Blo 1116628 1680725 := bbase (se 12 (by rfl) ⟨615, by rfl⟩ : syracuseStep 1680725 = 1231) (by norm_num)
theorem B3777893 : Blo 1116628 3777893 := bbase (se 4 (by rfl) ⟨354177, by rfl⟩ : syracuseStep 3777893 = 708355) (by norm_num)
theorem B1680749 : Blo 1116628 1680749 := bbase (se 3 (by rfl) ⟨315140, by rfl⟩ : syracuseStep 1680749 = 630281) (by norm_num)
theorem B1680773 : Blo 1116628 1680773 := bbase (se 4 (by rfl) ⟨157572, by rfl⟩ : syracuseStep 1680773 = 315145) (by norm_num)
theorem B2827669 : Blo 1116628 2827669 := bbase (se 6 (by rfl) ⟨66273, by rfl⟩ : syracuseStep 2827669 = 132547) (by norm_num)
theorem B1680797 : Blo 1116628 1680797 := bbase (se 3 (by rfl) ⟨315149, by rfl⟩ : syracuseStep 1680797 = 630299) (by norm_num)
theorem B1680821 : Blo 1116628 1680821 := bbase (se 5 (by rfl) ⟨78788, by rfl⟩ : syracuseStep 1680821 = 157577) (by norm_num)
theorem B1680845 : Blo 1116628 1680845 := bbase (se 3 (by rfl) ⟨315158, by rfl⟩ : syracuseStep 1680845 = 630317) (by norm_num)
theorem B1680869 : Blo 1116628 1680869 := bbase (se 4 (by rfl) ⟨157581, by rfl⟩ : syracuseStep 1680869 = 315163) (by norm_num)
theorem B1680893 : Blo 1116628 1680893 := bbase (se 3 (by rfl) ⟨315167, by rfl⟩ : syracuseStep 1680893 = 630335) (by norm_num)
theorem B2827781 : Blo 1116628 2827781 := bbase (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) (by norm_num)
theorem B4531717 : Blo 1116628 4531717 := bbase (se 4 (by rfl) ⟨424848, by rfl⟩ : syracuseStep 4531717 = 849697) (by norm_num)
theorem B1680917 : Blo 1116628 1680917 := bbase (se 6 (by rfl) ⟨39396, by rfl⟩ : syracuseStep 1680917 = 78793) (by norm_num)
theorem B1680941 : Blo 1116628 1680941 := bbase (se 3 (by rfl) ⟨315176, by rfl⟩ : syracuseStep 1680941 = 630353) (by norm_num)
theorem B4531781 : Blo 1116628 4531781 := bbase (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) (by norm_num)
theorem B2827973 : Blo 1116628 2827973 := bbase (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) (by norm_num)
theorem B3778325 : Blo 1116628 3778325 := bbase (se 6 (by rfl) ⟨88554, by rfl⟩ : syracuseStep 3778325 = 177109) (by norm_num)
theorem B2828317 : Blo 1116628 2828317 := bbase (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) (by norm_num)
theorem B2271341 : Blo 1116628 2271341 := bbase (se 3 (by rfl) ⟨425876, by rfl⟩ : syracuseStep 2271341 = 851753) (by norm_num)
theorem B2828429 : Blo 1116628 2828429 := bbase (se 3 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 2828429 = 1060661) (by norm_num)
theorem B3582101 : Blo 1116628 3582101 := bbase (se 6 (by rfl) ⟨83955, by rfl⟩ : syracuseStep 3582101 = 167911) (by norm_num)
theorem B3778757 : Blo 1116628 3778757 := bbase (se 4 (by rfl) ⟨354258, by rfl⟩ : syracuseStep 3778757 = 708517) (by norm_num)
theorem B3188965 : Blo 1116628 3188965 := bbase (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) (by norm_num)
theorem B2828621 : Blo 1116628 2828621 := bbase (se 3 (by rfl) ⟨530366, by rfl⟩ : syracuseStep 2828621 = 1060733) (by norm_num)
theorem B3189125 : Blo 1116628 3189125 := bbase (se 4 (by rfl) ⟨298980, by rfl⟩ : syracuseStep 3189125 = 597961) (by norm_num)
theorem B3779189 : Blo 1116628 3779189 := bbase (se 5 (by rfl) ⟨177149, by rfl⟩ : syracuseStep 3779189 = 354299) (by norm_num)
theorem B3189365 : Blo 1116628 3189365 := bbase (se 5 (by rfl) ⟨149501, by rfl⟩ : syracuseStep 3189365 = 299003) (by norm_num)
theorem B2828965 : Blo 1116628 2828965 := bbase (se 4 (by rfl) ⟨265215, by rfl⟩ : syracuseStep 2828965 = 530431) (by norm_num)
theorem B3025621 : Blo 1116628 3025621 := bbase (se 7 (by rfl) ⟨35456, by rfl⟩ : syracuseStep 3025621 = 70913) (by norm_num)
theorem B2829077 : Blo 1116628 2829077 := bbase (se 6 (by rfl) ⟨66306, by rfl⟩ : syracuseStep 2829077 = 132613) (by norm_num)
theorem B3025685 : Blo 1116628 3025685 := bbase (se 6 (by rfl) ⟨70914, by rfl⟩ : syracuseStep 3025685 = 141829) (by norm_num)
theorem B1256233 : Blo 1116628 1256233 := bbase (se 2 (by rfl) ⟨471087, by rfl⟩ : syracuseStep 1256233 = 942175) (by norm_num)
theorem B3189557 : Blo 1116628 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B1256269 : Blo 1116628 1256269 := bbase (se 3 (by rfl) ⟨235550, by rfl⟩ : syracuseStep 1256269 = 471101) (by norm_num)
theorem B1256305 : Blo 1116628 1256305 := bbase (se 2 (by rfl) ⟨471114, by rfl⟩ : syracuseStep 1256305 = 942229) (by norm_num)
theorem B1256341 : Blo 1116628 1256341 := bbase (se 6 (by rfl) ⟨29445, by rfl⟩ : syracuseStep 1256341 = 58891) (by norm_num)
theorem B1256377 : Blo 1116628 1256377 := bbase (se 2 (by rfl) ⟨471141, by rfl⟩ : syracuseStep 1256377 = 942283) (by norm_num)
theorem B2829269 : Blo 1116628 2829269 := bbase (se 7 (by rfl) ⟨33155, by rfl⟩ : syracuseStep 2829269 = 66311) (by norm_num)
theorem B1256413 : Blo 1116628 1256413 := bbase (se 3 (by rfl) ⟨235577, by rfl⟩ : syracuseStep 1256413 = 471155) (by norm_num)
theorem B1256449 : Blo 1116628 1256449 := bbase (se 2 (by rfl) ⟨471168, by rfl⟩ : syracuseStep 1256449 = 942337) (by norm_num)
theorem B1256485 : Blo 1116628 1256485 := bbase (se 4 (by rfl) ⟨117795, by rfl⟩ : syracuseStep 1256485 = 235591) (by norm_num)
theorem B3779621 : Blo 1116628 3779621 := bbase (se 4 (by rfl) ⟨354339, by rfl⟩ : syracuseStep 3779621 = 708679) (by norm_num)
theorem B1256521 : Blo 1116628 1256521 := bbase (se 2 (by rfl) ⟨471195, by rfl⟩ : syracuseStep 1256521 = 942391) (by norm_num)
theorem B1256557 : Blo 1116628 1256557 := bbase (se 3 (by rfl) ⟨235604, by rfl⟩ : syracuseStep 1256557 = 471209) (by norm_num)
theorem B1256593 : Blo 1116628 1256593 := bbase (se 2 (by rfl) ⟨471222, by rfl⟩ : syracuseStep 1256593 = 942445) (by norm_num)
theorem B1256629 : Blo 1116628 1256629 := bbase (se 5 (by rfl) ⟨58904, by rfl⟩ : syracuseStep 1256629 = 117809) (by norm_num)
theorem B1256665 : Blo 1116628 1256665 := bbase (se 2 (by rfl) ⟨471249, by rfl⟩ : syracuseStep 1256665 = 942499) (by norm_num)
theorem B1256701 : Blo 1116628 1256701 := bbase (se 3 (by rfl) ⟨235631, by rfl⟩ : syracuseStep 1256701 = 471263) (by norm_num)
theorem B1256737 : Blo 1116628 1256737 := bbase (se 2 (by rfl) ⟨471276, by rfl⟩ : syracuseStep 1256737 = 942553) (by norm_num)
theorem B2829613 : Blo 1116628 2829613 := bbase (se 3 (by rfl) ⟨530552, by rfl⟩ : syracuseStep 2829613 = 1061105) (by norm_num)
theorem B1256773 : Blo 1116628 1256773 := bbase (se 4 (by rfl) ⟨117822, by rfl⟩ : syracuseStep 1256773 = 235645) (by norm_num)
theorem B1256809 : Blo 1116628 1256809 := bbase (se 2 (by rfl) ⟨471303, by rfl⟩ : syracuseStep 1256809 = 942607) (by norm_num)
theorem B1256845 : Blo 1116628 1256845 := bbase (se 3 (by rfl) ⟨235658, by rfl⟩ : syracuseStep 1256845 = 471317) (by norm_num)
theorem B2829725 : Blo 1116628 2829725 := bbase (se 3 (by rfl) ⟨530573, by rfl⟩ : syracuseStep 2829725 = 1061147) (by norm_num)
theorem B1256881 : Blo 1116628 1256881 := bbase (se 2 (by rfl) ⟨471330, by rfl⟩ : syracuseStep 1256881 = 942661) (by norm_num)
theorem B1256917 : Blo 1116628 1256917 := bbase (se 7 (by rfl) ⟨14729, by rfl⟩ : syracuseStep 1256917 = 29459) (by norm_num)
theorem B3780053 : Blo 1116628 3780053 := bbase (se 7 (by rfl) ⟨44297, by rfl⟩ : syracuseStep 3780053 = 88595) (by norm_num)
theorem B1256953 : Blo 1116628 1256953 := bbase (se 2 (by rfl) ⟨471357, by rfl⟩ : syracuseStep 1256953 = 942715) (by norm_num)
theorem B1256989 : Blo 1116628 1256989 := bbase (se 3 (by rfl) ⟨235685, by rfl⟩ : syracuseStep 1256989 = 471371) (by norm_num)
theorem B1257025 : Blo 1116628 1257025 := bbase (se 2 (by rfl) ⟨471384, by rfl⟩ : syracuseStep 1257025 = 942769) (by norm_num)
theorem B2829917 : Blo 1116628 2829917 := bbase (se 3 (by rfl) ⟨530609, by rfl⟩ : syracuseStep 2829917 = 1061219) (by norm_num)
theorem B1257061 : Blo 1116628 1257061 := bbase (se 4 (by rfl) ⟨117849, by rfl⟩ : syracuseStep 1257061 = 235699) (by norm_num)
theorem B1257097 : Blo 1116628 1257097 := bbase (se 2 (by rfl) ⟨471411, by rfl⟩ : syracuseStep 1257097 = 942823) (by norm_num)
theorem B1257133 : Blo 1116628 1257133 := bbase (se 3 (by rfl) ⟨235712, by rfl⟩ : syracuseStep 1257133 = 471425) (by norm_num)
theorem B1257169 : Blo 1116628 1257169 := bbase (se 2 (by rfl) ⟨471438, by rfl⟩ : syracuseStep 1257169 = 942877) (by norm_num)
theorem B1257205 : Blo 1116628 1257205 := bbase (se 5 (by rfl) ⟨58931, by rfl⟩ : syracuseStep 1257205 = 117863) (by norm_num)
theorem B3190549 : Blo 1116628 3190549 := bbase (se 6 (by rfl) ⟨74778, by rfl⟩ : syracuseStep 3190549 = 149557) (by norm_num)
theorem B1257241 : Blo 1116628 1257241 := bbase (se 2 (by rfl) ⟨471465, by rfl⟩ : syracuseStep 1257241 = 942931) (by norm_num)
theorem B1257277 : Blo 1116628 1257277 := bbase (se 3 (by rfl) ⟨235739, by rfl⟩ : syracuseStep 1257277 = 471479) (by norm_num)
theorem B1257313 : Blo 1116628 1257313 := bbase (se 2 (by rfl) ⟨471492, by rfl⟩ : syracuseStep 1257313 = 942985) (by norm_num)
theorem B1257349 : Blo 1116628 1257349 := bbase (se 4 (by rfl) ⟨117876, by rfl⟩ : syracuseStep 1257349 = 235753) (by norm_num)
theorem B3780485 : Blo 1116628 3780485 := bbase (se 4 (by rfl) ⟨354420, by rfl⟩ : syracuseStep 3780485 = 708841) (by norm_num)
theorem B1257385 : Blo 1116628 1257385 := bbase (se 2 (by rfl) ⟨471519, by rfl⟩ : syracuseStep 1257385 = 943039) (by norm_num)
theorem B2830261 : Blo 1116628 2830261 := bbase (se 5 (by rfl) ⟨132668, by rfl⟩ : syracuseStep 2830261 = 265337) (by norm_num)
theorem B1257421 : Blo 1116628 1257421 := bbase (se 3 (by rfl) ⟨235766, by rfl⟩ : syracuseStep 1257421 = 471533) (by norm_num)
theorem B1257457 : Blo 1116628 1257457 := bbase (se 2 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 1257457 = 943093) (by norm_num)
theorem B1257493 : Blo 1116628 1257493 := bbase (se 6 (by rfl) ⟨29472, by rfl⟩ : syracuseStep 1257493 = 58945) (by norm_num)
theorem B2830373 : Blo 1116628 2830373 := bbase (se 4 (by rfl) ⟨265347, by rfl⟩ : syracuseStep 2830373 = 530695) (by norm_num)
theorem B1257529 : Blo 1116628 1257529 := bbase (se 2 (by rfl) ⟨471573, by rfl⟩ : syracuseStep 1257529 = 943147) (by norm_num)
theorem B1257565 : Blo 1116628 1257565 := bbase (se 3 (by rfl) ⟨235793, by rfl⟩ : syracuseStep 1257565 = 471587) (by norm_num)
theorem B3584101 : Blo 1116628 3584101 := bbase (se 4 (by rfl) ⟨336009, by rfl⟩ : syracuseStep 3584101 = 672019) (by norm_num)
theorem B1257601 : Blo 1116628 1257601 := bbase (se 2 (by rfl) ⟨471600, by rfl⟩ : syracuseStep 1257601 = 943201) (by norm_num)
theorem B1257637 : Blo 1116628 1257637 := bbase (se 4 (by rfl) ⟨117903, by rfl⟩ : syracuseStep 1257637 = 235807) (by norm_num)
theorem B1257673 : Blo 1116628 1257673 := bbase (se 2 (by rfl) ⟨471627, by rfl⟩ : syracuseStep 1257673 = 943255) (by norm_num)
theorem B2830565 : Blo 1116628 2830565 := bbase (se 4 (by rfl) ⟨265365, by rfl⟩ : syracuseStep 2830565 = 530731) (by norm_num)
theorem B1257709 : Blo 1116628 1257709 := bbase (se 3 (by rfl) ⟨235820, by rfl⟩ : syracuseStep 1257709 = 471641) (by norm_num)
theorem B1257745 : Blo 1116628 1257745 := bbase (se 2 (by rfl) ⟨471654, by rfl⟩ : syracuseStep 1257745 = 943309) (by norm_num)
theorem B1257781 : Blo 1116628 1257781 := bbase (se 5 (by rfl) ⟨58958, by rfl⟩ : syracuseStep 1257781 = 117917) (by norm_num)
theorem B3780917 : Blo 1116628 3780917 := bbase (se 5 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 3780917 = 354461) (by norm_num)
theorem B1257817 : Blo 1116628 1257817 := bbase (se 2 (by rfl) ⟨471681, by rfl⟩ : syracuseStep 1257817 = 943363) (by norm_num)
theorem B7647605 : Blo 1116628 7647605 := bbase (se 5 (by rfl) ⟨358481, by rfl⟩ : syracuseStep 7647605 = 716963) (by norm_num)
theorem B1257853 : Blo 1116628 1257853 := bbase (se 3 (by rfl) ⟨235847, by rfl⟩ : syracuseStep 1257853 = 471695) (by norm_num)
theorem B1257889 : Blo 1116628 1257889 := bbase (se 2 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 1257889 = 943417) (by norm_num)
theorem B1913269 : Blo 1116628 1913269 := bbase (se 5 (by rfl) ⟨89684, by rfl⟩ : syracuseStep 1913269 = 179369) (by norm_num)
theorem B1257925 : Blo 1116628 1257925 := bbase (se 4 (by rfl) ⟨117930, by rfl⟩ : syracuseStep 1257925 = 235861) (by norm_num)
theorem B4305349 : Blo 1116628 4305349 := bbase (se 4 (by rfl) ⟨403626, by rfl⟩ : syracuseStep 4305349 = 807253) (by norm_num)
theorem B1257961 : Blo 1116628 1257961 := bbase (se 2 (by rfl) ⟨471735, by rfl⟩ : syracuseStep 1257961 = 943471) (by norm_num)
theorem B1257997 : Blo 1116628 1257997 := bbase (se 3 (by rfl) ⟨235874, by rfl⟩ : syracuseStep 1257997 = 471749) (by norm_num)
theorem B1258033 : Blo 1116628 1258033 := bbase (se 2 (by rfl) ⟨471762, by rfl⟩ : syracuseStep 1258033 = 943525) (by norm_num)
theorem B2830909 : Blo 1116628 2830909 := bbase (se 3 (by rfl) ⟨530795, by rfl⟩ : syracuseStep 2830909 = 1061591) (by norm_num)
theorem B7156309 : Blo 1116628 7156309 := bbase (se 8 (by rfl) ⟨41931, by rfl⟩ : syracuseStep 7156309 = 83863) (by norm_num)
theorem B1258069 : Blo 1116628 1258069 := bbase (se 8 (by rfl) ⟨7371, by rfl⟩ : syracuseStep 1258069 = 14743) (by norm_num)
theorem B1258105 : Blo 1116628 1258105 := bbase (se 2 (by rfl) ⟨471789, by rfl⟩ : syracuseStep 1258105 = 943579) (by norm_num)
theorem B1192573 : Blo 1116628 1192573 := bbase (se 3 (by rfl) ⟨223607, by rfl⟩ : syracuseStep 1192573 = 447215) (by norm_num)
theorem B1258141 : Blo 1116628 1258141 := bbase (se 3 (by rfl) ⟨235901, by rfl⟩ : syracuseStep 1258141 = 471803) (by norm_num)
theorem B2831021 : Blo 1116628 2831021 := bbase (se 3 (by rfl) ⟨530816, by rfl⟩ : syracuseStep 2831021 = 1061633) (by norm_num)
theorem B1258177 : Blo 1116628 1258177 := bbase (se 2 (by rfl) ⟨471816, by rfl⟩ : syracuseStep 1258177 = 943633) (by norm_num)
theorem B1258213 : Blo 1116628 1258213 := bbase (se 4 (by rfl) ⟨117957, by rfl⟩ : syracuseStep 1258213 = 235915) (by norm_num)
theorem B3781349 : Blo 1116628 3781349 := bbase (se 4 (by rfl) ⟨354501, by rfl⟩ : syracuseStep 3781349 = 709003) (by norm_num)
theorem B1913597 : Blo 1116628 1913597 := bbase (se 3 (by rfl) ⟨358799, by rfl⟩ : syracuseStep 1913597 = 717599) (by norm_num)
theorem B1258249 : Blo 1116628 1258249 := bbase (se 2 (by rfl) ⟨471843, by rfl⟩ : syracuseStep 1258249 = 943687) (by norm_num)
theorem B13611797 : Blo 1116628 13611797 := bbase (se 6 (by rfl) ⟨319026, by rfl⟩ : syracuseStep 13611797 = 638053) (by norm_num)
theorem B1258285 : Blo 1116628 1258285 := bbase (se 3 (by rfl) ⟨235928, by rfl⟩ : syracuseStep 1258285 = 471857) (by norm_num)
theorem B1258321 : Blo 1116628 1258321 := bbase (se 2 (by rfl) ⟨471870, by rfl⟩ : syracuseStep 1258321 = 943741) (by norm_num)
theorem B2831213 : Blo 1116628 2831213 := bbase (se 3 (by rfl) ⟨530852, by rfl⟩ : syracuseStep 2831213 = 1061705) (by norm_num)
theorem B1258357 : Blo 1116628 1258357 := bbase (se 5 (by rfl) ⟨58985, by rfl⟩ : syracuseStep 1258357 = 117971) (by norm_num)
theorem B1258393 : Blo 1116628 1258393 := bbase (se 2 (by rfl) ⟨471897, by rfl⟩ : syracuseStep 1258393 = 943795) (by norm_num)
theorem B1258429 : Blo 1116628 1258429 := bbase (se 3 (by rfl) ⟨235955, by rfl⟩ : syracuseStep 1258429 = 471911) (by norm_num)
theorem B1258465 : Blo 1116628 1258465 := bbase (se 2 (by rfl) ⟨471924, by rfl⟩ : syracuseStep 1258465 = 943849) (by norm_num)
theorem B1258501 : Blo 1116628 1258501 := bbase (se 4 (by rfl) ⟨117984, by rfl⟩ : syracuseStep 1258501 = 235969) (by norm_num)
theorem B1258537 : Blo 1116628 1258537 := bbase (se 2 (by rfl) ⟨471951, by rfl⟩ : syracuseStep 1258537 = 943903) (by norm_num)
theorem B1193005 : Blo 1116628 1193005 := bbase (se 3 (by rfl) ⟨223688, by rfl⟩ : syracuseStep 1193005 = 447377) (by norm_num)
theorem B1258573 : Blo 1116628 1258573 := bbase (se 3 (by rfl) ⟨235982, by rfl⟩ : syracuseStep 1258573 = 471965) (by norm_num)
theorem B1258609 : Blo 1116628 1258609 := bbase (se 2 (by rfl) ⟨471978, by rfl⟩ : syracuseStep 1258609 = 943957) (by norm_num)
theorem B1193077 : Blo 1116628 1193077 := bbase (se 5 (by rfl) ⟨55925, by rfl⟩ : syracuseStep 1193077 = 111851) (by norm_num)
theorem B1258645 : Blo 1116628 1258645 := bbase (se 6 (by rfl) ⟨29499, by rfl⟩ : syracuseStep 1258645 = 58999) (by norm_num)
theorem B3781781 : Blo 1116628 3781781 := bbase (se 6 (by rfl) ⟨88635, by rfl⟩ : syracuseStep 3781781 = 177271) (by norm_num)
theorem B1258681 : Blo 1116628 1258681 := bbase (se 2 (by rfl) ⟨472005, by rfl⟩ : syracuseStep 1258681 = 944011) (by norm_num)
theorem B2831557 : Blo 1116628 2831557 := bbase (se 4 (by rfl) ⟨265458, by rfl⟩ : syracuseStep 2831557 = 530917) (by norm_num)
theorem B1258717 : Blo 1116628 1258717 := bbase (se 3 (by rfl) ⟨236009, by rfl⟩ : syracuseStep 1258717 = 472019) (by norm_num)
theorem B1258753 : Blo 1116628 1258753 := bbase (se 2 (by rfl) ⟨472032, by rfl⟩ : syracuseStep 1258753 = 944065) (by norm_num)
theorem B1258789 : Blo 1116628 1258789 := bbase (se 4 (by rfl) ⟨118011, by rfl⟩ : syracuseStep 1258789 = 236023) (by norm_num)
theorem B2831669 : Blo 1116628 2831669 := bbase (se 5 (by rfl) ⟨132734, by rfl⟩ : syracuseStep 2831669 = 265469) (by norm_num)
theorem B1258825 : Blo 1116628 1258825 := bbase (se 2 (by rfl) ⟨472059, by rfl⟩ : syracuseStep 1258825 = 944119) (by norm_num)
theorem B1258861 : Blo 1116628 1258861 := bbase (se 3 (by rfl) ⟨236036, by rfl⟩ : syracuseStep 1258861 = 472073) (by norm_num)
theorem B3028357 : Blo 1116628 3028357 := bbase (se 4 (by rfl) ⟨283908, by rfl⟩ : syracuseStep 3028357 = 567817) (by norm_num)
theorem B1258897 : Blo 1116628 1258897 := bbase (se 2 (by rfl) ⟨472086, by rfl⟩ : syracuseStep 1258897 = 944173) (by norm_num)
theorem B1258933 : Blo 1116628 1258933 := bbase (se 5 (by rfl) ⟨59012, by rfl⟩ : syracuseStep 1258933 = 118025) (by norm_num)
theorem B1258969 : Blo 1116628 1258969 := bbase (se 2 (by rfl) ⟨472113, by rfl⟩ : syracuseStep 1258969 = 944227) (by norm_num)
theorem B1193449 : Blo 1116628 1193449 := bbase (se 2 (by rfl) ⟨447543, by rfl⟩ : syracuseStep 1193449 = 895087) (by norm_num)
theorem B2831861 : Blo 1116628 2831861 := bbase (se 5 (by rfl) ⟨132743, by rfl⟩ : syracuseStep 2831861 = 265487) (by norm_num)
theorem B1259005 : Blo 1116628 1259005 := bbase (se 3 (by rfl) ⟨236063, by rfl⟩ : syracuseStep 1259005 = 472127) (by norm_num)
theorem B1259041 : Blo 1116628 1259041 := bbase (se 2 (by rfl) ⟨472140, by rfl⟩ : syracuseStep 1259041 = 944281) (by norm_num)
theorem B2012741 : Blo 1116628 2012741 := bbase (se 4 (by rfl) ⟨188694, by rfl⟩ : syracuseStep 2012741 = 377389) (by norm_num)
theorem B1259077 : Blo 1116628 1259077 := bbase (se 4 (by rfl) ⟨118038, by rfl⟩ : syracuseStep 1259077 = 236077) (by norm_num)
theorem B1259113 : Blo 1116628 1259113 := bbase (se 2 (by rfl) ⟨472167, by rfl⟩ : syracuseStep 1259113 = 944335) (by norm_num)
theorem B1259149 : Blo 1116628 1259149 := bbase (se 3 (by rfl) ⟨236090, by rfl⟩ : syracuseStep 1259149 = 472181) (by norm_num)
theorem B1259185 : Blo 1116628 1259185 := bbase (se 2 (by rfl) ⟨472194, by rfl⟩ : syracuseStep 1259185 = 944389) (by norm_num)
theorem B1259221 : Blo 1116628 1259221 := bbase (se 7 (by rfl) ⟨14756, by rfl⟩ : syracuseStep 1259221 = 29513) (by norm_num)
theorem B1259257 : Blo 1116628 1259257 := bbase (se 2 (by rfl) ⟨472221, by rfl⟩ : syracuseStep 1259257 = 944443) (by norm_num)
theorem B1259293 : Blo 1116628 1259293 := bbase (se 3 (by rfl) ⟨236117, by rfl⟩ : syracuseStep 1259293 = 472235) (by norm_num)
theorem B1259329 : Blo 1116628 1259329 := bbase (se 2 (by rfl) ⟨472248, by rfl⟩ : syracuseStep 1259329 = 944497) (by norm_num)
theorem B2832205 : Blo 1116628 2832205 := bbase (se 3 (by rfl) ⟨531038, by rfl⟩ : syracuseStep 2832205 = 1062077) (by norm_num)
theorem B1193825 : Blo 1116628 1193825 := bbase (se 2 (by rfl) ⟨447684, by rfl⟩ : syracuseStep 1193825 = 895369) (by norm_num)
theorem B1259365 : Blo 1116628 1259365 := bbase (se 4 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 1259365 = 236131) (by norm_num)
theorem B1259401 : Blo 1116628 1259401 := bbase (se 2 (by rfl) ⟨472275, by rfl⟩ : syracuseStep 1259401 = 944551) (by norm_num)
theorem B4601765 : Blo 1116628 4601765 := bbase (se 4 (by rfl) ⟨431415, by rfl⟩ : syracuseStep 4601765 = 862831) (by norm_num)
theorem B1193897 : Blo 1116628 1193897 := bbase (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) (by norm_num)
theorem B1259437 : Blo 1116628 1259437 := bbase (se 3 (by rfl) ⟨236144, by rfl⟩ : syracuseStep 1259437 = 472289) (by norm_num)
theorem B2832317 : Blo 1116628 2832317 := bbase (se 3 (by rfl) ⟨531059, by rfl⟩ : syracuseStep 2832317 = 1062119) (by norm_num)
theorem B1259473 : Blo 1116628 1259473 := bbase (se 2 (by rfl) ⟨472302, by rfl⟩ : syracuseStep 1259473 = 944605) (by norm_num)
theorem B1259509 : Blo 1116628 1259509 := bbase (se 5 (by rfl) ⟨59039, by rfl⟩ : syracuseStep 1259509 = 118079) (by norm_num)
theorem B4241429 : Blo 1116628 4241429 := bbase (se 6 (by rfl) ⟨99408, by rfl⟩ : syracuseStep 4241429 = 198817) (by norm_num)
theorem B1259545 : Blo 1116628 1259545 := bbase (se 2 (by rfl) ⟨472329, by rfl⟩ : syracuseStep 1259545 = 944659) (by norm_num)
theorem B1259581 : Blo 1116628 1259581 := bbase (se 3 (by rfl) ⟨236171, by rfl⟩ : syracuseStep 1259581 = 472343) (by norm_num)
theorem B1259617 : Blo 1116628 1259617 := bbase (se 2 (by rfl) ⟨472356, by rfl⟩ : syracuseStep 1259617 = 944713) (by norm_num)
theorem B1194085 : Blo 1116628 1194085 := bbase (se 4 (by rfl) ⟨111945, by rfl⟩ : syracuseStep 1194085 = 223891) (by norm_num)
theorem B2832509 : Blo 1116628 2832509 := bbase (se 3 (by rfl) ⟨531095, by rfl⟩ : syracuseStep 2832509 = 1062191) (by norm_num)
theorem B1259653 : Blo 1116628 1259653 := bbase (se 4 (by rfl) ⟨118092, by rfl⟩ : syracuseStep 1259653 = 236185) (by norm_num)
theorem B1259689 : Blo 1116628 1259689 := bbase (se 2 (by rfl) ⟨472383, by rfl⟩ : syracuseStep 1259689 = 944767) (by norm_num)
theorem B1259725 : Blo 1116628 1259725 := bbase (se 3 (by rfl) ⟨236198, by rfl⟩ : syracuseStep 1259725 = 472397) (by norm_num)
theorem B1259761 : Blo 1116628 1259761 := bbase (se 2 (by rfl) ⟨472410, by rfl⟩ : syracuseStep 1259761 = 944821) (by norm_num)
theorem B1259797 : Blo 1116628 1259797 := bbase (se 6 (by rfl) ⟨29526, by rfl⟩ : syracuseStep 1259797 = 59053) (by norm_num)
theorem B1194269 : Blo 1116628 1194269 := bbase (se 3 (by rfl) ⟨223925, by rfl⟩ : syracuseStep 1194269 = 447851) (by norm_num)
theorem B4241717 : Blo 1116628 4241717 := bbase (se 5 (by rfl) ⟨198830, by rfl⟩ : syracuseStep 4241717 = 397661) (by norm_num)
theorem B1259833 : Blo 1116628 1259833 := bbase (se 2 (by rfl) ⟨472437, by rfl⟩ : syracuseStep 1259833 = 944875) (by norm_num)
theorem B1259869 : Blo 1116628 1259869 := bbase (se 3 (by rfl) ⟨236225, by rfl⟩ : syracuseStep 1259869 = 472451) (by norm_num)
theorem B1259905 : Blo 1116628 1259905 := bbase (se 2 (by rfl) ⟨472464, by rfl⟩ : syracuseStep 1259905 = 944929) (by norm_num)
theorem B1259941 : Blo 1116628 1259941 := bbase (se 4 (by rfl) ⟨118119, by rfl⟩ : syracuseStep 1259941 = 236239) (by norm_num)
theorem B1259977 : Blo 1116628 1259977 := bbase (se 2 (by rfl) ⟨472491, by rfl⟩ : syracuseStep 1259977 = 944983) (by norm_num)
theorem B2832853 : Blo 1116628 2832853 := bbase (se 7 (by rfl) ⟨33197, by rfl⟩ : syracuseStep 2832853 = 66395) (by norm_num)
theorem B1260013 : Blo 1116628 1260013 := bbase (se 3 (by rfl) ⟨236252, by rfl⟩ : syracuseStep 1260013 = 472505) (by norm_num)
theorem B1260049 : Blo 1116628 1260049 := bbase (se 2 (by rfl) ⟨472518, by rfl⟩ : syracuseStep 1260049 = 945037) (by norm_num)
theorem B1260085 : Blo 1116628 1260085 := bbase (se 5 (by rfl) ⟨59066, by rfl⟩ : syracuseStep 1260085 = 118133) (by norm_num)
theorem B2832965 : Blo 1116628 2832965 := bbase (se 4 (by rfl) ⟨265590, by rfl⟩ : syracuseStep 2832965 = 531181) (by norm_num)
theorem B1260121 : Blo 1116628 1260121 := bbase (se 2 (by rfl) ⟨472545, by rfl⟩ : syracuseStep 1260121 = 945091) (by norm_num)
theorem B1260157 : Blo 1116628 1260157 := bbase (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) (by norm_num)
theorem B1260193 : Blo 1116628 1260193 := bbase (se 2 (by rfl) ⟨472572, by rfl⟩ : syracuseStep 1260193 = 945145) (by norm_num)
theorem B1260229 : Blo 1116628 1260229 := bbase (se 4 (by rfl) ⟨118146, by rfl⟩ : syracuseStep 1260229 = 236293) (by norm_num)
theorem B6372053 : Blo 1116628 6372053 := bbase (se 7 (by rfl) ⟨74672, by rfl⟩ : syracuseStep 6372053 = 149345) (by norm_num)
theorem B1260265 : Blo 1116628 1260265 := bbase (se 2 (by rfl) ⟨472599, by rfl⟩ : syracuseStep 1260265 = 945199) (by norm_num)
theorem B2833157 : Blo 1116628 2833157 := bbase (se 4 (by rfl) ⟨265608, by rfl⟩ : syracuseStep 2833157 = 531217) (by norm_num)
theorem B1260301 : Blo 1116628 1260301 := bbase (se 3 (by rfl) ⟨236306, by rfl⟩ : syracuseStep 1260301 = 472613) (by norm_num)
theorem B5749541 : Blo 1116628 5749541 := bbase (se 4 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 5749541 = 1078039) (by norm_num)
theorem B1260337 : Blo 1116628 1260337 := bbase (se 2 (by rfl) ⟨472626, by rfl⟩ : syracuseStep 1260337 = 945253) (by norm_num)
theorem B1817405 : Blo 1116628 1817405 := bbase (se 3 (by rfl) ⟨340763, by rfl⟩ : syracuseStep 1817405 = 681527) (by norm_num)
theorem B1260373 : Blo 1116628 1260373 := bbase (se 9 (by rfl) ⟨3692, by rfl⟩ : syracuseStep 1260373 = 7385) (by norm_num)
theorem B1260409 : Blo 1116628 1260409 := bbase (se 2 (by rfl) ⟨472653, by rfl⟩ : syracuseStep 1260409 = 945307) (by norm_num)
theorem B1260445 : Blo 1116628 1260445 := bbase (se 3 (by rfl) ⟨236333, by rfl⟩ : syracuseStep 1260445 = 472667) (by norm_num)
theorem B7650229 : Blo 1116628 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B1260481 : Blo 1116628 1260481 := bbase (se 2 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 1260481 = 945361) (by norm_num)
theorem B1260517 : Blo 1116628 1260517 := bbase (se 4 (by rfl) ⟨118173, by rfl⟩ : syracuseStep 1260517 = 236347) (by norm_num)
theorem B1260553 : Blo 1116628 1260553 := bbase (se 2 (by rfl) ⟨472707, by rfl⟩ : syracuseStep 1260553 = 945415) (by norm_num)
theorem B1195021 : Blo 1116628 1195021 := bbase (se 3 (by rfl) ⟨224066, by rfl⟩ : syracuseStep 1195021 = 448133) (by norm_num)
theorem B1260589 : Blo 1116628 1260589 := bbase (se 3 (by rfl) ⟨236360, by rfl⟩ : syracuseStep 1260589 = 472721) (by norm_num)
theorem B3587125 : Blo 1116628 3587125 := bbase (se 5 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 3587125 = 336293) (by norm_num)
theorem B5749829 : Blo 1116628 5749829 := bbase (se 4 (by rfl) ⟨539046, by rfl⟩ : syracuseStep 5749829 = 1078093) (by norm_num)
theorem B1260625 : Blo 1116628 1260625 := bbase (se 2 (by rfl) ⟨472734, by rfl⟩ : syracuseStep 1260625 = 945469) (by norm_num)
theorem B1195093 : Blo 1116628 1195093 := bbase (se 8 (by rfl) ⟨7002, by rfl⟩ : syracuseStep 1195093 = 14005) (by norm_num)
theorem B2833501 : Blo 1116628 2833501 := bbase (se 3 (by rfl) ⟨531281, by rfl⟩ : syracuseStep 2833501 = 1062563) (by norm_num)
theorem B1260661 : Blo 1116628 1260661 := bbase (se 5 (by rfl) ⟨59093, by rfl⟩ : syracuseStep 1260661 = 118187) (by norm_num)
theorem B1260697 : Blo 1116628 1260697 := bbase (se 2 (by rfl) ⟨472761, by rfl⟩ : syracuseStep 1260697 = 945523) (by norm_num)
theorem B2833613 : Blo 1116628 2833613 := bbase (se 3 (by rfl) ⟨531302, by rfl⟩ : syracuseStep 2833613 = 1062605) (by norm_num)
theorem B5749973 : Blo 1116628 5749973 := bbase (se 7 (by rfl) ⟨67382, by rfl⟩ : syracuseStep 5749973 = 134765) (by norm_num)
theorem B2014429 : Blo 1116628 2014429 := bbase (se 3 (by rfl) ⟨377705, by rfl⟩ : syracuseStep 2014429 = 755411) (by norm_num)
theorem B1195273 : Blo 1116628 1195273 := bbase (se 2 (by rfl) ⟨448227, by rfl⟩ : syracuseStep 1195273 = 896455) (by norm_num)
theorem B3063109 : Blo 1116628 3063109 := bbase (se 4 (by rfl) ⟨287166, by rfl⟩ : syracuseStep 3063109 = 574333) (by norm_num)
theorem B2833805 : Blo 1116628 2833805 := bbase (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) (by norm_num)
theorem B2014637 : Blo 1116628 2014637 := bbase (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) (by norm_num)
theorem B2014645 : Blo 1116628 2014645 := bbase (se 5 (by rfl) ⟨94436, by rfl⟩ : syracuseStep 2014645 = 188873) (by norm_num)
theorem B4242901 : Blo 1116628 4242901 := bbase (se 7 (by rfl) ⟨49721, by rfl⟩ : syracuseStep 4242901 = 99443) (by norm_num)
theorem B2014789 : Blo 1116628 2014789 := bbase (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) (by norm_num)
theorem B1818293 : Blo 1116628 1818293 := bbase (se 5 (by rfl) ⟨85232, by rfl⟩ : syracuseStep 1818293 = 170465) (by norm_num)
theorem B1195717 : Blo 1116628 1195717 := bbase (se 4 (by rfl) ⟨112098, by rfl⟩ : syracuseStep 1195717 = 224197) (by norm_num)
theorem B2834149 : Blo 1116628 2834149 := bbase (se 4 (by rfl) ⟨265701, by rfl⟩ : syracuseStep 2834149 = 531403) (by norm_num)
theorem B4243205 : Blo 1116628 4243205 := bbase (se 4 (by rfl) ⟨397800, by rfl⟩ : syracuseStep 4243205 = 795601) (by norm_num)
theorem B4079413 : Blo 1116628 4079413 := bbase (se 5 (by rfl) ⟨191222, by rfl⟩ : syracuseStep 4079413 = 382445) (by norm_num)
theorem B1195841 : Blo 1116628 1195841 := bbase (se 2 (by rfl) ⟨448440, by rfl⟩ : syracuseStep 1195841 = 896881) (by norm_num)
theorem B2834261 : Blo 1116628 2834261 := bbase (se 9 (by rfl) ⟨8303, by rfl⟩ : syracuseStep 2834261 = 16607) (by norm_num)
theorem B2834453 : Blo 1116628 2834453 := bbase (se 6 (by rfl) ⟨66432, by rfl⟩ : syracuseStep 2834453 = 132865) (by norm_num)
theorem B6045749 : Blo 1116628 6045749 := bbase (se 5 (by rfl) ⟨283394, by rfl⟩ : syracuseStep 6045749 = 566789) (by norm_num)
theorem B1196093 : Blo 1116628 1196093 := bbase (se 3 (by rfl) ⟨224267, by rfl⟩ : syracuseStep 1196093 = 448535) (by norm_num)
theorem B1884397 : Blo 1116628 1884397 := bbase (se 3 (by rfl) ⟨353324, by rfl⟩ : syracuseStep 1884397 = 706649) (by norm_num)
theorem B8503541 : Blo 1116628 8503541 := bbase (se 5 (by rfl) ⟨398603, by rfl⟩ : syracuseStep 8503541 = 797207) (by norm_num)
theorem B2015509 : Blo 1116628 2015509 := bbase (se 6 (by rfl) ⟨47238, by rfl⟩ : syracuseStep 2015509 = 94477) (by norm_num)
theorem B1884485 : Blo 1116628 1884485 := bbase (se 4 (by rfl) ⟨176670, by rfl⟩ : syracuseStep 1884485 = 353341) (by norm_num)
theorem B4538693 : Blo 1116628 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B2015597 : Blo 1116628 2015597 := bbase (se 3 (by rfl) ⟨377924, by rfl⟩ : syracuseStep 2015597 = 755849) (by norm_num)
theorem B2834797 : Blo 1116628 2834797 := bbase (se 3 (by rfl) ⟨531524, by rfl⟩ : syracuseStep 2834797 = 1063049) (by norm_num)
theorem B1884613 : Blo 1116628 1884613 := bbase (se 4 (by rfl) ⟨176682, by rfl⟩ : syracuseStep 1884613 = 353365) (by norm_num)
theorem B2834909 : Blo 1116628 2834909 := bbase (se 3 (by rfl) ⟨531545, by rfl⟩ : syracuseStep 2834909 = 1063091) (by norm_num)
theorem B1196537 : Blo 1116628 1196537 := bbase (se 2 (by rfl) ⟨448701, by rfl⟩ : syracuseStep 1196537 = 897403) (by norm_num)
theorem B1884701 : Blo 1116628 1884701 := bbase (se 3 (by rfl) ⟨353381, by rfl⟩ : syracuseStep 1884701 = 706763) (by norm_num)
theorem B1884829 : Blo 1116628 1884829 := bbase (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) (by norm_num)
theorem B2835101 : Blo 1116628 2835101 := bbase (se 3 (by rfl) ⟨531581, by rfl⟩ : syracuseStep 2835101 = 1063163) (by norm_num)
theorem B1884917 : Blo 1116628 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B2016029 : Blo 1116628 2016029 := bbase (se 3 (by rfl) ⟨378005, by rfl⟩ : syracuseStep 2016029 = 756011) (by norm_num)
theorem B1885045 : Blo 1116628 1885045 := bbase (se 5 (by rfl) ⟨88361, by rfl⟩ : syracuseStep 1885045 = 176723) (by norm_num)
theorem B2016173 : Blo 1116628 2016173 := bbase (se 3 (by rfl) ⟨378032, by rfl⟩ : syracuseStep 2016173 = 756065) (by norm_num)
theorem B1885133 : Blo 1116628 1885133 := bbase (se 3 (by rfl) ⟨353462, by rfl⟩ : syracuseStep 1885133 = 706925) (by norm_num)
theorem B2835445 : Blo 1116628 2835445 := bbase (se 5 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 2835445 = 265823) (by norm_num)
theorem B1885261 : Blo 1116628 1885261 := bbase (se 3 (by rfl) ⟨353486, by rfl⟩ : syracuseStep 1885261 = 706973) (by norm_num)
theorem B2835557 : Blo 1116628 2835557 := bbase (se 4 (by rfl) ⟨265833, by rfl⟩ : syracuseStep 2835557 = 531667) (by norm_num)
theorem B5653637 : Blo 1116628 5653637 := bbase (se 4 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 5653637 = 1060057) (by norm_num)
theorem B2016389 : Blo 1116628 2016389 := bbase (se 4 (by rfl) ⟨189036, by rfl⟩ : syracuseStep 2016389 = 378073) (by norm_num)
theorem B1885349 : Blo 1116628 1885349 := bbase (se 4 (by rfl) ⟨176751, by rfl⟩ : syracuseStep 1885349 = 353503) (by norm_num)
theorem B1590445 : Blo 1116628 1590445 := bbase (se 3 (by rfl) ⟨298208, by rfl⟩ : syracuseStep 1590445 = 596417) (by norm_num)
theorem B3884213 : Blo 1116628 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B1885477 : Blo 1116628 1885477 := bbase (se 4 (by rfl) ⟨176763, by rfl⟩ : syracuseStep 1885477 = 353527) (by norm_num)
theorem B2835749 : Blo 1116628 2835749 := bbase (se 4 (by rfl) ⟨265851, by rfl⟩ : syracuseStep 2835749 = 531703) (by norm_num)
theorem B1885565 : Blo 1116628 1885565 := bbase (se 3 (by rfl) ⟨353543, by rfl⟩ : syracuseStep 1885565 = 707087) (by norm_num)
theorem B1361305 : Blo 1116628 1361305 := bbase (se 2 (by rfl) ⟨510489, by rfl⟩ : syracuseStep 1361305 = 1020979) (by norm_num)
theorem B1590781 : Blo 1116628 1590781 := bbase (se 3 (by rfl) ⟨298271, by rfl⟩ : syracuseStep 1590781 = 596543) (by norm_num)
theorem B1885693 : Blo 1116628 1885693 := bbase (se 3 (by rfl) ⟨353567, by rfl⟩ : syracuseStep 1885693 = 707135) (by norm_num)
theorem B1885781 : Blo 1116628 1885781 := bbase (se 8 (by rfl) ⟨11049, by rfl⟩ : syracuseStep 1885781 = 22099) (by norm_num)
theorem B2836093 : Blo 1116628 2836093 := bbase (se 3 (by rfl) ⟨531767, by rfl⟩ : syracuseStep 2836093 = 1063535) (by norm_num)
theorem B1590997 : Blo 1116628 1590997 := bbase (se 7 (by rfl) ⟨18644, by rfl⟩ : syracuseStep 1590997 = 37289) (by norm_num)
theorem B1885909 : Blo 1116628 1885909 := bbase (se 7 (by rfl) ⟨22100, by rfl⟩ : syracuseStep 1885909 = 44201) (by norm_num)
theorem B2836205 : Blo 1116628 2836205 := bbase (se 3 (by rfl) ⟨531788, by rfl⟩ : syracuseStep 2836205 = 1063577) (by norm_num)
theorem B1885997 : Blo 1116628 1885997 := bbase (se 3 (by rfl) ⟨353624, by rfl⟩ : syracuseStep 1885997 = 707249) (by norm_num)
theorem B4245317 : Blo 1116628 4245317 := bbase (se 4 (by rfl) ⟨397998, by rfl⟩ : syracuseStep 4245317 = 795997) (by norm_num)
theorem B3590021 : Blo 1116628 3590021 := bbase (se 4 (by rfl) ⟨336564, by rfl⟩ : syracuseStep 3590021 = 673129) (by norm_num)
theorem B2017181 : Blo 1116628 2017181 := bbase (se 3 (by rfl) ⟨378221, by rfl⟩ : syracuseStep 2017181 = 756443) (by norm_num)
theorem B2869157 : Blo 1116628 2869157 := bbase (se 4 (by rfl) ⟨268983, by rfl⟩ : syracuseStep 2869157 = 537967) (by norm_num)
theorem B1886125 : Blo 1116628 1886125 := bbase (se 3 (by rfl) ⟨353648, by rfl⟩ : syracuseStep 1886125 = 707297) (by norm_num)
theorem B2836397 : Blo 1116628 2836397 := bbase (se 3 (by rfl) ⟨531824, by rfl⟩ : syracuseStep 2836397 = 1063649) (by norm_num)
theorem B9553909 : Blo 1116628 9553909 := bbase (se 5 (by rfl) ⟨447839, by rfl⟩ : syracuseStep 9553909 = 895679) (by norm_num)
theorem B1886213 : Blo 1116628 1886213 := bbase (se 4 (by rfl) ⟨176832, by rfl⟩ : syracuseStep 1886213 = 353665) (by norm_num)
theorem B1132585 : Blo 1116628 1132585 := bbase (se 2 (by rfl) ⟨424719, by rfl⟩ : syracuseStep 1132585 = 849439) (by norm_num)
theorem B1591373 : Blo 1116628 1591373 := bbase (se 3 (by rfl) ⟨298382, by rfl⟩ : syracuseStep 1591373 = 596765) (by norm_num)
theorem B4245605 : Blo 1116628 4245605 := bbase (se 4 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 4245605 = 796051) (by norm_num)
theorem B2017405 : Blo 1116628 2017405 := bbase (se 3 (by rfl) ⟨378263, by rfl⟩ : syracuseStep 2017405 = 756527) (by norm_num)
theorem B1886341 : Blo 1116628 1886341 := bbase (se 4 (by rfl) ⟨176844, by rfl⟩ : syracuseStep 1886341 = 353689) (by norm_num)
theorem B1886429 : Blo 1116628 1886429 := bbase (se 3 (by rfl) ⟨353705, by rfl⟩ : syracuseStep 1886429 = 707411) (by norm_num)
theorem B4770053 : Blo 1116628 4770053 := bbase (se 4 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 4770053 = 894385) (by norm_num)
theorem B1886557 : Blo 1116628 1886557 := bbase (se 3 (by rfl) ⟨353729, by rfl⟩ : syracuseStep 1886557 = 707459) (by norm_num)
theorem B5654933 : Blo 1116628 5654933 := bbase (se 6 (by rfl) ⟨132537, by rfl⟩ : syracuseStep 5654933 = 265075) (by norm_num)
theorem B1886645 : Blo 1116628 1886645 := bbase (se 5 (by rfl) ⟨88436, by rfl⟩ : syracuseStep 1886645 = 176873) (by norm_num)
theorem B7162357 : Blo 1116628 7162357 := bbase (se 5 (by rfl) ⟨335735, by rfl⟩ : syracuseStep 7162357 = 671471) (by norm_num)
theorem B1886773 : Blo 1116628 1886773 := bbase (se 5 (by rfl) ⟨88442, by rfl⟩ : syracuseStep 1886773 = 176885) (by norm_num)
theorem B1886861 : Blo 1116628 1886861 := bbase (se 3 (by rfl) ⟨353786, by rfl⟩ : syracuseStep 1886861 = 707573) (by norm_num)
theorem B2869925 : Blo 1116628 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B1886989 : Blo 1116628 1886989 := bbase (se 3 (by rfl) ⟨353810, by rfl⟩ : syracuseStep 1886989 = 707621) (by norm_num)
theorem B10734389 : Blo 1116628 10734389 := bbase (se 5 (by rfl) ⟨503174, by rfl⟩ : syracuseStep 10734389 = 1006349) (by norm_num)
theorem B1887077 : Blo 1116628 1887077 := bbase (se 4 (by rfl) ⟨176913, by rfl⟩ : syracuseStep 1887077 = 353827) (by norm_num)
theorem B1133497 : Blo 1116628 1133497 := bbase (se 2 (by rfl) ⟨425061, by rfl⟩ : syracuseStep 1133497 = 850123) (by norm_num)
theorem B1887205 : Blo 1116628 1887205 := bbase (se 4 (by rfl) ⟨176925, by rfl⟩ : syracuseStep 1887205 = 353851) (by norm_num)
theorem B1788949 : Blo 1116628 1788949 := bbase (se 6 (by rfl) ⟨41928, by rfl⟩ : syracuseStep 1788949 = 83857) (by norm_num)
theorem B1887293 : Blo 1116628 1887293 := bbase (se 3 (by rfl) ⟨353867, by rfl⟩ : syracuseStep 1887293 = 707735) (by norm_num)
theorem B1887421 : Blo 1116628 1887421 := bbase (se 3 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 1887421 = 707783) (by norm_num)
theorem B4246789 : Blo 1116628 4246789 := bbase (se 4 (by rfl) ⟨398136, by rfl⟩ : syracuseStep 4246789 = 796273) (by norm_num)
theorem B1887509 : Blo 1116628 1887509 := bbase (se 6 (by rfl) ⟨44238, by rfl⟩ : syracuseStep 1887509 = 88477) (by norm_num)
theorem B5098837 : Blo 1116628 5098837 := bbase (se 11 (by rfl) ⟨3734, by rfl⟩ : syracuseStep 5098837 = 7469) (by norm_num)
theorem B1887637 : Blo 1116628 1887637 := bbase (se 6 (by rfl) ⟨44241, by rfl⟩ : syracuseStep 1887637 = 88483) (by norm_num)
theorem B1789373 : Blo 1116628 1789373 := bbase (se 3 (by rfl) ⟨335507, by rfl⟩ : syracuseStep 1789373 = 671015) (by norm_num)
theorem B24202709 : Blo 1116628 24202709 := bbase (se 7 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 24202709 = 567251) (by norm_num)
theorem B1592797 : Blo 1116628 1592797 := bbase (se 3 (by rfl) ⟨298649, by rfl⟩ : syracuseStep 1592797 = 597299) (by norm_num)
theorem B1887725 : Blo 1116628 1887725 := bbase (se 3 (by rfl) ⟨353948, by rfl⟩ : syracuseStep 1887725 = 707897) (by norm_num)
theorem B16109077 : Blo 1116628 16109077 := bbase (se 6 (by rfl) ⟨377556, by rfl⟩ : syracuseStep 16109077 = 755113) (by norm_num)
theorem B1134113 : Blo 1116628 1134113 := bbase (se 2 (by rfl) ⟨425292, by rfl⟩ : syracuseStep 1134113 = 850585) (by norm_num)
theorem B4247093 : Blo 1116628 4247093 := bbase (se 5 (by rfl) ⟨199082, by rfl⟩ : syracuseStep 4247093 = 398165) (by norm_num)
theorem B1887853 : Blo 1116628 1887853 := bbase (se 3 (by rfl) ⟨353972, by rfl⟩ : syracuseStep 1887853 = 707945) (by norm_num)
theorem B5656229 : Blo 1116628 5656229 := bbase (se 4 (by rfl) ⟨530271, by rfl⟩ : syracuseStep 5656229 = 1060543) (by norm_num)
theorem B1887941 : Blo 1116628 1887941 := bbase (se 4 (by rfl) ⟨176994, by rfl⟩ : syracuseStep 1887941 = 353989) (by norm_num)
theorem B4542149 : Blo 1116628 4542149 := bbase (se 4 (by rfl) ⟨425826, by rfl⟩ : syracuseStep 4542149 = 851653) (by norm_num)
theorem B1789661 : Blo 1116628 1789661 := bbase (se 3 (by rfl) ⟨335561, by rfl⟩ : syracuseStep 1789661 = 671123) (by norm_num)
theorem B4837141 : Blo 1116628 4837141 := bbase (se 6 (by rfl) ⟨113370, by rfl⟩ : syracuseStep 4837141 = 226741) (by norm_num)
theorem B1888069 : Blo 1116628 1888069 := bbase (se 4 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 1888069 = 354013) (by norm_num)
theorem B4542277 : Blo 1116628 4542277 := bbase (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) (by norm_num)
theorem B1888157 : Blo 1116628 1888157 := bbase (se 3 (by rfl) ⟨354029, by rfl⟩ : syracuseStep 1888157 = 708059) (by norm_num)
theorem B9555893 : Blo 1116628 9555893 := bbase (se 5 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 9555893 = 895865) (by norm_num)
theorem B1789885 : Blo 1116628 1789885 := bbase (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) (by norm_num)
theorem B1888285 : Blo 1116628 1888285 := bbase (se 3 (by rfl) ⟨354053, by rfl⟩ : syracuseStep 1888285 = 708107) (by norm_num)
theorem B1593389 : Blo 1116628 1593389 := bbase (se 3 (by rfl) ⟨298760, by rfl⟩ : syracuseStep 1593389 = 597521) (by norm_num)
theorem B1888373 : Blo 1116628 1888373 := bbase (se 5 (by rfl) ⟨88517, by rfl⟩ : syracuseStep 1888373 = 177035) (by norm_num)
theorem B1593469 : Blo 1116628 1593469 := bbase (se 3 (by rfl) ⟨298775, by rfl⟩ : syracuseStep 1593469 = 597551) (by norm_num)
theorem B7852277 : Blo 1116628 7852277 := bbase (se 5 (by rfl) ⟨368075, by rfl⟩ : syracuseStep 7852277 = 736151) (by norm_num)
theorem B1888501 : Blo 1116628 1888501 := bbase (se 5 (by rfl) ⟨88523, by rfl⟩ : syracuseStep 1888501 = 177047) (by norm_num)
theorem B1593589 : Blo 1116628 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B1888589 : Blo 1116628 1888589 := bbase (se 3 (by rfl) ⟨354110, by rfl⟩ : syracuseStep 1888589 = 708221) (by norm_num)
theorem B1593685 : Blo 1116628 1593685 := bbase (se 10 (by rfl) ⟨2334, by rfl⟩ : syracuseStep 1593685 = 4669) (by norm_num)
theorem B1888717 : Blo 1116628 1888717 := bbase (se 3 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 1888717 = 708269) (by norm_num)
theorem B1364441 : Blo 1116628 1364441 := bbase (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) (by norm_num)
theorem B1888805 : Blo 1116628 1888805 := bbase (se 4 (by rfl) ⟨177075, by rfl⟩ : syracuseStep 1888805 = 354151) (by norm_num)
theorem B1888933 : Blo 1116628 1888933 := bbase (se 4 (by rfl) ⟨177087, by rfl⟩ : syracuseStep 1888933 = 354175) (by norm_num)
theorem B3232453 : Blo 1116628 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B1889021 : Blo 1116628 1889021 := bbase (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) (by norm_num)
theorem B2904893 : Blo 1116628 2904893 := bbase (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) (by norm_num)
theorem B1594181 : Blo 1116628 1594181 := bbase (se 4 (by rfl) ⟨149454, by rfl⟩ : syracuseStep 1594181 = 298909) (by norm_num)
theorem B3232613 : Blo 1116628 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B1889149 : Blo 1116628 1889149 := bbase (se 3 (by rfl) ⟨354215, by rfl⟩ : syracuseStep 1889149 = 708431) (by norm_num)
theorem B5657525 : Blo 1116628 5657525 := bbase (se 5 (by rfl) ⟨265196, by rfl⟩ : syracuseStep 5657525 = 530393) (by norm_num)
theorem B1889237 : Blo 1116628 1889237 := bbase (se 7 (by rfl) ⟨22139, by rfl⟩ : syracuseStep 1889237 = 44279) (by norm_num)
theorem B2872325 : Blo 1116628 2872325 := bbase (se 4 (by rfl) ⟨269280, by rfl⟩ : syracuseStep 2872325 = 538561) (by norm_num)
theorem B1791013 : Blo 1116628 1791013 := bbase (se 4 (by rfl) ⟨167907, by rfl⟩ : syracuseStep 1791013 = 335815) (by norm_num)
theorem B1889365 : Blo 1116628 1889365 := bbase (se 8 (by rfl) ⟨11070, by rfl⟩ : syracuseStep 1889365 = 22141) (by norm_num)
theorem B1889453 : Blo 1116628 1889453 := bbase (se 3 (by rfl) ⟨354272, by rfl⟩ : syracuseStep 1889453 = 708545) (by norm_num)
theorem B1135829 : Blo 1116628 1135829 := bbase (se 7 (by rfl) ⟨13310, by rfl⟩ : syracuseStep 1135829 = 26621) (by norm_num)
theorem B7165205 : Blo 1116628 7165205 := bbase (se 6 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 7165205 = 335869) (by norm_num)
theorem B1889581 : Blo 1116628 1889581 := bbase (se 3 (by rfl) ⟨354296, by rfl⟩ : syracuseStep 1889581 = 708593) (by norm_num)
theorem B1594733 : Blo 1116628 1594733 := bbase (se 3 (by rfl) ⟨299012, by rfl⟩ : syracuseStep 1594733 = 598025) (by norm_num)
theorem B1889669 : Blo 1116628 1889669 := bbase (se 4 (by rfl) ⟨177156, by rfl⟩ : syracuseStep 1889669 = 354313) (by norm_num)
theorem B1791461 : Blo 1116628 1791461 := bbase (se 4 (by rfl) ⟨167949, by rfl⟩ : syracuseStep 1791461 = 335899) (by norm_num)
theorem B5821925 : Blo 1116628 5821925 := bbase (se 4 (by rfl) ⟨545805, by rfl⟩ : syracuseStep 5821925 = 1091611) (by norm_num)
theorem B1889797 : Blo 1116628 1889797 := bbase (se 4 (by rfl) ⟨177168, by rfl⟩ : syracuseStep 1889797 = 354337) (by norm_num)
theorem B2512421 : Blo 1116628 2512421 := bbase (se 4 (by rfl) ⟨235539, by rfl⟩ : syracuseStep 2512421 = 471079) (by norm_num)
theorem B1889885 : Blo 1116628 1889885 := bbase (se 3 (by rfl) ⟨354353, by rfl⟩ : syracuseStep 1889885 = 708707) (by norm_num)
theorem B2512493 : Blo 1116628 2512493 := bbase (se 3 (by rfl) ⟨471092, by rfl⟩ : syracuseStep 2512493 = 942185) (by norm_num)
theorem B4249205 : Blo 1116628 4249205 := bbase (se 5 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 4249205 = 398363) (by norm_num)
theorem B2512565 : Blo 1116628 2512565 := bbase (se 5 (by rfl) ⟨117776, by rfl⟩ : syracuseStep 2512565 = 235553) (by norm_num)
theorem B1890013 : Blo 1116628 1890013 := bbase (se 3 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 1890013 = 708755) (by norm_num)
theorem B2512637 : Blo 1116628 2512637 := bbase (se 3 (by rfl) ⟨471119, by rfl⟩ : syracuseStep 2512637 = 942239) (by norm_num)
theorem B2152213 : Blo 1116628 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B1890101 : Blo 1116628 1890101 := bbase (se 5 (by rfl) ⟨88598, by rfl⟩ : syracuseStep 1890101 = 177197) (by norm_num)
theorem B2512709 : Blo 1116628 2512709 := bbase (se 4 (by rfl) ⟨235566, by rfl⟩ : syracuseStep 2512709 = 471133) (by norm_num)
theorem B2512781 : Blo 1116628 2512781 := bbase (se 3 (by rfl) ⟨471146, by rfl⟩ : syracuseStep 2512781 = 942293) (by norm_num)
theorem B4249493 : Blo 1116628 4249493 := bbase (se 6 (by rfl) ⟨99597, by rfl⟩ : syracuseStep 4249493 = 199195) (by norm_num)
theorem B1890229 : Blo 1116628 1890229 := bbase (se 5 (by rfl) ⟨88604, by rfl⟩ : syracuseStep 1890229 = 177209) (by norm_num)
theorem B2512853 : Blo 1116628 2512853 := bbase (se 7 (by rfl) ⟨29447, by rfl⟩ : syracuseStep 2512853 = 58895) (by norm_num)
theorem B3397621 : Blo 1116628 3397621 := bbase (se 5 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 3397621 = 318527) (by norm_num)
theorem B1890317 : Blo 1116628 1890317 := bbase (se 3 (by rfl) ⟨354434, by rfl⟩ : syracuseStep 1890317 = 708869) (by norm_num)
theorem B2512925 : Blo 1116628 2512925 := bbase (se 3 (by rfl) ⟨471173, by rfl⟩ : syracuseStep 2512925 = 942347) (by norm_num)
theorem B1595485 : Blo 1116628 1595485 := bbase (se 3 (by rfl) ⟨299153, by rfl⟩ : syracuseStep 1595485 = 598307) (by norm_num)
theorem B2512997 : Blo 1116628 2512997 := bbase (se 4 (by rfl) ⟨235593, by rfl⟩ : syracuseStep 2512997 = 471187) (by norm_num)
theorem B1890445 : Blo 1116628 1890445 := bbase (se 3 (by rfl) ⟨354458, by rfl⟩ : syracuseStep 1890445 = 708917) (by norm_num)
theorem B2513069 : Blo 1116628 2513069 := bbase (se 3 (by rfl) ⟨471200, by rfl⟩ : syracuseStep 2513069 = 942401) (by norm_num)
theorem B4774085 : Blo 1116628 4774085 := bbase (se 4 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 4774085 = 895141) (by norm_num)
theorem B5658821 : Blo 1116628 5658821 := bbase (se 4 (by rfl) ⟨530514, by rfl⟩ : syracuseStep 5658821 = 1061029) (by norm_num)
theorem B1890533 : Blo 1116628 1890533 := bbase (se 4 (by rfl) ⟨177237, by rfl⟩ : syracuseStep 1890533 = 354475) (by norm_num)
theorem B2119925 : Blo 1116628 2119925 := bbase (se 5 (by rfl) ⟨99371, by rfl⟩ : syracuseStep 2119925 = 198743) (by norm_num)
theorem B2513141 : Blo 1116628 2513141 := bbase (se 5 (by rfl) ⟨117803, by rfl⟩ : syracuseStep 2513141 = 235607) (by norm_num)
theorem B2513213 : Blo 1116628 2513213 := bbase (se 3 (by rfl) ⟨471227, by rfl⟩ : syracuseStep 2513213 = 942455) (by norm_num)
theorem B1890661 : Blo 1116628 1890661 := bbase (se 4 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 1890661 = 354499) (by norm_num)
theorem B2120069 : Blo 1116628 2120069 := bbase (se 4 (by rfl) ⟨198756, by rfl⟩ : syracuseStep 2120069 = 397513) (by norm_num)
theorem B2513285 : Blo 1116628 2513285 := bbase (se 4 (by rfl) ⟨235620, by rfl⟩ : syracuseStep 2513285 = 471241) (by norm_num)
theorem B1890749 : Blo 1116628 1890749 := bbase (se 3 (by rfl) ⟨354515, by rfl⟩ : syracuseStep 1890749 = 709031) (by norm_num)
theorem B2513357 : Blo 1116628 2513357 := bbase (se 3 (by rfl) ⟨471254, by rfl⟩ : syracuseStep 2513357 = 942509) (by norm_num)
theorem B2513429 : Blo 1116628 2513429 := bbase (se 6 (by rfl) ⟨58908, by rfl⟩ : syracuseStep 2513429 = 117817) (by norm_num)
theorem B1890877 : Blo 1116628 1890877 := bbase (se 3 (by rfl) ⟨354539, by rfl⟩ : syracuseStep 1890877 = 709079) (by norm_num)
theorem B6380117 : Blo 1116628 6380117 := bbase (se 8 (by rfl) ⟨37383, by rfl⟩ : syracuseStep 6380117 = 74767) (by norm_num)
theorem B2513501 : Blo 1116628 2513501 := bbase (se 3 (by rfl) ⟨471281, by rfl⟩ : syracuseStep 2513501 = 942563) (by norm_num)
theorem B1890965 : Blo 1116628 1890965 := bbase (se 6 (by rfl) ⟨44319, by rfl⟩ : syracuseStep 1890965 = 88639) (by norm_num)
theorem B2120357 : Blo 1116628 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B2513573 : Blo 1116628 2513573 := bbase (se 4 (by rfl) ⟨235647, by rfl⟩ : syracuseStep 2513573 = 471295) (by norm_num)
theorem B2513645 : Blo 1116628 2513645 := bbase (se 3 (by rfl) ⟨471308, by rfl⟩ : syracuseStep 2513645 = 942617) (by norm_num)
theorem B3824405 : Blo 1116628 3824405 := bbase (se 6 (by rfl) ⟨89634, by rfl⟩ : syracuseStep 3824405 = 179269) (by norm_num)
theorem B2513717 : Blo 1116628 2513717 := bbase (se 5 (by rfl) ⟨117830, by rfl⟩ : syracuseStep 2513717 = 235661) (by norm_num)
theorem B2120509 : Blo 1116628 2120509 := bbase (se 3 (by rfl) ⟨397595, by rfl⟩ : syracuseStep 2120509 = 795191) (by norm_num)
theorem B2513789 : Blo 1116628 2513789 := bbase (se 3 (by rfl) ⟨471335, by rfl⟩ : syracuseStep 2513789 = 942671) (by norm_num)
theorem B2513861 : Blo 1116628 2513861 := bbase (se 4 (by rfl) ⟨235674, by rfl⟩ : syracuseStep 2513861 = 471349) (by norm_num)
theorem B1792973 : Blo 1116628 1792973 := bbase (se 3 (by rfl) ⟨336182, by rfl⟩ : syracuseStep 1792973 = 672365) (by norm_num)
theorem B2513933 : Blo 1116628 2513933 := bbase (se 3 (by rfl) ⟨471362, by rfl⟩ : syracuseStep 2513933 = 942725) (by norm_num)
theorem B4250677 : Blo 1116628 4250677 := bbase (se 5 (by rfl) ⟨199250, by rfl⟩ : syracuseStep 4250677 = 398501) (by norm_num)
theorem B1793101 : Blo 1116628 1793101 := bbase (se 3 (by rfl) ⟨336206, by rfl⟩ : syracuseStep 1793101 = 672413) (by norm_num)
theorem B2514005 : Blo 1116628 2514005 := bbase (se 8 (by rfl) ⟨14730, by rfl⟩ : syracuseStep 2514005 = 29461) (by norm_num)
theorem B2120813 : Blo 1116628 2120813 := bbase (se 3 (by rfl) ⟨397652, by rfl⟩ : syracuseStep 2120813 = 795305) (by norm_num)
theorem B2514077 : Blo 1116628 2514077 := bbase (se 3 (by rfl) ⟨471389, by rfl⟩ : syracuseStep 2514077 = 942779) (by norm_num)
theorem B2514149 : Blo 1116628 2514149 := bbase (se 4 (by rfl) ⟨235701, by rfl⟩ : syracuseStep 2514149 = 471403) (by norm_num)
theorem B2514221 : Blo 1116628 2514221 := bbase (se 3 (by rfl) ⟨471416, by rfl⟩ : syracuseStep 2514221 = 942833) (by norm_num)
theorem B96722261 : Blo 1116628 96722261 := bbase (se 11 (by rfl) ⟨70841, by rfl⟩ : syracuseStep 96722261 = 141683) (by norm_num)
theorem B4250981 : Blo 1116628 4250981 := bbase (se 4 (by rfl) ⟨398529, by rfl⟩ : syracuseStep 4250981 = 797059) (by norm_num)
theorem B2514293 : Blo 1116628 2514293 := bbase (se 5 (by rfl) ⟨117857, by rfl⟩ : syracuseStep 2514293 = 235715) (by norm_num)
theorem B2514365 : Blo 1116628 2514365 := bbase (se 3 (by rfl) ⟨471443, by rfl⟩ : syracuseStep 2514365 = 942887) (by norm_num)
theorem B5660117 : Blo 1116628 5660117 := bbase (se 7 (by rfl) ⟨66329, by rfl⟩ : syracuseStep 5660117 = 132659) (by norm_num)
theorem B2514437 : Blo 1116628 2514437 := bbase (se 4 (by rfl) ⟨235728, by rfl⟩ : syracuseStep 2514437 = 471457) (by norm_num)
theorem B2514509 : Blo 1116628 2514509 := bbase (se 3 (by rfl) ⟨471470, by rfl⟩ : syracuseStep 2514509 = 942941) (by norm_num)
theorem B2514581 : Blo 1116628 2514581 := bbase (se 6 (by rfl) ⟨58935, by rfl⟩ : syracuseStep 2514581 = 117871) (by norm_num)
theorem B2514653 : Blo 1116628 2514653 := bbase (se 3 (by rfl) ⟨471497, by rfl⟩ : syracuseStep 2514653 = 942995) (by norm_num)
theorem B6381301 : Blo 1116628 6381301 := bbase (se 5 (by rfl) ⟨299123, by rfl⟩ : syracuseStep 6381301 = 598247) (by norm_num)
theorem B2514725 : Blo 1116628 2514725 := bbase (se 4 (by rfl) ⟨235755, by rfl⟩ : syracuseStep 2514725 = 471511) (by norm_num)
theorem B2121565 : Blo 1116628 2121565 := bbase (se 3 (by rfl) ⟨397793, by rfl⟩ : syracuseStep 2121565 = 795587) (by norm_num)
theorem B3628901 : Blo 1116628 3628901 := bbase (se 4 (by rfl) ⟨340209, by rfl⟩ : syracuseStep 3628901 = 680419) (by norm_num)
theorem B2514797 : Blo 1116628 2514797 := bbase (se 3 (by rfl) ⟨471524, by rfl⟩ : syracuseStep 2514797 = 943049) (by norm_num)
theorem B2514869 : Blo 1116628 2514869 := bbase (se 5 (by rfl) ⟨117884, by rfl⟩ : syracuseStep 2514869 = 235769) (by norm_num)
theorem B4775861 : Blo 1116628 4775861 := bbase (se 5 (by rfl) ⟨223868, by rfl⟩ : syracuseStep 4775861 = 447737) (by norm_num)
theorem B2121709 : Blo 1116628 2121709 := bbase (se 3 (by rfl) ⟨397820, by rfl⟩ : syracuseStep 2121709 = 795641) (by norm_num)
theorem B2514941 : Blo 1116628 2514941 := bbase (se 3 (by rfl) ⟨471551, by rfl⟩ : syracuseStep 2514941 = 943103) (by norm_num)
theorem B2515013 : Blo 1116628 2515013 := bbase (se 4 (by rfl) ⟨235782, by rfl⟩ : syracuseStep 2515013 = 471565) (by norm_num)
theorem B1531973 : Blo 1116628 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B2121869 : Blo 1116628 2121869 := bbase (se 3 (by rfl) ⟨397850, by rfl⟩ : syracuseStep 2121869 = 795701) (by norm_num)
theorem B2515085 : Blo 1116628 2515085 := bbase (se 3 (by rfl) ⟨471578, by rfl⟩ : syracuseStep 2515085 = 943157) (by norm_num)
theorem B2515157 : Blo 1116628 2515157 := bbase (se 7 (by rfl) ⟨29474, by rfl⟩ : syracuseStep 2515157 = 58949) (by norm_num)
theorem B1532125 : Blo 1116628 1532125 := bbase (se 3 (by rfl) ⟨287273, by rfl⟩ : syracuseStep 1532125 = 574547) (by norm_num)
theorem B8053013 : Blo 1116628 8053013 := bbase (se 6 (by rfl) ⟨188742, by rfl⟩ : syracuseStep 8053013 = 377485) (by norm_num)
theorem B2122013 : Blo 1116628 2122013 := bbase (se 3 (by rfl) ⟨397877, by rfl⟩ : syracuseStep 2122013 = 795755) (by norm_num)
theorem B2515229 : Blo 1116628 2515229 := bbase (se 3 (by rfl) ⟨471605, by rfl⟩ : syracuseStep 2515229 = 943211) (by norm_num)
theorem B2515301 : Blo 1116628 2515301 := bbase (se 4 (by rfl) ⟨235809, by rfl⟩ : syracuseStep 2515301 = 471619) (by norm_num)
theorem B2515373 : Blo 1116628 2515373 := bbase (se 3 (by rfl) ⟨471632, by rfl⟩ : syracuseStep 2515373 = 943265) (by norm_num)
theorem B1794485 : Blo 1116628 1794485 := bbase (se 5 (by rfl) ⟨84116, by rfl⟩ : syracuseStep 1794485 = 168233) (by norm_num)
theorem B2515445 : Blo 1116628 2515445 := bbase (se 5 (by rfl) ⟨117911, by rfl⟩ : syracuseStep 2515445 = 235823) (by norm_num)
theorem B13591061 : Blo 1116628 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B2122301 : Blo 1116628 2122301 := bbase (se 3 (by rfl) ⟨397931, by rfl⟩ : syracuseStep 2122301 = 795863) (by norm_num)
theorem B2515517 : Blo 1116628 2515517 := bbase (se 3 (by rfl) ⟨471659, by rfl⟩ : syracuseStep 2515517 = 943319) (by norm_num)
theorem B2515589 : Blo 1116628 2515589 := bbase (se 4 (by rfl) ⟨235836, by rfl⟩ : syracuseStep 2515589 = 471673) (by norm_num)
theorem B2515661 : Blo 1116628 2515661 := bbase (se 3 (by rfl) ⟨471686, by rfl⟩ : syracuseStep 2515661 = 943373) (by norm_num)
theorem B2122453 : Blo 1116628 2122453 := bbase (se 7 (by rfl) ⟨24872, by rfl⟩ : syracuseStep 2122453 = 49745) (by norm_num)
theorem B5661413 : Blo 1116628 5661413 := bbase (se 4 (by rfl) ⟨530757, by rfl⟩ : syracuseStep 5661413 = 1061515) (by norm_num)
theorem B2155261 : Blo 1116628 2155261 := bbase (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) (by norm_num)
theorem B2417413 : Blo 1116628 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B2515733 : Blo 1116628 2515733 := bbase (se 6 (by rfl) ⟨58962, by rfl⟩ : syracuseStep 2515733 = 117925) (by norm_num)
theorem B2515805 : Blo 1116628 2515805 := bbase (se 3 (by rfl) ⟨471713, by rfl⟩ : syracuseStep 2515805 = 943427) (by norm_num)
theorem B4776853 : Blo 1116628 4776853 := bbase (se 6 (by rfl) ⟨111957, by rfl⟩ : syracuseStep 4776853 = 223915) (by norm_num)
theorem B5366693 : Blo 1116628 5366693 := bbase (se 4 (by rfl) ⟨503127, by rfl⟩ : syracuseStep 5366693 = 1006255) (by norm_num)
theorem B2515877 : Blo 1116628 2515877 := bbase (se 4 (by rfl) ⟨235863, by rfl⟩ : syracuseStep 2515877 = 471727) (by norm_num)
theorem B2155477 : Blo 1116628 2155477 := bbase (se 7 (by rfl) ⟨25259, by rfl⟩ : syracuseStep 2155477 = 50519) (by norm_num)
theorem B2515949 : Blo 1116628 2515949 := bbase (se 3 (by rfl) ⟨471740, by rfl⟩ : syracuseStep 2515949 = 943481) (by norm_num)
theorem B2122757 : Blo 1116628 2122757 := bbase (se 4 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 2122757 = 398017) (by norm_num)
theorem B2548781 : Blo 1116628 2548781 := bbase (se 3 (by rfl) ⟨477896, by rfl⟩ : syracuseStep 2548781 = 955793) (by norm_num)
theorem B2516021 : Blo 1116628 2516021 := bbase (se 5 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 2516021 = 235877) (by norm_num)
theorem B2516093 : Blo 1116628 2516093 := bbase (se 3 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 2516093 = 943535) (by norm_num)
theorem B1434757 : Blo 1116628 1434757 := bbase (se 4 (by rfl) ⟨134508, by rfl⟩ : syracuseStep 1434757 = 269017) (by norm_num)
theorem B2516165 : Blo 1116628 2516165 := bbase (se 4 (by rfl) ⟨235890, by rfl⟩ : syracuseStep 2516165 = 471781) (by norm_num)
theorem B28697813 : Blo 1116628 28697813 := bbase (se 7 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 28697813 = 672605) (by norm_num)
theorem B2516237 : Blo 1116628 2516237 := bbase (se 3 (by rfl) ⟨471794, by rfl⟩ : syracuseStep 2516237 = 943589) (by norm_num)
theorem B2516309 : Blo 1116628 2516309 := bbase (se 12 (by rfl) ⟨921, by rfl⟩ : syracuseStep 2516309 = 1843) (by norm_num)
theorem B2516381 : Blo 1116628 2516381 := bbase (se 3 (by rfl) ⟨471821, by rfl⟩ : syracuseStep 2516381 = 943643) (by norm_num)
theorem B4253093 : Blo 1116628 4253093 := bbase (se 4 (by rfl) ⟨398727, by rfl⟩ : syracuseStep 4253093 = 797455) (by norm_num)
theorem B8480213 : Blo 1116628 8480213 := bbase (se 7 (by rfl) ⟨99377, by rfl⟩ : syracuseStep 8480213 = 198755) (by norm_num)
theorem B2516453 : Blo 1116628 2516453 := bbase (se 4 (by rfl) ⟨235917, by rfl⟩ : syracuseStep 2516453 = 471835) (by norm_num)
theorem B2549237 : Blo 1116628 2549237 := bbase (se 5 (by rfl) ⟨119495, by rfl⟩ : syracuseStep 2549237 = 238991) (by norm_num)
theorem B2516525 : Blo 1116628 2516525 := bbase (se 3 (by rfl) ⟨471848, by rfl⟩ : syracuseStep 2516525 = 943697) (by norm_num)
theorem B2418245 : Blo 1116628 2418245 := bbase (se 4 (by rfl) ⟨226710, by rfl⟩ : syracuseStep 2418245 = 453421) (by norm_num)
theorem B2516597 : Blo 1116628 2516597 := bbase (se 5 (by rfl) ⟨117965, by rfl⟩ : syracuseStep 2516597 = 235931) (by norm_num)
theorem B2516669 : Blo 1116628 2516669 := bbase (se 3 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 2516669 = 943751) (by norm_num)
theorem B4253381 : Blo 1116628 4253381 := bbase (se 4 (by rfl) ⟨398754, by rfl⟩ : syracuseStep 4253381 = 797509) (by norm_num)
theorem B2123509 : Blo 1116628 2123509 := bbase (se 5 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 2123509 = 199079) (by norm_num)
theorem B2516741 : Blo 1116628 2516741 := bbase (se 4 (by rfl) ⟨235944, by rfl⟩ : syracuseStep 2516741 = 471889) (by norm_num)
theorem B2516813 : Blo 1116628 2516813 := bbase (se 3 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 2516813 = 943805) (by norm_num)
theorem B2123653 : Blo 1116628 2123653 := bbase (se 4 (by rfl) ⟨199092, by rfl⟩ : syracuseStep 2123653 = 398185) (by norm_num)
theorem B2516885 : Blo 1116628 2516885 := bbase (se 6 (by rfl) ⟨58989, by rfl⟩ : syracuseStep 2516885 = 117979) (by norm_num)
theorem B2516957 : Blo 1116628 2516957 := bbase (se 3 (by rfl) ⟨471929, by rfl⟩ : syracuseStep 2516957 = 943859) (by norm_num)
theorem B5662709 : Blo 1116628 5662709 := bbase (se 5 (by rfl) ⟨265439, by rfl⟩ : syracuseStep 5662709 = 530879) (by norm_num)
theorem B1697813 : Blo 1116628 1697813 := bbase (se 6 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 1697813 = 79585) (by norm_num)
theorem B2385949 : Blo 1116628 2385949 := bbase (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) (by norm_num)
theorem B2517029 : Blo 1116628 2517029 := bbase (se 4 (by rfl) ⟨235971, by rfl⟩ : syracuseStep 2517029 = 471943) (by norm_num)
theorem B2123813 : Blo 1116628 2123813 := bbase (se 4 (by rfl) ⟨199107, by rfl⟩ : syracuseStep 2123813 = 398215) (by norm_num)
theorem B2418797 : Blo 1116628 2418797 := bbase (se 3 (by rfl) ⟨453524, by rfl⟩ : syracuseStep 2418797 = 907049) (by norm_num)
theorem B2517101 : Blo 1116628 2517101 := bbase (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) (by norm_num)
theorem B2517173 : Blo 1116628 2517173 := bbase (se 5 (by rfl) ⟨117992, by rfl⟩ : syracuseStep 2517173 = 235985) (by norm_num)
theorem B2123957 : Blo 1116628 2123957 := bbase (se 5 (by rfl) ⟨99560, by rfl⟩ : syracuseStep 2123957 = 199121) (by norm_num)
theorem B1435897 : Blo 1116628 1435897 := bbase (se 2 (by rfl) ⟨538461, by rfl⟩ : syracuseStep 1435897 = 1076923) (by norm_num)
theorem B2517245 : Blo 1116628 2517245 := bbase (se 3 (by rfl) ⟨471983, by rfl⟩ : syracuseStep 2517245 = 943967) (by norm_num)
theorem B6056213 : Blo 1116628 6056213 := bbase (se 6 (by rfl) ⟨141942, by rfl⟩ : syracuseStep 6056213 = 283885) (by norm_num)
theorem B2517317 : Blo 1116628 2517317 := bbase (se 4 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 2517317 = 471997) (by norm_num)
theorem B2517389 : Blo 1116628 2517389 := bbase (se 3 (by rfl) ⟨472010, by rfl⟩ : syracuseStep 2517389 = 944021) (by norm_num)
theorem B2517461 : Blo 1116628 2517461 := bbase (se 7 (by rfl) ⟨29501, by rfl⟩ : syracuseStep 2517461 = 59003) (by norm_num)
theorem B2124245 : Blo 1116628 2124245 := bbase (se 7 (by rfl) ⟨24893, by rfl⟩ : syracuseStep 2124245 = 49787) (by norm_num)
theorem B2517533 : Blo 1116628 2517533 := bbase (se 3 (by rfl) ⟨472037, by rfl⟩ : syracuseStep 2517533 = 944075) (by norm_num)
theorem B2517605 : Blo 1116628 2517605 := bbase (se 4 (by rfl) ⟨236025, by rfl⟩ : syracuseStep 2517605 = 472051) (by norm_num)
theorem B2124397 : Blo 1116628 2124397 := bbase (se 3 (by rfl) ⟨398324, by rfl⟩ : syracuseStep 2124397 = 796649) (by norm_num)
theorem B2517677 : Blo 1116628 2517677 := bbase (se 3 (by rfl) ⟨472064, by rfl⟩ : syracuseStep 2517677 = 944129) (by norm_num)
theorem B2517749 : Blo 1116628 2517749 := bbase (se 5 (by rfl) ⟨118019, by rfl⟩ : syracuseStep 2517749 = 236039) (by norm_num)
theorem B6810421 : Blo 1116628 6810421 := bbase (se 5 (by rfl) ⟨319238, by rfl⟩ : syracuseStep 6810421 = 638477) (by norm_num)
theorem B2517821 : Blo 1116628 2517821 := bbase (se 3 (by rfl) ⟨472091, by rfl⟩ : syracuseStep 2517821 = 944183) (by norm_num)
theorem B12741461 : Blo 1116628 12741461 := bbase (se 9 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 12741461 = 74657) (by norm_num)
theorem B4254565 : Blo 1116628 4254565 := bbase (se 4 (by rfl) ⟨398865, by rfl⟩ : syracuseStep 4254565 = 797731) (by norm_num)
theorem B5368693 : Blo 1116628 5368693 := bbase (se 5 (by rfl) ⟨251657, by rfl⟩ : syracuseStep 5368693 = 503315) (by norm_num)
theorem B2517893 : Blo 1116628 2517893 := bbase (se 4 (by rfl) ⟨236052, by rfl⟩ : syracuseStep 2517893 = 472105) (by norm_num)
theorem B2386837 : Blo 1116628 2386837 := bbase (se 6 (by rfl) ⟨55941, by rfl⟩ : syracuseStep 2386837 = 111883) (by norm_num)
theorem B2124701 : Blo 1116628 2124701 := bbase (se 3 (by rfl) ⟨398381, by rfl⟩ : syracuseStep 2124701 = 796763) (by norm_num)
theorem B2517965 : Blo 1116628 2517965 := bbase (se 3 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 2517965 = 944237) (by norm_num)
theorem B2518037 : Blo 1116628 2518037 := bbase (se 6 (by rfl) ⟨59016, by rfl⟩ : syracuseStep 2518037 = 118033) (by norm_num)
theorem B2518109 : Blo 1116628 2518109 := bbase (se 3 (by rfl) ⟨472145, by rfl⟩ : syracuseStep 2518109 = 944291) (by norm_num)
theorem B4254869 : Blo 1116628 4254869 := bbase (se 6 (by rfl) ⟨99723, by rfl⟩ : syracuseStep 4254869 = 199447) (by norm_num)
theorem B2518181 : Blo 1116628 2518181 := bbase (se 4 (by rfl) ⟨236079, by rfl⟩ : syracuseStep 2518181 = 472159) (by norm_num)
theorem B2518253 : Blo 1116628 2518253 := bbase (se 3 (by rfl) ⟨472172, by rfl⟩ : syracuseStep 2518253 = 944345) (by norm_num)
theorem B5664005 : Blo 1116628 5664005 := bbase (se 4 (by rfl) ⟨531000, by rfl⟩ : syracuseStep 5664005 = 1062001) (by norm_num)
theorem B2518325 : Blo 1116628 2518325 := bbase (se 5 (by rfl) ⟨118046, by rfl⟩ : syracuseStep 2518325 = 236093) (by norm_num)
theorem B2518397 : Blo 1116628 2518397 := bbase (se 3 (by rfl) ⟨472199, by rfl⟩ : syracuseStep 2518397 = 944399) (by norm_num)
theorem B2387333 : Blo 1116628 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B2518469 : Blo 1116628 2518469 := bbase (se 4 (by rfl) ⟨236106, by rfl⟩ : syracuseStep 2518469 = 472213) (by norm_num)
theorem B2518541 : Blo 1116628 2518541 := bbase (se 3 (by rfl) ⟨472226, by rfl⟩ : syracuseStep 2518541 = 944453) (by norm_num)
theorem B2518613 : Blo 1116628 2518613 := bbase (se 8 (by rfl) ⟨14757, by rfl⟩ : syracuseStep 2518613 = 29515) (by norm_num)
theorem B2125453 : Blo 1116628 2125453 := bbase (se 3 (by rfl) ⟨398522, by rfl⟩ : syracuseStep 2125453 = 797045) (by norm_num)
theorem B2518685 : Blo 1116628 2518685 := bbase (se 3 (by rfl) ⟨472253, by rfl⟩ : syracuseStep 2518685 = 944507) (by norm_num)
theorem B2518757 : Blo 1116628 2518757 := bbase (se 4 (by rfl) ⟨236133, by rfl⟩ : syracuseStep 2518757 = 472267) (by norm_num)
theorem B2125597 : Blo 1116628 2125597 := bbase (se 3 (by rfl) ⟨398549, by rfl⟩ : syracuseStep 2125597 = 797099) (by norm_num)
theorem B2518829 : Blo 1116628 2518829 := bbase (se 3 (by rfl) ⟨472280, by rfl⟩ : syracuseStep 2518829 = 944561) (by norm_num)
theorem B2518901 : Blo 1116628 2518901 := bbase (se 5 (by rfl) ⟨118073, by rfl⟩ : syracuseStep 2518901 = 236147) (by norm_num)
theorem B6123413 : Blo 1116628 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B2125757 : Blo 1116628 2125757 := bbase (se 3 (by rfl) ⟨398579, by rfl⟩ : syracuseStep 2125757 = 797159) (by norm_num)
theorem B2518973 : Blo 1116628 2518973 := bbase (se 3 (by rfl) ⟨472307, by rfl⟩ : syracuseStep 2518973 = 944615) (by norm_num)
theorem B2519045 : Blo 1116628 2519045 := bbase (se 4 (by rfl) ⟨236160, by rfl⟩ : syracuseStep 2519045 = 472321) (by norm_num)
theorem B2519117 : Blo 1116628 2519117 := bbase (se 3 (by rfl) ⟨472334, by rfl⟩ : syracuseStep 2519117 = 944669) (by norm_num)
theorem B2125901 : Blo 1116628 2125901 := bbase (se 3 (by rfl) ⟨398606, by rfl⟩ : syracuseStep 2125901 = 797213) (by norm_num)
theorem B6451285 : Blo 1116628 6451285 := bbase (se 8 (by rfl) ⟨37800, by rfl⟩ : syracuseStep 6451285 = 75601) (by norm_num)
theorem B1699949 : Blo 1116628 1699949 := bbase (se 3 (by rfl) ⟨318740, by rfl⟩ : syracuseStep 1699949 = 637481) (by norm_num)
theorem B2519189 : Blo 1116628 2519189 := bbase (se 6 (by rfl) ⟨59043, by rfl⟩ : syracuseStep 2519189 = 118087) (by norm_num)
theorem B2519261 : Blo 1116628 2519261 := bbase (se 3 (by rfl) ⟨472361, by rfl⟩ : syracuseStep 2519261 = 944723) (by norm_num)
theorem B2388197 : Blo 1116628 2388197 := bbase (se 4 (by rfl) ⟨223893, by rfl⟩ : syracuseStep 2388197 = 447787) (by norm_num)
theorem B2519333 : Blo 1116628 2519333 := bbase (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) (by norm_num)
theorem B2617661 : Blo 1116628 2617661 := bbase (se 3 (by rfl) ⟨490811, by rfl⟩ : syracuseStep 2617661 = 981623) (by norm_num)
theorem B4092245 : Blo 1116628 4092245 := bbase (se 10 (by rfl) ⟨5994, by rfl⟩ : syracuseStep 4092245 = 11989) (by norm_num)
theorem B2519405 : Blo 1116628 2519405 := bbase (se 3 (by rfl) ⟨472388, by rfl⟩ : syracuseStep 2519405 = 944777) (by norm_num)
theorem B2126189 : Blo 1116628 2126189 := bbase (se 3 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 2126189 = 797321) (by norm_num)
theorem B2388341 : Blo 1116628 2388341 := bbase (se 5 (by rfl) ⟨111953, by rfl⟩ : syracuseStep 2388341 = 223907) (by norm_num)
theorem B2683309 : Blo 1116628 2683309 := bbase (se 3 (by rfl) ⟨503120, by rfl⟩ : syracuseStep 2683309 = 1006241) (by norm_num)
theorem B2519477 : Blo 1116628 2519477 := bbase (se 5 (by rfl) ⟨118100, by rfl⟩ : syracuseStep 2519477 = 236201) (by norm_num)
theorem B2552285 : Blo 1116628 2552285 := bbase (se 3 (by rfl) ⟨478553, by rfl⟩ : syracuseStep 2552285 = 957107) (by norm_num)
theorem B2519549 : Blo 1116628 2519549 := bbase (se 3 (by rfl) ⟨472415, by rfl⟩ : syracuseStep 2519549 = 944831) (by norm_num)
theorem B2126341 : Blo 1116628 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B5665301 : Blo 1116628 5665301 := bbase (se 6 (by rfl) ⟨132780, by rfl⟩ : syracuseStep 5665301 = 265561) (by norm_num)
theorem B2519621 : Blo 1116628 2519621 := bbase (se 4 (by rfl) ⟨236214, by rfl⟩ : syracuseStep 2519621 = 472429) (by norm_num)
theorem B2519693 : Blo 1116628 2519693 := bbase (se 3 (by rfl) ⟨472442, by rfl⟩ : syracuseStep 2519693 = 944885) (by norm_num)
theorem B2552485 : Blo 1116628 2552485 := bbase (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) (by norm_num)
theorem B2519765 : Blo 1116628 2519765 := bbase (se 7 (by rfl) ⟨29528, by rfl⟩ : syracuseStep 2519765 = 59057) (by norm_num)
theorem B1700581 : Blo 1116628 1700581 := bbase (se 4 (by rfl) ⟨159429, by rfl⟩ : syracuseStep 1700581 = 318859) (by norm_num)
theorem B4027157 : Blo 1116628 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B2519837 : Blo 1116628 2519837 := bbase (se 3 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 2519837 = 944939) (by norm_num)
theorem B2126645 : Blo 1116628 2126645 := bbase (se 5 (by rfl) ⟨99686, by rfl⟩ : syracuseStep 2126645 = 199373) (by norm_num)
theorem B2519909 : Blo 1116628 2519909 := bbase (se 4 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 2519909 = 472483) (by norm_num)
theorem B2519981 : Blo 1116628 2519981 := bbase (se 3 (by rfl) ⟨472496, by rfl⟩ : syracuseStep 2519981 = 944993) (by norm_num)
theorem B2683829 : Blo 1116628 2683829 := bbase (se 5 (by rfl) ⟨125804, by rfl⟩ : syracuseStep 2683829 = 251609) (by norm_num)
theorem B2520053 : Blo 1116628 2520053 := bbase (se 5 (by rfl) ⟨118127, by rfl⟩ : syracuseStep 2520053 = 236255) (by norm_num)
theorem B2683925 : Blo 1116628 2683925 := bbase (se 6 (by rfl) ⟨62904, by rfl⟩ : syracuseStep 2683925 = 125809) (by norm_num)
theorem B4027429 : Blo 1116628 4027429 := bbase (se 4 (by rfl) ⟨377571, by rfl⟩ : syracuseStep 4027429 = 755143) (by norm_num)
theorem B2520125 : Blo 1116628 2520125 := bbase (se 3 (by rfl) ⟨472523, by rfl⟩ : syracuseStep 2520125 = 945047) (by norm_num)
theorem B2421829 : Blo 1116628 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B2389085 : Blo 1116628 2389085 := bbase (se 3 (by rfl) ⟨447953, by rfl⟩ : syracuseStep 2389085 = 895907) (by norm_num)
theorem B2520197 : Blo 1116628 2520197 := bbase (se 4 (by rfl) ⟨236268, by rfl⟩ : syracuseStep 2520197 = 472537) (by norm_num)
theorem B4027589 : Blo 1116628 4027589 := bbase (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) (by norm_num)
theorem B2520269 : Blo 1116628 2520269 := bbase (se 3 (by rfl) ⟨472550, by rfl⟩ : syracuseStep 2520269 = 945101) (by norm_num)
theorem B2520341 : Blo 1116628 2520341 := bbase (se 6 (by rfl) ⟨59070, by rfl⟩ : syracuseStep 2520341 = 118141) (by norm_num)
theorem B2520413 : Blo 1116628 2520413 := bbase (se 3 (by rfl) ⟨472577, by rfl⟩ : syracuseStep 2520413 = 945155) (by norm_num)
theorem B2520485 : Blo 1116628 2520485 := bbase (se 4 (by rfl) ⟨236295, by rfl⟩ : syracuseStep 2520485 = 472591) (by norm_num)
theorem B2520557 : Blo 1116628 2520557 := bbase (se 3 (by rfl) ⟨472604, by rfl⟩ : syracuseStep 2520557 = 945209) (by norm_num)
theorem B2127397 : Blo 1116628 2127397 := bbase (se 4 (by rfl) ⟨199443, by rfl⟩ : syracuseStep 2127397 = 398887) (by norm_num)
theorem B2520629 : Blo 1116628 2520629 := bbase (se 5 (by rfl) ⟨118154, by rfl⟩ : syracuseStep 2520629 = 236309) (by norm_num)
theorem B2586221 : Blo 1116628 2586221 := bbase (se 3 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 2586221 = 969833) (by norm_num)
theorem B2520701 : Blo 1116628 2520701 := bbase (se 3 (by rfl) ⟨472631, by rfl⟩ : syracuseStep 2520701 = 945263) (by norm_num)
theorem B1210009 : Blo 1116628 1210009 := bbase (se 2 (by rfl) ⟨453753, by rfl⟩ : syracuseStep 1210009 = 907507) (by norm_num)
theorem B2520773 : Blo 1116628 2520773 := bbase (se 4 (by rfl) ⟨236322, by rfl⟩ : syracuseStep 2520773 = 472645) (by norm_num)
theorem B2520845 : Blo 1116628 2520845 := bbase (se 3 (by rfl) ⟨472658, by rfl⟩ : syracuseStep 2520845 = 945317) (by norm_num)
theorem B5666597 : Blo 1116628 5666597 := bbase (se 4 (by rfl) ⟨531243, by rfl⟩ : syracuseStep 5666597 = 1062487) (by norm_num)
theorem B4781861 : Blo 1116628 4781861 := bbase (se 4 (by rfl) ⟨448299, by rfl⟩ : syracuseStep 4781861 = 896599) (by norm_num)
theorem B1275713 : Blo 1116628 1275713 := bbase (se 2 (by rfl) ⟨478392, by rfl⟩ : syracuseStep 1275713 = 956785) (by norm_num)
theorem B2389837 : Blo 1116628 2389837 := bbase (se 3 (by rfl) ⟨448094, by rfl⟩ : syracuseStep 2389837 = 896189) (by norm_num)
theorem B2520917 : Blo 1116628 2520917 := bbase (se 9 (by rfl) ⟨7385, by rfl⟩ : syracuseStep 2520917 = 14771) (by norm_num)
theorem B2520989 : Blo 1116628 2520989 := bbase (se 3 (by rfl) ⟨472685, by rfl⟩ : syracuseStep 2520989 = 945371) (by norm_num)
theorem B2389981 : Blo 1116628 2389981 := bbase (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) (by norm_num)
theorem B2521061 : Blo 1116628 2521061 := bbase (se 4 (by rfl) ⟨236349, by rfl⟩ : syracuseStep 2521061 = 472699) (by norm_num)
theorem B2521133 : Blo 1116628 2521133 := bbase (se 3 (by rfl) ⟨472712, by rfl⟩ : syracuseStep 2521133 = 945425) (by norm_num)
theorem B4782149 : Blo 1116628 4782149 := bbase (se 4 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 4782149 = 896653) (by norm_num)
theorem B2521205 : Blo 1116628 2521205 := bbase (se 5 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 2521205 = 236363) (by norm_num)
theorem B2521277 : Blo 1116628 2521277 := bbase (se 3 (by rfl) ⟨472739, by rfl⟩ : syracuseStep 2521277 = 945479) (by norm_num)
theorem B2521349 : Blo 1116628 2521349 := bbase (se 4 (by rfl) ⟨236376, by rfl⟩ : syracuseStep 2521349 = 472753) (by norm_num)
theorem B2685269 : Blo 1116628 2685269 := bbase (se 10 (by rfl) ⟨3933, by rfl⟩ : syracuseStep 2685269 = 7867) (by norm_num)
theorem B2390357 : Blo 1116628 2390357 := bbase (se 10 (by rfl) ⟨3501, by rfl⟩ : syracuseStep 2390357 = 7003) (by norm_num)
theorem B1702253 : Blo 1116628 1702253 := bbase (se 3 (by rfl) ⟨319172, by rfl⟩ : syracuseStep 1702253 = 638345) (by norm_num)
theorem B1702301 : Blo 1116628 1702301 := bbase (se 3 (by rfl) ⟨319181, by rfl⟩ : syracuseStep 1702301 = 638363) (by norm_num)
theorem B2390725 : Blo 1116628 2390725 := bbase (se 4 (by rfl) ⟨224130, by rfl⟩ : syracuseStep 2390725 = 448261) (by norm_num)
theorem B4782901 : Blo 1116628 4782901 := bbase (se 5 (by rfl) ⟨224198, by rfl⟩ : syracuseStep 4782901 = 448397) (by norm_num)
theorem B1342337 : Blo 1116628 1342337 := bbase (se 2 (by rfl) ⟨503376, by rfl⟩ : syracuseStep 1342337 = 1006753) (by norm_num)
theorem B5110661 : Blo 1116628 5110661 := bbase (se 4 (by rfl) ⟨479124, by rfl⟩ : syracuseStep 5110661 = 958249) (by norm_num)
theorem B8616917 : Blo 1116628 8616917 := bbase (se 7 (by rfl) ⟨100979, by rfl⟩ : syracuseStep 8616917 = 201959) (by norm_num)
theorem B5667893 : Blo 1116628 5667893 := bbase (se 5 (by rfl) ⟨265682, by rfl⟩ : syracuseStep 5667893 = 531365) (by norm_num)
theorem B2555077 : Blo 1116628 2555077 := bbase (se 4 (by rfl) ⟨239538, by rfl⟩ : syracuseStep 2555077 = 479077) (by norm_num)
theorem B1277137 : Blo 1116628 1277137 := bbase (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) (by norm_num)
theorem B1342693 : Blo 1116628 1342693 := bbase (se 4 (by rfl) ⟨125877, by rfl⟩ : syracuseStep 1342693 = 251755) (by norm_num)
theorem B1342885 : Blo 1116628 1342885 := bbase (se 4 (by rfl) ⟨125895, by rfl⟩ : syracuseStep 1342885 = 251791) (by norm_num)
theorem B4783637 : Blo 1116628 4783637 := bbase (se 6 (by rfl) ⟨112116, by rfl⟩ : syracuseStep 4783637 = 224233) (by norm_num)
theorem B1343029 : Blo 1116628 1343029 := bbase (se 5 (by rfl) ⟨62954, by rfl⟩ : syracuseStep 1343029 = 125909) (by norm_num)
theorem B5111429 : Blo 1116628 5111429 := bbase (se 4 (by rfl) ⟨479196, by rfl⟩ : syracuseStep 5111429 = 958393) (by norm_num)
theorem B9567989 : Blo 1116628 9567989 := bbase (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) (by norm_num)
theorem B1703797 : Blo 1116628 1703797 := bbase (se 5 (by rfl) ⟨79865, by rfl⟩ : syracuseStep 1703797 = 159731) (by norm_num)
theorem B4030357 : Blo 1116628 4030357 := bbase (se 6 (by rfl) ⟨94461, by rfl⟩ : syracuseStep 4030357 = 188923) (by norm_num)
theorem B4030499 : Blo 1116628 4030499 := bstep (se 1 (by rfl) ⟨3022874, by rfl⟩ : syracuseStep 4030499 = 6045749) B6045749
theorem B5669027 : Blo 1116628 5669027 := bstep (se 1 (by rfl) ⟨4251770, by rfl⟩ : syracuseStep 5669027 = 8503541) B8503541
theorem B1343731 : Blo 1116628 1343731 := bstep (se 1 (by rfl) ⟨1007798, by rfl⟩ : syracuseStep 1343731 = 2015597) B2015597
theorem B2687345 : Blo 1116628 2687345 := bstep (se 2 (by rfl) ⟨1007754, by rfl⟩ : syracuseStep 2687345 = 2015509) B2015509
theorem B1344019 : Blo 1116628 1344019 := bstep (se 1 (by rfl) ⟨1008014, by rfl⟩ : syracuseStep 1344019 = 2016029) B2016029
theorem B1344115 : Blo 1116628 1344115 := bstep (se 1 (by rfl) ⟨1008086, by rfl⟩ : syracuseStep 1344115 = 2016173) B2016173
theorem B3769037 : Blo 1116628 3769037 := bstep (se 3 (by rfl) ⟨706694, by rfl⟩ : syracuseStep 3769037 = 1413389) B1413389
theorem B3769091 : Blo 1116628 3769091 := bstep (se 1 (by rfl) ⟨2826818, by rfl⟩ : syracuseStep 3769091 = 5653637) B5653637
theorem B1344259 : Blo 1116628 1344259 := bstep (se 1 (by rfl) ⟨1008194, by rfl⟩ : syracuseStep 1344259 = 2016389) B2016389
theorem B2589475 : Blo 1116628 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B5669837 : Blo 1116628 5669837 := bstep (se 3 (by rfl) ⟨1063094, by rfl⟩ : syracuseStep 5669837 = 2126189) B2126189
theorem B9700337 : Blo 1116628 9700337 := bstep (se 2 (by rfl) ⟨3637626, by rfl⟩ : syracuseStep 9700337 = 7275253) B7275253
theorem B3769361 : Blo 1116628 3769361 := bstep (se 2 (by rfl) ⟨1413510, by rfl⟩ : syracuseStep 3769361 = 2827021) B2827021
theorem B4785293 : Blo 1116628 4785293 := bstep (se 3 (by rfl) ⟨897242, by rfl⟩ : syracuseStep 4785293 = 1794485) B1794485
theorem B5178595 : Blo 1116628 5178595 := bstep (se 1 (by rfl) ⟨3883946, by rfl⟩ : syracuseStep 5178595 = 7767893) B7767893
theorem B5375459 : Blo 1116628 5375459 := bstep (se 1 (by rfl) ⟨4031594, by rfl⟩ : syracuseStep 5375459 = 8063189) B8063189
theorem B4785635 : Blo 1116628 4785635 := bstep (se 1 (by rfl) ⟨3589226, by rfl⟩ : syracuseStep 4785635 = 7178453) B7178453
theorem B3180035 : Blo 1116628 3180035 := bstep (se 1 (by rfl) ⟨2385026, by rfl⟩ : syracuseStep 3180035 = 4770053) B4770053
theorem B3769901 : Blo 1116628 3769901 := bstep (se 3 (by rfl) ⟨706856, by rfl⟩ : syracuseStep 3769901 = 1413713) B1413713
theorem B3769955 : Blo 1116628 3769955 := bstep (se 1 (by rfl) ⟨2827466, by rfl⟩ : syracuseStep 3769955 = 5654933) B5654933
theorem B2688643 : Blo 1116628 2688643 := bstep (se 1 (by rfl) ⟨2016482, by rfl⟩ : syracuseStep 2688643 = 4032965) B4032965
theorem B3770225 : Blo 1116628 3770225 := bstep (se 2 (by rfl) ⟨1413834, by rfl⟩ : syracuseStep 3770225 = 2827669) B2827669
theorem B103254101 : Blo 1116628 103254101 := bstep (se 8 (by rfl) ⟨605004, by rfl⟩ : syracuseStep 103254101 = 1210009) B1210009
theorem B3770765 : Blo 1116628 3770765 := bstep (se 3 (by rfl) ⟨707018, by rfl⟩ : syracuseStep 3770765 = 1414037) B1414037
theorem B3770819 : Blo 1116628 3770819 := bstep (se 1 (by rfl) ⟨2828114, by rfl⟩ : syracuseStep 3770819 = 5656229) B5656229
theorem B1116643 : Blo 1116628 1116643 := bstep (se 1 (by rfl) ⟨837482, by rfl⟩ : syracuseStep 1116643 = 1674965) B1674965
theorem B1116659 : Blo 1116628 1116659 := bstep (se 1 (by rfl) ⟨837494, by rfl⟩ : syracuseStep 1116659 = 1674989) B1674989
theorem B1116675 : Blo 1116628 1116675 := bstep (se 1 (by rfl) ⟨837506, by rfl⟩ : syracuseStep 1116675 = 1675013) B1675013
theorem B1116691 : Blo 1116628 1116691 := bstep (se 1 (by rfl) ⟨837518, by rfl⟩ : syracuseStep 1116691 = 1675037) B1675037
theorem B1116707 : Blo 1116628 1116707 := bstep (se 1 (by rfl) ⟨837530, by rfl⟩ : syracuseStep 1116707 = 1675061) B1675061
theorem B1116723 : Blo 1116628 1116723 := bstep (se 1 (by rfl) ⟨837542, by rfl⟩ : syracuseStep 1116723 = 1675085) B1675085
theorem B1116739 : Blo 1116628 1116739 := bstep (se 1 (by rfl) ⟨837554, by rfl⟩ : syracuseStep 1116739 = 1675109) B1675109
theorem B1116755 : Blo 1116628 1116755 := bstep (se 1 (by rfl) ⟨837566, by rfl⟩ : syracuseStep 1116755 = 1675133) B1675133
theorem B1116771 : Blo 1116628 1116771 := bstep (se 1 (by rfl) ⟨837578, by rfl⟩ : syracuseStep 1116771 = 1675157) B1675157
theorem B1116787 : Blo 1116628 1116787 := bstep (se 1 (by rfl) ⟨837590, by rfl⟩ : syracuseStep 1116787 = 1675181) B1675181
theorem B1116803 : Blo 1116628 1116803 := bstep (se 1 (by rfl) ⟨837602, by rfl⟩ : syracuseStep 1116803 = 1675205) B1675205
theorem B1116819 : Blo 1116628 1116819 := bstep (se 1 (by rfl) ⟨837614, by rfl⟩ : syracuseStep 1116819 = 1675229) B1675229
theorem B1116835 : Blo 1116628 1116835 := bstep (se 1 (by rfl) ⟨837626, by rfl⟩ : syracuseStep 1116835 = 1675253) B1675253
theorem B5376689 : Blo 1116628 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B1116851 : Blo 1116628 1116851 := bstep (se 1 (by rfl) ⟨837638, by rfl⟩ : syracuseStep 1116851 = 1675277) B1675277
theorem B1116867 : Blo 1116628 1116867 := bstep (se 1 (by rfl) ⟨837650, by rfl⟩ : syracuseStep 1116867 = 1675301) B1675301
theorem B3181265 : Blo 1116628 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B3771089 : Blo 1116628 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B1116883 : Blo 1116628 1116883 := bstep (se 1 (by rfl) ⟨837662, by rfl⟩ : syracuseStep 1116883 = 1675325) B1675325
theorem B1116899 : Blo 1116628 1116899 := bstep (se 1 (by rfl) ⟨837674, by rfl⟩ : syracuseStep 1116899 = 1675349) B1675349
theorem B1116915 : Blo 1116628 1116915 := bstep (se 1 (by rfl) ⟨837686, by rfl⟩ : syracuseStep 1116915 = 1675373) B1675373
theorem B1116931 : Blo 1116628 1116931 := bstep (se 1 (by rfl) ⟨837698, by rfl⟩ : syracuseStep 1116931 = 1675397) B1675397
theorem B1116947 : Blo 1116628 1116947 := bstep (se 1 (by rfl) ⟨837710, by rfl⟩ : syracuseStep 1116947 = 1675421) B1675421
theorem B1116963 : Blo 1116628 1116963 := bstep (se 1 (by rfl) ⟨837722, by rfl⟩ : syracuseStep 1116963 = 1675445) B1675445
theorem B1116979 : Blo 1116628 1116979 := bstep (se 1 (by rfl) ⟨837734, by rfl⟩ : syracuseStep 1116979 = 1675469) B1675469
theorem B1116995 : Blo 1116628 1116995 := bstep (se 1 (by rfl) ⟨837746, by rfl⟩ : syracuseStep 1116995 = 1675493) B1675493
theorem B1117011 : Blo 1116628 1117011 := bstep (se 1 (by rfl) ⟨837758, by rfl⟩ : syracuseStep 1117011 = 1675517) B1675517
theorem B1117027 : Blo 1116628 1117027 := bstep (se 1 (by rfl) ⟨837770, by rfl⟩ : syracuseStep 1117027 = 1675541) B1675541
theorem B1117043 : Blo 1116628 1117043 := bstep (se 1 (by rfl) ⟨837782, by rfl⟩ : syracuseStep 1117043 = 1675565) B1675565
theorem B1117059 : Blo 1116628 1117059 := bstep (se 1 (by rfl) ⟨837794, by rfl⟩ : syracuseStep 1117059 = 1675589) B1675589
theorem B1117075 : Blo 1116628 1117075 := bstep (se 1 (by rfl) ⟨837806, by rfl⟩ : syracuseStep 1117075 = 1675613) B1675613
theorem B1117091 : Blo 1116628 1117091 := bstep (se 1 (by rfl) ⟨837818, by rfl⟩ : syracuseStep 1117091 = 1675637) B1675637
theorem B1117107 : Blo 1116628 1117107 := bstep (se 1 (by rfl) ⟨837830, by rfl⟩ : syracuseStep 1117107 = 1675661) B1675661
theorem B1117123 : Blo 1116628 1117123 := bstep (se 1 (by rfl) ⟨837842, by rfl⟩ : syracuseStep 1117123 = 1675685) B1675685
theorem B1117139 : Blo 1116628 1117139 := bstep (se 1 (by rfl) ⟨837854, by rfl⟩ : syracuseStep 1117139 = 1675709) B1675709
theorem B1117155 : Blo 1116628 1117155 := bstep (se 1 (by rfl) ⟨837866, by rfl⟩ : syracuseStep 1117155 = 1675733) B1675733
theorem B1117171 : Blo 1116628 1117171 := bstep (se 1 (by rfl) ⟨837878, by rfl⟩ : syracuseStep 1117171 = 1675757) B1675757
theorem B1117187 : Blo 1116628 1117187 := bstep (se 1 (by rfl) ⟨837890, by rfl⟩ : syracuseStep 1117187 = 1675781) B1675781
theorem B1117203 : Blo 1116628 1117203 := bstep (se 1 (by rfl) ⟨837902, by rfl⟩ : syracuseStep 1117203 = 1675805) B1675805
theorem B1117219 : Blo 1116628 1117219 := bstep (se 1 (by rfl) ⟨837914, by rfl⟩ : syracuseStep 1117219 = 1675829) B1675829
theorem B1117235 : Blo 1116628 1117235 := bstep (se 1 (by rfl) ⟨837926, by rfl⟩ : syracuseStep 1117235 = 1675853) B1675853
theorem B1117251 : Blo 1116628 1117251 := bstep (se 1 (by rfl) ⟨837938, by rfl⟩ : syracuseStep 1117251 = 1675877) B1675877
theorem B1117267 : Blo 1116628 1117267 := bstep (se 1 (by rfl) ⟨837950, by rfl⟩ : syracuseStep 1117267 = 1675901) B1675901
theorem B1117283 : Blo 1116628 1117283 := bstep (se 1 (by rfl) ⟨837962, by rfl⟩ : syracuseStep 1117283 = 1675925) B1675925
theorem B1117299 : Blo 1116628 1117299 := bstep (se 1 (by rfl) ⟨837974, by rfl⟩ : syracuseStep 1117299 = 1675949) B1675949
theorem B1117315 : Blo 1116628 1117315 := bstep (se 1 (by rfl) ⟨837986, by rfl⟩ : syracuseStep 1117315 = 1675973) B1675973
theorem B1117331 : Blo 1116628 1117331 := bstep (se 1 (by rfl) ⟨837998, by rfl⟩ : syracuseStep 1117331 = 1675997) B1675997
theorem B1117347 : Blo 1116628 1117347 := bstep (se 1 (by rfl) ⟨838010, by rfl⟩ : syracuseStep 1117347 = 1676021) B1676021
theorem B1117363 : Blo 1116628 1117363 := bstep (se 1 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 1117363 = 1676045) B1676045
theorem B1117379 : Blo 1116628 1117379 := bstep (se 1 (by rfl) ⟨838034, by rfl⟩ : syracuseStep 1117379 = 1676069) B1676069
theorem B1936595 : Blo 1116628 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B1117395 : Blo 1116628 1117395 := bstep (se 1 (by rfl) ⟨838046, by rfl⟩ : syracuseStep 1117395 = 1676093) B1676093
theorem B1117411 : Blo 1116628 1117411 := bstep (se 1 (by rfl) ⟨838058, by rfl⟩ : syracuseStep 1117411 = 1676117) B1676117
theorem B3771629 : Blo 1116628 3771629 := bstep (se 3 (by rfl) ⟨707180, by rfl⟩ : syracuseStep 3771629 = 1414361) B1414361
theorem B1117427 : Blo 1116628 1117427 := bstep (se 1 (by rfl) ⟨838070, by rfl⟩ : syracuseStep 1117427 = 1676141) B1676141
theorem B1117443 : Blo 1116628 1117443 := bstep (se 1 (by rfl) ⟨838082, by rfl⟩ : syracuseStep 1117443 = 1676165) B1676165
theorem B1117459 : Blo 1116628 1117459 := bstep (se 1 (by rfl) ⟨838094, by rfl⟩ : syracuseStep 1117459 = 1676189) B1676189
theorem B1117475 : Blo 1116628 1117475 := bstep (se 1 (by rfl) ⟨838106, by rfl⟩ : syracuseStep 1117475 = 1676213) B1676213
theorem B3771683 : Blo 1116628 3771683 := bstep (se 1 (by rfl) ⟨2828762, by rfl⟩ : syracuseStep 3771683 = 5657525) B5657525
theorem B1117491 : Blo 1116628 1117491 := bstep (se 1 (by rfl) ⟨838118, by rfl⟩ : syracuseStep 1117491 = 1676237) B1676237
theorem B1117507 : Blo 1116628 1117507 := bstep (se 1 (by rfl) ⟨838130, by rfl⟩ : syracuseStep 1117507 = 1676261) B1676261
theorem B6360389 : Blo 1116628 6360389 := bstep (se 4 (by rfl) ⟨596286, by rfl⟩ : syracuseStep 6360389 = 1192573) B1192573
theorem B1117523 : Blo 1116628 1117523 := bstep (se 1 (by rfl) ⟨838142, by rfl⟩ : syracuseStep 1117523 = 1676285) B1676285
theorem B1117539 : Blo 1116628 1117539 := bstep (se 1 (by rfl) ⟨838154, by rfl⟩ : syracuseStep 1117539 = 1676309) B1676309
theorem B1117555 : Blo 1116628 1117555 := bstep (se 1 (by rfl) ⟨838166, by rfl⟩ : syracuseStep 1117555 = 1676333) B1676333
theorem B1117571 : Blo 1116628 1117571 := bstep (se 1 (by rfl) ⟨838178, by rfl⟩ : syracuseStep 1117571 = 1676357) B1676357
theorem B1117587 : Blo 1116628 1117587 := bstep (se 1 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 1117587 = 1676381) B1676381
theorem B1117603 : Blo 1116628 1117603 := bstep (se 1 (by rfl) ⟨838202, by rfl⟩ : syracuseStep 1117603 = 1676405) B1676405
theorem B1117619 : Blo 1116628 1117619 := bstep (se 1 (by rfl) ⟨838214, by rfl⟩ : syracuseStep 1117619 = 1676429) B1676429
theorem B1117635 : Blo 1116628 1117635 := bstep (se 1 (by rfl) ⟨838226, by rfl⟩ : syracuseStep 1117635 = 1676453) B1676453
theorem B1117651 : Blo 1116628 1117651 := bstep (se 1 (by rfl) ⟨838238, by rfl⟩ : syracuseStep 1117651 = 1676477) B1676477
theorem B1117667 : Blo 1116628 1117667 := bstep (se 1 (by rfl) ⟨838250, by rfl⟩ : syracuseStep 1117667 = 1676501) B1676501
theorem B1117683 : Blo 1116628 1117683 := bstep (se 1 (by rfl) ⟨838262, by rfl⟩ : syracuseStep 1117683 = 1676525) B1676525
theorem B1117699 : Blo 1116628 1117699 := bstep (se 1 (by rfl) ⟨838274, by rfl⟩ : syracuseStep 1117699 = 1676549) B1676549
theorem B1117715 : Blo 1116628 1117715 := bstep (se 1 (by rfl) ⟨838286, by rfl⟩ : syracuseStep 1117715 = 1676573) B1676573
theorem B1117731 : Blo 1116628 1117731 := bstep (se 1 (by rfl) ⟨838298, by rfl⟩ : syracuseStep 1117731 = 1676597) B1676597
theorem B3771953 : Blo 1116628 3771953 := bstep (se 2 (by rfl) ⟨1414482, by rfl⟩ : syracuseStep 3771953 = 2828965) B2828965
theorem B1117747 : Blo 1116628 1117747 := bstep (se 1 (by rfl) ⟨838310, by rfl⟩ : syracuseStep 1117747 = 1676621) B1676621
theorem B1117763 : Blo 1116628 1117763 := bstep (se 1 (by rfl) ⟨838322, by rfl⟩ : syracuseStep 1117763 = 1676645) B1676645
theorem B1117779 : Blo 1116628 1117779 := bstep (se 1 (by rfl) ⟨838334, by rfl⟩ : syracuseStep 1117779 = 1676669) B1676669
theorem B1117795 : Blo 1116628 1117795 := bstep (se 1 (by rfl) ⟨838346, by rfl⟩ : syracuseStep 1117795 = 1676693) B1676693
theorem B4034161 : Blo 1116628 4034161 := bstep (se 2 (by rfl) ⟨1512810, by rfl⟩ : syracuseStep 4034161 = 3025621) B3025621
theorem B1117811 : Blo 1116628 1117811 := bstep (se 1 (by rfl) ⟨838358, by rfl⟩ : syracuseStep 1117811 = 1676717) B1676717
theorem B1117827 : Blo 1116628 1117827 := bstep (se 1 (by rfl) ⟨838370, by rfl⟩ : syracuseStep 1117827 = 1676741) B1676741
theorem B1117843 : Blo 1116628 1117843 := bstep (se 1 (by rfl) ⟨838382, by rfl⟩ : syracuseStep 1117843 = 1676765) B1676765
theorem B1117859 : Blo 1116628 1117859 := bstep (se 1 (by rfl) ⟨838394, by rfl⟩ : syracuseStep 1117859 = 1676789) B1676789
theorem B1117875 : Blo 1116628 1117875 := bstep (se 1 (by rfl) ⟨838406, by rfl⟩ : syracuseStep 1117875 = 1676813) B1676813
theorem B1674947 : Blo 1116628 1674947 := bstep (se 1 (by rfl) ⟨1256210, by rfl⟩ : syracuseStep 1674947 = 2512421) B2512421
theorem B1117891 : Blo 1116628 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B1117907 : Blo 1116628 1117907 := bstep (se 1 (by rfl) ⟨838430, by rfl⟩ : syracuseStep 1117907 = 1676861) B1676861
theorem B1674977 : Blo 1116628 1674977 := bstep (se 2 (by rfl) ⟨628116, by rfl⟩ : syracuseStep 1674977 = 1256233) B1256233
theorem B1117923 : Blo 1116628 1117923 := bstep (se 1 (by rfl) ⟨838442, by rfl⟩ : syracuseStep 1117923 = 1676885) B1676885
theorem B9080561 : Blo 1116628 9080561 := bstep (se 2 (by rfl) ⟨3405210, by rfl⟩ : syracuseStep 9080561 = 6810421) B6810421
theorem B1674995 : Blo 1116628 1674995 := bstep (se 1 (by rfl) ⟨1256246, by rfl⟩ : syracuseStep 1674995 = 2512493) B2512493
theorem B1117939 : Blo 1116628 1117939 := bstep (se 1 (by rfl) ⟨838454, by rfl⟩ : syracuseStep 1117939 = 1676909) B1676909
theorem B1117955 : Blo 1116628 1117955 := bstep (se 1 (by rfl) ⟨838466, by rfl⟩ : syracuseStep 1117955 = 1676933) B1676933
theorem B1675025 : Blo 1116628 1675025 := bstep (se 2 (by rfl) ⟨628134, by rfl⟩ : syracuseStep 1675025 = 1256269) B1256269
theorem B1117971 : Blo 1116628 1117971 := bstep (se 1 (by rfl) ⟨838478, by rfl⟩ : syracuseStep 1117971 = 1676957) B1676957
theorem B1675043 : Blo 1116628 1675043 := bstep (se 1 (by rfl) ⟨1256282, by rfl⟩ : syracuseStep 1675043 = 2512565) B2512565
theorem B1117987 : Blo 1116628 1117987 := bstep (se 1 (by rfl) ⟨838490, by rfl⟩ : syracuseStep 1117987 = 1676981) B1676981
theorem B5672753 : Blo 1116628 5672753 := bstep (se 2 (by rfl) ⟨2127282, by rfl⟩ : syracuseStep 5672753 = 4254565) B4254565
theorem B1118003 : Blo 1116628 1118003 := bstep (se 1 (by rfl) ⟨838502, by rfl⟩ : syracuseStep 1118003 = 1677005) B1677005
theorem B1675073 : Blo 1116628 1675073 := bstep (se 2 (by rfl) ⟨628152, by rfl⟩ : syracuseStep 1675073 = 1256305) B1256305
theorem B1118019 : Blo 1116628 1118019 := bstep (se 1 (by rfl) ⟨838514, by rfl⟩ : syracuseStep 1118019 = 1677029) B1677029
theorem B1675091 : Blo 1116628 1675091 := bstep (se 1 (by rfl) ⟨1256318, by rfl⟩ : syracuseStep 1675091 = 2512637) B2512637
theorem B1118035 : Blo 1116628 1118035 := bstep (se 1 (by rfl) ⟨838526, by rfl⟩ : syracuseStep 1118035 = 1677053) B1677053
theorem B1118051 : Blo 1116628 1118051 := bstep (se 1 (by rfl) ⟨838538, by rfl⟩ : syracuseStep 1118051 = 1677077) B1677077
theorem B1675121 : Blo 1116628 1675121 := bstep (se 2 (by rfl) ⟨628170, by rfl⟩ : syracuseStep 1675121 = 1256341) B1256341
theorem B1118067 : Blo 1116628 1118067 := bstep (se 1 (by rfl) ⟨838550, by rfl⟩ : syracuseStep 1118067 = 1677101) B1677101
theorem B1675139 : Blo 1116628 1675139 := bstep (se 1 (by rfl) ⟨1256354, by rfl⟩ : syracuseStep 1675139 = 2512709) B2512709
theorem B1118083 : Blo 1116628 1118083 := bstep (se 1 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 1118083 = 1677125) B1677125
theorem B1118099 : Blo 1116628 1118099 := bstep (se 1 (by rfl) ⟨838574, by rfl⟩ : syracuseStep 1118099 = 1677149) B1677149
theorem B1675169 : Blo 1116628 1675169 := bstep (se 2 (by rfl) ⟨628188, by rfl⟩ : syracuseStep 1675169 = 1256377) B1256377
theorem B1118115 : Blo 1116628 1118115 := bstep (se 1 (by rfl) ⟨838586, by rfl⟩ : syracuseStep 1118115 = 1677173) B1677173
theorem B1675187 : Blo 1116628 1675187 := bstep (se 1 (by rfl) ⟨1256390, by rfl⟩ : syracuseStep 1675187 = 2512781) B2512781
theorem B1118131 : Blo 1116628 1118131 := bstep (se 1 (by rfl) ⟨838598, by rfl⟩ : syracuseStep 1118131 = 1677197) B1677197
theorem B1118147 : Blo 1116628 1118147 := bstep (se 1 (by rfl) ⟨838610, by rfl⟩ : syracuseStep 1118147 = 1677221) B1677221
theorem B1675217 : Blo 1116628 1675217 := bstep (se 2 (by rfl) ⟨628206, by rfl⟩ : syracuseStep 1675217 = 1256413) B1256413
theorem B1118163 : Blo 1116628 1118163 := bstep (se 1 (by rfl) ⟨838622, by rfl⟩ : syracuseStep 1118163 = 1677245) B1677245
theorem B1675235 : Blo 1116628 1675235 := bstep (se 1 (by rfl) ⟨1256426, by rfl⟩ : syracuseStep 1675235 = 2512853) B2512853
theorem B1118179 : Blo 1116628 1118179 := bstep (se 1 (by rfl) ⟨838634, by rfl⟩ : syracuseStep 1118179 = 1677269) B1677269
theorem B1118195 : Blo 1116628 1118195 := bstep (se 1 (by rfl) ⟨838646, by rfl⟩ : syracuseStep 1118195 = 1677293) B1677293
theorem B1675265 : Blo 1116628 1675265 := bstep (se 2 (by rfl) ⟨628224, by rfl⟩ : syracuseStep 1675265 = 1256449) B1256449
theorem B1118211 : Blo 1116628 1118211 := bstep (se 1 (by rfl) ⟨838658, by rfl⟩ : syracuseStep 1118211 = 1677317) B1677317
theorem B1675283 : Blo 1116628 1675283 := bstep (se 1 (by rfl) ⟨1256462, by rfl⟩ : syracuseStep 1675283 = 2512925) B2512925
theorem B1118227 : Blo 1116628 1118227 := bstep (se 1 (by rfl) ⟨838670, by rfl⟩ : syracuseStep 1118227 = 1677341) B1677341
theorem B1118243 : Blo 1116628 1118243 := bstep (se 1 (by rfl) ⟨838682, by rfl⟩ : syracuseStep 1118243 = 1677365) B1677365
theorem B1675313 : Blo 1116628 1675313 := bstep (se 2 (by rfl) ⟨628242, by rfl⟩ : syracuseStep 1675313 = 1256485) B1256485
theorem B1118259 : Blo 1116628 1118259 := bstep (se 1 (by rfl) ⟨838694, by rfl⟩ : syracuseStep 1118259 = 1677389) B1677389
theorem B1675331 : Blo 1116628 1675331 := bstep (se 1 (by rfl) ⟨1256498, by rfl⟩ : syracuseStep 1675331 = 2512997) B2512997
theorem B1118275 : Blo 1116628 1118275 := bstep (se 1 (by rfl) ⟨838706, by rfl⟩ : syracuseStep 1118275 = 1677413) B1677413
theorem B3772493 : Blo 1116628 3772493 := bstep (se 3 (by rfl) ⟨707342, by rfl⟩ : syracuseStep 3772493 = 1414685) B1414685
theorem B1118291 : Blo 1116628 1118291 := bstep (se 1 (by rfl) ⟨838718, by rfl⟩ : syracuseStep 1118291 = 1677437) B1677437
theorem B1675361 : Blo 1116628 1675361 := bstep (se 2 (by rfl) ⟨628260, by rfl⟩ : syracuseStep 1675361 = 1256521) B1256521
theorem B1118307 : Blo 1116628 1118307 := bstep (se 1 (by rfl) ⟨838730, by rfl⟩ : syracuseStep 1118307 = 1677461) B1677461
theorem B1675379 : Blo 1116628 1675379 := bstep (se 1 (by rfl) ⟨1256534, by rfl⟩ : syracuseStep 1675379 = 2513069) B2513069
theorem B1118323 : Blo 1116628 1118323 := bstep (se 1 (by rfl) ⟨838742, by rfl⟩ : syracuseStep 1118323 = 1677485) B1677485
theorem B3182723 : Blo 1116628 3182723 := bstep (se 1 (by rfl) ⟨2387042, by rfl⟩ : syracuseStep 3182723 = 4774085) B4774085
theorem B3772547 : Blo 1116628 3772547 := bstep (se 1 (by rfl) ⟨2829410, by rfl⟩ : syracuseStep 3772547 = 5658821) B5658821
theorem B1118339 : Blo 1116628 1118339 := bstep (se 1 (by rfl) ⟨838754, by rfl⟩ : syracuseStep 1118339 = 1677509) B1677509
theorem B1675409 : Blo 1116628 1675409 := bstep (se 2 (by rfl) ⟨628278, by rfl⟩ : syracuseStep 1675409 = 1256557) B1256557
theorem B1118355 : Blo 1116628 1118355 := bstep (se 1 (by rfl) ⟨838766, by rfl⟩ : syracuseStep 1118355 = 1677533) B1677533
theorem B1413283 : Blo 1116628 1413283 := bstep (se 1 (by rfl) ⟨1059962, by rfl⟩ : syracuseStep 1413283 = 2119925) B2119925
theorem B1675427 : Blo 1116628 1675427 := bstep (se 1 (by rfl) ⟨1256570, by rfl⟩ : syracuseStep 1675427 = 2513141) B2513141
theorem B1118371 : Blo 1116628 1118371 := bstep (se 1 (by rfl) ⟨838778, by rfl⟩ : syracuseStep 1118371 = 1677557) B1677557
theorem B1118387 : Blo 1116628 1118387 := bstep (se 1 (by rfl) ⟨838790, by rfl⟩ : syracuseStep 1118387 = 1677581) B1677581
theorem B1675457 : Blo 1116628 1675457 := bstep (se 2 (by rfl) ⟨628296, by rfl⟩ : syracuseStep 1675457 = 1256593) B1256593
theorem B1118403 : Blo 1116628 1118403 := bstep (se 1 (by rfl) ⟨838802, by rfl⟩ : syracuseStep 1118403 = 1677605) B1677605
theorem B1675475 : Blo 1116628 1675475 := bstep (se 1 (by rfl) ⟨1256606, by rfl⟩ : syracuseStep 1675475 = 2513213) B2513213
theorem B1118419 : Blo 1116628 1118419 := bstep (se 1 (by rfl) ⟨838814, by rfl⟩ : syracuseStep 1118419 = 1677629) B1677629
theorem B1118435 : Blo 1116628 1118435 := bstep (se 1 (by rfl) ⟨838826, by rfl⟩ : syracuseStep 1118435 = 1677653) B1677653
theorem B1675505 : Blo 1116628 1675505 := bstep (se 2 (by rfl) ⟨628314, by rfl⟩ : syracuseStep 1675505 = 1256629) B1256629
theorem B1118451 : Blo 1116628 1118451 := bstep (se 1 (by rfl) ⟨838838, by rfl⟩ : syracuseStep 1118451 = 1677677) B1677677
theorem B1413379 : Blo 1116628 1413379 := bstep (se 1 (by rfl) ⟨1060034, by rfl⟩ : syracuseStep 1413379 = 2120069) B2120069
theorem B1675523 : Blo 1116628 1675523 := bstep (se 1 (by rfl) ⟨1256642, by rfl⟩ : syracuseStep 1675523 = 2513285) B2513285
theorem B1118467 : Blo 1116628 1118467 := bstep (se 1 (by rfl) ⟨838850, by rfl⟩ : syracuseStep 1118467 = 1677701) B1677701
theorem B1118483 : Blo 1116628 1118483 := bstep (se 1 (by rfl) ⟨838862, by rfl⟩ : syracuseStep 1118483 = 1677725) B1677725
theorem B1675553 : Blo 1116628 1675553 := bstep (se 2 (by rfl) ⟨628332, by rfl⟩ : syracuseStep 1675553 = 1256665) B1256665
theorem B1118499 : Blo 1116628 1118499 := bstep (se 1 (by rfl) ⟨838874, by rfl⟩ : syracuseStep 1118499 = 1677749) B1677749
theorem B1675571 : Blo 1116628 1675571 := bstep (se 1 (by rfl) ⟨1256678, by rfl⟩ : syracuseStep 1675571 = 2513357) B2513357
theorem B1118515 : Blo 1116628 1118515 := bstep (se 1 (by rfl) ⟨838886, by rfl⟩ : syracuseStep 1118515 = 1677773) B1677773
theorem B18157877 : Blo 1116628 18157877 := bstep (se 5 (by rfl) ⟨851150, by rfl⟩ : syracuseStep 18157877 = 1702301) B1702301
theorem B1118531 : Blo 1116628 1118531 := bstep (se 1 (by rfl) ⟨838898, by rfl⟩ : syracuseStep 1118531 = 1677797) B1677797
theorem B1675601 : Blo 1116628 1675601 := bstep (se 2 (by rfl) ⟨628350, by rfl⟩ : syracuseStep 1675601 = 1256701) B1256701
theorem B1118547 : Blo 1116628 1118547 := bstep (se 1 (by rfl) ⟨838910, by rfl⟩ : syracuseStep 1118547 = 1677821) B1677821
theorem B1675619 : Blo 1116628 1675619 := bstep (se 1 (by rfl) ⟨1256714, by rfl⟩ : syracuseStep 1675619 = 2513429) B2513429
theorem B1118563 : Blo 1116628 1118563 := bstep (se 1 (by rfl) ⟨838922, by rfl⟩ : syracuseStep 1118563 = 1677845) B1677845
theorem B1118579 : Blo 1116628 1118579 := bstep (se 1 (by rfl) ⟨838934, by rfl⟩ : syracuseStep 1118579 = 1677869) B1677869
theorem B1675649 : Blo 1116628 1675649 := bstep (se 2 (by rfl) ⟨628368, by rfl⟩ : syracuseStep 1675649 = 1256737) B1256737
theorem B1118595 : Blo 1116628 1118595 := bstep (se 1 (by rfl) ⟨838946, by rfl⟩ : syracuseStep 1118595 = 1677893) B1677893
theorem B3772817 : Blo 1116628 3772817 := bstep (se 2 (by rfl) ⟨1414806, by rfl⟩ : syracuseStep 3772817 = 2829613) B2829613
theorem B1675667 : Blo 1116628 1675667 := bstep (se 1 (by rfl) ⟨1256750, by rfl⟩ : syracuseStep 1675667 = 2513501) B2513501
theorem B1118611 : Blo 1116628 1118611 := bstep (se 1 (by rfl) ⟨838958, by rfl⟩ : syracuseStep 1118611 = 1677917) B1677917
theorem B1118627 : Blo 1116628 1118627 := bstep (se 1 (by rfl) ⟨838970, by rfl⟩ : syracuseStep 1118627 = 1677941) B1677941
theorem B1675697 : Blo 1116628 1675697 := bstep (se 2 (by rfl) ⟨628386, by rfl⟩ : syracuseStep 1675697 = 1256773) B1256773
theorem B1118643 : Blo 1116628 1118643 := bstep (se 1 (by rfl) ⟨838982, by rfl⟩ : syracuseStep 1118643 = 1677965) B1677965
theorem B1675715 : Blo 1116628 1675715 := bstep (se 1 (by rfl) ⟨1256786, by rfl⟩ : syracuseStep 1675715 = 2513573) B2513573
theorem B1118659 : Blo 1116628 1118659 := bstep (se 1 (by rfl) ⟨838994, by rfl⟩ : syracuseStep 1118659 = 1677989) B1677989
theorem B1118675 : Blo 1116628 1118675 := bstep (se 1 (by rfl) ⟨839006, by rfl⟩ : syracuseStep 1118675 = 1678013) B1678013
theorem B1675745 : Blo 1116628 1675745 := bstep (se 2 (by rfl) ⟨628404, by rfl⟩ : syracuseStep 1675745 = 1256809) B1256809
theorem B1118691 : Blo 1116628 1118691 := bstep (se 1 (by rfl) ⟨839018, by rfl⟩ : syracuseStep 1118691 = 1678037) B1678037
theorem B1675763 : Blo 1116628 1675763 := bstep (se 1 (by rfl) ⟨1256822, by rfl⟩ : syracuseStep 1675763 = 2513645) B2513645
theorem B1118707 : Blo 1116628 1118707 := bstep (se 1 (by rfl) ⟨839030, by rfl⟩ : syracuseStep 1118707 = 1678061) B1678061
theorem B1118723 : Blo 1116628 1118723 := bstep (se 1 (by rfl) ⟨839042, by rfl⟩ : syracuseStep 1118723 = 1678085) B1678085
theorem B1675793 : Blo 1116628 1675793 := bstep (se 2 (by rfl) ⟨628422, by rfl⟩ : syracuseStep 1675793 = 1256845) B1256845
theorem B1118739 : Blo 1116628 1118739 := bstep (se 1 (by rfl) ⟨839054, by rfl⟩ : syracuseStep 1118739 = 1678109) B1678109
theorem B1675811 : Blo 1116628 1675811 := bstep (se 1 (by rfl) ⟨1256858, by rfl⟩ : syracuseStep 1675811 = 2513717) B2513717
theorem B1118755 : Blo 1116628 1118755 := bstep (se 1 (by rfl) ⟨839066, by rfl⟩ : syracuseStep 1118755 = 1678133) B1678133
theorem B1118771 : Blo 1116628 1118771 := bstep (se 1 (by rfl) ⟨839078, by rfl⟩ : syracuseStep 1118771 = 1678157) B1678157
theorem B1675841 : Blo 1116628 1675841 := bstep (se 2 (by rfl) ⟨628440, by rfl⟩ : syracuseStep 1675841 = 1256881) B1256881
theorem B1118787 : Blo 1116628 1118787 := bstep (se 1 (by rfl) ⟨839090, by rfl⟩ : syracuseStep 1118787 = 1678181) B1678181
theorem B1675859 : Blo 1116628 1675859 := bstep (se 1 (by rfl) ⟨1256894, by rfl⟩ : syracuseStep 1675859 = 2513789) B2513789
theorem B1118803 : Blo 1116628 1118803 := bstep (se 1 (by rfl) ⟨839102, by rfl⟩ : syracuseStep 1118803 = 1678205) B1678205
theorem B1118819 : Blo 1116628 1118819 := bstep (se 1 (by rfl) ⟨839114, by rfl⟩ : syracuseStep 1118819 = 1678229) B1678229
theorem B1675889 : Blo 1116628 1675889 := bstep (se 2 (by rfl) ⟨628458, by rfl⟩ : syracuseStep 1675889 = 1256917) B1256917
theorem B1118835 : Blo 1116628 1118835 := bstep (se 1 (by rfl) ⟨839126, by rfl⟩ : syracuseStep 1118835 = 1678253) B1678253
theorem B1675907 : Blo 1116628 1675907 := bstep (se 1 (by rfl) ⟨1256930, by rfl⟩ : syracuseStep 1675907 = 2513861) B2513861
theorem B1118851 : Blo 1116628 1118851 := bstep (se 1 (by rfl) ⟨839138, by rfl⟩ : syracuseStep 1118851 = 1678277) B1678277
theorem B1118867 : Blo 1116628 1118867 := bstep (se 1 (by rfl) ⟨839150, by rfl⟩ : syracuseStep 1118867 = 1678301) B1678301
theorem B1675937 : Blo 1116628 1675937 := bstep (se 2 (by rfl) ⟨628476, by rfl⟩ : syracuseStep 1675937 = 1256953) B1256953
theorem B1118883 : Blo 1116628 1118883 := bstep (se 1 (by rfl) ⟨839162, by rfl⟩ : syracuseStep 1118883 = 1678325) B1678325
theorem B1675955 : Blo 1116628 1675955 := bstep (se 1 (by rfl) ⟨1256966, by rfl⟩ : syracuseStep 1675955 = 2513933) B2513933
theorem B1118899 : Blo 1116628 1118899 := bstep (se 1 (by rfl) ⟨839174, by rfl⟩ : syracuseStep 1118899 = 1678349) B1678349
theorem B1118915 : Blo 1116628 1118915 := bstep (se 1 (by rfl) ⟨839186, by rfl⟩ : syracuseStep 1118915 = 1678373) B1678373
theorem B1675985 : Blo 1116628 1675985 := bstep (se 2 (by rfl) ⟨628494, by rfl⟩ : syracuseStep 1675985 = 1256989) B1256989
theorem B1118931 : Blo 1116628 1118931 := bstep (se 1 (by rfl) ⟨839198, by rfl⟩ : syracuseStep 1118931 = 1678397) B1678397
theorem B1676003 : Blo 1116628 1676003 := bstep (se 1 (by rfl) ⟨1257002, by rfl⟩ : syracuseStep 1676003 = 2514005) B2514005
theorem B1118947 : Blo 1116628 1118947 := bstep (se 1 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 1118947 = 1678421) B1678421
theorem B1413875 : Blo 1116628 1413875 := bstep (se 1 (by rfl) ⟨1060406, by rfl⟩ : syracuseStep 1413875 = 2120813) B2120813
theorem B1118963 : Blo 1116628 1118963 := bstep (se 1 (by rfl) ⟨839222, by rfl⟩ : syracuseStep 1118963 = 1678445) B1678445
theorem B1676033 : Blo 1116628 1676033 := bstep (se 2 (by rfl) ⟨628512, by rfl⟩ : syracuseStep 1676033 = 1257025) B1257025
theorem B1118979 : Blo 1116628 1118979 := bstep (se 1 (by rfl) ⟨839234, by rfl⟩ : syracuseStep 1118979 = 1678469) B1678469
theorem B1676051 : Blo 1116628 1676051 := bstep (se 1 (by rfl) ⟨1257038, by rfl⟩ : syracuseStep 1676051 = 2514077) B2514077
theorem B1118995 : Blo 1116628 1118995 := bstep (se 1 (by rfl) ⟨839246, by rfl⟩ : syracuseStep 1118995 = 1678493) B1678493
theorem B1119011 : Blo 1116628 1119011 := bstep (se 1 (by rfl) ⟨839258, by rfl⟩ : syracuseStep 1119011 = 1678517) B1678517
theorem B1676081 : Blo 1116628 1676081 := bstep (se 2 (by rfl) ⟨628530, by rfl⟩ : syracuseStep 1676081 = 1257061) B1257061
theorem B1119027 : Blo 1116628 1119027 := bstep (se 1 (by rfl) ⟨839270, by rfl⟩ : syracuseStep 1119027 = 1678541) B1678541
theorem B1676099 : Blo 1116628 1676099 := bstep (se 1 (by rfl) ⟨1257074, by rfl⟩ : syracuseStep 1676099 = 2514149) B2514149
theorem B1119043 : Blo 1116628 1119043 := bstep (se 1 (by rfl) ⟨839282, by rfl⟩ : syracuseStep 1119043 = 1678565) B1678565
theorem B1119059 : Blo 1116628 1119059 := bstep (se 1 (by rfl) ⟨839294, by rfl⟩ : syracuseStep 1119059 = 1678589) B1678589
theorem B1676129 : Blo 1116628 1676129 := bstep (se 2 (by rfl) ⟨628548, by rfl⟩ : syracuseStep 1676129 = 1257097) B1257097
theorem B1119075 : Blo 1116628 1119075 := bstep (se 1 (by rfl) ⟨839306, by rfl⟩ : syracuseStep 1119075 = 1678613) B1678613
theorem B1676147 : Blo 1116628 1676147 := bstep (se 1 (by rfl) ⟨1257110, by rfl⟩ : syracuseStep 1676147 = 2514221) B2514221
theorem B1119091 : Blo 1116628 1119091 := bstep (se 1 (by rfl) ⟨839318, by rfl⟩ : syracuseStep 1119091 = 1678637) B1678637
theorem B1119107 : Blo 1116628 1119107 := bstep (se 1 (by rfl) ⟨839330, by rfl⟩ : syracuseStep 1119107 = 1678661) B1678661
theorem B1676177 : Blo 1116628 1676177 := bstep (se 2 (by rfl) ⟨628566, by rfl⟩ : syracuseStep 1676177 = 1257133) B1257133
theorem B1119123 : Blo 1116628 1119123 := bstep (se 1 (by rfl) ⟨839342, by rfl⟩ : syracuseStep 1119123 = 1678685) B1678685
theorem B1676195 : Blo 1116628 1676195 := bstep (se 1 (by rfl) ⟨1257146, by rfl⟩ : syracuseStep 1676195 = 2514293) B2514293
theorem B1119139 : Blo 1116628 1119139 := bstep (se 1 (by rfl) ⟨839354, by rfl⟩ : syracuseStep 1119139 = 1678709) B1678709
theorem B3183533 : Blo 1116628 3183533 := bstep (se 3 (by rfl) ⟨596912, by rfl⟩ : syracuseStep 3183533 = 1193825) B1193825
theorem B3773357 : Blo 1116628 3773357 := bstep (se 3 (by rfl) ⟨707504, by rfl⟩ : syracuseStep 3773357 = 1415009) B1415009
theorem B1119155 : Blo 1116628 1119155 := bstep (se 1 (by rfl) ⟨839366, by rfl⟩ : syracuseStep 1119155 = 1678733) B1678733
theorem B14554037 : Blo 1116628 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B1676225 : Blo 1116628 1676225 := bstep (se 2 (by rfl) ⟨628584, by rfl⟩ : syracuseStep 1676225 = 1257169) B1257169
theorem B1119171 : Blo 1116628 1119171 := bstep (se 1 (by rfl) ⟨839378, by rfl⟩ : syracuseStep 1119171 = 1678757) B1678757
theorem B1676243 : Blo 1116628 1676243 := bstep (se 1 (by rfl) ⟨1257182, by rfl⟩ : syracuseStep 1676243 = 2514365) B2514365
theorem B1119187 : Blo 1116628 1119187 := bstep (se 1 (by rfl) ⟨839390, by rfl⟩ : syracuseStep 1119187 = 1678781) B1678781
theorem B3773411 : Blo 1116628 3773411 := bstep (se 1 (by rfl) ⟨2830058, by rfl⟩ : syracuseStep 3773411 = 5660117) B5660117
theorem B1119203 : Blo 1116628 1119203 := bstep (se 1 (by rfl) ⟨839402, by rfl⟩ : syracuseStep 1119203 = 1678805) B1678805
theorem B1676273 : Blo 1116628 1676273 := bstep (se 2 (by rfl) ⟨628602, by rfl⟩ : syracuseStep 1676273 = 1257205) B1257205
theorem B1119219 : Blo 1116628 1119219 := bstep (se 1 (by rfl) ⟨839414, by rfl⟩ : syracuseStep 1119219 = 1678829) B1678829
theorem B1676291 : Blo 1116628 1676291 := bstep (se 1 (by rfl) ⟨1257218, by rfl⟩ : syracuseStep 1676291 = 2514437) B2514437
theorem B1119235 : Blo 1116628 1119235 := bstep (se 1 (by rfl) ⟨839426, by rfl⟩ : syracuseStep 1119235 = 1678853) B1678853
theorem B9573389 : Blo 1116628 9573389 := bstep (se 3 (by rfl) ⟨1795010, by rfl⟩ : syracuseStep 9573389 = 3590021) B3590021
theorem B1119251 : Blo 1116628 1119251 := bstep (se 1 (by rfl) ⟨839438, by rfl⟩ : syracuseStep 1119251 = 1678877) B1678877
theorem B1676321 : Blo 1116628 1676321 := bstep (se 2 (by rfl) ⟨628620, by rfl⟩ : syracuseStep 1676321 = 1257241) B1257241
theorem B1119267 : Blo 1116628 1119267 := bstep (se 1 (by rfl) ⟨839450, by rfl⟩ : syracuseStep 1119267 = 1678901) B1678901
theorem B1676339 : Blo 1116628 1676339 := bstep (se 1 (by rfl) ⟨1257254, by rfl⟩ : syracuseStep 1676339 = 2514509) B2514509
theorem B1119283 : Blo 1116628 1119283 := bstep (se 1 (by rfl) ⟨839462, by rfl⟩ : syracuseStep 1119283 = 1678925) B1678925
theorem B62100533 : Blo 1116628 62100533 := bstep (se 5 (by rfl) ⟨2910962, by rfl⟩ : syracuseStep 62100533 = 5821925) B5821925
theorem B1119299 : Blo 1116628 1119299 := bstep (se 1 (by rfl) ⟨839474, by rfl⟩ : syracuseStep 1119299 = 1678949) B1678949
theorem B5379149 : Blo 1116628 5379149 := bstep (se 3 (by rfl) ⟨1008590, by rfl⟩ : syracuseStep 5379149 = 2017181) B2017181
theorem B1676369 : Blo 1116628 1676369 := bstep (se 2 (by rfl) ⟨628638, by rfl⟩ : syracuseStep 1676369 = 1257277) B1257277
theorem B1119315 : Blo 1116628 1119315 := bstep (se 1 (by rfl) ⟨839486, by rfl⟩ : syracuseStep 1119315 = 1678973) B1678973
theorem B1676387 : Blo 1116628 1676387 := bstep (se 1 (by rfl) ⟨1257290, by rfl⟩ : syracuseStep 1676387 = 2514581) B2514581
theorem B1119331 : Blo 1116628 1119331 := bstep (se 1 (by rfl) ⟨839498, by rfl⟩ : syracuseStep 1119331 = 1678997) B1678997
theorem B3183725 : Blo 1116628 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B1119347 : Blo 1116628 1119347 := bstep (se 1 (by rfl) ⟨839510, by rfl⟩ : syracuseStep 1119347 = 1679021) B1679021
theorem B1676417 : Blo 1116628 1676417 := bstep (se 2 (by rfl) ⟨628656, by rfl⟩ : syracuseStep 1676417 = 1257313) B1257313
theorem B1119363 : Blo 1116628 1119363 := bstep (se 1 (by rfl) ⟨839522, by rfl⟩ : syracuseStep 1119363 = 1679045) B1679045
theorem B1676435 : Blo 1116628 1676435 := bstep (se 1 (by rfl) ⟨1257326, by rfl⟩ : syracuseStep 1676435 = 2514653) B2514653
theorem B1119379 : Blo 1116628 1119379 := bstep (se 1 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 1119379 = 1679069) B1679069
theorem B1119395 : Blo 1116628 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B1676465 : Blo 1116628 1676465 := bstep (se 2 (by rfl) ⟨628674, by rfl⟩ : syracuseStep 1676465 = 1257349) B1257349
theorem B1119411 : Blo 1116628 1119411 := bstep (se 1 (by rfl) ⟨839558, by rfl⟩ : syracuseStep 1119411 = 1679117) B1679117
theorem B1676483 : Blo 1116628 1676483 := bstep (se 1 (by rfl) ⟨1257362, by rfl⟩ : syracuseStep 1676483 = 2514725) B2514725
theorem B1119427 : Blo 1116628 1119427 := bstep (se 1 (by rfl) ⟨839570, by rfl⟩ : syracuseStep 1119427 = 1679141) B1679141
theorem B1119443 : Blo 1116628 1119443 := bstep (se 1 (by rfl) ⟨839582, by rfl⟩ : syracuseStep 1119443 = 1679165) B1679165
theorem B1676513 : Blo 1116628 1676513 := bstep (se 2 (by rfl) ⟨628692, by rfl⟩ : syracuseStep 1676513 = 1257385) B1257385
theorem B1119459 : Blo 1116628 1119459 := bstep (se 1 (by rfl) ⟨839594, by rfl⟩ : syracuseStep 1119459 = 1679189) B1679189
theorem B3773681 : Blo 1116628 3773681 := bstep (se 2 (by rfl) ⟨1415130, by rfl⟩ : syracuseStep 3773681 = 2830261) B2830261
theorem B1676531 : Blo 1116628 1676531 := bstep (se 1 (by rfl) ⟨1257398, by rfl⟩ : syracuseStep 1676531 = 2514797) B2514797
theorem B1119475 : Blo 1116628 1119475 := bstep (se 1 (by rfl) ⟨839606, by rfl⟩ : syracuseStep 1119475 = 1679213) B1679213
theorem B1119491 : Blo 1116628 1119491 := bstep (se 1 (by rfl) ⟨839618, by rfl⟩ : syracuseStep 1119491 = 1679237) B1679237
theorem B1676561 : Blo 1116628 1676561 := bstep (se 2 (by rfl) ⟨628710, by rfl⟩ : syracuseStep 1676561 = 1257421) B1257421
theorem B1119507 : Blo 1116628 1119507 := bstep (se 1 (by rfl) ⟨839630, by rfl⟩ : syracuseStep 1119507 = 1679261) B1679261
theorem B1676579 : Blo 1116628 1676579 := bstep (se 1 (by rfl) ⟨1257434, by rfl⟩ : syracuseStep 1676579 = 2514869) B2514869
theorem B1119523 : Blo 1116628 1119523 := bstep (se 1 (by rfl) ⟨839642, by rfl⟩ : syracuseStep 1119523 = 1679285) B1679285
theorem B1119539 : Blo 1116628 1119539 := bstep (se 1 (by rfl) ⟨839654, by rfl⟩ : syracuseStep 1119539 = 1679309) B1679309
theorem B1676609 : Blo 1116628 1676609 := bstep (se 2 (by rfl) ⟨628728, by rfl⟩ : syracuseStep 1676609 = 1257457) B1257457
theorem B1119555 : Blo 1116628 1119555 := bstep (se 1 (by rfl) ⟨839666, by rfl⟩ : syracuseStep 1119555 = 1679333) B1679333
theorem B1676627 : Blo 1116628 1676627 := bstep (se 1 (by rfl) ⟨1257470, by rfl⟩ : syracuseStep 1676627 = 2514941) B2514941
theorem B1119571 : Blo 1116628 1119571 := bstep (se 1 (by rfl) ⟨839678, by rfl⟩ : syracuseStep 1119571 = 1679357) B1679357
theorem B1119587 : Blo 1116628 1119587 := bstep (se 1 (by rfl) ⟨839690, by rfl⟩ : syracuseStep 1119587 = 1679381) B1679381
theorem B1676657 : Blo 1116628 1676657 := bstep (se 2 (by rfl) ⟨628746, by rfl⟩ : syracuseStep 1676657 = 1257493) B1257493
theorem B1119603 : Blo 1116628 1119603 := bstep (se 1 (by rfl) ⟨839702, by rfl⟩ : syracuseStep 1119603 = 1679405) B1679405
theorem B1676675 : Blo 1116628 1676675 := bstep (se 1 (by rfl) ⟨1257506, by rfl⟩ : syracuseStep 1676675 = 2515013) B2515013
theorem B1119619 : Blo 1116628 1119619 := bstep (se 1 (by rfl) ⟨839714, by rfl⟩ : syracuseStep 1119619 = 1679429) B1679429
theorem B1119635 : Blo 1116628 1119635 := bstep (se 1 (by rfl) ⟨839726, by rfl⟩ : syracuseStep 1119635 = 1679453) B1679453
theorem B1676705 : Blo 1116628 1676705 := bstep (se 2 (by rfl) ⟨628764, by rfl⟩ : syracuseStep 1676705 = 1257529) B1257529
theorem B1119651 : Blo 1116628 1119651 := bstep (se 1 (by rfl) ⟨839738, by rfl⟩ : syracuseStep 1119651 = 1679477) B1679477
theorem B1414579 : Blo 1116628 1414579 := bstep (se 1 (by rfl) ⟨1060934, by rfl⟩ : syracuseStep 1414579 = 2121869) B2121869
theorem B1676723 : Blo 1116628 1676723 := bstep (se 1 (by rfl) ⟨1257542, by rfl⟩ : syracuseStep 1676723 = 2515085) B2515085
theorem B1119667 : Blo 1116628 1119667 := bstep (se 1 (by rfl) ⟨839750, by rfl⟩ : syracuseStep 1119667 = 1679501) B1679501
theorem B1119683 : Blo 1116628 1119683 := bstep (se 1 (by rfl) ⟨839762, by rfl⟩ : syracuseStep 1119683 = 1679525) B1679525
theorem B9541061 : Blo 1116628 9541061 := bstep (se 4 (by rfl) ⟨894474, by rfl⟩ : syracuseStep 9541061 = 1788949) B1788949
theorem B1676753 : Blo 1116628 1676753 := bstep (se 2 (by rfl) ⟨628782, by rfl⟩ : syracuseStep 1676753 = 1257565) B1257565
theorem B1119699 : Blo 1116628 1119699 := bstep (se 1 (by rfl) ⟨839774, by rfl⟩ : syracuseStep 1119699 = 1679549) B1679549
theorem B1676771 : Blo 1116628 1676771 := bstep (se 1 (by rfl) ⟨1257578, by rfl⟩ : syracuseStep 1676771 = 2515157) B2515157
theorem B1119715 : Blo 1116628 1119715 := bstep (se 1 (by rfl) ⟨839786, by rfl⟩ : syracuseStep 1119715 = 1679573) B1679573
theorem B1119731 : Blo 1116628 1119731 := bstep (se 1 (by rfl) ⟨839798, by rfl⟩ : syracuseStep 1119731 = 1679597) B1679597
theorem B1676801 : Blo 1116628 1676801 := bstep (se 2 (by rfl) ⟨628800, by rfl⟩ : syracuseStep 1676801 = 1257601) B1257601
theorem B1119747 : Blo 1116628 1119747 := bstep (se 1 (by rfl) ⟨839810, by rfl⟩ : syracuseStep 1119747 = 1679621) B1679621
theorem B1414675 : Blo 1116628 1414675 := bstep (se 1 (by rfl) ⟨1061006, by rfl⟩ : syracuseStep 1414675 = 2122013) B2122013
theorem B1676819 : Blo 1116628 1676819 := bstep (se 1 (by rfl) ⟨1257614, by rfl⟩ : syracuseStep 1676819 = 2515229) B2515229
theorem B1119763 : Blo 1116628 1119763 := bstep (se 1 (by rfl) ⟨839822, by rfl⟩ : syracuseStep 1119763 = 1679645) B1679645
theorem B3020323 : Blo 1116628 3020323 := bstep (se 1 (by rfl) ⟨2265242, by rfl⟩ : syracuseStep 3020323 = 4530485) B4530485
theorem B1119779 : Blo 1116628 1119779 := bstep (se 1 (by rfl) ⟨839834, by rfl⟩ : syracuseStep 1119779 = 1679669) B1679669
theorem B1676849 : Blo 1116628 1676849 := bstep (se 2 (by rfl) ⟨628818, by rfl⟩ : syracuseStep 1676849 = 1257637) B1257637
theorem B1119795 : Blo 1116628 1119795 := bstep (se 1 (by rfl) ⟨839846, by rfl⟩ : syracuseStep 1119795 = 1679693) B1679693
theorem B1676867 : Blo 1116628 1676867 := bstep (se 1 (by rfl) ⟨1257650, by rfl⟩ : syracuseStep 1676867 = 2515301) B2515301
theorem B1119811 : Blo 1116628 1119811 := bstep (se 1 (by rfl) ⟨839858, by rfl⟩ : syracuseStep 1119811 = 1679717) B1679717
theorem B1119827 : Blo 1116628 1119827 := bstep (se 1 (by rfl) ⟨839870, by rfl⟩ : syracuseStep 1119827 = 1679741) B1679741
theorem B1676897 : Blo 1116628 1676897 := bstep (se 2 (by rfl) ⟨628836, by rfl⟩ : syracuseStep 1676897 = 1257673) B1257673
theorem B1119843 : Blo 1116628 1119843 := bstep (se 1 (by rfl) ⟨839882, by rfl⟩ : syracuseStep 1119843 = 1679765) B1679765
theorem B1676915 : Blo 1116628 1676915 := bstep (se 1 (by rfl) ⟨1257686, by rfl⟩ : syracuseStep 1676915 = 2515373) B2515373
theorem B1119859 : Blo 1116628 1119859 := bstep (se 1 (by rfl) ⟨839894, by rfl⟩ : syracuseStep 1119859 = 1679789) B1679789
theorem B1119875 : Blo 1116628 1119875 := bstep (se 1 (by rfl) ⟨839906, by rfl⟩ : syracuseStep 1119875 = 1679813) B1679813
theorem B1676945 : Blo 1116628 1676945 := bstep (se 2 (by rfl) ⟨628854, by rfl⟩ : syracuseStep 1676945 = 1257709) B1257709
theorem B1119891 : Blo 1116628 1119891 := bstep (se 1 (by rfl) ⟨839918, by rfl⟩ : syracuseStep 1119891 = 1679837) B1679837
theorem B1676963 : Blo 1116628 1676963 := bstep (se 1 (by rfl) ⟨1257722, by rfl⟩ : syracuseStep 1676963 = 2515445) B2515445
theorem B1119907 : Blo 1116628 1119907 := bstep (se 1 (by rfl) ⟨839930, by rfl⟩ : syracuseStep 1119907 = 1679861) B1679861
theorem B1119923 : Blo 1116628 1119923 := bstep (se 1 (by rfl) ⟨839942, by rfl⟩ : syracuseStep 1119923 = 1679885) B1679885
theorem B1676993 : Blo 1116628 1676993 := bstep (se 2 (by rfl) ⟨628872, by rfl⟩ : syracuseStep 1676993 = 1257745) B1257745
theorem B1119939 : Blo 1116628 1119939 := bstep (se 1 (by rfl) ⟨839954, by rfl⟩ : syracuseStep 1119939 = 1679909) B1679909
theorem B12916421 : Blo 1116628 12916421 := bstep (se 4 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 12916421 = 2421829) B2421829
theorem B1677011 : Blo 1116628 1677011 := bstep (se 1 (by rfl) ⟨1257758, by rfl⟩ : syracuseStep 1677011 = 2515517) B2515517
theorem B1119955 : Blo 1116628 1119955 := bstep (se 1 (by rfl) ⟨839966, by rfl⟩ : syracuseStep 1119955 = 1679933) B1679933
theorem B1119971 : Blo 1116628 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B1677041 : Blo 1116628 1677041 := bstep (se 2 (by rfl) ⟨628890, by rfl⟩ : syracuseStep 1677041 = 1257781) B1257781
theorem B1119987 : Blo 1116628 1119987 := bstep (se 1 (by rfl) ⟨839990, by rfl⟩ : syracuseStep 1119987 = 1679981) B1679981
theorem B1677059 : Blo 1116628 1677059 := bstep (se 1 (by rfl) ⟨1257794, by rfl⟩ : syracuseStep 1677059 = 2515589) B2515589
theorem B1120003 : Blo 1116628 1120003 := bstep (se 1 (by rfl) ⟨840002, by rfl⟩ : syracuseStep 1120003 = 1680005) B1680005
theorem B3774221 : Blo 1116628 3774221 := bstep (se 3 (by rfl) ⟨707666, by rfl⟩ : syracuseStep 3774221 = 1415333) B1415333
theorem B1120019 : Blo 1116628 1120019 := bstep (se 1 (by rfl) ⟨840014, by rfl⟩ : syracuseStep 1120019 = 1680029) B1680029
theorem B45913877 : Blo 1116628 45913877 := bstep (se 6 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 45913877 = 2152213) B2152213
theorem B1677089 : Blo 1116628 1677089 := bstep (se 2 (by rfl) ⟨628908, by rfl⟩ : syracuseStep 1677089 = 1257817) B1257817
theorem B1120035 : Blo 1116628 1120035 := bstep (se 1 (by rfl) ⟨840026, by rfl⟩ : syracuseStep 1120035 = 1680053) B1680053
theorem B1677107 : Blo 1116628 1677107 := bstep (se 1 (by rfl) ⟨1257830, by rfl⟩ : syracuseStep 1677107 = 2515661) B2515661
theorem B1120051 : Blo 1116628 1120051 := bstep (se 1 (by rfl) ⟨840038, by rfl⟩ : syracuseStep 1120051 = 1680077) B1680077
theorem B3774275 : Blo 1116628 3774275 := bstep (se 1 (by rfl) ⟨2830706, by rfl⟩ : syracuseStep 3774275 = 5661413) B5661413
theorem B1120067 : Blo 1116628 1120067 := bstep (se 1 (by rfl) ⟨840050, by rfl⟩ : syracuseStep 1120067 = 1680101) B1680101
theorem B1677137 : Blo 1116628 1677137 := bstep (se 2 (by rfl) ⟨628926, by rfl⟩ : syracuseStep 1677137 = 1257853) B1257853
theorem B1120083 : Blo 1116628 1120083 := bstep (se 1 (by rfl) ⟨840062, by rfl⟩ : syracuseStep 1120083 = 1680125) B1680125
theorem B1677155 : Blo 1116628 1677155 := bstep (se 1 (by rfl) ⟨1257866, by rfl⟩ : syracuseStep 1677155 = 2515733) B2515733
theorem B1120099 : Blo 1116628 1120099 := bstep (se 1 (by rfl) ⟨840074, by rfl⟩ : syracuseStep 1120099 = 1680149) B1680149
theorem B1120115 : Blo 1116628 1120115 := bstep (se 1 (by rfl) ⟨840086, by rfl⟩ : syracuseStep 1120115 = 1680173) B1680173
theorem B1677185 : Blo 1116628 1677185 := bstep (se 2 (by rfl) ⟨628944, by rfl⟩ : syracuseStep 1677185 = 1257889) B1257889
theorem B1120131 : Blo 1116628 1120131 := bstep (se 1 (by rfl) ⟨840098, by rfl⟩ : syracuseStep 1120131 = 1680197) B1680197
theorem B3577745 : Blo 1116628 3577745 := bstep (se 2 (by rfl) ⟨1341654, by rfl⟩ : syracuseStep 3577745 = 2683309) B2683309
theorem B1677203 : Blo 1116628 1677203 := bstep (se 1 (by rfl) ⟨1257902, by rfl⟩ : syracuseStep 1677203 = 2515805) B2515805
theorem B1120147 : Blo 1116628 1120147 := bstep (se 1 (by rfl) ⟨840110, by rfl⟩ : syracuseStep 1120147 = 1680221) B1680221
theorem B1120163 : Blo 1116628 1120163 := bstep (se 1 (by rfl) ⟨840122, by rfl⟩ : syracuseStep 1120163 = 1680245) B1680245
theorem B1677233 : Blo 1116628 1677233 := bstep (se 2 (by rfl) ⟨628962, by rfl⟩ : syracuseStep 1677233 = 1257925) B1257925
theorem B5740465 : Blo 1116628 5740465 := bstep (se 2 (by rfl) ⟨2152674, by rfl⟩ : syracuseStep 5740465 = 4305349) B4305349
theorem B1120179 : Blo 1116628 1120179 := bstep (se 1 (by rfl) ⟨840134, by rfl⟩ : syracuseStep 1120179 = 1680269) B1680269
theorem B1677251 : Blo 1116628 1677251 := bstep (se 1 (by rfl) ⟨1257938, by rfl⟩ : syracuseStep 1677251 = 2515877) B2515877
theorem B1120195 : Blo 1116628 1120195 := bstep (se 1 (by rfl) ⟨840146, by rfl⟩ : syracuseStep 1120195 = 1680293) B1680293
theorem B1120211 : Blo 1116628 1120211 := bstep (se 1 (by rfl) ⟨840158, by rfl⟩ : syracuseStep 1120211 = 1680317) B1680317
theorem B1677281 : Blo 1116628 1677281 := bstep (se 2 (by rfl) ⟨628980, by rfl⟩ : syracuseStep 1677281 = 1257961) B1257961
theorem B1120227 : Blo 1116628 1120227 := bstep (se 1 (by rfl) ⟨840170, by rfl⟩ : syracuseStep 1120227 = 1680341) B1680341
theorem B1677299 : Blo 1116628 1677299 := bstep (se 1 (by rfl) ⟨1257974, by rfl⟩ : syracuseStep 1677299 = 2515949) B2515949
theorem B1120243 : Blo 1116628 1120243 := bstep (se 1 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 1120243 = 1680365) B1680365
theorem B1415171 : Blo 1116628 1415171 := bstep (se 1 (by rfl) ⟨1061378, by rfl⟩ : syracuseStep 1415171 = 2122757) B2122757
theorem B1120259 : Blo 1116628 1120259 := bstep (se 1 (by rfl) ⟨840194, by rfl⟩ : syracuseStep 1120259 = 1680389) B1680389
theorem B1677329 : Blo 1116628 1677329 := bstep (se 2 (by rfl) ⟨628998, by rfl⟩ : syracuseStep 1677329 = 1257997) B1257997
theorem B1120275 : Blo 1116628 1120275 := bstep (se 1 (by rfl) ⟨840206, by rfl⟩ : syracuseStep 1120275 = 1680413) B1680413
theorem B1677347 : Blo 1116628 1677347 := bstep (se 1 (by rfl) ⟨1258010, by rfl⟩ : syracuseStep 1677347 = 2516021) B2516021
theorem B1120291 : Blo 1116628 1120291 := bstep (se 1 (by rfl) ⟨840218, by rfl⟩ : syracuseStep 1120291 = 1680437) B1680437
theorem B1120307 : Blo 1116628 1120307 := bstep (se 1 (by rfl) ⟨840230, by rfl⟩ : syracuseStep 1120307 = 1680461) B1680461
theorem B1677377 : Blo 1116628 1677377 := bstep (se 2 (by rfl) ⟨629016, by rfl⟩ : syracuseStep 1677377 = 1258033) B1258033
theorem B1120323 : Blo 1116628 1120323 := bstep (se 1 (by rfl) ⟨840242, by rfl⟩ : syracuseStep 1120323 = 1680485) B1680485
theorem B3184717 : Blo 1116628 3184717 := bstep (se 3 (by rfl) ⟨597134, by rfl⟩ : syracuseStep 3184717 = 1194269) B1194269
theorem B3774545 : Blo 1116628 3774545 := bstep (se 2 (by rfl) ⟨1415454, by rfl⟩ : syracuseStep 3774545 = 2830909) B2830909
theorem B1677395 : Blo 1116628 1677395 := bstep (se 1 (by rfl) ⟨1258046, by rfl⟩ : syracuseStep 1677395 = 2516093) B2516093
theorem B1120339 : Blo 1116628 1120339 := bstep (se 1 (by rfl) ⟨840254, by rfl⟩ : syracuseStep 1120339 = 1680509) B1680509
theorem B10754147 : Blo 1116628 10754147 := bstep (se 1 (by rfl) ⟨8065610, by rfl⟩ : syracuseStep 10754147 = 16131221) B16131221
theorem B1120355 : Blo 1116628 1120355 := bstep (se 1 (by rfl) ⟨840266, by rfl⟩ : syracuseStep 1120355 = 1680533) B1680533
theorem B9541745 : Blo 1116628 9541745 := bstep (se 2 (by rfl) ⟨3578154, by rfl⟩ : syracuseStep 9541745 = 7156309) B7156309
theorem B1677425 : Blo 1116628 1677425 := bstep (se 2 (by rfl) ⟨629034, by rfl⟩ : syracuseStep 1677425 = 1258069) B1258069
theorem B1120371 : Blo 1116628 1120371 := bstep (se 1 (by rfl) ⟨840278, by rfl⟩ : syracuseStep 1120371 = 1680557) B1680557
theorem B1677443 : Blo 1116628 1677443 := bstep (se 1 (by rfl) ⟨1258082, by rfl⟩ : syracuseStep 1677443 = 2516165) B2516165
theorem B1120387 : Blo 1116628 1120387 := bstep (se 1 (by rfl) ⟨840290, by rfl⟩ : syracuseStep 1120387 = 1680581) B1680581
theorem B1120403 : Blo 1116628 1120403 := bstep (se 1 (by rfl) ⟨840302, by rfl⟩ : syracuseStep 1120403 = 1680605) B1680605
theorem B1677473 : Blo 1116628 1677473 := bstep (se 2 (by rfl) ⟨629052, by rfl⟩ : syracuseStep 1677473 = 1258105) B1258105
theorem B1120419 : Blo 1116628 1120419 := bstep (se 1 (by rfl) ⟨840314, by rfl⟩ : syracuseStep 1120419 = 1680629) B1680629
theorem B1677491 : Blo 1116628 1677491 := bstep (se 1 (by rfl) ⟨1258118, by rfl⟩ : syracuseStep 1677491 = 2516237) B2516237
theorem B1120435 : Blo 1116628 1120435 := bstep (se 1 (by rfl) ⟨840326, by rfl⟩ : syracuseStep 1120435 = 1680653) B1680653
theorem B1120451 : Blo 1116628 1120451 := bstep (se 1 (by rfl) ⟨840338, by rfl⟩ : syracuseStep 1120451 = 1680677) B1680677
theorem B1677521 : Blo 1116628 1677521 := bstep (se 2 (by rfl) ⟨629070, by rfl⟩ : syracuseStep 1677521 = 1258141) B1258141
theorem B1120467 : Blo 1116628 1120467 := bstep (se 1 (by rfl) ⟨840350, by rfl⟩ : syracuseStep 1120467 = 1680701) B1680701
theorem B1677539 : Blo 1116628 1677539 := bstep (se 1 (by rfl) ⟨1258154, by rfl⟩ : syracuseStep 1677539 = 2516309) B2516309
theorem B1120483 : Blo 1116628 1120483 := bstep (se 1 (by rfl) ⟨840362, by rfl⟩ : syracuseStep 1120483 = 1680725) B1680725
theorem B1120499 : Blo 1116628 1120499 := bstep (se 1 (by rfl) ⟨840374, by rfl⟩ : syracuseStep 1120499 = 1680749) B1680749
theorem B1677569 : Blo 1116628 1677569 := bstep (se 2 (by rfl) ⟨629088, by rfl⟩ : syracuseStep 1677569 = 1258177) B1258177
theorem B1120515 : Blo 1116628 1120515 := bstep (se 1 (by rfl) ⟨840386, by rfl⟩ : syracuseStep 1120515 = 1680773) B1680773
theorem B1677587 : Blo 1116628 1677587 := bstep (se 1 (by rfl) ⟨1258190, by rfl⟩ : syracuseStep 1677587 = 2516381) B2516381
theorem B1120531 : Blo 1116628 1120531 := bstep (se 1 (by rfl) ⟨840398, by rfl⟩ : syracuseStep 1120531 = 1680797) B1680797
theorem B1120547 : Blo 1116628 1120547 := bstep (se 1 (by rfl) ⟨840410, by rfl⟩ : syracuseStep 1120547 = 1680821) B1680821
theorem B1677617 : Blo 1116628 1677617 := bstep (se 2 (by rfl) ⟨629106, by rfl⟩ : syracuseStep 1677617 = 1258213) B1258213
theorem B2267441 : Blo 1116628 2267441 := bstep (se 2 (by rfl) ⟨850290, by rfl⟩ : syracuseStep 2267441 = 1700581) B1700581
theorem B1120563 : Blo 1116628 1120563 := bstep (se 1 (by rfl) ⟨840422, by rfl⟩ : syracuseStep 1120563 = 1680845) B1680845
theorem B1677635 : Blo 1116628 1677635 := bstep (se 1 (by rfl) ⟨1258226, by rfl⟩ : syracuseStep 1677635 = 2516453) B2516453
theorem B1120579 : Blo 1116628 1120579 := bstep (se 1 (by rfl) ⟨840434, by rfl⟩ : syracuseStep 1120579 = 1680869) B1680869
theorem B1120595 : Blo 1116628 1120595 := bstep (se 1 (by rfl) ⟨840446, by rfl⟩ : syracuseStep 1120595 = 1680893) B1680893
theorem B1677665 : Blo 1116628 1677665 := bstep (se 2 (by rfl) ⟨629124, by rfl⟩ : syracuseStep 1677665 = 1258249) B1258249
theorem B1120611 : Blo 1116628 1120611 := bstep (se 1 (by rfl) ⟨840458, by rfl⟩ : syracuseStep 1120611 = 1680917) B1680917
theorem B1677683 : Blo 1116628 1677683 := bstep (se 1 (by rfl) ⟨1258262, by rfl⟩ : syracuseStep 1677683 = 2516525) B2516525
theorem B1120627 : Blo 1116628 1120627 := bstep (se 1 (by rfl) ⟨840470, by rfl⟩ : syracuseStep 1120627 = 1680941) B1680941
theorem B1612163 : Blo 1116628 1612163 := bstep (se 1 (by rfl) ⟨1209122, by rfl⟩ : syracuseStep 1612163 = 2418245) B2418245
theorem B3021187 : Blo 1116628 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B1677713 : Blo 1116628 1677713 := bstep (se 2 (by rfl) ⟨629142, by rfl⟩ : syracuseStep 1677713 = 1258285) B1258285
theorem B1677731 : Blo 1116628 1677731 := bstep (se 1 (by rfl) ⟨1258298, by rfl⟩ : syracuseStep 1677731 = 2516597) B2516597
theorem B1677761 : Blo 1116628 1677761 := bstep (se 2 (by rfl) ⟨629160, by rfl⟩ : syracuseStep 1677761 = 1258321) B1258321
theorem B1677779 : Blo 1116628 1677779 := bstep (se 1 (by rfl) ⟨1258334, by rfl⟩ : syracuseStep 1677779 = 2516669) B2516669
theorem B1677809 : Blo 1116628 1677809 := bstep (se 2 (by rfl) ⟨629178, by rfl⟩ : syracuseStep 1677809 = 1258357) B1258357
theorem B1677827 : Blo 1116628 1677827 := bstep (se 1 (by rfl) ⟨1258370, by rfl⟩ : syracuseStep 1677827 = 2516741) B2516741
theorem B1677857 : Blo 1116628 1677857 := bstep (se 2 (by rfl) ⟨629196, by rfl⟩ : syracuseStep 1677857 = 1258393) B1258393
theorem B1677875 : Blo 1116628 1677875 := bstep (se 1 (by rfl) ⟨1258406, by rfl⟩ : syracuseStep 1677875 = 2516813) B2516813
theorem B1677905 : Blo 1116628 1677905 := bstep (se 2 (by rfl) ⟨629214, by rfl⟩ : syracuseStep 1677905 = 1258429) B1258429
theorem B1677923 : Blo 1116628 1677923 := bstep (se 1 (by rfl) ⟨1258442, by rfl⟩ : syracuseStep 1677923 = 2516885) B2516885
theorem B3775085 : Blo 1116628 3775085 := bstep (se 3 (by rfl) ⟨707828, by rfl⟩ : syracuseStep 3775085 = 1415657) B1415657
theorem B1677953 : Blo 1116628 1677953 := bstep (se 2 (by rfl) ⟨629232, by rfl⟩ : syracuseStep 1677953 = 1258465) B1258465
theorem B1677971 : Blo 1116628 1677971 := bstep (se 1 (by rfl) ⟨1258478, by rfl⟩ : syracuseStep 1677971 = 2516957) B2516957
theorem B3775139 : Blo 1116628 3775139 := bstep (se 1 (by rfl) ⟨2831354, by rfl⟩ : syracuseStep 3775139 = 5662709) B5662709
theorem B1678001 : Blo 1116628 1678001 := bstep (se 2 (by rfl) ⟨629250, by rfl⟩ : syracuseStep 1678001 = 1258501) B1258501
theorem B1678019 : Blo 1116628 1678019 := bstep (se 1 (by rfl) ⟨1258514, by rfl⟩ : syracuseStep 1678019 = 2517029) B2517029
theorem B1415875 : Blo 1116628 1415875 := bstep (se 1 (by rfl) ⟨1061906, by rfl⟩ : syracuseStep 1415875 = 2123813) B2123813
theorem B1678049 : Blo 1116628 1678049 := bstep (se 2 (by rfl) ⟨629268, by rfl⟩ : syracuseStep 1678049 = 1258537) B1258537
theorem B1612531 : Blo 1116628 1612531 := bstep (se 1 (by rfl) ⟨1209398, by rfl⟩ : syracuseStep 1612531 = 2418797) B2418797
theorem B1678067 : Blo 1116628 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B1514227 : Blo 1116628 1514227 := bstep (se 1 (by rfl) ⟨1135670, by rfl⟩ : syracuseStep 1514227 = 2271341) B2271341
theorem B1678097 : Blo 1116628 1678097 := bstep (se 2 (by rfl) ⟨629286, by rfl⟩ : syracuseStep 1678097 = 1258573) B1258573
theorem B1678115 : Blo 1116628 1678115 := bstep (se 1 (by rfl) ⟨1258586, by rfl⟩ : syracuseStep 1678115 = 2517173) B2517173
theorem B1415971 : Blo 1116628 1415971 := bstep (se 1 (by rfl) ⟨1061978, by rfl⟩ : syracuseStep 1415971 = 2123957) B2123957
theorem B1678145 : Blo 1116628 1678145 := bstep (se 2 (by rfl) ⟨629304, by rfl⟩ : syracuseStep 1678145 = 1258609) B1258609
theorem B1678163 : Blo 1116628 1678163 := bstep (se 1 (by rfl) ⟨1258622, by rfl⟩ : syracuseStep 1678163 = 2517245) B2517245
theorem B1678193 : Blo 1116628 1678193 := bstep (se 2 (by rfl) ⟨629322, by rfl⟩ : syracuseStep 1678193 = 1258645) B1258645
theorem B1678211 : Blo 1116628 1678211 := bstep (se 1 (by rfl) ⟨1258658, by rfl⟩ : syracuseStep 1678211 = 2517317) B2517317
theorem B1678241 : Blo 1116628 1678241 := bstep (se 2 (by rfl) ⟨629340, by rfl⟩ : syracuseStep 1678241 = 1258681) B1258681
theorem B3775409 : Blo 1116628 3775409 := bstep (se 2 (by rfl) ⟨1415778, by rfl⟩ : syracuseStep 3775409 = 2831557) B2831557
theorem B1678259 : Blo 1116628 1678259 := bstep (se 1 (by rfl) ⟨1258694, by rfl⟩ : syracuseStep 1678259 = 2517389) B2517389
theorem B1678289 : Blo 1116628 1678289 := bstep (se 2 (by rfl) ⟨629358, by rfl⟩ : syracuseStep 1678289 = 1258717) B1258717
theorem B1678307 : Blo 1116628 1678307 := bstep (se 1 (by rfl) ⟨1258730, by rfl⟩ : syracuseStep 1678307 = 2517461) B2517461
theorem B1678337 : Blo 1116628 1678337 := bstep (se 2 (by rfl) ⟨629376, by rfl⟩ : syracuseStep 1678337 = 1258753) B1258753
theorem B1678355 : Blo 1116628 1678355 := bstep (se 1 (by rfl) ⟨1258766, by rfl⟩ : syracuseStep 1678355 = 2517533) B2517533
theorem B1678385 : Blo 1116628 1678385 := bstep (se 2 (by rfl) ⟨629394, by rfl⟩ : syracuseStep 1678385 = 1258789) B1258789
theorem B1678403 : Blo 1116628 1678403 := bstep (se 1 (by rfl) ⟨1258802, by rfl⟩ : syracuseStep 1678403 = 2517605) B2517605
theorem B1678433 : Blo 1116628 1678433 := bstep (se 2 (by rfl) ⟨629412, by rfl⟩ : syracuseStep 1678433 = 1258825) B1258825
theorem B1678451 : Blo 1116628 1678451 := bstep (se 1 (by rfl) ⟨1258838, by rfl⟩ : syracuseStep 1678451 = 2517677) B2517677
theorem B1678481 : Blo 1116628 1678481 := bstep (se 2 (by rfl) ⟨629430, by rfl⟩ : syracuseStep 1678481 = 1258861) B1258861
theorem B1678499 : Blo 1116628 1678499 := bstep (se 1 (by rfl) ⟨1258874, by rfl⟩ : syracuseStep 1678499 = 2517749) B2517749
theorem B1678529 : Blo 1116628 1678529 := bstep (se 2 (by rfl) ⟨629448, by rfl⟩ : syracuseStep 1678529 = 1258897) B1258897
theorem B1678547 : Blo 1116628 1678547 := bstep (se 1 (by rfl) ⟨1258910, by rfl⟩ : syracuseStep 1678547 = 2517821) B2517821
theorem B8494307 : Blo 1116628 8494307 := bstep (se 1 (by rfl) ⟨6370730, by rfl⟩ : syracuseStep 8494307 = 12741461) B12741461
theorem B1678577 : Blo 1116628 1678577 := bstep (se 2 (by rfl) ⟨629466, by rfl⟩ : syracuseStep 1678577 = 1258933) B1258933
theorem B1678595 : Blo 1116628 1678595 := bstep (se 1 (by rfl) ⟨1258946, by rfl⟩ : syracuseStep 1678595 = 2517893) B2517893
theorem B1416467 : Blo 1116628 1416467 := bstep (se 1 (by rfl) ⟨1062350, by rfl⟩ : syracuseStep 1416467 = 2124701) B2124701
theorem B1678625 : Blo 1116628 1678625 := bstep (se 2 (by rfl) ⟨629484, by rfl⟩ : syracuseStep 1678625 = 1258969) B1258969
theorem B1678643 : Blo 1116628 1678643 := bstep (se 1 (by rfl) ⟨1258982, by rfl⟩ : syracuseStep 1678643 = 2517965) B2517965
theorem B1678673 : Blo 1116628 1678673 := bstep (se 2 (by rfl) ⟨629502, by rfl⟩ : syracuseStep 1678673 = 1259005) B1259005
theorem B1678691 : Blo 1116628 1678691 := bstep (se 1 (by rfl) ⟨1259018, by rfl⟩ : syracuseStep 1678691 = 2518037) B2518037
theorem B1678721 : Blo 1116628 1678721 := bstep (se 2 (by rfl) ⟨629520, by rfl⟩ : syracuseStep 1678721 = 1259041) B1259041
theorem B8068493 : Blo 1116628 8068493 := bstep (se 3 (by rfl) ⟨1512842, by rfl⟩ : syracuseStep 8068493 = 3025685) B3025685
theorem B1678739 : Blo 1116628 1678739 := bstep (se 1 (by rfl) ⟨1259054, by rfl⟩ : syracuseStep 1678739 = 2518109) B2518109
theorem B1678769 : Blo 1116628 1678769 := bstep (se 2 (by rfl) ⟨629538, by rfl⟩ : syracuseStep 1678769 = 1259077) B1259077
theorem B1678787 : Blo 1116628 1678787 := bstep (se 1 (by rfl) ⟨1259090, by rfl⟩ : syracuseStep 1678787 = 2518181) B2518181
theorem B3775949 : Blo 1116628 3775949 := bstep (se 3 (by rfl) ⟨707990, by rfl⟩ : syracuseStep 3775949 = 1415981) B1415981
theorem B1678817 : Blo 1116628 1678817 := bstep (se 2 (by rfl) ⟨629556, by rfl⟩ : syracuseStep 1678817 = 1259113) B1259113
theorem B1678835 : Blo 1116628 1678835 := bstep (se 1 (by rfl) ⟨1259126, by rfl⟩ : syracuseStep 1678835 = 2518253) B2518253
theorem B3776003 : Blo 1116628 3776003 := bstep (se 1 (by rfl) ⟨2832002, by rfl⟩ : syracuseStep 3776003 = 5664005) B5664005
theorem B1678865 : Blo 1116628 1678865 := bstep (se 2 (by rfl) ⟨629574, by rfl⟩ : syracuseStep 1678865 = 1259149) B1259149
theorem B1678883 : Blo 1116628 1678883 := bstep (se 1 (by rfl) ⟨1259162, by rfl⟩ : syracuseStep 1678883 = 2518325) B2518325
theorem B1678913 : Blo 1116628 1678913 := bstep (se 2 (by rfl) ⟨629592, by rfl⟩ : syracuseStep 1678913 = 1259185) B1259185
theorem B1678931 : Blo 1116628 1678931 := bstep (se 1 (by rfl) ⟨1259198, by rfl⟩ : syracuseStep 1678931 = 2518397) B2518397
theorem B1678961 : Blo 1116628 1678961 := bstep (se 2 (by rfl) ⟨629610, by rfl⟩ : syracuseStep 1678961 = 1259221) B1259221
theorem B1678979 : Blo 1116628 1678979 := bstep (se 1 (by rfl) ⟨1259234, by rfl⟩ : syracuseStep 1678979 = 2518469) B2518469
theorem B1679009 : Blo 1116628 1679009 := bstep (se 2 (by rfl) ⟨629628, by rfl⟩ : syracuseStep 1679009 = 1259257) B1259257
theorem B3579565 : Blo 1116628 3579565 := bstep (se 3 (by rfl) ⟨671168, by rfl⟩ : syracuseStep 3579565 = 1342337) B1342337
theorem B1679027 : Blo 1116628 1679027 := bstep (se 1 (by rfl) ⟨1259270, by rfl⟩ : syracuseStep 1679027 = 2518541) B2518541
theorem B1679057 : Blo 1116628 1679057 := bstep (se 2 (by rfl) ⟨629646, by rfl⟩ : syracuseStep 1679057 = 1259293) B1259293
theorem B1679075 : Blo 1116628 1679075 := bstep (se 1 (by rfl) ⟨1259306, by rfl⟩ : syracuseStep 1679075 = 2518613) B2518613
theorem B1679105 : Blo 1116628 1679105 := bstep (se 2 (by rfl) ⟨629664, by rfl⟩ : syracuseStep 1679105 = 1259329) B1259329
theorem B3776273 : Blo 1116628 3776273 := bstep (se 2 (by rfl) ⟨1416102, by rfl⟩ : syracuseStep 3776273 = 2832205) B2832205
theorem B3186449 : Blo 1116628 3186449 := bstep (se 2 (by rfl) ⟨1194918, by rfl⟩ : syracuseStep 3186449 = 2389837) B2389837
theorem B1679123 : Blo 1116628 1679123 := bstep (se 1 (by rfl) ⟨1259342, by rfl⟩ : syracuseStep 1679123 = 2518685) B2518685
theorem B1679153 : Blo 1116628 1679153 := bstep (se 2 (by rfl) ⟨629682, by rfl⟩ : syracuseStep 1679153 = 1259365) B1259365
theorem B1679171 : Blo 1116628 1679171 := bstep (se 1 (by rfl) ⟨1259378, by rfl⟩ : syracuseStep 1679171 = 2518757) B2518757
theorem B1679201 : Blo 1116628 1679201 := bstep (se 2 (by rfl) ⟨629700, by rfl⟩ : syracuseStep 1679201 = 1259401) B1259401
theorem B1679219 : Blo 1116628 1679219 := bstep (se 1 (by rfl) ⟨1259414, by rfl⟩ : syracuseStep 1679219 = 2518829) B2518829
theorem B1679249 : Blo 1116628 1679249 := bstep (se 2 (by rfl) ⟨629718, by rfl⟩ : syracuseStep 1679249 = 1259437) B1259437
theorem B1679267 : Blo 1116628 1679267 := bstep (se 1 (by rfl) ⟨1259450, by rfl⟩ : syracuseStep 1679267 = 2518901) B2518901
theorem B1679297 : Blo 1116628 1679297 := bstep (se 2 (by rfl) ⟨629736, by rfl⟩ : syracuseStep 1679297 = 1259473) B1259473
theorem B3186641 : Blo 1116628 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B1679315 : Blo 1116628 1679315 := bstep (se 1 (by rfl) ⟨1259486, by rfl⟩ : syracuseStep 1679315 = 2518973) B2518973
theorem B1417171 : Blo 1116628 1417171 := bstep (se 1 (by rfl) ⟨1062878, by rfl⟩ : syracuseStep 1417171 = 2125757) B2125757
theorem B4530161 : Blo 1116628 4530161 := bstep (se 2 (by rfl) ⟨1698810, by rfl⟩ : syracuseStep 4530161 = 3397621) B3397621
theorem B1679345 : Blo 1116628 1679345 := bstep (se 2 (by rfl) ⟨629754, by rfl⟩ : syracuseStep 1679345 = 1259509) B1259509
theorem B1679363 : Blo 1116628 1679363 := bstep (se 1 (by rfl) ⟨1259522, by rfl⟩ : syracuseStep 1679363 = 2519045) B2519045
theorem B1679393 : Blo 1116628 1679393 := bstep (se 2 (by rfl) ⟨629772, by rfl⟩ : syracuseStep 1679393 = 1259545) B1259545
theorem B1679411 : Blo 1116628 1679411 := bstep (se 1 (by rfl) ⟨1259558, by rfl⟩ : syracuseStep 1679411 = 2519117) B2519117
theorem B1417267 : Blo 1116628 1417267 := bstep (se 1 (by rfl) ⟨1062950, by rfl⟩ : syracuseStep 1417267 = 2125901) B2125901
theorem B1679441 : Blo 1116628 1679441 := bstep (se 2 (by rfl) ⟨629790, by rfl⟩ : syracuseStep 1679441 = 1259581) B1259581
theorem B1679459 : Blo 1116628 1679459 := bstep (se 1 (by rfl) ⟨1259594, by rfl⟩ : syracuseStep 1679459 = 2519189) B2519189
theorem B1679489 : Blo 1116628 1679489 := bstep (se 2 (by rfl) ⟨629808, by rfl⟩ : syracuseStep 1679489 = 1259617) B1259617
theorem B1679507 : Blo 1116628 1679507 := bstep (se 1 (by rfl) ⟨1259630, by rfl⟩ : syracuseStep 1679507 = 2519261) B2519261
theorem B1679537 : Blo 1116628 1679537 := bstep (se 2 (by rfl) ⟨629826, by rfl⟩ : syracuseStep 1679537 = 1259653) B1259653
theorem B1679555 : Blo 1116628 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B1745107 : Blo 1116628 1745107 := bstep (se 1 (by rfl) ⟨1308830, by rfl⟩ : syracuseStep 1745107 = 2617661) B2617661
theorem B1679585 : Blo 1116628 1679585 := bstep (se 2 (by rfl) ⟨629844, by rfl⟩ : syracuseStep 1679585 = 1259689) B1259689
theorem B2728163 : Blo 1116628 2728163 := bstep (se 1 (by rfl) ⟨2046122, by rfl⟩ : syracuseStep 2728163 = 4092245) B4092245
theorem B1679603 : Blo 1116628 1679603 := bstep (se 1 (by rfl) ⟨1259702, by rfl⟩ : syracuseStep 1679603 = 2519405) B2519405
theorem B1679633 : Blo 1116628 1679633 := bstep (se 2 (by rfl) ⟨629862, by rfl⟩ : syracuseStep 1679633 = 1259725) B1259725
theorem B1679651 : Blo 1116628 1679651 := bstep (se 1 (by rfl) ⟨1259738, by rfl⟩ : syracuseStep 1679651 = 2519477) B2519477
theorem B3776813 : Blo 1116628 3776813 := bstep (se 3 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 3776813 = 1416305) B1416305
theorem B1679681 : Blo 1116628 1679681 := bstep (se 2 (by rfl) ⟨629880, by rfl⟩ : syracuseStep 1679681 = 1259761) B1259761
theorem B1679699 : Blo 1116628 1679699 := bstep (se 1 (by rfl) ⟨1259774, by rfl⟩ : syracuseStep 1679699 = 2519549) B2519549
theorem B3776867 : Blo 1116628 3776867 := bstep (se 1 (by rfl) ⟨2832650, by rfl⟩ : syracuseStep 3776867 = 5665301) B5665301
theorem B1679729 : Blo 1116628 1679729 := bstep (se 2 (by rfl) ⟨629898, by rfl⟩ : syracuseStep 1679729 = 1259797) B1259797
theorem B1679747 : Blo 1116628 1679747 := bstep (se 1 (by rfl) ⟨1259810, by rfl⟩ : syracuseStep 1679747 = 2519621) B2519621
theorem B1679777 : Blo 1116628 1679777 := bstep (se 2 (by rfl) ⟨629916, by rfl⟩ : syracuseStep 1679777 = 1259833) B1259833
theorem B1679795 : Blo 1116628 1679795 := bstep (se 1 (by rfl) ⟨1259846, by rfl⟩ : syracuseStep 1679795 = 2519693) B2519693
theorem B1679825 : Blo 1116628 1679825 := bstep (se 2 (by rfl) ⟨629934, by rfl⟩ : syracuseStep 1679825 = 1259869) B1259869
theorem B1679843 : Blo 1116628 1679843 := bstep (se 1 (by rfl) ⟨1259882, by rfl⟩ : syracuseStep 1679843 = 2519765) B2519765
theorem B1679873 : Blo 1116628 1679873 := bstep (se 2 (by rfl) ⟨629952, by rfl⟩ : syracuseStep 1679873 = 1259905) B1259905
theorem B1679891 : Blo 1116628 1679891 := bstep (se 1 (by rfl) ⟨1259918, by rfl⟩ : syracuseStep 1679891 = 2519837) B2519837
theorem B1417763 : Blo 1116628 1417763 := bstep (se 1 (by rfl) ⟨1063322, by rfl⟩ : syracuseStep 1417763 = 2126645) B2126645
theorem B1679921 : Blo 1116628 1679921 := bstep (se 2 (by rfl) ⟨629970, by rfl⟩ : syracuseStep 1679921 = 1259941) B1259941
theorem B1679939 : Blo 1116628 1679939 := bstep (se 1 (by rfl) ⟨1259954, by rfl⟩ : syracuseStep 1679939 = 2519909) B2519909
theorem B1679969 : Blo 1116628 1679969 := bstep (se 2 (by rfl) ⟨629988, by rfl⟩ : syracuseStep 1679969 = 1259977) B1259977
theorem B3777137 : Blo 1116628 3777137 := bstep (se 2 (by rfl) ⟨1416426, by rfl⟩ : syracuseStep 3777137 = 2832853) B2832853
theorem B1679987 : Blo 1116628 1679987 := bstep (se 1 (by rfl) ⟨1259990, by rfl⟩ : syracuseStep 1679987 = 2519981) B2519981
theorem B1680017 : Blo 1116628 1680017 := bstep (se 2 (by rfl) ⟨630006, by rfl⟩ : syracuseStep 1680017 = 1260013) B1260013
theorem B1680035 : Blo 1116628 1680035 := bstep (se 1 (by rfl) ⟨1260026, by rfl⟩ : syracuseStep 1680035 = 2520053) B2520053
theorem B13607605 : Blo 1116628 13607605 := bstep (se 5 (by rfl) ⟨637856, by rfl⟩ : syracuseStep 13607605 = 1275713) B1275713
theorem B1680065 : Blo 1116628 1680065 := bstep (se 2 (by rfl) ⟨630024, by rfl⟩ : syracuseStep 1680065 = 1260049) B1260049
theorem B1680083 : Blo 1116628 1680083 := bstep (se 1 (by rfl) ⟨1260062, by rfl⟩ : syracuseStep 1680083 = 2520125) B2520125
theorem B1680113 : Blo 1116628 1680113 := bstep (se 2 (by rfl) ⟨630042, by rfl⟩ : syracuseStep 1680113 = 1260085) B1260085
theorem B1680131 : Blo 1116628 1680131 := bstep (se 1 (by rfl) ⟨1260098, by rfl⟩ : syracuseStep 1680131 = 2520197) B2520197
theorem B1680161 : Blo 1116628 1680161 := bstep (se 2 (by rfl) ⟨630060, by rfl⟩ : syracuseStep 1680161 = 1260121) B1260121
theorem B1680179 : Blo 1116628 1680179 := bstep (se 1 (by rfl) ⟨1260134, by rfl⟩ : syracuseStep 1680179 = 2520269) B2520269
theorem B1680209 : Blo 1116628 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B1680227 : Blo 1116628 1680227 := bstep (se 1 (by rfl) ⟨1260170, by rfl⟩ : syracuseStep 1680227 = 2520341) B2520341
theorem B1680257 : Blo 1116628 1680257 := bstep (se 2 (by rfl) ⟨630096, by rfl⟩ : syracuseStep 1680257 = 1260193) B1260193
theorem B1680275 : Blo 1116628 1680275 := bstep (se 1 (by rfl) ⟨1260206, by rfl⟩ : syracuseStep 1680275 = 2520413) B2520413
theorem B3187633 : Blo 1116628 3187633 := bstep (se 2 (by rfl) ⟨1195362, by rfl⟩ : syracuseStep 3187633 = 2390725) B2390725
theorem B1680305 : Blo 1116628 1680305 := bstep (se 2 (by rfl) ⟨630114, by rfl⟩ : syracuseStep 1680305 = 1260229) B1260229
theorem B1680323 : Blo 1116628 1680323 := bstep (se 1 (by rfl) ⟨1260242, by rfl⟩ : syracuseStep 1680323 = 2520485) B2520485
theorem B1680353 : Blo 1116628 1680353 := bstep (se 2 (by rfl) ⟨630132, by rfl⟩ : syracuseStep 1680353 = 1260265) B1260265
theorem B1680371 : Blo 1116628 1680371 := bstep (se 1 (by rfl) ⟨1260278, by rfl⟩ : syracuseStep 1680371 = 2520557) B2520557
theorem B6366221 : Blo 1116628 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B1680401 : Blo 1116628 1680401 := bstep (se 2 (by rfl) ⟨630150, by rfl⟩ : syracuseStep 1680401 = 1260301) B1260301
theorem B1680419 : Blo 1116628 1680419 := bstep (se 1 (by rfl) ⟨1260314, by rfl⟩ : syracuseStep 1680419 = 2520629) B2520629
theorem B1680449 : Blo 1116628 1680449 := bstep (se 2 (by rfl) ⟨630168, by rfl⟩ : syracuseStep 1680449 = 1260337) B1260337
theorem B2827345 : Blo 1116628 2827345 := bstep (se 2 (by rfl) ⟨1060254, by rfl⟩ : syracuseStep 2827345 = 2120509) B2120509
theorem B1680467 : Blo 1116628 1680467 := bstep (se 1 (by rfl) ⟨1260350, by rfl⟩ : syracuseStep 1680467 = 2520701) B2520701
theorem B1680497 : Blo 1116628 1680497 := bstep (se 2 (by rfl) ⟨630186, by rfl⟩ : syracuseStep 1680497 = 1260373) B1260373
theorem B1680515 : Blo 1116628 1680515 := bstep (se 1 (by rfl) ⟨1260386, by rfl⟩ : syracuseStep 1680515 = 2520773) B2520773
theorem B3777677 : Blo 1116628 3777677 := bstep (se 3 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 3777677 = 1416629) B1416629
theorem B1680545 : Blo 1116628 1680545 := bstep (se 2 (by rfl) ⟨630204, by rfl⟩ : syracuseStep 1680545 = 1260409) B1260409
theorem B1680563 : Blo 1116628 1680563 := bstep (se 1 (by rfl) ⟨1260422, by rfl⟩ : syracuseStep 1680563 = 2520845) B2520845
theorem B3777731 : Blo 1116628 3777731 := bstep (se 1 (by rfl) ⟨2833298, by rfl⟩ : syracuseStep 3777731 = 5666597) B5666597
theorem B3187907 : Blo 1116628 3187907 := bstep (se 1 (by rfl) ⟨2390930, by rfl⟩ : syracuseStep 3187907 = 4781861) B4781861
theorem B1680593 : Blo 1116628 1680593 := bstep (se 2 (by rfl) ⟨630222, by rfl⟩ : syracuseStep 1680593 = 1260445) B1260445
theorem B1680611 : Blo 1116628 1680611 := bstep (se 1 (by rfl) ⟨1260458, by rfl⟩ : syracuseStep 1680611 = 2520917) B2520917
theorem B10200305 : Blo 1116628 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1680641 : Blo 1116628 1680641 := bstep (se 2 (by rfl) ⟨630240, by rfl⟩ : syracuseStep 1680641 = 1260481) B1260481
theorem B1680659 : Blo 1116628 1680659 := bstep (se 1 (by rfl) ⟨1260494, by rfl⟩ : syracuseStep 1680659 = 2520989) B2520989
theorem B33596693 : Blo 1116628 33596693 := bstep (se 6 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 33596693 = 1574845) B1574845
theorem B1680689 : Blo 1116628 1680689 := bstep (se 2 (by rfl) ⟨630258, by rfl⟩ : syracuseStep 1680689 = 1260517) B1260517
theorem B1680707 : Blo 1116628 1680707 := bstep (se 1 (by rfl) ⟨1260530, by rfl⟩ : syracuseStep 1680707 = 2521061) B2521061
theorem B2827619 : Blo 1116628 2827619 := bstep (se 1 (by rfl) ⟨2120714, by rfl⟩ : syracuseStep 2827619 = 4241429) B4241429
theorem B1680737 : Blo 1116628 1680737 := bstep (se 2 (by rfl) ⟨630276, by rfl⟩ : syracuseStep 1680737 = 1260553) B1260553
theorem B1680755 : Blo 1116628 1680755 := bstep (se 1 (by rfl) ⟨1260566, by rfl⟩ : syracuseStep 1680755 = 2521133) B2521133
theorem B3188099 : Blo 1116628 3188099 := bstep (se 1 (by rfl) ⟨2391074, by rfl⟩ : syracuseStep 3188099 = 4782149) B4782149
theorem B1680785 : Blo 1116628 1680785 := bstep (se 2 (by rfl) ⟨630294, by rfl⟩ : syracuseStep 1680785 = 1260589) B1260589
theorem B1680803 : Blo 1116628 1680803 := bstep (se 1 (by rfl) ⟨1260602, by rfl⟩ : syracuseStep 1680803 = 2521205) B2521205
theorem B3024301 : Blo 1116628 3024301 := bstep (se 3 (by rfl) ⟨567056, by rfl⟩ : syracuseStep 3024301 = 1134113) B1134113
theorem B1680833 : Blo 1116628 1680833 := bstep (se 2 (by rfl) ⟨630312, by rfl⟩ : syracuseStep 1680833 = 1260625) B1260625
theorem B25798085 : Blo 1116628 25798085 := bstep (se 4 (by rfl) ⟨2418570, by rfl⟩ : syracuseStep 25798085 = 4837141) B4837141
theorem B3778001 : Blo 1116628 3778001 := bstep (se 2 (by rfl) ⟨1416750, by rfl⟩ : syracuseStep 3778001 = 2833501) B2833501
theorem B1680851 : Blo 1116628 1680851 := bstep (se 1 (by rfl) ⟨1260638, by rfl⟩ : syracuseStep 1680851 = 2521277) B2521277
theorem B1680881 : Blo 1116628 1680881 := bstep (se 2 (by rfl) ⟨630330, by rfl⟩ : syracuseStep 1680881 = 1260661) B1260661
theorem B1680899 : Blo 1116628 1680899 := bstep (se 1 (by rfl) ⟨1260674, by rfl⟩ : syracuseStep 1680899 = 2521349) B2521349
theorem B1680929 : Blo 1116628 1680929 := bstep (se 2 (by rfl) ⟨630348, by rfl⟩ : syracuseStep 1680929 = 1260697) B1260697
theorem B2827811 : Blo 1116628 2827811 := bstep (se 1 (by rfl) ⟨2120858, by rfl⟩ : syracuseStep 2827811 = 4241717) B4241717
theorem B9086917 : Blo 1116628 9086917 := bstep (se 4 (by rfl) ⟨851898, by rfl⟩ : syracuseStep 9086917 = 1703797) B1703797
theorem B5744611 : Blo 1116628 5744611 := bstep (se 1 (by rfl) ⟨4308458, by rfl⟩ : syracuseStep 5744611 = 8616917) B8616917
theorem B3778541 : Blo 1116628 3778541 := bstep (se 3 (by rfl) ⟨708476, by rfl⟩ : syracuseStep 3778541 = 1416953) B1416953
theorem B3778595 : Blo 1116628 3778595 := bstep (se 1 (by rfl) ⟨2833946, by rfl⟩ : syracuseStep 3778595 = 5667893) B5667893
theorem B3188909 : Blo 1116628 3188909 := bstep (se 3 (by rfl) ⟨597920, by rfl⟩ : syracuseStep 3188909 = 1195841) B1195841
theorem B3778865 : Blo 1116628 3778865 := bstep (se 2 (by rfl) ⟨1417074, by rfl⟩ : syracuseStep 3778865 = 2834149) B2834149
theorem B3189091 : Blo 1116628 3189091 := bstep (se 1 (by rfl) ⟨2391818, by rfl⟩ : syracuseStep 3189091 = 4783637) B4783637
theorem B2828753 : Blo 1116628 2828753 := bstep (se 2 (by rfl) ⟨1060782, by rfl⟩ : syracuseStep 2828753 = 2121565) B2121565
theorem B2828803 : Blo 1116628 2828803 := bstep (se 1 (by rfl) ⟨2121602, by rfl⟩ : syracuseStep 2828803 = 4243205) B4243205
theorem B2828945 : Blo 1116628 2828945 := bstep (se 2 (by rfl) ⟨1060854, by rfl⟩ : syracuseStep 2828945 = 2121709) B2121709
theorem B3779405 : Blo 1116628 3779405 := bstep (se 3 (by rfl) ⟨708638, by rfl⟩ : syracuseStep 3779405 = 1417277) B1417277
theorem B3189581 : Blo 1116628 3189581 := bstep (se 3 (by rfl) ⟨598046, by rfl⟩ : syracuseStep 3189581 = 1196093) B1196093
theorem B3779459 : Blo 1116628 3779459 := bstep (se 1 (by rfl) ⟨2834594, by rfl⟩ : syracuseStep 3779459 = 5669189) B5669189
theorem B3025795 : Blo 1116628 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B1256323 : Blo 1116628 1256323 := bstep (se 1 (by rfl) ⟨942242, by rfl⟩ : syracuseStep 1256323 = 1884485) B1884485
theorem B6040453 : Blo 1116628 6040453 := bstep (se 4 (by rfl) ⟨566292, by rfl⟩ : syracuseStep 6040453 = 1132585) B1132585
theorem B2042833 : Blo 1116628 2042833 := bstep (se 2 (by rfl) ⟨766062, by rfl⟩ : syracuseStep 2042833 = 1532125) B1532125
theorem B1256467 : Blo 1116628 1256467 := bstep (se 1 (by rfl) ⟨942350, by rfl⟩ : syracuseStep 1256467 = 1884701) B1884701
theorem B3583025 : Blo 1116628 3583025 := bstep (se 2 (by rfl) ⟨1343634, by rfl⟩ : syracuseStep 3583025 = 2687269) B2687269
theorem B3779729 : Blo 1116628 3779729 := bstep (se 2 (by rfl) ⟨1417398, by rfl⟩ : syracuseStep 3779729 = 2834797) B2834797
theorem B1256611 : Blo 1116628 1256611 := bstep (se 1 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 1256611 = 1884917) B1884917
theorem B6368453 : Blo 1116628 6368453 := bstep (se 4 (by rfl) ⟨597042, by rfl⟩ : syracuseStep 6368453 = 1194085) B1194085
theorem B3583217 : Blo 1116628 3583217 := bstep (se 2 (by rfl) ⟨1343706, by rfl⟩ : syracuseStep 3583217 = 2687413) B2687413
theorem B1256755 : Blo 1116628 1256755 := bstep (se 1 (by rfl) ⟨942566, by rfl⟩ : syracuseStep 1256755 = 1885133) B1885133
theorem B10759493 : Blo 1116628 10759493 := bstep (se 4 (by rfl) ⟨1008702, by rfl⟩ : syracuseStep 10759493 = 2017405) B2017405
theorem B6040973 : Blo 1116628 6040973 := bstep (se 3 (by rfl) ⟨1132682, by rfl⟩ : syracuseStep 6040973 = 2265365) B2265365
theorem B1256899 : Blo 1116628 1256899 := bstep (se 1 (by rfl) ⟨942674, by rfl⟩ : syracuseStep 1256899 = 1885349) B1885349
theorem B1257043 : Blo 1116628 1257043 := bstep (se 1 (by rfl) ⟨942782, by rfl⟩ : syracuseStep 1257043 = 1885565) B1885565
theorem B2829937 : Blo 1116628 2829937 := bstep (se 2 (by rfl) ⟨1061226, by rfl⟩ : syracuseStep 2829937 = 2122453) B2122453
theorem B3780269 : Blo 1116628 3780269 := bstep (se 3 (by rfl) ⟨708800, by rfl⟩ : syracuseStep 3780269 = 1417601) B1417601
theorem B3223217 : Blo 1116628 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B1257187 : Blo 1116628 1257187 := bstep (se 1 (by rfl) ⟨942890, by rfl⟩ : syracuseStep 1257187 = 1885781) B1885781
theorem B3780323 : Blo 1116628 3780323 := bstep (se 1 (by rfl) ⟨2835242, by rfl⟩ : syracuseStep 3780323 = 5670485) B5670485
theorem B6369137 : Blo 1116628 6369137 := bstep (se 2 (by rfl) ⟨2388426, by rfl⟩ : syracuseStep 6369137 = 4776853) B4776853
theorem B3026801 : Blo 1116628 3026801 := bstep (se 2 (by rfl) ⟨1135050, by rfl⟩ : syracuseStep 3026801 = 2270101) B2270101
theorem B1257331 : Blo 1116628 1257331 := bstep (se 1 (by rfl) ⟨942998, by rfl⟩ : syracuseStep 1257331 = 1885997) B1885997
theorem B2830211 : Blo 1116628 2830211 := bstep (se 1 (by rfl) ⟨2122658, by rfl⟩ : syracuseStep 2830211 = 4245317) B4245317
theorem B1912771 : Blo 1116628 1912771 := bstep (se 1 (by rfl) ⟨1434578, by rfl⟩ : syracuseStep 1912771 = 2869157) B2869157
theorem B3190765 : Blo 1116628 3190765 := bstep (se 3 (by rfl) ⟨598268, by rfl⟩ : syracuseStep 3190765 = 1196537) B1196537
theorem B3780593 : Blo 1116628 3780593 := bstep (se 2 (by rfl) ⟨1417722, by rfl⟩ : syracuseStep 3780593 = 2835445) B2835445
theorem B1257475 : Blo 1116628 1257475 := bstep (se 1 (by rfl) ⟨943106, by rfl⟩ : syracuseStep 1257475 = 1886213) B1886213
theorem B2830403 : Blo 1116628 2830403 := bstep (se 1 (by rfl) ⟨2122802, by rfl⟩ : syracuseStep 2830403 = 4245605) B4245605
theorem B1257619 : Blo 1116628 1257619 := bstep (se 1 (by rfl) ⟨943214, by rfl⟩ : syracuseStep 1257619 = 1886429) B1886429
theorem B1913009 : Blo 1116628 1913009 := bstep (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) B1434757
theorem B1257763 : Blo 1116628 1257763 := bstep (se 1 (by rfl) ⟨943322, by rfl⟩ : syracuseStep 1257763 = 1886645) B1886645
theorem B14332301 : Blo 1116628 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B1257907 : Blo 1116628 1257907 := bstep (se 1 (by rfl) ⟨943430, by rfl⟩ : syracuseStep 1257907 = 1886861) B1886861
theorem B8499653 : Blo 1116628 8499653 := bstep (se 4 (by rfl) ⟨796842, by rfl⟩ : syracuseStep 8499653 = 1593685) B1593685
theorem B3781133 : Blo 1116628 3781133 := bstep (se 3 (by rfl) ⟨708962, by rfl⟩ : syracuseStep 3781133 = 1417925) B1417925
theorem B7156259 : Blo 1116628 7156259 := bstep (se 1 (by rfl) ⟨5367194, by rfl⟩ : syracuseStep 7156259 = 10734389) B10734389
theorem B1258051 : Blo 1116628 1258051 := bstep (se 1 (by rfl) ⟨943538, by rfl⟩ : syracuseStep 1258051 = 1887077) B1887077
theorem B3781187 : Blo 1116628 3781187 := bstep (se 1 (by rfl) ⟨2835890, by rfl⟩ : syracuseStep 3781187 = 5671781) B5671781
theorem B4239971 : Blo 1116628 4239971 := bstep (se 1 (by rfl) ⟨3179978, by rfl⟩ : syracuseStep 4239971 = 6359957) B6359957
theorem B4239985 : Blo 1116628 4239985 := bstep (se 2 (by rfl) ⟨1589994, by rfl⟩ : syracuseStep 4239985 = 3179989) B3179989
theorem B6042289 : Blo 1116628 6042289 := bstep (se 2 (by rfl) ⟨2265858, by rfl⟩ : syracuseStep 6042289 = 4531717) B4531717
theorem B1258195 : Blo 1116628 1258195 := bstep (se 1 (by rfl) ⟨943646, by rfl⟩ : syracuseStep 1258195 = 1887293) B1887293
theorem B3781457 : Blo 1116628 3781457 := bstep (se 2 (by rfl) ⟨1418046, by rfl⟩ : syracuseStep 3781457 = 2836093) B2836093
theorem B1258339 : Blo 1116628 1258339 := bstep (se 1 (by rfl) ⟨943754, by rfl⟩ : syracuseStep 1258339 = 1887509) B1887509
theorem B1192915 : Blo 1116628 1192915 := bstep (se 1 (by rfl) ⟨894686, by rfl⟩ : syracuseStep 1192915 = 1789373) B1789373
theorem B16135139 : Blo 1116628 16135139 := bstep (se 1 (by rfl) ⟨12101354, by rfl⟩ : syracuseStep 16135139 = 24202709) B24202709
theorem B2831345 : Blo 1116628 2831345 := bstep (se 2 (by rfl) ⟨1061754, by rfl⟩ : syracuseStep 2831345 = 2123509) B2123509
theorem B1258483 : Blo 1116628 1258483 := bstep (se 1 (by rfl) ⟨943862, by rfl⟩ : syracuseStep 1258483 = 1887725) B1887725
theorem B2831395 : Blo 1116628 2831395 := bstep (se 1 (by rfl) ⟨2123546, by rfl⟩ : syracuseStep 2831395 = 4247093) B4247093
theorem B1258627 : Blo 1116628 1258627 := bstep (se 1 (by rfl) ⟨943970, by rfl⟩ : syracuseStep 1258627 = 1887941) B1887941
theorem B3028099 : Blo 1116628 3028099 := bstep (se 1 (by rfl) ⟨2271074, by rfl⟩ : syracuseStep 3028099 = 4542149) B4542149
theorem B2831537 : Blo 1116628 2831537 := bstep (se 2 (by rfl) ⟨1061826, by rfl⟩ : syracuseStep 2831537 = 2123653) B2123653
theorem B1258771 : Blo 1116628 1258771 := bstep (se 1 (by rfl) ⟨944078, by rfl⟩ : syracuseStep 1258771 = 1888157) B1888157
theorem B6370595 : Blo 1116628 6370595 := bstep (se 1 (by rfl) ⟨4777946, by rfl⟩ : syracuseStep 6370595 = 9555893) B9555893
theorem B3781997 : Blo 1116628 3781997 := bstep (se 3 (by rfl) ⟨709124, by rfl⟩ : syracuseStep 3781997 = 1418249) B1418249
theorem B1258915 : Blo 1116628 1258915 := bstep (se 1 (by rfl) ⟨944186, by rfl⟩ : syracuseStep 1258915 = 1888373) B1888373
theorem B3782051 : Blo 1116628 3782051 := bstep (se 1 (by rfl) ⟨2836538, by rfl⟩ : syracuseStep 3782051 = 5673077) B5673077
theorem B3585485 : Blo 1116628 3585485 := bstep (se 3 (by rfl) ⟨672278, by rfl⟩ : syracuseStep 3585485 = 1344557) B1344557
theorem B15316451 : Blo 1116628 15316451 := bstep (se 1 (by rfl) ⟨11487338, by rfl⟩ : syracuseStep 15316451 = 22974677) B22974677
theorem B1259059 : Blo 1116628 1259059 := bstep (se 1 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 1259059 = 1888589) B1888589
theorem B64599605 : Blo 1116628 64599605 := bstep (se 5 (by rfl) ⟨3028106, by rfl⟩ : syracuseStep 64599605 = 6056213) B6056213
theorem B1914529 : Blo 1116628 1914529 := bstep (se 2 (by rfl) ⟨717948, by rfl⟩ : syracuseStep 1914529 = 1435897) B1435897
theorem B1259203 : Blo 1116628 1259203 := bstep (se 1 (by rfl) ⟨944402, by rfl⟩ : syracuseStep 1259203 = 1888805) B1888805
theorem B5748515 : Blo 1116628 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B1259347 : Blo 1116628 1259347 := bstep (se 1 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 1259347 = 1889021) B1889021
theorem B3028877 : Blo 1116628 3028877 := bstep (se 3 (by rfl) ⟨567914, by rfl⟩ : syracuseStep 3028877 = 1135829) B1135829
theorem B1259491 : Blo 1116628 1259491 := bstep (se 1 (by rfl) ⟨944618, by rfl⟩ : syracuseStep 1259491 = 1889237) B1889237
theorem B9549809 : Blo 1116628 9549809 := bstep (se 2 (by rfl) ⟨3581178, by rfl⟩ : syracuseStep 9549809 = 7162357) B7162357
theorem B1914883 : Blo 1116628 1914883 := bstep (se 1 (by rfl) ⟨1436162, by rfl⟩ : syracuseStep 1914883 = 2872325) B2872325
theorem B4241443 : Blo 1116628 4241443 := bstep (se 1 (by rfl) ⟨3181082, by rfl⟩ : syracuseStep 4241443 = 6362165) B6362165
theorem B1259635 : Blo 1116628 1259635 := bstep (se 1 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 1259635 = 1889453) B1889453
theorem B2832529 : Blo 1116628 2832529 := bstep (se 2 (by rfl) ⟨1062198, by rfl⟩ : syracuseStep 2832529 = 2124397) B2124397
theorem B1259779 : Blo 1116628 1259779 := bstep (se 1 (by rfl) ⟨944834, by rfl⟩ : syracuseStep 1259779 = 1889669) B1889669
theorem B1194307 : Blo 1116628 1194307 := bstep (se 1 (by rfl) ⟨895730, by rfl⟩ : syracuseStep 1194307 = 1791461) B1791461
theorem B1259923 : Blo 1116628 1259923 := bstep (se 1 (by rfl) ⟨944942, by rfl⟩ : syracuseStep 1259923 = 1889885) B1889885
theorem B2832803 : Blo 1116628 2832803 := bstep (se 1 (by rfl) ⟨2124602, by rfl⟩ : syracuseStep 2832803 = 4249205) B4249205
theorem B7158257 : Blo 1116628 7158257 := bstep (se 2 (by rfl) ⟨2684346, by rfl⟩ : syracuseStep 7158257 = 5368693) B5368693
theorem B1260067 : Blo 1116628 1260067 := bstep (se 1 (by rfl) ⟨945050, by rfl⟩ : syracuseStep 1260067 = 1890101) B1890101
theorem B2832995 : Blo 1116628 2832995 := bstep (se 1 (by rfl) ⟨2124746, by rfl⟩ : syracuseStep 2832995 = 4249493) B4249493
theorem B1260211 : Blo 1116628 1260211 := bstep (se 1 (by rfl) ⟨945158, by rfl⟩ : syracuseStep 1260211 = 1890317) B1890317
theorem B2210627 : Blo 1116628 2210627 := bstep (se 1 (by rfl) ⟨1657970, by rfl⟩ : syracuseStep 2210627 = 3315941) B3315941
theorem B1260355 : Blo 1116628 1260355 := bstep (se 1 (by rfl) ⟨945266, by rfl⟩ : syracuseStep 1260355 = 1890533) B1890533
theorem B1260499 : Blo 1116628 1260499 := bstep (se 1 (by rfl) ⟨945374, by rfl⟩ : syracuseStep 1260499 = 1890749) B1890749
theorem B3587075 : Blo 1116628 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B1260643 : Blo 1116628 1260643 := bstep (se 1 (by rfl) ⟨945482, by rfl⟩ : syracuseStep 1260643 = 1890965) B1890965
theorem B6798449 : Blo 1116628 6798449 := bstep (se 2 (by rfl) ⟨2549418, by rfl⟩ : syracuseStep 6798449 = 5098837) B5098837
theorem B21478769 : Blo 1116628 21478769 := bstep (se 2 (by rfl) ⟨8054538, by rfl⟩ : syracuseStep 21478769 = 16109077) B16109077
theorem B12729797 : Blo 1116628 12729797 := bstep (se 4 (by rfl) ⟨1193418, by rfl⟩ : syracuseStep 12729797 = 2386837) B2386837
theorem B2833937 : Blo 1116628 2833937 := bstep (se 2 (by rfl) ⟨1062726, by rfl⟩ : syracuseStep 2833937 = 2125453) B2125453
theorem B2833987 : Blo 1116628 2833987 := bstep (se 1 (by rfl) ⟨2125490, by rfl⟩ : syracuseStep 2833987 = 4250981) B4250981
theorem B6045317 : Blo 1116628 6045317 := bstep (se 4 (by rfl) ⟨566748, by rfl⟩ : syracuseStep 6045317 = 1133497) B1133497
theorem B2834129 : Blo 1116628 2834129 := bstep (se 2 (by rfl) ⟨1062798, by rfl⟩ : syracuseStep 2834129 = 2125597) B2125597
theorem B3587971 : Blo 1116628 3587971 := bstep (se 1 (by rfl) ⟨2690978, by rfl⟩ : syracuseStep 3587971 = 5381957) B5381957
theorem B8601713 : Blo 1116628 8601713 := bstep (se 2 (by rfl) ⟨3225642, by rfl⟩ : syracuseStep 8601713 = 6451285) B6451285
theorem B1884323 : Blo 1116628 1884323 := bstep (se 1 (by rfl) ⟨1413242, by rfl⟩ : syracuseStep 1884323 = 2826485) B2826485
theorem B4243661 : Blo 1116628 4243661 := bstep (se 3 (by rfl) ⟨795686, by rfl⟩ : syracuseStep 4243661 = 1591373) B1591373
theorem B1884451 : Blo 1116628 1884451 := bstep (se 1 (by rfl) ⟨1413338, by rfl⟩ : syracuseStep 1884451 = 2826677) B2826677
theorem B9060707 : Blo 1116628 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B9552269 : Blo 1116628 9552269 := bstep (se 3 (by rfl) ⟨1791050, by rfl⟩ : syracuseStep 9552269 = 3582101) B3582101
theorem B1884593 : Blo 1116628 1884593 := bstep (se 2 (by rfl) ⟨706722, by rfl⟩ : syracuseStep 1884593 = 1413445) B1413445
theorem B6373829 : Blo 1116628 6373829 := bstep (se 4 (by rfl) ⟨597546, by rfl⟩ : syracuseStep 6373829 = 1195093) B1195093
theorem B1884721 : Blo 1116628 1884721 := bstep (se 2 (by rfl) ⟨706770, by rfl⟩ : syracuseStep 1884721 = 1413541) B1413541
theorem B1884755 : Blo 1116628 1884755 := bstep (se 1 (by rfl) ⟨1413566, by rfl⟩ : syracuseStep 1884755 = 2827133) B2827133
theorem B2835121 : Blo 1116628 2835121 := bstep (se 2 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 2835121 = 2126341) B2126341
theorem B1884883 : Blo 1116628 1884883 := bstep (se 1 (by rfl) ⟨1413662, by rfl⟩ : syracuseStep 1884883 = 2827325) B2827325
theorem B1885025 : Blo 1116628 1885025 := bstep (se 2 (by rfl) ⟨706884, by rfl⟩ : syracuseStep 1885025 = 1413769) B1413769
theorem B7160717 : Blo 1116628 7160717 := bstep (se 3 (by rfl) ⟨1342634, by rfl⟩ : syracuseStep 7160717 = 2685269) B2685269
theorem B6374285 : Blo 1116628 6374285 := bstep (se 3 (by rfl) ⟨1195178, by rfl⟩ : syracuseStep 6374285 = 2390357) B2390357
theorem B4309937 : Blo 1116628 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B2835395 : Blo 1116628 2835395 := bstep (se 1 (by rfl) ⟨2126546, by rfl⟩ : syracuseStep 2835395 = 4253093) B4253093
theorem B4539341 : Blo 1116628 4539341 := bstep (se 3 (by rfl) ⟨851126, by rfl⟩ : syracuseStep 4539341 = 1702253) B1702253
theorem B3589073 : Blo 1116628 3589073 := bstep (se 2 (by rfl) ⟨1345902, by rfl⟩ : syracuseStep 3589073 = 2691805) B2691805
theorem B1885153 : Blo 1116628 1885153 := bstep (se 2 (by rfl) ⟨706932, by rfl⟩ : syracuseStep 1885153 = 1413865) B1413865
theorem B5653475 : Blo 1116628 5653475 := bstep (se 1 (by rfl) ⟨4240106, by rfl⟩ : syracuseStep 5653475 = 8480213) B8480213
theorem B1885187 : Blo 1116628 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B3589201 : Blo 1116628 3589201 := bstep (se 2 (by rfl) ⟨1345950, by rfl⟩ : syracuseStep 3589201 = 2691901) B2691901
theorem B1885315 : Blo 1116628 1885315 := bstep (se 1 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 1885315 = 2827973) B2827973
theorem B2835587 : Blo 1116628 2835587 := bstep (se 1 (by rfl) ⟨2126690, by rfl⟩ : syracuseStep 2835587 = 4253381) B4253381
theorem B1885457 : Blo 1116628 1885457 := bstep (se 2 (by rfl) ⟨707046, by rfl⟩ : syracuseStep 1885457 = 1414093) B1414093
theorem B1131875 : Blo 1116628 1131875 := bstep (se 1 (by rfl) ⟨848906, by rfl⟩ : syracuseStep 1131875 = 1697813) B1697813
theorem B1590673 : Blo 1116628 1590673 := bstep (se 2 (by rfl) ⟨596502, by rfl⟩ : syracuseStep 1590673 = 1193005) B1193005
theorem B1885585 : Blo 1116628 1885585 := bstep (se 2 (by rfl) ⟨707094, by rfl⟩ : syracuseStep 1885585 = 1414189) B1414189
theorem B1885619 : Blo 1116628 1885619 := bstep (se 1 (by rfl) ⟨1414214, by rfl⟩ : syracuseStep 1885619 = 2828429) B2828429
theorem B1590769 : Blo 1116628 1590769 := bstep (se 2 (by rfl) ⟨596538, by rfl⟩ : syracuseStep 1590769 = 1193077) B1193077
theorem B1885747 : Blo 1116628 1885747 := bstep (se 1 (by rfl) ⟨1414310, by rfl⟩ : syracuseStep 1885747 = 2828621) B2828621
theorem B1885889 : Blo 1116628 1885889 := bstep (se 2 (by rfl) ⟨707208, by rfl⟩ : syracuseStep 1885889 = 1414417) B1414417
theorem B5654285 : Blo 1116628 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B7653133 : Blo 1116628 7653133 := bstep (se 3 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 7653133 = 2869925) B2869925
theorem B1886017 : Blo 1116628 1886017 := bstep (se 2 (by rfl) ⟨707256, by rfl⟩ : syracuseStep 1886017 = 1414513) B1414513
theorem B1886051 : Blo 1116628 1886051 := bstep (se 1 (by rfl) ⟨1414538, by rfl⟩ : syracuseStep 1886051 = 2829077) B2829077
theorem B16107461 : Blo 1116628 16107461 := bstep (se 4 (by rfl) ⟨1510074, by rfl⟩ : syracuseStep 16107461 = 3020149) B3020149
theorem B1591265 : Blo 1116628 1591265 := bstep (se 2 (by rfl) ⟨596724, by rfl⟩ : syracuseStep 1591265 = 1193449) B1193449
theorem B1886179 : Blo 1116628 1886179 := bstep (se 1 (by rfl) ⟨1414634, by rfl⟩ : syracuseStep 1886179 = 2829269) B2829269
theorem B2836529 : Blo 1116628 2836529 := bstep (se 2 (by rfl) ⟨1063698, by rfl⟩ : syracuseStep 2836529 = 2127397) B2127397
theorem B2836579 : Blo 1116628 2836579 := bstep (se 1 (by rfl) ⟨2127434, by rfl⟩ : syracuseStep 2836579 = 4254869) B4254869
theorem B1886321 : Blo 1116628 1886321 := bstep (se 2 (by rfl) ⟨707370, by rfl⟩ : syracuseStep 1886321 = 1414741) B1414741
theorem B7260293 : Blo 1116628 7260293 := bstep (se 4 (by rfl) ⟨680652, by rfl⟩ : syracuseStep 7260293 = 1361305) B1361305
theorem B8505485 : Blo 1116628 8505485 := bstep (se 3 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 8505485 = 3189557) B3189557
theorem B1886449 : Blo 1116628 1886449 := bstep (se 2 (by rfl) ⟨707418, by rfl⟩ : syracuseStep 1886449 = 1414837) B1414837
theorem B1886483 : Blo 1116628 1886483 := bstep (se 1 (by rfl) ⟨1414862, by rfl⟩ : syracuseStep 1886483 = 2829725) B2829725
theorem B2017585 : Blo 1116628 2017585 := bstep (se 2 (by rfl) ⟨756594, by rfl⟩ : syracuseStep 2017585 = 1513189) B1513189
theorem B1886611 : Blo 1116628 1886611 := bstep (se 1 (by rfl) ⟨1414958, by rfl⟩ : syracuseStep 1886611 = 2829917) B2829917
theorem B1886753 : Blo 1116628 1886753 := bstep (se 2 (by rfl) ⟨707532, by rfl⟩ : syracuseStep 1886753 = 1415065) B1415065
theorem B4082275 : Blo 1116628 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B1886881 : Blo 1116628 1886881 := bstep (se 2 (by rfl) ⟨707580, by rfl⟩ : syracuseStep 1886881 = 1415161) B1415161
theorem B1886915 : Blo 1116628 1886915 := bstep (se 1 (by rfl) ⟨1415186, by rfl⟩ : syracuseStep 1886915 = 2830373) B2830373
theorem B1133299 : Blo 1116628 1133299 := bstep (se 1 (by rfl) ⟨849974, by rfl⟩ : syracuseStep 1133299 = 1699949) B1699949
theorem B1592131 : Blo 1116628 1592131 := bstep (se 1 (by rfl) ⟨1194098, by rfl⟩ : syracuseStep 1592131 = 2388197) B2388197
theorem B1887043 : Blo 1116628 1887043 := bstep (se 1 (by rfl) ⟨1415282, by rfl⟩ : syracuseStep 1887043 = 2830565) B2830565
theorem B5098403 : Blo 1116628 5098403 := bstep (se 1 (by rfl) ⟨3823802, by rfl⟩ : syracuseStep 5098403 = 7647605) B7647605
theorem B1592227 : Blo 1116628 1592227 := bstep (se 1 (by rfl) ⟨1194170, by rfl⟩ : syracuseStep 1592227 = 2388341) B2388341
theorem B4770737 : Blo 1116628 4770737 := bstep (se 2 (by rfl) ⟨1789026, by rfl⟩ : syracuseStep 4770737 = 3578053) B3578053
theorem B1887185 : Blo 1116628 1887185 := bstep (se 2 (by rfl) ⟨707694, by rfl⟩ : syracuseStep 1887185 = 1415389) B1415389
theorem B4246577 : Blo 1116628 4246577 := bstep (se 2 (by rfl) ⟨1592466, by rfl⟩ : syracuseStep 4246577 = 3184933) B3184933
theorem B1887313 : Blo 1116628 1887313 := bstep (se 2 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 1887313 = 1415485) B1415485
theorem B1887347 : Blo 1116628 1887347 := bstep (se 1 (by rfl) ⟨1415510, by rfl⟩ : syracuseStep 1887347 = 2831021) B2831021
theorem B1887475 : Blo 1116628 1887475 := bstep (se 1 (by rfl) ⟨1415606, by rfl⟩ : syracuseStep 1887475 = 2831213) B2831213
theorem B1789219 : Blo 1116628 1789219 := bstep (se 1 (by rfl) ⟨1341914, by rfl⟩ : syracuseStep 1789219 = 2683829) B2683829
theorem B1789283 : Blo 1116628 1789283 := bstep (se 1 (by rfl) ⟨1341962, by rfl⟩ : syracuseStep 1789283 = 2683925) B2683925
theorem B1887617 : Blo 1116628 1887617 := bstep (se 2 (by rfl) ⟨707856, by rfl⟩ : syracuseStep 1887617 = 1415713) B1415713
theorem B1592723 : Blo 1116628 1592723 := bstep (se 1 (by rfl) ⟨1194542, by rfl⟩ : syracuseStep 1592723 = 2389085) B2389085
theorem B1887745 : Blo 1116628 1887745 := bstep (se 2 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 1887745 = 1415809) B1415809
theorem B1887779 : Blo 1116628 1887779 := bstep (se 1 (by rfl) ⟨1415834, by rfl⟩ : syracuseStep 1887779 = 2831669) B2831669
theorem B1887907 : Blo 1116628 1887907 := bstep (se 1 (by rfl) ⟨1415930, by rfl⟩ : syracuseStep 1887907 = 2831861) B2831861
theorem B6377201 : Blo 1116628 6377201 := bstep (se 2 (by rfl) ⟨2391450, by rfl⟩ : syracuseStep 6377201 = 4782901) B4782901
theorem B1724147 : Blo 1116628 1724147 := bstep (se 1 (by rfl) ⟨1293110, by rfl⟩ : syracuseStep 1724147 = 2586221) B2586221
theorem B1888049 : Blo 1116628 1888049 := bstep (se 2 (by rfl) ⟨708018, by rfl⟩ : syracuseStep 1888049 = 1416037) B1416037
theorem B3067757 : Blo 1116628 3067757 := bstep (se 3 (by rfl) ⟨575204, by rfl⟩ : syracuseStep 3067757 = 1150409) B1150409
theorem B1888177 : Blo 1116628 1888177 := bstep (se 2 (by rfl) ⟨708066, by rfl⟩ : syracuseStep 1888177 = 1416133) B1416133
theorem B3067843 : Blo 1116628 3067843 := bstep (se 1 (by rfl) ⟨2300882, by rfl⟩ : syracuseStep 3067843 = 4601765) B4601765
theorem B1888211 : Blo 1116628 1888211 := bstep (se 1 (by rfl) ⟨1416158, by rfl⟩ : syracuseStep 1888211 = 2832317) B2832317
theorem B1593361 : Blo 1116628 1593361 := bstep (se 2 (by rfl) ⟨597510, by rfl⟩ : syracuseStep 1593361 = 1195021) B1195021
theorem B1888339 : Blo 1116628 1888339 := bstep (se 1 (by rfl) ⟨1416254, by rfl⟩ : syracuseStep 1888339 = 2832509) B2832509
theorem B1888481 : Blo 1116628 1888481 := bstep (se 2 (by rfl) ⟨708180, by rfl⟩ : syracuseStep 1888481 = 1416361) B1416361
theorem B2150705 : Blo 1116628 2150705 := bstep (se 2 (by rfl) ⟨806514, by rfl⟩ : syracuseStep 2150705 = 1613029) B1613029
theorem B1790257 : Blo 1116628 1790257 := bstep (se 2 (by rfl) ⟨671346, by rfl⟩ : syracuseStep 1790257 = 1342693) B1342693
theorem B1888609 : Blo 1116628 1888609 := bstep (se 2 (by rfl) ⟨708228, by rfl⟩ : syracuseStep 1888609 = 1416457) B1416457
theorem B1593697 : Blo 1116628 1593697 := bstep (se 2 (by rfl) ⟨597636, by rfl⟩ : syracuseStep 1593697 = 1195273) B1195273
theorem B1888643 : Blo 1116628 1888643 := bstep (se 1 (by rfl) ⟨1416482, by rfl⟩ : syracuseStep 1888643 = 2832965) B2832965
theorem B4084145 : Blo 1116628 4084145 := bstep (se 2 (by rfl) ⟨1531554, by rfl⟩ : syracuseStep 4084145 = 3063109) B3063109
theorem B4248035 : Blo 1116628 4248035 := bstep (se 1 (by rfl) ⟨3186026, by rfl⟩ : syracuseStep 4248035 = 6372053) B6372053
theorem B1888771 : Blo 1116628 1888771 := bstep (se 1 (by rfl) ⟨1416578, by rfl⟩ : syracuseStep 1888771 = 2833157) B2833157
theorem B10768909 : Blo 1116628 10768909 := bstep (se 3 (by rfl) ⟨2019170, by rfl⟩ : syracuseStep 10768909 = 4038341) B4038341
theorem B1790513 : Blo 1116628 1790513 := bstep (se 2 (by rfl) ⟨671442, by rfl⟩ : syracuseStep 1790513 = 1342885) B1342885
theorem B4772429 : Blo 1116628 4772429 := bstep (se 3 (by rfl) ⟨894830, by rfl⟩ : syracuseStep 4772429 = 1789661) B1789661
theorem B5657201 : Blo 1116628 5657201 := bstep (se 2 (by rfl) ⟨2121450, by rfl⟩ : syracuseStep 5657201 = 4242901) B4242901
theorem B1888913 : Blo 1116628 1888913 := bstep (se 2 (by rfl) ⟨708342, by rfl⟩ : syracuseStep 1888913 = 1416685) B1416685
theorem B1790705 : Blo 1116628 1790705 := bstep (se 2 (by rfl) ⟨671514, by rfl⟩ : syracuseStep 1790705 = 1343029) B1343029
theorem B1889041 : Blo 1116628 1889041 := bstep (se 2 (by rfl) ⟨708390, by rfl⟩ : syracuseStep 1889041 = 1416781) B1416781
theorem B1889075 : Blo 1116628 1889075 := bstep (se 1 (by rfl) ⟨1416806, by rfl⟩ : syracuseStep 1889075 = 2833613) B2833613
theorem B1594289 : Blo 1116628 1594289 := bstep (se 2 (by rfl) ⟨597858, by rfl⟩ : syracuseStep 1594289 = 1195717) B1195717
theorem B1889203 : Blo 1116628 1889203 := bstep (se 1 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 1889203 = 2833805) B2833805
theorem B8508401 : Blo 1116628 8508401 := bstep (se 2 (by rfl) ⟨3190650, by rfl⟩ : syracuseStep 8508401 = 6381301) B6381301
theorem B1889345 : Blo 1116628 1889345 := bstep (se 2 (by rfl) ⟨708504, by rfl⟩ : syracuseStep 1889345 = 1417009) B1417009
theorem B12735629 : Blo 1116628 12735629 := bstep (se 3 (by rfl) ⟨2387930, by rfl⟩ : syracuseStep 12735629 = 4775861) B4775861
theorem B6378659 : Blo 1116628 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B1889473 : Blo 1116628 1889473 := bstep (se 2 (by rfl) ⟨708552, by rfl⟩ : syracuseStep 1889473 = 1417105) B1417105
theorem B1889507 : Blo 1116628 1889507 := bstep (se 1 (by rfl) ⟨1417130, by rfl⟩ : syracuseStep 1889507 = 2834261) B2834261
theorem B1889635 : Blo 1116628 1889635 := bstep (se 1 (by rfl) ⟨1417226, by rfl⟩ : syracuseStep 1889635 = 2834453) B2834453
theorem B1594819 : Blo 1116628 1594819 := bstep (se 1 (by rfl) ⟨1196114, by rfl⟩ : syracuseStep 1594819 = 2392229) B2392229
theorem B4249037 : Blo 1116628 4249037 := bstep (se 3 (by rfl) ⟨796694, by rfl⟩ : syracuseStep 4249037 = 1593389) B1593389
theorem B1889777 : Blo 1116628 1889777 := bstep (se 2 (by rfl) ⟨708666, by rfl⟩ : syracuseStep 1889777 = 1417333) B1417333
theorem B4085261 : Blo 1116628 4085261 := bstep (se 3 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 4085261 = 1531973) B1531973
theorem B1889905 : Blo 1116628 1889905 := bstep (se 2 (by rfl) ⟨708714, by rfl⟩ : syracuseStep 1889905 = 1417429) B1417429
theorem B2512529 : Blo 1116628 2512529 := bstep (se 2 (by rfl) ⟨942198, by rfl⟩ : syracuseStep 2512529 = 1884397) B1884397
theorem B1889939 : Blo 1116628 1889939 := bstep (se 1 (by rfl) ⟨1417454, by rfl⟩ : syracuseStep 1889939 = 2834909) B2834909
theorem B2512547 : Blo 1116628 2512547 := bstep (se 1 (by rfl) ⟨1884410, by rfl⟩ : syracuseStep 2512547 = 3768821) B3768821
theorem B1890067 : Blo 1116628 1890067 := bstep (se 1 (by rfl) ⟨1417550, by rfl⟩ : syracuseStep 1890067 = 2835101) B2835101
theorem B1595155 : Blo 1116628 1595155 := bstep (se 1 (by rfl) ⟨1196366, by rfl⟩ : syracuseStep 1595155 = 2392733) B2392733
theorem B13588337 : Blo 1116628 13588337 := bstep (se 2 (by rfl) ⟨5095626, by rfl⟩ : syracuseStep 13588337 = 10191253) B10191253
theorem B1890209 : Blo 1116628 1890209 := bstep (se 2 (by rfl) ⟨708828, by rfl⟩ : syracuseStep 1890209 = 1417657) B1417657
theorem B2512817 : Blo 1116628 2512817 := bstep (se 2 (by rfl) ⟨942306, by rfl⟩ : syracuseStep 2512817 = 1884613) B1884613
theorem B2512835 : Blo 1116628 2512835 := bstep (se 1 (by rfl) ⟨1884626, by rfl⟩ : syracuseStep 2512835 = 3769253) B3769253
theorem B1792019 : Blo 1116628 1792019 := bstep (se 1 (by rfl) ⟨1344014, by rfl⟩ : syracuseStep 1792019 = 2688029) B2688029
theorem B1890337 : Blo 1116628 1890337 := bstep (se 2 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 1890337 = 1417753) B1417753
theorem B5658659 : Blo 1116628 5658659 := bstep (se 1 (by rfl) ⟨4243994, by rfl⟩ : syracuseStep 5658659 = 8487989) B8487989
theorem B1890371 : Blo 1116628 1890371 := bstep (se 1 (by rfl) ⟨1417778, by rfl⟩ : syracuseStep 1890371 = 2835557) B2835557
theorem B6379661 : Blo 1116628 6379661 := bstep (se 3 (by rfl) ⟨1196186, by rfl⟩ : syracuseStep 6379661 = 2392373) B2392373
theorem B1890499 : Blo 1116628 1890499 := bstep (se 1 (by rfl) ⟨1417874, by rfl⟩ : syracuseStep 1890499 = 2835749) B2835749
theorem B2513105 : Blo 1116628 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B2513123 : Blo 1116628 2513123 := bstep (se 1 (by rfl) ⟨1884842, by rfl⟩ : syracuseStep 2513123 = 3769685) B3769685
theorem B1792243 : Blo 1116628 1792243 := bstep (se 1 (by rfl) ⟨1344182, by rfl⟩ : syracuseStep 1792243 = 2688365) B2688365
theorem B1792307 : Blo 1116628 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B2873681 : Blo 1116628 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B1890641 : Blo 1116628 1890641 := bstep (se 2 (by rfl) ⟨708990, by rfl⟩ : syracuseStep 1890641 = 1417981) B1417981
theorem B1792435 : Blo 1116628 1792435 := bstep (se 1 (by rfl) ⟨1344326, by rfl⟩ : syracuseStep 1792435 = 2688653) B2688653
theorem B1890769 : Blo 1116628 1890769 := bstep (se 2 (by rfl) ⟨709038, by rfl⟩ : syracuseStep 1890769 = 1418077) B1418077
theorem B2513393 : Blo 1116628 2513393 := bstep (se 2 (by rfl) ⟨942522, by rfl⟩ : syracuseStep 2513393 = 1885045) B1885045
theorem B1890803 : Blo 1116628 1890803 := bstep (se 1 (by rfl) ⟨1418102, by rfl⟩ : syracuseStep 1890803 = 2836205) B2836205
theorem B2513411 : Blo 1116628 2513411 := bstep (se 1 (by rfl) ⟨1885058, by rfl⟩ : syracuseStep 2513411 = 3770117) B3770117
theorem B2873969 : Blo 1116628 2873969 := bstep (se 2 (by rfl) ⟨1077738, by rfl⟩ : syracuseStep 2873969 = 2155477) B2155477
theorem B1890931 : Blo 1116628 1890931 := bstep (se 1 (by rfl) ⟨1418198, by rfl⟩ : syracuseStep 1890931 = 2836397) B2836397
theorem B2513681 : Blo 1116628 2513681 := bstep (se 2 (by rfl) ⟨942630, by rfl⟩ : syracuseStep 2513681 = 1885261) B1885261
theorem B2513699 : Blo 1116628 2513699 := bstep (se 1 (by rfl) ⟨1885274, by rfl⟩ : syracuseStep 2513699 = 3770549) B3770549
theorem B5659469 : Blo 1116628 5659469 := bstep (se 3 (by rfl) ⟨1061150, by rfl⟩ : syracuseStep 5659469 = 2122301) B2122301
theorem B2120593 : Blo 1116628 2120593 := bstep (se 2 (by rfl) ⟨795222, by rfl⟩ : syracuseStep 2120593 = 1590445) B1590445
theorem B2513969 : Blo 1116628 2513969 := bstep (se 2 (by rfl) ⟨942738, by rfl⟩ : syracuseStep 2513969 = 1885477) B1885477
theorem B2513987 : Blo 1116628 2513987 := bstep (se 1 (by rfl) ⟨1885490, by rfl⟩ : syracuseStep 2513987 = 3770981) B3770981
theorem B1793153 : Blo 1116628 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B1793281 : Blo 1116628 1793281 := bstep (se 2 (by rfl) ⟨672480, by rfl⟩ : syracuseStep 1793281 = 1344961) B1344961
theorem B2120995 : Blo 1116628 2120995 := bstep (se 1 (by rfl) ⟨1590746, by rfl⟩ : syracuseStep 2120995 = 3181493) B3181493
theorem B2121041 : Blo 1116628 2121041 := bstep (se 2 (by rfl) ⟨795390, by rfl⟩ : syracuseStep 2121041 = 1590781) B1590781
theorem B2514257 : Blo 1116628 2514257 := bstep (se 2 (by rfl) ⟨942846, by rfl⟩ : syracuseStep 2514257 = 1885693) B1885693
theorem B2514275 : Blo 1116628 2514275 := bstep (se 1 (by rfl) ⟨1885706, by rfl⟩ : syracuseStep 2514275 = 3771413) B3771413
theorem B2907523 : Blo 1116628 2907523 := bstep (se 1 (by rfl) ⟨2180642, by rfl⟩ : syracuseStep 2907523 = 4361285) B4361285
theorem B4251149 : Blo 1116628 4251149 := bstep (se 3 (by rfl) ⟨797090, by rfl⟩ : syracuseStep 4251149 = 1594181) B1594181
theorem B2121329 : Blo 1116628 2121329 := bstep (se 2 (by rfl) ⟨795498, by rfl⟩ : syracuseStep 2121329 = 1590997) B1590997
theorem B2514545 : Blo 1116628 2514545 := bstep (se 2 (by rfl) ⟨942954, by rfl⟩ : syracuseStep 2514545 = 1885909) B1885909
theorem B1793665 : Blo 1116628 1793665 := bstep (se 2 (by rfl) ⟨672624, by rfl⟩ : syracuseStep 1793665 = 1345249) B1345249
theorem B2514563 : Blo 1116628 2514563 := bstep (se 1 (by rfl) ⟨1885922, by rfl⟩ : syracuseStep 2514563 = 3771845) B3771845
theorem B4087523 : Blo 1116628 4087523 := bstep (se 1 (by rfl) ⟨3065642, by rfl⟩ : syracuseStep 4087523 = 6131285) B6131285
theorem B14311181 : Blo 1116628 14311181 := bstep (se 3 (by rfl) ⟨2683346, by rfl⟩ : syracuseStep 14311181 = 5366693) B5366693
theorem B1793921 : Blo 1116628 1793921 := bstep (se 2 (by rfl) ⟨672720, by rfl⟩ : syracuseStep 1793921 = 1345441) B1345441
theorem B2514833 : Blo 1116628 2514833 := bstep (se 2 (by rfl) ⟨943062, by rfl⟩ : syracuseStep 2514833 = 1886125) B1886125
theorem B2514851 : Blo 1116628 2514851 := bstep (se 1 (by rfl) ⟨1886138, by rfl⟩ : syracuseStep 2514851 = 3772277) B3772277
theorem B12738545 : Blo 1116628 12738545 := bstep (se 2 (by rfl) ⟨4776954, by rfl⟩ : syracuseStep 12738545 = 9553909) B9553909
theorem B5234851 : Blo 1116628 5234851 := bstep (se 1 (by rfl) ⟨3926138, by rfl⟩ : syracuseStep 5234851 = 7852277) B7852277
theorem B2515121 : Blo 1116628 2515121 := bstep (se 2 (by rfl) ⟨943170, by rfl⟩ : syracuseStep 2515121 = 1886341) B1886341
theorem B2515139 : Blo 1116628 2515139 := bstep (se 1 (by rfl) ⟨1886354, by rfl⟩ : syracuseStep 2515139 = 3772709) B3772709
theorem B4251953 : Blo 1116628 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B2122051 : Blo 1116628 2122051 := bstep (se 1 (by rfl) ⟨1591538, by rfl⟩ : syracuseStep 2122051 = 3183077) B3183077
theorem B2515409 : Blo 1116628 2515409 := bstep (se 2 (by rfl) ⟨943278, by rfl⟩ : syracuseStep 2515409 = 1886557) B1886557
theorem B2515427 : Blo 1116628 2515427 := bstep (se 1 (by rfl) ⟨1886570, by rfl⟩ : syracuseStep 2515427 = 3773141) B3773141
theorem B2155075 : Blo 1116628 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B2515697 : Blo 1116628 2515697 := bstep (se 2 (by rfl) ⟨943386, by rfl⟩ : syracuseStep 2515697 = 1886773) B1886773
theorem B2122499 : Blo 1116628 2122499 := bstep (se 1 (by rfl) ⟨1591874, by rfl⟩ : syracuseStep 2122499 = 3183749) B3183749
theorem B2515715 : Blo 1116628 2515715 := bstep (se 1 (by rfl) ⟨1886786, by rfl⟩ : syracuseStep 2515715 = 3773573) B3773573
theorem B4776803 : Blo 1116628 4776803 := bstep (se 1 (by rfl) ⟨3582602, by rfl⟩ : syracuseStep 4776803 = 7165205) B7165205
theorem B4252621 : Blo 1116628 4252621 := bstep (se 3 (by rfl) ⟨797366, by rfl⟩ : syracuseStep 4252621 = 1594733) B1594733
theorem B2515985 : Blo 1116628 2515985 := bstep (se 2 (by rfl) ⟨943494, by rfl⟩ : syracuseStep 2515985 = 1886989) B1886989
theorem B2122787 : Blo 1116628 2122787 := bstep (se 1 (by rfl) ⟨1592090, by rfl⟩ : syracuseStep 2122787 = 3184181) B3184181
theorem B2516003 : Blo 1116628 2516003 := bstep (se 1 (by rfl) ⟨1887002, by rfl⟩ : syracuseStep 2516003 = 3774005) B3774005
theorem B7169123 : Blo 1116628 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B2516273 : Blo 1116628 2516273 := bstep (se 2 (by rfl) ⟨943602, by rfl⟩ : syracuseStep 2516273 = 1887205) B1887205
theorem B2516291 : Blo 1116628 2516291 := bstep (se 1 (by rfl) ⟨1887218, by rfl⟩ : syracuseStep 2516291 = 3774437) B3774437
theorem B2385283 : Blo 1116628 2385283 := bstep (se 1 (by rfl) ⟨1788962, by rfl⟩ : syracuseStep 2385283 = 3577925) B3577925
theorem B2516561 : Blo 1116628 2516561 := bstep (se 2 (by rfl) ⟨943710, by rfl⟩ : syracuseStep 2516561 = 1887421) B1887421
theorem B2516579 : Blo 1116628 2516579 := bstep (se 1 (by rfl) ⟨1887434, by rfl⟩ : syracuseStep 2516579 = 3774869) B3774869
theorem B6055523 : Blo 1116628 6055523 := bstep (se 1 (by rfl) ⟨4541642, by rfl⟩ : syracuseStep 6055523 = 9083285) B9083285
theorem B2385539 : Blo 1116628 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B5662385 : Blo 1116628 5662385 := bstep (se 2 (by rfl) ⟨2123394, by rfl⟩ : syracuseStep 5662385 = 4246789) B4246789
theorem B4253411 : Blo 1116628 4253411 := bstep (se 1 (by rfl) ⟨3190058, by rfl⟩ : syracuseStep 4253411 = 6380117) B6380117
theorem B21489461 : Blo 1116628 21489461 := bstep (se 5 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 21489461 = 2014637) B2014637
theorem B2549603 : Blo 1116628 2549603 := bstep (se 1 (by rfl) ⟨1912202, by rfl⟩ : syracuseStep 2549603 = 3824405) B3824405
theorem B2516849 : Blo 1116628 2516849 := bstep (se 2 (by rfl) ⟨943818, by rfl⟩ : syracuseStep 2516849 = 1887637) B1887637
theorem B2516867 : Blo 1116628 2516867 := bstep (se 1 (by rfl) ⟨1887650, by rfl⟩ : syracuseStep 2516867 = 3775301) B3775301
theorem B2123729 : Blo 1116628 2123729 := bstep (se 2 (by rfl) ⟨796398, by rfl⟩ : syracuseStep 2123729 = 1592797) B1592797
theorem B2517137 : Blo 1116628 2517137 := bstep (se 2 (by rfl) ⟨943926, by rfl⟩ : syracuseStep 2517137 = 1887853) B1887853
theorem B2517155 : Blo 1116628 2517155 := bstep (se 1 (by rfl) ⟨1887866, by rfl⟩ : syracuseStep 2517155 = 3775733) B3775733
theorem B64481507 : Blo 1116628 64481507 := bstep (se 1 (by rfl) ⟨48361130, by rfl⟩ : syracuseStep 64481507 = 96722261) B96722261
theorem B7170353 : Blo 1116628 7170353 := bstep (se 2 (by rfl) ⟨2688882, by rfl⟩ : syracuseStep 7170353 = 5377765) B5377765
theorem B4254065 : Blo 1116628 4254065 := bstep (se 2 (by rfl) ⟨1595274, by rfl⟩ : syracuseStep 4254065 = 3190549) B3190549
theorem B2517425 : Blo 1116628 2517425 := bstep (se 2 (by rfl) ⟨944034, by rfl⟩ : syracuseStep 2517425 = 1888069) B1888069
theorem B6056369 : Blo 1116628 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B2517443 : Blo 1116628 2517443 := bstep (se 1 (by rfl) ⟨1888082, by rfl⟩ : syracuseStep 2517443 = 3776165) B3776165
theorem B6121925 : Blo 1116628 6121925 := bstep (se 4 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 6121925 = 1147861) B1147861
theorem B27191861 : Blo 1116628 27191861 := bstep (se 5 (by rfl) ⟨1274618, by rfl⟩ : syracuseStep 27191861 = 2549237) B2549237
theorem B2419267 : Blo 1116628 2419267 := bstep (se 1 (by rfl) ⟨1814450, by rfl⟩ : syracuseStep 2419267 = 3628901) B3628901
theorem B2386513 : Blo 1116628 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B2517713 : Blo 1116628 2517713 := bstep (se 2 (by rfl) ⟨944142, by rfl⟩ : syracuseStep 2517713 = 1888285) B1888285
theorem B2517731 : Blo 1116628 2517731 := bstep (se 1 (by rfl) ⟨1888298, by rfl⟩ : syracuseStep 2517731 = 3776597) B3776597
theorem B4025123 : Blo 1116628 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B4778801 : Blo 1116628 4778801 := bstep (se 2 (by rfl) ⟨1792050, by rfl⟩ : syracuseStep 4778801 = 3584101) B3584101
theorem B2124625 : Blo 1116628 2124625 := bstep (se 2 (by rfl) ⟨796734, by rfl⟩ : syracuseStep 2124625 = 1593469) B1593469
theorem B5368675 : Blo 1116628 5368675 := bstep (se 1 (by rfl) ⟨4026506, by rfl⟩ : syracuseStep 5368675 = 8053013) B8053013
theorem B4025251 : Blo 1116628 4025251 := bstep (se 1 (by rfl) ⟨3018938, by rfl⟩ : syracuseStep 4025251 = 6037877) B6037877
theorem B2518001 : Blo 1116628 2518001 := bstep (se 2 (by rfl) ⟨944250, by rfl⟩ : syracuseStep 2518001 = 1888501) B1888501
theorem B2124785 : Blo 1116628 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B2518019 : Blo 1116628 2518019 := bstep (se 1 (by rfl) ⟨1888514, by rfl⟩ : syracuseStep 2518019 = 3777029) B3777029
theorem B5663843 : Blo 1116628 5663843 := bstep (se 1 (by rfl) ⟨4247882, by rfl⟩ : syracuseStep 5663843 = 8495765) B8495765
theorem B2387171 : Blo 1116628 2387171 := bstep (se 1 (by rfl) ⟨1790378, by rfl⟩ : syracuseStep 2387171 = 3580757) B3580757
theorem B2551025 : Blo 1116628 2551025 := bstep (se 2 (by rfl) ⟨956634, by rfl⟩ : syracuseStep 2551025 = 1913269) B1913269
theorem B2518289 : Blo 1116628 2518289 := bstep (se 2 (by rfl) ⟨944358, by rfl⟩ : syracuseStep 2518289 = 1888717) B1888717
theorem B2518307 : Blo 1116628 2518307 := bstep (se 1 (by rfl) ⟨1888730, by rfl⟩ : syracuseStep 2518307 = 3777461) B3777461
theorem B4025713 : Blo 1116628 4025713 := bstep (se 2 (by rfl) ⟨1509642, by rfl⟩ : syracuseStep 4025713 = 3019285) B3019285
theorem B1699187 : Blo 1116628 1699187 := bstep (se 1 (by rfl) ⟨1274390, by rfl⟩ : syracuseStep 1699187 = 2548781) B2548781
theorem B2125187 : Blo 1116628 2125187 := bstep (se 1 (by rfl) ⟨1593890, by rfl⟩ : syracuseStep 2125187 = 3187781) B3187781
theorem B19131875 : Blo 1116628 19131875 := bstep (se 1 (by rfl) ⟨14348906, by rfl⟩ : syracuseStep 19131875 = 28697813) B28697813
theorem B3403313 : Blo 1116628 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B2518577 : Blo 1116628 2518577 := bstep (se 2 (by rfl) ⟨944466, by rfl⟩ : syracuseStep 2518577 = 1888933) B1888933
theorem B2518595 : Blo 1116628 2518595 := bstep (se 1 (by rfl) ⟨1888946, by rfl⟩ : syracuseStep 2518595 = 3777893) B3777893
theorem B6811397 : Blo 1116628 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B2518865 : Blo 1116628 2518865 := bstep (se 2 (by rfl) ⟨944574, by rfl⟩ : syracuseStep 2518865 = 1889149) B1889149
theorem B2518883 : Blo 1116628 2518883 := bstep (se 1 (by rfl) ⟨1889162, by rfl⟩ : syracuseStep 2518883 = 3778325) B3778325
theorem B5664653 : Blo 1116628 5664653 := bstep (se 3 (by rfl) ⟨1062122, by rfl⟩ : syracuseStep 5664653 = 2124245) B2124245
theorem B5369905 : Blo 1116628 5369905 := bstep (se 2 (by rfl) ⟨2013714, by rfl⟩ : syracuseStep 5369905 = 4027429) B4027429
theorem B2388017 : Blo 1116628 2388017 := bstep (se 2 (by rfl) ⟨895506, by rfl⟩ : syracuseStep 2388017 = 1791013) B1791013
theorem B54521909 : Blo 1116628 54521909 := bstep (se 5 (by rfl) ⟨2555714, by rfl⟩ : syracuseStep 54521909 = 5111429) B5111429
theorem B2519153 : Blo 1116628 2519153 := bstep (se 2 (by rfl) ⟨944682, by rfl⟩ : syracuseStep 2519153 = 1889365) B1889365
theorem B2519171 : Blo 1116628 2519171 := bstep (se 1 (by rfl) ⟨1889378, by rfl⟩ : syracuseStep 2519171 = 3778757) B3778757
theorem B2126083 : Blo 1116628 2126083 := bstep (se 1 (by rfl) ⟨1594562, by rfl⟩ : syracuseStep 2126083 = 3189125) B3189125
theorem B2519441 : Blo 1116628 2519441 := bstep (se 2 (by rfl) ⟨944790, by rfl⟩ : syracuseStep 2519441 = 1889581) B1889581
theorem B2519459 : Blo 1116628 2519459 := bstep (se 1 (by rfl) ⟨1889594, by rfl⟩ : syracuseStep 2519459 = 3779189) B3779189
theorem B2126243 : Blo 1116628 2126243 := bstep (se 1 (by rfl) ⟨1594682, by rfl⟩ : syracuseStep 2126243 = 3189365) B3189365
theorem B2519729 : Blo 1116628 2519729 := bstep (se 2 (by rfl) ⟨944898, by rfl⟩ : syracuseStep 2519729 = 1889797) B1889797
theorem B2519747 : Blo 1116628 2519747 := bstep (se 1 (by rfl) ⟨1889810, by rfl⟩ : syracuseStep 2519747 = 3779621) B3779621
theorem B16151237 : Blo 1116628 16151237 := bstep (se 4 (by rfl) ⟨1514178, by rfl⟩ : syracuseStep 16151237 = 3028357) B3028357
theorem B7172813 : Blo 1116628 7172813 := bstep (se 3 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 7172813 = 2689805) B2689805
theorem B22999949 : Blo 1116628 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B2520017 : Blo 1116628 2520017 := bstep (se 2 (by rfl) ⟨945006, by rfl⟩ : syracuseStep 2520017 = 1890013) B1890013
theorem B2520035 : Blo 1116628 2520035 := bstep (se 1 (by rfl) ⟨1890026, by rfl⟩ : syracuseStep 2520035 = 3780053) B3780053
theorem B4781261 : Blo 1116628 4781261 := bstep (se 3 (by rfl) ⟨896486, by rfl⟩ : syracuseStep 4781261 = 1792973) B1792973
theorem B10188017 : Blo 1116628 10188017 := bstep (se 2 (by rfl) ⟨3820506, by rfl⟩ : syracuseStep 10188017 = 7641013) B7641013
theorem B2520305 : Blo 1116628 2520305 := bstep (se 2 (by rfl) ⟨945114, by rfl⟩ : syracuseStep 2520305 = 1890229) B1890229
theorem B2520323 : Blo 1116628 2520323 := bstep (se 1 (by rfl) ⟨1890242, by rfl⟩ : syracuseStep 2520323 = 3780485) B3780485
theorem B2127313 : Blo 1116628 2127313 := bstep (se 2 (by rfl) ⟨797742, by rfl⟩ : syracuseStep 2127313 = 1595485) B1595485
theorem B2520593 : Blo 1116628 2520593 := bstep (se 2 (by rfl) ⟨945222, by rfl⟩ : syracuseStep 2520593 = 1890445) B1890445
theorem B2520611 : Blo 1116628 2520611 := bstep (se 1 (by rfl) ⟨1890458, by rfl⟩ : syracuseStep 2520611 = 3780917) B3780917
theorem B1701523 : Blo 1116628 1701523 := bstep (se 1 (by rfl) ⟨1276142, by rfl⟩ : syracuseStep 1701523 = 2552285) B2552285
theorem B2520881 : Blo 1116628 2520881 := bstep (se 2 (by rfl) ⟨945330, by rfl⟩ : syracuseStep 2520881 = 1890661) B1890661
theorem B2520899 : Blo 1116628 2520899 := bstep (se 1 (by rfl) ⟨1890674, by rfl⟩ : syracuseStep 2520899 = 3781349) B3781349
theorem B1275731 : Blo 1116628 1275731 := bstep (se 1 (by rfl) ⟨956798, by rfl⟩ : syracuseStep 1275731 = 1913597) B1913597
theorem B2684771 : Blo 1116628 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B9074531 : Blo 1116628 9074531 := bstep (se 1 (by rfl) ⟨6805898, by rfl⟩ : syracuseStep 9074531 = 13611797) B13611797
theorem B2521169 : Blo 1116628 2521169 := bstep (se 2 (by rfl) ⟨945438, by rfl⟩ : syracuseStep 2521169 = 1890877) B1890877
theorem B2521187 : Blo 1116628 2521187 := bstep (se 1 (by rfl) ⟨1890890, by rfl⟩ : syracuseStep 2521187 = 3781781) B3781781
theorem B2685059 : Blo 1116628 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B2586865 : Blo 1116628 2586865 := bstep (se 2 (by rfl) ⟨970074, by rfl⟩ : syracuseStep 2586865 = 1940149) B1940149
theorem B1341827 : Blo 1116628 1341827 := bstep (se 1 (by rfl) ⟨1006370, by rfl⟩ : syracuseStep 1341827 = 2012741) B2012741
theorem B5667569 : Blo 1116628 5667569 := bstep (se 2 (by rfl) ⟨2125338, by rfl⟩ : syracuseStep 5667569 = 4250677) B4250677
theorem B4782833 : Blo 1116628 4782833 := bstep (se 2 (by rfl) ⟨1793562, by rfl⟩ : syracuseStep 4782833 = 3587125) B3587125
theorem B2390801 : Blo 1116628 2390801 := bstep (se 2 (by rfl) ⟨896550, by rfl⟩ : syracuseStep 2390801 = 1793101) B1793101
theorem B3406769 : Blo 1116628 3406769 := bstep (se 2 (by rfl) ⟨1277538, by rfl⟩ : syracuseStep 3406769 = 2555077) B2555077
theorem B21756869 : Blo 1116628 21756869 := bstep (se 4 (by rfl) ⟨2039706, by rfl⟩ : syracuseStep 21756869 = 4079413) B4079413
theorem B2685905 : Blo 1116628 2685905 := bstep (se 2 (by rfl) ⟨1007214, by rfl⟩ : syracuseStep 2685905 = 2014429) B2014429
theorem B24476813 : Blo 1116628 24476813 := bstep (se 3 (by rfl) ⟨4589402, by rfl⟩ : syracuseStep 24476813 = 9178805) B9178805
theorem B4848781 : Blo 1116628 4848781 := bstep (se 3 (by rfl) ⟨909146, by rfl⟩ : syracuseStep 4848781 = 1818293) B1818293
theorem B3833027 : Blo 1116628 3833027 := bstep (se 1 (by rfl) ⟨2874770, by rfl⟩ : syracuseStep 3833027 = 5749541) B5749541
theorem B1211603 : Blo 1116628 1211603 := bstep (se 1 (by rfl) ⟨908702, by rfl⟩ : syracuseStep 1211603 = 1817405) B1817405
theorem B2686193 : Blo 1116628 2686193 := bstep (se 2 (by rfl) ⟨1007322, by rfl⟩ : syracuseStep 2686193 = 2014645) B2014645
theorem B3407107 : Blo 1116628 3407107 := bstep (se 1 (by rfl) ⟨2555330, by rfl⟩ : syracuseStep 3407107 = 5110661) B5110661
theorem B3833219 : Blo 1116628 3833219 := bstep (se 1 (by rfl) ⟨2874914, by rfl⟩ : syracuseStep 3833219 = 5749829) B5749829
theorem B2686385 : Blo 1116628 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B3833315 : Blo 1116628 3833315 := bstep (se 1 (by rfl) ⟨2874986, by rfl⟩ : syracuseStep 3833315 = 5749973) B5749973
theorem B5373809 : Blo 1116628 5373809 := bstep (se 2 (by rfl) ⟨2015178, by rfl⟩ : syracuseStep 5373809 = 4030357) B4030357
theorem B5734475 : Blo 1116628 5734475 := bstep (se 1 (by rfl) ⟨4300856, by rfl⟩ : syracuseStep 5734475 = 8601713) B8601713
theorem B10747997 : Blo 1116628 10747997 := bstep (se 3 (by rfl) ⟨2015249, by rfl⟩ : syracuseStep 10747997 = 4030499) B4030499
theorem B2392715 : Blo 1116628 2392715 := bstep (se 1 (by rfl) ⟨1794536, by rfl⟩ : syracuseStep 2392715 = 3589073) B3589073
theorem B3768983 : Blo 1116628 3768983 := bstep (se 1 (by rfl) ⟨2826737, by rfl⟩ : syracuseStep 3768983 = 5653475) B5653475
theorem B27919205 : Blo 1116628 27919205 := bstep (se 4 (by rfl) ⟨2617425, by rfl⟩ : syracuseStep 27919205 = 5234851) B5234851
theorem B9307237 : Blo 1116628 9307237 := bstep (se 4 (by rfl) ⟨872553, by rfl⟩ : syracuseStep 9307237 = 1745107) B1745107
theorem B3769523 : Blo 1116628 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B5670161 : Blo 1116628 5670161 := bstep (se 2 (by rfl) ⟨2126310, by rfl⟩ : syracuseStep 5670161 = 4252621) B4252621
theorem B5670323 : Blo 1116628 5670323 := bstep (se 1 (by rfl) ⟨4252742, by rfl⟩ : syracuseStep 5670323 = 8505485) B8505485
theorem B3769793 : Blo 1116628 3769793 := bstep (se 2 (by rfl) ⟨1413672, by rfl⟩ : syracuseStep 3769793 = 2827345) B2827345
theorem B4785601 : Blo 1116628 4785601 := bstep (se 2 (by rfl) ⟨1794600, by rfl⟩ : syracuseStep 4785601 = 3589201) B3589201
theorem B3180377 : Blo 1116628 3180377 := bstep (se 2 (by rfl) ⟨1192641, by rfl⟩ : syracuseStep 3180377 = 2385283) B2385283
theorem B4032401 : Blo 1116628 4032401 := bstep (se 2 (by rfl) ⟨1512150, by rfl⟩ : syracuseStep 4032401 = 3024301) B3024301
theorem B3180491 : Blo 1116628 3180491 := bstep (se 1 (by rfl) ⟨2385368, by rfl⟩ : syracuseStep 3180491 = 4770737) B4770737
theorem B3770333 : Blo 1116628 3770333 := bstep (se 3 (by rfl) ⟨706937, by rfl⟩ : syracuseStep 3770333 = 1413875) B1413875
theorem B1116631 : Blo 1116628 1116631 := bstep (se 1 (by rfl) ⟨837473, by rfl⟩ : syracuseStep 1116631 = 1674947) B1674947
theorem B1116651 : Blo 1116628 1116651 := bstep (se 1 (by rfl) ⟨837488, by rfl⟩ : syracuseStep 1116651 = 1674977) B1674977
theorem B1116663 : Blo 1116628 1116663 := bstep (se 1 (by rfl) ⟨837497, by rfl⟩ : syracuseStep 1116663 = 1674995) B1674995
theorem B1149431 : Blo 1116628 1149431 := bstep (se 1 (by rfl) ⟨862073, by rfl⟩ : syracuseStep 1149431 = 1724147) B1724147
theorem B1116683 : Blo 1116628 1116683 := bstep (se 1 (by rfl) ⟨837512, by rfl⟩ : syracuseStep 1116683 = 1675025) B1675025
theorem B1116695 : Blo 1116628 1116695 := bstep (se 1 (by rfl) ⟨837521, by rfl⟩ : syracuseStep 1116695 = 1675043) B1675043
theorem B1116715 : Blo 1116628 1116715 := bstep (se 1 (by rfl) ⟨837536, by rfl⟩ : syracuseStep 1116715 = 1675073) B1675073
theorem B1116727 : Blo 1116628 1116727 := bstep (se 1 (by rfl) ⟨837545, by rfl⟩ : syracuseStep 1116727 = 1675091) B1675091
theorem B1116747 : Blo 1116628 1116747 := bstep (se 1 (by rfl) ⟨837560, by rfl⟩ : syracuseStep 1116747 = 1675121) B1675121
theorem B1116759 : Blo 1116628 1116759 := bstep (se 1 (by rfl) ⟨837569, by rfl⟩ : syracuseStep 1116759 = 1675139) B1675139
theorem B43027037 : Blo 1116628 43027037 := bstep (se 3 (by rfl) ⟨8067569, by rfl⟩ : syracuseStep 43027037 = 16135139) B16135139
theorem B1116779 : Blo 1116628 1116779 := bstep (se 1 (by rfl) ⟨837584, by rfl⟩ : syracuseStep 1116779 = 1675169) B1675169
theorem B1116791 : Blo 1116628 1116791 := bstep (se 1 (by rfl) ⟨837593, by rfl⟩ : syracuseStep 1116791 = 1675187) B1675187
theorem B1116811 : Blo 1116628 1116811 := bstep (se 1 (by rfl) ⟨837608, by rfl⟩ : syracuseStep 1116811 = 1675217) B1675217
theorem B1116823 : Blo 1116628 1116823 := bstep (se 1 (by rfl) ⟨837617, by rfl⟩ : syracuseStep 1116823 = 1675235) B1675235
theorem B1116843 : Blo 1116628 1116843 := bstep (se 1 (by rfl) ⟨837632, by rfl⟩ : syracuseStep 1116843 = 1675265) B1675265
theorem B1116855 : Blo 1116628 1116855 := bstep (se 1 (by rfl) ⟨837641, by rfl⟩ : syracuseStep 1116855 = 1675283) B1675283
theorem B1116875 : Blo 1116628 1116875 := bstep (se 1 (by rfl) ⟨837656, by rfl⟩ : syracuseStep 1116875 = 1675313) B1675313
theorem B1116887 : Blo 1116628 1116887 := bstep (se 1 (by rfl) ⟨837665, by rfl⟩ : syracuseStep 1116887 = 1675331) B1675331
theorem B1116907 : Blo 1116628 1116907 := bstep (se 1 (by rfl) ⟨837680, by rfl⟩ : syracuseStep 1116907 = 1675361) B1675361
theorem B1116919 : Blo 1116628 1116919 := bstep (se 1 (by rfl) ⟨837689, by rfl⟩ : syracuseStep 1116919 = 1675379) B1675379
theorem B1116939 : Blo 1116628 1116939 := bstep (se 1 (by rfl) ⟨837704, by rfl⟩ : syracuseStep 1116939 = 1675409) B1675409
theorem B1116951 : Blo 1116628 1116951 := bstep (se 1 (by rfl) ⟨837713, by rfl⟩ : syracuseStep 1116951 = 1675427) B1675427
theorem B1116971 : Blo 1116628 1116971 := bstep (se 1 (by rfl) ⟨837728, by rfl⟩ : syracuseStep 1116971 = 1675457) B1675457
theorem B1116983 : Blo 1116628 1116983 := bstep (se 1 (by rfl) ⟨837737, by rfl⟩ : syracuseStep 1116983 = 1675475) B1675475
theorem B1117003 : Blo 1116628 1117003 := bstep (se 1 (by rfl) ⟨837752, by rfl⟩ : syracuseStep 1117003 = 1675505) B1675505
theorem B1117015 : Blo 1116628 1117015 := bstep (se 1 (by rfl) ⟨837761, by rfl⟩ : syracuseStep 1117015 = 1675523) B1675523
theorem B1117035 : Blo 1116628 1117035 := bstep (se 1 (by rfl) ⟨837776, by rfl⟩ : syracuseStep 1117035 = 1675553) B1675553
theorem B1117047 : Blo 1116628 1117047 := bstep (se 1 (by rfl) ⟨837785, by rfl⟩ : syracuseStep 1117047 = 1675571) B1675571
theorem B1117067 : Blo 1116628 1117067 := bstep (se 1 (by rfl) ⟨837800, by rfl⟩ : syracuseStep 1117067 = 1675601) B1675601
theorem B1117079 : Blo 1116628 1117079 := bstep (se 1 (by rfl) ⟨837809, by rfl⟩ : syracuseStep 1117079 = 1675619) B1675619
theorem B1117099 : Blo 1116628 1117099 := bstep (se 1 (by rfl) ⟨837824, by rfl⟩ : syracuseStep 1117099 = 1675649) B1675649
theorem B1117111 : Blo 1116628 1117111 := bstep (se 1 (by rfl) ⟨837833, by rfl⟩ : syracuseStep 1117111 = 1675667) B1675667
theorem B1117131 : Blo 1116628 1117131 := bstep (se 1 (by rfl) ⟨837848, by rfl⟩ : syracuseStep 1117131 = 1675697) B1675697
theorem B2722763 : Blo 1116628 2722763 := bstep (se 1 (by rfl) ⟨2042072, by rfl⟩ : syracuseStep 2722763 = 4084145) B4084145
theorem B8489933 : Blo 1116628 8489933 := bstep (se 3 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 8489933 = 3183725) B3183725
theorem B1117143 : Blo 1116628 1117143 := bstep (se 1 (by rfl) ⟨837857, by rfl⟩ : syracuseStep 1117143 = 1675715) B1675715
theorem B1117163 : Blo 1116628 1117163 := bstep (se 1 (by rfl) ⟨837872, by rfl⟩ : syracuseStep 1117163 = 1675745) B1675745
theorem B1117175 : Blo 1116628 1117175 := bstep (se 1 (by rfl) ⟨837881, by rfl⟩ : syracuseStep 1117175 = 1675763) B1675763
theorem B1117195 : Blo 1116628 1117195 := bstep (se 1 (by rfl) ⟨837896, by rfl⟩ : syracuseStep 1117195 = 1675793) B1675793
theorem B1117207 : Blo 1116628 1117207 := bstep (se 1 (by rfl) ⟨837905, by rfl⟩ : syracuseStep 1117207 = 1675811) B1675811
theorem B1117227 : Blo 1116628 1117227 := bstep (se 1 (by rfl) ⟨837920, by rfl⟩ : syracuseStep 1117227 = 1675841) B1675841
theorem B3181619 : Blo 1116628 3181619 := bstep (se 1 (by rfl) ⟨2386214, by rfl⟩ : syracuseStep 3181619 = 4772429) B4772429
theorem B1117239 : Blo 1116628 1117239 := bstep (se 1 (by rfl) ⟨837929, by rfl⟩ : syracuseStep 1117239 = 1675859) B1675859
theorem B2690113 : Blo 1116628 2690113 := bstep (se 2 (by rfl) ⟨1008792, by rfl⟩ : syracuseStep 2690113 = 2017585) B2017585
theorem B1117259 : Blo 1116628 1117259 := bstep (se 1 (by rfl) ⟨837944, by rfl⟩ : syracuseStep 1117259 = 1675889) B1675889
theorem B3771467 : Blo 1116628 3771467 := bstep (se 1 (by rfl) ⟨2828600, by rfl⟩ : syracuseStep 3771467 = 5657201) B5657201
theorem B1117271 : Blo 1116628 1117271 := bstep (se 1 (by rfl) ⟨837953, by rfl⟩ : syracuseStep 1117271 = 1675907) B1675907
theorem B1117291 : Blo 1116628 1117291 := bstep (se 1 (by rfl) ⟨837968, by rfl⟩ : syracuseStep 1117291 = 1675937) B1675937
theorem B1117303 : Blo 1116628 1117303 := bstep (se 1 (by rfl) ⟨837977, by rfl⟩ : syracuseStep 1117303 = 1675955) B1675955
theorem B1117323 : Blo 1116628 1117323 := bstep (se 1 (by rfl) ⟨837992, by rfl⟩ : syracuseStep 1117323 = 1675985) B1675985
theorem B1117335 : Blo 1116628 1117335 := bstep (se 1 (by rfl) ⟨838001, by rfl⟩ : syracuseStep 1117335 = 1676003) B1676003
theorem B1117355 : Blo 1116628 1117355 := bstep (se 1 (by rfl) ⟨838016, by rfl⟩ : syracuseStep 1117355 = 1676033) B1676033
theorem B1117367 : Blo 1116628 1117367 := bstep (se 1 (by rfl) ⟨838025, by rfl⟩ : syracuseStep 1117367 = 1676051) B1676051
theorem B1117387 : Blo 1116628 1117387 := bstep (se 1 (by rfl) ⟨838040, by rfl⟩ : syracuseStep 1117387 = 1676081) B1676081
theorem B1117399 : Blo 1116628 1117399 := bstep (se 1 (by rfl) ⟨838049, by rfl⟩ : syracuseStep 1117399 = 1676099) B1676099
theorem B1117419 : Blo 1116628 1117419 := bstep (se 1 (by rfl) ⟨838064, by rfl⟩ : syracuseStep 1117419 = 1676129) B1676129
theorem B1117431 : Blo 1116628 1117431 := bstep (se 1 (by rfl) ⟨838073, by rfl⟩ : syracuseStep 1117431 = 1676147) B1676147
theorem B1117451 : Blo 1116628 1117451 := bstep (se 1 (by rfl) ⟨838088, by rfl⟩ : syracuseStep 1117451 = 1676177) B1676177
theorem B1117463 : Blo 1116628 1117463 := bstep (se 1 (by rfl) ⟨838097, by rfl⟩ : syracuseStep 1117463 = 1676195) B1676195
theorem B1117483 : Blo 1116628 1117483 := bstep (se 1 (by rfl) ⟨838112, by rfl⟩ : syracuseStep 1117483 = 1676225) B1676225
theorem B1117495 : Blo 1116628 1117495 := bstep (se 1 (by rfl) ⟨838121, by rfl⟩ : syracuseStep 1117495 = 1676243) B1676243
theorem B1117515 : Blo 1116628 1117515 := bstep (se 1 (by rfl) ⟨838136, by rfl⟩ : syracuseStep 1117515 = 1676273) B1676273
theorem B5672267 : Blo 1116628 5672267 := bstep (se 1 (by rfl) ⟨4254200, by rfl⟩ : syracuseStep 5672267 = 8508401) B8508401
theorem B1117527 : Blo 1116628 1117527 := bstep (se 1 (by rfl) ⟨838145, by rfl⟩ : syracuseStep 1117527 = 1676291) B1676291
theorem B3771737 : Blo 1116628 3771737 := bstep (se 2 (by rfl) ⟨1414401, by rfl⟩ : syracuseStep 3771737 = 2828803) B2828803
theorem B1117547 : Blo 1116628 1117547 := bstep (se 1 (by rfl) ⟨838160, by rfl⟩ : syracuseStep 1117547 = 1676321) B1676321
theorem B1117559 : Blo 1116628 1117559 := bstep (se 1 (by rfl) ⟨838169, by rfl⟩ : syracuseStep 1117559 = 1676339) B1676339
theorem B1117579 : Blo 1116628 1117579 := bstep (se 1 (by rfl) ⟨838184, by rfl⟩ : syracuseStep 1117579 = 1676369) B1676369
theorem B1117591 : Blo 1116628 1117591 := bstep (se 1 (by rfl) ⟨838193, by rfl⟩ : syracuseStep 1117591 = 1676387) B1676387
theorem B1117611 : Blo 1116628 1117611 := bstep (se 1 (by rfl) ⟨838208, by rfl⟩ : syracuseStep 1117611 = 1676417) B1676417
theorem B8490419 : Blo 1116628 8490419 := bstep (se 1 (by rfl) ⟨6367814, by rfl⟩ : syracuseStep 8490419 = 12735629) B12735629
theorem B1117623 : Blo 1116628 1117623 := bstep (se 1 (by rfl) ⟨838217, by rfl⟩ : syracuseStep 1117623 = 1676435) B1676435
theorem B3182017 : Blo 1116628 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B1117643 : Blo 1116628 1117643 := bstep (se 1 (by rfl) ⟨838232, by rfl⟩ : syracuseStep 1117643 = 1676465) B1676465
theorem B1117655 : Blo 1116628 1117655 := bstep (se 1 (by rfl) ⟨838241, by rfl⟩ : syracuseStep 1117655 = 1676483) B1676483
theorem B5443033 : Blo 1116628 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B1117675 : Blo 1116628 1117675 := bstep (se 1 (by rfl) ⟨838256, by rfl⟩ : syracuseStep 1117675 = 1676513) B1676513
theorem B1117687 : Blo 1116628 1117687 := bstep (se 1 (by rfl) ⟨838265, by rfl⟩ : syracuseStep 1117687 = 1676531) B1676531
theorem B1117707 : Blo 1116628 1117707 := bstep (se 1 (by rfl) ⟨838280, by rfl⟩ : syracuseStep 1117707 = 1676561) B1676561
theorem B1117719 : Blo 1116628 1117719 := bstep (se 1 (by rfl) ⟨838289, by rfl⟩ : syracuseStep 1117719 = 1676579) B1676579
theorem B1117739 : Blo 1116628 1117739 := bstep (se 1 (by rfl) ⟨838304, by rfl⟩ : syracuseStep 1117739 = 1676609) B1676609
theorem B1117751 : Blo 1116628 1117751 := bstep (se 1 (by rfl) ⟨838313, by rfl⟩ : syracuseStep 1117751 = 1676627) B1676627
theorem B1117771 : Blo 1116628 1117771 := bstep (se 1 (by rfl) ⟨838328, by rfl⟩ : syracuseStep 1117771 = 1676657) B1676657
theorem B1117783 : Blo 1116628 1117783 := bstep (se 1 (by rfl) ⟨838337, by rfl⟩ : syracuseStep 1117783 = 1676675) B1676675
theorem B1117803 : Blo 1116628 1117803 := bstep (se 1 (by rfl) ⟨838352, by rfl⟩ : syracuseStep 1117803 = 1676705) B1676705
theorem B1117815 : Blo 1116628 1117815 := bstep (se 1 (by rfl) ⟨838361, by rfl⟩ : syracuseStep 1117815 = 1676723) B1676723
theorem B6360707 : Blo 1116628 6360707 := bstep (se 1 (by rfl) ⟨4770530, by rfl⟩ : syracuseStep 6360707 = 9541061) B9541061
theorem B1117835 : Blo 1116628 1117835 := bstep (se 1 (by rfl) ⟨838376, by rfl⟩ : syracuseStep 1117835 = 1676753) B1676753
theorem B1117847 : Blo 1116628 1117847 := bstep (se 1 (by rfl) ⟨838385, by rfl⟩ : syracuseStep 1117847 = 1676771) B1676771
theorem B1511065 : Blo 1116628 1511065 := bstep (se 2 (by rfl) ⟨566649, by rfl⟩ : syracuseStep 1511065 = 1133299) B1133299
theorem B1117867 : Blo 1116628 1117867 := bstep (se 1 (by rfl) ⟨838400, by rfl⟩ : syracuseStep 1117867 = 1676801) B1676801
theorem B2723507 : Blo 1116628 2723507 := bstep (se 1 (by rfl) ⟨2042630, by rfl⟩ : syracuseStep 2723507 = 4085261) B4085261
theorem B1117879 : Blo 1116628 1117879 := bstep (se 1 (by rfl) ⟨838409, by rfl⟩ : syracuseStep 1117879 = 1676819) B1676819
theorem B1117899 : Blo 1116628 1117899 := bstep (se 1 (by rfl) ⟨838424, by rfl⟩ : syracuseStep 1117899 = 1676849) B1676849
theorem B1117911 : Blo 1116628 1117911 := bstep (se 1 (by rfl) ⟨838433, by rfl⟩ : syracuseStep 1117911 = 1676867) B1676867
theorem B1117931 : Blo 1116628 1117931 := bstep (se 1 (by rfl) ⟨838448, by rfl⟩ : syracuseStep 1117931 = 1676897) B1676897
theorem B1117943 : Blo 1116628 1117943 := bstep (se 1 (by rfl) ⟨838457, by rfl⟩ : syracuseStep 1117943 = 1676915) B1676915
theorem B1675019 : Blo 1116628 1675019 := bstep (se 1 (by rfl) ⟨1256264, by rfl⟩ : syracuseStep 1675019 = 2512529) B2512529
theorem B1117963 : Blo 1116628 1117963 := bstep (se 1 (by rfl) ⟨838472, by rfl⟩ : syracuseStep 1117963 = 1676945) B1676945
theorem B1675031 : Blo 1116628 1675031 := bstep (se 1 (by rfl) ⟨1256273, by rfl⟩ : syracuseStep 1675031 = 2512547) B2512547
theorem B1117975 : Blo 1116628 1117975 := bstep (se 1 (by rfl) ⟨838481, by rfl⟩ : syracuseStep 1117975 = 1676963) B1676963
theorem B1117995 : Blo 1116628 1117995 := bstep (se 1 (by rfl) ⟨838496, by rfl⟩ : syracuseStep 1117995 = 1676993) B1676993
theorem B1118007 : Blo 1116628 1118007 := bstep (se 1 (by rfl) ⟨838505, by rfl⟩ : syracuseStep 1118007 = 1677011) B1677011
theorem B1118027 : Blo 1116628 1118027 := bstep (se 1 (by rfl) ⟨838520, by rfl⟩ : syracuseStep 1118027 = 1677041) B1677041
theorem B1118039 : Blo 1116628 1118039 := bstep (se 1 (by rfl) ⟨838529, by rfl⟩ : syracuseStep 1118039 = 1677059) B1677059
theorem B1675097 : Blo 1116628 1675097 := bstep (se 2 (by rfl) ⟨628161, by rfl⟩ : syracuseStep 1675097 = 1256323) B1256323
theorem B4034393 : Blo 1116628 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B30609251 : Blo 1116628 30609251 := bstep (se 1 (by rfl) ⟨22956938, by rfl⟩ : syracuseStep 30609251 = 45913877) B45913877
theorem B1118059 : Blo 1116628 1118059 := bstep (se 1 (by rfl) ⟨838544, by rfl⟩ : syracuseStep 1118059 = 1677089) B1677089
theorem B18124661 : Blo 1116628 18124661 := bstep (se 5 (by rfl) ⟨849593, by rfl⟩ : syracuseStep 18124661 = 1699187) B1699187
theorem B1118071 : Blo 1116628 1118071 := bstep (se 1 (by rfl) ⟨838553, by rfl⟩ : syracuseStep 1118071 = 1677107) B1677107
theorem B1118091 : Blo 1116628 1118091 := bstep (se 1 (by rfl) ⟨838568, by rfl⟩ : syracuseStep 1118091 = 1677137) B1677137
theorem B1118103 : Blo 1116628 1118103 := bstep (se 1 (by rfl) ⟨838577, by rfl⟩ : syracuseStep 1118103 = 1677155) B1677155
theorem B1118123 : Blo 1116628 1118123 := bstep (se 1 (by rfl) ⟨838592, by rfl⟩ : syracuseStep 1118123 = 1677185) B1677185
theorem B1118135 : Blo 1116628 1118135 := bstep (se 1 (by rfl) ⟨838601, by rfl⟩ : syracuseStep 1118135 = 1677203) B1677203
theorem B2723777 : Blo 1116628 2723777 := bstep (se 2 (by rfl) ⟨1021416, by rfl⟩ : syracuseStep 2723777 = 2042833) B2042833
theorem B1675211 : Blo 1116628 1675211 := bstep (se 1 (by rfl) ⟨1256408, by rfl⟩ : syracuseStep 1675211 = 2512817) B2512817
theorem B1118155 : Blo 1116628 1118155 := bstep (se 1 (by rfl) ⟨838616, by rfl⟩ : syracuseStep 1118155 = 1677233) B1677233
theorem B1675223 : Blo 1116628 1675223 := bstep (se 1 (by rfl) ⟨1256417, by rfl⟩ : syracuseStep 1675223 = 2512835) B2512835
theorem B1118167 : Blo 1116628 1118167 := bstep (se 1 (by rfl) ⟨838625, by rfl⟩ : syracuseStep 1118167 = 1677251) B1677251
theorem B1118187 : Blo 1116628 1118187 := bstep (se 1 (by rfl) ⟨838640, by rfl⟩ : syracuseStep 1118187 = 1677281) B1677281
theorem B1118199 : Blo 1116628 1118199 := bstep (se 1 (by rfl) ⟨838649, by rfl⟩ : syracuseStep 1118199 = 1677299) B1677299
theorem B1118219 : Blo 1116628 1118219 := bstep (se 1 (by rfl) ⟨838664, by rfl⟩ : syracuseStep 1118219 = 1677329) B1677329
theorem B3772439 : Blo 1116628 3772439 := bstep (se 1 (by rfl) ⟨2829329, by rfl⟩ : syracuseStep 3772439 = 5658659) B5658659
theorem B1118231 : Blo 1116628 1118231 := bstep (se 1 (by rfl) ⟨838673, by rfl⟩ : syracuseStep 1118231 = 1677347) B1677347
theorem B1675289 : Blo 1116628 1675289 := bstep (se 2 (by rfl) ⟨628233, by rfl⟩ : syracuseStep 1675289 = 1256467) B1256467
theorem B1118251 : Blo 1116628 1118251 := bstep (se 1 (by rfl) ⟨838688, by rfl⟩ : syracuseStep 1118251 = 1677377) B1677377
theorem B1118263 : Blo 1116628 1118263 := bstep (se 1 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 1118263 = 1677395) B1677395
theorem B6361163 : Blo 1116628 6361163 := bstep (se 1 (by rfl) ⟨4770872, by rfl⟩ : syracuseStep 6361163 = 9541745) B9541745
theorem B1118283 : Blo 1116628 1118283 := bstep (se 1 (by rfl) ⟨838712, by rfl⟩ : syracuseStep 1118283 = 1677425) B1677425
theorem B1118295 : Blo 1116628 1118295 := bstep (se 1 (by rfl) ⟨838721, by rfl⟩ : syracuseStep 1118295 = 1677443) B1677443
theorem B1118315 : Blo 1116628 1118315 := bstep (se 1 (by rfl) ⟨838736, by rfl⟩ : syracuseStep 1118315 = 1677473) B1677473
theorem B1118327 : Blo 1116628 1118327 := bstep (se 1 (by rfl) ⟨838745, by rfl⟩ : syracuseStep 1118327 = 1677491) B1677491
theorem B1675403 : Blo 1116628 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B1118347 : Blo 1116628 1118347 := bstep (se 1 (by rfl) ⟨838760, by rfl⟩ : syracuseStep 1118347 = 1677521) B1677521
theorem B1675415 : Blo 1116628 1675415 := bstep (se 1 (by rfl) ⟨1256561, by rfl⟩ : syracuseStep 1675415 = 2513123) B2513123
theorem B1118359 : Blo 1116628 1118359 := bstep (se 1 (by rfl) ⟨838769, by rfl⟩ : syracuseStep 1118359 = 1677539) B1677539
theorem B1118379 : Blo 1116628 1118379 := bstep (se 1 (by rfl) ⟨838784, by rfl⟩ : syracuseStep 1118379 = 1677569) B1677569
theorem B1118391 : Blo 1116628 1118391 := bstep (se 1 (by rfl) ⟨838793, by rfl⟩ : syracuseStep 1118391 = 1677587) B1677587
theorem B1118411 : Blo 1116628 1118411 := bstep (se 1 (by rfl) ⟨838808, by rfl⟩ : syracuseStep 1118411 = 1677617) B1677617
theorem B1511627 : Blo 1116628 1511627 := bstep (se 1 (by rfl) ⟨1133720, by rfl⟩ : syracuseStep 1511627 = 2267441) B2267441
theorem B1118423 : Blo 1116628 1118423 := bstep (se 1 (by rfl) ⟨838817, by rfl⟩ : syracuseStep 1118423 = 1677635) B1677635
theorem B1675481 : Blo 1116628 1675481 := bstep (se 2 (by rfl) ⟨628305, by rfl⟩ : syracuseStep 1675481 = 1256611) B1256611
theorem B1118443 : Blo 1116628 1118443 := bstep (se 1 (by rfl) ⟨838832, by rfl⟩ : syracuseStep 1118443 = 1677665) B1677665
theorem B1118455 : Blo 1116628 1118455 := bstep (se 1 (by rfl) ⟨838841, by rfl⟩ : syracuseStep 1118455 = 1677683) B1677683
theorem B1118475 : Blo 1116628 1118475 := bstep (se 1 (by rfl) ⟨838856, by rfl⟩ : syracuseStep 1118475 = 1677713) B1677713
theorem B1118487 : Blo 1116628 1118487 := bstep (se 1 (by rfl) ⟨838865, by rfl⟩ : syracuseStep 1118487 = 1677731) B1677731
theorem B1118507 : Blo 1116628 1118507 := bstep (se 1 (by rfl) ⟨838880, by rfl⟩ : syracuseStep 1118507 = 1677761) B1677761
theorem B1118519 : Blo 1116628 1118519 := bstep (se 1 (by rfl) ⟨838889, by rfl⟩ : syracuseStep 1118519 = 1677779) B1677779
theorem B1675595 : Blo 1116628 1675595 := bstep (se 1 (by rfl) ⟨1256696, by rfl⟩ : syracuseStep 1675595 = 2513393) B2513393
theorem B1118539 : Blo 1116628 1118539 := bstep (se 1 (by rfl) ⟨838904, by rfl⟩ : syracuseStep 1118539 = 1677809) B1677809
theorem B1675607 : Blo 1116628 1675607 := bstep (se 1 (by rfl) ⟨1256705, by rfl⟩ : syracuseStep 1675607 = 2513411) B2513411
theorem B1118551 : Blo 1116628 1118551 := bstep (se 1 (by rfl) ⟨838913, by rfl⟩ : syracuseStep 1118551 = 1677827) B1677827
theorem B1118571 : Blo 1116628 1118571 := bstep (se 1 (by rfl) ⟨838928, by rfl⟩ : syracuseStep 1118571 = 1677857) B1677857
theorem B1118583 : Blo 1116628 1118583 := bstep (se 1 (by rfl) ⟨838937, by rfl⟩ : syracuseStep 1118583 = 1677875) B1677875
theorem B1118603 : Blo 1116628 1118603 := bstep (se 1 (by rfl) ⟨838952, by rfl⟩ : syracuseStep 1118603 = 1677905) B1677905
theorem B1118615 : Blo 1116628 1118615 := bstep (se 1 (by rfl) ⟨838961, by rfl⟩ : syracuseStep 1118615 = 1677923) B1677923
theorem B1675673 : Blo 1116628 1675673 := bstep (se 2 (by rfl) ⟨628377, by rfl⟩ : syracuseStep 1675673 = 1256755) B1256755
theorem B1118635 : Blo 1116628 1118635 := bstep (se 1 (by rfl) ⟨838976, by rfl⟩ : syracuseStep 1118635 = 1677953) B1677953
theorem B1118647 : Blo 1116628 1118647 := bstep (se 1 (by rfl) ⟨838985, by rfl⟩ : syracuseStep 1118647 = 1677971) B1677971
theorem B1118667 : Blo 1116628 1118667 := bstep (se 1 (by rfl) ⟨839000, by rfl⟩ : syracuseStep 1118667 = 1678001) B1678001
theorem B1118679 : Blo 1116628 1118679 := bstep (se 1 (by rfl) ⟨839009, by rfl⟩ : syracuseStep 1118679 = 1678019) B1678019
theorem B1118699 : Blo 1116628 1118699 := bstep (se 1 (by rfl) ⟨839024, by rfl⟩ : syracuseStep 1118699 = 1678049) B1678049
theorem B1118711 : Blo 1116628 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B1675787 : Blo 1116628 1675787 := bstep (se 1 (by rfl) ⟨1256840, by rfl⟩ : syracuseStep 1675787 = 2513681) B2513681
theorem B1118731 : Blo 1116628 1118731 := bstep (se 1 (by rfl) ⟨839048, by rfl⟩ : syracuseStep 1118731 = 1678097) B1678097
theorem B1675799 : Blo 1116628 1675799 := bstep (se 1 (by rfl) ⟨1256849, by rfl⟩ : syracuseStep 1675799 = 2513699) B2513699
theorem B1118743 : Blo 1116628 1118743 := bstep (se 1 (by rfl) ⟨839057, by rfl⟩ : syracuseStep 1118743 = 1678115) B1678115
theorem B1118763 : Blo 1116628 1118763 := bstep (se 1 (by rfl) ⟨839072, by rfl⟩ : syracuseStep 1118763 = 1678145) B1678145
theorem B3772979 : Blo 1116628 3772979 := bstep (se 1 (by rfl) ⟨2829734, by rfl⟩ : syracuseStep 3772979 = 5659469) B5659469
theorem B1118775 : Blo 1116628 1118775 := bstep (se 1 (by rfl) ⟨839081, by rfl⟩ : syracuseStep 1118775 = 1678163) B1678163
theorem B1118795 : Blo 1116628 1118795 := bstep (se 1 (by rfl) ⟨839096, by rfl⟩ : syracuseStep 1118795 = 1678193) B1678193
theorem B1118807 : Blo 1116628 1118807 := bstep (se 1 (by rfl) ⟨839105, by rfl⟩ : syracuseStep 1118807 = 1678211) B1678211
theorem B1675865 : Blo 1116628 1675865 := bstep (se 2 (by rfl) ⟨628449, by rfl⟩ : syracuseStep 1675865 = 1256899) B1256899
theorem B1118827 : Blo 1116628 1118827 := bstep (se 1 (by rfl) ⟨839120, by rfl⟩ : syracuseStep 1118827 = 1678241) B1678241
theorem B1118839 : Blo 1116628 1118839 := bstep (se 1 (by rfl) ⟨839129, by rfl⟩ : syracuseStep 1118839 = 1678259) B1678259
theorem B1118859 : Blo 1116628 1118859 := bstep (se 1 (by rfl) ⟨839144, by rfl⟩ : syracuseStep 1118859 = 1678289) B1678289
theorem B1118871 : Blo 1116628 1118871 := bstep (se 1 (by rfl) ⟨839153, by rfl⟩ : syracuseStep 1118871 = 1678307) B1678307
theorem B1118891 : Blo 1116628 1118891 := bstep (se 1 (by rfl) ⟨839168, by rfl⟩ : syracuseStep 1118891 = 1678337) B1678337
theorem B1118903 : Blo 1116628 1118903 := bstep (se 1 (by rfl) ⟨839177, by rfl⟩ : syracuseStep 1118903 = 1678355) B1678355
theorem B1675979 : Blo 1116628 1675979 := bstep (se 1 (by rfl) ⟨1256984, by rfl⟩ : syracuseStep 1675979 = 2513969) B2513969
theorem B1118923 : Blo 1116628 1118923 := bstep (se 1 (by rfl) ⟨839192, by rfl⟩ : syracuseStep 1118923 = 1678385) B1678385
theorem B1675991 : Blo 1116628 1675991 := bstep (se 1 (by rfl) ⟨1256993, by rfl⟩ : syracuseStep 1675991 = 2513987) B2513987
theorem B1118935 : Blo 1116628 1118935 := bstep (se 1 (by rfl) ⟨839201, by rfl⟩ : syracuseStep 1118935 = 1678403) B1678403
theorem B1118955 : Blo 1116628 1118955 := bstep (se 1 (by rfl) ⟨839216, by rfl⟩ : syracuseStep 1118955 = 1678433) B1678433
theorem B1118967 : Blo 1116628 1118967 := bstep (se 1 (by rfl) ⟨839225, by rfl⟩ : syracuseStep 1118967 = 1678451) B1678451
theorem B1118987 : Blo 1116628 1118987 := bstep (se 1 (by rfl) ⟨839240, by rfl⟩ : syracuseStep 1118987 = 1678481) B1678481
theorem B1118999 : Blo 1116628 1118999 := bstep (se 1 (by rfl) ⟨839249, by rfl⟩ : syracuseStep 1118999 = 1678499) B1678499
theorem B1676057 : Blo 1116628 1676057 := bstep (se 2 (by rfl) ⟨628521, by rfl⟩ : syracuseStep 1676057 = 1257043) B1257043
theorem B1119019 : Blo 1116628 1119019 := bstep (se 1 (by rfl) ⟨839264, by rfl⟩ : syracuseStep 1119019 = 1678529) B1678529
theorem B1119031 : Blo 1116628 1119031 := bstep (se 1 (by rfl) ⟨839273, by rfl⟩ : syracuseStep 1119031 = 1678547) B1678547
theorem B3773249 : Blo 1116628 3773249 := bstep (se 2 (by rfl) ⟨1414968, by rfl⟩ : syracuseStep 3773249 = 2829937) B2829937
theorem B5378881 : Blo 1116628 5378881 := bstep (se 2 (by rfl) ⟨2017080, by rfl⟩ : syracuseStep 5378881 = 4034161) B4034161
theorem B1119051 : Blo 1116628 1119051 := bstep (se 1 (by rfl) ⟨839288, by rfl⟩ : syracuseStep 1119051 = 1678577) B1678577
theorem B1119063 : Blo 1116628 1119063 := bstep (se 1 (by rfl) ⟨839297, by rfl⟩ : syracuseStep 1119063 = 1678595) B1678595
theorem B8491877 : Blo 1116628 8491877 := bstep (se 4 (by rfl) ⟨796113, by rfl⟩ : syracuseStep 8491877 = 1592227) B1592227
theorem B1119083 : Blo 1116628 1119083 := bstep (se 1 (by rfl) ⟨839312, by rfl⟩ : syracuseStep 1119083 = 1678625) B1678625
theorem B1119095 : Blo 1116628 1119095 := bstep (se 1 (by rfl) ⟨839321, by rfl⟩ : syracuseStep 1119095 = 1678643) B1678643
theorem B1414027 : Blo 1116628 1414027 := bstep (se 1 (by rfl) ⟨1060520, by rfl⟩ : syracuseStep 1414027 = 2121041) B2121041
theorem B1676171 : Blo 1116628 1676171 := bstep (se 1 (by rfl) ⟨1257128, by rfl⟩ : syracuseStep 1676171 = 2514257) B2514257
theorem B1119115 : Blo 1116628 1119115 := bstep (se 1 (by rfl) ⟨839336, by rfl⟩ : syracuseStep 1119115 = 1678673) B1678673
theorem B1676183 : Blo 1116628 1676183 := bstep (se 1 (by rfl) ⟨1257137, by rfl⟩ : syracuseStep 1676183 = 2514275) B2514275
theorem B1119127 : Blo 1116628 1119127 := bstep (se 1 (by rfl) ⟨839345, by rfl⟩ : syracuseStep 1119127 = 1678691) B1678691
theorem B1119147 : Blo 1116628 1119147 := bstep (se 1 (by rfl) ⟨839360, by rfl⟩ : syracuseStep 1119147 = 1678721) B1678721
theorem B5378995 : Blo 1116628 5378995 := bstep (se 1 (by rfl) ⟨4034246, by rfl⟩ : syracuseStep 5378995 = 8068493) B8068493
theorem B1119159 : Blo 1116628 1119159 := bstep (se 1 (by rfl) ⟨839369, by rfl⟩ : syracuseStep 1119159 = 1678739) B1678739
theorem B1119179 : Blo 1116628 1119179 := bstep (se 1 (by rfl) ⟨839384, by rfl⟩ : syracuseStep 1119179 = 1678769) B1678769
theorem B1119191 : Blo 1116628 1119191 := bstep (se 1 (by rfl) ⟨839393, by rfl⟩ : syracuseStep 1119191 = 1678787) B1678787
theorem B1676249 : Blo 1116628 1676249 := bstep (se 2 (by rfl) ⟨628593, by rfl⟩ : syracuseStep 1676249 = 1257187) B1257187
theorem B1119211 : Blo 1116628 1119211 := bstep (se 1 (by rfl) ⟨839408, by rfl⟩ : syracuseStep 1119211 = 1678817) B1678817
theorem B1119223 : Blo 1116628 1119223 := bstep (se 1 (by rfl) ⟨839417, by rfl⟩ : syracuseStep 1119223 = 1678835) B1678835
theorem B1119243 : Blo 1116628 1119243 := bstep (se 1 (by rfl) ⟨839432, by rfl⟩ : syracuseStep 1119243 = 1678865) B1678865
theorem B1119255 : Blo 1116628 1119255 := bstep (se 1 (by rfl) ⟨839441, by rfl⟩ : syracuseStep 1119255 = 1678883) B1678883
theorem B1119275 : Blo 1116628 1119275 := bstep (se 1 (by rfl) ⟨839456, by rfl⟩ : syracuseStep 1119275 = 1678913) B1678913
theorem B1119287 : Blo 1116628 1119287 := bstep (se 1 (by rfl) ⟨839465, by rfl⟩ : syracuseStep 1119287 = 1678931) B1678931
theorem B1676363 : Blo 1116628 1676363 := bstep (se 1 (by rfl) ⟨1257272, by rfl⟩ : syracuseStep 1676363 = 2514545) B2514545
theorem B1119307 : Blo 1116628 1119307 := bstep (se 1 (by rfl) ⟨839480, by rfl⟩ : syracuseStep 1119307 = 1678961) B1678961
theorem B1676375 : Blo 1116628 1676375 := bstep (se 1 (by rfl) ⟨1257281, by rfl⟩ : syracuseStep 1676375 = 2514563) B2514563
theorem B1119319 : Blo 1116628 1119319 := bstep (se 1 (by rfl) ⟨839489, by rfl⟩ : syracuseStep 1119319 = 1678979) B1678979
theorem B1119339 : Blo 1116628 1119339 := bstep (se 1 (by rfl) ⟨839504, by rfl⟩ : syracuseStep 1119339 = 1679009) B1679009
theorem B1119351 : Blo 1116628 1119351 := bstep (se 1 (by rfl) ⟨839513, by rfl⟩ : syracuseStep 1119351 = 1679027) B1679027
theorem B1119371 : Blo 1116628 1119371 := bstep (se 1 (by rfl) ⟨839528, by rfl⟩ : syracuseStep 1119371 = 1679057) B1679057
theorem B2725015 : Blo 1116628 2725015 := bstep (se 1 (by rfl) ⟨2043761, by rfl⟩ : syracuseStep 2725015 = 4087523) B4087523
theorem B1119383 : Blo 1116628 1119383 := bstep (se 1 (by rfl) ⟨839537, by rfl⟩ : syracuseStep 1119383 = 1679075) B1679075
theorem B1676441 : Blo 1116628 1676441 := bstep (se 2 (by rfl) ⟨628665, by rfl⟩ : syracuseStep 1676441 = 1257331) B1257331
theorem B1119403 : Blo 1116628 1119403 := bstep (se 1 (by rfl) ⟨839552, by rfl⟩ : syracuseStep 1119403 = 1679105) B1679105
theorem B9540787 : Blo 1116628 9540787 := bstep (se 1 (by rfl) ⟨7155590, by rfl⟩ : syracuseStep 9540787 = 14311181) B14311181
theorem B1119415 : Blo 1116628 1119415 := bstep (se 1 (by rfl) ⟨839561, by rfl⟩ : syracuseStep 1119415 = 1679123) B1679123
theorem B1119435 : Blo 1116628 1119435 := bstep (se 1 (by rfl) ⟨839576, by rfl⟩ : syracuseStep 1119435 = 1679153) B1679153
theorem B1119447 : Blo 1116628 1119447 := bstep (se 1 (by rfl) ⟨839585, by rfl⟩ : syracuseStep 1119447 = 1679171) B1679171
theorem B1119467 : Blo 1116628 1119467 := bstep (se 1 (by rfl) ⟨839600, by rfl⟩ : syracuseStep 1119467 = 1679201) B1679201
theorem B1119479 : Blo 1116628 1119479 := bstep (se 1 (by rfl) ⟨839609, by rfl⟩ : syracuseStep 1119479 = 1679219) B1679219
theorem B1676555 : Blo 1116628 1676555 := bstep (se 1 (by rfl) ⟨1257416, by rfl⟩ : syracuseStep 1676555 = 2514833) B2514833
theorem B1119499 : Blo 1116628 1119499 := bstep (se 1 (by rfl) ⟨839624, by rfl⟩ : syracuseStep 1119499 = 1679249) B1679249
theorem B1676567 : Blo 1116628 1676567 := bstep (se 1 (by rfl) ⟨1257425, by rfl⟩ : syracuseStep 1676567 = 2514851) B2514851
theorem B1119511 : Blo 1116628 1119511 := bstep (se 1 (by rfl) ⟨839633, by rfl⟩ : syracuseStep 1119511 = 1679267) B1679267
theorem B1119531 : Blo 1116628 1119531 := bstep (se 1 (by rfl) ⟨839648, by rfl⟩ : syracuseStep 1119531 = 1679297) B1679297
theorem B1119543 : Blo 1116628 1119543 := bstep (se 1 (by rfl) ⟨839657, by rfl⟩ : syracuseStep 1119543 = 1679315) B1679315
theorem B3020107 : Blo 1116628 3020107 := bstep (se 1 (by rfl) ⟨2265080, by rfl⟩ : syracuseStep 3020107 = 4530161) B4530161
theorem B8492363 : Blo 1116628 8492363 := bstep (se 1 (by rfl) ⟨6369272, by rfl⟩ : syracuseStep 8492363 = 12738545) B12738545
theorem B1119563 : Blo 1116628 1119563 := bstep (se 1 (by rfl) ⟨839672, by rfl⟩ : syracuseStep 1119563 = 1679345) B1679345
theorem B1119575 : Blo 1116628 1119575 := bstep (se 1 (by rfl) ⟨839681, by rfl⟩ : syracuseStep 1119575 = 1679363) B1679363
theorem B1676633 : Blo 1116628 1676633 := bstep (se 2 (by rfl) ⟨628737, by rfl⟩ : syracuseStep 1676633 = 1257475) B1257475
theorem B3773789 : Blo 1116628 3773789 := bstep (se 3 (by rfl) ⟨707585, by rfl⟩ : syracuseStep 3773789 = 1415171) B1415171
theorem B1119595 : Blo 1116628 1119595 := bstep (se 1 (by rfl) ⟨839696, by rfl⟩ : syracuseStep 1119595 = 1679393) B1679393
theorem B1119607 : Blo 1116628 1119607 := bstep (se 1 (by rfl) ⟨839705, by rfl⟩ : syracuseStep 1119607 = 1679411) B1679411
theorem B1119627 : Blo 1116628 1119627 := bstep (se 1 (by rfl) ⟨839720, by rfl⟩ : syracuseStep 1119627 = 1679441) B1679441
theorem B1119639 : Blo 1116628 1119639 := bstep (se 1 (by rfl) ⟨839729, by rfl⟩ : syracuseStep 1119639 = 1679459) B1679459
theorem B1119659 : Blo 1116628 1119659 := bstep (se 1 (by rfl) ⟨839744, by rfl⟩ : syracuseStep 1119659 = 1679489) B1679489
theorem B1119671 : Blo 1116628 1119671 := bstep (se 1 (by rfl) ⟨839753, by rfl⟩ : syracuseStep 1119671 = 1679507) B1679507
theorem B1676747 : Blo 1116628 1676747 := bstep (se 1 (by rfl) ⟨1257560, by rfl⟩ : syracuseStep 1676747 = 2515121) B2515121
theorem B1119691 : Blo 1116628 1119691 := bstep (se 1 (by rfl) ⟨839768, by rfl⟩ : syracuseStep 1119691 = 1679537) B1679537
theorem B1676759 : Blo 1116628 1676759 := bstep (se 1 (by rfl) ⟨1257569, by rfl⟩ : syracuseStep 1676759 = 2515139) B2515139
theorem B1119703 : Blo 1116628 1119703 := bstep (se 1 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 1119703 = 1679555) B1679555
theorem B1119723 : Blo 1116628 1119723 := bstep (se 1 (by rfl) ⟨839792, by rfl⟩ : syracuseStep 1119723 = 1679585) B1679585
theorem B1119735 : Blo 1116628 1119735 := bstep (se 1 (by rfl) ⟨839801, by rfl⟩ : syracuseStep 1119735 = 1679603) B1679603
theorem B1119755 : Blo 1116628 1119755 := bstep (se 1 (by rfl) ⟨839816, by rfl⟩ : syracuseStep 1119755 = 1679633) B1679633
theorem B1119767 : Blo 1116628 1119767 := bstep (se 1 (by rfl) ⟨839825, by rfl⟩ : syracuseStep 1119767 = 1679651) B1679651
theorem B1676825 : Blo 1116628 1676825 := bstep (se 2 (by rfl) ⟨628809, by rfl⟩ : syracuseStep 1676825 = 1257619) B1257619
theorem B1119787 : Blo 1116628 1119787 := bstep (se 1 (by rfl) ⟨839840, by rfl⟩ : syracuseStep 1119787 = 1679681) B1679681
theorem B1119799 : Blo 1116628 1119799 := bstep (se 1 (by rfl) ⟨839849, by rfl⟩ : syracuseStep 1119799 = 1679699) B1679699
theorem B1119819 : Blo 1116628 1119819 := bstep (se 1 (by rfl) ⟨839864, by rfl⟩ : syracuseStep 1119819 = 1679729) B1679729
theorem B1119831 : Blo 1116628 1119831 := bstep (se 1 (by rfl) ⟨839873, by rfl⟩ : syracuseStep 1119831 = 1679747) B1679747
theorem B1119851 : Blo 1116628 1119851 := bstep (se 1 (by rfl) ⟨839888, by rfl⟩ : syracuseStep 1119851 = 1679777) B1679777
theorem B1119863 : Blo 1116628 1119863 := bstep (se 1 (by rfl) ⟨839897, by rfl⟩ : syracuseStep 1119863 = 1679795) B1679795
theorem B1676939 : Blo 1116628 1676939 := bstep (se 1 (by rfl) ⟨1257704, by rfl⟩ : syracuseStep 1676939 = 2515409) B2515409
theorem B1119883 : Blo 1116628 1119883 := bstep (se 1 (by rfl) ⟨839912, by rfl⟩ : syracuseStep 1119883 = 1679825) B1679825
theorem B1676951 : Blo 1116628 1676951 := bstep (se 1 (by rfl) ⟨1257713, by rfl⟩ : syracuseStep 1676951 = 2515427) B2515427
theorem B1119895 : Blo 1116628 1119895 := bstep (se 1 (by rfl) ⟨839921, by rfl⟩ : syracuseStep 1119895 = 1679843) B1679843
theorem B1119915 : Blo 1116628 1119915 := bstep (se 1 (by rfl) ⟨839936, by rfl⟩ : syracuseStep 1119915 = 1679873) B1679873
theorem B1119927 : Blo 1116628 1119927 := bstep (se 1 (by rfl) ⟨839945, by rfl⟩ : syracuseStep 1119927 = 1679891) B1679891
theorem B1119947 : Blo 1116628 1119947 := bstep (se 1 (by rfl) ⟨839960, by rfl⟩ : syracuseStep 1119947 = 1679921) B1679921
theorem B1119959 : Blo 1116628 1119959 := bstep (se 1 (by rfl) ⟨839969, by rfl⟩ : syracuseStep 1119959 = 1679939) B1679939
theorem B1677017 : Blo 1116628 1677017 := bstep (se 2 (by rfl) ⟨628881, by rfl⟩ : syracuseStep 1677017 = 1257763) B1257763
theorem B1119979 : Blo 1116628 1119979 := bstep (se 1 (by rfl) ⟨839984, by rfl⟩ : syracuseStep 1119979 = 1679969) B1679969
theorem B1119991 : Blo 1116628 1119991 := bstep (se 1 (by rfl) ⟨839993, by rfl⟩ : syracuseStep 1119991 = 1679987) B1679987
theorem B1120011 : Blo 1116628 1120011 := bstep (se 1 (by rfl) ⟨840008, by rfl⟩ : syracuseStep 1120011 = 1680017) B1680017
theorem B1120023 : Blo 1116628 1120023 := bstep (se 1 (by rfl) ⟨840017, by rfl⟩ : syracuseStep 1120023 = 1680035) B1680035
theorem B1120043 : Blo 1116628 1120043 := bstep (se 1 (by rfl) ⟨840032, by rfl⟩ : syracuseStep 1120043 = 1680065) B1680065
theorem B1120055 : Blo 1116628 1120055 := bstep (se 1 (by rfl) ⟨840041, by rfl⟩ : syracuseStep 1120055 = 1680083) B1680083
theorem B1677131 : Blo 1116628 1677131 := bstep (se 1 (by rfl) ⟨1257848, by rfl⟩ : syracuseStep 1677131 = 2515697) B2515697
theorem B1120075 : Blo 1116628 1120075 := bstep (se 1 (by rfl) ⟨840056, by rfl⟩ : syracuseStep 1120075 = 1680113) B1680113
theorem B1414999 : Blo 1116628 1414999 := bstep (se 1 (by rfl) ⟨1061249, by rfl⟩ : syracuseStep 1414999 = 2122499) B2122499
theorem B1677143 : Blo 1116628 1677143 := bstep (se 1 (by rfl) ⟨1257857, by rfl⟩ : syracuseStep 1677143 = 2515715) B2515715
theorem B1120087 : Blo 1116628 1120087 := bstep (se 1 (by rfl) ⟨840065, by rfl⟩ : syracuseStep 1120087 = 1680131) B1680131
theorem B1120107 : Blo 1116628 1120107 := bstep (se 1 (by rfl) ⟨840080, by rfl⟩ : syracuseStep 1120107 = 1680161) B1680161
theorem B1120119 : Blo 1116628 1120119 := bstep (se 1 (by rfl) ⟨840089, by rfl⟩ : syracuseStep 1120119 = 1680179) B1680179
theorem B1120139 : Blo 1116628 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B3184535 : Blo 1116628 3184535 := bstep (se 1 (by rfl) ⟨2388401, by rfl⟩ : syracuseStep 3184535 = 4776803) B4776803
theorem B1120151 : Blo 1116628 1120151 := bstep (se 1 (by rfl) ⟨840113, by rfl⟩ : syracuseStep 1120151 = 1680227) B1680227
theorem B1677209 : Blo 1116628 1677209 := bstep (se 2 (by rfl) ⟨628953, by rfl⟩ : syracuseStep 1677209 = 1257907) B1257907
theorem B1120171 : Blo 1116628 1120171 := bstep (se 1 (by rfl) ⟨840128, by rfl⟩ : syracuseStep 1120171 = 1680257) B1680257
theorem B1120183 : Blo 1116628 1120183 := bstep (se 1 (by rfl) ⟨840137, by rfl⟩ : syracuseStep 1120183 = 1680275) B1680275
theorem B1120203 : Blo 1116628 1120203 := bstep (se 1 (by rfl) ⟨840152, by rfl⟩ : syracuseStep 1120203 = 1680305) B1680305
theorem B1120215 : Blo 1116628 1120215 := bstep (se 1 (by rfl) ⟨840161, by rfl⟩ : syracuseStep 1120215 = 1680323) B1680323
theorem B1120235 : Blo 1116628 1120235 := bstep (se 1 (by rfl) ⟨840176, by rfl⟩ : syracuseStep 1120235 = 1680353) B1680353
theorem B1120247 : Blo 1116628 1120247 := bstep (se 1 (by rfl) ⟨840185, by rfl⟩ : syracuseStep 1120247 = 1680371) B1680371
theorem B1677323 : Blo 1116628 1677323 := bstep (se 1 (by rfl) ⟨1257992, by rfl⟩ : syracuseStep 1677323 = 2515985) B2515985
theorem B1120267 : Blo 1116628 1120267 := bstep (se 1 (by rfl) ⟨840200, by rfl⟩ : syracuseStep 1120267 = 1680401) B1680401
theorem B14358545 : Blo 1116628 14358545 := bstep (se 2 (by rfl) ⟨5384454, by rfl⟩ : syracuseStep 14358545 = 10768909) B10768909
theorem B1677335 : Blo 1116628 1677335 := bstep (se 1 (by rfl) ⟨1258001, by rfl⟩ : syracuseStep 1677335 = 2516003) B2516003
theorem B1120279 : Blo 1116628 1120279 := bstep (se 1 (by rfl) ⟨840209, by rfl⟩ : syracuseStep 1120279 = 1680419) B1680419
theorem B1120299 : Blo 1116628 1120299 := bstep (se 1 (by rfl) ⟨840224, by rfl⟩ : syracuseStep 1120299 = 1680449) B1680449
theorem B1120311 : Blo 1116628 1120311 := bstep (se 1 (by rfl) ⟨840233, by rfl⟩ : syracuseStep 1120311 = 1680467) B1680467
theorem B1120331 : Blo 1116628 1120331 := bstep (se 1 (by rfl) ⟨840248, by rfl⟩ : syracuseStep 1120331 = 1680497) B1680497
theorem B1120343 : Blo 1116628 1120343 := bstep (se 1 (by rfl) ⟨840257, by rfl⟩ : syracuseStep 1120343 = 1680515) B1680515
theorem B1677401 : Blo 1116628 1677401 := bstep (se 2 (by rfl) ⟨629025, by rfl⟩ : syracuseStep 1677401 = 1258051) B1258051
theorem B1120363 : Blo 1116628 1120363 := bstep (se 1 (by rfl) ⟨840272, by rfl⟩ : syracuseStep 1120363 = 1680545) B1680545
theorem B1120375 : Blo 1116628 1120375 := bstep (se 1 (by rfl) ⟨840281, by rfl⟩ : syracuseStep 1120375 = 1680563) B1680563
theorem B1120395 : Blo 1116628 1120395 := bstep (se 1 (by rfl) ⟨840296, by rfl⟩ : syracuseStep 1120395 = 1680593) B1680593
theorem B1120407 : Blo 1116628 1120407 := bstep (se 1 (by rfl) ⟨840305, by rfl⟩ : syracuseStep 1120407 = 1680611) B1680611
theorem B1120427 : Blo 1116628 1120427 := bstep (se 1 (by rfl) ⟨840320, by rfl⟩ : syracuseStep 1120427 = 1680641) B1680641
theorem B1120439 : Blo 1116628 1120439 := bstep (se 1 (by rfl) ⟨840329, by rfl⟩ : syracuseStep 1120439 = 1680659) B1680659
theorem B1677515 : Blo 1116628 1677515 := bstep (se 1 (by rfl) ⟨1258136, by rfl⟩ : syracuseStep 1677515 = 2516273) B2516273
theorem B1120459 : Blo 1116628 1120459 := bstep (se 1 (by rfl) ⟨840344, by rfl⟩ : syracuseStep 1120459 = 1680689) B1680689
theorem B1677527 : Blo 1116628 1677527 := bstep (se 1 (by rfl) ⟨1258145, by rfl⟩ : syracuseStep 1677527 = 2516291) B2516291
theorem B1120471 : Blo 1116628 1120471 := bstep (se 1 (by rfl) ⟨840353, by rfl⟩ : syracuseStep 1120471 = 1680707) B1680707
theorem B1120491 : Blo 1116628 1120491 := bstep (se 1 (by rfl) ⟨840368, by rfl⟩ : syracuseStep 1120491 = 1680737) B1680737
theorem B1120503 : Blo 1116628 1120503 := bstep (se 1 (by rfl) ⟨840377, by rfl⟩ : syracuseStep 1120503 = 1680755) B1680755
theorem B1120523 : Blo 1116628 1120523 := bstep (se 1 (by rfl) ⟨840392, by rfl⟩ : syracuseStep 1120523 = 1680785) B1680785
theorem B1120535 : Blo 1116628 1120535 := bstep (se 1 (by rfl) ⟨840401, by rfl⟩ : syracuseStep 1120535 = 1680803) B1680803
theorem B1677593 : Blo 1116628 1677593 := bstep (se 2 (by rfl) ⟨629097, by rfl⟩ : syracuseStep 1677593 = 1258195) B1258195
theorem B1120555 : Blo 1116628 1120555 := bstep (se 1 (by rfl) ⟨840416, by rfl⟩ : syracuseStep 1120555 = 1680833) B1680833
theorem B1120567 : Blo 1116628 1120567 := bstep (se 1 (by rfl) ⟨840425, by rfl⟩ : syracuseStep 1120567 = 1680851) B1680851
theorem B1120587 : Blo 1116628 1120587 := bstep (se 1 (by rfl) ⟨840440, by rfl⟩ : syracuseStep 1120587 = 1680881) B1680881
theorem B1120599 : Blo 1116628 1120599 := bstep (se 1 (by rfl) ⟨840449, by rfl⟩ : syracuseStep 1120599 = 1680899) B1680899
theorem B4299101 : Blo 1116628 4299101 := bstep (se 3 (by rfl) ⟨806081, by rfl⟩ : syracuseStep 4299101 = 1612163) B1612163
theorem B1120619 : Blo 1116628 1120619 := bstep (se 1 (by rfl) ⟨840464, by rfl⟩ : syracuseStep 1120619 = 1680929) B1680929
theorem B1677707 : Blo 1116628 1677707 := bstep (se 1 (by rfl) ⟨1258280, by rfl⟩ : syracuseStep 1677707 = 2516561) B2516561
theorem B1677719 : Blo 1116628 1677719 := bstep (se 1 (by rfl) ⟨1258289, by rfl⟩ : syracuseStep 1677719 = 2516579) B2516579
theorem B4037015 : Blo 1116628 4037015 := bstep (se 1 (by rfl) ⟨3027761, by rfl⟩ : syracuseStep 4037015 = 6055523) B6055523
theorem B3774923 : Blo 1116628 3774923 := bstep (se 1 (by rfl) ⟨2831192, by rfl⟩ : syracuseStep 3774923 = 5662385) B5662385
theorem B1677785 : Blo 1116628 1677785 := bstep (se 2 (by rfl) ⟨629169, by rfl⟩ : syracuseStep 1677785 = 1258339) B1258339
theorem B14326307 : Blo 1116628 14326307 := bstep (se 1 (by rfl) ⟨10744730, by rfl⟩ : syracuseStep 14326307 = 21489461) B21489461
theorem B1677899 : Blo 1116628 1677899 := bstep (se 1 (by rfl) ⟨1258424, by rfl⟩ : syracuseStep 1677899 = 2516849) B2516849
theorem B1677911 : Blo 1116628 1677911 := bstep (se 1 (by rfl) ⟨1258433, by rfl⟩ : syracuseStep 1677911 = 2516867) B2516867
theorem B1415819 : Blo 1116628 1415819 := bstep (se 1 (by rfl) ⟨1061864, by rfl⟩ : syracuseStep 1415819 = 2123729) B2123729
theorem B1677977 : Blo 1116628 1677977 := bstep (se 2 (by rfl) ⟨629241, by rfl⟩ : syracuseStep 1677977 = 1258483) B1258483
theorem B3775193 : Blo 1116628 3775193 := bstep (se 2 (by rfl) ⟨1415697, by rfl⟩ : syracuseStep 3775193 = 2831395) B2831395
theorem B1678091 : Blo 1116628 1678091 := bstep (se 1 (by rfl) ⟨1258568, by rfl⟩ : syracuseStep 1678091 = 2517137) B2517137
theorem B1678103 : Blo 1116628 1678103 := bstep (se 1 (by rfl) ⟨1258577, by rfl⟩ : syracuseStep 1678103 = 2517155) B2517155
theorem B1678169 : Blo 1116628 1678169 := bstep (se 2 (by rfl) ⟨629313, by rfl⟩ : syracuseStep 1678169 = 1258627) B1258627
theorem B4037465 : Blo 1116628 4037465 := bstep (se 2 (by rfl) ⟨1514049, by rfl⟩ : syracuseStep 4037465 = 3028099) B3028099
theorem B1678283 : Blo 1116628 1678283 := bstep (se 1 (by rfl) ⟨1258712, by rfl⟩ : syracuseStep 1678283 = 2517425) B2517425
theorem B4037579 : Blo 1116628 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B1678295 : Blo 1116628 1678295 := bstep (se 1 (by rfl) ⟨1258721, by rfl⟩ : syracuseStep 1678295 = 2517443) B2517443
theorem B1678361 : Blo 1116628 1678361 := bstep (se 2 (by rfl) ⟨629385, by rfl⟩ : syracuseStep 1678361 = 1258771) B1258771
theorem B18127907 : Blo 1116628 18127907 := bstep (se 1 (by rfl) ⟨13595930, by rfl⟩ : syracuseStep 18127907 = 27191861) B27191861
theorem B1678475 : Blo 1116628 1678475 := bstep (se 1 (by rfl) ⟨1258856, by rfl⟩ : syracuseStep 1678475 = 2517713) B2517713
theorem B1678487 : Blo 1116628 1678487 := bstep (se 1 (by rfl) ⟨1258865, by rfl⟩ : syracuseStep 1678487 = 2517731) B2517731
theorem B3185867 : Blo 1116628 3185867 := bstep (se 1 (by rfl) ⟨2389400, by rfl⟩ : syracuseStep 3185867 = 4778801) B4778801
theorem B1678553 : Blo 1116628 1678553 := bstep (se 2 (by rfl) ⟨629457, by rfl⟩ : syracuseStep 1678553 = 1258915) B1258915
theorem B1678667 : Blo 1116628 1678667 := bstep (se 1 (by rfl) ⟨1259000, by rfl⟩ : syracuseStep 1678667 = 2518001) B2518001
theorem B1416523 : Blo 1116628 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B1678679 : Blo 1116628 1678679 := bstep (se 1 (by rfl) ⟨1259009, by rfl⟩ : syracuseStep 1678679 = 2518019) B2518019
theorem B3775895 : Blo 1116628 3775895 := bstep (se 1 (by rfl) ⟨2831921, by rfl⟩ : syracuseStep 3775895 = 5663843) B5663843
theorem B1678745 : Blo 1116628 1678745 := bstep (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) B1259059
theorem B1678859 : Blo 1116628 1678859 := bstep (se 1 (by rfl) ⟨1259144, by rfl⟩ : syracuseStep 1678859 = 2518289) B2518289
theorem B1678871 : Blo 1116628 1678871 := bstep (se 1 (by rfl) ⟨1259153, by rfl⟩ : syracuseStep 1678871 = 2518307) B2518307
theorem B2268697 : Blo 1116628 2268697 := bstep (se 2 (by rfl) ⟨850761, by rfl⟩ : syracuseStep 2268697 = 1701523) B1701523
theorem B1416791 : Blo 1116628 1416791 := bstep (se 1 (by rfl) ⟨1062593, by rfl⟩ : syracuseStep 1416791 = 2125187) B2125187
theorem B1678937 : Blo 1116628 1678937 := bstep (se 2 (by rfl) ⟨629601, by rfl⟩ : syracuseStep 1678937 = 1259203) B1259203
theorem B12754583 : Blo 1116628 12754583 := bstep (se 1 (by rfl) ⟨9565937, by rfl⟩ : syracuseStep 12754583 = 19131875) B19131875
theorem B2268875 : Blo 1116628 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B1679051 : Blo 1116628 1679051 := bstep (se 1 (by rfl) ⟨1259288, by rfl⟩ : syracuseStep 1679051 = 2518577) B2518577
theorem B1679063 : Blo 1116628 1679063 := bstep (se 1 (by rfl) ⟨1259297, by rfl⟩ : syracuseStep 1679063 = 2518595) B2518595
theorem B1679129 : Blo 1116628 1679129 := bstep (se 2 (by rfl) ⟨629673, by rfl⟩ : syracuseStep 1679129 = 1259347) B1259347
theorem B1679243 : Blo 1116628 1679243 := bstep (se 1 (by rfl) ⟨1259432, by rfl⟩ : syracuseStep 1679243 = 2518865) B2518865
theorem B1679255 : Blo 1116628 1679255 := bstep (se 1 (by rfl) ⟨1259441, by rfl⟩ : syracuseStep 1679255 = 2518883) B2518883
theorem B3776435 : Blo 1116628 3776435 := bstep (se 1 (by rfl) ⟨2832326, by rfl⟩ : syracuseStep 3776435 = 5664653) B5664653
theorem B1679321 : Blo 1116628 1679321 := bstep (se 2 (by rfl) ⟨629745, by rfl⟩ : syracuseStep 1679321 = 1259491) B1259491
theorem B36347939 : Blo 1116628 36347939 := bstep (se 1 (by rfl) ⟨27260954, by rfl⟩ : syracuseStep 36347939 = 54521909) B54521909
theorem B1679435 : Blo 1116628 1679435 := bstep (se 1 (by rfl) ⟨1259576, by rfl⟩ : syracuseStep 1679435 = 2519153) B2519153
theorem B1679447 : Blo 1116628 1679447 := bstep (se 1 (by rfl) ⟨1259585, by rfl⟩ : syracuseStep 1679447 = 2519171) B2519171
theorem B1679513 : Blo 1116628 1679513 := bstep (se 2 (by rfl) ⟨629817, by rfl⟩ : syracuseStep 1679513 = 1259635) B1259635
theorem B3776705 : Blo 1116628 3776705 := bstep (se 2 (by rfl) ⟨1416264, by rfl⟩ : syracuseStep 3776705 = 2832529) B2832529
theorem B1679627 : Blo 1116628 1679627 := bstep (se 1 (by rfl) ⟨1259720, by rfl⟩ : syracuseStep 1679627 = 2519441) B2519441
theorem B1679639 : Blo 1116628 1679639 := bstep (se 1 (by rfl) ⟨1259729, by rfl⟩ : syracuseStep 1679639 = 2519459) B2519459
theorem B1417495 : Blo 1116628 1417495 := bstep (se 1 (by rfl) ⟨1063121, by rfl⟩ : syracuseStep 1417495 = 2126243) B2126243
theorem B18129197 : Blo 1116628 18129197 := bstep (se 3 (by rfl) ⟨3399224, by rfl⟩ : syracuseStep 18129197 = 6798449) B6798449
theorem B3449153 : Blo 1116628 3449153 := bstep (se 2 (by rfl) ⟨1293432, by rfl⟩ : syracuseStep 3449153 = 2586865) B2586865
theorem B1679705 : Blo 1116628 1679705 := bstep (se 2 (by rfl) ⟨629889, by rfl⟩ : syracuseStep 1679705 = 1259779) B1259779
theorem B2826647 : Blo 1116628 2826647 := bstep (se 1 (by rfl) ⟨2119985, by rfl⟩ : syracuseStep 2826647 = 4239971) B4239971
theorem B1679819 : Blo 1116628 1679819 := bstep (se 1 (by rfl) ⟨1259864, by rfl⟩ : syracuseStep 1679819 = 2519729) B2519729
theorem B1679831 : Blo 1116628 1679831 := bstep (se 1 (by rfl) ⟨1259873, by rfl⟩ : syracuseStep 1679831 = 2519747) B2519747
theorem B1679897 : Blo 1116628 1679897 := bstep (se 2 (by rfl) ⟨629961, by rfl⟩ : syracuseStep 1679897 = 1259923) B1259923
theorem B6365789 : Blo 1116628 6365789 := bstep (se 3 (by rfl) ⟨1193585, by rfl⟩ : syracuseStep 6365789 = 2387171) B2387171
theorem B1680011 : Blo 1116628 1680011 := bstep (se 1 (by rfl) ⟨1260008, by rfl⟩ : syracuseStep 1680011 = 2520017) B2520017
theorem B1680023 : Blo 1116628 1680023 := bstep (se 1 (by rfl) ⟨1260017, by rfl⟩ : syracuseStep 1680023 = 2520035) B2520035
theorem B1680089 : Blo 1116628 1680089 := bstep (se 2 (by rfl) ⟨630033, by rfl⟩ : syracuseStep 1680089 = 1260067) B1260067
theorem B3777245 : Blo 1116628 3777245 := bstep (se 3 (by rfl) ⟨708233, by rfl⟩ : syracuseStep 3777245 = 1416467) B1416467
theorem B3187507 : Blo 1116628 3187507 := bstep (se 1 (by rfl) ⟨2390630, by rfl⟩ : syracuseStep 3187507 = 4781261) B4781261
theorem B6792011 : Blo 1116628 6792011 := bstep (se 1 (by rfl) ⟨5094008, by rfl⟩ : syracuseStep 6792011 = 10188017) B10188017
theorem B1680203 : Blo 1116628 1680203 := bstep (se 1 (by rfl) ⟨1260152, by rfl⟩ : syracuseStep 1680203 = 2520305) B2520305
theorem B1680215 : Blo 1116628 1680215 := bstep (se 1 (by rfl) ⟨1260161, by rfl⟩ : syracuseStep 1680215 = 2520323) B2520323
theorem B13607797 : Blo 1116628 13607797 := bstep (se 5 (by rfl) ⟨637865, by rfl⟩ : syracuseStep 13607797 = 1275731) B1275731
theorem B1680281 : Blo 1116628 1680281 := bstep (se 2 (by rfl) ⟨630105, by rfl⟩ : syracuseStep 1680281 = 1260211) B1260211
theorem B1680395 : Blo 1116628 1680395 := bstep (se 1 (by rfl) ⟨1260296, by rfl⟩ : syracuseStep 1680395 = 2520593) B2520593
theorem B1680407 : Blo 1116628 1680407 := bstep (se 1 (by rfl) ⟨1260305, by rfl⟩ : syracuseStep 1680407 = 2520611) B2520611
theorem B43066403 : Blo 1116628 43066403 := bstep (se 1 (by rfl) ⟨32299802, by rfl⟩ : syracuseStep 43066403 = 64599605) B64599605
theorem B1680473 : Blo 1116628 1680473 := bstep (se 2 (by rfl) ⟨630177, by rfl⟩ : syracuseStep 1680473 = 1260355) B1260355
theorem B2827457 : Blo 1116628 2827457 := bstep (se 2 (by rfl) ⟨1060296, by rfl⟩ : syracuseStep 2827457 = 2120593) B2120593
theorem B1680587 : Blo 1116628 1680587 := bstep (se 1 (by rfl) ⟨1260440, by rfl⟩ : syracuseStep 1680587 = 2520881) B2520881
theorem B1680599 : Blo 1116628 1680599 := bstep (se 1 (by rfl) ⟨1260449, by rfl⟩ : syracuseStep 1680599 = 2520899) B2520899
theorem B1680665 : Blo 1116628 1680665 := bstep (se 2 (by rfl) ⟨630249, by rfl⟩ : syracuseStep 1680665 = 1260499) B1260499
theorem B6366539 : Blo 1116628 6366539 := bstep (se 1 (by rfl) ⟨4774904, by rfl⟩ : syracuseStep 6366539 = 9549809) B9549809
theorem B1680779 : Blo 1116628 1680779 := bstep (se 1 (by rfl) ⟨1260584, by rfl⟩ : syracuseStep 1680779 = 2521169) B2521169
theorem B1680791 : Blo 1116628 1680791 := bstep (se 1 (by rfl) ⟨1260593, by rfl⟩ : syracuseStep 1680791 = 2521187) B2521187
theorem B1680857 : Blo 1116628 1680857 := bstep (se 2 (by rfl) ⟨630321, by rfl⟩ : syracuseStep 1680857 = 1260643) B1260643
theorem B6465041 : Blo 1116628 6465041 := bstep (se 2 (by rfl) ⟨2424390, by rfl⟩ : syracuseStep 6465041 = 4848781) B4848781
theorem B2827993 : Blo 1116628 2827993 := bstep (se 2 (by rfl) ⟨1060497, by rfl⟩ : syracuseStep 2827993 = 2120995) B2120995
theorem B3778379 : Blo 1116628 3778379 := bstep (se 1 (by rfl) ⟨2833784, by rfl⟩ : syracuseStep 3778379 = 5667569) B5667569
theorem B3188555 : Blo 1116628 3188555 := bstep (se 1 (by rfl) ⟨2391416, by rfl⟩ : syracuseStep 3188555 = 4782833) B4782833
theorem B3876697 : Blo 1116628 3876697 := bstep (se 2 (by rfl) ⟨1453761, by rfl⟩ : syracuseStep 3876697 = 2907523) B2907523
theorem B2271179 : Blo 1116628 2271179 := bstep (se 1 (by rfl) ⟨1703384, by rfl⟩ : syracuseStep 2271179 = 3406769) B3406769
theorem B3778649 : Blo 1116628 3778649 := bstep (se 2 (by rfl) ⟨1416993, by rfl⟩ : syracuseStep 3778649 = 2833987) B2833987
theorem B8497709 : Blo 1116628 8497709 := bstep (se 3 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 8497709 = 3186641) B3186641
theorem B3582539 : Blo 1116628 3582539 := bstep (se 1 (by rfl) ⟨2686904, by rfl⟩ : syracuseStep 3582539 = 5373809) B5373809
theorem B1256215 : Blo 1116628 1256215 := bstep (se 1 (by rfl) ⟨942161, by rfl⟩ : syracuseStep 1256215 = 1884323) B1884323
theorem B3779351 : Blo 1116628 3779351 := bstep (se 1 (by rfl) ⟨2834513, by rfl⟩ : syracuseStep 3779351 = 5669027) B5669027
theorem B2829107 : Blo 1116628 2829107 := bstep (se 1 (by rfl) ⟨2121830, by rfl⟩ : syracuseStep 2829107 = 4243661) B4243661
theorem B6368179 : Blo 1116628 6368179 := bstep (se 1 (by rfl) ⟨4776134, by rfl⟩ : syracuseStep 6368179 = 9552269) B9552269
theorem B1256395 : Blo 1116628 1256395 := bstep (se 1 (by rfl) ⟨942296, by rfl⟩ : syracuseStep 1256395 = 1884593) B1884593
theorem B1256503 : Blo 1116628 1256503 := bstep (se 1 (by rfl) ⟨942377, by rfl⟩ : syracuseStep 1256503 = 1884755) B1884755
theorem B2829401 : Blo 1116628 2829401 := bstep (se 2 (by rfl) ⟨1061025, by rfl⟩ : syracuseStep 2829401 = 2122051) B2122051
theorem B1256683 : Blo 1116628 1256683 := bstep (se 1 (by rfl) ⟨942512, by rfl⟩ : syracuseStep 1256683 = 1885025) B1885025
theorem B3779891 : Blo 1116628 3779891 := bstep (se 1 (by rfl) ⟨2834918, by rfl⟩ : syracuseStep 3779891 = 5669837) B5669837
theorem B6466891 : Blo 1116628 6466891 := bstep (se 1 (by rfl) ⟨4850168, by rfl⟩ : syracuseStep 6466891 = 9700337) B9700337
theorem B1256791 : Blo 1116628 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B3190195 : Blo 1116628 3190195 := bstep (se 1 (by rfl) ⟨2392646, by rfl⟩ : syracuseStep 3190195 = 4785293) B4785293
theorem B1256971 : Blo 1116628 1256971 := bstep (se 1 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 1256971 = 1885457) B1885457
theorem B3780161 : Blo 1116628 3780161 := bstep (se 2 (by rfl) ⟨1417560, by rfl⟩ : syracuseStep 3780161 = 2835121) B2835121
theorem B24161885 : Blo 1116628 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B1257079 : Blo 1116628 1257079 := bstep (se 1 (by rfl) ⟨942809, by rfl⟩ : syracuseStep 1257079 = 1885619) B1885619
theorem B3583639 : Blo 1116628 3583639 := bstep (se 1 (by rfl) ⟨2687729, by rfl⟩ : syracuseStep 3583639 = 5375459) B5375459
theorem B3190423 : Blo 1116628 3190423 := bstep (se 1 (by rfl) ⟨2392817, by rfl⟩ : syracuseStep 3190423 = 4785635) B4785635
theorem B3452633 : Blo 1116628 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B1257259 : Blo 1116628 1257259 := bstep (se 1 (by rfl) ⟨942944, by rfl⟩ : syracuseStep 1257259 = 1885889) B1885889
theorem B1257367 : Blo 1116628 1257367 := bstep (se 1 (by rfl) ⟨943025, by rfl⟩ : syracuseStep 1257367 = 1886051) B1886051
theorem B1257547 : Blo 1116628 1257547 := bstep (se 1 (by rfl) ⟨943160, by rfl⟩ : syracuseStep 1257547 = 1886321) B1886321
theorem B3780701 : Blo 1116628 3780701 := bstep (se 3 (by rfl) ⟨708881, by rfl⟩ : syracuseStep 3780701 = 1417763) B1417763
theorem B1257655 : Blo 1116628 1257655 := bstep (se 1 (by rfl) ⟨943241, by rfl⟩ : syracuseStep 1257655 = 1886483) B1886483
theorem B6369637 : Blo 1116628 6369637 := bstep (se 4 (by rfl) ⟨597153, by rfl⟩ : syracuseStep 6369637 = 1194307) B1194307
theorem B1257835 : Blo 1116628 1257835 := bstep (se 1 (by rfl) ⟨943376, by rfl⟩ : syracuseStep 1257835 = 1886753) B1886753
theorem B3584459 : Blo 1116628 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B1257943 : Blo 1116628 1257943 := bstep (se 1 (by rfl) ⟨943457, by rfl⟩ : syracuseStep 1257943 = 1886915) B1886915
theorem B1258123 : Blo 1116628 1258123 := bstep (se 1 (by rfl) ⟨943592, by rfl⟩ : syracuseStep 1258123 = 1887185) B1887185
theorem B2831051 : Blo 1116628 2831051 := bstep (se 1 (by rfl) ⟨2123288, by rfl⟩ : syracuseStep 2831051 = 4246577) B4246577
theorem B1258231 : Blo 1116628 1258231 := bstep (se 1 (by rfl) ⟨943673, by rfl⟩ : syracuseStep 1258231 = 1887347) B1887347
theorem B1291063 : Blo 1116628 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B4240259 : Blo 1116628 4240259 := bstep (se 1 (by rfl) ⟨3180194, by rfl⟩ : syracuseStep 4240259 = 6360389) B6360389
theorem B1192855 : Blo 1116628 1192855 := bstep (se 1 (by rfl) ⟨894641, by rfl⟩ : syracuseStep 1192855 = 1789283) B1789283
theorem B1258411 : Blo 1116628 1258411 := bstep (se 1 (by rfl) ⟨943808, by rfl⟩ : syracuseStep 1258411 = 1887617) B1887617
theorem B10204177 : Blo 1116628 10204177 := bstep (se 2 (by rfl) ⟨3826566, by rfl⟩ : syracuseStep 10204177 = 7653133) B7653133
theorem B1258519 : Blo 1116628 1258519 := bstep (se 1 (by rfl) ⟨943889, by rfl⟩ : syracuseStep 1258519 = 1887779) B1887779
theorem B38810765 : Blo 1116628 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B1258699 : Blo 1116628 1258699 := bstep (se 1 (by rfl) ⟨944024, by rfl⟩ : syracuseStep 1258699 = 1888049) B1888049
theorem B3781835 : Blo 1116628 3781835 := bstep (se 1 (by rfl) ⟨2836376, by rfl⟩ : syracuseStep 3781835 = 5672753) B5672753
theorem B12104909 : Blo 1116628 12104909 := bstep (se 3 (by rfl) ⟨2269670, by rfl⟩ : syracuseStep 12104909 = 4539341) B4539341
theorem B2045171 : Blo 1116628 2045171 := bstep (se 1 (by rfl) ⟨1533878, by rfl⟩ : syracuseStep 2045171 = 3067757) B3067757
theorem B1258807 : Blo 1116628 1258807 := bstep (se 1 (by rfl) ⟨944105, by rfl⟩ : syracuseStep 1258807 = 1888211) B1888211
theorem B3782105 : Blo 1116628 3782105 := bstep (se 2 (by rfl) ⟨1418289, by rfl⟩ : syracuseStep 3782105 = 2836579) B2836579
theorem B1258987 : Blo 1116628 1258987 := bstep (se 1 (by rfl) ⟨944240, by rfl⟩ : syracuseStep 1258987 = 1888481) B1888481
theorem B12105251 : Blo 1116628 12105251 := bstep (se 1 (by rfl) ⟨9078938, by rfl⟩ : syracuseStep 12105251 = 18157877) B18157877
theorem B1259095 : Blo 1116628 1259095 := bstep (se 1 (by rfl) ⟨944321, by rfl⟩ : syracuseStep 1259095 = 1888643) B1888643
theorem B2832023 : Blo 1116628 2832023 := bstep (se 1 (by rfl) ⟨2124017, by rfl⟩ : syracuseStep 2832023 = 4248035) B4248035
theorem B1193675 : Blo 1116628 1193675 := bstep (se 1 (by rfl) ⟨895256, by rfl⟩ : syracuseStep 1193675 = 1790513) B1790513
theorem B1259275 : Blo 1116628 1259275 := bstep (se 1 (by rfl) ⟨944456, by rfl⟩ : syracuseStep 1259275 = 1888913) B1888913
theorem B1259383 : Blo 1116628 1259383 := bstep (se 1 (by rfl) ⟨944537, by rfl⟩ : syracuseStep 1259383 = 1889075) B1889075
theorem B41400355 : Blo 1116628 41400355 := bstep (se 1 (by rfl) ⟨31050266, by rfl⟩ : syracuseStep 41400355 = 62100533) B62100533
theorem B1259563 : Blo 1116628 1259563 := bstep (se 1 (by rfl) ⟨944672, by rfl⟩ : syracuseStep 1259563 = 1889345) B1889345
theorem B3225689 : Blo 1116628 3225689 := bstep (se 2 (by rfl) ⟨1209633, by rfl⟩ : syracuseStep 3225689 = 2419267) B2419267
theorem B1259671 : Blo 1116628 1259671 := bstep (se 1 (by rfl) ⟨944753, by rfl⟩ : syracuseStep 1259671 = 1889507) B1889507
theorem B2832691 : Blo 1116628 2832691 := bstep (se 1 (by rfl) ⟨2124518, by rfl⟩ : syracuseStep 2832691 = 4249037) B4249037
theorem B1259851 : Blo 1116628 1259851 := bstep (se 1 (by rfl) ⟨944888, by rfl⟩ : syracuseStep 1259851 = 1889777) B1889777
theorem B8501597 : Blo 1116628 8501597 := bstep (se 3 (by rfl) ⟨1594049, by rfl⟩ : syracuseStep 8501597 = 3188099) B3188099
theorem B12073333 : Blo 1116628 12073333 := bstep (se 5 (by rfl) ⟨565937, by rfl⟩ : syracuseStep 12073333 = 1131875) B1131875
theorem B1259959 : Blo 1116628 1259959 := bstep (se 1 (by rfl) ⟨944969, by rfl⟩ : syracuseStep 1259959 = 1889939) B1889939
theorem B2832833 : Blo 1116628 2832833 := bstep (se 2 (by rfl) ⟨1062312, by rfl⟩ : syracuseStep 2832833 = 2124625) B2124625
theorem B7158233 : Blo 1116628 7158233 := bstep (se 2 (by rfl) ⟨2684337, by rfl⟩ : syracuseStep 7158233 = 5368675) B5368675
theorem B9058891 : Blo 1116628 9058891 := bstep (se 1 (by rfl) ⟨6794168, by rfl⟩ : syracuseStep 9058891 = 13588337) B13588337
theorem B1260139 : Blo 1116628 1260139 := bstep (se 1 (by rfl) ⟨945104, by rfl⟩ : syracuseStep 1260139 = 1890209) B1890209
theorem B1194679 : Blo 1116628 1194679 := bstep (se 1 (by rfl) ⟨896009, by rfl⟩ : syracuseStep 1194679 = 1792019) B1792019
theorem B1260247 : Blo 1116628 1260247 := bstep (se 1 (by rfl) ⟨945185, by rfl⟩ : syracuseStep 1260247 = 1890371) B1890371
theorem B1915787 : Blo 1116628 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B1260427 : Blo 1116628 1260427 := bstep (se 1 (by rfl) ⟨945320, by rfl⟩ : syracuseStep 1260427 = 1890641) B1890641
theorem B1260535 : Blo 1116628 1260535 := bstep (se 1 (by rfl) ⟨945401, by rfl⟩ : syracuseStep 1260535 = 1890803) B1890803
theorem B1915979 : Blo 1116628 1915979 := bstep (se 1 (by rfl) ⟨1436984, by rfl⟩ : syracuseStep 1915979 = 2873969) B2873969
theorem B1195435 : Blo 1116628 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B2834099 : Blo 1116628 2834099 := bstep (se 1 (by rfl) ⟨2125574, by rfl⟩ : syracuseStep 2834099 = 4251149) B4251149
theorem B4243373 : Blo 1116628 4243373 := bstep (se 3 (by rfl) ⟨795632, by rfl⟩ : syracuseStep 4243373 = 1591265) B1591265
theorem B7159873 : Blo 1116628 7159873 := bstep (se 2 (by rfl) ⟨2684952, by rfl⟩ : syracuseStep 7159873 = 5369905) B5369905
theorem B1818775 : Blo 1116628 1818775 := bstep (se 1 (by rfl) ⟨1364081, by rfl⟩ : syracuseStep 1818775 = 2728163) B2728163
theorem B2834635 : Blo 1116628 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B1884377 : Blo 1116628 1884377 := bstep (se 2 (by rfl) ⟨706641, by rfl⟩ : syracuseStep 1884377 = 1413283) B1413283
theorem B1884505 : Blo 1116628 1884505 := bstep (se 2 (by rfl) ⟨706689, by rfl⟩ : syracuseStep 1884505 = 1413379) B1413379
theorem B2834777 : Blo 1116628 2834777 := bstep (se 2 (by rfl) ⟨1063041, by rfl⟩ : syracuseStep 2834777 = 2126083) B2126083
theorem B4244147 : Blo 1116628 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B5653313 : Blo 1116628 5653313 := bstep (se 2 (by rfl) ⟨2119992, by rfl⟩ : syracuseStep 5653313 = 4239985) B4239985
theorem B6800203 : Blo 1116628 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B22397795 : Blo 1116628 22397795 := bstep (se 1 (by rfl) ⟨16798346, by rfl⟩ : syracuseStep 22397795 = 33596693) B33596693
theorem B1885079 : Blo 1116628 1885079 := bstep (se 1 (by rfl) ⟨1413809, by rfl⟩ : syracuseStep 1885079 = 2827619) B2827619
theorem B1885207 : Blo 1116628 1885207 := bstep (se 1 (by rfl) ⟨1413905, by rfl⟩ : syracuseStep 1885207 = 2827811) B2827811
theorem B1590359 : Blo 1116628 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B2835607 : Blo 1116628 2835607 := bstep (se 1 (by rfl) ⟨2126705, by rfl⟩ : syracuseStep 2835607 = 4253411) B4253411
theorem B1590553 : Blo 1116628 1590553 := bstep (se 2 (by rfl) ⟨596457, by rfl⟩ : syracuseStep 1590553 = 1192915) B1192915
theorem B2836043 : Blo 1116628 2836043 := bstep (se 1 (by rfl) ⟨2127032, by rfl⟩ : syracuseStep 2836043 = 4254065) B4254065
theorem B4081283 : Blo 1116628 4081283 := bstep (se 1 (by rfl) ⟨3060962, by rfl⟩ : syracuseStep 4081283 = 6121925) B6121925
theorem B1885835 : Blo 1116628 1885835 := bstep (se 1 (by rfl) ⟨1414376, by rfl⟩ : syracuseStep 1885835 = 2828753) B2828753
theorem B1885963 : Blo 1116628 1885963 := bstep (se 1 (by rfl) ⟨1414472, by rfl⟩ : syracuseStep 1885963 = 2828945) B2828945
theorem B1886105 : Blo 1116628 1886105 := bstep (se 2 (by rfl) ⟨707289, by rfl⟩ : syracuseStep 1886105 = 1414579) B1414579
theorem B2836417 : Blo 1116628 2836417 := bstep (se 2 (by rfl) ⟨1063656, by rfl⟩ : syracuseStep 2836417 = 2127313) B2127313
theorem B1886233 : Blo 1116628 1886233 := bstep (se 2 (by rfl) ⟨707337, by rfl⟩ : syracuseStep 1886233 = 1414675) B1414675
theorem B6375469 : Blo 1116628 6375469 := bstep (se 3 (by rfl) ⟨1195400, by rfl⟩ : syracuseStep 6375469 = 2390801) B2390801
theorem B4245635 : Blo 1116628 4245635 := bstep (se 1 (by rfl) ⟨3184226, by rfl⟩ : syracuseStep 4245635 = 6368453) B6368453
theorem B2148811 : Blo 1116628 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B4540931 : Blo 1116628 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B7653953 : Blo 1116628 7653953 := bstep (se 2 (by rfl) ⟨2870232, by rfl⟩ : syracuseStep 7653953 = 5740465) B5740465
theorem B4246091 : Blo 1116628 4246091 := bstep (se 1 (by rfl) ⟨3184568, by rfl⟩ : syracuseStep 4246091 = 6369137) B6369137
theorem B2017867 : Blo 1116628 2017867 := bstep (se 1 (by rfl) ⟨1513400, by rfl⟩ : syracuseStep 2017867 = 3026801) B3026801
theorem B1886807 : Blo 1116628 1886807 := bstep (se 1 (by rfl) ⟨1415105, by rfl⟩ : syracuseStep 1886807 = 2830211) B2830211
theorem B1592011 : Blo 1116628 1592011 := bstep (se 1 (by rfl) ⟨1194008, by rfl⟩ : syracuseStep 1592011 = 2388017) B2388017
theorem B1886935 : Blo 1116628 1886935 := bstep (se 1 (by rfl) ⟨1415201, by rfl⟩ : syracuseStep 1886935 = 2830403) B2830403
theorem B5655257 : Blo 1116628 5655257 := bstep (se 2 (by rfl) ⟨2120721, by rfl⟩ : syracuseStep 5655257 = 4241443) B4241443
theorem B4246289 : Blo 1116628 4246289 := bstep (se 2 (by rfl) ⟨1592358, by rfl⟩ : syracuseStep 4246289 = 3184717) B3184717
theorem B9554867 : Blo 1116628 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B4770839 : Blo 1116628 4770839 := bstep (se 1 (by rfl) ⟨3578129, by rfl⟩ : syracuseStep 4770839 = 7156259) B7156259
theorem B10767491 : Blo 1116628 10767491 := bstep (se 1 (by rfl) ⟨8075618, by rfl⟩ : syracuseStep 10767491 = 16151237) B16151237
theorem B3230941 : Blo 1116628 3230941 := bstep (se 3 (by rfl) ⟨605801, by rfl⟩ : syracuseStep 3230941 = 1211603) B1211603
theorem B9555245 : Blo 1116628 9555245 := bstep (se 3 (by rfl) ⟨1791608, by rfl⟩ : syracuseStep 9555245 = 3583217) B3583217
theorem B1887563 : Blo 1116628 1887563 := bstep (se 1 (by rfl) ⟨1415672, by rfl⟩ : syracuseStep 1887563 = 2831345) B2831345
theorem B14339429 : Blo 1116628 14339429 := bstep (se 4 (by rfl) ⟨1344321, by rfl⟩ : syracuseStep 14339429 = 2688643) B2688643
theorem B1887691 : Blo 1116628 1887691 := bstep (se 1 (by rfl) ⟨1415768, by rfl⟩ : syracuseStep 1887691 = 2831537) B2831537
theorem B4247063 : Blo 1116628 4247063 := bstep (se 1 (by rfl) ⟨3185297, by rfl⟩ : syracuseStep 4247063 = 6370595) B6370595
theorem B1887833 : Blo 1116628 1887833 := bstep (se 2 (by rfl) ⟨707937, by rfl⟩ : syracuseStep 1887833 = 1415875) B1415875
theorem B10210967 : Blo 1116628 10210967 := bstep (se 1 (by rfl) ⟨7658225, by rfl⟩ : syracuseStep 10210967 = 15316451) B15316451
theorem B2150041 : Blo 1116628 2150041 := bstep (se 2 (by rfl) ⟨806265, by rfl⟩ : syracuseStep 2150041 = 1612531) B1612531
theorem B2018969 : Blo 1116628 2018969 := bstep (se 2 (by rfl) ⟨757113, by rfl⟩ : syracuseStep 2018969 = 1514227) B1514227
theorem B1887961 : Blo 1116628 1887961 := bstep (se 2 (by rfl) ⟨707985, by rfl⟩ : syracuseStep 1887961 = 1415971) B1415971
theorem B4247261 : Blo 1116628 4247261 := bstep (se 3 (by rfl) ⟨796361, by rfl⟩ : syracuseStep 4247261 = 1592723) B1592723
theorem B1789847 : Blo 1116628 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B6049687 : Blo 1116628 6049687 := bstep (se 1 (by rfl) ⟨4537265, by rfl⟩ : syracuseStep 6049687 = 9074531) B9074531
theorem B2019251 : Blo 1116628 2019251 := bstep (se 1 (by rfl) ⟨1514438, by rfl⟩ : syracuseStep 2019251 = 3028877) B3028877
theorem B1790039 : Blo 1116628 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1888535 : Blo 1116628 1888535 := bstep (se 1 (by rfl) ⟨1416401, by rfl⟩ : syracuseStep 1888535 = 2832803) B2832803
theorem B5656877 : Blo 1116628 5656877 := bstep (se 3 (by rfl) ⟨1060664, by rfl⟩ : syracuseStep 5656877 = 2121329) B2121329
theorem B4772171 : Blo 1116628 4772171 := bstep (se 1 (by rfl) ⟨3579128, by rfl⟩ : syracuseStep 4772171 = 7158257) B7158257
theorem B4542809 : Blo 1116628 4542809 := bstep (se 2 (by rfl) ⟨1703553, by rfl⟩ : syracuseStep 4542809 = 3407107) B3407107
theorem B1888663 : Blo 1116628 1888663 := bstep (se 1 (by rfl) ⟨1416497, by rfl⟩ : syracuseStep 1888663 = 2832995) B2832995
theorem B14504579 : Blo 1116628 14504579 := bstep (se 1 (by rfl) ⟨10878434, by rfl⟩ : syracuseStep 14504579 = 21756869) B21756869
theorem B1790603 : Blo 1116628 1790603 := bstep (se 1 (by rfl) ⟨1342952, by rfl⟩ : syracuseStep 1790603 = 2685905) B2685905
theorem B1790795 : Blo 1116628 1790795 := bstep (se 1 (by rfl) ⟨1343096, by rfl⟩ : syracuseStep 1790795 = 2686193) B2686193
theorem B4772753 : Blo 1116628 4772753 := bstep (se 2 (by rfl) ⟨1789782, by rfl⟩ : syracuseStep 4772753 = 3579565) B3579565
theorem B1790923 : Blo 1116628 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B1889291 : Blo 1116628 1889291 := bstep (se 1 (by rfl) ⟨1416968, by rfl⟩ : syracuseStep 1889291 = 2833937) B2833937
theorem B1889419 : Blo 1116628 1889419 := bstep (se 1 (by rfl) ⟨1417064, by rfl⟩ : syracuseStep 1889419 = 2834129) B2834129
theorem B1889561 : Blo 1116628 1889561 := bstep (se 2 (by rfl) ⟨708585, by rfl⟩ : syracuseStep 1889561 = 1417171) B1417171
theorem B40850837 : Blo 1116628 40850837 := bstep (se 6 (by rfl) ⟨957441, by rfl⟩ : syracuseStep 40850837 = 1914883) B1914883
theorem B1889689 : Blo 1116628 1889689 := bstep (se 2 (by rfl) ⟨708633, by rfl⟩ : syracuseStep 1889689 = 1417267) B1417267
theorem B1791563 : Blo 1116628 1791563 := bstep (se 1 (by rfl) ⟨1343672, by rfl⟩ : syracuseStep 1791563 = 2687345) B2687345
theorem B4249219 : Blo 1116628 4249219 := bstep (se 1 (by rfl) ⟨3186914, by rfl⟩ : syracuseStep 4249219 = 6373829) B6373829
theorem B1791641 : Blo 1116628 1791641 := bstep (se 2 (by rfl) ⟨671865, by rfl⟩ : syracuseStep 1791641 = 1343731) B1343731
theorem B2512601 : Blo 1116628 2512601 := bstep (se 2 (by rfl) ⟨942225, by rfl⟩ : syracuseStep 2512601 = 1884451) B1884451
theorem B2512691 : Blo 1116628 2512691 := bstep (se 1 (by rfl) ⟨1884518, by rfl⟩ : syracuseStep 2512691 = 3769037) B3769037
theorem B2512727 : Blo 1116628 2512727 := bstep (se 1 (by rfl) ⟨1884545, by rfl⟩ : syracuseStep 2512727 = 3769091) B3769091
theorem B4773811 : Blo 1116628 4773811 := bstep (se 1 (by rfl) ⟨3580358, by rfl⟩ : syracuseStep 4773811 = 7160717) B7160717
theorem B4249523 : Blo 1116628 4249523 := bstep (se 1 (by rfl) ⟨3187142, by rfl⟩ : syracuseStep 4249523 = 6374285) B6374285
theorem B2873291 : Blo 1116628 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B1890263 : Blo 1116628 1890263 := bstep (se 1 (by rfl) ⟨1417697, by rfl⟩ : syracuseStep 1890263 = 2835395) B2835395
theorem B2512907 : Blo 1116628 2512907 := bstep (se 1 (by rfl) ⟨1884680, by rfl⟩ : syracuseStep 2512907 = 3769361) B3769361
theorem B1792025 : Blo 1116628 1792025 := bstep (se 2 (by rfl) ⟨672009, by rfl⟩ : syracuseStep 1792025 = 1344019) B1344019
theorem B2512961 : Blo 1116628 2512961 := bstep (se 2 (by rfl) ⟨942360, by rfl⟩ : syracuseStep 2512961 = 1884721) B1884721
theorem B1890391 : Blo 1116628 1890391 := bstep (se 1 (by rfl) ⟨1417793, by rfl⟩ : syracuseStep 1890391 = 2835587) B2835587
theorem B1792153 : Blo 1116628 1792153 := bstep (se 2 (by rfl) ⟨672057, by rfl⟩ : syracuseStep 1792153 = 1344115) B1344115
theorem B18143473 : Blo 1116628 18143473 := bstep (se 2 (by rfl) ⟨6803802, by rfl⟩ : syracuseStep 18143473 = 13607605) B13607605
theorem B2513177 : Blo 1116628 2513177 := bstep (se 2 (by rfl) ⟨942441, by rfl⟩ : syracuseStep 2513177 = 1884883) B1884883
theorem B2120023 : Blo 1116628 2120023 := bstep (se 1 (by rfl) ⟨1590017, by rfl⟩ : syracuseStep 2120023 = 3180035) B3180035
theorem B2513267 : Blo 1116628 2513267 := bstep (se 1 (by rfl) ⟨1884950, by rfl⟩ : syracuseStep 2513267 = 3769901) B3769901
theorem B2513303 : Blo 1116628 2513303 := bstep (se 1 (by rfl) ⟨1884977, by rfl⟩ : syracuseStep 2513303 = 3769955) B3769955
theorem B4250177 : Blo 1116628 4250177 := bstep (se 2 (by rfl) ⟨1593816, by rfl⟩ : syracuseStep 4250177 = 3187633) B3187633
theorem B2513483 : Blo 1116628 2513483 := bstep (se 1 (by rfl) ⟨1885112, by rfl⟩ : syracuseStep 2513483 = 3770225) B3770225
theorem B2513537 : Blo 1116628 2513537 := bstep (se 2 (by rfl) ⟨942576, by rfl⟩ : syracuseStep 2513537 = 1885153) B1885153
theorem B10738307 : Blo 1116628 10738307 := bstep (se 1 (by rfl) ⟨8053730, by rfl⟩ : syracuseStep 10738307 = 16107461) B16107461
theorem B1891019 : Blo 1116628 1891019 := bstep (se 1 (by rfl) ⟨1418264, by rfl⟩ : syracuseStep 1891019 = 2836529) B2836529
theorem B68836067 : Blo 1116628 68836067 := bstep (se 1 (by rfl) ⟨51627050, by rfl⟩ : syracuseStep 68836067 = 103254101) B103254101
theorem B4840195 : Blo 1116628 4840195 := bstep (se 1 (by rfl) ⟨3630146, by rfl⟩ : syracuseStep 4840195 = 7260293) B7260293
theorem B2513753 : Blo 1116628 2513753 := bstep (se 2 (by rfl) ⟨942657, by rfl⟩ : syracuseStep 2513753 = 1885315) B1885315
theorem B2513843 : Blo 1116628 2513843 := bstep (se 1 (by rfl) ⟨1885382, by rfl⟩ : syracuseStep 2513843 = 3770765) B3770765
theorem B2513879 : Blo 1116628 2513879 := bstep (se 1 (by rfl) ⟨1885409, by rfl⟩ : syracuseStep 2513879 = 3770819) B3770819
theorem B6904793 : Blo 1116628 6904793 := bstep (se 2 (by rfl) ⟨2589297, by rfl⟩ : syracuseStep 6904793 = 5178595) B5178595
theorem B2120843 : Blo 1116628 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B2514059 : Blo 1116628 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B20405429 : Blo 1116628 20405429 := bstep (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) B1913009
theorem B2120897 : Blo 1116628 2120897 := bstep (se 2 (by rfl) ⟨795336, by rfl⟩ : syracuseStep 2120897 = 1590673) B1590673
theorem B2514113 : Blo 1116628 2514113 := bstep (se 2 (by rfl) ⟨942792, by rfl⟩ : syracuseStep 2514113 = 1885585) B1885585
theorem B19127501 : Blo 1116628 19127501 := bstep (se 3 (by rfl) ⟨3586406, by rfl⟩ : syracuseStep 19127501 = 7172813) B7172813
theorem B3398935 : Blo 1116628 3398935 := bstep (se 1 (by rfl) ⟨2549201, by rfl⟩ : syracuseStep 3398935 = 5098403) B5098403
theorem B4775213 : Blo 1116628 4775213 := bstep (se 3 (by rfl) ⟨895352, by rfl⟩ : syracuseStep 4775213 = 1790705) B1790705
theorem B2514329 : Blo 1116628 2514329 := bstep (se 2 (by rfl) ⟨942873, by rfl⟩ : syracuseStep 2514329 = 1885747) B1885747
theorem B2514419 : Blo 1116628 2514419 := bstep (se 1 (by rfl) ⟨1885814, by rfl⟩ : syracuseStep 2514419 = 3771629) B3771629
theorem B2514455 : Blo 1116628 2514455 := bstep (se 1 (by rfl) ⟨1885841, by rfl⟩ : syracuseStep 2514455 = 3771683) B3771683
theorem B2514635 : Blo 1116628 2514635 := bstep (se 1 (by rfl) ⟨1885976, by rfl⟩ : syracuseStep 2514635 = 3771953) B3771953
theorem B2514689 : Blo 1116628 2514689 := bstep (se 2 (by rfl) ⟨943008, by rfl⟩ : syracuseStep 2514689 = 1886017) B1886017
theorem B4251437 : Blo 1116628 4251437 := bstep (se 3 (by rfl) ⟨797144, by rfl⟩ : syracuseStep 4251437 = 1594289) B1594289
theorem B4251467 : Blo 1116628 4251467 := bstep (se 1 (by rfl) ⟨3188600, by rfl⟩ : syracuseStep 4251467 = 6377201) B6377201
theorem B6053707 : Blo 1116628 6053707 := bstep (se 1 (by rfl) ⟨4540280, by rfl⟩ : syracuseStep 6053707 = 9080561) B9080561
theorem B12115889 : Blo 1116628 12115889 := bstep (se 2 (by rfl) ⟨4543458, by rfl⟩ : syracuseStep 12115889 = 9086917) B9086917
theorem B2514905 : Blo 1116628 2514905 := bstep (se 2 (by rfl) ⟨943089, by rfl⟩ : syracuseStep 2514905 = 1886179) B1886179
theorem B2514995 : Blo 1116628 2514995 := bstep (se 1 (by rfl) ⟨1886246, by rfl⟩ : syracuseStep 2514995 = 3772493) B3772493
theorem B2121815 : Blo 1116628 2121815 := bstep (se 1 (by rfl) ⟨1591361, by rfl⟩ : syracuseStep 2121815 = 3182723) B3182723
theorem B2515031 : Blo 1116628 2515031 := bstep (se 1 (by rfl) ⟨1886273, by rfl⟩ : syracuseStep 2515031 = 3772547) B3772547
theorem B5660765 : Blo 1116628 5660765 := bstep (se 3 (by rfl) ⟨1061393, by rfl⟩ : syracuseStep 5660765 = 2122787) B2122787
theorem B1433803 : Blo 1116628 1433803 := bstep (se 1 (by rfl) ⟨1075352, by rfl⟩ : syracuseStep 1433803 = 2150705) B2150705
theorem B14344397 : Blo 1116628 14344397 := bstep (se 3 (by rfl) ⟨2689574, by rfl⟩ : syracuseStep 14344397 = 5379149) B5379149
theorem B2515211 : Blo 1116628 2515211 := bstep (se 1 (by rfl) ⟨1886408, by rfl⟩ : syracuseStep 2515211 = 3772817) B3772817
theorem B2515265 : Blo 1116628 2515265 := bstep (se 2 (by rfl) ⟨943224, by rfl⟩ : syracuseStep 2515265 = 1886449) B1886449
theorem B11493733 : Blo 1116628 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B4252121 : Blo 1116628 4252121 := bstep (se 2 (by rfl) ⟨1594545, by rfl⟩ : syracuseStep 4252121 = 3189091) B3189091
theorem B2515481 : Blo 1116628 2515481 := bstep (se 2 (by rfl) ⟨943305, by rfl⟩ : syracuseStep 2515481 = 1886611) B1886611
theorem B2122355 : Blo 1116628 2122355 := bstep (se 1 (by rfl) ⟨1591766, by rfl⟩ : syracuseStep 2122355 = 3183533) B3183533
theorem B2515571 : Blo 1116628 2515571 := bstep (se 1 (by rfl) ⟨1886678, by rfl⟩ : syracuseStep 2515571 = 3773357) B3773357
theorem B2515607 : Blo 1116628 2515607 := bstep (se 1 (by rfl) ⟨1886705, by rfl⟩ : syracuseStep 2515607 = 3773411) B3773411
theorem B6382259 : Blo 1116628 6382259 := bstep (se 1 (by rfl) ⟨4786694, by rfl⟩ : syracuseStep 6382259 = 9573389) B9573389
theorem B4252439 : Blo 1116628 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B2515787 : Blo 1116628 2515787 := bstep (se 1 (by rfl) ⟨1886840, by rfl⟩ : syracuseStep 2515787 = 3773681) B3773681
theorem B2515841 : Blo 1116628 2515841 := bstep (se 2 (by rfl) ⟨943440, by rfl⟩ : syracuseStep 2515841 = 1886881) B1886881
theorem B2122841 : Blo 1116628 2122841 := bstep (se 2 (by rfl) ⟨796065, by rfl⟩ : syracuseStep 2122841 = 1592131) B1592131
theorem B2516057 : Blo 1116628 2516057 := bstep (se 2 (by rfl) ⟨943521, by rfl⟩ : syracuseStep 2516057 = 1887043) B1887043
theorem B8610947 : Blo 1116628 8610947 := bstep (se 1 (by rfl) ⟨6458210, by rfl⟩ : syracuseStep 8610947 = 12916421) B12916421
theorem B8053937 : Blo 1116628 8053937 := bstep (se 2 (by rfl) ⟨3020226, by rfl⟩ : syracuseStep 8053937 = 6040453) B6040453
theorem B2516147 : Blo 1116628 2516147 := bstep (se 1 (by rfl) ⟨1887110, by rfl⟩ : syracuseStep 2516147 = 3774221) B3774221
theorem B2516183 : Blo 1116628 2516183 := bstep (se 1 (by rfl) ⟨1887137, by rfl⟩ : syracuseStep 2516183 = 3774275) B3774275
theorem B5367001 : Blo 1116628 5367001 := bstep (se 2 (by rfl) ⟨2012625, by rfl⟩ : syracuseStep 5367001 = 4025251) B4025251
theorem B2385163 : Blo 1116628 2385163 := bstep (se 1 (by rfl) ⟨1788872, by rfl⟩ : syracuseStep 2385163 = 3577745) B3577745
theorem B7169381 : Blo 1116628 7169381 := bstep (se 4 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 7169381 = 1344259) B1344259
theorem B14312821 : Blo 1116628 14312821 := bstep (se 5 (by rfl) ⟨670913, by rfl⟩ : syracuseStep 14312821 = 1341827) B1341827
theorem B2516363 : Blo 1116628 2516363 := bstep (se 1 (by rfl) ⟨1887272, by rfl⟩ : syracuseStep 2516363 = 3774545) B3774545
theorem B7169431 : Blo 1116628 7169431 := bstep (se 1 (by rfl) ⟨5377073, by rfl⟩ : syracuseStep 7169431 = 10754147) B10754147
theorem B4253107 : Blo 1116628 4253107 := bstep (se 1 (by rfl) ⟨3189830, by rfl⟩ : syracuseStep 4253107 = 6379661) B6379661
theorem B2516417 : Blo 1116628 2516417 := bstep (se 2 (by rfl) ⟨943656, by rfl⟩ : syracuseStep 2516417 = 1887313) B1887313
theorem B2516633 : Blo 1116628 2516633 := bstep (se 2 (by rfl) ⟨943737, by rfl⟩ : syracuseStep 2516633 = 1887475) B1887475
theorem B2385625 : Blo 1116628 2385625 := bstep (se 2 (by rfl) ⟨894609, by rfl⟩ : syracuseStep 2385625 = 1789219) B1789219
theorem B2516723 : Blo 1116628 2516723 := bstep (se 1 (by rfl) ⟨1887542, by rfl⟩ : syracuseStep 2516723 = 3775085) B3775085
theorem B2516759 : Blo 1116628 2516759 := bstep (se 1 (by rfl) ⟨1887569, by rfl⟩ : syracuseStep 2516759 = 3775139) B3775139
theorem B5367617 : Blo 1116628 5367617 := bstep (se 2 (by rfl) ⟨2012856, by rfl⟩ : syracuseStep 5367617 = 4025713) B4025713
theorem B2516939 : Blo 1116628 2516939 := bstep (se 1 (by rfl) ⟨1887704, by rfl⟩ : syracuseStep 2516939 = 3775409) B3775409
theorem B2516993 : Blo 1116628 2516993 := bstep (se 2 (by rfl) ⟨943872, by rfl⟩ : syracuseStep 2516993 = 1887745) B1887745
theorem B5662871 : Blo 1116628 5662871 := bstep (se 1 (by rfl) ⟨4247153, by rfl⟩ : syracuseStep 5662871 = 8494307) B8494307
theorem B2517209 : Blo 1116628 2517209 := bstep (se 2 (by rfl) ⟨943953, by rfl⟩ : syracuseStep 2517209 = 1887907) B1887907
theorem B2517299 : Blo 1116628 2517299 := bstep (se 1 (by rfl) ⟨1887974, by rfl⟩ : syracuseStep 2517299 = 3775949) B3775949
theorem B2517335 : Blo 1116628 2517335 := bstep (se 1 (by rfl) ⟨1888001, by rfl⟩ : syracuseStep 2517335 = 3776003) B3776003
theorem B2517515 : Blo 1116628 2517515 := bstep (se 1 (by rfl) ⟨1888136, by rfl⟩ : syracuseStep 2517515 = 3776273) B3776273
theorem B2124299 : Blo 1116628 2124299 := bstep (se 1 (by rfl) ⟨1593224, by rfl⟩ : syracuseStep 2124299 = 3186449) B3186449
theorem B2517569 : Blo 1116628 2517569 := bstep (se 2 (by rfl) ⟨944088, by rfl⟩ : syracuseStep 2517569 = 1888177) B1888177
theorem B2550361 : Blo 1116628 2550361 := bstep (se 2 (by rfl) ⟨956385, by rfl⟩ : syracuseStep 2550361 = 1912771) B1912771
theorem B4090457 : Blo 1116628 4090457 := bstep (se 2 (by rfl) ⟨1533921, by rfl⟩ : syracuseStep 4090457 = 3067843) B3067843
theorem B4254353 : Blo 1116628 4254353 := bstep (se 2 (by rfl) ⟨1595382, by rfl⟩ : syracuseStep 4254353 = 3190765) B3190765
theorem B2124481 : Blo 1116628 2124481 := bstep (se 2 (by rfl) ⟨796680, by rfl⟩ : syracuseStep 2124481 = 1593361) B1593361
theorem B2517785 : Blo 1116628 2517785 := bstep (se 2 (by rfl) ⟨944169, by rfl⟩ : syracuseStep 2517785 = 1888339) B1888339
theorem B2517875 : Blo 1116628 2517875 := bstep (se 1 (by rfl) ⟨1888406, by rfl⟩ : syracuseStep 2517875 = 3776813) B3776813
theorem B2517911 : Blo 1116628 2517911 := bstep (se 1 (by rfl) ⟨1888433, by rfl⟩ : syracuseStep 2517911 = 3776867) B3776867
theorem B2387009 : Blo 1116628 2387009 := bstep (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) B1790257
theorem B2518091 : Blo 1116628 2518091 := bstep (se 1 (by rfl) ⟨1888568, by rfl⟩ : syracuseStep 2518091 = 3777137) B3777137
theorem B2518145 : Blo 1116628 2518145 := bstep (se 2 (by rfl) ⟨944304, by rfl⟩ : syracuseStep 2518145 = 1888609) B1888609
theorem B2124929 : Blo 1116628 2124929 := bstep (se 2 (by rfl) ⟨796848, by rfl⟩ : syracuseStep 2124929 = 1593697) B1593697
theorem B2518361 : Blo 1116628 2518361 := bstep (se 2 (by rfl) ⟨944385, by rfl⟩ : syracuseStep 2518361 = 1888771) B1888771
theorem B4779415 : Blo 1116628 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B2518451 : Blo 1116628 2518451 := bstep (se 1 (by rfl) ⟨1888838, by rfl⟩ : syracuseStep 2518451 = 3777677) B3777677
theorem B2125271 : Blo 1116628 2125271 := bstep (se 1 (by rfl) ⟨1593953, by rfl⟩ : syracuseStep 2125271 = 3187907) B3187907
theorem B2518487 : Blo 1116628 2518487 := bstep (se 1 (by rfl) ⟨1888865, by rfl⟩ : syracuseStep 2518487 = 3777731) B3777731
theorem B4779485 : Blo 1116628 4779485 := bstep (se 3 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 4779485 = 1792307) B1792307
theorem B8056385 : Blo 1116628 8056385 := bstep (se 2 (by rfl) ⟨3021144, by rfl⟩ : syracuseStep 8056385 = 6042289) B6042289
theorem B17198723 : Blo 1116628 17198723 := bstep (se 1 (by rfl) ⟨12899042, by rfl⟩ : syracuseStep 17198723 = 25798085) B25798085
theorem B2518667 : Blo 1116628 2518667 := bstep (se 1 (by rfl) ⟨1889000, by rfl⟩ : syracuseStep 2518667 = 3778001) B3778001
theorem B2518721 : Blo 1116628 2518721 := bstep (se 2 (by rfl) ⟨944520, by rfl⟩ : syracuseStep 2518721 = 1889041) B1889041
theorem B1699735 : Blo 1116628 1699735 := bstep (se 1 (by rfl) ⟨1274801, by rfl⟩ : syracuseStep 1699735 = 2549603) B2549603
theorem B2518937 : Blo 1116628 2518937 := bstep (se 2 (by rfl) ⟨944601, by rfl⟩ : syracuseStep 2518937 = 1889203) B1889203
theorem B2519027 : Blo 1116628 2519027 := bstep (se 1 (by rfl) ⟨1889270, by rfl⟩ : syracuseStep 2519027 = 3778541) B3778541
theorem B2519063 : Blo 1116628 2519063 := bstep (se 1 (by rfl) ⟨1889297, by rfl⟩ : syracuseStep 2519063 = 3778595) B3778595
theorem B2125939 : Blo 1116628 2125939 := bstep (se 1 (by rfl) ⟨1594454, by rfl⟩ : syracuseStep 2125939 = 3188909) B3188909
theorem B42987671 : Blo 1116628 42987671 := bstep (se 1 (by rfl) ⟨32240753, by rfl⟩ : syracuseStep 42987671 = 64481507) B64481507
theorem B2519243 : Blo 1116628 2519243 := bstep (se 1 (by rfl) ⟨1889432, by rfl⟩ : syracuseStep 2519243 = 3778865) B3778865
theorem B4780235 : Blo 1116628 4780235 := bstep (se 1 (by rfl) ⟨3585176, by rfl⟩ : syracuseStep 4780235 = 7170353) B7170353
theorem B2519297 : Blo 1116628 2519297 := bstep (se 2 (by rfl) ⟨944736, by rfl⟩ : syracuseStep 2519297 = 1889473) B1889473
theorem B2519513 : Blo 1116628 2519513 := bstep (se 2 (by rfl) ⟨944817, by rfl⟩ : syracuseStep 2519513 = 1889635) B1889635
theorem B2683415 : Blo 1116628 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B2519603 : Blo 1116628 2519603 := bstep (se 1 (by rfl) ⟨1889702, by rfl⟩ : syracuseStep 2519603 = 3779405) B3779405
theorem B2126387 : Blo 1116628 2126387 := bstep (se 1 (by rfl) ⟨1594790, by rfl⟩ : syracuseStep 2126387 = 3189581) B3189581
theorem B2519639 : Blo 1116628 2519639 := bstep (se 1 (by rfl) ⟨1889729, by rfl⟩ : syracuseStep 2519639 = 3779459) B3779459
theorem B2126425 : Blo 1116628 2126425 := bstep (se 2 (by rfl) ⟨797409, by rfl⟩ : syracuseStep 2126425 = 1594819) B1594819
theorem B2388683 : Blo 1116628 2388683 := bstep (se 1 (by rfl) ⟨1791512, by rfl⟩ : syracuseStep 2388683 = 3583025) B3583025
theorem B4027097 : Blo 1116628 4027097 := bstep (se 2 (by rfl) ⟨1510161, by rfl⟩ : syracuseStep 4027097 = 3020323) B3020323
theorem B2519819 : Blo 1116628 2519819 := bstep (se 1 (by rfl) ⟨1889864, by rfl⟩ : syracuseStep 2519819 = 3779729) B3779729
theorem B2519873 : Blo 1116628 2519873 := bstep (se 2 (by rfl) ⟨944952, by rfl⟩ : syracuseStep 2519873 = 1889905) B1889905
theorem B1700683 : Blo 1116628 1700683 := bstep (se 1 (by rfl) ⟨1275512, by rfl⟩ : syracuseStep 1700683 = 2551025) B2551025
theorem B5895005 : Blo 1116628 5895005 := bstep (se 3 (by rfl) ⟨1105313, by rfl⟩ : syracuseStep 5895005 = 2210627) B2210627
theorem B2552705 : Blo 1116628 2552705 := bstep (se 2 (by rfl) ⟨957264, by rfl⟩ : syracuseStep 2552705 = 1914529) B1914529
theorem B7172995 : Blo 1116628 7172995 := bstep (se 1 (by rfl) ⟨5379746, by rfl⟩ : syracuseStep 7172995 = 10759493) B10759493
theorem B4027315 : Blo 1116628 4027315 := bstep (se 1 (by rfl) ⟨3020486, by rfl⟩ : syracuseStep 4027315 = 6040973) B6040973
theorem B2520089 : Blo 1116628 2520089 := bstep (se 2 (by rfl) ⟨945033, by rfl⟩ : syracuseStep 2520089 = 1890067) B1890067
theorem B2126873 : Blo 1116628 2126873 := bstep (se 2 (by rfl) ⟨797577, by rfl⟩ : syracuseStep 2126873 = 1595155) B1595155
theorem B2520179 : Blo 1116628 2520179 := bstep (se 1 (by rfl) ⟨1890134, by rfl⟩ : syracuseStep 2520179 = 3780269) B3780269
theorem B2520215 : Blo 1116628 2520215 := bstep (se 1 (by rfl) ⟨1890161, by rfl⟩ : syracuseStep 2520215 = 3780323) B3780323
theorem B8484101 : Blo 1116628 8484101 := bstep (se 4 (by rfl) ⟨795384, by rfl⟩ : syracuseStep 8484101 = 1590769) B1590769
theorem B2520395 : Blo 1116628 2520395 := bstep (se 1 (by rfl) ⟨1890296, by rfl⟩ : syracuseStep 2520395 = 3780593) B3780593
theorem B2520449 : Blo 1116628 2520449 := bstep (se 2 (by rfl) ⟨945168, by rfl⟩ : syracuseStep 2520449 = 1890337) B1890337
theorem B2520665 : Blo 1116628 2520665 := bstep (se 2 (by rfl) ⟨945249, by rfl⟩ : syracuseStep 2520665 = 1890499) B1890499
theorem B5666435 : Blo 1116628 5666435 := bstep (se 1 (by rfl) ⟨4249826, by rfl⟩ : syracuseStep 5666435 = 8499653) B8499653
theorem B2389657 : Blo 1116628 2389657 := bstep (se 2 (by rfl) ⟨896121, by rfl⟩ : syracuseStep 2389657 = 1792243) B1792243
theorem B2520755 : Blo 1116628 2520755 := bstep (se 1 (by rfl) ⟨1890566, by rfl⟩ : syracuseStep 2520755 = 3781133) B3781133
theorem B2520791 : Blo 1116628 2520791 := bstep (se 1 (by rfl) ⟨1890593, by rfl⟩ : syracuseStep 2520791 = 3781187) B3781187
theorem B4028249 : Blo 1116628 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B2520971 : Blo 1116628 2520971 := bstep (se 1 (by rfl) ⟨1890728, by rfl⟩ : syracuseStep 2520971 = 3781457) B3781457
theorem B2389913 : Blo 1116628 2389913 := bstep (se 2 (by rfl) ⟨896217, by rfl⟩ : syracuseStep 2389913 = 1792435) B1792435
theorem B15333299 : Blo 1116628 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B2521025 : Blo 1116628 2521025 := bstep (se 2 (by rfl) ⟨945384, by rfl⟩ : syracuseStep 2521025 = 1890769) B1890769
theorem B2521241 : Blo 1116628 2521241 := bstep (se 2 (by rfl) ⟨945465, by rfl⟩ : syracuseStep 2521241 = 1890931) B1890931
theorem B2521331 : Blo 1116628 2521331 := bstep (se 1 (by rfl) ⟨1890998, by rfl⟩ : syracuseStep 2521331 = 3781997) B3781997
theorem B2521367 : Blo 1116628 2521367 := bstep (se 1 (by rfl) ⟨1891025, by rfl⟩ : syracuseStep 2521367 = 3782051) B3782051
theorem B2390323 : Blo 1116628 2390323 := bstep (se 1 (by rfl) ⟨1792742, by rfl⟩ : syracuseStep 2390323 = 3585485) B3585485
theorem B3832343 : Blo 1116628 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B2391041 : Blo 1116628 2391041 := bstep (se 2 (by rfl) ⟨896640, by rfl⟩ : syracuseStep 2391041 = 1793281) B1793281
theorem B2391383 : Blo 1116628 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B16317875 : Blo 1116628 16317875 := bstep (se 1 (by rfl) ⟨12238406, by rfl⟩ : syracuseStep 16317875 = 24476813) B24476813
theorem B2555351 : Blo 1116628 2555351 := bstep (se 1 (by rfl) ⟨1916513, by rfl⟩ : syracuseStep 2555351 = 3833027) B3833027
theorem B2391553 : Blo 1116628 2391553 := bstep (se 2 (by rfl) ⟨896832, by rfl⟩ : syracuseStep 2391553 = 1793665) B1793665
theorem B14319179 : Blo 1116628 14319179 := bstep (se 1 (by rfl) ⟨10739384, by rfl⟩ : syracuseStep 14319179 = 21478769) B21478769
theorem B2555479 : Blo 1116628 2555479 := bstep (se 1 (by rfl) ⟨1916609, by rfl⟩ : syracuseStep 2555479 = 3833219) B3833219
theorem B8486531 : Blo 1116628 8486531 := bstep (se 1 (by rfl) ⟨6364898, by rfl⟩ : syracuseStep 8486531 = 12729797) B12729797
theorem B2555543 : Blo 1116628 2555543 := bstep (se 1 (by rfl) ⟨1916657, by rfl⟩ : syracuseStep 2555543 = 3833315) B3833315
theorem B4783789 : Blo 1116628 4783789 := bstep (se 3 (by rfl) ⟨896960, by rfl⟩ : syracuseStep 4783789 = 1793921) B1793921
theorem B4030211 : Blo 1116628 4030211 := bstep (se 1 (by rfl) ⟨3022658, by rfl⟩ : syracuseStep 4030211 = 6045317) B6045317
theorem B4783961 : Blo 1116628 4783961 := bstep (se 2 (by rfl) ⟨1793985, by rfl⟩ : syracuseStep 4783961 = 3587971) B3587971
theorem B30637925 : Blo 1116628 30637925 := bstep (se 4 (by rfl) ⟨2872305, by rfl⟩ : syracuseStep 30637925 = 5744611) B5744611
theorem B2425033 : Blo 1116628 2425033 := bstep (se 2 (by rfl) ⟨909387, by rfl⟩ : syracuseStep 2425033 = 1818775) B1818775
theorem B12747293 : Blo 1116628 12747293 := bstep (se 3 (by rfl) ⟨2390117, by rfl⟩ : syracuseStep 12747293 = 4780235) B4780235
theorem B3768875 : Blo 1116628 3768875 := bstep (se 1 (by rfl) ⟨2826656, by rfl⟩ : syracuseStep 3768875 = 5653313) B5653313
theorem B18612803 : Blo 1116628 18612803 := bstep (se 1 (by rfl) ⟨13959602, by rfl⟩ : syracuseStep 18612803 = 27919205) B27919205
theorem B2720855 : Blo 1116628 2720855 := bstep (se 1 (by rfl) ⟨2040641, by rfl⟩ : syracuseStep 2720855 = 4081283) B4081283
theorem B3180217 : Blo 1116628 3180217 := bstep (se 2 (by rfl) ⟨1192581, by rfl⟩ : syracuseStep 3180217 = 2385163) B2385163
theorem B3770171 : Blo 1116628 3770171 := bstep (se 1 (by rfl) ⟨2827628, by rfl⟩ : syracuseStep 3770171 = 5655257) B5655257
theorem B5670809 : Blo 1116628 5670809 := bstep (se 2 (by rfl) ⟨2126553, by rfl⟩ : syracuseStep 5670809 = 4253107) B4253107
theorem B3180559 : Blo 1116628 3180559 := bstep (se 1 (by rfl) ⟨2385419, by rfl⟩ : syracuseStep 3180559 = 4770839) B4770839
theorem B7178327 : Blo 1116628 7178327 := bstep (se 1 (by rfl) ⟨5383745, by rfl⟩ : syracuseStep 7178327 = 10767491) B10767491
theorem B16124021 : Blo 1116628 16124021 := bstep (se 5 (by rfl) ⟨755813, by rfl⟩ : syracuseStep 16124021 = 1511627) B1511627
theorem B3180833 : Blo 1116628 3180833 := bstep (se 2 (by rfl) ⟨1192812, by rfl⟩ : syracuseStep 3180833 = 2385625) B2385625
theorem B3770657 : Blo 1116628 3770657 := bstep (se 2 (by rfl) ⟨1413996, by rfl⟩ : syracuseStep 3770657 = 2827993) B2827993
theorem B1345979 : Blo 1116628 1345979 := bstep (se 1 (by rfl) ⟨1009484, by rfl⟩ : syracuseStep 1345979 = 2018969) B2018969
theorem B1116679 : Blo 1116628 1116679 := bstep (se 1 (by rfl) ⟨837509, by rfl⟩ : syracuseStep 1116679 = 1675019) B1675019
theorem B1116687 : Blo 1116628 1116687 := bstep (se 1 (by rfl) ⟨837515, by rfl⟩ : syracuseStep 1116687 = 1675031) B1675031
theorem B1116731 : Blo 1116628 1116731 := bstep (se 1 (by rfl) ⟨837548, by rfl⟩ : syracuseStep 1116731 = 1675097) B1675097
theorem B2689595 : Blo 1116628 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B1346167 : Blo 1116628 1346167 := bstep (se 1 (by rfl) ⟨1009625, by rfl⟩ : syracuseStep 1346167 = 2019251) B2019251
theorem B1116807 : Blo 1116628 1116807 := bstep (se 1 (by rfl) ⟨837605, by rfl⟩ : syracuseStep 1116807 = 1675211) B1675211
theorem B1116815 : Blo 1116628 1116815 := bstep (se 1 (by rfl) ⟨837611, by rfl⟩ : syracuseStep 1116815 = 1675223) B1675223
theorem B1116859 : Blo 1116628 1116859 := bstep (se 1 (by rfl) ⟨837644, by rfl⟩ : syracuseStep 1116859 = 1675289) B1675289
theorem B1116935 : Blo 1116628 1116935 := bstep (se 1 (by rfl) ⟨837701, by rfl⟩ : syracuseStep 1116935 = 1675403) B1675403
theorem B1116943 : Blo 1116628 1116943 := bstep (se 1 (by rfl) ⟨837707, by rfl⟩ : syracuseStep 1116943 = 1675415) B1675415
theorem B1116987 : Blo 1116628 1116987 := bstep (se 1 (by rfl) ⟨837740, by rfl⟩ : syracuseStep 1116987 = 1675481) B1675481
theorem B3771251 : Blo 1116628 3771251 := bstep (se 1 (by rfl) ⟨2828438, by rfl⟩ : syracuseStep 3771251 = 5656877) B5656877
theorem B1117063 : Blo 1116628 1117063 := bstep (se 1 (by rfl) ⟨837797, by rfl⟩ : syracuseStep 1117063 = 1675595) B1675595
theorem B3181447 : Blo 1116628 3181447 := bstep (se 1 (by rfl) ⟨2386085, by rfl⟩ : syracuseStep 3181447 = 4772171) B4772171
theorem B1117071 : Blo 1116628 1117071 := bstep (se 1 (by rfl) ⟨837803, by rfl⟩ : syracuseStep 1117071 = 1675607) B1675607
theorem B1117115 : Blo 1116628 1117115 := bstep (se 1 (by rfl) ⟨837836, by rfl⟩ : syracuseStep 1117115 = 1675673) B1675673
theorem B1117191 : Blo 1116628 1117191 := bstep (se 1 (by rfl) ⟨837893, by rfl⟩ : syracuseStep 1117191 = 1675787) B1675787
theorem B1117199 : Blo 1116628 1117199 := bstep (se 1 (by rfl) ⟨837899, by rfl⟩ : syracuseStep 1117199 = 1675799) B1675799
theorem B1117243 : Blo 1116628 1117243 := bstep (se 1 (by rfl) ⟨837932, by rfl⟩ : syracuseStep 1117243 = 1675865) B1675865
theorem B9669719 : Blo 1116628 9669719 := bstep (se 1 (by rfl) ⟨7252289, by rfl⟩ : syracuseStep 9669719 = 14504579) B14504579
theorem B1117319 : Blo 1116628 1117319 := bstep (se 1 (by rfl) ⟨837989, by rfl⟩ : syracuseStep 1117319 = 1675979) B1675979
theorem B1117327 : Blo 1116628 1117327 := bstep (se 1 (by rfl) ⟨837995, by rfl⟩ : syracuseStep 1117327 = 1675991) B1675991
theorem B1117371 : Blo 1116628 1117371 := bstep (se 1 (by rfl) ⟨838028, by rfl⟩ : syracuseStep 1117371 = 1676057) B1676057
theorem B1117447 : Blo 1116628 1117447 := bstep (se 1 (by rfl) ⟨838085, by rfl⟩ : syracuseStep 1117447 = 1676171) B1676171
theorem B3181835 : Blo 1116628 3181835 := bstep (se 1 (by rfl) ⟨2386376, by rfl⟩ : syracuseStep 3181835 = 4772753) B4772753
theorem B1117455 : Blo 1116628 1117455 := bstep (se 1 (by rfl) ⟨838091, by rfl⟩ : syracuseStep 1117455 = 1676183) B1676183
theorem B1117499 : Blo 1116628 1117499 := bstep (se 1 (by rfl) ⟨838124, by rfl⟩ : syracuseStep 1117499 = 1676249) B1676249
theorem B1117575 : Blo 1116628 1117575 := bstep (se 1 (by rfl) ⟨838181, by rfl⟩ : syracuseStep 1117575 = 1676363) B1676363
theorem B1117583 : Blo 1116628 1117583 := bstep (se 1 (by rfl) ⟨838187, by rfl⟩ : syracuseStep 1117583 = 1676375) B1676375
theorem B2690489 : Blo 1116628 2690489 := bstep (se 2 (by rfl) ⟨1008933, by rfl⟩ : syracuseStep 2690489 = 2017867) B2017867
theorem B1117627 : Blo 1116628 1117627 := bstep (se 1 (by rfl) ⟨838220, by rfl⟩ : syracuseStep 1117627 = 1676441) B1676441
theorem B1117703 : Blo 1116628 1117703 := bstep (se 1 (by rfl) ⟨838277, by rfl⟩ : syracuseStep 1117703 = 1676555) B1676555
theorem B1117711 : Blo 1116628 1117711 := bstep (se 1 (by rfl) ⟨838283, by rfl⟩ : syracuseStep 1117711 = 1676567) B1676567
theorem B1117755 : Blo 1116628 1117755 := bstep (se 1 (by rfl) ⟨838316, by rfl⟩ : syracuseStep 1117755 = 1676633) B1676633
theorem B27233891 : Blo 1116628 27233891 := bstep (se 1 (by rfl) ⟨20425418, by rfl⟩ : syracuseStep 27233891 = 40850837) B40850837
theorem B1117831 : Blo 1116628 1117831 := bstep (se 1 (by rfl) ⟨838373, by rfl⟩ : syracuseStep 1117831 = 1676747) B1676747
theorem B1117839 : Blo 1116628 1117839 := bstep (se 1 (by rfl) ⟨838379, by rfl⟩ : syracuseStep 1117839 = 1676759) B1676759
theorem B1117883 : Blo 1116628 1117883 := bstep (se 1 (by rfl) ⟨838412, by rfl⟩ : syracuseStep 1117883 = 1676825) B1676825
theorem B1674953 : Blo 1116628 1674953 := bstep (se 2 (by rfl) ⟨628107, by rfl⟩ : syracuseStep 1674953 = 1256215) B1256215
theorem B1117959 : Blo 1116628 1117959 := bstep (se 1 (by rfl) ⟨838469, by rfl⟩ : syracuseStep 1117959 = 1676939) B1676939
theorem B1117967 : Blo 1116628 1117967 := bstep (se 1 (by rfl) ⟨838475, by rfl⟩ : syracuseStep 1117967 = 1676951) B1676951
theorem B1675067 : Blo 1116628 1675067 := bstep (se 1 (by rfl) ⟨1256300, by rfl⟩ : syracuseStep 1675067 = 2512601) B2512601
theorem B1118011 : Blo 1116628 1118011 := bstep (se 1 (by rfl) ⟨838508, by rfl⟩ : syracuseStep 1118011 = 1677017) B1677017
theorem B1675127 : Blo 1116628 1675127 := bstep (se 1 (by rfl) ⟨1256345, by rfl⟩ : syracuseStep 1675127 = 2512691) B2512691
theorem B1118087 : Blo 1116628 1118087 := bstep (se 1 (by rfl) ⟨838565, by rfl⟩ : syracuseStep 1118087 = 1677131) B1677131
theorem B1675151 : Blo 1116628 1675151 := bstep (se 1 (by rfl) ⟨1256363, by rfl⟩ : syracuseStep 1675151 = 2512727) B2512727
theorem B1118095 : Blo 1116628 1118095 := bstep (se 1 (by rfl) ⟨838571, by rfl⟩ : syracuseStep 1118095 = 1677143) B1677143
theorem B8490905 : Blo 1116628 8490905 := bstep (se 2 (by rfl) ⟨3184089, by rfl⟩ : syracuseStep 8490905 = 6368179) B6368179
theorem B1675193 : Blo 1116628 1675193 := bstep (se 2 (by rfl) ⟨628197, by rfl⟩ : syracuseStep 1675193 = 1256395) B1256395
theorem B1118139 : Blo 1116628 1118139 := bstep (se 1 (by rfl) ⟨838604, by rfl⟩ : syracuseStep 1118139 = 1677209) B1677209
theorem B1675271 : Blo 1116628 1675271 := bstep (se 1 (by rfl) ⟨1256453, by rfl⟩ : syracuseStep 1675271 = 2512907) B2512907
theorem B1118215 : Blo 1116628 1118215 := bstep (se 1 (by rfl) ⟨838661, by rfl⟩ : syracuseStep 1118215 = 1677323) B1677323
theorem B9572363 : Blo 1116628 9572363 := bstep (se 1 (by rfl) ⟨7179272, by rfl⟩ : syracuseStep 9572363 = 14358545) B14358545
theorem B1118223 : Blo 1116628 1118223 := bstep (se 1 (by rfl) ⟨838667, by rfl⟩ : syracuseStep 1118223 = 1677335) B1677335
theorem B1675307 : Blo 1116628 1675307 := bstep (se 1 (by rfl) ⟨1256480, by rfl⟩ : syracuseStep 1675307 = 2512961) B2512961
theorem B1118267 : Blo 1116628 1118267 := bstep (se 1 (by rfl) ⟨838700, by rfl⟩ : syracuseStep 1118267 = 1677401) B1677401
theorem B1675337 : Blo 1116628 1675337 := bstep (se 2 (by rfl) ⟨628251, by rfl⟩ : syracuseStep 1675337 = 1256503) B1256503
theorem B1118343 : Blo 1116628 1118343 := bstep (se 1 (by rfl) ⟨838757, by rfl⟩ : syracuseStep 1118343 = 1677515) B1677515
theorem B1118351 : Blo 1116628 1118351 := bstep (se 1 (by rfl) ⟨838763, by rfl⟩ : syracuseStep 1118351 = 1677527) B1677527
theorem B1675451 : Blo 1116628 1675451 := bstep (se 1 (by rfl) ⟨1256588, by rfl⟩ : syracuseStep 1675451 = 2513177) B2513177
theorem B1118395 : Blo 1116628 1118395 := bstep (se 1 (by rfl) ⟨838796, by rfl⟩ : syracuseStep 1118395 = 1677593) B1677593
theorem B1675511 : Blo 1116628 1675511 := bstep (se 1 (by rfl) ⟨1256633, by rfl⟩ : syracuseStep 1675511 = 2513267) B2513267
theorem B1118471 : Blo 1116628 1118471 := bstep (se 1 (by rfl) ⟨838853, by rfl⟩ : syracuseStep 1118471 = 1677707) B1677707
theorem B1675535 : Blo 1116628 1675535 := bstep (se 1 (by rfl) ⟨1256651, by rfl⟩ : syracuseStep 1675535 = 2513303) B2513303
theorem B1118479 : Blo 1116628 1118479 := bstep (se 1 (by rfl) ⟨838859, by rfl⟩ : syracuseStep 1118479 = 1677719) B1677719
theorem B2691343 : Blo 1116628 2691343 := bstep (se 1 (by rfl) ⟨2018507, by rfl⟩ : syracuseStep 2691343 = 4037015) B4037015
theorem B1675577 : Blo 1116628 1675577 := bstep (se 2 (by rfl) ⟨628341, by rfl⟩ : syracuseStep 1675577 = 1256683) B1256683
theorem B1118523 : Blo 1116628 1118523 := bstep (se 1 (by rfl) ⟨838892, by rfl⟩ : syracuseStep 1118523 = 1677785) B1677785
theorem B1675655 : Blo 1116628 1675655 := bstep (se 1 (by rfl) ⟨1256741, by rfl⟩ : syracuseStep 1675655 = 2513483) B2513483
theorem B1118599 : Blo 1116628 1118599 := bstep (se 1 (by rfl) ⟨838949, by rfl⟩ : syracuseStep 1118599 = 1677899) B1677899
theorem B1118607 : Blo 1116628 1118607 := bstep (se 1 (by rfl) ⟨838955, by rfl⟩ : syracuseStep 1118607 = 1677911) B1677911
theorem B1675691 : Blo 1116628 1675691 := bstep (se 1 (by rfl) ⟨1256768, by rfl⟩ : syracuseStep 1675691 = 2513537) B2513537
theorem B8622521 : Blo 1116628 8622521 := bstep (se 2 (by rfl) ⟨3233445, by rfl⟩ : syracuseStep 8622521 = 6466891) B6466891
theorem B1118651 : Blo 1116628 1118651 := bstep (se 1 (by rfl) ⟨838988, by rfl⟩ : syracuseStep 1118651 = 1677977) B1677977
theorem B1675721 : Blo 1116628 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B1118727 : Blo 1116628 1118727 := bstep (se 1 (by rfl) ⟨839045, by rfl⟩ : syracuseStep 1118727 = 1678091) B1678091
theorem B1118735 : Blo 1116628 1118735 := bstep (se 1 (by rfl) ⟨839051, by rfl⟩ : syracuseStep 1118735 = 1678103) B1678103
theorem B3183133 : Blo 1116628 3183133 := bstep (se 3 (by rfl) ⟨596837, by rfl⟩ : syracuseStep 3183133 = 1193675) B1193675
theorem B1675835 : Blo 1116628 1675835 := bstep (se 1 (by rfl) ⟨1256876, by rfl⟩ : syracuseStep 1675835 = 2513753) B2513753
theorem B1118779 : Blo 1116628 1118779 := bstep (se 1 (by rfl) ⟨839084, by rfl⟩ : syracuseStep 1118779 = 1678169) B1678169
theorem B2691643 : Blo 1116628 2691643 := bstep (se 1 (by rfl) ⟨2018732, by rfl⟩ : syracuseStep 2691643 = 4037465) B4037465
theorem B1675895 : Blo 1116628 1675895 := bstep (se 1 (by rfl) ⟨1256921, by rfl⟩ : syracuseStep 1675895 = 2513843) B2513843
theorem B1118855 : Blo 1116628 1118855 := bstep (se 1 (by rfl) ⟨839141, by rfl⟩ : syracuseStep 1118855 = 1678283) B1678283
theorem B2691719 : Blo 1116628 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B1675919 : Blo 1116628 1675919 := bstep (se 1 (by rfl) ⟨1256939, by rfl⟩ : syracuseStep 1675919 = 2513879) B2513879
theorem B1118863 : Blo 1116628 1118863 := bstep (se 1 (by rfl) ⟨839147, by rfl⟩ : syracuseStep 1118863 = 1678295) B1678295
theorem B1675961 : Blo 1116628 1675961 := bstep (se 2 (by rfl) ⟨628485, by rfl⟩ : syracuseStep 1675961 = 1256971) B1256971
theorem B1118907 : Blo 1116628 1118907 := bstep (se 1 (by rfl) ⟨839180, by rfl⟩ : syracuseStep 1118907 = 1678361) B1678361
theorem B1676039 : Blo 1116628 1676039 := bstep (se 1 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 1676039 = 2514059) B2514059
theorem B1118983 : Blo 1116628 1118983 := bstep (se 1 (by rfl) ⟨839237, by rfl⟩ : syracuseStep 1118983 = 1678475) B1678475
theorem B1118991 : Blo 1116628 1118991 := bstep (se 1 (by rfl) ⟨839243, by rfl⟩ : syracuseStep 1118991 = 1678487) B1678487
theorem B13603619 : Blo 1116628 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B1413931 : Blo 1116628 1413931 := bstep (se 1 (by rfl) ⟨1060448, by rfl⟩ : syracuseStep 1413931 = 2120897) B2120897
theorem B1676075 : Blo 1116628 1676075 := bstep (se 1 (by rfl) ⟨1257056, by rfl⟩ : syracuseStep 1676075 = 2514113) B2514113
theorem B12751667 : Blo 1116628 12751667 := bstep (se 1 (by rfl) ⟨9563750, by rfl⟩ : syracuseStep 12751667 = 19127501) B19127501
theorem B1119035 : Blo 1116628 1119035 := bstep (se 1 (by rfl) ⟨839276, by rfl⟩ : syracuseStep 1119035 = 1678553) B1678553
theorem B1676105 : Blo 1116628 1676105 := bstep (se 2 (by rfl) ⟨628539, by rfl⟩ : syracuseStep 1676105 = 1257079) B1257079
theorem B3183475 : Blo 1116628 3183475 := bstep (se 1 (by rfl) ⟨2387606, by rfl⟩ : syracuseStep 3183475 = 4775213) B4775213
theorem B1119111 : Blo 1116628 1119111 := bstep (se 1 (by rfl) ⟨839333, by rfl⟩ : syracuseStep 1119111 = 1678667) B1678667
theorem B1119119 : Blo 1116628 1119119 := bstep (se 1 (by rfl) ⟨839339, by rfl⟩ : syracuseStep 1119119 = 1678679) B1678679
theorem B1676219 : Blo 1116628 1676219 := bstep (se 1 (by rfl) ⟨1257164, by rfl⟩ : syracuseStep 1676219 = 2514329) B2514329
theorem B1119163 : Blo 1116628 1119163 := bstep (se 1 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 1119163 = 1678745) B1678745
theorem B1676279 : Blo 1116628 1676279 := bstep (se 1 (by rfl) ⟨1257209, by rfl⟩ : syracuseStep 1676279 = 2514419) B2514419
theorem B1119239 : Blo 1116628 1119239 := bstep (se 1 (by rfl) ⟨839429, by rfl⟩ : syracuseStep 1119239 = 1678859) B1678859
theorem B1676303 : Blo 1116628 1676303 := bstep (se 1 (by rfl) ⟨1257227, by rfl⟩ : syracuseStep 1676303 = 2514455) B2514455
theorem B1119247 : Blo 1116628 1119247 := bstep (se 1 (by rfl) ⟨839435, by rfl⟩ : syracuseStep 1119247 = 1678871) B1678871
theorem B10753069 : Blo 1116628 10753069 := bstep (se 3 (by rfl) ⟨2016200, by rfl⟩ : syracuseStep 10753069 = 4032401) B4032401
theorem B1676345 : Blo 1116628 1676345 := bstep (se 2 (by rfl) ⟨628629, by rfl⟩ : syracuseStep 1676345 = 1257259) B1257259
theorem B1119291 : Blo 1116628 1119291 := bstep (se 1 (by rfl) ⟨839468, by rfl⟩ : syracuseStep 1119291 = 1678937) B1678937
theorem B1676423 : Blo 1116628 1676423 := bstep (se 1 (by rfl) ⟨1257317, by rfl⟩ : syracuseStep 1676423 = 2514635) B2514635
theorem B1512583 : Blo 1116628 1512583 := bstep (se 1 (by rfl) ⟨1134437, by rfl⟩ : syracuseStep 1512583 = 2268875) B2268875
theorem B1119367 : Blo 1116628 1119367 := bstep (se 1 (by rfl) ⟨839525, by rfl⟩ : syracuseStep 1119367 = 1679051) B1679051
theorem B1119375 : Blo 1116628 1119375 := bstep (se 1 (by rfl) ⟨839531, by rfl⟩ : syracuseStep 1119375 = 1679063) B1679063
theorem B1676459 : Blo 1116628 1676459 := bstep (se 1 (by rfl) ⟨1257344, by rfl⟩ : syracuseStep 1676459 = 2514689) B2514689
theorem B1119419 : Blo 1116628 1119419 := bstep (se 1 (by rfl) ⟨839564, by rfl⟩ : syracuseStep 1119419 = 1679129) B1679129
theorem B1676489 : Blo 1116628 1676489 := bstep (se 2 (by rfl) ⟨628683, by rfl⟩ : syracuseStep 1676489 = 1257367) B1257367
theorem B2266313 : Blo 1116628 2266313 := bstep (se 2 (by rfl) ⟨849867, by rfl⟩ : syracuseStep 2266313 = 1699735) B1699735
theorem B8066249 : Blo 1116628 8066249 := bstep (se 2 (by rfl) ⟨3024843, by rfl⟩ : syracuseStep 8066249 = 6049687) B6049687
theorem B1119495 : Blo 1116628 1119495 := bstep (se 1 (by rfl) ⟨839621, by rfl⟩ : syracuseStep 1119495 = 1679243) B1679243
theorem B1119503 : Blo 1116628 1119503 := bstep (se 1 (by rfl) ⟨839627, by rfl⟩ : syracuseStep 1119503 = 1679255) B1679255
theorem B1676603 : Blo 1116628 1676603 := bstep (se 1 (by rfl) ⟨1257452, by rfl⟩ : syracuseStep 1676603 = 2514905) B2514905
theorem B1119547 : Blo 1116628 1119547 := bstep (se 1 (by rfl) ⟨839660, by rfl⟩ : syracuseStep 1119547 = 1679321) B1679321
theorem B1676663 : Blo 1116628 1676663 := bstep (se 1 (by rfl) ⟨1257497, by rfl⟩ : syracuseStep 1676663 = 2514995) B2514995
theorem B1119623 : Blo 1116628 1119623 := bstep (se 1 (by rfl) ⟨839717, by rfl⟩ : syracuseStep 1119623 = 1679435) B1679435
theorem B1676687 : Blo 1116628 1676687 := bstep (se 1 (by rfl) ⟨1257515, by rfl⟩ : syracuseStep 1676687 = 2515031) B2515031
theorem B1119631 : Blo 1116628 1119631 := bstep (se 1 (by rfl) ⟨839723, by rfl⟩ : syracuseStep 1119631 = 1679447) B1679447
theorem B3773843 : Blo 1116628 3773843 := bstep (se 1 (by rfl) ⟨2830382, by rfl⟩ : syracuseStep 3773843 = 5660765) B5660765
theorem B1676729 : Blo 1116628 1676729 := bstep (se 2 (by rfl) ⟨628773, by rfl⟩ : syracuseStep 1676729 = 1257547) B1257547
theorem B1119675 : Blo 1116628 1119675 := bstep (se 1 (by rfl) ⟨839756, by rfl⟩ : syracuseStep 1119675 = 1679513) B1679513
theorem B1676807 : Blo 1116628 1676807 := bstep (se 1 (by rfl) ⟨1257605, by rfl⟩ : syracuseStep 1676807 = 2515211) B2515211
theorem B1119751 : Blo 1116628 1119751 := bstep (se 1 (by rfl) ⟨839813, by rfl⟩ : syracuseStep 1119751 = 1679627) B1679627
theorem B1119759 : Blo 1116628 1119759 := bstep (se 1 (by rfl) ⟨839819, by rfl⟩ : syracuseStep 1119759 = 1679639) B1679639
theorem B1676843 : Blo 1116628 1676843 := bstep (se 1 (by rfl) ⟨1257632, by rfl⟩ : syracuseStep 1676843 = 2515265) B2515265
theorem B2299435 : Blo 1116628 2299435 := bstep (se 1 (by rfl) ⟨1724576, by rfl⟩ : syracuseStep 2299435 = 3449153) B3449153
theorem B1119803 : Blo 1116628 1119803 := bstep (se 1 (by rfl) ⟨839852, by rfl⟩ : syracuseStep 1119803 = 1679705) B1679705
theorem B1676873 : Blo 1116628 1676873 := bstep (se 2 (by rfl) ⟨628827, by rfl⟩ : syracuseStep 1676873 = 1257655) B1257655
theorem B1119879 : Blo 1116628 1119879 := bstep (se 1 (by rfl) ⟨839909, by rfl⟩ : syracuseStep 1119879 = 1679819) B1679819
theorem B1119887 : Blo 1116628 1119887 := bstep (se 1 (by rfl) ⟨839915, by rfl⟩ : syracuseStep 1119887 = 1679831) B1679831
theorem B1676987 : Blo 1116628 1676987 := bstep (se 1 (by rfl) ⟨1257740, by rfl⟩ : syracuseStep 1676987 = 2515481) B2515481
theorem B1119931 : Blo 1116628 1119931 := bstep (se 1 (by rfl) ⟨839948, by rfl⟩ : syracuseStep 1119931 = 1679897) B1679897
theorem B1414903 : Blo 1116628 1414903 := bstep (se 1 (by rfl) ⟨1061177, by rfl⟩ : syracuseStep 1414903 = 2122355) B2122355
theorem B1677047 : Blo 1116628 1677047 := bstep (se 1 (by rfl) ⟨1257785, by rfl⟩ : syracuseStep 1677047 = 2515571) B2515571
theorem B1120007 : Blo 1116628 1120007 := bstep (se 1 (by rfl) ⟨840005, by rfl⟩ : syracuseStep 1120007 = 1680011) B1680011
theorem B1677071 : Blo 1116628 1677071 := bstep (se 1 (by rfl) ⟨1257803, by rfl⟩ : syracuseStep 1677071 = 2515607) B2515607
theorem B1120015 : Blo 1116628 1120015 := bstep (se 1 (by rfl) ⟨840011, by rfl⟩ : syracuseStep 1120015 = 1680023) B1680023
theorem B8492849 : Blo 1116628 8492849 := bstep (se 2 (by rfl) ⟨3184818, by rfl⟩ : syracuseStep 8492849 = 6369637) B6369637
theorem B1677113 : Blo 1116628 1677113 := bstep (se 2 (by rfl) ⟨628917, by rfl⟩ : syracuseStep 1677113 = 1257835) B1257835
theorem B1120059 : Blo 1116628 1120059 := bstep (se 1 (by rfl) ⟨840044, by rfl⟩ : syracuseStep 1120059 = 1680089) B1680089
theorem B4528007 : Blo 1116628 4528007 := bstep (se 1 (by rfl) ⟨3396005, by rfl⟩ : syracuseStep 4528007 = 6792011) B6792011
theorem B1677191 : Blo 1116628 1677191 := bstep (se 1 (by rfl) ⟨1257893, by rfl⟩ : syracuseStep 1677191 = 2515787) B2515787
theorem B1120135 : Blo 1116628 1120135 := bstep (se 1 (by rfl) ⟨840101, by rfl⟩ : syracuseStep 1120135 = 1680203) B1680203
theorem B1120143 : Blo 1116628 1120143 := bstep (se 1 (by rfl) ⟨840107, by rfl⟩ : syracuseStep 1120143 = 1680215) B1680215
theorem B1677227 : Blo 1116628 1677227 := bstep (se 1 (by rfl) ⟨1257920, by rfl⟩ : syracuseStep 1677227 = 2515841) B2515841
theorem B1120187 : Blo 1116628 1120187 := bstep (se 1 (by rfl) ⟨840140, by rfl⟩ : syracuseStep 1120187 = 1680281) B1680281
theorem B1677257 : Blo 1116628 1677257 := bstep (se 2 (by rfl) ⟨628971, by rfl⟩ : syracuseStep 1677257 = 1257943) B1257943
theorem B1120263 : Blo 1116628 1120263 := bstep (se 1 (by rfl) ⟨840197, by rfl⟩ : syracuseStep 1120263 = 1680395) B1680395
theorem B1120271 : Blo 1116628 1120271 := bstep (se 1 (by rfl) ⟨840203, by rfl⟩ : syracuseStep 1120271 = 1680407) B1680407
theorem B28710935 : Blo 1116628 28710935 := bstep (se 1 (by rfl) ⟨21533201, by rfl⟩ : syracuseStep 28710935 = 43066403) B43066403
theorem B1415227 : Blo 1116628 1415227 := bstep (se 1 (by rfl) ⟨1061420, by rfl⟩ : syracuseStep 1415227 = 2122841) B2122841
theorem B1677371 : Blo 1116628 1677371 := bstep (se 1 (by rfl) ⟨1258028, by rfl⟩ : syracuseStep 1677371 = 2516057) B2516057
theorem B1120315 : Blo 1116628 1120315 := bstep (se 1 (by rfl) ⟨840236, by rfl⟩ : syracuseStep 1120315 = 1680473) B1680473
theorem B5740631 : Blo 1116628 5740631 := bstep (se 1 (by rfl) ⟨4305473, by rfl⟩ : syracuseStep 5740631 = 8610947) B8610947
theorem B19110005 : Blo 1116628 19110005 := bstep (se 5 (by rfl) ⟨895781, by rfl⟩ : syracuseStep 19110005 = 1791563) B1791563
theorem B1677431 : Blo 1116628 1677431 := bstep (se 1 (by rfl) ⟨1258073, by rfl⟩ : syracuseStep 1677431 = 2516147) B2516147
theorem B1120391 : Blo 1116628 1120391 := bstep (se 1 (by rfl) ⟨840293, by rfl⟩ : syracuseStep 1120391 = 1680587) B1680587
theorem B1677455 : Blo 1116628 1677455 := bstep (se 1 (by rfl) ⟨1258091, by rfl⟩ : syracuseStep 1677455 = 2516183) B2516183
theorem B1120399 : Blo 1116628 1120399 := bstep (se 1 (by rfl) ⟨840299, by rfl⟩ : syracuseStep 1120399 = 1680599) B1680599
theorem B1677497 : Blo 1116628 1677497 := bstep (se 2 (by rfl) ⟨629061, by rfl⟩ : syracuseStep 1677497 = 1258123) B1258123
theorem B1120443 : Blo 1116628 1120443 := bstep (se 1 (by rfl) ⟨840332, by rfl⟩ : syracuseStep 1120443 = 1680665) B1680665
theorem B1677575 : Blo 1116628 1677575 := bstep (se 1 (by rfl) ⟨1258181, by rfl⟩ : syracuseStep 1677575 = 2516363) B2516363
theorem B1120519 : Blo 1116628 1120519 := bstep (se 1 (by rfl) ⟨840389, by rfl⟩ : syracuseStep 1120519 = 1680779) B1680779
theorem B1120527 : Blo 1116628 1120527 := bstep (se 1 (by rfl) ⟨840395, by rfl⟩ : syracuseStep 1120527 = 1680791) B1680791
theorem B1677611 : Blo 1116628 1677611 := bstep (se 1 (by rfl) ⟨1258208, by rfl⟩ : syracuseStep 1677611 = 2516417) B2516417
theorem B1120571 : Blo 1116628 1120571 := bstep (se 1 (by rfl) ⟨840428, by rfl⟩ : syracuseStep 1120571 = 1680857) B1680857
theorem B1677641 : Blo 1116628 1677641 := bstep (se 2 (by rfl) ⟨629115, by rfl⟩ : syracuseStep 1677641 = 1258231) B1258231
theorem B1677755 : Blo 1116628 1677755 := bstep (se 1 (by rfl) ⟨1258316, by rfl⟩ : syracuseStep 1677755 = 2516633) B2516633
theorem B1677815 : Blo 1116628 1677815 := bstep (se 1 (by rfl) ⟨1258361, by rfl⟩ : syracuseStep 1677815 = 2516723) B2516723
theorem B1677839 : Blo 1116628 1677839 := bstep (se 1 (by rfl) ⟨1258379, by rfl⟩ : syracuseStep 1677839 = 2516759) B2516759
theorem B3578411 : Blo 1116628 3578411 := bstep (se 1 (by rfl) ⟨2683808, by rfl⟩ : syracuseStep 3578411 = 5367617) B5367617
theorem B1677881 : Blo 1116628 1677881 := bstep (se 2 (by rfl) ⟨629205, by rfl⟩ : syracuseStep 1677881 = 1258411) B1258411
theorem B1677959 : Blo 1116628 1677959 := bstep (se 1 (by rfl) ⟨1258469, by rfl⟩ : syracuseStep 1677959 = 2516939) B2516939
theorem B1677995 : Blo 1116628 1677995 := bstep (se 1 (by rfl) ⟨1258496, by rfl⟩ : syracuseStep 1677995 = 2516993) B2516993
theorem B13605569 : Blo 1116628 13605569 := bstep (se 2 (by rfl) ⟨5102088, by rfl⟩ : syracuseStep 13605569 = 10204177) B10204177
theorem B1678025 : Blo 1116628 1678025 := bstep (se 2 (by rfl) ⟨629259, by rfl⟩ : syracuseStep 1678025 = 1258519) B1258519
theorem B3775247 : Blo 1116628 3775247 := bstep (se 1 (by rfl) ⟨2831435, by rfl⟩ : syracuseStep 3775247 = 5662871) B5662871
theorem B1678139 : Blo 1116628 1678139 := bstep (se 1 (by rfl) ⟨1258604, by rfl⟩ : syracuseStep 1678139 = 2517209) B2517209
theorem B1678199 : Blo 1116628 1678199 := bstep (se 1 (by rfl) ⟨1258649, by rfl⟩ : syracuseStep 1678199 = 2517299) B2517299
theorem B1678223 : Blo 1116628 1678223 := bstep (se 1 (by rfl) ⟨1258667, by rfl⟩ : syracuseStep 1678223 = 2517335) B2517335
theorem B12721049 : Blo 1116628 12721049 := bstep (se 2 (by rfl) ⟨4770393, by rfl⟩ : syracuseStep 12721049 = 9540787) B9540787
theorem B1678265 : Blo 1116628 1678265 := bstep (se 2 (by rfl) ⟨629349, by rfl⟩ : syracuseStep 1678265 = 1258699) B1258699
theorem B1678343 : Blo 1116628 1678343 := bstep (se 1 (by rfl) ⟨1258757, by rfl⟩ : syracuseStep 1678343 = 2517515) B2517515
theorem B1416199 : Blo 1116628 1416199 := bstep (se 1 (by rfl) ⟨1062149, by rfl⟩ : syracuseStep 1416199 = 2124299) B2124299
theorem B3775517 : Blo 1116628 3775517 := bstep (se 3 (by rfl) ⟨707909, by rfl⟩ : syracuseStep 3775517 = 1415819) B1415819
theorem B1678379 : Blo 1116628 1678379 := bstep (se 1 (by rfl) ⟨1258784, by rfl⟩ : syracuseStep 1678379 = 2517569) B2517569
theorem B1678409 : Blo 1116628 1678409 := bstep (se 2 (by rfl) ⟨629403, by rfl⟩ : syracuseStep 1678409 = 1258807) B1258807
theorem B1678523 : Blo 1116628 1678523 := bstep (se 1 (by rfl) ⟨1258892, by rfl⟩ : syracuseStep 1678523 = 2517785) B2517785
theorem B1678583 : Blo 1116628 1678583 := bstep (se 1 (by rfl) ⟨1258937, by rfl⟩ : syracuseStep 1678583 = 2517875) B2517875
theorem B1678607 : Blo 1116628 1678607 := bstep (se 1 (by rfl) ⟨1258955, by rfl⟩ : syracuseStep 1678607 = 2517911) B2517911
theorem B1678649 : Blo 1116628 1678649 := bstep (se 2 (by rfl) ⟨629493, by rfl⟩ : syracuseStep 1678649 = 1258987) B1258987
theorem B1678727 : Blo 1116628 1678727 := bstep (se 1 (by rfl) ⟨1259045, by rfl⟩ : syracuseStep 1678727 = 2518091) B2518091
theorem B1678763 : Blo 1116628 1678763 := bstep (se 1 (by rfl) ⟨1259072, by rfl⟩ : syracuseStep 1678763 = 2518145) B2518145
theorem B1416619 : Blo 1116628 1416619 := bstep (se 1 (by rfl) ⟨1062464, by rfl⟩ : syracuseStep 1416619 = 2124929) B2124929
theorem B1678793 : Blo 1116628 1678793 := bstep (se 2 (by rfl) ⟨629547, by rfl⟩ : syracuseStep 1678793 = 1259095) B1259095
theorem B3186209 : Blo 1116628 3186209 := bstep (se 2 (by rfl) ⟨1194828, by rfl⟩ : syracuseStep 3186209 = 2389657) B2389657
theorem B1678907 : Blo 1116628 1678907 := bstep (se 1 (by rfl) ⟨1259180, by rfl⟩ : syracuseStep 1678907 = 2518361) B2518361
theorem B1678967 : Blo 1116628 1678967 := bstep (se 1 (by rfl) ⟨1259225, by rfl⟩ : syracuseStep 1678967 = 2518451) B2518451
theorem B1678991 : Blo 1116628 1678991 := bstep (se 1 (by rfl) ⟨1259243, by rfl⟩ : syracuseStep 1678991 = 2518487) B2518487
theorem B1416847 : Blo 1116628 1416847 := bstep (se 1 (by rfl) ⟨1062635, by rfl⟩ : syracuseStep 1416847 = 2125271) B2125271
theorem B3186323 : Blo 1116628 3186323 := bstep (se 1 (by rfl) ⟨2389742, by rfl⟩ : syracuseStep 3186323 = 4779485) B4779485
theorem B1679033 : Blo 1116628 1679033 := bstep (se 2 (by rfl) ⟨629637, by rfl⟩ : syracuseStep 1679033 = 1259275) B1259275
theorem B1679111 : Blo 1116628 1679111 := bstep (se 1 (by rfl) ⟨1259333, by rfl⟩ : syracuseStep 1679111 = 2518667) B2518667
theorem B1679147 : Blo 1116628 1679147 := bstep (se 1 (by rfl) ⟨1259360, by rfl⟩ : syracuseStep 1679147 = 2518721) B2518721
theorem B2301755 : Blo 1116628 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B1679177 : Blo 1116628 1679177 := bstep (se 2 (by rfl) ⟨629691, by rfl⟩ : syracuseStep 1679177 = 1259383) B1259383
theorem B6365081 : Blo 1116628 6365081 := bstep (se 2 (by rfl) ⟨2386905, by rfl⟩ : syracuseStep 6365081 = 4773811) B4773811
theorem B1679291 : Blo 1116628 1679291 := bstep (se 1 (by rfl) ⟨1259468, by rfl⟩ : syracuseStep 1679291 = 2518937) B2518937
theorem B1679351 : Blo 1116628 1679351 := bstep (se 1 (by rfl) ⟨1259513, by rfl⟩ : syracuseStep 1679351 = 2519027) B2519027
theorem B1679375 : Blo 1116628 1679375 := bstep (se 1 (by rfl) ⟨1259531, by rfl⟩ : syracuseStep 1679375 = 2519063) B2519063
theorem B1679417 : Blo 1116628 1679417 := bstep (se 2 (by rfl) ⟨629781, by rfl⟩ : syracuseStep 1679417 = 1259563) B1259563
theorem B1679495 : Blo 1116628 1679495 := bstep (se 1 (by rfl) ⟨1259621, by rfl⟩ : syracuseStep 1679495 = 2519243) B2519243
theorem B1679531 : Blo 1116628 1679531 := bstep (se 1 (by rfl) ⟨1259648, by rfl⟩ : syracuseStep 1679531 = 2519297) B2519297
theorem B1679561 : Blo 1116628 1679561 := bstep (se 2 (by rfl) ⟨629835, by rfl⟩ : syracuseStep 1679561 = 1259671) B1259671
theorem B1679675 : Blo 1116628 1679675 := bstep (se 1 (by rfl) ⟨1259756, by rfl⟩ : syracuseStep 1679675 = 2519513) B2519513
theorem B24191297 : Blo 1116628 24191297 := bstep (se 2 (by rfl) ⟨9071736, by rfl⟩ : syracuseStep 24191297 = 18143473) B18143473
theorem B1679735 : Blo 1116628 1679735 := bstep (se 1 (by rfl) ⟨1259801, by rfl⟩ : syracuseStep 1679735 = 2519603) B2519603
theorem B1417591 : Blo 1116628 1417591 := bstep (se 1 (by rfl) ⟨1063193, by rfl⟩ : syracuseStep 1417591 = 2126387) B2126387
theorem B1679759 : Blo 1116628 1679759 := bstep (se 1 (by rfl) ⟨1259819, by rfl⟩ : syracuseStep 1679759 = 2519639) B2519639
theorem B3776921 : Blo 1116628 3776921 := bstep (se 2 (by rfl) ⟨1416345, by rfl⟩ : syracuseStep 3776921 = 2832691) B2832691
theorem B3187097 : Blo 1116628 3187097 := bstep (se 2 (by rfl) ⟨1195161, by rfl⟩ : syracuseStep 3187097 = 2390323) B2390323
theorem B1679801 : Blo 1116628 1679801 := bstep (se 2 (by rfl) ⟨629925, by rfl⟩ : syracuseStep 1679801 = 1259851) B1259851
theorem B2826697 : Blo 1116628 2826697 := bstep (se 2 (by rfl) ⟨1060011, by rfl⟩ : syracuseStep 2826697 = 2120023) B2120023
theorem B16097777 : Blo 1116628 16097777 := bstep (se 2 (by rfl) ⟨6036666, by rfl⟩ : syracuseStep 16097777 = 12073333) B12073333
theorem B1679879 : Blo 1116628 1679879 := bstep (se 1 (by rfl) ⟨1259909, by rfl⟩ : syracuseStep 1679879 = 2519819) B2519819
theorem B1679915 : Blo 1116628 1679915 := bstep (se 1 (by rfl) ⟨1259936, by rfl⟩ : syracuseStep 1679915 = 2519873) B2519873
theorem B1679945 : Blo 1116628 1679945 := bstep (se 2 (by rfl) ⟨629979, by rfl⟩ : syracuseStep 1679945 = 1259959) B1259959
theorem B2826839 : Blo 1116628 2826839 := bstep (se 1 (by rfl) ⟨2120129, by rfl⟩ : syracuseStep 2826839 = 4240259) B4240259
theorem B1680059 : Blo 1116628 1680059 := bstep (se 1 (by rfl) ⟨1260044, by rfl⟩ : syracuseStep 1680059 = 2520089) B2520089
theorem B1417915 : Blo 1116628 1417915 := bstep (se 1 (by rfl) ⟨1063436, by rfl⟩ : syracuseStep 1417915 = 2126873) B2126873
theorem B1680119 : Blo 1116628 1680119 := bstep (se 1 (by rfl) ⟨1260089, by rfl⟩ : syracuseStep 1680119 = 2520179) B2520179
theorem B1680143 : Blo 1116628 1680143 := bstep (se 1 (by rfl) ⟨1260107, by rfl⟩ : syracuseStep 1680143 = 2520215) B2520215
theorem B8069939 : Blo 1116628 8069939 := bstep (se 1 (by rfl) ⟨6052454, by rfl⟩ : syracuseStep 8069939 = 12104909) B12104909
theorem B1680185 : Blo 1116628 1680185 := bstep (se 2 (by rfl) ⟨630069, by rfl⟩ : syracuseStep 1680185 = 1260139) B1260139
theorem B1680263 : Blo 1116628 1680263 := bstep (se 1 (by rfl) ⟨1260197, by rfl⟩ : syracuseStep 1680263 = 2520395) B2520395
theorem B1680299 : Blo 1116628 1680299 := bstep (se 1 (by rfl) ⟨1260224, by rfl⟩ : syracuseStep 1680299 = 2520449) B2520449
theorem B1680329 : Blo 1116628 1680329 := bstep (se 2 (by rfl) ⟨630123, by rfl⟩ : syracuseStep 1680329 = 1260247) B1260247
theorem B8070167 : Blo 1116628 8070167 := bstep (se 1 (by rfl) ⟨6052625, by rfl⟩ : syracuseStep 8070167 = 12105251) B12105251
theorem B1680443 : Blo 1116628 1680443 := bstep (se 1 (by rfl) ⟨1260332, by rfl⟩ : syracuseStep 1680443 = 2520665) B2520665
theorem B3777623 : Blo 1116628 3777623 := bstep (se 1 (by rfl) ⟨2833217, by rfl⟩ : syracuseStep 3777623 = 5666435) B5666435
theorem B1680503 : Blo 1116628 1680503 := bstep (se 1 (by rfl) ⟨1260377, by rfl⟩ : syracuseStep 1680503 = 2520755) B2520755
theorem B1680527 : Blo 1116628 1680527 := bstep (se 1 (by rfl) ⟨1260395, by rfl⟩ : syracuseStep 1680527 = 2520791) B2520791
theorem B1680569 : Blo 1116628 1680569 := bstep (se 2 (by rfl) ⟨630213, by rfl⟩ : syracuseStep 1680569 = 1260427) B1260427
theorem B1680647 : Blo 1116628 1680647 := bstep (se 1 (by rfl) ⟨1260485, by rfl⟩ : syracuseStep 1680647 = 2520971) B2520971
theorem B1680683 : Blo 1116628 1680683 := bstep (se 1 (by rfl) ⟨1260512, by rfl⟩ : syracuseStep 1680683 = 2521025) B2521025
theorem B1680713 : Blo 1116628 1680713 := bstep (se 2 (by rfl) ⟨630267, by rfl⟩ : syracuseStep 1680713 = 1260535) B1260535
theorem B1680827 : Blo 1116628 1680827 := bstep (se 1 (by rfl) ⟨1260620, by rfl⟩ : syracuseStep 1680827 = 2521241) B2521241
theorem B1680887 : Blo 1116628 1680887 := bstep (se 1 (by rfl) ⟨1260665, by rfl⟩ : syracuseStep 1680887 = 2521331) B2521331
theorem B1680911 : Blo 1116628 1680911 := bstep (se 1 (by rfl) ⟨1260683, by rfl⟩ : syracuseStep 1680911 = 2521367) B2521367
theorem B3778109 : Blo 1116628 3778109 := bstep (se 3 (by rfl) ⟨708395, by rfl⟩ : syracuseStep 3778109 = 1416791) B1416791
theorem B4531913 : Blo 1116628 4531913 := bstep (se 2 (by rfl) ⟨1699467, by rfl⟩ : syracuseStep 4531913 = 3398935) B3398935
theorem B3188737 : Blo 1116628 3188737 := bstep (se 2 (by rfl) ⟨1195776, by rfl⟩ : syracuseStep 3188737 = 2391553) B2391553
theorem B3024929 : Blo 1116628 3024929 := bstep (se 2 (by rfl) ⟨1134348, by rfl⟩ : syracuseStep 3024929 = 2268697) B2268697
theorem B9546119 : Blo 1116628 9546119 := bstep (se 1 (by rfl) ⟨7159589, by rfl⟩ : syracuseStep 9546119 = 14319179) B14319179
theorem B8071609 : Blo 1116628 8071609 := bstep (se 2 (by rfl) ⟨3026853, by rfl⟩ : syracuseStep 8071609 = 6053707) B6053707
theorem B3189307 : Blo 1116628 3189307 := bstep (se 1 (by rfl) ⟨2391980, by rfl⟩ : syracuseStep 3189307 = 4783961) B4783961
theorem B20425283 : Blo 1116628 20425283 := bstep (se 1 (by rfl) ⟨15318962, by rfl⟩ : syracuseStep 20425283 = 30637925) B30637925
theorem B2828915 : Blo 1116628 2828915 := bstep (se 1 (by rfl) ⟨2121686, by rfl⟩ : syracuseStep 2828915 = 4243373) B4243373
theorem B9546497 : Blo 1116628 9546497 := bstep (se 2 (by rfl) ⟨3579936, by rfl⟩ : syracuseStep 9546497 = 7159873) B7159873
theorem B1256251 : Blo 1116628 1256251 := bstep (se 1 (by rfl) ⟨942188, by rfl⟩ : syracuseStep 1256251 = 1884377) B1884377
theorem B1911737 : Blo 1116628 1911737 := bstep (se 2 (by rfl) ⟨716901, by rfl⟩ : syracuseStep 1911737 = 1433803) B1433803
theorem B3779513 : Blo 1116628 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B2829431 : Blo 1116628 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B1256719 : Blo 1116628 1256719 := bstep (se 1 (by rfl) ⟨942539, by rfl⟩ : syracuseStep 1256719 = 1885079) B1885079
theorem B48344525 : Blo 1116628 48344525 := bstep (se 3 (by rfl) ⟨9064598, by rfl⟩ : syracuseStep 48344525 = 18129197) B18129197
theorem B3780107 : Blo 1116628 3780107 := bstep (se 1 (by rfl) ⟨2835080, by rfl⟩ : syracuseStep 3780107 = 5670161) B5670161
theorem B3780215 : Blo 1116628 3780215 := bstep (se 1 (by rfl) ⟨2835161, by rfl⟩ : syracuseStep 3780215 = 5670323) B5670323
theorem B1257223 : Blo 1116628 1257223 := bstep (se 1 (by rfl) ⟨942917, by rfl⟩ : syracuseStep 1257223 = 1885835) B1885835
theorem B1257403 : Blo 1116628 1257403 := bstep (se 1 (by rfl) ⟨943052, by rfl⟩ : syracuseStep 1257403 = 1886105) B1886105
theorem B7155773 : Blo 1116628 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B2830423 : Blo 1116628 2830423 := bstep (se 1 (by rfl) ⟨2122817, by rfl⟩ : syracuseStep 2830423 = 4245635) B4245635
theorem B3780809 : Blo 1116628 3780809 := bstep (se 2 (by rfl) ⟨1417803, by rfl⟩ : syracuseStep 3780809 = 2835607) B2835607
theorem B7156001 : Blo 1116628 7156001 := bstep (se 2 (by rfl) ⟨2683500, by rfl⟩ : syracuseStep 7156001 = 5367001) B5367001
theorem B3027287 : Blo 1116628 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B2830727 : Blo 1116628 2830727 := bstep (se 1 (by rfl) ⟨2123045, by rfl⟩ : syracuseStep 2830727 = 4246091) B4246091
theorem B1257871 : Blo 1116628 1257871 := bstep (se 1 (by rfl) ⟨943403, by rfl⟩ : syracuseStep 1257871 = 1886807) B1886807
theorem B28684691 : Blo 1116628 28684691 := bstep (se 1 (by rfl) ⟨21513518, by rfl⟩ : syracuseStep 28684691 = 43027037) B43027037
theorem B19083761 : Blo 1116628 19083761 := bstep (se 2 (by rfl) ⟨7156410, by rfl⟩ : syracuseStep 19083761 = 14312821) B14312821
theorem B2830859 : Blo 1116628 2830859 := bstep (se 1 (by rfl) ⟨2123144, by rfl⟩ : syracuseStep 2830859 = 4246289) B4246289
theorem B6369911 : Blo 1116628 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B1815175 : Blo 1116628 1815175 := bstep (se 1 (by rfl) ⟨1361381, by rfl⟩ : syracuseStep 1815175 = 2722763) B2722763
theorem B6370163 : Blo 1116628 6370163 := bstep (se 1 (by rfl) ⟨4777622, by rfl⟩ : syracuseStep 6370163 = 9555245) B9555245
theorem B1258375 : Blo 1116628 1258375 := bstep (se 1 (by rfl) ⟨943781, by rfl⟩ : syracuseStep 1258375 = 1887563) B1887563
theorem B3781511 : Blo 1116628 3781511 := bstep (se 1 (by rfl) ⟨2836133, by rfl⟩ : syracuseStep 3781511 = 5672267) B5672267
theorem B2831375 : Blo 1116628 2831375 := bstep (se 1 (by rfl) ⟨2123531, by rfl⟩ : syracuseStep 2831375 = 4247063) B4247063
theorem B1258555 : Blo 1116628 1258555 := bstep (se 1 (by rfl) ⟨943916, by rfl⟩ : syracuseStep 1258555 = 1887833) B1887833
theorem B4240471 : Blo 1116628 4240471 := bstep (se 1 (by rfl) ⟨3180353, by rfl⟩ : syracuseStep 4240471 = 6360707) B6360707
theorem B1815671 : Blo 1116628 1815671 := bstep (se 1 (by rfl) ⟨1361753, by rfl⟩ : syracuseStep 1815671 = 2723507) B2723507
theorem B2831507 : Blo 1116628 2831507 := bstep (se 1 (by rfl) ⟨2123630, by rfl⟩ : syracuseStep 2831507 = 4247261) B4247261
theorem B3781889 : Blo 1116628 3781889 := bstep (se 2 (by rfl) ⟨1418208, by rfl⟩ : syracuseStep 3781889 = 2836417) B2836417
theorem B1193231 : Blo 1116628 1193231 := bstep (se 1 (by rfl) ⟨894923, by rfl⟩ : syracuseStep 1193231 = 1789847) B1789847
theorem B1815851 : Blo 1116628 1815851 := bstep (se 1 (by rfl) ⟨1361888, by rfl⟩ : syracuseStep 1815851 = 2723777) B2723777
theorem B4240775 : Blo 1116628 4240775 := bstep (se 1 (by rfl) ⟨3180581, by rfl⟩ : syracuseStep 4240775 = 6361163) B6361163
theorem B8500625 : Blo 1116628 8500625 := bstep (se 2 (by rfl) ⟨3187734, by rfl⟩ : syracuseStep 8500625 = 6375469) B6375469
theorem B1259023 : Blo 1116628 1259023 := bstep (se 1 (by rfl) ⟨944267, by rfl⟩ : syracuseStep 1259023 = 1888535) B1888535
theorem B4240957 : Blo 1116628 4240957 := bstep (se 3 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 4240957 = 1590359) B1590359
theorem B1193735 : Blo 1116628 1193735 := bstep (se 1 (by rfl) ⟨895301, by rfl⟩ : syracuseStep 1193735 = 1790603) B1790603
theorem B1193863 : Blo 1116628 1193863 := bstep (se 1 (by rfl) ⟨895397, by rfl⟩ : syracuseStep 1193863 = 1790795) B1790795
theorem B1259527 : Blo 1116628 1259527 := bstep (se 1 (by rfl) ⟨944645, by rfl⟩ : syracuseStep 1259527 = 1889291) B1889291
theorem B1259707 : Blo 1116628 1259707 := bstep (se 1 (by rfl) ⟨944780, by rfl⟩ : syracuseStep 1259707 = 1889561) B1889561
theorem B2832641 : Blo 1116628 2832641 := bstep (se 2 (by rfl) ⟨1062240, by rfl⟩ : syracuseStep 2832641 = 2124481) B2124481
theorem B6371621 : Blo 1116628 6371621 := bstep (se 4 (by rfl) ⟨597339, by rfl⟩ : syracuseStep 6371621 = 1194679) B1194679
theorem B1194427 : Blo 1116628 1194427 := bstep (se 1 (by rfl) ⟨895820, by rfl⟩ : syracuseStep 1194427 = 1791641) B1791641
theorem B2833015 : Blo 1116628 2833015 := bstep (se 1 (by rfl) ⟨2124761, by rfl⟩ : syracuseStep 2833015 = 4249523) B4249523
theorem B1260175 : Blo 1116628 1260175 := bstep (se 1 (by rfl) ⟨945131, by rfl⟩ : syracuseStep 1260175 = 1890263) B1890263
theorem B1194683 : Blo 1116628 1194683 := bstep (se 1 (by rfl) ⟨896012, by rfl⟩ : syracuseStep 1194683 = 1792025) B1792025
theorem B3586817 : Blo 1116628 3586817 := bstep (se 2 (by rfl) ⟨1345056, by rfl⟩ : syracuseStep 3586817 = 2690113) B2690113
theorem B2866067 : Blo 1116628 2866067 := bstep (se 1 (by rfl) ⟨2149550, by rfl⟩ : syracuseStep 2866067 = 4299101) B4299101
theorem B4307921 : Blo 1116628 4307921 := bstep (se 2 (by rfl) ⟨1615470, by rfl⟩ : syracuseStep 4307921 = 3230941) B3230941
theorem B9550871 : Blo 1116628 9550871 := bstep (se 1 (by rfl) ⟨7163153, by rfl⟩ : syracuseStep 9550871 = 14326307) B14326307
theorem B2833451 : Blo 1116628 2833451 := bstep (se 1 (by rfl) ⟨2125088, by rfl⟩ : syracuseStep 2833451 = 4250177) B4250177
theorem B7158871 : Blo 1116628 7158871 := bstep (se 1 (by rfl) ⟨5369153, by rfl⟩ : syracuseStep 7158871 = 10738307) B10738307
theorem B1260679 : Blo 1116628 1260679 := bstep (se 1 (by rfl) ⟨945509, by rfl⟩ : syracuseStep 1260679 = 1891019) B1891019
theorem B45890711 : Blo 1116628 45890711 := bstep (se 1 (by rfl) ⟨34418033, by rfl⟩ : syracuseStep 45890711 = 68836067) B68836067
theorem B6372553 : Blo 1116628 6372553 := bstep (se 2 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 6372553 = 4779415) B4779415
theorem B4242689 : Blo 1116628 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B7257377 : Blo 1116628 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B4603195 : Blo 1116628 4603195 := bstep (se 1 (by rfl) ⟨3452396, by rfl⟩ : syracuseStep 4603195 = 6904793) B6904793
theorem B8503055 : Blo 1116628 8503055 := bstep (se 1 (by rfl) ⟨6377291, by rfl⟩ : syracuseStep 8503055 = 12754583) B12754583
theorem B2834291 : Blo 1116628 2834291 := bstep (se 1 (by rfl) ⟨2125718, by rfl⟩ : syracuseStep 2834291 = 4251437) B4251437
theorem B2834311 : Blo 1116628 2834311 := bstep (se 1 (by rfl) ⟨2125733, by rfl⟩ : syracuseStep 2834311 = 4251467) B4251467
theorem B8077259 : Blo 1116628 8077259 := bstep (se 1 (by rfl) ⟨6057944, by rfl⟩ : syracuseStep 8077259 = 12115889) B12115889
theorem B24231959 : Blo 1116628 24231959 := bstep (se 1 (by rfl) ⟨18173969, by rfl⟩ : syracuseStep 24231959 = 36347939) B36347939
theorem B2834585 : Blo 1116628 2834585 := bstep (se 2 (by rfl) ⟨1062969, by rfl⟩ : syracuseStep 2834585 = 2125939) B2125939
theorem B1884431 : Blo 1116628 1884431 := bstep (se 1 (by rfl) ⟨1413323, by rfl⟩ : syracuseStep 1884431 = 2826647) B2826647
theorem B2834747 : Blo 1116628 2834747 := bstep (se 1 (by rfl) ⟨2126060, by rfl⟩ : syracuseStep 2834747 = 4252121) B4252121
theorem B4243859 : Blo 1116628 4243859 := bstep (se 1 (by rfl) ⟨3182894, by rfl⟩ : syracuseStep 4243859 = 6365789) B6365789
theorem B2834959 : Blo 1116628 2834959 := bstep (se 1 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 2834959 = 4252439) B4252439
theorem B2835233 : Blo 1116628 2835233 := bstep (se 2 (by rfl) ⟨1063212, by rfl⟩ : syracuseStep 2835233 = 2126425) B2126425
theorem B1884971 : Blo 1116628 1884971 := bstep (se 1 (by rfl) ⟨1413728, by rfl⟩ : syracuseStep 1884971 = 2827457) B2827457
theorem B4244359 : Blo 1116628 4244359 := bstep (se 1 (by rfl) ⟨3183269, by rfl⟩ : syracuseStep 4244359 = 6366539) B6366539
theorem B4310027 : Blo 1116628 4310027 := bstep (se 1 (by rfl) ⟨3232520, by rfl⟩ : syracuseStep 4310027 = 6465041) B6465041
theorem B1721417 : Blo 1116628 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B1885369 : Blo 1116628 1885369 := bstep (se 2 (by rfl) ⟨707013, by rfl⟩ : syracuseStep 1885369 = 1414027) B1414027
theorem B1590473 : Blo 1116628 1590473 := bstep (se 2 (by rfl) ⟨596427, by rfl⟩ : syracuseStep 1590473 = 1192855) B1192855
theorem B3065149 : Blo 1116628 3065149 := bstep (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) B1149431
theorem B2836235 : Blo 1116628 2836235 := bstep (se 1 (by rfl) ⟨2127176, by rfl⟩ : syracuseStep 2836235 = 4254353) B4254353
theorem B1886071 : Blo 1116628 1886071 := bstep (se 1 (by rfl) ⟨1414553, by rfl⟩ : syracuseStep 1886071 = 2829107) B2829107
theorem B1591339 : Blo 1116628 1591339 := bstep (se 1 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 1591339 = 2387009) B2387009
theorem B1886267 : Blo 1116628 1886267 := bstep (se 1 (by rfl) ⟨1414700, by rfl⟩ : syracuseStep 1886267 = 2829401) B2829401
theorem B16107923 : Blo 1116628 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B1886665 : Blo 1116628 1886665 := bstep (se 2 (by rfl) ⟨707499, by rfl⟩ : syracuseStep 1886665 = 1414999) B1414999
theorem B55200473 : Blo 1116628 55200473 := bstep (se 2 (by rfl) ⟨20700177, by rfl⟩ : syracuseStep 55200473 = 41400355) B41400355
theorem B28658447 : Blo 1116628 28658447 := bstep (se 1 (by rfl) ⟨21493835, by rfl⟩ : syracuseStep 28658447 = 42987671) B42987671
theorem B5655581 : Blo 1116628 5655581 := bstep (se 3 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 5655581 = 2120843) B2120843
theorem B1592455 : Blo 1116628 1592455 := bstep (se 1 (by rfl) ⟨1194341, by rfl⟩ : syracuseStep 1592455 = 2388683) B2388683
theorem B1887367 : Blo 1116628 1887367 := bstep (se 1 (by rfl) ⟨1415525, by rfl⟩ : syracuseStep 1887367 = 2831051) B2831051
theorem B25873843 : Blo 1116628 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B12078521 : Blo 1116628 12078521 := bstep (se 2 (by rfl) ⟨4529445, by rfl⟩ : syracuseStep 12078521 = 9058891) B9058891
theorem B1363447 : Blo 1116628 1363447 := bstep (se 1 (by rfl) ⟨1022585, by rfl⟩ : syracuseStep 1363447 = 2045171) B2045171
theorem B5656067 : Blo 1116628 5656067 := bstep (se 1 (by rfl) ⟨4242050, by rfl⟩ : syracuseStep 5656067 = 8484101) B8484101
theorem B1888015 : Blo 1116628 1888015 := bstep (se 1 (by rfl) ⟨1416011, by rfl⟩ : syracuseStep 1888015 = 2832023) B2832023
theorem B1593275 : Blo 1116628 1593275 := bstep (se 1 (by rfl) ⟨1194956, by rfl⟩ : syracuseStep 1593275 = 2389913) B2389913
theorem B2150459 : Blo 1116628 2150459 := bstep (se 1 (by rfl) ⟨1612844, by rfl⟩ : syracuseStep 2150459 = 3225689) B3225689
theorem B1888555 : Blo 1116628 1888555 := bstep (se 1 (by rfl) ⟨1416416, by rfl⟩ : syracuseStep 1888555 = 2832833) B2832833
theorem B4772155 : Blo 1116628 4772155 := bstep (se 1 (by rfl) ⟨3579116, by rfl⟩ : syracuseStep 4772155 = 7158233) B7158233
theorem B1888697 : Blo 1116628 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B1593913 : Blo 1116628 1593913 := bstep (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) B1195435
theorem B1594027 : Blo 1116628 1594027 := bstep (se 1 (by rfl) ⟨1195520, by rfl⟩ : syracuseStep 1594027 = 2391041) B2391041
theorem B1594255 : Blo 1116628 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B6378385 : Blo 1116628 6378385 := bstep (se 2 (by rfl) ⟨2391894, by rfl⟩ : syracuseStep 6378385 = 4783789) B4783789
theorem B5657687 : Blo 1116628 5657687 := bstep (se 1 (by rfl) ⟨4243265, by rfl⟩ : syracuseStep 5657687 = 8486531) B8486531
theorem B1889399 : Blo 1116628 1889399 := bstep (se 1 (by rfl) ⟨1417049, by rfl⟩ : syracuseStep 1889399 = 2834099) B2834099
theorem B3822983 : Blo 1116628 3822983 := bstep (se 1 (by rfl) ⟨2867237, by rfl⟩ : syracuseStep 3822983 = 5734475) B5734475
theorem B7165331 : Blo 1116628 7165331 := bstep (se 1 (by rfl) ⟨5373998, by rfl⟩ : syracuseStep 7165331 = 10747997) B10747997
theorem B1889851 : Blo 1116628 1889851 := bstep (se 1 (by rfl) ⟨1417388, by rfl⟩ : syracuseStep 1889851 = 2834777) B2834777
theorem B4773437 : Blo 1116628 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B5658173 : Blo 1116628 5658173 := bstep (se 3 (by rfl) ⟨1060907, by rfl⟩ : syracuseStep 5658173 = 2121815) B2121815
theorem B1889993 : Blo 1116628 1889993 := bstep (se 2 (by rfl) ⟨708747, by rfl⟩ : syracuseStep 1889993 = 1417495) B1417495
theorem B1595143 : Blo 1116628 1595143 := bstep (se 1 (by rfl) ⟨1196357, by rfl⟩ : syracuseStep 1595143 = 2392715) B2392715
theorem B2512655 : Blo 1116628 2512655 := bstep (se 1 (by rfl) ⟨1884491, by rfl⟩ : syracuseStep 2512655 = 3768983) B3768983
theorem B2512673 : Blo 1116628 2512673 := bstep (se 2 (by rfl) ⟨942252, by rfl⟩ : syracuseStep 2512673 = 1884505) B1884505
theorem B15324977 : Blo 1116628 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B14931863 : Blo 1116628 14931863 := bstep (se 1 (by rfl) ⟨11198897, by rfl⟩ : syracuseStep 14931863 = 22397795) B22397795
theorem B2513015 : Blo 1116628 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B2513195 : Blo 1116628 2513195 := bstep (se 1 (by rfl) ⟨1884896, by rfl⟩ : syracuseStep 2513195 = 3769793) B3769793
theorem B1890695 : Blo 1116628 1890695 := bstep (se 1 (by rfl) ⟨1418021, by rfl⟩ : syracuseStep 1890695 = 2836043) B2836043
theorem B4250009 : Blo 1116628 4250009 := bstep (se 2 (by rfl) ⟨1593753, by rfl⟩ : syracuseStep 4250009 = 3187507) B3187507
theorem B9066937 : Blo 1116628 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B18143729 : Blo 1116628 18143729 := bstep (se 2 (by rfl) ⟨6803898, by rfl⟩ : syracuseStep 18143729 = 13607797) B13607797
theorem B9558557 : Blo 1116628 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B2120251 : Blo 1116628 2120251 := bstep (se 1 (by rfl) ⟨1590188, by rfl⟩ : syracuseStep 2120251 = 3180377) B3180377
theorem B2120327 : Blo 1116628 2120327 := bstep (se 1 (by rfl) ⟨1590245, by rfl⟩ : syracuseStep 2120327 = 3180491) B3180491
theorem B2513555 : Blo 1116628 2513555 := bstep (se 1 (by rfl) ⟨1885166, by rfl⟩ : syracuseStep 2513555 = 3770333) B3770333
theorem B2513609 : Blo 1116628 2513609 := bstep (se 2 (by rfl) ⟨942603, by rfl⟩ : syracuseStep 2513609 = 1885207) B1885207
theorem B12409649 : Blo 1116628 12409649 := bstep (se 2 (by rfl) ⟨4653618, by rfl⟩ : syracuseStep 12409649 = 9307237) B9307237
theorem B2120737 : Blo 1116628 2120737 := bstep (se 2 (by rfl) ⟨795276, by rfl⟩ : syracuseStep 2120737 = 1590553) B1590553
theorem B5102635 : Blo 1116628 5102635 := bstep (se 1 (by rfl) ⟨3826976, by rfl⟩ : syracuseStep 5102635 = 7653953) B7653953
theorem B9559241 : Blo 1116628 9559241 := bstep (se 2 (by rfl) ⟨3584715, by rfl⟩ : syracuseStep 9559241 = 7169431) B7169431
theorem B6380801 : Blo 1116628 6380801 := bstep (se 2 (by rfl) ⟨2392800, by rfl⟩ : syracuseStep 6380801 = 4785601) B4785601
theorem B5659955 : Blo 1116628 5659955 := bstep (se 1 (by rfl) ⟨4244966, by rfl⟩ : syracuseStep 5659955 = 8489933) B8489933
theorem B2121079 : Blo 1116628 2121079 := bstep (se 1 (by rfl) ⟨1590809, by rfl⟩ : syracuseStep 2121079 = 3181619) B3181619
theorem B2514311 : Blo 1116628 2514311 := bstep (se 1 (by rfl) ⟨1885733, by rfl⟩ : syracuseStep 2514311 = 3771467) B3771467
theorem B2514491 : Blo 1116628 2514491 := bstep (se 1 (by rfl) ⟨1885868, by rfl⟩ : syracuseStep 2514491 = 3771737) B3771737
theorem B9559619 : Blo 1116628 9559619 := bstep (se 1 (by rfl) ⟨7169714, by rfl⟩ : syracuseStep 9559619 = 14339429) B14339429
theorem B15720013 : Blo 1116628 15720013 := bstep (se 3 (by rfl) ⟨2947502, by rfl⟩ : syracuseStep 15720013 = 5895005) B5895005
theorem B5660279 : Blo 1116628 5660279 := bstep (se 1 (by rfl) ⟨4245209, by rfl⟩ : syracuseStep 5660279 = 8490419) B8490419
theorem B2514617 : Blo 1116628 2514617 := bstep (se 2 (by rfl) ⟨942981, by rfl⟩ : syracuseStep 2514617 = 1885963) B1885963
theorem B11460325 : Blo 1116628 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B6807311 : Blo 1116628 6807311 := bstep (se 1 (by rfl) ⟨5105483, by rfl⟩ : syracuseStep 6807311 = 10210967) B10210967
theorem B5168929 : Blo 1116628 5168929 := bstep (se 2 (by rfl) ⟨1938348, by rfl⟩ : syracuseStep 5168929 = 3876697) B3876697
theorem B20406167 : Blo 1116628 20406167 := bstep (se 1 (by rfl) ⟨15304625, by rfl⟩ : syracuseStep 20406167 = 30609251) B30609251
theorem B12083107 : Blo 1116628 12083107 := bstep (se 1 (by rfl) ⟨9062330, by rfl⟩ : syracuseStep 12083107 = 18124661) B18124661
theorem B2514959 : Blo 1116628 2514959 := bstep (se 1 (by rfl) ⟨1886219, by rfl⟩ : syracuseStep 2514959 = 3772439) B3772439
theorem B2514977 : Blo 1116628 2514977 := bstep (se 2 (by rfl) ⟨943116, by rfl⟩ : syracuseStep 2514977 = 1886233) B1886233
theorem B2515319 : Blo 1116628 2515319 := bstep (se 1 (by rfl) ⟨1886489, by rfl⟩ : syracuseStep 2515319 = 3772979) B3772979
theorem B45867541 : Blo 1116628 45867541 := bstep (se 6 (by rfl) ⟨1075020, by rfl⟩ : syracuseStep 45867541 = 2150041) B2150041
theorem B2515499 : Blo 1116628 2515499 := bstep (se 1 (by rfl) ⟨1886624, by rfl⟩ : syracuseStep 2515499 = 3773249) B3773249
theorem B5661251 : Blo 1116628 5661251 := bstep (se 1 (by rfl) ⟨4245938, by rfl⟩ : syracuseStep 5661251 = 8491877) B8491877
theorem B3400481 : Blo 1116628 3400481 := bstep (se 2 (by rfl) ⟨1275180, by rfl⟩ : syracuseStep 3400481 = 2550361) B2550361
theorem B5661575 : Blo 1116628 5661575 := bstep (se 1 (by rfl) ⟨4246181, by rfl⟩ : syracuseStep 5661575 = 8492363) B8492363
theorem B2515859 : Blo 1116628 2515859 := bstep (se 1 (by rfl) ⟨1886894, by rfl⟩ : syracuseStep 2515859 = 3773789) B3773789
theorem B48456629 : Blo 1116628 48456629 := bstep (se 5 (by rfl) ⟨2271404, by rfl⟩ : syracuseStep 48456629 = 4542809) B4542809
theorem B2122681 : Blo 1116628 2122681 := bstep (se 2 (by rfl) ⟨796005, by rfl⟩ : syracuseStep 2122681 = 1592011) B1592011
theorem B2515913 : Blo 1116628 2515913 := bstep (se 2 (by rfl) ⟨943467, by rfl⟩ : syracuseStep 2515913 = 1886935) B1886935
theorem B2123023 : Blo 1116628 2123023 := bstep (se 1 (by rfl) ⟨1592267, by rfl⟩ : syracuseStep 2123023 = 3184535) B3184535
theorem B2516615 : Blo 1116628 2516615 := bstep (se 1 (by rfl) ⟨1887461, by rfl⟩ : syracuseStep 2516615 = 3774923) B3774923
theorem B9070309 : Blo 1116628 9070309 := bstep (se 4 (by rfl) ⟨850341, by rfl⟩ : syracuseStep 9070309 = 1700683) B1700683
theorem B2516795 : Blo 1116628 2516795 := bstep (se 1 (by rfl) ⟨1887596, by rfl⟩ : syracuseStep 2516795 = 3775193) B3775193
theorem B4253593 : Blo 1116628 4253593 := bstep (se 2 (by rfl) ⟨1595097, by rfl⟩ : syracuseStep 4253593 = 3190195) B3190195
theorem B2516921 : Blo 1116628 2516921 := bstep (se 2 (by rfl) ⟨943845, by rfl⟩ : syracuseStep 2516921 = 1887691) B1887691
theorem B12085271 : Blo 1116628 12085271 := bstep (se 1 (by rfl) ⟨9063953, by rfl⟩ : syracuseStep 12085271 = 18127907) B18127907
theorem B2123911 : Blo 1116628 2123911 := bstep (se 1 (by rfl) ⟨1592933, by rfl⟩ : syracuseStep 2123911 = 3185867) B3185867
theorem B4778185 : Blo 1116628 4778185 := bstep (se 2 (by rfl) ⟨1791819, by rfl⟩ : syracuseStep 4778185 = 3583639) B3583639
theorem B4253897 : Blo 1116628 4253897 := bstep (se 2 (by rfl) ⟨1595211, by rfl⟩ : syracuseStep 4253897 = 3190423) B3190423
theorem B10741997 : Blo 1116628 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B2517263 : Blo 1116628 2517263 := bstep (se 1 (by rfl) ⟨1887947, by rfl⟩ : syracuseStep 2517263 = 3775895) B3775895
theorem B2517281 : Blo 1116628 2517281 := bstep (se 2 (by rfl) ⟨943980, by rfl⟩ : syracuseStep 2517281 = 1887961) B1887961
theorem B7662109 : Blo 1116628 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B6056477 : Blo 1116628 6056477 := bstep (se 3 (by rfl) ⟨1135589, by rfl⟩ : syracuseStep 6056477 = 2271179) B2271179
theorem B2517623 : Blo 1116628 2517623 := bstep (se 1 (by rfl) ⟨1888217, by rfl⟩ : syracuseStep 2517623 = 3776435) B3776435
theorem B2517803 : Blo 1116628 2517803 := bstep (se 1 (by rfl) ⟨1888352, by rfl⟩ : syracuseStep 2517803 = 3776705) B3776705
theorem B9562931 : Blo 1116628 9562931 := bstep (se 1 (by rfl) ⟨7172198, by rfl⟩ : syracuseStep 9562931 = 14344397) B14344397
theorem B4254839 : Blo 1116628 4254839 := bstep (se 1 (by rfl) ⟨3191129, by rfl⟩ : syracuseStep 4254839 = 6382259) B6382259
theorem B2518163 : Blo 1116628 2518163 := bstep (se 1 (by rfl) ⟨1888622, by rfl⟩ : syracuseStep 2518163 = 3777245) B3777245
theorem B2518217 : Blo 1116628 2518217 := bstep (se 2 (by rfl) ⟨944331, by rfl⟩ : syracuseStep 2518217 = 1888663) B1888663
theorem B5369291 : Blo 1116628 5369291 := bstep (se 1 (by rfl) ⟨4026968, by rfl⟩ : syracuseStep 5369291 = 8053937) B8053937
theorem B4779587 : Blo 1116628 4779587 := bstep (se 1 (by rfl) ⟨3584690, by rfl⟩ : syracuseStep 4779587 = 7169381) B7169381
theorem B7171841 : Blo 1116628 7171841 := bstep (se 2 (by rfl) ⟨2689440, by rfl⟩ : syracuseStep 7171841 = 5378881) B5378881
theorem B9563993 : Blo 1116628 9563993 := bstep (se 2 (by rfl) ⟨3586497, by rfl⟩ : syracuseStep 9563993 = 7172995) B7172995
theorem B2518919 : Blo 1116628 2518919 := bstep (se 1 (by rfl) ⟨1889189, by rfl⟩ : syracuseStep 2518919 = 3778379) B3778379
theorem B2125703 : Blo 1116628 2125703 := bstep (se 1 (by rfl) ⟨1594277, by rfl⟩ : syracuseStep 2125703 = 3188555) B3188555
theorem B5369753 : Blo 1116628 5369753 := bstep (se 2 (by rfl) ⟨2013657, by rfl⟩ : syracuseStep 5369753 = 4027315) B4027315
theorem B7171993 : Blo 1116628 7171993 := bstep (se 2 (by rfl) ⟨2689497, by rfl⟩ : syracuseStep 7171993 = 5378995) B5378995
theorem B2387897 : Blo 1116628 2387897 := bstep (se 2 (by rfl) ⟨895461, by rfl⟩ : syracuseStep 2387897 = 1790923) B1790923
theorem B2519099 : Blo 1116628 2519099 := bstep (se 1 (by rfl) ⟨1889324, by rfl⟩ : syracuseStep 2519099 = 3778649) B3778649
theorem B2519225 : Blo 1116628 2519225 := bstep (se 2 (by rfl) ⟨944709, by rfl⟩ : syracuseStep 2519225 = 1889419) B1889419
theorem B3633353 : Blo 1116628 3633353 := bstep (se 2 (by rfl) ⟨1362507, by rfl⟩ : syracuseStep 3633353 = 2725015) B2725015
theorem B10907885 : Blo 1116628 10907885 := bstep (se 3 (by rfl) ⟨2045228, by rfl⟩ : syracuseStep 10907885 = 4090457) B4090457
theorem B5665139 : Blo 1116628 5665139 := bstep (se 1 (by rfl) ⟨4248854, by rfl⟩ : syracuseStep 5665139 = 8497709) B8497709
theorem B2388359 : Blo 1116628 2388359 := bstep (se 1 (by rfl) ⟨1791269, by rfl⟩ : syracuseStep 2388359 = 3582539) B3582539
theorem B4026809 : Blo 1116628 4026809 := bstep (se 2 (by rfl) ⟨1510053, by rfl⟩ : syracuseStep 4026809 = 3020107) B3020107
theorem B2519567 : Blo 1116628 2519567 := bstep (se 1 (by rfl) ⟨1889675, by rfl⟩ : syracuseStep 2519567 = 3779351) B3779351
theorem B2519585 : Blo 1116628 2519585 := bstep (se 2 (by rfl) ⟨944844, by rfl⟩ : syracuseStep 2519585 = 1889689) B1889689
theorem B5665625 : Blo 1116628 5665625 := bstep (se 2 (by rfl) ⟨2124609, by rfl⟩ : syracuseStep 5665625 = 4249219) B4249219
theorem B2519927 : Blo 1116628 2519927 := bstep (se 1 (by rfl) ⟨1889945, by rfl⟩ : syracuseStep 2519927 = 3779891) B3779891
theorem B5370923 : Blo 1116628 5370923 := bstep (se 1 (by rfl) ⟨4028192, by rfl⟩ : syracuseStep 5370923 = 8056385) B8056385
theorem B2520107 : Blo 1116628 2520107 := bstep (se 1 (by rfl) ⟨1890080, by rfl⟩ : syracuseStep 2520107 = 3780161) B3780161
theorem B11465815 : Blo 1116628 11465815 := bstep (se 1 (by rfl) ⟨8599361, by rfl⟩ : syracuseStep 11465815 = 17198723) B17198723
theorem B2520467 : Blo 1116628 2520467 := bstep (se 1 (by rfl) ⟨1890350, by rfl⟩ : syracuseStep 2520467 = 3780701) B3780701
theorem B2520521 : Blo 1116628 2520521 := bstep (se 2 (by rfl) ⟨945195, by rfl⟩ : syracuseStep 2520521 = 1890391) B1890391
theorem B5109277 : Blo 1116628 5109277 := bstep (se 3 (by rfl) ⟨957989, by rfl⟩ : syracuseStep 5109277 = 1915979) B1915979
theorem B2389537 : Blo 1116628 2389537 := bstep (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) B1792153
theorem B2684731 : Blo 1116628 2684731 := bstep (se 1 (by rfl) ⟨2013548, by rfl⟩ : syracuseStep 2684731 = 4027097) B4027097
theorem B1701803 : Blo 1116628 1701803 := bstep (se 1 (by rfl) ⟨1276352, by rfl⟩ : syracuseStep 1701803 = 2552705) B2552705
theorem B8059013 : Blo 1116628 8059013 := bstep (se 4 (by rfl) ⟨755532, by rfl⟩ : syracuseStep 8059013 = 1511065) B1511065
theorem B2521223 : Blo 1116628 2521223 := bstep (se 1 (by rfl) ⟨1890917, by rfl⟩ : syracuseStep 2521223 = 3781835) B3781835
theorem B2521403 : Blo 1116628 2521403 := bstep (se 1 (by rfl) ⟨1891052, by rfl⟩ : syracuseStep 2521403 = 3782105) B3782105
theorem B6453593 : Blo 1116628 6453593 := bstep (se 2 (by rfl) ⟨2420097, by rfl⟩ : syracuseStep 6453593 = 4840195) B4840195
theorem B10222199 : Blo 1116628 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B5667731 : Blo 1116628 5667731 := bstep (se 1 (by rfl) ⟨4250798, by rfl⟩ : syracuseStep 5667731 = 8501597) B8501597
theorem B2554895 : Blo 1116628 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B1277191 : Blo 1116628 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B3407305 : Blo 1116628 3407305 := bstep (se 2 (by rfl) ⟨1277739, by rfl⟩ : syracuseStep 3407305 = 2555479) B2555479
theorem B10878583 : Blo 1116628 10878583 := bstep (se 1 (by rfl) ⟨8158937, by rfl⟩ : syracuseStep 10878583 = 16317875) B16317875
theorem B1703567 : Blo 1116628 1703567 := bstep (se 1 (by rfl) ⟨1277675, by rfl⟩ : syracuseStep 1703567 = 2555351) B2555351
theorem B1703695 : Blo 1116628 1703695 := bstep (se 1 (by rfl) ⟨1277771, by rfl⟩ : syracuseStep 1703695 = 2555543) B2555543
theorem B2686807 : Blo 1116628 2686807 := bstep (se 1 (by rfl) ⟨2015105, by rfl⟩ : syracuseStep 2686807 = 4030211) B4030211
theorem B16154639 : Blo 1116628 16154639 := bstep (se 1 (by rfl) ⟨12115979, by rfl⟩ : syracuseStep 16154639 = 24231959) B24231959
theorem B3768929 : Blo 1116628 3768929 := bstep (se 2 (by rfl) ⟨1413348, by rfl⟩ : syracuseStep 3768929 = 2826697) B2826697
theorem B4785551 : Blo 1116628 4785551 := bstep (se 1 (by rfl) ⟨3589163, by rfl⟩ : syracuseStep 4785551 = 7178327) B7178327
theorem B10749347 : Blo 1116628 10749347 := bstep (se 1 (by rfl) ⟨8062010, by rfl⟩ : syracuseStep 10749347 = 16124021) B16124021
theorem B36800315 : Blo 1116628 36800315 := bstep (se 1 (by rfl) ⟨27600236, by rfl⟩ : syracuseStep 36800315 = 55200473) B55200473
theorem B19105631 : Blo 1116628 19105631 := bstep (se 1 (by rfl) ⟨14329223, by rfl⟩ : syracuseStep 19105631 = 28658447) B28658447
theorem B3770387 : Blo 1116628 3770387 := bstep (se 1 (by rfl) ⟨2827790, by rfl⟩ : syracuseStep 3770387 = 5655581) B5655581
theorem B12093745 : Blo 1116628 12093745 := bstep (se 2 (by rfl) ⟨4535154, by rfl⟩ : syracuseStep 12093745 = 9070309) B9070309
theorem B3770711 : Blo 1116628 3770711 := bstep (se 1 (by rfl) ⟨2828033, by rfl⟩ : syracuseStep 3770711 = 5656067) B5656067
theorem B18155927 : Blo 1116628 18155927 := bstep (se 1 (by rfl) ⟨13616945, by rfl⟩ : syracuseStep 18155927 = 27233891) B27233891
theorem B1116635 : Blo 1116628 1116635 := bstep (se 1 (by rfl) ⟨837476, by rfl⟩ : syracuseStep 1116635 = 1674953) B1674953
theorem B5671457 : Blo 1116628 5671457 := bstep (se 2 (by rfl) ⟨2126796, by rfl⟩ : syracuseStep 5671457 = 4253593) B4253593
theorem B1116711 : Blo 1116628 1116711 := bstep (se 1 (by rfl) ⟨837533, by rfl⟩ : syracuseStep 1116711 = 1675067) B1675067
theorem B1116751 : Blo 1116628 1116751 := bstep (se 1 (by rfl) ⟨837563, by rfl⟩ : syracuseStep 1116751 = 1675127) B1675127
theorem B1116767 : Blo 1116628 1116767 := bstep (se 1 (by rfl) ⟨837575, by rfl⟩ : syracuseStep 1116767 = 1675151) B1675151
theorem B1116795 : Blo 1116628 1116795 := bstep (se 1 (by rfl) ⟨837596, by rfl⟩ : syracuseStep 1116795 = 1675193) B1675193
theorem B1116847 : Blo 1116628 1116847 := bstep (se 1 (by rfl) ⟨837635, by rfl⟩ : syracuseStep 1116847 = 1675271) B1675271
theorem B1116871 : Blo 1116628 1116871 := bstep (se 1 (by rfl) ⟨837653, by rfl⟩ : syracuseStep 1116871 = 1675307) B1675307
theorem B1116891 : Blo 1116628 1116891 := bstep (se 1 (by rfl) ⟨837668, by rfl⟩ : syracuseStep 1116891 = 1675337) B1675337
theorem B1116967 : Blo 1116628 1116967 := bstep (se 1 (by rfl) ⟨837725, by rfl⟩ : syracuseStep 1116967 = 1675451) B1675451
theorem B1117007 : Blo 1116628 1117007 := bstep (se 1 (by rfl) ⟨837755, by rfl⟩ : syracuseStep 1117007 = 1675511) B1675511
theorem B1117023 : Blo 1116628 1117023 := bstep (se 1 (by rfl) ⟨837767, by rfl⟩ : syracuseStep 1117023 = 1675535) B1675535
theorem B4590445 : Blo 1116628 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B1117051 : Blo 1116628 1117051 := bstep (se 1 (by rfl) ⟨837788, by rfl⟩ : syracuseStep 1117051 = 1675577) B1675577
theorem B1117103 : Blo 1116628 1117103 := bstep (se 1 (by rfl) ⟨837827, by rfl⟩ : syracuseStep 1117103 = 1675655) B1675655
theorem B1117127 : Blo 1116628 1117127 := bstep (se 1 (by rfl) ⟨837845, by rfl⟩ : syracuseStep 1117127 = 1675691) B1675691
theorem B1117147 : Blo 1116628 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B1117223 : Blo 1116628 1117223 := bstep (se 1 (by rfl) ⟨837917, by rfl⟩ : syracuseStep 1117223 = 1675835) B1675835
theorem B1117263 : Blo 1116628 1117263 := bstep (se 1 (by rfl) ⟨837947, by rfl⟩ : syracuseStep 1117263 = 1675895) B1675895
theorem B1117279 : Blo 1116628 1117279 := bstep (se 1 (by rfl) ⟨837959, by rfl⟩ : syracuseStep 1117279 = 1675919) B1675919
theorem B1117307 : Blo 1116628 1117307 := bstep (se 1 (by rfl) ⟨837980, by rfl⟩ : syracuseStep 1117307 = 1675961) B1675961
theorem B1117359 : Blo 1116628 1117359 := bstep (se 1 (by rfl) ⟨838019, by rfl⟩ : syracuseStep 1117359 = 1676039) B1676039
theorem B1117383 : Blo 1116628 1117383 := bstep (se 1 (by rfl) ⟨838037, by rfl⟩ : syracuseStep 1117383 = 1676075) B1676075
theorem B1117403 : Blo 1116628 1117403 := bstep (se 1 (by rfl) ⟨838052, by rfl⟩ : syracuseStep 1117403 = 1676105) B1676105
theorem B1117479 : Blo 1116628 1117479 := bstep (se 1 (by rfl) ⟨838109, by rfl⟩ : syracuseStep 1117479 = 1676219) B1676219
theorem B1117519 : Blo 1116628 1117519 := bstep (se 1 (by rfl) ⟨838139, by rfl⟩ : syracuseStep 1117519 = 1676279) B1676279
theorem B1117535 : Blo 1116628 1117535 := bstep (se 1 (by rfl) ⟨838151, by rfl⟩ : syracuseStep 1117535 = 1676303) B1676303
theorem B1117563 : Blo 1116628 1117563 := bstep (se 1 (by rfl) ⟨838172, by rfl⟩ : syracuseStep 1117563 = 1676345) B1676345
theorem B3181949 : Blo 1116628 3181949 := bstep (se 3 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 3181949 = 1193231) B1193231
theorem B3771791 : Blo 1116628 3771791 := bstep (se 1 (by rfl) ⟨2828843, by rfl⟩ : syracuseStep 3771791 = 5657687) B5657687
theorem B1117615 : Blo 1116628 1117615 := bstep (se 1 (by rfl) ⟨838211, by rfl⟩ : syracuseStep 1117615 = 1676423) B1676423
theorem B1117639 : Blo 1116628 1117639 := bstep (se 1 (by rfl) ⟨838229, by rfl⟩ : syracuseStep 1117639 = 1676459) B1676459
theorem B1117659 : Blo 1116628 1117659 := bstep (se 1 (by rfl) ⟨838244, by rfl⟩ : syracuseStep 1117659 = 1676489) B1676489
theorem B5377499 : Blo 1116628 5377499 := bstep (se 1 (by rfl) ⟨4033124, by rfl⟩ : syracuseStep 5377499 = 8066249) B8066249
theorem B1117735 : Blo 1116628 1117735 := bstep (se 1 (by rfl) ⟨838301, by rfl⟩ : syracuseStep 1117735 = 1676603) B1676603
theorem B1117775 : Blo 1116628 1117775 := bstep (se 1 (by rfl) ⟨838331, by rfl⟩ : syracuseStep 1117775 = 1676663) B1676663
theorem B1117791 : Blo 1116628 1117791 := bstep (se 1 (by rfl) ⟨838343, by rfl⟩ : syracuseStep 1117791 = 1676687) B1676687
theorem B1117819 : Blo 1116628 1117819 := bstep (se 1 (by rfl) ⟨838364, by rfl⟩ : syracuseStep 1117819 = 1676729) B1676729
theorem B1117871 : Blo 1116628 1117871 := bstep (se 1 (by rfl) ⟨838403, by rfl⟩ : syracuseStep 1117871 = 1676807) B1676807
theorem B1117895 : Blo 1116628 1117895 := bstep (se 1 (by rfl) ⟨838421, by rfl⟩ : syracuseStep 1117895 = 1676843) B1676843
theorem B3182291 : Blo 1116628 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B3772115 : Blo 1116628 3772115 := bstep (se 1 (by rfl) ⟨2829086, by rfl⟩ : syracuseStep 3772115 = 5658173) B5658173
theorem B1117915 : Blo 1116628 1117915 := bstep (se 1 (by rfl) ⟨838436, by rfl⟩ : syracuseStep 1117915 = 1676873) B1676873
theorem B1675001 : Blo 1116628 1675001 := bstep (se 2 (by rfl) ⟨628125, by rfl⟩ : syracuseStep 1675001 = 1256251) B1256251
theorem B1117991 : Blo 1116628 1117991 := bstep (se 1 (by rfl) ⟨838493, by rfl⟩ : syracuseStep 1117991 = 1676987) B1676987
theorem B1118031 : Blo 1116628 1118031 := bstep (se 1 (by rfl) ⟨838523, by rfl⟩ : syracuseStep 1118031 = 1677047) B1677047
theorem B1675103 : Blo 1116628 1675103 := bstep (se 1 (by rfl) ⟨1256327, by rfl⟩ : syracuseStep 1675103 = 2512655) B2512655
theorem B1118047 : Blo 1116628 1118047 := bstep (se 1 (by rfl) ⟨838535, by rfl⟩ : syracuseStep 1118047 = 1677071) B1677071
theorem B1675115 : Blo 1116628 1675115 := bstep (se 1 (by rfl) ⟨1256336, by rfl⟩ : syracuseStep 1675115 = 2512673) B2512673
theorem B1118075 : Blo 1116628 1118075 := bstep (se 1 (by rfl) ⟨838556, by rfl⟩ : syracuseStep 1118075 = 1677113) B1677113
theorem B3018671 : Blo 1116628 3018671 := bstep (se 1 (by rfl) ⟨2264003, by rfl⟩ : syracuseStep 3018671 = 4528007) B4528007
theorem B1118127 : Blo 1116628 1118127 := bstep (se 1 (by rfl) ⟨838595, by rfl⟩ : syracuseStep 1118127 = 1677191) B1677191
theorem B1118151 : Blo 1116628 1118151 := bstep (se 1 (by rfl) ⟨838613, by rfl⟩ : syracuseStep 1118151 = 1677227) B1677227
theorem B1118171 : Blo 1116628 1118171 := bstep (se 1 (by rfl) ⟨838628, by rfl⟩ : syracuseStep 1118171 = 1677257) B1677257
theorem B19140623 : Blo 1116628 19140623 := bstep (se 1 (by rfl) ⟨14355467, by rfl⟩ : syracuseStep 19140623 = 28710935) B28710935
theorem B1118247 : Blo 1116628 1118247 := bstep (se 1 (by rfl) ⟨838685, by rfl⟩ : syracuseStep 1118247 = 1677371) B1677371
theorem B1675343 : Blo 1116628 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B1118287 : Blo 1116628 1118287 := bstep (se 1 (by rfl) ⟨838715, by rfl⟩ : syracuseStep 1118287 = 1677431) B1677431
theorem B1118303 : Blo 1116628 1118303 := bstep (se 1 (by rfl) ⟨838727, by rfl⟩ : syracuseStep 1118303 = 1677455) B1677455
theorem B1118331 : Blo 1116628 1118331 := bstep (se 1 (by rfl) ⟨838748, by rfl⟩ : syracuseStep 1118331 = 1677497) B1677497
theorem B1118383 : Blo 1116628 1118383 := bstep (se 1 (by rfl) ⟨838787, by rfl⟩ : syracuseStep 1118383 = 1677575) B1677575
theorem B1675463 : Blo 1116628 1675463 := bstep (se 1 (by rfl) ⟨1256597, by rfl⟩ : syracuseStep 1675463 = 2513195) B2513195
theorem B1118407 : Blo 1116628 1118407 := bstep (se 1 (by rfl) ⟨838805, by rfl⟩ : syracuseStep 1118407 = 1677611) B1677611
theorem B1118427 : Blo 1116628 1118427 := bstep (se 1 (by rfl) ⟨838820, by rfl⟩ : syracuseStep 1118427 = 1677641) B1677641
theorem B1118503 : Blo 1116628 1118503 := bstep (se 1 (by rfl) ⟨838877, by rfl⟩ : syracuseStep 1118503 = 1677755) B1677755
theorem B12095819 : Blo 1116628 12095819 := bstep (se 1 (by rfl) ⟨9071864, by rfl⟩ : syracuseStep 12095819 = 18143729) B18143729
theorem B1118543 : Blo 1116628 1118543 := bstep (se 1 (by rfl) ⟨838907, by rfl⟩ : syracuseStep 1118543 = 1677815) B1677815
theorem B1118559 : Blo 1116628 1118559 := bstep (se 1 (by rfl) ⟨838919, by rfl⟩ : syracuseStep 1118559 = 1677839) B1677839
theorem B1675625 : Blo 1116628 1675625 := bstep (se 2 (by rfl) ⟨628359, by rfl⟩ : syracuseStep 1675625 = 1256719) B1256719
theorem B1118587 : Blo 1116628 1118587 := bstep (se 1 (by rfl) ⟨838940, by rfl⟩ : syracuseStep 1118587 = 1677881) B1677881
theorem B1413551 : Blo 1116628 1413551 := bstep (se 1 (by rfl) ⟨1060163, by rfl⟩ : syracuseStep 1413551 = 2120327) B2120327
theorem B1118639 : Blo 1116628 1118639 := bstep (se 1 (by rfl) ⟨838979, by rfl⟩ : syracuseStep 1118639 = 1677959) B1677959
theorem B1675703 : Blo 1116628 1675703 := bstep (se 1 (by rfl) ⟨1256777, by rfl⟩ : syracuseStep 1675703 = 2513555) B2513555
theorem B1118663 : Blo 1116628 1118663 := bstep (se 1 (by rfl) ⟨838997, by rfl⟩ : syracuseStep 1118663 = 1677995) B1677995
theorem B1675739 : Blo 1116628 1675739 := bstep (se 1 (by rfl) ⟨1256804, by rfl⟩ : syracuseStep 1675739 = 2513609) B2513609
theorem B1118683 : Blo 1116628 1118683 := bstep (se 1 (by rfl) ⟨839012, by rfl⟩ : syracuseStep 1118683 = 1678025) B1678025
theorem B1118759 : Blo 1116628 1118759 := bstep (se 1 (by rfl) ⟨839069, by rfl⟩ : syracuseStep 1118759 = 1678139) B1678139
theorem B1118799 : Blo 1116628 1118799 := bstep (se 1 (by rfl) ⟨839099, by rfl⟩ : syracuseStep 1118799 = 1678199) B1678199
theorem B1118815 : Blo 1116628 1118815 := bstep (se 1 (by rfl) ⟨839111, by rfl⟩ : syracuseStep 1118815 = 1678223) B1678223
theorem B1118843 : Blo 1116628 1118843 := bstep (se 1 (by rfl) ⟨839132, by rfl⟩ : syracuseStep 1118843 = 1678265) B1678265
theorem B1118895 : Blo 1116628 1118895 := bstep (se 1 (by rfl) ⟨839171, by rfl⟩ : syracuseStep 1118895 = 1678343) B1678343
theorem B3183293 : Blo 1116628 3183293 := bstep (se 3 (by rfl) ⟨596867, by rfl⟩ : syracuseStep 3183293 = 1193735) B1193735
theorem B1118919 : Blo 1116628 1118919 := bstep (se 1 (by rfl) ⟨839189, by rfl⟩ : syracuseStep 1118919 = 1678379) B1678379
theorem B1118939 : Blo 1116628 1118939 := bstep (se 1 (by rfl) ⟨839204, by rfl⟩ : syracuseStep 1118939 = 1678409) B1678409
theorem B1119015 : Blo 1116628 1119015 := bstep (se 1 (by rfl) ⟨839261, by rfl⟩ : syracuseStep 1119015 = 1678523) B1678523
theorem B1119055 : Blo 1116628 1119055 := bstep (se 1 (by rfl) ⟨839291, by rfl⟩ : syracuseStep 1119055 = 1678583) B1678583
theorem B1119071 : Blo 1116628 1119071 := bstep (se 1 (by rfl) ⟨839303, by rfl⟩ : syracuseStep 1119071 = 1678607) B1678607
theorem B3773303 : Blo 1116628 3773303 := bstep (se 1 (by rfl) ⟨2829977, by rfl⟩ : syracuseStep 3773303 = 5659955) B5659955
theorem B1119099 : Blo 1116628 1119099 := bstep (se 1 (by rfl) ⟨839324, by rfl⟩ : syracuseStep 1119099 = 1678649) B1678649
theorem B1676207 : Blo 1116628 1676207 := bstep (se 1 (by rfl) ⟨1257155, by rfl⟩ : syracuseStep 1676207 = 2514311) B2514311
theorem B1119151 : Blo 1116628 1119151 := bstep (se 1 (by rfl) ⟨839363, by rfl⟩ : syracuseStep 1119151 = 1678727) B1678727
theorem B1119175 : Blo 1116628 1119175 := bstep (se 1 (by rfl) ⟨839381, by rfl⟩ : syracuseStep 1119175 = 1678763) B1678763
theorem B1119195 : Blo 1116628 1119195 := bstep (se 1 (by rfl) ⟨839396, by rfl⟩ : syracuseStep 1119195 = 1678793) B1678793
theorem B1676297 : Blo 1116628 1676297 := bstep (se 2 (by rfl) ⟨628611, by rfl⟩ : syracuseStep 1676297 = 1257223) B1257223
theorem B1676327 : Blo 1116628 1676327 := bstep (se 1 (by rfl) ⟨1257245, by rfl⟩ : syracuseStep 1676327 = 2514491) B2514491
theorem B1119271 : Blo 1116628 1119271 := bstep (se 1 (by rfl) ⟨839453, by rfl⟩ : syracuseStep 1119271 = 1678907) B1678907
theorem B3773519 : Blo 1116628 3773519 := bstep (se 1 (by rfl) ⟨2830139, by rfl⟩ : syracuseStep 3773519 = 5660279) B5660279
theorem B1119311 : Blo 1116628 1119311 := bstep (se 1 (by rfl) ⟨839483, by rfl⟩ : syracuseStep 1119311 = 1678967) B1678967
theorem B1119327 : Blo 1116628 1119327 := bstep (se 1 (by rfl) ⟨839495, by rfl⟩ : syracuseStep 1119327 = 1678991) B1678991
theorem B1676411 : Blo 1116628 1676411 := bstep (se 1 (by rfl) ⟨1257308, by rfl⟩ : syracuseStep 1676411 = 2514617) B2514617
theorem B1119355 : Blo 1116628 1119355 := bstep (se 1 (by rfl) ⟨839516, by rfl⟩ : syracuseStep 1119355 = 1679033) B1679033
theorem B1119407 : Blo 1116628 1119407 := bstep (se 1 (by rfl) ⟨839555, by rfl⟩ : syracuseStep 1119407 = 1679111) B1679111
theorem B1119431 : Blo 1116628 1119431 := bstep (se 1 (by rfl) ⟨839573, by rfl⟩ : syracuseStep 1119431 = 1679147) B1679147
theorem B1119451 : Blo 1116628 1119451 := bstep (se 1 (by rfl) ⟨839588, by rfl⟩ : syracuseStep 1119451 = 1679177) B1679177
theorem B1676537 : Blo 1116628 1676537 := bstep (se 2 (by rfl) ⟨628701, by rfl⟩ : syracuseStep 1676537 = 1257403) B1257403
theorem B13604111 : Blo 1116628 13604111 := bstep (se 1 (by rfl) ⟨10203083, by rfl⟩ : syracuseStep 13604111 = 20406167) B20406167
theorem B1119527 : Blo 1116628 1119527 := bstep (se 1 (by rfl) ⟨839645, by rfl⟩ : syracuseStep 1119527 = 1679291) B1679291
theorem B1119567 : Blo 1116628 1119567 := bstep (se 1 (by rfl) ⟨839675, by rfl⟩ : syracuseStep 1119567 = 1679351) B1679351
theorem B1676639 : Blo 1116628 1676639 := bstep (se 1 (by rfl) ⟨1257479, by rfl⟩ : syracuseStep 1676639 = 2514959) B2514959
theorem B1119583 : Blo 1116628 1119583 := bstep (se 1 (by rfl) ⟨839687, by rfl⟩ : syracuseStep 1119583 = 1679375) B1679375
theorem B1676651 : Blo 1116628 1676651 := bstep (se 1 (by rfl) ⟨1257488, by rfl⟩ : syracuseStep 1676651 = 2514977) B2514977
theorem B1119611 : Blo 1116628 1119611 := bstep (se 1 (by rfl) ⟨839708, by rfl⟩ : syracuseStep 1119611 = 1679417) B1679417
theorem B1119663 : Blo 1116628 1119663 := bstep (se 1 (by rfl) ⟨839747, by rfl⟩ : syracuseStep 1119663 = 1679495) B1679495
theorem B1119687 : Blo 1116628 1119687 := bstep (se 1 (by rfl) ⟨839765, by rfl⟩ : syracuseStep 1119687 = 1679531) B1679531
theorem B3773897 : Blo 1116628 3773897 := bstep (se 2 (by rfl) ⟨1415211, by rfl⟩ : syracuseStep 3773897 = 2830423) B2830423
theorem B1119707 : Blo 1116628 1119707 := bstep (se 1 (by rfl) ⟨839780, by rfl⟩ : syracuseStep 1119707 = 1679561) B1679561
theorem B1119783 : Blo 1116628 1119783 := bstep (se 1 (by rfl) ⟨839837, by rfl⟩ : syracuseStep 1119783 = 1679675) B1679675
theorem B16127531 : Blo 1116628 16127531 := bstep (se 1 (by rfl) ⟨12095648, by rfl⟩ : syracuseStep 16127531 = 24191297) B24191297
theorem B1676879 : Blo 1116628 1676879 := bstep (se 1 (by rfl) ⟨1257659, by rfl⟩ : syracuseStep 1676879 = 2515319) B2515319
theorem B1119823 : Blo 1116628 1119823 := bstep (se 1 (by rfl) ⟨839867, by rfl⟩ : syracuseStep 1119823 = 1679735) B1679735
theorem B1119839 : Blo 1116628 1119839 := bstep (se 1 (by rfl) ⟨839879, by rfl⟩ : syracuseStep 1119839 = 1679759) B1679759
theorem B1119867 : Blo 1116628 1119867 := bstep (se 1 (by rfl) ⟨839900, by rfl⟩ : syracuseStep 1119867 = 1679801) B1679801
theorem B1119919 : Blo 1116628 1119919 := bstep (se 1 (by rfl) ⟨839939, by rfl⟩ : syracuseStep 1119919 = 1679879) B1679879
theorem B1676999 : Blo 1116628 1676999 := bstep (se 1 (by rfl) ⟨1257749, by rfl⟩ : syracuseStep 1676999 = 2515499) B2515499
theorem B1119943 : Blo 1116628 1119943 := bstep (se 1 (by rfl) ⟨839957, by rfl⟩ : syracuseStep 1119943 = 1679915) B1679915
theorem B3774167 : Blo 1116628 3774167 := bstep (se 1 (by rfl) ⟨2830625, by rfl⟩ : syracuseStep 3774167 = 5661251) B5661251
theorem B1119963 : Blo 1116628 1119963 := bstep (se 1 (by rfl) ⟨839972, by rfl⟩ : syracuseStep 1119963 = 1679945) B1679945
theorem B6362873 : Blo 1116628 6362873 := bstep (se 2 (by rfl) ⟨2386077, by rfl⟩ : syracuseStep 6362873 = 4772155) B4772155
theorem B1120039 : Blo 1116628 1120039 := bstep (se 1 (by rfl) ⟨840029, by rfl⟩ : syracuseStep 1120039 = 1680059) B1680059
theorem B1120079 : Blo 1116628 1120079 := bstep (se 1 (by rfl) ⟨840059, by rfl⟩ : syracuseStep 1120079 = 1680119) B1680119
theorem B1120095 : Blo 1116628 1120095 := bstep (se 1 (by rfl) ⟨840071, by rfl⟩ : syracuseStep 1120095 = 1680143) B1680143
theorem B1677161 : Blo 1116628 1677161 := bstep (se 2 (by rfl) ⟨628935, by rfl⟩ : syracuseStep 1677161 = 1257871) B1257871
theorem B2266987 : Blo 1116628 2266987 := bstep (se 1 (by rfl) ⟨1700240, by rfl⟩ : syracuseStep 2266987 = 3400481) B3400481
theorem B5379959 : Blo 1116628 5379959 := bstep (se 1 (by rfl) ⟨4034969, by rfl⟩ : syracuseStep 5379959 = 8069939) B8069939
theorem B1120123 : Blo 1116628 1120123 := bstep (se 1 (by rfl) ⟨840092, by rfl⟩ : syracuseStep 1120123 = 1680185) B1680185
theorem B3774383 : Blo 1116628 3774383 := bstep (se 1 (by rfl) ⟨2830787, by rfl⟩ : syracuseStep 3774383 = 5661575) B5661575
theorem B1120175 : Blo 1116628 1120175 := bstep (se 1 (by rfl) ⟨840131, by rfl⟩ : syracuseStep 1120175 = 1680263) B1680263
theorem B1677239 : Blo 1116628 1677239 := bstep (se 1 (by rfl) ⟨1257929, by rfl⟩ : syracuseStep 1677239 = 2515859) B2515859
theorem B1120199 : Blo 1116628 1120199 := bstep (se 1 (by rfl) ⟨840149, by rfl⟩ : syracuseStep 1120199 = 1680299) B1680299
theorem B28645325 : Blo 1116628 28645325 := bstep (se 3 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 28645325 = 10741997) B10741997
theorem B1677275 : Blo 1116628 1677275 := bstep (se 1 (by rfl) ⟨1257956, by rfl⟩ : syracuseStep 1677275 = 2515913) B2515913
theorem B1120219 : Blo 1116628 1120219 := bstep (se 1 (by rfl) ⟨840164, by rfl⟩ : syracuseStep 1120219 = 1680329) B1680329
theorem B5380111 : Blo 1116628 5380111 := bstep (se 1 (by rfl) ⟨4035083, by rfl⟩ : syracuseStep 5380111 = 8070167) B8070167
theorem B8067109 : Blo 1116628 8067109 := bstep (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) B1512583
theorem B1120295 : Blo 1116628 1120295 := bstep (se 1 (by rfl) ⟨840221, by rfl⟩ : syracuseStep 1120295 = 1680443) B1680443
theorem B1120335 : Blo 1116628 1120335 := bstep (se 1 (by rfl) ⟨840251, by rfl⟩ : syracuseStep 1120335 = 1680503) B1680503
theorem B1120351 : Blo 1116628 1120351 := bstep (se 1 (by rfl) ⟨840263, by rfl⟩ : syracuseStep 1120351 = 1680527) B1680527
theorem B1120379 : Blo 1116628 1120379 := bstep (se 1 (by rfl) ⟨840284, by rfl⟩ : syracuseStep 1120379 = 1680569) B1680569
theorem B1120431 : Blo 1116628 1120431 := bstep (se 1 (by rfl) ⟨840323, by rfl⟩ : syracuseStep 1120431 = 1680647) B1680647
theorem B1120455 : Blo 1116628 1120455 := bstep (se 1 (by rfl) ⟨840341, by rfl⟩ : syracuseStep 1120455 = 1680683) B1680683
theorem B1120475 : Blo 1116628 1120475 := bstep (se 1 (by rfl) ⟨840356, by rfl⟩ : syracuseStep 1120475 = 1680713) B1680713
theorem B1120551 : Blo 1116628 1120551 := bstep (se 1 (by rfl) ⟨840413, by rfl⟩ : syracuseStep 1120551 = 1680827) B1680827
theorem B1120591 : Blo 1116628 1120591 := bstep (se 1 (by rfl) ⟨840443, by rfl⟩ : syracuseStep 1120591 = 1680887) B1680887
theorem B1120607 : Blo 1116628 1120607 := bstep (se 1 (by rfl) ⟨840455, by rfl⟩ : syracuseStep 1120607 = 1680911) B1680911
theorem B1677743 : Blo 1116628 1677743 := bstep (se 1 (by rfl) ⟨1258307, by rfl⟩ : syracuseStep 1677743 = 2516615) B2516615
theorem B3021275 : Blo 1116628 3021275 := bstep (se 1 (by rfl) ⟨2265956, by rfl⟩ : syracuseStep 3021275 = 4531913) B4531913
theorem B1677833 : Blo 1116628 1677833 := bstep (se 2 (by rfl) ⟨629187, by rfl⟩ : syracuseStep 1677833 = 1258375) B1258375
theorem B1677863 : Blo 1116628 1677863 := bstep (se 1 (by rfl) ⟨1258397, by rfl⟩ : syracuseStep 1677863 = 2516795) B2516795
theorem B1677947 : Blo 1116628 1677947 := bstep (se 1 (by rfl) ⟨1258460, by rfl⟩ : syracuseStep 1677947 = 2516921) B2516921
theorem B1678073 : Blo 1116628 1678073 := bstep (se 2 (by rfl) ⟨629277, by rfl⟩ : syracuseStep 1678073 = 1258555) B1258555
theorem B1678175 : Blo 1116628 1678175 := bstep (se 1 (by rfl) ⟨1258631, by rfl⟩ : syracuseStep 1678175 = 2517263) B2517263
theorem B1678187 : Blo 1116628 1678187 := bstep (se 1 (by rfl) ⟨1258640, by rfl⟩ : syracuseStep 1678187 = 2517281) B2517281
theorem B6364079 : Blo 1116628 6364079 := bstep (se 1 (by rfl) ⟨4773059, by rfl⟩ : syracuseStep 6364079 = 9546119) B9546119
theorem B4037651 : Blo 1116628 4037651 := bstep (se 1 (by rfl) ⟨3028238, by rfl⟩ : syracuseStep 4037651 = 6056477) B6056477
theorem B1678415 : Blo 1116628 1678415 := bstep (se 1 (by rfl) ⟨1258811, by rfl⟩ : syracuseStep 1678415 = 2517623) B2517623
theorem B3185821 : Blo 1116628 3185821 := bstep (se 3 (by rfl) ⟨597341, by rfl⟩ : syracuseStep 3185821 = 1194683) B1194683
theorem B6364331 : Blo 1116628 6364331 := bstep (se 1 (by rfl) ⟨4773248, by rfl⟩ : syracuseStep 6364331 = 9546497) B9546497
theorem B1678535 : Blo 1116628 1678535 := bstep (se 1 (by rfl) ⟨1258901, by rfl⟩ : syracuseStep 1678535 = 2517803) B2517803
theorem B1678697 : Blo 1116628 1678697 := bstep (se 2 (by rfl) ⟨629511, by rfl⟩ : syracuseStep 1678697 = 1259023) B1259023
theorem B3186049 : Blo 1116628 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B1678775 : Blo 1116628 1678775 := bstep (se 1 (by rfl) ⟨1259081, by rfl⟩ : syracuseStep 1678775 = 2518163) B2518163
theorem B1678811 : Blo 1116628 1678811 := bstep (se 1 (by rfl) ⟨1259108, by rfl⟩ : syracuseStep 1678811 = 2518217) B2518217
theorem B3579527 : Blo 1116628 3579527 := bstep (se 1 (by rfl) ⟨2684645, by rfl⟩ : syracuseStep 3579527 = 5369291) B5369291
theorem B3186391 : Blo 1116628 3186391 := bstep (se 1 (by rfl) ⟨2389793, by rfl⟩ : syracuseStep 3186391 = 4779587) B4779587
theorem B3579641 : Blo 1116628 3579641 := bstep (se 2 (by rfl) ⟨1342365, by rfl⟩ : syracuseStep 3579641 = 2684731) B2684731
theorem B1679279 : Blo 1116628 1679279 := bstep (se 1 (by rfl) ⟨1259459, by rfl⟩ : syracuseStep 1679279 = 2518919) B2518919
theorem B3579835 : Blo 1116628 3579835 := bstep (se 1 (by rfl) ⟨2684876, by rfl⟩ : syracuseStep 3579835 = 5369753) B5369753
theorem B1679369 : Blo 1116628 1679369 := bstep (se 2 (by rfl) ⟨629763, by rfl⟩ : syracuseStep 1679369 = 1259527) B1259527
theorem B1679399 : Blo 1116628 1679399 := bstep (se 1 (by rfl) ⟨1259549, by rfl⟩ : syracuseStep 1679399 = 2519099) B2519099
theorem B1679483 : Blo 1116628 1679483 := bstep (se 1 (by rfl) ⟨1259612, by rfl⟩ : syracuseStep 1679483 = 2519225) B2519225
theorem B12263653 : Blo 1116628 12263653 := bstep (se 4 (by rfl) ⟨1149717, by rfl⟩ : syracuseStep 12263653 = 2299435) B2299435
theorem B3776759 : Blo 1116628 3776759 := bstep (se 1 (by rfl) ⟨2832569, by rfl⟩ : syracuseStep 3776759 = 5665139) B5665139
theorem B1679609 : Blo 1116628 1679609 := bstep (se 2 (by rfl) ⟨629853, by rfl⟩ : syracuseStep 1679609 = 1259707) B1259707
theorem B12722507 : Blo 1116628 12722507 := bstep (se 1 (by rfl) ⟨9541880, by rfl⟩ : syracuseStep 12722507 = 19083761) B19083761
theorem B1679711 : Blo 1116628 1679711 := bstep (se 1 (by rfl) ⟨1259783, by rfl⟩ : syracuseStep 1679711 = 2519567) B2519567
theorem B1679723 : Blo 1116628 1679723 := bstep (se 1 (by rfl) ⟨1259792, by rfl⟩ : syracuseStep 1679723 = 2519585) B2519585
theorem B3777083 : Blo 1116628 3777083 := bstep (se 1 (by rfl) ⟨2832812, by rfl⟩ : syracuseStep 3777083 = 5665625) B5665625
theorem B1679951 : Blo 1116628 1679951 := bstep (se 1 (by rfl) ⟨1259963, by rfl⟩ : syracuseStep 1679951 = 2519927) B2519927
theorem B3580615 : Blo 1116628 3580615 := bstep (se 1 (by rfl) ⟨2685461, by rfl⟩ : syracuseStep 3580615 = 5370923) B5370923
theorem B1680071 : Blo 1116628 1680071 := bstep (se 1 (by rfl) ⟨1260053, by rfl⟩ : syracuseStep 1680071 = 2520107) B2520107
theorem B2827001 : Blo 1116628 2827001 := bstep (se 2 (by rfl) ⟨1060125, by rfl⟩ : syracuseStep 2827001 = 2120251) B2120251
theorem B3777353 : Blo 1116628 3777353 := bstep (se 2 (by rfl) ⟨1416507, by rfl⟩ : syracuseStep 3777353 = 2833015) B2833015
theorem B1680233 : Blo 1116628 1680233 := bstep (se 2 (by rfl) ⟨630087, by rfl⟩ : syracuseStep 1680233 = 1260175) B1260175
theorem B2827183 : Blo 1116628 2827183 := bstep (se 1 (by rfl) ⟨2120387, by rfl⟩ : syracuseStep 2827183 = 4240775) B4240775
theorem B1680311 : Blo 1116628 1680311 := bstep (se 1 (by rfl) ⟨1260233, by rfl⟩ : syracuseStep 1680311 = 2520467) B2520467
theorem B1680347 : Blo 1116628 1680347 := bstep (se 1 (by rfl) ⟨1260260, by rfl⟩ : syracuseStep 1680347 = 2520521) B2520521
theorem B2827649 : Blo 1116628 2827649 := bstep (se 2 (by rfl) ⟨1060368, by rfl⟩ : syracuseStep 2827649 = 2120737) B2120737
theorem B1680815 : Blo 1116628 1680815 := bstep (se 1 (by rfl) ⟨1260611, by rfl⟩ : syracuseStep 1680815 = 2521223) B2521223
theorem B9545161 : Blo 1116628 9545161 := bstep (se 2 (by rfl) ⟨3579435, by rfl⟩ : syracuseStep 9545161 = 7158871) B7158871
theorem B1680905 : Blo 1116628 1680905 := bstep (se 2 (by rfl) ⟨630339, by rfl⟩ : syracuseStep 1680905 = 1260679) B1260679
theorem B1680935 : Blo 1116628 1680935 := bstep (se 1 (by rfl) ⟨1260701, by rfl⟩ : syracuseStep 1680935 = 2521403) B2521403
theorem B4302395 : Blo 1116628 4302395 := bstep (se 1 (by rfl) ⟨3226796, by rfl⟩ : syracuseStep 4302395 = 6453593) B6453593
theorem B8496737 : Blo 1116628 8496737 := bstep (se 2 (by rfl) ⟨3186276, by rfl⟩ : syracuseStep 8496737 = 6372553) B6372553
theorem B6137593 : Blo 1116628 6137593 := bstep (se 2 (by rfl) ⟨2301597, by rfl⟩ : syracuseStep 6137593 = 4603195) B4603195
theorem B2828105 : Blo 1116628 2828105 := bstep (se 2 (by rfl) ⟨1060539, by rfl⟩ : syracuseStep 2828105 = 2121079) B2121079
theorem B1910711 : Blo 1116628 1910711 := bstep (se 1 (by rfl) ⟨1433033, by rfl⟩ : syracuseStep 1910711 = 2866067) B2866067
theorem B3778487 : Blo 1116628 3778487 := bstep (se 1 (by rfl) ⟨2833865, by rfl⟩ : syracuseStep 3778487 = 5667731) B5667731
theorem B6367247 : Blo 1116628 6367247 := bstep (se 1 (by rfl) ⟨4775435, by rfl⟩ : syracuseStep 6367247 = 9550871) B9550871
theorem B6138013 : Blo 1116628 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B2828459 : Blo 1116628 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B15280433 : Blo 1116628 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B2271593 : Blo 1116628 2271593 := bstep (se 2 (by rfl) ⟨851847, by rfl⟩ : syracuseStep 2271593 = 1703695) B1703695
theorem B6891905 : Blo 1116628 6891905 := bstep (se 2 (by rfl) ⟨2584464, by rfl⟩ : syracuseStep 6891905 = 5168929) B5168929
theorem B3582409 : Blo 1116628 3582409 := bstep (se 2 (by rfl) ⟨1343403, by rfl⟩ : syracuseStep 3582409 = 2686807) B2686807
theorem B3779081 : Blo 1116628 3779081 := bstep (se 2 (by rfl) ⟨1417155, by rfl⟩ : syracuseStep 3779081 = 2834311) B2834311
theorem B5384839 : Blo 1116628 5384839 := bstep (se 1 (by rfl) ⟨4038629, by rfl⟩ : syracuseStep 5384839 = 8077259) B8077259
theorem B1256287 : Blo 1116628 1256287 := bstep (se 1 (by rfl) ⟨942215, by rfl⟩ : syracuseStep 1256287 = 1884431) B1884431
theorem B2829239 : Blo 1116628 2829239 := bstep (se 1 (by rfl) ⟨2121929, by rfl⟩ : syracuseStep 2829239 = 4243859) B4243859
theorem B8498195 : Blo 1116628 8498195 := bstep (se 1 (by rfl) ⟨6373646, by rfl⟩ : syracuseStep 8498195 = 12747293) B12747293
theorem B1256647 : Blo 1116628 1256647 := bstep (se 1 (by rfl) ⟨942485, by rfl⟩ : syracuseStep 1256647 = 1884971) B1884971
theorem B3779945 : Blo 1116628 3779945 := bstep (se 2 (by rfl) ⟨1417479, by rfl⟩ : syracuseStep 3779945 = 2834959) B2834959
theorem B61156721 : Blo 1116628 61156721 := bstep (se 2 (by rfl) ⟨22933770, by rfl⟩ : syracuseStep 61156721 = 45867541) B45867541
theorem B1813903 : Blo 1116628 1813903 := bstep (se 1 (by rfl) ⟨1360427, by rfl⟩ : syracuseStep 1813903 = 2720855) B2720855
theorem B2830241 : Blo 1116628 2830241 := bstep (se 2 (by rfl) ⟨1061340, by rfl⟩ : syracuseStep 2830241 = 2122681) B2122681
theorem B3780539 : Blo 1116628 3780539 := bstep (se 1 (by rfl) ⟨2835404, by rfl⟩ : syracuseStep 3780539 = 5670809) B5670809
theorem B1257511 : Blo 1116628 1257511 := bstep (se 1 (by rfl) ⟨943133, by rfl⟩ : syracuseStep 1257511 = 1886267) B1886267
theorem B2830697 : Blo 1116628 2830697 := bstep (se 2 (by rfl) ⟨1061511, by rfl⟩ : syracuseStep 2830697 = 2123023) B2123023
theorem B4240289 : Blo 1116628 4240289 := bstep (se 2 (by rfl) ⟨1590108, by rfl⟩ : syracuseStep 4240289 = 3180217) B3180217
theorem B4240745 : Blo 1116628 4240745 := bstep (se 2 (by rfl) ⟨1590279, by rfl⟩ : syracuseStep 4240745 = 3180559) B3180559
theorem B2831881 : Blo 1116628 2831881 := bstep (se 2 (by rfl) ⟨1061955, by rfl⟩ : syracuseStep 2831881 = 2123911) B2123911
theorem B6370913 : Blo 1116628 6370913 := bstep (se 2 (by rfl) ⟨2389092, by rfl⟩ : syracuseStep 6370913 = 4778185) B4778185
theorem B1259131 : Blo 1116628 1259131 := bstep (se 1 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 1259131 = 1888697) B1888697
theorem B5748347 : Blo 1116628 5748347 := bstep (se 1 (by rfl) ⟨4311260, by rfl⟩ : syracuseStep 5748347 = 8622521) B8622521
theorem B4241261 : Blo 1116628 4241261 := bstep (se 3 (by rfl) ⟨795236, by rfl⟩ : syracuseStep 4241261 = 1590473) B1590473
theorem B6043501 : Blo 1116628 6043501 := bstep (se 3 (by rfl) ⟨1133156, by rfl⟩ : syracuseStep 6043501 = 2266313) B2266313
theorem B8501111 : Blo 1116628 8501111 := bstep (se 1 (by rfl) ⟨6375833, by rfl⟩ : syracuseStep 8501111 = 12751667) B12751667
theorem B10762145 : Blo 1116628 10762145 := bstep (se 2 (by rfl) ⟨4035804, by rfl⟩ : syracuseStep 10762145 = 8071609) B8071609
theorem B9680933 : Blo 1116628 9680933 := bstep (se 4 (by rfl) ⟨907587, by rfl⟩ : syracuseStep 9680933 = 1815175) B1815175
theorem B1259599 : Blo 1116628 1259599 := bstep (se 1 (by rfl) ⟨944699, by rfl⟩ : syracuseStep 1259599 = 1889399) B1889399
theorem B1259995 : Blo 1116628 1259995 := bstep (se 1 (by rfl) ⟨944996, by rfl⟩ : syracuseStep 1259995 = 1889993) B1889993
theorem B4241929 : Blo 1116628 4241929 := bstep (se 2 (by rfl) ⟨1590723, by rfl⟩ : syracuseStep 4241929 = 3181447) B3181447
theorem B1260463 : Blo 1116628 1260463 := bstep (se 1 (by rfl) ⟨945347, by rfl⟩ : syracuseStep 1260463 = 1890695) B1890695
theorem B2833339 : Blo 1116628 2833339 := bstep (se 1 (by rfl) ⟨2125004, by rfl⟩ : syracuseStep 2833339 = 4250009) B4250009
theorem B6372371 : Blo 1116628 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B8273099 : Blo 1116628 8273099 := bstep (se 1 (by rfl) ⟨6204824, by rfl⟩ : syracuseStep 8273099 = 12409649) B12409649
theorem B1817929 : Blo 1116628 1817929 := bstep (se 2 (by rfl) ⟨681723, by rfl⟩ : syracuseStep 1817929 = 1363447) B1363447
theorem B6372827 : Blo 1116628 6372827 := bstep (se 1 (by rfl) ⟨4779620, by rfl⟩ : syracuseStep 6372827 = 9559241) B9559241
theorem B6373079 : Blo 1116628 6373079 := bstep (se 1 (by rfl) ⟨4779809, by rfl⟩ : syracuseStep 6373079 = 9559619) B9559619
theorem B4538207 : Blo 1116628 4538207 := bstep (se 1 (by rfl) ⟨3403655, by rfl⟩ : syracuseStep 4538207 = 6807311) B6807311
theorem B4243387 : Blo 1116628 4243387 := bstep (se 1 (by rfl) ⟨3182540, by rfl⟩ : syracuseStep 4243387 = 6365081) B6365081
theorem B10731851 : Blo 1116628 10731851 := bstep (se 1 (by rfl) ⟨8048888, by rfl⟩ : syracuseStep 10731851 = 16097777) B16097777
theorem B3588457 : Blo 1116628 3588457 := bstep (se 2 (by rfl) ⟨1345671, by rfl⟩ : syracuseStep 3588457 = 2691343) B2691343
theorem B1884559 : Blo 1116628 1884559 := bstep (se 1 (by rfl) ⟨1413419, by rfl⟩ : syracuseStep 1884559 = 2826839) B2826839
theorem B4244177 : Blo 1116628 4244177 := bstep (se 2 (by rfl) ⟨1591566, by rfl⟩ : syracuseStep 4244177 = 3183133) B3183133
theorem B3588857 : Blo 1116628 3588857 := bstep (se 2 (by rfl) ⟨1345821, by rfl⟩ : syracuseStep 3588857 = 2691643) B2691643
theorem B1885241 : Blo 1116628 1885241 := bstep (se 2 (by rfl) ⟨706965, by rfl⟩ : syracuseStep 1885241 = 1413931) B1413931
theorem B4244633 : Blo 1116628 4244633 := bstep (se 2 (by rfl) ⟨1591737, by rfl⟩ : syracuseStep 4244633 = 3183475) B3183475
theorem B3589277 : Blo 1116628 3589277 := bstep (se 3 (by rfl) ⟨672989, by rfl⟩ : syracuseStep 3589277 = 1345979) B1345979
theorem B8504513 : Blo 1116628 8504513 := bstep (se 2 (by rfl) ⟨3189192, by rfl⟩ : syracuseStep 8504513 = 6378385) B6378385
theorem B2016619 : Blo 1116628 2016619 := bstep (se 1 (by rfl) ⟨1512464, by rfl⟩ : syracuseStep 2016619 = 3024929) B3024929
theorem B14337425 : Blo 1116628 14337425 := bstep (se 2 (by rfl) ⟨5376534, by rfl⟩ : syracuseStep 14337425 = 10753069) B10753069
theorem B5653961 : Blo 1116628 5653961 := bstep (se 2 (by rfl) ⟨2120235, by rfl⟩ : syracuseStep 5653961 = 4240471) B4240471
theorem B15287753 : Blo 1116628 15287753 := bstep (se 2 (by rfl) ⟨5732907, by rfl⟩ : syracuseStep 15287753 = 11465815) B11465815
theorem B2835931 : Blo 1116628 2835931 := bstep (se 1 (by rfl) ⟨2126948, by rfl⟩ : syracuseStep 2835931 = 4253897) B4253897
theorem B13616855 : Blo 1116628 13616855 := bstep (se 1 (by rfl) ⟨10212641, by rfl⟩ : syracuseStep 13616855 = 20425283) B20425283
theorem B1885943 : Blo 1116628 1885943 := bstep (se 1 (by rfl) ⟨1414457, by rfl⟩ : syracuseStep 1885943 = 2828915) B2828915
theorem B6375287 : Blo 1116628 6375287 := bstep (se 1 (by rfl) ⟨4781465, by rfl⟩ : syracuseStep 6375287 = 9562931) B9562931
theorem B1886287 : Blo 1116628 1886287 := bstep (se 1 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 1886287 = 2829431) B2829431
theorem B2836559 : Blo 1116628 2836559 := bstep (se 1 (by rfl) ⟨2127419, by rfl⟩ : syracuseStep 2836559 = 4254839) B4254839
theorem B5654609 : Blo 1116628 5654609 := bstep (se 2 (by rfl) ⟨2120478, by rfl⟩ : syracuseStep 5654609 = 4240957) B4240957
theorem B32229683 : Blo 1116628 32229683 := bstep (se 1 (by rfl) ⟨24172262, by rfl⟩ : syracuseStep 32229683 = 48344525) B48344525
theorem B1886537 : Blo 1116628 1886537 := bstep (se 2 (by rfl) ⟨707451, by rfl⟩ : syracuseStep 1886537 = 1414903) B1414903
theorem B1591817 : Blo 1116628 1591817 := bstep (se 2 (by rfl) ⟨596931, by rfl⟩ : syracuseStep 1591817 = 1193863) B1193863
theorem B6375995 : Blo 1116628 6375995 := bstep (se 1 (by rfl) ⟨4781996, by rfl⟩ : syracuseStep 6375995 = 9563993) B9563993
theorem B1591931 : Blo 1116628 1591931 := bstep (se 1 (by rfl) ⟨1193948, by rfl⟩ : syracuseStep 1591931 = 2387897) B2387897
theorem B4770515 : Blo 1116628 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B1886969 : Blo 1116628 1886969 := bstep (se 2 (by rfl) ⟨707613, by rfl⟩ : syracuseStep 1886969 = 1415227) B1415227
theorem B4770667 : Blo 1116628 4770667 := bstep (se 1 (by rfl) ⟨3578000, by rfl⟩ : syracuseStep 4770667 = 7156001) B7156001
theorem B2018191 : Blo 1116628 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B1592239 : Blo 1116628 1592239 := bstep (se 1 (by rfl) ⟨1194179, by rfl⟩ : syracuseStep 1592239 = 2388359) B2388359
theorem B1887151 : Blo 1116628 1887151 := bstep (se 1 (by rfl) ⟨1415363, by rfl⟩ : syracuseStep 1887151 = 2830727) B2830727
theorem B19123127 : Blo 1116628 19123127 := bstep (se 1 (by rfl) ⟨14342345, by rfl⟩ : syracuseStep 19123127 = 28684691) B28684691
theorem B1887239 : Blo 1116628 1887239 := bstep (se 1 (by rfl) ⟨1415429, by rfl⟩ : syracuseStep 1887239 = 2830859) B2830859
theorem B4246607 : Blo 1116628 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B4246775 : Blo 1116628 4246775 := bstep (se 1 (by rfl) ⟨3185081, by rfl⟩ : syracuseStep 4246775 = 6370163) B6370163
theorem B1592569 : Blo 1116628 1592569 := bstep (se 2 (by rfl) ⟨597213, by rfl⟩ : syracuseStep 1592569 = 1194427) B1194427
theorem B1887583 : Blo 1116628 1887583 := bstep (se 1 (by rfl) ⟨1415687, by rfl⟩ : syracuseStep 1887583 = 2831375) B2831375
theorem B19353005 : Blo 1116628 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B1887671 : Blo 1116628 1887671 := bstep (se 1 (by rfl) ⟨1415753, by rfl⟩ : syracuseStep 1887671 = 2831507) B2831507
theorem B1134535 : Blo 1116628 1134535 := bstep (se 1 (by rfl) ⟨850901, by rfl⟩ : syracuseStep 1134535 = 1701803) B1701803
theorem B1888265 : Blo 1116628 1888265 := bstep (se 2 (by rfl) ⟨708099, by rfl⟩ : syracuseStep 1888265 = 1416199) B1416199
theorem B8507429 : Blo 1116628 8507429 := bstep (se 4 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 8507429 = 1595143) B1595143
theorem B6803513 : Blo 1116628 6803513 := bstep (se 2 (by rfl) ⟨2551317, by rfl⟩ : syracuseStep 6803513 = 5102635) B5102635
theorem B1888427 : Blo 1116628 1888427 := bstep (se 1 (by rfl) ⟨1416320, by rfl⟩ : syracuseStep 1888427 = 2832641) B2832641
theorem B4247747 : Blo 1116628 4247747 := bstep (se 1 (by rfl) ⟨3185810, by rfl⟩ : syracuseStep 4247747 = 6371621) B6371621
theorem B1888825 : Blo 1116628 1888825 := bstep (se 2 (by rfl) ⟨708309, by rfl⟩ : syracuseStep 1888825 = 1416619) B1416619
theorem B4543073 : Blo 1116628 4543073 := bstep (se 2 (by rfl) ⟨1703652, by rfl⟩ : syracuseStep 4543073 = 3407305) B3407305
theorem B2871947 : Blo 1116628 2871947 := bstep (se 1 (by rfl) ⟨2153960, by rfl⟩ : syracuseStep 2871947 = 4307921) B4307921
theorem B1888967 : Blo 1116628 1888967 := bstep (se 1 (by rfl) ⟨1416725, by rfl⟩ : syracuseStep 1888967 = 2833451) B2833451
theorem B30593807 : Blo 1116628 30593807 := bstep (se 1 (by rfl) ⟨22945355, by rfl⟩ : syracuseStep 30593807 = 45890711) B45890711
theorem B20960017 : Blo 1116628 20960017 := bstep (se 2 (by rfl) ⟨7860006, by rfl⟩ : syracuseStep 20960017 = 15720013) B15720013
theorem B14504777 : Blo 1116628 14504777 := bstep (se 2 (by rfl) ⟨5439291, by rfl⟩ : syracuseStep 14504777 = 10878583) B10878583
theorem B1889129 : Blo 1116628 1889129 := bstep (se 2 (by rfl) ⟨708423, by rfl⟩ : syracuseStep 1889129 = 1416847) B1416847
theorem B1135711 : Blo 1116628 1135711 := bstep (se 1 (by rfl) ⟨851783, by rfl⟩ : syracuseStep 1135711 = 1703567) B1703567
theorem B4248733 : Blo 1116628 4248733 := bstep (se 3 (by rfl) ⟨796637, by rfl⟩ : syracuseStep 4248733 = 1593275) B1593275
theorem B16110809 : Blo 1116628 16110809 := bstep (se 2 (by rfl) ⟨6041553, by rfl⟩ : syracuseStep 16110809 = 12083107) B12083107
theorem B1889527 : Blo 1116628 1889527 := bstep (se 1 (by rfl) ⟨1417145, by rfl⟩ : syracuseStep 1889527 = 2834291) B2834291
theorem B1889723 : Blo 1116628 1889723 := bstep (se 1 (by rfl) ⟨1417292, by rfl⟩ : syracuseStep 1889723 = 2834585) B2834585
theorem B1889831 : Blo 1116628 1889831 := bstep (se 1 (by rfl) ⟨1417373, by rfl⟩ : syracuseStep 1889831 = 2834747) B2834747
theorem B3233377 : Blo 1116628 3233377 := bstep (se 2 (by rfl) ⟨1212516, by rfl⟩ : syracuseStep 3233377 = 2425033) B2425033
theorem B2512583 : Blo 1116628 2512583 := bstep (se 1 (by rfl) ⟨1884437, by rfl⟩ : syracuseStep 2512583 = 3768875) B3768875
theorem B12408535 : Blo 1116628 12408535 := bstep (se 1 (by rfl) ⟨9306401, by rfl⟩ : syracuseStep 12408535 = 18612803) B18612803
theorem B1890121 : Blo 1116628 1890121 := bstep (se 2 (by rfl) ⟨708795, by rfl⟩ : syracuseStep 1890121 = 1417591) B1417591
theorem B1890155 : Blo 1116628 1890155 := bstep (se 1 (by rfl) ⟨1417616, by rfl⟩ : syracuseStep 1890155 = 2835233) B2835233
theorem B29087693 : Blo 1116628 29087693 := bstep (se 3 (by rfl) ⟨5453942, by rfl⟩ : syracuseStep 29087693 = 10907885) B10907885
theorem B2873351 : Blo 1116628 2873351 := bstep (se 1 (by rfl) ⟨2155013, by rfl⟩ : syracuseStep 2873351 = 4310027) B4310027
theorem B1890553 : Blo 1116628 1890553 := bstep (se 2 (by rfl) ⟨708957, by rfl⟩ : syracuseStep 1890553 = 1417915) B1417915
theorem B1890823 : Blo 1116628 1890823 := bstep (se 1 (by rfl) ⟨1418117, by rfl⟩ : syracuseStep 1890823 = 2836235) B2836235
theorem B5659145 : Blo 1116628 5659145 := bstep (se 2 (by rfl) ⟨2122179, by rfl⟩ : syracuseStep 5659145 = 4244359) B4244359
theorem B2513447 : Blo 1116628 2513447 := bstep (se 1 (by rfl) ⟨1885085, by rfl⟩ : syracuseStep 2513447 = 3770171) B3770171
theorem B2120555 : Blo 1116628 2120555 := bstep (se 1 (by rfl) ⟨1590416, by rfl⟩ : syracuseStep 2120555 = 3180833) B3180833
theorem B2513771 : Blo 1116628 2513771 := bstep (se 1 (by rfl) ⟨1885328, by rfl⟩ : syracuseStep 2513771 = 3770657) B3770657
theorem B2513825 : Blo 1116628 2513825 := bstep (se 2 (by rfl) ⟨942684, by rfl⟩ : syracuseStep 2513825 = 1885369) B1885369
theorem B10738615 : Blo 1116628 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B1793063 : Blo 1116628 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B4086865 : Blo 1116628 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B2514167 : Blo 1116628 2514167 := bstep (se 1 (by rfl) ⟨1885625, by rfl⟩ : syracuseStep 2514167 = 3771251) B3771251
theorem B6446479 : Blo 1116628 6446479 := bstep (se 1 (by rfl) ⟨4834859, by rfl⟩ : syracuseStep 6446479 = 9669719) B9669719
theorem B2121223 : Blo 1116628 2121223 := bstep (se 1 (by rfl) ⟨1590917, by rfl⟩ : syracuseStep 2121223 = 3181835) B3181835
theorem B8052347 : Blo 1116628 8052347 := bstep (se 1 (by rfl) ⟨6039260, by rfl⟩ : syracuseStep 8052347 = 12078521) B12078521
theorem B1793659 : Blo 1116628 1793659 := bstep (se 1 (by rfl) ⟨1345244, by rfl⟩ : syracuseStep 1793659 = 2690489) B2690489
theorem B2514761 : Blo 1116628 2514761 := bstep (se 2 (by rfl) ⟨943035, by rfl⟩ : syracuseStep 2514761 = 1886071) B1886071
theorem B5660603 : Blo 1116628 5660603 := bstep (se 1 (by rfl) ⟨4245452, by rfl⟩ : syracuseStep 5660603 = 8490905) B8490905
theorem B4251649 : Blo 1116628 4251649 := bstep (se 2 (by rfl) ⟨1594368, by rfl⟩ : syracuseStep 4251649 = 3188737) B3188737
theorem B6381575 : Blo 1116628 6381575 := bstep (se 1 (by rfl) ⟨4786181, by rfl⟩ : syracuseStep 6381575 = 9572363) B9572363
theorem B1433639 : Blo 1116628 1433639 := bstep (se 1 (by rfl) ⟨1075229, by rfl⟩ : syracuseStep 1433639 = 2150459) B2150459
theorem B2121785 : Blo 1116628 2121785 := bstep (se 2 (by rfl) ⟨795669, by rfl⟩ : syracuseStep 2121785 = 1591339) B1591339
theorem B1794479 : Blo 1116628 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B9069079 : Blo 1116628 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B2515553 : Blo 1116628 2515553 := bstep (se 2 (by rfl) ⟨943332, by rfl⟩ : syracuseStep 2515553 = 1886665) B1886665
theorem B10216145 : Blo 1116628 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B4252409 : Blo 1116628 4252409 := bstep (se 2 (by rfl) ⟨1594653, by rfl⟩ : syracuseStep 4252409 = 3189307) B3189307
theorem B4842269 : Blo 1116628 4842269 := bstep (se 3 (by rfl) ⟨907925, by rfl⟩ : syracuseStep 4842269 = 1815851) B1815851
theorem B1794889 : Blo 1116628 1794889 := bstep (se 2 (by rfl) ⟨673083, by rfl⟩ : syracuseStep 1794889 = 1346167) B1346167
theorem B2548655 : Blo 1116628 2548655 := bstep (se 1 (by rfl) ⟨1911491, by rfl⟩ : syracuseStep 2548655 = 3822983) B3822983
theorem B2515895 : Blo 1116628 2515895 := bstep (se 1 (by rfl) ⟨1886921, by rfl⟩ : syracuseStep 2515895 = 3773843) B3773843
theorem B4776887 : Blo 1116628 4776887 := bstep (se 1 (by rfl) ⟨3582665, by rfl⟩ : syracuseStep 4776887 = 7165331) B7165331
theorem B5661899 : Blo 1116628 5661899 := bstep (se 1 (by rfl) ⟨4246424, by rfl⟩ : syracuseStep 5661899 = 8492849) B8492849
theorem B10216651 : Blo 1116628 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B9954575 : Blo 1116628 9954575 := bstep (se 1 (by rfl) ⟨7465931, by rfl⟩ : syracuseStep 9954575 = 14931863) B14931863
theorem B3827087 : Blo 1116628 3827087 := bstep (se 1 (by rfl) ⟨2870315, by rfl⟩ : syracuseStep 3827087 = 5740631) B5740631
theorem B12740003 : Blo 1116628 12740003 := bstep (se 1 (by rfl) ⟨9555002, by rfl⟩ : syracuseStep 12740003 = 19110005) B19110005
theorem B2123273 : Blo 1116628 2123273 := bstep (se 2 (by rfl) ⟨796227, by rfl⟩ : syracuseStep 2123273 = 1592455) B1592455
theorem B2516489 : Blo 1116628 2516489 := bstep (se 2 (by rfl) ⟨943683, by rfl⟩ : syracuseStep 2516489 = 1887367) B1887367
theorem B2385607 : Blo 1116628 2385607 := bstep (se 1 (by rfl) ⟨1789205, by rfl⟩ : syracuseStep 2385607 = 3578411) B3578411
theorem B9070379 : Blo 1116628 9070379 := bstep (se 1 (by rfl) ⟨6802784, by rfl⟩ : syracuseStep 9070379 = 13605569) B13605569
theorem B2516831 : Blo 1116628 2516831 := bstep (se 1 (by rfl) ⟨1887623, by rfl⟩ : syracuseStep 2516831 = 3775247) B3775247
theorem B34498457 : Blo 1116628 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B8480699 : Blo 1116628 8480699 := bstep (se 1 (by rfl) ⟨6360524, by rfl⟩ : syracuseStep 8480699 = 12721049) B12721049
theorem B2517011 : Blo 1116628 2517011 := bstep (se 1 (by rfl) ⟨1887758, by rfl⟩ : syracuseStep 2517011 = 3775517) B3775517
theorem B4253867 : Blo 1116628 4253867 := bstep (se 1 (by rfl) ⟨3190400, by rfl⟩ : syracuseStep 4253867 = 6380801) B6380801
theorem B2517353 : Blo 1116628 2517353 := bstep (se 2 (by rfl) ⟨944007, by rfl⟩ : syracuseStep 2517353 = 1888015) B1888015
theorem B2124139 : Blo 1116628 2124139 := bstep (se 1 (by rfl) ⟨1593104, by rfl⟩ : syracuseStep 2124139 = 3186209) B3186209
theorem B2124215 : Blo 1116628 2124215 := bstep (se 1 (by rfl) ⟨1593161, by rfl⟩ : syracuseStep 2124215 = 3186323) B3186323
theorem B9562657 : Blo 1116628 9562657 := bstep (se 2 (by rfl) ⟨3585996, by rfl⟩ : syracuseStep 9562657 = 7171993) B7171993
theorem B2517947 : Blo 1116628 2517947 := bstep (se 1 (by rfl) ⟨1888460, by rfl⟩ : syracuseStep 2517947 = 3776921) B3776921
theorem B2124731 : Blo 1116628 2124731 := bstep (se 1 (by rfl) ⟨1593548, by rfl⟩ : syracuseStep 2124731 = 3187097) B3187097
theorem B2518073 : Blo 1116628 2518073 := bstep (se 2 (by rfl) ⟨944277, by rfl⟩ : syracuseStep 2518073 = 1888555) B1888555
theorem B32304419 : Blo 1116628 32304419 := bstep (se 1 (by rfl) ⟨24228314, by rfl⟩ : syracuseStep 32304419 = 48456629) B48456629
theorem B2518415 : Blo 1116628 2518415 := bstep (se 1 (by rfl) ⟨1888811, by rfl⟩ : syracuseStep 2518415 = 3777623) B3777623
theorem B2125217 : Blo 1116628 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B2125369 : Blo 1116628 2125369 := bstep (se 2 (by rfl) ⟨797013, by rfl⟩ : syracuseStep 2125369 = 1594027) B1594027
theorem B2518739 : Blo 1116628 2518739 := bstep (se 1 (by rfl) ⟨1889054, by rfl⟩ : syracuseStep 2518739 = 3778109) B3778109
theorem B2125673 : Blo 1116628 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B8056847 : Blo 1116628 8056847 := bstep (se 1 (by rfl) ⟨6042635, by rfl⟩ : syracuseStep 8056847 = 12085271) B12085271
theorem B1274491 : Blo 1116628 1274491 := bstep (se 1 (by rfl) ⟨955868, by rfl⟩ : syracuseStep 1274491 = 1911737) B1911737
theorem B2519675 : Blo 1116628 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B6812369 : Blo 1116628 6812369 := bstep (se 2 (by rfl) ⟨2554638, by rfl⟩ : syracuseStep 6812369 = 5109277) B5109277
theorem B2519801 : Blo 1116628 2519801 := bstep (se 2 (by rfl) ⟨944925, by rfl⟩ : syracuseStep 2519801 = 1889851) B1889851
theorem B2520071 : Blo 1116628 2520071 := bstep (se 1 (by rfl) ⟨1890053, by rfl⟩ : syracuseStep 2520071 = 3780107) B3780107
theorem B2520143 : Blo 1116628 2520143 := bstep (se 1 (by rfl) ⟨1890107, by rfl⟩ : syracuseStep 2520143 = 3780215) B3780215
theorem B4781227 : Blo 1116628 4781227 := bstep (se 1 (by rfl) ⟨3585920, by rfl⟩ : syracuseStep 4781227 = 7171841) B7171841
theorem B2422235 : Blo 1116628 2422235 := bstep (se 1 (by rfl) ⟨1816676, by rfl⟩ : syracuseStep 2422235 = 3633353) B3633353
theorem B2520539 : Blo 1116628 2520539 := bstep (se 1 (by rfl) ⟨1890404, by rfl⟩ : syracuseStep 2520539 = 3780809) B3780809
theorem B2684539 : Blo 1116628 2684539 := bstep (se 1 (by rfl) ⟨2013404, by rfl⟩ : syracuseStep 2684539 = 4026809) B4026809
theorem B12089249 : Blo 1116628 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B2521007 : Blo 1116628 2521007 := bstep (se 1 (by rfl) ⟨1890755, by rfl⟩ : syracuseStep 2521007 = 3781511) B3781511
theorem B1210447 : Blo 1116628 1210447 := bstep (se 1 (by rfl) ⟨907835, by rfl⟩ : syracuseStep 1210447 = 1815671) B1815671
theorem B2521259 : Blo 1116628 2521259 := bstep (se 1 (by rfl) ⟨1890944, by rfl⟩ : syracuseStep 2521259 = 3781889) B3781889
theorem B5667083 : Blo 1116628 5667083 := bstep (se 1 (by rfl) ⟨4250312, by rfl⟩ : syracuseStep 5667083 = 8500625) B8500625
theorem B5372675 : Blo 1116628 5372675 := bstep (se 1 (by rfl) ⟨4029506, by rfl⟩ : syracuseStep 5372675 = 8059013) B8059013
theorem B1702921 : Blo 1116628 1702921 := bstep (se 2 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 1702921 = 1277191) B1277191
theorem B6814799 : Blo 1116628 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B2391211 : Blo 1116628 2391211 := bstep (se 1 (by rfl) ⟨1793408, by rfl⟩ : syracuseStep 2391211 = 3586817) B3586817
theorem B1703263 : Blo 1116628 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B5668541 : Blo 1116628 5668541 := bstep (se 3 (by rfl) ⟨1062851, by rfl⟩ : syracuseStep 5668541 = 2125703) B2125703
theorem B5668703 : Blo 1116628 5668703 := bstep (se 1 (by rfl) ⟨4251527, by rfl⟩ : syracuseStep 5668703 = 8503055) B8503055
theorem B5668865 : Blo 1116628 5668865 := bstep (se 2 (by rfl) ⟨2125824, by rfl⟩ : syracuseStep 5668865 = 4251649) B4251649
theorem B6455717 : Blo 1116628 6455717 := bstep (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) B1210447
theorem B4784609 : Blo 1116628 4784609 := bstep (se 2 (by rfl) ⟨1794228, by rfl⟩ : syracuseStep 4784609 = 3588457) B3588457
theorem B2392571 : Blo 1116628 2392571 := bstep (se 1 (by rfl) ⟨1794428, by rfl⟩ : syracuseStep 2392571 = 3588857) B3588857
theorem B12092105 : Blo 1116628 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B5669675 : Blo 1116628 5669675 := bstep (se 1 (by rfl) ⟨4252256, by rfl⟩ : syracuseStep 5669675 = 8504513) B8504513
theorem B3769307 : Blo 1116628 3769307 := bstep (se 1 (by rfl) ⟨2826980, by rfl⟩ : syracuseStep 3769307 = 5653961) B5653961
theorem B10191835 : Blo 1116628 10191835 := bstep (se 1 (by rfl) ⟨7643876, by rfl⟩ : syracuseStep 10191835 = 15287753) B15287753
theorem B3769469 : Blo 1116628 3769469 := bstep (se 3 (by rfl) ⟨706775, by rfl⟩ : syracuseStep 3769469 = 1413551) B1413551
theorem B4785277 : Blo 1116628 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B9077903 : Blo 1116628 9077903 := bstep (se 1 (by rfl) ⟨6808427, by rfl⟩ : syracuseStep 9077903 = 13616855) B13616855
theorem B65406149 : Blo 1116628 65406149 := bstep (se 4 (by rfl) ⟨6131826, by rfl⟩ : syracuseStep 65406149 = 12263653) B12263653
theorem B3769577 : Blo 1116628 3769577 := bstep (se 2 (by rfl) ⟨1413591, by rfl⟩ : syracuseStep 3769577 = 2827183) B2827183
theorem B3769739 : Blo 1116628 3769739 := bstep (se 1 (by rfl) ⟨2827304, by rfl⟩ : syracuseStep 3769739 = 5654609) B5654609
theorem B3180343 : Blo 1116628 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B12748751 : Blo 1116628 12748751 := bstep (se 1 (by rfl) ⟨9561563, by rfl⟩ : syracuseStep 12748751 = 19123127) B19123127
theorem B3180809 : Blo 1116628 3180809 := bstep (se 2 (by rfl) ⟨1192803, by rfl⟩ : syracuseStep 3180809 = 2385607) B2385607
theorem B1116667 : Blo 1116628 1116667 := bstep (se 1 (by rfl) ⟨837500, by rfl⟩ : syracuseStep 1116667 = 1675001) B1675001
theorem B1116735 : Blo 1116628 1116735 := bstep (se 1 (by rfl) ⟨837551, by rfl⟩ : syracuseStep 1116735 = 1675103) B1675103
theorem B1116743 : Blo 1116628 1116743 := bstep (se 1 (by rfl) ⟨837557, by rfl⟩ : syracuseStep 1116743 = 1675115) B1675115
theorem B5671619 : Blo 1116628 5671619 := bstep (se 1 (by rfl) ⟨4253714, by rfl⟩ : syracuseStep 5671619 = 8507429) B8507429
theorem B1116895 : Blo 1116628 1116895 := bstep (se 1 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 1116895 = 1675343) B1675343
theorem B1116975 : Blo 1116628 1116975 := bstep (se 1 (by rfl) ⟨837731, by rfl⟩ : syracuseStep 1116975 = 1675463) B1675463
theorem B8063879 : Blo 1116628 8063879 := bstep (se 1 (by rfl) ⟨6047909, by rfl⟩ : syracuseStep 8063879 = 12095819) B12095819
theorem B1117083 : Blo 1116628 1117083 := bstep (se 1 (by rfl) ⟨837812, by rfl⟩ : syracuseStep 1117083 = 1675625) B1675625
theorem B1117135 : Blo 1116628 1117135 := bstep (se 1 (by rfl) ⟨837851, by rfl⟩ : syracuseStep 1117135 = 1675703) B1675703
theorem B1117159 : Blo 1116628 1117159 := bstep (se 1 (by rfl) ⟨837869, by rfl⟩ : syracuseStep 1117159 = 1675739) B1675739
theorem B16124993 : Blo 1116628 16124993 := bstep (se 2 (by rfl) ⟨6046872, by rfl⟩ : syracuseStep 16124993 = 12093745) B12093745
theorem B9571405 : Blo 1116628 9571405 := bstep (se 3 (by rfl) ⟨1794638, by rfl⟩ : syracuseStep 9571405 = 3589277) B3589277
theorem B9669851 : Blo 1116628 9669851 := bstep (se 1 (by rfl) ⟨7252388, by rfl⟩ : syracuseStep 9669851 = 14504777) B14504777
theorem B1117471 : Blo 1116628 1117471 := bstep (se 1 (by rfl) ⟨838103, by rfl⟩ : syracuseStep 1117471 = 1676207) B1676207
theorem B1117531 : Blo 1116628 1117531 := bstep (se 1 (by rfl) ⟨838148, by rfl⟩ : syracuseStep 1117531 = 1676297) B1676297
theorem B1117551 : Blo 1116628 1117551 := bstep (se 1 (by rfl) ⟨838163, by rfl⟩ : syracuseStep 1117551 = 1676327) B1676327
theorem B12750209 : Blo 1116628 12750209 := bstep (se 2 (by rfl) ⟨4781328, by rfl⟩ : syracuseStep 12750209 = 9562657) B9562657
theorem B1117607 : Blo 1116628 1117607 := bstep (se 1 (by rfl) ⟨838205, by rfl⟩ : syracuseStep 1117607 = 1676411) B1676411
theorem B1117691 : Blo 1116628 1117691 := bstep (se 1 (by rfl) ⟨838268, by rfl⟩ : syracuseStep 1117691 = 1676537) B1676537
theorem B7179785 : Blo 1116628 7179785 := bstep (se 2 (by rfl) ⟨2692419, by rfl⟩ : syracuseStep 7179785 = 5384839) B5384839
theorem B1117759 : Blo 1116628 1117759 := bstep (se 1 (by rfl) ⟨838319, by rfl⟩ : syracuseStep 1117759 = 1676639) B1676639
theorem B1117767 : Blo 1116628 1117767 := bstep (se 1 (by rfl) ⟨838325, by rfl⟩ : syracuseStep 1117767 = 1676651) B1676651
theorem B10751687 : Blo 1116628 10751687 := bstep (se 1 (by rfl) ⟨8063765, by rfl⟩ : syracuseStep 10751687 = 16127531) B16127531
theorem B1117919 : Blo 1116628 1117919 := bstep (se 1 (by rfl) ⟨838439, by rfl⟩ : syracuseStep 1117919 = 1676879) B1676879
theorem B1675049 : Blo 1116628 1675049 := bstep (se 2 (by rfl) ⟨628143, by rfl⟩ : syracuseStep 1675049 = 1256287) B1256287
theorem B1675055 : Blo 1116628 1675055 := bstep (se 1 (by rfl) ⟨1256291, by rfl⟩ : syracuseStep 1675055 = 2512583) B2512583
theorem B1117999 : Blo 1116628 1117999 := bstep (se 1 (by rfl) ⟨838499, by rfl⟩ : syracuseStep 1117999 = 1676999) B1676999
theorem B6360889 : Blo 1116628 6360889 := bstep (se 2 (by rfl) ⟨2385333, by rfl⟩ : syracuseStep 6360889 = 4770667) B4770667
theorem B2690921 : Blo 1116628 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B1118107 : Blo 1116628 1118107 := bstep (se 1 (by rfl) ⟨838580, by rfl⟩ : syracuseStep 1118107 = 1677161) B1677161
theorem B1118159 : Blo 1116628 1118159 := bstep (se 1 (by rfl) ⟨838619, by rfl⟩ : syracuseStep 1118159 = 1677239) B1677239
theorem B1118183 : Blo 1116628 1118183 := bstep (se 1 (by rfl) ⟨838637, by rfl⟩ : syracuseStep 1118183 = 1677275) B1677275
theorem B1675529 : Blo 1116628 1675529 := bstep (se 2 (by rfl) ⟨628323, by rfl⟩ : syracuseStep 1675529 = 1256647) B1256647
theorem B1118495 : Blo 1116628 1118495 := bstep (se 1 (by rfl) ⟨838871, by rfl⟩ : syracuseStep 1118495 = 1677743) B1677743
theorem B3772763 : Blo 1116628 3772763 := bstep (se 1 (by rfl) ⟨2829572, by rfl⟩ : syracuseStep 3772763 = 5659145) B5659145
theorem B1118555 : Blo 1116628 1118555 := bstep (se 1 (by rfl) ⟨838916, by rfl⟩ : syracuseStep 1118555 = 1677833) B1677833
theorem B1675631 : Blo 1116628 1675631 := bstep (se 1 (by rfl) ⟨1256723, by rfl⟩ : syracuseStep 1675631 = 2513447) B2513447
theorem B1118575 : Blo 1116628 1118575 := bstep (se 1 (by rfl) ⟨838931, by rfl⟩ : syracuseStep 1118575 = 1677863) B1677863
theorem B9572741 : Blo 1116628 9572741 := bstep (se 4 (by rfl) ⟨897444, by rfl⟩ : syracuseStep 9572741 = 1794889) B1794889
theorem B1118631 : Blo 1116628 1118631 := bstep (se 1 (by rfl) ⟨838973, by rfl⟩ : syracuseStep 1118631 = 1677947) B1677947
theorem B1118715 : Blo 1116628 1118715 := bstep (se 1 (by rfl) ⟨839036, by rfl⟩ : syracuseStep 1118715 = 1678073) B1678073
theorem B1118783 : Blo 1116628 1118783 := bstep (se 1 (by rfl) ⟨839087, by rfl⟩ : syracuseStep 1118783 = 1678175) B1678175
theorem B1413703 : Blo 1116628 1413703 := bstep (se 1 (by rfl) ⟨1060277, by rfl⟩ : syracuseStep 1413703 = 2120555) B2120555
theorem B1675847 : Blo 1116628 1675847 := bstep (se 1 (by rfl) ⟨1256885, by rfl⟩ : syracuseStep 1675847 = 2513771) B2513771
theorem B1118791 : Blo 1116628 1118791 := bstep (se 1 (by rfl) ⟨839093, by rfl⟩ : syracuseStep 1118791 = 1678187) B1678187
theorem B1675883 : Blo 1116628 1675883 := bstep (se 1 (by rfl) ⟨1256912, by rfl⟩ : syracuseStep 1675883 = 2513825) B2513825
theorem B2691767 : Blo 1116628 2691767 := bstep (se 1 (by rfl) ⟨2018825, by rfl⟩ : syracuseStep 2691767 = 4037651) B4037651
theorem B1118943 : Blo 1116628 1118943 := bstep (se 1 (by rfl) ⟨839207, by rfl⟩ : syracuseStep 1118943 = 1678415) B1678415
theorem B1119023 : Blo 1116628 1119023 := bstep (se 1 (by rfl) ⟨839267, by rfl⟩ : syracuseStep 1119023 = 1678535) B1678535
theorem B1676111 : Blo 1116628 1676111 := bstep (se 1 (by rfl) ⟨1257083, by rfl⟩ : syracuseStep 1676111 = 2514167) B2514167
theorem B1119131 : Blo 1116628 1119131 := bstep (se 1 (by rfl) ⟨839348, by rfl⟩ : syracuseStep 1119131 = 1678697) B1678697
theorem B1119183 : Blo 1116628 1119183 := bstep (se 1 (by rfl) ⟨839387, by rfl⟩ : syracuseStep 1119183 = 1678775) B1678775
theorem B1119207 : Blo 1116628 1119207 := bstep (se 1 (by rfl) ⟨839405, by rfl⟩ : syracuseStep 1119207 = 1678811) B1678811
theorem B1676507 : Blo 1116628 1676507 := bstep (se 1 (by rfl) ⟨1257380, by rfl⟩ : syracuseStep 1676507 = 2514761) B2514761
theorem B1512713 : Blo 1116628 1512713 := bstep (se 2 (by rfl) ⟨567267, by rfl⟩ : syracuseStep 1512713 = 1134535) B1134535
theorem B1119519 : Blo 1116628 1119519 := bstep (se 1 (by rfl) ⟨839639, by rfl⟩ : syracuseStep 1119519 = 1679279) B1679279
theorem B3773735 : Blo 1116628 3773735 := bstep (se 1 (by rfl) ⟨2830301, by rfl⟩ : syracuseStep 3773735 = 5660603) B5660603
theorem B1119579 : Blo 1116628 1119579 := bstep (se 1 (by rfl) ⟨839684, by rfl⟩ : syracuseStep 1119579 = 1679369) B1679369
theorem B1119599 : Blo 1116628 1119599 := bstep (se 1 (by rfl) ⟨839699, by rfl⟩ : syracuseStep 1119599 = 1679399) B1679399
theorem B1414523 : Blo 1116628 1414523 := bstep (se 1 (by rfl) ⟨1060892, by rfl⟩ : syracuseStep 1414523 = 2121785) B2121785
theorem B1676681 : Blo 1116628 1676681 := bstep (se 2 (by rfl) ⟨628755, by rfl⟩ : syracuseStep 1676681 = 1257511) B1257511
theorem B1119655 : Blo 1116628 1119655 := bstep (se 1 (by rfl) ⟨839741, by rfl⟩ : syracuseStep 1119655 = 1679483) B1679483
theorem B1119739 : Blo 1116628 1119739 := bstep (se 1 (by rfl) ⟨839804, by rfl⟩ : syracuseStep 1119739 = 1679609) B1679609
theorem B1119807 : Blo 1116628 1119807 := bstep (se 1 (by rfl) ⟨839855, by rfl⟩ : syracuseStep 1119807 = 1679711) B1679711
theorem B1119815 : Blo 1116628 1119815 := bstep (se 1 (by rfl) ⟨839861, by rfl⟩ : syracuseStep 1119815 = 1679723) B1679723
theorem B1119967 : Blo 1116628 1119967 := bstep (se 1 (by rfl) ⟨839975, by rfl⟩ : syracuseStep 1119967 = 1679951) B1679951
theorem B1677035 : Blo 1116628 1677035 := bstep (se 1 (by rfl) ⟨1257776, by rfl⟩ : syracuseStep 1677035 = 2515553) B2515553
theorem B21796613 : Blo 1116628 21796613 := bstep (se 4 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 21796613 = 4086865) B4086865
theorem B1120047 : Blo 1116628 1120047 := bstep (se 1 (by rfl) ⟨840035, by rfl⟩ : syracuseStep 1120047 = 1680071) B1680071
theorem B1120155 : Blo 1116628 1120155 := bstep (se 1 (by rfl) ⟨840116, by rfl⟩ : syracuseStep 1120155 = 1680233) B1680233
theorem B1677263 : Blo 1116628 1677263 := bstep (se 1 (by rfl) ⟨1257947, by rfl⟩ : syracuseStep 1677263 = 2515895) B2515895
theorem B3184591 : Blo 1116628 3184591 := bstep (se 1 (by rfl) ⟨2388443, by rfl⟩ : syracuseStep 3184591 = 4776887) B4776887
theorem B1120207 : Blo 1116628 1120207 := bstep (se 1 (by rfl) ⟨840155, by rfl⟩ : syracuseStep 1120207 = 1680311) B1680311
theorem B1120231 : Blo 1116628 1120231 := bstep (se 1 (by rfl) ⟨840173, by rfl⟩ : syracuseStep 1120231 = 1680347) B1680347
theorem B3774599 : Blo 1116628 3774599 := bstep (se 1 (by rfl) ⟨2830949, by rfl⟩ : syracuseStep 3774599 = 5661899) B5661899
theorem B12753125 : Blo 1116628 12753125 := bstep (se 4 (by rfl) ⟨1195605, by rfl⟩ : syracuseStep 12753125 = 2391211) B2391211
theorem B8493335 : Blo 1116628 8493335 := bstep (se 1 (by rfl) ⟨6370001, by rfl⟩ : syracuseStep 8493335 = 12740003) B12740003
theorem B1120543 : Blo 1116628 1120543 := bstep (se 1 (by rfl) ⟨840407, by rfl⟩ : syracuseStep 1120543 = 1680815) B1680815
theorem B1677659 : Blo 1116628 1677659 := bstep (se 1 (by rfl) ⟨1258244, by rfl⟩ : syracuseStep 1677659 = 2516489) B2516489
theorem B1120603 : Blo 1116628 1120603 := bstep (se 1 (by rfl) ⟨840452, by rfl⟩ : syracuseStep 1120603 = 1680905) B1680905
theorem B1120623 : Blo 1116628 1120623 := bstep (se 1 (by rfl) ⟨840467, by rfl⟩ : syracuseStep 1120623 = 1680935) B1680935
theorem B1677887 : Blo 1116628 1677887 := bstep (se 1 (by rfl) ⟨1258415, by rfl⟩ : syracuseStep 1677887 = 2516831) B2516831
theorem B1678007 : Blo 1116628 1678007 := bstep (se 1 (by rfl) ⟨1258505, by rfl⟩ : syracuseStep 1678007 = 2517011) B2517011
theorem B1678235 : Blo 1116628 1678235 := bstep (se 1 (by rfl) ⟨1258676, by rfl⟩ : syracuseStep 1678235 = 2517353) B2517353
theorem B1514395 : Blo 1116628 1514395 := bstep (se 1 (by rfl) ⟨1135796, by rfl⟩ : syracuseStep 1514395 = 2271593) B2271593
theorem B4594603 : Blo 1116628 4594603 := bstep (se 1 (by rfl) ⟨3445952, by rfl⟩ : syracuseStep 4594603 = 6891905) B6891905
theorem B1416143 : Blo 1116628 1416143 := bstep (se 1 (by rfl) ⟨1062107, by rfl⟩ : syracuseStep 1416143 = 2124215) B2124215
theorem B10755301 : Blo 1116628 10755301 := bstep (se 4 (by rfl) ⟨1008309, by rfl⟩ : syracuseStep 10755301 = 2016619) B2016619
theorem B1678631 : Blo 1116628 1678631 := bstep (se 1 (by rfl) ⟨1258973, by rfl⟩ : syracuseStep 1678631 = 2517947) B2517947
theorem B3775841 : Blo 1116628 3775841 := bstep (se 2 (by rfl) ⟨1415940, by rfl⟩ : syracuseStep 3775841 = 2831881) B2831881
theorem B1678715 : Blo 1116628 1678715 := bstep (se 1 (by rfl) ⟨1259036, by rfl⟩ : syracuseStep 1678715 = 2518073) B2518073
theorem B9674149 : Blo 1116628 9674149 := bstep (se 4 (by rfl) ⟨906951, by rfl⟩ : syracuseStep 9674149 = 1813903) B1813903
theorem B3579385 : Blo 1116628 3579385 := bstep (se 2 (by rfl) ⟨1342269, by rfl⟩ : syracuseStep 3579385 = 2684539) B2684539
theorem B1678841 : Blo 1116628 1678841 := bstep (se 2 (by rfl) ⟨629565, by rfl⟩ : syracuseStep 1678841 = 1259131) B1259131
theorem B21536279 : Blo 1116628 21536279 := bstep (se 1 (by rfl) ⟨16152209, by rfl⟩ : syracuseStep 21536279 = 32304419) B32304419
theorem B40771147 : Blo 1116628 40771147 := bstep (se 1 (by rfl) ⟨30578360, by rfl⟩ : syracuseStep 40771147 = 61156721) B61156721
theorem B1678943 : Blo 1116628 1678943 := bstep (se 1 (by rfl) ⟨1259207, by rfl⟩ : syracuseStep 1678943 = 2518415) B2518415
theorem B1679159 : Blo 1116628 1679159 := bstep (se 1 (by rfl) ⟨1259369, by rfl⟩ : syracuseStep 1679159 = 2518739) B2518739
theorem B3022649 : Blo 1116628 3022649 := bstep (se 2 (by rfl) ⟨1133493, by rfl⟩ : syracuseStep 3022649 = 2266987) B2266987
theorem B1417115 : Blo 1116628 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B10756145 : Blo 1116628 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B1679465 : Blo 1116628 1679465 := bstep (se 2 (by rfl) ⟨629799, by rfl⟩ : syracuseStep 1679465 = 1259599) B1259599
theorem B1679783 : Blo 1116628 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B1679867 : Blo 1116628 1679867 := bstep (se 1 (by rfl) ⟨1259900, by rfl⟩ : syracuseStep 1679867 = 2519801) B2519801
theorem B17244677 : Blo 1116628 17244677 := bstep (se 4 (by rfl) ⟨1616688, by rfl⟩ : syracuseStep 17244677 = 3233377) B3233377
theorem B2826859 : Blo 1116628 2826859 := bstep (se 1 (by rfl) ⟨2120144, by rfl⟩ : syracuseStep 2826859 = 4240289) B4240289
theorem B1679993 : Blo 1116628 1679993 := bstep (se 2 (by rfl) ⟨629997, by rfl⟩ : syracuseStep 1679993 = 1259995) B1259995
theorem B1680047 : Blo 1116628 1680047 := bstep (se 1 (by rfl) ⟨1260035, by rfl⟩ : syracuseStep 1680047 = 2520071) B2520071
theorem B1680095 : Blo 1116628 1680095 := bstep (se 1 (by rfl) ⟨1260071, by rfl⟩ : syracuseStep 1680095 = 2520143) B2520143
theorem B2827163 : Blo 1116628 2827163 := bstep (se 1 (by rfl) ⟨2120372, by rfl⟩ : syracuseStep 2827163 = 4240745) B4240745
theorem B1614823 : Blo 1116628 1614823 := bstep (se 1 (by rfl) ⟨1211117, by rfl⟩ : syracuseStep 1614823 = 2422235) B2422235
theorem B1680359 : Blo 1116628 1680359 := bstep (se 1 (by rfl) ⟨1260269, by rfl⟩ : syracuseStep 1680359 = 2520539) B2520539
theorem B1680617 : Blo 1116628 1680617 := bstep (se 2 (by rfl) ⟨630231, by rfl⟩ : syracuseStep 1680617 = 1260463) B1260463
theorem B2827507 : Blo 1116628 2827507 := bstep (se 1 (by rfl) ⟨2120630, by rfl⟩ : syracuseStep 2827507 = 4241261) B4241261
theorem B3777785 : Blo 1116628 3777785 := bstep (se 2 (by rfl) ⟨1416669, by rfl⟩ : syracuseStep 3777785 = 2833339) B2833339
theorem B1680671 : Blo 1116628 1680671 := bstep (se 1 (by rfl) ⟨1260503, by rfl⟩ : syracuseStep 1680671 = 2521007) B2521007
theorem B2270561 : Blo 1116628 2270561 := bstep (se 2 (by rfl) ⟨851460, by rfl⟩ : syracuseStep 2270561 = 1702921) B1702921
theorem B1680839 : Blo 1116628 1680839 := bstep (se 1 (by rfl) ⟨1260629, by rfl⟩ : syracuseStep 1680839 = 2521259) B2521259
theorem B3778055 : Blo 1116628 3778055 := bstep (se 1 (by rfl) ⟨2833541, by rfl⟩ : syracuseStep 3778055 = 5667083) B5667083
theorem B2271017 : Blo 1116628 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B3581783 : Blo 1116628 3581783 := bstep (se 1 (by rfl) ⟨2686337, by rfl⟩ : syracuseStep 3581783 = 5372675) B5372675
theorem B8595305 : Blo 1116628 8595305 := bstep (se 2 (by rfl) ⟨3223239, by rfl⟩ : syracuseStep 8595305 = 6446479) B6446479
theorem B2828297 : Blo 1116628 2828297 := bstep (se 2 (by rfl) ⟨1060611, by rfl⟩ : syracuseStep 2828297 = 2121223) B2121223
theorem B5515399 : Blo 1116628 5515399 := bstep (se 1 (by rfl) ⟨4136549, by rfl⟩ : syracuseStep 5515399 = 8273099) B8273099
theorem B3779027 : Blo 1116628 3779027 := bstep (se 1 (by rfl) ⟨2834270, by rfl⟩ : syracuseStep 3779027 = 5668541) B5668541
theorem B3025471 : Blo 1116628 3025471 := bstep (se 1 (by rfl) ⟨2269103, by rfl⟩ : syracuseStep 3025471 = 4538207) B4538207
theorem B3779135 : Blo 1116628 3779135 := bstep (se 1 (by rfl) ⟨2834351, by rfl⟩ : syracuseStep 3779135 = 5668703) B5668703
theorem B7154567 : Blo 1116628 7154567 := bstep (se 1 (by rfl) ⟨5365925, by rfl⟩ : syracuseStep 7154567 = 10731851) B10731851
theorem B2829451 : Blo 1116628 2829451 := bstep (se 1 (by rfl) ⟨2122088, by rfl⟩ : syracuseStep 2829451 = 4244177) B4244177
theorem B1256827 : Blo 1116628 1256827 := bstep (se 1 (by rfl) ⟨942620, by rfl⟩ : syracuseStep 1256827 = 1885241) B1885241
theorem B2829755 : Blo 1116628 2829755 := bstep (se 1 (by rfl) ⟨2122316, by rfl⟩ : syracuseStep 2829755 = 4244633) B4244633
theorem B3190367 : Blo 1116628 3190367 := bstep (se 1 (by rfl) ⟨2392775, by rfl⟩ : syracuseStep 3190367 = 4785551) B4785551
theorem B1257295 : Blo 1116628 1257295 := bstep (se 1 (by rfl) ⟨942971, by rfl⟩ : syracuseStep 1257295 = 1885943) B1885943
theorem B1257691 : Blo 1116628 1257691 := bstep (se 1 (by rfl) ⟨943268, by rfl⟩ : syracuseStep 1257691 = 1886537) B1886537
theorem B3780971 : Blo 1116628 3780971 := bstep (se 1 (by rfl) ⟨2835728, by rfl⟩ : syracuseStep 3780971 = 5671457) B5671457
theorem B1257979 : Blo 1116628 1257979 := bstep (se 1 (by rfl) ⟨943484, by rfl⟩ : syracuseStep 1257979 = 1886969) B1886969
theorem B12726881 : Blo 1116628 12726881 := bstep (se 2 (by rfl) ⟨4772580, by rfl⟩ : syracuseStep 12726881 = 9545161) B9545161
theorem B3781241 : Blo 1116628 3781241 := bstep (se 2 (by rfl) ⟨1417965, by rfl⟩ : syracuseStep 3781241 = 2835931) B2835931
theorem B1258159 : Blo 1116628 1258159 := bstep (se 1 (by rfl) ⟨943619, by rfl⟩ : syracuseStep 1258159 = 1887239) B1887239
theorem B2831071 : Blo 1116628 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B2831183 : Blo 1116628 2831183 := bstep (se 1 (by rfl) ⟨2123387, by rfl⟩ : syracuseStep 2831183 = 4246775) B4246775
theorem B1258447 : Blo 1116628 1258447 := bstep (se 1 (by rfl) ⟨943835, by rfl⟩ : syracuseStep 1258447 = 1887671) B1887671
theorem B3584999 : Blo 1116628 3584999 := bstep (se 1 (by rfl) ⟨2688749, by rfl⟩ : syracuseStep 3584999 = 5377499) B5377499
theorem B2012447 : Blo 1116628 2012447 := bstep (se 1 (by rfl) ⟨1509335, by rfl⟩ : syracuseStep 2012447 = 3018671) B3018671
theorem B1258843 : Blo 1116628 1258843 := bstep (se 1 (by rfl) ⟨944132, by rfl⟩ : syracuseStep 1258843 = 1888265) B1888265
theorem B12760415 : Blo 1116628 12760415 := bstep (se 1 (by rfl) ⟨9570311, by rfl⟩ : syracuseStep 12760415 = 19140623) B19140623
theorem B4535675 : Blo 1116628 4535675 := bstep (se 1 (by rfl) ⟨3401756, by rfl⟩ : syracuseStep 4535675 = 6803513) B6803513
theorem B1258951 : Blo 1116628 1258951 := bstep (se 1 (by rfl) ⟨944213, by rfl⟩ : syracuseStep 1258951 = 1888427) B1888427
theorem B2831831 : Blo 1116628 2831831 := bstep (se 1 (by rfl) ⟨2123873, by rfl⟩ : syracuseStep 2831831 = 4247747) B4247747
theorem B3028715 : Blo 1116628 3028715 := bstep (se 1 (by rfl) ⟨2271536, by rfl⟩ : syracuseStep 3028715 = 4543073) B4543073
theorem B1259311 : Blo 1116628 1259311 := bstep (se 1 (by rfl) ⟨944483, by rfl⟩ : syracuseStep 1259311 = 1888967) B1888967
theorem B2832185 : Blo 1116628 2832185 := bstep (se 2 (by rfl) ⟨1062069, by rfl⟩ : syracuseStep 2832185 = 2124139) B2124139
theorem B20395871 : Blo 1116628 20395871 := bstep (se 1 (by rfl) ⟨15296903, by rfl⟩ : syracuseStep 20395871 = 30593807) B30593807
theorem B1259419 : Blo 1116628 1259419 := bstep (se 1 (by rfl) ⟨944564, by rfl⟩ : syracuseStep 1259419 = 1889129) B1889129
theorem B1259815 : Blo 1116628 1259815 := bstep (se 1 (by rfl) ⟨944861, by rfl⟩ : syracuseStep 1259815 = 1889723) B1889723
theorem B1259887 : Blo 1116628 1259887 := bstep (se 1 (by rfl) ⟨944915, by rfl⟩ : syracuseStep 1259887 = 1889831) B1889831
theorem B4241915 : Blo 1116628 4241915 := bstep (se 1 (by rfl) ⟨3181436, by rfl⟩ : syracuseStep 4241915 = 6362873) B6362873
theorem B1260103 : Blo 1116628 1260103 := bstep (se 1 (by rfl) ⟨945077, by rfl⟩ : syracuseStep 1260103 = 1890155) B1890155
theorem B3586639 : Blo 1116628 3586639 := bstep (se 1 (by rfl) ⟨2689979, by rfl⟩ : syracuseStep 3586639 = 5379959) B5379959
theorem B2014183 : Blo 1116628 2014183 := bstep (se 1 (by rfl) ⟨1510637, by rfl⟩ : syracuseStep 2014183 = 3021275) B3021275
theorem B4242719 : Blo 1116628 4242719 := bstep (se 1 (by rfl) ⟨3182039, by rfl⟩ : syracuseStep 4242719 = 6364079) B6364079
theorem B2833825 : Blo 1116628 2833825 := bstep (se 2 (by rfl) ⟨1062684, by rfl⟩ : syracuseStep 2833825 = 2125369) B2125369
theorem B4242887 : Blo 1116628 4242887 := bstep (se 1 (by rfl) ⟨3182165, by rfl⟩ : syracuseStep 4242887 = 6364331) B6364331
theorem B1884667 : Blo 1116628 1884667 := bstep (se 1 (by rfl) ⟨1413500, by rfl⟩ : syracuseStep 1884667 = 2827001) B2827001
theorem B2834939 : Blo 1116628 2834939 := bstep (se 1 (by rfl) ⟨2126204, by rfl⟩ : syracuseStep 2834939 = 4252409) B4252409
theorem B3228179 : Blo 1116628 3228179 := bstep (se 1 (by rfl) ⟨2421134, by rfl⟩ : syracuseStep 3228179 = 4842269) B4842269
theorem B6636383 : Blo 1116628 6636383 := bstep (se 1 (by rfl) ⟨4977287, by rfl⟩ : syracuseStep 6636383 = 9954575) B9954575
theorem B1885099 : Blo 1116628 1885099 := bstep (se 1 (by rfl) ⟨1413824, by rfl⟩ : syracuseStep 1885099 = 2827649) B2827649
theorem B2868263 : Blo 1116628 2868263 := bstep (se 1 (by rfl) ⟨2151197, by rfl⟩ : syracuseStep 2868263 = 4302395) B4302395
theorem B48415805 : Blo 1116628 48415805 := bstep (se 3 (by rfl) ⟨9077963, by rfl⟩ : syracuseStep 48415805 = 18155927) B18155927
theorem B6046919 : Blo 1116628 6046919 := bstep (se 1 (by rfl) ⟨4535189, by rfl⟩ : syracuseStep 6046919 = 9070379) B9070379
theorem B1885403 : Blo 1116628 1885403 := bstep (se 1 (by rfl) ⟨1414052, by rfl⟩ : syracuseStep 1885403 = 2828105) B2828105
theorem B5653799 : Blo 1116628 5653799 := bstep (se 1 (by rfl) ⟨4240349, by rfl⟩ : syracuseStep 5653799 = 8480699) B8480699
theorem B4244831 : Blo 1116628 4244831 := bstep (se 1 (by rfl) ⟨3183623, by rfl⟩ : syracuseStep 4244831 = 6367247) B6367247
theorem B4244845 : Blo 1116628 4244845 := bstep (se 3 (by rfl) ⟨795908, by rfl⟩ : syracuseStep 4244845 = 1591817) B1591817
theorem B1885639 : Blo 1116628 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B2835911 : Blo 1116628 2835911 := bstep (se 1 (by rfl) ⟨2126933, by rfl⟩ : syracuseStep 2835911 = 4253867) B4253867
theorem B6374969 : Blo 1116628 6374969 := bstep (se 2 (by rfl) ⟨2390613, by rfl⟩ : syracuseStep 6374969 = 4781227) B4781227
theorem B4245149 : Blo 1116628 4245149 := bstep (se 3 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 4245149 = 1591931) B1591931
theorem B1886159 : Blo 1116628 1886159 := bstep (se 1 (by rfl) ⟨1414619, by rfl⟩ : syracuseStep 1886159 = 2829239) B2829239
theorem B1886827 : Blo 1116628 1886827 := bstep (se 1 (by rfl) ⟨1415120, by rfl⟩ : syracuseStep 1886827 = 2830241) B2830241
theorem B1887131 : Blo 1116628 1887131 := bstep (se 1 (by rfl) ⟨1415348, by rfl⟩ : syracuseStep 1887131 = 2830697) B2830697
theorem B4541579 : Blo 1116628 4541579 := bstep (se 1 (by rfl) ⟨3406184, by rfl⟩ : syracuseStep 4541579 = 6812369) B6812369
theorem B5655905 : Blo 1116628 5655905 := bstep (se 2 (by rfl) ⟨2120964, by rfl⟩ : syracuseStep 5655905 = 4241929) B4241929
theorem B4247275 : Blo 1116628 4247275 := bstep (se 1 (by rfl) ⟨3185456, by rfl⟩ : syracuseStep 4247275 = 6370913) B6370913
theorem B66178853 : Blo 1116628 66178853 := bstep (se 4 (by rfl) ⟨6204267, by rfl⟩ : syracuseStep 66178853 = 12408535) B12408535
theorem B4247761 : Blo 1116628 4247761 := bstep (se 2 (by rfl) ⟨1592910, by rfl⟩ : syracuseStep 4247761 = 3185821) B3185821
theorem B4248065 : Blo 1116628 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B4248247 : Blo 1116628 4248247 := bstep (se 1 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 4248247 = 6372371) B6372371
theorem B4543199 : Blo 1116628 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B4248521 : Blo 1116628 4248521 := bstep (se 2 (by rfl) ⟨1593195, by rfl⟩ : syracuseStep 4248521 = 3186391) B3186391
theorem B4248551 : Blo 1116628 4248551 := bstep (se 1 (by rfl) ⟨3186413, by rfl⟩ : syracuseStep 4248551 = 6372827) B6372827
theorem B4248719 : Blo 1116628 4248719 := bstep (se 1 (by rfl) ⟨3186539, by rfl⟩ : syracuseStep 4248719 = 6373079) B6373079
theorem B4773113 : Blo 1116628 4773113 := bstep (se 2 (by rfl) ⟨1789917, by rfl⟩ : syracuseStep 4773113 = 3579835) B3579835
theorem B5657849 : Blo 1116628 5657849 := bstep (se 2 (by rfl) ⟨2121693, by rfl⟩ : syracuseStep 5657849 = 4243387) B4243387
theorem B10769759 : Blo 1116628 10769759 := bstep (se 1 (by rfl) ⟨8077319, by rfl⟩ : syracuseStep 10769759 = 16154639) B16154639
theorem B3823037 : Blo 1116628 3823037 := bstep (se 3 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 3823037 = 1433639) B1433639
theorem B2512619 : Blo 1116628 2512619 := bstep (se 1 (by rfl) ⟨1884464, by rfl⟩ : syracuseStep 2512619 = 3768929) B3768929
theorem B2512745 : Blo 1116628 2512745 := bstep (se 2 (by rfl) ⟨942279, by rfl⟩ : syracuseStep 2512745 = 1884559) B1884559
theorem B4774153 : Blo 1116628 4774153 := bstep (se 2 (by rfl) ⟨1790307, by rfl⟩ : syracuseStep 4774153 = 3580615) B3580615
theorem B9558283 : Blo 1116628 9558283 := bstep (se 1 (by rfl) ⟨7168712, by rfl⟩ : syracuseStep 9558283 = 14337425) B14337425
theorem B7166231 : Blo 1116628 7166231 := bstep (se 1 (by rfl) ⟨5374673, by rfl⟩ : syracuseStep 7166231 = 10749347) B10749347
theorem B24533543 : Blo 1116628 24533543 := bstep (se 1 (by rfl) ⟨18400157, by rfl⟩ : syracuseStep 24533543 = 36800315) B36800315
theorem B12737087 : Blo 1116628 12737087 := bstep (se 1 (by rfl) ⟨9552815, by rfl⟩ : syracuseStep 12737087 = 19105631) B19105631
theorem B4250191 : Blo 1116628 4250191 := bstep (se 1 (by rfl) ⟨3187643, by rfl⟩ : syracuseStep 4250191 = 6375287) B6375287
theorem B2513591 : Blo 1116628 2513591 := bstep (se 1 (by rfl) ⟨1885193, by rfl⟩ : syracuseStep 2513591 = 3770387) B3770387
theorem B1891039 : Blo 1116628 1891039 := bstep (se 1 (by rfl) ⟨1418279, by rfl⟩ : syracuseStep 1891039 = 2836559) B2836559
theorem B21486455 : Blo 1116628 21486455 := bstep (se 1 (by rfl) ⟨16114841, by rfl⟩ : syracuseStep 21486455 = 32229683) B32229683
theorem B2513807 : Blo 1116628 2513807 := bstep (se 1 (by rfl) ⟨1885355, by rfl⟩ : syracuseStep 2513807 = 3770711) B3770711
theorem B13622201 : Blo 1116628 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B7658525 : Blo 1116628 7658525 := bstep (se 3 (by rfl) ⟨1435973, by rfl⟩ : syracuseStep 7658525 = 2871947) B2871947
theorem B4250663 : Blo 1116628 4250663 := bstep (se 1 (by rfl) ⟨3187997, by rfl⟩ : syracuseStep 4250663 = 6375995) B6375995
theorem B2121299 : Blo 1116628 2121299 := bstep (se 1 (by rfl) ⟨1590974, by rfl⟩ : syracuseStep 2121299 = 3181949) B3181949
theorem B2514527 : Blo 1116628 2514527 := bstep (se 1 (by rfl) ⟨1885895, by rfl⟩ : syracuseStep 2514527 = 3771791) B3771791
theorem B12902003 : Blo 1116628 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B2121527 : Blo 1116628 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B2514743 : Blo 1116628 2514743 := bstep (se 1 (by rfl) ⟨1886057, by rfl⟩ : syracuseStep 2514743 = 3772115) B3772115
theorem B2515049 : Blo 1116628 2515049 := bstep (se 2 (by rfl) ⟨943143, by rfl⟩ : syracuseStep 2515049 = 1886287) B1886287
theorem B8184017 : Blo 1116628 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B2122195 : Blo 1116628 2122195 := bstep (se 1 (by rfl) ⟨1591646, by rfl⟩ : syracuseStep 2122195 = 3183293) B3183293
theorem B2515535 : Blo 1116628 2515535 := bstep (se 1 (by rfl) ⟨1886651, by rfl⟩ : syracuseStep 2515535 = 3773303) B3773303
theorem B4776545 : Blo 1116628 4776545 := bstep (se 2 (by rfl) ⟨1791204, by rfl⟩ : syracuseStep 4776545 = 3582409) B3582409
theorem B2515679 : Blo 1116628 2515679 := bstep (se 1 (by rfl) ⟨1886759, by rfl⟩ : syracuseStep 2515679 = 3773519) B3773519
theorem B10740539 : Blo 1116628 10740539 := bstep (se 1 (by rfl) ⟨8055404, by rfl⟩ : syracuseStep 10740539 = 16110809) B16110809
theorem B9069407 : Blo 1116628 9069407 := bstep (se 1 (by rfl) ⟨6802055, by rfl⟩ : syracuseStep 9069407 = 13604111) B13604111
theorem B2515931 : Blo 1116628 2515931 := bstep (se 1 (by rfl) ⟨1886948, by rfl⟩ : syracuseStep 2515931 = 3773897) B3773897
theorem B2516111 : Blo 1116628 2516111 := bstep (se 1 (by rfl) ⟨1887083, by rfl⟩ : syracuseStep 2516111 = 3774167) B3774167
theorem B6120593 : Blo 1116628 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B2122985 : Blo 1116628 2122985 := bstep (se 2 (by rfl) ⟨796119, by rfl⟩ : syracuseStep 2122985 = 1592239) B1592239
theorem B2516201 : Blo 1116628 2516201 := bstep (se 2 (by rfl) ⟨943575, by rfl⟩ : syracuseStep 2516201 = 1887151) B1887151
theorem B2516255 : Blo 1116628 2516255 := bstep (se 1 (by rfl) ⟨1887191, by rfl⟩ : syracuseStep 2516255 = 3774383) B3774383
theorem B19096883 : Blo 1116628 19096883 := bstep (se 1 (by rfl) ⟨14322662, by rfl⟩ : syracuseStep 19096883 = 28645325) B28645325
theorem B19391795 : Blo 1116628 19391795 := bstep (se 1 (by rfl) ⟨14543846, by rfl⟩ : syracuseStep 19391795 = 29087693) B29087693
theorem B5662061 : Blo 1116628 5662061 := bstep (se 3 (by rfl) ⟨1061636, by rfl⟩ : syracuseStep 5662061 = 2123273) B2123273
theorem B15328925 : Blo 1116628 15328925 := bstep (se 3 (by rfl) ⟨2874173, by rfl⟩ : syracuseStep 15328925 = 5748347) B5748347
theorem B2123425 : Blo 1116628 2123425 := bstep (se 2 (by rfl) ⟨796284, by rfl⟩ : syracuseStep 2123425 = 1592569) B1592569
theorem B2516777 : Blo 1116628 2516777 := bstep (se 2 (by rfl) ⟨943791, by rfl⟩ : syracuseStep 2516777 = 1887583) B1887583
theorem B5368231 : Blo 1116628 5368231 := bstep (se 1 (by rfl) ⟨4026173, by rfl⟩ : syracuseStep 5368231 = 8052347) B8052347
theorem B2386351 : Blo 1116628 2386351 := bstep (se 1 (by rfl) ⟨1789763, by rfl⟩ : syracuseStep 2386351 = 3579527) B3579527
theorem B2386427 : Blo 1116628 2386427 := bstep (se 1 (by rfl) ⟨1789820, by rfl⟩ : syracuseStep 2386427 = 3579641) B3579641
theorem B4254383 : Blo 1116628 4254383 := bstep (se 1 (by rfl) ⟨3190787, by rfl⟩ : syracuseStep 4254383 = 6381575) B6381575
theorem B7662269 : Blo 1116628 7662269 := bstep (se 3 (by rfl) ⟨1436675, by rfl⟩ : syracuseStep 7662269 = 2873351) B2873351
theorem B2517839 : Blo 1116628 2517839 := bstep (se 1 (by rfl) ⟨1888379, by rfl⟩ : syracuseStep 2517839 = 3776759) B3776759
theorem B8481671 : Blo 1116628 8481671 := bstep (se 1 (by rfl) ⟨6361253, by rfl⟩ : syracuseStep 8481671 = 12722507) B12722507
theorem B447147029 : Blo 1116628 447147029 := bstep (se 6 (by rfl) ⟨10480008, by rfl⟩ : syracuseStep 447147029 = 20960017) B20960017
theorem B2518055 : Blo 1116628 2518055 := bstep (se 1 (by rfl) ⟨1888541, by rfl⟩ : syracuseStep 2518055 = 3777083) B3777083
theorem B6810763 : Blo 1116628 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B6057125 : Blo 1116628 6057125 := bstep (se 4 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 6057125 = 1135711) B1135711
theorem B2518235 : Blo 1116628 2518235 := bstep (se 1 (by rfl) ⟨1888676, by rfl⟩ : syracuseStep 2518235 = 3777353) B3777353
theorem B1699103 : Blo 1116628 1699103 := bstep (se 1 (by rfl) ⟨1274327, by rfl⟩ : syracuseStep 1699103 = 2548655) B2548655
theorem B2518433 : Blo 1116628 2518433 := bstep (se 2 (by rfl) ⟨944412, by rfl⟩ : syracuseStep 2518433 = 1888825) B1888825
theorem B1699321 : Blo 1116628 1699321 := bstep (se 2 (by rfl) ⟨637245, by rfl⟩ : syracuseStep 1699321 = 1274491) B1274491
theorem B2551391 : Blo 1116628 2551391 := bstep (se 1 (by rfl) ⟨1913543, by rfl⟩ : syracuseStep 2551391 = 3827087) B3827087
theorem B5664491 : Blo 1116628 5664491 := bstep (se 1 (by rfl) ⟨4248368, by rfl⟩ : syracuseStep 5664491 = 8496737) B8496737
theorem B22998971 : Blo 1116628 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B1273807 : Blo 1116628 1273807 := bstep (se 1 (by rfl) ⟨955355, by rfl⟩ : syracuseStep 1273807 = 1910711) B1910711
theorem B2518991 : Blo 1116628 2518991 := bstep (se 1 (by rfl) ⟨1889243, by rfl⟩ : syracuseStep 2518991 = 3778487) B3778487
theorem B10186955 : Blo 1116628 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B5664977 : Blo 1116628 5664977 := bstep (se 2 (by rfl) ⟨2124366, by rfl⟩ : syracuseStep 5664977 = 4248733) B4248733
theorem B2519369 : Blo 1116628 2519369 := bstep (se 2 (by rfl) ⟨944763, by rfl⟩ : syracuseStep 2519369 = 1889527) B1889527
theorem B2519387 : Blo 1116628 2519387 := bstep (se 1 (by rfl) ⟨1889540, by rfl⟩ : syracuseStep 2519387 = 3779081) B3779081
theorem B9695621 : Blo 1116628 9695621 := bstep (se 4 (by rfl) ⟨908964, by rfl⟩ : syracuseStep 9695621 = 1817929) B1817929
theorem B5665463 : Blo 1116628 5665463 := bstep (se 1 (by rfl) ⟨4249097, by rfl⟩ : syracuseStep 5665463 = 8498195) B8498195
theorem B2519963 : Blo 1116628 2519963 := bstep (se 1 (by rfl) ⟨1889972, by rfl⟩ : syracuseStep 2519963 = 3779945) B3779945
theorem B2520161 : Blo 1116628 2520161 := bstep (se 2 (by rfl) ⟨945060, by rfl⟩ : syracuseStep 2520161 = 1890121) B1890121
theorem B8058001 : Blo 1116628 8058001 := bstep (se 2 (by rfl) ⟨3021750, by rfl⟩ : syracuseStep 8058001 = 6043501) B6043501
theorem B5665949 : Blo 1116628 5665949 := bstep (se 3 (by rfl) ⟨1062365, by rfl⟩ : syracuseStep 5665949 = 2124731) B2124731
theorem B2520359 : Blo 1116628 2520359 := bstep (se 1 (by rfl) ⟨1890269, by rfl⟩ : syracuseStep 2520359 = 3780539) B3780539
theorem B5371231 : Blo 1116628 5371231 := bstep (se 1 (by rfl) ⟨4028423, by rfl⟩ : syracuseStep 5371231 = 8056847) B8056847
theorem B7173481 : Blo 1116628 7173481 := bstep (se 2 (by rfl) ⟨2690055, by rfl⟩ : syracuseStep 7173481 = 5380111) B5380111
theorem B4781501 : Blo 1116628 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B2520737 : Blo 1116628 2520737 := bstep (se 2 (by rfl) ⟨945276, by rfl⟩ : syracuseStep 2520737 = 1890553) B1890553
theorem B2521097 : Blo 1116628 2521097 := bstep (se 2 (by rfl) ⟨945411, by rfl⟩ : syracuseStep 2521097 = 1890823) B1890823
theorem B5667245 : Blo 1116628 5667245 := bstep (se 3 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 5667245 = 2125217) B2125217
theorem B14318153 : Blo 1116628 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B5667407 : Blo 1116628 5667407 := bstep (se 1 (by rfl) ⟨4250555, by rfl⟩ : syracuseStep 5667407 = 8501111) B8501111
theorem B8059499 : Blo 1116628 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B7174763 : Blo 1116628 7174763 := bstep (se 1 (by rfl) ⟨5381072, by rfl⟩ : syracuseStep 7174763 = 10762145) B10762145
theorem B32733829 : Blo 1116628 32733829 := bstep (se 4 (by rfl) ⟨3068796, by rfl⟩ : syracuseStep 32733829 = 6137593) B6137593
theorem B6453955 : Blo 1116628 6453955 := bstep (se 1 (by rfl) ⟨4840466, by rfl⟩ : syracuseStep 6453955 = 9680933) B9680933
theorem B2391545 : Blo 1116628 2391545 := bstep (se 2 (by rfl) ⟨896829, by rfl⟩ : syracuseStep 2391545 = 1793659) B1793659
theorem B8061403 : Blo 1116628 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B4424255 : Blo 1116628 4424255 := bstep (se 1 (by rfl) ⟨3318191, by rfl⟩ : syracuseStep 4424255 = 6636383) B6636383
theorem B32277203 : Blo 1116628 32277203 := bstep (se 1 (by rfl) ⟨24207902, by rfl⟩ : syracuseStep 32277203 = 48415805) B48415805
theorem B4031279 : Blo 1116628 4031279 := bstep (se 1 (by rfl) ⟨3023459, by rfl⟩ : syracuseStep 4031279 = 6046919) B6046919
theorem B3769145 : Blo 1116628 3769145 := bstep (se 2 (by rfl) ⟨1413429, by rfl⟩ : syracuseStep 3769145 = 2826859) B2826859
theorem B3769199 : Blo 1116628 3769199 := bstep (se 1 (by rfl) ⟨2826899, by rfl⟩ : syracuseStep 3769199 = 5653799) B5653799
theorem B3770009 : Blo 1116628 3770009 := bstep (se 2 (by rfl) ⟨1413753, by rfl⟩ : syracuseStep 3770009 = 2827507) B2827507
theorem B10749995 : Blo 1116628 10749995 := bstep (se 1 (by rfl) ⟨8062496, by rfl⟩ : syracuseStep 10749995 = 16124993) B16124993
theorem B3770603 : Blo 1116628 3770603 := bstep (se 1 (by rfl) ⟨2827952, by rfl⟩ : syracuseStep 3770603 = 5655905) B5655905
theorem B4786523 : Blo 1116628 4786523 := bstep (se 1 (by rfl) ⟨3589892, by rfl⟩ : syracuseStep 4786523 = 7179785) B7179785
theorem B1116699 : Blo 1116628 1116699 := bstep (se 1 (by rfl) ⟨837524, by rfl⟩ : syracuseStep 1116699 = 1675049) B1675049
theorem B1116703 : Blo 1116628 1116703 := bstep (se 1 (by rfl) ⟨837527, by rfl⟩ : syracuseStep 1116703 = 1675055) B1675055
theorem B1117019 : Blo 1116628 1117019 := bstep (se 1 (by rfl) ⟨837764, by rfl⟩ : syracuseStep 1117019 = 1675529) B1675529
theorem B1117087 : Blo 1116628 1117087 := bstep (se 1 (by rfl) ⟨837815, by rfl⟩ : syracuseStep 1117087 = 1675631) B1675631
theorem B1117231 : Blo 1116628 1117231 := bstep (se 1 (by rfl) ⟨837923, by rfl⟩ : syracuseStep 1117231 = 1675847) B1675847
theorem B1117255 : Blo 1116628 1117255 := bstep (se 1 (by rfl) ⟨837941, by rfl⟩ : syracuseStep 1117255 = 1675883) B1675883
theorem B1117407 : Blo 1116628 1117407 := bstep (se 1 (by rfl) ⟨838055, by rfl⟩ : syracuseStep 1117407 = 1676111) B1676111
theorem B3181801 : Blo 1116628 3181801 := bstep (se 2 (by rfl) ⟨1193175, by rfl⟩ : syracuseStep 3181801 = 2386351) B2386351
theorem B4033901 : Blo 1116628 4033901 := bstep (se 3 (by rfl) ⟨756356, by rfl⟩ : syracuseStep 4033901 = 1512713) B1512713
theorem B4033961 : Blo 1116628 4033961 := bstep (se 2 (by rfl) ⟨1512735, by rfl⟩ : syracuseStep 4033961 = 3025471) B3025471
theorem B1117671 : Blo 1116628 1117671 := bstep (se 1 (by rfl) ⟨838253, by rfl⟩ : syracuseStep 1117671 = 1676507) B1676507
theorem B3182075 : Blo 1116628 3182075 := bstep (se 1 (by rfl) ⟨2386556, by rfl⟩ : syracuseStep 3182075 = 4773113) B4773113
theorem B3771899 : Blo 1116628 3771899 := bstep (se 1 (by rfl) ⟨2828924, by rfl⟩ : syracuseStep 3771899 = 5657849) B5657849
theorem B7179839 : Blo 1116628 7179839 := bstep (se 1 (by rfl) ⟨5384879, by rfl⟩ : syracuseStep 7179839 = 10769759) B10769759
theorem B1117787 : Blo 1116628 1117787 := bstep (se 1 (by rfl) ⟨838340, by rfl⟩ : syracuseStep 1117787 = 1676681) B1676681
theorem B3772061 : Blo 1116628 3772061 := bstep (se 3 (by rfl) ⟨707261, by rfl⟩ : syracuseStep 3772061 = 1414523) B1414523
theorem B24219317 : Blo 1116628 24219317 := bstep (se 5 (by rfl) ⟨1135280, by rfl⟩ : syracuseStep 24219317 = 2270561) B2270561
theorem B1675079 : Blo 1116628 1675079 := bstep (se 1 (by rfl) ⟨1256309, by rfl⟩ : syracuseStep 1675079 = 2512619) B2512619
theorem B1118023 : Blo 1116628 1118023 := bstep (se 1 (by rfl) ⟨838517, by rfl⟩ : syracuseStep 1118023 = 1677035) B1677035
theorem B1675163 : Blo 1116628 1675163 := bstep (se 1 (by rfl) ⟨1256372, by rfl⟩ : syracuseStep 1675163 = 2512745) B2512745
theorem B1118175 : Blo 1116628 1118175 := bstep (se 1 (by rfl) ⟨838631, by rfl⟩ : syracuseStep 1118175 = 1677263) B1677263
theorem B3772601 : Blo 1116628 3772601 := bstep (se 2 (by rfl) ⟨1414725, by rfl⟩ : syracuseStep 3772601 = 2829451) B2829451
theorem B9081017 : Blo 1116628 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B1118439 : Blo 1116628 1118439 := bstep (se 1 (by rfl) ⟨838829, by rfl⟩ : syracuseStep 1118439 = 1677659) B1677659
theorem B16355695 : Blo 1116628 16355695 := bstep (se 1 (by rfl) ⟨12266771, by rfl⟩ : syracuseStep 16355695 = 24533543) B24533543
theorem B8491391 : Blo 1116628 8491391 := bstep (se 1 (by rfl) ⟨6368543, by rfl⟩ : syracuseStep 8491391 = 12737087) B12737087
theorem B1118591 : Blo 1116628 1118591 := bstep (se 1 (by rfl) ⟨838943, by rfl⟩ : syracuseStep 1118591 = 1677887) B1677887
theorem B1675727 : Blo 1116628 1675727 := bstep (se 1 (by rfl) ⟨1256795, by rfl⟩ : syracuseStep 1675727 = 2513591) B2513591
theorem B1118671 : Blo 1116628 1118671 := bstep (se 1 (by rfl) ⟨839003, by rfl⟩ : syracuseStep 1118671 = 1678007) B1678007
theorem B1675769 : Blo 1116628 1675769 := bstep (se 2 (by rfl) ⟨628413, by rfl⟩ : syracuseStep 1675769 = 1256827) B1256827
theorem B14324303 : Blo 1116628 14324303 := bstep (se 1 (by rfl) ⟨10743227, by rfl⟩ : syracuseStep 14324303 = 21486455) B21486455
theorem B1675871 : Blo 1116628 1675871 := bstep (se 1 (by rfl) ⟨1256903, by rfl⟩ : syracuseStep 1675871 = 2513807) B2513807
theorem B1118823 : Blo 1116628 1118823 := bstep (se 1 (by rfl) ⟨839117, by rfl⟩ : syracuseStep 1118823 = 1678235) B1678235
theorem B9081467 : Blo 1116628 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B2265761 : Blo 1116628 2265761 := bstep (se 2 (by rfl) ⟨849660, by rfl⟩ : syracuseStep 2265761 = 1699321) B1699321
theorem B1119087 : Blo 1116628 1119087 := bstep (se 1 (by rfl) ⟨839315, by rfl⟩ : syracuseStep 1119087 = 1678631) B1678631
theorem B1119143 : Blo 1116628 1119143 := bstep (se 1 (by rfl) ⟨839357, by rfl⟩ : syracuseStep 1119143 = 1678715) B1678715
theorem B1119227 : Blo 1116628 1119227 := bstep (se 1 (by rfl) ⟨839420, by rfl⟩ : syracuseStep 1119227 = 1678841) B1678841
theorem B14357519 : Blo 1116628 14357519 := bstep (se 1 (by rfl) ⟨10768139, by rfl⟩ : syracuseStep 14357519 = 21536279) B21536279
theorem B1414199 : Blo 1116628 1414199 := bstep (se 1 (by rfl) ⟨1060649, by rfl⟩ : syracuseStep 1414199 = 2121299) B2121299
theorem B1676351 : Blo 1116628 1676351 := bstep (se 1 (by rfl) ⟨1257263, by rfl⟩ : syracuseStep 1676351 = 2514527) B2514527
theorem B1119295 : Blo 1116628 1119295 := bstep (se 1 (by rfl) ⟨839471, by rfl⟩ : syracuseStep 1119295 = 1678943) B1678943
theorem B1676393 : Blo 1116628 1676393 := bstep (se 2 (by rfl) ⟨628647, by rfl⟩ : syracuseStep 1676393 = 1257295) B1257295
theorem B1414351 : Blo 1116628 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B1676495 : Blo 1116628 1676495 := bstep (se 1 (by rfl) ⟨1257371, by rfl⟩ : syracuseStep 1676495 = 2514743) B2514743
theorem B1119439 : Blo 1116628 1119439 := bstep (se 1 (by rfl) ⟨839579, by rfl⟩ : syracuseStep 1119439 = 1679159) B1679159
theorem B1676699 : Blo 1116628 1676699 := bstep (se 1 (by rfl) ⟨1257524, by rfl⟩ : syracuseStep 1676699 = 2515049) B2515049
theorem B1119643 : Blo 1116628 1119643 := bstep (se 1 (by rfl) ⟨839732, by rfl⟩ : syracuseStep 1119643 = 1679465) B1679465
theorem B1119855 : Blo 1116628 1119855 := bstep (se 1 (by rfl) ⟨839891, by rfl⟩ : syracuseStep 1119855 = 1679783) B1679783
theorem B1676921 : Blo 1116628 1676921 := bstep (se 2 (by rfl) ⟨628845, by rfl⟩ : syracuseStep 1676921 = 1257691) B1257691
theorem B1119911 : Blo 1116628 1119911 := bstep (se 1 (by rfl) ⟨839933, by rfl⟩ : syracuseStep 1119911 = 1679867) B1679867
theorem B1677023 : Blo 1116628 1677023 := bstep (se 1 (by rfl) ⟨1257767, by rfl⟩ : syracuseStep 1677023 = 2515535) B2515535
theorem B3184363 : Blo 1116628 3184363 := bstep (se 1 (by rfl) ⟨2388272, by rfl⟩ : syracuseStep 3184363 = 4776545) B4776545
theorem B1119995 : Blo 1116628 1119995 := bstep (se 1 (by rfl) ⟨839996, by rfl⟩ : syracuseStep 1119995 = 1679993) B1679993
theorem B1120031 : Blo 1116628 1120031 := bstep (se 1 (by rfl) ⟨840023, by rfl⟩ : syracuseStep 1120031 = 1680047) B1680047
theorem B1677119 : Blo 1116628 1677119 := bstep (se 1 (by rfl) ⟨1257839, by rfl⟩ : syracuseStep 1677119 = 2515679) B2515679
theorem B1120063 : Blo 1116628 1120063 := bstep (se 1 (by rfl) ⟨840047, by rfl⟩ : syracuseStep 1120063 = 1680095) B1680095
theorem B1677287 : Blo 1116628 1677287 := bstep (se 1 (by rfl) ⟨1257965, by rfl⟩ : syracuseStep 1677287 = 2515931) B2515931
theorem B1120239 : Blo 1116628 1120239 := bstep (se 1 (by rfl) ⟨840179, by rfl⟩ : syracuseStep 1120239 = 1680359) B1680359
theorem B1677305 : Blo 1116628 1677305 := bstep (se 2 (by rfl) ⟨628989, by rfl⟩ : syracuseStep 1677305 = 1257979) B1257979
theorem B1677407 : Blo 1116628 1677407 := bstep (se 1 (by rfl) ⟨1258055, by rfl⟩ : syracuseStep 1677407 = 2516111) B2516111
theorem B1415323 : Blo 1116628 1415323 := bstep (se 1 (by rfl) ⟨1061492, by rfl⟩ : syracuseStep 1415323 = 2122985) B2122985
theorem B1677467 : Blo 1116628 1677467 := bstep (se 1 (by rfl) ⟨1258100, by rfl⟩ : syracuseStep 1677467 = 2516201) B2516201
theorem B1120411 : Blo 1116628 1120411 := bstep (se 1 (by rfl) ⟨840308, by rfl⟩ : syracuseStep 1120411 = 1680617) B1680617
theorem B1677503 : Blo 1116628 1677503 := bstep (se 1 (by rfl) ⟨1258127, by rfl⟩ : syracuseStep 1677503 = 2516255) B2516255
theorem B1120447 : Blo 1116628 1120447 := bstep (se 1 (by rfl) ⟨840335, by rfl⟩ : syracuseStep 1120447 = 1680671) B1680671
theorem B1677545 : Blo 1116628 1677545 := bstep (se 2 (by rfl) ⟨629079, by rfl⟩ : syracuseStep 1677545 = 1258159) B1258159
theorem B3774707 : Blo 1116628 3774707 := bstep (se 1 (by rfl) ⟨2831030, by rfl⟩ : syracuseStep 3774707 = 5662061) B5662061
theorem B3774761 : Blo 1116628 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B1120559 : Blo 1116628 1120559 := bstep (se 1 (by rfl) ⟨840419, by rfl⟩ : syracuseStep 1120559 = 1680839) B1680839
theorem B1677851 : Blo 1116628 1677851 := bstep (se 1 (by rfl) ⟨1258388, by rfl⟩ : syracuseStep 1677851 = 2516777) B2516777
theorem B1677929 : Blo 1116628 1677929 := bstep (se 2 (by rfl) ⟨629223, by rfl⟩ : syracuseStep 1677929 = 1258447) B1258447
theorem B6363805 : Blo 1116628 6363805 := bstep (se 3 (by rfl) ⟨1193213, by rfl⟩ : syracuseStep 6363805 = 2386427) B2386427
theorem B1678457 : Blo 1116628 1678457 := bstep (se 2 (by rfl) ⟨629421, by rfl⟩ : syracuseStep 1678457 = 1258843) B1258843
theorem B1678559 : Blo 1116628 1678559 := bstep (se 1 (by rfl) ⟨1258919, by rfl⟩ : syracuseStep 1678559 = 2517839) B2517839
theorem B1678601 : Blo 1116628 1678601 := bstep (se 2 (by rfl) ⟨629475, by rfl⟩ : syracuseStep 1678601 = 1258951) B1258951
theorem B298098019 : Blo 1116628 298098019 := bstep (se 1 (by rfl) ⟨223573514, by rfl⟩ : syracuseStep 298098019 = 447147029) B447147029
theorem B1678703 : Blo 1116628 1678703 := bstep (se 1 (by rfl) ⟨1259027, by rfl⟩ : syracuseStep 1678703 = 2518055) B2518055
theorem B4038083 : Blo 1116628 4038083 := bstep (se 1 (by rfl) ⟨3028562, by rfl⟩ : syracuseStep 4038083 = 6057125) B6057125
theorem B1678823 : Blo 1116628 1678823 := bstep (se 1 (by rfl) ⟨1259117, by rfl⟩ : syracuseStep 1678823 = 2518235) B2518235
theorem B1678955 : Blo 1116628 1678955 := bstep (se 1 (by rfl) ⟨1259216, by rfl⟩ : syracuseStep 1678955 = 2518433) B2518433
theorem B21503677 : Blo 1116628 21503677 := bstep (se 3 (by rfl) ⟨4031939, by rfl⟩ : syracuseStep 21503677 = 8063879) B8063879
theorem B1679081 : Blo 1116628 1679081 := bstep (se 2 (by rfl) ⟨629655, by rfl⟩ : syracuseStep 1679081 = 1259311) B1259311
theorem B3776327 : Blo 1116628 3776327 := bstep (se 1 (by rfl) ⟨2832245, by rfl⟩ : syracuseStep 3776327 = 5664491) B5664491
theorem B1679225 : Blo 1116628 1679225 := bstep (se 2 (by rfl) ⟨629709, by rfl⟩ : syracuseStep 1679225 = 1259419) B1259419
theorem B3776381 : Blo 1116628 3776381 := bstep (se 3 (by rfl) ⟨708071, by rfl⟩ : syracuseStep 3776381 = 1416143) B1416143
theorem B1679327 : Blo 1116628 1679327 := bstep (se 1 (by rfl) ⟨1259495, by rfl⟩ : syracuseStep 1679327 = 2518991) B2518991
theorem B6791303 : Blo 1116628 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B3776651 : Blo 1116628 3776651 := bstep (se 1 (by rfl) ⟨2832488, by rfl⟩ : syracuseStep 3776651 = 5664977) B5664977
theorem B1679579 : Blo 1116628 1679579 := bstep (se 1 (by rfl) ⟨1259684, by rfl⟩ : syracuseStep 1679579 = 2519369) B2519369
theorem B1679591 : Blo 1116628 1679591 := bstep (se 1 (by rfl) ⟨1259693, by rfl⟩ : syracuseStep 1679591 = 2519387) B2519387
theorem B6463747 : Blo 1116628 6463747 := bstep (se 1 (by rfl) ⟨4847810, by rfl⟩ : syracuseStep 6463747 = 9695621) B9695621
theorem B6365537 : Blo 1116628 6365537 := bstep (se 2 (by rfl) ⟨2387076, by rfl⟩ : syracuseStep 6365537 = 4774153) B4774153
theorem B1679753 : Blo 1116628 1679753 := bstep (se 2 (by rfl) ⟨629907, by rfl⟩ : syracuseStep 1679753 = 1259815) B1259815
theorem B3776975 : Blo 1116628 3776975 := bstep (se 1 (by rfl) ⟨2832731, by rfl⟩ : syracuseStep 3776975 = 5665463) B5665463
theorem B1679849 : Blo 1116628 1679849 := bstep (se 2 (by rfl) ⟨629943, by rfl⟩ : syracuseStep 1679849 = 1259887) B1259887
theorem B1679975 : Blo 1116628 1679975 := bstep (se 1 (by rfl) ⟨1259981, by rfl⟩ : syracuseStep 1679975 = 2519963) B2519963
theorem B1680107 : Blo 1116628 1680107 := bstep (se 1 (by rfl) ⟨1260080, by rfl⟩ : syracuseStep 1680107 = 2520161) B2520161
theorem B4530941 : Blo 1116628 4530941 := bstep (se 3 (by rfl) ⟨849551, by rfl⟩ : syracuseStep 4530941 = 1699103) B1699103
theorem B1680137 : Blo 1116628 1680137 := bstep (se 2 (by rfl) ⟨630051, by rfl⟩ : syracuseStep 1680137 = 1260103) B1260103
theorem B3777299 : Blo 1116628 3777299 := bstep (se 1 (by rfl) ⟨2832974, by rfl⟩ : syracuseStep 3777299 = 5665949) B5665949
theorem B1680239 : Blo 1116628 1680239 := bstep (se 1 (by rfl) ⟨1260179, by rfl⟩ : syracuseStep 1680239 = 2520359) B2520359
theorem B3023783 : Blo 1116628 3023783 := bstep (se 1 (by rfl) ⟨2267837, by rfl⟩ : syracuseStep 3023783 = 4535675) B4535675
theorem B3187667 : Blo 1116628 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B1680491 : Blo 1116628 1680491 := bstep (se 1 (by rfl) ⟨1260368, by rfl⟩ : syracuseStep 1680491 = 2520737) B2520737
theorem B1680731 : Blo 1116628 1680731 := bstep (se 1 (by rfl) ⟨1260548, by rfl⟩ : syracuseStep 1680731 = 2521097) B2521097
theorem B3778163 : Blo 1116628 3778163 := bstep (se 1 (by rfl) ⟨2833622, by rfl⟩ : syracuseStep 3778163 = 5667245) B5667245
theorem B2827943 : Blo 1116628 2827943 := bstep (se 1 (by rfl) ⟨2120957, by rfl⟩ : syracuseStep 2827943 = 4241915) B4241915
theorem B9545435 : Blo 1116628 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B3778271 : Blo 1116628 3778271 := bstep (se 1 (by rfl) ⟨2833703, by rfl⟩ : syracuseStep 3778271 = 5667407) B5667407
theorem B3778433 : Blo 1116628 3778433 := bstep (se 2 (by rfl) ⟨1416912, by rfl⟩ : syracuseStep 3778433 = 2833825) B2833825
theorem B2828479 : Blo 1116628 2828479 := bstep (se 1 (by rfl) ⟨2121359, by rfl⟩ : syracuseStep 2828479 = 4242719) B4242719
theorem B2828591 : Blo 1116628 2828591 := bstep (se 1 (by rfl) ⟨2121443, by rfl⟩ : syracuseStep 2828591 = 4242887) B4242887
theorem B3778973 : Blo 1116628 3778973 := bstep (se 3 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 3778973 = 1417115) B1417115
theorem B3779243 : Blo 1116628 3779243 := bstep (se 1 (by rfl) ⟨2834432, by rfl⟩ : syracuseStep 3779243 = 5668865) B5668865
theorem B4303811 : Blo 1116628 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B3779783 : Blo 1116628 3779783 := bstep (se 1 (by rfl) ⟨2834837, by rfl⟩ : syracuseStep 3779783 = 5669675) B5669675
theorem B2829593 : Blo 1116628 2829593 := bstep (se 2 (by rfl) ⟨1061097, by rfl⟩ : syracuseStep 2829593 = 2122195) B2122195
theorem B1912175 : Blo 1116628 1912175 := bstep (se 1 (by rfl) ⟨1434131, by rfl⟩ : syracuseStep 1912175 = 2868263) B2868263
theorem B1256935 : Blo 1116628 1256935 := bstep (se 1 (by rfl) ⟨942701, by rfl⟩ : syracuseStep 1256935 = 1885403) B1885403
theorem B2829887 : Blo 1116628 2829887 := bstep (se 1 (by rfl) ⟨2122415, by rfl⟩ : syracuseStep 2829887 = 4244831) B4244831
theorem B2830099 : Blo 1116628 2830099 := bstep (se 1 (by rfl) ⟨2122574, by rfl⟩ : syracuseStep 2830099 = 4245149) B4245149
theorem B12758957 : Blo 1116628 12758957 := bstep (se 3 (by rfl) ⟨2392304, by rfl⟩ : syracuseStep 12758957 = 4784609) B4784609
theorem B1257439 : Blo 1116628 1257439 := bstep (se 1 (by rfl) ⟨943079, by rfl⟩ : syracuseStep 1257439 = 1886159) B1886159
theorem B8499167 : Blo 1116628 8499167 := bstep (se 1 (by rfl) ⟨6374375, by rfl⟩ : syracuseStep 8499167 = 12748751) B12748751
theorem B3781079 : Blo 1116628 3781079 := bstep (se 1 (by rfl) ⟨2835809, by rfl⟩ : syracuseStep 3781079 = 5671619) B5671619
theorem B1258087 : Blo 1116628 1258087 := bstep (se 1 (by rfl) ⟨943565, by rfl⟩ : syracuseStep 1258087 = 1887131) B1887131
theorem B3027719 : Blo 1116628 3027719 := bstep (se 1 (by rfl) ⟨2270789, by rfl⟩ : syracuseStep 3027719 = 4541579) B4541579
theorem B2831233 : Blo 1116628 2831233 := bstep (se 2 (by rfl) ⟨1061712, by rfl⟩ : syracuseStep 2831233 = 2123425) B2123425
theorem B8500139 : Blo 1116628 8500139 := bstep (se 1 (by rfl) ⟨6375104, by rfl⟩ : syracuseStep 8500139 = 12750209) B12750209
theorem B4240457 : Blo 1116628 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B44119235 : Blo 1116628 44119235 := bstep (se 1 (by rfl) ⟨33089426, by rfl⟩ : syracuseStep 44119235 = 66178853) B66178853
theorem B7353865 : Blo 1116628 7353865 := bstep (se 2 (by rfl) ⟨2757699, by rfl⟩ : syracuseStep 7353865 = 5515399) B5515399
theorem B2832043 : Blo 1116628 2832043 := bstep (se 1 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 2832043 = 4248065) B4248065
theorem B3028799 : Blo 1116628 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B7157641 : Blo 1116628 7157641 := bstep (se 2 (by rfl) ⟨2684115, by rfl⟩ : syracuseStep 7157641 = 5368231) B5368231
theorem B2832347 : Blo 1116628 2832347 := bstep (se 1 (by rfl) ⟨2124260, by rfl⟩ : syracuseStep 2832347 = 4248521) B4248521
theorem B2832367 : Blo 1116628 2832367 := bstep (se 1 (by rfl) ⟨2124275, by rfl⟩ : syracuseStep 2832367 = 4248551) B4248551
theorem B2832479 : Blo 1116628 2832479 := bstep (se 1 (by rfl) ⟨2124359, by rfl⟩ : syracuseStep 2832479 = 4248719) B4248719
theorem B14531075 : Blo 1116628 14531075 := bstep (se 1 (by rfl) ⟨10898306, by rfl⟩ : syracuseStep 14531075 = 21796613) B21796613
theorem B12761873 : Blo 1116628 12761873 := bstep (se 2 (by rfl) ⟨4785702, by rfl⟩ : syracuseStep 12761873 = 9571405) B9571405
theorem B8502083 : Blo 1116628 8502083 := bstep (se 1 (by rfl) ⟨6376562, by rfl⟩ : syracuseStep 8502083 = 12753125) B12753125
theorem B2833775 : Blo 1116628 2833775 := bstep (se 1 (by rfl) ⟨2125331, by rfl⟩ : syracuseStep 2833775 = 4250663) B4250663
theorem B8076773 : Blo 1116628 8076773 := bstep (se 4 (by rfl) ⟨757197, by rfl⟩ : syracuseStep 8076773 = 1514395) B1514395
theorem B8601335 : Blo 1116628 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B2015099 : Blo 1116628 2015099 := bstep (se 1 (by rfl) ⟨1511324, by rfl⟩ : syracuseStep 2015099 = 3022649) B3022649
theorem B5456011 : Blo 1116628 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B7160359 : Blo 1116628 7160359 := bstep (se 1 (by rfl) ⟨5370269, by rfl⟩ : syracuseStep 7160359 = 10740539) B10740539
theorem B6046271 : Blo 1116628 6046271 := bstep (se 1 (by rfl) ⟨4534703, by rfl⟩ : syracuseStep 6046271 = 9069407) B9069407
theorem B1884775 : Blo 1116628 1884775 := bstep (se 1 (by rfl) ⟨1413581, by rfl⟩ : syracuseStep 1884775 = 2827163) B2827163
theorem B1884937 : Blo 1116628 1884937 := bstep (se 2 (by rfl) ⟨706851, by rfl⟩ : syracuseStep 1884937 = 1413703) B1413703
theorem B4080395 : Blo 1116628 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B12731255 : Blo 1116628 12731255 := bstep (se 1 (by rfl) ⟨9548441, by rfl⟩ : syracuseStep 12731255 = 19096883) B19096883
theorem B12927863 : Blo 1116628 12927863 := bstep (se 1 (by rfl) ⟨9695897, by rfl⟩ : syracuseStep 12927863 = 19391795) B19391795
theorem B1885531 : Blo 1116628 1885531 := bstep (se 1 (by rfl) ⟨1414148, by rfl⟩ : syracuseStep 1885531 = 2828297) B2828297
theorem B2836255 : Blo 1116628 2836255 := bstep (se 1 (by rfl) ⟨2127191, by rfl⟩ : syracuseStep 2836255 = 4254383) B4254383
theorem B7161641 : Blo 1116628 7161641 := bstep (se 2 (by rfl) ⟨2685615, by rfl⟩ : syracuseStep 7161641 = 5371231) B5371231
theorem B4769711 : Blo 1116628 4769711 := bstep (se 1 (by rfl) ⟨3577283, by rfl⟩ : syracuseStep 4769711 = 7154567) B7154567
theorem B5654447 : Blo 1116628 5654447 := bstep (se 1 (by rfl) ⟨4240835, by rfl⟩ : syracuseStep 5654447 = 8481671) B8481671
theorem B1886503 : Blo 1116628 1886503 := bstep (se 1 (by rfl) ⟨1414877, by rfl⟩ : syracuseStep 1886503 = 2829755) B2829755
theorem B4246121 : Blo 1116628 4246121 := bstep (se 2 (by rfl) ⟨1592295, by rfl⟩ : syracuseStep 4246121 = 3184591) B3184591
theorem B1887455 : Blo 1116628 1887455 := bstep (se 1 (by rfl) ⟨1415591, by rfl⟩ : syracuseStep 1887455 = 2831183) B2831183
theorem B8506943 : Blo 1116628 8506943 := bstep (se 1 (by rfl) ⟨6380207, by rfl⟩ : syracuseStep 8506943 = 12760415) B12760415
theorem B8605273 : Blo 1116628 8605273 := bstep (se 2 (by rfl) ⟨3226977, by rfl⟩ : syracuseStep 8605273 = 6453955) B6453955
theorem B1887887 : Blo 1116628 1887887 := bstep (se 1 (by rfl) ⟨1415915, by rfl⟩ : syracuseStep 1887887 = 2831831) B2831831
theorem B2019143 : Blo 1116628 2019143 := bstep (se 1 (by rfl) ⟨1514357, by rfl⟩ : syracuseStep 2019143 = 3028715) B3028715
theorem B1888123 : Blo 1116628 1888123 := bstep (se 1 (by rfl) ⟨1416092, by rfl⟩ : syracuseStep 1888123 = 2832185) B2832185
theorem B6377453 : Blo 1116628 6377453 := bstep (se 3 (by rfl) ⟨1195772, by rfl⟩ : syracuseStep 6377453 = 2391545) B2391545
theorem B14340401 : Blo 1116628 14340401 := bstep (se 2 (by rfl) ⟨5377650, by rfl⟩ : syracuseStep 14340401 = 10755301) B10755301
theorem B12898865 : Blo 1116628 12898865 := bstep (se 2 (by rfl) ⟨4837074, by rfl⟩ : syracuseStep 12898865 = 9674149) B9674149
theorem B4772513 : Blo 1116628 4772513 := bstep (se 2 (by rfl) ⟨1789692, by rfl⟩ : syracuseStep 4772513 = 3579385) B3579385
theorem B1889959 : Blo 1116628 1889959 := bstep (se 1 (by rfl) ⟨1417469, by rfl⟩ : syracuseStep 1889959 = 2834939) B2834939
theorem B1595047 : Blo 1116628 1595047 := bstep (se 1 (by rfl) ⟨1196285, by rfl⟩ : syracuseStep 1595047 = 2392571) B2392571
theorem B2512871 : Blo 1116628 2512871 := bstep (se 1 (by rfl) ⟨1884653, by rfl⟩ : syracuseStep 2512871 = 3769307) B3769307
theorem B2512889 : Blo 1116628 2512889 := bstep (se 2 (by rfl) ⟨942333, by rfl⟩ : syracuseStep 2512889 = 1884667) B1884667
theorem B2512979 : Blo 1116628 2512979 := bstep (se 1 (by rfl) ⟨1884734, by rfl⟩ : syracuseStep 2512979 = 3769469) B3769469
theorem B6051935 : Blo 1116628 6051935 := bstep (se 1 (by rfl) ⟨4538951, by rfl⟩ : syracuseStep 6051935 = 9077903) B9077903
theorem B43604099 : Blo 1116628 43604099 := bstep (se 1 (by rfl) ⟨32703074, by rfl⟩ : syracuseStep 43604099 = 65406149) B65406149
theorem B2513051 : Blo 1116628 2513051 := bstep (se 1 (by rfl) ⟨1884788, by rfl⟩ : syracuseStep 2513051 = 3769577) B3769577
theorem B2513159 : Blo 1116628 2513159 := bstep (se 1 (by rfl) ⟨1884869, by rfl⟩ : syracuseStep 2513159 = 3769739) B3769739
theorem B1890607 : Blo 1116628 1890607 := bstep (se 1 (by rfl) ⟨1417955, by rfl⟩ : syracuseStep 1890607 = 2835911) B2835911
theorem B4249979 : Blo 1116628 4249979 := bstep (se 1 (by rfl) ⟨3187484, by rfl⟩ : syracuseStep 4249979 = 6374969) B6374969
theorem B2513465 : Blo 1116628 2513465 := bstep (se 2 (by rfl) ⟨942549, by rfl⟩ : syracuseStep 2513465 = 1885099) B1885099
theorem B13589113 : Blo 1116628 13589113 := bstep (se 2 (by rfl) ⟨5095917, by rfl⟩ : syracuseStep 13589113 = 10191835) B10191835
theorem B8608477 : Blo 1116628 8608477 := bstep (se 3 (by rfl) ⟨1614089, by rfl⟩ : syracuseStep 8608477 = 3228179) B3228179
theorem B6380369 : Blo 1116628 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B5659793 : Blo 1116628 5659793 := bstep (se 2 (by rfl) ⟨2122422, by rfl⟩ : syracuseStep 5659793 = 4244845) B4244845
theorem B2514185 : Blo 1116628 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B6446567 : Blo 1116628 6446567 := bstep (se 1 (by rfl) ⟨4834925, by rfl⟩ : syracuseStep 6446567 = 9669851) B9669851
theorem B7167791 : Blo 1116628 7167791 := bstep (se 1 (by rfl) ⟨5375843, by rfl⟩ : syracuseStep 7167791 = 10751687) B10751687
theorem B2515175 : Blo 1116628 2515175 := bstep (se 1 (by rfl) ⟨1886381, by rfl⟩ : syracuseStep 2515175 = 3772763) B3772763
theorem B6381827 : Blo 1116628 6381827 := bstep (se 1 (by rfl) ⟨4786370, by rfl⟩ : syracuseStep 6381827 = 9572741) B9572741
theorem B1794511 : Blo 1116628 1794511 := bstep (se 1 (by rfl) ⟨1345883, by rfl⟩ : syracuseStep 1794511 = 2691767) B2691767
theorem B2515769 : Blo 1116628 2515769 := bstep (se 2 (by rfl) ⟨943413, by rfl⟩ : syracuseStep 2515769 = 1886827) B1886827
theorem B2515823 : Blo 1116628 2515823 := bstep (se 1 (by rfl) ⟨1886867, by rfl⟩ : syracuseStep 2515823 = 3773735) B3773735
theorem B2548691 : Blo 1116628 2548691 := bstep (se 1 (by rfl) ⟨1911518, by rfl⟩ : syracuseStep 2548691 = 3823037) B3823037
theorem B2516399 : Blo 1116628 2516399 := bstep (se 1 (by rfl) ⟨1887299, by rfl⟩ : syracuseStep 2516399 = 3774599) B3774599
theorem B4777487 : Blo 1116628 4777487 := bstep (se 1 (by rfl) ⟨3583115, by rfl⟩ : syracuseStep 4777487 = 7166231) B7166231
theorem B5662223 : Blo 1116628 5662223 := bstep (se 1 (by rfl) ⟨4246667, by rfl⟩ : syracuseStep 5662223 = 8493335) B8493335
theorem B5105683 : Blo 1116628 5105683 := bstep (se 1 (by rfl) ⟨3829262, by rfl⟩ : syracuseStep 5105683 = 7658525) B7658525
theorem B6056045 : Blo 1116628 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B2517227 : Blo 1116628 2517227 := bstep (se 1 (by rfl) ⟨1887920, by rfl⟩ : syracuseStep 2517227 = 3775841) B3775841
theorem B5663033 : Blo 1116628 5663033 := bstep (se 2 (by rfl) ⟨2123637, by rfl⟩ : syracuseStep 5663033 = 4247275) B4247275
theorem B8481185 : Blo 1116628 8481185 := bstep (se 2 (by rfl) ⟨3180444, by rfl⟩ : syracuseStep 8481185 = 6360889) B6360889
theorem B8612389 : Blo 1116628 8612389 := bstep (se 4 (by rfl) ⟨807411, by rfl⟩ : syracuseStep 8612389 = 1614823) B1614823
theorem B1698409 : Blo 1116628 1698409 := bstep (se 2 (by rfl) ⟨636903, by rfl⟩ : syracuseStep 1698409 = 1273807) B1273807
theorem B7170763 : Blo 1116628 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B5663681 : Blo 1116628 5663681 := bstep (se 2 (by rfl) ⟨2123880, by rfl⟩ : syracuseStep 5663681 = 4247761) B4247761
theorem B11496451 : Blo 1116628 11496451 := bstep (se 1 (by rfl) ⟨8622338, by rfl⟩ : syracuseStep 11496451 = 17244677) B17244677
theorem B8482157 : Blo 1116628 8482157 := bstep (se 3 (by rfl) ⟨1590404, by rfl⟩ : syracuseStep 8482157 = 3180809) B3180809
theorem B2518523 : Blo 1116628 2518523 := bstep (se 1 (by rfl) ⟨1888892, by rfl⟩ : syracuseStep 2518523 = 3777785) B3777785
theorem B5664329 : Blo 1116628 5664329 := bstep (se 2 (by rfl) ⟨2124123, by rfl⟩ : syracuseStep 5664329 = 4248247) B4248247
theorem B2518703 : Blo 1116628 2518703 := bstep (se 1 (by rfl) ⟨1889027, by rfl⟩ : syracuseStep 2518703 = 3778055) B3778055
theorem B10219283 : Blo 1116628 10219283 := bstep (se 1 (by rfl) ⟨7664462, by rfl⟩ : syracuseStep 10219283 = 15328925) B15328925
theorem B2387855 : Blo 1116628 2387855 := bstep (se 1 (by rfl) ⟨1790891, by rfl⟩ : syracuseStep 2387855 = 3581783) B3581783
theorem B5730203 : Blo 1116628 5730203 := bstep (se 1 (by rfl) ⟨4297652, by rfl⟩ : syracuseStep 5730203 = 8595305) B8595305
theorem B10744001 : Blo 1116628 10744001 := bstep (se 2 (by rfl) ⟨4029000, by rfl⟩ : syracuseStep 10744001 = 8058001) B8058001
theorem B2519351 : Blo 1116628 2519351 := bstep (se 1 (by rfl) ⟨1889513, by rfl⟩ : syracuseStep 2519351 = 3779027) B3779027
theorem B2519423 : Blo 1116628 2519423 := bstep (se 1 (by rfl) ⟨1889567, by rfl⟩ : syracuseStep 2519423 = 3779135) B3779135
theorem B5108179 : Blo 1116628 5108179 := bstep (se 1 (by rfl) ⟨3831134, by rfl⟩ : syracuseStep 5108179 = 7662269) B7662269
theorem B9564641 : Blo 1116628 9564641 := bstep (se 2 (by rfl) ⟨3586740, by rfl⟩ : syracuseStep 9564641 = 7173481) B7173481
theorem B1700927 : Blo 1116628 1700927 := bstep (se 1 (by rfl) ⟨1275695, by rfl⟩ : syracuseStep 1700927 = 2551391) B2551391
theorem B2126911 : Blo 1116628 2126911 := bstep (se 1 (by rfl) ⟨1595183, by rfl⟩ : syracuseStep 2126911 = 3190367) B3190367
theorem B15332647 : Blo 1116628 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B2520647 : Blo 1116628 2520647 := bstep (se 1 (by rfl) ⟨1890485, by rfl⟩ : syracuseStep 2520647 = 3780971) B3780971
theorem B12744377 : Blo 1116628 12744377 := bstep (se 2 (by rfl) ⟨4779141, by rfl⟩ : syracuseStep 12744377 = 9558283) B9558283
theorem B8484587 : Blo 1116628 8484587 := bstep (se 1 (by rfl) ⟨6363440, by rfl⟩ : syracuseStep 8484587 = 12726881) B12726881
theorem B2520827 : Blo 1116628 2520827 := bstep (se 1 (by rfl) ⟨1890620, by rfl⟩ : syracuseStep 2520827 = 3781241) B3781241
theorem B2389999 : Blo 1116628 2389999 := bstep (se 1 (by rfl) ⟨1792499, by rfl⟩ : syracuseStep 2389999 = 3584999) B3584999
theorem B5666921 : Blo 1116628 5666921 := bstep (se 2 (by rfl) ⟨2125095, by rfl⟩ : syracuseStep 5666921 = 4250191) B4250191
theorem B4782185 : Blo 1116628 4782185 := bstep (se 2 (by rfl) ⟨1793319, by rfl⟩ : syracuseStep 4782185 = 3586639) B3586639
theorem B43645105 : Blo 1116628 43645105 := bstep (se 2 (by rfl) ⟨16366914, by rfl⟩ : syracuseStep 43645105 = 32733829) B32733829
theorem B1341631 : Blo 1116628 1341631 := bstep (se 1 (by rfl) ⟨1006223, by rfl⟩ : syracuseStep 1341631 = 2012447) B2012447
theorem B2521385 : Blo 1116628 2521385 := bstep (se 2 (by rfl) ⟨945519, by rfl⟩ : syracuseStep 2521385 = 1891039) B1891039
theorem B6126137 : Blo 1116628 6126137 := bstep (se 2 (by rfl) ⟨2297301, by rfl⟩ : syracuseStep 6126137 = 4594603) B4594603
theorem B13597247 : Blo 1116628 13597247 := bstep (se 1 (by rfl) ⟨10197935, by rfl⟩ : syracuseStep 13597247 = 20395871) B20395871
theorem B2685577 : Blo 1116628 2685577 := bstep (se 2 (by rfl) ⟨1007091, by rfl⟩ : syracuseStep 2685577 = 2014183) B2014183
theorem B5372999 : Blo 1116628 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B4783175 : Blo 1116628 4783175 := bstep (se 1 (by rfl) ⟨3587381, by rfl⟩ : syracuseStep 4783175 = 7174763) B7174763
theorem B54361529 : Blo 1116628 54361529 := bstep (se 2 (by rfl) ⟨20385573, by rfl⟩ : syracuseStep 54361529 = 40771147) B40771147
theorem B7175789 : Blo 1116628 7175789 := bstep (se 3 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 7175789 = 2690921) B2690921
theorem B7274681 : Blo 1116628 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B8618329 : Blo 1116628 8618329 := bstep (se 2 (by rfl) ⟨3231873, by rfl⟩ : syracuseStep 8618329 = 6463747) B6463747
theorem B4030847 : Blo 1116628 4030847 := bstep (se 1 (by rfl) ⟨3023135, by rfl⟩ : syracuseStep 4030847 = 6046271) B6046271
theorem B2949503 : Blo 1116628 2949503 := bstep (se 1 (by rfl) ⟨2212127, by rfl⟩ : syracuseStep 2949503 = 4424255) B4424255
theorem B2687519 : Blo 1116628 2687519 := bstep (se 1 (by rfl) ⟨2015639, by rfl⟩ : syracuseStep 2687519 = 4031279) B4031279
theorem B8487503 : Blo 1116628 8487503 := bstep (se 1 (by rfl) ⟨6365627, by rfl⟩ : syracuseStep 8487503 = 12731255) B12731255
theorem B8618575 : Blo 1116628 8618575 := bstep (se 1 (by rfl) ⟨6463931, by rfl⟩ : syracuseStep 8618575 = 12927863) B12927863
theorem B2392681 : Blo 1116628 2392681 := bstep (se 2 (by rfl) ⟨897255, by rfl⟩ : syracuseStep 2392681 = 1794511) B1794511
theorem B10748537 : Blo 1116628 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B3179807 : Blo 1116628 3179807 := bstep (se 1 (by rfl) ⟨2384855, by rfl⟩ : syracuseStep 3179807 = 4769711) B4769711
theorem B3769631 : Blo 1116628 3769631 := bstep (se 1 (by rfl) ⟨2827223, by rfl⟩ : syracuseStep 3769631 = 5654447) B5654447
theorem B10881053 : Blo 1116628 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B2689307 : Blo 1116628 2689307 := bstep (se 1 (by rfl) ⟨2016980, by rfl⟩ : syracuseStep 2689307 = 4033961) B4033961
theorem B5671295 : Blo 1116628 5671295 := bstep (se 1 (by rfl) ⟨4253471, by rfl⟩ : syracuseStep 5671295 = 8506943) B8506943
theorem B4786559 : Blo 1116628 4786559 := bstep (se 1 (by rfl) ⟨3589919, by rfl⟩ : syracuseStep 4786559 = 7179839) B7179839
theorem B1116719 : Blo 1116628 1116719 := bstep (se 1 (by rfl) ⟨837539, by rfl⟩ : syracuseStep 1116719 = 1675079) B1675079
theorem B1346095 : Blo 1116628 1346095 := bstep (se 1 (by rfl) ⟨1009571, by rfl⟩ : syracuseStep 1346095 = 2019143) B2019143
theorem B1116775 : Blo 1116628 1116775 := bstep (se 1 (by rfl) ⟨837581, by rfl⟩ : syracuseStep 1116775 = 1675163) B1675163
theorem B3771197 : Blo 1116628 3771197 := bstep (se 3 (by rfl) ⟨707099, by rfl⟩ : syracuseStep 3771197 = 1414199) B1414199
theorem B3771305 : Blo 1116628 3771305 := bstep (se 2 (by rfl) ⟨1414239, by rfl⟩ : syracuseStep 3771305 = 2828479) B2828479
theorem B1117151 : Blo 1116628 1117151 := bstep (se 1 (by rfl) ⟨837863, by rfl⟩ : syracuseStep 1117151 = 1675727) B1675727
theorem B1117179 : Blo 1116628 1117179 := bstep (se 1 (by rfl) ⟨837884, by rfl⟩ : syracuseStep 1117179 = 1675769) B1675769
theorem B1117247 : Blo 1116628 1117247 := bstep (se 1 (by rfl) ⟨837935, by rfl⟩ : syracuseStep 1117247 = 1675871) B1675871
theorem B3181675 : Blo 1116628 3181675 := bstep (se 1 (by rfl) ⟨2386256, by rfl⟩ : syracuseStep 3181675 = 4772513) B4772513
theorem B1510507 : Blo 1116628 1510507 := bstep (se 1 (by rfl) ⟨1132880, by rfl⟩ : syracuseStep 1510507 = 2265761) B2265761
theorem B9571679 : Blo 1116628 9571679 := bstep (se 1 (by rfl) ⟨7178759, by rfl⟩ : syracuseStep 9571679 = 14357519) B14357519
theorem B1117567 : Blo 1116628 1117567 := bstep (se 1 (by rfl) ⟨838175, by rfl⟩ : syracuseStep 1117567 = 1676351) B1676351
theorem B1117595 : Blo 1116628 1117595 := bstep (se 1 (by rfl) ⟨838196, by rfl⟩ : syracuseStep 1117595 = 1676393) B1676393
theorem B1117663 : Blo 1116628 1117663 := bstep (se 1 (by rfl) ⟨838247, by rfl⟩ : syracuseStep 1117663 = 1676495) B1676495
theorem B2264545 : Blo 1116628 2264545 := bstep (se 2 (by rfl) ⟨849204, by rfl⟩ : syracuseStep 2264545 = 1698409) B1698409
theorem B1117799 : Blo 1116628 1117799 := bstep (se 1 (by rfl) ⟨838349, by rfl⟩ : syracuseStep 1117799 = 1676699) B1676699
theorem B1117947 : Blo 1116628 1117947 := bstep (se 1 (by rfl) ⟨838460, by rfl⟩ : syracuseStep 1117947 = 1676921) B1676921
theorem B1118015 : Blo 1116628 1118015 := bstep (se 1 (by rfl) ⟨838511, by rfl⟩ : syracuseStep 1118015 = 1677023) B1677023
theorem B1118079 : Blo 1116628 1118079 := bstep (se 1 (by rfl) ⟨838559, by rfl⟩ : syracuseStep 1118079 = 1677119) B1677119
theorem B1675247 : Blo 1116628 1675247 := bstep (se 1 (by rfl) ⟨1256435, by rfl⟩ : syracuseStep 1675247 = 2512871) B2512871
theorem B1118191 : Blo 1116628 1118191 := bstep (se 1 (by rfl) ⟨838643, by rfl⟩ : syracuseStep 1118191 = 1677287) B1677287
theorem B1675259 : Blo 1116628 1675259 := bstep (se 1 (by rfl) ⟨1256444, by rfl⟩ : syracuseStep 1675259 = 2512889) B2512889
theorem B1118203 : Blo 1116628 1118203 := bstep (se 1 (by rfl) ⟨838652, by rfl⟩ : syracuseStep 1118203 = 1677305) B1677305
theorem B1675319 : Blo 1116628 1675319 := bstep (se 1 (by rfl) ⟨1256489, by rfl⟩ : syracuseStep 1675319 = 2512979) B2512979
theorem B1118271 : Blo 1116628 1118271 := bstep (se 1 (by rfl) ⟨838703, by rfl⟩ : syracuseStep 1118271 = 1677407) B1677407
theorem B4034623 : Blo 1116628 4034623 := bstep (se 1 (by rfl) ⟨3025967, by rfl⟩ : syracuseStep 4034623 = 6051935) B6051935
theorem B29069399 : Blo 1116628 29069399 := bstep (se 1 (by rfl) ⟨21802049, by rfl⟩ : syracuseStep 29069399 = 43604099) B43604099
theorem B1675367 : Blo 1116628 1675367 := bstep (se 1 (by rfl) ⟨1256525, by rfl⟩ : syracuseStep 1675367 = 2513051) B2513051
theorem B1118311 : Blo 1116628 1118311 := bstep (se 1 (by rfl) ⟨838733, by rfl⟩ : syracuseStep 1118311 = 1677467) B1677467
theorem B1118335 : Blo 1116628 1118335 := bstep (se 1 (by rfl) ⟨838751, by rfl⟩ : syracuseStep 1118335 = 1677503) B1677503
theorem B1118363 : Blo 1116628 1118363 := bstep (se 1 (by rfl) ⟨838772, by rfl⟩ : syracuseStep 1118363 = 1677545) B1677545
theorem B1675439 : Blo 1116628 1675439 := bstep (se 1 (by rfl) ⟨1256579, by rfl⟩ : syracuseStep 1675439 = 2513159) B2513159
theorem B1118567 : Blo 1116628 1118567 := bstep (se 1 (by rfl) ⟨838925, by rfl⟩ : syracuseStep 1118567 = 1677851) B1677851
theorem B1675643 : Blo 1116628 1675643 := bstep (se 1 (by rfl) ⟨1256732, by rfl⟩ : syracuseStep 1675643 = 2513465) B2513465
theorem B1118619 : Blo 1116628 1118619 := bstep (se 1 (by rfl) ⟨838964, by rfl⟩ : syracuseStep 1118619 = 1677929) B1677929
theorem B1675913 : Blo 1116628 1675913 := bstep (se 2 (by rfl) ⟨628467, by rfl⟩ : syracuseStep 1675913 = 1256935) B1256935
theorem B1118971 : Blo 1116628 1118971 := bstep (se 1 (by rfl) ⟨839228, by rfl⟩ : syracuseStep 1118971 = 1678457) B1678457
theorem B3773195 : Blo 1116628 3773195 := bstep (se 1 (by rfl) ⟨2829896, by rfl⟩ : syracuseStep 3773195 = 5659793) B5659793
theorem B11473697 : Blo 1116628 11473697 := bstep (se 2 (by rfl) ⟨4302636, by rfl⟩ : syracuseStep 11473697 = 8605273) B8605273
theorem B1119039 : Blo 1116628 1119039 := bstep (se 1 (by rfl) ⟨839279, by rfl⟩ : syracuseStep 1119039 = 1678559) B1678559
theorem B1676123 : Blo 1116628 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B1119067 : Blo 1116628 1119067 := bstep (se 1 (by rfl) ⟨839300, by rfl⟩ : syracuseStep 1119067 = 1678601) B1678601
theorem B1119135 : Blo 1116628 1119135 := bstep (se 1 (by rfl) ⟨839351, by rfl⟩ : syracuseStep 1119135 = 1678703) B1678703
theorem B2692055 : Blo 1116628 2692055 := bstep (se 1 (by rfl) ⟨2019041, by rfl⟩ : syracuseStep 2692055 = 4038083) B4038083
theorem B4297711 : Blo 1116628 4297711 := bstep (se 1 (by rfl) ⟨3223283, by rfl⟩ : syracuseStep 4297711 = 6446567) B6446567
theorem B1119215 : Blo 1116628 1119215 := bstep (se 1 (by rfl) ⟨839411, by rfl⟩ : syracuseStep 1119215 = 1678823) B1678823
theorem B3773465 : Blo 1116628 3773465 := bstep (se 2 (by rfl) ⟨1415049, by rfl⟩ : syracuseStep 3773465 = 2830099) B2830099
theorem B1119303 : Blo 1116628 1119303 := bstep (se 1 (by rfl) ⟨839477, by rfl⟩ : syracuseStep 1119303 = 1678955) B1678955
theorem B1119387 : Blo 1116628 1119387 := bstep (se 1 (by rfl) ⟨839540, by rfl⟩ : syracuseStep 1119387 = 1679081) B1679081
theorem B1119483 : Blo 1116628 1119483 := bstep (se 1 (by rfl) ⟨839612, by rfl⟩ : syracuseStep 1119483 = 1679225) B1679225
theorem B1676585 : Blo 1116628 1676585 := bstep (se 2 (by rfl) ⟨628719, by rfl⟩ : syracuseStep 1676585 = 1257439) B1257439
theorem B1119551 : Blo 1116628 1119551 := bstep (se 1 (by rfl) ⟨839663, by rfl⟩ : syracuseStep 1119551 = 1679327) B1679327
theorem B4527535 : Blo 1116628 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B1119719 : Blo 1116628 1119719 := bstep (se 1 (by rfl) ⟨839789, by rfl⟩ : syracuseStep 1119719 = 1679579) B1679579
theorem B1676783 : Blo 1116628 1676783 := bstep (se 1 (by rfl) ⟨1257587, by rfl⟩ : syracuseStep 1676783 = 2515175) B2515175
theorem B1119727 : Blo 1116628 1119727 := bstep (se 1 (by rfl) ⟨839795, by rfl⟩ : syracuseStep 1119727 = 1679591) B1679591
theorem B1119835 : Blo 1116628 1119835 := bstep (se 1 (by rfl) ⟨839876, by rfl⟩ : syracuseStep 1119835 = 1679753) B1679753
theorem B1119899 : Blo 1116628 1119899 := bstep (se 1 (by rfl) ⟨839924, by rfl⟩ : syracuseStep 1119899 = 1679849) B1679849
theorem B1119983 : Blo 1116628 1119983 := bstep (se 1 (by rfl) ⟨839987, by rfl⟩ : syracuseStep 1119983 = 1679975) B1679975
theorem B1120071 : Blo 1116628 1120071 := bstep (se 1 (by rfl) ⟨840053, by rfl⟩ : syracuseStep 1120071 = 1680107) B1680107
theorem B3020627 : Blo 1116628 3020627 := bstep (se 1 (by rfl) ⟨2265470, by rfl⟩ : syracuseStep 3020627 = 4530941) B4530941
theorem B1120091 : Blo 1116628 1120091 := bstep (se 1 (by rfl) ⟨840068, by rfl⟩ : syracuseStep 1120091 = 1680137) B1680137
theorem B1677179 : Blo 1116628 1677179 := bstep (se 1 (by rfl) ⟨1257884, by rfl⟩ : syracuseStep 1677179 = 2515769) B2515769
theorem B1677215 : Blo 1116628 1677215 := bstep (se 1 (by rfl) ⟨1257911, by rfl⟩ : syracuseStep 1677215 = 2515823) B2515823
theorem B1120159 : Blo 1116628 1120159 := bstep (se 1 (by rfl) ⟨840119, by rfl⟩ : syracuseStep 1120159 = 1680239) B1680239
theorem B1120327 : Blo 1116628 1120327 := bstep (se 1 (by rfl) ⟨840245, by rfl⟩ : syracuseStep 1120327 = 1680491) B1680491
theorem B1677449 : Blo 1116628 1677449 := bstep (se 2 (by rfl) ⟨629043, by rfl⟩ : syracuseStep 1677449 = 1258087) B1258087
theorem B1120487 : Blo 1116628 1120487 := bstep (se 1 (by rfl) ⟨840365, by rfl⟩ : syracuseStep 1120487 = 1680731) B1680731
theorem B1677599 : Blo 1116628 1677599 := bstep (se 1 (by rfl) ⟨1258199, by rfl⟩ : syracuseStep 1677599 = 2516399) B2516399
theorem B3184991 : Blo 1116628 3184991 := bstep (se 1 (by rfl) ⟨2388743, by rfl⟩ : syracuseStep 3184991 = 4777487) B4777487
theorem B3774815 : Blo 1116628 3774815 := bstep (se 1 (by rfl) ⟨2831111, by rfl⟩ : syracuseStep 3774815 = 5662223) B5662223
theorem B6363623 : Blo 1116628 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B3774977 : Blo 1116628 3774977 := bstep (se 2 (by rfl) ⟨1415616, by rfl⟩ : syracuseStep 3774977 = 2831233) B2831233
theorem B4037363 : Blo 1116628 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B1678151 : Blo 1116628 1678151 := bstep (se 1 (by rfl) ⟨1258613, by rfl⟩ : syracuseStep 1678151 = 2517227) B2517227
theorem B3775355 : Blo 1116628 3775355 := bstep (se 1 (by rfl) ⟨2831516, by rfl⟩ : syracuseStep 3775355 = 5663033) B5663033
theorem B3775787 : Blo 1116628 3775787 := bstep (se 1 (by rfl) ⟨2831840, by rfl⟩ : syracuseStep 3775787 = 5663681) B5663681
theorem B9805153 : Blo 1116628 9805153 := bstep (se 2 (by rfl) ⟨3676932, by rfl⟩ : syracuseStep 9805153 = 7353865) B7353865
theorem B3776057 : Blo 1116628 3776057 := bstep (se 2 (by rfl) ⟨1416021, by rfl⟩ : syracuseStep 3776057 = 2832043) B2832043
theorem B1679015 : Blo 1116628 1679015 := bstep (se 1 (by rfl) ⟨1259261, by rfl⟩ : syracuseStep 1679015 = 2518523) B2518523
theorem B3776219 : Blo 1116628 3776219 := bstep (se 1 (by rfl) ⟨2832164, by rfl⟩ : syracuseStep 3776219 = 5664329) B5664329
theorem B1679135 : Blo 1116628 1679135 := bstep (se 1 (by rfl) ⟨1259351, by rfl⟩ : syracuseStep 1679135 = 2518703) B2518703
theorem B11476829 : Blo 1116628 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B9543521 : Blo 1116628 9543521 := bstep (se 2 (by rfl) ⟨3578820, by rfl⟩ : syracuseStep 9543521 = 7157641) B7157641
theorem B3776489 : Blo 1116628 3776489 := bstep (se 2 (by rfl) ⟨1416183, by rfl⟩ : syracuseStep 3776489 = 2832367) B2832367
theorem B3186665 : Blo 1116628 3186665 := bstep (se 2 (by rfl) ⟨1194999, by rfl⟩ : syracuseStep 3186665 = 2389999) B2389999
theorem B1679567 : Blo 1116628 1679567 := bstep (se 1 (by rfl) ⟨1259675, by rfl⟩ : syracuseStep 1679567 = 2519351) B2519351
theorem B1679615 : Blo 1116628 1679615 := bstep (se 1 (by rfl) ⟨1259711, by rfl⟩ : syracuseStep 1679615 = 2519423) B2519423
theorem B2826971 : Blo 1116628 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B3580769 : Blo 1116628 3580769 := bstep (se 2 (by rfl) ⟨1342788, by rfl⟩ : syracuseStep 3580769 = 2685577) B2685577
theorem B10757069 : Blo 1116628 10757069 := bstep (se 3 (by rfl) ⟨2016950, by rfl⟩ : syracuseStep 10757069 = 4033901) B4033901
theorem B11477969 : Blo 1116628 11477969 := bstep (se 2 (by rfl) ⟨4304238, by rfl⟩ : syracuseStep 11477969 = 8608477) B8608477
theorem B1680431 : Blo 1116628 1680431 := bstep (se 1 (by rfl) ⟨1260323, by rfl⟩ : syracuseStep 1680431 = 2520647) B2520647
theorem B8496251 : Blo 1116628 8496251 := bstep (se 1 (by rfl) ⟨6372188, by rfl⟩ : syracuseStep 8496251 = 12744377) B12744377
theorem B1680551 : Blo 1116628 1680551 := bstep (se 1 (by rfl) ⟨1260413, by rfl⟩ : syracuseStep 1680551 = 2520827) B2520827
theorem B3777947 : Blo 1116628 3777947 := bstep (se 1 (by rfl) ⟨2833460, by rfl⟩ : syracuseStep 3777947 = 5666921) B5666921
theorem B3188123 : Blo 1116628 3188123 := bstep (se 1 (by rfl) ⟨2391092, by rfl⟩ : syracuseStep 3188123 = 4782185) B4782185
theorem B1680923 : Blo 1116628 1680923 := bstep (se 1 (by rfl) ⟨1260692, by rfl⟩ : syracuseStep 1680923 = 2521385) B2521385
theorem B3581999 : Blo 1116628 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B3188783 : Blo 1116628 3188783 := bstep (se 1 (by rfl) ⟨2391587, by rfl⟩ : syracuseStep 3188783 = 4783175) B4783175
theorem B5384515 : Blo 1116628 5384515 := bstep (se 1 (by rfl) ⟨4038386, by rfl⟩ : syracuseStep 5384515 = 8076773) B8076773
theorem B9547145 : Blo 1116628 9547145 := bstep (se 2 (by rfl) ⟨3580179, by rfl⟩ : syracuseStep 9547145 = 7160359) B7160359
theorem B3191015 : Blo 1116628 3191015 := bstep (se 1 (by rfl) ⟨2393261, by rfl⟩ : syracuseStep 3191015 = 4786523) B4786523
theorem B2830747 : Blo 1116628 2830747 := bstep (se 1 (by rfl) ⟨2123060, by rfl⟩ : syracuseStep 2830747 = 4246121) B4246121
theorem B8073917 : Blo 1116628 8073917 := bstep (se 3 (by rfl) ⟨1513859, by rfl⟩ : syracuseStep 8073917 = 3027719) B3027719
theorem B1258303 : Blo 1116628 1258303 := bstep (se 1 (by rfl) ⟨943727, by rfl⟩ : syracuseStep 1258303 = 1887455) B1887455
theorem B3781673 : Blo 1116628 3781673 := bstep (se 2 (by rfl) ⟨1418127, by rfl⟩ : syracuseStep 3781673 = 2836255) B2836255
theorem B1258591 : Blo 1116628 1258591 := bstep (se 1 (by rfl) ⟨943943, by rfl⟩ : syracuseStep 1258591 = 1887887) B1887887
theorem B8599243 : Blo 1116628 8599243 := bstep (se 1 (by rfl) ⟨6449432, by rfl⟩ : syracuseStep 8599243 = 12898865) B12898865
theorem B9549535 : Blo 1116628 9549535 := bstep (se 1 (by rfl) ⟨7162151, by rfl⟩ : syracuseStep 9549535 = 14324303) B14324303
theorem B2833319 : Blo 1116628 2833319 := bstep (se 1 (by rfl) ⟨2124989, by rfl⟩ : syracuseStep 2833319 = 4249979) B4249979
theorem B4242401 : Blo 1116628 4242401 := bstep (se 2 (by rfl) ⟨1590900, by rfl⟩ : syracuseStep 4242401 = 3181801) B3181801
theorem B8076797 : Blo 1116628 8076797 := bstep (se 3 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 8076797 = 3028799) B3028799
theorem B4243691 : Blo 1116628 4243691 := bstep (se 1 (by rfl) ⟨3182768, by rfl⟩ : syracuseStep 4243691 = 6365537) B6365537
theorem B21807593 : Blo 1116628 21807593 := bstep (se 2 (by rfl) ⟨8177847, by rfl⟩ : syracuseStep 21807593 = 16355695) B16355695
theorem B2015855 : Blo 1116628 2015855 := bstep (se 1 (by rfl) ⟨1511891, by rfl⟩ : syracuseStep 2015855 = 3023783) B3023783
theorem B1885295 : Blo 1116628 1885295 := bstep (se 1 (by rfl) ⟨1413971, by rfl⟩ : syracuseStep 1885295 = 2827943) B2827943
theorem B2835881 : Blo 1116628 2835881 := bstep (se 2 (by rfl) ⟨1063455, by rfl⟩ : syracuseStep 2835881 = 2126911) B2126911
theorem B1885727 : Blo 1116628 1885727 := bstep (se 1 (by rfl) ⟨1414295, by rfl⟩ : syracuseStep 1885727 = 2828591) B2828591
theorem B1885801 : Blo 1116628 1885801 := bstep (se 2 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 1885801 = 1414351) B1414351
theorem B5654123 : Blo 1116628 5654123 := bstep (se 1 (by rfl) ⟨4240592, by rfl⟩ : syracuseStep 5654123 = 8481185) B8481185
theorem B1886395 : Blo 1116628 1886395 := bstep (se 1 (by rfl) ⟨1414796, by rfl⟩ : syracuseStep 1886395 = 2829593) B2829593
theorem B5654771 : Blo 1116628 5654771 := bstep (se 1 (by rfl) ⟨4241078, by rfl⟩ : syracuseStep 5654771 = 8482157) B8482157
theorem B4245817 : Blo 1116628 4245817 := bstep (se 2 (by rfl) ⟨1592181, by rfl⟩ : syracuseStep 4245817 = 3184363) B3184363
theorem B1886591 : Blo 1116628 1886591 := bstep (se 1 (by rfl) ⟨1414943, by rfl⟩ : syracuseStep 1886591 = 2829887) B2829887
theorem B1591903 : Blo 1116628 1591903 := bstep (se 1 (by rfl) ⟨1193927, by rfl⟩ : syracuseStep 1591903 = 2387855) B2387855
theorem B3820135 : Blo 1116628 3820135 := bstep (se 1 (by rfl) ⟨2865101, by rfl⟩ : syracuseStep 3820135 = 5730203) B5730203
theorem B8505971 : Blo 1116628 8505971 := bstep (se 1 (by rfl) ⟨6379478, by rfl⟩ : syracuseStep 8505971 = 12758957) B12758957
theorem B7162667 : Blo 1116628 7162667 := bstep (se 1 (by rfl) ⟨5372000, by rfl⟩ : syracuseStep 7162667 = 10744001) B10744001
theorem B1887097 : Blo 1116628 1887097 := bstep (se 2 (by rfl) ⟨707661, by rfl⟩ : syracuseStep 1887097 = 1415323) B1415323
theorem B1788841 : Blo 1116628 1788841 := bstep (se 2 (by rfl) ⟨670815, by rfl⟩ : syracuseStep 1788841 = 1341631) B1341631
theorem B6376427 : Blo 1116628 6376427 := bstep (se 1 (by rfl) ⟨4782320, by rfl⟩ : syracuseStep 6376427 = 9564641) B9564641
theorem B1133951 : Blo 1116628 1133951 := bstep (se 1 (by rfl) ⟨850463, by rfl⟩ : syracuseStep 1133951 = 1700927) B1700927
theorem B29412823 : Blo 1116628 29412823 := bstep (se 1 (by rfl) ⟨22059617, by rfl⟩ : syracuseStep 29412823 = 44119235) B44119235
theorem B5656391 : Blo 1116628 5656391 := bstep (se 1 (by rfl) ⟨4242293, by rfl⟩ : syracuseStep 5656391 = 8484587) B8484587
theorem B1888231 : Blo 1116628 1888231 := bstep (se 1 (by rfl) ⟨1416173, by rfl⟩ : syracuseStep 1888231 = 2832347) B2832347
theorem B1888319 : Blo 1116628 1888319 := bstep (se 1 (by rfl) ⟨1416239, by rfl⟩ : syracuseStep 1888319 = 2832479) B2832479
theorem B9687383 : Blo 1116628 9687383 := bstep (se 1 (by rfl) ⟨7265537, by rfl⟩ : syracuseStep 9687383 = 14531075) B14531075
theorem B4084091 : Blo 1116628 4084091 := bstep (se 1 (by rfl) ⟨3063068, by rfl⟩ : syracuseStep 4084091 = 6126137) B6126137
theorem B9064831 : Blo 1116628 9064831 := bstep (se 1 (by rfl) ⟨6798623, by rfl⟩ : syracuseStep 9064831 = 13597247) B13597247
theorem B397464025 : Blo 1116628 397464025 := bstep (se 2 (by rfl) ⟨149049009, by rfl⟩ : syracuseStep 397464025 = 298098019) B298098019
theorem B8507915 : Blo 1116628 8507915 := bstep (se 1 (by rfl) ⟨6380936, by rfl⟩ : syracuseStep 8507915 = 12761873) B12761873
theorem B1889183 : Blo 1116628 1889183 := bstep (se 1 (by rfl) ⟨1416887, by rfl⟩ : syracuseStep 1889183 = 2833775) B2833775
theorem B21518135 : Blo 1116628 21518135 := bstep (se 1 (by rfl) ⟨16138601, by rfl⟩ : syracuseStep 21518135 = 32277203) B32277203
theorem B2512763 : Blo 1116628 2512763 := bstep (se 1 (by rfl) ⟨1884572, by rfl⟩ : syracuseStep 2512763 = 3769145) B3769145
theorem B2512799 : Blo 1116628 2512799 := bstep (se 1 (by rfl) ⟨1884599, by rfl⟩ : syracuseStep 2512799 = 3769199) B3769199
theorem B2513033 : Blo 1116628 2513033 := bstep (se 2 (by rfl) ⟨942387, by rfl⟩ : syracuseStep 2513033 = 1884775) B1884775
theorem B2513249 : Blo 1116628 2513249 := bstep (se 2 (by rfl) ⟨942468, by rfl⟩ : syracuseStep 2513249 = 1884937) B1884937
theorem B2513339 : Blo 1116628 2513339 := bstep (se 1 (by rfl) ⟨1885004, by rfl⟩ : syracuseStep 2513339 = 3770009) B3770009
theorem B4774427 : Blo 1116628 4774427 := bstep (se 1 (by rfl) ⟨3580820, by rfl⟩ : syracuseStep 4774427 = 7161641) B7161641
theorem B7166663 : Blo 1116628 7166663 := bstep (se 1 (by rfl) ⟨5374997, by rfl⟩ : syracuseStep 7166663 = 10749995) B10749995
theorem B2513735 : Blo 1116628 2513735 := bstep (se 1 (by rfl) ⟨1885301, by rfl⟩ : syracuseStep 2513735 = 3770603) B3770603
theorem B2514041 : Blo 1116628 2514041 := bstep (se 2 (by rfl) ⟨942765, by rfl⟩ : syracuseStep 2514041 = 1885531) B1885531
theorem B2121383 : Blo 1116628 2121383 := bstep (se 1 (by rfl) ⟨1591037, by rfl⟩ : syracuseStep 2121383 = 3182075) B3182075
theorem B2514599 : Blo 1116628 2514599 := bstep (se 1 (by rfl) ⟨1885949, by rfl⟩ : syracuseStep 2514599 = 3771899) B3771899
theorem B2514707 : Blo 1116628 2514707 := bstep (se 1 (by rfl) ⟨1886030, by rfl⟩ : syracuseStep 2514707 = 3772061) B3772061
theorem B16146211 : Blo 1116628 16146211 := bstep (se 1 (by rfl) ⟨12109658, by rfl⟩ : syracuseStep 16146211 = 24219317) B24219317
theorem B4251635 : Blo 1116628 4251635 := bstep (se 1 (by rfl) ⟨3188726, by rfl⟩ : syracuseStep 4251635 = 6377453) B6377453
theorem B6807577 : Blo 1116628 6807577 := bstep (se 2 (by rfl) ⟨2552841, by rfl⟩ : syracuseStep 6807577 = 5105683) B5105683
theorem B2515067 : Blo 1116628 2515067 := bstep (se 1 (by rfl) ⟨1886300, by rfl⟩ : syracuseStep 2515067 = 3772601) B3772601
theorem B6054011 : Blo 1116628 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B45932741 : Blo 1116628 45932741 := bstep (se 4 (by rfl) ⟨4306194, by rfl⟩ : syracuseStep 45932741 = 8612389) B8612389
theorem B9560267 : Blo 1116628 9560267 := bstep (se 1 (by rfl) ⟨7170200, by rfl⟩ : syracuseStep 9560267 = 14340401) B14340401
theorem B5660927 : Blo 1116628 5660927 := bstep (se 1 (by rfl) ⟨4245695, by rfl⟩ : syracuseStep 5660927 = 8491391) B8491391
theorem B2515337 : Blo 1116628 2515337 := bstep (se 2 (by rfl) ⟨943251, by rfl⟩ : syracuseStep 2515337 = 1886503) B1886503
theorem B6054311 : Blo 1116628 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B9561017 : Blo 1116628 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B15328601 : Blo 1116628 15328601 := bstep (se 2 (by rfl) ⟨5748225, by rfl⟩ : syracuseStep 15328601 = 11496451) B11496451
theorem B2516471 : Blo 1116628 2516471 := bstep (se 1 (by rfl) ⟨1887353, by rfl⟩ : syracuseStep 2516471 = 3774707) B3774707
theorem B2516507 : Blo 1116628 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B4253579 : Blo 1116628 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B2517497 : Blo 1116628 2517497 := bstep (se 2 (by rfl) ⟨944061, by rfl⟩ : syracuseStep 2517497 = 1888123) B1888123
theorem B4778527 : Blo 1116628 4778527 := bstep (se 1 (by rfl) ⟨3583895, by rfl⟩ : syracuseStep 4778527 = 7167791) B7167791
theorem B2517551 : Blo 1116628 2517551 := bstep (se 1 (by rfl) ⟨1888163, by rfl⟩ : syracuseStep 2517551 = 3776327) B3776327
theorem B2517587 : Blo 1116628 2517587 := bstep (se 1 (by rfl) ⟨1888190, by rfl⟩ : syracuseStep 2517587 = 3776381) B3776381
theorem B2517767 : Blo 1116628 2517767 := bstep (se 1 (by rfl) ⟨1888325, by rfl⟩ : syracuseStep 2517767 = 3776651) B3776651
theorem B4254551 : Blo 1116628 4254551 := bstep (se 1 (by rfl) ⟨3190913, by rfl⟩ : syracuseStep 4254551 = 6381827) B6381827
theorem B2517983 : Blo 1116628 2517983 := bstep (se 1 (by rfl) ⟨1888487, by rfl⟩ : syracuseStep 2517983 = 3776975) B3776975
theorem B2518199 : Blo 1116628 2518199 := bstep (se 1 (by rfl) ⟨1888649, by rfl⟩ : syracuseStep 2518199 = 3777299) B3777299
theorem B6810905 : Blo 1116628 6810905 := bstep (se 2 (by rfl) ⟨2554089, by rfl⟩ : syracuseStep 6810905 = 5108179) B5108179
theorem B1699127 : Blo 1116628 1699127 := bstep (se 1 (by rfl) ⟨1274345, by rfl⟩ : syracuseStep 1699127 = 2548691) B2548691
theorem B2125111 : Blo 1116628 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B2518775 : Blo 1116628 2518775 := bstep (se 1 (by rfl) ⟨1889081, by rfl⟩ : syracuseStep 2518775 = 3778163) B3778163
theorem B2518847 : Blo 1116628 2518847 := bstep (se 1 (by rfl) ⟨1889135, by rfl⟩ : syracuseStep 2518847 = 3778271) B3778271
theorem B2518955 : Blo 1116628 2518955 := bstep (se 1 (by rfl) ⟨1889216, by rfl⟩ : syracuseStep 2518955 = 3778433) B3778433
theorem B2519315 : Blo 1116628 2519315 := bstep (se 1 (by rfl) ⟨1889486, by rfl⟩ : syracuseStep 2519315 = 3778973) B3778973
theorem B20443529 : Blo 1116628 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B2519495 : Blo 1116628 2519495 := bstep (se 1 (by rfl) ⟨1889621, by rfl⟩ : syracuseStep 2519495 = 3779243) B3779243
theorem B2519855 : Blo 1116628 2519855 := bstep (se 1 (by rfl) ⟨1889891, by rfl⟩ : syracuseStep 2519855 = 3779783) B3779783
theorem B2519945 : Blo 1116628 2519945 := bstep (se 2 (by rfl) ⟨944979, by rfl⟩ : syracuseStep 2519945 = 1889959) B1889959
theorem B2126729 : Blo 1116628 2126729 := bstep (se 2 (by rfl) ⟨797523, by rfl⟩ : syracuseStep 2126729 = 1595047) B1595047
theorem B1274783 : Blo 1116628 1274783 := bstep (se 1 (by rfl) ⟨956087, by rfl⟩ : syracuseStep 1274783 = 1912175) B1912175
theorem B6812855 : Blo 1116628 6812855 := bstep (se 1 (by rfl) ⟨5109641, by rfl⟩ : syracuseStep 6812855 = 10219283) B10219283
theorem B5666111 : Blo 1116628 5666111 := bstep (se 1 (by rfl) ⟨4249583, by rfl⟩ : syracuseStep 5666111 = 8499167) B8499167
theorem B58193473 : Blo 1116628 58193473 := bstep (se 2 (by rfl) ⟨21822552, by rfl⟩ : syracuseStep 58193473 = 43645105) B43645105
theorem B2520719 : Blo 1116628 2520719 := bstep (se 1 (by rfl) ⟨1890539, by rfl⟩ : syracuseStep 2520719 = 3781079) B3781079
theorem B2520809 : Blo 1116628 2520809 := bstep (se 2 (by rfl) ⟨945303, by rfl⟩ : syracuseStep 2520809 = 1890607) B1890607
theorem B5666759 : Blo 1116628 5666759 := bstep (se 1 (by rfl) ⟨4250069, by rfl⟩ : syracuseStep 5666759 = 8500139) B8500139
theorem B18118817 : Blo 1116628 18118817 := bstep (se 2 (by rfl) ⟨6794556, by rfl⟩ : syracuseStep 18118817 = 13589113) B13589113
theorem B8485073 : Blo 1116628 8485073 := bstep (se 2 (by rfl) ⟨3181902, by rfl⟩ : syracuseStep 8485073 = 6363805) B6363805
theorem B5668055 : Blo 1116628 5668055 := bstep (se 1 (by rfl) ⟨4251041, by rfl⟩ : syracuseStep 5668055 = 8502083) B8502083
theorem B28671569 : Blo 1116628 28671569 := bstep (se 2 (by rfl) ⟨10751838, by rfl⟩ : syracuseStep 28671569 = 21503677) B21503677
theorem B36241019 : Blo 1116628 36241019 := bstep (se 1 (by rfl) ⟨27180764, by rfl⟩ : syracuseStep 36241019 = 54361529) B54361529
theorem B4783859 : Blo 1116628 4783859 := bstep (se 1 (by rfl) ⟨3587894, by rfl⟩ : syracuseStep 4783859 = 7175789) B7175789
theorem B5734223 : Blo 1116628 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B1343399 : Blo 1116628 1343399 := bstep (se 1 (by rfl) ⟨1007549, by rfl⟩ : syracuseStep 1343399 = 2015099) B2015099
theorem B9076769 : Blo 1116628 9076769 := bstep (se 2 (by rfl) ⟨3403788, by rfl⟩ : syracuseStep 9076769 = 6807577) B6807577
theorem B4849787 : Blo 1116628 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B2687231 : Blo 1116628 2687231 := bstep (se 1 (by rfl) ⟨2015423, by rfl⟩ : syracuseStep 2687231 = 4030847) B4030847
theorem B1343903 : Blo 1116628 1343903 := bstep (se 1 (by rfl) ⟨1007927, by rfl⟩ : syracuseStep 1343903 = 2015855) B2015855
theorem B3769415 : Blo 1116628 3769415 := bstep (se 1 (by rfl) ⟨2827061, by rfl⟩ : syracuseStep 3769415 = 5654123) B5654123
theorem B3769847 : Blo 1116628 3769847 := bstep (se 1 (by rfl) ⟨2827385, by rfl⟩ : syracuseStep 3769847 = 5654771) B5654771
theorem B5670647 : Blo 1116628 5670647 := bstep (se 1 (by rfl) ⟨4252985, by rfl⟩ : syracuseStep 5670647 = 8505971) B8505971
theorem B3770927 : Blo 1116628 3770927 := bstep (se 1 (by rfl) ⟨2828195, by rfl⟩ : syracuseStep 3770927 = 5656391) B5656391
theorem B7178813 : Blo 1116628 7178813 := bstep (se 3 (by rfl) ⟨1346027, by rfl⟩ : syracuseStep 7178813 = 2692055) B2692055
theorem B1116831 : Blo 1116628 1116831 := bstep (se 1 (by rfl) ⟨837623, by rfl⟩ : syracuseStep 1116831 = 1675247) B1675247
theorem B1116839 : Blo 1116628 1116839 := bstep (se 1 (by rfl) ⟨837629, by rfl⟩ : syracuseStep 1116839 = 1675259) B1675259
theorem B1116879 : Blo 1116628 1116879 := bstep (se 1 (by rfl) ⟨837659, by rfl⟩ : syracuseStep 1116879 = 1675319) B1675319
theorem B1116911 : Blo 1116628 1116911 := bstep (se 1 (by rfl) ⟨837683, by rfl⟩ : syracuseStep 1116911 = 1675367) B1675367
theorem B1116959 : Blo 1116628 1116959 := bstep (se 1 (by rfl) ⟨837719, by rfl⟩ : syracuseStep 1116959 = 1675439) B1675439
theorem B6458255 : Blo 1116628 6458255 := bstep (se 1 (by rfl) ⟨4843691, by rfl⟩ : syracuseStep 6458255 = 9687383) B9687383
theorem B1117095 : Blo 1116628 1117095 := bstep (se 1 (by rfl) ⟨837821, by rfl⟩ : syracuseStep 1117095 = 1675643) B1675643
theorem B2722727 : Blo 1116628 2722727 := bstep (se 1 (by rfl) ⟨2042045, by rfl⟩ : syracuseStep 2722727 = 4084091) B4084091
theorem B5671943 : Blo 1116628 5671943 := bstep (se 1 (by rfl) ⟨4253957, by rfl⟩ : syracuseStep 5671943 = 8507915) B8507915
theorem B7179353 : Blo 1116628 7179353 := bstep (se 2 (by rfl) ⟨2692257, by rfl⟩ : syracuseStep 7179353 = 5384515) B5384515
theorem B1117275 : Blo 1116628 1117275 := bstep (se 1 (by rfl) ⟨837956, by rfl⟩ : syracuseStep 1117275 = 1675913) B1675913
theorem B1117415 : Blo 1116628 1117415 := bstep (se 1 (by rfl) ⟨838061, by rfl⟩ : syracuseStep 1117415 = 1676123) B1676123
theorem B1117723 : Blo 1116628 1117723 := bstep (se 1 (by rfl) ⟨838292, by rfl⟩ : syracuseStep 1117723 = 1676585) B1676585
theorem B1117855 : Blo 1116628 1117855 := bstep (se 1 (by rfl) ⟨838391, by rfl⟩ : syracuseStep 1117855 = 1676783) B1676783
theorem B1675175 : Blo 1116628 1675175 := bstep (se 1 (by rfl) ⟨1256381, by rfl⟩ : syracuseStep 1675175 = 2512763) B2512763
theorem B1118119 : Blo 1116628 1118119 := bstep (se 1 (by rfl) ⟨838589, by rfl⟩ : syracuseStep 1118119 = 1677179) B1677179
theorem B1675199 : Blo 1116628 1675199 := bstep (se 1 (by rfl) ⟨1256399, by rfl⟩ : syracuseStep 1675199 = 2512799) B2512799
theorem B1118143 : Blo 1116628 1118143 := bstep (se 1 (by rfl) ⟨838607, by rfl⟩ : syracuseStep 1118143 = 1677215) B1677215
theorem B12095477 : Blo 1116628 12095477 := bstep (se 5 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 12095477 = 1133951) B1133951
theorem B31461365 : Blo 1116628 31461365 := bstep (se 5 (by rfl) ⟨1474751, by rfl⟩ : syracuseStep 31461365 = 2949503) B2949503
theorem B1675355 : Blo 1116628 1675355 := bstep (se 1 (by rfl) ⟨1256516, by rfl⟩ : syracuseStep 1675355 = 2513033) B2513033
theorem B1118299 : Blo 1116628 1118299 := bstep (se 1 (by rfl) ⟨838724, by rfl⟩ : syracuseStep 1118299 = 1677449) B1677449
theorem B1118399 : Blo 1116628 1118399 := bstep (se 1 (by rfl) ⟨838799, by rfl⟩ : syracuseStep 1118399 = 1677599) B1677599
theorem B1675499 : Blo 1116628 1675499 := bstep (se 1 (by rfl) ⟨1256624, by rfl⟩ : syracuseStep 1675499 = 2513249) B2513249
theorem B1675559 : Blo 1116628 1675559 := bstep (se 1 (by rfl) ⟨1256669, by rfl⟩ : syracuseStep 1675559 = 2513339) B2513339
theorem B3182951 : Blo 1116628 3182951 := bstep (se 1 (by rfl) ⟨2387213, by rfl⟩ : syracuseStep 3182951 = 4774427) B4774427
theorem B2691575 : Blo 1116628 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B1675823 : Blo 1116628 1675823 := bstep (se 1 (by rfl) ⟨1256867, by rfl⟩ : syracuseStep 1675823 = 2513735) B2513735
theorem B1118767 : Blo 1116628 1118767 := bstep (se 1 (by rfl) ⟨839075, by rfl⟩ : syracuseStep 1118767 = 1678151) B1678151
theorem B3019393 : Blo 1116628 3019393 := bstep (se 2 (by rfl) ⟨1132272, by rfl⟩ : syracuseStep 3019393 = 2264545) B2264545
theorem B1676027 : Blo 1116628 1676027 := bstep (se 1 (by rfl) ⟨1257020, by rfl⟩ : syracuseStep 1676027 = 2514041) B2514041
theorem B1414255 : Blo 1116628 1414255 := bstep (se 1 (by rfl) ⟨1060691, by rfl⟩ : syracuseStep 1414255 = 2121383) B2121383
theorem B1676399 : Blo 1116628 1676399 := bstep (se 1 (by rfl) ⟨1257299, by rfl⟩ : syracuseStep 1676399 = 2514599) B2514599
theorem B1119343 : Blo 1116628 1119343 := bstep (se 1 (by rfl) ⟨839507, by rfl⟩ : syracuseStep 1119343 = 1679015) B1679015
theorem B1676471 : Blo 1116628 1676471 := bstep (se 1 (by rfl) ⟨1257353, by rfl⟩ : syracuseStep 1676471 = 2514707) B2514707
theorem B1119423 : Blo 1116628 1119423 := bstep (se 1 (by rfl) ⟨839567, by rfl⟩ : syracuseStep 1119423 = 1679135) B1679135
theorem B6362347 : Blo 1116628 6362347 := bstep (se 1 (by rfl) ⟨4771760, by rfl⟩ : syracuseStep 6362347 = 9543521) B9543521
theorem B1676711 : Blo 1116628 1676711 := bstep (se 1 (by rfl) ⟨1257533, by rfl⟩ : syracuseStep 1676711 = 2515067) B2515067
theorem B5379497 : Blo 1116628 5379497 := bstep (se 2 (by rfl) ⟨2017311, by rfl⟩ : syracuseStep 5379497 = 4034623) B4034623
theorem B4036007 : Blo 1116628 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B1119711 : Blo 1116628 1119711 := bstep (se 1 (by rfl) ⟨839783, by rfl⟩ : syracuseStep 1119711 = 1679567) B1679567
theorem B3773951 : Blo 1116628 3773951 := bstep (se 1 (by rfl) ⟨2830463, by rfl⟩ : syracuseStep 3773951 = 5660927) B5660927
theorem B1119743 : Blo 1116628 1119743 := bstep (se 1 (by rfl) ⟨839807, by rfl⟩ : syracuseStep 1119743 = 1679615) B1679615
theorem B1676891 : Blo 1116628 1676891 := bstep (se 1 (by rfl) ⟨1257668, by rfl⟩ : syracuseStep 1676891 = 2515337) B2515337
theorem B3774329 : Blo 1116628 3774329 := bstep (se 2 (by rfl) ⟨1415373, by rfl⟩ : syracuseStep 3774329 = 2830747) B2830747
theorem B1120287 : Blo 1116628 1120287 := bstep (se 1 (by rfl) ⟨840215, by rfl⟩ : syracuseStep 1120287 = 1680431) B1680431
theorem B1120367 : Blo 1116628 1120367 := bstep (se 1 (by rfl) ⟨840275, by rfl⟩ : syracuseStep 1120367 = 1680551) B1680551
theorem B1677647 : Blo 1116628 1677647 := bstep (se 1 (by rfl) ⟨1258235, by rfl⟩ : syracuseStep 1677647 = 2516471) B2516471
theorem B1677671 : Blo 1116628 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B1120615 : Blo 1116628 1120615 := bstep (se 1 (by rfl) ⟨840461, by rfl⟩ : syracuseStep 1120615 = 1680923) B1680923
theorem B1677737 : Blo 1116628 1677737 := bstep (se 2 (by rfl) ⟨629151, by rfl⟩ : syracuseStep 1677737 = 1258303) B1258303
theorem B1678121 : Blo 1116628 1678121 := bstep (se 2 (by rfl) ⟨629295, by rfl⟩ : syracuseStep 1678121 = 1258591) B1258591
theorem B1678331 : Blo 1116628 1678331 := bstep (se 1 (by rfl) ⟨1258748, by rfl⟩ : syracuseStep 1678331 = 2517497) B2517497
theorem B1678367 : Blo 1116628 1678367 := bstep (se 1 (by rfl) ⟨1258775, by rfl⟩ : syracuseStep 1678367 = 2517551) B2517551
theorem B1678391 : Blo 1116628 1678391 := bstep (se 1 (by rfl) ⟨1258793, by rfl⟩ : syracuseStep 1678391 = 2517587) B2517587
theorem B1678511 : Blo 1116628 1678511 := bstep (se 1 (by rfl) ⟨1258883, by rfl⟩ : syracuseStep 1678511 = 2517767) B2517767
theorem B6036713 : Blo 1116628 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B1678655 : Blo 1116628 1678655 := bstep (se 1 (by rfl) ⟨1258991, by rfl⟩ : syracuseStep 1678655 = 2517983) B2517983
theorem B1678799 : Blo 1116628 1678799 := bstep (se 1 (by rfl) ⟨1259099, by rfl⟩ : syracuseStep 1678799 = 2518199) B2518199
theorem B6364763 : Blo 1116628 6364763 := bstep (se 1 (by rfl) ⟨4773572, by rfl⟩ : syracuseStep 6364763 = 9547145) B9547145
theorem B1679183 : Blo 1116628 1679183 := bstep (se 1 (by rfl) ⟨1259387, by rfl⟩ : syracuseStep 1679183 = 2518775) B2518775
theorem B1679231 : Blo 1116628 1679231 := bstep (se 1 (by rfl) ⟨1259423, by rfl⟩ : syracuseStep 1679231 = 2518847) B2518847
theorem B1679303 : Blo 1116628 1679303 := bstep (se 1 (by rfl) ⟨1259477, by rfl⟩ : syracuseStep 1679303 = 2518955) B2518955
theorem B1679543 : Blo 1116628 1679543 := bstep (se 1 (by rfl) ⟨1259657, by rfl⟩ : syracuseStep 1679543 = 2519315) B2519315
theorem B1679663 : Blo 1116628 1679663 := bstep (se 1 (by rfl) ⟨1259747, by rfl⟩ : syracuseStep 1679663 = 2519495) B2519495
theorem B5382611 : Blo 1116628 5382611 := bstep (se 1 (by rfl) ⟨4036958, by rfl⟩ : syracuseStep 5382611 = 8073917) B8073917
theorem B1679903 : Blo 1116628 1679903 := bstep (se 1 (by rfl) ⟨1259927, by rfl⟩ : syracuseStep 1679903 = 2519855) B2519855
theorem B1679963 : Blo 1116628 1679963 := bstep (se 1 (by rfl) ⟨1259972, by rfl⟩ : syracuseStep 1679963 = 2519945) B2519945
theorem B1417819 : Blo 1116628 1417819 := bstep (se 1 (by rfl) ⟨1063364, by rfl⟩ : syracuseStep 1417819 = 2126729) B2126729
theorem B18162413 : Blo 1116628 18162413 := bstep (se 3 (by rfl) ⟨3405452, by rfl⟩ : syracuseStep 18162413 = 6810905) B6810905
theorem B3777407 : Blo 1116628 3777407 := bstep (se 1 (by rfl) ⟨2833055, by rfl⟩ : syracuseStep 3777407 = 5666111) B5666111
theorem B1680479 : Blo 1116628 1680479 := bstep (se 1 (by rfl) ⟨1260359, by rfl⟩ : syracuseStep 1680479 = 2520719) B2520719
theorem B1680539 : Blo 1116628 1680539 := bstep (se 1 (by rfl) ⟨1260404, by rfl⟩ : syracuseStep 1680539 = 2520809) B2520809
theorem B3777839 : Blo 1116628 3777839 := bstep (se 1 (by rfl) ⟨2833379, by rfl⟩ : syracuseStep 3777839 = 5666759) B5666759
theorem B2828267 : Blo 1116628 2828267 := bstep (se 1 (by rfl) ⟨2121200, by rfl⟩ : syracuseStep 2828267 = 4242401) B4242401
theorem B3778703 : Blo 1116628 3778703 := bstep (se 1 (by rfl) ⟨2834027, by rfl⟩ : syracuseStep 3778703 = 5668055) B5668055
theorem B5384531 : Blo 1116628 5384531 := bstep (se 1 (by rfl) ⟨4038398, by rfl⟩ : syracuseStep 5384531 = 8076797) B8076797
theorem B19114379 : Blo 1116628 19114379 := bstep (se 1 (by rfl) ⟨14335784, by rfl⟩ : syracuseStep 19114379 = 28671569) B28671569
theorem B24160679 : Blo 1116628 24160679 := bstep (se 1 (by rfl) ⟨18120509, by rfl⟩ : syracuseStep 24160679 = 36241019) B36241019
theorem B3582397 : Blo 1116628 3582397 := bstep (se 3 (by rfl) ⟨671699, by rfl⟩ : syracuseStep 3582397 = 1343399) B1343399
theorem B3189239 : Blo 1116628 3189239 := bstep (se 1 (by rfl) ⟨2391929, by rfl⟩ : syracuseStep 3189239 = 4783859) B4783859
theorem B2829127 : Blo 1116628 2829127 := bstep (se 1 (by rfl) ⟨2121845, by rfl⟩ : syracuseStep 2829127 = 4243691) B4243691
theorem B1256863 : Blo 1116628 1256863 := bstep (se 1 (by rfl) ⟨942647, by rfl⟩ : syracuseStep 1256863 = 1885295) B1885295
theorem B3190241 : Blo 1116628 3190241 := bstep (se 2 (by rfl) ⟨1196340, by rfl⟩ : syracuseStep 3190241 = 2392681) B2392681
theorem B1257151 : Blo 1116628 1257151 := bstep (se 1 (by rfl) ⟨942863, by rfl⟩ : syracuseStep 1257151 = 1885727) B1885727
theorem B7254035 : Blo 1116628 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B1257727 : Blo 1116628 1257727 := bstep (se 1 (by rfl) ⟨943295, by rfl⟩ : syracuseStep 1257727 = 1886591) B1886591
theorem B3780863 : Blo 1116628 3780863 := bstep (se 1 (by rfl) ⟨2835647, by rfl⟩ : syracuseStep 3780863 = 5671295) B5671295
theorem B3191039 : Blo 1116628 3191039 := bstep (se 1 (by rfl) ⟨2393279, by rfl⟩ : syracuseStep 3191039 = 4786559) B4786559
theorem B1258879 : Blo 1116628 1258879 := bstep (se 1 (by rfl) ⟨944159, by rfl⟩ : syracuseStep 1258879 = 1888319) B1888319
theorem B1259455 : Blo 1116628 1259455 := bstep (se 1 (by rfl) ⟨944591, by rfl⟩ : syracuseStep 1259455 = 1889183) B1889183
theorem B6371369 : Blo 1116628 6371369 := bstep (se 2 (by rfl) ⟨2389263, by rfl⟩ : syracuseStep 6371369 = 4778527) B4778527
theorem B5093513 : Blo 1116628 5093513 := bstep (se 2 (by rfl) ⟨1910067, by rfl⟩ : syracuseStep 5093513 = 3820135) B3820135
theorem B2013751 : Blo 1116628 2013751 := bstep (se 1 (by rfl) ⟨1510313, by rfl⟩ : syracuseStep 2013751 = 3020627) B3020627
theorem B4242233 : Blo 1116628 4242233 := bstep (se 2 (by rfl) ⟨1590837, by rfl⟩ : syracuseStep 4242233 = 3181675) B3181675
theorem B4242415 : Blo 1116628 4242415 := bstep (se 1 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 4242415 = 6363623) B6363623
theorem B2833481 : Blo 1116628 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B7651219 : Blo 1116628 7651219 := bstep (se 1 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 7651219 = 11476829) B11476829
theorem B2834423 : Blo 1116628 2834423 := bstep (se 1 (by rfl) ⟨2125817, by rfl⟩ : syracuseStep 2834423 = 4251635) B4251635
theorem B30621827 : Blo 1116628 30621827 := bstep (se 1 (by rfl) ⟨22966370, by rfl⟩ : syracuseStep 30621827 = 45932741) B45932741
theorem B6373511 : Blo 1116628 6373511 := bstep (se 1 (by rfl) ⟨4780133, by rfl⟩ : syracuseStep 6373511 = 9560267) B9560267
theorem B1884647 : Blo 1116628 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B6374011 : Blo 1116628 6374011 := bstep (se 1 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 6374011 = 9561017) B9561017
theorem B7651979 : Blo 1116628 7651979 := bstep (se 1 (by rfl) ⟨5738984, by rfl⟩ : syracuseStep 7651979 = 11477969) B11477969
theorem B2835719 : Blo 1116628 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B2836367 : Blo 1116628 2836367 := bstep (se 1 (by rfl) ⟨2127275, by rfl⟩ : syracuseStep 2836367 = 4254551) B4254551
theorem B1132751 : Blo 1116628 1132751 := bstep (se 1 (by rfl) ⟨849563, by rfl⟩ : syracuseStep 1132751 = 1699127) B1699127
theorem B12732713 : Blo 1116628 12732713 := bstep (se 2 (by rfl) ⟨4774767, by rfl⟩ : syracuseStep 12732713 = 9549535) B9549535
theorem B4541903 : Blo 1116628 4541903 := bstep (se 1 (by rfl) ⟨3406427, by rfl⟩ : syracuseStep 4541903 = 6812855) B6812855
theorem B12079211 : Blo 1116628 12079211 := bstep (se 1 (by rfl) ⟨9059408, by rfl⟩ : syracuseStep 12079211 = 18118817) B18118817
theorem B5656715 : Blo 1116628 5656715 := bstep (se 1 (by rfl) ⟨4242536, by rfl⟩ : syracuseStep 5656715 = 8485073) B8485073
theorem B1888879 : Blo 1116628 1888879 := bstep (se 1 (by rfl) ⟨1416659, by rfl⟩ : syracuseStep 1888879 = 2833319) B2833319
theorem B3822815 : Blo 1116628 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B77518397 : Blo 1116628 77518397 := bstep (se 3 (by rfl) ⟨14534699, by rfl⟩ : syracuseStep 77518397 = 29069399) B29069399
theorem B14538395 : Blo 1116628 14538395 := bstep (se 1 (by rfl) ⟨10903796, by rfl⟩ : syracuseStep 14538395 = 21807593) B21807593
theorem B5658335 : Blo 1116628 5658335 := bstep (se 1 (by rfl) ⟨4243751, by rfl⟩ : syracuseStep 5658335 = 8487503) B8487503
theorem B7165691 : Blo 1116628 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B8509373 : Blo 1116628 8509373 := bstep (se 3 (by rfl) ⟨1595507, by rfl⟩ : syracuseStep 8509373 = 3191015) B3191015
theorem B11491433 : Blo 1116628 11491433 := bstep (se 2 (by rfl) ⟨4309287, by rfl⟩ : syracuseStep 11491433 = 8618575) B8618575
theorem B2119871 : Blo 1116628 2119871 := bstep (se 1 (by rfl) ⟨1589903, by rfl⟩ : syracuseStep 2119871 = 3179807) B3179807
theorem B2513087 : Blo 1116628 2513087 := bstep (se 1 (by rfl) ⟨1884815, by rfl⟩ : syracuseStep 2513087 = 3769631) B3769631
theorem B1890587 : Blo 1116628 1890587 := bstep (se 1 (by rfl) ⟨1417940, by rfl⟩ : syracuseStep 1890587 = 2835881) B2835881
theorem B16144829 : Blo 1116628 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B7166717 : Blo 1116628 7166717 := bstep (se 3 (by rfl) ⟨1343759, by rfl⟩ : syracuseStep 7166717 = 2687519) B2687519
theorem B1792871 : Blo 1116628 1792871 := bstep (se 1 (by rfl) ⟨1344653, by rfl⟩ : syracuseStep 1792871 = 2689307) B2689307
theorem B45964421 : Blo 1116628 45964421 := bstep (se 4 (by rfl) ⟨4309164, by rfl⟩ : syracuseStep 45964421 = 8618329) B8618329
theorem B4775111 : Blo 1116628 4775111 := bstep (se 1 (by rfl) ⟨3581333, by rfl⟩ : syracuseStep 4775111 = 7162667) B7162667
theorem B2514131 : Blo 1116628 2514131 := bstep (se 1 (by rfl) ⟨1885598, by rfl⟩ : syracuseStep 2514131 = 3771197) B3771197
theorem B2514203 : Blo 1116628 2514203 := bstep (se 1 (by rfl) ⟨1885652, by rfl⟩ : syracuseStep 2514203 = 3771305) B3771305
theorem B4250951 : Blo 1116628 4250951 := bstep (se 1 (by rfl) ⟨3188213, by rfl⟩ : syracuseStep 4250951 = 6376427) B6376427
theorem B30596525 : Blo 1116628 30596525 := bstep (se 3 (by rfl) ⟨5736848, by rfl⟩ : syracuseStep 30596525 = 11473697) B11473697
theorem B2514401 : Blo 1116628 2514401 := bstep (se 2 (by rfl) ⟨942900, by rfl⟩ : syracuseStep 2514401 = 1885801) B1885801
theorem B6381119 : Blo 1116628 6381119 := bstep (se 1 (by rfl) ⟨4785839, by rfl⟩ : syracuseStep 6381119 = 9571679) B9571679
theorem B3399421 : Blo 1116628 3399421 := bstep (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) B1274783
theorem B2515193 : Blo 1116628 2515193 := bstep (se 2 (by rfl) ⟨943197, by rfl⟩ : syracuseStep 2515193 = 1886395) B1886395
theorem B5661089 : Blo 1116628 5661089 := bstep (se 2 (by rfl) ⟨2122908, by rfl⟩ : syracuseStep 5661089 = 4245817) B4245817
theorem B2515463 : Blo 1116628 2515463 := bstep (se 1 (by rfl) ⟨1886597, by rfl⟩ : syracuseStep 2515463 = 3773195) B3773195
theorem B2515643 : Blo 1116628 2515643 := bstep (se 1 (by rfl) ⟨1886732, by rfl⟩ : syracuseStep 2515643 = 3773465) B3773465
theorem B1794793 : Blo 1116628 1794793 := bstep (se 2 (by rfl) ⟨673047, by rfl⟩ : syracuseStep 1794793 = 1346095) B1346095
theorem B2122537 : Blo 1116628 2122537 := bstep (se 2 (by rfl) ⟨795951, by rfl⟩ : syracuseStep 2122537 = 1591903) B1591903
theorem B2516129 : Blo 1116628 2516129 := bstep (se 2 (by rfl) ⟨943548, by rfl⟩ : syracuseStep 2516129 = 1887097) B1887097
theorem B14345423 : Blo 1116628 14345423 := bstep (se 1 (by rfl) ⟨10759067, by rfl⟩ : syracuseStep 14345423 = 21518135) B21518135
theorem B2385121 : Blo 1116628 2385121 := bstep (se 2 (by rfl) ⟨894420, by rfl⟩ : syracuseStep 2385121 = 1788841) B1788841
theorem B2123327 : Blo 1116628 2123327 := bstep (se 1 (by rfl) ⟨1592495, by rfl⟩ : syracuseStep 2123327 = 3184991) B3184991
theorem B2516543 : Blo 1116628 2516543 := bstep (se 1 (by rfl) ⟨1887407, by rfl⟩ : syracuseStep 2516543 = 3774815) B3774815
theorem B2516651 : Blo 1116628 2516651 := bstep (se 1 (by rfl) ⟨1887488, by rfl⟩ : syracuseStep 2516651 = 3774977) B3774977
theorem B4777775 : Blo 1116628 4777775 := bstep (se 1 (by rfl) ⟨3583331, by rfl⟩ : syracuseStep 4777775 = 7166663) B7166663
theorem B2516903 : Blo 1116628 2516903 := bstep (se 1 (by rfl) ⟨1887677, by rfl⟩ : syracuseStep 2516903 = 3775355) B3775355
theorem B39217097 : Blo 1116628 39217097 := bstep (se 2 (by rfl) ⟨14706411, by rfl⟩ : syracuseStep 39217097 = 29412823) B29412823
theorem B2517191 : Blo 1116628 2517191 := bstep (se 1 (by rfl) ⟨1887893, by rfl⟩ : syracuseStep 2517191 = 3775787) B3775787
theorem B2517371 : Blo 1116628 2517371 := bstep (se 1 (by rfl) ⟨1888028, by rfl⟩ : syracuseStep 2517371 = 3776057) B3776057
theorem B2517479 : Blo 1116628 2517479 := bstep (se 1 (by rfl) ⟨1888109, by rfl⟩ : syracuseStep 2517479 = 3776219) B3776219
theorem B2517641 : Blo 1116628 2517641 := bstep (se 2 (by rfl) ⟨944115, by rfl⟩ : syracuseStep 2517641 = 1888231) B1888231
theorem B2517659 : Blo 1116628 2517659 := bstep (se 1 (by rfl) ⟨1888244, by rfl⟩ : syracuseStep 2517659 = 3776489) B3776489
theorem B2124443 : Blo 1116628 2124443 := bstep (se 1 (by rfl) ⟨1593332, by rfl⟩ : syracuseStep 2124443 = 3186665) B3186665
theorem B12086441 : Blo 1116628 12086441 := bstep (se 2 (by rfl) ⟨4532415, by rfl⟩ : syracuseStep 12086441 = 9064831) B9064831
theorem B8056037 : Blo 1116628 8056037 := bstep (se 4 (by rfl) ⟨755253, by rfl⟩ : syracuseStep 8056037 = 1510507) B1510507
theorem B2387179 : Blo 1116628 2387179 := bstep (se 1 (by rfl) ⟨1790384, by rfl⟩ : syracuseStep 2387179 = 3580769) B3580769
theorem B529952033 : Blo 1116628 529952033 := bstep (se 2 (by rfl) ⟨198732012, by rfl⟩ : syracuseStep 529952033 = 397464025) B397464025
theorem B7171379 : Blo 1116628 7171379 := bstep (se 1 (by rfl) ⟨5378534, by rfl⟩ : syracuseStep 7171379 = 10757069) B10757069
theorem B5664167 : Blo 1116628 5664167 := bstep (se 1 (by rfl) ⟨4248125, by rfl⟩ : syracuseStep 5664167 = 8496251) B8496251
theorem B10219067 : Blo 1116628 10219067 := bstep (se 1 (by rfl) ⟨7664300, by rfl⟩ : syracuseStep 10219067 = 15328601) B15328601
theorem B2518631 : Blo 1116628 2518631 := bstep (se 1 (by rfl) ⟨1888973, by rfl⟩ : syracuseStep 2518631 = 3777947) B3777947
theorem B2125415 : Blo 1116628 2125415 := bstep (se 1 (by rfl) ⟨1594061, by rfl⟩ : syracuseStep 2125415 = 3188123) B3188123
theorem B5730281 : Blo 1116628 5730281 := bstep (se 2 (by rfl) ⟨2148855, by rfl⟩ : syracuseStep 5730281 = 4297711) B4297711
theorem B2387999 : Blo 1116628 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B2125855 : Blo 1116628 2125855 := bstep (se 1 (by rfl) ⟨1594391, by rfl⟩ : syracuseStep 2125855 = 3188783) B3188783
theorem B77591297 : Blo 1116628 77591297 := bstep (se 2 (by rfl) ⟨29096736, by rfl⟩ : syracuseStep 77591297 = 58193473) B58193473
theorem B11465657 : Blo 1116628 11465657 := bstep (se 2 (by rfl) ⟨4299621, by rfl⟩ : syracuseStep 11465657 = 8599243) B8599243
theorem B13629019 : Blo 1116628 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B2521115 : Blo 1116628 2521115 := bstep (se 1 (by rfl) ⟨1890836, by rfl⟩ : syracuseStep 2521115 = 3781673) B3781673
theorem B13073537 : Blo 1116628 13073537 := bstep (se 2 (by rfl) ⟨4902576, by rfl⟩ : syracuseStep 13073537 = 9805153) B9805153
theorem B21528281 : Blo 1116628 21528281 := bstep (se 2 (by rfl) ⟨8073105, by rfl⟩ : syracuseStep 21528281 = 16146211) B16146211
theorem B32211229 : Blo 1116628 32211229 := bstep (se 3 (by rfl) ⟨6039605, by rfl⟩ : syracuseStep 32211229 = 12079211) B12079211
theorem B81658205 : Blo 1116628 81658205 := bstep (se 3 (by rfl) ⟨15310913, by rfl⟩ : syracuseStep 81658205 = 30621827) B30621827
theorem B2393057 : Blo 1116628 2393057 := bstep (se 2 (by rfl) ⟨897396, by rfl⟩ : syracuseStep 2393057 = 1794793) B1794793
theorem B8488475 : Blo 1116628 8488475 := bstep (se 1 (by rfl) ⟨6366356, by rfl⟩ : syracuseStep 8488475 = 12732713) B12732713
theorem B3180161 : Blo 1116628 3180161 := bstep (se 2 (by rfl) ⟨1192560, by rfl⟩ : syracuseStep 3180161 = 2385121) B2385121
theorem B4785875 : Blo 1116628 4785875 := bstep (se 1 (by rfl) ⟨3589406, by rfl⟩ : syracuseStep 4785875 = 7178813) B7178813
theorem B4786235 : Blo 1116628 4786235 := bstep (se 1 (by rfl) ⟨3589676, by rfl⟩ : syracuseStep 4786235 = 7179353) B7179353
theorem B1116783 : Blo 1116628 1116783 := bstep (se 1 (by rfl) ⟨837587, by rfl⟩ : syracuseStep 1116783 = 1675175) B1675175
theorem B1116799 : Blo 1116628 1116799 := bstep (se 1 (by rfl) ⟨837599, by rfl⟩ : syracuseStep 1116799 = 1675199) B1675199
theorem B8063651 : Blo 1116628 8063651 := bstep (se 1 (by rfl) ⟨6047738, by rfl⟩ : syracuseStep 8063651 = 12095477) B12095477
theorem B20974243 : Blo 1116628 20974243 := bstep (se 1 (by rfl) ⟨15730682, by rfl⟩ : syracuseStep 20974243 = 31461365) B31461365
theorem B1116903 : Blo 1116628 1116903 := bstep (se 1 (by rfl) ⟨837677, by rfl⟩ : syracuseStep 1116903 = 1675355) B1675355
theorem B3771143 : Blo 1116628 3771143 := bstep (se 1 (by rfl) ⟨2828357, by rfl⟩ : syracuseStep 3771143 = 5656715) B5656715
theorem B1116999 : Blo 1116628 1116999 := bstep (se 1 (by rfl) ⟨837749, by rfl⟩ : syracuseStep 1116999 = 1675499) B1675499
theorem B1117039 : Blo 1116628 1117039 := bstep (se 1 (by rfl) ⟨837779, by rfl⟩ : syracuseStep 1117039 = 1675559) B1675559
theorem B1117215 : Blo 1116628 1117215 := bstep (se 1 (by rfl) ⟨837911, by rfl⟩ : syracuseStep 1117215 = 1675823) B1675823
theorem B1117351 : Blo 1116628 1117351 := bstep (se 1 (by rfl) ⟨838013, by rfl⟩ : syracuseStep 1117351 = 1676027) B1676027
theorem B10194173 : Blo 1116628 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B1117599 : Blo 1116628 1117599 := bstep (se 1 (by rfl) ⟨838199, by rfl⟩ : syracuseStep 1117599 = 1676399) B1676399
theorem B1117647 : Blo 1116628 1117647 := bstep (se 1 (by rfl) ⟨838235, by rfl⟩ : syracuseStep 1117647 = 1676471) B1676471
theorem B1117807 : Blo 1116628 1117807 := bstep (se 1 (by rfl) ⟨838355, by rfl⟩ : syracuseStep 1117807 = 1676711) B1676711
theorem B2690671 : Blo 1116628 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B51678931 : Blo 1116628 51678931 := bstep (se 1 (by rfl) ⟨38759198, by rfl⟩ : syracuseStep 51678931 = 77518397) B77518397
theorem B1117927 : Blo 1116628 1117927 := bstep (se 1 (by rfl) ⟨838445, by rfl⟩ : syracuseStep 1117927 = 1676891) B1676891
theorem B3772169 : Blo 1116628 3772169 := bstep (se 2 (by rfl) ⟨1414563, by rfl⟩ : syracuseStep 3772169 = 2829127) B2829127
theorem B3772223 : Blo 1116628 3772223 := bstep (se 1 (by rfl) ⟨2829167, by rfl⟩ : syracuseStep 3772223 = 5658335) B5658335
theorem B5672915 : Blo 1116628 5672915 := bstep (se 1 (by rfl) ⟨4254686, by rfl⟩ : syracuseStep 5672915 = 8509373) B8509373
theorem B1675391 : Blo 1116628 1675391 := bstep (se 1 (by rfl) ⟨1256543, by rfl⟩ : syracuseStep 1675391 = 2513087) B2513087
theorem B1118431 : Blo 1116628 1118431 := bstep (se 1 (by rfl) ⟨838823, by rfl⟩ : syracuseStep 1118431 = 1677647) B1677647
theorem B1118447 : Blo 1116628 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B1118491 : Blo 1116628 1118491 := bstep (se 1 (by rfl) ⟨838868, by rfl⟩ : syracuseStep 1118491 = 1677737) B1677737
theorem B3182905 : Blo 1116628 3182905 := bstep (se 2 (by rfl) ⟨1193589, by rfl⟩ : syracuseStep 3182905 = 2387179) B2387179
theorem B1118747 : Blo 1116628 1118747 := bstep (se 1 (by rfl) ⟨839060, by rfl⟩ : syracuseStep 1118747 = 1678121) B1678121
theorem B1675817 : Blo 1116628 1675817 := bstep (se 2 (by rfl) ⟨628431, by rfl⟩ : syracuseStep 1675817 = 1256863) B1256863
theorem B1118887 : Blo 1116628 1118887 := bstep (se 1 (by rfl) ⟨839165, by rfl⟩ : syracuseStep 1118887 = 1678331) B1678331
theorem B1118911 : Blo 1116628 1118911 := bstep (se 1 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 1118911 = 1678367) B1678367
theorem B1118927 : Blo 1116628 1118927 := bstep (se 1 (by rfl) ⟨839195, by rfl⟩ : syracuseStep 1118927 = 1678391) B1678391
theorem B30642947 : Blo 1116628 30642947 := bstep (se 1 (by rfl) ⟨22982210, by rfl⟩ : syracuseStep 30642947 = 45964421) B45964421
theorem B1119007 : Blo 1116628 1119007 := bstep (se 1 (by rfl) ⟨839255, by rfl⟩ : syracuseStep 1119007 = 1678511) B1678511
theorem B3183407 : Blo 1116628 3183407 := bstep (se 1 (by rfl) ⟨2387555, by rfl⟩ : syracuseStep 3183407 = 4775111) B4775111
theorem B1676087 : Blo 1116628 1676087 := bstep (se 1 (by rfl) ⟨1257065, by rfl⟩ : syracuseStep 1676087 = 2514131) B2514131
theorem B1676135 : Blo 1116628 1676135 := bstep (se 1 (by rfl) ⟨1257101, by rfl⟩ : syracuseStep 1676135 = 2514203) B2514203
theorem B1119103 : Blo 1116628 1119103 := bstep (se 1 (by rfl) ⟨839327, by rfl⟩ : syracuseStep 1119103 = 1678655) B1678655
theorem B1676201 : Blo 1116628 1676201 := bstep (se 2 (by rfl) ⟨628575, by rfl⟩ : syracuseStep 1676201 = 1257151) B1257151
theorem B1119199 : Blo 1116628 1119199 := bstep (se 1 (by rfl) ⟨839399, by rfl⟩ : syracuseStep 1119199 = 1678799) B1678799
theorem B1676267 : Blo 1116628 1676267 := bstep (se 1 (by rfl) ⟨1257200, by rfl⟩ : syracuseStep 1676267 = 2514401) B2514401
theorem B1119455 : Blo 1116628 1119455 := bstep (se 1 (by rfl) ⟨839591, by rfl⟩ : syracuseStep 1119455 = 1679183) B1679183
theorem B1119487 : Blo 1116628 1119487 := bstep (se 1 (by rfl) ⟨839615, by rfl⟩ : syracuseStep 1119487 = 1679231) B1679231
theorem B1119535 : Blo 1116628 1119535 := bstep (se 1 (by rfl) ⟨839651, by rfl⟩ : syracuseStep 1119535 = 1679303) B1679303
theorem B1119695 : Blo 1116628 1119695 := bstep (se 1 (by rfl) ⟨839771, by rfl⟩ : syracuseStep 1119695 = 1679543) B1679543
theorem B1676795 : Blo 1116628 1676795 := bstep (se 1 (by rfl) ⟨1257596, by rfl⟩ : syracuseStep 1676795 = 2515193) B2515193
theorem B1119775 : Blo 1116628 1119775 := bstep (se 1 (by rfl) ⟨839831, by rfl⟩ : syracuseStep 1119775 = 1679663) B1679663
theorem B3774059 : Blo 1116628 3774059 := bstep (se 1 (by rfl) ⟨2830544, by rfl⟩ : syracuseStep 3774059 = 5661089) B5661089
theorem B1676969 : Blo 1116628 1676969 := bstep (se 2 (by rfl) ⟨628863, by rfl⟩ : syracuseStep 1676969 = 1257727) B1257727
theorem B1676975 : Blo 1116628 1676975 := bstep (se 1 (by rfl) ⟨1257731, by rfl⟩ : syracuseStep 1676975 = 2515463) B2515463
theorem B1119935 : Blo 1116628 1119935 := bstep (se 1 (by rfl) ⟨839951, by rfl⟩ : syracuseStep 1119935 = 1679903) B1679903
theorem B1119975 : Blo 1116628 1119975 := bstep (se 1 (by rfl) ⟨839981, by rfl⟩ : syracuseStep 1119975 = 1679963) B1679963
theorem B1677095 : Blo 1116628 1677095 := bstep (se 1 (by rfl) ⟨1257821, by rfl⟩ : syracuseStep 1677095 = 2515643) B2515643
theorem B3020669 : Blo 1116628 3020669 := bstep (se 3 (by rfl) ⟨566375, by rfl⟩ : syracuseStep 3020669 = 1132751) B1132751
theorem B1120319 : Blo 1116628 1120319 := bstep (se 1 (by rfl) ⟨840239, by rfl⟩ : syracuseStep 1120319 = 1680479) B1680479
theorem B1120359 : Blo 1116628 1120359 := bstep (se 1 (by rfl) ⟨840269, by rfl⟩ : syracuseStep 1120359 = 1680539) B1680539
theorem B1677419 : Blo 1116628 1677419 := bstep (se 1 (by rfl) ⟨1258064, by rfl⟩ : syracuseStep 1677419 = 2516129) B2516129
theorem B1415551 : Blo 1116628 1415551 := bstep (se 1 (by rfl) ⟨1061663, by rfl⟩ : syracuseStep 1415551 = 2123327) B2123327
theorem B1677695 : Blo 1116628 1677695 := bstep (se 1 (by rfl) ⟨1258271, by rfl⟩ : syracuseStep 1677695 = 2516543) B2516543
theorem B1677767 : Blo 1116628 1677767 := bstep (se 1 (by rfl) ⟨1258325, by rfl⟩ : syracuseStep 1677767 = 2516651) B2516651
theorem B3185183 : Blo 1116628 3185183 := bstep (se 1 (by rfl) ⟨2388887, by rfl⟩ : syracuseStep 3185183 = 4777775) B4777775
theorem B1677935 : Blo 1116628 1677935 := bstep (se 1 (by rfl) ⟨1258451, by rfl⟩ : syracuseStep 1677935 = 2516903) B2516903
theorem B1678127 : Blo 1116628 1678127 := bstep (se 1 (by rfl) ⟨1258595, by rfl⟩ : syracuseStep 1678127 = 2517191) B2517191
theorem B1678247 : Blo 1116628 1678247 := bstep (se 1 (by rfl) ⟨1258685, by rfl⟩ : syracuseStep 1678247 = 2517371) B2517371
theorem B1678319 : Blo 1116628 1678319 := bstep (se 1 (by rfl) ⟨1258739, by rfl⟩ : syracuseStep 1678319 = 2517479) B2517479
theorem B1678427 : Blo 1116628 1678427 := bstep (se 1 (by rfl) ⟨1258820, by rfl⟩ : syracuseStep 1678427 = 2517641) B2517641
theorem B1678439 : Blo 1116628 1678439 := bstep (se 1 (by rfl) ⟨1258829, by rfl⟩ : syracuseStep 1678439 = 2517659) B2517659
theorem B1416295 : Blo 1116628 1416295 := bstep (se 1 (by rfl) ⟨1062221, by rfl⟩ : syracuseStep 1416295 = 2124443) B2124443
theorem B1678505 : Blo 1116628 1678505 := bstep (se 2 (by rfl) ⟨629439, by rfl⟩ : syracuseStep 1678505 = 1258879) B1258879
theorem B3776111 : Blo 1116628 3776111 := bstep (se 1 (by rfl) ⟨2832083, by rfl⟩ : syracuseStep 3776111 = 5664167) B5664167
theorem B1679087 : Blo 1116628 1679087 := bstep (se 1 (by rfl) ⟨1259315, by rfl⟩ : syracuseStep 1679087 = 2518631) B2518631
theorem B1416943 : Blo 1116628 1416943 := bstep (se 1 (by rfl) ⟨1062707, by rfl⟩ : syracuseStep 1416943 = 2125415) B2125415
theorem B1679273 : Blo 1116628 1679273 := bstep (se 2 (by rfl) ⟨629727, by rfl⟩ : syracuseStep 1679273 = 1259455) B1259455
theorem B7643771 : Blo 1116628 7643771 := bstep (se 1 (by rfl) ⟨5732828, by rfl⟩ : syracuseStep 7643771 = 11465657) B11465657
theorem B1680743 : Blo 1116628 1680743 := bstep (se 1 (by rfl) ⟨1260557, by rfl⟩ : syracuseStep 1680743 = 2521115) B2521115
theorem B2828155 : Blo 1116628 2828155 := bstep (se 1 (by rfl) ⟨2121116, by rfl⟩ : syracuseStep 2828155 = 4242233) B4242233
theorem B4532561 : Blo 1116628 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B10201625 : Blo 1116628 10201625 := bstep (se 2 (by rfl) ⟨3825609, by rfl⟩ : syracuseStep 10201625 = 7651219) B7651219
theorem B6367997 : Blo 1116628 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B1256431 : Blo 1116628 1256431 := bstep (se 1 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 1256431 = 1884647) B1884647
theorem B8498681 : Blo 1116628 8498681 := bstep (se 2 (by rfl) ⟨3187005, by rfl⟩ : syracuseStep 8498681 = 6374011) B6374011
theorem B2830049 : Blo 1116628 2830049 := bstep (se 2 (by rfl) ⟨1061268, by rfl⟩ : syracuseStep 2830049 = 2122537) B2122537
theorem B3780431 : Blo 1116628 3780431 := bstep (se 1 (by rfl) ⟨2835323, by rfl⟩ : syracuseStep 3780431 = 5670647) B5670647
theorem B4305503 : Blo 1116628 4305503 := bstep (se 1 (by rfl) ⟨3229127, by rfl⟩ : syracuseStep 4305503 = 6458255) B6458255
theorem B1815151 : Blo 1116628 1815151 := bstep (se 1 (by rfl) ⟨1361363, by rfl⟩ : syracuseStep 1815151 = 2722727) B2722727
theorem B206910125 : Blo 1116628 206910125 := bstep (se 3 (by rfl) ⟨38795648, by rfl⟩ : syracuseStep 206910125 = 77591297) B77591297
theorem B3781295 : Blo 1116628 3781295 := bstep (se 1 (by rfl) ⟨2835971, by rfl⟩ : syracuseStep 3781295 = 5671943) B5671943
theorem B3027935 : Blo 1116628 3027935 := bstep (se 1 (by rfl) ⟨2270951, by rfl⟩ : syracuseStep 3027935 = 4541903) B4541903
theorem B3586331 : Blo 1116628 3586331 := bstep (se 1 (by rfl) ⟨2689748, by rfl⟩ : syracuseStep 3586331 = 5379497) B5379497
theorem B1260391 : Blo 1116628 1260391 := bstep (se 1 (by rfl) ⟨945293, by rfl⟩ : syracuseStep 1260391 = 1890587) B1890587
theorem B10763219 : Blo 1116628 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B14334965 : Blo 1116628 14334965 := bstep (se 5 (by rfl) ⟨671951, by rfl⟩ : syracuseStep 14334965 = 1343903) B1343903
theorem B1195247 : Blo 1116628 1195247 := bstep (se 1 (by rfl) ⟨896435, by rfl⟩ : syracuseStep 1195247 = 1792871) B1792871
theorem B2833967 : Blo 1116628 2833967 := bstep (se 1 (by rfl) ⟨2125475, by rfl⟩ : syracuseStep 2833967 = 4250951) B4250951
theorem B20397683 : Blo 1116628 20397683 := bstep (se 1 (by rfl) ⟨15298262, by rfl⟩ : syracuseStep 20397683 = 30596525) B30596525
theorem B4243175 : Blo 1116628 4243175 := bstep (se 1 (by rfl) ⟨3182381, by rfl⟩ : syracuseStep 4243175 = 6364763) B6364763
theorem B2834473 : Blo 1116628 2834473 := bstep (se 2 (by rfl) ⟨1062927, by rfl⟩ : syracuseStep 2834473 = 2125855) B2125855
theorem B3588407 : Blo 1116628 3588407 := bstep (se 1 (by rfl) ⟨2691305, by rfl⟩ : syracuseStep 3588407 = 5382611) B5382611
theorem B12108275 : Blo 1116628 12108275 := bstep (se 1 (by rfl) ⟨9081206, by rfl⟩ : syracuseStep 12108275 = 18162413) B18162413
theorem B5652989 : Blo 1116628 5652989 := bstep (se 3 (by rfl) ⟨1059935, by rfl⟩ : syracuseStep 5652989 = 2119871) B2119871
theorem B1885511 : Blo 1116628 1885511 := bstep (se 1 (by rfl) ⟨1414133, by rfl⟩ : syracuseStep 1885511 = 2828267) B2828267
theorem B1885673 : Blo 1116628 1885673 := bstep (se 2 (by rfl) ⟨707127, by rfl⟩ : syracuseStep 1885673 = 1414255) B1414255
theorem B3589687 : Blo 1116628 3589687 := bstep (se 1 (by rfl) ⟨2692265, by rfl⟩ : syracuseStep 3589687 = 5384531) B5384531
theorem B16107119 : Blo 1116628 16107119 := bstep (se 1 (by rfl) ⟨12080339, by rfl⟩ : syracuseStep 16107119 = 24160679) B24160679
theorem B18172025 : Blo 1116628 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B3820187 : Blo 1116628 3820187 := bstep (se 1 (by rfl) ⟨2865140, by rfl⟩ : syracuseStep 3820187 = 5730281) B5730281
theorem B4836023 : Blo 1116628 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B21482765 : Blo 1116628 21482765 := bstep (se 3 (by rfl) ⟨4028018, by rfl⟩ : syracuseStep 21482765 = 8056037) B8056037
theorem B5656553 : Blo 1116628 5656553 := bstep (se 2 (by rfl) ⟨2121207, by rfl⟩ : syracuseStep 5656553 = 4242415) B4242415
theorem B4247579 : Blo 1116628 4247579 := bstep (se 1 (by rfl) ⟨3185684, by rfl⟩ : syracuseStep 4247579 = 6371369) B6371369
theorem B3395675 : Blo 1116628 3395675 := bstep (se 1 (by rfl) ⟨2546756, by rfl⟩ : syracuseStep 3395675 = 5093513) B5093513
theorem B1888987 : Blo 1116628 1888987 := bstep (se 1 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 1888987 = 2833481) B2833481
theorem B1889615 : Blo 1116628 1889615 := bstep (se 1 (by rfl) ⟨1417211, by rfl⟩ : syracuseStep 1889615 = 2834423) B2834423
theorem B6051179 : Blo 1116628 6051179 := bstep (se 1 (by rfl) ⟨4538384, by rfl⟩ : syracuseStep 6051179 = 9076769) B9076769
theorem B3233191 : Blo 1116628 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B4249007 : Blo 1116628 4249007 := bstep (se 1 (by rfl) ⟨3186755, by rfl⟩ : syracuseStep 4249007 = 6373511) B6373511
theorem B1791487 : Blo 1116628 1791487 := bstep (se 1 (by rfl) ⟨1343615, by rfl⟩ : syracuseStep 1791487 = 2687231) B2687231
theorem B5101319 : Blo 1116628 5101319 := bstep (se 1 (by rfl) ⟨3825989, by rfl⟩ : syracuseStep 5101319 = 7651979) B7651979
theorem B2512943 : Blo 1116628 2512943 := bstep (se 1 (by rfl) ⟨1884707, by rfl⟩ : syracuseStep 2512943 = 3769415) B3769415
theorem B1890425 : Blo 1116628 1890425 := bstep (se 2 (by rfl) ⟨708909, by rfl⟩ : syracuseStep 1890425 = 1417819) B1417819
theorem B1890479 : Blo 1116628 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B2513231 : Blo 1116628 2513231 := bstep (se 1 (by rfl) ⟨1884923, by rfl⟩ : syracuseStep 2513231 = 3769847) B3769847
theorem B1890911 : Blo 1116628 1890911 := bstep (se 1 (by rfl) ⟨1418183, by rfl⟩ : syracuseStep 1890911 = 2836367) B2836367
theorem B2513951 : Blo 1116628 2513951 := bstep (se 1 (by rfl) ⟨1885463, by rfl⟩ : syracuseStep 2513951 = 3770927) B3770927
theorem B2121967 : Blo 1116628 2121967 := bstep (se 1 (by rfl) ⟨1591475, by rfl⟩ : syracuseStep 2121967 = 3182951) B3182951
theorem B1794383 : Blo 1116628 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B4776529 : Blo 1116628 4776529 := bstep (se 2 (by rfl) ⟨1791198, by rfl⟩ : syracuseStep 4776529 = 3582397) B3582397
theorem B2515967 : Blo 1116628 2515967 := bstep (se 1 (by rfl) ⟨1886975, by rfl⟩ : syracuseStep 2515967 = 3773951) B3773951
theorem B9692263 : Blo 1116628 9692263 := bstep (se 1 (by rfl) ⟨7269197, by rfl⟩ : syracuseStep 9692263 = 14538395) B14538395
theorem B4777127 : Blo 1116628 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B2516219 : Blo 1116628 2516219 := bstep (se 1 (by rfl) ⟨1887164, by rfl⟩ : syracuseStep 2516219 = 3774329) B3774329
theorem B7660955 : Blo 1116628 7660955 := bstep (se 1 (by rfl) ⟨5745716, by rfl⟩ : syracuseStep 7660955 = 11491433) B11491433
theorem B4777811 : Blo 1116628 4777811 := bstep (se 1 (by rfl) ⟨3583358, by rfl⟩ : syracuseStep 4777811 = 7166717) B7166717
theorem B4024475 : Blo 1116628 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B4254079 : Blo 1116628 4254079 := bstep (se 1 (by rfl) ⟨3190559, by rfl⟩ : syracuseStep 4254079 = 6381119) B6381119
theorem B2518271 : Blo 1116628 2518271 := bstep (se 1 (by rfl) ⟨1888703, by rfl⟩ : syracuseStep 2518271 = 3777407) B3777407
theorem B9563615 : Blo 1116628 9563615 := bstep (se 1 (by rfl) ⟨7172711, by rfl⟩ : syracuseStep 9563615 = 14345423) B14345423
theorem B2518505 : Blo 1116628 2518505 := bstep (se 2 (by rfl) ⟨944439, by rfl⟩ : syracuseStep 2518505 = 1888879) B1888879
theorem B4025857 : Blo 1116628 4025857 := bstep (se 2 (by rfl) ⟨1509696, by rfl⟩ : syracuseStep 4025857 = 3019393) B3019393
theorem B2518559 : Blo 1116628 2518559 := bstep (se 1 (by rfl) ⟨1888919, by rfl⟩ : syracuseStep 2518559 = 3777839) B3777839
theorem B26144731 : Blo 1116628 26144731 := bstep (se 1 (by rfl) ⟨19608548, by rfl⟩ : syracuseStep 26144731 = 39217097) B39217097
theorem B2519135 : Blo 1116628 2519135 := bstep (se 1 (by rfl) ⟨1889351, by rfl⟩ : syracuseStep 2519135 = 3778703) B3778703
theorem B12742919 : Blo 1116628 12742919 := bstep (se 1 (by rfl) ⟨9557189, by rfl⟩ : syracuseStep 12742919 = 19114379) B19114379
theorem B8483129 : Blo 1116628 8483129 := bstep (se 2 (by rfl) ⟨3181173, by rfl⟩ : syracuseStep 8483129 = 6362347) B6362347
theorem B2126159 : Blo 1116628 2126159 := bstep (se 1 (by rfl) ⟨1594619, by rfl⟩ : syracuseStep 2126159 = 3189239) B3189239
theorem B8057627 : Blo 1116628 8057627 := bstep (se 1 (by rfl) ⟨6043220, by rfl⟩ : syracuseStep 8057627 = 12086441) B12086441
theorem B353301355 : Blo 1116628 353301355 := bstep (se 1 (by rfl) ⟨264976016, by rfl⟩ : syracuseStep 353301355 = 529952033) B529952033
theorem B4780919 : Blo 1116628 4780919 := bstep (se 1 (by rfl) ⟨3585689, by rfl⟩ : syracuseStep 4780919 = 7171379) B7171379
theorem B2126827 : Blo 1116628 2126827 := bstep (se 1 (by rfl) ⟨1595120, by rfl⟩ : syracuseStep 2126827 = 3190241) B3190241
theorem B6812711 : Blo 1116628 6812711 := bstep (se 1 (by rfl) ⟨5109533, by rfl⟩ : syracuseStep 6812711 = 10219067) B10219067
theorem B2520575 : Blo 1116628 2520575 := bstep (se 1 (by rfl) ⟨1890431, by rfl⟩ : syracuseStep 2520575 = 3780863) B3780863
theorem B2127359 : Blo 1116628 2127359 := bstep (se 1 (by rfl) ⟨1595519, by rfl⟩ : syracuseStep 2127359 = 3191039) B3191039
theorem B2685001 : Blo 1116628 2685001 := bstep (se 2 (by rfl) ⟨1006875, by rfl⟩ : syracuseStep 2685001 = 2013751) B2013751
theorem B8715691 : Blo 1116628 8715691 := bstep (se 1 (by rfl) ⟨6536768, by rfl⟩ : syracuseStep 8715691 = 13073537) B13073537
theorem B14352187 : Blo 1116628 14352187 := bstep (se 1 (by rfl) ⟨10764140, by rfl⟩ : syracuseStep 14352187 = 21528281) B21528281
theorem B2392271 : Blo 1116628 2392271 := bstep (se 1 (by rfl) ⟨1794203, by rfl⟩ : syracuseStep 2392271 = 3588407) B3588407
theorem B3768659 : Blo 1116628 3768659 := bstep (se 1 (by rfl) ⟨2826494, by rfl⟩ : syracuseStep 3768659 = 5652989) B5652989
theorem B5375767 : Blo 1116628 5375767 := bstep (se 1 (by rfl) ⟨4031825, by rfl⟩ : syracuseStep 5375767 = 8063651) B8063651
theorem B14321843 : Blo 1116628 14321843 := bstep (se 1 (by rfl) ⟨10741382, by rfl⟩ : syracuseStep 14321843 = 21482765) B21482765
theorem B3770873 : Blo 1116628 3770873 := bstep (se 2 (by rfl) ⟨1414077, by rfl⟩ : syracuseStep 3770873 = 2828155) B2828155
theorem B3771035 : Blo 1116628 3771035 := bstep (se 1 (by rfl) ⟨2828276, by rfl⟩ : syracuseStep 3771035 = 5656553) B5656553
theorem B2263783 : Blo 1116628 2263783 := bstep (se 1 (by rfl) ⟨1697837, by rfl⟩ : syracuseStep 2263783 = 3395675) B3395675
theorem B1116927 : Blo 1116628 1116927 := bstep (se 1 (by rfl) ⟨837695, by rfl⟩ : syracuseStep 1116927 = 1675391) B1675391
theorem B1117211 : Blo 1116628 1117211 := bstep (se 1 (by rfl) ⟨837908, by rfl⟩ : syracuseStep 1117211 = 1675817) B1675817
theorem B5672105 : Blo 1116628 5672105 := bstep (se 2 (by rfl) ⟨2127039, by rfl⟩ : syracuseStep 5672105 = 4254079) B4254079
theorem B1117391 : Blo 1116628 1117391 := bstep (se 1 (by rfl) ⟨838043, by rfl⟩ : syracuseStep 1117391 = 1676087) B1676087
theorem B1117423 : Blo 1116628 1117423 := bstep (se 1 (by rfl) ⟨838067, by rfl⟩ : syracuseStep 1117423 = 1676135) B1676135
theorem B1117467 : Blo 1116628 1117467 := bstep (se 1 (by rfl) ⟨838100, by rfl⟩ : syracuseStep 1117467 = 1676201) B1676201
theorem B1117511 : Blo 1116628 1117511 := bstep (se 1 (by rfl) ⟨838133, by rfl⟩ : syracuseStep 1117511 = 1676267) B1676267
theorem B4034119 : Blo 1116628 4034119 := bstep (se 1 (by rfl) ⟨3025589, by rfl⟩ : syracuseStep 4034119 = 6051179) B6051179
theorem B1117863 : Blo 1116628 1117863 := bstep (se 1 (by rfl) ⟨838397, by rfl⟩ : syracuseStep 1117863 = 1676795) B1676795
theorem B1117979 : Blo 1116628 1117979 := bstep (se 1 (by rfl) ⟨838484, by rfl⟩ : syracuseStep 1117979 = 1676969) B1676969
theorem B1117983 : Blo 1116628 1117983 := bstep (se 1 (by rfl) ⟨838487, by rfl⟩ : syracuseStep 1117983 = 1676975) B1676975
theorem B1118063 : Blo 1116628 1118063 := bstep (se 1 (by rfl) ⟨838547, by rfl⟩ : syracuseStep 1118063 = 1677095) B1677095
theorem B1675241 : Blo 1116628 1675241 := bstep (se 2 (by rfl) ⟨628215, by rfl⟩ : syracuseStep 1675241 = 1256431) B1256431
theorem B1675295 : Blo 1116628 1675295 := bstep (se 1 (by rfl) ⟨1256471, by rfl⟩ : syracuseStep 1675295 = 2512943) B2512943
theorem B1118279 : Blo 1116628 1118279 := bstep (se 1 (by rfl) ⟨838709, by rfl⟩ : syracuseStep 1118279 = 1677419) B1677419
theorem B1675487 : Blo 1116628 1675487 := bstep (se 1 (by rfl) ⟨1256615, by rfl⟩ : syracuseStep 1675487 = 2513231) B2513231
theorem B1118463 : Blo 1116628 1118463 := bstep (se 1 (by rfl) ⟨838847, by rfl⟩ : syracuseStep 1118463 = 1677695) B1677695
theorem B1118511 : Blo 1116628 1118511 := bstep (se 1 (by rfl) ⟨838883, by rfl⟩ : syracuseStep 1118511 = 1677767) B1677767
theorem B1118623 : Blo 1116628 1118623 := bstep (se 1 (by rfl) ⟨838967, by rfl⟩ : syracuseStep 1118623 = 1677935) B1677935
theorem B1118751 : Blo 1116628 1118751 := bstep (se 1 (by rfl) ⟨839063, by rfl⟩ : syracuseStep 1118751 = 1678127) B1678127
theorem B1118831 : Blo 1116628 1118831 := bstep (se 1 (by rfl) ⟨839123, by rfl⟩ : syracuseStep 1118831 = 1678247) B1678247
theorem B1118879 : Blo 1116628 1118879 := bstep (se 1 (by rfl) ⟨839159, by rfl⟩ : syracuseStep 1118879 = 1678319) B1678319
theorem B13603517 : Blo 1116628 13603517 := bstep (se 3 (by rfl) ⟨2550659, by rfl⟩ : syracuseStep 13603517 = 5101319) B5101319
theorem B1675967 : Blo 1116628 1675967 := bstep (se 1 (by rfl) ⟨1256975, by rfl⟩ : syracuseStep 1675967 = 2513951) B2513951
theorem B1118951 : Blo 1116628 1118951 := bstep (se 1 (by rfl) ⟨839213, by rfl⟩ : syracuseStep 1118951 = 1678427) B1678427
theorem B1118959 : Blo 1116628 1118959 := bstep (se 1 (by rfl) ⟨839219, by rfl⟩ : syracuseStep 1118959 = 1678439) B1678439
theorem B1119003 : Blo 1116628 1119003 := bstep (se 1 (by rfl) ⟨839252, by rfl⟩ : syracuseStep 1119003 = 1678505) B1678505
theorem B1119391 : Blo 1116628 1119391 := bstep (se 1 (by rfl) ⟨839543, by rfl⟩ : syracuseStep 1119391 = 1679087) B1679087
theorem B1119515 : Blo 1116628 1119515 := bstep (se 1 (by rfl) ⟨839636, by rfl⟩ : syracuseStep 1119515 = 1679273) B1679273
theorem B1677311 : Blo 1116628 1677311 := bstep (se 1 (by rfl) ⟨1257983, by rfl⟩ : syracuseStep 1677311 = 2515967) B2515967
theorem B3184751 : Blo 1116628 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B1677479 : Blo 1116628 1677479 := bstep (se 1 (by rfl) ⟨1258109, by rfl⟩ : syracuseStep 1677479 = 2516219) B2516219
theorem B1120495 : Blo 1116628 1120495 := bstep (se 1 (by rfl) ⟨840371, by rfl⟩ : syracuseStep 1120495 = 1680743) B1680743
theorem B3185207 : Blo 1116628 3185207 := bstep (se 1 (by rfl) ⟨2388905, by rfl⟩ : syracuseStep 3185207 = 4777811) B4777811
theorem B8493821 : Blo 1116628 8493821 := bstep (se 3 (by rfl) ⟨1592591, by rfl⟩ : syracuseStep 8493821 = 3185183) B3185183
theorem B3021707 : Blo 1116628 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B1678847 : Blo 1116628 1678847 := bstep (se 1 (by rfl) ⟨1259135, by rfl⟩ : syracuseStep 1678847 = 2518271) B2518271
theorem B1679003 : Blo 1116628 1679003 := bstep (se 1 (by rfl) ⟨1259252, by rfl⟩ : syracuseStep 1679003 = 2518505) B2518505
theorem B1679039 : Blo 1116628 1679039 := bstep (se 1 (by rfl) ⟨1259279, by rfl⟩ : syracuseStep 1679039 = 2518559) B2518559
theorem B1679423 : Blo 1116628 1679423 := bstep (se 1 (by rfl) ⟨1259567, by rfl⟩ : syracuseStep 1679423 = 2519135) B2519135
theorem B3580001 : Blo 1116628 3580001 := bstep (se 2 (by rfl) ⟨1342500, by rfl⟩ : syracuseStep 3580001 = 2685001) B2685001
theorem B8495279 : Blo 1116628 8495279 := bstep (se 1 (by rfl) ⟨6371459, by rfl⟩ : syracuseStep 8495279 = 12742919) B12742919
theorem B1417439 : Blo 1116628 1417439 := bstep (se 1 (by rfl) ⟨1063079, by rfl⟩ : syracuseStep 1417439 = 2126159) B2126159
theorem B19144997 : Blo 1116628 19144997 := bstep (se 4 (by rfl) ⟨1794843, by rfl⟩ : syracuseStep 19144997 = 3589687) B3589687
theorem B3187279 : Blo 1116628 3187279 := bstep (se 1 (by rfl) ⟨2390459, by rfl⟩ : syracuseStep 3187279 = 4780919) B4780919
theorem B3187325 : Blo 1116628 3187325 := bstep (se 3 (by rfl) ⟨597623, by rfl⟩ : syracuseStep 3187325 = 1195247) B1195247
theorem B1680383 : Blo 1116628 1680383 := bstep (se 1 (by rfl) ⟨1260287, by rfl⟩ : syracuseStep 1680383 = 2520575) B2520575
theorem B1418239 : Blo 1116628 1418239 := bstep (se 1 (by rfl) ⟨1063679, by rfl⟩ : syracuseStep 1418239 = 2127359) B2127359
theorem B1680521 : Blo 1116628 1680521 := bstep (se 2 (by rfl) ⟨630195, by rfl⟩ : syracuseStep 1680521 = 1260391) B1260391
theorem B2828783 : Blo 1116628 2828783 := bstep (se 1 (by rfl) ⟨2121587, by rfl⟩ : syracuseStep 2828783 = 4243175) B4243175
theorem B3779297 : Blo 1116628 3779297 := bstep (se 2 (by rfl) ⟨1417236, by rfl⟩ : syracuseStep 3779297 = 2834473) B2834473
theorem B54438803 : Blo 1116628 54438803 := bstep (se 1 (by rfl) ⟨40829102, by rfl⟩ : syracuseStep 54438803 = 81658205) B81658205
theorem B2829289 : Blo 1116628 2829289 := bstep (se 2 (by rfl) ⟨1060983, by rfl⟩ : syracuseStep 2829289 = 2121967) B2121967
theorem B8072183 : Blo 1116628 8072183 := bstep (se 1 (by rfl) ⟨6054137, by rfl⟩ : syracuseStep 8072183 = 12108275) B12108275
theorem B6368705 : Blo 1116628 6368705 := bstep (se 2 (by rfl) ⟨2388264, by rfl⟩ : syracuseStep 6368705 = 4776529) B4776529
theorem B1257007 : Blo 1116628 1257007 := bstep (se 1 (by rfl) ⟨942755, by rfl⟩ : syracuseStep 1257007 = 1885511) B1885511
theorem B1257115 : Blo 1116628 1257115 := bstep (se 1 (by rfl) ⟨942836, by rfl⟩ : syracuseStep 1257115 = 1885673) B1885673
theorem B3190583 : Blo 1116628 3190583 := bstep (se 1 (by rfl) ⟨2392937, by rfl⟩ : syracuseStep 3190583 = 4785875) B4785875
theorem B3190823 : Blo 1116628 3190823 := bstep (se 1 (by rfl) ⟨2393117, by rfl⟩ : syracuseStep 3190823 = 4786235) B4786235
theorem B3224015 : Blo 1116628 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B6796115 : Blo 1116628 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B3781943 : Blo 1116628 3781943 := bstep (se 1 (by rfl) ⟨2836457, by rfl⟩ : syracuseStep 3781943 = 5672915) B5672915
theorem B2831719 : Blo 1116628 2831719 := bstep (se 1 (by rfl) ⟨2123789, by rfl⟩ : syracuseStep 2831719 = 4247579) B4247579
theorem B20428631 : Blo 1116628 20428631 := bstep (se 1 (by rfl) ⟨15321473, by rfl⟩ : syracuseStep 20428631 = 30642947) B30642947
theorem B27965657 : Blo 1116628 27965657 := bstep (se 2 (by rfl) ⟨10487121, by rfl⟩ : syracuseStep 27965657 = 20974243) B20974243
theorem B1259743 : Blo 1116628 1259743 := bstep (se 1 (by rfl) ⟨944807, by rfl⟩ : syracuseStep 1259743 = 1889615) B1889615
theorem B2832671 : Blo 1116628 2832671 := bstep (se 1 (by rfl) ⟨2124503, by rfl⟩ : syracuseStep 2832671 = 4249007) B4249007
theorem B2013779 : Blo 1116628 2013779 := bstep (se 1 (by rfl) ⟨1510334, by rfl⟩ : syracuseStep 2013779 = 3020669) B3020669
theorem B1260283 : Blo 1116628 1260283 := bstep (se 1 (by rfl) ⟨945212, by rfl⟩ : syracuseStep 1260283 = 1890425) B1890425
theorem B1260319 : Blo 1116628 1260319 := bstep (se 1 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 1260319 = 1890479) B1890479
theorem B1260607 : Blo 1116628 1260607 := bstep (se 1 (by rfl) ⟨945455, by rfl⟩ : syracuseStep 1260607 = 1890911) B1890911
theorem B3587561 : Blo 1116628 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B1196255 : Blo 1116628 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B4243873 : Blo 1116628 4243873 := bstep (se 2 (by rfl) ⟨1591452, by rfl⟩ : syracuseStep 4243873 = 3182905) B3182905
theorem B5095847 : Blo 1116628 5095847 := bstep (se 1 (by rfl) ⟨3821885, by rfl⟩ : syracuseStep 5095847 = 7643771) B7643771
theorem B51692069 : Blo 1116628 51692069 := bstep (se 4 (by rfl) ⟨4846131, by rfl⟩ : syracuseStep 51692069 = 9692263) B9692263
theorem B2835769 : Blo 1116628 2835769 := bstep (se 2 (by rfl) ⟨1063413, by rfl⟩ : syracuseStep 2835769 = 2126827) B2126827
theorem B6801083 : Blo 1116628 6801083 := bstep (se 1 (by rfl) ⟨5100812, by rfl⟩ : syracuseStep 6801083 = 10201625) B10201625
theorem B4245331 : Blo 1116628 4245331 := bstep (se 1 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 4245331 = 6367997) B6367997
theorem B4310921 : Blo 1116628 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B6375743 : Blo 1116628 6375743 := bstep (se 1 (by rfl) ⟨4781807, by rfl⟩ : syracuseStep 6375743 = 9563615) B9563615
theorem B1886699 : Blo 1116628 1886699 := bstep (se 1 (by rfl) ⟨1415024, by rfl⟩ : syracuseStep 1886699 = 2830049) B2830049
theorem B5655419 : Blo 1116628 5655419 := bstep (se 1 (by rfl) ⟨4241564, by rfl⟩ : syracuseStep 5655419 = 8483129) B8483129
theorem B2870335 : Blo 1116628 2870335 := bstep (se 1 (by rfl) ⟨2152751, by rfl⟩ : syracuseStep 2870335 = 4305503) B4305503
theorem B137940083 : Blo 1116628 137940083 := bstep (se 1 (by rfl) ⟨103455062, by rfl⟩ : syracuseStep 137940083 = 206910125) B206910125
theorem B1887401 : Blo 1116628 1887401 := bstep (se 2 (by rfl) ⟨707775, by rfl⟩ : syracuseStep 1887401 = 1415551) B1415551
theorem B2018623 : Blo 1116628 2018623 := bstep (se 1 (by rfl) ⟨1513967, by rfl⟩ : syracuseStep 2018623 = 3027935) B3027935
theorem B4541807 : Blo 1116628 4541807 := bstep (se 1 (by rfl) ⟨3406355, by rfl⟩ : syracuseStep 4541807 = 6812711) B6812711
theorem B1888393 : Blo 1116628 1888393 := bstep (se 2 (by rfl) ⟨708147, by rfl⟩ : syracuseStep 1888393 = 1416295) B1416295
theorem B11620921 : Blo 1116628 11620921 := bstep (se 2 (by rfl) ⟨4357845, by rfl⟩ : syracuseStep 11620921 = 8715691) B8715691
theorem B9556643 : Blo 1116628 9556643 := bstep (se 1 (by rfl) ⟨7167482, by rfl⟩ : syracuseStep 9556643 = 14334965) B14334965
theorem B1889257 : Blo 1116628 1889257 := bstep (se 2 (by rfl) ⟨708471, by rfl⟩ : syracuseStep 1889257 = 1416943) B1416943
theorem B1889311 : Blo 1116628 1889311 := bstep (se 1 (by rfl) ⟨1416983, by rfl⟩ : syracuseStep 1889311 = 2833967) B2833967
theorem B42948305 : Blo 1116628 42948305 := bstep (se 2 (by rfl) ⟨16105614, by rfl⟩ : syracuseStep 42948305 = 32211229) B32211229
theorem B1595371 : Blo 1116628 1595371 := bstep (se 1 (by rfl) ⟨1196528, by rfl⟩ : syracuseStep 1595371 = 2393057) B2393057
theorem B5658983 : Blo 1116628 5658983 := bstep (se 1 (by rfl) ⟨4244237, by rfl⟩ : syracuseStep 5658983 = 8488475) B8488475
theorem B10738079 : Blo 1116628 10738079 := bstep (se 1 (by rfl) ⟨8053559, by rfl⟩ : syracuseStep 10738079 = 16107119) B16107119
theorem B2120107 : Blo 1116628 2120107 := bstep (se 1 (by rfl) ⟨1590080, by rfl⟩ : syracuseStep 2120107 = 3180161) B3180161
theorem B12114683 : Blo 1116628 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B2546791 : Blo 1116628 2546791 := bstep (se 1 (by rfl) ⟨1910093, by rfl⟩ : syracuseStep 2546791 = 3820187) B3820187
theorem B2514095 : Blo 1116628 2514095 := bstep (se 1 (by rfl) ⟨1885571, by rfl⟩ : syracuseStep 2514095 = 3771143) B3771143
theorem B2514779 : Blo 1116628 2514779 := bstep (se 1 (by rfl) ⟨1886084, by rfl⟩ : syracuseStep 2514779 = 3772169) B3772169
theorem B2514815 : Blo 1116628 2514815 := bstep (se 1 (by rfl) ⟨1886111, by rfl⟩ : syracuseStep 2514815 = 3772223) B3772223
theorem B2122271 : Blo 1116628 2122271 := bstep (se 1 (by rfl) ⟨1591703, by rfl⟩ : syracuseStep 2122271 = 3183407) B3183407
theorem B2516039 : Blo 1116628 2516039 := bstep (se 1 (by rfl) ⟨1887029, by rfl⟩ : syracuseStep 2516039 = 3774059) B3774059
theorem B5367809 : Blo 1116628 5367809 := bstep (se 2 (by rfl) ⟨2012928, by rfl⟩ : syracuseStep 5367809 = 4025857) B4025857
theorem B68905241 : Blo 1116628 68905241 := bstep (se 2 (by rfl) ⟨25839465, by rfl⟩ : syracuseStep 68905241 = 51678931) B51678931
theorem B2517407 : Blo 1116628 2517407 := bstep (se 1 (by rfl) ⟨1888055, by rfl⟩ : syracuseStep 2517407 = 3776111) B3776111
theorem B34859641 : Blo 1116628 34859641 := bstep (se 2 (by rfl) ⟨13072365, by rfl⟩ : syracuseStep 34859641 = 26144731) B26144731
theorem B2420201 : Blo 1116628 2420201 := bstep (se 2 (by rfl) ⟨907575, by rfl⟩ : syracuseStep 2420201 = 1815151) B1815151
theorem B5107303 : Blo 1116628 5107303 := bstep (se 1 (by rfl) ⟨3830477, by rfl⟩ : syracuseStep 5107303 = 7660955) B7660955
theorem B2518649 : Blo 1116628 2518649 := bstep (se 2 (by rfl) ⟨944493, by rfl⟩ : syracuseStep 2518649 = 1888987) B1888987
theorem B471068473 : Blo 1116628 471068473 := bstep (se 2 (by rfl) ⟨176650677, by rfl⟩ : syracuseStep 471068473 = 353301355) B353301355
theorem B2682983 : Blo 1116628 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B2388649 : Blo 1116628 2388649 := bstep (se 2 (by rfl) ⟨895743, by rfl⟩ : syracuseStep 2388649 = 1791487) B1791487
theorem B5665787 : Blo 1116628 5665787 := bstep (se 1 (by rfl) ⟨4249340, by rfl⟩ : syracuseStep 5665787 = 8498681) B8498681
theorem B2520287 : Blo 1116628 2520287 := bstep (se 1 (by rfl) ⟨1890215, by rfl⟩ : syracuseStep 2520287 = 3780431) B3780431
theorem B2520863 : Blo 1116628 2520863 := bstep (se 1 (by rfl) ⟨1890647, by rfl⟩ : syracuseStep 2520863 = 3781295) B3781295
theorem B5371751 : Blo 1116628 5371751 := bstep (se 1 (by rfl) ⟨4028813, by rfl⟩ : syracuseStep 5371751 = 8057627) B8057627
theorem B2390887 : Blo 1116628 2390887 := bstep (se 1 (by rfl) ⟨1793165, by rfl⟩ : syracuseStep 2390887 = 3586331) B3586331
theorem B7175479 : Blo 1116628 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B13598455 : Blo 1116628 13598455 := bstep (se 1 (by rfl) ⟨10198841, by rfl⟩ : syracuseStep 13598455 = 20397683) B20397683
theorem B19136249 : Blo 1116628 19136249 := bstep (se 2 (by rfl) ⟨7176093, by rfl⟩ : syracuseStep 19136249 = 14352187) B14352187
theorem B3770279 : Blo 1116628 3770279 := bstep (se 1 (by rfl) ⟨2827709, by rfl⟩ : syracuseStep 3770279 = 5655419) B5655419
theorem B1116827 : Blo 1116628 1116827 := bstep (se 1 (by rfl) ⟨837620, by rfl⟩ : syracuseStep 1116827 = 1675241) B1675241
theorem B1116863 : Blo 1116628 1116863 := bstep (se 1 (by rfl) ⟨837647, by rfl⟩ : syracuseStep 1116863 = 1675295) B1675295
theorem B1116991 : Blo 1116628 1116991 := bstep (se 1 (by rfl) ⟨837743, by rfl⟩ : syracuseStep 1116991 = 1675487) B1675487
theorem B1117311 : Blo 1116628 1117311 := bstep (se 1 (by rfl) ⟨837983, by rfl⟩ : syracuseStep 1117311 = 1675967) B1675967
theorem B3018377 : Blo 1116628 3018377 := bstep (se 2 (by rfl) ⟨1131891, by rfl⟩ : syracuseStep 3018377 = 2263783) B2263783
theorem B3772385 : Blo 1116628 3772385 := bstep (se 2 (by rfl) ⟨1414644, by rfl⟩ : syracuseStep 3772385 = 2829289) B2829289
theorem B1118207 : Blo 1116628 1118207 := bstep (se 1 (by rfl) ⟨838655, by rfl⟩ : syracuseStep 1118207 = 1677311) B1677311
theorem B1118319 : Blo 1116628 1118319 := bstep (se 1 (by rfl) ⟨838739, by rfl⟩ : syracuseStep 1118319 = 1677479) B1677479
theorem B3772655 : Blo 1116628 3772655 := bstep (se 1 (by rfl) ⟨2829491, by rfl⟩ : syracuseStep 3772655 = 5658983) B5658983
theorem B2691497 : Blo 1116628 2691497 := bstep (se 2 (by rfl) ⟨1009311, by rfl⟩ : syracuseStep 2691497 = 2018623) B2018623
theorem B1676009 : Blo 1116628 1676009 := bstep (se 2 (by rfl) ⟨628503, by rfl⟩ : syracuseStep 1676009 = 1257007) B1257007
theorem B5378825 : Blo 1116628 5378825 := bstep (se 2 (by rfl) ⟨2017059, by rfl⟩ : syracuseStep 5378825 = 4034119) B4034119
theorem B1676063 : Blo 1116628 1676063 := bstep (se 1 (by rfl) ⟨1257047, by rfl⟩ : syracuseStep 1676063 = 2514095) B2514095
theorem B1676153 : Blo 1116628 1676153 := bstep (se 2 (by rfl) ⟨628557, by rfl⟩ : syracuseStep 1676153 = 1257115) B1257115
theorem B1119231 : Blo 1116628 1119231 := bstep (se 1 (by rfl) ⟨839423, by rfl⟩ : syracuseStep 1119231 = 1678847) B1678847
theorem B1119335 : Blo 1116628 1119335 := bstep (se 1 (by rfl) ⟨839501, by rfl⟩ : syracuseStep 1119335 = 1679003) B1679003
theorem B1119359 : Blo 1116628 1119359 := bstep (se 1 (by rfl) ⟨839519, by rfl⟩ : syracuseStep 1119359 = 1679039) B1679039
theorem B1676519 : Blo 1116628 1676519 := bstep (se 1 (by rfl) ⟨1257389, by rfl⟩ : syracuseStep 1676519 = 2514779) B2514779
theorem B1676543 : Blo 1116628 1676543 := bstep (se 1 (by rfl) ⟨1257407, by rfl⟩ : syracuseStep 1676543 = 2514815) B2514815
theorem B1119615 : Blo 1116628 1119615 := bstep (se 1 (by rfl) ⟨839711, by rfl⟩ : syracuseStep 1119615 = 1679423) B1679423
theorem B15308453 : Blo 1116628 15308453 := bstep (se 4 (by rfl) ⟨1435167, by rfl⟩ : syracuseStep 15308453 = 2870335) B2870335
theorem B1414847 : Blo 1116628 1414847 := bstep (se 1 (by rfl) ⟨1061135, by rfl⟩ : syracuseStep 1414847 = 2122271) B2122271
theorem B1120255 : Blo 1116628 1120255 := bstep (se 1 (by rfl) ⟨840191, by rfl⟩ : syracuseStep 1120255 = 1680383) B1680383
theorem B1677359 : Blo 1116628 1677359 := bstep (se 1 (by rfl) ⟨1258019, by rfl⟩ : syracuseStep 1677359 = 2516039) B2516039
theorem B1120347 : Blo 1116628 1120347 := bstep (se 1 (by rfl) ⟨840260, by rfl⟩ : syracuseStep 1120347 = 1680521) B1680521
theorem B3184865 : Blo 1116628 3184865 := bstep (se 2 (by rfl) ⟨1194324, by rfl⟩ : syracuseStep 3184865 = 2388649) B2388649
theorem B1678271 : Blo 1116628 1678271 := bstep (se 1 (by rfl) ⟨1258703, by rfl⟩ : syracuseStep 1678271 = 2517407) B2517407
theorem B3775625 : Blo 1116628 3775625 := bstep (se 2 (by rfl) ⟨1415859, by rfl⟩ : syracuseStep 3775625 = 2831719) B2831719
theorem B1613467 : Blo 1116628 1613467 := bstep (se 1 (by rfl) ⟨1210100, by rfl⟩ : syracuseStep 1613467 = 2420201) B2420201
theorem B1679099 : Blo 1116628 1679099 := bstep (se 1 (by rfl) ⟨1259324, by rfl⟩ : syracuseStep 1679099 = 2518649) B2518649
theorem B1679657 : Blo 1116628 1679657 := bstep (se 2 (by rfl) ⟨629871, by rfl⟩ : syracuseStep 1679657 = 1259743) B1259743
theorem B27238949 : Blo 1116628 27238949 := bstep (se 4 (by rfl) ⟨2553651, by rfl⟩ : syracuseStep 27238949 = 5107303) B5107303
theorem B4530743 : Blo 1116628 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B2826809 : Blo 1116628 2826809 := bstep (se 2 (by rfl) ⟨1060053, by rfl⟩ : syracuseStep 2826809 = 2120107) B2120107
theorem B3777191 : Blo 1116628 3777191 := bstep (se 1 (by rfl) ⟨2832893, by rfl⟩ : syracuseStep 3777191 = 5665787) B5665787
theorem B1680191 : Blo 1116628 1680191 := bstep (se 1 (by rfl) ⟨1260143, by rfl⟩ : syracuseStep 1680191 = 2520287) B2520287
theorem B1680377 : Blo 1116628 1680377 := bstep (se 2 (by rfl) ⟨630141, by rfl⟩ : syracuseStep 1680377 = 1260283) B1260283
theorem B1680425 : Blo 1116628 1680425 := bstep (se 2 (by rfl) ⟨630159, by rfl⟩ : syracuseStep 1680425 = 1260319) B1260319
theorem B3187849 : Blo 1116628 3187849 := bstep (se 2 (by rfl) ⟨1195443, by rfl⟩ : syracuseStep 3187849 = 2390887) B2390887
theorem B1680575 : Blo 1116628 1680575 := bstep (se 1 (by rfl) ⟨1260431, by rfl⟩ : syracuseStep 1680575 = 2520863) B2520863
theorem B3581167 : Blo 1116628 3581167 := bstep (se 1 (by rfl) ⟨2685875, by rfl⟩ : syracuseStep 3581167 = 5371751) B5371751
theorem B1680809 : Blo 1116628 1680809 := bstep (se 2 (by rfl) ⟨630303, by rfl⟩ : syracuseStep 1680809 = 1260607) B1260607
theorem B18131273 : Blo 1116628 18131273 := bstep (se 2 (by rfl) ⟨6799227, by rfl⟩ : syracuseStep 18131273 = 13598455) B13598455
theorem B12757499 : Blo 1116628 12757499 := bstep (se 1 (by rfl) ⟨9568124, by rfl⟩ : syracuseStep 12757499 = 19136249) B19136249
theorem B3779837 : Blo 1116628 3779837 := bstep (se 3 (by rfl) ⟨708719, by rfl⟩ : syracuseStep 3779837 = 1417439) B1417439
theorem B3190013 : Blo 1116628 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B4534055 : Blo 1116628 4534055 := bstep (se 1 (by rfl) ⟨3400541, by rfl⟩ : syracuseStep 4534055 = 6801083) B6801083
theorem B9547895 : Blo 1116628 9547895 := bstep (se 1 (by rfl) ⟨7160921, by rfl⟩ : syracuseStep 9547895 = 14321843) B14321843
theorem B1257799 : Blo 1116628 1257799 := bstep (se 1 (by rfl) ⟨943349, by rfl⟩ : syracuseStep 1257799 = 1886699) B1886699
theorem B3781025 : Blo 1116628 3781025 := bstep (se 2 (by rfl) ⟨1417884, by rfl⟩ : syracuseStep 3781025 = 2835769) B2835769
theorem B91960055 : Blo 1116628 91960055 := bstep (se 1 (by rfl) ⟨68970041, by rfl⟩ : syracuseStep 91960055 = 137940083) B137940083
theorem B1258267 : Blo 1116628 1258267 := bstep (se 1 (by rfl) ⟨943700, by rfl⟩ : syracuseStep 1258267 = 1887401) B1887401
theorem B3781403 : Blo 1116628 3781403 := bstep (se 1 (by rfl) ⟨2836052, by rfl⟩ : syracuseStep 3781403 = 5672105) B5672105
theorem B3027871 : Blo 1116628 3027871 := bstep (se 1 (by rfl) ⟨2270903, by rfl⟩ : syracuseStep 3027871 = 4541807) B4541807
theorem B6371095 : Blo 1116628 6371095 := bstep (se 1 (by rfl) ⟨4778321, by rfl⟩ : syracuseStep 6371095 = 9556643) B9556643
theorem B46479521 : Blo 1116628 46479521 := bstep (se 2 (by rfl) ⟨17429820, by rfl⟩ : syracuseStep 46479521 = 34859641) B34859641
theorem B7158719 : Blo 1116628 7158719 := bstep (se 1 (by rfl) ⟨5369039, by rfl⟩ : syracuseStep 7158719 = 10738079) B10738079
theorem B8076455 : Blo 1116628 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B2014471 : Blo 1116628 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B12763331 : Blo 1116628 12763331 := bstep (se 1 (by rfl) ⟨9572498, by rfl⟩ : syracuseStep 12763331 = 19144997) B19144997
theorem B13582885 : Blo 1116628 13582885 := bstep (se 4 (by rfl) ⟨1273395, by rfl⟩ : syracuseStep 13582885 = 2546791) B2546791
theorem B1885855 : Blo 1116628 1885855 := bstep (se 1 (by rfl) ⟨1414391, by rfl⟩ : syracuseStep 1885855 = 2828783) B2828783
theorem B36292535 : Blo 1116628 36292535 := bstep (se 1 (by rfl) ⟨27219401, by rfl⟩ : syracuseStep 36292535 = 54438803) B54438803
theorem B4245803 : Blo 1116628 4245803 := bstep (se 1 (by rfl) ⟨3184352, by rfl⟩ : syracuseStep 4245803 = 6368705) B6368705
theorem B1788655 : Blo 1116628 1788655 := bstep (se 1 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 1788655 = 2682983) B2682983
theorem B2149343 : Blo 1116628 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B13619087 : Blo 1116628 13619087 := bstep (se 1 (by rfl) ⟨10214315, by rfl⟩ : syracuseStep 13619087 = 20428631) B20428631
theorem B1888447 : Blo 1116628 1888447 := bstep (se 1 (by rfl) ⟨1416335, by rfl⟩ : syracuseStep 1888447 = 2832671) B2832671
theorem B1594847 : Blo 1116628 1594847 := bstep (se 1 (by rfl) ⟨1196135, by rfl⟩ : syracuseStep 1594847 = 2392271) B2392271
theorem B2512439 : Blo 1116628 2512439 := bstep (se 1 (by rfl) ⟨1884329, by rfl⟩ : syracuseStep 2512439 = 3768659) B3768659
theorem B3397231 : Blo 1116628 3397231 := bstep (se 1 (by rfl) ⟨2547923, by rfl⟩ : syracuseStep 3397231 = 5095847) B5095847
theorem B34461379 : Blo 1116628 34461379 := bstep (se 1 (by rfl) ⟨25846034, by rfl⟩ : syracuseStep 34461379 = 51692069) B51692069
theorem B5658497 : Blo 1116628 5658497 := bstep (se 2 (by rfl) ⟨2121936, by rfl⟩ : syracuseStep 5658497 = 4243873) B4243873
theorem B4249705 : Blo 1116628 4249705 := bstep (se 2 (by rfl) ⟨1593639, by rfl⟩ : syracuseStep 4249705 = 3187279) B3187279
theorem B1890985 : Blo 1116628 1890985 := bstep (se 2 (by rfl) ⟨709119, by rfl⟩ : syracuseStep 1890985 = 1418239) B1418239
theorem B4250495 : Blo 1116628 4250495 := bstep (se 1 (by rfl) ⟨3187871, by rfl⟩ : syracuseStep 4250495 = 6375743) B6375743
theorem B2513915 : Blo 1116628 2513915 := bstep (se 1 (by rfl) ⟨1885436, by rfl⟩ : syracuseStep 2513915 = 3770873) B3770873
theorem B2514023 : Blo 1116628 2514023 := bstep (se 1 (by rfl) ⟨1885517, by rfl⟩ : syracuseStep 2514023 = 3771035) B3771035
theorem B7167689 : Blo 1116628 7167689 := bstep (se 2 (by rfl) ⟨2687883, by rfl⟩ : syracuseStep 7167689 = 5375767) B5375767
theorem B5660441 : Blo 1116628 5660441 := bstep (se 2 (by rfl) ⟨2122665, by rfl⟩ : syracuseStep 5660441 = 4245331) B4245331
theorem B9069011 : Blo 1116628 9069011 := bstep (se 1 (by rfl) ⟨6801758, by rfl⟩ : syracuseStep 9069011 = 13603517) B13603517
theorem B28632203 : Blo 1116628 28632203 := bstep (se 1 (by rfl) ⟨21474152, by rfl⟩ : syracuseStep 28632203 = 42948305) B42948305
theorem B2123167 : Blo 1116628 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B2123471 : Blo 1116628 2123471 := bstep (se 1 (by rfl) ⟨1592603, by rfl⟩ : syracuseStep 2123471 = 3185207) B3185207
theorem B5662547 : Blo 1116628 5662547 := bstep (se 1 (by rfl) ⟨4246910, by rfl⟩ : syracuseStep 5662547 = 8493821) B8493821
theorem B11495789 : Blo 1116628 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B628091297 : Blo 1116628 628091297 := bstep (se 2 (by rfl) ⟨235534236, by rfl⟩ : syracuseStep 628091297 = 471068473) B471068473
theorem B14314157 : Blo 1116628 14314157 := bstep (se 3 (by rfl) ⟨2683904, by rfl⟩ : syracuseStep 14314157 = 5367809) B5367809
theorem B2386667 : Blo 1116628 2386667 := bstep (se 1 (by rfl) ⟨1790000, by rfl⟩ : syracuseStep 2386667 = 3580001) B3580001
theorem B5663519 : Blo 1116628 5663519 := bstep (se 1 (by rfl) ⟨4247639, by rfl⟩ : syracuseStep 5663519 = 8495279) B8495279
theorem B2517857 : Blo 1116628 2517857 := bstep (se 2 (by rfl) ⟨944196, by rfl⟩ : syracuseStep 2517857 = 1888393) B1888393
theorem B2124883 : Blo 1116628 2124883 := bstep (se 1 (by rfl) ⟨1593662, by rfl⟩ : syracuseStep 2124883 = 3187325) B3187325
theorem B15494561 : Blo 1116628 15494561 := bstep (se 2 (by rfl) ⟨5810460, by rfl⟩ : syracuseStep 15494561 = 11620921) B11620921
theorem B2519009 : Blo 1116628 2519009 := bstep (se 2 (by rfl) ⟨944628, by rfl⟩ : syracuseStep 2519009 = 1889257) B1889257
theorem B2519081 : Blo 1116628 2519081 := bstep (se 2 (by rfl) ⟨944655, by rfl⟩ : syracuseStep 2519081 = 1889311) B1889311
theorem B45936827 : Blo 1116628 45936827 := bstep (se 1 (by rfl) ⟨34452620, by rfl⟩ : syracuseStep 45936827 = 68905241) B68905241
theorem B5370077 : Blo 1116628 5370077 := bstep (se 3 (by rfl) ⟨1006889, by rfl⟩ : syracuseStep 5370077 = 2013779) B2013779
theorem B2519531 : Blo 1116628 2519531 := bstep (se 1 (by rfl) ⟨1889648, by rfl⟩ : syracuseStep 2519531 = 3779297) B3779297
theorem B2127055 : Blo 1116628 2127055 := bstep (se 1 (by rfl) ⟨1595291, by rfl⟩ : syracuseStep 2127055 = 3190583) B3190583
theorem B2127161 : Blo 1116628 2127161 := bstep (se 2 (by rfl) ⟨797685, by rfl⟩ : syracuseStep 2127161 = 1595371) B1595371
theorem B21525821 : Blo 1116628 21525821 := bstep (se 3 (by rfl) ⟨4036091, by rfl⟩ : syracuseStep 21525821 = 8072183) B8072183
theorem B2127215 : Blo 1116628 2127215 := bstep (se 1 (by rfl) ⟨1595411, by rfl⟩ : syracuseStep 2127215 = 3190823) B3190823
theorem B2521295 : Blo 1116628 2521295 := bstep (se 1 (by rfl) ⟨1890971, by rfl⟩ : syracuseStep 2521295 = 3781943) B3781943
theorem B18643771 : Blo 1116628 18643771 := bstep (se 1 (by rfl) ⟨13982828, by rfl⟩ : syracuseStep 18643771 = 27965657) B27965657
theorem B9567305 : Blo 1116628 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B2391707 : Blo 1116628 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B9079391 : Blo 1116628 9079391 := bstep (se 1 (by rfl) ⟨6809543, by rfl⟩ : syracuseStep 9079391 = 13619087) B13619087
theorem B1117339 : Blo 1116628 1117339 := bstep (se 1 (by rfl) ⟨838004, by rfl⟩ : syracuseStep 1117339 = 1676009) B1676009
theorem B1117375 : Blo 1116628 1117375 := bstep (se 1 (by rfl) ⟨838031, by rfl⟩ : syracuseStep 1117375 = 1676063) B1676063
theorem B1117435 : Blo 1116628 1117435 := bstep (se 1 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 1117435 = 1676153) B1676153
theorem B5672429 : Blo 1116628 5672429 := bstep (se 3 (by rfl) ⟨1063580, by rfl⟩ : syracuseStep 5672429 = 2127161) B2127161
theorem B1117679 : Blo 1116628 1117679 := bstep (se 1 (by rfl) ⟨838259, by rfl⟩ : syracuseStep 1117679 = 1676519) B1676519
theorem B1117695 : Blo 1116628 1117695 := bstep (se 1 (by rfl) ⟨838271, by rfl⟩ : syracuseStep 1117695 = 1676543) B1676543
theorem B1674959 : Blo 1116628 1674959 := bstep (se 1 (by rfl) ⟨1256219, by rfl⟩ : syracuseStep 1674959 = 2512439) B2512439
theorem B3772331 : Blo 1116628 3772331 := bstep (se 1 (by rfl) ⟨2829248, by rfl⟩ : syracuseStep 3772331 = 5658497) B5658497
theorem B1118239 : Blo 1116628 1118239 := bstep (se 1 (by rfl) ⟨838679, by rfl⟩ : syracuseStep 1118239 = 1677359) B1677359
theorem B3772925 : Blo 1116628 3772925 := bstep (se 3 (by rfl) ⟨707423, by rfl⟩ : syracuseStep 3772925 = 1414847) B1414847
theorem B1118847 : Blo 1116628 1118847 := bstep (se 1 (by rfl) ⟨839135, by rfl⟩ : syracuseStep 1118847 = 1678271) B1678271
theorem B1675943 : Blo 1116628 1675943 := bstep (se 1 (by rfl) ⟨1256957, by rfl⟩ : syracuseStep 1675943 = 2513915) B2513915
theorem B1676015 : Blo 1116628 1676015 := bstep (se 1 (by rfl) ⟨1257011, by rfl⟩ : syracuseStep 1676015 = 2514023) B2514023
theorem B1119399 : Blo 1116628 1119399 := bstep (se 1 (by rfl) ⟨839549, by rfl⟩ : syracuseStep 1119399 = 1679099) B1679099
theorem B3773627 : Blo 1116628 3773627 := bstep (se 1 (by rfl) ⟨2830220, by rfl⟩ : syracuseStep 3773627 = 5660441) B5660441
theorem B1119771 : Blo 1116628 1119771 := bstep (se 1 (by rfl) ⟨839828, by rfl⟩ : syracuseStep 1119771 = 1679657) B1679657
theorem B18159299 : Blo 1116628 18159299 := bstep (se 1 (by rfl) ⟨13619474, by rfl⟩ : syracuseStep 18159299 = 27238949) B27238949
theorem B3020495 : Blo 1116628 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B1677065 : Blo 1116628 1677065 := bstep (se 2 (by rfl) ⟨628899, by rfl⟩ : syracuseStep 1677065 = 1257799) B1257799
theorem B1120127 : Blo 1116628 1120127 := bstep (se 1 (by rfl) ⟨840095, by rfl⟩ : syracuseStep 1120127 = 1680191) B1680191
theorem B1120251 : Blo 1116628 1120251 := bstep (se 1 (by rfl) ⟨840188, by rfl⟩ : syracuseStep 1120251 = 1680377) B1680377
theorem B1120283 : Blo 1116628 1120283 := bstep (se 1 (by rfl) ⟨840212, by rfl⟩ : syracuseStep 1120283 = 1680425) B1680425
theorem B1120383 : Blo 1116628 1120383 := bstep (se 1 (by rfl) ⟨840287, by rfl⟩ : syracuseStep 1120383 = 1680575) B1680575
theorem B1120539 : Blo 1116628 1120539 := bstep (se 1 (by rfl) ⟨840404, by rfl⟩ : syracuseStep 1120539 = 1680809) B1680809
theorem B1677689 : Blo 1116628 1677689 := bstep (se 2 (by rfl) ⟨629133, by rfl⟩ : syracuseStep 1677689 = 1258267) B1258267
theorem B1415647 : Blo 1116628 1415647 := bstep (se 1 (by rfl) ⟨1061735, by rfl⟩ : syracuseStep 1415647 = 2123471) B2123471
theorem B4037161 : Blo 1116628 4037161 := bstep (se 2 (by rfl) ⟨1513935, by rfl⟩ : syracuseStep 4037161 = 3027871) B3027871
theorem B3775031 : Blo 1116628 3775031 := bstep (se 1 (by rfl) ⟨2831273, by rfl⟩ : syracuseStep 3775031 = 5662547) B5662547
theorem B9542771 : Blo 1116628 9542771 := bstep (se 1 (by rfl) ⟨7157078, by rfl⟩ : syracuseStep 9542771 = 14314157) B14314157
theorem B3775679 : Blo 1116628 3775679 := bstep (se 1 (by rfl) ⟨2831759, by rfl⟩ : syracuseStep 3775679 = 5663519) B5663519
theorem B1678571 : Blo 1116628 1678571 := bstep (se 1 (by rfl) ⟨1258928, by rfl⟩ : syracuseStep 1678571 = 2517857) B2517857
theorem B45948505 : Blo 1116628 45948505 := bstep (se 2 (by rfl) ⟨17230689, by rfl⟩ : syracuseStep 45948505 = 34461379) B34461379
theorem B10329707 : Blo 1116628 10329707 := bstep (se 1 (by rfl) ⟨7747280, by rfl⟩ : syracuseStep 10329707 = 15494561) B15494561
theorem B8494793 : Blo 1116628 8494793 := bstep (se 2 (by rfl) ⟨3185547, by rfl⟩ : syracuseStep 8494793 = 6371095) B6371095
theorem B3022703 : Blo 1116628 3022703 := bstep (se 1 (by rfl) ⟨2267027, by rfl⟩ : syracuseStep 3022703 = 4534055) B4534055
theorem B1679339 : Blo 1116628 1679339 := bstep (se 1 (by rfl) ⟨1259504, by rfl⟩ : syracuseStep 1679339 = 2519009) B2519009
theorem B1679387 : Blo 1116628 1679387 := bstep (se 1 (by rfl) ⟨1259540, by rfl⟩ : syracuseStep 1679387 = 2519081) B2519081
theorem B6365263 : Blo 1116628 6365263 := bstep (se 1 (by rfl) ⟨4773947, by rfl⟩ : syracuseStep 6365263 = 9547895) B9547895
theorem B3580051 : Blo 1116628 3580051 := bstep (se 1 (by rfl) ⟨2685038, by rfl⟩ : syracuseStep 3580051 = 5370077) B5370077
theorem B1679687 : Blo 1116628 1679687 := bstep (se 1 (by rfl) ⟨1259765, by rfl⟩ : syracuseStep 1679687 = 2519531) B2519531
theorem B1418143 : Blo 1116628 1418143 := bstep (se 1 (by rfl) ⟨1063607, by rfl⟩ : syracuseStep 1418143 = 2127215) B2127215
theorem B1680863 : Blo 1116628 1680863 := bstep (se 1 (by rfl) ⟨1260647, by rfl⟩ : syracuseStep 1680863 = 2521295) B2521295
theorem B5384303 : Blo 1116628 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B24195023 : Blo 1116628 24195023 := bstep (se 1 (by rfl) ⟨18146267, by rfl⟩ : syracuseStep 24195023 = 36292535) B36292535
theorem B2830535 : Blo 1116628 2830535 := bstep (se 1 (by rfl) ⟨2122901, by rfl⟩ : syracuseStep 2830535 = 4245803) B4245803
theorem B2830889 : Blo 1116628 2830889 := bstep (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) B2123167
theorem B2012251 : Blo 1116628 2012251 := bstep (se 1 (by rfl) ⟨1509188, by rfl⟩ : syracuseStep 2012251 = 3018377) B3018377
theorem B3585883 : Blo 1116628 3585883 := bstep (se 1 (by rfl) ⟨2689412, by rfl⟩ : syracuseStep 3585883 = 5378825) B5378825
theorem B2833177 : Blo 1116628 2833177 := bstep (se 2 (by rfl) ⟨1062441, by rfl⟩ : syracuseStep 2833177 = 2124883) B2124883
theorem B2833663 : Blo 1116628 2833663 := bstep (se 1 (by rfl) ⟨2125247, by rfl⟩ : syracuseStep 2833663 = 4250495) B4250495
theorem B6046007 : Blo 1116628 6046007 := bstep (se 1 (by rfl) ⟨4534505, by rfl⟩ : syracuseStep 6046007 = 9069011) B9069011
theorem B1884539 : Blo 1116628 1884539 := bstep (se 1 (by rfl) ⟨1413404, by rfl⟩ : syracuseStep 1884539 = 2826809) B2826809
theorem B19088135 : Blo 1116628 19088135 := bstep (se 1 (by rfl) ⟨14316101, by rfl⟩ : syracuseStep 19088135 = 28632203) B28632203
theorem B2836073 : Blo 1116628 2836073 := bstep (se 2 (by rfl) ⟨1063527, by rfl⟩ : syracuseStep 2836073 = 2127055) B2127055
theorem B418727531 : Blo 1116628 418727531 := bstep (se 1 (by rfl) ⟨314045648, by rfl⟩ : syracuseStep 418727531 = 628091297) B628091297
theorem B8504999 : Blo 1116628 8504999 := bstep (se 1 (by rfl) ⟨6378749, by rfl⟩ : syracuseStep 8504999 = 12757499) B12757499
theorem B1591111 : Blo 1116628 1591111 := bstep (se 1 (by rfl) ⟨1193333, by rfl⟩ : syracuseStep 1591111 = 2386667) B2386667
theorem B30624551 : Blo 1116628 30624551 := bstep (se 1 (by rfl) ⟨22968413, by rfl⟩ : syracuseStep 30624551 = 45936827) B45936827
theorem B24858361 : Blo 1116628 24858361 := bstep (se 2 (by rfl) ⟨9321885, by rfl⟩ : syracuseStep 24858361 = 18643771) B18643771
theorem B30986347 : Blo 1116628 30986347 := bstep (se 1 (by rfl) ⟨23239760, by rfl⟩ : syracuseStep 30986347 = 46479521) B46479521
theorem B6377885 : Blo 1116628 6377885 := bstep (se 3 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 6377885 = 2391707) B2391707
theorem B4772479 : Blo 1116628 4772479 := bstep (se 1 (by rfl) ⟨3579359, by rfl⟩ : syracuseStep 4772479 = 7158719) B7158719
theorem B6378203 : Blo 1116628 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B2151289 : Blo 1116628 2151289 := bstep (se 2 (by rfl) ⟨806733, by rfl⟩ : syracuseStep 2151289 = 1613467) B1613467
theorem B8508887 : Blo 1116628 8508887 := bstep (se 1 (by rfl) ⟨6381665, by rfl⟩ : syracuseStep 8508887 = 12763331) B12763331
theorem B18110513 : Blo 1116628 18110513 := bstep (se 2 (by rfl) ⟨6791442, by rfl⟩ : syracuseStep 18110513 = 13582885) B13582885
theorem B2513519 : Blo 1116628 2513519 := bstep (se 1 (by rfl) ⟨1885139, by rfl⟩ : syracuseStep 2513519 = 3770279) B3770279
theorem B4250465 : Blo 1116628 4250465 := bstep (se 2 (by rfl) ⟨1593924, by rfl⟩ : syracuseStep 4250465 = 3187849) B3187849
theorem B4774889 : Blo 1116628 4774889 := bstep (se 2 (by rfl) ⟨1790583, by rfl⟩ : syracuseStep 4774889 = 3581167) B3581167
theorem B1432895 : Blo 1116628 1432895 := bstep (se 1 (by rfl) ⟨1074671, by rfl⟩ : syracuseStep 1432895 = 2149343) B2149343
theorem B2514473 : Blo 1116628 2514473 := bstep (se 2 (by rfl) ⟨942927, by rfl⟩ : syracuseStep 2514473 = 1885855) B1885855
theorem B2514923 : Blo 1116628 2514923 := bstep (se 1 (by rfl) ⟨1886192, by rfl⟩ : syracuseStep 2514923 = 3772385) B3772385
theorem B2515103 : Blo 1116628 2515103 := bstep (se 1 (by rfl) ⟨1886327, by rfl⟩ : syracuseStep 2515103 = 3772655) B3772655
theorem B1794331 : Blo 1116628 1794331 := bstep (se 1 (by rfl) ⟨1345748, by rfl⟩ : syracuseStep 1794331 = 2691497) B2691497
theorem B2384873 : Blo 1116628 2384873 := bstep (se 2 (by rfl) ⟨894327, by rfl⟩ : syracuseStep 2384873 = 1788655) B1788655
theorem B4252925 : Blo 1116628 4252925 := bstep (se 3 (by rfl) ⟨797423, by rfl⟩ : syracuseStep 4252925 = 1594847) B1594847
theorem B2123243 : Blo 1116628 2123243 := bstep (se 1 (by rfl) ⟨1592432, by rfl⟩ : syracuseStep 2123243 = 3184865) B3184865
theorem B40822541 : Blo 1116628 40822541 := bstep (se 3 (by rfl) ⟨7654226, by rfl⟩ : syracuseStep 40822541 = 15308453) B15308453
theorem B2517083 : Blo 1116628 2517083 := bstep (se 1 (by rfl) ⟨1887812, by rfl⟩ : syracuseStep 2517083 = 3775625) B3775625
theorem B4778459 : Blo 1116628 4778459 := bstep (se 1 (by rfl) ⟨3583844, by rfl⟩ : syracuseStep 4778459 = 7167689) B7167689
theorem B2517929 : Blo 1116628 2517929 := bstep (se 2 (by rfl) ⟨944223, by rfl⟩ : syracuseStep 2517929 = 1888447) B1888447
theorem B2518127 : Blo 1116628 2518127 := bstep (se 1 (by rfl) ⟨1888595, by rfl⟩ : syracuseStep 2518127 = 3777191) B3777191
theorem B12087515 : Blo 1116628 12087515 := bstep (se 1 (by rfl) ⟨9065636, by rfl⟩ : syracuseStep 12087515 = 18131273) B18131273
theorem B7663859 : Blo 1116628 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B2519891 : Blo 1116628 2519891 := bstep (se 1 (by rfl) ⟨1889918, by rfl⟩ : syracuseStep 2519891 = 3779837) B3779837
theorem B2126675 : Blo 1116628 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B5666273 : Blo 1116628 5666273 := bstep (se 2 (by rfl) ⟨2124852, by rfl⟩ : syracuseStep 5666273 = 4249705) B4249705
theorem B2520683 : Blo 1116628 2520683 := bstep (se 1 (by rfl) ⟨1890512, by rfl⟩ : syracuseStep 2520683 = 3781025) B3781025
theorem B61306703 : Blo 1116628 61306703 := bstep (se 1 (by rfl) ⟨45980027, by rfl⟩ : syracuseStep 61306703 = 91960055) B91960055
theorem B2520935 : Blo 1116628 2520935 := bstep (se 1 (by rfl) ⟨1890701, by rfl⟩ : syracuseStep 2520935 = 3781403) B3781403
theorem B18118565 : Blo 1116628 18118565 := bstep (se 4 (by rfl) ⟨1698615, by rfl⟩ : syracuseStep 18118565 = 3397231) B3397231
theorem B14350547 : Blo 1116628 14350547 := bstep (se 1 (by rfl) ⟨10762910, by rfl⟩ : syracuseStep 14350547 = 21525821) B21525821
theorem B2521313 : Blo 1116628 2521313 := bstep (se 2 (by rfl) ⟨945492, by rfl⟩ : syracuseStep 2521313 = 1890985) B1890985
theorem B2685961 : Blo 1116628 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B8487017 : Blo 1116628 8487017 := bstep (se 2 (by rfl) ⟨3182631, by rfl⟩ : syracuseStep 8487017 = 6365263) B6365263
theorem B16122685 : Blo 1116628 16122685 := bstep (se 3 (by rfl) ⟨3023003, by rfl⟩ : syracuseStep 16122685 = 6046007) B6046007
theorem B279151687 : Blo 1116628 279151687 := bstep (se 1 (by rfl) ⟨209363765, by rfl⟩ : syracuseStep 279151687 = 418727531) B418727531
theorem B5669999 : Blo 1116628 5669999 := bstep (se 1 (by rfl) ⟨4252499, by rfl⟩ : syracuseStep 5669999 = 8504999) B8504999
theorem B9569765 : Blo 1116628 9569765 := bstep (se 4 (by rfl) ⟨897165, by rfl⟩ : syracuseStep 9569765 = 1794331) B1794331
theorem B20416367 : Blo 1116628 20416367 := bstep (se 1 (by rfl) ⟨15312275, by rfl⟩ : syracuseStep 20416367 = 30624551) B30624551
theorem B5671133 : Blo 1116628 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B1116639 : Blo 1116628 1116639 := bstep (se 1 (by rfl) ⟨837479, by rfl⟩ : syracuseStep 1116639 = 1674959) B1674959
theorem B1117295 : Blo 1116628 1117295 := bstep (se 1 (by rfl) ⟨837971, by rfl⟩ : syracuseStep 1117295 = 1675943) B1675943
theorem B1117343 : Blo 1116628 1117343 := bstep (se 1 (by rfl) ⟨838007, by rfl⟩ : syracuseStep 1117343 = 1676015) B1676015
theorem B5672591 : Blo 1116628 5672591 := bstep (se 1 (by rfl) ⟨4254443, by rfl⟩ : syracuseStep 5672591 = 8508887) B8508887
theorem B1118043 : Blo 1116628 1118043 := bstep (se 1 (by rfl) ⟨838532, by rfl⟩ : syracuseStep 1118043 = 1677065) B1677065
theorem B1118459 : Blo 1116628 1118459 := bstep (se 1 (by rfl) ⟨838844, by rfl⟩ : syracuseStep 1118459 = 1677689) B1677689
theorem B1675679 : Blo 1116628 1675679 := bstep (se 1 (by rfl) ⟨1256759, by rfl⟩ : syracuseStep 1675679 = 2513519) B2513519
theorem B3183259 : Blo 1116628 3183259 := bstep (se 1 (by rfl) ⟨2387444, by rfl⟩ : syracuseStep 3183259 = 4774889) B4774889
theorem B6361847 : Blo 1116628 6361847 := bstep (se 1 (by rfl) ⟨4771385, by rfl⟩ : syracuseStep 6361847 = 9542771) B9542771
theorem B1119047 : Blo 1116628 1119047 := bstep (se 1 (by rfl) ⟨839285, by rfl⟩ : syracuseStep 1119047 = 1678571) B1678571
theorem B1676315 : Blo 1116628 1676315 := bstep (se 1 (by rfl) ⟨1257236, by rfl⟩ : syracuseStep 1676315 = 2514473) B2514473
theorem B6886471 : Blo 1116628 6886471 := bstep (se 1 (by rfl) ⟨5164853, by rfl⟩ : syracuseStep 6886471 = 10329707) B10329707
theorem B1676615 : Blo 1116628 1676615 := bstep (se 1 (by rfl) ⟨1257461, by rfl⟩ : syracuseStep 1676615 = 2514923) B2514923
theorem B1119559 : Blo 1116628 1119559 := bstep (se 1 (by rfl) ⟨839669, by rfl⟩ : syracuseStep 1119559 = 1679339) B1679339
theorem B1119591 : Blo 1116628 1119591 := bstep (se 1 (by rfl) ⟨839693, by rfl⟩ : syracuseStep 1119591 = 1679387) B1679387
theorem B1676735 : Blo 1116628 1676735 := bstep (se 1 (by rfl) ⟨1257551, by rfl⟩ : syracuseStep 1676735 = 2515103) B2515103
theorem B1119791 : Blo 1116628 1119791 := bstep (se 1 (by rfl) ⟨839843, by rfl⟩ : syracuseStep 1119791 = 1679687) B1679687
theorem B6363305 : Blo 1116628 6363305 := bstep (se 2 (by rfl) ⟨2386239, by rfl⟩ : syracuseStep 6363305 = 4772479) B4772479
theorem B1120575 : Blo 1116628 1120575 := bstep (se 1 (by rfl) ⟨840431, by rfl⟩ : syracuseStep 1120575 = 1680863) B1680863
theorem B1415495 : Blo 1116628 1415495 := bstep (se 1 (by rfl) ⟨1061621, by rfl⟩ : syracuseStep 1415495 = 2123243) B2123243
theorem B1678055 : Blo 1116628 1678055 := bstep (se 1 (by rfl) ⟨1258541, by rfl⟩ : syracuseStep 1678055 = 2517083) B2517083
theorem B3185639 : Blo 1116628 3185639 := bstep (se 1 (by rfl) ⟨2389229, by rfl⟩ : syracuseStep 3185639 = 4778459) B4778459
theorem B1678619 : Blo 1116628 1678619 := bstep (se 1 (by rfl) ⟨1258964, by rfl⟩ : syracuseStep 1678619 = 2517929) B2517929
theorem B1678751 : Blo 1116628 1678751 := bstep (se 1 (by rfl) ⟨1259063, by rfl⟩ : syracuseStep 1678751 = 2518127) B2518127
theorem B16130015 : Blo 1116628 16130015 := bstep (se 1 (by rfl) ⟨12097511, by rfl⟩ : syracuseStep 16130015 = 24195023) B24195023
theorem B1679927 : Blo 1116628 1679927 := bstep (se 1 (by rfl) ⟨1259945, by rfl⟩ : syracuseStep 1679927 = 2519891) B2519891
theorem B5382881 : Blo 1116628 5382881 := bstep (se 2 (by rfl) ⟨2018580, by rfl⟩ : syracuseStep 5382881 = 4037161) B4037161
theorem B3777515 : Blo 1116628 3777515 := bstep (se 1 (by rfl) ⟨2833136, by rfl⟩ : syracuseStep 3777515 = 5666273) B5666273
theorem B3777569 : Blo 1116628 3777569 := bstep (se 2 (by rfl) ⟨1416588, by rfl⟩ : syracuseStep 3777569 = 2833177) B2833177
theorem B1680455 : Blo 1116628 1680455 := bstep (se 1 (by rfl) ⟨1260341, by rfl⟩ : syracuseStep 1680455 = 2520683) B2520683
theorem B40871135 : Blo 1116628 40871135 := bstep (se 1 (by rfl) ⟨30653351, by rfl⟩ : syracuseStep 40871135 = 61306703) B61306703
theorem B1680623 : Blo 1116628 1680623 := bstep (se 1 (by rfl) ⟨1260467, by rfl⟩ : syracuseStep 1680623 = 2520935) B2520935
theorem B3581281 : Blo 1116628 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B1680875 : Blo 1116628 1680875 := bstep (se 1 (by rfl) ⟨1260656, by rfl⟩ : syracuseStep 1680875 = 2521313) B2521313
theorem B3778217 : Blo 1116628 3778217 := bstep (se 2 (by rfl) ⟨1416831, by rfl⟩ : syracuseStep 3778217 = 2833663) B2833663
theorem B1256359 : Blo 1116628 1256359 := bstep (se 1 (by rfl) ⟨942269, by rfl⟩ : syracuseStep 1256359 = 1884539) B1884539
theorem B12725423 : Blo 1116628 12725423 := bstep (se 1 (by rfl) ⟨9544067, by rfl⟩ : syracuseStep 12725423 = 19088135) B19088135
theorem B3781619 : Blo 1116628 3781619 := bstep (se 1 (by rfl) ⟨2836214, by rfl⟩ : syracuseStep 3781619 = 5672429) B5672429
theorem B15284213 : Blo 1116628 15284213 := bstep (se 5 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 15284213 = 1432895) B1432895
theorem B12106199 : Blo 1116628 12106199 := bstep (se 1 (by rfl) ⟨9079649, by rfl⟩ : syracuseStep 12106199 = 18159299) B18159299
theorem B2833643 : Blo 1116628 2833643 := bstep (se 1 (by rfl) ⟨2125232, by rfl⟩ : syracuseStep 2833643 = 4250465) B4250465
theorem B33144481 : Blo 1116628 33144481 := bstep (se 2 (by rfl) ⟨12429180, by rfl⟩ : syracuseStep 33144481 = 24858361) B24858361
theorem B2015135 : Blo 1116628 2015135 := bstep (se 1 (by rfl) ⟨1511351, by rfl⟩ : syracuseStep 2015135 = 3022703) B3022703
theorem B1589915 : Blo 1116628 1589915 := bstep (se 1 (by rfl) ⟨1192436, by rfl⟩ : syracuseStep 1589915 = 2384873) B2384873
theorem B2835283 : Blo 1116628 2835283 := bstep (se 1 (by rfl) ⟨2126462, by rfl⟩ : syracuseStep 2835283 = 4252925) B4252925
theorem B2868385 : Blo 1116628 2868385 := bstep (se 2 (by rfl) ⟨1075644, by rfl⟩ : syracuseStep 2868385 = 2151289) B2151289
theorem B27215027 : Blo 1116628 27215027 := bstep (se 1 (by rfl) ⟨20411270, by rfl⟩ : syracuseStep 27215027 = 40822541) B40822541
theorem B3589535 : Blo 1116628 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B1887023 : Blo 1116628 1887023 := bstep (se 1 (by rfl) ⟨1415267, by rfl⟩ : syracuseStep 1887023 = 2830535) B2830535
theorem B1887259 : Blo 1116628 1887259 := bstep (se 1 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 1887259 = 2830889) B2830889
theorem B1887529 : Blo 1116628 1887529 := bstep (se 2 (by rfl) ⟨707823, by rfl⟩ : syracuseStep 1887529 = 1415647) B1415647
theorem B12079043 : Blo 1116628 12079043 := bstep (se 1 (by rfl) ⟨9059282, by rfl⟩ : syracuseStep 12079043 = 18118565) B18118565
theorem B61264673 : Blo 1116628 61264673 := bstep (se 2 (by rfl) ⟨22974252, by rfl⟩ : syracuseStep 61264673 = 45948505) B45948505
theorem B4773401 : Blo 1116628 4773401 := bstep (se 2 (by rfl) ⟨1790025, by rfl⟩ : syracuseStep 4773401 = 3580051) B3580051
theorem B32233373 : Blo 1116628 32233373 := bstep (se 3 (by rfl) ⟨6043757, by rfl⟩ : syracuseStep 32233373 = 12087515) B12087515
theorem B1890715 : Blo 1116628 1890715 := bstep (se 1 (by rfl) ⟨1418036, by rfl⟩ : syracuseStep 1890715 = 2836073) B2836073
theorem B1890857 : Blo 1116628 1890857 := bstep (se 2 (by rfl) ⟨709071, by rfl⟩ : syracuseStep 1890857 = 1418143) B1418143
theorem B2121481 : Blo 1116628 2121481 := bstep (se 2 (by rfl) ⟨795555, by rfl⟩ : syracuseStep 2121481 = 1591111) B1591111
theorem B2514887 : Blo 1116628 2514887 := bstep (se 1 (by rfl) ⟨1886165, by rfl⟩ : syracuseStep 2514887 = 3772331) B3772331
theorem B4251923 : Blo 1116628 4251923 := bstep (se 1 (by rfl) ⟨3188942, by rfl⟩ : syracuseStep 4251923 = 6377885) B6377885
theorem B2515283 : Blo 1116628 2515283 := bstep (se 1 (by rfl) ⟨1886462, by rfl⟩ : syracuseStep 2515283 = 3772925) B3772925
theorem B4252135 : Blo 1116628 4252135 := bstep (se 1 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 4252135 = 6378203) B6378203
theorem B2515751 : Blo 1116628 2515751 := bstep (se 1 (by rfl) ⟨1886813, by rfl⟩ : syracuseStep 2515751 = 3773627) B3773627
theorem B2516687 : Blo 1116628 2516687 := bstep (se 1 (by rfl) ⟨1887515, by rfl⟩ : syracuseStep 2516687 = 3775031) B3775031
theorem B8054653 : Blo 1116628 8054653 := bstep (se 3 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 8054653 = 3020495) B3020495
theorem B2517119 : Blo 1116628 2517119 := bstep (se 1 (by rfl) ⟨1887839, by rfl⟩ : syracuseStep 2517119 = 3775679) B3775679
theorem B5663195 : Blo 1116628 5663195 := bstep (se 1 (by rfl) ⟨4247396, by rfl⟩ : syracuseStep 5663195 = 8494793) B8494793
theorem B48294701 : Blo 1116628 48294701 := bstep (se 3 (by rfl) ⟨9055256, by rfl⟩ : syracuseStep 48294701 = 18110513) B18110513
theorem B41315129 : Blo 1116628 41315129 := bstep (se 2 (by rfl) ⟨15493173, by rfl⟩ : syracuseStep 41315129 = 30986347) B30986347
theorem B2683001 : Blo 1116628 2683001 := bstep (se 2 (by rfl) ⟨1006125, by rfl⟩ : syracuseStep 2683001 = 2012251) B2012251
theorem B24211709 : Blo 1116628 24211709 := bstep (se 3 (by rfl) ⟨4539695, by rfl⟩ : syracuseStep 24211709 = 9079391) B9079391
theorem B4781177 : Blo 1116628 4781177 := bstep (se 2 (by rfl) ⟨1792941, by rfl⟩ : syracuseStep 4781177 = 3585883) B3585883
theorem B5109239 : Blo 1116628 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B9567031 : Blo 1116628 9567031 := bstep (se 1 (by rfl) ⟨7175273, by rfl⟩ : syracuseStep 9567031 = 14350547) B14350547
theorem B5669513 : Blo 1116628 5669513 := bstep (se 2 (by rfl) ⟨2126067, by rfl⟩ : syracuseStep 5669513 = 4252135) B4252135
theorem B2393023 : Blo 1116628 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B21496913 : Blo 1116628 21496913 := bstep (se 2 (by rfl) ⟨8061342, by rfl⟩ : syracuseStep 21496913 = 16122685) B16122685
theorem B1117119 : Blo 1116628 1117119 := bstep (se 1 (by rfl) ⟨837839, by rfl⟩ : syracuseStep 1117119 = 1675679) B1675679
theorem B1117543 : Blo 1116628 1117543 := bstep (se 1 (by rfl) ⟨838157, by rfl⟩ : syracuseStep 1117543 = 1676315) B1676315
theorem B1117743 : Blo 1116628 1117743 := bstep (se 1 (by rfl) ⟨838307, by rfl⟩ : syracuseStep 1117743 = 1676615) B1676615
theorem B1117823 : Blo 1116628 1117823 := bstep (se 1 (by rfl) ⟨838367, by rfl⟩ : syracuseStep 1117823 = 1676735) B1676735
theorem B3182267 : Blo 1116628 3182267 := bstep (se 1 (by rfl) ⟨2386700, by rfl⟩ : syracuseStep 3182267 = 4773401) B4773401
theorem B1675145 : Blo 1116628 1675145 := bstep (se 2 (by rfl) ⟨628179, by rfl⟩ : syracuseStep 1675145 = 1256359) B1256359
theorem B1118703 : Blo 1116628 1118703 := bstep (se 1 (by rfl) ⟨839027, by rfl⟩ : syracuseStep 1118703 = 1678055) B1678055
theorem B1119079 : Blo 1116628 1119079 := bstep (se 1 (by rfl) ⟨839309, by rfl⟩ : syracuseStep 1119079 = 1678619) B1678619
theorem B1119167 : Blo 1116628 1119167 := bstep (se 1 (by rfl) ⟨839375, by rfl⟩ : syracuseStep 1119167 = 1678751) B1678751
theorem B1676591 : Blo 1116628 1676591 := bstep (se 1 (by rfl) ⟨1257443, by rfl⟩ : syracuseStep 1676591 = 2514887) B2514887
theorem B10753343 : Blo 1116628 10753343 := bstep (se 1 (by rfl) ⟨8065007, by rfl⟩ : syracuseStep 10753343 = 16130015) B16130015
theorem B1676855 : Blo 1116628 1676855 := bstep (se 1 (by rfl) ⟨1257641, by rfl⟩ : syracuseStep 1676855 = 2515283) B2515283
theorem B1119951 : Blo 1116628 1119951 := bstep (se 1 (by rfl) ⟨839963, by rfl⟩ : syracuseStep 1119951 = 1679927) B1679927
theorem B1677167 : Blo 1116628 1677167 := bstep (se 1 (by rfl) ⟨1257875, by rfl⟩ : syracuseStep 1677167 = 2515751) B2515751
theorem B1120303 : Blo 1116628 1120303 := bstep (se 1 (by rfl) ⟨840227, by rfl⟩ : syracuseStep 1120303 = 1680455) B1680455
theorem B1120415 : Blo 1116628 1120415 := bstep (se 1 (by rfl) ⟨840311, by rfl⟩ : syracuseStep 1120415 = 1680623) B1680623
theorem B3774653 : Blo 1116628 3774653 := bstep (se 3 (by rfl) ⟨707747, by rfl⟩ : syracuseStep 3774653 = 1415495) B1415495
theorem B1120583 : Blo 1116628 1120583 := bstep (se 1 (by rfl) ⟨840437, by rfl⟩ : syracuseStep 1120583 = 1680875) B1680875
theorem B1677791 : Blo 1116628 1677791 := bstep (se 1 (by rfl) ⟨1258343, by rfl⟩ : syracuseStep 1677791 = 2516687) B2516687
theorem B32283197 : Blo 1116628 32283197 := bstep (se 3 (by rfl) ⟨6053099, by rfl⟩ : syracuseStep 32283197 = 12106199) B12106199
theorem B1678079 : Blo 1116628 1678079 := bstep (se 1 (by rfl) ⟨1258559, by rfl⟩ : syracuseStep 1678079 = 2517119) B2517119
theorem B9181961 : Blo 1116628 9181961 := bstep (se 2 (by rfl) ⟨3443235, by rfl⟩ : syracuseStep 9181961 = 6886471) B6886471
theorem B3775463 : Blo 1116628 3775463 := bstep (se 1 (by rfl) ⟨2831597, by rfl⟩ : syracuseStep 3775463 = 5663195) B5663195
theorem B3187451 : Blo 1116628 3187451 := bstep (se 1 (by rfl) ⟨2390588, by rfl⟩ : syracuseStep 3187451 = 4781177) B4781177
theorem B12756041 : Blo 1116628 12756041 := bstep (se 2 (by rfl) ⟨4783515, by rfl⟩ : syracuseStep 12756041 = 9567031) B9567031
theorem B2828641 : Blo 1116628 2828641 := bstep (se 2 (by rfl) ⟨1060740, by rfl⟩ : syracuseStep 2828641 = 2121481) B2121481
theorem B7154669 : Blo 1116628 7154669 := bstep (se 3 (by rfl) ⟨1341500, by rfl⟩ : syracuseStep 7154669 = 2683001) B2683001
theorem B3779999 : Blo 1116628 3779999 := bstep (se 1 (by rfl) ⟨2834999, by rfl⟩ : syracuseStep 3779999 = 5669999) B5669999
theorem B3780377 : Blo 1116628 3780377 := bstep (se 2 (by rfl) ⟨1417641, by rfl⟩ : syracuseStep 3780377 = 2835283) B2835283
theorem B13610911 : Blo 1116628 13610911 := bstep (se 1 (by rfl) ⟨10208183, by rfl⟩ : syracuseStep 13610911 = 20416367) B20416367
theorem B3780755 : Blo 1116628 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B4239773 : Blo 1116628 4239773 := bstep (se 3 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 4239773 = 1589915) B1589915
theorem B1258015 : Blo 1116628 1258015 := bstep (se 1 (by rfl) ⟨943511, by rfl⟩ : syracuseStep 1258015 = 1887023) B1887023
theorem B3781727 : Blo 1116628 3781727 := bstep (se 1 (by rfl) ⟨2836295, by rfl⟩ : syracuseStep 3781727 = 5672591) B5672591
theorem B4241231 : Blo 1116628 4241231 := bstep (se 1 (by rfl) ⟨3180923, by rfl⟩ : syracuseStep 4241231 = 6361847) B6361847
theorem B40843115 : Blo 1116628 40843115 := bstep (se 1 (by rfl) ⟨30632336, by rfl⟩ : syracuseStep 40843115 = 61264673) B61264673
theorem B4242203 : Blo 1116628 4242203 := bstep (se 1 (by rfl) ⟨3181652, by rfl⟩ : syracuseStep 4242203 = 6363305) B6363305
theorem B1260571 : Blo 1116628 1260571 := bstep (se 1 (by rfl) ⟨945428, by rfl⟩ : syracuseStep 1260571 = 1890857) B1890857
theorem B2834615 : Blo 1116628 2834615 := bstep (se 1 (by rfl) ⟨2125961, by rfl⟩ : syracuseStep 2834615 = 4251923) B4251923
theorem B3588587 : Blo 1116628 3588587 := bstep (se 1 (by rfl) ⟨2691440, by rfl⟩ : syracuseStep 3588587 = 5382881) B5382881
theorem B27247423 : Blo 1116628 27247423 := bstep (se 1 (by rfl) ⟨20435567, by rfl⟩ : syracuseStep 27247423 = 40871135) B40871135
theorem B4244345 : Blo 1116628 4244345 := bstep (se 2 (by rfl) ⟨1591629, by rfl⟩ : syracuseStep 4244345 = 3183259) B3183259
theorem B32196467 : Blo 1116628 32196467 := bstep (se 1 (by rfl) ⟨24147350, by rfl⟩ : syracuseStep 32196467 = 48294701) B48294701
theorem B27543419 : Blo 1116628 27543419 := bstep (se 1 (by rfl) ⟨20657564, by rfl⟩ : syracuseStep 27543419 = 41315129) B41315129
theorem B16141139 : Blo 1116628 16141139 := bstep (se 1 (by rfl) ⟨12105854, by rfl⟩ : syracuseStep 16141139 = 24211709) B24211709
theorem B1889095 : Blo 1116628 1889095 := bstep (se 1 (by rfl) ⟨1416821, by rfl⟩ : syracuseStep 1889095 = 2833643) B2833643
theorem B44192641 : Blo 1116628 44192641 := bstep (se 2 (by rfl) ⟨16572240, by rfl⟩ : syracuseStep 44192641 = 33144481) B33144481
theorem B5658011 : Blo 1116628 5658011 := bstep (se 1 (by rfl) ⟨4243508, by rfl⟩ : syracuseStep 5658011 = 8487017) B8487017
theorem B18143351 : Blo 1116628 18143351 := bstep (se 1 (by rfl) ⟨13607513, by rfl⟩ : syracuseStep 18143351 = 27215027) B27215027
theorem B6379843 : Blo 1116628 6379843 := bstep (se 1 (by rfl) ⟨4784882, by rfl⟩ : syracuseStep 6379843 = 9569765) B9569765
theorem B372202249 : Blo 1116628 372202249 := bstep (se 2 (by rfl) ⟨139575843, by rfl⟩ : syracuseStep 372202249 = 279151687) B279151687
theorem B3824513 : Blo 1116628 3824513 := bstep (se 2 (by rfl) ⟨1434192, by rfl⟩ : syracuseStep 3824513 = 2868385) B2868385
theorem B4775041 : Blo 1116628 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B10739537 : Blo 1116628 10739537 := bstep (se 2 (by rfl) ⟨4027326, by rfl⟩ : syracuseStep 10739537 = 8054653) B8054653
theorem B8052695 : Blo 1116628 8052695 := bstep (se 1 (by rfl) ⟨6039521, by rfl⟩ : syracuseStep 8052695 = 12079043) B12079043
theorem B21488915 : Blo 1116628 21488915 := bstep (se 1 (by rfl) ⟨16116686, by rfl⟩ : syracuseStep 21488915 = 32233373) B32233373
theorem B2516345 : Blo 1116628 2516345 := bstep (se 2 (by rfl) ⟨943629, by rfl⟩ : syracuseStep 2516345 = 1887259) B1887259
theorem B2516705 : Blo 1116628 2516705 := bstep (se 2 (by rfl) ⟨943764, by rfl⟩ : syracuseStep 2516705 = 1887529) B1887529
theorem B2123759 : Blo 1116628 2123759 := bstep (se 1 (by rfl) ⟨1592819, by rfl⟩ : syracuseStep 2123759 = 3185639) B3185639
theorem B2518343 : Blo 1116628 2518343 := bstep (se 1 (by rfl) ⟨1888757, by rfl⟩ : syracuseStep 2518343 = 3777515) B3777515
theorem B2518379 : Blo 1116628 2518379 := bstep (se 1 (by rfl) ⟨1888784, by rfl⟩ : syracuseStep 2518379 = 3777569) B3777569
theorem B2518811 : Blo 1116628 2518811 := bstep (se 1 (by rfl) ⟨1889108, by rfl⟩ : syracuseStep 2518811 = 3778217) B3778217
theorem B8483615 : Blo 1116628 8483615 := bstep (se 1 (by rfl) ⟨6362711, by rfl⟩ : syracuseStep 8483615 = 12725423) B12725423
theorem B2520953 : Blo 1116628 2520953 := bstep (se 2 (by rfl) ⟨945357, by rfl⟩ : syracuseStep 2520953 = 1890715) B1890715
theorem B2521079 : Blo 1116628 2521079 := bstep (se 1 (by rfl) ⟨1890809, by rfl⟩ : syracuseStep 2521079 = 3781619) B3781619
theorem B3406159 : Blo 1116628 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B10189475 : Blo 1116628 10189475 := bstep (se 1 (by rfl) ⟨7642106, by rfl⟩ : syracuseStep 10189475 = 15284213) B15284213
theorem B1343423 : Blo 1116628 1343423 := bstep (se 1 (by rfl) ⟨1007567, by rfl⟩ : syracuseStep 1343423 = 2015135) B2015135
theorem B2392391 : Blo 1116628 2392391 := bstep (se 1 (by rfl) ⟨1794293, by rfl⟩ : syracuseStep 2392391 = 3588587) B3588587
theorem B21464311 : Blo 1116628 21464311 := bstep (se 1 (by rfl) ⟨16098233, by rfl⟩ : syracuseStep 21464311 = 32196467) B32196467
theorem B1116763 : Blo 1116628 1116763 := bstep (se 1 (by rfl) ⟨837572, by rfl⟩ : syracuseStep 1116763 = 1675145) B1675145
theorem B3771521 : Blo 1116628 3771521 := bstep (se 2 (by rfl) ⟨1414320, by rfl⟩ : syracuseStep 3771521 = 2828641) B2828641
theorem B1117727 : Blo 1116628 1117727 := bstep (se 1 (by rfl) ⟨838295, by rfl⟩ : syracuseStep 1117727 = 1676591) B1676591
theorem B3772007 : Blo 1116628 3772007 := bstep (se 1 (by rfl) ⟨2829005, by rfl⟩ : syracuseStep 3772007 = 5658011) B5658011
theorem B1117903 : Blo 1116628 1117903 := bstep (se 1 (by rfl) ⟨838427, by rfl⟩ : syracuseStep 1117903 = 1676855) B1676855
theorem B1118111 : Blo 1116628 1118111 := bstep (se 1 (by rfl) ⟨838583, by rfl⟩ : syracuseStep 1118111 = 1677167) B1677167
theorem B12095567 : Blo 1116628 12095567 := bstep (se 1 (by rfl) ⟨9071675, by rfl⟩ : syracuseStep 12095567 = 18143351) B18143351
theorem B1118527 : Blo 1116628 1118527 := bstep (se 1 (by rfl) ⟨838895, by rfl⟩ : syracuseStep 1118527 = 1677791) B1677791
theorem B1118719 : Blo 1116628 1118719 := bstep (se 1 (by rfl) ⟨839039, by rfl⟩ : syracuseStep 1118719 = 1678079) B1678079
theorem B1677353 : Blo 1116628 1677353 := bstep (se 2 (by rfl) ⟨629007, by rfl⟩ : syracuseStep 1677353 = 1258015) B1258015
theorem B14325943 : Blo 1116628 14325943 := bstep (se 1 (by rfl) ⟨10744457, by rfl⟩ : syracuseStep 14325943 = 21488915) B21488915
theorem B1677563 : Blo 1116628 1677563 := bstep (se 1 (by rfl) ⟨1258172, by rfl⟩ : syracuseStep 1677563 = 2516345) B2516345
theorem B1677803 : Blo 1116628 1677803 := bstep (se 1 (by rfl) ⟨1258352, by rfl⟩ : syracuseStep 1677803 = 2516705) B2516705
theorem B58923521 : Blo 1116628 58923521 := bstep (se 2 (by rfl) ⟨22096320, by rfl⟩ : syracuseStep 58923521 = 44192641) B44192641
theorem B1678895 : Blo 1116628 1678895 := bstep (se 1 (by rfl) ⟨1259171, by rfl⟩ : syracuseStep 1678895 = 2518343) B2518343
theorem B1678919 : Blo 1116628 1678919 := bstep (se 1 (by rfl) ⟨1259189, by rfl⟩ : syracuseStep 1678919 = 2518379) B2518379
theorem B1679207 : Blo 1116628 1679207 := bstep (se 1 (by rfl) ⟨1259405, by rfl⟩ : syracuseStep 1679207 = 2518811) B2518811
theorem B2826515 : Blo 1116628 2826515 := bstep (se 1 (by rfl) ⟨2119886, by rfl⟩ : syracuseStep 2826515 = 4239773) B4239773
theorem B2827487 : Blo 1116628 2827487 := bstep (se 1 (by rfl) ⟨2120615, by rfl⟩ : syracuseStep 2827487 = 4241231) B4241231
theorem B1680635 : Blo 1116628 1680635 := bstep (se 1 (by rfl) ⟨1260476, by rfl⟩ : syracuseStep 1680635 = 2520953) B2520953
theorem B1680719 : Blo 1116628 1680719 := bstep (se 1 (by rfl) ⟨1260539, by rfl⟩ : syracuseStep 1680719 = 2521079) B2521079
theorem B1680761 : Blo 1116628 1680761 := bstep (se 2 (by rfl) ⟨630285, by rfl⟩ : syracuseStep 1680761 = 1260571) B1260571
theorem B6366721 : Blo 1116628 6366721 := bstep (se 2 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 6366721 = 4775041) B4775041
theorem B6792983 : Blo 1116628 6792983 := bstep (se 1 (by rfl) ⟨5094737, by rfl⟩ : syracuseStep 6792983 = 10189475) B10189475
theorem B2828135 : Blo 1116628 2828135 := bstep (se 1 (by rfl) ⟨2121101, by rfl⟩ : syracuseStep 2828135 = 4242203) B4242203
theorem B3582461 : Blo 1116628 3582461 := bstep (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) B1343423
theorem B3779675 : Blo 1116628 3779675 := bstep (se 1 (by rfl) ⟨2834756, by rfl⟩ : syracuseStep 3779675 = 5669513) B5669513
theorem B2829563 : Blo 1116628 2829563 := bstep (se 1 (by rfl) ⟨2122172, by rfl⟩ : syracuseStep 2829563 = 4244345) B4244345
theorem B14331275 : Blo 1116628 14331275 := bstep (se 1 (by rfl) ⟨10748456, by rfl⟩ : syracuseStep 14331275 = 21496913) B21496913
theorem B18362279 : Blo 1116628 18362279 := bstep (se 1 (by rfl) ⟨13771709, by rfl⟩ : syracuseStep 18362279 = 27543419) B27543419
theorem B3190697 : Blo 1116628 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B10760759 : Blo 1116628 10760759 := bstep (se 1 (by rfl) ⟨8070569, by rfl⟩ : syracuseStep 10760759 = 16141139) B16141139
theorem B7159691 : Blo 1116628 7159691 := bstep (se 1 (by rfl) ⟨5369768, by rfl⟩ : syracuseStep 7159691 = 10739537) B10739537
theorem B8504027 : Blo 1116628 8504027 := bstep (se 1 (by rfl) ⟨6378020, by rfl⟩ : syracuseStep 8504027 = 12756041) B12756041
theorem B4769779 : Blo 1116628 4769779 := bstep (se 1 (by rfl) ⟨3577334, by rfl⟩ : syracuseStep 4769779 = 7154669) B7154669
theorem B8506457 : Blo 1116628 8506457 := bstep (se 2 (by rfl) ⟨3189921, by rfl⟩ : syracuseStep 8506457 = 6379843) B6379843
theorem B4541545 : Blo 1116628 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B5655743 : Blo 1116628 5655743 := bstep (se 1 (by rfl) ⟨4241807, by rfl⟩ : syracuseStep 5655743 = 8483615) B8483615
theorem B1889743 : Blo 1116628 1889743 := bstep (se 1 (by rfl) ⟨1417307, by rfl⟩ : syracuseStep 1889743 = 2834615) B2834615
theorem B36329897 : Blo 1116628 36329897 := bstep (se 2 (by rfl) ⟨13623711, by rfl⟩ : syracuseStep 36329897 = 27247423) B27247423
theorem B7168895 : Blo 1116628 7168895 := bstep (se 1 (by rfl) ⟨5376671, by rfl⟩ : syracuseStep 7168895 = 10753343) B10753343
theorem B2516435 : Blo 1116628 2516435 := bstep (se 1 (by rfl) ⟨1887326, by rfl⟩ : syracuseStep 2516435 = 3774653) B3774653
theorem B21522131 : Blo 1116628 21522131 := bstep (se 1 (by rfl) ⟨16141598, by rfl⟩ : syracuseStep 21522131 = 32283197) B32283197
theorem B6121307 : Blo 1116628 6121307 := bstep (se 1 (by rfl) ⟨4590980, by rfl⟩ : syracuseStep 6121307 = 9181961) B9181961
theorem B2549675 : Blo 1116628 2549675 := bstep (se 1 (by rfl) ⟨1912256, by rfl⟩ : syracuseStep 2549675 = 3824513) B3824513
theorem B2516975 : Blo 1116628 2516975 := bstep (se 1 (by rfl) ⟨1887731, by rfl⟩ : syracuseStep 2516975 = 3775463) B3775463
theorem B18147881 : Blo 1116628 18147881 := bstep (se 2 (by rfl) ⟨6805455, by rfl⟩ : syracuseStep 18147881 = 13610911) B13610911
theorem B5663357 : Blo 1116628 5663357 := bstep (se 3 (by rfl) ⟨1061879, by rfl⟩ : syracuseStep 5663357 = 2123759) B2123759
theorem B5368463 : Blo 1116628 5368463 := bstep (se 1 (by rfl) ⟨4026347, by rfl⟩ : syracuseStep 5368463 = 8052695) B8052695
theorem B2124967 : Blo 1116628 2124967 := bstep (se 1 (by rfl) ⟨1593725, by rfl⟩ : syracuseStep 2124967 = 3187451) B3187451
theorem B2518793 : Blo 1116628 2518793 := bstep (se 2 (by rfl) ⟨944547, by rfl⟩ : syracuseStep 2518793 = 1889095) B1889095
theorem B2519999 : Blo 1116628 2519999 := bstep (se 1 (by rfl) ⟨1889999, by rfl⟩ : syracuseStep 2519999 = 3779999) B3779999
theorem B2520251 : Blo 1116628 2520251 := bstep (se 1 (by rfl) ⟨1890188, by rfl⟩ : syracuseStep 2520251 = 3780377) B3780377
theorem B2520503 : Blo 1116628 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B2521151 : Blo 1116628 2521151 := bstep (se 1 (by rfl) ⟨1890863, by rfl⟩ : syracuseStep 2521151 = 3781727) B3781727
theorem B496269665 : Blo 1116628 496269665 := bstep (se 2 (by rfl) ⟨186101124, by rfl⟩ : syracuseStep 496269665 = 372202249) B372202249
theorem B27228743 : Blo 1116628 27228743 := bstep (se 1 (by rfl) ⟨20421557, by rfl⟩ : syracuseStep 27228743 = 40843115) B40843115
theorem B8486045 : Blo 1116628 8486045 := bstep (se 3 (by rfl) ⟨1591133, by rfl⟩ : syracuseStep 8486045 = 3182267) B3182267
theorem B5669351 : Blo 1116628 5669351 := bstep (se 1 (by rfl) ⟨4252013, by rfl⟩ : syracuseStep 5669351 = 8504027) B8504027
theorem B8488961 : Blo 1116628 8488961 := bstep (se 2 (by rfl) ⟨3183360, by rfl⟩ : syracuseStep 8488961 = 6366721) B6366721
theorem B5670971 : Blo 1116628 5670971 := bstep (se 1 (by rfl) ⟨4253228, by rfl⟩ : syracuseStep 5670971 = 8506457) B8506457
theorem B3770495 : Blo 1116628 3770495 := bstep (se 1 (by rfl) ⟨2827871, by rfl⟩ : syracuseStep 3770495 = 5655743) B5655743
theorem B6359705 : Blo 1116628 6359705 := bstep (se 2 (by rfl) ⟨2384889, by rfl⟩ : syracuseStep 6359705 = 4769779) B4769779
theorem B8063711 : Blo 1116628 8063711 := bstep (se 1 (by rfl) ⟨6047783, by rfl⟩ : syracuseStep 8063711 = 12095567) B12095567
theorem B1118235 : Blo 1116628 1118235 := bstep (se 1 (by rfl) ⟨838676, by rfl⟩ : syracuseStep 1118235 = 1677353) B1677353
theorem B1118375 : Blo 1116628 1118375 := bstep (se 1 (by rfl) ⟨838781, by rfl⟩ : syracuseStep 1118375 = 1677563) B1677563
theorem B24219931 : Blo 1116628 24219931 := bstep (se 1 (by rfl) ⟨18164948, by rfl⟩ : syracuseStep 24219931 = 36329897) B36329897
theorem B1118535 : Blo 1116628 1118535 := bstep (se 1 (by rfl) ⟨838901, by rfl⟩ : syracuseStep 1118535 = 1677803) B1677803
theorem B1119263 : Blo 1116628 1119263 := bstep (se 1 (by rfl) ⟨839447, by rfl⟩ : syracuseStep 1119263 = 1678895) B1678895
theorem B1119279 : Blo 1116628 1119279 := bstep (se 1 (by rfl) ⟨839459, by rfl⟩ : syracuseStep 1119279 = 1678919) B1678919
theorem B1119471 : Blo 1116628 1119471 := bstep (se 1 (by rfl) ⟨839603, by rfl⟩ : syracuseStep 1119471 = 1679207) B1679207
theorem B1120423 : Blo 1116628 1120423 := bstep (se 1 (by rfl) ⟨840317, by rfl⟩ : syracuseStep 1120423 = 1680635) B1680635
theorem B1120479 : Blo 1116628 1120479 := bstep (se 1 (by rfl) ⟨840359, by rfl⟩ : syracuseStep 1120479 = 1680719) B1680719
theorem B1120507 : Blo 1116628 1120507 := bstep (se 1 (by rfl) ⟨840380, by rfl⟩ : syracuseStep 1120507 = 1680761) B1680761
theorem B1677623 : Blo 1116628 1677623 := bstep (se 1 (by rfl) ⟨1258217, by rfl⟩ : syracuseStep 1677623 = 2516435) B2516435
theorem B4528655 : Blo 1116628 4528655 := bstep (se 1 (by rfl) ⟨3396491, by rfl⟩ : syracuseStep 4528655 = 6792983) B6792983
theorem B1677983 : Blo 1116628 1677983 := bstep (se 1 (by rfl) ⟨1258487, by rfl⟩ : syracuseStep 1677983 = 2516975) B2516975
theorem B12098587 : Blo 1116628 12098587 := bstep (se 1 (by rfl) ⟨9073940, by rfl⟩ : syracuseStep 12098587 = 18147881) B18147881
theorem B3775571 : Blo 1116628 3775571 := bstep (se 1 (by rfl) ⟨2831678, by rfl⟩ : syracuseStep 3775571 = 5663357) B5663357
theorem B3578975 : Blo 1116628 3578975 := bstep (se 1 (by rfl) ⟨2684231, by rfl⟩ : syracuseStep 3578975 = 5368463) B5368463
theorem B1679195 : Blo 1116628 1679195 := bstep (se 1 (by rfl) ⟨1259396, by rfl⟩ : syracuseStep 1679195 = 2518793) B2518793
theorem B1679999 : Blo 1116628 1679999 := bstep (se 1 (by rfl) ⟨1259999, by rfl⟩ : syracuseStep 1679999 = 2519999) B2519999
theorem B1680167 : Blo 1116628 1680167 := bstep (se 1 (by rfl) ⟨1260125, by rfl⟩ : syracuseStep 1680167 = 2520251) B2520251
theorem B1680335 : Blo 1116628 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B1680767 : Blo 1116628 1680767 := bstep (se 1 (by rfl) ⟨1260575, by rfl⟩ : syracuseStep 1680767 = 2521151) B2521151
theorem B28619081 : Blo 1116628 28619081 := bstep (se 2 (by rfl) ⟨10732155, by rfl⟩ : syracuseStep 28619081 = 21464311) B21464311
theorem B2833289 : Blo 1116628 2833289 := bstep (se 2 (by rfl) ⟨1062483, by rfl⟩ : syracuseStep 2833289 = 2124967) B2124967
theorem B6799133 : Blo 1116628 6799133 := bstep (se 3 (by rfl) ⟨1274837, by rfl⟩ : syracuseStep 6799133 = 2549675) B2549675
theorem B1884343 : Blo 1116628 1884343 := bstep (se 1 (by rfl) ⟨1413257, by rfl⟩ : syracuseStep 1884343 = 2826515) B2826515
theorem B1884991 : Blo 1116628 1884991 := bstep (se 1 (by rfl) ⟨1413743, by rfl⟩ : syracuseStep 1884991 = 2827487) B2827487
theorem B4080871 : Blo 1116628 4080871 := bstep (se 1 (by rfl) ⟨3060653, by rfl⟩ : syracuseStep 4080871 = 6121307) B6121307
theorem B1885423 : Blo 1116628 1885423 := bstep (se 1 (by rfl) ⟨1414067, by rfl⟩ : syracuseStep 1885423 = 2828135) B2828135
theorem B1886375 : Blo 1116628 1886375 := bstep (se 1 (by rfl) ⟨1414781, by rfl⟩ : syracuseStep 1886375 = 2829563) B2829563
theorem B9554183 : Blo 1116628 9554183 := bstep (se 1 (by rfl) ⟨7165637, by rfl⟩ : syracuseStep 9554183 = 14331275) B14331275
theorem B12241519 : Blo 1116628 12241519 := bstep (se 1 (by rfl) ⟨9181139, by rfl⟩ : syracuseStep 12241519 = 18362279) B18362279
theorem B330846443 : Blo 1116628 330846443 := bstep (se 1 (by rfl) ⟨248134832, by rfl⟩ : syracuseStep 330846443 = 496269665) B496269665
theorem B5657363 : Blo 1116628 5657363 := bstep (se 1 (by rfl) ⟨4243022, by rfl⟩ : syracuseStep 5657363 = 8486045) B8486045
theorem B19092509 : Blo 1116628 19092509 := bstep (se 3 (by rfl) ⟨3579845, by rfl⟩ : syracuseStep 19092509 = 7159691) B7159691
theorem B1594927 : Blo 1116628 1594927 := bstep (se 1 (by rfl) ⟨1196195, by rfl⟩ : syracuseStep 1594927 = 2392391) B2392391
theorem B2514347 : Blo 1116628 2514347 := bstep (se 1 (by rfl) ⟨1885760, by rfl⟩ : syracuseStep 2514347 = 3771521) B3771521
theorem B2514671 : Blo 1116628 2514671 := bstep (se 1 (by rfl) ⟨1886003, by rfl⟩ : syracuseStep 2514671 = 3772007) B3772007
theorem B6055393 : Blo 1116628 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B39282347 : Blo 1116628 39282347 := bstep (se 1 (by rfl) ⟨29461760, by rfl⟩ : syracuseStep 39282347 = 58923521) B58923521
theorem B4779263 : Blo 1116628 4779263 := bstep (se 1 (by rfl) ⟨3584447, by rfl⟩ : syracuseStep 4779263 = 7168895) B7168895
theorem B14348087 : Blo 1116628 14348087 := bstep (se 1 (by rfl) ⟨10761065, by rfl⟩ : syracuseStep 14348087 = 21522131) B21522131
theorem B2388307 : Blo 1116628 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B2519657 : Blo 1116628 2519657 := bstep (se 2 (by rfl) ⟨944871, by rfl⟩ : syracuseStep 2519657 = 1889743) B1889743
theorem B2519783 : Blo 1116628 2519783 := bstep (se 1 (by rfl) ⟨1889837, by rfl⟩ : syracuseStep 2519783 = 3779675) B3779675
theorem B2127131 : Blo 1116628 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B19101257 : Blo 1116628 19101257 := bstep (se 2 (by rfl) ⟨7162971, by rfl⟩ : syracuseStep 19101257 = 14325943) B14325943
theorem B7173839 : Blo 1116628 7173839 := bstep (se 1 (by rfl) ⟨5380379, by rfl⟩ : syracuseStep 7173839 = 10760759) B10760759
theorem B18152495 : Blo 1116628 18152495 := bstep (se 1 (by rfl) ⟨13614371, by rfl⟩ : syracuseStep 18152495 = 27228743) B27228743
theorem B5375807 : Blo 1116628 5375807 := bstep (se 1 (by rfl) ⟨4031855, by rfl⟩ : syracuseStep 5375807 = 8063711) B8063711
theorem B220564295 : Blo 1116628 220564295 := bstep (se 1 (by rfl) ⟨165423221, by rfl⟩ : syracuseStep 220564295 = 330846443) B330846443
theorem B3771575 : Blo 1116628 3771575 := bstep (se 1 (by rfl) ⟨2828681, by rfl⟩ : syracuseStep 3771575 = 5657363) B5657363
theorem B1118415 : Blo 1116628 1118415 := bstep (se 1 (by rfl) ⟨838811, by rfl⟩ : syracuseStep 1118415 = 1677623) B1677623
theorem B3019103 : Blo 1116628 3019103 := bstep (se 1 (by rfl) ⟨2264327, by rfl⟩ : syracuseStep 3019103 = 4528655) B4528655
theorem B1118655 : Blo 1116628 1118655 := bstep (se 1 (by rfl) ⟨838991, by rfl⟩ : syracuseStep 1118655 = 1677983) B1677983
theorem B1676231 : Blo 1116628 1676231 := bstep (se 1 (by rfl) ⟨1257173, by rfl⟩ : syracuseStep 1676231 = 2514347) B2514347
theorem B1676447 : Blo 1116628 1676447 := bstep (se 1 (by rfl) ⟨1257335, by rfl⟩ : syracuseStep 1676447 = 2514671) B2514671
theorem B1119463 : Blo 1116628 1119463 := bstep (se 1 (by rfl) ⟨839597, by rfl⟩ : syracuseStep 1119463 = 1679195) B1679195
theorem B1119999 : Blo 1116628 1119999 := bstep (se 1 (by rfl) ⟨839999, by rfl⟩ : syracuseStep 1119999 = 1679999) B1679999
theorem B3184409 : Blo 1116628 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B1120111 : Blo 1116628 1120111 := bstep (se 1 (by rfl) ⟨840083, by rfl⟩ : syracuseStep 1120111 = 1680167) B1680167
theorem B1120223 : Blo 1116628 1120223 := bstep (se 1 (by rfl) ⟨840167, by rfl⟩ : syracuseStep 1120223 = 1680335) B1680335
theorem B1120511 : Blo 1116628 1120511 := bstep (se 1 (by rfl) ⟨840383, by rfl⟩ : syracuseStep 1120511 = 1680767) B1680767
theorem B26188231 : Blo 1116628 26188231 := bstep (se 1 (by rfl) ⟨19641173, by rfl⟩ : syracuseStep 26188231 = 39282347) B39282347
theorem B21764645 : Blo 1116628 21764645 := bstep (se 4 (by rfl) ⟨2040435, by rfl⟩ : syracuseStep 21764645 = 4080871) B4080871
theorem B3186175 : Blo 1116628 3186175 := bstep (se 1 (by rfl) ⟨2389631, by rfl⟩ : syracuseStep 3186175 = 4779263) B4779263
theorem B19079387 : Blo 1116628 19079387 := bstep (se 1 (by rfl) ⟨14309540, by rfl⟩ : syracuseStep 19079387 = 28619081) B28619081
theorem B1679771 : Blo 1116628 1679771 := bstep (se 1 (by rfl) ⟨1259828, by rfl⟩ : syracuseStep 1679771 = 2519657) B2519657
theorem B1679855 : Blo 1116628 1679855 := bstep (se 1 (by rfl) ⟨1259891, by rfl⟩ : syracuseStep 1679855 = 2519783) B2519783
theorem B1418087 : Blo 1116628 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B16131449 : Blo 1116628 16131449 := bstep (se 2 (by rfl) ⟨6049293, by rfl⟩ : syracuseStep 16131449 = 12098587) B12098587
theorem B12101663 : Blo 1116628 12101663 := bstep (se 1 (by rfl) ⟨9076247, by rfl⟩ : syracuseStep 12101663 = 18152495) B18152495
theorem B4532755 : Blo 1116628 4532755 := bstep (se 1 (by rfl) ⟨3399566, by rfl⟩ : syracuseStep 4532755 = 6799133) B6799133
theorem B3779567 : Blo 1116628 3779567 := bstep (se 1 (by rfl) ⟨2834675, by rfl⟩ : syracuseStep 3779567 = 5669351) B5669351
theorem B3780647 : Blo 1116628 3780647 := bstep (se 1 (by rfl) ⟨2835485, by rfl⟩ : syracuseStep 3780647 = 5670971) B5670971
theorem B1257583 : Blo 1116628 1257583 := bstep (se 1 (by rfl) ⟨943187, by rfl⟩ : syracuseStep 1257583 = 1886375) B1886375
theorem B6369455 : Blo 1116628 6369455 := bstep (se 1 (by rfl) ⟨4777091, by rfl⟩ : syracuseStep 6369455 = 9554183) B9554183
theorem B4239803 : Blo 1116628 4239803 := bstep (se 1 (by rfl) ⟨3179852, by rfl⟩ : syracuseStep 4239803 = 6359705) B6359705
theorem B8073857 : Blo 1116628 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B65288101 : Blo 1116628 65288101 := bstep (se 4 (by rfl) ⟨6120759, by rfl⟩ : syracuseStep 65288101 = 12241519) B12241519
theorem B12728339 : Blo 1116628 12728339 := bstep (se 1 (by rfl) ⟨9546254, by rfl⟩ : syracuseStep 12728339 = 19092509) B19092509
theorem B32293241 : Blo 1116628 32293241 := bstep (se 2 (by rfl) ⟨12109965, by rfl⟩ : syracuseStep 32293241 = 24219931) B24219931
theorem B12734171 : Blo 1116628 12734171 := bstep (se 1 (by rfl) ⟨9550628, by rfl⟩ : syracuseStep 12734171 = 19101257) B19101257
theorem B1888859 : Blo 1116628 1888859 := bstep (se 1 (by rfl) ⟨1416644, by rfl⟩ : syracuseStep 1888859 = 2833289) B2833289
theorem B2512457 : Blo 1116628 2512457 := bstep (se 2 (by rfl) ⟨942171, by rfl⟩ : syracuseStep 2512457 = 1884343) B1884343
theorem B2513321 : Blo 1116628 2513321 := bstep (se 2 (by rfl) ⟨942495, by rfl⟩ : syracuseStep 2513321 = 1884991) B1884991
theorem B5659307 : Blo 1116628 5659307 := bstep (se 1 (by rfl) ⟨4244480, by rfl⟩ : syracuseStep 5659307 = 8488961) B8488961
theorem B2513663 : Blo 1116628 2513663 := bstep (se 1 (by rfl) ⟨1885247, by rfl⟩ : syracuseStep 2513663 = 3770495) B3770495
theorem B2513897 : Blo 1116628 2513897 := bstep (se 2 (by rfl) ⟨942711, by rfl⟩ : syracuseStep 2513897 = 1885423) B1885423
theorem B2517047 : Blo 1116628 2517047 := bstep (se 1 (by rfl) ⟨1887785, by rfl⟩ : syracuseStep 2517047 = 3775571) B3775571
theorem B2385983 : Blo 1116628 2385983 := bstep (se 1 (by rfl) ⟨1789487, by rfl⟩ : syracuseStep 2385983 = 3578975) B3578975
theorem B2126569 : Blo 1116628 2126569 := bstep (se 2 (by rfl) ⟨797463, by rfl⟩ : syracuseStep 2126569 = 1594927) B1594927
theorem B9565391 : Blo 1116628 9565391 := bstep (se 1 (by rfl) ⟨7174043, by rfl⟩ : syracuseStep 9565391 = 14348087) B14348087
theorem B4782559 : Blo 1116628 4782559 := bstep (se 1 (by rfl) ⟨3586919, by rfl⟩ : syracuseStep 4782559 = 7173839) B7173839
theorem B21528827 : Blo 1116628 21528827 := bstep (se 1 (by rfl) ⟨16146620, by rfl⟩ : syracuseStep 21528827 = 32293241) B32293241
theorem B21530285 : Blo 1116628 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B8489447 : Blo 1116628 8489447 := bstep (se 1 (by rfl) ⟨6367085, by rfl⟩ : syracuseStep 8489447 = 12734171) B12734171
theorem B1117487 : Blo 1116628 1117487 := bstep (se 1 (by rfl) ⟨838115, by rfl⟩ : syracuseStep 1117487 = 1676231) B1676231
theorem B1117631 : Blo 1116628 1117631 := bstep (se 1 (by rfl) ⟨838223, by rfl⟩ : syracuseStep 1117631 = 1676447) B1676447
theorem B1674971 : Blo 1116628 1674971 := bstep (se 1 (by rfl) ⟨1256228, by rfl⟩ : syracuseStep 1674971 = 2512457) B2512457
theorem B1675547 : Blo 1116628 1675547 := bstep (se 1 (by rfl) ⟨1256660, by rfl⟩ : syracuseStep 1675547 = 2513321) B2513321
theorem B3772871 : Blo 1116628 3772871 := bstep (se 1 (by rfl) ⟨2829653, by rfl⟩ : syracuseStep 3772871 = 5659307) B5659307
theorem B1675775 : Blo 1116628 1675775 := bstep (se 1 (by rfl) ⟨1256831, by rfl⟩ : syracuseStep 1675775 = 2513663) B2513663
theorem B1675931 : Blo 1116628 1675931 := bstep (se 1 (by rfl) ⟨1256948, by rfl⟩ : syracuseStep 1675931 = 2513897) B2513897
theorem B12719591 : Blo 1116628 12719591 := bstep (se 1 (by rfl) ⟨9539693, by rfl⟩ : syracuseStep 12719591 = 19079387) B19079387
theorem B1676777 : Blo 1116628 1676777 := bstep (se 2 (by rfl) ⟨628791, by rfl⟩ : syracuseStep 1676777 = 1257583) B1257583
theorem B6362621 : Blo 1116628 6362621 := bstep (se 3 (by rfl) ⟨1192991, by rfl⟩ : syracuseStep 6362621 = 2385983) B2385983
theorem B1119847 : Blo 1116628 1119847 := bstep (se 1 (by rfl) ⟨839885, by rfl⟩ : syracuseStep 1119847 = 1679771) B1679771
theorem B1119903 : Blo 1116628 1119903 := bstep (se 1 (by rfl) ⟨839927, by rfl⟩ : syracuseStep 1119903 = 1679855) B1679855
theorem B10754299 : Blo 1116628 10754299 := bstep (se 1 (by rfl) ⟨8065724, by rfl⟩ : syracuseStep 10754299 = 16131449) B16131449
theorem B8067775 : Blo 1116628 8067775 := bstep (se 1 (by rfl) ⟨6050831, by rfl⟩ : syracuseStep 8067775 = 12101663) B12101663
theorem B1678031 : Blo 1116628 1678031 := bstep (se 1 (by rfl) ⟨1258523, by rfl⟩ : syracuseStep 1678031 = 2517047) B2517047
theorem B2826535 : Blo 1116628 2826535 := bstep (se 1 (by rfl) ⟨2119901, by rfl⟩ : syracuseStep 2826535 = 4239803) B4239803
theorem B3583871 : Blo 1116628 3583871 := bstep (se 1 (by rfl) ⟨2687903, by rfl⟩ : syracuseStep 3583871 = 5375807) B5375807
theorem B147042863 : Blo 1116628 147042863 := bstep (se 1 (by rfl) ⟨110282147, by rfl⟩ : syracuseStep 147042863 = 220564295) B220564295
theorem B3781565 : Blo 1116628 3781565 := bstep (se 3 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 3781565 = 1418087) B1418087
theorem B2012735 : Blo 1116628 2012735 := bstep (se 1 (by rfl) ⟨1509551, by rfl⟩ : syracuseStep 2012735 = 3019103) B3019103
theorem B1259239 : Blo 1116628 1259239 := bstep (se 1 (by rfl) ⟨944429, by rfl⟩ : syracuseStep 1259239 = 1888859) B1888859
theorem B6043673 : Blo 1116628 6043673 := bstep (se 2 (by rfl) ⟨2266377, by rfl⟩ : syracuseStep 6043673 = 4532755) B4532755
theorem B2835425 : Blo 1116628 2835425 := bstep (se 2 (by rfl) ⟨1063284, by rfl⟩ : syracuseStep 2835425 = 2126569) B2126569
theorem B87050801 : Blo 1116628 87050801 := bstep (se 2 (by rfl) ⟨32644050, by rfl⟩ : syracuseStep 87050801 = 65288101) B65288101
theorem B4246303 : Blo 1116628 4246303 := bstep (se 1 (by rfl) ⟨3184727, by rfl⟩ : syracuseStep 4246303 = 6369455) B6369455
theorem B34917641 : Blo 1116628 34917641 := bstep (se 2 (by rfl) ⟨13094115, by rfl⟩ : syracuseStep 34917641 = 26188231) B26188231
theorem B6376745 : Blo 1116628 6376745 := bstep (se 2 (by rfl) ⟨2391279, by rfl⟩ : syracuseStep 6376745 = 4782559) B4782559
theorem B6376927 : Blo 1116628 6376927 := bstep (se 1 (by rfl) ⟨4782695, by rfl⟩ : syracuseStep 6376927 = 9565391) B9565391
theorem B4248233 : Blo 1116628 4248233 := bstep (se 2 (by rfl) ⟨1593087, by rfl⟩ : syracuseStep 4248233 = 3186175) B3186175
theorem B2514383 : Blo 1116628 2514383 := bstep (se 1 (by rfl) ⟨1885787, by rfl⟩ : syracuseStep 2514383 = 3771575) B3771575
theorem B2122939 : Blo 1116628 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B14509763 : Blo 1116628 14509763 := bstep (se 1 (by rfl) ⟨10882322, by rfl⟩ : syracuseStep 14509763 = 21764645) B21764645
theorem B2519711 : Blo 1116628 2519711 := bstep (se 1 (by rfl) ⟨1889783, by rfl⟩ : syracuseStep 2519711 = 3779567) B3779567
theorem B2520431 : Blo 1116628 2520431 := bstep (se 1 (by rfl) ⟨1890323, by rfl⟩ : syracuseStep 2520431 = 3780647) B3780647
theorem B8485559 : Blo 1116628 8485559 := bstep (se 1 (by rfl) ⟨6364169, by rfl⟩ : syracuseStep 8485559 = 12728339) B12728339
theorem B14352551 : Blo 1116628 14352551 := bstep (se 1 (by rfl) ⟨10764413, by rfl⟩ : syracuseStep 14352551 = 21528827) B21528827
theorem B3768713 : Blo 1116628 3768713 := bstep (se 2 (by rfl) ⟨1413267, by rfl⟩ : syracuseStep 3768713 = 2826535) B2826535
theorem B14353523 : Blo 1116628 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B58033867 : Blo 1116628 58033867 := bstep (se 1 (by rfl) ⟨43525400, by rfl⟩ : syracuseStep 58033867 = 87050801) B87050801
theorem B1116647 : Blo 1116628 1116647 := bstep (se 1 (by rfl) ⟨837485, by rfl⟩ : syracuseStep 1116647 = 1674971) B1674971
theorem B1117031 : Blo 1116628 1117031 := bstep (se 1 (by rfl) ⟨837773, by rfl⟩ : syracuseStep 1117031 = 1675547) B1675547
theorem B1117183 : Blo 1116628 1117183 := bstep (se 1 (by rfl) ⟨837887, by rfl⟩ : syracuseStep 1117183 = 1675775) B1675775
theorem B1117287 : Blo 1116628 1117287 := bstep (se 1 (by rfl) ⟨837965, by rfl⟩ : syracuseStep 1117287 = 1675931) B1675931
theorem B1117851 : Blo 1116628 1117851 := bstep (se 1 (by rfl) ⟨838388, by rfl⟩ : syracuseStep 1117851 = 1676777) B1676777
theorem B1118687 : Blo 1116628 1118687 := bstep (se 1 (by rfl) ⟨839015, by rfl⟩ : syracuseStep 1118687 = 1678031) B1678031
theorem B1676255 : Blo 1116628 1676255 := bstep (se 1 (by rfl) ⟨1257191, by rfl⟩ : syracuseStep 1676255 = 2514383) B2514383
theorem B9673175 : Blo 1116628 9673175 := bstep (se 1 (by rfl) ⟨7254881, by rfl⟩ : syracuseStep 9673175 = 14509763) B14509763
theorem B1678985 : Blo 1116628 1678985 := bstep (se 2 (by rfl) ⟨629619, by rfl⟩ : syracuseStep 1678985 = 1259239) B1259239
theorem B1679807 : Blo 1116628 1679807 := bstep (se 1 (by rfl) ⟨1259855, by rfl⟩ : syracuseStep 1679807 = 2519711) B2519711
theorem B1680287 : Blo 1116628 1680287 := bstep (se 1 (by rfl) ⟨1260215, by rfl⟩ : syracuseStep 1680287 = 2520431) B2520431
theorem B10757033 : Blo 1116628 10757033 := bstep (se 2 (by rfl) ⟨4033887, by rfl⟩ : syracuseStep 10757033 = 8067775) B8067775
theorem B2830585 : Blo 1116628 2830585 := bstep (se 2 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 2830585 = 2122939) B2122939
theorem B23278427 : Blo 1116628 23278427 := bstep (se 1 (by rfl) ⟨17458820, by rfl⟩ : syracuseStep 23278427 = 34917641) B34917641
theorem B2832155 : Blo 1116628 2832155 := bstep (se 1 (by rfl) ⟨2124116, by rfl⟩ : syracuseStep 2832155 = 4248233) B4248233
theorem B4241747 : Blo 1116628 4241747 := bstep (se 1 (by rfl) ⟨3181310, by rfl⟩ : syracuseStep 4241747 = 6362621) B6362621
theorem B8502569 : Blo 1116628 8502569 := bstep (se 2 (by rfl) ⟨3188463, by rfl⟩ : syracuseStep 8502569 = 6376927) B6376927
theorem B14339065 : Blo 1116628 14339065 := bstep (se 2 (by rfl) ⟨5377149, by rfl⟩ : syracuseStep 14339065 = 10754299) B10754299
theorem B98028575 : Blo 1116628 98028575 := bstep (se 1 (by rfl) ⟨73521431, by rfl⟩ : syracuseStep 98028575 = 147042863) B147042863
theorem B5657039 : Blo 1116628 5657039 := bstep (se 1 (by rfl) ⟨4242779, by rfl⟩ : syracuseStep 5657039 = 8485559) B8485559
theorem B1890283 : Blo 1116628 1890283 := bstep (se 1 (by rfl) ⟨1417712, by rfl⟩ : syracuseStep 1890283 = 2835425) B2835425
theorem B5659631 : Blo 1116628 5659631 := bstep (se 1 (by rfl) ⟨4244723, by rfl⟩ : syracuseStep 5659631 = 8489447) B8489447
theorem B4251163 : Blo 1116628 4251163 := bstep (se 1 (by rfl) ⟨3188372, by rfl⟩ : syracuseStep 4251163 = 6376745) B6376745
theorem B2515247 : Blo 1116628 2515247 := bstep (se 1 (by rfl) ⟨1886435, by rfl⟩ : syracuseStep 2515247 = 3772871) B3772871
theorem B8479727 : Blo 1116628 8479727 := bstep (se 1 (by rfl) ⟨6359795, by rfl⟩ : syracuseStep 8479727 = 12719591) B12719591
theorem B5661737 : Blo 1116628 5661737 := bstep (se 2 (by rfl) ⟨2123151, by rfl⟩ : syracuseStep 5661737 = 4246303) B4246303
theorem B5367293 : Blo 1116628 5367293 := bstep (se 3 (by rfl) ⟨1006367, by rfl⟩ : syracuseStep 5367293 = 2012735) B2012735
theorem B2389247 : Blo 1116628 2389247 := bstep (se 1 (by rfl) ⟨1791935, by rfl⟩ : syracuseStep 2389247 = 3583871) B3583871
theorem B2521043 : Blo 1116628 2521043 := bstep (se 1 (by rfl) ⟨1890782, by rfl⟩ : syracuseStep 2521043 = 3781565) B3781565
theorem B4029115 : Blo 1116628 4029115 := bstep (se 1 (by rfl) ⟨3021836, by rfl⟩ : syracuseStep 4029115 = 6043673) B6043673
theorem B9568367 : Blo 1116628 9568367 := bstep (se 1 (by rfl) ⟨7176275, by rfl⟩ : syracuseStep 9568367 = 14352551) B14352551
theorem B9569015 : Blo 1116628 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B3771359 : Blo 1116628 3771359 := bstep (se 1 (by rfl) ⟨2828519, by rfl⟩ : syracuseStep 3771359 = 5657039) B5657039
theorem B1117503 : Blo 1116628 1117503 := bstep (se 1 (by rfl) ⟨838127, by rfl⟩ : syracuseStep 1117503 = 1676255) B1676255
theorem B3773087 : Blo 1116628 3773087 := bstep (se 1 (by rfl) ⟨2829815, by rfl⟩ : syracuseStep 3773087 = 5659631) B5659631
theorem B1119323 : Blo 1116628 1119323 := bstep (se 1 (by rfl) ⟨839492, by rfl⟩ : syracuseStep 1119323 = 1678985) B1678985
theorem B1676831 : Blo 1116628 1676831 := bstep (se 1 (by rfl) ⟨1257623, by rfl⟩ : syracuseStep 1676831 = 2515247) B2515247
theorem B1119871 : Blo 1116628 1119871 := bstep (se 1 (by rfl) ⟨839903, by rfl⟩ : syracuseStep 1119871 = 1679807) B1679807
theorem B3774113 : Blo 1116628 3774113 := bstep (se 2 (by rfl) ⟨1415292, by rfl⟩ : syracuseStep 3774113 = 2830585) B2830585
theorem B1120191 : Blo 1116628 1120191 := bstep (se 1 (by rfl) ⟨840143, by rfl⟩ : syracuseStep 1120191 = 1680287) B1680287
theorem B3774491 : Blo 1116628 3774491 := bstep (se 1 (by rfl) ⟨2830868, by rfl⟩ : syracuseStep 3774491 = 5661737) B5661737
theorem B3578195 : Blo 1116628 3578195 := bstep (se 1 (by rfl) ⟨2683646, by rfl⟩ : syracuseStep 3578195 = 5367293) B5367293
theorem B1680695 : Blo 1116628 1680695 := bstep (se 1 (by rfl) ⟨1260521, by rfl⟩ : syracuseStep 1680695 = 2521043) B2521043
theorem B2827831 : Blo 1116628 2827831 := bstep (se 1 (by rfl) ⟨2120873, by rfl⟩ : syracuseStep 2827831 = 4241747) B4241747
theorem B65352383 : Blo 1116628 65352383 := bstep (se 1 (by rfl) ⟨49014287, by rfl⟩ : syracuseStep 65352383 = 98028575) B98028575
theorem B77378489 : Blo 1116628 77378489 := bstep (se 2 (by rfl) ⟨29016933, by rfl⟩ : syracuseStep 77378489 = 58033867) B58033867
theorem B19118753 : Blo 1116628 19118753 := bstep (se 2 (by rfl) ⟨7169532, by rfl⟩ : syracuseStep 19118753 = 14339065) B14339065
theorem B5653151 : Blo 1116628 5653151 := bstep (se 1 (by rfl) ⟨4239863, by rfl⟩ : syracuseStep 5653151 = 8479727) B8479727
theorem B15518951 : Blo 1116628 15518951 := bstep (se 1 (by rfl) ⟨11639213, by rfl⟩ : syracuseStep 15518951 = 23278427) B23278427
theorem B1592831 : Blo 1116628 1592831 := bstep (se 1 (by rfl) ⟨1194623, by rfl⟩ : syracuseStep 1592831 = 2389247) B2389247
theorem B1888103 : Blo 1116628 1888103 := bstep (se 1 (by rfl) ⟨1416077, by rfl⟩ : syracuseStep 1888103 = 2832155) B2832155
theorem B2512475 : Blo 1116628 2512475 := bstep (se 1 (by rfl) ⟨1884356, by rfl⟩ : syracuseStep 2512475 = 3768713) B3768713
theorem B6448783 : Blo 1116628 6448783 := bstep (se 1 (by rfl) ⟨4836587, by rfl⟩ : syracuseStep 6448783 = 9673175) B9673175
theorem B7171355 : Blo 1116628 7171355 := bstep (se 1 (by rfl) ⟨5378516, by rfl⟩ : syracuseStep 7171355 = 10757033) B10757033
theorem B2520377 : Blo 1116628 2520377 := bstep (se 2 (by rfl) ⟨945141, by rfl⟩ : syracuseStep 2520377 = 1890283) B1890283
theorem B5372153 : Blo 1116628 5372153 := bstep (se 2 (by rfl) ⟨2014557, by rfl⟩ : syracuseStep 5372153 = 4029115) B4029115
theorem B5668217 : Blo 1116628 5668217 := bstep (se 2 (by rfl) ⟨2125581, by rfl⟩ : syracuseStep 5668217 = 4251163) B4251163
theorem B5668379 : Blo 1116628 5668379 := bstep (se 1 (by rfl) ⟨4251284, by rfl⟩ : syracuseStep 5668379 = 8502569) B8502569
theorem B3768767 : Blo 1116628 3768767 := bstep (se 1 (by rfl) ⟨2826575, by rfl⟩ : syracuseStep 3768767 = 5653151) B5653151
theorem B3770441 : Blo 1116628 3770441 := bstep (se 2 (by rfl) ⟨1413915, by rfl⟩ : syracuseStep 3770441 = 2827831) B2827831
theorem B1117887 : Blo 1116628 1117887 := bstep (se 1 (by rfl) ⟨838415, by rfl⟩ : syracuseStep 1117887 = 1676831) B1676831
theorem B1674983 : Blo 1116628 1674983 := bstep (se 1 (by rfl) ⟨1256237, by rfl⟩ : syracuseStep 1674983 = 2512475) B2512475
theorem B1120463 : Blo 1116628 1120463 := bstep (se 1 (by rfl) ⟨840347, by rfl⟩ : syracuseStep 1120463 = 1680695) B1680695
theorem B51585659 : Blo 1116628 51585659 := bstep (se 1 (by rfl) ⟨38689244, by rfl⟩ : syracuseStep 51585659 = 77378489) B77378489
theorem B1680251 : Blo 1116628 1680251 := bstep (se 1 (by rfl) ⟨1260188, by rfl⟩ : syracuseStep 1680251 = 2520377) B2520377
theorem B3581435 : Blo 1116628 3581435 := bstep (se 1 (by rfl) ⟨2686076, by rfl⟩ : syracuseStep 3581435 = 5372153) B5372153
theorem B3778811 : Blo 1116628 3778811 := bstep (se 1 (by rfl) ⟨2834108, by rfl⟩ : syracuseStep 3778811 = 5668217) B5668217
theorem B3778919 : Blo 1116628 3778919 := bstep (se 1 (by rfl) ⟨2834189, by rfl⟩ : syracuseStep 3778919 = 5668379) B5668379
theorem B8598377 : Blo 1116628 8598377 := bstep (se 2 (by rfl) ⟨3224391, by rfl⟩ : syracuseStep 8598377 = 6448783) B6448783
theorem B1258735 : Blo 1116628 1258735 := bstep (se 1 (by rfl) ⟨944051, by rfl⟩ : syracuseStep 1258735 = 1888103) B1888103
theorem B43568255 : Blo 1116628 43568255 := bstep (se 1 (by rfl) ⟨32676191, by rfl⟩ : syracuseStep 43568255 = 65352383) B65352383
theorem B4247549 : Blo 1116628 4247549 := bstep (se 3 (by rfl) ⟨796415, by rfl⟩ : syracuseStep 4247549 = 1592831) B1592831
theorem B6378911 : Blo 1116628 6378911 := bstep (se 1 (by rfl) ⟨4784183, by rfl⟩ : syracuseStep 6378911 = 9568367) B9568367
theorem B6379343 : Blo 1116628 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B2514239 : Blo 1116628 2514239 := bstep (se 1 (by rfl) ⟨1885679, by rfl⟩ : syracuseStep 2514239 = 3771359) B3771359
theorem B10345967 : Blo 1116628 10345967 := bstep (se 1 (by rfl) ⟨7759475, by rfl⟩ : syracuseStep 10345967 = 15518951) B15518951
theorem B2515391 : Blo 1116628 2515391 := bstep (se 1 (by rfl) ⟨1886543, by rfl⟩ : syracuseStep 2515391 = 3773087) B3773087
theorem B2516075 : Blo 1116628 2516075 := bstep (se 1 (by rfl) ⟨1887056, by rfl⟩ : syracuseStep 2516075 = 3774113) B3774113
theorem B2516327 : Blo 1116628 2516327 := bstep (se 1 (by rfl) ⟨1887245, by rfl⟩ : syracuseStep 2516327 = 3774491) B3774491
theorem B2385463 : Blo 1116628 2385463 := bstep (se 1 (by rfl) ⟨1789097, by rfl⟩ : syracuseStep 2385463 = 3578195) B3578195
theorem B4780903 : Blo 1116628 4780903 := bstep (se 1 (by rfl) ⟨3585677, by rfl⟩ : syracuseStep 4780903 = 7171355) B7171355
theorem B12745835 : Blo 1116628 12745835 := bstep (se 1 (by rfl) ⟨9559376, by rfl⟩ : syracuseStep 12745835 = 19118753) B19118753
theorem B3180617 : Blo 1116628 3180617 := bstep (se 2 (by rfl) ⟨1192731, by rfl⟩ : syracuseStep 3180617 = 2385463) B2385463
theorem B1116655 : Blo 1116628 1116655 := bstep (se 1 (by rfl) ⟨837491, by rfl⟩ : syracuseStep 1116655 = 1674983) B1674983
theorem B1676159 : Blo 1116628 1676159 := bstep (se 1 (by rfl) ⟨1257119, by rfl⟩ : syracuseStep 1676159 = 2514239) B2514239
theorem B1676927 : Blo 1116628 1676927 := bstep (se 1 (by rfl) ⟨1257695, by rfl⟩ : syracuseStep 1676927 = 2515391) B2515391
theorem B1120167 : Blo 1116628 1120167 := bstep (se 1 (by rfl) ⟨840125, by rfl⟩ : syracuseStep 1120167 = 1680251) B1680251
theorem B1677383 : Blo 1116628 1677383 := bstep (se 1 (by rfl) ⟨1258037, by rfl⟩ : syracuseStep 1677383 = 2516075) B2516075
theorem B1677551 : Blo 1116628 1677551 := bstep (se 1 (by rfl) ⟨1258163, by rfl⟩ : syracuseStep 1677551 = 2516327) B2516327
theorem B1678313 : Blo 1116628 1678313 := bstep (se 2 (by rfl) ⟨629367, by rfl⟩ : syracuseStep 1678313 = 1258735) B1258735
theorem B8497223 : Blo 1116628 8497223 := bstep (se 1 (by rfl) ⟨6372917, by rfl⟩ : syracuseStep 8497223 = 12745835) B12745835
theorem B29045503 : Blo 1116628 29045503 := bstep (se 1 (by rfl) ⟨21784127, by rfl⟩ : syracuseStep 29045503 = 43568255) B43568255
theorem B2831699 : Blo 1116628 2831699 := bstep (se 1 (by rfl) ⟨2123774, by rfl⟩ : syracuseStep 2831699 = 4247549) B4247549
theorem B9550493 : Blo 1116628 9550493 := bstep (se 3 (by rfl) ⟨1790717, by rfl⟩ : syracuseStep 9550493 = 3581435) B3581435
theorem B6897311 : Blo 1116628 6897311 := bstep (se 1 (by rfl) ⟨5172983, by rfl⟩ : syracuseStep 6897311 = 10345967) B10345967
theorem B34390439 : Blo 1116628 34390439 := bstep (se 1 (by rfl) ⟨25792829, by rfl⟩ : syracuseStep 34390439 = 51585659) B51585659
theorem B6374537 : Blo 1116628 6374537 := bstep (se 2 (by rfl) ⟨2390451, by rfl⟩ : syracuseStep 6374537 = 4780903) B4780903
theorem B2512511 : Blo 1116628 2512511 := bstep (se 1 (by rfl) ⟨1884383, by rfl⟩ : syracuseStep 2512511 = 3768767) B3768767
theorem B2513627 : Blo 1116628 2513627 := bstep (se 1 (by rfl) ⟨1885220, by rfl⟩ : syracuseStep 2513627 = 3770441) B3770441
theorem B4252607 : Blo 1116628 4252607 := bstep (se 1 (by rfl) ⟨3189455, by rfl⟩ : syracuseStep 4252607 = 6378911) B6378911
theorem B4252895 : Blo 1116628 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B2519207 : Blo 1116628 2519207 := bstep (se 1 (by rfl) ⟨1889405, by rfl⟩ : syracuseStep 2519207 = 3778811) B3778811
theorem B2519279 : Blo 1116628 2519279 := bstep (se 1 (by rfl) ⟨1889459, by rfl⟩ : syracuseStep 2519279 = 3778919) B3778919
theorem B5732251 : Blo 1116628 5732251 := bstep (se 1 (by rfl) ⟨4299188, by rfl⟩ : syracuseStep 5732251 = 8598377) B8598377
theorem B1117439 : Blo 1116628 1117439 := bstep (se 1 (by rfl) ⟨838079, by rfl⟩ : syracuseStep 1117439 = 1676159) B1676159
theorem B1675007 : Blo 1116628 1675007 := bstep (se 1 (by rfl) ⟨1256255, by rfl⟩ : syracuseStep 1675007 = 2512511) B2512511
theorem B1117951 : Blo 1116628 1117951 := bstep (se 1 (by rfl) ⟨838463, by rfl⟩ : syracuseStep 1117951 = 1676927) B1676927
theorem B1118255 : Blo 1116628 1118255 := bstep (se 1 (by rfl) ⟨838691, by rfl⟩ : syracuseStep 1118255 = 1677383) B1677383
theorem B1118367 : Blo 1116628 1118367 := bstep (se 1 (by rfl) ⟨838775, by rfl⟩ : syracuseStep 1118367 = 1677551) B1677551
theorem B1675751 : Blo 1116628 1675751 := bstep (se 1 (by rfl) ⟨1256813, by rfl⟩ : syracuseStep 1675751 = 2513627) B2513627
theorem B1118875 : Blo 1116628 1118875 := bstep (se 1 (by rfl) ⟨839156, by rfl⟩ : syracuseStep 1118875 = 1678313) B1678313
theorem B1679471 : Blo 1116628 1679471 := bstep (se 1 (by rfl) ⟨1259603, by rfl⟩ : syracuseStep 1679471 = 2519207) B2519207
theorem B1679519 : Blo 1116628 1679519 := bstep (se 1 (by rfl) ⟨1259639, by rfl⟩ : syracuseStep 1679519 = 2519279) B2519279
theorem B6366995 : Blo 1116628 6366995 := bstep (se 1 (by rfl) ⟨4775246, by rfl⟩ : syracuseStep 6366995 = 9550493) B9550493
theorem B4598207 : Blo 1116628 4598207 := bstep (se 1 (by rfl) ⟨3448655, by rfl⟩ : syracuseStep 4598207 = 6897311) B6897311
theorem B2835071 : Blo 1116628 2835071 := bstep (se 1 (by rfl) ⟨2126303, by rfl⟩ : syracuseStep 2835071 = 4252607) B4252607
theorem B2835263 : Blo 1116628 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B1887799 : Blo 1116628 1887799 := bstep (se 1 (by rfl) ⟨1415849, by rfl⟩ : syracuseStep 1887799 = 2831699) B2831699
theorem B22926959 : Blo 1116628 22926959 := bstep (se 1 (by rfl) ⟨17195219, by rfl⟩ : syracuseStep 22926959 = 34390439) B34390439
theorem B4249691 : Blo 1116628 4249691 := bstep (se 1 (by rfl) ⟨3187268, by rfl⟩ : syracuseStep 4249691 = 6374537) B6374537
theorem B2120411 : Blo 1116628 2120411 := bstep (se 1 (by rfl) ⟨1590308, by rfl⟩ : syracuseStep 2120411 = 3180617) B3180617
theorem B38727337 : Blo 1116628 38727337 := bstep (se 2 (by rfl) ⟨14522751, by rfl⟩ : syracuseStep 38727337 = 29045503) B29045503
theorem B5664815 : Blo 1116628 5664815 := bstep (se 1 (by rfl) ⟨4248611, by rfl⟩ : syracuseStep 5664815 = 8497223) B8497223
theorem B30572005 : Blo 1116628 30572005 := bstep (se 4 (by rfl) ⟨2866125, by rfl⟩ : syracuseStep 30572005 = 5732251) B5732251
theorem B1116671 : Blo 1116628 1116671 := bstep (se 1 (by rfl) ⟨837503, by rfl⟩ : syracuseStep 1116671 = 1675007) B1675007
theorem B1117167 : Blo 1116628 1117167 := bstep (se 1 (by rfl) ⟨837875, by rfl⟩ : syracuseStep 1117167 = 1675751) B1675751
theorem B1413607 : Blo 1116628 1413607 := bstep (se 1 (by rfl) ⟨1060205, by rfl⟩ : syracuseStep 1413607 = 2120411) B2120411
theorem B1119647 : Blo 1116628 1119647 := bstep (se 1 (by rfl) ⟨839735, by rfl⟩ : syracuseStep 1119647 = 1679471) B1679471
theorem B1119679 : Blo 1116628 1119679 := bstep (se 1 (by rfl) ⟨839759, by rfl⟩ : syracuseStep 1119679 = 1679519) B1679519
theorem B3776543 : Blo 1116628 3776543 := bstep (se 1 (by rfl) ⟨2832407, by rfl⟩ : syracuseStep 3776543 = 5664815) B5664815
theorem B15284639 : Blo 1116628 15284639 := bstep (se 1 (by rfl) ⟨11463479, by rfl⟩ : syracuseStep 15284639 = 22926959) B22926959
theorem B2833127 : Blo 1116628 2833127 := bstep (se 1 (by rfl) ⟨2124845, by rfl⟩ : syracuseStep 2833127 = 4249691) B4249691
theorem B4244663 : Blo 1116628 4244663 := bstep (se 1 (by rfl) ⟨3183497, by rfl⟩ : syracuseStep 4244663 = 6366995) B6366995
theorem B3065471 : Blo 1116628 3065471 := bstep (se 1 (by rfl) ⟨2299103, by rfl⟩ : syracuseStep 3065471 = 4598207) B4598207
theorem B1890047 : Blo 1116628 1890047 := bstep (se 1 (by rfl) ⟨1417535, by rfl⟩ : syracuseStep 1890047 = 2835071) B2835071
theorem B1890175 : Blo 1116628 1890175 := bstep (se 1 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 1890175 = 2835263) B2835263
theorem B2517065 : Blo 1116628 2517065 := bstep (se 2 (by rfl) ⟨943899, by rfl⟩ : syracuseStep 2517065 = 1887799) B1887799
theorem B51636449 : Blo 1116628 51636449 := bstep (se 2 (by rfl) ⟨19363668, by rfl⟩ : syracuseStep 51636449 = 38727337) B38727337
theorem B40762673 : Blo 1116628 40762673 := bstep (se 2 (by rfl) ⟨15286002, by rfl⟩ : syracuseStep 40762673 = 30572005) B30572005
theorem B1678043 : Blo 1116628 1678043 := bstep (se 1 (by rfl) ⟨1258532, by rfl⟩ : syracuseStep 1678043 = 2517065) B2517065
theorem B27175115 : Blo 1116628 27175115 := bstep (se 1 (by rfl) ⟨20381336, by rfl⟩ : syracuseStep 27175115 = 40762673) B40762673
theorem B2829775 : Blo 1116628 2829775 := bstep (se 1 (by rfl) ⟨2122331, by rfl⟩ : syracuseStep 2829775 = 4244663) B4244663
theorem B2043647 : Blo 1116628 2043647 := bstep (se 1 (by rfl) ⟨1532735, by rfl⟩ : syracuseStep 2043647 = 3065471) B3065471
theorem B1260031 : Blo 1116628 1260031 := bstep (se 1 (by rfl) ⟨945023, by rfl⟩ : syracuseStep 1260031 = 1890047) B1890047
theorem B1884809 : Blo 1116628 1884809 := bstep (se 2 (by rfl) ⟨706803, by rfl⟩ : syracuseStep 1884809 = 1413607) B1413607
theorem B34424299 : Blo 1116628 34424299 := bstep (se 1 (by rfl) ⟨25818224, by rfl⟩ : syracuseStep 34424299 = 51636449) B51636449
theorem B1888751 : Blo 1116628 1888751 := bstep (se 1 (by rfl) ⟨1416563, by rfl⟩ : syracuseStep 1888751 = 2833127) B2833127
theorem B2517695 : Blo 1116628 2517695 := bstep (se 1 (by rfl) ⟨1888271, by rfl⟩ : syracuseStep 2517695 = 3776543) B3776543
theorem B40759037 : Blo 1116628 40759037 := bstep (se 3 (by rfl) ⟨7642319, by rfl⟩ : syracuseStep 40759037 = 15284639) B15284639
theorem B2520233 : Blo 1116628 2520233 := bstep (se 2 (by rfl) ⟨945087, by rfl⟩ : syracuseStep 2520233 = 1890175) B1890175
theorem B1118695 : Blo 1116628 1118695 := bstep (se 1 (by rfl) ⟨839021, by rfl⟩ : syracuseStep 1118695 = 1678043) B1678043
theorem B3773033 : Blo 1116628 3773033 := bstep (se 2 (by rfl) ⟨1414887, by rfl⟩ : syracuseStep 3773033 = 2829775) B2829775
theorem B1678463 : Blo 1116628 1678463 := bstep (se 1 (by rfl) ⟨1258847, by rfl⟩ : syracuseStep 1678463 = 2517695) B2517695
theorem B27172691 : Blo 1116628 27172691 := bstep (se 1 (by rfl) ⟨20379518, by rfl⟩ : syracuseStep 27172691 = 40759037) B40759037
theorem B1680041 : Blo 1116628 1680041 := bstep (se 2 (by rfl) ⟨630015, by rfl⟩ : syracuseStep 1680041 = 1260031) B1260031
theorem B1680155 : Blo 1116628 1680155 := bstep (se 1 (by rfl) ⟨1260116, by rfl⟩ : syracuseStep 1680155 = 2520233) B2520233
theorem B1256539 : Blo 1116628 1256539 := bstep (se 1 (by rfl) ⟨942404, by rfl⟩ : syracuseStep 1256539 = 1884809) B1884809
theorem B1259167 : Blo 1116628 1259167 := bstep (se 1 (by rfl) ⟨944375, by rfl⟩ : syracuseStep 1259167 = 1888751) B1888751
theorem B1362431 : Blo 1116628 1362431 := bstep (se 1 (by rfl) ⟨1021823, by rfl⟩ : syracuseStep 1362431 = 2043647) B2043647
theorem B45899065 : Blo 1116628 45899065 := bstep (se 2 (by rfl) ⟨17212149, by rfl⟩ : syracuseStep 45899065 = 34424299) B34424299
theorem B18116743 : Blo 1116628 18116743 := bstep (se 1 (by rfl) ⟨13587557, by rfl⟩ : syracuseStep 18116743 = 27175115) B27175115
theorem B1675385 : Blo 1116628 1675385 := bstep (se 2 (by rfl) ⟨628269, by rfl⟩ : syracuseStep 1675385 = 1256539) B1256539
theorem B1118975 : Blo 1116628 1118975 := bstep (se 1 (by rfl) ⟨839231, by rfl⟩ : syracuseStep 1118975 = 1678463) B1678463
theorem B24155657 : Blo 1116628 24155657 := bstep (se 2 (by rfl) ⟨9058371, by rfl⟩ : syracuseStep 24155657 = 18116743) B18116743
theorem B1120027 : Blo 1116628 1120027 := bstep (se 1 (by rfl) ⟨840020, by rfl⟩ : syracuseStep 1120027 = 1680041) B1680041
theorem B1120103 : Blo 1116628 1120103 := bstep (se 1 (by rfl) ⟨840077, by rfl⟩ : syracuseStep 1120103 = 1680155) B1680155
theorem B1678889 : Blo 1116628 1678889 := bstep (se 2 (by rfl) ⟨629583, by rfl⟩ : syracuseStep 1678889 = 1259167) B1259167
theorem B61198753 : Blo 1116628 61198753 := bstep (se 2 (by rfl) ⟨22949532, by rfl⟩ : syracuseStep 61198753 = 45899065) B45899065
theorem B2515355 : Blo 1116628 2515355 := bstep (se 1 (by rfl) ⟨1886516, by rfl⟩ : syracuseStep 2515355 = 3773033) B3773033
theorem B18115127 : Blo 1116628 18115127 := bstep (se 1 (by rfl) ⟨13586345, by rfl⟩ : syracuseStep 18115127 = 27172691) B27172691
theorem B3633149 : Blo 1116628 3633149 := bstep (se 3 (by rfl) ⟨681215, by rfl⟩ : syracuseStep 3633149 = 1362431) B1362431
theorem B1116923 : Blo 1116628 1116923 := bstep (se 1 (by rfl) ⟨837692, by rfl⟩ : syracuseStep 1116923 = 1675385) B1675385
theorem B1119259 : Blo 1116628 1119259 := bstep (se 1 (by rfl) ⟨839444, by rfl⟩ : syracuseStep 1119259 = 1678889) B1678889
theorem B1676903 : Blo 1116628 1676903 := bstep (se 1 (by rfl) ⟨1257677, by rfl⟩ : syracuseStep 1676903 = 2515355) B2515355
theorem B81598337 : Blo 1116628 81598337 := bstep (se 2 (by rfl) ⟨30599376, by rfl⟩ : syracuseStep 81598337 = 61198753) B61198753
theorem B16103771 : Blo 1116628 16103771 := bstep (se 1 (by rfl) ⟨12077828, by rfl⟩ : syracuseStep 16103771 = 24155657) B24155657
theorem B12076751 : Blo 1116628 12076751 := bstep (se 1 (by rfl) ⟨9057563, by rfl⟩ : syracuseStep 12076751 = 18115127) B18115127
theorem B2422099 : Blo 1116628 2422099 := bstep (se 1 (by rfl) ⟨1816574, by rfl⟩ : syracuseStep 2422099 = 3633149) B3633149
theorem B1117935 : Blo 1116628 1117935 := bstep (se 1 (by rfl) ⟨838451, by rfl⟩ : syracuseStep 1117935 = 1676903) B1676903
theorem B54398891 : Blo 1116628 54398891 := bstep (se 1 (by rfl) ⟨40799168, by rfl⟩ : syracuseStep 54398891 = 81598337) B81598337
theorem B3229465 : Blo 1116628 3229465 := bstep (se 2 (by rfl) ⟨1211049, by rfl⟩ : syracuseStep 3229465 = 2422099) B2422099
theorem B10735847 : Blo 1116628 10735847 := bstep (se 1 (by rfl) ⟨8051885, by rfl⟩ : syracuseStep 10735847 = 16103771) B16103771
theorem B8051167 : Blo 1116628 8051167 := bstep (se 1 (by rfl) ⟨6038375, by rfl⟩ : syracuseStep 8051167 = 12076751) B12076751
theorem B4305953 : Blo 1116628 4305953 := bstep (se 2 (by rfl) ⟨1614732, by rfl⟩ : syracuseStep 4305953 = 3229465) B3229465
theorem B7157231 : Blo 1116628 7157231 := bstep (se 1 (by rfl) ⟨5367923, by rfl⟩ : syracuseStep 7157231 = 10735847) B10735847
theorem B10734889 : Blo 1116628 10734889 := bstep (se 2 (by rfl) ⟨4025583, by rfl⟩ : syracuseStep 10734889 = 8051167) B8051167
theorem B36265927 : Blo 1116628 36265927 := bstep (se 1 (by rfl) ⟨27199445, by rfl⟩ : syracuseStep 36265927 = 54398891) B54398891
theorem B2870635 : Blo 1116628 2870635 := bstep (se 1 (by rfl) ⟨2152976, by rfl⟩ : syracuseStep 2870635 = 4305953) B4305953
theorem B4771487 : Blo 1116628 4771487 := bstep (se 1 (by rfl) ⟨3578615, by rfl⟩ : syracuseStep 4771487 = 7157231) B7157231
theorem B48354569 : Blo 1116628 48354569 := bstep (se 2 (by rfl) ⟨18132963, by rfl⟩ : syracuseStep 48354569 = 36265927) B36265927
theorem B14313185 : Blo 1116628 14313185 := bstep (se 2 (by rfl) ⟨5367444, by rfl⟩ : syracuseStep 14313185 = 10734889) B10734889
theorem B9542123 : Blo 1116628 9542123 := bstep (se 1 (by rfl) ⟨7156592, by rfl⟩ : syracuseStep 9542123 = 14313185) B14313185
theorem B12723965 : Blo 1116628 12723965 := bstep (se 3 (by rfl) ⟨2385743, by rfl⟩ : syracuseStep 12723965 = 4771487) B4771487
theorem B32236379 : Blo 1116628 32236379 := bstep (se 1 (by rfl) ⟨24177284, by rfl⟩ : syracuseStep 32236379 = 48354569) B48354569
theorem B3827513 : Blo 1116628 3827513 := bstep (se 2 (by rfl) ⟨1435317, by rfl⟩ : syracuseStep 3827513 = 2870635) B2870635
theorem B6361415 : Blo 1116628 6361415 := bstep (se 1 (by rfl) ⟨4771061, by rfl⟩ : syracuseStep 6361415 = 9542123) B9542123
theorem B21490919 : Blo 1116628 21490919 := bstep (se 1 (by rfl) ⟨16118189, by rfl⟩ : syracuseStep 21490919 = 32236379) B32236379
theorem B8482643 : Blo 1116628 8482643 := bstep (se 1 (by rfl) ⟨6361982, by rfl⟩ : syracuseStep 8482643 = 12723965) B12723965
theorem B2551675 : Blo 1116628 2551675 := bstep (se 1 (by rfl) ⟨1913756, by rfl⟩ : syracuseStep 2551675 = 3827513) B3827513
theorem B14327279 : Blo 1116628 14327279 := bstep (se 1 (by rfl) ⟨10745459, by rfl⟩ : syracuseStep 14327279 = 21490919) B21490919
theorem B4240943 : Blo 1116628 4240943 := bstep (se 1 (by rfl) ⟨3180707, by rfl⟩ : syracuseStep 4240943 = 6361415) B6361415
theorem B5655095 : Blo 1116628 5655095 := bstep (se 1 (by rfl) ⟨4241321, by rfl⟩ : syracuseStep 5655095 = 8482643) B8482643
theorem B3402233 : Blo 1116628 3402233 := bstep (se 2 (by rfl) ⟨1275837, by rfl⟩ : syracuseStep 3402233 = 2551675) B2551675
theorem B3770063 : Blo 1116628 3770063 := bstep (se 1 (by rfl) ⟨2827547, by rfl⟩ : syracuseStep 3770063 = 5655095) B5655095
theorem B2268155 : Blo 1116628 2268155 := bstep (se 1 (by rfl) ⟨1701116, by rfl⟩ : syracuseStep 2268155 = 3402233) B3402233
theorem B2827295 : Blo 1116628 2827295 := bstep (se 1 (by rfl) ⟨2120471, by rfl⟩ : syracuseStep 2827295 = 4240943) B4240943
theorem B9551519 : Blo 1116628 9551519 := bstep (se 1 (by rfl) ⟨7163639, by rfl⟩ : syracuseStep 9551519 = 14327279) B14327279
theorem B1512103 : Blo 1116628 1512103 := bstep (se 1 (by rfl) ⟨1134077, by rfl⟩ : syracuseStep 1512103 = 2268155) B2268155
theorem B6367679 : Blo 1116628 6367679 := bstep (se 1 (by rfl) ⟨4775759, by rfl⟩ : syracuseStep 6367679 = 9551519) B9551519
theorem B1884863 : Blo 1116628 1884863 := bstep (se 1 (by rfl) ⟨1413647, by rfl⟩ : syracuseStep 1884863 = 2827295) B2827295
theorem B2513375 : Blo 1116628 2513375 := bstep (se 1 (by rfl) ⟨1885031, by rfl⟩ : syracuseStep 2513375 = 3770063) B3770063
theorem B1675583 : Blo 1116628 1675583 := bstep (se 1 (by rfl) ⟨1256687, by rfl⟩ : syracuseStep 1675583 = 2513375) B2513375
theorem B1256575 : Blo 1116628 1256575 := bstep (se 1 (by rfl) ⟨942431, by rfl⟩ : syracuseStep 1256575 = 1884863) B1884863
theorem B2016137 : Blo 1116628 2016137 := bstep (se 2 (by rfl) ⟨756051, by rfl⟩ : syracuseStep 2016137 = 1512103) B1512103
theorem B4245119 : Blo 1116628 4245119 := bstep (se 1 (by rfl) ⟨3183839, by rfl⟩ : syracuseStep 4245119 = 6367679) B6367679
theorem B5376365 : Blo 1116628 5376365 := bstep (se 3 (by rfl) ⟨1008068, by rfl⟩ : syracuseStep 5376365 = 2016137) B2016137
theorem B1117055 : Blo 1116628 1117055 := bstep (se 1 (by rfl) ⟨837791, by rfl⟩ : syracuseStep 1117055 = 1675583) B1675583
theorem B1675433 : Blo 1116628 1675433 := bstep (se 2 (by rfl) ⟨628287, by rfl⟩ : syracuseStep 1675433 = 1256575) B1256575
theorem B2830079 : Blo 1116628 2830079 := bstep (se 1 (by rfl) ⟨2122559, by rfl⟩ : syracuseStep 2830079 = 4245119) B4245119
theorem B1116955 : Blo 1116628 1116955 := bstep (se 1 (by rfl) ⟨837716, by rfl⟩ : syracuseStep 1116955 = 1675433) B1675433
theorem B3584243 : Blo 1116628 3584243 := bstep (se 1 (by rfl) ⟨2688182, by rfl⟩ : syracuseStep 3584243 = 5376365) B5376365
theorem B1886719 : Blo 1116628 1886719 := bstep (se 1 (by rfl) ⟨1415039, by rfl⟩ : syracuseStep 1886719 = 2830079) B2830079
theorem B2515625 : Blo 1116628 2515625 := bstep (se 2 (by rfl) ⟨943359, by rfl⟩ : syracuseStep 2515625 = 1886719) B1886719
theorem B2389495 : Blo 1116628 2389495 := bstep (se 1 (by rfl) ⟨1792121, by rfl⟩ : syracuseStep 2389495 = 3584243) B3584243
theorem B1677083 : Blo 1116628 1677083 := bstep (se 1 (by rfl) ⟨1257812, by rfl⟩ : syracuseStep 1677083 = 2515625) B2515625
theorem B3185993 : Blo 1116628 3185993 := bstep (se 2 (by rfl) ⟨1194747, by rfl⟩ : syracuseStep 3185993 = 2389495) B2389495
theorem B1118055 : Blo 1116628 1118055 := bstep (se 1 (by rfl) ⟨838541, by rfl⟩ : syracuseStep 1118055 = 1677083) B1677083
theorem B2123995 : Blo 1116628 2123995 := bstep (se 1 (by rfl) ⟨1592996, by rfl⟩ : syracuseStep 2123995 = 3185993) B3185993
theorem B2831993 : Blo 1116628 2831993 := bstep (se 2 (by rfl) ⟨1061997, by rfl⟩ : syracuseStep 2831993 = 2123995) B2123995
theorem B1887995 : Blo 1116628 1887995 := bstep (se 1 (by rfl) ⟨1415996, by rfl⟩ : syracuseStep 1887995 = 2831993) B2831993
theorem B1258663 : Blo 1116628 1258663 := bstep (se 1 (by rfl) ⟨943997, by rfl⟩ : syracuseStep 1258663 = 1887995) B1887995
theorem B1678217 : Blo 1116628 1678217 := bstep (se 2 (by rfl) ⟨629331, by rfl⟩ : syracuseStep 1678217 = 1258663) B1258663
theorem B1118811 : Blo 1116628 1118811 := bstep (se 1 (by rfl) ⟨839108, by rfl⟩ : syracuseStep 1118811 = 1678217) B1678217

theorem C0 (j : ℕ) (h1 : 279157 ≤ j) (h2 : j ≤ 279856) : Blo 1116628 (4 * j + 3) := by
  interval_cases j
  · exact B1116631
  · exact B1116635
  · exact B1116639
  · exact B1116643
  · exact B1116647
  · exact B1116651
  · exact B1116655
  · exact B1116659
  · exact B1116663
  · exact B1116667
  · exact B1116671
  · exact B1116675
  · exact B1116679
  · exact B1116683
  · exact B1116687
  · exact B1116691
  · exact B1116695
  · exact B1116699
  · exact B1116703
  · exact B1116707
  · exact B1116711
  · exact B1116715
  · exact B1116719
  · exact B1116723
  · exact B1116727
  · exact B1116731
  · exact B1116735
  · exact B1116739
  · exact B1116743
  · exact B1116747
  · exact B1116751
  · exact B1116755
  · exact B1116759
  · exact B1116763
  · exact B1116767
  · exact B1116771
  · exact B1116775
  · exact B1116779
  · exact B1116783
  · exact B1116787
  · exact B1116791
  · exact B1116795
  · exact B1116799
  · exact B1116803
  · exact B1116807
  · exact B1116811
  · exact B1116815
  · exact B1116819
  · exact B1116823
  · exact B1116827
  · exact B1116831
  · exact B1116835
  · exact B1116839
  · exact B1116843
  · exact B1116847
  · exact B1116851
  · exact B1116855
  · exact B1116859
  · exact B1116863
  · exact B1116867
  · exact B1116871
  · exact B1116875
  · exact B1116879
  · exact B1116883
  · exact B1116887
  · exact B1116891
  · exact B1116895
  · exact B1116899
  · exact B1116903
  · exact B1116907
  · exact B1116911
  · exact B1116915
  · exact B1116919
  · exact B1116923
  · exact B1116927
  · exact B1116931
  · exact B1116935
  · exact B1116939
  · exact B1116943
  · exact B1116947
  · exact B1116951
  · exact B1116955
  · exact B1116959
  · exact B1116963
  · exact B1116967
  · exact B1116971
  · exact B1116975
  · exact B1116979
  · exact B1116983
  · exact B1116987
  · exact B1116991
  · exact B1116995
  · exact B1116999
  · exact B1117003
  · exact B1117007
  · exact B1117011
  · exact B1117015
  · exact B1117019
  · exact B1117023
  · exact B1117027
  · exact B1117031
  · exact B1117035
  · exact B1117039
  · exact B1117043
  · exact B1117047
  · exact B1117051
  · exact B1117055
  · exact B1117059
  · exact B1117063
  · exact B1117067
  · exact B1117071
  · exact B1117075
  · exact B1117079
  · exact B1117083
  · exact B1117087
  · exact B1117091
  · exact B1117095
  · exact B1117099
  · exact B1117103
  · exact B1117107
  · exact B1117111
  · exact B1117115
  · exact B1117119
  · exact B1117123
  · exact B1117127
  · exact B1117131
  · exact B1117135
  · exact B1117139
  · exact B1117143
  · exact B1117147
  · exact B1117151
  · exact B1117155
  · exact B1117159
  · exact B1117163
  · exact B1117167
  · exact B1117171
  · exact B1117175
  · exact B1117179
  · exact B1117183
  · exact B1117187
  · exact B1117191
  · exact B1117195
  · exact B1117199
  · exact B1117203
  · exact B1117207
  · exact B1117211
  · exact B1117215
  · exact B1117219
  · exact B1117223
  · exact B1117227
  · exact B1117231
  · exact B1117235
  · exact B1117239
  · exact B1117243
  · exact B1117247
  · exact B1117251
  · exact B1117255
  · exact B1117259
  · exact B1117263
  · exact B1117267
  · exact B1117271
  · exact B1117275
  · exact B1117279
  · exact B1117283
  · exact B1117287
  · exact B1117291
  · exact B1117295
  · exact B1117299
  · exact B1117303
  · exact B1117307
  · exact B1117311
  · exact B1117315
  · exact B1117319
  · exact B1117323
  · exact B1117327
  · exact B1117331
  · exact B1117335
  · exact B1117339
  · exact B1117343
  · exact B1117347
  · exact B1117351
  · exact B1117355
  · exact B1117359
  · exact B1117363
  · exact B1117367
  · exact B1117371
  · exact B1117375
  · exact B1117379
  · exact B1117383
  · exact B1117387
  · exact B1117391
  · exact B1117395
  · exact B1117399
  · exact B1117403
  · exact B1117407
  · exact B1117411
  · exact B1117415
  · exact B1117419
  · exact B1117423
  · exact B1117427
  · exact B1117431
  · exact B1117435
  · exact B1117439
  · exact B1117443
  · exact B1117447
  · exact B1117451
  · exact B1117455
  · exact B1117459
  · exact B1117463
  · exact B1117467
  · exact B1117471
  · exact B1117475
  · exact B1117479
  · exact B1117483
  · exact B1117487
  · exact B1117491
  · exact B1117495
  · exact B1117499
  · exact B1117503
  · exact B1117507
  · exact B1117511
  · exact B1117515
  · exact B1117519
  · exact B1117523
  · exact B1117527
  · exact B1117531
  · exact B1117535
  · exact B1117539
  · exact B1117543
  · exact B1117547
  · exact B1117551
  · exact B1117555
  · exact B1117559
  · exact B1117563
  · exact B1117567
  · exact B1117571
  · exact B1117575
  · exact B1117579
  · exact B1117583
  · exact B1117587
  · exact B1117591
  · exact B1117595
  · exact B1117599
  · exact B1117603
  · exact B1117607
  · exact B1117611
  · exact B1117615
  · exact B1117619
  · exact B1117623
  · exact B1117627
  · exact B1117631
  · exact B1117635
  · exact B1117639
  · exact B1117643
  · exact B1117647
  · exact B1117651
  · exact B1117655
  · exact B1117659
  · exact B1117663
  · exact B1117667
  · exact B1117671
  · exact B1117675
  · exact B1117679
  · exact B1117683
  · exact B1117687
  · exact B1117691
  · exact B1117695
  · exact B1117699
  · exact B1117703
  · exact B1117707
  · exact B1117711
  · exact B1117715
  · exact B1117719
  · exact B1117723
  · exact B1117727
  · exact B1117731
  · exact B1117735
  · exact B1117739
  · exact B1117743
  · exact B1117747
  · exact B1117751
  · exact B1117755
  · exact B1117759
  · exact B1117763
  · exact B1117767
  · exact B1117771
  · exact B1117775
  · exact B1117779
  · exact B1117783
  · exact B1117787
  · exact B1117791
  · exact B1117795
  · exact B1117799
  · exact B1117803
  · exact B1117807
  · exact B1117811
  · exact B1117815
  · exact B1117819
  · exact B1117823
  · exact B1117827
  · exact B1117831
  · exact B1117835
  · exact B1117839
  · exact B1117843
  · exact B1117847
  · exact B1117851
  · exact B1117855
  · exact B1117859
  · exact B1117863
  · exact B1117867
  · exact B1117871
  · exact B1117875
  · exact B1117879
  · exact B1117883
  · exact B1117887
  · exact B1117891
  · exact B1117895
  · exact B1117899
  · exact B1117903
  · exact B1117907
  · exact B1117911
  · exact B1117915
  · exact B1117919
  · exact B1117923
  · exact B1117927
  · exact B1117931
  · exact B1117935
  · exact B1117939
  · exact B1117943
  · exact B1117947
  · exact B1117951
  · exact B1117955
  · exact B1117959
  · exact B1117963
  · exact B1117967
  · exact B1117971
  · exact B1117975
  · exact B1117979
  · exact B1117983
  · exact B1117987
  · exact B1117991
  · exact B1117995
  · exact B1117999
  · exact B1118003
  · exact B1118007
  · exact B1118011
  · exact B1118015
  · exact B1118019
  · exact B1118023
  · exact B1118027
  · exact B1118031
  · exact B1118035
  · exact B1118039
  · exact B1118043
  · exact B1118047
  · exact B1118051
  · exact B1118055
  · exact B1118059
  · exact B1118063
  · exact B1118067
  · exact B1118071
  · exact B1118075
  · exact B1118079
  · exact B1118083
  · exact B1118087
  · exact B1118091
  · exact B1118095
  · exact B1118099
  · exact B1118103
  · exact B1118107
  · exact B1118111
  · exact B1118115
  · exact B1118119
  · exact B1118123
  · exact B1118127
  · exact B1118131
  · exact B1118135
  · exact B1118139
  · exact B1118143
  · exact B1118147
  · exact B1118151
  · exact B1118155
  · exact B1118159
  · exact B1118163
  · exact B1118167
  · exact B1118171
  · exact B1118175
  · exact B1118179
  · exact B1118183
  · exact B1118187
  · exact B1118191
  · exact B1118195
  · exact B1118199
  · exact B1118203
  · exact B1118207
  · exact B1118211
  · exact B1118215
  · exact B1118219
  · exact B1118223
  · exact B1118227
  · exact B1118231
  · exact B1118235
  · exact B1118239
  · exact B1118243
  · exact B1118247
  · exact B1118251
  · exact B1118255
  · exact B1118259
  · exact B1118263
  · exact B1118267
  · exact B1118271
  · exact B1118275
  · exact B1118279
  · exact B1118283
  · exact B1118287
  · exact B1118291
  · exact B1118295
  · exact B1118299
  · exact B1118303
  · exact B1118307
  · exact B1118311
  · exact B1118315
  · exact B1118319
  · exact B1118323
  · exact B1118327
  · exact B1118331
  · exact B1118335
  · exact B1118339
  · exact B1118343
  · exact B1118347
  · exact B1118351
  · exact B1118355
  · exact B1118359
  · exact B1118363
  · exact B1118367
  · exact B1118371
  · exact B1118375
  · exact B1118379
  · exact B1118383
  · exact B1118387
  · exact B1118391
  · exact B1118395
  · exact B1118399
  · exact B1118403
  · exact B1118407
  · exact B1118411
  · exact B1118415
  · exact B1118419
  · exact B1118423
  · exact B1118427
  · exact B1118431
  · exact B1118435
  · exact B1118439
  · exact B1118443
  · exact B1118447
  · exact B1118451
  · exact B1118455
  · exact B1118459
  · exact B1118463
  · exact B1118467
  · exact B1118471
  · exact B1118475
  · exact B1118479
  · exact B1118483
  · exact B1118487
  · exact B1118491
  · exact B1118495
  · exact B1118499
  · exact B1118503
  · exact B1118507
  · exact B1118511
  · exact B1118515
  · exact B1118519
  · exact B1118523
  · exact B1118527
  · exact B1118531
  · exact B1118535
  · exact B1118539
  · exact B1118543
  · exact B1118547
  · exact B1118551
  · exact B1118555
  · exact B1118559
  · exact B1118563
  · exact B1118567
  · exact B1118571
  · exact B1118575
  · exact B1118579
  · exact B1118583
  · exact B1118587
  · exact B1118591
  · exact B1118595
  · exact B1118599
  · exact B1118603
  · exact B1118607
  · exact B1118611
  · exact B1118615
  · exact B1118619
  · exact B1118623
  · exact B1118627
  · exact B1118631
  · exact B1118635
  · exact B1118639
  · exact B1118643
  · exact B1118647
  · exact B1118651
  · exact B1118655
  · exact B1118659
  · exact B1118663
  · exact B1118667
  · exact B1118671
  · exact B1118675
  · exact B1118679
  · exact B1118683
  · exact B1118687
  · exact B1118691
  · exact B1118695
  · exact B1118699
  · exact B1118703
  · exact B1118707
  · exact B1118711
  · exact B1118715
  · exact B1118719
  · exact B1118723
  · exact B1118727
  · exact B1118731
  · exact B1118735
  · exact B1118739
  · exact B1118743
  · exact B1118747
  · exact B1118751
  · exact B1118755
  · exact B1118759
  · exact B1118763
  · exact B1118767
  · exact B1118771
  · exact B1118775
  · exact B1118779
  · exact B1118783
  · exact B1118787
  · exact B1118791
  · exact B1118795
  · exact B1118799
  · exact B1118803
  · exact B1118807
  · exact B1118811
  · exact B1118815
  · exact B1118819
  · exact B1118823
  · exact B1118827
  · exact B1118831
  · exact B1118835
  · exact B1118839
  · exact B1118843
  · exact B1118847
  · exact B1118851
  · exact B1118855
  · exact B1118859
  · exact B1118863
  · exact B1118867
  · exact B1118871
  · exact B1118875
  · exact B1118879
  · exact B1118883
  · exact B1118887
  · exact B1118891
  · exact B1118895
  · exact B1118899
  · exact B1118903
  · exact B1118907
  · exact B1118911
  · exact B1118915
  · exact B1118919
  · exact B1118923
  · exact B1118927
  · exact B1118931
  · exact B1118935
  · exact B1118939
  · exact B1118943
  · exact B1118947
  · exact B1118951
  · exact B1118955
  · exact B1118959
  · exact B1118963
  · exact B1118967
  · exact B1118971
  · exact B1118975
  · exact B1118979
  · exact B1118983
  · exact B1118987
  · exact B1118991
  · exact B1118995
  · exact B1118999
  · exact B1119003
  · exact B1119007
  · exact B1119011
  · exact B1119015
  · exact B1119019
  · exact B1119023
  · exact B1119027
  · exact B1119031
  · exact B1119035
  · exact B1119039
  · exact B1119043
  · exact B1119047
  · exact B1119051
  · exact B1119055
  · exact B1119059
  · exact B1119063
  · exact B1119067
  · exact B1119071
  · exact B1119075
  · exact B1119079
  · exact B1119083
  · exact B1119087
  · exact B1119091
  · exact B1119095
  · exact B1119099
  · exact B1119103
  · exact B1119107
  · exact B1119111
  · exact B1119115
  · exact B1119119
  · exact B1119123
  · exact B1119127
  · exact B1119131
  · exact B1119135
  · exact B1119139
  · exact B1119143
  · exact B1119147
  · exact B1119151
  · exact B1119155
  · exact B1119159
  · exact B1119163
  · exact B1119167
  · exact B1119171
  · exact B1119175
  · exact B1119179
  · exact B1119183
  · exact B1119187
  · exact B1119191
  · exact B1119195
  · exact B1119199
  · exact B1119203
  · exact B1119207
  · exact B1119211
  · exact B1119215
  · exact B1119219
  · exact B1119223
  · exact B1119227
  · exact B1119231
  · exact B1119235
  · exact B1119239
  · exact B1119243
  · exact B1119247
  · exact B1119251
  · exact B1119255
  · exact B1119259
  · exact B1119263
  · exact B1119267
  · exact B1119271
  · exact B1119275
  · exact B1119279
  · exact B1119283
  · exact B1119287
  · exact B1119291
  · exact B1119295
  · exact B1119299
  · exact B1119303
  · exact B1119307
  · exact B1119311
  · exact B1119315
  · exact B1119319
  · exact B1119323
  · exact B1119327
  · exact B1119331
  · exact B1119335
  · exact B1119339
  · exact B1119343
  · exact B1119347
  · exact B1119351
  · exact B1119355
  · exact B1119359
  · exact B1119363
  · exact B1119367
  · exact B1119371
  · exact B1119375
  · exact B1119379
  · exact B1119383
  · exact B1119387
  · exact B1119391
  · exact B1119395
  · exact B1119399
  · exact B1119403
  · exact B1119407
  · exact B1119411
  · exact B1119415
  · exact B1119419
  · exact B1119423
  · exact B1119427

theorem C1 (j : ℕ) (h1 : 279857 ≤ j) (h2 : j ≤ 280156) : Blo 1116628 (4 * j + 3) := by
  interval_cases j
  · exact B1119431
  · exact B1119435
  · exact B1119439
  · exact B1119443
  · exact B1119447
  · exact B1119451
  · exact B1119455
  · exact B1119459
  · exact B1119463
  · exact B1119467
  · exact B1119471
  · exact B1119475
  · exact B1119479
  · exact B1119483
  · exact B1119487
  · exact B1119491
  · exact B1119495
  · exact B1119499
  · exact B1119503
  · exact B1119507
  · exact B1119511
  · exact B1119515
  · exact B1119519
  · exact B1119523
  · exact B1119527
  · exact B1119531
  · exact B1119535
  · exact B1119539
  · exact B1119543
  · exact B1119547
  · exact B1119551
  · exact B1119555
  · exact B1119559
  · exact B1119563
  · exact B1119567
  · exact B1119571
  · exact B1119575
  · exact B1119579
  · exact B1119583
  · exact B1119587
  · exact B1119591
  · exact B1119595
  · exact B1119599
  · exact B1119603
  · exact B1119607
  · exact B1119611
  · exact B1119615
  · exact B1119619
  · exact B1119623
  · exact B1119627
  · exact B1119631
  · exact B1119635
  · exact B1119639
  · exact B1119643
  · exact B1119647
  · exact B1119651
  · exact B1119655
  · exact B1119659
  · exact B1119663
  · exact B1119667
  · exact B1119671
  · exact B1119675
  · exact B1119679
  · exact B1119683
  · exact B1119687
  · exact B1119691
  · exact B1119695
  · exact B1119699
  · exact B1119703
  · exact B1119707
  · exact B1119711
  · exact B1119715
  · exact B1119719
  · exact B1119723
  · exact B1119727
  · exact B1119731
  · exact B1119735
  · exact B1119739
  · exact B1119743
  · exact B1119747
  · exact B1119751
  · exact B1119755
  · exact B1119759
  · exact B1119763
  · exact B1119767
  · exact B1119771
  · exact B1119775
  · exact B1119779
  · exact B1119783
  · exact B1119787
  · exact B1119791
  · exact B1119795
  · exact B1119799
  · exact B1119803
  · exact B1119807
  · exact B1119811
  · exact B1119815
  · exact B1119819
  · exact B1119823
  · exact B1119827
  · exact B1119831
  · exact B1119835
  · exact B1119839
  · exact B1119843
  · exact B1119847
  · exact B1119851
  · exact B1119855
  · exact B1119859
  · exact B1119863
  · exact B1119867
  · exact B1119871
  · exact B1119875
  · exact B1119879
  · exact B1119883
  · exact B1119887
  · exact B1119891
  · exact B1119895
  · exact B1119899
  · exact B1119903
  · exact B1119907
  · exact B1119911
  · exact B1119915
  · exact B1119919
  · exact B1119923
  · exact B1119927
  · exact B1119931
  · exact B1119935
  · exact B1119939
  · exact B1119943
  · exact B1119947
  · exact B1119951
  · exact B1119955
  · exact B1119959
  · exact B1119963
  · exact B1119967
  · exact B1119971
  · exact B1119975
  · exact B1119979
  · exact B1119983
  · exact B1119987
  · exact B1119991
  · exact B1119995
  · exact B1119999
  · exact B1120003
  · exact B1120007
  · exact B1120011
  · exact B1120015
  · exact B1120019
  · exact B1120023
  · exact B1120027
  · exact B1120031
  · exact B1120035
  · exact B1120039
  · exact B1120043
  · exact B1120047
  · exact B1120051
  · exact B1120055
  · exact B1120059
  · exact B1120063
  · exact B1120067
  · exact B1120071
  · exact B1120075
  · exact B1120079
  · exact B1120083
  · exact B1120087
  · exact B1120091
  · exact B1120095
  · exact B1120099
  · exact B1120103
  · exact B1120107
  · exact B1120111
  · exact B1120115
  · exact B1120119
  · exact B1120123
  · exact B1120127
  · exact B1120131
  · exact B1120135
  · exact B1120139
  · exact B1120143
  · exact B1120147
  · exact B1120151
  · exact B1120155
  · exact B1120159
  · exact B1120163
  · exact B1120167
  · exact B1120171
  · exact B1120175
  · exact B1120179
  · exact B1120183
  · exact B1120187
  · exact B1120191
  · exact B1120195
  · exact B1120199
  · exact B1120203
  · exact B1120207
  · exact B1120211
  · exact B1120215
  · exact B1120219
  · exact B1120223
  · exact B1120227
  · exact B1120231
  · exact B1120235
  · exact B1120239
  · exact B1120243
  · exact B1120247
  · exact B1120251
  · exact B1120255
  · exact B1120259
  · exact B1120263
  · exact B1120267
  · exact B1120271
  · exact B1120275
  · exact B1120279
  · exact B1120283
  · exact B1120287
  · exact B1120291
  · exact B1120295
  · exact B1120299
  · exact B1120303
  · exact B1120307
  · exact B1120311
  · exact B1120315
  · exact B1120319
  · exact B1120323
  · exact B1120327
  · exact B1120331
  · exact B1120335
  · exact B1120339
  · exact B1120343
  · exact B1120347
  · exact B1120351
  · exact B1120355
  · exact B1120359
  · exact B1120363
  · exact B1120367
  · exact B1120371
  · exact B1120375
  · exact B1120379
  · exact B1120383
  · exact B1120387
  · exact B1120391
  · exact B1120395
  · exact B1120399
  · exact B1120403
  · exact B1120407
  · exact B1120411
  · exact B1120415
  · exact B1120419
  · exact B1120423
  · exact B1120427
  · exact B1120431
  · exact B1120435
  · exact B1120439
  · exact B1120443
  · exact B1120447
  · exact B1120451
  · exact B1120455
  · exact B1120459
  · exact B1120463
  · exact B1120467
  · exact B1120471
  · exact B1120475
  · exact B1120479
  · exact B1120483
  · exact B1120487
  · exact B1120491
  · exact B1120495
  · exact B1120499
  · exact B1120503
  · exact B1120507
  · exact B1120511
  · exact B1120515
  · exact B1120519
  · exact B1120523
  · exact B1120527
  · exact B1120531
  · exact B1120535
  · exact B1120539
  · exact B1120543
  · exact B1120547
  · exact B1120551
  · exact B1120555
  · exact B1120559
  · exact B1120563
  · exact B1120567
  · exact B1120571
  · exact B1120575
  · exact B1120579
  · exact B1120583
  · exact B1120587
  · exact B1120591
  · exact B1120595
  · exact B1120599
  · exact B1120603
  · exact B1120607
  · exact B1120611
  · exact B1120615
  · exact B1120619
  · exact B1120623
  · exact B1120627

theorem solution (m : ℕ) (hlo : 1116628 ≤ m) (hhi : m ≤ 1120628) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 279157 ≤ j := by omega
    have hj2 : j ≤ 280156 := by omega
    have hb : Blo 1116628 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 279857 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
