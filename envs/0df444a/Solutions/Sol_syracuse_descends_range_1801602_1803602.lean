-- Prove2me | solution 1 for syracuse_descends_range_1801602_1803602
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:50:48.030535+00:00
-- url     : https://prove2.me/submissions/3b8ed562-96e6-47da-8619-82b8040f09a0

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


theorem B2703365 : Blo 1801602 2703365 := bbase (se 4 (by rfl) ⟨253440, by rfl⟩ : syracuseStep 2703365 = 506881) (by norm_num)
theorem B1925137 : Blo 1801602 1925137 := bbase (se 2 (by rfl) ⟨721926, by rfl⟩ : syracuseStep 1925137 = 1443853) (by norm_num)
theorem B1925141 : Blo 1801602 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B2703389 : Blo 1801602 2703389 := bbase (se 3 (by rfl) ⟨506885, by rfl⟩ : syracuseStep 2703389 = 1013771) (by norm_num)
theorem B4055093 : Blo 1801602 4055093 := bbase (se 5 (by rfl) ⟨190082, by rfl⟩ : syracuseStep 4055093 = 380165) (by norm_num)
theorem B2703413 : Blo 1801602 2703413 := bbase (se 5 (by rfl) ⟨126722, by rfl⟩ : syracuseStep 2703413 = 253445) (by norm_num)
theorem B4563013 : Blo 1801602 4563013 := bbase (se 4 (by rfl) ⟨427782, by rfl⟩ : syracuseStep 4563013 = 855565) (by norm_num)
theorem B2703437 : Blo 1801602 2703437 := bbase (se 3 (by rfl) ⟨506894, by rfl⟩ : syracuseStep 2703437 = 1013789) (by norm_num)
theorem B2703461 : Blo 1801602 2703461 := bbase (se 4 (by rfl) ⟨253449, by rfl⟩ : syracuseStep 2703461 = 506899) (by norm_num)
theorem B4055165 : Blo 1801602 4055165 := bbase (se 3 (by rfl) ⟨760343, by rfl⟩ : syracuseStep 4055165 = 1520687) (by norm_num)
theorem B2703485 : Blo 1801602 2703485 := bbase (se 3 (by rfl) ⟨506903, by rfl⟩ : syracuseStep 2703485 = 1013807) (by norm_num)
theorem B2056333 : Blo 1801602 2056333 := bbase (se 3 (by rfl) ⟨385562, by rfl⟩ : syracuseStep 2056333 = 771125) (by norm_num)
theorem B2703509 : Blo 1801602 2703509 := bbase (se 6 (by rfl) ⟨63363, by rfl⟩ : syracuseStep 2703509 = 126727) (by norm_num)
theorem B2703533 : Blo 1801602 2703533 := bbase (se 3 (by rfl) ⟨506912, by rfl⟩ : syracuseStep 2703533 = 1013825) (by norm_num)
theorem B4563125 : Blo 1801602 4563125 := bbase (se 5 (by rfl) ⟨213896, by rfl⟩ : syracuseStep 4563125 = 427793) (by norm_num)
theorem B4055237 : Blo 1801602 4055237 := bbase (se 4 (by rfl) ⟨380178, by rfl⟩ : syracuseStep 4055237 = 760357) (by norm_num)
theorem B2703557 : Blo 1801602 2703557 := bbase (se 4 (by rfl) ⟨253458, by rfl⟩ : syracuseStep 2703557 = 506917) (by norm_num)
theorem B3850453 : Blo 1801602 3850453 := bbase (se 7 (by rfl) ⟨45122, by rfl⟩ : syracuseStep 3850453 = 90245) (by norm_num)
theorem B2703581 : Blo 1801602 2703581 := bbase (se 3 (by rfl) ⟨506921, by rfl⟩ : syracuseStep 2703581 = 1013843) (by norm_num)
theorem B2703605 : Blo 1801602 2703605 := bbase (se 5 (by rfl) ⟨126731, by rfl⟩ : syracuseStep 2703605 = 253463) (by norm_num)
theorem B4055309 : Blo 1801602 4055309 := bbase (se 3 (by rfl) ⟨760370, by rfl⟩ : syracuseStep 4055309 = 1520741) (by norm_num)
theorem B2703629 : Blo 1801602 2703629 := bbase (se 3 (by rfl) ⟨506930, by rfl⟩ : syracuseStep 2703629 = 1013861) (by norm_num)
theorem B1827085 : Blo 1801602 1827085 := bbase (se 3 (by rfl) ⟨342578, by rfl⟩ : syracuseStep 1827085 = 685157) (by norm_num)
theorem B6086933 : Blo 1801602 6086933 := bbase (se 6 (by rfl) ⟨142662, by rfl⟩ : syracuseStep 6086933 = 285325) (by norm_num)
theorem B2703653 : Blo 1801602 2703653 := bbase (se 4 (by rfl) ⟨253467, by rfl⟩ : syracuseStep 2703653 = 506935) (by norm_num)
theorem B2703677 : Blo 1801602 2703677 := bbase (se 3 (by rfl) ⟨506939, by rfl⟩ : syracuseStep 2703677 = 1013879) (by norm_num)
theorem B3850573 : Blo 1801602 3850573 := bbase (se 3 (by rfl) ⟨721982, by rfl⟩ : syracuseStep 3850573 = 1443965) (by norm_num)
theorem B4055381 : Blo 1801602 4055381 := bbase (se 10 (by rfl) ⟨5940, by rfl⟩ : syracuseStep 4055381 = 11881) (by norm_num)
theorem B2703701 : Blo 1801602 2703701 := bbase (se 10 (by rfl) ⟨3960, by rfl⟩ : syracuseStep 2703701 = 7921) (by norm_num)
theorem B2703725 : Blo 1801602 2703725 := bbase (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) (by norm_num)
theorem B4563317 : Blo 1801602 4563317 := bbase (se 5 (by rfl) ⟨213905, by rfl⟩ : syracuseStep 4563317 = 427811) (by norm_num)
theorem B2703749 : Blo 1801602 2703749 := bbase (se 4 (by rfl) ⟨253476, by rfl⟩ : syracuseStep 2703749 = 506953) (by norm_num)
theorem B4055453 : Blo 1801602 4055453 := bbase (se 3 (by rfl) ⟨760397, by rfl⟩ : syracuseStep 4055453 = 1520795) (by norm_num)
theorem B2703773 : Blo 1801602 2703773 := bbase (se 3 (by rfl) ⟨506957, by rfl⟩ : syracuseStep 2703773 = 1013915) (by norm_num)
theorem B2703797 : Blo 1801602 2703797 := bbase (se 5 (by rfl) ⟨126740, by rfl⟩ : syracuseStep 2703797 = 253481) (by norm_num)
theorem B2703821 : Blo 1801602 2703821 := bbase (se 3 (by rfl) ⟨506966, by rfl⟩ : syracuseStep 2703821 = 1013933) (by norm_num)
theorem B10961365 : Blo 1801602 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B1851869 : Blo 1801602 1851869 := bbase (se 3 (by rfl) ⟨347225, by rfl⟩ : syracuseStep 1851869 = 694451) (by norm_num)
theorem B4055525 : Blo 1801602 4055525 := bbase (se 4 (by rfl) ⟨380205, by rfl⟩ : syracuseStep 4055525 = 760411) (by norm_num)
theorem B2703845 : Blo 1801602 2703845 := bbase (se 4 (by rfl) ⟨253485, by rfl⟩ : syracuseStep 2703845 = 506971) (by norm_num)
theorem B2703869 : Blo 1801602 2703869 := bbase (se 3 (by rfl) ⟨506975, by rfl⟩ : syracuseStep 2703869 = 1013951) (by norm_num)
theorem B2703893 : Blo 1801602 2703893 := bbase (se 6 (by rfl) ⟨63372, by rfl⟩ : syracuseStep 2703893 = 126745) (by norm_num)
theorem B4055597 : Blo 1801602 4055597 := bbase (se 3 (by rfl) ⟨760424, by rfl⟩ : syracuseStep 4055597 = 1520849) (by norm_num)
theorem B2703917 : Blo 1801602 2703917 := bbase (se 3 (by rfl) ⟨506984, by rfl⟩ : syracuseStep 2703917 = 1013969) (by norm_num)
theorem B2703941 : Blo 1801602 2703941 := bbase (se 4 (by rfl) ⟨253494, by rfl⟩ : syracuseStep 2703941 = 506989) (by norm_num)
theorem B1827397 : Blo 1801602 1827397 := bbase (se 4 (by rfl) ⟨171318, by rfl⟩ : syracuseStep 1827397 = 342637) (by norm_num)
theorem B1925705 : Blo 1801602 1925705 := bbase (se 2 (by rfl) ⟨722139, by rfl⟩ : syracuseStep 1925705 = 1444279) (by norm_num)
theorem B3850829 : Blo 1801602 3850829 := bbase (se 3 (by rfl) ⟨722030, by rfl⟩ : syracuseStep 3850829 = 1444061) (by norm_num)
theorem B2703965 : Blo 1801602 2703965 := bbase (se 3 (by rfl) ⟨506993, by rfl⟩ : syracuseStep 2703965 = 1013987) (by norm_num)
theorem B4055669 : Blo 1801602 4055669 := bbase (se 5 (by rfl) ⟨190109, by rfl⟩ : syracuseStep 4055669 = 380219) (by norm_num)
theorem B2703989 : Blo 1801602 2703989 := bbase (se 5 (by rfl) ⟨126749, by rfl⟩ : syracuseStep 2703989 = 253499) (by norm_num)
theorem B1852045 : Blo 1801602 1852045 := bbase (se 3 (by rfl) ⟨347258, by rfl⟩ : syracuseStep 1852045 = 694517) (by norm_num)
theorem B2704013 : Blo 1801602 2704013 := bbase (se 3 (by rfl) ⟨507002, by rfl⟩ : syracuseStep 2704013 = 1014005) (by norm_num)
theorem B2704037 : Blo 1801602 2704037 := bbase (se 4 (by rfl) ⟨253503, by rfl⟩ : syracuseStep 2704037 = 507007) (by norm_num)
theorem B2343605 : Blo 1801602 2343605 := bbase (se 5 (by rfl) ⟨109856, by rfl⟩ : syracuseStep 2343605 = 219713) (by norm_num)
theorem B4055741 : Blo 1801602 4055741 := bbase (se 3 (by rfl) ⟨760451, by rfl⟩ : syracuseStep 4055741 = 1520903) (by norm_num)
theorem B2704061 : Blo 1801602 2704061 := bbase (se 3 (by rfl) ⟨507011, by rfl⟩ : syracuseStep 2704061 = 1014023) (by norm_num)
theorem B4563661 : Blo 1801602 4563661 := bbase (se 3 (by rfl) ⟨855686, by rfl⟩ : syracuseStep 4563661 = 1711373) (by norm_num)
theorem B2704085 : Blo 1801602 2704085 := bbase (se 7 (by rfl) ⟨31688, by rfl⟩ : syracuseStep 2704085 = 63377) (by norm_num)
theorem B2704109 : Blo 1801602 2704109 := bbase (se 3 (by rfl) ⟨507020, by rfl⟩ : syracuseStep 2704109 = 1014041) (by norm_num)
theorem B3654389 : Blo 1801602 3654389 := bbase (se 5 (by rfl) ⟨171299, by rfl⟩ : syracuseStep 3654389 = 342599) (by norm_num)
theorem B4055813 : Blo 1801602 4055813 := bbase (se 4 (by rfl) ⟨380232, by rfl⟩ : syracuseStep 4055813 = 760465) (by norm_num)
theorem B2704133 : Blo 1801602 2704133 := bbase (se 4 (by rfl) ⟨253512, by rfl⟩ : syracuseStep 2704133 = 507025) (by norm_num)
theorem B1925893 : Blo 1801602 1925893 := bbase (se 4 (by rfl) ⟨180552, by rfl⟩ : syracuseStep 1925893 = 361105) (by norm_num)
theorem B2196229 : Blo 1801602 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B2704157 : Blo 1801602 2704157 := bbase (se 3 (by rfl) ⟨507029, by rfl⟩ : syracuseStep 2704157 = 1014059) (by norm_num)
theorem B2704181 : Blo 1801602 2704181 := bbase (se 5 (by rfl) ⟨126758, by rfl⟩ : syracuseStep 2704181 = 253517) (by norm_num)
theorem B4563773 : Blo 1801602 4563773 := bbase (se 3 (by rfl) ⟨855707, by rfl⟩ : syracuseStep 4563773 = 1711415) (by norm_num)
theorem B7701317 : Blo 1801602 7701317 := bbase (se 4 (by rfl) ⟨721998, by rfl⟩ : syracuseStep 7701317 = 1443997) (by norm_num)
theorem B4055885 : Blo 1801602 4055885 := bbase (se 3 (by rfl) ⟨760478, by rfl⟩ : syracuseStep 4055885 = 1520957) (by norm_num)
theorem B2704205 : Blo 1801602 2704205 := bbase (se 3 (by rfl) ⟨507038, by rfl⟩ : syracuseStep 2704205 = 1014077) (by norm_num)
theorem B2704229 : Blo 1801602 2704229 := bbase (se 4 (by rfl) ⟨253521, by rfl⟩ : syracuseStep 2704229 = 507043) (by norm_num)
theorem B2704253 : Blo 1801602 2704253 := bbase (se 3 (by rfl) ⟨507047, by rfl⟩ : syracuseStep 2704253 = 1014095) (by norm_num)
theorem B4055957 : Blo 1801602 4055957 := bbase (se 6 (by rfl) ⟨95061, by rfl⟩ : syracuseStep 4055957 = 190123) (by norm_num)
theorem B2704277 : Blo 1801602 2704277 := bbase (se 6 (by rfl) ⟨63381, by rfl⟩ : syracuseStep 2704277 = 126763) (by norm_num)
theorem B6939557 : Blo 1801602 6939557 := bbase (se 4 (by rfl) ⟨650583, by rfl⟩ : syracuseStep 6939557 = 1301167) (by norm_num)
theorem B2704301 : Blo 1801602 2704301 := bbase (se 3 (by rfl) ⟨507056, by rfl⟩ : syracuseStep 2704301 = 1014113) (by norm_num)
theorem B14615477 : Blo 1801602 14615477 := bbase (se 5 (by rfl) ⟨685100, by rfl⟩ : syracuseStep 14615477 = 1370201) (by norm_num)
theorem B2704325 : Blo 1801602 2704325 := bbase (se 4 (by rfl) ⟨253530, by rfl⟩ : syracuseStep 2704325 = 507061) (by norm_num)
theorem B3040213 : Blo 1801602 3040213 := bbase (se 7 (by rfl) ⟨35627, by rfl⟩ : syracuseStep 3040213 = 71255) (by norm_num)
theorem B4056029 : Blo 1801602 4056029 := bbase (se 3 (by rfl) ⟨760505, by rfl⟩ : syracuseStep 4056029 = 1521011) (by norm_num)
theorem B2704349 : Blo 1801602 2704349 := bbase (se 3 (by rfl) ⟨507065, by rfl⟩ : syracuseStep 2704349 = 1014131) (by norm_num)
theorem B2704373 : Blo 1801602 2704373 := bbase (se 5 (by rfl) ⟨126767, by rfl⟩ : syracuseStep 2704373 = 253535) (by norm_num)
theorem B5776373 : Blo 1801602 5776373 := bbase (se 5 (by rfl) ⟨270767, by rfl⟩ : syracuseStep 5776373 = 541535) (by norm_num)
theorem B4563965 : Blo 1801602 4563965 := bbase (se 3 (by rfl) ⟨855743, by rfl⟩ : syracuseStep 4563965 = 1711487) (by norm_num)
theorem B9126917 : Blo 1801602 9126917 := bbase (se 4 (by rfl) ⟨855648, by rfl⟩ : syracuseStep 9126917 = 1711297) (by norm_num)
theorem B2704397 : Blo 1801602 2704397 := bbase (se 3 (by rfl) ⟨507074, by rfl⟩ : syracuseStep 2704397 = 1014149) (by norm_num)
theorem B4056101 : Blo 1801602 4056101 := bbase (se 4 (by rfl) ⟨380259, by rfl⟩ : syracuseStep 4056101 = 760519) (by norm_num)
theorem B2704421 : Blo 1801602 2704421 := bbase (se 4 (by rfl) ⟨253539, by rfl⟩ : syracuseStep 2704421 = 507079) (by norm_num)
theorem B3040301 : Blo 1801602 3040301 := bbase (se 3 (by rfl) ⟨570056, by rfl⟩ : syracuseStep 3040301 = 1140113) (by norm_num)
theorem B2704445 : Blo 1801602 2704445 := bbase (se 3 (by rfl) ⟨507083, by rfl⟩ : syracuseStep 2704445 = 1014167) (by norm_num)
theorem B2704469 : Blo 1801602 2704469 := bbase (se 8 (by rfl) ⟨15846, by rfl⟩ : syracuseStep 2704469 = 31693) (by norm_num)
theorem B4056173 : Blo 1801602 4056173 := bbase (se 3 (by rfl) ⟨760532, by rfl⟩ : syracuseStep 4056173 = 1521065) (by norm_num)
theorem B2704493 : Blo 1801602 2704493 := bbase (se 3 (by rfl) ⟨507092, by rfl⟩ : syracuseStep 2704493 = 1014185) (by norm_num)
theorem B2704517 : Blo 1801602 2704517 := bbase (se 4 (by rfl) ⟨253548, by rfl⟩ : syracuseStep 2704517 = 507097) (by norm_num)
theorem B2704541 : Blo 1801602 2704541 := bbase (se 3 (by rfl) ⟨507101, by rfl⟩ : syracuseStep 2704541 = 1014203) (by norm_num)
theorem B3040429 : Blo 1801602 3040429 := bbase (se 3 (by rfl) ⟨570080, by rfl⟩ : syracuseStep 3040429 = 1140161) (by norm_num)
theorem B4056245 : Blo 1801602 4056245 := bbase (se 5 (by rfl) ⟨190136, by rfl⟩ : syracuseStep 4056245 = 380273) (by norm_num)
theorem B2704565 : Blo 1801602 2704565 := bbase (se 5 (by rfl) ⟨126776, by rfl⟩ : syracuseStep 2704565 = 253553) (by norm_num)
theorem B2565317 : Blo 1801602 2565317 := bbase (se 4 (by rfl) ⟨240498, by rfl⟩ : syracuseStep 2565317 = 480997) (by norm_num)
theorem B2704589 : Blo 1801602 2704589 := bbase (se 3 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 2704589 = 1014221) (by norm_num)
theorem B2704613 : Blo 1801602 2704613 := bbase (se 4 (by rfl) ⟨253557, by rfl⟩ : syracuseStep 2704613 = 507115) (by norm_num)
theorem B8660213 : Blo 1801602 8660213 := bbase (se 5 (by rfl) ⟨405947, by rfl⟩ : syracuseStep 8660213 = 811895) (by norm_num)
theorem B4056317 : Blo 1801602 4056317 := bbase (se 3 (by rfl) ⟨760559, by rfl⟩ : syracuseStep 4056317 = 1521119) (by norm_num)
theorem B2704637 : Blo 1801602 2704637 := bbase (se 3 (by rfl) ⟨507119, by rfl⟩ : syracuseStep 2704637 = 1014239) (by norm_num)
theorem B3040517 : Blo 1801602 3040517 := bbase (se 4 (by rfl) ⟨285048, by rfl⟩ : syracuseStep 3040517 = 570097) (by norm_num)
theorem B13690133 : Blo 1801602 13690133 := bbase (se 6 (by rfl) ⟨320862, by rfl⟩ : syracuseStep 13690133 = 641725) (by norm_num)
theorem B2704661 : Blo 1801602 2704661 := bbase (se 6 (by rfl) ⟨63390, by rfl⟩ : syracuseStep 2704661 = 126781) (by norm_num)
theorem B2311465 : Blo 1801602 2311465 := bbase (se 2 (by rfl) ⟨866799, by rfl⟩ : syracuseStep 2311465 = 1733599) (by norm_num)
theorem B2704685 : Blo 1801602 2704685 := bbase (se 3 (by rfl) ⟨507128, by rfl⟩ : syracuseStep 2704685 = 1014257) (by norm_num)
theorem B4056389 : Blo 1801602 4056389 := bbase (se 4 (by rfl) ⟨380286, by rfl⟩ : syracuseStep 4056389 = 760573) (by norm_num)
theorem B2704709 : Blo 1801602 2704709 := bbase (se 4 (by rfl) ⟨253566, by rfl⟩ : syracuseStep 2704709 = 507133) (by norm_num)
theorem B1951061 : Blo 1801602 1951061 := bbase (se 12 (by rfl) ⟨714, by rfl⟩ : syracuseStep 1951061 = 1429) (by norm_num)
theorem B4564309 : Blo 1801602 4564309 := bbase (se 12 (by rfl) ⟨1671, by rfl⟩ : syracuseStep 4564309 = 3343) (by norm_num)
theorem B2704733 : Blo 1801602 2704733 := bbase (se 3 (by rfl) ⟨507137, by rfl⟩ : syracuseStep 2704733 = 1014275) (by norm_num)
theorem B2704757 : Blo 1801602 2704757 := bbase (se 5 (by rfl) ⟨126785, by rfl⟩ : syracuseStep 2704757 = 253571) (by norm_num)
theorem B3040645 : Blo 1801602 3040645 := bbase (se 4 (by rfl) ⟨285060, by rfl⟩ : syracuseStep 3040645 = 570121) (by norm_num)
theorem B6014341 : Blo 1801602 6014341 := bbase (se 4 (by rfl) ⟨563844, by rfl⟩ : syracuseStep 6014341 = 1127689) (by norm_num)
theorem B4056461 : Blo 1801602 4056461 := bbase (se 3 (by rfl) ⟨760586, by rfl⟩ : syracuseStep 4056461 = 1521173) (by norm_num)
theorem B2704781 : Blo 1801602 2704781 := bbase (se 3 (by rfl) ⟨507146, by rfl⟩ : syracuseStep 2704781 = 1014293) (by norm_num)
theorem B2704805 : Blo 1801602 2704805 := bbase (se 4 (by rfl) ⟨253575, by rfl⟩ : syracuseStep 2704805 = 507151) (by norm_num)
theorem B2704829 : Blo 1801602 2704829 := bbase (se 3 (by rfl) ⟨507155, by rfl⟩ : syracuseStep 2704829 = 1014311) (by norm_num)
theorem B4564421 : Blo 1801602 4564421 := bbase (se 4 (by rfl) ⟨427914, by rfl⟩ : syracuseStep 4564421 = 855829) (by norm_num)
theorem B3851717 : Blo 1801602 3851717 := bbase (se 4 (by rfl) ⟨361098, by rfl⟩ : syracuseStep 3851717 = 722197) (by norm_num)
theorem B2311625 : Blo 1801602 2311625 := bbase (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) (by norm_num)
theorem B4056533 : Blo 1801602 4056533 := bbase (se 7 (by rfl) ⟨47537, by rfl⟩ : syracuseStep 4056533 = 95075) (by norm_num)
theorem B2704853 : Blo 1801602 2704853 := bbase (se 7 (by rfl) ⟨31697, by rfl⟩ : syracuseStep 2704853 = 63395) (by norm_num)
theorem B3040733 : Blo 1801602 3040733 := bbase (se 3 (by rfl) ⟨570137, by rfl⟩ : syracuseStep 3040733 = 1140275) (by norm_num)
theorem B2704877 : Blo 1801602 2704877 := bbase (se 3 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 2704877 = 1014329) (by norm_num)
theorem B2704901 : Blo 1801602 2704901 := bbase (se 4 (by rfl) ⟨253584, by rfl⟩ : syracuseStep 2704901 = 507169) (by norm_num)
theorem B6497813 : Blo 1801602 6497813 := bbase (se 6 (by rfl) ⟨152292, by rfl⟩ : syracuseStep 6497813 = 304585) (by norm_num)
theorem B16451093 : Blo 1801602 16451093 := bbase (se 6 (by rfl) ⟨385572, by rfl⟩ : syracuseStep 16451093 = 771145) (by norm_num)
theorem B4056605 : Blo 1801602 4056605 := bbase (se 3 (by rfl) ⟨760613, by rfl⟩ : syracuseStep 4056605 = 1521227) (by norm_num)
theorem B2704925 : Blo 1801602 2704925 := bbase (se 3 (by rfl) ⟨507173, by rfl⟩ : syracuseStep 2704925 = 1014347) (by norm_num)
theorem B2704949 : Blo 1801602 2704949 := bbase (se 5 (by rfl) ⟨126794, by rfl⟩ : syracuseStep 2704949 = 253589) (by norm_num)
theorem B2704973 : Blo 1801602 2704973 := bbase (se 3 (by rfl) ⟨507182, by rfl⟩ : syracuseStep 2704973 = 1014365) (by norm_num)
theorem B3040861 : Blo 1801602 3040861 := bbase (se 3 (by rfl) ⟨570161, by rfl⟩ : syracuseStep 3040861 = 1140323) (by norm_num)
theorem B4056677 : Blo 1801602 4056677 := bbase (se 4 (by rfl) ⟨380313, by rfl⟩ : syracuseStep 4056677 = 760627) (by norm_num)
theorem B2704997 : Blo 1801602 2704997 := bbase (se 4 (by rfl) ⟨253593, by rfl⟩ : syracuseStep 2704997 = 507187) (by norm_num)
theorem B2705021 : Blo 1801602 2705021 := bbase (se 3 (by rfl) ⟨507191, by rfl⟩ : syracuseStep 2705021 = 1014383) (by norm_num)
theorem B4564613 : Blo 1801602 4564613 := bbase (se 4 (by rfl) ⟨427932, by rfl⟩ : syracuseStep 4564613 = 855865) (by norm_num)
theorem B2705045 : Blo 1801602 2705045 := bbase (se 6 (by rfl) ⟨63399, by rfl⟩ : syracuseStep 2705045 = 126799) (by norm_num)
theorem B4056749 : Blo 1801602 4056749 := bbase (se 3 (by rfl) ⟨760640, by rfl⟩ : syracuseStep 4056749 = 1521281) (by norm_num)
theorem B2705069 : Blo 1801602 2705069 := bbase (se 3 (by rfl) ⟨507200, by rfl⟩ : syracuseStep 2705069 = 1014401) (by norm_num)
theorem B13682357 : Blo 1801602 13682357 := bbase (se 5 (by rfl) ⟨641360, by rfl⟩ : syracuseStep 13682357 = 1282721) (by norm_num)
theorem B3040949 : Blo 1801602 3040949 := bbase (se 5 (by rfl) ⟨142544, by rfl⟩ : syracuseStep 3040949 = 285089) (by norm_num)
theorem B3851957 : Blo 1801602 3851957 := bbase (se 5 (by rfl) ⟨180560, by rfl⟩ : syracuseStep 3851957 = 361121) (by norm_num)
theorem B2705093 : Blo 1801602 2705093 := bbase (se 4 (by rfl) ⟨253602, by rfl⟩ : syracuseStep 2705093 = 507205) (by norm_num)
theorem B2705117 : Blo 1801602 2705117 := bbase (se 3 (by rfl) ⟨507209, by rfl⟩ : syracuseStep 2705117 = 1014419) (by norm_num)
theorem B4056821 : Blo 1801602 4056821 := bbase (se 5 (by rfl) ⟨190163, by rfl⟩ : syracuseStep 4056821 = 380327) (by norm_num)
theorem B2705141 : Blo 1801602 2705141 := bbase (se 5 (by rfl) ⟨126803, by rfl⟩ : syracuseStep 2705141 = 253607) (by norm_num)
theorem B2164477 : Blo 1801602 2164477 := bbase (se 3 (by rfl) ⟨405839, by rfl⟩ : syracuseStep 2164477 = 811679) (by norm_num)
theorem B2705165 : Blo 1801602 2705165 := bbase (se 3 (by rfl) ⟨507218, by rfl⟩ : syracuseStep 2705165 = 1014437) (by norm_num)
theorem B2705189 : Blo 1801602 2705189 := bbase (se 4 (by rfl) ⟨253611, by rfl⟩ : syracuseStep 2705189 = 507223) (by norm_num)
theorem B3041077 : Blo 1801602 3041077 := bbase (se 5 (by rfl) ⟨142550, by rfl⟩ : syracuseStep 3041077 = 285101) (by norm_num)
theorem B12994357 : Blo 1801602 12994357 := bbase (se 5 (by rfl) ⟨609110, by rfl⟩ : syracuseStep 12994357 = 1218221) (by norm_num)
theorem B6498101 : Blo 1801602 6498101 := bbase (se 5 (by rfl) ⟨304598, by rfl⟩ : syracuseStep 6498101 = 609197) (by norm_num)
theorem B4056893 : Blo 1801602 4056893 := bbase (se 3 (by rfl) ⟨760667, by rfl⟩ : syracuseStep 4056893 = 1521335) (by norm_num)
theorem B2705213 : Blo 1801602 2705213 := bbase (se 3 (by rfl) ⟨507227, by rfl⟩ : syracuseStep 2705213 = 1014455) (by norm_num)
theorem B2705237 : Blo 1801602 2705237 := bbase (se 9 (by rfl) ⟨7925, by rfl⟩ : syracuseStep 2705237 = 15851) (by norm_num)
theorem B2164573 : Blo 1801602 2164573 := bbase (se 3 (by rfl) ⟨405857, by rfl⟩ : syracuseStep 2164573 = 811715) (by norm_num)
theorem B2705261 : Blo 1801602 2705261 := bbase (se 3 (by rfl) ⟨507236, by rfl⟩ : syracuseStep 2705261 = 1014473) (by norm_num)
theorem B3082117 : Blo 1801602 3082117 := bbase (se 4 (by rfl) ⟨288948, by rfl⟩ : syracuseStep 3082117 = 577897) (by norm_num)
theorem B4056965 : Blo 1801602 4056965 := bbase (se 4 (by rfl) ⟨380340, by rfl⟩ : syracuseStep 4056965 = 760681) (by norm_num)
theorem B2705285 : Blo 1801602 2705285 := bbase (se 4 (by rfl) ⟨253620, by rfl⟩ : syracuseStep 2705285 = 507241) (by norm_num)
theorem B3041165 : Blo 1801602 3041165 := bbase (se 3 (by rfl) ⟨570218, by rfl⟩ : syracuseStep 3041165 = 1140437) (by norm_num)
theorem B2705309 : Blo 1801602 2705309 := bbase (se 3 (by rfl) ⟨507245, by rfl⟩ : syracuseStep 2705309 = 1014491) (by norm_num)
theorem B6588325 : Blo 1801602 6588325 := bbase (se 4 (by rfl) ⟨617655, by rfl⟩ : syracuseStep 6588325 = 1235311) (by norm_num)
theorem B2705333 : Blo 1801602 2705333 := bbase (se 5 (by rfl) ⟨126812, by rfl⟩ : syracuseStep 2705333 = 253625) (by norm_num)
theorem B6080453 : Blo 1801602 6080453 := bbase (se 4 (by rfl) ⟨570042, by rfl⟩ : syracuseStep 6080453 = 1140085) (by norm_num)
theorem B4057037 : Blo 1801602 4057037 := bbase (se 3 (by rfl) ⟨760694, by rfl⟩ : syracuseStep 4057037 = 1521389) (by norm_num)
theorem B2705357 : Blo 1801602 2705357 := bbase (se 3 (by rfl) ⟨507254, by rfl⟩ : syracuseStep 2705357 = 1014509) (by norm_num)
theorem B4564957 : Blo 1801602 4564957 := bbase (se 3 (by rfl) ⟨855929, by rfl⟩ : syracuseStep 4564957 = 1711859) (by norm_num)
theorem B8660965 : Blo 1801602 8660965 := bbase (se 4 (by rfl) ⟨811965, by rfl⟩ : syracuseStep 8660965 = 1623931) (by norm_num)
theorem B2705381 : Blo 1801602 2705381 := bbase (se 4 (by rfl) ⟨253629, by rfl⟩ : syracuseStep 2705381 = 507259) (by norm_num)
theorem B3041293 : Blo 1801602 3041293 := bbase (se 3 (by rfl) ⟨570242, by rfl⟩ : syracuseStep 3041293 = 1140485) (by norm_num)
theorem B4057109 : Blo 1801602 4057109 := bbase (se 6 (by rfl) ⟨95088, by rfl⟩ : syracuseStep 4057109 = 190177) (by norm_num)
theorem B3655733 : Blo 1801602 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B4565069 : Blo 1801602 4565069 := bbase (se 3 (by rfl) ⟨855950, by rfl⟩ : syracuseStep 4565069 = 1711901) (by norm_num)
theorem B4057181 : Blo 1801602 4057181 := bbase (se 3 (by rfl) ⟨760721, by rfl⟩ : syracuseStep 4057181 = 1521443) (by norm_num)
theorem B3041381 : Blo 1801602 3041381 := bbase (se 4 (by rfl) ⟨285129, by rfl⟩ : syracuseStep 3041381 = 570259) (by norm_num)
theorem B6842501 : Blo 1801602 6842501 := bbase (se 4 (by rfl) ⟨641484, by rfl⟩ : syracuseStep 6842501 = 1282969) (by norm_num)
theorem B9250949 : Blo 1801602 9250949 := bbase (se 4 (by rfl) ⟨867276, by rfl⟩ : syracuseStep 9250949 = 1734553) (by norm_num)
theorem B2435221 : Blo 1801602 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B4057253 : Blo 1801602 4057253 := bbase (se 4 (by rfl) ⟨380367, by rfl⟩ : syracuseStep 4057253 = 760735) (by norm_num)
theorem B1951957 : Blo 1801602 1951957 := bbase (se 7 (by rfl) ⟨22874, by rfl⟩ : syracuseStep 1951957 = 45749) (by norm_num)
theorem B2885861 : Blo 1801602 2885861 := bbase (se 4 (by rfl) ⟨270549, by rfl⟩ : syracuseStep 2885861 = 541099) (by norm_num)
theorem B3041509 : Blo 1801602 3041509 := bbase (se 4 (by rfl) ⟨285141, by rfl⟩ : syracuseStep 3041509 = 570283) (by norm_num)
theorem B4057325 : Blo 1801602 4057325 := bbase (se 3 (by rfl) ⟨760748, by rfl⟩ : syracuseStep 4057325 = 1521497) (by norm_num)
theorem B4565261 : Blo 1801602 4565261 := bbase (se 3 (by rfl) ⟨855986, by rfl⟩ : syracuseStep 4565261 = 1711973) (by norm_num)
theorem B9128213 : Blo 1801602 9128213 := bbase (se 6 (by rfl) ⟨213942, by rfl⟩ : syracuseStep 9128213 = 427885) (by norm_num)
theorem B4057397 : Blo 1801602 4057397 := bbase (se 5 (by rfl) ⟨190190, by rfl⟩ : syracuseStep 4057397 = 380381) (by norm_num)
theorem B2345269 : Blo 1801602 2345269 := bbase (se 5 (by rfl) ⟨109934, by rfl⟩ : syracuseStep 2345269 = 219869) (by norm_num)
theorem B3041597 : Blo 1801602 3041597 := bbase (se 3 (by rfl) ⟨570299, by rfl⟩ : syracuseStep 3041597 = 1140599) (by norm_num)
theorem B6080885 : Blo 1801602 6080885 := bbase (se 5 (by rfl) ⟨285041, by rfl⟩ : syracuseStep 6080885 = 570083) (by norm_num)
theorem B16673141 : Blo 1801602 16673141 := bbase (se 5 (by rfl) ⟨781553, by rfl⟩ : syracuseStep 16673141 = 1563107) (by norm_num)
theorem B4057469 : Blo 1801602 4057469 := bbase (se 3 (by rfl) ⟨760775, by rfl⟩ : syracuseStep 4057469 = 1521551) (by norm_num)
theorem B6842789 : Blo 1801602 6842789 := bbase (se 4 (by rfl) ⟨641511, by rfl⟩ : syracuseStep 6842789 = 1283023) (by norm_num)
theorem B2083261 : Blo 1801602 2083261 := bbase (se 3 (by rfl) ⟨390611, by rfl⟩ : syracuseStep 2083261 = 781223) (by norm_num)
theorem B3041725 : Blo 1801602 3041725 := bbase (se 3 (by rfl) ⟨570323, by rfl⟩ : syracuseStep 3041725 = 1140647) (by norm_num)
theorem B4057541 : Blo 1801602 4057541 := bbase (se 4 (by rfl) ⟨380394, by rfl⟩ : syracuseStep 4057541 = 760789) (by norm_num)
theorem B5851621 : Blo 1801602 5851621 := bbase (se 4 (by rfl) ⟨548589, by rfl⟩ : syracuseStep 5851621 = 1097179) (by norm_num)
theorem B4057613 : Blo 1801602 4057613 := bbase (se 3 (by rfl) ⟨760802, by rfl⟩ : syracuseStep 4057613 = 1521605) (by norm_num)
theorem B3041813 : Blo 1801602 3041813 := bbase (se 6 (by rfl) ⟨71292, by rfl⟩ : syracuseStep 3041813 = 142585) (by norm_num)
theorem B7703093 : Blo 1801602 7703093 := bbase (se 5 (by rfl) ⟨361082, by rfl⟩ : syracuseStep 7703093 = 722165) (by norm_num)
theorem B2566741 : Blo 1801602 2566741 := bbase (se 8 (by rfl) ⟨15039, by rfl⟩ : syracuseStep 2566741 = 30079) (by norm_num)
theorem B7309909 : Blo 1801602 7309909 := bbase (se 8 (by rfl) ⟨42831, by rfl⟩ : syracuseStep 7309909 = 85663) (by norm_num)
theorem B4057685 : Blo 1801602 4057685 := bbase (se 8 (by rfl) ⟨23775, by rfl⟩ : syracuseStep 4057685 = 47551) (by norm_num)
theorem B3041941 : Blo 1801602 3041941 := bbase (se 6 (by rfl) ⟨71295, by rfl⟩ : syracuseStep 3041941 = 142591) (by norm_num)
theorem B4057757 : Blo 1801602 4057757 := bbase (se 3 (by rfl) ⟨760829, by rfl⟩ : syracuseStep 4057757 = 1521659) (by norm_num)
theorem B5130965 : Blo 1801602 5130965 := bbase (se 7 (by rfl) ⟨60128, by rfl⟩ : syracuseStep 5130965 = 120257) (by norm_num)
theorem B4057829 : Blo 1801602 4057829 := bbase (se 4 (by rfl) ⟨380421, by rfl⟩ : syracuseStep 4057829 = 760843) (by norm_num)
theorem B3042029 : Blo 1801602 3042029 := bbase (se 3 (by rfl) ⟨570380, by rfl⟩ : syracuseStep 3042029 = 1140761) (by norm_num)
theorem B2435837 : Blo 1801602 2435837 := bbase (se 3 (by rfl) ⟨456719, by rfl⟩ : syracuseStep 2435837 = 913439) (by norm_num)
theorem B6081317 : Blo 1801602 6081317 := bbase (se 4 (by rfl) ⟨570123, by rfl⟩ : syracuseStep 6081317 = 1140247) (by norm_num)
theorem B7703333 : Blo 1801602 7703333 := bbase (se 4 (by rfl) ⟨722187, by rfl⟩ : syracuseStep 7703333 = 1444375) (by norm_num)
theorem B4057901 : Blo 1801602 4057901 := bbase (se 3 (by rfl) ⟨760856, by rfl⟩ : syracuseStep 4057901 = 1521713) (by norm_num)
theorem B2280241 : Blo 1801602 2280241 := bbase (se 2 (by rfl) ⟨855090, by rfl⟩ : syracuseStep 2280241 = 1710181) (by norm_num)
theorem B3042157 : Blo 1801602 3042157 := bbase (se 3 (by rfl) ⟨570404, by rfl⟩ : syracuseStep 3042157 = 1140809) (by norm_num)
theorem B4057973 : Blo 1801602 4057973 := bbase (se 5 (by rfl) ⟨190217, by rfl⟩ : syracuseStep 4057973 = 380435) (by norm_num)
theorem B2886533 : Blo 1801602 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B4058045 : Blo 1801602 4058045 := bbase (se 3 (by rfl) ⟨760883, by rfl⟩ : syracuseStep 4058045 = 1521767) (by norm_num)
theorem B3042245 : Blo 1801602 3042245 := bbase (se 4 (by rfl) ⟨285210, by rfl⟩ : syracuseStep 3042245 = 570421) (by norm_num)
theorem B3247061 : Blo 1801602 3247061 := bbase (se 7 (by rfl) ⟨38051, by rfl⟩ : syracuseStep 3247061 = 76103) (by norm_num)
theorem B2165717 : Blo 1801602 2165717 := bbase (se 7 (by rfl) ⟨25379, by rfl⟩ : syracuseStep 2165717 = 50759) (by norm_num)
theorem B2280413 : Blo 1801602 2280413 := bbase (se 3 (by rfl) ⟨427577, by rfl⟩ : syracuseStep 2280413 = 855155) (by norm_num)
theorem B2280469 : Blo 1801602 2280469 := bbase (se 6 (by rfl) ⟨53448, by rfl⟩ : syracuseStep 2280469 = 106897) (by norm_num)
theorem B3042373 : Blo 1801602 3042373 := bbase (se 4 (by rfl) ⟨285222, by rfl⟩ : syracuseStep 3042373 = 570445) (by norm_num)
theorem B1977433 : Blo 1801602 1977433 := bbase (se 2 (by rfl) ⟨741537, by rfl⟩ : syracuseStep 1977433 = 1483075) (by norm_num)
theorem B2280565 : Blo 1801602 2280565 := bbase (se 5 (by rfl) ⟨106901, by rfl⟩ : syracuseStep 2280565 = 213803) (by norm_num)
theorem B3247229 : Blo 1801602 3247229 := bbase (se 3 (by rfl) ⟨608855, by rfl⟩ : syracuseStep 3247229 = 1217711) (by norm_num)
theorem B3042461 : Blo 1801602 3042461 := bbase (se 3 (by rfl) ⟨570461, by rfl⟩ : syracuseStep 3042461 = 1140923) (by norm_num)
theorem B2567333 : Blo 1801602 2567333 := bbase (se 4 (by rfl) ⟨240687, by rfl⟩ : syracuseStep 2567333 = 481375) (by norm_num)
theorem B10267829 : Blo 1801602 10267829 := bbase (se 5 (by rfl) ⟨481304, by rfl⟩ : syracuseStep 10267829 = 962609) (by norm_num)
theorem B6081749 : Blo 1801602 6081749 := bbase (se 7 (by rfl) ⟨71270, by rfl⟩ : syracuseStep 6081749 = 142541) (by norm_num)
theorem B2567413 : Blo 1801602 2567413 := bbase (se 5 (by rfl) ⟨120347, by rfl⟩ : syracuseStep 2567413 = 240695) (by norm_num)
theorem B3042589 : Blo 1801602 3042589 := bbase (se 3 (by rfl) ⟨570485, by rfl⟩ : syracuseStep 3042589 = 1140971) (by norm_num)
theorem B2280737 : Blo 1801602 2280737 := bbase (se 2 (by rfl) ⟨855276, by rfl⟩ : syracuseStep 2280737 = 1710553) (by norm_num)
theorem B2166049 : Blo 1801602 2166049 := bbase (se 2 (by rfl) ⟨812268, by rfl⟩ : syracuseStep 2166049 = 1624537) (by norm_num)
theorem B2026813 : Blo 1801602 2026813 := bbase (se 3 (by rfl) ⟨380027, by rfl⟩ : syracuseStep 2026813 = 760055) (by norm_num)
theorem B2436421 : Blo 1801602 2436421 := bbase (se 4 (by rfl) ⟨228414, by rfl⟩ : syracuseStep 2436421 = 456829) (by norm_num)
theorem B2280793 : Blo 1801602 2280793 := bbase (se 2 (by rfl) ⟨855297, by rfl⟩ : syracuseStep 2280793 = 1710595) (by norm_num)
theorem B2026849 : Blo 1801602 2026849 := bbase (se 2 (by rfl) ⟨760068, by rfl⟩ : syracuseStep 2026849 = 1520137) (by norm_num)
theorem B2567533 : Blo 1801602 2567533 := bbase (se 3 (by rfl) ⟨481412, by rfl⟩ : syracuseStep 2567533 = 962825) (by norm_num)
theorem B5131637 : Blo 1801602 5131637 := bbase (se 5 (by rfl) ⟨240545, by rfl⟩ : syracuseStep 5131637 = 481091) (by norm_num)
theorem B3042677 : Blo 1801602 3042677 := bbase (se 5 (by rfl) ⟨142625, by rfl⟩ : syracuseStep 3042677 = 285251) (by norm_num)
theorem B2026885 : Blo 1801602 2026885 := bbase (se 4 (by rfl) ⟨190020, by rfl⟩ : syracuseStep 2026885 = 380041) (by norm_num)
theorem B2887045 : Blo 1801602 2887045 := bbase (se 4 (by rfl) ⟨270660, by rfl⟩ : syracuseStep 2887045 = 541321) (by norm_num)
theorem B2026921 : Blo 1801602 2026921 := bbase (se 2 (by rfl) ⟨760095, by rfl⟩ : syracuseStep 2026921 = 1520191) (by norm_num)
theorem B2280889 : Blo 1801602 2280889 := bbase (se 2 (by rfl) ⟨855333, by rfl⟩ : syracuseStep 2280889 = 1710667) (by norm_num)
theorem B2026957 : Blo 1801602 2026957 := bbase (se 3 (by rfl) ⟨380054, by rfl⟩ : syracuseStep 2026957 = 760109) (by norm_num)
theorem B2567629 : Blo 1801602 2567629 := bbase (se 3 (by rfl) ⟨481430, by rfl⟩ : syracuseStep 2567629 = 962861) (by norm_num)
theorem B2436589 : Blo 1801602 2436589 := bbase (se 3 (by rfl) ⟨456860, by rfl⟩ : syracuseStep 2436589 = 913721) (by norm_num)
theorem B2026993 : Blo 1801602 2026993 := bbase (se 2 (by rfl) ⟨760122, by rfl⟩ : syracuseStep 2026993 = 1520245) (by norm_num)
theorem B8220149 : Blo 1801602 8220149 := bbase (se 5 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 8220149 = 770639) (by norm_num)
theorem B3042805 : Blo 1801602 3042805 := bbase (se 5 (by rfl) ⟨142631, by rfl⟩ : syracuseStep 3042805 = 285263) (by norm_num)
theorem B2027029 : Blo 1801602 2027029 := bbase (se 6 (by rfl) ⟨47508, by rfl⟩ : syracuseStep 2027029 = 95017) (by norm_num)
theorem B30797333 : Blo 1801602 30797333 := bbase (se 6 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 30797333 = 1443625) (by norm_num)
theorem B9129509 : Blo 1801602 9129509 := bbase (se 4 (by rfl) ⟨855891, by rfl⟩ : syracuseStep 9129509 = 1711783) (by norm_num)
theorem B2027065 : Blo 1801602 2027065 := bbase (se 2 (by rfl) ⟨760149, by rfl⟩ : syracuseStep 2027065 = 1520299) (by norm_num)
theorem B6843973 : Blo 1801602 6843973 := bbase (se 4 (by rfl) ⟨641622, by rfl⟩ : syracuseStep 6843973 = 1283245) (by norm_num)
theorem B3042893 : Blo 1801602 3042893 := bbase (se 3 (by rfl) ⟨570542, by rfl⟩ : syracuseStep 3042893 = 1141085) (by norm_num)
theorem B58453589 : Blo 1801602 58453589 := bbase (se 8 (by rfl) ⟨342501, by rfl⟩ : syracuseStep 58453589 = 685003) (by norm_num)
theorem B2027101 : Blo 1801602 2027101 := bbase (se 3 (by rfl) ⟨380081, by rfl⟩ : syracuseStep 2027101 = 760163) (by norm_num)
theorem B2281061 : Blo 1801602 2281061 := bbase (se 4 (by rfl) ⟨213849, by rfl⟩ : syracuseStep 2281061 = 427699) (by norm_num)
theorem B2027137 : Blo 1801602 2027137 := bbase (se 2 (by rfl) ⟨760176, by rfl⟩ : syracuseStep 2027137 = 1520353) (by norm_num)
theorem B6082181 : Blo 1801602 6082181 := bbase (se 4 (by rfl) ⟨570204, by rfl⟩ : syracuseStep 6082181 = 1140409) (by norm_num)
theorem B3083917 : Blo 1801602 3083917 := bbase (se 3 (by rfl) ⟨578234, by rfl⟩ : syracuseStep 3083917 = 1156469) (by norm_num)
theorem B2281117 : Blo 1801602 2281117 := bbase (se 3 (by rfl) ⟨427709, by rfl⟩ : syracuseStep 2281117 = 855419) (by norm_num)
theorem B2027173 : Blo 1801602 2027173 := bbase (se 4 (by rfl) ⟨190047, by rfl⟩ : syracuseStep 2027173 = 380095) (by norm_num)
theorem B2027209 : Blo 1801602 2027209 := bbase (se 2 (by rfl) ⟨760203, by rfl⟩ : syracuseStep 2027209 = 1520407) (by norm_num)
theorem B3043021 : Blo 1801602 3043021 := bbase (se 3 (by rfl) ⟨570566, by rfl⟩ : syracuseStep 3043021 = 1141133) (by norm_num)
theorem B2027245 : Blo 1801602 2027245 := bbase (se 3 (by rfl) ⟨380108, by rfl⟩ : syracuseStep 2027245 = 760217) (by norm_num)
theorem B2281213 : Blo 1801602 2281213 := bbase (se 3 (by rfl) ⟨427727, by rfl⟩ : syracuseStep 2281213 = 855455) (by norm_num)
theorem B2027281 : Blo 1801602 2027281 := bbase (se 2 (by rfl) ⟨760230, by rfl⟩ : syracuseStep 2027281 = 1520461) (by norm_num)
theorem B20533013 : Blo 1801602 20533013 := bbase (se 6 (by rfl) ⟨481242, by rfl⟩ : syracuseStep 20533013 = 962485) (by norm_num)
theorem B5132069 : Blo 1801602 5132069 := bbase (se 4 (by rfl) ⟨481131, by rfl⟩ : syracuseStep 5132069 = 962263) (by norm_num)
theorem B3043109 : Blo 1801602 3043109 := bbase (se 4 (by rfl) ⟨285291, by rfl⟩ : syracuseStep 3043109 = 570583) (by norm_num)
theorem B2027317 : Blo 1801602 2027317 := bbase (se 5 (by rfl) ⟨95030, by rfl⟩ : syracuseStep 2027317 = 190061) (by norm_num)
theorem B2887501 : Blo 1801602 2887501 := bbase (se 3 (by rfl) ⟨541406, by rfl⟩ : syracuseStep 2887501 = 1082813) (by norm_num)
theorem B2027353 : Blo 1801602 2027353 := bbase (se 2 (by rfl) ⟨760257, by rfl⟩ : syracuseStep 2027353 = 1520515) (by norm_num)
theorem B6844277 : Blo 1801602 6844277 := bbase (se 5 (by rfl) ⟨320825, by rfl⟩ : syracuseStep 6844277 = 641651) (by norm_num)
theorem B2027389 : Blo 1801602 2027389 := bbase (se 3 (by rfl) ⟨380135, by rfl⟩ : syracuseStep 2027389 = 760271) (by norm_num)
theorem B2027425 : Blo 1801602 2027425 := bbase (se 2 (by rfl) ⟨760284, by rfl⟩ : syracuseStep 2027425 = 1520569) (by norm_num)
theorem B3043237 : Blo 1801602 3043237 := bbase (se 4 (by rfl) ⟨285303, by rfl⟩ : syracuseStep 3043237 = 570607) (by norm_num)
theorem B2281385 : Blo 1801602 2281385 := bbase (se 2 (by rfl) ⟨855519, by rfl⟩ : syracuseStep 2281385 = 1711039) (by norm_num)
theorem B11554741 : Blo 1801602 11554741 := bbase (se 5 (by rfl) ⟨541628, by rfl⟩ : syracuseStep 11554741 = 1083257) (by norm_num)
theorem B9121733 : Blo 1801602 9121733 := bbase (se 4 (by rfl) ⟨855162, by rfl⟩ : syracuseStep 9121733 = 1710325) (by norm_num)
theorem B2027461 : Blo 1801602 2027461 := bbase (se 4 (by rfl) ⟨190074, by rfl⟩ : syracuseStep 2027461 = 380149) (by norm_num)
theorem B10014677 : Blo 1801602 10014677 := bbase (se 7 (by rfl) ⟨117359, by rfl⟩ : syracuseStep 10014677 = 234719) (by norm_num)
theorem B2166745 : Blo 1801602 2166745 := bbase (se 2 (by rfl) ⟨812529, by rfl⟩ : syracuseStep 2166745 = 1625059) (by norm_num)
theorem B2281441 : Blo 1801602 2281441 := bbase (se 2 (by rfl) ⟨855540, by rfl⟩ : syracuseStep 2281441 = 1711081) (by norm_num)
theorem B6164453 : Blo 1801602 6164453 := bbase (se 4 (by rfl) ⟨577917, by rfl⟩ : syracuseStep 6164453 = 1155835) (by norm_num)
theorem B2027497 : Blo 1801602 2027497 := bbase (se 2 (by rfl) ⟨760311, by rfl⟩ : syracuseStep 2027497 = 1520623) (by norm_num)
theorem B3043325 : Blo 1801602 3043325 := bbase (se 3 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 3043325 = 1141247) (by norm_num)
theorem B2027533 : Blo 1801602 2027533 := bbase (se 3 (by rfl) ⟨380162, by rfl⟩ : syracuseStep 2027533 = 760325) (by norm_num)
theorem B2027569 : Blo 1801602 2027569 := bbase (se 2 (by rfl) ⟨760338, by rfl⟩ : syracuseStep 2027569 = 1520677) (by norm_num)
theorem B6082613 : Blo 1801602 6082613 := bbase (se 5 (by rfl) ⟨285122, by rfl⟩ : syracuseStep 6082613 = 570245) (by norm_num)
theorem B2281537 : Blo 1801602 2281537 := bbase (se 2 (by rfl) ⟨855576, by rfl⟩ : syracuseStep 2281537 = 1711153) (by norm_num)
theorem B18493525 : Blo 1801602 18493525 := bbase (se 8 (by rfl) ⟨108360, by rfl⟩ : syracuseStep 18493525 = 216721) (by norm_num)
theorem B2027605 : Blo 1801602 2027605 := bbase (se 8 (by rfl) ⟨11880, by rfl⟩ : syracuseStep 2027605 = 23761) (by norm_num)
theorem B2027641 : Blo 1801602 2027641 := bbase (se 2 (by rfl) ⟨760365, by rfl⟩ : syracuseStep 2027641 = 1520731) (by norm_num)
theorem B3043453 : Blo 1801602 3043453 := bbase (se 3 (by rfl) ⟨570647, by rfl⟩ : syracuseStep 3043453 = 1141295) (by norm_num)
theorem B3420301 : Blo 1801602 3420301 := bbase (se 3 (by rfl) ⟨641306, by rfl⟩ : syracuseStep 3420301 = 1282613) (by norm_num)
theorem B2027677 : Blo 1801602 2027677 := bbase (se 3 (by rfl) ⟨380189, by rfl⟩ : syracuseStep 2027677 = 760379) (by norm_num)
theorem B2027713 : Blo 1801602 2027713 := bbase (se 2 (by rfl) ⟨760392, by rfl⟩ : syracuseStep 2027713 = 1520785) (by norm_num)
theorem B3043541 : Blo 1801602 3043541 := bbase (se 7 (by rfl) ⟨35666, by rfl⟩ : syracuseStep 3043541 = 71333) (by norm_num)
theorem B2027749 : Blo 1801602 2027749 := bbase (se 4 (by rfl) ⟨190101, by rfl⟩ : syracuseStep 2027749 = 380203) (by norm_num)
theorem B2281709 : Blo 1801602 2281709 := bbase (se 3 (by rfl) ⟨427820, by rfl⟩ : syracuseStep 2281709 = 855641) (by norm_num)
theorem B2027785 : Blo 1801602 2027785 := bbase (se 2 (by rfl) ⟨760419, by rfl⟩ : syracuseStep 2027785 = 1520839) (by norm_num)
theorem B2281765 : Blo 1801602 2281765 := bbase (se 4 (by rfl) ⟨213915, by rfl⟩ : syracuseStep 2281765 = 427831) (by norm_num)
theorem B3420461 : Blo 1801602 3420461 := bbase (se 3 (by rfl) ⟨641336, by rfl⟩ : syracuseStep 3420461 = 1282673) (by norm_num)
theorem B2027821 : Blo 1801602 2027821 := bbase (se 3 (by rfl) ⟨380216, by rfl⟩ : syracuseStep 2027821 = 760433) (by norm_num)
theorem B2027857 : Blo 1801602 2027857 := bbase (se 2 (by rfl) ⟨760446, by rfl⟩ : syracuseStep 2027857 = 1520893) (by norm_num)
theorem B2027893 : Blo 1801602 2027893 := bbase (se 5 (by rfl) ⟨95057, by rfl⟩ : syracuseStep 2027893 = 190115) (by norm_num)
theorem B2281861 : Blo 1801602 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B2027929 : Blo 1801602 2027929 := bbase (se 2 (by rfl) ⟨760473, by rfl⟩ : syracuseStep 2027929 = 1520947) (by norm_num)
theorem B3420605 : Blo 1801602 3420605 := bbase (se 3 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 3420605 = 1282727) (by norm_num)
theorem B2027965 : Blo 1801602 2027965 := bbase (se 3 (by rfl) ⟨380243, by rfl⟩ : syracuseStep 2027965 = 760487) (by norm_num)
theorem B2028001 : Blo 1801602 2028001 := bbase (se 2 (by rfl) ⟨760500, by rfl⟩ : syracuseStep 2028001 = 1521001) (by norm_num)
theorem B6083045 : Blo 1801602 6083045 := bbase (se 4 (by rfl) ⟨570285, by rfl⟩ : syracuseStep 6083045 = 1140571) (by norm_num)
theorem B2888173 : Blo 1801602 2888173 := bbase (se 3 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 2888173 = 1083065) (by norm_num)
theorem B2028037 : Blo 1801602 2028037 := bbase (se 4 (by rfl) ⟨190128, by rfl⟩ : syracuseStep 2028037 = 380257) (by norm_num)
theorem B5132821 : Blo 1801602 5132821 := bbase (se 6 (by rfl) ⟨120300, by rfl⟩ : syracuseStep 5132821 = 240601) (by norm_num)
theorem B2028073 : Blo 1801602 2028073 := bbase (se 2 (by rfl) ⟨760527, by rfl⟩ : syracuseStep 2028073 = 1521055) (by norm_num)
theorem B2282033 : Blo 1801602 2282033 := bbase (se 2 (by rfl) ⟨855762, by rfl⟩ : syracuseStep 2282033 = 1711525) (by norm_num)
theorem B2028109 : Blo 1801602 2028109 := bbase (se 3 (by rfl) ⟨380270, by rfl⟩ : syracuseStep 2028109 = 760541) (by norm_num)
theorem B2282089 : Blo 1801602 2282089 := bbase (se 2 (by rfl) ⟨855783, by rfl⟩ : syracuseStep 2282089 = 1711567) (by norm_num)
theorem B2028145 : Blo 1801602 2028145 := bbase (se 2 (by rfl) ⟨760554, by rfl⟩ : syracuseStep 2028145 = 1521109) (by norm_num)
theorem B13873781 : Blo 1801602 13873781 := bbase (se 5 (by rfl) ⟨650333, by rfl⟩ : syracuseStep 13873781 = 1300667) (by norm_num)
theorem B7697045 : Blo 1801602 7697045 := bbase (se 6 (by rfl) ⟨180399, by rfl⟩ : syracuseStep 7697045 = 360799) (by norm_num)
theorem B2028181 : Blo 1801602 2028181 := bbase (se 6 (by rfl) ⟨47535, by rfl⟩ : syracuseStep 2028181 = 95071) (by norm_num)
theorem B2028217 : Blo 1801602 2028217 := bbase (se 2 (by rfl) ⟨760581, by rfl⟩ : syracuseStep 2028217 = 1521163) (by norm_num)
theorem B2740925 : Blo 1801602 2740925 := bbase (se 3 (by rfl) ⟨513923, by rfl⟩ : syracuseStep 2740925 = 1027847) (by norm_num)
theorem B2282185 : Blo 1801602 2282185 := bbase (se 2 (by rfl) ⟨855819, by rfl⟩ : syracuseStep 2282185 = 1711639) (by norm_num)
theorem B5771989 : Blo 1801602 5771989 := bbase (se 7 (by rfl) ⟨67640, by rfl⟩ : syracuseStep 5771989 = 135281) (by norm_num)
theorem B3420893 : Blo 1801602 3420893 := bbase (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) (by norm_num)
theorem B2028253 : Blo 1801602 2028253 := bbase (se 3 (by rfl) ⟨380297, by rfl⟩ : syracuseStep 2028253 = 760595) (by norm_num)
theorem B2028289 : Blo 1801602 2028289 := bbase (se 2 (by rfl) ⟨760608, by rfl⟩ : syracuseStep 2028289 = 1521217) (by norm_num)
theorem B4330253 : Blo 1801602 4330253 := bbase (se 3 (by rfl) ⟨811922, by rfl⟩ : syracuseStep 4330253 = 1623845) (by norm_num)
theorem B2028325 : Blo 1801602 2028325 := bbase (se 4 (by rfl) ⟨190155, by rfl⟩ : syracuseStep 2028325 = 380311) (by norm_num)
theorem B2028361 : Blo 1801602 2028361 := bbase (se 2 (by rfl) ⟨760635, by rfl⟩ : syracuseStep 2028361 = 1521271) (by norm_num)
theorem B3904357 : Blo 1801602 3904357 := bbase (se 4 (by rfl) ⟨366033, by rfl⟩ : syracuseStep 3904357 = 732067) (by norm_num)
theorem B3126125 : Blo 1801602 3126125 := bbase (se 3 (by rfl) ⟨586148, by rfl⟩ : syracuseStep 3126125 = 1172297) (by norm_num)
theorem B2028397 : Blo 1801602 2028397 := bbase (se 3 (by rfl) ⟨380324, by rfl⟩ : syracuseStep 2028397 = 760649) (by norm_num)
theorem B3421045 : Blo 1801602 3421045 := bbase (se 5 (by rfl) ⟨160361, by rfl⟩ : syracuseStep 3421045 = 320723) (by norm_num)
theorem B2282357 : Blo 1801602 2282357 := bbase (se 5 (by rfl) ⟨106985, by rfl⟩ : syracuseStep 2282357 = 213971) (by norm_num)
theorem B4109197 : Blo 1801602 4109197 := bbase (se 3 (by rfl) ⟨770474, by rfl⟩ : syracuseStep 4109197 = 1540949) (by norm_num)
theorem B2028433 : Blo 1801602 2028433 := bbase (se 2 (by rfl) ⟨760662, by rfl⟩ : syracuseStep 2028433 = 1521325) (by norm_num)
theorem B6083477 : Blo 1801602 6083477 := bbase (se 6 (by rfl) ⟨142581, by rfl⟩ : syracuseStep 6083477 = 285163) (by norm_num)
theorem B2888597 : Blo 1801602 2888597 := bbase (se 6 (by rfl) ⟨67701, by rfl⟩ : syracuseStep 2888597 = 135403) (by norm_num)
theorem B2282413 : Blo 1801602 2282413 := bbase (se 3 (by rfl) ⟨427952, by rfl⟩ : syracuseStep 2282413 = 855905) (by norm_num)
theorem B2028469 : Blo 1801602 2028469 := bbase (se 5 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 2028469 = 190169) (by norm_num)
theorem B3470293 : Blo 1801602 3470293 := bbase (se 7 (by rfl) ⟨40667, by rfl⟩ : syracuseStep 3470293 = 81335) (by norm_num)
theorem B2028505 : Blo 1801602 2028505 := bbase (se 2 (by rfl) ⟨760689, by rfl⟩ : syracuseStep 2028505 = 1521379) (by norm_num)
theorem B2028541 : Blo 1801602 2028541 := bbase (se 3 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 2028541 = 760703) (by norm_num)
theorem B2282509 : Blo 1801602 2282509 := bbase (se 3 (by rfl) ⟨427970, by rfl⟩ : syracuseStep 2282509 = 855941) (by norm_num)
theorem B2028577 : Blo 1801602 2028577 := bbase (se 2 (by rfl) ⟨760716, by rfl⟩ : syracuseStep 2028577 = 1521433) (by norm_num)
theorem B2028613 : Blo 1801602 2028613 := bbase (se 4 (by rfl) ⟨190182, by rfl⟩ : syracuseStep 2028613 = 380365) (by norm_num)
theorem B2028649 : Blo 1801602 2028649 := bbase (se 2 (by rfl) ⟨760743, by rfl⟩ : syracuseStep 2028649 = 1521487) (by norm_num)
theorem B4871285 : Blo 1801602 4871285 := bbase (se 5 (by rfl) ⟨228341, by rfl⟩ : syracuseStep 4871285 = 456683) (by norm_num)
theorem B4330637 : Blo 1801602 4330637 := bbase (se 3 (by rfl) ⟨811994, by rfl⟩ : syracuseStep 4330637 = 1623989) (by norm_num)
theorem B2028685 : Blo 1801602 2028685 := bbase (se 3 (by rfl) ⟨380378, by rfl⟩ : syracuseStep 2028685 = 760757) (by norm_num)
theorem B3421349 : Blo 1801602 3421349 := bbase (se 4 (by rfl) ⟨320751, by rfl⟩ : syracuseStep 3421349 = 641503) (by norm_num)
theorem B2028721 : Blo 1801602 2028721 := bbase (se 2 (by rfl) ⟨760770, by rfl⟩ : syracuseStep 2028721 = 1521541) (by norm_num)
theorem B2888885 : Blo 1801602 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B2282681 : Blo 1801602 2282681 := bbase (se 2 (by rfl) ⟨856005, by rfl⟩ : syracuseStep 2282681 = 1712011) (by norm_num)
theorem B9123029 : Blo 1801602 9123029 := bbase (se 7 (by rfl) ⟨106910, by rfl⟩ : syracuseStep 9123029 = 213821) (by norm_num)
theorem B2028757 : Blo 1801602 2028757 := bbase (se 7 (by rfl) ⟨23774, by rfl⟩ : syracuseStep 2028757 = 47549) (by norm_num)
theorem B2028793 : Blo 1801602 2028793 := bbase (se 2 (by rfl) ⟨760797, by rfl⟩ : syracuseStep 2028793 = 1521595) (by norm_num)
theorem B2028829 : Blo 1801602 2028829 := bbase (se 3 (by rfl) ⟨380405, by rfl⟩ : syracuseStep 2028829 = 760811) (by norm_num)
theorem B2028865 : Blo 1801602 2028865 := bbase (se 2 (by rfl) ⟨760824, by rfl⟩ : syracuseStep 2028865 = 1521649) (by norm_num)
theorem B6083909 : Blo 1801602 6083909 := bbase (se 4 (by rfl) ⟨570366, by rfl⟩ : syracuseStep 6083909 = 1140733) (by norm_num)
theorem B4330837 : Blo 1801602 4330837 := bbase (se 14 (by rfl) ⟨396, by rfl⟩ : syracuseStep 4330837 = 793) (by norm_num)
theorem B2028901 : Blo 1801602 2028901 := bbase (se 4 (by rfl) ⟨190209, by rfl⟩ : syracuseStep 2028901 = 380419) (by norm_num)
theorem B2028937 : Blo 1801602 2028937 := bbase (se 2 (by rfl) ⟨760851, by rfl⟩ : syracuseStep 2028937 = 1521703) (by norm_num)
theorem B2028973 : Blo 1801602 2028973 := bbase (se 3 (by rfl) ⟨380432, by rfl⟩ : syracuseStep 2028973 = 760865) (by norm_num)
theorem B2029009 : Blo 1801602 2029009 := bbase (se 2 (by rfl) ⟨760878, by rfl⟩ : syracuseStep 2029009 = 1521757) (by norm_num)
theorem B2029045 : Blo 1801602 2029045 := bbase (se 5 (by rfl) ⟨95111, by rfl⟩ : syracuseStep 2029045 = 190223) (by norm_num)
theorem B4560421 : Blo 1801602 4560421 := bbase (se 4 (by rfl) ⟨427539, by rfl⟩ : syracuseStep 4560421 = 855079) (by norm_num)
theorem B4560533 : Blo 1801602 4560533 := bbase (se 6 (by rfl) ⟨106887, by rfl⟩ : syracuseStep 4560533 = 213775) (by norm_num)
theorem B3249829 : Blo 1801602 3249829 := bbase (se 4 (by rfl) ⟨304671, by rfl⟩ : syracuseStep 3249829 = 609343) (by norm_num)
theorem B2741941 : Blo 1801602 2741941 := bbase (se 5 (by rfl) ⟨128528, by rfl⟩ : syracuseStep 2741941 = 257057) (by norm_num)
theorem B3847925 : Blo 1801602 3847925 := bbase (se 5 (by rfl) ⟨180371, by rfl⟩ : syracuseStep 3847925 = 360743) (by norm_num)
theorem B6084341 : Blo 1801602 6084341 := bbase (se 5 (by rfl) ⟨285203, by rfl⟩ : syracuseStep 6084341 = 570407) (by norm_num)
theorem B4560725 : Blo 1801602 4560725 := bbase (se 9 (by rfl) ⟨13361, by rfl⟩ : syracuseStep 4560725 = 26723) (by norm_num)
theorem B5773157 : Blo 1801602 5773157 := bbase (se 4 (by rfl) ⟨541233, by rfl⟩ : syracuseStep 5773157 = 1082467) (by norm_num)
theorem B3422101 : Blo 1801602 3422101 := bbase (se 6 (by rfl) ⟨80205, by rfl⟩ : syracuseStep 3422101 = 160411) (by norm_num)
theorem B6846389 : Blo 1801602 6846389 := bbase (se 5 (by rfl) ⟨320924, by rfl⟩ : syracuseStep 6846389 = 641849) (by norm_num)
theorem B32872405 : Blo 1801602 32872405 := bbase (se 7 (by rfl) ⟨385223, by rfl⟩ : syracuseStep 32872405 = 770447) (by norm_num)
theorem B3250133 : Blo 1801602 3250133 := bbase (se 7 (by rfl) ⟨38087, by rfl⟩ : syracuseStep 3250133 = 76175) (by norm_num)
theorem B3422245 : Blo 1801602 3422245 := bbase (se 4 (by rfl) ⟨320835, by rfl⟩ : syracuseStep 3422245 = 641671) (by norm_num)
theorem B17324117 : Blo 1801602 17324117 := bbase (se 8 (by rfl) ⟨101508, by rfl⟩ : syracuseStep 17324117 = 203017) (by norm_num)
theorem B6084773 : Blo 1801602 6084773 := bbase (se 4 (by rfl) ⟨570447, by rfl⟩ : syracuseStep 6084773 = 1140895) (by norm_num)
theorem B4561069 : Blo 1801602 4561069 := bbase (se 3 (by rfl) ⟨855200, by rfl⟩ : syracuseStep 4561069 = 1710401) (by norm_num)
theorem B3422405 : Blo 1801602 3422405 := bbase (se 4 (by rfl) ⟨320850, by rfl⟩ : syracuseStep 3422405 = 641701) (by norm_num)
theorem B6846677 : Blo 1801602 6846677 := bbase (se 7 (by rfl) ⟨80234, by rfl⟩ : syracuseStep 6846677 = 160469) (by norm_num)
theorem B6584597 : Blo 1801602 6584597 := bbase (se 6 (by rfl) ⟨154326, by rfl⟩ : syracuseStep 6584597 = 308653) (by norm_num)
theorem B4561181 : Blo 1801602 4561181 := bbase (se 3 (by rfl) ⟨855221, by rfl⟩ : syracuseStep 4561181 = 1710443) (by norm_num)
theorem B3422549 : Blo 1801602 3422549 := bbase (se 10 (by rfl) ⟨5013, by rfl⟩ : syracuseStep 3422549 = 10027) (by norm_num)
theorem B3291589 : Blo 1801602 3291589 := bbase (se 4 (by rfl) ⟨308586, by rfl⟩ : syracuseStep 3291589 = 617173) (by norm_num)
theorem B4561373 : Blo 1801602 4561373 := bbase (se 3 (by rfl) ⟨855257, by rfl⟩ : syracuseStep 4561373 = 1710515) (by norm_num)
theorem B9124325 : Blo 1801602 9124325 := bbase (se 4 (by rfl) ⟨855405, by rfl⟩ : syracuseStep 9124325 = 1710811) (by norm_num)
theorem B6085205 : Blo 1801602 6085205 := bbase (se 8 (by rfl) ⟨35655, by rfl⟩ : syracuseStep 6085205 = 71311) (by norm_num)
theorem B3848813 : Blo 1801602 3848813 := bbase (se 3 (by rfl) ⟨721652, by rfl⟩ : syracuseStep 3848813 = 1443305) (by norm_num)
theorem B3422837 : Blo 1801602 3422837 := bbase (se 5 (by rfl) ⟨160445, by rfl⟩ : syracuseStep 3422837 = 320891) (by norm_num)
theorem B4053653 : Blo 1801602 4053653 := bbase (se 6 (by rfl) ⟨95007, by rfl⟩ : syracuseStep 4053653 = 190015) (by norm_num)
theorem B4053725 : Blo 1801602 4053725 := bbase (se 3 (by rfl) ⟨760073, by rfl⟩ : syracuseStep 4053725 = 1520147) (by norm_num)
theorem B3848933 : Blo 1801602 3848933 := bbase (se 4 (by rfl) ⟨360837, by rfl⟩ : syracuseStep 3848933 = 721675) (by norm_num)
theorem B3422989 : Blo 1801602 3422989 := bbase (se 3 (by rfl) ⟨641810, by rfl⟩ : syracuseStep 3422989 = 1283621) (by norm_num)
theorem B4053797 : Blo 1801602 4053797 := bbase (se 4 (by rfl) ⟨380043, by rfl⟩ : syracuseStep 4053797 = 760087) (by norm_num)
theorem B4561717 : Blo 1801602 4561717 := bbase (se 5 (by rfl) ⟨213830, by rfl⟩ : syracuseStep 4561717 = 427661) (by norm_num)
theorem B4053869 : Blo 1801602 4053869 := bbase (se 3 (by rfl) ⟨760100, by rfl⟩ : syracuseStep 4053869 = 1520201) (by norm_num)
theorem B4332413 : Blo 1801602 4332413 := bbase (se 3 (by rfl) ⟨812327, by rfl⟩ : syracuseStep 4332413 = 1624655) (by norm_num)
theorem B4561829 : Blo 1801602 4561829 := bbase (se 4 (by rfl) ⟨427671, by rfl⟩ : syracuseStep 4561829 = 855343) (by norm_num)
theorem B4053941 : Blo 1801602 4053941 := bbase (se 5 (by rfl) ⟨190028, by rfl⟩ : syracuseStep 4053941 = 380057) (by norm_num)
theorem B7306213 : Blo 1801602 7306213 := bbase (se 4 (by rfl) ⟨684957, by rfl⟩ : syracuseStep 7306213 = 1369915) (by norm_num)
theorem B4054013 : Blo 1801602 4054013 := bbase (se 3 (by rfl) ⟨760127, by rfl⟩ : syracuseStep 4054013 = 1520255) (by norm_num)
theorem B6085637 : Blo 1801602 6085637 := bbase (se 4 (by rfl) ⟨570528, by rfl⟩ : syracuseStep 6085637 = 1141057) (by norm_num)
theorem B1924133 : Blo 1801602 1924133 := bbase (se 4 (by rfl) ⟨180387, by rfl⟩ : syracuseStep 1924133 = 360775) (by norm_num)
theorem B3423293 : Blo 1801602 3423293 := bbase (se 3 (by rfl) ⟨641867, by rfl⟩ : syracuseStep 3423293 = 1283735) (by norm_num)
theorem B4627517 : Blo 1801602 4627517 := bbase (se 3 (by rfl) ⟨867659, by rfl⟩ : syracuseStep 4627517 = 1735319) (by norm_num)
theorem B2702405 : Blo 1801602 2702405 := bbase (se 4 (by rfl) ⟨253350, by rfl⟩ : syracuseStep 2702405 = 506701) (by norm_num)
theorem B4054085 : Blo 1801602 4054085 := bbase (se 4 (by rfl) ⟨380070, by rfl⟩ : syracuseStep 4054085 = 760141) (by norm_num)
theorem B2702429 : Blo 1801602 2702429 := bbase (se 3 (by rfl) ⟨506705, by rfl⟩ : syracuseStep 2702429 = 1013411) (by norm_num)
theorem B1924193 : Blo 1801602 1924193 := bbase (se 2 (by rfl) ⟨721572, by rfl⟩ : syracuseStep 1924193 = 1443145) (by norm_num)
theorem B4562021 : Blo 1801602 4562021 := bbase (se 4 (by rfl) ⟨427689, by rfl⟩ : syracuseStep 4562021 = 855379) (by norm_num)
theorem B2702453 : Blo 1801602 2702453 := bbase (se 5 (by rfl) ⟨126677, by rfl⟩ : syracuseStep 2702453 = 253355) (by norm_num)
theorem B2702477 : Blo 1801602 2702477 := bbase (se 3 (by rfl) ⟨506714, by rfl⟩ : syracuseStep 2702477 = 1013429) (by norm_num)
theorem B4054157 : Blo 1801602 4054157 := bbase (se 3 (by rfl) ⟨760154, by rfl⟩ : syracuseStep 4054157 = 1520309) (by norm_num)
theorem B2702501 : Blo 1801602 2702501 := bbase (se 4 (by rfl) ⟨253359, by rfl⟩ : syracuseStep 2702501 = 506719) (by norm_num)
theorem B2702525 : Blo 1801602 2702525 := bbase (se 3 (by rfl) ⟨506723, by rfl⟩ : syracuseStep 2702525 = 1013447) (by norm_num)
theorem B2702549 : Blo 1801602 2702549 := bbase (se 7 (by rfl) ⟨31670, by rfl⟩ : syracuseStep 2702549 = 63341) (by norm_num)
theorem B4054229 : Blo 1801602 4054229 := bbase (se 7 (by rfl) ⟨47510, by rfl⟩ : syracuseStep 4054229 = 95021) (by norm_num)
theorem B1924321 : Blo 1801602 1924321 := bbase (se 2 (by rfl) ⟨721620, by rfl⟩ : syracuseStep 1924321 = 1443241) (by norm_num)
theorem B2702573 : Blo 1801602 2702573 := bbase (se 3 (by rfl) ⟨506732, by rfl⟩ : syracuseStep 2702573 = 1013465) (by norm_num)
theorem B2702597 : Blo 1801602 2702597 := bbase (se 4 (by rfl) ⟨253368, by rfl⟩ : syracuseStep 2702597 = 506737) (by norm_num)
theorem B6495493 : Blo 1801602 6495493 := bbase (se 4 (by rfl) ⟨608952, by rfl⟩ : syracuseStep 6495493 = 1217905) (by norm_num)
theorem B8658197 : Blo 1801602 8658197 := bbase (se 6 (by rfl) ⟨202926, by rfl⟩ : syracuseStep 8658197 = 405853) (by norm_num)
theorem B2702621 : Blo 1801602 2702621 := bbase (se 3 (by rfl) ⟨506741, by rfl⟩ : syracuseStep 2702621 = 1013483) (by norm_num)
theorem B4054301 : Blo 1801602 4054301 := bbase (se 3 (by rfl) ⟨760181, by rfl⟩ : syracuseStep 4054301 = 1520363) (by norm_num)
theorem B2702645 : Blo 1801602 2702645 := bbase (se 5 (by rfl) ⟨126686, by rfl⟩ : syracuseStep 2702645 = 253373) (by norm_num)
theorem B5135669 : Blo 1801602 5135669 := bbase (se 5 (by rfl) ⟨240734, by rfl⟩ : syracuseStep 5135669 = 481469) (by norm_num)
theorem B2702669 : Blo 1801602 2702669 := bbase (se 3 (by rfl) ⟨506750, by rfl⟩ : syracuseStep 2702669 = 1013501) (by norm_num)
theorem B3849565 : Blo 1801602 3849565 := bbase (se 3 (by rfl) ⟨721793, by rfl⟩ : syracuseStep 3849565 = 1443587) (by norm_num)
theorem B2702693 : Blo 1801602 2702693 := bbase (se 4 (by rfl) ⟨253377, by rfl⟩ : syracuseStep 2702693 = 506755) (by norm_num)
theorem B4054373 : Blo 1801602 4054373 := bbase (se 4 (by rfl) ⟨380097, by rfl⟩ : syracuseStep 4054373 = 760195) (by norm_num)
theorem B6847861 : Blo 1801602 6847861 := bbase (se 5 (by rfl) ⟨320993, by rfl⟩ : syracuseStep 6847861 = 641987) (by norm_num)
theorem B2702717 : Blo 1801602 2702717 := bbase (se 3 (by rfl) ⟨506759, by rfl⟩ : syracuseStep 2702717 = 1013519) (by norm_num)
theorem B2702741 : Blo 1801602 2702741 := bbase (se 6 (by rfl) ⟨63345, by rfl⟩ : syracuseStep 2702741 = 126691) (by norm_num)
theorem B6495653 : Blo 1801602 6495653 := bbase (se 4 (by rfl) ⟨608967, by rfl⟩ : syracuseStep 6495653 = 1217935) (by norm_num)
theorem B2702765 : Blo 1801602 2702765 := bbase (se 3 (by rfl) ⟨506768, by rfl⟩ : syracuseStep 2702765 = 1013537) (by norm_num)
theorem B4054445 : Blo 1801602 4054445 := bbase (se 3 (by rfl) ⟨760208, by rfl⟩ : syracuseStep 4054445 = 1520417) (by norm_num)
theorem B6086069 : Blo 1801602 6086069 := bbase (se 5 (by rfl) ⟨285284, by rfl⟩ : syracuseStep 6086069 = 570569) (by norm_num)
theorem B4562365 : Blo 1801602 4562365 := bbase (se 3 (by rfl) ⟨855443, by rfl⟩ : syracuseStep 4562365 = 1710887) (by norm_num)
theorem B2702789 : Blo 1801602 2702789 := bbase (se 4 (by rfl) ⟨253386, by rfl⟩ : syracuseStep 2702789 = 506773) (by norm_num)
theorem B2702813 : Blo 1801602 2702813 := bbase (se 3 (by rfl) ⟨506777, by rfl⟩ : syracuseStep 2702813 = 1013555) (by norm_num)
theorem B2702837 : Blo 1801602 2702837 := bbase (se 5 (by rfl) ⟨126695, by rfl⟩ : syracuseStep 2702837 = 253391) (by norm_num)
theorem B4054517 : Blo 1801602 4054517 := bbase (se 5 (by rfl) ⟨190055, by rfl⟩ : syracuseStep 4054517 = 380111) (by norm_num)
theorem B2702861 : Blo 1801602 2702861 := bbase (se 3 (by rfl) ⟨506786, by rfl⟩ : syracuseStep 2702861 = 1013573) (by norm_num)
theorem B2702885 : Blo 1801602 2702885 := bbase (se 4 (by rfl) ⟨253395, by rfl⟩ : syracuseStep 2702885 = 506791) (by norm_num)
theorem B4562477 : Blo 1801602 4562477 := bbase (se 3 (by rfl) ⟨855464, by rfl⟩ : syracuseStep 4562477 = 1710929) (by norm_num)
theorem B2702909 : Blo 1801602 2702909 := bbase (se 3 (by rfl) ⟨506795, by rfl⟩ : syracuseStep 2702909 = 1013591) (by norm_num)
theorem B4054589 : Blo 1801602 4054589 := bbase (se 3 (by rfl) ⟨760235, by rfl⟩ : syracuseStep 4054589 = 1520471) (by norm_num)
theorem B25042517 : Blo 1801602 25042517 := bbase (se 8 (by rfl) ⟨146733, by rfl⟩ : syracuseStep 25042517 = 293467) (by norm_num)
theorem B2702933 : Blo 1801602 2702933 := bbase (se 8 (by rfl) ⟨15837, by rfl⟩ : syracuseStep 2702933 = 31675) (by norm_num)
theorem B2702957 : Blo 1801602 2702957 := bbase (se 3 (by rfl) ⟨506804, by rfl⟩ : syracuseStep 2702957 = 1013609) (by norm_num)
theorem B2702981 : Blo 1801602 2702981 := bbase (se 4 (by rfl) ⟨253404, by rfl⟩ : syracuseStep 2702981 = 506809) (by norm_num)
theorem B4054661 : Blo 1801602 4054661 := bbase (se 4 (by rfl) ⟨380124, by rfl⟩ : syracuseStep 4054661 = 760249) (by norm_num)
theorem B2703005 : Blo 1801602 2703005 := bbase (se 3 (by rfl) ⟨506813, by rfl⟩ : syracuseStep 2703005 = 1013627) (by norm_num)
theorem B1924765 : Blo 1801602 1924765 := bbase (se 3 (by rfl) ⟨360893, by rfl⟩ : syracuseStep 1924765 = 721787) (by norm_num)
theorem B5775013 : Blo 1801602 5775013 := bbase (se 4 (by rfl) ⟨541407, by rfl⟩ : syracuseStep 5775013 = 1082815) (by norm_num)
theorem B9379493 : Blo 1801602 9379493 := bbase (se 4 (by rfl) ⟨879327, by rfl⟩ : syracuseStep 9379493 = 1758655) (by norm_num)
theorem B2703029 : Blo 1801602 2703029 := bbase (se 5 (by rfl) ⟨126704, by rfl⟩ : syracuseStep 2703029 = 253409) (by norm_num)
theorem B2703053 : Blo 1801602 2703053 := bbase (se 3 (by rfl) ⟨506822, by rfl⟩ : syracuseStep 2703053 = 1013645) (by norm_num)
theorem B4054733 : Blo 1801602 4054733 := bbase (se 3 (by rfl) ⟨760262, by rfl⟩ : syracuseStep 4054733 = 1520525) (by norm_num)
theorem B2703077 : Blo 1801602 2703077 := bbase (se 4 (by rfl) ⟨253413, by rfl⟩ : syracuseStep 2703077 = 506827) (by norm_num)
theorem B4562669 : Blo 1801602 4562669 := bbase (se 3 (by rfl) ⟨855500, by rfl⟩ : syracuseStep 4562669 = 1711001) (by norm_num)
theorem B9125621 : Blo 1801602 9125621 := bbase (se 5 (by rfl) ⟨427763, by rfl⟩ : syracuseStep 9125621 = 855527) (by norm_num)
theorem B4112117 : Blo 1801602 4112117 := bbase (se 5 (by rfl) ⟨192755, by rfl⟩ : syracuseStep 4112117 = 385511) (by norm_num)
theorem B2703101 : Blo 1801602 2703101 := bbase (se 3 (by rfl) ⟨506831, by rfl⟩ : syracuseStep 2703101 = 1013663) (by norm_num)
theorem B2703125 : Blo 1801602 2703125 := bbase (se 6 (by rfl) ⟨63354, by rfl⟩ : syracuseStep 2703125 = 126709) (by norm_num)
theorem B4054805 : Blo 1801602 4054805 := bbase (se 6 (by rfl) ⟨95034, by rfl⟩ : syracuseStep 4054805 = 190069) (by norm_num)
theorem B1924885 : Blo 1801602 1924885 := bbase (se 6 (by rfl) ⟨45114, by rfl⟩ : syracuseStep 1924885 = 90229) (by norm_num)
theorem B2703149 : Blo 1801602 2703149 := bbase (se 3 (by rfl) ⟨506840, by rfl⟩ : syracuseStep 2703149 = 1013681) (by norm_num)
theorem B2703173 : Blo 1801602 2703173 := bbase (se 4 (by rfl) ⟨253422, by rfl⟩ : syracuseStep 2703173 = 506845) (by norm_num)
theorem B4874053 : Blo 1801602 4874053 := bbase (se 4 (by rfl) ⟨456942, by rfl⟩ : syracuseStep 4874053 = 913885) (by norm_num)
theorem B2703197 : Blo 1801602 2703197 := bbase (se 3 (by rfl) ⟨506849, by rfl⟩ : syracuseStep 2703197 = 1013699) (by norm_num)
theorem B4054877 : Blo 1801602 4054877 := bbase (se 3 (by rfl) ⟨760289, by rfl⟩ : syracuseStep 4054877 = 1520579) (by norm_num)
theorem B6086501 : Blo 1801602 6086501 := bbase (se 4 (by rfl) ⟨570609, by rfl⟩ : syracuseStep 6086501 = 1141219) (by norm_num)
theorem B2703221 : Blo 1801602 2703221 := bbase (se 5 (by rfl) ⟨126713, by rfl⟩ : syracuseStep 2703221 = 253427) (by norm_num)
theorem B2703245 : Blo 1801602 2703245 := bbase (se 3 (by rfl) ⟨506858, by rfl⟩ : syracuseStep 2703245 = 1013717) (by norm_num)
theorem B2703269 : Blo 1801602 2703269 := bbase (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) (by norm_num)
theorem B4054949 : Blo 1801602 4054949 := bbase (se 4 (by rfl) ⟨380151, by rfl⟩ : syracuseStep 4054949 = 760303) (by norm_num)
theorem B2703293 : Blo 1801602 2703293 := bbase (se 3 (by rfl) ⟨506867, by rfl⟩ : syracuseStep 2703293 = 1013735) (by norm_num)
theorem B2703317 : Blo 1801602 2703317 := bbase (se 7 (by rfl) ⟨31679, by rfl⟩ : syracuseStep 2703317 = 63359) (by norm_num)
theorem B14622677 : Blo 1801602 14622677 := bbase (se 7 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 14622677 = 342719) (by norm_num)
theorem B2703341 : Blo 1801602 2703341 := bbase (se 3 (by rfl) ⟨506876, by rfl⟩ : syracuseStep 2703341 = 1013753) (by norm_num)
theorem B4055021 : Blo 1801602 4055021 := bbase (se 3 (by rfl) ⟨760316, by rfl⟩ : syracuseStep 4055021 = 1520633) (by norm_num)
theorem B2056177 : Blo 1801602 2056177 := bbase (se 2 (by rfl) ⟨771066, by rfl⟩ : syracuseStep 2056177 = 1542133) (by norm_num)
theorem B1802243 : Blo 1801602 1802243 := bstep (se 1 (by rfl) ⟨1351682, by rfl⟩ : syracuseStep 1802243 = 2703365) B2703365
theorem B4055057 : Blo 1801602 4055057 := bstep (se 2 (by rfl) ⟨1520646, by rfl⟩ : syracuseStep 4055057 = 3041293) B3041293
theorem B2703377 : Blo 1801602 2703377 := bstep (se 2 (by rfl) ⟨1013766, by rfl⟩ : syracuseStep 2703377 = 2027533) B2027533
theorem B1802259 : Blo 1801602 1802259 := bstep (se 1 (by rfl) ⟨1351694, by rfl⟩ : syracuseStep 1802259 = 2703389) B2703389
theorem B4055075 : Blo 1801602 4055075 := bstep (se 1 (by rfl) ⟨3041306, by rfl⟩ : syracuseStep 4055075 = 6082613) B6082613
theorem B2703395 : Blo 1801602 2703395 := bstep (se 1 (by rfl) ⟨2027546, by rfl⟩ : syracuseStep 2703395 = 4055093) B4055093
theorem B1802275 : Blo 1801602 1802275 := bstep (se 1 (by rfl) ⟨1351706, by rfl⟩ : syracuseStep 1802275 = 2703413) B2703413
theorem B4562993 : Blo 1801602 4562993 := bstep (se 2 (by rfl) ⟨1711122, by rfl⟩ : syracuseStep 4562993 = 3422245) B3422245
theorem B1802291 : Blo 1801602 1802291 := bstep (se 1 (by rfl) ⟨1351718, by rfl⟩ : syracuseStep 1802291 = 2703437) B2703437
theorem B2703425 : Blo 1801602 2703425 := bstep (se 2 (by rfl) ⟨1013784, by rfl⟩ : syracuseStep 2703425 = 2027569) B2027569
theorem B1802307 : Blo 1801602 1802307 := bstep (se 1 (by rfl) ⟨1351730, by rfl⟩ : syracuseStep 1802307 = 2703461) B2703461
theorem B2703443 : Blo 1801602 2703443 := bstep (se 1 (by rfl) ⟨2027582, by rfl⟩ : syracuseStep 2703443 = 4055165) B4055165
theorem B1802323 : Blo 1801602 1802323 := bstep (se 1 (by rfl) ⟨1351742, by rfl⟩ : syracuseStep 1802323 = 2703485) B2703485
theorem B1802339 : Blo 1801602 1802339 := bstep (se 1 (by rfl) ⟨1351754, by rfl⟩ : syracuseStep 1802339 = 2703509) B2703509
theorem B24658033 : Blo 1801602 24658033 := bstep (se 2 (by rfl) ⟨9246762, by rfl⟩ : syracuseStep 24658033 = 18493525) B18493525
theorem B2703473 : Blo 1801602 2703473 := bstep (se 2 (by rfl) ⟨1013802, by rfl⟩ : syracuseStep 2703473 = 2027605) B2027605
theorem B1802355 : Blo 1801602 1802355 := bstep (se 1 (by rfl) ⟨1351766, by rfl⟩ : syracuseStep 1802355 = 2703533) B2703533
theorem B2703491 : Blo 1801602 2703491 := bstep (se 1 (by rfl) ⟨2027618, by rfl⟩ : syracuseStep 2703491 = 4055237) B4055237
theorem B1802371 : Blo 1801602 1802371 := bstep (se 1 (by rfl) ⟨1351778, by rfl⟩ : syracuseStep 1802371 = 2703557) B2703557
theorem B9748621 : Blo 1801602 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B1802387 : Blo 1801602 1802387 := bstep (se 1 (by rfl) ⟨1351790, by rfl⟩ : syracuseStep 1802387 = 2703581) B2703581
theorem B2703521 : Blo 1801602 2703521 := bstep (se 2 (by rfl) ⟨1013820, by rfl⟩ : syracuseStep 2703521 = 2027641) B2027641
theorem B1802403 : Blo 1801602 1802403 := bstep (se 1 (by rfl) ⟨1351802, by rfl⟩ : syracuseStep 1802403 = 2703605) B2703605
theorem B2703539 : Blo 1801602 2703539 := bstep (se 1 (by rfl) ⟨2027654, by rfl⟩ : syracuseStep 2703539 = 4055309) B4055309
theorem B1802419 : Blo 1801602 1802419 := bstep (se 1 (by rfl) ⟨1351814, by rfl⟩ : syracuseStep 1802419 = 2703629) B2703629
theorem B1802435 : Blo 1801602 1802435 := bstep (se 1 (by rfl) ⟨1351826, by rfl⟩ : syracuseStep 1802435 = 2703653) B2703653
theorem B2703569 : Blo 1801602 2703569 := bstep (se 2 (by rfl) ⟨1013838, by rfl⟩ : syracuseStep 2703569 = 2027677) B2027677
theorem B1802451 : Blo 1801602 1802451 := bstep (se 1 (by rfl) ⟨1351838, by rfl⟩ : syracuseStep 1802451 = 2703677) B2703677
theorem B2703587 : Blo 1801602 2703587 := bstep (se 1 (by rfl) ⟨2027690, by rfl⟩ : syracuseStep 2703587 = 4055381) B4055381
theorem B1802467 : Blo 1801602 1802467 := bstep (se 1 (by rfl) ⟨1351850, by rfl⟩ : syracuseStep 1802467 = 2703701) B2703701
theorem B1802483 : Blo 1801602 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B2703617 : Blo 1801602 2703617 := bstep (se 2 (by rfl) ⟨1013856, by rfl⟩ : syracuseStep 2703617 = 2027713) B2027713
theorem B1802499 : Blo 1801602 1802499 := bstep (se 1 (by rfl) ⟨1351874, by rfl⟩ : syracuseStep 1802499 = 2703749) B2703749
theorem B2703635 : Blo 1801602 2703635 := bstep (se 1 (by rfl) ⟨2027726, by rfl⟩ : syracuseStep 2703635 = 4055453) B4055453
theorem B1802515 : Blo 1801602 1802515 := bstep (se 1 (by rfl) ⟨1351886, by rfl⟩ : syracuseStep 1802515 = 2703773) B2703773
theorem B1802531 : Blo 1801602 1802531 := bstep (se 1 (by rfl) ⟨1351898, by rfl⟩ : syracuseStep 1802531 = 2703797) B2703797
theorem B4055345 : Blo 1801602 4055345 := bstep (se 2 (by rfl) ⟨1520754, by rfl⟩ : syracuseStep 4055345 = 3041509) B3041509
theorem B2703665 : Blo 1801602 2703665 := bstep (se 2 (by rfl) ⟨1013874, by rfl⟩ : syracuseStep 2703665 = 2027749) B2027749
theorem B1802547 : Blo 1801602 1802547 := bstep (se 1 (by rfl) ⟨1351910, by rfl⟩ : syracuseStep 1802547 = 2703821) B2703821
theorem B4055363 : Blo 1801602 4055363 := bstep (se 1 (by rfl) ⟨3041522, by rfl⟩ : syracuseStep 4055363 = 6083045) B6083045
theorem B2703683 : Blo 1801602 2703683 := bstep (se 1 (by rfl) ⟨2027762, by rfl⟩ : syracuseStep 2703683 = 4055525) B4055525
theorem B1802563 : Blo 1801602 1802563 := bstep (se 1 (by rfl) ⟨1351922, by rfl⟩ : syracuseStep 1802563 = 2703845) B2703845
theorem B1802579 : Blo 1801602 1802579 := bstep (se 1 (by rfl) ⟨1351934, by rfl⟩ : syracuseStep 1802579 = 2703869) B2703869
theorem B2703713 : Blo 1801602 2703713 := bstep (se 2 (by rfl) ⟨1013892, by rfl⟩ : syracuseStep 2703713 = 2027785) B2027785
theorem B1802595 : Blo 1801602 1802595 := bstep (se 1 (by rfl) ⟨1351946, by rfl⟩ : syracuseStep 1802595 = 2703893) B2703893
theorem B2703731 : Blo 1801602 2703731 := bstep (se 1 (by rfl) ⟨2027798, by rfl⟩ : syracuseStep 2703731 = 4055597) B4055597
theorem B1802611 : Blo 1801602 1802611 := bstep (se 1 (by rfl) ⟨1351958, by rfl⟩ : syracuseStep 1802611 = 2703917) B2703917
theorem B1802627 : Blo 1801602 1802627 := bstep (se 1 (by rfl) ⟨1351970, by rfl⟩ : syracuseStep 1802627 = 2703941) B2703941
theorem B2703761 : Blo 1801602 2703761 := bstep (se 2 (by rfl) ⟨1013910, by rfl⟩ : syracuseStep 2703761 = 2027821) B2027821
theorem B1802643 : Blo 1801602 1802643 := bstep (se 1 (by rfl) ⟨1351982, by rfl⟩ : syracuseStep 1802643 = 2703965) B2703965
theorem B9249187 : Blo 1801602 9249187 := bstep (se 1 (by rfl) ⟨6936890, by rfl⟩ : syracuseStep 9249187 = 13873781) B13873781
theorem B2703779 : Blo 1801602 2703779 := bstep (se 1 (by rfl) ⟨2027834, by rfl⟩ : syracuseStep 2703779 = 4055669) B4055669
theorem B1802659 : Blo 1801602 1802659 := bstep (se 1 (by rfl) ⟨1351994, by rfl⟩ : syracuseStep 1802659 = 2703989) B2703989
theorem B1802675 : Blo 1801602 1802675 := bstep (se 1 (by rfl) ⟨1352006, by rfl⟩ : syracuseStep 1802675 = 2704013) B2704013
theorem B2703809 : Blo 1801602 2703809 := bstep (se 2 (by rfl) ⟨1013928, by rfl⟩ : syracuseStep 2703809 = 2027857) B2027857
theorem B1802691 : Blo 1801602 1802691 := bstep (se 1 (by rfl) ⟨1352018, by rfl⟩ : syracuseStep 1802691 = 2704037) B2704037
theorem B38986181 : Blo 1801602 38986181 := bstep (se 4 (by rfl) ⟨3654954, by rfl⟩ : syracuseStep 38986181 = 7309909) B7309909
theorem B2703827 : Blo 1801602 2703827 := bstep (se 1 (by rfl) ⟨2027870, by rfl⟩ : syracuseStep 2703827 = 4055741) B4055741
theorem B1827283 : Blo 1801602 1827283 := bstep (se 1 (by rfl) ⟨1370462, by rfl⟩ : syracuseStep 1827283 = 2740925) B2740925
theorem B1802707 : Blo 1801602 1802707 := bstep (se 1 (by rfl) ⟨1352030, by rfl⟩ : syracuseStep 1802707 = 2704061) B2704061
theorem B1802723 : Blo 1801602 1802723 := bstep (se 1 (by rfl) ⟨1352042, by rfl⟩ : syracuseStep 1802723 = 2704085) B2704085
theorem B6087149 : Blo 1801602 6087149 := bstep (se 3 (by rfl) ⟨1141340, by rfl⟩ : syracuseStep 6087149 = 2282681) B2282681
theorem B2703857 : Blo 1801602 2703857 := bstep (se 2 (by rfl) ⟨1013946, by rfl⟩ : syracuseStep 2703857 = 2027893) B2027893
theorem B1802739 : Blo 1801602 1802739 := bstep (se 1 (by rfl) ⟨1352054, by rfl⟩ : syracuseStep 1802739 = 2704109) B2704109
theorem B2703875 : Blo 1801602 2703875 := bstep (se 1 (by rfl) ⟨2027906, by rfl⟩ : syracuseStep 2703875 = 4055813) B4055813
theorem B1802755 : Blo 1801602 1802755 := bstep (se 1 (by rfl) ⟨1352066, by rfl⟩ : syracuseStep 1802755 = 2704133) B2704133
theorem B6840845 : Blo 1801602 6840845 := bstep (se 3 (by rfl) ⟨1282658, by rfl⟩ : syracuseStep 6840845 = 2565317) B2565317
theorem B1802771 : Blo 1801602 1802771 := bstep (se 1 (by rfl) ⟨1352078, by rfl⟩ : syracuseStep 1802771 = 2704157) B2704157
theorem B2703905 : Blo 1801602 2703905 := bstep (se 2 (by rfl) ⟨1013964, by rfl⟩ : syracuseStep 2703905 = 2027929) B2027929
theorem B1802787 : Blo 1801602 1802787 := bstep (se 1 (by rfl) ⟨1352090, by rfl⟩ : syracuseStep 1802787 = 2704181) B2704181
theorem B2703923 : Blo 1801602 2703923 := bstep (se 1 (by rfl) ⟨2027942, by rfl⟩ : syracuseStep 2703923 = 4055885) B4055885
theorem B1802803 : Blo 1801602 1802803 := bstep (se 1 (by rfl) ⟨1352102, by rfl⟩ : syracuseStep 1802803 = 2704205) B2704205
theorem B1802819 : Blo 1801602 1802819 := bstep (se 1 (by rfl) ⟨1352114, by rfl⟩ : syracuseStep 1802819 = 2704229) B2704229
theorem B2777681 : Blo 1801602 2777681 := bstep (se 2 (by rfl) ⟨1041630, by rfl⟩ : syracuseStep 2777681 = 2083261) B2083261
theorem B4055633 : Blo 1801602 4055633 := bstep (se 2 (by rfl) ⟨1520862, by rfl⟩ : syracuseStep 4055633 = 3041725) B3041725
theorem B2703953 : Blo 1801602 2703953 := bstep (se 2 (by rfl) ⟨1013982, by rfl⟩ : syracuseStep 2703953 = 2027965) B2027965
theorem B1802835 : Blo 1801602 1802835 := bstep (se 1 (by rfl) ⟨1352126, by rfl⟩ : syracuseStep 1802835 = 2704253) B2704253
theorem B4055651 : Blo 1801602 4055651 := bstep (se 1 (by rfl) ⟨3041738, by rfl⟩ : syracuseStep 4055651 = 6083477) B6083477
theorem B2703971 : Blo 1801602 2703971 := bstep (se 1 (by rfl) ⟨2027978, by rfl⟩ : syracuseStep 2703971 = 4055957) B4055957
theorem B1802851 : Blo 1801602 1802851 := bstep (se 1 (by rfl) ⟨1352138, by rfl⟩ : syracuseStep 1802851 = 2704277) B2704277
theorem B1925731 : Blo 1801602 1925731 := bstep (se 1 (by rfl) ⟨1444298, by rfl⟩ : syracuseStep 1925731 = 2888597) B2888597
theorem B14615153 : Blo 1801602 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B1802867 : Blo 1801602 1802867 := bstep (se 1 (by rfl) ⟨1352150, by rfl⟩ : syracuseStep 1802867 = 2704301) B2704301
theorem B2704001 : Blo 1801602 2704001 := bstep (se 2 (by rfl) ⟨1014000, by rfl⟩ : syracuseStep 2704001 = 2028001) B2028001
theorem B1802883 : Blo 1801602 1802883 := bstep (se 1 (by rfl) ⟨1352162, by rfl⟩ : syracuseStep 1802883 = 2704325) B2704325
theorem B3850897 : Blo 1801602 3850897 := bstep (se 2 (by rfl) ⟨1444086, by rfl⟩ : syracuseStep 3850897 = 2888173) B2888173
theorem B2704019 : Blo 1801602 2704019 := bstep (se 1 (by rfl) ⟨2028014, by rfl⟩ : syracuseStep 2704019 = 4056029) B4056029
theorem B1802899 : Blo 1801602 1802899 := bstep (se 1 (by rfl) ⟨1352174, by rfl⟩ : syracuseStep 1802899 = 2704349) B2704349
theorem B1802915 : Blo 1801602 1802915 := bstep (se 1 (by rfl) ⟨1352186, by rfl⟩ : syracuseStep 1802915 = 2704373) B2704373
theorem B3850915 : Blo 1801602 3850915 := bstep (se 1 (by rfl) ⟨2888186, by rfl⟩ : syracuseStep 3850915 = 5776373) B5776373
theorem B2704049 : Blo 1801602 2704049 := bstep (se 2 (by rfl) ⟨1014018, by rfl⟩ : syracuseStep 2704049 = 2028037) B2028037
theorem B1802931 : Blo 1801602 1802931 := bstep (se 1 (by rfl) ⟨1352198, by rfl⟩ : syracuseStep 1802931 = 2704397) B2704397
theorem B2704067 : Blo 1801602 2704067 := bstep (se 1 (by rfl) ⟨2028050, by rfl⟩ : syracuseStep 2704067 = 4056101) B4056101
theorem B1802947 : Blo 1801602 1802947 := bstep (se 1 (by rfl) ⟨1352210, by rfl⟩ : syracuseStep 1802947 = 2704421) B2704421
theorem B1802963 : Blo 1801602 1802963 := bstep (se 1 (by rfl) ⟨1352222, by rfl⟩ : syracuseStep 1802963 = 2704445) B2704445
theorem B2704097 : Blo 1801602 2704097 := bstep (se 2 (by rfl) ⟨1014036, by rfl⟩ : syracuseStep 2704097 = 2028073) B2028073
theorem B1802979 : Blo 1801602 1802979 := bstep (se 1 (by rfl) ⟨1352234, by rfl⟩ : syracuseStep 1802979 = 2704469) B2704469
theorem B2704115 : Blo 1801602 2704115 := bstep (se 1 (by rfl) ⟨2028086, by rfl⟩ : syracuseStep 2704115 = 4056173) B4056173
theorem B1802995 : Blo 1801602 1802995 := bstep (se 1 (by rfl) ⟨1352246, by rfl⟩ : syracuseStep 1802995 = 2704493) B2704493
theorem B1803011 : Blo 1801602 1803011 := bstep (se 1 (by rfl) ⟨1352258, by rfl⟩ : syracuseStep 1803011 = 2704517) B2704517
theorem B2704145 : Blo 1801602 2704145 := bstep (se 2 (by rfl) ⟨1014054, by rfl⟩ : syracuseStep 2704145 = 2028109) B2028109
theorem B1803027 : Blo 1801602 1803027 := bstep (se 1 (by rfl) ⟨1352270, by rfl⟩ : syracuseStep 1803027 = 2704541) B2704541
theorem B2704163 : Blo 1801602 2704163 := bstep (se 1 (by rfl) ⟨2028122, by rfl⟩ : syracuseStep 2704163 = 4056245) B4056245
theorem B1803043 : Blo 1801602 1803043 := bstep (se 1 (by rfl) ⟨1352282, by rfl⟩ : syracuseStep 1803043 = 2704565) B2704565
theorem B1803059 : Blo 1801602 1803059 := bstep (se 1 (by rfl) ⟨1352294, by rfl⟩ : syracuseStep 1803059 = 2704589) B2704589
theorem B2704193 : Blo 1801602 2704193 := bstep (se 2 (by rfl) ⟨1014072, by rfl⟩ : syracuseStep 2704193 = 2028145) B2028145
theorem B1803075 : Blo 1801602 1803075 := bstep (se 1 (by rfl) ⟨1352306, by rfl⟩ : syracuseStep 1803075 = 2704613) B2704613
theorem B10265413 : Blo 1801602 10265413 := bstep (se 4 (by rfl) ⟨962382, by rfl⟩ : syracuseStep 10265413 = 1924765) B1924765
theorem B2704211 : Blo 1801602 2704211 := bstep (se 1 (by rfl) ⟨2028158, by rfl⟩ : syracuseStep 2704211 = 4056317) B4056317
theorem B1803091 : Blo 1801602 1803091 := bstep (se 1 (by rfl) ⟨1352318, by rfl⟩ : syracuseStep 1803091 = 2704637) B2704637
theorem B9126755 : Blo 1801602 9126755 := bstep (se 1 (by rfl) ⟨6845066, by rfl⟩ : syracuseStep 9126755 = 13690133) B13690133
theorem B1803107 : Blo 1801602 1803107 := bstep (se 1 (by rfl) ⟨1352330, by rfl⟩ : syracuseStep 1803107 = 2704661) B2704661
theorem B4055921 : Blo 1801602 4055921 := bstep (se 2 (by rfl) ⟨1520970, by rfl⟩ : syracuseStep 4055921 = 3041941) B3041941
theorem B2704241 : Blo 1801602 2704241 := bstep (se 2 (by rfl) ⟨1014090, by rfl⟩ : syracuseStep 2704241 = 2028181) B2028181
theorem B1803123 : Blo 1801602 1803123 := bstep (se 1 (by rfl) ⟨1352342, by rfl⟩ : syracuseStep 1803123 = 2704685) B2704685
theorem B4055939 : Blo 1801602 4055939 := bstep (se 1 (by rfl) ⟨3041954, by rfl⟩ : syracuseStep 4055939 = 6083909) B6083909
theorem B2704259 : Blo 1801602 2704259 := bstep (se 1 (by rfl) ⟨2028194, by rfl⟩ : syracuseStep 2704259 = 4056389) B4056389
theorem B1803139 : Blo 1801602 1803139 := bstep (se 1 (by rfl) ⟨1352354, by rfl⟩ : syracuseStep 1803139 = 2704709) B2704709
theorem B5202829 : Blo 1801602 5202829 := bstep (se 3 (by rfl) ⟨975530, by rfl⟩ : syracuseStep 5202829 = 1951061) B1951061
theorem B1803155 : Blo 1801602 1803155 := bstep (se 1 (by rfl) ⟨1352366, by rfl⟩ : syracuseStep 1803155 = 2704733) B2704733
theorem B2704289 : Blo 1801602 2704289 := bstep (se 2 (by rfl) ⟨1014108, by rfl⟩ : syracuseStep 2704289 = 2028217) B2028217
theorem B1803171 : Blo 1801602 1803171 := bstep (se 1 (by rfl) ⟨1352378, by rfl⟩ : syracuseStep 1803171 = 2704757) B2704757
theorem B2704307 : Blo 1801602 2704307 := bstep (se 1 (by rfl) ⟨2028230, by rfl⟩ : syracuseStep 2704307 = 4056461) B4056461
theorem B1803187 : Blo 1801602 1803187 := bstep (se 1 (by rfl) ⟨1352390, by rfl⟩ : syracuseStep 1803187 = 2704781) B2704781
theorem B1803203 : Blo 1801602 1803203 := bstep (se 1 (by rfl) ⟨1352402, by rfl⟩ : syracuseStep 1803203 = 2704805) B2704805
theorem B14623685 : Blo 1801602 14623685 := bstep (se 4 (by rfl) ⟨1370970, by rfl⟩ : syracuseStep 14623685 = 2741941) B2741941
theorem B2704337 : Blo 1801602 2704337 := bstep (se 2 (by rfl) ⟨1014126, by rfl⟩ : syracuseStep 2704337 = 2028253) B2028253
theorem B1803219 : Blo 1801602 1803219 := bstep (se 1 (by rfl) ⟨1352414, by rfl⟩ : syracuseStep 1803219 = 2704829) B2704829
theorem B2704355 : Blo 1801602 2704355 := bstep (se 1 (by rfl) ⟨2028266, by rfl⟩ : syracuseStep 2704355 = 4056533) B4056533
theorem B1803235 : Blo 1801602 1803235 := bstep (se 1 (by rfl) ⟨1352426, by rfl⟩ : syracuseStep 1803235 = 2704853) B2704853
theorem B1803251 : Blo 1801602 1803251 := bstep (se 1 (by rfl) ⟨1352438, by rfl⟩ : syracuseStep 1803251 = 2704877) B2704877
theorem B2704385 : Blo 1801602 2704385 := bstep (se 2 (by rfl) ⟨1014144, by rfl⟩ : syracuseStep 2704385 = 2028289) B2028289
theorem B1803267 : Blo 1801602 1803267 := bstep (se 1 (by rfl) ⟨1352450, by rfl⟩ : syracuseStep 1803267 = 2704901) B2704901
theorem B4563985 : Blo 1801602 4563985 := bstep (se 2 (by rfl) ⟨1711494, by rfl⟩ : syracuseStep 4563985 = 3422989) B3422989
theorem B2704403 : Blo 1801602 2704403 := bstep (se 1 (by rfl) ⟨2028302, by rfl⟩ : syracuseStep 2704403 = 4056605) B4056605
theorem B1803283 : Blo 1801602 1803283 := bstep (se 1 (by rfl) ⟨1352462, by rfl⟩ : syracuseStep 1803283 = 2704925) B2704925
theorem B1803299 : Blo 1801602 1803299 := bstep (se 1 (by rfl) ⟨1352474, by rfl⟩ : syracuseStep 1803299 = 2704949) B2704949
theorem B2704433 : Blo 1801602 2704433 := bstep (se 2 (by rfl) ⟨1014162, by rfl⟩ : syracuseStep 2704433 = 2028325) B2028325
theorem B1803315 : Blo 1801602 1803315 := bstep (se 1 (by rfl) ⟨1352486, by rfl⟩ : syracuseStep 1803315 = 2704973) B2704973
theorem B3040321 : Blo 1801602 3040321 := bstep (se 2 (by rfl) ⟨1140120, by rfl⟩ : syracuseStep 3040321 = 2280241) B2280241
theorem B2704451 : Blo 1801602 2704451 := bstep (se 1 (by rfl) ⟨2028338, by rfl⟩ : syracuseStep 2704451 = 4056677) B4056677
theorem B1803331 : Blo 1801602 1803331 := bstep (se 1 (by rfl) ⟨1352498, by rfl⟩ : syracuseStep 1803331 = 2704997) B2704997
theorem B1803347 : Blo 1801602 1803347 := bstep (se 1 (by rfl) ⟨1352510, by rfl⟩ : syracuseStep 1803347 = 2705021) B2705021
theorem B2704481 : Blo 1801602 2704481 := bstep (se 2 (by rfl) ⟨1014180, by rfl⟩ : syracuseStep 2704481 = 2028361) B2028361
theorem B3040355 : Blo 1801602 3040355 := bstep (se 1 (by rfl) ⟨2280266, by rfl⟩ : syracuseStep 3040355 = 4560533) B4560533
theorem B1803363 : Blo 1801602 1803363 := bstep (se 1 (by rfl) ⟨1352522, by rfl⟩ : syracuseStep 1803363 = 2705045) B2705045
theorem B2704499 : Blo 1801602 2704499 := bstep (se 1 (by rfl) ⟨2028374, by rfl⟩ : syracuseStep 2704499 = 4056749) B4056749
theorem B1803379 : Blo 1801602 1803379 := bstep (se 1 (by rfl) ⟨1352534, by rfl⟩ : syracuseStep 1803379 = 2705069) B2705069
theorem B1803395 : Blo 1801602 1803395 := bstep (se 1 (by rfl) ⟨1352546, by rfl⟩ : syracuseStep 1803395 = 2705093) B2705093
theorem B4056209 : Blo 1801602 4056209 := bstep (se 2 (by rfl) ⟨1521078, by rfl⟩ : syracuseStep 4056209 = 3042157) B3042157
theorem B2704529 : Blo 1801602 2704529 := bstep (se 2 (by rfl) ⟨1014198, by rfl⟩ : syracuseStep 2704529 = 2028397) B2028397
theorem B1803411 : Blo 1801602 1803411 := bstep (se 1 (by rfl) ⟨1352558, by rfl⟩ : syracuseStep 1803411 = 2705117) B2705117
theorem B2565283 : Blo 1801602 2565283 := bstep (se 1 (by rfl) ⟨1923962, by rfl⟩ : syracuseStep 2565283 = 3847925) B3847925
theorem B4056227 : Blo 1801602 4056227 := bstep (se 1 (by rfl) ⟨3042170, by rfl⟩ : syracuseStep 4056227 = 6084341) B6084341
theorem B2704547 : Blo 1801602 2704547 := bstep (se 1 (by rfl) ⟨2028410, by rfl⟩ : syracuseStep 2704547 = 4056821) B4056821
theorem B1803427 : Blo 1801602 1803427 := bstep (se 1 (by rfl) ⟨1352570, by rfl⟩ : syracuseStep 1803427 = 2705141) B2705141
theorem B1803443 : Blo 1801602 1803443 := bstep (se 1 (by rfl) ⟨1352582, by rfl⟩ : syracuseStep 1803443 = 2705165) B2705165
theorem B2704577 : Blo 1801602 2704577 := bstep (se 2 (by rfl) ⟨1014216, by rfl⟩ : syracuseStep 2704577 = 2028433) B2028433
theorem B1803459 : Blo 1801602 1803459 := bstep (se 1 (by rfl) ⟨1352594, by rfl⟩ : syracuseStep 1803459 = 2705189) B2705189
theorem B2704595 : Blo 1801602 2704595 := bstep (se 1 (by rfl) ⟨2028446, by rfl⟩ : syracuseStep 2704595 = 4056893) B4056893
theorem B1803475 : Blo 1801602 1803475 := bstep (se 1 (by rfl) ⟨1352606, by rfl⟩ : syracuseStep 1803475 = 2705213) B2705213
theorem B3040483 : Blo 1801602 3040483 := bstep (se 1 (by rfl) ⟨2280362, by rfl⟩ : syracuseStep 3040483 = 4560725) B4560725
theorem B1803491 : Blo 1801602 1803491 := bstep (se 1 (by rfl) ⟨1352618, by rfl⟩ : syracuseStep 1803491 = 2705237) B2705237
theorem B2704625 : Blo 1801602 2704625 := bstep (se 2 (by rfl) ⟨1014234, by rfl⟩ : syracuseStep 2704625 = 2028469) B2028469
theorem B1803507 : Blo 1801602 1803507 := bstep (se 1 (by rfl) ⟨1352630, by rfl⟩ : syracuseStep 1803507 = 2705261) B2705261
theorem B2704643 : Blo 1801602 2704643 := bstep (se 1 (by rfl) ⟨2028482, by rfl⟩ : syracuseStep 2704643 = 4056965) B4056965
theorem B1803523 : Blo 1801602 1803523 := bstep (se 1 (by rfl) ⟨1352642, by rfl⟩ : syracuseStep 1803523 = 2705285) B2705285
theorem B1803539 : Blo 1801602 1803539 := bstep (se 1 (by rfl) ⟨1352654, by rfl⟩ : syracuseStep 1803539 = 2705309) B2705309
theorem B2704673 : Blo 1801602 2704673 := bstep (se 2 (by rfl) ⟨1014252, by rfl⟩ : syracuseStep 2704673 = 2028505) B2028505
theorem B4564259 : Blo 1801602 4564259 := bstep (se 1 (by rfl) ⟨3423194, by rfl⟩ : syracuseStep 4564259 = 6846389) B6846389
theorem B1803555 : Blo 1801602 1803555 := bstep (se 1 (by rfl) ⟨1352666, by rfl⟩ : syracuseStep 1803555 = 2705333) B2705333
theorem B9741617 : Blo 1801602 9741617 := bstep (se 2 (by rfl) ⟨3653106, by rfl⟩ : syracuseStep 9741617 = 7306213) B7306213
theorem B2704691 : Blo 1801602 2704691 := bstep (se 1 (by rfl) ⟨2028518, by rfl⟩ : syracuseStep 2704691 = 4057037) B4057037
theorem B1803571 : Blo 1801602 1803571 := bstep (se 1 (by rfl) ⟨1352678, by rfl⟩ : syracuseStep 1803571 = 2705357) B2705357
theorem B1803587 : Blo 1801602 1803587 := bstep (se 1 (by rfl) ⟨1352690, by rfl⟩ : syracuseStep 1803587 = 2705381) B2705381
theorem B2704721 : Blo 1801602 2704721 := bstep (se 2 (by rfl) ⟨1014270, by rfl⟩ : syracuseStep 2704721 = 2028541) B2028541
theorem B2704739 : Blo 1801602 2704739 := bstep (se 1 (by rfl) ⟨2028554, by rfl⟩ : syracuseStep 2704739 = 4057109) B4057109
theorem B3040625 : Blo 1801602 3040625 := bstep (se 2 (by rfl) ⟨1140234, by rfl⟩ : syracuseStep 3040625 = 2280469) B2280469
theorem B2704769 : Blo 1801602 2704769 := bstep (se 2 (by rfl) ⟨1014288, by rfl⟩ : syracuseStep 2704769 = 2028577) B2028577
theorem B2704787 : Blo 1801602 2704787 := bstep (se 1 (by rfl) ⟨2028590, by rfl⟩ : syracuseStep 2704787 = 4057181) B4057181
theorem B4056497 : Blo 1801602 4056497 := bstep (se 2 (by rfl) ⟨1521186, by rfl⟩ : syracuseStep 4056497 = 3042373) B3042373
theorem B2704817 : Blo 1801602 2704817 := bstep (se 2 (by rfl) ⟨1014306, by rfl⟩ : syracuseStep 2704817 = 2028613) B2028613
theorem B4056515 : Blo 1801602 4056515 := bstep (se 1 (by rfl) ⟨3042386, by rfl⟩ : syracuseStep 4056515 = 6084773) B6084773
theorem B2704835 : Blo 1801602 2704835 := bstep (se 1 (by rfl) ⟨2028626, by rfl⟩ : syracuseStep 2704835 = 4057253) B4057253
theorem B2704865 : Blo 1801602 2704865 := bstep (se 2 (by rfl) ⟨1014324, by rfl⟩ : syracuseStep 2704865 = 2028649) B2028649
theorem B4564451 : Blo 1801602 4564451 := bstep (se 1 (by rfl) ⟨3423338, by rfl⟩ : syracuseStep 4564451 = 6846677) B6846677
theorem B3040753 : Blo 1801602 3040753 := bstep (se 2 (by rfl) ⟨1140282, by rfl⟩ : syracuseStep 3040753 = 2280565) B2280565
theorem B2704883 : Blo 1801602 2704883 := bstep (se 1 (by rfl) ⟨2028662, by rfl⟩ : syracuseStep 2704883 = 4057325) B4057325
theorem B2704913 : Blo 1801602 2704913 := bstep (se 2 (by rfl) ⟨1014342, by rfl⟩ : syracuseStep 2704913 = 2028685) B2028685
theorem B3040787 : Blo 1801602 3040787 := bstep (se 1 (by rfl) ⟨2280590, by rfl⟩ : syracuseStep 3040787 = 4561181) B4561181
theorem B2704931 : Blo 1801602 2704931 := bstep (se 1 (by rfl) ⟨2028698, by rfl⟩ : syracuseStep 2704931 = 4057397) B4057397
theorem B2704961 : Blo 1801602 2704961 := bstep (se 2 (by rfl) ⟨1014360, by rfl⟩ : syracuseStep 2704961 = 2028721) B2028721
theorem B2704979 : Blo 1801602 2704979 := bstep (se 1 (by rfl) ⟨2028734, by rfl⟩ : syracuseStep 2704979 = 4057469) B4057469
theorem B2705009 : Blo 1801602 2705009 := bstep (se 2 (by rfl) ⟨1014378, by rfl⟩ : syracuseStep 2705009 = 2028757) B2028757
theorem B2565761 : Blo 1801602 2565761 := bstep (se 2 (by rfl) ⟨962160, by rfl⟩ : syracuseStep 2565761 = 1924321) B1924321
theorem B2705027 : Blo 1801602 2705027 := bstep (se 1 (by rfl) ⟨2028770, by rfl⟩ : syracuseStep 2705027 = 4057541) B4057541
theorem B9127565 : Blo 1801602 9127565 := bstep (se 3 (by rfl) ⟨1711418, by rfl⟩ : syracuseStep 9127565 = 3422837) B3422837
theorem B3040915 : Blo 1801602 3040915 := bstep (se 1 (by rfl) ⟨2280686, by rfl⟩ : syracuseStep 3040915 = 4561373) B4561373
theorem B2705057 : Blo 1801602 2705057 := bstep (se 2 (by rfl) ⟨1014396, by rfl⟩ : syracuseStep 2705057 = 2028793) B2028793
theorem B8660657 : Blo 1801602 8660657 := bstep (se 2 (by rfl) ⟨3247746, by rfl⟩ : syracuseStep 8660657 = 6495493) B6495493
theorem B2705075 : Blo 1801602 2705075 := bstep (se 1 (by rfl) ⟨2028806, by rfl⟩ : syracuseStep 2705075 = 4057613) B4057613
theorem B4056785 : Blo 1801602 4056785 := bstep (se 2 (by rfl) ⟨1521294, by rfl⟩ : syracuseStep 4056785 = 3042589) B3042589
theorem B2705105 : Blo 1801602 2705105 := bstep (se 2 (by rfl) ⟨1014414, by rfl⟩ : syracuseStep 2705105 = 2028829) B2028829
theorem B3081953 : Blo 1801602 3081953 := bstep (se 2 (by rfl) ⟨1155732, by rfl⟩ : syracuseStep 3081953 = 2311465) B2311465
theorem B4056803 : Blo 1801602 4056803 := bstep (se 1 (by rfl) ⟨3042602, by rfl⟩ : syracuseStep 4056803 = 6085205) B6085205
theorem B2705123 : Blo 1801602 2705123 := bstep (se 1 (by rfl) ⟨2028842, by rfl⟩ : syracuseStep 2705123 = 4057685) B4057685
theorem B2565875 : Blo 1801602 2565875 := bstep (se 1 (by rfl) ⟨1924406, by rfl⟩ : syracuseStep 2565875 = 3848813) B3848813
theorem B2705153 : Blo 1801602 2705153 := bstep (se 2 (by rfl) ⟨1014432, by rfl⟩ : syracuseStep 2705153 = 2028865) B2028865
theorem B2705171 : Blo 1801602 2705171 := bstep (se 1 (by rfl) ⟨2028878, by rfl⟩ : syracuseStep 2705171 = 4057757) B4057757
theorem B3041057 : Blo 1801602 3041057 := bstep (se 2 (by rfl) ⟨1140396, by rfl⟩ : syracuseStep 3041057 = 2280793) B2280793
theorem B2705201 : Blo 1801602 2705201 := bstep (se 2 (by rfl) ⟨1014450, by rfl⟩ : syracuseStep 2705201 = 2028901) B2028901
theorem B2565955 : Blo 1801602 2565955 := bstep (se 1 (by rfl) ⟨1924466, by rfl⟩ : syracuseStep 2565955 = 3848933) B3848933
theorem B2705219 : Blo 1801602 2705219 := bstep (se 1 (by rfl) ⟨2028914, by rfl⟩ : syracuseStep 2705219 = 4057829) B4057829
theorem B11544389 : Blo 1801602 11544389 := bstep (se 4 (by rfl) ⟨1082286, by rfl⟩ : syracuseStep 11544389 = 2164573) B2164573
theorem B2705249 : Blo 1801602 2705249 := bstep (se 2 (by rfl) ⟨1014468, by rfl⟩ : syracuseStep 2705249 = 2028937) B2028937
theorem B2705267 : Blo 1801602 2705267 := bstep (se 1 (by rfl) ⟨2028950, by rfl⟩ : syracuseStep 2705267 = 4057901) B4057901
theorem B2705297 : Blo 1801602 2705297 := bstep (se 2 (by rfl) ⟨1014486, by rfl⟩ : syracuseStep 2705297 = 2028973) B2028973
theorem B3041185 : Blo 1801602 3041185 := bstep (se 2 (by rfl) ⟨1140444, by rfl⟩ : syracuseStep 3041185 = 2280889) B2280889
theorem B2705315 : Blo 1801602 2705315 := bstep (se 1 (by rfl) ⟨2028986, by rfl⟩ : syracuseStep 2705315 = 4057973) B4057973
theorem B2705345 : Blo 1801602 2705345 := bstep (se 2 (by rfl) ⟨1014504, by rfl⟩ : syracuseStep 2705345 = 2029009) B2029009
theorem B3041219 : Blo 1801602 3041219 := bstep (se 1 (by rfl) ⟨2280914, by rfl⟩ : syracuseStep 3041219 = 4561829) B4561829
theorem B2705363 : Blo 1801602 2705363 := bstep (se 1 (by rfl) ⟨2029022, by rfl⟩ : syracuseStep 2705363 = 4058045) B4058045
theorem B4057073 : Blo 1801602 4057073 := bstep (se 2 (by rfl) ⟨1521402, by rfl⟩ : syracuseStep 4057073 = 3042805) B3042805
theorem B2705393 : Blo 1801602 2705393 := bstep (se 2 (by rfl) ⟨1014522, by rfl⟩ : syracuseStep 2705393 = 2029045) B2029045
theorem B4057091 : Blo 1801602 4057091 := bstep (se 1 (by rfl) ⟨3042818, by rfl⟩ : syracuseStep 4057091 = 6085637) B6085637
theorem B6080561 : Blo 1801602 6080561 := bstep (se 2 (by rfl) ⟨2280210, by rfl⟩ : syracuseStep 6080561 = 4560421) B4560421
theorem B3041347 : Blo 1801602 3041347 := bstep (se 1 (by rfl) ⟨2281010, by rfl⟩ : syracuseStep 3041347 = 4562021) B4562021
theorem B2164819 : Blo 1801602 2164819 := bstep (se 1 (by rfl) ⟨1623614, by rfl⟩ : syracuseStep 2164819 = 3247229) B3247229
theorem B17328269 : Blo 1801602 17328269 := bstep (se 3 (by rfl) ⟨3249050, by rfl⟩ : syracuseStep 17328269 = 6498101) B6498101
theorem B3041489 : Blo 1801602 3041489 := bstep (se 2 (by rfl) ⟨1140558, by rfl⟩ : syracuseStep 3041489 = 2281117) B2281117
theorem B4057361 : Blo 1801602 4057361 := bstep (se 2 (by rfl) ⟨1521510, by rfl⟩ : syracuseStep 4057361 = 3043021) B3043021
theorem B4057379 : Blo 1801602 4057379 := bstep (se 1 (by rfl) ⟨3043034, by rfl⟩ : syracuseStep 4057379 = 6086069) B6086069
theorem B11553101 : Blo 1801602 11553101 := bstep (se 3 (by rfl) ⟨2166206, by rfl⟩ : syracuseStep 11553101 = 4332413) B4332413
theorem B2885969 : Blo 1801602 2885969 := bstep (se 2 (by rfl) ⟨1082238, by rfl⟩ : syracuseStep 2885969 = 2164477) B2164477
theorem B3041617 : Blo 1801602 3041617 := bstep (se 2 (by rfl) ⟨1140606, by rfl⟩ : syracuseStep 3041617 = 2281213) B2281213
theorem B20531555 : Blo 1801602 20531555 := bstep (se 1 (by rfl) ⟨15398666, by rfl⟩ : syracuseStep 20531555 = 30797333) B30797333
theorem B2566513 : Blo 1801602 2566513 := bstep (se 2 (by rfl) ⟨962442, by rfl⟩ : syracuseStep 2566513 = 1924885) B1924885
theorem B3041651 : Blo 1801602 3041651 := bstep (se 1 (by rfl) ⟨2281238, by rfl⟩ : syracuseStep 3041651 = 4562477) B4562477
theorem B6498737 : Blo 1801602 6498737 := bstep (se 2 (by rfl) ⟨2437026, by rfl⟩ : syracuseStep 6498737 = 4874053) B4874053
theorem B6252995 : Blo 1801602 6252995 := bstep (se 1 (by rfl) ⟨4689746, by rfl⟩ : syracuseStep 6252995 = 9379493) B9379493
theorem B3041779 : Blo 1801602 3041779 := bstep (se 1 (by rfl) ⟨2281334, by rfl⟩ : syracuseStep 3041779 = 4562669) B4562669
theorem B4057649 : Blo 1801602 4057649 := bstep (se 2 (by rfl) ⟨1521618, by rfl⟩ : syracuseStep 4057649 = 3043237) B3043237
theorem B8784433 : Blo 1801602 8784433 := bstep (se 2 (by rfl) ⟨3294162, by rfl⟩ : syracuseStep 8784433 = 6588325) B6588325
theorem B4057667 : Blo 1801602 4057667 := bstep (se 1 (by rfl) ⟨3043250, by rfl⟩ : syracuseStep 4057667 = 6086501) B6086501
theorem B6081101 : Blo 1801602 6081101 := bstep (se 3 (by rfl) ⟨1140206, by rfl⟩ : syracuseStep 6081101 = 2280413) B2280413
theorem B43829873 : Blo 1801602 43829873 := bstep (se 2 (by rfl) ⟨16436202, by rfl⟩ : syracuseStep 43829873 = 32872405) B32872405
theorem B3041921 : Blo 1801602 3041921 := bstep (se 2 (by rfl) ⟨1140720, by rfl⟩ : syracuseStep 3041921 = 2281441) B2281441
theorem B6081155 : Blo 1801602 6081155 := bstep (se 1 (by rfl) ⟨4560866, by rfl⟩ : syracuseStep 6081155 = 9121733) B9121733
theorem B3042049 : Blo 1801602 3042049 := bstep (se 2 (by rfl) ⟨1140768, by rfl⟩ : syracuseStep 3042049 = 2281537) B2281537
theorem B10267397 : Blo 1801602 10267397 := bstep (se 4 (by rfl) ⟨962568, by rfl⟩ : syracuseStep 10267397 = 1925137) B1925137
theorem B5131021 : Blo 1801602 5131021 := bstep (se 3 (by rfl) ⟨962066, by rfl⟩ : syracuseStep 5131021 = 1924133) B1924133
theorem B3042083 : Blo 1801602 3042083 := bstep (se 1 (by rfl) ⟨2281562, by rfl⟩ : syracuseStep 3042083 = 4563125) B4563125
theorem B12340045 : Blo 1801602 12340045 := bstep (se 3 (by rfl) ⟨2313758, by rfl⟩ : syracuseStep 12340045 = 4627517) B4627517
theorem B4057937 : Blo 1801602 4057937 := bstep (se 2 (by rfl) ⟨1521726, by rfl⟩ : syracuseStep 4057937 = 3043453) B3043453
theorem B4057955 : Blo 1801602 4057955 := bstep (se 1 (by rfl) ⟨3043466, by rfl⟩ : syracuseStep 4057955 = 6086933) B6086933
theorem B3246961 : Blo 1801602 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B2280307 : Blo 1801602 2280307 := bstep (se 1 (by rfl) ⟨1710230, by rfl⟩ : syracuseStep 2280307 = 3420461) B3420461
theorem B6081425 : Blo 1801602 6081425 := bstep (se 2 (by rfl) ⟨2280534, by rfl⟩ : syracuseStep 6081425 = 4561069) B4561069
theorem B3042211 : Blo 1801602 3042211 := bstep (se 1 (by rfl) ⟨2281658, by rfl⟩ : syracuseStep 3042211 = 4563317) B4563317
theorem B5131181 : Blo 1801602 5131181 := bstep (se 3 (by rfl) ⟨962096, by rfl⟩ : syracuseStep 5131181 = 1924193) B1924193
theorem B2280403 : Blo 1801602 2280403 := bstep (se 1 (by rfl) ⟨1710302, by rfl⟩ : syracuseStep 2280403 = 3420605) B3420605
theorem B2436113 : Blo 1801602 2436113 := bstep (se 2 (by rfl) ⟨913542, by rfl⟩ : syracuseStep 2436113 = 1827085) B1827085
theorem B3042353 : Blo 1801602 3042353 := bstep (se 2 (by rfl) ⟨1140882, by rfl⟩ : syracuseStep 3042353 = 2281765) B2281765
theorem B2567219 : Blo 1801602 2567219 := bstep (se 1 (by rfl) ⟨1925414, by rfl⟩ : syracuseStep 2567219 = 3850829) B3850829
theorem B5131363 : Blo 1801602 5131363 := bstep (se 1 (by rfl) ⟨3848522, by rfl⟩ : syracuseStep 5131363 = 7697045) B7697045
theorem B10546309 : Blo 1801602 10546309 := bstep (se 4 (by rfl) ⟨988716, by rfl⟩ : syracuseStep 10546309 = 1977433) B1977433
theorem B7703693 : Blo 1801602 7703693 := bstep (se 3 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 7703693 = 2888885) B2888885
theorem B2436259 : Blo 1801602 2436259 := bstep (se 1 (by rfl) ⟨1827194, by rfl⟩ : syracuseStep 2436259 = 3654389) B3654389
theorem B3042481 : Blo 1801602 3042481 := bstep (se 2 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 3042481 = 2281861) B2281861
theorem B2886835 : Blo 1801602 2886835 := bstep (se 1 (by rfl) ⟨2165126, by rfl⟩ : syracuseStep 2886835 = 4330253) B4330253
theorem B3042515 : Blo 1801602 3042515 := bstep (se 1 (by rfl) ⟨2281886, by rfl⟩ : syracuseStep 3042515 = 4563773) B4563773
theorem B9743651 : Blo 1801602 9743651 := bstep (se 1 (by rfl) ⟨7307738, by rfl⟩ : syracuseStep 9743651 = 14615477) B14615477
theorem B7802161 : Blo 1801602 7802161 := bstep (se 2 (by rfl) ⟨2925810, by rfl⟩ : syracuseStep 7802161 = 5851621) B5851621
theorem B3042643 : Blo 1801602 3042643 := bstep (se 1 (by rfl) ⟨2281982, by rfl⟩ : syracuseStep 3042643 = 4563965) B4563965
theorem B6843761 : Blo 1801602 6843761 := bstep (se 2 (by rfl) ⟨2566410, by rfl⟩ : syracuseStep 6843761 = 5132821) B5132821
theorem B2026867 : Blo 1801602 2026867 := bstep (se 1 (by rfl) ⟨1520150, by rfl⟩ : syracuseStep 2026867 = 3040301) B3040301
theorem B3247523 : Blo 1801602 3247523 := bstep (se 1 (by rfl) ⟨2435642, by rfl⟩ : syracuseStep 3247523 = 4871285) B4871285
theorem B6081965 : Blo 1801602 6081965 := bstep (se 3 (by rfl) ⟨1140368, by rfl⟩ : syracuseStep 6081965 = 2280737) B2280737
theorem B2436529 : Blo 1801602 2436529 := bstep (se 2 (by rfl) ⟨913698, by rfl⟩ : syracuseStep 2436529 = 1827397) B1827397
theorem B2887091 : Blo 1801602 2887091 := bstep (se 1 (by rfl) ⟨2165318, by rfl⟩ : syracuseStep 2887091 = 4330637) B4330637
theorem B2280899 : Blo 1801602 2280899 := bstep (se 1 (by rfl) ⟨1710674, by rfl⟩ : syracuseStep 2280899 = 3421349) B3421349
theorem B3042785 : Blo 1801602 3042785 := bstep (se 2 (by rfl) ⟨1141044, by rfl⟩ : syracuseStep 3042785 = 2282089) B2282089
theorem B6082019 : Blo 1801602 6082019 := bstep (se 1 (by rfl) ⟨4561514, by rfl⟩ : syracuseStep 6082019 = 9123029) B9123029
theorem B2027011 : Blo 1801602 2027011 := bstep (se 1 (by rfl) ⟨1520258, by rfl⟩ : syracuseStep 2027011 = 3040517) B3040517
theorem B3042913 : Blo 1801602 3042913 := bstep (se 2 (by rfl) ⟨1141092, by rfl⟩ : syracuseStep 3042913 = 2282185) B2282185
theorem B7695985 : Blo 1801602 7695985 := bstep (se 2 (by rfl) ⟨2885994, by rfl⟩ : syracuseStep 7695985 = 5771989) B5771989
theorem B3042947 : Blo 1801602 3042947 := bstep (se 1 (by rfl) ⟨2282210, by rfl⟩ : syracuseStep 3042947 = 4564421) B4564421
theorem B44461709 : Blo 1801602 44461709 := bstep (se 3 (by rfl) ⟨8336570, by rfl⟩ : syracuseStep 44461709 = 16673141) B16673141
theorem B2027155 : Blo 1801602 2027155 := bstep (se 1 (by rfl) ⟨1520366, by rfl⟩ : syracuseStep 2027155 = 3040733) B3040733
theorem B2567857 : Blo 1801602 2567857 := bstep (se 2 (by rfl) ⟨962946, by rfl⟩ : syracuseStep 2567857 = 1925893) B1925893
theorem B2928305 : Blo 1801602 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B6082289 : Blo 1801602 6082289 := bstep (se 2 (by rfl) ⟨2280858, by rfl⟩ : syracuseStep 6082289 = 4561717) B4561717
theorem B3043075 : Blo 1801602 3043075 := bstep (se 1 (by rfl) ⟨2282306, by rfl⟩ : syracuseStep 3043075 = 4564613) B4564613
theorem B9121571 : Blo 1801602 9121571 := bstep (se 1 (by rfl) ⟨6841178, by rfl⟩ : syracuseStep 9121571 = 13682357) B13682357
theorem B2027299 : Blo 1801602 2027299 := bstep (se 1 (by rfl) ⟨1520474, by rfl⟩ : syracuseStep 2027299 = 3040949) B3040949
theorem B2567971 : Blo 1801602 2567971 := bstep (se 1 (by rfl) ⟨1925978, by rfl⟩ : syracuseStep 2567971 = 3851957) B3851957
theorem B5205809 : Blo 1801602 5205809 := bstep (se 2 (by rfl) ⟨1952178, by rfl⟩ : syracuseStep 5205809 = 3904357) B3904357
theorem B6164333 : Blo 1801602 6164333 := bstep (se 3 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 6164333 = 2311625) B2311625
theorem B3043217 : Blo 1801602 3043217 := bstep (se 2 (by rfl) ⟨1141206, by rfl⟩ : syracuseStep 3043217 = 2282413) B2282413
theorem B2027443 : Blo 1801602 2027443 := bstep (se 1 (by rfl) ⟨1520582, by rfl⟩ : syracuseStep 2027443 = 3041165) B3041165
theorem B2166755 : Blo 1801602 2166755 := bstep (se 1 (by rfl) ⟨1625066, by rfl⟩ : syracuseStep 2166755 = 3250133) B3250133
theorem B3043345 : Blo 1801602 3043345 := bstep (se 2 (by rfl) ⟨1141254, by rfl⟩ : syracuseStep 3043345 = 2282509) B2282509
theorem B3043379 : Blo 1801602 3043379 := bstep (se 1 (by rfl) ⟨2282534, by rfl⟩ : syracuseStep 3043379 = 4565069) B4565069
theorem B2027587 : Blo 1801602 2027587 := bstep (se 1 (by rfl) ⟨1520690, by rfl⟩ : syracuseStep 2027587 = 3041381) B3041381
theorem B2281603 : Blo 1801602 2281603 := bstep (se 1 (by rfl) ⟨1711202, by rfl⟩ : syracuseStep 2281603 = 3422405) B3422405
theorem B3043507 : Blo 1801602 3043507 := bstep (se 1 (by rfl) ⟨2282630, by rfl⟩ : syracuseStep 3043507 = 4565261) B4565261
theorem B2027731 : Blo 1801602 2027731 := bstep (se 1 (by rfl) ⟨1520798, by rfl⟩ : syracuseStep 2027731 = 3041597) B3041597
theorem B2281699 : Blo 1801602 2281699 := bstep (se 1 (by rfl) ⟨1711274, by rfl⟩ : syracuseStep 2281699 = 3422549) B3422549
theorem B6082829 : Blo 1801602 6082829 := bstep (se 3 (by rfl) ⟨1140530, by rfl⟩ : syracuseStep 6082829 = 2281061) B2281061
theorem B6082883 : Blo 1801602 6082883 := bstep (se 1 (by rfl) ⟨4562162, by rfl⟩ : syracuseStep 6082883 = 9124325) B9124325
theorem B2027875 : Blo 1801602 2027875 := bstep (se 1 (by rfl) ⟨1520906, by rfl⟩ : syracuseStep 2027875 = 3041813) B3041813
theorem B2888065 : Blo 1801602 2888065 := bstep (se 2 (by rfl) ⟨1083024, by rfl⟩ : syracuseStep 2888065 = 2166049) B2166049
theorem B3248561 : Blo 1801602 3248561 := bstep (se 2 (by rfl) ⟨1218210, by rfl⟩ : syracuseStep 3248561 = 2436421) B2436421
theorem B23097797 : Blo 1801602 23097797 := bstep (se 4 (by rfl) ⟨2165418, by rfl⟩ : syracuseStep 23097797 = 4330837) B4330837
theorem B5132753 : Blo 1801602 5132753 := bstep (se 2 (by rfl) ⟨1924782, by rfl⟩ : syracuseStep 5132753 = 3849565) B3849565
theorem B3420643 : Blo 1801602 3420643 := bstep (se 1 (by rfl) ⟨2565482, by rfl⟩ : syracuseStep 3420643 = 5130965) B5130965
theorem B9130481 : Blo 1801602 9130481 := bstep (se 2 (by rfl) ⟨3423930, by rfl⟩ : syracuseStep 9130481 = 6847861) B6847861
theorem B2028019 : Blo 1801602 2028019 := bstep (se 1 (by rfl) ⟨1521014, by rfl⟩ : syracuseStep 2028019 = 3042029) B3042029
theorem B24998453 : Blo 1801602 24998453 := bstep (se 5 (by rfl) ⟨1171802, by rfl⟩ : syracuseStep 24998453 = 2343605) B2343605
theorem B9122381 : Blo 1801602 9122381 := bstep (se 3 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 9122381 = 3420893) B3420893
theorem B6083153 : Blo 1801602 6083153 := bstep (se 2 (by rfl) ⟨2281182, by rfl⟩ : syracuseStep 6083153 = 4562365) B4562365
theorem B2028163 : Blo 1801602 2028163 := bstep (se 1 (by rfl) ⟨1521122, by rfl⟩ : syracuseStep 2028163 = 3042245) B3042245
theorem B3248785 : Blo 1801602 3248785 := bstep (se 2 (by rfl) ⟨1218294, by rfl⟩ : syracuseStep 3248785 = 2436589) B2436589
theorem B15397573 : Blo 1801602 15397573 := bstep (se 4 (by rfl) ⟨1443522, by rfl⟩ : syracuseStep 15397573 = 2887045) B2887045
theorem B2282195 : Blo 1801602 2282195 := bstep (se 1 (by rfl) ⟨1711646, by rfl⟩ : syracuseStep 2282195 = 3423293) B3423293
theorem B2028307 : Blo 1801602 2028307 := bstep (se 1 (by rfl) ⟨1521230, by rfl⟩ : syracuseStep 2028307 = 3042461) B3042461
theorem B6845219 : Blo 1801602 6845219 := bstep (se 1 (by rfl) ⟨5133914, by rfl⟩ : syracuseStep 6845219 = 10267829) B10267829
theorem B5772131 : Blo 1801602 5772131 := bstep (se 1 (by rfl) ⟨4329098, by rfl⟩ : syracuseStep 5772131 = 8658197) B8658197
theorem B3421091 : Blo 1801602 3421091 := bstep (se 1 (by rfl) ⟨2565818, by rfl⟩ : syracuseStep 3421091 = 5131637) B5131637
theorem B2028451 : Blo 1801602 2028451 := bstep (se 1 (by rfl) ⟨1521338, by rfl⟩ : syracuseStep 2028451 = 3042677) B3042677
theorem B4330435 : Blo 1801602 4330435 := bstep (se 1 (by rfl) ⟨3247826, by rfl⟩ : syracuseStep 4330435 = 6495653) B6495653
theorem B8336333 : Blo 1801602 8336333 := bstep (se 3 (by rfl) ⟨1563062, by rfl⟩ : syracuseStep 8336333 = 3126125) B3126125
theorem B2028595 : Blo 1801602 2028595 := bstep (se 1 (by rfl) ⟨1521446, by rfl⟩ : syracuseStep 2028595 = 3042893) B3042893
theorem B13694021 : Blo 1801602 13694021 := bstep (se 4 (by rfl) ⟨1283814, by rfl⟩ : syracuseStep 13694021 = 2567629) B2567629
theorem B6083693 : Blo 1801602 6083693 := bstep (se 3 (by rfl) ⟨1140692, by rfl⟩ : syracuseStep 6083693 = 2281385) B2281385
theorem B6083747 : Blo 1801602 6083747 := bstep (se 1 (by rfl) ⟨4562810, by rfl⟩ : syracuseStep 6083747 = 9125621) B9125621
theorem B2741411 : Blo 1801602 2741411 := bstep (se 1 (by rfl) ⟨2056058, by rfl⟩ : syracuseStep 2741411 = 4112117) B4112117
theorem B4109489 : Blo 1801602 4109489 := bstep (se 2 (by rfl) ⟨1541058, by rfl⟩ : syracuseStep 4109489 = 3082117) B3082117
theorem B3421379 : Blo 1801602 3421379 := bstep (se 1 (by rfl) ⟨2566034, by rfl⟩ : syracuseStep 3421379 = 5132069) B5132069
theorem B2028739 : Blo 1801602 2028739 := bstep (se 1 (by rfl) ⟨1521554, by rfl⟩ : syracuseStep 2028739 = 3043109) B3043109
theorem B15406321 : Blo 1801602 15406321 := bstep (se 2 (by rfl) ⟨5777370, by rfl⟩ : syracuseStep 15406321 = 11554741) B11554741
theorem B2888993 : Blo 1801602 2888993 := bstep (se 2 (by rfl) ⟨1083372, by rfl⟩ : syracuseStep 2888993 = 2166745) B2166745
theorem B11547953 : Blo 1801602 11547953 := bstep (se 2 (by rfl) ⟨4330482, by rfl⟩ : syracuseStep 11547953 = 8660965) B8660965
theorem B2741569 : Blo 1801602 2741569 := bstep (se 2 (by rfl) ⟨1028088, by rfl⟩ : syracuseStep 2741569 = 2056177) B2056177
theorem B4109635 : Blo 1801602 4109635 := bstep (se 1 (by rfl) ⟨3082226, by rfl⟩ : syracuseStep 4109635 = 6164453) B6164453
theorem B2028883 : Blo 1801602 2028883 := bstep (se 1 (by rfl) ⟨1521662, by rfl⟩ : syracuseStep 2028883 = 3043325) B3043325
theorem B5133709 : Blo 1801602 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B6084017 : Blo 1801602 6084017 := bstep (se 2 (by rfl) ⟨2281506, by rfl⟩ : syracuseStep 6084017 = 4563013) B4563013
theorem B2029027 : Blo 1801602 2029027 := bstep (se 1 (by rfl) ⟨1521770, by rfl⟩ : syracuseStep 2029027 = 3043541) B3043541
theorem B4560401 : Blo 1801602 4560401 := bstep (se 2 (by rfl) ⟨1710150, by rfl⟩ : syracuseStep 4560401 = 3420301) B3420301
theorem B2741777 : Blo 1801602 2741777 := bstep (se 2 (by rfl) ⟨1028166, by rfl⟩ : syracuseStep 2741777 = 2056333) B2056333
theorem B5133937 : Blo 1801602 5133937 := bstep (se 2 (by rfl) ⟨1925226, by rfl⟩ : syracuseStep 5133937 = 3850453) B3850453
theorem B3127025 : Blo 1801602 3127025 := bstep (se 2 (by rfl) ⟨1172634, by rfl⟩ : syracuseStep 3127025 = 2345269) B2345269
theorem B6846221 : Blo 1801602 6846221 := bstep (se 3 (by rfl) ⟨1283666, by rfl⟩ : syracuseStep 6846221 = 2567333) B2567333
theorem B5134097 : Blo 1801602 5134097 := bstep (se 2 (by rfl) ⟨1925286, by rfl⟩ : syracuseStep 5134097 = 3850573) B3850573
theorem B5134211 : Blo 1801602 5134211 := bstep (se 1 (by rfl) ⟨3850658, by rfl⟩ : syracuseStep 5134211 = 7701317) B7701317
theorem B4388785 : Blo 1801602 4388785 := bstep (se 2 (by rfl) ⟨1645794, by rfl⟩ : syracuseStep 4388785 = 3291589) B3291589
theorem B4626371 : Blo 1801602 4626371 := bstep (se 1 (by rfl) ⟨3469778, by rfl⟩ : syracuseStep 4626371 = 6939557) B6939557
theorem B6084557 : Blo 1801602 6084557 := bstep (se 3 (by rfl) ⟨1140854, by rfl⟩ : syracuseStep 6084557 = 2281709) B2281709
theorem B6084611 : Blo 1801602 6084611 := bstep (se 1 (by rfl) ⟨4563458, by rfl⟩ : syracuseStep 6084611 = 9126917) B9126917
theorem B9877573 : Blo 1801602 9877573 := bstep (se 4 (by rfl) ⟨926022, by rfl⟩ : syracuseStep 9877573 = 1852045) B1852045
theorem B3422321 : Blo 1801602 3422321 := bstep (se 2 (by rfl) ⟨1283370, by rfl⟩ : syracuseStep 3422321 = 2566741) B2566741
theorem B5773475 : Blo 1801602 5773475 := bstep (se 1 (by rfl) ⟨4330106, by rfl⟩ : syracuseStep 5773475 = 8660213) B8660213
theorem B6084881 : Blo 1801602 6084881 := bstep (se 2 (by rfl) ⟨2281830, by rfl⟩ : syracuseStep 6084881 = 4563661) B4563661
theorem B4331875 : Blo 1801602 4331875 := bstep (se 1 (by rfl) ⟨3248906, by rfl⟩ : syracuseStep 4331875 = 6497813) B6497813
theorem B10967395 : Blo 1801602 10967395 := bstep (se 1 (by rfl) ⟨8225546, by rfl⟩ : syracuseStep 10967395 = 16451093) B16451093
theorem B10410437 : Blo 1801602 10410437 := bstep (se 4 (by rfl) ⟨975978, by rfl⟩ : syracuseStep 10410437 = 1951957) B1951957
theorem B4561393 : Blo 1801602 4561393 := bstep (se 2 (by rfl) ⟨1710522, by rfl⟩ : syracuseStep 4561393 = 3421045) B3421045
theorem B10271245 : Blo 1801602 10271245 := bstep (se 3 (by rfl) ⟨1925858, by rfl⟩ : syracuseStep 10271245 = 3851717) B3851717
theorem B5478929 : Blo 1801602 5478929 := bstep (se 2 (by rfl) ⟨2054598, by rfl⟩ : syracuseStep 5478929 = 4109197) B4109197
theorem B3848771 : Blo 1801602 3848771 := bstep (se 1 (by rfl) ⟨2886578, by rfl⟩ : syracuseStep 3848771 = 5773157) B5773157
theorem B4938317 : Blo 1801602 4938317 := bstep (se 3 (by rfl) ⟨925934, by rfl⟩ : syracuseStep 4938317 = 1851869) B1851869
theorem B4053617 : Blo 1801602 4053617 := bstep (se 2 (by rfl) ⟨1520106, by rfl⟩ : syracuseStep 4053617 = 3040213) B3040213
theorem B4627057 : Blo 1801602 4627057 := bstep (se 2 (by rfl) ⟨1735146, by rfl⟩ : syracuseStep 4627057 = 3470293) B3470293
theorem B4053635 : Blo 1801602 4053635 := bstep (se 1 (by rfl) ⟨3040226, by rfl⟩ : syracuseStep 4053635 = 6080453) B6080453
theorem B11549411 : Blo 1801602 11549411 := bstep (se 1 (by rfl) ⟨8662058, by rfl⟩ : syracuseStep 11549411 = 17324117) B17324117
theorem B4561667 : Blo 1801602 4561667 := bstep (se 1 (by rfl) ⟨3421250, by rfl⟩ : syracuseStep 4561667 = 6842501) B6842501
theorem B6167299 : Blo 1801602 6167299 := bstep (se 1 (by rfl) ⟨4625474, by rfl⟩ : syracuseStep 6167299 = 9250949) B9250949
theorem B6085421 : Blo 1801602 6085421 := bstep (se 3 (by rfl) ⟨1141016, by rfl⟩ : syracuseStep 6085421 = 2282033) B2282033
theorem B1923907 : Blo 1801602 1923907 := bstep (se 1 (by rfl) ⟨1442930, by rfl⟩ : syracuseStep 1923907 = 2885861) B2885861
theorem B4389731 : Blo 1801602 4389731 := bstep (se 1 (by rfl) ⟨3292298, by rfl⟩ : syracuseStep 4389731 = 6584597) B6584597
theorem B6085475 : Blo 1801602 6085475 := bstep (se 1 (by rfl) ⟨4564106, by rfl⟩ : syracuseStep 6085475 = 9128213) B9128213
theorem B5135213 : Blo 1801602 5135213 := bstep (se 3 (by rfl) ⟨962852, by rfl⟩ : syracuseStep 5135213 = 1925705) B1925705
theorem B4053905 : Blo 1801602 4053905 := bstep (se 2 (by rfl) ⟨1520214, by rfl⟩ : syracuseStep 4053905 = 3040429) B3040429
theorem B4053923 : Blo 1801602 4053923 := bstep (se 1 (by rfl) ⟨3040442, by rfl⟩ : syracuseStep 4053923 = 6080885) B6080885
theorem B4561859 : Blo 1801602 4561859 := bstep (se 1 (by rfl) ⟨3421394, by rfl⟩ : syracuseStep 4561859 = 6842789) B6842789
theorem B3423217 : Blo 1801602 3423217 := bstep (se 2 (by rfl) ⟨1283706, by rfl⟩ : syracuseStep 3423217 = 2567413) B2567413
theorem B5135395 : Blo 1801602 5135395 := bstep (se 1 (by rfl) ⟨3851546, by rfl⟩ : syracuseStep 5135395 = 7703093) B7703093
theorem B2702417 : Blo 1801602 2702417 := bstep (se 2 (by rfl) ⟨1013406, by rfl⟩ : syracuseStep 2702417 = 2026813) B2026813
theorem B2702435 : Blo 1801602 2702435 := bstep (se 1 (by rfl) ⟨2026826, by rfl⟩ : syracuseStep 2702435 = 4053653) B4053653
theorem B6085745 : Blo 1801602 6085745 := bstep (se 2 (by rfl) ⟨2282154, by rfl⟩ : syracuseStep 6085745 = 4564309) B4564309
theorem B2702465 : Blo 1801602 2702465 := bstep (se 2 (by rfl) ⟨1013424, by rfl⟩ : syracuseStep 2702465 = 2026849) B2026849
theorem B3423377 : Blo 1801602 3423377 := bstep (se 2 (by rfl) ⟨1283766, by rfl⟩ : syracuseStep 3423377 = 2567533) B2567533
theorem B2702483 : Blo 1801602 2702483 := bstep (se 1 (by rfl) ⟨2026862, by rfl⟩ : syracuseStep 2702483 = 4053725) B4053725
theorem B2702513 : Blo 1801602 2702513 := bstep (se 2 (by rfl) ⟨1013442, by rfl⟩ : syracuseStep 2702513 = 2026885) B2026885
theorem B4054193 : Blo 1801602 4054193 := bstep (se 2 (by rfl) ⟨1520322, by rfl⟩ : syracuseStep 4054193 = 3040645) B3040645
theorem B8019121 : Blo 1801602 8019121 := bstep (se 2 (by rfl) ⟨3007170, by rfl⟩ : syracuseStep 8019121 = 6014341) B6014341
theorem B2702531 : Blo 1801602 2702531 := bstep (se 1 (by rfl) ⟨2026898, by rfl⟩ : syracuseStep 2702531 = 4053797) B4053797
theorem B4054211 : Blo 1801602 4054211 := bstep (se 1 (by rfl) ⟨3040658, by rfl⟩ : syracuseStep 4054211 = 6081317) B6081317
theorem B5135555 : Blo 1801602 5135555 := bstep (se 1 (by rfl) ⟨3851666, by rfl⟩ : syracuseStep 5135555 = 7703333) B7703333
theorem B2702561 : Blo 1801602 2702561 := bstep (se 2 (by rfl) ⟨1013460, by rfl⟩ : syracuseStep 2702561 = 2026921) B2026921
theorem B2702579 : Blo 1801602 2702579 := bstep (se 1 (by rfl) ⟨2026934, by rfl⟩ : syracuseStep 2702579 = 4053869) B4053869
theorem B1924355 : Blo 1801602 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B2702609 : Blo 1801602 2702609 := bstep (se 2 (by rfl) ⟨1013478, by rfl⟩ : syracuseStep 2702609 = 2026957) B2026957
theorem B2702627 : Blo 1801602 2702627 := bstep (se 1 (by rfl) ⟨2026970, by rfl⟩ : syracuseStep 2702627 = 4053941) B4053941
theorem B2702657 : Blo 1801602 2702657 := bstep (se 2 (by rfl) ⟨1013496, by rfl⟩ : syracuseStep 2702657 = 2026993) B2026993
theorem B6495565 : Blo 1801602 6495565 := bstep (se 3 (by rfl) ⟨1217918, by rfl⟩ : syracuseStep 6495565 = 2435837) B2435837
theorem B2702675 : Blo 1801602 2702675 := bstep (se 1 (by rfl) ⟨2027006, by rfl⟩ : syracuseStep 2702675 = 4054013) B4054013
theorem B2702705 : Blo 1801602 2702705 := bstep (se 2 (by rfl) ⟨1013514, by rfl⟩ : syracuseStep 2702705 = 2027029) B2027029
theorem B1801603 : Blo 1801602 1801603 := bstep (se 1 (by rfl) ⟨1351202, by rfl⟩ : syracuseStep 1801603 = 2702405) B2702405
theorem B2702723 : Blo 1801602 2702723 := bstep (se 1 (by rfl) ⟨2027042, by rfl⟩ : syracuseStep 2702723 = 4054085) B4054085
theorem B1801619 : Blo 1801602 1801619 := bstep (se 1 (by rfl) ⟨1351214, by rfl⟩ : syracuseStep 1801619 = 2702429) B2702429
theorem B2702753 : Blo 1801602 2702753 := bstep (se 2 (by rfl) ⟨1013532, by rfl⟩ : syracuseStep 2702753 = 2027065) B2027065
theorem B1801635 : Blo 1801602 1801635 := bstep (se 1 (by rfl) ⟨1351226, by rfl⟩ : syracuseStep 1801635 = 2702453) B2702453
theorem B9125297 : Blo 1801602 9125297 := bstep (se 2 (by rfl) ⟨3421986, by rfl⟩ : syracuseStep 9125297 = 6843973) B6843973
theorem B1801651 : Blo 1801602 1801651 := bstep (se 1 (by rfl) ⟨1351238, by rfl⟩ : syracuseStep 1801651 = 2702477) B2702477
theorem B2702771 : Blo 1801602 2702771 := bstep (se 1 (by rfl) ⟨2027078, by rfl⟩ : syracuseStep 2702771 = 4054157) B4054157
theorem B1801667 : Blo 1801602 1801667 := bstep (se 1 (by rfl) ⟨1351250, by rfl⟩ : syracuseStep 1801667 = 2702501) B2702501
theorem B2702801 : Blo 1801602 2702801 := bstep (se 2 (by rfl) ⟨1013550, by rfl⟩ : syracuseStep 2702801 = 2027101) B2027101
theorem B4054481 : Blo 1801602 4054481 := bstep (se 2 (by rfl) ⟨1520430, by rfl⟩ : syracuseStep 4054481 = 3040861) B3040861
theorem B1801683 : Blo 1801602 1801683 := bstep (se 1 (by rfl) ⟨1351262, by rfl⟩ : syracuseStep 1801683 = 2702525) B2702525
theorem B1801699 : Blo 1801602 1801699 := bstep (se 1 (by rfl) ⟨1351274, by rfl⟩ : syracuseStep 1801699 = 2702549) B2702549
theorem B2702819 : Blo 1801602 2702819 := bstep (se 1 (by rfl) ⟨2027114, by rfl⟩ : syracuseStep 2702819 = 4054229) B4054229
theorem B4054499 : Blo 1801602 4054499 := bstep (se 1 (by rfl) ⟨3040874, by rfl⟩ : syracuseStep 4054499 = 6081749) B6081749
theorem B1801715 : Blo 1801602 1801715 := bstep (se 1 (by rfl) ⟨1351286, by rfl⟩ : syracuseStep 1801715 = 2702573) B2702573
theorem B2702849 : Blo 1801602 2702849 := bstep (se 2 (by rfl) ⟨1013568, by rfl⟩ : syracuseStep 2702849 = 2027137) B2027137
theorem B1801731 : Blo 1801602 1801731 := bstep (se 1 (by rfl) ⟨1351298, by rfl⟩ : syracuseStep 1801731 = 2702597) B2702597
theorem B4111889 : Blo 1801602 4111889 := bstep (se 2 (by rfl) ⟨1541958, by rfl⟩ : syracuseStep 4111889 = 3083917) B3083917
theorem B1801747 : Blo 1801602 1801747 := bstep (se 1 (by rfl) ⟨1351310, by rfl⟩ : syracuseStep 1801747 = 2702621) B2702621
theorem B2702867 : Blo 1801602 2702867 := bstep (se 1 (by rfl) ⟨2027150, by rfl⟩ : syracuseStep 2702867 = 4054301) B4054301
theorem B1801763 : Blo 1801602 1801763 := bstep (se 1 (by rfl) ⟨1351322, by rfl⟩ : syracuseStep 1801763 = 2702645) B2702645
theorem B3423779 : Blo 1801602 3423779 := bstep (se 1 (by rfl) ⟨2567834, by rfl⟩ : syracuseStep 3423779 = 5135669) B5135669
theorem B2702897 : Blo 1801602 2702897 := bstep (se 2 (by rfl) ⟨1013586, by rfl⟩ : syracuseStep 2702897 = 2027173) B2027173
theorem B1801779 : Blo 1801602 1801779 := bstep (se 1 (by rfl) ⟨1351334, by rfl⟩ : syracuseStep 1801779 = 2702669) B2702669
theorem B7700017 : Blo 1801602 7700017 := bstep (se 2 (by rfl) ⟨2887506, by rfl⟩ : syracuseStep 7700017 = 5775013) B5775013
theorem B4333105 : Blo 1801602 4333105 := bstep (se 2 (by rfl) ⟨1624914, by rfl⟩ : syracuseStep 4333105 = 3249829) B3249829
theorem B1801795 : Blo 1801602 1801795 := bstep (se 1 (by rfl) ⟨1351346, by rfl⟩ : syracuseStep 1801795 = 2702693) B2702693
theorem B2702915 : Blo 1801602 2702915 := bstep (se 1 (by rfl) ⟨2027186, by rfl⟩ : syracuseStep 2702915 = 4054373) B4054373
theorem B1801811 : Blo 1801602 1801811 := bstep (se 1 (by rfl) ⟨1351358, by rfl⟩ : syracuseStep 1801811 = 2702717) B2702717
theorem B2702945 : Blo 1801602 2702945 := bstep (se 2 (by rfl) ⟨1013604, by rfl⟩ : syracuseStep 2702945 = 2027209) B2027209
theorem B1801827 : Blo 1801602 1801827 := bstep (se 1 (by rfl) ⟨1351370, by rfl⟩ : syracuseStep 1801827 = 2702741) B2702741
theorem B1801843 : Blo 1801602 1801843 := bstep (se 1 (by rfl) ⟨1351382, by rfl⟩ : syracuseStep 1801843 = 2702765) B2702765
theorem B2702963 : Blo 1801602 2702963 := bstep (se 1 (by rfl) ⟨2027222, by rfl⟩ : syracuseStep 2702963 = 4054445) B4054445
theorem B1801859 : Blo 1801602 1801859 := bstep (se 1 (by rfl) ⟨1351394, by rfl⟩ : syracuseStep 1801859 = 2702789) B2702789
theorem B6086285 : Blo 1801602 6086285 := bstep (se 3 (by rfl) ⟨1141178, by rfl⟩ : syracuseStep 6086285 = 2282357) B2282357
theorem B2702993 : Blo 1801602 2702993 := bstep (se 2 (by rfl) ⟨1013622, by rfl⟩ : syracuseStep 2702993 = 2027245) B2027245
theorem B1801875 : Blo 1801602 1801875 := bstep (se 1 (by rfl) ⟨1351406, by rfl⟩ : syracuseStep 1801875 = 2702813) B2702813
theorem B1801891 : Blo 1801602 1801891 := bstep (se 1 (by rfl) ⟨1351418, by rfl⟩ : syracuseStep 1801891 = 2702837) B2702837
theorem B2703011 : Blo 1801602 2703011 := bstep (se 1 (by rfl) ⟨2027258, by rfl⟩ : syracuseStep 2703011 = 4054517) B4054517
theorem B5480099 : Blo 1801602 5480099 := bstep (se 1 (by rfl) ⟨4110074, by rfl⟩ : syracuseStep 5480099 = 8220149) B8220149
theorem B1801907 : Blo 1801602 1801907 := bstep (se 1 (by rfl) ⟨1351430, by rfl⟩ : syracuseStep 1801907 = 2702861) B2702861
theorem B2703041 : Blo 1801602 2703041 := bstep (se 2 (by rfl) ⟨1013640, by rfl⟩ : syracuseStep 2703041 = 2027281) B2027281
theorem B1801923 : Blo 1801602 1801923 := bstep (se 1 (by rfl) ⟨1351442, by rfl⟩ : syracuseStep 1801923 = 2702885) B2702885
theorem B6086339 : Blo 1801602 6086339 := bstep (se 1 (by rfl) ⟨4564754, by rfl⟩ : syracuseStep 6086339 = 9129509) B9129509
theorem B1801939 : Blo 1801602 1801939 := bstep (se 1 (by rfl) ⟨1351454, by rfl⟩ : syracuseStep 1801939 = 2702909) B2702909
theorem B2703059 : Blo 1801602 2703059 := bstep (se 1 (by rfl) ⟨2027294, by rfl⟩ : syracuseStep 2703059 = 4054589) B4054589
theorem B16695011 : Blo 1801602 16695011 := bstep (se 1 (by rfl) ⟨12521258, by rfl⟩ : syracuseStep 16695011 = 25042517) B25042517
theorem B1801955 : Blo 1801602 1801955 := bstep (se 1 (by rfl) ⟨1351466, by rfl⟩ : syracuseStep 1801955 = 2702933) B2702933
theorem B38969059 : Blo 1801602 38969059 := bstep (se 1 (by rfl) ⟨29226794, by rfl⟩ : syracuseStep 38969059 = 58453589) B58453589
theorem B2703089 : Blo 1801602 2703089 := bstep (se 2 (by rfl) ⟨1013658, by rfl⟩ : syracuseStep 2703089 = 2027317) B2027317
theorem B4054769 : Blo 1801602 4054769 := bstep (se 2 (by rfl) ⟨1520538, by rfl⟩ : syracuseStep 4054769 = 3041077) B3041077
theorem B1801971 : Blo 1801602 1801971 := bstep (se 1 (by rfl) ⟨1351478, by rfl⟩ : syracuseStep 1801971 = 2702957) B2702957
theorem B17325809 : Blo 1801602 17325809 := bstep (se 2 (by rfl) ⟨6497178, by rfl⟩ : syracuseStep 17325809 = 12994357) B12994357
theorem B1801987 : Blo 1801602 1801987 := bstep (se 1 (by rfl) ⟨1351490, by rfl⟩ : syracuseStep 1801987 = 2702981) B2702981
theorem B2703107 : Blo 1801602 2703107 := bstep (se 1 (by rfl) ⟨2027330, by rfl⟩ : syracuseStep 2703107 = 4054661) B4054661
theorem B4054787 : Blo 1801602 4054787 := bstep (se 1 (by rfl) ⟨3041090, by rfl⟩ : syracuseStep 4054787 = 6082181) B6082181
theorem B3850001 : Blo 1801602 3850001 := bstep (se 2 (by rfl) ⟨1443750, by rfl⟩ : syracuseStep 3850001 = 2887501) B2887501
theorem B1802003 : Blo 1801602 1802003 := bstep (se 1 (by rfl) ⟨1351502, by rfl⟩ : syracuseStep 1802003 = 2703005) B2703005
theorem B2703137 : Blo 1801602 2703137 := bstep (se 2 (by rfl) ⟨1013676, by rfl⟩ : syracuseStep 2703137 = 2027353) B2027353
theorem B1802019 : Blo 1801602 1802019 := bstep (se 1 (by rfl) ⟨1351514, by rfl⟩ : syracuseStep 1802019 = 2703029) B2703029
theorem B1802035 : Blo 1801602 1802035 := bstep (se 1 (by rfl) ⟨1351526, by rfl⟩ : syracuseStep 1802035 = 2703053) B2703053
theorem B2703155 : Blo 1801602 2703155 := bstep (se 1 (by rfl) ⟨2027366, by rfl⟩ : syracuseStep 2703155 = 4054733) B4054733
theorem B1802051 : Blo 1801602 1802051 := bstep (se 1 (by rfl) ⟨1351538, by rfl⟩ : syracuseStep 1802051 = 2703077) B2703077
theorem B2703185 : Blo 1801602 2703185 := bstep (se 2 (by rfl) ⟨1013694, by rfl⟩ : syracuseStep 2703185 = 2027389) B2027389
theorem B1802067 : Blo 1801602 1802067 := bstep (se 1 (by rfl) ⟨1351550, by rfl⟩ : syracuseStep 1802067 = 2703101) B2703101
theorem B1802083 : Blo 1801602 1802083 := bstep (se 1 (by rfl) ⟨1351562, by rfl⟩ : syracuseStep 1802083 = 2703125) B2703125
theorem B2703203 : Blo 1801602 2703203 := bstep (se 1 (by rfl) ⟨2027402, by rfl⟩ : syracuseStep 2703203 = 4054805) B4054805
theorem B13688675 : Blo 1801602 13688675 := bstep (se 1 (by rfl) ⟨10266506, by rfl⟩ : syracuseStep 13688675 = 20533013) B20533013
theorem B4562801 : Blo 1801602 4562801 := bstep (se 2 (by rfl) ⟨1711050, by rfl⟩ : syracuseStep 4562801 = 3422101) B3422101
theorem B1802099 : Blo 1801602 1802099 := bstep (se 1 (by rfl) ⟨1351574, by rfl⟩ : syracuseStep 1802099 = 2703149) B2703149
theorem B2703233 : Blo 1801602 2703233 := bstep (se 2 (by rfl) ⟨1013712, by rfl⟩ : syracuseStep 2703233 = 2027425) B2027425
theorem B1802115 : Blo 1801602 1802115 := bstep (se 1 (by rfl) ⟨1351586, by rfl⟩ : syracuseStep 1802115 = 2703173) B2703173
theorem B8658829 : Blo 1801602 8658829 := bstep (se 3 (by rfl) ⟨1623530, by rfl⟩ : syracuseStep 8658829 = 3247061) B3247061
theorem B5775245 : Blo 1801602 5775245 := bstep (se 3 (by rfl) ⟨1082858, by rfl⟩ : syracuseStep 5775245 = 2165717) B2165717
theorem B1802131 : Blo 1801602 1802131 := bstep (se 1 (by rfl) ⟨1351598, by rfl⟩ : syracuseStep 1802131 = 2703197) B2703197
theorem B2703251 : Blo 1801602 2703251 := bstep (se 1 (by rfl) ⟨2027438, by rfl⟩ : syracuseStep 2703251 = 4054877) B4054877
theorem B1802147 : Blo 1801602 1802147 := bstep (se 1 (by rfl) ⟨1351610, by rfl⟩ : syracuseStep 1802147 = 2703221) B2703221
theorem B4562851 : Blo 1801602 4562851 := bstep (se 1 (by rfl) ⟨3422138, by rfl⟩ : syracuseStep 4562851 = 6844277) B6844277
theorem B2703281 : Blo 1801602 2703281 := bstep (se 2 (by rfl) ⟨1013730, by rfl⟩ : syracuseStep 2703281 = 2027461) B2027461
theorem B1802163 : Blo 1801602 1802163 := bstep (se 1 (by rfl) ⟨1351622, by rfl⟩ : syracuseStep 1802163 = 2703245) B2703245
theorem B1802179 : Blo 1801602 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B2703299 : Blo 1801602 2703299 := bstep (se 1 (by rfl) ⟨2027474, by rfl⟩ : syracuseStep 2703299 = 4054949) B4054949
theorem B6086609 : Blo 1801602 6086609 := bstep (se 2 (by rfl) ⟨2282478, by rfl⟩ : syracuseStep 6086609 = 4564957) B4564957
theorem B1802195 : Blo 1801602 1802195 := bstep (se 1 (by rfl) ⟨1351646, by rfl⟩ : syracuseStep 1802195 = 2703293) B2703293
theorem B2703329 : Blo 1801602 2703329 := bstep (se 2 (by rfl) ⟨1013748, by rfl⟩ : syracuseStep 2703329 = 2027497) B2027497
theorem B1802211 : Blo 1801602 1802211 := bstep (se 1 (by rfl) ⟨1351658, by rfl⟩ : syracuseStep 1802211 = 2703317) B2703317
theorem B6676451 : Blo 1801602 6676451 := bstep (se 1 (by rfl) ⟨5007338, by rfl⟩ : syracuseStep 6676451 = 10014677) B10014677
theorem B9748451 : Blo 1801602 9748451 := bstep (se 1 (by rfl) ⟨7311338, by rfl⟩ : syracuseStep 9748451 = 14622677) B14622677
theorem B1802227 : Blo 1801602 1802227 := bstep (se 1 (by rfl) ⟨1351670, by rfl⟩ : syracuseStep 1802227 = 2703341) B2703341
theorem B2703347 : Blo 1801602 2703347 := bstep (se 1 (by rfl) ⟨2027510, by rfl⟩ : syracuseStep 2703347 = 4055021) B4055021
theorem B2703371 : Blo 1801602 2703371 := bstep (se 1 (by rfl) ⟨2027528, by rfl⟩ : syracuseStep 2703371 = 4055057) B4055057
theorem B1802251 : Blo 1801602 1802251 := bstep (se 1 (by rfl) ⟨1351688, by rfl⟩ : syracuseStep 1802251 = 2703377) B2703377
theorem B2703383 : Blo 1801602 2703383 := bstep (se 1 (by rfl) ⟨2027537, by rfl⟩ : syracuseStep 2703383 = 4055075) B4055075
theorem B1802263 : Blo 1801602 1802263 := bstep (se 1 (by rfl) ⟨1351697, by rfl⟩ : syracuseStep 1802263 = 2703395) B2703395
theorem B1802283 : Blo 1801602 1802283 := bstep (se 1 (by rfl) ⟨1351712, by rfl⟩ : syracuseStep 1802283 = 2703425) B2703425
theorem B6496301 : Blo 1801602 6496301 := bstep (se 3 (by rfl) ⟨1218056, by rfl⟩ : syracuseStep 6496301 = 2436113) B2436113
theorem B1802295 : Blo 1801602 1802295 := bstep (se 1 (by rfl) ⟨1351721, by rfl⟩ : syracuseStep 1802295 = 2703443) B2703443
theorem B1802315 : Blo 1801602 1802315 := bstep (se 1 (by rfl) ⟨1351736, by rfl⟩ : syracuseStep 1802315 = 2703473) B2703473
theorem B1802327 : Blo 1801602 1802327 := bstep (se 1 (by rfl) ⟨1351745, by rfl⟩ : syracuseStep 1802327 = 2703491) B2703491
theorem B4055129 : Blo 1801602 4055129 := bstep (se 2 (by rfl) ⟨1520673, by rfl⟩ : syracuseStep 4055129 = 3041347) B3041347
theorem B2703449 : Blo 1801602 2703449 := bstep (se 2 (by rfl) ⟨1013793, by rfl⟩ : syracuseStep 2703449 = 2027587) B2027587
theorem B1802347 : Blo 1801602 1802347 := bstep (se 1 (by rfl) ⟨1351760, by rfl⟩ : syracuseStep 1802347 = 2703521) B2703521
theorem B1802359 : Blo 1801602 1802359 := bstep (se 1 (by rfl) ⟨1351769, by rfl⟩ : syracuseStep 1802359 = 2703539) B2703539
theorem B1802379 : Blo 1801602 1802379 := bstep (se 1 (by rfl) ⟨1351784, by rfl⟩ : syracuseStep 1802379 = 2703569) B2703569
theorem B1802391 : Blo 1801602 1802391 := bstep (se 1 (by rfl) ⟨1351793, by rfl⟩ : syracuseStep 1802391 = 2703587) B2703587
theorem B1802411 : Blo 1801602 1802411 := bstep (se 1 (by rfl) ⟨1351808, by rfl⟩ : syracuseStep 1802411 = 2703617) B2703617
theorem B4055219 : Blo 1801602 4055219 := bstep (se 1 (by rfl) ⟨3041414, by rfl⟩ : syracuseStep 4055219 = 6082829) B6082829
theorem B1802423 : Blo 1801602 1802423 := bstep (se 1 (by rfl) ⟨1351817, by rfl⟩ : syracuseStep 1802423 = 2703635) B2703635
theorem B43860149 : Blo 1801602 43860149 := bstep (se 5 (by rfl) ⟨2055944, by rfl⟩ : syracuseStep 43860149 = 4111889) B4111889
theorem B2703563 : Blo 1801602 2703563 := bstep (se 1 (by rfl) ⟨2027672, by rfl⟩ : syracuseStep 2703563 = 4055345) B4055345
theorem B1802443 : Blo 1801602 1802443 := bstep (se 1 (by rfl) ⟨1351832, by rfl⟩ : syracuseStep 1802443 = 2703665) B2703665
theorem B4055255 : Blo 1801602 4055255 := bstep (se 1 (by rfl) ⟨3041441, by rfl⟩ : syracuseStep 4055255 = 6082883) B6082883
theorem B2703575 : Blo 1801602 2703575 := bstep (se 1 (by rfl) ⟨2027681, by rfl⟩ : syracuseStep 2703575 = 4055363) B4055363
theorem B1802455 : Blo 1801602 1802455 := bstep (se 1 (by rfl) ⟨1351841, by rfl⟩ : syracuseStep 1802455 = 2703683) B2703683
theorem B1802475 : Blo 1801602 1802475 := bstep (se 1 (by rfl) ⟨1351856, by rfl⟩ : syracuseStep 1802475 = 2703713) B2703713
theorem B1802487 : Blo 1801602 1802487 := bstep (se 1 (by rfl) ⟨1351865, by rfl⟩ : syracuseStep 1802487 = 2703731) B2703731
theorem B46850309 : Blo 1801602 46850309 := bstep (se 4 (by rfl) ⟨4392216, by rfl⟩ : syracuseStep 46850309 = 8784433) B8784433
theorem B23109893 : Blo 1801602 23109893 := bstep (se 4 (by rfl) ⟨2166552, by rfl⟩ : syracuseStep 23109893 = 4333105) B4333105
theorem B1802507 : Blo 1801602 1802507 := bstep (se 1 (by rfl) ⟨1351880, by rfl⟩ : syracuseStep 1802507 = 2703761) B2703761
theorem B1802519 : Blo 1801602 1802519 := bstep (se 1 (by rfl) ⟨1351889, by rfl⟩ : syracuseStep 1802519 = 2703779) B2703779
theorem B2703641 : Blo 1801602 2703641 := bstep (se 2 (by rfl) ⟨1013865, by rfl⟩ : syracuseStep 2703641 = 2027731) B2027731
theorem B1802539 : Blo 1801602 1802539 := bstep (se 1 (by rfl) ⟨1351904, by rfl⟩ : syracuseStep 1802539 = 2703809) B2703809
theorem B1802551 : Blo 1801602 1802551 := bstep (se 1 (by rfl) ⟨1351913, by rfl⟩ : syracuseStep 1802551 = 2703827) B2703827
theorem B1802571 : Blo 1801602 1802571 := bstep (se 1 (by rfl) ⟨1351928, by rfl⟩ : syracuseStep 1802571 = 2703857) B2703857
theorem B6086987 : Blo 1801602 6086987 := bstep (se 1 (by rfl) ⟨4565240, by rfl⟩ : syracuseStep 6086987 = 9130481) B9130481
theorem B1802583 : Blo 1801602 1802583 := bstep (se 1 (by rfl) ⟨1351937, by rfl⟩ : syracuseStep 1802583 = 2703875) B2703875
theorem B1802603 : Blo 1801602 1802603 := bstep (se 1 (by rfl) ⟨1351952, by rfl⟩ : syracuseStep 1802603 = 2703905) B2703905
theorem B1802615 : Blo 1801602 1802615 := bstep (se 1 (by rfl) ⟨1351961, by rfl⟩ : syracuseStep 1802615 = 2703923) B2703923
theorem B1851787 : Blo 1801602 1851787 := bstep (se 1 (by rfl) ⟨1388840, by rfl⟩ : syracuseStep 1851787 = 2777681) B2777681
theorem B4055435 : Blo 1801602 4055435 := bstep (se 1 (by rfl) ⟨3041576, by rfl⟩ : syracuseStep 4055435 = 6083153) B6083153
theorem B2703755 : Blo 1801602 2703755 := bstep (se 1 (by rfl) ⟨2027816, by rfl⟩ : syracuseStep 2703755 = 4055633) B4055633
theorem B1802635 : Blo 1801602 1802635 := bstep (se 1 (by rfl) ⟨1351976, by rfl⟩ : syracuseStep 1802635 = 2703953) B2703953
theorem B2703767 : Blo 1801602 2703767 := bstep (se 1 (by rfl) ⟨2027825, by rfl⟩ : syracuseStep 2703767 = 4055651) B4055651
theorem B1802647 : Blo 1801602 1802647 := bstep (se 1 (by rfl) ⟨1351985, by rfl⟩ : syracuseStep 1802647 = 2703971) B2703971
theorem B1802667 : Blo 1801602 1802667 := bstep (se 1 (by rfl) ⟨1352000, by rfl⟩ : syracuseStep 1802667 = 2704001) B2704001
theorem B1802679 : Blo 1801602 1802679 := bstep (se 1 (by rfl) ⟨1352009, by rfl⟩ : syracuseStep 1802679 = 2704019) B2704019
theorem B4055489 : Blo 1801602 4055489 := bstep (se 2 (by rfl) ⟨1520808, by rfl⟩ : syracuseStep 4055489 = 3041617) B3041617
theorem B1802699 : Blo 1801602 1802699 := bstep (se 1 (by rfl) ⟨1352024, by rfl⟩ : syracuseStep 1802699 = 2704049) B2704049
theorem B1802711 : Blo 1801602 1802711 := bstep (se 1 (by rfl) ⟨1352033, by rfl⟩ : syracuseStep 1802711 = 2704067) B2704067
theorem B2703833 : Blo 1801602 2703833 := bstep (se 2 (by rfl) ⟨1013937, by rfl⟩ : syracuseStep 2703833 = 2027875) B2027875
theorem B5775833 : Blo 1801602 5775833 := bstep (se 2 (by rfl) ⟨2165937, by rfl⟩ : syracuseStep 5775833 = 4331875) B4331875
theorem B14623193 : Blo 1801602 14623193 := bstep (se 2 (by rfl) ⟨5483697, by rfl⟩ : syracuseStep 14623193 = 10967395) B10967395
theorem B1802731 : Blo 1801602 1802731 := bstep (se 1 (by rfl) ⟨1352048, by rfl⟩ : syracuseStep 1802731 = 2704097) B2704097
theorem B1802743 : Blo 1801602 1802743 := bstep (se 1 (by rfl) ⟨1352057, by rfl⟩ : syracuseStep 1802743 = 2704115) B2704115
theorem B3850753 : Blo 1801602 3850753 := bstep (se 2 (by rfl) ⟨1444032, by rfl⟩ : syracuseStep 3850753 = 2888065) B2888065
theorem B1802763 : Blo 1801602 1802763 := bstep (se 1 (by rfl) ⟨1352072, by rfl⟩ : syracuseStep 1802763 = 2704145) B2704145
theorem B1802775 : Blo 1801602 1802775 := bstep (se 1 (by rfl) ⟨1352081, by rfl⟩ : syracuseStep 1802775 = 2704163) B2704163
theorem B4563479 : Blo 1801602 4563479 := bstep (se 1 (by rfl) ⟨3422609, by rfl⟩ : syracuseStep 4563479 = 6845219) B6845219
theorem B1802795 : Blo 1801602 1802795 := bstep (se 1 (by rfl) ⟨1352096, by rfl⟩ : syracuseStep 1802795 = 2704193) B2704193
theorem B1802807 : Blo 1801602 1802807 := bstep (se 1 (by rfl) ⟨1352105, by rfl⟩ : syracuseStep 1802807 = 2704211) B2704211
theorem B2703947 : Blo 1801602 2703947 := bstep (se 1 (by rfl) ⟨2027960, by rfl⟩ : syracuseStep 2703947 = 4055921) B4055921
theorem B1802827 : Blo 1801602 1802827 := bstep (se 1 (by rfl) ⟨1352120, by rfl⟩ : syracuseStep 1802827 = 2704241) B2704241
theorem B2703959 : Blo 1801602 2703959 := bstep (se 1 (by rfl) ⟨2027969, by rfl⟩ : syracuseStep 2703959 = 4055939) B4055939
theorem B1802839 : Blo 1801602 1802839 := bstep (se 1 (by rfl) ⟨1352129, by rfl⟩ : syracuseStep 1802839 = 2704259) B2704259
theorem B1802859 : Blo 1801602 1802859 := bstep (se 1 (by rfl) ⟨1352144, by rfl⟩ : syracuseStep 1802859 = 2704289) B2704289
theorem B1802871 : Blo 1801602 1802871 := bstep (se 1 (by rfl) ⟨1352153, by rfl⟩ : syracuseStep 1802871 = 2704307) B2704307
theorem B9749123 : Blo 1801602 9749123 := bstep (se 1 (by rfl) ⟨7311842, by rfl⟩ : syracuseStep 9749123 = 14623685) B14623685
theorem B1802891 : Blo 1801602 1802891 := bstep (se 1 (by rfl) ⟨1352168, by rfl⟩ : syracuseStep 1802891 = 2704337) B2704337
theorem B1802903 : Blo 1801602 1802903 := bstep (se 1 (by rfl) ⟨1352177, by rfl⟩ : syracuseStep 1802903 = 2704355) B2704355
theorem B4055705 : Blo 1801602 4055705 := bstep (se 2 (by rfl) ⟨1520889, by rfl⟩ : syracuseStep 4055705 = 3041779) B3041779
theorem B2704025 : Blo 1801602 2704025 := bstep (se 2 (by rfl) ⟨1014009, by rfl⟩ : syracuseStep 2704025 = 2028019) B2028019
theorem B1802923 : Blo 1801602 1802923 := bstep (se 1 (by rfl) ⟨1352192, by rfl⟩ : syracuseStep 1802923 = 2704385) B2704385
theorem B1802935 : Blo 1801602 1802935 := bstep (se 1 (by rfl) ⟨1352201, by rfl⟩ : syracuseStep 1802935 = 2704403) B2704403
theorem B1802955 : Blo 1801602 1802955 := bstep (se 1 (by rfl) ⟨1352216, by rfl⟩ : syracuseStep 1802955 = 2704433) B2704433
theorem B1802967 : Blo 1801602 1802967 := bstep (se 1 (by rfl) ⟨1352225, by rfl⟩ : syracuseStep 1802967 = 2704451) B2704451
theorem B1802987 : Blo 1801602 1802987 := bstep (se 1 (by rfl) ⟨1352240, by rfl⟩ : syracuseStep 1802987 = 2704481) B2704481
theorem B4055795 : Blo 1801602 4055795 := bstep (se 1 (by rfl) ⟨3041846, by rfl⟩ : syracuseStep 4055795 = 6083693) B6083693
theorem B1802999 : Blo 1801602 1802999 := bstep (se 1 (by rfl) ⟨1352249, by rfl⟩ : syracuseStep 1802999 = 2704499) B2704499
theorem B2704139 : Blo 1801602 2704139 := bstep (se 1 (by rfl) ⟨2028104, by rfl⟩ : syracuseStep 2704139 = 4056209) B4056209
theorem B1803019 : Blo 1801602 1803019 := bstep (se 1 (by rfl) ⟨1352264, by rfl⟩ : syracuseStep 1803019 = 2704529) B2704529
theorem B4055831 : Blo 1801602 4055831 := bstep (se 1 (by rfl) ⟨3041873, by rfl⟩ : syracuseStep 4055831 = 6083747) B6083747
theorem B2704151 : Blo 1801602 2704151 := bstep (se 1 (by rfl) ⟨2028113, by rfl⟩ : syracuseStep 2704151 = 4056227) B4056227
theorem B1803031 : Blo 1801602 1803031 := bstep (se 1 (by rfl) ⟨1352273, by rfl⟩ : syracuseStep 1803031 = 2704547) B2704547
theorem B1803051 : Blo 1801602 1803051 := bstep (se 1 (by rfl) ⟨1352288, by rfl⟩ : syracuseStep 1803051 = 2704577) B2704577
theorem B1803063 : Blo 1801602 1803063 := bstep (se 1 (by rfl) ⟨1352297, by rfl⟩ : syracuseStep 1803063 = 2704595) B2704595
theorem B6169409 : Blo 1801602 6169409 := bstep (se 2 (by rfl) ⟨2313528, by rfl⟩ : syracuseStep 6169409 = 4627057) B4627057
theorem B1803083 : Blo 1801602 1803083 := bstep (se 1 (by rfl) ⟨1352312, by rfl⟩ : syracuseStep 1803083 = 2704625) B2704625
theorem B1803095 : Blo 1801602 1803095 := bstep (se 1 (by rfl) ⟨1352321, by rfl⟩ : syracuseStep 1803095 = 2704643) B2704643
theorem B2704217 : Blo 1801602 2704217 := bstep (se 2 (by rfl) ⟨1014081, by rfl⟩ : syracuseStep 2704217 = 2028163) B2028163
theorem B1803115 : Blo 1801602 1803115 := bstep (se 1 (by rfl) ⟨1352336, by rfl⟩ : syracuseStep 1803115 = 2704673) B2704673
theorem B1803127 : Blo 1801602 1803127 := bstep (se 1 (by rfl) ⟨1352345, by rfl⟩ : syracuseStep 1803127 = 2704691) B2704691
theorem B1803147 : Blo 1801602 1803147 := bstep (se 1 (by rfl) ⟨1352360, by rfl⟩ : syracuseStep 1803147 = 2704721) B2704721
theorem B1803159 : Blo 1801602 1803159 := bstep (se 1 (by rfl) ⟨1352369, by rfl⟩ : syracuseStep 1803159 = 2704739) B2704739
theorem B1803179 : Blo 1801602 1803179 := bstep (se 1 (by rfl) ⟨1352384, by rfl⟩ : syracuseStep 1803179 = 2704769) B2704769
theorem B20530097 : Blo 1801602 20530097 := bstep (se 2 (by rfl) ⟨7698786, by rfl⟩ : syracuseStep 20530097 = 15397573) B15397573
theorem B1803191 : Blo 1801602 1803191 := bstep (se 1 (by rfl) ⟨1352393, by rfl⟩ : syracuseStep 1803191 = 2704787) B2704787
theorem B4056011 : Blo 1801602 4056011 := bstep (se 1 (by rfl) ⟨3042008, by rfl⟩ : syracuseStep 4056011 = 6084017) B6084017
theorem B2704331 : Blo 1801602 2704331 := bstep (se 1 (by rfl) ⟨2028248, by rfl⟩ : syracuseStep 2704331 = 4056497) B4056497
theorem B1803211 : Blo 1801602 1803211 := bstep (se 1 (by rfl) ⟨1352408, by rfl⟩ : syracuseStep 1803211 = 2704817) B2704817
theorem B2704343 : Blo 1801602 2704343 := bstep (se 1 (by rfl) ⟨2028257, by rfl⟩ : syracuseStep 2704343 = 4056515) B4056515
theorem B1803223 : Blo 1801602 1803223 := bstep (se 1 (by rfl) ⟨1352417, by rfl⟩ : syracuseStep 1803223 = 2704835) B2704835
theorem B1803243 : Blo 1801602 1803243 := bstep (se 1 (by rfl) ⟨1352432, by rfl⟩ : syracuseStep 1803243 = 2704865) B2704865
theorem B1803255 : Blo 1801602 1803255 := bstep (se 1 (by rfl) ⟨1352441, by rfl⟩ : syracuseStep 1803255 = 2704883) B2704883
theorem B4056065 : Blo 1801602 4056065 := bstep (se 2 (by rfl) ⟨1521024, by rfl⟩ : syracuseStep 4056065 = 3042049) B3042049
theorem B3040267 : Blo 1801602 3040267 := bstep (se 1 (by rfl) ⟨2280200, by rfl⟩ : syracuseStep 3040267 = 4560401) B4560401
theorem B1827851 : Blo 1801602 1827851 := bstep (se 1 (by rfl) ⟨1370888, by rfl⟩ : syracuseStep 1827851 = 2741777) B2741777
theorem B1803275 : Blo 1801602 1803275 := bstep (se 1 (by rfl) ⟨1352456, by rfl⟩ : syracuseStep 1803275 = 2704913) B2704913
theorem B6841361 : Blo 1801602 6841361 := bstep (se 2 (by rfl) ⟨2565510, by rfl⟩ : syracuseStep 6841361 = 5131021) B5131021
theorem B93627413 : Blo 1801602 93627413 := bstep (se 6 (by rfl) ⟨2194392, by rfl⟩ : syracuseStep 93627413 = 4388785) B4388785
theorem B1803287 : Blo 1801602 1803287 := bstep (se 1 (by rfl) ⟨1352465, by rfl⟩ : syracuseStep 1803287 = 2704931) B2704931
theorem B2704409 : Blo 1801602 2704409 := bstep (se 2 (by rfl) ⟨1014153, by rfl⟩ : syracuseStep 2704409 = 2028307) B2028307
theorem B1803307 : Blo 1801602 1803307 := bstep (se 1 (by rfl) ⟨1352480, by rfl⟩ : syracuseStep 1803307 = 2704961) B2704961
theorem B1803319 : Blo 1801602 1803319 := bstep (se 1 (by rfl) ⟨1352489, by rfl⟩ : syracuseStep 1803319 = 2704979) B2704979
theorem B1803339 : Blo 1801602 1803339 := bstep (se 1 (by rfl) ⟨1352504, by rfl⟩ : syracuseStep 1803339 = 2705009) B2705009
theorem B2565209 : Blo 1801602 2565209 := bstep (se 2 (by rfl) ⟨961953, by rfl⟩ : syracuseStep 2565209 = 1923907) B1923907
theorem B1803351 : Blo 1801602 1803351 := bstep (se 1 (by rfl) ⟨1352513, by rfl⟩ : syracuseStep 1803351 = 2705027) B2705027
theorem B1803371 : Blo 1801602 1803371 := bstep (se 1 (by rfl) ⟨1352528, by rfl⟩ : syracuseStep 1803371 = 2705057) B2705057
theorem B1803383 : Blo 1801602 1803383 := bstep (se 1 (by rfl) ⟨1352537, by rfl⟩ : syracuseStep 1803383 = 2705075) B2705075
theorem B2704523 : Blo 1801602 2704523 := bstep (se 1 (by rfl) ⟨2028392, by rfl⟩ : syracuseStep 2704523 = 4056785) B4056785
theorem B1803403 : Blo 1801602 1803403 := bstep (se 1 (by rfl) ⟨1352552, by rfl⟩ : syracuseStep 1803403 = 2705105) B2705105
theorem B2704535 : Blo 1801602 2704535 := bstep (se 1 (by rfl) ⟨2028401, by rfl⟩ : syracuseStep 2704535 = 4056803) B4056803
theorem B1803415 : Blo 1801602 1803415 := bstep (se 1 (by rfl) ⟨1352561, by rfl⟩ : syracuseStep 1803415 = 2705123) B2705123
theorem B3040409 : Blo 1801602 3040409 := bstep (se 2 (by rfl) ⟨1140153, by rfl⟩ : syracuseStep 3040409 = 2280307) B2280307
theorem B1803435 : Blo 1801602 1803435 := bstep (se 1 (by rfl) ⟨1352576, by rfl⟩ : syracuseStep 1803435 = 2705153) B2705153
theorem B4564147 : Blo 1801602 4564147 := bstep (se 1 (by rfl) ⟨3423110, by rfl⟩ : syracuseStep 4564147 = 6846221) B6846221
theorem B1803447 : Blo 1801602 1803447 := bstep (se 1 (by rfl) ⟨1352585, by rfl⟩ : syracuseStep 1803447 = 2705171) B2705171
theorem B1803467 : Blo 1801602 1803467 := bstep (se 1 (by rfl) ⟨1352600, by rfl⟩ : syracuseStep 1803467 = 2705201) B2705201
theorem B1803479 : Blo 1801602 1803479 := bstep (se 1 (by rfl) ⟨1352609, by rfl⟩ : syracuseStep 1803479 = 2705219) B2705219
theorem B4056281 : Blo 1801602 4056281 := bstep (se 2 (by rfl) ⟨1521105, by rfl⟩ : syracuseStep 4056281 = 3042211) B3042211
theorem B2704601 : Blo 1801602 2704601 := bstep (se 2 (by rfl) ⟨1014225, by rfl⟩ : syracuseStep 2704601 = 2028451) B2028451
theorem B1803499 : Blo 1801602 1803499 := bstep (se 1 (by rfl) ⟨1352624, by rfl⟩ : syracuseStep 1803499 = 2705249) B2705249
theorem B1803511 : Blo 1801602 1803511 := bstep (se 1 (by rfl) ⟨1352633, by rfl⟩ : syracuseStep 1803511 = 2705267) B2705267
theorem B1803531 : Blo 1801602 1803531 := bstep (se 1 (by rfl) ⟨1352648, by rfl⟩ : syracuseStep 1803531 = 2705297) B2705297
theorem B1803543 : Blo 1801602 1803543 := bstep (se 1 (by rfl) ⟨1352657, by rfl⟩ : syracuseStep 1803543 = 2705315) B2705315
theorem B3040537 : Blo 1801602 3040537 := bstep (se 2 (by rfl) ⟨1140201, by rfl⟩ : syracuseStep 3040537 = 2280403) B2280403
theorem B1803563 : Blo 1801602 1803563 := bstep (se 1 (by rfl) ⟨1352672, by rfl⟩ : syracuseStep 1803563 = 2705345) B2705345
theorem B4056371 : Blo 1801602 4056371 := bstep (se 1 (by rfl) ⟨3042278, by rfl⟩ : syracuseStep 4056371 = 6084557) B6084557
theorem B1803575 : Blo 1801602 1803575 := bstep (se 1 (by rfl) ⟨1352681, by rfl⟩ : syracuseStep 1803575 = 2705363) B2705363
theorem B4564289 : Blo 1801602 4564289 := bstep (se 2 (by rfl) ⟨1711608, by rfl⟩ : syracuseStep 4564289 = 3423217) B3423217
theorem B2704715 : Blo 1801602 2704715 := bstep (se 1 (by rfl) ⟨2028536, by rfl⟩ : syracuseStep 2704715 = 4057073) B4057073
theorem B1803595 : Blo 1801602 1803595 := bstep (se 1 (by rfl) ⟨1352696, by rfl⟩ : syracuseStep 1803595 = 2705393) B2705393
theorem B4056407 : Blo 1801602 4056407 := bstep (se 1 (by rfl) ⟨3042305, by rfl⟩ : syracuseStep 4056407 = 6084611) B6084611
theorem B2704727 : Blo 1801602 2704727 := bstep (se 1 (by rfl) ⟨2028545, by rfl⟩ : syracuseStep 2704727 = 4057091) B4057091
theorem B2704793 : Blo 1801602 2704793 := bstep (se 2 (by rfl) ⟨1014297, by rfl⟩ : syracuseStep 2704793 = 2028595) B2028595
theorem B11552179 : Blo 1801602 11552179 := bstep (se 1 (by rfl) ⟨8664134, by rfl⟩ : syracuseStep 11552179 = 17328269) B17328269
theorem B6841817 : Blo 1801602 6841817 := bstep (se 2 (by rfl) ⟨2565681, by rfl⟩ : syracuseStep 6841817 = 5131363) B5131363
theorem B4056587 : Blo 1801602 4056587 := bstep (se 1 (by rfl) ⟨3042440, by rfl⟩ : syracuseStep 4056587 = 6084881) B6084881
theorem B2704907 : Blo 1801602 2704907 := bstep (se 1 (by rfl) ⟨2028680, by rfl⟩ : syracuseStep 2704907 = 4057361) B4057361
theorem B2704919 : Blo 1801602 2704919 := bstep (se 1 (by rfl) ⟨2028689, by rfl⟩ : syracuseStep 2704919 = 4057379) B4057379
theorem B7702067 : Blo 1801602 7702067 := bstep (se 1 (by rfl) ⟨5776550, by rfl⟩ : syracuseStep 7702067 = 11553101) B11553101
theorem B10692161 : Blo 1801602 10692161 := bstep (se 2 (by rfl) ⟨4009560, by rfl⟩ : syracuseStep 10692161 = 8019121) B8019121
theorem B4056641 : Blo 1801602 4056641 := bstep (se 2 (by rfl) ⟨1521240, by rfl⟩ : syracuseStep 4056641 = 3042481) B3042481
theorem B2704985 : Blo 1801602 2704985 := bstep (se 2 (by rfl) ⟨1014369, by rfl⟩ : syracuseStep 2704985 = 2028739) B2028739
theorem B6940291 : Blo 1801602 6940291 := bstep (se 1 (by rfl) ⟨5205218, by rfl⟩ : syracuseStep 6940291 = 10410437) B10410437
theorem B6842029 : Blo 1801602 6842029 := bstep (se 3 (by rfl) ⟨1282880, by rfl⟩ : syracuseStep 6842029 = 2565761) B2565761
theorem B2705099 : Blo 1801602 2705099 := bstep (se 1 (by rfl) ⟨2028824, by rfl⟩ : syracuseStep 2705099 = 4057649) B4057649
theorem B2565847 : Blo 1801602 2565847 := bstep (se 1 (by rfl) ⟨1924385, by rfl⟩ : syracuseStep 2565847 = 3848771) B3848771
theorem B2705111 : Blo 1801602 2705111 := bstep (se 1 (by rfl) ⟨2028833, by rfl⟩ : syracuseStep 2705111 = 4057667) B4057667
theorem B8660753 : Blo 1801602 8660753 := bstep (se 2 (by rfl) ⟨3247782, by rfl⟩ : syracuseStep 8660753 = 6495565) B6495565
theorem B4056857 : Blo 1801602 4056857 := bstep (se 2 (by rfl) ⟨1521321, by rfl⟩ : syracuseStep 4056857 = 3042643) B3042643
theorem B2705177 : Blo 1801602 2705177 := bstep (se 2 (by rfl) ⟨1014441, by rfl⟩ : syracuseStep 2705177 = 2028883) B2028883
theorem B7808813 : Blo 1801602 7808813 := bstep (se 3 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 7808813 = 2928305) B2928305
theorem B3041111 : Blo 1801602 3041111 := bstep (se 1 (by rfl) ⟨2280833, by rfl⟩ : syracuseStep 3041111 = 4561667) B4561667
theorem B4056947 : Blo 1801602 4056947 := bstep (se 1 (by rfl) ⟨3042710, by rfl⟩ : syracuseStep 4056947 = 6085421) B6085421
theorem B2705291 : Blo 1801602 2705291 := bstep (se 1 (by rfl) ⟨2028968, by rfl⟩ : syracuseStep 2705291 = 4057937) B4057937
theorem B2926487 : Blo 1801602 2926487 := bstep (se 1 (by rfl) ⟨2194865, by rfl⟩ : syracuseStep 2926487 = 4389731) B4389731
theorem B4056983 : Blo 1801602 4056983 := bstep (se 1 (by rfl) ⟨3042737, by rfl⟩ : syracuseStep 4056983 = 6085475) B6085475
theorem B2705303 : Blo 1801602 2705303 := bstep (se 1 (by rfl) ⟨2028977, by rfl⟩ : syracuseStep 2705303 = 4057955) B4057955
theorem B8218541 : Blo 1801602 8218541 := bstep (se 3 (by rfl) ⟨1540976, by rfl⟩ : syracuseStep 8218541 = 3081953) B3081953
theorem B3041239 : Blo 1801602 3041239 := bstep (se 1 (by rfl) ⟨2280929, by rfl⟩ : syracuseStep 3041239 = 4561859) B4561859
theorem B2705369 : Blo 1801602 2705369 := bstep (se 2 (by rfl) ⟨1014513, by rfl⟩ : syracuseStep 2705369 = 2029027) B2029027
theorem B6842333 : Blo 1801602 6842333 := bstep (se 3 (by rfl) ⟨1282937, by rfl⟩ : syracuseStep 6842333 = 2565875) B2565875
theorem B10266689 : Blo 1801602 10266689 := bstep (se 2 (by rfl) ⟨3850008, by rfl⟩ : syracuseStep 10266689 = 7700017) B7700017
theorem B4057163 : Blo 1801602 4057163 := bstep (se 1 (by rfl) ⟨3042872, by rfl⟩ : syracuseStep 4057163 = 6085745) B6085745
theorem B4057217 : Blo 1801602 4057217 := bstep (se 2 (by rfl) ⟨1521456, by rfl⟩ : syracuseStep 4057217 = 3042913) B3042913
theorem B2165015 : Blo 1801602 2165015 := bstep (se 1 (by rfl) ⟨1623761, by rfl⟩ : syracuseStep 2165015 = 3247523) B3247523
theorem B4057433 : Blo 1801602 4057433 := bstep (se 2 (by rfl) ⟨1521537, by rfl⟩ : syracuseStep 4057433 = 3043075) B3043075
theorem B29641139 : Blo 1801602 29641139 := bstep (se 1 (by rfl) ⟨22230854, by rfl⟩ : syracuseStep 29641139 = 44461709) B44461709
theorem B4057523 : Blo 1801602 4057523 := bstep (se 1 (by rfl) ⟨3043142, by rfl⟩ : syracuseStep 4057523 = 6086285) B6086285
theorem B4057559 : Blo 1801602 4057559 := bstep (se 1 (by rfl) ⟨3043169, by rfl⟩ : syracuseStep 4057559 = 6086339) B6086339
theorem B2566667 : Blo 1801602 2566667 := bstep (se 1 (by rfl) ⟨1925000, by rfl⟩ : syracuseStep 2566667 = 3850001) B3850001
theorem B11545105 : Blo 1801602 11545105 := bstep (se 2 (by rfl) ⟨4329414, by rfl⟩ : syracuseStep 11545105 = 8658829) B8658829
theorem B6081047 : Blo 1801602 6081047 := bstep (se 1 (by rfl) ⟨4560785, by rfl⟩ : syracuseStep 6081047 = 9121571) B9121571
theorem B3041867 : Blo 1801602 3041867 := bstep (se 1 (by rfl) ⟨2281400, by rfl⟩ : syracuseStep 3041867 = 4562801) B4562801
theorem B5778013 : Blo 1801602 5778013 := bstep (se 3 (by rfl) ⟨1083377, by rfl⟩ : syracuseStep 5778013 = 2166755) B2166755
theorem B4057739 : Blo 1801602 4057739 := bstep (se 1 (by rfl) ⟨3043304, by rfl⟩ : syracuseStep 4057739 = 6086609) B6086609
theorem B4450967 : Blo 1801602 4450967 := bstep (se 1 (by rfl) ⟨3338225, by rfl⟩ : syracuseStep 4450967 = 6676451) B6676451
theorem B6498967 : Blo 1801602 6498967 := bstep (se 1 (by rfl) ⟨4874225, by rfl⟩ : syracuseStep 6498967 = 9748451) B9748451
theorem B4057793 : Blo 1801602 4057793 := bstep (se 2 (by rfl) ⟨1521672, by rfl⟩ : syracuseStep 4057793 = 3043345) B3043345
theorem B3041995 : Blo 1801602 3041995 := bstep (se 1 (by rfl) ⟨2281496, by rfl⟩ : syracuseStep 3041995 = 4562993) B4562993
theorem B2886425 : Blo 1801602 2886425 := bstep (se 2 (by rfl) ⟨1082409, by rfl⟩ : syracuseStep 2886425 = 2164819) B2164819
theorem B32877377 : Blo 1801602 32877377 := bstep (se 2 (by rfl) ⟨12329016, by rfl⟩ : syracuseStep 32877377 = 24658033) B24658033
theorem B3042137 : Blo 1801602 3042137 := bstep (se 2 (by rfl) ⟨1140801, by rfl⟩ : syracuseStep 3042137 = 2281603) B2281603
theorem B4058009 : Blo 1801602 4058009 := bstep (se 2 (by rfl) ⟨1521753, by rfl⟩ : syracuseStep 4058009 = 3043507) B3043507
theorem B2165707 : Blo 1801602 2165707 := bstep (se 1 (by rfl) ⟨1624280, by rfl⟩ : syracuseStep 2165707 = 3248561) B3248561
theorem B3042265 : Blo 1801602 3042265 := bstep (se 2 (by rfl) ⟨1140849, by rfl⟩ : syracuseStep 3042265 = 2281699) B2281699
theorem B4058099 : Blo 1801602 4058099 := bstep (se 1 (by rfl) ⟨3043574, by rfl⟩ : syracuseStep 4058099 = 6087149) B6087149
theorem B16665635 : Blo 1801602 16665635 := bstep (se 1 (by rfl) ⟨12499226, by rfl⟩ : syracuseStep 16665635 = 24998453) B24998453
theorem B6081587 : Blo 1801602 6081587 := bstep (se 1 (by rfl) ⟨4561190, by rfl⟩ : syracuseStep 6081587 = 9122381) B9122381
theorem B9743435 : Blo 1801602 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B15395933 : Blo 1801602 15395933 := bstep (se 3 (by rfl) ⟨2886737, by rfl⟩ : syracuseStep 15395933 = 5773475) B5773475
theorem B7310429 : Blo 1801602 7310429 := bstep (se 3 (by rfl) ⟨1370705, by rfl⟩ : syracuseStep 7310429 = 2741411) B2741411
theorem B12332249 : Blo 1801602 12332249 := bstep (se 2 (by rfl) ⟨4624593, by rfl⟩ : syracuseStep 12332249 = 9249187) B9249187
theorem B2280727 : Blo 1801602 2280727 := bstep (se 1 (by rfl) ⟨1710545, by rfl⟩ : syracuseStep 2280727 = 3421091) B3421091
theorem B2436377 : Blo 1801602 2436377 := bstep (se 2 (by rfl) ⟨913641, by rfl⟩ : syracuseStep 2436377 = 1827283) B1827283
theorem B5557555 : Blo 1801602 5557555 := bstep (se 1 (by rfl) ⟨4168166, by rfl⟩ : syracuseStep 5557555 = 8336333) B8336333
theorem B6081857 : Blo 1801602 6081857 := bstep (se 2 (by rfl) ⟨2280696, by rfl⟩ : syracuseStep 6081857 = 4561393) B4561393
theorem B5131613 : Blo 1801602 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B9129347 : Blo 1801602 9129347 := bstep (se 1 (by rfl) ⟨6847010, by rfl⟩ : syracuseStep 9129347 = 13694021) B13694021
theorem B2026903 : Blo 1801602 2026903 := bstep (se 1 (by rfl) ⟨1520177, by rfl⟩ : syracuseStep 2026903 = 3040355) B3040355
theorem B7703981 : Blo 1801602 7703981 := bstep (se 3 (by rfl) ⟨1444496, by rfl⟩ : syracuseStep 7703981 = 2888993) B2888993
theorem B2739659 : Blo 1801602 2739659 := bstep (se 1 (by rfl) ⟨2054744, by rfl⟩ : syracuseStep 2739659 = 4109489) B4109489
theorem B2567641 : Blo 1801602 2567641 := bstep (se 2 (by rfl) ⟨962865, by rfl⟩ : syracuseStep 2567641 = 1925731) B1925731
theorem B3042839 : Blo 1801602 3042839 := bstep (se 1 (by rfl) ⟨2282129, by rfl⟩ : syracuseStep 3042839 = 4564259) B4564259
theorem B7695917 : Blo 1801602 7695917 := bstep (se 3 (by rfl) ⟨1442984, by rfl⟩ : syracuseStep 7695917 = 2885969) B2885969
theorem B2027083 : Blo 1801602 2027083 := bstep (se 1 (by rfl) ⟨1520312, by rfl⟩ : syracuseStep 2027083 = 3040625) B3040625
theorem B3042967 : Blo 1801602 3042967 := bstep (se 1 (by rfl) ⟨2282225, by rfl⟩ : syracuseStep 3042967 = 4564451) B4564451
theorem B2027191 : Blo 1801602 2027191 := bstep (se 1 (by rfl) ⟨1520393, by rfl⟩ : syracuseStep 2027191 = 3040787) B3040787
theorem B4329281 : Blo 1801602 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B6082397 : Blo 1801602 6082397 := bstep (se 3 (by rfl) ⟨1140449, by rfl⟩ : syracuseStep 6082397 = 2280899) B2280899
theorem B16674653 : Blo 1801602 16674653 := bstep (se 3 (by rfl) ⟨3126497, by rfl⟩ : syracuseStep 16674653 = 6252995) B6252995
theorem B2027371 : Blo 1801602 2027371 := bstep (se 1 (by rfl) ⟨1520528, by rfl⟩ : syracuseStep 2027371 = 3041057) B3041057
theorem B7696259 : Blo 1801602 7696259 := bstep (se 1 (by rfl) ⟨5772194, by rfl⟩ : syracuseStep 7696259 = 11544389) B11544389
theorem B2027479 : Blo 1801602 2027479 := bstep (se 1 (by rfl) ⟨1520609, by rfl⟩ : syracuseStep 2027479 = 3041219) B3041219
theorem B3084247 : Blo 1801602 3084247 := bstep (se 1 (by rfl) ⟨2313185, by rfl⟩ : syracuseStep 3084247 = 4626371) B4626371
theorem B58486805 : Blo 1801602 58486805 := bstep (se 6 (by rfl) ⟨1370784, by rfl⟩ : syracuseStep 58486805 = 2741569) B2741569
theorem B2281547 : Blo 1801602 2281547 := bstep (se 1 (by rfl) ⟨1711160, by rfl⟩ : syracuseStep 2281547 = 3422321) B3422321
theorem B2027659 : Blo 1801602 2027659 := bstep (se 1 (by rfl) ⟨1520744, by rfl⟩ : syracuseStep 2027659 = 3041489) B3041489
theorem B14061745 : Blo 1801602 14061745 := bstep (se 2 (by rfl) ⟨5273154, by rfl⟩ : syracuseStep 14061745 = 10546309) B10546309
theorem B3420377 : Blo 1801602 3420377 := bstep (se 2 (by rfl) ⟨1282641, by rfl⟩ : syracuseStep 3420377 = 2565283) B2565283
theorem B3248345 : Blo 1801602 3248345 := bstep (se 2 (by rfl) ⟨1218129, by rfl⟩ : syracuseStep 3248345 = 2436259) B2436259
theorem B2027767 : Blo 1801602 2027767 := bstep (se 1 (by rfl) ⟨1520825, by rfl⟩ : syracuseStep 2027767 = 3041651) B3041651
theorem B41611525 : Blo 1801602 41611525 := bstep (se 4 (by rfl) ⟨3901080, by rfl⟩ : syracuseStep 41611525 = 7802161) B7802161
theorem B20541761 : Blo 1801602 20541761 := bstep (se 2 (by rfl) ⟨7703160, by rfl⟩ : syracuseStep 20541761 = 15406321) B15406321
theorem B21918053 : Blo 1801602 21918053 := bstep (se 4 (by rfl) ⟨2054817, by rfl⟩ : syracuseStep 21918053 = 4109635) B4109635
theorem B2027947 : Blo 1801602 2027947 := bstep (se 1 (by rfl) ⟨1520960, by rfl⟩ : syracuseStep 2027947 = 3041921) B3041921
theorem B6844931 : Blo 1801602 6844931 := bstep (se 1 (by rfl) ⟨5133698, by rfl⟩ : syracuseStep 6844931 = 10267397) B10267397
theorem B6844945 : Blo 1801602 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B2028055 : Blo 1801602 2028055 := bstep (se 1 (by rfl) ⟨1521041, by rfl⟩ : syracuseStep 2028055 = 3042083) B3042083
theorem B3248705 : Blo 1801602 3248705 := bstep (se 2 (by rfl) ⟨1218264, by rfl⟩ : syracuseStep 3248705 = 2436529) B2436529
theorem B44520029 : Blo 1801602 44520029 := bstep (se 3 (by rfl) ⟨8347505, by rfl⟩ : syracuseStep 44520029 = 16695011) B16695011
theorem B3420787 : Blo 1801602 3420787 := bstep (se 1 (by rfl) ⟨2565590, by rfl⟩ : syracuseStep 3420787 = 5131181) B5131181
theorem B2028235 : Blo 1801602 2028235 := bstep (se 1 (by rfl) ⟨1521176, by rfl⟩ : syracuseStep 2028235 = 3042353) B3042353
theorem B2282251 : Blo 1801602 2282251 := bstep (se 1 (by rfl) ⟨1711688, by rfl⟩ : syracuseStep 2282251 = 3423377) B3423377
theorem B2028343 : Blo 1801602 2028343 := bstep (se 1 (by rfl) ⟨1521257, by rfl⟩ : syracuseStep 2028343 = 3042515) B3042515
theorem B10261313 : Blo 1801602 10261313 := bstep (se 2 (by rfl) ⟨3847992, by rfl⟩ : syracuseStep 10261313 = 7695985) B7695985
theorem B6845249 : Blo 1801602 6845249 := bstep (se 2 (by rfl) ⟨2566968, by rfl⟩ : syracuseStep 6845249 = 5133937) B5133937
theorem B6083531 : Blo 1801602 6083531 := bstep (se 1 (by rfl) ⟨4562648, by rfl⟩ : syracuseStep 6083531 = 9125297) B9125297
theorem B51958745 : Blo 1801602 51958745 := bstep (se 2 (by rfl) ⟨19484529, by rfl⟩ : syracuseStep 51958745 = 38969059) B38969059
theorem B2028523 : Blo 1801602 2028523 := bstep (se 1 (by rfl) ⟨1521392, by rfl⟩ : syracuseStep 2028523 = 3042785) B3042785
theorem B2282519 : Blo 1801602 2282519 := bstep (se 1 (by rfl) ⟨1711889, by rfl⟩ : syracuseStep 2282519 = 3423779) B3423779
theorem B2028631 : Blo 1801602 2028631 := bstep (se 1 (by rfl) ⟨1521473, by rfl⟩ : syracuseStep 2028631 = 3042947) B3042947
theorem B3421273 : Blo 1801602 3421273 := bstep (se 2 (by rfl) ⟨1282977, by rfl⟩ : syracuseStep 3421273 = 2565955) B2565955
theorem B3470539 : Blo 1801602 3470539 := bstep (se 1 (by rfl) ⟨2602904, by rfl⟩ : syracuseStep 3470539 = 5205809) B5205809
theorem B6083801 : Blo 1801602 6083801 := bstep (se 2 (by rfl) ⟨2281425, by rfl⟩ : syracuseStep 6083801 = 4562851) B4562851
theorem B4109555 : Blo 1801602 4109555 := bstep (se 1 (by rfl) ⟨3082166, by rfl⟩ : syracuseStep 4109555 = 6164333) B6164333
theorem B2028811 : Blo 1801602 2028811 := bstep (se 1 (by rfl) ⟨1521608, by rfl⟩ : syracuseStep 2028811 = 3043217) B3043217
theorem B2028919 : Blo 1801602 2028919 := bstep (se 1 (by rfl) ⟨1521689, by rfl⟩ : syracuseStep 2028919 = 3043379) B3043379
theorem B13170097 : Blo 1801602 13170097 := bstep (se 2 (by rfl) ⟨4938786, by rfl⟩ : syracuseStep 13170097 = 9877573) B9877573
theorem B6845917 : Blo 1801602 6845917 := bstep (se 3 (by rfl) ⟨1283609, by rfl⟩ : syracuseStep 6845917 = 2567219) B2567219
theorem B12998161 : Blo 1801602 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B15398531 : Blo 1801602 15398531 := bstep (se 1 (by rfl) ⟨11548898, by rfl⟩ : syracuseStep 15398531 = 23097797) B23097797
theorem B25990787 : Blo 1801602 25990787 := bstep (se 1 (by rfl) ⟨19493090, by rfl⟩ : syracuseStep 25990787 = 38986181) B38986181
theorem B3421835 : Blo 1801602 3421835 := bstep (se 1 (by rfl) ⟨2566376, by rfl⟩ : syracuseStep 3421835 = 5132753) B5132753
theorem B4560563 : Blo 1801602 4560563 := bstep (se 1 (by rfl) ⟨3420422, by rfl⟩ : syracuseStep 4560563 = 6840845) B6840845
theorem B3422017 : Blo 1801602 3422017 := bstep (se 2 (by rfl) ⟨1283256, by rfl⟩ : syracuseStep 3422017 = 2566513) B2566513
theorem B9123677 : Blo 1801602 9123677 := bstep (se 3 (by rfl) ⟨1710689, by rfl⟩ : syracuseStep 9123677 = 3421379) B3421379
theorem B3848087 : Blo 1801602 3848087 := bstep (se 1 (by rfl) ⟨2886065, by rfl⟩ : syracuseStep 3848087 = 5772131) B5772131
theorem B6084503 : Blo 1801602 6084503 := bstep (se 1 (by rfl) ⟨4563377, by rfl⟩ : syracuseStep 6084503 = 9126755) B9126755
theorem B4560857 : Blo 1801602 4560857 := bstep (se 2 (by rfl) ⟨1710321, by rfl⟩ : syracuseStep 4560857 = 3420643) B3420643
theorem B13694993 : Blo 1801602 13694993 := bstep (se 2 (by rfl) ⟨5135622, by rfl⟩ : syracuseStep 13694993 = 10271245) B10271245
theorem B4331713 : Blo 1801602 4331713 := bstep (se 2 (by rfl) ⟨1624392, by rfl⟩ : syracuseStep 4331713 = 3248785) B3248785
theorem B5134529 : Blo 1801602 5134529 := bstep (se 2 (by rfl) ⟨1925448, by rfl⟩ : syracuseStep 5134529 = 3850897) B3850897
theorem B6494411 : Blo 1801602 6494411 := bstep (se 1 (by rfl) ⟨4870808, by rfl⟩ : syracuseStep 6494411 = 9741617) B9741617
theorem B7698635 : Blo 1801602 7698635 := bstep (se 1 (by rfl) ⟨5773976, by rfl⟩ : syracuseStep 7698635 = 11547953) B11547953
theorem B5134553 : Blo 1801602 5134553 := bstep (se 2 (by rfl) ⟨1925457, by rfl⟩ : syracuseStep 5134553 = 3850915) B3850915
theorem B8223065 : Blo 1801602 8223065 := bstep (se 2 (by rfl) ⟨3083649, by rfl⟩ : syracuseStep 8223065 = 6167299) B6167299
theorem B13687217 : Blo 1801602 13687217 := bstep (se 2 (by rfl) ⟨5132706, by rfl⟩ : syracuseStep 13687217 = 10265413) B10265413
theorem B6085043 : Blo 1801602 6085043 := bstep (se 1 (by rfl) ⟨4563782, by rfl⟩ : syracuseStep 6085043 = 9127565) B9127565
theorem B5773771 : Blo 1801602 5773771 := bstep (se 1 (by rfl) ⟨4330328, by rfl⟩ : syracuseStep 5773771 = 8660657) B8660657
theorem B3422731 : Blo 1801602 3422731 := bstep (se 1 (by rfl) ⟨2567048, by rfl⟩ : syracuseStep 3422731 = 5134097) B5134097
theorem B6937105 : Blo 1801602 6937105 := bstep (se 2 (by rfl) ⟨2601414, by rfl⟩ : syracuseStep 6937105 = 5202829) B5202829
theorem B3422807 : Blo 1801602 3422807 := bstep (se 1 (by rfl) ⟨2567105, by rfl⟩ : syracuseStep 3422807 = 5134211) B5134211
theorem B5773913 : Blo 1801602 5773913 := bstep (se 2 (by rfl) ⟨2165217, by rfl⟩ : syracuseStep 5773913 = 4330435) B4330435
theorem B6085313 : Blo 1801602 6085313 := bstep (se 2 (by rfl) ⟨2281992, by rfl⟩ : syracuseStep 6085313 = 4563985) B4563985
theorem B4053707 : Blo 1801602 4053707 := bstep (se 1 (by rfl) ⟨3040280, by rfl⟩ : syracuseStep 4053707 = 6080561) B6080561
theorem B6847193 : Blo 1801602 6847193 := bstep (se 2 (by rfl) ⟨2567697, by rfl⟩ : syracuseStep 6847193 = 5135395) B5135395
theorem B4053761 : Blo 1801602 4053761 := bstep (se 2 (by rfl) ⟨1520160, by rfl⟩ : syracuseStep 4053761 = 3040321) B3040321
theorem B13687703 : Blo 1801602 13687703 := bstep (se 1 (by rfl) ⟨10265777, by rfl⟩ : syracuseStep 13687703 = 20531555) B20531555
theorem B3849113 : Blo 1801602 3849113 := bstep (se 2 (by rfl) ⟨1443417, by rfl⟩ : syracuseStep 3849113 = 2886835) B2886835
theorem B4332491 : Blo 1801602 4332491 := bstep (se 1 (by rfl) ⟨3249368, by rfl⟩ : syracuseStep 4332491 = 6498737) B6498737
theorem B4053977 : Blo 1801602 4053977 := bstep (se 2 (by rfl) ⟨1520241, by rfl⟩ : syracuseStep 4053977 = 3040483) B3040483
theorem B3652619 : Blo 1801602 3652619 := bstep (se 1 (by rfl) ⟨2739464, by rfl⟩ : syracuseStep 3652619 = 5478929) B5478929
theorem B4054067 : Blo 1801602 4054067 := bstep (se 1 (by rfl) ⟨3040550, by rfl⟩ : syracuseStep 4054067 = 6081101) B6081101
theorem B3292211 : Blo 1801602 3292211 := bstep (se 1 (by rfl) ⟨2469158, by rfl⟩ : syracuseStep 3292211 = 4938317) B4938317
theorem B65813573 : Blo 1801602 65813573 := bstep (se 4 (by rfl) ⟨6170022, by rfl⟩ : syracuseStep 65813573 = 12340045) B12340045
theorem B2702411 : Blo 1801602 2702411 := bstep (se 1 (by rfl) ⟨2026808, by rfl⟩ : syracuseStep 2702411 = 4053617) B4053617
theorem B29219915 : Blo 1801602 29219915 := bstep (se 1 (by rfl) ⟨21914936, by rfl⟩ : syracuseStep 29219915 = 43829873) B43829873
theorem B2702423 : Blo 1801602 2702423 := bstep (se 1 (by rfl) ⟨2026817, by rfl⟩ : syracuseStep 2702423 = 4053635) B4053635
theorem B4054103 : Blo 1801602 4054103 := bstep (se 1 (by rfl) ⟨3040577, by rfl⟩ : syracuseStep 4054103 = 6081155) B6081155
theorem B7699607 : Blo 1801602 7699607 := bstep (se 1 (by rfl) ⟨5774705, by rfl⟩ : syracuseStep 7699607 = 11549411) B11549411
theorem B2702489 : Blo 1801602 2702489 := bstep (se 2 (by rfl) ⟨1013433, by rfl⟩ : syracuseStep 2702489 = 2026867) B2026867
theorem B6085853 : Blo 1801602 6085853 := bstep (se 3 (by rfl) ⟨1141097, by rfl⟩ : syracuseStep 6085853 = 2282195) B2282195
theorem B3423475 : Blo 1801602 3423475 := bstep (se 1 (by rfl) ⟨2567606, by rfl⟩ : syracuseStep 3423475 = 5135213) B5135213
theorem B2702603 : Blo 1801602 2702603 := bstep (se 1 (by rfl) ⟨2026952, by rfl⟩ : syracuseStep 2702603 = 4053905) B4053905
theorem B4054283 : Blo 1801602 4054283 := bstep (se 1 (by rfl) ⟨3040712, by rfl⟩ : syracuseStep 4054283 = 6081425) B6081425
theorem B2702615 : Blo 1801602 2702615 := bstep (se 1 (by rfl) ⟨2026961, by rfl⟩ : syracuseStep 2702615 = 4053923) B4053923
theorem B8338733 : Blo 1801602 8338733 := bstep (se 3 (by rfl) ⟨1563512, by rfl⟩ : syracuseStep 8338733 = 3127025) B3127025
theorem B4054337 : Blo 1801602 4054337 := bstep (se 2 (by rfl) ⟨1520376, by rfl⟩ : syracuseStep 4054337 = 3040753) B3040753
theorem B2702681 : Blo 1801602 2702681 := bstep (se 2 (by rfl) ⟨1013505, by rfl⟩ : syracuseStep 2702681 = 2027011) B2027011
theorem B1801611 : Blo 1801602 1801611 := bstep (se 1 (by rfl) ⟨1351208, by rfl⟩ : syracuseStep 1801611 = 2702417) B2702417
theorem B1801623 : Blo 1801602 1801623 := bstep (se 1 (by rfl) ⟨1351217, by rfl⟩ : syracuseStep 1801623 = 2702435) B2702435
theorem B1801643 : Blo 1801602 1801643 := bstep (se 1 (by rfl) ⟨1351232, by rfl⟩ : syracuseStep 1801643 = 2702465) B2702465
theorem B5135795 : Blo 1801602 5135795 := bstep (se 1 (by rfl) ⟨3851846, by rfl⟩ : syracuseStep 5135795 = 7703693) B7703693
theorem B1801655 : Blo 1801602 1801655 := bstep (se 1 (by rfl) ⟨1351241, by rfl⟩ : syracuseStep 1801655 = 2702483) B2702483
theorem B1801675 : Blo 1801602 1801675 := bstep (se 1 (by rfl) ⟨1351256, by rfl⟩ : syracuseStep 1801675 = 2702513) B2702513
theorem B2702795 : Blo 1801602 2702795 := bstep (se 1 (by rfl) ⟨2027096, by rfl⟩ : syracuseStep 2702795 = 4054193) B4054193
theorem B1801687 : Blo 1801602 1801687 := bstep (se 1 (by rfl) ⟨1351265, by rfl⟩ : syracuseStep 1801687 = 2702531) B2702531
theorem B2702807 : Blo 1801602 2702807 := bstep (se 1 (by rfl) ⟨2027105, by rfl⟩ : syracuseStep 2702807 = 4054211) B4054211
theorem B3423703 : Blo 1801602 3423703 := bstep (se 1 (by rfl) ⟨2567777, by rfl⟩ : syracuseStep 3423703 = 5135555) B5135555
theorem B1801707 : Blo 1801602 1801707 := bstep (se 1 (by rfl) ⟨1351280, by rfl⟩ : syracuseStep 1801707 = 2702561) B2702561
theorem B1801719 : Blo 1801602 1801719 := bstep (se 1 (by rfl) ⟨1351289, by rfl⟩ : syracuseStep 1801719 = 2702579) B2702579
theorem B1801739 : Blo 1801602 1801739 := bstep (se 1 (by rfl) ⟨1351304, by rfl⟩ : syracuseStep 1801739 = 2702609) B2702609
theorem B1801751 : Blo 1801602 1801751 := bstep (se 1 (by rfl) ⟨1351313, by rfl⟩ : syracuseStep 1801751 = 2702627) B2702627
theorem B6495767 : Blo 1801602 6495767 := bstep (se 1 (by rfl) ⟨4871825, by rfl⟩ : syracuseStep 6495767 = 9743651) B9743651
theorem B2702873 : Blo 1801602 2702873 := bstep (se 2 (by rfl) ⟨1013577, by rfl⟩ : syracuseStep 2702873 = 2027155) B2027155
theorem B4054553 : Blo 1801602 4054553 := bstep (se 2 (by rfl) ⟨1520457, by rfl⟩ : syracuseStep 4054553 = 3040915) B3040915
theorem B1801771 : Blo 1801602 1801771 := bstep (se 1 (by rfl) ⟨1351328, by rfl⟩ : syracuseStep 1801771 = 2702657) B2702657
theorem B1801783 : Blo 1801602 1801783 := bstep (se 1 (by rfl) ⟨1351337, by rfl⟩ : syracuseStep 1801783 = 2702675) B2702675
theorem B3423809 : Blo 1801602 3423809 := bstep (se 2 (by rfl) ⟨1283928, by rfl⟩ : syracuseStep 3423809 = 2567857) B2567857
theorem B1801803 : Blo 1801602 1801803 := bstep (se 1 (by rfl) ⟨1351352, by rfl⟩ : syracuseStep 1801803 = 2702705) B2702705
theorem B4562507 : Blo 1801602 4562507 := bstep (se 1 (by rfl) ⟨3421880, by rfl⟩ : syracuseStep 4562507 = 6843761) B6843761
theorem B1801815 : Blo 1801602 1801815 := bstep (se 1 (by rfl) ⟨1351361, by rfl⟩ : syracuseStep 1801815 = 2702723) B2702723
theorem B1801835 : Blo 1801602 1801835 := bstep (se 1 (by rfl) ⟨1351376, by rfl⟩ : syracuseStep 1801835 = 2702753) B2702753
theorem B4054643 : Blo 1801602 4054643 := bstep (se 1 (by rfl) ⟨3040982, by rfl⟩ : syracuseStep 4054643 = 6081965) B6081965
theorem B1801847 : Blo 1801602 1801847 := bstep (se 1 (by rfl) ⟨1351385, by rfl⟩ : syracuseStep 1801847 = 2702771) B2702771
theorem B1924727 : Blo 1801602 1924727 := bstep (se 1 (by rfl) ⟨1443545, by rfl⟩ : syracuseStep 1924727 = 2887091) B2887091
theorem B1801867 : Blo 1801602 1801867 := bstep (se 1 (by rfl) ⟨1351400, by rfl⟩ : syracuseStep 1801867 = 2702801) B2702801
theorem B2702987 : Blo 1801602 2702987 := bstep (se 1 (by rfl) ⟨2027240, by rfl⟩ : syracuseStep 2702987 = 4054481) B4054481
theorem B1801879 : Blo 1801602 1801879 := bstep (se 1 (by rfl) ⟨1351409, by rfl⟩ : syracuseStep 1801879 = 2702819) B2702819
theorem B2702999 : Blo 1801602 2702999 := bstep (se 1 (by rfl) ⟨2027249, by rfl⟩ : syracuseStep 2702999 = 4054499) B4054499
theorem B4054679 : Blo 1801602 4054679 := bstep (se 1 (by rfl) ⟨3041009, by rfl⟩ : syracuseStep 4054679 = 6082019) B6082019
theorem B1801899 : Blo 1801602 1801899 := bstep (se 1 (by rfl) ⟨1351424, by rfl⟩ : syracuseStep 1801899 = 2702849) B2702849
theorem B1801911 : Blo 1801602 1801911 := bstep (se 1 (by rfl) ⟨1351433, by rfl⟩ : syracuseStep 1801911 = 2702867) B2702867
theorem B1801931 : Blo 1801602 1801931 := bstep (se 1 (by rfl) ⟨1351448, by rfl⟩ : syracuseStep 1801931 = 2702897) B2702897
theorem B1801943 : Blo 1801602 1801943 := bstep (se 1 (by rfl) ⟨1351457, by rfl⟩ : syracuseStep 1801943 = 2702915) B2702915
theorem B2703065 : Blo 1801602 2703065 := bstep (se 2 (by rfl) ⟨1013649, by rfl⟩ : syracuseStep 2703065 = 2027299) B2027299
theorem B3423961 : Blo 1801602 3423961 := bstep (se 2 (by rfl) ⟨1283985, by rfl⟩ : syracuseStep 3423961 = 2567971) B2567971
theorem B1801963 : Blo 1801602 1801963 := bstep (se 1 (by rfl) ⟨1351472, by rfl⟩ : syracuseStep 1801963 = 2702945) B2702945
theorem B1801975 : Blo 1801602 1801975 := bstep (se 1 (by rfl) ⟨1351481, by rfl⟩ : syracuseStep 1801975 = 2702963) B2702963
theorem B1801995 : Blo 1801602 1801995 := bstep (se 1 (by rfl) ⟨1351496, by rfl⟩ : syracuseStep 1801995 = 2702993) B2702993
theorem B1802007 : Blo 1801602 1802007 := bstep (se 1 (by rfl) ⟨1351505, by rfl⟩ : syracuseStep 1802007 = 2703011) B2703011
theorem B3653399 : Blo 1801602 3653399 := bstep (se 1 (by rfl) ⟨2740049, by rfl⟩ : syracuseStep 3653399 = 5480099) B5480099
theorem B1802027 : Blo 1801602 1802027 := bstep (se 1 (by rfl) ⟨1351520, by rfl⟩ : syracuseStep 1802027 = 2703041) B2703041
theorem B1802039 : Blo 1801602 1802039 := bstep (se 1 (by rfl) ⟨1351529, by rfl⟩ : syracuseStep 1802039 = 2703059) B2703059
theorem B1802059 : Blo 1801602 1802059 := bstep (se 1 (by rfl) ⟨1351544, by rfl⟩ : syracuseStep 1802059 = 2703089) B2703089
theorem B2703179 : Blo 1801602 2703179 := bstep (se 1 (by rfl) ⟨2027384, by rfl⟩ : syracuseStep 2703179 = 4054769) B4054769
theorem B4054859 : Blo 1801602 4054859 := bstep (se 1 (by rfl) ⟨3041144, by rfl⟩ : syracuseStep 4054859 = 6082289) B6082289
theorem B11550539 : Blo 1801602 11550539 := bstep (se 1 (by rfl) ⟨8662904, by rfl⟩ : syracuseStep 11550539 = 17325809) B17325809
theorem B1802071 : Blo 1801602 1802071 := bstep (se 1 (by rfl) ⟨1351553, by rfl⟩ : syracuseStep 1802071 = 2703107) B2703107
theorem B2703191 : Blo 1801602 2703191 := bstep (se 1 (by rfl) ⟨2027393, by rfl⟩ : syracuseStep 2703191 = 4054787) B4054787
theorem B1802091 : Blo 1801602 1802091 := bstep (se 1 (by rfl) ⟨1351568, by rfl⟩ : syracuseStep 1802091 = 2703137) B2703137
theorem B1802103 : Blo 1801602 1802103 := bstep (se 1 (by rfl) ⟨1351577, by rfl⟩ : syracuseStep 1802103 = 2703155) B2703155
theorem B4054913 : Blo 1801602 4054913 := bstep (se 2 (by rfl) ⟨1520592, by rfl⟩ : syracuseStep 4054913 = 3041185) B3041185
theorem B1802123 : Blo 1801602 1802123 := bstep (se 1 (by rfl) ⟨1351592, by rfl⟩ : syracuseStep 1802123 = 2703185) B2703185
theorem B1802135 : Blo 1801602 1802135 := bstep (se 1 (by rfl) ⟨1351601, by rfl⟩ : syracuseStep 1802135 = 2703203) B2703203
theorem B9125783 : Blo 1801602 9125783 := bstep (se 1 (by rfl) ⟨6844337, by rfl⟩ : syracuseStep 9125783 = 13688675) B13688675
theorem B2703257 : Blo 1801602 2703257 := bstep (se 2 (by rfl) ⟨1013721, by rfl⟩ : syracuseStep 2703257 = 2027443) B2027443
theorem B1802155 : Blo 1801602 1802155 := bstep (se 1 (by rfl) ⟨1351616, by rfl⟩ : syracuseStep 1802155 = 2703233) B2703233
theorem B3850163 : Blo 1801602 3850163 := bstep (se 1 (by rfl) ⟨2887622, by rfl⟩ : syracuseStep 3850163 = 5775245) B5775245
theorem B1802167 : Blo 1801602 1802167 := bstep (se 1 (by rfl) ⟨1351625, by rfl⟩ : syracuseStep 1802167 = 2703251) B2703251
theorem B1802187 : Blo 1801602 1802187 := bstep (se 1 (by rfl) ⟨1351640, by rfl⟩ : syracuseStep 1802187 = 2703281) B2703281
theorem B1802199 : Blo 1801602 1802199 := bstep (se 1 (by rfl) ⟨1351649, by rfl⟩ : syracuseStep 1802199 = 2703299) B2703299
theorem B1802219 : Blo 1801602 1802219 := bstep (se 1 (by rfl) ⟨1351664, by rfl⟩ : syracuseStep 1802219 = 2703329) B2703329
theorem B1802231 : Blo 1801602 1802231 := bstep (se 1 (by rfl) ⟨1351673, by rfl⟩ : syracuseStep 1802231 = 2703347) B2703347
theorem B1802247 : Blo 1801602 1802247 := bstep (se 1 (by rfl) ⟨1351685, by rfl⟩ : syracuseStep 1802247 = 2703371) B2703371
theorem B1802255 : Blo 1801602 1802255 := bstep (se 1 (by rfl) ⟨1351691, by rfl⟩ : syracuseStep 1802255 = 2703383) B2703383
theorem B4874269 : Blo 1801602 4874269 := bstep (se 3 (by rfl) ⟨913925, by rfl⟩ : syracuseStep 4874269 = 1827851) B1827851
theorem B2703419 : Blo 1801602 2703419 := bstep (se 1 (by rfl) ⟨2027564, by rfl⟩ : syracuseStep 2703419 = 4055129) B4055129
theorem B1802299 : Blo 1801602 1802299 := bstep (se 1 (by rfl) ⟨1351724, by rfl⟩ : syracuseStep 1802299 = 2703449) B2703449
theorem B6086717 : Blo 1801602 6086717 := bstep (se 3 (by rfl) ⟨1141259, by rfl⟩ : syracuseStep 6086717 = 2282519) B2282519
theorem B44441693 : Blo 1801602 44441693 := bstep (se 3 (by rfl) ⟨8332817, by rfl⟩ : syracuseStep 44441693 = 16665635) B16665635
theorem B38961269 : Blo 1801602 38961269 := bstep (se 5 (by rfl) ⟨1826309, by rfl⟩ : syracuseStep 38961269 = 3652619) B3652619
theorem B2703479 : Blo 1801602 2703479 := bstep (se 1 (by rfl) ⟨2027609, by rfl⟩ : syracuseStep 2703479 = 4055219) B4055219
theorem B1802375 : Blo 1801602 1802375 := bstep (se 1 (by rfl) ⟨1351781, by rfl⟩ : syracuseStep 1802375 = 2703563) B2703563
theorem B2703503 : Blo 1801602 2703503 := bstep (se 1 (by rfl) ⟨2027627, by rfl⟩ : syracuseStep 2703503 = 4055255) B4055255
theorem B1802383 : Blo 1801602 1802383 := bstep (se 1 (by rfl) ⟨1351787, by rfl⟩ : syracuseStep 1802383 = 2703575) B2703575
theorem B2703545 : Blo 1801602 2703545 := bstep (se 2 (by rfl) ⟨1013829, by rfl⟩ : syracuseStep 2703545 = 2027659) B2027659
theorem B1802427 : Blo 1801602 1802427 := bstep (se 1 (by rfl) ⟨1351820, by rfl⟩ : syracuseStep 1802427 = 2703641) B2703641
theorem B6840557 : Blo 1801602 6840557 := bstep (se 3 (by rfl) ⟨1282604, by rfl⟩ : syracuseStep 6840557 = 2565209) B2565209
theorem B5775617 : Blo 1801602 5775617 := bstep (se 2 (by rfl) ⟨2165856, by rfl⟩ : syracuseStep 5775617 = 4331713) B4331713
theorem B2703623 : Blo 1801602 2703623 := bstep (se 1 (by rfl) ⟨2027717, by rfl⟩ : syracuseStep 2703623 = 4055435) B4055435
theorem B1802503 : Blo 1801602 1802503 := bstep (se 1 (by rfl) ⟨1351877, by rfl⟩ : syracuseStep 1802503 = 2703755) B2703755
theorem B1802511 : Blo 1801602 1802511 := bstep (se 1 (by rfl) ⟨1351883, by rfl⟩ : syracuseStep 1802511 = 2703767) B2703767
theorem B2703659 : Blo 1801602 2703659 := bstep (se 1 (by rfl) ⟨2027744, by rfl⟩ : syracuseStep 2703659 = 4055489) B4055489
theorem B1802555 : Blo 1801602 1802555 := bstep (se 1 (by rfl) ⟨1351916, by rfl⟩ : syracuseStep 1802555 = 2703833) B2703833
theorem B2703689 : Blo 1801602 2703689 := bstep (se 2 (by rfl) ⟨1013883, by rfl⟩ : syracuseStep 2703689 = 2027767) B2027767
theorem B4563287 : Blo 1801602 4563287 := bstep (se 1 (by rfl) ⟨3422465, by rfl⟩ : syracuseStep 4563287 = 6844931) B6844931
theorem B1802631 : Blo 1801602 1802631 := bstep (se 1 (by rfl) ⟨1351973, by rfl⟩ : syracuseStep 1802631 = 2703947) B2703947
theorem B1802639 : Blo 1801602 1802639 := bstep (se 1 (by rfl) ⟨1351979, by rfl⟩ : syracuseStep 1802639 = 2703959) B2703959
theorem B29680019 : Blo 1801602 29680019 := bstep (se 1 (by rfl) ⟨22260014, by rfl⟩ : syracuseStep 29680019 = 44520029) B44520029
theorem B2703803 : Blo 1801602 2703803 := bstep (se 1 (by rfl) ⟨2027852, by rfl⟩ : syracuseStep 2703803 = 4055705) B4055705
theorem B1802683 : Blo 1801602 1802683 := bstep (se 1 (by rfl) ⟨1352012, by rfl⟩ : syracuseStep 1802683 = 2704025) B2704025
theorem B2703863 : Blo 1801602 2703863 := bstep (se 1 (by rfl) ⟨2027897, by rfl⟩ : syracuseStep 2703863 = 4055795) B4055795
theorem B1802759 : Blo 1801602 1802759 := bstep (se 1 (by rfl) ⟨1352069, by rfl⟩ : syracuseStep 1802759 = 2704139) B2704139
theorem B2703887 : Blo 1801602 2703887 := bstep (se 1 (by rfl) ⟨2027915, by rfl⟩ : syracuseStep 2703887 = 4055831) B4055831
theorem B1802767 : Blo 1801602 1802767 := bstep (se 1 (by rfl) ⟨1352075, by rfl⟩ : syracuseStep 1802767 = 2704151) B2704151
theorem B6840875 : Blo 1801602 6840875 := bstep (se 1 (by rfl) ⟨5130656, by rfl⟩ : syracuseStep 6840875 = 10261313) B10261313
theorem B4563499 : Blo 1801602 4563499 := bstep (se 1 (by rfl) ⟨3422624, by rfl⟩ : syracuseStep 4563499 = 6845249) B6845249
theorem B4112939 : Blo 1801602 4112939 := bstep (se 1 (by rfl) ⟨3084704, by rfl⟩ : syracuseStep 4112939 = 6169409) B6169409
theorem B2703929 : Blo 1801602 2703929 := bstep (se 2 (by rfl) ⟨1013973, by rfl⟩ : syracuseStep 2703929 = 2027947) B2027947
theorem B1802811 : Blo 1801602 1802811 := bstep (se 1 (by rfl) ⟨1352108, by rfl⟩ : syracuseStep 1802811 = 2704217) B2704217
theorem B4055687 : Blo 1801602 4055687 := bstep (se 1 (by rfl) ⟨3041765, by rfl⟩ : syracuseStep 4055687 = 6083531) B6083531
theorem B2704007 : Blo 1801602 2704007 := bstep (se 1 (by rfl) ⟨2028005, by rfl⟩ : syracuseStep 2704007 = 4056011) B4056011
theorem B1802887 : Blo 1801602 1802887 := bstep (se 1 (by rfl) ⟨1352165, by rfl⟩ : syracuseStep 1802887 = 2704331) B2704331
theorem B1802895 : Blo 1801602 1802895 := bstep (se 1 (by rfl) ⟨1352171, by rfl⟩ : syracuseStep 1802895 = 2704343) B2704343
theorem B2704043 : Blo 1801602 2704043 := bstep (se 1 (by rfl) ⟨2028032, by rfl⟩ : syracuseStep 2704043 = 4056065) B4056065
theorem B4563641 : Blo 1801602 4563641 := bstep (se 2 (by rfl) ⟨1711365, by rfl⟩ : syracuseStep 4563641 = 3422731) B3422731
theorem B1802939 : Blo 1801602 1802939 := bstep (se 1 (by rfl) ⟨1352204, by rfl⟩ : syracuseStep 1802939 = 2704409) B2704409
theorem B15393473 : Blo 1801602 15393473 := bstep (se 2 (by rfl) ⟨5772552, by rfl⟩ : syracuseStep 15393473 = 11545105) B11545105
theorem B9249473 : Blo 1801602 9249473 := bstep (se 2 (by rfl) ⟨3468552, by rfl⟩ : syracuseStep 9249473 = 6937105) B6937105
theorem B9126593 : Blo 1801602 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B2704073 : Blo 1801602 2704073 := bstep (se 2 (by rfl) ⟨1014027, by rfl⟩ : syracuseStep 2704073 = 2028055) B2028055
theorem B6497005 : Blo 1801602 6497005 := bstep (se 3 (by rfl) ⟨1218188, by rfl⟩ : syracuseStep 6497005 = 2436377) B2436377
theorem B1803015 : Blo 1801602 1803015 := bstep (se 1 (by rfl) ⟨1352261, by rfl⟩ : syracuseStep 1803015 = 2704523) B2704523
theorem B1803023 : Blo 1801602 1803023 := bstep (se 1 (by rfl) ⟨1352267, by rfl⟩ : syracuseStep 1803023 = 2704535) B2704535
theorem B4055867 : Blo 1801602 4055867 := bstep (se 1 (by rfl) ⟨3041900, by rfl⟩ : syracuseStep 4055867 = 6083801) B6083801
theorem B2704187 : Blo 1801602 2704187 := bstep (se 1 (by rfl) ⟨2028140, by rfl⟩ : syracuseStep 2704187 = 4056281) B4056281
theorem B1803067 : Blo 1801602 1803067 := bstep (se 1 (by rfl) ⟨1352300, by rfl⟩ : syracuseStep 1803067 = 2704601) B2704601
theorem B2704247 : Blo 1801602 2704247 := bstep (se 1 (by rfl) ⟨2028185, by rfl⟩ : syracuseStep 2704247 = 4056371) B4056371
theorem B1803143 : Blo 1801602 1803143 := bstep (se 1 (by rfl) ⟨1352357, by rfl⟩ : syracuseStep 1803143 = 2704715) B2704715
theorem B2704271 : Blo 1801602 2704271 := bstep (se 1 (by rfl) ⟨2028203, by rfl⟩ : syracuseStep 2704271 = 4056407) B4056407
theorem B1803151 : Blo 1801602 1803151 := bstep (se 1 (by rfl) ⟨1352363, by rfl⟩ : syracuseStep 1803151 = 2704727) B2704727
theorem B4055993 : Blo 1801602 4055993 := bstep (se 2 (by rfl) ⟨1520997, by rfl⟩ : syracuseStep 4055993 = 3041995) B3041995
theorem B2704313 : Blo 1801602 2704313 := bstep (se 2 (by rfl) ⟨1014117, by rfl⟩ : syracuseStep 2704313 = 2028235) B2028235
theorem B1803195 : Blo 1801602 1803195 := bstep (se 1 (by rfl) ⟨1352396, by rfl⟩ : syracuseStep 1803195 = 2704793) B2704793
theorem B2704391 : Blo 1801602 2704391 := bstep (se 1 (by rfl) ⟨2028293, by rfl⟩ : syracuseStep 2704391 = 4056587) B4056587
theorem B1803271 : Blo 1801602 1803271 := bstep (se 1 (by rfl) ⟨1352453, by rfl⟩ : syracuseStep 1803271 = 2704907) B2704907
theorem B1803279 : Blo 1801602 1803279 := bstep (se 1 (by rfl) ⟨1352459, by rfl⟩ : syracuseStep 1803279 = 2704919) B2704919
theorem B7128107 : Blo 1801602 7128107 := bstep (se 1 (by rfl) ⟨5346080, by rfl⟩ : syracuseStep 7128107 = 10692161) B10692161
theorem B2704427 : Blo 1801602 2704427 := bstep (se 1 (by rfl) ⟨2028320, by rfl⟩ : syracuseStep 2704427 = 4056641) B4056641
theorem B1803323 : Blo 1801602 1803323 := bstep (se 1 (by rfl) ⟨1352492, by rfl⟩ : syracuseStep 1803323 = 2704985) B2704985
theorem B2704457 : Blo 1801602 2704457 := bstep (se 2 (by rfl) ⟨1014171, by rfl⟩ : syracuseStep 2704457 = 2028343) B2028343
theorem B10265687 : Blo 1801602 10265687 := bstep (se 1 (by rfl) ⟨7699265, by rfl⟩ : syracuseStep 10265687 = 15398531) B15398531
theorem B17327191 : Blo 1801602 17327191 := bstep (se 1 (by rfl) ⟨12995393, by rfl⟩ : syracuseStep 17327191 = 25990787) B25990787
theorem B3040375 : Blo 1801602 3040375 := bstep (se 1 (by rfl) ⟨2280281, by rfl⟩ : syracuseStep 3040375 = 4560563) B4560563
theorem B1803399 : Blo 1801602 1803399 := bstep (se 1 (by rfl) ⟨1352549, by rfl⟩ : syracuseStep 1803399 = 2705099) B2705099
theorem B1803407 : Blo 1801602 1803407 := bstep (se 1 (by rfl) ⟨1352555, by rfl⟩ : syracuseStep 1803407 = 2705111) B2705111
theorem B2704571 : Blo 1801602 2704571 := bstep (se 1 (by rfl) ⟨2028428, by rfl⟩ : syracuseStep 2704571 = 4056857) B4056857
theorem B1803451 : Blo 1801602 1803451 := bstep (se 1 (by rfl) ⟨1352588, by rfl⟩ : syracuseStep 1803451 = 2705177) B2705177
theorem B15402221 : Blo 1801602 15402221 := bstep (se 3 (by rfl) ⟨2887916, by rfl⟩ : syracuseStep 15402221 = 5775833) B5775833
theorem B38995181 : Blo 1801602 38995181 := bstep (se 3 (by rfl) ⟨7311596, by rfl⟩ : syracuseStep 38995181 = 14623193) B14623193
theorem B2704631 : Blo 1801602 2704631 := bstep (se 1 (by rfl) ⟨2028473, by rfl⟩ : syracuseStep 2704631 = 4056947) B4056947
theorem B1803527 : Blo 1801602 1803527 := bstep (se 1 (by rfl) ⟨1352645, by rfl⟩ : syracuseStep 1803527 = 2705291) B2705291
theorem B4056335 : Blo 1801602 4056335 := bstep (se 1 (by rfl) ⟨3042251, by rfl⟩ : syracuseStep 4056335 = 6084503) B6084503
theorem B2704655 : Blo 1801602 2704655 := bstep (se 1 (by rfl) ⟨2028491, by rfl⟩ : syracuseStep 2704655 = 4056983) B4056983
theorem B1803535 : Blo 1801602 1803535 := bstep (se 1 (by rfl) ⟨1352651, by rfl⟩ : syracuseStep 1803535 = 2705303) B2705303
theorem B4056353 : Blo 1801602 4056353 := bstep (se 2 (by rfl) ⟨1521132, by rfl⟩ : syracuseStep 4056353 = 3042265) B3042265
theorem B2704697 : Blo 1801602 2704697 := bstep (se 2 (by rfl) ⟨1014261, by rfl⟩ : syracuseStep 2704697 = 2028523) B2028523
theorem B3040571 : Blo 1801602 3040571 := bstep (se 1 (by rfl) ⟨2280428, by rfl⟩ : syracuseStep 3040571 = 4560857) B4560857
theorem B1803579 : Blo 1801602 1803579 := bstep (se 1 (by rfl) ⟨1352684, by rfl⟩ : syracuseStep 1803579 = 2705369) B2705369
theorem B2704775 : Blo 1801602 2704775 := bstep (se 1 (by rfl) ⟨2028581, by rfl⟩ : syracuseStep 2704775 = 4057163) B4057163
theorem B2704811 : Blo 1801602 2704811 := bstep (se 1 (by rfl) ⟨2028608, by rfl⟩ : syracuseStep 2704811 = 4057217) B4057217
theorem B2704841 : Blo 1801602 2704841 := bstep (se 2 (by rfl) ⟨1014315, by rfl⟩ : syracuseStep 2704841 = 2028631) B2028631
theorem B20538845 : Blo 1801602 20538845 := bstep (se 3 (by rfl) ⟨3851033, by rfl⟩ : syracuseStep 20538845 = 7702067) B7702067
theorem B5482043 : Blo 1801602 5482043 := bstep (se 1 (by rfl) ⟨4111532, by rfl⟩ : syracuseStep 5482043 = 8223065) B8223065
theorem B2704955 : Blo 1801602 2704955 := bstep (se 1 (by rfl) ⟨2028716, by rfl⟩ : syracuseStep 2704955 = 4057433) B4057433
theorem B29640293 : Blo 1801602 29640293 := bstep (se 4 (by rfl) ⟨2778777, by rfl⟩ : syracuseStep 29640293 = 5557555) B5557555
theorem B4056695 : Blo 1801602 4056695 := bstep (se 1 (by rfl) ⟨3042521, by rfl⟩ : syracuseStep 4056695 = 6085043) B6085043
theorem B19760759 : Blo 1801602 19760759 := bstep (se 1 (by rfl) ⟨14820569, by rfl⟩ : syracuseStep 19760759 = 29641139) B29641139
theorem B2705015 : Blo 1801602 2705015 := bstep (se 1 (by rfl) ⟨2028761, by rfl⟩ : syracuseStep 2705015 = 4057523) B4057523
theorem B2705039 : Blo 1801602 2705039 := bstep (se 1 (by rfl) ⟨2028779, by rfl⟩ : syracuseStep 2705039 = 4057559) B4057559
theorem B4564633 : Blo 1801602 4564633 := bstep (se 2 (by rfl) ⟨1711737, by rfl⟩ : syracuseStep 4564633 = 3423475) B3423475
theorem B2705081 : Blo 1801602 2705081 := bstep (se 2 (by rfl) ⟨1014405, by rfl⟩ : syracuseStep 2705081 = 2028811) B2028811
theorem B3040969 : Blo 1801602 3040969 := bstep (se 2 (by rfl) ⟨1140363, by rfl⟩ : syracuseStep 3040969 = 2280727) B2280727
theorem B2705159 : Blo 1801602 2705159 := bstep (se 1 (by rfl) ⟨2028869, by rfl⟩ : syracuseStep 2705159 = 4057739) B4057739
theorem B2967311 : Blo 1801602 2967311 := bstep (se 1 (by rfl) ⟨2225483, by rfl⟩ : syracuseStep 2967311 = 4450967) B4450967
theorem B4056875 : Blo 1801602 4056875 := bstep (se 1 (by rfl) ⟨3042656, by rfl⟩ : syracuseStep 4056875 = 6085313) B6085313
theorem B2705195 : Blo 1801602 2705195 := bstep (se 1 (by rfl) ⟨2028896, by rfl⟩ : syracuseStep 2705195 = 4057793) B4057793
theorem B4564795 : Blo 1801602 4564795 := bstep (se 1 (by rfl) ⟨3423596, by rfl⟩ : syracuseStep 4564795 = 6847193) B6847193
theorem B2705225 : Blo 1801602 2705225 := bstep (se 2 (by rfl) ⟨1014459, by rfl⟩ : syracuseStep 2705225 = 2028919) B2028919
theorem B15402905 : Blo 1801602 15402905 := bstep (se 2 (by rfl) ⟨5776089, by rfl⟩ : syracuseStep 15402905 = 11552179) B11552179
theorem B2566075 : Blo 1801602 2566075 := bstep (se 1 (by rfl) ⟨1924556, by rfl⟩ : syracuseStep 2566075 = 3849113) B3849113
theorem B2705339 : Blo 1801602 2705339 := bstep (se 1 (by rfl) ⟨2029004, by rfl⟩ : syracuseStep 2705339 = 4058009) B4058009
theorem B4564937 : Blo 1801602 4564937 := bstep (se 2 (by rfl) ⟨1711851, by rfl⟩ : syracuseStep 4564937 = 3423703) B3423703
theorem B9127889 : Blo 1801602 9127889 := bstep (se 2 (by rfl) ⟨3422958, by rfl⟩ : syracuseStep 9127889 = 6845917) B6845917
theorem B2705399 : Blo 1801602 2705399 := bstep (se 1 (by rfl) ⟨2029049, by rfl⟩ : syracuseStep 2705399 = 4058099) B4058099
theorem B4057235 : Blo 1801602 4057235 := bstep (se 1 (by rfl) ⟨3042926, by rfl⟩ : syracuseStep 4057235 = 6085853) B6085853
theorem B4057289 : Blo 1801602 4057289 := bstep (se 2 (by rfl) ⟨1521483, by rfl⟩ : syracuseStep 4057289 = 3042967) B3042967
theorem B70240517 : Blo 1801602 70240517 := bstep (se 4 (by rfl) ⟨6585048, by rfl⟩ : syracuseStep 70240517 = 13170097) B13170097
theorem B4565281 : Blo 1801602 4565281 := bstep (se 2 (by rfl) ⟨1711980, by rfl⟩ : syracuseStep 4565281 = 3423961) B3423961
theorem B5130611 : Blo 1801602 5130611 := bstep (se 1 (by rfl) ⟨3847958, by rfl⟩ : syracuseStep 5130611 = 7695917) B7695917
theorem B3041671 : Blo 1801602 3041671 := bstep (se 1 (by rfl) ⟨2281253, by rfl⟩ : syracuseStep 3041671 = 4562507) B4562507
theorem B21916109 : Blo 1801602 21916109 := bstep (se 3 (by rfl) ⟨4109270, by rfl⟩ : syracuseStep 21916109 = 8218541) B8218541
theorem B2435599 : Blo 1801602 2435599 := bstep (se 1 (by rfl) ⟨1826699, by rfl⟩ : syracuseStep 2435599 = 3653399) B3653399
theorem B2886187 : Blo 1801602 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B5130839 : Blo 1801602 5130839 := bstep (se 1 (by rfl) ⟨3848129, by rfl⟩ : syracuseStep 5130839 = 7696259) B7696259
theorem B2566775 : Blo 1801602 2566775 := bstep (se 1 (by rfl) ⟨1925081, by rfl⟩ : syracuseStep 2566775 = 3850163) B3850163
theorem B69323525 : Blo 1801602 69323525 := bstep (se 4 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 69323525 = 12998161) B12998161
theorem B29240099 : Blo 1801602 29240099 := bstep (se 1 (by rfl) ⟨21930074, by rfl⟩ : syracuseStep 29240099 = 43860149) B43860149
theorem B2280251 : Blo 1801602 2280251 := bstep (se 1 (by rfl) ⟨1710188, by rfl⟩ : syracuseStep 2280251 = 3420377) B3420377
theorem B2165563 : Blo 1801602 2165563 := bstep (se 1 (by rfl) ⟨1624172, by rfl⟩ : syracuseStep 2165563 = 3248345) B3248345
theorem B4057991 : Blo 1801602 4057991 := bstep (se 1 (by rfl) ⟨3043493, by rfl⟩ : syracuseStep 4057991 = 6086987) B6086987
theorem B3042319 : Blo 1801602 3042319 := bstep (se 1 (by rfl) ⟨2281739, by rfl⟩ : syracuseStep 3042319 = 4563479) B4563479
theorem B6499415 : Blo 1801602 6499415 := bstep (se 1 (by rfl) ⟨4874561, by rfl⟩ : syracuseStep 6499415 = 9749123) B9749123
theorem B13692077 : Blo 1801602 13692077 := bstep (se 3 (by rfl) ⟨2567264, by rfl⟩ : syracuseStep 13692077 = 5134529) B5134529
theorem B2469049 : Blo 1801602 2469049 := bstep (se 2 (by rfl) ⟨925893, by rfl⟩ : syracuseStep 2469049 = 1851787) B1851787
theorem B34639163 : Blo 1801602 34639163 := bstep (se 1 (by rfl) ⟨25979372, by rfl⟩ : syracuseStep 34639163 = 51958745) B51958745
theorem B62418275 : Blo 1801602 62418275 := bstep (se 1 (by rfl) ⟨46813706, by rfl⟩ : syracuseStep 62418275 = 93627413) B93627413
theorem B2026939 : Blo 1801602 2026939 := bstep (se 1 (by rfl) ⟨1520204, by rfl⟩ : syracuseStep 2026939 = 3040409) B3040409
theorem B7704017 : Blo 1801602 7704017 := bstep (se 2 (by rfl) ⟨2889006, by rfl⟩ : syracuseStep 7704017 = 5778013) B5778013
theorem B3042859 : Blo 1801602 3042859 := bstep (se 1 (by rfl) ⟨2282144, by rfl⟩ : syracuseStep 3042859 = 4564289) B4564289
theorem B13684301 : Blo 1801602 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B3043001 : Blo 1801602 3043001 := bstep (se 2 (by rfl) ⟨1141125, by rfl⟩ : syracuseStep 3043001 = 2282251) B2282251
theorem B2281223 : Blo 1801602 2281223 := bstep (se 1 (by rfl) ⟨1710917, by rfl⟩ : syracuseStep 2281223 = 3421835) B3421835
theorem B5205875 : Blo 1801602 5205875 := bstep (se 1 (by rfl) ⟨3904406, by rfl⟩ : syracuseStep 5205875 = 7808813) B7808813
theorem B2027407 : Blo 1801602 2027407 := bstep (se 1 (by rfl) ⟨1520555, by rfl⟩ : syracuseStep 2027407 = 3041111) B3041111
theorem B6082451 : Blo 1801602 6082451 := bstep (se 1 (by rfl) ⟨4561838, by rfl⟩ : syracuseStep 6082451 = 9123677) B9123677
theorem B9129995 : Blo 1801602 9129995 := bstep (se 1 (by rfl) ⟨6847496, by rfl⟩ : syracuseStep 9129995 = 13694993) B13694993
theorem B6844445 : Blo 1801602 6844445 := bstep (se 3 (by rfl) ⟨1283333, by rfl⟩ : syracuseStep 6844445 = 2566667) B2566667
theorem B6844459 : Blo 1801602 6844459 := bstep (se 1 (by rfl) ⟨5133344, by rfl⟩ : syracuseStep 6844459 = 10266689) B10266689
theorem B4329607 : Blo 1801602 4329607 := bstep (se 1 (by rfl) ⟨3247205, by rfl⟩ : syracuseStep 4329607 = 6494411) B6494411
theorem B5132423 : Blo 1801602 5132423 := bstep (se 1 (by rfl) ⟨3849317, by rfl⟩ : syracuseStep 5132423 = 7698635) B7698635
theorem B8663213 : Blo 1801602 8663213 := bstep (se 3 (by rfl) ⟨1624352, by rfl⟩ : syracuseStep 8663213 = 3248705) B3248705
theorem B9130157 : Blo 1801602 9130157 := bstep (se 3 (by rfl) ⟨1711904, by rfl⟩ : syracuseStep 9130157 = 3423809) B3423809
theorem B5132605 : Blo 1801602 5132605 := bstep (se 3 (by rfl) ⟨962363, by rfl⟩ : syracuseStep 5132605 = 1924727) B1924727
theorem B2027911 : Blo 1801602 2027911 := bstep (se 1 (by rfl) ⟨1520933, by rfl⟩ : syracuseStep 2027911 = 3041867) B3041867
theorem B2281871 : Blo 1801602 2281871 := bstep (se 1 (by rfl) ⟨1711403, by rfl⟩ : syracuseStep 2281871 = 3422807) B3422807
theorem B21918251 : Blo 1801602 21918251 := bstep (se 1 (by rfl) ⟨16438688, by rfl⟩ : syracuseStep 21918251 = 32877377) B32877377
theorem B2028091 : Blo 1801602 2028091 := bstep (se 1 (by rfl) ⟨1521068, by rfl⟩ : syracuseStep 2028091 = 3042137) B3042137
theorem B2888327 : Blo 1801602 2888327 := bstep (se 1 (by rfl) ⟨2166245, by rfl⟩ : syracuseStep 2888327 = 4332491) B4332491
theorem B5133071 : Blo 1801602 5133071 := bstep (se 1 (by rfl) ⟨3849803, by rfl⟩ : syracuseStep 5133071 = 7699607) B7699607
theorem B8221499 : Blo 1801602 8221499 := bstep (se 1 (by rfl) ⟨6166124, by rfl⟩ : syracuseStep 8221499 = 12332249) B12332249
theorem B9253721 : Blo 1801602 9253721 := bstep (se 2 (by rfl) ⟨3470145, by rfl⟩ : syracuseStep 9253721 = 6940291) B6940291
theorem B5559155 : Blo 1801602 5559155 := bstep (se 1 (by rfl) ⟨4169366, by rfl⟩ : syracuseStep 5559155 = 8338733) B8338733
theorem B9122705 : Blo 1801602 9122705 := bstep (se 2 (by rfl) ⟨3421014, by rfl⟩ : syracuseStep 9122705 = 6842029) B6842029
theorem B3421129 : Blo 1801602 3421129 := bstep (se 2 (by rfl) ⟨1282923, by rfl⟩ : syracuseStep 3421129 = 2565847) B2565847
theorem B4330511 : Blo 1801602 4330511 := bstep (se 1 (by rfl) ⟨3247883, by rfl⟩ : syracuseStep 4330511 = 6495767) B6495767
theorem B2028559 : Blo 1801602 2028559 := bstep (se 1 (by rfl) ⟨1521419, by rfl⟩ : syracuseStep 2028559 = 3042839) B3042839
theorem B10261565 : Blo 1801602 10261565 := bstep (se 3 (by rfl) ⟨1924043, by rfl⟩ : syracuseStep 10261565 = 3848087) B3848087
theorem B7803965 : Blo 1801602 7803965 := bstep (se 3 (by rfl) ⟨1463243, by rfl⟩ : syracuseStep 7803965 = 2926487) B2926487
theorem B6083855 : Blo 1801602 6083855 := bstep (se 1 (by rfl) ⟨4562891, by rfl⟩ : syracuseStep 6083855 = 9125783) B9125783
theorem B38991203 : Blo 1801602 38991203 := bstep (se 1 (by rfl) ⟨29243402, by rfl⟩ : syracuseStep 38991203 = 58486805) B58486805
theorem B17323469 : Blo 1801602 17323469 := bstep (se 3 (by rfl) ⟨3248150, by rfl⟩ : syracuseStep 17323469 = 6496301) B6496301
theorem B8779229 : Blo 1801602 8779229 := bstep (se 3 (by rfl) ⟨1646105, by rfl⟩ : syracuseStep 8779229 = 3292211) B3292211
theorem B31233539 : Blo 1801602 31233539 := bstep (se 1 (by rfl) ⟨23425154, by rfl⟩ : syracuseStep 31233539 = 46850309) B46850309
theorem B15406595 : Blo 1801602 15406595 := bstep (se 1 (by rfl) ⟨11554946, by rfl⟩ : syracuseStep 15406595 = 23109893) B23109893
theorem B6084125 : Blo 1801602 6084125 := bstep (se 3 (by rfl) ⟨1140773, by rfl⟩ : syracuseStep 6084125 = 2281547) B2281547
theorem B13694507 : Blo 1801602 13694507 := bstep (se 1 (by rfl) ⟨10270880, by rfl⟩ : syracuseStep 13694507 = 20541761) B20541761
theorem B18748993 : Blo 1801602 18748993 := bstep (se 2 (by rfl) ⟨7030872, by rfl⟩ : syracuseStep 18748993 = 14061745) B14061745
theorem B14612035 : Blo 1801602 14612035 := bstep (se 1 (by rfl) ⟨10959026, by rfl⟩ : syracuseStep 14612035 = 21918053) B21918053
theorem B7698361 : Blo 1801602 7698361 := bstep (se 2 (by rfl) ⟨2886885, by rfl⟩ : syracuseStep 7698361 = 5773771) B5773771
theorem B13686731 : Blo 1801602 13686731 := bstep (se 1 (by rfl) ⟨10265048, by rfl⟩ : syracuseStep 13686731 = 20530097) B20530097
theorem B10958813 : Blo 1801602 10958813 := bstep (se 3 (by rfl) ⟨2054777, by rfl⟩ : syracuseStep 10958813 = 4109555) B4109555
theorem B5134337 : Blo 1801602 5134337 := bstep (se 2 (by rfl) ⟨1925376, by rfl⟩ : syracuseStep 5134337 = 3850753) B3850753
theorem B4560907 : Blo 1801602 4560907 := bstep (se 1 (by rfl) ⟨3420680, by rfl⟩ : syracuseStep 4560907 = 6841361) B6841361
theorem B5773373 : Blo 1801602 5773373 := bstep (se 3 (by rfl) ⟨1082507, by rfl⟩ : syracuseStep 5773373 = 2165015) B2165015
theorem B4561049 : Blo 1801602 4561049 := bstep (se 2 (by rfl) ⟨1710393, by rfl⟩ : syracuseStep 4561049 = 3420787) B3420787
theorem B8665289 : Blo 1801602 8665289 := bstep (se 2 (by rfl) ⟨3249483, by rfl⟩ : syracuseStep 8665289 = 6498967) B6498967
theorem B4561211 : Blo 1801602 4561211 := bstep (se 1 (by rfl) ⟨3420908, by rfl⟩ : syracuseStep 4561211 = 6841817) B6841817
theorem B5773835 : Blo 1801602 5773835 := bstep (se 1 (by rfl) ⟨4330376, by rfl⟩ : syracuseStep 5773835 = 8660753) B8660753
theorem B7305757 : Blo 1801602 7305757 := bstep (se 3 (by rfl) ⟨1369829, by rfl⟩ : syracuseStep 7305757 = 2739659) B2739659
theorem B4561555 : Blo 1801602 4561555 := bstep (se 1 (by rfl) ⟨3421166, by rfl⟩ : syracuseStep 4561555 = 6842333) B6842333
theorem B4053689 : Blo 1801602 4053689 := bstep (se 2 (by rfl) ⟨1520133, by rfl⟩ : syracuseStep 4053689 = 3040267) B3040267
theorem B221928133 : Blo 1801602 221928133 := bstep (se 4 (by rfl) ⟨20805762, by rfl⟩ : syracuseStep 221928133 = 41611525) B41611525
theorem B4561697 : Blo 1801602 4561697 := bstep (se 2 (by rfl) ⟨1710636, by rfl⟩ : syracuseStep 4561697 = 3421273) B3421273
theorem B3423035 : Blo 1801602 3423035 := bstep (se 1 (by rfl) ⟨2567276, by rfl⟩ : syracuseStep 3423035 = 5134553) B5134553
theorem B6085529 : Blo 1801602 6085529 := bstep (se 2 (by rfl) ⟨2282073, by rfl⟩ : syracuseStep 6085529 = 4564147) B4564147
theorem B4627385 : Blo 1801602 4627385 := bstep (se 2 (by rfl) ⟨1735269, by rfl⟩ : syracuseStep 4627385 = 3470539) B3470539
theorem B9124811 : Blo 1801602 9124811 := bstep (se 1 (by rfl) ⟨6843608, by rfl⟩ : syracuseStep 9124811 = 13687217) B13687217
theorem B4054031 : Blo 1801602 4054031 := bstep (se 1 (by rfl) ⟨3040523, by rfl⟩ : syracuseStep 4054031 = 6081047) B6081047
theorem B4054049 : Blo 1801602 4054049 := bstep (se 2 (by rfl) ⟨1520268, by rfl⟩ : syracuseStep 4054049 = 3040537) B3040537
theorem B3849275 : Blo 1801602 3849275 := bstep (se 1 (by rfl) ⟨2886956, by rfl⟩ : syracuseStep 3849275 = 5773913) B5773913
theorem B2702471 : Blo 1801602 2702471 := bstep (se 1 (by rfl) ⟨2026853, by rfl⟩ : syracuseStep 2702471 = 4053707) B4053707
theorem B2702507 : Blo 1801602 2702507 := bstep (se 1 (by rfl) ⟨2026880, by rfl⟩ : syracuseStep 2702507 = 4053761) B4053761
theorem B1924283 : Blo 1801602 1924283 := bstep (se 1 (by rfl) ⟨1443212, by rfl⟩ : syracuseStep 1924283 = 2886425) B2886425
theorem B2702537 : Blo 1801602 2702537 := bstep (se 2 (by rfl) ⟨1013451, by rfl⟩ : syracuseStep 2702537 = 2026903) B2026903
theorem B9125135 : Blo 1801602 9125135 := bstep (se 1 (by rfl) ⟨6843851, by rfl⟩ : syracuseStep 9125135 = 13687703) B13687703
theorem B3423521 : Blo 1801602 3423521 := bstep (se 2 (by rfl) ⟨1283820, by rfl⟩ : syracuseStep 3423521 = 2567641) B2567641
theorem B2702651 : Blo 1801602 2702651 := bstep (se 1 (by rfl) ⟨2026988, by rfl⟩ : syracuseStep 2702651 = 4053977) B4053977
theorem B2702711 : Blo 1801602 2702711 := bstep (se 1 (by rfl) ⟨2027033, by rfl⟩ : syracuseStep 2702711 = 4054067) B4054067
theorem B4054391 : Blo 1801602 4054391 := bstep (se 1 (by rfl) ⟨3040793, by rfl⟩ : syracuseStep 4054391 = 6081587) B6081587
theorem B43875715 : Blo 1801602 43875715 := bstep (se 1 (by rfl) ⟨32906786, by rfl⟩ : syracuseStep 43875715 = 65813573) B65813573
theorem B1801607 : Blo 1801602 1801607 := bstep (se 1 (by rfl) ⟨1351205, by rfl⟩ : syracuseStep 1801607 = 2702411) B2702411
theorem B19479943 : Blo 1801602 19479943 := bstep (se 1 (by rfl) ⟨14609957, by rfl⟩ : syracuseStep 19479943 = 29219915) B29219915
theorem B6495623 : Blo 1801602 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B1801615 : Blo 1801602 1801615 := bstep (se 1 (by rfl) ⟨1351211, by rfl⟩ : syracuseStep 1801615 = 2702423) B2702423
theorem B2702735 : Blo 1801602 2702735 := bstep (se 1 (by rfl) ⟨2027051, by rfl⟩ : syracuseStep 2702735 = 4054103) B4054103
theorem B10263955 : Blo 1801602 10263955 := bstep (se 1 (by rfl) ⟨7697966, by rfl⟩ : syracuseStep 10263955 = 15395933) B15395933
theorem B4873619 : Blo 1801602 4873619 := bstep (se 1 (by rfl) ⟨3655214, by rfl⟩ : syracuseStep 4873619 = 7310429) B7310429
theorem B2702777 : Blo 1801602 2702777 := bstep (se 2 (by rfl) ⟨1013541, by rfl⟩ : syracuseStep 2702777 = 2027083) B2027083
theorem B1801659 : Blo 1801602 1801659 := bstep (se 1 (by rfl) ⟨1351244, by rfl⟩ : syracuseStep 1801659 = 2702489) B2702489
theorem B1801735 : Blo 1801602 1801735 := bstep (se 1 (by rfl) ⟨1351301, by rfl⟩ : syracuseStep 1801735 = 2702603) B2702603
theorem B2702855 : Blo 1801602 2702855 := bstep (se 1 (by rfl) ⟨2027141, by rfl⟩ : syracuseStep 2702855 = 4054283) B4054283
theorem B1801743 : Blo 1801602 1801743 := bstep (se 1 (by rfl) ⟨1351307, by rfl⟩ : syracuseStep 1801743 = 2702615) B2702615
theorem B2702891 : Blo 1801602 2702891 := bstep (se 1 (by rfl) ⟨2027168, by rfl⟩ : syracuseStep 2702891 = 4054337) B4054337
theorem B4054571 : Blo 1801602 4054571 := bstep (se 1 (by rfl) ⟨3040928, by rfl⟩ : syracuseStep 4054571 = 6081857) B6081857
theorem B1801787 : Blo 1801602 1801787 := bstep (se 1 (by rfl) ⟨1351340, by rfl⟩ : syracuseStep 1801787 = 2702681) B2702681
theorem B2702921 : Blo 1801602 2702921 := bstep (se 2 (by rfl) ⟨1013595, by rfl⟩ : syracuseStep 2702921 = 2027191) B2027191
theorem B6086231 : Blo 1801602 6086231 := bstep (se 1 (by rfl) ⟨4564673, by rfl⟩ : syracuseStep 6086231 = 9129347) B9129347
theorem B5135987 : Blo 1801602 5135987 := bstep (se 1 (by rfl) ⟨3851990, by rfl⟩ : syracuseStep 5135987 = 7703981) B7703981
theorem B3423863 : Blo 1801602 3423863 := bstep (se 1 (by rfl) ⟨2567897, by rfl⟩ : syracuseStep 3423863 = 5135795) B5135795
theorem B1801863 : Blo 1801602 1801863 := bstep (se 1 (by rfl) ⟨1351397, by rfl⟩ : syracuseStep 1801863 = 2702795) B2702795
theorem B1801871 : Blo 1801602 1801871 := bstep (se 1 (by rfl) ⟨1351403, by rfl⟩ : syracuseStep 1801871 = 2702807) B2702807
theorem B1801915 : Blo 1801602 1801915 := bstep (se 1 (by rfl) ⟨1351436, by rfl⟩ : syracuseStep 1801915 = 2702873) B2702873
theorem B2703035 : Blo 1801602 2703035 := bstep (se 1 (by rfl) ⟨2027276, by rfl⟩ : syracuseStep 2703035 = 4054553) B4054553
theorem B11550437 : Blo 1801602 11550437 := bstep (se 4 (by rfl) ⟨1082853, by rfl⟩ : syracuseStep 11550437 = 2165707) B2165707
theorem B2703095 : Blo 1801602 2703095 := bstep (se 1 (by rfl) ⟨2027321, by rfl⟩ : syracuseStep 2703095 = 4054643) B4054643
theorem B4562689 : Blo 1801602 4562689 := bstep (se 2 (by rfl) ⟨1711008, by rfl⟩ : syracuseStep 4562689 = 3422017) B3422017
theorem B1801991 : Blo 1801602 1801991 := bstep (se 1 (by rfl) ⟨1351493, by rfl⟩ : syracuseStep 1801991 = 2702987) B2702987
theorem B1801999 : Blo 1801602 1801999 := bstep (se 1 (by rfl) ⟨1351499, by rfl⟩ : syracuseStep 1801999 = 2702999) B2702999
theorem B2703119 : Blo 1801602 2703119 := bstep (se 1 (by rfl) ⟨2027339, by rfl⟩ : syracuseStep 2703119 = 4054679) B4054679
theorem B16449317 : Blo 1801602 16449317 := bstep (se 4 (by rfl) ⟨1542123, by rfl⟩ : syracuseStep 16449317 = 3084247) B3084247
theorem B2703161 : Blo 1801602 2703161 := bstep (se 2 (by rfl) ⟨1013685, by rfl⟩ : syracuseStep 2703161 = 2027371) B2027371
theorem B1802043 : Blo 1801602 1802043 := bstep (se 1 (by rfl) ⟨1351532, by rfl⟩ : syracuseStep 1802043 = 2703065) B2703065
theorem B1802119 : Blo 1801602 1802119 := bstep (se 1 (by rfl) ⟨1351589, by rfl⟩ : syracuseStep 1802119 = 2703179) B2703179
theorem B2703239 : Blo 1801602 2703239 := bstep (se 1 (by rfl) ⟨2027429, by rfl⟩ : syracuseStep 2703239 = 4054859) B4054859
theorem B7700359 : Blo 1801602 7700359 := bstep (se 1 (by rfl) ⟨5775269, by rfl⟩ : syracuseStep 7700359 = 11550539) B11550539
theorem B1802127 : Blo 1801602 1802127 := bstep (se 1 (by rfl) ⟨1351595, by rfl⟩ : syracuseStep 1802127 = 2703191) B2703191
theorem B4054931 : Blo 1801602 4054931 := bstep (se 1 (by rfl) ⟨3041198, by rfl⟩ : syracuseStep 4054931 = 6082397) B6082397
theorem B11116435 : Blo 1801602 11116435 := bstep (se 1 (by rfl) ⟨8337326, by rfl⟩ : syracuseStep 11116435 = 16674653) B16674653
theorem B2703275 : Blo 1801602 2703275 := bstep (se 1 (by rfl) ⟨2027456, by rfl⟩ : syracuseStep 2703275 = 4054913) B4054913
theorem B1802171 : Blo 1801602 1802171 := bstep (se 1 (by rfl) ⟨1351628, by rfl⟩ : syracuseStep 1802171 = 2703257) B2703257
theorem B2703305 : Blo 1801602 2703305 := bstep (se 2 (by rfl) ⟨1013739, by rfl⟩ : syracuseStep 2703305 = 2027479) B2027479
theorem B4054985 : Blo 1801602 4054985 := bstep (se 2 (by rfl) ⟨1520619, by rfl⟩ : syracuseStep 4054985 = 3041239) B3041239
theorem B6086663 : Blo 1801602 6086663 := bstep (se 1 (by rfl) ⟨4564997, by rfl⟩ : syracuseStep 6086663 = 9129995) B9129995
theorem B4562963 : Blo 1801602 4562963 := bstep (se 1 (by rfl) ⟨3422222, by rfl⟩ : syracuseStep 4562963 = 6844445) B6844445
theorem B1802279 : Blo 1801602 1802279 := bstep (se 1 (by rfl) ⟨1351709, by rfl⟩ : syracuseStep 1802279 = 2703419) B2703419
theorem B9125945 : Blo 1801602 9125945 := bstep (se 2 (by rfl) ⟨3422229, by rfl⟩ : syracuseStep 9125945 = 6844459) B6844459
theorem B1802319 : Blo 1801602 1802319 := bstep (se 1 (by rfl) ⟨1351739, by rfl⟩ : syracuseStep 1802319 = 2703479) B2703479
theorem B1802335 : Blo 1801602 1802335 := bstep (se 1 (by rfl) ⟨1351751, by rfl⟩ : syracuseStep 1802335 = 2703503) B2703503
theorem B5775475 : Blo 1801602 5775475 := bstep (se 1 (by rfl) ⟨4331606, by rfl⟩ : syracuseStep 5775475 = 8663213) B8663213
theorem B6086771 : Blo 1801602 6086771 := bstep (se 1 (by rfl) ⟨4565078, by rfl⟩ : syracuseStep 6086771 = 9130157) B9130157
theorem B1802363 : Blo 1801602 1802363 := bstep (se 1 (by rfl) ⟨1351772, by rfl⟩ : syracuseStep 1802363 = 2703545) B2703545
theorem B3850411 : Blo 1801602 3850411 := bstep (se 1 (by rfl) ⟨2887808, by rfl⟩ : syracuseStep 3850411 = 5775617) B5775617
theorem B1802415 : Blo 1801602 1802415 := bstep (se 1 (by rfl) ⟨1351811, by rfl⟩ : syracuseStep 1802415 = 2703623) B2703623
theorem B1802439 : Blo 1801602 1802439 := bstep (se 1 (by rfl) ⟨1351829, by rfl⟩ : syracuseStep 1802439 = 2703659) B2703659
theorem B1802459 : Blo 1801602 1802459 := bstep (se 1 (by rfl) ⟨1351844, by rfl⟩ : syracuseStep 1802459 = 2703689) B2703689
theorem B1802535 : Blo 1801602 1802535 := bstep (se 1 (by rfl) ⟨1351901, by rfl⟩ : syracuseStep 1802535 = 2703803) B2703803
theorem B1802575 : Blo 1801602 1802575 := bstep (se 1 (by rfl) ⟨1351931, by rfl⟩ : syracuseStep 1802575 = 2703863) B2703863
theorem B1802591 : Blo 1801602 1802591 := bstep (se 1 (by rfl) ⟨1351943, by rfl⟩ : syracuseStep 1802591 = 2703887) B2703887
theorem B1802619 : Blo 1801602 1802619 := bstep (se 1 (by rfl) ⟨1351964, by rfl⟩ : syracuseStep 1802619 = 2703929) B2703929
theorem B6087041 : Blo 1801602 6087041 := bstep (se 2 (by rfl) ⟨2282640, by rfl⟩ : syracuseStep 6087041 = 4565281) B4565281
theorem B2703791 : Blo 1801602 2703791 := bstep (se 1 (by rfl) ⟨2027843, by rfl⟩ : syracuseStep 2703791 = 4055687) B4055687
theorem B1802671 : Blo 1801602 1802671 := bstep (se 1 (by rfl) ⟨1352003, by rfl⟩ : syracuseStep 1802671 = 2704007) B2704007
theorem B1925551 : Blo 1801602 1925551 := bstep (se 1 (by rfl) ⟨1444163, by rfl⟩ : syracuseStep 1925551 = 2888327) B2888327
theorem B1802695 : Blo 1801602 1802695 := bstep (se 1 (by rfl) ⟨1352021, by rfl⟩ : syracuseStep 1802695 = 2704043) B2704043
theorem B1802715 : Blo 1801602 1802715 := bstep (se 1 (by rfl) ⟨1352036, by rfl⟩ : syracuseStep 1802715 = 2704073) B2704073
theorem B4055561 : Blo 1801602 4055561 := bstep (se 2 (by rfl) ⟨1520835, by rfl⟩ : syracuseStep 4055561 = 3041671) B3041671
theorem B2703881 : Blo 1801602 2703881 := bstep (se 2 (by rfl) ⟨1013955, by rfl⟩ : syracuseStep 2703881 = 2027911) B2027911
theorem B5480999 : Blo 1801602 5480999 := bstep (se 1 (by rfl) ⟨4110749, by rfl⟩ : syracuseStep 5480999 = 8221499) B8221499
theorem B2703911 : Blo 1801602 2703911 := bstep (se 1 (by rfl) ⟨2027933, by rfl⟩ : syracuseStep 2703911 = 4055867) B4055867
theorem B1802791 : Blo 1801602 1802791 := bstep (se 1 (by rfl) ⟨1352093, by rfl⟩ : syracuseStep 1802791 = 2704187) B2704187
theorem B1802831 : Blo 1801602 1802831 := bstep (se 1 (by rfl) ⟨1352123, by rfl⟩ : syracuseStep 1802831 = 2704247) B2704247
theorem B1802847 : Blo 1801602 1802847 := bstep (se 1 (by rfl) ⟨1352135, by rfl⟩ : syracuseStep 1802847 = 2704271) B2704271
theorem B2703995 : Blo 1801602 2703995 := bstep (se 1 (by rfl) ⟨2027996, by rfl⟩ : syracuseStep 2703995 = 4055993) B4055993
theorem B1802875 : Blo 1801602 1802875 := bstep (se 1 (by rfl) ⟨1352156, by rfl⟩ : syracuseStep 1802875 = 2704313) B2704313
theorem B1802927 : Blo 1801602 1802927 := bstep (se 1 (by rfl) ⟨1352195, by rfl⟩ : syracuseStep 1802927 = 2704391) B2704391
theorem B4752071 : Blo 1801602 4752071 := bstep (se 1 (by rfl) ⟨3564053, by rfl⟩ : syracuseStep 4752071 = 7128107) B7128107
theorem B1802951 : Blo 1801602 1802951 := bstep (se 1 (by rfl) ⟨1352213, by rfl⟩ : syracuseStep 1802951 = 2704427) B2704427
theorem B6841043 : Blo 1801602 6841043 := bstep (se 1 (by rfl) ⟨5130782, by rfl⟩ : syracuseStep 6841043 = 10261565) B10261565
theorem B5202643 : Blo 1801602 5202643 := bstep (se 1 (by rfl) ⟨3901982, by rfl⟩ : syracuseStep 5202643 = 7803965) B7803965
theorem B1802971 : Blo 1801602 1802971 := bstep (se 1 (by rfl) ⟨1352228, by rfl⟩ : syracuseStep 1802971 = 2704457) B2704457
theorem B2704121 : Blo 1801602 2704121 := bstep (se 2 (by rfl) ⟨1014045, by rfl⟩ : syracuseStep 2704121 = 2028091) B2028091
theorem B1803047 : Blo 1801602 1803047 := bstep (se 1 (by rfl) ⟨1352285, by rfl⟩ : syracuseStep 1803047 = 2704571) B2704571
theorem B1803087 : Blo 1801602 1803087 := bstep (se 1 (by rfl) ⟨1352315, by rfl⟩ : syracuseStep 1803087 = 2704631) B2704631
theorem B4055903 : Blo 1801602 4055903 := bstep (se 1 (by rfl) ⟨3041927, by rfl⟩ : syracuseStep 4055903 = 6083855) B6083855
theorem B2704223 : Blo 1801602 2704223 := bstep (se 1 (by rfl) ⟨2028167, by rfl⟩ : syracuseStep 2704223 = 4056335) B4056335
theorem B1803103 : Blo 1801602 1803103 := bstep (se 1 (by rfl) ⟨1352327, by rfl⟩ : syracuseStep 1803103 = 2704655) B2704655
theorem B2704235 : Blo 1801602 2704235 := bstep (se 1 (by rfl) ⟨2028176, by rfl⟩ : syracuseStep 2704235 = 4056353) B4056353
theorem B1803131 : Blo 1801602 1803131 := bstep (se 1 (by rfl) ⟨1352348, by rfl⟩ : syracuseStep 1803131 = 2704697) B2704697
theorem B25994135 : Blo 1801602 25994135 := bstep (se 1 (by rfl) ⟨19495601, by rfl⟩ : syracuseStep 25994135 = 38991203) B38991203
theorem B1803183 : Blo 1801602 1803183 := bstep (se 1 (by rfl) ⟨1352387, by rfl⟩ : syracuseStep 1803183 = 2704775) B2704775
theorem B295904177 : Blo 1801602 295904177 := bstep (se 2 (by rfl) ⟨110964066, by rfl⟩ : syracuseStep 295904177 = 221928133) B221928133
theorem B1803207 : Blo 1801602 1803207 := bstep (se 1 (by rfl) ⟨1352405, by rfl⟩ : syracuseStep 1803207 = 2704811) B2704811
theorem B1803227 : Blo 1801602 1803227 := bstep (se 1 (by rfl) ⟨1352420, by rfl⟩ : syracuseStep 1803227 = 2704841) B2704841
theorem B4056083 : Blo 1801602 4056083 := bstep (se 1 (by rfl) ⟨3042062, by rfl⟩ : syracuseStep 4056083 = 6084125) B6084125
theorem B3654695 : Blo 1801602 3654695 := bstep (se 1 (by rfl) ⟨2741021, by rfl⟩ : syracuseStep 3654695 = 5482043) B5482043
theorem B1803303 : Blo 1801602 1803303 := bstep (se 1 (by rfl) ⟨1352477, by rfl⟩ : syracuseStep 1803303 = 2704955) B2704955
theorem B19760195 : Blo 1801602 19760195 := bstep (se 1 (by rfl) ⟨14820146, by rfl⟩ : syracuseStep 19760195 = 29640293) B29640293
theorem B2704463 : Blo 1801602 2704463 := bstep (se 1 (by rfl) ⟨2028347, by rfl⟩ : syracuseStep 2704463 = 4056695) B4056695
theorem B13173839 : Blo 1801602 13173839 := bstep (se 1 (by rfl) ⟨9880379, by rfl⟩ : syracuseStep 13173839 = 19760759) B19760759
theorem B1803343 : Blo 1801602 1803343 := bstep (se 1 (by rfl) ⟨1352507, by rfl⟩ : syracuseStep 1803343 = 2705015) B2705015
theorem B1803359 : Blo 1801602 1803359 := bstep (se 1 (by rfl) ⟨1352519, by rfl⟩ : syracuseStep 1803359 = 2705039) B2705039
theorem B1803387 : Blo 1801602 1803387 := bstep (se 1 (by rfl) ⟨1352540, by rfl⟩ : syracuseStep 1803387 = 2705081) B2705081
theorem B1803439 : Blo 1801602 1803439 := bstep (se 1 (by rfl) ⟨1352579, by rfl⟩ : syracuseStep 1803439 = 2705159) B2705159
theorem B2704583 : Blo 1801602 2704583 := bstep (se 1 (by rfl) ⟨2028437, by rfl⟩ : syracuseStep 2704583 = 4056875) B4056875
theorem B1803463 : Blo 1801602 1803463 := bstep (se 1 (by rfl) ⟨1352597, by rfl⟩ : syracuseStep 1803463 = 2705195) B2705195
theorem B1803483 : Blo 1801602 1803483 := bstep (se 1 (by rfl) ⟨1352612, by rfl⟩ : syracuseStep 1803483 = 2705225) B2705225
theorem B1803559 : Blo 1801602 1803559 := bstep (se 1 (by rfl) ⟨1352669, by rfl⟩ : syracuseStep 1803559 = 2705339) B2705339
theorem B1803599 : Blo 1801602 1803599 := bstep (se 1 (by rfl) ⟨1352699, by rfl⟩ : syracuseStep 1803599 = 2705399) B2705399
theorem B4056425 : Blo 1801602 4056425 := bstep (se 2 (by rfl) ⟨1521159, by rfl⟩ : syracuseStep 4056425 = 3042319) B3042319
theorem B2704745 : Blo 1801602 2704745 := bstep (se 2 (by rfl) ⟨1014279, by rfl⟩ : syracuseStep 2704745 = 2028559) B2028559
theorem B2704823 : Blo 1801602 2704823 := bstep (se 1 (by rfl) ⟨2028617, by rfl⟩ : syracuseStep 2704823 = 4057235) B4057235
theorem B3040699 : Blo 1801602 3040699 := bstep (se 1 (by rfl) ⟨2280524, by rfl⟩ : syracuseStep 3040699 = 4561049) B4561049
theorem B23102921 : Blo 1801602 23102921 := bstep (se 2 (by rfl) ⟨8663595, by rfl⟩ : syracuseStep 23102921 = 17327191) B17327191
theorem B5776859 : Blo 1801602 5776859 := bstep (se 1 (by rfl) ⟨4332644, by rfl⟩ : syracuseStep 5776859 = 8665289) B8665289
theorem B2704859 : Blo 1801602 2704859 := bstep (se 1 (by rfl) ⟨2028644, by rfl⟩ : syracuseStep 2704859 = 4057289) B4057289
theorem B46827011 : Blo 1801602 46827011 := bstep (se 1 (by rfl) ⟨35120258, by rfl⟩ : syracuseStep 46827011 = 70240517) B70240517
theorem B3040807 : Blo 1801602 3040807 := bstep (se 1 (by rfl) ⟨2280605, by rfl⟩ : syracuseStep 3040807 = 4561211) B4561211
theorem B58500953 : Blo 1801602 58500953 := bstep (se 2 (by rfl) ⟨21937857, by rfl⟩ : syracuseStep 58500953 = 43875715) B43875715
theorem B3041131 : Blo 1801602 3041131 := bstep (se 1 (by rfl) ⟨2280848, by rfl⟩ : syracuseStep 3041131 = 4561697) B4561697
theorem B2705327 : Blo 1801602 2705327 := bstep (se 1 (by rfl) ⟨2028995, by rfl⟩ : syracuseStep 2705327 = 4057991) B4057991
theorem B4057019 : Blo 1801602 4057019 := bstep (se 1 (by rfl) ⟨3042764, by rfl⟩ : syracuseStep 4057019 = 6085529) B6085529
theorem B2566183 : Blo 1801602 2566183 := bstep (se 1 (by rfl) ⟨1924637, by rfl⟩ : syracuseStep 2566183 = 3849275) B3849275
theorem B4057145 : Blo 1801602 4057145 := bstep (se 2 (by rfl) ⟨1521429, by rfl⟩ : syracuseStep 4057145 = 3042859) B3042859
theorem B19482713 : Blo 1801602 19482713 := bstep (se 2 (by rfl) ⟨7306017, by rfl⟩ : syracuseStep 19482713 = 14612035) B14612035
theorem B9128051 : Blo 1801602 9128051 := bstep (se 1 (by rfl) ⟨6846038, by rfl⟩ : syracuseStep 9128051 = 13692077) B13692077
theorem B6080669 : Blo 1801602 6080669 := bstep (se 3 (by rfl) ⟨1140125, by rfl⟩ : syracuseStep 6080669 = 2280251) B2280251
theorem B24676589 : Blo 1801602 24676589 := bstep (se 3 (by rfl) ⟨4626860, by rfl⟩ : syracuseStep 24676589 = 9253721) B9253721
theorem B4057487 : Blo 1801602 4057487 := bstep (se 1 (by rfl) ⟨3043115, by rfl⟩ : syracuseStep 4057487 = 6086231) B6086231
theorem B10267145 : Blo 1801602 10267145 := bstep (se 2 (by rfl) ⟨3850179, by rfl⟩ : syracuseStep 10267145 = 7700359) B7700359
theorem B14821913 : Blo 1801602 14821913 := bstep (se 2 (by rfl) ⟨5558217, by rfl⟩ : syracuseStep 14821913 = 11116435) B11116435
theorem B6081209 : Blo 1801602 6081209 := bstep (se 2 (by rfl) ⟨2280453, by rfl⟩ : syracuseStep 6081209 = 4560907) B4560907
theorem B6499025 : Blo 1801602 6499025 := bstep (se 2 (by rfl) ⟨2437134, by rfl⟩ : syracuseStep 6499025 = 4874269) B4874269
theorem B4057811 : Blo 1801602 4057811 := bstep (se 1 (by rfl) ⟨3043358, by rfl⟩ : syracuseStep 4057811 = 6086717) B6086717
theorem B38964037 : Blo 1801602 38964037 := bstep (se 4 (by rfl) ⟨3652878, by rfl⟩ : syracuseStep 38964037 = 7305757) B7305757
theorem B3042191 : Blo 1801602 3042191 := bstep (se 1 (by rfl) ⟨2281643, by rfl⟩ : syracuseStep 3042191 = 4563287) B4563287
theorem B19786679 : Blo 1801602 19786679 := bstep (se 1 (by rfl) ⟨14840009, by rfl⟩ : syracuseStep 19786679 = 29680019) B29680019
theorem B6843473 : Blo 1801602 6843473 := bstep (se 2 (by rfl) ⟨2566302, by rfl⟩ : syracuseStep 6843473 = 5132605) B5132605
theorem B3042427 : Blo 1801602 3042427 := bstep (se 1 (by rfl) ⟨2281820, by rfl⟩ : syracuseStep 3042427 = 4563641) B4563641
theorem B5131421 : Blo 1801602 5131421 := bstep (se 3 (by rfl) ⟨962141, by rfl⟩ : syracuseStep 5131421 = 1924283) B1924283
theorem B3706103 : Blo 1801602 3706103 := bstep (se 1 (by rfl) ⟨2779577, by rfl⟩ : syracuseStep 3706103 = 5559155) B5559155
theorem B6081803 : Blo 1801602 6081803 := bstep (se 1 (by rfl) ⟨4561352, by rfl⟩ : syracuseStep 6081803 = 9122705) B9122705
theorem B2887007 : Blo 1801602 2887007 := bstep (se 1 (by rfl) ⟨2165255, by rfl⟩ : syracuseStep 2887007 = 4330511) B4330511
theorem B3247465 : Blo 1801602 3247465 := bstep (se 2 (by rfl) ⟨1217799, by rfl⟩ : syracuseStep 3247465 = 2435599) B2435599
theorem B6843791 : Blo 1801602 6843791 := bstep (se 1 (by rfl) ⟨5132843, by rfl⟩ : syracuseStep 6843791 = 10265687) B10265687
theorem B10268147 : Blo 1801602 10268147 := bstep (se 1 (by rfl) ⟨7701110, by rfl⟩ : syracuseStep 10268147 = 15402221) B15402221
theorem B25996787 : Blo 1801602 25996787 := bstep (se 1 (by rfl) ⟨19497590, by rfl⟩ : syracuseStep 25996787 = 38995181) B38995181
theorem B6082073 : Blo 1801602 6082073 := bstep (se 2 (by rfl) ⟨2280777, by rfl⟩ : syracuseStep 6082073 = 4561555) B4561555
theorem B2027047 : Blo 1801602 2027047 := bstep (se 1 (by rfl) ⟨1520285, by rfl⟩ : syracuseStep 2027047 = 3040571) B3040571
theorem B13168261 : Blo 1801602 13168261 := bstep (se 4 (by rfl) ⟨1234524, by rfl⟩ : syracuseStep 13168261 = 2469049) B2469049
theorem B8662673 : Blo 1801602 8662673 := bstep (se 2 (by rfl) ⟨3248502, by rfl⟩ : syracuseStep 8662673 = 6497005) B6497005
theorem B5852819 : Blo 1801602 5852819 := bstep (se 1 (by rfl) ⟨4389614, by rfl⟩ : syracuseStep 5852819 = 8779229) B8779229
theorem B13692563 : Blo 1801602 13692563 := bstep (se 1 (by rfl) ⟨10269422, by rfl⟩ : syracuseStep 13692563 = 20538845) B20538845
theorem B9129671 : Blo 1801602 9129671 := bstep (se 1 (by rfl) ⟨6847253, by rfl⟩ : syracuseStep 9129671 = 13694507) B13694507
theorem B2887417 : Blo 1801602 2887417 := bstep (se 2 (by rfl) ⟨1082781, by rfl⟩ : syracuseStep 2887417 = 2165563) B2165563
theorem B55529333 : Blo 1801602 55529333 := bstep (se 5 (by rfl) ⟨2602937, by rfl⟩ : syracuseStep 55529333 = 5205875) B5205875
theorem B10268603 : Blo 1801602 10268603 := bstep (se 1 (by rfl) ⟨7701452, by rfl⟩ : syracuseStep 10268603 = 15402905) B15402905
theorem B3043291 : Blo 1801602 3043291 := bstep (se 1 (by rfl) ⟨2282468, by rfl⟩ : syracuseStep 3043291 = 4564937) B4564937
theorem B3420407 : Blo 1801602 3420407 := bstep (se 1 (by rfl) ⟨2565305, by rfl⟩ : syracuseStep 3420407 = 5130611) B5130611
theorem B14610739 : Blo 1801602 14610739 := bstep (se 1 (by rfl) ⟨10958054, by rfl⟩ : syracuseStep 14610739 = 21916109) B21916109
theorem B6844733 : Blo 1801602 6844733 := bstep (se 3 (by rfl) ⟨1283387, by rfl⟩ : syracuseStep 6844733 = 2566775) B2566775
theorem B3420559 : Blo 1801602 3420559 := bstep (se 1 (by rfl) ⟨2565419, by rfl⟩ : syracuseStep 3420559 = 5130839) B5130839
theorem B46215683 : Blo 1801602 46215683 := bstep (se 1 (by rfl) ⟨34661762, by rfl⟩ : syracuseStep 46215683 = 69323525) B69323525
theorem B25973257 : Blo 1801602 25973257 := bstep (se 2 (by rfl) ⟨9739971, by rfl⟩ : syracuseStep 25973257 = 19479943) B19479943
theorem B19493399 : Blo 1801602 19493399 := bstep (se 1 (by rfl) ⟨14620049, by rfl⟩ : syracuseStep 19493399 = 29240099) B29240099
theorem B13685273 : Blo 1801602 13685273 := bstep (se 2 (by rfl) ⟨5131977, by rfl⟩ : syracuseStep 13685273 = 10263955) B10263955
theorem B2282023 : Blo 1801602 2282023 := bstep (se 1 (by rfl) ⟨1711517, by rfl⟩ : syracuseStep 2282023 = 3423035) B3423035
theorem B3084923 : Blo 1801602 3084923 := bstep (se 1 (by rfl) ⟨2313692, by rfl⟩ : syracuseStep 3084923 = 4627385) B4627385
theorem B6083207 : Blo 1801602 6083207 := bstep (se 1 (by rfl) ⟨4562405, by rfl⟩ : syracuseStep 6083207 = 9124811) B9124811
theorem B6083261 : Blo 1801602 6083261 := bstep (se 3 (by rfl) ⟨1140611, by rfl⟩ : syracuseStep 6083261 = 2281223) B2281223
theorem B24998657 : Blo 1801602 24998657 := bstep (se 2 (by rfl) ⟨9374496, by rfl⟩ : syracuseStep 24998657 = 18748993) B18748993
theorem B6083423 : Blo 1801602 6083423 := bstep (se 1 (by rfl) ⟨4562567, by rfl⟩ : syracuseStep 6083423 = 9125135) B9125135
theorem B2282347 : Blo 1801602 2282347 := bstep (se 1 (by rfl) ⟨1711760, by rfl⟩ : syracuseStep 2282347 = 3423521) B3423521
theorem B41612183 : Blo 1801602 41612183 := bstep (se 1 (by rfl) ⟨31209137, by rfl⟩ : syracuseStep 41612183 = 62418275) B62418275
theorem B4330415 : Blo 1801602 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B3249079 : Blo 1801602 3249079 := bstep (se 1 (by rfl) ⟨2436809, by rfl⟩ : syracuseStep 3249079 = 4873619) B4873619
theorem B6083585 : Blo 1801602 6083585 := bstep (se 2 (by rfl) ⟨2281344, by rfl⟩ : syracuseStep 6083585 = 4562689) B4562689
theorem B9122867 : Blo 1801602 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B2282575 : Blo 1801602 2282575 := bstep (se 1 (by rfl) ⟨1711931, by rfl⟩ : syracuseStep 2282575 = 3423863) B3423863
theorem B2028667 : Blo 1801602 2028667 := bstep (se 1 (by rfl) ⟨1521500, by rfl⟩ : syracuseStep 2028667 = 3043001) B3043001
theorem B10966211 : Blo 1801602 10966211 := bstep (se 1 (by rfl) ⟨8224658, by rfl⟩ : syracuseStep 10966211 = 16449317) B16449317
theorem B3421433 : Blo 1801602 3421433 := bstep (se 2 (by rfl) ⟨1283037, by rfl⟩ : syracuseStep 3421433 = 2566075) B2566075
theorem B29627795 : Blo 1801602 29627795 := bstep (se 1 (by rfl) ⟨22220846, by rfl⟩ : syracuseStep 29627795 = 44441693) B44441693
theorem B25974179 : Blo 1801602 25974179 := bstep (se 1 (by rfl) ⟨19480634, by rfl⟩ : syracuseStep 25974179 = 38961269) B38961269
theorem B3421615 : Blo 1801602 3421615 := bstep (se 1 (by rfl) ⟨2566211, by rfl⟩ : syracuseStep 3421615 = 5132423) B5132423
theorem B4560371 : Blo 1801602 4560371 := bstep (se 1 (by rfl) ⟨3420278, by rfl⟩ : syracuseStep 4560371 = 6840557) B6840557
theorem B5772809 : Blo 1801602 5772809 := bstep (se 2 (by rfl) ⟨2164803, by rfl⟩ : syracuseStep 5772809 = 4329607) B4329607
theorem B4560583 : Blo 1801602 4560583 := bstep (se 1 (by rfl) ⟨3420437, by rfl⟩ : syracuseStep 4560583 = 6840875) B6840875
theorem B14612167 : Blo 1801602 14612167 := bstep (se 1 (by rfl) ⟨10959125, by rfl⟩ : syracuseStep 14612167 = 21918251) B21918251
theorem B2741959 : Blo 1801602 2741959 := bstep (se 1 (by rfl) ⟨2056469, by rfl⟩ : syracuseStep 2741959 = 4112939) B4112939
theorem B10262315 : Blo 1801602 10262315 := bstep (se 1 (by rfl) ⟨7696736, by rfl⟩ : syracuseStep 10262315 = 15393473) B15393473
theorem B6166315 : Blo 1801602 6166315 := bstep (se 1 (by rfl) ⟨4624736, by rfl⟩ : syracuseStep 6166315 = 9249473) B9249473
theorem B6084395 : Blo 1801602 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B3848249 : Blo 1801602 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B6084665 : Blo 1801602 6084665 := bstep (se 2 (by rfl) ⟨2281749, by rfl⟩ : syracuseStep 6084665 = 4563499) B4563499
theorem B11548979 : Blo 1801602 11548979 := bstep (se 1 (by rfl) ⟨8661734, by rfl⟩ : syracuseStep 11548979 = 17323469) B17323469
theorem B20822359 : Blo 1801602 20822359 := bstep (se 1 (by rfl) ⟨15616769, by rfl⟩ : syracuseStep 20822359 = 31233539) B31233539
theorem B10271063 : Blo 1801602 10271063 := bstep (se 1 (by rfl) ⟨7703297, by rfl⟩ : syracuseStep 10271063 = 15406595) B15406595
theorem B6084989 : Blo 1801602 6084989 := bstep (se 3 (by rfl) ⟨1140935, by rfl⟩ : syracuseStep 6084989 = 2281871) B2281871
theorem B4561505 : Blo 1801602 4561505 := bstep (se 2 (by rfl) ⟨1710564, by rfl⟩ : syracuseStep 4561505 = 3421129) B3421129
theorem B9124487 : Blo 1801602 9124487 := bstep (se 1 (by rfl) ⟨6843365, by rfl⟩ : syracuseStep 9124487 = 13686731) B13686731
theorem B6085259 : Blo 1801602 6085259 := bstep (se 1 (by rfl) ⟨4563944, by rfl⟩ : syracuseStep 6085259 = 9127889) B9127889
theorem B7305875 : Blo 1801602 7305875 := bstep (se 1 (by rfl) ⟨5479406, by rfl⟩ : syracuseStep 7305875 = 10958813) B10958813
theorem B3422891 : Blo 1801602 3422891 := bstep (se 1 (by rfl) ⟨2567168, by rfl⟩ : syracuseStep 3422891 = 5134337) B5134337
theorem B3848915 : Blo 1801602 3848915 := bstep (se 1 (by rfl) ⟨2886686, by rfl⟩ : syracuseStep 3848915 = 5773373) B5773373
theorem B4053833 : Blo 1801602 4053833 := bstep (se 2 (by rfl) ⟨1520187, by rfl⟩ : syracuseStep 4053833 = 3040375) B3040375
theorem B13695965 : Blo 1801602 13695965 := bstep (se 3 (by rfl) ⟨2567993, by rfl⟩ : syracuseStep 13695965 = 5135987) B5135987
theorem B3849223 : Blo 1801602 3849223 := bstep (se 1 (by rfl) ⟨2886917, by rfl⟩ : syracuseStep 3849223 = 5773835) B5773835
theorem B2702459 : Blo 1801602 2702459 := bstep (se 1 (by rfl) ⟨2026844, by rfl⟩ : syracuseStep 2702459 = 4053689) B4053689
theorem B2702585 : Blo 1801602 2702585 := bstep (se 2 (by rfl) ⟨1013469, by rfl⟩ : syracuseStep 2702585 = 2026939) B2026939
theorem B2702687 : Blo 1801602 2702687 := bstep (se 1 (by rfl) ⟨2027015, by rfl⟩ : syracuseStep 2702687 = 4054031) B4054031
theorem B2702699 : Blo 1801602 2702699 := bstep (se 1 (by rfl) ⟨2027024, by rfl⟩ : syracuseStep 2702699 = 4054049) B4054049
theorem B13688189 : Blo 1801602 13688189 := bstep (se 3 (by rfl) ⟨2566535, by rfl⟩ : syracuseStep 13688189 = 5133071) B5133071
theorem B7912829 : Blo 1801602 7912829 := bstep (se 3 (by rfl) ⟨1483655, by rfl⟩ : syracuseStep 7912829 = 2967311) B2967311
theorem B4332943 : Blo 1801602 4332943 := bstep (se 1 (by rfl) ⟨3249707, by rfl⟩ : syracuseStep 4332943 = 6499415) B6499415
theorem B1801647 : Blo 1801602 1801647 := bstep (se 1 (by rfl) ⟨1351235, by rfl⟩ : syracuseStep 1801647 = 2702471) B2702471
theorem B1801671 : Blo 1801602 1801671 := bstep (se 1 (by rfl) ⟨1351253, by rfl⟩ : syracuseStep 1801671 = 2702507) B2702507
theorem B1801691 : Blo 1801602 1801691 := bstep (se 1 (by rfl) ⟨1351268, by rfl⟩ : syracuseStep 1801691 = 2702537) B2702537
theorem B6086177 : Blo 1801602 6086177 := bstep (se 2 (by rfl) ⟨2282316, by rfl⟩ : syracuseStep 6086177 = 4564633) B4564633
theorem B1801767 : Blo 1801602 1801767 := bstep (se 1 (by rfl) ⟨1351325, by rfl⟩ : syracuseStep 1801767 = 2702651) B2702651
theorem B23092775 : Blo 1801602 23092775 := bstep (se 1 (by rfl) ⟨17319581, by rfl⟩ : syracuseStep 23092775 = 34639163) B34639163
theorem B1801807 : Blo 1801602 1801807 := bstep (se 1 (by rfl) ⟨1351355, by rfl⟩ : syracuseStep 1801807 = 2702711) B2702711
theorem B2702927 : Blo 1801602 2702927 := bstep (se 1 (by rfl) ⟨2027195, by rfl⟩ : syracuseStep 2702927 = 4054391) B4054391
theorem B1801823 : Blo 1801602 1801823 := bstep (se 1 (by rfl) ⟨1351367, by rfl⟩ : syracuseStep 1801823 = 2702735) B2702735
theorem B4054625 : Blo 1801602 4054625 := bstep (se 2 (by rfl) ⟨1520484, by rfl⟩ : syracuseStep 4054625 = 3040969) B3040969
theorem B1801851 : Blo 1801602 1801851 := bstep (se 1 (by rfl) ⟨1351388, by rfl⟩ : syracuseStep 1801851 = 2702777) B2702777
theorem B5136011 : Blo 1801602 5136011 := bstep (se 1 (by rfl) ⟨3852008, by rfl⟩ : syracuseStep 5136011 = 7704017) B7704017
theorem B1801903 : Blo 1801602 1801903 := bstep (se 1 (by rfl) ⟨1351427, by rfl⟩ : syracuseStep 1801903 = 2702855) B2702855
theorem B1801927 : Blo 1801602 1801927 := bstep (se 1 (by rfl) ⟨1351445, by rfl⟩ : syracuseStep 1801927 = 2702891) B2702891
theorem B2703047 : Blo 1801602 2703047 := bstep (se 1 (by rfl) ⟨2027285, by rfl⟩ : syracuseStep 2703047 = 4054571) B4054571
theorem B1801947 : Blo 1801602 1801947 := bstep (se 1 (by rfl) ⟨1351460, by rfl⟩ : syracuseStep 1801947 = 2702921) B2702921
theorem B6086393 : Blo 1801602 6086393 := bstep (se 2 (by rfl) ⟨2282397, by rfl⟩ : syracuseStep 6086393 = 4564795) B4564795
theorem B1802023 : Blo 1801602 1802023 := bstep (se 1 (by rfl) ⟨1351517, by rfl⟩ : syracuseStep 1802023 = 2703035) B2703035
theorem B7700291 : Blo 1801602 7700291 := bstep (se 1 (by rfl) ⟨5775218, by rfl⟩ : syracuseStep 7700291 = 11550437) B11550437
theorem B1802063 : Blo 1801602 1802063 := bstep (se 1 (by rfl) ⟨1351547, by rfl⟩ : syracuseStep 1802063 = 2703095) B2703095
theorem B1802079 : Blo 1801602 1802079 := bstep (se 1 (by rfl) ⟨1351559, by rfl⟩ : syracuseStep 1802079 = 2703119) B2703119
theorem B2703209 : Blo 1801602 2703209 := bstep (se 2 (by rfl) ⟨1013703, by rfl⟩ : syracuseStep 2703209 = 2027407) B2027407
theorem B1802107 : Blo 1801602 1802107 := bstep (se 1 (by rfl) ⟨1351580, by rfl⟩ : syracuseStep 1802107 = 2703161) B2703161
theorem B10264481 : Blo 1801602 10264481 := bstep (se 2 (by rfl) ⟨3849180, by rfl⟩ : syracuseStep 10264481 = 7698361) B7698361
theorem B1802159 : Blo 1801602 1802159 := bstep (se 1 (by rfl) ⟨1351619, by rfl⟩ : syracuseStep 1802159 = 2703239) B2703239
theorem B2703287 : Blo 1801602 2703287 := bstep (se 1 (by rfl) ⟨2027465, by rfl⟩ : syracuseStep 2703287 = 4054931) B4054931
theorem B4054967 : Blo 1801602 4054967 := bstep (se 1 (by rfl) ⟨3041225, by rfl⟩ : syracuseStep 4054967 = 6082451) B6082451
theorem B1802183 : Blo 1801602 1802183 := bstep (se 1 (by rfl) ⟨1351637, by rfl⟩ : syracuseStep 1802183 = 2703275) B2703275
theorem B1802203 : Blo 1801602 1802203 := bstep (se 1 (by rfl) ⟨1351652, by rfl⟩ : syracuseStep 1802203 = 2703305) B2703305
theorem B2703323 : Blo 1801602 2703323 := bstep (se 1 (by rfl) ⟨2027492, by rfl⟩ : syracuseStep 2703323 = 4054985) B4054985
theorem B7700633 : Blo 1801602 7700633 := bstep (se 2 (by rfl) ⟨2887737, by rfl⟩ : syracuseStep 7700633 = 5775475) B5775475
theorem B4563155 : Blo 1801602 4563155 := bstep (se 1 (by rfl) ⟨3422366, by rfl⟩ : syracuseStep 4563155 = 6844733) B6844733
theorem B1802527 : Blo 1801602 1802527 := bstep (se 1 (by rfl) ⟨1351895, by rfl⟩ : syracuseStep 1802527 = 2703791) B2703791
theorem B30810455 : Blo 1801602 30810455 := bstep (se 1 (by rfl) ⟨23107841, by rfl⟩ : syracuseStep 30810455 = 46215683) B46215683
theorem B2703707 : Blo 1801602 2703707 := bstep (se 1 (by rfl) ⟨2027780, by rfl⟩ : syracuseStep 2703707 = 4055561) B4055561
theorem B1802587 : Blo 1801602 1802587 := bstep (se 1 (by rfl) ⟨1351940, by rfl⟩ : syracuseStep 1802587 = 2703881) B2703881
theorem B3653999 : Blo 1801602 3653999 := bstep (se 1 (by rfl) ⟨2740499, by rfl⟩ : syracuseStep 3653999 = 5480999) B5480999
theorem B1802607 : Blo 1801602 1802607 := bstep (se 1 (by rfl) ⟨1351955, by rfl⟩ : syracuseStep 1802607 = 2703911) B2703911
theorem B19480985 : Blo 1801602 19480985 := bstep (se 2 (by rfl) ⟨7305369, by rfl⟩ : syracuseStep 19480985 = 14610739) B14610739
theorem B1802663 : Blo 1801602 1802663 := bstep (se 1 (by rfl) ⟨1351997, by rfl⟩ : syracuseStep 1802663 = 2703995) B2703995
theorem B4055471 : Blo 1801602 4055471 := bstep (se 1 (by rfl) ⟨3041603, by rfl⟩ : syracuseStep 4055471 = 6083207) B6083207
theorem B27763145 : Blo 1801602 27763145 := bstep (se 2 (by rfl) ⟨10411179, by rfl⟩ : syracuseStep 27763145 = 20822359) B20822359
theorem B4055507 : Blo 1801602 4055507 := bstep (se 1 (by rfl) ⟨3041630, by rfl⟩ : syracuseStep 4055507 = 6083261) B6083261
theorem B1802747 : Blo 1801602 1802747 := bstep (se 1 (by rfl) ⟨1352060, by rfl⟩ : syracuseStep 1802747 = 2704121) B2704121
theorem B4055615 : Blo 1801602 4055615 := bstep (se 1 (by rfl) ⟨3041711, by rfl⟩ : syracuseStep 4055615 = 6083423) B6083423
theorem B2703935 : Blo 1801602 2703935 := bstep (se 1 (by rfl) ⟨2027951, by rfl⟩ : syracuseStep 2703935 = 4055903) B4055903
theorem B1802815 : Blo 1801602 1802815 := bstep (se 1 (by rfl) ⟨1352111, by rfl⟩ : syracuseStep 1802815 = 2704223) B2704223
theorem B1802823 : Blo 1801602 1802823 := bstep (se 1 (by rfl) ⟨1352117, by rfl⟩ : syracuseStep 1802823 = 2704235) B2704235
theorem B4055723 : Blo 1801602 4055723 := bstep (se 1 (by rfl) ⟨3041792, by rfl⟩ : syracuseStep 4055723 = 6083585) B6083585
theorem B2704055 : Blo 1801602 2704055 := bstep (se 1 (by rfl) ⟨2028041, by rfl⟩ : syracuseStep 2704055 = 4056083) B4056083
theorem B13173463 : Blo 1801602 13173463 := bstep (se 1 (by rfl) ⟨9880097, by rfl⟩ : syracuseStep 13173463 = 19760195) B19760195
theorem B1802975 : Blo 1801602 1802975 := bstep (se 1 (by rfl) ⟨1352231, by rfl⟩ : syracuseStep 1802975 = 2704463) B2704463
theorem B8782559 : Blo 1801602 8782559 := bstep (se 1 (by rfl) ⟨6586919, by rfl⟩ : syracuseStep 8782559 = 13173839) B13173839
theorem B1803055 : Blo 1801602 1803055 := bstep (se 1 (by rfl) ⟨1352291, by rfl⟩ : syracuseStep 1803055 = 2704583) B2704583
theorem B2704283 : Blo 1801602 2704283 := bstep (se 1 (by rfl) ⟨2028212, by rfl⟩ : syracuseStep 2704283 = 4056425) B4056425
theorem B1803163 : Blo 1801602 1803163 := bstep (se 1 (by rfl) ⟨1352372, by rfl⟩ : syracuseStep 1803163 = 2704745) B2704745
theorem B19751863 : Blo 1801602 19751863 := bstep (se 1 (by rfl) ⟨14813897, by rfl⟩ : syracuseStep 19751863 = 29627795) B29627795
theorem B1803215 : Blo 1801602 1803215 := bstep (se 1 (by rfl) ⟨1352411, by rfl⟩ : syracuseStep 1803215 = 2704823) B2704823
theorem B15401947 : Blo 1801602 15401947 := bstep (se 1 (by rfl) ⟨11551460, by rfl⟩ : syracuseStep 15401947 = 23102921) B23102921
theorem B3851239 : Blo 1801602 3851239 := bstep (se 1 (by rfl) ⟨2888429, by rfl⟩ : syracuseStep 3851239 = 5776859) B5776859
theorem B1803239 : Blo 1801602 1803239 := bstep (se 1 (by rfl) ⟨1352429, by rfl⟩ : syracuseStep 1803239 = 2704859) B2704859
theorem B3040247 : Blo 1801602 3040247 := bstep (se 1 (by rfl) ⟨2280185, by rfl⟩ : syracuseStep 3040247 = 4560371) B4560371
theorem B6841543 : Blo 1801602 6841543 := bstep (se 1 (by rfl) ⟨5131157, by rfl⟩ : syracuseStep 6841543 = 10262315) B10262315
theorem B4056263 : Blo 1801602 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B1803551 : Blo 1801602 1803551 := bstep (se 1 (by rfl) ⟨1352663, by rfl⟩ : syracuseStep 1803551 = 2705327) B2705327
theorem B2704679 : Blo 1801602 2704679 := bstep (se 1 (by rfl) ⟨2028509, by rfl⟩ : syracuseStep 2704679 = 4057019) B4057019
theorem B124872029 : Blo 1801602 124872029 := bstep (se 3 (by rfl) ⟨23413505, by rfl⟩ : syracuseStep 124872029 = 46827011) B46827011
theorem B15394157 : Blo 1801602 15394157 := bstep (se 3 (by rfl) ⟨2886404, by rfl⟩ : syracuseStep 15394157 = 5772809) B5772809
theorem B4056443 : Blo 1801602 4056443 := bstep (se 1 (by rfl) ⟨3042332, by rfl⟩ : syracuseStep 4056443 = 6084665) B6084665
theorem B2704763 : Blo 1801602 2704763 := bstep (se 1 (by rfl) ⟨2028572, by rfl⟩ : syracuseStep 2704763 = 4057145) B4057145
theorem B16451059 : Blo 1801602 16451059 := bstep (se 1 (by rfl) ⟨12338294, by rfl⟩ : syracuseStep 16451059 = 24676589) B24676589
theorem B4056569 : Blo 1801602 4056569 := bstep (se 2 (by rfl) ⟨1521213, by rfl⟩ : syracuseStep 4056569 = 3042427) B3042427
theorem B2704889 : Blo 1801602 2704889 := bstep (se 2 (by rfl) ⟨1014333, by rfl⟩ : syracuseStep 2704889 = 2028667) B2028667
theorem B4056659 : Blo 1801602 4056659 := bstep (se 1 (by rfl) ⟨3042494, by rfl⟩ : syracuseStep 4056659 = 6084989) B6084989
theorem B2704991 : Blo 1801602 2704991 := bstep (se 1 (by rfl) ⟨2028743, by rfl⟩ : syracuseStep 2704991 = 4057487) B4057487
theorem B8226461 : Blo 1801602 8226461 := bstep (se 3 (by rfl) ⟨1542461, by rfl⟩ : syracuseStep 8226461 = 3084923) B3084923
theorem B9881275 : Blo 1801602 9881275 := bstep (se 1 (by rfl) ⟨7410956, by rfl⟩ : syracuseStep 9881275 = 14821913) B14821913
theorem B3041003 : Blo 1801602 3041003 := bstep (se 1 (by rfl) ⟨2280752, by rfl⟩ : syracuseStep 3041003 = 4561505) B4561505
theorem B4056839 : Blo 1801602 4056839 := bstep (se 1 (by rfl) ⟨3042629, by rfl⟩ : syracuseStep 4056839 = 6085259) B6085259
theorem B2705207 : Blo 1801602 2705207 := bstep (se 1 (by rfl) ⟨2028905, by rfl⟩ : syracuseStep 2705207 = 4057811) B4057811
theorem B5777257 : Blo 1801602 5777257 := bstep (se 2 (by rfl) ⟨2166471, by rfl⟩ : syracuseStep 5777257 = 4332943) B4332943
theorem B13191119 : Blo 1801602 13191119 := bstep (se 1 (by rfl) ⟨9893339, by rfl⟩ : syracuseStep 13191119 = 19786679) B19786679
theorem B17557681 : Blo 1801602 17557681 := bstep (se 2 (by rfl) ⟨6584130, by rfl⟩ : syracuseStep 17557681 = 13168261) B13168261
theorem B6080777 : Blo 1801602 6080777 := bstep (se 2 (by rfl) ⟨2280291, by rfl⟩ : syracuseStep 6080777 = 4560583) B4560583
theorem B19482889 : Blo 1801602 19482889 := bstep (se 2 (by rfl) ⟨7306083, by rfl⟩ : syracuseStep 19482889 = 14612167) B14612167
theorem B3655945 : Blo 1801602 3655945 := bstep (se 2 (by rfl) ⟨1370979, by rfl⟩ : syracuseStep 3655945 = 2741959) B2741959
theorem B17328421 : Blo 1801602 17328421 := bstep (se 4 (by rfl) ⟨1624539, by rfl⟩ : syracuseStep 17328421 = 3249079) B3249079
theorem B4057451 : Blo 1801602 4057451 := bstep (se 1 (by rfl) ⟨3043088, by rfl⟩ : syracuseStep 4057451 = 6086177) B6086177
theorem B15395183 : Blo 1801602 15395183 := bstep (se 1 (by rfl) ⟨11546387, by rfl⟩ : syracuseStep 15395183 = 23092775) B23092775
theorem B3901879 : Blo 1801602 3901879 := bstep (se 1 (by rfl) ⟨2926409, by rfl⟩ : syracuseStep 3901879 = 5852819) B5852819
theorem B9128375 : Blo 1801602 9128375 := bstep (se 1 (by rfl) ⟨6846281, by rfl⟩ : syracuseStep 9128375 = 13692563) B13692563
theorem B4057595 : Blo 1801602 4057595 := bstep (se 1 (by rfl) ⟨3043196, by rfl⟩ : syracuseStep 4057595 = 6086393) B6086393
theorem B6842987 : Blo 1801602 6842987 := bstep (se 1 (by rfl) ⟨5132240, by rfl⟩ : syracuseStep 6842987 = 10264481) B10264481
theorem B4057721 : Blo 1801602 4057721 := bstep (se 2 (by rfl) ⟨1521645, by rfl⟩ : syracuseStep 4057721 = 3043291) B3043291
theorem B4057775 : Blo 1801602 4057775 := bstep (se 1 (by rfl) ⟨3043331, by rfl⟩ : syracuseStep 4057775 = 6086663) B6086663
theorem B3041975 : Blo 1801602 3041975 := bstep (se 1 (by rfl) ⟨2281481, by rfl⟩ : syracuseStep 3041975 = 4562963) B4562963
theorem B4057847 : Blo 1801602 4057847 := bstep (se 1 (by rfl) ⟨3043385, by rfl⟩ : syracuseStep 4057847 = 6086771) B6086771
theorem B4058027 : Blo 1801602 4058027 := bstep (se 1 (by rfl) ⟨3043520, by rfl⟩ : syracuseStep 4058027 = 6087041) B6087041
theorem B12995599 : Blo 1801602 12995599 := bstep (se 1 (by rfl) ⟨9746699, by rfl⟩ : syracuseStep 12995599 = 19493399) B19493399
theorem B27741455 : Blo 1801602 27741455 := bstep (se 1 (by rfl) ⟨20806091, by rfl⟩ : syracuseStep 27741455 = 41612183) B41612183
theorem B17329423 : Blo 1801602 17329423 := bstep (se 1 (by rfl) ⟨12997067, by rfl⟩ : syracuseStep 17329423 = 25994135) B25994135
theorem B2886943 : Blo 1801602 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B9121085 : Blo 1801602 9121085 := bstep (se 3 (by rfl) ⟨1710203, by rfl⟩ : syracuseStep 9121085 = 3420407) B3420407
theorem B9882941 : Blo 1801602 9882941 := bstep (se 3 (by rfl) ⟨1853051, by rfl⟩ : syracuseStep 9882941 = 3706103) B3706103
theorem B34631009 : Blo 1801602 34631009 := bstep (se 2 (by rfl) ⟨12986628, by rfl⟩ : syracuseStep 34631009 = 25973257) B25973257
theorem B6081911 : Blo 1801602 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B3042697 : Blo 1801602 3042697 := bstep (se 2 (by rfl) ⟨1141011, by rfl⟩ : syracuseStep 3042697 = 2282023) B2282023
theorem B7310807 : Blo 1801602 7310807 := bstep (se 1 (by rfl) ⟨5483105, by rfl⟩ : syracuseStep 7310807 = 10966211) B10966211
theorem B2280955 : Blo 1801602 2280955 := bstep (se 1 (by rfl) ⟨1710716, by rfl⟩ : syracuseStep 2280955 = 3421433) B3421433
theorem B3043129 : Blo 1801602 3043129 := bstep (se 2 (by rfl) ⟨1141173, by rfl⟩ : syracuseStep 3043129 = 2282347) B2282347
theorem B5132297 : Blo 1801602 5132297 := bstep (se 2 (by rfl) ⟨1924611, by rfl⟩ : syracuseStep 5132297 = 3849223) B3849223
theorem B12988475 : Blo 1801602 12988475 := bstep (se 1 (by rfl) ⟨9741356, by rfl⟩ : syracuseStep 12988475 = 19482713) B19482713
theorem B3043433 : Blo 1801602 3043433 := bstep (se 2 (by rfl) ⟨1141287, by rfl⟩ : syracuseStep 3043433 = 2282575) B2282575
theorem B6844763 : Blo 1801602 6844763 := bstep (se 1 (by rfl) ⟨5133572, by rfl⟩ : syracuseStep 6844763 = 10267145) B10267145
theorem B6082991 : Blo 1801602 6082991 := bstep (se 1 (by rfl) ⟨4562243, by rfl⟩ : syracuseStep 6082991 = 9124487) B9124487
theorem B4870583 : Blo 1801602 4870583 := bstep (se 1 (by rfl) ⟨3652937, by rfl⟩ : syracuseStep 4870583 = 7305875) B7305875
theorem B2281927 : Blo 1801602 2281927 := bstep (se 1 (by rfl) ⟨1711445, by rfl⟩ : syracuseStep 2281927 = 3422891) B3422891
theorem B4329953 : Blo 1801602 4329953 := bstep (se 2 (by rfl) ⟨1623732, by rfl⟩ : syracuseStep 4329953 = 3247465) B3247465
theorem B2028127 : Blo 1801602 2028127 := bstep (se 1 (by rfl) ⟨1521095, by rfl⟩ : syracuseStep 2028127 = 3042191) B3042191
theorem B9130643 : Blo 1801602 9130643 := bstep (se 1 (by rfl) ⟨6847982, by rfl⟩ : syracuseStep 9130643 = 13695965) B13695965
theorem B66663085 : Blo 1801602 66663085 := bstep (se 3 (by rfl) ⟨12499328, by rfl⟩ : syracuseStep 66663085 = 24998657) B24998657
theorem B3420947 : Blo 1801602 3420947 := bstep (se 1 (by rfl) ⟨2565710, by rfl⟩ : syracuseStep 3420947 = 5131421) B5131421
theorem B10269605 : Blo 1801602 10269605 := bstep (se 4 (by rfl) ⟨962775, by rfl⟩ : syracuseStep 10269605 = 1925551) B1925551
theorem B6845431 : Blo 1801602 6845431 := bstep (se 1 (by rfl) ⟨5134073, by rfl⟩ : syracuseStep 6845431 = 10268147) B10268147
theorem B17331191 : Blo 1801602 17331191 := bstep (se 1 (by rfl) ⟨12998393, by rfl⟩ : syracuseStep 17331191 = 25996787) B25996787
theorem B8221753 : Blo 1801602 8221753 := bstep (se 2 (by rfl) ⟨3083157, by rfl⟩ : syracuseStep 8221753 = 6166315) B6166315
theorem B5133527 : Blo 1801602 5133527 := bstep (se 1 (by rfl) ⟨3850145, by rfl⟩ : syracuseStep 5133527 = 7700291) B7700291
theorem B6845735 : Blo 1801602 6845735 := bstep (se 1 (by rfl) ⟨5134301, by rfl⟩ : syracuseStep 6845735 = 10268603) B10268603
theorem B6083963 : Blo 1801602 6083963 := bstep (se 1 (by rfl) ⟨4562972, by rfl⟩ : syracuseStep 6083963 = 9125945) B9125945
theorem B3421577 : Blo 1801602 3421577 := bstep (se 2 (by rfl) ⟨1283091, by rfl⟩ : syracuseStep 3421577 = 2566183) B2566183
theorem B9745853 : Blo 1801602 9745853 := bstep (se 3 (by rfl) ⟨1827347, by rfl⟩ : syracuseStep 9745853 = 3654695) B3654695
theorem B10261997 : Blo 1801602 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B5133881 : Blo 1801602 5133881 := bstep (se 2 (by rfl) ⟨1925205, by rfl⟩ : syracuseStep 5133881 = 3850411) B3850411
theorem B9123515 : Blo 1801602 9123515 := bstep (se 1 (by rfl) ⟨6842636, by rfl⟩ : syracuseStep 9123515 = 13685273) B13685273
theorem B3168047 : Blo 1801602 3168047 := bstep (se 1 (by rfl) ⟨2376035, by rfl⟩ : syracuseStep 3168047 = 4752071) B4752071
theorem B4560695 : Blo 1801602 4560695 := bstep (se 1 (by rfl) ⟨3420521, by rfl⟩ : syracuseStep 4560695 = 6841043) B6841043
theorem B4560745 : Blo 1801602 4560745 := bstep (se 2 (by rfl) ⟨1710279, by rfl⟩ : syracuseStep 4560745 = 3420559) B3420559
theorem B197269451 : Blo 1801602 197269451 := bstep (se 1 (by rfl) ⟨147952088, by rfl⟩ : syracuseStep 197269451 = 295904177) B295904177
theorem B7698685 : Blo 1801602 7698685 := bstep (se 3 (by rfl) ⟨1443503, by rfl⟩ : syracuseStep 7698685 = 2887007) B2887007
theorem B17316119 : Blo 1801602 17316119 := bstep (se 1 (by rfl) ⟨12987089, by rfl⟩ : syracuseStep 17316119 = 25974179) B25974179
theorem B6936857 : Blo 1801602 6936857 := bstep (se 2 (by rfl) ⟨2601321, by rfl⟩ : syracuseStep 6936857 = 5202643) B5202643
theorem B51952049 : Blo 1801602 51952049 := bstep (se 2 (by rfl) ⟨19482018, by rfl⟩ : syracuseStep 51952049 = 38964037) B38964037
theorem B39000635 : Blo 1801602 39000635 := bstep (se 1 (by rfl) ⟨29250476, by rfl⟩ : syracuseStep 39000635 = 58500953) B58500953
theorem B15399557 : Blo 1801602 15399557 := bstep (se 4 (by rfl) ⟨1443708, by rfl⟩ : syracuseStep 15399557 = 2887417) B2887417
theorem B6085367 : Blo 1801602 6085367 := bstep (se 1 (by rfl) ⟨4564025, by rfl⟩ : syracuseStep 6085367 = 9128051) B9128051
theorem B4053779 : Blo 1801602 4053779 := bstep (se 1 (by rfl) ⟨3040334, by rfl⟩ : syracuseStep 4053779 = 6080669) B6080669
theorem B7699319 : Blo 1801602 7699319 := bstep (se 1 (by rfl) ⟨5774489, by rfl⟩ : syracuseStep 7699319 = 11548979) B11548979
theorem B6847375 : Blo 1801602 6847375 := bstep (se 1 (by rfl) ⟨5135531, by rfl⟩ : syracuseStep 6847375 = 10271063) B10271063
theorem B23100461 : Blo 1801602 23100461 := bstep (se 3 (by rfl) ⟨4331336, by rfl⟩ : syracuseStep 23100461 = 8662673) B8662673
theorem B4054139 : Blo 1801602 4054139 := bstep (se 1 (by rfl) ⟨3040604, by rfl⟩ : syracuseStep 4054139 = 6081209) B6081209
theorem B4332683 : Blo 1801602 4332683 := bstep (se 1 (by rfl) ⟨3249512, by rfl⟩ : syracuseStep 4332683 = 6499025) B6499025
theorem B2702555 : Blo 1801602 2702555 := bstep (se 1 (by rfl) ⟨2026916, by rfl⟩ : syracuseStep 2702555 = 4053833) B4053833
theorem B10263773 : Blo 1801602 10263773 := bstep (se 3 (by rfl) ⟨1924457, by rfl⟩ : syracuseStep 10263773 = 3848915) B3848915
theorem B4562153 : Blo 1801602 4562153 := bstep (se 2 (by rfl) ⟨1710807, by rfl⟩ : syracuseStep 4562153 = 3421615) B3421615
theorem B4054265 : Blo 1801602 4054265 := bstep (se 2 (by rfl) ⟨1520349, by rfl⟩ : syracuseStep 4054265 = 3040699) B3040699
theorem B2702729 : Blo 1801602 2702729 := bstep (se 2 (by rfl) ⟨1013523, by rfl⟩ : syracuseStep 2702729 = 2027047) B2027047
theorem B4054409 : Blo 1801602 4054409 := bstep (se 2 (by rfl) ⟨1520403, by rfl⟩ : syracuseStep 4054409 = 3040807) B3040807
theorem B4562315 : Blo 1801602 4562315 := bstep (se 1 (by rfl) ⟨3421736, by rfl⟩ : syracuseStep 4562315 = 6843473) B6843473
theorem B1801639 : Blo 1801602 1801639 := bstep (se 1 (by rfl) ⟨1351229, by rfl⟩ : syracuseStep 1801639 = 2702459) B2702459
theorem B1801723 : Blo 1801602 1801723 := bstep (se 1 (by rfl) ⟨1351292, by rfl⟩ : syracuseStep 1801723 = 2702585) B2702585
theorem B4054535 : Blo 1801602 4054535 := bstep (se 1 (by rfl) ⟨3040901, by rfl⟩ : syracuseStep 4054535 = 6081803) B6081803
theorem B1801791 : Blo 1801602 1801791 := bstep (se 1 (by rfl) ⟨1351343, by rfl⟩ : syracuseStep 1801791 = 2702687) B2702687
theorem B1801799 : Blo 1801602 1801799 := bstep (se 1 (by rfl) ⟨1351349, by rfl⟩ : syracuseStep 1801799 = 2702699) B2702699
theorem B9125459 : Blo 1801602 9125459 := bstep (se 1 (by rfl) ⟨6844094, by rfl⟩ : syracuseStep 9125459 = 13688189) B13688189
theorem B5275219 : Blo 1801602 5275219 := bstep (se 1 (by rfl) ⟨3956414, by rfl⟩ : syracuseStep 5275219 = 7912829) B7912829
theorem B4562527 : Blo 1801602 4562527 := bstep (se 1 (by rfl) ⟨3421895, by rfl⟩ : syracuseStep 4562527 = 6843791) B6843791
theorem B4054715 : Blo 1801602 4054715 := bstep (se 1 (by rfl) ⟨3041036, by rfl⟩ : syracuseStep 4054715 = 6082073) B6082073
theorem B1801951 : Blo 1801602 1801951 := bstep (se 1 (by rfl) ⟨1351463, by rfl⟩ : syracuseStep 1801951 = 2702927) B2702927
theorem B2703083 : Blo 1801602 2703083 := bstep (se 1 (by rfl) ⟨2027312, by rfl⟩ : syracuseStep 2703083 = 4054625) B4054625
theorem B3424007 : Blo 1801602 3424007 := bstep (se 1 (by rfl) ⟨2568005, by rfl⟩ : syracuseStep 3424007 = 5136011) B5136011
theorem B1802031 : Blo 1801602 1802031 := bstep (se 1 (by rfl) ⟨1351523, by rfl⟩ : syracuseStep 1802031 = 2703047) B2703047
theorem B6086447 : Blo 1801602 6086447 := bstep (se 1 (by rfl) ⟨4564835, by rfl⟩ : syracuseStep 6086447 = 9129671) B9129671
theorem B4054841 : Blo 1801602 4054841 := bstep (se 2 (by rfl) ⟨1520565, by rfl⟩ : syracuseStep 4054841 = 3041131) B3041131
theorem B1802139 : Blo 1801602 1802139 := bstep (se 1 (by rfl) ⟨1351604, by rfl⟩ : syracuseStep 1802139 = 2703209) B2703209
theorem B37019555 : Blo 1801602 37019555 := bstep (se 1 (by rfl) ⟨27764666, by rfl⟩ : syracuseStep 37019555 = 55529333) B55529333
theorem B1802191 : Blo 1801602 1802191 := bstep (se 1 (by rfl) ⟨1351643, by rfl⟩ : syracuseStep 1802191 = 2703287) B2703287
theorem B2703311 : Blo 1801602 2703311 := bstep (se 1 (by rfl) ⟨2027483, by rfl⟩ : syracuseStep 2703311 = 4054967) B4054967
theorem B1802215 : Blo 1801602 1802215 := bstep (se 1 (by rfl) ⟨1351661, by rfl⟩ : syracuseStep 1802215 = 2703323) B2703323
theorem B8658983 : Blo 1801602 8658983 := bstep (se 1 (by rfl) ⟨6494237, by rfl⟩ : syracuseStep 8658983 = 12988475) B12988475
theorem B1802471 : Blo 1801602 1802471 := bstep (se 1 (by rfl) ⟨1351853, by rfl⟩ : syracuseStep 1802471 = 2703707) B2703707
theorem B4563175 : Blo 1801602 4563175 := bstep (se 1 (by rfl) ⟨3422381, by rfl⟩ : syracuseStep 4563175 = 6844763) B6844763
theorem B4055327 : Blo 1801602 4055327 := bstep (se 1 (by rfl) ⟨3041495, by rfl⟩ : syracuseStep 4055327 = 6082991) B6082991
theorem B2703647 : Blo 1801602 2703647 := bstep (se 1 (by rfl) ⟨2027735, by rfl⟩ : syracuseStep 2703647 = 4055471) B4055471
theorem B2703671 : Blo 1801602 2703671 := bstep (se 1 (by rfl) ⟨2027753, by rfl⟩ : syracuseStep 2703671 = 4055507) B4055507
theorem B10264913 : Blo 1801602 10264913 := bstep (se 2 (by rfl) ⟨3849342, by rfl⟩ : syracuseStep 10264913 = 7698685) B7698685
theorem B25977185 : Blo 1801602 25977185 := bstep (se 2 (by rfl) ⟨9741444, by rfl⟩ : syracuseStep 25977185 = 19482889) B19482889
theorem B4874593 : Blo 1801602 4874593 := bstep (se 2 (by rfl) ⟨1827972, by rfl⟩ : syracuseStep 4874593 = 3655945) B3655945
theorem B2703743 : Blo 1801602 2703743 := bstep (se 1 (by rfl) ⟨2027807, by rfl⟩ : syracuseStep 2703743 = 4055615) B4055615
theorem B1802623 : Blo 1801602 1802623 := bstep (se 1 (by rfl) ⟨1351967, by rfl⟩ : syracuseStep 1802623 = 2703935) B2703935
theorem B6087095 : Blo 1801602 6087095 := bstep (se 1 (by rfl) ⟨4565321, by rfl⟩ : syracuseStep 6087095 = 9130643) B9130643
theorem B2703815 : Blo 1801602 2703815 := bstep (se 1 (by rfl) ⟨2027861, by rfl⟩ : syracuseStep 2703815 = 4055723) B4055723
theorem B1802703 : Blo 1801602 1802703 := bstep (se 1 (by rfl) ⟨1352027, by rfl⟩ : syracuseStep 1802703 = 2704055) B2704055
theorem B5202505 : Blo 1801602 5202505 := bstep (se 2 (by rfl) ⟨1950939, by rfl⟩ : syracuseStep 5202505 = 3901879) B3901879
theorem B1802855 : Blo 1801602 1802855 := bstep (se 1 (by rfl) ⟨1352141, by rfl⟩ : syracuseStep 1802855 = 2704283) B2704283
theorem B2704169 : Blo 1801602 2704169 := bstep (se 2 (by rfl) ⟨1014063, by rfl⟩ : syracuseStep 2704169 = 2028127) B2028127
theorem B2704175 : Blo 1801602 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B4563823 : Blo 1801602 4563823 := bstep (se 1 (by rfl) ⟨3422867, by rfl⟩ : syracuseStep 4563823 = 6845735) B6845735
theorem B1803119 : Blo 1801602 1803119 := bstep (se 1 (by rfl) ⟨1352339, by rfl⟩ : syracuseStep 1803119 = 2704679) B2704679
theorem B88884113 : Blo 1801602 88884113 := bstep (se 2 (by rfl) ⟨33331542, by rfl⟩ : syracuseStep 88884113 = 66663085) B66663085
theorem B83248019 : Blo 1801602 83248019 := bstep (se 1 (by rfl) ⟨62436014, by rfl⟩ : syracuseStep 83248019 = 124872029) B124872029
theorem B4055975 : Blo 1801602 4055975 := bstep (se 1 (by rfl) ⟨3041981, by rfl⟩ : syracuseStep 4055975 = 6083963) B6083963
theorem B2704295 : Blo 1801602 2704295 := bstep (se 1 (by rfl) ⟨2028221, by rfl⟩ : syracuseStep 2704295 = 4056443) B4056443
theorem B1803175 : Blo 1801602 1803175 := bstep (se 1 (by rfl) ⟨1352381, by rfl⟩ : syracuseStep 1803175 = 2704763) B2704763
theorem B17564617 : Blo 1801602 17564617 := bstep (se 2 (by rfl) ⟨6586731, by rfl⟩ : syracuseStep 17564617 = 13173463) B13173463
theorem B6841331 : Blo 1801602 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B2704379 : Blo 1801602 2704379 := bstep (se 1 (by rfl) ⟨2028284, by rfl⟩ : syracuseStep 2704379 = 4056569) B4056569
theorem B1803259 : Blo 1801602 1803259 := bstep (se 1 (by rfl) ⟨1352444, by rfl⟩ : syracuseStep 1803259 = 2704889) B2704889
theorem B2704439 : Blo 1801602 2704439 := bstep (se 1 (by rfl) ⟨2028329, by rfl⟩ : syracuseStep 2704439 = 4056659) B4056659
theorem B1803327 : Blo 1801602 1803327 := bstep (se 1 (by rfl) ⟨1352495, by rfl⟩ : syracuseStep 1803327 = 2704991) B2704991
theorem B2704559 : Blo 1801602 2704559 := bstep (se 1 (by rfl) ⟨2028419, by rfl⟩ : syracuseStep 2704559 = 4056839) B4056839
theorem B3040463 : Blo 1801602 3040463 := bstep (se 1 (by rfl) ⟨2280347, by rfl⟩ : syracuseStep 3040463 = 4560695) B4560695
theorem B1803471 : Blo 1801602 1803471 := bstep (se 1 (by rfl) ⟨1352603, by rfl⟩ : syracuseStep 1803471 = 2705207) B2705207
theorem B9127241 : Blo 1801602 9127241 := bstep (se 2 (by rfl) ⟨3422715, by rfl⟩ : syracuseStep 9127241 = 6845431) B6845431
theorem B17327465 : Blo 1801602 17327465 := bstep (se 2 (by rfl) ⟨6497799, by rfl⟩ : syracuseStep 17327465 = 12995599) B12995599
theorem B2704967 : Blo 1801602 2704967 := bstep (se 1 (by rfl) ⟨2028725, by rfl⟩ : syracuseStep 2704967 = 4057451) B4057451
theorem B2705063 : Blo 1801602 2705063 := bstep (se 1 (by rfl) ⟨2028797, by rfl⟩ : syracuseStep 2705063 = 4057595) B4057595
theorem B2705147 : Blo 1801602 2705147 := bstep (se 1 (by rfl) ⟨2028860, by rfl⟩ : syracuseStep 2705147 = 4057721) B4057721
theorem B10266371 : Blo 1801602 10266371 := bstep (se 1 (by rfl) ⟨7699778, by rfl⟩ : syracuseStep 10266371 = 15399557) B15399557
theorem B2705183 : Blo 1801602 2705183 := bstep (se 1 (by rfl) ⟨2028887, by rfl⟩ : syracuseStep 2705183 = 4057775) B4057775
theorem B4056911 : Blo 1801602 4056911 := bstep (se 1 (by rfl) ⟨3042683, by rfl⟩ : syracuseStep 4056911 = 6085367) B6085367
theorem B2705231 : Blo 1801602 2705231 := bstep (se 1 (by rfl) ⟨2028923, by rfl⟩ : syracuseStep 2705231 = 4057847) B4057847
theorem B4056929 : Blo 1801602 4056929 := bstep (se 2 (by rfl) ⟨1521348, by rfl⟩ : syracuseStep 4056929 = 3042697) B3042697
theorem B2705351 : Blo 1801602 2705351 := bstep (se 1 (by rfl) ⟨2029013, by rfl⟩ : syracuseStep 2705351 = 4058027) B4058027
theorem B3041273 : Blo 1801602 3041273 := bstep (se 2 (by rfl) ⟨1140477, by rfl⟩ : syracuseStep 3041273 = 2280955) B2280955
theorem B6842515 : Blo 1801602 6842515 := bstep (se 1 (by rfl) ⟨5131886, by rfl⟩ : syracuseStep 6842515 = 10263773) B10263773
theorem B3041435 : Blo 1801602 3041435 := bstep (se 1 (by rfl) ⟨2281076, by rfl⟩ : syracuseStep 3041435 = 4562153) B4562153
theorem B6080723 : Blo 1801602 6080723 := bstep (se 1 (by rfl) ⟨4560542, by rfl⟩ : syracuseStep 6080723 = 9121085) B9121085
theorem B23087339 : Blo 1801602 23087339 := bstep (se 1 (by rfl) ⟨17315504, by rfl⟩ : syracuseStep 23087339 = 34631009) B34631009
theorem B13175033 : Blo 1801602 13175033 := bstep (se 2 (by rfl) ⟨4940637, by rfl⟩ : syracuseStep 13175033 = 9881275) B9881275
theorem B3041543 : Blo 1801602 3041543 := bstep (se 1 (by rfl) ⟨2281157, by rfl⟩ : syracuseStep 3041543 = 4562315) B4562315
theorem B4057505 : Blo 1801602 4057505 := bstep (se 2 (by rfl) ⟨1521564, by rfl⟩ : syracuseStep 4057505 = 3043129) B3043129
theorem B6080993 : Blo 1801602 6080993 := bstep (se 2 (by rfl) ⟨2280372, by rfl⟩ : syracuseStep 6080993 = 4560745) B4560745
theorem B7703009 : Blo 1801602 7703009 := bstep (se 2 (by rfl) ⟨2888628, by rfl⟩ : syracuseStep 7703009 = 5777257) B5777257
theorem B4057631 : Blo 1801602 4057631 := bstep (se 1 (by rfl) ⟨3043223, by rfl⟩ : syracuseStep 4057631 = 6086447) B6086447
theorem B3042103 : Blo 1801602 3042103 := bstep (se 1 (by rfl) ⟨2281577, by rfl⟩ : syracuseStep 3042103 = 4563155) B4563155
theorem B20540303 : Blo 1801602 20540303 := bstep (se 1 (by rfl) ⟨15405227, by rfl⟩ : syracuseStep 20540303 = 30810455) B30810455
theorem B2435999 : Blo 1801602 2435999 := bstep (se 1 (by rfl) ⟨1826999, by rfl⟩ : syracuseStep 2435999 = 3653999) B3653999
theorem B12987323 : Blo 1801602 12987323 := bstep (se 1 (by rfl) ⟨9740492, by rfl⟩ : syracuseStep 12987323 = 19480985) B19480985
theorem B3247055 : Blo 1801602 3247055 := bstep (se 1 (by rfl) ⟨2435291, by rfl⟩ : syracuseStep 3247055 = 4870583) B4870583
theorem B18508763 : Blo 1801602 18508763 := bstep (se 1 (by rfl) ⟨13881572, by rfl⟩ : syracuseStep 18508763 = 27763145) B27763145
theorem B2886635 : Blo 1801602 2886635 := bstep (se 1 (by rfl) ⟨2164976, by rfl⟩ : syracuseStep 2886635 = 4329953) B4329953
theorem B23104561 : Blo 1801602 23104561 := bstep (se 2 (by rfl) ⟨8664210, by rfl⟩ : syracuseStep 23104561 = 17328421) B17328421
theorem B2280631 : Blo 1801602 2280631 := bstep (se 1 (by rfl) ⟨1710473, by rfl⟩ : syracuseStep 2280631 = 3420947) B3420947
theorem B3042569 : Blo 1801602 3042569 := bstep (se 2 (by rfl) ⟨1140963, by rfl⟩ : syracuseStep 3042569 = 2281927) B2281927
theorem B105418037 : Blo 1801602 105418037 := bstep (se 5 (by rfl) ⟨4941470, by rfl⟩ : syracuseStep 105418037 = 9882941) B9882941
theorem B2026831 : Blo 1801602 2026831 := bstep (se 1 (by rfl) ⟨1520123, by rfl⟩ : syracuseStep 2026831 = 3040247) B3040247
theorem B11554127 : Blo 1801602 11554127 := bstep (se 1 (by rfl) ⟨8665595, by rfl⟩ : syracuseStep 11554127 = 17331191) B17331191
theorem B2281051 : Blo 1801602 2281051 := bstep (se 1 (by rfl) ⟨1710788, by rfl⟩ : syracuseStep 2281051 = 3421577) B3421577
theorem B6082343 : Blo 1801602 6082343 := bstep (se 1 (by rfl) ⟨4561757, by rfl⟩ : syracuseStep 6082343 = 9123515) B9123515
theorem B2027335 : Blo 1801602 2027335 := bstep (se 1 (by rfl) ⟨1520501, by rfl⟩ : syracuseStep 2027335 = 3041003) B3041003
theorem B25988941 : Blo 1801602 25988941 := bstep (se 3 (by rfl) ⟨4872926, by rfl⟩ : syracuseStep 25988941 = 9745853) B9745853
theorem B9129833 : Blo 1801602 9129833 := bstep (se 2 (by rfl) ⟨3423687, by rfl⟩ : syracuseStep 9129833 = 6847375) B6847375
theorem B8794079 : Blo 1801602 8794079 := bstep (se 1 (by rfl) ⟨6595559, by rfl⟩ : syracuseStep 8794079 = 13191119) B13191119
theorem B4624571 : Blo 1801602 4624571 := bstep (se 1 (by rfl) ⟨3468428, by rfl⟩ : syracuseStep 4624571 = 6936857) B6936857
theorem B9122057 : Blo 1801602 9122057 := bstep (se 2 (by rfl) ⟨3420771, by rfl⟩ : syracuseStep 9122057 = 6841543) B6841543
theorem B23105897 : Blo 1801602 23105897 := bstep (se 2 (by rfl) ⟨8664711, by rfl⟩ : syracuseStep 23105897 = 17329423) B17329423
theorem B2027983 : Blo 1801602 2027983 := bstep (se 1 (by rfl) ⟨1520987, by rfl⟩ : syracuseStep 2027983 = 3041975) B3041975
theorem B5132879 : Blo 1801602 5132879 := bstep (se 1 (by rfl) ⟨3849659, by rfl⟩ : syracuseStep 5132879 = 7699319) B7699319
theorem B21934745 : Blo 1801602 21934745 := bstep (se 2 (by rfl) ⟨8225529, by rfl⟩ : syracuseStep 21934745 = 16451059) B16451059
theorem B2888455 : Blo 1801602 2888455 := bstep (se 1 (by rfl) ⟨2166341, by rfl⟩ : syracuseStep 2888455 = 4332683) B4332683
theorem B7033625 : Blo 1801602 7033625 := bstep (se 2 (by rfl) ⟨2637609, by rfl⟩ : syracuseStep 7033625 = 5275219) B5275219
theorem B6083369 : Blo 1801602 6083369 := bstep (se 2 (by rfl) ⟨2281263, by rfl⟩ : syracuseStep 6083369 = 4562527) B4562527
theorem B18494303 : Blo 1801602 18494303 := bstep (se 1 (by rfl) ⟨13870727, by rfl⟩ : syracuseStep 18494303 = 27741455) B27741455
theorem B6083639 : Blo 1801602 6083639 := bstep (se 1 (by rfl) ⟨4562729, by rfl⟩ : syracuseStep 6083639 = 9125459) B9125459
theorem B2282671 : Blo 1801602 2282671 := bstep (se 1 (by rfl) ⟨1712003, by rfl⟩ : syracuseStep 2282671 = 3424007) B3424007
theorem B24679703 : Blo 1801602 24679703 := bstep (se 1 (by rfl) ⟨18509777, by rfl⟩ : syracuseStep 24679703 = 37019555) B37019555
theorem B3421531 : Blo 1801602 3421531 := bstep (se 1 (by rfl) ⟨2566148, by rfl⟩ : syracuseStep 3421531 = 5132297) B5132297
theorem B2028955 : Blo 1801602 2028955 := bstep (se 1 (by rfl) ⟨1521716, by rfl⟩ : syracuseStep 2028955 = 3043433) B3043433
theorem B5133755 : Blo 1801602 5133755 := bstep (se 1 (by rfl) ⟨3850316, by rfl⟩ : syracuseStep 5133755 = 7700633) B7700633
theorem B23410241 : Blo 1801602 23410241 := bstep (se 2 (by rfl) ⟨8778840, by rfl⟩ : syracuseStep 23410241 = 17557681) B17557681
theorem B43849349 : Blo 1801602 43849349 := bstep (se 4 (by rfl) ⟨4110876, by rfl⟩ : syracuseStep 43849349 = 8221753) B8221753
theorem B5855039 : Blo 1801602 5855039 := bstep (se 1 (by rfl) ⟨4391279, by rfl⟩ : syracuseStep 5855039 = 8782559) B8782559
theorem B6846403 : Blo 1801602 6846403 := bstep (se 1 (by rfl) ⟨5134802, by rfl⟩ : syracuseStep 6846403 = 10269605) B10269605
theorem B46176317 : Blo 1801602 46176317 := bstep (se 3 (by rfl) ⟨8658059, by rfl⟩ : syracuseStep 46176317 = 17316119) B17316119
theorem B3422351 : Blo 1801602 3422351 := bstep (se 1 (by rfl) ⟨2566763, by rfl⟩ : syracuseStep 3422351 = 5133527) B5133527
theorem B10262771 : Blo 1801602 10262771 := bstep (se 1 (by rfl) ⟨7697078, by rfl⟩ : syracuseStep 10262771 = 15394157) B15394157
theorem B3422587 : Blo 1801602 3422587 := bstep (se 1 (by rfl) ⟨2566940, by rfl⟩ : syracuseStep 3422587 = 5133881) B5133881
theorem B2112031 : Blo 1801602 2112031 := bstep (se 1 (by rfl) ⟨1584023, by rfl⟩ : syracuseStep 2112031 = 3168047) B3168047
theorem B26335817 : Blo 1801602 26335817 := bstep (se 2 (by rfl) ⟨9875931, by rfl⟩ : syracuseStep 26335817 = 19751863) B19751863
theorem B20535929 : Blo 1801602 20535929 := bstep (se 2 (by rfl) ⟨7700973, by rfl⟩ : syracuseStep 20535929 = 15401947) B15401947
theorem B131512967 : Blo 1801602 131512967 := bstep (se 1 (by rfl) ⟨98634725, by rfl⟩ : syracuseStep 131512967 = 197269451) B197269451
theorem B5134985 : Blo 1801602 5134985 := bstep (se 2 (by rfl) ⟨1925619, by rfl⟩ : syracuseStep 5134985 = 3851239) B3851239
theorem B4053851 : Blo 1801602 4053851 := bstep (se 1 (by rfl) ⟨3040388, by rfl⟩ : syracuseStep 4053851 = 6080777) B6080777
theorem B10263455 : Blo 1801602 10263455 := bstep (se 1 (by rfl) ⟨7697591, by rfl⟩ : syracuseStep 10263455 = 15395183) B15395183
theorem B34634699 : Blo 1801602 34634699 := bstep (se 1 (by rfl) ⟨25976024, by rfl⟩ : syracuseStep 34634699 = 51952049) B51952049
theorem B6085583 : Blo 1801602 6085583 := bstep (se 1 (by rfl) ⟨4564187, by rfl⟩ : syracuseStep 6085583 = 9128375) B9128375
theorem B26000423 : Blo 1801602 26000423 := bstep (se 1 (by rfl) ⟨19500317, by rfl⟩ : syracuseStep 26000423 = 39000635) B39000635
theorem B3849257 : Blo 1801602 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B4561991 : Blo 1801602 4561991 := bstep (se 1 (by rfl) ⟨3421493, by rfl⟩ : syracuseStep 4561991 = 6842987) B6842987
theorem B21937229 : Blo 1801602 21937229 := bstep (se 3 (by rfl) ⟨4113230, by rfl⟩ : syracuseStep 21937229 = 8226461) B8226461
theorem B2702519 : Blo 1801602 2702519 := bstep (se 1 (by rfl) ⟨2026889, by rfl⟩ : syracuseStep 2702519 = 4053779) B4053779
theorem B15400307 : Blo 1801602 15400307 := bstep (se 1 (by rfl) ⟨11550230, by rfl⟩ : syracuseStep 15400307 = 23100461) B23100461
theorem B2702759 : Blo 1801602 2702759 := bstep (se 1 (by rfl) ⟨2027069, by rfl⟩ : syracuseStep 2702759 = 4054139) B4054139
theorem B1801703 : Blo 1801602 1801703 := bstep (se 1 (by rfl) ⟨1351277, by rfl⟩ : syracuseStep 1801703 = 2702555) B2702555
theorem B2702843 : Blo 1801602 2702843 := bstep (se 1 (by rfl) ⟨2027132, by rfl⟩ : syracuseStep 2702843 = 4054265) B4054265
theorem B4054607 : Blo 1801602 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B1801819 : Blo 1801602 1801819 := bstep (se 1 (by rfl) ⟨1351364, by rfl⟩ : syracuseStep 1801819 = 2702729) B2702729
theorem B2702939 : Blo 1801602 2702939 := bstep (se 1 (by rfl) ⟨2027204, by rfl⟩ : syracuseStep 2702939 = 4054409) B4054409
theorem B4873871 : Blo 1801602 4873871 := bstep (se 1 (by rfl) ⟨3655403, by rfl⟩ : syracuseStep 4873871 = 7310807) B7310807
theorem B2703023 : Blo 1801602 2703023 := bstep (se 1 (by rfl) ⟨2027267, by rfl⟩ : syracuseStep 2703023 = 4054535) B4054535
theorem B2703143 : Blo 1801602 2703143 := bstep (se 1 (by rfl) ⟨2027357, by rfl⟩ : syracuseStep 2703143 = 4054715) B4054715
theorem B1802055 : Blo 1801602 1802055 := bstep (se 1 (by rfl) ⟨1351541, by rfl⟩ : syracuseStep 1802055 = 2703083) B2703083
theorem B2703227 : Blo 1801602 2703227 := bstep (se 1 (by rfl) ⟨2027420, by rfl⟩ : syracuseStep 2703227 = 4054841) B4054841
theorem B1802207 : Blo 1801602 1802207 := bstep (se 1 (by rfl) ⟨1351655, by rfl⟩ : syracuseStep 1802207 = 2703311) B2703311
theorem B2703551 : Blo 1801602 2703551 := bstep (se 1 (by rfl) ⟨2027663, by rfl⟩ : syracuseStep 2703551 = 4055327) B4055327
theorem B1802431 : Blo 1801602 1802431 := bstep (se 1 (by rfl) ⟨1351823, by rfl⟩ : syracuseStep 1802431 = 2703647) B2703647
theorem B1802447 : Blo 1801602 1802447 := bstep (se 1 (by rfl) ⟨1351835, by rfl⟩ : syracuseStep 1802447 = 2703671) B2703671
theorem B17318123 : Blo 1801602 17318123 := bstep (se 1 (by rfl) ⟨12988592, by rfl⟩ : syracuseStep 17318123 = 25977185) B25977185
theorem B1802495 : Blo 1801602 1802495 := bstep (se 1 (by rfl) ⟨1351871, by rfl⟩ : syracuseStep 1802495 = 2703743) B2703743
theorem B1802543 : Blo 1801602 1802543 := bstep (se 1 (by rfl) ⟨1351907, by rfl⟩ : syracuseStep 1802543 = 2703815) B2703815
theorem B9126269 : Blo 1801602 9126269 := bstep (se 3 (by rfl) ⟨1711175, by rfl⟩ : syracuseStep 9126269 = 3422351) B3422351
theorem B14623163 : Blo 1801602 14623163 := bstep (se 1 (by rfl) ⟨10967372, by rfl⟩ : syracuseStep 14623163 = 21934745) B21934745
theorem B4563449 : Blo 1801602 4563449 := bstep (se 2 (by rfl) ⟨1711293, by rfl⟩ : syracuseStep 4563449 = 3422587) B3422587
theorem B4055579 : Blo 1801602 4055579 := bstep (se 1 (by rfl) ⟨3041684, by rfl⟩ : syracuseStep 4055579 = 6083369) B6083369
theorem B1802779 : Blo 1801602 1802779 := bstep (se 1 (by rfl) ⟨1352084, by rfl⟩ : syracuseStep 1802779 = 2704169) B2704169
theorem B1802783 : Blo 1801602 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B2703977 : Blo 1801602 2703977 := bstep (se 2 (by rfl) ⟨1013991, by rfl⟩ : syracuseStep 2703977 = 2027983) B2027983
theorem B2703983 : Blo 1801602 2703983 := bstep (se 1 (by rfl) ⟨2027987, by rfl⟩ : syracuseStep 2703983 = 4055975) B4055975
theorem B1802863 : Blo 1801602 1802863 := bstep (se 1 (by rfl) ⟨1352147, by rfl⟩ : syracuseStep 1802863 = 2704295) B2704295
theorem B1802919 : Blo 1801602 1802919 := bstep (se 1 (by rfl) ⟨1352189, by rfl⟩ : syracuseStep 1802919 = 2704379) B2704379
theorem B4055759 : Blo 1801602 4055759 := bstep (se 1 (by rfl) ⟨3041819, by rfl⟩ : syracuseStep 4055759 = 6083639) B6083639
theorem B1802959 : Blo 1801602 1802959 := bstep (se 1 (by rfl) ⟨1352219, by rfl⟩ : syracuseStep 1802959 = 2704439) B2704439
theorem B1803039 : Blo 1801602 1803039 := bstep (se 1 (by rfl) ⟨1352279, by rfl⟩ : syracuseStep 1803039 = 2704559) B2704559
theorem B11551643 : Blo 1801602 11551643 := bstep (se 1 (by rfl) ⟨8663732, by rfl⟩ : syracuseStep 11551643 = 17327465) B17327465
theorem B3851273 : Blo 1801602 3851273 := bstep (se 2 (by rfl) ⟨1444227, by rfl⟩ : syracuseStep 3851273 = 2888455) B2888455
theorem B15606827 : Blo 1801602 15606827 := bstep (se 1 (by rfl) ⟨11705120, by rfl⟩ : syracuseStep 15606827 = 23410241) B23410241
theorem B1803311 : Blo 1801602 1803311 := bstep (se 1 (by rfl) ⟨1352483, by rfl⟩ : syracuseStep 1803311 = 2704967) B2704967
theorem B4056137 : Blo 1801602 4056137 := bstep (se 2 (by rfl) ⟨1521051, by rfl⟩ : syracuseStep 4056137 = 3042103) B3042103
theorem B1803375 : Blo 1801602 1803375 := bstep (se 1 (by rfl) ⟨1352531, by rfl⟩ : syracuseStep 1803375 = 2705063) B2705063
theorem B1803431 : Blo 1801602 1803431 := bstep (se 1 (by rfl) ⟨1352573, by rfl⟩ : syracuseStep 1803431 = 2705147) B2705147
theorem B1803455 : Blo 1801602 1803455 := bstep (se 1 (by rfl) ⟨1352591, by rfl⟩ : syracuseStep 1803455 = 2705183) B2705183
theorem B2704607 : Blo 1801602 2704607 := bstep (se 1 (by rfl) ⟨2028455, by rfl⟩ : syracuseStep 2704607 = 4056911) B4056911
theorem B1803487 : Blo 1801602 1803487 := bstep (se 1 (by rfl) ⟨1352615, by rfl⟩ : syracuseStep 1803487 = 2705231) B2705231
theorem B2704619 : Blo 1801602 2704619 := bstep (se 1 (by rfl) ⟨2028464, by rfl⟩ : syracuseStep 2704619 = 4056929) B4056929
theorem B1803567 : Blo 1801602 1803567 := bstep (se 1 (by rfl) ⟨1352675, by rfl⟩ : syracuseStep 1803567 = 2705351) B2705351
theorem B6841847 : Blo 1801602 6841847 := bstep (se 1 (by rfl) ⟨5131385, by rfl⟩ : syracuseStep 6841847 = 10262771) B10262771
theorem B3040841 : Blo 1801602 3040841 := bstep (se 2 (by rfl) ⟨1140315, by rfl⟩ : syracuseStep 3040841 = 2280631) B2280631
theorem B2705003 : Blo 1801602 2705003 := bstep (se 1 (by rfl) ⟨2028752, by rfl⟩ : syracuseStep 2705003 = 4057505) B4057505
theorem B2705087 : Blo 1801602 2705087 := bstep (se 1 (by rfl) ⟨2028815, by rfl⟩ : syracuseStep 2705087 = 4057631) B4057631
theorem B17557211 : Blo 1801602 17557211 := bstep (se 1 (by rfl) ⟨13167908, by rfl⟩ : syracuseStep 17557211 = 26335817) B26335817
theorem B13690619 : Blo 1801602 13690619 := bstep (se 1 (by rfl) ⟨10267964, by rfl⟩ : syracuseStep 13690619 = 20535929) B20535929
theorem B2705273 : Blo 1801602 2705273 := bstep (se 2 (by rfl) ⟨1014477, by rfl⟩ : syracuseStep 2705273 = 2028955) B2028955
theorem B6842303 : Blo 1801602 6842303 := bstep (se 1 (by rfl) ⟨5131727, by rfl⟩ : syracuseStep 6842303 = 10263455) B10263455
theorem B2164703 : Blo 1801602 2164703 := bstep (se 1 (by rfl) ⟨1623527, by rfl⟩ : syracuseStep 2164703 = 3247055) B3247055
theorem B4057055 : Blo 1801602 4057055 := bstep (se 1 (by rfl) ⟨3042791, by rfl⟩ : syracuseStep 4057055 = 6085583) B6085583
theorem B12339175 : Blo 1801602 12339175 := bstep (se 1 (by rfl) ⟨9254381, by rfl⟩ : syracuseStep 12339175 = 18508763) B18508763
theorem B2566171 : Blo 1801602 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B3041327 : Blo 1801602 3041327 := bstep (se 1 (by rfl) ⟨2280995, by rfl⟩ : syracuseStep 3041327 = 4561991) B4561991
theorem B14624819 : Blo 1801602 14624819 := bstep (se 1 (by rfl) ⟨10968614, by rfl⟩ : syracuseStep 14624819 = 21937229) B21937229
theorem B3041401 : Blo 1801602 3041401 := bstep (se 2 (by rfl) ⟨1140525, by rfl⟩ : syracuseStep 3041401 = 2281051) B2281051
theorem B7702751 : Blo 1801602 7702751 := bstep (se 1 (by rfl) ⟨5777063, by rfl⟩ : syracuseStep 7702751 = 11554127) B11554127
theorem B10266871 : Blo 1801602 10266871 := bstep (se 1 (by rfl) ⟨7700153, by rfl⟩ : syracuseStep 10266871 = 15400307) B15400307
theorem B49318141 : Blo 1801602 49318141 := bstep (se 3 (by rfl) ⟨9247151, by rfl⟩ : syracuseStep 49318141 = 18494303) B18494303
theorem B9128537 : Blo 1801602 9128537 := bstep (se 2 (by rfl) ⟨3423201, by rfl⟩ : syracuseStep 9128537 = 6846403) B6846403
theorem B6081371 : Blo 1801602 6081371 := bstep (se 1 (by rfl) ⟨4561028, by rfl⟩ : syracuseStep 6081371 = 9122057) B9122057
theorem B6843275 : Blo 1801602 6843275 := bstep (se 1 (by rfl) ⟨5132456, by rfl⟩ : syracuseStep 6843275 = 10264913) B10264913
theorem B15403931 : Blo 1801602 15403931 := bstep (se 1 (by rfl) ⟨11552948, by rfl⟩ : syracuseStep 15403931 = 23105897) B23105897
theorem B4058063 : Blo 1801602 4058063 := bstep (se 1 (by rfl) ⟨3043547, by rfl⟩ : syracuseStep 4058063 = 6087095) B6087095
theorem B6499457 : Blo 1801602 6499457 := bstep (se 2 (by rfl) ⟨2437296, by rfl⟩ : syracuseStep 6499457 = 4874593) B4874593
theorem B12332189 : Blo 1801602 12332189 := bstep (se 3 (by rfl) ⟨2312285, by rfl⟩ : syracuseStep 12332189 = 4624571) B4624571
theorem B4689083 : Blo 1801602 4689083 := bstep (se 1 (by rfl) ⟨3516812, by rfl⟩ : syracuseStep 4689083 = 7033625) B7033625
theorem B2026975 : Blo 1801602 2026975 := bstep (se 1 (by rfl) ⟨1520231, by rfl⟩ : syracuseStep 2026975 = 3040463) B3040463
theorem B16453135 : Blo 1801602 16453135 := bstep (se 1 (by rfl) ⟨12339851, by rfl⟩ : syracuseStep 16453135 = 24679703) B24679703
theorem B29232899 : Blo 1801602 29232899 := bstep (se 1 (by rfl) ⟨21924674, by rfl⟩ : syracuseStep 29232899 = 43849349) B43849349
theorem B6844247 : Blo 1801602 6844247 := bstep (se 1 (by rfl) ⟨5133185, by rfl⟩ : syracuseStep 6844247 = 10266371) B10266371
theorem B2027515 : Blo 1801602 2027515 := bstep (se 1 (by rfl) ⟨1520636, by rfl⟩ : syracuseStep 2027515 = 3041273) B3041273
theorem B30806081 : Blo 1801602 30806081 := bstep (se 2 (by rfl) ⟨11552280, by rfl⟩ : syracuseStep 30806081 = 23104561) B23104561
theorem B2027623 : Blo 1801602 2027623 := bstep (se 1 (by rfl) ⟨1520717, by rfl⟩ : syracuseStep 2027623 = 3041435) B3041435
theorem B2027695 : Blo 1801602 2027695 := bstep (se 1 (by rfl) ⟨1520771, by rfl⟩ : syracuseStep 2027695 = 3041543) B3041543
theorem B3043561 : Blo 1801602 3043561 := bstep (se 2 (by rfl) ⟨1141335, by rfl⟩ : syracuseStep 3043561 = 2282671) B2282671
theorem B87675311 : Blo 1801602 87675311 := bstep (se 1 (by rfl) ⟨65756483, by rfl⟩ : syracuseStep 87675311 = 131512967) B131512967
theorem B13693535 : Blo 1801602 13693535 := bstep (se 1 (by rfl) ⟨10270151, by rfl⟩ : syracuseStep 13693535 = 20540303) B20540303
theorem B23089799 : Blo 1801602 23089799 := bstep (se 1 (by rfl) ⟨17317349, by rfl⟩ : syracuseStep 23089799 = 34634699) B34634699
theorem B2028379 : Blo 1801602 2028379 := bstep (se 1 (by rfl) ⟨1521284, by rfl⟩ : syracuseStep 2028379 = 3042569) B3042569
theorem B237024301 : Blo 1801602 237024301 := bstep (se 3 (by rfl) ⟨44442056, by rfl⟩ : syracuseStep 237024301 = 88884113) B88884113
theorem B3249247 : Blo 1801602 3249247 := bstep (se 1 (by rfl) ⟨2436935, by rfl⟩ : syracuseStep 3249247 = 4873871) B4873871
theorem B7697693 : Blo 1801602 7697693 := bstep (se 3 (by rfl) ⟨1443317, by rfl⟩ : syracuseStep 7697693 = 2886635) B2886635
theorem B5862719 : Blo 1801602 5862719 := bstep (se 1 (by rfl) ⟨4397039, by rfl⟩ : syracuseStep 5862719 = 8794079) B8794079
theorem B5772655 : Blo 1801602 5772655 := bstep (se 1 (by rfl) ⟨4329491, by rfl⟩ : syracuseStep 5772655 = 8658983) B8658983
theorem B9123353 : Blo 1801602 9123353 := bstep (se 2 (by rfl) ⟨3421257, by rfl⟩ : syracuseStep 9123353 = 6842515) B6842515
theorem B6084233 : Blo 1801602 6084233 := bstep (se 2 (by rfl) ⟨2281587, by rfl⟩ : syracuseStep 6084233 = 4563175) B4563175
theorem B3421919 : Blo 1801602 3421919 := bstep (se 1 (by rfl) ⟨2566439, by rfl⟩ : syracuseStep 3421919 = 5132879) B5132879
theorem B55498679 : Blo 1801602 55498679 := bstep (se 1 (by rfl) ⟨41624009, by rfl⟩ : syracuseStep 55498679 = 83248019) B83248019
theorem B35133421 : Blo 1801602 35133421 := bstep (se 3 (by rfl) ⟨6587516, by rfl⟩ : syracuseStep 35133421 = 13175033) B13175033
theorem B62453749 : Blo 1801602 62453749 := bstep (se 5 (by rfl) ⟨2927519, by rfl⟩ : syracuseStep 62453749 = 5855039) B5855039
theorem B4560887 : Blo 1801602 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B2816041 : Blo 1801602 2816041 := bstep (se 2 (by rfl) ⟨1056015, by rfl⟩ : syracuseStep 2816041 = 2112031) B2112031
theorem B6936673 : Blo 1801602 6936673 := bstep (se 2 (by rfl) ⟨2601252, by rfl⟩ : syracuseStep 6936673 = 5202505) B5202505
theorem B6084827 : Blo 1801602 6084827 := bstep (se 1 (by rfl) ⟨4563620, by rfl⟩ : syracuseStep 6084827 = 9127241) B9127241
theorem B3422503 : Blo 1801602 3422503 := bstep (se 1 (by rfl) ⟨2566877, by rfl⟩ : syracuseStep 3422503 = 5133755) B5133755
theorem B6085097 : Blo 1801602 6085097 := bstep (se 2 (by rfl) ⟨2281911, by rfl⟩ : syracuseStep 6085097 = 4563823) B4563823
theorem B23419489 : Blo 1801602 23419489 := bstep (se 2 (by rfl) ⟨8782308, by rfl⟩ : syracuseStep 23419489 = 17564617) B17564617
theorem B30784211 : Blo 1801602 30784211 := bstep (se 1 (by rfl) ⟨23088158, by rfl⟩ : syracuseStep 30784211 = 46176317) B46176317
theorem B4053815 : Blo 1801602 4053815 := bstep (se 1 (by rfl) ⟨3040361, by rfl⟩ : syracuseStep 4053815 = 6080723) B6080723
theorem B15391559 : Blo 1801602 15391559 := bstep (se 1 (by rfl) ⟨11543669, by rfl⟩ : syracuseStep 15391559 = 23087339) B23087339
theorem B4053995 : Blo 1801602 4053995 := bstep (se 1 (by rfl) ⟨3040496, by rfl⟩ : syracuseStep 4053995 = 6080993) B6080993
theorem B5135339 : Blo 1801602 5135339 := bstep (se 1 (by rfl) ⟨3851504, by rfl⟩ : syracuseStep 5135339 = 7703009) B7703009
theorem B25983989 : Blo 1801602 25983989 := bstep (se 5 (by rfl) ⟨1217999, by rfl⟩ : syracuseStep 25983989 = 2435999) B2435999
theorem B3423323 : Blo 1801602 3423323 := bstep (se 1 (by rfl) ⟨2567492, by rfl⟩ : syracuseStep 3423323 = 5134985) B5134985
theorem B2702441 : Blo 1801602 2702441 := bstep (se 2 (by rfl) ⟨1013415, by rfl⟩ : syracuseStep 2702441 = 2026831) B2026831
theorem B4562041 : Blo 1801602 4562041 := bstep (se 2 (by rfl) ⟨1710765, by rfl⟩ : syracuseStep 4562041 = 3421531) B3421531
theorem B2702567 : Blo 1801602 2702567 := bstep (se 1 (by rfl) ⟨2026925, by rfl⟩ : syracuseStep 2702567 = 4053851) B4053851
theorem B8658215 : Blo 1801602 8658215 := bstep (se 1 (by rfl) ⟨6493661, by rfl⟩ : syracuseStep 8658215 = 12987323) B12987323
theorem B17333615 : Blo 1801602 17333615 := bstep (se 1 (by rfl) ⟨13000211, by rfl⟩ : syracuseStep 17333615 = 26000423) B26000423
theorem B1801679 : Blo 1801602 1801679 := bstep (se 1 (by rfl) ⟨1351259, by rfl⟩ : syracuseStep 1801679 = 2702519) B2702519
theorem B70278691 : Blo 1801602 70278691 := bstep (se 1 (by rfl) ⟨52709018, by rfl⟩ : syracuseStep 70278691 = 105418037) B105418037
theorem B1801839 : Blo 1801602 1801839 := bstep (se 1 (by rfl) ⟨1351379, by rfl⟩ : syracuseStep 1801839 = 2702759) B2702759
theorem B1801895 : Blo 1801602 1801895 := bstep (se 1 (by rfl) ⟨1351421, by rfl⟩ : syracuseStep 1801895 = 2702843) B2702843
theorem B2703071 : Blo 1801602 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B1801959 : Blo 1801602 1801959 := bstep (se 1 (by rfl) ⟨1351469, by rfl⟩ : syracuseStep 1801959 = 2702939) B2702939
theorem B2703113 : Blo 1801602 2703113 := bstep (se 2 (by rfl) ⟨1013667, by rfl⟩ : syracuseStep 2703113 = 2027335) B2027335
theorem B34651921 : Blo 1801602 34651921 := bstep (se 2 (by rfl) ⟨12994470, by rfl⟩ : syracuseStep 34651921 = 25988941) B25988941
theorem B1802015 : Blo 1801602 1802015 := bstep (se 1 (by rfl) ⟨1351511, by rfl⟩ : syracuseStep 1802015 = 2703023) B2703023
theorem B1802095 : Blo 1801602 1802095 := bstep (se 1 (by rfl) ⟨1351571, by rfl⟩ : syracuseStep 1802095 = 2703143) B2703143
theorem B4054895 : Blo 1801602 4054895 := bstep (se 1 (by rfl) ⟨3041171, by rfl⟩ : syracuseStep 4054895 = 6082343) B6082343
theorem B6086555 : Blo 1801602 6086555 := bstep (se 1 (by rfl) ⟨4564916, by rfl⟩ : syracuseStep 6086555 = 9129833) B9129833
theorem B1802151 : Blo 1801602 1802151 := bstep (se 1 (by rfl) ⟨1351613, by rfl⟩ : syracuseStep 1802151 = 2703227) B2703227
theorem B20537387 : Blo 1801602 20537387 := bstep (se 1 (by rfl) ⟨15403040, by rfl⟩ : syracuseStep 20537387 = 30806081) B30806081
theorem B1802367 : Blo 1801602 1802367 := bstep (se 1 (by rfl) ⟨1351775, by rfl⟩ : syracuseStep 1802367 = 2703551) B2703551
theorem B9248897 : Blo 1801602 9248897 := bstep (se 2 (by rfl) ⟨3468336, by rfl⟩ : syracuseStep 9248897 = 6936673) B6936673
theorem B2703497 : Blo 1801602 2703497 := bstep (se 2 (by rfl) ⟨1013811, by rfl⟩ : syracuseStep 2703497 = 2027623) B2027623
theorem B4055201 : Blo 1801602 4055201 := bstep (se 2 (by rfl) ⟨1520700, by rfl⟩ : syracuseStep 4055201 = 3041401) B3041401
theorem B2703593 : Blo 1801602 2703593 := bstep (se 2 (by rfl) ⟨1013847, by rfl⟩ : syracuseStep 2703593 = 2027695) B2027695
theorem B58450207 : Blo 1801602 58450207 := bstep (se 1 (by rfl) ⟨43837655, by rfl⟩ : syracuseStep 58450207 = 87675311) B87675311
theorem B9748775 : Blo 1801602 9748775 := bstep (se 1 (by rfl) ⟨7311581, by rfl⟩ : syracuseStep 9748775 = 14623163) B14623163
theorem B13689161 : Blo 1801602 13689161 := bstep (se 2 (by rfl) ⟨5133435, by rfl⟩ : syracuseStep 13689161 = 10266871) B10266871
theorem B65757521 : Blo 1801602 65757521 := bstep (se 2 (by rfl) ⟨24659070, by rfl⟩ : syracuseStep 65757521 = 49318141) B49318141
theorem B2703719 : Blo 1801602 2703719 := bstep (se 1 (by rfl) ⟨2027789, by rfl⟩ : syracuseStep 2703719 = 4055579) B4055579
theorem B4563337 : Blo 1801602 4563337 := bstep (se 2 (by rfl) ⟨1711251, by rfl⟩ : syracuseStep 4563337 = 3422503) B3422503
theorem B1802651 : Blo 1801602 1802651 := bstep (se 1 (by rfl) ⟨1351988, by rfl⟩ : syracuseStep 1802651 = 2703977) B2703977
theorem B1802655 : Blo 1801602 1802655 := bstep (se 1 (by rfl) ⟨1351991, by rfl⟩ : syracuseStep 1802655 = 2703983) B2703983
theorem B15393199 : Blo 1801602 15393199 := bstep (se 1 (by rfl) ⟨11544899, by rfl⟩ : syracuseStep 15393199 = 23089799) B23089799
theorem B2703839 : Blo 1801602 2703839 := bstep (se 1 (by rfl) ⟨2027879, by rfl⟩ : syracuseStep 2703839 = 4055759) B4055759
theorem B7701095 : Blo 1801602 7701095 := bstep (se 1 (by rfl) ⟨5775821, by rfl⟩ : syracuseStep 7701095 = 11551643) B11551643
theorem B10404551 : Blo 1801602 10404551 := bstep (se 1 (by rfl) ⟨7803413, by rfl⟩ : syracuseStep 10404551 = 15606827) B15606827
theorem B2704091 : Blo 1801602 2704091 := bstep (se 1 (by rfl) ⟨2028068, by rfl⟩ : syracuseStep 2704091 = 4056137) B4056137
theorem B1803071 : Blo 1801602 1803071 := bstep (se 1 (by rfl) ⟨1352303, by rfl⟩ : syracuseStep 1803071 = 2704607) B2704607
theorem B1803079 : Blo 1801602 1803079 := bstep (se 1 (by rfl) ⟨1352309, by rfl⟩ : syracuseStep 1803079 = 2704619) B2704619
theorem B1803335 : Blo 1801602 1803335 := bstep (se 1 (by rfl) ⟨1352501, by rfl⟩ : syracuseStep 1803335 = 2705003) B2705003
theorem B4056155 : Blo 1801602 4056155 := bstep (se 1 (by rfl) ⟨3042116, by rfl⟩ : syracuseStep 4056155 = 6084233) B6084233
theorem B2704505 : Blo 1801602 2704505 := bstep (se 2 (by rfl) ⟨1014189, by rfl⟩ : syracuseStep 2704505 = 2028379) B2028379
theorem B1803391 : Blo 1801602 1803391 := bstep (se 1 (by rfl) ⟨1352543, by rfl⟩ : syracuseStep 1803391 = 2705087) B2705087
theorem B9127079 : Blo 1801602 9127079 := bstep (se 1 (by rfl) ⟨6845309, by rfl⟩ : syracuseStep 9127079 = 13690619) B13690619
theorem B1803515 : Blo 1801602 1803515 := bstep (se 1 (by rfl) ⟨1352636, by rfl⟩ : syracuseStep 1803515 = 2705273) B2705273
theorem B2704703 : Blo 1801602 2704703 := bstep (se 1 (by rfl) ⟨2028527, by rfl⟩ : syracuseStep 2704703 = 4057055) B4057055
theorem B3040591 : Blo 1801602 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B9749879 : Blo 1801602 9749879 := bstep (se 1 (by rfl) ⟨7312409, by rfl⟩ : syracuseStep 9749879 = 14624819) B14624819
theorem B316032401 : Blo 1801602 316032401 := bstep (se 2 (by rfl) ⟨118512150, by rfl⟩ : syracuseStep 316032401 = 237024301) B237024301
theorem B4056551 : Blo 1801602 4056551 := bstep (se 1 (by rfl) ⟨3042413, by rfl⟩ : syracuseStep 4056551 = 6084827) B6084827
theorem B4056731 : Blo 1801602 4056731 := bstep (se 1 (by rfl) ⟨3042548, by rfl⟩ : syracuseStep 4056731 = 6085097) B6085097
theorem B20522807 : Blo 1801602 20522807 := bstep (se 1 (by rfl) ⟨15392105, by rfl⟩ : syracuseStep 20522807 = 30784211) B30784211
theorem B2705375 : Blo 1801602 2705375 := bstep (se 1 (by rfl) ⟨2029031, by rfl⟩ : syracuseStep 2705375 = 4058063) B4058063
theorem B4057703 : Blo 1801602 4057703 := bstep (se 1 (by rfl) ⟨3043277, by rfl⟩ : syracuseStep 4057703 = 6086555) B6086555
theorem B16452233 : Blo 1801602 16452233 := bstep (se 2 (by rfl) ⟨6169587, by rfl⟩ : syracuseStep 16452233 = 12339175) B12339175
theorem B46844561 : Blo 1801602 46844561 := bstep (se 2 (by rfl) ⟨17566710, by rfl⟩ : syracuseStep 46844561 = 35133421) B35133421
theorem B3754721 : Blo 1801602 3754721 := bstep (se 2 (by rfl) ⟨1408020, by rfl⟩ : syracuseStep 3754721 = 2816041) B2816041
theorem B11545415 : Blo 1801602 11545415 := bstep (se 1 (by rfl) ⟨8659061, by rfl⟩ : syracuseStep 11545415 = 17318123) B17318123
theorem B9128861 : Blo 1801602 9128861 := bstep (se 3 (by rfl) ⟨1711661, by rfl⟩ : syracuseStep 9128861 = 3423323) B3423323
theorem B4058081 : Blo 1801602 4058081 := bstep (se 2 (by rfl) ⟨1521780, by rfl⟩ : syracuseStep 4058081 = 3043561) B3043561
theorem B3042299 : Blo 1801602 3042299 := bstep (se 1 (by rfl) ⟨2281724, by rfl⟩ : syracuseStep 3042299 = 4563449) B4563449
theorem B9129023 : Blo 1801602 9129023 := bstep (se 1 (by rfl) ⟨6846767, by rfl⟩ : syracuseStep 9129023 = 13693535) B13693535
theorem B32885837 : Blo 1801602 32885837 := bstep (se 3 (by rfl) ⟨6166094, by rfl⟩ : syracuseStep 32885837 = 12332189) B12332189
theorem B15633917 : Blo 1801602 15633917 := bstep (se 3 (by rfl) ⟨2931359, by rfl⟩ : syracuseStep 15633917 = 5862719) B5862719
theorem B6082235 : Blo 1801602 6082235 := bstep (se 1 (by rfl) ⟨4561676, by rfl⟩ : syracuseStep 6082235 = 9123353) B9123353
theorem B2027227 : Blo 1801602 2027227 := bstep (se 1 (by rfl) ⟨1520420, by rfl⟩ : syracuseStep 2027227 = 3040841) B3040841
theorem B2281279 : Blo 1801602 2281279 := bstep (se 1 (by rfl) ⟨1710959, by rfl⟩ : syracuseStep 2281279 = 3421919) B3421919
theorem B36999119 : Blo 1801602 36999119 := bstep (se 1 (by rfl) ⟨27749339, by rfl⟩ : syracuseStep 36999119 = 55498679) B55498679
theorem B2027551 : Blo 1801602 2027551 := bstep (se 1 (by rfl) ⟨1520663, by rfl⟩ : syracuseStep 2027551 = 3041327) B3041327
theorem B6082721 : Blo 1801602 6082721 := bstep (se 2 (by rfl) ⟨2281020, by rfl⟩ : syracuseStep 6082721 = 4562041) B4562041
theorem B7696873 : Blo 1801602 7696873 := bstep (se 2 (by rfl) ⟨2886327, by rfl⟩ : syracuseStep 7696873 = 5772655) B5772655
theorem B10261039 : Blo 1801602 10261039 := bstep (se 1 (by rfl) ⟨7695779, by rfl⟩ : syracuseStep 10261039 = 15391559) B15391559
theorem B10269287 : Blo 1801602 10269287 := bstep (se 1 (by rfl) ⟨7701965, by rfl⟩ : syracuseStep 10269287 = 15403931) B15403931
theorem B17322659 : Blo 1801602 17322659 := bstep (se 1 (by rfl) ⟨12991994, by rfl⟩ : syracuseStep 17322659 = 25983989) B25983989
theorem B93704921 : Blo 1801602 93704921 := bstep (se 2 (by rfl) ⟨35139345, by rfl⟩ : syracuseStep 93704921 = 70278691) B70278691
theorem B3126055 : Blo 1801602 3126055 := bstep (se 1 (by rfl) ⟨2344541, by rfl⟩ : syracuseStep 3126055 = 4689083) B4689083
theorem B5772143 : Blo 1801602 5772143 := bstep (se 1 (by rfl) ⟨4329107, by rfl⟩ : syracuseStep 5772143 = 8658215) B8658215
theorem B11555743 : Blo 1801602 11555743 := bstep (se 1 (by rfl) ⟨8666807, by rfl⟩ : syracuseStep 11555743 = 17333615) B17333615
theorem B5772541 : Blo 1801602 5772541 := bstep (se 3 (by rfl) ⟨1082351, by rfl⟩ : syracuseStep 5772541 = 2164703) B2164703
theorem B10270061 : Blo 1801602 10270061 := bstep (se 3 (by rfl) ⟨1925636, by rfl⟩ : syracuseStep 10270061 = 3851273) B3851273
theorem B13686245 : Blo 1801602 13686245 := bstep (se 4 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 13686245 = 2566171) B2566171
theorem B6084179 : Blo 1801602 6084179 := bstep (se 1 (by rfl) ⟨4563134, by rfl⟩ : syracuseStep 6084179 = 9126269) B9126269
theorem B20527181 : Blo 1801602 20527181 := bstep (se 3 (by rfl) ⟨3848846, by rfl⟩ : syracuseStep 20527181 = 7697693) B7697693
theorem B31225985 : Blo 1801602 31225985 := bstep (se 2 (by rfl) ⟨11709744, by rfl⟩ : syracuseStep 31225985 = 23419489) B23419489
theorem B4561231 : Blo 1801602 4561231 := bstep (se 1 (by rfl) ⟨3420923, by rfl⟩ : syracuseStep 4561231 = 6841847) B6841847
theorem B11704807 : Blo 1801602 11704807 := bstep (se 1 (by rfl) ⟨8778605, by rfl⟩ : syracuseStep 11704807 = 17557211) B17557211
theorem B4561535 : Blo 1801602 4561535 := bstep (se 1 (by rfl) ⟨3421151, by rfl⟩ : syracuseStep 4561535 = 6842303) B6842303
theorem B4332329 : Blo 1801602 4332329 := bstep (se 2 (by rfl) ⟨1624623, by rfl⟩ : syracuseStep 4332329 = 3249247) B3249247
theorem B5135167 : Blo 1801602 5135167 := bstep (se 1 (by rfl) ⟨3851375, by rfl⟩ : syracuseStep 5135167 = 7702751) B7702751
theorem B6085691 : Blo 1801602 6085691 := bstep (se 1 (by rfl) ⟨4564268, by rfl⟩ : syracuseStep 6085691 = 9128537) B9128537
theorem B2702543 : Blo 1801602 2702543 := bstep (se 1 (by rfl) ⟨2026907, by rfl⟩ : syracuseStep 2702543 = 4053815) B4053815
theorem B4054247 : Blo 1801602 4054247 := bstep (se 1 (by rfl) ⟨3040685, by rfl⟩ : syracuseStep 4054247 = 6081371) B6081371
theorem B4562183 : Blo 1801602 4562183 := bstep (se 1 (by rfl) ⟨3421637, by rfl⟩ : syracuseStep 4562183 = 6843275) B6843275
theorem B2702633 : Blo 1801602 2702633 := bstep (se 2 (by rfl) ⟨1013487, by rfl⟩ : syracuseStep 2702633 = 2026975) B2026975
theorem B2702663 : Blo 1801602 2702663 := bstep (se 1 (by rfl) ⟨2026997, by rfl⟩ : syracuseStep 2702663 = 4053995) B4053995
theorem B3423559 : Blo 1801602 3423559 := bstep (se 1 (by rfl) ⟨2567669, by rfl⟩ : syracuseStep 3423559 = 5135339) B5135339
theorem B21937513 : Blo 1801602 21937513 := bstep (se 2 (by rfl) ⟨8226567, by rfl⟩ : syracuseStep 21937513 = 16453135) B16453135
theorem B1801627 : Blo 1801602 1801627 := bstep (se 1 (by rfl) ⟨1351220, by rfl⟩ : syracuseStep 1801627 = 2702441) B2702441
theorem B4332971 : Blo 1801602 4332971 := bstep (se 1 (by rfl) ⟨3249728, by rfl⟩ : syracuseStep 4332971 = 6499457) B6499457
theorem B1801711 : Blo 1801602 1801711 := bstep (se 1 (by rfl) ⟨1351283, by rfl⟩ : syracuseStep 1801711 = 2702567) B2702567
theorem B46202561 : Blo 1801602 46202561 := bstep (se 2 (by rfl) ⟨17325960, by rfl⟩ : syracuseStep 46202561 = 34651921) B34651921
theorem B1802047 : Blo 1801602 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B19488599 : Blo 1801602 19488599 := bstep (se 1 (by rfl) ⟨14616449, by rfl⟩ : syracuseStep 19488599 = 29232899) B29232899
theorem B1802075 : Blo 1801602 1802075 := bstep (se 1 (by rfl) ⟨1351556, by rfl⟩ : syracuseStep 1802075 = 2703113) B2703113
theorem B4562831 : Blo 1801602 4562831 := bstep (se 1 (by rfl) ⟨3422123, by rfl⟩ : syracuseStep 4562831 = 6844247) B6844247
theorem B2703263 : Blo 1801602 2703263 := bstep (se 1 (by rfl) ⟨2027447, by rfl⟩ : syracuseStep 2703263 = 4054895) B4054895
theorem B83271665 : Blo 1801602 83271665 := bstep (se 2 (by rfl) ⟨31226874, by rfl⟩ : syracuseStep 83271665 = 62453749) B62453749
theorem B2703353 : Blo 1801602 2703353 := bstep (se 2 (by rfl) ⟨1013757, by rfl⟩ : syracuseStep 2703353 = 2027515) B2027515
theorem B2703401 : Blo 1801602 2703401 := bstep (se 2 (by rfl) ⟨1013775, by rfl⟩ : syracuseStep 2703401 = 2027551) B2027551
theorem B1802331 : Blo 1801602 1802331 := bstep (se 1 (by rfl) ⟨1351748, by rfl⟩ : syracuseStep 1802331 = 2703497) B2703497
theorem B4055147 : Blo 1801602 4055147 := bstep (se 1 (by rfl) ⟨3041360, by rfl⟩ : syracuseStep 4055147 = 6082721) B6082721
theorem B2703467 : Blo 1801602 2703467 := bstep (se 1 (by rfl) ⟨2027600, by rfl⟩ : syracuseStep 2703467 = 4055201) B4055201
theorem B1802395 : Blo 1801602 1802395 := bstep (se 1 (by rfl) ⟨1351796, by rfl⟩ : syracuseStep 1802395 = 2703593) B2703593
theorem B9126107 : Blo 1801602 9126107 := bstep (se 1 (by rfl) ⟨6844580, by rfl⟩ : syracuseStep 9126107 = 13689161) B13689161
theorem B1802479 : Blo 1801602 1802479 := bstep (se 1 (by rfl) ⟨1351859, by rfl⟩ : syracuseStep 1802479 = 2703719) B2703719
theorem B1802559 : Blo 1801602 1802559 := bstep (se 1 (by rfl) ⟨1351919, by rfl⟩ : syracuseStep 1802559 = 2703839) B2703839
theorem B1802727 : Blo 1801602 1802727 := bstep (se 1 (by rfl) ⟨1352045, by rfl⟩ : syracuseStep 1802727 = 2704091) B2704091
theorem B2704103 : Blo 1801602 2704103 := bstep (se 1 (by rfl) ⟨2028077, by rfl⟩ : syracuseStep 2704103 = 4056155) B4056155
theorem B13681385 : Blo 1801602 13681385 := bstep (se 2 (by rfl) ⟨5130519, by rfl⟩ : syracuseStep 13681385 = 10261039) B10261039
theorem B1803003 : Blo 1801602 1803003 := bstep (se 1 (by rfl) ⟨1352252, by rfl⟩ : syracuseStep 1803003 = 2704505) B2704505
theorem B1803135 : Blo 1801602 1803135 := bstep (se 1 (by rfl) ⟨1352351, by rfl⟩ : syracuseStep 1803135 = 2704703) B2704703
theorem B2704367 : Blo 1801602 2704367 := bstep (se 1 (by rfl) ⟨2028275, by rfl⟩ : syracuseStep 2704367 = 4056551) B4056551
theorem B842753069 : Blo 1801602 842753069 := bstep (se 3 (by rfl) ⟨158016200, by rfl⟩ : syracuseStep 842753069 = 316032401) B316032401
theorem B4056119 : Blo 1801602 4056119 := bstep (se 1 (by rfl) ⟨3042089, by rfl⟩ : syracuseStep 4056119 = 6084179) B6084179
theorem B2704487 : Blo 1801602 2704487 := bstep (se 1 (by rfl) ⟨2028365, by rfl⟩ : syracuseStep 2704487 = 4056731) B4056731
theorem B13681871 : Blo 1801602 13681871 := bstep (se 1 (by rfl) ⟨10261403, by rfl⟩ : syracuseStep 13681871 = 20522807) B20522807
theorem B1803583 : Blo 1801602 1803583 := bstep (se 1 (by rfl) ⟨1352687, by rfl⟩ : syracuseStep 1803583 = 2705375) B2705375
theorem B20817323 : Blo 1801602 20817323 := bstep (se 1 (by rfl) ⟨15612992, by rfl⟩ : syracuseStep 20817323 = 31225985) B31225985
theorem B2705135 : Blo 1801602 2705135 := bstep (se 1 (by rfl) ⟨2028851, by rfl⟩ : syracuseStep 2705135 = 4057703) B4057703
theorem B3041023 : Blo 1801602 3041023 := bstep (se 1 (by rfl) ⟨2280767, by rfl⟩ : syracuseStep 3041023 = 4561535) B4561535
theorem B4564745 : Blo 1801602 4564745 := bstep (se 2 (by rfl) ⟨1711779, by rfl⟩ : syracuseStep 4564745 = 3423559) B3423559
theorem B31229707 : Blo 1801602 31229707 := bstep (se 1 (by rfl) ⟨23422280, by rfl⟩ : syracuseStep 31229707 = 46844561) B46844561
theorem B2705387 : Blo 1801602 2705387 := bstep (se 1 (by rfl) ⟨2029040, by rfl⟩ : syracuseStep 2705387 = 4058081) B4058081
theorem B4057127 : Blo 1801602 4057127 := bstep (se 1 (by rfl) ⟨3042845, by rfl⟩ : syracuseStep 4057127 = 6085691) B6085691
theorem B21923891 : Blo 1801602 21923891 := bstep (se 1 (by rfl) ⟨16442918, by rfl⟩ : syracuseStep 21923891 = 32885837) B32885837
theorem B3041455 : Blo 1801602 3041455 := bstep (se 1 (by rfl) ⟨2281091, by rfl⟩ : syracuseStep 3041455 = 4562183) B4562183
theorem B10422611 : Blo 1801602 10422611 := bstep (se 1 (by rfl) ⟨7816958, by rfl⟩ : syracuseStep 10422611 = 15633917) B15633917
theorem B3041705 : Blo 1801602 3041705 := bstep (se 2 (by rfl) ⟨1140639, by rfl⟩ : syracuseStep 3041705 = 2281279) B2281279
theorem B62425637 : Blo 1801602 62425637 := bstep (se 4 (by rfl) ⟨5852403, by rfl⟩ : syracuseStep 62425637 = 11704807) B11704807
theorem B3041887 : Blo 1801602 3041887 := bstep (se 1 (by rfl) ⟨2281415, by rfl⟩ : syracuseStep 3041887 = 4562831) B4562831
theorem B13691591 : Blo 1801602 13691591 := bstep (se 1 (by rfl) ⟨10268693, by rfl⟩ : syracuseStep 13691591 = 20537387) B20537387
theorem B43838347 : Blo 1801602 43838347 := bstep (se 1 (by rfl) ⟨32878760, by rfl⟩ : syracuseStep 43838347 = 65757521) B65757521
theorem B77933609 : Blo 1801602 77933609 := bstep (se 2 (by rfl) ⟨29225103, by rfl⟩ : syracuseStep 77933609 = 58450207) B58450207
theorem B6081641 : Blo 1801602 6081641 := bstep (se 2 (by rfl) ⟨2280615, by rfl⟩ : syracuseStep 6081641 = 4561231) B4561231
theorem B20524265 : Blo 1801602 20524265 := bstep (se 2 (by rfl) ⟨7696599, by rfl⟩ : syracuseStep 20524265 = 15393199) B15393199
theorem B25996733 : Blo 1801602 25996733 := bstep (se 3 (by rfl) ⟨4874387, by rfl⟩ : syracuseStep 25996733 = 9748775) B9748775
theorem B6499919 : Blo 1801602 6499919 := bstep (se 1 (by rfl) ⟨4874939, by rfl⟩ : syracuseStep 6499919 = 9749879) B9749879
theorem B11554589 : Blo 1801602 11554589 := bstep (se 3 (by rfl) ⟨2166485, by rfl⟩ : syracuseStep 11554589 = 4332971) B4332971
theorem B13684787 : Blo 1801602 13684787 := bstep (se 1 (by rfl) ⟨10263590, by rfl⟩ : syracuseStep 13684787 = 20527181) B20527181
theorem B7696721 : Blo 1801602 7696721 := bstep (se 2 (by rfl) ⟨2886270, by rfl⟩ : syracuseStep 7696721 = 5772541) B5772541
theorem B29250017 : Blo 1801602 29250017 := bstep (se 2 (by rfl) ⟨10968756, by rfl⟩ : syracuseStep 29250017 = 21937513) B21937513
theorem B2503147 : Blo 1801602 2503147 := bstep (se 1 (by rfl) ⟨1877360, by rfl⟩ : syracuseStep 2503147 = 3754721) B3754721
theorem B2888219 : Blo 1801602 2888219 := bstep (se 1 (by rfl) ⟨2166164, by rfl⟩ : syracuseStep 2888219 = 4332329) B4332329
theorem B7696943 : Blo 1801602 7696943 := bstep (se 1 (by rfl) ⟨5772707, by rfl⟩ : syracuseStep 7696943 = 11545415) B11545415
theorem B2028199 : Blo 1801602 2028199 := bstep (se 1 (by rfl) ⟨1521149, by rfl⟩ : syracuseStep 2028199 = 3042299) B3042299
theorem B55514443 : Blo 1801602 55514443 := bstep (se 1 (by rfl) ⟨41635832, by rfl⟩ : syracuseStep 55514443 = 83271665) B83271665
theorem B6165931 : Blo 1801602 6165931 := bstep (se 1 (by rfl) ⟨4624448, by rfl⟩ : syracuseStep 6165931 = 9248897) B9248897
theorem B5134063 : Blo 1801602 5134063 := bstep (se 1 (by rfl) ⟨3850547, by rfl⟩ : syracuseStep 5134063 = 7701095) B7701095
theorem B6846191 : Blo 1801602 6846191 := bstep (se 1 (by rfl) ⟨5134643, by rfl⟩ : syracuseStep 6846191 = 10269287) B10269287
theorem B11548439 : Blo 1801602 11548439 := bstep (se 1 (by rfl) ⟨8661329, by rfl⟩ : syracuseStep 11548439 = 17322659) B17322659
theorem B6936367 : Blo 1801602 6936367 := bstep (se 1 (by rfl) ⟨5202275, by rfl⟩ : syracuseStep 6936367 = 10404551) B10404551
theorem B62469947 : Blo 1801602 62469947 := bstep (se 1 (by rfl) ⟨46852460, by rfl⟩ : syracuseStep 62469947 = 93704921) B93704921
theorem B6084449 : Blo 1801602 6084449 := bstep (se 2 (by rfl) ⟨2281668, by rfl⟩ : syracuseStep 6084449 = 4563337) B4563337
theorem B3848095 : Blo 1801602 3848095 := bstep (se 1 (by rfl) ⟨2886071, by rfl⟩ : syracuseStep 3848095 = 5772143) B5772143
theorem B10262497 : Blo 1801602 10262497 := bstep (se 2 (by rfl) ⟨3848436, by rfl⟩ : syracuseStep 10262497 = 7696873) B7696873
theorem B6084719 : Blo 1801602 6084719 := bstep (se 1 (by rfl) ⟨4563539, by rfl⟩ : syracuseStep 6084719 = 9127079) B9127079
theorem B6846707 : Blo 1801602 6846707 := bstep (se 1 (by rfl) ⟨5135030, by rfl⟩ : syracuseStep 6846707 = 10270061) B10270061
theorem B9124163 : Blo 1801602 9124163 := bstep (se 1 (by rfl) ⟨6843122, by rfl⟩ : syracuseStep 9124163 = 13686245) B13686245
theorem B4168073 : Blo 1801602 4168073 := bstep (se 2 (by rfl) ⟨1563027, by rfl⟩ : syracuseStep 4168073 = 3126055) B3126055
theorem B6846889 : Blo 1801602 6846889 := bstep (se 2 (by rfl) ⟨2567583, by rfl⟩ : syracuseStep 6846889 = 5135167) B5135167
theorem B15407657 : Blo 1801602 15407657 := bstep (se 2 (by rfl) ⟨5777871, by rfl⟩ : syracuseStep 15407657 = 11555743) B11555743
theorem B10968155 : Blo 1801602 10968155 := bstep (se 1 (by rfl) ⟨8226116, by rfl⟩ : syracuseStep 10968155 = 16452233) B16452233
theorem B4054121 : Blo 1801602 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B6085907 : Blo 1801602 6085907 := bstep (se 1 (by rfl) ⟨4564430, by rfl⟩ : syracuseStep 6085907 = 9128861) B9128861
theorem B6086015 : Blo 1801602 6086015 := bstep (se 1 (by rfl) ⟨4564511, by rfl⟩ : syracuseStep 6086015 = 9129023) B9129023
theorem B1801695 : Blo 1801602 1801695 := bstep (se 1 (by rfl) ⟨1351271, by rfl⟩ : syracuseStep 1801695 = 2702543) B2702543
theorem B2702831 : Blo 1801602 2702831 := bstep (se 1 (by rfl) ⟨2027123, by rfl⟩ : syracuseStep 2702831 = 4054247) B4054247
theorem B1801755 : Blo 1801602 1801755 := bstep (se 1 (by rfl) ⟨1351316, by rfl⟩ : syracuseStep 1801755 = 2702633) B2702633
theorem B1801775 : Blo 1801602 1801775 := bstep (se 1 (by rfl) ⟨1351331, by rfl⟩ : syracuseStep 1801775 = 2702663) B2702663
theorem B2702969 : Blo 1801602 2702969 := bstep (se 2 (by rfl) ⟨1013613, by rfl⟩ : syracuseStep 2702969 = 2027227) B2027227
theorem B4054823 : Blo 1801602 4054823 := bstep (se 1 (by rfl) ⟨3041117, by rfl⟩ : syracuseStep 4054823 = 6082235) B6082235
theorem B30801707 : Blo 1801602 30801707 := bstep (se 1 (by rfl) ⟨23101280, by rfl⟩ : syracuseStep 30801707 = 46202561) B46202561
theorem B98664317 : Blo 1801602 98664317 := bstep (se 3 (by rfl) ⟨18499559, by rfl⟩ : syracuseStep 98664317 = 36999119) B36999119
theorem B12992399 : Blo 1801602 12992399 := bstep (se 1 (by rfl) ⟨9744299, by rfl⟩ : syracuseStep 12992399 = 19488599) B19488599
theorem B1802175 : Blo 1801602 1802175 := bstep (se 1 (by rfl) ⟨1351631, by rfl⟩ : syracuseStep 1802175 = 2703263) B2703263
theorem B1802235 : Blo 1801602 1802235 := bstep (se 1 (by rfl) ⟨1351676, by rfl⟩ : syracuseStep 1802235 = 2703353) B2703353
theorem B1802267 : Blo 1801602 1802267 := bstep (se 1 (by rfl) ⟨1351700, by rfl⟩ : syracuseStep 1802267 = 2703401) B2703401
theorem B2703431 : Blo 1801602 2703431 := bstep (se 1 (by rfl) ⟨2027573, by rfl⟩ : syracuseStep 2703431 = 4055147) B4055147
theorem B1802311 : Blo 1801602 1802311 := bstep (se 1 (by rfl) ⟨1351733, by rfl⟩ : syracuseStep 1802311 = 2703467) B2703467
theorem B4055273 : Blo 1801602 4055273 := bstep (se 2 (by rfl) ⟨1520727, by rfl⟩ : syracuseStep 4055273 = 3041455) B3041455
theorem B1925479 : Blo 1801602 1925479 := bstep (se 1 (by rfl) ⟨1444109, by rfl⟩ : syracuseStep 1925479 = 2888219) B2888219
theorem B1802735 : Blo 1801602 1802735 := bstep (se 1 (by rfl) ⟨1352051, by rfl⟩ : syracuseStep 1802735 = 2704103) B2704103
theorem B1802911 : Blo 1801602 1802911 := bstep (se 1 (by rfl) ⟨1352183, by rfl⟩ : syracuseStep 1802911 = 2704367) B2704367
theorem B2704079 : Blo 1801602 2704079 := bstep (se 1 (by rfl) ⟨2028059, by rfl⟩ : syracuseStep 2704079 = 4056119) B4056119
theorem B1802991 : Blo 1801602 1802991 := bstep (se 1 (by rfl) ⟨1352243, by rfl⟩ : syracuseStep 1802991 = 2704487) B2704487
theorem B4055849 : Blo 1801602 4055849 := bstep (se 2 (by rfl) ⟨1520943, by rfl⟩ : syracuseStep 4055849 = 3041887) B3041887
theorem B2704265 : Blo 1801602 2704265 := bstep (se 2 (by rfl) ⟨1014099, by rfl⟩ : syracuseStep 2704265 = 2028199) B2028199
theorem B13878215 : Blo 1801602 13878215 := bstep (se 1 (by rfl) ⟨10408661, by rfl⟩ : syracuseStep 13878215 = 20817323) B20817323
theorem B4564127 : Blo 1801602 4564127 := bstep (se 1 (by rfl) ⟨3423095, by rfl⟩ : syracuseStep 4564127 = 6846191) B6846191
theorem B1803423 : Blo 1801602 1803423 := bstep (se 1 (by rfl) ⟨1352567, by rfl⟩ : syracuseStep 1803423 = 2705135) B2705135
theorem B58451129 : Blo 1801602 58451129 := bstep (se 2 (by rfl) ⟨21919173, by rfl⟩ : syracuseStep 58451129 = 43838347) B43838347
theorem B4056299 : Blo 1801602 4056299 := bstep (se 1 (by rfl) ⟨3042224, by rfl⟩ : syracuseStep 4056299 = 6084449) B6084449
theorem B1803591 : Blo 1801602 1803591 := bstep (se 1 (by rfl) ⟨1352693, by rfl⟩ : syracuseStep 1803591 = 2705387) B2705387
theorem B2704751 : Blo 1801602 2704751 := bstep (se 1 (by rfl) ⟨2028563, by rfl⟩ : syracuseStep 2704751 = 4057127) B4057127
theorem B14615927 : Blo 1801602 14615927 := bstep (se 1 (by rfl) ⟨10961945, by rfl⟩ : syracuseStep 14615927 = 21923891) B21923891
theorem B4056479 : Blo 1801602 4056479 := bstep (se 1 (by rfl) ⟨3042359, by rfl⟩ : syracuseStep 4056479 = 6084719) B6084719
theorem B4564471 : Blo 1801602 4564471 := bstep (se 1 (by rfl) ⟨3423353, by rfl⟩ : syracuseStep 4564471 = 6846707) B6846707
theorem B6948407 : Blo 1801602 6948407 := bstep (se 1 (by rfl) ⟨5211305, by rfl⟩ : syracuseStep 6948407 = 10422611) B10422611
theorem B2778715 : Blo 1801602 2778715 := bstep (se 1 (by rfl) ⟨2084036, by rfl⟩ : syracuseStep 2778715 = 4168073) B4168073
theorem B41617091 : Blo 1801602 41617091 := bstep (se 1 (by rfl) ⟨31212818, by rfl⟩ : syracuseStep 41617091 = 62425637) B62425637
theorem B9127727 : Blo 1801602 9127727 := bstep (se 1 (by rfl) ⟨6845795, by rfl⟩ : syracuseStep 9127727 = 13691591) B13691591
theorem B51955739 : Blo 1801602 51955739 := bstep (se 1 (by rfl) ⟨38966804, by rfl⟩ : syracuseStep 51955739 = 77933609) B77933609
theorem B13682843 : Blo 1801602 13682843 := bstep (se 1 (by rfl) ⟨10262132, by rfl⟩ : syracuseStep 13682843 = 20524265) B20524265
theorem B4057271 : Blo 1801602 4057271 := bstep (se 1 (by rfl) ⟨3042953, by rfl⟩ : syracuseStep 4057271 = 6085907) B6085907
theorem B4057343 : Blo 1801602 4057343 := bstep (se 1 (by rfl) ⟨3043007, by rfl⟩ : syracuseStep 4057343 = 6086015) B6086015
theorem B7703059 : Blo 1801602 7703059 := bstep (se 1 (by rfl) ⟨5777294, by rfl⟩ : syracuseStep 7703059 = 11554589) B11554589
theorem B5130793 : Blo 1801602 5130793 := bstep (se 2 (by rfl) ⟨1924047, by rfl⟩ : syracuseStep 5130793 = 3848095) B3848095
theorem B65776211 : Blo 1801602 65776211 := bstep (se 1 (by rfl) ⟨49332158, by rfl⟩ : syracuseStep 65776211 = 98664317) B98664317
theorem B8661599 : Blo 1801602 8661599 := bstep (se 1 (by rfl) ⟨6496199, by rfl⟩ : syracuseStep 8661599 = 12992399) B12992399
theorem B13683329 : Blo 1801602 13683329 := bstep (se 2 (by rfl) ⟨5131248, by rfl⟩ : syracuseStep 13683329 = 10262497) B10262497
theorem B4333279 : Blo 1801602 4333279 := bstep (se 1 (by rfl) ⟨3249959, by rfl⟩ : syracuseStep 4333279 = 6499919) B6499919
theorem B5131147 : Blo 1801602 5131147 := bstep (se 1 (by rfl) ⟨3848360, by rfl⟩ : syracuseStep 5131147 = 7696721) B7696721
theorem B19500011 : Blo 1801602 19500011 := bstep (se 1 (by rfl) ⟨14625008, by rfl⟩ : syracuseStep 19500011 = 29250017) B29250017
theorem B5131295 : Blo 1801602 5131295 := bstep (se 1 (by rfl) ⟨3848471, by rfl⟩ : syracuseStep 5131295 = 7696943) B7696943
theorem B9120923 : Blo 1801602 9120923 := bstep (se 1 (by rfl) ⟨6840692, by rfl⟩ : syracuseStep 9120923 = 13681385) B13681385
theorem B9129185 : Blo 1801602 9129185 := bstep (se 2 (by rfl) ⟨3423444, by rfl⟩ : syracuseStep 9129185 = 6846889) B6846889
theorem B3337529 : Blo 1801602 3337529 := bstep (se 2 (by rfl) ⟨1251573, by rfl⟩ : syracuseStep 3337529 = 2503147) B2503147
theorem B561835379 : Blo 1801602 561835379 := bstep (se 1 (by rfl) ⟨421376534, by rfl⟩ : syracuseStep 561835379 = 842753069) B842753069
theorem B9121247 : Blo 1801602 9121247 := bstep (se 1 (by rfl) ⟨6840935, by rfl⟩ : syracuseStep 9121247 = 13681871) B13681871
theorem B3043163 : Blo 1801602 3043163 := bstep (se 1 (by rfl) ⟨2282372, by rfl⟩ : syracuseStep 3043163 = 4564745) B4564745
theorem B6082775 : Blo 1801602 6082775 := bstep (se 1 (by rfl) ⟨4562081, by rfl⟩ : syracuseStep 6082775 = 9124163) B9124163
theorem B2027803 : Blo 1801602 2027803 := bstep (se 1 (by rfl) ⟨1520852, by rfl⟩ : syracuseStep 2027803 = 3041705) B3041705
theorem B74019257 : Blo 1801602 74019257 := bstep (se 2 (by rfl) ⟨27757221, by rfl⟩ : syracuseStep 74019257 = 55514443) B55514443
theorem B8221241 : Blo 1801602 8221241 := bstep (se 2 (by rfl) ⟨3082965, by rfl⟩ : syracuseStep 8221241 = 6165931) B6165931
theorem B7312103 : Blo 1801602 7312103 := bstep (se 1 (by rfl) ⟨5484077, by rfl⟩ : syracuseStep 7312103 = 10968155) B10968155
theorem B17331155 : Blo 1801602 17331155 := bstep (se 1 (by rfl) ⟨12998366, by rfl⟩ : syracuseStep 17331155 = 25996733) B25996733
theorem B6845417 : Blo 1801602 6845417 := bstep (se 2 (by rfl) ⟨2567031, by rfl⟩ : syracuseStep 6845417 = 5134063) B5134063
theorem B20534471 : Blo 1801602 20534471 := bstep (se 1 (by rfl) ⟨15400853, by rfl⟩ : syracuseStep 20534471 = 30801707) B30801707
theorem B9123191 : Blo 1801602 9123191 := bstep (se 1 (by rfl) ⟨6842393, by rfl⟩ : syracuseStep 9123191 = 13684787) B13684787
theorem B6084071 : Blo 1801602 6084071 := bstep (se 1 (by rfl) ⟨4563053, by rfl⟩ : syracuseStep 6084071 = 9126107) B9126107
theorem B7698959 : Blo 1801602 7698959 := bstep (se 1 (by rfl) ⟨5774219, by rfl⟩ : syracuseStep 7698959 = 11548439) B11548439
theorem B41646631 : Blo 1801602 41646631 := bstep (se 1 (by rfl) ⟨31234973, by rfl⟩ : syracuseStep 41646631 = 62469947) B62469947
theorem B10271771 : Blo 1801602 10271771 := bstep (se 1 (by rfl) ⟨7703828, by rfl⟩ : syracuseStep 10271771 = 15407657) B15407657
theorem B2702747 : Blo 1801602 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B4054427 : Blo 1801602 4054427 := bstep (se 1 (by rfl) ⟨3040820, by rfl⟩ : syracuseStep 4054427 = 6081641) B6081641
theorem B1801887 : Blo 1801602 1801887 := bstep (se 1 (by rfl) ⟨1351415, by rfl⟩ : syracuseStep 1801887 = 2702831) B2702831
theorem B4054697 : Blo 1801602 4054697 := bstep (se 2 (by rfl) ⟨1520511, by rfl⟩ : syracuseStep 4054697 = 3041023) B3041023
theorem B41639609 : Blo 1801602 41639609 := bstep (se 2 (by rfl) ⟨15614853, by rfl⟩ : syracuseStep 41639609 = 31229707) B31229707
theorem B9248489 : Blo 1801602 9248489 := bstep (se 2 (by rfl) ⟨3468183, by rfl⟩ : syracuseStep 9248489 = 6936367) B6936367
theorem B1801979 : Blo 1801602 1801979 := bstep (se 1 (by rfl) ⟨1351484, by rfl⟩ : syracuseStep 1801979 = 2702969) B2702969
theorem B2703215 : Blo 1801602 2703215 := bstep (se 1 (by rfl) ⟨2027411, by rfl⟩ : syracuseStep 2703215 = 4054823) B4054823
theorem B1802287 : Blo 1801602 1802287 := bstep (se 1 (by rfl) ⟨1351715, by rfl⟩ : syracuseStep 1802287 = 2703431) B2703431
theorem B4055183 : Blo 1801602 4055183 := bstep (se 1 (by rfl) ⟨3041387, by rfl⟩ : syracuseStep 4055183 = 6082775) B6082775
theorem B2703515 : Blo 1801602 2703515 := bstep (se 1 (by rfl) ⟨2027636, by rfl⟩ : syracuseStep 2703515 = 4055273) B4055273
theorem B2703737 : Blo 1801602 2703737 := bstep (se 2 (by rfl) ⟨1013901, by rfl⟩ : syracuseStep 2703737 = 2027803) B2027803
theorem B5480827 : Blo 1801602 5480827 := bstep (se 1 (by rfl) ⟨4110620, by rfl⟩ : syracuseStep 5480827 = 8221241) B8221241
theorem B1802719 : Blo 1801602 1802719 := bstep (se 1 (by rfl) ⟨1352039, by rfl⟩ : syracuseStep 1802719 = 2704079) B2704079
theorem B4874735 : Blo 1801602 4874735 := bstep (se 1 (by rfl) ⟨3656051, by rfl⟩ : syracuseStep 4874735 = 7312103) B7312103
theorem B2703899 : Blo 1801602 2703899 := bstep (se 1 (by rfl) ⟨2027924, by rfl⟩ : syracuseStep 2703899 = 4055849) B4055849
theorem B1802843 : Blo 1801602 1802843 := bstep (se 1 (by rfl) ⟨1352132, by rfl⟩ : syracuseStep 1802843 = 2704265) B2704265
theorem B4563611 : Blo 1801602 4563611 := bstep (se 1 (by rfl) ⟨3422708, by rfl⟩ : syracuseStep 4563611 = 6845417) B6845417
theorem B6841057 : Blo 1801602 6841057 := bstep (se 2 (by rfl) ⟨2565396, by rfl⟩ : syracuseStep 6841057 = 5130793) B5130793
theorem B13689647 : Blo 1801602 13689647 := bstep (se 1 (by rfl) ⟨10267235, by rfl⟩ : syracuseStep 13689647 = 20534471) B20534471
theorem B2704199 : Blo 1801602 2704199 := bstep (se 1 (by rfl) ⟨2028149, by rfl⟩ : syracuseStep 2704199 = 4056299) B4056299
theorem B1803167 : Blo 1801602 1803167 := bstep (se 1 (by rfl) ⟨1352375, by rfl⟩ : syracuseStep 1803167 = 2704751) B2704751
theorem B2704319 : Blo 1801602 2704319 := bstep (se 1 (by rfl) ⟨2028239, by rfl⟩ : syracuseStep 2704319 = 4056479) B4056479
theorem B1498227677 : Blo 1801602 1498227677 := bstep (se 3 (by rfl) ⟨280917689, by rfl⟩ : syracuseStep 1498227677 = 561835379) B561835379
theorem B4056047 : Blo 1801602 4056047 := bstep (se 1 (by rfl) ⟨3042035, by rfl⟩ : syracuseStep 4056047 = 6084071) B6084071
theorem B6841529 : Blo 1801602 6841529 := bstep (se 2 (by rfl) ⟨2565573, by rfl⟩ : syracuseStep 6841529 = 5131147) B5131147
theorem B34637159 : Blo 1801602 34637159 := bstep (se 1 (by rfl) ⟨25977869, by rfl⟩ : syracuseStep 34637159 = 51955739) B51955739
theorem B2704847 : Blo 1801602 2704847 := bstep (se 1 (by rfl) ⟨2028635, by rfl⟩ : syracuseStep 2704847 = 4057271) B4057271
theorem B2704895 : Blo 1801602 2704895 := bstep (se 1 (by rfl) ⟨2028671, by rfl⟩ : syracuseStep 2704895 = 4057343) B4057343
theorem B6080615 : Blo 1801602 6080615 := bstep (se 1 (by rfl) ⟨4560461, by rfl⟩ : syracuseStep 6080615 = 9120923) B9120923
theorem B3704953 : Blo 1801602 3704953 := bstep (se 2 (by rfl) ⟨1389357, by rfl⟩ : syracuseStep 3704953 = 2778715) B2778715
theorem B5777705 : Blo 1801602 5777705 := bstep (se 2 (by rfl) ⟨2166639, by rfl⟩ : syracuseStep 5777705 = 4333279) B4333279
theorem B6080831 : Blo 1801602 6080831 := bstep (se 1 (by rfl) ⟨4560623, by rfl⟩ : syracuseStep 6080831 = 9121247) B9121247
theorem B2567305 : Blo 1801602 2567305 := bstep (se 2 (by rfl) ⟨962739, by rfl⟩ : syracuseStep 2567305 = 1925479) B1925479
theorem B9252143 : Blo 1801602 9252143 := bstep (se 1 (by rfl) ⟨6939107, by rfl⟩ : syracuseStep 9252143 = 13878215) B13878215
theorem B11554103 : Blo 1801602 11554103 := bstep (se 1 (by rfl) ⟨8665577, by rfl⟩ : syracuseStep 11554103 = 17331155) B17331155
theorem B55528841 : Blo 1801602 55528841 := bstep (se 2 (by rfl) ⟨20823315, by rfl⟩ : syracuseStep 55528841 = 41646631) B41646631
theorem B3042751 : Blo 1801602 3042751 := bstep (se 1 (by rfl) ⟨2282063, by rfl⟩ : syracuseStep 3042751 = 4564127) B4564127
theorem B8900077 : Blo 1801602 8900077 := bstep (se 3 (by rfl) ⟨1668764, by rfl⟩ : syracuseStep 8900077 = 3337529) B3337529
theorem B6082127 : Blo 1801602 6082127 := bstep (se 1 (by rfl) ⟨4561595, by rfl⟩ : syracuseStep 6082127 = 9123191) B9123191
theorem B9743951 : Blo 1801602 9743951 := bstep (se 1 (by rfl) ⟨7307963, by rfl⟩ : syracuseStep 9743951 = 14615927) B14615927
theorem B4632271 : Blo 1801602 4632271 := bstep (se 1 (by rfl) ⟨3474203, by rfl⟩ : syracuseStep 4632271 = 6948407) B6948407
theorem B9121895 : Blo 1801602 9121895 := bstep (se 1 (by rfl) ⟨6841421, by rfl⟩ : syracuseStep 9121895 = 13682843) B13682843
theorem B5132639 : Blo 1801602 5132639 := bstep (se 1 (by rfl) ⟨3849479, by rfl⟩ : syracuseStep 5132639 = 7698959) B7698959
theorem B9122219 : Blo 1801602 9122219 := bstep (se 1 (by rfl) ⟨6841664, by rfl⟩ : syracuseStep 9122219 = 13683329) B13683329
theorem B111038957 : Blo 1801602 111038957 := bstep (se 3 (by rfl) ⟨20819804, by rfl⟩ : syracuseStep 111038957 = 41639609) B41639609
theorem B3420863 : Blo 1801602 3420863 := bstep (se 1 (by rfl) ⟨2565647, by rfl⟩ : syracuseStep 3420863 = 5131295) B5131295
theorem B6165659 : Blo 1801602 6165659 := bstep (se 1 (by rfl) ⟨4624244, by rfl⟩ : syracuseStep 6165659 = 9248489) B9248489
theorem B2028775 : Blo 1801602 2028775 := bstep (se 1 (by rfl) ⟨1521581, by rfl⟩ : syracuseStep 2028775 = 3043163) B3043163
theorem B49346171 : Blo 1801602 49346171 := bstep (se 1 (by rfl) ⟨37009628, by rfl⟩ : syracuseStep 49346171 = 74019257) B74019257
theorem B10270745 : Blo 1801602 10270745 := bstep (se 2 (by rfl) ⟨3851529, by rfl⟩ : syracuseStep 10270745 = 7703059) B7703059
theorem B38967419 : Blo 1801602 38967419 := bstep (se 1 (by rfl) ⟨29225564, by rfl⟩ : syracuseStep 38967419 = 58451129) B58451129
theorem B27744727 : Blo 1801602 27744727 := bstep (se 1 (by rfl) ⟨20808545, by rfl⟩ : syracuseStep 27744727 = 41617091) B41617091
theorem B6085151 : Blo 1801602 6085151 := bstep (se 1 (by rfl) ⟨4563863, by rfl⟩ : syracuseStep 6085151 = 9127727) B9127727
theorem B43850807 : Blo 1801602 43850807 := bstep (se 1 (by rfl) ⟨32888105, by rfl⟩ : syracuseStep 43850807 = 65776211) B65776211
theorem B5774399 : Blo 1801602 5774399 := bstep (se 1 (by rfl) ⟨4330799, by rfl⟩ : syracuseStep 5774399 = 8661599) B8661599
theorem B6085961 : Blo 1801602 6085961 := bstep (se 2 (by rfl) ⟨2282235, by rfl⟩ : syracuseStep 6085961 = 4564471) B4564471
theorem B13000007 : Blo 1801602 13000007 := bstep (se 1 (by rfl) ⟨9750005, by rfl⟩ : syracuseStep 13000007 = 19500011) B19500011
theorem B6847847 : Blo 1801602 6847847 := bstep (se 1 (by rfl) ⟨5135885, by rfl⟩ : syracuseStep 6847847 = 10271771) B10271771
theorem B6086123 : Blo 1801602 6086123 := bstep (se 1 (by rfl) ⟨4564592, by rfl⟩ : syracuseStep 6086123 = 9129185) B9129185
theorem B1801831 : Blo 1801602 1801831 := bstep (se 1 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 1801831 = 2702747) B2702747
theorem B2702951 : Blo 1801602 2702951 := bstep (se 1 (by rfl) ⟨2027213, by rfl⟩ : syracuseStep 2702951 = 4054427) B4054427
theorem B2703131 : Blo 1801602 2703131 := bstep (se 1 (by rfl) ⟨2027348, by rfl⟩ : syracuseStep 2703131 = 4054697) B4054697
theorem B1802143 : Blo 1801602 1802143 := bstep (se 1 (by rfl) ⟨1351607, by rfl⟩ : syracuseStep 1802143 = 2703215) B2703215
theorem B2703455 : Blo 1801602 2703455 := bstep (se 1 (by rfl) ⟨2027591, by rfl⟩ : syracuseStep 2703455 = 4055183) B4055183
theorem B1802343 : Blo 1801602 1802343 := bstep (se 1 (by rfl) ⟨1351757, by rfl⟩ : syracuseStep 1802343 = 2703515) B2703515
theorem B4939937 : Blo 1801602 4939937 := bstep (se 2 (by rfl) ⟨1852476, by rfl⟩ : syracuseStep 4939937 = 3704953) B3704953
theorem B1802491 : Blo 1801602 1802491 := bstep (se 1 (by rfl) ⟨1351868, by rfl⟩ : syracuseStep 1802491 = 2703737) B2703737
theorem B1802599 : Blo 1801602 1802599 := bstep (se 1 (by rfl) ⟨1351949, by rfl⟩ : syracuseStep 1802599 = 2703899) B2703899
theorem B9126431 : Blo 1801602 9126431 := bstep (se 1 (by rfl) ⟨6844823, by rfl⟩ : syracuseStep 9126431 = 13689647) B13689647
theorem B1802799 : Blo 1801602 1802799 := bstep (se 1 (by rfl) ⟨1352099, by rfl⟩ : syracuseStep 1802799 = 2704199) B2704199
theorem B1802879 : Blo 1801602 1802879 := bstep (se 1 (by rfl) ⟨1352159, by rfl⟩ : syracuseStep 1802879 = 2704319) B2704319
theorem B998818451 : Blo 1801602 998818451 := bstep (se 1 (by rfl) ⟨749113838, by rfl⟩ : syracuseStep 998818451 = 1498227677) B1498227677
theorem B2704031 : Blo 1801602 2704031 := bstep (se 1 (by rfl) ⟨2028023, by rfl⟩ : syracuseStep 2704031 = 4056047) B4056047
theorem B1803231 : Blo 1801602 1803231 := bstep (se 1 (by rfl) ⟨1352423, by rfl⟩ : syracuseStep 1803231 = 2704847) B2704847
theorem B1803263 : Blo 1801602 1803263 := bstep (se 1 (by rfl) ⟨1352447, by rfl⟩ : syracuseStep 1803263 = 2704895) B2704895
theorem B25978279 : Blo 1801602 25978279 := bstep (se 1 (by rfl) ⟨19483709, by rfl⟩ : syracuseStep 25978279 = 38967419) B38967419
theorem B3851803 : Blo 1801602 3851803 := bstep (se 1 (by rfl) ⟨2888852, by rfl⟩ : syracuseStep 3851803 = 5777705) B5777705
theorem B2705033 : Blo 1801602 2705033 := bstep (se 2 (by rfl) ⟨1014387, by rfl⟩ : syracuseStep 2705033 = 2028775) B2028775
theorem B98821781 : Blo 1801602 98821781 := bstep (se 6 (by rfl) ⟨2316135, by rfl⟩ : syracuseStep 98821781 = 4632271) B4632271
theorem B4056767 : Blo 1801602 4056767 := bstep (se 1 (by rfl) ⟨3042575, by rfl⟩ : syracuseStep 4056767 = 6085151) B6085151
theorem B4057001 : Blo 1801602 4057001 := bstep (se 2 (by rfl) ⟨1521375, by rfl⟩ : syracuseStep 4057001 = 3042751) B3042751
theorem B29231077 : Blo 1801602 29231077 := bstep (se 4 (by rfl) ⟨2740413, by rfl⟩ : syracuseStep 29231077 = 5480827) B5480827
theorem B7702735 : Blo 1801602 7702735 := bstep (se 1 (by rfl) ⟨5777051, by rfl⟩ : syracuseStep 7702735 = 11554103) B11554103
theorem B4057307 : Blo 1801602 4057307 := bstep (se 1 (by rfl) ⟨3042980, by rfl⟩ : syracuseStep 4057307 = 6085961) B6085961
theorem B4565231 : Blo 1801602 4565231 := bstep (se 1 (by rfl) ⟨3423923, by rfl⟩ : syracuseStep 4565231 = 6847847) B6847847
theorem B4057415 : Blo 1801602 4057415 := bstep (se 1 (by rfl) ⟨3043061, by rfl⟩ : syracuseStep 4057415 = 6086123) B6086123
theorem B6081263 : Blo 1801602 6081263 := bstep (se 1 (by rfl) ⟨4560947, by rfl⟩ : syracuseStep 6081263 = 9121895) B9121895
theorem B6081479 : Blo 1801602 6081479 := bstep (se 1 (by rfl) ⟨4561109, by rfl⟩ : syracuseStep 6081479 = 9122219) B9122219
theorem B74025971 : Blo 1801602 74025971 := bstep (se 1 (by rfl) ⟨55519478, by rfl⟩ : syracuseStep 74025971 = 111038957) B111038957
theorem B3042407 : Blo 1801602 3042407 := bstep (se 1 (by rfl) ⟨2281805, by rfl⟩ : syracuseStep 3042407 = 4563611) B4563611
theorem B2280575 : Blo 1801602 2280575 := bstep (se 1 (by rfl) ⟨1710431, by rfl⟩ : syracuseStep 2280575 = 3420863) B3420863
theorem B9121409 : Blo 1801602 9121409 := bstep (se 2 (by rfl) ⟨3420528, by rfl⟩ : syracuseStep 9121409 = 6841057) B6841057
theorem B11866769 : Blo 1801602 11866769 := bstep (se 2 (by rfl) ⟨4450038, by rfl⟩ : syracuseStep 11866769 = 8900077) B8900077
theorem B29233871 : Blo 1801602 29233871 := bstep (se 1 (by rfl) ⟨21925403, by rfl⟩ : syracuseStep 29233871 = 43850807) B43850807
theorem B3421759 : Blo 1801602 3421759 := bstep (se 1 (by rfl) ⟨2566319, by rfl⟩ : syracuseStep 3421759 = 5132639) B5132639
theorem B3249823 : Blo 1801602 3249823 := bstep (se 1 (by rfl) ⟨2437367, by rfl⟩ : syracuseStep 3249823 = 4874735) B4874735
theorem B36992969 : Blo 1801602 36992969 := bstep (se 2 (by rfl) ⟨13872363, by rfl⟩ : syracuseStep 36992969 = 27744727) B27744727
theorem B4110439 : Blo 1801602 4110439 := bstep (se 1 (by rfl) ⟨3082829, by rfl⟩ : syracuseStep 4110439 = 6165659) B6165659
theorem B4561019 : Blo 1801602 4561019 := bstep (se 1 (by rfl) ⟨3420764, by rfl⟩ : syracuseStep 4561019 = 6841529) B6841529
theorem B23091439 : Blo 1801602 23091439 := bstep (se 1 (by rfl) ⟨17318579, by rfl⟩ : syracuseStep 23091439 = 34637159) B34637159
theorem B32897447 : Blo 1801602 32897447 := bstep (se 1 (by rfl) ⟨24673085, by rfl⟩ : syracuseStep 32897447 = 49346171) B49346171
theorem B6847163 : Blo 1801602 6847163 := bstep (se 1 (by rfl) ⟨5135372, by rfl⟩ : syracuseStep 6847163 = 10270745) B10270745
theorem B4053743 : Blo 1801602 4053743 := bstep (se 1 (by rfl) ⟨3040307, by rfl⟩ : syracuseStep 4053743 = 6080615) B6080615
theorem B3423073 : Blo 1801602 3423073 := bstep (se 2 (by rfl) ⟨1283652, by rfl⟩ : syracuseStep 3423073 = 2567305) B2567305
theorem B4053887 : Blo 1801602 4053887 := bstep (se 1 (by rfl) ⟨3040415, by rfl⟩ : syracuseStep 4053887 = 6080831) B6080831
theorem B3849599 : Blo 1801602 3849599 := bstep (se 1 (by rfl) ⟨2887199, by rfl⟩ : syracuseStep 3849599 = 5774399) B5774399
theorem B6168095 : Blo 1801602 6168095 := bstep (se 1 (by rfl) ⟨4626071, by rfl⟩ : syracuseStep 6168095 = 9252143) B9252143
theorem B8666671 : Blo 1801602 8666671 := bstep (se 1 (by rfl) ⟨6500003, by rfl⟩ : syracuseStep 8666671 = 13000007) B13000007
theorem B37019227 : Blo 1801602 37019227 := bstep (se 1 (by rfl) ⟨27764420, by rfl⟩ : syracuseStep 37019227 = 55528841) B55528841
theorem B6495967 : Blo 1801602 6495967 := bstep (se 1 (by rfl) ⟨4871975, by rfl⟩ : syracuseStep 6495967 = 9743951) B9743951
theorem B4054751 : Blo 1801602 4054751 := bstep (se 1 (by rfl) ⟨3041063, by rfl⟩ : syracuseStep 4054751 = 6082127) B6082127
theorem B1801967 : Blo 1801602 1801967 := bstep (se 1 (by rfl) ⟨1351475, by rfl⟩ : syracuseStep 1801967 = 2702951) B2702951
theorem B1802087 : Blo 1801602 1802087 := bstep (se 1 (by rfl) ⟨1351565, by rfl⟩ : syracuseStep 1802087 = 2703131) B2703131
theorem B1802303 : Blo 1801602 1802303 := bstep (se 1 (by rfl) ⟨1351727, by rfl⟩ : syracuseStep 1802303 = 2703455) B2703455
theorem B3293291 : Blo 1801602 3293291 := bstep (se 1 (by rfl) ⟨2469968, by rfl⟩ : syracuseStep 3293291 = 4939937) B4939937
theorem B5480585 : Blo 1801602 5480585 := bstep (se 2 (by rfl) ⟨2055219, by rfl⟩ : syracuseStep 5480585 = 4110439) B4110439
theorem B665878967 : Blo 1801602 665878967 := bstep (se 1 (by rfl) ⟨499409225, by rfl⟩ : syracuseStep 665878967 = 998818451) B998818451
theorem B1802687 : Blo 1801602 1802687 := bstep (se 1 (by rfl) ⟨1352015, by rfl⟩ : syracuseStep 1802687 = 2704031) B2704031
theorem B19489247 : Blo 1801602 19489247 := bstep (se 1 (by rfl) ⟨14616935, by rfl⟩ : syracuseStep 19489247 = 29233871) B29233871
theorem B1803355 : Blo 1801602 1803355 := bstep (se 1 (by rfl) ⟨1352516, by rfl⟩ : syracuseStep 1803355 = 2705033) B2705033
theorem B65881187 : Blo 1801602 65881187 := bstep (se 1 (by rfl) ⟨49410890, by rfl⟩ : syracuseStep 65881187 = 98821781) B98821781
theorem B2704511 : Blo 1801602 2704511 := bstep (se 1 (by rfl) ⟨2028383, by rfl⟩ : syracuseStep 2704511 = 4056767) B4056767
theorem B4564097 : Blo 1801602 4564097 := bstep (se 2 (by rfl) ⟨1711536, by rfl⟩ : syracuseStep 4564097 = 3423073) B3423073
theorem B34645157 : Blo 1801602 34645157 := bstep (se 4 (by rfl) ⟨3247983, by rfl⟩ : syracuseStep 34645157 = 6495967) B6495967
theorem B2704667 : Blo 1801602 2704667 := bstep (se 1 (by rfl) ⟨2028500, by rfl⟩ : syracuseStep 2704667 = 4057001) B4057001
theorem B3040679 : Blo 1801602 3040679 := bstep (se 1 (by rfl) ⟨2280509, by rfl⟩ : syracuseStep 3040679 = 4561019) B4561019
theorem B2704871 : Blo 1801602 2704871 := bstep (se 1 (by rfl) ⟨2028653, by rfl⟩ : syracuseStep 2704871 = 4057307) B4057307
theorem B2704943 : Blo 1801602 2704943 := bstep (se 1 (by rfl) ⟨2028707, by rfl⟩ : syracuseStep 2704943 = 4057415) B4057415
theorem B21931631 : Blo 1801602 21931631 := bstep (se 1 (by rfl) ⟨16448723, by rfl⟩ : syracuseStep 21931631 = 32897447) B32897447
theorem B4564775 : Blo 1801602 4564775 := bstep (se 1 (by rfl) ⟨3423581, by rfl⟩ : syracuseStep 4564775 = 6847163) B6847163
theorem B34637705 : Blo 1801602 34637705 := bstep (se 2 (by rfl) ⟨12989139, by rfl⟩ : syracuseStep 34637705 = 25978279) B25978279
theorem B49350647 : Blo 1801602 49350647 := bstep (se 1 (by rfl) ⟨37012985, by rfl⟩ : syracuseStep 49350647 = 74025971) B74025971
theorem B49358969 : Blo 1801602 49358969 := bstep (se 2 (by rfl) ⟨18509613, by rfl⟩ : syracuseStep 49358969 = 37019227) B37019227
theorem B2566399 : Blo 1801602 2566399 := bstep (se 1 (by rfl) ⟨1924799, by rfl⟩ : syracuseStep 2566399 = 3849599) B3849599
theorem B6080939 : Blo 1801602 6080939 := bstep (se 1 (by rfl) ⟨4560704, by rfl⟩ : syracuseStep 6080939 = 9121409) B9121409
theorem B30788585 : Blo 1801602 30788585 := bstep (se 2 (by rfl) ⟨11545719, by rfl⟩ : syracuseStep 30788585 = 23091439) B23091439
theorem B6081533 : Blo 1801602 6081533 := bstep (se 3 (by rfl) ⟨1140287, by rfl⟩ : syracuseStep 6081533 = 2280575) B2280575
theorem B24661979 : Blo 1801602 24661979 := bstep (se 1 (by rfl) ⟨18496484, by rfl⟩ : syracuseStep 24661979 = 36992969) B36992969
theorem B3043487 : Blo 1801602 3043487 := bstep (se 1 (by rfl) ⟨2282615, by rfl⟩ : syracuseStep 3043487 = 4565231) B4565231
theorem B11555561 : Blo 1801602 11555561 := bstep (se 2 (by rfl) ⟨4333335, by rfl⟩ : syracuseStep 11555561 = 8666671) B8666671
theorem B2028271 : Blo 1801602 2028271 := bstep (se 1 (by rfl) ⟨1521203, by rfl⟩ : syracuseStep 2028271 = 3042407) B3042407
theorem B38974769 : Blo 1801602 38974769 := bstep (se 2 (by rfl) ⟨14615538, by rfl⟩ : syracuseStep 38974769 = 29231077) B29231077
theorem B10270313 : Blo 1801602 10270313 := bstep (se 2 (by rfl) ⟨3851367, by rfl⟩ : syracuseStep 10270313 = 7702735) B7702735
theorem B6084287 : Blo 1801602 6084287 := bstep (se 1 (by rfl) ⟨4563215, by rfl⟩ : syracuseStep 6084287 = 9126431) B9126431
theorem B7911179 : Blo 1801602 7911179 := bstep (se 1 (by rfl) ⟨5933384, by rfl⟩ : syracuseStep 7911179 = 11866769) B11866769
theorem B2702495 : Blo 1801602 2702495 := bstep (se 1 (by rfl) ⟨2026871, by rfl⟩ : syracuseStep 2702495 = 4053743) B4053743
theorem B4054175 : Blo 1801602 4054175 := bstep (se 1 (by rfl) ⟨3040631, by rfl⟩ : syracuseStep 4054175 = 6081263) B6081263
theorem B2702591 : Blo 1801602 2702591 := bstep (se 1 (by rfl) ⟨2026943, by rfl⟩ : syracuseStep 2702591 = 4053887) B4053887
theorem B4054319 : Blo 1801602 4054319 := bstep (se 1 (by rfl) ⟨3040739, by rfl⟩ : syracuseStep 4054319 = 6081479) B6081479
theorem B5135737 : Blo 1801602 5135737 := bstep (se 2 (by rfl) ⟨1925901, by rfl⟩ : syracuseStep 5135737 = 3851803) B3851803
theorem B4562345 : Blo 1801602 4562345 := bstep (se 2 (by rfl) ⟨1710879, by rfl⟩ : syracuseStep 4562345 = 3421759) B3421759
theorem B4333097 : Blo 1801602 4333097 := bstep (se 2 (by rfl) ⟨1624911, by rfl⟩ : syracuseStep 4333097 = 3249823) B3249823
theorem B4112063 : Blo 1801602 4112063 := bstep (se 1 (by rfl) ⟨3084047, by rfl⟩ : syracuseStep 4112063 = 6168095) B6168095
theorem B2703167 : Blo 1801602 2703167 := bstep (se 1 (by rfl) ⟨2027375, by rfl⟩ : syracuseStep 2703167 = 4054751) B4054751
theorem B3653723 : Blo 1801602 3653723 := bstep (se 1 (by rfl) ⟨2740292, by rfl⟩ : syracuseStep 3653723 = 5480585) B5480585
theorem B8782109 : Blo 1801602 8782109 := bstep (se 3 (by rfl) ⟨1646645, by rfl⟩ : syracuseStep 8782109 = 3293291) B3293291
theorem B12992831 : Blo 1801602 12992831 := bstep (se 1 (by rfl) ⟨9744623, by rfl⟩ : syracuseStep 12992831 = 19489247) B19489247
theorem B1803007 : Blo 1801602 1803007 := bstep (se 1 (by rfl) ⟨1352255, by rfl⟩ : syracuseStep 1803007 = 2704511) B2704511
theorem B1803111 : Blo 1801602 1803111 := bstep (se 1 (by rfl) ⟨1352333, by rfl⟩ : syracuseStep 1803111 = 2704667) B2704667
theorem B2704361 : Blo 1801602 2704361 := bstep (se 2 (by rfl) ⟨1014135, by rfl⟩ : syracuseStep 2704361 = 2028271) B2028271
theorem B1803247 : Blo 1801602 1803247 := bstep (se 1 (by rfl) ⟨1352435, by rfl⟩ : syracuseStep 1803247 = 2704871) B2704871
theorem B1803295 : Blo 1801602 1803295 := bstep (se 1 (by rfl) ⟨1352471, by rfl⟩ : syracuseStep 1803295 = 2704943) B2704943
theorem B4056191 : Blo 1801602 4056191 := bstep (se 1 (by rfl) ⟨3042143, by rfl⟩ : syracuseStep 4056191 = 6084287) B6084287
theorem B32900431 : Blo 1801602 32900431 := bstep (se 1 (by rfl) ⟨24675323, by rfl⟩ : syracuseStep 32900431 = 49350647) B49350647
theorem B3041563 : Blo 1801602 3041563 := bstep (se 1 (by rfl) ⟨2281172, by rfl⟩ : syracuseStep 3041563 = 4562345) B4562345
theorem B443919311 : Blo 1801602 443919311 := bstep (se 1 (by rfl) ⟨332939483, by rfl⟩ : syracuseStep 443919311 = 665878967) B665878967
theorem B43920791 : Blo 1801602 43920791 := bstep (se 1 (by rfl) ⟨32940593, by rfl⟩ : syracuseStep 43920791 = 65881187) B65881187
theorem B3042731 : Blo 1801602 3042731 := bstep (se 1 (by rfl) ⟨2282048, by rfl⟩ : syracuseStep 3042731 = 4564097) B4564097
theorem B23096771 : Blo 1801602 23096771 := bstep (se 1 (by rfl) ⟨17322578, by rfl⟩ : syracuseStep 23096771 = 34645157) B34645157
theorem B2027119 : Blo 1801602 2027119 := bstep (se 1 (by rfl) ⟨1520339, by rfl⟩ : syracuseStep 2027119 = 3040679) B3040679
theorem B3043183 : Blo 1801602 3043183 := bstep (se 1 (by rfl) ⟨2282387, by rfl⟩ : syracuseStep 3043183 = 4564775) B4564775
theorem B30814829 : Blo 1801602 30814829 := bstep (se 3 (by rfl) ⟨5777780, by rfl⟩ : syracuseStep 30814829 = 11555561) B11555561
theorem B20525723 : Blo 1801602 20525723 := bstep (se 1 (by rfl) ⟨15394292, by rfl⟩ : syracuseStep 20525723 = 30788585) B30788585
theorem B2888731 : Blo 1801602 2888731 := bstep (se 1 (by rfl) ⟨2166548, by rfl⟩ : syracuseStep 2888731 = 4333097) B4333097
theorem B2741375 : Blo 1801602 2741375 := bstep (se 1 (by rfl) ⟨2056031, by rfl⟩ : syracuseStep 2741375 = 4112063) B4112063
theorem B2028991 : Blo 1801602 2028991 := bstep (se 1 (by rfl) ⟨1521743, by rfl⟩ : syracuseStep 2028991 = 3043487) B3043487
theorem B3421865 : Blo 1801602 3421865 := bstep (se 2 (by rfl) ⟨1283199, by rfl⟩ : syracuseStep 3421865 = 2566399) B2566399
theorem B25983179 : Blo 1801602 25983179 := bstep (se 1 (by rfl) ⟨19487384, by rfl⟩ : syracuseStep 25983179 = 38974769) B38974769
theorem B6846875 : Blo 1801602 6846875 := bstep (se 1 (by rfl) ⟨5135156, by rfl⟩ : syracuseStep 6846875 = 10270313) B10270313
theorem B14621087 : Blo 1801602 14621087 := bstep (se 1 (by rfl) ⟨10965815, by rfl⟩ : syracuseStep 14621087 = 21931631) B21931631
theorem B5274119 : Blo 1801602 5274119 := bstep (se 1 (by rfl) ⟨3955589, by rfl⟩ : syracuseStep 5274119 = 7911179) B7911179
theorem B23091803 : Blo 1801602 23091803 := bstep (se 1 (by rfl) ⟨17318852, by rfl⟩ : syracuseStep 23091803 = 34637705) B34637705
theorem B32905979 : Blo 1801602 32905979 := bstep (se 1 (by rfl) ⟨24679484, by rfl⟩ : syracuseStep 32905979 = 49358969) B49358969
theorem B4053959 : Blo 1801602 4053959 := bstep (se 1 (by rfl) ⟨3040469, by rfl⟩ : syracuseStep 4053959 = 6080939) B6080939
theorem B6847649 : Blo 1801602 6847649 := bstep (se 2 (by rfl) ⟨2567868, by rfl⟩ : syracuseStep 6847649 = 5135737) B5135737
theorem B4054355 : Blo 1801602 4054355 := bstep (se 1 (by rfl) ⟨3040766, by rfl⟩ : syracuseStep 4054355 = 6081533) B6081533
theorem B1801663 : Blo 1801602 1801663 := bstep (se 1 (by rfl) ⟨1351247, by rfl⟩ : syracuseStep 1801663 = 2702495) B2702495
theorem B2702783 : Blo 1801602 2702783 := bstep (se 1 (by rfl) ⟨2027087, by rfl⟩ : syracuseStep 2702783 = 4054175) B4054175
theorem B1801727 : Blo 1801602 1801727 := bstep (se 1 (by rfl) ⟨1351295, by rfl⟩ : syracuseStep 1801727 = 2702591) B2702591
theorem B2702879 : Blo 1801602 2702879 := bstep (se 1 (by rfl) ⟨2027159, by rfl⟩ : syracuseStep 2702879 = 4054319) B4054319
theorem B1802111 : Blo 1801602 1802111 := bstep (se 1 (by rfl) ⟨1351583, by rfl⟩ : syracuseStep 1802111 = 2703167) B2703167
theorem B16441319 : Blo 1801602 16441319 := bstep (se 1 (by rfl) ⟨12330989, by rfl⟩ : syracuseStep 16441319 = 24661979) B24661979
theorem B4055417 : Blo 1801602 4055417 := bstep (se 2 (by rfl) ⟨1520781, by rfl⟩ : syracuseStep 4055417 = 3041563) B3041563
theorem B1802907 : Blo 1801602 1802907 := bstep (se 1 (by rfl) ⟨1352180, by rfl⟩ : syracuseStep 1802907 = 2704361) B2704361
theorem B2704127 : Blo 1801602 2704127 := bstep (se 1 (by rfl) ⟨2028095, by rfl⟩ : syracuseStep 2704127 = 4056191) B4056191
theorem B3851641 : Blo 1801602 3851641 := bstep (se 2 (by rfl) ⟨1444365, by rfl⟩ : syracuseStep 3851641 = 2888731) B2888731
theorem B4564583 : Blo 1801602 4564583 := bstep (se 1 (by rfl) ⟨3423437, by rfl⟩ : syracuseStep 4564583 = 6846875) B6846875
theorem B15394535 : Blo 1801602 15394535 := bstep (se 1 (by rfl) ⟨11545901, by rfl⟩ : syracuseStep 15394535 = 23091803) B23091803
theorem B2705321 : Blo 1801602 2705321 := bstep (se 2 (by rfl) ⟨1014495, by rfl⟩ : syracuseStep 2705321 = 2028991) B2028991
theorem B295946207 : Blo 1801602 295946207 := bstep (se 1 (by rfl) ⟨221959655, by rfl⟩ : syracuseStep 295946207 = 443919311) B443919311
theorem B4565099 : Blo 1801602 4565099 := bstep (se 1 (by rfl) ⟨3423824, by rfl⟩ : syracuseStep 4565099 = 6847649) B6847649
theorem B29280527 : Blo 1801602 29280527 := bstep (se 1 (by rfl) ⟨21960395, by rfl⟩ : syracuseStep 29280527 = 43920791) B43920791
theorem B4057577 : Blo 1801602 4057577 := bstep (se 2 (by rfl) ⟨1521591, by rfl⟩ : syracuseStep 4057577 = 3043183) B3043183
theorem B2435815 : Blo 1801602 2435815 := bstep (se 1 (by rfl) ⟨1826861, by rfl⟩ : syracuseStep 2435815 = 3653723) B3653723
theorem B8661887 : Blo 1801602 8661887 := bstep (se 1 (by rfl) ⟨6496415, by rfl⟩ : syracuseStep 8661887 = 12992831) B12992831
theorem B7310333 : Blo 1801602 7310333 := bstep (se 3 (by rfl) ⟨1370687, by rfl⟩ : syracuseStep 7310333 = 2741375) B2741375
theorem B13683815 : Blo 1801602 13683815 := bstep (se 1 (by rfl) ⟨10262861, by rfl⟩ : syracuseStep 13683815 = 20525723) B20525723
theorem B17322119 : Blo 1801602 17322119 := bstep (se 1 (by rfl) ⟨12991589, by rfl⟩ : syracuseStep 17322119 = 25983179) B25983179
theorem B2028487 : Blo 1801602 2028487 := bstep (se 1 (by rfl) ⟨1521365, by rfl⟩ : syracuseStep 2028487 = 3042731) B3042731
theorem B15397847 : Blo 1801602 15397847 := bstep (se 1 (by rfl) ⟨11548385, by rfl⟩ : syracuseStep 15397847 = 23096771) B23096771
theorem B5854739 : Blo 1801602 5854739 := bstep (se 1 (by rfl) ⟨4391054, by rfl⟩ : syracuseStep 5854739 = 8782109) B8782109
theorem B20543219 : Blo 1801602 20543219 := bstep (se 1 (by rfl) ⟨15407414, by rfl⟩ : syracuseStep 20543219 = 30814829) B30814829
theorem B14064317 : Blo 1801602 14064317 := bstep (se 3 (by rfl) ⟨2637059, by rfl⟩ : syracuseStep 14064317 = 5274119) B5274119
theorem B9747391 : Blo 1801602 9747391 := bstep (se 1 (by rfl) ⟨7310543, by rfl⟩ : syracuseStep 9747391 = 14621087) B14621087
theorem B43867241 : Blo 1801602 43867241 := bstep (se 2 (by rfl) ⟨16450215, by rfl⟩ : syracuseStep 43867241 = 32900431) B32900431
theorem B9124973 : Blo 1801602 9124973 := bstep (se 3 (by rfl) ⟨1710932, by rfl⟩ : syracuseStep 9124973 = 3421865) B3421865
theorem B21937319 : Blo 1801602 21937319 := bstep (se 1 (by rfl) ⟨16452989, by rfl⟩ : syracuseStep 21937319 = 32905979) B32905979
theorem B2702639 : Blo 1801602 2702639 := bstep (se 1 (by rfl) ⟨2026979, by rfl⟩ : syracuseStep 2702639 = 4053959) B4053959
theorem B2702825 : Blo 1801602 2702825 := bstep (se 2 (by rfl) ⟨1013559, by rfl⟩ : syracuseStep 2702825 = 2027119) B2027119
theorem B2702903 : Blo 1801602 2702903 := bstep (se 1 (by rfl) ⟨2027177, by rfl⟩ : syracuseStep 2702903 = 4054355) B4054355
theorem B1801855 : Blo 1801602 1801855 := bstep (se 1 (by rfl) ⟨1351391, by rfl⟩ : syracuseStep 1801855 = 2702783) B2702783
theorem B1801919 : Blo 1801602 1801919 := bstep (se 1 (by rfl) ⟨1351439, by rfl⟩ : syracuseStep 1801919 = 2702879) B2702879
theorem B10960879 : Blo 1801602 10960879 := bstep (se 1 (by rfl) ⟨8220659, by rfl⟩ : syracuseStep 10960879 = 16441319) B16441319
theorem B2703611 : Blo 1801602 2703611 := bstep (se 1 (by rfl) ⟨2027708, by rfl⟩ : syracuseStep 2703611 = 4055417) B4055417
theorem B1802751 : Blo 1801602 1802751 := bstep (se 1 (by rfl) ⟨1352063, by rfl⟩ : syracuseStep 1802751 = 2704127) B2704127
theorem B10265231 : Blo 1801602 10265231 := bstep (se 1 (by rfl) ⟨7698923, by rfl⟩ : syracuseStep 10265231 = 15397847) B15397847
theorem B2704649 : Blo 1801602 2704649 := bstep (se 2 (by rfl) ⟨1014243, by rfl⟩ : syracuseStep 2704649 = 2028487) B2028487
theorem B1803547 : Blo 1801602 1803547 := bstep (se 1 (by rfl) ⟨1352660, by rfl⟩ : syracuseStep 1803547 = 2705321) B2705321
theorem B197297471 : Blo 1801602 197297471 := bstep (se 1 (by rfl) ⟨147973103, by rfl⟩ : syracuseStep 197297471 = 295946207) B295946207
theorem B2705051 : Blo 1801602 2705051 := bstep (se 1 (by rfl) ⟨2028788, by rfl⟩ : syracuseStep 2705051 = 4057577) B4057577
theorem B14624879 : Blo 1801602 14624879 := bstep (se 1 (by rfl) ⟨10968659, by rfl⟩ : syracuseStep 14624879 = 21937319) B21937319
theorem B3043055 : Blo 1801602 3043055 := bstep (se 1 (by rfl) ⟨2282291, by rfl⟩ : syracuseStep 3043055 = 4564583) B4564583
theorem B12996521 : Blo 1801602 12996521 := bstep (se 2 (by rfl) ⟨4873695, by rfl⟩ : syracuseStep 12996521 = 9747391) B9747391
theorem B3043399 : Blo 1801602 3043399 := bstep (se 1 (by rfl) ⟨2282549, by rfl⟩ : syracuseStep 3043399 = 4565099) B4565099
theorem B9376211 : Blo 1801602 9376211 := bstep (se 1 (by rfl) ⟨7032158, by rfl⟩ : syracuseStep 9376211 = 14064317) B14064317
theorem B9122543 : Blo 1801602 9122543 := bstep (se 1 (by rfl) ⟨6841907, by rfl⟩ : syracuseStep 9122543 = 13683815) B13683815
theorem B6083315 : Blo 1801602 6083315 := bstep (se 1 (by rfl) ⟨4562486, by rfl⟩ : syracuseStep 6083315 = 9124973) B9124973
theorem B11548079 : Blo 1801602 11548079 := bstep (se 1 (by rfl) ⟨8661059, by rfl⟩ : syracuseStep 11548079 = 17322119) B17322119
theorem B10263023 : Blo 1801602 10263023 := bstep (se 1 (by rfl) ⟨7697267, by rfl⟩ : syracuseStep 10263023 = 15394535) B15394535
theorem B13695479 : Blo 1801602 13695479 := bstep (se 1 (by rfl) ⟨10271609, by rfl⟩ : syracuseStep 13695479 = 20543219) B20543219
theorem B12991013 : Blo 1801602 12991013 := bstep (se 4 (by rfl) ⟨1217907, by rfl⟩ : syracuseStep 12991013 = 2435815) B2435815
theorem B15612637 : Blo 1801602 15612637 := bstep (se 3 (by rfl) ⟨2927369, by rfl⟩ : syracuseStep 15612637 = 5854739) B5854739
theorem B19520351 : Blo 1801602 19520351 := bstep (se 1 (by rfl) ⟨14640263, by rfl⟩ : syracuseStep 19520351 = 29280527) B29280527
theorem B5135521 : Blo 1801602 5135521 := bstep (se 2 (by rfl) ⟨1925820, by rfl⟩ : syracuseStep 5135521 = 3851641) B3851641
theorem B5774591 : Blo 1801602 5774591 := bstep (se 1 (by rfl) ⟨4330943, by rfl⟩ : syracuseStep 5774591 = 8661887) B8661887
theorem B4873555 : Blo 1801602 4873555 := bstep (se 1 (by rfl) ⟨3655166, by rfl⟩ : syracuseStep 4873555 = 7310333) B7310333
theorem B29244827 : Blo 1801602 29244827 := bstep (se 1 (by rfl) ⟨21933620, by rfl⟩ : syracuseStep 29244827 = 43867241) B43867241
theorem B1801759 : Blo 1801602 1801759 := bstep (se 1 (by rfl) ⟨1351319, by rfl⟩ : syracuseStep 1801759 = 2702639) B2702639
theorem B1801883 : Blo 1801602 1801883 := bstep (se 1 (by rfl) ⟨1351412, by rfl⟩ : syracuseStep 1801883 = 2702825) B2702825
theorem B1801935 : Blo 1801602 1801935 := bstep (se 1 (by rfl) ⟨1351451, by rfl⟩ : syracuseStep 1801935 = 2702903) B2702903
theorem B14614505 : Blo 1801602 14614505 := bstep (se 2 (by rfl) ⟨5480439, by rfl⟩ : syracuseStep 14614505 = 10960879) B10960879
theorem B1802407 : Blo 1801602 1802407 := bstep (se 1 (by rfl) ⟨1351805, by rfl⟩ : syracuseStep 1802407 = 2703611) B2703611
theorem B6250807 : Blo 1801602 6250807 := bstep (se 1 (by rfl) ⟨4688105, by rfl⟩ : syracuseStep 6250807 = 9376211) B9376211
theorem B4055543 : Blo 1801602 4055543 := bstep (se 1 (by rfl) ⟨3041657, by rfl⟩ : syracuseStep 4055543 = 6083315) B6083315
theorem B1803099 : Blo 1801602 1803099 := bstep (se 1 (by rfl) ⟨1352324, by rfl⟩ : syracuseStep 1803099 = 2704649) B2704649
theorem B20816849 : Blo 1801602 20816849 := bstep (se 2 (by rfl) ⟨7806318, by rfl⟩ : syracuseStep 20816849 = 15612637) B15612637
theorem B1803367 : Blo 1801602 1803367 := bstep (se 1 (by rfl) ⟨1352525, by rfl⟩ : syracuseStep 1803367 = 2705051) B2705051
theorem B6842015 : Blo 1801602 6842015 := bstep (se 1 (by rfl) ⟨5131511, by rfl⟩ : syracuseStep 6842015 = 10263023) B10263023
theorem B8660675 : Blo 1801602 8660675 := bstep (se 1 (by rfl) ⟨6495506, by rfl⟩ : syracuseStep 8660675 = 12991013) B12991013
theorem B6498073 : Blo 1801602 6498073 := bstep (se 2 (by rfl) ⟨2436777, by rfl⟩ : syracuseStep 6498073 = 4873555) B4873555
theorem B9743003 : Blo 1801602 9743003 := bstep (se 1 (by rfl) ⟨7307252, by rfl⟩ : syracuseStep 9743003 = 14614505) B14614505
theorem B4057865 : Blo 1801602 4057865 := bstep (se 2 (by rfl) ⟨1521699, by rfl⟩ : syracuseStep 4057865 = 3043399) B3043399
theorem B6843487 : Blo 1801602 6843487 := bstep (se 1 (by rfl) ⟨5132615, by rfl⟩ : syracuseStep 6843487 = 10265231) B10265231
theorem B6081695 : Blo 1801602 6081695 := bstep (se 1 (by rfl) ⟨4561271, by rfl⟩ : syracuseStep 6081695 = 9122543) B9122543
theorem B526126589 : Blo 1801602 526126589 := bstep (se 3 (by rfl) ⟨98648735, by rfl⟩ : syracuseStep 526126589 = 197297471) B197297471
theorem B9130319 : Blo 1801602 9130319 := bstep (se 1 (by rfl) ⟨6847739, by rfl⟩ : syracuseStep 9130319 = 13695479) B13695479
theorem B13013567 : Blo 1801602 13013567 := bstep (se 1 (by rfl) ⟨9760175, by rfl⟩ : syracuseStep 13013567 = 19520351) B19520351
theorem B2028703 : Blo 1801602 2028703 := bstep (se 1 (by rfl) ⟨1521527, by rfl⟩ : syracuseStep 2028703 = 3043055) B3043055
theorem B8664347 : Blo 1801602 8664347 := bstep (se 1 (by rfl) ⟨6498260, by rfl⟩ : syracuseStep 8664347 = 12996521) B12996521
theorem B38999677 : Blo 1801602 38999677 := bstep (se 3 (by rfl) ⟨7312439, by rfl⟩ : syracuseStep 38999677 = 14624879) B14624879
theorem B15398909 : Blo 1801602 15398909 := bstep (se 3 (by rfl) ⟨2887295, by rfl⟩ : syracuseStep 15398909 = 5774591) B5774591
theorem B7698719 : Blo 1801602 7698719 := bstep (se 1 (by rfl) ⟨5774039, by rfl⟩ : syracuseStep 7698719 = 11548079) B11548079
theorem B6847361 : Blo 1801602 6847361 := bstep (se 2 (by rfl) ⟨2567760, by rfl⟩ : syracuseStep 6847361 = 5135521) B5135521
theorem B19496551 : Blo 1801602 19496551 := bstep (se 1 (by rfl) ⟨14622413, by rfl⟩ : syracuseStep 19496551 = 29244827) B29244827
theorem B6086879 : Blo 1801602 6086879 := bstep (se 1 (by rfl) ⟨4565159, by rfl⟩ : syracuseStep 6086879 = 9130319) B9130319
theorem B2703695 : Blo 1801602 2703695 := bstep (se 1 (by rfl) ⟨2027771, by rfl⟩ : syracuseStep 2703695 = 4055543) B4055543
theorem B8675711 : Blo 1801602 8675711 := bstep (se 1 (by rfl) ⟨6506783, by rfl⟩ : syracuseStep 8675711 = 13013567) B13013567
theorem B13877899 : Blo 1801602 13877899 := bstep (se 1 (by rfl) ⟨10408424, by rfl⟩ : syracuseStep 13877899 = 20816849) B20816849
theorem B10265939 : Blo 1801602 10265939 := bstep (se 1 (by rfl) ⟨7699454, by rfl⟩ : syracuseStep 10265939 = 15398909) B15398909
theorem B2704937 : Blo 1801602 2704937 := bstep (se 2 (by rfl) ⟨1014351, by rfl⟩ : syracuseStep 2704937 = 2028703) B2028703
theorem B2705243 : Blo 1801602 2705243 := bstep (se 1 (by rfl) ⟨2028932, by rfl⟩ : syracuseStep 2705243 = 4057865) B4057865
theorem B4564907 : Blo 1801602 4564907 := bstep (se 1 (by rfl) ⟨3423680, by rfl⟩ : syracuseStep 4564907 = 6847361) B6847361
theorem B25995401 : Blo 1801602 25995401 := bstep (se 2 (by rfl) ⟨9748275, by rfl⟩ : syracuseStep 25995401 = 19496551) B19496551
theorem B350751059 : Blo 1801602 350751059 := bstep (se 1 (by rfl) ⟨263063294, by rfl⟩ : syracuseStep 350751059 = 526126589) B526126589
theorem B8334409 : Blo 1801602 8334409 := bstep (se 2 (by rfl) ⟨3125403, by rfl⟩ : syracuseStep 8334409 = 6250807) B6250807
theorem B23104925 : Blo 1801602 23104925 := bstep (se 3 (by rfl) ⟨4332173, by rfl⟩ : syracuseStep 23104925 = 8664347) B8664347
theorem B5132479 : Blo 1801602 5132479 := bstep (se 1 (by rfl) ⟨3849359, by rfl⟩ : syracuseStep 5132479 = 7698719) B7698719
theorem B51999569 : Blo 1801602 51999569 := bstep (se 2 (by rfl) ⟨19499838, by rfl⟩ : syracuseStep 51999569 = 38999677) B38999677
theorem B8664097 : Blo 1801602 8664097 := bstep (se 2 (by rfl) ⟨3249036, by rfl⟩ : syracuseStep 8664097 = 6498073) B6498073
theorem B4561343 : Blo 1801602 4561343 := bstep (se 1 (by rfl) ⟨3421007, by rfl⟩ : syracuseStep 4561343 = 6842015) B6842015
theorem B5773783 : Blo 1801602 5773783 := bstep (se 1 (by rfl) ⟨4330337, by rfl⟩ : syracuseStep 5773783 = 8660675) B8660675
theorem B9124649 : Blo 1801602 9124649 := bstep (se 2 (by rfl) ⟨3421743, by rfl⟩ : syracuseStep 9124649 = 6843487) B6843487
theorem B6495335 : Blo 1801602 6495335 := bstep (se 1 (by rfl) ⟨4871501, by rfl⟩ : syracuseStep 6495335 = 9743003) B9743003
theorem B4054463 : Blo 1801602 4054463 := bstep (se 1 (by rfl) ⟨3040847, by rfl⟩ : syracuseStep 4054463 = 6081695) B6081695
theorem B1802463 : Blo 1801602 1802463 := bstep (se 1 (by rfl) ⟨1351847, by rfl⟩ : syracuseStep 1802463 = 2703695) B2703695
theorem B5783807 : Blo 1801602 5783807 := bstep (se 1 (by rfl) ⟨4337855, by rfl⟩ : syracuseStep 5783807 = 8675711) B8675711
theorem B74015461 : Blo 1801602 74015461 := bstep (se 4 (by rfl) ⟨6938949, by rfl⟩ : syracuseStep 74015461 = 13877899) B13877899
theorem B1803291 : Blo 1801602 1803291 := bstep (se 1 (by rfl) ⟨1352468, by rfl⟩ : syracuseStep 1803291 = 2704937) B2704937
theorem B1803495 : Blo 1801602 1803495 := bstep (se 1 (by rfl) ⟨1352621, by rfl⟩ : syracuseStep 1803495 = 2705243) B2705243
theorem B11552129 : Blo 1801602 11552129 := bstep (se 2 (by rfl) ⟨4332048, by rfl⟩ : syracuseStep 11552129 = 8664097) B8664097
theorem B233834039 : Blo 1801602 233834039 := bstep (se 1 (by rfl) ⟨175375529, by rfl⟩ : syracuseStep 233834039 = 350751059) B350751059
theorem B3040895 : Blo 1801602 3040895 := bstep (se 1 (by rfl) ⟨2280671, by rfl⟩ : syracuseStep 3040895 = 4561343) B4561343
theorem B15403283 : Blo 1801602 15403283 := bstep (se 1 (by rfl) ⟨11552462, by rfl⟩ : syracuseStep 15403283 = 23104925) B23104925
theorem B4057919 : Blo 1801602 4057919 := bstep (se 1 (by rfl) ⟨3043439, by rfl⟩ : syracuseStep 4057919 = 6086879) B6086879
theorem B6843305 : Blo 1801602 6843305 := bstep (se 2 (by rfl) ⟨2566239, by rfl⟩ : syracuseStep 6843305 = 5132479) B5132479
theorem B6843959 : Blo 1801602 6843959 := bstep (se 1 (by rfl) ⟨5132969, by rfl⟩ : syracuseStep 6843959 = 10265939) B10265939
theorem B3043271 : Blo 1801602 3043271 := bstep (se 1 (by rfl) ⟨2282453, by rfl⟩ : syracuseStep 3043271 = 4564907) B4564907
theorem B17330267 : Blo 1801602 17330267 := bstep (se 1 (by rfl) ⟨12997700, by rfl⟩ : syracuseStep 17330267 = 25995401) B25995401
theorem B11112545 : Blo 1801602 11112545 := bstep (se 2 (by rfl) ⟨4167204, by rfl⟩ : syracuseStep 11112545 = 8334409) B8334409
theorem B6083099 : Blo 1801602 6083099 := bstep (se 1 (by rfl) ⟨4562324, by rfl⟩ : syracuseStep 6083099 = 9124649) B9124649
theorem B4330223 : Blo 1801602 4330223 := bstep (se 1 (by rfl) ⟨3247667, by rfl⟩ : syracuseStep 4330223 = 6495335) B6495335
theorem B34666379 : Blo 1801602 34666379 := bstep (se 1 (by rfl) ⟨25999784, by rfl⟩ : syracuseStep 34666379 = 51999569) B51999569
theorem B7698377 : Blo 1801602 7698377 := bstep (se 2 (by rfl) ⟨2886891, by rfl⟩ : syracuseStep 7698377 = 5773783) B5773783
theorem B2702975 : Blo 1801602 2702975 := bstep (se 1 (by rfl) ⟨2027231, by rfl⟩ : syracuseStep 2702975 = 4054463) B4054463
theorem B4055399 : Blo 1801602 4055399 := bstep (se 1 (by rfl) ⟨3041549, by rfl⟩ : syracuseStep 4055399 = 6083099) B6083099
theorem B7701419 : Blo 1801602 7701419 := bstep (se 1 (by rfl) ⟨5776064, by rfl⟩ : syracuseStep 7701419 = 11552129) B11552129
theorem B23110919 : Blo 1801602 23110919 := bstep (se 1 (by rfl) ⟨17333189, by rfl⟩ : syracuseStep 23110919 = 34666379) B34666379
theorem B2705279 : Blo 1801602 2705279 := bstep (se 1 (by rfl) ⟨2028959, by rfl⟩ : syracuseStep 2705279 = 4057919) B4057919
theorem B11553511 : Blo 1801602 11553511 := bstep (se 1 (by rfl) ⟨8665133, by rfl⟩ : syracuseStep 11553511 = 17330267) B17330267
theorem B7408363 : Blo 1801602 7408363 := bstep (se 1 (by rfl) ⟨5556272, by rfl⟩ : syracuseStep 7408363 = 11112545) B11112545
theorem B2886815 : Blo 1801602 2886815 := bstep (se 1 (by rfl) ⟨2165111, by rfl⟩ : syracuseStep 2886815 = 4330223) B4330223
theorem B155889359 : Blo 1801602 155889359 := bstep (se 1 (by rfl) ⟨116917019, by rfl⟩ : syracuseStep 155889359 = 233834039) B233834039
theorem B2027263 : Blo 1801602 2027263 := bstep (se 1 (by rfl) ⟨1520447, by rfl⟩ : syracuseStep 2027263 = 3040895) B3040895
theorem B5132251 : Blo 1801602 5132251 := bstep (se 1 (by rfl) ⟨3849188, by rfl⟩ : syracuseStep 5132251 = 7698377) B7698377
theorem B10268855 : Blo 1801602 10268855 := bstep (se 1 (by rfl) ⟨7701641, by rfl⟩ : syracuseStep 10268855 = 15403283) B15403283
theorem B2028847 : Blo 1801602 2028847 := bstep (se 1 (by rfl) ⟨1521635, by rfl⟩ : syracuseStep 2028847 = 3043271) B3043271
theorem B3855871 : Blo 1801602 3855871 := bstep (se 1 (by rfl) ⟨2891903, by rfl⟩ : syracuseStep 3855871 = 5783807) B5783807
theorem B98687281 : Blo 1801602 98687281 := bstep (se 2 (by rfl) ⟨37007730, by rfl⟩ : syracuseStep 98687281 = 74015461) B74015461
theorem B4562203 : Blo 1801602 4562203 := bstep (se 1 (by rfl) ⟨3421652, by rfl⟩ : syracuseStep 4562203 = 6843305) B6843305
theorem B4562639 : Blo 1801602 4562639 := bstep (se 1 (by rfl) ⟨3421979, by rfl⟩ : syracuseStep 4562639 = 6843959) B6843959
theorem B1801983 : Blo 1801602 1801983 := bstep (se 1 (by rfl) ⟨1351487, by rfl⟩ : syracuseStep 1801983 = 2702975) B2702975
theorem B2703599 : Blo 1801602 2703599 := bstep (se 1 (by rfl) ⟨2027699, by rfl⟩ : syracuseStep 2703599 = 4055399) B4055399
theorem B1803519 : Blo 1801602 1803519 := bstep (se 1 (by rfl) ⟨1352639, by rfl⟩ : syracuseStep 1803519 = 2705279) B2705279
theorem B2705129 : Blo 1801602 2705129 := bstep (se 2 (by rfl) ⟨1014423, by rfl⟩ : syracuseStep 2705129 = 2028847) B2028847
theorem B103926239 : Blo 1801602 103926239 := bstep (se 1 (by rfl) ⟨77944679, by rfl⟩ : syracuseStep 103926239 = 155889359) B155889359
theorem B3041759 : Blo 1801602 3041759 := bstep (se 1 (by rfl) ⟨2281319, by rfl⟩ : syracuseStep 3041759 = 4562639) B4562639
theorem B6843001 : Blo 1801602 6843001 := bstep (se 2 (by rfl) ⟨2566125, by rfl⟩ : syracuseStep 6843001 = 5132251) B5132251
theorem B131583041 : Blo 1801602 131583041 := bstep (se 2 (by rfl) ⟨49343640, by rfl⟩ : syracuseStep 131583041 = 98687281) B98687281
theorem B15404681 : Blo 1801602 15404681 := bstep (se 2 (by rfl) ⟨5776755, by rfl⟩ : syracuseStep 15404681 = 11553511) B11553511
theorem B6082937 : Blo 1801602 6082937 := bstep (se 2 (by rfl) ⟨2281101, by rfl⟩ : syracuseStep 6082937 = 4562203) B4562203
theorem B5141161 : Blo 1801602 5141161 := bstep (se 2 (by rfl) ⟨1927935, by rfl⟩ : syracuseStep 5141161 = 3855871) B3855871
theorem B6845903 : Blo 1801602 6845903 := bstep (se 1 (by rfl) ⟨5134427, by rfl⟩ : syracuseStep 6845903 = 10268855) B10268855
theorem B5134279 : Blo 1801602 5134279 := bstep (se 1 (by rfl) ⟨3850709, by rfl⟩ : syracuseStep 5134279 = 7701419) B7701419
theorem B15407279 : Blo 1801602 15407279 := bstep (se 1 (by rfl) ⟨11555459, by rfl⟩ : syracuseStep 15407279 = 23110919) B23110919
theorem B9877817 : Blo 1801602 9877817 := bstep (se 2 (by rfl) ⟨3704181, by rfl⟩ : syracuseStep 9877817 = 7408363) B7408363
theorem B1924543 : Blo 1801602 1924543 := bstep (se 1 (by rfl) ⟨1443407, by rfl⟩ : syracuseStep 1924543 = 2886815) B2886815
theorem B2703017 : Blo 1801602 2703017 := bstep (se 2 (by rfl) ⟨1013631, by rfl⟩ : syracuseStep 2703017 = 2027263) B2027263
theorem B1802399 : Blo 1801602 1802399 := bstep (se 1 (by rfl) ⟨1351799, by rfl⟩ : syracuseStep 1802399 = 2703599) B2703599
theorem B4055291 : Blo 1801602 4055291 := bstep (se 1 (by rfl) ⟨3041468, by rfl⟩ : syracuseStep 4055291 = 6082937) B6082937
theorem B4563935 : Blo 1801602 4563935 := bstep (se 1 (by rfl) ⟨3422951, by rfl⟩ : syracuseStep 4563935 = 6845903) B6845903
theorem B1803419 : Blo 1801602 1803419 := bstep (se 1 (by rfl) ⟨1352564, by rfl⟩ : syracuseStep 1803419 = 2705129) B2705129
theorem B87722027 : Blo 1801602 87722027 := bstep (se 1 (by rfl) ⟨65791520, by rfl⟩ : syracuseStep 87722027 = 131583041) B131583041
theorem B69284159 : Blo 1801602 69284159 := bstep (se 1 (by rfl) ⟨51963119, by rfl⟩ : syracuseStep 69284159 = 103926239) B103926239
theorem B2027839 : Blo 1801602 2027839 := bstep (se 1 (by rfl) ⟨1520879, by rfl⟩ : syracuseStep 2027839 = 3041759) B3041759
theorem B10269787 : Blo 1801602 10269787 := bstep (se 1 (by rfl) ⟨7702340, by rfl⟩ : syracuseStep 10269787 = 15404681) B15404681
theorem B6845705 : Blo 1801602 6845705 := bstep (se 2 (by rfl) ⟨2567139, by rfl⟩ : syracuseStep 6845705 = 5134279) B5134279
theorem B9124001 : Blo 1801602 9124001 := bstep (se 2 (by rfl) ⟨3421500, by rfl⟩ : syracuseStep 9124001 = 6843001) B6843001
theorem B6854881 : Blo 1801602 6854881 := bstep (se 2 (by rfl) ⟨2570580, by rfl⟩ : syracuseStep 6854881 = 5141161) B5141161
theorem B10271519 : Blo 1801602 10271519 := bstep (se 1 (by rfl) ⟨7703639, by rfl⟩ : syracuseStep 10271519 = 15407279) B15407279
theorem B6585211 : Blo 1801602 6585211 := bstep (se 1 (by rfl) ⟨4938908, by rfl⟩ : syracuseStep 6585211 = 9877817) B9877817
theorem B10264229 : Blo 1801602 10264229 := bstep (se 4 (by rfl) ⟨962271, by rfl⟩ : syracuseStep 10264229 = 1924543) B1924543
theorem B1802011 : Blo 1801602 1802011 := bstep (se 1 (by rfl) ⟨1351508, by rfl⟩ : syracuseStep 1802011 = 2703017) B2703017
theorem B2703527 : Blo 1801602 2703527 := bstep (se 1 (by rfl) ⟨2027645, by rfl⟩ : syracuseStep 2703527 = 4055291) B4055291
theorem B2703785 : Blo 1801602 2703785 := bstep (se 2 (by rfl) ⟨1013919, by rfl⟩ : syracuseStep 2703785 = 2027839) B2027839
theorem B4563803 : Blo 1801602 4563803 := bstep (se 1 (by rfl) ⟨3422852, by rfl⟩ : syracuseStep 4563803 = 6845705) B6845705
theorem B6842819 : Blo 1801602 6842819 := bstep (se 1 (by rfl) ⟨5132114, by rfl⟩ : syracuseStep 6842819 = 10264229) B10264229
theorem B46189439 : Blo 1801602 46189439 := bstep (se 1 (by rfl) ⟨34642079, by rfl⟩ : syracuseStep 46189439 = 69284159) B69284159
theorem B3042623 : Blo 1801602 3042623 := bstep (se 1 (by rfl) ⟨2281967, by rfl⟩ : syracuseStep 3042623 = 4563935) B4563935
theorem B6082667 : Blo 1801602 6082667 := bstep (se 1 (by rfl) ⟨4562000, by rfl⟩ : syracuseStep 6082667 = 9124001) B9124001
theorem B13693049 : Blo 1801602 13693049 := bstep (se 2 (by rfl) ⟨5134893, by rfl⟩ : syracuseStep 13693049 = 10269787) B10269787
theorem B9139841 : Blo 1801602 9139841 := bstep (se 2 (by rfl) ⟨3427440, by rfl⟩ : syracuseStep 9139841 = 6854881) B6854881
theorem B8780281 : Blo 1801602 8780281 := bstep (se 2 (by rfl) ⟨3292605, by rfl⟩ : syracuseStep 8780281 = 6585211) B6585211
theorem B58481351 : Blo 1801602 58481351 := bstep (se 1 (by rfl) ⟨43861013, by rfl⟩ : syracuseStep 58481351 = 87722027) B87722027
theorem B6847679 : Blo 1801602 6847679 := bstep (se 1 (by rfl) ⟨5135759, by rfl⟩ : syracuseStep 6847679 = 10271519) B10271519
theorem B4055111 : Blo 1801602 4055111 := bstep (se 1 (by rfl) ⟨3041333, by rfl⟩ : syracuseStep 4055111 = 6082667) B6082667
theorem B1802351 : Blo 1801602 1802351 := bstep (se 1 (by rfl) ⟨1351763, by rfl⟩ : syracuseStep 1802351 = 2703527) B2703527
theorem B1802523 : Blo 1801602 1802523 := bstep (se 1 (by rfl) ⟨1351892, by rfl⟩ : syracuseStep 1802523 = 2703785) B2703785
theorem B38987567 : Blo 1801602 38987567 := bstep (se 1 (by rfl) ⟨29240675, by rfl⟩ : syracuseStep 38987567 = 58481351) B58481351
theorem B4565119 : Blo 1801602 4565119 := bstep (se 1 (by rfl) ⟨3423839, by rfl⟩ : syracuseStep 4565119 = 6847679) B6847679
theorem B46828165 : Blo 1801602 46828165 := bstep (se 4 (by rfl) ⟨4390140, by rfl⟩ : syracuseStep 46828165 = 8780281) B8780281
theorem B9128699 : Blo 1801602 9128699 := bstep (se 1 (by rfl) ⟨6846524, by rfl⟩ : syracuseStep 9128699 = 13693049) B13693049
theorem B3042535 : Blo 1801602 3042535 := bstep (se 1 (by rfl) ⟨2281901, by rfl⟩ : syracuseStep 3042535 = 4563803) B4563803
theorem B2028415 : Blo 1801602 2028415 := bstep (se 1 (by rfl) ⟨1521311, by rfl⟩ : syracuseStep 2028415 = 3042623) B3042623
theorem B6093227 : Blo 1801602 6093227 := bstep (se 1 (by rfl) ⟨4569920, by rfl⟩ : syracuseStep 6093227 = 9139841) B9139841
theorem B4561879 : Blo 1801602 4561879 := bstep (se 1 (by rfl) ⟨3421409, by rfl⟩ : syracuseStep 4561879 = 6842819) B6842819
theorem B30792959 : Blo 1801602 30792959 := bstep (se 1 (by rfl) ⟨23094719, by rfl⟩ : syracuseStep 30792959 = 46189439) B46189439
theorem B2703407 : Blo 1801602 2703407 := bstep (se 1 (by rfl) ⟨2027555, by rfl⟩ : syracuseStep 2703407 = 4055111) B4055111
theorem B6086825 : Blo 1801602 6086825 := bstep (se 2 (by rfl) ⟨2282559, by rfl⟩ : syracuseStep 6086825 = 4565119) B4565119
theorem B2704553 : Blo 1801602 2704553 := bstep (se 2 (by rfl) ⟨1014207, by rfl⟩ : syracuseStep 2704553 = 2028415) B2028415
theorem B4056713 : Blo 1801602 4056713 := bstep (se 2 (by rfl) ⟨1521267, by rfl⟩ : syracuseStep 4056713 = 3042535) B3042535
theorem B16248605 : Blo 1801602 16248605 := bstep (se 3 (by rfl) ⟨3046613, by rfl⟩ : syracuseStep 16248605 = 6093227) B6093227
theorem B6082505 : Blo 1801602 6082505 := bstep (se 2 (by rfl) ⟨2280939, by rfl⟩ : syracuseStep 6082505 = 4561879) B4561879
theorem B62437553 : Blo 1801602 62437553 := bstep (se 2 (by rfl) ⟨23414082, by rfl⟩ : syracuseStep 62437553 = 46828165) B46828165
theorem B25991711 : Blo 1801602 25991711 := bstep (se 1 (by rfl) ⟨19493783, by rfl⟩ : syracuseStep 25991711 = 38987567) B38987567
theorem B6085799 : Blo 1801602 6085799 := bstep (se 1 (by rfl) ⟨4564349, by rfl⟩ : syracuseStep 6085799 = 9128699) B9128699
theorem B20528639 : Blo 1801602 20528639 := bstep (se 1 (by rfl) ⟨15396479, by rfl⟩ : syracuseStep 20528639 = 30792959) B30792959
theorem B1802271 : Blo 1801602 1802271 := bstep (se 1 (by rfl) ⟨1351703, by rfl⟩ : syracuseStep 1802271 = 2703407) B2703407
theorem B173318453 : Blo 1801602 173318453 := bstep (se 5 (by rfl) ⟨8124302, by rfl⟩ : syracuseStep 173318453 = 16248605) B16248605
theorem B1803035 : Blo 1801602 1803035 := bstep (se 1 (by rfl) ⟨1352276, by rfl⟩ : syracuseStep 1803035 = 2704553) B2704553
theorem B2704475 : Blo 1801602 2704475 := bstep (se 1 (by rfl) ⟨2028356, by rfl⟩ : syracuseStep 2704475 = 4056713) B4056713
theorem B41625035 : Blo 1801602 41625035 := bstep (se 1 (by rfl) ⟨31218776, by rfl⟩ : syracuseStep 41625035 = 62437553) B62437553
theorem B17327807 : Blo 1801602 17327807 := bstep (se 1 (by rfl) ⟨12995855, by rfl⟩ : syracuseStep 17327807 = 25991711) B25991711
theorem B4057199 : Blo 1801602 4057199 := bstep (se 1 (by rfl) ⟨3042899, by rfl⟩ : syracuseStep 4057199 = 6085799) B6085799
theorem B4057883 : Blo 1801602 4057883 := bstep (se 1 (by rfl) ⟨3043412, by rfl⟩ : syracuseStep 4057883 = 6086825) B6086825
theorem B13685759 : Blo 1801602 13685759 := bstep (se 1 (by rfl) ⟨10264319, by rfl⟩ : syracuseStep 13685759 = 20528639) B20528639
theorem B4055003 : Blo 1801602 4055003 := bstep (se 1 (by rfl) ⟨3041252, by rfl⟩ : syracuseStep 4055003 = 6082505) B6082505
theorem B1802983 : Blo 1801602 1802983 := bstep (se 1 (by rfl) ⟨1352237, by rfl⟩ : syracuseStep 1802983 = 2704475) B2704475
theorem B11551871 : Blo 1801602 11551871 := bstep (se 1 (by rfl) ⟨8663903, by rfl⟩ : syracuseStep 11551871 = 17327807) B17327807
theorem B2704799 : Blo 1801602 2704799 := bstep (se 1 (by rfl) ⟨2028599, by rfl⟩ : syracuseStep 2704799 = 4057199) B4057199
theorem B2705255 : Blo 1801602 2705255 := bstep (se 1 (by rfl) ⟨2028941, by rfl⟩ : syracuseStep 2705255 = 4057883) B4057883
theorem B27750023 : Blo 1801602 27750023 := bstep (se 1 (by rfl) ⟨20812517, by rfl⟩ : syracuseStep 27750023 = 41625035) B41625035
theorem B115545635 : Blo 1801602 115545635 := bstep (se 1 (by rfl) ⟨86659226, by rfl⟩ : syracuseStep 115545635 = 173318453) B173318453
theorem B9123839 : Blo 1801602 9123839 := bstep (se 1 (by rfl) ⟨6842879, by rfl⟩ : syracuseStep 9123839 = 13685759) B13685759
theorem B2703335 : Blo 1801602 2703335 := bstep (se 1 (by rfl) ⟨2027501, by rfl⟩ : syracuseStep 2703335 = 4055003) B4055003
theorem B7701247 : Blo 1801602 7701247 := bstep (se 1 (by rfl) ⟨5775935, by rfl⟩ : syracuseStep 7701247 = 11551871) B11551871
theorem B1803199 : Blo 1801602 1803199 := bstep (se 1 (by rfl) ⟨1352399, by rfl⟩ : syracuseStep 1803199 = 2704799) B2704799
theorem B77030423 : Blo 1801602 77030423 := bstep (se 1 (by rfl) ⟨57772817, by rfl⟩ : syracuseStep 77030423 = 115545635) B115545635
theorem B1803503 : Blo 1801602 1803503 := bstep (se 1 (by rfl) ⟨1352627, by rfl⟩ : syracuseStep 1803503 = 2705255) B2705255
theorem B18500015 : Blo 1801602 18500015 := bstep (se 1 (by rfl) ⟨13875011, by rfl⟩ : syracuseStep 18500015 = 27750023) B27750023
theorem B6082559 : Blo 1801602 6082559 := bstep (se 1 (by rfl) ⟨4561919, by rfl⟩ : syracuseStep 6082559 = 9123839) B9123839
theorem B1802223 : Blo 1801602 1802223 := bstep (se 1 (by rfl) ⟨1351667, by rfl⟩ : syracuseStep 1802223 = 2703335) B2703335
theorem B10268329 : Blo 1801602 10268329 := bstep (se 2 (by rfl) ⟨3850623, by rfl⟩ : syracuseStep 10268329 = 7701247) B7701247
theorem B4055039 : Blo 1801602 4055039 := bstep (se 1 (by rfl) ⟨3041279, by rfl⟩ : syracuseStep 4055039 = 6082559) B6082559
theorem B12333343 : Blo 1801602 12333343 := bstep (se 1 (by rfl) ⟨9250007, by rfl⟩ : syracuseStep 12333343 = 18500015) B18500015
theorem B51353615 : Blo 1801602 51353615 := bstep (se 1 (by rfl) ⟨38515211, by rfl⟩ : syracuseStep 51353615 = 77030423) B77030423
theorem B34235743 : Blo 1801602 34235743 := bstep (se 1 (by rfl) ⟨25676807, by rfl⟩ : syracuseStep 34235743 = 51353615) B51353615
theorem B13691105 : Blo 1801602 13691105 := bstep (se 2 (by rfl) ⟨5134164, by rfl⟩ : syracuseStep 13691105 = 10268329) B10268329
theorem B16444457 : Blo 1801602 16444457 := bstep (se 2 (by rfl) ⟨6166671, by rfl⟩ : syracuseStep 16444457 = 12333343) B12333343
theorem B2703359 : Blo 1801602 2703359 := bstep (se 1 (by rfl) ⟨2027519, by rfl⟩ : syracuseStep 2703359 = 4055039) B4055039
theorem B9127403 : Blo 1801602 9127403 := bstep (se 1 (by rfl) ⟨6845552, by rfl⟩ : syracuseStep 9127403 = 13691105) B13691105
theorem B45647657 : Blo 1801602 45647657 := bstep (se 2 (by rfl) ⟨17117871, by rfl⟩ : syracuseStep 45647657 = 34235743) B34235743
theorem B10962971 : Blo 1801602 10962971 := bstep (se 1 (by rfl) ⟨8222228, by rfl⟩ : syracuseStep 10962971 = 16444457) B16444457
theorem B1802239 : Blo 1801602 1802239 := bstep (se 1 (by rfl) ⟨1351679, by rfl⟩ : syracuseStep 1802239 = 2703359) B2703359
theorem B7308647 : Blo 1801602 7308647 := bstep (se 1 (by rfl) ⟨5481485, by rfl⟩ : syracuseStep 7308647 = 10962971) B10962971
theorem B6084935 : Blo 1801602 6084935 := bstep (se 1 (by rfl) ⟨4563701, by rfl⟩ : syracuseStep 6084935 = 9127403) B9127403
theorem B30431771 : Blo 1801602 30431771 := bstep (se 1 (by rfl) ⟨22823828, by rfl⟩ : syracuseStep 30431771 = 45647657) B45647657
theorem B4056623 : Blo 1801602 4056623 := bstep (se 1 (by rfl) ⟨3042467, by rfl⟩ : syracuseStep 4056623 = 6084935) B6084935
theorem B20287847 : Blo 1801602 20287847 := bstep (se 1 (by rfl) ⟨15215885, by rfl⟩ : syracuseStep 20287847 = 30431771) B30431771
theorem B4872431 : Blo 1801602 4872431 := bstep (se 1 (by rfl) ⟨3654323, by rfl⟩ : syracuseStep 4872431 = 7308647) B7308647
theorem B13525231 : Blo 1801602 13525231 := bstep (se 1 (by rfl) ⟨10143923, by rfl⟩ : syracuseStep 13525231 = 20287847) B20287847
theorem B12993149 : Blo 1801602 12993149 := bstep (se 3 (by rfl) ⟨2436215, by rfl⟩ : syracuseStep 12993149 = 4872431) B4872431
theorem B2704415 : Blo 1801602 2704415 := bstep (se 1 (by rfl) ⟨2028311, by rfl⟩ : syracuseStep 2704415 = 4056623) B4056623
theorem B1802943 : Blo 1801602 1802943 := bstep (se 1 (by rfl) ⟨1352207, by rfl⟩ : syracuseStep 1802943 = 2704415) B2704415
theorem B18033641 : Blo 1801602 18033641 := bstep (se 2 (by rfl) ⟨6762615, by rfl⟩ : syracuseStep 18033641 = 13525231) B13525231
theorem B8662099 : Blo 1801602 8662099 := bstep (se 1 (by rfl) ⟨6496574, by rfl⟩ : syracuseStep 8662099 = 12993149) B12993149
theorem B12022427 : Blo 1801602 12022427 := bstep (se 1 (by rfl) ⟨9016820, by rfl⟩ : syracuseStep 12022427 = 18033641) B18033641
theorem B11549465 : Blo 1801602 11549465 := bstep (se 2 (by rfl) ⟨4331049, by rfl⟩ : syracuseStep 11549465 = 8662099) B8662099
theorem B8014951 : Blo 1801602 8014951 := bstep (se 1 (by rfl) ⟨6011213, by rfl⟩ : syracuseStep 8014951 = 12022427) B12022427
theorem B7699643 : Blo 1801602 7699643 := bstep (se 1 (by rfl) ⟨5774732, by rfl⟩ : syracuseStep 7699643 = 11549465) B11549465
theorem B10686601 : Blo 1801602 10686601 := bstep (se 2 (by rfl) ⟨4007475, by rfl⟩ : syracuseStep 10686601 = 8014951) B8014951
theorem B5133095 : Blo 1801602 5133095 := bstep (se 1 (by rfl) ⟨3849821, by rfl⟩ : syracuseStep 5133095 = 7699643) B7699643
theorem B14248801 : Blo 1801602 14248801 := bstep (se 2 (by rfl) ⟨5343300, by rfl⟩ : syracuseStep 14248801 = 10686601) B10686601
theorem B3422063 : Blo 1801602 3422063 := bstep (se 1 (by rfl) ⟨2566547, by rfl⟩ : syracuseStep 3422063 = 5133095) B5133095
theorem B18998401 : Blo 1801602 18998401 := bstep (se 2 (by rfl) ⟨7124400, by rfl⟩ : syracuseStep 18998401 = 14248801) B14248801
theorem B2281375 : Blo 1801602 2281375 := bstep (se 1 (by rfl) ⟨1711031, by rfl⟩ : syracuseStep 2281375 = 3422063) B3422063
theorem B25331201 : Blo 1801602 25331201 := bstep (se 2 (by rfl) ⟨9499200, by rfl⟩ : syracuseStep 25331201 = 18998401) B18998401
theorem B3041833 : Blo 1801602 3041833 := bstep (se 2 (by rfl) ⟨1140687, by rfl⟩ : syracuseStep 3041833 = 2281375) B2281375
theorem B4055777 : Blo 1801602 4055777 := bstep (se 2 (by rfl) ⟨1520916, by rfl⟩ : syracuseStep 4055777 = 3041833) B3041833
theorem B16887467 : Blo 1801602 16887467 := bstep (se 1 (by rfl) ⟨12665600, by rfl⟩ : syracuseStep 16887467 = 25331201) B25331201
theorem B2703851 : Blo 1801602 2703851 := bstep (se 1 (by rfl) ⟨2027888, by rfl⟩ : syracuseStep 2703851 = 4055777) B4055777
theorem B11258311 : Blo 1801602 11258311 := bstep (se 1 (by rfl) ⟨8443733, by rfl⟩ : syracuseStep 11258311 = 16887467) B16887467
theorem B1802567 : Blo 1801602 1802567 := bstep (se 1 (by rfl) ⟨1351925, by rfl⟩ : syracuseStep 1802567 = 2703851) B2703851
theorem B15011081 : Blo 1801602 15011081 := bstep (se 2 (by rfl) ⟨5629155, by rfl⟩ : syracuseStep 15011081 = 11258311) B11258311
theorem B10007387 : Blo 1801602 10007387 := bstep (se 1 (by rfl) ⟨7505540, by rfl⟩ : syracuseStep 10007387 = 15011081) B15011081
theorem B6671591 : Blo 1801602 6671591 := bstep (se 1 (by rfl) ⟨5003693, by rfl⟩ : syracuseStep 6671591 = 10007387) B10007387
theorem B4447727 : Blo 1801602 4447727 := bstep (se 1 (by rfl) ⟨3335795, by rfl⟩ : syracuseStep 4447727 = 6671591) B6671591
theorem B2965151 : Blo 1801602 2965151 := bstep (se 1 (by rfl) ⟨2223863, by rfl⟩ : syracuseStep 2965151 = 4447727) B4447727
theorem B1976767 : Blo 1801602 1976767 := bstep (se 1 (by rfl) ⟨1482575, by rfl⟩ : syracuseStep 1976767 = 2965151) B2965151
theorem B10542757 : Blo 1801602 10542757 := bstep (se 4 (by rfl) ⟨988383, by rfl⟩ : syracuseStep 10542757 = 1976767) B1976767
theorem B14057009 : Blo 1801602 14057009 := bstep (se 2 (by rfl) ⟨5271378, by rfl⟩ : syracuseStep 14057009 = 10542757) B10542757
theorem B9371339 : Blo 1801602 9371339 := bstep (se 1 (by rfl) ⟨7028504, by rfl⟩ : syracuseStep 9371339 = 14057009) B14057009
theorem B6247559 : Blo 1801602 6247559 := bstep (se 1 (by rfl) ⟨4685669, by rfl⟩ : syracuseStep 6247559 = 9371339) B9371339
theorem B4165039 : Blo 1801602 4165039 := bstep (se 1 (by rfl) ⟨3123779, by rfl⟩ : syracuseStep 4165039 = 6247559) B6247559
theorem B22213541 : Blo 1801602 22213541 := bstep (se 4 (by rfl) ⟨2082519, by rfl⟩ : syracuseStep 22213541 = 4165039) B4165039
theorem B14809027 : Blo 1801602 14809027 := bstep (se 1 (by rfl) ⟨11106770, by rfl⟩ : syracuseStep 14809027 = 22213541) B22213541
theorem B19745369 : Blo 1801602 19745369 := bstep (se 2 (by rfl) ⟨7404513, by rfl⟩ : syracuseStep 19745369 = 14809027) B14809027
theorem B13163579 : Blo 1801602 13163579 := bstep (se 1 (by rfl) ⟨9872684, by rfl⟩ : syracuseStep 13163579 = 19745369) B19745369
theorem B8775719 : Blo 1801602 8775719 := bstep (se 1 (by rfl) ⟨6581789, by rfl⟩ : syracuseStep 8775719 = 13163579) B13163579
theorem B5850479 : Blo 1801602 5850479 := bstep (se 1 (by rfl) ⟨4387859, by rfl⟩ : syracuseStep 5850479 = 8775719) B8775719
theorem B15601277 : Blo 1801602 15601277 := bstep (se 3 (by rfl) ⟨2925239, by rfl⟩ : syracuseStep 15601277 = 5850479) B5850479
theorem B10400851 : Blo 1801602 10400851 := bstep (se 1 (by rfl) ⟨7800638, by rfl⟩ : syracuseStep 10400851 = 15601277) B15601277
theorem B55471205 : Blo 1801602 55471205 := bstep (se 4 (by rfl) ⟨5200425, by rfl⟩ : syracuseStep 55471205 = 10400851) B10400851
theorem B36980803 : Blo 1801602 36980803 := bstep (se 1 (by rfl) ⟨27735602, by rfl⟩ : syracuseStep 36980803 = 55471205) B55471205
theorem B49307737 : Blo 1801602 49307737 := bstep (se 2 (by rfl) ⟨18490401, by rfl⟩ : syracuseStep 49307737 = 36980803) B36980803
theorem B65743649 : Blo 1801602 65743649 := bstep (se 2 (by rfl) ⟨24653868, by rfl⟩ : syracuseStep 65743649 = 49307737) B49307737
theorem B43829099 : Blo 1801602 43829099 := bstep (se 1 (by rfl) ⟨32871824, by rfl⟩ : syracuseStep 43829099 = 65743649) B65743649
theorem B29219399 : Blo 1801602 29219399 := bstep (se 1 (by rfl) ⟨21914549, by rfl⟩ : syracuseStep 29219399 = 43829099) B43829099
theorem B19479599 : Blo 1801602 19479599 := bstep (se 1 (by rfl) ⟨14609699, by rfl⟩ : syracuseStep 19479599 = 29219399) B29219399
theorem B12986399 : Blo 1801602 12986399 := bstep (se 1 (by rfl) ⟨9739799, by rfl⟩ : syracuseStep 12986399 = 19479599) B19479599
theorem B8657599 : Blo 1801602 8657599 := bstep (se 1 (by rfl) ⟨6493199, by rfl⟩ : syracuseStep 8657599 = 12986399) B12986399
theorem B11543465 : Blo 1801602 11543465 := bstep (se 2 (by rfl) ⟨4328799, by rfl⟩ : syracuseStep 11543465 = 8657599) B8657599
theorem B7695643 : Blo 1801602 7695643 := bstep (se 1 (by rfl) ⟨5771732, by rfl⟩ : syracuseStep 7695643 = 11543465) B11543465
theorem B10260857 : Blo 1801602 10260857 := bstep (se 2 (by rfl) ⟨3847821, by rfl⟩ : syracuseStep 10260857 = 7695643) B7695643
theorem B6840571 : Blo 1801602 6840571 := bstep (se 1 (by rfl) ⟨5130428, by rfl⟩ : syracuseStep 6840571 = 10260857) B10260857
theorem B9120761 : Blo 1801602 9120761 := bstep (se 2 (by rfl) ⟨3420285, by rfl⟩ : syracuseStep 9120761 = 6840571) B6840571
theorem B6080507 : Blo 1801602 6080507 := bstep (se 1 (by rfl) ⟨4560380, by rfl⟩ : syracuseStep 6080507 = 9120761) B9120761
theorem B4053671 : Blo 1801602 4053671 := bstep (se 1 (by rfl) ⟨3040253, by rfl⟩ : syracuseStep 4053671 = 6080507) B6080507
theorem B2702447 : Blo 1801602 2702447 := bstep (se 1 (by rfl) ⟨2026835, by rfl⟩ : syracuseStep 2702447 = 4053671) B4053671
theorem B1801631 : Blo 1801602 1801631 := bstep (se 1 (by rfl) ⟨1351223, by rfl⟩ : syracuseStep 1801631 = 2702447) B2702447

theorem C0 (j : ℕ) (h1 : 450400 ≤ j) (h2 : j ≤ 450899) : Blo 1801602 (4 * j + 3) := by
  interval_cases j
  · exact B1801603
  · exact B1801607
  · exact B1801611
  · exact B1801615
  · exact B1801619
  · exact B1801623
  · exact B1801627
  · exact B1801631
  · exact B1801635
  · exact B1801639
  · exact B1801643
  · exact B1801647
  · exact B1801651
  · exact B1801655
  · exact B1801659
  · exact B1801663
  · exact B1801667
  · exact B1801671
  · exact B1801675
  · exact B1801679
  · exact B1801683
  · exact B1801687
  · exact B1801691
  · exact B1801695
  · exact B1801699
  · exact B1801703
  · exact B1801707
  · exact B1801711
  · exact B1801715
  · exact B1801719
  · exact B1801723
  · exact B1801727
  · exact B1801731
  · exact B1801735
  · exact B1801739
  · exact B1801743
  · exact B1801747
  · exact B1801751
  · exact B1801755
  · exact B1801759
  · exact B1801763
  · exact B1801767
  · exact B1801771
  · exact B1801775
  · exact B1801779
  · exact B1801783
  · exact B1801787
  · exact B1801791
  · exact B1801795
  · exact B1801799
  · exact B1801803
  · exact B1801807
  · exact B1801811
  · exact B1801815
  · exact B1801819
  · exact B1801823
  · exact B1801827
  · exact B1801831
  · exact B1801835
  · exact B1801839
  · exact B1801843
  · exact B1801847
  · exact B1801851
  · exact B1801855
  · exact B1801859
  · exact B1801863
  · exact B1801867
  · exact B1801871
  · exact B1801875
  · exact B1801879
  · exact B1801883
  · exact B1801887
  · exact B1801891
  · exact B1801895
  · exact B1801899
  · exact B1801903
  · exact B1801907
  · exact B1801911
  · exact B1801915
  · exact B1801919
  · exact B1801923
  · exact B1801927
  · exact B1801931
  · exact B1801935
  · exact B1801939
  · exact B1801943
  · exact B1801947
  · exact B1801951
  · exact B1801955
  · exact B1801959
  · exact B1801963
  · exact B1801967
  · exact B1801971
  · exact B1801975
  · exact B1801979
  · exact B1801983
  · exact B1801987
  · exact B1801991
  · exact B1801995
  · exact B1801999
  · exact B1802003
  · exact B1802007
  · exact B1802011
  · exact B1802015
  · exact B1802019
  · exact B1802023
  · exact B1802027
  · exact B1802031
  · exact B1802035
  · exact B1802039
  · exact B1802043
  · exact B1802047
  · exact B1802051
  · exact B1802055
  · exact B1802059
  · exact B1802063
  · exact B1802067
  · exact B1802071
  · exact B1802075
  · exact B1802079
  · exact B1802083
  · exact B1802087
  · exact B1802091
  · exact B1802095
  · exact B1802099
  · exact B1802103
  · exact B1802107
  · exact B1802111
  · exact B1802115
  · exact B1802119
  · exact B1802123
  · exact B1802127
  · exact B1802131
  · exact B1802135
  · exact B1802139
  · exact B1802143
  · exact B1802147
  · exact B1802151
  · exact B1802155
  · exact B1802159
  · exact B1802163
  · exact B1802167
  · exact B1802171
  · exact B1802175
  · exact B1802179
  · exact B1802183
  · exact B1802187
  · exact B1802191
  · exact B1802195
  · exact B1802199
  · exact B1802203
  · exact B1802207
  · exact B1802211
  · exact B1802215
  · exact B1802219
  · exact B1802223
  · exact B1802227
  · exact B1802231
  · exact B1802235
  · exact B1802239
  · exact B1802243
  · exact B1802247
  · exact B1802251
  · exact B1802255
  · exact B1802259
  · exact B1802263
  · exact B1802267
  · exact B1802271
  · exact B1802275
  · exact B1802279
  · exact B1802283
  · exact B1802287
  · exact B1802291
  · exact B1802295
  · exact B1802299
  · exact B1802303
  · exact B1802307
  · exact B1802311
  · exact B1802315
  · exact B1802319
  · exact B1802323
  · exact B1802327
  · exact B1802331
  · exact B1802335
  · exact B1802339
  · exact B1802343
  · exact B1802347
  · exact B1802351
  · exact B1802355
  · exact B1802359
  · exact B1802363
  · exact B1802367
  · exact B1802371
  · exact B1802375
  · exact B1802379
  · exact B1802383
  · exact B1802387
  · exact B1802391
  · exact B1802395
  · exact B1802399
  · exact B1802403
  · exact B1802407
  · exact B1802411
  · exact B1802415
  · exact B1802419
  · exact B1802423
  · exact B1802427
  · exact B1802431
  · exact B1802435
  · exact B1802439
  · exact B1802443
  · exact B1802447
  · exact B1802451
  · exact B1802455
  · exact B1802459
  · exact B1802463
  · exact B1802467
  · exact B1802471
  · exact B1802475
  · exact B1802479
  · exact B1802483
  · exact B1802487
  · exact B1802491
  · exact B1802495
  · exact B1802499
  · exact B1802503
  · exact B1802507
  · exact B1802511
  · exact B1802515
  · exact B1802519
  · exact B1802523
  · exact B1802527
  · exact B1802531
  · exact B1802535
  · exact B1802539
  · exact B1802543
  · exact B1802547
  · exact B1802551
  · exact B1802555
  · exact B1802559
  · exact B1802563
  · exact B1802567
  · exact B1802571
  · exact B1802575
  · exact B1802579
  · exact B1802583
  · exact B1802587
  · exact B1802591
  · exact B1802595
  · exact B1802599
  · exact B1802603
  · exact B1802607
  · exact B1802611
  · exact B1802615
  · exact B1802619
  · exact B1802623
  · exact B1802627
  · exact B1802631
  · exact B1802635
  · exact B1802639
  · exact B1802643
  · exact B1802647
  · exact B1802651
  · exact B1802655
  · exact B1802659
  · exact B1802663
  · exact B1802667
  · exact B1802671
  · exact B1802675
  · exact B1802679
  · exact B1802683
  · exact B1802687
  · exact B1802691
  · exact B1802695
  · exact B1802699
  · exact B1802703
  · exact B1802707
  · exact B1802711
  · exact B1802715
  · exact B1802719
  · exact B1802723
  · exact B1802727
  · exact B1802731
  · exact B1802735
  · exact B1802739
  · exact B1802743
  · exact B1802747
  · exact B1802751
  · exact B1802755
  · exact B1802759
  · exact B1802763
  · exact B1802767
  · exact B1802771
  · exact B1802775
  · exact B1802779
  · exact B1802783
  · exact B1802787
  · exact B1802791
  · exact B1802795
  · exact B1802799
  · exact B1802803
  · exact B1802807
  · exact B1802811
  · exact B1802815
  · exact B1802819
  · exact B1802823
  · exact B1802827
  · exact B1802831
  · exact B1802835
  · exact B1802839
  · exact B1802843
  · exact B1802847
  · exact B1802851
  · exact B1802855
  · exact B1802859
  · exact B1802863
  · exact B1802867
  · exact B1802871
  · exact B1802875
  · exact B1802879
  · exact B1802883
  · exact B1802887
  · exact B1802891
  · exact B1802895
  · exact B1802899
  · exact B1802903
  · exact B1802907
  · exact B1802911
  · exact B1802915
  · exact B1802919
  · exact B1802923
  · exact B1802927
  · exact B1802931
  · exact B1802935
  · exact B1802939
  · exact B1802943
  · exact B1802947
  · exact B1802951
  · exact B1802955
  · exact B1802959
  · exact B1802963
  · exact B1802967
  · exact B1802971
  · exact B1802975
  · exact B1802979
  · exact B1802983
  · exact B1802987
  · exact B1802991
  · exact B1802995
  · exact B1802999
  · exact B1803003
  · exact B1803007
  · exact B1803011
  · exact B1803015
  · exact B1803019
  · exact B1803023
  · exact B1803027
  · exact B1803031
  · exact B1803035
  · exact B1803039
  · exact B1803043
  · exact B1803047
  · exact B1803051
  · exact B1803055
  · exact B1803059
  · exact B1803063
  · exact B1803067
  · exact B1803071
  · exact B1803075
  · exact B1803079
  · exact B1803083
  · exact B1803087
  · exact B1803091
  · exact B1803095
  · exact B1803099
  · exact B1803103
  · exact B1803107
  · exact B1803111
  · exact B1803115
  · exact B1803119
  · exact B1803123
  · exact B1803127
  · exact B1803131
  · exact B1803135
  · exact B1803139
  · exact B1803143
  · exact B1803147
  · exact B1803151
  · exact B1803155
  · exact B1803159
  · exact B1803163
  · exact B1803167
  · exact B1803171
  · exact B1803175
  · exact B1803179
  · exact B1803183
  · exact B1803187
  · exact B1803191
  · exact B1803195
  · exact B1803199
  · exact B1803203
  · exact B1803207
  · exact B1803211
  · exact B1803215
  · exact B1803219
  · exact B1803223
  · exact B1803227
  · exact B1803231
  · exact B1803235
  · exact B1803239
  · exact B1803243
  · exact B1803247
  · exact B1803251
  · exact B1803255
  · exact B1803259
  · exact B1803263
  · exact B1803267
  · exact B1803271
  · exact B1803275
  · exact B1803279
  · exact B1803283
  · exact B1803287
  · exact B1803291
  · exact B1803295
  · exact B1803299
  · exact B1803303
  · exact B1803307
  · exact B1803311
  · exact B1803315
  · exact B1803319
  · exact B1803323
  · exact B1803327
  · exact B1803331
  · exact B1803335
  · exact B1803339
  · exact B1803343
  · exact B1803347
  · exact B1803351
  · exact B1803355
  · exact B1803359
  · exact B1803363
  · exact B1803367
  · exact B1803371
  · exact B1803375
  · exact B1803379
  · exact B1803383
  · exact B1803387
  · exact B1803391
  · exact B1803395
  · exact B1803399
  · exact B1803403
  · exact B1803407
  · exact B1803411
  · exact B1803415
  · exact B1803419
  · exact B1803423
  · exact B1803427
  · exact B1803431
  · exact B1803435
  · exact B1803439
  · exact B1803443
  · exact B1803447
  · exact B1803451
  · exact B1803455
  · exact B1803459
  · exact B1803463
  · exact B1803467
  · exact B1803471
  · exact B1803475
  · exact B1803479
  · exact B1803483
  · exact B1803487
  · exact B1803491
  · exact B1803495
  · exact B1803499
  · exact B1803503
  · exact B1803507
  · exact B1803511
  · exact B1803515
  · exact B1803519
  · exact B1803523
  · exact B1803527
  · exact B1803531
  · exact B1803535
  · exact B1803539
  · exact B1803543
  · exact B1803547
  · exact B1803551
  · exact B1803555
  · exact B1803559
  · exact B1803563
  · exact B1803567
  · exact B1803571
  · exact B1803575
  · exact B1803579
  · exact B1803583
  · exact B1803587
  · exact B1803591
  · exact B1803595
  · exact B1803599

theorem solution (m : ℕ) (hlo : 1801602 ≤ m) (hhi : m ≤ 1803602) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 450400 ≤ j := by omega
    have hj2 : j ≤ 450899 := by omega
    have hb : Blo 1801602 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
