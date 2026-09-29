-- Prove2me | solution 1 for syracuse_descends_range_1564980_1566980
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:06:38.612986+00:00
-- url     : https://prove2.me/submissions/24f4594b-bfb7-4549-b8c1-07cefe5e6ad7

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


theorem B5283845 : Blo 1564980 5283845 := bbase (se 4 (by rfl) ⟨495360, by rfl⟩ : syracuseStep 5283845 = 990721) (by norm_num)
theorem B3522581 : Blo 1564980 3522581 := bbase (se 6 (by rfl) ⟨82560, by rfl⟩ : syracuseStep 3522581 = 165121) (by norm_num)
theorem B1982485 : Blo 1564980 1982485 := bbase (se 6 (by rfl) ⟨46464, by rfl⟩ : syracuseStep 1982485 = 92929) (by norm_num)
theorem B1761313 : Blo 1564980 1761313 := bbase (se 2 (by rfl) ⟨660492, by rfl⟩ : syracuseStep 1761313 = 1320985) (by norm_num)
theorem B1761349 : Blo 1564980 1761349 := bbase (se 4 (by rfl) ⟨165126, by rfl⟩ : syracuseStep 1761349 = 330253) (by norm_num)
theorem B2973773 : Blo 1564980 2973773 := bbase (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) (by norm_num)
theorem B3522653 : Blo 1564980 3522653 := bbase (se 3 (by rfl) ⟨660497, by rfl⟩ : syracuseStep 3522653 = 1320995) (by norm_num)
theorem B3965021 : Blo 1564980 3965021 := bbase (se 3 (by rfl) ⟨743441, by rfl⟩ : syracuseStep 3965021 = 1486883) (by norm_num)
theorem B1761385 : Blo 1564980 1761385 := bbase (se 2 (by rfl) ⟨660519, by rfl⟩ : syracuseStep 1761385 = 1321039) (by norm_num)
theorem B1761421 : Blo 1564980 1761421 := bbase (se 3 (by rfl) ⟨330266, by rfl⟩ : syracuseStep 1761421 = 660533) (by norm_num)
theorem B3522725 : Blo 1564980 3522725 := bbase (se 4 (by rfl) ⟨330255, by rfl⟩ : syracuseStep 3522725 = 660511) (by norm_num)
theorem B1761457 : Blo 1564980 1761457 := bbase (se 2 (by rfl) ⟨660546, by rfl⟩ : syracuseStep 1761457 = 1321093) (by norm_num)
theorem B1982657 : Blo 1564980 1982657 := bbase (se 2 (by rfl) ⟨743496, by rfl⟩ : syracuseStep 1982657 = 1486993) (by norm_num)
theorem B1761493 : Blo 1564980 1761493 := bbase (se 7 (by rfl) ⟨20642, by rfl⟩ : syracuseStep 1761493 = 41285) (by norm_num)
theorem B2859229 : Blo 1564980 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B7520485 : Blo 1564980 7520485 := bbase (se 4 (by rfl) ⟨705045, by rfl⟩ : syracuseStep 7520485 = 1410091) (by norm_num)
theorem B2973925 : Blo 1564980 2973925 := bbase (se 4 (by rfl) ⟨278805, by rfl⟩ : syracuseStep 2973925 = 557611) (by norm_num)
theorem B3522797 : Blo 1564980 3522797 := bbase (se 3 (by rfl) ⟨660524, by rfl⟩ : syracuseStep 3522797 = 1321049) (by norm_num)
theorem B1761529 : Blo 1564980 1761529 := bbase (se 2 (by rfl) ⟨660573, by rfl⟩ : syracuseStep 1761529 = 1321147) (by norm_num)
theorem B1982713 : Blo 1564980 1982713 := bbase (se 2 (by rfl) ⟨743517, by rfl⟩ : syracuseStep 1982713 = 1487035) (by norm_num)
theorem B2228485 : Blo 1564980 2228485 := bbase (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) (by norm_num)
theorem B1671445 : Blo 1564980 1671445 := bbase (se 6 (by rfl) ⟨39174, by rfl⟩ : syracuseStep 1671445 = 78349) (by norm_num)
theorem B1671449 : Blo 1564980 1671449 := bbase (se 2 (by rfl) ⟨626793, by rfl⟩ : syracuseStep 1671449 = 1253587) (by norm_num)
theorem B1761565 : Blo 1564980 1761565 := bbase (se 3 (by rfl) ⟨330293, by rfl⟩ : syracuseStep 1761565 = 660587) (by norm_num)
theorem B3965213 : Blo 1564980 3965213 := bbase (se 3 (by rfl) ⟨743477, by rfl⟩ : syracuseStep 3965213 = 1486955) (by norm_num)
theorem B3522869 : Blo 1564980 3522869 := bbase (se 5 (by rfl) ⟨165134, by rfl⟩ : syracuseStep 3522869 = 330269) (by norm_num)
theorem B3760445 : Blo 1564980 3760445 := bbase (se 3 (by rfl) ⟨705083, by rfl⟩ : syracuseStep 3760445 = 1410167) (by norm_num)
theorem B1761601 : Blo 1564980 1761601 := bbase (se 2 (by rfl) ⟨660600, by rfl⟩ : syracuseStep 1761601 = 1321201) (by norm_num)
theorem B3760453 : Blo 1564980 3760453 := bbase (se 4 (by rfl) ⟨352542, by rfl⟩ : syracuseStep 3760453 = 705085) (by norm_num)
theorem B1982809 : Blo 1564980 1982809 := bbase (se 2 (by rfl) ⟨743553, by rfl⟩ : syracuseStep 1982809 = 1487107) (by norm_num)
theorem B1761637 : Blo 1564980 1761637 := bbase (se 4 (by rfl) ⟨165153, by rfl⟩ : syracuseStep 1761637 = 330307) (by norm_num)
theorem B3522941 : Blo 1564980 3522941 := bbase (se 3 (by rfl) ⟨660551, by rfl⟩ : syracuseStep 3522941 = 1321103) (by norm_num)
theorem B1761673 : Blo 1564980 1761673 := bbase (se 2 (by rfl) ⟨660627, by rfl⟩ : syracuseStep 1761673 = 1321255) (by norm_num)
theorem B1761709 : Blo 1564980 1761709 := bbase (se 3 (by rfl) ⟨330320, by rfl⟩ : syracuseStep 1761709 = 660641) (by norm_num)
theorem B5284277 : Blo 1564980 5284277 := bbase (se 5 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 5284277 = 495401) (by norm_num)
theorem B3523013 : Blo 1564980 3523013 := bbase (se 4 (by rfl) ⟨330282, by rfl⟩ : syracuseStep 3523013 = 660565) (by norm_num)
theorem B1761745 : Blo 1564980 1761745 := bbase (se 2 (by rfl) ⟨660654, by rfl⟩ : syracuseStep 1761745 = 1321309) (by norm_num)
theorem B1761781 : Blo 1564980 1761781 := bbase (se 5 (by rfl) ⟨82583, by rfl⟩ : syracuseStep 1761781 = 165167) (by norm_num)
theorem B1982981 : Blo 1564980 1982981 := bbase (se 4 (by rfl) ⟨185904, by rfl⟩ : syracuseStep 1982981 = 371809) (by norm_num)
theorem B3523085 : Blo 1564980 3523085 := bbase (se 3 (by rfl) ⟨660578, by rfl⟩ : syracuseStep 3523085 = 1321157) (by norm_num)
theorem B2974229 : Blo 1564980 2974229 := bbase (se 6 (by rfl) ⟨69708, by rfl⟩ : syracuseStep 2974229 = 139417) (by norm_num)
theorem B1761817 : Blo 1564980 1761817 := bbase (se 2 (by rfl) ⟨660681, by rfl⟩ : syracuseStep 1761817 = 1321363) (by norm_num)
theorem B1761853 : Blo 1564980 1761853 := bbase (se 3 (by rfl) ⟨330347, by rfl⟩ : syracuseStep 1761853 = 660695) (by norm_num)
theorem B1983037 : Blo 1564980 1983037 := bbase (se 3 (by rfl) ⟨371819, by rfl⟩ : syracuseStep 1983037 = 743639) (by norm_num)
theorem B3523157 : Blo 1564980 3523157 := bbase (se 8 (by rfl) ⟨20643, by rfl⟩ : syracuseStep 3523157 = 41287) (by norm_num)
theorem B1761889 : Blo 1564980 1761889 := bbase (se 2 (by rfl) ⟨660708, by rfl⟩ : syracuseStep 1761889 = 1321417) (by norm_num)
theorem B3965557 : Blo 1564980 3965557 := bbase (se 5 (by rfl) ⟨185885, by rfl⟩ : syracuseStep 3965557 = 371771) (by norm_num)
theorem B1761925 : Blo 1564980 1761925 := bbase (se 4 (by rfl) ⟨165180, by rfl⟩ : syracuseStep 1761925 = 330361) (by norm_num)
theorem B3523229 : Blo 1564980 3523229 := bbase (se 3 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 3523229 = 1321211) (by norm_num)
theorem B1983133 : Blo 1564980 1983133 := bbase (se 3 (by rfl) ⟨371837, by rfl⟩ : syracuseStep 1983133 = 743675) (by norm_num)
theorem B1761961 : Blo 1564980 1761961 := bbase (se 2 (by rfl) ⟨660735, by rfl⟩ : syracuseStep 1761961 = 1321471) (by norm_num)
theorem B1761997 : Blo 1564980 1761997 := bbase (se 3 (by rfl) ⟨330374, by rfl⟩ : syracuseStep 1761997 = 660749) (by norm_num)
theorem B3343069 : Blo 1564980 3343069 := bbase (se 3 (by rfl) ⟨626825, by rfl⟩ : syracuseStep 3343069 = 1253651) (by norm_num)
theorem B3523301 : Blo 1564980 3523301 := bbase (se 4 (by rfl) ⟨330309, by rfl⟩ : syracuseStep 3523301 = 660619) (by norm_num)
theorem B3965669 : Blo 1564980 3965669 := bbase (se 4 (by rfl) ⟨371781, by rfl⟩ : syracuseStep 3965669 = 743563) (by norm_num)
theorem B1762033 : Blo 1564980 1762033 := bbase (se 2 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 1762033 = 1321525) (by norm_num)
theorem B1762069 : Blo 1564980 1762069 := bbase (se 6 (by rfl) ⟨41298, by rfl⟩ : syracuseStep 1762069 = 82597) (by norm_num)
theorem B3523373 : Blo 1564980 3523373 := bbase (se 3 (by rfl) ⟨660632, by rfl⟩ : syracuseStep 3523373 = 1321265) (by norm_num)
theorem B1762105 : Blo 1564980 1762105 := bbase (se 2 (by rfl) ⟨660789, by rfl⟩ : syracuseStep 1762105 = 1321579) (by norm_num)
theorem B1786681 : Blo 1564980 1786681 := bbase (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) (by norm_num)
theorem B1672013 : Blo 1564980 1672013 := bbase (se 3 (by rfl) ⟨313502, by rfl⟩ : syracuseStep 1672013 = 627005) (by norm_num)
theorem B3343189 : Blo 1564980 3343189 := bbase (se 9 (by rfl) ⟨9794, by rfl⟩ : syracuseStep 3343189 = 19589) (by norm_num)
theorem B2229077 : Blo 1564980 2229077 := bbase (se 9 (by rfl) ⟨6530, by rfl⟩ : syracuseStep 2229077 = 13061) (by norm_num)
theorem B7930709 : Blo 1564980 7930709 := bbase (se 9 (by rfl) ⟨23234, by rfl⟩ : syracuseStep 7930709 = 46469) (by norm_num)
theorem B1762141 : Blo 1564980 1762141 := bbase (se 3 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 1762141 = 660803) (by norm_num)
theorem B5284709 : Blo 1564980 5284709 := bbase (se 4 (by rfl) ⟨495441, by rfl⟩ : syracuseStep 5284709 = 990883) (by norm_num)
theorem B5948261 : Blo 1564980 5948261 := bbase (se 4 (by rfl) ⟨557649, by rfl⟩ : syracuseStep 5948261 = 1115299) (by norm_num)
theorem B3523445 : Blo 1564980 3523445 := bbase (se 5 (by rfl) ⟨165161, by rfl⟩ : syracuseStep 3523445 = 330323) (by norm_num)
theorem B1762177 : Blo 1564980 1762177 := bbase (se 2 (by rfl) ⟨660816, by rfl⟩ : syracuseStep 1762177 = 1321633) (by norm_num)
theorem B2229157 : Blo 1564980 2229157 := bbase (se 4 (by rfl) ⟨208983, by rfl⟩ : syracuseStep 2229157 = 417967) (by norm_num)
theorem B1762213 : Blo 1564980 1762213 := bbase (se 4 (by rfl) ⟨165207, by rfl⟩ : syracuseStep 1762213 = 330415) (by norm_num)
theorem B3965861 : Blo 1564980 3965861 := bbase (se 4 (by rfl) ⟨371799, by rfl⟩ : syracuseStep 3965861 = 743599) (by norm_num)
theorem B3523517 : Blo 1564980 3523517 := bbase (se 3 (by rfl) ⟨660659, by rfl⟩ : syracuseStep 3523517 = 1321319) (by norm_num)
theorem B1762249 : Blo 1564980 1762249 := bbase (se 2 (by rfl) ⟨660843, by rfl⟩ : syracuseStep 1762249 = 1321687) (by norm_num)
theorem B1762285 : Blo 1564980 1762285 := bbase (se 3 (by rfl) ⟨330428, by rfl⟩ : syracuseStep 1762285 = 660857) (by norm_num)
theorem B3523589 : Blo 1564980 3523589 := bbase (se 4 (by rfl) ⟨330336, by rfl⟩ : syracuseStep 3523589 = 660673) (by norm_num)
theorem B1672201 : Blo 1564980 1672201 := bbase (se 2 (by rfl) ⟨627075, by rfl⟩ : syracuseStep 1672201 = 1254151) (by norm_num)
theorem B2507789 : Blo 1564980 2507789 := bbase (se 3 (by rfl) ⟨470210, by rfl⟩ : syracuseStep 2507789 = 940421) (by norm_num)
theorem B1762321 : Blo 1564980 1762321 := bbase (se 2 (by rfl) ⟨660870, by rfl⟩ : syracuseStep 1762321 = 1321741) (by norm_num)
theorem B2229277 : Blo 1564980 2229277 := bbase (se 3 (by rfl) ⟨417989, by rfl⟩ : syracuseStep 2229277 = 835979) (by norm_num)
theorem B1762357 : Blo 1564980 1762357 := bbase (se 5 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 1762357 = 165221) (by norm_num)
theorem B3523661 : Blo 1564980 3523661 := bbase (se 3 (by rfl) ⟨660686, by rfl⟩ : syracuseStep 3523661 = 1321373) (by norm_num)
theorem B3343445 : Blo 1564980 3343445 := bbase (se 8 (by rfl) ⟨19590, by rfl⟩ : syracuseStep 3343445 = 39181) (by norm_num)
theorem B7529557 : Blo 1564980 7529557 := bbase (se 8 (by rfl) ⟨44118, by rfl⟩ : syracuseStep 7529557 = 88237) (by norm_num)
theorem B1762393 : Blo 1564980 1762393 := bbase (se 2 (by rfl) ⟨660897, by rfl⟩ : syracuseStep 1762393 = 1321795) (by norm_num)
theorem B2229373 : Blo 1564980 2229373 := bbase (se 3 (by rfl) ⟨418007, by rfl⟩ : syracuseStep 2229373 = 836015) (by norm_num)
theorem B1762429 : Blo 1564980 1762429 := bbase (se 3 (by rfl) ⟨330455, by rfl⟩ : syracuseStep 1762429 = 660911) (by norm_num)
theorem B5948549 : Blo 1564980 5948549 := bbase (se 4 (by rfl) ⟨557676, by rfl⟩ : syracuseStep 5948549 = 1115353) (by norm_num)
theorem B2507917 : Blo 1564980 2507917 := bbase (se 3 (by rfl) ⟨470234, by rfl⟩ : syracuseStep 2507917 = 940469) (by norm_num)
theorem B17826965 : Blo 1564980 17826965 := bbase (se 6 (by rfl) ⟨417819, by rfl⟩ : syracuseStep 17826965 = 835639) (by norm_num)
theorem B3523733 : Blo 1564980 3523733 := bbase (se 6 (by rfl) ⟨82587, by rfl⟩ : syracuseStep 3523733 = 165175) (by norm_num)
theorem B1762465 : Blo 1564980 1762465 := bbase (se 2 (by rfl) ⟨660924, by rfl⟩ : syracuseStep 1762465 = 1321849) (by norm_num)
theorem B11281589 : Blo 1564980 11281589 := bbase (se 5 (by rfl) ⟨528824, by rfl⟩ : syracuseStep 11281589 = 1057649) (by norm_num)
theorem B1762501 : Blo 1564980 1762501 := bbase (se 4 (by rfl) ⟨165234, by rfl⟩ : syracuseStep 1762501 = 330469) (by norm_num)
theorem B36660437 : Blo 1564980 36660437 := bbase (se 7 (by rfl) ⟨429614, by rfl⟩ : syracuseStep 36660437 = 859229) (by norm_num)
theorem B3523805 : Blo 1564980 3523805 := bbase (se 3 (by rfl) ⟨660713, by rfl⟩ : syracuseStep 3523805 = 1321427) (by norm_num)
theorem B5014757 : Blo 1564980 5014757 := bbase (se 4 (by rfl) ⟨470133, by rfl⟩ : syracuseStep 5014757 = 940267) (by norm_num)
theorem B1762537 : Blo 1564980 1762537 := bbase (se 2 (by rfl) ⟨660951, by rfl⟩ : syracuseStep 1762537 = 1321903) (by norm_num)
theorem B7922933 : Blo 1564980 7922933 := bbase (se 5 (by rfl) ⟨371387, by rfl⟩ : syracuseStep 7922933 = 742775) (by norm_num)
theorem B3966205 : Blo 1564980 3966205 := bbase (se 3 (by rfl) ⟨743663, by rfl⟩ : syracuseStep 3966205 = 1487327) (by norm_num)
theorem B1762573 : Blo 1564980 1762573 := bbase (se 3 (by rfl) ⟨330482, by rfl⟩ : syracuseStep 1762573 = 660965) (by norm_num)
theorem B5285141 : Blo 1564980 5285141 := bbase (se 6 (by rfl) ⟨123870, by rfl⟩ : syracuseStep 5285141 = 247741) (by norm_num)
theorem B5358869 : Blo 1564980 5358869 := bbase (se 6 (by rfl) ⟨125598, by rfl⟩ : syracuseStep 5358869 = 251197) (by norm_num)
theorem B3523877 : Blo 1564980 3523877 := bbase (se 4 (by rfl) ⟨330363, by rfl⟩ : syracuseStep 3523877 = 660727) (by norm_num)
theorem B3761453 : Blo 1564980 3761453 := bbase (se 3 (by rfl) ⟨705272, by rfl⟩ : syracuseStep 3761453 = 1410545) (by norm_num)
theorem B1762609 : Blo 1564980 1762609 := bbase (se 2 (by rfl) ⟨660978, by rfl⟩ : syracuseStep 1762609 = 1321957) (by norm_num)
theorem B1762645 : Blo 1564980 1762645 := bbase (se 12 (by rfl) ⟨645, by rfl⟩ : syracuseStep 1762645 = 1291) (by norm_num)
theorem B3523949 : Blo 1564980 3523949 := bbase (se 3 (by rfl) ⟨660740, by rfl⟩ : syracuseStep 3523949 = 1321481) (by norm_num)
theorem B3966317 : Blo 1564980 3966317 := bbase (se 3 (by rfl) ⟨743684, by rfl⟩ : syracuseStep 3966317 = 1487369) (by norm_num)
theorem B1762681 : Blo 1564980 1762681 := bbase (se 2 (by rfl) ⟨661005, by rfl⟩ : syracuseStep 1762681 = 1322011) (by norm_num)
theorem B1762717 : Blo 1564980 1762717 := bbase (se 3 (by rfl) ⟨330509, by rfl⟩ : syracuseStep 1762717 = 661019) (by norm_num)
theorem B3524021 : Blo 1564980 3524021 := bbase (se 5 (by rfl) ⟨165188, by rfl⟩ : syracuseStep 3524021 = 330377) (by norm_num)
theorem B1762753 : Blo 1564980 1762753 := bbase (se 2 (by rfl) ⟨661032, by rfl⟩ : syracuseStep 1762753 = 1322065) (by norm_num)
theorem B1762789 : Blo 1564980 1762789 := bbase (se 4 (by rfl) ⟨165261, by rfl⟩ : syracuseStep 1762789 = 330523) (by norm_num)
theorem B12699125 : Blo 1564980 12699125 := bbase (se 5 (by rfl) ⟨595271, by rfl⟩ : syracuseStep 12699125 = 1190543) (by norm_num)
theorem B3524093 : Blo 1564980 3524093 := bbase (se 3 (by rfl) ⟨660767, by rfl⟩ : syracuseStep 3524093 = 1321535) (by norm_num)
theorem B4580869 : Blo 1564980 4580869 := bbase (se 4 (by rfl) ⟨429456, by rfl⟩ : syracuseStep 4580869 = 858913) (by norm_num)
theorem B1762825 : Blo 1564980 1762825 := bbase (se 2 (by rfl) ⟨661059, by rfl⟩ : syracuseStep 1762825 = 1322119) (by norm_num)
theorem B3524165 : Blo 1564980 3524165 := bbase (se 4 (by rfl) ⟨330390, by rfl⟩ : syracuseStep 3524165 = 660781) (by norm_num)
theorem B4761173 : Blo 1564980 4761173 := bbase (se 8 (by rfl) ⟨27897, by rfl⟩ : syracuseStep 4761173 = 55795) (by norm_num)
theorem B2229869 : Blo 1564980 2229869 := bbase (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) (by norm_num)
theorem B3524237 : Blo 1564980 3524237 := bbase (se 3 (by rfl) ⟨660794, by rfl⟩ : syracuseStep 3524237 = 1321589) (by norm_num)
theorem B5285573 : Blo 1564980 5285573 := bbase (se 4 (by rfl) ⟨495522, by rfl⟩ : syracuseStep 5285573 = 991045) (by norm_num)
theorem B3524309 : Blo 1564980 3524309 := bbase (se 7 (by rfl) ⟨41300, by rfl⟩ : syracuseStep 3524309 = 82601) (by norm_num)
theorem B2541277 : Blo 1564980 2541277 := bbase (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) (by norm_num)
theorem B8922869 : Blo 1564980 8922869 := bbase (se 5 (by rfl) ⟨418259, by rfl⟩ : syracuseStep 8922869 = 836519) (by norm_num)
theorem B3524381 : Blo 1564980 3524381 := bbase (se 3 (by rfl) ⟨660821, by rfl⟩ : syracuseStep 3524381 = 1321643) (by norm_num)
theorem B1673021 : Blo 1564980 1673021 := bbase (se 3 (by rfl) ⟨313691, by rfl⟩ : syracuseStep 1673021 = 627383) (by norm_num)
theorem B6686549 : Blo 1564980 6686549 := bbase (se 9 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 6686549 = 39179) (by norm_num)
theorem B3524453 : Blo 1564980 3524453 := bbase (se 4 (by rfl) ⟨330417, by rfl⟩ : syracuseStep 3524453 = 660835) (by norm_num)
theorem B8914805 : Blo 1564980 8914805 := bbase (se 5 (by rfl) ⟨417881, by rfl⟩ : syracuseStep 8914805 = 835763) (by norm_num)
theorem B3524525 : Blo 1564980 3524525 := bbase (se 3 (by rfl) ⟨660848, by rfl⟩ : syracuseStep 3524525 = 1321697) (by norm_num)
theorem B2508725 : Blo 1564980 2508725 := bbase (se 5 (by rfl) ⟨117596, by rfl⟩ : syracuseStep 2508725 = 235193) (by norm_num)
theorem B3344333 : Blo 1564980 3344333 := bbase (se 3 (by rfl) ⟨627062, by rfl⟩ : syracuseStep 3344333 = 1254125) (by norm_num)
theorem B3524597 : Blo 1564980 3524597 := bbase (se 5 (by rfl) ⟨165215, by rfl⟩ : syracuseStep 3524597 = 330431) (by norm_num)
theorem B15042581 : Blo 1564980 15042581 := bbase (se 6 (by rfl) ⟨352560, by rfl⟩ : syracuseStep 15042581 = 705121) (by norm_num)
theorem B3762221 : Blo 1564980 3762221 := bbase (se 3 (by rfl) ⟨705416, by rfl⟩ : syracuseStep 3762221 = 1410833) (by norm_num)
theorem B3524669 : Blo 1564980 3524669 := bbase (se 3 (by rfl) ⟨660875, by rfl⟩ : syracuseStep 3524669 = 1321751) (by norm_num)
theorem B7932005 : Blo 1564980 7932005 := bbase (se 4 (by rfl) ⟨743625, by rfl⟩ : syracuseStep 7932005 = 1487251) (by norm_num)
theorem B5286005 : Blo 1564980 5286005 := bbase (se 5 (by rfl) ⟨247781, by rfl⟩ : syracuseStep 5286005 = 495563) (by norm_num)
theorem B2115709 : Blo 1564980 2115709 := bbase (se 3 (by rfl) ⟨396695, by rfl⟩ : syracuseStep 2115709 = 793391) (by norm_num)
theorem B3524741 : Blo 1564980 3524741 := bbase (se 4 (by rfl) ⟨330444, by rfl⟩ : syracuseStep 3524741 = 660889) (by norm_num)
theorem B2230421 : Blo 1564980 2230421 := bbase (se 6 (by rfl) ⟨52275, by rfl⟩ : syracuseStep 2230421 = 104551) (by norm_num)
theorem B3344573 : Blo 1564980 3344573 := bbase (se 3 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 3344573 = 1254215) (by norm_num)
theorem B3524813 : Blo 1564980 3524813 := bbase (se 3 (by rfl) ⟨660902, by rfl⟩ : syracuseStep 3524813 = 1321805) (by norm_num)
theorem B2509013 : Blo 1564980 2509013 := bbase (se 7 (by rfl) ⟨29402, by rfl⟩ : syracuseStep 2509013 = 58805) (by norm_num)
theorem B2115829 : Blo 1564980 2115829 := bbase (se 5 (by rfl) ⟨99179, by rfl⟩ : syracuseStep 2115829 = 198359) (by norm_num)
theorem B3524885 : Blo 1564980 3524885 := bbase (se 6 (by rfl) ⟨82614, by rfl⟩ : syracuseStep 3524885 = 165229) (by norm_num)
theorem B3524957 : Blo 1564980 3524957 := bbase (se 3 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 3524957 = 1321859) (by norm_num)
theorem B3525029 : Blo 1564980 3525029 := bbase (se 4 (by rfl) ⟨330471, by rfl⟩ : syracuseStep 3525029 = 660943) (by norm_num)
theorem B4762037 : Blo 1564980 4762037 := bbase (se 5 (by rfl) ⟨223220, by rfl⟩ : syracuseStep 4762037 = 446441) (by norm_num)
theorem B3525101 : Blo 1564980 3525101 := bbase (se 3 (by rfl) ⟨660956, by rfl⟩ : syracuseStep 3525101 = 1321913) (by norm_num)
theorem B7924229 : Blo 1564980 7924229 := bbase (se 4 (by rfl) ⟨742896, by rfl⟩ : syracuseStep 7924229 = 1485793) (by norm_num)
theorem B5286437 : Blo 1564980 5286437 := bbase (se 4 (by rfl) ⟨495603, by rfl⟩ : syracuseStep 5286437 = 991207) (by norm_num)
theorem B3525173 : Blo 1564980 3525173 := bbase (se 5 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 3525173 = 330485) (by norm_num)
theorem B5016181 : Blo 1564980 5016181 := bbase (se 5 (by rfl) ⟨235133, by rfl⟩ : syracuseStep 5016181 = 470267) (by norm_num)
theorem B2509429 : Blo 1564980 2509429 := bbase (se 5 (by rfl) ⟨117629, by rfl⟩ : syracuseStep 2509429 = 235259) (by norm_num)
theorem B3525245 : Blo 1564980 3525245 := bbase (se 3 (by rfl) ⟨660983, by rfl⟩ : syracuseStep 3525245 = 1321967) (by norm_num)
theorem B4459157 : Blo 1564980 4459157 := bbase (se 6 (by rfl) ⟨104511, by rfl⟩ : syracuseStep 4459157 = 209023) (by norm_num)
theorem B3345077 : Blo 1564980 3345077 := bbase (se 5 (by rfl) ⟨156800, by rfl⟩ : syracuseStep 3345077 = 313601) (by norm_num)
theorem B3345085 : Blo 1564980 3345085 := bbase (se 3 (by rfl) ⟨627203, by rfl⟩ : syracuseStep 3345085 = 1254407) (by norm_num)
theorem B3525317 : Blo 1564980 3525317 := bbase (se 4 (by rfl) ⟨330498, by rfl⟩ : syracuseStep 3525317 = 660997) (by norm_num)
theorem B3525389 : Blo 1564980 3525389 := bbase (se 3 (by rfl) ⟨661010, by rfl⟩ : syracuseStep 3525389 = 1322021) (by norm_num)
theorem B2009933 : Blo 1564980 2009933 := bbase (se 3 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 2009933 = 753725) (by norm_num)
theorem B3525461 : Blo 1564980 3525461 := bbase (se 9 (by rfl) ⟨10328, by rfl⟩ : syracuseStep 3525461 = 20657) (by norm_num)
theorem B8924053 : Blo 1564980 8924053 := bbase (se 6 (by rfl) ⟨209157, by rfl⟩ : syracuseStep 8924053 = 418315) (by norm_num)
theorem B3525533 : Blo 1564980 3525533 := bbase (se 3 (by rfl) ⟨661037, by rfl⟩ : syracuseStep 3525533 = 1322075) (by norm_num)
theorem B2862005 : Blo 1564980 2862005 := bbase (se 5 (by rfl) ⟨134156, by rfl⟩ : syracuseStep 2862005 = 268313) (by norm_num)
theorem B5286869 : Blo 1564980 5286869 := bbase (se 7 (by rfl) ⟨61955, by rfl⟩ : syracuseStep 5286869 = 123911) (by norm_num)
theorem B3525605 : Blo 1564980 3525605 := bbase (se 4 (by rfl) ⟨330525, by rfl⟩ : syracuseStep 3525605 = 661051) (by norm_num)
theorem B5942261 : Blo 1564980 5942261 := bbase (se 5 (by rfl) ⟨278543, by rfl⟩ : syracuseStep 5942261 = 557087) (by norm_num)
theorem B2640917 : Blo 1564980 2640917 := bbase (se 6 (by rfl) ⟨61896, by rfl⟩ : syracuseStep 2640917 = 123793) (by norm_num)
theorem B3525677 : Blo 1564980 3525677 := bbase (se 3 (by rfl) ⟨661064, by rfl⟩ : syracuseStep 3525677 = 1322129) (by norm_num)
theorem B5016629 : Blo 1564980 5016629 := bbase (se 5 (by rfl) ⟨235154, by rfl⟩ : syracuseStep 5016629 = 470309) (by norm_num)
theorem B2821205 : Blo 1564980 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B2641045 : Blo 1564980 2641045 := bbase (se 6 (by rfl) ⟨61899, by rfl⟩ : syracuseStep 2641045 = 123799) (by norm_num)
theorem B2641133 : Blo 1564980 2641133 := bbase (se 3 (by rfl) ⟨495212, by rfl⟩ : syracuseStep 2641133 = 990425) (by norm_num)
theorem B9522517 : Blo 1564980 9522517 := bbase (se 11 (by rfl) ⟨6974, by rfl⟩ : syracuseStep 9522517 = 13949) (by norm_num)
theorem B2641261 : Blo 1564980 2641261 := bbase (se 3 (by rfl) ⟨495236, by rfl⟩ : syracuseStep 2641261 = 990473) (by norm_num)
theorem B1609081 : Blo 1564980 1609081 := bbase (se 2 (by rfl) ⟨603405, by rfl⟩ : syracuseStep 1609081 = 1206811) (by norm_num)
theorem B5287301 : Blo 1564980 5287301 := bbase (se 4 (by rfl) ⟨495684, by rfl⟩ : syracuseStep 5287301 = 991369) (by norm_num)
theorem B2035109 : Blo 1564980 2035109 := bbase (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) (by norm_num)
theorem B2641349 : Blo 1564980 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B1609205 : Blo 1564980 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B2641477 : Blo 1564980 2641477 := bbase (se 4 (by rfl) ⟨247638, by rfl⟩ : syracuseStep 2641477 = 495277) (by norm_num)
theorem B6688325 : Blo 1564980 6688325 := bbase (se 4 (by rfl) ⟨627030, by rfl⟩ : syracuseStep 6688325 = 1254061) (by norm_num)
theorem B2641565 : Blo 1564980 2641565 := bbase (se 3 (by rfl) ⟨495293, by rfl⟩ : syracuseStep 2641565 = 990587) (by norm_num)
theorem B7925525 : Blo 1564980 7925525 := bbase (se 6 (by rfl) ⟨185754, by rfl⟩ : syracuseStep 7925525 = 371509) (by norm_num)
theorem B2641693 : Blo 1564980 2641693 := bbase (se 3 (by rfl) ⟨495317, by rfl⟩ : syracuseStep 2641693 = 990635) (by norm_num)
theorem B3346213 : Blo 1564980 3346213 := bbase (se 4 (by rfl) ⟨313707, by rfl⟩ : syracuseStep 3346213 = 627415) (by norm_num)
theorem B6688565 : Blo 1564980 6688565 := bbase (se 5 (by rfl) ⟨313526, by rfl⟩ : syracuseStep 6688565 = 627053) (by norm_num)
theorem B4460341 : Blo 1564980 4460341 := bbase (se 5 (by rfl) ⟨209078, by rfl⟩ : syracuseStep 4460341 = 418157) (by norm_num)
theorem B5287733 : Blo 1564980 5287733 := bbase (se 5 (by rfl) ⟨247862, by rfl⟩ : syracuseStep 5287733 = 495725) (by norm_num)
theorem B3764029 : Blo 1564980 3764029 := bbase (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) (by norm_num)
theorem B4763461 : Blo 1564980 4763461 := bbase (se 4 (by rfl) ⟨446574, by rfl⟩ : syracuseStep 4763461 = 893149) (by norm_num)
theorem B2641781 : Blo 1564980 2641781 := bbase (se 5 (by rfl) ⟨123833, by rfl⟩ : syracuseStep 2641781 = 247667) (by norm_num)
theorem B6352757 : Blo 1564980 6352757 := bbase (se 5 (by rfl) ⟨297785, by rfl⟩ : syracuseStep 6352757 = 595571) (by norm_num)
theorem B6352805 : Blo 1564980 6352805 := bbase (se 4 (by rfl) ⟨595575, by rfl⟩ : syracuseStep 6352805 = 1191151) (by norm_num)
theorem B4460501 : Blo 1564980 4460501 := bbase (se 7 (by rfl) ⟨52271, by rfl⟩ : syracuseStep 4460501 = 104543) (by norm_num)
theorem B2641909 : Blo 1564980 2641909 := bbase (se 5 (by rfl) ⟨123839, by rfl⟩ : syracuseStep 2641909 = 247679) (by norm_num)
theorem B2379773 : Blo 1564980 2379773 := bbase (se 3 (by rfl) ⟨446207, by rfl⟩ : syracuseStep 2379773 = 892415) (by norm_num)
theorem B6352901 : Blo 1564980 6352901 := bbase (se 4 (by rfl) ⟨595584, by rfl⟩ : syracuseStep 6352901 = 1191169) (by norm_num)
theorem B2641997 : Blo 1564980 2641997 := bbase (se 3 (by rfl) ⟨495374, by rfl⟩ : syracuseStep 2641997 = 990749) (by norm_num)
theorem B3346589 : Blo 1564980 3346589 := bbase (se 3 (by rfl) ⟨627485, by rfl⟩ : syracuseStep 3346589 = 1254971) (by norm_num)
theorem B4460741 : Blo 1564980 4460741 := bbase (se 4 (by rfl) ⟨418194, by rfl⟩ : syracuseStep 4460741 = 836389) (by norm_num)
theorem B2642125 : Blo 1564980 2642125 := bbase (se 3 (by rfl) ⟨495398, by rfl⟩ : syracuseStep 2642125 = 990797) (by norm_num)
theorem B12701909 : Blo 1564980 12701909 := bbase (se 7 (by rfl) ⟨148850, by rfl⟩ : syracuseStep 12701909 = 297701) (by norm_num)
theorem B4231397 : Blo 1564980 4231397 := bbase (se 4 (by rfl) ⟨396693, by rfl⟩ : syracuseStep 4231397 = 793387) (by norm_num)
theorem B5288165 : Blo 1564980 5288165 := bbase (se 4 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 5288165 = 991531) (by norm_num)
theorem B2642213 : Blo 1564980 2642213 := bbase (se 4 (by rfl) ⟨247707, by rfl⟩ : syracuseStep 2642213 = 495415) (by norm_num)
theorem B3764549 : Blo 1564980 3764549 := bbase (se 4 (by rfl) ⟨352926, by rfl⟩ : syracuseStep 3764549 = 705853) (by norm_num)
theorem B1880453 : Blo 1564980 1880453 := bbase (se 4 (by rfl) ⟨176292, by rfl⟩ : syracuseStep 1880453 = 352585) (by norm_num)
theorem B4460933 : Blo 1564980 4460933 := bbase (se 4 (by rfl) ⟨418212, by rfl⟩ : syracuseStep 4460933 = 836425) (by norm_num)
theorem B2642341 : Blo 1564980 2642341 := bbase (se 4 (by rfl) ⟨247719, by rfl⟩ : syracuseStep 2642341 = 495439) (by norm_num)
theorem B2347493 : Blo 1564980 2347493 := bbase (se 4 (by rfl) ⟨220077, by rfl⟩ : syracuseStep 2347493 = 440155) (by norm_num)
theorem B2347517 : Blo 1564980 2347517 := bbase (se 3 (by rfl) ⟨440159, by rfl⟩ : syracuseStep 2347517 = 880319) (by norm_num)
theorem B2642429 : Blo 1564980 2642429 := bbase (se 3 (by rfl) ⟨495455, by rfl⟩ : syracuseStep 2642429 = 990911) (by norm_num)
theorem B8040965 : Blo 1564980 8040965 := bbase (se 4 (by rfl) ⟨753840, by rfl⟩ : syracuseStep 8040965 = 1507681) (by norm_num)
theorem B2347541 : Blo 1564980 2347541 := bbase (se 6 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 2347541 = 110041) (by norm_num)
theorem B2347565 : Blo 1564980 2347565 := bbase (se 3 (by rfl) ⟨440168, by rfl⟩ : syracuseStep 2347565 = 880337) (by norm_num)
theorem B2347589 : Blo 1564980 2347589 := bbase (se 4 (by rfl) ⟨220086, by rfl⟩ : syracuseStep 2347589 = 440173) (by norm_num)
theorem B2347613 : Blo 1564980 2347613 := bbase (se 3 (by rfl) ⟨440177, by rfl⟩ : syracuseStep 2347613 = 880355) (by norm_num)
theorem B2347637 : Blo 1564980 2347637 := bbase (se 5 (by rfl) ⟨110045, by rfl⟩ : syracuseStep 2347637 = 220091) (by norm_num)
theorem B2642557 : Blo 1564980 2642557 := bbase (se 3 (by rfl) ⟨495479, by rfl⟩ : syracuseStep 2642557 = 990959) (by norm_num)
theorem B2347661 : Blo 1564980 2347661 := bbase (se 3 (by rfl) ⟨440186, by rfl⟩ : syracuseStep 2347661 = 880373) (by norm_num)
theorem B2347685 : Blo 1564980 2347685 := bbase (se 4 (by rfl) ⟨220095, by rfl⟩ : syracuseStep 2347685 = 440191) (by norm_num)
theorem B1880761 : Blo 1564980 1880761 := bbase (se 2 (by rfl) ⟨705285, by rfl⟩ : syracuseStep 1880761 = 1410571) (by norm_num)
theorem B2347709 : Blo 1564980 2347709 := bbase (se 3 (by rfl) ⟨440195, by rfl⟩ : syracuseStep 2347709 = 880391) (by norm_num)
theorem B3764933 : Blo 1564980 3764933 := bbase (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) (by norm_num)
theorem B2347733 : Blo 1564980 2347733 := bbase (se 7 (by rfl) ⟨27512, by rfl⟩ : syracuseStep 2347733 = 55025) (by norm_num)
theorem B2642645 : Blo 1564980 2642645 := bbase (se 7 (by rfl) ⟨30968, by rfl⟩ : syracuseStep 2642645 = 61937) (by norm_num)
theorem B2347757 : Blo 1564980 2347757 := bbase (se 3 (by rfl) ⟨440204, by rfl⟩ : syracuseStep 2347757 = 880409) (by norm_num)
theorem B3764981 : Blo 1564980 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B3764989 : Blo 1564980 3764989 := bbase (se 3 (by rfl) ⟨705935, by rfl⟩ : syracuseStep 3764989 = 1411871) (by norm_num)
theorem B2347781 : Blo 1564980 2347781 := bbase (se 4 (by rfl) ⟨220104, by rfl⟩ : syracuseStep 2347781 = 440209) (by norm_num)
theorem B2347805 : Blo 1564980 2347805 := bbase (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) (by norm_num)
theorem B2347829 : Blo 1564980 2347829 := bbase (se 5 (by rfl) ⟨110054, by rfl⟩ : syracuseStep 2347829 = 220109) (by norm_num)
theorem B3961669 : Blo 1564980 3961669 := bbase (se 4 (by rfl) ⟨371406, by rfl⟩ : syracuseStep 3961669 = 742813) (by norm_num)
theorem B2347853 : Blo 1564980 2347853 := bbase (se 3 (by rfl) ⟨440222, by rfl⟩ : syracuseStep 2347853 = 880445) (by norm_num)
theorem B2642773 : Blo 1564980 2642773 := bbase (se 9 (by rfl) ⟨7742, by rfl⟩ : syracuseStep 2642773 = 15485) (by norm_num)
theorem B2347877 : Blo 1564980 2347877 := bbase (se 4 (by rfl) ⟨220113, by rfl⟩ : syracuseStep 2347877 = 440227) (by norm_num)
theorem B2347901 : Blo 1564980 2347901 := bbase (se 3 (by rfl) ⟨440231, by rfl⟩ : syracuseStep 2347901 = 880463) (by norm_num)
theorem B2347925 : Blo 1564980 2347925 := bbase (se 6 (by rfl) ⟨55029, by rfl⟩ : syracuseStep 2347925 = 110059) (by norm_num)
theorem B2347949 : Blo 1564980 2347949 := bbase (se 3 (by rfl) ⟨440240, by rfl⟩ : syracuseStep 2347949 = 880481) (by norm_num)
theorem B2642861 : Blo 1564980 2642861 := bbase (se 3 (by rfl) ⟨495536, by rfl⟩ : syracuseStep 2642861 = 991073) (by norm_num)
theorem B3961781 : Blo 1564980 3961781 := bbase (se 5 (by rfl) ⟨185708, by rfl⟩ : syracuseStep 3961781 = 371417) (by norm_num)
theorem B2347973 : Blo 1564980 2347973 := bbase (se 4 (by rfl) ⟨220122, by rfl⟩ : syracuseStep 2347973 = 440245) (by norm_num)
theorem B2347997 : Blo 1564980 2347997 := bbase (se 3 (by rfl) ⟨440249, by rfl⟩ : syracuseStep 2347997 = 880499) (by norm_num)
theorem B2905069 : Blo 1564980 2905069 := bbase (se 3 (by rfl) ⟨544700, by rfl⟩ : syracuseStep 2905069 = 1089401) (by norm_num)
theorem B2348021 : Blo 1564980 2348021 := bbase (se 5 (by rfl) ⟨110063, by rfl⟩ : syracuseStep 2348021 = 220127) (by norm_num)
theorem B2348045 : Blo 1564980 2348045 := bbase (se 3 (by rfl) ⟨440258, by rfl⟩ : syracuseStep 2348045 = 880517) (by norm_num)
theorem B2348069 : Blo 1564980 2348069 := bbase (se 4 (by rfl) ⟨220131, by rfl⟩ : syracuseStep 2348069 = 440263) (by norm_num)
theorem B7926821 : Blo 1564980 7926821 := bbase (se 4 (by rfl) ⟨743139, by rfl⟩ : syracuseStep 7926821 = 1486279) (by norm_num)
theorem B2642989 : Blo 1564980 2642989 := bbase (se 3 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 2642989 = 991121) (by norm_num)
theorem B5944373 : Blo 1564980 5944373 := bbase (se 5 (by rfl) ⟨278642, by rfl⟩ : syracuseStep 5944373 = 557285) (by norm_num)
theorem B1881145 : Blo 1564980 1881145 := bbase (se 2 (by rfl) ⟨705429, by rfl⟩ : syracuseStep 1881145 = 1410859) (by norm_num)
theorem B2348093 : Blo 1564980 2348093 := bbase (se 3 (by rfl) ⟨440267, by rfl⟩ : syracuseStep 2348093 = 880535) (by norm_num)
theorem B1881149 : Blo 1564980 1881149 := bbase (se 3 (by rfl) ⟨352715, by rfl⟩ : syracuseStep 1881149 = 705431) (by norm_num)
theorem B3011653 : Blo 1564980 3011653 := bbase (se 4 (by rfl) ⟨282342, by rfl⟩ : syracuseStep 3011653 = 564685) (by norm_num)
theorem B2348117 : Blo 1564980 2348117 := bbase (se 8 (by rfl) ⟨13758, by rfl⟩ : syracuseStep 2348117 = 27517) (by norm_num)
theorem B4764773 : Blo 1564980 4764773 := bbase (se 4 (by rfl) ⟨446697, by rfl⟩ : syracuseStep 4764773 = 893395) (by norm_num)
theorem B2348141 : Blo 1564980 2348141 := bbase (se 3 (by rfl) ⟨440276, by rfl⟩ : syracuseStep 2348141 = 880553) (by norm_num)
theorem B3961973 : Blo 1564980 3961973 := bbase (se 5 (by rfl) ⟨185717, by rfl⟩ : syracuseStep 3961973 = 371435) (by norm_num)
theorem B2348165 : Blo 1564980 2348165 := bbase (se 4 (by rfl) ⟨220140, by rfl⟩ : syracuseStep 2348165 = 440281) (by norm_num)
theorem B2643077 : Blo 1564980 2643077 := bbase (se 4 (by rfl) ⟨247788, by rfl⟩ : syracuseStep 2643077 = 495577) (by norm_num)
theorem B2413709 : Blo 1564980 2413709 := bbase (se 3 (by rfl) ⟨452570, by rfl⟩ : syracuseStep 2413709 = 905141) (by norm_num)
theorem B2348189 : Blo 1564980 2348189 := bbase (se 3 (by rfl) ⟨440285, by rfl⟩ : syracuseStep 2348189 = 880571) (by norm_num)
theorem B2348213 : Blo 1564980 2348213 := bbase (se 5 (by rfl) ⟨110072, by rfl⟩ : syracuseStep 2348213 = 220145) (by norm_num)
theorem B2348237 : Blo 1564980 2348237 := bbase (se 3 (by rfl) ⟨440294, by rfl⟩ : syracuseStep 2348237 = 880589) (by norm_num)
theorem B33871061 : Blo 1564980 33871061 := bbase (se 7 (by rfl) ⟨396926, by rfl⟩ : syracuseStep 33871061 = 793853) (by norm_num)
theorem B2348261 : Blo 1564980 2348261 := bbase (se 4 (by rfl) ⟨220149, by rfl⟩ : syracuseStep 2348261 = 440299) (by norm_num)
theorem B2348285 : Blo 1564980 2348285 := bbase (se 3 (by rfl) ⟨440303, by rfl⟩ : syracuseStep 2348285 = 880607) (by norm_num)
theorem B2643205 : Blo 1564980 2643205 := bbase (se 4 (by rfl) ⟨247800, by rfl⟩ : syracuseStep 2643205 = 495601) (by norm_num)
theorem B5018885 : Blo 1564980 5018885 := bbase (se 4 (by rfl) ⟨470520, by rfl⟩ : syracuseStep 5018885 = 941041) (by norm_num)
theorem B2348309 : Blo 1564980 2348309 := bbase (se 6 (by rfl) ⟨55038, by rfl⟩ : syracuseStep 2348309 = 110077) (by norm_num)
theorem B4019477 : Blo 1564980 4019477 := bbase (se 6 (by rfl) ⟨94206, by rfl⟩ : syracuseStep 4019477 = 188413) (by norm_num)
theorem B2348333 : Blo 1564980 2348333 := bbase (se 3 (by rfl) ⟨440312, by rfl⟩ : syracuseStep 2348333 = 880625) (by norm_num)
theorem B10032437 : Blo 1564980 10032437 := bbase (se 5 (by rfl) ⟨470270, by rfl⟩ : syracuseStep 10032437 = 940541) (by norm_num)
theorem B2348357 : Blo 1564980 2348357 := bbase (se 4 (by rfl) ⟨220158, by rfl⟩ : syracuseStep 2348357 = 440317) (by norm_num)
theorem B5944661 : Blo 1564980 5944661 := bbase (se 13 (by rfl) ⟨1088, by rfl⟩ : syracuseStep 5944661 = 2177) (by norm_num)
theorem B2348381 : Blo 1564980 2348381 := bbase (se 3 (by rfl) ⟨440321, by rfl⟩ : syracuseStep 2348381 = 880643) (by norm_num)
theorem B2643293 : Blo 1564980 2643293 := bbase (se 3 (by rfl) ⟨495617, by rfl⟩ : syracuseStep 2643293 = 991235) (by norm_num)
theorem B4461925 : Blo 1564980 4461925 := bbase (se 4 (by rfl) ⟨418305, by rfl⟩ : syracuseStep 4461925 = 836611) (by norm_num)
theorem B5641589 : Blo 1564980 5641589 := bbase (se 5 (by rfl) ⟨264449, by rfl⟩ : syracuseStep 5641589 = 528899) (by norm_num)
theorem B2348405 : Blo 1564980 2348405 := bbase (se 5 (by rfl) ⟨110081, by rfl⟩ : syracuseStep 2348405 = 220163) (by norm_num)
theorem B2348429 : Blo 1564980 2348429 := bbase (se 3 (by rfl) ⟨440330, by rfl⟩ : syracuseStep 2348429 = 880661) (by norm_num)
theorem B8033701 : Blo 1564980 8033701 := bbase (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) (by norm_num)
theorem B2348453 : Blo 1564980 2348453 := bbase (se 4 (by rfl) ⟨220167, by rfl⟩ : syracuseStep 2348453 = 440335) (by norm_num)
theorem B3175861 : Blo 1564980 3175861 := bbase (se 5 (by rfl) ⟨148868, by rfl⟩ : syracuseStep 3175861 = 297737) (by norm_num)
theorem B2348477 : Blo 1564980 2348477 := bbase (se 3 (by rfl) ⟨440339, by rfl⟩ : syracuseStep 2348477 = 880679) (by norm_num)
theorem B3962317 : Blo 1564980 3962317 := bbase (se 3 (by rfl) ⟨742934, by rfl⟩ : syracuseStep 3962317 = 1485869) (by norm_num)
theorem B1881553 : Blo 1564980 1881553 := bbase (se 2 (by rfl) ⟨705582, by rfl⟩ : syracuseStep 1881553 = 1411165) (by norm_num)
theorem B2971093 : Blo 1564980 2971093 := bbase (se 7 (by rfl) ⟨34817, by rfl⟩ : syracuseStep 2971093 = 69635) (by norm_num)
theorem B2348501 : Blo 1564980 2348501 := bbase (se 7 (by rfl) ⟨27521, by rfl⟩ : syracuseStep 2348501 = 55043) (by norm_num)
theorem B2643421 : Blo 1564980 2643421 := bbase (se 3 (by rfl) ⟨495641, by rfl⟩ : syracuseStep 2643421 = 991283) (by norm_num)
theorem B2348525 : Blo 1564980 2348525 := bbase (se 3 (by rfl) ⟨440348, by rfl⟩ : syracuseStep 2348525 = 880697) (by norm_num)
theorem B2348549 : Blo 1564980 2348549 := bbase (se 4 (by rfl) ⟨220176, by rfl⟩ : syracuseStep 2348549 = 440353) (by norm_num)
theorem B2348573 : Blo 1564980 2348573 := bbase (se 3 (by rfl) ⟨440357, by rfl⟩ : syracuseStep 2348573 = 880715) (by norm_num)
theorem B2348597 : Blo 1564980 2348597 := bbase (se 5 (by rfl) ⟨110090, by rfl⟩ : syracuseStep 2348597 = 220181) (by norm_num)
theorem B2643509 : Blo 1564980 2643509 := bbase (se 5 (by rfl) ⟨123914, by rfl⟩ : syracuseStep 2643509 = 247829) (by norm_num)
theorem B3962429 : Blo 1564980 3962429 := bbase (se 3 (by rfl) ⟨742955, by rfl⟩ : syracuseStep 3962429 = 1485911) (by norm_num)
theorem B2348621 : Blo 1564980 2348621 := bbase (se 3 (by rfl) ⟨440366, by rfl⟩ : syracuseStep 2348621 = 880733) (by norm_num)
theorem B2971237 : Blo 1564980 2971237 := bbase (se 4 (by rfl) ⟨278553, by rfl⟩ : syracuseStep 2971237 = 557107) (by norm_num)
theorem B2348645 : Blo 1564980 2348645 := bbase (se 4 (by rfl) ⟨220185, by rfl⟩ : syracuseStep 2348645 = 440371) (by norm_num)
theorem B2348669 : Blo 1564980 2348669 := bbase (se 3 (by rfl) ⟨440375, by rfl⟩ : syracuseStep 2348669 = 880751) (by norm_num)
theorem B4232837 : Blo 1564980 4232837 := bbase (se 4 (by rfl) ⟨396828, by rfl⟩ : syracuseStep 4232837 = 793657) (by norm_num)
theorem B2348693 : Blo 1564980 2348693 := bbase (se 6 (by rfl) ⟨55047, by rfl⟩ : syracuseStep 2348693 = 110095) (by norm_num)
theorem B4019861 : Blo 1564980 4019861 := bbase (se 6 (by rfl) ⟨94215, by rfl⟩ : syracuseStep 4019861 = 188431) (by norm_num)
theorem B2348717 : Blo 1564980 2348717 := bbase (se 3 (by rfl) ⟨440384, by rfl⟩ : syracuseStep 2348717 = 880769) (by norm_num)
theorem B2643637 : Blo 1564980 2643637 := bbase (se 5 (by rfl) ⟨123920, by rfl⟩ : syracuseStep 2643637 = 247841) (by norm_num)
theorem B2348741 : Blo 1564980 2348741 := bbase (se 4 (by rfl) ⟨220194, by rfl⟩ : syracuseStep 2348741 = 440389) (by norm_num)
theorem B2348765 : Blo 1564980 2348765 := bbase (se 3 (by rfl) ⟨440393, by rfl⟩ : syracuseStep 2348765 = 880787) (by norm_num)
theorem B2348789 : Blo 1564980 2348789 := bbase (se 5 (by rfl) ⟨110099, by rfl⟩ : syracuseStep 2348789 = 220199) (by norm_num)
theorem B3962621 : Blo 1564980 3962621 := bbase (se 3 (by rfl) ⟨742991, by rfl⟩ : syracuseStep 3962621 = 1485983) (by norm_num)
theorem B2971397 : Blo 1564980 2971397 := bbase (se 4 (by rfl) ⟨278568, by rfl⟩ : syracuseStep 2971397 = 557137) (by norm_num)
theorem B2348813 : Blo 1564980 2348813 := bbase (se 3 (by rfl) ⟨440402, by rfl⟩ : syracuseStep 2348813 = 880805) (by norm_num)
theorem B2643725 : Blo 1564980 2643725 := bbase (se 3 (by rfl) ⟨495698, by rfl⟩ : syracuseStep 2643725 = 991397) (by norm_num)
theorem B12048149 : Blo 1564980 12048149 := bbase (se 6 (by rfl) ⟨282378, by rfl⟩ : syracuseStep 12048149 = 564757) (by norm_num)
theorem B28571413 : Blo 1564980 28571413 := bbase (se 6 (by rfl) ⟨669642, by rfl⟩ : syracuseStep 28571413 = 1339285) (by norm_num)
theorem B2348837 : Blo 1564980 2348837 := bbase (se 4 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 2348837 = 440407) (by norm_num)
theorem B2348861 : Blo 1564980 2348861 := bbase (se 3 (by rfl) ⟨440411, by rfl⟩ : syracuseStep 2348861 = 880823) (by norm_num)
theorem B3012437 : Blo 1564980 3012437 := bbase (se 9 (by rfl) ⟨8825, by rfl⟩ : syracuseStep 3012437 = 17651) (by norm_num)
theorem B2348885 : Blo 1564980 2348885 := bbase (se 9 (by rfl) ⟨6881, by rfl⟩ : syracuseStep 2348885 = 13763) (by norm_num)
theorem B2348909 : Blo 1564980 2348909 := bbase (se 3 (by rfl) ⟨440420, by rfl⟩ : syracuseStep 2348909 = 880841) (by norm_num)
theorem B2348933 : Blo 1564980 2348933 := bbase (se 4 (by rfl) ⟨220212, by rfl⟩ : syracuseStep 2348933 = 440425) (by norm_num)
theorem B2643853 : Blo 1564980 2643853 := bbase (se 3 (by rfl) ⟨495722, by rfl⟩ : syracuseStep 2643853 = 991445) (by norm_num)
theorem B2971541 : Blo 1564980 2971541 := bbase (se 6 (by rfl) ⟨69645, by rfl⟩ : syracuseStep 2971541 = 139291) (by norm_num)
theorem B2348957 : Blo 1564980 2348957 := bbase (se 3 (by rfl) ⟨440429, by rfl⟩ : syracuseStep 2348957 = 880859) (by norm_num)
theorem B2348981 : Blo 1564980 2348981 := bbase (se 5 (by rfl) ⟨110108, by rfl⟩ : syracuseStep 2348981 = 220217) (by norm_num)
theorem B2349005 : Blo 1564980 2349005 := bbase (se 3 (by rfl) ⟨440438, by rfl⟩ : syracuseStep 2349005 = 880877) (by norm_num)
theorem B22566869 : Blo 1564980 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B2349029 : Blo 1564980 2349029 := bbase (se 4 (by rfl) ⟨220221, by rfl⟩ : syracuseStep 2349029 = 440443) (by norm_num)
theorem B2381797 : Blo 1564980 2381797 := bbase (se 4 (by rfl) ⟨223293, by rfl⟩ : syracuseStep 2381797 = 446587) (by norm_num)
theorem B2643941 : Blo 1564980 2643941 := bbase (se 4 (by rfl) ⟨247869, by rfl⟩ : syracuseStep 2643941 = 495739) (by norm_num)
theorem B2349053 : Blo 1564980 2349053 := bbase (se 3 (by rfl) ⟨440447, by rfl⟩ : syracuseStep 2349053 = 880895) (by norm_num)
theorem B1906709 : Blo 1564980 1906709 := bbase (se 6 (by rfl) ⟨44688, by rfl⟩ : syracuseStep 1906709 = 89377) (by norm_num)
theorem B2349077 : Blo 1564980 2349077 := bbase (se 6 (by rfl) ⟨55056, by rfl⟩ : syracuseStep 2349077 = 110113) (by norm_num)
theorem B6690853 : Blo 1564980 6690853 := bbase (se 4 (by rfl) ⟨627267, by rfl⟩ : syracuseStep 6690853 = 1254535) (by norm_num)
theorem B2349101 : Blo 1564980 2349101 := bbase (se 3 (by rfl) ⟨440456, by rfl⟩ : syracuseStep 2349101 = 880913) (by norm_num)
theorem B2349125 : Blo 1564980 2349125 := bbase (se 4 (by rfl) ⟨220230, by rfl⟩ : syracuseStep 2349125 = 440461) (by norm_num)
theorem B3962965 : Blo 1564980 3962965 := bbase (se 8 (by rfl) ⟨23220, by rfl⟩ : syracuseStep 3962965 = 46441) (by norm_num)
theorem B2349149 : Blo 1564980 2349149 := bbase (se 3 (by rfl) ⟨440465, by rfl⟩ : syracuseStep 2349149 = 880931) (by norm_num)
theorem B2644069 : Blo 1564980 2644069 := bbase (se 4 (by rfl) ⟨247881, by rfl⟩ : syracuseStep 2644069 = 495763) (by norm_num)
theorem B1587317 : Blo 1564980 1587317 := bbase (se 5 (by rfl) ⟨74405, by rfl⟩ : syracuseStep 1587317 = 148811) (by norm_num)
theorem B2349173 : Blo 1564980 2349173 := bbase (se 5 (by rfl) ⟨110117, by rfl⟩ : syracuseStep 2349173 = 220235) (by norm_num)
theorem B2349197 : Blo 1564980 2349197 := bbase (se 3 (by rfl) ⟨440474, by rfl⟩ : syracuseStep 2349197 = 880949) (by norm_num)
theorem B2349221 : Blo 1564980 2349221 := bbase (se 4 (by rfl) ⟨220239, by rfl⟩ : syracuseStep 2349221 = 440479) (by norm_num)
theorem B2971829 : Blo 1564980 2971829 := bbase (se 5 (by rfl) ⟨139304, by rfl⟩ : syracuseStep 2971829 = 278609) (by norm_num)
theorem B2349245 : Blo 1564980 2349245 := bbase (se 3 (by rfl) ⟨440483, by rfl⟩ : syracuseStep 2349245 = 880967) (by norm_num)
theorem B2644157 : Blo 1564980 2644157 := bbase (se 3 (by rfl) ⟨495779, by rfl⟩ : syracuseStep 2644157 = 991559) (by norm_num)
theorem B3963077 : Blo 1564980 3963077 := bbase (se 4 (by rfl) ⟨371538, by rfl⟩ : syracuseStep 3963077 = 743077) (by norm_num)
theorem B2349269 : Blo 1564980 2349269 := bbase (se 7 (by rfl) ⟨27530, by rfl⟩ : syracuseStep 2349269 = 55061) (by norm_num)
theorem B13383893 : Blo 1564980 13383893 := bbase (se 7 (by rfl) ⟨156842, by rfl⟩ : syracuseStep 13383893 = 313685) (by norm_num)
theorem B2349293 : Blo 1564980 2349293 := bbase (se 3 (by rfl) ⟨440492, by rfl⟩ : syracuseStep 2349293 = 880985) (by norm_num)
theorem B3012869 : Blo 1564980 3012869 := bbase (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) (by norm_num)
theorem B2349317 : Blo 1564980 2349317 := bbase (se 4 (by rfl) ⟨220248, by rfl⟩ : syracuseStep 2349317 = 440497) (by norm_num)
theorem B2349341 : Blo 1564980 2349341 := bbase (se 3 (by rfl) ⟨440501, by rfl⟩ : syracuseStep 2349341 = 881003) (by norm_num)
theorem B1980713 : Blo 1564980 1980713 := bbase (se 2 (by rfl) ⟨742767, by rfl⟩ : syracuseStep 1980713 = 1485535) (by norm_num)
theorem B7928117 : Blo 1564980 7928117 := bbase (se 5 (by rfl) ⟨371630, by rfl⟩ : syracuseStep 7928117 = 743261) (by norm_num)
theorem B2349365 : Blo 1564980 2349365 := bbase (se 5 (by rfl) ⟨110126, by rfl⟩ : syracuseStep 2349365 = 220253) (by norm_num)
theorem B5282117 : Blo 1564980 5282117 := bbase (se 4 (by rfl) ⟨495198, by rfl⟩ : syracuseStep 5282117 = 990397) (by norm_num)
theorem B1587529 : Blo 1564980 1587529 := bbase (se 2 (by rfl) ⟨595323, by rfl⟩ : syracuseStep 1587529 = 1190647) (by norm_num)
theorem B2971981 : Blo 1564980 2971981 := bbase (se 3 (by rfl) ⟨557246, by rfl⟩ : syracuseStep 2971981 = 1114493) (by norm_num)
theorem B2349389 : Blo 1564980 2349389 := bbase (se 3 (by rfl) ⟨440510, by rfl⟩ : syracuseStep 2349389 = 881021) (by norm_num)
theorem B1980769 : Blo 1564980 1980769 := bbase (se 2 (by rfl) ⟨742788, by rfl⟩ : syracuseStep 1980769 = 1485577) (by norm_num)
theorem B2349413 : Blo 1564980 2349413 := bbase (se 4 (by rfl) ⟨220257, by rfl⟩ : syracuseStep 2349413 = 440515) (by norm_num)
theorem B2349437 : Blo 1564980 2349437 := bbase (se 3 (by rfl) ⟨440519, by rfl⟩ : syracuseStep 2349437 = 881039) (by norm_num)
theorem B3963269 : Blo 1564980 3963269 := bbase (se 4 (by rfl) ⟨371556, by rfl⟩ : syracuseStep 3963269 = 743113) (by norm_num)
theorem B7526789 : Blo 1564980 7526789 := bbase (se 4 (by rfl) ⟨705636, by rfl⟩ : syracuseStep 7526789 = 1411273) (by norm_num)
theorem B2349461 : Blo 1564980 2349461 := bbase (se 6 (by rfl) ⟨55065, by rfl⟩ : syracuseStep 2349461 = 110131) (by norm_num)
theorem B2349485 : Blo 1564980 2349485 := bbase (se 3 (by rfl) ⟨440528, by rfl⟩ : syracuseStep 2349485 = 881057) (by norm_num)
theorem B1980865 : Blo 1564980 1980865 := bbase (se 2 (by rfl) ⟨742824, by rfl⟩ : syracuseStep 1980865 = 1485649) (by norm_num)
theorem B2349509 : Blo 1564980 2349509 := bbase (se 4 (by rfl) ⟨220266, by rfl⟩ : syracuseStep 2349509 = 440533) (by norm_num)
theorem B2349533 : Blo 1564980 2349533 := bbase (se 3 (by rfl) ⟨440537, by rfl⟩ : syracuseStep 2349533 = 881075) (by norm_num)
theorem B5945845 : Blo 1564980 5945845 := bbase (se 5 (by rfl) ⟨278711, by rfl⟩ : syracuseStep 5945845 = 557423) (by norm_num)
theorem B2349557 : Blo 1564980 2349557 := bbase (se 5 (by rfl) ⟨110135, by rfl⟩ : syracuseStep 2349557 = 220271) (by norm_num)
theorem B2349581 : Blo 1564980 2349581 := bbase (se 3 (by rfl) ⟨440546, by rfl⟩ : syracuseStep 2349581 = 881093) (by norm_num)
theorem B2349605 : Blo 1564980 2349605 := bbase (se 4 (by rfl) ⟨220275, by rfl⟩ : syracuseStep 2349605 = 440551) (by norm_num)
theorem B2349629 : Blo 1564980 2349629 := bbase (se 3 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 2349629 = 881111) (by norm_num)
theorem B2349653 : Blo 1564980 2349653 := bbase (se 8 (by rfl) ⟨13767, by rfl⟩ : syracuseStep 2349653 = 27535) (by norm_num)
theorem B1981037 : Blo 1564980 1981037 := bbase (se 3 (by rfl) ⟨371444, by rfl⟩ : syracuseStep 1981037 = 742889) (by norm_num)
theorem B2349677 : Blo 1564980 2349677 := bbase (se 3 (by rfl) ⟨440564, by rfl⟩ : syracuseStep 2349677 = 881129) (by norm_num)
theorem B2972285 : Blo 1564980 2972285 := bbase (se 3 (by rfl) ⟨557303, by rfl⟩ : syracuseStep 2972285 = 1114607) (by norm_num)
theorem B2382461 : Blo 1564980 2382461 := bbase (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) (by norm_num)
theorem B2349701 : Blo 1564980 2349701 := bbase (se 4 (by rfl) ⟨220284, by rfl⟩ : syracuseStep 2349701 = 440569) (by norm_num)
theorem B2349725 : Blo 1564980 2349725 := bbase (se 3 (by rfl) ⟨440573, by rfl⟩ : syracuseStep 2349725 = 881147) (by norm_num)
theorem B1981093 : Blo 1564980 1981093 := bbase (se 4 (by rfl) ⟨185727, by rfl⟩ : syracuseStep 1981093 = 371455) (by norm_num)
theorem B2349749 : Blo 1564980 2349749 := bbase (se 5 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 2349749 = 220289) (by norm_num)
theorem B3521213 : Blo 1564980 3521213 := bbase (se 3 (by rfl) ⟨660227, by rfl⟩ : syracuseStep 3521213 = 1320455) (by norm_num)
theorem B2349773 : Blo 1564980 2349773 := bbase (se 3 (by rfl) ⟨440582, by rfl⟩ : syracuseStep 2349773 = 881165) (by norm_num)
theorem B3963613 : Blo 1564980 3963613 := bbase (se 3 (by rfl) ⟨743177, by rfl⟩ : syracuseStep 3963613 = 1486355) (by norm_num)
theorem B2349797 : Blo 1564980 2349797 := bbase (se 4 (by rfl) ⟨220293, by rfl⟩ : syracuseStep 2349797 = 440587) (by norm_num)
theorem B5282549 : Blo 1564980 5282549 := bbase (se 5 (by rfl) ⟨247619, by rfl⟩ : syracuseStep 5282549 = 495239) (by norm_num)
theorem B2349821 : Blo 1564980 2349821 := bbase (se 3 (by rfl) ⟨440591, by rfl⟩ : syracuseStep 2349821 = 881183) (by norm_num)
theorem B3521285 : Blo 1564980 3521285 := bbase (se 4 (by rfl) ⟨330120, by rfl⟩ : syracuseStep 3521285 = 660241) (by norm_num)
theorem B1981189 : Blo 1564980 1981189 := bbase (se 4 (by rfl) ⟨185736, by rfl⟩ : syracuseStep 1981189 = 371473) (by norm_num)
theorem B2349845 : Blo 1564980 2349845 := bbase (se 6 (by rfl) ⟨55074, by rfl⟩ : syracuseStep 2349845 = 110149) (by norm_num)
theorem B5946149 : Blo 1564980 5946149 := bbase (se 4 (by rfl) ⟨557451, by rfl⟩ : syracuseStep 5946149 = 1114903) (by norm_num)
theorem B2349869 : Blo 1564980 2349869 := bbase (se 3 (by rfl) ⟨440600, by rfl⟩ : syracuseStep 2349869 = 881201) (by norm_num)
theorem B2349893 : Blo 1564980 2349893 := bbase (se 4 (by rfl) ⟨220302, by rfl⟩ : syracuseStep 2349893 = 440605) (by norm_num)
theorem B3521357 : Blo 1564980 3521357 := bbase (se 3 (by rfl) ⟨660254, by rfl⟩ : syracuseStep 3521357 = 1320509) (by norm_num)
theorem B3963725 : Blo 1564980 3963725 := bbase (se 3 (by rfl) ⟨743198, by rfl⟩ : syracuseStep 3963725 = 1486397) (by norm_num)
theorem B2349917 : Blo 1564980 2349917 := bbase (se 3 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 2349917 = 881219) (by norm_num)
theorem B4291429 : Blo 1564980 4291429 := bbase (se 4 (by rfl) ⟨402321, by rfl⟩ : syracuseStep 4291429 = 804643) (by norm_num)
theorem B2349941 : Blo 1564980 2349941 := bbase (se 5 (by rfl) ⟨110153, by rfl⟩ : syracuseStep 2349941 = 220307) (by norm_num)
theorem B2349965 : Blo 1564980 2349965 := bbase (se 3 (by rfl) ⟨440618, by rfl⟩ : syracuseStep 2349965 = 881237) (by norm_num)
theorem B3521429 : Blo 1564980 3521429 := bbase (se 6 (by rfl) ⟨82533, by rfl⟩ : syracuseStep 3521429 = 165067) (by norm_num)
theorem B2349989 : Blo 1564980 2349989 := bbase (se 4 (by rfl) ⟨220311, by rfl⟩ : syracuseStep 2349989 = 440623) (by norm_num)
theorem B1981361 : Blo 1564980 1981361 := bbase (se 2 (by rfl) ⟨743010, by rfl⟩ : syracuseStep 1981361 = 1486021) (by norm_num)
theorem B1907645 : Blo 1564980 1907645 := bbase (se 3 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 1907645 = 715367) (by norm_num)
theorem B2350013 : Blo 1564980 2350013 := bbase (se 3 (by rfl) ⟨440627, by rfl⟩ : syracuseStep 2350013 = 881255) (by norm_num)
theorem B2350037 : Blo 1564980 2350037 := bbase (se 7 (by rfl) ⟨27539, by rfl⟩ : syracuseStep 2350037 = 55079) (by norm_num)
theorem B3521501 : Blo 1564980 3521501 := bbase (se 3 (by rfl) ⟨660281, by rfl⟩ : syracuseStep 3521501 = 1320563) (by norm_num)
theorem B1981417 : Blo 1564980 1981417 := bbase (se 2 (by rfl) ⟨743031, by rfl⟩ : syracuseStep 1981417 = 1486063) (by norm_num)
theorem B2350061 : Blo 1564980 2350061 := bbase (se 3 (by rfl) ⟨440636, by rfl⟩ : syracuseStep 2350061 = 881273) (by norm_num)
theorem B4234229 : Blo 1564980 4234229 := bbase (se 5 (by rfl) ⟨198479, by rfl⟩ : syracuseStep 4234229 = 396959) (by norm_num)
theorem B2350085 : Blo 1564980 2350085 := bbase (se 4 (by rfl) ⟨220320, by rfl⟩ : syracuseStep 2350085 = 440641) (by norm_num)
theorem B3963917 : Blo 1564980 3963917 := bbase (se 3 (by rfl) ⟨743234, by rfl⟩ : syracuseStep 3963917 = 1486469) (by norm_num)
theorem B2350109 : Blo 1564980 2350109 := bbase (se 3 (by rfl) ⟨440645, by rfl⟩ : syracuseStep 2350109 = 881291) (by norm_num)
theorem B3521573 : Blo 1564980 3521573 := bbase (se 4 (by rfl) ⟨330147, by rfl⟩ : syracuseStep 3521573 = 660295) (by norm_num)
theorem B3013669 : Blo 1564980 3013669 := bbase (se 4 (by rfl) ⟨282531, by rfl⟩ : syracuseStep 3013669 = 565063) (by norm_num)
theorem B2350133 : Blo 1564980 2350133 := bbase (se 5 (by rfl) ⟨110162, by rfl⟩ : syracuseStep 2350133 = 220325) (by norm_num)
theorem B1981513 : Blo 1564980 1981513 := bbase (se 2 (by rfl) ⟨743067, by rfl⟩ : syracuseStep 1981513 = 1486135) (by norm_num)
theorem B2350157 : Blo 1564980 2350157 := bbase (se 3 (by rfl) ⟨440654, by rfl⟩ : syracuseStep 2350157 = 881309) (by norm_num)
theorem B2350181 : Blo 1564980 2350181 := bbase (se 4 (by rfl) ⟨220329, by rfl⟩ : syracuseStep 2350181 = 440659) (by norm_num)
theorem B3521645 : Blo 1564980 3521645 := bbase (se 3 (by rfl) ⟨660308, by rfl⟩ : syracuseStep 3521645 = 1320617) (by norm_num)
theorem B11893877 : Blo 1564980 11893877 := bbase (se 5 (by rfl) ⟨557525, by rfl⟩ : syracuseStep 11893877 = 1115051) (by norm_num)
theorem B2350205 : Blo 1564980 2350205 := bbase (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) (by norm_num)
theorem B2350229 : Blo 1564980 2350229 := bbase (se 6 (by rfl) ⟨55083, by rfl⟩ : syracuseStep 2350229 = 110167) (by norm_num)
theorem B5282981 : Blo 1564980 5282981 := bbase (se 4 (by rfl) ⟨495279, by rfl⟩ : syracuseStep 5282981 = 990559) (by norm_num)
theorem B2350253 : Blo 1564980 2350253 := bbase (se 3 (by rfl) ⟨440672, by rfl⟩ : syracuseStep 2350253 = 881345) (by norm_num)
theorem B3521717 : Blo 1564980 3521717 := bbase (se 5 (by rfl) ⟨165080, by rfl⟩ : syracuseStep 3521717 = 330161) (by norm_num)
theorem B2350277 : Blo 1564980 2350277 := bbase (se 4 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 2350277 = 440677) (by norm_num)
theorem B2350301 : Blo 1564980 2350301 := bbase (se 3 (by rfl) ⟨440681, by rfl⟩ : syracuseStep 2350301 = 881363) (by norm_num)
theorem B6110437 : Blo 1564980 6110437 := bbase (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) (by norm_num)
theorem B1981685 : Blo 1564980 1981685 := bbase (se 5 (by rfl) ⟨92891, by rfl⟩ : syracuseStep 1981685 = 185783) (by norm_num)
theorem B2350325 : Blo 1564980 2350325 := bbase (se 5 (by rfl) ⟨110171, by rfl⟩ : syracuseStep 2350325 = 220343) (by norm_num)
theorem B3521789 : Blo 1564980 3521789 := bbase (se 3 (by rfl) ⟨660335, by rfl⟩ : syracuseStep 3521789 = 1320671) (by norm_num)
theorem B2350349 : Blo 1564980 2350349 := bbase (se 3 (by rfl) ⟨440690, by rfl⟩ : syracuseStep 2350349 = 881381) (by norm_num)
theorem B2350373 : Blo 1564980 2350373 := bbase (se 4 (by rfl) ⟨220347, by rfl⟩ : syracuseStep 2350373 = 440695) (by norm_num)
theorem B1981741 : Blo 1564980 1981741 := bbase (se 3 (by rfl) ⟨371576, by rfl⟩ : syracuseStep 1981741 = 743153) (by norm_num)
theorem B1785145 : Blo 1564980 1785145 := bbase (se 2 (by rfl) ⟨669429, by rfl⟩ : syracuseStep 1785145 = 1338859) (by norm_num)
theorem B2350397 : Blo 1564980 2350397 := bbase (se 3 (by rfl) ⟨440699, by rfl⟩ : syracuseStep 2350397 = 881399) (by norm_num)
theorem B3521861 : Blo 1564980 3521861 := bbase (se 4 (by rfl) ⟨330174, by rfl⟩ : syracuseStep 3521861 = 660349) (by norm_num)
theorem B2350421 : Blo 1564980 2350421 := bbase (se 11 (by rfl) ⟨1721, by rfl⟩ : syracuseStep 2350421 = 3443) (by norm_num)
theorem B1785181 : Blo 1564980 1785181 := bbase (se 3 (by rfl) ⟨334721, by rfl⟩ : syracuseStep 1785181 = 669443) (by norm_num)
theorem B3964261 : Blo 1564980 3964261 := bbase (se 4 (by rfl) ⟨371649, by rfl⟩ : syracuseStep 3964261 = 743299) (by norm_num)
theorem B2973037 : Blo 1564980 2973037 := bbase (se 3 (by rfl) ⟨557444, by rfl⟩ : syracuseStep 2973037 = 1114889) (by norm_num)
theorem B2350445 : Blo 1564980 2350445 := bbase (se 3 (by rfl) ⟨440708, by rfl⟩ : syracuseStep 2350445 = 881417) (by norm_num)
theorem B1760629 : Blo 1564980 1760629 := bbase (se 5 (by rfl) ⟨82529, by rfl⟩ : syracuseStep 1760629 = 165059) (by norm_num)
theorem B2350469 : Blo 1564980 2350469 := bbase (se 4 (by rfl) ⟨220356, by rfl⟩ : syracuseStep 2350469 = 440713) (by norm_num)
theorem B3521933 : Blo 1564980 3521933 := bbase (se 3 (by rfl) ⟨660362, by rfl⟩ : syracuseStep 3521933 = 1320725) (by norm_num)
theorem B1981837 : Blo 1564980 1981837 := bbase (se 3 (by rfl) ⟨371594, by rfl⟩ : syracuseStep 1981837 = 743189) (by norm_num)
theorem B1760665 : Blo 1564980 1760665 := bbase (se 2 (by rfl) ⟨660249, by rfl⟩ : syracuseStep 1760665 = 1320499) (by norm_num)
theorem B1760701 : Blo 1564980 1760701 := bbase (se 3 (by rfl) ⟨330131, by rfl⟩ : syracuseStep 1760701 = 660263) (by norm_num)
theorem B3522005 : Blo 1564980 3522005 := bbase (se 7 (by rfl) ⟨41273, by rfl⟩ : syracuseStep 3522005 = 82547) (by norm_num)
theorem B3964373 : Blo 1564980 3964373 := bbase (se 7 (by rfl) ⟨46457, by rfl⟩ : syracuseStep 3964373 = 92915) (by norm_num)
theorem B1760737 : Blo 1564980 1760737 := bbase (se 2 (by rfl) ⟨660276, by rfl⟩ : syracuseStep 1760737 = 1320553) (by norm_num)
theorem B6692341 : Blo 1564980 6692341 := bbase (se 5 (by rfl) ⟨313703, by rfl⟩ : syracuseStep 6692341 = 627407) (by norm_num)
theorem B2973181 : Blo 1564980 2973181 := bbase (se 3 (by rfl) ⟨557471, by rfl⟩ : syracuseStep 2973181 = 1114943) (by norm_num)
theorem B1760773 : Blo 1564980 1760773 := bbase (se 4 (by rfl) ⟨165072, by rfl⟩ : syracuseStep 1760773 = 330145) (by norm_num)
theorem B6692357 : Blo 1564980 6692357 := bbase (se 4 (by rfl) ⟨627408, by rfl⟩ : syracuseStep 6692357 = 1254817) (by norm_num)
theorem B11886101 : Blo 1564980 11886101 := bbase (se 6 (by rfl) ⟨278580, by rfl⟩ : syracuseStep 11886101 = 557161) (by norm_num)
theorem B3522077 : Blo 1564980 3522077 := bbase (se 3 (by rfl) ⟨660389, by rfl⟩ : syracuseStep 3522077 = 1320779) (by norm_num)
theorem B1760809 : Blo 1564980 1760809 := bbase (se 2 (by rfl) ⟨660303, by rfl⟩ : syracuseStep 1760809 = 1320607) (by norm_num)
theorem B1982009 : Blo 1564980 1982009 := bbase (se 2 (by rfl) ⟨743253, by rfl⟩ : syracuseStep 1982009 = 1486507) (by norm_num)
theorem B7929413 : Blo 1564980 7929413 := bbase (se 4 (by rfl) ⟨743382, by rfl⟩ : syracuseStep 7929413 = 1486765) (by norm_num)
theorem B1760845 : Blo 1564980 1760845 := bbase (se 3 (by rfl) ⟨330158, by rfl⟩ : syracuseStep 1760845 = 660317) (by norm_num)
theorem B5283413 : Blo 1564980 5283413 := bbase (se 8 (by rfl) ⟨30957, by rfl⟩ : syracuseStep 5283413 = 61915) (by norm_num)
theorem B3522149 : Blo 1564980 3522149 := bbase (se 4 (by rfl) ⟨330201, by rfl⟩ : syracuseStep 3522149 = 660403) (by norm_num)
theorem B1760881 : Blo 1564980 1760881 := bbase (se 2 (by rfl) ⟨660330, by rfl⟩ : syracuseStep 1760881 = 1320661) (by norm_num)
theorem B1982065 : Blo 1564980 1982065 := bbase (se 2 (by rfl) ⟨743274, by rfl⟩ : syracuseStep 1982065 = 1486549) (by norm_num)
theorem B5799557 : Blo 1564980 5799557 := bbase (se 4 (by rfl) ⟨543708, by rfl⟩ : syracuseStep 5799557 = 1087417) (by norm_num)
theorem B1760917 : Blo 1564980 1760917 := bbase (se 6 (by rfl) ⟨41271, by rfl⟩ : syracuseStep 1760917 = 82543) (by norm_num)
theorem B3964565 : Blo 1564980 3964565 := bbase (se 6 (by rfl) ⟨92919, by rfl⟩ : syracuseStep 3964565 = 185839) (by norm_num)
theorem B2973341 : Blo 1564980 2973341 := bbase (se 3 (by rfl) ⟨557501, by rfl⟩ : syracuseStep 2973341 = 1115003) (by norm_num)
theorem B3522221 : Blo 1564980 3522221 := bbase (se 3 (by rfl) ⟨660416, by rfl⟩ : syracuseStep 3522221 = 1320833) (by norm_num)
theorem B1760953 : Blo 1564980 1760953 := bbase (se 2 (by rfl) ⟨660357, by rfl⟩ : syracuseStep 1760953 = 1320715) (by norm_num)
theorem B7528133 : Blo 1564980 7528133 := bbase (se 4 (by rfl) ⟨705762, by rfl⟩ : syracuseStep 7528133 = 1411525) (by norm_num)
theorem B1982161 : Blo 1564980 1982161 := bbase (se 2 (by rfl) ⟨743310, by rfl⟩ : syracuseStep 1982161 = 1486621) (by norm_num)
theorem B1760989 : Blo 1564980 1760989 := bbase (se 3 (by rfl) ⟨330185, by rfl⟩ : syracuseStep 1760989 = 660371) (by norm_num)
theorem B3522293 : Blo 1564980 3522293 := bbase (se 5 (by rfl) ⟨165107, by rfl⟩ : syracuseStep 3522293 = 330215) (by norm_num)
theorem B1761025 : Blo 1564980 1761025 := bbase (se 2 (by rfl) ⟨660384, by rfl⟩ : syracuseStep 1761025 = 1320769) (by norm_num)
theorem B1761061 : Blo 1564980 1761061 := bbase (se 4 (by rfl) ⟨165099, by rfl⟩ : syracuseStep 1761061 = 330199) (by norm_num)
theorem B2973485 : Blo 1564980 2973485 := bbase (se 3 (by rfl) ⟨557528, by rfl⟩ : syracuseStep 2973485 = 1115057) (by norm_num)
theorem B7143221 : Blo 1564980 7143221 := bbase (se 5 (by rfl) ⟨334838, by rfl⟩ : syracuseStep 7143221 = 669677) (by norm_num)
theorem B3522365 : Blo 1564980 3522365 := bbase (se 3 (by rfl) ⟨660443, by rfl⟩ : syracuseStep 3522365 = 1320887) (by norm_num)
theorem B1695553 : Blo 1564980 1695553 := bbase (se 2 (by rfl) ⟨635832, by rfl⟩ : syracuseStep 1695553 = 1271665) (by norm_num)
theorem B1761097 : Blo 1564980 1761097 := bbase (se 2 (by rfl) ⟨660411, by rfl⟩ : syracuseStep 1761097 = 1320823) (by norm_num)
theorem B1761133 : Blo 1564980 1761133 := bbase (se 3 (by rfl) ⟨330212, by rfl⟩ : syracuseStep 1761133 = 660425) (by norm_num)
theorem B1982333 : Blo 1564980 1982333 := bbase (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) (by norm_num)
theorem B3522437 : Blo 1564980 3522437 := bbase (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) (by norm_num)
theorem B1761169 : Blo 1564980 1761169 := bbase (se 2 (by rfl) ⟨660438, by rfl⟩ : syracuseStep 1761169 = 1320877) (by norm_num)
theorem B1761205 : Blo 1564980 1761205 := bbase (se 5 (by rfl) ⟨82556, by rfl⟩ : syracuseStep 1761205 = 165113) (by norm_num)
theorem B1982389 : Blo 1564980 1982389 := bbase (se 5 (by rfl) ⟨92924, by rfl⟩ : syracuseStep 1982389 = 185849) (by norm_num)
theorem B3522509 : Blo 1564980 3522509 := bbase (se 3 (by rfl) ⟨660470, by rfl⟩ : syracuseStep 3522509 = 1320941) (by norm_num)
theorem B1761241 : Blo 1564980 1761241 := bbase (se 2 (by rfl) ⟨660465, by rfl⟩ : syracuseStep 1761241 = 1320931) (by norm_num)
theorem B5717989 : Blo 1564980 5717989 := bbase (se 4 (by rfl) ⟨536061, by rfl⟩ : syracuseStep 5717989 = 1072123) (by norm_num)
theorem B3964909 : Blo 1564980 3964909 := bbase (se 3 (by rfl) ⟨743420, by rfl⟩ : syracuseStep 3964909 = 1486841) (by norm_num)
theorem B1761277 : Blo 1564980 1761277 := bbase (se 3 (by rfl) ⟨330239, by rfl⟩ : syracuseStep 1761277 = 660479) (by norm_num)
theorem B3522563 : Blo 1564980 3522563 := bstep (se 1 (by rfl) ⟨2641922, by rfl⟩ : syracuseStep 3522563 = 5283845) B5283845
theorem B4235267 : Blo 1564980 4235267 := bstep (se 1 (by rfl) ⟨3176450, by rfl⟩ : syracuseStep 4235267 = 6352901) B6352901
theorem B8921137 : Blo 1564980 8921137 := bstep (se 2 (by rfl) ⟨3345426, by rfl⟩ : syracuseStep 8921137 = 6690853) B6690853
theorem B1761331 : Blo 1564980 1761331 := bstep (se 1 (by rfl) ⟨1320998, by rfl⟩ : syracuseStep 1761331 = 2641997) B2641997
theorem B5283953 : Blo 1564980 5283953 := bstep (se 2 (by rfl) ⟨1981482, by rfl⟩ : syracuseStep 5283953 = 3962965) B3962965
theorem B2973827 : Blo 1564980 2973827 := bstep (se 1 (by rfl) ⟨2230370, by rfl⟩ : syracuseStep 2973827 = 4460741) B4460741
theorem B1761475 : Blo 1564980 1761475 := bstep (se 1 (by rfl) ⟨1321106, by rfl⟩ : syracuseStep 1761475 = 2642213) B2642213
theorem B16072901 : Blo 1564980 16072901 := bstep (se 4 (by rfl) ⟨1506834, by rfl⟩ : syracuseStep 16072901 = 3013669) B3013669
theorem B7930061 : Blo 1564980 7930061 := bstep (se 3 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 7930061 = 2973773) B2973773
theorem B2506963 : Blo 1564980 2506963 := bstep (se 1 (by rfl) ⟨1880222, by rfl⟩ : syracuseStep 2506963 = 3760445) B3760445
theorem B3522833 : Blo 1564980 3522833 := bstep (se 2 (by rfl) ⟨1321062, by rfl⟩ : syracuseStep 3522833 = 2642125) B2642125
theorem B3522851 : Blo 1564980 3522851 := bstep (se 1 (by rfl) ⟨2642138, by rfl⟩ : syracuseStep 3522851 = 5284277) B5284277
theorem B10027313 : Blo 1564980 10027313 := bstep (se 2 (by rfl) ⟨3760242, by rfl⟩ : syracuseStep 10027313 = 7520485) B7520485
theorem B3965233 : Blo 1564980 3965233 := bstep (se 2 (by rfl) ⟨1486962, by rfl⟩ : syracuseStep 3965233 = 2973925) B2973925
theorem B1564995 : Blo 1564980 1564995 := bstep (se 1 (by rfl) ⟨1173746, by rfl⟩ : syracuseStep 1564995 = 2347493) B2347493
theorem B1565011 : Blo 1564980 1565011 := bstep (se 1 (by rfl) ⟨1173758, by rfl⟩ : syracuseStep 1565011 = 2347517) B2347517
theorem B1761619 : Blo 1564980 1761619 := bstep (se 1 (by rfl) ⟨1321214, by rfl⟩ : syracuseStep 1761619 = 2642429) B2642429
theorem B1565027 : Blo 1564980 1565027 := bstep (se 1 (by rfl) ⟨1173770, by rfl⟩ : syracuseStep 1565027 = 2347541) B2347541
theorem B1982819 : Blo 1564980 1982819 := bstep (se 1 (by rfl) ⟨1487114, by rfl⟩ : syracuseStep 1982819 = 2974229) B2974229
theorem B1565043 : Blo 1564980 1565043 := bstep (se 1 (by rfl) ⟨1173782, by rfl⟩ : syracuseStep 1565043 = 2347565) B2347565
theorem B1565059 : Blo 1564980 1565059 := bstep (se 1 (by rfl) ⟨1173794, by rfl⟩ : syracuseStep 1565059 = 2347589) B2347589
theorem B5947789 : Blo 1564980 5947789 := bstep (se 3 (by rfl) ⟨1115210, by rfl⟩ : syracuseStep 5947789 = 2230421) B2230421
theorem B1565075 : Blo 1564980 1565075 := bstep (se 1 (by rfl) ⟨1173806, by rfl⟩ : syracuseStep 1565075 = 2347613) B2347613
theorem B1565091 : Blo 1564980 1565091 := bstep (se 1 (by rfl) ⟨1173818, by rfl⟩ : syracuseStep 1565091 = 2347637) B2347637
theorem B5013937 : Blo 1564980 5013937 := bstep (se 2 (by rfl) ⟨1880226, by rfl⟩ : syracuseStep 5013937 = 3760453) B3760453
theorem B1565107 : Blo 1564980 1565107 := bstep (se 1 (by rfl) ⟨1173830, by rfl⟩ : syracuseStep 1565107 = 2347661) B2347661
theorem B1565123 : Blo 1564980 1565123 := bstep (se 1 (by rfl) ⟨1173842, by rfl⟩ : syracuseStep 1565123 = 2347685) B2347685
theorem B1565139 : Blo 1564980 1565139 := bstep (se 1 (by rfl) ⟨1173854, by rfl⟩ : syracuseStep 1565139 = 2347709) B2347709
theorem B1565155 : Blo 1564980 1565155 := bstep (se 1 (by rfl) ⟨1173866, by rfl⟩ : syracuseStep 1565155 = 2347733) B2347733
theorem B1761763 : Blo 1564980 1761763 := bstep (se 1 (by rfl) ⟨1321322, by rfl⟩ : syracuseStep 1761763 = 2642645) B2642645
theorem B1565171 : Blo 1564980 1565171 := bstep (se 1 (by rfl) ⟨1173878, by rfl⟩ : syracuseStep 1565171 = 2347757) B2347757
theorem B1565187 : Blo 1564980 1565187 := bstep (se 1 (by rfl) ⟨1173890, by rfl⟩ : syracuseStep 1565187 = 2347781) B2347781
theorem B1565203 : Blo 1564980 1565203 := bstep (se 1 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 1565203 = 2347805) B2347805
theorem B1565219 : Blo 1564980 1565219 := bstep (se 1 (by rfl) ⟨1173914, by rfl⟩ : syracuseStep 1565219 = 2347829) B2347829
theorem B3523121 : Blo 1564980 3523121 := bstep (se 2 (by rfl) ⟨1321170, by rfl⟩ : syracuseStep 3523121 = 2642341) B2642341
theorem B1565235 : Blo 1564980 1565235 := bstep (se 1 (by rfl) ⟨1173926, by rfl⟩ : syracuseStep 1565235 = 2347853) B2347853
theorem B1565251 : Blo 1564980 1565251 := bstep (se 1 (by rfl) ⟨1173938, by rfl⟩ : syracuseStep 1565251 = 2347877) B2347877
theorem B3523139 : Blo 1564980 3523139 := bstep (se 1 (by rfl) ⟨2642354, by rfl⟩ : syracuseStep 3523139 = 5284709) B5284709
theorem B3965507 : Blo 1564980 3965507 := bstep (se 1 (by rfl) ⟨2974130, by rfl⟩ : syracuseStep 3965507 = 5948261) B5948261
theorem B1565267 : Blo 1564980 1565267 := bstep (se 1 (by rfl) ⟨1173950, by rfl⟩ : syracuseStep 1565267 = 2347901) B2347901
theorem B1565283 : Blo 1564980 1565283 := bstep (se 1 (by rfl) ⟨1173962, by rfl⟩ : syracuseStep 1565283 = 2347925) B2347925
theorem B1565299 : Blo 1564980 1565299 := bstep (se 1 (by rfl) ⟨1173974, by rfl⟩ : syracuseStep 1565299 = 2347949) B2347949
theorem B1761907 : Blo 1564980 1761907 := bstep (se 1 (by rfl) ⟨1321430, by rfl⟩ : syracuseStep 1761907 = 2642861) B2642861
theorem B1565315 : Blo 1564980 1565315 := bstep (se 1 (by rfl) ⟨1173986, by rfl⟩ : syracuseStep 1565315 = 2347973) B2347973
theorem B5284493 : Blo 1564980 5284493 := bstep (se 3 (by rfl) ⟨990842, by rfl⟩ : syracuseStep 5284493 = 1981685) B1981685
theorem B1565331 : Blo 1564980 1565331 := bstep (se 1 (by rfl) ⟨1173998, by rfl⟩ : syracuseStep 1565331 = 2347997) B2347997
theorem B1565347 : Blo 1564980 1565347 := bstep (se 1 (by rfl) ⟨1174010, by rfl⟩ : syracuseStep 1565347 = 2348021) B2348021
theorem B1565363 : Blo 1564980 1565363 := bstep (se 1 (by rfl) ⟨1174022, by rfl⟩ : syracuseStep 1565363 = 2348045) B2348045
theorem B1671859 : Blo 1564980 1671859 := bstep (se 1 (by rfl) ⟨1253894, by rfl⟩ : syracuseStep 1671859 = 2507789) B2507789
theorem B1565379 : Blo 1564980 1565379 := bstep (se 1 (by rfl) ⟨1174034, by rfl⟩ : syracuseStep 1565379 = 2348069) B2348069
theorem B5284547 : Blo 1564980 5284547 := bstep (se 1 (by rfl) ⟨3963410, by rfl⟩ : syracuseStep 5284547 = 7926821) B7926821
theorem B1565395 : Blo 1564980 1565395 := bstep (se 1 (by rfl) ⟨1174046, by rfl⟩ : syracuseStep 1565395 = 2348093) B2348093
theorem B1565411 : Blo 1564980 1565411 := bstep (se 1 (by rfl) ⟨1174058, by rfl⟩ : syracuseStep 1565411 = 2348117) B2348117
theorem B2228963 : Blo 1564980 2228963 := bstep (se 1 (by rfl) ⟨1671722, by rfl⟩ : syracuseStep 2228963 = 3343445) B3343445
theorem B4457197 : Blo 1564980 4457197 := bstep (se 3 (by rfl) ⟨835724, by rfl⟩ : syracuseStep 4457197 = 1671449) B1671449
theorem B1565427 : Blo 1564980 1565427 := bstep (se 1 (by rfl) ⟨1174070, by rfl⟩ : syracuseStep 1565427 = 2348141) B2348141
theorem B1565443 : Blo 1564980 1565443 := bstep (se 1 (by rfl) ⟨1174082, by rfl⟩ : syracuseStep 1565443 = 2348165) B2348165
theorem B1762051 : Blo 1564980 1762051 := bstep (se 1 (by rfl) ⟨1321538, by rfl⟩ : syracuseStep 1762051 = 2643077) B2643077
theorem B3965699 : Blo 1564980 3965699 := bstep (se 1 (by rfl) ⟨2974274, by rfl⟩ : syracuseStep 3965699 = 5948549) B5948549
theorem B1565459 : Blo 1564980 1565459 := bstep (se 1 (by rfl) ⟨1174094, by rfl⟩ : syracuseStep 1565459 = 2348189) B2348189
theorem B7521059 : Blo 1564980 7521059 := bstep (se 1 (by rfl) ⟨5640794, by rfl⟩ : syracuseStep 7521059 = 11281589) B11281589
theorem B1565475 : Blo 1564980 1565475 := bstep (se 1 (by rfl) ⟨1174106, by rfl⟩ : syracuseStep 1565475 = 2348213) B2348213
theorem B1565491 : Blo 1564980 1565491 := bstep (se 1 (by rfl) ⟨1174118, by rfl⟩ : syracuseStep 1565491 = 2348237) B2348237
theorem B21439285 : Blo 1564980 21439285 := bstep (se 5 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 21439285 = 2009933) B2009933
theorem B1565507 : Blo 1564980 1565507 := bstep (se 1 (by rfl) ⟨1174130, by rfl⟩ : syracuseStep 1565507 = 2348261) B2348261
theorem B3523409 : Blo 1564980 3523409 := bstep (se 2 (by rfl) ⟨1321278, by rfl⟩ : syracuseStep 3523409 = 2642557) B2642557
theorem B1565523 : Blo 1564980 1565523 := bstep (se 1 (by rfl) ⟨1174142, by rfl⟩ : syracuseStep 1565523 = 2348285) B2348285
theorem B1565539 : Blo 1564980 1565539 := bstep (se 1 (by rfl) ⟨1174154, by rfl⟩ : syracuseStep 1565539 = 2348309) B2348309
theorem B3523427 : Blo 1564980 3523427 := bstep (se 1 (by rfl) ⟨2642570, by rfl⟩ : syracuseStep 3523427 = 5285141) B5285141
theorem B3572579 : Blo 1564980 3572579 := bstep (se 1 (by rfl) ⟨2679434, by rfl⟩ : syracuseStep 3572579 = 5358869) B5358869
theorem B2507635 : Blo 1564980 2507635 := bstep (se 1 (by rfl) ⟨1880726, by rfl⟩ : syracuseStep 2507635 = 3761453) B3761453
theorem B1565555 : Blo 1564980 1565555 := bstep (se 1 (by rfl) ⟨1174166, by rfl⟩ : syracuseStep 1565555 = 2348333) B2348333
theorem B1565571 : Blo 1564980 1565571 := bstep (se 1 (by rfl) ⟨1174178, by rfl⟩ : syracuseStep 1565571 = 2348357) B2348357
theorem B1565587 : Blo 1564980 1565587 := bstep (se 1 (by rfl) ⟨1174190, by rfl⟩ : syracuseStep 1565587 = 2348381) B2348381
theorem B1762195 : Blo 1564980 1762195 := bstep (se 1 (by rfl) ⟨1321646, by rfl⟩ : syracuseStep 1762195 = 2643293) B2643293
theorem B2507681 : Blo 1564980 2507681 := bstep (se 2 (by rfl) ⟨940380, by rfl⟩ : syracuseStep 2507681 = 1880761) B1880761
theorem B1565603 : Blo 1564980 1565603 := bstep (se 1 (by rfl) ⟨1174202, by rfl⟩ : syracuseStep 1565603 = 2348405) B2348405
theorem B1565619 : Blo 1564980 1565619 := bstep (se 1 (by rfl) ⟨1174214, by rfl⟩ : syracuseStep 1565619 = 2348429) B2348429
theorem B1565635 : Blo 1564980 1565635 := bstep (se 1 (by rfl) ⟨1174226, by rfl⟩ : syracuseStep 1565635 = 2348453) B2348453
theorem B4457425 : Blo 1564980 4457425 := bstep (se 2 (by rfl) ⟨1671534, by rfl⟩ : syracuseStep 4457425 = 3343069) B3343069
theorem B5284817 : Blo 1564980 5284817 := bstep (se 2 (by rfl) ⟨1981806, by rfl⟩ : syracuseStep 5284817 = 3963613) B3963613
theorem B1565651 : Blo 1564980 1565651 := bstep (se 1 (by rfl) ⟨1174238, by rfl⟩ : syracuseStep 1565651 = 2348477) B2348477
theorem B1565667 : Blo 1564980 1565667 := bstep (se 1 (by rfl) ⟨1174250, by rfl⟩ : syracuseStep 1565667 = 2348501) B2348501
theorem B1565683 : Blo 1564980 1565683 := bstep (se 1 (by rfl) ⟨1174262, by rfl⟩ : syracuseStep 1565683 = 2348525) B2348525
theorem B1565699 : Blo 1564980 1565699 := bstep (se 1 (by rfl) ⟨1174274, by rfl⟩ : syracuseStep 1565699 = 2348549) B2348549
theorem B5014541 : Blo 1564980 5014541 := bstep (se 3 (by rfl) ⟨940226, by rfl⟩ : syracuseStep 5014541 = 1880453) B1880453
theorem B11895821 : Blo 1564980 11895821 := bstep (se 3 (by rfl) ⟨2230466, by rfl⟩ : syracuseStep 11895821 = 4460933) B4460933
theorem B1565715 : Blo 1564980 1565715 := bstep (se 1 (by rfl) ⟨1174286, by rfl⟩ : syracuseStep 1565715 = 2348573) B2348573
theorem B1565731 : Blo 1564980 1565731 := bstep (se 1 (by rfl) ⟨1174298, by rfl⟩ : syracuseStep 1565731 = 2348597) B2348597
theorem B1762339 : Blo 1564980 1762339 := bstep (se 1 (by rfl) ⟨1321754, by rfl⟩ : syracuseStep 1762339 = 2643509) B2643509
theorem B1565747 : Blo 1564980 1565747 := bstep (se 1 (by rfl) ⟨1174310, by rfl⟩ : syracuseStep 1565747 = 2348621) B2348621
theorem B1565763 : Blo 1564980 1565763 := bstep (se 1 (by rfl) ⟨1174322, by rfl⟩ : syracuseStep 1565763 = 2348645) B2348645
theorem B1565779 : Blo 1564980 1565779 := bstep (se 1 (by rfl) ⟨1174334, by rfl⟩ : syracuseStep 1565779 = 2348669) B2348669
theorem B1565795 : Blo 1564980 1565795 := bstep (se 1 (by rfl) ⟨1174346, by rfl⟩ : syracuseStep 1565795 = 2348693) B2348693
theorem B2679907 : Blo 1564980 2679907 := bstep (se 1 (by rfl) ⟨2009930, by rfl⟩ : syracuseStep 2679907 = 4019861) B4019861
theorem B4457585 : Blo 1564980 4457585 := bstep (se 2 (by rfl) ⟨1671594, by rfl⟩ : syracuseStep 4457585 = 3343189) B3343189
theorem B3523697 : Blo 1564980 3523697 := bstep (se 2 (by rfl) ⟨1321386, by rfl⟩ : syracuseStep 3523697 = 2642773) B2642773
theorem B1565811 : Blo 1564980 1565811 := bstep (se 1 (by rfl) ⟨1174358, by rfl⟩ : syracuseStep 1565811 = 2348717) B2348717
theorem B1565827 : Blo 1564980 1565827 := bstep (se 1 (by rfl) ⟨1174370, by rfl⟩ : syracuseStep 1565827 = 2348741) B2348741
theorem B3523715 : Blo 1564980 3523715 := bstep (se 1 (by rfl) ⟨2642786, by rfl⟩ : syracuseStep 3523715 = 5285573) B5285573
theorem B12698765 : Blo 1564980 12698765 := bstep (se 3 (by rfl) ⟨2381018, by rfl⟩ : syracuseStep 12698765 = 4762037) B4762037
theorem B1565843 : Blo 1564980 1565843 := bstep (se 1 (by rfl) ⟨1174382, by rfl⟩ : syracuseStep 1565843 = 2348765) B2348765
theorem B1565859 : Blo 1564980 1565859 := bstep (se 1 (by rfl) ⟨1174394, by rfl⟩ : syracuseStep 1565859 = 2348789) B2348789
theorem B5948579 : Blo 1564980 5948579 := bstep (se 1 (by rfl) ⟨4461434, by rfl⟩ : syracuseStep 5948579 = 8922869) B8922869
theorem B1565875 : Blo 1564980 1565875 := bstep (se 1 (by rfl) ⟨1174406, by rfl⟩ : syracuseStep 1565875 = 2348813) B2348813
theorem B1762483 : Blo 1564980 1762483 := bstep (se 1 (by rfl) ⟨1321862, by rfl⟩ : syracuseStep 1762483 = 2643725) B2643725
theorem B1565891 : Blo 1564980 1565891 := bstep (se 1 (by rfl) ⟨1174418, by rfl⟩ : syracuseStep 1565891 = 2348837) B2348837
theorem B1565907 : Blo 1564980 1565907 := bstep (se 1 (by rfl) ⟨1174430, by rfl⟩ : syracuseStep 1565907 = 2348861) B2348861
theorem B4457699 : Blo 1564980 4457699 := bstep (se 1 (by rfl) ⟨3343274, by rfl⟩ : syracuseStep 4457699 = 6686549) B6686549
theorem B1565923 : Blo 1564980 1565923 := bstep (se 1 (by rfl) ⟨1174442, by rfl⟩ : syracuseStep 1565923 = 2348885) B2348885
theorem B1565939 : Blo 1564980 1565939 := bstep (se 1 (by rfl) ⟨1174454, by rfl⟩ : syracuseStep 1565939 = 2348909) B2348909
theorem B1565955 : Blo 1564980 1565955 := bstep (se 1 (by rfl) ⟨1174466, by rfl⟩ : syracuseStep 1565955 = 2348933) B2348933
theorem B1565971 : Blo 1564980 1565971 := bstep (se 1 (by rfl) ⟨1174478, by rfl⟩ : syracuseStep 1565971 = 2348957) B2348957
theorem B1565987 : Blo 1564980 1565987 := bstep (se 1 (by rfl) ⟨1174490, by rfl⟩ : syracuseStep 1565987 = 2348981) B2348981
theorem B1672483 : Blo 1564980 1672483 := bstep (se 1 (by rfl) ⟨1254362, by rfl⟩ : syracuseStep 1672483 = 2508725) B2508725
theorem B1566003 : Blo 1564980 1566003 := bstep (se 1 (by rfl) ⟨1174502, by rfl⟩ : syracuseStep 1566003 = 2349005) B2349005
theorem B1566019 : Blo 1564980 1566019 := bstep (se 1 (by rfl) ⟨1174514, by rfl⟩ : syracuseStep 1566019 = 2349029) B2349029
theorem B1762627 : Blo 1564980 1762627 := bstep (se 1 (by rfl) ⟨1321970, by rfl⟩ : syracuseStep 1762627 = 2643941) B2643941
theorem B1566035 : Blo 1564980 1566035 := bstep (se 1 (by rfl) ⟨1174526, by rfl⟩ : syracuseStep 1566035 = 2349053) B2349053
theorem B2229601 : Blo 1564980 2229601 := bstep (se 2 (by rfl) ⟨836100, by rfl⟩ : syracuseStep 2229601 = 1672201) B1672201
theorem B10028387 : Blo 1564980 10028387 := bstep (se 1 (by rfl) ⟨7521290, by rfl⟩ : syracuseStep 10028387 = 15042581) B15042581
theorem B1566051 : Blo 1564980 1566051 := bstep (se 1 (by rfl) ⟨1174538, by rfl⟩ : syracuseStep 1566051 = 2349077) B2349077
theorem B1566067 : Blo 1564980 1566067 := bstep (se 1 (by rfl) ⟨1174550, by rfl⟩ : syracuseStep 1566067 = 2349101) B2349101
theorem B1566083 : Blo 1564980 1566083 := bstep (se 1 (by rfl) ⟨1174562, by rfl⟩ : syracuseStep 1566083 = 2349125) B2349125
theorem B3523985 : Blo 1564980 3523985 := bstep (se 2 (by rfl) ⟨1321494, by rfl⟩ : syracuseStep 3523985 = 2642989) B2642989
theorem B1566099 : Blo 1564980 1566099 := bstep (se 1 (by rfl) ⟨1174574, by rfl⟩ : syracuseStep 1566099 = 2349149) B2349149
theorem B2508193 : Blo 1564980 2508193 := bstep (se 2 (by rfl) ⟨940572, by rfl⟩ : syracuseStep 2508193 = 1881145) B1881145
theorem B1566115 : Blo 1564980 1566115 := bstep (se 1 (by rfl) ⟨1174586, by rfl⟩ : syracuseStep 1566115 = 2349173) B2349173
theorem B3524003 : Blo 1564980 3524003 := bstep (se 1 (by rfl) ⟨2643002, by rfl⟩ : syracuseStep 3524003 = 5286005) B5286005
theorem B4015537 : Blo 1564980 4015537 := bstep (se 2 (by rfl) ⟨1505826, by rfl⟩ : syracuseStep 4015537 = 3011653) B3011653
theorem B1566131 : Blo 1564980 1566131 := bstep (se 1 (by rfl) ⟨1174598, by rfl⟩ : syracuseStep 1566131 = 2349197) B2349197
theorem B1566147 : Blo 1564980 1566147 := bstep (se 1 (by rfl) ⟨1174610, by rfl⟩ : syracuseStep 1566147 = 2349221) B2349221
theorem B8914373 : Blo 1564980 8914373 := bstep (se 4 (by rfl) ⟨835722, by rfl⟩ : syracuseStep 8914373 = 1671445) B1671445
theorem B2229715 : Blo 1564980 2229715 := bstep (se 1 (by rfl) ⟨1672286, by rfl⟩ : syracuseStep 2229715 = 3344573) B3344573
theorem B1566163 : Blo 1564980 1566163 := bstep (se 1 (by rfl) ⟨1174622, by rfl⟩ : syracuseStep 1566163 = 2349245) B2349245
theorem B1762771 : Blo 1564980 1762771 := bstep (se 1 (by rfl) ⟨1322078, by rfl⟩ : syracuseStep 1762771 = 2644157) B2644157
theorem B1566179 : Blo 1564980 1566179 := bstep (se 1 (by rfl) ⟨1174634, by rfl⟩ : syracuseStep 1566179 = 2349269) B2349269
theorem B8922595 : Blo 1564980 8922595 := bstep (se 1 (by rfl) ⟨6691946, by rfl⟩ : syracuseStep 8922595 = 13383893) B13383893
theorem B5285357 : Blo 1564980 5285357 := bstep (se 3 (by rfl) ⟨991004, by rfl⟩ : syracuseStep 5285357 = 1982009) B1982009
theorem B1566195 : Blo 1564980 1566195 := bstep (se 1 (by rfl) ⟨1174646, by rfl⟩ : syracuseStep 1566195 = 2349293) B2349293
theorem B1566211 : Blo 1564980 1566211 := bstep (se 1 (by rfl) ⟨1174658, by rfl⟩ : syracuseStep 1566211 = 2349317) B2349317
theorem B3343889 : Blo 1564980 3343889 := bstep (se 2 (by rfl) ⟨1253958, by rfl⟩ : syracuseStep 3343889 = 2507917) B2507917
theorem B1566227 : Blo 1564980 1566227 := bstep (se 1 (by rfl) ⟨1174670, by rfl⟩ : syracuseStep 1566227 = 2349341) B2349341
theorem B5285411 : Blo 1564980 5285411 := bstep (se 1 (by rfl) ⟨3964058, by rfl⟩ : syracuseStep 5285411 = 7928117) B7928117
theorem B1566243 : Blo 1564980 1566243 := bstep (se 1 (by rfl) ⟨1174682, by rfl⟩ : syracuseStep 1566243 = 2349365) B2349365
theorem B1566259 : Blo 1564980 1566259 := bstep (se 1 (by rfl) ⟨1174694, by rfl⟩ : syracuseStep 1566259 = 2349389) B2349389
theorem B1566275 : Blo 1564980 1566275 := bstep (se 1 (by rfl) ⟨1174706, by rfl⟩ : syracuseStep 1566275 = 2349413) B2349413
theorem B1566291 : Blo 1564980 1566291 := bstep (se 1 (by rfl) ⟨1174718, by rfl⟩ : syracuseStep 1566291 = 2349437) B2349437
theorem B1566307 : Blo 1564980 1566307 := bstep (se 1 (by rfl) ⟨1174730, by rfl⟩ : syracuseStep 1566307 = 2349461) B2349461
theorem B1566323 : Blo 1564980 1566323 := bstep (se 1 (by rfl) ⟨1174742, by rfl⟩ : syracuseStep 1566323 = 2349485) B2349485
theorem B1566339 : Blo 1564980 1566339 := bstep (se 1 (by rfl) ⟨1174754, by rfl⟩ : syracuseStep 1566339 = 2349509) B2349509
theorem B9528965 : Blo 1564980 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B1566355 : Blo 1564980 1566355 := bstep (se 1 (by rfl) ⟨1174766, by rfl⟩ : syracuseStep 1566355 = 2349533) B2349533
theorem B1566371 : Blo 1564980 1566371 := bstep (se 1 (by rfl) ⟨1174778, by rfl⟩ : syracuseStep 1566371 = 2349557) B2349557
theorem B3524273 : Blo 1564980 3524273 := bstep (se 2 (by rfl) ⟨1321602, by rfl⟩ : syracuseStep 3524273 = 2643205) B2643205
theorem B1566387 : Blo 1564980 1566387 := bstep (se 1 (by rfl) ⟨1174790, by rfl⟩ : syracuseStep 1566387 = 2349581) B2349581
theorem B3524291 : Blo 1564980 3524291 := bstep (se 1 (by rfl) ⟨2643218, by rfl⟩ : syracuseStep 3524291 = 5286437) B5286437
theorem B1566403 : Blo 1564980 1566403 := bstep (se 1 (by rfl) ⟨1174802, by rfl⟩ : syracuseStep 1566403 = 2349605) B2349605
theorem B1566419 : Blo 1564980 1566419 := bstep (se 1 (by rfl) ⟨1174814, by rfl⟩ : syracuseStep 1566419 = 2349629) B2349629
theorem B1566435 : Blo 1564980 1566435 := bstep (se 1 (by rfl) ⟨1174826, by rfl⟩ : syracuseStep 1566435 = 2349653) B2349653
theorem B1566451 : Blo 1564980 1566451 := bstep (se 1 (by rfl) ⟨1174838, by rfl⟩ : syracuseStep 1566451 = 2349677) B2349677
theorem B1566467 : Blo 1564980 1566467 := bstep (se 1 (by rfl) ⟨1174850, by rfl⟩ : syracuseStep 1566467 = 2349701) B2349701
theorem B1566483 : Blo 1564980 1566483 := bstep (se 1 (by rfl) ⟨1174862, by rfl⟩ : syracuseStep 1566483 = 2349725) B2349725
theorem B1566499 : Blo 1564980 1566499 := bstep (se 1 (by rfl) ⟨1174874, by rfl⟩ : syracuseStep 1566499 = 2349749) B2349749
theorem B5285681 : Blo 1564980 5285681 := bstep (se 2 (by rfl) ⟨1982130, by rfl⟩ : syracuseStep 5285681 = 3964261) B3964261
theorem B5949233 : Blo 1564980 5949233 := bstep (se 2 (by rfl) ⟨2230962, by rfl⟩ : syracuseStep 5949233 = 4461925) B4461925
theorem B1566515 : Blo 1564980 1566515 := bstep (se 1 (by rfl) ⟨1174886, by rfl⟩ : syracuseStep 1566515 = 2349773) B2349773
theorem B1566531 : Blo 1564980 1566531 := bstep (se 1 (by rfl) ⟨1174898, by rfl⟩ : syracuseStep 1566531 = 2349797) B2349797
theorem B1566547 : Blo 1564980 1566547 := bstep (se 1 (by rfl) ⟨1174910, by rfl⟩ : syracuseStep 1566547 = 2349821) B2349821
theorem B1566563 : Blo 1564980 1566563 := bstep (se 1 (by rfl) ⟨1174922, by rfl⟩ : syracuseStep 1566563 = 2349845) B2349845
theorem B1566579 : Blo 1564980 1566579 := bstep (se 1 (by rfl) ⟨1174934, by rfl⟩ : syracuseStep 1566579 = 2349869) B2349869
theorem B1566595 : Blo 1564980 1566595 := bstep (se 1 (by rfl) ⟨1174946, by rfl⟩ : syracuseStep 1566595 = 2349893) B2349893
theorem B1566611 : Blo 1564980 1566611 := bstep (se 1 (by rfl) ⟨1174958, by rfl⟩ : syracuseStep 1566611 = 2349917) B2349917
theorem B1566627 : Blo 1564980 1566627 := bstep (se 1 (by rfl) ⟨1174970, by rfl⟩ : syracuseStep 1566627 = 2349941) B2349941
theorem B1566643 : Blo 1564980 1566643 := bstep (se 1 (by rfl) ⟨1174982, by rfl⟩ : syracuseStep 1566643 = 2349965) B2349965
theorem B2508737 : Blo 1564980 2508737 := bstep (se 2 (by rfl) ⟨940776, by rfl⟩ : syracuseStep 2508737 = 1881553) B1881553
theorem B1566659 : Blo 1564980 1566659 := bstep (se 1 (by rfl) ⟨1174994, by rfl⟩ : syracuseStep 1566659 = 2349989) B2349989
theorem B3524561 : Blo 1564980 3524561 := bstep (se 2 (by rfl) ⟨1321710, by rfl⟩ : syracuseStep 3524561 = 2643421) B2643421
theorem B1566675 : Blo 1564980 1566675 := bstep (se 1 (by rfl) ⟨1175006, by rfl⟩ : syracuseStep 1566675 = 2350013) B2350013
theorem B3524579 : Blo 1564980 3524579 := bstep (se 1 (by rfl) ⟨2643434, by rfl⟩ : syracuseStep 3524579 = 5286869) B5286869
theorem B1566691 : Blo 1564980 1566691 := bstep (se 1 (by rfl) ⟨1175018, by rfl⟩ : syracuseStep 1566691 = 2350037) B2350037
theorem B8923121 : Blo 1564980 8923121 := bstep (se 2 (by rfl) ⟨3346170, by rfl⟩ : syracuseStep 8923121 = 6692341) B6692341
theorem B1566707 : Blo 1564980 1566707 := bstep (se 1 (by rfl) ⟨1175030, by rfl⟩ : syracuseStep 1566707 = 2350061) B2350061
theorem B1566723 : Blo 1564980 1566723 := bstep (se 1 (by rfl) ⟨1175042, by rfl⟩ : syracuseStep 1566723 = 2350085) B2350085
theorem B1566739 : Blo 1564980 1566739 := bstep (se 1 (by rfl) ⟨1175054, by rfl⟩ : syracuseStep 1566739 = 2350109) B2350109
theorem B3344419 : Blo 1564980 3344419 := bstep (se 1 (by rfl) ⟨2508314, by rfl⟩ : syracuseStep 3344419 = 5016629) B5016629
theorem B1566755 : Blo 1564980 1566755 := bstep (se 1 (by rfl) ⟨1175066, by rfl⟩ : syracuseStep 1566755 = 2350133) B2350133
theorem B1566771 : Blo 1564980 1566771 := bstep (se 1 (by rfl) ⟨1175078, by rfl⟩ : syracuseStep 1566771 = 2350157) B2350157
theorem B1566787 : Blo 1564980 1566787 := bstep (se 1 (by rfl) ⟨1175090, by rfl⟩ : syracuseStep 1566787 = 2350181) B2350181
theorem B1566803 : Blo 1564980 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B1566819 : Blo 1564980 1566819 := bstep (se 1 (by rfl) ⟨1175114, by rfl⟩ : syracuseStep 1566819 = 2350229) B2350229
theorem B1566835 : Blo 1564980 1566835 := bstep (se 1 (by rfl) ⟨1175126, by rfl⟩ : syracuseStep 1566835 = 2350253) B2350253
theorem B1566851 : Blo 1564980 1566851 := bstep (se 1 (by rfl) ⟨1175138, by rfl⟩ : syracuseStep 1566851 = 2350277) B2350277
theorem B1566867 : Blo 1564980 1566867 := bstep (se 1 (by rfl) ⟨1175150, by rfl⟩ : syracuseStep 1566867 = 2350301) B2350301
theorem B1566883 : Blo 1564980 1566883 := bstep (se 1 (by rfl) ⟨1175162, by rfl⟩ : syracuseStep 1566883 = 2350325) B2350325
theorem B1566899 : Blo 1564980 1566899 := bstep (se 1 (by rfl) ⟨1175174, by rfl⟩ : syracuseStep 1566899 = 2350349) B2350349
theorem B1566915 : Blo 1564980 1566915 := bstep (se 1 (by rfl) ⟨1175186, by rfl⟩ : syracuseStep 1566915 = 2350373) B2350373
theorem B4458701 : Blo 1564980 4458701 := bstep (se 3 (by rfl) ⟨836006, by rfl⟩ : syracuseStep 4458701 = 1672013) B1672013
theorem B1566931 : Blo 1564980 1566931 := bstep (se 1 (by rfl) ⟨1175198, by rfl⟩ : syracuseStep 1566931 = 2350397) B2350397
theorem B1566947 : Blo 1564980 1566947 := bstep (se 1 (by rfl) ⟨1175210, by rfl⟩ : syracuseStep 1566947 = 2350421) B2350421
theorem B3524849 : Blo 1564980 3524849 := bstep (se 2 (by rfl) ⟨1321818, by rfl⟩ : syracuseStep 3524849 = 2643637) B2643637
theorem B1566963 : Blo 1564980 1566963 := bstep (se 1 (by rfl) ⟨1175222, by rfl⟩ : syracuseStep 1566963 = 2350445) B2350445
theorem B3524867 : Blo 1564980 3524867 := bstep (se 1 (by rfl) ⟨2643650, by rfl⟩ : syracuseStep 3524867 = 5287301) B5287301
theorem B1566979 : Blo 1564980 1566979 := bstep (se 1 (by rfl) ⟨1175234, by rfl⟩ : syracuseStep 1566979 = 2350469) B2350469
theorem B5286221 : Blo 1564980 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B7924067 : Blo 1564980 7924067 := bstep (se 1 (by rfl) ⟨5943050, by rfl⟩ : syracuseStep 7924067 = 11886101) B11886101
theorem B38095217 : Blo 1564980 38095217 := bstep (se 2 (by rfl) ⟨14285706, by rfl⟩ : syracuseStep 38095217 = 28571413) B28571413
theorem B4458883 : Blo 1564980 4458883 := bstep (se 1 (by rfl) ⟨3344162, by rfl⟩ : syracuseStep 4458883 = 6688325) B6688325
theorem B5286275 : Blo 1564980 5286275 := bstep (se 1 (by rfl) ⟨3964706, by rfl⟩ : syracuseStep 5286275 = 7929413) B7929413
theorem B6351281 : Blo 1564980 6351281 := bstep (se 2 (by rfl) ⟨2381730, by rfl⟩ : syracuseStep 6351281 = 4763461) B4763461
theorem B3525137 : Blo 1564980 3525137 := bstep (se 2 (by rfl) ⟨1321926, by rfl⟩ : syracuseStep 3525137 = 2643853) B2643853
theorem B34327061 : Blo 1564980 34327061 := bstep (se 6 (by rfl) ⟨804540, by rfl⟩ : syracuseStep 34327061 = 1609081) B1609081
theorem B4459043 : Blo 1564980 4459043 := bstep (se 1 (by rfl) ⟨3344282, by rfl⟩ : syracuseStep 4459043 = 6688565) B6688565
theorem B4762147 : Blo 1564980 4762147 := bstep (se 1 (by rfl) ⟨3571610, by rfl⟩ : syracuseStep 4762147 = 7143221) B7143221
theorem B3525155 : Blo 1564980 3525155 := bstep (se 1 (by rfl) ⟨2643866, by rfl⟩ : syracuseStep 3525155 = 5287733) B5287733
theorem B5286545 : Blo 1564980 5286545 := bstep (se 2 (by rfl) ⟨1982454, by rfl⟩ : syracuseStep 5286545 = 3964909) B3964909
theorem B2231059 : Blo 1564980 2231059 := bstep (se 1 (by rfl) ⟨1673294, by rfl⟩ : syracuseStep 2231059 = 3346589) B3346589
theorem B3525425 : Blo 1564980 3525425 := bstep (se 2 (by rfl) ⟨1322034, by rfl⟩ : syracuseStep 3525425 = 2644069) B2644069
theorem B3525443 : Blo 1564980 3525443 := bstep (se 1 (by rfl) ⟨2644082, by rfl⟩ : syracuseStep 3525443 = 5288165) B5288165
theorem B2509699 : Blo 1564980 2509699 := bstep (se 1 (by rfl) ⟨1882274, by rfl⟩ : syracuseStep 2509699 = 3764549) B3764549
theorem B2821105 : Blo 1564980 2821105 := bstep (se 2 (by rfl) ⟨1057914, by rfl⟩ : syracuseStep 2821105 = 2115829) B2115829
theorem B2116705 : Blo 1564980 2116705 := bstep (se 2 (by rfl) ⟨793764, by rfl⟩ : syracuseStep 2116705 = 1587529) B1587529
theorem B2641025 : Blo 1564980 2641025 := bstep (se 2 (by rfl) ⟨990384, by rfl⟩ : syracuseStep 2641025 = 1980769) B1980769
theorem B2509955 : Blo 1564980 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B7924877 : Blo 1564980 7924877 := bstep (se 3 (by rfl) ⟨1485914, by rfl⟩ : syracuseStep 7924877 = 2971829) B2971829
theorem B5287085 : Blo 1564980 5287085 := bstep (se 3 (by rfl) ⟨991328, by rfl⟩ : syracuseStep 5287085 = 1982657) B1982657
theorem B5287139 : Blo 1564980 5287139 := bstep (se 1 (by rfl) ⟨3965354, by rfl⟩ : syracuseStep 5287139 = 7930709) B7930709
theorem B2641153 : Blo 1564980 2641153 := bstep (se 2 (by rfl) ⟨990432, by rfl⟩ : syracuseStep 2641153 = 1980865) B1980865
theorem B13372685 : Blo 1564980 13372685 := bstep (se 3 (by rfl) ⟨2507378, by rfl⟩ : syracuseStep 13372685 = 5014757) B5014757
theorem B11283725 : Blo 1564980 11283725 := bstep (se 3 (by rfl) ⟨2115698, by rfl⟩ : syracuseStep 11283725 = 4231397) B4231397
theorem B2641187 : Blo 1564980 2641187 := bstep (se 1 (by rfl) ⟨1980890, by rfl⟩ : syracuseStep 2641187 = 3961781) B3961781
theorem B20065589 : Blo 1564980 20065589 := bstep (se 5 (by rfl) ⟨940574, by rfl⟩ : syracuseStep 20065589 = 1881149) B1881149
theorem B11283781 : Blo 1564980 11283781 := bstep (se 4 (by rfl) ⟨1057854, by rfl⟩ : syracuseStep 11283781 = 2115709) B2115709
theorem B11889989 : Blo 1564980 11889989 := bstep (se 4 (by rfl) ⟨1114686, by rfl⟩ : syracuseStep 11889989 = 2229373) B2229373
theorem B10718605 : Blo 1564980 10718605 := bstep (se 3 (by rfl) ⟨2009738, by rfl⟩ : syracuseStep 10718605 = 4019477) B4019477
theorem B2641315 : Blo 1564980 2641315 := bstep (se 1 (by rfl) ⟨1980986, by rfl⟩ : syracuseStep 2641315 = 3961973) B3961973
theorem B1609139 : Blo 1564980 1609139 := bstep (se 1 (by rfl) ⟨1206854, by rfl⟩ : syracuseStep 1609139 = 2413709) B2413709
theorem B24440291 : Blo 1564980 24440291 := bstep (se 1 (by rfl) ⟨18330218, by rfl⟩ : syracuseStep 24440291 = 36660437) B36660437
theorem B22580707 : Blo 1564980 22580707 := bstep (se 1 (by rfl) ⟨16935530, by rfl⟩ : syracuseStep 22580707 = 33871061) B33871061
theorem B6688241 : Blo 1564980 6688241 := bstep (se 2 (by rfl) ⟨2508090, by rfl⟩ : syracuseStep 6688241 = 5016181) B5016181
theorem B3345905 : Blo 1564980 3345905 := bstep (se 2 (by rfl) ⟨1254714, by rfl⟩ : syracuseStep 3345905 = 2509429) B2509429
theorem B5287409 : Blo 1564980 5287409 := bstep (se 2 (by rfl) ⟨1982778, by rfl⟩ : syracuseStep 5287409 = 3965557) B3965557
theorem B3345923 : Blo 1564980 3345923 := bstep (se 1 (by rfl) ⟨2509442, by rfl⟩ : syracuseStep 3345923 = 5018885) B5018885
theorem B6688291 : Blo 1564980 6688291 := bstep (se 1 (by rfl) ⟨5016218, by rfl⟩ : syracuseStep 6688291 = 10032437) B10032437
theorem B2641457 : Blo 1564980 2641457 := bstep (se 2 (by rfl) ⟨990546, by rfl⟩ : syracuseStep 2641457 = 1981093) B1981093
theorem B4460113 : Blo 1564980 4460113 := bstep (se 2 (by rfl) ⟨1672542, by rfl⟩ : syracuseStep 4460113 = 3345085) B3345085
theorem B15044237 : Blo 1564980 15044237 := bstep (se 3 (by rfl) ⟨2820794, by rfl⟩ : syracuseStep 15044237 = 5641589) B5641589
theorem B8466083 : Blo 1564980 8466083 := bstep (se 1 (by rfl) ⟨6349562, by rfl⟩ : syracuseStep 8466083 = 12699125) B12699125
theorem B2641585 : Blo 1564980 2641585 := bstep (se 2 (by rfl) ⟨990594, by rfl⟩ : syracuseStep 2641585 = 1981189) B1981189
theorem B2641619 : Blo 1564980 2641619 := bstep (se 1 (by rfl) ⟨1981214, by rfl⟩ : syracuseStep 2641619 = 3962429) B3962429
theorem B3174115 : Blo 1564980 3174115 := bstep (se 1 (by rfl) ⟨2380586, by rfl⟩ : syracuseStep 3174115 = 4761173) B4761173
theorem B2821891 : Blo 1564980 2821891 := bstep (se 1 (by rfl) ⟨2116418, by rfl⟩ : syracuseStep 2821891 = 4232837) B4232837
theorem B5426957 : Blo 1564980 5426957 := bstep (se 3 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 5426957 = 2035109) B2035109
theorem B5721905 : Blo 1564980 5721905 := bstep (se 2 (by rfl) ⟨2145714, by rfl⟩ : syracuseStep 5721905 = 4291429) B4291429
theorem B13553477 : Blo 1564980 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B15249221 : Blo 1564980 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B2641747 : Blo 1564980 2641747 := bstep (se 1 (by rfl) ⟨1981310, by rfl⟩ : syracuseStep 2641747 = 3962621) B3962621
theorem B11898737 : Blo 1564980 11898737 := bstep (se 2 (by rfl) ⟨4462026, by rfl⟩ : syracuseStep 11898737 = 8924053) B8924053
theorem B5943203 : Blo 1564980 5943203 := bstep (se 1 (by rfl) ⟨4457402, by rfl⟩ : syracuseStep 5943203 = 8914805) B8914805
theorem B2641889 : Blo 1564980 2641889 := bstep (se 2 (by rfl) ⟨990708, by rfl⟩ : syracuseStep 2641889 = 1981417) B1981417
theorem B15044579 : Blo 1564980 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B5287949 : Blo 1564980 5287949 := bstep (se 3 (by rfl) ⟨991490, by rfl⟩ : syracuseStep 5287949 = 1982981) B1982981
theorem B21442573 : Blo 1564980 21442573 := bstep (se 3 (by rfl) ⟨4020482, by rfl⟩ : syracuseStep 21442573 = 8040965) B8040965
theorem B5288003 : Blo 1564980 5288003 := bstep (se 1 (by rfl) ⟨3966002, by rfl⟩ : syracuseStep 5288003 = 7932005) B7932005
theorem B2642017 : Blo 1564980 2642017 := bstep (se 2 (by rfl) ⟨990756, by rfl⟩ : syracuseStep 2642017 = 1981513) B1981513
theorem B10039409 : Blo 1564980 10039409 := bstep (se 2 (by rfl) ⟨3764778, by rfl⟩ : syracuseStep 10039409 = 7529557) B7529557
theorem B2642051 : Blo 1564980 2642051 := bstep (se 1 (by rfl) ⟨1981538, by rfl⟩ : syracuseStep 2642051 = 3963077) B3963077
theorem B2642179 : Blo 1564980 2642179 := bstep (se 1 (by rfl) ⟨1981634, by rfl⟩ : syracuseStep 2642179 = 3963269) B3963269
theorem B5017859 : Blo 1564980 5017859 := bstep (se 1 (by rfl) ⟨3763394, by rfl⟩ : syracuseStep 5017859 = 7526789) B7526789
theorem B8147249 : Blo 1564980 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B5288273 : Blo 1564980 5288273 := bstep (se 2 (by rfl) ⟨1983102, by rfl⟩ : syracuseStep 5288273 = 3966205) B3966205
theorem B2642321 : Blo 1564980 2642321 := bstep (se 2 (by rfl) ⟨990870, by rfl⟩ : syracuseStep 2642321 = 1981741) B1981741
theorem B2380193 : Blo 1564980 2380193 := bstep (se 2 (by rfl) ⟨892572, by rfl⟩ : syracuseStep 2380193 = 1785145) B1785145
theorem B2380241 : Blo 1564980 2380241 := bstep (se 2 (by rfl) ⟨892590, by rfl⟩ : syracuseStep 2380241 = 1785181) B1785181
theorem B2347475 : Blo 1564980 2347475 := bstep (se 1 (by rfl) ⟨1760606, by rfl⟩ : syracuseStep 2347475 = 3521213) B3521213
theorem B2347505 : Blo 1564980 2347505 := bstep (se 2 (by rfl) ⟨880314, by rfl⟩ : syracuseStep 2347505 = 1760629) B1760629
theorem B2347523 : Blo 1564980 2347523 := bstep (se 1 (by rfl) ⟨1760642, by rfl⟩ : syracuseStep 2347523 = 3521285) B3521285
theorem B2642449 : Blo 1564980 2642449 := bstep (se 2 (by rfl) ⟨990918, by rfl⟩ : syracuseStep 2642449 = 1981837) B1981837
theorem B2347553 : Blo 1564980 2347553 := bstep (se 2 (by rfl) ⟨880332, by rfl⟩ : syracuseStep 2347553 = 1760665) B1760665
theorem B10711601 : Blo 1564980 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B2347571 : Blo 1564980 2347571 := bstep (se 1 (by rfl) ⟨1760678, by rfl⟩ : syracuseStep 2347571 = 3521357) B3521357
theorem B2642483 : Blo 1564980 2642483 := bstep (se 1 (by rfl) ⟨1981862, by rfl⟩ : syracuseStep 2642483 = 3963725) B3963725
theorem B30528053 : Blo 1564980 30528053 := bstep (se 5 (by rfl) ⟨1431002, by rfl⟩ : syracuseStep 30528053 = 2862005) B2862005
theorem B2347601 : Blo 1564980 2347601 := bstep (se 2 (by rfl) ⟨880350, by rfl⟩ : syracuseStep 2347601 = 1760701) B1760701
theorem B2347619 : Blo 1564980 2347619 := bstep (se 1 (by rfl) ⟨1760714, by rfl⟩ : syracuseStep 2347619 = 3521429) B3521429
theorem B3961457 : Blo 1564980 3961457 := bstep (se 2 (by rfl) ⟨1485546, by rfl⟩ : syracuseStep 3961457 = 2971093) B2971093
theorem B2347649 : Blo 1564980 2347649 := bstep (se 2 (by rfl) ⟨880368, by rfl⟩ : syracuseStep 2347649 = 1760737) B1760737
theorem B10039949 : Blo 1564980 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B2347667 : Blo 1564980 2347667 := bstep (se 1 (by rfl) ⟨1760750, by rfl⟩ : syracuseStep 2347667 = 3521501) B3521501
theorem B3961507 : Blo 1564980 3961507 := bstep (se 1 (by rfl) ⟨2971130, by rfl⟩ : syracuseStep 3961507 = 5942261) B5942261
theorem B2822819 : Blo 1564980 2822819 := bstep (se 1 (by rfl) ⟨2117114, by rfl⟩ : syracuseStep 2822819 = 4234229) B4234229
theorem B2347697 : Blo 1564980 2347697 := bstep (se 2 (by rfl) ⟨880386, by rfl⟩ : syracuseStep 2347697 = 1760773) B1760773
theorem B6107825 : Blo 1564980 6107825 := bstep (se 2 (by rfl) ⟨2290434, by rfl⟩ : syracuseStep 6107825 = 4580869) B4580869
theorem B2642611 : Blo 1564980 2642611 := bstep (se 1 (by rfl) ⟨1981958, by rfl⟩ : syracuseStep 2642611 = 3963917) B3963917
theorem B2347715 : Blo 1564980 2347715 := bstep (se 1 (by rfl) ⟨1760786, by rfl⟩ : syracuseStep 2347715 = 3521573) B3521573
theorem B2347745 : Blo 1564980 2347745 := bstep (se 2 (by rfl) ⟨880404, by rfl⟩ : syracuseStep 2347745 = 1760809) B1760809
theorem B1880803 : Blo 1564980 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B2347763 : Blo 1564980 2347763 := bstep (se 1 (by rfl) ⟨1760822, by rfl⟩ : syracuseStep 2347763 = 3521645) B3521645
theorem B2347793 : Blo 1564980 2347793 := bstep (se 2 (by rfl) ⟨880422, by rfl⟩ : syracuseStep 2347793 = 1760845) B1760845
theorem B2347811 : Blo 1564980 2347811 := bstep (se 1 (by rfl) ⟨1760858, by rfl⟩ : syracuseStep 2347811 = 3521717) B3521717
theorem B3961649 : Blo 1564980 3961649 := bstep (se 2 (by rfl) ⟨1485618, by rfl⟩ : syracuseStep 3961649 = 2971237) B2971237
theorem B2347841 : Blo 1564980 2347841 := bstep (se 2 (by rfl) ⟨880440, by rfl⟩ : syracuseStep 2347841 = 1760881) B1760881
theorem B2642753 : Blo 1564980 2642753 := bstep (se 2 (by rfl) ⟨991032, by rfl⟩ : syracuseStep 2642753 = 1982065) B1982065
theorem B4461389 : Blo 1564980 4461389 := bstep (se 3 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 4461389 = 1673021) B1673021
theorem B2347859 : Blo 1564980 2347859 := bstep (se 1 (by rfl) ⟨1760894, by rfl⟩ : syracuseStep 2347859 = 3521789) B3521789
theorem B2347889 : Blo 1564980 2347889 := bstep (se 2 (by rfl) ⟨880458, by rfl⟩ : syracuseStep 2347889 = 1760917) B1760917
theorem B2347907 : Blo 1564980 2347907 := bstep (se 1 (by rfl) ⟨1760930, by rfl⟩ : syracuseStep 2347907 = 3521861) B3521861
theorem B8033165 : Blo 1564980 8033165 := bstep (se 3 (by rfl) ⟨1506218, by rfl⟩ : syracuseStep 8033165 = 3012437) B3012437
theorem B5944205 : Blo 1564980 5944205 := bstep (se 3 (by rfl) ⟨1114538, by rfl⟩ : syracuseStep 5944205 = 2229077) B2229077
theorem B2347937 : Blo 1564980 2347937 := bstep (se 2 (by rfl) ⟨880476, by rfl⟩ : syracuseStep 2347937 = 1760953) B1760953
theorem B2347955 : Blo 1564980 2347955 := bstep (se 1 (by rfl) ⟨1760966, by rfl⟩ : syracuseStep 2347955 = 3521933) B3521933
theorem B2642881 : Blo 1564980 2642881 := bstep (se 2 (by rfl) ⟨991080, by rfl⟩ : syracuseStep 2642881 = 1982161) B1982161
theorem B2347985 : Blo 1564980 2347985 := bstep (se 2 (by rfl) ⟨880494, by rfl⟩ : syracuseStep 2347985 = 1760989) B1760989
theorem B2348003 : Blo 1564980 2348003 := bstep (se 1 (by rfl) ⟨1761002, by rfl⟩ : syracuseStep 2348003 = 3522005) B3522005
theorem B2642915 : Blo 1564980 2642915 := bstep (se 1 (by rfl) ⟨1982186, by rfl⟩ : syracuseStep 2642915 = 3964373) B3964373
theorem B2348033 : Blo 1564980 2348033 := bstep (se 2 (by rfl) ⟨880512, by rfl⟩ : syracuseStep 2348033 = 1761025) B1761025
theorem B4461571 : Blo 1564980 4461571 := bstep (se 1 (by rfl) ⟨3346178, by rfl⟩ : syracuseStep 4461571 = 6692357) B6692357
theorem B2348051 : Blo 1564980 2348051 := bstep (se 1 (by rfl) ⟨1761038, by rfl⟩ : syracuseStep 2348051 = 3522077) B3522077
theorem B2348081 : Blo 1564980 2348081 := bstep (se 2 (by rfl) ⟨880530, by rfl⟩ : syracuseStep 2348081 = 1761061) B1761061
theorem B4461617 : Blo 1564980 4461617 := bstep (se 2 (by rfl) ⟨1673106, by rfl⟩ : syracuseStep 4461617 = 3346213) B3346213
theorem B2348099 : Blo 1564980 2348099 := bstep (se 1 (by rfl) ⟨1761074, by rfl⟩ : syracuseStep 2348099 = 3522149) B3522149
theorem B5018705 : Blo 1564980 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B2348129 : Blo 1564980 2348129 := bstep (se 2 (by rfl) ⟨880548, by rfl⟩ : syracuseStep 2348129 = 1761097) B1761097
theorem B2643043 : Blo 1564980 2643043 := bstep (se 1 (by rfl) ⟨1982282, by rfl⟩ : syracuseStep 2643043 = 3964565) B3964565
theorem B2348147 : Blo 1564980 2348147 := bstep (se 1 (by rfl) ⟨1761110, by rfl⟩ : syracuseStep 2348147 = 3522221) B3522221
theorem B5018755 : Blo 1564980 5018755 := bstep (se 1 (by rfl) ⟨3764066, by rfl⟩ : syracuseStep 5018755 = 7528133) B7528133
theorem B2348177 : Blo 1564980 2348177 := bstep (se 2 (by rfl) ⟨880566, by rfl⟩ : syracuseStep 2348177 = 1761133) B1761133
theorem B2348195 : Blo 1564980 2348195 := bstep (se 1 (by rfl) ⟨1761146, by rfl⟩ : syracuseStep 2348195 = 3522293) B3522293
theorem B2348225 : Blo 1564980 2348225 := bstep (se 2 (by rfl) ⟨880584, by rfl⟩ : syracuseStep 2348225 = 1761169) B1761169
theorem B8918221 : Blo 1564980 8918221 := bstep (se 3 (by rfl) ⟨1672166, by rfl⟩ : syracuseStep 8918221 = 3344333) B3344333
theorem B2348243 : Blo 1564980 2348243 := bstep (se 1 (by rfl) ⟨1761182, by rfl⟩ : syracuseStep 2348243 = 3522365) B3522365
theorem B2348273 : Blo 1564980 2348273 := bstep (se 2 (by rfl) ⟨880602, by rfl⟩ : syracuseStep 2348273 = 1761205) B1761205
theorem B2643185 : Blo 1564980 2643185 := bstep (se 2 (by rfl) ⟨991194, by rfl⟩ : syracuseStep 2643185 = 1982389) B1982389
theorem B2348291 : Blo 1564980 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B2348321 : Blo 1564980 2348321 := bstep (se 2 (by rfl) ⟨880620, by rfl⟩ : syracuseStep 2348321 = 1761241) B1761241
theorem B7623985 : Blo 1564980 7623985 := bstep (se 2 (by rfl) ⟨2858994, by rfl⟩ : syracuseStep 7623985 = 5717989) B5717989
theorem B2348339 : Blo 1564980 2348339 := bstep (se 1 (by rfl) ⟨1761254, by rfl⟩ : syracuseStep 2348339 = 3522509) B3522509
theorem B3175729 : Blo 1564980 3175729 := bstep (se 2 (by rfl) ⟨1190898, by rfl⟩ : syracuseStep 3175729 = 2381797) B2381797
theorem B2348369 : Blo 1564980 2348369 := bstep (se 2 (by rfl) ⟨880638, by rfl⟩ : syracuseStep 2348369 = 1761277) B1761277
theorem B1586515 : Blo 1564980 1586515 := bstep (se 1 (by rfl) ⟨1189886, by rfl⟩ : syracuseStep 1586515 = 2379773) B2379773
theorem B2348387 : Blo 1564980 2348387 := bstep (se 1 (by rfl) ⟨1761290, by rfl⟩ : syracuseStep 2348387 = 3522581) B3522581
theorem B2643313 : Blo 1564980 2643313 := bstep (se 2 (by rfl) ⟨991242, by rfl⟩ : syracuseStep 2643313 = 1982485) B1982485
theorem B2348417 : Blo 1564980 2348417 := bstep (se 2 (by rfl) ⟨880656, by rfl⟩ : syracuseStep 2348417 = 1761313) B1761313
theorem B2348435 : Blo 1564980 2348435 := bstep (se 1 (by rfl) ⟨1761326, by rfl⟩ : syracuseStep 2348435 = 3522653) B3522653
theorem B2643347 : Blo 1564980 2643347 := bstep (se 1 (by rfl) ⟨1982510, by rfl⟩ : syracuseStep 2643347 = 3965021) B3965021
theorem B2348465 : Blo 1564980 2348465 := bstep (se 2 (by rfl) ⟨880674, by rfl⟩ : syracuseStep 2348465 = 1761349) B1761349
theorem B2348483 : Blo 1564980 2348483 := bstep (se 1 (by rfl) ⟨1761362, by rfl⟩ : syracuseStep 2348483 = 3522725) B3522725
theorem B10032589 : Blo 1564980 10032589 := bstep (se 3 (by rfl) ⟨1881110, by rfl⟩ : syracuseStep 10032589 = 3762221) B3762221
theorem B2348513 : Blo 1564980 2348513 := bstep (se 2 (by rfl) ⟨880692, by rfl⟩ : syracuseStep 2348513 = 1761385) B1761385
theorem B8467939 : Blo 1564980 8467939 := bstep (se 1 (by rfl) ⟨6350954, by rfl⟩ : syracuseStep 8467939 = 12701909) B12701909
theorem B2348531 : Blo 1564980 2348531 := bstep (se 1 (by rfl) ⟨1761398, by rfl⟩ : syracuseStep 2348531 = 3522797) B3522797
theorem B2348561 : Blo 1564980 2348561 := bstep (se 2 (by rfl) ⟨880710, by rfl⟩ : syracuseStep 2348561 = 1761421) B1761421
theorem B2643475 : Blo 1564980 2643475 := bstep (se 1 (by rfl) ⟨1982606, by rfl⟩ : syracuseStep 2643475 = 3965213) B3965213
theorem B2348579 : Blo 1564980 2348579 := bstep (se 1 (by rfl) ⟨1761434, by rfl⟩ : syracuseStep 2348579 = 3522869) B3522869
theorem B20338229 : Blo 1564980 20338229 := bstep (se 5 (by rfl) ⟨953354, by rfl⟩ : syracuseStep 20338229 = 1906709) B1906709
theorem B2348609 : Blo 1564980 2348609 := bstep (se 2 (by rfl) ⟨880728, by rfl⟩ : syracuseStep 2348609 = 1761457) B1761457
theorem B2348627 : Blo 1564980 2348627 := bstep (se 1 (by rfl) ⟨1761470, by rfl⟩ : syracuseStep 2348627 = 3522941) B3522941
theorem B2348657 : Blo 1564980 2348657 := bstep (se 2 (by rfl) ⟨880746, by rfl⟩ : syracuseStep 2348657 = 1761493) B1761493
theorem B2348675 : Blo 1564980 2348675 := bstep (se 1 (by rfl) ⟨1761506, by rfl⟩ : syracuseStep 2348675 = 3523013) B3523013
theorem B4232845 : Blo 1564980 4232845 := bstep (se 3 (by rfl) ⟨793658, by rfl⟩ : syracuseStep 4232845 = 1587317) B1587317
theorem B2348705 : Blo 1564980 2348705 := bstep (se 2 (by rfl) ⟨880764, by rfl⟩ : syracuseStep 2348705 = 1761529) B1761529
theorem B2643617 : Blo 1564980 2643617 := bstep (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) B1982713
theorem B2971313 : Blo 1564980 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B2348723 : Blo 1564980 2348723 := bstep (se 1 (by rfl) ⟨1761542, by rfl⟩ : syracuseStep 2348723 = 3523085) B3523085
theorem B2348753 : Blo 1564980 2348753 := bstep (se 2 (by rfl) ⟨880782, by rfl⟩ : syracuseStep 2348753 = 1761565) B1761565
theorem B2348771 : Blo 1564980 2348771 := bstep (se 1 (by rfl) ⟨1761578, by rfl⟩ : syracuseStep 2348771 = 3523157) B3523157
theorem B2348801 : Blo 1564980 2348801 := bstep (se 2 (by rfl) ⟨880800, by rfl⟩ : syracuseStep 2348801 = 1761601) B1761601
theorem B3962641 : Blo 1564980 3962641 := bstep (se 2 (by rfl) ⟨1485990, by rfl⟩ : syracuseStep 3962641 = 2971981) B2971981
theorem B2348819 : Blo 1564980 2348819 := bstep (se 1 (by rfl) ⟨1761614, by rfl⟩ : syracuseStep 2348819 = 3523229) B3523229
theorem B2643745 : Blo 1564980 2643745 := bstep (se 2 (by rfl) ⟨991404, by rfl⟩ : syracuseStep 2643745 = 1982809) B1982809
theorem B2348849 : Blo 1564980 2348849 := bstep (se 2 (by rfl) ⟨880818, by rfl⟩ : syracuseStep 2348849 = 1761637) B1761637
theorem B2348867 : Blo 1564980 2348867 := bstep (se 1 (by rfl) ⟨1761650, by rfl⟩ : syracuseStep 2348867 = 3523301) B3523301
theorem B2643779 : Blo 1564980 2643779 := bstep (se 1 (by rfl) ⟨1982834, by rfl⟩ : syracuseStep 2643779 = 3965669) B3965669
theorem B2348897 : Blo 1564980 2348897 := bstep (se 2 (by rfl) ⟨880836, by rfl⟩ : syracuseStep 2348897 = 1761673) B1761673
theorem B2348915 : Blo 1564980 2348915 := bstep (se 1 (by rfl) ⟨1761686, by rfl⟩ : syracuseStep 2348915 = 3523373) B3523373
theorem B6690701 : Blo 1564980 6690701 := bstep (se 3 (by rfl) ⟨1254506, by rfl⟩ : syracuseStep 6690701 = 2509013) B2509013
theorem B2348945 : Blo 1564980 2348945 := bstep (se 2 (by rfl) ⟨880854, by rfl⟩ : syracuseStep 2348945 = 1761709) B1761709
theorem B2348963 : Blo 1564980 2348963 := bstep (se 1 (by rfl) ⟨1761722, by rfl⟩ : syracuseStep 2348963 = 3523445) B3523445
theorem B2348993 : Blo 1564980 2348993 := bstep (se 2 (by rfl) ⟨880872, by rfl⟩ : syracuseStep 2348993 = 1761745) B1761745
theorem B2643907 : Blo 1564980 2643907 := bstep (se 1 (by rfl) ⟨1982930, by rfl⟩ : syracuseStep 2643907 = 3965861) B3965861
theorem B2349011 : Blo 1564980 2349011 := bstep (se 1 (by rfl) ⟨1761758, by rfl⟩ : syracuseStep 2349011 = 3523517) B3523517
theorem B7927793 : Blo 1564980 7927793 := bstep (se 2 (by rfl) ⟨2972922, by rfl⟩ : syracuseStep 7927793 = 5945845) B5945845
theorem B2349041 : Blo 1564980 2349041 := bstep (se 2 (by rfl) ⟨880890, by rfl⟩ : syracuseStep 2349041 = 1761781) B1761781
theorem B2349059 : Blo 1564980 2349059 := bstep (se 1 (by rfl) ⟨1761794, by rfl⟩ : syracuseStep 2349059 = 3523589) B3523589
theorem B8034317 : Blo 1564980 8034317 := bstep (se 3 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 8034317 = 3012869) B3012869
theorem B2349089 : Blo 1564980 2349089 := bstep (se 2 (by rfl) ⟨880908, by rfl⟩ : syracuseStep 2349089 = 1761817) B1761817
theorem B3962915 : Blo 1564980 3962915 := bstep (se 1 (by rfl) ⟨2972186, by rfl⟩ : syracuseStep 3962915 = 5944373) B5944373
theorem B2349107 : Blo 1564980 2349107 := bstep (se 1 (by rfl) ⟨1761830, by rfl⟩ : syracuseStep 2349107 = 3523661) B3523661
theorem B3176515 : Blo 1564980 3176515 := bstep (se 1 (by rfl) ⟨2382386, by rfl⟩ : syracuseStep 3176515 = 4764773) B4764773
theorem B2349137 : Blo 1564980 2349137 := bstep (se 2 (by rfl) ⟨880926, by rfl⟩ : syracuseStep 2349137 = 1761853) B1761853
theorem B2644049 : Blo 1564980 2644049 := bstep (se 2 (by rfl) ⟨991518, by rfl⟩ : syracuseStep 2644049 = 1983037) B1983037
theorem B11884643 : Blo 1564980 11884643 := bstep (se 1 (by rfl) ⟨8913482, by rfl⟩ : syracuseStep 11884643 = 17826965) B17826965
theorem B2349155 : Blo 1564980 2349155 := bstep (se 1 (by rfl) ⟨1761866, by rfl⟩ : syracuseStep 2349155 = 3523733) B3523733
theorem B5281901 : Blo 1564980 5281901 := bstep (se 3 (by rfl) ⟨990356, by rfl⟩ : syracuseStep 5281901 = 1980713) B1980713
theorem B2349185 : Blo 1564980 2349185 := bstep (se 2 (by rfl) ⟨880944, by rfl⟩ : syracuseStep 2349185 = 1761889) B1761889
theorem B2349203 : Blo 1564980 2349203 := bstep (se 1 (by rfl) ⟨1761902, by rfl⟩ : syracuseStep 2349203 = 3523805) B3523805
theorem B5281955 : Blo 1564980 5281955 := bstep (se 1 (by rfl) ⟨3961466, by rfl⟩ : syracuseStep 5281955 = 7922933) B7922933
theorem B2349233 : Blo 1564980 2349233 := bstep (se 2 (by rfl) ⟨880962, by rfl⟩ : syracuseStep 2349233 = 1761925) B1761925
theorem B2349251 : Blo 1564980 2349251 := bstep (se 1 (by rfl) ⟨1761938, by rfl⟩ : syracuseStep 2349251 = 3523877) B3523877
theorem B2644177 : Blo 1564980 2644177 := bstep (se 2 (by rfl) ⟨991566, by rfl⟩ : syracuseStep 2644177 = 1983133) B1983133
theorem B2349281 : Blo 1564980 2349281 := bstep (se 2 (by rfl) ⟨880980, by rfl⟩ : syracuseStep 2349281 = 1761961) B1761961
theorem B3963107 : Blo 1564980 3963107 := bstep (se 1 (by rfl) ⟨2972330, by rfl⟩ : syracuseStep 3963107 = 5944661) B5944661
theorem B2349299 : Blo 1564980 2349299 := bstep (se 1 (by rfl) ⟨1761974, by rfl⟩ : syracuseStep 2349299 = 3523949) B3523949
theorem B2644211 : Blo 1564980 2644211 := bstep (se 1 (by rfl) ⟨1983158, by rfl⟩ : syracuseStep 2644211 = 3966317) B3966317
theorem B2349329 : Blo 1564980 2349329 := bstep (se 2 (by rfl) ⟨880998, by rfl⟩ : syracuseStep 2349329 = 1761997) B1761997
theorem B2349347 : Blo 1564980 2349347 := bstep (se 1 (by rfl) ⟨1762010, by rfl⟩ : syracuseStep 2349347 = 3524021) B3524021
theorem B2349377 : Blo 1564980 2349377 := bstep (se 2 (by rfl) ⟨881016, by rfl⟩ : syracuseStep 2349377 = 1762033) B1762033
theorem B5019985 : Blo 1564980 5019985 := bstep (se 2 (by rfl) ⟨1882494, by rfl⟩ : syracuseStep 5019985 = 3764989) B3764989
theorem B2349395 : Blo 1564980 2349395 := bstep (se 1 (by rfl) ⟨1762046, by rfl⟩ : syracuseStep 2349395 = 3524093) B3524093
theorem B2349425 : Blo 1564980 2349425 := bstep (se 2 (by rfl) ⟨881034, by rfl⟩ : syracuseStep 2349425 = 1762069) B1762069
theorem B2349443 : Blo 1564980 2349443 := bstep (se 1 (by rfl) ⟨1762082, by rfl⟩ : syracuseStep 2349443 = 3524165) B3524165
theorem B2349473 : Blo 1564980 2349473 := bstep (se 2 (by rfl) ⟨881052, by rfl⟩ : syracuseStep 2349473 = 1762105) B1762105
theorem B5282225 : Blo 1564980 5282225 := bstep (se 2 (by rfl) ⟨1980834, by rfl⟩ : syracuseStep 5282225 = 3961669) B3961669
theorem B2349491 : Blo 1564980 2349491 := bstep (se 1 (by rfl) ⟨1762118, by rfl⟩ : syracuseStep 2349491 = 3524237) B3524237
theorem B2349521 : Blo 1564980 2349521 := bstep (se 2 (by rfl) ⟨881070, by rfl⟩ : syracuseStep 2349521 = 1762141) B1762141
theorem B2349539 : Blo 1564980 2349539 := bstep (se 1 (by rfl) ⟨1762154, by rfl⟩ : syracuseStep 2349539 = 3524309) B3524309
theorem B2349569 : Blo 1564980 2349569 := bstep (se 2 (by rfl) ⟨881088, by rfl⟩ : syracuseStep 2349569 = 1762177) B1762177
theorem B1980931 : Blo 1564980 1980931 := bstep (se 1 (by rfl) ⟨1485698, by rfl⟩ : syracuseStep 1980931 = 2971397) B2971397
theorem B2349587 : Blo 1564980 2349587 := bstep (se 1 (by rfl) ⟨1762190, by rfl⟩ : syracuseStep 2349587 = 3524381) B3524381
theorem B2972209 : Blo 1564980 2972209 := bstep (se 2 (by rfl) ⟨1114578, by rfl⟩ : syracuseStep 2972209 = 2229157) B2229157
theorem B2349617 : Blo 1564980 2349617 := bstep (se 2 (by rfl) ⟨881106, by rfl⟩ : syracuseStep 2349617 = 1762213) B1762213
theorem B2349635 : Blo 1564980 2349635 := bstep (se 1 (by rfl) ⟨1762226, by rfl⟩ : syracuseStep 2349635 = 3524453) B3524453
theorem B2349665 : Blo 1564980 2349665 := bstep (se 2 (by rfl) ⟨881124, by rfl⟩ : syracuseStep 2349665 = 1762249) B1762249
theorem B1981027 : Blo 1564980 1981027 := bstep (se 1 (by rfl) ⟨1485770, by rfl⟩ : syracuseStep 1981027 = 2971541) B2971541
theorem B2349683 : Blo 1564980 2349683 := bstep (se 1 (by rfl) ⟨1762262, by rfl⟩ : syracuseStep 2349683 = 3524525) B3524525
theorem B4291213 : Blo 1564980 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B3873425 : Blo 1564980 3873425 := bstep (se 2 (by rfl) ⟨1452534, by rfl⟩ : syracuseStep 3873425 = 2905069) B2905069
theorem B2349713 : Blo 1564980 2349713 := bstep (se 2 (by rfl) ⟨881142, by rfl⟩ : syracuseStep 2349713 = 1762285) B1762285
theorem B2349731 : Blo 1564980 2349731 := bstep (se 1 (by rfl) ⟨1762298, by rfl⟩ : syracuseStep 2349731 = 3524597) B3524597
theorem B2349761 : Blo 1564980 2349761 := bstep (se 2 (by rfl) ⟨881160, by rfl⟩ : syracuseStep 2349761 = 1762321) B1762321
theorem B2972369 : Blo 1564980 2972369 := bstep (se 2 (by rfl) ⟨1114638, by rfl⟩ : syracuseStep 2972369 = 2229277) B2229277
theorem B2349779 : Blo 1564980 2349779 := bstep (se 1 (by rfl) ⟨1762334, by rfl⟩ : syracuseStep 2349779 = 3524669) B3524669
theorem B2349809 : Blo 1564980 2349809 := bstep (se 2 (by rfl) ⟨881178, by rfl⟩ : syracuseStep 2349809 = 1762357) B1762357
theorem B2349827 : Blo 1564980 2349827 := bstep (se 1 (by rfl) ⟨1762370, by rfl⟩ : syracuseStep 2349827 = 3524741) B3524741
theorem B2349857 : Blo 1564980 2349857 := bstep (se 2 (by rfl) ⟨881196, by rfl⟩ : syracuseStep 2349857 = 1762393) B1762393
theorem B2349875 : Blo 1564980 2349875 := bstep (se 1 (by rfl) ⟨1762406, by rfl⟩ : syracuseStep 2349875 = 3524813) B3524813
theorem B2349905 : Blo 1564980 2349905 := bstep (se 2 (by rfl) ⟨881214, by rfl⟩ : syracuseStep 2349905 = 1762429) B1762429
theorem B2349923 : Blo 1564980 2349923 := bstep (se 1 (by rfl) ⟨1762442, by rfl⟩ : syracuseStep 2349923 = 3524885) B3524885
theorem B3521393 : Blo 1564980 3521393 := bstep (se 2 (by rfl) ⟨1320522, by rfl⟩ : syracuseStep 3521393 = 2641045) B2641045
theorem B2349953 : Blo 1564980 2349953 := bstep (se 2 (by rfl) ⟨881232, by rfl⟩ : syracuseStep 2349953 = 1762465) B1762465
theorem B3521411 : Blo 1564980 3521411 := bstep (se 1 (by rfl) ⟨2641058, by rfl⟩ : syracuseStep 3521411 = 5282117) B5282117
theorem B2349971 : Blo 1564980 2349971 := bstep (se 1 (by rfl) ⟨1762478, by rfl⟩ : syracuseStep 2349971 = 3524957) B3524957
theorem B2350001 : Blo 1564980 2350001 := bstep (se 2 (by rfl) ⟨881250, by rfl⟩ : syracuseStep 2350001 = 1762501) B1762501
theorem B2350019 : Blo 1564980 2350019 := bstep (se 1 (by rfl) ⟨1762514, by rfl⟩ : syracuseStep 2350019 = 3525029) B3525029
theorem B5282765 : Blo 1564980 5282765 := bstep (se 3 (by rfl) ⟨990518, by rfl⟩ : syracuseStep 5282765 = 1981037) B1981037
theorem B5946317 : Blo 1564980 5946317 := bstep (se 3 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 5946317 = 2229869) B2229869
theorem B2350049 : Blo 1564980 2350049 := bstep (se 2 (by rfl) ⟨881268, by rfl⟩ : syracuseStep 2350049 = 1762537) B1762537
theorem B2350067 : Blo 1564980 2350067 := bstep (se 1 (by rfl) ⟨1762550, by rfl⟩ : syracuseStep 2350067 = 3525101) B3525101
theorem B5282819 : Blo 1564980 5282819 := bstep (se 1 (by rfl) ⟨3962114, by rfl⟩ : syracuseStep 5282819 = 7924229) B7924229
theorem B9042949 : Blo 1564980 9042949 := bstep (se 4 (by rfl) ⟨847776, by rfl⟩ : syracuseStep 9042949 = 1695553) B1695553
theorem B15465485 : Blo 1564980 15465485 := bstep (se 3 (by rfl) ⟨2899778, by rfl⟩ : syracuseStep 15465485 = 5799557) B5799557
theorem B2350097 : Blo 1564980 2350097 := bstep (se 2 (by rfl) ⟨881286, by rfl⟩ : syracuseStep 2350097 = 1762573) B1762573
theorem B2350115 : Blo 1564980 2350115 := bstep (se 1 (by rfl) ⟨1762586, by rfl⟩ : syracuseStep 2350115 = 3525173) B3525173
theorem B2350145 : Blo 1564980 2350145 := bstep (se 2 (by rfl) ⟨881304, by rfl⟩ : syracuseStep 2350145 = 1762609) B1762609
theorem B1981523 : Blo 1564980 1981523 := bstep (se 1 (by rfl) ⟨1486142, by rfl⟩ : syracuseStep 1981523 = 2972285) B2972285
theorem B2350163 : Blo 1564980 2350163 := bstep (se 1 (by rfl) ⟨1762622, by rfl⟩ : syracuseStep 2350163 = 3525245) B3525245
theorem B1588307 : Blo 1564980 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B2972771 : Blo 1564980 2972771 := bstep (se 1 (by rfl) ⟨2229578, by rfl⟩ : syracuseStep 2972771 = 4459157) B4459157
theorem B12696689 : Blo 1564980 12696689 := bstep (se 2 (by rfl) ⟨4761258, by rfl⟩ : syracuseStep 12696689 = 9522517) B9522517
theorem B2350193 : Blo 1564980 2350193 := bstep (se 2 (by rfl) ⟨881322, by rfl⟩ : syracuseStep 2350193 = 1762645) B1762645
theorem B2350211 : Blo 1564980 2350211 := bstep (se 1 (by rfl) ⟨1762658, by rfl⟩ : syracuseStep 2350211 = 3525317) B3525317
theorem B8920205 : Blo 1564980 8920205 := bstep (se 3 (by rfl) ⟨1672538, by rfl⟩ : syracuseStep 8920205 = 3345077) B3345077
theorem B3521681 : Blo 1564980 3521681 := bstep (se 2 (by rfl) ⟨1320630, by rfl⟩ : syracuseStep 3521681 = 2641261) B2641261
theorem B3964049 : Blo 1564980 3964049 := bstep (se 2 (by rfl) ⟨1486518, by rfl⟩ : syracuseStep 3964049 = 2973037) B2973037
theorem B2350241 : Blo 1564980 2350241 := bstep (se 2 (by rfl) ⟨881340, by rfl⟩ : syracuseStep 2350241 = 1762681) B1762681
theorem B3521699 : Blo 1564980 3521699 := bstep (se 1 (by rfl) ⟨2641274, by rfl⟩ : syracuseStep 3521699 = 5282549) B5282549
theorem B2350259 : Blo 1564980 2350259 := bstep (se 1 (by rfl) ⟨1762694, by rfl⟩ : syracuseStep 2350259 = 3525389) B3525389
theorem B3964099 : Blo 1564980 3964099 := bstep (se 1 (by rfl) ⟨2973074, by rfl⟩ : syracuseStep 3964099 = 5946149) B5946149
theorem B2350289 : Blo 1564980 2350289 := bstep (se 2 (by rfl) ⟨881358, by rfl⟩ : syracuseStep 2350289 = 1762717) B1762717
theorem B2350307 : Blo 1564980 2350307 := bstep (se 1 (by rfl) ⟨1762730, by rfl⟩ : syracuseStep 2350307 = 3525461) B3525461
theorem B4234481 : Blo 1564980 4234481 := bstep (se 2 (by rfl) ⟨1587930, by rfl⟩ : syracuseStep 4234481 = 3175861) B3175861
theorem B2350337 : Blo 1564980 2350337 := bstep (se 2 (by rfl) ⟨881376, by rfl⟩ : syracuseStep 2350337 = 1762753) B1762753
theorem B5283089 : Blo 1564980 5283089 := bstep (se 2 (by rfl) ⟨1981158, by rfl⟩ : syracuseStep 5283089 = 3962317) B3962317
theorem B2350355 : Blo 1564980 2350355 := bstep (se 1 (by rfl) ⟨1762766, by rfl⟩ : syracuseStep 2350355 = 3525533) B3525533
theorem B2350385 : Blo 1564980 2350385 := bstep (se 2 (by rfl) ⟨881394, by rfl⟩ : syracuseStep 2350385 = 1762789) B1762789
theorem B2350403 : Blo 1564980 2350403 := bstep (se 1 (by rfl) ⟨1762802, by rfl⟩ : syracuseStep 2350403 = 3525605) B3525605
theorem B3964241 : Blo 1564980 3964241 := bstep (se 2 (by rfl) ⟨1486590, by rfl⟩ : syracuseStep 3964241 = 2973181) B2973181
theorem B2350433 : Blo 1564980 2350433 := bstep (se 2 (by rfl) ⟨881412, by rfl⟩ : syracuseStep 2350433 = 1762825) B1762825
theorem B1760611 : Blo 1564980 1760611 := bstep (se 1 (by rfl) ⟨1320458, by rfl⟩ : syracuseStep 1760611 = 2640917) B2640917
theorem B2350451 : Blo 1564980 2350451 := bstep (se 1 (by rfl) ⟨1762838, by rfl⟩ : syracuseStep 2350451 = 3525677) B3525677
theorem B32128397 : Blo 1564980 32128397 := bstep (se 3 (by rfl) ⟨6024074, by rfl⟩ : syracuseStep 32128397 = 12048149) B12048149
theorem B7929251 : Blo 1564980 7929251 := bstep (se 1 (by rfl) ⟨5946938, by rfl⟩ : syracuseStep 7929251 = 11893877) B11893877
theorem B3521969 : Blo 1564980 3521969 := bstep (se 2 (by rfl) ⟨1320738, by rfl⟩ : syracuseStep 3521969 = 2641477) B2641477
theorem B3521987 : Blo 1564980 3521987 := bstep (se 1 (by rfl) ⟨2641490, by rfl⟩ : syracuseStep 3521987 = 5282981) B5282981
theorem B1760755 : Blo 1564980 1760755 := bstep (se 1 (by rfl) ⟨1320566, by rfl⟩ : syracuseStep 1760755 = 2641133) B2641133
theorem B1760899 : Blo 1564980 1760899 := bstep (se 1 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 1760899 = 2641349) B2641349
theorem B3522257 : Blo 1564980 3522257 := bstep (se 2 (by rfl) ⟨1320846, by rfl⟩ : syracuseStep 3522257 = 2641693) B2641693
theorem B3522275 : Blo 1564980 3522275 := bstep (se 1 (by rfl) ⟨2641706, by rfl⟩ : syracuseStep 3522275 = 5283413) B5283413
theorem B5947121 : Blo 1564980 5947121 := bstep (se 2 (by rfl) ⟨2230170, by rfl⟩ : syracuseStep 5947121 = 4460341) B4460341
theorem B1761043 : Blo 1564980 1761043 := bstep (se 1 (by rfl) ⟨1320782, by rfl⟩ : syracuseStep 1761043 = 2641565) B2641565
theorem B1982227 : Blo 1564980 1982227 := bstep (se 1 (by rfl) ⟨1486670, by rfl⟩ : syracuseStep 1982227 = 2973341) B2973341
theorem B5283629 : Blo 1564980 5283629 := bstep (se 3 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 5283629 = 1981361) B1981361
theorem B5087053 : Blo 1564980 5087053 := bstep (se 3 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 5087053 = 1907645) B1907645
theorem B5283683 : Blo 1564980 5283683 := bstep (se 1 (by rfl) ⟨3962762, by rfl⟩ : syracuseStep 5283683 = 7925525) B7925525
theorem B1982323 : Blo 1564980 1982323 := bstep (se 1 (by rfl) ⟨1486742, by rfl⟩ : syracuseStep 1982323 = 2973485) B2973485
theorem B1761187 : Blo 1564980 1761187 := bstep (se 1 (by rfl) ⟨1320890, by rfl⟩ : syracuseStep 1761187 = 2641781) B2641781
theorem B4235171 : Blo 1564980 4235171 := bstep (se 1 (by rfl) ⟨3176378, by rfl⟩ : syracuseStep 4235171 = 6352757) B6352757
theorem B4235203 : Blo 1564980 4235203 := bstep (se 1 (by rfl) ⟨3176402, by rfl⟩ : syracuseStep 4235203 = 6352805) B6352805
theorem B2973667 : Blo 1564980 2973667 := bstep (se 1 (by rfl) ⟨2230250, by rfl⟩ : syracuseStep 2973667 = 4460501) B4460501
theorem B3522545 : Blo 1564980 3522545 := bstep (se 2 (by rfl) ⟨1320954, by rfl⟩ : syracuseStep 3522545 = 2641909) B2641909
theorem B28590097 : Blo 1564980 28590097 := bstep (se 2 (by rfl) ⟨10721286, by rfl⟩ : syracuseStep 28590097 = 21442573) B21442573
theorem B11894849 : Blo 1564980 11894849 := bstep (se 2 (by rfl) ⟨4460568, by rfl⟩ : syracuseStep 11894849 = 8921137) B8921137
theorem B3522635 : Blo 1564980 3522635 := bstep (se 1 (by rfl) ⟨2641976, by rfl⟩ : syracuseStep 3522635 = 5283953) B5283953
theorem B6692939 : Blo 1564980 6692939 := bstep (se 1 (by rfl) ⟨5019704, by rfl⟩ : syracuseStep 6692939 = 10039409) B10039409
theorem B1761367 : Blo 1564980 1761367 := bstep (se 1 (by rfl) ⟨1321025, by rfl⟩ : syracuseStep 1761367 = 2642051) B2642051
theorem B1982551 : Blo 1564980 1982551 := bstep (se 1 (by rfl) ⟨1486913, by rfl⟩ : syracuseStep 1982551 = 2973827) B2973827
theorem B3522689 : Blo 1564980 3522689 := bstep (se 2 (by rfl) ⟨1321008, by rfl⟩ : syracuseStep 3522689 = 2642017) B2642017
theorem B10715267 : Blo 1564980 10715267 := bstep (se 1 (by rfl) ⟨8036450, by rfl⟩ : syracuseStep 10715267 = 16072901) B16072901
theorem B6684875 : Blo 1564980 6684875 := bstep (se 1 (by rfl) ⟨5013656, by rfl⟩ : syracuseStep 6684875 = 10027313) B10027313
theorem B5431499 : Blo 1564980 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B5284061 : Blo 1564980 5284061 := bstep (se 3 (by rfl) ⟨990761, by rfl⟩ : syracuseStep 5284061 = 1981523) B1981523
theorem B4235485 : Blo 1564980 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B1761547 : Blo 1564980 1761547 := bstep (se 1 (by rfl) ⟨1321160, by rfl⟩ : syracuseStep 1761547 = 2642321) B2642321
theorem B3342617 : Blo 1564980 3342617 := bstep (se 2 (by rfl) ⟨1253481, by rfl⟩ : syracuseStep 3342617 = 2506963) B2506963
theorem B33857837 : Blo 1564980 33857837 := bstep (se 3 (by rfl) ⟨6348344, by rfl⟩ : syracuseStep 33857837 = 12696689) B12696689
theorem B1564983 : Blo 1564980 1564983 := bstep (se 1 (by rfl) ⟨1173737, by rfl⟩ : syracuseStep 1564983 = 2347475) B2347475
theorem B1565003 : Blo 1564980 1565003 := bstep (se 1 (by rfl) ⟨1173752, by rfl⟩ : syracuseStep 1565003 = 2347505) B2347505
theorem B1565015 : Blo 1564980 1565015 := bstep (se 1 (by rfl) ⟨1173761, by rfl⟩ : syracuseStep 1565015 = 2347523) B2347523
theorem B3522905 : Blo 1564980 3522905 := bstep (se 2 (by rfl) ⟨1321089, by rfl⟩ : syracuseStep 3522905 = 2642179) B2642179
theorem B16941413 : Blo 1564980 16941413 := bstep (se 4 (by rfl) ⟨1588257, by rfl⟩ : syracuseStep 16941413 = 3176515) B3176515
theorem B1565035 : Blo 1564980 1565035 := bstep (se 1 (by rfl) ⟨1173776, by rfl⟩ : syracuseStep 1565035 = 2347553) B2347553
theorem B1565047 : Blo 1564980 1565047 := bstep (se 1 (by rfl) ⟨1173785, by rfl⟩ : syracuseStep 1565047 = 2347571) B2347571
theorem B1761655 : Blo 1564980 1761655 := bstep (se 1 (by rfl) ⟨1321241, by rfl⟩ : syracuseStep 1761655 = 2642483) B2642483
theorem B1565067 : Blo 1564980 1565067 := bstep (se 1 (by rfl) ⟨1173800, by rfl⟩ : syracuseStep 1565067 = 2347601) B2347601
theorem B1565079 : Blo 1564980 1565079 := bstep (se 1 (by rfl) ⟨1173809, by rfl⟩ : syracuseStep 1565079 = 2347619) B2347619
theorem B1565099 : Blo 1564980 1565099 := bstep (se 1 (by rfl) ⟨1173824, by rfl⟩ : syracuseStep 1565099 = 2347649) B2347649
theorem B3522995 : Blo 1564980 3522995 := bstep (se 1 (by rfl) ⟨2642246, by rfl⟩ : syracuseStep 3522995 = 5284493) B5284493
theorem B6693299 : Blo 1564980 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B1565111 : Blo 1564980 1565111 := bstep (se 1 (by rfl) ⟨1173833, by rfl⟩ : syracuseStep 1565111 = 2347667) B2347667
theorem B1565131 : Blo 1564980 1565131 := bstep (se 1 (by rfl) ⟨1173848, by rfl⟩ : syracuseStep 1565131 = 2347697) B2347697
theorem B4071883 : Blo 1564980 4071883 := bstep (se 1 (by rfl) ⟨3053912, by rfl⟩ : syracuseStep 4071883 = 6107825) B6107825
theorem B1565143 : Blo 1564980 1565143 := bstep (se 1 (by rfl) ⟨1173857, by rfl⟩ : syracuseStep 1565143 = 2347715) B2347715
theorem B3523031 : Blo 1564980 3523031 := bstep (se 1 (by rfl) ⟨2642273, by rfl⟩ : syracuseStep 3523031 = 5284547) B5284547
theorem B1565163 : Blo 1564980 1565163 := bstep (se 1 (by rfl) ⟨1173872, by rfl⟩ : syracuseStep 1565163 = 2347745) B2347745
theorem B1565175 : Blo 1564980 1565175 := bstep (se 1 (by rfl) ⟨1173881, by rfl⟩ : syracuseStep 1565175 = 2347763) B2347763
theorem B1565195 : Blo 1564980 1565195 := bstep (se 1 (by rfl) ⟨1173896, by rfl⟩ : syracuseStep 1565195 = 2347793) B2347793
theorem B7930385 : Blo 1564980 7930385 := bstep (se 2 (by rfl) ⟨2973894, by rfl⟩ : syracuseStep 7930385 = 5947789) B5947789
theorem B1565207 : Blo 1564980 1565207 := bstep (se 1 (by rfl) ⟨1173905, by rfl⟩ : syracuseStep 1565207 = 2347811) B2347811
theorem B1565227 : Blo 1564980 1565227 := bstep (se 1 (by rfl) ⟨1173920, by rfl⟩ : syracuseStep 1565227 = 2347841) B2347841
theorem B1761835 : Blo 1564980 1761835 := bstep (se 1 (by rfl) ⟨1321376, by rfl⟩ : syracuseStep 1761835 = 2642753) B2642753
theorem B2974259 : Blo 1564980 2974259 := bstep (se 1 (by rfl) ⟨2230694, by rfl⟩ : syracuseStep 2974259 = 4461389) B4461389
theorem B1565239 : Blo 1564980 1565239 := bstep (se 1 (by rfl) ⟨1173929, by rfl⟩ : syracuseStep 1565239 = 2347859) B2347859
theorem B6685249 : Blo 1564980 6685249 := bstep (se 2 (by rfl) ⟨2506968, by rfl⟩ : syracuseStep 6685249 = 5013937) B5013937
theorem B1565259 : Blo 1564980 1565259 := bstep (se 1 (by rfl) ⟨1173944, by rfl⟩ : syracuseStep 1565259 = 2347889) B2347889
theorem B1565271 : Blo 1564980 1565271 := bstep (se 1 (by rfl) ⟨1173953, by rfl⟩ : syracuseStep 1565271 = 2347907) B2347907
theorem B1565291 : Blo 1564980 1565291 := bstep (se 1 (by rfl) ⟨1173968, by rfl⟩ : syracuseStep 1565291 = 2347937) B2347937
theorem B1671787 : Blo 1564980 1671787 := bstep (se 1 (by rfl) ⟨1253840, by rfl⟩ : syracuseStep 1671787 = 2507681) B2507681
theorem B1565303 : Blo 1564980 1565303 := bstep (se 1 (by rfl) ⟨1173977, by rfl⟩ : syracuseStep 1565303 = 2347955) B2347955
theorem B1565323 : Blo 1564980 1565323 := bstep (se 1 (by rfl) ⟨1173992, by rfl⟩ : syracuseStep 1565323 = 2347985) B2347985
theorem B3523211 : Blo 1564980 3523211 := bstep (se 1 (by rfl) ⟨2642408, by rfl⟩ : syracuseStep 3523211 = 5284817) B5284817
theorem B1565335 : Blo 1564980 1565335 := bstep (se 1 (by rfl) ⟨1174001, by rfl⟩ : syracuseStep 1565335 = 2348003) B2348003
theorem B1761943 : Blo 1564980 1761943 := bstep (se 1 (by rfl) ⟨1321457, by rfl⟩ : syracuseStep 1761943 = 2642915) B2642915
theorem B1565355 : Blo 1564980 1565355 := bstep (se 1 (by rfl) ⟨1174016, by rfl⟩ : syracuseStep 1565355 = 2348033) B2348033
theorem B3343027 : Blo 1564980 3343027 := bstep (se 1 (by rfl) ⟨2507270, by rfl⟩ : syracuseStep 3343027 = 5014541) B5014541
theorem B7930547 : Blo 1564980 7930547 := bstep (se 1 (by rfl) ⟨5947910, by rfl⟩ : syracuseStep 7930547 = 11895821) B11895821
theorem B1565367 : Blo 1564980 1565367 := bstep (se 1 (by rfl) ⟨1174025, by rfl⟩ : syracuseStep 1565367 = 2348051) B2348051
theorem B3523265 : Blo 1564980 3523265 := bstep (se 2 (by rfl) ⟨1321224, by rfl⟩ : syracuseStep 3523265 = 2642449) B2642449
theorem B1565387 : Blo 1564980 1565387 := bstep (se 1 (by rfl) ⟨1174040, by rfl⟩ : syracuseStep 1565387 = 2348081) B2348081
theorem B2974411 : Blo 1564980 2974411 := bstep (se 1 (by rfl) ⟨2230808, by rfl⟩ : syracuseStep 2974411 = 4461617) B4461617
theorem B1565399 : Blo 1564980 1565399 := bstep (se 1 (by rfl) ⟨1174049, by rfl⟩ : syracuseStep 1565399 = 2348099) B2348099
theorem B6349529 : Blo 1564980 6349529 := bstep (se 2 (by rfl) ⟨2381073, by rfl⟩ : syracuseStep 6349529 = 4762147) B4762147
theorem B1565419 : Blo 1564980 1565419 := bstep (se 1 (by rfl) ⟨1174064, by rfl⟩ : syracuseStep 1565419 = 2348129) B2348129
theorem B1565431 : Blo 1564980 1565431 := bstep (se 1 (by rfl) ⟨1174073, by rfl⟩ : syracuseStep 1565431 = 2348147) B2348147
theorem B1565451 : Blo 1564980 1565451 := bstep (se 1 (by rfl) ⟨1174088, by rfl⟩ : syracuseStep 1565451 = 2348177) B2348177
theorem B1565463 : Blo 1564980 1565463 := bstep (se 1 (by rfl) ⟨1174097, by rfl⟩ : syracuseStep 1565463 = 2348195) B2348195
theorem B3965719 : Blo 1564980 3965719 := bstep (se 1 (by rfl) ⟨2974289, by rfl⟩ : syracuseStep 3965719 = 5948579) B5948579
theorem B1565483 : Blo 1564980 1565483 := bstep (se 1 (by rfl) ⟨1174112, by rfl⟩ : syracuseStep 1565483 = 2348225) B2348225
theorem B1565495 : Blo 1564980 1565495 := bstep (se 1 (by rfl) ⟨1174121, by rfl⟩ : syracuseStep 1565495 = 2348243) B2348243
theorem B1565515 : Blo 1564980 1565515 := bstep (se 1 (by rfl) ⟨1174136, by rfl⟩ : syracuseStep 1565515 = 2348273) B2348273
theorem B1762123 : Blo 1564980 1762123 := bstep (se 1 (by rfl) ⟨1321592, by rfl⟩ : syracuseStep 1762123 = 2643185) B2643185
theorem B1565527 : Blo 1564980 1565527 := bstep (se 1 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 1565527 = 2348291) B2348291
theorem B1565547 : Blo 1564980 1565547 := bstep (se 1 (by rfl) ⟨1174160, by rfl⟩ : syracuseStep 1565547 = 2348321) B2348321
theorem B1565559 : Blo 1564980 1565559 := bstep (se 1 (by rfl) ⟨1174169, by rfl⟩ : syracuseStep 1565559 = 2348339) B2348339
theorem B1565579 : Blo 1564980 1565579 := bstep (se 1 (by rfl) ⟨1174184, by rfl⟩ : syracuseStep 1565579 = 2348369) B2348369
theorem B6685591 : Blo 1564980 6685591 := bstep (se 1 (by rfl) ⟨5014193, by rfl⟩ : syracuseStep 6685591 = 10028387) B10028387
theorem B1565591 : Blo 1564980 1565591 := bstep (se 1 (by rfl) ⟨1174193, by rfl⟩ : syracuseStep 1565591 = 2348387) B2348387
theorem B3523481 : Blo 1564980 3523481 := bstep (se 2 (by rfl) ⟨1321305, by rfl⟩ : syracuseStep 3523481 = 2642611) B2642611
theorem B1565611 : Blo 1564980 1565611 := bstep (se 1 (by rfl) ⟨1174208, by rfl⟩ : syracuseStep 1565611 = 2348417) B2348417
theorem B1565623 : Blo 1564980 1565623 := bstep (se 1 (by rfl) ⟨1174217, by rfl⟩ : syracuseStep 1565623 = 2348435) B2348435
theorem B1762231 : Blo 1564980 1762231 := bstep (se 1 (by rfl) ⟨1321673, by rfl⟩ : syracuseStep 1762231 = 2643347) B2643347
theorem B1565643 : Blo 1564980 1565643 := bstep (se 1 (by rfl) ⟨1174232, by rfl⟩ : syracuseStep 1565643 = 2348465) B2348465
theorem B1565655 : Blo 1564980 1565655 := bstep (se 1 (by rfl) ⟨1174241, by rfl⟩ : syracuseStep 1565655 = 2348483) B2348483
theorem B1565675 : Blo 1564980 1565675 := bstep (se 1 (by rfl) ⟨1174256, by rfl⟩ : syracuseStep 1565675 = 2348513) B2348513
theorem B3523571 : Blo 1564980 3523571 := bstep (se 1 (by rfl) ⟨2642678, by rfl⟩ : syracuseStep 3523571 = 5285357) B5285357
theorem B1565687 : Blo 1564980 1565687 := bstep (se 1 (by rfl) ⟨1174265, by rfl⟩ : syracuseStep 1565687 = 2348531) B2348531
theorem B1565707 : Blo 1564980 1565707 := bstep (se 1 (by rfl) ⟨1174280, by rfl⟩ : syracuseStep 1565707 = 2348561) B2348561
theorem B67748885 : Blo 1564980 67748885 := bstep (se 6 (by rfl) ⟨1587864, by rfl⟩ : syracuseStep 67748885 = 3175729) B3175729
theorem B1565719 : Blo 1564980 1565719 := bstep (se 1 (by rfl) ⟨1174289, by rfl⟩ : syracuseStep 1565719 = 2348579) B2348579
theorem B3523607 : Blo 1564980 3523607 := bstep (se 1 (by rfl) ⟨2642705, by rfl⟩ : syracuseStep 3523607 = 5285411) B5285411
theorem B2974745 : Blo 1564980 2974745 := bstep (se 2 (by rfl) ⟨1115529, by rfl⟩ : syracuseStep 2974745 = 2231059) B2231059
theorem B1565739 : Blo 1564980 1565739 := bstep (se 1 (by rfl) ⟨1174304, by rfl⟩ : syracuseStep 1565739 = 2348609) B2348609
theorem B1565751 : Blo 1564980 1565751 := bstep (se 1 (by rfl) ⟨1174313, by rfl⟩ : syracuseStep 1565751 = 2348627) B2348627
theorem B1565771 : Blo 1564980 1565771 := bstep (se 1 (by rfl) ⟨1174328, by rfl⟩ : syracuseStep 1565771 = 2348657) B2348657
theorem B1565783 : Blo 1564980 1565783 := bstep (se 1 (by rfl) ⟨1174337, by rfl⟩ : syracuseStep 1565783 = 2348675) B2348675
theorem B1565803 : Blo 1564980 1565803 := bstep (se 1 (by rfl) ⟨1174352, by rfl⟩ : syracuseStep 1565803 = 2348705) B2348705
theorem B1762411 : Blo 1564980 1762411 := bstep (se 1 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 1762411 = 2643617) B2643617
theorem B1565815 : Blo 1564980 1565815 := bstep (se 1 (by rfl) ⟨1174361, by rfl⟩ : syracuseStep 1565815 = 2348723) B2348723
theorem B1565835 : Blo 1564980 1565835 := bstep (se 1 (by rfl) ⟨1174376, by rfl⟩ : syracuseStep 1565835 = 2348753) B2348753
theorem B1565847 : Blo 1564980 1565847 := bstep (se 1 (by rfl) ⟨1174385, by rfl⟩ : syracuseStep 1565847 = 2348771) B2348771
theorem B3343513 : Blo 1564980 3343513 := bstep (se 2 (by rfl) ⟨1253817, by rfl⟩ : syracuseStep 3343513 = 2507635) B2507635
theorem B1565867 : Blo 1564980 1565867 := bstep (se 1 (by rfl) ⟨1174400, by rfl⟩ : syracuseStep 1565867 = 2348801) B2348801
theorem B1565879 : Blo 1564980 1565879 := bstep (se 1 (by rfl) ⟨1174409, by rfl⟩ : syracuseStep 1565879 = 2348819) B2348819
theorem B1565899 : Blo 1564980 1565899 := bstep (se 1 (by rfl) ⟨1174424, by rfl⟩ : syracuseStep 1565899 = 2348849) B2348849
theorem B3523787 : Blo 1564980 3523787 := bstep (se 1 (by rfl) ⟨2642840, by rfl⟩ : syracuseStep 3523787 = 5285681) B5285681
theorem B3966155 : Blo 1564980 3966155 := bstep (se 1 (by rfl) ⟨2974616, by rfl⟩ : syracuseStep 3966155 = 5949233) B5949233
theorem B1565911 : Blo 1564980 1565911 := bstep (se 1 (by rfl) ⟨1174433, by rfl⟩ : syracuseStep 1565911 = 2348867) B2348867
theorem B1762519 : Blo 1564980 1762519 := bstep (se 1 (by rfl) ⟨1321889, by rfl⟩ : syracuseStep 1762519 = 2643779) B2643779
theorem B1565931 : Blo 1564980 1565931 := bstep (se 1 (by rfl) ⟨1174448, by rfl⟩ : syracuseStep 1565931 = 2348897) B2348897
theorem B1565943 : Blo 1564980 1565943 := bstep (se 1 (by rfl) ⟨1174457, by rfl⟩ : syracuseStep 1565943 = 2348915) B2348915
theorem B3523841 : Blo 1564980 3523841 := bstep (se 2 (by rfl) ⟨1321440, by rfl⟩ : syracuseStep 3523841 = 2642881) B2642881
theorem B1565963 : Blo 1564980 1565963 := bstep (se 1 (by rfl) ⟨1174472, by rfl⟩ : syracuseStep 1565963 = 2348945) B2348945
theorem B1565975 : Blo 1564980 1565975 := bstep (se 1 (by rfl) ⟨1174481, by rfl⟩ : syracuseStep 1565975 = 2348963) B2348963
theorem B1565995 : Blo 1564980 1565995 := bstep (se 1 (by rfl) ⟨1174496, by rfl⟩ : syracuseStep 1565995 = 2348993) B2348993
theorem B8922413 : Blo 1564980 8922413 := bstep (se 3 (by rfl) ⟨1672952, by rfl⟩ : syracuseStep 8922413 = 3345905) B3345905
theorem B1566007 : Blo 1564980 1566007 := bstep (se 1 (by rfl) ⟨1174505, by rfl⟩ : syracuseStep 1566007 = 2349011) B2349011
theorem B3761473 : Blo 1564980 3761473 := bstep (se 2 (by rfl) ⟨1410552, by rfl⟩ : syracuseStep 3761473 = 2821105) B2821105
theorem B5285195 : Blo 1564980 5285195 := bstep (se 1 (by rfl) ⟨3963896, by rfl⟩ : syracuseStep 5285195 = 7927793) B7927793
theorem B1566027 : Blo 1564980 1566027 := bstep (se 1 (by rfl) ⟨1174520, by rfl⟩ : syracuseStep 1566027 = 2349041) B2349041
theorem B5948747 : Blo 1564980 5948747 := bstep (se 1 (by rfl) ⟨4461560, by rfl⟩ : syracuseStep 5948747 = 8923121) B8923121
theorem B1566039 : Blo 1564980 1566039 := bstep (se 1 (by rfl) ⟨1174529, by rfl⟩ : syracuseStep 1566039 = 2349059) B2349059
theorem B5948761 : Blo 1564980 5948761 := bstep (se 2 (by rfl) ⟨2230785, by rfl⟩ : syracuseStep 5948761 = 4461571) B4461571
theorem B1566059 : Blo 1564980 1566059 := bstep (se 1 (by rfl) ⟨1174544, by rfl⟩ : syracuseStep 1566059 = 2349089) B2349089
theorem B1566071 : Blo 1564980 1566071 := bstep (se 1 (by rfl) ⟨1174553, by rfl⟩ : syracuseStep 1566071 = 2349107) B2349107
theorem B1566091 : Blo 1564980 1566091 := bstep (se 1 (by rfl) ⟨1174568, by rfl⟩ : syracuseStep 1566091 = 2349137) B2349137
theorem B1762699 : Blo 1564980 1762699 := bstep (se 1 (by rfl) ⟨1322024, by rfl⟩ : syracuseStep 1762699 = 2644049) B2644049
theorem B7923095 : Blo 1564980 7923095 := bstep (se 1 (by rfl) ⟨5942321, by rfl⟩ : syracuseStep 7923095 = 11884643) B11884643
theorem B1566103 : Blo 1564980 1566103 := bstep (se 1 (by rfl) ⟨1174577, by rfl⟩ : syracuseStep 1566103 = 2349155) B2349155
theorem B1566123 : Blo 1564980 1566123 := bstep (se 1 (by rfl) ⟨1174592, by rfl⟩ : syracuseStep 1566123 = 2349185) B2349185
theorem B1566135 : Blo 1564980 1566135 := bstep (se 1 (by rfl) ⟨1174601, by rfl⟩ : syracuseStep 1566135 = 2349203) B2349203
theorem B1566155 : Blo 1564980 1566155 := bstep (se 1 (by rfl) ⟨1174616, by rfl⟩ : syracuseStep 1566155 = 2349233) B2349233
theorem B1566167 : Blo 1564980 1566167 := bstep (se 1 (by rfl) ⟨1174625, by rfl⟩ : syracuseStep 1566167 = 2349251) B2349251
theorem B3524057 : Blo 1564980 3524057 := bstep (se 2 (by rfl) ⟨1321521, by rfl⟩ : syracuseStep 3524057 = 2643043) B2643043
theorem B3573209 : Blo 1564980 3573209 := bstep (se 2 (by rfl) ⟨1339953, by rfl⟩ : syracuseStep 3573209 = 2679907) B2679907
theorem B1566187 : Blo 1564980 1566187 := bstep (se 1 (by rfl) ⟨1174640, by rfl⟩ : syracuseStep 1566187 = 2349281) B2349281
theorem B1566199 : Blo 1564980 1566199 := bstep (se 1 (by rfl) ⟨1174649, by rfl⟩ : syracuseStep 1566199 = 2349299) B2349299
theorem B1762807 : Blo 1564980 1762807 := bstep (se 1 (by rfl) ⟨1322105, by rfl⟩ : syracuseStep 1762807 = 2644211) B2644211
theorem B1566219 : Blo 1564980 1566219 := bstep (se 1 (by rfl) ⟨1174664, by rfl⟩ : syracuseStep 1566219 = 2349329) B2349329
theorem B1566231 : Blo 1564980 1566231 := bstep (se 1 (by rfl) ⟨1174673, by rfl⟩ : syracuseStep 1566231 = 2349347) B2349347
theorem B1566251 : Blo 1564980 1566251 := bstep (se 1 (by rfl) ⟨1174688, by rfl⟩ : syracuseStep 1566251 = 2349377) B2349377
theorem B3524147 : Blo 1564980 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B1566263 : Blo 1564980 1566263 := bstep (se 1 (by rfl) ⟨1174697, by rfl⟩ : syracuseStep 1566263 = 2349395) B2349395
theorem B25396811 : Blo 1564980 25396811 := bstep (se 1 (by rfl) ⟨19047608, by rfl⟩ : syracuseStep 25396811 = 38095217) B38095217
theorem B1566283 : Blo 1564980 1566283 := bstep (se 1 (by rfl) ⟨1174712, by rfl⟩ : syracuseStep 1566283 = 2349425) B2349425
theorem B1566295 : Blo 1564980 1566295 := bstep (se 1 (by rfl) ⟨1174721, by rfl⟩ : syracuseStep 1566295 = 2349443) B2349443
theorem B3524183 : Blo 1564980 3524183 := bstep (se 1 (by rfl) ⟨2643137, by rfl⟩ : syracuseStep 3524183 = 5286275) B5286275
theorem B5285465 : Blo 1564980 5285465 := bstep (se 2 (by rfl) ⟨1982049, by rfl⟩ : syracuseStep 5285465 = 3964099) B3964099
theorem B1566315 : Blo 1564980 1566315 := bstep (se 1 (by rfl) ⟨1174736, by rfl⟩ : syracuseStep 1566315 = 2349473) B2349473
theorem B1566327 : Blo 1564980 1566327 := bstep (se 1 (by rfl) ⟨1174745, by rfl⟩ : syracuseStep 1566327 = 2349491) B2349491
theorem B1566347 : Blo 1564980 1566347 := bstep (se 1 (by rfl) ⟨1174760, by rfl⟩ : syracuseStep 1566347 = 2349521) B2349521
theorem B1566359 : Blo 1564980 1566359 := bstep (se 1 (by rfl) ⟨1174769, by rfl⟩ : syracuseStep 1566359 = 2349539) B2349539
theorem B1566379 : Blo 1564980 1566379 := bstep (se 1 (by rfl) ⟨1174784, by rfl⟩ : syracuseStep 1566379 = 2349569) B2349569
theorem B1566391 : Blo 1564980 1566391 := bstep (se 1 (by rfl) ⟨1174793, by rfl⟩ : syracuseStep 1566391 = 2349587) B2349587
theorem B1566411 : Blo 1564980 1566411 := bstep (se 1 (by rfl) ⟨1174808, by rfl⟩ : syracuseStep 1566411 = 2349617) B2349617
theorem B1566423 : Blo 1564980 1566423 := bstep (se 1 (by rfl) ⟨1174817, by rfl⟩ : syracuseStep 1566423 = 2349635) B2349635
theorem B2229977 : Blo 1564980 2229977 := bstep (se 2 (by rfl) ⟨836241, by rfl⟩ : syracuseStep 2229977 = 1672483) B1672483
theorem B1566443 : Blo 1564980 1566443 := bstep (se 1 (by rfl) ⟨1174832, by rfl⟩ : syracuseStep 1566443 = 2349665) B2349665
theorem B1566455 : Blo 1564980 1566455 := bstep (se 1 (by rfl) ⟨1174841, by rfl⟩ : syracuseStep 1566455 = 2349683) B2349683
theorem B26773253 : Blo 1564980 26773253 := bstep (se 4 (by rfl) ⟨2509992, by rfl⟩ : syracuseStep 26773253 = 5019985) B5019985
theorem B3524363 : Blo 1564980 3524363 := bstep (se 1 (by rfl) ⟨2643272, by rfl⟩ : syracuseStep 3524363 = 5286545) B5286545
theorem B1566475 : Blo 1564980 1566475 := bstep (se 1 (by rfl) ⟨1174856, by rfl⟩ : syracuseStep 1566475 = 2349713) B2349713
theorem B1566487 : Blo 1564980 1566487 := bstep (se 1 (by rfl) ⟨1174865, by rfl⟩ : syracuseStep 1566487 = 2349731) B2349731
theorem B2115353 : Blo 1564980 2115353 := bstep (se 2 (by rfl) ⟨793257, by rfl⟩ : syracuseStep 2115353 = 1586515) B1586515
theorem B1566507 : Blo 1564980 1566507 := bstep (se 1 (by rfl) ⟨1174880, by rfl⟩ : syracuseStep 1566507 = 2349761) B2349761
theorem B1566519 : Blo 1564980 1566519 := bstep (se 1 (by rfl) ⟨1174889, by rfl⟩ : syracuseStep 1566519 = 2349779) B2349779
theorem B3524417 : Blo 1564980 3524417 := bstep (se 2 (by rfl) ⟨1321656, by rfl⟩ : syracuseStep 3524417 = 2643313) B2643313
theorem B1566539 : Blo 1564980 1566539 := bstep (se 1 (by rfl) ⟨1174904, by rfl⟩ : syracuseStep 1566539 = 2349809) B2349809
theorem B1566551 : Blo 1564980 1566551 := bstep (se 1 (by rfl) ⟨1174913, by rfl⟩ : syracuseStep 1566551 = 2349827) B2349827
theorem B1566571 : Blo 1564980 1566571 := bstep (se 1 (by rfl) ⟨1174928, by rfl⟩ : syracuseStep 1566571 = 2349857) B2349857
theorem B1566583 : Blo 1564980 1566583 := bstep (se 1 (by rfl) ⟨1174937, by rfl⟩ : syracuseStep 1566583 = 2349875) B2349875
theorem B3344257 : Blo 1564980 3344257 := bstep (se 2 (by rfl) ⟨1254096, by rfl⟩ : syracuseStep 3344257 = 2508193) B2508193
theorem B1566603 : Blo 1564980 1566603 := bstep (se 1 (by rfl) ⟨1174952, by rfl⟩ : syracuseStep 1566603 = 2349905) B2349905
theorem B1566615 : Blo 1564980 1566615 := bstep (se 1 (by rfl) ⟨1174961, by rfl⟩ : syracuseStep 1566615 = 2349923) B2349923
theorem B1566635 : Blo 1564980 1566635 := bstep (se 1 (by rfl) ⟨1174976, by rfl⟩ : syracuseStep 1566635 = 2349953) B2349953
theorem B1566647 : Blo 1564980 1566647 := bstep (se 1 (by rfl) ⟨1174985, by rfl⟩ : syracuseStep 1566647 = 2349971) B2349971
theorem B1566667 : Blo 1564980 1566667 := bstep (se 1 (by rfl) ⟨1175000, by rfl⟩ : syracuseStep 1566667 = 2350001) B2350001
theorem B1566679 : Blo 1564980 1566679 := bstep (se 1 (by rfl) ⟨1175009, by rfl⟩ : syracuseStep 1566679 = 2350019) B2350019
theorem B30107609 : Blo 1564980 30107609 := bstep (se 2 (by rfl) ⟨11290353, by rfl⟩ : syracuseStep 30107609 = 22580707) B22580707
theorem B11290585 : Blo 1564980 11290585 := bstep (se 2 (by rfl) ⟨4233969, by rfl⟩ : syracuseStep 11290585 = 8467939) B8467939
theorem B11896793 : Blo 1564980 11896793 := bstep (se 2 (by rfl) ⟨4461297, by rfl⟩ : syracuseStep 11896793 = 8922595) B8922595
theorem B1566699 : Blo 1564980 1566699 := bstep (se 1 (by rfl) ⟨1175024, by rfl⟩ : syracuseStep 1566699 = 2350049) B2350049
theorem B1566711 : Blo 1564980 1566711 := bstep (se 1 (by rfl) ⟨1175033, by rfl⟩ : syracuseStep 1566711 = 2350067) B2350067
theorem B1566731 : Blo 1564980 1566731 := bstep (se 1 (by rfl) ⟨1175048, by rfl⟩ : syracuseStep 1566731 = 2350097) B2350097
theorem B1566743 : Blo 1564980 1566743 := bstep (se 1 (by rfl) ⟨1175057, by rfl⟩ : syracuseStep 1566743 = 2350115) B2350115
theorem B3524633 : Blo 1564980 3524633 := bstep (se 2 (by rfl) ⟨1321737, by rfl⟩ : syracuseStep 3524633 = 2643475) B2643475
theorem B1566763 : Blo 1564980 1566763 := bstep (se 1 (by rfl) ⟨1175072, by rfl⟩ : syracuseStep 1566763 = 2350145) B2350145
theorem B1566775 : Blo 1564980 1566775 := bstep (se 1 (by rfl) ⟨1175081, by rfl⟩ : syracuseStep 1566775 = 2350163) B2350163
theorem B1566795 : Blo 1564980 1566795 := bstep (se 1 (by rfl) ⟨1175096, by rfl⟩ : syracuseStep 1566795 = 2350193) B2350193
theorem B1566807 : Blo 1564980 1566807 := bstep (se 1 (by rfl) ⟨1175105, by rfl⟩ : syracuseStep 1566807 = 2350211) B2350211
theorem B1673303 : Blo 1564980 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B20056157 : Blo 1564980 20056157 := bstep (se 3 (by rfl) ⟨3760529, by rfl⟩ : syracuseStep 20056157 = 7521059) B7521059
theorem B1566827 : Blo 1564980 1566827 := bstep (se 1 (by rfl) ⟨1175120, by rfl⟩ : syracuseStep 1566827 = 2350241) B2350241
theorem B3524723 : Blo 1564980 3524723 := bstep (se 1 (by rfl) ⟨2643542, by rfl⟩ : syracuseStep 3524723 = 5287085) B5287085
theorem B1566839 : Blo 1564980 1566839 := bstep (se 1 (by rfl) ⟨1175129, by rfl⟩ : syracuseStep 1566839 = 2350259) B2350259
theorem B1566859 : Blo 1564980 1566859 := bstep (se 1 (by rfl) ⟨1175144, by rfl⟩ : syracuseStep 1566859 = 2350289) B2350289
theorem B3524759 : Blo 1564980 3524759 := bstep (se 1 (by rfl) ⟨2643569, by rfl⟩ : syracuseStep 3524759 = 5287139) B5287139
theorem B1566871 : Blo 1564980 1566871 := bstep (se 1 (by rfl) ⟨1175153, by rfl⟩ : syracuseStep 1566871 = 2350307) B2350307
theorem B1566891 : Blo 1564980 1566891 := bstep (se 1 (by rfl) ⟨1175168, by rfl⟩ : syracuseStep 1566891 = 2350337) B2350337
theorem B8915123 : Blo 1564980 8915123 := bstep (se 1 (by rfl) ⟨6686342, by rfl⟩ : syracuseStep 8915123 = 13372685) B13372685
theorem B7522483 : Blo 1564980 7522483 := bstep (se 1 (by rfl) ⟨5641862, by rfl⟩ : syracuseStep 7522483 = 11283725) B11283725
theorem B1566903 : Blo 1564980 1566903 := bstep (se 1 (by rfl) ⟨1175177, by rfl⟩ : syracuseStep 1566903 = 2350355) B2350355
theorem B1566923 : Blo 1564980 1566923 := bstep (se 1 (by rfl) ⟨1175192, by rfl⟩ : syracuseStep 1566923 = 2350385) B2350385
theorem B1566935 : Blo 1564980 1566935 := bstep (se 1 (by rfl) ⟨1175201, by rfl⟩ : syracuseStep 1566935 = 2350403) B2350403
theorem B1566955 : Blo 1564980 1566955 := bstep (se 1 (by rfl) ⟨1175216, by rfl⟩ : syracuseStep 1566955 = 2350433) B2350433
theorem B1566967 : Blo 1564980 1566967 := bstep (se 1 (by rfl) ⟨1175225, by rfl⟩ : syracuseStep 1566967 = 2350451) B2350451
theorem B21416197 : Blo 1564980 21416197 := bstep (se 4 (by rfl) ⟨2007768, by rfl⟩ : syracuseStep 21416197 = 4015537) B4015537
theorem B5286167 : Blo 1564980 5286167 := bstep (se 1 (by rfl) ⟨3964625, by rfl⟩ : syracuseStep 5286167 = 7929251) B7929251
theorem B4458827 : Blo 1564980 4458827 := bstep (se 1 (by rfl) ⟨3344120, by rfl⟩ : syracuseStep 4458827 = 6688241) B6688241
theorem B3524939 : Blo 1564980 3524939 := bstep (se 1 (by rfl) ⟨2643704, by rfl⟩ : syracuseStep 3524939 = 5287409) B5287409
theorem B2230615 : Blo 1564980 2230615 := bstep (se 1 (by rfl) ⟨1672961, by rfl⟩ : syracuseStep 2230615 = 3345923) B3345923
theorem B3762521 : Blo 1564980 3762521 := bstep (se 2 (by rfl) ⟨1410945, by rfl⟩ : syracuseStep 3762521 = 2821891) B2821891
theorem B3524993 : Blo 1564980 3524993 := bstep (se 2 (by rfl) ⟨1321872, by rfl⟩ : syracuseStep 3524993 = 2643745) B2643745
theorem B10029491 : Blo 1564980 10029491 := bstep (se 1 (by rfl) ⟨7522118, by rfl⟩ : syracuseStep 10029491 = 15044237) B15044237
theorem B7932491 : Blo 1564980 7932491 := bstep (se 1 (by rfl) ⟨5949368, by rfl⟩ : syracuseStep 7932491 = 11898737) B11898737
theorem B3525209 : Blo 1564980 3525209 := bstep (se 2 (by rfl) ⟨1321953, by rfl⟩ : syracuseStep 3525209 = 2643907) B2643907
theorem B5646937 : Blo 1564980 5646937 := bstep (se 2 (by rfl) ⟨2117601, by rfl⟩ : syracuseStep 5646937 = 4235203) B4235203
theorem B10029719 : Blo 1564980 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B3525299 : Blo 1564980 3525299 := bstep (se 1 (by rfl) ⟨2643974, by rfl⟩ : syracuseStep 3525299 = 5287949) B5287949
theorem B3525335 : Blo 1564980 3525335 := bstep (se 1 (by rfl) ⟨2644001, by rfl⟩ : syracuseStep 3525335 = 5288003) B5288003
theorem B4459225 : Blo 1564980 4459225 := bstep (se 2 (by rfl) ⟨1672209, by rfl⟩ : syracuseStep 4459225 = 3344419) B3344419
theorem B5286707 : Blo 1564980 5286707 := bstep (se 1 (by rfl) ⟨3965030, by rfl⟩ : syracuseStep 5286707 = 7930061) B7930061
theorem B3345239 : Blo 1564980 3345239 := bstep (se 1 (by rfl) ⟨2508929, by rfl⟩ : syracuseStep 3345239 = 5017859) B5017859
theorem B3525515 : Blo 1564980 3525515 := bstep (se 1 (by rfl) ⟨2644136, by rfl⟩ : syracuseStep 3525515 = 5288273) B5288273
theorem B3525569 : Blo 1564980 3525569 := bstep (se 2 (by rfl) ⟨1322088, by rfl⟩ : syracuseStep 3525569 = 2644177) B2644177
theorem B20352035 : Blo 1564980 20352035 := bstep (se 1 (by rfl) ⟨15264026, by rfl⟩ : syracuseStep 20352035 = 30528053) B30528053
theorem B5286977 : Blo 1564980 5286977 := bstep (se 2 (by rfl) ⟨1982616, by rfl⟩ : syracuseStep 5286977 = 3965233) B3965233
theorem B2640971 : Blo 1564980 2640971 := bstep (se 1 (by rfl) ⟨1980728, by rfl⟩ : syracuseStep 2640971 = 3961457) B3961457
theorem B2641099 : Blo 1564980 2641099 := bstep (se 1 (by rfl) ⟨1980824, by rfl⟩ : syracuseStep 2641099 = 3961649) B3961649
theorem B2641241 : Blo 1564980 2641241 := bstep (se 2 (by rfl) ⟨990465, by rfl⟩ : syracuseStep 2641241 = 1980931) B1980931
theorem B3345803 : Blo 1564980 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B8465843 : Blo 1564980 8465843 := bstep (se 1 (by rfl) ⟨6349382, by rfl⟩ : syracuseStep 8465843 = 12698765) B12698765
theorem B2641369 : Blo 1564980 2641369 := bstep (se 2 (by rfl) ⟨990513, by rfl⟩ : syracuseStep 2641369 = 1981027) B1981027
theorem B5721617 : Blo 1564980 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B5287517 : Blo 1564980 5287517 := bstep (se 3 (by rfl) ⟨991409, by rfl⟩ : syracuseStep 5287517 = 1982819) B1982819
theorem B8916581 : Blo 1564980 8916581 := bstep (se 4 (by rfl) ⟨835929, by rfl⟩ : syracuseStep 8916581 = 1671859) B1671859
theorem B5942915 : Blo 1564980 5942915 := bstep (se 1 (by rfl) ⟨4457186, by rfl⟩ : syracuseStep 5942915 = 8914373) B8914373
theorem B5942929 : Blo 1564980 5942929 := bstep (se 2 (by rfl) ⟨2228598, by rfl⟩ : syracuseStep 5942929 = 4457197) B4457197
theorem B6352643 : Blo 1564980 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B3346265 : Blo 1564980 3346265 := bstep (se 2 (by rfl) ⟨1254849, by rfl⟩ : syracuseStep 3346265 = 2509699) B2509699
theorem B10030949 : Blo 1564980 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B4460467 : Blo 1564980 4460467 := bstep (se 1 (by rfl) ⟨3345350, by rfl⟩ : syracuseStep 4460467 = 6690701) B6690701
theorem B5943233 : Blo 1564980 5943233 := bstep (se 2 (by rfl) ⟨2228712, by rfl⟩ : syracuseStep 5943233 = 4457425) B4457425
theorem B2641943 : Blo 1564980 2641943 := bstep (se 1 (by rfl) ⟨1981457, by rfl⟩ : syracuseStep 2641943 = 3962915) B3962915
theorem B8917037 : Blo 1564980 8917037 := bstep (se 3 (by rfl) ⟨1671944, by rfl⟩ : syracuseStep 8917037 = 3343889) B3343889
theorem B2822273 : Blo 1564980 2822273 := bstep (se 2 (by rfl) ⟨1058352, by rfl⟩ : syracuseStep 2822273 = 2116705) B2116705
theorem B54235277 : Blo 1564980 54235277 := bstep (se 3 (by rfl) ⟨10169114, by rfl⟩ : syracuseStep 54235277 = 20338229) B20338229
theorem B2642071 : Blo 1564980 2642071 := bstep (se 1 (by rfl) ⟨1981553, by rfl⟩ : syracuseStep 2642071 = 3963107) B3963107
theorem B11890961 : Blo 1564980 11890961 := bstep (se 2 (by rfl) ⟨4459110, by rfl⟩ : syracuseStep 11890961 = 8918221) B8918221
theorem B22884707 : Blo 1564980 22884707 := bstep (se 1 (by rfl) ⟨17163530, by rfl⟩ : syracuseStep 22884707 = 34327061) B34327061
theorem B30110069 : Blo 1564980 30110069 := bstep (se 5 (by rfl) ⟨1411409, by rfl⟩ : syracuseStep 30110069 = 2822819) B2822819
theorem B15045041 : Blo 1564980 15045041 := bstep (se 2 (by rfl) ⟨5641890, by rfl⟩ : syracuseStep 15045041 = 11283781) B11283781
theorem B2347481 : Blo 1564980 2347481 := bstep (se 2 (by rfl) ⟨880305, by rfl⟩ : syracuseStep 2347481 = 1760611) B1760611
theorem B14291473 : Blo 1564980 14291473 := bstep (se 2 (by rfl) ⟨5359302, by rfl⟩ : syracuseStep 14291473 = 10718605) B10718605
theorem B2347595 : Blo 1564980 2347595 := bstep (se 1 (by rfl) ⟨1760696, by rfl⟩ : syracuseStep 2347595 = 3521393) B3521393
theorem B2347607 : Blo 1564980 2347607 := bstep (se 1 (by rfl) ⟨1760705, by rfl⟩ : syracuseStep 2347607 = 3521411) B3521411
theorem B5943901 : Blo 1564980 5943901 := bstep (se 3 (by rfl) ⟨1114481, by rfl⟩ : syracuseStep 5943901 = 2228963) B2228963
theorem B2347673 : Blo 1564980 2347673 := bstep (se 2 (by rfl) ⟨880377, by rfl⟩ : syracuseStep 2347673 = 1760755) B1760755
theorem B10310323 : Blo 1564980 10310323 := bstep (se 1 (by rfl) ⟨7732742, by rfl⟩ : syracuseStep 10310323 = 15465485) B15465485
theorem B14471885 : Blo 1564980 14471885 := bstep (se 3 (by rfl) ⟨2713478, by rfl⟩ : syracuseStep 14471885 = 5426957) B5426957
theorem B8917721 : Blo 1564980 8917721 := bstep (se 2 (by rfl) ⟨3344145, by rfl⟩ : syracuseStep 8917721 = 6688291) B6688291
theorem B2347787 : Blo 1564980 2347787 := bstep (se 1 (by rfl) ⟨1760840, by rfl⟩ : syracuseStep 2347787 = 3521681) B3521681
theorem B2642699 : Blo 1564980 2642699 := bstep (se 1 (by rfl) ⟨1982024, by rfl⟩ : syracuseStep 2642699 = 3964049) B3964049
theorem B2347799 : Blo 1564980 2347799 := bstep (se 1 (by rfl) ⟨1760849, by rfl⟩ : syracuseStep 2347799 = 3521699) B3521699
theorem B15258413 : Blo 1564980 15258413 := bstep (se 3 (by rfl) ⟨2860952, by rfl⟩ : syracuseStep 15258413 = 5721905) B5721905
theorem B2822987 : Blo 1564980 2822987 := bstep (se 1 (by rfl) ⟨2117240, by rfl⟩ : syracuseStep 2822987 = 4234481) B4234481
theorem B2347865 : Blo 1564980 2347865 := bstep (se 2 (by rfl) ⟨880449, by rfl⟩ : syracuseStep 2347865 = 1760899) B1760899
theorem B7926659 : Blo 1564980 7926659 := bstep (se 1 (by rfl) ⟨5944994, by rfl⟩ : syracuseStep 7926659 = 11889989) B11889989
theorem B2642827 : Blo 1564980 2642827 := bstep (se 1 (by rfl) ⟨1982120, by rfl⟩ : syracuseStep 2642827 = 3964241) B3964241
theorem B21418931 : Blo 1564980 21418931 := bstep (se 1 (by rfl) ⟨16064198, by rfl⟩ : syracuseStep 21418931 = 32128397) B32128397
theorem B2347979 : Blo 1564980 2347979 := bstep (se 1 (by rfl) ⟨1760984, by rfl⟩ : syracuseStep 2347979 = 3521969) B3521969
theorem B2347991 : Blo 1564980 2347991 := bstep (se 1 (by rfl) ⟨1760993, by rfl⟩ : syracuseStep 2347991 = 3521987) B3521987
theorem B4232153 : Blo 1564980 4232153 := bstep (se 2 (by rfl) ⟨1587057, by rfl⟩ : syracuseStep 4232153 = 3174115) B3174115
theorem B2348057 : Blo 1564980 2348057 := bstep (se 2 (by rfl) ⟨880521, by rfl⟩ : syracuseStep 2348057 = 1761043) B1761043
theorem B2642969 : Blo 1564980 2642969 := bstep (se 2 (by rfl) ⟨991113, by rfl⟩ : syracuseStep 2642969 = 1982227) B1982227
theorem B11293789 : Blo 1564980 11293789 := bstep (se 3 (by rfl) ⟨2117585, by rfl⟩ : syracuseStep 11293789 = 4235171) B4235171
theorem B2348171 : Blo 1564980 2348171 := bstep (se 1 (by rfl) ⟨1761128, by rfl⟩ : syracuseStep 2348171 = 3522257) B3522257
theorem B2348183 : Blo 1564980 2348183 := bstep (se 1 (by rfl) ⟨1761137, by rfl⟩ : syracuseStep 2348183 = 3522275) B3522275
theorem B2643097 : Blo 1564980 2643097 := bstep (se 2 (by rfl) ⟨991161, by rfl⟩ : syracuseStep 2643097 = 1982323) B1982323
theorem B6689965 : Blo 1564980 6689965 := bstep (se 3 (by rfl) ⟨1254368, by rfl⟩ : syracuseStep 6689965 = 2508737) B2508737
theorem B2348249 : Blo 1564980 2348249 := bstep (se 2 (by rfl) ⟨880593, by rfl⟩ : syracuseStep 2348249 = 1761187) B1761187
theorem B3962135 : Blo 1564980 3962135 := bstep (se 1 (by rfl) ⟨2971601, by rfl⟩ : syracuseStep 3962135 = 5943203) B5943203
theorem B2348363 : Blo 1564980 2348363 := bstep (se 1 (by rfl) ⟨1761272, by rfl⟩ : syracuseStep 2348363 = 3522545) B3522545
theorem B2348375 : Blo 1564980 2348375 := bstep (se 1 (by rfl) ⟨1761281, by rfl⟩ : syracuseStep 2348375 = 3522563) B3522563
theorem B11294045 : Blo 1564980 11294045 := bstep (se 3 (by rfl) ⟨2117633, by rfl⟩ : syracuseStep 11294045 = 4235267) B4235267
theorem B2348441 : Blo 1564980 2348441 := bstep (se 2 (by rfl) ⟨880665, by rfl⟩ : syracuseStep 2348441 = 1761331) B1761331
theorem B2348555 : Blo 1564980 2348555 := bstep (se 1 (by rfl) ⟨1761416, by rfl⟩ : syracuseStep 2348555 = 3522833) B3522833
theorem B2348567 : Blo 1564980 2348567 := bstep (se 1 (by rfl) ⟨1761425, by rfl⟩ : syracuseStep 2348567 = 3522851) B3522851
theorem B2348633 : Blo 1564980 2348633 := bstep (se 2 (by rfl) ⟨880737, by rfl⟩ : syracuseStep 2348633 = 1761475) B1761475
theorem B1586795 : Blo 1564980 1586795 := bstep (se 1 (by rfl) ⟨1190096, by rfl⟩ : syracuseStep 1586795 = 2380193) B2380193
theorem B1586827 : Blo 1564980 1586827 := bstep (se 1 (by rfl) ⟨1190120, by rfl⟩ : syracuseStep 1586827 = 2380241) B2380241
theorem B7141067 : Blo 1564980 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B2348747 : Blo 1564980 2348747 := bstep (se 1 (by rfl) ⟨1761560, by rfl⟩ : syracuseStep 2348747 = 3523121) B3523121
theorem B2348759 : Blo 1564980 2348759 := bstep (se 1 (by rfl) ⟨1761569, by rfl⟩ : syracuseStep 2348759 = 3523139) B3523139
theorem B2643671 : Blo 1564980 2643671 := bstep (se 1 (by rfl) ⟨1982753, by rfl⟩ : syracuseStep 2643671 = 3965507) B3965507
theorem B2348825 : Blo 1564980 2348825 := bstep (se 2 (by rfl) ⟨880809, by rfl⟩ : syracuseStep 2348825 = 1761619) B1761619
theorem B2643799 : Blo 1564980 2643799 := bstep (se 1 (by rfl) ⟨1982849, by rfl⟩ : syracuseStep 2643799 = 3965699) B3965699
theorem B5945177 : Blo 1564980 5945177 := bstep (se 2 (by rfl) ⟨2229441, by rfl⟩ : syracuseStep 5945177 = 4458883) B4458883
theorem B2348939 : Blo 1564980 2348939 := bstep (se 1 (by rfl) ⟨1761704, by rfl⟩ : syracuseStep 2348939 = 3523409) B3523409
theorem B2348951 : Blo 1564980 2348951 := bstep (se 1 (by rfl) ⟨1761713, by rfl⟩ : syracuseStep 2348951 = 3523427) B3523427
theorem B2381719 : Blo 1564980 2381719 := bstep (se 1 (by rfl) ⟨1786289, by rfl⟩ : syracuseStep 2381719 = 3572579) B3572579
theorem B5355443 : Blo 1564980 5355443 := bstep (se 1 (by rfl) ⟨4016582, by rfl⟩ : syracuseStep 5355443 = 8033165) B8033165
theorem B3962803 : Blo 1564980 3962803 := bstep (se 1 (by rfl) ⟨2972102, by rfl⟩ : syracuseStep 3962803 = 5944205) B5944205
theorem B2349017 : Blo 1564980 2349017 := bstep (se 2 (by rfl) ⟨880881, by rfl⟩ : syracuseStep 2349017 = 1761763) B1761763
theorem B3962945 : Blo 1564980 3962945 := bstep (se 2 (by rfl) ⟨1486104, by rfl⟩ : syracuseStep 3962945 = 2972209) B2972209
theorem B2971723 : Blo 1564980 2971723 := bstep (se 1 (by rfl) ⟨2228792, by rfl⟩ : syracuseStep 2971723 = 4457585) B4457585
theorem B2349131 : Blo 1564980 2349131 := bstep (se 1 (by rfl) ⟨1761848, by rfl⟩ : syracuseStep 2349131 = 3523697) B3523697
theorem B2349143 : Blo 1564980 2349143 := bstep (se 1 (by rfl) ⟨1761857, by rfl⟩ : syracuseStep 2349143 = 3523715) B3523715
theorem B2971799 : Blo 1564980 2971799 := bstep (se 1 (by rfl) ⟨2228849, by rfl⟩ : syracuseStep 2971799 = 4457699) B4457699
theorem B2349209 : Blo 1564980 2349209 := bstep (se 2 (by rfl) ⟨880953, by rfl⟩ : syracuseStep 2349209 = 1761907) B1761907
theorem B5282009 : Blo 1564980 5282009 := bstep (se 2 (by rfl) ⟨1980753, by rfl⟩ : syracuseStep 5282009 = 3961507) B3961507
theorem B2349323 : Blo 1564980 2349323 := bstep (se 1 (by rfl) ⟨1761992, by rfl⟩ : syracuseStep 2349323 = 3523985) B3523985
theorem B2349335 : Blo 1564980 2349335 := bstep (se 1 (by rfl) ⟨1762001, by rfl⟩ : syracuseStep 2349335 = 3524003) B3524003
theorem B2349401 : Blo 1564980 2349401 := bstep (se 2 (by rfl) ⟨881025, by rfl⟩ : syracuseStep 2349401 = 1762051) B1762051
theorem B1980875 : Blo 1564980 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B2349515 : Blo 1564980 2349515 := bstep (se 1 (by rfl) ⟨1762136, by rfl⟩ : syracuseStep 2349515 = 3524273) B3524273
theorem B2349527 : Blo 1564980 2349527 := bstep (se 1 (by rfl) ⟨1762145, by rfl⟩ : syracuseStep 2349527 = 3524291) B3524291
theorem B4291037 : Blo 1564980 4291037 := bstep (se 3 (by rfl) ⟨804569, by rfl⟩ : syracuseStep 4291037 = 1609139) B1609139
theorem B2349593 : Blo 1564980 2349593 := bstep (se 2 (by rfl) ⟨881097, by rfl⟩ : syracuseStep 2349593 = 1762195) B1762195
theorem B2349707 : Blo 1564980 2349707 := bstep (se 1 (by rfl) ⟨1762280, by rfl⟩ : syracuseStep 2349707 = 3524561) B3524561
theorem B2349719 : Blo 1564980 2349719 := bstep (se 1 (by rfl) ⟨1762289, by rfl⟩ : syracuseStep 2349719 = 3524579) B3524579
theorem B12057265 : Blo 1564980 12057265 := bstep (se 2 (by rfl) ⟨4521474, by rfl⟩ : syracuseStep 12057265 = 9042949) B9042949
theorem B5356211 : Blo 1564980 5356211 := bstep (se 1 (by rfl) ⟨4017158, by rfl⟩ : syracuseStep 5356211 = 8034317) B8034317
theorem B2349785 : Blo 1564980 2349785 := bstep (se 2 (by rfl) ⟨881169, by rfl⟩ : syracuseStep 2349785 = 1762339) B1762339
theorem B3521267 : Blo 1564980 3521267 := bstep (se 1 (by rfl) ⟨2640950, by rfl⟩ : syracuseStep 3521267 = 5281901) B5281901
theorem B3521303 : Blo 1564980 3521303 := bstep (se 1 (by rfl) ⟨2640977, by rfl⟩ : syracuseStep 3521303 = 5281955) B5281955
theorem B2972467 : Blo 1564980 2972467 := bstep (se 1 (by rfl) ⟨2229350, by rfl⟩ : syracuseStep 2972467 = 4458701) B4458701
theorem B2349899 : Blo 1564980 2349899 := bstep (se 1 (by rfl) ⟨1762424, by rfl⟩ : syracuseStep 2349899 = 3524849) B3524849
theorem B2349911 : Blo 1564980 2349911 := bstep (se 1 (by rfl) ⟨1762433, by rfl⟩ : syracuseStep 2349911 = 3524867) B3524867
theorem B6691673 : Blo 1564980 6691673 := bstep (se 2 (by rfl) ⟨2509377, by rfl⟩ : syracuseStep 6691673 = 5018755) B5018755
theorem B5282711 : Blo 1564980 5282711 := bstep (se 1 (by rfl) ⟨3962033, by rfl⟩ : syracuseStep 5282711 = 7924067) B7924067
theorem B2349977 : Blo 1564980 2349977 := bstep (se 2 (by rfl) ⟨881241, by rfl⟩ : syracuseStep 2349977 = 1762483) B1762483
theorem B114342853 : Blo 1564980 114342853 := bstep (se 4 (by rfl) ⟨10719642, by rfl⟩ : syracuseStep 114342853 = 21439285) B21439285
theorem B3521483 : Blo 1564980 3521483 := bstep (se 1 (by rfl) ⟨2641112, by rfl⟩ : syracuseStep 3521483 = 5282225) B5282225
theorem B4234187 : Blo 1564980 4234187 := bstep (se 1 (by rfl) ⟨3175640, by rfl⟩ : syracuseStep 4234187 = 6351281) B6351281
theorem B3521537 : Blo 1564980 3521537 := bstep (se 2 (by rfl) ⟨1320576, by rfl⟩ : syracuseStep 3521537 = 2641153) B2641153
theorem B2350091 : Blo 1564980 2350091 := bstep (se 1 (by rfl) ⟨1762568, by rfl⟩ : syracuseStep 2350091 = 3525137) B3525137
theorem B2972695 : Blo 1564980 2972695 := bstep (se 1 (by rfl) ⟨2229521, by rfl⟩ : syracuseStep 2972695 = 4459043) B4459043
theorem B2350103 : Blo 1564980 2350103 := bstep (se 1 (by rfl) ⟨1762577, by rfl⟩ : syracuseStep 2350103 = 3525155) B3525155
theorem B10329133 : Blo 1564980 10329133 := bstep (se 3 (by rfl) ⟨1936712, by rfl⟩ : syracuseStep 10329133 = 3873425) B3873425
theorem B10165313 : Blo 1564980 10165313 := bstep (se 2 (by rfl) ⟨3811992, by rfl⟩ : syracuseStep 10165313 = 7623985) B7623985
theorem B2350169 : Blo 1564980 2350169 := bstep (se 2 (by rfl) ⟨881313, by rfl⟩ : syracuseStep 2350169 = 1762627) B1762627
theorem B2972801 : Blo 1564980 2972801 := bstep (se 2 (by rfl) ⟨1114800, by rfl⟩ : syracuseStep 2972801 = 2229601) B2229601
theorem B1981579 : Blo 1564980 1981579 := bstep (se 1 (by rfl) ⟨1486184, by rfl⟩ : syracuseStep 1981579 = 2972369) B2972369
theorem B2350283 : Blo 1564980 2350283 := bstep (se 1 (by rfl) ⟨1762712, by rfl⟩ : syracuseStep 2350283 = 3525425) B3525425
theorem B2350295 : Blo 1564980 2350295 := bstep (se 1 (by rfl) ⟨1762721, by rfl⟩ : syracuseStep 2350295 = 3525443) B3525443
theorem B3521753 : Blo 1564980 3521753 := bstep (se 2 (by rfl) ⟨1320657, by rfl⟩ : syracuseStep 3521753 = 2641315) B2641315
theorem B13376785 : Blo 1564980 13376785 := bstep (se 2 (by rfl) ⟨5016294, by rfl⟩ : syracuseStep 13376785 = 10032589) B10032589
theorem B2972953 : Blo 1564980 2972953 := bstep (se 2 (by rfl) ⟨1114857, by rfl⟩ : syracuseStep 2972953 = 2229715) B2229715
theorem B2350361 : Blo 1564980 2350361 := bstep (se 2 (by rfl) ⟨881385, by rfl⟩ : syracuseStep 2350361 = 1762771) B1762771
theorem B3521843 : Blo 1564980 3521843 := bstep (se 1 (by rfl) ⟨2641382, by rfl⟩ : syracuseStep 3521843 = 5282765) B5282765
theorem B3964211 : Blo 1564980 3964211 := bstep (se 1 (by rfl) ⟨2973158, by rfl⟩ : syracuseStep 3964211 = 5946317) B5946317
theorem B3521879 : Blo 1564980 3521879 := bstep (se 1 (by rfl) ⟨2641409, by rfl⟩ : syracuseStep 3521879 = 5282819) B5282819
theorem B1981847 : Blo 1564980 1981847 := bstep (se 1 (by rfl) ⟨1486385, by rfl⟩ : syracuseStep 1981847 = 2972771) B2972771
theorem B1760683 : Blo 1564980 1760683 := bstep (se 1 (by rfl) ⟨1320512, by rfl⟩ : syracuseStep 1760683 = 2641025) B2641025
theorem B5283251 : Blo 1564980 5283251 := bstep (se 1 (by rfl) ⟨3962438, by rfl⟩ : syracuseStep 5283251 = 7924877) B7924877
theorem B5946803 : Blo 1564980 5946803 := bstep (se 1 (by rfl) ⟨4460102, by rfl⟩ : syracuseStep 5946803 = 8920205) B8920205
theorem B5946817 : Blo 1564980 5946817 := bstep (se 2 (by rfl) ⟨2230056, by rfl⟩ : syracuseStep 5946817 = 4460113) B4460113
theorem B3522059 : Blo 1564980 3522059 := bstep (se 1 (by rfl) ⟨2641544, by rfl⟩ : syracuseStep 3522059 = 5283089) B5283089
theorem B5643793 : Blo 1564980 5643793 := bstep (se 2 (by rfl) ⟨2116422, by rfl⟩ : syracuseStep 5643793 = 4232845) B4232845
theorem B1760791 : Blo 1564980 1760791 := bstep (se 1 (by rfl) ⟨1320593, by rfl⟩ : syracuseStep 1760791 = 2641187) B2641187
theorem B13377059 : Blo 1564980 13377059 := bstep (se 1 (by rfl) ⟨10032794, by rfl⟩ : syracuseStep 13377059 = 20065589) B20065589
theorem B3522113 : Blo 1564980 3522113 := bstep (se 2 (by rfl) ⟨1320792, by rfl⟩ : syracuseStep 3522113 = 2641585) B2641585
theorem B16293527 : Blo 1564980 16293527 := bstep (se 1 (by rfl) ⟨12220145, by rfl⟩ : syracuseStep 16293527 = 24440291) B24440291
theorem B5283521 : Blo 1564980 5283521 := bstep (se 2 (by rfl) ⟨1981320, by rfl⟩ : syracuseStep 5283521 = 3962641) B3962641
theorem B1760971 : Blo 1564980 1760971 := bstep (se 1 (by rfl) ⟨1320728, by rfl⟩ : syracuseStep 1760971 = 2641457) B2641457
theorem B6782737 : Blo 1564980 6782737 := bstep (se 2 (by rfl) ⟨2543526, by rfl⟩ : syracuseStep 6782737 = 5087053) B5087053
theorem B5644055 : Blo 1564980 5644055 := bstep (se 1 (by rfl) ⟨4233041, by rfl⟩ : syracuseStep 5644055 = 8466083) B8466083
theorem B3522329 : Blo 1564980 3522329 := bstep (se 2 (by rfl) ⟨1320873, by rfl⟩ : syracuseStep 3522329 = 2641747) B2641747
theorem B1761079 : Blo 1564980 1761079 := bstep (se 1 (by rfl) ⟨1320809, by rfl⟩ : syracuseStep 1761079 = 2641619) B2641619
theorem B3964747 : Blo 1564980 3964747 := bstep (se 1 (by rfl) ⟨2973560, by rfl⟩ : syracuseStep 3964747 = 5947121) B5947121
theorem B3522419 : Blo 1564980 3522419 := bstep (se 1 (by rfl) ⟨2641814, by rfl⟩ : syracuseStep 3522419 = 5283629) B5283629
theorem B9035651 : Blo 1564980 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B10166147 : Blo 1564980 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B3522455 : Blo 1564980 3522455 := bstep (se 1 (by rfl) ⟨2641841, by rfl⟩ : syracuseStep 3522455 = 5283683) B5283683
theorem B3964889 : Blo 1564980 3964889 := bstep (se 2 (by rfl) ⟨1486833, by rfl⟩ : syracuseStep 3964889 = 2973667) B2973667
theorem B1761259 : Blo 1564980 1761259 := bstep (se 1 (by rfl) ⟨1320944, by rfl⟩ : syracuseStep 1761259 = 2641889) B2641889
theorem B1761295 : Blo 1564980 1761295 := bstep (se 1 (by rfl) ⟨1320971, by rfl⟩ : syracuseStep 1761295 = 2641943) B2641943
theorem B7929899 : Blo 1564980 7929899 := bstep (se 1 (by rfl) ⟨5947424, by rfl⟩ : syracuseStep 7929899 = 11894849) B11894849
theorem B4456583 : Blo 1564980 4456583 := bstep (se 1 (by rfl) ⟨3342437, by rfl⟩ : syracuseStep 4456583 = 6684875) B6684875
theorem B3620999 : Blo 1564980 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B3522707 : Blo 1564980 3522707 := bstep (se 1 (by rfl) ⟨2642030, by rfl⟩ : syracuseStep 3522707 = 5284061) B5284061
theorem B2228411 : Blo 1564980 2228411 := bstep (se 1 (by rfl) ⟨1671308, by rfl⟩ : syracuseStep 2228411 = 3342617) B3342617
theorem B3522761 : Blo 1564980 3522761 := bstep (se 2 (by rfl) ⟨1321035, by rfl⟩ : syracuseStep 3522761 = 2642071) B2642071
theorem B1564987 : Blo 1564980 1564987 := bstep (se 1 (by rfl) ⟨1173740, by rfl⟩ : syracuseStep 1564987 = 2347481) B2347481
theorem B28574045 : Blo 1564980 28574045 := bstep (se 3 (by rfl) ⟨5357633, by rfl⟩ : syracuseStep 28574045 = 10715267) B10715267
theorem B1565063 : Blo 1564980 1565063 := bstep (se 1 (by rfl) ⟨1173797, by rfl⟩ : syracuseStep 1565063 = 2347595) B2347595
theorem B1565071 : Blo 1564980 1565071 := bstep (se 1 (by rfl) ⟨1173803, by rfl⟩ : syracuseStep 1565071 = 2347607) B2347607
theorem B1565115 : Blo 1564980 1565115 := bstep (se 1 (by rfl) ⟨1173836, by rfl⟩ : syracuseStep 1565115 = 2347673) B2347673
theorem B2974153 : Blo 1564980 2974153 := bstep (se 2 (by rfl) ⟨1115307, by rfl⟩ : syracuseStep 2974153 = 2230615) B2230615
theorem B1565191 : Blo 1564980 1565191 := bstep (se 1 (by rfl) ⟨1173893, by rfl⟩ : syracuseStep 1565191 = 2347787) B2347787
theorem B1761799 : Blo 1564980 1761799 := bstep (se 1 (by rfl) ⟨1321349, by rfl⟩ : syracuseStep 1761799 = 2642699) B2642699
theorem B1565199 : Blo 1564980 1565199 := bstep (se 1 (by rfl) ⟨1173899, by rfl⟩ : syracuseStep 1565199 = 2347799) B2347799
theorem B1565243 : Blo 1564980 1565243 := bstep (se 1 (by rfl) ⟨1173932, by rfl⟩ : syracuseStep 1565243 = 2347865) B2347865
theorem B5284439 : Blo 1564980 5284439 := bstep (se 1 (by rfl) ⟨3963329, by rfl⟩ : syracuseStep 5284439 = 7926659) B7926659
theorem B1565319 : Blo 1564980 1565319 := bstep (se 1 (by rfl) ⟨1173989, by rfl⟩ : syracuseStep 1565319 = 2347979) B2347979
theorem B1565327 : Blo 1564980 1565327 := bstep (se 1 (by rfl) ⟨1173995, by rfl⟩ : syracuseStep 1565327 = 2347991) B2347991
theorem B1565371 : Blo 1564980 1565371 := bstep (se 1 (by rfl) ⟨1174028, by rfl⟩ : syracuseStep 1565371 = 2348057) B2348057
theorem B1761979 : Blo 1564980 1761979 := bstep (se 1 (by rfl) ⟨1321484, by rfl⟩ : syracuseStep 1761979 = 2642969) B2642969
theorem B19055297 : Blo 1564980 19055297 := bstep (se 2 (by rfl) ⟨7145736, by rfl⟩ : syracuseStep 19055297 = 14291473) B14291473
theorem B8913665 : Blo 1564980 8913665 := bstep (se 2 (by rfl) ⟨3342624, by rfl⟩ : syracuseStep 8913665 = 6685249) B6685249
theorem B1565447 : Blo 1564980 1565447 := bstep (se 1 (by rfl) ⟨1174085, by rfl⟩ : syracuseStep 1565447 = 2348171) B2348171
theorem B1565455 : Blo 1564980 1565455 := bstep (se 1 (by rfl) ⟨1174091, by rfl⟩ : syracuseStep 1565455 = 2348183) B2348183
theorem B7529249 : Blo 1564980 7529249 := bstep (se 2 (by rfl) ⟨2823468, by rfl⟩ : syracuseStep 7529249 = 5646937) B5646937
theorem B2229049 : Blo 1564980 2229049 := bstep (se 2 (by rfl) ⟨835893, by rfl⟩ : syracuseStep 2229049 = 1671787) B1671787
theorem B1565499 : Blo 1564980 1565499 := bstep (se 1 (by rfl) ⟨1174124, by rfl⟩ : syracuseStep 1565499 = 2348249) B2348249
theorem B5948275 : Blo 1564980 5948275 := bstep (se 1 (by rfl) ⟨4461206, by rfl⟩ : syracuseStep 5948275 = 8922413) B8922413
theorem B1565575 : Blo 1564980 1565575 := bstep (se 1 (by rfl) ⟨1174181, by rfl⟩ : syracuseStep 1565575 = 2348363) B2348363
theorem B3523463 : Blo 1564980 3523463 := bstep (se 1 (by rfl) ⟨2642597, by rfl⟩ : syracuseStep 3523463 = 5285195) B5285195
theorem B3965831 : Blo 1564980 3965831 := bstep (se 1 (by rfl) ⟨2974373, by rfl⟩ : syracuseStep 3965831 = 5948747) B5948747
theorem B1565583 : Blo 1564980 1565583 := bstep (se 1 (by rfl) ⟨1174187, by rfl⟩ : syracuseStep 1565583 = 2348375) B2348375
theorem B7529363 : Blo 1564980 7529363 := bstep (se 1 (by rfl) ⟨5647022, by rfl⟩ : syracuseStep 7529363 = 11294045) B11294045
theorem B4457369 : Blo 1564980 4457369 := bstep (se 2 (by rfl) ⟨1671513, by rfl⟩ : syracuseStep 4457369 = 3343027) B3343027
theorem B13747097 : Blo 1564980 13747097 := bstep (se 2 (by rfl) ⟨5155161, by rfl⟩ : syracuseStep 13747097 = 10310323) B10310323
theorem B3965881 : Blo 1564980 3965881 := bstep (se 2 (by rfl) ⟨1487205, by rfl⟩ : syracuseStep 3965881 = 2974411) B2974411
theorem B1565627 : Blo 1564980 1565627 := bstep (se 1 (by rfl) ⟨1174220, by rfl⟩ : syracuseStep 1565627 = 2348441) B2348441
theorem B1565703 : Blo 1564980 1565703 := bstep (se 1 (by rfl) ⟨1174277, by rfl⟩ : syracuseStep 1565703 = 2348555) B2348555
theorem B1565711 : Blo 1564980 1565711 := bstep (se 1 (by rfl) ⟨1174283, by rfl⟩ : syracuseStep 1565711 = 2348567) B2348567
theorem B1565755 : Blo 1564980 1565755 := bstep (se 1 (by rfl) ⟨1174316, by rfl⟩ : syracuseStep 1565755 = 2348633) B2348633
theorem B3523643 : Blo 1564980 3523643 := bstep (se 1 (by rfl) ⟨2642732, by rfl⟩ : syracuseStep 3523643 = 5285465) B5285465
theorem B5284925 : Blo 1564980 5284925 := bstep (se 3 (by rfl) ⟨990923, by rfl⟩ : syracuseStep 5284925 = 1981847) B1981847
theorem B4760711 : Blo 1564980 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B1565831 : Blo 1564980 1565831 := bstep (se 1 (by rfl) ⟨1174373, by rfl⟩ : syracuseStep 1565831 = 2348747) B2348747
theorem B1565839 : Blo 1564980 1565839 := bstep (se 1 (by rfl) ⟨1174379, by rfl⟩ : syracuseStep 1565839 = 2348759) B2348759
theorem B1762447 : Blo 1564980 1762447 := bstep (se 1 (by rfl) ⟨1321835, by rfl⟩ : syracuseStep 1762447 = 2643671) B2643671
theorem B3523769 : Blo 1564980 3523769 := bstep (se 2 (by rfl) ⟨1321413, by rfl⟩ : syracuseStep 3523769 = 2642827) B2642827
theorem B1565883 : Blo 1564980 1565883 := bstep (se 1 (by rfl) ⟨1174412, by rfl⟩ : syracuseStep 1565883 = 2348825) B2348825
theorem B8914121 : Blo 1564980 8914121 := bstep (se 2 (by rfl) ⟨3342795, by rfl⟩ : syracuseStep 8914121 = 6685591) B6685591
theorem B1565959 : Blo 1564980 1565959 := bstep (se 1 (by rfl) ⟨1174469, by rfl⟩ : syracuseStep 1565959 = 2348939) B2348939
theorem B1565967 : Blo 1564980 1565967 := bstep (se 1 (by rfl) ⟨1174475, by rfl⟩ : syracuseStep 1565967 = 2348951) B2348951
theorem B1566011 : Blo 1564980 1566011 := bstep (se 1 (by rfl) ⟨1174508, by rfl⟩ : syracuseStep 1566011 = 2349017) B2349017
theorem B20071739 : Blo 1564980 20071739 := bstep (se 1 (by rfl) ⟨15053804, by rfl⟩ : syracuseStep 20071739 = 30107609) B30107609
theorem B7931195 : Blo 1564980 7931195 := bstep (se 1 (by rfl) ⟨5948396, by rfl⟩ : syracuseStep 7931195 = 11896793) B11896793
theorem B1566087 : Blo 1564980 1566087 := bstep (se 1 (by rfl) ⟨1174565, by rfl⟩ : syracuseStep 1566087 = 2349131) B2349131
theorem B1566095 : Blo 1564980 1566095 := bstep (se 1 (by rfl) ⟨1174571, by rfl⟩ : syracuseStep 1566095 = 2349143) B2349143
theorem B13772177 : Blo 1564980 13772177 := bstep (se 2 (by rfl) ⟨5164566, by rfl⟩ : syracuseStep 13772177 = 10329133) B10329133
theorem B13370771 : Blo 1564980 13370771 := bstep (se 1 (by rfl) ⟨10028078, by rfl⟩ : syracuseStep 13370771 = 20056157) B20056157
theorem B1566139 : Blo 1564980 1566139 := bstep (se 1 (by rfl) ⟨1174604, by rfl⟩ : syracuseStep 1566139 = 2349209) B2349209
theorem B15058385 : Blo 1564980 15058385 := bstep (se 2 (by rfl) ⟨5646894, by rfl⟩ : syracuseStep 15058385 = 11293789) B11293789
theorem B7931357 : Blo 1564980 7931357 := bstep (se 3 (by rfl) ⟨1487129, by rfl⟩ : syracuseStep 7931357 = 2974259) B2974259
theorem B1566215 : Blo 1564980 1566215 := bstep (se 1 (by rfl) ⟨1174661, by rfl⟩ : syracuseStep 1566215 = 2349323) B2349323
theorem B1566223 : Blo 1564980 1566223 := bstep (se 1 (by rfl) ⟨1174667, by rfl⟩ : syracuseStep 1566223 = 2349335) B2349335
theorem B3524111 : Blo 1564980 3524111 := bstep (se 1 (by rfl) ⟨2643083, by rfl⟩ : syracuseStep 3524111 = 5286167) B5286167
theorem B4458017 : Blo 1564980 4458017 := bstep (se 2 (by rfl) ⟨1671756, by rfl⟩ : syracuseStep 4458017 = 3343513) B3343513
theorem B3524129 : Blo 1564980 3524129 := bstep (se 2 (by rfl) ⟨1321548, by rfl⟩ : syracuseStep 3524129 = 2643097) B2643097
theorem B2508347 : Blo 1564980 2508347 := bstep (se 1 (by rfl) ⟨1881260, by rfl⟩ : syracuseStep 2508347 = 3762521) B3762521
theorem B1566267 : Blo 1564980 1566267 := bstep (se 1 (by rfl) ⟨1174700, by rfl⟩ : syracuseStep 1566267 = 2349401) B2349401
theorem B6686327 : Blo 1564980 6686327 := bstep (se 1 (by rfl) ⟨5014745, by rfl⟩ : syracuseStep 6686327 = 10029491) B10029491
theorem B1566343 : Blo 1564980 1566343 := bstep (se 1 (by rfl) ⟨1174757, by rfl⟩ : syracuseStep 1566343 = 2349515) B2349515
theorem B1566351 : Blo 1564980 1566351 := bstep (se 1 (by rfl) ⟨1174763, by rfl⟩ : syracuseStep 1566351 = 2349527) B2349527
theorem B2860691 : Blo 1564980 2860691 := bstep (se 1 (by rfl) ⟨2145518, by rfl⟩ : syracuseStep 2860691 = 4291037) B4291037
theorem B1566395 : Blo 1564980 1566395 := bstep (se 1 (by rfl) ⟨1174796, by rfl⟩ : syracuseStep 1566395 = 2349593) B2349593
theorem B17835713 : Blo 1564980 17835713 := bstep (se 2 (by rfl) ⟨6688392, by rfl⟩ : syracuseStep 17835713 = 13376785) B13376785
theorem B5015297 : Blo 1564980 5015297 := bstep (se 2 (by rfl) ⟨1880736, by rfl⟩ : syracuseStep 5015297 = 3761473) B3761473
theorem B1566471 : Blo 1564980 1566471 := bstep (se 1 (by rfl) ⟨1174853, by rfl⟩ : syracuseStep 1566471 = 2349707) B2349707
theorem B6686479 : Blo 1564980 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B1566479 : Blo 1564980 1566479 := bstep (se 1 (by rfl) ⟨1174859, by rfl⟩ : syracuseStep 1566479 = 2349719) B2349719
theorem B7931681 : Blo 1564980 7931681 := bstep (se 2 (by rfl) ⟨2974380, by rfl⟩ : syracuseStep 7931681 = 5948761) B5948761
theorem B1566523 : Blo 1564980 1566523 := bstep (se 1 (by rfl) ⟨1174892, by rfl⟩ : syracuseStep 1566523 = 2349785) B2349785
theorem B3524471 : Blo 1564980 3524471 := bstep (se 1 (by rfl) ⟨2643353, by rfl⟩ : syracuseStep 3524471 = 5286707) B5286707
theorem B1566599 : Blo 1564980 1566599 := bstep (se 1 (by rfl) ⟨1174949, by rfl⟩ : syracuseStep 1566599 = 2349899) B2349899
theorem B1566607 : Blo 1564980 1566607 := bstep (se 1 (by rfl) ⟨1174955, by rfl⟩ : syracuseStep 1566607 = 2349911) B2349911
theorem B1566651 : Blo 1564980 1566651 := bstep (se 1 (by rfl) ⟨1174988, by rfl⟩ : syracuseStep 1566651 = 2349977) B2349977
theorem B1566727 : Blo 1564980 1566727 := bstep (se 1 (by rfl) ⟨1175045, by rfl⟩ : syracuseStep 1566727 = 2350091) B2350091
theorem B1566735 : Blo 1564980 1566735 := bstep (se 1 (by rfl) ⟨1175051, by rfl⟩ : syracuseStep 1566735 = 2350103) B2350103
theorem B13568023 : Blo 1564980 13568023 := bstep (se 1 (by rfl) ⟨10176017, by rfl⟩ : syracuseStep 13568023 = 20352035) B20352035
theorem B6776875 : Blo 1564980 6776875 := bstep (se 1 (by rfl) ⟨5082656, by rfl⟩ : syracuseStep 6776875 = 10165313) B10165313
theorem B3524651 : Blo 1564980 3524651 := bstep (se 1 (by rfl) ⟨2643488, by rfl⟩ : syracuseStep 3524651 = 5286977) B5286977
theorem B1566779 : Blo 1564980 1566779 := bstep (se 1 (by rfl) ⟨1175084, by rfl⟩ : syracuseStep 1566779 = 2350169) B2350169
theorem B1566855 : Blo 1564980 1566855 := bstep (se 1 (by rfl) ⟨1175141, by rfl⟩ : syracuseStep 1566855 = 2350283) B2350283
theorem B1566863 : Blo 1564980 1566863 := bstep (se 1 (by rfl) ⟨1175147, by rfl⟩ : syracuseStep 1566863 = 2350295) B2350295
theorem B2115769 : Blo 1564980 2115769 := bstep (se 2 (by rfl) ⟨793413, by rfl⟩ : syracuseStep 2115769 = 1586827) B1586827
theorem B1566907 : Blo 1564980 1566907 := bstep (se 1 (by rfl) ⟨1175180, by rfl⟩ : syracuseStep 1566907 = 2350361) B2350361
theorem B7923905 : Blo 1564980 7923905 := bstep (se 2 (by rfl) ⟨2971464, by rfl⟩ : syracuseStep 7923905 = 5942929) B5942929
theorem B17844461 : Blo 1564980 17844461 := bstep (se 3 (by rfl) ⟨3345836, by rfl⟩ : syracuseStep 17844461 = 6691673) B6691673
theorem B2230535 : Blo 1564980 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B24095069 : Blo 1564980 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B3525011 : Blo 1564980 3525011 := bstep (se 1 (by rfl) ⟨2643758, by rfl⟩ : syracuseStep 3525011 = 5287517) B5287517
theorem B5286329 : Blo 1564980 5286329 := bstep (se 2 (by rfl) ⟨1982373, by rfl⟩ : syracuseStep 5286329 = 3964747) B3964747
theorem B3525065 : Blo 1564980 3525065 := bstep (se 2 (by rfl) ⟨1321899, by rfl⟩ : syracuseStep 3525065 = 2643799) B2643799
theorem B57117149 : Blo 1564980 57117149 := bstep (se 3 (by rfl) ⟨10709465, by rfl⟩ : syracuseStep 57117149 = 21418931) B21418931
theorem B14281181 : Blo 1564980 14281181 := bstep (se 3 (by rfl) ⟨2677721, by rfl⟩ : syracuseStep 14281181 = 5355443) B5355443
theorem B4459009 : Blo 1564980 4459009 := bstep (se 2 (by rfl) ⟨1672128, by rfl⟩ : syracuseStep 4459009 = 3344257) B3344257
theorem B3762703 : Blo 1564980 3762703 := bstep (se 1 (by rfl) ⟨2822027, by rfl⟩ : syracuseStep 3762703 = 5644055) B5644055
theorem B2230843 : Blo 1564980 2230843 := bstep (se 1 (by rfl) ⟨1673132, by rfl⟩ : syracuseStep 2230843 = 3346265) B3346265
theorem B6687299 : Blo 1564980 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B6777431 : Blo 1564980 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B38120129 : Blo 1564980 38120129 := bstep (se 2 (by rfl) ⟨14295048, by rfl⟩ : syracuseStep 38120129 = 28590097) B28590097
theorem B7932653 : Blo 1564980 7932653 := bstep (se 3 (by rfl) ⟨1487372, by rfl⟩ : syracuseStep 7932653 = 2974745) B2974745
theorem B22571891 : Blo 1564980 22571891 := bstep (se 1 (by rfl) ⟨16928918, by rfl⟩ : syracuseStep 22571891 = 33857837) B33857837
theorem B15256471 : Blo 1564980 15256471 := bstep (se 1 (by rfl) ⟨11442353, by rfl⟩ : syracuseStep 15256471 = 22884707) B22884707
theorem B10029977 : Blo 1564980 10029977 := bstep (se 2 (by rfl) ⟨3761241, by rfl⟩ : syracuseStep 10029977 = 7522483) B7522483
theorem B20073379 : Blo 1564980 20073379 := bstep (se 1 (by rfl) ⟨15055034, by rfl⟩ : syracuseStep 20073379 = 30110069) B30110069
theorem B10030027 : Blo 1564980 10030027 := bstep (se 1 (by rfl) ⟨7522520, by rfl⟩ : syracuseStep 10030027 = 15045041) B15045041
theorem B5647313 : Blo 1564980 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B5286923 : Blo 1564980 5286923 := bstep (se 1 (by rfl) ⟨3965192, by rfl⟩ : syracuseStep 5286923 = 7930385) B7930385
theorem B5287031 : Blo 1564980 5287031 := bstep (se 1 (by rfl) ⟨3965273, by rfl⟩ : syracuseStep 5287031 = 7930547) B7930547
theorem B2821435 : Blo 1564980 2821435 := bstep (se 1 (by rfl) ⟨2116076, by rfl⟩ : syracuseStep 2821435 = 4232153) B4232153
theorem B45165923 : Blo 1564980 45165923 := bstep (se 1 (by rfl) ⟨33874442, by rfl⟩ : syracuseStep 45165923 = 67748885) B67748885
theorem B7925201 : Blo 1564980 7925201 := bstep (se 2 (by rfl) ⟨2971950, by rfl⟩ : syracuseStep 7925201 = 5943901) B5943901
theorem B2641423 : Blo 1564980 2641423 := bstep (se 1 (by rfl) ⟨1981067, by rfl⟩ : syracuseStep 2641423 = 3962135) B3962135
theorem B16076353 : Blo 1564980 16076353 := bstep (se 2 (by rfl) ⟨6028632, by rfl⟩ : syracuseStep 16076353 = 12057265) B12057265
theorem B5287625 : Blo 1564980 5287625 := bstep (se 2 (by rfl) ⟨1982859, by rfl⟩ : syracuseStep 5287625 = 3965719) B3965719
theorem B152457137 : Blo 1564980 152457137 := bstep (se 2 (by rfl) ⟨57171426, by rfl⟩ : syracuseStep 152457137 = 114342853) B114342853
theorem B2641963 : Blo 1564980 2641963 := bstep (se 1 (by rfl) ⟨1981472, by rfl⟩ : syracuseStep 2641963 = 3962945) B3962945
theorem B5943415 : Blo 1564980 5943415 := bstep (se 1 (by rfl) ⟨4457561, by rfl⟩ : syracuseStep 5943415 = 8915123) B8915123
theorem B2642105 : Blo 1564980 2642105 := bstep (se 2 (by rfl) ⟨990789, by rfl⟩ : syracuseStep 2642105 = 1981579) B1981579
theorem B4231453 : Blo 1564980 4231453 := bstep (se 3 (by rfl) ⟨793397, by rfl⟩ : syracuseStep 4231453 = 1586795) B1586795
theorem B5288327 : Blo 1564980 5288327 := bstep (se 1 (by rfl) ⟨3966245, by rfl⟩ : syracuseStep 5288327 = 7932491) B7932491
theorem B14283229 : Blo 1564980 14283229 := bstep (se 3 (by rfl) ⟨2678105, by rfl⟩ : syracuseStep 14283229 = 5356211) B5356211
theorem B2347511 : Blo 1564980 2347511 := bstep (se 1 (by rfl) ⟨1760633, by rfl⟩ : syracuseStep 2347511 = 3521267) B3521267
theorem B2347535 : Blo 1564980 2347535 := bstep (se 1 (by rfl) ⟨1760651, by rfl⟩ : syracuseStep 2347535 = 3521303) B3521303
theorem B2347577 : Blo 1564980 2347577 := bstep (se 2 (by rfl) ⟨880341, by rfl⟩ : syracuseStep 2347577 = 1760683) B1760683
theorem B2347655 : Blo 1564980 2347655 := bstep (se 1 (by rfl) ⟨1760741, by rfl⟩ : syracuseStep 2347655 = 3521483) B3521483
theorem B2822791 : Blo 1564980 2822791 := bstep (se 1 (by rfl) ⟨2117093, by rfl⟩ : syracuseStep 2822791 = 4234187) B4234187
theorem B2347691 : Blo 1564980 2347691 := bstep (se 1 (by rfl) ⟨1760768, by rfl⟩ : syracuseStep 2347691 = 3521537) B3521537
theorem B7525057 : Blo 1564980 7525057 := bstep (se 2 (by rfl) ⟨2821896, by rfl⟩ : syracuseStep 7525057 = 5643793) B5643793
theorem B2347721 : Blo 1564980 2347721 := bstep (se 2 (by rfl) ⟨880395, by rfl⟩ : syracuseStep 2347721 = 1760791) B1760791
theorem B5640941 : Blo 1564980 5640941 := bstep (se 3 (by rfl) ⟨1057676, by rfl⟩ : syracuseStep 5640941 = 2115353) B2115353
theorem B2347835 : Blo 1564980 2347835 := bstep (se 1 (by rfl) ⟨1760876, by rfl⟩ : syracuseStep 2347835 = 3521753) B3521753
theorem B2347895 : Blo 1564980 2347895 := bstep (se 1 (by rfl) ⟨1760921, by rfl⟩ : syracuseStep 2347895 = 3521843) B3521843
theorem B2642807 : Blo 1564980 2642807 := bstep (se 1 (by rfl) ⟨1982105, by rfl⟩ : syracuseStep 2642807 = 3964211) B3964211
theorem B2347919 : Blo 1564980 2347919 := bstep (se 1 (by rfl) ⟨1760939, by rfl⟩ : syracuseStep 2347919 = 3521879) B3521879
theorem B2347961 : Blo 1564980 2347961 := bstep (se 2 (by rfl) ⟨880485, by rfl⟩ : syracuseStep 2347961 = 1760971) B1760971
theorem B2348039 : Blo 1564980 2348039 := bstep (se 1 (by rfl) ⟨1761029, by rfl⟩ : syracuseStep 2348039 = 3522059) B3522059
theorem B3814411 : Blo 1564980 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B8918039 : Blo 1564980 8918039 := bstep (se 1 (by rfl) ⟨6688529, by rfl⟩ : syracuseStep 8918039 = 13377059) B13377059
theorem B2348075 : Blo 1564980 2348075 := bstep (se 1 (by rfl) ⟨1761056, by rfl⟩ : syracuseStep 2348075 = 3522113) B3522113
theorem B5944387 : Blo 1564980 5944387 := bstep (se 1 (by rfl) ⟨4458290, by rfl⟩ : syracuseStep 5944387 = 8916581) B8916581
theorem B2348105 : Blo 1564980 2348105 := bstep (se 2 (by rfl) ⟨880539, by rfl⟩ : syracuseStep 2348105 = 1761079) B1761079
theorem B3961943 : Blo 1564980 3961943 := bstep (se 1 (by rfl) ⟨2971457, by rfl⟩ : syracuseStep 3961943 = 5942915) B5942915
theorem B2348219 : Blo 1564980 2348219 := bstep (se 1 (by rfl) ⟨1761164, by rfl⟩ : syracuseStep 2348219 = 3522329) B3522329
theorem B3175625 : Blo 1564980 3175625 := bstep (se 2 (by rfl) ⟨1190859, by rfl⟩ : syracuseStep 3175625 = 2381719) B2381719
theorem B2348279 : Blo 1564980 2348279 := bstep (se 1 (by rfl) ⟨1761209, by rfl⟩ : syracuseStep 2348279 = 3522419) B3522419
theorem B2348303 : Blo 1564980 2348303 := bstep (se 1 (by rfl) ⟨1761227, by rfl⟩ : syracuseStep 2348303 = 3522455) B3522455
theorem B15054113 : Blo 1564980 15054113 := bstep (se 2 (by rfl) ⟨5645292, by rfl⟩ : syracuseStep 15054113 = 11290585) B11290585
theorem B3962155 : Blo 1564980 3962155 := bstep (se 1 (by rfl) ⟨2971616, by rfl⟩ : syracuseStep 3962155 = 5943233) B5943233
theorem B2348345 : Blo 1564980 2348345 := bstep (se 2 (by rfl) ⟨880629, by rfl⟩ : syracuseStep 2348345 = 1761259) B1761259
theorem B2643259 : Blo 1564980 2643259 := bstep (se 1 (by rfl) ⟨1982444, by rfl⟩ : syracuseStep 2643259 = 3964889) B3964889
theorem B5944691 : Blo 1564980 5944691 := bstep (se 1 (by rfl) ⟨4458518, by rfl⟩ : syracuseStep 5944691 = 8917037) B8917037
theorem B2348423 : Blo 1564980 2348423 := bstep (se 1 (by rfl) ⟨1761317, by rfl⟩ : syracuseStep 2348423 = 3522635) B3522635
theorem B4461959 : Blo 1564980 4461959 := bstep (se 1 (by rfl) ⟨3346469, by rfl⟩ : syracuseStep 4461959 = 6692939) B6692939
theorem B2348459 : Blo 1564980 2348459 := bstep (se 1 (by rfl) ⟨1761344, by rfl⟩ : syracuseStep 2348459 = 3522689) B3522689
theorem B1881515 : Blo 1564980 1881515 := bstep (se 1 (by rfl) ⟨1411136, by rfl⟩ : syracuseStep 1881515 = 2822273) B2822273
theorem B36156851 : Blo 1564980 36156851 := bstep (se 1 (by rfl) ⟨27117638, by rfl⟩ : syracuseStep 36156851 = 54235277) B54235277
theorem B3962297 : Blo 1564980 3962297 := bstep (se 2 (by rfl) ⟨1485861, by rfl⟩ : syracuseStep 3962297 = 2971723) B2971723
theorem B2348489 : Blo 1564980 2348489 := bstep (se 2 (by rfl) ⟨880683, by rfl⟩ : syracuseStep 2348489 = 1761367) B1761367
theorem B2643401 : Blo 1564980 2643401 := bstep (se 2 (by rfl) ⟨991275, by rfl⟩ : syracuseStep 2643401 = 1982551) B1982551
theorem B7927307 : Blo 1564980 7927307 := bstep (se 1 (by rfl) ⟨5945480, by rfl⟩ : syracuseStep 7927307 = 11890961) B11890961
theorem B2348603 : Blo 1564980 2348603 := bstep (se 1 (by rfl) ⟨1761452, by rfl⟩ : syracuseStep 2348603 = 3522905) B3522905
theorem B4462141 : Blo 1564980 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B2348663 : Blo 1564980 2348663 := bstep (se 1 (by rfl) ⟨1761497, by rfl⟩ : syracuseStep 2348663 = 3522995) B3522995
theorem B4462199 : Blo 1564980 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B2348687 : Blo 1564980 2348687 := bstep (se 1 (by rfl) ⟨1761515, by rfl⟩ : syracuseStep 2348687 = 3523031) B3523031
theorem B7927469 : Blo 1564980 7927469 := bstep (se 3 (by rfl) ⟨1486400, by rfl⟩ : syracuseStep 7927469 = 2972801) B2972801
theorem B28554929 : Blo 1564980 28554929 := bstep (se 2 (by rfl) ⟨10708098, by rfl⟩ : syracuseStep 28554929 = 21416197) B21416197
theorem B2348729 : Blo 1564980 2348729 := bstep (se 2 (by rfl) ⟨880773, by rfl⟩ : syracuseStep 2348729 = 1761547) B1761547
theorem B2348807 : Blo 1564980 2348807 := bstep (se 1 (by rfl) ⟨1761605, by rfl⟩ : syracuseStep 2348807 = 3523211) B3523211
theorem B2348843 : Blo 1564980 2348843 := bstep (se 1 (by rfl) ⟨1761632, by rfl⟩ : syracuseStep 2348843 = 3523265) B3523265
theorem B9647923 : Blo 1564980 9647923 := bstep (se 1 (by rfl) ⟨7235942, by rfl⟩ : syracuseStep 9647923 = 14471885) B14471885
theorem B5945147 : Blo 1564980 5945147 := bstep (se 1 (by rfl) ⟨4458860, by rfl⟩ : syracuseStep 5945147 = 8917721) B8917721
theorem B4233019 : Blo 1564980 4233019 := bstep (se 1 (by rfl) ⟨3174764, by rfl⟩ : syracuseStep 4233019 = 6349529) B6349529
theorem B2348873 : Blo 1564980 2348873 := bstep (se 2 (by rfl) ⟨880827, by rfl⟩ : syracuseStep 2348873 = 1761655) B1761655
theorem B1881991 : Blo 1564980 1881991 := bstep (se 1 (by rfl) ⟨1411493, by rfl⟩ : syracuseStep 1881991 = 2822987) B2822987
theorem B5429177 : Blo 1564980 5429177 := bstep (se 2 (by rfl) ⟨2035941, by rfl⟩ : syracuseStep 5429177 = 4071883) B4071883
theorem B2348987 : Blo 1564980 2348987 := bstep (se 1 (by rfl) ⟨1761740, by rfl⟩ : syracuseStep 2348987 = 3523481) B3523481
theorem B2349047 : Blo 1564980 2349047 := bstep (se 1 (by rfl) ⟨1761785, by rfl⟩ : syracuseStep 2349047 = 3523571) B3523571
theorem B2349071 : Blo 1564980 2349071 := bstep (se 1 (by rfl) ⟨1761803, by rfl⟩ : syracuseStep 2349071 = 3523607) B3523607
theorem B2349113 : Blo 1564980 2349113 := bstep (se 2 (by rfl) ⟨880917, by rfl⟩ : syracuseStep 2349113 = 1761835) B1761835
theorem B2349191 : Blo 1564980 2349191 := bstep (se 1 (by rfl) ⟨1761893, by rfl⟩ : syracuseStep 2349191 = 3523787) B3523787
theorem B2644103 : Blo 1564980 2644103 := bstep (se 1 (by rfl) ⟨1983077, by rfl⟩ : syracuseStep 2644103 = 3966155) B3966155
theorem B2349227 : Blo 1564980 2349227 := bstep (se 1 (by rfl) ⟨1761920, by rfl⟩ : syracuseStep 2349227 = 3523841) B3523841
theorem B2349257 : Blo 1564980 2349257 := bstep (se 2 (by rfl) ⟨880971, by rfl⟩ : syracuseStep 2349257 = 1761943) B1761943
theorem B45177101 : Blo 1564980 45177101 := bstep (se 3 (by rfl) ⟨8470706, by rfl⟩ : syracuseStep 45177101 = 16941413) B16941413
theorem B5282063 : Blo 1564980 5282063 := bstep (se 1 (by rfl) ⟨3961547, by rfl⟩ : syracuseStep 5282063 = 7923095) B7923095
theorem B5945633 : Blo 1564980 5945633 := bstep (se 2 (by rfl) ⟨2229612, by rfl⟩ : syracuseStep 5945633 = 4459225) B4459225
theorem B2349371 : Blo 1564980 2349371 := bstep (se 1 (by rfl) ⟨1762028, by rfl⟩ : syracuseStep 2349371 = 3524057) B3524057
theorem B2382139 : Blo 1564980 2382139 := bstep (se 1 (by rfl) ⟨1786604, by rfl⟩ : syracuseStep 2382139 = 3573209) B3573209
theorem B2349431 : Blo 1564980 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B16931207 : Blo 1564980 16931207 := bstep (se 1 (by rfl) ⟨12698405, by rfl⟩ : syracuseStep 16931207 = 25396811) B25396811
theorem B2349455 : Blo 1564980 2349455 := bstep (se 1 (by rfl) ⟨1762091, by rfl⟩ : syracuseStep 2349455 = 3524183) B3524183
theorem B3963289 : Blo 1564980 3963289 := bstep (se 2 (by rfl) ⟨1486233, by rfl⟩ : syracuseStep 3963289 = 2972467) B2972467
theorem B2349497 : Blo 1564980 2349497 := bstep (se 2 (by rfl) ⟨881061, by rfl⟩ : syracuseStep 2349497 = 1762123) B1762123
theorem B22575581 : Blo 1564980 22575581 := bstep (se 3 (by rfl) ⟨4232921, by rfl⟩ : syracuseStep 22575581 = 8465843) B8465843
theorem B17848835 : Blo 1564980 17848835 := bstep (se 1 (by rfl) ⟨13386626, by rfl⟩ : syracuseStep 17848835 = 26773253) B26773253
theorem B2349575 : Blo 1564980 2349575 := bstep (se 1 (by rfl) ⟨1762181, by rfl⟩ : syracuseStep 2349575 = 3524363) B3524363
theorem B5282333 : Blo 1564980 5282333 := bstep (se 3 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 5282333 = 1980875) B1980875
theorem B2349611 : Blo 1564980 2349611 := bstep (se 1 (by rfl) ⟨1762208, by rfl⟩ : syracuseStep 2349611 = 3524417) B3524417
theorem B3963451 : Blo 1564980 3963451 := bstep (se 1 (by rfl) ⟨2972588, by rfl⟩ : syracuseStep 3963451 = 5945177) B5945177
theorem B2349641 : Blo 1564980 2349641 := bstep (se 2 (by rfl) ⟨881115, by rfl⟩ : syracuseStep 2349641 = 1762231) B1762231
theorem B2349755 : Blo 1564980 2349755 := bstep (se 1 (by rfl) ⟨1762316, by rfl⟩ : syracuseStep 2349755 = 3524633) B3524633
theorem B3963593 : Blo 1564980 3963593 := bstep (se 2 (by rfl) ⟨1486347, by rfl⟩ : syracuseStep 3963593 = 2972695) B2972695
theorem B2349815 : Blo 1564980 2349815 := bstep (se 1 (by rfl) ⟨1762361, by rfl⟩ : syracuseStep 2349815 = 3524723) B3524723
theorem B1981199 : Blo 1564980 1981199 := bstep (se 1 (by rfl) ⟨1485899, by rfl⟩ : syracuseStep 1981199 = 2971799) B2971799
theorem B2349839 : Blo 1564980 2349839 := bstep (se 1 (by rfl) ⟨1762379, by rfl⟩ : syracuseStep 2349839 = 3524759) B3524759
theorem B2349881 : Blo 1564980 2349881 := bstep (se 2 (by rfl) ⟨881205, by rfl⟩ : syracuseStep 2349881 = 1762411) B1762411
theorem B3521339 : Blo 1564980 3521339 := bstep (se 1 (by rfl) ⟨2641004, by rfl⟩ : syracuseStep 3521339 = 5282009) B5282009
theorem B2972551 : Blo 1564980 2972551 := bstep (se 1 (by rfl) ⟨2229413, by rfl⟩ : syracuseStep 2972551 = 4458827) B4458827
theorem B2349959 : Blo 1564980 2349959 := bstep (se 1 (by rfl) ⟨1762469, by rfl⟩ : syracuseStep 2349959 = 3524939) B3524939
theorem B8919953 : Blo 1564980 8919953 := bstep (se 2 (by rfl) ⟨3344982, by rfl⟩ : syracuseStep 8919953 = 6689965) B6689965
theorem B2349995 : Blo 1564980 2349995 := bstep (se 1 (by rfl) ⟨1762496, by rfl⟩ : syracuseStep 2349995 = 3524993) B3524993
theorem B3521465 : Blo 1564980 3521465 := bstep (se 2 (by rfl) ⟨1320549, by rfl⟩ : syracuseStep 3521465 = 2641099) B2641099
theorem B2350025 : Blo 1564980 2350025 := bstep (se 2 (by rfl) ⟨881259, by rfl⟩ : syracuseStep 2350025 = 1762519) B1762519
theorem B3963937 : Blo 1564980 3963937 := bstep (se 2 (by rfl) ⟨1486476, by rfl⟩ : syracuseStep 3963937 = 2972953) B2972953
theorem B2350139 : Blo 1564980 2350139 := bstep (se 1 (by rfl) ⟨1762604, by rfl⟩ : syracuseStep 2350139 = 3525209) B3525209
theorem B2350199 : Blo 1564980 2350199 := bstep (se 1 (by rfl) ⟨1762649, by rfl⟩ : syracuseStep 2350199 = 3525299) B3525299
theorem B2350223 : Blo 1564980 2350223 := bstep (se 1 (by rfl) ⟨1762667, by rfl⟩ : syracuseStep 2350223 = 3525335) B3525335
theorem B2350265 : Blo 1564980 2350265 := bstep (se 2 (by rfl) ⟨881349, by rfl⟩ : syracuseStep 2350265 = 1762699) B1762699
theorem B5946605 : Blo 1564980 5946605 := bstep (se 3 (by rfl) ⟨1114988, by rfl⟩ : syracuseStep 5946605 = 2229977) B2229977
theorem B7929089 : Blo 1564980 7929089 := bstep (se 2 (by rfl) ⟨2973408, by rfl⟩ : syracuseStep 7929089 = 5946817) B5946817
theorem B2350343 : Blo 1564980 2350343 := bstep (se 1 (by rfl) ⟨1762757, by rfl⟩ : syracuseStep 2350343 = 3525515) B3525515
theorem B3521807 : Blo 1564980 3521807 := bstep (se 1 (by rfl) ⟨2641355, by rfl⟩ : syracuseStep 3521807 = 5282711) B5282711
theorem B3521825 : Blo 1564980 3521825 := bstep (se 2 (by rfl) ⟨1320684, by rfl⟩ : syracuseStep 3521825 = 2641369) B2641369
theorem B2350379 : Blo 1564980 2350379 := bstep (se 1 (by rfl) ⟨1762784, by rfl⟩ : syracuseStep 2350379 = 3525569) B3525569
theorem B2350409 : Blo 1564980 2350409 := bstep (se 2 (by rfl) ⟨881403, by rfl⟩ : syracuseStep 2350409 = 1762807) B1762807
theorem B1760647 : Blo 1564980 1760647 := bstep (se 1 (by rfl) ⟨1320485, by rfl⟩ : syracuseStep 1760647 = 2640971) B2640971
theorem B40689101 : Blo 1564980 40689101 := bstep (se 3 (by rfl) ⟨7629206, by rfl⟩ : syracuseStep 40689101 = 15258413) B15258413
theorem B1760827 : Blo 1564980 1760827 := bstep (se 1 (by rfl) ⟨1320620, by rfl⟩ : syracuseStep 1760827 = 2641241) B2641241
theorem B8920637 : Blo 1564980 8920637 := bstep (se 3 (by rfl) ⟨1672619, by rfl⟩ : syracuseStep 8920637 = 3345239) B3345239
theorem B3522167 : Blo 1564980 3522167 := bstep (se 1 (by rfl) ⟨2641625, by rfl⟩ : syracuseStep 3522167 = 5283251) B5283251
theorem B3964535 : Blo 1564980 3964535 := bstep (se 1 (by rfl) ⟨2973401, by rfl⟩ : syracuseStep 3964535 = 5946803) B5946803
theorem B9043649 : Blo 1564980 9043649 := bstep (se 2 (by rfl) ⟨3391368, by rfl⟩ : syracuseStep 9043649 = 6782737) B6782737
theorem B10862351 : Blo 1564980 10862351 := bstep (se 1 (by rfl) ⟨8146763, by rfl⟩ : syracuseStep 10862351 = 16293527) B16293527
theorem B3522347 : Blo 1564980 3522347 := bstep (se 1 (by rfl) ⟨2641760, by rfl⟩ : syracuseStep 3522347 = 5283521) B5283521
theorem B4235095 : Blo 1564980 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B5283737 : Blo 1564980 5283737 := bstep (se 2 (by rfl) ⟨1981401, by rfl⟩ : syracuseStep 5283737 = 3962803) B3962803
theorem B5947289 : Blo 1564980 5947289 := bstep (se 2 (by rfl) ⟨2230233, by rfl⟩ : syracuseStep 5947289 = 4460467) B4460467
theorem B3522617 : Blo 1564980 3522617 := bstep (se 2 (by rfl) ⟨1320981, by rfl⟩ : syracuseStep 3522617 = 2641963) B2641963
theorem B1761403 : Blo 1564980 1761403 := bstep (se 1 (by rfl) ⟨1321052, by rfl⟩ : syracuseStep 1761403 = 2642105) B2642105
theorem B36143333 : Blo 1564980 36143333 := bstep (se 4 (by rfl) ⟨3388437, by rfl⟩ : syracuseStep 36143333 = 6776875) B6776875
theorem B1565007 : Blo 1564980 1565007 := bstep (se 1 (by rfl) ⟨1173755, by rfl⟩ : syracuseStep 1565007 = 2347511) B2347511
theorem B1565023 : Blo 1564980 1565023 := bstep (se 1 (by rfl) ⟨1173767, by rfl⟩ : syracuseStep 1565023 = 2347535) B2347535
theorem B1565051 : Blo 1564980 1565051 := bstep (se 1 (by rfl) ⟨1173788, by rfl⟩ : syracuseStep 1565051 = 2347577) B2347577
theorem B3522959 : Blo 1564980 3522959 := bstep (se 1 (by rfl) ⟨2642219, by rfl⟩ : syracuseStep 3522959 = 5284439) B5284439
theorem B1565103 : Blo 1564980 1565103 := bstep (se 1 (by rfl) ⟨1173827, by rfl⟩ : syracuseStep 1565103 = 2347655) B2347655
theorem B1565127 : Blo 1564980 1565127 := bstep (se 1 (by rfl) ⟨1173845, by rfl⟩ : syracuseStep 1565127 = 2347691) B2347691
theorem B1565147 : Blo 1564980 1565147 := bstep (se 1 (by rfl) ⟨1173860, by rfl⟩ : syracuseStep 1565147 = 2347721) B2347721
theorem B3760627 : Blo 1564980 3760627 := bstep (se 1 (by rfl) ⟨2820470, by rfl⟩ : syracuseStep 3760627 = 5640941) B5640941
theorem B5284385 : Blo 1564980 5284385 := bstep (se 2 (by rfl) ⟨1981644, by rfl⟩ : syracuseStep 5284385 = 3963289) B3963289
theorem B1565223 : Blo 1564980 1565223 := bstep (se 1 (by rfl) ⟨1173917, by rfl⟩ : syracuseStep 1565223 = 2347835) B2347835
theorem B1565263 : Blo 1564980 1565263 := bstep (se 1 (by rfl) ⟨1173947, by rfl⟩ : syracuseStep 1565263 = 2347895) B2347895
theorem B1761871 : Blo 1564980 1761871 := bstep (se 1 (by rfl) ⟨1321403, by rfl⟩ : syracuseStep 1761871 = 2642807) B2642807
theorem B1565279 : Blo 1564980 1565279 := bstep (se 1 (by rfl) ⟨1173959, by rfl⟩ : syracuseStep 1565279 = 2347919) B2347919
theorem B3965537 : Blo 1564980 3965537 := bstep (se 2 (by rfl) ⟨1487076, by rfl⟩ : syracuseStep 3965537 = 2974153) B2974153
theorem B1565307 : Blo 1564980 1565307 := bstep (se 1 (by rfl) ⟨1173980, by rfl⟩ : syracuseStep 1565307 = 2347961) B2347961
theorem B1565359 : Blo 1564980 1565359 := bstep (se 1 (by rfl) ⟨1174019, by rfl⟩ : syracuseStep 1565359 = 2348039) B2348039
theorem B5948093 : Blo 1564980 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B1565383 : Blo 1564980 1565383 := bstep (se 1 (by rfl) ⟨1174037, by rfl⟩ : syracuseStep 1565383 = 2348075) B2348075
theorem B3523283 : Blo 1564980 3523283 := bstep (se 1 (by rfl) ⟨2642462, by rfl⟩ : syracuseStep 3523283 = 5284925) B5284925
theorem B1565403 : Blo 1564980 1565403 := bstep (se 1 (by rfl) ⟨1174052, by rfl⟩ : syracuseStep 1565403 = 2348105) B2348105
theorem B5284601 : Blo 1564980 5284601 := bstep (se 2 (by rfl) ⟨1981725, by rfl⟩ : syracuseStep 5284601 = 3963451) B3963451
theorem B2974457 : Blo 1564980 2974457 := bstep (se 2 (by rfl) ⟨1115421, by rfl⟩ : syracuseStep 2974457 = 2230843) B2230843
theorem B1565479 : Blo 1564980 1565479 := bstep (se 1 (by rfl) ⟨1174109, by rfl⟩ : syracuseStep 1565479 = 2348219) B2348219
theorem B1565519 : Blo 1564980 1565519 := bstep (se 1 (by rfl) ⟨1174139, by rfl⟩ : syracuseStep 1565519 = 2348279) B2348279
theorem B1565535 : Blo 1564980 1565535 := bstep (se 1 (by rfl) ⟨1174151, by rfl⟩ : syracuseStep 1565535 = 2348303) B2348303
theorem B10036075 : Blo 1564980 10036075 := bstep (se 1 (by rfl) ⟨7527056, by rfl⟩ : syracuseStep 10036075 = 15054113) B15054113
theorem B1565563 : Blo 1564980 1565563 := bstep (se 1 (by rfl) ⟨1174172, by rfl⟩ : syracuseStep 1565563 = 2348345) B2348345
theorem B1565615 : Blo 1564980 1565615 := bstep (se 1 (by rfl) ⟨1174211, by rfl⟩ : syracuseStep 1565615 = 2348423) B2348423
theorem B2974639 : Blo 1564980 2974639 := bstep (se 1 (by rfl) ⟨2230979, by rfl⟩ : syracuseStep 2974639 = 4461959) B4461959
theorem B8913847 : Blo 1564980 8913847 := bstep (se 1 (by rfl) ⟨6685385, by rfl⟩ : syracuseStep 8913847 = 13370771) B13370771
theorem B1565639 : Blo 1564980 1565639 := bstep (se 1 (by rfl) ⟨1174229, by rfl⟩ : syracuseStep 1565639 = 2348459) B2348459
theorem B1565659 : Blo 1564980 1565659 := bstep (se 1 (by rfl) ⟨1174244, by rfl⟩ : syracuseStep 1565659 = 2348489) B2348489
theorem B1762267 : Blo 1564980 1762267 := bstep (se 1 (by rfl) ⟨1321700, by rfl⟩ : syracuseStep 1762267 = 2643401) B2643401
theorem B5284871 : Blo 1564980 5284871 := bstep (se 1 (by rfl) ⟨3963653, by rfl⟩ : syracuseStep 5284871 = 7927307) B7927307
theorem B1565735 : Blo 1564980 1565735 := bstep (se 1 (by rfl) ⟨1174301, by rfl⟩ : syracuseStep 1565735 = 2348603) B2348603
theorem B4457551 : Blo 1564980 4457551 := bstep (se 1 (by rfl) ⟨3343163, by rfl⟩ : syracuseStep 4457551 = 6686327) B6686327
theorem B1565775 : Blo 1564980 1565775 := bstep (se 1 (by rfl) ⟨1174331, by rfl⟩ : syracuseStep 1565775 = 2348663) B2348663
theorem B2974799 : Blo 1564980 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B1565791 : Blo 1564980 1565791 := bstep (se 1 (by rfl) ⟨1174343, by rfl⟩ : syracuseStep 1565791 = 2348687) B2348687
theorem B5284979 : Blo 1564980 5284979 := bstep (se 1 (by rfl) ⟨3963734, by rfl⟩ : syracuseStep 5284979 = 7927469) B7927469
theorem B1565819 : Blo 1564980 1565819 := bstep (se 1 (by rfl) ⟨1174364, by rfl⟩ : syracuseStep 1565819 = 2348729) B2348729
theorem B7931033 : Blo 1564980 7931033 := bstep (se 2 (by rfl) ⟨2974137, by rfl⟩ : syracuseStep 7931033 = 5948275) B5948275
theorem B3343531 : Blo 1564980 3343531 := bstep (se 1 (by rfl) ⟨2507648, by rfl⟩ : syracuseStep 3343531 = 5015297) B5015297
theorem B1565871 : Blo 1564980 1565871 := bstep (se 1 (by rfl) ⟨1174403, by rfl⟩ : syracuseStep 1565871 = 2348807) B2348807
theorem B1565895 : Blo 1564980 1565895 := bstep (se 1 (by rfl) ⟨1174421, by rfl⟩ : syracuseStep 1565895 = 2348843) B2348843
theorem B20341961 : Blo 1564980 20341961 := bstep (se 2 (by rfl) ⟨7628235, by rfl⟩ : syracuseStep 20341961 = 15256471) B15256471
theorem B108504269 : Blo 1564980 108504269 := bstep (se 3 (by rfl) ⟨20344550, by rfl⟩ : syracuseStep 108504269 = 40689101) B40689101
theorem B26764505 : Blo 1564980 26764505 := bstep (se 2 (by rfl) ⟨10036689, by rfl⟩ : syracuseStep 26764505 = 20073379) B20073379
theorem B1565915 : Blo 1564980 1565915 := bstep (se 1 (by rfl) ⟨1174436, by rfl⟩ : syracuseStep 1565915 = 2348873) B2348873
theorem B1565991 : Blo 1564980 1565991 := bstep (se 1 (by rfl) ⟨1174493, by rfl⟩ : syracuseStep 1565991 = 2348987) B2348987
theorem B1566031 : Blo 1564980 1566031 := bstep (se 1 (by rfl) ⟨1174523, by rfl⟩ : syracuseStep 1566031 = 2349047) B2349047
theorem B1566047 : Blo 1564980 1566047 := bstep (se 1 (by rfl) ⟨1174535, by rfl⟩ : syracuseStep 1566047 = 2349071) B2349071
theorem B1566075 : Blo 1564980 1566075 := bstep (se 1 (by rfl) ⟨1174556, by rfl⟩ : syracuseStep 1566075 = 2349113) B2349113
theorem B5285249 : Blo 1564980 5285249 := bstep (se 2 (by rfl) ⟨1981968, by rfl⟩ : syracuseStep 5285249 = 3963937) B3963937
theorem B11888045 : Blo 1564980 11888045 := bstep (se 3 (by rfl) ⟨2229008, by rfl⟩ : syracuseStep 11888045 = 4458017) B4458017
theorem B1566127 : Blo 1564980 1566127 := bstep (se 1 (by rfl) ⟨1174595, by rfl⟩ : syracuseStep 1566127 = 2349191) B2349191
theorem B1762735 : Blo 1564980 1762735 := bstep (se 1 (by rfl) ⟨1322051, by rfl⟩ : syracuseStep 1762735 = 2644103) B2644103
theorem B1566151 : Blo 1564980 1566151 := bstep (se 1 (by rfl) ⟨1174613, by rfl⟩ : syracuseStep 1566151 = 2349227) B2349227
theorem B1566171 : Blo 1564980 1566171 := bstep (se 1 (by rfl) ⟨1174628, by rfl⟩ : syracuseStep 1566171 = 2349257) B2349257
theorem B11896307 : Blo 1564980 11896307 := bstep (se 1 (by rfl) ⟨8922230, by rfl⟩ : syracuseStep 11896307 = 17844461) B17844461
theorem B1566247 : Blo 1564980 1566247 := bstep (se 1 (by rfl) ⟨1174685, by rfl⟩ : syracuseStep 1566247 = 2349371) B2349371
theorem B1566287 : Blo 1564980 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B1566303 : Blo 1564980 1566303 := bstep (se 1 (by rfl) ⟨1174727, by rfl⟩ : syracuseStep 1566303 = 2349455) B2349455
theorem B3524219 : Blo 1564980 3524219 := bstep (se 1 (by rfl) ⟨2643164, by rfl⟩ : syracuseStep 3524219 = 5286329) B5286329
theorem B1566331 : Blo 1564980 1566331 := bstep (se 1 (by rfl) ⟨1174748, by rfl⟩ : syracuseStep 1566331 = 2349497) B2349497
theorem B38078099 : Blo 1564980 38078099 := bstep (se 1 (by rfl) ⟨28558574, by rfl⟩ : syracuseStep 38078099 = 57117149) B57117149
theorem B9520787 : Blo 1564980 9520787 := bstep (se 1 (by rfl) ⟨7140590, by rfl⟩ : syracuseStep 9520787 = 14281181) B14281181
theorem B15050387 : Blo 1564980 15050387 := bstep (se 1 (by rfl) ⟨11287790, by rfl⟩ : syracuseStep 15050387 = 22575581) B22575581
theorem B1566383 : Blo 1564980 1566383 := bstep (se 1 (by rfl) ⟨1174787, by rfl⟩ : syracuseStep 1566383 = 2349575) B2349575
theorem B1566407 : Blo 1564980 1566407 := bstep (se 1 (by rfl) ⟨1174805, by rfl⟩ : syracuseStep 1566407 = 2349611) B2349611
theorem B1566427 : Blo 1564980 1566427 := bstep (se 1 (by rfl) ⟨1174820, by rfl⟩ : syracuseStep 1566427 = 2349641) B2349641
theorem B7628509 : Blo 1564980 7628509 := bstep (se 3 (by rfl) ⟨1430345, by rfl⟩ : syracuseStep 7628509 = 2860691) B2860691
theorem B3524345 : Blo 1564980 3524345 := bstep (se 2 (by rfl) ⟨1321629, by rfl⟩ : syracuseStep 3524345 = 2643259) B2643259
theorem B1566503 : Blo 1564980 1566503 := bstep (se 1 (by rfl) ⟨1174877, by rfl⟩ : syracuseStep 1566503 = 2349755) B2349755
theorem B25413419 : Blo 1564980 25413419 := bstep (se 1 (by rfl) ⟨19060064, by rfl⟩ : syracuseStep 25413419 = 38120129) B38120129
theorem B1566543 : Blo 1564980 1566543 := bstep (se 1 (by rfl) ⟨1174907, by rfl⟩ : syracuseStep 1566543 = 2349815) B2349815
theorem B1566559 : Blo 1564980 1566559 := bstep (se 1 (by rfl) ⟨1174919, by rfl⟩ : syracuseStep 1566559 = 2349839) B2349839
theorem B1566587 : Blo 1564980 1566587 := bstep (se 1 (by rfl) ⟨1174940, by rfl⟩ : syracuseStep 1566587 = 2349881) B2349881
theorem B1566639 : Blo 1564980 1566639 := bstep (se 1 (by rfl) ⟨1174979, by rfl⟩ : syracuseStep 1566639 = 2349959) B2349959
theorem B6686651 : Blo 1564980 6686651 := bstep (se 1 (by rfl) ⟨5014988, by rfl⟩ : syracuseStep 6686651 = 10029977) B10029977
theorem B1566663 : Blo 1564980 1566663 := bstep (se 1 (by rfl) ⟨1174997, by rfl⟩ : syracuseStep 1566663 = 2349995) B2349995
theorem B1566683 : Blo 1564980 1566683 := bstep (se 1 (by rfl) ⟨1175012, by rfl⟩ : syracuseStep 1566683 = 2350025) B2350025
theorem B3524615 : Blo 1564980 3524615 := bstep (se 1 (by rfl) ⟨2643461, by rfl⟩ : syracuseStep 3524615 = 5286923) B5286923
theorem B1566759 : Blo 1564980 1566759 := bstep (se 1 (by rfl) ⟨1175069, by rfl⟩ : syracuseStep 1566759 = 2350139) B2350139
theorem B3524687 : Blo 1564980 3524687 := bstep (se 1 (by rfl) ⟨2643515, by rfl⟩ : syracuseStep 3524687 = 5287031) B5287031
theorem B1566799 : Blo 1564980 1566799 := bstep (se 1 (by rfl) ⟨1175099, by rfl⟩ : syracuseStep 1566799 = 2350199) B2350199
theorem B5949521 : Blo 1564980 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B1566815 : Blo 1564980 1566815 := bstep (se 1 (by rfl) ⟨1175111, by rfl⟩ : syracuseStep 1566815 = 2350223) B2350223
theorem B1566843 : Blo 1564980 1566843 := bstep (se 1 (by rfl) ⟨1175132, by rfl⟩ : syracuseStep 1566843 = 2350265) B2350265
theorem B5286059 : Blo 1564980 5286059 := bstep (se 1 (by rfl) ⟨3964544, by rfl⟩ : syracuseStep 5286059 = 7929089) B7929089
theorem B1566895 : Blo 1564980 1566895 := bstep (se 1 (by rfl) ⟨1175171, by rfl⟩ : syracuseStep 1566895 = 2350343) B2350343
theorem B1566919 : Blo 1564980 1566919 := bstep (se 1 (by rfl) ⟨1175189, by rfl⟩ : syracuseStep 1566919 = 2350379) B2350379
theorem B1566939 : Blo 1564980 1566939 := bstep (se 1 (by rfl) ⟨1175204, by rfl⟩ : syracuseStep 1566939 = 2350409) B2350409
theorem B8915305 : Blo 1564980 8915305 := bstep (se 2 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 8915305 = 6686479) B6686479
theorem B12863897 : Blo 1564980 12863897 := bstep (se 2 (by rfl) ⟨4823961, by rfl⟩ : syracuseStep 12863897 = 9647923) B9647923
theorem B5646793 : Blo 1564980 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B3525083 : Blo 1564980 3525083 := bstep (se 1 (by rfl) ⟨2643812, by rfl⟩ : syracuseStep 3525083 = 5287625) B5287625
theorem B2509321 : Blo 1564980 2509321 := bstep (se 2 (by rfl) ⟨940995, by rfl⟩ : syracuseStep 2509321 = 1881991) B1881991
theorem B5286599 : Blo 1564980 5286599 := bstep (se 1 (by rfl) ⟨3964949, by rfl⟩ : syracuseStep 5286599 = 7929899) B7929899
theorem B18090697 : Blo 1564980 18090697 := bstep (se 2 (by rfl) ⟨6784011, by rfl⟩ : syracuseStep 18090697 = 13568023) B13568023
theorem B7924553 : Blo 1564980 7924553 := bstep (se 2 (by rfl) ⟨2971707, by rfl⟩ : syracuseStep 7924553 = 5943415) B5943415
theorem B19049363 : Blo 1564980 19049363 := bstep (se 1 (by rfl) ⟨14287022, by rfl⟩ : syracuseStep 19049363 = 28574045) B28574045
theorem B2821025 : Blo 1564980 2821025 := bstep (se 2 (by rfl) ⟨1057884, by rfl⟩ : syracuseStep 2821025 = 2115769) B2115769
theorem B3525551 : Blo 1564980 3525551 := bstep (se 1 (by rfl) ⟨2644163, by rfl⟩ : syracuseStep 3525551 = 5288327) B5288327
theorem B5942429 : Blo 1564980 5942429 := bstep (se 3 (by rfl) ⟨1114205, by rfl⟩ : syracuseStep 5942429 = 2228411) B2228411
theorem B5942443 : Blo 1564980 5942443 := bstep (se 1 (by rfl) ⟨4456832, by rfl⟩ : syracuseStep 5942443 = 8913665) B8913665
theorem B5016937 : Blo 1564980 5016937 := bstep (se 2 (by rfl) ⟨1881351, by rfl⟩ : syracuseStep 5016937 = 3762703) B3762703
theorem B2641295 : Blo 1564980 2641295 := bstep (se 1 (by rfl) ⟨1980971, by rfl⟩ : syracuseStep 2641295 = 3961943) B3961943
theorem B3173807 : Blo 1564980 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B5942747 : Blo 1564980 5942747 := bstep (se 1 (by rfl) ⟨4457060, by rfl⟩ : syracuseStep 5942747 = 8914121) B8914121
theorem B2117083 : Blo 1564980 2117083 := bstep (se 1 (by rfl) ⟨1587812, by rfl⟩ : syracuseStep 2117083 = 3175625) B3175625
theorem B3763721 : Blo 1564980 3763721 := bstep (se 2 (by rfl) ⟨1411395, by rfl⟩ : syracuseStep 3763721 = 2822791) B2822791
theorem B13381159 : Blo 1564980 13381159 := bstep (se 1 (by rfl) ⟨10035869, by rfl⟩ : syracuseStep 13381159 = 20071739) B20071739
theorem B5287463 : Blo 1564980 5287463 := bstep (se 1 (by rfl) ⟨3965597, by rfl⟩ : syracuseStep 5287463 = 7931195) B7931195
theorem B24104567 : Blo 1564980 24104567 := bstep (se 1 (by rfl) ⟨18078425, by rfl⟩ : syracuseStep 24104567 = 36156851) B36156851
theorem B2641531 : Blo 1564980 2641531 := bstep (se 1 (by rfl) ⟨1981148, by rfl⟩ : syracuseStep 2641531 = 3962297) B3962297
theorem B10038923 : Blo 1564980 10038923 := bstep (se 1 (by rfl) ⟨7529192, by rfl⟩ : syracuseStep 10038923 = 15058385) B15058385
theorem B5287571 : Blo 1564980 5287571 := bstep (se 1 (by rfl) ⟨3965678, by rfl⟩ : syracuseStep 5287571 = 7931357) B7931357
theorem B45149885 : Blo 1564980 45149885 := bstep (se 3 (by rfl) ⟨8465603, by rfl⟩ : syracuseStep 45149885 = 16931207) B16931207
theorem B5017373 : Blo 1564980 5017373 := bstep (se 3 (by rfl) ⟨940757, by rfl⟩ : syracuseStep 5017373 = 1881515) B1881515
theorem B11890475 : Blo 1564980 11890475 := bstep (se 1 (by rfl) ⟨8917856, by rfl⟩ : syracuseStep 11890475 = 17835713) B17835713
theorem B5287787 : Blo 1564980 5287787 := bstep (se 1 (by rfl) ⟨3965840, by rfl⟩ : syracuseStep 5287787 = 7931681) B7931681
theorem B60190613 : Blo 1564980 60190613 := bstep (se 6 (by rfl) ⟨1410717, by rfl⟩ : syracuseStep 60190613 = 2821435) B2821435
theorem B5287841 : Blo 1564980 5287841 := bstep (se 2 (by rfl) ⟨1982940, by rfl⟩ : syracuseStep 5287841 = 3965881) B3965881
theorem B13373369 : Blo 1564980 13373369 := bstep (se 2 (by rfl) ⟨5015013, by rfl⟩ : syracuseStep 13373369 = 10030027) B10030027
theorem B7925849 : Blo 1564980 7925849 := bstep (se 2 (by rfl) ⟨2972193, by rfl⟩ : syracuseStep 7925849 = 5944387) B5944387
theorem B6688925 : Blo 1564980 6688925 := bstep (se 3 (by rfl) ⟨1254173, by rfl⟩ : syracuseStep 6688925 = 2508347) B2508347
theorem B30118067 : Blo 1564980 30118067 := bstep (se 1 (by rfl) ⟨22588550, by rfl⟩ : syracuseStep 30118067 = 45177101) B45177101
theorem B11899223 : Blo 1564980 11899223 := bstep (se 1 (by rfl) ⟨8924417, by rfl⟩ : syracuseStep 11899223 = 17848835) B17848835
theorem B4518287 : Blo 1564980 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B2642395 : Blo 1564980 2642395 := bstep (se 1 (by rfl) ⟨1981796, by rfl⟩ : syracuseStep 2642395 = 3963593) B3963593
theorem B5288435 : Blo 1564980 5288435 := bstep (se 1 (by rfl) ⟨3966326, by rfl⟩ : syracuseStep 5288435 = 7932653) B7932653
theorem B2347529 : Blo 1564980 2347529 := bstep (se 2 (by rfl) ⟨880323, by rfl⟩ : syracuseStep 2347529 = 1760647) B1760647
theorem B2347559 : Blo 1564980 2347559 := bstep (se 1 (by rfl) ⟨1760669, by rfl⟩ : syracuseStep 2347559 = 3521339) B3521339
theorem B2347643 : Blo 1564980 2347643 := bstep (se 1 (by rfl) ⟨1760732, by rfl⟩ : syracuseStep 2347643 = 3521465) B3521465
theorem B3764875 : Blo 1564980 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B2347769 : Blo 1564980 2347769 := bstep (se 2 (by rfl) ⟨880413, by rfl⟩ : syracuseStep 2347769 = 1760827) B1760827
theorem B21435137 : Blo 1564980 21435137 := bstep (se 2 (by rfl) ⟨8038176, by rfl⟩ : syracuseStep 21435137 = 16076353) B16076353
theorem B2347871 : Blo 1564980 2347871 := bstep (se 1 (by rfl) ⟨1760903, by rfl⟩ : syracuseStep 2347871 = 3521807) B3521807
theorem B2347883 : Blo 1564980 2347883 := bstep (se 1 (by rfl) ⟨1760912, by rfl⟩ : syracuseStep 2347883 = 3521825) B3521825
theorem B30110615 : Blo 1564980 30110615 := bstep (se 1 (by rfl) ⟨22582961, by rfl⟩ : syracuseStep 30110615 = 45165923) B45165923
theorem B2348111 : Blo 1564980 2348111 := bstep (se 1 (by rfl) ⟨1761083, by rfl⟩ : syracuseStep 2348111 = 3522167) B3522167
theorem B2643023 : Blo 1564980 2643023 := bstep (se 1 (by rfl) ⟨1982267, by rfl⟩ : syracuseStep 2643023 = 3964535) B3964535
theorem B2348231 : Blo 1564980 2348231 := bstep (se 1 (by rfl) ⟨1761173, by rfl⟩ : syracuseStep 2348231 = 3522347) B3522347
theorem B2348393 : Blo 1564980 2348393 := bstep (se 2 (by rfl) ⟨880647, by rfl⟩ : syracuseStep 2348393 = 1761295) B1761295
theorem B2971055 : Blo 1564980 2971055 := bstep (se 1 (by rfl) ⟨2228291, by rfl⟩ : syracuseStep 2971055 = 4456583) B4456583
theorem B2413999 : Blo 1564980 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B2348471 : Blo 1564980 2348471 := bstep (se 1 (by rfl) ⟨1761353, by rfl⟩ : syracuseStep 2348471 = 3522707) B3522707
theorem B2348507 : Blo 1564980 2348507 := bstep (se 1 (by rfl) ⟨1761380, by rfl⟩ : syracuseStep 2348507 = 3522761) B3522761
theorem B5641937 : Blo 1564980 5641937 := bstep (se 2 (by rfl) ⟨2115726, by rfl⟩ : syracuseStep 5641937 = 4231453) B4231453
theorem B3176185 : Blo 1564980 3176185 := bstep (se 2 (by rfl) ⟨1191069, by rfl⟩ : syracuseStep 3176185 = 2382139) B2382139
theorem B5019499 : Blo 1564980 5019499 := bstep (se 1 (by rfl) ⟨3764624, by rfl⟩ : syracuseStep 5019499 = 7529249) B7529249
theorem B2348975 : Blo 1564980 2348975 := bstep (se 1 (by rfl) ⟨1761731, by rfl⟩ : syracuseStep 2348975 = 3523463) B3523463
theorem B2643887 : Blo 1564980 2643887 := bstep (se 1 (by rfl) ⟨1982915, by rfl⟩ : syracuseStep 2643887 = 3965831) B3965831
theorem B5019575 : Blo 1564980 5019575 := bstep (se 1 (by rfl) ⟨3764681, by rfl⟩ : syracuseStep 5019575 = 7529363) B7529363
theorem B2971579 : Blo 1564980 2971579 := bstep (se 1 (by rfl) ⟨2228684, by rfl⟩ : syracuseStep 2971579 = 4457369) B4457369
theorem B9164731 : Blo 1564980 9164731 := bstep (se 1 (by rfl) ⟨6873548, by rfl⟩ : syracuseStep 9164731 = 13747097) B13747097
theorem B19044305 : Blo 1564980 19044305 := bstep (se 2 (by rfl) ⟨7141614, by rfl⟩ : syracuseStep 19044305 = 14283229) B14283229
theorem B5945345 : Blo 1564980 5945345 := bstep (se 2 (by rfl) ⟨2229504, by rfl⟩ : syracuseStep 5945345 = 4459009) B4459009
theorem B2349065 : Blo 1564980 2349065 := bstep (se 2 (by rfl) ⟨880899, by rfl⟩ : syracuseStep 2349065 = 1761799) B1761799
theorem B5945359 : Blo 1564980 5945359 := bstep (se 1 (by rfl) ⟨4459019, by rfl⟩ : syracuseStep 5945359 = 8918039) B8918039
theorem B2349095 : Blo 1564980 2349095 := bstep (se 1 (by rfl) ⟨1761821, by rfl⟩ : syracuseStep 2349095 = 3523643) B3523643
theorem B2349179 : Blo 1564980 2349179 := bstep (se 1 (by rfl) ⟨1761884, by rfl⟩ : syracuseStep 2349179 = 3523769) B3523769
theorem B3963127 : Blo 1564980 3963127 := bstep (se 1 (by rfl) ⟨2972345, by rfl⟩ : syracuseStep 3963127 = 5944691) B5944691
theorem B2349305 : Blo 1564980 2349305 := bstep (se 2 (by rfl) ⟨880989, by rfl⟩ : syracuseStep 2349305 = 1761979) B1761979
theorem B10033409 : Blo 1564980 10033409 := bstep (se 2 (by rfl) ⟨3762528, by rfl⟩ : syracuseStep 10033409 = 7525057) B7525057
theorem B9181451 : Blo 1564980 9181451 := bstep (se 1 (by rfl) ⟨6886088, by rfl⟩ : syracuseStep 9181451 = 13772177) B13772177
theorem B2349407 : Blo 1564980 2349407 := bstep (se 1 (by rfl) ⟨1762055, by rfl⟩ : syracuseStep 2349407 = 3524111) B3524111
theorem B2349419 : Blo 1564980 2349419 := bstep (se 1 (by rfl) ⟨1762064, by rfl⟩ : syracuseStep 2349419 = 3524129) B3524129
theorem B2972065 : Blo 1564980 2972065 := bstep (se 2 (by rfl) ⟨1114524, by rfl⟩ : syracuseStep 2972065 = 2229049) B2229049
theorem B19036619 : Blo 1564980 19036619 := bstep (se 1 (by rfl) ⟨14277464, by rfl⟩ : syracuseStep 19036619 = 28554929) B28554929
theorem B3963401 : Blo 1564980 3963401 := bstep (se 2 (by rfl) ⟨1486275, by rfl⟩ : syracuseStep 3963401 = 2972551) B2972551
theorem B3963431 : Blo 1564980 3963431 := bstep (se 1 (by rfl) ⟨2972573, by rfl⟩ : syracuseStep 3963431 = 5945147) B5945147
theorem B2349647 : Blo 1564980 2349647 := bstep (se 1 (by rfl) ⟨1762235, by rfl⟩ : syracuseStep 2349647 = 3524471) B3524471
theorem B3619451 : Blo 1564980 3619451 := bstep (se 1 (by rfl) ⟨2714588, by rfl⟩ : syracuseStep 3619451 = 5429177) B5429177
theorem B5085881 : Blo 1564980 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B2349767 : Blo 1564980 2349767 := bstep (se 1 (by rfl) ⟨1762325, by rfl⟩ : syracuseStep 2349767 = 3524651) B3524651
theorem B5282603 : Blo 1564980 5282603 := bstep (se 1 (by rfl) ⟨3961952, by rfl⟩ : syracuseStep 5282603 = 7923905) B7923905
theorem B17832797 : Blo 1564980 17832797 := bstep (se 3 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 17832797 = 6687299) B6687299
theorem B3521375 : Blo 1564980 3521375 := bstep (se 1 (by rfl) ⟨2641031, by rfl⟩ : syracuseStep 3521375 = 5282063) B5282063
theorem B2349929 : Blo 1564980 2349929 := bstep (se 2 (by rfl) ⟨881223, by rfl⟩ : syracuseStep 2349929 = 1762447) B1762447
theorem B3963755 : Blo 1564980 3963755 := bstep (se 1 (by rfl) ⟨2972816, by rfl⟩ : syracuseStep 3963755 = 5945633) B5945633
theorem B16063379 : Blo 1564980 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B2350007 : Blo 1564980 2350007 := bstep (se 1 (by rfl) ⟨1762505, by rfl⟩ : syracuseStep 2350007 = 3525011) B3525011
theorem B2350043 : Blo 1564980 2350043 := bstep (se 1 (by rfl) ⟨1762532, by rfl⟩ : syracuseStep 2350043 = 3525065) B3525065
theorem B3521555 : Blo 1564980 3521555 := bstep (se 1 (by rfl) ⟨2641166, by rfl⟩ : syracuseStep 3521555 = 5282333) B5282333
theorem B5282873 : Blo 1564980 5282873 := bstep (se 2 (by rfl) ⟨1981077, by rfl⟩ : syracuseStep 5282873 = 3962155) B3962155
theorem B50814125 : Blo 1564980 50814125 := bstep (se 3 (by rfl) ⟨9527648, by rfl⟩ : syracuseStep 50814125 = 19055297) B19055297
theorem B15047927 : Blo 1564980 15047927 := bstep (se 1 (by rfl) ⟨11285945, by rfl⟩ : syracuseStep 15047927 = 22571891) B22571891
theorem B5946635 : Blo 1564980 5946635 := bstep (se 1 (by rfl) ⟨4459976, by rfl⟩ : syracuseStep 5946635 = 8919953) B8919953
theorem B3521897 : Blo 1564980 3521897 := bstep (se 2 (by rfl) ⟨1320711, by rfl⟩ : syracuseStep 3521897 = 2641423) B2641423
theorem B5283197 : Blo 1564980 5283197 := bstep (se 3 (by rfl) ⟨990599, by rfl⟩ : syracuseStep 5283197 = 1981199) B1981199
theorem B3964403 : Blo 1564980 3964403 := bstep (se 1 (by rfl) ⟨2973302, by rfl⟩ : syracuseStep 3964403 = 5946605) B5946605
theorem B5283467 : Blo 1564980 5283467 := bstep (se 1 (by rfl) ⟨3962600, by rfl⟩ : syracuseStep 5283467 = 7925201) B7925201
theorem B5947091 : Blo 1564980 5947091 := bstep (se 1 (by rfl) ⟨4460318, by rfl⟩ : syracuseStep 5947091 = 8920637) B8920637
theorem B5644025 : Blo 1564980 5644025 := bstep (se 2 (by rfl) ⟨2116509, by rfl⟩ : syracuseStep 5644025 = 4233019) B4233019
theorem B6029099 : Blo 1564980 6029099 := bstep (se 1 (by rfl) ⟨4521824, by rfl⟩ : syracuseStep 6029099 = 9043649) B9043649
theorem B7241567 : Blo 1564980 7241567 := bstep (se 1 (by rfl) ⟨5431175, by rfl⟩ : syracuseStep 7241567 = 10862351) B10862351
theorem B3522491 : Blo 1564980 3522491 := bstep (se 1 (by rfl) ⟨2641868, by rfl⟩ : syracuseStep 3522491 = 5283737) B5283737
theorem B3964859 : Blo 1564980 3964859 := bstep (se 1 (by rfl) ⟨2973644, by rfl⟩ : syracuseStep 3964859 = 5947289) B5947289
theorem B101638091 : Blo 1564980 101638091 := bstep (se 1 (by rfl) ⟨76228568, by rfl⟩ : syracuseStep 101638091 = 152457137) B152457137
theorem B5283899 : Blo 1564980 5283899 := bstep (se 1 (by rfl) ⟨3962924, by rfl⟩ : syracuseStep 5283899 = 7925849) B7925849
theorem B20078711 : Blo 1564980 20078711 := bstep (se 1 (by rfl) ⟨15059033, by rfl⟩ : syracuseStep 20078711 = 30118067) B30118067
theorem B5284169 : Blo 1564980 5284169 := bstep (se 2 (by rfl) ⟨1981563, by rfl⟩ : syracuseStep 5284169 = 3963127) B3963127
theorem B1565019 : Blo 1564980 1565019 := bstep (se 1 (by rfl) ⟨1173764, by rfl⟩ : syracuseStep 1565019 = 2347529) B2347529
theorem B3522923 : Blo 1564980 3522923 := bstep (se 1 (by rfl) ⟨2642192, by rfl⟩ : syracuseStep 3522923 = 5284385) B5284385
theorem B1565039 : Blo 1564980 1565039 := bstep (se 1 (by rfl) ⟨1173779, by rfl⟩ : syracuseStep 1565039 = 2347559) B2347559
theorem B1565095 : Blo 1564980 1565095 := bstep (se 1 (by rfl) ⟨1173821, by rfl⟩ : syracuseStep 1565095 = 2347643) B2347643
theorem B3965395 : Blo 1564980 3965395 := bstep (se 1 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 3965395 = 5948093) B5948093
theorem B11887073 : Blo 1564980 11887073 := bstep (se 2 (by rfl) ⟨4457652, by rfl⟩ : syracuseStep 11887073 = 8915305) B8915305
theorem B1565179 : Blo 1564980 1565179 := bstep (se 1 (by rfl) ⟨1173884, by rfl⟩ : syracuseStep 1565179 = 2347769) B2347769
theorem B3523067 : Blo 1564980 3523067 := bstep (se 1 (by rfl) ⟨2642300, by rfl⟩ : syracuseStep 3523067 = 5284601) B5284601
theorem B1982971 : Blo 1564980 1982971 := bstep (se 1 (by rfl) ⟨1487228, by rfl⟩ : syracuseStep 1982971 = 2974457) B2974457
theorem B1565247 : Blo 1564980 1565247 := bstep (se 1 (by rfl) ⟨1173935, by rfl⟩ : syracuseStep 1565247 = 2347871) B2347871
theorem B1565255 : Blo 1564980 1565255 := bstep (se 1 (by rfl) ⟨1173941, by rfl⟩ : syracuseStep 1565255 = 2347883) B2347883
theorem B7529057 : Blo 1564980 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B3523193 : Blo 1564980 3523193 := bstep (se 2 (by rfl) ⟨1321197, by rfl⟩ : syracuseStep 3523193 = 2642395) B2642395
theorem B5014169 : Blo 1564980 5014169 := bstep (se 2 (by rfl) ⟨1880313, by rfl⟩ : syracuseStep 5014169 = 3760627) B3760627
theorem B26755757 : Blo 1564980 26755757 := bstep (se 3 (by rfl) ⟨5016704, by rfl⟩ : syracuseStep 26755757 = 10033409) B10033409
theorem B3523247 : Blo 1564980 3523247 := bstep (se 1 (by rfl) ⟨2642435, by rfl⟩ : syracuseStep 3523247 = 5284871) B5284871
theorem B1565407 : Blo 1564980 1565407 := bstep (se 1 (by rfl) ⟨1174055, by rfl⟩ : syracuseStep 1565407 = 2348111) B2348111
theorem B1762015 : Blo 1564980 1762015 := bstep (se 1 (by rfl) ⟨1321511, by rfl⟩ : syracuseStep 1762015 = 2643023) B2643023
theorem B1983199 : Blo 1564980 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B3523319 : Blo 1564980 3523319 := bstep (se 1 (by rfl) ⟨2642489, by rfl⟩ : syracuseStep 3523319 = 5284979) B5284979
theorem B1565487 : Blo 1564980 1565487 := bstep (se 1 (by rfl) ⟨1174115, by rfl⟩ : syracuseStep 1565487 = 2348231) B2348231
theorem B72336179 : Blo 1564980 72336179 := bstep (se 1 (by rfl) ⟨54252134, by rfl⟩ : syracuseStep 72336179 = 108504269) B108504269
theorem B17843003 : Blo 1564980 17843003 := bstep (se 1 (by rfl) ⟨13382252, by rfl⟩ : syracuseStep 17843003 = 26764505) B26764505
theorem B1565595 : Blo 1564980 1565595 := bstep (se 1 (by rfl) ⟨1174196, by rfl⟩ : syracuseStep 1565595 = 2348393) B2348393
theorem B3523499 : Blo 1564980 3523499 := bstep (se 1 (by rfl) ⟨2642624, by rfl⟩ : syracuseStep 3523499 = 5285249) B5285249
theorem B1565647 : Blo 1564980 1565647 := bstep (se 1 (by rfl) ⟨1174235, by rfl⟩ : syracuseStep 1565647 = 2348471) B2348471
theorem B1565671 : Blo 1564980 1565671 := bstep (se 1 (by rfl) ⟨1174253, by rfl⟩ : syracuseStep 1565671 = 2348507) B2348507
theorem B7930871 : Blo 1564980 7930871 := bstep (se 1 (by rfl) ⟨5948153, by rfl⟩ : syracuseStep 7930871 = 11896307) B11896307
theorem B8463485 : Blo 1564980 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B3761291 : Blo 1564980 3761291 := bstep (se 1 (by rfl) ⟨2820968, by rfl⟩ : syracuseStep 3761291 = 5641937) B5641937
theorem B16942279 : Blo 1564980 16942279 := bstep (se 1 (by rfl) ⟨12706709, by rfl⟩ : syracuseStep 16942279 = 25413419) B25413419
theorem B3966185 : Blo 1564980 3966185 := bstep (se 2 (by rfl) ⟨1487319, by rfl⟩ : syracuseStep 3966185 = 2974639) B2974639
theorem B1565983 : Blo 1564980 1565983 := bstep (se 1 (by rfl) ⟨1174487, by rfl⟩ : syracuseStep 1565983 = 2348975) B2348975
theorem B1762591 : Blo 1564980 1762591 := bstep (se 1 (by rfl) ⟨1321943, by rfl⟩ : syracuseStep 1762591 = 2643887) B2643887
theorem B4457767 : Blo 1564980 4457767 := bstep (se 1 (by rfl) ⟨3343325, by rfl⟩ : syracuseStep 4457767 = 6686651) B6686651
theorem B1566043 : Blo 1564980 1566043 := bstep (se 1 (by rfl) ⟨1174532, by rfl⟩ : syracuseStep 1566043 = 2349065) B2349065
theorem B1566063 : Blo 1564980 1566063 := bstep (se 1 (by rfl) ⟨1174547, by rfl⟩ : syracuseStep 1566063 = 2349095) B2349095
theorem B3966347 : Blo 1564980 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B1566119 : Blo 1564980 1566119 := bstep (se 1 (by rfl) ⟨1174589, by rfl⟩ : syracuseStep 1566119 = 2349179) B2349179
theorem B3524039 : Blo 1564980 3524039 := bstep (se 1 (by rfl) ⟨2643029, by rfl⟩ : syracuseStep 3524039 = 5286059) B5286059
theorem B1566203 : Blo 1564980 1566203 := bstep (se 1 (by rfl) ⟨1174652, by rfl⟩ : syracuseStep 1566203 = 2349305) B2349305
theorem B6120967 : Blo 1564980 6120967 := bstep (se 1 (by rfl) ⟨4590725, by rfl⟩ : syracuseStep 6120967 = 9181451) B9181451
theorem B7923257 : Blo 1564980 7923257 := bstep (se 2 (by rfl) ⟨2971221, by rfl⟩ : syracuseStep 7923257 = 5942443) B5942443
theorem B4458041 : Blo 1564980 4458041 := bstep (se 2 (by rfl) ⟨1671765, by rfl⟩ : syracuseStep 4458041 = 3343531) B3343531
theorem B1566271 : Blo 1564980 1566271 := bstep (se 1 (by rfl) ⟨1174703, by rfl⟩ : syracuseStep 1566271 = 2349407) B2349407
theorem B1566279 : Blo 1564980 1566279 := bstep (se 1 (by rfl) ⟨1174709, by rfl⟩ : syracuseStep 1566279 = 2349419) B2349419
theorem B12691079 : Blo 1564980 12691079 := bstep (se 1 (by rfl) ⟨9518309, by rfl⟩ : syracuseStep 12691079 = 19036619) B19036619
theorem B9651869 : Blo 1564980 9651869 := bstep (se 3 (by rfl) ⟨1809725, by rfl⟩ : syracuseStep 9651869 = 3619451) B3619451
theorem B25388765 : Blo 1564980 25388765 := bstep (se 3 (by rfl) ⟨4760393, by rfl⟩ : syracuseStep 25388765 = 9520787) B9520787
theorem B1566431 : Blo 1564980 1566431 := bstep (se 1 (by rfl) ⟨1174823, by rfl⟩ : syracuseStep 1566431 = 2349647) B2349647
theorem B3524399 : Blo 1564980 3524399 := bstep (se 1 (by rfl) ⟨2643299, by rfl⟩ : syracuseStep 3524399 = 5286599) B5286599
theorem B1566511 : Blo 1564980 1566511 := bstep (se 1 (by rfl) ⟨1174883, by rfl⟩ : syracuseStep 1566511 = 2349767) B2349767
theorem B11888531 : Blo 1564980 11888531 := bstep (se 1 (by rfl) ⟨8916398, by rfl⟩ : syracuseStep 11888531 = 17832797) B17832797
theorem B1566619 : Blo 1564980 1566619 := bstep (se 1 (by rfl) ⟨1174964, by rfl⟩ : syracuseStep 1566619 = 2349929) B2349929
theorem B10708919 : Blo 1564980 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B12699575 : Blo 1564980 12699575 := bstep (se 1 (by rfl) ⟨9524681, by rfl⟩ : syracuseStep 12699575 = 19049363) B19049363
theorem B1566671 : Blo 1564980 1566671 := bstep (se 1 (by rfl) ⟨1175003, by rfl⟩ : syracuseStep 1566671 = 2350007) B2350007
theorem B1566695 : Blo 1564980 1566695 := bstep (se 1 (by rfl) ⟨1175021, by rfl⟩ : syracuseStep 1566695 = 2350043) B2350043
theorem B33876083 : Blo 1564980 33876083 := bstep (se 1 (by rfl) ⟨25407062, by rfl⟩ : syracuseStep 33876083 = 50814125) B50814125
theorem B19310845 : Blo 1564980 19310845 := bstep (se 3 (by rfl) ⟨3620783, by rfl⟩ : syracuseStep 19310845 = 7241567) B7241567
theorem B2509147 : Blo 1564980 2509147 := bstep (se 1 (by rfl) ⟨1881860, by rfl⟩ : syracuseStep 2509147 = 3763721) B3763721
theorem B3524975 : Blo 1564980 3524975 := bstep (se 1 (by rfl) ⟨2643731, by rfl⟩ : syracuseStep 3524975 = 5287463) B5287463
theorem B7522733 : Blo 1564980 7522733 := bstep (se 3 (by rfl) ⟨1410512, by rfl⟩ : syracuseStep 7522733 = 2821025) B2821025
theorem B3525047 : Blo 1564980 3525047 := bstep (se 1 (by rfl) ⟨2643785, by rfl⟩ : syracuseStep 3525047 = 5287571) B5287571
theorem B30099923 : Blo 1564980 30099923 := bstep (se 1 (by rfl) ⟨22574942, by rfl⟩ : syracuseStep 30099923 = 45149885) B45149885
theorem B3762683 : Blo 1564980 3762683 := bstep (se 1 (by rfl) ⟨2822012, by rfl⟩ : syracuseStep 3762683 = 5644025) B5644025
theorem B3344915 : Blo 1564980 3344915 := bstep (se 1 (by rfl) ⟨2508686, by rfl⟩ : syracuseStep 3344915 = 5017373) B5017373
theorem B3525191 : Blo 1564980 3525191 := bstep (se 1 (by rfl) ⟨2643893, by rfl⟩ : syracuseStep 3525191 = 5287787) B5287787
theorem B40127075 : Blo 1564980 40127075 := bstep (se 1 (by rfl) ⟨30095306, by rfl⟩ : syracuseStep 40127075 = 60190613) B60190613
theorem B3525227 : Blo 1564980 3525227 := bstep (se 1 (by rfl) ⟨2643920, by rfl⟩ : syracuseStep 3525227 = 5287841) B5287841
theorem B8915579 : Blo 1564980 8915579 := bstep (se 1 (by rfl) ⟨6686684, by rfl⟩ : syracuseStep 8915579 = 13373369) B13373369
theorem B67758727 : Blo 1564980 67758727 := bstep (se 1 (by rfl) ⟨50819045, by rfl⟩ : syracuseStep 67758727 = 101638091) B101638091
theorem B4459283 : Blo 1564980 4459283 := bstep (se 1 (by rfl) ⟨3344462, by rfl⟩ : syracuseStep 4459283 = 6688925) B6688925
theorem B24095555 : Blo 1564980 24095555 := bstep (se 1 (by rfl) ⟨18071666, by rfl⟩ : syracuseStep 24095555 = 36143333) B36143333
theorem B7932815 : Blo 1564980 7932815 := bstep (se 1 (by rfl) ⟨5949611, by rfl⟩ : syracuseStep 7932815 = 11899223) B11899223
theorem B3525623 : Blo 1564980 3525623 := bstep (se 1 (by rfl) ⟨2644217, by rfl⟩ : syracuseStep 3525623 = 5288435) B5288435
theorem B14290091 : Blo 1564980 14290091 := bstep (se 1 (by rfl) ⟨10717568, by rfl⟩ : syracuseStep 14290091 = 21435137) B21435137
theorem B20073743 : Blo 1564980 20073743 := bstep (se 1 (by rfl) ⟨15055307, by rfl⟩ : syracuseStep 20073743 = 30110615) B30110615
theorem B3345761 : Blo 1564980 3345761 := bstep (se 2 (by rfl) ⟨1254660, by rfl⟩ : syracuseStep 3345761 = 2509321) B2509321
theorem B5287355 : Blo 1564980 5287355 := bstep (se 1 (by rfl) ⟨3965516, by rfl⟩ : syracuseStep 5287355 = 7931033) B7931033
theorem B13561307 : Blo 1564980 13561307 := bstep (se 1 (by rfl) ⟨10170980, by rfl⟩ : syracuseStep 13561307 = 20341961) B20341961
theorem B24120929 : Blo 1564980 24120929 := bstep (se 2 (by rfl) ⟨9045348, by rfl⟩ : syracuseStep 24120929 = 18090697) B18090697
theorem B7925363 : Blo 1564980 7925363 := bstep (se 1 (by rfl) ⟨5944022, by rfl⟩ : syracuseStep 7925363 = 11888045) B11888045
theorem B13381433 : Blo 1564980 13381433 := bstep (se 2 (by rfl) ⟨5018037, by rfl⟩ : syracuseStep 13381433 = 10036075) B10036075
theorem B5943401 : Blo 1564980 5943401 := bstep (se 2 (by rfl) ⟨2228775, by rfl⟩ : syracuseStep 5943401 = 4457551) B4457551
theorem B2642267 : Blo 1564980 2642267 := bstep (se 1 (by rfl) ⟨1981700, by rfl⟩ : syracuseStep 2642267 = 3963401) B3963401
theorem B2642287 : Blo 1564980 2642287 := bstep (se 1 (by rfl) ⟨1981715, by rfl⟩ : syracuseStep 2642287 = 3963431) B3963431
theorem B6689249 : Blo 1564980 6689249 := bstep (se 2 (by rfl) ⟨2508468, by rfl⟩ : syracuseStep 6689249 = 5016937) B5016937
theorem B2347583 : Blo 1564980 2347583 := bstep (se 1 (by rfl) ⟨1760687, by rfl⟩ : syracuseStep 2347583 = 3521375) B3521375
theorem B2642503 : Blo 1564980 2642503 := bstep (se 1 (by rfl) ⟨1981877, by rfl⟩ : syracuseStep 2642503 = 3963755) B3963755
theorem B2822777 : Blo 1564980 2822777 := bstep (se 2 (by rfl) ⟨1058541, by rfl⟩ : syracuseStep 2822777 = 2117083) B2117083
theorem B2347703 : Blo 1564980 2347703 := bstep (se 1 (by rfl) ⟨1760777, by rfl⟩ : syracuseStep 2347703 = 3521555) B3521555
theorem B3961619 : Blo 1564980 3961619 := bstep (se 1 (by rfl) ⟨2971214, by rfl⟩ : syracuseStep 3961619 = 5942429) B5942429
theorem B10031951 : Blo 1564980 10031951 := bstep (se 1 (by rfl) ⟨7523963, by rfl⟩ : syracuseStep 10031951 = 15047927) B15047927
theorem B2347931 : Blo 1564980 2347931 := bstep (se 1 (by rfl) ⟨1760948, by rfl⟩ : syracuseStep 2347931 = 3521897) B3521897
theorem B10171345 : Blo 1564980 10171345 := bstep (se 2 (by rfl) ⟨3814254, by rfl⟩ : syracuseStep 10171345 = 7628509) B7628509
theorem B3961831 : Blo 1564980 3961831 := bstep (se 1 (by rfl) ⟨2971373, by rfl⟩ : syracuseStep 3961831 = 5942747) B5942747
theorem B2642935 : Blo 1564980 2642935 := bstep (se 1 (by rfl) ⟨1982201, by rfl⟩ : syracuseStep 2642935 = 3964403) B3964403
theorem B16069711 : Blo 1564980 16069711 := bstep (se 1 (by rfl) ⟨12052283, by rfl⟩ : syracuseStep 16069711 = 24104567) B24104567
theorem B7926983 : Blo 1564980 7926983 := bstep (se 1 (by rfl) ⟨5945237, by rfl⟩ : syracuseStep 7926983 = 11890475) B11890475
theorem B4019399 : Blo 1564980 4019399 := bstep (se 1 (by rfl) ⟨3014549, by rfl⟩ : syracuseStep 4019399 = 6029099) B6029099
theorem B3962105 : Blo 1564980 3962105 := bstep (se 2 (by rfl) ⟨1485789, by rfl⟩ : syracuseStep 3962105 = 2971579) B2971579
theorem B12219641 : Blo 1564980 12219641 := bstep (se 2 (by rfl) ⟨4582365, by rfl⟩ : syracuseStep 12219641 = 9164731) B9164731
theorem B2348327 : Blo 1564980 2348327 := bstep (se 1 (by rfl) ⟨1761245, by rfl⟩ : syracuseStep 2348327 = 3522491) B3522491
theorem B2643239 : Blo 1564980 2643239 := bstep (se 1 (by rfl) ⟨1982429, by rfl⟩ : syracuseStep 2643239 = 3964859) B3964859
theorem B7927145 : Blo 1564980 7927145 := bstep (se 2 (by rfl) ⟨2972679, by rfl⟩ : syracuseStep 7927145 = 5945359) B5945359
theorem B2348411 : Blo 1564980 2348411 := bstep (se 1 (by rfl) ⟨1761308, by rfl⟩ : syracuseStep 2348411 = 3522617) B3522617
theorem B2348537 : Blo 1564980 2348537 := bstep (se 2 (by rfl) ⟨880701, by rfl⟩ : syracuseStep 2348537 = 1761403) B1761403
theorem B3012191 : Blo 1564980 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B2348639 : Blo 1564980 2348639 := bstep (se 1 (by rfl) ⟨1761479, by rfl⟩ : syracuseStep 2348639 = 3522959) B3522959
theorem B2643691 : Blo 1564980 2643691 := bstep (se 1 (by rfl) ⟨1982768, by rfl⟩ : syracuseStep 2643691 = 3965537) B3965537
theorem B2348855 : Blo 1564980 2348855 := bstep (se 1 (by rfl) ⟨1761641, by rfl⟩ : syracuseStep 2348855 = 3523283) B3523283
theorem B3962753 : Blo 1564980 3962753 := bstep (se 2 (by rfl) ⟨1486032, by rfl⟩ : syracuseStep 3962753 = 2972065) B2972065
theorem B2349161 : Blo 1564980 2349161 := bstep (se 2 (by rfl) ⟨880935, by rfl⟩ : syracuseStep 2349161 = 1761871) B1761871
theorem B5019833 : Blo 1564980 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B1980703 : Blo 1564980 1980703 := bstep (se 1 (by rfl) ⟨1485527, by rfl⟩ : syracuseStep 1980703 = 2971055) B2971055
theorem B2349479 : Blo 1564980 2349479 := bstep (se 1 (by rfl) ⟨1762109, by rfl⟩ : syracuseStep 2349479 = 3524219) B3524219
theorem B25385399 : Blo 1564980 25385399 := bstep (se 1 (by rfl) ⟨19039049, by rfl⟩ : syracuseStep 25385399 = 38078099) B38078099
theorem B10033591 : Blo 1564980 10033591 := bstep (se 1 (by rfl) ⟨7525193, by rfl⟩ : syracuseStep 10033591 = 15050387) B15050387
theorem B2349563 : Blo 1564980 2349563 := bstep (se 1 (by rfl) ⟨1762172, by rfl⟩ : syracuseStep 2349563 = 3524345) B3524345
theorem B11885129 : Blo 1564980 11885129 := bstep (se 2 (by rfl) ⟨4456923, by rfl⟩ : syracuseStep 11885129 = 8913847) B8913847
theorem B2349689 : Blo 1564980 2349689 := bstep (se 2 (by rfl) ⟨881133, by rfl⟩ : syracuseStep 2349689 = 1762267) B1762267
theorem B12696203 : Blo 1564980 12696203 := bstep (se 1 (by rfl) ⟨9522152, by rfl⟩ : syracuseStep 12696203 = 19044305) B19044305
theorem B3963563 : Blo 1564980 3963563 := bstep (se 1 (by rfl) ⟨2972672, by rfl⟩ : syracuseStep 3963563 = 5945345) B5945345
theorem B2349743 : Blo 1564980 2349743 := bstep (se 1 (by rfl) ⟨1762307, by rfl⟩ : syracuseStep 2349743 = 3524615) B3524615
theorem B2349791 : Blo 1564980 2349791 := bstep (se 1 (by rfl) ⟨1762343, by rfl⟩ : syracuseStep 2349791 = 3524687) B3524687
theorem B8575931 : Blo 1564980 8575931 := bstep (se 1 (by rfl) ⟨6431948, by rfl⟩ : syracuseStep 8575931 = 12863897) B12863897
theorem B2350055 : Blo 1564980 2350055 := bstep (se 1 (by rfl) ⟨1762541, by rfl⟩ : syracuseStep 2350055 = 3525083) B3525083
theorem B3390587 : Blo 1564980 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B3521735 : Blo 1564980 3521735 := bstep (se 1 (by rfl) ⟨2641301, by rfl⟩ : syracuseStep 3521735 = 5282603) B5282603
theorem B5283035 : Blo 1564980 5283035 := bstep (se 1 (by rfl) ⟨3962276, by rfl⟩ : syracuseStep 5283035 = 7924553) B7924553
theorem B3218665 : Blo 1564980 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B2350313 : Blo 1564980 2350313 := bstep (se 2 (by rfl) ⟨881367, by rfl⟩ : syracuseStep 2350313 = 1762735) B1762735
theorem B2350367 : Blo 1564980 2350367 := bstep (se 1 (by rfl) ⟨1762775, by rfl⟩ : syracuseStep 2350367 = 3525551) B3525551
theorem B3521915 : Blo 1564980 3521915 := bstep (se 1 (by rfl) ⟨2641436, by rfl⟩ : syracuseStep 3521915 = 5282873) B5282873
theorem B17841545 : Blo 1564980 17841545 := bstep (se 2 (by rfl) ⟨6690579, by rfl⟩ : syracuseStep 17841545 = 13381159) B13381159
theorem B3522041 : Blo 1564980 3522041 := bstep (se 2 (by rfl) ⟨1320765, by rfl⟩ : syracuseStep 3522041 = 2641531) B2641531
theorem B3964423 : Blo 1564980 3964423 := bstep (se 1 (by rfl) ⟨2973317, by rfl⟩ : syracuseStep 3964423 = 5946635) B5946635
theorem B3522131 : Blo 1564980 3522131 := bstep (se 1 (by rfl) ⟨2641598, by rfl⟩ : syracuseStep 3522131 = 5283197) B5283197
theorem B1760863 : Blo 1564980 1760863 := bstep (se 1 (by rfl) ⟨1320647, by rfl⟩ : syracuseStep 1760863 = 2641295) B2641295
theorem B4234913 : Blo 1564980 4234913 := bstep (se 2 (by rfl) ⟨1588092, by rfl⟩ : syracuseStep 4234913 = 3176185) B3176185
theorem B3522311 : Blo 1564980 3522311 := bstep (se 1 (by rfl) ⟨2641733, by rfl⟩ : syracuseStep 3522311 = 5283467) B5283467
theorem B6692615 : Blo 1564980 6692615 := bstep (se 1 (by rfl) ⟨5019461, by rfl⟩ : syracuseStep 6692615 = 10038923) B10038923
theorem B3964727 : Blo 1564980 3964727 := bstep (se 1 (by rfl) ⟨2973545, by rfl⟩ : syracuseStep 3964727 = 5947091) B5947091
theorem B6692665 : Blo 1564980 6692665 := bstep (se 2 (by rfl) ⟨2509749, by rfl⟩ : syracuseStep 6692665 = 5019499) B5019499
theorem B13385533 : Blo 1564980 13385533 := bstep (se 3 (by rfl) ⟨2509787, by rfl⟩ : syracuseStep 13385533 = 5019575) B5019575
theorem B3522599 : Blo 1564980 3522599 := bstep (se 1 (by rfl) ⟨2641949, by rfl⟩ : syracuseStep 3522599 = 5283899) B5283899
theorem B13385807 : Blo 1564980 13385807 := bstep (se 1 (by rfl) ⟨10039355, by rfl⟩ : syracuseStep 13385807 = 20078711) B20078711
theorem B3522779 : Blo 1564980 3522779 := bstep (se 1 (by rfl) ⟨2642084, by rfl⟩ : syracuseStep 3522779 = 5284169) B5284169
theorem B1761511 : Blo 1564980 1761511 := bstep (se 1 (by rfl) ⟨1321133, by rfl⟩ : syracuseStep 1761511 = 2642267) B2642267
theorem B22569293 : Blo 1564980 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B25747793 : Blo 1564980 25747793 := bstep (se 2 (by rfl) ⟨9655422, by rfl⟩ : syracuseStep 25747793 = 19310845) B19310845
theorem B1565055 : Blo 1564980 1565055 := bstep (se 1 (by rfl) ⟨1173791, by rfl⟩ : syracuseStep 1565055 = 2347583) B2347583
theorem B3342779 : Blo 1564980 3342779 := bstep (se 1 (by rfl) ⟨2507084, by rfl⟩ : syracuseStep 3342779 = 5014169) B5014169
theorem B1565135 : Blo 1564980 1565135 := bstep (se 1 (by rfl) ⟨1173851, by rfl⟩ : syracuseStep 1565135 = 2347703) B2347703
theorem B3523049 : Blo 1564980 3523049 := bstep (se 2 (by rfl) ⟨1321143, by rfl⟩ : syracuseStep 3523049 = 2642287) B2642287
theorem B11895335 : Blo 1564980 11895335 := bstep (se 1 (by rfl) ⟨8921501, by rfl⟩ : syracuseStep 11895335 = 17843003) B17843003
theorem B13378121 : Blo 1564980 13378121 := bstep (se 2 (by rfl) ⟨5016795, by rfl⟩ : syracuseStep 13378121 = 10033591) B10033591
theorem B1565287 : Blo 1564980 1565287 := bstep (se 1 (by rfl) ⟨1173965, by rfl⟩ : syracuseStep 1565287 = 2347931) B2347931
theorem B2507527 : Blo 1564980 2507527 := bstep (se 1 (by rfl) ⟨1880645, by rfl⟩ : syracuseStep 2507527 = 3761291) B3761291
theorem B3523337 : Blo 1564980 3523337 := bstep (se 2 (by rfl) ⟨1321251, by rfl⟩ : syracuseStep 3523337 = 2642503) B2642503
theorem B5284655 : Blo 1564980 5284655 := bstep (se 1 (by rfl) ⟨3963491, by rfl⟩ : syracuseStep 5284655 = 7926983) B7926983
theorem B2679599 : Blo 1564980 2679599 := bstep (se 1 (by rfl) ⟨2009699, by rfl⟩ : syracuseStep 2679599 = 4019399) B4019399
theorem B1565551 : Blo 1564980 1565551 := bstep (se 1 (by rfl) ⟨1174163, by rfl⟩ : syracuseStep 1565551 = 2348327) B2348327
theorem B1762159 : Blo 1564980 1762159 := bstep (se 1 (by rfl) ⟨1321619, by rfl⟩ : syracuseStep 1762159 = 2643239) B2643239
theorem B5284763 : Blo 1564980 5284763 := bstep (se 1 (by rfl) ⟨3963572, by rfl⟩ : syracuseStep 5284763 = 7927145) B7927145
theorem B1565607 : Blo 1564980 1565607 := bstep (se 1 (by rfl) ⟨1174205, by rfl⟩ : syracuseStep 1565607 = 2348411) B2348411
theorem B1565691 : Blo 1564980 1565691 := bstep (se 1 (by rfl) ⟨1174268, by rfl⟩ : syracuseStep 1565691 = 2348537) B2348537
theorem B2008127 : Blo 1564980 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B1565759 : Blo 1564980 1565759 := bstep (se 1 (by rfl) ⟨1174319, by rfl⟩ : syracuseStep 1565759 = 2348639) B2348639
theorem B16925843 : Blo 1564980 16925843 := bstep (se 1 (by rfl) ⟨12694382, by rfl⟩ : syracuseStep 16925843 = 25388765) B25388765
theorem B1565903 : Blo 1564980 1565903 := bstep (se 1 (by rfl) ⟨1174427, by rfl⟩ : syracuseStep 1565903 = 2348855) B2348855
theorem B3523913 : Blo 1564980 3523913 := bstep (se 2 (by rfl) ⟨1321467, by rfl⟩ : syracuseStep 3523913 = 2642935) B2642935
theorem B1566107 : Blo 1564980 1566107 := bstep (se 1 (by rfl) ⟨1174580, by rfl⟩ : syracuseStep 1566107 = 2349161) B2349161
theorem B1566319 : Blo 1564980 1566319 := bstep (se 1 (by rfl) ⟨1174739, by rfl⟩ : syracuseStep 1566319 = 2349479) B2349479
theorem B2508455 : Blo 1564980 2508455 := bstep (se 1 (by rfl) ⟨1881341, by rfl⟩ : syracuseStep 2508455 = 3762683) B3762683
theorem B1566375 : Blo 1564980 1566375 := bstep (se 1 (by rfl) ⟨1174781, by rfl⟩ : syracuseStep 1566375 = 2349563) B2349563
theorem B2229943 : Blo 1564980 2229943 := bstep (se 1 (by rfl) ⟨1672457, by rfl⟩ : syracuseStep 2229943 = 3344915) B3344915
theorem B7923419 : Blo 1564980 7923419 := bstep (se 1 (by rfl) ⟨5942564, by rfl⟩ : syracuseStep 7923419 = 11885129) B11885129
theorem B1566459 : Blo 1564980 1566459 := bstep (se 1 (by rfl) ⟨1174844, by rfl⟩ : syracuseStep 1566459 = 2349689) B2349689
theorem B8464135 : Blo 1564980 8464135 := bstep (se 1 (by rfl) ⟨6348101, by rfl⟩ : syracuseStep 8464135 = 12696203) B12696203
theorem B1566495 : Blo 1564980 1566495 := bstep (se 1 (by rfl) ⟨1174871, by rfl⟩ : syracuseStep 1566495 = 2349743) B2349743
theorem B1566527 : Blo 1564980 1566527 := bstep (se 1 (by rfl) ⟨1174895, by rfl⟩ : syracuseStep 1566527 = 2349791) B2349791
theorem B1566703 : Blo 1564980 1566703 := bstep (se 1 (by rfl) ⟨1175027, by rfl⟩ : syracuseStep 1566703 = 2350055) B2350055
theorem B8161289 : Blo 1564980 8161289 := bstep (se 2 (by rfl) ⟨3060483, by rfl⟩ : syracuseStep 8161289 = 6120967) B6120967
theorem B5285897 : Blo 1564980 5285897 := bstep (se 2 (by rfl) ⟨1982211, by rfl⟩ : syracuseStep 5285897 = 3964423) B3964423
theorem B1566875 : Blo 1564980 1566875 := bstep (se 1 (by rfl) ⟨1175156, by rfl⟩ : syracuseStep 1566875 = 2350313) B2350313
theorem B1566911 : Blo 1564980 1566911 := bstep (se 1 (by rfl) ⟨1175183, by rfl⟩ : syracuseStep 1566911 = 2350367) B2350367
theorem B2230507 : Blo 1564980 2230507 := bstep (se 1 (by rfl) ⟨1672880, by rfl⟩ : syracuseStep 2230507 = 3345761) B3345761
theorem B3524903 : Blo 1564980 3524903 := bstep (se 1 (by rfl) ⟨2643677, by rfl⟩ : syracuseStep 3524903 = 5287355) B5287355
theorem B3524921 : Blo 1564980 3524921 := bstep (se 2 (by rfl) ⟨1321845, by rfl⟩ : syracuseStep 3524921 = 2643691) B2643691
theorem B8923553 : Blo 1564980 8923553 := bstep (se 2 (by rfl) ⟨3346332, by rfl⟩ : syracuseStep 8923553 = 6692665) B6692665
theorem B7924715 : Blo 1564980 7924715 := bstep (se 1 (by rfl) ⟨5943536, by rfl⟩ : syracuseStep 7924715 = 11887073) B11887073
theorem B4459499 : Blo 1564980 4459499 := bstep (se 1 (by rfl) ⟨3344624, by rfl⟩ : syracuseStep 4459499 = 6689249) B6689249
theorem B2640937 : Blo 1564980 2640937 := bstep (se 2 (by rfl) ⟨990351, by rfl⟩ : syracuseStep 2640937 = 1980703) B1980703
theorem B17837171 : Blo 1564980 17837171 := bstep (se 1 (by rfl) ⟨13377878, by rfl⟩ : syracuseStep 17837171 = 26755757) B26755757
theorem B2641079 : Blo 1564980 2641079 := bstep (se 1 (by rfl) ⟨1980809, by rfl⟩ : syracuseStep 2641079 = 3961619) B3961619
theorem B6687967 : Blo 1564980 6687967 := bstep (se 1 (by rfl) ⟨5015975, by rfl⟩ : syracuseStep 6687967 = 10031951) B10031951
theorem B5287193 : Blo 1564980 5287193 := bstep (se 2 (by rfl) ⟨1982697, by rfl⟩ : syracuseStep 5287193 = 3965395) B3965395
theorem B5287247 : Blo 1564980 5287247 := bstep (se 1 (by rfl) ⟨3965435, by rfl⟩ : syracuseStep 5287247 = 7930871) B7930871
theorem B2641403 : Blo 1564980 2641403 := bstep (se 1 (by rfl) ⟨1981052, by rfl⟩ : syracuseStep 2641403 = 3962105) B3962105
theorem B8146427 : Blo 1564980 8146427 := bstep (se 1 (by rfl) ⟨6109820, by rfl⟩ : syracuseStep 8146427 = 12219641) B12219641
theorem B90344969 : Blo 1564980 90344969 := bstep (se 2 (by rfl) ⟨33879363, by rfl⟩ : syracuseStep 90344969 = 67758727) B67758727
theorem B6434579 : Blo 1564980 6434579 := bstep (se 1 (by rfl) ⟨4825934, by rfl⟩ : syracuseStep 6434579 = 9651869) B9651869
theorem B2641835 : Blo 1564980 2641835 := bstep (se 1 (by rfl) ⟨1981376, by rfl⟩ : syracuseStep 2641835 = 3962753) B3962753
theorem B7925687 : Blo 1564980 7925687 := bstep (se 1 (by rfl) ⟨5944265, by rfl⟩ : syracuseStep 7925687 = 11888531) B11888531
theorem B13561793 : Blo 1564980 13561793 := bstep (se 2 (by rfl) ⟨5085672, by rfl⟩ : syracuseStep 13561793 = 10171345) B10171345
theorem B7139279 : Blo 1564980 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B8466383 : Blo 1564980 8466383 := bstep (se 1 (by rfl) ⟨6349787, by rfl⟩ : syracuseStep 8466383 = 12699575) B12699575
theorem B21426281 : Blo 1564980 21426281 := bstep (se 2 (by rfl) ⟨8034855, by rfl⟩ : syracuseStep 21426281 = 16069711) B16069711
theorem B3346555 : Blo 1564980 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B22589705 : Blo 1564980 22589705 := bstep (se 2 (by rfl) ⟨8471139, by rfl⟩ : syracuseStep 22589705 = 16942279) B16942279
theorem B20066615 : Blo 1564980 20066615 := bstep (se 1 (by rfl) ⟨15049961, by rfl⟩ : syracuseStep 20066615 = 30099923) B30099923
theorem B5943689 : Blo 1564980 5943689 := bstep (se 2 (by rfl) ⟨2228883, by rfl⟩ : syracuseStep 5943689 = 4457767) B4457767
theorem B26751383 : Blo 1564980 26751383 := bstep (se 1 (by rfl) ⟨20063537, by rfl⟩ : syracuseStep 26751383 = 40127075) B40127075
theorem B5943719 : Blo 1564980 5943719 := bstep (se 1 (by rfl) ⟨4457789, by rfl⟩ : syracuseStep 5943719 = 8915579) B8915579
theorem B2642375 : Blo 1564980 2642375 := bstep (se 1 (by rfl) ⟨1981781, by rfl⟩ : syracuseStep 2642375 = 3963563) B3963563
theorem B13382117 : Blo 1564980 13382117 := bstep (se 4 (by rfl) ⟨1254573, by rfl⟩ : syracuseStep 13382117 = 2509147) B2509147
theorem B5288543 : Blo 1564980 5288543 := bstep (se 1 (by rfl) ⟨3966407, by rfl⟩ : syracuseStep 5288543 = 7932815) B7932815
theorem B2347817 : Blo 1564980 2347817 := bstep (se 2 (by rfl) ⟨880431, by rfl⟩ : syracuseStep 2347817 = 1760863) B1760863
theorem B2347823 : Blo 1564980 2347823 := bstep (se 1 (by rfl) ⟨1760867, by rfl⟩ : syracuseStep 2347823 = 3521735) B3521735
theorem B13382495 : Blo 1564980 13382495 := bstep (se 1 (by rfl) ⟨10036871, by rfl⟩ : syracuseStep 13382495 = 20073743) B20073743
theorem B2347943 : Blo 1564980 2347943 := bstep (se 1 (by rfl) ⟨1760957, by rfl⟩ : syracuseStep 2347943 = 3521915) B3521915
theorem B9040871 : Blo 1564980 9040871 := bstep (se 1 (by rfl) ⟨6780653, by rfl⟩ : syracuseStep 9040871 = 13561307) B13561307
theorem B2348027 : Blo 1564980 2348027 := bstep (se 1 (by rfl) ⟨1761020, by rfl⟩ : syracuseStep 2348027 = 3522041) B3522041
theorem B2348087 : Blo 1564980 2348087 := bstep (se 1 (by rfl) ⟨1761065, by rfl⟩ : syracuseStep 2348087 = 3522131) B3522131
theorem B17847377 : Blo 1564980 17847377 := bstep (se 2 (by rfl) ⟨6692766, by rfl⟩ : syracuseStep 17847377 = 13385533) B13385533
theorem B2823275 : Blo 1564980 2823275 := bstep (se 1 (by rfl) ⟨2117456, by rfl⟩ : syracuseStep 2823275 = 4234913) B4234913
theorem B2348207 : Blo 1564980 2348207 := bstep (se 1 (by rfl) ⟨1761155, by rfl⟩ : syracuseStep 2348207 = 3522311) B3522311
theorem B4461743 : Blo 1564980 4461743 := bstep (se 1 (by rfl) ⟨3346307, by rfl⟩ : syracuseStep 4461743 = 6692615) B6692615
theorem B2643151 : Blo 1564980 2643151 := bstep (se 1 (by rfl) ⟨1982363, by rfl⟩ : syracuseStep 2643151 = 3964727) B3964727
theorem B3962267 : Blo 1564980 3962267 := bstep (se 1 (by rfl) ⟨2971700, by rfl⟩ : syracuseStep 3962267 = 5943401) B5943401
theorem B2348615 : Blo 1564980 2348615 := bstep (se 1 (by rfl) ⟨1761461, by rfl⟩ : syracuseStep 2348615 = 3522923) B3522923
theorem B2348711 : Blo 1564980 2348711 := bstep (se 1 (by rfl) ⟨1761533, by rfl⟩ : syracuseStep 2348711 = 3523067) B3523067
theorem B5019371 : Blo 1564980 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B2348795 : Blo 1564980 2348795 := bstep (se 1 (by rfl) ⟨1761596, by rfl⟩ : syracuseStep 2348795 = 3523193) B3523193
theorem B1881851 : Blo 1564980 1881851 := bstep (se 1 (by rfl) ⟨1411388, by rfl⟩ : syracuseStep 1881851 = 2822777) B2822777
theorem B2348831 : Blo 1564980 2348831 := bstep (se 1 (by rfl) ⟨1761623, by rfl⟩ : syracuseStep 2348831 = 3523247) B3523247
theorem B2348879 : Blo 1564980 2348879 := bstep (se 1 (by rfl) ⟨1761659, by rfl⟩ : syracuseStep 2348879 = 3523319) B3523319
theorem B2348999 : Blo 1564980 2348999 := bstep (se 1 (by rfl) ⟨1761749, by rfl⟩ : syracuseStep 2348999 = 3523499) B3523499
theorem B2643961 : Blo 1564980 2643961 := bstep (se 2 (by rfl) ⟨991485, by rfl⟩ : syracuseStep 2643961 = 1982971) B1982971
theorem B2644123 : Blo 1564980 2644123 := bstep (se 1 (by rfl) ⟨1983092, by rfl⟩ : syracuseStep 2644123 = 3966185) B3966185
theorem B2644231 : Blo 1564980 2644231 := bstep (se 1 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 2644231 = 3966347) B3966347
theorem B2349353 : Blo 1564980 2349353 := bstep (se 2 (by rfl) ⟨881007, by rfl⟩ : syracuseStep 2349353 = 1762015) B1762015
theorem B2644265 : Blo 1564980 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B2349359 : Blo 1564980 2349359 := bstep (se 1 (by rfl) ⟨1762019, by rfl⟩ : syracuseStep 2349359 = 3524039) B3524039
theorem B5282171 : Blo 1564980 5282171 := bstep (se 1 (by rfl) ⟨3961628, by rfl⟩ : syracuseStep 5282171 = 7923257) B7923257
theorem B2972027 : Blo 1564980 2972027 := bstep (se 1 (by rfl) ⟨2229020, by rfl⟩ : syracuseStep 2972027 = 4458041) B4458041
theorem B8460719 : Blo 1564980 8460719 := bstep (se 1 (by rfl) ⟨6345539, by rfl⟩ : syracuseStep 8460719 = 12691079) B12691079
theorem B20060621 : Blo 1564980 20060621 := bstep (se 3 (by rfl) ⟨3761366, by rfl⟩ : syracuseStep 20060621 = 7522733) B7522733
theorem B2349599 : Blo 1564980 2349599 := bstep (se 1 (by rfl) ⟨1762199, by rfl⟩ : syracuseStep 2349599 = 3524399) B3524399
theorem B5282441 : Blo 1564980 5282441 := bstep (se 2 (by rfl) ⟨1980915, by rfl⟩ : syracuseStep 5282441 = 3961831) B3961831
theorem B22584055 : Blo 1564980 22584055 := bstep (se 1 (by rfl) ⟨16938041, by rfl⟩ : syracuseStep 22584055 = 33876083) B33876083
theorem B2349983 : Blo 1564980 2349983 := bstep (se 1 (by rfl) ⟨1762487, by rfl⟩ : syracuseStep 2349983 = 3524975) B3524975
theorem B16923599 : Blo 1564980 16923599 := bstep (se 1 (by rfl) ⟨12692699, by rfl⟩ : syracuseStep 16923599 = 25385399) B25385399
theorem B2350031 : Blo 1564980 2350031 := bstep (se 1 (by rfl) ⟨1762523, by rfl⟩ : syracuseStep 2350031 = 3525047) B3525047
theorem B4291553 : Blo 1564980 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B2350121 : Blo 1564980 2350121 := bstep (se 2 (by rfl) ⟨881295, by rfl⟩ : syracuseStep 2350121 = 1762591) B1762591
theorem B2350127 : Blo 1564980 2350127 := bstep (se 1 (by rfl) ⟨1762595, by rfl⟩ : syracuseStep 2350127 = 3525191) B3525191
theorem B2350151 : Blo 1564980 2350151 := bstep (se 1 (by rfl) ⟨1762613, by rfl⟩ : syracuseStep 2350151 = 3525227) B3525227
theorem B2972855 : Blo 1564980 2972855 := bstep (se 1 (by rfl) ⟨2229641, by rfl⟩ : syracuseStep 2972855 = 4459283) B4459283
theorem B16063703 : Blo 1564980 16063703 := bstep (se 1 (by rfl) ⟨12047777, by rfl⟩ : syracuseStep 16063703 = 24095555) B24095555
theorem B5717287 : Blo 1564980 5717287 := bstep (se 1 (by rfl) ⟨4287965, by rfl⟩ : syracuseStep 5717287 = 8575931) B8575931
theorem B2350415 : Blo 1564980 2350415 := bstep (se 1 (by rfl) ⟨1762811, by rfl⟩ : syracuseStep 2350415 = 3525623) B3525623
theorem B2260391 : Blo 1564980 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B9526727 : Blo 1564980 9526727 := bstep (se 1 (by rfl) ⟨7145045, by rfl⟩ : syracuseStep 9526727 = 14290091) B14290091
theorem B192896477 : Blo 1564980 192896477 := bstep (se 3 (by rfl) ⟨36168089, by rfl⟩ : syracuseStep 192896477 = 72336179) B72336179
theorem B3522023 : Blo 1564980 3522023 := bstep (se 1 (by rfl) ⟨2641517, by rfl⟩ : syracuseStep 3522023 = 5283035) B5283035
theorem B11894363 : Blo 1564980 11894363 := bstep (se 1 (by rfl) ⟨8920772, by rfl⟩ : syracuseStep 11894363 = 17841545) B17841545
theorem B16080619 : Blo 1564980 16080619 := bstep (se 1 (by rfl) ⟨12060464, by rfl⟩ : syracuseStep 16080619 = 24120929) B24120929
theorem B5283575 : Blo 1564980 5283575 := bstep (se 1 (by rfl) ⟨3962681, by rfl⟩ : syracuseStep 5283575 = 7925363) B7925363
theorem B8920955 : Blo 1564980 8920955 := bstep (se 1 (by rfl) ⟨6690716, by rfl⟩ : syracuseStep 8920955 = 13381433) B13381433
theorem B13377743 : Blo 1564980 13377743 := bstep (se 1 (by rfl) ⟨10033307, by rfl⟩ : syracuseStep 13377743 = 20066615) B20066615
theorem B17834255 : Blo 1564980 17834255 := bstep (se 1 (by rfl) ⟨13375691, by rfl⟩ : syracuseStep 17834255 = 26751383) B26751383
theorem B7528733 : Blo 1564980 7528733 := bstep (se 3 (by rfl) ⟨1411637, by rfl⟩ : syracuseStep 7528733 = 2823275) B2823275
theorem B2228519 : Blo 1564980 2228519 := bstep (se 1 (by rfl) ⟨1671389, by rfl⟩ : syracuseStep 2228519 = 3342779) B3342779
theorem B1761583 : Blo 1564980 1761583 := bstep (se 1 (by rfl) ⟨1321187, by rfl⟩ : syracuseStep 1761583 = 2642375) B2642375
theorem B2974009 : Blo 1564980 2974009 := bstep (se 2 (by rfl) ⟨1115253, by rfl⟩ : syracuseStep 2974009 = 2230507) B2230507
theorem B8921411 : Blo 1564980 8921411 := bstep (se 1 (by rfl) ⟨6691058, by rfl⟩ : syracuseStep 8921411 = 13382117) B13382117
theorem B7930223 : Blo 1564980 7930223 := bstep (se 1 (by rfl) ⟨5947667, by rfl⟩ : syracuseStep 7930223 = 11895335) B11895335
theorem B1565211 : Blo 1564980 1565211 := bstep (se 1 (by rfl) ⟨1173908, by rfl⟩ : syracuseStep 1565211 = 2347817) B2347817
theorem B1565215 : Blo 1564980 1565215 := bstep (se 1 (by rfl) ⟨1173911, by rfl⟩ : syracuseStep 1565215 = 2347823) B2347823
theorem B3523103 : Blo 1564980 3523103 := bstep (se 1 (by rfl) ⟨2642327, by rfl⟩ : syracuseStep 3523103 = 5284655) B5284655
theorem B8921663 : Blo 1564980 8921663 := bstep (se 1 (by rfl) ⟨6691247, by rfl⟩ : syracuseStep 8921663 = 13382495) B13382495
theorem B3523175 : Blo 1564980 3523175 := bstep (se 1 (by rfl) ⟨2642381, by rfl⟩ : syracuseStep 3523175 = 5284763) B5284763
theorem B1565295 : Blo 1564980 1565295 := bstep (se 1 (by rfl) ⟨1173971, by rfl⟩ : syracuseStep 1565295 = 2347943) B2347943
theorem B1565351 : Blo 1564980 1565351 := bstep (se 1 (by rfl) ⟨1174013, by rfl⟩ : syracuseStep 1565351 = 2348027) B2348027
theorem B1565391 : Blo 1564980 1565391 := bstep (se 1 (by rfl) ⟨1174043, by rfl⟩ : syracuseStep 1565391 = 2348087) B2348087
theorem B1565471 : Blo 1564980 1565471 := bstep (se 1 (by rfl) ⟨1174103, by rfl⟩ : syracuseStep 1565471 = 2348207) B2348207
theorem B2974495 : Blo 1564980 2974495 := bstep (se 1 (by rfl) ⟨2230871, by rfl⟩ : syracuseStep 2974495 = 4461743) B4461743
theorem B3343369 : Blo 1564980 3343369 := bstep (se 2 (by rfl) ⟨1253763, by rfl⟩ : syracuseStep 3343369 = 2507527) B2507527
theorem B1565743 : Blo 1564980 1565743 := bstep (se 1 (by rfl) ⟨1174307, by rfl⟩ : syracuseStep 1565743 = 2348615) B2348615
theorem B1565807 : Blo 1564980 1565807 := bstep (se 1 (by rfl) ⟨1174355, by rfl⟩ : syracuseStep 1565807 = 2348711) B2348711
theorem B1565863 : Blo 1564980 1565863 := bstep (se 1 (by rfl) ⟨1174397, by rfl⟩ : syracuseStep 1565863 = 2348795) B2348795
theorem B1565887 : Blo 1564980 1565887 := bstep (se 1 (by rfl) ⟨1174415, by rfl⟩ : syracuseStep 1565887 = 2348831) B2348831
theorem B1565919 : Blo 1564980 1565919 := bstep (se 1 (by rfl) ⟨1174439, by rfl⟩ : syracuseStep 1565919 = 2348879) B2348879
theorem B1565999 : Blo 1564980 1565999 := bstep (se 1 (by rfl) ⟨1174499, by rfl⟩ : syracuseStep 1565999 = 2348999) B2348999
theorem B5440859 : Blo 1564980 5440859 := bstep (se 1 (by rfl) ⟨4080644, by rfl⟩ : syracuseStep 5440859 = 8161289) B8161289
theorem B3523931 : Blo 1564980 3523931 := bstep (se 1 (by rfl) ⟨2642948, by rfl⟩ : syracuseStep 3523931 = 5285897) B5285897
theorem B1566235 : Blo 1564980 1566235 := bstep (se 1 (by rfl) ⟨1174676, by rfl⟩ : syracuseStep 1566235 = 2349353) B2349353
theorem B1762843 : Blo 1564980 1762843 := bstep (se 1 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 1762843 = 2644265) B2644265
theorem B1566239 : Blo 1564980 1566239 := bstep (se 1 (by rfl) ⟨1174679, by rfl⟩ : syracuseStep 1566239 = 2349359) B2349359
theorem B30492197 : Blo 1564980 30492197 := bstep (se 4 (by rfl) ⟨2858643, by rfl⟩ : syracuseStep 30492197 = 5717287) B5717287
theorem B3524201 : Blo 1564980 3524201 := bstep (se 2 (by rfl) ⟨1321575, by rfl⟩ : syracuseStep 3524201 = 2643151) B2643151
theorem B5949035 : Blo 1564980 5949035 := bstep (se 1 (by rfl) ⟨4461776, by rfl⟩ : syracuseStep 5949035 = 8923553) B8923553
theorem B1566399 : Blo 1564980 1566399 := bstep (se 1 (by rfl) ⟨1174799, by rfl⟩ : syracuseStep 1566399 = 2349599) B2349599
theorem B1566655 : Blo 1564980 1566655 := bstep (se 1 (by rfl) ⟨1174991, by rfl⟩ : syracuseStep 1566655 = 2349983) B2349983
theorem B11282399 : Blo 1564980 11282399 := bstep (se 1 (by rfl) ⟨8461799, by rfl⟩ : syracuseStep 11282399 = 16923599) B16923599
theorem B1566687 : Blo 1564980 1566687 := bstep (se 1 (by rfl) ⟨1175015, by rfl⟩ : syracuseStep 1566687 = 2350031) B2350031
theorem B1566747 : Blo 1564980 1566747 := bstep (se 1 (by rfl) ⟨1175060, by rfl⟩ : syracuseStep 1566747 = 2350121) B2350121
theorem B1566751 : Blo 1564980 1566751 := bstep (se 1 (by rfl) ⟨1175063, by rfl⟩ : syracuseStep 1566751 = 2350127) B2350127
theorem B1566767 : Blo 1564980 1566767 := bstep (se 1 (by rfl) ⟨1175075, by rfl⟩ : syracuseStep 1566767 = 2350151) B2350151
theorem B7145597 : Blo 1564980 7145597 := bstep (se 3 (by rfl) ⟨1339799, by rfl⟩ : syracuseStep 7145597 = 2679599) B2679599
theorem B10709135 : Blo 1564980 10709135 := bstep (se 1 (by rfl) ⟨8031851, by rfl⟩ : syracuseStep 10709135 = 16063703) B16063703
theorem B3524795 : Blo 1564980 3524795 := bstep (se 1 (by rfl) ⟨2643596, by rfl⟩ : syracuseStep 3524795 = 5287193) B5287193
theorem B3524831 : Blo 1564980 3524831 := bstep (se 1 (by rfl) ⟨2643623, by rfl⟩ : syracuseStep 3524831 = 5287247) B5287247
theorem B1566943 : Blo 1564980 1566943 := bstep (se 1 (by rfl) ⟨1175207, by rfl⟩ : syracuseStep 1566943 = 2350415) B2350415
theorem B6351151 : Blo 1564980 6351151 := bstep (se 1 (by rfl) ⟨4763363, by rfl⟩ : syracuseStep 6351151 = 9526727) B9526727
theorem B21440825 : Blo 1564980 21440825 := bstep (se 2 (by rfl) ⟨8040309, by rfl⟩ : syracuseStep 21440825 = 16080619) B16080619
theorem B60229979 : Blo 1564980 60229979 := bstep (se 1 (by rfl) ⟨45172484, by rfl⟩ : syracuseStep 60229979 = 90344969) B90344969
theorem B3525281 : Blo 1564980 3525281 := bstep (se 2 (by rfl) ⟨1321980, by rfl⟩ : syracuseStep 3525281 = 2643961) B2643961
theorem B8923871 : Blo 1564980 8923871 := bstep (se 1 (by rfl) ⟨6692903, by rfl⟩ : syracuseStep 8923871 = 13385807) B13385807
theorem B15059803 : Blo 1564980 15059803 := bstep (se 1 (by rfl) ⟨11294852, by rfl⟩ : syracuseStep 15059803 = 22589705) B22589705
theorem B3525497 : Blo 1564980 3525497 := bstep (se 2 (by rfl) ⟨1322061, by rfl⟩ : syracuseStep 3525497 = 2644123) B2644123
theorem B17165195 : Blo 1564980 17165195 := bstep (se 1 (by rfl) ⟨12873896, by rfl⟩ : syracuseStep 17165195 = 25747793) B25747793
theorem B3525641 : Blo 1564980 3525641 := bstep (se 2 (by rfl) ⟨1322115, by rfl⟩ : syracuseStep 3525641 = 2644231) B2644231
theorem B3525695 : Blo 1564980 3525695 := bstep (se 1 (by rfl) ⟨2644271, by rfl⟩ : syracuseStep 3525695 = 5288543) B5288543
theorem B11898251 : Blo 1564980 11898251 := bstep (se 1 (by rfl) ⟨8923688, by rfl⟩ : syracuseStep 11898251 = 17847377) B17847377
theorem B11283895 : Blo 1564980 11283895 := bstep (se 1 (by rfl) ⟨8462921, by rfl⟩ : syracuseStep 11283895 = 16925843) B16925843
theorem B2641511 : Blo 1564980 2641511 := bstep (se 1 (by rfl) ⟨1981133, by rfl⟩ : syracuseStep 2641511 = 3962267) B3962267
theorem B3346247 : Blo 1564980 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B5640479 : Blo 1564980 5640479 := bstep (se 1 (by rfl) ⟨4230359, by rfl⟩ : syracuseStep 5640479 = 8460719) B8460719
theorem B8917289 : Blo 1564980 8917289 := bstep (se 2 (by rfl) ⟨3343983, by rfl⟩ : syracuseStep 8917289 = 6687967) B6687967
theorem B13373747 : Blo 1564980 13373747 := bstep (se 1 (by rfl) ⟨10030310, by rfl⟩ : syracuseStep 13373747 = 20060621) B20060621
theorem B6689213 : Blo 1564980 6689213 := bstep (se 3 (by rfl) ⟨1254227, by rfl⟩ : syracuseStep 6689213 = 2508455) B2508455
theorem B5018269 : Blo 1564980 5018269 := bstep (se 3 (by rfl) ⟨940925, by rfl⟩ : syracuseStep 5018269 = 1881851) B1881851
theorem B17158877 : Blo 1564980 17158877 := bstep (se 3 (by rfl) ⟨3217289, by rfl⟩ : syracuseStep 17158877 = 6434579) B6434579
theorem B11891447 : Blo 1564980 11891447 := bstep (se 1 (by rfl) ⟨8918585, by rfl⟩ : syracuseStep 11891447 = 17837171) B17837171
theorem B2348015 : Blo 1564980 2348015 := bstep (se 1 (by rfl) ⟨1761011, by rfl⟩ : syracuseStep 2348015 = 3522023) B3522023
theorem B11285513 : Blo 1564980 11285513 := bstep (se 2 (by rfl) ⟨4232067, by rfl⟩ : syracuseStep 11285513 = 8464135) B8464135
theorem B9041195 : Blo 1564980 9041195 := bstep (se 1 (by rfl) ⟨6780896, by rfl⟩ : syracuseStep 9041195 = 13561793) B13561793
theorem B2348399 : Blo 1564980 2348399 := bstep (se 1 (by rfl) ⟨1761299, by rfl⟩ : syracuseStep 2348399 = 3522599) B3522599
theorem B14284187 : Blo 1564980 14284187 := bstep (se 1 (by rfl) ⟨10713140, by rfl⟩ : syracuseStep 14284187 = 21426281) B21426281
theorem B2348519 : Blo 1564980 2348519 := bstep (se 1 (by rfl) ⟨1761389, by rfl⟩ : syracuseStep 2348519 = 3522779) B3522779
theorem B4462073 : Blo 1564980 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B5355005 : Blo 1564980 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B15046195 : Blo 1564980 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B3962459 : Blo 1564980 3962459 := bstep (se 1 (by rfl) ⟨2971844, by rfl⟩ : syracuseStep 3962459 = 5943689) B5943689
theorem B3962479 : Blo 1564980 3962479 := bstep (se 1 (by rfl) ⟨2971859, by rfl⟩ : syracuseStep 3962479 = 5943719) B5943719
theorem B2348681 : Blo 1564980 2348681 := bstep (se 2 (by rfl) ⟨880755, by rfl⟩ : syracuseStep 2348681 = 1761511) B1761511
theorem B2348699 : Blo 1564980 2348699 := bstep (se 1 (by rfl) ⟨1761524, by rfl⟩ : syracuseStep 2348699 = 3523049) B3523049
theorem B8918747 : Blo 1564980 8918747 := bstep (se 1 (by rfl) ⟨6689060, by rfl⟩ : syracuseStep 8918747 = 13378121) B13378121
theorem B2348891 : Blo 1564980 2348891 := bstep (se 1 (by rfl) ⟨1761668, by rfl⟩ : syracuseStep 2348891 = 3523337) B3523337
theorem B6027247 : Blo 1564980 6027247 := bstep (se 1 (by rfl) ⟨4520435, by rfl⟩ : syracuseStep 6027247 = 9040871) B9040871
theorem B2349275 : Blo 1564980 2349275 := bstep (se 1 (by rfl) ⟨1761956, by rfl⟩ : syracuseStep 2349275 = 3523913) B3523913
theorem B30112073 : Blo 1564980 30112073 := bstep (se 2 (by rfl) ⟨11292027, by rfl⟩ : syracuseStep 30112073 = 22584055) B22584055
theorem B6027709 : Blo 1564980 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B5282279 : Blo 1564980 5282279 := bstep (se 1 (by rfl) ⟨3961709, by rfl⟩ : syracuseStep 5282279 = 7923419) B7923419
theorem B2349545 : Blo 1564980 2349545 := bstep (se 2 (by rfl) ⟨881079, by rfl⟩ : syracuseStep 2349545 = 1762159) B1762159
theorem B21723805 : Blo 1564980 21723805 := bstep (se 3 (by rfl) ⟨4073213, by rfl⟩ : syracuseStep 21723805 = 8146427) B8146427
theorem B3521249 : Blo 1564980 3521249 := bstep (se 2 (by rfl) ⟨1320468, by rfl⟩ : syracuseStep 3521249 = 2640937) B2640937
theorem B2349935 : Blo 1564980 2349935 := bstep (se 1 (by rfl) ⟨1762451, by rfl⟩ : syracuseStep 2349935 = 3524903) B3524903
theorem B2349947 : Blo 1564980 2349947 := bstep (se 1 (by rfl) ⟨1762460, by rfl⟩ : syracuseStep 2349947 = 3524921) B3524921
theorem B3521447 : Blo 1564980 3521447 := bstep (se 1 (by rfl) ⟨2641085, by rfl⟩ : syracuseStep 3521447 = 5282171) B5282171
theorem B1981351 : Blo 1564980 1981351 := bstep (se 1 (by rfl) ⟨1486013, by rfl⟩ : syracuseStep 1981351 = 2972027) B2972027
theorem B3521627 : Blo 1564980 3521627 := bstep (se 1 (by rfl) ⟨2641220, by rfl⟩ : syracuseStep 3521627 = 5282441) B5282441
theorem B5283143 : Blo 1564980 5283143 := bstep (se 1 (by rfl) ⟨3962357, by rfl⟩ : syracuseStep 5283143 = 7924715) B7924715
theorem B2972999 : Blo 1564980 2972999 := bstep (se 1 (by rfl) ⟨2229749, by rfl⟩ : syracuseStep 2972999 = 4459499) B4459499
theorem B1760719 : Blo 1564980 1760719 := bstep (se 1 (by rfl) ⟨1320539, by rfl⟩ : syracuseStep 1760719 = 2641079) B2641079
theorem B1981903 : Blo 1564980 1981903 := bstep (se 1 (by rfl) ⟨1486427, by rfl⟩ : syracuseStep 1981903 = 2972855) B2972855
theorem B2973257 : Blo 1564980 2973257 := bstep (se 2 (by rfl) ⟨1114971, by rfl⟩ : syracuseStep 2973257 = 2229943) B2229943
theorem B128597651 : Blo 1564980 128597651 := bstep (se 1 (by rfl) ⟨96448238, by rfl⟩ : syracuseStep 128597651 = 192896477) B192896477
theorem B1760935 : Blo 1564980 1760935 := bstep (se 1 (by rfl) ⟨1320701, by rfl⟩ : syracuseStep 1760935 = 2641403) B2641403
theorem B7929575 : Blo 1564980 7929575 := bstep (se 1 (by rfl) ⟨5947181, by rfl⟩ : syracuseStep 7929575 = 11894363) B11894363
theorem B3522383 : Blo 1564980 3522383 := bstep (se 1 (by rfl) ⟨2641787, by rfl⟩ : syracuseStep 3522383 = 5283575) B5283575
theorem B19038077 : Blo 1564980 19038077 := bstep (se 3 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 19038077 = 7139279) B7139279
theorem B5947303 : Blo 1564980 5947303 := bstep (se 1 (by rfl) ⟨4460477, by rfl⟩ : syracuseStep 5947303 = 8920955) B8920955
theorem B11444141 : Blo 1564980 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B1761223 : Blo 1564980 1761223 := bstep (se 1 (by rfl) ⟨1320917, by rfl⟩ : syracuseStep 1761223 = 2641835) B2641835
theorem B5283791 : Blo 1564980 5283791 := bstep (se 1 (by rfl) ⟨3962843, by rfl⟩ : syracuseStep 5283791 = 7925687) B7925687
theorem B5644255 : Blo 1564980 5644255 := bstep (se 1 (by rfl) ⟨4233191, by rfl⟩ : syracuseStep 5644255 = 8466383) B8466383
theorem B3760319 : Blo 1564980 3760319 := bstep (se 1 (by rfl) ⟨2820239, by rfl⟩ : syracuseStep 3760319 = 5640479) B5640479
theorem B5947607 : Blo 1564980 5947607 := bstep (se 1 (by rfl) ⟨4460705, by rfl⟩ : syracuseStep 5947607 = 8921411) B8921411
theorem B5947775 : Blo 1564980 5947775 := bstep (se 1 (by rfl) ⟨4460831, by rfl⟩ : syracuseStep 5947775 = 8921663) B8921663
theorem B3965345 : Blo 1564980 3965345 := bstep (se 2 (by rfl) ⟨1487004, by rfl⟩ : syracuseStep 3965345 = 2974009) B2974009
theorem B8036945 : Blo 1564980 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B1565343 : Blo 1564980 1565343 := bstep (se 1 (by rfl) ⟨1174007, by rfl⟩ : syracuseStep 1565343 = 2348015) B2348015
theorem B1565599 : Blo 1564980 1565599 := bstep (se 1 (by rfl) ⟨1174199, by rfl⟩ : syracuseStep 1565599 = 2348399) B2348399
theorem B1565679 : Blo 1564980 1565679 := bstep (se 1 (by rfl) ⟨1174259, by rfl⟩ : syracuseStep 1565679 = 2348519) B2348519
theorem B2974715 : Blo 1564980 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B3965993 : Blo 1564980 3965993 := bstep (se 2 (by rfl) ⟨1487247, by rfl⟩ : syracuseStep 3965993 = 2974495) B2974495
theorem B3966023 : Blo 1564980 3966023 := bstep (se 1 (by rfl) ⟨2974517, by rfl⟩ : syracuseStep 3966023 = 5949035) B5949035
theorem B1565787 : Blo 1564980 1565787 := bstep (se 1 (by rfl) ⟨1174340, by rfl⟩ : syracuseStep 1565787 = 2348681) B2348681
theorem B1565799 : Blo 1564980 1565799 := bstep (se 1 (by rfl) ⟨1174349, by rfl⟩ : syracuseStep 1565799 = 2348699) B2348699
theorem B20079737 : Blo 1564980 20079737 := bstep (se 2 (by rfl) ⟨7529901, by rfl⟩ : syracuseStep 20079737 = 15059803) B15059803
theorem B1565927 : Blo 1564980 1565927 := bstep (se 1 (by rfl) ⟨1174445, by rfl⟩ : syracuseStep 1565927 = 2348891) B2348891
theorem B7521599 : Blo 1564980 7521599 := bstep (se 1 (by rfl) ⟨5641199, by rfl⟩ : syracuseStep 7521599 = 11282399) B11282399
theorem B14280013 : Blo 1564980 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B4457825 : Blo 1564980 4457825 := bstep (se 2 (by rfl) ⟨1671684, by rfl⟩ : syracuseStep 4457825 = 3343369) B3343369
theorem B1566183 : Blo 1564980 1566183 := bstep (se 1 (by rfl) ⟨1174637, by rfl⟩ : syracuseStep 1566183 = 2349275) B2349275
theorem B1566363 : Blo 1564980 1566363 := bstep (se 1 (by rfl) ⟨1174772, by rfl⟩ : syracuseStep 1566363 = 2349545) B2349545
theorem B5949247 : Blo 1564980 5949247 := bstep (se 1 (by rfl) ⟨4461935, by rfl⟩ : syracuseStep 5949247 = 8923871) B8923871
theorem B1566623 : Blo 1564980 1566623 := bstep (se 1 (by rfl) ⟨1174967, by rfl⟩ : syracuseStep 1566623 = 2349935) B2349935
theorem B1566631 : Blo 1564980 1566631 := bstep (se 1 (by rfl) ⟨1174973, by rfl⟩ : syracuseStep 1566631 = 2349947) B2349947
theorem B7932167 : Blo 1564980 7932167 := bstep (se 1 (by rfl) ⟨5949125, by rfl⟩ : syracuseStep 7932167 = 11898251) B11898251
theorem B85731767 : Blo 1564980 85731767 := bstep (se 1 (by rfl) ⟨64298825, by rfl⟩ : syracuseStep 85731767 = 128597651) B128597651
theorem B5286383 : Blo 1564980 5286383 := bstep (se 1 (by rfl) ⟨3964787, by rfl⟩ : syracuseStep 5286383 = 7929575) B7929575
theorem B2230831 : Blo 1564980 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B12692051 : Blo 1564980 12692051 := bstep (se 1 (by rfl) ⟨9519038, by rfl⟩ : syracuseStep 12692051 = 19038077) B19038077
theorem B7629427 : Blo 1564980 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B11889503 : Blo 1564980 11889503 := bstep (se 1 (by rfl) ⟨8917127, by rfl⟩ : syracuseStep 11889503 = 17834255) B17834255
theorem B8915831 : Blo 1564980 8915831 := bstep (se 1 (by rfl) ⟨6686873, by rfl⟩ : syracuseStep 8915831 = 13373747) B13373747
theorem B5286815 : Blo 1564980 5286815 := bstep (se 1 (by rfl) ⟨3965111, by rfl⟩ : syracuseStep 5286815 = 7930223) B7930223
theorem B4459475 : Blo 1564980 4459475 := bstep (se 1 (by rfl) ⟨3344606, by rfl⟩ : syracuseStep 4459475 = 6689213) B6689213
theorem B11439251 : Blo 1564980 11439251 := bstep (se 1 (by rfl) ⟨8579438, by rfl⟩ : syracuseStep 11439251 = 17158877) B17158877
theorem B7523675 : Blo 1564980 7523675 := bstep (se 1 (by rfl) ⟨5642756, by rfl⟩ : syracuseStep 7523675 = 11285513) B11285513
theorem B5942717 : Blo 1564980 5942717 := bstep (se 3 (by rfl) ⟨1114259, by rfl⟩ : syracuseStep 5942717 = 2228519) B2228519
theorem B9522791 : Blo 1564980 9522791 := bstep (se 1 (by rfl) ⟨7142093, by rfl⟩ : syracuseStep 9522791 = 14284187) B14284187
theorem B20328131 : Blo 1564980 20328131 := bstep (se 1 (by rfl) ⟨15246098, by rfl⟩ : syracuseStep 20328131 = 30492197) B30492197
theorem B2641639 : Blo 1564980 2641639 := bstep (se 1 (by rfl) ⟨1981229, by rfl⟩ : syracuseStep 2641639 = 3962459) B3962459
theorem B2641801 : Blo 1564980 2641801 := bstep (se 2 (by rfl) ⟨990675, by rfl⟩ : syracuseStep 2641801 = 1981351) B1981351
theorem B4763731 : Blo 1564980 4763731 := bstep (se 1 (by rfl) ⟨3572798, by rfl⟩ : syracuseStep 4763731 = 7145597) B7145597
theorem B7139423 : Blo 1564980 7139423 := bstep (se 1 (by rfl) ⟨5354567, by rfl⟩ : syracuseStep 7139423 = 10709135) B10709135
theorem B20074715 : Blo 1564980 20074715 := bstep (se 1 (by rfl) ⟨15056036, by rfl⟩ : syracuseStep 20074715 = 30112073) B30112073
theorem B40153319 : Blo 1564980 40153319 := bstep (se 1 (by rfl) ⟨30114989, by rfl⟩ : syracuseStep 40153319 = 60229979) B60229979
theorem B2347499 : Blo 1564980 2347499 := bstep (se 1 (by rfl) ⟨1760624, by rfl⟩ : syracuseStep 2347499 = 3521249) B3521249
theorem B15045193 : Blo 1564980 15045193 := bstep (se 2 (by rfl) ⟨5641947, by rfl⟩ : syracuseStep 15045193 = 11283895) B11283895
theorem B2347625 : Blo 1564980 2347625 := bstep (se 2 (by rfl) ⟨880359, by rfl⟩ : syracuseStep 2347625 = 1760719) B1760719
theorem B2642537 : Blo 1564980 2642537 := bstep (se 2 (by rfl) ⟨990951, by rfl⟩ : syracuseStep 2642537 = 1981903) B1981903
theorem B2347631 : Blo 1564980 2347631 := bstep (se 1 (by rfl) ⟨1760723, by rfl⟩ : syracuseStep 2347631 = 3521447) B3521447
theorem B2347751 : Blo 1564980 2347751 := bstep (se 1 (by rfl) ⟨1760813, by rfl⟩ : syracuseStep 2347751 = 3521627) B3521627
theorem B2347913 : Blo 1564980 2347913 := bstep (se 2 (by rfl) ⟨880467, by rfl⟩ : syracuseStep 2347913 = 1760935) B1760935
theorem B2348255 : Blo 1564980 2348255 := bstep (se 1 (by rfl) ⟨1761191, by rfl⟩ : syracuseStep 2348255 = 3522383) B3522383
theorem B2348297 : Blo 1564980 2348297 := bstep (se 2 (by rfl) ⟨880611, by rfl⟩ : syracuseStep 2348297 = 1761223) B1761223
theorem B7525673 : Blo 1564980 7525673 := bstep (se 2 (by rfl) ⟨2822127, by rfl⟩ : syracuseStep 7525673 = 5644255) B5644255
theorem B8918495 : Blo 1564980 8918495 := bstep (se 1 (by rfl) ⟨6688871, by rfl⟩ : syracuseStep 8918495 = 13377743) B13377743
theorem B5019155 : Blo 1564980 5019155 := bstep (se 1 (by rfl) ⟨3764366, by rfl⟩ : syracuseStep 5019155 = 7528733) B7528733
theorem B5944859 : Blo 1564980 5944859 := bstep (se 1 (by rfl) ⟨4458644, by rfl⟩ : syracuseStep 5944859 = 8917289) B8917289
theorem B2348735 : Blo 1564980 2348735 := bstep (se 1 (by rfl) ⟨1761551, by rfl⟩ : syracuseStep 2348735 = 3523103) B3523103
theorem B2348777 : Blo 1564980 2348777 := bstep (se 2 (by rfl) ⟨880791, by rfl⟩ : syracuseStep 2348777 = 1761583) B1761583
theorem B8468201 : Blo 1564980 8468201 := bstep (se 2 (by rfl) ⟨3175575, by rfl⟩ : syracuseStep 8468201 = 6351151) B6351151
theorem B2348783 : Blo 1564980 2348783 := bstep (se 1 (by rfl) ⟨1761587, by rfl⟩ : syracuseStep 2348783 = 3523175) B3523175
theorem B7927631 : Blo 1564980 7927631 := bstep (se 1 (by rfl) ⟨5945723, by rfl⟩ : syracuseStep 7927631 = 11891447) B11891447
theorem B6027463 : Blo 1564980 6027463 := bstep (se 1 (by rfl) ⟨4520597, by rfl⟩ : syracuseStep 6027463 = 9041195) B9041195
theorem B28965073 : Blo 1564980 28965073 := bstep (se 2 (by rfl) ⟨10861902, by rfl⟩ : syracuseStep 28965073 = 21723805) B21723805
theorem B6691025 : Blo 1564980 6691025 := bstep (se 2 (by rfl) ⟨2509134, by rfl⟩ : syracuseStep 6691025 = 5018269) B5018269
theorem B3627239 : Blo 1564980 3627239 := bstep (se 1 (by rfl) ⟨2720429, by rfl⟩ : syracuseStep 3627239 = 5440859) B5440859
theorem B2349287 : Blo 1564980 2349287 := bstep (se 1 (by rfl) ⟨1761965, by rfl⟩ : syracuseStep 2349287 = 3523931) B3523931
theorem B2349467 : Blo 1564980 2349467 := bstep (se 1 (by rfl) ⟨1762100, by rfl⟩ : syracuseStep 2349467 = 3524201) B3524201
theorem B5945831 : Blo 1564980 5945831 := bstep (se 1 (by rfl) ⟨4459373, by rfl⟩ : syracuseStep 5945831 = 8918747) B8918747
theorem B2349863 : Blo 1564980 2349863 := bstep (se 1 (by rfl) ⟨1762397, by rfl⟩ : syracuseStep 2349863 = 3524795) B3524795
theorem B2349887 : Blo 1564980 2349887 := bstep (se 1 (by rfl) ⟨1762415, by rfl⟩ : syracuseStep 2349887 = 3524831) B3524831
theorem B14293883 : Blo 1564980 14293883 := bstep (se 1 (by rfl) ⟨10720412, by rfl⟩ : syracuseStep 14293883 = 21440825) B21440825
theorem B3521519 : Blo 1564980 3521519 := bstep (se 1 (by rfl) ⟨2641139, by rfl⟩ : syracuseStep 3521519 = 5282279) B5282279
theorem B2350187 : Blo 1564980 2350187 := bstep (se 1 (by rfl) ⟨1762640, by rfl⟩ : syracuseStep 2350187 = 3525281) B3525281
theorem B2350331 : Blo 1564980 2350331 := bstep (se 1 (by rfl) ⟨1762748, by rfl⟩ : syracuseStep 2350331 = 3525497) B3525497
theorem B11443463 : Blo 1564980 11443463 := bstep (se 1 (by rfl) ⟨8582597, by rfl⟩ : syracuseStep 11443463 = 17165195) B17165195
theorem B2350427 : Blo 1564980 2350427 := bstep (se 1 (by rfl) ⟨1762820, by rfl⟩ : syracuseStep 2350427 = 3525641) B3525641
theorem B2350457 : Blo 1564980 2350457 := bstep (se 2 (by rfl) ⟨881421, by rfl⟩ : syracuseStep 2350457 = 1762843) B1762843
theorem B2350463 : Blo 1564980 2350463 := bstep (se 1 (by rfl) ⟨1762847, by rfl⟩ : syracuseStep 2350463 = 3525695) B3525695
theorem B20061593 : Blo 1564980 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B5283305 : Blo 1564980 5283305 := bstep (se 2 (by rfl) ⟨1981239, by rfl⟩ : syracuseStep 5283305 = 3962479) B3962479
theorem B3522095 : Blo 1564980 3522095 := bstep (se 1 (by rfl) ⟨2641571, by rfl⟩ : syracuseStep 3522095 = 5283143) B5283143
theorem B1981999 : Blo 1564980 1981999 := bstep (se 1 (by rfl) ⟨1486499, by rfl⟩ : syracuseStep 1981999 = 2972999) B2972999
theorem B1982171 : Blo 1564980 1982171 := bstep (se 1 (by rfl) ⟨1486628, by rfl⟩ : syracuseStep 1982171 = 2973257) B2973257
theorem B1761007 : Blo 1564980 1761007 := bstep (se 1 (by rfl) ⟨1320755, by rfl⟩ : syracuseStep 1761007 = 2641511) B2641511
theorem B7929737 : Blo 1564980 7929737 := bstep (se 2 (by rfl) ⟨2973651, by rfl⟩ : syracuseStep 7929737 = 5947303) B5947303
theorem B3522527 : Blo 1564980 3522527 := bstep (se 1 (by rfl) ⟨2641895, by rfl⟩ : syracuseStep 3522527 = 5283791) B5283791
theorem B8036329 : Blo 1564980 8036329 := bstep (se 2 (by rfl) ⟨3013623, by rfl⟩ : syracuseStep 8036329 = 6027247) B6027247
theorem B4759615 : Blo 1564980 4759615 := bstep (se 1 (by rfl) ⟨3569711, by rfl⟩ : syracuseStep 4759615 = 7139423) B7139423
theorem B2506879 : Blo 1564980 2506879 := bstep (se 1 (by rfl) ⟨1880159, by rfl⟩ : syracuseStep 2506879 = 3760319) B3760319
theorem B3965071 : Blo 1564980 3965071 := bstep (se 1 (by rfl) ⟨2973803, by rfl⟩ : syracuseStep 3965071 = 5947607) B5947607
theorem B3965183 : Blo 1564980 3965183 := bstep (se 1 (by rfl) ⟨2973887, by rfl⟩ : syracuseStep 3965183 = 5947775) B5947775
theorem B8036617 : Blo 1564980 8036617 := bstep (se 2 (by rfl) ⟨3013731, by rfl⟩ : syracuseStep 8036617 = 6027463) B6027463
theorem B1564999 : Blo 1564980 1564999 := bstep (se 1 (by rfl) ⟨1173749, by rfl⟩ : syracuseStep 1564999 = 2347499) B2347499
theorem B5357963 : Blo 1564980 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B1565083 : Blo 1564980 1565083 := bstep (se 1 (by rfl) ⟨1173812, by rfl⟩ : syracuseStep 1565083 = 2347625) B2347625
theorem B1761691 : Blo 1564980 1761691 := bstep (se 1 (by rfl) ⟨1321268, by rfl⟩ : syracuseStep 1761691 = 2642537) B2642537
theorem B1565087 : Blo 1564980 1565087 := bstep (se 1 (by rfl) ⟨1173815, by rfl⟩ : syracuseStep 1565087 = 2347631) B2347631
theorem B1565167 : Blo 1564980 1565167 := bstep (se 1 (by rfl) ⟨1173875, by rfl⟩ : syracuseStep 1565167 = 2347751) B2347751
theorem B1565275 : Blo 1564980 1565275 := bstep (se 1 (by rfl) ⟨1173956, by rfl⟩ : syracuseStep 1565275 = 2347913) B2347913
theorem B1983143 : Blo 1564980 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B13386491 : Blo 1564980 13386491 := bstep (se 1 (by rfl) ⟨10039868, by rfl⟩ : syracuseStep 13386491 = 20079737) B20079737
theorem B1565503 : Blo 1564980 1565503 := bstep (se 1 (by rfl) ⟨1174127, by rfl⟩ : syracuseStep 1565503 = 2348255) B2348255
theorem B1565531 : Blo 1564980 1565531 := bstep (se 1 (by rfl) ⟨1174148, by rfl⟩ : syracuseStep 1565531 = 2348297) B2348297
theorem B5014399 : Blo 1564980 5014399 := bstep (se 1 (by rfl) ⟨3760799, by rfl⟩ : syracuseStep 5014399 = 7521599) B7521599
theorem B1565823 : Blo 1564980 1565823 := bstep (se 1 (by rfl) ⟨1174367, by rfl⟩ : syracuseStep 1565823 = 2348735) B2348735
theorem B1565851 : Blo 1564980 1565851 := bstep (se 1 (by rfl) ⟨1174388, by rfl⟩ : syracuseStep 1565851 = 2348777) B2348777
theorem B5645467 : Blo 1564980 5645467 := bstep (se 1 (by rfl) ⟨4234100, by rfl⟩ : syracuseStep 5645467 = 8468201) B8468201
theorem B1565855 : Blo 1564980 1565855 := bstep (se 1 (by rfl) ⟨1174391, by rfl⟩ : syracuseStep 1565855 = 2348783) B2348783
theorem B5285087 : Blo 1564980 5285087 := bstep (se 1 (by rfl) ⟨3963815, by rfl⟩ : syracuseStep 5285087 = 7927631) B7927631
theorem B1566191 : Blo 1564980 1566191 := bstep (se 1 (by rfl) ⟨1174643, by rfl⟩ : syracuseStep 1566191 = 2349287) B2349287
theorem B1566311 : Blo 1564980 1566311 := bstep (se 1 (by rfl) ⟨1174733, by rfl⟩ : syracuseStep 1566311 = 2349467) B2349467
theorem B3524255 : Blo 1564980 3524255 := bstep (se 1 (by rfl) ⟨2643191, by rfl⟩ : syracuseStep 3524255 = 5286383) B5286383
theorem B19040017 : Blo 1564980 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B54208349 : Blo 1564980 54208349 := bstep (se 3 (by rfl) ⟨10164065, by rfl⟩ : syracuseStep 54208349 = 20328131) B20328131
theorem B1566575 : Blo 1564980 1566575 := bstep (se 1 (by rfl) ⟨1174931, by rfl⟩ : syracuseStep 1566575 = 2349863) B2349863
theorem B1566591 : Blo 1564980 1566591 := bstep (se 1 (by rfl) ⟨1174943, by rfl⟩ : syracuseStep 1566591 = 2349887) B2349887
theorem B5285789 : Blo 1564980 5285789 := bstep (se 3 (by rfl) ⟨991085, by rfl⟩ : syracuseStep 5285789 = 1982171) B1982171
theorem B9529255 : Blo 1564980 9529255 := bstep (se 1 (by rfl) ⟨7146941, by rfl⟩ : syracuseStep 9529255 = 14293883) B14293883
theorem B3524543 : Blo 1564980 3524543 := bstep (se 1 (by rfl) ⟨2643407, by rfl⟩ : syracuseStep 3524543 = 5286815) B5286815
theorem B1566791 : Blo 1564980 1566791 := bstep (se 1 (by rfl) ⟨1175093, by rfl⟩ : syracuseStep 1566791 = 2350187) B2350187
theorem B1566887 : Blo 1564980 1566887 := bstep (se 1 (by rfl) ⟨1175165, by rfl⟩ : syracuseStep 1566887 = 2350331) B2350331
theorem B7628975 : Blo 1564980 7628975 := bstep (se 1 (by rfl) ⟨5721731, by rfl⟩ : syracuseStep 7628975 = 11443463) B11443463
theorem B5015783 : Blo 1564980 5015783 := bstep (se 1 (by rfl) ⟨3761837, by rfl⟩ : syracuseStep 5015783 = 7523675) B7523675
theorem B1566951 : Blo 1564980 1566951 := bstep (se 1 (by rfl) ⟨1175213, by rfl⟩ : syracuseStep 1566951 = 2350427) B2350427
theorem B1566971 : Blo 1564980 1566971 := bstep (se 1 (by rfl) ⟨1175228, by rfl⟩ : syracuseStep 1566971 = 2350457) B2350457
theorem B1566975 : Blo 1564980 1566975 := bstep (se 1 (by rfl) ⟨1175231, by rfl⟩ : syracuseStep 1566975 = 2350463) B2350463
theorem B7932329 : Blo 1564980 7932329 := bstep (se 2 (by rfl) ⟨2974623, by rfl⟩ : syracuseStep 7932329 = 5949247) B5949247
theorem B5286491 : Blo 1564980 5286491 := bstep (se 1 (by rfl) ⟨3964868, by rfl⟩ : syracuseStep 5286491 = 7929737) B7929737
theorem B6351641 : Blo 1564980 6351641 := bstep (se 2 (by rfl) ⟨2381865, by rfl⟩ : syracuseStep 6351641 = 4763731) B4763731
theorem B11897765 : Blo 1564980 11897765 := bstep (se 4 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 11897765 = 2230831) B2230831
theorem B38620097 : Blo 1564980 38620097 := bstep (se 2 (by rfl) ⟨14482536, by rfl⟩ : syracuseStep 38620097 = 28965073) B28965073
theorem B5017115 : Blo 1564980 5017115 := bstep (se 1 (by rfl) ⟨3762836, by rfl⟩ : syracuseStep 5017115 = 7525673) B7525673
theorem B3346103 : Blo 1564980 3346103 := bstep (se 1 (by rfl) ⟨2509577, by rfl⟩ : syracuseStep 3346103 = 5019155) B5019155
theorem B4460683 : Blo 1564980 4460683 := bstep (se 1 (by rfl) ⟨3345512, by rfl⟩ : syracuseStep 4460683 = 6691025) B6691025
theorem B5288111 : Blo 1564980 5288111 := bstep (se 1 (by rfl) ⟨3966083, by rfl⟩ : syracuseStep 5288111 = 7932167) B7932167
theorem B7926335 : Blo 1564980 7926335 := bstep (se 1 (by rfl) ⟨5944751, by rfl⟩ : syracuseStep 7926335 = 11889503) B11889503
theorem B5943887 : Blo 1564980 5943887 := bstep (se 1 (by rfl) ⟨4457915, by rfl⟩ : syracuseStep 5943887 = 8915831) B8915831
theorem B2347679 : Blo 1564980 2347679 := bstep (se 1 (by rfl) ⟨1760759, by rfl⟩ : syracuseStep 2347679 = 3521519) B3521519
theorem B2642665 : Blo 1564980 2642665 := bstep (se 2 (by rfl) ⟨990999, by rfl⟩ : syracuseStep 2642665 = 1981999) B1981999
theorem B13374395 : Blo 1564980 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B3961811 : Blo 1564980 3961811 := bstep (se 1 (by rfl) ⟨2971358, by rfl⟩ : syracuseStep 3961811 = 5942717) B5942717
theorem B2348009 : Blo 1564980 2348009 := bstep (se 2 (by rfl) ⟨880503, by rfl⟩ : syracuseStep 2348009 = 1761007) B1761007
theorem B2348063 : Blo 1564980 2348063 := bstep (se 1 (by rfl) ⟨1761047, by rfl⟩ : syracuseStep 2348063 = 3522095) B3522095
theorem B11891933 : Blo 1564980 11891933 := bstep (se 3 (by rfl) ⟨2229737, by rfl⟩ : syracuseStep 11891933 = 4459475) B4459475
theorem B2348351 : Blo 1564980 2348351 := bstep (se 1 (by rfl) ⟨1761263, by rfl⟩ : syracuseStep 2348351 = 3522527) B3522527
theorem B13383143 : Blo 1564980 13383143 := bstep (se 1 (by rfl) ⟨10037357, by rfl⟩ : syracuseStep 13383143 = 20074715) B20074715
theorem B26768879 : Blo 1564980 26768879 := bstep (se 1 (by rfl) ⟨20076659, by rfl⟩ : syracuseStep 26768879 = 40153319) B40153319
theorem B2643563 : Blo 1564980 2643563 := bstep (se 1 (by rfl) ⟨1982672, by rfl⟩ : syracuseStep 2643563 = 3965345) B3965345
theorem B2643995 : Blo 1564980 2643995 := bstep (se 1 (by rfl) ⟨1982996, by rfl⟩ : syracuseStep 2643995 = 3965993) B3965993
theorem B2644015 : Blo 1564980 2644015 := bstep (se 1 (by rfl) ⟨1983011, by rfl⟩ : syracuseStep 2644015 = 3966023) B3966023
theorem B20060257 : Blo 1564980 20060257 := bstep (se 2 (by rfl) ⟨7522596, by rfl⟩ : syracuseStep 20060257 = 15045193) B15045193
theorem B10172569 : Blo 1564980 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B2971883 : Blo 1564980 2971883 := bstep (se 1 (by rfl) ⟨2228912, by rfl⟩ : syracuseStep 2971883 = 4457825) B4457825
theorem B5945663 : Blo 1564980 5945663 := bstep (se 1 (by rfl) ⟨4459247, by rfl⟩ : syracuseStep 5945663 = 8918495) B8918495
theorem B3963239 : Blo 1564980 3963239 := bstep (se 1 (by rfl) ⟨2972429, by rfl⟩ : syracuseStep 3963239 = 5944859) B5944859
theorem B57154511 : Blo 1564980 57154511 := bstep (se 1 (by rfl) ⟨42865883, by rfl⟩ : syracuseStep 57154511 = 85731767) B85731767
theorem B3963887 : Blo 1564980 3963887 := bstep (se 1 (by rfl) ⟨2972915, by rfl⟩ : syracuseStep 3963887 = 5945831) B5945831
theorem B8461367 : Blo 1564980 8461367 := bstep (se 1 (by rfl) ⟨6346025, by rfl⟩ : syracuseStep 8461367 = 12692051) B12692051
theorem B7626167 : Blo 1564980 7626167 := bstep (se 1 (by rfl) ⟨5719625, by rfl⟩ : syracuseStep 7626167 = 11439251) B11439251
theorem B3522185 : Blo 1564980 3522185 := bstep (se 2 (by rfl) ⟨1320819, by rfl⟩ : syracuseStep 3522185 = 2641639) B2641639
theorem B3522203 : Blo 1564980 3522203 := bstep (se 1 (by rfl) ⟨2641652, by rfl⟩ : syracuseStep 3522203 = 5283305) B5283305
theorem B6348527 : Blo 1564980 6348527 := bstep (se 1 (by rfl) ⟨4761395, by rfl⟩ : syracuseStep 6348527 = 9522791) B9522791
theorem B38690549 : Blo 1564980 38690549 := bstep (se 5 (by rfl) ⟨1813619, by rfl⟩ : syracuseStep 38690549 = 3627239) B3627239
theorem B3522401 : Blo 1564980 3522401 := bstep (se 2 (by rfl) ⟨1320900, by rfl⟩ : syracuseStep 3522401 = 2641801) B2641801
theorem B10715105 : Blo 1564980 10715105 := bstep (se 2 (by rfl) ⟨4018164, by rfl⟩ : syracuseStep 10715105 = 8036329) B8036329
theorem B26747009 : Blo 1564980 26747009 := bstep (se 2 (by rfl) ⟨10030128, by rfl⟩ : syracuseStep 26747009 = 20060257) B20060257
theorem B5947577 : Blo 1564980 5947577 := bstep (se 2 (by rfl) ⟨2230341, by rfl⟩ : syracuseStep 5947577 = 4460683) B4460683
theorem B3571975 : Blo 1564980 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B10715489 : Blo 1564980 10715489 := bstep (se 2 (by rfl) ⟨4018308, by rfl⟩ : syracuseStep 10715489 = 8036617) B8036617
theorem B5284223 : Blo 1564980 5284223 := bstep (se 1 (by rfl) ⟨3963167, by rfl⟩ : syracuseStep 5284223 = 7926335) B7926335
theorem B1565119 : Blo 1564980 1565119 := bstep (se 1 (by rfl) ⟨1173839, by rfl⟩ : syracuseStep 1565119 = 2347679) B2347679
theorem B1565339 : Blo 1564980 1565339 := bstep (se 1 (by rfl) ⟨1174004, by rfl⟩ : syracuseStep 1565339 = 2348009) B2348009
theorem B13370021 : Blo 1564980 13370021 := bstep (se 4 (by rfl) ⟨1253439, by rfl⟩ : syracuseStep 13370021 = 2506879) B2506879
theorem B1565375 : Blo 1564980 1565375 := bstep (se 1 (by rfl) ⟨1174031, by rfl⟩ : syracuseStep 1565375 = 2348063) B2348063
theorem B3523391 : Blo 1564980 3523391 := bstep (se 1 (by rfl) ⟨2642543, by rfl⟩ : syracuseStep 3523391 = 5285087) B5285087
theorem B1565567 : Blo 1564980 1565567 := bstep (se 1 (by rfl) ⟨1174175, by rfl⟩ : syracuseStep 1565567 = 2348351) B2348351
theorem B3523553 : Blo 1564980 3523553 := bstep (se 2 (by rfl) ⟨1321332, by rfl⟩ : syracuseStep 3523553 = 2642665) B2642665
theorem B8922095 : Blo 1564980 8922095 := bstep (se 1 (by rfl) ⟨6691571, by rfl⟩ : syracuseStep 8922095 = 13383143) B13383143
theorem B1762375 : Blo 1564980 1762375 := bstep (se 1 (by rfl) ⟨1321781, by rfl⟩ : syracuseStep 1762375 = 2643563) B2643563
theorem B6685865 : Blo 1564980 6685865 := bstep (se 2 (by rfl) ⟨2507199, by rfl⟩ : syracuseStep 6685865 = 5014399) B5014399
theorem B3523859 : Blo 1564980 3523859 := bstep (se 1 (by rfl) ⟨2642894, by rfl⟩ : syracuseStep 3523859 = 5285789) B5285789
theorem B1762663 : Blo 1564980 1762663 := bstep (se 1 (by rfl) ⟨1321997, by rfl⟩ : syracuseStep 1762663 = 2643995) B2643995
theorem B3343855 : Blo 1564980 3343855 := bstep (se 1 (by rfl) ⟨2507891, by rfl⟩ : syracuseStep 3343855 = 5015783) B5015783
theorem B3524327 : Blo 1564980 3524327 := bstep (se 1 (by rfl) ⟨2643245, by rfl⟩ : syracuseStep 3524327 = 5286491) B5286491
theorem B7931843 : Blo 1564980 7931843 := bstep (se 1 (by rfl) ⟨5948882, by rfl⟩ : syracuseStep 7931843 = 11897765) B11897765
theorem B38103007 : Blo 1564980 38103007 := bstep (se 1 (by rfl) ⟨28577255, by rfl⟩ : syracuseStep 38103007 = 57154511) B57154511
theorem B3344743 : Blo 1564980 3344743 := bstep (se 1 (by rfl) ⟨2508557, by rfl⟩ : syracuseStep 3344743 = 5017115) B5017115
theorem B2230735 : Blo 1564980 2230735 := bstep (se 1 (by rfl) ⟨1673051, by rfl⟩ : syracuseStep 2230735 = 3346103) B3346103
theorem B3525353 : Blo 1564980 3525353 := bstep (se 2 (by rfl) ⟨1322007, by rfl⟩ : syracuseStep 3525353 = 2644015) B2644015
theorem B3525407 : Blo 1564980 3525407 := bstep (se 1 (by rfl) ⟨2644055, by rfl⟩ : syracuseStep 3525407 = 5288111) B5288111
theorem B5286761 : Blo 1564980 5286761 := bstep (se 2 (by rfl) ⟨1982535, by rfl⟩ : syracuseStep 5286761 = 3965071) B3965071
theorem B8924327 : Blo 1564980 8924327 := bstep (se 1 (by rfl) ⟨6693245, by rfl⟩ : syracuseStep 8924327 = 13386491) B13386491
theorem B8916263 : Blo 1564980 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B2641207 : Blo 1564980 2641207 := bstep (se 1 (by rfl) ⟨1980905, by rfl⟩ : syracuseStep 2641207 = 3961811) B3961811
theorem B17845919 : Blo 1564980 17845919 := bstep (se 1 (by rfl) ⟨13384439, by rfl⟩ : syracuseStep 17845919 = 26768879) B26768879
theorem B36138899 : Blo 1564980 36138899 := bstep (se 1 (by rfl) ⟨27104174, by rfl⟩ : syracuseStep 36138899 = 54208349) B54208349
theorem B2642159 : Blo 1564980 2642159 := bstep (se 1 (by rfl) ⟨1981619, by rfl⟩ : syracuseStep 2642159 = 3963239) B3963239
theorem B5288219 : Blo 1564980 5288219 := bstep (se 1 (by rfl) ⟨3966164, by rfl⟩ : syracuseStep 5288219 = 7932329) B7932329
theorem B5288381 : Blo 1564980 5288381 := bstep (se 3 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 5288381 = 1983143) B1983143
theorem B2642591 : Blo 1564980 2642591 := bstep (se 1 (by rfl) ⟨1981943, by rfl⟩ : syracuseStep 2642591 = 3963887) B3963887
theorem B5640911 : Blo 1564980 5640911 := bstep (se 1 (by rfl) ⟨4230683, by rfl⟩ : syracuseStep 5640911 = 8461367) B8461367
theorem B5084111 : Blo 1564980 5084111 := bstep (se 1 (by rfl) ⟨3813083, by rfl⟩ : syracuseStep 5084111 = 7626167) B7626167
theorem B2348123 : Blo 1564980 2348123 := bstep (se 1 (by rfl) ⟨1761092, by rfl⟩ : syracuseStep 2348123 = 3522185) B3522185
theorem B2348135 : Blo 1564980 2348135 := bstep (se 1 (by rfl) ⟨1761101, by rfl⟩ : syracuseStep 2348135 = 3522203) B3522203
theorem B4232351 : Blo 1564980 4232351 := bstep (se 1 (by rfl) ⟨3174263, by rfl⟩ : syracuseStep 4232351 = 6348527) B6348527
theorem B25793699 : Blo 1564980 25793699 := bstep (se 1 (by rfl) ⟨19345274, by rfl⟩ : syracuseStep 25793699 = 38690549) B38690549
theorem B2348267 : Blo 1564980 2348267 := bstep (se 1 (by rfl) ⟨1761200, by rfl⟩ : syracuseStep 2348267 = 3522401) B3522401
theorem B6346153 : Blo 1564980 6346153 := bstep (se 2 (by rfl) ⟨2379807, by rfl⟩ : syracuseStep 6346153 = 4759615) B4759615
theorem B2643455 : Blo 1564980 2643455 := bstep (se 1 (by rfl) ⟨1982591, by rfl⟩ : syracuseStep 2643455 = 3965183) B3965183
theorem B13563425 : Blo 1564980 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B3962591 : Blo 1564980 3962591 := bstep (se 1 (by rfl) ⟨2971943, by rfl⟩ : syracuseStep 3962591 = 5943887) B5943887
theorem B2348921 : Blo 1564980 2348921 := bstep (se 2 (by rfl) ⟨880845, by rfl⟩ : syracuseStep 2348921 = 1761691) B1761691
theorem B7927955 : Blo 1564980 7927955 := bstep (se 1 (by rfl) ⟨5945966, by rfl⟩ : syracuseStep 7927955 = 11891933) B11891933
theorem B2349503 : Blo 1564980 2349503 := bstep (se 1 (by rfl) ⟨1762127, by rfl⟩ : syracuseStep 2349503 = 3524255) B3524255
theorem B2349695 : Blo 1564980 2349695 := bstep (se 1 (by rfl) ⟨1762271, by rfl⟩ : syracuseStep 2349695 = 3524543) B3524543
theorem B5085983 : Blo 1564980 5085983 := bstep (se 1 (by rfl) ⟨3814487, by rfl⟩ : syracuseStep 5085983 = 7628975) B7628975
theorem B1981255 : Blo 1564980 1981255 := bstep (se 1 (by rfl) ⟨1485941, by rfl⟩ : syracuseStep 1981255 = 2971883) B2971883
theorem B7527289 : Blo 1564980 7527289 := bstep (se 2 (by rfl) ⟨2822733, by rfl⟩ : syracuseStep 7527289 = 5645467) B5645467
theorem B3963775 : Blo 1564980 3963775 := bstep (se 1 (by rfl) ⟨2972831, by rfl⟩ : syracuseStep 3963775 = 5945663) B5945663
theorem B4234427 : Blo 1564980 4234427 := bstep (se 1 (by rfl) ⟨3175820, by rfl⟩ : syracuseStep 4234427 = 6351641) B6351641
theorem B25746731 : Blo 1564980 25746731 := bstep (se 1 (by rfl) ⟨19310048, by rfl⟩ : syracuseStep 25746731 = 38620097) B38620097
theorem B25386689 : Blo 1564980 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B12705673 : Blo 1564980 12705673 := bstep (se 2 (by rfl) ⟨4764627, by rfl⟩ : syracuseStep 12705673 = 9529255) B9529255
theorem B7143403 : Blo 1564980 7143403 := bstep (se 1 (by rfl) ⟨5357552, by rfl⟩ : syracuseStep 7143403 = 10715105) B10715105
theorem B3965051 : Blo 1564980 3965051 := bstep (se 1 (by rfl) ⟨2973788, by rfl⟩ : syracuseStep 3965051 = 5947577) B5947577
theorem B1761439 : Blo 1564980 1761439 := bstep (se 1 (by rfl) ⟨1321079, by rfl⟩ : syracuseStep 1761439 = 2642159) B2642159
theorem B7143659 : Blo 1564980 7143659 := bstep (se 1 (by rfl) ⟨5357744, by rfl⟩ : syracuseStep 7143659 = 10715489) B10715489
theorem B3522815 : Blo 1564980 3522815 := bstep (se 1 (by rfl) ⟨2642111, by rfl⟩ : syracuseStep 3522815 = 5284223) B5284223
theorem B1761727 : Blo 1564980 1761727 := bstep (se 1 (by rfl) ⟨1321295, by rfl⟩ : syracuseStep 1761727 = 2642591) B2642591
theorem B8913347 : Blo 1564980 8913347 := bstep (se 1 (by rfl) ⟨6685010, by rfl⟩ : syracuseStep 8913347 = 13370021) B13370021
theorem B3760607 : Blo 1564980 3760607 := bstep (se 1 (by rfl) ⟨2820455, by rfl⟩ : syracuseStep 3760607 = 5640911) B5640911
theorem B2974313 : Blo 1564980 2974313 := bstep (se 2 (by rfl) ⟨1115367, by rfl⟩ : syracuseStep 2974313 = 2230735) B2230735
theorem B5948063 : Blo 1564980 5948063 := bstep (se 1 (by rfl) ⟨4461047, by rfl⟩ : syracuseStep 5948063 = 8922095) B8922095
theorem B1565415 : Blo 1564980 1565415 := bstep (se 1 (by rfl) ⟨1174061, by rfl⟩ : syracuseStep 1565415 = 2348123) B2348123
theorem B1565423 : Blo 1564980 1565423 := bstep (se 1 (by rfl) ⟨1174067, by rfl⟩ : syracuseStep 1565423 = 2348135) B2348135
theorem B4457243 : Blo 1564980 4457243 := bstep (se 1 (by rfl) ⟨3342932, by rfl⟩ : syracuseStep 4457243 = 6685865) B6685865
theorem B1565511 : Blo 1564980 1565511 := bstep (se 1 (by rfl) ⟨1174133, by rfl⟩ : syracuseStep 1565511 = 2348267) B2348267
theorem B1762303 : Blo 1564980 1762303 := bstep (se 1 (by rfl) ⟨1321727, by rfl⟩ : syracuseStep 1762303 = 2643455) B2643455
theorem B10036385 : Blo 1564980 10036385 := bstep (se 2 (by rfl) ⟨3763644, by rfl⟩ : syracuseStep 10036385 = 7527289) B7527289
theorem B5285033 : Blo 1564980 5285033 := bstep (se 2 (by rfl) ⟨1981887, by rfl⟩ : syracuseStep 5285033 = 3963775) B3963775
theorem B1565947 : Blo 1564980 1565947 := bstep (se 1 (by rfl) ⟨1174460, by rfl⟩ : syracuseStep 1565947 = 2348921) B2348921
theorem B5285303 : Blo 1564980 5285303 := bstep (se 1 (by rfl) ⟨3963977, by rfl⟩ : syracuseStep 5285303 = 7927955) B7927955
theorem B1566335 : Blo 1564980 1566335 := bstep (se 1 (by rfl) ⟨1174751, by rfl⟩ : syracuseStep 1566335 = 2349503) B2349503
theorem B1566463 : Blo 1564980 1566463 := bstep (se 1 (by rfl) ⟨1174847, by rfl⟩ : syracuseStep 1566463 = 2349695) B2349695
theorem B3524507 : Blo 1564980 3524507 := bstep (se 1 (by rfl) ⟨2643380, by rfl⟩ : syracuseStep 3524507 = 5286761) B5286761
theorem B4458473 : Blo 1564980 4458473 := bstep (se 2 (by rfl) ⟨1671927, by rfl⟩ : syracuseStep 4458473 = 3343855) B3343855
theorem B5949551 : Blo 1564980 5949551 := bstep (se 1 (by rfl) ⟨4462163, by rfl⟩ : syracuseStep 5949551 = 8924327) B8924327
theorem B17164487 : Blo 1564980 17164487 := bstep (se 1 (by rfl) ⟨12873365, by rfl⟩ : syracuseStep 17164487 = 25746731) B25746731
theorem B11897279 : Blo 1564980 11897279 := bstep (se 1 (by rfl) ⟨8922959, by rfl⟩ : syracuseStep 11897279 = 17845919) B17845919
theorem B3525479 : Blo 1564980 3525479 := bstep (se 1 (by rfl) ⟨2644109, by rfl⟩ : syracuseStep 3525479 = 5288219) B5288219
theorem B3525587 : Blo 1564980 3525587 := bstep (se 1 (by rfl) ⟨2644190, by rfl⟩ : syracuseStep 3525587 = 5288381) B5288381
theorem B4762633 : Blo 1564980 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B68783197 : Blo 1564980 68783197 := bstep (se 3 (by rfl) ⟨12896849, by rfl⟩ : syracuseStep 68783197 = 25793699) B25793699
theorem B2821567 : Blo 1564980 2821567 := bstep (se 1 (by rfl) ⟨2116175, by rfl⟩ : syracuseStep 2821567 = 4232351) B4232351
theorem B2641673 : Blo 1564980 2641673 := bstep (se 2 (by rfl) ⟨990627, by rfl⟩ : syracuseStep 2641673 = 1981255) B1981255
theorem B2641727 : Blo 1564980 2641727 := bstep (se 1 (by rfl) ⟨1981295, by rfl⟩ : syracuseStep 2641727 = 3962591) B3962591
theorem B5287895 : Blo 1564980 5287895 := bstep (se 1 (by rfl) ⟨3965921, by rfl⟩ : syracuseStep 5287895 = 7931843) B7931843
theorem B17838629 : Blo 1564980 17838629 := bstep (se 4 (by rfl) ⟨1672371, by rfl⟩ : syracuseStep 17838629 = 3344743) B3344743
theorem B2822951 : Blo 1564980 2822951 := bstep (se 1 (by rfl) ⟨2117213, by rfl⟩ : syracuseStep 2822951 = 4234427) B4234427
theorem B5944175 : Blo 1564980 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B33846149 : Blo 1564980 33846149 := bstep (se 4 (by rfl) ⟨3173076, by rfl⟩ : syracuseStep 33846149 = 6346153) B6346153
theorem B50804009 : Blo 1564980 50804009 := bstep (se 2 (by rfl) ⟨19051503, by rfl⟩ : syracuseStep 50804009 = 38103007) B38103007
theorem B9524537 : Blo 1564980 9524537 := bstep (se 2 (by rfl) ⟨3571701, by rfl⟩ : syracuseStep 9524537 = 7143403) B7143403
theorem B17831339 : Blo 1564980 17831339 := bstep (se 1 (by rfl) ⟨13373504, by rfl⟩ : syracuseStep 17831339 = 26747009) B26747009
theorem B2348927 : Blo 1564980 2348927 := bstep (se 1 (by rfl) ⟨1761695, by rfl⟩ : syracuseStep 2348927 = 3523391) B3523391
theorem B3389407 : Blo 1564980 3389407 := bstep (se 1 (by rfl) ⟨2542055, by rfl⟩ : syracuseStep 3389407 = 5084111) B5084111
theorem B2349035 : Blo 1564980 2349035 := bstep (se 1 (by rfl) ⟨1761776, by rfl⟩ : syracuseStep 2349035 = 3523553) B3523553
theorem B2349239 : Blo 1564980 2349239 := bstep (se 1 (by rfl) ⟨1761929, by rfl⟩ : syracuseStep 2349239 = 3523859) B3523859
theorem B9042283 : Blo 1564980 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B2349551 : Blo 1564980 2349551 := bstep (se 1 (by rfl) ⟨1762163, by rfl⟩ : syracuseStep 2349551 = 3524327) B3524327
theorem B2349833 : Blo 1564980 2349833 := bstep (se 2 (by rfl) ⟨881187, by rfl⟩ : syracuseStep 2349833 = 1762375) B1762375
theorem B3521609 : Blo 1564980 3521609 := bstep (se 2 (by rfl) ⟨1320603, by rfl⟩ : syracuseStep 3521609 = 2641207) B2641207
theorem B2350217 : Blo 1564980 2350217 := bstep (se 2 (by rfl) ⟨881331, by rfl⟩ : syracuseStep 2350217 = 1762663) B1762663
theorem B2350235 : Blo 1564980 2350235 := bstep (se 1 (by rfl) ⟨1762676, by rfl⟩ : syracuseStep 2350235 = 3525353) B3525353
theorem B3390655 : Blo 1564980 3390655 := bstep (se 1 (by rfl) ⟨2542991, by rfl⟩ : syracuseStep 3390655 = 5085983) B5085983
theorem B2350271 : Blo 1564980 2350271 := bstep (se 1 (by rfl) ⟨1762703, by rfl⟩ : syracuseStep 2350271 = 3525407) B3525407
theorem B96370397 : Blo 1564980 96370397 := bstep (se 3 (by rfl) ⟨18069449, by rfl⟩ : syracuseStep 96370397 = 36138899) B36138899
theorem B16924459 : Blo 1564980 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B16940897 : Blo 1564980 16940897 := bstep (se 2 (by rfl) ⟨6352836, by rfl⟩ : syracuseStep 16940897 = 12705673) B12705673
theorem B1982875 : Blo 1564980 1982875 := bstep (se 1 (by rfl) ⟨1487156, by rfl⟩ : syracuseStep 1982875 = 2974313) B2974313
theorem B3965375 : Blo 1564980 3965375 := bstep (se 1 (by rfl) ⟨2974031, by rfl⟩ : syracuseStep 3965375 = 5948063) B5948063
theorem B3523355 : Blo 1564980 3523355 := bstep (se 1 (by rfl) ⟨2642516, by rfl⟩ : syracuseStep 3523355 = 5285033) B5285033
theorem B6349691 : Blo 1564980 6349691 := bstep (se 1 (by rfl) ⟨4762268, by rfl⟩ : syracuseStep 6349691 = 9524537) B9524537
theorem B11887559 : Blo 1564980 11887559 := bstep (se 1 (by rfl) ⟨8915669, by rfl⟩ : syracuseStep 11887559 = 17831339) B17831339
theorem B3523535 : Blo 1564980 3523535 := bstep (se 1 (by rfl) ⟨2642651, by rfl⟩ : syracuseStep 3523535 = 5285303) B5285303
theorem B10028285 : Blo 1564980 10028285 := bstep (se 3 (by rfl) ⟨1880303, by rfl⟩ : syracuseStep 10028285 = 3760607) B3760607
theorem B1565951 : Blo 1564980 1565951 := bstep (se 1 (by rfl) ⟨1174463, by rfl⟩ : syracuseStep 1565951 = 2348927) B2348927
theorem B1566023 : Blo 1564980 1566023 := bstep (se 1 (by rfl) ⟨1174517, by rfl⟩ : syracuseStep 1566023 = 2349035) B2349035
theorem B6350177 : Blo 1564980 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B3966367 : Blo 1564980 3966367 := bstep (se 1 (by rfl) ⟨2974775, by rfl⟩ : syracuseStep 3966367 = 5949551) B5949551
theorem B1566159 : Blo 1564980 1566159 := bstep (se 1 (by rfl) ⟨1174619, by rfl⟩ : syracuseStep 1566159 = 2349239) B2349239
theorem B91710929 : Blo 1564980 91710929 := bstep (se 2 (by rfl) ⟨34391598, by rfl⟩ : syracuseStep 91710929 = 68783197) B68783197
theorem B7931519 : Blo 1564980 7931519 := bstep (se 1 (by rfl) ⟨5948639, by rfl⟩ : syracuseStep 7931519 = 11897279) B11897279
theorem B1566367 : Blo 1564980 1566367 := bstep (se 1 (by rfl) ⟨1174775, by rfl⟩ : syracuseStep 1566367 = 2349551) B2349551
theorem B1566555 : Blo 1564980 1566555 := bstep (se 1 (by rfl) ⟨1174916, by rfl⟩ : syracuseStep 1566555 = 2349833) B2349833
theorem B3762089 : Blo 1564980 3762089 := bstep (se 2 (by rfl) ⟨1410783, by rfl⟩ : syracuseStep 3762089 = 2821567) B2821567
theorem B1566811 : Blo 1564980 1566811 := bstep (se 1 (by rfl) ⟨1175108, by rfl⟩ : syracuseStep 1566811 = 2350217) B2350217
theorem B1566823 : Blo 1564980 1566823 := bstep (se 1 (by rfl) ⟨1175117, by rfl⟩ : syracuseStep 1566823 = 2350235) B2350235
theorem B1566847 : Blo 1564980 1566847 := bstep (se 1 (by rfl) ⟨1175135, by rfl⟩ : syracuseStep 1566847 = 2350271) B2350271
theorem B3525263 : Blo 1564980 3525263 := bstep (se 1 (by rfl) ⟨2643947, by rfl⟩ : syracuseStep 3525263 = 5287895) B5287895
theorem B4762439 : Blo 1564980 4762439 := bstep (se 1 (by rfl) ⟨3571829, by rfl⟩ : syracuseStep 4762439 = 7143659) B7143659
theorem B5942231 : Blo 1564980 5942231 := bstep (se 1 (by rfl) ⟨4456673, by rfl⟩ : syracuseStep 5942231 = 8913347) B8913347
theorem B45771965 : Blo 1564980 45771965 := bstep (se 3 (by rfl) ⟨8582243, by rfl⟩ : syracuseStep 45771965 = 17164487) B17164487
theorem B22564099 : Blo 1564980 22564099 := bstep (se 1 (by rfl) ⟨16923074, by rfl⟩ : syracuseStep 22564099 = 33846149) B33846149
theorem B33869339 : Blo 1564980 33869339 := bstep (se 1 (by rfl) ⟨25402004, by rfl⟩ : syracuseStep 33869339 = 50804009) B50804009
theorem B2347739 : Blo 1564980 2347739 := bstep (se 1 (by rfl) ⟨1760804, by rfl⟩ : syracuseStep 2347739 = 3521609) B3521609
theorem B22565945 : Blo 1564980 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B64246931 : Blo 1564980 64246931 := bstep (se 1 (by rfl) ⟨48185198, by rfl⟩ : syracuseStep 64246931 = 96370397) B96370397
theorem B18076837 : Blo 1564980 18076837 := bstep (se 4 (by rfl) ⟨1694703, by rfl⟩ : syracuseStep 18076837 = 3389407) B3389407
theorem B11293931 : Blo 1564980 11293931 := bstep (se 1 (by rfl) ⟨8470448, by rfl⟩ : syracuseStep 11293931 = 16940897) B16940897
theorem B2643367 : Blo 1564980 2643367 := bstep (se 1 (by rfl) ⟨1982525, by rfl⟩ : syracuseStep 2643367 = 3965051) B3965051
theorem B2348543 : Blo 1564980 2348543 := bstep (se 1 (by rfl) ⟨1761407, by rfl⟩ : syracuseStep 2348543 = 3522815) B3522815
theorem B2348585 : Blo 1564980 2348585 := bstep (se 2 (by rfl) ⟨880719, by rfl⟩ : syracuseStep 2348585 = 1761439) B1761439
theorem B11892419 : Blo 1564980 11892419 := bstep (se 1 (by rfl) ⟨8919314, by rfl⟩ : syracuseStep 11892419 = 17838629) B17838629
theorem B12056377 : Blo 1564980 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B2971495 : Blo 1564980 2971495 := bstep (se 1 (by rfl) ⟨2228621, by rfl⟩ : syracuseStep 2971495 = 4457243) B4457243
theorem B1881967 : Blo 1564980 1881967 := bstep (se 1 (by rfl) ⟨1411475, by rfl⟩ : syracuseStep 1881967 = 2822951) B2822951
theorem B3962783 : Blo 1564980 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B2348969 : Blo 1564980 2348969 := bstep (se 2 (by rfl) ⟨880863, by rfl⟩ : syracuseStep 2348969 = 1761727) B1761727
theorem B6690923 : Blo 1564980 6690923 := bstep (se 1 (by rfl) ⟨5018192, by rfl⟩ : syracuseStep 6690923 = 10036385) B10036385
theorem B2349671 : Blo 1564980 2349671 := bstep (se 1 (by rfl) ⟨1762253, by rfl⟩ : syracuseStep 2349671 = 3524507) B3524507
theorem B2972315 : Blo 1564980 2972315 := bstep (se 1 (by rfl) ⟨2229236, by rfl⟩ : syracuseStep 2972315 = 4458473) B4458473
theorem B2349737 : Blo 1564980 2349737 := bstep (se 2 (by rfl) ⟨881151, by rfl⟩ : syracuseStep 2349737 = 1762303) B1762303
theorem B4520873 : Blo 1564980 4520873 := bstep (se 2 (by rfl) ⟨1695327, by rfl⟩ : syracuseStep 4520873 = 3390655) B3390655
theorem B2350319 : Blo 1564980 2350319 := bstep (se 1 (by rfl) ⟨1762739, by rfl⟩ : syracuseStep 2350319 = 3525479) B3525479
theorem B2350391 : Blo 1564980 2350391 := bstep (se 1 (by rfl) ⟨1762793, by rfl⟩ : syracuseStep 2350391 = 3525587) B3525587
theorem B1761115 : Blo 1564980 1761115 := bstep (se 1 (by rfl) ⟨1320836, by rfl⟩ : syracuseStep 1761115 = 2641673) B2641673
theorem B1761151 : Blo 1564980 1761151 := bstep (se 1 (by rfl) ⟨1320863, by rfl⟩ : syracuseStep 1761151 = 2641727) B2641727
theorem B1565159 : Blo 1564980 1565159 := bstep (se 1 (by rfl) ⟨1173869, by rfl⟩ : syracuseStep 1565159 = 2347739) B2347739
theorem B7529287 : Blo 1564980 7529287 := bstep (se 1 (by rfl) ⟨5646965, by rfl⟩ : syracuseStep 7529287 = 11293931) B11293931
theorem B6685523 : Blo 1564980 6685523 := bstep (se 1 (by rfl) ⟨5014142, by rfl⟩ : syracuseStep 6685523 = 10028285) B10028285
theorem B16933805 : Blo 1564980 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B1565695 : Blo 1564980 1565695 := bstep (se 1 (by rfl) ⟨1174271, by rfl⟩ : syracuseStep 1565695 = 2348543) B2348543
theorem B1565723 : Blo 1564980 1565723 := bstep (se 1 (by rfl) ⟨1174292, by rfl⟩ : syracuseStep 1565723 = 2348585) B2348585
theorem B2508059 : Blo 1564980 2508059 := bstep (se 1 (by rfl) ⟨1881044, by rfl⟩ : syracuseStep 2508059 = 3762089) B3762089
theorem B1565979 : Blo 1564980 1565979 := bstep (se 1 (by rfl) ⟨1174484, by rfl⟩ : syracuseStep 1565979 = 2348969) B2348969
theorem B24102449 : Blo 1564980 24102449 := bstep (se 2 (by rfl) ⟨9038418, by rfl⟩ : syracuseStep 24102449 = 18076837) B18076837
theorem B1566447 : Blo 1564980 1566447 := bstep (se 1 (by rfl) ⟨1174835, by rfl⟩ : syracuseStep 1566447 = 2349671) B2349671
theorem B1566491 : Blo 1564980 1566491 := bstep (se 1 (by rfl) ⟨1174868, by rfl⟩ : syracuseStep 1566491 = 2349737) B2349737
theorem B3524489 : Blo 1564980 3524489 := bstep (se 2 (by rfl) ⟨1321683, by rfl⟩ : syracuseStep 3524489 = 2643367) B2643367
theorem B1566879 : Blo 1564980 1566879 := bstep (se 1 (by rfl) ⟨1175159, by rfl⟩ : syracuseStep 1566879 = 2350319) B2350319
theorem B1566927 : Blo 1564980 1566927 := bstep (se 1 (by rfl) ⟨1175195, by rfl⟩ : syracuseStep 1566927 = 2350391) B2350391
theorem B22579559 : Blo 1564980 22579559 := bstep (se 1 (by rfl) ⟨16934669, by rfl⟩ : syracuseStep 22579559 = 33869339) B33869339
theorem B16075169 : Blo 1564980 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B2509289 : Blo 1564980 2509289 := bstep (se 2 (by rfl) ⟨940983, by rfl⟩ : syracuseStep 2509289 = 1881967) B1881967
theorem B7925039 : Blo 1564980 7925039 := bstep (se 1 (by rfl) ⟨5943779, by rfl⟩ : syracuseStep 7925039 = 11887559) B11887559
theorem B15043963 : Blo 1564980 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B42831287 : Blo 1564980 42831287 := bstep (se 1 (by rfl) ⟨32123465, by rfl⟩ : syracuseStep 42831287 = 64246931) B64246931
theorem B61140619 : Blo 1564980 61140619 := bstep (se 1 (by rfl) ⟨45855464, by rfl⟩ : syracuseStep 61140619 = 91710929) B91710929
theorem B5287679 : Blo 1564980 5287679 := bstep (se 1 (by rfl) ⟨3965759, by rfl⟩ : syracuseStep 5287679 = 7931519) B7931519
theorem B2641855 : Blo 1564980 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B4460615 : Blo 1564980 4460615 := bstep (se 1 (by rfl) ⟨3345461, by rfl⟩ : syracuseStep 4460615 = 6690923) B6690923
theorem B30085465 : Blo 1564980 30085465 := bstep (se 2 (by rfl) ⟨11282049, by rfl⟩ : syracuseStep 30085465 = 22564099) B22564099
theorem B7926173 : Blo 1564980 7926173 := bstep (se 3 (by rfl) ⟨1486157, by rfl⟩ : syracuseStep 7926173 = 2972315) B2972315
theorem B5288489 : Blo 1564980 5288489 := bstep (se 2 (by rfl) ⟨1983183, by rfl⟩ : syracuseStep 5288489 = 3966367) B3966367
theorem B3174959 : Blo 1564980 3174959 := bstep (se 1 (by rfl) ⟨2381219, by rfl⟩ : syracuseStep 3174959 = 4762439) B4762439
theorem B3961487 : Blo 1564980 3961487 := bstep (se 1 (by rfl) ⟨2971115, by rfl⟩ : syracuseStep 3961487 = 5942231) B5942231
theorem B12055661 : Blo 1564980 12055661 := bstep (se 3 (by rfl) ⟨2260436, by rfl⟩ : syracuseStep 12055661 = 4520873) B4520873
theorem B2348153 : Blo 1564980 2348153 := bstep (se 2 (by rfl) ⟨880557, by rfl⟩ : syracuseStep 2348153 = 1761115) B1761115
theorem B3961993 : Blo 1564980 3961993 := bstep (se 2 (by rfl) ⟨1485747, by rfl⟩ : syracuseStep 3961993 = 2971495) B2971495
theorem B2348201 : Blo 1564980 2348201 := bstep (se 2 (by rfl) ⟨880575, by rfl⟩ : syracuseStep 2348201 = 1761151) B1761151
theorem B2643583 : Blo 1564980 2643583 := bstep (se 1 (by rfl) ⟨1982687, by rfl⟩ : syracuseStep 2643583 = 3965375) B3965375
theorem B2348903 : Blo 1564980 2348903 := bstep (se 1 (by rfl) ⟨1761677, by rfl⟩ : syracuseStep 2348903 = 3523355) B3523355
theorem B2643833 : Blo 1564980 2643833 := bstep (se 2 (by rfl) ⟨991437, by rfl⟩ : syracuseStep 2643833 = 1982875) B1982875
theorem B4233127 : Blo 1564980 4233127 := bstep (se 1 (by rfl) ⟨3174845, by rfl⟩ : syracuseStep 4233127 = 6349691) B6349691
theorem B2349023 : Blo 1564980 2349023 := bstep (se 1 (by rfl) ⟨1761767, by rfl⟩ : syracuseStep 2349023 = 3523535) B3523535
theorem B7928279 : Blo 1564980 7928279 := bstep (se 1 (by rfl) ⟨5946209, by rfl⟩ : syracuseStep 7928279 = 11892419) B11892419
theorem B2350175 : Blo 1564980 2350175 := bstep (se 1 (by rfl) ⟨1762631, by rfl⟩ : syracuseStep 2350175 = 3525263) B3525263
theorem B30514643 : Blo 1564980 30514643 := bstep (se 1 (by rfl) ⟨22885982, by rfl⟩ : syracuseStep 30514643 = 45771965) B45771965
theorem B2973743 : Blo 1564980 2973743 := bstep (se 1 (by rfl) ⟨2230307, by rfl⟩ : syracuseStep 2973743 = 4460615) B4460615
theorem B5284115 : Blo 1564980 5284115 := bstep (se 1 (by rfl) ⟨3963086, by rfl⟩ : syracuseStep 5284115 = 7926173) B7926173
theorem B4457015 : Blo 1564980 4457015 := bstep (se 1 (by rfl) ⟨3342761, by rfl⟩ : syracuseStep 4457015 = 6685523) B6685523
theorem B11289203 : Blo 1564980 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B8037107 : Blo 1564980 8037107 := bstep (se 1 (by rfl) ⟨6027830, by rfl⟩ : syracuseStep 8037107 = 12055661) B12055661
theorem B1565435 : Blo 1564980 1565435 := bstep (se 1 (by rfl) ⟨1174076, by rfl⟩ : syracuseStep 1565435 = 2348153) B2348153
theorem B1565467 : Blo 1564980 1565467 := bstep (se 1 (by rfl) ⟨1174100, by rfl⟩ : syracuseStep 1565467 = 2348201) B2348201
theorem B1672039 : Blo 1564980 1672039 := bstep (se 1 (by rfl) ⟨1254029, by rfl⟩ : syracuseStep 1672039 = 2508059) B2508059
theorem B1565935 : Blo 1564980 1565935 := bstep (se 1 (by rfl) ⟨1174451, by rfl⟩ : syracuseStep 1565935 = 2348903) B2348903
theorem B1762555 : Blo 1564980 1762555 := bstep (se 1 (by rfl) ⟨1321916, by rfl⟩ : syracuseStep 1762555 = 2643833) B2643833
theorem B1566015 : Blo 1564980 1566015 := bstep (se 1 (by rfl) ⟨1174511, by rfl⟩ : syracuseStep 1566015 = 2349023) B2349023
theorem B10716779 : Blo 1564980 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B5285519 : Blo 1564980 5285519 := bstep (se 1 (by rfl) ⟨3964139, by rfl⟩ : syracuseStep 5285519 = 7928279) B7928279
theorem B1672859 : Blo 1564980 1672859 := bstep (se 1 (by rfl) ⟨1254644, by rfl⟩ : syracuseStep 1672859 = 2509289) B2509289
theorem B1566783 : Blo 1564980 1566783 := bstep (se 1 (by rfl) ⟨1175087, by rfl⟩ : syracuseStep 1566783 = 2350175) B2350175
theorem B3524777 : Blo 1564980 3524777 := bstep (se 2 (by rfl) ⟨1321791, by rfl⟩ : syracuseStep 3524777 = 2643583) B2643583
theorem B81520825 : Blo 1564980 81520825 := bstep (se 2 (by rfl) ⟨30570309, by rfl⟩ : syracuseStep 81520825 = 61140619) B61140619
theorem B20343095 : Blo 1564980 20343095 := bstep (se 1 (by rfl) ⟨15257321, by rfl⟩ : syracuseStep 20343095 = 30514643) B30514643
theorem B3525119 : Blo 1564980 3525119 := bstep (se 1 (by rfl) ⟨2643839, by rfl⟩ : syracuseStep 3525119 = 5287679) B5287679
theorem B3525659 : Blo 1564980 3525659 := bstep (se 1 (by rfl) ⟨2644244, by rfl⟩ : syracuseStep 3525659 = 5288489) B5288489
theorem B2116639 : Blo 1564980 2116639 := bstep (se 1 (by rfl) ⟨1587479, by rfl⟩ : syracuseStep 2116639 = 3174959) B3174959
theorem B2640991 : Blo 1564980 2640991 := bstep (se 1 (by rfl) ⟨1980743, by rfl⟩ : syracuseStep 2640991 = 3961487) B3961487
theorem B16068299 : Blo 1564980 16068299 := bstep (se 1 (by rfl) ⟨12051224, by rfl⟩ : syracuseStep 16068299 = 24102449) B24102449
theorem B10039049 : Blo 1564980 10039049 := bstep (se 2 (by rfl) ⟨3764643, by rfl⟩ : syracuseStep 10039049 = 7529287) B7529287
theorem B15053039 : Blo 1564980 15053039 := bstep (se 1 (by rfl) ⟨11289779, by rfl⟩ : syracuseStep 15053039 = 22579559) B22579559
theorem B20058617 : Blo 1564980 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B28554191 : Blo 1564980 28554191 := bstep (se 1 (by rfl) ⟨21415643, by rfl⟩ : syracuseStep 28554191 = 42831287) B42831287
theorem B40113953 : Blo 1564980 40113953 := bstep (se 2 (by rfl) ⟨15042732, by rfl⟩ : syracuseStep 40113953 = 30085465) B30085465
theorem B2349659 : Blo 1564980 2349659 := bstep (se 1 (by rfl) ⟨1762244, by rfl⟩ : syracuseStep 2349659 = 3524489) B3524489
theorem B5282657 : Blo 1564980 5282657 := bstep (se 2 (by rfl) ⟨1980996, by rfl⟩ : syracuseStep 5282657 = 3961993) B3961993
theorem B5283359 : Blo 1564980 5283359 := bstep (se 1 (by rfl) ⟨3962519, by rfl⟩ : syracuseStep 5283359 = 7925039) B7925039
theorem B5644169 : Blo 1564980 5644169 := bstep (se 2 (by rfl) ⟨2116563, by rfl⟩ : syracuseStep 5644169 = 4233127) B4233127
theorem B3522473 : Blo 1564980 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B1982495 : Blo 1564980 1982495 := bstep (se 1 (by rfl) ⟨1486871, by rfl⟩ : syracuseStep 1982495 = 2973743) B2973743
theorem B10035359 : Blo 1564980 10035359 := bstep (se 1 (by rfl) ⟨7526519, by rfl⟩ : syracuseStep 10035359 = 15053039) B15053039
theorem B3522743 : Blo 1564980 3522743 := bstep (se 1 (by rfl) ⟨2642057, by rfl⟩ : syracuseStep 3522743 = 5284115) B5284115
theorem B5358071 : Blo 1564980 5358071 := bstep (se 1 (by rfl) ⟨4018553, by rfl⟩ : syracuseStep 5358071 = 8037107) B8037107
theorem B7144519 : Blo 1564980 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B3523679 : Blo 1564980 3523679 := bstep (se 1 (by rfl) ⟨2642759, by rfl⟩ : syracuseStep 3523679 = 5285519) B5285519
theorem B2229385 : Blo 1564980 2229385 := bstep (se 2 (by rfl) ⟨836019, by rfl⟩ : syracuseStep 2229385 = 1672039) B1672039
theorem B1566439 : Blo 1564980 1566439 := bstep (se 1 (by rfl) ⟨1174829, by rfl⟩ : syracuseStep 1566439 = 2349659) B2349659
theorem B171395189 : Blo 1564980 171395189 := bstep (se 5 (by rfl) ⟨8034149, by rfl⟩ : syracuseStep 171395189 = 16068299) B16068299
theorem B3762779 : Blo 1564980 3762779 := bstep (se 1 (by rfl) ⟨2822084, by rfl⟩ : syracuseStep 3762779 = 5644169) B5644169
theorem B108694433 : Blo 1564980 108694433 := bstep (se 2 (by rfl) ⟨40760412, by rfl⟩ : syracuseStep 108694433 = 81520825) B81520825
theorem B13372411 : Blo 1564980 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B26742635 : Blo 1564980 26742635 := bstep (se 1 (by rfl) ⟨20056976, by rfl⟩ : syracuseStep 26742635 = 40113953) B40113953
theorem B2822185 : Blo 1564980 2822185 := bstep (se 2 (by rfl) ⟨1058319, by rfl⟩ : syracuseStep 2822185 = 2116639) B2116639
theorem B13562063 : Blo 1564980 13562063 := bstep (se 1 (by rfl) ⟨10171547, by rfl⟩ : syracuseStep 13562063 = 20343095) B20343095
theorem B4460957 : Blo 1564980 4460957 := bstep (se 3 (by rfl) ⟨836429, by rfl⟩ : syracuseStep 4460957 = 1672859) B1672859
theorem B2348315 : Blo 1564980 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B2971343 : Blo 1564980 2971343 := bstep (se 1 (by rfl) ⟨2228507, by rfl⟩ : syracuseStep 2971343 = 4457015) B4457015
theorem B7526135 : Blo 1564980 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B19036127 : Blo 1564980 19036127 := bstep (se 1 (by rfl) ⟨14277095, by rfl⟩ : syracuseStep 19036127 = 28554191) B28554191
theorem B2349851 : Blo 1564980 2349851 := bstep (se 1 (by rfl) ⟨1762388, by rfl⟩ : syracuseStep 2349851 = 3524777) B3524777
theorem B3521321 : Blo 1564980 3521321 := bstep (se 2 (by rfl) ⟨1320495, by rfl⟩ : syracuseStep 3521321 = 2640991) B2640991
theorem B2350073 : Blo 1564980 2350073 := bstep (se 2 (by rfl) ⟨881277, by rfl⟩ : syracuseStep 2350073 = 1762555) B1762555
theorem B2350079 : Blo 1564980 2350079 := bstep (se 1 (by rfl) ⟨1762559, by rfl⟩ : syracuseStep 2350079 = 3525119) B3525119
theorem B3521771 : Blo 1564980 3521771 := bstep (se 1 (by rfl) ⟨2641328, by rfl⟩ : syracuseStep 3521771 = 5282657) B5282657
theorem B2350439 : Blo 1564980 2350439 := bstep (se 1 (by rfl) ⟨1762829, by rfl⟩ : syracuseStep 2350439 = 3525659) B3525659
theorem B3522239 : Blo 1564980 3522239 := bstep (se 1 (by rfl) ⟨2641679, by rfl⟩ : syracuseStep 3522239 = 5283359) B5283359
theorem B6692699 : Blo 1564980 6692699 := bstep (se 1 (by rfl) ⟨5019524, by rfl⟩ : syracuseStep 6692699 = 10039049) B10039049
theorem B2973971 : Blo 1564980 2973971 := bstep (se 1 (by rfl) ⟨2230478, by rfl⟩ : syracuseStep 2973971 = 4460957) B4460957
theorem B3572047 : Blo 1564980 3572047 := bstep (se 1 (by rfl) ⟨2679035, by rfl⟩ : syracuseStep 3572047 = 5358071) B5358071
theorem B1565543 : Blo 1564980 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B12690751 : Blo 1564980 12690751 := bstep (se 1 (by rfl) ⟨9518063, by rfl⟩ : syracuseStep 12690751 = 19036127) B19036127
theorem B114263459 : Blo 1564980 114263459 := bstep (se 1 (by rfl) ⟨85697594, by rfl⟩ : syracuseStep 114263459 = 171395189) B171395189
theorem B1566567 : Blo 1564980 1566567 := bstep (se 1 (by rfl) ⟨1174925, by rfl⟩ : syracuseStep 1566567 = 2349851) B2349851
theorem B7923581 : Blo 1564980 7923581 := bstep (se 3 (by rfl) ⟨1485671, by rfl⟩ : syracuseStep 7923581 = 2971343) B2971343
theorem B1566715 : Blo 1564980 1566715 := bstep (se 1 (by rfl) ⟨1175036, by rfl⟩ : syracuseStep 1566715 = 2350073) B2350073
theorem B1566719 : Blo 1564980 1566719 := bstep (se 1 (by rfl) ⟨1175039, by rfl⟩ : syracuseStep 1566719 = 2350079) B2350079
theorem B1566959 : Blo 1564980 1566959 := bstep (se 1 (by rfl) ⟨1175219, by rfl⟩ : syracuseStep 1566959 = 2350439) B2350439
theorem B289851821 : Blo 1564980 289851821 := bstep (se 3 (by rfl) ⟨54347216, by rfl⟩ : syracuseStep 289851821 = 108694433) B108694433
theorem B17828423 : Blo 1564980 17828423 := bstep (se 1 (by rfl) ⟨13371317, by rfl⟩ : syracuseStep 17828423 = 26742635) B26742635
theorem B5286653 : Blo 1564980 5286653 := bstep (se 3 (by rfl) ⟨991247, by rfl⟩ : syracuseStep 5286653 = 1982495) B1982495
theorem B15051653 : Blo 1564980 15051653 := bstep (se 4 (by rfl) ⟨1411092, by rfl⟩ : syracuseStep 15051653 = 2822185) B2822185
theorem B5017423 : Blo 1564980 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B17829881 : Blo 1564980 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B2347547 : Blo 1564980 2347547 := bstep (se 1 (by rfl) ⟨1760660, by rfl⟩ : syracuseStep 2347547 = 3521321) B3521321
theorem B2347847 : Blo 1564980 2347847 := bstep (se 1 (by rfl) ⟨1760885, by rfl⟩ : syracuseStep 2347847 = 3521771) B3521771
theorem B2348159 : Blo 1564980 2348159 := bstep (se 1 (by rfl) ⟨1761119, by rfl⟩ : syracuseStep 2348159 = 3522239) B3522239
theorem B4461799 : Blo 1564980 4461799 := bstep (se 1 (by rfl) ⟨3346349, by rfl⟩ : syracuseStep 4461799 = 6692699) B6692699
theorem B6690239 : Blo 1564980 6690239 := bstep (se 1 (by rfl) ⟨5017679, by rfl⟩ : syracuseStep 6690239 = 10035359) B10035359
theorem B2348495 : Blo 1564980 2348495 := bstep (se 1 (by rfl) ⟨1761371, by rfl⟩ : syracuseStep 2348495 = 3522743) B3522743
theorem B9041375 : Blo 1564980 9041375 := bstep (se 1 (by rfl) ⟨6781031, by rfl⟩ : syracuseStep 9041375 = 13562063) B13562063
theorem B2349119 : Blo 1564980 2349119 := bstep (se 1 (by rfl) ⟨1761839, by rfl⟩ : syracuseStep 2349119 = 3523679) B3523679
theorem B9526025 : Blo 1564980 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B2972513 : Blo 1564980 2972513 := bstep (se 2 (by rfl) ⟨1114692, by rfl⟩ : syracuseStep 2972513 = 2229385) B2229385
theorem B10034077 : Blo 1564980 10034077 := bstep (se 3 (by rfl) ⟨1881389, by rfl⟩ : syracuseStep 10034077 = 3762779) B3762779
theorem B1982647 : Blo 1564980 1982647 := bstep (se 1 (by rfl) ⟨1486985, by rfl⟩ : syracuseStep 1982647 = 2973971) B2973971
theorem B1565031 : Blo 1564980 1565031 := bstep (se 1 (by rfl) ⟨1173773, by rfl⟩ : syracuseStep 1565031 = 2347547) B2347547
theorem B1565231 : Blo 1564980 1565231 := bstep (se 1 (by rfl) ⟨1173923, by rfl⟩ : syracuseStep 1565231 = 2347847) B2347847
theorem B1565439 : Blo 1564980 1565439 := bstep (se 1 (by rfl) ⟨1174079, by rfl⟩ : syracuseStep 1565439 = 2348159) B2348159
theorem B1565663 : Blo 1564980 1565663 := bstep (se 1 (by rfl) ⟨1174247, by rfl⟩ : syracuseStep 1565663 = 2348495) B2348495
theorem B13378769 : Blo 1564980 13378769 := bstep (se 2 (by rfl) ⟨5017038, by rfl⟩ : syracuseStep 13378769 = 10034077) B10034077
theorem B1566079 : Blo 1564980 1566079 := bstep (se 1 (by rfl) ⟨1174559, by rfl⟩ : syracuseStep 1566079 = 2349119) B2349119
theorem B193234547 : Blo 1564980 193234547 := bstep (se 1 (by rfl) ⟨144925910, by rfl⟩ : syracuseStep 193234547 = 289851821) B289851821
theorem B5949065 : Blo 1564980 5949065 := bstep (se 2 (by rfl) ⟨2230899, by rfl⟩ : syracuseStep 5949065 = 4461799) B4461799
theorem B3524435 : Blo 1564980 3524435 := bstep (se 1 (by rfl) ⟨2643326, by rfl⟩ : syracuseStep 3524435 = 5286653) B5286653
theorem B6350683 : Blo 1564980 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B4762729 : Blo 1564980 4762729 := bstep (se 2 (by rfl) ⟨1786023, by rfl⟩ : syracuseStep 4762729 = 3572047) B3572047
theorem B4460159 : Blo 1564980 4460159 := bstep (se 1 (by rfl) ⟨3345119, by rfl⟩ : syracuseStep 4460159 = 6690239) B6690239
theorem B16921001 : Blo 1564980 16921001 := bstep (se 2 (by rfl) ⟨6345375, by rfl⟩ : syracuseStep 16921001 = 12690751) B12690751
theorem B6689897 : Blo 1564980 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B76175639 : Blo 1564980 76175639 := bstep (se 1 (by rfl) ⟨57131729, by rfl⟩ : syracuseStep 76175639 = 114263459) B114263459
theorem B6027583 : Blo 1564980 6027583 := bstep (se 1 (by rfl) ⟨4520687, by rfl⟩ : syracuseStep 6027583 = 9041375) B9041375
theorem B5282387 : Blo 1564980 5282387 := bstep (se 1 (by rfl) ⟨3961790, by rfl⟩ : syracuseStep 5282387 = 7923581) B7923581
theorem B11885615 : Blo 1564980 11885615 := bstep (se 1 (by rfl) ⟨8914211, by rfl⟩ : syracuseStep 11885615 = 17828423) B17828423
theorem B1981675 : Blo 1564980 1981675 := bstep (se 1 (by rfl) ⟨1486256, by rfl⟩ : syracuseStep 1981675 = 2972513) B2972513
theorem B10034435 : Blo 1564980 10034435 := bstep (se 1 (by rfl) ⟨7525826, by rfl⟩ : syracuseStep 10034435 = 15051653) B15051653
theorem B11886587 : Blo 1564980 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B11280667 : Blo 1564980 11280667 := bstep (se 1 (by rfl) ⟨8460500, by rfl⟩ : syracuseStep 11280667 = 16921001) B16921001
theorem B8036777 : Blo 1564980 8036777 := bstep (se 2 (by rfl) ⟨3013791, by rfl⟩ : syracuseStep 8036777 = 6027583) B6027583
theorem B3966043 : Blo 1564980 3966043 := bstep (se 1 (by rfl) ⟨2974532, by rfl⟩ : syracuseStep 3966043 = 5949065) B5949065
theorem B50783759 : Blo 1564980 50783759 := bstep (se 1 (by rfl) ⟨38087819, by rfl⟩ : syracuseStep 50783759 = 76175639) B76175639
theorem B7923743 : Blo 1564980 7923743 := bstep (se 1 (by rfl) ⟨5942807, by rfl⟩ : syracuseStep 7923743 = 11885615) B11885615
theorem B7924391 : Blo 1564980 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B4459931 : Blo 1564980 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B128823031 : Blo 1564980 128823031 := bstep (se 1 (by rfl) ⟨96617273, by rfl⟩ : syracuseStep 128823031 = 193234547) B193234547
theorem B2642233 : Blo 1564980 2642233 := bstep (se 2 (by rfl) ⟨990837, by rfl⟩ : syracuseStep 2642233 = 1981675) B1981675
theorem B6689623 : Blo 1564980 6689623 := bstep (se 1 (by rfl) ⟨5017217, by rfl⟩ : syracuseStep 6689623 = 10034435) B10034435
theorem B8467577 : Blo 1564980 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B2643529 : Blo 1564980 2643529 := bstep (se 2 (by rfl) ⟨991323, by rfl⟩ : syracuseStep 2643529 = 1982647) B1982647
theorem B25401221 : Blo 1564980 25401221 := bstep (se 4 (by rfl) ⟨2381364, by rfl⟩ : syracuseStep 25401221 = 4762729) B4762729
theorem B8919179 : Blo 1564980 8919179 := bstep (se 1 (by rfl) ⟨6689384, by rfl⟩ : syracuseStep 8919179 = 13378769) B13378769
theorem B2349623 : Blo 1564980 2349623 := bstep (se 1 (by rfl) ⟨1762217, by rfl⟩ : syracuseStep 2349623 = 3524435) B3524435
theorem B3521591 : Blo 1564980 3521591 := bstep (se 1 (by rfl) ⟨2641193, by rfl⟩ : syracuseStep 3521591 = 5282387) B5282387
theorem B2973439 : Blo 1564980 2973439 := bstep (se 1 (by rfl) ⟨2230079, by rfl⟩ : syracuseStep 2973439 = 4460159) B4460159
theorem B5357851 : Blo 1564980 5357851 := bstep (se 1 (by rfl) ⟨4018388, by rfl⟩ : syracuseStep 5357851 = 8036777) B8036777
theorem B15040889 : Blo 1564980 15040889 := bstep (se 2 (by rfl) ⟨5640333, by rfl⟩ : syracuseStep 15040889 = 11280667) B11280667
theorem B3522977 : Blo 1564980 3522977 := bstep (se 2 (by rfl) ⟨1321116, by rfl⟩ : syracuseStep 3522977 = 2642233) B2642233
theorem B5645051 : Blo 1564980 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B16934147 : Blo 1564980 16934147 := bstep (se 1 (by rfl) ⟨12700610, by rfl⟩ : syracuseStep 16934147 = 25401221) B25401221
theorem B687056165 : Blo 1564980 687056165 := bstep (se 4 (by rfl) ⟨64411515, by rfl⟩ : syracuseStep 687056165 = 128823031) B128823031
theorem B1566415 : Blo 1564980 1566415 := bstep (se 1 (by rfl) ⟨1174811, by rfl⟩ : syracuseStep 1566415 = 2349623) B2349623
theorem B3524705 : Blo 1564980 3524705 := bstep (se 2 (by rfl) ⟨1321764, by rfl⟩ : syracuseStep 3524705 = 2643529) B2643529
theorem B5288057 : Blo 1564980 5288057 := bstep (se 2 (by rfl) ⟨1983021, by rfl⟩ : syracuseStep 5288057 = 3966043) B3966043
theorem B2347727 : Blo 1564980 2347727 := bstep (se 1 (by rfl) ⟨1760795, by rfl⟩ : syracuseStep 2347727 = 3521591) B3521591
theorem B33855839 : Blo 1564980 33855839 := bstep (se 1 (by rfl) ⟨25391879, by rfl⟩ : syracuseStep 33855839 = 50783759) B50783759
theorem B8919497 : Blo 1564980 8919497 := bstep (se 2 (by rfl) ⟨3344811, by rfl⟩ : syracuseStep 8919497 = 6689623) B6689623
theorem B5282495 : Blo 1564980 5282495 := bstep (se 1 (by rfl) ⟨3961871, by rfl⟩ : syracuseStep 5282495 = 7923743) B7923743
theorem B5946119 : Blo 1564980 5946119 := bstep (se 1 (by rfl) ⟨4459589, by rfl⟩ : syracuseStep 5946119 = 8919179) B8919179
theorem B5282927 : Blo 1564980 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B2973287 : Blo 1564980 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B3964585 : Blo 1564980 3964585 := bstep (se 2 (by rfl) ⟨1486719, by rfl⟩ : syracuseStep 3964585 = 2973439) B2973439
theorem B10027259 : Blo 1564980 10027259 := bstep (se 1 (by rfl) ⟨7520444, by rfl⟩ : syracuseStep 10027259 = 15040889) B15040889
theorem B1565151 : Blo 1564980 1565151 := bstep (se 1 (by rfl) ⟨1173863, by rfl⟩ : syracuseStep 1565151 = 2347727) B2347727
theorem B11289431 : Blo 1564980 11289431 := bstep (se 1 (by rfl) ⟨8467073, by rfl⟩ : syracuseStep 11289431 = 16934147) B16934147
theorem B22570559 : Blo 1564980 22570559 := bstep (se 1 (by rfl) ⟨16927919, by rfl⟩ : syracuseStep 22570559 = 33855839) B33855839
theorem B5286113 : Blo 1564980 5286113 := bstep (se 2 (by rfl) ⟨1982292, by rfl⟩ : syracuseStep 5286113 = 3964585) B3964585
theorem B3525371 : Blo 1564980 3525371 := bstep (se 1 (by rfl) ⟨2644028, by rfl⟩ : syracuseStep 3525371 = 5288057) B5288057
theorem B3763367 : Blo 1564980 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B2348651 : Blo 1564980 2348651 := bstep (se 1 (by rfl) ⟨1761488, by rfl⟩ : syracuseStep 2348651 = 3522977) B3522977
theorem B114300821 : Blo 1564980 114300821 := bstep (se 6 (by rfl) ⟨2678925, by rfl⟩ : syracuseStep 114300821 = 5357851) B5357851
theorem B458037443 : Blo 1564980 458037443 := bstep (se 1 (by rfl) ⟨343528082, by rfl⟩ : syracuseStep 458037443 = 687056165) B687056165
theorem B2349803 : Blo 1564980 2349803 := bstep (se 1 (by rfl) ⟨1762352, by rfl⟩ : syracuseStep 2349803 = 3524705) B3524705
theorem B7928765 : Blo 1564980 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B5946331 : Blo 1564980 5946331 := bstep (se 1 (by rfl) ⟨4459748, by rfl⟩ : syracuseStep 5946331 = 8919497) B8919497
theorem B3521663 : Blo 1564980 3521663 := bstep (se 1 (by rfl) ⟨2641247, by rfl⟩ : syracuseStep 3521663 = 5282495) B5282495
theorem B3964079 : Blo 1564980 3964079 := bstep (se 1 (by rfl) ⟨2973059, by rfl⟩ : syracuseStep 3964079 = 5946119) B5946119
theorem B3521951 : Blo 1564980 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B6684839 : Blo 1564980 6684839 := bstep (se 1 (by rfl) ⟨5013629, by rfl⟩ : syracuseStep 6684839 = 10027259) B10027259
theorem B1565767 : Blo 1564980 1565767 := bstep (se 1 (by rfl) ⟨1174325, by rfl⟩ : syracuseStep 1565767 = 2348651) B2348651
theorem B3524075 : Blo 1564980 3524075 := bstep (se 1 (by rfl) ⟨2643056, by rfl⟩ : syracuseStep 3524075 = 5286113) B5286113
theorem B1566535 : Blo 1564980 1566535 := bstep (se 1 (by rfl) ⟨1174901, by rfl⟩ : syracuseStep 1566535 = 2349803) B2349803
theorem B5285843 : Blo 1564980 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B2508911 : Blo 1564980 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B2347775 : Blo 1564980 2347775 := bstep (se 1 (by rfl) ⟨1760831, by rfl⟩ : syracuseStep 2347775 = 3521663) B3521663
theorem B2642719 : Blo 1564980 2642719 := bstep (se 1 (by rfl) ⟨1982039, by rfl⟩ : syracuseStep 2642719 = 3964079) B3964079
theorem B2347967 : Blo 1564980 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B1221433181 : Blo 1564980 1221433181 := bstep (se 3 (by rfl) ⟨229018721, by rfl⟩ : syracuseStep 1221433181 = 458037443) B458037443
theorem B7526287 : Blo 1564980 7526287 := bstep (se 1 (by rfl) ⟨5644715, by rfl⟩ : syracuseStep 7526287 = 11289431) B11289431
theorem B15047039 : Blo 1564980 15047039 := bstep (se 1 (by rfl) ⟨11285279, by rfl⟩ : syracuseStep 15047039 = 22570559) B22570559
theorem B76200547 : Blo 1564980 76200547 := bstep (se 1 (by rfl) ⟨57150410, by rfl⟩ : syracuseStep 76200547 = 114300821) B114300821
theorem B7928441 : Blo 1564980 7928441 := bstep (se 2 (by rfl) ⟨2973165, by rfl⟩ : syracuseStep 7928441 = 5946331) B5946331
theorem B2350247 : Blo 1564980 2350247 := bstep (se 1 (by rfl) ⟨1762685, by rfl⟩ : syracuseStep 2350247 = 3525371) B3525371
theorem B4456559 : Blo 1564980 4456559 := bstep (se 1 (by rfl) ⟨3342419, by rfl⟩ : syracuseStep 4456559 = 6684839) B6684839
theorem B1565183 : Blo 1564980 1565183 := bstep (se 1 (by rfl) ⟨1173887, by rfl⟩ : syracuseStep 1565183 = 2347775) B2347775
theorem B1565311 : Blo 1564980 1565311 := bstep (se 1 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 1565311 = 2347967) B2347967
theorem B3523625 : Blo 1564980 3523625 := bstep (se 2 (by rfl) ⟨1321359, by rfl⟩ : syracuseStep 3523625 = 2642719) B2642719
theorem B3523895 : Blo 1564980 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B1672607 : Blo 1564980 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B5285627 : Blo 1564980 5285627 := bstep (se 1 (by rfl) ⟨3964220, by rfl⟩ : syracuseStep 5285627 = 7928441) B7928441
theorem B1566831 : Blo 1564980 1566831 := bstep (se 1 (by rfl) ⟨1175123, by rfl⟩ : syracuseStep 1566831 = 2350247) B2350247
theorem B101600729 : Blo 1564980 101600729 := bstep (se 2 (by rfl) ⟨38100273, by rfl⟩ : syracuseStep 101600729 = 76200547) B76200547
theorem B814288787 : Blo 1564980 814288787 := bstep (se 1 (by rfl) ⟨610716590, by rfl⟩ : syracuseStep 814288787 = 1221433181) B1221433181
theorem B10031359 : Blo 1564980 10031359 := bstep (se 1 (by rfl) ⟨7523519, by rfl⟩ : syracuseStep 10031359 = 15047039) B15047039
theorem B2349383 : Blo 1564980 2349383 := bstep (se 1 (by rfl) ⟨1762037, by rfl⟩ : syracuseStep 2349383 = 3524075) B3524075
theorem B40140197 : Blo 1564980 40140197 := bstep (se 4 (by rfl) ⟨3763143, by rfl⟩ : syracuseStep 40140197 = 7526287) B7526287
theorem B3523751 : Blo 1564980 3523751 := bstep (se 1 (by rfl) ⟨2642813, by rfl⟩ : syracuseStep 3523751 = 5285627) B5285627
theorem B1566255 : Blo 1564980 1566255 := bstep (se 1 (by rfl) ⟨1174691, by rfl⟩ : syracuseStep 1566255 = 2349383) B2349383
theorem B67733819 : Blo 1564980 67733819 := bstep (se 1 (by rfl) ⟨50800364, by rfl⟩ : syracuseStep 67733819 = 101600729) B101600729
theorem B4460285 : Blo 1564980 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B26760131 : Blo 1564980 26760131 := bstep (se 1 (by rfl) ⟨20070098, by rfl⟩ : syracuseStep 26760131 = 40140197) B40140197
theorem B11884157 : Blo 1564980 11884157 := bstep (se 3 (by rfl) ⟨2228279, by rfl⟩ : syracuseStep 11884157 = 4456559) B4456559
theorem B13375145 : Blo 1564980 13375145 := bstep (se 2 (by rfl) ⟨5015679, by rfl⟩ : syracuseStep 13375145 = 10031359) B10031359
theorem B2349083 : Blo 1564980 2349083 := bstep (se 1 (by rfl) ⟨1761812, by rfl⟩ : syracuseStep 2349083 = 3523625) B3523625
theorem B2349263 : Blo 1564980 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B542859191 : Blo 1564980 542859191 := bstep (se 1 (by rfl) ⟨407144393, by rfl⟩ : syracuseStep 542859191 = 814288787) B814288787
theorem B7922771 : Blo 1564980 7922771 := bstep (se 1 (by rfl) ⟨5942078, by rfl⟩ : syracuseStep 7922771 = 11884157) B11884157
theorem B1566055 : Blo 1564980 1566055 := bstep (se 1 (by rfl) ⟨1174541, by rfl⟩ : syracuseStep 1566055 = 2349083) B2349083
theorem B1566175 : Blo 1564980 1566175 := bstep (se 1 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 1566175 = 2349263) B2349263
theorem B45155879 : Blo 1564980 45155879 := bstep (se 1 (by rfl) ⟨33866909, by rfl⟩ : syracuseStep 45155879 = 67733819) B67733819
theorem B8916763 : Blo 1564980 8916763 := bstep (se 1 (by rfl) ⟨6687572, by rfl⟩ : syracuseStep 8916763 = 13375145) B13375145
theorem B17840087 : Blo 1564980 17840087 := bstep (se 1 (by rfl) ⟨13380065, by rfl⟩ : syracuseStep 17840087 = 26760131) B26760131
theorem B2349167 : Blo 1564980 2349167 := bstep (se 1 (by rfl) ⟨1761875, by rfl⟩ : syracuseStep 2349167 = 3523751) B3523751
theorem B2973523 : Blo 1564980 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B361906127 : Blo 1564980 361906127 := bstep (se 1 (by rfl) ⟨271429595, by rfl⟩ : syracuseStep 361906127 = 542859191) B542859191
theorem B1566111 : Blo 1564980 1566111 := bstep (se 1 (by rfl) ⟨1174583, by rfl⟩ : syracuseStep 1566111 = 2349167) B2349167
theorem B11889017 : Blo 1564980 11889017 := bstep (se 2 (by rfl) ⟨4458381, by rfl⟩ : syracuseStep 11889017 = 8916763) B8916763
theorem B5281847 : Blo 1564980 5281847 := bstep (se 1 (by rfl) ⟨3961385, by rfl⟩ : syracuseStep 5281847 = 7922771) B7922771
theorem B30103919 : Blo 1564980 30103919 := bstep (se 1 (by rfl) ⟨22577939, by rfl⟩ : syracuseStep 30103919 = 45155879) B45155879
theorem B11893391 : Blo 1564980 11893391 := bstep (se 1 (by rfl) ⟨8920043, by rfl⟩ : syracuseStep 11893391 = 17840087) B17840087
theorem B3964697 : Blo 1564980 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B241270751 : Blo 1564980 241270751 := bstep (se 1 (by rfl) ⟨180953063, by rfl⟩ : syracuseStep 241270751 = 361906127) B361906127
theorem B7926011 : Blo 1564980 7926011 := bstep (se 1 (by rfl) ⟨5944508, by rfl⟩ : syracuseStep 7926011 = 11889017) B11889017
theorem B2643131 : Blo 1564980 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B160847167 : Blo 1564980 160847167 := bstep (se 1 (by rfl) ⟨120635375, by rfl⟩ : syracuseStep 160847167 = 241270751) B241270751
theorem B3521231 : Blo 1564980 3521231 := bstep (se 1 (by rfl) ⟨2640923, by rfl⟩ : syracuseStep 3521231 = 5281847) B5281847
theorem B20069279 : Blo 1564980 20069279 := bstep (se 1 (by rfl) ⟨15051959, by rfl⟩ : syracuseStep 20069279 = 30103919) B30103919
theorem B7928927 : Blo 1564980 7928927 := bstep (se 1 (by rfl) ⟨5946695, by rfl⟩ : syracuseStep 7928927 = 11893391) B11893391
theorem B5284007 : Blo 1564980 5284007 := bstep (se 1 (by rfl) ⟨3963005, by rfl⟩ : syracuseStep 5284007 = 7926011) B7926011
theorem B1762087 : Blo 1564980 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B13379519 : Blo 1564980 13379519 := bstep (se 1 (by rfl) ⟨10034639, by rfl⟩ : syracuseStep 13379519 = 20069279) B20069279
theorem B5285951 : Blo 1564980 5285951 := bstep (se 1 (by rfl) ⟨3964463, by rfl⟩ : syracuseStep 5285951 = 7928927) B7928927
theorem B214462889 : Blo 1564980 214462889 := bstep (se 2 (by rfl) ⟨80423583, by rfl⟩ : syracuseStep 214462889 = 160847167) B160847167
theorem B2347487 : Blo 1564980 2347487 := bstep (se 1 (by rfl) ⟨1760615, by rfl⟩ : syracuseStep 2347487 = 3521231) B3521231
theorem B3522671 : Blo 1564980 3522671 := bstep (se 1 (by rfl) ⟨2642003, by rfl⟩ : syracuseStep 3522671 = 5284007) B5284007
theorem B142975259 : Blo 1564980 142975259 := bstep (se 1 (by rfl) ⟨107231444, by rfl⟩ : syracuseStep 142975259 = 214462889) B214462889
theorem B1564991 : Blo 1564980 1564991 := bstep (se 1 (by rfl) ⟨1173743, by rfl⟩ : syracuseStep 1564991 = 2347487) B2347487
theorem B3523967 : Blo 1564980 3523967 := bstep (se 1 (by rfl) ⟨2642975, by rfl⟩ : syracuseStep 3523967 = 5285951) B5285951
theorem B2349449 : Blo 1564980 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B8919679 : Blo 1564980 8919679 := bstep (se 1 (by rfl) ⟨6689759, by rfl⟩ : syracuseStep 8919679 = 13379519) B13379519
theorem B1566299 : Blo 1564980 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B95316839 : Blo 1564980 95316839 := bstep (se 1 (by rfl) ⟨71487629, by rfl⟩ : syracuseStep 95316839 = 142975259) B142975259
theorem B2348447 : Blo 1564980 2348447 := bstep (se 1 (by rfl) ⟨1761335, by rfl⟩ : syracuseStep 2348447 = 3522671) B3522671
theorem B11892905 : Blo 1564980 11892905 := bstep (se 2 (by rfl) ⟨4459839, by rfl⟩ : syracuseStep 11892905 = 8919679) B8919679
theorem B2349311 : Blo 1564980 2349311 := bstep (se 1 (by rfl) ⟨1761983, by rfl⟩ : syracuseStep 2349311 = 3523967) B3523967
theorem B1565631 : Blo 1564980 1565631 := bstep (se 1 (by rfl) ⟨1174223, by rfl⟩ : syracuseStep 1565631 = 2348447) B2348447
theorem B1566207 : Blo 1564980 1566207 := bstep (se 1 (by rfl) ⟨1174655, by rfl⟩ : syracuseStep 1566207 = 2349311) B2349311
theorem B7928603 : Blo 1564980 7928603 := bstep (se 1 (by rfl) ⟨5946452, by rfl⟩ : syracuseStep 7928603 = 11892905) B11892905
theorem B63544559 : Blo 1564980 63544559 := bstep (se 1 (by rfl) ⟨47658419, by rfl⟩ : syracuseStep 63544559 = 95316839) B95316839
theorem B169452157 : Blo 1564980 169452157 := bstep (se 3 (by rfl) ⟨31772279, by rfl⟩ : syracuseStep 169452157 = 63544559) B63544559
theorem B5285735 : Blo 1564980 5285735 := bstep (se 1 (by rfl) ⟨3964301, by rfl⟩ : syracuseStep 5285735 = 7928603) B7928603
theorem B225936209 : Blo 1564980 225936209 := bstep (se 2 (by rfl) ⟨84726078, by rfl⟩ : syracuseStep 225936209 = 169452157) B169452157
theorem B3523823 : Blo 1564980 3523823 := bstep (se 1 (by rfl) ⟨2642867, by rfl⟩ : syracuseStep 3523823 = 5285735) B5285735
theorem B150624139 : Blo 1564980 150624139 := bstep (se 1 (by rfl) ⟨112968104, by rfl⟩ : syracuseStep 150624139 = 225936209) B225936209
theorem B2349215 : Blo 1564980 2349215 := bstep (se 1 (by rfl) ⟨1761911, by rfl⟩ : syracuseStep 2349215 = 3523823) B3523823
theorem B1566143 : Blo 1564980 1566143 := bstep (se 1 (by rfl) ⟨1174607, by rfl⟩ : syracuseStep 1566143 = 2349215) B2349215
theorem B200832185 : Blo 1564980 200832185 := bstep (se 2 (by rfl) ⟨75312069, by rfl⟩ : syracuseStep 200832185 = 150624139) B150624139
theorem B133888123 : Blo 1564980 133888123 := bstep (se 1 (by rfl) ⟨100416092, by rfl⟩ : syracuseStep 133888123 = 200832185) B200832185
theorem B714069989 : Blo 1564980 714069989 := bstep (se 4 (by rfl) ⟨66944061, by rfl⟩ : syracuseStep 714069989 = 133888123) B133888123
theorem B476046659 : Blo 1564980 476046659 := bstep (se 1 (by rfl) ⟨357034994, by rfl⟩ : syracuseStep 476046659 = 714069989) B714069989
theorem B317364439 : Blo 1564980 317364439 := bstep (se 1 (by rfl) ⟨238023329, by rfl⟩ : syracuseStep 317364439 = 476046659) B476046659
theorem B423152585 : Blo 1564980 423152585 := bstep (se 2 (by rfl) ⟨158682219, by rfl⟩ : syracuseStep 423152585 = 317364439) B317364439
theorem B282101723 : Blo 1564980 282101723 := bstep (se 1 (by rfl) ⟨211576292, by rfl⟩ : syracuseStep 282101723 = 423152585) B423152585
theorem B188067815 : Blo 1564980 188067815 := bstep (se 1 (by rfl) ⟨141050861, by rfl⟩ : syracuseStep 188067815 = 282101723) B282101723
theorem B125378543 : Blo 1564980 125378543 := bstep (se 1 (by rfl) ⟨94033907, by rfl⟩ : syracuseStep 125378543 = 188067815) B188067815
theorem B83585695 : Blo 1564980 83585695 := bstep (se 1 (by rfl) ⟨62689271, by rfl⟩ : syracuseStep 83585695 = 125378543) B125378543
theorem B111447593 : Blo 1564980 111447593 := bstep (se 2 (by rfl) ⟨41792847, by rfl⟩ : syracuseStep 111447593 = 83585695) B83585695
theorem B74298395 : Blo 1564980 74298395 := bstep (se 1 (by rfl) ⟨55723796, by rfl⟩ : syracuseStep 74298395 = 111447593) B111447593
theorem B198129053 : Blo 1564980 198129053 := bstep (se 3 (by rfl) ⟨37149197, by rfl⟩ : syracuseStep 198129053 = 74298395) B74298395
theorem B132086035 : Blo 1564980 132086035 := bstep (se 1 (by rfl) ⟨99064526, by rfl⟩ : syracuseStep 132086035 = 198129053) B198129053
theorem B704458853 : Blo 1564980 704458853 := bstep (se 4 (by rfl) ⟨66043017, by rfl⟩ : syracuseStep 704458853 = 132086035) B132086035
theorem B469639235 : Blo 1564980 469639235 := bstep (se 1 (by rfl) ⟨352229426, by rfl⟩ : syracuseStep 469639235 = 704458853) B704458853
theorem B313092823 : Blo 1564980 313092823 := bstep (se 1 (by rfl) ⟨234819617, by rfl⟩ : syracuseStep 313092823 = 469639235) B469639235
theorem B417457097 : Blo 1564980 417457097 := bstep (se 2 (by rfl) ⟨156546411, by rfl⟩ : syracuseStep 417457097 = 313092823) B313092823
theorem B278304731 : Blo 1564980 278304731 := bstep (se 1 (by rfl) ⟨208728548, by rfl⟩ : syracuseStep 278304731 = 417457097) B417457097
theorem B185536487 : Blo 1564980 185536487 := bstep (se 1 (by rfl) ⟨139152365, by rfl⟩ : syracuseStep 185536487 = 278304731) B278304731
theorem B123690991 : Blo 1564980 123690991 := bstep (se 1 (by rfl) ⟨92768243, by rfl⟩ : syracuseStep 123690991 = 185536487) B185536487
theorem B164921321 : Blo 1564980 164921321 := bstep (se 2 (by rfl) ⟨61845495, by rfl⟩ : syracuseStep 164921321 = 123690991) B123690991
theorem B109947547 : Blo 1564980 109947547 := bstep (se 1 (by rfl) ⟨82460660, by rfl⟩ : syracuseStep 109947547 = 164921321) B164921321
theorem B146596729 : Blo 1564980 146596729 := bstep (se 2 (by rfl) ⟨54973773, by rfl⟩ : syracuseStep 146596729 = 109947547) B109947547
theorem B195462305 : Blo 1564980 195462305 := bstep (se 2 (by rfl) ⟨73298364, by rfl⟩ : syracuseStep 195462305 = 146596729) B146596729
theorem B130308203 : Blo 1564980 130308203 := bstep (se 1 (by rfl) ⟨97731152, by rfl⟩ : syracuseStep 130308203 = 195462305) B195462305
theorem B86872135 : Blo 1564980 86872135 := bstep (se 1 (by rfl) ⟨65154101, by rfl⟩ : syracuseStep 86872135 = 130308203) B130308203
theorem B115829513 : Blo 1564980 115829513 := bstep (se 2 (by rfl) ⟨43436067, by rfl⟩ : syracuseStep 115829513 = 86872135) B86872135
theorem B77219675 : Blo 1564980 77219675 := bstep (se 1 (by rfl) ⟨57914756, by rfl⟩ : syracuseStep 77219675 = 115829513) B115829513
theorem B51479783 : Blo 1564980 51479783 := bstep (se 1 (by rfl) ⟨38609837, by rfl⟩ : syracuseStep 51479783 = 77219675) B77219675
theorem B34319855 : Blo 1564980 34319855 := bstep (se 1 (by rfl) ⟨25739891, by rfl⟩ : syracuseStep 34319855 = 51479783) B51479783
theorem B22879903 : Blo 1564980 22879903 := bstep (se 1 (by rfl) ⟨17159927, by rfl⟩ : syracuseStep 22879903 = 34319855) B34319855
theorem B30506537 : Blo 1564980 30506537 := bstep (se 2 (by rfl) ⟨11439951, by rfl⟩ : syracuseStep 30506537 = 22879903) B22879903
theorem B20337691 : Blo 1564980 20337691 := bstep (se 1 (by rfl) ⟨15253268, by rfl⟩ : syracuseStep 20337691 = 30506537) B30506537
theorem B27116921 : Blo 1564980 27116921 := bstep (se 2 (by rfl) ⟨10168845, by rfl⟩ : syracuseStep 27116921 = 20337691) B20337691
theorem B18077947 : Blo 1564980 18077947 := bstep (se 1 (by rfl) ⟨13558460, by rfl⟩ : syracuseStep 18077947 = 27116921) B27116921
theorem B96415717 : Blo 1564980 96415717 := bstep (se 4 (by rfl) ⟨9038973, by rfl⟩ : syracuseStep 96415717 = 18077947) B18077947
theorem B128554289 : Blo 1564980 128554289 := bstep (se 2 (by rfl) ⟨48207858, by rfl⟩ : syracuseStep 128554289 = 96415717) B96415717
theorem B85702859 : Blo 1564980 85702859 := bstep (se 1 (by rfl) ⟨64277144, by rfl⟩ : syracuseStep 85702859 = 128554289) B128554289
theorem B57135239 : Blo 1564980 57135239 := bstep (se 1 (by rfl) ⟨42851429, by rfl⟩ : syracuseStep 57135239 = 85702859) B85702859
theorem B38090159 : Blo 1564980 38090159 := bstep (se 1 (by rfl) ⟨28567619, by rfl⟩ : syracuseStep 38090159 = 57135239) B57135239
theorem B25393439 : Blo 1564980 25393439 := bstep (se 1 (by rfl) ⟨19045079, by rfl⟩ : syracuseStep 25393439 = 38090159) B38090159
theorem B16928959 : Blo 1564980 16928959 := bstep (se 1 (by rfl) ⟨12696719, by rfl⟩ : syracuseStep 16928959 = 25393439) B25393439
theorem B22571945 : Blo 1564980 22571945 := bstep (se 2 (by rfl) ⟨8464479, by rfl⟩ : syracuseStep 22571945 = 16928959) B16928959
theorem B15047963 : Blo 1564980 15047963 := bstep (se 1 (by rfl) ⟨11285972, by rfl⟩ : syracuseStep 15047963 = 22571945) B22571945
theorem B10031975 : Blo 1564980 10031975 := bstep (se 1 (by rfl) ⟨7523981, by rfl⟩ : syracuseStep 10031975 = 15047963) B15047963
theorem B6687983 : Blo 1564980 6687983 := bstep (se 1 (by rfl) ⟨5015987, by rfl⟩ : syracuseStep 6687983 = 10031975) B10031975
theorem B4458655 : Blo 1564980 4458655 := bstep (se 1 (by rfl) ⟨3343991, by rfl⟩ : syracuseStep 4458655 = 6687983) B6687983
theorem B5944873 : Blo 1564980 5944873 := bstep (se 2 (by rfl) ⟨2229327, by rfl⟩ : syracuseStep 5944873 = 4458655) B4458655
theorem B7926497 : Blo 1564980 7926497 := bstep (se 2 (by rfl) ⟨2972436, by rfl⟩ : syracuseStep 7926497 = 5944873) B5944873
theorem B5284331 : Blo 1564980 5284331 := bstep (se 1 (by rfl) ⟨3963248, by rfl⟩ : syracuseStep 5284331 = 7926497) B7926497
theorem B3522887 : Blo 1564980 3522887 := bstep (se 1 (by rfl) ⟨2642165, by rfl⟩ : syracuseStep 3522887 = 5284331) B5284331
theorem B2348591 : Blo 1564980 2348591 := bstep (se 1 (by rfl) ⟨1761443, by rfl⟩ : syracuseStep 2348591 = 3522887) B3522887
theorem B1565727 : Blo 1564980 1565727 := bstep (se 1 (by rfl) ⟨1174295, by rfl⟩ : syracuseStep 1565727 = 2348591) B2348591

theorem C0 (j : ℕ) (h1 : 391245 ≤ j) (h2 : j ≤ 391744) : Blo 1564980 (4 * j + 3) := by
  interval_cases j
  · exact B1564983
  · exact B1564987
  · exact B1564991
  · exact B1564995
  · exact B1564999
  · exact B1565003
  · exact B1565007
  · exact B1565011
  · exact B1565015
  · exact B1565019
  · exact B1565023
  · exact B1565027
  · exact B1565031
  · exact B1565035
  · exact B1565039
  · exact B1565043
  · exact B1565047
  · exact B1565051
  · exact B1565055
  · exact B1565059
  · exact B1565063
  · exact B1565067
  · exact B1565071
  · exact B1565075
  · exact B1565079
  · exact B1565083
  · exact B1565087
  · exact B1565091
  · exact B1565095
  · exact B1565099
  · exact B1565103
  · exact B1565107
  · exact B1565111
  · exact B1565115
  · exact B1565119
  · exact B1565123
  · exact B1565127
  · exact B1565131
  · exact B1565135
  · exact B1565139
  · exact B1565143
  · exact B1565147
  · exact B1565151
  · exact B1565155
  · exact B1565159
  · exact B1565163
  · exact B1565167
  · exact B1565171
  · exact B1565175
  · exact B1565179
  · exact B1565183
  · exact B1565187
  · exact B1565191
  · exact B1565195
  · exact B1565199
  · exact B1565203
  · exact B1565207
  · exact B1565211
  · exact B1565215
  · exact B1565219
  · exact B1565223
  · exact B1565227
  · exact B1565231
  · exact B1565235
  · exact B1565239
  · exact B1565243
  · exact B1565247
  · exact B1565251
  · exact B1565255
  · exact B1565259
  · exact B1565263
  · exact B1565267
  · exact B1565271
  · exact B1565275
  · exact B1565279
  · exact B1565283
  · exact B1565287
  · exact B1565291
  · exact B1565295
  · exact B1565299
  · exact B1565303
  · exact B1565307
  · exact B1565311
  · exact B1565315
  · exact B1565319
  · exact B1565323
  · exact B1565327
  · exact B1565331
  · exact B1565335
  · exact B1565339
  · exact B1565343
  · exact B1565347
  · exact B1565351
  · exact B1565355
  · exact B1565359
  · exact B1565363
  · exact B1565367
  · exact B1565371
  · exact B1565375
  · exact B1565379
  · exact B1565383
  · exact B1565387
  · exact B1565391
  · exact B1565395
  · exact B1565399
  · exact B1565403
  · exact B1565407
  · exact B1565411
  · exact B1565415
  · exact B1565419
  · exact B1565423
  · exact B1565427
  · exact B1565431
  · exact B1565435
  · exact B1565439
  · exact B1565443
  · exact B1565447
  · exact B1565451
  · exact B1565455
  · exact B1565459
  · exact B1565463
  · exact B1565467
  · exact B1565471
  · exact B1565475
  · exact B1565479
  · exact B1565483
  · exact B1565487
  · exact B1565491
  · exact B1565495
  · exact B1565499
  · exact B1565503
  · exact B1565507
  · exact B1565511
  · exact B1565515
  · exact B1565519
  · exact B1565523
  · exact B1565527
  · exact B1565531
  · exact B1565535
  · exact B1565539
  · exact B1565543
  · exact B1565547
  · exact B1565551
  · exact B1565555
  · exact B1565559
  · exact B1565563
  · exact B1565567
  · exact B1565571
  · exact B1565575
  · exact B1565579
  · exact B1565583
  · exact B1565587
  · exact B1565591
  · exact B1565595
  · exact B1565599
  · exact B1565603
  · exact B1565607
  · exact B1565611
  · exact B1565615
  · exact B1565619
  · exact B1565623
  · exact B1565627
  · exact B1565631
  · exact B1565635
  · exact B1565639
  · exact B1565643
  · exact B1565647
  · exact B1565651
  · exact B1565655
  · exact B1565659
  · exact B1565663
  · exact B1565667
  · exact B1565671
  · exact B1565675
  · exact B1565679
  · exact B1565683
  · exact B1565687
  · exact B1565691
  · exact B1565695
  · exact B1565699
  · exact B1565703
  · exact B1565707
  · exact B1565711
  · exact B1565715
  · exact B1565719
  · exact B1565723
  · exact B1565727
  · exact B1565731
  · exact B1565735
  · exact B1565739
  · exact B1565743
  · exact B1565747
  · exact B1565751
  · exact B1565755
  · exact B1565759
  · exact B1565763
  · exact B1565767
  · exact B1565771
  · exact B1565775
  · exact B1565779
  · exact B1565783
  · exact B1565787
  · exact B1565791
  · exact B1565795
  · exact B1565799
  · exact B1565803
  · exact B1565807
  · exact B1565811
  · exact B1565815
  · exact B1565819
  · exact B1565823
  · exact B1565827
  · exact B1565831
  · exact B1565835
  · exact B1565839
  · exact B1565843
  · exact B1565847
  · exact B1565851
  · exact B1565855
  · exact B1565859
  · exact B1565863
  · exact B1565867
  · exact B1565871
  · exact B1565875
  · exact B1565879
  · exact B1565883
  · exact B1565887
  · exact B1565891
  · exact B1565895
  · exact B1565899
  · exact B1565903
  · exact B1565907
  · exact B1565911
  · exact B1565915
  · exact B1565919
  · exact B1565923
  · exact B1565927
  · exact B1565931
  · exact B1565935
  · exact B1565939
  · exact B1565943
  · exact B1565947
  · exact B1565951
  · exact B1565955
  · exact B1565959
  · exact B1565963
  · exact B1565967
  · exact B1565971
  · exact B1565975
  · exact B1565979
  · exact B1565983
  · exact B1565987
  · exact B1565991
  · exact B1565995
  · exact B1565999
  · exact B1566003
  · exact B1566007
  · exact B1566011
  · exact B1566015
  · exact B1566019
  · exact B1566023
  · exact B1566027
  · exact B1566031
  · exact B1566035
  · exact B1566039
  · exact B1566043
  · exact B1566047
  · exact B1566051
  · exact B1566055
  · exact B1566059
  · exact B1566063
  · exact B1566067
  · exact B1566071
  · exact B1566075
  · exact B1566079
  · exact B1566083
  · exact B1566087
  · exact B1566091
  · exact B1566095
  · exact B1566099
  · exact B1566103
  · exact B1566107
  · exact B1566111
  · exact B1566115
  · exact B1566119
  · exact B1566123
  · exact B1566127
  · exact B1566131
  · exact B1566135
  · exact B1566139
  · exact B1566143
  · exact B1566147
  · exact B1566151
  · exact B1566155
  · exact B1566159
  · exact B1566163
  · exact B1566167
  · exact B1566171
  · exact B1566175
  · exact B1566179
  · exact B1566183
  · exact B1566187
  · exact B1566191
  · exact B1566195
  · exact B1566199
  · exact B1566203
  · exact B1566207
  · exact B1566211
  · exact B1566215
  · exact B1566219
  · exact B1566223
  · exact B1566227
  · exact B1566231
  · exact B1566235
  · exact B1566239
  · exact B1566243
  · exact B1566247
  · exact B1566251
  · exact B1566255
  · exact B1566259
  · exact B1566263
  · exact B1566267
  · exact B1566271
  · exact B1566275
  · exact B1566279
  · exact B1566283
  · exact B1566287
  · exact B1566291
  · exact B1566295
  · exact B1566299
  · exact B1566303
  · exact B1566307
  · exact B1566311
  · exact B1566315
  · exact B1566319
  · exact B1566323
  · exact B1566327
  · exact B1566331
  · exact B1566335
  · exact B1566339
  · exact B1566343
  · exact B1566347
  · exact B1566351
  · exact B1566355
  · exact B1566359
  · exact B1566363
  · exact B1566367
  · exact B1566371
  · exact B1566375
  · exact B1566379
  · exact B1566383
  · exact B1566387
  · exact B1566391
  · exact B1566395
  · exact B1566399
  · exact B1566403
  · exact B1566407
  · exact B1566411
  · exact B1566415
  · exact B1566419
  · exact B1566423
  · exact B1566427
  · exact B1566431
  · exact B1566435
  · exact B1566439
  · exact B1566443
  · exact B1566447
  · exact B1566451
  · exact B1566455
  · exact B1566459
  · exact B1566463
  · exact B1566467
  · exact B1566471
  · exact B1566475
  · exact B1566479
  · exact B1566483
  · exact B1566487
  · exact B1566491
  · exact B1566495
  · exact B1566499
  · exact B1566503
  · exact B1566507
  · exact B1566511
  · exact B1566515
  · exact B1566519
  · exact B1566523
  · exact B1566527
  · exact B1566531
  · exact B1566535
  · exact B1566539
  · exact B1566543
  · exact B1566547
  · exact B1566551
  · exact B1566555
  · exact B1566559
  · exact B1566563
  · exact B1566567
  · exact B1566571
  · exact B1566575
  · exact B1566579
  · exact B1566583
  · exact B1566587
  · exact B1566591
  · exact B1566595
  · exact B1566599
  · exact B1566603
  · exact B1566607
  · exact B1566611
  · exact B1566615
  · exact B1566619
  · exact B1566623
  · exact B1566627
  · exact B1566631
  · exact B1566635
  · exact B1566639
  · exact B1566643
  · exact B1566647
  · exact B1566651
  · exact B1566655
  · exact B1566659
  · exact B1566663
  · exact B1566667
  · exact B1566671
  · exact B1566675
  · exact B1566679
  · exact B1566683
  · exact B1566687
  · exact B1566691
  · exact B1566695
  · exact B1566699
  · exact B1566703
  · exact B1566707
  · exact B1566711
  · exact B1566715
  · exact B1566719
  · exact B1566723
  · exact B1566727
  · exact B1566731
  · exact B1566735
  · exact B1566739
  · exact B1566743
  · exact B1566747
  · exact B1566751
  · exact B1566755
  · exact B1566759
  · exact B1566763
  · exact B1566767
  · exact B1566771
  · exact B1566775
  · exact B1566779
  · exact B1566783
  · exact B1566787
  · exact B1566791
  · exact B1566795
  · exact B1566799
  · exact B1566803
  · exact B1566807
  · exact B1566811
  · exact B1566815
  · exact B1566819
  · exact B1566823
  · exact B1566827
  · exact B1566831
  · exact B1566835
  · exact B1566839
  · exact B1566843
  · exact B1566847
  · exact B1566851
  · exact B1566855
  · exact B1566859
  · exact B1566863
  · exact B1566867
  · exact B1566871
  · exact B1566875
  · exact B1566879
  · exact B1566883
  · exact B1566887
  · exact B1566891
  · exact B1566895
  · exact B1566899
  · exact B1566903
  · exact B1566907
  · exact B1566911
  · exact B1566915
  · exact B1566919
  · exact B1566923
  · exact B1566927
  · exact B1566931
  · exact B1566935
  · exact B1566939
  · exact B1566943
  · exact B1566947
  · exact B1566951
  · exact B1566955
  · exact B1566959
  · exact B1566963
  · exact B1566967
  · exact B1566971
  · exact B1566975
  · exact B1566979

theorem solution (m : ℕ) (hlo : 1564980 ≤ m) (hhi : m ≤ 1566980) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 391245 ≤ j := by omega
    have hj2 : j ≤ 391744 := by omega
    have hb : Blo 1564980 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
