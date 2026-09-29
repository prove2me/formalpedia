-- Prove2me | solution 1 for syracuse_descends_range_1825614_1827614
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:58:05.074088+00:00
-- url     : https://prove2.me/submissions/a67a22a8-ed4d-4e91-8b03-f133a6c5213f

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


theorem B6586373 : Blo 1825614 6586373 := bbase (se 4 (by rfl) ⟨617472, by rfl⟩ : syracuseStep 6586373 = 1234945) (by norm_num)
theorem B4759597 : Blo 1825614 4759597 := bbase (se 3 (by rfl) ⟨892424, by rfl⟩ : syracuseStep 4759597 = 1784849) (by norm_num)
theorem B2924669 : Blo 1825614 2924669 := bbase (se 3 (by rfl) ⟨548375, by rfl⟩ : syracuseStep 2924669 = 1096751) (by norm_num)
theorem B5202053 : Blo 1825614 5202053 := bbase (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) (by norm_num)
theorem B8896661 : Blo 1825614 8896661 := bbase (se 6 (by rfl) ⟨208515, by rfl⟩ : syracuseStep 8896661 = 417031) (by norm_num)
theorem B8331445 : Blo 1825614 8331445 := bbase (se 5 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 8331445 = 781073) (by norm_num)
theorem B7028965 : Blo 1825614 7028965 := bbase (se 4 (by rfl) ⟨658965, by rfl⟩ : syracuseStep 7028965 = 1317931) (by norm_num)
theorem B1949933 : Blo 1825614 1949933 := bbase (se 3 (by rfl) ⟨365612, by rfl⟩ : syracuseStep 1949933 = 731225) (by norm_num)
theorem B7028981 : Blo 1825614 7028981 := bbase (se 5 (by rfl) ⟨329483, by rfl⟩ : syracuseStep 7028981 = 658967) (by norm_num)
theorem B2343157 : Blo 1825614 2343157 := bbase (se 5 (by rfl) ⟨109835, by rfl⟩ : syracuseStep 2343157 = 219671) (by norm_num)
theorem B2343277 : Blo 1825614 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B1851769 : Blo 1825614 1851769 := bbase (se 2 (by rfl) ⟨694413, by rfl⟩ : syracuseStep 1851769 = 1388827) (by norm_num)
theorem B2310545 : Blo 1825614 2310545 := bbase (se 2 (by rfl) ⟨866454, by rfl⟩ : syracuseStep 2310545 = 1732909) (by norm_num)
theorem B3088813 : Blo 1825614 3088813 := bbase (se 3 (by rfl) ⟨579152, by rfl⟩ : syracuseStep 3088813 = 1158305) (by norm_num)
theorem B7799237 : Blo 1825614 7799237 := bbase (se 4 (by rfl) ⟨731178, by rfl⟩ : syracuseStep 7799237 = 1462357) (by norm_num)
theorem B2310601 : Blo 1825614 2310601 := bbase (se 2 (by rfl) ⟨866475, by rfl⟩ : syracuseStep 2310601 = 1732951) (by norm_num)
theorem B3899917 : Blo 1825614 3899917 := bbase (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) (by norm_num)
theorem B26346005 : Blo 1825614 26346005 := bbase (se 6 (by rfl) ⟨617484, by rfl⟩ : syracuseStep 26346005 = 1234969) (by norm_num)
theorem B2310697 : Blo 1825614 2310697 := bbase (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) (by norm_num)
theorem B3080821 : Blo 1825614 3080821 := bbase (se 5 (by rfl) ⟨144413, by rfl⟩ : syracuseStep 3080821 = 288827) (by norm_num)
theorem B2925181 : Blo 1825614 2925181 := bbase (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) (by norm_num)
theorem B1950377 : Blo 1825614 1950377 := bbase (se 2 (by rfl) ⟨731391, by rfl⟩ : syracuseStep 1950377 = 1462783) (by norm_num)
theorem B3080909 : Blo 1825614 3080909 := bbase (se 3 (by rfl) ⟨577670, by rfl⟩ : syracuseStep 3080909 = 1155341) (by norm_num)
theorem B2310869 : Blo 1825614 2310869 := bbase (se 7 (by rfl) ⟨27080, by rfl⟩ : syracuseStep 2310869 = 54161) (by norm_num)
theorem B1950437 : Blo 1825614 1950437 := bbase (se 4 (by rfl) ⟨182853, by rfl⟩ : syracuseStep 1950437 = 365707) (by norm_num)
theorem B2310925 : Blo 1825614 2310925 := bbase (se 3 (by rfl) ⟨433298, by rfl⟩ : syracuseStep 2310925 = 866597) (by norm_num)
theorem B3466061 : Blo 1825614 3466061 := bbase (se 3 (by rfl) ⟨649886, by rfl⟩ : syracuseStep 3466061 = 1299773) (by norm_num)
theorem B3081037 : Blo 1825614 3081037 := bbase (se 3 (by rfl) ⟨577694, by rfl⟩ : syracuseStep 3081037 = 1155389) (by norm_num)
theorem B5849941 : Blo 1825614 5849941 := bbase (se 9 (by rfl) ⟨17138, by rfl⟩ : syracuseStep 5849941 = 34277) (by norm_num)
theorem B1950565 : Blo 1825614 1950565 := bbase (se 4 (by rfl) ⟨182865, by rfl⟩ : syracuseStep 1950565 = 365731) (by norm_num)
theorem B2311021 : Blo 1825614 2311021 := bbase (se 3 (by rfl) ⟨433316, by rfl⟩ : syracuseStep 2311021 = 866633) (by norm_num)
theorem B5202805 : Blo 1825614 5202805 := bbase (se 5 (by rfl) ⟨243881, by rfl⟩ : syracuseStep 5202805 = 487763) (by norm_num)
theorem B10544021 : Blo 1825614 10544021 := bbase (se 6 (by rfl) ⟨247125, by rfl⟩ : syracuseStep 10544021 = 494251) (by norm_num)
theorem B3081125 : Blo 1825614 3081125 := bbase (se 4 (by rfl) ⟨288855, by rfl⟩ : syracuseStep 3081125 = 577711) (by norm_num)
theorem B8446949 : Blo 1825614 8446949 := bbase (se 4 (by rfl) ⟨791901, by rfl⟩ : syracuseStep 8446949 = 1583803) (by norm_num)
theorem B3900413 : Blo 1825614 3900413 := bbase (se 3 (by rfl) ⟨731327, by rfl⟩ : syracuseStep 3900413 = 1462655) (by norm_num)
theorem B4621333 : Blo 1825614 4621333 := bbase (se 6 (by rfl) ⟨108312, by rfl⟩ : syracuseStep 4621333 = 216625) (by norm_num)
theorem B2311193 : Blo 1825614 2311193 := bbase (se 2 (by rfl) ⟨866697, by rfl⟩ : syracuseStep 2311193 = 1733395) (by norm_num)
theorem B3081253 : Blo 1825614 3081253 := bbase (se 4 (by rfl) ⟨288867, by rfl⟩ : syracuseStep 3081253 = 577735) (by norm_num)
theorem B2311249 : Blo 1825614 2311249 := bbase (se 2 (by rfl) ⟨866718, by rfl⟩ : syracuseStep 2311249 = 1733437) (by norm_num)
theorem B3081341 : Blo 1825614 3081341 := bbase (se 3 (by rfl) ⟨577751, by rfl⟩ : syracuseStep 3081341 = 1155503) (by norm_num)
theorem B4621445 : Blo 1825614 4621445 := bbase (se 4 (by rfl) ⟨433260, by rfl⟩ : syracuseStep 4621445 = 866521) (by norm_num)
theorem B2311345 : Blo 1825614 2311345 := bbase (se 2 (by rfl) ⟨866754, by rfl⟩ : syracuseStep 2311345 = 1733509) (by norm_num)
theorem B9250037 : Blo 1825614 9250037 := bbase (se 5 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 9250037 = 867191) (by norm_num)
theorem B3081469 : Blo 1825614 3081469 := bbase (se 3 (by rfl) ⟨577775, by rfl⟩ : syracuseStep 3081469 = 1155551) (by norm_num)
theorem B6161669 : Blo 1825614 6161669 := bbase (se 4 (by rfl) ⟨577656, by rfl⟩ : syracuseStep 6161669 = 1155313) (by norm_num)
theorem B1951009 : Blo 1825614 1951009 := bbase (se 2 (by rfl) ⟨731628, by rfl⟩ : syracuseStep 1951009 = 1463257) (by norm_num)
theorem B2344225 : Blo 1825614 2344225 := bbase (se 2 (by rfl) ⟨879084, by rfl⟩ : syracuseStep 2344225 = 1758169) (by norm_num)
theorem B4621637 : Blo 1825614 4621637 := bbase (se 4 (by rfl) ⟨433278, by rfl⟩ : syracuseStep 4621637 = 866557) (by norm_num)
theorem B3515717 : Blo 1825614 3515717 := bbase (se 4 (by rfl) ⟨329598, by rfl⟩ : syracuseStep 3515717 = 659197) (by norm_num)
theorem B3081557 : Blo 1825614 3081557 := bbase (se 12 (by rfl) ⟨1128, by rfl⟩ : syracuseStep 3081557 = 2257) (by norm_num)
theorem B2311517 : Blo 1825614 2311517 := bbase (se 3 (by rfl) ⟨433409, by rfl⟩ : syracuseStep 2311517 = 866819) (by norm_num)
theorem B2311573 : Blo 1825614 2311573 := bbase (se 6 (by rfl) ⟨54177, by rfl⟩ : syracuseStep 2311573 = 108355) (by norm_num)
theorem B1951129 : Blo 1825614 1951129 := bbase (se 2 (by rfl) ⟨731673, by rfl⟩ : syracuseStep 1951129 = 1463347) (by norm_num)
theorem B7800245 : Blo 1825614 7800245 := bbase (se 5 (by rfl) ⟨365636, by rfl⟩ : syracuseStep 7800245 = 731273) (by norm_num)
theorem B6931925 : Blo 1825614 6931925 := bbase (se 7 (by rfl) ⟨81233, by rfl⟩ : syracuseStep 6931925 = 162467) (by norm_num)
theorem B3081685 : Blo 1825614 3081685 := bbase (se 7 (by rfl) ⟨36113, by rfl⟩ : syracuseStep 3081685 = 72227) (by norm_num)
theorem B2311669 : Blo 1825614 2311669 := bbase (se 5 (by rfl) ⟨108359, by rfl⟩ : syracuseStep 2311669 = 216719) (by norm_num)
theorem B3081773 : Blo 1825614 3081773 := bbase (se 3 (by rfl) ⟨577832, by rfl⟩ : syracuseStep 3081773 = 1155665) (by norm_num)
theorem B3466813 : Blo 1825614 3466813 := bbase (se 3 (by rfl) ⟨650027, by rfl⟩ : syracuseStep 3466813 = 1300055) (by norm_num)
theorem B2926181 : Blo 1825614 2926181 := bbase (se 4 (by rfl) ⟨274329, by rfl⟩ : syracuseStep 2926181 = 548659) (by norm_num)
theorem B9242261 : Blo 1825614 9242261 := bbase (se 6 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 9242261 = 433231) (by norm_num)
theorem B1951381 : Blo 1825614 1951381 := bbase (se 6 (by rfl) ⟨45735, by rfl⟩ : syracuseStep 1951381 = 91471) (by norm_num)
theorem B1951385 : Blo 1825614 1951385 := bbase (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) (by norm_num)
theorem B4621981 : Blo 1825614 4621981 := bbase (se 3 (by rfl) ⟨866621, by rfl⟩ : syracuseStep 4621981 = 1733243) (by norm_num)
theorem B2311841 : Blo 1825614 2311841 := bbase (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) (by norm_num)
theorem B3081901 : Blo 1825614 3081901 := bbase (se 3 (by rfl) ⟨577856, by rfl⟩ : syracuseStep 3081901 = 1155713) (by norm_num)
theorem B6162101 : Blo 1825614 6162101 := bbase (se 5 (by rfl) ⟨288848, by rfl⟩ : syracuseStep 6162101 = 577697) (by norm_num)
theorem B3466957 : Blo 1825614 3466957 := bbase (se 3 (by rfl) ⟨650054, by rfl⟩ : syracuseStep 3466957 = 1300109) (by norm_num)
theorem B2311897 : Blo 1825614 2311897 := bbase (se 2 (by rfl) ⟨866961, by rfl⟩ : syracuseStep 2311897 = 1733923) (by norm_num)
theorem B2926309 : Blo 1825614 2926309 := bbase (se 4 (by rfl) ⟨274341, by rfl⟩ : syracuseStep 2926309 = 548683) (by norm_num)
theorem B6932213 : Blo 1825614 6932213 := bbase (se 5 (by rfl) ⟨324947, by rfl⟩ : syracuseStep 6932213 = 649895) (by norm_num)
theorem B3081989 : Blo 1825614 3081989 := bbase (se 4 (by rfl) ⟨288936, by rfl⟩ : syracuseStep 3081989 = 577873) (by norm_num)
theorem B4622093 : Blo 1825614 4622093 := bbase (se 3 (by rfl) ⟨866642, by rfl⟩ : syracuseStep 4622093 = 1733285) (by norm_num)
theorem B2926373 : Blo 1825614 2926373 := bbase (se 4 (by rfl) ⟨274347, by rfl⟩ : syracuseStep 2926373 = 548695) (by norm_num)
theorem B2311993 : Blo 1825614 2311993 := bbase (se 2 (by rfl) ⟨866997, by rfl⟩ : syracuseStep 2311993 = 1733995) (by norm_num)
theorem B8898389 : Blo 1825614 8898389 := bbase (se 9 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 8898389 = 52139) (by norm_num)
theorem B3467117 : Blo 1825614 3467117 := bbase (se 3 (by rfl) ⟨650084, by rfl⟩ : syracuseStep 3467117 = 1300169) (by norm_num)
theorem B11700085 : Blo 1825614 11700085 := bbase (se 5 (by rfl) ⟨548441, by rfl⟩ : syracuseStep 11700085 = 1096883) (by norm_num)
theorem B3901301 : Blo 1825614 3901301 := bbase (se 5 (by rfl) ⟨182873, by rfl⟩ : syracuseStep 3901301 = 365747) (by norm_num)
theorem B3082117 : Blo 1825614 3082117 := bbase (se 4 (by rfl) ⟨288948, by rfl⟩ : syracuseStep 3082117 = 577897) (by norm_num)
theorem B4622285 : Blo 1825614 4622285 := bbase (se 3 (by rfl) ⟨866678, by rfl⟩ : syracuseStep 4622285 = 1733357) (by norm_num)
theorem B3082205 : Blo 1825614 3082205 := bbase (se 3 (by rfl) ⟨577913, by rfl⟩ : syracuseStep 3082205 = 1155827) (by norm_num)
theorem B2312165 : Blo 1825614 2312165 := bbase (se 4 (by rfl) ⟨216765, by rfl⟩ : syracuseStep 2312165 = 433531) (by norm_num)
theorem B3901421 : Blo 1825614 3901421 := bbase (se 3 (by rfl) ⟨731516, by rfl⟩ : syracuseStep 3901421 = 1463033) (by norm_num)
theorem B3467261 : Blo 1825614 3467261 := bbase (se 3 (by rfl) ⟨650111, by rfl⟩ : syracuseStep 3467261 = 1300223) (by norm_num)
theorem B2312221 : Blo 1825614 2312221 := bbase (se 3 (by rfl) ⟨433541, by rfl⟩ : syracuseStep 2312221 = 867083) (by norm_num)
theorem B4687949 : Blo 1825614 4687949 := bbase (se 3 (by rfl) ⟨878990, by rfl⟩ : syracuseStep 4687949 = 1757981) (by norm_num)
theorem B3082333 : Blo 1825614 3082333 := bbase (se 3 (by rfl) ⟨577937, by rfl⟩ : syracuseStep 3082333 = 1155875) (by norm_num)
theorem B6162533 : Blo 1825614 6162533 := bbase (se 4 (by rfl) ⟨577737, by rfl⟩ : syracuseStep 6162533 = 1155475) (by norm_num)
theorem B2312317 : Blo 1825614 2312317 := bbase (se 3 (by rfl) ⟨433559, by rfl⟩ : syracuseStep 2312317 = 867119) (by norm_num)
theorem B3704989 : Blo 1825614 3704989 := bbase (se 3 (by rfl) ⟨694685, by rfl⟩ : syracuseStep 3704989 = 1389371) (by norm_num)
theorem B3705005 : Blo 1825614 3705005 := bbase (se 3 (by rfl) ⟨694688, by rfl⟩ : syracuseStep 3705005 = 1389377) (by norm_num)
theorem B3082421 : Blo 1825614 3082421 := bbase (se 5 (by rfl) ⟨144488, by rfl⟩ : syracuseStep 3082421 = 288977) (by norm_num)
theorem B10397909 : Blo 1825614 10397909 := bbase (se 7 (by rfl) ⟨121850, by rfl⟩ : syracuseStep 10397909 = 243701) (by norm_num)
theorem B2738429 : Blo 1825614 2738429 := bbase (se 3 (by rfl) ⟨513455, by rfl⟩ : syracuseStep 2738429 = 1026911) (by norm_num)
theorem B2738453 : Blo 1825614 2738453 := bbase (se 6 (by rfl) ⟨64182, by rfl⟩ : syracuseStep 2738453 = 128365) (by norm_num)
theorem B3467549 : Blo 1825614 3467549 := bbase (se 3 (by rfl) ⟨650165, by rfl⟩ : syracuseStep 3467549 = 1300331) (by norm_num)
theorem B4622629 : Blo 1825614 4622629 := bbase (se 4 (by rfl) ⟨433371, by rfl⟩ : syracuseStep 4622629 = 866743) (by norm_num)
theorem B2312489 : Blo 1825614 2312489 := bbase (se 2 (by rfl) ⟨867183, by rfl⟩ : syracuseStep 2312489 = 1734367) (by norm_num)
theorem B2738477 : Blo 1825614 2738477 := bbase (se 3 (by rfl) ⟨513464, by rfl⟩ : syracuseStep 2738477 = 1026929) (by norm_num)
theorem B3082549 : Blo 1825614 3082549 := bbase (se 5 (by rfl) ⟨144494, by rfl⟩ : syracuseStep 3082549 = 288989) (by norm_num)
theorem B2738501 : Blo 1825614 2738501 := bbase (se 4 (by rfl) ⟨256734, by rfl⟩ : syracuseStep 2738501 = 513469) (by norm_num)
theorem B2468165 : Blo 1825614 2468165 := bbase (se 4 (by rfl) ⟨231390, by rfl⟩ : syracuseStep 2468165 = 462781) (by norm_num)
theorem B2738525 : Blo 1825614 2738525 := bbase (se 3 (by rfl) ⟨513473, by rfl⟩ : syracuseStep 2738525 = 1026947) (by norm_num)
theorem B2312545 : Blo 1825614 2312545 := bbase (se 2 (by rfl) ⟨867204, by rfl⟩ : syracuseStep 2312545 = 1734409) (by norm_num)
theorem B2738549 : Blo 1825614 2738549 := bbase (se 5 (by rfl) ⟨128369, by rfl⟩ : syracuseStep 2738549 = 256739) (by norm_num)
theorem B3123581 : Blo 1825614 3123581 := bbase (se 3 (by rfl) ⟨585671, by rfl⟩ : syracuseStep 3123581 = 1171343) (by norm_num)
theorem B2083205 : Blo 1825614 2083205 := bbase (se 4 (by rfl) ⟨195300, by rfl⟩ : syracuseStep 2083205 = 390601) (by norm_num)
theorem B2738573 : Blo 1825614 2738573 := bbase (se 3 (by rfl) ⟨513482, by rfl⟩ : syracuseStep 2738573 = 1026965) (by norm_num)
theorem B3082637 : Blo 1825614 3082637 := bbase (se 3 (by rfl) ⟨577994, by rfl⟩ : syracuseStep 3082637 = 1155989) (by norm_num)
theorem B4622741 : Blo 1825614 4622741 := bbase (se 6 (by rfl) ⟨108345, by rfl⟩ : syracuseStep 4622741 = 216691) (by norm_num)
theorem B5851541 : Blo 1825614 5851541 := bbase (se 6 (by rfl) ⟨137145, by rfl⟩ : syracuseStep 5851541 = 274291) (by norm_num)
theorem B2738597 : Blo 1825614 2738597 := bbase (se 4 (by rfl) ⟨256743, by rfl⟩ : syracuseStep 2738597 = 513487) (by norm_num)
theorem B3467701 : Blo 1825614 3467701 := bbase (se 5 (by rfl) ⟨162548, by rfl⟩ : syracuseStep 3467701 = 325097) (by norm_num)
theorem B2738621 : Blo 1825614 2738621 := bbase (se 3 (by rfl) ⟨513491, by rfl⟩ : syracuseStep 2738621 = 1026983) (by norm_num)
theorem B2312641 : Blo 1825614 2312641 := bbase (se 2 (by rfl) ⟨867240, by rfl⟩ : syracuseStep 2312641 = 1734481) (by norm_num)
theorem B2599381 : Blo 1825614 2599381 := bbase (se 7 (by rfl) ⟨30461, by rfl⟩ : syracuseStep 2599381 = 60923) (by norm_num)
theorem B2738645 : Blo 1825614 2738645 := bbase (se 7 (by rfl) ⟨32093, by rfl⟩ : syracuseStep 2738645 = 64187) (by norm_num)
theorem B2738669 : Blo 1825614 2738669 := bbase (se 3 (by rfl) ⟨513500, by rfl⟩ : syracuseStep 2738669 = 1027001) (by norm_num)
theorem B16665077 : Blo 1825614 16665077 := bbase (se 5 (by rfl) ⟨781175, by rfl⟩ : syracuseStep 16665077 = 1562351) (by norm_num)
theorem B2738693 : Blo 1825614 2738693 := bbase (se 4 (by rfl) ⟨256752, by rfl⟩ : syracuseStep 2738693 = 513505) (by norm_num)
theorem B9251333 : Blo 1825614 9251333 := bbase (se 4 (by rfl) ⟨867312, by rfl⟩ : syracuseStep 9251333 = 1734625) (by norm_num)
theorem B3082765 : Blo 1825614 3082765 := bbase (se 3 (by rfl) ⟨578018, by rfl⟩ : syracuseStep 3082765 = 1156037) (by norm_num)
theorem B6162965 : Blo 1825614 6162965 := bbase (se 6 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 6162965 = 288889) (by norm_num)
theorem B2738717 : Blo 1825614 2738717 := bbase (se 3 (by rfl) ⟨513509, by rfl⟩ : syracuseStep 2738717 = 1027019) (by norm_num)
theorem B2738741 : Blo 1825614 2738741 := bbase (se 5 (by rfl) ⟨128378, by rfl⟩ : syracuseStep 2738741 = 256757) (by norm_num)
theorem B2738765 : Blo 1825614 2738765 := bbase (se 3 (by rfl) ⟨513518, by rfl⟩ : syracuseStep 2738765 = 1027037) (by norm_num)
theorem B10005077 : Blo 1825614 10005077 := bbase (se 8 (by rfl) ⟨58623, by rfl⟩ : syracuseStep 10005077 = 117247) (by norm_num)
theorem B4622933 : Blo 1825614 4622933 := bbase (se 8 (by rfl) ⟨27087, by rfl⟩ : syracuseStep 4622933 = 54175) (by norm_num)
theorem B2738789 : Blo 1825614 2738789 := bbase (se 4 (by rfl) ⟨256761, by rfl⟩ : syracuseStep 2738789 = 513523) (by norm_num)
theorem B3082853 : Blo 1825614 3082853 := bbase (se 4 (by rfl) ⟨289017, by rfl⟩ : syracuseStep 3082853 = 578035) (by norm_num)
theorem B3902053 : Blo 1825614 3902053 := bbase (se 4 (by rfl) ⟨365817, by rfl⟩ : syracuseStep 3902053 = 731635) (by norm_num)
theorem B2312813 : Blo 1825614 2312813 := bbase (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) (by norm_num)
theorem B2738813 : Blo 1825614 2738813 := bbase (se 3 (by rfl) ⟨513527, by rfl⟩ : syracuseStep 2738813 = 1027055) (by norm_num)
theorem B2738837 : Blo 1825614 2738837 := bbase (se 6 (by rfl) ⟨64191, by rfl⟩ : syracuseStep 2738837 = 128383) (by norm_num)
theorem B2312869 : Blo 1825614 2312869 := bbase (se 4 (by rfl) ⟨216831, by rfl⟩ : syracuseStep 2312869 = 433663) (by norm_num)
theorem B2738861 : Blo 1825614 2738861 := bbase (se 3 (by rfl) ⟨513536, by rfl⟩ : syracuseStep 2738861 = 1027073) (by norm_num)
theorem B2738885 : Blo 1825614 2738885 := bbase (se 4 (by rfl) ⟨256770, by rfl⟩ : syracuseStep 2738885 = 513541) (by norm_num)
theorem B2738909 : Blo 1825614 2738909 := bbase (se 3 (by rfl) ⟨513545, by rfl⟩ : syracuseStep 2738909 = 1027091) (by norm_num)
theorem B3468005 : Blo 1825614 3468005 := bbase (se 4 (by rfl) ⟨325125, by rfl⟩ : syracuseStep 3468005 = 650251) (by norm_num)
theorem B3082981 : Blo 1825614 3082981 := bbase (se 4 (by rfl) ⟨289029, by rfl⟩ : syracuseStep 3082981 = 578059) (by norm_num)
theorem B2738933 : Blo 1825614 2738933 := bbase (se 5 (by rfl) ⟨128387, by rfl⟩ : syracuseStep 2738933 = 256775) (by norm_num)
theorem B2312965 : Blo 1825614 2312965 := bbase (se 4 (by rfl) ⟨216840, by rfl⟩ : syracuseStep 2312965 = 433681) (by norm_num)
theorem B2738957 : Blo 1825614 2738957 := bbase (se 3 (by rfl) ⟨513554, by rfl⟩ : syracuseStep 2738957 = 1027109) (by norm_num)
theorem B17795861 : Blo 1825614 17795861 := bbase (se 6 (by rfl) ⟨417090, by rfl⟩ : syracuseStep 17795861 = 834181) (by norm_num)
theorem B2599717 : Blo 1825614 2599717 := bbase (se 4 (by rfl) ⟨243723, by rfl⟩ : syracuseStep 2599717 = 487447) (by norm_num)
theorem B2738981 : Blo 1825614 2738981 := bbase (se 4 (by rfl) ⟨256779, by rfl⟩ : syracuseStep 2738981 = 513559) (by norm_num)
theorem B2739005 : Blo 1825614 2739005 := bbase (se 3 (by rfl) ⟨513563, by rfl⟩ : syracuseStep 2739005 = 1027127) (by norm_num)
theorem B3083069 : Blo 1825614 3083069 := bbase (se 3 (by rfl) ⟨578075, by rfl⟩ : syracuseStep 3083069 = 1156151) (by norm_num)
theorem B2739029 : Blo 1825614 2739029 := bbase (se 9 (by rfl) ⟨8024, by rfl⟩ : syracuseStep 2739029 = 16049) (by norm_num)
theorem B2739053 : Blo 1825614 2739053 := bbase (se 3 (by rfl) ⟨513572, by rfl⟩ : syracuseStep 2739053 = 1027145) (by norm_num)
theorem B2739077 : Blo 1825614 2739077 := bbase (se 4 (by rfl) ⟨256788, by rfl⟩ : syracuseStep 2739077 = 513577) (by norm_num)
theorem B6933397 : Blo 1825614 6933397 := bbase (se 6 (by rfl) ⟨162501, by rfl⟩ : syracuseStep 6933397 = 325003) (by norm_num)
theorem B2739101 : Blo 1825614 2739101 := bbase (se 3 (by rfl) ⟨513581, by rfl⟩ : syracuseStep 2739101 = 1027163) (by norm_num)
theorem B9243557 : Blo 1825614 9243557 := bbase (se 4 (by rfl) ⟨866583, by rfl⟩ : syracuseStep 9243557 = 1733167) (by norm_num)
theorem B4623277 : Blo 1825614 4623277 := bbase (se 3 (by rfl) ⟨866864, by rfl⟩ : syracuseStep 4623277 = 1733729) (by norm_num)
theorem B2739125 : Blo 1825614 2739125 := bbase (se 5 (by rfl) ⟨128396, by rfl⟩ : syracuseStep 2739125 = 256793) (by norm_num)
theorem B3083197 : Blo 1825614 3083197 := bbase (se 3 (by rfl) ⟨578099, by rfl⟩ : syracuseStep 3083197 = 1156199) (by norm_num)
theorem B6163397 : Blo 1825614 6163397 := bbase (se 4 (by rfl) ⟨577818, by rfl⟩ : syracuseStep 6163397 = 1155637) (by norm_num)
theorem B2739149 : Blo 1825614 2739149 := bbase (se 3 (by rfl) ⟨513590, by rfl⟩ : syracuseStep 2739149 = 1027181) (by norm_num)
theorem B2739173 : Blo 1825614 2739173 := bbase (se 4 (by rfl) ⟨256797, by rfl⟩ : syracuseStep 2739173 = 513595) (by norm_num)
theorem B11111413 : Blo 1825614 11111413 := bbase (se 5 (by rfl) ⟨520847, by rfl⟩ : syracuseStep 11111413 = 1041695) (by norm_num)
theorem B2599933 : Blo 1825614 2599933 := bbase (se 3 (by rfl) ⟨487487, by rfl⟩ : syracuseStep 2599933 = 974975) (by norm_num)
theorem B2739197 : Blo 1825614 2739197 := bbase (se 3 (by rfl) ⟨513599, by rfl⟩ : syracuseStep 2739197 = 1027199) (by norm_num)
theorem B2739221 : Blo 1825614 2739221 := bbase (se 6 (by rfl) ⟨64200, by rfl⟩ : syracuseStep 2739221 = 128401) (by norm_num)
theorem B3083285 : Blo 1825614 3083285 := bbase (se 6 (by rfl) ⟨72264, by rfl⟩ : syracuseStep 3083285 = 144529) (by norm_num)
theorem B4623389 : Blo 1825614 4623389 := bbase (se 3 (by rfl) ⟨866885, by rfl⟩ : syracuseStep 4623389 = 1733771) (by norm_num)
theorem B2739245 : Blo 1825614 2739245 := bbase (se 3 (by rfl) ⟨513608, by rfl⟩ : syracuseStep 2739245 = 1027217) (by norm_num)
theorem B2739269 : Blo 1825614 2739269 := bbase (se 4 (by rfl) ⟨256806, by rfl⟩ : syracuseStep 2739269 = 513613) (by norm_num)
theorem B2739293 : Blo 1825614 2739293 := bbase (se 3 (by rfl) ⟨513617, by rfl⟩ : syracuseStep 2739293 = 1027235) (by norm_num)
theorem B5270629 : Blo 1825614 5270629 := bbase (se 4 (by rfl) ⟨494121, by rfl⟩ : syracuseStep 5270629 = 988243) (by norm_num)
theorem B2739317 : Blo 1825614 2739317 := bbase (se 5 (by rfl) ⟨128405, by rfl⟩ : syracuseStep 2739317 = 256811) (by norm_num)
theorem B2739341 : Blo 1825614 2739341 := bbase (se 3 (by rfl) ⟨513626, by rfl⟩ : syracuseStep 2739341 = 1027253) (by norm_num)
theorem B3124373 : Blo 1825614 3124373 := bbase (se 6 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 3124373 = 146455) (by norm_num)
theorem B3083413 : Blo 1825614 3083413 := bbase (se 6 (by rfl) ⟨72267, by rfl⟩ : syracuseStep 3083413 = 144535) (by norm_num)
theorem B2739365 : Blo 1825614 2739365 := bbase (se 4 (by rfl) ⟨256815, by rfl⟩ : syracuseStep 2739365 = 513631) (by norm_num)
theorem B7802021 : Blo 1825614 7802021 := bbase (se 4 (by rfl) ⟨731439, by rfl⟩ : syracuseStep 7802021 = 1462879) (by norm_num)
theorem B2739389 : Blo 1825614 2739389 := bbase (se 3 (by rfl) ⟨513635, by rfl⟩ : syracuseStep 2739389 = 1027271) (by norm_num)
theorem B6933701 : Blo 1825614 6933701 := bbase (se 4 (by rfl) ⟨650034, by rfl⟩ : syracuseStep 6933701 = 1300069) (by norm_num)
theorem B2739413 : Blo 1825614 2739413 := bbase (se 7 (by rfl) ⟨32102, by rfl⟩ : syracuseStep 2739413 = 64205) (by norm_num)
theorem B4623581 : Blo 1825614 4623581 := bbase (se 3 (by rfl) ⟨866921, by rfl⟩ : syracuseStep 4623581 = 1733843) (by norm_num)
theorem B2739437 : Blo 1825614 2739437 := bbase (se 3 (by rfl) ⟨513644, by rfl⟩ : syracuseStep 2739437 = 1027289) (by norm_num)
theorem B3083501 : Blo 1825614 3083501 := bbase (se 3 (by rfl) ⟨578156, by rfl⟩ : syracuseStep 3083501 = 1156313) (by norm_num)
theorem B2739461 : Blo 1825614 2739461 := bbase (se 4 (by rfl) ⟨256824, by rfl⟩ : syracuseStep 2739461 = 513649) (by norm_num)
theorem B2739485 : Blo 1825614 2739485 := bbase (se 3 (by rfl) ⟨513653, by rfl⟩ : syracuseStep 2739485 = 1027307) (by norm_num)
theorem B4689181 : Blo 1825614 4689181 := bbase (se 3 (by rfl) ⟨879221, by rfl⟩ : syracuseStep 4689181 = 1758443) (by norm_num)
theorem B4164901 : Blo 1825614 4164901 := bbase (se 4 (by rfl) ⟨390459, by rfl⟩ : syracuseStep 4164901 = 780919) (by norm_num)
theorem B2739509 : Blo 1825614 2739509 := bbase (se 5 (by rfl) ⟨128414, by rfl⟩ : syracuseStep 2739509 = 256829) (by norm_num)
theorem B2739533 : Blo 1825614 2739533 := bbase (se 3 (by rfl) ⟨513662, by rfl⟩ : syracuseStep 2739533 = 1027325) (by norm_num)
theorem B2739557 : Blo 1825614 2739557 := bbase (se 4 (by rfl) ⟨256833, by rfl⟩ : syracuseStep 2739557 = 513667) (by norm_num)
theorem B3083629 : Blo 1825614 3083629 := bbase (se 3 (by rfl) ⟨578180, by rfl⟩ : syracuseStep 3083629 = 1156361) (by norm_num)
theorem B2600309 : Blo 1825614 2600309 := bbase (se 5 (by rfl) ⟨121889, by rfl⟩ : syracuseStep 2600309 = 243779) (by norm_num)
theorem B6163829 : Blo 1825614 6163829 := bbase (se 5 (by rfl) ⟨288929, by rfl⟩ : syracuseStep 6163829 = 577859) (by norm_num)
theorem B2739581 : Blo 1825614 2739581 := bbase (se 3 (by rfl) ⟨513671, by rfl⟩ : syracuseStep 2739581 = 1027343) (by norm_num)
theorem B4107653 : Blo 1825614 4107653 := bbase (se 4 (by rfl) ⟨385092, by rfl⟩ : syracuseStep 4107653 = 770185) (by norm_num)
theorem B2739605 : Blo 1825614 2739605 := bbase (se 6 (by rfl) ⟨64209, by rfl⟩ : syracuseStep 2739605 = 128419) (by norm_num)
theorem B2739629 : Blo 1825614 2739629 := bbase (se 3 (by rfl) ⟨513680, by rfl⟩ : syracuseStep 2739629 = 1027361) (by norm_num)
theorem B2739653 : Blo 1825614 2739653 := bbase (se 4 (by rfl) ⟨256842, by rfl⟩ : syracuseStep 2739653 = 513685) (by norm_num)
theorem B3083717 : Blo 1825614 3083717 := bbase (se 4 (by rfl) ⟨289098, by rfl⟩ : syracuseStep 3083717 = 578197) (by norm_num)
theorem B4107725 : Blo 1825614 4107725 := bbase (se 3 (by rfl) ⟨770198, by rfl⟩ : syracuseStep 4107725 = 1540397) (by norm_num)
theorem B3468757 : Blo 1825614 3468757 := bbase (se 7 (by rfl) ⟨40649, by rfl⟩ : syracuseStep 3468757 = 81299) (by norm_num)
theorem B2739677 : Blo 1825614 2739677 := bbase (se 3 (by rfl) ⟨513689, by rfl⟩ : syracuseStep 2739677 = 1027379) (by norm_num)
theorem B3902941 : Blo 1825614 3902941 := bbase (se 3 (by rfl) ⟨731801, by rfl⟩ : syracuseStep 3902941 = 1463603) (by norm_num)
theorem B5852645 : Blo 1825614 5852645 := bbase (se 4 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 5852645 = 1097371) (by norm_num)
theorem B2739701 : Blo 1825614 2739701 := bbase (se 5 (by rfl) ⟨128423, by rfl⟩ : syracuseStep 2739701 = 256847) (by norm_num)
theorem B2739725 : Blo 1825614 2739725 := bbase (se 3 (by rfl) ⟨513698, by rfl⟩ : syracuseStep 2739725 = 1027397) (by norm_num)
theorem B4107797 : Blo 1825614 4107797 := bbase (se 6 (by rfl) ⟨96276, by rfl⟩ : syracuseStep 4107797 = 192553) (by norm_num)
theorem B2739749 : Blo 1825614 2739749 := bbase (se 4 (by rfl) ⟨256851, by rfl⟩ : syracuseStep 2739749 = 513703) (by norm_num)
theorem B4623925 : Blo 1825614 4623925 := bbase (se 5 (by rfl) ⟨216746, by rfl⟩ : syracuseStep 4623925 = 433493) (by norm_num)
theorem B2739773 : Blo 1825614 2739773 := bbase (se 3 (by rfl) ⟨513707, by rfl⟩ : syracuseStep 2739773 = 1027415) (by norm_num)
theorem B3083845 : Blo 1825614 3083845 := bbase (se 4 (by rfl) ⟨289110, by rfl⟩ : syracuseStep 3083845 = 578221) (by norm_num)
theorem B2739797 : Blo 1825614 2739797 := bbase (se 8 (by rfl) ⟨16053, by rfl⟩ : syracuseStep 2739797 = 32107) (by norm_num)
theorem B3903061 : Blo 1825614 3903061 := bbase (se 8 (by rfl) ⟨22869, by rfl⟩ : syracuseStep 3903061 = 45739) (by norm_num)
theorem B4107869 : Blo 1825614 4107869 := bbase (se 3 (by rfl) ⟨770225, by rfl⟩ : syracuseStep 4107869 = 1540451) (by norm_num)
theorem B3468901 : Blo 1825614 3468901 := bbase (se 4 (by rfl) ⟨325209, by rfl⟩ : syracuseStep 3468901 = 650419) (by norm_num)
theorem B2739821 : Blo 1825614 2739821 := bbase (se 3 (by rfl) ⟨513716, by rfl⟩ : syracuseStep 2739821 = 1027433) (by norm_num)
theorem B2739845 : Blo 1825614 2739845 := bbase (se 4 (by rfl) ⟨256860, by rfl⟩ : syracuseStep 2739845 = 513721) (by norm_num)
theorem B13168277 : Blo 1825614 13168277 := bbase (se 6 (by rfl) ⟨308631, by rfl⟩ : syracuseStep 13168277 = 617263) (by norm_num)
theorem B2739869 : Blo 1825614 2739869 := bbase (se 3 (by rfl) ⟨513725, by rfl⟩ : syracuseStep 2739869 = 1027451) (by norm_num)
theorem B3083933 : Blo 1825614 3083933 := bbase (se 3 (by rfl) ⟨578237, by rfl⟩ : syracuseStep 3083933 = 1156475) (by norm_num)
theorem B4107941 : Blo 1825614 4107941 := bbase (se 4 (by rfl) ⟨385119, by rfl⟩ : syracuseStep 4107941 = 770239) (by norm_num)
theorem B4624037 : Blo 1825614 4624037 := bbase (se 4 (by rfl) ⟨433503, by rfl⟩ : syracuseStep 4624037 = 867007) (by norm_num)
theorem B2739893 : Blo 1825614 2739893 := bbase (se 5 (by rfl) ⟨128432, by rfl⟩ : syracuseStep 2739893 = 256865) (by norm_num)
theorem B9875125 : Blo 1825614 9875125 := bbase (se 5 (by rfl) ⟨462896, by rfl⟩ : syracuseStep 9875125 = 925793) (by norm_num)
theorem B2739917 : Blo 1825614 2739917 := bbase (se 3 (by rfl) ⟨513734, by rfl⟩ : syracuseStep 2739917 = 1027469) (by norm_num)
theorem B8335061 : Blo 1825614 8335061 := bbase (se 7 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 8335061 = 195353) (by norm_num)
theorem B2739941 : Blo 1825614 2739941 := bbase (se 4 (by rfl) ⟨256869, by rfl⟩ : syracuseStep 2739941 = 513739) (by norm_num)
theorem B4108013 : Blo 1825614 4108013 := bbase (se 3 (by rfl) ⟨770252, by rfl⟩ : syracuseStep 4108013 = 1540505) (by norm_num)
theorem B6582005 : Blo 1825614 6582005 := bbase (se 5 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 6582005 = 617063) (by norm_num)
theorem B2739965 : Blo 1825614 2739965 := bbase (se 3 (by rfl) ⟨513743, by rfl⟩ : syracuseStep 2739965 = 1027487) (by norm_num)
theorem B3469061 : Blo 1825614 3469061 := bbase (se 4 (by rfl) ⟨325224, by rfl⟩ : syracuseStep 3469061 = 650449) (by norm_num)
theorem B2739989 : Blo 1825614 2739989 := bbase (se 6 (by rfl) ⟨64218, by rfl⟩ : syracuseStep 2739989 = 128437) (by norm_num)
theorem B3084061 : Blo 1825614 3084061 := bbase (se 3 (by rfl) ⟨578261, by rfl⟩ : syracuseStep 3084061 = 1156523) (by norm_num)
theorem B6164261 : Blo 1825614 6164261 := bbase (se 4 (by rfl) ⟨577899, by rfl⟩ : syracuseStep 6164261 = 1155799) (by norm_num)
theorem B2740013 : Blo 1825614 2740013 := bbase (se 3 (by rfl) ⟨513752, by rfl⟩ : syracuseStep 2740013 = 1027505) (by norm_num)
theorem B4108085 : Blo 1825614 4108085 := bbase (se 5 (by rfl) ⟨192566, by rfl⟩ : syracuseStep 4108085 = 385133) (by norm_num)
theorem B2740037 : Blo 1825614 2740037 := bbase (se 4 (by rfl) ⟨256878, by rfl⟩ : syracuseStep 2740037 = 513757) (by norm_num)
theorem B4935509 : Blo 1825614 4935509 := bbase (se 9 (by rfl) ⟨14459, by rfl⟩ : syracuseStep 4935509 = 28919) (by norm_num)
theorem B2740061 : Blo 1825614 2740061 := bbase (se 3 (by rfl) ⟨513761, by rfl⟩ : syracuseStep 2740061 = 1027523) (by norm_num)
theorem B4624229 : Blo 1825614 4624229 := bbase (se 4 (by rfl) ⟨433521, by rfl⟩ : syracuseStep 4624229 = 867043) (by norm_num)
theorem B2740085 : Blo 1825614 2740085 := bbase (se 5 (by rfl) ⟨128441, by rfl⟩ : syracuseStep 2740085 = 256883) (by norm_num)
theorem B10407797 : Blo 1825614 10407797 := bbase (se 5 (by rfl) ⟨487865, by rfl⟩ : syracuseStep 10407797 = 975731) (by norm_num)
theorem B4108157 : Blo 1825614 4108157 := bbase (se 3 (by rfl) ⟨770279, by rfl⟩ : syracuseStep 4108157 = 1540559) (by norm_num)
theorem B2740109 : Blo 1825614 2740109 := bbase (se 3 (by rfl) ⟨513770, by rfl⟩ : syracuseStep 2740109 = 1027541) (by norm_num)
theorem B3469205 : Blo 1825614 3469205 := bbase (se 6 (by rfl) ⟨81309, by rfl⟩ : syracuseStep 3469205 = 162619) (by norm_num)
theorem B2740133 : Blo 1825614 2740133 := bbase (se 4 (by rfl) ⟨256887, by rfl⟩ : syracuseStep 2740133 = 513775) (by norm_num)
theorem B2740157 : Blo 1825614 2740157 := bbase (se 3 (by rfl) ⟨513779, by rfl⟩ : syracuseStep 2740157 = 1027559) (by norm_num)
theorem B4108229 : Blo 1825614 4108229 := bbase (se 4 (by rfl) ⟨385146, by rfl⟩ : syracuseStep 4108229 = 770293) (by norm_num)
theorem B4386773 : Blo 1825614 4386773 := bbase (se 7 (by rfl) ⟨51407, by rfl⟩ : syracuseStep 4386773 = 102815) (by norm_num)
theorem B2740181 : Blo 1825614 2740181 := bbase (se 7 (by rfl) ⟨32111, by rfl⟩ : syracuseStep 2740181 = 64223) (by norm_num)
theorem B2740205 : Blo 1825614 2740205 := bbase (se 3 (by rfl) ⟨513788, by rfl⟩ : syracuseStep 2740205 = 1027577) (by norm_num)
theorem B2740229 : Blo 1825614 2740229 := bbase (se 4 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 2740229 = 513793) (by norm_num)
theorem B4108301 : Blo 1825614 4108301 := bbase (se 3 (by rfl) ⟨770306, by rfl⟩ : syracuseStep 4108301 = 1540613) (by norm_num)
theorem B21082133 : Blo 1825614 21082133 := bbase (se 6 (by rfl) ⟨494112, by rfl⟩ : syracuseStep 21082133 = 988225) (by norm_num)
theorem B6582293 : Blo 1825614 6582293 := bbase (se 6 (by rfl) ⟨154272, by rfl⟩ : syracuseStep 6582293 = 308545) (by norm_num)
theorem B2740253 : Blo 1825614 2740253 := bbase (se 3 (by rfl) ⟨513797, by rfl⟩ : syracuseStep 2740253 = 1027595) (by norm_num)
theorem B2740277 : Blo 1825614 2740277 := bbase (se 5 (by rfl) ⟨128450, by rfl⟩ : syracuseStep 2740277 = 256901) (by norm_num)
theorem B2740301 : Blo 1825614 2740301 := bbase (se 3 (by rfl) ⟨513806, by rfl⟩ : syracuseStep 2740301 = 1027613) (by norm_num)
theorem B4108373 : Blo 1825614 4108373 := bbase (se 8 (by rfl) ⟨24072, by rfl⟩ : syracuseStep 4108373 = 48145) (by norm_num)
theorem B4386917 : Blo 1825614 4386917 := bbase (se 4 (by rfl) ⟨411273, by rfl⟩ : syracuseStep 4386917 = 822547) (by norm_num)
theorem B2740325 : Blo 1825614 2740325 := bbase (se 4 (by rfl) ⟨256905, by rfl⟩ : syracuseStep 2740325 = 513811) (by norm_num)
theorem B2740349 : Blo 1825614 2740349 := bbase (se 3 (by rfl) ⟨513815, by rfl⟩ : syracuseStep 2740349 = 1027631) (by norm_num)
theorem B2740373 : Blo 1825614 2740373 := bbase (se 6 (by rfl) ⟨64227, by rfl⟩ : syracuseStep 2740373 = 128455) (by norm_num)
theorem B4108445 : Blo 1825614 4108445 := bbase (se 3 (by rfl) ⟨770333, by rfl⟩ : syracuseStep 4108445 = 1540667) (by norm_num)
theorem B2740397 : Blo 1825614 2740397 := bbase (se 3 (by rfl) ⟨513824, by rfl⟩ : syracuseStep 2740397 = 1027649) (by norm_num)
theorem B9244853 : Blo 1825614 9244853 := bbase (se 5 (by rfl) ⟨433352, by rfl⟩ : syracuseStep 9244853 = 866705) (by norm_num)
theorem B3469493 : Blo 1825614 3469493 := bbase (se 5 (by rfl) ⟨162632, by rfl⟩ : syracuseStep 3469493 = 325265) (by norm_num)
theorem B4624573 : Blo 1825614 4624573 := bbase (se 3 (by rfl) ⟨867107, by rfl⟩ : syracuseStep 4624573 = 1734215) (by norm_num)
theorem B2740421 : Blo 1825614 2740421 := bbase (se 4 (by rfl) ⟨256914, by rfl⟩ : syracuseStep 2740421 = 513829) (by norm_num)
theorem B6164693 : Blo 1825614 6164693 := bbase (se 7 (by rfl) ⟨72242, by rfl⟩ : syracuseStep 6164693 = 144485) (by norm_num)
theorem B2740445 : Blo 1825614 2740445 := bbase (se 3 (by rfl) ⟨513833, by rfl⟩ : syracuseStep 2740445 = 1027667) (by norm_num)
theorem B4108517 : Blo 1825614 4108517 := bbase (se 4 (by rfl) ⟨385173, by rfl⟩ : syracuseStep 4108517 = 770347) (by norm_num)
theorem B2740469 : Blo 1825614 2740469 := bbase (se 5 (by rfl) ⟨128459, by rfl⟩ : syracuseStep 2740469 = 256919) (by norm_num)
theorem B2740493 : Blo 1825614 2740493 := bbase (se 3 (by rfl) ⟨513842, by rfl⟩ : syracuseStep 2740493 = 1027685) (by norm_num)
theorem B2740517 : Blo 1825614 2740517 := bbase (se 4 (by rfl) ⟨256923, by rfl⟩ : syracuseStep 2740517 = 513847) (by norm_num)
theorem B4108589 : Blo 1825614 4108589 := bbase (se 3 (by rfl) ⟨770360, by rfl⟩ : syracuseStep 4108589 = 1540721) (by norm_num)
theorem B4624685 : Blo 1825614 4624685 := bbase (se 3 (by rfl) ⟨867128, by rfl⟩ : syracuseStep 4624685 = 1734257) (by norm_num)
theorem B2740541 : Blo 1825614 2740541 := bbase (se 3 (by rfl) ⟨513851, by rfl⟩ : syracuseStep 2740541 = 1027703) (by norm_num)
theorem B2740565 : Blo 1825614 2740565 := bbase (se 10 (by rfl) ⟨4014, by rfl⟩ : syracuseStep 2740565 = 8029) (by norm_num)
theorem B2740589 : Blo 1825614 2740589 := bbase (se 3 (by rfl) ⟨513860, by rfl⟩ : syracuseStep 2740589 = 1027721) (by norm_num)
theorem B4108661 : Blo 1825614 4108661 := bbase (se 5 (by rfl) ⟨192593, by rfl⟩ : syracuseStep 4108661 = 385187) (by norm_num)
theorem B2740613 : Blo 1825614 2740613 := bbase (se 4 (by rfl) ⟨256932, by rfl⟩ : syracuseStep 2740613 = 513865) (by norm_num)
theorem B2740637 : Blo 1825614 2740637 := bbase (se 3 (by rfl) ⟨513869, by rfl⟩ : syracuseStep 2740637 = 1027739) (by norm_num)
theorem B2740661 : Blo 1825614 2740661 := bbase (se 5 (by rfl) ⟨128468, by rfl⟩ : syracuseStep 2740661 = 256937) (by norm_num)
theorem B4108733 : Blo 1825614 4108733 := bbase (se 3 (by rfl) ⟨770387, by rfl⟩ : syracuseStep 4108733 = 1540775) (by norm_num)
theorem B2740685 : Blo 1825614 2740685 := bbase (se 3 (by rfl) ⟨513878, by rfl⟩ : syracuseStep 2740685 = 1027757) (by norm_num)
theorem B2740709 : Blo 1825614 2740709 := bbase (se 4 (by rfl) ⟨256941, by rfl⟩ : syracuseStep 2740709 = 513883) (by norm_num)
theorem B4624877 : Blo 1825614 4624877 := bbase (se 3 (by rfl) ⟨867164, by rfl⟩ : syracuseStep 4624877 = 1734329) (by norm_num)
theorem B2740733 : Blo 1825614 2740733 := bbase (se 3 (by rfl) ⟨513887, by rfl⟩ : syracuseStep 2740733 = 1027775) (by norm_num)
theorem B4108805 : Blo 1825614 4108805 := bbase (se 4 (by rfl) ⟨385200, by rfl⟩ : syracuseStep 4108805 = 770401) (by norm_num)
theorem B2740757 : Blo 1825614 2740757 := bbase (se 6 (by rfl) ⟨64236, by rfl⟩ : syracuseStep 2740757 = 128473) (by norm_num)
theorem B2740781 : Blo 1825614 2740781 := bbase (se 3 (by rfl) ⟨513896, by rfl⟩ : syracuseStep 2740781 = 1027793) (by norm_num)
theorem B2740805 : Blo 1825614 2740805 := bbase (se 4 (by rfl) ⟨256950, by rfl⟩ : syracuseStep 2740805 = 513901) (by norm_num)
theorem B4108877 : Blo 1825614 4108877 := bbase (se 3 (by rfl) ⟨770414, by rfl⟩ : syracuseStep 4108877 = 1540829) (by norm_num)
theorem B2740829 : Blo 1825614 2740829 := bbase (se 3 (by rfl) ⟨513905, by rfl⟩ : syracuseStep 2740829 = 1027811) (by norm_num)
theorem B2740853 : Blo 1825614 2740853 := bbase (se 5 (by rfl) ⟨128477, by rfl⟩ : syracuseStep 2740853 = 256955) (by norm_num)
theorem B6165125 : Blo 1825614 6165125 := bbase (se 4 (by rfl) ⟨577980, by rfl⟩ : syracuseStep 6165125 = 1155961) (by norm_num)
theorem B2740877 : Blo 1825614 2740877 := bbase (se 3 (by rfl) ⟨513914, by rfl⟩ : syracuseStep 2740877 = 1027829) (by norm_num)
theorem B4108949 : Blo 1825614 4108949 := bbase (se 6 (by rfl) ⟨96303, by rfl⟩ : syracuseStep 4108949 = 192607) (by norm_num)
theorem B2740901 : Blo 1825614 2740901 := bbase (se 4 (by rfl) ⟨256959, by rfl⟩ : syracuseStep 2740901 = 513919) (by norm_num)
theorem B2740925 : Blo 1825614 2740925 := bbase (se 3 (by rfl) ⟨513923, by rfl⟩ : syracuseStep 2740925 = 1027847) (by norm_num)
theorem B2740949 : Blo 1825614 2740949 := bbase (se 7 (by rfl) ⟨32120, by rfl⟩ : syracuseStep 2740949 = 64241) (by norm_num)
theorem B4109021 : Blo 1825614 4109021 := bbase (se 3 (by rfl) ⟨770441, by rfl⟩ : syracuseStep 4109021 = 1540883) (by norm_num)
theorem B2740973 : Blo 1825614 2740973 := bbase (se 3 (by rfl) ⟨513932, by rfl⟩ : syracuseStep 2740973 = 1027865) (by norm_num)
theorem B2601733 : Blo 1825614 2601733 := bbase (se 4 (by rfl) ⟨243912, by rfl⟩ : syracuseStep 2601733 = 487825) (by norm_num)
theorem B2740997 : Blo 1825614 2740997 := bbase (se 4 (by rfl) ⟨256968, by rfl⟩ : syracuseStep 2740997 = 513937) (by norm_num)
theorem B2741021 : Blo 1825614 2741021 := bbase (se 3 (by rfl) ⟨513941, by rfl⟩ : syracuseStep 2741021 = 1027883) (by norm_num)
theorem B4109093 : Blo 1825614 4109093 := bbase (se 4 (by rfl) ⟨385227, by rfl⟩ : syracuseStep 4109093 = 770455) (by norm_num)
theorem B2741045 : Blo 1825614 2741045 := bbase (se 5 (by rfl) ⟨128486, by rfl⟩ : syracuseStep 2741045 = 256973) (by norm_num)
theorem B4625221 : Blo 1825614 4625221 := bbase (se 4 (by rfl) ⟨433614, by rfl⟩ : syracuseStep 4625221 = 867229) (by norm_num)
theorem B2741069 : Blo 1825614 2741069 := bbase (se 3 (by rfl) ⟨513950, by rfl⟩ : syracuseStep 2741069 = 1027901) (by norm_num)
theorem B2741093 : Blo 1825614 2741093 := bbase (se 4 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 2741093 = 513955) (by norm_num)
theorem B4109165 : Blo 1825614 4109165 := bbase (se 3 (by rfl) ⟨770468, by rfl⟩ : syracuseStep 4109165 = 1540937) (by norm_num)
theorem B3126125 : Blo 1825614 3126125 := bbase (se 3 (by rfl) ⟨586148, by rfl⟩ : syracuseStep 3126125 = 1172297) (by norm_num)
theorem B2003837 : Blo 1825614 2003837 := bbase (se 3 (by rfl) ⟨375719, by rfl⟩ : syracuseStep 2003837 = 751439) (by norm_num)
theorem B2741117 : Blo 1825614 2741117 := bbase (se 3 (by rfl) ⟨513959, by rfl⟩ : syracuseStep 2741117 = 1027919) (by norm_num)
theorem B2503549 : Blo 1825614 2503549 := bbase (se 3 (by rfl) ⟨469415, by rfl⟩ : syracuseStep 2503549 = 938831) (by norm_num)
theorem B2741141 : Blo 1825614 2741141 := bbase (se 6 (by rfl) ⟨64245, by rfl⟩ : syracuseStep 2741141 = 128491) (by norm_num)
theorem B2741165 : Blo 1825614 2741165 := bbase (se 3 (by rfl) ⟨513968, by rfl⟩ : syracuseStep 2741165 = 1027937) (by norm_num)
theorem B4109237 : Blo 1825614 4109237 := bbase (se 5 (by rfl) ⟨192620, by rfl⟩ : syracuseStep 4109237 = 385241) (by norm_num)
theorem B14062517 : Blo 1825614 14062517 := bbase (se 5 (by rfl) ⟨659180, by rfl⟩ : syracuseStep 14062517 = 1318361) (by norm_num)
theorem B4625333 : Blo 1825614 4625333 := bbase (se 5 (by rfl) ⟨216812, by rfl⟩ : syracuseStep 4625333 = 433625) (by norm_num)
theorem B2741189 : Blo 1825614 2741189 := bbase (se 4 (by rfl) ⟨256986, by rfl⟩ : syracuseStep 2741189 = 513973) (by norm_num)
theorem B11105237 : Blo 1825614 11105237 := bbase (se 7 (by rfl) ⟨130139, by rfl⟩ : syracuseStep 11105237 = 260279) (by norm_num)
theorem B2741213 : Blo 1825614 2741213 := bbase (se 3 (by rfl) ⟨513977, by rfl⟩ : syracuseStep 2741213 = 1027955) (by norm_num)
theorem B2741237 : Blo 1825614 2741237 := bbase (se 5 (by rfl) ⟨128495, by rfl⟩ : syracuseStep 2741237 = 256991) (by norm_num)
theorem B4109309 : Blo 1825614 4109309 := bbase (se 3 (by rfl) ⟨770495, by rfl⟩ : syracuseStep 4109309 = 1540991) (by norm_num)
theorem B2741261 : Blo 1825614 2741261 := bbase (se 3 (by rfl) ⟨513986, by rfl⟩ : syracuseStep 2741261 = 1027973) (by norm_num)
theorem B8778773 : Blo 1825614 8778773 := bbase (se 6 (by rfl) ⟨205752, by rfl⟩ : syracuseStep 8778773 = 411505) (by norm_num)
theorem B2741285 : Blo 1825614 2741285 := bbase (se 4 (by rfl) ⟨256995, by rfl⟩ : syracuseStep 2741285 = 513991) (by norm_num)
theorem B7402549 : Blo 1825614 7402549 := bbase (se 5 (by rfl) ⟨346994, by rfl⟩ : syracuseStep 7402549 = 693989) (by norm_num)
theorem B6165557 : Blo 1825614 6165557 := bbase (se 5 (by rfl) ⟨289010, by rfl⟩ : syracuseStep 6165557 = 578021) (by norm_num)
theorem B2741309 : Blo 1825614 2741309 := bbase (se 3 (by rfl) ⟨513995, by rfl⟩ : syracuseStep 2741309 = 1027991) (by norm_num)
theorem B4109381 : Blo 1825614 4109381 := bbase (se 4 (by rfl) ⟨385254, by rfl⟩ : syracuseStep 4109381 = 770509) (by norm_num)
theorem B13169749 : Blo 1825614 13169749 := bbase (se 8 (by rfl) ⟨77166, by rfl⟩ : syracuseStep 13169749 = 154333) (by norm_num)
theorem B2741333 : Blo 1825614 2741333 := bbase (se 8 (by rfl) ⟨16062, by rfl⟩ : syracuseStep 2741333 = 32125) (by norm_num)
theorem B2741357 : Blo 1825614 2741357 := bbase (se 3 (by rfl) ⟨514004, by rfl⟩ : syracuseStep 2741357 = 1028009) (by norm_num)
theorem B4625525 : Blo 1825614 4625525 := bbase (se 5 (by rfl) ⟨216821, by rfl⟩ : syracuseStep 4625525 = 433643) (by norm_num)
theorem B2741381 : Blo 1825614 2741381 := bbase (se 4 (by rfl) ⟨257004, by rfl⟩ : syracuseStep 2741381 = 514009) (by norm_num)
theorem B4109453 : Blo 1825614 4109453 := bbase (se 3 (by rfl) ⟨770522, by rfl⟩ : syracuseStep 4109453 = 1541045) (by norm_num)
theorem B20812949 : Blo 1825614 20812949 := bbase (se 6 (by rfl) ⟨487803, by rfl⟩ : syracuseStep 20812949 = 975607) (by norm_num)
theorem B2741405 : Blo 1825614 2741405 := bbase (se 3 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 2741405 = 1028027) (by norm_num)
theorem B4109525 : Blo 1825614 4109525 := bbase (se 7 (by rfl) ⟨48158, by rfl⟩ : syracuseStep 4109525 = 96317) (by norm_num)
theorem B6935813 : Blo 1825614 6935813 := bbase (se 4 (by rfl) ⟨650232, by rfl⟩ : syracuseStep 6935813 = 1300465) (by norm_num)
theorem B4109597 : Blo 1825614 4109597 := bbase (se 3 (by rfl) ⟨770549, by rfl⟩ : syracuseStep 4109597 = 1541099) (by norm_num)
theorem B25335125 : Blo 1825614 25335125 := bbase (se 14 (by rfl) ⟨2319, by rfl⟩ : syracuseStep 25335125 = 4639) (by norm_num)
theorem B4109669 : Blo 1825614 4109669 := bbase (se 4 (by rfl) ⟨385281, by rfl⟩ : syracuseStep 4109669 = 770563) (by norm_num)
theorem B5854565 : Blo 1825614 5854565 := bbase (se 4 (by rfl) ⟨548865, by rfl⟩ : syracuseStep 5854565 = 1097731) (by norm_num)
theorem B2225569 : Blo 1825614 2225569 := bbase (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) (by norm_num)
theorem B4109741 : Blo 1825614 4109741 := bbase (se 3 (by rfl) ⟨770576, by rfl⟩ : syracuseStep 4109741 = 1541153) (by norm_num)
theorem B9246149 : Blo 1825614 9246149 := bbase (se 4 (by rfl) ⟨866826, by rfl⟩ : syracuseStep 9246149 = 1733653) (by norm_num)
theorem B4625869 : Blo 1825614 4625869 := bbase (se 3 (by rfl) ⟨867350, by rfl⟩ : syracuseStep 4625869 = 1734701) (by norm_num)
theorem B6165989 : Blo 1825614 6165989 := bbase (se 4 (by rfl) ⟨578061, by rfl⟩ : syracuseStep 6165989 = 1156123) (by norm_num)
theorem B4109813 : Blo 1825614 4109813 := bbase (se 5 (by rfl) ⟨192647, by rfl⟩ : syracuseStep 4109813 = 385295) (by norm_num)
theorem B5199365 : Blo 1825614 5199365 := bbase (se 4 (by rfl) ⟨487440, by rfl⟩ : syracuseStep 5199365 = 974881) (by norm_num)
theorem B6936101 : Blo 1825614 6936101 := bbase (se 4 (by rfl) ⟨650259, by rfl⟩ : syracuseStep 6936101 = 1300519) (by norm_num)
theorem B4109885 : Blo 1825614 4109885 := bbase (se 3 (by rfl) ⟨770603, by rfl⟩ : syracuseStep 4109885 = 1541207) (by norm_num)
theorem B4625981 : Blo 1825614 4625981 := bbase (se 3 (by rfl) ⟨867371, by rfl⟩ : syracuseStep 4625981 = 1734743) (by norm_num)
theorem B31217237 : Blo 1825614 31217237 := bbase (se 8 (by rfl) ⟨182913, by rfl⟩ : syracuseStep 31217237 = 365827) (by norm_num)
theorem B4109957 : Blo 1825614 4109957 := bbase (se 4 (by rfl) ⟨385308, by rfl⟩ : syracuseStep 4109957 = 770617) (by norm_num)
theorem B4110029 : Blo 1825614 4110029 := bbase (se 3 (by rfl) ⟨770630, by rfl⟩ : syracuseStep 4110029 = 1541261) (by norm_num)
theorem B64149205 : Blo 1825614 64149205 := bbase (se 7 (by rfl) ⟨751748, by rfl⟩ : syracuseStep 64149205 = 1503497) (by norm_num)
theorem B2053849 : Blo 1825614 2053849 := bbase (se 2 (by rfl) ⟨770193, by rfl⟩ : syracuseStep 2053849 = 1540387) (by norm_num)
theorem B2053885 : Blo 1825614 2053885 := bbase (se 3 (by rfl) ⟨385103, by rfl⟩ : syracuseStep 2053885 = 770207) (by norm_num)
theorem B4110101 : Blo 1825614 4110101 := bbase (se 6 (by rfl) ⟨96330, by rfl⟩ : syracuseStep 4110101 = 192661) (by norm_num)
theorem B2053921 : Blo 1825614 2053921 := bbase (se 2 (by rfl) ⟨770220, by rfl⟩ : syracuseStep 2053921 = 1540441) (by norm_num)
theorem B2053957 : Blo 1825614 2053957 := bbase (se 4 (by rfl) ⟨192558, by rfl⟩ : syracuseStep 2053957 = 385117) (by norm_num)
theorem B4110173 : Blo 1825614 4110173 := bbase (se 3 (by rfl) ⟨770657, by rfl⟩ : syracuseStep 4110173 = 1541315) (by norm_num)
theorem B2053993 : Blo 1825614 2053993 := bbase (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) (by norm_num)
theorem B2054029 : Blo 1825614 2054029 := bbase (se 3 (by rfl) ⟨385130, by rfl⟩ : syracuseStep 2054029 = 770261) (by norm_num)
theorem B6166421 : Blo 1825614 6166421 := bbase (se 6 (by rfl) ⟨144525, by rfl⟩ : syracuseStep 6166421 = 289051) (by norm_num)
theorem B4110245 : Blo 1825614 4110245 := bbase (se 4 (by rfl) ⟨385335, by rfl⟩ : syracuseStep 4110245 = 770671) (by norm_num)
theorem B2054065 : Blo 1825614 2054065 := bbase (se 2 (by rfl) ⟨770274, by rfl⟩ : syracuseStep 2054065 = 1540549) (by norm_num)
theorem B2054101 : Blo 1825614 2054101 := bbase (se 7 (by rfl) ⟨24071, by rfl⟩ : syracuseStep 2054101 = 48143) (by norm_num)
theorem B4110317 : Blo 1825614 4110317 := bbase (se 3 (by rfl) ⟨770684, by rfl⟩ : syracuseStep 4110317 = 1541369) (by norm_num)
theorem B2054137 : Blo 1825614 2054137 := bbase (se 2 (by rfl) ⟨770301, by rfl⟩ : syracuseStep 2054137 = 1540603) (by norm_num)
theorem B5273605 : Blo 1825614 5273605 := bbase (se 4 (by rfl) ⟨494400, by rfl⟩ : syracuseStep 5273605 = 988801) (by norm_num)
theorem B2193421 : Blo 1825614 2193421 := bbase (se 3 (by rfl) ⟨411266, by rfl⟩ : syracuseStep 2193421 = 822533) (by norm_num)
theorem B2054173 : Blo 1825614 2054173 := bbase (se 3 (by rfl) ⟨385157, by rfl⟩ : syracuseStep 2054173 = 770315) (by norm_num)
theorem B4388917 : Blo 1825614 4388917 := bbase (se 5 (by rfl) ⟨205730, by rfl⟩ : syracuseStep 4388917 = 411461) (by norm_num)
theorem B4110389 : Blo 1825614 4110389 := bbase (se 5 (by rfl) ⟨192674, by rfl⟩ : syracuseStep 4110389 = 385349) (by norm_num)
theorem B2054209 : Blo 1825614 2054209 := bbase (se 2 (by rfl) ⟨770328, by rfl⟩ : syracuseStep 2054209 = 1540657) (by norm_num)
theorem B2054245 : Blo 1825614 2054245 := bbase (se 4 (by rfl) ⟨192585, by rfl⟩ : syracuseStep 2054245 = 385171) (by norm_num)
theorem B4110461 : Blo 1825614 4110461 := bbase (se 3 (by rfl) ⟨770711, by rfl⟩ : syracuseStep 4110461 = 1541423) (by norm_num)
theorem B2054281 : Blo 1825614 2054281 := bbase (se 2 (by rfl) ⟨770355, by rfl⟩ : syracuseStep 2054281 = 1540711) (by norm_num)
theorem B2054317 : Blo 1825614 2054317 := bbase (se 3 (by rfl) ⟨385184, by rfl⟩ : syracuseStep 2054317 = 770369) (by norm_num)
theorem B4110533 : Blo 1825614 4110533 := bbase (se 4 (by rfl) ⟨385362, by rfl⟩ : syracuseStep 4110533 = 770725) (by norm_num)
theorem B2054353 : Blo 1825614 2054353 := bbase (se 2 (by rfl) ⟨770382, by rfl⟩ : syracuseStep 2054353 = 1540765) (by norm_num)
theorem B2054389 : Blo 1825614 2054389 := bbase (se 5 (by rfl) ⟨96299, by rfl⟩ : syracuseStep 2054389 = 192599) (by norm_num)
theorem B4110605 : Blo 1825614 4110605 := bbase (se 3 (by rfl) ⟨770738, by rfl⟩ : syracuseStep 4110605 = 1541477) (by norm_num)
theorem B23394581 : Blo 1825614 23394581 := bbase (se 6 (by rfl) ⟨548310, by rfl⟩ : syracuseStep 23394581 = 1096621) (by norm_num)
theorem B16668949 : Blo 1825614 16668949 := bbase (se 6 (by rfl) ⟨390678, by rfl⟩ : syracuseStep 16668949 = 781357) (by norm_num)
theorem B2054425 : Blo 1825614 2054425 := bbase (se 2 (by rfl) ⟨770409, by rfl⟩ : syracuseStep 2054425 = 1540819) (by norm_num)
theorem B2054461 : Blo 1825614 2054461 := bbase (se 3 (by rfl) ⟨385211, by rfl⟩ : syracuseStep 2054461 = 770423) (by norm_num)
theorem B7027013 : Blo 1825614 7027013 := bbase (se 4 (by rfl) ⟨658782, by rfl⟩ : syracuseStep 7027013 = 1317565) (by norm_num)
theorem B6166853 : Blo 1825614 6166853 := bbase (se 4 (by rfl) ⟨578142, by rfl⟩ : syracuseStep 6166853 = 1156285) (by norm_num)
theorem B4110677 : Blo 1825614 4110677 := bbase (se 10 (by rfl) ⟨6021, by rfl⟩ : syracuseStep 4110677 = 12043) (by norm_num)
theorem B2054497 : Blo 1825614 2054497 := bbase (se 2 (by rfl) ⟨770436, by rfl⟩ : syracuseStep 2054497 = 1540873) (by norm_num)
theorem B2054533 : Blo 1825614 2054533 := bbase (se 4 (by rfl) ⟨192612, by rfl⟩ : syracuseStep 2054533 = 385225) (by norm_num)
theorem B2193809 : Blo 1825614 2193809 := bbase (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) (by norm_num)
theorem B17562005 : Blo 1825614 17562005 := bbase (se 6 (by rfl) ⟨411609, by rfl⟩ : syracuseStep 17562005 = 823219) (by norm_num)
theorem B4110749 : Blo 1825614 4110749 := bbase (se 3 (by rfl) ⟨770765, by rfl⟩ : syracuseStep 4110749 = 1541531) (by norm_num)
theorem B8780197 : Blo 1825614 8780197 := bbase (se 4 (by rfl) ⟨823143, by rfl⟩ : syracuseStep 8780197 = 1646287) (by norm_num)
theorem B2054569 : Blo 1825614 2054569 := bbase (se 2 (by rfl) ⟨770463, by rfl⟩ : syracuseStep 2054569 = 1540927) (by norm_num)
theorem B6584773 : Blo 1825614 6584773 := bbase (se 4 (by rfl) ⟨617322, by rfl⟩ : syracuseStep 6584773 = 1234645) (by norm_num)
theorem B2054605 : Blo 1825614 2054605 := bbase (se 3 (by rfl) ⟨385238, by rfl⟩ : syracuseStep 2054605 = 770477) (by norm_num)
theorem B13171157 : Blo 1825614 13171157 := bbase (se 7 (by rfl) ⟨154349, by rfl⟩ : syracuseStep 13171157 = 308699) (by norm_num)
theorem B4110821 : Blo 1825614 4110821 := bbase (se 4 (by rfl) ⟨385389, by rfl⟩ : syracuseStep 4110821 = 770779) (by norm_num)
theorem B2054641 : Blo 1825614 2054641 := bbase (se 2 (by rfl) ⟨770490, by rfl⟩ : syracuseStep 2054641 = 1540981) (by norm_num)
theorem B3291637 : Blo 1825614 3291637 := bbase (se 5 (by rfl) ⟨154295, by rfl⟩ : syracuseStep 3291637 = 308591) (by norm_num)
theorem B2054677 : Blo 1825614 2054677 := bbase (se 6 (by rfl) ⟨48156, by rfl⟩ : syracuseStep 2054677 = 96313) (by norm_num)
theorem B4110893 : Blo 1825614 4110893 := bbase (se 3 (by rfl) ⟨770792, by rfl⟩ : syracuseStep 4110893 = 1541585) (by norm_num)
theorem B2054713 : Blo 1825614 2054713 := bbase (se 2 (by rfl) ⟨770517, by rfl⟩ : syracuseStep 2054713 = 1541035) (by norm_num)
theorem B2054749 : Blo 1825614 2054749 := bbase (se 3 (by rfl) ⟨385265, by rfl⟩ : syracuseStep 2054749 = 770531) (by norm_num)
theorem B4110965 : Blo 1825614 4110965 := bbase (se 5 (by rfl) ⟨192701, by rfl⟩ : syracuseStep 4110965 = 385403) (by norm_num)
theorem B2054785 : Blo 1825614 2054785 := bbase (se 2 (by rfl) ⟨770544, by rfl⟩ : syracuseStep 2054785 = 1541089) (by norm_num)
theorem B2054821 : Blo 1825614 2054821 := bbase (se 4 (by rfl) ⟨192639, by rfl⟩ : syracuseStep 2054821 = 385279) (by norm_num)
theorem B4111037 : Blo 1825614 4111037 := bbase (se 3 (by rfl) ⟨770819, by rfl⟩ : syracuseStep 4111037 = 1541639) (by norm_num)
theorem B5552837 : Blo 1825614 5552837 := bbase (se 4 (by rfl) ⟨520578, by rfl⟩ : syracuseStep 5552837 = 1041157) (by norm_num)
theorem B6937285 : Blo 1825614 6937285 := bbase (se 4 (by rfl) ⟨650370, by rfl⟩ : syracuseStep 6937285 = 1300741) (by norm_num)
theorem B2054857 : Blo 1825614 2054857 := bbase (se 2 (by rfl) ⟨770571, by rfl⟩ : syracuseStep 2054857 = 1541143) (by norm_num)
theorem B9247445 : Blo 1825614 9247445 := bbase (se 7 (by rfl) ⟨108368, by rfl⟩ : syracuseStep 9247445 = 216737) (by norm_num)
theorem B2054893 : Blo 1825614 2054893 := bbase (se 3 (by rfl) ⟨385292, by rfl⟩ : syracuseStep 2054893 = 770585) (by norm_num)
theorem B2194165 : Blo 1825614 2194165 := bbase (se 5 (by rfl) ⟨102851, by rfl⟩ : syracuseStep 2194165 = 205703) (by norm_num)
theorem B6167285 : Blo 1825614 6167285 := bbase (se 5 (by rfl) ⟨289091, by rfl⟩ : syracuseStep 6167285 = 578183) (by norm_num)
theorem B4111109 : Blo 1825614 4111109 := bbase (se 4 (by rfl) ⟨385416, by rfl⟩ : syracuseStep 4111109 = 770833) (by norm_num)
theorem B2054929 : Blo 1825614 2054929 := bbase (se 2 (by rfl) ⟨770598, by rfl⟩ : syracuseStep 2054929 = 1541197) (by norm_num)
theorem B2054965 : Blo 1825614 2054965 := bbase (se 5 (by rfl) ⟨96326, by rfl⟩ : syracuseStep 2054965 = 192653) (by norm_num)
theorem B4111181 : Blo 1825614 4111181 := bbase (se 3 (by rfl) ⟨770846, by rfl⟩ : syracuseStep 4111181 = 1541693) (by norm_num)
theorem B2055001 : Blo 1825614 2055001 := bbase (se 2 (by rfl) ⟨770625, by rfl⟩ : syracuseStep 2055001 = 1541251) (by norm_num)
theorem B2055037 : Blo 1825614 2055037 := bbase (se 3 (by rfl) ⟨385319, by rfl⟩ : syracuseStep 2055037 = 770639) (by norm_num)
theorem B4111253 : Blo 1825614 4111253 := bbase (se 6 (by rfl) ⟨96357, by rfl⟩ : syracuseStep 4111253 = 192715) (by norm_num)
theorem B2055073 : Blo 1825614 2055073 := bbase (se 2 (by rfl) ⟨770652, by rfl⟩ : syracuseStep 2055073 = 1541305) (by norm_num)
theorem B17546165 : Blo 1825614 17546165 := bbase (se 5 (by rfl) ⟨822476, by rfl⟩ : syracuseStep 17546165 = 1644953) (by norm_num)
theorem B2055109 : Blo 1825614 2055109 := bbase (se 4 (by rfl) ⟨192666, by rfl⟩ : syracuseStep 2055109 = 385333) (by norm_num)
theorem B4111325 : Blo 1825614 4111325 := bbase (se 3 (by rfl) ⟨770873, by rfl⟩ : syracuseStep 4111325 = 1541747) (by norm_num)
theorem B2055145 : Blo 1825614 2055145 := bbase (se 2 (by rfl) ⟨770679, by rfl⟩ : syracuseStep 2055145 = 1541359) (by norm_num)
theorem B6937589 : Blo 1825614 6937589 := bbase (se 5 (by rfl) ⟨325199, by rfl⟩ : syracuseStep 6937589 = 650399) (by norm_num)
theorem B2055181 : Blo 1825614 2055181 := bbase (se 3 (by rfl) ⟨385346, by rfl⟩ : syracuseStep 2055181 = 770693) (by norm_num)
theorem B4111397 : Blo 1825614 4111397 := bbase (se 4 (by rfl) ⟨385443, by rfl⟩ : syracuseStep 4111397 = 770887) (by norm_num)
theorem B2055217 : Blo 1825614 2055217 := bbase (se 2 (by rfl) ⟨770706, by rfl⟩ : syracuseStep 2055217 = 1541413) (by norm_num)
theorem B5200949 : Blo 1825614 5200949 := bbase (se 5 (by rfl) ⟨243794, by rfl⟩ : syracuseStep 5200949 = 487589) (by norm_num)
theorem B3292213 : Blo 1825614 3292213 := bbase (se 5 (by rfl) ⟨154322, by rfl⟩ : syracuseStep 3292213 = 308645) (by norm_num)
theorem B3513413 : Blo 1825614 3513413 := bbase (se 4 (by rfl) ⟨329382, by rfl⟩ : syracuseStep 3513413 = 658765) (by norm_num)
theorem B2194501 : Blo 1825614 2194501 := bbase (se 4 (by rfl) ⟨205734, by rfl⟩ : syracuseStep 2194501 = 411469) (by norm_num)
theorem B2055253 : Blo 1825614 2055253 := bbase (se 8 (by rfl) ⟨12042, by rfl⟩ : syracuseStep 2055253 = 24085) (by norm_num)
theorem B4447325 : Blo 1825614 4447325 := bbase (se 3 (by rfl) ⟨833873, by rfl⟩ : syracuseStep 4447325 = 1667747) (by norm_num)
theorem B4111469 : Blo 1825614 4111469 := bbase (se 3 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 4111469 = 1541801) (by norm_num)
theorem B2055289 : Blo 1825614 2055289 := bbase (se 2 (by rfl) ⟨770733, by rfl⟩ : syracuseStep 2055289 = 1541467) (by norm_num)
theorem B2964637 : Blo 1825614 2964637 := bbase (se 3 (by rfl) ⟨555869, by rfl⟩ : syracuseStep 2964637 = 1111739) (by norm_num)
theorem B2055325 : Blo 1825614 2055325 := bbase (se 3 (by rfl) ⟨385373, by rfl⟩ : syracuseStep 2055325 = 770747) (by norm_num)
theorem B6167717 : Blo 1825614 6167717 := bbase (se 4 (by rfl) ⟨578223, by rfl⟩ : syracuseStep 6167717 = 1156447) (by norm_num)
theorem B4111541 : Blo 1825614 4111541 := bbase (se 5 (by rfl) ⟨192728, by rfl⟩ : syracuseStep 4111541 = 385457) (by norm_num)
theorem B2055361 : Blo 1825614 2055361 := bbase (se 2 (by rfl) ⟨770760, by rfl⟩ : syracuseStep 2055361 = 1541521) (by norm_num)
theorem B2055397 : Blo 1825614 2055397 := bbase (se 4 (by rfl) ⟨192693, by rfl⟩ : syracuseStep 2055397 = 385387) (by norm_num)
theorem B3955949 : Blo 1825614 3955949 := bbase (se 3 (by rfl) ⟨741740, by rfl⟩ : syracuseStep 3955949 = 1483481) (by norm_num)
theorem B4111613 : Blo 1825614 4111613 := bbase (se 3 (by rfl) ⟨770927, by rfl⟩ : syracuseStep 4111613 = 1541855) (by norm_num)
theorem B2055433 : Blo 1825614 2055433 := bbase (se 2 (by rfl) ⟨770787, by rfl⟩ : syracuseStep 2055433 = 1541575) (by norm_num)
theorem B7404821 : Blo 1825614 7404821 := bbase (se 6 (by rfl) ⟨173550, by rfl⟩ : syracuseStep 7404821 = 347101) (by norm_num)
theorem B2055469 : Blo 1825614 2055469 := bbase (se 3 (by rfl) ⟨385400, by rfl⟩ : syracuseStep 2055469 = 770801) (by norm_num)
theorem B4111685 : Blo 1825614 4111685 := bbase (se 4 (by rfl) ⟨385470, by rfl⟩ : syracuseStep 4111685 = 770941) (by norm_num)
theorem B2055505 : Blo 1825614 2055505 := bbase (se 2 (by rfl) ⟨770814, by rfl⟩ : syracuseStep 2055505 = 1541629) (by norm_num)
theorem B7806293 : Blo 1825614 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B2055541 : Blo 1825614 2055541 := bbase (se 5 (by rfl) ⟨96353, by rfl⟩ : syracuseStep 2055541 = 192707) (by norm_num)
theorem B4111757 : Blo 1825614 4111757 := bbase (se 3 (by rfl) ⟨770954, by rfl⟩ : syracuseStep 4111757 = 1541909) (by norm_num)
theorem B2055577 : Blo 1825614 2055577 := bbase (se 2 (by rfl) ⟨770841, by rfl⟩ : syracuseStep 2055577 = 1541683) (by norm_num)
theorem B4390301 : Blo 1825614 4390301 := bbase (se 3 (by rfl) ⟨823181, by rfl⟩ : syracuseStep 4390301 = 1646363) (by norm_num)
theorem B4390309 : Blo 1825614 4390309 := bbase (se 4 (by rfl) ⟨411591, by rfl⟩ : syracuseStep 4390309 = 823183) (by norm_num)
theorem B2055613 : Blo 1825614 2055613 := bbase (se 3 (by rfl) ⟨385427, by rfl⟩ : syracuseStep 2055613 = 770855) (by norm_num)
theorem B2170309 : Blo 1825614 2170309 := bbase (se 4 (by rfl) ⟨203466, by rfl⟩ : syracuseStep 2170309 = 406933) (by norm_num)
theorem B6766037 : Blo 1825614 6766037 := bbase (se 7 (by rfl) ⟨79289, by rfl⟩ : syracuseStep 6766037 = 158579) (by norm_num)
theorem B4111829 : Blo 1825614 4111829 := bbase (se 7 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 4111829 = 96371) (by norm_num)
theorem B2055649 : Blo 1825614 2055649 := bbase (se 2 (by rfl) ⟨770868, by rfl⟩ : syracuseStep 2055649 = 1541737) (by norm_num)
theorem B1850861 : Blo 1825614 1850861 := bbase (se 3 (by rfl) ⟨347036, by rfl⟩ : syracuseStep 1850861 = 694073) (by norm_num)
theorem B2055685 : Blo 1825614 2055685 := bbase (se 4 (by rfl) ⟨192720, by rfl⟩ : syracuseStep 2055685 = 385441) (by norm_num)
theorem B1850897 : Blo 1825614 1850897 := bbase (se 2 (by rfl) ⟨694086, by rfl⟩ : syracuseStep 1850897 = 1388173) (by norm_num)
theorem B13876757 : Blo 1825614 13876757 := bbase (se 6 (by rfl) ⟨325236, by rfl⟩ : syracuseStep 13876757 = 650473) (by norm_num)
theorem B4111901 : Blo 1825614 4111901 := bbase (se 3 (by rfl) ⟨770981, by rfl⟩ : syracuseStep 4111901 = 1541963) (by norm_num)
theorem B2055721 : Blo 1825614 2055721 := bbase (se 2 (by rfl) ⟨770895, by rfl⟩ : syracuseStep 2055721 = 1541791) (by norm_num)
theorem B2055757 : Blo 1825614 2055757 := bbase (se 3 (by rfl) ⟨385454, by rfl⟩ : syracuseStep 2055757 = 770909) (by norm_num)
theorem B6168149 : Blo 1825614 6168149 := bbase (se 8 (by rfl) ⟨36141, by rfl⟩ : syracuseStep 6168149 = 72283) (by norm_num)
theorem B4111973 : Blo 1825614 4111973 := bbase (se 4 (by rfl) ⟨385497, by rfl⟩ : syracuseStep 4111973 = 770995) (by norm_num)
theorem B2055793 : Blo 1825614 2055793 := bbase (se 2 (by rfl) ⟨770922, by rfl⟩ : syracuseStep 2055793 = 1541845) (by norm_num)
theorem B2055829 : Blo 1825614 2055829 := bbase (se 6 (by rfl) ⟨48183, by rfl⟩ : syracuseStep 2055829 = 96367) (by norm_num)
theorem B4112045 : Blo 1825614 4112045 := bbase (se 3 (by rfl) ⟨771008, by rfl⟩ : syracuseStep 4112045 = 1542017) (by norm_num)
theorem B2055865 : Blo 1825614 2055865 := bbase (se 2 (by rfl) ⟨770949, by rfl⟩ : syracuseStep 2055865 = 1541899) (by norm_num)
theorem B5201621 : Blo 1825614 5201621 := bbase (se 7 (by rfl) ⟨60956, by rfl⟩ : syracuseStep 5201621 = 121913) (by norm_num)
theorem B2055901 : Blo 1825614 2055901 := bbase (se 3 (by rfl) ⟨385481, by rfl⟩ : syracuseStep 2055901 = 770963) (by norm_num)
theorem B1851121 : Blo 1825614 1851121 := bbase (se 2 (by rfl) ⟨694170, by rfl⟩ : syracuseStep 1851121 = 1388341) (by norm_num)
theorem B4112117 : Blo 1825614 4112117 := bbase (se 5 (by rfl) ⟨192755, by rfl⟩ : syracuseStep 4112117 = 385511) (by norm_num)
theorem B2055937 : Blo 1825614 2055937 := bbase (se 2 (by rfl) ⟨770976, by rfl⟩ : syracuseStep 2055937 = 1541953) (by norm_num)
theorem B2055973 : Blo 1825614 2055973 := bbase (se 4 (by rfl) ⟨192747, by rfl⟩ : syracuseStep 2055973 = 385495) (by norm_num)
theorem B2056009 : Blo 1825614 2056009 := bbase (se 2 (by rfl) ⟨771003, by rfl⟩ : syracuseStep 2056009 = 1542007) (by norm_num)
theorem B2056045 : Blo 1825614 2056045 := bbase (se 3 (by rfl) ⟨385508, by rfl⟩ : syracuseStep 2056045 = 771017) (by norm_num)
theorem B1949557 : Blo 1825614 1949557 := bbase (se 5 (by rfl) ⟨91385, by rfl⟩ : syracuseStep 1949557 = 182771) (by norm_num)
theorem B1949617 : Blo 1825614 1949617 := bbase (se 2 (by rfl) ⟨731106, by rfl⟩ : syracuseStep 1949617 = 1462213) (by norm_num)
theorem B13868981 : Blo 1825614 13868981 := bbase (se 5 (by rfl) ⟨650108, by rfl⟩ : syracuseStep 13868981 = 1300217) (by norm_num)
theorem B2195381 : Blo 1825614 2195381 := bbase (se 5 (by rfl) ⟨102908, by rfl⟩ : syracuseStep 2195381 = 205817) (by norm_num)
theorem B9248741 : Blo 1825614 9248741 := bbase (se 4 (by rfl) ⟨867069, by rfl⟩ : syracuseStep 9248741 = 1734139) (by norm_num)
theorem B1826819 : Blo 1825614 1826819 := bstep (se 1 (by rfl) ⟨1370114, by rfl⟩ : syracuseStep 1826819 = 2740229) B2740229
theorem B17563661 : Blo 1825614 17563661 := bstep (se 3 (by rfl) ⟨3293186, by rfl⟩ : syracuseStep 17563661 = 6586373) B6586373
theorem B2924561 : Blo 1825614 2924561 := bstep (se 2 (by rfl) ⟨1096710, by rfl⟩ : syracuseStep 2924561 = 2193421) B2193421
theorem B1826835 : Blo 1825614 1826835 := bstep (se 1 (by rfl) ⟨1370126, by rfl⟩ : syracuseStep 1826835 = 2740253) B2740253
theorem B1826851 : Blo 1825614 1826851 := bstep (se 1 (by rfl) ⟨1370138, by rfl⟩ : syracuseStep 1826851 = 2740277) B2740277
theorem B1826867 : Blo 1825614 1826867 := bstep (se 1 (by rfl) ⟨1370150, by rfl⟩ : syracuseStep 1826867 = 2740301) B2740301
theorem B1826883 : Blo 1825614 1826883 := bstep (se 1 (by rfl) ⟨1370162, by rfl⟩ : syracuseStep 1826883 = 2740325) B2740325
theorem B1949779 : Blo 1825614 1949779 := bstep (se 1 (by rfl) ⟨1462334, by rfl⟩ : syracuseStep 1949779 = 2924669) B2924669
theorem B1826899 : Blo 1825614 1826899 := bstep (se 1 (by rfl) ⟨1370174, by rfl⟩ : syracuseStep 1826899 = 2740349) B2740349
theorem B5931107 : Blo 1825614 5931107 := bstep (se 1 (by rfl) ⟨4448330, by rfl⟩ : syracuseStep 5931107 = 8896661) B8896661
theorem B1826915 : Blo 1825614 1826915 := bstep (se 1 (by rfl) ⟨1370186, by rfl⟩ : syracuseStep 1826915 = 2740373) B2740373
theorem B1826931 : Blo 1825614 1826931 := bstep (se 1 (by rfl) ⟨1370198, by rfl⟩ : syracuseStep 1826931 = 2740397) B2740397
theorem B1826947 : Blo 1825614 1826947 := bstep (se 1 (by rfl) ⟨1370210, by rfl⟩ : syracuseStep 1826947 = 2740421) B2740421
theorem B1826963 : Blo 1825614 1826963 := bstep (se 1 (by rfl) ⟨1370222, by rfl⟩ : syracuseStep 1826963 = 2740445) B2740445
theorem B4685987 : Blo 1825614 4685987 := bstep (se 1 (by rfl) ⟨3514490, by rfl⟩ : syracuseStep 4685987 = 7028981) B7028981
theorem B1826979 : Blo 1825614 1826979 := bstep (se 1 (by rfl) ⟨1370234, by rfl⟩ : syracuseStep 1826979 = 2740469) B2740469
theorem B1826995 : Blo 1825614 1826995 := bstep (se 1 (by rfl) ⟨1370246, by rfl⟩ : syracuseStep 1826995 = 2740493) B2740493
theorem B1827011 : Blo 1825614 1827011 := bstep (se 1 (by rfl) ⟨1370258, by rfl⟩ : syracuseStep 1827011 = 2740517) B2740517
theorem B4939985 : Blo 1825614 4939985 := bstep (se 2 (by rfl) ⟨1852494, by rfl⟩ : syracuseStep 4939985 = 3704989) B3704989
theorem B1827027 : Blo 1825614 1827027 := bstep (se 1 (by rfl) ⟨1370270, by rfl⟩ : syracuseStep 1827027 = 2740541) B2740541
theorem B1827043 : Blo 1825614 1827043 := bstep (se 1 (by rfl) ⟨1370282, by rfl⟩ : syracuseStep 1827043 = 2740565) B2740565
theorem B11108593 : Blo 1825614 11108593 := bstep (se 2 (by rfl) ⟨4165722, by rfl⟩ : syracuseStep 11108593 = 8331445) B8331445
theorem B1827059 : Blo 1825614 1827059 := bstep (se 1 (by rfl) ⟨1370294, by rfl⟩ : syracuseStep 1827059 = 2740589) B2740589
theorem B1827075 : Blo 1825614 1827075 := bstep (se 1 (by rfl) ⟨1370306, by rfl⟩ : syracuseStep 1827075 = 2740613) B2740613
theorem B11698445 : Blo 1825614 11698445 := bstep (se 3 (by rfl) ⟨2193458, by rfl⟩ : syracuseStep 11698445 = 4386917) B4386917
theorem B1827091 : Blo 1825614 1827091 := bstep (se 1 (by rfl) ⟨1370318, by rfl⟩ : syracuseStep 1827091 = 2740637) B2740637
theorem B1827107 : Blo 1825614 1827107 := bstep (se 1 (by rfl) ⟨1370330, by rfl⟩ : syracuseStep 1827107 = 2740661) B2740661
theorem B9371953 : Blo 1825614 9371953 := bstep (se 2 (by rfl) ⟨3514482, by rfl⟩ : syracuseStep 9371953 = 7028965) B7028965
theorem B1827123 : Blo 1825614 1827123 := bstep (se 1 (by rfl) ⟨1370342, by rfl⟩ : syracuseStep 1827123 = 2740685) B2740685
theorem B1827139 : Blo 1825614 1827139 := bstep (se 1 (by rfl) ⟨1370354, by rfl⟩ : syracuseStep 1827139 = 2740709) B2740709
theorem B1827155 : Blo 1825614 1827155 := bstep (se 1 (by rfl) ⟨1370366, by rfl⟩ : syracuseStep 1827155 = 2740733) B2740733
theorem B1827171 : Blo 1825614 1827171 := bstep (se 1 (by rfl) ⟨1370378, by rfl⟩ : syracuseStep 1827171 = 2740757) B2740757
theorem B17564003 : Blo 1825614 17564003 := bstep (se 1 (by rfl) ⟨13173002, by rfl⟩ : syracuseStep 17564003 = 26346005) B26346005
theorem B22225265 : Blo 1825614 22225265 := bstep (se 2 (by rfl) ⟨8334474, by rfl⟩ : syracuseStep 22225265 = 16668949) B16668949
theorem B1827187 : Blo 1825614 1827187 := bstep (se 1 (by rfl) ⟨1370390, by rfl⟩ : syracuseStep 1827187 = 2740781) B2740781
theorem B1827203 : Blo 1825614 1827203 := bstep (se 1 (by rfl) ⟨1370402, by rfl⟩ : syracuseStep 1827203 = 2740805) B2740805
theorem B1827219 : Blo 1825614 1827219 := bstep (se 1 (by rfl) ⟨1370414, by rfl⟩ : syracuseStep 1827219 = 2740829) B2740829
theorem B1827235 : Blo 1825614 1827235 := bstep (se 1 (by rfl) ⟨1370426, by rfl⟩ : syracuseStep 1827235 = 2740853) B2740853
theorem B1827251 : Blo 1825614 1827251 := bstep (se 1 (by rfl) ⟨1370438, by rfl⟩ : syracuseStep 1827251 = 2740877) B2740877
theorem B1827267 : Blo 1825614 1827267 := bstep (se 1 (by rfl) ⟨1370450, by rfl⟩ : syracuseStep 1827267 = 2740901) B2740901
theorem B1827283 : Blo 1825614 1827283 := bstep (se 1 (by rfl) ⟨1370462, by rfl⟩ : syracuseStep 1827283 = 2740925) B2740925
theorem B1827299 : Blo 1825614 1827299 := bstep (se 1 (by rfl) ⟨1370474, by rfl⟩ : syracuseStep 1827299 = 2740949) B2740949
theorem B1827315 : Blo 1825614 1827315 := bstep (se 1 (by rfl) ⟨1370486, by rfl⟩ : syracuseStep 1827315 = 2740973) B2740973
theorem B1827331 : Blo 1825614 1827331 := bstep (se 1 (by rfl) ⟨1370498, by rfl⟩ : syracuseStep 1827331 = 2740997) B2740997
theorem B1827347 : Blo 1825614 1827347 := bstep (se 1 (by rfl) ⟨1370510, by rfl⟩ : syracuseStep 1827347 = 2741021) B2741021
theorem B1827363 : Blo 1825614 1827363 := bstep (se 1 (by rfl) ⟨1370522, by rfl⟩ : syracuseStep 1827363 = 2741045) B2741045
theorem B11706929 : Blo 1825614 11706929 := bstep (se 2 (by rfl) ⟨4390098, by rfl⟩ : syracuseStep 11706929 = 8780197) B8780197
theorem B2310707 : Blo 1825614 2310707 := bstep (se 1 (by rfl) ⟨1733030, by rfl⟩ : syracuseStep 2310707 = 3466061) B3466061
theorem B1827379 : Blo 1825614 1827379 := bstep (se 1 (by rfl) ⟨1370534, by rfl⟩ : syracuseStep 1827379 = 2741069) B2741069
theorem B1827395 : Blo 1825614 1827395 := bstep (se 1 (by rfl) ⟨1370546, by rfl⟩ : syracuseStep 1827395 = 2741093) B2741093
theorem B1827411 : Blo 1825614 1827411 := bstep (se 1 (by rfl) ⟨1370558, by rfl⟩ : syracuseStep 1827411 = 2741117) B2741117
theorem B3080801 : Blo 1825614 3080801 := bstep (se 2 (by rfl) ⟨1155300, by rfl⟩ : syracuseStep 3080801 = 2310601) B2310601
theorem B7029347 : Blo 1825614 7029347 := bstep (se 1 (by rfl) ⟨5272010, by rfl⟩ : syracuseStep 7029347 = 10544021) B10544021
theorem B1827427 : Blo 1825614 1827427 := bstep (se 1 (by rfl) ⟨1370570, by rfl⟩ : syracuseStep 1827427 = 2741141) B2741141
theorem B3465841 : Blo 1825614 3465841 := bstep (se 2 (by rfl) ⟨1299690, by rfl⟩ : syracuseStep 3465841 = 2599381) B2599381
theorem B1827443 : Blo 1825614 1827443 := bstep (se 1 (by rfl) ⟨1370582, by rfl⟩ : syracuseStep 1827443 = 2741165) B2741165
theorem B1827459 : Blo 1825614 1827459 := bstep (se 1 (by rfl) ⟨1370594, by rfl⟩ : syracuseStep 1827459 = 2741189) B2741189
theorem B1827475 : Blo 1825614 1827475 := bstep (se 1 (by rfl) ⟨1370606, by rfl⟩ : syracuseStep 1827475 = 2741213) B2741213
theorem B1827491 : Blo 1825614 1827491 := bstep (se 1 (by rfl) ⟨1370618, by rfl⟩ : syracuseStep 1827491 = 2741237) B2741237
theorem B1827507 : Blo 1825614 1827507 := bstep (se 1 (by rfl) ⟨1370630, by rfl⟩ : syracuseStep 1827507 = 2741261) B2741261
theorem B1827523 : Blo 1825614 1827523 := bstep (se 1 (by rfl) ⟨1370642, by rfl⟩ : syracuseStep 1827523 = 2741285) B2741285
theorem B1827539 : Blo 1825614 1827539 := bstep (se 1 (by rfl) ⟨1370654, by rfl⟩ : syracuseStep 1827539 = 2741309) B2741309
theorem B3080929 : Blo 1825614 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B1827555 : Blo 1825614 1827555 := bstep (se 1 (by rfl) ⟨1370666, by rfl⟩ : syracuseStep 1827555 = 2741333) B2741333
theorem B1827571 : Blo 1825614 1827571 := bstep (se 1 (by rfl) ⟨1370678, by rfl⟩ : syracuseStep 1827571 = 2741357) B2741357
theorem B3080963 : Blo 1825614 3080963 := bstep (se 1 (by rfl) ⟨2310722, by rfl⟩ : syracuseStep 3080963 = 4621445) B4621445
theorem B1827587 : Blo 1825614 1827587 := bstep (se 1 (by rfl) ⟨1370690, by rfl⟩ : syracuseStep 1827587 = 2741381) B2741381
theorem B1827603 : Blo 1825614 1827603 := bstep (se 1 (by rfl) ⟨1370702, by rfl⟩ : syracuseStep 1827603 = 2741405) B2741405
theorem B5202737 : Blo 1825614 5202737 := bstep (se 2 (by rfl) ⟨1951026, by rfl⟩ : syracuseStep 5202737 = 3902053) B3902053
theorem B3900241 : Blo 1825614 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B3081091 : Blo 1825614 3081091 := bstep (se 1 (by rfl) ⟨2310818, by rfl⟩ : syracuseStep 3081091 = 4621637) B4621637
theorem B2343811 : Blo 1825614 2343811 := bstep (se 1 (by rfl) ⟨1757858, by rfl⟩ : syracuseStep 2343811 = 3515717) B3515717
theorem B9249713 : Blo 1825614 9249713 := bstep (se 2 (by rfl) ⟨3468642, by rfl⟩ : syracuseStep 9249713 = 6937285) B6937285
theorem B52667333 : Blo 1825614 52667333 := bstep (se 4 (by rfl) ⟨4937562, by rfl⟩ : syracuseStep 52667333 = 9875125) B9875125
theorem B4621283 : Blo 1825614 4621283 := bstep (se 1 (by rfl) ⟨3465962, by rfl⟩ : syracuseStep 4621283 = 6931925) B6931925
theorem B2925553 : Blo 1825614 2925553 := bstep (se 2 (by rfl) ⟨1097082, by rfl⟩ : syracuseStep 2925553 = 2194165) B2194165
theorem B3466243 : Blo 1825614 3466243 := bstep (se 1 (by rfl) ⟨2599682, by rfl⟩ : syracuseStep 3466243 = 5199365) B5199365
theorem B5555213 : Blo 1825614 5555213 := bstep (se 3 (by rfl) ⟨1041602, by rfl⟩ : syracuseStep 5555213 = 2083205) B2083205
theorem B3081233 : Blo 1825614 3081233 := bstep (se 2 (by rfl) ⟨1155462, by rfl⟩ : syracuseStep 3081233 = 2310925) B2310925
theorem B6161453 : Blo 1825614 6161453 := bstep (se 3 (by rfl) ⟨1155272, by rfl⟩ : syracuseStep 6161453 = 2310545) B2310545
theorem B5850157 : Blo 1825614 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B3466289 : Blo 1825614 3466289 := bstep (se 2 (by rfl) ⟨1299858, by rfl⟩ : syracuseStep 3466289 = 2599717) B2599717
theorem B1950787 : Blo 1825614 1950787 := bstep (se 1 (by rfl) ⟨1463090, by rfl⟩ : syracuseStep 1950787 = 2926181) B2926181
theorem B6161507 : Blo 1825614 6161507 := bstep (se 1 (by rfl) ⟨4621130, by rfl⟩ : syracuseStep 6161507 = 9242261) B9242261
theorem B7799921 : Blo 1825614 7799921 := bstep (se 2 (by rfl) ⟨2924970, by rfl⟩ : syracuseStep 7799921 = 5849941) B5849941
theorem B3081361 : Blo 1825614 3081361 := bstep (se 2 (by rfl) ⟨1155510, by rfl⟩ : syracuseStep 3081361 = 2311021) B2311021
theorem B4621475 : Blo 1825614 4621475 := bstep (se 1 (by rfl) ⟨3466106, by rfl⟩ : syracuseStep 4621475 = 6932213) B6932213
theorem B3081395 : Blo 1825614 3081395 := bstep (se 1 (by rfl) ⟨2311046, by rfl⟩ : syracuseStep 3081395 = 4622093) B4622093
theorem B5932259 : Blo 1825614 5932259 := bstep (se 1 (by rfl) ⟨4449194, by rfl⟩ : syracuseStep 5932259 = 8898389) B8898389
theorem B2311411 : Blo 1825614 2311411 := bstep (se 1 (by rfl) ⟨1733558, by rfl⟩ : syracuseStep 2311411 = 3467117) B3467117
theorem B3081523 : Blo 1825614 3081523 := bstep (se 1 (by rfl) ⟨2311142, by rfl⟩ : syracuseStep 3081523 = 4622285) B4622285
theorem B3466577 : Blo 1825614 3466577 := bstep (se 2 (by rfl) ⟨1299966, by rfl⟩ : syracuseStep 3466577 = 2599933) B2599933
theorem B2311507 : Blo 1825614 2311507 := bstep (se 1 (by rfl) ⟨1733630, by rfl⟩ : syracuseStep 2311507 = 3467261) B3467261
theorem B6161777 : Blo 1825614 6161777 := bstep (se 2 (by rfl) ⟨2310666, by rfl⟩ : syracuseStep 6161777 = 4621333) B4621333
theorem B2926001 : Blo 1825614 2926001 := bstep (se 2 (by rfl) ⟨1097250, by rfl⟩ : syracuseStep 2926001 = 2194501) B2194501
theorem B3081665 : Blo 1825614 3081665 := bstep (se 2 (by rfl) ⟨1155624, by rfl⟩ : syracuseStep 3081665 = 2311249) B2311249
theorem B6931939 : Blo 1825614 6931939 := bstep (se 1 (by rfl) ⟨5198954, by rfl⟩ : syracuseStep 6931939 = 10397909) B10397909
theorem B10405381 : Blo 1825614 10405381 := bstep (se 4 (by rfl) ⟨975504, by rfl⟩ : syracuseStep 10405381 = 1951009) B1951009
theorem B33326645 : Blo 1825614 33326645 := bstep (se 5 (by rfl) ⟨1562186, by rfl⟩ : syracuseStep 33326645 = 3124373) B3124373
theorem B3081793 : Blo 1825614 3081793 := bstep (se 2 (by rfl) ⟨1155672, by rfl⟩ : syracuseStep 3081793 = 2311345) B2311345
theorem B3081827 : Blo 1825614 3081827 := bstep (se 1 (by rfl) ⟨2311370, by rfl⟩ : syracuseStep 3081827 = 4622741) B4622741
theorem B11708003 : Blo 1825614 11708003 := bstep (se 1 (by rfl) ⟨8781002, by rfl⟩ : syracuseStep 11708003 = 17562005) B17562005
theorem B11110051 : Blo 1825614 11110051 := bstep (se 1 (by rfl) ⟨8332538, by rfl⟩ : syracuseStep 11110051 = 16665077) B16665077
theorem B6252241 : Blo 1825614 6252241 := bstep (se 2 (by rfl) ⟨2344590, by rfl⟩ : syracuseStep 6252241 = 4689181) B4689181
theorem B3081955 : Blo 1825614 3081955 := bstep (se 1 (by rfl) ⟨2311466, by rfl⟩ : syracuseStep 3081955 = 4622933) B4622933
theorem B5203693 : Blo 1825614 5203693 := bstep (se 3 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 5203693 = 1951385) B1951385
theorem B2312003 : Blo 1825614 2312003 := bstep (se 1 (by rfl) ⟨1734002, by rfl⟩ : syracuseStep 2312003 = 3468005) B3468005
theorem B11863907 : Blo 1825614 11863907 := bstep (se 1 (by rfl) ⟨8897930, by rfl⟩ : syracuseStep 11863907 = 17795861) B17795861
theorem B3082097 : Blo 1825614 3082097 := bstep (se 2 (by rfl) ⟨1155786, by rfl⟩ : syracuseStep 3082097 = 2311573) B2311573
theorem B2967425 : Blo 1825614 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B6162317 : Blo 1825614 6162317 := bstep (se 3 (by rfl) ⟨1155434, by rfl⟩ : syracuseStep 6162317 = 2310869) B2310869
theorem B2893745 : Blo 1825614 2893745 := bstep (se 2 (by rfl) ⟨1085154, by rfl⟩ : syracuseStep 2893745 = 2170309) B2170309
theorem B6162371 : Blo 1825614 6162371 := bstep (se 1 (by rfl) ⟨4621778, by rfl⟩ : syracuseStep 6162371 = 9243557) B9243557
theorem B5203921 : Blo 1825614 5203921 := bstep (se 2 (by rfl) ⟨1951470, by rfl⟩ : syracuseStep 5203921 = 3902941) B3902941
theorem B3082225 : Blo 1825614 3082225 := bstep (se 2 (by rfl) ⟨1155834, by rfl⟩ : syracuseStep 3082225 = 2311669) B2311669
theorem B3082259 : Blo 1825614 3082259 := bstep (se 1 (by rfl) ⟨2311694, by rfl⟩ : syracuseStep 3082259 = 4623389) B4623389
theorem B3467299 : Blo 1825614 3467299 := bstep (se 1 (by rfl) ⟨2600474, by rfl⟩ : syracuseStep 3467299 = 5200949) B5200949
theorem B4622417 : Blo 1825614 4622417 := bstep (se 2 (by rfl) ⟨1733406, by rfl⟩ : syracuseStep 4622417 = 3466813) B3466813
theorem B5204081 : Blo 1825614 5204081 := bstep (se 2 (by rfl) ⟨1951530, by rfl⟩ : syracuseStep 5204081 = 3903061) B3903061
theorem B4622467 : Blo 1825614 4622467 := bstep (se 1 (by rfl) ⟨3466850, by rfl⟩ : syracuseStep 4622467 = 6933701) B6933701
theorem B3082387 : Blo 1825614 3082387 := bstep (se 1 (by rfl) ⟨2311790, by rfl⟩ : syracuseStep 3082387 = 4623581) B4623581
theorem B6162641 : Blo 1825614 6162641 := bstep (se 2 (by rfl) ⟨2310990, by rfl⟩ : syracuseStep 6162641 = 4621981) B4621981
theorem B5204195 : Blo 1825614 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B2738435 : Blo 1825614 2738435 := bstep (se 1 (by rfl) ⟨2053826, by rfl⟩ : syracuseStep 2738435 = 4107653) B4107653
theorem B4622609 : Blo 1825614 4622609 := bstep (se 2 (by rfl) ⟨1733478, by rfl⟩ : syracuseStep 4622609 = 3466957) B3466957
theorem B2926867 : Blo 1825614 2926867 := bstep (se 1 (by rfl) ⟨2195150, by rfl⟩ : syracuseStep 2926867 = 4390301) B4390301
theorem B2738465 : Blo 1825614 2738465 := bstep (se 2 (by rfl) ⟨1026924, by rfl⟩ : syracuseStep 2738465 = 2053849) B2053849
theorem B3082529 : Blo 1825614 3082529 := bstep (se 2 (by rfl) ⟨1155948, by rfl⟩ : syracuseStep 3082529 = 2311897) B2311897
theorem B3901745 : Blo 1825614 3901745 := bstep (se 2 (by rfl) ⟨1463154, by rfl⟩ : syracuseStep 3901745 = 2926309) B2926309
theorem B2738483 : Blo 1825614 2738483 := bstep (se 1 (by rfl) ⟨2053862, by rfl⟩ : syracuseStep 2738483 = 4107725) B4107725
theorem B2468161 : Blo 1825614 2468161 := bstep (se 2 (by rfl) ⟨925560, by rfl⟩ : syracuseStep 2468161 = 1851121) B1851121
theorem B3901763 : Blo 1825614 3901763 := bstep (se 1 (by rfl) ⟨2926322, by rfl⟩ : syracuseStep 3901763 = 5852645) B5852645
theorem B5343565 : Blo 1825614 5343565 := bstep (se 3 (by rfl) ⟨1001918, by rfl⟩ : syracuseStep 5343565 = 2003837) B2003837
theorem B2738513 : Blo 1825614 2738513 := bstep (se 2 (by rfl) ⟨1026942, by rfl⟩ : syracuseStep 2738513 = 2053885) B2053885
theorem B2738531 : Blo 1825614 2738531 := bstep (se 1 (by rfl) ⟨2053898, by rfl⟩ : syracuseStep 2738531 = 4107797) B4107797
theorem B9251171 : Blo 1825614 9251171 := bstep (se 1 (by rfl) ⟨6938378, by rfl⟩ : syracuseStep 9251171 = 13876757) B13876757
theorem B2738561 : Blo 1825614 2738561 := bstep (se 2 (by rfl) ⟨1026960, by rfl⟩ : syracuseStep 2738561 = 2053921) B2053921
theorem B2738579 : Blo 1825614 2738579 := bstep (se 1 (by rfl) ⟨2053934, by rfl⟩ : syracuseStep 2738579 = 4107869) B4107869
theorem B3082657 : Blo 1825614 3082657 := bstep (se 2 (by rfl) ⟨1155996, by rfl⟩ : syracuseStep 3082657 = 2311993) B2311993
theorem B2738609 : Blo 1825614 2738609 := bstep (se 2 (by rfl) ⟨1026978, by rfl⟩ : syracuseStep 2738609 = 2053957) B2053957
theorem B2738627 : Blo 1825614 2738627 := bstep (se 1 (by rfl) ⟨2053970, by rfl⟩ : syracuseStep 2738627 = 4107941) B4107941
theorem B3082691 : Blo 1825614 3082691 := bstep (se 1 (by rfl) ⟨2312018, by rfl⟩ : syracuseStep 3082691 = 4624037) B4624037
theorem B2738657 : Blo 1825614 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B3467747 : Blo 1825614 3467747 := bstep (se 1 (by rfl) ⟨2600810, by rfl⟩ : syracuseStep 3467747 = 5201621) B5201621
theorem B5556707 : Blo 1825614 5556707 := bstep (se 1 (by rfl) ⟨4167530, by rfl⟩ : syracuseStep 5556707 = 8335061) B8335061
theorem B2599409 : Blo 1825614 2599409 := bstep (se 2 (by rfl) ⟨974778, by rfl⟩ : syracuseStep 2599409 = 1949557) B1949557
theorem B15600113 : Blo 1825614 15600113 := bstep (se 2 (by rfl) ⟨5850042, by rfl⟩ : syracuseStep 15600113 = 11700085) B11700085
theorem B2738675 : Blo 1825614 2738675 := bstep (se 1 (by rfl) ⟨2054006, by rfl⟩ : syracuseStep 2738675 = 4108013) B4108013
theorem B2312707 : Blo 1825614 2312707 := bstep (se 1 (by rfl) ⟨1734530, by rfl⟩ : syracuseStep 2312707 = 3469061) B3469061
theorem B2738705 : Blo 1825614 2738705 := bstep (se 2 (by rfl) ⟨1027014, by rfl⟩ : syracuseStep 2738705 = 2054029) B2054029
theorem B2738723 : Blo 1825614 2738723 := bstep (se 1 (by rfl) ⟨2054042, by rfl⟩ : syracuseStep 2738723 = 4108085) B4108085
theorem B2599489 : Blo 1825614 2599489 := bstep (se 2 (by rfl) ⟨974808, by rfl⟩ : syracuseStep 2599489 = 1949617) B1949617
theorem B2738753 : Blo 1825614 2738753 := bstep (se 2 (by rfl) ⟨1027032, by rfl⟩ : syracuseStep 2738753 = 2054065) B2054065
theorem B3082819 : Blo 1825614 3082819 := bstep (se 1 (by rfl) ⟨2312114, by rfl⟩ : syracuseStep 3082819 = 4624229) B4624229
theorem B2738771 : Blo 1825614 2738771 := bstep (se 1 (by rfl) ⟨2054078, by rfl⟩ : syracuseStep 2738771 = 4108157) B4108157
theorem B2312803 : Blo 1825614 2312803 := bstep (se 1 (by rfl) ⟨1734602, by rfl⟩ : syracuseStep 2312803 = 3469205) B3469205
theorem B2738801 : Blo 1825614 2738801 := bstep (se 2 (by rfl) ⟨1027050, by rfl⟩ : syracuseStep 2738801 = 2054101) B2054101
theorem B2738819 : Blo 1825614 2738819 := bstep (se 1 (by rfl) ⟨2054114, by rfl⟩ : syracuseStep 2738819 = 4108229) B4108229
theorem B2738849 : Blo 1825614 2738849 := bstep (se 2 (by rfl) ⟨1027068, by rfl⟩ : syracuseStep 2738849 = 2054137) B2054137
theorem B2738867 : Blo 1825614 2738867 := bstep (se 1 (by rfl) ⟨2054150, by rfl⟩ : syracuseStep 2738867 = 4108301) B4108301
theorem B28125893 : Blo 1825614 28125893 := bstep (se 4 (by rfl) ⟨2636802, by rfl⟩ : syracuseStep 28125893 = 5273605) B5273605
theorem B2738897 : Blo 1825614 2738897 := bstep (se 2 (by rfl) ⟨1027086, by rfl⟩ : syracuseStep 2738897 = 2054173) B2054173
theorem B3082961 : Blo 1825614 3082961 := bstep (se 2 (by rfl) ⟨1156110, by rfl⟩ : syracuseStep 3082961 = 2312221) B2312221
theorem B2738915 : Blo 1825614 2738915 := bstep (se 1 (by rfl) ⟨2054186, by rfl⟩ : syracuseStep 2738915 = 4108373) B4108373
theorem B6163181 : Blo 1825614 6163181 := bstep (se 3 (by rfl) ⟨1155596, by rfl⟩ : syracuseStep 6163181 = 2311193) B2311193
theorem B5851889 : Blo 1825614 5851889 := bstep (se 2 (by rfl) ⟨2194458, by rfl⟩ : syracuseStep 5851889 = 4388917) B4388917
theorem B2738945 : Blo 1825614 2738945 := bstep (se 2 (by rfl) ⟨1027104, by rfl⟩ : syracuseStep 2738945 = 2054209) B2054209
theorem B3468035 : Blo 1825614 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B2738963 : Blo 1825614 2738963 := bstep (se 1 (by rfl) ⟨2054222, by rfl⟩ : syracuseStep 2738963 = 4108445) B4108445
theorem B6163235 : Blo 1825614 6163235 := bstep (se 1 (by rfl) ⟨4622426, by rfl⟩ : syracuseStep 6163235 = 9244853) B9244853
theorem B2738993 : Blo 1825614 2738993 := bstep (se 2 (by rfl) ⟨1027122, by rfl⟩ : syracuseStep 2738993 = 2054245) B2054245
theorem B2739011 : Blo 1825614 2739011 := bstep (se 1 (by rfl) ⟨2054258, by rfl⟩ : syracuseStep 2739011 = 4108517) B4108517
theorem B3083089 : Blo 1825614 3083089 := bstep (se 2 (by rfl) ⟨1156158, by rfl⟩ : syracuseStep 3083089 = 2312317) B2312317
theorem B2739041 : Blo 1825614 2739041 := bstep (se 2 (by rfl) ⟨1027140, by rfl⟩ : syracuseStep 2739041 = 2054281) B2054281
theorem B2739059 : Blo 1825614 2739059 := bstep (se 1 (by rfl) ⟨2054294, by rfl⟩ : syracuseStep 2739059 = 4108589) B4108589
theorem B3083123 : Blo 1825614 3083123 := bstep (se 1 (by rfl) ⟨2312342, by rfl⟩ : syracuseStep 3083123 = 4624685) B4624685
theorem B2739089 : Blo 1825614 2739089 := bstep (se 2 (by rfl) ⟨1027158, by rfl⟩ : syracuseStep 2739089 = 2054317) B2054317
theorem B2739107 : Blo 1825614 2739107 := bstep (se 1 (by rfl) ⟨2054330, by rfl⟩ : syracuseStep 2739107 = 4108661) B4108661
theorem B2739137 : Blo 1825614 2739137 := bstep (se 2 (by rfl) ⟨1027176, by rfl⟩ : syracuseStep 2739137 = 2054353) B2054353
theorem B2739155 : Blo 1825614 2739155 := bstep (se 1 (by rfl) ⟨2054366, by rfl⟩ : syracuseStep 2739155 = 4108733) B4108733
theorem B2739185 : Blo 1825614 2739185 := bstep (se 2 (by rfl) ⟨1027194, by rfl⟩ : syracuseStep 2739185 = 2054389) B2054389
theorem B3083251 : Blo 1825614 3083251 := bstep (se 1 (by rfl) ⟨2312438, by rfl⟩ : syracuseStep 3083251 = 4624877) B4624877
theorem B2739203 : Blo 1825614 2739203 := bstep (se 1 (by rfl) ⟨2054402, by rfl⟩ : syracuseStep 2739203 = 4108805) B4108805
theorem B2739233 : Blo 1825614 2739233 := bstep (se 2 (by rfl) ⟨1027212, by rfl⟩ : syracuseStep 2739233 = 2054425) B2054425
theorem B6163505 : Blo 1825614 6163505 := bstep (se 2 (by rfl) ⟨2311314, by rfl⟩ : syracuseStep 6163505 = 4622629) B4622629
theorem B2739251 : Blo 1825614 2739251 := bstep (se 1 (by rfl) ⟨2054438, by rfl⟩ : syracuseStep 2739251 = 4108877) B4108877
theorem B2739281 : Blo 1825614 2739281 := bstep (se 2 (by rfl) ⟨1027230, by rfl⟩ : syracuseStep 2739281 = 2054461) B2054461
theorem B2739299 : Blo 1825614 2739299 := bstep (se 1 (by rfl) ⟨2054474, by rfl⟩ : syracuseStep 2739299 = 4108949) B4108949
theorem B2739329 : Blo 1825614 2739329 := bstep (se 2 (by rfl) ⟨1027248, by rfl⟩ : syracuseStep 2739329 = 2054497) B2054497
theorem B3083393 : Blo 1825614 3083393 := bstep (se 2 (by rfl) ⟨1156272, by rfl⟩ : syracuseStep 3083393 = 2312545) B2312545
theorem B9251981 : Blo 1825614 9251981 := bstep (se 3 (by rfl) ⟨1734746, by rfl⟩ : syracuseStep 9251981 = 3469493) B3469493
theorem B3124369 : Blo 1825614 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B2739347 : Blo 1825614 2739347 := bstep (se 1 (by rfl) ⟨2054510, by rfl⟩ : syracuseStep 2739347 = 4109021) B4109021
theorem B2469025 : Blo 1825614 2469025 := bstep (se 2 (by rfl) ⟨925884, by rfl⟩ : syracuseStep 2469025 = 1851769) B1851769
theorem B2739377 : Blo 1825614 2739377 := bstep (se 2 (by rfl) ⟨1027266, by rfl⟩ : syracuseStep 2739377 = 2054533) B2054533
theorem B2739395 : Blo 1825614 2739395 := bstep (se 1 (by rfl) ⟨2054546, by rfl⟩ : syracuseStep 2739395 = 4109093) B4109093
theorem B2739425 : Blo 1825614 2739425 := bstep (se 2 (by rfl) ⟨1027284, by rfl⟩ : syracuseStep 2739425 = 2054569) B2054569
theorem B4623601 : Blo 1825614 4623601 := bstep (se 2 (by rfl) ⟨1733850, by rfl⟩ : syracuseStep 4623601 = 3467701) B3467701
theorem B2739443 : Blo 1825614 2739443 := bstep (se 1 (by rfl) ⟨2054582, by rfl⟩ : syracuseStep 2739443 = 4109165) B4109165
theorem B3083521 : Blo 1825614 3083521 := bstep (se 2 (by rfl) ⟨1156320, by rfl⟩ : syracuseStep 3083521 = 2312641) B2312641
theorem B2739473 : Blo 1825614 2739473 := bstep (se 2 (by rfl) ⟨1027302, by rfl⟩ : syracuseStep 2739473 = 2054605) B2054605
theorem B2739491 : Blo 1825614 2739491 := bstep (se 1 (by rfl) ⟨2054618, by rfl⟩ : syracuseStep 2739491 = 4109237) B4109237
theorem B9375011 : Blo 1825614 9375011 := bstep (se 1 (by rfl) ⟨7031258, by rfl⟩ : syracuseStep 9375011 = 14062517) B14062517
theorem B3083555 : Blo 1825614 3083555 := bstep (se 1 (by rfl) ⟨2312666, by rfl⟩ : syracuseStep 3083555 = 4625333) B4625333
theorem B2739521 : Blo 1825614 2739521 := bstep (se 2 (by rfl) ⟨1027320, by rfl⟩ : syracuseStep 2739521 = 2054641) B2054641
theorem B5631299 : Blo 1825614 5631299 := bstep (se 1 (by rfl) ⟨4223474, by rfl⟩ : syracuseStep 5631299 = 8446949) B8446949
theorem B2600275 : Blo 1825614 2600275 := bstep (se 1 (by rfl) ⟨1950206, by rfl⟩ : syracuseStep 2600275 = 3900413) B3900413
theorem B2739539 : Blo 1825614 2739539 := bstep (se 1 (by rfl) ⟨2054654, by rfl⟩ : syracuseStep 2739539 = 4109309) B4109309
theorem B5852515 : Blo 1825614 5852515 := bstep (se 1 (by rfl) ⟨4389386, by rfl⟩ : syracuseStep 5852515 = 8778773) B8778773
theorem B2739569 : Blo 1825614 2739569 := bstep (se 2 (by rfl) ⟨1027338, by rfl⟩ : syracuseStep 2739569 = 2054677) B2054677
theorem B2739587 : Blo 1825614 2739587 := bstep (se 1 (by rfl) ⟨2054690, by rfl⟩ : syracuseStep 2739587 = 4109381) B4109381
theorem B2739617 : Blo 1825614 2739617 := bstep (se 2 (by rfl) ⟨1027356, by rfl⟩ : syracuseStep 2739617 = 2054713) B2054713
theorem B3083683 : Blo 1825614 3083683 := bstep (se 1 (by rfl) ⟨2312762, by rfl⟩ : syracuseStep 3083683 = 4625525) B4625525
theorem B2739635 : Blo 1825614 2739635 := bstep (se 1 (by rfl) ⟨2054726, by rfl⟩ : syracuseStep 2739635 = 4109453) B4109453
theorem B10407365 : Blo 1825614 10407365 := bstep (se 4 (by rfl) ⟨975690, by rfl⟩ : syracuseStep 10407365 = 1951381) B1951381
theorem B2739665 : Blo 1825614 2739665 := bstep (se 2 (by rfl) ⟨1027374, by rfl⟩ : syracuseStep 2739665 = 2054749) B2054749
theorem B2739683 : Blo 1825614 2739683 := bstep (se 1 (by rfl) ⟨2054762, by rfl⟩ : syracuseStep 2739683 = 4109525) B4109525
theorem B4107761 : Blo 1825614 4107761 := bstep (se 2 (by rfl) ⟨1540410, by rfl⟩ : syracuseStep 4107761 = 3080821) B3080821
theorem B2739713 : Blo 1825614 2739713 := bstep (se 2 (by rfl) ⟨1027392, by rfl⟩ : syracuseStep 2739713 = 2054785) B2054785
theorem B4107779 : Blo 1825614 4107779 := bstep (se 1 (by rfl) ⟨3080834, by rfl⟩ : syracuseStep 4107779 = 6161669) B6161669
theorem B4623875 : Blo 1825614 4623875 := bstep (se 1 (by rfl) ⟨3467906, by rfl⟩ : syracuseStep 4623875 = 6935813) B6935813
theorem B6581773 : Blo 1825614 6581773 := bstep (se 3 (by rfl) ⟨1234082, by rfl⟩ : syracuseStep 6581773 = 2468165) B2468165
theorem B2739731 : Blo 1825614 2739731 := bstep (se 1 (by rfl) ⟨2054798, by rfl⟩ : syracuseStep 2739731 = 4109597) B4109597
theorem B2739761 : Blo 1825614 2739761 := bstep (se 2 (by rfl) ⟨1027410, by rfl⟩ : syracuseStep 2739761 = 2054821) B2054821
theorem B3083825 : Blo 1825614 3083825 := bstep (se 2 (by rfl) ⟨1156434, by rfl⟩ : syracuseStep 3083825 = 2312869) B2312869
theorem B2739779 : Blo 1825614 2739779 := bstep (se 1 (by rfl) ⟨2054834, by rfl⟩ : syracuseStep 2739779 = 4109669) B4109669
theorem B6164045 : Blo 1825614 6164045 := bstep (se 3 (by rfl) ⟨1155758, by rfl⟩ : syracuseStep 6164045 = 2311517) B2311517
theorem B2739809 : Blo 1825614 2739809 := bstep (se 2 (by rfl) ⟨1027428, by rfl⟩ : syracuseStep 2739809 = 2054857) B2054857
theorem B2739827 : Blo 1825614 2739827 := bstep (se 1 (by rfl) ⟨2054870, by rfl⟩ : syracuseStep 2739827 = 4109741) B4109741
theorem B6164099 : Blo 1825614 6164099 := bstep (se 1 (by rfl) ⟨4623074, by rfl⟩ : syracuseStep 6164099 = 9246149) B9246149
theorem B6934157 : Blo 1825614 6934157 := bstep (se 3 (by rfl) ⟨1300154, by rfl⟩ : syracuseStep 6934157 = 2600309) B2600309
theorem B2739857 : Blo 1825614 2739857 := bstep (se 2 (by rfl) ⟨1027446, by rfl⟩ : syracuseStep 2739857 = 2054893) B2054893
theorem B2739875 : Blo 1825614 2739875 := bstep (se 1 (by rfl) ⟨2054906, by rfl⟩ : syracuseStep 2739875 = 4109813) B4109813
theorem B3468977 : Blo 1825614 3468977 := bstep (se 2 (by rfl) ⟨1300866, by rfl⟩ : syracuseStep 3468977 = 2601733) B2601733
theorem B3083953 : Blo 1825614 3083953 := bstep (se 2 (by rfl) ⟨1156482, by rfl⟩ : syracuseStep 3083953 = 2312965) B2312965
theorem B2739905 : Blo 1825614 2739905 := bstep (se 2 (by rfl) ⟨1027464, by rfl⟩ : syracuseStep 2739905 = 2054929) B2054929
theorem B4624067 : Blo 1825614 4624067 := bstep (se 1 (by rfl) ⟨3468050, by rfl⟩ : syracuseStep 4624067 = 6936101) B6936101
theorem B2739923 : Blo 1825614 2739923 := bstep (se 1 (by rfl) ⟨2054942, by rfl⟩ : syracuseStep 2739923 = 4109885) B4109885
theorem B3083987 : Blo 1825614 3083987 := bstep (se 1 (by rfl) ⟨2312990, by rfl⟩ : syracuseStep 3083987 = 4625981) B4625981
theorem B20811491 : Blo 1825614 20811491 := bstep (se 1 (by rfl) ⟨15608618, by rfl⟩ : syracuseStep 20811491 = 31217237) B31217237
theorem B2739953 : Blo 1825614 2739953 := bstep (se 2 (by rfl) ⟨1027482, by rfl⟩ : syracuseStep 2739953 = 2054965) B2054965
theorem B2739971 : Blo 1825614 2739971 := bstep (se 1 (by rfl) ⟨2054978, by rfl⟩ : syracuseStep 2739971 = 4109957) B4109957
theorem B4108049 : Blo 1825614 4108049 := bstep (se 2 (by rfl) ⟨1540518, by rfl⟩ : syracuseStep 4108049 = 3081037) B3081037
theorem B2740001 : Blo 1825614 2740001 := bstep (se 2 (by rfl) ⟨1027500, by rfl⟩ : syracuseStep 2740001 = 2055001) B2055001
theorem B4108067 : Blo 1825614 4108067 := bstep (se 1 (by rfl) ⟨3081050, by rfl⟩ : syracuseStep 4108067 = 6162101) B6162101
theorem B2600753 : Blo 1825614 2600753 := bstep (se 2 (by rfl) ⟨975282, by rfl⟩ : syracuseStep 2600753 = 1950565) B1950565
theorem B2740019 : Blo 1825614 2740019 := bstep (se 1 (by rfl) ⟨2055014, by rfl⟩ : syracuseStep 2740019 = 4110029) B4110029
theorem B2740049 : Blo 1825614 2740049 := bstep (se 2 (by rfl) ⟨1027518, by rfl⟩ : syracuseStep 2740049 = 2055037) B2055037
theorem B3338065 : Blo 1825614 3338065 := bstep (se 2 (by rfl) ⟨1251774, by rfl⟩ : syracuseStep 3338065 = 2503549) B2503549
theorem B2740067 : Blo 1825614 2740067 := bstep (se 1 (by rfl) ⟨2055050, by rfl⟩ : syracuseStep 2740067 = 4110101) B4110101
theorem B9244529 : Blo 1825614 9244529 := bstep (se 2 (by rfl) ⟨3466698, by rfl⟩ : syracuseStep 9244529 = 6933397) B6933397
theorem B2740097 : Blo 1825614 2740097 := bstep (se 2 (by rfl) ⟨1027536, by rfl⟩ : syracuseStep 2740097 = 2055073) B2055073
theorem B6164369 : Blo 1825614 6164369 := bstep (se 2 (by rfl) ⟨2311638, by rfl⟩ : syracuseStep 6164369 = 4623277) B4623277
theorem B2740115 : Blo 1825614 2740115 := bstep (se 1 (by rfl) ⟨2055086, by rfl⟩ : syracuseStep 2740115 = 4110173) B4110173
theorem B2600867 : Blo 1825614 2600867 := bstep (se 1 (by rfl) ⟨1950650, by rfl⟩ : syracuseStep 2600867 = 3901301) B3901301
theorem B2740145 : Blo 1825614 2740145 := bstep (se 2 (by rfl) ⟨1027554, by rfl⟩ : syracuseStep 2740145 = 2055109) B2055109
theorem B2740163 : Blo 1825614 2740163 := bstep (se 1 (by rfl) ⟨2055122, by rfl⟩ : syracuseStep 2740163 = 4110245) B4110245
theorem B12496837 : Blo 1825614 12496837 := bstep (se 4 (by rfl) ⟨1171578, by rfl⟩ : syracuseStep 12496837 = 2343157) B2343157
theorem B4935629 : Blo 1825614 4935629 := bstep (se 3 (by rfl) ⟨925430, by rfl⟩ : syracuseStep 4935629 = 1850861) B1850861
theorem B2740193 : Blo 1825614 2740193 := bstep (se 2 (by rfl) ⟨1027572, by rfl⟩ : syracuseStep 2740193 = 2055145) B2055145
theorem B14815217 : Blo 1825614 14815217 := bstep (se 2 (by rfl) ⟨5555706, by rfl⟩ : syracuseStep 14815217 = 11111413) B11111413
theorem B2600947 : Blo 1825614 2600947 := bstep (se 1 (by rfl) ⟨1950710, by rfl⟩ : syracuseStep 2600947 = 3901421) B3901421
theorem B2740211 : Blo 1825614 2740211 := bstep (se 1 (by rfl) ⟨2055158, by rfl⟩ : syracuseStep 2740211 = 4110317) B4110317
theorem B2740241 : Blo 1825614 2740241 := bstep (se 2 (by rfl) ⟨1027590, by rfl⟩ : syracuseStep 2740241 = 2055181) B2055181
theorem B2740259 : Blo 1825614 2740259 := bstep (se 1 (by rfl) ⟨2055194, by rfl⟩ : syracuseStep 2740259 = 4110389) B4110389
theorem B4935725 : Blo 1825614 4935725 := bstep (se 3 (by rfl) ⟨925448, by rfl⟩ : syracuseStep 4935725 = 1850897) B1850897
theorem B4108337 : Blo 1825614 4108337 := bstep (se 2 (by rfl) ⟨1540626, by rfl⟩ : syracuseStep 4108337 = 3081253) B3081253
theorem B3125299 : Blo 1825614 3125299 := bstep (se 1 (by rfl) ⟨2343974, by rfl⟩ : syracuseStep 3125299 = 4687949) B4687949
theorem B2740289 : Blo 1825614 2740289 := bstep (se 2 (by rfl) ⟨1027608, by rfl⟩ : syracuseStep 2740289 = 2055217) B2055217
theorem B4108355 : Blo 1825614 4108355 := bstep (se 1 (by rfl) ⟨3081266, by rfl⟩ : syracuseStep 4108355 = 6162533) B6162533
theorem B2740307 : Blo 1825614 2740307 := bstep (se 1 (by rfl) ⟨2055230, by rfl⟩ : syracuseStep 2740307 = 4110461) B4110461
theorem B2740337 : Blo 1825614 2740337 := bstep (se 2 (by rfl) ⟨1027626, by rfl⟩ : syracuseStep 2740337 = 2055253) B2055253
theorem B17559665 : Blo 1825614 17559665 := bstep (se 2 (by rfl) ⟨6584874, by rfl⟩ : syracuseStep 17559665 = 13169749) B13169749
theorem B2470003 : Blo 1825614 2470003 := bstep (se 1 (by rfl) ⟨1852502, by rfl⟩ : syracuseStep 2470003 = 3705005) B3705005
theorem B2740355 : Blo 1825614 2740355 := bstep (se 1 (by rfl) ⟨2055266, by rfl⟩ : syracuseStep 2740355 = 4110533) B4110533
theorem B2740385 : Blo 1825614 2740385 := bstep (se 2 (by rfl) ⟨1027644, by rfl⟩ : syracuseStep 2740385 = 2055289) B2055289
theorem B2740403 : Blo 1825614 2740403 := bstep (se 1 (by rfl) ⟨2055302, by rfl⟩ : syracuseStep 2740403 = 4110605) B4110605
theorem B22212805 : Blo 1825614 22212805 := bstep (se 4 (by rfl) ⟨2082450, by rfl⟩ : syracuseStep 22212805 = 4164901) B4164901
theorem B3952849 : Blo 1825614 3952849 := bstep (se 2 (by rfl) ⟨1482318, by rfl⟩ : syracuseStep 3952849 = 2964637) B2964637
theorem B2740433 : Blo 1825614 2740433 := bstep (se 2 (by rfl) ⟨1027662, by rfl⟩ : syracuseStep 2740433 = 2055325) B2055325
theorem B2740451 : Blo 1825614 2740451 := bstep (se 1 (by rfl) ⟨2055338, by rfl⟩ : syracuseStep 2740451 = 4110677) B4110677
theorem B2740481 : Blo 1825614 2740481 := bstep (se 2 (by rfl) ⟨1027680, by rfl⟩ : syracuseStep 2740481 = 2055361) B2055361
theorem B2740499 : Blo 1825614 2740499 := bstep (se 1 (by rfl) ⟨2055374, by rfl⟩ : syracuseStep 2740499 = 4110749) B4110749
theorem B2740529 : Blo 1825614 2740529 := bstep (se 2 (by rfl) ⟨1027698, by rfl⟩ : syracuseStep 2740529 = 2055397) B2055397
theorem B2740547 : Blo 1825614 2740547 := bstep (se 1 (by rfl) ⟨2055410, by rfl⟩ : syracuseStep 2740547 = 4110821) B4110821
theorem B4108625 : Blo 1825614 4108625 := bstep (se 2 (by rfl) ⟨1540734, by rfl⟩ : syracuseStep 4108625 = 3081469) B3081469
theorem B2740577 : Blo 1825614 2740577 := bstep (se 2 (by rfl) ⟨1027716, by rfl⟩ : syracuseStep 2740577 = 2055433) B2055433
theorem B4108643 : Blo 1825614 4108643 := bstep (se 1 (by rfl) ⟨3081482, by rfl⟩ : syracuseStep 4108643 = 6162965) B6162965
theorem B2740595 : Blo 1825614 2740595 := bstep (se 1 (by rfl) ⟨2055446, by rfl⟩ : syracuseStep 2740595 = 4110893) B4110893
theorem B3125633 : Blo 1825614 3125633 := bstep (se 2 (by rfl) ⟨1172112, by rfl⟩ : syracuseStep 3125633 = 2344225) B2344225
theorem B2740625 : Blo 1825614 2740625 := bstep (se 2 (by rfl) ⟨1027734, by rfl⟩ : syracuseStep 2740625 = 2055469) B2055469
theorem B2740643 : Blo 1825614 2740643 := bstep (se 1 (by rfl) ⟨2055482, by rfl⟩ : syracuseStep 2740643 = 4110965) B4110965
theorem B6164909 : Blo 1825614 6164909 := bstep (se 3 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 6164909 = 2311841) B2311841
theorem B2740673 : Blo 1825614 2740673 := bstep (se 2 (by rfl) ⟨1027752, by rfl⟩ : syracuseStep 2740673 = 2055505) B2055505
theorem B2740691 : Blo 1825614 2740691 := bstep (se 1 (by rfl) ⟨2055518, by rfl⟩ : syracuseStep 2740691 = 4111037) B4111037
theorem B6164963 : Blo 1825614 6164963 := bstep (se 1 (by rfl) ⟨4623722, by rfl⟩ : syracuseStep 6164963 = 9247445) B9247445
theorem B2740721 : Blo 1825614 2740721 := bstep (se 2 (by rfl) ⟨1027770, by rfl⟩ : syracuseStep 2740721 = 2055541) B2055541
theorem B2740739 : Blo 1825614 2740739 := bstep (se 1 (by rfl) ⟨2055554, by rfl⟩ : syracuseStep 2740739 = 4111109) B4111109
theorem B2601505 : Blo 1825614 2601505 := bstep (se 2 (by rfl) ⟨975564, by rfl⟩ : syracuseStep 2601505 = 1951129) B1951129
theorem B2740769 : Blo 1825614 2740769 := bstep (se 2 (by rfl) ⟨1027788, by rfl⟩ : syracuseStep 2740769 = 2055577) B2055577
theorem B5853745 : Blo 1825614 5853745 := bstep (se 2 (by rfl) ⟨2195154, by rfl⟩ : syracuseStep 5853745 = 4390309) B4390309
theorem B2740787 : Blo 1825614 2740787 := bstep (se 1 (by rfl) ⟨2055590, by rfl⟩ : syracuseStep 2740787 = 4111181) B4111181
theorem B2740817 : Blo 1825614 2740817 := bstep (se 2 (by rfl) ⟨1027806, by rfl⟩ : syracuseStep 2740817 = 2055613) B2055613
theorem B2740835 : Blo 1825614 2740835 := bstep (se 1 (by rfl) ⟨2055626, by rfl⟩ : syracuseStep 2740835 = 4111253) B4111253
theorem B4108913 : Blo 1825614 4108913 := bstep (se 2 (by rfl) ⟨1540842, by rfl⟩ : syracuseStep 4108913 = 3081685) B3081685
theorem B4625009 : Blo 1825614 4625009 := bstep (se 2 (by rfl) ⟨1734378, by rfl⟩ : syracuseStep 4625009 = 3468757) B3468757
theorem B2740865 : Blo 1825614 2740865 := bstep (se 2 (by rfl) ⟨1027824, by rfl⟩ : syracuseStep 2740865 = 2055649) B2055649
theorem B4108931 : Blo 1825614 4108931 := bstep (se 1 (by rfl) ⟨3081698, by rfl⟩ : syracuseStep 4108931 = 6163397) B6163397
theorem B2740883 : Blo 1825614 2740883 := bstep (se 1 (by rfl) ⟨2055662, by rfl⟩ : syracuseStep 2740883 = 4111325) B4111325
theorem B4625059 : Blo 1825614 4625059 := bstep (se 1 (by rfl) ⟨3468794, by rfl⟩ : syracuseStep 4625059 = 6937589) B6937589
theorem B2740913 : Blo 1825614 2740913 := bstep (se 2 (by rfl) ⟨1027842, by rfl⟩ : syracuseStep 2740913 = 2055685) B2055685
theorem B2740931 : Blo 1825614 2740931 := bstep (se 1 (by rfl) ⟨2055698, by rfl⟩ : syracuseStep 2740931 = 4111397) B4111397
theorem B2740961 : Blo 1825614 2740961 := bstep (se 2 (by rfl) ⟨1027860, by rfl⟩ : syracuseStep 2740961 = 2055721) B2055721
theorem B6165233 : Blo 1825614 6165233 := bstep (se 2 (by rfl) ⟨2311962, by rfl⟩ : syracuseStep 6165233 = 4623925) B4623925
theorem B2740979 : Blo 1825614 2740979 := bstep (se 1 (by rfl) ⟨2055734, by rfl⟩ : syracuseStep 2740979 = 4111469) B4111469
theorem B7803661 : Blo 1825614 7803661 := bstep (se 3 (by rfl) ⟨1463186, by rfl⟩ : syracuseStep 7803661 = 2926373) B2926373
theorem B2741009 : Blo 1825614 2741009 := bstep (se 2 (by rfl) ⟨1027878, by rfl⟩ : syracuseStep 2741009 = 2055757) B2055757
theorem B2741027 : Blo 1825614 2741027 := bstep (se 1 (by rfl) ⟨2055770, by rfl⟩ : syracuseStep 2741027 = 4111541) B4111541
theorem B4625201 : Blo 1825614 4625201 := bstep (se 2 (by rfl) ⟨1734450, by rfl⟩ : syracuseStep 4625201 = 3468901) B3468901
theorem B2741057 : Blo 1825614 2741057 := bstep (se 2 (by rfl) ⟨1027896, by rfl⟩ : syracuseStep 2741057 = 2055793) B2055793
theorem B2741075 : Blo 1825614 2741075 := bstep (se 1 (by rfl) ⟨2055806, by rfl⟩ : syracuseStep 2741075 = 4111613) B4111613
theorem B4936547 : Blo 1825614 4936547 := bstep (se 1 (by rfl) ⟨3702410, by rfl⟩ : syracuseStep 4936547 = 7404821) B7404821
theorem B2741105 : Blo 1825614 2741105 := bstep (se 2 (by rfl) ⟨1027914, by rfl⟩ : syracuseStep 2741105 = 2055829) B2055829
theorem B2741123 : Blo 1825614 2741123 := bstep (se 1 (by rfl) ⟨2055842, by rfl⟩ : syracuseStep 2741123 = 4111685) B4111685
theorem B4109201 : Blo 1825614 4109201 := bstep (se 2 (by rfl) ⟨1540950, by rfl⟩ : syracuseStep 4109201 = 3081901) B3081901
theorem B2741153 : Blo 1825614 2741153 := bstep (se 2 (by rfl) ⟨1027932, by rfl⟩ : syracuseStep 2741153 = 2055865) B2055865
theorem B4109219 : Blo 1825614 4109219 := bstep (se 1 (by rfl) ⟨3081914, by rfl⟩ : syracuseStep 4109219 = 6163829) B6163829
theorem B2741171 : Blo 1825614 2741171 := bstep (se 1 (by rfl) ⟨2055878, by rfl⟩ : syracuseStep 2741171 = 4111757) B4111757
theorem B8336333 : Blo 1825614 8336333 := bstep (se 3 (by rfl) ⟨1563062, by rfl⟩ : syracuseStep 8336333 = 3126125) B3126125
theorem B2741201 : Blo 1825614 2741201 := bstep (se 2 (by rfl) ⟨1027950, by rfl⟩ : syracuseStep 2741201 = 2055901) B2055901
theorem B4510691 : Blo 1825614 4510691 := bstep (se 1 (by rfl) ⟨3383018, by rfl⟩ : syracuseStep 4510691 = 6766037) B6766037
theorem B2741219 : Blo 1825614 2741219 := bstep (se 1 (by rfl) ⟨2055914, by rfl⟩ : syracuseStep 2741219 = 4111829) B4111829
theorem B2741249 : Blo 1825614 2741249 := bstep (se 2 (by rfl) ⟨1027968, by rfl⟩ : syracuseStep 2741249 = 2055937) B2055937
theorem B2741267 : Blo 1825614 2741267 := bstep (se 1 (by rfl) ⟨2055950, by rfl⟩ : syracuseStep 2741267 = 4111901) B4111901
theorem B2741297 : Blo 1825614 2741297 := bstep (se 2 (by rfl) ⟨1027986, by rfl⟩ : syracuseStep 2741297 = 2055973) B2055973
theorem B2741315 : Blo 1825614 2741315 := bstep (se 1 (by rfl) ⟨2055986, by rfl⟩ : syracuseStep 2741315 = 4111973) B4111973
theorem B2741345 : Blo 1825614 2741345 := bstep (se 2 (by rfl) ⟨1028004, by rfl⟩ : syracuseStep 2741345 = 2056009) B2056009
theorem B8778851 : Blo 1825614 8778851 := bstep (se 1 (by rfl) ⟨6584138, by rfl⟩ : syracuseStep 8778851 = 13168277) B13168277
theorem B2741363 : Blo 1825614 2741363 := bstep (se 1 (by rfl) ⟨2056022, by rfl⟩ : syracuseStep 2741363 = 4112045) B4112045
theorem B5854349 : Blo 1825614 5854349 := bstep (se 3 (by rfl) ⟨1097690, by rfl⟩ : syracuseStep 5854349 = 2195381) B2195381
theorem B2741393 : Blo 1825614 2741393 := bstep (se 2 (by rfl) ⟨1028022, by rfl⟩ : syracuseStep 2741393 = 2056045) B2056045
theorem B4388003 : Blo 1825614 4388003 := bstep (se 1 (by rfl) ⟨3291002, by rfl⟩ : syracuseStep 4388003 = 6582005) B6582005
theorem B2741411 : Blo 1825614 2741411 := bstep (se 1 (by rfl) ⟨2056058, by rfl⟩ : syracuseStep 2741411 = 4112117) B4112117
theorem B4109489 : Blo 1825614 4109489 := bstep (se 2 (by rfl) ⟨1541058, by rfl⟩ : syracuseStep 4109489 = 3082117) B3082117
theorem B4109507 : Blo 1825614 4109507 := bstep (se 1 (by rfl) ⟨3082130, by rfl⟩ : syracuseStep 4109507 = 6164261) B6164261
theorem B3290339 : Blo 1825614 3290339 := bstep (se 1 (by rfl) ⟨2467754, by rfl⟩ : syracuseStep 3290339 = 4935509) B4935509
theorem B6165773 : Blo 1825614 6165773 := bstep (se 3 (by rfl) ⟨1156082, by rfl⟩ : syracuseStep 6165773 = 2312165) B2312165
theorem B9245987 : Blo 1825614 9245987 := bstep (se 1 (by rfl) ⟨6934490, by rfl⟩ : syracuseStep 9245987 = 13868981) B13868981
theorem B6165827 : Blo 1825614 6165827 := bstep (se 1 (by rfl) ⟨4624370, by rfl⟩ : syracuseStep 6165827 = 9248741) B9248741
theorem B4388195 : Blo 1825614 4388195 := bstep (se 1 (by rfl) ⟨3291146, by rfl⟩ : syracuseStep 4388195 = 6582293) B6582293
theorem B56219021 : Blo 1825614 56219021 := bstep (se 3 (by rfl) ⟨10541066, by rfl⟩ : syracuseStep 56219021 = 21082133) B21082133
theorem B6346129 : Blo 1825614 6346129 := bstep (se 2 (by rfl) ⟨2379798, by rfl⟩ : syracuseStep 6346129 = 4759597) B4759597
theorem B4109777 : Blo 1825614 4109777 := bstep (se 2 (by rfl) ⟨1541166, by rfl⟩ : syracuseStep 4109777 = 3082333) B3082333
theorem B4109795 : Blo 1825614 4109795 := bstep (se 1 (by rfl) ⟨3082346, by rfl⟩ : syracuseStep 4109795 = 6164693) B6164693
theorem B9369101 : Blo 1825614 9369101 := bstep (se 3 (by rfl) ⟨1756706, by rfl⟩ : syracuseStep 9369101 = 3513413) B3513413
theorem B11859533 : Blo 1825614 11859533 := bstep (se 3 (by rfl) ⟨2223662, by rfl⟩ : syracuseStep 11859533 = 4447325) B4447325
theorem B6166097 : Blo 1825614 6166097 := bstep (se 2 (by rfl) ⟨2312286, by rfl⟩ : syracuseStep 6166097 = 4624573) B4624573
theorem B5199491 : Blo 1825614 5199491 := bstep (se 1 (by rfl) ⟨3899618, by rfl⟩ : syracuseStep 5199491 = 7799237) B7799237
theorem B4110065 : Blo 1825614 4110065 := bstep (se 2 (by rfl) ⟨1541274, by rfl⟩ : syracuseStep 4110065 = 3082549) B3082549
theorem B4110083 : Blo 1825614 4110083 := bstep (se 1 (by rfl) ⟨3082562, by rfl⟩ : syracuseStep 4110083 = 6165125) B6165125
theorem B2053939 : Blo 1825614 2053939 := bstep (se 1 (by rfl) ⟨1540454, by rfl⟩ : syracuseStep 2053939 = 3080909) B3080909
theorem B4118417 : Blo 1825614 4118417 := bstep (se 2 (by rfl) ⟨1544406, by rfl⟩ : syracuseStep 4118417 = 3088813) B3088813
theorem B8779697 : Blo 1825614 8779697 := bstep (se 2 (by rfl) ⟨3292386, by rfl⟩ : syracuseStep 8779697 = 6584773) B6584773
theorem B2054083 : Blo 1825614 2054083 := bstep (se 1 (by rfl) ⟨1540562, by rfl⟩ : syracuseStep 2054083 = 3081125) B3081125
theorem B5199821 : Blo 1825614 5199821 := bstep (se 3 (by rfl) ⟨974966, by rfl⟩ : syracuseStep 5199821 = 1949933) B1949933
theorem B7403491 : Blo 1825614 7403491 := bstep (se 1 (by rfl) ⟨5552618, by rfl⟩ : syracuseStep 7403491 = 11105237) B11105237
theorem B4388849 : Blo 1825614 4388849 := bstep (se 2 (by rfl) ⟨1645818, by rfl⟩ : syracuseStep 4388849 = 3291637) B3291637
theorem B5199889 : Blo 1825614 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B4110353 : Blo 1825614 4110353 := bstep (se 2 (by rfl) ⟨1541382, by rfl⟩ : syracuseStep 4110353 = 3082765) B3082765
theorem B4110371 : Blo 1825614 4110371 := bstep (se 1 (by rfl) ⟨3082778, by rfl⟩ : syracuseStep 4110371 = 6165557) B6165557
theorem B9246797 : Blo 1825614 9246797 := bstep (se 3 (by rfl) ⟨1733774, by rfl⟩ : syracuseStep 9246797 = 3467549) B3467549
theorem B2054227 : Blo 1825614 2054227 := bstep (se 1 (by rfl) ⟨1540670, by rfl⟩ : syracuseStep 2054227 = 3081341) B3081341
theorem B13875299 : Blo 1825614 13875299 := bstep (se 1 (by rfl) ⟨10406474, by rfl⟩ : syracuseStep 13875299 = 20812949) B20812949
theorem B6166637 : Blo 1825614 6166637 := bstep (se 3 (by rfl) ⟨1156244, by rfl⟩ : syracuseStep 6166637 = 2312489) B2312489
theorem B6166691 : Blo 1825614 6166691 := bstep (se 1 (by rfl) ⟨4625018, by rfl⟩ : syracuseStep 6166691 = 9250037) B9250037
theorem B2054371 : Blo 1825614 2054371 := bstep (se 1 (by rfl) ⟨1540778, by rfl⟩ : syracuseStep 2054371 = 3081557) B3081557
theorem B16890083 : Blo 1825614 16890083 := bstep (se 1 (by rfl) ⟨12667562, by rfl⟩ : syracuseStep 16890083 = 25335125) B25335125
theorem B15612173 : Blo 1825614 15612173 := bstep (se 3 (by rfl) ⟨2927282, by rfl⟩ : syracuseStep 15612173 = 5854565) B5854565
theorem B5200163 : Blo 1825614 5200163 := bstep (se 1 (by rfl) ⟨3900122, by rfl⟩ : syracuseStep 5200163 = 7800245) B7800245
theorem B4110641 : Blo 1825614 4110641 := bstep (se 2 (by rfl) ⟨1541490, by rfl⟩ : syracuseStep 4110641 = 3082981) B3082981
theorem B4110659 : Blo 1825614 4110659 := bstep (se 1 (by rfl) ⟨3082994, by rfl⟩ : syracuseStep 4110659 = 6165989) B6165989
theorem B8329549 : Blo 1825614 8329549 := bstep (se 3 (by rfl) ⟨1561790, by rfl⟩ : syracuseStep 8329549 = 3123581) B3123581
theorem B2054515 : Blo 1825614 2054515 := bstep (se 1 (by rfl) ⟨1540886, by rfl⟩ : syracuseStep 2054515 = 3081773) B3081773
theorem B15604109 : Blo 1825614 15604109 := bstep (se 3 (by rfl) ⟨2925770, by rfl⟩ : syracuseStep 15604109 = 5851541) B5851541
theorem B6166961 : Blo 1825614 6166961 := bstep (se 2 (by rfl) ⟨2312610, by rfl⟩ : syracuseStep 6166961 = 4625221) B4625221
theorem B6937073 : Blo 1825614 6937073 := bstep (se 2 (by rfl) ⟨2601402, by rfl⟩ : syracuseStep 6937073 = 5202805) B5202805
theorem B2054659 : Blo 1825614 2054659 := bstep (se 1 (by rfl) ⟨1540994, by rfl⟩ : syracuseStep 2054659 = 3081989) B3081989
theorem B4110929 : Blo 1825614 4110929 := bstep (se 2 (by rfl) ⟨1541598, by rfl⟩ : syracuseStep 4110929 = 3083197) B3083197
theorem B4110947 : Blo 1825614 4110947 := bstep (se 1 (by rfl) ⟨3083210, by rfl⟩ : syracuseStep 4110947 = 6166421) B6166421
theorem B2054803 : Blo 1825614 2054803 := bstep (se 1 (by rfl) ⟨1541102, by rfl⟩ : syracuseStep 2054803 = 3082205) B3082205
theorem B9870065 : Blo 1825614 9870065 := bstep (se 2 (by rfl) ⟨3701274, by rfl⟩ : syracuseStep 9870065 = 7402549) B7402549
theorem B4389617 : Blo 1825614 4389617 := bstep (se 2 (by rfl) ⟨1646106, by rfl⟩ : syracuseStep 4389617 = 3292213) B3292213
theorem B2054947 : Blo 1825614 2054947 := bstep (se 1 (by rfl) ⟨1541210, by rfl⟩ : syracuseStep 2054947 = 3082421) B3082421
theorem B7027505 : Blo 1825614 7027505 := bstep (se 2 (by rfl) ⟨2635314, by rfl⟩ : syracuseStep 7027505 = 5270629) B5270629
theorem B1825619 : Blo 1825614 1825619 := bstep (se 1 (by rfl) ⟨1369214, by rfl⟩ : syracuseStep 1825619 = 2738429) B2738429
theorem B1825635 : Blo 1825614 1825635 := bstep (se 1 (by rfl) ⟨1369226, by rfl⟩ : syracuseStep 1825635 = 2738453) B2738453
theorem B15596387 : Blo 1825614 15596387 := bstep (se 1 (by rfl) ⟨11697290, by rfl⟩ : syracuseStep 15596387 = 23394581) B23394581
theorem B4111217 : Blo 1825614 4111217 := bstep (se 2 (by rfl) ⟨1541706, by rfl⟩ : syracuseStep 4111217 = 3083413) B3083413
theorem B1825651 : Blo 1825614 1825651 := bstep (se 1 (by rfl) ⟨1369238, by rfl⟩ : syracuseStep 1825651 = 2738477) B2738477
theorem B1825667 : Blo 1825614 1825667 := bstep (se 1 (by rfl) ⟨1369250, by rfl⟩ : syracuseStep 1825667 = 2738501) B2738501
theorem B4684675 : Blo 1825614 4684675 := bstep (se 1 (by rfl) ⟨3513506, by rfl⟩ : syracuseStep 4684675 = 7027013) B7027013
theorem B4111235 : Blo 1825614 4111235 := bstep (se 1 (by rfl) ⟨3083426, by rfl⟩ : syracuseStep 4111235 = 6166853) B6166853
theorem B26680205 : Blo 1825614 26680205 := bstep (se 3 (by rfl) ⟨5002538, by rfl⟩ : syracuseStep 26680205 = 10005077) B10005077
theorem B1825683 : Blo 1825614 1825683 := bstep (se 1 (by rfl) ⟨1369262, by rfl⟩ : syracuseStep 1825683 = 2738525) B2738525
theorem B1825699 : Blo 1825614 1825699 := bstep (se 1 (by rfl) ⟨1369274, by rfl⟩ : syracuseStep 1825699 = 2738549) B2738549
theorem B1825715 : Blo 1825614 1825715 := bstep (se 1 (by rfl) ⟨1369286, by rfl⟩ : syracuseStep 1825715 = 2738573) B2738573
theorem B2055091 : Blo 1825614 2055091 := bstep (se 1 (by rfl) ⟨1541318, by rfl⟩ : syracuseStep 2055091 = 3082637) B3082637
theorem B1825731 : Blo 1825614 1825731 := bstep (se 1 (by rfl) ⟨1369298, by rfl⟩ : syracuseStep 1825731 = 2738597) B2738597
theorem B6167501 : Blo 1825614 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B1825747 : Blo 1825614 1825747 := bstep (se 1 (by rfl) ⟨1369310, by rfl⟩ : syracuseStep 1825747 = 2738621) B2738621
theorem B1825763 : Blo 1825614 1825763 := bstep (se 1 (by rfl) ⟨1369322, by rfl⟩ : syracuseStep 1825763 = 2738645) B2738645
theorem B8780771 : Blo 1825614 8780771 := bstep (se 1 (by rfl) ⟨6585578, by rfl⟩ : syracuseStep 8780771 = 13171157) B13171157
theorem B1825779 : Blo 1825614 1825779 := bstep (se 1 (by rfl) ⟨1369334, by rfl⟩ : syracuseStep 1825779 = 2738669) B2738669
theorem B1825795 : Blo 1825614 1825795 := bstep (se 1 (by rfl) ⟨1369346, by rfl⟩ : syracuseStep 1825795 = 2738693) B2738693
theorem B6167555 : Blo 1825614 6167555 := bstep (se 1 (by rfl) ⟨4625666, by rfl⟩ : syracuseStep 6167555 = 9251333) B9251333
theorem B1825811 : Blo 1825614 1825811 := bstep (se 1 (by rfl) ⟨1369358, by rfl⟩ : syracuseStep 1825811 = 2738717) B2738717
theorem B1825827 : Blo 1825614 1825827 := bstep (se 1 (by rfl) ⟨1369370, by rfl⟩ : syracuseStep 1825827 = 2738741) B2738741
theorem B1825843 : Blo 1825614 1825843 := bstep (se 1 (by rfl) ⟨1369382, by rfl⟩ : syracuseStep 1825843 = 2738765) B2738765
theorem B1825859 : Blo 1825614 1825859 := bstep (se 1 (by rfl) ⟨1369394, by rfl⟩ : syracuseStep 1825859 = 2738789) B2738789
theorem B2055235 : Blo 1825614 2055235 := bstep (se 1 (by rfl) ⟨1541426, by rfl⟩ : syracuseStep 2055235 = 3082853) B3082853
theorem B1825875 : Blo 1825614 1825875 := bstep (se 1 (by rfl) ⟨1369406, by rfl⟩ : syracuseStep 1825875 = 2738813) B2738813
theorem B1825891 : Blo 1825614 1825891 := bstep (se 1 (by rfl) ⟨1369418, by rfl⟩ : syracuseStep 1825891 = 2738837) B2738837
theorem B5201005 : Blo 1825614 5201005 := bstep (se 3 (by rfl) ⟨975188, by rfl⟩ : syracuseStep 5201005 = 1950377) B1950377
theorem B1825907 : Blo 1825614 1825907 := bstep (se 1 (by rfl) ⟨1369430, by rfl⟩ : syracuseStep 1825907 = 2738861) B2738861
theorem B1825923 : Blo 1825614 1825923 := bstep (se 1 (by rfl) ⟨1369442, by rfl⟩ : syracuseStep 1825923 = 2738885) B2738885
theorem B3701891 : Blo 1825614 3701891 := bstep (se 1 (by rfl) ⟨2776418, by rfl⟩ : syracuseStep 3701891 = 5552837) B5552837
theorem B4111505 : Blo 1825614 4111505 := bstep (se 2 (by rfl) ⟨1541814, by rfl⟩ : syracuseStep 4111505 = 3083629) B3083629
theorem B1825939 : Blo 1825614 1825939 := bstep (se 1 (by rfl) ⟨1369454, by rfl⟩ : syracuseStep 1825939 = 2738909) B2738909
theorem B1825955 : Blo 1825614 1825955 := bstep (se 1 (by rfl) ⟨1369466, by rfl⟩ : syracuseStep 1825955 = 2738933) B2738933
theorem B4111523 : Blo 1825614 4111523 := bstep (se 1 (by rfl) ⟨3083642, by rfl⟩ : syracuseStep 4111523 = 6167285) B6167285
theorem B1825971 : Blo 1825614 1825971 := bstep (se 1 (by rfl) ⟨1369478, by rfl⟩ : syracuseStep 1825971 = 2738957) B2738957
theorem B1825987 : Blo 1825614 1825987 := bstep (se 1 (by rfl) ⟨1369490, by rfl⟩ : syracuseStep 1825987 = 2738981) B2738981
theorem B1826003 : Blo 1825614 1826003 := bstep (se 1 (by rfl) ⟨1369502, by rfl⟩ : syracuseStep 1826003 = 2739005) B2739005
theorem B2055379 : Blo 1825614 2055379 := bstep (se 1 (by rfl) ⟨1541534, by rfl⟩ : syracuseStep 2055379 = 3083069) B3083069
theorem B1826019 : Blo 1825614 1826019 := bstep (se 1 (by rfl) ⟨1369514, by rfl⟩ : syracuseStep 1826019 = 2739029) B2739029
theorem B1826035 : Blo 1825614 1826035 := bstep (se 1 (by rfl) ⟨1369526, by rfl⟩ : syracuseStep 1826035 = 2739053) B2739053
theorem B1826051 : Blo 1825614 1826051 := bstep (se 1 (by rfl) ⟨1369538, by rfl⟩ : syracuseStep 1826051 = 2739077) B2739077
theorem B5201165 : Blo 1825614 5201165 := bstep (se 3 (by rfl) ⟨975218, by rfl⟩ : syracuseStep 5201165 = 1950437) B1950437
theorem B6167825 : Blo 1825614 6167825 := bstep (se 2 (by rfl) ⟨2312934, by rfl⟩ : syracuseStep 6167825 = 4625869) B4625869
theorem B1826067 : Blo 1825614 1826067 := bstep (se 1 (by rfl) ⟨1369550, by rfl⟩ : syracuseStep 1826067 = 2739101) B2739101
theorem B11697443 : Blo 1825614 11697443 := bstep (se 1 (by rfl) ⟨8773082, by rfl⟩ : syracuseStep 11697443 = 17546165) B17546165
theorem B1826083 : Blo 1825614 1826083 := bstep (se 1 (by rfl) ⟨1369562, by rfl⟩ : syracuseStep 1826083 = 2739125) B2739125
theorem B1826099 : Blo 1825614 1826099 := bstep (se 1 (by rfl) ⟨1369574, by rfl⟩ : syracuseStep 1826099 = 2739149) B2739149
theorem B1826115 : Blo 1825614 1826115 := bstep (se 1 (by rfl) ⟨1369586, by rfl⟩ : syracuseStep 1826115 = 2739173) B2739173
theorem B1826131 : Blo 1825614 1826131 := bstep (se 1 (by rfl) ⟨1369598, by rfl⟩ : syracuseStep 1826131 = 2739197) B2739197
theorem B1826147 : Blo 1825614 1826147 := bstep (se 1 (by rfl) ⟨1369610, by rfl⟩ : syracuseStep 1826147 = 2739221) B2739221
theorem B2055523 : Blo 1825614 2055523 := bstep (se 1 (by rfl) ⟨1541642, by rfl⟩ : syracuseStep 2055523 = 3083285) B3083285
theorem B1826163 : Blo 1825614 1826163 := bstep (se 1 (by rfl) ⟨1369622, by rfl⟩ : syracuseStep 1826163 = 2739245) B2739245
theorem B1826179 : Blo 1825614 1826179 := bstep (se 1 (by rfl) ⟨1369634, by rfl⟩ : syracuseStep 1826179 = 2739269) B2739269
theorem B1826195 : Blo 1825614 1826195 := bstep (se 1 (by rfl) ⟨1369646, by rfl⟩ : syracuseStep 1826195 = 2739293) B2739293
theorem B1826211 : Blo 1825614 1826211 := bstep (se 1 (by rfl) ⟨1369658, by rfl⟩ : syracuseStep 1826211 = 2739317) B2739317
theorem B4111793 : Blo 1825614 4111793 := bstep (se 2 (by rfl) ⟨1541922, by rfl⟩ : syracuseStep 4111793 = 3083845) B3083845
theorem B1826227 : Blo 1825614 1826227 := bstep (se 1 (by rfl) ⟨1369670, by rfl⟩ : syracuseStep 1826227 = 2739341) B2739341
theorem B1826243 : Blo 1825614 1826243 := bstep (se 1 (by rfl) ⟨1369682, by rfl⟩ : syracuseStep 1826243 = 2739365) B2739365
theorem B5201347 : Blo 1825614 5201347 := bstep (se 1 (by rfl) ⟨3901010, by rfl⟩ : syracuseStep 5201347 = 7802021) B7802021
theorem B4111811 : Blo 1825614 4111811 := bstep (se 1 (by rfl) ⟨3083858, by rfl⟩ : syracuseStep 4111811 = 6167717) B6167717
theorem B1826259 : Blo 1825614 1826259 := bstep (se 1 (by rfl) ⟨1369694, by rfl⟩ : syracuseStep 1826259 = 2739389) B2739389
theorem B1826275 : Blo 1825614 1826275 := bstep (se 1 (by rfl) ⟨1369706, by rfl⟩ : syracuseStep 1826275 = 2739413) B2739413
theorem B1826291 : Blo 1825614 1826291 := bstep (se 1 (by rfl) ⟨1369718, by rfl⟩ : syracuseStep 1826291 = 2739437) B2739437
theorem B2055667 : Blo 1825614 2055667 := bstep (se 1 (by rfl) ⟨1541750, by rfl⟩ : syracuseStep 2055667 = 3083501) B3083501
theorem B2637299 : Blo 1825614 2637299 := bstep (se 1 (by rfl) ⟨1977974, by rfl⟩ : syracuseStep 2637299 = 3955949) B3955949
theorem B1826307 : Blo 1825614 1826307 := bstep (se 1 (by rfl) ⟨1369730, by rfl⟩ : syracuseStep 1826307 = 2739461) B2739461
theorem B1826323 : Blo 1825614 1826323 := bstep (se 1 (by rfl) ⟨1369742, by rfl⟩ : syracuseStep 1826323 = 2739485) B2739485
theorem B1826339 : Blo 1825614 1826339 := bstep (se 1 (by rfl) ⟨1369754, by rfl⟩ : syracuseStep 1826339 = 2739509) B2739509
theorem B1826355 : Blo 1825614 1826355 := bstep (se 1 (by rfl) ⟨1369766, by rfl⟩ : syracuseStep 1826355 = 2739533) B2739533
theorem B1826371 : Blo 1825614 1826371 := bstep (se 1 (by rfl) ⟨1369778, by rfl⟩ : syracuseStep 1826371 = 2739557) B2739557
theorem B1826387 : Blo 1825614 1826387 := bstep (se 1 (by rfl) ⟨1369790, by rfl⟩ : syracuseStep 1826387 = 2739581) B2739581
theorem B1826403 : Blo 1825614 1826403 := bstep (se 1 (by rfl) ⟨1369802, by rfl⟩ : syracuseStep 1826403 = 2739605) B2739605
theorem B85532273 : Blo 1825614 85532273 := bstep (se 2 (by rfl) ⟨32074602, by rfl⟩ : syracuseStep 85532273 = 64149205) B64149205
theorem B1826419 : Blo 1825614 1826419 := bstep (se 1 (by rfl) ⟨1369814, by rfl⟩ : syracuseStep 1826419 = 2739629) B2739629
theorem B1826435 : Blo 1825614 1826435 := bstep (se 1 (by rfl) ⟨1369826, by rfl⟩ : syracuseStep 1826435 = 2739653) B2739653
theorem B2055811 : Blo 1825614 2055811 := bstep (se 1 (by rfl) ⟨1541858, by rfl⟩ : syracuseStep 2055811 = 3083717) B3083717
theorem B1826451 : Blo 1825614 1826451 := bstep (se 1 (by rfl) ⟨1369838, by rfl⟩ : syracuseStep 1826451 = 2739677) B2739677
theorem B1826467 : Blo 1825614 1826467 := bstep (se 1 (by rfl) ⟨1369850, by rfl⟩ : syracuseStep 1826467 = 2739701) B2739701
theorem B1826483 : Blo 1825614 1826483 := bstep (se 1 (by rfl) ⟨1369862, by rfl⟩ : syracuseStep 1826483 = 2739725) B2739725
theorem B1826499 : Blo 1825614 1826499 := bstep (se 1 (by rfl) ⟨1369874, by rfl⟩ : syracuseStep 1826499 = 2739749) B2739749
theorem B4112081 : Blo 1825614 4112081 := bstep (se 2 (by rfl) ⟨1542030, by rfl⟩ : syracuseStep 4112081 = 3084061) B3084061
theorem B1826515 : Blo 1825614 1826515 := bstep (se 1 (by rfl) ⟨1369886, by rfl⟩ : syracuseStep 1826515 = 2739773) B2739773
theorem B1826531 : Blo 1825614 1826531 := bstep (se 1 (by rfl) ⟨1369898, by rfl⟩ : syracuseStep 1826531 = 2739797) B2739797
theorem B4112099 : Blo 1825614 4112099 := bstep (se 1 (by rfl) ⟨3084074, by rfl⟩ : syracuseStep 4112099 = 6168149) B6168149
theorem B1826547 : Blo 1825614 1826547 := bstep (se 1 (by rfl) ⟨1369910, by rfl⟩ : syracuseStep 1826547 = 2739821) B2739821
theorem B1826563 : Blo 1825614 1826563 := bstep (se 1 (by rfl) ⟨1369922, by rfl⟩ : syracuseStep 1826563 = 2739845) B2739845
theorem B1826579 : Blo 1825614 1826579 := bstep (se 1 (by rfl) ⟨1369934, by rfl⟩ : syracuseStep 1826579 = 2739869) B2739869
theorem B2055955 : Blo 1825614 2055955 := bstep (se 1 (by rfl) ⟨1541966, by rfl⟩ : syracuseStep 2055955 = 3083933) B3083933
theorem B1826595 : Blo 1825614 1826595 := bstep (se 1 (by rfl) ⟨1369946, by rfl⟩ : syracuseStep 1826595 = 2739893) B2739893
theorem B1826611 : Blo 1825614 1826611 := bstep (se 1 (by rfl) ⟨1369958, by rfl⟩ : syracuseStep 1826611 = 2739917) B2739917
theorem B1826627 : Blo 1825614 1826627 := bstep (se 1 (by rfl) ⟨1369970, by rfl⟩ : syracuseStep 1826627 = 2739941) B2739941
theorem B1826643 : Blo 1825614 1826643 := bstep (se 1 (by rfl) ⟨1369982, by rfl⟩ : syracuseStep 1826643 = 2739965) B2739965
theorem B1826659 : Blo 1825614 1826659 := bstep (se 1 (by rfl) ⟨1369994, by rfl⟩ : syracuseStep 1826659 = 2739989) B2739989
theorem B1826675 : Blo 1825614 1826675 := bstep (se 1 (by rfl) ⟨1370006, by rfl⟩ : syracuseStep 1826675 = 2740013) B2740013
theorem B1826691 : Blo 1825614 1826691 := bstep (se 1 (by rfl) ⟨1370018, by rfl⟩ : syracuseStep 1826691 = 2740037) B2740037
theorem B1826707 : Blo 1825614 1826707 := bstep (se 1 (by rfl) ⟨1370030, by rfl⟩ : syracuseStep 1826707 = 2740061) B2740061
theorem B1826723 : Blo 1825614 1826723 := bstep (se 1 (by rfl) ⟨1370042, by rfl⟩ : syracuseStep 1826723 = 2740085) B2740085
theorem B6938531 : Blo 1825614 6938531 := bstep (se 1 (by rfl) ⟨5203898, by rfl⟩ : syracuseStep 6938531 = 10407797) B10407797
theorem B1826739 : Blo 1825614 1826739 := bstep (se 1 (by rfl) ⟨1370054, by rfl⟩ : syracuseStep 1826739 = 2740109) B2740109
theorem B1826755 : Blo 1825614 1826755 := bstep (se 1 (by rfl) ⟨1370066, by rfl⟩ : syracuseStep 1826755 = 2740133) B2740133
theorem B1826771 : Blo 1825614 1826771 := bstep (se 1 (by rfl) ⟨1370078, by rfl⟩ : syracuseStep 1826771 = 2740157) B2740157
theorem B2924515 : Blo 1825614 2924515 := bstep (se 1 (by rfl) ⟨2193386, by rfl⟩ : syracuseStep 2924515 = 4386773) B4386773
theorem B1826787 : Blo 1825614 1826787 := bstep (se 1 (by rfl) ⟨1370090, by rfl⟩ : syracuseStep 1826787 = 2740181) B2740181
theorem B1826803 : Blo 1825614 1826803 := bstep (se 1 (by rfl) ⟨1370102, by rfl⟩ : syracuseStep 1826803 = 2740205) B2740205
theorem B1949707 : Blo 1825614 1949707 := bstep (se 1 (by rfl) ⟨1462280, by rfl⟩ : syracuseStep 1949707 = 2924561) B2924561
theorem B1826827 : Blo 1825614 1826827 := bstep (se 1 (by rfl) ⟨1370120, by rfl⟩ : syracuseStep 1826827 = 2740241) B2740241
theorem B1826839 : Blo 1825614 1826839 := bstep (se 1 (by rfl) ⟨1370129, by rfl⟩ : syracuseStep 1826839 = 2740259) B2740259
theorem B1826859 : Blo 1825614 1826859 := bstep (se 1 (by rfl) ⟨1370144, by rfl⟩ : syracuseStep 1826859 = 2740289) B2740289
theorem B1826871 : Blo 1825614 1826871 := bstep (se 1 (by rfl) ⟨1370153, by rfl⟩ : syracuseStep 1826871 = 2740307) B2740307
theorem B1826891 : Blo 1825614 1826891 := bstep (se 1 (by rfl) ⟨1370168, by rfl⟩ : syracuseStep 1826891 = 2740337) B2740337
theorem B11706443 : Blo 1825614 11706443 := bstep (se 1 (by rfl) ⟨8779832, by rfl⟩ : syracuseStep 11706443 = 17559665) B17559665
theorem B1826903 : Blo 1825614 1826903 := bstep (se 1 (by rfl) ⟨1370177, by rfl⟩ : syracuseStep 1826903 = 2740355) B2740355
theorem B1826923 : Blo 1825614 1826923 := bstep (se 1 (by rfl) ⟨1370192, by rfl⟩ : syracuseStep 1826923 = 2740385) B2740385
theorem B1826935 : Blo 1825614 1826935 := bstep (se 1 (by rfl) ⟨1370201, by rfl⟩ : syracuseStep 1826935 = 2740403) B2740403
theorem B1826955 : Blo 1825614 1826955 := bstep (se 1 (by rfl) ⟨1370216, by rfl⟩ : syracuseStep 1826955 = 2740433) B2740433
theorem B1826967 : Blo 1825614 1826967 := bstep (se 1 (by rfl) ⟨1370225, by rfl⟩ : syracuseStep 1826967 = 2740451) B2740451
theorem B1826987 : Blo 1825614 1826987 := bstep (se 1 (by rfl) ⟨1370240, by rfl⟩ : syracuseStep 1826987 = 2740481) B2740481
theorem B7798963 : Blo 1825614 7798963 := bstep (se 1 (by rfl) ⟨5849222, by rfl⟩ : syracuseStep 7798963 = 11698445) B11698445
theorem B1826999 : Blo 1825614 1826999 := bstep (se 1 (by rfl) ⟨1370249, by rfl⟩ : syracuseStep 1826999 = 2740499) B2740499
theorem B1827019 : Blo 1825614 1827019 := bstep (se 1 (by rfl) ⟨1370264, by rfl⟩ : syracuseStep 1827019 = 2740529) B2740529
theorem B1827031 : Blo 1825614 1827031 := bstep (se 1 (by rfl) ⟨1370273, by rfl⟩ : syracuseStep 1827031 = 2740547) B2740547
theorem B1827051 : Blo 1825614 1827051 := bstep (se 1 (by rfl) ⟨1370288, by rfl⟩ : syracuseStep 1827051 = 2740577) B2740577
theorem B1827063 : Blo 1825614 1827063 := bstep (se 1 (by rfl) ⟨1370297, by rfl⟩ : syracuseStep 1827063 = 2740595) B2740595
theorem B1827083 : Blo 1825614 1827083 := bstep (se 1 (by rfl) ⟨1370312, by rfl⟩ : syracuseStep 1827083 = 2740625) B2740625
theorem B1827095 : Blo 1825614 1827095 := bstep (se 1 (by rfl) ⟨1370321, by rfl⟩ : syracuseStep 1827095 = 2740643) B2740643
theorem B1827115 : Blo 1825614 1827115 := bstep (se 1 (by rfl) ⟨1370336, by rfl⟩ : syracuseStep 1827115 = 2740673) B2740673
theorem B1827127 : Blo 1825614 1827127 := bstep (se 1 (by rfl) ⟨1370345, by rfl⟩ : syracuseStep 1827127 = 2740691) B2740691
theorem B1827147 : Blo 1825614 1827147 := bstep (se 1 (by rfl) ⟨1370360, by rfl⟩ : syracuseStep 1827147 = 2740721) B2740721
theorem B1827159 : Blo 1825614 1827159 := bstep (se 1 (by rfl) ⟨1370369, by rfl⟩ : syracuseStep 1827159 = 2740739) B2740739
theorem B10404197 : Blo 1825614 10404197 := bstep (se 4 (by rfl) ⟨975393, by rfl⟩ : syracuseStep 10404197 = 1950787) B1950787
theorem B1827179 : Blo 1825614 1827179 := bstep (se 1 (by rfl) ⟨1370384, by rfl⟩ : syracuseStep 1827179 = 2740769) B2740769
theorem B1827191 : Blo 1825614 1827191 := bstep (se 1 (by rfl) ⟨1370393, by rfl⟩ : syracuseStep 1827191 = 2740787) B2740787
theorem B1827211 : Blo 1825614 1827211 := bstep (se 1 (by rfl) ⟨1370408, by rfl⟩ : syracuseStep 1827211 = 2740817) B2740817
theorem B1827223 : Blo 1825614 1827223 := bstep (se 1 (by rfl) ⟨1370417, by rfl⟩ : syracuseStep 1827223 = 2740835) B2740835
theorem B1827243 : Blo 1825614 1827243 := bstep (se 1 (by rfl) ⟨1370432, by rfl⟩ : syracuseStep 1827243 = 2740865) B2740865
theorem B1827255 : Blo 1825614 1827255 := bstep (se 1 (by rfl) ⟨1370441, by rfl⟩ : syracuseStep 1827255 = 2740883) B2740883
theorem B1827275 : Blo 1825614 1827275 := bstep (se 1 (by rfl) ⟨1370456, by rfl⟩ : syracuseStep 1827275 = 2740913) B2740913
theorem B1827287 : Blo 1825614 1827287 := bstep (se 1 (by rfl) ⟨1370465, by rfl⟩ : syracuseStep 1827287 = 2740931) B2740931
theorem B1827307 : Blo 1825614 1827307 := bstep (se 1 (by rfl) ⟨1370480, by rfl⟩ : syracuseStep 1827307 = 2740961) B2740961
theorem B1827319 : Blo 1825614 1827319 := bstep (se 1 (by rfl) ⟨1370489, by rfl⟩ : syracuseStep 1827319 = 2740979) B2740979
theorem B1827339 : Blo 1825614 1827339 := bstep (se 1 (by rfl) ⟨1370504, by rfl⟩ : syracuseStep 1827339 = 2741009) B2741009
theorem B1827351 : Blo 1825614 1827351 := bstep (se 1 (by rfl) ⟨1370513, by rfl⟩ : syracuseStep 1827351 = 2741027) B2741027
theorem B1827371 : Blo 1825614 1827371 := bstep (se 1 (by rfl) ⟨1370528, by rfl⟩ : syracuseStep 1827371 = 2741057) B2741057
theorem B13173293 : Blo 1825614 13173293 := bstep (se 3 (by rfl) ⟨2469992, by rfl⟩ : syracuseStep 13173293 = 4939985) B4939985
theorem B1827383 : Blo 1825614 1827383 := bstep (se 1 (by rfl) ⟨1370537, by rfl⟩ : syracuseStep 1827383 = 2741075) B2741075
theorem B1827403 : Blo 1825614 1827403 := bstep (se 1 (by rfl) ⟨1370552, by rfl⟩ : syracuseStep 1827403 = 2741105) B2741105
theorem B1827415 : Blo 1825614 1827415 := bstep (se 1 (by rfl) ⟨1370561, by rfl⟩ : syracuseStep 1827415 = 2741123) B2741123
theorem B8774237 : Blo 1825614 8774237 := bstep (se 3 (by rfl) ⟨1645169, by rfl⟩ : syracuseStep 8774237 = 3290339) B3290339
theorem B13173349 : Blo 1825614 13173349 := bstep (se 4 (by rfl) ⟨1235001, by rfl⟩ : syracuseStep 13173349 = 2470003) B2470003
theorem B1827435 : Blo 1825614 1827435 := bstep (se 1 (by rfl) ⟨1370576, by rfl⟩ : syracuseStep 1827435 = 2741153) B2741153
theorem B1827447 : Blo 1825614 1827447 := bstep (se 1 (by rfl) ⟨1370585, by rfl⟩ : syracuseStep 1827447 = 2741171) B2741171
theorem B35111555 : Blo 1825614 35111555 := bstep (se 1 (by rfl) ⟨26333666, by rfl⟩ : syracuseStep 35111555 = 52667333) B52667333
theorem B1827467 : Blo 1825614 1827467 := bstep (se 1 (by rfl) ⟨1370600, by rfl⟩ : syracuseStep 1827467 = 2741201) B2741201
theorem B3080855 : Blo 1825614 3080855 := bstep (se 1 (by rfl) ⟨2310641, by rfl⟩ : syracuseStep 3080855 = 4621283) B4621283
theorem B3007127 : Blo 1825614 3007127 := bstep (se 1 (by rfl) ⟨2255345, by rfl⟩ : syracuseStep 3007127 = 4510691) B4510691
theorem B1827479 : Blo 1825614 1827479 := bstep (se 1 (by rfl) ⟨1370609, by rfl⟩ : syracuseStep 1827479 = 2741219) B2741219
theorem B1827499 : Blo 1825614 1827499 := bstep (se 1 (by rfl) ⟨1370624, by rfl⟩ : syracuseStep 1827499 = 2741249) B2741249
theorem B3703475 : Blo 1825614 3703475 := bstep (se 1 (by rfl) ⟨2777606, by rfl⟩ : syracuseStep 3703475 = 5555213) B5555213
theorem B1827511 : Blo 1825614 1827511 := bstep (se 1 (by rfl) ⟨1370633, by rfl⟩ : syracuseStep 1827511 = 2741267) B2741267
theorem B2310859 : Blo 1825614 2310859 := bstep (se 1 (by rfl) ⟨1733144, by rfl⟩ : syracuseStep 2310859 = 3466289) B3466289
theorem B1827531 : Blo 1825614 1827531 := bstep (se 1 (by rfl) ⟨1370648, by rfl⟩ : syracuseStep 1827531 = 2741297) B2741297
theorem B1827543 : Blo 1825614 1827543 := bstep (se 1 (by rfl) ⟨1370657, by rfl⟩ : syracuseStep 1827543 = 2741315) B2741315
theorem B1827563 : Blo 1825614 1827563 := bstep (se 1 (by rfl) ⟨1370672, by rfl⟩ : syracuseStep 1827563 = 2741345) B2741345
theorem B1827575 : Blo 1825614 1827575 := bstep (se 1 (by rfl) ⟨1370681, by rfl⟩ : syracuseStep 1827575 = 2741363) B2741363
theorem B3465985 : Blo 1825614 3465985 := bstep (se 2 (by rfl) ⟨1299744, by rfl⟩ : syracuseStep 3465985 = 2599489) B2599489
theorem B1827595 : Blo 1825614 1827595 := bstep (se 1 (by rfl) ⟨1370696, by rfl⟩ : syracuseStep 1827595 = 2741393) B2741393
theorem B3080983 : Blo 1825614 3080983 := bstep (se 1 (by rfl) ⟨2310737, by rfl⟩ : syracuseStep 3080983 = 4621475) B4621475
theorem B2925335 : Blo 1825614 2925335 := bstep (se 1 (by rfl) ⟨2194001, by rfl⟩ : syracuseStep 2925335 = 4388003) B4388003
theorem B1827607 : Blo 1825614 1827607 := bstep (se 1 (by rfl) ⟨1370705, by rfl⟩ : syracuseStep 1827607 = 2741411) B2741411
theorem B4621121 : Blo 1825614 4621121 := bstep (se 2 (by rfl) ⟨1732920, by rfl⟩ : syracuseStep 4621121 = 3465841) B3465841
theorem B37479347 : Blo 1825614 37479347 := bstep (se 1 (by rfl) ⟨28109510, by rfl⟩ : syracuseStep 37479347 = 56219021) B56219021
theorem B10404881 : Blo 1825614 10404881 := bstep (se 2 (by rfl) ⟨3901830, by rfl⟩ : syracuseStep 10404881 = 7803661) B7803661
theorem B7906355 : Blo 1825614 7906355 := bstep (se 1 (by rfl) ⟨5929766, by rfl⟩ : syracuseStep 7906355 = 11859533) B11859533
theorem B3466327 : Blo 1825614 3466327 := bstep (se 1 (by rfl) ⟨2599745, by rfl⟩ : syracuseStep 3466327 = 5199491) B5199491
theorem B59245829 : Blo 1825614 59245829 := bstep (se 4 (by rfl) ⟨5554296, by rfl⟩ : syracuseStep 59245829 = 11108593) B11108593
theorem B2745611 : Blo 1825614 2745611 := bstep (se 1 (by rfl) ⟨2059208, by rfl⟩ : syracuseStep 2745611 = 4118417) B4118417
theorem B6931757 : Blo 1825614 6931757 := bstep (se 3 (by rfl) ⟨1299704, by rfl⟩ : syracuseStep 6931757 = 2599409) B2599409
theorem B3466547 : Blo 1825614 3466547 := bstep (se 1 (by rfl) ⟨2599910, by rfl⟩ : syracuseStep 3466547 = 5199821) B5199821
theorem B3900737 : Blo 1825614 3900737 := bstep (se 2 (by rfl) ⟨1462776, by rfl⟩ : syracuseStep 3900737 = 2925553) B2925553
theorem B2925899 : Blo 1825614 2925899 := bstep (se 1 (by rfl) ⟨2194424, by rfl⟩ : syracuseStep 2925899 = 4388849) B4388849
theorem B4621657 : Blo 1825614 4621657 := bstep (se 2 (by rfl) ⟨1733121, by rfl⟩ : syracuseStep 4621657 = 3466243) B3466243
theorem B3081611 : Blo 1825614 3081611 := bstep (se 1 (by rfl) ⟨2311208, by rfl⟩ : syracuseStep 3081611 = 4622417) B4622417
theorem B7800209 : Blo 1825614 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B9250199 : Blo 1825614 9250199 := bstep (se 1 (by rfl) ⟨6937649, by rfl⟩ : syracuseStep 9250199 = 13875299) B13875299
theorem B6161885 : Blo 1825614 6161885 := bstep (se 3 (by rfl) ⟨1155353, by rfl⟩ : syracuseStep 6161885 = 2310707) B2310707
theorem B3081739 : Blo 1825614 3081739 := bstep (se 1 (by rfl) ⟨2311304, by rfl⟩ : syracuseStep 3081739 = 4622609) B4622609
theorem B3466775 : Blo 1825614 3466775 := bstep (se 1 (by rfl) ⟨2600081, by rfl⟩ : syracuseStep 3466775 = 5200163) B5200163
theorem B2311831 : Blo 1825614 2311831 := bstep (se 1 (by rfl) ⟨1733873, by rfl⟩ : syracuseStep 2311831 = 3467747) B3467747
theorem B3704471 : Blo 1825614 3704471 := bstep (se 1 (by rfl) ⟨2778353, by rfl⟩ : syracuseStep 3704471 = 5556707) B5556707
theorem B3081881 : Blo 1825614 3081881 := bstep (se 2 (by rfl) ⟨1155705, by rfl⟩ : syracuseStep 3081881 = 2311411) B2311411
theorem B20801285 : Blo 1825614 20801285 := bstep (se 4 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 20801285 = 3900241) B3900241
theorem B3467033 : Blo 1825614 3467033 := bstep (se 2 (by rfl) ⟨1300137, by rfl⟩ : syracuseStep 3467033 = 2600275) B2600275
theorem B3082009 : Blo 1825614 3082009 := bstep (se 2 (by rfl) ⟨1155753, by rfl⟩ : syracuseStep 3082009 = 2311507) B2311507
theorem B6580043 : Blo 1825614 6580043 := bstep (se 1 (by rfl) ⟨4935032, by rfl⟩ : syracuseStep 6580043 = 9870065) B9870065
theorem B3901259 : Blo 1825614 3901259 := bstep (se 1 (by rfl) ⟨2925944, by rfl⟩ : syracuseStep 3901259 = 5851889) B5851889
theorem B2926411 : Blo 1825614 2926411 := bstep (se 1 (by rfl) ⟨2194808, by rfl⟩ : syracuseStep 2926411 = 4389617) B4389617
theorem B10397591 : Blo 1825614 10397591 := bstep (se 1 (by rfl) ⟨7798193, by rfl⟩ : syracuseStep 10397591 = 15596387) B15596387
theorem B17786803 : Blo 1825614 17786803 := bstep (se 1 (by rfl) ⟨13340102, by rfl⟩ : syracuseStep 17786803 = 26680205) B26680205
theorem B9242585 : Blo 1825614 9242585 := bstep (se 2 (by rfl) ⟨3465969, by rfl⟩ : syracuseStep 9242585 = 6931939) B6931939
theorem B8775697 : Blo 1825614 8775697 := bstep (se 2 (by rfl) ⟨3290886, by rfl⟩ : syracuseStep 8775697 = 6581773) B6581773
theorem B2467927 : Blo 1825614 2467927 := bstep (se 1 (by rfl) ⟨1850945, by rfl⟩ : syracuseStep 2467927 = 3701891) B3701891
theorem B3467443 : Blo 1825614 3467443 := bstep (se 1 (by rfl) ⟨2600582, by rfl⟩ : syracuseStep 3467443 = 5201165) B5201165
theorem B3754199 : Blo 1825614 3754199 := bstep (se 1 (by rfl) ⟨2815649, by rfl⟩ : syracuseStep 3754199 = 5631299) B5631299
theorem B14813401 : Blo 1825614 14813401 := bstep (se 2 (by rfl) ⟨5555025, by rfl⟩ : syracuseStep 14813401 = 11110051) B11110051
theorem B2738507 : Blo 1825614 2738507 := bstep (se 1 (by rfl) ⟨2053880, by rfl⟩ : syracuseStep 2738507 = 4107761) B4107761
theorem B2738519 : Blo 1825614 2738519 := bstep (se 1 (by rfl) ⟨2053889, by rfl⟩ : syracuseStep 2738519 = 4107779) B4107779
theorem B3082583 : Blo 1825614 3082583 := bstep (se 1 (by rfl) ⟨2311937, by rfl⟩ : syracuseStep 3082583 = 4623875) B4623875
theorem B2738585 : Blo 1825614 2738585 := bstep (se 2 (by rfl) ⟨1026969, by rfl⟩ : syracuseStep 2738585 = 2053939) B2053939
theorem B4622771 : Blo 1825614 4622771 := bstep (se 1 (by rfl) ⟨3467078, by rfl⟩ : syracuseStep 4622771 = 6934157) B6934157
theorem B4450753 : Blo 1825614 4450753 := bstep (se 2 (by rfl) ⟨1669032, by rfl⟩ : syracuseStep 4450753 = 3338065) B3338065
theorem B2312651 : Blo 1825614 2312651 := bstep (se 1 (by rfl) ⟨1734488, by rfl⟩ : syracuseStep 2312651 = 3468977) B3468977
theorem B3082711 : Blo 1825614 3082711 := bstep (se 1 (by rfl) ⟨2312033, by rfl⟩ : syracuseStep 3082711 = 4624067) B4624067
theorem B2738699 : Blo 1825614 2738699 := bstep (se 1 (by rfl) ⟨2054024, by rfl⟩ : syracuseStep 2738699 = 4108049) B4108049
theorem B2738711 : Blo 1825614 2738711 := bstep (se 1 (by rfl) ⟨2054033, by rfl⟩ : syracuseStep 2738711 = 4108067) B4108067
theorem B6163019 : Blo 1825614 6163019 := bstep (se 1 (by rfl) ⟨4622264, by rfl⟩ : syracuseStep 6163019 = 9244529) B9244529
theorem B2738777 : Blo 1825614 2738777 := bstep (se 2 (by rfl) ⟨1027041, by rfl⟩ : syracuseStep 2738777 = 2054083) B2054083
theorem B23415389 : Blo 1825614 23415389 := bstep (se 3 (by rfl) ⟨4390385, by rfl⟩ : syracuseStep 23415389 = 8780771) B8780771
theorem B3467929 : Blo 1825614 3467929 := bstep (se 2 (by rfl) ⟨1300473, by rfl⟩ : syracuseStep 3467929 = 2600947) B2600947
theorem B11709107 : Blo 1825614 11709107 := bstep (se 1 (by rfl) ⟨8781830, by rfl⟩ : syracuseStep 11709107 = 17563661) B17563661
theorem B6933185 : Blo 1825614 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B2738891 : Blo 1825614 2738891 := bstep (se 1 (by rfl) ⟨2054168, by rfl⟩ : syracuseStep 2738891 = 4108337) B4108337
theorem B2738903 : Blo 1825614 2738903 := bstep (se 1 (by rfl) ⟨2054177, by rfl⟩ : syracuseStep 2738903 = 4108355) B4108355
theorem B4623065 : Blo 1825614 4623065 := bstep (se 2 (by rfl) ⟨1733649, by rfl⟩ : syracuseStep 4623065 = 3467299) B3467299
theorem B3123991 : Blo 1825614 3123991 := bstep (se 1 (by rfl) ⟨2342993, by rfl⟩ : syracuseStep 3123991 = 4685987) B4685987
theorem B2599705 : Blo 1825614 2599705 := bstep (se 2 (by rfl) ⟨974889, by rfl⟩ : syracuseStep 2599705 = 1949779) B1949779
theorem B2738969 : Blo 1825614 2738969 := bstep (se 2 (by rfl) ⟨1027113, by rfl⟩ : syracuseStep 2738969 = 2054227) B2054227
theorem B6163289 : Blo 1825614 6163289 := bstep (se 2 (by rfl) ⟨2311233, by rfl⟩ : syracuseStep 6163289 = 4622467) B4622467
theorem B2739083 : Blo 1825614 2739083 := bstep (se 1 (by rfl) ⟨2054312, by rfl⟩ : syracuseStep 2739083 = 4108625) B4108625
theorem B2739095 : Blo 1825614 2739095 := bstep (se 1 (by rfl) ⟨2054321, by rfl⟩ : syracuseStep 2739095 = 4108643) B4108643
theorem B11709335 : Blo 1825614 11709335 := bstep (se 1 (by rfl) ⟨8782001, by rfl⟩ : syracuseStep 11709335 = 17564003) B17564003
theorem B29617073 : Blo 1825614 29617073 := bstep (se 2 (by rfl) ⟨11106402, by rfl⟩ : syracuseStep 29617073 = 22212805) B22212805
theorem B5270465 : Blo 1825614 5270465 := bstep (se 2 (by rfl) ⟨1976424, by rfl⟩ : syracuseStep 5270465 = 3952849) B3952849
theorem B2739161 : Blo 1825614 2739161 := bstep (se 2 (by rfl) ⟨1027185, by rfl⟩ : syracuseStep 2739161 = 2054371) B2054371
theorem B3902489 : Blo 1825614 3902489 := bstep (se 2 (by rfl) ⟨1463433, by rfl⟩ : syracuseStep 3902489 = 2926867) B2926867
theorem B2739275 : Blo 1825614 2739275 := bstep (se 1 (by rfl) ⟨2054456, by rfl⟩ : syracuseStep 2739275 = 4108913) B4108913
theorem B3083339 : Blo 1825614 3083339 := bstep (se 1 (by rfl) ⟨2312504, by rfl⟩ : syracuseStep 3083339 = 4625009) B4625009
theorem B2739287 : Blo 1825614 2739287 := bstep (se 1 (by rfl) ⟨2054465, by rfl⟩ : syracuseStep 2739287 = 4108931) B4108931
theorem B2739353 : Blo 1825614 2739353 := bstep (se 2 (by rfl) ⟨1027257, by rfl⟩ : syracuseStep 2739353 = 2054515) B2054515
theorem B3468491 : Blo 1825614 3468491 := bstep (se 1 (by rfl) ⟨2601368, by rfl⟩ : syracuseStep 3468491 = 5202737) B5202737
theorem B3083467 : Blo 1825614 3083467 := bstep (se 1 (by rfl) ⟨2312600, by rfl⟩ : syracuseStep 3083467 = 4625201) B4625201
theorem B2739467 : Blo 1825614 2739467 := bstep (se 1 (by rfl) ⟨2054600, by rfl⟩ : syracuseStep 2739467 = 4109201) B4109201
theorem B2739479 : Blo 1825614 2739479 := bstep (se 1 (by rfl) ⟨2054609, by rfl⟩ : syracuseStep 2739479 = 4109219) B4109219
theorem B5557555 : Blo 1825614 5557555 := bstep (se 1 (by rfl) ⟨4168166, by rfl⟩ : syracuseStep 5557555 = 8336333) B8336333
theorem B2739545 : Blo 1825614 2739545 := bstep (se 2 (by rfl) ⟨1027329, by rfl⟩ : syracuseStep 2739545 = 2054659) B2054659
theorem B3083609 : Blo 1825614 3083609 := bstep (se 2 (by rfl) ⟨1156353, by rfl⟩ : syracuseStep 3083609 = 2312707) B2312707
theorem B4107635 : Blo 1825614 4107635 := bstep (se 1 (by rfl) ⟨3080726, by rfl⟩ : syracuseStep 4107635 = 6161453) B6161453
theorem B3468673 : Blo 1825614 3468673 := bstep (se 2 (by rfl) ⟨1300752, by rfl⟩ : syracuseStep 3468673 = 2601505) B2601505
theorem B4107671 : Blo 1825614 4107671 := bstep (se 1 (by rfl) ⟨3080753, by rfl⟩ : syracuseStep 4107671 = 6161507) B6161507
theorem B5852567 : Blo 1825614 5852567 := bstep (se 1 (by rfl) ⟨4389425, by rfl⟩ : syracuseStep 5852567 = 8778851) B8778851
theorem B3902899 : Blo 1825614 3902899 := bstep (se 1 (by rfl) ⟨2927174, by rfl⟩ : syracuseStep 3902899 = 5854349) B5854349
theorem B2739659 : Blo 1825614 2739659 := bstep (se 1 (by rfl) ⟨2054744, by rfl⟩ : syracuseStep 2739659 = 4109489) B4109489
theorem B2739671 : Blo 1825614 2739671 := bstep (se 1 (by rfl) ⟨2054753, by rfl⟩ : syracuseStep 2739671 = 4109507) B4109507
theorem B3083737 : Blo 1825614 3083737 := bstep (se 2 (by rfl) ⟨1156401, by rfl⟩ : syracuseStep 3083737 = 2312803) B2312803
theorem B13168133 : Blo 1825614 13168133 := bstep (se 4 (by rfl) ⟨1234512, by rfl⟩ : syracuseStep 13168133 = 2469025) B2469025
theorem B6163991 : Blo 1825614 6163991 := bstep (se 1 (by rfl) ⟨4622993, by rfl⟩ : syracuseStep 6163991 = 9245987) B9245987
theorem B2739737 : Blo 1825614 2739737 := bstep (se 2 (by rfl) ⟨1027401, by rfl⟩ : syracuseStep 2739737 = 2054803) B2054803
theorem B9244205 : Blo 1825614 9244205 := bstep (se 3 (by rfl) ⟨1733288, by rfl⟩ : syracuseStep 9244205 = 3466577) B3466577
theorem B4107851 : Blo 1825614 4107851 := bstep (se 1 (by rfl) ⟨3080888, by rfl⟩ : syracuseStep 4107851 = 6161777) B6161777
theorem B11701853 : Blo 1825614 11701853 := bstep (se 3 (by rfl) ⟨2194097, by rfl⟩ : syracuseStep 11701853 = 4388195) B4388195
theorem B4107905 : Blo 1825614 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B2739851 : Blo 1825614 2739851 := bstep (se 1 (by rfl) ⟨2054888, by rfl⟩ : syracuseStep 2739851 = 4109777) B4109777
theorem B2739863 : Blo 1825614 2739863 := bstep (se 1 (by rfl) ⟨2054897, by rfl⟩ : syracuseStep 2739863 = 4109795) B4109795
theorem B6246067 : Blo 1825614 6246067 := bstep (se 1 (by rfl) ⟨4684550, by rfl⟩ : syracuseStep 6246067 = 9369101) B9369101
theorem B2739929 : Blo 1825614 2739929 := bstep (se 2 (by rfl) ⟨1027473, by rfl⟩ : syracuseStep 2739929 = 2054947) B2054947
theorem B7802669 : Blo 1825614 7802669 := bstep (se 3 (by rfl) ⟨1463000, by rfl⟩ : syracuseStep 7802669 = 2926001) B2926001
theorem B2740043 : Blo 1825614 2740043 := bstep (se 1 (by rfl) ⟨2055032, by rfl⟩ : syracuseStep 2740043 = 4110065) B4110065
theorem B2740055 : Blo 1825614 2740055 := bstep (se 1 (by rfl) ⟨2055041, by rfl⟩ : syracuseStep 2740055 = 4110083) B4110083
theorem B6246233 : Blo 1825614 6246233 := bstep (se 2 (by rfl) ⟨2342337, by rfl⟩ : syracuseStep 6246233 = 4684675) B4684675
theorem B4108121 : Blo 1825614 4108121 := bstep (se 2 (by rfl) ⟨1540545, by rfl⟩ : syracuseStep 4108121 = 3081091) B3081091
theorem B3125081 : Blo 1825614 3125081 := bstep (se 2 (by rfl) ⟨1171905, by rfl⟩ : syracuseStep 3125081 = 2343811) B2343811
theorem B7909271 : Blo 1825614 7909271 := bstep (se 1 (by rfl) ⟨5931953, by rfl⟩ : syracuseStep 7909271 = 11863907) B11863907
theorem B2740121 : Blo 1825614 2740121 := bstep (se 2 (by rfl) ⟨1027545, by rfl⟩ : syracuseStep 2740121 = 2055091) B2055091
theorem B1978283 : Blo 1825614 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B4108211 : Blo 1825614 4108211 := bstep (se 1 (by rfl) ⟨3081158, by rfl⟩ : syracuseStep 4108211 = 6162317) B6162317
theorem B5853131 : Blo 1825614 5853131 := bstep (se 1 (by rfl) ⟨4389848, by rfl⟩ : syracuseStep 5853131 = 8779697) B8779697
theorem B4108247 : Blo 1825614 4108247 := bstep (se 1 (by rfl) ⟨3081185, by rfl⟩ : syracuseStep 4108247 = 6162371) B6162371
theorem B7032797 : Blo 1825614 7032797 := bstep (se 3 (by rfl) ⟨1318649, by rfl⟩ : syracuseStep 7032797 = 2637299) B2637299
theorem B2740235 : Blo 1825614 2740235 := bstep (se 1 (by rfl) ⟨2055176, by rfl⟩ : syracuseStep 2740235 = 4110353) B4110353
theorem B2740247 : Blo 1825614 2740247 := bstep (se 1 (by rfl) ⟨2055185, by rfl⟩ : syracuseStep 2740247 = 4110371) B4110371
theorem B6164531 : Blo 1825614 6164531 := bstep (se 1 (by rfl) ⟨4623398, by rfl⟩ : syracuseStep 6164531 = 9246797) B9246797
theorem B3469387 : Blo 1825614 3469387 := bstep (se 1 (by rfl) ⟨2602040, by rfl⟩ : syracuseStep 3469387 = 5204081) B5204081
theorem B2740313 : Blo 1825614 2740313 := bstep (se 2 (by rfl) ⟨1027617, by rfl⟩ : syracuseStep 2740313 = 2055235) B2055235
theorem B4108427 : Blo 1825614 4108427 := bstep (se 1 (by rfl) ⟨3081320, by rfl⟩ : syracuseStep 4108427 = 6162641) B6162641
theorem B88871053 : Blo 1825614 88871053 := bstep (se 3 (by rfl) ⟨16663322, by rfl⟩ : syracuseStep 88871053 = 33326645) B33326645
theorem B6934673 : Blo 1825614 6934673 := bstep (se 2 (by rfl) ⟨2600502, by rfl⟩ : syracuseStep 6934673 = 5201005) B5201005
theorem B11260055 : Blo 1825614 11260055 := bstep (se 1 (by rfl) ⟨8445041, by rfl⟩ : syracuseStep 11260055 = 16890083) B16890083
theorem B3469463 : Blo 1825614 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B10408115 : Blo 1825614 10408115 := bstep (se 1 (by rfl) ⟨7806086, by rfl⟩ : syracuseStep 10408115 = 15612173) B15612173
theorem B4108481 : Blo 1825614 4108481 := bstep (se 2 (by rfl) ⟨1540680, by rfl⟩ : syracuseStep 4108481 = 3081361) B3081361
theorem B4165825 : Blo 1825614 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B2601163 : Blo 1825614 2601163 := bstep (se 1 (by rfl) ⟨1950872, by rfl⟩ : syracuseStep 2601163 = 3901745) B3901745
theorem B2740427 : Blo 1825614 2740427 := bstep (se 1 (by rfl) ⟨2055320, by rfl⟩ : syracuseStep 2740427 = 4110641) B4110641
theorem B2601175 : Blo 1825614 2601175 := bstep (se 1 (by rfl) ⟨1950881, by rfl⟩ : syracuseStep 2601175 = 3901763) B3901763
theorem B2740439 : Blo 1825614 2740439 := bstep (se 1 (by rfl) ⟨2055329, by rfl⟩ : syracuseStep 2740439 = 4110659) B4110659
theorem B49983749 : Blo 1825614 49983749 := bstep (se 4 (by rfl) ⟨4685976, by rfl⟩ : syracuseStep 49983749 = 9371953) B9371953
theorem B2740505 : Blo 1825614 2740505 := bstep (se 2 (by rfl) ⟨1027689, by rfl⟩ : syracuseStep 2740505 = 2055379) B2055379
theorem B6164801 : Blo 1825614 6164801 := bstep (se 2 (by rfl) ⟨2311800, by rfl⟩ : syracuseStep 6164801 = 4623601) B4623601
theorem B10400075 : Blo 1825614 10400075 := bstep (se 1 (by rfl) ⟨7800056, by rfl⟩ : syracuseStep 10400075 = 15600113) B15600113
theorem B4624715 : Blo 1825614 4624715 := bstep (se 1 (by rfl) ⟨3468536, by rfl⟩ : syracuseStep 4624715 = 6937073) B6937073
theorem B2740619 : Blo 1825614 2740619 := bstep (se 1 (by rfl) ⟨2055464, by rfl⟩ : syracuseStep 2740619 = 4110929) B4110929
theorem B2740631 : Blo 1825614 2740631 := bstep (se 1 (by rfl) ⟨2055473, by rfl⟩ : syracuseStep 2740631 = 4110947) B4110947
theorem B4108697 : Blo 1825614 4108697 := bstep (se 2 (by rfl) ⟨1540761, by rfl⟩ : syracuseStep 4108697 = 3081523) B3081523
theorem B7803353 : Blo 1825614 7803353 := bstep (se 2 (by rfl) ⟨2926257, by rfl⟩ : syracuseStep 7803353 = 5852515) B5852515
theorem B2740697 : Blo 1825614 2740697 := bstep (se 2 (by rfl) ⟨1027761, by rfl⟩ : syracuseStep 2740697 = 2055523) B2055523
theorem B4108787 : Blo 1825614 4108787 := bstep (se 1 (by rfl) ⟨3081590, by rfl⟩ : syracuseStep 4108787 = 6163181) B6163181
theorem B75002381 : Blo 1825614 75002381 := bstep (se 3 (by rfl) ⟨14062946, by rfl⟩ : syracuseStep 75002381 = 28125893) B28125893
theorem B4108823 : Blo 1825614 4108823 := bstep (se 1 (by rfl) ⟨3081617, by rfl⟩ : syracuseStep 4108823 = 6163235) B6163235
theorem B2740811 : Blo 1825614 2740811 := bstep (se 1 (by rfl) ⟨2055608, by rfl⟩ : syracuseStep 2740811 = 4111217) B4111217
theorem B2740823 : Blo 1825614 2740823 := bstep (se 1 (by rfl) ⟨2055617, by rfl⟩ : syracuseStep 2740823 = 4111235) B4111235
theorem B6935129 : Blo 1825614 6935129 := bstep (se 2 (by rfl) ⟨2600673, by rfl⟩ : syracuseStep 6935129 = 5201347) B5201347
theorem B2740889 : Blo 1825614 2740889 := bstep (se 2 (by rfl) ⟨1027833, by rfl⟩ : syracuseStep 2740889 = 2055667) B2055667
theorem B13873841 : Blo 1825614 13873841 := bstep (se 2 (by rfl) ⟨5202690, by rfl⟩ : syracuseStep 13873841 = 10405381) B10405381
theorem B4109003 : Blo 1825614 4109003 := bstep (se 1 (by rfl) ⟨3081752, by rfl⟩ : syracuseStep 4109003 = 6163505) B6163505
theorem B4109057 : Blo 1825614 4109057 := bstep (se 2 (by rfl) ⟨1540896, by rfl⟩ : syracuseStep 4109057 = 3081793) B3081793
theorem B2741003 : Blo 1825614 2741003 := bstep (se 1 (by rfl) ⟨2055752, by rfl⟩ : syracuseStep 2741003 = 4111505) B4111505
theorem B2741015 : Blo 1825614 2741015 := bstep (se 1 (by rfl) ⟨2055761, by rfl⟩ : syracuseStep 2741015 = 4111523) B4111523
theorem B6935341 : Blo 1825614 6935341 := bstep (se 3 (by rfl) ⟨1300376, by rfl⟩ : syracuseStep 6935341 = 2600753) B2600753
theorem B2741081 : Blo 1825614 2741081 := bstep (se 2 (by rfl) ⟨1027905, by rfl⟩ : syracuseStep 2741081 = 2055811) B2055811
theorem B6165341 : Blo 1825614 6165341 := bstep (se 3 (by rfl) ⟨1156001, by rfl⟩ : syracuseStep 6165341 = 2312003) B2312003
theorem B8336321 : Blo 1825614 8336321 := bstep (se 2 (by rfl) ⟨3126120, by rfl⟩ : syracuseStep 8336321 = 6252241) B6252241
theorem B2741195 : Blo 1825614 2741195 := bstep (se 1 (by rfl) ⟨2055896, by rfl⟩ : syracuseStep 2741195 = 4111793) B4111793
theorem B2741207 : Blo 1825614 2741207 := bstep (se 1 (by rfl) ⟨2055905, by rfl⟩ : syracuseStep 2741207 = 4111811) B4111811
theorem B4109273 : Blo 1825614 4109273 := bstep (se 2 (by rfl) ⟨1540977, by rfl⟩ : syracuseStep 4109273 = 3081955) B3081955
theorem B2741273 : Blo 1825614 2741273 := bstep (se 2 (by rfl) ⟨1027977, by rfl⟩ : syracuseStep 2741273 = 2055955) B2055955
theorem B4109363 : Blo 1825614 4109363 := bstep (se 1 (by rfl) ⟨3082022, by rfl⟩ : syracuseStep 4109363 = 6164045) B6164045
theorem B57021515 : Blo 1825614 57021515 := bstep (se 1 (by rfl) ⟨42766136, by rfl⟩ : syracuseStep 57021515 = 85532273) B85532273
theorem B4109399 : Blo 1825614 4109399 := bstep (se 1 (by rfl) ⟨3082049, by rfl⟩ : syracuseStep 4109399 = 6164099) B6164099
theorem B6935645 : Blo 1825614 6935645 := bstep (se 3 (by rfl) ⟨1300433, by rfl⟩ : syracuseStep 6935645 = 2600867) B2600867
theorem B2741387 : Blo 1825614 2741387 := bstep (se 1 (by rfl) ⟨2056040, by rfl⟩ : syracuseStep 2741387 = 4112081) B4112081
theorem B13874327 : Blo 1825614 13874327 := bstep (se 1 (by rfl) ⟨10405745, by rfl⟩ : syracuseStep 13874327 = 20811491) B20811491
theorem B2741399 : Blo 1825614 2741399 := bstep (se 1 (by rfl) ⟨2056049, by rfl⟩ : syracuseStep 2741399 = 4112099) B4112099
theorem B4109579 : Blo 1825614 4109579 := bstep (se 1 (by rfl) ⟨3082184, by rfl⟩ : syracuseStep 4109579 = 6164369) B6164369
theorem B4625687 : Blo 1825614 4625687 := bstep (se 1 (by rfl) ⟨3469265, by rfl⟩ : syracuseStep 4625687 = 6938531) B6938531
theorem B3290419 : Blo 1825614 3290419 := bstep (se 1 (by rfl) ⟨2467814, by rfl⟩ : syracuseStep 3290419 = 4935629) B4935629
theorem B4109633 : Blo 1825614 4109633 := bstep (se 2 (by rfl) ⟨1541112, by rfl⟩ : syracuseStep 4109633 = 3082225) B3082225
theorem B9876811 : Blo 1825614 9876811 := bstep (se 1 (by rfl) ⟨7407608, by rfl⟩ : syracuseStep 9876811 = 14815217) B14815217
theorem B3290483 : Blo 1825614 3290483 := bstep (se 1 (by rfl) ⟨2467862, by rfl⟩ : syracuseStep 3290483 = 4935725) B4935725
theorem B3954071 : Blo 1825614 3954071 := bstep (se 1 (by rfl) ⟨2965553, by rfl⟩ : syracuseStep 3954071 = 5931107) B5931107
theorem B4167065 : Blo 1825614 4167065 := bstep (se 2 (by rfl) ⟨1562649, by rfl⟩ : syracuseStep 4167065 = 3125299) B3125299
theorem B4109849 : Blo 1825614 4109849 := bstep (se 2 (by rfl) ⟨1541193, by rfl⟩ : syracuseStep 4109849 = 3082387) B3082387
theorem B14816843 : Blo 1825614 14816843 := bstep (se 1 (by rfl) ⟨11112632, by rfl⟩ : syracuseStep 14816843 = 22225265) B22225265
theorem B4109939 : Blo 1825614 4109939 := bstep (se 1 (by rfl) ⟨3082454, by rfl⟩ : syracuseStep 4109939 = 6164909) B6164909
theorem B4109975 : Blo 1825614 4109975 := bstep (se 1 (by rfl) ⟨3082481, by rfl⟩ : syracuseStep 4109975 = 6164963) B6164963
theorem B7804619 : Blo 1825614 7804619 := bstep (se 1 (by rfl) ⟨5853464, by rfl⟩ : syracuseStep 7804619 = 11706929) B11706929
theorem B2053867 : Blo 1825614 2053867 := bstep (se 1 (by rfl) ⟨1540400, by rfl⟩ : syracuseStep 2053867 = 3080801) B3080801
theorem B3290881 : Blo 1825614 3290881 := bstep (se 2 (by rfl) ⟨1234080, by rfl⟩ : syracuseStep 3290881 = 2468161) B2468161
theorem B11106065 : Blo 1825614 11106065 := bstep (se 2 (by rfl) ⟨4164774, by rfl⟩ : syracuseStep 11106065 = 8329549) B8329549
theorem B7124753 : Blo 1825614 7124753 := bstep (se 2 (by rfl) ⟨2671782, by rfl⟩ : syracuseStep 7124753 = 5343565) B5343565
theorem B4110155 : Blo 1825614 4110155 := bstep (se 1 (by rfl) ⟨3082616, by rfl⟩ : syracuseStep 4110155 = 6165233) B6165233
theorem B2053975 : Blo 1825614 2053975 := bstep (se 1 (by rfl) ⟨1540481, by rfl⟩ : syracuseStep 2053975 = 3080963) B3080963
theorem B4110209 : Blo 1825614 4110209 := bstep (se 2 (by rfl) ⟨1541328, by rfl⟩ : syracuseStep 4110209 = 3082657) B3082657
theorem B3291031 : Blo 1825614 3291031 := bstep (se 1 (by rfl) ⟨2468273, by rfl⟩ : syracuseStep 3291031 = 4936547) B4936547
theorem B6166475 : Blo 1825614 6166475 := bstep (se 1 (by rfl) ⟨4624856, by rfl⟩ : syracuseStep 6166475 = 9249713) B9249713
theorem B2054155 : Blo 1825614 2054155 := bstep (se 1 (by rfl) ⟨1540616, by rfl⟩ : syracuseStep 2054155 = 3081233) B3081233
theorem B7804993 : Blo 1825614 7804993 := bstep (se 2 (by rfl) ⟨2926872, by rfl⟩ : syracuseStep 7804993 = 5853745) B5853745
theorem B5199947 : Blo 1825614 5199947 := bstep (se 1 (by rfl) ⟨3899960, by rfl⟩ : syracuseStep 5199947 = 7799921) B7799921
theorem B4110425 : Blo 1825614 4110425 := bstep (se 2 (by rfl) ⟨1541409, by rfl⟩ : syracuseStep 4110425 = 3082819) B3082819
theorem B2054263 : Blo 1825614 2054263 := bstep (se 1 (by rfl) ⟨1540697, by rfl⟩ : syracuseStep 2054263 = 3081395) B3081395
theorem B3954839 : Blo 1825614 3954839 := bstep (se 1 (by rfl) ⟨2966129, by rfl⟩ : syracuseStep 3954839 = 5932259) B5932259
theorem B4110515 : Blo 1825614 4110515 := bstep (se 1 (by rfl) ⟨3082886, by rfl⟩ : syracuseStep 4110515 = 6165773) B6165773
theorem B4110551 : Blo 1825614 4110551 := bstep (se 1 (by rfl) ⟨3082913, by rfl⟩ : syracuseStep 4110551 = 6165827) B6165827
theorem B6166745 : Blo 1825614 6166745 := bstep (se 2 (by rfl) ⟨2312529, by rfl⟩ : syracuseStep 6166745 = 4625059) B4625059
theorem B2054443 : Blo 1825614 2054443 := bstep (se 1 (by rfl) ⟨1540832, by rfl⟩ : syracuseStep 2054443 = 3081665) B3081665
theorem B74979701 : Blo 1825614 74979701 := bstep (se 5 (by rfl) ⟨3514673, by rfl⟩ : syracuseStep 74979701 = 7029347) B7029347
theorem B4110731 : Blo 1825614 4110731 := bstep (se 1 (by rfl) ⟨3083048, by rfl⟩ : syracuseStep 4110731 = 6166097) B6166097
theorem B2054551 : Blo 1825614 2054551 := bstep (se 1 (by rfl) ⟨1540913, by rfl⟩ : syracuseStep 2054551 = 3081827) B3081827
theorem B7805335 : Blo 1825614 7805335 := bstep (se 1 (by rfl) ⟨5854001, by rfl⟩ : syracuseStep 7805335 = 11708003) B11708003
theorem B4110785 : Blo 1825614 4110785 := bstep (se 2 (by rfl) ⟨1541544, by rfl⟩ : syracuseStep 4110785 = 3083089) B3083089
theorem B2054731 : Blo 1825614 2054731 := bstep (se 1 (by rfl) ⟨1541048, by rfl⟩ : syracuseStep 2054731 = 3082097) B3082097
theorem B4111001 : Blo 1825614 4111001 := bstep (se 2 (by rfl) ⟨1541625, by rfl⟩ : syracuseStep 4111001 = 3083251) B3083251
theorem B33340085 : Blo 1825614 33340085 := bstep (se 5 (by rfl) ⟨1562816, by rfl⟩ : syracuseStep 33340085 = 3125633) B3125633
theorem B2054839 : Blo 1825614 2054839 := bstep (se 1 (by rfl) ⟨1541129, by rfl⟩ : syracuseStep 2054839 = 3082259) B3082259
theorem B4111091 : Blo 1825614 4111091 := bstep (se 1 (by rfl) ⟨3083318, by rfl⟩ : syracuseStep 4111091 = 6166637) B6166637
theorem B4111127 : Blo 1825614 4111127 := bstep (se 1 (by rfl) ⟨3083345, by rfl⟩ : syracuseStep 4111127 = 6166691) B6166691
theorem B1825623 : Blo 1825614 1825623 := bstep (se 1 (by rfl) ⟨1369217, by rfl⟩ : syracuseStep 1825623 = 2738435) B2738435
theorem B1825643 : Blo 1825614 1825643 := bstep (se 1 (by rfl) ⟨1369232, by rfl⟩ : syracuseStep 1825643 = 2738465) B2738465
theorem B2055019 : Blo 1825614 2055019 := bstep (se 1 (by rfl) ⟨1541264, by rfl⟩ : syracuseStep 2055019 = 3082529) B3082529
theorem B1825655 : Blo 1825614 1825655 := bstep (se 1 (by rfl) ⟨1369241, by rfl⟩ : syracuseStep 1825655 = 2738483) B2738483
theorem B1825675 : Blo 1825614 1825675 := bstep (se 1 (by rfl) ⟨1369256, by rfl⟩ : syracuseStep 1825675 = 2738513) B2738513
theorem B1825687 : Blo 1825614 1825687 := bstep (se 1 (by rfl) ⟨1369265, by rfl⟩ : syracuseStep 1825687 = 2738531) B2738531
theorem B6167447 : Blo 1825614 6167447 := bstep (se 1 (by rfl) ⟨4625585, by rfl⟩ : syracuseStep 6167447 = 9251171) B9251171
theorem B1825707 : Blo 1825614 1825707 := bstep (se 1 (by rfl) ⟨1369280, by rfl⟩ : syracuseStep 1825707 = 2738561) B2738561
theorem B10402739 : Blo 1825614 10402739 := bstep (se 1 (by rfl) ⟨7802054, by rfl⟩ : syracuseStep 10402739 = 15604109) B15604109
theorem B1825719 : Blo 1825614 1825719 := bstep (se 1 (by rfl) ⟨1369289, by rfl⟩ : syracuseStep 1825719 = 2738579) B2738579
theorem B1825739 : Blo 1825614 1825739 := bstep (se 1 (by rfl) ⟨1369304, by rfl⟩ : syracuseStep 1825739 = 2738609) B2738609
theorem B4111307 : Blo 1825614 4111307 := bstep (se 1 (by rfl) ⟨3083480, by rfl⟩ : syracuseStep 4111307 = 6166961) B6166961
theorem B1825751 : Blo 1825614 1825751 := bstep (se 1 (by rfl) ⟨1369313, by rfl⟩ : syracuseStep 1825751 = 2738627) B2738627
theorem B2055127 : Blo 1825614 2055127 := bstep (se 1 (by rfl) ⟨1541345, by rfl⟩ : syracuseStep 2055127 = 3082691) B3082691
theorem B1825771 : Blo 1825614 1825771 := bstep (se 1 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 1825771 = 2738657) B2738657
theorem B1825783 : Blo 1825614 1825783 := bstep (se 1 (by rfl) ⟨1369337, by rfl⟩ : syracuseStep 1825783 = 2738675) B2738675
theorem B4111361 : Blo 1825614 4111361 := bstep (se 2 (by rfl) ⟨1541760, by rfl⟩ : syracuseStep 4111361 = 3083521) B3083521
theorem B1825803 : Blo 1825614 1825803 := bstep (se 1 (by rfl) ⟨1369352, by rfl⟩ : syracuseStep 1825803 = 2738705) B2738705
theorem B1825815 : Blo 1825614 1825815 := bstep (se 1 (by rfl) ⟨1369361, by rfl⟩ : syracuseStep 1825815 = 2738723) B2738723
theorem B1825835 : Blo 1825614 1825835 := bstep (se 1 (by rfl) ⟨1369376, by rfl⟩ : syracuseStep 1825835 = 2738753) B2738753
theorem B1825847 : Blo 1825614 1825847 := bstep (se 1 (by rfl) ⟨1369385, by rfl⟩ : syracuseStep 1825847 = 2738771) B2738771
theorem B1825867 : Blo 1825614 1825867 := bstep (se 1 (by rfl) ⟨1369400, by rfl⟩ : syracuseStep 1825867 = 2738801) B2738801
theorem B1825879 : Blo 1825614 1825879 := bstep (se 1 (by rfl) ⟨1369409, by rfl⟩ : syracuseStep 1825879 = 2738819) B2738819
theorem B1825899 : Blo 1825614 1825899 := bstep (se 1 (by rfl) ⟨1369424, by rfl⟩ : syracuseStep 1825899 = 2738849) B2738849
theorem B1825911 : Blo 1825614 1825911 := bstep (se 1 (by rfl) ⟨1369433, by rfl⟩ : syracuseStep 1825911 = 2738867) B2738867
theorem B1825931 : Blo 1825614 1825931 := bstep (se 1 (by rfl) ⟨1369448, by rfl⟩ : syracuseStep 1825931 = 2738897) B2738897
theorem B2055307 : Blo 1825614 2055307 := bstep (se 1 (by rfl) ⟨1541480, by rfl⟩ : syracuseStep 2055307 = 3082961) B3082961
theorem B1825943 : Blo 1825614 1825943 := bstep (se 1 (by rfl) ⟨1369457, by rfl⟩ : syracuseStep 1825943 = 2738915) B2738915
theorem B1825963 : Blo 1825614 1825963 := bstep (se 1 (by rfl) ⟨1369472, by rfl⟩ : syracuseStep 1825963 = 2738945) B2738945
theorem B1825975 : Blo 1825614 1825975 := bstep (se 1 (by rfl) ⟨1369481, by rfl⟩ : syracuseStep 1825975 = 2738963) B2738963
theorem B8461505 : Blo 1825614 8461505 := bstep (se 2 (by rfl) ⟨3173064, by rfl⟩ : syracuseStep 8461505 = 6346129) B6346129
theorem B4685003 : Blo 1825614 4685003 := bstep (se 1 (by rfl) ⟨3513752, by rfl⟩ : syracuseStep 4685003 = 7027505) B7027505
theorem B1825995 : Blo 1825614 1825995 := bstep (se 1 (by rfl) ⟨1369496, by rfl⟩ : syracuseStep 1825995 = 2738993) B2738993
theorem B1826007 : Blo 1825614 1826007 := bstep (se 1 (by rfl) ⟨1369505, by rfl⟩ : syracuseStep 1826007 = 2739011) B2739011
theorem B4111577 : Blo 1825614 4111577 := bstep (se 2 (by rfl) ⟨1541841, by rfl⟩ : syracuseStep 4111577 = 3083683) B3083683
theorem B1826027 : Blo 1825614 1826027 := bstep (se 1 (by rfl) ⟨1369520, by rfl⟩ : syracuseStep 1826027 = 2739041) B2739041
theorem B1826039 : Blo 1825614 1826039 := bstep (se 1 (by rfl) ⟨1369529, by rfl⟩ : syracuseStep 1826039 = 2739059) B2739059
theorem B2055415 : Blo 1825614 2055415 := bstep (se 1 (by rfl) ⟨1541561, by rfl⟩ : syracuseStep 2055415 = 3083123) B3083123
theorem B1826059 : Blo 1825614 1826059 := bstep (se 1 (by rfl) ⟨1369544, by rfl⟩ : syracuseStep 1826059 = 2739089) B2739089
theorem B1826071 : Blo 1825614 1826071 := bstep (se 1 (by rfl) ⟨1369553, by rfl⟩ : syracuseStep 1826071 = 2739107) B2739107
theorem B1826091 : Blo 1825614 1826091 := bstep (se 1 (by rfl) ⟨1369568, by rfl⟩ : syracuseStep 1826091 = 2739137) B2739137
theorem B4111667 : Blo 1825614 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B1826103 : Blo 1825614 1826103 := bstep (se 1 (by rfl) ⟨1369577, by rfl⟩ : syracuseStep 1826103 = 2739155) B2739155
theorem B1826123 : Blo 1825614 1826123 := bstep (se 1 (by rfl) ⟨1369592, by rfl⟩ : syracuseStep 1826123 = 2739185) B2739185
theorem B1826135 : Blo 1825614 1826135 := bstep (se 1 (by rfl) ⟨1369601, by rfl⟩ : syracuseStep 1826135 = 2739203) B2739203
theorem B4111703 : Blo 1825614 4111703 := bstep (se 1 (by rfl) ⟨3083777, by rfl⟩ : syracuseStep 4111703 = 6167555) B6167555
theorem B9248093 : Blo 1825614 9248093 := bstep (se 3 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 9248093 = 3468035) B3468035
theorem B1826155 : Blo 1825614 1826155 := bstep (se 1 (by rfl) ⟨1369616, by rfl⟩ : syracuseStep 1826155 = 2739233) B2739233
theorem B1826167 : Blo 1825614 1826167 := bstep (se 1 (by rfl) ⟨1369625, by rfl⟩ : syracuseStep 1826167 = 2739251) B2739251
theorem B1826187 : Blo 1825614 1826187 := bstep (se 1 (by rfl) ⟨1369640, by rfl⟩ : syracuseStep 1826187 = 2739281) B2739281
theorem B1826199 : Blo 1825614 1826199 := bstep (se 1 (by rfl) ⟨1369649, by rfl⟩ : syracuseStep 1826199 = 2739299) B2739299
theorem B1826219 : Blo 1825614 1826219 := bstep (se 1 (by rfl) ⟨1369664, by rfl⟩ : syracuseStep 1826219 = 2739329) B2739329
theorem B2055595 : Blo 1825614 2055595 := bstep (se 1 (by rfl) ⟨1541696, by rfl⟩ : syracuseStep 2055595 = 3083393) B3083393
theorem B6167987 : Blo 1825614 6167987 := bstep (se 1 (by rfl) ⟨4625990, by rfl⟩ : syracuseStep 6167987 = 9251981) B9251981
theorem B1826231 : Blo 1825614 1826231 := bstep (se 1 (by rfl) ⟨1369673, by rfl⟩ : syracuseStep 1826231 = 2739347) B2739347
theorem B1826251 : Blo 1825614 1826251 := bstep (se 1 (by rfl) ⟨1369688, by rfl⟩ : syracuseStep 1826251 = 2739377) B2739377
theorem B1826263 : Blo 1825614 1826263 := bstep (se 1 (by rfl) ⟨1369697, by rfl⟩ : syracuseStep 1826263 = 2739395) B2739395
theorem B1826283 : Blo 1825614 1826283 := bstep (se 1 (by rfl) ⟨1369712, by rfl⟩ : syracuseStep 1826283 = 2739425) B2739425
theorem B1826295 : Blo 1825614 1826295 := bstep (se 1 (by rfl) ⟨1369721, by rfl⟩ : syracuseStep 1826295 = 2739443) B2739443
theorem B1826315 : Blo 1825614 1826315 := bstep (se 1 (by rfl) ⟨1369736, by rfl⟩ : syracuseStep 1826315 = 2739473) B2739473
theorem B4111883 : Blo 1825614 4111883 := bstep (se 1 (by rfl) ⟨3083912, by rfl⟩ : syracuseStep 4111883 = 6167825) B6167825
theorem B7798295 : Blo 1825614 7798295 := bstep (se 1 (by rfl) ⟨5848721, by rfl⟩ : syracuseStep 7798295 = 11697443) B11697443
theorem B1826327 : Blo 1825614 1826327 := bstep (se 1 (by rfl) ⟨1369745, by rfl⟩ : syracuseStep 1826327 = 2739491) B2739491
theorem B6250007 : Blo 1825614 6250007 := bstep (se 1 (by rfl) ⟨4687505, by rfl⟩ : syracuseStep 6250007 = 9375011) B9375011
theorem B2055703 : Blo 1825614 2055703 := bstep (se 1 (by rfl) ⟨1541777, by rfl⟩ : syracuseStep 2055703 = 3083555) B3083555
theorem B1826347 : Blo 1825614 1826347 := bstep (se 1 (by rfl) ⟨1369760, by rfl⟩ : syracuseStep 1826347 = 2739521) B2739521
theorem B1826359 : Blo 1825614 1826359 := bstep (se 1 (by rfl) ⟨1369769, by rfl⟩ : syracuseStep 1826359 = 2739539) B2739539
theorem B4111937 : Blo 1825614 4111937 := bstep (se 2 (by rfl) ⟨1541976, by rfl⟩ : syracuseStep 4111937 = 3083953) B3083953
theorem B1826379 : Blo 1825614 1826379 := bstep (se 1 (by rfl) ⟨1369784, by rfl⟩ : syracuseStep 1826379 = 2739569) B2739569
theorem B1826391 : Blo 1825614 1826391 := bstep (se 1 (by rfl) ⟨1369793, by rfl⟩ : syracuseStep 1826391 = 2739587) B2739587
theorem B1826411 : Blo 1825614 1826411 := bstep (se 1 (by rfl) ⟨1369808, by rfl⟩ : syracuseStep 1826411 = 2739617) B2739617
theorem B1826423 : Blo 1825614 1826423 := bstep (se 1 (by rfl) ⟨1369817, by rfl⟩ : syracuseStep 1826423 = 2739635) B2739635
theorem B6938243 : Blo 1825614 6938243 := bstep (se 1 (by rfl) ⟨5203682, by rfl⟩ : syracuseStep 6938243 = 10407365) B10407365
theorem B1826443 : Blo 1825614 1826443 := bstep (se 1 (by rfl) ⟨1369832, by rfl⟩ : syracuseStep 1826443 = 2739665) B2739665
theorem B6938257 : Blo 1825614 6938257 := bstep (se 2 (by rfl) ⟨2601846, by rfl⟩ : syracuseStep 6938257 = 5203693) B5203693
theorem B1826455 : Blo 1825614 1826455 := bstep (se 1 (by rfl) ⟨1369841, by rfl⟩ : syracuseStep 1826455 = 2739683) B2739683
theorem B1826475 : Blo 1825614 1826475 := bstep (se 1 (by rfl) ⟨1369856, by rfl⟩ : syracuseStep 1826475 = 2739713) B2739713
theorem B1826487 : Blo 1825614 1826487 := bstep (se 1 (by rfl) ⟨1369865, by rfl⟩ : syracuseStep 1826487 = 2739731) B2739731
theorem B1826507 : Blo 1825614 1826507 := bstep (se 1 (by rfl) ⟨1369880, by rfl⟩ : syracuseStep 1826507 = 2739761) B2739761
theorem B2055883 : Blo 1825614 2055883 := bstep (se 1 (by rfl) ⟨1541912, by rfl⟩ : syracuseStep 2055883 = 3083825) B3083825
theorem B1826519 : Blo 1825614 1826519 := bstep (se 1 (by rfl) ⟨1369889, by rfl⟩ : syracuseStep 1826519 = 2739779) B2739779
theorem B1826539 : Blo 1825614 1826539 := bstep (se 1 (by rfl) ⟨1369904, by rfl⟩ : syracuseStep 1826539 = 2739809) B2739809
theorem B1826551 : Blo 1825614 1826551 := bstep (se 1 (by rfl) ⟨1369913, by rfl⟩ : syracuseStep 1826551 = 2739827) B2739827
theorem B1826571 : Blo 1825614 1826571 := bstep (se 1 (by rfl) ⟨1369928, by rfl⟩ : syracuseStep 1826571 = 2739857) B2739857
theorem B1826583 : Blo 1825614 1826583 := bstep (se 1 (by rfl) ⟨1369937, by rfl⟩ : syracuseStep 1826583 = 2739875) B2739875
theorem B1826603 : Blo 1825614 1826603 := bstep (se 1 (by rfl) ⟨1369952, by rfl⟩ : syracuseStep 1826603 = 2739905) B2739905
theorem B7716653 : Blo 1825614 7716653 := bstep (se 3 (by rfl) ⟨1446872, by rfl⟩ : syracuseStep 7716653 = 2893745) B2893745
theorem B1826615 : Blo 1825614 1826615 := bstep (se 1 (by rfl) ⟨1369961, by rfl⟩ : syracuseStep 1826615 = 2739923) B2739923
theorem B2055991 : Blo 1825614 2055991 := bstep (se 1 (by rfl) ⟨1541993, by rfl⟩ : syracuseStep 2055991 = 3083987) B3083987
theorem B1826635 : Blo 1825614 1826635 := bstep (se 1 (by rfl) ⟨1369976, by rfl⟩ : syracuseStep 1826635 = 2739953) B2739953
theorem B1826647 : Blo 1825614 1826647 := bstep (se 1 (by rfl) ⟨1369985, by rfl⟩ : syracuseStep 1826647 = 2739971) B2739971
theorem B1826667 : Blo 1825614 1826667 := bstep (se 1 (by rfl) ⟨1370000, by rfl⟩ : syracuseStep 1826667 = 2740001) B2740001
theorem B1826679 : Blo 1825614 1826679 := bstep (se 1 (by rfl) ⟨1370009, by rfl⟩ : syracuseStep 1826679 = 2740019) B2740019
theorem B1826699 : Blo 1825614 1826699 := bstep (se 1 (by rfl) ⟨1370024, by rfl⟩ : syracuseStep 1826699 = 2740049) B2740049
theorem B1826711 : Blo 1825614 1826711 := bstep (se 1 (by rfl) ⟨1370033, by rfl⟩ : syracuseStep 1826711 = 2740067) B2740067
theorem B1826731 : Blo 1825614 1826731 := bstep (se 1 (by rfl) ⟨1370048, by rfl⟩ : syracuseStep 1826731 = 2740097) B2740097
theorem B16662449 : Blo 1825614 16662449 := bstep (se 2 (by rfl) ⟨6248418, by rfl⟩ : syracuseStep 16662449 = 12496837) B12496837
theorem B1826743 : Blo 1825614 1826743 := bstep (se 1 (by rfl) ⟨1370057, by rfl⟩ : syracuseStep 1826743 = 2740115) B2740115
theorem B6938561 : Blo 1825614 6938561 := bstep (se 2 (by rfl) ⟨2601960, by rfl⟩ : syracuseStep 6938561 = 5203921) B5203921
theorem B1826763 : Blo 1825614 1826763 := bstep (se 1 (by rfl) ⟨1370072, by rfl⟩ : syracuseStep 1826763 = 2740145) B2740145
theorem B1826775 : Blo 1825614 1826775 := bstep (se 1 (by rfl) ⟨1370081, by rfl⟩ : syracuseStep 1826775 = 2740163) B2740163
theorem B3899353 : Blo 1825614 3899353 := bstep (se 2 (by rfl) ⟨1462257, by rfl⟩ : syracuseStep 3899353 = 2924515) B2924515
theorem B9871321 : Blo 1825614 9871321 := bstep (se 2 (by rfl) ⟨3701745, by rfl⟩ : syracuseStep 9871321 = 7403491) B7403491
theorem B1826795 : Blo 1825614 1826795 := bstep (se 1 (by rfl) ⟨1370096, by rfl⟩ : syracuseStep 1826795 = 2740193) B2740193
theorem B1826807 : Blo 1825614 1826807 := bstep (se 1 (by rfl) ⟨1370105, by rfl⟩ : syracuseStep 1826807 = 2740211) B2740211
theorem B1826823 : Blo 1825614 1826823 := bstep (se 1 (by rfl) ⟨1370117, by rfl⟩ : syracuseStep 1826823 = 2740235) B2740235
theorem B1826831 : Blo 1825614 1826831 := bstep (se 1 (by rfl) ⟨1370123, by rfl⟩ : syracuseStep 1826831 = 2740247) B2740247
theorem B1826875 : Blo 1825614 1826875 := bstep (se 1 (by rfl) ⟨1370156, by rfl⟩ : syracuseStep 1826875 = 2740313) B2740313
theorem B6938743 : Blo 1825614 6938743 := bstep (se 1 (by rfl) ⟨5204057, by rfl⟩ : syracuseStep 6938743 = 10408115) B10408115
theorem B1826951 : Blo 1825614 1826951 := bstep (se 1 (by rfl) ⟨1370213, by rfl⟩ : syracuseStep 1826951 = 2740427) B2740427
theorem B1826959 : Blo 1825614 1826959 := bstep (se 1 (by rfl) ⟨1370219, by rfl⟩ : syracuseStep 1826959 = 2740439) B2740439
theorem B1827003 : Blo 1825614 1827003 := bstep (se 1 (by rfl) ⟨1370252, by rfl⟩ : syracuseStep 1827003 = 2740505) B2740505
theorem B5554433 : Blo 1825614 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B1827079 : Blo 1825614 1827079 := bstep (se 1 (by rfl) ⟨1370309, by rfl⟩ : syracuseStep 1827079 = 2740619) B2740619
theorem B1827087 : Blo 1825614 1827087 := bstep (se 1 (by rfl) ⟨1370315, by rfl⟩ : syracuseStep 1827087 = 2740631) B2740631
theorem B19751201 : Blo 1825614 19751201 := bstep (se 2 (by rfl) ⟨7406700, by rfl⟩ : syracuseStep 19751201 = 14813401) B14813401
theorem B5202235 : Blo 1825614 5202235 := bstep (se 1 (by rfl) ⟨3901676, by rfl⟩ : syracuseStep 5202235 = 7803353) B7803353
theorem B1827131 : Blo 1825614 1827131 := bstep (se 1 (by rfl) ⟨1370348, by rfl⟩ : syracuseStep 1827131 = 2740697) B2740697
theorem B8782195 : Blo 1825614 8782195 := bstep (se 1 (by rfl) ⟨6586646, by rfl⟩ : syracuseStep 8782195 = 13173293) B13173293
theorem B1827207 : Blo 1825614 1827207 := bstep (se 1 (by rfl) ⟨1370405, by rfl⟩ : syracuseStep 1827207 = 2740811) B2740811
theorem B1827215 : Blo 1825614 1827215 := bstep (se 1 (by rfl) ⟨1370411, by rfl⟩ : syracuseStep 1827215 = 2740823) B2740823
theorem B5849491 : Blo 1825614 5849491 := bstep (se 1 (by rfl) ⟨4387118, by rfl⟩ : syracuseStep 5849491 = 8774237) B8774237
theorem B1827259 : Blo 1825614 1827259 := bstep (se 1 (by rfl) ⟨1370444, by rfl⟩ : syracuseStep 1827259 = 2740889) B2740889
theorem B9249227 : Blo 1825614 9249227 := bstep (se 1 (by rfl) ⟨6936920, by rfl⟩ : syracuseStep 9249227 = 13873841) B13873841
theorem B1827335 : Blo 1825614 1827335 := bstep (se 1 (by rfl) ⟨1370501, by rfl⟩ : syracuseStep 1827335 = 2741003) B2741003
theorem B1827343 : Blo 1825614 1827343 := bstep (se 1 (by rfl) ⟨1370507, by rfl⟩ : syracuseStep 1827343 = 2741015) B2741015
theorem B3080747 : Blo 1825614 3080747 := bstep (se 1 (by rfl) ⟨2310560, by rfl⟩ : syracuseStep 3080747 = 4621121) B4621121
theorem B1827387 : Blo 1825614 1827387 := bstep (se 1 (by rfl) ⟨1370540, by rfl⟩ : syracuseStep 1827387 = 2741081) B2741081
theorem B24986231 : Blo 1825614 24986231 := bstep (se 1 (by rfl) ⟨18739673, by rfl⟩ : syracuseStep 24986231 = 37479347) B37479347
theorem B1827463 : Blo 1825614 1827463 := bstep (se 1 (by rfl) ⟨1370597, by rfl⟩ : syracuseStep 1827463 = 2741195) B2741195
theorem B1827471 : Blo 1825614 1827471 := bstep (se 1 (by rfl) ⟨1370603, by rfl⟩ : syracuseStep 1827471 = 2741207) B2741207
theorem B1827515 : Blo 1825614 1827515 := bstep (se 1 (by rfl) ⟨1370636, by rfl⟩ : syracuseStep 1827515 = 2741273) B2741273
theorem B1827591 : Blo 1825614 1827591 := bstep (se 1 (by rfl) ⟨1370693, by rfl⟩ : syracuseStep 1827591 = 2741387) B2741387
theorem B9249551 : Blo 1825614 9249551 := bstep (se 1 (by rfl) ⟨6937163, by rfl⟩ : syracuseStep 9249551 = 13874327) B13874327
theorem B1827599 : Blo 1825614 1827599 := bstep (se 1 (by rfl) ⟨1370699, by rfl⟩ : syracuseStep 1827599 = 2741399) B2741399
theorem B17564465 : Blo 1825614 17564465 := bstep (se 2 (by rfl) ⟨6586674, by rfl⟩ : syracuseStep 17564465 = 13173349) B13173349
theorem B4621171 : Blo 1825614 4621171 := bstep (se 1 (by rfl) ⟨3465878, by rfl⟩ : syracuseStep 4621171 = 6931757) B6931757
theorem B2311031 : Blo 1825614 2311031 := bstep (se 1 (by rfl) ⟨1733273, by rfl⟩ : syracuseStep 2311031 = 3466547) B3466547
theorem B1950599 : Blo 1825614 1950599 := bstep (se 1 (by rfl) ⟨1462949, by rfl⟩ : syracuseStep 1950599 = 2925899) B2925899
theorem B3081145 : Blo 1825614 3081145 := bstep (se 2 (by rfl) ⟨1155429, by rfl⟩ : syracuseStep 3081145 = 2310859) B2310859
theorem B2778043 : Blo 1825614 2778043 := bstep (se 1 (by rfl) ⟨2083532, by rfl⟩ : syracuseStep 2778043 = 4167065) B4167065
theorem B8774621 : Blo 1825614 8774621 := bstep (se 3 (by rfl) ⟨1645241, by rfl⟩ : syracuseStep 8774621 = 3290483) B3290483
theorem B4621313 : Blo 1825614 4621313 := bstep (se 2 (by rfl) ⟨1732992, by rfl⟩ : syracuseStep 4621313 = 3465985) B3465985
theorem B2311183 : Blo 1825614 2311183 := bstep (se 1 (by rfl) ⟨1733387, by rfl⟩ : syracuseStep 2311183 = 3466775) B3466775
theorem B5203079 : Blo 1825614 5203079 := bstep (se 1 (by rfl) ⟨3902309, by rfl⟩ : syracuseStep 5203079 = 7804619) B7804619
theorem B2311355 : Blo 1825614 2311355 := bstep (se 1 (by rfl) ⟨1733516, by rfl⟩ : syracuseStep 2311355 = 3467033) B3467033
theorem B6931727 : Blo 1825614 6931727 := bstep (se 1 (by rfl) ⟨5198795, by rfl⟩ : syracuseStep 6931727 = 10397591) B10397591
theorem B6161723 : Blo 1825614 6161723 := bstep (se 1 (by rfl) ⟨4621292, by rfl⟩ : syracuseStep 6161723 = 9242585) B9242585
theorem B3466631 : Blo 1825614 3466631 := bstep (se 1 (by rfl) ⟨2599973, by rfl⟩ : syracuseStep 3466631 = 5199947) B5199947
theorem B4621769 : Blo 1825614 4621769 := bstep (se 2 (by rfl) ⟨1733163, by rfl⟩ : syracuseStep 4621769 = 3466327) B3466327
theorem B29640293 : Blo 1825614 29640293 := bstep (se 4 (by rfl) ⟨2778777, by rfl⟩ : syracuseStep 29640293 = 5557555) B5557555
theorem B3081847 : Blo 1825614 3081847 := bstep (se 1 (by rfl) ⟨2311385, by rfl⟩ : syracuseStep 3081847 = 4622771) B4622771
theorem B15607525 : Blo 1825614 15607525 := bstep (se 4 (by rfl) ⟨1463205, by rfl⟩ : syracuseStep 15607525 = 2926411) B2926411
theorem B6162209 : Blo 1825614 6162209 := bstep (se 2 (by rfl) ⟨2310828, by rfl⟩ : syracuseStep 6162209 = 4621657) B4621657
theorem B22226723 : Blo 1825614 22226723 := bstep (se 1 (by rfl) ⟨16670042, by rfl⟩ : syracuseStep 22226723 = 33340085) B33340085
theorem B4622123 : Blo 1825614 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B3082043 : Blo 1825614 3082043 := bstep (se 1 (by rfl) ⟨2311532, by rfl⟩ : syracuseStep 3082043 = 4623065) B4623065
theorem B5203865 : Blo 1825614 5203865 := bstep (se 2 (by rfl) ⟨1951449, by rfl⟩ : syracuseStep 5203865 = 3902899) B3902899
theorem B19744715 : Blo 1825614 19744715 := bstep (se 1 (by rfl) ⟨14808536, by rfl⟩ : syracuseStep 19744715 = 29617073) B29617073
theorem B18999341 : Blo 1825614 18999341 := bstep (se 3 (by rfl) ⟨3562376, by rfl⟩ : syracuseStep 18999341 = 7124753) B7124753
theorem B7800893 : Blo 1825614 7800893 := bstep (se 3 (by rfl) ⟨1462667, by rfl⟩ : syracuseStep 7800893 = 2925335) B2925335
theorem B3123335 : Blo 1825614 3123335 := bstep (se 1 (by rfl) ⟨2342501, by rfl⟩ : syracuseStep 3123335 = 4685003) B4685003
theorem B2312327 : Blo 1825614 2312327 := bstep (se 1 (by rfl) ⟨1734245, by rfl⟩ : syracuseStep 2312327 = 3468491) B3468491
theorem B9251009 : Blo 1825614 9251009 := bstep (se 2 (by rfl) ⟨3469128, by rfl⟩ : syracuseStep 9251009 = 6938257) B6938257
theorem B3082441 : Blo 1825614 3082441 := bstep (se 2 (by rfl) ⟨1155915, by rfl⟩ : syracuseStep 3082441 = 2311831) B2311831
theorem B8333549 : Blo 1825614 8333549 := bstep (se 3 (by rfl) ⟨1562540, by rfl⟩ : syracuseStep 8333549 = 3125081) B3125081
theorem B2738423 : Blo 1825614 2738423 := bstep (se 1 (by rfl) ⟨2053817, by rfl⟩ : syracuseStep 2738423 = 4107635) B4107635
theorem B2738447 : Blo 1825614 2738447 := bstep (se 1 (by rfl) ⟨2053835, by rfl⟩ : syracuseStep 2738447 = 4107671) B4107671
theorem B3901711 : Blo 1825614 3901711 := bstep (se 1 (by rfl) ⟨2926283, by rfl⟩ : syracuseStep 3901711 = 5852567) B5852567
theorem B2738489 : Blo 1825614 2738489 := bstep (se 2 (by rfl) ⟨1026933, by rfl⟩ : syracuseStep 2738489 = 2053867) B2053867
theorem B6162803 : Blo 1825614 6162803 := bstep (se 1 (by rfl) ⟨4622102, by rfl⟩ : syracuseStep 6162803 = 9244205) B9244205
theorem B2738567 : Blo 1825614 2738567 := bstep (se 1 (by rfl) ⟨2053925, by rfl⟩ : syracuseStep 2738567 = 4107851) B4107851
theorem B7801235 : Blo 1825614 7801235 := bstep (se 1 (by rfl) ⟨5850926, by rfl⟩ : syracuseStep 7801235 = 11701853) B11701853
theorem B2738603 : Blo 1825614 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B2738633 : Blo 1825614 2738633 := bstep (se 2 (by rfl) ⟨1026987, by rfl⟩ : syracuseStep 2738633 = 2053975) B2053975
theorem B4164155 : Blo 1825614 4164155 := bstep (se 1 (by rfl) ⟨3123116, by rfl⟩ : syracuseStep 4164155 = 6246233) B6246233
theorem B2738747 : Blo 1825614 2738747 := bstep (se 1 (by rfl) ⟨2054060, by rfl⟩ : syracuseStep 2738747 = 4108121) B4108121
theorem B2738807 : Blo 1825614 2738807 := bstep (se 1 (by rfl) ⟨2054105, by rfl⟩ : syracuseStep 2738807 = 4108211) B4108211
theorem B3902087 : Blo 1825614 3902087 := bstep (se 1 (by rfl) ⟨2926565, by rfl⟩ : syracuseStep 3902087 = 5853131) B5853131
theorem B2738831 : Blo 1825614 2738831 := bstep (se 1 (by rfl) ⟨2054123, by rfl⟩ : syracuseStep 2738831 = 4108247) B4108247
theorem B4688531 : Blo 1825614 4688531 := bstep (se 1 (by rfl) ⟨3516398, by rfl⟩ : syracuseStep 4688531 = 7032797) B7032797
theorem B2599609 : Blo 1825614 2599609 := bstep (se 2 (by rfl) ⟨974853, by rfl⟩ : syracuseStep 2599609 = 1949707) B1949707
theorem B2738873 : Blo 1825614 2738873 := bstep (se 2 (by rfl) ⟨1027077, by rfl⟩ : syracuseStep 2738873 = 2054155) B2054155
theorem B11700929 : Blo 1825614 11700929 := bstep (se 2 (by rfl) ⟨4387848, by rfl⟩ : syracuseStep 11700929 = 8775697) B8775697
theorem B10406657 : Blo 1825614 10406657 := bstep (se 2 (by rfl) ⟨3902496, by rfl⟩ : syracuseStep 10406657 = 7804993) B7804993
theorem B2738951 : Blo 1825614 2738951 := bstep (se 1 (by rfl) ⟨2054213, by rfl⟩ : syracuseStep 2738951 = 4108427) B4108427
theorem B4623115 : Blo 1825614 4623115 := bstep (se 1 (by rfl) ⟨3467336, by rfl⟩ : syracuseStep 4623115 = 6934673) B6934673
theorem B7506703 : Blo 1825614 7506703 := bstep (se 1 (by rfl) ⟨5630027, by rfl⟩ : syracuseStep 7506703 = 11260055) B11260055
theorem B2312975 : Blo 1825614 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B2738987 : Blo 1825614 2738987 := bstep (se 1 (by rfl) ⟨2054240, by rfl⟩ : syracuseStep 2738987 = 4108481) B4108481
theorem B2739017 : Blo 1825614 2739017 := bstep (se 2 (by rfl) ⟨1027131, by rfl⟩ : syracuseStep 2739017 = 2054263) B2054263
theorem B6933383 : Blo 1825614 6933383 := bstep (se 1 (by rfl) ⟨5200037, by rfl⟩ : syracuseStep 6933383 = 10400075) B10400075
theorem B3083143 : Blo 1825614 3083143 := bstep (se 1 (by rfl) ⟨2312357, by rfl⟩ : syracuseStep 3083143 = 4624715) B4624715
theorem B10398617 : Blo 1825614 10398617 := bstep (se 2 (by rfl) ⟨3899481, by rfl⟩ : syracuseStep 10398617 = 7798963) B7798963
theorem B4623257 : Blo 1825614 4623257 := bstep (se 2 (by rfl) ⟨1733721, by rfl⟩ : syracuseStep 4623257 = 3467443) B3467443
theorem B2739131 : Blo 1825614 2739131 := bstep (se 1 (by rfl) ⟨2054348, by rfl⟩ : syracuseStep 2739131 = 4108697) B4108697
theorem B3468233 : Blo 1825614 3468233 := bstep (se 2 (by rfl) ⟨1300587, by rfl⟩ : syracuseStep 3468233 = 2601175) B2601175
theorem B2739191 : Blo 1825614 2739191 := bstep (se 1 (by rfl) ⟨2054393, by rfl⟩ : syracuseStep 2739191 = 4108787) B4108787
theorem B2739215 : Blo 1825614 2739215 := bstep (se 1 (by rfl) ⟨2054411, by rfl⟩ : syracuseStep 2739215 = 4108823) B4108823
theorem B2739257 : Blo 1825614 2739257 := bstep (se 2 (by rfl) ⟨1027221, by rfl⟩ : syracuseStep 2739257 = 2054443) B2054443
theorem B4623419 : Blo 1825614 4623419 := bstep (se 1 (by rfl) ⟨3467564, by rfl⟩ : syracuseStep 4623419 = 6935129) B6935129
theorem B10546237 : Blo 1825614 10546237 := bstep (se 3 (by rfl) ⟨1977419, by rfl⟩ : syracuseStep 10546237 = 3954839) B3954839
theorem B23407703 : Blo 1825614 23407703 := bstep (se 1 (by rfl) ⟨17555777, by rfl⟩ : syracuseStep 23407703 = 35111555) B35111555
theorem B2468983 : Blo 1825614 2468983 := bstep (se 1 (by rfl) ⟨1851737, by rfl⟩ : syracuseStep 2468983 = 3703475) B3703475
theorem B2739335 : Blo 1825614 2739335 := bstep (se 1 (by rfl) ⟨2054501, by rfl⟩ : syracuseStep 2739335 = 4109003) B4109003
theorem B2739371 : Blo 1825614 2739371 := bstep (se 1 (by rfl) ⟨2054528, by rfl⟩ : syracuseStep 2739371 = 4109057) B4109057
theorem B22564013 : Blo 1825614 22564013 := bstep (se 3 (by rfl) ⟨4230752, by rfl⟩ : syracuseStep 22564013 = 8461505) B8461505
theorem B2739401 : Blo 1825614 2739401 := bstep (se 2 (by rfl) ⟨1027275, by rfl⟩ : syracuseStep 2739401 = 2054551) B2054551
theorem B10407113 : Blo 1825614 10407113 := bstep (se 2 (by rfl) ⟨3902667, by rfl⟩ : syracuseStep 10407113 = 7805335) B7805335
theorem B5557547 : Blo 1825614 5557547 := bstep (se 1 (by rfl) ⟨4168160, by rfl⟩ : syracuseStep 5557547 = 8336321) B8336321
theorem B2739515 : Blo 1825614 2739515 := bstep (se 1 (by rfl) ⟨2054636, by rfl⟩ : syracuseStep 2739515 = 4109273) B4109273
theorem B5270903 : Blo 1825614 5270903 := bstep (se 1 (by rfl) ⟨3953177, by rfl⟩ : syracuseStep 5270903 = 7906355) B7906355
theorem B2739575 : Blo 1825614 2739575 := bstep (se 1 (by rfl) ⟨2054681, by rfl⟩ : syracuseStep 2739575 = 4109363) B4109363
theorem B38014343 : Blo 1825614 38014343 := bstep (se 1 (by rfl) ⟨28510757, by rfl⟩ : syracuseStep 38014343 = 57021515) B57021515
theorem B2739599 : Blo 1825614 2739599 := bstep (se 1 (by rfl) ⟨2054699, by rfl⟩ : syracuseStep 2739599 = 4109399) B4109399
theorem B4623763 : Blo 1825614 4623763 := bstep (se 1 (by rfl) ⟨3467822, by rfl⟩ : syracuseStep 4623763 = 6935645) B6935645
theorem B2739641 : Blo 1825614 2739641 := bstep (se 2 (by rfl) ⟨1027365, by rfl⟩ : syracuseStep 2739641 = 2054731) B2054731
theorem B39497219 : Blo 1825614 39497219 := bstep (se 1 (by rfl) ⟨29622914, by rfl⟩ : syracuseStep 39497219 = 59245829) B59245829
theorem B2739719 : Blo 1825614 2739719 := bstep (se 1 (by rfl) ⟨2054789, by rfl⟩ : syracuseStep 2739719 = 4109579) B4109579
theorem B1830407 : Blo 1825614 1830407 := bstep (se 1 (by rfl) ⟨1372805, by rfl⟩ : syracuseStep 1830407 = 2745611) B2745611
theorem B3083791 : Blo 1825614 3083791 := bstep (se 1 (by rfl) ⟨2312843, by rfl⟩ : syracuseStep 3083791 = 4625687) B4625687
theorem B4623905 : Blo 1825614 4623905 := bstep (se 2 (by rfl) ⟨1733964, by rfl⟩ : syracuseStep 4623905 = 3467929) B3467929
theorem B2739755 : Blo 1825614 2739755 := bstep (se 1 (by rfl) ⟨2054816, by rfl⟩ : syracuseStep 2739755 = 4109633) B4109633
theorem B2739785 : Blo 1825614 2739785 := bstep (se 2 (by rfl) ⟨1027419, by rfl⟩ : syracuseStep 2739785 = 2054839) B2054839
theorem B4107923 : Blo 1825614 4107923 := bstep (se 1 (by rfl) ⟨3080942, by rfl⟩ : syracuseStep 4107923 = 6161885) B6161885
theorem B2739899 : Blo 1825614 2739899 := bstep (se 1 (by rfl) ⟨2054924, by rfl⟩ : syracuseStep 2739899 = 4109849) B4109849
theorem B4107977 : Blo 1825614 4107977 := bstep (se 2 (by rfl) ⟨1540491, by rfl⟩ : syracuseStep 4107977 = 3080983) B3080983
theorem B13872869 : Blo 1825614 13872869 := bstep (se 4 (by rfl) ⟨1300581, by rfl⟩ : syracuseStep 13872869 = 2601163) B2601163
theorem B2739959 : Blo 1825614 2739959 := bstep (se 1 (by rfl) ⟨2054969, by rfl⟩ : syracuseStep 2739959 = 4109939) B4109939
theorem B2739983 : Blo 1825614 2739983 := bstep (se 1 (by rfl) ⟨2054987, by rfl⟩ : syracuseStep 2739983 = 4109975) B4109975
theorem B2469647 : Blo 1825614 2469647 := bstep (se 1 (by rfl) ⟨1852235, by rfl⟩ : syracuseStep 2469647 = 3704471) B3704471
theorem B2740025 : Blo 1825614 2740025 := bstep (se 2 (by rfl) ⟨1027509, by rfl⟩ : syracuseStep 2740025 = 2055019) B2055019
theorem B4386695 : Blo 1825614 4386695 := bstep (se 1 (by rfl) ⟨3290021, by rfl⟩ : syracuseStep 4386695 = 6580043) B6580043
theorem B2600839 : Blo 1825614 2600839 := bstep (se 1 (by rfl) ⟨1950629, by rfl⟩ : syracuseStep 2600839 = 3901259) B3901259
theorem B2740103 : Blo 1825614 2740103 := bstep (se 1 (by rfl) ⟨2055077, by rfl⟩ : syracuseStep 2740103 = 4110155) B4110155
theorem B2740139 : Blo 1825614 2740139 := bstep (se 1 (by rfl) ⟨2055104, by rfl⟩ : syracuseStep 2740139 = 4110209) B4110209
theorem B2740169 : Blo 1825614 2740169 := bstep (se 2 (by rfl) ⟨1027563, by rfl⟩ : syracuseStep 2740169 = 2055127) B2055127
theorem B2740283 : Blo 1825614 2740283 := bstep (se 1 (by rfl) ⟨2055212, by rfl⟩ : syracuseStep 2740283 = 4110425) B4110425
theorem B20795453 : Blo 1825614 20795453 := bstep (se 3 (by rfl) ⟨3899147, by rfl⟩ : syracuseStep 20795453 = 7798295) B7798295
theorem B2740343 : Blo 1825614 2740343 := bstep (se 1 (by rfl) ⟨2055257, by rfl⟩ : syracuseStep 2740343 = 4110515) B4110515
theorem B13865093 : Blo 1825614 13865093 := bstep (se 4 (by rfl) ⟨1299852, by rfl⟩ : syracuseStep 13865093 = 2599705) B2599705
theorem B2502799 : Blo 1825614 2502799 := bstep (se 1 (by rfl) ⟨1877099, by rfl⟩ : syracuseStep 2502799 = 3754199) B3754199
theorem B2740367 : Blo 1825614 2740367 := bstep (se 1 (by rfl) ⟨2055275, by rfl⟩ : syracuseStep 2740367 = 4110551) B4110551
theorem B2740409 : Blo 1825614 2740409 := bstep (se 2 (by rfl) ⟨1027653, by rfl⟩ : syracuseStep 2740409 = 2055307) B2055307
theorem B2740487 : Blo 1825614 2740487 := bstep (se 1 (by rfl) ⟨2055365, by rfl⟩ : syracuseStep 2740487 = 4110731) B4110731
theorem B2740523 : Blo 1825614 2740523 := bstep (se 1 (by rfl) ⟨2055392, by rfl⟩ : syracuseStep 2740523 = 4110785) B4110785
theorem B2740553 : Blo 1825614 2740553 := bstep (se 2 (by rfl) ⟨1027707, by rfl⟩ : syracuseStep 2740553 = 2055415) B2055415
theorem B4108679 : Blo 1825614 4108679 := bstep (se 1 (by rfl) ⟨3081509, by rfl⟩ : syracuseStep 4108679 = 6163019) B6163019
theorem B15610259 : Blo 1825614 15610259 := bstep (se 1 (by rfl) ⟨11707694, by rfl⟩ : syracuseStep 15610259 = 23415389) B23415389
theorem B4387225 : Blo 1825614 4387225 := bstep (se 2 (by rfl) ⟨1645209, by rfl⟩ : syracuseStep 4387225 = 3290419) B3290419
theorem B13169081 : Blo 1825614 13169081 := bstep (se 2 (by rfl) ⟨4938405, by rfl⟩ : syracuseStep 13169081 = 9876811) B9876811
theorem B2740667 : Blo 1825614 2740667 := bstep (se 1 (by rfl) ⟨2055500, by rfl⟩ : syracuseStep 2740667 = 4111001) B4111001
theorem B2740727 : Blo 1825614 2740727 := bstep (se 1 (by rfl) ⟨2055545, by rfl⟩ : syracuseStep 2740727 = 4111091) B4111091
theorem B4624897 : Blo 1825614 4624897 := bstep (se 2 (by rfl) ⟨1734336, by rfl⟩ : syracuseStep 4624897 = 3468673) B3468673
theorem B2740751 : Blo 1825614 2740751 := bstep (se 1 (by rfl) ⟨2055563, by rfl⟩ : syracuseStep 2740751 = 4111127) B4111127
theorem B2740793 : Blo 1825614 2740793 := bstep (se 2 (by rfl) ⟨1027797, by rfl⟩ : syracuseStep 2740793 = 2055595) B2055595
theorem B4108859 : Blo 1825614 4108859 := bstep (se 1 (by rfl) ⟨3081644, by rfl⟩ : syracuseStep 4108859 = 6163289) B6163289
theorem B6935159 : Blo 1825614 6935159 := bstep (se 1 (by rfl) ⟨5201369, by rfl⟩ : syracuseStep 6935159 = 10402739) B10402739
theorem B2740871 : Blo 1825614 2740871 := bstep (se 1 (by rfl) ⟨2055653, by rfl⟩ : syracuseStep 2740871 = 4111307) B4111307
theorem B2740907 : Blo 1825614 2740907 := bstep (se 1 (by rfl) ⟨2055680, by rfl⟩ : syracuseStep 2740907 = 4111361) B4111361
theorem B4108985 : Blo 1825614 4108985 := bstep (se 2 (by rfl) ⟨1540869, by rfl⟩ : syracuseStep 4108985 = 3081739) B3081739
theorem B2601659 : Blo 1825614 2601659 := bstep (se 1 (by rfl) ⟨1951244, by rfl⟩ : syracuseStep 2601659 = 3902489) B3902489
theorem B2740937 : Blo 1825614 2740937 := bstep (se 2 (by rfl) ⟨1027851, by rfl⟩ : syracuseStep 2740937 = 2055703) B2055703
theorem B2741051 : Blo 1825614 2741051 := bstep (se 1 (by rfl) ⟨2055788, by rfl⟩ : syracuseStep 2741051 = 4111577) B4111577
theorem B2741111 : Blo 1825614 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B2741135 : Blo 1825614 2741135 := bstep (se 1 (by rfl) ⟨2055851, by rfl⟩ : syracuseStep 2741135 = 4111703) B4111703
theorem B6165395 : Blo 1825614 6165395 := bstep (se 1 (by rfl) ⟨4624046, by rfl⟩ : syracuseStep 6165395 = 9248093) B9248093
theorem B8328089 : Blo 1825614 8328089 := bstep (se 2 (by rfl) ⟨3123033, by rfl⟩ : syracuseStep 8328089 = 6246067) B6246067
theorem B2741177 : Blo 1825614 2741177 := bstep (se 2 (by rfl) ⟨1027941, by rfl⟩ : syracuseStep 2741177 = 2055883) B2055883
theorem B4387841 : Blo 1825614 4387841 := bstep (se 2 (by rfl) ⟨1645440, by rfl⟩ : syracuseStep 4387841 = 3290881) B3290881
theorem B8778755 : Blo 1825614 8778755 := bstep (se 1 (by rfl) ⟨6584066, by rfl⟩ : syracuseStep 8778755 = 13168133) B13168133
theorem B23737349 : Blo 1825614 23737349 := bstep (se 4 (by rfl) ⟨2225376, by rfl⟩ : syracuseStep 23737349 = 4450753) B4450753
theorem B2741255 : Blo 1825614 2741255 := bstep (se 1 (by rfl) ⟨2055941, by rfl⟩ : syracuseStep 2741255 = 4111883) B4111883
theorem B4109327 : Blo 1825614 4109327 := bstep (se 1 (by rfl) ⟨3081995, by rfl⟩ : syracuseStep 4109327 = 6163991) B6163991
theorem B4166671 : Blo 1825614 4166671 := bstep (se 1 (by rfl) ⟨3125003, by rfl⟩ : syracuseStep 4166671 = 6250007) B6250007
theorem B4109345 : Blo 1825614 4109345 := bstep (se 2 (by rfl) ⟨1541004, by rfl⟩ : syracuseStep 4109345 = 3082009) B3082009
theorem B2741291 : Blo 1825614 2741291 := bstep (se 1 (by rfl) ⟨2055968, by rfl⟩ : syracuseStep 2741291 = 4111937) B4111937
theorem B2741321 : Blo 1825614 2741321 := bstep (se 2 (by rfl) ⟨1027995, by rfl⟩ : syracuseStep 2741321 = 2055991) B2055991
theorem B4625495 : Blo 1825614 4625495 := bstep (se 1 (by rfl) ⟨3469121, by rfl⟩ : syracuseStep 4625495 = 6938243) B6938243
theorem B14054573 : Blo 1825614 14054573 := bstep (se 3 (by rfl) ⟨2635232, by rfl⟩ : syracuseStep 14054573 = 5270465) B5270465
theorem B4388041 : Blo 1825614 4388041 := bstep (se 2 (by rfl) ⟨1645515, by rfl⟩ : syracuseStep 4388041 = 3291031) B3291031
theorem B5272847 : Blo 1825614 5272847 := bstep (se 1 (by rfl) ⟨3954635, by rfl⟩ : syracuseStep 5272847 = 7909271) B7909271
theorem B5199137 : Blo 1825614 5199137 := bstep (se 2 (by rfl) ⟨1949676, by rfl⟩ : syracuseStep 5199137 = 3899353) B3899353
theorem B13161761 : Blo 1825614 13161761 := bstep (se 2 (by rfl) ⟨4935660, by rfl⟩ : syracuseStep 13161761 = 9871321) B9871321
theorem B4625707 : Blo 1825614 4625707 := bstep (se 1 (by rfl) ⟨3469280, by rfl⟩ : syracuseStep 4625707 = 6938561) B6938561
theorem B4109687 : Blo 1825614 4109687 := bstep (se 1 (by rfl) ⟨3082265, by rfl⟩ : syracuseStep 4109687 = 6164531) B6164531
theorem B7804295 : Blo 1825614 7804295 := bstep (se 1 (by rfl) ⟨5853221, by rfl⟩ : syracuseStep 7804295 = 11706443) B11706443
theorem B4625849 : Blo 1825614 4625849 := bstep (se 2 (by rfl) ⟨1734693, by rfl⟩ : syracuseStep 4625849 = 3469387) B3469387
theorem B33322499 : Blo 1825614 33322499 := bstep (se 1 (by rfl) ⟨24991874, by rfl⟩ : syracuseStep 33322499 = 49983749) B49983749
theorem B118494737 : Blo 1825614 118494737 := bstep (se 2 (by rfl) ⟨44435526, by rfl⟩ : syracuseStep 118494737 = 88871053) B88871053
theorem B4109867 : Blo 1825614 4109867 := bstep (se 1 (by rfl) ⟨3082400, by rfl⟩ : syracuseStep 4109867 = 6164801) B6164801
theorem B6936131 : Blo 1825614 6936131 := bstep (se 1 (by rfl) ⟨5202098, by rfl⟩ : syracuseStep 6936131 = 10404197) B10404197
theorem B50001587 : Blo 1825614 50001587 := bstep (se 1 (by rfl) ⟨37501190, by rfl⟩ : syracuseStep 50001587 = 75002381) B75002381
theorem B2053903 : Blo 1825614 2053903 := bstep (se 1 (by rfl) ⟨1540427, by rfl⟩ : syracuseStep 2053903 = 3080855) B3080855
theorem B2004751 : Blo 1825614 2004751 := bstep (se 1 (by rfl) ⟨1503563, by rfl⟩ : syracuseStep 2004751 = 3007127) B3007127
theorem B13162277 : Blo 1825614 13162277 := bstep (se 4 (by rfl) ⟨1233963, by rfl⟩ : syracuseStep 13162277 = 2467927) B2467927
theorem B4110227 : Blo 1825614 4110227 := bstep (se 1 (by rfl) ⟨3082670, by rfl⟩ : syracuseStep 4110227 = 6165341) B6165341
theorem B4110281 : Blo 1825614 4110281 := bstep (se 2 (by rfl) ⟨1541355, by rfl⟩ : syracuseStep 4110281 = 3082711) B3082711
theorem B6936587 : Blo 1825614 6936587 := bstep (se 1 (by rfl) ⟨5202440, by rfl⟩ : syracuseStep 6936587 = 10404881) B10404881
theorem B10401965 : Blo 1825614 10401965 := bstep (se 3 (by rfl) ⟨1950368, by rfl⟩ : syracuseStep 10401965 = 3900737) B3900737
theorem B2054407 : Blo 1825614 2054407 := bstep (se 1 (by rfl) ⟨1540805, by rfl⟩ : syracuseStep 2054407 = 3081611) B3081611
theorem B5200139 : Blo 1825614 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B2636047 : Blo 1825614 2636047 := bstep (se 1 (by rfl) ⟨1977035, by rfl⟩ : syracuseStep 2636047 = 3954071) B3954071
theorem B6166799 : Blo 1825614 6166799 := bstep (se 1 (by rfl) ⟨4625099, by rfl⟩ : syracuseStep 6166799 = 9250199) B9250199
theorem B9877895 : Blo 1825614 9877895 := bstep (se 1 (by rfl) ⟨7408421, by rfl⟩ : syracuseStep 9877895 = 14816843) B14816843
theorem B9247121 : Blo 1825614 9247121 := bstep (se 2 (by rfl) ⟨3467670, by rfl⟩ : syracuseStep 9247121 = 6935341) B6935341
theorem B2054587 : Blo 1825614 2054587 := bstep (se 1 (by rfl) ⟨1540940, by rfl⟩ : syracuseStep 2054587 = 3081881) B3081881
theorem B13867523 : Blo 1825614 13867523 := bstep (se 1 (by rfl) ⟨10400642, by rfl⟩ : syracuseStep 13867523 = 20801285) B20801285
theorem B7404043 : Blo 1825614 7404043 := bstep (se 1 (by rfl) ⟨5553032, by rfl⟩ : syracuseStep 7404043 = 11106065) B11106065
theorem B6167069 : Blo 1825614 6167069 := bstep (se 3 (by rfl) ⟨1156325, by rfl⟩ : syracuseStep 6167069 = 2312651) B2312651
theorem B4110983 : Blo 1825614 4110983 := bstep (se 1 (by rfl) ⟨3083237, by rfl⟩ : syracuseStep 4110983 = 6166475) B6166475
theorem B16661285 : Blo 1825614 16661285 := bstep (se 4 (by rfl) ⟨1561995, by rfl⟩ : syracuseStep 16661285 = 3123991) B3123991
theorem B4111163 : Blo 1825614 4111163 := bstep (se 1 (by rfl) ⟨3083372, by rfl⟩ : syracuseStep 4111163 = 6166745) B6166745
theorem B1825671 : Blo 1825614 1825671 := bstep (se 1 (by rfl) ⟨1369253, by rfl⟩ : syracuseStep 1825671 = 2738507) B2738507
theorem B1825679 : Blo 1825614 1825679 := bstep (se 1 (by rfl) ⟨1369259, by rfl⟩ : syracuseStep 1825679 = 2738519) B2738519
theorem B2055055 : Blo 1825614 2055055 := bstep (se 1 (by rfl) ⟨1541291, by rfl⟩ : syracuseStep 2055055 = 3082583) B3082583
theorem B49986467 : Blo 1825614 49986467 := bstep (se 1 (by rfl) ⟨37489850, by rfl⟩ : syracuseStep 49986467 = 74979701) B74979701
theorem B4111289 : Blo 1825614 4111289 := bstep (se 2 (by rfl) ⟨1541733, by rfl⟩ : syracuseStep 4111289 = 3083467) B3083467
theorem B1825723 : Blo 1825614 1825723 := bstep (se 1 (by rfl) ⟨1369292, by rfl⟩ : syracuseStep 1825723 = 2738585) B2738585
theorem B1825799 : Blo 1825614 1825799 := bstep (se 1 (by rfl) ⟨1369349, by rfl⟩ : syracuseStep 1825799 = 2738699) B2738699
theorem B1825807 : Blo 1825614 1825807 := bstep (se 1 (by rfl) ⟨1369355, by rfl⟩ : syracuseStep 1825807 = 2738711) B2738711
theorem B1825851 : Blo 1825614 1825851 := bstep (se 1 (by rfl) ⟨1369388, by rfl⟩ : syracuseStep 1825851 = 2738777) B2738777
theorem B7806071 : Blo 1825614 7806071 := bstep (se 1 (by rfl) ⟨5854553, by rfl⟩ : syracuseStep 7806071 = 11709107) B11709107
theorem B1825927 : Blo 1825614 1825927 := bstep (se 1 (by rfl) ⟨1369445, by rfl⟩ : syracuseStep 1825927 = 2738891) B2738891
theorem B1825935 : Blo 1825614 1825935 := bstep (se 1 (by rfl) ⟨1369451, by rfl⟩ : syracuseStep 1825935 = 2738903) B2738903
theorem B1825979 : Blo 1825614 1825979 := bstep (se 1 (by rfl) ⟨1369484, by rfl⟩ : syracuseStep 1825979 = 2738969) B2738969
theorem B1826055 : Blo 1825614 1826055 := bstep (se 1 (by rfl) ⟨1369541, by rfl⟩ : syracuseStep 1826055 = 2739083) B2739083
theorem B1826063 : Blo 1825614 1826063 := bstep (se 1 (by rfl) ⟨1369547, by rfl⟩ : syracuseStep 1826063 = 2739095) B2739095
theorem B4111631 : Blo 1825614 4111631 := bstep (se 1 (by rfl) ⟨3083723, by rfl⟩ : syracuseStep 4111631 = 6167447) B6167447
theorem B7806223 : Blo 1825614 7806223 := bstep (se 1 (by rfl) ⟨5854667, by rfl⟩ : syracuseStep 7806223 = 11709335) B11709335
theorem B4111649 : Blo 1825614 4111649 := bstep (se 2 (by rfl) ⟨1541868, by rfl⟩ : syracuseStep 4111649 = 3083737) B3083737
theorem B1826107 : Blo 1825614 1826107 := bstep (se 1 (by rfl) ⟨1369580, by rfl⟩ : syracuseStep 1826107 = 2739161) B2739161
theorem B1826183 : Blo 1825614 1826183 := bstep (se 1 (by rfl) ⟨1369637, by rfl⟩ : syracuseStep 1826183 = 2739275) B2739275
theorem B2055559 : Blo 1825614 2055559 := bstep (se 1 (by rfl) ⟨1541669, by rfl⟩ : syracuseStep 2055559 = 3083339) B3083339
theorem B1826191 : Blo 1825614 1826191 := bstep (se 1 (by rfl) ⟨1369643, by rfl⟩ : syracuseStep 1826191 = 2739287) B2739287
theorem B1826235 : Blo 1825614 1826235 := bstep (se 1 (by rfl) ⟨1369676, by rfl⟩ : syracuseStep 1826235 = 2739353) B2739353
theorem B20807117 : Blo 1825614 20807117 := bstep (se 3 (by rfl) ⟨3901334, by rfl⟩ : syracuseStep 20807117 = 7802669) B7802669
theorem B1826311 : Blo 1825614 1826311 := bstep (se 1 (by rfl) ⟨1369733, by rfl⟩ : syracuseStep 1826311 = 2739467) B2739467
theorem B1826319 : Blo 1825614 1826319 := bstep (se 1 (by rfl) ⟨1369739, by rfl⟩ : syracuseStep 1826319 = 2739479) B2739479
theorem B1826363 : Blo 1825614 1826363 := bstep (se 1 (by rfl) ⟨1369772, by rfl⟩ : syracuseStep 1826363 = 2739545) B2739545
theorem B2055739 : Blo 1825614 2055739 := bstep (se 1 (by rfl) ⟨1541804, by rfl⟩ : syracuseStep 2055739 = 3083609) B3083609
theorem B4111991 : Blo 1825614 4111991 := bstep (se 1 (by rfl) ⟨3083993, by rfl⟩ : syracuseStep 4111991 = 6167987) B6167987
theorem B1826439 : Blo 1825614 1826439 := bstep (se 1 (by rfl) ⟨1369829, by rfl⟩ : syracuseStep 1826439 = 2739659) B2739659
theorem B1826447 : Blo 1825614 1826447 := bstep (se 1 (by rfl) ⟨1369835, by rfl⟩ : syracuseStep 1826447 = 2739671) B2739671
theorem B1826491 : Blo 1825614 1826491 := bstep (se 1 (by rfl) ⟨1369868, by rfl⟩ : syracuseStep 1826491 = 2739737) B2739737
theorem B1826567 : Blo 1825614 1826567 := bstep (se 1 (by rfl) ⟨1369925, by rfl⟩ : syracuseStep 1826567 = 2739851) B2739851
theorem B1826575 : Blo 1825614 1826575 := bstep (se 1 (by rfl) ⟨1369931, by rfl⟩ : syracuseStep 1826575 = 2739863) B2739863
theorem B5275421 : Blo 1825614 5275421 := bstep (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) B1978283
theorem B44433197 : Blo 1825614 44433197 := bstep (se 3 (by rfl) ⟨8331224, by rfl⟩ : syracuseStep 44433197 = 16662449) B16662449
theorem B1826619 : Blo 1825614 1826619 := bstep (se 1 (by rfl) ⟨1369964, by rfl⟩ : syracuseStep 1826619 = 2739929) B2739929
theorem B5144435 : Blo 1825614 5144435 := bstep (se 1 (by rfl) ⟨3858326, by rfl⟩ : syracuseStep 5144435 = 7716653) B7716653
theorem B1826695 : Blo 1825614 1826695 := bstep (se 1 (by rfl) ⟨1370021, by rfl⟩ : syracuseStep 1826695 = 2740043) B2740043
theorem B1826703 : Blo 1825614 1826703 := bstep (se 1 (by rfl) ⟨1370027, by rfl⟩ : syracuseStep 1826703 = 2740055) B2740055
theorem B23715737 : Blo 1825614 23715737 := bstep (se 2 (by rfl) ⟨8893401, by rfl⟩ : syracuseStep 23715737 = 17786803) B17786803
theorem B1826747 : Blo 1825614 1826747 := bstep (se 1 (by rfl) ⟨1370060, by rfl⟩ : syracuseStep 1826747 = 2740121) B2740121
theorem B1826855 : Blo 1825614 1826855 := bstep (se 1 (by rfl) ⟨1370141, by rfl⟩ : syracuseStep 1826855 = 2740283) B2740283
theorem B1826895 : Blo 1825614 1826895 := bstep (se 1 (by rfl) ⟨1370171, by rfl⟩ : syracuseStep 1826895 = 2740343) B2740343
theorem B1826911 : Blo 1825614 1826911 := bstep (se 1 (by rfl) ⟨1370183, by rfl⟩ : syracuseStep 1826911 = 2740367) B2740367
theorem B1826939 : Blo 1825614 1826939 := bstep (se 1 (by rfl) ⟨1370204, by rfl⟩ : syracuseStep 1826939 = 2740409) B2740409
theorem B1826991 : Blo 1825614 1826991 := bstep (se 1 (by rfl) ⟨1370243, by rfl⟩ : syracuseStep 1826991 = 2740487) B2740487
theorem B1827015 : Blo 1825614 1827015 := bstep (se 1 (by rfl) ⟨1370261, by rfl⟩ : syracuseStep 1827015 = 2740523) B2740523
theorem B1827035 : Blo 1825614 1827035 := bstep (se 1 (by rfl) ⟨1370276, by rfl⟩ : syracuseStep 1827035 = 2740553) B2740553
theorem B1827111 : Blo 1825614 1827111 := bstep (se 1 (by rfl) ⟨1370333, by rfl⟩ : syracuseStep 1827111 = 2740667) B2740667
theorem B1827151 : Blo 1825614 1827151 := bstep (se 1 (by rfl) ⟨1370363, by rfl⟩ : syracuseStep 1827151 = 2740727) B2740727
theorem B1827167 : Blo 1825614 1827167 := bstep (se 1 (by rfl) ⟨1370375, by rfl⟩ : syracuseStep 1827167 = 2740751) B2740751
theorem B5202281 : Blo 1825614 5202281 := bstep (se 2 (by rfl) ⟨1950855, by rfl⟩ : syracuseStep 5202281 = 3901711) B3901711
theorem B1827195 : Blo 1825614 1827195 := bstep (se 1 (by rfl) ⟨1370396, by rfl⟩ : syracuseStep 1827195 = 2740793) B2740793
theorem B1827247 : Blo 1825614 1827247 := bstep (se 1 (by rfl) ⟨1370435, by rfl⟩ : syracuseStep 1827247 = 2740871) B2740871
theorem B1827271 : Blo 1825614 1827271 := bstep (se 1 (by rfl) ⟨1370453, by rfl⟩ : syracuseStep 1827271 = 2740907) B2740907
theorem B37478861 : Blo 1825614 37478861 := bstep (se 3 (by rfl) ⟨7027286, by rfl⟩ : syracuseStep 37478861 = 14054573) B14054573
theorem B60170701 : Blo 1825614 60170701 := bstep (se 3 (by rfl) ⟨11282006, by rfl⟩ : syracuseStep 60170701 = 22564013) B22564013
theorem B1827291 : Blo 1825614 1827291 := bstep (se 1 (by rfl) ⟨1370468, by rfl⟩ : syracuseStep 1827291 = 2740937) B2740937
theorem B7799321 : Blo 1825614 7799321 := bstep (se 2 (by rfl) ⟨2924745, by rfl⟩ : syracuseStep 7799321 = 5849491) B5849491
theorem B5849633 : Blo 1825614 5849633 := bstep (se 2 (by rfl) ⟨2193612, by rfl⟩ : syracuseStep 5849633 = 4387225) B4387225
theorem B1827367 : Blo 1825614 1827367 := bstep (se 1 (by rfl) ⟨1370525, by rfl⟩ : syracuseStep 1827367 = 2741051) B2741051
theorem B1827407 : Blo 1825614 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B1827423 : Blo 1825614 1827423 := bstep (se 1 (by rfl) ⟨1370567, by rfl⟩ : syracuseStep 1827423 = 2741135) B2741135
theorem B1827451 : Blo 1825614 1827451 := bstep (se 1 (by rfl) ⟨1370588, by rfl⟩ : syracuseStep 1827451 = 2741177) B2741177
theorem B5849747 : Blo 1825614 5849747 := bstep (se 1 (by rfl) ⟨4387310, by rfl⟩ : syracuseStep 5849747 = 8774621) B8774621
theorem B3080875 : Blo 1825614 3080875 := bstep (se 1 (by rfl) ⟨2310656, by rfl⟩ : syracuseStep 3080875 = 4621313) B4621313
theorem B2925227 : Blo 1825614 2925227 := bstep (se 1 (by rfl) ⟨2193920, by rfl⟩ : syracuseStep 2925227 = 4387841) B4387841
theorem B14811821 : Blo 1825614 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B1827503 : Blo 1825614 1827503 := bstep (se 1 (by rfl) ⟨1370627, by rfl⟩ : syracuseStep 1827503 = 2741255) B2741255
theorem B9872057 : Blo 1825614 9872057 := bstep (se 2 (by rfl) ⟨3702021, by rfl⟩ : syracuseStep 9872057 = 7404043) B7404043
theorem B1827527 : Blo 1825614 1827527 := bstep (se 1 (by rfl) ⟨1370645, by rfl⟩ : syracuseStep 1827527 = 2741291) B2741291
theorem B1827547 : Blo 1825614 1827547 := bstep (se 1 (by rfl) ⟨1370660, by rfl⟩ : syracuseStep 1827547 = 2741321) B2741321
theorem B4621151 : Blo 1825614 4621151 := bstep (se 1 (by rfl) ⟨3465863, by rfl⟩ : syracuseStep 4621151 = 6931727) B6931727
theorem B3515231 : Blo 1825614 3515231 := bstep (se 1 (by rfl) ⟨2636423, by rfl⟩ : syracuseStep 3515231 = 5272847) B5272847
theorem B3466091 : Blo 1825614 3466091 := bstep (se 1 (by rfl) ⟨2599568, by rfl⟩ : syracuseStep 3466091 = 5199137) B5199137
theorem B8774507 : Blo 1825614 8774507 := bstep (se 1 (by rfl) ⟨6580880, by rfl⟩ : syracuseStep 8774507 = 13161761) B13161761
theorem B3466145 : Blo 1825614 3466145 := bstep (se 2 (by rfl) ⟨1299804, by rfl⟩ : syracuseStep 3466145 = 2599609) B2599609
theorem B2311087 : Blo 1825614 2311087 := bstep (se 1 (by rfl) ⟨1733315, by rfl⟩ : syracuseStep 2311087 = 3466631) B3466631
theorem B5202863 : Blo 1825614 5202863 := bstep (se 1 (by rfl) ⟨3902147, by rfl⟩ : syracuseStep 5202863 = 7804295) B7804295
theorem B3081179 : Blo 1825614 3081179 := bstep (se 1 (by rfl) ⟨2310884, by rfl⟩ : syracuseStep 3081179 = 4621769) B4621769
theorem B78996491 : Blo 1825614 78996491 := bstep (se 1 (by rfl) ⟨59247368, by rfl⟩ : syracuseStep 78996491 = 118494737) B118494737
theorem B19760195 : Blo 1825614 19760195 := bstep (se 1 (by rfl) ⟨14820146, by rfl⟩ : syracuseStep 19760195 = 29640293) B29640293
theorem B33334391 : Blo 1825614 33334391 := bstep (se 1 (by rfl) ⟨25000793, by rfl⟩ : syracuseStep 33334391 = 50001587) B50001587
theorem B6161561 : Blo 1825614 6161561 := bstep (se 2 (by rfl) ⟨2310585, by rfl⟩ : syracuseStep 6161561 = 4621171) B4621171
theorem B3081415 : Blo 1825614 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B3704057 : Blo 1825614 3704057 := bstep (se 2 (by rfl) ⟨1389021, by rfl⟩ : syracuseStep 3704057 = 2778043) B2778043
theorem B3081577 : Blo 1825614 3081577 := bstep (se 2 (by rfl) ⟨1155591, by rfl⟩ : syracuseStep 3081577 = 2311183) B2311183
theorem B5555561 : Blo 1825614 5555561 := bstep (se 2 (by rfl) ⟨2083335, by rfl⟩ : syracuseStep 5555561 = 4166671) B4166671
theorem B12666227 : Blo 1825614 12666227 := bstep (se 1 (by rfl) ⟨9499670, by rfl⟩ : syracuseStep 12666227 = 18999341) B18999341
theorem B14058917 : Blo 1825614 14058917 := bstep (se 4 (by rfl) ⟨1318023, by rfl⟩ : syracuseStep 14058917 = 2636047) B2636047
theorem B2082223 : Blo 1825614 2082223 := bstep (se 1 (by rfl) ⟨1561667, by rfl⟩ : syracuseStep 2082223 = 3123335) B3123335
theorem B5555699 : Blo 1825614 5555699 := bstep (se 1 (by rfl) ⟨4166774, by rfl⟩ : syracuseStep 5555699 = 8333549) B8333549
theorem B5850721 : Blo 1825614 5850721 := bstep (se 2 (by rfl) ⟨2194020, by rfl⟩ : syracuseStep 5850721 = 4388041) B4388041
theorem B7800619 : Blo 1825614 7800619 := bstep (se 1 (by rfl) ⟨5850464, by rfl⟩ : syracuseStep 7800619 = 11700929) B11700929
theorem B4622255 : Blo 1825614 4622255 := bstep (se 1 (by rfl) ⟨3466691, by rfl⟩ : syracuseStep 4622255 = 6933383) B6933383
theorem B6932411 : Blo 1825614 6932411 := bstep (se 1 (by rfl) ⟨5199308, by rfl⟩ : syracuseStep 6932411 = 10398617) B10398617
theorem B3082171 : Blo 1825614 3082171 := bstep (se 1 (by rfl) ⟨2311628, by rfl⟩ : syracuseStep 3082171 = 4623257) B4623257
theorem B2312155 : Blo 1825614 2312155 := bstep (se 1 (by rfl) ⟨1734116, by rfl⟩ : syracuseStep 2312155 = 3468233) B3468233
theorem B3082279 : Blo 1825614 3082279 := bstep (se 1 (by rfl) ⟨2311709, by rfl⟩ : syracuseStep 3082279 = 4623419) B4623419
theorem B5204047 : Blo 1825614 5204047 := bstep (se 1 (by rfl) ⟨3903035, by rfl⟩ : syracuseStep 5204047 = 7806071) B7806071
theorem B3705031 : Blo 1825614 3705031 := bstep (se 1 (by rfl) ⟨2778773, by rfl⟩ : syracuseStep 3705031 = 5557547) B5557547
theorem B20810033 : Blo 1825614 20810033 := bstep (se 2 (by rfl) ⟨7803762, by rfl⟩ : syracuseStep 20810033 = 15607525) B15607525
theorem B13871411 : Blo 1825614 13871411 := bstep (se 1 (by rfl) ⟨10403558, by rfl⟩ : syracuseStep 13871411 = 20807117) B20807117
theorem B6162749 : Blo 1825614 6162749 := bstep (se 3 (by rfl) ⟨1155515, by rfl⟩ : syracuseStep 6162749 = 2311031) B2311031
theorem B26331479 : Blo 1825614 26331479 := bstep (se 1 (by rfl) ⟨19748609, by rfl⟩ : syracuseStep 26331479 = 39497219) B39497219
theorem B2738537 : Blo 1825614 2738537 := bstep (se 2 (by rfl) ⟨1026951, by rfl⟩ : syracuseStep 2738537 = 2053903) B2053903
theorem B2673001 : Blo 1825614 2673001 := bstep (se 2 (by rfl) ⟨1002375, by rfl⟩ : syracuseStep 2673001 = 2004751) B2004751
theorem B3082603 : Blo 1825614 3082603 := bstep (se 1 (by rfl) ⟨2311952, by rfl⟩ : syracuseStep 3082603 = 4623905) B4623905
theorem B2738615 : Blo 1825614 2738615 := bstep (se 1 (by rfl) ⟨2053961, by rfl⟩ : syracuseStep 2738615 = 4107923) B4107923
theorem B2738651 : Blo 1825614 2738651 := bstep (se 1 (by rfl) ⟨2053988, by rfl⟩ : syracuseStep 2738651 = 4107977) B4107977
theorem B3467785 : Blo 1825614 3467785 := bstep (se 2 (by rfl) ⟨1300419, by rfl⟩ : syracuseStep 3467785 = 2600839) B2600839
theorem B3516947 : Blo 1825614 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B13863635 : Blo 1825614 13863635 := bstep (se 1 (by rfl) ⟨10397726, by rfl⟩ : syracuseStep 13863635 = 20795453) B20795453
theorem B19524341 : Blo 1825614 19524341 := bstep (se 5 (by rfl) ⟨915203, by rfl⟩ : syracuseStep 19524341 = 1830407) B1830407
theorem B9243395 : Blo 1825614 9243395 := bstep (se 1 (by rfl) ⟨6932546, by rfl⟩ : syracuseStep 9243395 = 13865093) B13865093
theorem B9251657 : Blo 1825614 9251657 := bstep (se 2 (by rfl) ⟨3469371, by rfl⟩ : syracuseStep 9251657 = 6938743) B6938743
theorem B13167467 : Blo 1825614 13167467 := bstep (se 1 (by rfl) ⟨9875600, by rfl⟩ : syracuseStep 13167467 = 19751201) B19751201
theorem B2739119 : Blo 1825614 2739119 := bstep (se 1 (by rfl) ⟨2054339, by rfl⟩ : syracuseStep 2739119 = 4108679) B4108679
theorem B10406839 : Blo 1825614 10406839 := bstep (se 1 (by rfl) ⟨7805129, by rfl⟩ : syracuseStep 10406839 = 15610259) B15610259
theorem B2739209 : Blo 1825614 2739209 := bstep (se 2 (by rfl) ⟨1027203, by rfl⟩ : syracuseStep 2739209 = 2054407) B2054407
theorem B2739239 : Blo 1825614 2739239 := bstep (se 1 (by rfl) ⟨2054429, by rfl⟩ : syracuseStep 2739239 = 4108859) B4108859
theorem B16657487 : Blo 1825614 16657487 := bstep (se 1 (by rfl) ⟨12493115, by rfl⟩ : syracuseStep 16657487 = 24986231) B24986231
theorem B4623439 : Blo 1825614 4623439 := bstep (se 1 (by rfl) ⟨3467579, by rfl⟩ : syracuseStep 4623439 = 6935159) B6935159
theorem B2739323 : Blo 1825614 2739323 := bstep (se 1 (by rfl) ⟨2054492, by rfl⟩ : syracuseStep 2739323 = 4108985) B4108985
theorem B11709593 : Blo 1825614 11709593 := bstep (se 2 (by rfl) ⟨4391097, by rfl⟩ : syracuseStep 11709593 = 8782195) B8782195
theorem B6163613 : Blo 1825614 6163613 := bstep (se 3 (by rfl) ⟨1155677, by rfl⟩ : syracuseStep 6163613 = 2311355) B2311355
theorem B11709643 : Blo 1825614 11709643 := bstep (se 1 (by rfl) ⟨8782232, by rfl⟩ : syracuseStep 11709643 = 17564465) B17564465
theorem B2739449 : Blo 1825614 2739449 := bstep (se 2 (by rfl) ⟨1027293, by rfl⟩ : syracuseStep 2739449 = 2054587) B2054587
theorem B5852503 : Blo 1825614 5852503 := bstep (se 1 (by rfl) ⟨4389377, by rfl⟩ : syracuseStep 5852503 = 8778755) B8778755
theorem B2739551 : Blo 1825614 2739551 := bstep (se 1 (by rfl) ⟨2054663, by rfl⟩ : syracuseStep 2739551 = 4109327) B4109327
theorem B2739563 : Blo 1825614 2739563 := bstep (se 1 (by rfl) ⟨2054672, by rfl⟩ : syracuseStep 2739563 = 4109345) B4109345
theorem B3083663 : Blo 1825614 3083663 := bstep (se 1 (by rfl) ⟨2312747, by rfl⟩ : syracuseStep 3083663 = 4625495) B4625495
theorem B13348261 : Blo 1825614 13348261 := bstep (se 4 (by rfl) ⟨1251399, by rfl⟩ : syracuseStep 13348261 = 2502799) B2502799
theorem B3468719 : Blo 1825614 3468719 := bstep (se 1 (by rfl) ⟨2601539, by rfl⟩ : syracuseStep 3468719 = 5203079) B5203079
theorem B4107815 : Blo 1825614 4107815 := bstep (se 1 (by rfl) ⟨3080861, by rfl⟩ : syracuseStep 4107815 = 6161723) B6161723
theorem B2739791 : Blo 1825614 2739791 := bstep (se 1 (by rfl) ⟨2054843, by rfl⟩ : syracuseStep 2739791 = 4109687) B4109687
theorem B3083899 : Blo 1825614 3083899 := bstep (se 1 (by rfl) ⟨2312924, by rfl⟩ : syracuseStep 3083899 = 4625849) B4625849
theorem B6164153 : Blo 1825614 6164153 := bstep (se 2 (by rfl) ⟨2311557, by rfl⟩ : syracuseStep 6164153 = 4623115) B4623115
theorem B2739911 : Blo 1825614 2739911 := bstep (se 1 (by rfl) ⟨2054933, by rfl⟩ : syracuseStep 2739911 = 4109867) B4109867
theorem B4624087 : Blo 1825614 4624087 := bstep (se 1 (by rfl) ⟨3468065, by rfl⟩ : syracuseStep 4624087 = 6936131) B6936131
theorem B2740073 : Blo 1825614 2740073 := bstep (se 2 (by rfl) ⟨1027527, by rfl⟩ : syracuseStep 2740073 = 2055055) B2055055
theorem B4108139 : Blo 1825614 4108139 := bstep (se 1 (by rfl) ⟨3081104, by rfl⟩ : syracuseStep 4108139 = 6162209) B6162209
theorem B4108193 : Blo 1825614 4108193 := bstep (se 2 (by rfl) ⟨1540572, by rfl⟩ : syracuseStep 4108193 = 3081145) B3081145
theorem B2740151 : Blo 1825614 2740151 := bstep (se 1 (by rfl) ⟨2055113, by rfl⟩ : syracuseStep 2740151 = 4110227) B4110227
theorem B3469243 : Blo 1825614 3469243 := bstep (se 1 (by rfl) ⟨2601932, by rfl⟩ : syracuseStep 3469243 = 5203865) B5203865
theorem B2740187 : Blo 1825614 2740187 := bstep (se 1 (by rfl) ⟨2055140, by rfl⟩ : syracuseStep 2740187 = 4110281) B4110281
theorem B4624391 : Blo 1825614 4624391 := bstep (se 1 (by rfl) ⟨3468293, by rfl⟩ : syracuseStep 4624391 = 6936587) B6936587
theorem B14061649 : Blo 1825614 14061649 := bstep (se 2 (by rfl) ⟨5273118, by rfl⟩ : syracuseStep 14061649 = 10546237) B10546237
theorem B6934643 : Blo 1825614 6934643 := bstep (se 1 (by rfl) ⟨5200982, by rfl⟩ : syracuseStep 6934643 = 10401965) B10401965
theorem B4108535 : Blo 1825614 4108535 := bstep (se 1 (by rfl) ⟨3081401, by rfl⟩ : syracuseStep 4108535 = 6162803) B6162803
theorem B6164747 : Blo 1825614 6164747 := bstep (se 1 (by rfl) ⟨4623560, by rfl⟩ : syracuseStep 6164747 = 9247121) B9247121
theorem B9245015 : Blo 1825614 9245015 := bstep (se 1 (by rfl) ⟨6933761, by rfl⟩ : syracuseStep 9245015 = 13867523) B13867523
theorem B10408297 : Blo 1825614 10408297 := bstep (se 2 (by rfl) ⟨3903111, by rfl⟩ : syracuseStep 10408297 = 7806223) B7806223
theorem B2601391 : Blo 1825614 2601391 := bstep (se 1 (by rfl) ⟨1951043, by rfl⟩ : syracuseStep 2601391 = 3902087) B3902087
theorem B2740655 : Blo 1825614 2740655 := bstep (se 1 (by rfl) ⟨2055491, by rfl⟩ : syracuseStep 2740655 = 4110983) B4110983
theorem B3125687 : Blo 1825614 3125687 := bstep (se 1 (by rfl) ⟨2344265, by rfl⟩ : syracuseStep 3125687 = 4688531) B4688531
theorem B2740745 : Blo 1825614 2740745 := bstep (se 2 (by rfl) ⟨1027779, by rfl⟩ : syracuseStep 2740745 = 2055559) B2055559
theorem B6165017 : Blo 1825614 6165017 := bstep (se 2 (by rfl) ⟨2311881, by rfl⟩ : syracuseStep 6165017 = 4623763) B4623763
theorem B2740775 : Blo 1825614 2740775 := bstep (se 1 (by rfl) ⟨2055581, by rfl⟩ : syracuseStep 2740775 = 4111163) B4111163
theorem B2740859 : Blo 1825614 2740859 := bstep (se 1 (by rfl) ⟨2055644, by rfl⟩ : syracuseStep 2740859 = 4111289) B4111289
theorem B2740985 : Blo 1825614 2740985 := bstep (se 2 (by rfl) ⟨1027869, by rfl⟩ : syracuseStep 2740985 = 2055739) B2055739
theorem B35099405 : Blo 1825614 35099405 := bstep (se 3 (by rfl) ⟨6581138, by rfl⟩ : syracuseStep 35099405 = 13162277) B13162277
theorem B4109129 : Blo 1825614 4109129 := bstep (se 2 (by rfl) ⟨1540923, by rfl⟩ : syracuseStep 4109129 = 3081847) B3081847
theorem B2741087 : Blo 1825614 2741087 := bstep (se 1 (by rfl) ⟨2055815, by rfl⟩ : syracuseStep 2741087 = 4111631) B4111631
theorem B2741099 : Blo 1825614 2741099 := bstep (se 1 (by rfl) ⟨2055824, by rfl⟩ : syracuseStep 2741099 = 4111649) B4111649
theorem B25342895 : Blo 1825614 25342895 := bstep (se 1 (by rfl) ⟨19007171, by rfl⟩ : syracuseStep 25342895 = 38014343) B38014343
theorem B2741327 : Blo 1825614 2741327 := bstep (se 1 (by rfl) ⟨2055995, by rfl⟩ : syracuseStep 2741327 = 4111991) B4111991
theorem B3429623 : Blo 1825614 3429623 := bstep (se 1 (by rfl) ⟨2572217, by rfl⟩ : syracuseStep 3429623 = 5144435) B5144435
theorem B4109921 : Blo 1825614 4109921 := bstep (se 2 (by rfl) ⟨1541220, by rfl⟩ : syracuseStep 4109921 = 3082441) B3082441
theorem B6166151 : Blo 1825614 6166151 := bstep (se 1 (by rfl) ⟨4624613, by rfl⟩ : syracuseStep 6166151 = 9249227) B9249227
theorem B6166205 : Blo 1825614 6166205 := bstep (se 3 (by rfl) ⟨1156163, by rfl⟩ : syracuseStep 6166205 = 2312327) B2312327
theorem B2053831 : Blo 1825614 2053831 := bstep (se 1 (by rfl) ⟨1540373, by rfl⟩ : syracuseStep 2053831 = 3080747) B3080747
theorem B6936313 : Blo 1825614 6936313 := bstep (se 2 (by rfl) ⟨2601117, by rfl⟩ : syracuseStep 6936313 = 5202235) B5202235
theorem B6166367 : Blo 1825614 6166367 := bstep (se 1 (by rfl) ⟨4624775, by rfl⟩ : syracuseStep 6166367 = 9249551) B9249551
theorem B4110263 : Blo 1825614 4110263 := bstep (se 1 (by rfl) ⟨3082697, by rfl⟩ : syracuseStep 4110263 = 6165395) B6165395
theorem B5552059 : Blo 1825614 5552059 := bstep (se 1 (by rfl) ⟨4164044, by rfl⟩ : syracuseStep 5552059 = 8328089) B8328089
theorem B6166529 : Blo 1825614 6166529 := bstep (se 2 (by rfl) ⟨2312448, by rfl⟩ : syracuseStep 6166529 = 4624897) B4624897
theorem B15824899 : Blo 1825614 15824899 := bstep (se 1 (by rfl) ⟨11868674, by rfl⟩ : syracuseStep 15824899 = 23737349) B23737349
theorem B13867037 : Blo 1825614 13867037 := bstep (se 3 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 13867037 = 5200139) B5200139
theorem B22214999 : Blo 1825614 22214999 := bstep (se 1 (by rfl) ⟨16661249, by rfl⟩ : syracuseStep 22214999 = 33322499) B33322499
theorem B10008937 : Blo 1825614 10008937 := bstep (se 2 (by rfl) ⟨3753351, by rfl⟩ : syracuseStep 10008937 = 7506703) B7506703
theorem B35117549 : Blo 1825614 35117549 := bstep (se 3 (by rfl) ⟨6584540, by rfl⟩ : syracuseStep 35117549 = 13169081) B13169081
theorem B4110857 : Blo 1825614 4110857 := bstep (se 2 (by rfl) ⟨1541571, by rfl⟩ : syracuseStep 4110857 = 3083143) B3083143
theorem B14817815 : Blo 1825614 14817815 := bstep (se 1 (by rfl) ⟨11113361, by rfl⟩ : syracuseStep 14817815 = 22226723) B22226723
theorem B2054695 : Blo 1825614 2054695 := bstep (se 1 (by rfl) ⟨1541021, by rfl⟩ : syracuseStep 2054695 = 3082043) B3082043
theorem B13163143 : Blo 1825614 13163143 := bstep (se 1 (by rfl) ⟨9872357, by rfl⟩ : syracuseStep 13163143 = 19744715) B19744715
theorem B5200595 : Blo 1825614 5200595 := bstep (se 1 (by rfl) ⟨3900446, by rfl⟩ : syracuseStep 5200595 = 7800893) B7800893
theorem B6167339 : Blo 1825614 6167339 := bstep (se 1 (by rfl) ⟨4625504, by rfl⟩ : syracuseStep 6167339 = 9251009) B9251009
theorem B3291977 : Blo 1825614 3291977 := bstep (se 2 (by rfl) ⟨1234491, by rfl⟩ : syracuseStep 3291977 = 2468983) B2468983
theorem B1825615 : Blo 1825614 1825615 := bstep (se 1 (by rfl) ⟨1369211, by rfl⟩ : syracuseStep 1825615 = 2738423) B2738423
theorem B1825631 : Blo 1825614 1825631 := bstep (se 1 (by rfl) ⟨1369223, by rfl⟩ : syracuseStep 1825631 = 2738447) B2738447
theorem B4111199 : Blo 1825614 4111199 := bstep (se 1 (by rfl) ⟨3083399, by rfl⟩ : syracuseStep 4111199 = 6166799) B6166799
theorem B1825659 : Blo 1825614 1825659 := bstep (se 1 (by rfl) ⟨1369244, by rfl⟩ : syracuseStep 1825659 = 2738489) B2738489
theorem B1825711 : Blo 1825614 1825711 := bstep (se 1 (by rfl) ⟨1369283, by rfl⟩ : syracuseStep 1825711 = 2738567) B2738567
theorem B6585263 : Blo 1825614 6585263 := bstep (se 1 (by rfl) ⟨4938947, by rfl⟩ : syracuseStep 6585263 = 9877895) B9877895
theorem B5200823 : Blo 1825614 5200823 := bstep (se 1 (by rfl) ⟨3900617, by rfl⟩ : syracuseStep 5200823 = 7801235) B7801235
theorem B1825735 : Blo 1825614 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B1825755 : Blo 1825614 1825755 := bstep (se 1 (by rfl) ⟨1369316, by rfl⟩ : syracuseStep 1825755 = 2738633) B2738633
theorem B4111379 : Blo 1825614 4111379 := bstep (se 1 (by rfl) ⟨3083534, by rfl⟩ : syracuseStep 4111379 = 6167069) B6167069
theorem B2776103 : Blo 1825614 2776103 := bstep (se 1 (by rfl) ⟨2082077, by rfl⟩ : syracuseStep 2776103 = 4164155) B4164155
theorem B1825831 : Blo 1825614 1825831 := bstep (se 1 (by rfl) ⟨1369373, by rfl⟩ : syracuseStep 1825831 = 2738747) B2738747
theorem B6167609 : Blo 1825614 6167609 := bstep (se 2 (by rfl) ⟨2312853, by rfl⟩ : syracuseStep 6167609 = 4625707) B4625707
theorem B1825871 : Blo 1825614 1825871 := bstep (se 1 (by rfl) ⟨1369403, by rfl⟩ : syracuseStep 1825871 = 2738807) B2738807
theorem B1825887 : Blo 1825614 1825887 := bstep (se 1 (by rfl) ⟨1369415, by rfl⟩ : syracuseStep 1825887 = 2738831) B2738831
theorem B1825915 : Blo 1825614 1825915 := bstep (se 1 (by rfl) ⟨1369436, by rfl⟩ : syracuseStep 1825915 = 2738873) B2738873
theorem B6937757 : Blo 1825614 6937757 := bstep (se 3 (by rfl) ⟨1300829, by rfl⟩ : syracuseStep 6937757 = 2601659) B2601659
theorem B6937771 : Blo 1825614 6937771 := bstep (se 1 (by rfl) ⟨5203328, by rfl⟩ : syracuseStep 6937771 = 10406657) B10406657
theorem B1825967 : Blo 1825614 1825967 := bstep (se 1 (by rfl) ⟨1369475, by rfl⟩ : syracuseStep 1825967 = 2738951) B2738951
theorem B11107523 : Blo 1825614 11107523 := bstep (se 1 (by rfl) ⟨8330642, by rfl⟩ : syracuseStep 11107523 = 16661285) B16661285
theorem B1825991 : Blo 1825614 1825991 := bstep (se 1 (by rfl) ⟨1369493, by rfl⟩ : syracuseStep 1825991 = 2738987) B2738987
theorem B1826011 : Blo 1825614 1826011 := bstep (se 1 (by rfl) ⟨1369508, by rfl⟩ : syracuseStep 1826011 = 2739017) B2739017
theorem B33324311 : Blo 1825614 33324311 := bstep (se 1 (by rfl) ⟨24993233, by rfl⟩ : syracuseStep 33324311 = 49986467) B49986467
theorem B1826087 : Blo 1825614 1826087 := bstep (se 1 (by rfl) ⟨1369565, by rfl⟩ : syracuseStep 1826087 = 2739131) B2739131
theorem B1826127 : Blo 1825614 1826127 := bstep (se 1 (by rfl) ⟨1369595, by rfl⟩ : syracuseStep 1826127 = 2739191) B2739191
theorem B1826143 : Blo 1825614 1826143 := bstep (se 1 (by rfl) ⟨1369607, by rfl⟩ : syracuseStep 1826143 = 2739215) B2739215
theorem B4111721 : Blo 1825614 4111721 := bstep (se 2 (by rfl) ⟨1541895, by rfl⟩ : syracuseStep 4111721 = 3083791) B3083791
theorem B1826171 : Blo 1825614 1826171 := bstep (se 1 (by rfl) ⟨1369628, by rfl⟩ : syracuseStep 1826171 = 2739257) B2739257
theorem B6585725 : Blo 1825614 6585725 := bstep (se 3 (by rfl) ⟨1234823, by rfl⟩ : syracuseStep 6585725 = 2469647) B2469647
theorem B6167933 : Blo 1825614 6167933 := bstep (se 3 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 6167933 = 2312975) B2312975
theorem B15605135 : Blo 1825614 15605135 := bstep (se 1 (by rfl) ⟨11703851, by rfl⟩ : syracuseStep 15605135 = 23407703) B23407703
theorem B1826223 : Blo 1825614 1826223 := bstep (se 1 (by rfl) ⟨1369667, by rfl⟩ : syracuseStep 1826223 = 2739335) B2739335
theorem B1826247 : Blo 1825614 1826247 := bstep (se 1 (by rfl) ⟨1369685, by rfl⟩ : syracuseStep 1826247 = 2739371) B2739371
theorem B1826267 : Blo 1825614 1826267 := bstep (se 1 (by rfl) ⟨1369700, by rfl⟩ : syracuseStep 1826267 = 2739401) B2739401
theorem B6938075 : Blo 1825614 6938075 := bstep (se 1 (by rfl) ⟨5203556, by rfl⟩ : syracuseStep 6938075 = 10407113) B10407113
theorem B1826343 : Blo 1825614 1826343 := bstep (se 1 (by rfl) ⟨1369757, by rfl⟩ : syracuseStep 1826343 = 2739515) B2739515
theorem B3513935 : Blo 1825614 3513935 := bstep (se 1 (by rfl) ⟨2635451, by rfl⟩ : syracuseStep 3513935 = 5270903) B5270903
theorem B1826383 : Blo 1825614 1826383 := bstep (se 1 (by rfl) ⟨1369787, by rfl⟩ : syracuseStep 1826383 = 2739575) B2739575
theorem B1826399 : Blo 1825614 1826399 := bstep (se 1 (by rfl) ⟨1369799, by rfl⟩ : syracuseStep 1826399 = 2739599) B2739599
theorem B1826427 : Blo 1825614 1826427 := bstep (se 1 (by rfl) ⟨1369820, by rfl⟩ : syracuseStep 1826427 = 2739641) B2739641
theorem B1826479 : Blo 1825614 1826479 := bstep (se 1 (by rfl) ⟨1369859, by rfl⟩ : syracuseStep 1826479 = 2739719) B2739719
theorem B11697853 : Blo 1825614 11697853 := bstep (se 3 (by rfl) ⟨2193347, by rfl⟩ : syracuseStep 11697853 = 4386695) B4386695
theorem B5201597 : Blo 1825614 5201597 := bstep (se 3 (by rfl) ⟨975299, by rfl⟩ : syracuseStep 5201597 = 1950599) B1950599
theorem B1826503 : Blo 1825614 1826503 := bstep (se 1 (by rfl) ⟨1369877, by rfl⟩ : syracuseStep 1826503 = 2739755) B2739755
theorem B1826523 : Blo 1825614 1826523 := bstep (se 1 (by rfl) ⟨1369892, by rfl⟩ : syracuseStep 1826523 = 2739785) B2739785
theorem B1826599 : Blo 1825614 1826599 := bstep (se 1 (by rfl) ⟨1369949, by rfl⟩ : syracuseStep 1826599 = 2739899) B2739899
theorem B9248579 : Blo 1825614 9248579 := bstep (se 1 (by rfl) ⟨6936434, by rfl⟩ : syracuseStep 9248579 = 13872869) B13872869
theorem B1826639 : Blo 1825614 1826639 := bstep (se 1 (by rfl) ⟨1369979, by rfl⟩ : syracuseStep 1826639 = 2739959) B2739959
theorem B1826655 : Blo 1825614 1826655 := bstep (se 1 (by rfl) ⟨1369991, by rfl⟩ : syracuseStep 1826655 = 2739983) B2739983
theorem B29622131 : Blo 1825614 29622131 := bstep (se 1 (by rfl) ⟨22216598, by rfl⟩ : syracuseStep 29622131 = 44433197) B44433197
theorem B1826683 : Blo 1825614 1826683 := bstep (se 1 (by rfl) ⟨1370012, by rfl⟩ : syracuseStep 1826683 = 2740025) B2740025
theorem B1826735 : Blo 1825614 1826735 := bstep (se 1 (by rfl) ⟨1370051, by rfl⟩ : syracuseStep 1826735 = 2740103) B2740103
theorem B15810491 : Blo 1825614 15810491 := bstep (se 1 (by rfl) ⟨11857868, by rfl⟩ : syracuseStep 15810491 = 23715737) B23715737
theorem B1826759 : Blo 1825614 1826759 := bstep (se 1 (by rfl) ⟨1370069, by rfl⟩ : syracuseStep 1826759 = 2740139) B2740139
theorem B1826779 : Blo 1825614 1826779 := bstep (se 1 (by rfl) ⟨1370084, by rfl⟩ : syracuseStep 1826779 = 2740169) B2740169
theorem B6938729 : Blo 1825614 6938729 := bstep (se 2 (by rfl) ⟨2602023, by rfl⟩ : syracuseStep 6938729 = 5204047) B5204047
theorem B4940041 : Blo 1825614 4940041 := bstep (se 2 (by rfl) ⟨1852515, by rfl⟩ : syracuseStep 4940041 = 3705031) B3705031
theorem B1827103 : Blo 1825614 1827103 := bstep (se 1 (by rfl) ⟨1370327, by rfl⟩ : syracuseStep 1827103 = 2740655) B2740655
theorem B24985907 : Blo 1825614 24985907 := bstep (se 1 (by rfl) ⟨18739430, by rfl⟩ : syracuseStep 24985907 = 37478861) B37478861
theorem B1827163 : Blo 1825614 1827163 := bstep (se 1 (by rfl) ⟨1370372, by rfl⟩ : syracuseStep 1827163 = 2740745) B2740745
theorem B3899755 : Blo 1825614 3899755 := bstep (se 1 (by rfl) ⟨2924816, by rfl⟩ : syracuseStep 3899755 = 5849633) B5849633
theorem B1827183 : Blo 1825614 1827183 := bstep (se 1 (by rfl) ⟨1370387, by rfl⟩ : syracuseStep 1827183 = 2740775) B2740775
theorem B1827239 : Blo 1825614 1827239 := bstep (se 1 (by rfl) ⟨1370429, by rfl⟩ : syracuseStep 1827239 = 2740859) B2740859
theorem B3899831 : Blo 1825614 3899831 := bstep (se 1 (by rfl) ⟨2924873, by rfl⟩ : syracuseStep 3899831 = 5849747) B5849747
theorem B1950151 : Blo 1825614 1950151 := bstep (se 1 (by rfl) ⟨1462613, by rfl⟩ : syracuseStep 1950151 = 2925227) B2925227
theorem B13345249 : Blo 1825614 13345249 := bstep (se 2 (by rfl) ⟨5004468, by rfl⟩ : syracuseStep 13345249 = 10008937) B10008937
theorem B3564001 : Blo 1825614 3564001 := bstep (se 2 (by rfl) ⟨1336500, by rfl⟩ : syracuseStep 3564001 = 2673001) B2673001
theorem B13877729 : Blo 1825614 13877729 := bstep (se 2 (by rfl) ⟨5204148, by rfl⟩ : syracuseStep 13877729 = 10408297) B10408297
theorem B1827323 : Blo 1825614 1827323 := bstep (se 1 (by rfl) ⟨1370492, by rfl⟩ : syracuseStep 1827323 = 2740985) B2740985
theorem B3080767 : Blo 1825614 3080767 := bstep (se 1 (by rfl) ⟨2310575, by rfl⟩ : syracuseStep 3080767 = 4621151) B4621151
theorem B2343487 : Blo 1825614 2343487 := bstep (se 1 (by rfl) ⟨1757615, by rfl⟩ : syracuseStep 2343487 = 3515231) B3515231
theorem B1827391 : Blo 1825614 1827391 := bstep (se 1 (by rfl) ⟨1370543, by rfl⟩ : syracuseStep 1827391 = 2741087) B2741087
theorem B5849671 : Blo 1825614 5849671 := bstep (se 1 (by rfl) ⟨4387253, by rfl⟩ : syracuseStep 5849671 = 8774507) B8774507
theorem B1827399 : Blo 1825614 1827399 := bstep (se 1 (by rfl) ⟨1370549, by rfl⟩ : syracuseStep 1827399 = 2741099) B2741099
theorem B2310763 : Blo 1825614 2310763 := bstep (se 1 (by rfl) ⟨1733072, by rfl⟩ : syracuseStep 2310763 = 3466145) B3466145
theorem B13173463 : Blo 1825614 13173463 := bstep (se 1 (by rfl) ⟨9880097, by rfl⟩ : syracuseStep 13173463 = 19760195) B19760195
theorem B1827551 : Blo 1825614 1827551 := bstep (se 1 (by rfl) ⟨1370663, by rfl⟩ : syracuseStep 1827551 = 2741327) B2741327
theorem B2286415 : Blo 1825614 2286415 := bstep (se 1 (by rfl) ⟨1714811, by rfl⟩ : syracuseStep 2286415 = 3429623) B3429623
theorem B9372611 : Blo 1825614 9372611 := bstep (se 1 (by rfl) ⟨7029458, by rfl⟩ : syracuseStep 9372611 = 14058917) B14058917
theorem B33776605 : Blo 1825614 33776605 := bstep (se 3 (by rfl) ⟨6333113, by rfl⟩ : syracuseStep 33776605 = 12666227) B12666227
theorem B3703799 : Blo 1825614 3703799 := bstep (se 1 (by rfl) ⟨2777849, by rfl⟩ : syracuseStep 3703799 = 5555699) B5555699
theorem B3081449 : Blo 1825614 3081449 := bstep (se 2 (by rfl) ⟨1155543, by rfl⟩ : syracuseStep 3081449 = 2311087) B2311087
theorem B3081503 : Blo 1825614 3081503 := bstep (se 1 (by rfl) ⟨2311127, by rfl⟩ : syracuseStep 3081503 = 4622255) B4622255
theorem B4621607 : Blo 1825614 4621607 := bstep (se 1 (by rfl) ⟨3466205, by rfl⟩ : syracuseStep 4621607 = 6932411) B6932411
theorem B9250361 : Blo 1825614 9250361 := bstep (se 2 (by rfl) ⟨3468885, by rfl⟩ : syracuseStep 9250361 = 6937771) B6937771
theorem B2344631 : Blo 1825614 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B9242423 : Blo 1825614 9242423 := bstep (se 1 (by rfl) ⟨6931817, by rfl⟩ : syracuseStep 9242423 = 13863635) B13863635
theorem B3467063 : Blo 1825614 3467063 := bstep (se 1 (by rfl) ⟨2600297, by rfl⟩ : syracuseStep 3467063 = 5200595) B5200595
theorem B13870925 : Blo 1825614 13870925 := bstep (se 3 (by rfl) ⟨2600798, by rfl⟩ : syracuseStep 13870925 = 5201597) B5201597
theorem B6162263 : Blo 1825614 6162263 := bstep (se 1 (by rfl) ⟨4621697, by rfl⟩ : syracuseStep 6162263 = 9243395) B9243395
theorem B3467215 : Blo 1825614 3467215 := bstep (se 1 (by rfl) ⟨2600411, by rfl⟩ : syracuseStep 3467215 = 5200823) B5200823
theorem B7800961 : Blo 1825614 7800961 := bstep (se 2 (by rfl) ⟨2925360, by rfl⟩ : syracuseStep 7800961 = 5850721) B5850721
theorem B2738441 : Blo 1825614 2738441 := bstep (se 2 (by rfl) ⟨1026915, by rfl⟩ : syracuseStep 2738441 = 2053831) B2053831
theorem B9242909 : Blo 1825614 9242909 := bstep (se 3 (by rfl) ⟨1733045, by rfl⟩ : syracuseStep 9242909 = 3466091) B3466091
theorem B2312479 : Blo 1825614 2312479 := bstep (se 1 (by rfl) ⟨1734359, by rfl⟩ : syracuseStep 2312479 = 3468719) B3468719
theorem B2738543 : Blo 1825614 2738543 := bstep (se 1 (by rfl) ⟨2053907, by rfl⟩ : syracuseStep 2738543 = 4107815) B4107815
theorem B2738759 : Blo 1825614 2738759 := bstep (se 1 (by rfl) ⟨2054069, by rfl⟩ : syracuseStep 2738759 = 4108139) B4108139
theorem B2738795 : Blo 1825614 2738795 := bstep (se 1 (by rfl) ⟨2054096, by rfl⟩ : syracuseStep 2738795 = 4108193) B4108193
theorem B3082873 : Blo 1825614 3082873 := bstep (se 2 (by rfl) ⟨1156077, by rfl⟩ : syracuseStep 3082873 = 2312155) B2312155
theorem B3082927 : Blo 1825614 3082927 := bstep (se 1 (by rfl) ⟨2312195, by rfl⟩ : syracuseStep 3082927 = 4624391) B4624391
theorem B4623095 : Blo 1825614 4623095 := bstep (se 1 (by rfl) ⟨3467321, by rfl⟩ : syracuseStep 4623095 = 6934643) B6934643
theorem B2739023 : Blo 1825614 2739023 := bstep (se 1 (by rfl) ⟨2054267, by rfl⟩ : syracuseStep 2739023 = 4108535) B4108535
theorem B6163343 : Blo 1825614 6163343 := bstep (se 1 (by rfl) ⟨4622507, by rfl⟩ : syracuseStep 6163343 = 9245015) B9245015
theorem B3468187 : Blo 1825614 3468187 := bstep (se 1 (by rfl) ⟨2601140, by rfl⟩ : syracuseStep 3468187 = 5202281) B5202281
theorem B9874547 : Blo 1825614 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B6581371 : Blo 1825614 6581371 := bstep (se 1 (by rfl) ⟨4936028, by rfl⟩ : syracuseStep 6581371 = 9872057) B9872057
theorem B23399603 : Blo 1825614 23399603 := bstep (se 1 (by rfl) ⟨17549702, by rfl⟩ : syracuseStep 23399603 = 35099405) B35099405
theorem B2739419 : Blo 1825614 2739419 := bstep (se 1 (by rfl) ⟨2054564, by rfl⟩ : syracuseStep 2739419 = 4109129) B4109129
theorem B3468521 : Blo 1825614 3468521 := bstep (se 2 (by rfl) ⟨1300695, by rfl⟩ : syracuseStep 3468521 = 2601391) B2601391
theorem B80227601 : Blo 1825614 80227601 := bstep (se 2 (by rfl) ⟨30085350, by rfl⟩ : syracuseStep 80227601 = 60170701) B60170701
theorem B16895263 : Blo 1825614 16895263 := bstep (se 1 (by rfl) ⟨12671447, by rfl⟩ : syracuseStep 16895263 = 25342895) B25342895
theorem B3468575 : Blo 1825614 3468575 := bstep (se 1 (by rfl) ⟨2601431, by rfl⟩ : syracuseStep 3468575 = 5202863) B5202863
theorem B4623713 : Blo 1825614 4623713 := bstep (se 2 (by rfl) ⟨1733892, by rfl⟩ : syracuseStep 4623713 = 3467785) B3467785
theorem B2739593 : Blo 1825614 2739593 := bstep (se 2 (by rfl) ⟨1027347, by rfl⟩ : syracuseStep 2739593 = 2054695) B2054695
theorem B4107707 : Blo 1825614 4107707 := bstep (se 1 (by rfl) ⟨3080780, by rfl⟩ : syracuseStep 4107707 = 6161561) B6161561
theorem B2469371 : Blo 1825614 2469371 := bstep (se 1 (by rfl) ⟨1852028, by rfl⟩ : syracuseStep 2469371 = 3704057) B3704057
theorem B17550857 : Blo 1825614 17550857 := bstep (se 2 (by rfl) ⟨6581571, by rfl⟩ : syracuseStep 17550857 = 13163143) B13163143
theorem B4107833 : Blo 1825614 4107833 := bstep (se 2 (by rfl) ⟨1540437, by rfl⟩ : syracuseStep 4107833 = 3080875) B3080875
theorem B14814829 : Blo 1825614 14814829 := bstep (se 3 (by rfl) ⟨2777780, by rfl⟩ : syracuseStep 14814829 = 5555561) B5555561
theorem B2739947 : Blo 1825614 2739947 := bstep (se 1 (by rfl) ⟨2054960, by rfl⟩ : syracuseStep 2739947 = 4109921) B4109921
theorem B8335165 : Blo 1825614 8335165 := bstep (se 3 (by rfl) ⟨1562843, by rfl⟩ : syracuseStep 8335165 = 3125687) B3125687
theorem B2740175 : Blo 1825614 2740175 := bstep (se 1 (by rfl) ⟨2055131, by rfl⟩ : syracuseStep 2740175 = 4110263) B4110263
theorem B9244691 : Blo 1825614 9244691 := bstep (se 1 (by rfl) ⟨6933518, by rfl⟩ : syracuseStep 9244691 = 13867037) B13867037
theorem B6164585 : Blo 1825614 6164585 := bstep (se 2 (by rfl) ⟨2311719, by rfl⟩ : syracuseStep 6164585 = 4623439) B4623439
theorem B13873355 : Blo 1825614 13873355 := bstep (se 1 (by rfl) ⟨10405016, by rfl⟩ : syracuseStep 13873355 = 20810033) B20810033
theorem B4108499 : Blo 1825614 4108499 := bstep (se 1 (by rfl) ⟨3081374, by rfl⟩ : syracuseStep 4108499 = 6162749) B6162749
theorem B4108553 : Blo 1825614 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B2740571 : Blo 1825614 2740571 := bstep (se 1 (by rfl) ⟨2055428, by rfl⟩ : syracuseStep 2740571 = 4110857) B4110857
theorem B7803337 : Blo 1825614 7803337 := bstep (se 2 (by rfl) ⟨2926251, by rfl⟩ : syracuseStep 7803337 = 5852503) B5852503
theorem B4108769 : Blo 1825614 4108769 := bstep (se 2 (by rfl) ⟨1540788, by rfl⟩ : syracuseStep 4108769 = 3081577) B3081577
theorem B17797681 : Blo 1825614 17797681 := bstep (se 2 (by rfl) ⟨6674130, by rfl⟩ : syracuseStep 17797681 = 13348261) B13348261
theorem B2740799 : Blo 1825614 2740799 := bstep (se 1 (by rfl) ⟨2055599, by rfl⟩ : syracuseStep 2740799 = 4111199) B4111199
theorem B8778311 : Blo 1825614 8778311 := bstep (se 1 (by rfl) ⟨6583733, by rfl⟩ : syracuseStep 8778311 = 13167467) B13167467
theorem B52064909 : Blo 1825614 52064909 := bstep (se 3 (by rfl) ⟨9762170, by rfl⟩ : syracuseStep 52064909 = 19524341) B19524341
theorem B2740919 : Blo 1825614 2740919 := bstep (se 1 (by rfl) ⟨2055689, by rfl⟩ : syracuseStep 2740919 = 4111379) B4111379
theorem B11104991 : Blo 1825614 11104991 := bstep (se 1 (by rfl) ⟨8328743, by rfl⟩ : syracuseStep 11104991 = 16657487) B16657487
theorem B4109075 : Blo 1825614 4109075 := bstep (se 1 (by rfl) ⟨3081806, by rfl⟩ : syracuseStep 4109075 = 6163613) B6163613
theorem B4625171 : Blo 1825614 4625171 := bstep (se 1 (by rfl) ⟨3468878, by rfl⟩ : syracuseStep 4625171 = 6937757) B6937757
theorem B2741147 : Blo 1825614 2741147 := bstep (se 1 (by rfl) ⟨2055860, by rfl⟩ : syracuseStep 2741147 = 4111721) B4111721
theorem B6165449 : Blo 1825614 6165449 := bstep (se 2 (by rfl) ⟨2312043, by rfl⟩ : syracuseStep 6165449 = 4624087) B4624087
theorem B4625383 : Blo 1825614 4625383 := bstep (se 1 (by rfl) ⟨3469037, by rfl⟩ : syracuseStep 4625383 = 6938075) B6938075
theorem B10400825 : Blo 1825614 10400825 := bstep (se 2 (by rfl) ⟨3900309, by rfl⟩ : syracuseStep 10400825 = 7800619) B7800619
theorem B4109435 : Blo 1825614 4109435 := bstep (se 1 (by rfl) ⟨3082076, by rfl⟩ : syracuseStep 4109435 = 6164153) B6164153
theorem B6165719 : Blo 1825614 6165719 := bstep (se 1 (by rfl) ⟨4624289, by rfl⟩ : syracuseStep 6165719 = 9248579) B9248579
theorem B19748087 : Blo 1825614 19748087 := bstep (se 1 (by rfl) ⟨14811065, by rfl⟩ : syracuseStep 19748087 = 29622131) B29622131
theorem B7402745 : Blo 1825614 7402745 := bstep (se 2 (by rfl) ⟨2776029, by rfl⟩ : syracuseStep 7402745 = 5552059) B5552059
theorem B4109561 : Blo 1825614 4109561 := bstep (se 2 (by rfl) ⟨1541085, by rfl⟩ : syracuseStep 4109561 = 3082171) B3082171
theorem B4625657 : Blo 1825614 4625657 := bstep (se 2 (by rfl) ⟨1734621, by rfl⟩ : syracuseStep 4625657 = 3469243) B3469243
theorem B10540327 : Blo 1825614 10540327 := bstep (se 1 (by rfl) ⟨7905245, by rfl⟩ : syracuseStep 10540327 = 15810491) B15810491
theorem B21099865 : Blo 1825614 21099865 := bstep (se 2 (by rfl) ⟨7912449, by rfl⟩ : syracuseStep 21099865 = 15824899) B15824899
theorem B4109705 : Blo 1825614 4109705 := bstep (se 2 (by rfl) ⟨1541139, by rfl⟩ : syracuseStep 4109705 = 3082279) B3082279
theorem B18748865 : Blo 1825614 18748865 := bstep (se 2 (by rfl) ⟨7030824, by rfl⟩ : syracuseStep 18748865 = 14061649) B14061649
theorem B4109831 : Blo 1825614 4109831 := bstep (se 1 (by rfl) ⟨3082373, by rfl⟩ : syracuseStep 4109831 = 6164747) B6164747
theorem B5199547 : Blo 1825614 5199547 := bstep (se 1 (by rfl) ⟨3899660, by rfl⟩ : syracuseStep 5199547 = 7799321) B7799321
theorem B4110011 : Blo 1825614 4110011 := bstep (se 1 (by rfl) ⟨3082508, by rfl⟩ : syracuseStep 4110011 = 6165017) B6165017
theorem B4110137 : Blo 1825614 4110137 := bstep (se 2 (by rfl) ⟨1541301, by rfl⟩ : syracuseStep 4110137 = 3082603) B3082603
theorem B2054119 : Blo 1825614 2054119 := bstep (se 1 (by rfl) ⟨1540589, by rfl⟩ : syracuseStep 2054119 = 3081179) B3081179
theorem B52664327 : Blo 1825614 52664327 := bstep (se 1 (by rfl) ⟨39498245, by rfl⟩ : syracuseStep 52664327 = 78996491) B78996491
theorem B22222927 : Blo 1825614 22222927 := bstep (se 1 (by rfl) ⟨16667195, by rfl⟩ : syracuseStep 22222927 = 33334391) B33334391
theorem B4110767 : Blo 1825614 4110767 := bstep (se 1 (by rfl) ⟨3083075, by rfl⟩ : syracuseStep 4110767 = 6166151) B6166151
theorem B4110803 : Blo 1825614 4110803 := bstep (se 1 (by rfl) ⟨3083102, by rfl⟩ : syracuseStep 4110803 = 6166205) B6166205
theorem B4110911 : Blo 1825614 4110911 := bstep (se 1 (by rfl) ⟨3083183, by rfl⟩ : syracuseStep 4110911 = 6166367) B6166367
theorem B13875785 : Blo 1825614 13875785 := bstep (se 2 (by rfl) ⟨5203419, by rfl⟩ : syracuseStep 13875785 = 10406839) B10406839
theorem B4111019 : Blo 1825614 4111019 := bstep (se 1 (by rfl) ⟨3083264, by rfl⟩ : syracuseStep 4111019 = 6166529) B6166529
theorem B9247607 : Blo 1825614 9247607 := bstep (se 1 (by rfl) ⟨6935705, by rfl⟩ : syracuseStep 9247607 = 13871411) B13871411
theorem B14809999 : Blo 1825614 14809999 := bstep (se 1 (by rfl) ⟨11107499, by rfl⟩ : syracuseStep 14809999 = 22214999) B22214999
theorem B17554319 : Blo 1825614 17554319 := bstep (se 1 (by rfl) ⟨13165739, by rfl⟩ : syracuseStep 17554319 = 26331479) B26331479
theorem B1825691 : Blo 1825614 1825691 := bstep (se 1 (by rfl) ⟨1369268, by rfl⟩ : syracuseStep 1825691 = 2738537) B2738537
theorem B15612857 : Blo 1825614 15612857 := bstep (se 2 (by rfl) ⟨5854821, by rfl⟩ : syracuseStep 15612857 = 11709643) B11709643
theorem B1825743 : Blo 1825614 1825743 := bstep (se 1 (by rfl) ⟨1369307, by rfl⟩ : syracuseStep 1825743 = 2738615) B2738615
theorem B1825767 : Blo 1825614 1825767 := bstep (se 1 (by rfl) ⟨1369325, by rfl⟩ : syracuseStep 1825767 = 2738651) B2738651
theorem B23411699 : Blo 1825614 23411699 := bstep (se 1 (by rfl) ⟨17558774, by rfl⟩ : syracuseStep 23411699 = 35117549) B35117549
theorem B9878543 : Blo 1825614 9878543 := bstep (se 1 (by rfl) ⟨7408907, by rfl⟩ : syracuseStep 9878543 = 14817815) B14817815
theorem B4111559 : Blo 1825614 4111559 := bstep (se 1 (by rfl) ⟨3083669, by rfl⟩ : syracuseStep 4111559 = 6167339) B6167339
theorem B2194651 : Blo 1825614 2194651 := bstep (se 1 (by rfl) ⟨1645988, by rfl⟩ : syracuseStep 2194651 = 3291977) B3291977
theorem B6167771 : Blo 1825614 6167771 := bstep (se 1 (by rfl) ⟨4625828, by rfl⟩ : syracuseStep 6167771 = 9251657) B9251657
theorem B2776297 : Blo 1825614 2776297 := bstep (se 2 (by rfl) ⟨1041111, by rfl⟩ : syracuseStep 2776297 = 2082223) B2082223
theorem B1826079 : Blo 1825614 1826079 := bstep (se 1 (by rfl) ⟨1369559, by rfl⟩ : syracuseStep 1826079 = 2739119) B2739119
theorem B4390175 : Blo 1825614 4390175 := bstep (se 1 (by rfl) ⟨3292631, by rfl⟩ : syracuseStep 4390175 = 6585263) B6585263
theorem B1826139 : Blo 1825614 1826139 := bstep (se 1 (by rfl) ⟨1369604, by rfl⟩ : syracuseStep 1826139 = 2739209) B2739209
theorem B1850735 : Blo 1825614 1850735 := bstep (se 1 (by rfl) ⟨1388051, by rfl⟩ : syracuseStep 1850735 = 2776103) B2776103
theorem B1826159 : Blo 1825614 1826159 := bstep (se 1 (by rfl) ⟨1369619, by rfl⟩ : syracuseStep 1826159 = 2739239) B2739239
theorem B4111739 : Blo 1825614 4111739 := bstep (se 1 (by rfl) ⟨3083804, by rfl⟩ : syracuseStep 4111739 = 6167609) B6167609
theorem B1826215 : Blo 1825614 1826215 := bstep (se 1 (by rfl) ⟨1369661, by rfl⟩ : syracuseStep 1826215 = 2739323) B2739323
theorem B7806395 : Blo 1825614 7806395 := bstep (se 1 (by rfl) ⟨5854796, by rfl⟩ : syracuseStep 7806395 = 11709593) B11709593
theorem B7405015 : Blo 1825614 7405015 := bstep (se 1 (by rfl) ⟨5553761, by rfl⟩ : syracuseStep 7405015 = 11107523) B11107523
theorem B4111865 : Blo 1825614 4111865 := bstep (se 2 (by rfl) ⟨1541949, by rfl⟩ : syracuseStep 4111865 = 3083899) B3083899
theorem B1826299 : Blo 1825614 1826299 := bstep (se 1 (by rfl) ⟨1369724, by rfl⟩ : syracuseStep 1826299 = 2739449) B2739449
theorem B22216207 : Blo 1825614 22216207 := bstep (se 1 (by rfl) ⟨16662155, by rfl⟩ : syracuseStep 22216207 = 33324311) B33324311
theorem B1826367 : Blo 1825614 1826367 := bstep (se 1 (by rfl) ⟨1369775, by rfl⟩ : syracuseStep 1826367 = 2739551) B2739551
theorem B1826375 : Blo 1825614 1826375 := bstep (se 1 (by rfl) ⟨1369781, by rfl⟩ : syracuseStep 1826375 = 2739563) B2739563
theorem B15597137 : Blo 1825614 15597137 := bstep (se 2 (by rfl) ⟨5848926, by rfl⟩ : syracuseStep 15597137 = 11697853) B11697853
theorem B4390483 : Blo 1825614 4390483 := bstep (se 1 (by rfl) ⟨3292862, by rfl⟩ : syracuseStep 4390483 = 6585725) B6585725
theorem B4111955 : Blo 1825614 4111955 := bstep (se 1 (by rfl) ⟨3083966, by rfl⟩ : syracuseStep 4111955 = 6167933) B6167933
theorem B10403423 : Blo 1825614 10403423 := bstep (se 1 (by rfl) ⟨7802567, by rfl⟩ : syracuseStep 10403423 = 15605135) B15605135
theorem B2055775 : Blo 1825614 2055775 := bstep (se 1 (by rfl) ⟨1541831, by rfl⟩ : syracuseStep 2055775 = 3083663) B3083663
theorem B9248417 : Blo 1825614 9248417 := bstep (se 2 (by rfl) ⟨3468156, by rfl⟩ : syracuseStep 9248417 = 6936313) B6936313
theorem B2342623 : Blo 1825614 2342623 := bstep (se 1 (by rfl) ⟨1756967, by rfl⟩ : syracuseStep 2342623 = 3513935) B3513935
theorem B1826527 : Blo 1825614 1826527 := bstep (se 1 (by rfl) ⟨1369895, by rfl⟩ : syracuseStep 1826527 = 2739791) B2739791
theorem B1826607 : Blo 1825614 1826607 := bstep (se 1 (by rfl) ⟨1369955, by rfl⟩ : syracuseStep 1826607 = 2739911) B2739911
theorem B1826715 : Blo 1825614 1826715 := bstep (se 1 (by rfl) ⟨1370036, by rfl⟩ : syracuseStep 1826715 = 2740073) B2740073
theorem B1826767 : Blo 1825614 1826767 := bstep (se 1 (by rfl) ⟨1370075, by rfl⟩ : syracuseStep 1826767 = 2740151) B2740151
theorem B1826791 : Blo 1825614 1826791 := bstep (se 1 (by rfl) ⟨1370093, by rfl⟩ : syracuseStep 1826791 = 2740187) B2740187
theorem B29630569 : Blo 1825614 29630569 := bstep (se 2 (by rfl) ⟨11111463, by rfl⟩ : syracuseStep 29630569 = 22222927) B22222927
theorem B9248903 : Blo 1825614 9248903 := bstep (se 1 (by rfl) ⟨6936677, by rfl⟩ : syracuseStep 9248903 = 13873355) B13873355
theorem B1827047 : Blo 1825614 1827047 := bstep (se 1 (by rfl) ⟨1370285, by rfl⟩ : syracuseStep 1827047 = 2740571) B2740571
theorem B6586721 : Blo 1825614 6586721 := bstep (se 2 (by rfl) ⟨2470020, by rfl⟩ : syracuseStep 6586721 = 4940041) B4940041
theorem B1827199 : Blo 1825614 1827199 := bstep (se 1 (by rfl) ⟨1370399, by rfl⟩ : syracuseStep 1827199 = 2740799) B2740799
theorem B34709939 : Blo 1825614 34709939 := bstep (se 1 (by rfl) ⟨26032454, by rfl⟩ : syracuseStep 34709939 = 52064909) B52064909
theorem B1827279 : Blo 1825614 1827279 := bstep (se 1 (by rfl) ⟨1370459, by rfl⟩ : syracuseStep 1827279 = 2740919) B2740919
theorem B10404449 : Blo 1825614 10404449 := bstep (se 2 (by rfl) ⟨3901668, by rfl⟩ : syracuseStep 10404449 = 7803337) B7803337
theorem B1827431 : Blo 1825614 1827431 := bstep (se 1 (by rfl) ⟨1370573, by rfl⟩ : syracuseStep 1827431 = 2741147) B2741147
theorem B9249389 : Blo 1825614 9249389 := bstep (se 3 (by rfl) ⟨1734260, by rfl⟩ : syracuseStep 9249389 = 3468521) B3468521
theorem B17793665 : Blo 1825614 17793665 := bstep (se 2 (by rfl) ⟨6672624, by rfl⟩ : syracuseStep 17793665 = 13345249) B13345249
theorem B4752001 : Blo 1825614 4752001 := bstep (se 2 (by rfl) ⟨1782000, by rfl⟩ : syracuseStep 4752001 = 3564001) B3564001
theorem B7799561 : Blo 1825614 7799561 := bstep (se 2 (by rfl) ⟨2924835, by rfl⟩ : syracuseStep 7799561 = 5849671) B5849671
theorem B3081017 : Blo 1825614 3081017 := bstep (se 2 (by rfl) ⟨1155381, by rfl⟩ : syracuseStep 3081017 = 2310763) B2310763
theorem B13165391 : Blo 1825614 13165391 := bstep (se 1 (by rfl) ⟨9874043, by rfl⟩ : syracuseStep 13165391 = 19748087) B19748087
theorem B3081071 : Blo 1825614 3081071 := bstep (se 1 (by rfl) ⟨2310803, by rfl⟩ : syracuseStep 3081071 = 4621607) B4621607
theorem B17564617 : Blo 1825614 17564617 := bstep (se 2 (by rfl) ⟨6586731, by rfl⟩ : syracuseStep 17564617 = 13173463) B13173463
theorem B3048553 : Blo 1825614 3048553 := bstep (se 2 (by rfl) ⟨1143207, by rfl⟩ : syracuseStep 3048553 = 2286415) B2286415
theorem B49996973 : Blo 1825614 49996973 := bstep (se 3 (by rfl) ⟨9374432, by rfl⟩ : syracuseStep 49996973 = 18748865) B18748865
theorem B6161615 : Blo 1825614 6161615 := bstep (se 1 (by rfl) ⟨4621211, by rfl⟩ : syracuseStep 6161615 = 9242423) B9242423
theorem B8775161 : Blo 1825614 8775161 := bstep (se 2 (by rfl) ⟨3290685, by rfl⟩ : syracuseStep 8775161 = 6581371) B6581371
theorem B6161939 : Blo 1825614 6161939 := bstep (se 1 (by rfl) ⟨4621454, by rfl⟩ : syracuseStep 6161939 = 9242909) B9242909
theorem B2926201 : Blo 1825614 2926201 := bstep (se 2 (by rfl) ⟨1097325, by rfl⟩ : syracuseStep 2926201 = 2194651) B2194651
theorem B9250523 : Blo 1825614 9250523 := bstep (se 1 (by rfl) ⟨6937892, by rfl⟩ : syracuseStep 9250523 = 13875785) B13875785
theorem B28133153 : Blo 1825614 28133153 := bstep (se 2 (by rfl) ⟨10549932, by rfl⟩ : syracuseStep 28133153 = 21099865) B21099865
theorem B6252349 : Blo 1825614 6252349 := bstep (se 3 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 6252349 = 2344631) B2344631
theorem B3082063 : Blo 1825614 3082063 := bstep (se 1 (by rfl) ⟨2311547, by rfl⟩ : syracuseStep 3082063 = 4623095) B4623095
theorem B9873353 : Blo 1825614 9873353 := bstep (se 2 (by rfl) ⟨3702507, by rfl⟩ : syracuseStep 9873353 = 7405015) B7405015
theorem B15607799 : Blo 1825614 15607799 := bstep (se 1 (by rfl) ⟨11705849, by rfl⟩ : syracuseStep 15607799 = 23411699) B23411699
theorem B15599735 : Blo 1825614 15599735 := bstep (se 1 (by rfl) ⟨11699801, by rfl⟩ : syracuseStep 15599735 = 23399603) B23399603
theorem B19753105 : Blo 1825614 19753105 := bstep (se 2 (by rfl) ⟨7407414, by rfl⟩ : syracuseStep 19753105 = 14814829) B14814829
theorem B2312383 : Blo 1825614 2312383 := bstep (se 1 (by rfl) ⟨1734287, by rfl⟩ : syracuseStep 2312383 = 3468575) B3468575
theorem B2926783 : Blo 1825614 2926783 := bstep (se 1 (by rfl) ⟨2195087, by rfl⟩ : syracuseStep 2926783 = 4390175) B4390175
theorem B3082475 : Blo 1825614 3082475 := bstep (se 1 (by rfl) ⟨2311856, by rfl⟩ : syracuseStep 3082475 = 4623713) B4623713
theorem B6932729 : Blo 1825614 6932729 := bstep (se 2 (by rfl) ⟨2599773, by rfl⟩ : syracuseStep 6932729 = 5199547) B5199547
theorem B2738471 : Blo 1825614 2738471 := bstep (se 1 (by rfl) ⟨2053853, by rfl⟩ : syracuseStep 2738471 = 4107707) B4107707
theorem B5204263 : Blo 1825614 5204263 := bstep (se 1 (by rfl) ⟨3903197, by rfl⟩ : syracuseStep 5204263 = 7806395) B7806395
theorem B11700571 : Blo 1825614 11700571 := bstep (se 1 (by rfl) ⟨8775428, by rfl⟩ : syracuseStep 11700571 = 17550857) B17550857
theorem B2738555 : Blo 1825614 2738555 := bstep (se 1 (by rfl) ⟨2053916, by rfl⟩ : syracuseStep 2738555 = 4107833) B4107833
theorem B10398091 : Blo 1825614 10398091 := bstep (se 1 (by rfl) ⟨7798568, by rfl⟩ : syracuseStep 10398091 = 15597137) B15597137
theorem B4622953 : Blo 1825614 4622953 := bstep (se 2 (by rfl) ⟨1733607, by rfl⟩ : syracuseStep 4622953 = 3467215) B3467215
theorem B2738825 : Blo 1825614 2738825 := bstep (se 2 (by rfl) ⟨1027059, by rfl⟩ : syracuseStep 2738825 = 2054119) B2054119
theorem B6163127 : Blo 1825614 6163127 := bstep (se 1 (by rfl) ⟨4622345, by rfl⟩ : syracuseStep 6163127 = 9244691) B9244691
theorem B2738999 : Blo 1825614 2738999 := bstep (se 1 (by rfl) ⟨2054249, by rfl⟩ : syracuseStep 2738999 = 4108499) B4108499
theorem B2739035 : Blo 1825614 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B16657271 : Blo 1825614 16657271 := bstep (se 1 (by rfl) ⟨12492953, by rfl⟩ : syracuseStep 16657271 = 24985907) B24985907
theorem B2739179 : Blo 1825614 2739179 := bstep (se 1 (by rfl) ⟨2054384, by rfl⟩ : syracuseStep 2739179 = 4108769) B4108769
theorem B9251819 : Blo 1825614 9251819 := bstep (se 1 (by rfl) ⟨6938864, by rfl⟩ : syracuseStep 9251819 = 13877729) B13877729
theorem B3083305 : Blo 1825614 3083305 := bstep (se 2 (by rfl) ⟨1156239, by rfl⟩ : syracuseStep 3083305 = 2312479) B2312479
theorem B5852207 : Blo 1825614 5852207 := bstep (se 1 (by rfl) ⟨4389155, by rfl⟩ : syracuseStep 5852207 = 8778311) B8778311
theorem B2739383 : Blo 1825614 2739383 := bstep (se 1 (by rfl) ⟨2054537, by rfl⟩ : syracuseStep 2739383 = 4109075) B4109075
theorem B3083447 : Blo 1825614 3083447 := bstep (se 1 (by rfl) ⟨2312585, by rfl⟩ : syracuseStep 3083447 = 4625171) B4625171
theorem B2600201 : Blo 1825614 2600201 := bstep (se 2 (by rfl) ⟨975075, by rfl⟩ : syracuseStep 2600201 = 1950151) B1950151
theorem B2469199 : Blo 1825614 2469199 := bstep (se 1 (by rfl) ⟨1851899, by rfl⟩ : syracuseStep 2469199 = 3703799) B3703799
theorem B6933883 : Blo 1825614 6933883 := bstep (se 1 (by rfl) ⟨5200412, by rfl⟩ : syracuseStep 6933883 = 10400825) B10400825
theorem B2739623 : Blo 1825614 2739623 := bstep (se 1 (by rfl) ⟨2054717, by rfl⟩ : syracuseStep 2739623 = 4109435) B4109435
theorem B4107689 : Blo 1825614 4107689 := bstep (se 2 (by rfl) ⟨1540383, by rfl⟩ : syracuseStep 4107689 = 3080767) B3080767
theorem B3124649 : Blo 1825614 3124649 := bstep (se 2 (by rfl) ⟨1171743, by rfl⟩ : syracuseStep 3124649 = 2343487) B2343487
theorem B4935163 : Blo 1825614 4935163 := bstep (se 1 (by rfl) ⟨3701372, by rfl⟩ : syracuseStep 4935163 = 7402745) B7402745
theorem B2739707 : Blo 1825614 2739707 := bstep (se 1 (by rfl) ⟨2054780, by rfl⟩ : syracuseStep 2739707 = 4109561) B4109561
theorem B3083771 : Blo 1825614 3083771 := bstep (se 1 (by rfl) ⟨2312828, by rfl⟩ : syracuseStep 3083771 = 4625657) B4625657
theorem B2739803 : Blo 1825614 2739803 := bstep (se 1 (by rfl) ⟨2054852, by rfl⟩ : syracuseStep 2739803 = 4109705) B4109705
theorem B4935293 : Blo 1825614 4935293 := bstep (se 3 (by rfl) ⟨925367, by rfl⟩ : syracuseStep 4935293 = 1850735) B1850735
theorem B2739887 : Blo 1825614 2739887 := bstep (se 1 (by rfl) ⟨2054915, by rfl⟩ : syracuseStep 2739887 = 4109831) B4109831
theorem B2740007 : Blo 1825614 2740007 := bstep (se 1 (by rfl) ⟨2055005, by rfl⟩ : syracuseStep 2740007 = 4110011) B4110011
theorem B10399549 : Blo 1825614 10399549 := bstep (se 3 (by rfl) ⟨1949915, by rfl⟩ : syracuseStep 10399549 = 3899831) B3899831
theorem B19746665 : Blo 1825614 19746665 := bstep (se 2 (by rfl) ⟨7404999, by rfl⟩ : syracuseStep 19746665 = 14809999) B14809999
theorem B4624249 : Blo 1825614 4624249 := bstep (se 2 (by rfl) ⟨1734093, by rfl⟩ : syracuseStep 4624249 = 3468187) B3468187
theorem B2740091 : Blo 1825614 2740091 := bstep (se 1 (by rfl) ⟨2055068, by rfl⟩ : syracuseStep 2740091 = 4110137) B4110137
theorem B4108175 : Blo 1825614 4108175 := bstep (se 1 (by rfl) ⟨3081131, by rfl⟩ : syracuseStep 4108175 = 6162263) B6162263
theorem B2740511 : Blo 1825614 2740511 := bstep (se 1 (by rfl) ⟨2055383, by rfl⟩ : syracuseStep 2740511 = 4110767) B4110767
theorem B2740535 : Blo 1825614 2740535 := bstep (se 1 (by rfl) ⟨2055401, by rfl⟩ : syracuseStep 2740535 = 4110803) B4110803
theorem B2740607 : Blo 1825614 2740607 := bstep (se 1 (by rfl) ⟨2055455, by rfl⟩ : syracuseStep 2740607 = 4110911) B4110911
theorem B14053769 : Blo 1825614 14053769 := bstep (se 2 (by rfl) ⟨5270163, by rfl⟩ : syracuseStep 14053769 = 10540327) B10540327
theorem B2740679 : Blo 1825614 2740679 := bstep (se 1 (by rfl) ⟨2055509, by rfl⟩ : syracuseStep 2740679 = 4111019) B4111019
theorem B6165071 : Blo 1825614 6165071 := bstep (se 1 (by rfl) ⟨4623803, by rfl⟩ : syracuseStep 6165071 = 9247607) B9247607
theorem B4108895 : Blo 1825614 4108895 := bstep (se 1 (by rfl) ⟨3081671, by rfl⟩ : syracuseStep 4108895 = 6163343) B6163343
theorem B11702879 : Blo 1825614 11702879 := bstep (se 1 (by rfl) ⟨8777159, by rfl⟩ : syracuseStep 11702879 = 17554319) B17554319
theorem B10408571 : Blo 1825614 10408571 := bstep (se 1 (by rfl) ⟨7806428, by rfl⟩ : syracuseStep 10408571 = 15612857) B15612857
theorem B49975957 : Blo 1825614 49975957 := bstep (se 6 (by rfl) ⟨1171311, by rfl⟩ : syracuseStep 49975957 = 2342623) B2342623
theorem B6583031 : Blo 1825614 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B5853977 : Blo 1825614 5853977 := bstep (se 2 (by rfl) ⟨2195241, by rfl⟩ : syracuseStep 5853977 = 4390483) B4390483
theorem B2741033 : Blo 1825614 2741033 := bstep (se 2 (by rfl) ⟨1027887, by rfl⟩ : syracuseStep 2741033 = 2055775) B2055775
theorem B2741039 : Blo 1825614 2741039 := bstep (se 1 (by rfl) ⟨2055779, by rfl⟩ : syracuseStep 2741039 = 4111559) B4111559
theorem B9245501 : Blo 1825614 9245501 := bstep (se 3 (by rfl) ⟨1733531, by rfl⟩ : syracuseStep 9245501 = 3467063) B3467063
theorem B2741159 : Blo 1825614 2741159 := bstep (se 1 (by rfl) ⟨2055869, by rfl⟩ : syracuseStep 2741159 = 4111739) B4111739
theorem B2741243 : Blo 1825614 2741243 := bstep (se 1 (by rfl) ⟨2055932, by rfl⟩ : syracuseStep 2741243 = 4111865) B4111865
theorem B2741303 : Blo 1825614 2741303 := bstep (se 1 (by rfl) ⟨2055977, by rfl⟩ : syracuseStep 2741303 = 4111955) B4111955
theorem B6935615 : Blo 1825614 6935615 := bstep (se 1 (by rfl) ⟨5201711, by rfl⟩ : syracuseStep 6935615 = 10403423) B10403423
theorem B11113553 : Blo 1825614 11113553 := bstep (se 2 (by rfl) ⟨4167582, by rfl⟩ : syracuseStep 11113553 = 8335165) B8335165
theorem B6165611 : Blo 1825614 6165611 := bstep (se 1 (by rfl) ⟨4624208, by rfl⟩ : syracuseStep 6165611 = 9248417) B9248417
theorem B4109723 : Blo 1825614 4109723 := bstep (se 1 (by rfl) ⟨3082292, by rfl⟩ : syracuseStep 4109723 = 6164585) B6164585
theorem B4625819 : Blo 1825614 4625819 := bstep (se 1 (by rfl) ⟨3469364, by rfl⟩ : syracuseStep 4625819 = 6938729) B6938729
theorem B10401281 : Blo 1825614 10401281 := bstep (se 2 (by rfl) ⟨3900480, by rfl⟩ : syracuseStep 10401281 = 7800961) B7800961
theorem B5199673 : Blo 1825614 5199673 := bstep (se 2 (by rfl) ⟨1949877, by rfl⟩ : syracuseStep 5199673 = 3899755) B3899755
theorem B7403327 : Blo 1825614 7403327 := bstep (se 1 (by rfl) ⟨5552495, by rfl⟩ : syracuseStep 7403327 = 11104991) B11104991
theorem B4110299 : Blo 1825614 4110299 := bstep (se 1 (by rfl) ⟨3082724, by rfl⟩ : syracuseStep 4110299 = 6165449) B6165449
theorem B23730241 : Blo 1825614 23730241 := bstep (se 2 (by rfl) ⟨8898840, by rfl⟩ : syracuseStep 23730241 = 17797681) B17797681
theorem B4110479 : Blo 1825614 4110479 := bstep (se 1 (by rfl) ⟨3082859, by rfl⟩ : syracuseStep 4110479 = 6165719) B6165719
theorem B2054299 : Blo 1825614 2054299 := bstep (se 1 (by rfl) ⟨1540724, by rfl⟩ : syracuseStep 2054299 = 3081449) B3081449
theorem B4110497 : Blo 1825614 4110497 := bstep (se 2 (by rfl) ⟨1541436, by rfl⟩ : syracuseStep 4110497 = 3082873) B3082873
theorem B2054335 : Blo 1825614 2054335 := bstep (se 1 (by rfl) ⟨1540751, by rfl⟩ : syracuseStep 2054335 = 3081503) B3081503
theorem B4110569 : Blo 1825614 4110569 := bstep (se 2 (by rfl) ⟨1541463, by rfl⟩ : syracuseStep 4110569 = 3082927) B3082927
theorem B6166907 : Blo 1825614 6166907 := bstep (se 1 (by rfl) ⟨4625180, by rfl⟩ : syracuseStep 6166907 = 9250361) B9250361
theorem B9247283 : Blo 1825614 9247283 := bstep (se 1 (by rfl) ⟨6935462, by rfl⟩ : syracuseStep 9247283 = 13870925) B13870925
theorem B6167177 : Blo 1825614 6167177 := bstep (se 2 (by rfl) ⟨2312691, by rfl⟩ : syracuseStep 6167177 = 4625383) B4625383
theorem B6584989 : Blo 1825614 6584989 := bstep (se 3 (by rfl) ⟨1234685, by rfl⟩ : syracuseStep 6584989 = 2469371) B2469371
theorem B35109551 : Blo 1825614 35109551 := bstep (se 1 (by rfl) ⟨26332163, by rfl⟩ : syracuseStep 35109551 = 52664327) B52664327
theorem B1825627 : Blo 1825614 1825627 := bstep (se 1 (by rfl) ⟨1369220, by rfl⟩ : syracuseStep 1825627 = 2738441) B2738441
theorem B1825695 : Blo 1825614 1825695 := bstep (se 1 (by rfl) ⟨1369271, by rfl⟩ : syracuseStep 1825695 = 2738543) B2738543
theorem B3701729 : Blo 1825614 3701729 := bstep (se 2 (by rfl) ⟨1388148, by rfl⟩ : syracuseStep 3701729 = 2776297) B2776297
theorem B22527017 : Blo 1825614 22527017 := bstep (se 2 (by rfl) ⟨8447631, by rfl⟩ : syracuseStep 22527017 = 16895263) B16895263
theorem B1825839 : Blo 1825614 1825839 := bstep (se 1 (by rfl) ⟨1369379, by rfl⟩ : syracuseStep 1825839 = 2738759) B2738759
theorem B1825863 : Blo 1825614 1825863 := bstep (se 1 (by rfl) ⟨1369397, by rfl⟩ : syracuseStep 1825863 = 2738795) B2738795
theorem B1826015 : Blo 1825614 1826015 := bstep (se 1 (by rfl) ⟨1369511, by rfl⟩ : syracuseStep 1826015 = 2739023) B2739023
theorem B6585695 : Blo 1825614 6585695 := bstep (se 1 (by rfl) ⟨4939271, by rfl⟩ : syracuseStep 6585695 = 9878543) B9878543
theorem B29621609 : Blo 1825614 29621609 := bstep (se 2 (by rfl) ⟨11108103, by rfl⟩ : syracuseStep 29621609 = 22216207) B22216207
theorem B1826279 : Blo 1825614 1826279 := bstep (se 1 (by rfl) ⟨1369709, by rfl⟩ : syracuseStep 1826279 = 2739419) B2739419
theorem B4111847 : Blo 1825614 4111847 := bstep (se 1 (by rfl) ⟨3083885, by rfl⟩ : syracuseStep 4111847 = 6167771) B6167771
theorem B53485067 : Blo 1825614 53485067 := bstep (se 1 (by rfl) ⟨40113800, by rfl⟩ : syracuseStep 53485067 = 80227601) B80227601
theorem B1826395 : Blo 1825614 1826395 := bstep (se 1 (by rfl) ⟨1369796, by rfl⟩ : syracuseStep 1826395 = 2739593) B2739593
theorem B180141893 : Blo 1825614 180141893 := bstep (se 4 (by rfl) ⟨16888302, by rfl⟩ : syracuseStep 180141893 = 33776605) B33776605
theorem B1826631 : Blo 1825614 1826631 := bstep (se 1 (by rfl) ⟨1369973, by rfl⟩ : syracuseStep 1826631 = 2739947) B2739947
theorem B24993629 : Blo 1825614 24993629 := bstep (se 3 (by rfl) ⟨4686305, by rfl⟩ : syracuseStep 24993629 = 9372611) B9372611
theorem B1826783 : Blo 1825614 1826783 := bstep (se 1 (by rfl) ⟨1370087, by rfl⟩ : syracuseStep 1826783 = 2740175) B2740175
theorem B15605885 : Blo 1825614 15605885 := bstep (se 3 (by rfl) ⟨2926103, by rfl⟩ : syracuseStep 15605885 = 5852207) B5852207
theorem B1827007 : Blo 1825614 1827007 := bstep (se 1 (by rfl) ⟨1370255, by rfl⟩ : syracuseStep 1827007 = 2740511) B2740511
theorem B26337473 : Blo 1825614 26337473 := bstep (se 2 (by rfl) ⟨9876552, by rfl⟩ : syracuseStep 26337473 = 19753105) B19753105
theorem B1827023 : Blo 1825614 1827023 := bstep (se 1 (by rfl) ⟨1370267, by rfl⟩ : syracuseStep 1827023 = 2740535) B2740535
theorem B4391147 : Blo 1825614 4391147 := bstep (se 1 (by rfl) ⟨3293360, by rfl⟩ : syracuseStep 4391147 = 6586721) B6586721
theorem B1827071 : Blo 1825614 1827071 := bstep (se 1 (by rfl) ⟨1370303, by rfl⟩ : syracuseStep 1827071 = 2740607) B2740607
theorem B1827119 : Blo 1825614 1827119 := bstep (se 1 (by rfl) ⟨1370339, by rfl⟩ : syracuseStep 1827119 = 2740679) B2740679
theorem B6939017 : Blo 1825614 6939017 := bstep (se 2 (by rfl) ⟨2602131, by rfl⟩ : syracuseStep 6939017 = 5204263) B5204263
theorem B6939047 : Blo 1825614 6939047 := bstep (se 1 (by rfl) ⟨5204285, by rfl⟩ : syracuseStep 6939047 = 10408571) B10408571
theorem B11862443 : Blo 1825614 11862443 := bstep (se 1 (by rfl) ⟨8896832, by rfl⟩ : syracuseStep 11862443 = 17793665) B17793665
theorem B133325261 : Blo 1825614 133325261 := bstep (se 3 (by rfl) ⟨24998486, by rfl⟩ : syracuseStep 133325261 = 49996973) B49996973
theorem B1827355 : Blo 1825614 1827355 := bstep (se 1 (by rfl) ⟨1370516, by rfl⟩ : syracuseStep 1827355 = 2741033) B2741033
theorem B1827359 : Blo 1825614 1827359 := bstep (se 1 (by rfl) ⟨1370519, by rfl⟩ : syracuseStep 1827359 = 2741039) B2741039
theorem B1827439 : Blo 1825614 1827439 := bstep (se 1 (by rfl) ⟨1370579, by rfl⟩ : syracuseStep 1827439 = 2741159) B2741159
theorem B1827495 : Blo 1825614 1827495 := bstep (se 1 (by rfl) ⟨1370621, by rfl⟩ : syracuseStep 1827495 = 2741243) B2741243
theorem B1827535 : Blo 1825614 1827535 := bstep (se 1 (by rfl) ⟨1370651, by rfl⟩ : syracuseStep 1827535 = 2741303) B2741303
theorem B66634609 : Blo 1825614 66634609 := bstep (se 2 (by rfl) ⟨24987978, by rfl⟩ : syracuseStep 66634609 = 49975957) B49975957
theorem B5850107 : Blo 1825614 5850107 := bstep (se 1 (by rfl) ⟨4387580, by rfl⟩ : syracuseStep 5850107 = 8775161) B8775161
theorem B10405199 : Blo 1825614 10405199 := bstep (se 1 (by rfl) ⟨7803899, by rfl⟩ : syracuseStep 10405199 = 15607799) B15607799
theorem B4064737 : Blo 1825614 4064737 := bstep (se 2 (by rfl) ⟨1524276, by rfl⟩ : syracuseStep 4064737 = 3048553) B3048553
theorem B4621819 : Blo 1825614 4621819 := bstep (se 1 (by rfl) ⟨3466364, by rfl⟩ : syracuseStep 4621819 = 6932729) B6932729
theorem B23406367 : Blo 1825614 23406367 := bstep (se 1 (by rfl) ⟨17554775, by rfl⟩ : syracuseStep 23406367 = 35109551) B35109551
theorem B2467819 : Blo 1825614 2467819 := bstep (se 1 (by rfl) ⟨1850864, by rfl⟩ : syracuseStep 2467819 = 3701729) B3701729
theorem B6580217 : Blo 1825614 6580217 := bstep (se 2 (by rfl) ⟨2467581, by rfl⟩ : syracuseStep 6580217 = 4935163) B4935163
theorem B15018011 : Blo 1825614 15018011 := bstep (se 1 (by rfl) ⟨11263508, by rfl⟩ : syracuseStep 15018011 = 22527017) B22527017
theorem B3901601 : Blo 1825614 3901601 := bstep (se 2 (by rfl) ⟨1463100, by rfl⟩ : syracuseStep 3901601 = 2926201) B2926201
theorem B2738459 : Blo 1825614 2738459 := bstep (se 1 (by rfl) ⟨2053844, by rfl⟩ : syracuseStep 2738459 = 4107689) B4107689
theorem B2083099 : Blo 1825614 2083099 := bstep (se 1 (by rfl) ⟨1562324, by rfl⟩ : syracuseStep 2083099 = 3124649) B3124649
theorem B6932897 : Blo 1825614 6932897 := bstep (se 2 (by rfl) ⟨2599836, by rfl⟩ : syracuseStep 6932897 = 5199673) B5199673
theorem B2738783 : Blo 1825614 2738783 := bstep (se 1 (by rfl) ⟨2054087, by rfl⟩ : syracuseStep 2738783 = 4108175) B4108175
theorem B31640321 : Blo 1825614 31640321 := bstep (se 2 (by rfl) ⟨11865120, by rfl⟩ : syracuseStep 31640321 = 23730241) B23730241
theorem B2739065 : Blo 1825614 2739065 := bstep (se 2 (by rfl) ⟨1027149, by rfl⟩ : syracuseStep 2739065 = 2054299) B2054299
theorem B2739113 : Blo 1825614 2739113 := bstep (se 2 (by rfl) ⟨1027167, by rfl⟩ : syracuseStep 2739113 = 2054335) B2054335
theorem B3083177 : Blo 1825614 3083177 := bstep (se 2 (by rfl) ⟨1156191, by rfl⟩ : syracuseStep 3083177 = 2312383) B2312383
theorem B2739263 : Blo 1825614 2739263 := bstep (se 1 (by rfl) ⟨2054447, by rfl⟩ : syracuseStep 2739263 = 4108895) B4108895
theorem B7801919 : Blo 1825614 7801919 := bstep (se 1 (by rfl) ⟨5851439, by rfl⟩ : syracuseStep 7801919 = 11702879) B11702879
theorem B15600761 : Blo 1825614 15600761 := bstep (se 2 (by rfl) ⟨5850285, by rfl⟩ : syracuseStep 15600761 = 11700571) B11700571
theorem B13864121 : Blo 1825614 13864121 := bstep (se 2 (by rfl) ⟨5199045, by rfl⟩ : syracuseStep 13864121 = 10398091) B10398091
theorem B3902651 : Blo 1825614 3902651 := bstep (se 1 (by rfl) ⟨2926988, by rfl⟩ : syracuseStep 3902651 = 5853977) B5853977
theorem B6163667 : Blo 1825614 6163667 := bstep (se 1 (by rfl) ⟨4622750, by rfl⟩ : syracuseStep 6163667 = 9245501) B9245501
theorem B8776927 : Blo 1825614 8776927 := bstep (se 1 (by rfl) ⟨6582695, by rfl⟩ : syracuseStep 8776927 = 13165391) B13165391
theorem B6933869 : Blo 1825614 6933869 := bstep (se 3 (by rfl) ⟨1300100, by rfl⟩ : syracuseStep 6933869 = 2600201) B2600201
theorem B4623743 : Blo 1825614 4623743 := bstep (se 1 (by rfl) ⟨3467807, by rfl⟩ : syracuseStep 4623743 = 6935615) B6935615
theorem B7409035 : Blo 1825614 7409035 := bstep (se 1 (by rfl) ⟨5556776, by rfl⟩ : syracuseStep 7409035 = 11113553) B11113553
theorem B4107743 : Blo 1825614 4107743 := bstep (se 1 (by rfl) ⟨3080807, by rfl⟩ : syracuseStep 4107743 = 6161615) B6161615
theorem B6163937 : Blo 1825614 6163937 := bstep (se 2 (by rfl) ⟨2311476, by rfl⟩ : syracuseStep 6163937 = 4622953) B4622953
theorem B6336001 : Blo 1825614 6336001 := bstep (se 2 (by rfl) ⟨2376000, by rfl⟩ : syracuseStep 6336001 = 4752001) B4752001
theorem B2739815 : Blo 1825614 2739815 := bstep (se 1 (by rfl) ⟨2054861, by rfl⟩ : syracuseStep 2739815 = 4109723) B4109723
theorem B3083879 : Blo 1825614 3083879 := bstep (se 1 (by rfl) ⟨2312909, by rfl⟩ : syracuseStep 3083879 = 4625819) B4625819
theorem B15609509 : Blo 1825614 15609509 := bstep (se 4 (by rfl) ⟨1463391, by rfl⟩ : syracuseStep 15609509 = 2926783) B2926783
theorem B6934187 : Blo 1825614 6934187 := bstep (se 1 (by rfl) ⟨5200640, by rfl⟩ : syracuseStep 6934187 = 10401281) B10401281
theorem B4107959 : Blo 1825614 4107959 := bstep (se 1 (by rfl) ⟨3080969, by rfl⟩ : syracuseStep 4107959 = 6161939) B6161939
theorem B18755435 : Blo 1825614 18755435 := bstep (se 1 (by rfl) ⟨14066576, by rfl⟩ : syracuseStep 18755435 = 28133153) B28133153
theorem B4935551 : Blo 1825614 4935551 := bstep (se 1 (by rfl) ⟨3701663, by rfl⟩ : syracuseStep 4935551 = 7403327) B7403327
theorem B6582235 : Blo 1825614 6582235 := bstep (se 1 (by rfl) ⟨4936676, by rfl⟩ : syracuseStep 6582235 = 9873353) B9873353
theorem B2740199 : Blo 1825614 2740199 := bstep (se 1 (by rfl) ⟨2055149, by rfl⟩ : syracuseStep 2740199 = 4110299) B4110299
theorem B142626845 : Blo 1825614 142626845 := bstep (se 3 (by rfl) ⟨26742533, by rfl⟩ : syracuseStep 142626845 = 53485067) B53485067
theorem B10399823 : Blo 1825614 10399823 := bstep (se 1 (by rfl) ⟨7799867, by rfl⟩ : syracuseStep 10399823 = 15599735) B15599735
theorem B2740319 : Blo 1825614 2740319 := bstep (se 1 (by rfl) ⟨2055239, by rfl⟩ : syracuseStep 2740319 = 4110479) B4110479
theorem B2740331 : Blo 1825614 2740331 := bstep (se 1 (by rfl) ⟨2055248, by rfl⟩ : syracuseStep 2740331 = 4110497) B4110497
theorem B2740379 : Blo 1825614 2740379 := bstep (se 1 (by rfl) ⟨2055284, by rfl⟩ : syracuseStep 2740379 = 4110569) B4110569
theorem B6164855 : Blo 1825614 6164855 := bstep (se 1 (by rfl) ⟨4623641, by rfl⟩ : syracuseStep 6164855 = 9247283) B9247283
theorem B4108751 : Blo 1825614 4108751 := bstep (se 1 (by rfl) ⟨3081563, by rfl⟩ : syracuseStep 4108751 = 6163127) B6163127
theorem B9245177 : Blo 1825614 9245177 := bstep (se 2 (by rfl) ⟨3466941, by rfl⟩ : syracuseStep 9245177 = 6933883) B6933883
theorem B11104847 : Blo 1825614 11104847 := bstep (se 1 (by rfl) ⟨8328635, by rfl⟩ : syracuseStep 11104847 = 16657271) B16657271
theorem B19747739 : Blo 1825614 19747739 := bstep (se 1 (by rfl) ⟨14810804, by rfl⟩ : syracuseStep 19747739 = 29621609) B29621609
theorem B2741231 : Blo 1825614 2741231 := bstep (se 1 (by rfl) ⟨2055923, by rfl⟩ : syracuseStep 2741231 = 4111847) B4111847
theorem B13866065 : Blo 1825614 13866065 := bstep (se 2 (by rfl) ⟨5199774, by rfl⟩ : syracuseStep 13866065 = 10399549) B10399549
theorem B3290195 : Blo 1825614 3290195 := bstep (se 1 (by rfl) ⟨2467646, by rfl⟩ : syracuseStep 3290195 = 4935293) B4935293
theorem B8336465 : Blo 1825614 8336465 := bstep (se 2 (by rfl) ⟨3126174, by rfl⟩ : syracuseStep 8336465 = 6252349) B6252349
theorem B4109417 : Blo 1825614 4109417 := bstep (se 2 (by rfl) ⟨1541031, by rfl⟩ : syracuseStep 4109417 = 3082063) B3082063
theorem B6165665 : Blo 1825614 6165665 := bstep (se 2 (by rfl) ⟨2312124, by rfl⟩ : syracuseStep 6165665 = 4624249) B4624249
theorem B6165935 : Blo 1825614 6165935 := bstep (se 1 (by rfl) ⟨4624451, by rfl⟩ : syracuseStep 6165935 = 9248903) B9248903
theorem B39507425 : Blo 1825614 39507425 := bstep (se 2 (by rfl) ⟨14815284, by rfl⟩ : syracuseStep 39507425 = 29630569) B29630569
theorem B9369179 : Blo 1825614 9369179 := bstep (se 1 (by rfl) ⟨7026884, by rfl⟩ : syracuseStep 9369179 = 14053769) B14053769
theorem B23139959 : Blo 1825614 23139959 := bstep (se 1 (by rfl) ⟨17354969, by rfl⟩ : syracuseStep 23139959 = 34709939) B34709939
theorem B4110047 : Blo 1825614 4110047 := bstep (se 1 (by rfl) ⟨3082535, by rfl⟩ : syracuseStep 4110047 = 6165071) B6165071
theorem B6936299 : Blo 1825614 6936299 := bstep (se 1 (by rfl) ⟨5202224, by rfl⟩ : syracuseStep 6936299 = 10404449) B10404449
theorem B6166259 : Blo 1825614 6166259 := bstep (se 1 (by rfl) ⟨4624694, by rfl⟩ : syracuseStep 6166259 = 9249389) B9249389
theorem B4388687 : Blo 1825614 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B5199707 : Blo 1825614 5199707 := bstep (se 1 (by rfl) ⟨3899780, by rfl⟩ : syracuseStep 5199707 = 7799561) B7799561
theorem B2054011 : Blo 1825614 2054011 := bstep (se 1 (by rfl) ⟨1540508, by rfl⟩ : syracuseStep 2054011 = 3081017) B3081017
theorem B2054047 : Blo 1825614 2054047 := bstep (se 1 (by rfl) ⟨1540535, by rfl⟩ : syracuseStep 2054047 = 3081071) B3081071
theorem B4110407 : Blo 1825614 4110407 := bstep (se 1 (by rfl) ⟨3082805, by rfl⟩ : syracuseStep 4110407 = 6165611) B6165611
theorem B8779985 : Blo 1825614 8779985 := bstep (se 2 (by rfl) ⟨3292494, by rfl⟩ : syracuseStep 8779985 = 6584989) B6584989
theorem B6167015 : Blo 1825614 6167015 := bstep (se 1 (by rfl) ⟨4625261, by rfl⟩ : syracuseStep 6167015 = 9250523) B9250523
theorem B23419489 : Blo 1825614 23419489 := bstep (se 2 (by rfl) ⟨8782308, by rfl⟩ : syracuseStep 23419489 = 17564617) B17564617
theorem B4111073 : Blo 1825614 4111073 := bstep (se 2 (by rfl) ⟨1541652, by rfl⟩ : syracuseStep 4111073 = 3083305) B3083305
theorem B2054983 : Blo 1825614 2054983 := bstep (se 1 (by rfl) ⟨1541237, by rfl⟩ : syracuseStep 2054983 = 3082475) B3082475
theorem B1825647 : Blo 1825614 1825647 := bstep (se 1 (by rfl) ⟨1369235, by rfl⟩ : syracuseStep 1825647 = 2738471) B2738471
theorem B1825703 : Blo 1825614 1825703 := bstep (se 1 (by rfl) ⟨1369277, by rfl⟩ : syracuseStep 1825703 = 2738555) B2738555
theorem B4111271 : Blo 1825614 4111271 := bstep (se 1 (by rfl) ⟨3083453, by rfl⟩ : syracuseStep 4111271 = 6166907) B6166907
theorem B1825883 : Blo 1825614 1825883 := bstep (se 1 (by rfl) ⟨1369412, by rfl⟩ : syracuseStep 1825883 = 2738825) B2738825
theorem B4111451 : Blo 1825614 4111451 := bstep (se 1 (by rfl) ⟨3083588, by rfl⟩ : syracuseStep 4111451 = 6167177) B6167177
theorem B3292265 : Blo 1825614 3292265 := bstep (se 2 (by rfl) ⟨1234599, by rfl⟩ : syracuseStep 3292265 = 2469199) B2469199
theorem B1825999 : Blo 1825614 1825999 := bstep (se 1 (by rfl) ⟨1369499, by rfl⟩ : syracuseStep 1825999 = 2738999) B2738999
theorem B1826023 : Blo 1825614 1826023 := bstep (se 1 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 1826023 = 2739035) B2739035
theorem B1826119 : Blo 1825614 1826119 := bstep (se 1 (by rfl) ⟨1369589, by rfl⟩ : syracuseStep 1826119 = 2739179) B2739179
theorem B6167879 : Blo 1825614 6167879 := bstep (se 1 (by rfl) ⟨4625909, by rfl⟩ : syracuseStep 6167879 = 9251819) B9251819
theorem B1826255 : Blo 1825614 1826255 := bstep (se 1 (by rfl) ⟨1369691, by rfl⟩ : syracuseStep 1826255 = 2739383) B2739383
theorem B2055631 : Blo 1825614 2055631 := bstep (se 1 (by rfl) ⟨1541723, by rfl⟩ : syracuseStep 2055631 = 3083447) B3083447
theorem B4390463 : Blo 1825614 4390463 := bstep (se 1 (by rfl) ⟨3292847, by rfl⟩ : syracuseStep 4390463 = 6585695) B6585695
theorem B1826415 : Blo 1825614 1826415 := bstep (se 1 (by rfl) ⟨1369811, by rfl⟩ : syracuseStep 1826415 = 2739623) B2739623
theorem B1826471 : Blo 1825614 1826471 := bstep (se 1 (by rfl) ⟨1369853, by rfl⟩ : syracuseStep 1826471 = 2739707) B2739707
theorem B2055847 : Blo 1825614 2055847 := bstep (se 1 (by rfl) ⟨1541885, by rfl⟩ : syracuseStep 2055847 = 3083771) B3083771
theorem B1826535 : Blo 1825614 1826535 := bstep (se 1 (by rfl) ⟨1369901, by rfl⟩ : syracuseStep 1826535 = 2739803) B2739803
theorem B1826591 : Blo 1825614 1826591 := bstep (se 1 (by rfl) ⟨1369943, by rfl⟩ : syracuseStep 1826591 = 2739887) B2739887
theorem B1826671 : Blo 1825614 1826671 := bstep (se 1 (by rfl) ⟨1370003, by rfl⟩ : syracuseStep 1826671 = 2740007) B2740007
theorem B120094595 : Blo 1825614 120094595 := bstep (se 1 (by rfl) ⟨90070946, by rfl⟩ : syracuseStep 120094595 = 180141893) B180141893
theorem B16662419 : Blo 1825614 16662419 := bstep (se 1 (by rfl) ⟨12496814, by rfl⟩ : syracuseStep 16662419 = 24993629) B24993629
theorem B13164443 : Blo 1825614 13164443 := bstep (se 1 (by rfl) ⟨9873332, by rfl⟩ : syracuseStep 13164443 = 19746665) B19746665
theorem B1826727 : Blo 1825614 1826727 := bstep (se 1 (by rfl) ⟨1370045, by rfl⟩ : syracuseStep 1826727 = 2740091) B2740091
theorem B33792005 : Blo 1825614 33792005 := bstep (se 4 (by rfl) ⟨3168000, by rfl⟩ : syracuseStep 33792005 = 6336001) B6336001
theorem B1826879 : Blo 1825614 1826879 := bstep (se 1 (by rfl) ⟨1370159, by rfl⟩ : syracuseStep 1826879 = 2740319) B2740319
theorem B1826887 : Blo 1825614 1826887 := bstep (se 1 (by rfl) ⟨1370165, by rfl⟩ : syracuseStep 1826887 = 2740331) B2740331
theorem B380338253 : Blo 1825614 380338253 := bstep (se 3 (by rfl) ⟨71313422, by rfl⟩ : syracuseStep 380338253 = 142626845) B142626845
theorem B10403923 : Blo 1825614 10403923 := bstep (se 1 (by rfl) ⟨7802942, by rfl⟩ : syracuseStep 10403923 = 15605885) B15605885
theorem B1826919 : Blo 1825614 1826919 := bstep (se 1 (by rfl) ⟨1370189, by rfl⟩ : syracuseStep 1826919 = 2740379) B2740379
theorem B88883507 : Blo 1825614 88883507 := bstep (se 1 (by rfl) ⟨66662630, by rfl⟩ : syracuseStep 88883507 = 133325261) B133325261
theorem B2777465 : Blo 1825614 2777465 := bstep (se 2 (by rfl) ⟨1041549, by rfl⟩ : syracuseStep 2777465 = 2083099) B2083099
theorem B1827487 : Blo 1825614 1827487 := bstep (se 1 (by rfl) ⟨1370615, by rfl⟩ : syracuseStep 1827487 = 2741231) B2741231
theorem B3900071 : Blo 1825614 3900071 := bstep (se 1 (by rfl) ⟨2925053, by rfl⟩ : syracuseStep 3900071 = 5850107) B5850107
theorem B26338283 : Blo 1825614 26338283 := bstep (se 1 (by rfl) ⟨19753712, by rfl⟩ : syracuseStep 26338283 = 39507425) B39507425
theorem B2925791 : Blo 1825614 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B3466471 : Blo 1825614 3466471 := bstep (se 1 (by rfl) ⟨2599853, by rfl⟩ : syracuseStep 3466471 = 5199707) B5199707
theorem B10012007 : Blo 1825614 10012007 := bstep (se 1 (by rfl) ⟨7509005, by rfl⟩ : syracuseStep 10012007 = 15018011) B15018011
theorem B11707901 : Blo 1825614 11707901 := bstep (se 3 (by rfl) ⟨2195231, by rfl⟩ : syracuseStep 11707901 = 4390463) B4390463
theorem B4621931 : Blo 1825614 4621931 := bstep (se 1 (by rfl) ⟨3466448, by rfl⟩ : syracuseStep 4621931 = 6932897) B6932897
theorem B6162425 : Blo 1825614 6162425 := bstep (se 2 (by rfl) ⟨2310909, by rfl⟩ : syracuseStep 6162425 = 4621819) B4621819
theorem B9242747 : Blo 1825614 9242747 := bstep (se 1 (by rfl) ⟨6932060, by rfl⟩ : syracuseStep 9242747 = 13864121) B13864121
theorem B4622579 : Blo 1825614 4622579 := bstep (se 1 (by rfl) ⟨3466934, by rfl⟩ : syracuseStep 4622579 = 6933869) B6933869
theorem B3082495 : Blo 1825614 3082495 := bstep (se 1 (by rfl) ⟨2311871, by rfl⟩ : syracuseStep 3082495 = 4623743) B4623743
theorem B50014493 : Blo 1825614 50014493 := bstep (se 3 (by rfl) ⟨9377717, by rfl⟩ : syracuseStep 50014493 = 18755435) B18755435
theorem B2738495 : Blo 1825614 2738495 := bstep (se 1 (by rfl) ⟨2053871, by rfl⟩ : syracuseStep 2738495 = 4107743) B4107743
theorem B52660637 : Blo 1825614 52660637 := bstep (se 3 (by rfl) ⟨9873869, by rfl⟩ : syracuseStep 52660637 = 19747739) B19747739
theorem B10406339 : Blo 1825614 10406339 := bstep (se 1 (by rfl) ⟨7804754, by rfl⟩ : syracuseStep 10406339 = 15609509) B15609509
theorem B4622791 : Blo 1825614 4622791 := bstep (se 1 (by rfl) ⟨3467093, by rfl⟩ : syracuseStep 4622791 = 6934187) B6934187
theorem B2738639 : Blo 1825614 2738639 := bstep (se 1 (by rfl) ⟨2053979, by rfl⟩ : syracuseStep 2738639 = 4107959) B4107959
theorem B2738681 : Blo 1825614 2738681 := bstep (se 2 (by rfl) ⟨1027005, by rfl⟩ : syracuseStep 2738681 = 2054011) B2054011
theorem B2738729 : Blo 1825614 2738729 := bstep (se 2 (by rfl) ⟨1027023, by rfl⟩ : syracuseStep 2738729 = 2054047) B2054047
theorem B80063063 : Blo 1825614 80063063 := bstep (se 1 (by rfl) ⟨60047297, by rfl⟩ : syracuseStep 80063063 = 120094595) B120094595
theorem B8776295 : Blo 1825614 8776295 := bstep (se 1 (by rfl) ⟨6582221, by rfl⟩ : syracuseStep 8776295 = 13164443) B13164443
theorem B8776313 : Blo 1825614 8776313 := bstep (se 2 (by rfl) ⟨3291117, by rfl⟩ : syracuseStep 8776313 = 6582235) B6582235
theorem B6933215 : Blo 1825614 6933215 := bstep (se 1 (by rfl) ⟨5199911, by rfl⟩ : syracuseStep 6933215 = 10399823) B10399823
theorem B17558315 : Blo 1825614 17558315 := bstep (se 1 (by rfl) ⟨13168736, by rfl⟩ : syracuseStep 17558315 = 26337473) B26337473
theorem B2927431 : Blo 1825614 2927431 := bstep (se 1 (by rfl) ⟨2195573, by rfl⟩ : syracuseStep 2927431 = 4391147) B4391147
theorem B7908295 : Blo 1825614 7908295 := bstep (se 1 (by rfl) ⟨5931221, by rfl⟩ : syracuseStep 7908295 = 11862443) B11862443
theorem B2739167 : Blo 1825614 2739167 := bstep (se 1 (by rfl) ⟨2054375, by rfl⟩ : syracuseStep 2739167 = 4108751) B4108751
theorem B6163451 : Blo 1825614 6163451 := bstep (se 1 (by rfl) ⟨4622588, by rfl⟩ : syracuseStep 6163451 = 9245177) B9245177
theorem B9244043 : Blo 1825614 9244043 := bstep (se 1 (by rfl) ⟨6933032, by rfl⟩ : syracuseStep 9244043 = 13866065) B13866065
theorem B5557643 : Blo 1825614 5557643 := bstep (se 1 (by rfl) ⟨4168232, by rfl⟩ : syracuseStep 5557643 = 8336465) B8336465
theorem B2739611 : Blo 1825614 2739611 := bstep (se 1 (by rfl) ⟨2054708, by rfl⟩ : syracuseStep 2739611 = 4109417) B4109417
theorem B6246119 : Blo 1825614 6246119 := bstep (se 1 (by rfl) ⟨4684589, by rfl⟩ : syracuseStep 6246119 = 9369179) B9369179
theorem B2739977 : Blo 1825614 2739977 := bstep (se 2 (by rfl) ⟨1027491, by rfl⟩ : syracuseStep 2739977 = 2054983) B2054983
theorem B2740031 : Blo 1825614 2740031 := bstep (se 1 (by rfl) ⟨2055023, by rfl⟩ : syracuseStep 2740031 = 4110047) B4110047
theorem B88846145 : Blo 1825614 88846145 := bstep (se 2 (by rfl) ⟨33317304, by rfl⟩ : syracuseStep 88846145 = 66634609) B66634609
theorem B4624199 : Blo 1825614 4624199 := bstep (se 1 (by rfl) ⟨3468149, by rfl⟩ : syracuseStep 4624199 = 6936299) B6936299
theorem B4386811 : Blo 1825614 4386811 := bstep (se 1 (by rfl) ⟨3290108, by rfl⟩ : syracuseStep 4386811 = 6580217) B6580217
theorem B2740271 : Blo 1825614 2740271 := bstep (se 1 (by rfl) ⟨2055203, by rfl⟩ : syracuseStep 2740271 = 4110407) B4110407
theorem B2601067 : Blo 1825614 2601067 := bstep (se 1 (by rfl) ⟨1950800, by rfl⟩ : syracuseStep 2601067 = 3901601) B3901601
theorem B5853323 : Blo 1825614 5853323 := bstep (se 1 (by rfl) ⟨4389992, by rfl⟩ : syracuseStep 5853323 = 8779985) B8779985
theorem B11702569 : Blo 1825614 11702569 := bstep (se 2 (by rfl) ⟨4388463, by rfl⟩ : syracuseStep 11702569 = 8776927) B8776927
theorem B61706557 : Blo 1825614 61706557 := bstep (se 3 (by rfl) ⟨11569979, by rfl⟩ : syracuseStep 61706557 = 23139959) B23139959
theorem B2740715 : Blo 1825614 2740715 := bstep (se 1 (by rfl) ⟨2055536, by rfl⟩ : syracuseStep 2740715 = 4111073) B4111073
theorem B2740841 : Blo 1825614 2740841 := bstep (se 2 (by rfl) ⟨1027815, by rfl⟩ : syracuseStep 2740841 = 2055631) B2055631
theorem B2740847 : Blo 1825614 2740847 := bstep (se 1 (by rfl) ⟨2055635, by rfl⟩ : syracuseStep 2740847 = 4111271) B4111271
theorem B5419649 : Blo 1825614 5419649 := bstep (se 2 (by rfl) ⟨2032368, by rfl⟩ : syracuseStep 5419649 = 4064737) B4064737
theorem B39514853 : Blo 1825614 39514853 := bstep (se 4 (by rfl) ⟨3704517, by rfl⟩ : syracuseStep 39514853 = 7409035) B7409035
theorem B2740967 : Blo 1825614 2740967 := bstep (se 1 (by rfl) ⟨2055725, by rfl⟩ : syracuseStep 2740967 = 4111451) B4111451
theorem B10400507 : Blo 1825614 10400507 := bstep (se 1 (by rfl) ⟨7800380, by rfl⟩ : syracuseStep 10400507 = 15600761) B15600761
theorem B2601767 : Blo 1825614 2601767 := bstep (se 1 (by rfl) ⟨1951325, by rfl⟩ : syracuseStep 2601767 = 3902651) B3902651
theorem B4109111 : Blo 1825614 4109111 := bstep (se 1 (by rfl) ⟨3081833, by rfl⟩ : syracuseStep 4109111 = 6163667) B6163667
theorem B2741129 : Blo 1825614 2741129 := bstep (se 2 (by rfl) ⟨1027923, by rfl⟩ : syracuseStep 2741129 = 2055847) B2055847
theorem B4109291 : Blo 1825614 4109291 := bstep (se 1 (by rfl) ⟨3081968, by rfl⟩ : syracuseStep 4109291 = 6163937) B6163937
theorem B13161469 : Blo 1825614 13161469 := bstep (se 3 (by rfl) ⟨2467775, by rfl⟩ : syracuseStep 13161469 = 4935551) B4935551
theorem B31208489 : Blo 1825614 31208489 := bstep (se 2 (by rfl) ⟨11703183, by rfl⟩ : syracuseStep 31208489 = 23406367) B23406367
theorem B3290425 : Blo 1825614 3290425 := bstep (se 2 (by rfl) ⟨1233909, by rfl⟩ : syracuseStep 3290425 = 2467819) B2467819
theorem B4109903 : Blo 1825614 4109903 := bstep (se 1 (by rfl) ⟨3082427, by rfl⟩ : syracuseStep 4109903 = 6164855) B6164855
theorem B4626011 : Blo 1825614 4626011 := bstep (se 1 (by rfl) ⟨3469508, by rfl⟩ : syracuseStep 4626011 = 6939017) B6939017
theorem B4626031 : Blo 1825614 4626031 := bstep (se 1 (by rfl) ⟨3469523, by rfl⟩ : syracuseStep 4626031 = 6939047) B6939047
theorem B7403231 : Blo 1825614 7403231 := bstep (se 1 (by rfl) ⟨5552423, by rfl⟩ : syracuseStep 7403231 = 11104847) B11104847
theorem B2193463 : Blo 1825614 2193463 := bstep (se 1 (by rfl) ⟨1645097, by rfl⟩ : syracuseStep 2193463 = 3290195) B3290195
theorem B4110443 : Blo 1825614 4110443 := bstep (se 1 (by rfl) ⟨3082832, by rfl⟩ : syracuseStep 4110443 = 6165665) B6165665
theorem B31225985 : Blo 1825614 31225985 := bstep (se 2 (by rfl) ⟨11709744, by rfl⟩ : syracuseStep 31225985 = 23419489) B23419489
theorem B6936799 : Blo 1825614 6936799 := bstep (se 1 (by rfl) ⟨5202599, by rfl⟩ : syracuseStep 6936799 = 10405199) B10405199
theorem B4110623 : Blo 1825614 4110623 := bstep (se 1 (by rfl) ⟨3082967, by rfl⟩ : syracuseStep 4110623 = 6165935) B6165935
theorem B4110839 : Blo 1825614 4110839 := bstep (se 1 (by rfl) ⟨3083129, by rfl⟩ : syracuseStep 4110839 = 6166259) B6166259
theorem B1825639 : Blo 1825614 1825639 := bstep (se 1 (by rfl) ⟨1369229, by rfl⟩ : syracuseStep 1825639 = 2738459) B2738459
theorem B4111343 : Blo 1825614 4111343 := bstep (se 1 (by rfl) ⟨3083507, by rfl⟩ : syracuseStep 4111343 = 6167015) B6167015
theorem B1825855 : Blo 1825614 1825855 := bstep (se 1 (by rfl) ⟨1369391, by rfl⟩ : syracuseStep 1825855 = 2738783) B2738783
theorem B21093547 : Blo 1825614 21093547 := bstep (se 1 (by rfl) ⟨15820160, by rfl⟩ : syracuseStep 21093547 = 31640321) B31640321
theorem B1826043 : Blo 1825614 1826043 := bstep (se 1 (by rfl) ⟨1369532, by rfl⟩ : syracuseStep 1826043 = 2739065) B2739065
theorem B1826075 : Blo 1825614 1826075 := bstep (se 1 (by rfl) ⟨1369556, by rfl⟩ : syracuseStep 1826075 = 2739113) B2739113
theorem B2055451 : Blo 1825614 2055451 := bstep (se 1 (by rfl) ⟨1541588, by rfl⟩ : syracuseStep 2055451 = 3083177) B3083177
theorem B1826175 : Blo 1825614 1826175 := bstep (se 1 (by rfl) ⟨1369631, by rfl⟩ : syracuseStep 1826175 = 2739263) B2739263
theorem B5201279 : Blo 1825614 5201279 := bstep (se 1 (by rfl) ⟨3900959, by rfl⟩ : syracuseStep 5201279 = 7801919) B7801919
theorem B2194843 : Blo 1825614 2194843 := bstep (se 1 (by rfl) ⟨1646132, by rfl⟩ : syracuseStep 2194843 = 3292265) B3292265
theorem B4111919 : Blo 1825614 4111919 := bstep (se 1 (by rfl) ⟨3083939, by rfl⟩ : syracuseStep 4111919 = 6167879) B6167879
theorem B1826543 : Blo 1825614 1826543 := bstep (se 1 (by rfl) ⟨1369907, by rfl⟩ : syracuseStep 1826543 = 2739815) B2739815
theorem B2055919 : Blo 1825614 2055919 := bstep (se 1 (by rfl) ⟨1541939, by rfl⟩ : syracuseStep 2055919 = 3083879) B3083879
theorem B11108279 : Blo 1825614 11108279 := bstep (se 1 (by rfl) ⟨8331209, by rfl⟩ : syracuseStep 11108279 = 16662419) B16662419
theorem B1826799 : Blo 1825614 1826799 := bstep (se 1 (by rfl) ⟨1370099, by rfl⟩ : syracuseStep 1826799 = 2740199) B2740199
theorem B22528003 : Blo 1825614 22528003 := bstep (se 1 (by rfl) ⟨16896002, by rfl⟩ : syracuseStep 22528003 = 33792005) B33792005
theorem B1826847 : Blo 1825614 1826847 := bstep (se 1 (by rfl) ⟨1370135, by rfl⟩ : syracuseStep 1826847 = 2740271) B2740271
theorem B253558835 : Blo 1825614 253558835 := bstep (se 1 (by rfl) ⟨190169126, by rfl⟩ : syracuseStep 253558835 = 380338253) B380338253
theorem B1851643 : Blo 1825614 1851643 := bstep (se 1 (by rfl) ⟨1388732, by rfl⟩ : syracuseStep 1851643 = 2777465) B2777465
theorem B11698469 : Blo 1825614 11698469 := bstep (se 4 (by rfl) ⟨1096731, by rfl⟩ : syracuseStep 11698469 = 2193463) B2193463
theorem B9249065 : Blo 1825614 9249065 := bstep (se 2 (by rfl) ⟨3468399, by rfl⟩ : syracuseStep 9249065 = 6936799) B6936799
theorem B1827143 : Blo 1825614 1827143 := bstep (se 1 (by rfl) ⟨1370357, by rfl⟩ : syracuseStep 1827143 = 2740715) B2740715
theorem B1827227 : Blo 1825614 1827227 := bstep (se 1 (by rfl) ⟨1370420, by rfl⟩ : syracuseStep 1827227 = 2740841) B2740841
theorem B1827231 : Blo 1825614 1827231 := bstep (se 1 (by rfl) ⟨1370423, by rfl⟩ : syracuseStep 1827231 = 2740847) B2740847
theorem B1827311 : Blo 1825614 1827311 := bstep (se 1 (by rfl) ⟨1370483, by rfl⟩ : syracuseStep 1827311 = 2740967) B2740967
theorem B1827419 : Blo 1825614 1827419 := bstep (se 1 (by rfl) ⟨1370564, by rfl⟩ : syracuseStep 1827419 = 2741129) B2741129
theorem B1950527 : Blo 1825614 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B3081287 : Blo 1825614 3081287 := bstep (se 1 (by rfl) ⟨2310965, by rfl⟩ : syracuseStep 3081287 = 4621931) B4621931
theorem B10544393 : Blo 1825614 10544393 := bstep (se 2 (by rfl) ⟨3954147, by rfl⟩ : syracuseStep 10544393 = 7908295) B7908295
theorem B17548625 : Blo 1825614 17548625 := bstep (se 2 (by rfl) ⟨6580734, by rfl⟩ : syracuseStep 17548625 = 13161469) B13161469
theorem B6161831 : Blo 1825614 6161831 := bstep (se 1 (by rfl) ⟨4621373, by rfl⟩ : syracuseStep 6161831 = 9242747) B9242747
theorem B20817323 : Blo 1825614 20817323 := bstep (se 1 (by rfl) ⟨15612992, by rfl⟩ : syracuseStep 20817323 = 31225985) B31225985
theorem B3081719 : Blo 1825614 3081719 := bstep (se 1 (by rfl) ⟨2311289, by rfl⟩ : syracuseStep 3081719 = 4622579) B4622579
theorem B33342995 : Blo 1825614 33342995 := bstep (se 1 (by rfl) ⟨25007246, by rfl⟩ : syracuseStep 33342995 = 50014493) B50014493
theorem B28124729 : Blo 1825614 28124729 := bstep (se 2 (by rfl) ⟨10546773, by rfl⟩ : syracuseStep 28124729 = 21093547) B21093547
theorem B17548933 : Blo 1825614 17548933 := bstep (se 4 (by rfl) ⟨1645212, by rfl⟩ : syracuseStep 17548933 = 3290425) B3290425
theorem B4621961 : Blo 1825614 4621961 := bstep (se 2 (by rfl) ⟨1733235, by rfl⟩ : syracuseStep 4621961 = 3466471) B3466471
theorem B14452397 : Blo 1825614 14452397 := bstep (se 3 (by rfl) ⟨2709824, by rfl⟩ : syracuseStep 14452397 = 5419649) B5419649
theorem B5850863 : Blo 1825614 5850863 := bstep (se 1 (by rfl) ⟨4388147, by rfl⟩ : syracuseStep 5850863 = 8776295) B8776295
theorem B5850875 : Blo 1825614 5850875 := bstep (se 1 (by rfl) ⟨4388156, by rfl⟩ : syracuseStep 5850875 = 8776313) B8776313
theorem B4622143 : Blo 1825614 4622143 := bstep (se 1 (by rfl) ⟨3466607, by rfl⟩ : syracuseStep 4622143 = 6933215) B6933215
theorem B2926457 : Blo 1825614 2926457 := bstep (se 2 (by rfl) ⟨1097421, by rfl⟩ : syracuseStep 2926457 = 2194843) B2194843
theorem B3467519 : Blo 1825614 3467519 := bstep (se 1 (by rfl) ⟨2600639, by rfl⟩ : syracuseStep 3467519 = 5201279) B5201279
theorem B6162695 : Blo 1825614 6162695 := bstep (se 1 (by rfl) ⟨4622021, by rfl⟩ : syracuseStep 6162695 = 9244043) B9244043
theorem B3705095 : Blo 1825614 3705095 := bstep (se 1 (by rfl) ⟨2778821, by rfl⟩ : syracuseStep 3705095 = 5557643) B5557643
theorem B4164079 : Blo 1825614 4164079 := bstep (se 1 (by rfl) ⟨3123059, by rfl⟩ : syracuseStep 4164079 = 6246119) B6246119
theorem B59230763 : Blo 1825614 59230763 := bstep (se 1 (by rfl) ⟨44423072, by rfl⟩ : syracuseStep 59230763 = 88846145) B88846145
theorem B3082799 : Blo 1825614 3082799 := bstep (se 1 (by rfl) ⟨2312099, by rfl⟩ : syracuseStep 3082799 = 4624199) B4624199
theorem B13871897 : Blo 1825614 13871897 := bstep (se 2 (by rfl) ⟨5201961, by rfl⟩ : syracuseStep 13871897 = 10403923) B10403923
theorem B3468089 : Blo 1825614 3468089 := bstep (se 2 (by rfl) ⟨1300533, by rfl⟩ : syracuseStep 3468089 = 2601067) B2601067
theorem B15608861 : Blo 1825614 15608861 := bstep (se 3 (by rfl) ⟨2926661, by rfl⟩ : syracuseStep 15608861 = 5853323) B5853323
theorem B82275409 : Blo 1825614 82275409 := bstep (se 2 (by rfl) ⟨30853278, by rfl⟩ : syracuseStep 82275409 = 61706557) B61706557
theorem B2600047 : Blo 1825614 2600047 := bstep (se 1 (by rfl) ⟨1950035, by rfl⟩ : syracuseStep 2600047 = 3900071) B3900071
theorem B6933671 : Blo 1825614 6933671 := bstep (se 1 (by rfl) ⟨5200253, by rfl⟩ : syracuseStep 6933671 = 10400507) B10400507
theorem B2739407 : Blo 1825614 2739407 := bstep (se 1 (by rfl) ⟨2054555, by rfl⟩ : syracuseStep 2739407 = 4109111) B4109111
theorem B6163721 : Blo 1825614 6163721 := bstep (se 2 (by rfl) ⟨2311395, by rfl⟩ : syracuseStep 6163721 = 4622791) B4622791
theorem B2739527 : Blo 1825614 2739527 := bstep (se 1 (by rfl) ⟨2054645, by rfl⟩ : syracuseStep 2739527 = 4109291) B4109291
theorem B17558855 : Blo 1825614 17558855 := bstep (se 1 (by rfl) ⟨13169141, by rfl⟩ : syracuseStep 17558855 = 26338283) B26338283
theorem B237022685 : Blo 1825614 237022685 := bstep (se 3 (by rfl) ⟨44441753, by rfl⟩ : syracuseStep 237022685 = 88883507) B88883507
theorem B2739935 : Blo 1825614 2739935 := bstep (se 1 (by rfl) ⟨2054951, by rfl⟩ : syracuseStep 2739935 = 4109903) B4109903
theorem B3084007 : Blo 1825614 3084007 := bstep (se 1 (by rfl) ⟨2313005, by rfl⟩ : syracuseStep 3084007 = 4626011) B4626011
theorem B3903241 : Blo 1825614 3903241 := bstep (se 2 (by rfl) ⟨1463715, by rfl⟩ : syracuseStep 3903241 = 2927431) B2927431
theorem B4935487 : Blo 1825614 4935487 := bstep (se 1 (by rfl) ⟨3701615, by rfl⟩ : syracuseStep 4935487 = 7403231) B7403231
theorem B4108283 : Blo 1825614 4108283 := bstep (se 1 (by rfl) ⟨3081212, by rfl⟩ : syracuseStep 4108283 = 6162425) B6162425
theorem B2740295 : Blo 1825614 2740295 := bstep (se 1 (by rfl) ⟨2055221, by rfl⟩ : syracuseStep 2740295 = 4110443) B4110443
theorem B2740415 : Blo 1825614 2740415 := bstep (se 1 (by rfl) ⟨2055311, by rfl⟩ : syracuseStep 2740415 = 4110623) B4110623
theorem B35107091 : Blo 1825614 35107091 := bstep (se 1 (by rfl) ⟨26330318, by rfl⟩ : syracuseStep 35107091 = 52660637) B52660637
theorem B2740559 : Blo 1825614 2740559 := bstep (se 1 (by rfl) ⟨2055419, by rfl⟩ : syracuseStep 2740559 = 4110839) B4110839
theorem B2740601 : Blo 1825614 2740601 := bstep (se 2 (by rfl) ⟨1027725, by rfl⟩ : syracuseStep 2740601 = 2055451) B2055451
theorem B53375375 : Blo 1825614 53375375 := bstep (se 1 (by rfl) ⟨40031531, by rfl⟩ : syracuseStep 53375375 = 80063063) B80063063
theorem B2740895 : Blo 1825614 2740895 := bstep (se 1 (by rfl) ⟨2055671, by rfl⟩ : syracuseStep 2740895 = 4111343) B4111343
theorem B4108967 : Blo 1825614 4108967 := bstep (se 1 (by rfl) ⟨3081725, by rfl⟩ : syracuseStep 4108967 = 6163451) B6163451
theorem B2741225 : Blo 1825614 2741225 := bstep (se 2 (by rfl) ⟨1027959, by rfl⟩ : syracuseStep 2741225 = 2055919) B2055919
theorem B2741279 : Blo 1825614 2741279 := bstep (se 1 (by rfl) ⟨2055959, by rfl⟩ : syracuseStep 2741279 = 4111919) B4111919
theorem B4109993 : Blo 1825614 4109993 := bstep (se 2 (by rfl) ⟨1541247, by rfl⟩ : syracuseStep 4109993 = 3082495) B3082495
theorem B15603425 : Blo 1825614 15603425 := bstep (se 2 (by rfl) ⟨5851284, by rfl⟩ : syracuseStep 15603425 = 11702569) B11702569
theorem B26343235 : Blo 1825614 26343235 := bstep (se 1 (by rfl) ⟨19757426, by rfl⟩ : syracuseStep 26343235 = 39514853) B39514853
theorem B20805659 : Blo 1825614 20805659 := bstep (se 1 (by rfl) ⟨15604244, by rfl⟩ : syracuseStep 20805659 = 31208489) B31208489
theorem B6674671 : Blo 1825614 6674671 := bstep (se 1 (by rfl) ⟨5006003, by rfl⟩ : syracuseStep 6674671 = 10012007) B10012007
theorem B7805267 : Blo 1825614 7805267 := bstep (se 1 (by rfl) ⟨5853950, by rfl⟩ : syracuseStep 7805267 = 11707901) B11707901
theorem B1825663 : Blo 1825614 1825663 := bstep (se 1 (by rfl) ⟨1369247, by rfl⟩ : syracuseStep 1825663 = 2738495) B2738495
theorem B6937559 : Blo 1825614 6937559 := bstep (se 1 (by rfl) ⟨5203169, by rfl⟩ : syracuseStep 6937559 = 10406339) B10406339
theorem B1825759 : Blo 1825614 1825759 := bstep (se 1 (by rfl) ⟨1369319, by rfl⟩ : syracuseStep 1825759 = 2738639) B2738639
theorem B1825787 : Blo 1825614 1825787 := bstep (se 1 (by rfl) ⟨1369340, by rfl⟩ : syracuseStep 1825787 = 2738681) B2738681
theorem B1825819 : Blo 1825614 1825819 := bstep (se 1 (by rfl) ⟨1369364, by rfl⟩ : syracuseStep 1825819 = 2738729) B2738729
theorem B11705543 : Blo 1825614 11705543 := bstep (se 1 (by rfl) ⟨8779157, by rfl⟩ : syracuseStep 11705543 = 17558315) B17558315
theorem B1826111 : Blo 1825614 1826111 := bstep (se 1 (by rfl) ⟨1369583, by rfl⟩ : syracuseStep 1826111 = 2739167) B2739167
theorem B6938045 : Blo 1825614 6938045 := bstep (se 3 (by rfl) ⟨1300883, by rfl⟩ : syracuseStep 6938045 = 2601767) B2601767
theorem B6168041 : Blo 1825614 6168041 := bstep (se 2 (by rfl) ⟨2313015, by rfl⟩ : syracuseStep 6168041 = 4626031) B4626031
theorem B1826407 : Blo 1825614 1826407 := bstep (se 1 (by rfl) ⟨1369805, by rfl⟩ : syracuseStep 1826407 = 2739611) B2739611
theorem B1826651 : Blo 1825614 1826651 := bstep (se 1 (by rfl) ⟨1369988, by rfl⟩ : syracuseStep 1826651 = 2739977) B2739977
theorem B1826687 : Blo 1825614 1826687 := bstep (se 1 (by rfl) ⟨1370015, by rfl⟩ : syracuseStep 1826687 = 2740031) B2740031
theorem B7405519 : Blo 1825614 7405519 := bstep (se 1 (by rfl) ⟨5554139, by rfl⟩ : syracuseStep 7405519 = 11108279) B11108279
theorem B5849081 : Blo 1825614 5849081 := bstep (se 2 (by rfl) ⟨2193405, by rfl⟩ : syracuseStep 5849081 = 4386811) B4386811
theorem B1826863 : Blo 1825614 1826863 := bstep (se 1 (by rfl) ⟨1370147, by rfl⟩ : syracuseStep 1826863 = 2740295) B2740295
theorem B1826943 : Blo 1825614 1826943 := bstep (se 1 (by rfl) ⟨1370207, by rfl⟩ : syracuseStep 1826943 = 2740415) B2740415
theorem B23404727 : Blo 1825614 23404727 := bstep (se 1 (by rfl) ⟨17553545, by rfl⟩ : syracuseStep 23404727 = 35107091) B35107091
theorem B7798979 : Blo 1825614 7798979 := bstep (se 1 (by rfl) ⟨5849234, by rfl⟩ : syracuseStep 7798979 = 11698469) B11698469
theorem B1827039 : Blo 1825614 1827039 := bstep (se 1 (by rfl) ⟨1370279, by rfl⟩ : syracuseStep 1827039 = 2740559) B2740559
theorem B1827067 : Blo 1825614 1827067 := bstep (se 1 (by rfl) ⟨1370300, by rfl⟩ : syracuseStep 1827067 = 2740601) B2740601
theorem B1827263 : Blo 1825614 1827263 := bstep (se 1 (by rfl) ⟨1370447, by rfl⟩ : syracuseStep 1827263 = 2740895) B2740895
theorem B1827483 : Blo 1825614 1827483 := bstep (se 1 (by rfl) ⟨1370612, by rfl⟩ : syracuseStep 1827483 = 2741225) B2741225
theorem B1827519 : Blo 1825614 1827519 := bstep (se 1 (by rfl) ⟨1370639, by rfl⟩ : syracuseStep 1827519 = 2741279) B2741279
theorem B7029595 : Blo 1825614 7029595 := bstep (se 1 (by rfl) ⟨5272196, by rfl⟩ : syracuseStep 7029595 = 10544393) B10544393
theorem B11699083 : Blo 1825614 11699083 := bstep (se 1 (by rfl) ⟨8774312, by rfl⟩ : syracuseStep 11699083 = 17548625) B17548625
theorem B13878215 : Blo 1825614 13878215 := bstep (se 1 (by rfl) ⟨10408661, by rfl⟩ : syracuseStep 13878215 = 20817323) B20817323
theorem B3081307 : Blo 1825614 3081307 := bstep (se 1 (by rfl) ⟨2310980, by rfl⟩ : syracuseStep 3081307 = 4621961) B4621961
theorem B9634931 : Blo 1825614 9634931 := bstep (se 1 (by rfl) ⟨7226198, by rfl⟩ : syracuseStep 9634931 = 14452397) B14452397
theorem B3900575 : Blo 1825614 3900575 := bstep (se 1 (by rfl) ⟨2925431, by rfl⟩ : syracuseStep 3900575 = 5850863) B5850863
theorem B3900583 : Blo 1825614 3900583 := bstep (se 1 (by rfl) ⟨2925437, by rfl⟩ : syracuseStep 3900583 = 5850875) B5850875
theorem B1950971 : Blo 1825614 1950971 := bstep (se 1 (by rfl) ⟨1463228, by rfl⟩ : syracuseStep 1950971 = 2926457) B2926457
theorem B13870439 : Blo 1825614 13870439 := bstep (se 1 (by rfl) ⟨10402829, by rfl⟩ : syracuseStep 13870439 = 20805659) B20805659
theorem B3466729 : Blo 1825614 3466729 := bstep (se 2 (by rfl) ⟨1300023, by rfl⟩ : syracuseStep 3466729 = 2600047) B2600047
theorem B2311679 : Blo 1825614 2311679 := bstep (se 1 (by rfl) ⟨1733759, by rfl⟩ : syracuseStep 2311679 = 3467519) B3467519
theorem B5203511 : Blo 1825614 5203511 := bstep (se 1 (by rfl) ⟨3902633, by rfl⟩ : syracuseStep 5203511 = 7805267) B7805267
theorem B39487175 : Blo 1825614 39487175 := bstep (se 1 (by rfl) ⟨29615381, by rfl⟩ : syracuseStep 39487175 = 59230763) B59230763
theorem B2312059 : Blo 1825614 2312059 := bstep (se 1 (by rfl) ⟨1734044, by rfl⟩ : syracuseStep 2312059 = 3468089) B3468089
theorem B10405907 : Blo 1825614 10405907 := bstep (se 1 (by rfl) ⟨7804430, by rfl⟩ : syracuseStep 10405907 = 15608861) B15608861
theorem B4622447 : Blo 1825614 4622447 := bstep (se 1 (by rfl) ⟨3466835, by rfl⟩ : syracuseStep 4622447 = 6933671) B6933671
theorem B23398577 : Blo 1825614 23398577 := bstep (se 2 (by rfl) ⟨8774466, by rfl⟩ : syracuseStep 23398577 = 17548933) B17548933
theorem B5204321 : Blo 1825614 5204321 := bstep (se 2 (by rfl) ⟨1951620, by rfl⟩ : syracuseStep 5204321 = 3903241) B3903241
theorem B6580649 : Blo 1825614 6580649 := bstep (se 2 (by rfl) ⟨2467743, by rfl⟩ : syracuseStep 6580649 = 4935487) B4935487
theorem B6162857 : Blo 1825614 6162857 := bstep (se 2 (by rfl) ⟨2311071, by rfl⟩ : syracuseStep 6162857 = 4622143) B4622143
theorem B9874025 : Blo 1825614 9874025 := bstep (se 2 (by rfl) ⟨3702759, by rfl⟩ : syracuseStep 9874025 = 7405519) B7405519
theorem B2738855 : Blo 1825614 2738855 := bstep (se 1 (by rfl) ⟨2054141, by rfl⟩ : syracuseStep 2738855 = 4108283) B4108283
theorem B8899561 : Blo 1825614 8899561 := bstep (se 2 (by rfl) ⟨3337335, by rfl⟩ : syracuseStep 8899561 = 6674671) B6674671
theorem B2739311 : Blo 1825614 2739311 := bstep (se 1 (by rfl) ⟨2054483, by rfl⟩ : syracuseStep 2739311 = 4108967) B4108967
theorem B4107887 : Blo 1825614 4107887 := bstep (se 1 (by rfl) ⟨3080915, by rfl⟩ : syracuseStep 4107887 = 6161831) B6161831
theorem B22228663 : Blo 1825614 22228663 := bstep (se 1 (by rfl) ⟨16671497, by rfl⟩ : syracuseStep 22228663 = 33342995) B33342995
theorem B2739995 : Blo 1825614 2739995 := bstep (se 1 (by rfl) ⟨2054996, by rfl⟩ : syracuseStep 2739995 = 4109993) B4109993
theorem B9875429 : Blo 1825614 9875429 := bstep (se 4 (by rfl) ⟨925821, by rfl⟩ : syracuseStep 9875429 = 1851643) B1851643
theorem B4108463 : Blo 1825614 4108463 := bstep (se 1 (by rfl) ⟨3081347, by rfl⟩ : syracuseStep 4108463 = 6162695) B6162695
theorem B2470063 : Blo 1825614 2470063 := bstep (se 1 (by rfl) ⟨1852547, by rfl⟩ : syracuseStep 2470063 = 3705095) B3705095
theorem B4625039 : Blo 1825614 4625039 := bstep (se 1 (by rfl) ⟨3468779, by rfl⟩ : syracuseStep 4625039 = 6937559) B6937559
theorem B7803695 : Blo 1825614 7803695 := bstep (se 1 (by rfl) ⟨5852771, by rfl⟩ : syracuseStep 7803695 = 11705543) B11705543
theorem B4109147 : Blo 1825614 4109147 := bstep (se 1 (by rfl) ⟨3081860, by rfl⟩ : syracuseStep 4109147 = 6163721) B6163721
theorem B4625363 : Blo 1825614 4625363 := bstep (se 1 (by rfl) ⟨3469022, by rfl⟩ : syracuseStep 4625363 = 6938045) B6938045
theorem B35124313 : Blo 1825614 35124313 := bstep (se 2 (by rfl) ⟨13171617, by rfl⟩ : syracuseStep 35124313 = 26343235) B26343235
theorem B30037337 : Blo 1825614 30037337 := bstep (se 2 (by rfl) ⟨11264001, by rfl⟩ : syracuseStep 30037337 = 22528003) B22528003
theorem B169039223 : Blo 1825614 169039223 := bstep (se 1 (by rfl) ⟨126779417, by rfl⟩ : syracuseStep 169039223 = 253558835) B253558835
theorem B6166043 : Blo 1825614 6166043 := bstep (se 1 (by rfl) ⟨4624532, by rfl⟩ : syracuseStep 6166043 = 9249065) B9249065
theorem B35583583 : Blo 1825614 35583583 := bstep (se 1 (by rfl) ⟨26687687, by rfl⟩ : syracuseStep 35583583 = 53375375) B53375375
theorem B438802181 : Blo 1825614 438802181 := bstep (se 4 (by rfl) ⟨41137704, by rfl⟩ : syracuseStep 438802181 = 82275409) B82275409
theorem B2054191 : Blo 1825614 2054191 := bstep (se 1 (by rfl) ⟨1540643, by rfl⟩ : syracuseStep 2054191 = 3081287) B3081287
theorem B2054479 : Blo 1825614 2054479 := bstep (se 1 (by rfl) ⟨1540859, by rfl⟩ : syracuseStep 2054479 = 3081719) B3081719
theorem B18749819 : Blo 1825614 18749819 := bstep (se 1 (by rfl) ⟨14062364, by rfl⟩ : syracuseStep 18749819 = 28124729) B28124729
theorem B10402283 : Blo 1825614 10402283 := bstep (se 1 (by rfl) ⟨7801712, by rfl⟩ : syracuseStep 10402283 = 15603425) B15603425
theorem B2055199 : Blo 1825614 2055199 := bstep (se 1 (by rfl) ⟨1541399, by rfl⟩ : syracuseStep 2055199 = 3082799) B3082799
theorem B9247931 : Blo 1825614 9247931 := bstep (se 1 (by rfl) ⟨6935948, by rfl⟩ : syracuseStep 9247931 = 13871897) B13871897
theorem B1826271 : Blo 1825614 1826271 := bstep (se 1 (by rfl) ⟨1369703, by rfl⟩ : syracuseStep 1826271 = 2739407) B2739407
theorem B5201405 : Blo 1825614 5201405 := bstep (se 3 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 5201405 = 1950527) B1950527
theorem B1826351 : Blo 1825614 1826351 := bstep (se 1 (by rfl) ⟨1369763, by rfl⟩ : syracuseStep 1826351 = 2739527) B2739527
theorem B11705903 : Blo 1825614 11705903 := bstep (se 1 (by rfl) ⟨8779427, by rfl⟩ : syracuseStep 11705903 = 17558855) B17558855
theorem B4112009 : Blo 1825614 4112009 := bstep (se 2 (by rfl) ⟨1542003, by rfl⟩ : syracuseStep 4112009 = 3084007) B3084007
theorem B158015123 : Blo 1825614 158015123 := bstep (se 1 (by rfl) ⟨118511342, by rfl⟩ : syracuseStep 158015123 = 237022685) B237022685
theorem B88833685 : Blo 1825614 88833685 := bstep (se 6 (by rfl) ⟨2082039, by rfl⟩ : syracuseStep 88833685 = 4164079) B4164079
theorem B4112027 : Blo 1825614 4112027 := bstep (se 1 (by rfl) ⟨3084020, by rfl⟩ : syracuseStep 4112027 = 6168041) B6168041
theorem B1826623 : Blo 1825614 1826623 := bstep (se 1 (by rfl) ⟨1369967, by rfl⟩ : syracuseStep 1826623 = 2739935) B2739935
theorem B3899387 : Blo 1825614 3899387 := bstep (se 1 (by rfl) ⟨2924540, by rfl⟩ : syracuseStep 3899387 = 5849081) B5849081
theorem B3293417 : Blo 1825614 3293417 := bstep (se 2 (by rfl) ⟨1235031, by rfl⟩ : syracuseStep 3293417 = 2470063) B2470063
theorem B5202463 : Blo 1825614 5202463 := bstep (se 1 (by rfl) ⟨3901847, by rfl⟩ : syracuseStep 5202463 = 7803695) B7803695
theorem B5202589 : Blo 1825614 5202589 := bstep (se 3 (by rfl) ⟨975485, by rfl⟩ : syracuseStep 5202589 = 1950971) B1950971
theorem B17548397 : Blo 1825614 17548397 := bstep (se 3 (by rfl) ⟨3290324, by rfl⟩ : syracuseStep 17548397 = 6580649) B6580649
theorem B15598777 : Blo 1825614 15598777 := bstep (se 2 (by rfl) ⟨5849541, by rfl⟩ : syracuseStep 15598777 = 11699083) B11699083
theorem B3081631 : Blo 1825614 3081631 := bstep (se 1 (by rfl) ⟨2311223, by rfl⟩ : syracuseStep 3081631 = 4622447) B4622447
theorem B15599051 : Blo 1825614 15599051 := bstep (se 1 (by rfl) ⟨11699288, by rfl⟩ : syracuseStep 15599051 = 23398577) B23398577
theorem B4622305 : Blo 1825614 4622305 := bstep (se 2 (by rfl) ⟨1733364, by rfl⟩ : syracuseStep 4622305 = 3466729) B3466729
theorem B3467603 : Blo 1825614 3467603 := bstep (se 1 (by rfl) ⟨2600702, by rfl⟩ : syracuseStep 3467603 = 5201405) B5201405
theorem B2738591 : Blo 1825614 2738591 := bstep (se 1 (by rfl) ⟨2053943, by rfl⟩ : syracuseStep 2738591 = 4107887) B4107887
theorem B105343415 : Blo 1825614 105343415 := bstep (se 1 (by rfl) ⟨79007561, by rfl⟩ : syracuseStep 105343415 = 158015123) B158015123
theorem B3082745 : Blo 1825614 3082745 := bstep (se 2 (by rfl) ⟨1156029, by rfl⟩ : syracuseStep 3082745 = 2312059) B2312059
theorem B10398365 : Blo 1825614 10398365 := bstep (se 3 (by rfl) ⟨1949693, by rfl⟩ : syracuseStep 10398365 = 3899387) B3899387
theorem B2738921 : Blo 1825614 2738921 := bstep (se 2 (by rfl) ⟨1027095, by rfl⟩ : syracuseStep 2738921 = 2054191) B2054191
theorem B2738975 : Blo 1825614 2738975 := bstep (se 1 (by rfl) ⟨2054231, by rfl⟩ : syracuseStep 2738975 = 4108463) B4108463
theorem B3083359 : Blo 1825614 3083359 := bstep (se 1 (by rfl) ⟨2312519, by rfl⟩ : syracuseStep 3083359 = 4625039) B4625039
theorem B2739305 : Blo 1825614 2739305 := bstep (se 2 (by rfl) ⟨1027239, by rfl⟩ : syracuseStep 2739305 = 2054479) B2054479
theorem B2739431 : Blo 1825614 2739431 := bstep (se 1 (by rfl) ⟨2054573, by rfl⟩ : syracuseStep 2739431 = 4109147) B4109147
theorem B9252143 : Blo 1825614 9252143 := bstep (se 1 (by rfl) ⟨6939107, by rfl⟩ : syracuseStep 9252143 = 13878215) B13878215
theorem B3083575 : Blo 1825614 3083575 := bstep (se 1 (by rfl) ⟨2312681, by rfl⟩ : syracuseStep 3083575 = 4625363) B4625363
theorem B20024891 : Blo 1825614 20024891 := bstep (se 1 (by rfl) ⟨15018668, by rfl⟩ : syracuseStep 20024891 = 30037337) B30037337
theorem B112692815 : Blo 1825614 112692815 := bstep (se 1 (by rfl) ⟨84519611, by rfl⟩ : syracuseStep 112692815 = 169039223) B169039223
theorem B3469007 : Blo 1825614 3469007 := bstep (se 1 (by rfl) ⟨2601755, by rfl⟩ : syracuseStep 3469007 = 5203511) B5203511
theorem B26324783 : Blo 1825614 26324783 := bstep (se 1 (by rfl) ⟨19743587, by rfl⟩ : syracuseStep 26324783 = 39487175) B39487175
theorem B102772597 : Blo 1825614 102772597 := bstep (se 5 (by rfl) ⟨4817465, by rfl⟩ : syracuseStep 102772597 = 9634931) B9634931
theorem B6164477 : Blo 1825614 6164477 := bstep (se 3 (by rfl) ⟨1155839, by rfl⟩ : syracuseStep 6164477 = 2311679) B2311679
theorem B2740265 : Blo 1825614 2740265 := bstep (se 2 (by rfl) ⟨1027599, by rfl⟩ : syracuseStep 2740265 = 2055199) B2055199
theorem B4108409 : Blo 1825614 4108409 := bstep (se 2 (by rfl) ⟨1540653, by rfl⟩ : syracuseStep 4108409 = 3081307) B3081307
theorem B3469547 : Blo 1825614 3469547 := bstep (se 1 (by rfl) ⟨2602160, by rfl⟩ : syracuseStep 3469547 = 5204321) B5204321
theorem B4108571 : Blo 1825614 4108571 := bstep (se 1 (by rfl) ⟨3081428, by rfl⟩ : syracuseStep 4108571 = 6162857) B6162857
theorem B6934855 : Blo 1825614 6934855 := bstep (se 1 (by rfl) ⟨5201141, by rfl⟩ : syracuseStep 6934855 = 10402283) B10402283
theorem B6582683 : Blo 1825614 6582683 := bstep (se 1 (by rfl) ⟨4937012, by rfl⟩ : syracuseStep 6582683 = 9874025) B9874025
theorem B37491173 : Blo 1825614 37491173 := bstep (se 4 (by rfl) ⟨3514797, by rfl⟩ : syracuseStep 37491173 = 7029595) B7029595
theorem B6165287 : Blo 1825614 6165287 := bstep (se 1 (by rfl) ⟨4623965, by rfl⟩ : syracuseStep 6165287 = 9247931) B9247931
theorem B47444777 : Blo 1825614 47444777 := bstep (se 2 (by rfl) ⟨17791791, by rfl⟩ : syracuseStep 47444777 = 35583583) B35583583
theorem B118444913 : Blo 1825614 118444913 := bstep (se 2 (by rfl) ⟨44416842, by rfl⟩ : syracuseStep 118444913 = 88833685) B88833685
theorem B7803935 : Blo 1825614 7803935 := bstep (se 1 (by rfl) ⟨5852951, by rfl⟩ : syracuseStep 7803935 = 11705903) B11705903
theorem B2741339 : Blo 1825614 2741339 := bstep (se 1 (by rfl) ⟨2056004, by rfl⟩ : syracuseStep 2741339 = 4112009) B4112009
theorem B2741351 : Blo 1825614 2741351 := bstep (se 1 (by rfl) ⟨2056013, by rfl⟩ : syracuseStep 2741351 = 4112027) B4112027
theorem B6583619 : Blo 1825614 6583619 := bstep (se 1 (by rfl) ⟨4937714, by rfl⟩ : syracuseStep 6583619 = 9875429) B9875429
theorem B15603151 : Blo 1825614 15603151 := bstep (se 1 (by rfl) ⟨11702363, by rfl⟩ : syracuseStep 15603151 = 23404727) B23404727
theorem B5199319 : Blo 1825614 5199319 := bstep (se 1 (by rfl) ⟨3899489, by rfl⟩ : syracuseStep 5199319 = 7798979) B7798979
theorem B10401533 : Blo 1825614 10401533 := bstep (se 3 (by rfl) ⟨1950287, by rfl⟩ : syracuseStep 10401533 = 3900575) B3900575
theorem B9246959 : Blo 1825614 9246959 := bstep (se 1 (by rfl) ⟨6935219, by rfl⟩ : syracuseStep 9246959 = 13870439) B13870439
theorem B4110695 : Blo 1825614 4110695 := bstep (se 1 (by rfl) ⟨3083021, by rfl⟩ : syracuseStep 4110695 = 6166043) B6166043
theorem B292534787 : Blo 1825614 292534787 := bstep (se 1 (by rfl) ⟨219401090, by rfl⟩ : syracuseStep 292534787 = 438802181) B438802181
theorem B6937271 : Blo 1825614 6937271 := bstep (se 1 (by rfl) ⟨5202953, by rfl⟩ : syracuseStep 6937271 = 10405907) B10405907
theorem B46832417 : Blo 1825614 46832417 := bstep (se 2 (by rfl) ⟨17562156, by rfl⟩ : syracuseStep 46832417 = 35124313) B35124313
theorem B5200777 : Blo 1825614 5200777 := bstep (se 2 (by rfl) ⟨1950291, by rfl⟩ : syracuseStep 5200777 = 3900583) B3900583
theorem B12499879 : Blo 1825614 12499879 := bstep (se 1 (by rfl) ⟨9374909, by rfl⟩ : syracuseStep 12499879 = 18749819) B18749819
theorem B1825903 : Blo 1825614 1825903 := bstep (se 1 (by rfl) ⟨1369427, by rfl⟩ : syracuseStep 1825903 = 2738855) B2738855
theorem B1826207 : Blo 1825614 1826207 := bstep (se 1 (by rfl) ⟨1369655, by rfl⟩ : syracuseStep 1826207 = 2739311) B2739311
theorem B29638217 : Blo 1825614 29638217 := bstep (se 2 (by rfl) ⟨11114331, by rfl⟩ : syracuseStep 29638217 = 22228663) B22228663
theorem B1826663 : Blo 1825614 1826663 := bstep (se 1 (by rfl) ⟨1369997, by rfl⟩ : syracuseStep 1826663 = 2739995) B2739995
theorem B47464325 : Blo 1825614 47464325 := bstep (se 4 (by rfl) ⟨4449780, by rfl⟩ : syracuseStep 47464325 = 8899561) B8899561
theorem B1826843 : Blo 1825614 1826843 := bstep (se 1 (by rfl) ⟨1370132, by rfl⟩ : syracuseStep 1826843 = 2740265) B2740265
theorem B24994115 : Blo 1825614 24994115 := bstep (se 1 (by rfl) ⟨18745586, by rfl⟩ : syracuseStep 24994115 = 37491173) B37491173
theorem B31629851 : Blo 1825614 31629851 := bstep (se 1 (by rfl) ⟨23722388, by rfl⟩ : syracuseStep 31629851 = 47444777) B47444777
theorem B78963275 : Blo 1825614 78963275 := bstep (se 1 (by rfl) ⟨59222456, by rfl⟩ : syracuseStep 78963275 = 118444913) B118444913
theorem B8782445 : Blo 1825614 8782445 := bstep (se 3 (by rfl) ⟨1646708, by rfl⟩ : syracuseStep 8782445 = 3293417) B3293417
theorem B5202623 : Blo 1825614 5202623 := bstep (se 1 (by rfl) ⟨3901967, by rfl⟩ : syracuseStep 5202623 = 7803935) B7803935
theorem B1827559 : Blo 1825614 1827559 := bstep (se 1 (by rfl) ⟨1370669, by rfl⟩ : syracuseStep 1827559 = 2741339) B2741339
theorem B1827567 : Blo 1825614 1827567 := bstep (se 1 (by rfl) ⟨1370675, by rfl⟩ : syracuseStep 1827567 = 2741351) B2741351
theorem B11698931 : Blo 1825614 11698931 := bstep (se 1 (by rfl) ⟨8774198, by rfl⟩ : syracuseStep 11698931 = 17548397) B17548397
theorem B780092765 : Blo 1825614 780092765 := bstep (se 3 (by rfl) ⟨146267393, by rfl⟩ : syracuseStep 780092765 = 292534787) B292534787
theorem B2311735 : Blo 1825614 2311735 := bstep (se 1 (by rfl) ⟨1733801, by rfl⟩ : syracuseStep 2311735 = 3467603) B3467603
theorem B6932243 : Blo 1825614 6932243 := bstep (se 1 (by rfl) ⟨5199182, by rfl⟩ : syracuseStep 6932243 = 10398365) B10398365
theorem B31221611 : Blo 1825614 31221611 := bstep (se 1 (by rfl) ⟨23416208, by rfl⟩ : syracuseStep 31221611 = 46832417) B46832417
theorem B9250685 : Blo 1825614 9250685 := bstep (se 3 (by rfl) ⟨1734503, by rfl⟩ : syracuseStep 9250685 = 3469007) B3469007
theorem B6932425 : Blo 1825614 6932425 := bstep (se 2 (by rfl) ⟨2599659, by rfl⟩ : syracuseStep 6932425 = 5199319) B5199319
theorem B137030129 : Blo 1825614 137030129 := bstep (se 2 (by rfl) ⟨51386298, by rfl⟩ : syracuseStep 137030129 = 102772597) B102772597
theorem B17549855 : Blo 1825614 17549855 := bstep (se 1 (by rfl) ⟨13162391, by rfl⟩ : syracuseStep 17549855 = 26324783) B26324783
theorem B6163073 : Blo 1825614 6163073 := bstep (se 2 (by rfl) ⟨2311152, by rfl⟩ : syracuseStep 6163073 = 4622305) B4622305
theorem B2738939 : Blo 1825614 2738939 := bstep (se 1 (by rfl) ⟨2054204, by rfl⟩ : syracuseStep 2738939 = 4108409) B4108409
theorem B2313031 : Blo 1825614 2313031 := bstep (se 1 (by rfl) ⟨1734773, by rfl⟩ : syracuseStep 2313031 = 3469547) B3469547
theorem B2739047 : Blo 1825614 2739047 := bstep (se 1 (by rfl) ⟨2054285, by rfl⟩ : syracuseStep 2739047 = 4108571) B4108571
theorem B10399367 : Blo 1825614 10399367 := bstep (se 1 (by rfl) ⟨7799525, by rfl⟩ : syracuseStep 10399367 = 15599051) B15599051
theorem B6934355 : Blo 1825614 6934355 := bstep (se 1 (by rfl) ⟨5200766, by rfl⟩ : syracuseStep 6934355 = 10401533) B10401533
theorem B6934369 : Blo 1825614 6934369 := bstep (se 2 (by rfl) ⟨2600388, by rfl⟩ : syracuseStep 6934369 = 5200777) B5200777
theorem B16666505 : Blo 1825614 16666505 := bstep (se 2 (by rfl) ⟨6249939, by rfl⟩ : syracuseStep 16666505 = 12499879) B12499879
theorem B6164639 : Blo 1825614 6164639 := bstep (se 1 (by rfl) ⟨4623479, by rfl⟩ : syracuseStep 6164639 = 9246959) B9246959
theorem B2740463 : Blo 1825614 2740463 := bstep (se 1 (by rfl) ⟨2055347, by rfl⟩ : syracuseStep 2740463 = 4110695) B4110695
theorem B4624847 : Blo 1825614 4624847 := bstep (se 1 (by rfl) ⟨3468635, by rfl⟩ : syracuseStep 4624847 = 6937271) B6937271
theorem B4108841 : Blo 1825614 4108841 := bstep (se 2 (by rfl) ⟨1540815, by rfl⟩ : syracuseStep 4108841 = 3081631) B3081631
theorem B20804201 : Blo 1825614 20804201 := bstep (se 2 (by rfl) ⟨7801575, by rfl⟩ : syracuseStep 20804201 = 15603151) B15603151
theorem B13349927 : Blo 1825614 13349927 := bstep (se 1 (by rfl) ⟨10012445, by rfl⟩ : syracuseStep 13349927 = 20024891) B20024891
theorem B31642883 : Blo 1825614 31642883 := bstep (se 1 (by rfl) ⟨23732162, by rfl⟩ : syracuseStep 31642883 = 47464325) B47464325
theorem B4109651 : Blo 1825614 4109651 := bstep (se 1 (by rfl) ⟨3082238, by rfl⟩ : syracuseStep 4109651 = 6164477) B6164477
theorem B4388455 : Blo 1825614 4388455 := bstep (se 1 (by rfl) ⟨3291341, by rfl⟩ : syracuseStep 4388455 = 6582683) B6582683
theorem B9246473 : Blo 1825614 9246473 := bstep (se 2 (by rfl) ⟨3467427, by rfl⟩ : syracuseStep 9246473 = 6934855) B6934855
theorem B4110191 : Blo 1825614 4110191 := bstep (se 1 (by rfl) ⟨3082643, by rfl⟩ : syracuseStep 4110191 = 6165287) B6165287
theorem B6936617 : Blo 1825614 6936617 := bstep (se 2 (by rfl) ⟨2601231, by rfl⟩ : syracuseStep 6936617 = 5202463) B5202463
theorem B6936785 : Blo 1825614 6936785 := bstep (se 2 (by rfl) ⟨2601294, by rfl⟩ : syracuseStep 6936785 = 5202589) B5202589
theorem B4389079 : Blo 1825614 4389079 := bstep (se 1 (by rfl) ⟨3291809, by rfl⟩ : syracuseStep 4389079 = 6583619) B6583619
theorem B4111145 : Blo 1825614 4111145 := bstep (se 2 (by rfl) ⟨1541679, by rfl⟩ : syracuseStep 4111145 = 3083359) B3083359
theorem B20798369 : Blo 1825614 20798369 := bstep (se 2 (by rfl) ⟨7799388, by rfl⟩ : syracuseStep 20798369 = 15598777) B15598777
theorem B1825727 : Blo 1825614 1825727 := bstep (se 1 (by rfl) ⟨1369295, by rfl⟩ : syracuseStep 1825727 = 2738591) B2738591
theorem B70228943 : Blo 1825614 70228943 := bstep (se 1 (by rfl) ⟨52671707, by rfl⟩ : syracuseStep 70228943 = 105343415) B105343415
theorem B2055163 : Blo 1825614 2055163 := bstep (se 1 (by rfl) ⟨1541372, by rfl⟩ : syracuseStep 2055163 = 3082745) B3082745
theorem B4111433 : Blo 1825614 4111433 := bstep (se 2 (by rfl) ⟨1541787, by rfl⟩ : syracuseStep 4111433 = 3083575) B3083575
theorem B1825947 : Blo 1825614 1825947 := bstep (se 1 (by rfl) ⟨1369460, by rfl⟩ : syracuseStep 1825947 = 2738921) B2738921
theorem B1825983 : Blo 1825614 1825983 := bstep (se 1 (by rfl) ⟨1369487, by rfl⟩ : syracuseStep 1825983 = 2738975) B2738975
theorem B1826203 : Blo 1825614 1826203 := bstep (se 1 (by rfl) ⟨1369652, by rfl⟩ : syracuseStep 1826203 = 2739305) B2739305
theorem B1826287 : Blo 1825614 1826287 := bstep (se 1 (by rfl) ⟨1369715, by rfl⟩ : syracuseStep 1826287 = 2739431) B2739431
theorem B6168095 : Blo 1825614 6168095 := bstep (se 1 (by rfl) ⟨4626071, by rfl⟩ : syracuseStep 6168095 = 9252143) B9252143
theorem B19758811 : Blo 1825614 19758811 := bstep (se 1 (by rfl) ⟨14819108, by rfl⟩ : syracuseStep 19758811 = 29638217) B29638217
theorem B75128543 : Blo 1825614 75128543 := bstep (se 1 (by rfl) ⟨56346407, by rfl⟩ : syracuseStep 75128543 = 112692815) B112692815
theorem B1826975 : Blo 1825614 1826975 := bstep (se 1 (by rfl) ⟨1370231, by rfl⟩ : syracuseStep 1826975 = 2740463) B2740463
theorem B16662743 : Blo 1825614 16662743 := bstep (se 1 (by rfl) ⟨12497057, by rfl⟩ : syracuseStep 16662743 = 24994115) B24994115
theorem B21086567 : Blo 1825614 21086567 := bstep (se 1 (by rfl) ⟨15814925, by rfl⟩ : syracuseStep 21086567 = 31629851) B31629851
theorem B52642183 : Blo 1825614 52642183 := bstep (se 1 (by rfl) ⟨39481637, by rfl⟩ : syracuseStep 52642183 = 78963275) B78963275
theorem B13869467 : Blo 1825614 13869467 := bstep (se 1 (by rfl) ⟨10402100, by rfl⟩ : syracuseStep 13869467 = 20804201) B20804201
theorem B7799287 : Blo 1825614 7799287 := bstep (se 1 (by rfl) ⟨5849465, by rfl⟩ : syracuseStep 7799287 = 11698931) B11698931
theorem B21095255 : Blo 1825614 21095255 := bstep (se 1 (by rfl) ⟨15821441, by rfl⟩ : syracuseStep 21095255 = 31642883) B31642883
theorem B520061843 : Blo 1825614 520061843 := bstep (se 1 (by rfl) ⟨390046382, by rfl⟩ : syracuseStep 520061843 = 780092765) B780092765
theorem B4621495 : Blo 1825614 4621495 := bstep (se 1 (by rfl) ⟨3466121, by rfl⟩ : syracuseStep 4621495 = 6932243) B6932243
theorem B11699903 : Blo 1825614 11699903 := bstep (se 1 (by rfl) ⟨8774927, by rfl⟩ : syracuseStep 11699903 = 17549855) B17549855
theorem B46819295 : Blo 1825614 46819295 := bstep (se 1 (by rfl) ⟨35114471, by rfl⟩ : syracuseStep 46819295 = 70228943) B70228943
theorem B3082313 : Blo 1825614 3082313 := bstep (se 2 (by rfl) ⟨1155867, by rfl⟩ : syracuseStep 3082313 = 2311735) B2311735
theorem B5851273 : Blo 1825614 5851273 := bstep (se 2 (by rfl) ⟨2194227, by rfl⟩ : syracuseStep 5851273 = 4388455) B4388455
theorem B6932911 : Blo 1825614 6932911 := bstep (se 1 (by rfl) ⟨5199683, by rfl⟩ : syracuseStep 6932911 = 10399367) B10399367
theorem B4622903 : Blo 1825614 4622903 := bstep (se 1 (by rfl) ⟨3467177, by rfl⟩ : syracuseStep 4622903 = 6934355) B6934355
theorem B11111003 : Blo 1825614 11111003 := bstep (se 1 (by rfl) ⟨8333252, by rfl⟩ : syracuseStep 11111003 = 16666505) B16666505
theorem B9243233 : Blo 1825614 9243233 := bstep (se 2 (by rfl) ⟨3466212, by rfl⟩ : syracuseStep 9243233 = 6932425) B6932425
theorem B5852105 : Blo 1825614 5852105 := bstep (se 2 (by rfl) ⟨2194539, by rfl⟩ : syracuseStep 5852105 = 4389079) B4389079
theorem B3083231 : Blo 1825614 3083231 := bstep (se 1 (by rfl) ⟨2312423, by rfl⟩ : syracuseStep 3083231 = 4624847) B4624847
theorem B2739227 : Blo 1825614 2739227 := bstep (se 1 (by rfl) ⟨2054420, by rfl⟩ : syracuseStep 2739227 = 4108841) B4108841
theorem B3468415 : Blo 1825614 3468415 := bstep (se 1 (by rfl) ⟨2601311, by rfl⟩ : syracuseStep 3468415 = 5202623) B5202623
theorem B8899951 : Blo 1825614 8899951 := bstep (se 1 (by rfl) ⟨6674963, by rfl⟩ : syracuseStep 8899951 = 13349927) B13349927
theorem B2739767 : Blo 1825614 2739767 := bstep (se 1 (by rfl) ⟨2054825, by rfl⟩ : syracuseStep 2739767 = 4109651) B4109651
theorem B3084041 : Blo 1825614 3084041 := bstep (se 2 (by rfl) ⟨1156515, by rfl⟩ : syracuseStep 3084041 = 2313031) B2313031
theorem B6164315 : Blo 1825614 6164315 := bstep (se 1 (by rfl) ⟨4623236, by rfl⟩ : syracuseStep 6164315 = 9246473) B9246473
theorem B2740127 : Blo 1825614 2740127 := bstep (se 1 (by rfl) ⟨2055095, by rfl⟩ : syracuseStep 2740127 = 4110191) B4110191
theorem B2740217 : Blo 1825614 2740217 := bstep (se 2 (by rfl) ⟨1027581, by rfl⟩ : syracuseStep 2740217 = 2055163) B2055163
theorem B4624411 : Blo 1825614 4624411 := bstep (se 1 (by rfl) ⟨3468308, by rfl⟩ : syracuseStep 4624411 = 6936617) B6936617
theorem B4624523 : Blo 1825614 4624523 := bstep (se 1 (by rfl) ⟨3468392, by rfl⟩ : syracuseStep 4624523 = 6936785) B6936785
theorem B91353419 : Blo 1825614 91353419 := bstep (se 1 (by rfl) ⟨68515064, by rfl⟩ : syracuseStep 91353419 = 137030129) B137030129
theorem B4108715 : Blo 1825614 4108715 := bstep (se 1 (by rfl) ⟨3081536, by rfl⟩ : syracuseStep 4108715 = 6163073) B6163073
theorem B2740763 : Blo 1825614 2740763 := bstep (se 1 (by rfl) ⟨2055572, by rfl⟩ : syracuseStep 2740763 = 4111145) B4111145
theorem B13865579 : Blo 1825614 13865579 := bstep (se 1 (by rfl) ⟨10399184, by rfl⟩ : syracuseStep 13865579 = 20798369) B20798369
theorem B2740955 : Blo 1825614 2740955 := bstep (se 1 (by rfl) ⟨2055716, by rfl⟩ : syracuseStep 2740955 = 4111433) B4111433
theorem B9245825 : Blo 1825614 9245825 := bstep (se 2 (by rfl) ⟨3467184, by rfl⟩ : syracuseStep 9245825 = 6934369) B6934369
theorem B4109759 : Blo 1825614 4109759 := bstep (se 1 (by rfl) ⟨3082319, by rfl⟩ : syracuseStep 4109759 = 6164639) B6164639
theorem B20814407 : Blo 1825614 20814407 := bstep (se 1 (by rfl) ⟨15610805, by rfl⟩ : syracuseStep 20814407 = 31221611) B31221611
theorem B6167123 : Blo 1825614 6167123 := bstep (se 1 (by rfl) ⟨4625342, by rfl⟩ : syracuseStep 6167123 = 9250685) B9250685
theorem B23419853 : Blo 1825614 23419853 := bstep (se 3 (by rfl) ⟨4391222, by rfl⟩ : syracuseStep 23419853 = 8782445) B8782445
theorem B1825959 : Blo 1825614 1825959 := bstep (se 1 (by rfl) ⟨1369469, by rfl⟩ : syracuseStep 1825959 = 2738939) B2738939
theorem B1826031 : Blo 1825614 1826031 := bstep (se 1 (by rfl) ⟨1369523, by rfl⟩ : syracuseStep 1826031 = 2739047) B2739047
theorem B26345081 : Blo 1825614 26345081 := bstep (se 2 (by rfl) ⟨9879405, by rfl⟩ : syracuseStep 26345081 = 19758811) B19758811
theorem B4112063 : Blo 1825614 4112063 := bstep (se 1 (by rfl) ⟨3084047, by rfl⟩ : syracuseStep 4112063 = 6168095) B6168095
theorem B50085695 : Blo 1825614 50085695 := bstep (se 1 (by rfl) ⟨37564271, by rfl⟩ : syracuseStep 50085695 = 75128543) B75128543
theorem B11108495 : Blo 1825614 11108495 := bstep (se 1 (by rfl) ⟨8331371, by rfl⟩ : syracuseStep 11108495 = 16662743) B16662743
theorem B14057711 : Blo 1825614 14057711 := bstep (se 1 (by rfl) ⟨10543283, by rfl⟩ : syracuseStep 14057711 = 21086567) B21086567
theorem B1827175 : Blo 1825614 1827175 := bstep (se 1 (by rfl) ⟨1370381, by rfl⟩ : syracuseStep 1827175 = 2740763) B2740763
theorem B1827303 : Blo 1825614 1827303 := bstep (se 1 (by rfl) ⟨1370477, by rfl⟩ : syracuseStep 1827303 = 2740955) B2740955
theorem B70189577 : Blo 1825614 70189577 := bstep (se 2 (by rfl) ⟨26321091, by rfl⟩ : syracuseStep 70189577 = 52642183) B52642183
theorem B31212863 : Blo 1825614 31212863 := bstep (se 1 (by rfl) ⟨23409647, by rfl⟩ : syracuseStep 31212863 = 46819295) B46819295
theorem B6161993 : Blo 1825614 6161993 := bstep (se 2 (by rfl) ⟨2310747, by rfl⟩ : syracuseStep 6161993 = 4621495) B4621495
theorem B3081935 : Blo 1825614 3081935 := bstep (se 1 (by rfl) ⟨2311451, by rfl⟩ : syracuseStep 3081935 = 4622903) B4622903
theorem B7407335 : Blo 1825614 7407335 := bstep (se 1 (by rfl) ⟨5555501, by rfl⟩ : syracuseStep 7407335 = 11111003) B11111003
theorem B6162155 : Blo 1825614 6162155 := bstep (se 1 (by rfl) ⟨4621616, by rfl⟩ : syracuseStep 6162155 = 9243233) B9243233
theorem B3901403 : Blo 1825614 3901403 := bstep (se 1 (by rfl) ⟨2926052, by rfl⟩ : syracuseStep 3901403 = 5852105) B5852105
theorem B3083015 : Blo 1825614 3083015 := bstep (se 1 (by rfl) ⟨2312261, by rfl⟩ : syracuseStep 3083015 = 4624523) B4624523
theorem B7801697 : Blo 1825614 7801697 := bstep (se 2 (by rfl) ⟨2925636, by rfl⟩ : syracuseStep 7801697 = 5851273) B5851273
theorem B60902279 : Blo 1825614 60902279 := bstep (se 1 (by rfl) ⟨45676709, by rfl⟩ : syracuseStep 60902279 = 91353419) B91353419
theorem B2739143 : Blo 1825614 2739143 := bstep (se 1 (by rfl) ⟨2054357, by rfl⟩ : syracuseStep 2739143 = 4108715) B4108715
theorem B9243719 : Blo 1825614 9243719 := bstep (se 1 (by rfl) ⟨6932789, by rfl⟩ : syracuseStep 9243719 = 13865579) B13865579
theorem B9243881 : Blo 1825614 9243881 := bstep (se 2 (by rfl) ⟨3466455, by rfl⟩ : syracuseStep 9243881 = 6932911) B6932911
theorem B10399049 : Blo 1825614 10399049 := bstep (se 2 (by rfl) ⟨3899643, by rfl⟩ : syracuseStep 10399049 = 7799287) B7799287
theorem B6163883 : Blo 1825614 6163883 := bstep (se 1 (by rfl) ⟨4622912, by rfl⟩ : syracuseStep 6163883 = 9245825) B9245825
theorem B2739839 : Blo 1825614 2739839 := bstep (se 1 (by rfl) ⟨2054879, by rfl⟩ : syracuseStep 2739839 = 4109759) B4109759
theorem B4624553 : Blo 1825614 4624553 := bstep (se 2 (by rfl) ⟨1734207, by rfl⟩ : syracuseStep 4624553 = 3468415) B3468415
theorem B11866601 : Blo 1825614 11866601 := bstep (se 2 (by rfl) ⟨4449975, by rfl⟩ : syracuseStep 11866601 = 8899951) B8899951
theorem B31199741 : Blo 1825614 31199741 := bstep (se 3 (by rfl) ⟨5849951, by rfl⟩ : syracuseStep 31199741 = 11699903) B11699903
theorem B2741375 : Blo 1825614 2741375 := bstep (se 1 (by rfl) ⟨2056031, by rfl⟩ : syracuseStep 2741375 = 4112063) B4112063
theorem B4109543 : Blo 1825614 4109543 := bstep (se 1 (by rfl) ⟨3082157, by rfl⟩ : syracuseStep 4109543 = 6164315) B6164315
theorem B6165881 : Blo 1825614 6165881 := bstep (se 2 (by rfl) ⟨2312205, by rfl⟩ : syracuseStep 6165881 = 4624411) B4624411
theorem B9246311 : Blo 1825614 9246311 := bstep (se 1 (by rfl) ⟨6934733, by rfl⟩ : syracuseStep 9246311 = 13869467) B13869467
theorem B2054875 : Blo 1825614 2054875 := bstep (se 1 (by rfl) ⟨1541156, by rfl⟩ : syracuseStep 2054875 = 3082313) B3082313
theorem B13876271 : Blo 1825614 13876271 := bstep (se 1 (by rfl) ⟨10407203, by rfl⟩ : syracuseStep 13876271 = 20814407) B20814407
theorem B4111415 : Blo 1825614 4111415 := bstep (se 1 (by rfl) ⟨3083561, by rfl⟩ : syracuseStep 4111415 = 6167123) B6167123
theorem B15613235 : Blo 1825614 15613235 := bstep (se 1 (by rfl) ⟨11709926, by rfl⟩ : syracuseStep 15613235 = 23419853) B23419853
theorem B2055487 : Blo 1825614 2055487 := bstep (se 1 (by rfl) ⟨1541615, by rfl⟩ : syracuseStep 2055487 = 3083231) B3083231
theorem B1826151 : Blo 1825614 1826151 := bstep (se 1 (by rfl) ⟨1369613, by rfl⟩ : syracuseStep 1826151 = 2739227) B2739227
theorem B56254013 : Blo 1825614 56254013 := bstep (se 3 (by rfl) ⟨10547627, by rfl⟩ : syracuseStep 56254013 = 21095255) B21095255
theorem B1826511 : Blo 1825614 1826511 := bstep (se 1 (by rfl) ⟨1369883, by rfl⟩ : syracuseStep 1826511 = 2739767) B2739767
theorem B1386831581 : Blo 1825614 1386831581 := bstep (se 3 (by rfl) ⟨260030921, by rfl⟩ : syracuseStep 1386831581 = 520061843) B520061843
theorem B1826811 : Blo 1825614 1826811 := bstep (se 1 (by rfl) ⟨1370108, by rfl⟩ : syracuseStep 1826811 = 2740217) B2740217
theorem B17563387 : Blo 1825614 17563387 := bstep (se 1 (by rfl) ⟨13172540, by rfl⟩ : syracuseStep 17563387 = 26345081) B26345081
theorem B2056027 : Blo 1825614 2056027 := bstep (se 1 (by rfl) ⟨1542020, by rfl⟩ : syracuseStep 2056027 = 3084041) B3084041
theorem B33390463 : Blo 1825614 33390463 := bstep (se 1 (by rfl) ⟨25042847, by rfl⟩ : syracuseStep 33390463 = 50085695) B50085695
theorem B1826751 : Blo 1825614 1826751 := bstep (se 1 (by rfl) ⟨1370063, by rfl⟩ : syracuseStep 1826751 = 2740127) B2740127
theorem B7405663 : Blo 1825614 7405663 := bstep (se 1 (by rfl) ⟨5554247, by rfl⟩ : syracuseStep 7405663 = 11108495) B11108495
theorem B9371807 : Blo 1825614 9371807 := bstep (se 1 (by rfl) ⟨7028855, by rfl⟩ : syracuseStep 9371807 = 14057711) B14057711
theorem B20799827 : Blo 1825614 20799827 := bstep (se 1 (by rfl) ⟨15599870, by rfl⟩ : syracuseStep 20799827 = 31199741) B31199741
theorem B46793051 : Blo 1825614 46793051 := bstep (se 1 (by rfl) ⟨35094788, by rfl⟩ : syracuseStep 46793051 = 70189577) B70189577
theorem B1827583 : Blo 1825614 1827583 := bstep (se 1 (by rfl) ⟨1370687, by rfl⟩ : syracuseStep 1827583 = 2741375) B2741375
theorem B20808575 : Blo 1825614 20808575 := bstep (se 1 (by rfl) ⟨15606431, by rfl⟩ : syracuseStep 20808575 = 31212863) B31212863
theorem B40601519 : Blo 1825614 40601519 := bstep (se 1 (by rfl) ⟨30451139, by rfl⟩ : syracuseStep 40601519 = 60902279) B60902279
theorem B19752893 : Blo 1825614 19752893 := bstep (se 3 (by rfl) ⟨3703667, by rfl⟩ : syracuseStep 19752893 = 7407335) B7407335
theorem B9250847 : Blo 1825614 9250847 := bstep (se 1 (by rfl) ⟨6938135, by rfl⟩ : syracuseStep 9250847 = 13876271) B13876271
theorem B6162479 : Blo 1825614 6162479 := bstep (se 1 (by rfl) ⟨4621859, by rfl⟩ : syracuseStep 6162479 = 9243719) B9243719
theorem B6162587 : Blo 1825614 6162587 := bstep (se 1 (by rfl) ⟨4621940, by rfl⟩ : syracuseStep 6162587 = 9243881) B9243881
theorem B6932699 : Blo 1825614 6932699 := bstep (se 1 (by rfl) ⟨5199524, by rfl⟩ : syracuseStep 6932699 = 10399049) B10399049
theorem B3083035 : Blo 1825614 3083035 := bstep (se 1 (by rfl) ⟨2312276, by rfl⟩ : syracuseStep 3083035 = 4624553) B4624553
theorem B2739695 : Blo 1825614 2739695 := bstep (se 1 (by rfl) ⟨2054771, by rfl⟩ : syracuseStep 2739695 = 4109543) B4109543
theorem B2739833 : Blo 1825614 2739833 := bstep (se 2 (by rfl) ⟨1027437, by rfl⟩ : syracuseStep 2739833 = 2054875) B2054875
theorem B4107995 : Blo 1825614 4107995 := bstep (se 1 (by rfl) ⟨3080996, by rfl⟩ : syracuseStep 4107995 = 6161993) B6161993
theorem B6164207 : Blo 1825614 6164207 := bstep (se 1 (by rfl) ⟨4623155, by rfl⟩ : syracuseStep 6164207 = 9246311) B9246311
theorem B4108103 : Blo 1825614 4108103 := bstep (se 1 (by rfl) ⟨3081077, by rfl⟩ : syracuseStep 4108103 = 6162155) B6162155
theorem B2740649 : Blo 1825614 2740649 := bstep (se 2 (by rfl) ⟨1027743, by rfl⟩ : syracuseStep 2740649 = 2055487) B2055487
theorem B2740943 : Blo 1825614 2740943 := bstep (se 1 (by rfl) ⟨2055707, by rfl⟩ : syracuseStep 2740943 = 4111415) B4111415
theorem B10408823 : Blo 1825614 10408823 := bstep (se 1 (by rfl) ⟨7806617, by rfl⟩ : syracuseStep 10408823 = 15613235) B15613235
theorem B4109255 : Blo 1825614 4109255 := bstep (se 1 (by rfl) ⟨3081941, by rfl⟩ : syracuseStep 4109255 = 6163883) B6163883
theorem B23417849 : Blo 1825614 23417849 := bstep (se 2 (by rfl) ⟨8781693, by rfl⟩ : syracuseStep 23417849 = 17563387) B17563387
theorem B2741369 : Blo 1825614 2741369 := bstep (se 2 (by rfl) ⟨1028013, by rfl⟩ : syracuseStep 2741369 = 2056027) B2056027
theorem B924554387 : Blo 1825614 924554387 := bstep (se 1 (by rfl) ⟨693415790, by rfl⟩ : syracuseStep 924554387 = 1386831581) B1386831581
theorem B44520617 : Blo 1825614 44520617 := bstep (se 2 (by rfl) ⟨16695231, by rfl⟩ : syracuseStep 44520617 = 33390463) B33390463
theorem B7911067 : Blo 1825614 7911067 := bstep (se 1 (by rfl) ⟨5933300, by rfl⟩ : syracuseStep 7911067 = 11866601) B11866601
theorem B4110587 : Blo 1825614 4110587 := bstep (se 1 (by rfl) ⟨3082940, by rfl⟩ : syracuseStep 4110587 = 6165881) B6165881
theorem B2054623 : Blo 1825614 2054623 := bstep (se 1 (by rfl) ⟨1540967, by rfl⟩ : syracuseStep 2054623 = 3081935) B3081935
theorem B2055343 : Blo 1825614 2055343 := bstep (se 1 (by rfl) ⟨1541507, by rfl⟩ : syracuseStep 2055343 = 3083015) B3083015
theorem B5201131 : Blo 1825614 5201131 := bstep (se 1 (by rfl) ⟨3900848, by rfl⟩ : syracuseStep 5201131 = 7801697) B7801697
theorem B1826095 : Blo 1825614 1826095 := bstep (se 1 (by rfl) ⟨1369571, by rfl⟩ : syracuseStep 1826095 = 2739143) B2739143
theorem B37502675 : Blo 1825614 37502675 := bstep (se 1 (by rfl) ⟨28127006, by rfl⟩ : syracuseStep 37502675 = 56254013) B56254013
theorem B1826559 : Blo 1825614 1826559 := bstep (se 1 (by rfl) ⟨1369919, by rfl⟩ : syracuseStep 1826559 = 2739839) B2739839
theorem B10403741 : Blo 1825614 10403741 := bstep (se 3 (by rfl) ⟨1950701, by rfl⟩ : syracuseStep 10403741 = 3901403) B3901403
theorem B31195367 : Blo 1825614 31195367 := bstep (se 1 (by rfl) ⟨23396525, by rfl⟩ : syracuseStep 31195367 = 46793051) B46793051
theorem B1827099 : Blo 1825614 1827099 := bstep (se 1 (by rfl) ⟨1370324, by rfl⟩ : syracuseStep 1827099 = 2740649) B2740649
theorem B1827295 : Blo 1825614 1827295 := bstep (se 1 (by rfl) ⟨1370471, by rfl⟩ : syracuseStep 1827295 = 2740943) B2740943
theorem B6939215 : Blo 1825614 6939215 := bstep (se 1 (by rfl) ⟨5204411, by rfl⟩ : syracuseStep 6939215 = 10408823) B10408823
theorem B1827579 : Blo 1825614 1827579 := bstep (se 1 (by rfl) ⟨1370684, by rfl⟩ : syracuseStep 1827579 = 2741369) B2741369
theorem B29680411 : Blo 1825614 29680411 := bstep (se 1 (by rfl) ⟨22260308, by rfl⟩ : syracuseStep 29680411 = 44520617) B44520617
theorem B27067679 : Blo 1825614 27067679 := bstep (se 1 (by rfl) ⟨20300759, by rfl⟩ : syracuseStep 27067679 = 40601519) B40601519
theorem B4621799 : Blo 1825614 4621799 := bstep (se 1 (by rfl) ⟨3466349, by rfl⟩ : syracuseStep 4621799 = 6932699) B6932699
theorem B2738663 : Blo 1825614 2738663 := bstep (se 1 (by rfl) ⟨2053997, by rfl⟩ : syracuseStep 2738663 = 4107995) B4107995
theorem B2738735 : Blo 1825614 2738735 := bstep (se 1 (by rfl) ⟨2054051, by rfl⟩ : syracuseStep 2738735 = 4108103) B4108103
theorem B9874217 : Blo 1825614 9874217 := bstep (se 2 (by rfl) ⟨3702831, by rfl⟩ : syracuseStep 9874217 = 7405663) B7405663
theorem B13872383 : Blo 1825614 13872383 := bstep (se 1 (by rfl) ⟨10404287, by rfl⟩ : syracuseStep 13872383 = 20808575) B20808575
theorem B2739497 : Blo 1825614 2739497 := bstep (se 2 (by rfl) ⟨1027311, by rfl⟩ : syracuseStep 2739497 = 2054623) B2054623
theorem B2739503 : Blo 1825614 2739503 := bstep (se 1 (by rfl) ⟨2054627, by rfl⟩ : syracuseStep 2739503 = 4109255) B4109255
theorem B616369591 : Blo 1825614 616369591 := bstep (se 1 (by rfl) ⟨462277193, by rfl⟩ : syracuseStep 616369591 = 924554387) B924554387
theorem B13168595 : Blo 1825614 13168595 := bstep (se 1 (by rfl) ⟨9876446, by rfl⟩ : syracuseStep 13168595 = 19752893) B19752893
theorem B4108319 : Blo 1825614 4108319 := bstep (se 1 (by rfl) ⟨3081239, by rfl⟩ : syracuseStep 4108319 = 6162479) B6162479
theorem B4108391 : Blo 1825614 4108391 := bstep (se 1 (by rfl) ⟨3081293, by rfl⟩ : syracuseStep 4108391 = 6162587) B6162587
theorem B2740391 : Blo 1825614 2740391 := bstep (se 1 (by rfl) ⟨2055293, by rfl⟩ : syracuseStep 2740391 = 4110587) B4110587
theorem B2740457 : Blo 1825614 2740457 := bstep (se 2 (by rfl) ⟨1027671, by rfl⟩ : syracuseStep 2740457 = 2055343) B2055343
theorem B6934841 : Blo 1825614 6934841 := bstep (se 2 (by rfl) ⟨2600565, by rfl⟩ : syracuseStep 6934841 = 5201131) B5201131
theorem B10548089 : Blo 1825614 10548089 := bstep (se 2 (by rfl) ⟨3955533, by rfl⟩ : syracuseStep 10548089 = 7911067) B7911067
theorem B4109471 : Blo 1825614 4109471 := bstep (se 1 (by rfl) ⟨3082103, by rfl⟩ : syracuseStep 4109471 = 6164207) B6164207
theorem B6935827 : Blo 1825614 6935827 := bstep (se 1 (by rfl) ⟨5201870, by rfl⟩ : syracuseStep 6935827 = 10403741) B10403741
theorem B6247871 : Blo 1825614 6247871 := bstep (se 1 (by rfl) ⟨4685903, by rfl⟩ : syracuseStep 6247871 = 9371807) B9371807
theorem B13866551 : Blo 1825614 13866551 := bstep (se 1 (by rfl) ⟨10399913, by rfl⟩ : syracuseStep 13866551 = 20799827) B20799827
theorem B15611899 : Blo 1825614 15611899 := bstep (se 1 (by rfl) ⟨11708924, by rfl⟩ : syracuseStep 15611899 = 23417849) B23417849
theorem B4110713 : Blo 1825614 4110713 := bstep (se 2 (by rfl) ⟨1541517, by rfl⟩ : syracuseStep 4110713 = 3083035) B3083035
theorem B6167231 : Blo 1825614 6167231 := bstep (se 1 (by rfl) ⟨4625423, by rfl⟩ : syracuseStep 6167231 = 9250847) B9250847
theorem B1826463 : Blo 1825614 1826463 := bstep (se 1 (by rfl) ⟨1369847, by rfl⟩ : syracuseStep 1826463 = 2739695) B2739695
theorem B1826555 : Blo 1825614 1826555 := bstep (se 1 (by rfl) ⟨1369916, by rfl⟩ : syracuseStep 1826555 = 2739833) B2739833
theorem B25001783 : Blo 1825614 25001783 := bstep (se 1 (by rfl) ⟨18751337, by rfl⟩ : syracuseStep 25001783 = 37502675) B37502675
theorem B1826927 : Blo 1825614 1826927 := bstep (se 1 (by rfl) ⟨1370195, by rfl⟩ : syracuseStep 1826927 = 2740391) B2740391
theorem B1826971 : Blo 1825614 1826971 := bstep (se 1 (by rfl) ⟨1370228, by rfl⟩ : syracuseStep 1826971 = 2740457) B2740457
theorem B3081199 : Blo 1825614 3081199 := bstep (se 1 (by rfl) ⟨2310899, by rfl⟩ : syracuseStep 3081199 = 4621799) B4621799
theorem B2738879 : Blo 1825614 2738879 := bstep (se 1 (by rfl) ⟨2054159, by rfl⟩ : syracuseStep 2738879 = 4108319) B4108319
theorem B2738927 : Blo 1825614 2738927 := bstep (se 1 (by rfl) ⟨2054195, by rfl⟩ : syracuseStep 2738927 = 4108391) B4108391
theorem B4623227 : Blo 1825614 4623227 := bstep (se 1 (by rfl) ⟨3467420, by rfl⟩ : syracuseStep 4623227 = 6934841) B6934841
theorem B20815865 : Blo 1825614 20815865 := bstep (se 2 (by rfl) ⟨7805949, by rfl⟩ : syracuseStep 20815865 = 15611899) B15611899
theorem B7032059 : Blo 1825614 7032059 := bstep (se 1 (by rfl) ⟨5274044, by rfl⟩ : syracuseStep 7032059 = 10548089) B10548089
theorem B2739647 : Blo 1825614 2739647 := bstep (se 1 (by rfl) ⟨2054735, by rfl⟩ : syracuseStep 2739647 = 4109471) B4109471
theorem B4165247 : Blo 1825614 4165247 := bstep (se 1 (by rfl) ⟨3123935, by rfl⟩ : syracuseStep 4165247 = 6247871) B6247871
theorem B9244367 : Blo 1825614 9244367 := bstep (se 1 (by rfl) ⟨6933275, by rfl⟩ : syracuseStep 9244367 = 13866551) B13866551
theorem B2740475 : Blo 1825614 2740475 := bstep (se 1 (by rfl) ⟨2055356, by rfl⟩ : syracuseStep 2740475 = 4110713) B4110713
theorem B6582811 : Blo 1825614 6582811 := bstep (se 1 (by rfl) ⟨4937108, by rfl⟩ : syracuseStep 6582811 = 9874217) B9874217
theorem B821826121 : Blo 1825614 821826121 := bstep (se 2 (by rfl) ⟨308184795, by rfl⟩ : syracuseStep 821826121 = 616369591) B616369591
theorem B16667855 : Blo 1825614 16667855 := bstep (se 1 (by rfl) ⟨12500891, by rfl⟩ : syracuseStep 16667855 = 25001783) B25001783
theorem B8779063 : Blo 1825614 8779063 := bstep (se 1 (by rfl) ⟨6584297, by rfl⟩ : syracuseStep 8779063 = 13168595) B13168595
theorem B20796911 : Blo 1825614 20796911 := bstep (se 1 (by rfl) ⟨15597683, by rfl⟩ : syracuseStep 20796911 = 31195367) B31195367
theorem B4626143 : Blo 1825614 4626143 := bstep (se 1 (by rfl) ⟨3469607, by rfl⟩ : syracuseStep 4626143 = 6939215) B6939215
theorem B18045119 : Blo 1825614 18045119 := bstep (se 1 (by rfl) ⟨13533839, by rfl⟩ : syracuseStep 18045119 = 27067679) B27067679
theorem B39573881 : Blo 1825614 39573881 := bstep (se 2 (by rfl) ⟨14840205, by rfl⟩ : syracuseStep 39573881 = 29680411) B29680411
theorem B1825775 : Blo 1825614 1825775 := bstep (se 1 (by rfl) ⟨1369331, by rfl⟩ : syracuseStep 1825775 = 2738663) B2738663
theorem B9247769 : Blo 1825614 9247769 := bstep (se 2 (by rfl) ⟨3467913, by rfl⟩ : syracuseStep 9247769 = 6935827) B6935827
theorem B1825823 : Blo 1825614 1825823 := bstep (se 1 (by rfl) ⟨1369367, by rfl⟩ : syracuseStep 1825823 = 2738735) B2738735
theorem B4111487 : Blo 1825614 4111487 := bstep (se 1 (by rfl) ⟨3083615, by rfl⟩ : syracuseStep 4111487 = 6167231) B6167231
theorem B9248255 : Blo 1825614 9248255 := bstep (se 1 (by rfl) ⟨6936191, by rfl⟩ : syracuseStep 9248255 = 13872383) B13872383
theorem B1826331 : Blo 1825614 1826331 := bstep (se 1 (by rfl) ⟨1369748, by rfl⟩ : syracuseStep 1826331 = 2739497) B2739497
theorem B1826335 : Blo 1825614 1826335 := bstep (se 1 (by rfl) ⟨1369751, by rfl⟩ : syracuseStep 1826335 = 2739503) B2739503
theorem B1826983 : Blo 1825614 1826983 := bstep (se 1 (by rfl) ⟨1370237, by rfl⟩ : syracuseStep 1826983 = 2740475) B2740475
theorem B48120317 : Blo 1825614 48120317 := bstep (se 3 (by rfl) ⟨9022559, by rfl⟩ : syracuseStep 48120317 = 18045119) B18045119
theorem B3082151 : Blo 1825614 3082151 := bstep (se 1 (by rfl) ⟨2311613, by rfl⟩ : syracuseStep 3082151 = 4623227) B4623227
theorem B4688039 : Blo 1825614 4688039 := bstep (se 1 (by rfl) ⟨3516029, by rfl⟩ : syracuseStep 4688039 = 7032059) B7032059
theorem B6162911 : Blo 1825614 6162911 := bstep (se 1 (by rfl) ⟨4622183, by rfl⟩ : syracuseStep 6162911 = 9244367) B9244367
theorem B8777081 : Blo 1825614 8777081 := bstep (se 2 (by rfl) ⟨3291405, by rfl⟩ : syracuseStep 8777081 = 6582811) B6582811
theorem B11111903 : Blo 1825614 11111903 := bstep (se 1 (by rfl) ⟨8333927, by rfl⟩ : syracuseStep 11111903 = 16667855) B16667855
theorem B13864607 : Blo 1825614 13864607 := bstep (se 1 (by rfl) ⟨10398455, by rfl⟩ : syracuseStep 13864607 = 20796911) B20796911
theorem B3084095 : Blo 1825614 3084095 := bstep (se 1 (by rfl) ⟨2313071, by rfl⟩ : syracuseStep 3084095 = 4626143) B4626143
theorem B4108265 : Blo 1825614 4108265 := bstep (se 2 (by rfl) ⟨1540599, by rfl⟩ : syracuseStep 4108265 = 3081199) B3081199
theorem B26382587 : Blo 1825614 26382587 := bstep (se 1 (by rfl) ⟨19786940, by rfl⟩ : syracuseStep 26382587 = 39573881) B39573881
theorem B6165179 : Blo 1825614 6165179 := bstep (se 1 (by rfl) ⟨4623884, by rfl⟩ : syracuseStep 6165179 = 9247769) B9247769
theorem B2740991 : Blo 1825614 2740991 := bstep (se 1 (by rfl) ⟨2055743, by rfl⟩ : syracuseStep 2740991 = 4111487) B4111487
theorem B6165503 : Blo 1825614 6165503 := bstep (se 1 (by rfl) ⟨4624127, by rfl⟩ : syracuseStep 6165503 = 9248255) B9248255
theorem B1095768161 : Blo 1825614 1095768161 := bstep (se 2 (by rfl) ⟨410913060, by rfl⟩ : syracuseStep 1095768161 = 821826121) B821826121
theorem B11107325 : Blo 1825614 11107325 := bstep (se 3 (by rfl) ⟨2082623, by rfl⟩ : syracuseStep 11107325 = 4165247) B4165247
theorem B11705417 : Blo 1825614 11705417 := bstep (se 2 (by rfl) ⟨4389531, by rfl⟩ : syracuseStep 11705417 = 8779063) B8779063
theorem B1825919 : Blo 1825614 1825919 := bstep (se 1 (by rfl) ⟨1369439, by rfl⟩ : syracuseStep 1825919 = 2738879) B2738879
theorem B1825951 : Blo 1825614 1825951 := bstep (se 1 (by rfl) ⟨1369463, by rfl⟩ : syracuseStep 1825951 = 2738927) B2738927
theorem B13877243 : Blo 1825614 13877243 := bstep (se 1 (by rfl) ⟨10407932, by rfl⟩ : syracuseStep 13877243 = 20815865) B20815865
theorem B1826431 : Blo 1825614 1826431 := bstep (se 1 (by rfl) ⟨1369823, by rfl⟩ : syracuseStep 1826431 = 2739647) B2739647
theorem B32080211 : Blo 1825614 32080211 := bstep (se 1 (by rfl) ⟨24060158, by rfl⟩ : syracuseStep 32080211 = 48120317) B48120317
theorem B1827327 : Blo 1825614 1827327 := bstep (se 1 (by rfl) ⟨1370495, by rfl⟩ : syracuseStep 1827327 = 2740991) B2740991
theorem B5851387 : Blo 1825614 5851387 := bstep (se 1 (by rfl) ⟨4388540, by rfl⟩ : syracuseStep 5851387 = 8777081) B8777081
theorem B7407935 : Blo 1825614 7407935 := bstep (se 1 (by rfl) ⟨5555951, by rfl⟩ : syracuseStep 7407935 = 11111903) B11111903
theorem B9243071 : Blo 1825614 9243071 := bstep (se 1 (by rfl) ⟨6932303, by rfl⟩ : syracuseStep 9243071 = 13864607) B13864607
theorem B281414261 : Blo 1825614 281414261 := bstep (se 5 (by rfl) ⟨13191293, by rfl⟩ : syracuseStep 281414261 = 26382587) B26382587
theorem B2738843 : Blo 1825614 2738843 := bstep (se 1 (by rfl) ⟨2054132, by rfl⟩ : syracuseStep 2738843 = 4108265) B4108265
theorem B9251495 : Blo 1825614 9251495 := bstep (se 1 (by rfl) ⟨6938621, by rfl⟩ : syracuseStep 9251495 = 13877243) B13877243
theorem B3125359 : Blo 1825614 3125359 := bstep (se 1 (by rfl) ⟨2344019, by rfl⟩ : syracuseStep 3125359 = 4688039) B4688039
theorem B4108607 : Blo 1825614 4108607 := bstep (se 1 (by rfl) ⟨3081455, by rfl⟩ : syracuseStep 4108607 = 6162911) B6162911
theorem B7803611 : Blo 1825614 7803611 := bstep (se 1 (by rfl) ⟨5852708, by rfl⟩ : syracuseStep 7803611 = 11705417) B11705417
theorem B29619533 : Blo 1825614 29619533 := bstep (se 3 (by rfl) ⟨5553662, by rfl⟩ : syracuseStep 29619533 = 11107325) B11107325
theorem B4110119 : Blo 1825614 4110119 := bstep (se 1 (by rfl) ⟨3082589, by rfl⟩ : syracuseStep 4110119 = 6165179) B6165179
theorem B4110335 : Blo 1825614 4110335 := bstep (se 1 (by rfl) ⟨3082751, by rfl⟩ : syracuseStep 4110335 = 6165503) B6165503
theorem B2054767 : Blo 1825614 2054767 := bstep (se 1 (by rfl) ⟨1541075, by rfl⟩ : syracuseStep 2054767 = 3082151) B3082151
theorem B730512107 : Blo 1825614 730512107 := bstep (se 1 (by rfl) ⟨547884080, by rfl⟩ : syracuseStep 730512107 = 1095768161) B1095768161
theorem B2056063 : Blo 1825614 2056063 := bstep (se 1 (by rfl) ⟨1542047, by rfl⟩ : syracuseStep 2056063 = 3084095) B3084095
theorem B5202407 : Blo 1825614 5202407 := bstep (se 1 (by rfl) ⟨3901805, by rfl⟩ : syracuseStep 5202407 = 7803611) B7803611
theorem B6162047 : Blo 1825614 6162047 := bstep (se 1 (by rfl) ⟨4621535, by rfl⟩ : syracuseStep 6162047 = 9243071) B9243071
theorem B487008071 : Blo 1825614 487008071 := bstep (se 1 (by rfl) ⟨365256053, by rfl⟩ : syracuseStep 487008071 = 730512107) B730512107
theorem B2739071 : Blo 1825614 2739071 := bstep (se 1 (by rfl) ⟨2054303, by rfl⟩ : syracuseStep 2739071 = 4108607) B4108607
theorem B7801849 : Blo 1825614 7801849 := bstep (se 2 (by rfl) ⟨2925693, by rfl⟩ : syracuseStep 7801849 = 5851387) B5851387
theorem B2739689 : Blo 1825614 2739689 := bstep (se 2 (by rfl) ⟨1027383, by rfl⟩ : syracuseStep 2739689 = 2054767) B2054767
theorem B19746355 : Blo 1825614 19746355 := bstep (se 1 (by rfl) ⟨14809766, by rfl⟩ : syracuseStep 19746355 = 29619533) B29619533
theorem B2740079 : Blo 1825614 2740079 := bstep (se 1 (by rfl) ⟨2055059, by rfl⟩ : syracuseStep 2740079 = 4110119) B4110119
theorem B2740223 : Blo 1825614 2740223 := bstep (se 1 (by rfl) ⟨2055167, by rfl⟩ : syracuseStep 2740223 = 4110335) B4110335
theorem B187609507 : Blo 1825614 187609507 := bstep (se 1 (by rfl) ⟨140707130, by rfl⟩ : syracuseStep 187609507 = 281414261) B281414261
theorem B2741417 : Blo 1825614 2741417 := bstep (se 2 (by rfl) ⟨1028031, by rfl⟩ : syracuseStep 2741417 = 2056063) B2056063
theorem B4167145 : Blo 1825614 4167145 := bstep (se 2 (by rfl) ⟨1562679, by rfl⟩ : syracuseStep 4167145 = 3125359) B3125359
theorem B21386807 : Blo 1825614 21386807 := bstep (se 1 (by rfl) ⟨16040105, by rfl⟩ : syracuseStep 21386807 = 32080211) B32080211
theorem B4938623 : Blo 1825614 4938623 := bstep (se 1 (by rfl) ⟨3703967, by rfl⟩ : syracuseStep 4938623 = 7407935) B7407935
theorem B1825895 : Blo 1825614 1825895 := bstep (se 1 (by rfl) ⟨1369421, by rfl⟩ : syracuseStep 1825895 = 2738843) B2738843
theorem B6167663 : Blo 1825614 6167663 := bstep (se 1 (by rfl) ⟨4625747, by rfl⟩ : syracuseStep 6167663 = 9251495) B9251495
theorem B1827611 : Blo 1825614 1827611 := bstep (se 1 (by rfl) ⟨1370708, by rfl⟩ : syracuseStep 1827611 = 2741417) B2741417
theorem B3468271 : Blo 1825614 3468271 := bstep (se 1 (by rfl) ⟨2601203, by rfl⟩ : syracuseStep 3468271 = 5202407) B5202407
theorem B14257871 : Blo 1825614 14257871 := bstep (se 1 (by rfl) ⟨10693403, by rfl⟩ : syracuseStep 14257871 = 21386807) B21386807
theorem B4108031 : Blo 1825614 4108031 := bstep (se 1 (by rfl) ⟨3081023, by rfl⟩ : syracuseStep 4108031 = 6162047) B6162047
theorem B1000584037 : Blo 1825614 1000584037 := bstep (se 4 (by rfl) ⟨93804753, by rfl⟩ : syracuseStep 1000584037 = 187609507) B187609507
theorem B324672047 : Blo 1825614 324672047 := bstep (se 1 (by rfl) ⟨243504035, by rfl⟩ : syracuseStep 324672047 = 487008071) B487008071
theorem B10402465 : Blo 1825614 10402465 := bstep (se 2 (by rfl) ⟨3900924, by rfl⟩ : syracuseStep 10402465 = 7801849) B7801849
theorem B1826047 : Blo 1825614 1826047 := bstep (se 1 (by rfl) ⟨1369535, by rfl⟩ : syracuseStep 1826047 = 2739071) B2739071
theorem B3292415 : Blo 1825614 3292415 := bstep (se 1 (by rfl) ⟨2469311, by rfl⟩ : syracuseStep 3292415 = 4938623) B4938623
theorem B26328473 : Blo 1825614 26328473 := bstep (se 2 (by rfl) ⟨9873177, by rfl⟩ : syracuseStep 26328473 = 19746355) B19746355
theorem B4111775 : Blo 1825614 4111775 := bstep (se 1 (by rfl) ⟨3083831, by rfl⟩ : syracuseStep 4111775 = 6167663) B6167663
theorem B1826459 : Blo 1825614 1826459 := bstep (se 1 (by rfl) ⟨1369844, by rfl⟩ : syracuseStep 1826459 = 2739689) B2739689
theorem B22224773 : Blo 1825614 22224773 := bstep (se 4 (by rfl) ⟨2083572, by rfl⟩ : syracuseStep 22224773 = 4167145) B4167145
theorem B1826719 : Blo 1825614 1826719 := bstep (se 1 (by rfl) ⟨1370039, by rfl⟩ : syracuseStep 1826719 = 2740079) B2740079
theorem B1826815 : Blo 1825614 1826815 := bstep (se 1 (by rfl) ⟨1370111, by rfl⟩ : syracuseStep 1826815 = 2740223) B2740223
theorem B13869953 : Blo 1825614 13869953 := bstep (se 2 (by rfl) ⟨5201232, by rfl⟩ : syracuseStep 13869953 = 10402465) B10402465
theorem B9505247 : Blo 1825614 9505247 := bstep (se 1 (by rfl) ⟨7128935, by rfl⟩ : syracuseStep 9505247 = 14257871) B14257871
theorem B2738687 : Blo 1825614 2738687 := bstep (se 1 (by rfl) ⟨2054015, by rfl⟩ : syracuseStep 2738687 = 4108031) B4108031
theorem B1334112049 : Blo 1825614 1334112049 := bstep (se 2 (by rfl) ⟨500292018, by rfl⟩ : syracuseStep 1334112049 = 1000584037) B1000584037
theorem B4624361 : Blo 1825614 4624361 := bstep (se 2 (by rfl) ⟨1734135, by rfl⟩ : syracuseStep 4624361 = 3468271) B3468271
theorem B17552315 : Blo 1825614 17552315 := bstep (se 1 (by rfl) ⟨13164236, by rfl⟩ : syracuseStep 17552315 = 26328473) B26328473
theorem B2741183 : Blo 1825614 2741183 := bstep (se 1 (by rfl) ⟨2055887, by rfl⟩ : syracuseStep 2741183 = 4111775) B4111775
theorem B14816515 : Blo 1825614 14816515 := bstep (se 1 (by rfl) ⟨11112386, by rfl⟩ : syracuseStep 14816515 = 22224773) B22224773
theorem B216448031 : Blo 1825614 216448031 := bstep (se 1 (by rfl) ⟨162336023, by rfl⟩ : syracuseStep 216448031 = 324672047) B324672047
theorem B2194943 : Blo 1825614 2194943 := bstep (se 1 (by rfl) ⟨1646207, by rfl⟩ : syracuseStep 2194943 = 3292415) B3292415
theorem B1827455 : Blo 1825614 1827455 := bstep (se 1 (by rfl) ⟨1370591, by rfl⟩ : syracuseStep 1827455 = 2741183) B2741183
theorem B25347325 : Blo 1825614 25347325 := bstep (se 3 (by rfl) ⟨4752623, by rfl⟩ : syracuseStep 25347325 = 9505247) B9505247
theorem B3082907 : Blo 1825614 3082907 := bstep (se 1 (by rfl) ⟨2312180, by rfl⟩ : syracuseStep 3082907 = 4624361) B4624361
theorem B577194749 : Blo 1825614 577194749 := bstep (se 3 (by rfl) ⟨108224015, by rfl⟩ : syracuseStep 577194749 = 216448031) B216448031
theorem B19755353 : Blo 1825614 19755353 := bstep (se 2 (by rfl) ⟨7408257, by rfl⟩ : syracuseStep 19755353 = 14816515) B14816515
theorem B1778816065 : Blo 1825614 1778816065 := bstep (se 2 (by rfl) ⟨667056024, by rfl⟩ : syracuseStep 1778816065 = 1334112049) B1334112049
theorem B46806173 : Blo 1825614 46806173 := bstep (se 3 (by rfl) ⟨8776157, by rfl⟩ : syracuseStep 46806173 = 17552315) B17552315
theorem B9246635 : Blo 1825614 9246635 := bstep (se 1 (by rfl) ⟨6934976, by rfl⟩ : syracuseStep 9246635 = 13869953) B13869953
theorem B1825791 : Blo 1825614 1825791 := bstep (se 1 (by rfl) ⟨1369343, by rfl⟩ : syracuseStep 1825791 = 2738687) B2738687
theorem B23412725 : Blo 1825614 23412725 := bstep (se 5 (by rfl) ⟨1097471, by rfl⟩ : syracuseStep 23412725 = 2194943) B2194943
theorem B31204115 : Blo 1825614 31204115 := bstep (se 1 (by rfl) ⟨23403086, by rfl⟩ : syracuseStep 31204115 = 46806173) B46806173
theorem B384796499 : Blo 1825614 384796499 := bstep (se 1 (by rfl) ⟨288597374, by rfl⟩ : syracuseStep 384796499 = 577194749) B577194749
theorem B15608483 : Blo 1825614 15608483 := bstep (se 1 (by rfl) ⟨11706362, by rfl⟩ : syracuseStep 15608483 = 23412725) B23412725
theorem B6164423 : Blo 1825614 6164423 := bstep (se 1 (by rfl) ⟨4623317, by rfl⟩ : syracuseStep 6164423 = 9246635) B9246635
theorem B33796433 : Blo 1825614 33796433 := bstep (se 2 (by rfl) ⟨12673662, by rfl⟩ : syracuseStep 33796433 = 25347325) B25347325
theorem B13170235 : Blo 1825614 13170235 := bstep (se 1 (by rfl) ⟨9877676, by rfl⟩ : syracuseStep 13170235 = 19755353) B19755353
theorem B2371754753 : Blo 1825614 2371754753 := bstep (se 2 (by rfl) ⟨889408032, by rfl⟩ : syracuseStep 2371754753 = 1778816065) B1778816065
theorem B2055271 : Blo 1825614 2055271 := bstep (se 1 (by rfl) ⟨1541453, by rfl⟩ : syracuseStep 2055271 = 3082907) B3082907
theorem B4104495989 : Blo 1825614 4104495989 := bstep (se 5 (by rfl) ⟨192398249, by rfl⟩ : syracuseStep 4104495989 = 384796499) B384796499
theorem B10405655 : Blo 1825614 10405655 := bstep (se 1 (by rfl) ⟨7804241, by rfl⟩ : syracuseStep 10405655 = 15608483) B15608483
theorem B22530955 : Blo 1825614 22530955 := bstep (se 1 (by rfl) ⟨16898216, by rfl⟩ : syracuseStep 22530955 = 33796433) B33796433
theorem B20802743 : Blo 1825614 20802743 := bstep (se 1 (by rfl) ⟨15602057, by rfl⟩ : syracuseStep 20802743 = 31204115) B31204115
theorem B2740361 : Blo 1825614 2740361 := bstep (se 2 (by rfl) ⟨1027635, by rfl⟩ : syracuseStep 2740361 = 2055271) B2055271
theorem B17560313 : Blo 1825614 17560313 := bstep (se 2 (by rfl) ⟨6585117, by rfl⟩ : syracuseStep 17560313 = 13170235) B13170235
theorem B4109615 : Blo 1825614 4109615 := bstep (se 1 (by rfl) ⟨3082211, by rfl⟩ : syracuseStep 4109615 = 6164423) B6164423
theorem B1581169835 : Blo 1825614 1581169835 := bstep (se 1 (by rfl) ⟨1185877376, by rfl⟩ : syracuseStep 1581169835 = 2371754753) B2371754753
theorem B1826907 : Blo 1825614 1826907 := bstep (se 1 (by rfl) ⟨1370180, by rfl⟩ : syracuseStep 1826907 = 2740361) B2740361
theorem B11706875 : Blo 1825614 11706875 := bstep (se 1 (by rfl) ⟨8780156, by rfl⟩ : syracuseStep 11706875 = 17560313) B17560313
theorem B30041273 : Blo 1825614 30041273 := bstep (se 2 (by rfl) ⟨11265477, by rfl⟩ : syracuseStep 30041273 = 22530955) B22530955
theorem B2739743 : Blo 1825614 2739743 := bstep (se 1 (by rfl) ⟨2054807, by rfl⟩ : syracuseStep 2739743 = 4109615) B4109615
theorem B4216452893 : Blo 1825614 4216452893 := bstep (se 3 (by rfl) ⟨790584917, by rfl⟩ : syracuseStep 4216452893 = 1581169835) B1581169835
theorem B2736330659 : Blo 1825614 2736330659 := bstep (se 1 (by rfl) ⟨2052247994, by rfl⟩ : syracuseStep 2736330659 = 4104495989) B4104495989
theorem B6937103 : Blo 1825614 6937103 := bstep (se 1 (by rfl) ⟨5202827, by rfl⟩ : syracuseStep 6937103 = 10405655) B10405655
theorem B13868495 : Blo 1825614 13868495 := bstep (se 1 (by rfl) ⟨10401371, by rfl⟩ : syracuseStep 13868495 = 20802743) B20802743
theorem B80110061 : Blo 1825614 80110061 := bstep (se 3 (by rfl) ⟨15020636, by rfl⟩ : syracuseStep 80110061 = 30041273) B30041273
theorem B1824220439 : Blo 1825614 1824220439 := bstep (se 1 (by rfl) ⟨1368165329, by rfl⟩ : syracuseStep 1824220439 = 2736330659) B2736330659
theorem B4624735 : Blo 1825614 4624735 := bstep (se 1 (by rfl) ⟨3468551, by rfl⟩ : syracuseStep 4624735 = 6937103) B6937103
theorem B9245663 : Blo 1825614 9245663 := bstep (se 1 (by rfl) ⟨6934247, by rfl⟩ : syracuseStep 9245663 = 13868495) B13868495
theorem B7804583 : Blo 1825614 7804583 := bstep (se 1 (by rfl) ⟨5853437, by rfl⟩ : syracuseStep 7804583 = 11706875) B11706875
theorem B2810968595 : Blo 1825614 2810968595 := bstep (se 1 (by rfl) ⟨2108226446, by rfl⟩ : syracuseStep 2810968595 = 4216452893) B4216452893
theorem B1826495 : Blo 1825614 1826495 := bstep (se 1 (by rfl) ⟨1369871, by rfl⟩ : syracuseStep 1826495 = 2739743) B2739743
theorem B5203055 : Blo 1825614 5203055 := bstep (se 1 (by rfl) ⟨3902291, by rfl⟩ : syracuseStep 5203055 = 7804583) B7804583
theorem B1873979063 : Blo 1825614 1873979063 := bstep (se 1 (by rfl) ⟨1405484297, by rfl⟩ : syracuseStep 1873979063 = 2810968595) B2810968595
theorem B53406707 : Blo 1825614 53406707 := bstep (se 1 (by rfl) ⟨40055030, by rfl⟩ : syracuseStep 53406707 = 80110061) B80110061
theorem B6163775 : Blo 1825614 6163775 := bstep (se 1 (by rfl) ⟨4622831, by rfl⟩ : syracuseStep 6163775 = 9245663) B9245663
theorem B1216146959 : Blo 1825614 1216146959 := bstep (se 1 (by rfl) ⟨912110219, by rfl⟩ : syracuseStep 1216146959 = 1824220439) B1824220439
theorem B6166313 : Blo 1825614 6166313 := bstep (se 2 (by rfl) ⟨2312367, by rfl⟩ : syracuseStep 6166313 = 4624735) B4624735
theorem B810764639 : Blo 1825614 810764639 := bstep (se 1 (by rfl) ⟨608073479, by rfl⟩ : syracuseStep 810764639 = 1216146959) B1216146959
theorem B4109183 : Blo 1825614 4109183 := bstep (se 1 (by rfl) ⟨3081887, by rfl⟩ : syracuseStep 4109183 = 6163775) B6163775
theorem B13874813 : Blo 1825614 13874813 := bstep (se 3 (by rfl) ⟨2601527, by rfl⟩ : syracuseStep 13874813 = 5203055) B5203055
theorem B1249319375 : Blo 1825614 1249319375 := bstep (se 1 (by rfl) ⟨936989531, by rfl⟩ : syracuseStep 1249319375 = 1873979063) B1873979063
theorem B4110875 : Blo 1825614 4110875 := bstep (se 1 (by rfl) ⟨3083156, by rfl⟩ : syracuseStep 4110875 = 6166313) B6166313
theorem B142417885 : Blo 1825614 142417885 := bstep (se 3 (by rfl) ⟨26703353, by rfl⟩ : syracuseStep 142417885 = 53406707) B53406707
theorem B9249875 : Blo 1825614 9249875 := bstep (se 1 (by rfl) ⟨6937406, by rfl⟩ : syracuseStep 9249875 = 13874813) B13874813
theorem B540509759 : Blo 1825614 540509759 := bstep (se 1 (by rfl) ⟨405382319, by rfl⟩ : syracuseStep 540509759 = 810764639) B810764639
theorem B2739455 : Blo 1825614 2739455 := bstep (se 1 (by rfl) ⟨2054591, by rfl⟩ : syracuseStep 2739455 = 4109183) B4109183
theorem B2740583 : Blo 1825614 2740583 := bstep (se 1 (by rfl) ⟨2055437, by rfl⟩ : syracuseStep 2740583 = 4110875) B4110875
theorem B832879583 : Blo 1825614 832879583 := bstep (se 1 (by rfl) ⟨624659687, by rfl⟩ : syracuseStep 832879583 = 1249319375) B1249319375
theorem B189890513 : Blo 1825614 189890513 := bstep (se 2 (by rfl) ⟨71208942, by rfl⟩ : syracuseStep 189890513 = 142417885) B142417885
theorem B1827055 : Blo 1825614 1827055 := bstep (se 1 (by rfl) ⟨1370291, by rfl⟩ : syracuseStep 1827055 = 2740583) B2740583
theorem B126593675 : Blo 1825614 126593675 := bstep (se 1 (by rfl) ⟨94945256, by rfl⟩ : syracuseStep 126593675 = 189890513) B189890513
theorem B6166583 : Blo 1825614 6166583 := bstep (se 1 (by rfl) ⟨4624937, by rfl⟩ : syracuseStep 6166583 = 9249875) B9249875
theorem B360339839 : Blo 1825614 360339839 := bstep (se 1 (by rfl) ⟨270254879, by rfl⟩ : syracuseStep 360339839 = 540509759) B540509759
theorem B555253055 : Blo 1825614 555253055 := bstep (se 1 (by rfl) ⟨416439791, by rfl⟩ : syracuseStep 555253055 = 832879583) B832879583
theorem B1826303 : Blo 1825614 1826303 := bstep (se 1 (by rfl) ⟨1369727, by rfl⟩ : syracuseStep 1826303 = 2739455) B2739455
theorem B84395783 : Blo 1825614 84395783 := bstep (se 1 (by rfl) ⟨63296837, by rfl⟩ : syracuseStep 84395783 = 126593675) B126593675
theorem B240226559 : Blo 1825614 240226559 := bstep (se 1 (by rfl) ⟨180169919, by rfl⟩ : syracuseStep 240226559 = 360339839) B360339839
theorem B370168703 : Blo 1825614 370168703 := bstep (se 1 (by rfl) ⟨277626527, by rfl⟩ : syracuseStep 370168703 = 555253055) B555253055
theorem B4111055 : Blo 1825614 4111055 := bstep (se 1 (by rfl) ⟨3083291, by rfl⟩ : syracuseStep 4111055 = 6166583) B6166583
theorem B246779135 : Blo 1825614 246779135 := bstep (se 1 (by rfl) ⟨185084351, by rfl⟩ : syracuseStep 246779135 = 370168703) B370168703
theorem B2740703 : Blo 1825614 2740703 := bstep (se 1 (by rfl) ⟨2055527, by rfl⟩ : syracuseStep 2740703 = 4111055) B4111055
theorem B225055421 : Blo 1825614 225055421 := bstep (se 3 (by rfl) ⟨42197891, by rfl⟩ : syracuseStep 225055421 = 84395783) B84395783
theorem B160151039 : Blo 1825614 160151039 := bstep (se 1 (by rfl) ⟨120113279, by rfl⟩ : syracuseStep 160151039 = 240226559) B240226559
theorem B1827135 : Blo 1825614 1827135 := bstep (se 1 (by rfl) ⟨1370351, by rfl⟩ : syracuseStep 1827135 = 2740703) B2740703
theorem B150036947 : Blo 1825614 150036947 := bstep (se 1 (by rfl) ⟨112527710, by rfl⟩ : syracuseStep 150036947 = 225055421) B225055421
theorem B106767359 : Blo 1825614 106767359 := bstep (se 1 (by rfl) ⟨80075519, by rfl⟩ : syracuseStep 106767359 = 160151039) B160151039
theorem B164519423 : Blo 1825614 164519423 := bstep (se 1 (by rfl) ⟨123389567, by rfl⟩ : syracuseStep 164519423 = 246779135) B246779135
theorem B100024631 : Blo 1825614 100024631 := bstep (se 1 (by rfl) ⟨75018473, by rfl⟩ : syracuseStep 100024631 = 150036947) B150036947
theorem B109679615 : Blo 1825614 109679615 := bstep (se 1 (by rfl) ⟨82259711, by rfl⟩ : syracuseStep 109679615 = 164519423) B164519423
theorem B71178239 : Blo 1825614 71178239 := bstep (se 1 (by rfl) ⟨53383679, by rfl⟩ : syracuseStep 71178239 = 106767359) B106767359
theorem B66683087 : Blo 1825614 66683087 := bstep (se 1 (by rfl) ⟨50012315, by rfl⟩ : syracuseStep 66683087 = 100024631) B100024631
theorem B47452159 : Blo 1825614 47452159 := bstep (se 1 (by rfl) ⟨35589119, by rfl⟩ : syracuseStep 47452159 = 71178239) B71178239
theorem B73119743 : Blo 1825614 73119743 := bstep (se 1 (by rfl) ⟨54839807, by rfl⟩ : syracuseStep 73119743 = 109679615) B109679615
theorem B63269545 : Blo 1825614 63269545 := bstep (se 2 (by rfl) ⟨23726079, by rfl⟩ : syracuseStep 63269545 = 47452159) B47452159
theorem B48746495 : Blo 1825614 48746495 := bstep (se 1 (by rfl) ⟨36559871, by rfl⟩ : syracuseStep 48746495 = 73119743) B73119743
theorem B44455391 : Blo 1825614 44455391 := bstep (se 1 (by rfl) ⟨33341543, by rfl⟩ : syracuseStep 44455391 = 66683087) B66683087
theorem B84359393 : Blo 1825614 84359393 := bstep (se 2 (by rfl) ⟨31634772, by rfl⟩ : syracuseStep 84359393 = 63269545) B63269545
theorem B29636927 : Blo 1825614 29636927 := bstep (se 1 (by rfl) ⟨22227695, by rfl⟩ : syracuseStep 29636927 = 44455391) B44455391
theorem B129990653 : Blo 1825614 129990653 := bstep (se 3 (by rfl) ⟨24373247, by rfl⟩ : syracuseStep 129990653 = 48746495) B48746495
theorem B56239595 : Blo 1825614 56239595 := bstep (se 1 (by rfl) ⟨42179696, by rfl⟩ : syracuseStep 56239595 = 84359393) B84359393
theorem B86660435 : Blo 1825614 86660435 := bstep (se 1 (by rfl) ⟨64995326, by rfl⟩ : syracuseStep 86660435 = 129990653) B129990653
theorem B19757951 : Blo 1825614 19757951 := bstep (se 1 (by rfl) ⟨14818463, by rfl⟩ : syracuseStep 19757951 = 29636927) B29636927
theorem B57773623 : Blo 1825614 57773623 := bstep (se 1 (by rfl) ⟨43330217, by rfl⟩ : syracuseStep 57773623 = 86660435) B86660435
theorem B37493063 : Blo 1825614 37493063 := bstep (se 1 (by rfl) ⟨28119797, by rfl⟩ : syracuseStep 37493063 = 56239595) B56239595
theorem B13171967 : Blo 1825614 13171967 := bstep (se 1 (by rfl) ⟨9878975, by rfl⟩ : syracuseStep 13171967 = 19757951) B19757951
theorem B24995375 : Blo 1825614 24995375 := bstep (se 1 (by rfl) ⟨18746531, by rfl⟩ : syracuseStep 24995375 = 37493063) B37493063
theorem B77031497 : Blo 1825614 77031497 := bstep (se 2 (by rfl) ⟨28886811, by rfl⟩ : syracuseStep 77031497 = 57773623) B57773623
theorem B8781311 : Blo 1825614 8781311 := bstep (se 1 (by rfl) ⟨6585983, by rfl⟩ : syracuseStep 8781311 = 13171967) B13171967
theorem B16663583 : Blo 1825614 16663583 := bstep (se 1 (by rfl) ⟨12497687, by rfl⟩ : syracuseStep 16663583 = 24995375) B24995375
theorem B5854207 : Blo 1825614 5854207 := bstep (se 1 (by rfl) ⟨4390655, by rfl⟩ : syracuseStep 5854207 = 8781311) B8781311
theorem B51354331 : Blo 1825614 51354331 := bstep (se 1 (by rfl) ⟨38515748, by rfl⟩ : syracuseStep 51354331 = 77031497) B77031497
theorem B11109055 : Blo 1825614 11109055 := bstep (se 1 (by rfl) ⟨8331791, by rfl⟩ : syracuseStep 11109055 = 16663583) B16663583
theorem B273889765 : Blo 1825614 273889765 := bstep (se 4 (by rfl) ⟨25677165, by rfl⟩ : syracuseStep 273889765 = 51354331) B51354331
theorem B7805609 : Blo 1825614 7805609 := bstep (se 2 (by rfl) ⟨2927103, by rfl⟩ : syracuseStep 7805609 = 5854207) B5854207
theorem B14812073 : Blo 1825614 14812073 := bstep (se 2 (by rfl) ⟨5554527, by rfl⟩ : syracuseStep 14812073 = 11109055) B11109055
theorem B5203739 : Blo 1825614 5203739 := bstep (se 1 (by rfl) ⟨3902804, by rfl⟩ : syracuseStep 5203739 = 7805609) B7805609
theorem B365186353 : Blo 1825614 365186353 := bstep (se 2 (by rfl) ⟨136944882, by rfl⟩ : syracuseStep 365186353 = 273889765) B273889765
theorem B9874715 : Blo 1825614 9874715 := bstep (se 1 (by rfl) ⟨7406036, by rfl⟩ : syracuseStep 9874715 = 14812073) B14812073
theorem B3469159 : Blo 1825614 3469159 := bstep (se 1 (by rfl) ⟨2601869, by rfl⟩ : syracuseStep 3469159 = 5203739) B5203739
theorem B486915137 : Blo 1825614 486915137 := bstep (se 2 (by rfl) ⟨182593176, by rfl⟩ : syracuseStep 486915137 = 365186353) B365186353
theorem B324610091 : Blo 1825614 324610091 := bstep (se 1 (by rfl) ⟨243457568, by rfl⟩ : syracuseStep 324610091 = 486915137) B486915137
theorem B26332573 : Blo 1825614 26332573 := bstep (se 3 (by rfl) ⟨4937357, by rfl⟩ : syracuseStep 26332573 = 9874715) B9874715
theorem B4625545 : Blo 1825614 4625545 := bstep (se 2 (by rfl) ⟨1734579, by rfl⟩ : syracuseStep 4625545 = 3469159) B3469159
theorem B216406727 : Blo 1825614 216406727 := bstep (se 1 (by rfl) ⟨162305045, by rfl⟩ : syracuseStep 216406727 = 324610091) B324610091
theorem B6167393 : Blo 1825614 6167393 := bstep (se 2 (by rfl) ⟨2312772, by rfl⟩ : syracuseStep 6167393 = 4625545) B4625545
theorem B35110097 : Blo 1825614 35110097 := bstep (se 2 (by rfl) ⟨13166286, by rfl⟩ : syracuseStep 35110097 = 26332573) B26332573
theorem B144271151 : Blo 1825614 144271151 := bstep (se 1 (by rfl) ⟨108203363, by rfl⟩ : syracuseStep 144271151 = 216406727) B216406727
theorem B23406731 : Blo 1825614 23406731 := bstep (se 1 (by rfl) ⟨17555048, by rfl⟩ : syracuseStep 23406731 = 35110097) B35110097
theorem B4111595 : Blo 1825614 4111595 := bstep (se 1 (by rfl) ⟨3083696, by rfl⟩ : syracuseStep 4111595 = 6167393) B6167393
theorem B2741063 : Blo 1825614 2741063 := bstep (se 1 (by rfl) ⟨2055797, by rfl⟩ : syracuseStep 2741063 = 4111595) B4111595
theorem B96180767 : Blo 1825614 96180767 := bstep (se 1 (by rfl) ⟨72135575, by rfl⟩ : syracuseStep 96180767 = 144271151) B144271151
theorem B15604487 : Blo 1825614 15604487 := bstep (se 1 (by rfl) ⟨11703365, by rfl⟩ : syracuseStep 15604487 = 23406731) B23406731
theorem B1827375 : Blo 1825614 1827375 := bstep (se 1 (by rfl) ⟨1370531, by rfl⟩ : syracuseStep 1827375 = 2741063) B2741063
theorem B64120511 : Blo 1825614 64120511 := bstep (se 1 (by rfl) ⟨48090383, by rfl⟩ : syracuseStep 64120511 = 96180767) B96180767
theorem B10402991 : Blo 1825614 10402991 := bstep (se 1 (by rfl) ⟨7802243, by rfl⟩ : syracuseStep 10402991 = 15604487) B15604487
theorem B42747007 : Blo 1825614 42747007 := bstep (se 1 (by rfl) ⟨32060255, by rfl⟩ : syracuseStep 42747007 = 64120511) B64120511
theorem B6935327 : Blo 1825614 6935327 := bstep (se 1 (by rfl) ⟨5201495, by rfl⟩ : syracuseStep 6935327 = 10402991) B10402991
theorem B4623551 : Blo 1825614 4623551 := bstep (se 1 (by rfl) ⟨3467663, by rfl⟩ : syracuseStep 4623551 = 6935327) B6935327
theorem B56996009 : Blo 1825614 56996009 := bstep (se 2 (by rfl) ⟨21373503, by rfl⟩ : syracuseStep 56996009 = 42747007) B42747007
theorem B3082367 : Blo 1825614 3082367 := bstep (se 1 (by rfl) ⟨2311775, by rfl⟩ : syracuseStep 3082367 = 4623551) B4623551
theorem B607957429 : Blo 1825614 607957429 := bstep (se 5 (by rfl) ⟨28498004, by rfl⟩ : syracuseStep 607957429 = 56996009) B56996009
theorem B810609905 : Blo 1825614 810609905 := bstep (se 2 (by rfl) ⟨303978714, by rfl⟩ : syracuseStep 810609905 = 607957429) B607957429
theorem B2054911 : Blo 1825614 2054911 := bstep (se 1 (by rfl) ⟨1541183, by rfl⟩ : syracuseStep 2054911 = 3082367) B3082367
theorem B2739881 : Blo 1825614 2739881 := bstep (se 2 (by rfl) ⟨1027455, by rfl⟩ : syracuseStep 2739881 = 2054911) B2054911
theorem B540406603 : Blo 1825614 540406603 := bstep (se 1 (by rfl) ⟨405304952, by rfl⟩ : syracuseStep 540406603 = 810609905) B810609905
theorem B720542137 : Blo 1825614 720542137 := bstep (se 2 (by rfl) ⟨270203301, by rfl⟩ : syracuseStep 720542137 = 540406603) B540406603
theorem B1826587 : Blo 1825614 1826587 := bstep (se 1 (by rfl) ⟨1369940, by rfl⟩ : syracuseStep 1826587 = 2739881) B2739881
theorem B960722849 : Blo 1825614 960722849 := bstep (se 2 (by rfl) ⟨360271068, by rfl⟩ : syracuseStep 960722849 = 720542137) B720542137
theorem B640481899 : Blo 1825614 640481899 := bstep (se 1 (by rfl) ⟨480361424, by rfl⟩ : syracuseStep 640481899 = 960722849) B960722849
theorem B853975865 : Blo 1825614 853975865 := bstep (se 2 (by rfl) ⟨320240949, by rfl⟩ : syracuseStep 853975865 = 640481899) B640481899
theorem B569317243 : Blo 1825614 569317243 := bstep (se 1 (by rfl) ⟨426987932, by rfl⟩ : syracuseStep 569317243 = 853975865) B853975865
theorem B759089657 : Blo 1825614 759089657 := bstep (se 2 (by rfl) ⟨284658621, by rfl⟩ : syracuseStep 759089657 = 569317243) B569317243
theorem B506059771 : Blo 1825614 506059771 := bstep (se 1 (by rfl) ⟨379544828, by rfl⟩ : syracuseStep 506059771 = 759089657) B759089657
theorem B674746361 : Blo 1825614 674746361 := bstep (se 2 (by rfl) ⟨253029885, by rfl⟩ : syracuseStep 674746361 = 506059771) B506059771
theorem B449830907 : Blo 1825614 449830907 := bstep (se 1 (by rfl) ⟨337373180, by rfl⟩ : syracuseStep 449830907 = 674746361) B674746361
theorem B299887271 : Blo 1825614 299887271 := bstep (se 1 (by rfl) ⟨224915453, by rfl⟩ : syracuseStep 299887271 = 449830907) B449830907
theorem B199924847 : Blo 1825614 199924847 := bstep (se 1 (by rfl) ⟨149943635, by rfl⟩ : syracuseStep 199924847 = 299887271) B299887271
theorem B133283231 : Blo 1825614 133283231 := bstep (se 1 (by rfl) ⟨99962423, by rfl⟩ : syracuseStep 133283231 = 199924847) B199924847
theorem B88855487 : Blo 1825614 88855487 := bstep (se 1 (by rfl) ⟨66641615, by rfl⟩ : syracuseStep 88855487 = 133283231) B133283231
theorem B59236991 : Blo 1825614 59236991 := bstep (se 1 (by rfl) ⟨44427743, by rfl⟩ : syracuseStep 59236991 = 88855487) B88855487
theorem B39491327 : Blo 1825614 39491327 := bstep (se 1 (by rfl) ⟨29618495, by rfl⟩ : syracuseStep 39491327 = 59236991) B59236991
theorem B26327551 : Blo 1825614 26327551 := bstep (se 1 (by rfl) ⟨19745663, by rfl⟩ : syracuseStep 26327551 = 39491327) B39491327
theorem B35103401 : Blo 1825614 35103401 := bstep (se 2 (by rfl) ⟨13163775, by rfl⟩ : syracuseStep 35103401 = 26327551) B26327551
theorem B23402267 : Blo 1825614 23402267 := bstep (se 1 (by rfl) ⟨17551700, by rfl⟩ : syracuseStep 23402267 = 35103401) B35103401
theorem B15601511 : Blo 1825614 15601511 := bstep (se 1 (by rfl) ⟨11701133, by rfl⟩ : syracuseStep 15601511 = 23402267) B23402267
theorem B10401007 : Blo 1825614 10401007 := bstep (se 1 (by rfl) ⟨7800755, by rfl⟩ : syracuseStep 10401007 = 15601511) B15601511
theorem B13868009 : Blo 1825614 13868009 := bstep (se 2 (by rfl) ⟨5200503, by rfl⟩ : syracuseStep 13868009 = 10401007) B10401007
theorem B9245339 : Blo 1825614 9245339 := bstep (se 1 (by rfl) ⟨6934004, by rfl⟩ : syracuseStep 9245339 = 13868009) B13868009
theorem B6163559 : Blo 1825614 6163559 := bstep (se 1 (by rfl) ⟨4622669, by rfl⟩ : syracuseStep 6163559 = 9245339) B9245339
theorem B4109039 : Blo 1825614 4109039 := bstep (se 1 (by rfl) ⟨3081779, by rfl⟩ : syracuseStep 4109039 = 6163559) B6163559
theorem B2739359 : Blo 1825614 2739359 := bstep (se 1 (by rfl) ⟨2054519, by rfl⟩ : syracuseStep 2739359 = 4109039) B4109039
theorem B1826239 : Blo 1825614 1826239 := bstep (se 1 (by rfl) ⟨1369679, by rfl⟩ : syracuseStep 1826239 = 2739359) B2739359

theorem C0 (j : ℕ) (h1 : 456403 ≤ j) (h2 : j ≤ 456902) : Blo 1825614 (4 * j + 3) := by
  interval_cases j
  · exact B1825615
  · exact B1825619
  · exact B1825623
  · exact B1825627
  · exact B1825631
  · exact B1825635
  · exact B1825639
  · exact B1825643
  · exact B1825647
  · exact B1825651
  · exact B1825655
  · exact B1825659
  · exact B1825663
  · exact B1825667
  · exact B1825671
  · exact B1825675
  · exact B1825679
  · exact B1825683
  · exact B1825687
  · exact B1825691
  · exact B1825695
  · exact B1825699
  · exact B1825703
  · exact B1825707
  · exact B1825711
  · exact B1825715
  · exact B1825719
  · exact B1825723
  · exact B1825727
  · exact B1825731
  · exact B1825735
  · exact B1825739
  · exact B1825743
  · exact B1825747
  · exact B1825751
  · exact B1825755
  · exact B1825759
  · exact B1825763
  · exact B1825767
  · exact B1825771
  · exact B1825775
  · exact B1825779
  · exact B1825783
  · exact B1825787
  · exact B1825791
  · exact B1825795
  · exact B1825799
  · exact B1825803
  · exact B1825807
  · exact B1825811
  · exact B1825815
  · exact B1825819
  · exact B1825823
  · exact B1825827
  · exact B1825831
  · exact B1825835
  · exact B1825839
  · exact B1825843
  · exact B1825847
  · exact B1825851
  · exact B1825855
  · exact B1825859
  · exact B1825863
  · exact B1825867
  · exact B1825871
  · exact B1825875
  · exact B1825879
  · exact B1825883
  · exact B1825887
  · exact B1825891
  · exact B1825895
  · exact B1825899
  · exact B1825903
  · exact B1825907
  · exact B1825911
  · exact B1825915
  · exact B1825919
  · exact B1825923
  · exact B1825927
  · exact B1825931
  · exact B1825935
  · exact B1825939
  · exact B1825943
  · exact B1825947
  · exact B1825951
  · exact B1825955
  · exact B1825959
  · exact B1825963
  · exact B1825967
  · exact B1825971
  · exact B1825975
  · exact B1825979
  · exact B1825983
  · exact B1825987
  · exact B1825991
  · exact B1825995
  · exact B1825999
  · exact B1826003
  · exact B1826007
  · exact B1826011
  · exact B1826015
  · exact B1826019
  · exact B1826023
  · exact B1826027
  · exact B1826031
  · exact B1826035
  · exact B1826039
  · exact B1826043
  · exact B1826047
  · exact B1826051
  · exact B1826055
  · exact B1826059
  · exact B1826063
  · exact B1826067
  · exact B1826071
  · exact B1826075
  · exact B1826079
  · exact B1826083
  · exact B1826087
  · exact B1826091
  · exact B1826095
  · exact B1826099
  · exact B1826103
  · exact B1826107
  · exact B1826111
  · exact B1826115
  · exact B1826119
  · exact B1826123
  · exact B1826127
  · exact B1826131
  · exact B1826135
  · exact B1826139
  · exact B1826143
  · exact B1826147
  · exact B1826151
  · exact B1826155
  · exact B1826159
  · exact B1826163
  · exact B1826167
  · exact B1826171
  · exact B1826175
  · exact B1826179
  · exact B1826183
  · exact B1826187
  · exact B1826191
  · exact B1826195
  · exact B1826199
  · exact B1826203
  · exact B1826207
  · exact B1826211
  · exact B1826215
  · exact B1826219
  · exact B1826223
  · exact B1826227
  · exact B1826231
  · exact B1826235
  · exact B1826239
  · exact B1826243
  · exact B1826247
  · exact B1826251
  · exact B1826255
  · exact B1826259
  · exact B1826263
  · exact B1826267
  · exact B1826271
  · exact B1826275
  · exact B1826279
  · exact B1826283
  · exact B1826287
  · exact B1826291
  · exact B1826295
  · exact B1826299
  · exact B1826303
  · exact B1826307
  · exact B1826311
  · exact B1826315
  · exact B1826319
  · exact B1826323
  · exact B1826327
  · exact B1826331
  · exact B1826335
  · exact B1826339
  · exact B1826343
  · exact B1826347
  · exact B1826351
  · exact B1826355
  · exact B1826359
  · exact B1826363
  · exact B1826367
  · exact B1826371
  · exact B1826375
  · exact B1826379
  · exact B1826383
  · exact B1826387
  · exact B1826391
  · exact B1826395
  · exact B1826399
  · exact B1826403
  · exact B1826407
  · exact B1826411
  · exact B1826415
  · exact B1826419
  · exact B1826423
  · exact B1826427
  · exact B1826431
  · exact B1826435
  · exact B1826439
  · exact B1826443
  · exact B1826447
  · exact B1826451
  · exact B1826455
  · exact B1826459
  · exact B1826463
  · exact B1826467
  · exact B1826471
  · exact B1826475
  · exact B1826479
  · exact B1826483
  · exact B1826487
  · exact B1826491
  · exact B1826495
  · exact B1826499
  · exact B1826503
  · exact B1826507
  · exact B1826511
  · exact B1826515
  · exact B1826519
  · exact B1826523
  · exact B1826527
  · exact B1826531
  · exact B1826535
  · exact B1826539
  · exact B1826543
  · exact B1826547
  · exact B1826551
  · exact B1826555
  · exact B1826559
  · exact B1826563
  · exact B1826567
  · exact B1826571
  · exact B1826575
  · exact B1826579
  · exact B1826583
  · exact B1826587
  · exact B1826591
  · exact B1826595
  · exact B1826599
  · exact B1826603
  · exact B1826607
  · exact B1826611
  · exact B1826615
  · exact B1826619
  · exact B1826623
  · exact B1826627
  · exact B1826631
  · exact B1826635
  · exact B1826639
  · exact B1826643
  · exact B1826647
  · exact B1826651
  · exact B1826655
  · exact B1826659
  · exact B1826663
  · exact B1826667
  · exact B1826671
  · exact B1826675
  · exact B1826679
  · exact B1826683
  · exact B1826687
  · exact B1826691
  · exact B1826695
  · exact B1826699
  · exact B1826703
  · exact B1826707
  · exact B1826711
  · exact B1826715
  · exact B1826719
  · exact B1826723
  · exact B1826727
  · exact B1826731
  · exact B1826735
  · exact B1826739
  · exact B1826743
  · exact B1826747
  · exact B1826751
  · exact B1826755
  · exact B1826759
  · exact B1826763
  · exact B1826767
  · exact B1826771
  · exact B1826775
  · exact B1826779
  · exact B1826783
  · exact B1826787
  · exact B1826791
  · exact B1826795
  · exact B1826799
  · exact B1826803
  · exact B1826807
  · exact B1826811
  · exact B1826815
  · exact B1826819
  · exact B1826823
  · exact B1826827
  · exact B1826831
  · exact B1826835
  · exact B1826839
  · exact B1826843
  · exact B1826847
  · exact B1826851
  · exact B1826855
  · exact B1826859
  · exact B1826863
  · exact B1826867
  · exact B1826871
  · exact B1826875
  · exact B1826879
  · exact B1826883
  · exact B1826887
  · exact B1826891
  · exact B1826895
  · exact B1826899
  · exact B1826903
  · exact B1826907
  · exact B1826911
  · exact B1826915
  · exact B1826919
  · exact B1826923
  · exact B1826927
  · exact B1826931
  · exact B1826935
  · exact B1826939
  · exact B1826943
  · exact B1826947
  · exact B1826951
  · exact B1826955
  · exact B1826959
  · exact B1826963
  · exact B1826967
  · exact B1826971
  · exact B1826975
  · exact B1826979
  · exact B1826983
  · exact B1826987
  · exact B1826991
  · exact B1826995
  · exact B1826999
  · exact B1827003
  · exact B1827007
  · exact B1827011
  · exact B1827015
  · exact B1827019
  · exact B1827023
  · exact B1827027
  · exact B1827031
  · exact B1827035
  · exact B1827039
  · exact B1827043
  · exact B1827047
  · exact B1827051
  · exact B1827055
  · exact B1827059
  · exact B1827063
  · exact B1827067
  · exact B1827071
  · exact B1827075
  · exact B1827079
  · exact B1827083
  · exact B1827087
  · exact B1827091
  · exact B1827095
  · exact B1827099
  · exact B1827103
  · exact B1827107
  · exact B1827111
  · exact B1827115
  · exact B1827119
  · exact B1827123
  · exact B1827127
  · exact B1827131
  · exact B1827135
  · exact B1827139
  · exact B1827143
  · exact B1827147
  · exact B1827151
  · exact B1827155
  · exact B1827159
  · exact B1827163
  · exact B1827167
  · exact B1827171
  · exact B1827175
  · exact B1827179
  · exact B1827183
  · exact B1827187
  · exact B1827191
  · exact B1827195
  · exact B1827199
  · exact B1827203
  · exact B1827207
  · exact B1827211
  · exact B1827215
  · exact B1827219
  · exact B1827223
  · exact B1827227
  · exact B1827231
  · exact B1827235
  · exact B1827239
  · exact B1827243
  · exact B1827247
  · exact B1827251
  · exact B1827255
  · exact B1827259
  · exact B1827263
  · exact B1827267
  · exact B1827271
  · exact B1827275
  · exact B1827279
  · exact B1827283
  · exact B1827287
  · exact B1827291
  · exact B1827295
  · exact B1827299
  · exact B1827303
  · exact B1827307
  · exact B1827311
  · exact B1827315
  · exact B1827319
  · exact B1827323
  · exact B1827327
  · exact B1827331
  · exact B1827335
  · exact B1827339
  · exact B1827343
  · exact B1827347
  · exact B1827351
  · exact B1827355
  · exact B1827359
  · exact B1827363
  · exact B1827367
  · exact B1827371
  · exact B1827375
  · exact B1827379
  · exact B1827383
  · exact B1827387
  · exact B1827391
  · exact B1827395
  · exact B1827399
  · exact B1827403
  · exact B1827407
  · exact B1827411
  · exact B1827415
  · exact B1827419
  · exact B1827423
  · exact B1827427
  · exact B1827431
  · exact B1827435
  · exact B1827439
  · exact B1827443
  · exact B1827447
  · exact B1827451
  · exact B1827455
  · exact B1827459
  · exact B1827463
  · exact B1827467
  · exact B1827471
  · exact B1827475
  · exact B1827479
  · exact B1827483
  · exact B1827487
  · exact B1827491
  · exact B1827495
  · exact B1827499
  · exact B1827503
  · exact B1827507
  · exact B1827511
  · exact B1827515
  · exact B1827519
  · exact B1827523
  · exact B1827527
  · exact B1827531
  · exact B1827535
  · exact B1827539
  · exact B1827543
  · exact B1827547
  · exact B1827551
  · exact B1827555
  · exact B1827559
  · exact B1827563
  · exact B1827567
  · exact B1827571
  · exact B1827575
  · exact B1827579
  · exact B1827583
  · exact B1827587
  · exact B1827591
  · exact B1827595
  · exact B1827599
  · exact B1827603
  · exact B1827607
  · exact B1827611

theorem solution (m : ℕ) (hlo : 1825614 ≤ m) (hhi : m ≤ 1827614) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 456403 ≤ j := by omega
    have hj2 : j ≤ 456902 := by omega
    have hb : Blo 1825614 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
