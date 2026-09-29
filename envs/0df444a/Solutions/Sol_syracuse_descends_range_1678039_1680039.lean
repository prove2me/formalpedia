-- Prove2me | solution 1 for syracuse_descends_range_1678039_1680039
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:22:02.942114+00:00
-- url     : https://prove2.me/submissions/c9b88976-f546-4a1e-b4a4-b4df200a196b

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


theorem B3776525 : Blo 1678039 3776525 := bbase (se 3 (by rfl) ⟨708098, by rfl⟩ : syracuseStep 3776525 = 1416197) (by norm_num)
theorem B2834453 : Blo 1678039 2834453 := bbase (se 6 (by rfl) ⟨66432, by rfl⟩ : syracuseStep 2834453 = 132865) (by norm_num)
theorem B3588133 : Blo 1678039 3588133 := bbase (se 4 (by rfl) ⟨336387, by rfl⟩ : syracuseStep 3588133 = 672775) (by norm_num)
theorem B16146485 : Blo 1678039 16146485 := bbase (se 5 (by rfl) ⟨756866, by rfl⟩ : syracuseStep 16146485 = 1513733) (by norm_num)
theorem B3776597 : Blo 1678039 3776597 := bbase (se 8 (by rfl) ⟨22128, by rfl⟩ : syracuseStep 3776597 = 44257) (by norm_num)
theorem B4145237 : Blo 1678039 4145237 := bbase (se 8 (by rfl) ⟨24288, by rfl⟩ : syracuseStep 4145237 = 48577) (by norm_num)
theorem B6373525 : Blo 1678039 6373525 := bbase (se 6 (by rfl) ⟨149379, by rfl⟩ : syracuseStep 6373525 = 298759) (by norm_num)
theorem B2834581 : Blo 1678039 2834581 := bbase (se 6 (by rfl) ⟨66435, by rfl⟩ : syracuseStep 2834581 = 132871) (by norm_num)
theorem B3776669 : Blo 1678039 3776669 := bbase (se 3 (by rfl) ⟨708125, by rfl⟩ : syracuseStep 3776669 = 1416251) (by norm_num)
theorem B3186877 : Blo 1678039 3186877 := bbase (se 3 (by rfl) ⟨597539, by rfl⟩ : syracuseStep 3186877 = 1195079) (by norm_num)
theorem B3776741 : Blo 1678039 3776741 := bbase (se 4 (by rfl) ⟨354069, by rfl⟩ : syracuseStep 3776741 = 708139) (by norm_num)
theorem B2834669 : Blo 1678039 2834669 := bbase (se 3 (by rfl) ⟨531500, by rfl⟩ : syracuseStep 2834669 = 1063001) (by norm_num)
theorem B8503541 : Blo 1678039 8503541 := bbase (se 5 (by rfl) ⟨398603, by rfl⟩ : syracuseStep 8503541 = 797207) (by norm_num)
theorem B3776813 : Blo 1678039 3776813 := bbase (se 3 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 3776813 = 1416305) (by norm_num)
theorem B4538693 : Blo 1678039 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B5669189 : Blo 1678039 5669189 := bbase (se 4 (by rfl) ⟨531486, by rfl⟩ : syracuseStep 5669189 = 1062973) (by norm_num)
theorem B4251973 : Blo 1678039 4251973 := bbase (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) (by norm_num)
theorem B3187021 : Blo 1678039 3187021 := bbase (se 3 (by rfl) ⟨597566, by rfl⟩ : syracuseStep 3187021 = 1195133) (by norm_num)
theorem B2834797 : Blo 1678039 2834797 := bbase (se 3 (by rfl) ⟨531524, by rfl⟩ : syracuseStep 2834797 = 1063049) (by norm_num)
theorem B3776885 : Blo 1678039 3776885 := bbase (se 5 (by rfl) ⟨177041, by rfl⟩ : syracuseStep 3776885 = 354083) (by norm_num)
theorem B4252085 : Blo 1678039 4252085 := bbase (se 5 (by rfl) ⟨199316, by rfl⟩ : syracuseStep 4252085 = 398633) (by norm_num)
theorem B3776957 : Blo 1678039 3776957 := bbase (se 3 (by rfl) ⟨708179, by rfl⟩ : syracuseStep 3776957 = 1416359) (by norm_num)
theorem B6373829 : Blo 1678039 6373829 := bbase (se 4 (by rfl) ⟨597546, by rfl⟩ : syracuseStep 6373829 = 1195093) (by norm_num)
theorem B2834885 : Blo 1678039 2834885 := bbase (se 4 (by rfl) ⟨265770, by rfl⟩ : syracuseStep 2834885 = 531541) (by norm_num)
theorem B2154973 : Blo 1678039 2154973 := bbase (se 3 (by rfl) ⟨404057, by rfl⟩ : syracuseStep 2154973 = 808115) (by norm_num)
theorem B3187181 : Blo 1678039 3187181 := bbase (se 3 (by rfl) ⟨597596, by rfl⟩ : syracuseStep 3187181 = 1195193) (by norm_num)
theorem B3777029 : Blo 1678039 3777029 := bbase (se 4 (by rfl) ⟨354096, by rfl⟩ : syracuseStep 3777029 = 708193) (by norm_num)
theorem B2835013 : Blo 1678039 2835013 := bbase (se 4 (by rfl) ⟨265782, by rfl⟩ : syracuseStep 2835013 = 531565) (by norm_num)
theorem B3777101 : Blo 1678039 3777101 := bbase (se 3 (by rfl) ⟨708206, by rfl⟩ : syracuseStep 3777101 = 1416413) (by norm_num)
theorem B4252277 : Blo 1678039 4252277 := bbase (se 5 (by rfl) ⟨199325, by rfl⟩ : syracuseStep 4252277 = 398651) (by norm_num)
theorem B3187325 : Blo 1678039 3187325 := bbase (se 3 (by rfl) ⟨597623, by rfl⟩ : syracuseStep 3187325 = 1195247) (by norm_num)
theorem B10486421 : Blo 1678039 10486421 := bbase (se 6 (by rfl) ⟨245775, by rfl⟩ : syracuseStep 10486421 = 491551) (by norm_num)
theorem B8495765 : Blo 1678039 8495765 := bbase (se 6 (by rfl) ⟨199119, by rfl⟩ : syracuseStep 8495765 = 398239) (by norm_num)
theorem B3777173 : Blo 1678039 3777173 := bbase (se 6 (by rfl) ⟨88527, by rfl⟩ : syracuseStep 3777173 = 177055) (by norm_num)
theorem B13607605 : Blo 1678039 13607605 := bbase (se 5 (by rfl) ⟨637856, by rfl⟩ : syracuseStep 13607605 = 1275713) (by norm_num)
theorem B3777245 : Blo 1678039 3777245 := bbase (se 3 (by rfl) ⟨708233, by rfl⟩ : syracuseStep 3777245 = 1416467) (by norm_num)
theorem B13607669 : Blo 1678039 13607669 := bbase (se 5 (by rfl) ⟨637859, by rfl⟩ : syracuseStep 13607669 = 1275719) (by norm_num)
theorem B5669621 : Blo 1678039 5669621 := bbase (se 5 (by rfl) ⟨265763, by rfl⟩ : syracuseStep 5669621 = 531527) (by norm_num)
theorem B3777317 : Blo 1678039 3777317 := bbase (se 4 (by rfl) ⟨354123, by rfl⟩ : syracuseStep 3777317 = 708247) (by norm_num)
theorem B220930901 : Blo 1678039 220930901 := bbase (se 9 (by rfl) ⟨647258, by rfl⟩ : syracuseStep 220930901 = 1294517) (by norm_num)
theorem B3777389 : Blo 1678039 3777389 := bbase (se 3 (by rfl) ⟨708260, by rfl⟩ : syracuseStep 3777389 = 1416521) (by norm_num)
theorem B13607797 : Blo 1678039 13607797 := bbase (se 5 (by rfl) ⟨637865, by rfl⟩ : syracuseStep 13607797 = 1275731) (by norm_num)
theorem B20423573 : Blo 1678039 20423573 := bbase (se 6 (by rfl) ⟨478677, by rfl⟩ : syracuseStep 20423573 = 957355) (by norm_num)
theorem B3187613 : Blo 1678039 3187613 := bbase (se 3 (by rfl) ⟨597677, by rfl⟩ : syracuseStep 3187613 = 1195355) (by norm_num)
theorem B3777461 : Blo 1678039 3777461 := bbase (se 5 (by rfl) ⟨177068, by rfl⟩ : syracuseStep 3777461 = 354137) (by norm_num)
theorem B3777533 : Blo 1678039 3777533 := bbase (se 3 (by rfl) ⟨708287, by rfl⟩ : syracuseStep 3777533 = 1416575) (by norm_num)
theorem B6464549 : Blo 1678039 6464549 := bbase (se 4 (by rfl) ⟨606051, by rfl⟩ : syracuseStep 6464549 = 1212103) (by norm_num)
theorem B3187765 : Blo 1678039 3187765 := bbase (se 5 (by rfl) ⟨149426, by rfl⟩ : syracuseStep 3187765 = 298853) (by norm_num)
theorem B3777605 : Blo 1678039 3777605 := bbase (se 4 (by rfl) ⟨354150, by rfl⟩ : syracuseStep 3777605 = 708301) (by norm_num)
theorem B41976917 : Blo 1678039 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B3777677 : Blo 1678039 3777677 := bbase (se 3 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 3777677 = 1416629) (by norm_num)
theorem B16131221 : Blo 1678039 16131221 := bbase (se 6 (by rfl) ⟨378075, by rfl⟩ : syracuseStep 16131221 = 756151) (by norm_num)
theorem B5670053 : Blo 1678039 5670053 := bbase (se 4 (by rfl) ⟨531567, by rfl⟩ : syracuseStep 5670053 = 1063135) (by norm_num)
theorem B7267525 : Blo 1678039 7267525 := bbase (se 4 (by rfl) ⟨681330, by rfl⟩ : syracuseStep 7267525 = 1362661) (by norm_num)
theorem B3777749 : Blo 1678039 3777749 := bbase (se 7 (by rfl) ⟨44270, by rfl⟩ : syracuseStep 3777749 = 88541) (by norm_num)
theorem B28697813 : Blo 1678039 28697813 := bbase (se 7 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 28697813 = 672605) (by norm_num)
theorem B3777821 : Blo 1678039 3777821 := bbase (se 3 (by rfl) ⟨708341, by rfl⟩ : syracuseStep 3777821 = 1416683) (by norm_num)
theorem B2016581 : Blo 1678039 2016581 := bbase (se 4 (by rfl) ⟨189054, by rfl⟩ : syracuseStep 2016581 = 378109) (by norm_num)
theorem B7169381 : Blo 1678039 7169381 := bbase (se 4 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 7169381 = 1344259) (by norm_num)
theorem B3777893 : Blo 1678039 3777893 := bbase (se 4 (by rfl) ⟨354177, by rfl⟩ : syracuseStep 3777893 = 708355) (by norm_num)
theorem B3188069 : Blo 1678039 3188069 := bbase (se 4 (by rfl) ⟨298881, by rfl⟩ : syracuseStep 3188069 = 597763) (by norm_num)
theorem B2688365 : Blo 1678039 2688365 := bbase (se 3 (by rfl) ⟨504068, by rfl⟩ : syracuseStep 2688365 = 1008137) (by norm_num)
theorem B4367749 : Blo 1678039 4367749 := bbase (se 4 (by rfl) ⟨409476, by rfl⟩ : syracuseStep 4367749 = 818953) (by norm_num)
theorem B2270605 : Blo 1678039 2270605 := bbase (se 3 (by rfl) ⟨425738, by rfl⟩ : syracuseStep 2270605 = 851477) (by norm_num)
theorem B3024301 : Blo 1678039 3024301 := bbase (se 3 (by rfl) ⟨567056, by rfl⟩ : syracuseStep 3024301 = 1134113) (by norm_num)
theorem B3777965 : Blo 1678039 3777965 := bbase (se 3 (by rfl) ⟨708368, by rfl⟩ : syracuseStep 3777965 = 1416737) (by norm_num)
theorem B3778037 : Blo 1678039 3778037 := bbase (se 5 (by rfl) ⟨177095, by rfl⟩ : syracuseStep 3778037 = 354191) (by norm_num)
theorem B8504837 : Blo 1678039 8504837 := bbase (se 4 (by rfl) ⟨797328, by rfl⟩ : syracuseStep 8504837 = 1594657) (by norm_num)
theorem B3778109 : Blo 1678039 3778109 := bbase (se 3 (by rfl) ⟨708395, by rfl⟩ : syracuseStep 3778109 = 1416791) (by norm_num)
theorem B8619605 : Blo 1678039 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B3778181 : Blo 1678039 3778181 := bbase (se 4 (by rfl) ⟨354204, by rfl⟩ : syracuseStep 3778181 = 708409) (by norm_num)
theorem B3827341 : Blo 1678039 3827341 := bbase (se 3 (by rfl) ⟨717626, by rfl⟩ : syracuseStep 3827341 = 1435253) (by norm_num)
theorem B3024533 : Blo 1678039 3024533 := bbase (se 6 (by rfl) ⟨70887, by rfl⟩ : syracuseStep 3024533 = 141775) (by norm_num)
theorem B6809285 : Blo 1678039 6809285 := bbase (se 4 (by rfl) ⟨638370, by rfl⟩ : syracuseStep 6809285 = 1276741) (by norm_num)
theorem B3778253 : Blo 1678039 3778253 := bbase (se 3 (by rfl) ⟨708422, by rfl⟩ : syracuseStep 3778253 = 1416845) (by norm_num)
theorem B3778325 : Blo 1678039 3778325 := bbase (se 6 (by rfl) ⟨88554, by rfl⟩ : syracuseStep 3778325 = 177109) (by norm_num)
theorem B3778397 : Blo 1678039 3778397 := bbase (se 3 (by rfl) ⟨708449, by rfl⟩ : syracuseStep 3778397 = 1416899) (by norm_num)
theorem B2017181 : Blo 1678039 2017181 := bbase (se 3 (by rfl) ⟨378221, by rfl⟩ : syracuseStep 2017181 = 756443) (by norm_num)
theorem B5375909 : Blo 1678039 5375909 := bbase (se 4 (by rfl) ⟨503991, by rfl⟩ : syracuseStep 5375909 = 1007983) (by norm_num)
theorem B8497061 : Blo 1678039 8497061 := bbase (se 4 (by rfl) ⟨796599, by rfl⟩ : syracuseStep 8497061 = 1593199) (by norm_num)
theorem B3778469 : Blo 1678039 3778469 := bbase (se 4 (by rfl) ⟨354231, by rfl⟩ : syracuseStep 3778469 = 708463) (by norm_num)
theorem B8071109 : Blo 1678039 8071109 := bbase (se 4 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 8071109 = 1513333) (by norm_num)
theorem B3778541 : Blo 1678039 3778541 := bbase (se 3 (by rfl) ⟨708476, by rfl⟩ : syracuseStep 3778541 = 1416953) (by norm_num)
theorem B4032517 : Blo 1678039 4032517 := bbase (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) (by norm_num)
theorem B12757013 : Blo 1678039 12757013 := bbase (se 6 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 12757013 = 597985) (by norm_num)
theorem B3778613 : Blo 1678039 3778613 := bbase (se 5 (by rfl) ⟨177122, by rfl⟩ : syracuseStep 3778613 = 354245) (by norm_num)
theorem B3024965 : Blo 1678039 3024965 := bbase (se 4 (by rfl) ⟨283590, by rfl⟩ : syracuseStep 3024965 = 567181) (by norm_num)
theorem B2517077 : Blo 1678039 2517077 := bbase (se 8 (by rfl) ⟨14748, by rfl⟩ : syracuseStep 2517077 = 29497) (by norm_num)
theorem B3188821 : Blo 1678039 3188821 := bbase (se 8 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 3188821 = 37369) (by norm_num)
theorem B2517101 : Blo 1678039 2517101 := bbase (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) (by norm_num)
theorem B3778685 : Blo 1678039 3778685 := bbase (se 3 (by rfl) ⟨708503, by rfl⟩ : syracuseStep 3778685 = 1417007) (by norm_num)
theorem B2517125 : Blo 1678039 2517125 := bbase (se 4 (by rfl) ⟨235980, by rfl⟩ : syracuseStep 2517125 = 471961) (by norm_num)
theorem B2123921 : Blo 1678039 2123921 := bbase (se 2 (by rfl) ⟨796470, by rfl⟩ : syracuseStep 2123921 = 1592941) (by norm_num)
theorem B2517149 : Blo 1678039 2517149 := bbase (se 3 (by rfl) ⟨471965, by rfl⟩ : syracuseStep 2517149 = 943931) (by norm_num)
theorem B2517173 : Blo 1678039 2517173 := bbase (se 5 (by rfl) ⟨117992, by rfl⟩ : syracuseStep 2517173 = 235985) (by norm_num)
theorem B3778757 : Blo 1678039 3778757 := bbase (se 4 (by rfl) ⟨354258, by rfl⟩ : syracuseStep 3778757 = 708517) (by norm_num)
theorem B2123977 : Blo 1678039 2123977 := bbase (se 2 (by rfl) ⟨796491, by rfl⟩ : syracuseStep 2123977 = 1592983) (by norm_num)
theorem B2517197 : Blo 1678039 2517197 := bbase (se 3 (by rfl) ⟨471974, by rfl⟩ : syracuseStep 2517197 = 943949) (by norm_num)
theorem B2017489 : Blo 1678039 2017489 := bbase (se 2 (by rfl) ⟨756558, by rfl⟩ : syracuseStep 2017489 = 1513117) (by norm_num)
theorem B3025109 : Blo 1678039 3025109 := bbase (se 7 (by rfl) ⟨35450, by rfl⟩ : syracuseStep 3025109 = 70901) (by norm_num)
theorem B2517221 : Blo 1678039 2517221 := bbase (se 4 (by rfl) ⟨235989, by rfl⟩ : syracuseStep 2517221 = 471979) (by norm_num)
theorem B8071397 : Blo 1678039 8071397 := bbase (se 4 (by rfl) ⟨756693, by rfl⟩ : syracuseStep 8071397 = 1513387) (by norm_num)
theorem B3188965 : Blo 1678039 3188965 := bbase (se 4 (by rfl) ⟨298965, by rfl⟩ : syracuseStep 3188965 = 597931) (by norm_num)
theorem B2517245 : Blo 1678039 2517245 := bbase (se 3 (by rfl) ⟨471983, by rfl⟩ : syracuseStep 2517245 = 943967) (by norm_num)
theorem B3778829 : Blo 1678039 3778829 := bbase (se 3 (by rfl) ⟨708530, by rfl⟩ : syracuseStep 3778829 = 1417061) (by norm_num)
theorem B2517269 : Blo 1678039 2517269 := bbase (se 6 (by rfl) ⟨58998, by rfl⟩ : syracuseStep 2517269 = 117997) (by norm_num)
theorem B2124073 : Blo 1678039 2124073 := bbase (se 2 (by rfl) ⟨796527, by rfl⟩ : syracuseStep 2124073 = 1593055) (by norm_num)
theorem B2517293 : Blo 1678039 2517293 := bbase (se 3 (by rfl) ⟨471992, by rfl⟩ : syracuseStep 2517293 = 943985) (by norm_num)
theorem B2017585 : Blo 1678039 2017585 := bbase (se 2 (by rfl) ⟨756594, by rfl⟩ : syracuseStep 2017585 = 1513189) (by norm_num)
theorem B2517317 : Blo 1678039 2517317 := bbase (se 4 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 2517317 = 471997) (by norm_num)
theorem B2689357 : Blo 1678039 2689357 := bbase (se 3 (by rfl) ⟨504254, by rfl⟩ : syracuseStep 2689357 = 1008509) (by norm_num)
theorem B7170389 : Blo 1678039 7170389 := bbase (se 10 (by rfl) ⟨10503, by rfl⟩ : syracuseStep 7170389 = 21007) (by norm_num)
theorem B3778901 : Blo 1678039 3778901 := bbase (se 10 (by rfl) ⟨5535, by rfl⟩ : syracuseStep 3778901 = 11071) (by norm_num)
theorem B2517341 : Blo 1678039 2517341 := bbase (se 3 (by rfl) ⟨472001, by rfl⟩ : syracuseStep 2517341 = 944003) (by norm_num)
theorem B2017633 : Blo 1678039 2017633 := bbase (se 2 (by rfl) ⟨756612, by rfl⟩ : syracuseStep 2017633 = 1513225) (by norm_num)
theorem B2517365 : Blo 1678039 2517365 := bbase (se 5 (by rfl) ⟨118001, by rfl⟩ : syracuseStep 2517365 = 236003) (by norm_num)
theorem B3451261 : Blo 1678039 3451261 := bbase (se 3 (by rfl) ⟨647111, by rfl⟩ : syracuseStep 3451261 = 1294223) (by norm_num)
theorem B3189125 : Blo 1678039 3189125 := bbase (se 4 (by rfl) ⟨298980, by rfl⟩ : syracuseStep 3189125 = 597961) (by norm_num)
theorem B2517389 : Blo 1678039 2517389 := bbase (se 3 (by rfl) ⟨472010, by rfl⟩ : syracuseStep 2517389 = 944021) (by norm_num)
theorem B27232661 : Blo 1678039 27232661 := bbase (se 6 (by rfl) ⟨638265, by rfl⟩ : syracuseStep 27232661 = 1276531) (by norm_num)
theorem B3778973 : Blo 1678039 3778973 := bbase (se 3 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 3778973 = 1417115) (by norm_num)
theorem B2517413 : Blo 1678039 2517413 := bbase (se 4 (by rfl) ⟨236007, by rfl⟩ : syracuseStep 2517413 = 472015) (by norm_num)
theorem B12749237 : Blo 1678039 12749237 := bbase (se 5 (by rfl) ⟨597620, by rfl⟩ : syracuseStep 12749237 = 1195241) (by norm_num)
theorem B16361909 : Blo 1678039 16361909 := bbase (se 5 (by rfl) ⟨766964, by rfl⟩ : syracuseStep 16361909 = 1533929) (by norm_num)
theorem B2517437 : Blo 1678039 2517437 := bbase (se 3 (by rfl) ⟨472019, by rfl⟩ : syracuseStep 2517437 = 944039) (by norm_num)
theorem B2517461 : Blo 1678039 2517461 := bbase (se 7 (by rfl) ⟨29501, by rfl⟩ : syracuseStep 2517461 = 59003) (by norm_num)
theorem B2124245 : Blo 1678039 2124245 := bbase (se 7 (by rfl) ⟨24893, by rfl⟩ : syracuseStep 2124245 = 49787) (by norm_num)
theorem B3779045 : Blo 1678039 3779045 := bbase (se 4 (by rfl) ⟨354285, by rfl⟩ : syracuseStep 3779045 = 708571) (by norm_num)
theorem B2517485 : Blo 1678039 2517485 := bbase (se 3 (by rfl) ⟨472028, by rfl⟩ : syracuseStep 2517485 = 944057) (by norm_num)
theorem B3025397 : Blo 1678039 3025397 := bbase (se 5 (by rfl) ⟨141815, by rfl⟩ : syracuseStep 3025397 = 283631) (by norm_num)
theorem B9079285 : Blo 1678039 9079285 := bbase (se 5 (by rfl) ⟨425591, by rfl⟩ : syracuseStep 9079285 = 851183) (by norm_num)
theorem B2517509 : Blo 1678039 2517509 := bbase (se 4 (by rfl) ⟨236016, by rfl⟩ : syracuseStep 2517509 = 472033) (by norm_num)
theorem B6375941 : Blo 1678039 6375941 := bbase (se 4 (by rfl) ⟨597744, by rfl⟩ : syracuseStep 6375941 = 1195489) (by norm_num)
theorem B2124301 : Blo 1678039 2124301 := bbase (se 3 (by rfl) ⟨398306, by rfl⟩ : syracuseStep 2124301 = 796613) (by norm_num)
theorem B3189269 : Blo 1678039 3189269 := bbase (se 6 (by rfl) ⟨74748, by rfl⟩ : syracuseStep 3189269 = 149497) (by norm_num)
theorem B2517533 : Blo 1678039 2517533 := bbase (se 3 (by rfl) ⟨472037, by rfl⟩ : syracuseStep 2517533 = 944075) (by norm_num)
theorem B3779117 : Blo 1678039 3779117 := bbase (se 3 (by rfl) ⟨708584, by rfl⟩ : syracuseStep 3779117 = 1417169) (by norm_num)
theorem B2517557 : Blo 1678039 2517557 := bbase (se 5 (by rfl) ⟨118010, by rfl⟩ : syracuseStep 2517557 = 236021) (by norm_num)
theorem B2517581 : Blo 1678039 2517581 := bbase (se 3 (by rfl) ⟨472046, by rfl⟩ : syracuseStep 2517581 = 944093) (by norm_num)
theorem B2517605 : Blo 1678039 2517605 := bbase (se 4 (by rfl) ⟨236025, by rfl⟩ : syracuseStep 2517605 = 472051) (by norm_num)
theorem B3828325 : Blo 1678039 3828325 := bbase (se 4 (by rfl) ⟨358905, by rfl⟩ : syracuseStep 3828325 = 717811) (by norm_num)
theorem B2124397 : Blo 1678039 2124397 := bbase (se 3 (by rfl) ⟨398324, by rfl⟩ : syracuseStep 2124397 = 796649) (by norm_num)
theorem B3779189 : Blo 1678039 3779189 := bbase (se 5 (by rfl) ⟨177149, by rfl⟩ : syracuseStep 3779189 = 354299) (by norm_num)
theorem B2517629 : Blo 1678039 2517629 := bbase (se 3 (by rfl) ⟨472055, by rfl⟩ : syracuseStep 2517629 = 944111) (by norm_num)
theorem B2517653 : Blo 1678039 2517653 := bbase (se 6 (by rfl) ⟨59007, by rfl⟩ : syracuseStep 2517653 = 118015) (by norm_num)
theorem B2517677 : Blo 1678039 2517677 := bbase (se 3 (by rfl) ⟨472064, by rfl⟩ : syracuseStep 2517677 = 944129) (by norm_num)
theorem B3779261 : Blo 1678039 3779261 := bbase (se 3 (by rfl) ⟨708611, by rfl⟩ : syracuseStep 3779261 = 1417223) (by norm_num)
theorem B2517701 : Blo 1678039 2517701 := bbase (se 4 (by rfl) ⟨236034, by rfl⟩ : syracuseStep 2517701 = 472069) (by norm_num)
theorem B3025621 : Blo 1678039 3025621 := bbase (se 7 (by rfl) ⟨35456, by rfl⟩ : syracuseStep 3025621 = 70913) (by norm_num)
theorem B21523157 : Blo 1678039 21523157 := bbase (se 7 (by rfl) ⟨252224, by rfl⟩ : syracuseStep 21523157 = 504449) (by norm_num)
theorem B2517725 : Blo 1678039 2517725 := bbase (se 3 (by rfl) ⟨472073, by rfl⟩ : syracuseStep 2517725 = 944147) (by norm_num)
theorem B2517749 : Blo 1678039 2517749 := bbase (se 5 (by rfl) ⟨118019, by rfl⟩ : syracuseStep 2517749 = 236039) (by norm_num)
theorem B3779333 : Blo 1678039 3779333 := bbase (se 4 (by rfl) ⟨354312, by rfl⟩ : syracuseStep 3779333 = 708625) (by norm_num)
theorem B2517773 : Blo 1678039 2517773 := bbase (se 3 (by rfl) ⟨472082, by rfl⟩ : syracuseStep 2517773 = 944165) (by norm_num)
theorem B2689805 : Blo 1678039 2689805 := bbase (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) (by norm_num)
theorem B3025685 : Blo 1678039 3025685 := bbase (se 6 (by rfl) ⟨70914, by rfl⟩ : syracuseStep 3025685 = 141829) (by norm_num)
theorem B2124569 : Blo 1678039 2124569 := bbase (se 2 (by rfl) ⟨796713, by rfl⟩ : syracuseStep 2124569 = 1593427) (by norm_num)
theorem B2517797 : Blo 1678039 2517797 := bbase (se 4 (by rfl) ⟨236043, by rfl⟩ : syracuseStep 2517797 = 472087) (by norm_num)
theorem B6376229 : Blo 1678039 6376229 := bbase (se 4 (by rfl) ⟨597771, by rfl⟩ : syracuseStep 6376229 = 1195543) (by norm_num)
theorem B6810421 : Blo 1678039 6810421 := bbase (se 5 (by rfl) ⟨319238, by rfl⟩ : syracuseStep 6810421 = 638477) (by norm_num)
theorem B2517821 : Blo 1678039 2517821 := bbase (se 3 (by rfl) ⟨472091, by rfl⟩ : syracuseStep 2517821 = 944183) (by norm_num)
theorem B3779405 : Blo 1678039 3779405 := bbase (se 3 (by rfl) ⟨708638, by rfl⟩ : syracuseStep 3779405 = 1417277) (by norm_num)
theorem B2124625 : Blo 1678039 2124625 := bbase (se 2 (by rfl) ⟨796734, by rfl⟩ : syracuseStep 2124625 = 1593469) (by norm_num)
theorem B5663573 : Blo 1678039 5663573 := bbase (se 9 (by rfl) ⟨16592, by rfl⟩ : syracuseStep 5663573 = 33185) (by norm_num)
theorem B2517845 : Blo 1678039 2517845 := bbase (se 9 (by rfl) ⟨7376, by rfl⟩ : syracuseStep 2517845 = 14753) (by norm_num)
theorem B2517869 : Blo 1678039 2517869 := bbase (se 3 (by rfl) ⟨472100, by rfl⟩ : syracuseStep 2517869 = 944201) (by norm_num)
theorem B2517893 : Blo 1678039 2517893 := bbase (se 4 (by rfl) ⟨236052, by rfl⟩ : syracuseStep 2517893 = 472105) (by norm_num)
theorem B3779477 : Blo 1678039 3779477 := bbase (se 6 (by rfl) ⟨88581, by rfl⟩ : syracuseStep 3779477 = 177163) (by norm_num)
theorem B2517917 : Blo 1678039 2517917 := bbase (se 3 (by rfl) ⟨472109, by rfl⟩ : syracuseStep 2517917 = 944219) (by norm_num)
theorem B2124721 : Blo 1678039 2124721 := bbase (se 2 (by rfl) ⟨796770, by rfl⟩ : syracuseStep 2124721 = 1593541) (by norm_num)
theorem B2517941 : Blo 1678039 2517941 := bbase (se 5 (by rfl) ⟨118028, by rfl⟩ : syracuseStep 2517941 = 236057) (by norm_num)
theorem B2517965 : Blo 1678039 2517965 := bbase (se 3 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 2517965 = 944237) (by norm_num)
theorem B2690005 : Blo 1678039 2690005 := bbase (se 7 (by rfl) ⟨31523, by rfl⟩ : syracuseStep 2690005 = 63047) (by norm_num)
theorem B3779549 : Blo 1678039 3779549 := bbase (se 3 (by rfl) ⟨708665, by rfl⟩ : syracuseStep 3779549 = 1417331) (by norm_num)
theorem B2517989 : Blo 1678039 2517989 := bbase (se 4 (by rfl) ⟨236061, by rfl⟩ : syracuseStep 2517989 = 472123) (by norm_num)
theorem B2518013 : Blo 1678039 2518013 := bbase (se 3 (by rfl) ⟨472127, by rfl⟩ : syracuseStep 2518013 = 944255) (by norm_num)
theorem B2518037 : Blo 1678039 2518037 := bbase (se 6 (by rfl) ⟨59016, by rfl⟩ : syracuseStep 2518037 = 118033) (by norm_num)
theorem B3779621 : Blo 1678039 3779621 := bbase (se 4 (by rfl) ⟨354339, by rfl⟩ : syracuseStep 3779621 = 708679) (by norm_num)
theorem B2518061 : Blo 1678039 2518061 := bbase (se 3 (by rfl) ⟨472136, by rfl⟩ : syracuseStep 2518061 = 944273) (by norm_num)
theorem B2518085 : Blo 1678039 2518085 := bbase (se 4 (by rfl) ⟨236070, by rfl⟩ : syracuseStep 2518085 = 472141) (by norm_num)
theorem B2518109 : Blo 1678039 2518109 := bbase (se 3 (by rfl) ⟨472145, by rfl⟩ : syracuseStep 2518109 = 944291) (by norm_num)
theorem B2124893 : Blo 1678039 2124893 := bbase (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) (by norm_num)
theorem B3779693 : Blo 1678039 3779693 := bbase (se 3 (by rfl) ⟨708692, by rfl⟩ : syracuseStep 3779693 = 1417385) (by norm_num)
theorem B2518133 : Blo 1678039 2518133 := bbase (se 5 (by rfl) ⟨118037, by rfl⟩ : syracuseStep 2518133 = 236075) (by norm_num)
theorem B2518157 : Blo 1678039 2518157 := bbase (se 3 (by rfl) ⟨472154, by rfl⟩ : syracuseStep 2518157 = 944309) (by norm_num)
theorem B2124949 : Blo 1678039 2124949 := bbase (se 6 (by rfl) ⟨49803, by rfl⟩ : syracuseStep 2124949 = 99607) (by norm_num)
theorem B2518181 : Blo 1678039 2518181 := bbase (se 4 (by rfl) ⟨236079, by rfl⟩ : syracuseStep 2518181 = 472159) (by norm_num)
theorem B4033709 : Blo 1678039 4033709 := bbase (se 3 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 4033709 = 1512641) (by norm_num)
theorem B8498357 : Blo 1678039 8498357 := bbase (se 5 (by rfl) ⟨398360, by rfl⟩ : syracuseStep 8498357 = 796721) (by norm_num)
theorem B3779765 : Blo 1678039 3779765 := bbase (se 5 (by rfl) ⟨177176, by rfl⟩ : syracuseStep 3779765 = 354353) (by norm_num)
theorem B2518205 : Blo 1678039 2518205 := bbase (se 3 (by rfl) ⟨472163, by rfl⟩ : syracuseStep 2518205 = 944327) (by norm_num)
theorem B2518229 : Blo 1678039 2518229 := bbase (se 7 (by rfl) ⟨29510, by rfl⟩ : syracuseStep 2518229 = 59021) (by norm_num)
theorem B2690261 : Blo 1678039 2690261 := bbase (se 7 (by rfl) ⟨31526, by rfl⟩ : syracuseStep 2690261 = 63053) (by norm_num)
theorem B2518253 : Blo 1678039 2518253 := bbase (se 3 (by rfl) ⟨472172, by rfl⟩ : syracuseStep 2518253 = 944345) (by norm_num)
theorem B2125045 : Blo 1678039 2125045 := bbase (se 5 (by rfl) ⟨99611, by rfl⟩ : syracuseStep 2125045 = 199223) (by norm_num)
theorem B3779837 : Blo 1678039 3779837 := bbase (se 3 (by rfl) ⟨708719, by rfl⟩ : syracuseStep 3779837 = 1417439) (by norm_num)
theorem B5664005 : Blo 1678039 5664005 := bbase (se 4 (by rfl) ⟨531000, by rfl⟩ : syracuseStep 5664005 = 1062001) (by norm_num)
theorem B2518277 : Blo 1678039 2518277 := bbase (se 4 (by rfl) ⟨236088, by rfl⟩ : syracuseStep 2518277 = 472177) (by norm_num)
theorem B2518301 : Blo 1678039 2518301 := bbase (se 3 (by rfl) ⟨472181, by rfl⟩ : syracuseStep 2518301 = 944363) (by norm_num)
theorem B2518325 : Blo 1678039 2518325 := bbase (se 5 (by rfl) ⟨118046, by rfl⟩ : syracuseStep 2518325 = 236093) (by norm_num)
theorem B3779909 : Blo 1678039 3779909 := bbase (se 4 (by rfl) ⟨354366, by rfl⟩ : syracuseStep 3779909 = 708733) (by norm_num)
theorem B2518349 : Blo 1678039 2518349 := bbase (se 3 (by rfl) ⟨472190, by rfl⟩ : syracuseStep 2518349 = 944381) (by norm_num)
theorem B2518373 : Blo 1678039 2518373 := bbase (se 4 (by rfl) ⟨236097, by rfl⟩ : syracuseStep 2518373 = 472195) (by norm_num)
theorem B4033901 : Blo 1678039 4033901 := bbase (se 3 (by rfl) ⟨756356, by rfl⟩ : syracuseStep 4033901 = 1512713) (by norm_num)
theorem B2518397 : Blo 1678039 2518397 := bbase (se 3 (by rfl) ⟨472199, by rfl⟩ : syracuseStep 2518397 = 944399) (by norm_num)
theorem B3779981 : Blo 1678039 3779981 := bbase (se 3 (by rfl) ⟨708746, by rfl⟩ : syracuseStep 3779981 = 1417493) (by norm_num)
theorem B2518421 : Blo 1678039 2518421 := bbase (se 6 (by rfl) ⟨59025, by rfl⟩ : syracuseStep 2518421 = 118051) (by norm_num)
theorem B2125217 : Blo 1678039 2125217 := bbase (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) (by norm_num)
theorem B2518445 : Blo 1678039 2518445 := bbase (se 3 (by rfl) ⟨472208, by rfl⟩ : syracuseStep 2518445 = 944417) (by norm_num)
theorem B4779461 : Blo 1678039 4779461 := bbase (se 4 (by rfl) ⟨448074, by rfl⟩ : syracuseStep 4779461 = 896149) (by norm_num)
theorem B2518469 : Blo 1678039 2518469 := bbase (se 4 (by rfl) ⟨236106, by rfl⟩ : syracuseStep 2518469 = 472213) (by norm_num)
theorem B6049237 : Blo 1678039 6049237 := bbase (se 7 (by rfl) ⟨70889, by rfl⟩ : syracuseStep 6049237 = 141779) (by norm_num)
theorem B24202709 : Blo 1678039 24202709 := bbase (se 7 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 24202709 = 567251) (by norm_num)
theorem B3780053 : Blo 1678039 3780053 := bbase (se 7 (by rfl) ⟨44297, by rfl⟩ : syracuseStep 3780053 = 88595) (by norm_num)
theorem B2125273 : Blo 1678039 2125273 := bbase (se 2 (by rfl) ⟨796977, by rfl⟩ : syracuseStep 2125273 = 1593955) (by norm_num)
theorem B2518493 : Blo 1678039 2518493 := bbase (se 3 (by rfl) ⟨472217, by rfl⟩ : syracuseStep 2518493 = 944435) (by norm_num)
theorem B2518517 : Blo 1678039 2518517 := bbase (se 5 (by rfl) ⟨118055, by rfl⟩ : syracuseStep 2518517 = 236111) (by norm_num)
theorem B6458885 : Blo 1678039 6458885 := bbase (se 4 (by rfl) ⟨605520, by rfl⟩ : syracuseStep 6458885 = 1211041) (by norm_num)
theorem B2518541 : Blo 1678039 2518541 := bbase (se 3 (by rfl) ⟨472226, by rfl⟩ : syracuseStep 2518541 = 944453) (by norm_num)
theorem B2518565 : Blo 1678039 2518565 := bbase (se 4 (by rfl) ⟨236115, by rfl⟩ : syracuseStep 2518565 = 472231) (by norm_num)
theorem B2125369 : Blo 1678039 2125369 := bbase (se 2 (by rfl) ⟨797013, by rfl⟩ : syracuseStep 2125369 = 1594027) (by norm_num)
theorem B2518589 : Blo 1678039 2518589 := bbase (se 3 (by rfl) ⟨472235, by rfl⟩ : syracuseStep 2518589 = 944471) (by norm_num)
theorem B1887817 : Blo 1678039 1887817 := bbase (se 2 (by rfl) ⟨707931, by rfl⟩ : syracuseStep 1887817 = 1415863) (by norm_num)
theorem B2518613 : Blo 1678039 2518613 := bbase (se 8 (by rfl) ⟨14757, by rfl⟩ : syracuseStep 2518613 = 29515) (by norm_num)
theorem B1887853 : Blo 1678039 1887853 := bbase (se 3 (by rfl) ⟨353972, by rfl⟩ : syracuseStep 1887853 = 707945) (by norm_num)
theorem B2518637 : Blo 1678039 2518637 := bbase (se 3 (by rfl) ⟨472244, by rfl⟩ : syracuseStep 2518637 = 944489) (by norm_num)
theorem B6049397 : Blo 1678039 6049397 := bbase (se 5 (by rfl) ⟨283565, by rfl⟩ : syracuseStep 6049397 = 567131) (by norm_num)
theorem B2518661 : Blo 1678039 2518661 := bbase (se 4 (by rfl) ⟨236124, by rfl⟩ : syracuseStep 2518661 = 472249) (by norm_num)
theorem B1887889 : Blo 1678039 1887889 := bbase (se 2 (by rfl) ⟨707958, by rfl⟩ : syracuseStep 1887889 = 1415917) (by norm_num)
theorem B2518685 : Blo 1678039 2518685 := bbase (se 3 (by rfl) ⟨472253, by rfl⟩ : syracuseStep 2518685 = 944507) (by norm_num)
theorem B1887925 : Blo 1678039 1887925 := bbase (se 5 (by rfl) ⟨88496, by rfl⟩ : syracuseStep 1887925 = 176993) (by norm_num)
theorem B5664437 : Blo 1678039 5664437 := bbase (se 5 (by rfl) ⟨265520, by rfl⟩ : syracuseStep 5664437 = 531041) (by norm_num)
theorem B2518709 : Blo 1678039 2518709 := bbase (se 5 (by rfl) ⟨118064, by rfl⟩ : syracuseStep 2518709 = 236129) (by norm_num)
theorem B2518733 : Blo 1678039 2518733 := bbase (se 3 (by rfl) ⟨472262, by rfl⟩ : syracuseStep 2518733 = 944525) (by norm_num)
theorem B1887961 : Blo 1678039 1887961 := bbase (se 2 (by rfl) ⟨707985, by rfl⟩ : syracuseStep 1887961 = 1415971) (by norm_num)
theorem B5377765 : Blo 1678039 5377765 := bbase (se 4 (by rfl) ⟨504165, by rfl⟩ : syracuseStep 5377765 = 1008331) (by norm_num)
theorem B2518757 : Blo 1678039 2518757 := bbase (se 4 (by rfl) ⟨236133, by rfl⟩ : syracuseStep 2518757 = 472267) (by norm_num)
theorem B2125541 : Blo 1678039 2125541 := bbase (se 4 (by rfl) ⟨199269, by rfl⟩ : syracuseStep 2125541 = 398539) (by norm_num)
theorem B6049525 : Blo 1678039 6049525 := bbase (se 5 (by rfl) ⟨283571, by rfl⟩ : syracuseStep 6049525 = 567143) (by norm_num)
theorem B1887997 : Blo 1678039 1887997 := bbase (se 3 (by rfl) ⟨353999, by rfl⟩ : syracuseStep 1887997 = 707999) (by norm_num)
theorem B2518781 : Blo 1678039 2518781 := bbase (se 3 (by rfl) ⟨472271, by rfl⟩ : syracuseStep 2518781 = 944543) (by norm_num)
theorem B2518805 : Blo 1678039 2518805 := bbase (se 6 (by rfl) ⟨59034, by rfl⟩ : syracuseStep 2518805 = 118069) (by norm_num)
theorem B2125597 : Blo 1678039 2125597 := bbase (se 3 (by rfl) ⟨398549, by rfl⟩ : syracuseStep 2125597 = 797099) (by norm_num)
theorem B1888033 : Blo 1678039 1888033 := bbase (se 2 (by rfl) ⟨708012, by rfl⟩ : syracuseStep 1888033 = 1416025) (by norm_num)
theorem B2518829 : Blo 1678039 2518829 := bbase (se 3 (by rfl) ⟨472280, by rfl⟩ : syracuseStep 2518829 = 944561) (by norm_num)
theorem B1888069 : Blo 1678039 1888069 := bbase (se 4 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 1888069 = 354013) (by norm_num)
theorem B2518853 : Blo 1678039 2518853 := bbase (se 4 (by rfl) ⟨236142, by rfl⟩ : syracuseStep 2518853 = 472285) (by norm_num)
theorem B2518877 : Blo 1678039 2518877 := bbase (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) (by norm_num)
theorem B2043749 : Blo 1678039 2043749 := bbase (se 4 (by rfl) ⟨191601, by rfl⟩ : syracuseStep 2043749 = 383203) (by norm_num)
theorem B1888105 : Blo 1678039 1888105 := bbase (se 2 (by rfl) ⟨708039, by rfl⟩ : syracuseStep 1888105 = 1416079) (by norm_num)
theorem B2518901 : Blo 1678039 2518901 := bbase (se 5 (by rfl) ⟨118073, by rfl⟩ : syracuseStep 2518901 = 236147) (by norm_num)
theorem B2125693 : Blo 1678039 2125693 := bbase (se 3 (by rfl) ⟨398567, by rfl⟩ : syracuseStep 2125693 = 797135) (by norm_num)
theorem B1888141 : Blo 1678039 1888141 := bbase (se 3 (by rfl) ⟨354026, by rfl⟩ : syracuseStep 1888141 = 708053) (by norm_num)
theorem B2518925 : Blo 1678039 2518925 := bbase (se 3 (by rfl) ⟨472298, by rfl⟩ : syracuseStep 2518925 = 944597) (by norm_num)
theorem B2518949 : Blo 1678039 2518949 := bbase (se 4 (by rfl) ⟨236151, by rfl⟩ : syracuseStep 2518949 = 472303) (by norm_num)
theorem B1888177 : Blo 1678039 1888177 := bbase (se 2 (by rfl) ⟨708066, by rfl⟩ : syracuseStep 1888177 = 1416133) (by norm_num)
theorem B2518973 : Blo 1678039 2518973 := bbase (se 3 (by rfl) ⟨472307, by rfl⟩ : syracuseStep 2518973 = 944615) (by norm_num)
theorem B4599749 : Blo 1678039 4599749 := bbase (se 4 (by rfl) ⟨431226, by rfl⟩ : syracuseStep 4599749 = 862453) (by norm_num)
theorem B6377413 : Blo 1678039 6377413 := bbase (se 4 (by rfl) ⟨597882, by rfl⟩ : syracuseStep 6377413 = 1195765) (by norm_num)
theorem B1888213 : Blo 1678039 1888213 := bbase (se 7 (by rfl) ⟨22127, by rfl⟩ : syracuseStep 1888213 = 44255) (by norm_num)
theorem B2518997 : Blo 1678039 2518997 := bbase (se 7 (by rfl) ⟨29519, by rfl⟩ : syracuseStep 2518997 = 59039) (by norm_num)
theorem B2519021 : Blo 1678039 2519021 := bbase (se 3 (by rfl) ⟨472316, by rfl⟩ : syracuseStep 2519021 = 944633) (by norm_num)
theorem B1888249 : Blo 1678039 1888249 := bbase (se 2 (by rfl) ⟨708093, by rfl⟩ : syracuseStep 1888249 = 1416187) (by norm_num)
theorem B4247549 : Blo 1678039 4247549 := bbase (se 3 (by rfl) ⟨796415, by rfl⟩ : syracuseStep 4247549 = 1592831) (by norm_num)
theorem B2519045 : Blo 1678039 2519045 := bbase (se 4 (by rfl) ⟨236160, by rfl⟩ : syracuseStep 2519045 = 472321) (by norm_num)
theorem B1888285 : Blo 1678039 1888285 := bbase (se 3 (by rfl) ⟨354053, by rfl⟩ : syracuseStep 1888285 = 708107) (by norm_num)
theorem B2519069 : Blo 1678039 2519069 := bbase (se 3 (by rfl) ⟨472325, by rfl⟩ : syracuseStep 2519069 = 944651) (by norm_num)
theorem B2125865 : Blo 1678039 2125865 := bbase (se 2 (by rfl) ⟨797199, by rfl⟩ : syracuseStep 2125865 = 1594399) (by norm_num)
theorem B2519093 : Blo 1678039 2519093 := bbase (se 5 (by rfl) ⟨118082, by rfl⟩ : syracuseStep 2519093 = 236165) (by norm_num)
theorem B1888321 : Blo 1678039 1888321 := bbase (se 2 (by rfl) ⟨708120, by rfl⟩ : syracuseStep 1888321 = 1416241) (by norm_num)
theorem B7172165 : Blo 1678039 7172165 := bbase (se 4 (by rfl) ⟨672390, by rfl⟩ : syracuseStep 7172165 = 1344781) (by norm_num)
theorem B2519117 : Blo 1678039 2519117 := bbase (se 3 (by rfl) ⟨472334, by rfl⟩ : syracuseStep 2519117 = 944669) (by norm_num)
theorem B2125921 : Blo 1678039 2125921 := bbase (se 2 (by rfl) ⟨797220, by rfl⟩ : syracuseStep 2125921 = 1594441) (by norm_num)
theorem B3584101 : Blo 1678039 3584101 := bbase (se 4 (by rfl) ⟨336009, by rfl⟩ : syracuseStep 3584101 = 672019) (by norm_num)
theorem B5664869 : Blo 1678039 5664869 := bbase (se 4 (by rfl) ⟨531081, by rfl⟩ : syracuseStep 5664869 = 1062163) (by norm_num)
theorem B1888357 : Blo 1678039 1888357 := bbase (se 4 (by rfl) ⟨177033, by rfl⟩ : syracuseStep 1888357 = 354067) (by norm_num)
theorem B2519141 : Blo 1678039 2519141 := bbase (se 4 (by rfl) ⟨236169, by rfl⟩ : syracuseStep 2519141 = 472339) (by norm_num)
theorem B2519165 : Blo 1678039 2519165 := bbase (se 3 (by rfl) ⟨472343, by rfl⟩ : syracuseStep 2519165 = 944687) (by norm_num)
theorem B1888393 : Blo 1678039 1888393 := bbase (se 2 (by rfl) ⟨708147, by rfl⟩ : syracuseStep 1888393 = 1416295) (by norm_num)
theorem B2519189 : Blo 1678039 2519189 := bbase (se 6 (by rfl) ⟨59043, by rfl⟩ : syracuseStep 2519189 = 118087) (by norm_num)
theorem B1888429 : Blo 1678039 1888429 := bbase (se 3 (by rfl) ⟨354080, by rfl⟩ : syracuseStep 1888429 = 708161) (by norm_num)
theorem B2519213 : Blo 1678039 2519213 := bbase (se 3 (by rfl) ⟨472352, by rfl⟩ : syracuseStep 2519213 = 944705) (by norm_num)
theorem B4247741 : Blo 1678039 4247741 := bbase (se 3 (by rfl) ⟨796451, by rfl⟩ : syracuseStep 4247741 = 1592903) (by norm_num)
theorem B2126017 : Blo 1678039 2126017 := bbase (se 2 (by rfl) ⟨797256, by rfl⟩ : syracuseStep 2126017 = 1594513) (by norm_num)
theorem B2519237 : Blo 1678039 2519237 := bbase (se 4 (by rfl) ⟨236178, by rfl⟩ : syracuseStep 2519237 = 472357) (by norm_num)
theorem B1888465 : Blo 1678039 1888465 := bbase (se 2 (by rfl) ⟨708174, by rfl⟩ : syracuseStep 1888465 = 1416349) (by norm_num)
theorem B2519261 : Blo 1678039 2519261 := bbase (se 3 (by rfl) ⟨472361, by rfl⟩ : syracuseStep 2519261 = 944723) (by norm_num)
theorem B1888501 : Blo 1678039 1888501 := bbase (se 5 (by rfl) ⟨88523, by rfl⟩ : syracuseStep 1888501 = 177047) (by norm_num)
theorem B2519285 : Blo 1678039 2519285 := bbase (se 5 (by rfl) ⟨118091, by rfl⟩ : syracuseStep 2519285 = 236183) (by norm_num)
theorem B6377717 : Blo 1678039 6377717 := bbase (se 5 (by rfl) ⟨298955, by rfl⟩ : syracuseStep 6377717 = 597911) (by norm_num)
theorem B2519309 : Blo 1678039 2519309 := bbase (se 3 (by rfl) ⟨472370, by rfl⟩ : syracuseStep 2519309 = 944741) (by norm_num)
theorem B19378453 : Blo 1678039 19378453 := bbase (se 6 (by rfl) ⟨454182, by rfl⟩ : syracuseStep 19378453 = 908365) (by norm_num)
theorem B1888537 : Blo 1678039 1888537 := bbase (se 2 (by rfl) ⟨708201, by rfl⟩ : syracuseStep 1888537 = 1416403) (by norm_num)
theorem B2519333 : Blo 1678039 2519333 := bbase (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) (by norm_num)
theorem B1888573 : Blo 1678039 1888573 := bbase (se 3 (by rfl) ⟨354107, by rfl⟩ : syracuseStep 1888573 = 708215) (by norm_num)
theorem B2519357 : Blo 1678039 2519357 := bbase (se 3 (by rfl) ⟨472379, by rfl⟩ : syracuseStep 2519357 = 944759) (by norm_num)
theorem B2519381 : Blo 1678039 2519381 := bbase (se 10 (by rfl) ⟨3690, by rfl⟩ : syracuseStep 2519381 = 7381) (by norm_num)
theorem B1888609 : Blo 1678039 1888609 := bbase (se 2 (by rfl) ⟨708228, by rfl⟩ : syracuseStep 1888609 = 1416457) (by norm_num)
theorem B2519405 : Blo 1678039 2519405 := bbase (se 3 (by rfl) ⟨472388, by rfl⟩ : syracuseStep 2519405 = 944777) (by norm_num)
theorem B2126189 : Blo 1678039 2126189 := bbase (se 3 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 2126189 = 797321) (by norm_num)
theorem B1888645 : Blo 1678039 1888645 := bbase (se 4 (by rfl) ⟨177060, by rfl⟩ : syracuseStep 1888645 = 354121) (by norm_num)
theorem B2519429 : Blo 1678039 2519429 := bbase (se 4 (by rfl) ⟨236196, by rfl⟩ : syracuseStep 2519429 = 472393) (by norm_num)
theorem B5452181 : Blo 1678039 5452181 := bbase (se 6 (by rfl) ⟨127785, by rfl⟩ : syracuseStep 5452181 = 255571) (by norm_num)
theorem B2519453 : Blo 1678039 2519453 := bbase (se 3 (by rfl) ⟨472397, by rfl⟩ : syracuseStep 2519453 = 944795) (by norm_num)
theorem B2126245 : Blo 1678039 2126245 := bbase (se 4 (by rfl) ⟨199335, by rfl⟩ : syracuseStep 2126245 = 398671) (by norm_num)
theorem B1888681 : Blo 1678039 1888681 := bbase (se 2 (by rfl) ⟨708255, by rfl⟩ : syracuseStep 1888681 = 1416511) (by norm_num)
theorem B2519477 : Blo 1678039 2519477 := bbase (se 5 (by rfl) ⟨118100, by rfl⟩ : syracuseStep 2519477 = 236201) (by norm_num)
theorem B8499653 : Blo 1678039 8499653 := bbase (se 4 (by rfl) ⟨796842, by rfl⟩ : syracuseStep 8499653 = 1593685) (by norm_num)
theorem B1888717 : Blo 1678039 1888717 := bbase (se 3 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 1888717 = 708269) (by norm_num)
theorem B2519501 : Blo 1678039 2519501 := bbase (se 3 (by rfl) ⟨472406, by rfl⟩ : syracuseStep 2519501 = 944813) (by norm_num)
theorem B2552285 : Blo 1678039 2552285 := bbase (se 3 (by rfl) ⟨478553, by rfl⟩ : syracuseStep 2552285 = 957107) (by norm_num)
theorem B2519525 : Blo 1678039 2519525 := bbase (se 4 (by rfl) ⟨236205, by rfl⟩ : syracuseStep 2519525 = 472411) (by norm_num)
theorem B1888753 : Blo 1678039 1888753 := bbase (se 2 (by rfl) ⟨708282, by rfl⟩ : syracuseStep 1888753 = 1416565) (by norm_num)
theorem B2519549 : Blo 1678039 2519549 := bbase (se 3 (by rfl) ⟨472415, by rfl⟩ : syracuseStep 2519549 = 944831) (by norm_num)
theorem B4248085 : Blo 1678039 4248085 := bbase (se 6 (by rfl) ⟨99564, by rfl⟩ : syracuseStep 4248085 = 199129) (by norm_num)
theorem B5665301 : Blo 1678039 5665301 := bbase (se 6 (by rfl) ⟨132780, by rfl⟩ : syracuseStep 5665301 = 265561) (by norm_num)
theorem B1888789 : Blo 1678039 1888789 := bbase (se 6 (by rfl) ⟨44268, by rfl⟩ : syracuseStep 1888789 = 88537) (by norm_num)
theorem B2519573 : Blo 1678039 2519573 := bbase (se 6 (by rfl) ⟨59052, by rfl⟩ : syracuseStep 2519573 = 118105) (by norm_num)
theorem B2519597 : Blo 1678039 2519597 := bbase (se 3 (by rfl) ⟨472424, by rfl⟩ : syracuseStep 2519597 = 944849) (by norm_num)
theorem B12096053 : Blo 1678039 12096053 := bbase (se 5 (by rfl) ⟨567002, by rfl⟩ : syracuseStep 12096053 = 1134005) (by norm_num)
theorem B1888825 : Blo 1678039 1888825 := bbase (se 2 (by rfl) ⟨708309, by rfl⟩ : syracuseStep 1888825 = 1416619) (by norm_num)
theorem B2519621 : Blo 1678039 2519621 := bbase (se 4 (by rfl) ⟨236214, by rfl⟩ : syracuseStep 2519621 = 472429) (by norm_num)
theorem B1888861 : Blo 1678039 1888861 := bbase (se 3 (by rfl) ⟨354161, by rfl⟩ : syracuseStep 1888861 = 708323) (by norm_num)
theorem B2519645 : Blo 1678039 2519645 := bbase (se 3 (by rfl) ⟨472433, by rfl⟩ : syracuseStep 2519645 = 944867) (by norm_num)
theorem B2519669 : Blo 1678039 2519669 := bbase (se 5 (by rfl) ⟨118109, by rfl⟩ : syracuseStep 2519669 = 236219) (by norm_num)
theorem B1888897 : Blo 1678039 1888897 := bbase (se 2 (by rfl) ⟨708336, by rfl⟩ : syracuseStep 1888897 = 1416673) (by norm_num)
theorem B4248197 : Blo 1678039 4248197 := bbase (se 4 (by rfl) ⟨398268, by rfl⟩ : syracuseStep 4248197 = 796537) (by norm_num)
theorem B2519693 : Blo 1678039 2519693 := bbase (se 3 (by rfl) ⟨472442, by rfl⟩ : syracuseStep 2519693 = 944885) (by norm_num)
theorem B1888933 : Blo 1678039 1888933 := bbase (se 4 (by rfl) ⟨177087, by rfl⟩ : syracuseStep 1888933 = 354175) (by norm_num)
theorem B2519717 : Blo 1678039 2519717 := bbase (se 4 (by rfl) ⟨236223, by rfl⟩ : syracuseStep 2519717 = 472447) (by norm_num)
theorem B2519741 : Blo 1678039 2519741 := bbase (se 3 (by rfl) ⟨472451, by rfl⟩ : syracuseStep 2519741 = 944903) (by norm_num)
theorem B3232453 : Blo 1678039 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B1888969 : Blo 1678039 1888969 := bbase (se 2 (by rfl) ⟨708363, by rfl⟩ : syracuseStep 1888969 = 1416727) (by norm_num)
theorem B2519765 : Blo 1678039 2519765 := bbase (se 7 (by rfl) ⟨29528, by rfl⟩ : syracuseStep 2519765 = 59057) (by norm_num)
theorem B1889005 : Blo 1678039 1889005 := bbase (se 3 (by rfl) ⟨354188, by rfl⟩ : syracuseStep 1889005 = 708377) (by norm_num)
theorem B2519789 : Blo 1678039 2519789 := bbase (se 3 (by rfl) ⟨472460, by rfl⟩ : syracuseStep 2519789 = 944921) (by norm_num)
theorem B2519813 : Blo 1678039 2519813 := bbase (se 4 (by rfl) ⟨236232, by rfl⟩ : syracuseStep 2519813 = 472465) (by norm_num)
theorem B1889041 : Blo 1678039 1889041 := bbase (se 2 (by rfl) ⟨708390, by rfl⟩ : syracuseStep 1889041 = 1416781) (by norm_num)
theorem B2519837 : Blo 1678039 2519837 := bbase (se 3 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 2519837 = 944939) (by norm_num)
theorem B1889077 : Blo 1678039 1889077 := bbase (se 5 (by rfl) ⟨88550, by rfl⟩ : syracuseStep 1889077 = 177101) (by norm_num)
theorem B2519861 : Blo 1678039 2519861 := bbase (se 5 (by rfl) ⟨118118, by rfl⟩ : syracuseStep 2519861 = 236237) (by norm_num)
theorem B4248389 : Blo 1678039 4248389 := bbase (se 4 (by rfl) ⟨398286, by rfl⟩ : syracuseStep 4248389 = 796573) (by norm_num)
theorem B2519885 : Blo 1678039 2519885 := bbase (se 3 (by rfl) ⟨472478, by rfl⟩ : syracuseStep 2519885 = 944957) (by norm_num)
theorem B1889113 : Blo 1678039 1889113 := bbase (se 2 (by rfl) ⟨708417, by rfl⟩ : syracuseStep 1889113 = 1416835) (by norm_num)
theorem B3232613 : Blo 1678039 3232613 := bbase (se 4 (by rfl) ⟨303057, by rfl⟩ : syracuseStep 3232613 = 606115) (by norm_num)
theorem B2519909 : Blo 1678039 2519909 := bbase (se 4 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 2519909 = 472483) (by norm_num)
theorem B1889149 : Blo 1678039 1889149 := bbase (se 3 (by rfl) ⟨354215, by rfl⟩ : syracuseStep 1889149 = 708431) (by norm_num)
theorem B2519933 : Blo 1678039 2519933 := bbase (se 3 (by rfl) ⟨472487, by rfl⟩ : syracuseStep 2519933 = 944975) (by norm_num)
theorem B3404693 : Blo 1678039 3404693 := bbase (se 6 (by rfl) ⟨79797, by rfl⟩ : syracuseStep 3404693 = 159595) (by norm_num)
theorem B19133333 : Blo 1678039 19133333 := bbase (se 6 (by rfl) ⟨448437, by rfl⟩ : syracuseStep 19133333 = 896875) (by norm_num)
theorem B2519957 : Blo 1678039 2519957 := bbase (se 6 (by rfl) ⟨59061, by rfl⟩ : syracuseStep 2519957 = 118123) (by norm_num)
theorem B1889185 : Blo 1678039 1889185 := bbase (se 2 (by rfl) ⟨708444, by rfl⟩ : syracuseStep 1889185 = 1416889) (by norm_num)
theorem B2519981 : Blo 1678039 2519981 := bbase (se 3 (by rfl) ⟨472496, by rfl⟩ : syracuseStep 2519981 = 944993) (by norm_num)
theorem B6132677 : Blo 1678039 6132677 := bbase (se 4 (by rfl) ⟨574938, by rfl⟩ : syracuseStep 6132677 = 1149877) (by norm_num)
theorem B5665733 : Blo 1678039 5665733 := bbase (se 4 (by rfl) ⟨531162, by rfl⟩ : syracuseStep 5665733 = 1062325) (by norm_num)
theorem B1889221 : Blo 1678039 1889221 := bbase (se 4 (by rfl) ⟨177114, by rfl⟩ : syracuseStep 1889221 = 354229) (by norm_num)
theorem B2520005 : Blo 1678039 2520005 := bbase (se 4 (by rfl) ⟨236250, by rfl⟩ : syracuseStep 2520005 = 472501) (by norm_num)
theorem B3584989 : Blo 1678039 3584989 := bbase (se 3 (by rfl) ⟨672185, by rfl⟩ : syracuseStep 3584989 = 1344371) (by norm_num)
theorem B2520029 : Blo 1678039 2520029 := bbase (se 3 (by rfl) ⟨472505, by rfl⟩ : syracuseStep 2520029 = 945011) (by norm_num)
theorem B1889257 : Blo 1678039 1889257 := bbase (se 2 (by rfl) ⟨708471, by rfl⟩ : syracuseStep 1889257 = 1416943) (by norm_num)
theorem B4781045 : Blo 1678039 4781045 := bbase (se 5 (by rfl) ⟨224111, by rfl⟩ : syracuseStep 4781045 = 448223) (by norm_num)
theorem B2520053 : Blo 1678039 2520053 := bbase (se 5 (by rfl) ⟨118127, by rfl⟩ : syracuseStep 2520053 = 236255) (by norm_num)
theorem B2872325 : Blo 1678039 2872325 := bbase (se 4 (by rfl) ⟨269280, by rfl⟩ : syracuseStep 2872325 = 538561) (by norm_num)
theorem B1889293 : Blo 1678039 1889293 := bbase (se 3 (by rfl) ⟨354242, by rfl⟩ : syracuseStep 1889293 = 708485) (by norm_num)
theorem B1889329 : Blo 1678039 1889329 := bbase (se 2 (by rfl) ⟨708498, by rfl⟩ : syracuseStep 1889329 = 1416997) (by norm_num)
theorem B1889365 : Blo 1678039 1889365 := bbase (se 8 (by rfl) ⟨11070, by rfl⟩ : syracuseStep 1889365 = 22141) (by norm_num)
theorem B1889401 : Blo 1678039 1889401 := bbase (se 2 (by rfl) ⟨708525, by rfl⟩ : syracuseStep 1889401 = 1417051) (by norm_num)
theorem B4248733 : Blo 1678039 4248733 := bbase (se 3 (by rfl) ⟨796637, by rfl⟩ : syracuseStep 4248733 = 1593275) (by norm_num)
theorem B1889437 : Blo 1678039 1889437 := bbase (se 3 (by rfl) ⟨354269, by rfl⟩ : syracuseStep 1889437 = 708539) (by norm_num)
theorem B1889473 : Blo 1678039 1889473 := bbase (se 2 (by rfl) ⟨708552, by rfl⟩ : syracuseStep 1889473 = 1417105) (by norm_num)
theorem B1889509 : Blo 1678039 1889509 := bbase (se 4 (by rfl) ⟨177141, by rfl⟩ : syracuseStep 1889509 = 354283) (by norm_num)
theorem B1889545 : Blo 1678039 1889545 := bbase (se 2 (by rfl) ⟨708579, by rfl⟩ : syracuseStep 1889545 = 1417159) (by norm_num)
theorem B4248845 : Blo 1678039 4248845 := bbase (se 3 (by rfl) ⟨796658, by rfl⟩ : syracuseStep 4248845 = 1593317) (by norm_num)
theorem B1889581 : Blo 1678039 1889581 := bbase (se 3 (by rfl) ⟨354296, by rfl⟩ : syracuseStep 1889581 = 708593) (by norm_num)
theorem B1889617 : Blo 1678039 1889617 := bbase (se 2 (by rfl) ⟨708606, by rfl⟩ : syracuseStep 1889617 = 1417213) (by norm_num)
theorem B5666165 : Blo 1678039 5666165 := bbase (se 5 (by rfl) ⟨265601, by rfl⟩ : syracuseStep 5666165 = 531203) (by norm_num)
theorem B1889653 : Blo 1678039 1889653 := bbase (se 5 (by rfl) ⟨88577, by rfl⟩ : syracuseStep 1889653 = 177155) (by norm_num)
theorem B1889689 : Blo 1678039 1889689 := bbase (se 2 (by rfl) ⟨708633, by rfl⟩ : syracuseStep 1889689 = 1417267) (by norm_num)
theorem B2831773 : Blo 1678039 2831773 := bbase (se 3 (by rfl) ⟨530957, by rfl⟩ : syracuseStep 2831773 = 1061915) (by norm_num)
theorem B2389429 : Blo 1678039 2389429 := bbase (se 5 (by rfl) ⟨112004, by rfl⟩ : syracuseStep 2389429 = 224009) (by norm_num)
theorem B1889725 : Blo 1678039 1889725 := bbase (se 3 (by rfl) ⟨354323, by rfl⟩ : syracuseStep 1889725 = 708647) (by norm_num)
theorem B4249037 : Blo 1678039 4249037 := bbase (se 3 (by rfl) ⟨796694, by rfl⟩ : syracuseStep 4249037 = 1593389) (by norm_num)
theorem B3585485 : Blo 1678039 3585485 := bbase (se 3 (by rfl) ⟨672278, by rfl⟩ : syracuseStep 3585485 = 1344557) (by norm_num)
theorem B1889761 : Blo 1678039 1889761 := bbase (se 2 (by rfl) ⟨708660, by rfl⟩ : syracuseStep 1889761 = 1417321) (by norm_num)
theorem B2831861 : Blo 1678039 2831861 := bbase (se 5 (by rfl) ⟨132743, by rfl⟩ : syracuseStep 2831861 = 265487) (by norm_num)
theorem B1889797 : Blo 1678039 1889797 := bbase (se 4 (by rfl) ⟨177168, by rfl⟩ : syracuseStep 1889797 = 354337) (by norm_num)
theorem B1889833 : Blo 1678039 1889833 := bbase (se 2 (by rfl) ⟨708687, by rfl⟩ : syracuseStep 1889833 = 1417375) (by norm_num)
theorem B1889869 : Blo 1678039 1889869 := bbase (se 3 (by rfl) ⟨354350, by rfl⟩ : syracuseStep 1889869 = 708701) (by norm_num)
theorem B4036189 : Blo 1678039 4036189 := bbase (se 3 (by rfl) ⟨756785, by rfl⟩ : syracuseStep 4036189 = 1513571) (by norm_num)
theorem B1889905 : Blo 1678039 1889905 := bbase (se 2 (by rfl) ⟨708714, by rfl⟩ : syracuseStep 1889905 = 1417429) (by norm_num)
theorem B2831989 : Blo 1678039 2831989 := bbase (se 5 (by rfl) ⟨132749, by rfl⟩ : syracuseStep 2831989 = 265499) (by norm_num)
theorem B1914505 : Blo 1678039 1914505 := bbase (se 2 (by rfl) ⟨717939, by rfl⟩ : syracuseStep 1914505 = 1435879) (by norm_num)
theorem B10753685 : Blo 1678039 10753685 := bbase (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) (by norm_num)
theorem B4781717 : Blo 1678039 4781717 := bbase (se 6 (by rfl) ⟨112071, by rfl⟩ : syracuseStep 4781717 = 224143) (by norm_num)
theorem B1889941 : Blo 1678039 1889941 := bbase (se 6 (by rfl) ⟨44295, by rfl⟩ : syracuseStep 1889941 = 88591) (by norm_num)
theorem B1889977 : Blo 1678039 1889977 := bbase (se 2 (by rfl) ⟨708741, by rfl⟩ : syracuseStep 1889977 = 1417483) (by norm_num)
theorem B2832077 : Blo 1678039 2832077 := bbase (se 3 (by rfl) ⟨531014, by rfl⟩ : syracuseStep 2832077 = 1062029) (by norm_num)
theorem B8500949 : Blo 1678039 8500949 := bbase (se 7 (by rfl) ⟨99620, by rfl⟩ : syracuseStep 8500949 = 199241) (by norm_num)
theorem B1890013 : Blo 1678039 1890013 := bbase (se 3 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 1890013 = 708755) (by norm_num)
theorem B2389765 : Blo 1678039 2389765 := bbase (se 4 (by rfl) ⟨224040, by rfl⟩ : syracuseStep 2389765 = 448081) (by norm_num)
theorem B1701653 : Blo 1678039 1701653 := bbase (se 6 (by rfl) ⟨39882, by rfl⟩ : syracuseStep 1701653 = 79765) (by norm_num)
theorem B4249381 : Blo 1678039 4249381 := bbase (se 4 (by rfl) ⟨398379, by rfl⟩ : syracuseStep 4249381 = 796759) (by norm_num)
theorem B5666597 : Blo 1678039 5666597 := bbase (se 4 (by rfl) ⟨531243, by rfl⟩ : syracuseStep 5666597 = 1062487) (by norm_num)
theorem B2832205 : Blo 1678039 2832205 := bbase (se 3 (by rfl) ⟨531038, by rfl⟩ : syracuseStep 2832205 = 1062077) (by norm_num)
theorem B4249493 : Blo 1678039 4249493 := bbase (se 6 (by rfl) ⟨99597, by rfl⟩ : syracuseStep 4249493 = 199195) (by norm_num)
theorem B25851797 : Blo 1678039 25851797 := bbase (se 6 (by rfl) ⟨605901, by rfl⟩ : syracuseStep 25851797 = 1211803) (by norm_num)
theorem B2832293 : Blo 1678039 2832293 := bbase (se 4 (by rfl) ⟨265527, by rfl⟩ : syracuseStep 2832293 = 531055) (by norm_num)
theorem B4601765 : Blo 1678039 4601765 := bbase (se 4 (by rfl) ⟨431415, by rfl⟩ : syracuseStep 4601765 = 862831) (by norm_num)
theorem B2389981 : Blo 1678039 2389981 := bbase (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) (by norm_num)
theorem B2832421 : Blo 1678039 2832421 := bbase (se 4 (by rfl) ⟨265539, by rfl⟩ : syracuseStep 2832421 = 531079) (by norm_num)
theorem B8067109 : Blo 1678039 8067109 := bbase (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) (by norm_num)
theorem B4782149 : Blo 1678039 4782149 := bbase (se 4 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 4782149 = 896653) (by norm_num)
theorem B9558101 : Blo 1678039 9558101 := bbase (se 8 (by rfl) ⟨56004, by rfl⟩ : syracuseStep 9558101 = 112009) (by norm_num)
theorem B4249685 : Blo 1678039 4249685 := bbase (se 8 (by rfl) ⟨24900, by rfl⟩ : syracuseStep 4249685 = 49801) (by norm_num)
theorem B1792093 : Blo 1678039 1792093 := bbase (se 3 (by rfl) ⟨336017, by rfl⟩ : syracuseStep 1792093 = 672035) (by norm_num)
theorem B2832509 : Blo 1678039 2832509 := bbase (se 3 (by rfl) ⟨531095, by rfl⟩ : syracuseStep 2832509 = 1062191) (by norm_num)
theorem B1792153 : Blo 1678039 1792153 := bbase (se 2 (by rfl) ⟨672057, by rfl⟩ : syracuseStep 1792153 = 1344115) (by norm_num)
theorem B5667029 : Blo 1678039 5667029 := bbase (se 7 (by rfl) ⟨66410, by rfl⟩ : syracuseStep 5667029 = 132821) (by norm_num)
theorem B2832637 : Blo 1678039 2832637 := bbase (se 3 (by rfl) ⟨531119, by rfl⟩ : syracuseStep 2832637 = 1062239) (by norm_num)
theorem B2726141 : Blo 1678039 2726141 := bbase (se 3 (by rfl) ⟨511151, by rfl⟩ : syracuseStep 2726141 = 1022303) (by norm_num)
theorem B3635477 : Blo 1678039 3635477 := bbase (se 6 (by rfl) ⟨85206, by rfl⟩ : syracuseStep 3635477 = 170413) (by norm_num)
theorem B1816873 : Blo 1678039 1816873 := bbase (se 2 (by rfl) ⟨681327, by rfl⟩ : syracuseStep 1816873 = 1362655) (by norm_num)
theorem B3586373 : Blo 1678039 3586373 := bbase (se 4 (by rfl) ⟨336222, by rfl⟩ : syracuseStep 3586373 = 672445) (by norm_num)
theorem B2832725 : Blo 1678039 2832725 := bbase (se 10 (by rfl) ⟨4149, by rfl⟩ : syracuseStep 2832725 = 8299) (by norm_num)
theorem B2390357 : Blo 1678039 2390357 := bbase (se 10 (by rfl) ⟨3501, by rfl⟩ : syracuseStep 2390357 = 7003) (by norm_num)
theorem B1702301 : Blo 1678039 1702301 := bbase (se 3 (by rfl) ⟨319181, by rfl⟩ : syracuseStep 1702301 = 638363) (by norm_num)
theorem B4250029 : Blo 1678039 4250029 := bbase (se 3 (by rfl) ⟨796880, by rfl⟩ : syracuseStep 4250029 = 1593761) (by norm_num)
theorem B3586493 : Blo 1678039 3586493 := bbase (se 3 (by rfl) ⟨672467, by rfl⟩ : syracuseStep 3586493 = 1344935) (by norm_num)
theorem B1792469 : Blo 1678039 1792469 := bbase (se 7 (by rfl) ⟨21005, by rfl⟩ : syracuseStep 1792469 = 42011) (by norm_num)
theorem B2832853 : Blo 1678039 2832853 := bbase (se 7 (by rfl) ⟨33197, by rfl⟩ : syracuseStep 2832853 = 66395) (by norm_num)
theorem B4250141 : Blo 1678039 4250141 := bbase (se 3 (by rfl) ⟨796901, by rfl⟩ : syracuseStep 4250141 = 1593803) (by norm_num)
theorem B2832941 : Blo 1678039 2832941 := bbase (se 3 (by rfl) ⟨531176, by rfl⟩ : syracuseStep 2832941 = 1062353) (by norm_num)
theorem B4307525 : Blo 1678039 4307525 := bbase (se 4 (by rfl) ⟨403830, by rfl⟩ : syracuseStep 4307525 = 807661) (by norm_num)
theorem B5667461 : Blo 1678039 5667461 := bbase (se 4 (by rfl) ⟨531324, by rfl⟩ : syracuseStep 5667461 = 1062649) (by norm_num)
theorem B2833069 : Blo 1678039 2833069 := bbase (se 3 (by rfl) ⟨531200, by rfl⟩ : syracuseStep 2833069 = 1062401) (by norm_num)
theorem B1940149 : Blo 1678039 1940149 := bbase (se 5 (by rfl) ⟨90944, by rfl⟩ : syracuseStep 1940149 = 181889) (by norm_num)
theorem B6372053 : Blo 1678039 6372053 := bbase (se 7 (by rfl) ⟨74672, by rfl⟩ : syracuseStep 6372053 = 149345) (by norm_num)
theorem B4250333 : Blo 1678039 4250333 := bbase (se 3 (by rfl) ⟨796937, by rfl⟩ : syracuseStep 4250333 = 1593875) (by norm_num)
theorem B2833157 : Blo 1678039 2833157 := bbase (se 4 (by rfl) ⟨265608, by rfl⟩ : syracuseStep 2833157 = 531217) (by norm_num)
theorem B4782901 : Blo 1678039 4782901 := bbase (se 5 (by rfl) ⟨224198, by rfl⟩ : syracuseStep 4782901 = 448397) (by norm_num)
theorem B8616773 : Blo 1678039 8616773 := bbase (se 4 (by rfl) ⟨807822, by rfl⟩ : syracuseStep 8616773 = 1615645) (by norm_num)
theorem B2833285 : Blo 1678039 2833285 := bbase (se 4 (by rfl) ⟨265620, by rfl⟩ : syracuseStep 2833285 = 531241) (by norm_num)
theorem B1792913 : Blo 1678039 1792913 := bbase (se 2 (by rfl) ⟨672342, by rfl⟩ : syracuseStep 1792913 = 1344685) (by norm_num)
theorem B1792973 : Blo 1678039 1792973 := bbase (se 3 (by rfl) ⟨336182, by rfl⟩ : syracuseStep 1792973 = 672365) (by norm_num)
theorem B8616917 : Blo 1678039 8616917 := bbase (se 7 (by rfl) ⟨100979, by rfl⟩ : syracuseStep 8616917 = 201959) (by norm_num)
theorem B2833373 : Blo 1678039 2833373 := bbase (se 3 (by rfl) ⟨531257, by rfl⟩ : syracuseStep 2833373 = 1062515) (by norm_num)
theorem B8502245 : Blo 1678039 8502245 := bbase (se 4 (by rfl) ⟨797085, by rfl⟩ : syracuseStep 8502245 = 1594171) (by norm_num)
theorem B2153453 : Blo 1678039 2153453 := bbase (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) (by norm_num)
theorem B6372341 : Blo 1678039 6372341 := bbase (se 5 (by rfl) ⟨298703, by rfl⟩ : syracuseStep 6372341 = 597407) (by norm_num)
theorem B3185669 : Blo 1678039 3185669 := bbase (se 4 (by rfl) ⟨298656, by rfl⟩ : syracuseStep 3185669 = 597313) (by norm_num)
theorem B1702921 : Blo 1678039 1702921 := bbase (se 2 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 1702921 = 1277191) (by norm_num)
theorem B4250677 : Blo 1678039 4250677 := bbase (se 5 (by rfl) ⟨199250, by rfl⟩ : syracuseStep 4250677 = 398501) (by norm_num)
theorem B5667893 : Blo 1678039 5667893 := bbase (se 5 (by rfl) ⟨265682, by rfl⟩ : syracuseStep 5667893 = 531365) (by norm_num)
theorem B3587125 : Blo 1678039 3587125 := bbase (se 5 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 3587125 = 336293) (by norm_num)
theorem B1793101 : Blo 1678039 1793101 := bbase (se 3 (by rfl) ⟨336206, by rfl⟩ : syracuseStep 1793101 = 672413) (by norm_num)
theorem B2833501 : Blo 1678039 2833501 := bbase (se 3 (by rfl) ⟨531281, by rfl⟩ : syracuseStep 2833501 = 1062563) (by norm_num)
theorem B3775589 : Blo 1678039 3775589 := bbase (se 4 (by rfl) ⟨353961, by rfl⟩ : syracuseStep 3775589 = 707923) (by norm_num)
theorem B3185821 : Blo 1678039 3185821 := bbase (se 3 (by rfl) ⟨597341, by rfl⟩ : syracuseStep 3185821 = 1194683) (by norm_num)
theorem B4250789 : Blo 1678039 4250789 := bbase (se 4 (by rfl) ⟨398511, by rfl⟩ : syracuseStep 4250789 = 797023) (by norm_num)
theorem B3775661 : Blo 1678039 3775661 := bbase (se 3 (by rfl) ⟨707936, by rfl⟩ : syracuseStep 3775661 = 1415873) (by norm_num)
theorem B2833589 : Blo 1678039 2833589 := bbase (se 5 (by rfl) ⟨132824, by rfl⟩ : syracuseStep 2833589 = 265649) (by norm_num)
theorem B3775733 : Blo 1678039 3775733 := bbase (se 5 (by rfl) ⟨176987, by rfl⟩ : syracuseStep 3775733 = 353975) (by norm_num)
theorem B10206485 : Blo 1678039 10206485 := bbase (se 6 (by rfl) ⟨239214, by rfl⟩ : syracuseStep 10206485 = 478429) (by norm_num)
theorem B2424109 : Blo 1678039 2424109 := bbase (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) (by norm_num)
theorem B2833717 : Blo 1678039 2833717 := bbase (se 5 (by rfl) ⟨132830, by rfl⟩ : syracuseStep 2833717 = 265661) (by norm_num)
theorem B3775805 : Blo 1678039 3775805 := bbase (se 3 (by rfl) ⟨707963, by rfl⟩ : syracuseStep 3775805 = 1415927) (by norm_num)
theorem B1817929 : Blo 1678039 1817929 := bbase (se 2 (by rfl) ⟨681723, by rfl⟩ : syracuseStep 1817929 = 1363447) (by norm_num)
theorem B4250981 : Blo 1678039 4250981 := bbase (se 4 (by rfl) ⟨398529, by rfl⟩ : syracuseStep 4250981 = 797059) (by norm_num)
theorem B3775877 : Blo 1678039 3775877 := bbase (se 4 (by rfl) ⟨353988, by rfl⟩ : syracuseStep 3775877 = 707977) (by norm_num)
theorem B2833805 : Blo 1678039 2833805 := bbase (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) (by norm_num)
theorem B3775949 : Blo 1678039 3775949 := bbase (se 3 (by rfl) ⟨707990, by rfl⟩ : syracuseStep 3775949 = 1415981) (by norm_num)
theorem B3186125 : Blo 1678039 3186125 := bbase (se 3 (by rfl) ⟨597398, by rfl⟩ : syracuseStep 3186125 = 1194797) (by norm_num)
theorem B5668325 : Blo 1678039 5668325 := bbase (se 4 (by rfl) ⟨531405, by rfl⟩ : syracuseStep 5668325 = 1062811) (by norm_num)
theorem B1793545 : Blo 1678039 1793545 := bbase (se 2 (by rfl) ⟨672579, by rfl⟩ : syracuseStep 1793545 = 1345159) (by norm_num)
theorem B2833933 : Blo 1678039 2833933 := bbase (se 3 (by rfl) ⟨531362, by rfl⟩ : syracuseStep 2833933 = 1062725) (by norm_num)
theorem B3776021 : Blo 1678039 3776021 := bbase (se 6 (by rfl) ⟨88500, by rfl⟩ : syracuseStep 3776021 = 177001) (by norm_num)
theorem B3776093 : Blo 1678039 3776093 := bbase (se 3 (by rfl) ⟨708017, by rfl⟩ : syracuseStep 3776093 = 1416035) (by norm_num)
theorem B3636829 : Blo 1678039 3636829 := bbase (se 3 (by rfl) ⟨681905, by rfl⟩ : syracuseStep 3636829 = 1363811) (by norm_num)
theorem B7183973 : Blo 1678039 7183973 := bbase (se 4 (by rfl) ⟨673497, by rfl⟩ : syracuseStep 7183973 = 1346995) (by norm_num)
theorem B2834021 : Blo 1678039 2834021 := bbase (se 4 (by rfl) ⟨265689, by rfl⟩ : syracuseStep 2834021 = 531379) (by norm_num)
theorem B1793665 : Blo 1678039 1793665 := bbase (se 2 (by rfl) ⟨672624, by rfl⟩ : syracuseStep 1793665 = 1345249) (by norm_num)
theorem B3776165 : Blo 1678039 3776165 := bbase (se 4 (by rfl) ⟨354015, by rfl⟩ : syracuseStep 3776165 = 708031) (by norm_num)
theorem B1818293 : Blo 1678039 1818293 := bbase (se 5 (by rfl) ⟨85232, by rfl⟩ : syracuseStep 1818293 = 170465) (by norm_num)
theorem B4251325 : Blo 1678039 4251325 := bbase (se 3 (by rfl) ⟨797123, by rfl⟩ : syracuseStep 4251325 = 1594247) (by norm_num)
theorem B3546821 : Blo 1678039 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B2834149 : Blo 1678039 2834149 := bbase (se 4 (by rfl) ⟨265701, by rfl⟩ : syracuseStep 2834149 = 531403) (by norm_num)
theorem B2391781 : Blo 1678039 2391781 := bbase (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) (by norm_num)
theorem B3776237 : Blo 1678039 3776237 := bbase (se 3 (by rfl) ⟨708044, by rfl⟩ : syracuseStep 3776237 = 1416089) (by norm_num)
theorem B9567989 : Blo 1678039 9567989 := bbase (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) (by norm_num)
theorem B4251437 : Blo 1678039 4251437 := bbase (se 3 (by rfl) ⟨797144, by rfl⟩ : syracuseStep 4251437 = 1594289) (by norm_num)
theorem B3776309 : Blo 1678039 3776309 := bbase (se 5 (by rfl) ⟨177014, by rfl⟩ : syracuseStep 3776309 = 354029) (by norm_num)
theorem B2834237 : Blo 1678039 2834237 := bbase (se 3 (by rfl) ⟨531419, by rfl⟩ : syracuseStep 2834237 = 1062839) (by norm_num)
theorem B5381957 : Blo 1678039 5381957 := bbase (se 4 (by rfl) ⟨504558, by rfl⟩ : syracuseStep 5381957 = 1009117) (by norm_num)
theorem B3776381 : Blo 1678039 3776381 := bbase (se 3 (by rfl) ⟨708071, by rfl⟩ : syracuseStep 3776381 = 1416143) (by norm_num)
theorem B1793917 : Blo 1678039 1793917 := bbase (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) (by norm_num)
theorem B1793921 : Blo 1678039 1793921 := bbase (se 2 (by rfl) ⟨672720, by rfl⟩ : syracuseStep 1793921 = 1345441) (by norm_num)
theorem B5668757 : Blo 1678039 5668757 := bbase (se 6 (by rfl) ⟨132861, by rfl⟩ : syracuseStep 5668757 = 265723) (by norm_num)
theorem B3588013 : Blo 1678039 3588013 := bbase (se 3 (by rfl) ⟨672752, by rfl⟩ : syracuseStep 3588013 = 1345505) (by norm_num)
theorem B2834365 : Blo 1678039 2834365 := bbase (se 3 (by rfl) ⟨531443, by rfl⟩ : syracuseStep 2834365 = 1062887) (by norm_num)
theorem B3776453 : Blo 1678039 3776453 := bbase (se 4 (by rfl) ⟨354042, by rfl⟩ : syracuseStep 3776453 = 708085) (by norm_num)
theorem B4251629 : Blo 1678039 4251629 := bbase (se 3 (by rfl) ⟨797180, by rfl⟩ : syracuseStep 4251629 = 1594361) (by norm_num)
theorem B1679363 : Blo 1678039 1679363 := bstep (se 1 (by rfl) ⟨1259522, by rfl⟩ : syracuseStep 1679363 = 2519045) B2519045
theorem B8495117 : Blo 1678039 8495117 := bstep (se 3 (by rfl) ⟨1592834, by rfl⟩ : syracuseStep 8495117 = 3185669) B3185669
theorem B1679379 : Blo 1678039 1679379 := bstep (se 1 (by rfl) ⟨1259534, by rfl⟩ : syracuseStep 1679379 = 2519069) B2519069
theorem B1679395 : Blo 1678039 1679395 := bstep (se 1 (by rfl) ⟨1259546, by rfl⟩ : syracuseStep 1679395 = 2519093) B2519093
theorem B10764323 : Blo 1678039 10764323 := bstep (se 1 (by rfl) ⟨8073242, by rfl⟩ : syracuseStep 10764323 = 16146485) B16146485
theorem B3776561 : Blo 1678039 3776561 := bstep (se 2 (by rfl) ⟨1416210, by rfl⟩ : syracuseStep 3776561 = 2832421) B2832421
theorem B10756145 : Blo 1678039 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B1679411 : Blo 1678039 1679411 := bstep (se 1 (by rfl) ⟨1259558, by rfl⟩ : syracuseStep 1679411 = 2519117) B2519117
theorem B4784177 : Blo 1678039 4784177 := bstep (se 2 (by rfl) ⟨1794066, by rfl⟩ : syracuseStep 4784177 = 3588133) B3588133
theorem B3776579 : Blo 1678039 3776579 := bstep (se 1 (by rfl) ⟨2832434, by rfl⟩ : syracuseStep 3776579 = 5664869) B5664869
theorem B1679427 : Blo 1678039 1679427 := bstep (se 1 (by rfl) ⟨1259570, by rfl⟩ : syracuseStep 1679427 = 2519141) B2519141
theorem B1679443 : Blo 1678039 1679443 := bstep (se 1 (by rfl) ⟨1259582, by rfl⟩ : syracuseStep 1679443 = 2519165) B2519165
theorem B1679459 : Blo 1678039 1679459 := bstep (se 1 (by rfl) ⟨1259594, by rfl⟩ : syracuseStep 1679459 = 2519189) B2519189
theorem B5668973 : Blo 1678039 5668973 := bstep (se 3 (by rfl) ⟨1062932, by rfl⟩ : syracuseStep 5668973 = 2125865) B2125865
theorem B4251761 : Blo 1678039 4251761 := bstep (se 2 (by rfl) ⟨1594410, by rfl⟩ : syracuseStep 4251761 = 3188821) B3188821
theorem B1679475 : Blo 1678039 1679475 := bstep (se 1 (by rfl) ⟨1259606, by rfl⟩ : syracuseStep 1679475 = 2519213) B2519213
theorem B2834561 : Blo 1678039 2834561 := bstep (se 2 (by rfl) ⟨1062960, by rfl⟩ : syracuseStep 2834561 = 2125921) B2125921
theorem B1679491 : Blo 1678039 1679491 := bstep (se 1 (by rfl) ⟨1259618, by rfl⟩ : syracuseStep 1679491 = 2519237) B2519237
theorem B1679507 : Blo 1678039 1679507 := bstep (se 1 (by rfl) ⟨1259630, by rfl⟩ : syracuseStep 1679507 = 2519261) B2519261
theorem B1679523 : Blo 1678039 1679523 := bstep (se 1 (by rfl) ⟨1259642, by rfl⟩ : syracuseStep 1679523 = 2519285) B2519285
theorem B5669027 : Blo 1678039 5669027 := bstep (se 1 (by rfl) ⟨4251770, by rfl⟩ : syracuseStep 5669027 = 8503541) B8503541
theorem B4251811 : Blo 1678039 4251811 := bstep (se 1 (by rfl) ⟨3188858, by rfl⟩ : syracuseStep 4251811 = 6377717) B6377717
theorem B1679539 : Blo 1678039 1679539 := bstep (se 1 (by rfl) ⟨1259654, by rfl⟩ : syracuseStep 1679539 = 2519309) B2519309
theorem B1679555 : Blo 1678039 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B1679571 : Blo 1678039 1679571 := bstep (se 1 (by rfl) ⟨1259678, by rfl⟩ : syracuseStep 1679571 = 2519357) B2519357
theorem B1679587 : Blo 1678039 1679587 := bstep (se 1 (by rfl) ⟨1259690, by rfl⟩ : syracuseStep 1679587 = 2519381) B2519381
theorem B1679603 : Blo 1678039 1679603 := bstep (se 1 (by rfl) ⟨1259702, by rfl⟩ : syracuseStep 1679603 = 2519405) B2519405
theorem B2834689 : Blo 1678039 2834689 := bstep (se 2 (by rfl) ⟨1063008, by rfl⟩ : syracuseStep 2834689 = 2126017) B2126017
theorem B1679619 : Blo 1678039 1679619 := bstep (se 1 (by rfl) ⟨1259714, by rfl⟩ : syracuseStep 1679619 = 2519429) B2519429
theorem B1679635 : Blo 1678039 1679635 := bstep (se 1 (by rfl) ⟨1259726, by rfl⟩ : syracuseStep 1679635 = 2519453) B2519453
theorem B1679651 : Blo 1678039 1679651 := bstep (se 1 (by rfl) ⟨1259738, by rfl⟩ : syracuseStep 1679651 = 2519477) B2519477
theorem B2834723 : Blo 1678039 2834723 := bstep (se 1 (by rfl) ⟨2126042, by rfl⟩ : syracuseStep 2834723 = 4252085) B4252085
theorem B4251953 : Blo 1678039 4251953 := bstep (se 2 (by rfl) ⟨1594482, by rfl⟩ : syracuseStep 4251953 = 3188965) B3188965
theorem B1679667 : Blo 1678039 1679667 := bstep (se 1 (by rfl) ⟨1259750, by rfl⟩ : syracuseStep 1679667 = 2519501) B2519501
theorem B1679683 : Blo 1678039 1679683 := bstep (se 1 (by rfl) ⟨1259762, by rfl⟩ : syracuseStep 1679683 = 2519525) B2519525
theorem B3776849 : Blo 1678039 3776849 := bstep (se 2 (by rfl) ⟨1416318, by rfl⟩ : syracuseStep 3776849 = 2832637) B2832637
theorem B1679699 : Blo 1678039 1679699 := bstep (se 1 (by rfl) ⟨1259774, by rfl⟩ : syracuseStep 1679699 = 2519549) B2519549
theorem B3776867 : Blo 1678039 3776867 := bstep (se 1 (by rfl) ⟨2832650, by rfl⟩ : syracuseStep 3776867 = 5665301) B5665301
theorem B1679715 : Blo 1678039 1679715 := bstep (se 1 (by rfl) ⟨1259786, by rfl⟩ : syracuseStep 1679715 = 2519573) B2519573
theorem B25837937 : Blo 1678039 25837937 := bstep (se 2 (by rfl) ⟨9689226, by rfl⟩ : syracuseStep 25837937 = 19378453) B19378453
theorem B1679731 : Blo 1678039 1679731 := bstep (se 1 (by rfl) ⟨1259798, by rfl⟩ : syracuseStep 1679731 = 2519597) B2519597
theorem B1679747 : Blo 1678039 1679747 := bstep (se 1 (by rfl) ⟨1259810, by rfl⟩ : syracuseStep 1679747 = 2519621) B2519621
theorem B1679763 : Blo 1678039 1679763 := bstep (se 1 (by rfl) ⟨1259822, by rfl⟩ : syracuseStep 1679763 = 2519645) B2519645
theorem B1679779 : Blo 1678039 1679779 := bstep (se 1 (by rfl) ⟨1259834, by rfl⟩ : syracuseStep 1679779 = 2519669) B2519669
theorem B2834851 : Blo 1678039 2834851 := bstep (se 1 (by rfl) ⟨2126138, by rfl⟩ : syracuseStep 2834851 = 4252277) B4252277
theorem B5669297 : Blo 1678039 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B1679795 : Blo 1678039 1679795 := bstep (se 1 (by rfl) ⟨1259846, by rfl⟩ : syracuseStep 1679795 = 2519693) B2519693
theorem B1679811 : Blo 1678039 1679811 := bstep (se 1 (by rfl) ⟨1259858, by rfl⟩ : syracuseStep 1679811 = 2519717) B2519717
theorem B1679827 : Blo 1678039 1679827 := bstep (se 1 (by rfl) ⟨1259870, by rfl⟩ : syracuseStep 1679827 = 2519741) B2519741
theorem B1679843 : Blo 1678039 1679843 := bstep (se 1 (by rfl) ⟨1259882, by rfl⟩ : syracuseStep 1679843 = 2519765) B2519765
theorem B1679859 : Blo 1678039 1679859 := bstep (se 1 (by rfl) ⟨1259894, by rfl⟩ : syracuseStep 1679859 = 2519789) B2519789
theorem B1679875 : Blo 1678039 1679875 := bstep (se 1 (by rfl) ⟨1259906, by rfl⟩ : syracuseStep 1679875 = 2519813) B2519813
theorem B1679891 : Blo 1678039 1679891 := bstep (se 1 (by rfl) ⟨1259918, by rfl⟩ : syracuseStep 1679891 = 2519837) B2519837
theorem B1679907 : Blo 1678039 1679907 := bstep (se 1 (by rfl) ⟨1259930, by rfl⟩ : syracuseStep 1679907 = 2519861) B2519861
theorem B2834993 : Blo 1678039 2834993 := bstep (se 2 (by rfl) ⟨1063122, by rfl⟩ : syracuseStep 2834993 = 2126245) B2126245
theorem B1679923 : Blo 1678039 1679923 := bstep (se 1 (by rfl) ⟨1259942, by rfl⟩ : syracuseStep 1679923 = 2519885) B2519885
theorem B2155075 : Blo 1678039 2155075 := bstep (se 1 (by rfl) ⟨1616306, by rfl⟩ : syracuseStep 2155075 = 3232613) B3232613
theorem B1679939 : Blo 1678039 1679939 := bstep (se 1 (by rfl) ⟨1259954, by rfl⟩ : syracuseStep 1679939 = 2519909) B2519909
theorem B1679955 : Blo 1678039 1679955 := bstep (se 1 (by rfl) ⟨1259966, by rfl⟩ : syracuseStep 1679955 = 2519933) B2519933
theorem B13615715 : Blo 1678039 13615715 := bstep (se 1 (by rfl) ⟨10211786, by rfl⟩ : syracuseStep 13615715 = 20423573) B20423573
theorem B2269795 : Blo 1678039 2269795 := bstep (se 1 (by rfl) ⟨1702346, by rfl⟩ : syracuseStep 2269795 = 3404693) B3404693
theorem B12755555 : Blo 1678039 12755555 := bstep (se 1 (by rfl) ⟨9566666, by rfl⟩ : syracuseStep 12755555 = 19133333) B19133333
theorem B1679971 : Blo 1678039 1679971 := bstep (se 1 (by rfl) ⟨1259978, by rfl⟩ : syracuseStep 1679971 = 2519957) B2519957
theorem B3777137 : Blo 1678039 3777137 := bstep (se 2 (by rfl) ⟨1416426, by rfl⟩ : syracuseStep 3777137 = 2832853) B2832853
theorem B1679987 : Blo 1678039 1679987 := bstep (se 1 (by rfl) ⟨1259990, by rfl⟩ : syracuseStep 1679987 = 2519981) B2519981
theorem B3777155 : Blo 1678039 3777155 := bstep (se 1 (by rfl) ⟨2832866, by rfl⟩ : syracuseStep 3777155 = 5665733) B5665733
theorem B1680003 : Blo 1678039 1680003 := bstep (se 1 (by rfl) ⟨1260002, by rfl⟩ : syracuseStep 1680003 = 2520005) B2520005
theorem B1680019 : Blo 1678039 1680019 := bstep (se 1 (by rfl) ⟨1260014, by rfl⟩ : syracuseStep 1680019 = 2520029) B2520029
theorem B3187363 : Blo 1678039 3187363 := bstep (se 1 (by rfl) ⟨2390522, by rfl⟩ : syracuseStep 3187363 = 4781045) B4781045
theorem B1680035 : Blo 1678039 1680035 := bstep (se 1 (by rfl) ⟨1260026, by rfl⟩ : syracuseStep 1680035 = 2520053) B2520053
theorem B4309699 : Blo 1678039 4309699 := bstep (se 1 (by rfl) ⟨3232274, by rfl⟩ : syracuseStep 4309699 = 6464549) B6464549
theorem B27984611 : Blo 1678039 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B5104433 : Blo 1678039 5104433 := bstep (se 2 (by rfl) ⟨1914162, by rfl⟩ : syracuseStep 5104433 = 3828325) B3828325
theorem B6374285 : Blo 1678039 6374285 := bstep (se 3 (by rfl) ⟨1195178, by rfl⟩ : syracuseStep 6374285 = 2390357) B2390357
theorem B3777425 : Blo 1678039 3777425 := bstep (se 2 (by rfl) ⟨1416534, by rfl⟩ : syracuseStep 3777425 = 2833069) B2833069
theorem B3777443 : Blo 1678039 3777443 := bstep (se 1 (by rfl) ⟨2833082, by rfl⟩ : syracuseStep 3777443 = 5666165) B5666165
theorem B4309937 : Blo 1678039 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B10757069 : Blo 1678039 10757069 := bstep (se 3 (by rfl) ⟨2016950, by rfl⟩ : syracuseStep 10757069 = 4033901) B4033901
theorem B5669837 : Blo 1678039 5669837 := bstep (se 3 (by rfl) ⟨1063094, by rfl⟩ : syracuseStep 5669837 = 2126189) B2126189
theorem B5669891 : Blo 1678039 5669891 := bstep (se 1 (by rfl) ⟨4252418, by rfl⟩ : syracuseStep 5669891 = 8504837) B8504837
theorem B7169123 : Blo 1678039 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B2016355 : Blo 1678039 2016355 := bstep (se 1 (by rfl) ⟨1512266, by rfl⟩ : syracuseStep 2016355 = 3024533) B3024533
theorem B3187811 : Blo 1678039 3187811 := bstep (se 1 (by rfl) ⟨2390858, by rfl⟩ : syracuseStep 3187811 = 4781717) B4781717
theorem B3777713 : Blo 1678039 3777713 := bstep (se 2 (by rfl) ⟨1416642, by rfl⟩ : syracuseStep 3777713 = 2833285) B2833285
theorem B3777731 : Blo 1678039 3777731 := bstep (se 1 (by rfl) ⟨2833298, by rfl⟩ : syracuseStep 3777731 = 5666597) B5666597
theorem B2270561 : Blo 1678039 2270561 := bstep (se 2 (by rfl) ⟨851460, by rfl⟩ : syracuseStep 2270561 = 1702921) B1702921
theorem B8504675 : Blo 1678039 8504675 := bstep (se 1 (by rfl) ⟨6378506, by rfl⟩ : syracuseStep 8504675 = 12757013) B12757013
theorem B3188099 : Blo 1678039 3188099 := bstep (se 1 (by rfl) ⟨2391074, by rfl⟩ : syracuseStep 3188099 = 4782149) B4782149
theorem B3778001 : Blo 1678039 3778001 := bstep (se 2 (by rfl) ⟨1416750, by rfl⟩ : syracuseStep 3778001 = 2833501) B2833501
theorem B2016739 : Blo 1678039 2016739 := bstep (se 1 (by rfl) ⟨1512554, by rfl⟩ : syracuseStep 2016739 = 3025109) B3025109
theorem B3778019 : Blo 1678039 3778019 := bstep (se 1 (by rfl) ⟨2833514, by rfl⟩ : syracuseStep 3778019 = 5667029) B5667029
theorem B18155107 : Blo 1678039 18155107 := bstep (se 1 (by rfl) ⟨13616330, by rfl⟩ : syracuseStep 18155107 = 27232661) B27232661
theorem B3778289 : Blo 1678039 3778289 := bstep (se 2 (by rfl) ⟨1416858, by rfl⟩ : syracuseStep 3778289 = 2833717) B2833717
theorem B3778307 : Blo 1678039 3778307 := bstep (se 1 (by rfl) ⟨2833730, by rfl⟩ : syracuseStep 3778307 = 5667461) B5667461
theorem B5744515 : Blo 1678039 5744515 := bstep (se 1 (by rfl) ⟨4308386, by rfl⟩ : syracuseStep 5744515 = 8616773) B8616773
theorem B4032401 : Blo 1678039 4032401 := bstep (se 2 (by rfl) ⟨1512150, by rfl⟩ : syracuseStep 4032401 = 3024301) B3024301
theorem B5744611 : Blo 1678039 5744611 := bstep (se 1 (by rfl) ⟨4308458, by rfl⟩ : syracuseStep 5744611 = 8616917) B8616917
theorem B3778577 : Blo 1678039 3778577 := bstep (se 2 (by rfl) ⟨1416966, by rfl⟩ : syracuseStep 3778577 = 2833933) B2833933
theorem B3778595 : Blo 1678039 3778595 := bstep (se 1 (by rfl) ⟨2833946, by rfl⟩ : syracuseStep 3778595 = 5667893) B5667893
theorem B65415221 : Blo 1678039 65415221 := bstep (se 5 (by rfl) ⟨3066338, by rfl⟩ : syracuseStep 65415221 = 6132677) B6132677
theorem B2517059 : Blo 1678039 2517059 := bstep (se 1 (by rfl) ⟨1887794, by rfl⟩ : syracuseStep 2517059 = 3775589) B3775589
theorem B2517089 : Blo 1678039 2517089 := bstep (se 2 (by rfl) ⟨943908, by rfl⟩ : syracuseStep 2517089 = 1887817) B1887817
theorem B2517107 : Blo 1678039 2517107 := bstep (se 1 (by rfl) ⟨1887830, by rfl⟩ : syracuseStep 2517107 = 3775661) B3775661
theorem B2689139 : Blo 1678039 2689139 := bstep (se 1 (by rfl) ⟨2016854, by rfl⟩ : syracuseStep 2689139 = 4033709) B4033709
theorem B2517137 : Blo 1678039 2517137 := bstep (se 2 (by rfl) ⟨943926, by rfl⟩ : syracuseStep 2517137 = 1887853) B1887853
theorem B2517155 : Blo 1678039 2517155 := bstep (se 1 (by rfl) ⟨1887866, by rfl⟩ : syracuseStep 2517155 = 3775733) B3775733
theorem B2517185 : Blo 1678039 2517185 := bstep (se 2 (by rfl) ⟨943944, by rfl⟩ : syracuseStep 2517185 = 1887889) B1887889
theorem B2517203 : Blo 1678039 2517203 := bstep (se 1 (by rfl) ⟨1887902, by rfl⟩ : syracuseStep 2517203 = 3775805) B3775805
theorem B2517233 : Blo 1678039 2517233 := bstep (se 2 (by rfl) ⟨943962, by rfl⟩ : syracuseStep 2517233 = 1887925) B1887925
theorem B2517251 : Blo 1678039 2517251 := bstep (se 1 (by rfl) ⟨1887938, by rfl⟩ : syracuseStep 2517251 = 3775877) B3775877
theorem B5449997 : Blo 1678039 5449997 := bstep (se 3 (by rfl) ⟨1021874, by rfl⟩ : syracuseStep 5449997 = 2043749) B2043749
theorem B2517281 : Blo 1678039 2517281 := bstep (se 2 (by rfl) ⟨943980, by rfl⟩ : syracuseStep 2517281 = 1887961) B1887961
theorem B7170353 : Blo 1678039 7170353 := bstep (se 2 (by rfl) ⟨2688882, by rfl⟩ : syracuseStep 7170353 = 5377765) B5377765
theorem B2517299 : Blo 1678039 2517299 := bstep (se 1 (by rfl) ⟨1887974, by rfl⟩ : syracuseStep 2517299 = 3775949) B3775949
theorem B2124083 : Blo 1678039 2124083 := bstep (se 1 (by rfl) ⟨1593062, by rfl⟩ : syracuseStep 2124083 = 3186125) B3186125
theorem B3778865 : Blo 1678039 3778865 := bstep (se 2 (by rfl) ⟨1417074, by rfl⟩ : syracuseStep 3778865 = 2834149) B2834149
theorem B3189041 : Blo 1678039 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B3778883 : Blo 1678039 3778883 := bstep (se 1 (by rfl) ⟨2834162, by rfl⟩ : syracuseStep 3778883 = 5668325) B5668325
theorem B2517329 : Blo 1678039 2517329 := bstep (se 2 (by rfl) ⟨943998, by rfl⟩ : syracuseStep 2517329 = 1887997) B1887997
theorem B2517347 : Blo 1678039 2517347 := bstep (se 1 (by rfl) ⟨1888010, by rfl⟩ : syracuseStep 2517347 = 3776021) B3776021
theorem B2517377 : Blo 1678039 2517377 := bstep (se 2 (by rfl) ⟨944016, by rfl⟩ : syracuseStep 2517377 = 1888033) B1888033
theorem B2517395 : Blo 1678039 2517395 := bstep (se 1 (by rfl) ⟨1888046, by rfl⟩ : syracuseStep 2517395 = 3776093) B3776093
theorem B4032931 : Blo 1678039 4032931 := bstep (se 1 (by rfl) ⟨3024698, by rfl⟩ : syracuseStep 4032931 = 6049397) B6049397
theorem B2517425 : Blo 1678039 2517425 := bstep (se 2 (by rfl) ⟨944034, by rfl⟩ : syracuseStep 2517425 = 1888069) B1888069
theorem B2517443 : Blo 1678039 2517443 := bstep (se 1 (by rfl) ⟨1888082, by rfl⟩ : syracuseStep 2517443 = 3776165) B3776165
theorem B2517473 : Blo 1678039 2517473 := bstep (se 2 (by rfl) ⟨944052, by rfl⟩ : syracuseStep 2517473 = 1888105) B1888105
theorem B2517491 : Blo 1678039 2517491 := bstep (se 1 (by rfl) ⟨1888118, by rfl⟩ : syracuseStep 2517491 = 3776237) B3776237
theorem B2517521 : Blo 1678039 2517521 := bstep (se 2 (by rfl) ⟨944070, by rfl⟩ : syracuseStep 2517521 = 1888141) B1888141
theorem B2517539 : Blo 1678039 2517539 := bstep (se 1 (by rfl) ⟨1888154, by rfl⟩ : syracuseStep 2517539 = 3776309) B3776309
theorem B2517569 : Blo 1678039 2517569 := bstep (se 2 (by rfl) ⟨944088, by rfl⟩ : syracuseStep 2517569 = 1888177) B1888177
theorem B3779153 : Blo 1678039 3779153 := bstep (se 2 (by rfl) ⟨1417182, by rfl⟩ : syracuseStep 3779153 = 2834365) B2834365
theorem B2517587 : Blo 1678039 2517587 := bstep (se 1 (by rfl) ⟨1888190, by rfl⟩ : syracuseStep 2517587 = 3776381) B3776381
theorem B3779171 : Blo 1678039 3779171 := bstep (se 1 (by rfl) ⟨2834378, by rfl⟩ : syracuseStep 3779171 = 5668757) B5668757
theorem B2517617 : Blo 1678039 2517617 := bstep (se 2 (by rfl) ⟨944106, by rfl⟩ : syracuseStep 2517617 = 1888213) B1888213
theorem B2517635 : Blo 1678039 2517635 := bstep (se 1 (by rfl) ⟨1888226, by rfl⟩ : syracuseStep 2517635 = 3776453) B3776453
theorem B3066499 : Blo 1678039 3066499 := bstep (se 1 (by rfl) ⟨2299874, by rfl⟩ : syracuseStep 3066499 = 4599749) B4599749
theorem B2517665 : Blo 1678039 2517665 := bstep (se 2 (by rfl) ⟨944124, by rfl⟩ : syracuseStep 2517665 = 1888249) B1888249
theorem B5376689 : Blo 1678039 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B2517683 : Blo 1678039 2517683 := bstep (se 1 (by rfl) ⟨1888262, by rfl⟩ : syracuseStep 2517683 = 3776525) B3776525
theorem B2517713 : Blo 1678039 2517713 := bstep (se 2 (by rfl) ⟨944142, by rfl⟩ : syracuseStep 2517713 = 1888285) B1888285
theorem B2517731 : Blo 1678039 2517731 := bstep (se 1 (by rfl) ⟨1888298, by rfl⟩ : syracuseStep 2517731 = 3776597) B3776597
theorem B2763491 : Blo 1678039 2763491 := bstep (se 1 (by rfl) ⟨2072618, by rfl⟩ : syracuseStep 2763491 = 4145237) B4145237
theorem B2517761 : Blo 1678039 2517761 := bstep (se 2 (by rfl) ⟨944160, by rfl⟩ : syracuseStep 2517761 = 1888321) B1888321
theorem B2517779 : Blo 1678039 2517779 := bstep (se 1 (by rfl) ⟨1888334, by rfl⟩ : syracuseStep 2517779 = 3776669) B3776669
theorem B4778801 : Blo 1678039 4778801 := bstep (se 2 (by rfl) ⟨1792050, by rfl⟩ : syracuseStep 4778801 = 3584101) B3584101
theorem B2517809 : Blo 1678039 2517809 := bstep (se 2 (by rfl) ⟨944178, by rfl⟩ : syracuseStep 2517809 = 1888357) B1888357
theorem B2517827 : Blo 1678039 2517827 := bstep (se 1 (by rfl) ⟨1888370, by rfl⟩ : syracuseStep 2517827 = 3776741) B3776741
theorem B2517857 : Blo 1678039 2517857 := bstep (se 2 (by rfl) ⟨944196, by rfl⟩ : syracuseStep 2517857 = 1888393) B1888393
theorem B8498033 : Blo 1678039 8498033 := bstep (se 2 (by rfl) ⟨3186762, by rfl⟩ : syracuseStep 8498033 = 6373525) B6373525
theorem B3779441 : Blo 1678039 3779441 := bstep (se 2 (by rfl) ⟨1417290, by rfl⟩ : syracuseStep 3779441 = 2834581) B2834581
theorem B2517875 : Blo 1678039 2517875 := bstep (se 1 (by rfl) ⟨1888406, by rfl⟩ : syracuseStep 2517875 = 3776813) B3776813
theorem B3025795 : Blo 1678039 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B3779459 : Blo 1678039 3779459 := bstep (se 1 (by rfl) ⟨2834594, by rfl⟩ : syracuseStep 3779459 = 5669189) B5669189
theorem B2517905 : Blo 1678039 2517905 := bstep (se 2 (by rfl) ⟨944214, by rfl⟩ : syracuseStep 2517905 = 1888429) B1888429
theorem B2517923 : Blo 1678039 2517923 := bstep (se 1 (by rfl) ⟨1888442, by rfl⟩ : syracuseStep 2517923 = 3776885) B3776885
theorem B2517953 : Blo 1678039 2517953 := bstep (se 2 (by rfl) ⟨944232, by rfl⟩ : syracuseStep 2517953 = 1888465) B1888465
theorem B2689985 : Blo 1678039 2689985 := bstep (se 2 (by rfl) ⟨1008744, by rfl⟩ : syracuseStep 2689985 = 2017489) B2017489
theorem B2517971 : Blo 1678039 2517971 := bstep (se 1 (by rfl) ⟨1888478, by rfl⟩ : syracuseStep 2517971 = 3776957) B3776957
theorem B2518001 : Blo 1678039 2518001 := bstep (se 2 (by rfl) ⟨944250, by rfl⟩ : syracuseStep 2518001 = 1888501) B1888501
theorem B2124787 : Blo 1678039 2124787 := bstep (se 1 (by rfl) ⟨1593590, by rfl⟩ : syracuseStep 2124787 = 3187181) B3187181
theorem B2518019 : Blo 1678039 2518019 := bstep (se 1 (by rfl) ⟨1888514, by rfl⟩ : syracuseStep 2518019 = 3777029) B3777029
theorem B2518049 : Blo 1678039 2518049 := bstep (se 2 (by rfl) ⟨944268, by rfl⟩ : syracuseStep 2518049 = 1888537) B1888537
theorem B8064035 : Blo 1678039 8064035 := bstep (se 1 (by rfl) ⟨6048026, by rfl⟩ : syracuseStep 8064035 = 12096053) B12096053
theorem B5663789 : Blo 1678039 5663789 := bstep (se 3 (by rfl) ⟨1061960, by rfl⟩ : syracuseStep 5663789 = 2123921) B2123921
theorem B2518067 : Blo 1678039 2518067 := bstep (se 1 (by rfl) ⟨1888550, by rfl⟩ : syracuseStep 2518067 = 3777101) B3777101
theorem B2690113 : Blo 1678039 2690113 := bstep (se 2 (by rfl) ⟨1008792, by rfl⟩ : syracuseStep 2690113 = 2017585) B2017585
theorem B2518097 : Blo 1678039 2518097 := bstep (se 2 (by rfl) ⟨944286, by rfl⟩ : syracuseStep 2518097 = 1888573) B1888573
theorem B2124883 : Blo 1678039 2124883 := bstep (se 1 (by rfl) ⟨1593662, by rfl⟩ : syracuseStep 2124883 = 3187325) B3187325
theorem B2518115 : Blo 1678039 2518115 := bstep (se 1 (by rfl) ⟨1888586, by rfl⟩ : syracuseStep 2518115 = 3777173) B3777173
theorem B6990947 : Blo 1678039 6990947 := bstep (se 1 (by rfl) ⟨5243210, by rfl⟩ : syracuseStep 6990947 = 10486421) B10486421
theorem B5663843 : Blo 1678039 5663843 := bstep (se 1 (by rfl) ⟨4247882, by rfl⟩ : syracuseStep 5663843 = 8495765) B8495765
theorem B2518145 : Blo 1678039 2518145 := bstep (se 2 (by rfl) ⟨944304, by rfl⟩ : syracuseStep 2518145 = 1888609) B1888609
theorem B2690177 : Blo 1678039 2690177 := bstep (se 2 (by rfl) ⟨1008816, by rfl⟩ : syracuseStep 2690177 = 2017633) B2017633
theorem B3779729 : Blo 1678039 3779729 := bstep (se 2 (by rfl) ⟨1417398, by rfl⟩ : syracuseStep 3779729 = 2834797) B2834797
theorem B2518163 : Blo 1678039 2518163 := bstep (se 1 (by rfl) ⟨1888622, by rfl⟩ : syracuseStep 2518163 = 3777245) B3777245
theorem B9071779 : Blo 1678039 9071779 := bstep (se 1 (by rfl) ⟨6803834, by rfl⟩ : syracuseStep 9071779 = 13607669) B13607669
theorem B3779747 : Blo 1678039 3779747 := bstep (se 1 (by rfl) ⟨2834810, by rfl⟩ : syracuseStep 3779747 = 5669621) B5669621
theorem B2518193 : Blo 1678039 2518193 := bstep (se 2 (by rfl) ⟨944322, by rfl⟩ : syracuseStep 2518193 = 1888645) B1888645
theorem B2518211 : Blo 1678039 2518211 := bstep (se 1 (by rfl) ⟨1888658, by rfl⟩ : syracuseStep 2518211 = 3777317) B3777317
theorem B2518241 : Blo 1678039 2518241 := bstep (se 2 (by rfl) ⟨944340, by rfl⟩ : syracuseStep 2518241 = 1888681) B1888681
theorem B147287267 : Blo 1678039 147287267 := bstep (se 1 (by rfl) ⟨110465450, by rfl⟩ : syracuseStep 147287267 = 220930901) B220930901
theorem B2518259 : Blo 1678039 2518259 := bstep (se 1 (by rfl) ⟨1888694, by rfl⟩ : syracuseStep 2518259 = 3777389) B3777389
theorem B2518289 : Blo 1678039 2518289 := bstep (se 2 (by rfl) ⟨944358, by rfl⟩ : syracuseStep 2518289 = 1888717) B1888717
theorem B2518307 : Blo 1678039 2518307 := bstep (se 1 (by rfl) ⟨1888730, by rfl⟩ : syracuseStep 2518307 = 3777461) B3777461
theorem B2518337 : Blo 1678039 2518337 := bstep (se 2 (by rfl) ⟨944376, by rfl⟩ : syracuseStep 2518337 = 1888753) B1888753
theorem B7269709 : Blo 1678039 7269709 := bstep (se 3 (by rfl) ⟨1363070, by rfl⟩ : syracuseStep 7269709 = 2726141) B2726141
theorem B2518355 : Blo 1678039 2518355 := bstep (se 1 (by rfl) ⟨1888766, by rfl⟩ : syracuseStep 2518355 = 3777533) B3777533
theorem B5664113 : Blo 1678039 5664113 := bstep (se 2 (by rfl) ⟨2124042, by rfl⟩ : syracuseStep 5664113 = 4248085) B4248085
theorem B2518385 : Blo 1678039 2518385 := bstep (se 2 (by rfl) ⟨944394, by rfl⟩ : syracuseStep 2518385 = 1888789) B1888789
theorem B2518403 : Blo 1678039 2518403 := bstep (se 1 (by rfl) ⟨1888802, by rfl⟩ : syracuseStep 2518403 = 3777605) B3777605
theorem B10210693 : Blo 1678039 10210693 := bstep (se 4 (by rfl) ⟨957252, by rfl⟩ : syracuseStep 10210693 = 1914505) B1914505
theorem B2518433 : Blo 1678039 2518433 := bstep (se 2 (by rfl) ⟨944412, by rfl⟩ : syracuseStep 2518433 = 1888825) B1888825
theorem B3780017 : Blo 1678039 3780017 := bstep (se 2 (by rfl) ⟨1417506, by rfl⟩ : syracuseStep 3780017 = 2835013) B2835013
theorem B2518451 : Blo 1678039 2518451 := bstep (se 1 (by rfl) ⟨1888838, by rfl⟩ : syracuseStep 2518451 = 3777677) B3777677
theorem B3780035 : Blo 1678039 3780035 := bstep (se 1 (by rfl) ⟨2835026, by rfl⟩ : syracuseStep 3780035 = 5670053) B5670053
theorem B2518481 : Blo 1678039 2518481 := bstep (se 2 (by rfl) ⟨944430, by rfl⟩ : syracuseStep 2518481 = 1888861) B1888861
theorem B2518499 : Blo 1678039 2518499 := bstep (se 1 (by rfl) ⟨1888874, by rfl⟩ : syracuseStep 2518499 = 3777749) B3777749
theorem B19131875 : Blo 1678039 19131875 := bstep (se 1 (by rfl) ⟨14348906, by rfl⟩ : syracuseStep 19131875 = 28697813) B28697813
theorem B2518529 : Blo 1678039 2518529 := bstep (se 2 (by rfl) ⟨944448, by rfl⟩ : syracuseStep 2518529 = 1888897) B1888897
theorem B5377549 : Blo 1678039 5377549 := bstep (se 3 (by rfl) ⟨1008290, by rfl⟩ : syracuseStep 5377549 = 2016581) B2016581
theorem B2518547 : Blo 1678039 2518547 := bstep (se 1 (by rfl) ⟨1888910, by rfl⟩ : syracuseStep 2518547 = 3777821) B3777821
theorem B2518577 : Blo 1678039 2518577 := bstep (se 2 (by rfl) ⟨944466, by rfl⟩ : syracuseStep 2518577 = 1888933) B1888933
theorem B4779587 : Blo 1678039 4779587 := bstep (se 1 (by rfl) ⟨3584690, by rfl⟩ : syracuseStep 4779587 = 7169381) B7169381
theorem B2518595 : Blo 1678039 2518595 := bstep (se 1 (by rfl) ⟨1888946, by rfl⟩ : syracuseStep 2518595 = 3777893) B3777893
theorem B2125379 : Blo 1678039 2125379 := bstep (se 1 (by rfl) ⟨1594034, by rfl⟩ : syracuseStep 2125379 = 3188069) B3188069
theorem B2518625 : Blo 1678039 2518625 := bstep (se 2 (by rfl) ⟨944484, by rfl⟩ : syracuseStep 2518625 = 1888969) B1888969
theorem B4034161 : Blo 1678039 4034161 := bstep (se 2 (by rfl) ⟨1512810, by rfl⟩ : syracuseStep 4034161 = 3025621) B3025621
theorem B2518643 : Blo 1678039 2518643 := bstep (se 1 (by rfl) ⟨1888982, by rfl⟩ : syracuseStep 2518643 = 3777965) B3777965
theorem B2518673 : Blo 1678039 2518673 := bstep (se 2 (by rfl) ⟨944502, by rfl⟩ : syracuseStep 2518673 = 1889005) B1889005
theorem B1887907 : Blo 1678039 1887907 := bstep (se 1 (by rfl) ⟨1415930, by rfl⟩ : syracuseStep 1887907 = 2831861) B2831861
theorem B2518691 : Blo 1678039 2518691 := bstep (se 1 (by rfl) ⟨1889018, by rfl⟩ : syracuseStep 2518691 = 3778037) B3778037
theorem B2518721 : Blo 1678039 2518721 := bstep (se 2 (by rfl) ⟨944520, by rfl⟩ : syracuseStep 2518721 = 1889041) B1889041
theorem B38760133 : Blo 1678039 38760133 := bstep (se 4 (by rfl) ⟨3633762, by rfl⟩ : syracuseStep 38760133 = 7267525) B7267525
theorem B2518739 : Blo 1678039 2518739 := bstep (se 1 (by rfl) ⟨1889054, by rfl⟩ : syracuseStep 2518739 = 3778109) B3778109
theorem B5746403 : Blo 1678039 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B2518769 : Blo 1678039 2518769 := bstep (se 2 (by rfl) ⟨944538, by rfl⟩ : syracuseStep 2518769 = 1889077) B1889077
theorem B6377201 : Blo 1678039 6377201 := bstep (se 2 (by rfl) ⟨2391450, by rfl⟩ : syracuseStep 6377201 = 4782901) B4782901
theorem B9080561 : Blo 1678039 9080561 := bstep (se 2 (by rfl) ⟨3405210, by rfl⟩ : syracuseStep 9080561 = 6810421) B6810421
theorem B2518787 : Blo 1678039 2518787 := bstep (se 1 (by rfl) ⟨1889090, by rfl⟩ : syracuseStep 2518787 = 3778181) B3778181
theorem B2518817 : Blo 1678039 2518817 := bstep (se 2 (by rfl) ⟨944556, by rfl⟩ : syracuseStep 2518817 = 1889113) B1889113
theorem B1888051 : Blo 1678039 1888051 := bstep (se 1 (by rfl) ⟨1416038, by rfl⟩ : syracuseStep 1888051 = 2832077) B2832077
theorem B2518835 : Blo 1678039 2518835 := bstep (se 1 (by rfl) ⟨1889126, by rfl⟩ : syracuseStep 2518835 = 3778253) B3778253
theorem B2518865 : Blo 1678039 2518865 := bstep (se 2 (by rfl) ⟨944574, by rfl⟩ : syracuseStep 2518865 = 1889149) B1889149
theorem B2518883 : Blo 1678039 2518883 := bstep (se 1 (by rfl) ⟨1889162, by rfl⟩ : syracuseStep 2518883 = 3778325) B3778325
theorem B2518913 : Blo 1678039 2518913 := bstep (se 2 (by rfl) ⟨944592, by rfl⟩ : syracuseStep 2518913 = 1889185) B1889185
theorem B5664653 : Blo 1678039 5664653 := bstep (se 3 (by rfl) ⟨1062122, by rfl⟩ : syracuseStep 5664653 = 2124245) B2124245
theorem B4779917 : Blo 1678039 4779917 := bstep (se 3 (by rfl) ⟨896234, by rfl⟩ : syracuseStep 4779917 = 1792469) B1792469
theorem B2518931 : Blo 1678039 2518931 := bstep (se 1 (by rfl) ⟨1889198, by rfl⟩ : syracuseStep 2518931 = 3778397) B3778397
theorem B2518961 : Blo 1678039 2518961 := bstep (se 2 (by rfl) ⟨944610, by rfl⟩ : syracuseStep 2518961 = 1889221) B1889221
theorem B3583939 : Blo 1678039 3583939 := bstep (se 1 (by rfl) ⟨2687954, by rfl⟩ : syracuseStep 3583939 = 5375909) B5375909
theorem B1888195 : Blo 1678039 1888195 := bstep (se 1 (by rfl) ⟨1416146, by rfl⟩ : syracuseStep 1888195 = 2832293) B2832293
theorem B5664707 : Blo 1678039 5664707 := bstep (se 1 (by rfl) ⟨4248530, by rfl⟩ : syracuseStep 5664707 = 8497061) B8497061
theorem B2518979 : Blo 1678039 2518979 := bstep (se 1 (by rfl) ⟨1889234, by rfl⟩ : syracuseStep 2518979 = 3778469) B3778469
theorem B3067843 : Blo 1678039 3067843 := bstep (se 1 (by rfl) ⟨2300882, by rfl⟩ : syracuseStep 3067843 = 4601765) B4601765
theorem B4779985 : Blo 1678039 4779985 := bstep (se 2 (by rfl) ⟨1792494, by rfl⟩ : syracuseStep 4779985 = 3584989) B3584989
theorem B2519009 : Blo 1678039 2519009 := bstep (se 2 (by rfl) ⟨944628, by rfl⟩ : syracuseStep 2519009 = 1889257) B1889257
theorem B2519027 : Blo 1678039 2519027 := bstep (se 1 (by rfl) ⟨1889270, by rfl⟩ : syracuseStep 2519027 = 3778541) B3778541
theorem B2519057 : Blo 1678039 2519057 := bstep (se 2 (by rfl) ⟨944646, by rfl⟩ : syracuseStep 2519057 = 1889293) B1889293
theorem B2519075 : Blo 1678039 2519075 := bstep (se 1 (by rfl) ⟨1889306, by rfl⟩ : syracuseStep 2519075 = 3778613) B3778613
theorem B2519105 : Blo 1678039 2519105 := bstep (se 2 (by rfl) ⟨944664, by rfl⟩ : syracuseStep 2519105 = 1889329) B1889329
theorem B1888339 : Blo 1678039 1888339 := bstep (se 1 (by rfl) ⟨1416254, by rfl⟩ : syracuseStep 1888339 = 2832509) B2832509
theorem B2519123 : Blo 1678039 2519123 := bstep (se 1 (by rfl) ⟨1889342, by rfl⟩ : syracuseStep 2519123 = 3778685) B3778685
theorem B2519153 : Blo 1678039 2519153 := bstep (se 2 (by rfl) ⟨944682, by rfl⟩ : syracuseStep 2519153 = 1889365) B1889365
theorem B2519171 : Blo 1678039 2519171 := bstep (se 1 (by rfl) ⟨1889378, by rfl⟩ : syracuseStep 2519171 = 3778757) B3778757
theorem B2519201 : Blo 1678039 2519201 := bstep (se 2 (by rfl) ⟨944700, by rfl⟩ : syracuseStep 2519201 = 1889401) B1889401
theorem B2519219 : Blo 1678039 2519219 := bstep (se 1 (by rfl) ⟨1889414, by rfl⟩ : syracuseStep 2519219 = 3778829) B3778829
theorem B4247761 : Blo 1678039 4247761 := bstep (se 2 (by rfl) ⟨1592910, by rfl⟩ : syracuseStep 4247761 = 3185821) B3185821
theorem B5664977 : Blo 1678039 5664977 := bstep (se 2 (by rfl) ⟨2124366, by rfl⟩ : syracuseStep 5664977 = 4248733) B4248733
theorem B2519249 : Blo 1678039 2519249 := bstep (se 2 (by rfl) ⟨944718, by rfl⟩ : syracuseStep 2519249 = 1889437) B1889437
theorem B1888483 : Blo 1678039 1888483 := bstep (se 1 (by rfl) ⟨1416362, by rfl⟩ : syracuseStep 1888483 = 2832725) B2832725
theorem B4780259 : Blo 1678039 4780259 := bstep (se 1 (by rfl) ⟨3585194, by rfl⟩ : syracuseStep 4780259 = 7170389) B7170389
theorem B2519267 : Blo 1678039 2519267 := bstep (se 1 (by rfl) ⟨1889450, by rfl⟩ : syracuseStep 2519267 = 3778901) B3778901
theorem B2519297 : Blo 1678039 2519297 := bstep (se 2 (by rfl) ⟨944736, by rfl⟩ : syracuseStep 2519297 = 1889473) B1889473
theorem B2126083 : Blo 1678039 2126083 := bstep (se 1 (by rfl) ⟨1594562, by rfl⟩ : syracuseStep 2126083 = 3189125) B3189125
theorem B2519315 : Blo 1678039 2519315 := bstep (se 1 (by rfl) ⟨1889486, by rfl⟩ : syracuseStep 2519315 = 3778973) B3778973
theorem B8499491 : Blo 1678039 8499491 := bstep (se 1 (by rfl) ⟨6374618, by rfl⟩ : syracuseStep 8499491 = 12749237) B12749237
theorem B10907939 : Blo 1678039 10907939 := bstep (se 1 (by rfl) ⟨8180954, by rfl⟩ : syracuseStep 10907939 = 16361909) B16361909
theorem B2519345 : Blo 1678039 2519345 := bstep (se 2 (by rfl) ⟨944754, by rfl⟩ : syracuseStep 2519345 = 1889509) B1889509
theorem B18157877 : Blo 1678039 18157877 := bstep (se 5 (by rfl) ⟨851150, by rfl⟩ : syracuseStep 18157877 = 1702301) B1702301
theorem B2519363 : Blo 1678039 2519363 := bstep (se 1 (by rfl) ⟨1889522, by rfl⟩ : syracuseStep 2519363 = 3779045) B3779045
theorem B2519393 : Blo 1678039 2519393 := bstep (se 2 (by rfl) ⟨944772, by rfl⟩ : syracuseStep 2519393 = 1889545) B1889545
theorem B2126179 : Blo 1678039 2126179 := bstep (se 1 (by rfl) ⟨1594634, by rfl⟩ : syracuseStep 2126179 = 3189269) B3189269
theorem B1888627 : Blo 1678039 1888627 := bstep (se 1 (by rfl) ⟨1416470, by rfl⟩ : syracuseStep 1888627 = 2832941) B2832941
theorem B2519411 : Blo 1678039 2519411 := bstep (se 1 (by rfl) ⟨1889558, by rfl⟩ : syracuseStep 2519411 = 3779117) B3779117
theorem B2871683 : Blo 1678039 2871683 := bstep (se 1 (by rfl) ⟨2153762, by rfl⟩ : syracuseStep 2871683 = 4307525) B4307525
theorem B9695621 : Blo 1678039 9695621 := bstep (se 4 (by rfl) ⟨908964, by rfl⟩ : syracuseStep 9695621 = 1817929) B1817929
theorem B3232145 : Blo 1678039 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B2519441 : Blo 1678039 2519441 := bstep (se 2 (by rfl) ⟨944790, by rfl⟩ : syracuseStep 2519441 = 1889581) B1889581
theorem B2519459 : Blo 1678039 2519459 := bstep (se 1 (by rfl) ⟨1889594, by rfl⟩ : syracuseStep 2519459 = 3779189) B3779189
theorem B2519489 : Blo 1678039 2519489 := bstep (se 2 (by rfl) ⟨944808, by rfl⟩ : syracuseStep 2519489 = 1889617) B1889617
theorem B2519507 : Blo 1678039 2519507 := bstep (se 1 (by rfl) ⟨1889630, by rfl⟩ : syracuseStep 2519507 = 3779261) B3779261
theorem B4248035 : Blo 1678039 4248035 := bstep (se 1 (by rfl) ⟨3186026, by rfl⟩ : syracuseStep 4248035 = 6372053) B6372053
theorem B14348771 : Blo 1678039 14348771 := bstep (se 1 (by rfl) ⟨10761578, by rfl⟩ : syracuseStep 14348771 = 21523157) B21523157
theorem B2519537 : Blo 1678039 2519537 := bstep (se 2 (by rfl) ⟨944826, by rfl⟩ : syracuseStep 2519537 = 1889653) B1889653
theorem B1888771 : Blo 1678039 1888771 := bstep (se 1 (by rfl) ⟨1416578, by rfl⟩ : syracuseStep 1888771 = 2833157) B2833157
theorem B2519555 : Blo 1678039 2519555 := bstep (se 1 (by rfl) ⟨1889666, by rfl⟩ : syracuseStep 2519555 = 3779333) B3779333
theorem B18158093 : Blo 1678039 18158093 := bstep (se 3 (by rfl) ⟨3404642, by rfl⟩ : syracuseStep 18158093 = 6809285) B6809285
theorem B3027473 : Blo 1678039 3027473 := bstep (se 2 (by rfl) ⟨1135302, by rfl⟩ : syracuseStep 3027473 = 2270605) B2270605
theorem B2519585 : Blo 1678039 2519585 := bstep (se 2 (by rfl) ⟨944844, by rfl⟩ : syracuseStep 2519585 = 1889689) B1889689
theorem B2519603 : Blo 1678039 2519603 := bstep (se 1 (by rfl) ⟨1889702, by rfl⟩ : syracuseStep 2519603 = 3779405) B3779405
theorem B2519633 : Blo 1678039 2519633 := bstep (se 2 (by rfl) ⟨944862, by rfl⟩ : syracuseStep 2519633 = 1889725) B1889725
theorem B2519651 : Blo 1678039 2519651 := bstep (se 1 (by rfl) ⟨1889738, by rfl⟩ : syracuseStep 2519651 = 3779477) B3779477
theorem B8065649 : Blo 1678039 8065649 := bstep (se 2 (by rfl) ⟨3024618, by rfl⟩ : syracuseStep 8065649 = 6049237) B6049237
theorem B2519681 : Blo 1678039 2519681 := bstep (se 2 (by rfl) ⟨944880, by rfl⟩ : syracuseStep 2519681 = 1889761) B1889761
theorem B1888915 : Blo 1678039 1888915 := bstep (se 1 (by rfl) ⟨1416686, by rfl⟩ : syracuseStep 1888915 = 2833373) B2833373
theorem B2519699 : Blo 1678039 2519699 := bstep (se 1 (by rfl) ⟨1889774, by rfl⟩ : syracuseStep 2519699 = 3779549) B3779549
theorem B4248227 : Blo 1678039 4248227 := bstep (se 1 (by rfl) ⟨3186170, by rfl⟩ : syracuseStep 4248227 = 6372341) B6372341
theorem B2519729 : Blo 1678039 2519729 := bstep (se 2 (by rfl) ⟨944898, by rfl⟩ : syracuseStep 2519729 = 1889797) B1889797
theorem B2519747 : Blo 1678039 2519747 := bstep (se 1 (by rfl) ⟨1889810, by rfl⟩ : syracuseStep 2519747 = 3779621) B3779621
theorem B7172813 : Blo 1678039 7172813 := bstep (se 3 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 7172813 = 2689805) B2689805
theorem B2519777 : Blo 1678039 2519777 := bstep (se 2 (by rfl) ⟨944916, by rfl⟩ : syracuseStep 2519777 = 1889833) B1889833
theorem B5665517 : Blo 1678039 5665517 := bstep (se 3 (by rfl) ⟨1062284, by rfl⟩ : syracuseStep 5665517 = 2124569) B2124569
theorem B2519795 : Blo 1678039 2519795 := bstep (se 1 (by rfl) ⟨1889846, by rfl⟩ : syracuseStep 2519795 = 3779693) B3779693
theorem B2519825 : Blo 1678039 2519825 := bstep (se 2 (by rfl) ⟨944934, by rfl⟩ : syracuseStep 2519825 = 1889869) B1889869
theorem B5665571 : Blo 1678039 5665571 := bstep (se 1 (by rfl) ⟨4249178, by rfl⟩ : syracuseStep 5665571 = 8498357) B8498357
theorem B1889059 : Blo 1678039 1889059 := bstep (se 1 (by rfl) ⟨1416794, by rfl⟩ : syracuseStep 1889059 = 2833589) B2833589
theorem B2519843 : Blo 1678039 2519843 := bstep (se 1 (by rfl) ⟨1889882, by rfl⟩ : syracuseStep 2519843 = 3779765) B3779765
theorem B2519873 : Blo 1678039 2519873 := bstep (se 2 (by rfl) ⟨944952, by rfl⟩ : syracuseStep 2519873 = 1889905) B1889905
theorem B2519891 : Blo 1678039 2519891 := bstep (se 1 (by rfl) ⟨1889918, by rfl⟩ : syracuseStep 2519891 = 3779837) B3779837
theorem B6804323 : Blo 1678039 6804323 := bstep (se 1 (by rfl) ⟨5103242, by rfl⟩ : syracuseStep 6804323 = 10206485) B10206485
theorem B2519921 : Blo 1678039 2519921 := bstep (se 2 (by rfl) ⟨944970, by rfl⟩ : syracuseStep 2519921 = 1889941) B1889941
theorem B2519939 : Blo 1678039 2519939 := bstep (se 1 (by rfl) ⟨1889954, by rfl⟩ : syracuseStep 2519939 = 3779909) B3779909
theorem B2519969 : Blo 1678039 2519969 := bstep (se 2 (by rfl) ⟨944988, by rfl⟩ : syracuseStep 2519969 = 1889977) B1889977
theorem B1889203 : Blo 1678039 1889203 := bstep (se 1 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 1889203 = 2833805) B2833805
theorem B2519987 : Blo 1678039 2519987 := bstep (se 1 (by rfl) ⟨1889990, by rfl⟩ : syracuseStep 2519987 = 3779981) B3779981
theorem B2520017 : Blo 1678039 2520017 := bstep (se 2 (by rfl) ⟨945006, by rfl⟩ : syracuseStep 2520017 = 1890013) B1890013
theorem B16135139 : Blo 1678039 16135139 := bstep (se 1 (by rfl) ⟨12101354, by rfl⟩ : syracuseStep 16135139 = 24202709) B24202709
theorem B2520035 : Blo 1678039 2520035 := bstep (se 1 (by rfl) ⟨1890026, by rfl⟩ : syracuseStep 2520035 = 3780053) B3780053
theorem B8066033 : Blo 1678039 8066033 := bstep (se 2 (by rfl) ⟨3024762, by rfl⟩ : syracuseStep 8066033 = 6049525) B6049525
theorem B4305923 : Blo 1678039 4305923 := bstep (se 1 (by rfl) ⟨3229442, by rfl⟩ : syracuseStep 4305923 = 6458885) B6458885
theorem B4781101 : Blo 1678039 4781101 := bstep (se 3 (by rfl) ⟨896456, by rfl⟩ : syracuseStep 4781101 = 1792913) B1792913
theorem B5665841 : Blo 1678039 5665841 := bstep (se 2 (by rfl) ⟨2124690, by rfl⟩ : syracuseStep 5665841 = 4249381) B4249381
theorem B4789315 : Blo 1678039 4789315 := bstep (se 1 (by rfl) ⟨3591986, by rfl⟩ : syracuseStep 4789315 = 7183973) B7183973
theorem B1889347 : Blo 1678039 1889347 := bstep (se 1 (by rfl) ⟨1417010, by rfl⟩ : syracuseStep 1889347 = 2834021) B2834021
theorem B8500301 : Blo 1678039 8500301 := bstep (se 3 (by rfl) ⟨1593806, by rfl⟩ : syracuseStep 8500301 = 3187613) B3187613
theorem B5379149 : Blo 1678039 5379149 := bstep (se 3 (by rfl) ⟨1008590, by rfl⟩ : syracuseStep 5379149 = 2017181) B2017181
theorem B2364547 : Blo 1678039 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B6378659 : Blo 1678039 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B4781261 : Blo 1678039 4781261 := bstep (se 3 (by rfl) ⟨896486, by rfl⟩ : syracuseStep 4781261 = 1792973) B1792973
theorem B1889491 : Blo 1678039 1889491 := bstep (se 1 (by rfl) ⟨1417118, by rfl⟩ : syracuseStep 1889491 = 2834237) B2834237
theorem B2831699 : Blo 1678039 2831699 := bstep (se 1 (by rfl) ⟨2123774, by rfl⟩ : syracuseStep 2831699 = 4247549) B4247549
theorem B1889635 : Blo 1678039 1889635 := bstep (se 1 (by rfl) ⟨1417226, by rfl⟩ : syracuseStep 1889635 = 2834453) B2834453
theorem B4781443 : Blo 1678039 4781443 := bstep (se 1 (by rfl) ⟨3586082, by rfl⟩ : syracuseStep 4781443 = 7172165) B7172165
theorem B9565573 : Blo 1678039 9565573 := bstep (se 4 (by rfl) ⟨896772, by rfl⟩ : syracuseStep 9565573 = 1793545) B1793545
theorem B2389457 : Blo 1678039 2389457 := bstep (se 2 (by rfl) ⟨896046, by rfl⟩ : syracuseStep 2389457 = 1792093) B1792093
theorem B2831827 : Blo 1678039 2831827 := bstep (se 1 (by rfl) ⟨2123870, by rfl⟩ : syracuseStep 2831827 = 4247741) B4247741
theorem B1889779 : Blo 1678039 1889779 := bstep (se 1 (by rfl) ⟨1417334, by rfl⟩ : syracuseStep 1889779 = 2834669) B2834669
theorem B8066573 : Blo 1678039 8066573 := bstep (se 3 (by rfl) ⟨1512482, by rfl⟩ : syracuseStep 8066573 = 3024965) B3024965
theorem B2389537 : Blo 1678039 2389537 := bstep (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) B1792153
theorem B5666381 : Blo 1678039 5666381 := bstep (se 3 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 5666381 = 2124893) B2124893
theorem B4249169 : Blo 1678039 4249169 := bstep (se 2 (by rfl) ⟨1593438, by rfl⟩ : syracuseStep 4249169 = 3186877) B3186877
theorem B2831969 : Blo 1678039 2831969 := bstep (se 2 (by rfl) ⟨1061988, by rfl⟩ : syracuseStep 2831969 = 2123977) B2123977
theorem B3634787 : Blo 1678039 3634787 := bstep (se 1 (by rfl) ⟨2726090, by rfl⟩ : syracuseStep 3634787 = 5452181) B5452181
theorem B4249219 : Blo 1678039 4249219 := bstep (se 1 (by rfl) ⟨3186914, by rfl⟩ : syracuseStep 4249219 = 6373829) B6373829
theorem B5666435 : Blo 1678039 5666435 := bstep (se 1 (by rfl) ⟨4249826, by rfl⟩ : syracuseStep 5666435 = 8499653) B8499653
theorem B1889923 : Blo 1678039 1889923 := bstep (se 1 (by rfl) ⟨1417442, by rfl⟩ : syracuseStep 1889923 = 2834885) B2834885
theorem B1701523 : Blo 1678039 1701523 := bstep (se 1 (by rfl) ⟨1276142, by rfl⟩ : syracuseStep 1701523 = 2552285) B2552285
theorem B2832097 : Blo 1678039 2832097 := bstep (se 2 (by rfl) ⟨1062036, by rfl⟩ : syracuseStep 2832097 = 2124073) B2124073
theorem B2832131 : Blo 1678039 2832131 := bstep (se 1 (by rfl) ⟨2124098, by rfl⟩ : syracuseStep 2832131 = 4248197) B4248197
theorem B4249361 : Blo 1678039 4249361 := bstep (se 2 (by rfl) ⟨1593510, by rfl⟩ : syracuseStep 4249361 = 3187021) B3187021
theorem B3585809 : Blo 1678039 3585809 := bstep (se 2 (by rfl) ⟨1344678, by rfl⟩ : syracuseStep 3585809 = 2689357) B2689357
theorem B19396421 : Blo 1678039 19396421 := bstep (se 4 (by rfl) ⟨1818414, by rfl⟩ : syracuseStep 19396421 = 3636829) B3636829
theorem B4601681 : Blo 1678039 4601681 := bstep (se 2 (by rfl) ⟨1725630, by rfl⟩ : syracuseStep 4601681 = 3451261) B3451261
theorem B2832259 : Blo 1678039 2832259 := bstep (se 1 (by rfl) ⟨2124194, by rfl⟩ : syracuseStep 2832259 = 4248389) B4248389
theorem B5666705 : Blo 1678039 5666705 := bstep (se 2 (by rfl) ⟨2125014, by rfl⟩ : syracuseStep 5666705 = 4250029) B4250029
theorem B2873297 : Blo 1678039 2873297 := bstep (se 2 (by rfl) ⟨1077486, by rfl⟩ : syracuseStep 2873297 = 2154973) B2154973
theorem B12105713 : Blo 1678039 12105713 := bstep (se 2 (by rfl) ⟨4539642, by rfl⟩ : syracuseStep 12105713 = 9079285) B9079285
theorem B1914883 : Blo 1678039 1914883 := bstep (se 1 (by rfl) ⟨1436162, by rfl⟩ : syracuseStep 1914883 = 2872325) B2872325
theorem B2832401 : Blo 1678039 2832401 := bstep (se 2 (by rfl) ⟨1062150, by rfl⟩ : syracuseStep 2832401 = 2124301) B2124301
theorem B10754147 : Blo 1678039 10754147 := bstep (se 1 (by rfl) ⟨8065610, by rfl⟩ : syracuseStep 10754147 = 16131221) B16131221
theorem B2832529 : Blo 1678039 2832529 := bstep (se 2 (by rfl) ⟨1062198, by rfl⟩ : syracuseStep 2832529 = 2124397) B2124397
theorem B2832563 : Blo 1678039 2832563 := bstep (se 1 (by rfl) ⟨2124422, by rfl⟩ : syracuseStep 2832563 = 4248845) B4248845
theorem B18143473 : Blo 1678039 18143473 := bstep (se 2 (by rfl) ⟨6803802, by rfl⟩ : syracuseStep 18143473 = 13607605) B13607605
theorem B2586865 : Blo 1678039 2586865 := bstep (se 2 (by rfl) ⟨970074, by rfl⟩ : syracuseStep 2586865 = 1940149) B1940149
theorem B1792243 : Blo 1678039 1792243 := bstep (se 1 (by rfl) ⟨1344182, by rfl⟩ : syracuseStep 1792243 = 2688365) B2688365
theorem B2832691 : Blo 1678039 2832691 := bstep (se 1 (by rfl) ⟨2124518, by rfl⟩ : syracuseStep 2832691 = 4249037) B4249037
theorem B2390323 : Blo 1678039 2390323 := bstep (se 1 (by rfl) ⟨1792742, by rfl⟩ : syracuseStep 2390323 = 3585485) B3585485
theorem B5667245 : Blo 1678039 5667245 := bstep (se 3 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 5667245 = 2125217) B2125217
theorem B2832833 : Blo 1678039 2832833 := bstep (se 2 (by rfl) ⟨1062312, by rfl⟩ : syracuseStep 2832833 = 2124625) B2124625
theorem B5667299 : Blo 1678039 5667299 := bstep (se 1 (by rfl) ⟨4250474, by rfl⟩ : syracuseStep 5667299 = 8500949) B8500949
theorem B18143729 : Blo 1678039 18143729 := bstep (se 2 (by rfl) ⟨6803898, by rfl⟩ : syracuseStep 18143729 = 13607797) B13607797
theorem B2832961 : Blo 1678039 2832961 := bstep (se 2 (by rfl) ⟨1062360, by rfl⟩ : syracuseStep 2832961 = 2124721) B2124721
theorem B2832995 : Blo 1678039 2832995 := bstep (se 1 (by rfl) ⟨2124746, by rfl⟩ : syracuseStep 2832995 = 4249493) B4249493
theorem B17234531 : Blo 1678039 17234531 := bstep (se 1 (by rfl) ⟨12925898, by rfl⟩ : syracuseStep 17234531 = 25851797) B25851797
theorem B3586673 : Blo 1678039 3586673 := bstep (se 2 (by rfl) ⟨1345002, by rfl⟩ : syracuseStep 3586673 = 2690005) B2690005
theorem B5380739 : Blo 1678039 5380739 := bstep (se 1 (by rfl) ⟨4035554, by rfl⟩ : syracuseStep 5380739 = 8071109) B8071109
theorem B8067725 : Blo 1678039 8067725 := bstep (se 3 (by rfl) ⟨1512698, by rfl⟩ : syracuseStep 8067725 = 3025397) B3025397
theorem B1678051 : Blo 1678039 1678051 := bstep (se 1 (by rfl) ⟨1258538, by rfl⟩ : syracuseStep 1678051 = 2517077) B2517077
theorem B6372067 : Blo 1678039 6372067 := bstep (se 1 (by rfl) ⟨4779050, by rfl⟩ : syracuseStep 6372067 = 9558101) B9558101
theorem B2833123 : Blo 1678039 2833123 := bstep (se 1 (by rfl) ⟨2124842, by rfl⟩ : syracuseStep 2833123 = 4249685) B4249685
theorem B4250353 : Blo 1678039 4250353 := bstep (se 2 (by rfl) ⟨1593882, by rfl⟩ : syracuseStep 4250353 = 3187765) B3187765
theorem B5667569 : Blo 1678039 5667569 := bstep (se 2 (by rfl) ⟨2125338, by rfl⟩ : syracuseStep 5667569 = 4250677) B4250677
theorem B1678067 : Blo 1678039 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B4782833 : Blo 1678039 4782833 := bstep (se 2 (by rfl) ⟨1793562, by rfl⟩ : syracuseStep 4782833 = 3587125) B3587125
theorem B1678083 : Blo 1678039 1678083 := bstep (se 1 (by rfl) ⟨1258562, by rfl⟩ : syracuseStep 1678083 = 2517125) B2517125
theorem B2390801 : Blo 1678039 2390801 := bstep (se 2 (by rfl) ⟨896550, by rfl⟩ : syracuseStep 2390801 = 1793101) B1793101
theorem B1678099 : Blo 1678039 1678099 := bstep (se 1 (by rfl) ⟨1258574, by rfl⟩ : syracuseStep 1678099 = 2517149) B2517149
theorem B1678115 : Blo 1678039 1678115 := bstep (se 1 (by rfl) ⟨1258586, by rfl⟩ : syracuseStep 1678115 = 2517173) B2517173
theorem B1678131 : Blo 1678039 1678131 := bstep (se 1 (by rfl) ⟨1258598, by rfl⟩ : syracuseStep 1678131 = 2517197) B2517197
theorem B1678147 : Blo 1678039 1678147 := bstep (se 1 (by rfl) ⟨1258610, by rfl⟩ : syracuseStep 1678147 = 2517221) B2517221
theorem B5380931 : Blo 1678039 5380931 := bstep (se 1 (by rfl) ⟨4035698, by rfl⟩ : syracuseStep 5380931 = 8071397) B8071397
theorem B1678163 : Blo 1678039 1678163 := bstep (se 1 (by rfl) ⟨1258622, by rfl⟩ : syracuseStep 1678163 = 2517245) B2517245
theorem B1678179 : Blo 1678039 1678179 := bstep (se 1 (by rfl) ⟨1258634, by rfl⟩ : syracuseStep 1678179 = 2517269) B2517269
theorem B2423651 : Blo 1678039 2423651 := bstep (se 1 (by rfl) ⟨1817738, by rfl⟩ : syracuseStep 2423651 = 3635477) B3635477
theorem B2833265 : Blo 1678039 2833265 := bstep (se 2 (by rfl) ⟨1062474, by rfl⟩ : syracuseStep 2833265 = 2124949) B2124949
theorem B1678195 : Blo 1678039 1678195 := bstep (se 1 (by rfl) ⟨1258646, by rfl⟩ : syracuseStep 1678195 = 2517293) B2517293
theorem B1678211 : Blo 1678039 1678211 := bstep (se 1 (by rfl) ⟨1258658, by rfl⟩ : syracuseStep 1678211 = 2517317) B2517317
theorem B2390915 : Blo 1678039 2390915 := bstep (se 1 (by rfl) ⟨1793186, by rfl⟩ : syracuseStep 2390915 = 3586373) B3586373
theorem B9689989 : Blo 1678039 9689989 := bstep (se 4 (by rfl) ⟨908436, by rfl⟩ : syracuseStep 9689989 = 1816873) B1816873
theorem B1678227 : Blo 1678039 1678227 := bstep (se 1 (by rfl) ⟨1258670, by rfl⟩ : syracuseStep 1678227 = 2517341) B2517341
theorem B1678243 : Blo 1678039 1678243 := bstep (se 1 (by rfl) ⟨1258682, by rfl⟩ : syracuseStep 1678243 = 2517365) B2517365
theorem B1678259 : Blo 1678039 1678259 := bstep (se 1 (by rfl) ⟨1258694, by rfl⟩ : syracuseStep 1678259 = 2517389) B2517389
theorem B1678275 : Blo 1678039 1678275 := bstep (se 1 (by rfl) ⟨1258706, by rfl⟩ : syracuseStep 1678275 = 2517413) B2517413
theorem B1678291 : Blo 1678039 1678291 := bstep (se 1 (by rfl) ⟨1258718, by rfl⟩ : syracuseStep 1678291 = 2517437) B2517437
theorem B2390995 : Blo 1678039 2390995 := bstep (se 1 (by rfl) ⟨1793246, by rfl⟩ : syracuseStep 2390995 = 3586493) B3586493
theorem B1678307 : Blo 1678039 1678307 := bstep (se 1 (by rfl) ⟨1258730, by rfl⟩ : syracuseStep 1678307 = 2517461) B2517461
theorem B2833393 : Blo 1678039 2833393 := bstep (se 2 (by rfl) ⟨1062522, by rfl⟩ : syracuseStep 2833393 = 2125045) B2125045
theorem B1678323 : Blo 1678039 1678323 := bstep (se 1 (by rfl) ⟨1258742, by rfl⟩ : syracuseStep 1678323 = 2517485) B2517485
theorem B1678339 : Blo 1678039 1678339 := bstep (se 1 (by rfl) ⟨1258754, by rfl⟩ : syracuseStep 1678339 = 2517509) B2517509
theorem B4250627 : Blo 1678039 4250627 := bstep (se 1 (by rfl) ⟨3187970, by rfl⟩ : syracuseStep 4250627 = 6375941) B6375941
theorem B1678355 : Blo 1678039 1678355 := bstep (se 1 (by rfl) ⟨1258766, by rfl⟩ : syracuseStep 1678355 = 2517533) B2517533
theorem B2833427 : Blo 1678039 2833427 := bstep (se 1 (by rfl) ⟨2125070, by rfl⟩ : syracuseStep 2833427 = 4250141) B4250141
theorem B1678371 : Blo 1678039 1678371 := bstep (se 1 (by rfl) ⟨1258778, by rfl⟩ : syracuseStep 1678371 = 2517557) B2517557
theorem B1678387 : Blo 1678039 1678387 := bstep (se 1 (by rfl) ⟨1258790, by rfl⟩ : syracuseStep 1678387 = 2517581) B2517581
theorem B1678403 : Blo 1678039 1678403 := bstep (se 1 (by rfl) ⟨1258802, by rfl⟩ : syracuseStep 1678403 = 2517605) B2517605
theorem B1678419 : Blo 1678039 1678419 := bstep (se 1 (by rfl) ⟨1258814, by rfl⟩ : syracuseStep 1678419 = 2517629) B2517629
theorem B1678435 : Blo 1678039 1678435 := bstep (se 1 (by rfl) ⟨1258826, by rfl⟩ : syracuseStep 1678435 = 2517653) B2517653
theorem B1678451 : Blo 1678039 1678451 := bstep (se 1 (by rfl) ⟨1258838, by rfl⟩ : syracuseStep 1678451 = 2517677) B2517677
theorem B1678467 : Blo 1678039 1678467 := bstep (se 1 (by rfl) ⟨1258850, by rfl⟩ : syracuseStep 1678467 = 2517701) B2517701
theorem B4848781 : Blo 1678039 4848781 := bstep (se 3 (by rfl) ⟨909146, by rfl⟩ : syracuseStep 4848781 = 1818293) B1818293
theorem B1678483 : Blo 1678039 1678483 := bstep (se 1 (by rfl) ⟨1258862, by rfl⟩ : syracuseStep 1678483 = 2517725) B2517725
theorem B2833555 : Blo 1678039 2833555 := bstep (se 1 (by rfl) ⟨2125166, by rfl⟩ : syracuseStep 2833555 = 4250333) B4250333
theorem B1678499 : Blo 1678039 1678499 := bstep (se 1 (by rfl) ⟨1258874, by rfl⟩ : syracuseStep 1678499 = 2517749) B2517749
theorem B5823665 : Blo 1678039 5823665 := bstep (se 2 (by rfl) ⟨2183874, by rfl⟩ : syracuseStep 5823665 = 4367749) B4367749
theorem B1678515 : Blo 1678039 1678515 := bstep (se 1 (by rfl) ⟨1258886, by rfl⟩ : syracuseStep 1678515 = 2517773) B2517773
theorem B1678531 : Blo 1678039 1678531 := bstep (se 1 (by rfl) ⟨1258898, by rfl⟩ : syracuseStep 1678531 = 2517797) B2517797
theorem B4250819 : Blo 1678039 4250819 := bstep (se 1 (by rfl) ⟨3188114, by rfl⟩ : syracuseStep 4250819 = 6376229) B6376229
theorem B3775697 : Blo 1678039 3775697 := bstep (se 2 (by rfl) ⟨1415886, by rfl⟩ : syracuseStep 3775697 = 2831773) B2831773
theorem B1678547 : Blo 1678039 1678547 := bstep (se 1 (by rfl) ⟨1258910, by rfl⟩ : syracuseStep 1678547 = 2517821) B2517821
theorem B3775715 : Blo 1678039 3775715 := bstep (se 1 (by rfl) ⟨2831786, by rfl⟩ : syracuseStep 3775715 = 5663573) B5663573
theorem B1678563 : Blo 1678039 1678563 := bstep (se 1 (by rfl) ⟨1258922, by rfl⟩ : syracuseStep 1678563 = 2517845) B2517845
theorem B3185905 : Blo 1678039 3185905 := bstep (se 2 (by rfl) ⟨1194714, by rfl⟩ : syracuseStep 3185905 = 2389429) B2389429
theorem B1678579 : Blo 1678039 1678579 := bstep (se 1 (by rfl) ⟨1258934, by rfl⟩ : syracuseStep 1678579 = 2517869) B2517869
theorem B1678595 : Blo 1678039 1678595 := bstep (se 1 (by rfl) ⟨1258946, by rfl⟩ : syracuseStep 1678595 = 2517893) B2517893
theorem B5668109 : Blo 1678039 5668109 := bstep (se 3 (by rfl) ⟨1062770, by rfl⟩ : syracuseStep 5668109 = 2125541) B2125541
theorem B1678611 : Blo 1678039 1678611 := bstep (se 1 (by rfl) ⟨1258958, by rfl⟩ : syracuseStep 1678611 = 2517917) B2517917
theorem B1678627 : Blo 1678039 1678627 := bstep (se 1 (by rfl) ⟨1258970, by rfl⟩ : syracuseStep 1678627 = 2517941) B2517941
theorem B2833697 : Blo 1678039 2833697 := bstep (se 2 (by rfl) ⟨1062636, by rfl⟩ : syracuseStep 2833697 = 2125273) B2125273
theorem B1678643 : Blo 1678039 1678643 := bstep (se 1 (by rfl) ⟨1258982, by rfl⟩ : syracuseStep 1678643 = 2517965) B2517965
theorem B1678659 : Blo 1678039 1678659 := bstep (se 1 (by rfl) ⟨1258994, by rfl⟩ : syracuseStep 1678659 = 2517989) B2517989
theorem B5668163 : Blo 1678039 5668163 := bstep (se 1 (by rfl) ⟨4251122, by rfl⟩ : syracuseStep 5668163 = 8502245) B8502245
theorem B9567557 : Blo 1678039 9567557 := bstep (se 4 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 9567557 = 1793917) B1793917
theorem B1678675 : Blo 1678039 1678675 := bstep (se 1 (by rfl) ⟨1259006, by rfl⟩ : syracuseStep 1678675 = 2518013) B2518013
theorem B1678691 : Blo 1678039 1678691 := bstep (se 1 (by rfl) ⟨1259018, by rfl⟩ : syracuseStep 1678691 = 2518037) B2518037
theorem B1678707 : Blo 1678039 1678707 := bstep (se 1 (by rfl) ⟨1259030, by rfl⟩ : syracuseStep 1678707 = 2518061) B2518061
theorem B1678723 : Blo 1678039 1678723 := bstep (se 1 (by rfl) ⟨1259042, by rfl⟩ : syracuseStep 1678723 = 2518085) B2518085
theorem B4537741 : Blo 1678039 4537741 := bstep (se 3 (by rfl) ⟨850826, by rfl⟩ : syracuseStep 4537741 = 1701653) B1701653
theorem B8068493 : Blo 1678039 8068493 := bstep (se 3 (by rfl) ⟨1512842, by rfl⟩ : syracuseStep 8068493 = 3025685) B3025685
theorem B1678739 : Blo 1678039 1678739 := bstep (se 1 (by rfl) ⟨1259054, by rfl⟩ : syracuseStep 1678739 = 2518109) B2518109
theorem B2833825 : Blo 1678039 2833825 := bstep (se 2 (by rfl) ⟨1062684, by rfl⟩ : syracuseStep 2833825 = 2125369) B2125369
theorem B1678755 : Blo 1678039 1678755 := bstep (se 1 (by rfl) ⟨1259066, by rfl⟩ : syracuseStep 1678755 = 2518133) B2518133
theorem B1678771 : Blo 1678039 1678771 := bstep (se 1 (by rfl) ⟨1259078, by rfl⟩ : syracuseStep 1678771 = 2518157) B2518157
theorem B1678787 : Blo 1678039 1678787 := bstep (se 1 (by rfl) ⟨1259090, by rfl⟩ : syracuseStep 1678787 = 2518181) B2518181
theorem B2833859 : Blo 1678039 2833859 := bstep (se 1 (by rfl) ⟨2125394, by rfl⟩ : syracuseStep 2833859 = 4250789) B4250789
theorem B5381585 : Blo 1678039 5381585 := bstep (se 2 (by rfl) ⟨2018094, by rfl⟩ : syracuseStep 5381585 = 4036189) B4036189
theorem B1678803 : Blo 1678039 1678803 := bstep (se 1 (by rfl) ⟨1259102, by rfl⟩ : syracuseStep 1678803 = 2518205) B2518205
theorem B1678819 : Blo 1678039 1678819 := bstep (se 1 (by rfl) ⟨1259114, by rfl⟩ : syracuseStep 1678819 = 2518229) B2518229
theorem B1793507 : Blo 1678039 1793507 := bstep (se 1 (by rfl) ⟨1345130, by rfl⟩ : syracuseStep 1793507 = 2690261) B2690261
theorem B3775985 : Blo 1678039 3775985 := bstep (se 2 (by rfl) ⟨1415994, by rfl⟩ : syracuseStep 3775985 = 2831989) B2831989
theorem B1678835 : Blo 1678039 1678835 := bstep (se 1 (by rfl) ⟨1259126, by rfl⟩ : syracuseStep 1678835 = 2518253) B2518253
theorem B2391553 : Blo 1678039 2391553 := bstep (se 2 (by rfl) ⟨896832, by rfl⟩ : syracuseStep 2391553 = 1793665) B1793665
theorem B3776003 : Blo 1678039 3776003 := bstep (se 1 (by rfl) ⟨2832002, by rfl⟩ : syracuseStep 3776003 = 5664005) B5664005
theorem B1678851 : Blo 1678039 1678851 := bstep (se 1 (by rfl) ⟨1259138, by rfl⟩ : syracuseStep 1678851 = 2518277) B2518277
theorem B5103121 : Blo 1678039 5103121 := bstep (se 2 (by rfl) ⟨1913670, by rfl⟩ : syracuseStep 5103121 = 3827341) B3827341
theorem B1678867 : Blo 1678039 1678867 := bstep (se 1 (by rfl) ⟨1259150, by rfl⟩ : syracuseStep 1678867 = 2518301) B2518301
theorem B1678883 : Blo 1678039 1678883 := bstep (se 1 (by rfl) ⟨1259162, by rfl⟩ : syracuseStep 1678883 = 2518325) B2518325
theorem B1678899 : Blo 1678039 1678899 := bstep (se 1 (by rfl) ⟨1259174, by rfl⟩ : syracuseStep 1678899 = 2518349) B2518349
theorem B1678915 : Blo 1678039 1678915 := bstep (se 1 (by rfl) ⟨1259186, by rfl⟩ : syracuseStep 1678915 = 2518373) B2518373
theorem B2833987 : Blo 1678039 2833987 := bstep (se 1 (by rfl) ⟨2125490, by rfl⟩ : syracuseStep 2833987 = 4250981) B4250981
theorem B1678931 : Blo 1678039 1678931 := bstep (se 1 (by rfl) ⟨1259198, by rfl⟩ : syracuseStep 1678931 = 2518397) B2518397
theorem B5668433 : Blo 1678039 5668433 := bstep (se 2 (by rfl) ⟨2125662, by rfl⟩ : syracuseStep 5668433 = 4251325) B4251325
theorem B1678947 : Blo 1678039 1678947 := bstep (se 1 (by rfl) ⟨1259210, by rfl⟩ : syracuseStep 1678947 = 2518421) B2518421
theorem B1678963 : Blo 1678039 1678963 := bstep (se 1 (by rfl) ⟨1259222, by rfl⟩ : syracuseStep 1678963 = 2518445) B2518445
theorem B3186307 : Blo 1678039 3186307 := bstep (se 1 (by rfl) ⟨2389730, by rfl⟩ : syracuseStep 3186307 = 4779461) B4779461
theorem B1678979 : Blo 1678039 1678979 := bstep (se 1 (by rfl) ⟨1259234, by rfl⟩ : syracuseStep 1678979 = 2518469) B2518469
theorem B1678995 : Blo 1678039 1678995 := bstep (se 1 (by rfl) ⟨1259246, by rfl⟩ : syracuseStep 1678995 = 2518493) B2518493
theorem B1679011 : Blo 1678039 1679011 := bstep (se 1 (by rfl) ⟨1259258, by rfl⟩ : syracuseStep 1679011 = 2518517) B2518517
theorem B4783789 : Blo 1678039 4783789 := bstep (se 3 (by rfl) ⟨896960, by rfl⟩ : syracuseStep 4783789 = 1793921) B1793921
theorem B3186353 : Blo 1678039 3186353 := bstep (se 2 (by rfl) ⟨1194882, by rfl⟩ : syracuseStep 3186353 = 2389765) B2389765
theorem B1679027 : Blo 1678039 1679027 := bstep (se 1 (by rfl) ⟨1259270, by rfl⟩ : syracuseStep 1679027 = 2518541) B2518541
theorem B1679043 : Blo 1678039 1679043 := bstep (se 1 (by rfl) ⟨1259282, by rfl⟩ : syracuseStep 1679043 = 2518565) B2518565
theorem B2834129 : Blo 1678039 2834129 := bstep (se 2 (by rfl) ⟨1062798, by rfl⟩ : syracuseStep 2834129 = 2125597) B2125597
theorem B1679059 : Blo 1678039 1679059 := bstep (se 1 (by rfl) ⟨1259294, by rfl⟩ : syracuseStep 1679059 = 2518589) B2518589
theorem B1679075 : Blo 1678039 1679075 := bstep (se 1 (by rfl) ⟨1259306, by rfl⟩ : syracuseStep 1679075 = 2518613) B2518613
theorem B1679091 : Blo 1678039 1679091 := bstep (se 1 (by rfl) ⟨1259318, by rfl⟩ : syracuseStep 1679091 = 2518637) B2518637
theorem B1679107 : Blo 1678039 1679107 := bstep (se 1 (by rfl) ⟨1259330, by rfl⟩ : syracuseStep 1679107 = 2518661) B2518661
theorem B3776273 : Blo 1678039 3776273 := bstep (se 2 (by rfl) ⟨1416102, by rfl⟩ : syracuseStep 3776273 = 2832205) B2832205
theorem B1679123 : Blo 1678039 1679123 := bstep (se 1 (by rfl) ⟨1259342, by rfl⟩ : syracuseStep 1679123 = 2518685) B2518685
theorem B3776291 : Blo 1678039 3776291 := bstep (se 1 (by rfl) ⟨2832218, by rfl⟩ : syracuseStep 3776291 = 5664437) B5664437
theorem B1679139 : Blo 1678039 1679139 := bstep (se 1 (by rfl) ⟨1259354, by rfl⟩ : syracuseStep 1679139 = 2518709) B2518709
theorem B1679155 : Blo 1678039 1679155 := bstep (se 1 (by rfl) ⟨1259366, by rfl⟩ : syracuseStep 1679155 = 2518733) B2518733
theorem B1679171 : Blo 1678039 1679171 := bstep (se 1 (by rfl) ⟨1259378, by rfl⟩ : syracuseStep 1679171 = 2518757) B2518757
theorem B2834257 : Blo 1678039 2834257 := bstep (se 2 (by rfl) ⟨1062846, by rfl⟩ : syracuseStep 2834257 = 2125693) B2125693
theorem B1679187 : Blo 1678039 1679187 := bstep (se 1 (by rfl) ⟨1259390, by rfl⟩ : syracuseStep 1679187 = 2518781) B2518781
theorem B1679203 : Blo 1678039 1679203 := bstep (se 1 (by rfl) ⟨1259402, by rfl⟩ : syracuseStep 1679203 = 2518805) B2518805
theorem B1679219 : Blo 1678039 1679219 := bstep (se 1 (by rfl) ⟨1259414, by rfl⟩ : syracuseStep 1679219 = 2518829) B2518829
theorem B2834291 : Blo 1678039 2834291 := bstep (se 1 (by rfl) ⟨2125718, by rfl⟩ : syracuseStep 2834291 = 4251437) B4251437
theorem B1679235 : Blo 1678039 1679235 := bstep (se 1 (by rfl) ⟨1259426, by rfl⟩ : syracuseStep 1679235 = 2518853) B2518853
theorem B3587971 : Blo 1678039 3587971 := bstep (se 1 (by rfl) ⟨2690978, by rfl⟩ : syracuseStep 3587971 = 5381957) B5381957
theorem B4784017 : Blo 1678039 4784017 := bstep (se 2 (by rfl) ⟨1794006, by rfl⟩ : syracuseStep 4784017 = 3588013) B3588013
theorem B1679251 : Blo 1678039 1679251 := bstep (se 1 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 1679251 = 2518877) B2518877
theorem B1679267 : Blo 1678039 1679267 := bstep (se 1 (by rfl) ⟨1259450, by rfl⟩ : syracuseStep 1679267 = 2518901) B2518901
theorem B8503217 : Blo 1678039 8503217 := bstep (se 2 (by rfl) ⟨3188706, by rfl⟩ : syracuseStep 8503217 = 6377413) B6377413
theorem B1679283 : Blo 1678039 1679283 := bstep (se 1 (by rfl) ⟨1259462, by rfl⟩ : syracuseStep 1679283 = 2518925) B2518925
theorem B1679299 : Blo 1678039 1679299 := bstep (se 1 (by rfl) ⟨1259474, by rfl⟩ : syracuseStep 1679299 = 2518949) B2518949
theorem B5742541 : Blo 1678039 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B3186641 : Blo 1678039 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B1679315 : Blo 1678039 1679315 := bstep (se 1 (by rfl) ⟨1259486, by rfl⟩ : syracuseStep 1679315 = 2518973) B2518973
theorem B1679331 : Blo 1678039 1679331 := bstep (se 1 (by rfl) ⟨1259498, by rfl⟩ : syracuseStep 1679331 = 2518997) B2518997
theorem B1679347 : Blo 1678039 1679347 := bstep (se 1 (by rfl) ⟨1259510, by rfl⟩ : syracuseStep 1679347 = 2519021) B2519021
theorem B2834419 : Blo 1678039 2834419 := bstep (se 1 (by rfl) ⟨2125814, by rfl⟩ : syracuseStep 2834419 = 4251629) B4251629
theorem B1679371 : Blo 1678039 1679371 := bstep (se 1 (by rfl) ⟨1259528, by rfl⟩ : syracuseStep 1679371 = 2519057) B2519057
theorem B1679383 : Blo 1678039 1679383 := bstep (se 1 (by rfl) ⟨1259537, by rfl⟩ : syracuseStep 1679383 = 2519075) B2519075
theorem B7176215 : Blo 1678039 7176215 := bstep (se 1 (by rfl) ⟨5382161, by rfl⟩ : syracuseStep 7176215 = 10764323) B10764323
theorem B1679403 : Blo 1678039 1679403 := bstep (se 1 (by rfl) ⟨1259552, by rfl⟩ : syracuseStep 1679403 = 2519105) B2519105
theorem B1679415 : Blo 1678039 1679415 := bstep (se 1 (by rfl) ⟨1259561, by rfl⟩ : syracuseStep 1679415 = 2519123) B2519123
theorem B1679435 : Blo 1678039 1679435 := bstep (se 1 (by rfl) ⟨1259576, by rfl⟩ : syracuseStep 1679435 = 2519153) B2519153
theorem B2834507 : Blo 1678039 2834507 := bstep (se 1 (by rfl) ⟨2125880, by rfl⟩ : syracuseStep 2834507 = 4251761) B4251761
theorem B1679447 : Blo 1678039 1679447 := bstep (se 1 (by rfl) ⟨1259585, by rfl⟩ : syracuseStep 1679447 = 2519171) B2519171
theorem B1679467 : Blo 1678039 1679467 := bstep (se 1 (by rfl) ⟨1259600, by rfl⟩ : syracuseStep 1679467 = 2519201) B2519201
theorem B1679479 : Blo 1678039 1679479 := bstep (se 1 (by rfl) ⟨1259609, by rfl⟩ : syracuseStep 1679479 = 2519219) B2519219
theorem B3776651 : Blo 1678039 3776651 := bstep (se 1 (by rfl) ⟨2832488, by rfl⟩ : syracuseStep 3776651 = 5664977) B5664977
theorem B1679499 : Blo 1678039 1679499 := bstep (se 1 (by rfl) ⟨1259624, by rfl⟩ : syracuseStep 1679499 = 2519249) B2519249
theorem B3186839 : Blo 1678039 3186839 := bstep (se 1 (by rfl) ⟨2390129, by rfl⟩ : syracuseStep 3186839 = 4780259) B4780259
theorem B1679511 : Blo 1678039 1679511 := bstep (se 1 (by rfl) ⟨1259633, by rfl⟩ : syracuseStep 1679511 = 2519267) B2519267
theorem B1679531 : Blo 1678039 1679531 := bstep (se 1 (by rfl) ⟨1259648, by rfl⟩ : syracuseStep 1679531 = 2519297) B2519297
theorem B1679543 : Blo 1678039 1679543 := bstep (se 1 (by rfl) ⟨1259657, by rfl⟩ : syracuseStep 1679543 = 2519315) B2519315
theorem B3776705 : Blo 1678039 3776705 := bstep (se 2 (by rfl) ⟨1416264, by rfl⟩ : syracuseStep 3776705 = 2832529) B2832529
theorem B1679563 : Blo 1678039 1679563 := bstep (se 1 (by rfl) ⟨1259672, by rfl⟩ : syracuseStep 1679563 = 2519345) B2519345
theorem B14344397 : Blo 1678039 14344397 := bstep (se 3 (by rfl) ⟨2689574, by rfl⟩ : syracuseStep 14344397 = 5379149) B5379149
theorem B2834635 : Blo 1678039 2834635 := bstep (se 1 (by rfl) ⟨2125976, by rfl⟩ : syracuseStep 2834635 = 4251953) B4251953
theorem B1679575 : Blo 1678039 1679575 := bstep (se 1 (by rfl) ⟨1259681, by rfl⟩ : syracuseStep 1679575 = 2519363) B2519363
theorem B5669081 : Blo 1678039 5669081 := bstep (se 2 (by rfl) ⟨2125905, by rfl⟩ : syracuseStep 5669081 = 4251811) B4251811
theorem B1679595 : Blo 1678039 1679595 := bstep (se 1 (by rfl) ⟨1259696, by rfl⟩ : syracuseStep 1679595 = 2519393) B2519393
theorem B1679607 : Blo 1678039 1679607 := bstep (se 1 (by rfl) ⟨1259705, by rfl⟩ : syracuseStep 1679607 = 2519411) B2519411
theorem B6463747 : Blo 1678039 6463747 := bstep (se 1 (by rfl) ⟨4847810, by rfl⟩ : syracuseStep 6463747 = 9695621) B9695621
theorem B2154763 : Blo 1678039 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B1679627 : Blo 1678039 1679627 := bstep (se 1 (by rfl) ⟨1259720, by rfl⟩ : syracuseStep 1679627 = 2519441) B2519441
theorem B1679639 : Blo 1678039 1679639 := bstep (se 1 (by rfl) ⟨1259729, by rfl⟩ : syracuseStep 1679639 = 2519459) B2519459
theorem B1679659 : Blo 1678039 1679659 := bstep (se 1 (by rfl) ⟨1259744, by rfl⟩ : syracuseStep 1679659 = 2519489) B2519489
theorem B1679671 : Blo 1678039 1679671 := bstep (se 1 (by rfl) ⟨1259753, by rfl⟩ : syracuseStep 1679671 = 2519507) B2519507
theorem B24191297 : Blo 1678039 24191297 := bstep (se 2 (by rfl) ⟨9071736, by rfl⟩ : syracuseStep 24191297 = 18143473) B18143473
theorem B3449153 : Blo 1678039 3449153 := bstep (se 2 (by rfl) ⟨1293432, by rfl⟩ : syracuseStep 3449153 = 2586865) B2586865
theorem B1679691 : Blo 1678039 1679691 := bstep (se 1 (by rfl) ⟨1259768, by rfl⟩ : syracuseStep 1679691 = 2519537) B2519537
theorem B1679703 : Blo 1678039 1679703 := bstep (se 1 (by rfl) ⟨1259777, by rfl⟩ : syracuseStep 1679703 = 2519555) B2519555
theorem B2834777 : Blo 1678039 2834777 := bstep (se 2 (by rfl) ⟨1063041, by rfl⟩ : syracuseStep 2834777 = 2126083) B2126083
theorem B11493733 : Blo 1678039 11493733 := bstep (se 4 (by rfl) ⟨1077537, by rfl⟩ : syracuseStep 11493733 = 2155075) B2155075
theorem B1679723 : Blo 1678039 1679723 := bstep (se 1 (by rfl) ⟨1259792, by rfl⟩ : syracuseStep 1679723 = 2519585) B2519585
theorem B1679735 : Blo 1678039 1679735 := bstep (se 1 (by rfl) ⟨1259801, by rfl⟩ : syracuseStep 1679735 = 2519603) B2519603
theorem B1679755 : Blo 1678039 1679755 := bstep (se 1 (by rfl) ⟨1259816, by rfl⟩ : syracuseStep 1679755 = 2519633) B2519633
theorem B8503703 : Blo 1678039 8503703 := bstep (se 1 (by rfl) ⟨6377777, by rfl⟩ : syracuseStep 8503703 = 12755555) B12755555
theorem B1679767 : Blo 1678039 1679767 := bstep (se 1 (by rfl) ⟨1259825, by rfl⟩ : syracuseStep 1679767 = 2519651) B2519651
theorem B3776921 : Blo 1678039 3776921 := bstep (se 2 (by rfl) ⟨1416345, by rfl⟩ : syracuseStep 3776921 = 2832691) B2832691
theorem B3187097 : Blo 1678039 3187097 := bstep (se 2 (by rfl) ⟨1195161, by rfl⟩ : syracuseStep 3187097 = 2390323) B2390323
theorem B1679787 : Blo 1678039 1679787 := bstep (se 1 (by rfl) ⟨1259840, by rfl⟩ : syracuseStep 1679787 = 2519681) B2519681
theorem B1679799 : Blo 1678039 1679799 := bstep (se 1 (by rfl) ⟨1259849, by rfl⟩ : syracuseStep 1679799 = 2519699) B2519699
theorem B1679819 : Blo 1678039 1679819 := bstep (se 1 (by rfl) ⟨1259864, by rfl⟩ : syracuseStep 1679819 = 2519729) B2519729
theorem B1679831 : Blo 1678039 1679831 := bstep (se 1 (by rfl) ⟨1259873, by rfl⟩ : syracuseStep 1679831 = 2519747) B2519747
theorem B2834905 : Blo 1678039 2834905 := bstep (se 2 (by rfl) ⟨1063089, by rfl⟩ : syracuseStep 2834905 = 2126179) B2126179
theorem B1679851 : Blo 1678039 1679851 := bstep (se 1 (by rfl) ⟨1259888, by rfl⟩ : syracuseStep 1679851 = 2519777) B2519777
theorem B3777011 : Blo 1678039 3777011 := bstep (se 1 (by rfl) ⟨2832758, by rfl⟩ : syracuseStep 3777011 = 5665517) B5665517
theorem B1679863 : Blo 1678039 1679863 := bstep (se 1 (by rfl) ⟨1259897, by rfl⟩ : syracuseStep 1679863 = 2519795) B2519795
theorem B1679883 : Blo 1678039 1679883 := bstep (se 1 (by rfl) ⟨1259912, by rfl⟩ : syracuseStep 1679883 = 2519825) B2519825
theorem B3777047 : Blo 1678039 3777047 := bstep (se 1 (by rfl) ⟨2832785, by rfl⟩ : syracuseStep 3777047 = 5665571) B5665571
theorem B1679895 : Blo 1678039 1679895 := bstep (se 1 (by rfl) ⟨1259921, by rfl⟩ : syracuseStep 1679895 = 2519843) B2519843
theorem B1679915 : Blo 1678039 1679915 := bstep (se 1 (by rfl) ⟨1259936, by rfl⟩ : syracuseStep 1679915 = 2519873) B2519873
theorem B1679927 : Blo 1678039 1679927 := bstep (se 1 (by rfl) ⟨1259945, by rfl⟩ : syracuseStep 1679927 = 2519891) B2519891
theorem B1679947 : Blo 1678039 1679947 := bstep (se 1 (by rfl) ⟨1259960, by rfl⟩ : syracuseStep 1679947 = 2519921) B2519921
theorem B1679959 : Blo 1678039 1679959 := bstep (se 1 (by rfl) ⟨1259969, by rfl⟩ : syracuseStep 1679959 = 2519939) B2519939
theorem B1679979 : Blo 1678039 1679979 := bstep (se 1 (by rfl) ⟨1259984, by rfl⟩ : syracuseStep 1679979 = 2519969) B2519969
theorem B1679991 : Blo 1678039 1679991 := bstep (se 1 (by rfl) ⟨1259993, by rfl⟩ : syracuseStep 1679991 = 2519987) B2519987
theorem B1680011 : Blo 1678039 1680011 := bstep (se 1 (by rfl) ⟨1260008, by rfl⟩ : syracuseStep 1680011 = 2520017) B2520017
theorem B1680023 : Blo 1678039 1680023 := bstep (se 1 (by rfl) ⟨1260017, by rfl⟩ : syracuseStep 1680023 = 2520035) B2520035
theorem B3777227 : Blo 1678039 3777227 := bstep (se 1 (by rfl) ⟨2832920, by rfl⟩ : syracuseStep 3777227 = 5665841) B5665841
theorem B3777281 : Blo 1678039 3777281 := bstep (se 2 (by rfl) ⟨1416480, by rfl⟩ : syracuseStep 3777281 = 2832961) B2832961
theorem B4252439 : Blo 1678039 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B3187507 : Blo 1678039 3187507 := bstep (se 1 (by rfl) ⟨2390630, by rfl⟩ : syracuseStep 3187507 = 4781261) B4781261
theorem B4088665 : Blo 1678039 4088665 := bstep (se 2 (by rfl) ⟨1533249, by rfl⟩ : syracuseStep 4088665 = 3066499) B3066499
theorem B5669783 : Blo 1678039 5669783 := bstep (se 1 (by rfl) ⟨4252337, by rfl⟩ : syracuseStep 5669783 = 8504675) B8504675
theorem B8496089 : Blo 1678039 8496089 := bstep (se 2 (by rfl) ⟨3186033, by rfl⟩ : syracuseStep 8496089 = 6372067) B6372067
theorem B3777497 : Blo 1678039 3777497 := bstep (se 2 (by rfl) ⟨1416561, by rfl⟩ : syracuseStep 3777497 = 2833123) B2833123
theorem B3777587 : Blo 1678039 3777587 := bstep (se 1 (by rfl) ⟨2833190, by rfl⟩ : syracuseStep 3777587 = 5666381) B5666381
theorem B3777623 : Blo 1678039 3777623 := bstep (se 1 (by rfl) ⟨2833217, by rfl⟩ : syracuseStep 3777623 = 5666435) B5666435
theorem B12919985 : Blo 1678039 12919985 := bstep (se 2 (by rfl) ⟨4844994, by rfl⟩ : syracuseStep 12919985 = 9689989) B9689989
theorem B3777803 : Blo 1678039 3777803 := bstep (se 1 (by rfl) ⟨2833352, by rfl⟩ : syracuseStep 3777803 = 5666705) B5666705
theorem B3187993 : Blo 1678039 3187993 := bstep (se 2 (by rfl) ⟨1195497, by rfl⟩ : syracuseStep 3187993 = 2390995) B2390995
theorem B3777857 : Blo 1678039 3777857 := bstep (se 2 (by rfl) ⟨1416696, by rfl⟩ : syracuseStep 3777857 = 2833393) B2833393
theorem B8070475 : Blo 1678039 8070475 := bstep (se 1 (by rfl) ⟨6052856, by rfl⟩ : syracuseStep 8070475 = 12105713) B12105713
theorem B6374801 : Blo 1678039 6374801 := bstep (se 2 (by rfl) ⟨2390550, by rfl⟩ : syracuseStep 6374801 = 4781101) B4781101
theorem B7169431 : Blo 1678039 7169431 := bstep (se 1 (by rfl) ⟨5377073, by rfl⟩ : syracuseStep 7169431 = 10754147) B10754147
theorem B2688473 : Blo 1678039 2688473 := bstep (se 2 (by rfl) ⟨1008177, by rfl⟩ : syracuseStep 2688473 = 2016355) B2016355
theorem B6465041 : Blo 1678039 6465041 := bstep (se 2 (by rfl) ⟨2424390, by rfl⟩ : syracuseStep 6465041 = 4848781) B4848781
theorem B3778073 : Blo 1678039 3778073 := bstep (se 2 (by rfl) ⟨1416777, by rfl⟩ : syracuseStep 3778073 = 2833555) B2833555
theorem B36308573 : Blo 1678039 36308573 := bstep (se 3 (by rfl) ⟨6807857, by rfl⟩ : syracuseStep 36308573 = 13615715) B13615715
theorem B3778163 : Blo 1678039 3778163 := bstep (se 1 (by rfl) ⟨2833622, by rfl⟩ : syracuseStep 3778163 = 5667245) B5667245
theorem B3778199 : Blo 1678039 3778199 := bstep (se 1 (by rfl) ⟨2833649, by rfl⟩ : syracuseStep 3778199 = 5667299) B5667299
theorem B9692945 : Blo 1678039 9692945 := bstep (se 2 (by rfl) ⟨3634854, by rfl⟩ : syracuseStep 9692945 = 7269709) B7269709
theorem B3778379 : Blo 1678039 3778379 := bstep (se 1 (by rfl) ⟨2833784, by rfl⟩ : syracuseStep 3778379 = 5667569) B5667569
theorem B3188555 : Blo 1678039 3188555 := bstep (se 1 (by rfl) ⟨2391416, by rfl⟩ : syracuseStep 3188555 = 4782833) B4782833
theorem B6375257 : Blo 1678039 6375257 := bstep (se 2 (by rfl) ⟨2390721, by rfl⟩ : syracuseStep 6375257 = 4781443) B4781443
theorem B3778433 : Blo 1678039 3778433 := bstep (se 2 (by rfl) ⟨1416912, by rfl⟩ : syracuseStep 3778433 = 2833825) B2833825
theorem B2688985 : Blo 1678039 2688985 := bstep (se 2 (by rfl) ⟨1008369, by rfl⟩ : syracuseStep 2688985 = 2016739) B2016739
theorem B3188737 : Blo 1678039 3188737 := bstep (se 2 (by rfl) ⟨1195776, by rfl⟩ : syracuseStep 3188737 = 2391553) B2391553
theorem B7170065 : Blo 1678039 7170065 := bstep (se 2 (by rfl) ⟨2688774, by rfl⟩ : syracuseStep 7170065 = 5377549) B5377549
theorem B5376023 : Blo 1678039 5376023 := bstep (se 1 (by rfl) ⟨4032017, by rfl⟩ : syracuseStep 5376023 = 8064035) B8064035
theorem B9562157 : Blo 1678039 9562157 := bstep (se 3 (by rfl) ⟨1792904, by rfl⟩ : syracuseStep 9562157 = 3585809) B3585809
theorem B6375469 : Blo 1678039 6375469 := bstep (se 3 (by rfl) ⟨1195400, by rfl⟩ : syracuseStep 6375469 = 2390801) B2390801
theorem B3778649 : Blo 1678039 3778649 := bstep (se 2 (by rfl) ⟨1416993, by rfl⟩ : syracuseStep 3778649 = 2833987) B2833987
theorem B2517131 : Blo 1678039 2517131 := bstep (se 1 (by rfl) ⟨1887848, by rfl⟩ : syracuseStep 2517131 = 3775697) B3775697
theorem B2517143 : Blo 1678039 2517143 := bstep (se 1 (by rfl) ⟨1887857, by rfl⟩ : syracuseStep 2517143 = 3775715) B3775715
theorem B98191511 : Blo 1678039 98191511 := bstep (se 1 (by rfl) ⟨73643633, by rfl⟩ : syracuseStep 98191511 = 147287267) B147287267
theorem B3778739 : Blo 1678039 3778739 := bstep (se 1 (by rfl) ⟨2834054, by rfl⟩ : syracuseStep 3778739 = 5668109) B5668109
theorem B3778775 : Blo 1678039 3778775 := bstep (se 1 (by rfl) ⟨2834081, by rfl⟩ : syracuseStep 3778775 = 5668163) B5668163
theorem B2517209 : Blo 1678039 2517209 := bstep (se 2 (by rfl) ⟨943953, by rfl⟩ : syracuseStep 2517209 = 1887907) B1887907
theorem B2517323 : Blo 1678039 2517323 := bstep (se 1 (by rfl) ⟨1887992, by rfl⟩ : syracuseStep 2517323 = 3775985) B3775985
theorem B2517335 : Blo 1678039 2517335 := bstep (se 1 (by rfl) ⟨1888001, by rfl⟩ : syracuseStep 2517335 = 3776003) B3776003
theorem B6375773 : Blo 1678039 6375773 := bstep (se 3 (by rfl) ⟨1195457, by rfl⟩ : syracuseStep 6375773 = 2390915) B2390915
theorem B3778955 : Blo 1678039 3778955 := bstep (se 1 (by rfl) ⟨2834216, by rfl⟩ : syracuseStep 3778955 = 5668433) B5668433
theorem B2517401 : Blo 1678039 2517401 := bstep (se 2 (by rfl) ⟨944025, by rfl⟩ : syracuseStep 2517401 = 1888051) B1888051
theorem B3779009 : Blo 1678039 3779009 := bstep (se 2 (by rfl) ⟨1417128, by rfl⟩ : syracuseStep 3779009 = 2834257) B2834257
theorem B2124235 : Blo 1678039 2124235 := bstep (se 1 (by rfl) ⟨1593176, by rfl⟩ : syracuseStep 2124235 = 3186353) B3186353
theorem B2517515 : Blo 1678039 2517515 := bstep (se 1 (by rfl) ⟨1888136, by rfl⟩ : syracuseStep 2517515 = 3776273) B3776273
theorem B2517527 : Blo 1678039 2517527 := bstep (se 1 (by rfl) ⟨1888145, by rfl⟩ : syracuseStep 2517527 = 3776291) B3776291
theorem B8497709 : Blo 1678039 8497709 := bstep (se 3 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 8497709 = 3186641) B3186641
theorem B4778585 : Blo 1678039 4778585 := bstep (se 2 (by rfl) ⟨1791969, by rfl⟩ : syracuseStep 4778585 = 3583939) B3583939
theorem B2517593 : Blo 1678039 2517593 := bstep (se 2 (by rfl) ⟨944097, by rfl⟩ : syracuseStep 2517593 = 1888195) B1888195
theorem B4090457 : Blo 1678039 4090457 := bstep (se 2 (by rfl) ⟨1533921, by rfl⟩ : syracuseStep 4090457 = 3067843) B3067843
theorem B43027037 : Blo 1678039 43027037 := bstep (se 3 (by rfl) ⟨8067569, by rfl⟩ : syracuseStep 43027037 = 16135139) B16135139
theorem B3779225 : Blo 1678039 3779225 := bstep (se 2 (by rfl) ⟨1417209, by rfl⟩ : syracuseStep 3779225 = 2834419) B2834419
theorem B5663411 : Blo 1678039 5663411 := bstep (se 1 (by rfl) ⟨4247558, by rfl⟩ : syracuseStep 5663411 = 8495117) B8495117
theorem B2517707 : Blo 1678039 2517707 := bstep (se 1 (by rfl) ⟨1888280, by rfl⟩ : syracuseStep 2517707 = 3776561) B3776561
theorem B7170763 : Blo 1678039 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B3189451 : Blo 1678039 3189451 := bstep (se 1 (by rfl) ⟨2392088, by rfl⟩ : syracuseStep 3189451 = 4784177) B4784177
theorem B2517719 : Blo 1678039 2517719 := bstep (se 1 (by rfl) ⟨1888289, by rfl⟩ : syracuseStep 2517719 = 3776579) B3776579
theorem B3779315 : Blo 1678039 3779315 := bstep (se 1 (by rfl) ⟨2834486, by rfl⟩ : syracuseStep 3779315 = 5668973) B5668973
theorem B3779351 : Blo 1678039 3779351 := bstep (se 1 (by rfl) ⟨2834513, by rfl⟩ : syracuseStep 3779351 = 5669027) B5669027
theorem B2517785 : Blo 1678039 2517785 := bstep (se 2 (by rfl) ⟨944169, by rfl⟩ : syracuseStep 2517785 = 1888339) B1888339
theorem B2517899 : Blo 1678039 2517899 := bstep (se 1 (by rfl) ⟨1888424, by rfl⟩ : syracuseStep 2517899 = 3776849) B3776849
theorem B2517911 : Blo 1678039 2517911 := bstep (se 1 (by rfl) ⟨1888433, by rfl⟩ : syracuseStep 2517911 = 3776867) B3776867
theorem B5663681 : Blo 1678039 5663681 := bstep (se 2 (by rfl) ⟨2123880, by rfl⟩ : syracuseStep 5663681 = 4247761) B4247761
theorem B3779531 : Blo 1678039 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B2517977 : Blo 1678039 2517977 := bstep (se 2 (by rfl) ⟨944241, by rfl⟩ : syracuseStep 2517977 = 1888483) B1888483
theorem B7171037 : Blo 1678039 7171037 := bstep (se 3 (by rfl) ⟨1344569, by rfl⟩ : syracuseStep 7171037 = 2689139) B2689139
theorem B3779585 : Blo 1678039 3779585 := bstep (se 2 (by rfl) ⟨1417344, by rfl⟩ : syracuseStep 3779585 = 2834689) B2834689
theorem B2018315 : Blo 1678039 2018315 := bstep (se 1 (by rfl) ⟨1513736, by rfl⟩ : syracuseStep 2018315 = 3027473) B3027473
theorem B5377099 : Blo 1678039 5377099 := bstep (se 1 (by rfl) ⟨4032824, by rfl⟩ : syracuseStep 5377099 = 8065649) B8065649
theorem B2518091 : Blo 1678039 2518091 := bstep (se 1 (by rfl) ⟨1888568, by rfl⟩ : syracuseStep 2518091 = 3777137) B3777137
theorem B2518103 : Blo 1678039 2518103 := bstep (se 1 (by rfl) ⟨1888577, by rfl⟩ : syracuseStep 2518103 = 3777155) B3777155
theorem B18656407 : Blo 1678039 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B2518169 : Blo 1678039 2518169 := bstep (se 2 (by rfl) ⟨944313, by rfl⟩ : syracuseStep 2518169 = 1888627) B1888627
theorem B3402955 : Blo 1678039 3402955 := bstep (se 1 (by rfl) ⟨2552216, by rfl⟩ : syracuseStep 3402955 = 5104433) B5104433
theorem B5377241 : Blo 1678039 5377241 := bstep (se 2 (by rfl) ⟨2016465, by rfl⟩ : syracuseStep 5377241 = 4032931) B4032931
theorem B3779801 : Blo 1678039 3779801 := bstep (se 2 (by rfl) ⟨1417425, by rfl⟩ : syracuseStep 3779801 = 2834851) B2834851
theorem B2518283 : Blo 1678039 2518283 := bstep (se 1 (by rfl) ⟨1888712, by rfl⟩ : syracuseStep 2518283 = 3777425) B3777425
theorem B2518295 : Blo 1678039 2518295 := bstep (se 1 (by rfl) ⟨1888721, by rfl⟩ : syracuseStep 2518295 = 3777443) B3777443
theorem B7171379 : Blo 1678039 7171379 := bstep (se 1 (by rfl) ⟨5378534, by rfl⟩ : syracuseStep 7171379 = 10757069) B10757069
theorem B3779891 : Blo 1678039 3779891 := bstep (se 1 (by rfl) ⟨2834918, by rfl⟩ : syracuseStep 3779891 = 5669837) B5669837
theorem B5377355 : Blo 1678039 5377355 := bstep (se 1 (by rfl) ⟨4033016, by rfl⟩ : syracuseStep 5377355 = 8066033) B8066033
theorem B2870615 : Blo 1678039 2870615 := bstep (se 1 (by rfl) ⟨2152961, by rfl⟩ : syracuseStep 2870615 = 4305923) B4305923
theorem B2518361 : Blo 1678039 2518361 := bstep (se 2 (by rfl) ⟨944385, by rfl⟩ : syracuseStep 2518361 = 1888771) B1888771
theorem B3779927 : Blo 1678039 3779927 := bstep (se 1 (by rfl) ⟨2834945, by rfl⟩ : syracuseStep 3779927 = 5669891) B5669891
theorem B4779415 : Blo 1678039 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B2125207 : Blo 1678039 2125207 := bstep (se 1 (by rfl) ⟨1593905, by rfl⟩ : syracuseStep 2125207 = 3187811) B3187811
theorem B2518475 : Blo 1678039 2518475 := bstep (se 1 (by rfl) ⟨1888856, by rfl⟩ : syracuseStep 2518475 = 3777713) B3777713
theorem B2518487 : Blo 1678039 2518487 := bstep (se 1 (by rfl) ⟨1888865, by rfl⟩ : syracuseStep 2518487 = 3777731) B3777731
theorem B3026393 : Blo 1678039 3026393 := bstep (se 2 (by rfl) ⟨1134897, by rfl⟩ : syracuseStep 3026393 = 2269795) B2269795
theorem B5664221 : Blo 1678039 5664221 := bstep (se 3 (by rfl) ⟨1062041, by rfl⟩ : syracuseStep 5664221 = 2124083) B2124083
theorem B2518553 : Blo 1678039 2518553 := bstep (se 2 (by rfl) ⟨944457, by rfl⟩ : syracuseStep 2518553 = 1888915) B1888915
theorem B1887799 : Blo 1678039 1887799 := bstep (se 1 (by rfl) ⟨1415849, by rfl⟩ : syracuseStep 1887799 = 2831699) B2831699
theorem B5746265 : Blo 1678039 5746265 := bstep (se 2 (by rfl) ⟨2154849, by rfl⟩ : syracuseStep 5746265 = 4309699) B4309699
theorem B2518667 : Blo 1678039 2518667 := bstep (se 1 (by rfl) ⟨1889000, by rfl⟩ : syracuseStep 2518667 = 3778001) B3778001
theorem B2518679 : Blo 1678039 2518679 := bstep (se 1 (by rfl) ⟨1889009, by rfl⟩ : syracuseStep 2518679 = 3778019) B3778019
theorem B5377715 : Blo 1678039 5377715 := bstep (se 1 (by rfl) ⟨4033286, by rfl⟩ : syracuseStep 5377715 = 8066573) B8066573
theorem B24219317 : Blo 1678039 24219317 := bstep (se 5 (by rfl) ⟨1135280, by rfl⟩ : syracuseStep 24219317 = 2270561) B2270561
theorem B2518745 : Blo 1678039 2518745 := bstep (se 2 (by rfl) ⟨944529, by rfl⟩ : syracuseStep 2518745 = 1889059) B1889059
theorem B1887979 : Blo 1678039 1887979 := bstep (se 1 (by rfl) ⟨1415984, by rfl⟩ : syracuseStep 1887979 = 2831969) B2831969
theorem B2518859 : Blo 1678039 2518859 := bstep (se 1 (by rfl) ⟨1889144, by rfl⟩ : syracuseStep 2518859 = 3778289) B3778289
theorem B1888087 : Blo 1678039 1888087 := bstep (se 1 (by rfl) ⟨1416065, by rfl⟩ : syracuseStep 1888087 = 2832131) B2832131
theorem B4034393 : Blo 1678039 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B2518871 : Blo 1678039 2518871 := bstep (se 1 (by rfl) ⟨1889153, by rfl⟩ : syracuseStep 2518871 = 3778307) B3778307
theorem B12930947 : Blo 1678039 12930947 := bstep (se 1 (by rfl) ⟨9698210, by rfl⟩ : syracuseStep 12930947 = 19396421) B19396421
theorem B3067787 : Blo 1678039 3067787 := bstep (se 1 (by rfl) ⟨2300840, by rfl⟩ : syracuseStep 3067787 = 4601681) B4601681
theorem B2518937 : Blo 1678039 2518937 := bstep (se 2 (by rfl) ⟨944601, by rfl⟩ : syracuseStep 2518937 = 1889203) B1889203
theorem B1888267 : Blo 1678039 1888267 := bstep (se 1 (by rfl) ⟨1416200, by rfl⟩ : syracuseStep 1888267 = 2832401) B2832401
theorem B2519051 : Blo 1678039 2519051 := bstep (se 1 (by rfl) ⟨1889288, by rfl⟩ : syracuseStep 2519051 = 3778577) B3778577
theorem B2519063 : Blo 1678039 2519063 := bstep (se 1 (by rfl) ⟨1889297, by rfl⟩ : syracuseStep 2519063 = 3778595) B3778595
theorem B43610147 : Blo 1678039 43610147 := bstep (se 1 (by rfl) ⟨32707610, by rfl⟩ : syracuseStep 43610147 = 65415221) B65415221
theorem B6385753 : Blo 1678039 6385753 := bstep (se 2 (by rfl) ⟨2394657, by rfl⟩ : syracuseStep 6385753 = 4789315) B4789315
theorem B2519129 : Blo 1678039 2519129 := bstep (se 2 (by rfl) ⟨944673, by rfl⟩ : syracuseStep 2519129 = 1889347) B1889347
theorem B1888375 : Blo 1678039 1888375 := bstep (se 1 (by rfl) ⟨1416281, by rfl⟩ : syracuseStep 1888375 = 2832563) B2832563
theorem B3633331 : Blo 1678039 3633331 := bstep (se 1 (by rfl) ⟨2724998, by rfl⟩ : syracuseStep 3633331 = 5449997) B5449997
theorem B4780235 : Blo 1678039 4780235 := bstep (se 1 (by rfl) ⟨3585176, by rfl⟩ : syracuseStep 4780235 = 7170353) B7170353
theorem B2519243 : Blo 1678039 2519243 := bstep (se 1 (by rfl) ⟨1889432, by rfl⟩ : syracuseStep 2519243 = 3778865) B3778865
theorem B2126027 : Blo 1678039 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B2519255 : Blo 1678039 2519255 := bstep (se 1 (by rfl) ⟨1889441, by rfl⟩ : syracuseStep 2519255 = 3778883) B3778883
theorem B12095705 : Blo 1678039 12095705 := bstep (se 2 (by rfl) ⟨4535889, by rfl⟩ : syracuseStep 12095705 = 9071779) B9071779
theorem B2519321 : Blo 1678039 2519321 := bstep (se 2 (by rfl) ⟨944745, by rfl⟩ : syracuseStep 2519321 = 1889491) B1889491
theorem B1888555 : Blo 1678039 1888555 := bstep (se 1 (by rfl) ⟨1416416, by rfl⟩ : syracuseStep 1888555 = 2832833) B2832833
theorem B4247873 : Blo 1678039 4247873 := bstep (se 2 (by rfl) ⟨1592952, by rfl⟩ : syracuseStep 4247873 = 3185905) B3185905
theorem B12095819 : Blo 1678039 12095819 := bstep (se 1 (by rfl) ⟨9071864, by rfl⟩ : syracuseStep 12095819 = 18143729) B18143729
theorem B2519435 : Blo 1678039 2519435 := bstep (se 1 (by rfl) ⟨1889576, by rfl⟩ : syracuseStep 2519435 = 3779153) B3779153
theorem B1888663 : Blo 1678039 1888663 := bstep (se 1 (by rfl) ⟨1416497, by rfl⟩ : syracuseStep 1888663 = 2832995) B2832995
theorem B11489687 : Blo 1678039 11489687 := bstep (se 1 (by rfl) ⟨8617265, by rfl⟩ : syracuseStep 11489687 = 17234531) B17234531
theorem B2519447 : Blo 1678039 2519447 := bstep (se 1 (by rfl) ⟨1889585, by rfl⟩ : syracuseStep 2519447 = 3779171) B3779171
theorem B5378483 : Blo 1678039 5378483 := bstep (se 1 (by rfl) ⟨4033862, by rfl⟩ : syracuseStep 5378483 = 8067725) B8067725
theorem B3584459 : Blo 1678039 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B2519513 : Blo 1678039 2519513 := bstep (se 2 (by rfl) ⟨944817, by rfl⟩ : syracuseStep 2519513 = 1889635) B1889635
theorem B6050321 : Blo 1678039 6050321 := bstep (se 2 (by rfl) ⟨2268870, by rfl⟩ : syracuseStep 6050321 = 4537741) B4537741
theorem B5665355 : Blo 1678039 5665355 := bstep (se 1 (by rfl) ⟨4249016, by rfl⟩ : syracuseStep 5665355 = 8498033) B8498033
theorem B1888843 : Blo 1678039 1888843 := bstep (se 1 (by rfl) ⟨1416632, by rfl⟩ : syracuseStep 1888843 = 2833265) B2833265
theorem B2519627 : Blo 1678039 2519627 := bstep (se 1 (by rfl) ⟨1889720, by rfl⟩ : syracuseStep 2519627 = 3779441) B3779441
theorem B2519639 : Blo 1678039 2519639 := bstep (se 1 (by rfl) ⟨1889729, by rfl⟩ : syracuseStep 2519639 = 3779459) B3779459
theorem B7369309 : Blo 1678039 7369309 := bstep (se 3 (by rfl) ⟨1381745, by rfl⟩ : syracuseStep 7369309 = 2763491) B2763491
theorem B15323741 : Blo 1678039 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B2519705 : Blo 1678039 2519705 := bstep (se 2 (by rfl) ⟨944889, by rfl⟩ : syracuseStep 2519705 = 1889779) B1889779
theorem B1888951 : Blo 1678039 1888951 := bstep (se 1 (by rfl) ⟨1416713, by rfl⟩ : syracuseStep 1888951 = 2833427) B2833427
theorem B6804161 : Blo 1678039 6804161 := bstep (se 2 (by rfl) ⟨2551560, by rfl⟩ : syracuseStep 6804161 = 5103121) B5103121
theorem B2519819 : Blo 1678039 2519819 := bstep (se 1 (by rfl) ⟨1889864, by rfl⟩ : syracuseStep 2519819 = 3779729) B3779729
theorem B2519831 : Blo 1678039 2519831 := bstep (se 1 (by rfl) ⟨1889873, by rfl⟩ : syracuseStep 2519831 = 3779747) B3779747
theorem B5378881 : Blo 1678039 5378881 := bstep (se 2 (by rfl) ⟨2017080, by rfl⟩ : syracuseStep 5378881 = 4034161) B4034161
theorem B4248409 : Blo 1678039 4248409 := bstep (se 2 (by rfl) ⟨1593153, by rfl⟩ : syracuseStep 4248409 = 3186307) B3186307
theorem B5665625 : Blo 1678039 5665625 := bstep (se 2 (by rfl) ⟨2124609, by rfl⟩ : syracuseStep 5665625 = 4249219) B4249219
theorem B2519897 : Blo 1678039 2519897 := bstep (se 2 (by rfl) ⟨944961, by rfl⟩ : syracuseStep 2519897 = 1889923) B1889923
theorem B14349149 : Blo 1678039 14349149 := bstep (se 3 (by rfl) ⟨2690465, by rfl⟩ : syracuseStep 14349149 = 5380931) B5380931
theorem B1889131 : Blo 1678039 1889131 := bstep (se 1 (by rfl) ⟨1416848, by rfl⟩ : syracuseStep 1889131 = 2833697) B2833697
theorem B6378371 : Blo 1678039 6378371 := bstep (se 1 (by rfl) ⟨4783778, by rfl⟩ : syracuseStep 6378371 = 9567557) B9567557
theorem B6378385 : Blo 1678039 6378385 := bstep (se 2 (by rfl) ⟨2391894, by rfl⟩ : syracuseStep 6378385 = 4783789) B4783789
theorem B51680177 : Blo 1678039 51680177 := bstep (se 2 (by rfl) ⟨19380066, by rfl⟩ : syracuseStep 51680177 = 38760133) B38760133
theorem B5378995 : Blo 1678039 5378995 := bstep (se 1 (by rfl) ⟨4034246, by rfl⟩ : syracuseStep 5378995 = 8068493) B8068493
theorem B2520011 : Blo 1678039 2520011 := bstep (se 1 (by rfl) ⟨1890008, by rfl⟩ : syracuseStep 2520011 = 3780017) B3780017
theorem B1889239 : Blo 1678039 1889239 := bstep (se 1 (by rfl) ⟨1416929, by rfl⟩ : syracuseStep 1889239 = 2833859) B2833859
theorem B2520023 : Blo 1678039 2520023 := bstep (se 1 (by rfl) ⟨1890017, by rfl⟩ : syracuseStep 2520023 = 3780035) B3780035
theorem B10753069 : Blo 1678039 10753069 := bstep (se 3 (by rfl) ⟨2016200, by rfl⟩ : syracuseStep 10753069 = 4032401) B4032401
theorem B30626885 : Blo 1678039 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B1889419 : Blo 1678039 1889419 := bstep (se 1 (by rfl) ⟨1417064, by rfl⟩ : syracuseStep 1889419 = 2834129) B2834129
theorem B6378689 : Blo 1678039 6378689 := bstep (se 2 (by rfl) ⟨2392008, by rfl⟩ : syracuseStep 6378689 = 4784017) B4784017
theorem B1889527 : Blo 1678039 1889527 := bstep (se 1 (by rfl) ⟨1417145, by rfl⟩ : syracuseStep 1889527 = 2834291) B2834291
theorem B40850837 : Blo 1678039 40850837 := bstep (se 6 (by rfl) ⟨957441, by rfl⟩ : syracuseStep 40850837 = 1914883) B1914883
theorem B1889707 : Blo 1678039 1889707 := bstep (se 1 (by rfl) ⟨1417280, by rfl⟩ : syracuseStep 1889707 = 2834561) B2834561
theorem B5666327 : Blo 1678039 5666327 := bstep (se 1 (by rfl) ⟨4249745, by rfl⟩ : syracuseStep 5666327 = 8499491) B8499491
theorem B7271959 : Blo 1678039 7271959 := bstep (se 1 (by rfl) ⟨5453969, by rfl⟩ : syracuseStep 7271959 = 10907939) B10907939
theorem B1889815 : Blo 1678039 1889815 := bstep (se 1 (by rfl) ⟨1417361, by rfl⟩ : syracuseStep 1889815 = 2834723) B2834723
theorem B12105251 : Blo 1678039 12105251 := bstep (se 1 (by rfl) ⟨9078938, by rfl⟩ : syracuseStep 12105251 = 18157877) B18157877
theorem B17225291 : Blo 1678039 17225291 := bstep (se 1 (by rfl) ⟨12918968, by rfl⟩ : syracuseStep 17225291 = 25837937) B25837937
theorem B1914455 : Blo 1678039 1914455 := bstep (se 1 (by rfl) ⟨1435841, by rfl⟩ : syracuseStep 1914455 = 2871683) B2871683
theorem B2832023 : Blo 1678039 2832023 := bstep (se 1 (by rfl) ⟨2124017, by rfl⟩ : syracuseStep 2832023 = 4248035) B4248035
theorem B9565847 : Blo 1678039 9565847 := bstep (se 1 (by rfl) ⟨7174385, by rfl⟩ : syracuseStep 9565847 = 14348771) B14348771
theorem B2389657 : Blo 1678039 2389657 := bstep (se 2 (by rfl) ⟨896121, by rfl⟩ : syracuseStep 2389657 = 1792243) B1792243
theorem B7173805 : Blo 1678039 7173805 := bstep (se 3 (by rfl) ⟨1345088, by rfl⟩ : syracuseStep 7173805 = 2690177) B2690177
theorem B12105395 : Blo 1678039 12105395 := bstep (se 1 (by rfl) ⟨9079046, by rfl⟩ : syracuseStep 12105395 = 18158093) B18158093
theorem B1889995 : Blo 1678039 1889995 := bstep (se 1 (by rfl) ⟨1417496, by rfl⟩ : syracuseStep 1889995 = 2834993) B2834993
theorem B2832151 : Blo 1678039 2832151 := bstep (se 1 (by rfl) ⟨2124113, by rfl⟩ : syracuseStep 2832151 = 4248227) B4248227
theorem B4536215 : Blo 1678039 4536215 := bstep (se 1 (by rfl) ⟨3402161, by rfl⟩ : syracuseStep 4536215 = 6804323) B6804323
theorem B4249523 : Blo 1678039 4249523 := bstep (se 1 (by rfl) ⟨3187142, by rfl⟩ : syracuseStep 4249523 = 6374285) B6374285
theorem B2873291 : Blo 1678039 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B5666867 : Blo 1678039 5666867 := bstep (se 1 (by rfl) ⟨4250150, by rfl⟩ : syracuseStep 5666867 = 8500301) B8500301
theorem B4249817 : Blo 1678039 4249817 := bstep (se 2 (by rfl) ⟨1593681, by rfl⟩ : syracuseStep 4249817 = 3187363) B3187363
theorem B5667137 : Blo 1678039 5667137 := bstep (se 2 (by rfl) ⟨2125176, by rfl⟩ : syracuseStep 5667137 = 4250353) B4250353
theorem B8501597 : Blo 1678039 8501597 := bstep (se 3 (by rfl) ⟨1594049, by rfl⟩ : syracuseStep 8501597 = 3188099) B3188099
theorem B25852277 : Blo 1678039 25852277 := bstep (se 5 (by rfl) ⟨1211825, by rfl⟩ : syracuseStep 25852277 = 2423651) B2423651
theorem B2832779 : Blo 1678039 2832779 := bstep (se 1 (by rfl) ⟨2124584, by rfl⟩ : syracuseStep 2832779 = 4249169) B4249169
theorem B2423191 : Blo 1678039 2423191 := bstep (se 1 (by rfl) ⟨1817393, by rfl⟩ : syracuseStep 2423191 = 3634787) B3634787
theorem B2832907 : Blo 1678039 2832907 := bstep (se 1 (by rfl) ⟨2124680, by rfl⟩ : syracuseStep 2832907 = 4249361) B4249361
theorem B6371885 : Blo 1678039 6371885 := bstep (se 3 (by rfl) ⟨1194728, by rfl⟩ : syracuseStep 6371885 = 2389457) B2389457
theorem B4782685 : Blo 1678039 4782685 := bstep (se 3 (by rfl) ⟨896753, by rfl⟩ : syracuseStep 4782685 = 1793507) B1793507
theorem B1915531 : Blo 1678039 1915531 := bstep (se 1 (by rfl) ⟨1436648, by rfl⟩ : syracuseStep 1915531 = 2873297) B2873297
theorem B2833049 : Blo 1678039 2833049 := bstep (se 2 (by rfl) ⟨1062393, by rfl⟩ : syracuseStep 2833049 = 2124787) B2124787
theorem B1678039 : Blo 1678039 1678039 := bstep (se 1 (by rfl) ⟨1258529, by rfl⟩ : syracuseStep 1678039 = 2517059) B2517059
theorem B1678059 : Blo 1678039 1678059 := bstep (se 1 (by rfl) ⟨1258544, by rfl⟩ : syracuseStep 1678059 = 2517089) B2517089
theorem B1678071 : Blo 1678039 1678071 := bstep (se 1 (by rfl) ⟨1258553, by rfl⟩ : syracuseStep 1678071 = 2517107) B2517107
theorem B3586817 : Blo 1678039 3586817 := bstep (se 2 (by rfl) ⟨1345056, by rfl⟩ : syracuseStep 3586817 = 2690113) B2690113
theorem B1678091 : Blo 1678039 1678091 := bstep (se 1 (by rfl) ⟨1258568, by rfl⟩ : syracuseStep 1678091 = 2517137) B2517137
theorem B1678103 : Blo 1678039 1678103 := bstep (se 1 (by rfl) ⟨1258577, by rfl⟩ : syracuseStep 1678103 = 2517155) B2517155
theorem B2833177 : Blo 1678039 2833177 := bstep (se 2 (by rfl) ⟨1062441, by rfl⟩ : syracuseStep 2833177 = 2124883) B2124883
theorem B1678123 : Blo 1678039 1678123 := bstep (se 1 (by rfl) ⟨1258592, by rfl⟩ : syracuseStep 1678123 = 2517185) B2517185
theorem B1678135 : Blo 1678039 1678135 := bstep (se 1 (by rfl) ⟨1258601, by rfl⟩ : syracuseStep 1678135 = 2517203) B2517203
theorem B1678155 : Blo 1678039 1678155 := bstep (se 1 (by rfl) ⟨1258616, by rfl⟩ : syracuseStep 1678155 = 2517233) B2517233
theorem B1678167 : Blo 1678039 1678167 := bstep (se 1 (by rfl) ⟨1258625, by rfl⟩ : syracuseStep 1678167 = 2517251) B2517251
theorem B3152729 : Blo 1678039 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B5667677 : Blo 1678039 5667677 := bstep (se 3 (by rfl) ⟨1062689, by rfl⟩ : syracuseStep 5667677 = 2125379) B2125379
theorem B1678187 : Blo 1678039 1678187 := bstep (se 1 (by rfl) ⟨1258640, by rfl⟩ : syracuseStep 1678187 = 2517281) B2517281
theorem B1678199 : Blo 1678039 1678199 := bstep (se 1 (by rfl) ⟨1258649, by rfl⟩ : syracuseStep 1678199 = 2517299) B2517299
theorem B1678219 : Blo 1678039 1678219 := bstep (se 1 (by rfl) ⟨1258664, by rfl⟩ : syracuseStep 1678219 = 2517329) B2517329
theorem B1678231 : Blo 1678039 1678231 := bstep (se 1 (by rfl) ⟨1258673, by rfl⟩ : syracuseStep 1678231 = 2517347) B2517347
theorem B1678251 : Blo 1678039 1678251 := bstep (se 1 (by rfl) ⟨1258688, by rfl⟩ : syracuseStep 1678251 = 2517377) B2517377
theorem B1678263 : Blo 1678039 1678263 := bstep (se 1 (by rfl) ⟨1258697, by rfl⟩ : syracuseStep 1678263 = 2517395) B2517395
theorem B1678283 : Blo 1678039 1678283 := bstep (se 1 (by rfl) ⟨1258712, by rfl⟩ : syracuseStep 1678283 = 2517425) B2517425
theorem B1678295 : Blo 1678039 1678295 := bstep (se 1 (by rfl) ⟨1258721, by rfl⟩ : syracuseStep 1678295 = 2517443) B2517443
theorem B1678315 : Blo 1678039 1678315 := bstep (se 1 (by rfl) ⟨1258736, by rfl⟩ : syracuseStep 1678315 = 2517473) B2517473
theorem B1678327 : Blo 1678039 1678327 := bstep (se 1 (by rfl) ⟨1258745, by rfl⟩ : syracuseStep 1678327 = 2517491) B2517491
theorem B1678347 : Blo 1678039 1678347 := bstep (se 1 (by rfl) ⟨1258760, by rfl⟩ : syracuseStep 1678347 = 2517521) B2517521
theorem B1678359 : Blo 1678039 1678359 := bstep (se 1 (by rfl) ⟨1258769, by rfl⟩ : syracuseStep 1678359 = 2517539) B2517539
theorem B1678379 : Blo 1678039 1678379 := bstep (se 1 (by rfl) ⟨1258784, by rfl⟩ : syracuseStep 1678379 = 2517569) B2517569
theorem B1678391 : Blo 1678039 1678391 := bstep (se 1 (by rfl) ⟨1258793, by rfl⟩ : syracuseStep 1678391 = 2517587) B2517587
theorem B1678411 : Blo 1678039 1678411 := bstep (se 1 (by rfl) ⟨1258808, by rfl⟩ : syracuseStep 1678411 = 2517617) B2517617
theorem B2391115 : Blo 1678039 2391115 := bstep (se 1 (by rfl) ⟨1793336, by rfl⟩ : syracuseStep 2391115 = 3586673) B3586673
theorem B1678423 : Blo 1678039 1678423 := bstep (se 1 (by rfl) ⟨1258817, by rfl⟩ : syracuseStep 1678423 = 2517635) B2517635
theorem B3587159 : Blo 1678039 3587159 := bstep (se 1 (by rfl) ⟨2690369, by rfl⟩ : syracuseStep 3587159 = 5380739) B5380739
theorem B1678443 : Blo 1678039 1678443 := bstep (se 1 (by rfl) ⟨1258832, by rfl⟩ : syracuseStep 1678443 = 2517665) B2517665
theorem B1678455 : Blo 1678039 1678455 := bstep (se 1 (by rfl) ⟨1258841, by rfl⟩ : syracuseStep 1678455 = 2517683) B2517683
theorem B1678475 : Blo 1678039 1678475 := bstep (se 1 (by rfl) ⟨1258856, by rfl⟩ : syracuseStep 1678475 = 2517713) B2517713
theorem B1678487 : Blo 1678039 1678487 := bstep (se 1 (by rfl) ⟨1258865, by rfl⟩ : syracuseStep 1678487 = 2517731) B2517731
theorem B1678507 : Blo 1678039 1678507 := bstep (se 1 (by rfl) ⟨1258880, by rfl⟩ : syracuseStep 1678507 = 2517761) B2517761
theorem B13614257 : Blo 1678039 13614257 := bstep (se 2 (by rfl) ⟨5105346, by rfl⟩ : syracuseStep 13614257 = 10210693) B10210693
theorem B12754097 : Blo 1678039 12754097 := bstep (se 2 (by rfl) ⟨4782786, by rfl⟩ : syracuseStep 12754097 = 9565573) B9565573
theorem B1678519 : Blo 1678039 1678519 := bstep (se 1 (by rfl) ⟨1258889, by rfl⟩ : syracuseStep 1678519 = 2517779) B2517779
theorem B3185867 : Blo 1678039 3185867 := bstep (se 1 (by rfl) ⟨2389400, by rfl⟩ : syracuseStep 3185867 = 4778801) B4778801
theorem B1678539 : Blo 1678039 1678539 := bstep (se 1 (by rfl) ⟨1258904, by rfl⟩ : syracuseStep 1678539 = 2517809) B2517809
theorem B19127501 : Blo 1678039 19127501 := bstep (se 3 (by rfl) ⟨3586406, by rfl⟩ : syracuseStep 19127501 = 7172813) B7172813
theorem B1678551 : Blo 1678039 1678551 := bstep (se 1 (by rfl) ⟨1258913, by rfl⟩ : syracuseStep 1678551 = 2517827) B2517827
theorem B1678571 : Blo 1678039 1678571 := bstep (se 1 (by rfl) ⟨1258928, by rfl⟩ : syracuseStep 1678571 = 2517857) B2517857
theorem B1678583 : Blo 1678039 1678583 := bstep (se 1 (by rfl) ⟨1258937, by rfl⟩ : syracuseStep 1678583 = 2517875) B2517875
theorem B1678603 : Blo 1678039 1678603 := bstep (se 1 (by rfl) ⟨1258952, by rfl⟩ : syracuseStep 1678603 = 2517905) B2517905
theorem B1678615 : Blo 1678039 1678615 := bstep (se 1 (by rfl) ⟨1258961, by rfl⟩ : syracuseStep 1678615 = 2517923) B2517923
theorem B3775769 : Blo 1678039 3775769 := bstep (se 2 (by rfl) ⟨1415913, by rfl⟩ : syracuseStep 3775769 = 2831827) B2831827
theorem B1678635 : Blo 1678039 1678635 := bstep (se 1 (by rfl) ⟨1258976, by rfl⟩ : syracuseStep 1678635 = 2517953) B2517953
theorem B1793323 : Blo 1678039 1793323 := bstep (se 1 (by rfl) ⟨1344992, by rfl⟩ : syracuseStep 1793323 = 2689985) B2689985
theorem B1678647 : Blo 1678039 1678647 := bstep (se 1 (by rfl) ⟨1258985, by rfl⟩ : syracuseStep 1678647 = 2517971) B2517971
theorem B1678667 : Blo 1678039 1678667 := bstep (se 1 (by rfl) ⟨1259000, by rfl⟩ : syracuseStep 1678667 = 2518001) B2518001
theorem B1678679 : Blo 1678039 1678679 := bstep (se 1 (by rfl) ⟨1259009, by rfl⟩ : syracuseStep 1678679 = 2518019) B2518019
theorem B2833751 : Blo 1678039 2833751 := bstep (se 1 (by rfl) ⟨2125313, by rfl⟩ : syracuseStep 2833751 = 4250627) B4250627
theorem B1678699 : Blo 1678039 1678699 := bstep (se 1 (by rfl) ⟨1259024, by rfl⟩ : syracuseStep 1678699 = 2518049) B2518049
theorem B3775859 : Blo 1678039 3775859 := bstep (se 1 (by rfl) ⟨2831894, by rfl⟩ : syracuseStep 3775859 = 5663789) B5663789
theorem B1678711 : Blo 1678039 1678711 := bstep (se 1 (by rfl) ⟨1259033, by rfl⟩ : syracuseStep 1678711 = 2518067) B2518067
theorem B3186049 : Blo 1678039 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B1678731 : Blo 1678039 1678731 := bstep (se 1 (by rfl) ⟨1259048, by rfl⟩ : syracuseStep 1678731 = 2518097) B2518097
theorem B4660631 : Blo 1678039 4660631 := bstep (se 1 (by rfl) ⟨3495473, by rfl⟩ : syracuseStep 4660631 = 6990947) B6990947
theorem B3775895 : Blo 1678039 3775895 := bstep (se 1 (by rfl) ⟨2831921, by rfl⟩ : syracuseStep 3775895 = 5663843) B5663843
theorem B1678743 : Blo 1678039 1678743 := bstep (se 1 (by rfl) ⟨1259057, by rfl⟩ : syracuseStep 1678743 = 2518115) B2518115
theorem B1678763 : Blo 1678039 1678763 := bstep (se 1 (by rfl) ⟨1259072, by rfl⟩ : syracuseStep 1678763 = 2518145) B2518145
theorem B1678775 : Blo 1678039 1678775 := bstep (se 1 (by rfl) ⟨1259081, by rfl⟩ : syracuseStep 1678775 = 2518163) B2518163
theorem B1678795 : Blo 1678039 1678795 := bstep (se 1 (by rfl) ⟨1259096, by rfl⟩ : syracuseStep 1678795 = 2518193) B2518193
theorem B3882443 : Blo 1678039 3882443 := bstep (se 1 (by rfl) ⟨2911832, by rfl⟩ : syracuseStep 3882443 = 5823665) B5823665
theorem B1678807 : Blo 1678039 1678807 := bstep (se 1 (by rfl) ⟨1259105, by rfl⟩ : syracuseStep 1678807 = 2518211) B2518211
theorem B2833879 : Blo 1678039 2833879 := bstep (se 1 (by rfl) ⟨2125409, by rfl⟩ : syracuseStep 2833879 = 4250819) B4250819
theorem B24206809 : Blo 1678039 24206809 := bstep (se 2 (by rfl) ⟨9077553, by rfl⟩ : syracuseStep 24206809 = 18155107) B18155107
theorem B1678827 : Blo 1678039 1678827 := bstep (se 1 (by rfl) ⟨1259120, by rfl⟩ : syracuseStep 1678827 = 2518241) B2518241
theorem B1678839 : Blo 1678039 1678839 := bstep (se 1 (by rfl) ⟨1259129, by rfl⟩ : syracuseStep 1678839 = 2518259) B2518259
theorem B1678859 : Blo 1678039 1678859 := bstep (se 1 (by rfl) ⟨1259144, by rfl⟩ : syracuseStep 1678859 = 2518289) B2518289
theorem B1678871 : Blo 1678039 1678871 := bstep (se 1 (by rfl) ⟨1259153, by rfl⟩ : syracuseStep 1678871 = 2518307) B2518307
theorem B2268697 : Blo 1678039 2268697 := bstep (se 2 (by rfl) ⟨850761, by rfl⟩ : syracuseStep 2268697 = 1701523) B1701523
theorem B1678891 : Blo 1678039 1678891 := bstep (se 1 (by rfl) ⟨1259168, by rfl⟩ : syracuseStep 1678891 = 2518337) B2518337
theorem B1678903 : Blo 1678039 1678903 := bstep (se 1 (by rfl) ⟨1259177, by rfl⟩ : syracuseStep 1678903 = 2518355) B2518355
theorem B3776075 : Blo 1678039 3776075 := bstep (se 1 (by rfl) ⟨2832056, by rfl⟩ : syracuseStep 3776075 = 5664113) B5664113
theorem B1678923 : Blo 1678039 1678923 := bstep (se 1 (by rfl) ⟨1259192, by rfl⟩ : syracuseStep 1678923 = 2518385) B2518385
theorem B1678935 : Blo 1678039 1678935 := bstep (se 1 (by rfl) ⟨1259201, by rfl⟩ : syracuseStep 1678935 = 2518403) B2518403
theorem B1678955 : Blo 1678039 1678955 := bstep (se 1 (by rfl) ⟨1259216, by rfl⟩ : syracuseStep 1678955 = 2518433) B2518433
theorem B1678967 : Blo 1678039 1678967 := bstep (se 1 (by rfl) ⟨1259225, by rfl⟩ : syracuseStep 1678967 = 2518451) B2518451
theorem B3776129 : Blo 1678039 3776129 := bstep (se 2 (by rfl) ⟨1416048, by rfl⟩ : syracuseStep 3776129 = 2832097) B2832097
theorem B1678987 : Blo 1678039 1678987 := bstep (se 1 (by rfl) ⟨1259240, by rfl⟩ : syracuseStep 1678987 = 2518481) B2518481
theorem B3587723 : Blo 1678039 3587723 := bstep (se 1 (by rfl) ⟨2690792, by rfl⟩ : syracuseStep 3587723 = 5381585) B5381585
theorem B1678999 : Blo 1678039 1678999 := bstep (se 1 (by rfl) ⟨1259249, by rfl⟩ : syracuseStep 1678999 = 2518499) B2518499
theorem B12754583 : Blo 1678039 12754583 := bstep (se 1 (by rfl) ⟨9565937, by rfl⟩ : syracuseStep 12754583 = 19131875) B19131875
theorem B1679019 : Blo 1678039 1679019 := bstep (se 1 (by rfl) ⟨1259264, by rfl⟩ : syracuseStep 1679019 = 2518529) B2518529
theorem B1679031 : Blo 1678039 1679031 := bstep (se 1 (by rfl) ⟨1259273, by rfl⟩ : syracuseStep 1679031 = 2518547) B2518547
theorem B1679051 : Blo 1678039 1679051 := bstep (se 1 (by rfl) ⟨1259288, by rfl⟩ : syracuseStep 1679051 = 2518577) B2518577
theorem B3186391 : Blo 1678039 3186391 := bstep (se 1 (by rfl) ⟨2389793, by rfl⟩ : syracuseStep 3186391 = 4779587) B4779587
theorem B1679063 : Blo 1678039 1679063 := bstep (se 1 (by rfl) ⟨1259297, by rfl⟩ : syracuseStep 1679063 = 2518595) B2518595
theorem B1679083 : Blo 1678039 1679083 := bstep (se 1 (by rfl) ⟨1259312, by rfl⟩ : syracuseStep 1679083 = 2518625) B2518625
theorem B1679095 : Blo 1678039 1679095 := bstep (se 1 (by rfl) ⟨1259321, by rfl⟩ : syracuseStep 1679095 = 2518643) B2518643
theorem B1679115 : Blo 1678039 1679115 := bstep (se 1 (by rfl) ⟨1259336, by rfl⟩ : syracuseStep 1679115 = 2518673) B2518673
theorem B1679127 : Blo 1678039 1679127 := bstep (se 1 (by rfl) ⟨1259345, by rfl⟩ : syracuseStep 1679127 = 2518691) B2518691
theorem B1679147 : Blo 1678039 1679147 := bstep (se 1 (by rfl) ⟨1259360, by rfl⟩ : syracuseStep 1679147 = 2518721) B2518721
theorem B1679159 : Blo 1678039 1679159 := bstep (se 1 (by rfl) ⟨1259369, by rfl⟩ : syracuseStep 1679159 = 2518739) B2518739
theorem B1679179 : Blo 1678039 1679179 := bstep (se 1 (by rfl) ⟨1259384, by rfl⟩ : syracuseStep 1679179 = 2518769) B2518769
theorem B4251467 : Blo 1678039 4251467 := bstep (se 1 (by rfl) ⟨3188600, by rfl⟩ : syracuseStep 4251467 = 6377201) B6377201
theorem B6053707 : Blo 1678039 6053707 := bstep (se 1 (by rfl) ⟨4540280, by rfl⟩ : syracuseStep 6053707 = 9080561) B9080561
theorem B1679191 : Blo 1678039 1679191 := bstep (se 1 (by rfl) ⟨1259393, by rfl⟩ : syracuseStep 1679191 = 2518787) B2518787
theorem B3776345 : Blo 1678039 3776345 := bstep (se 2 (by rfl) ⟨1416129, by rfl⟩ : syracuseStep 3776345 = 2832259) B2832259
theorem B7659353 : Blo 1678039 7659353 := bstep (se 2 (by rfl) ⟨2872257, by rfl⟩ : syracuseStep 7659353 = 5744515) B5744515
theorem B4783961 : Blo 1678039 4783961 := bstep (se 2 (by rfl) ⟨1793985, by rfl⟩ : syracuseStep 4783961 = 3587971) B3587971
theorem B30637925 : Blo 1678039 30637925 := bstep (se 4 (by rfl) ⟨2872305, by rfl⟩ : syracuseStep 30637925 = 5744611) B5744611
theorem B1679211 : Blo 1678039 1679211 := bstep (se 1 (by rfl) ⟨1259408, by rfl⟩ : syracuseStep 1679211 = 2518817) B2518817
theorem B1679223 : Blo 1678039 1679223 := bstep (se 1 (by rfl) ⟨1259417, by rfl⟩ : syracuseStep 1679223 = 2518835) B2518835
theorem B1679243 : Blo 1678039 1679243 := bstep (se 1 (by rfl) ⟨1259432, by rfl⟩ : syracuseStep 1679243 = 2518865) B2518865
theorem B1679255 : Blo 1678039 1679255 := bstep (se 1 (by rfl) ⟨1259441, by rfl⟩ : syracuseStep 1679255 = 2518883) B2518883
theorem B1679275 : Blo 1678039 1679275 := bstep (se 1 (by rfl) ⟨1259456, by rfl⟩ : syracuseStep 1679275 = 2518913) B2518913
theorem B3776435 : Blo 1678039 3776435 := bstep (se 1 (by rfl) ⟨2832326, by rfl⟩ : syracuseStep 3776435 = 5664653) B5664653
theorem B3186611 : Blo 1678039 3186611 := bstep (se 1 (by rfl) ⟨2389958, by rfl⟩ : syracuseStep 3186611 = 4779917) B4779917
theorem B1679287 : Blo 1678039 1679287 := bstep (se 1 (by rfl) ⟨1259465, by rfl⟩ : syracuseStep 1679287 = 2518931) B2518931
theorem B6373313 : Blo 1678039 6373313 := bstep (se 2 (by rfl) ⟨2389992, by rfl⟩ : syracuseStep 6373313 = 4779985) B4779985
theorem B1679307 : Blo 1678039 1679307 := bstep (se 1 (by rfl) ⟨1259480, by rfl⟩ : syracuseStep 1679307 = 2518961) B2518961
theorem B5668811 : Blo 1678039 5668811 := bstep (se 1 (by rfl) ⟨4251608, by rfl⟩ : syracuseStep 5668811 = 8503217) B8503217
theorem B3776471 : Blo 1678039 3776471 := bstep (se 1 (by rfl) ⟨2832353, by rfl⟩ : syracuseStep 3776471 = 5664707) B5664707
theorem B1679319 : Blo 1678039 1679319 := bstep (se 1 (by rfl) ⟨1259489, by rfl⟩ : syracuseStep 1679319 = 2518979) B2518979
theorem B1679339 : Blo 1678039 1679339 := bstep (se 1 (by rfl) ⟨1259504, by rfl⟩ : syracuseStep 1679339 = 2519009) B2519009
theorem B1679351 : Blo 1678039 1679351 := bstep (se 1 (by rfl) ⟨1259513, by rfl⟩ : syracuseStep 1679351 = 2519027) B2519027
theorem B4251649 : Blo 1678039 4251649 := bstep (se 2 (by rfl) ⟨1594368, by rfl⟩ : syracuseStep 4251649 = 3188737) B3188737
theorem B1679367 : Blo 1678039 1679367 := bstep (se 1 (by rfl) ⟨1259525, by rfl⟩ : syracuseStep 1679367 = 2519051) B2519051
theorem B1679375 : Blo 1678039 1679375 := bstep (se 1 (by rfl) ⟨1259531, by rfl⟩ : syracuseStep 1679375 = 2519063) B2519063
theorem B4784143 : Blo 1678039 4784143 := bstep (se 1 (by rfl) ⟨3588107, by rfl⟩ : syracuseStep 4784143 = 7176215) B7176215
theorem B29073431 : Blo 1678039 29073431 := bstep (se 1 (by rfl) ⟨21805073, by rfl⟩ : syracuseStep 29073431 = 43610147) B43610147
theorem B5382173 : Blo 1678039 5382173 := bstep (se 3 (by rfl) ⟨1009157, by rfl⟩ : syracuseStep 5382173 = 2018315) B2018315
theorem B1679419 : Blo 1678039 1679419 := bstep (se 1 (by rfl) ⟨1259564, by rfl⟩ : syracuseStep 1679419 = 2519129) B2519129
theorem B1679495 : Blo 1678039 1679495 := bstep (se 1 (by rfl) ⟨1259621, by rfl⟩ : syracuseStep 1679495 = 2519243) B2519243
theorem B1679503 : Blo 1678039 1679503 := bstep (se 1 (by rfl) ⟨1259627, by rfl⟩ : syracuseStep 1679503 = 2519255) B2519255
theorem B1679547 : Blo 1678039 1679547 := bstep (se 1 (by rfl) ⟨1259660, by rfl⟩ : syracuseStep 1679547 = 2519321) B2519321
theorem B1679623 : Blo 1678039 1679623 := bstep (se 1 (by rfl) ⟨1259717, by rfl⟩ : syracuseStep 1679623 = 2519435) B2519435
theorem B7659791 : Blo 1678039 7659791 := bstep (se 1 (by rfl) ⟨5744843, by rfl⟩ : syracuseStep 7659791 = 11489687) B11489687
theorem B1679631 : Blo 1678039 1679631 := bstep (se 1 (by rfl) ⟨1259723, by rfl⟩ : syracuseStep 1679631 = 2519447) B2519447
theorem B5669135 : Blo 1678039 5669135 := bstep (se 1 (by rfl) ⟨4251851, by rfl⟩ : syracuseStep 5669135 = 8503703) B8503703
theorem B1679675 : Blo 1678039 1679675 := bstep (se 1 (by rfl) ⟨1259756, by rfl⟩ : syracuseStep 1679675 = 2519513) B2519513
theorem B8618329 : Blo 1678039 8618329 := bstep (se 2 (by rfl) ⟨3231873, by rfl⟩ : syracuseStep 8618329 = 6463747) B6463747
theorem B3776903 : Blo 1678039 3776903 := bstep (se 1 (by rfl) ⟨2832677, by rfl⟩ : syracuseStep 3776903 = 5665355) B5665355
theorem B1679751 : Blo 1678039 1679751 := bstep (se 1 (by rfl) ⟨1259813, by rfl⟩ : syracuseStep 1679751 = 2519627) B2519627
theorem B1679759 : Blo 1678039 1679759 := bstep (se 1 (by rfl) ⟨1259819, by rfl⟩ : syracuseStep 1679759 = 2519639) B2519639
theorem B10215827 : Blo 1678039 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B1679803 : Blo 1678039 1679803 := bstep (se 1 (by rfl) ⟨1259852, by rfl⟩ : syracuseStep 1679803 = 2519705) B2519705
theorem B1679879 : Blo 1678039 1679879 := bstep (se 1 (by rfl) ⟨1259909, by rfl⟩ : syracuseStep 1679879 = 2519819) B2519819
theorem B1679887 : Blo 1678039 1679887 := bstep (se 1 (by rfl) ⟨1259915, by rfl⟩ : syracuseStep 1679887 = 2519831) B2519831
theorem B2834959 : Blo 1678039 2834959 := bstep (se 1 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 2834959 = 4252439) B4252439
theorem B12747293 : Blo 1678039 12747293 := bstep (se 3 (by rfl) ⟨2390117, by rfl⟩ : syracuseStep 12747293 = 4780235) B4780235
theorem B5669405 : Blo 1678039 5669405 := bstep (se 3 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 5669405 = 2126027) B2126027
theorem B3777083 : Blo 1678039 3777083 := bstep (se 1 (by rfl) ⟨2832812, by rfl⟩ : syracuseStep 3777083 = 5665625) B5665625
theorem B1679931 : Blo 1678039 1679931 := bstep (se 1 (by rfl) ⟨1259948, by rfl⟩ : syracuseStep 1679931 = 2519897) B2519897
theorem B4252247 : Blo 1678039 4252247 := bstep (se 1 (by rfl) ⟨3189185, by rfl⟩ : syracuseStep 4252247 = 6378371) B6378371
theorem B1680007 : Blo 1678039 1680007 := bstep (se 1 (by rfl) ⟨1260005, by rfl⟩ : syracuseStep 1680007 = 2520011) B2520011
theorem B1680015 : Blo 1678039 1680015 := bstep (se 1 (by rfl) ⟨1260011, by rfl⟩ : syracuseStep 1680015 = 2520023) B2520023
theorem B3777209 : Blo 1678039 3777209 := bstep (se 2 (by rfl) ⟨1416453, by rfl⟩ : syracuseStep 3777209 = 2832907) B2832907
theorem B10216165 : Blo 1678039 10216165 := bstep (se 4 (by rfl) ⟨957765, by rfl⟩ : syracuseStep 10216165 = 1915531) B1915531
theorem B4252459 : Blo 1678039 4252459 := bstep (se 1 (by rfl) ⟨3189344, by rfl⟩ : syracuseStep 4252459 = 6378689) B6378689
theorem B9561017 : Blo 1678039 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B4252601 : Blo 1678039 4252601 := bstep (se 2 (by rfl) ⟨1594725, by rfl⟩ : syracuseStep 4252601 = 3189451) B3189451
theorem B4310027 : Blo 1678039 4310027 := bstep (se 1 (by rfl) ⟨3232520, by rfl⟩ : syracuseStep 4310027 = 6465041) B6465041
theorem B3777551 : Blo 1678039 3777551 := bstep (se 1 (by rfl) ⟨2833163, by rfl⟩ : syracuseStep 3777551 = 5666327) B5666327
theorem B8070167 : Blo 1678039 8070167 := bstep (se 1 (by rfl) ⟨6052625, by rfl⟩ : syracuseStep 8070167 = 12105251) B12105251
theorem B3777569 : Blo 1678039 3777569 := bstep (se 2 (by rfl) ⟨1416588, by rfl⟩ : syracuseStep 3777569 = 2833177) B2833177
theorem B8070263 : Blo 1678039 8070263 := bstep (se 1 (by rfl) ⟨6052697, by rfl⟩ : syracuseStep 8070263 = 12105395) B12105395
theorem B8504513 : Blo 1678039 8504513 := bstep (se 2 (by rfl) ⟨3189192, by rfl⟩ : syracuseStep 8504513 = 6378385) B6378385
theorem B3024143 : Blo 1678039 3024143 := bstep (se 1 (by rfl) ⟨2268107, by rfl⟩ : syracuseStep 3024143 = 4536215) B4536215
theorem B6374771 : Blo 1678039 6374771 := bstep (se 1 (by rfl) ⟨4781078, by rfl⟩ : syracuseStep 6374771 = 9562157) B9562157
theorem B3777911 : Blo 1678039 3777911 := bstep (se 1 (by rfl) ⟨2833433, by rfl⟩ : syracuseStep 3777911 = 5666867) B5666867
theorem B14337425 : Blo 1678039 14337425 := bstep (se 2 (by rfl) ⟨5376534, by rfl⟩ : syracuseStep 14337425 = 10753069) B10753069
theorem B7169465 : Blo 1678039 7169465 := bstep (se 2 (by rfl) ⟨2688549, by rfl⟩ : syracuseStep 7169465 = 5377099) B5377099
theorem B3188153 : Blo 1678039 3188153 := bstep (se 2 (by rfl) ⟨1195557, by rfl⟩ : syracuseStep 3188153 = 2391115) B2391115
theorem B3778091 : Blo 1678039 3778091 := bstep (se 1 (by rfl) ⟨2833568, by rfl⟩ : syracuseStep 3778091 = 5667137) B5667137
theorem B5105213 : Blo 1678039 5105213 := bstep (se 3 (by rfl) ⟨957227, by rfl⟩ : syracuseStep 5105213 = 1914455) B1914455
theorem B3778451 : Blo 1678039 3778451 := bstep (se 1 (by rfl) ⟨2833838, by rfl⟩ : syracuseStep 3778451 = 5667677) B5667677
theorem B3778505 : Blo 1678039 3778505 := bstep (se 2 (by rfl) ⟨1416939, by rfl⟩ : syracuseStep 3778505 = 2833879) B2833879
theorem B3024929 : Blo 1678039 3024929 := bstep (se 2 (by rfl) ⟨1134348, by rfl⟩ : syracuseStep 3024929 = 2268697) B2268697
theorem B2517065 : Blo 1678039 2517065 := bstep (se 2 (by rfl) ⟨943899, by rfl⟩ : syracuseStep 2517065 = 1887799) B1887799
theorem B41412725 : Blo 1678039 41412725 := bstep (se 5 (by rfl) ⟨1941221, by rfl⟩ : syracuseStep 41412725 = 3882443) B3882443
theorem B2123911 : Blo 1678039 2123911 := bstep (se 1 (by rfl) ⟨1592933, by rfl⟩ : syracuseStep 2123911 = 3185867) B3185867
theorem B2517179 : Blo 1678039 2517179 := bstep (se 1 (by rfl) ⟨1887884, by rfl⟩ : syracuseStep 2517179 = 3775769) B3775769
theorem B8407277 : Blo 1678039 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B2517239 : Blo 1678039 2517239 := bstep (se 1 (by rfl) ⟨1887929, by rfl⟩ : syracuseStep 2517239 = 3775859) B3775859
theorem B3107087 : Blo 1678039 3107087 := bstep (se 1 (by rfl) ⟨2330315, by rfl⟩ : syracuseStep 3107087 = 4660631) B4660631
theorem B2517263 : Blo 1678039 2517263 := bstep (se 1 (by rfl) ⟨1887947, by rfl⟩ : syracuseStep 2517263 = 3775895) B3775895
theorem B2517305 : Blo 1678039 2517305 := bstep (se 2 (by rfl) ⟨943989, by rfl⟩ : syracuseStep 2517305 = 1887979) B1887979
theorem B2017595 : Blo 1678039 2017595 := bstep (se 1 (by rfl) ⟨1513196, by rfl⟩ : syracuseStep 2017595 = 3026393) B3026393
theorem B2517383 : Blo 1678039 2517383 := bstep (se 1 (by rfl) ⟨1888037, by rfl⟩ : syracuseStep 2517383 = 3776075) B3776075
theorem B2517419 : Blo 1678039 2517419 := bstep (se 1 (by rfl) ⟨1888064, by rfl⟩ : syracuseStep 2517419 = 3776129) B3776129
theorem B8071609 : Blo 1678039 8071609 := bstep (se 2 (by rfl) ⟨3026853, by rfl⟩ : syracuseStep 8071609 = 6053707) B6053707
theorem B2517449 : Blo 1678039 2517449 := bstep (se 2 (by rfl) ⟨944043, by rfl⟩ : syracuseStep 2517449 = 1888087) B1888087
theorem B7662109 : Blo 1678039 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B2517563 : Blo 1678039 2517563 := bstep (se 1 (by rfl) ⟨1888172, by rfl⟩ : syracuseStep 2517563 = 3776345) B3776345
theorem B2689595 : Blo 1678039 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B5106235 : Blo 1678039 5106235 := bstep (se 1 (by rfl) ⟨3829676, by rfl⟩ : syracuseStep 5106235 = 7659353) B7659353
theorem B3189307 : Blo 1678039 3189307 := bstep (se 1 (by rfl) ⟨2391980, by rfl⟩ : syracuseStep 3189307 = 4783961) B4783961
theorem B20425283 : Blo 1678039 20425283 := bstep (se 1 (by rfl) ⟨15318962, by rfl⟩ : syracuseStep 20425283 = 30637925) B30637925
theorem B8620631 : Blo 1678039 8620631 := bstep (se 1 (by rfl) ⟨6465473, by rfl⟩ : syracuseStep 8620631 = 12930947) B12930947
theorem B2517623 : Blo 1678039 2517623 := bstep (se 1 (by rfl) ⟨1888217, by rfl⟩ : syracuseStep 2517623 = 3776435) B3776435
theorem B2124407 : Blo 1678039 2124407 := bstep (se 1 (by rfl) ⟨1593305, by rfl⟩ : syracuseStep 2124407 = 3186611) B3186611
theorem B3779207 : Blo 1678039 3779207 := bstep (se 1 (by rfl) ⟨2834405, by rfl⟩ : syracuseStep 3779207 = 5668811) B5668811
theorem B2517647 : Blo 1678039 2517647 := bstep (se 1 (by rfl) ⟨1888235, by rfl⟩ : syracuseStep 2517647 = 3776471) B3776471
theorem B2517689 : Blo 1678039 2517689 := bstep (se 2 (by rfl) ⟨944133, by rfl⟩ : syracuseStep 2517689 = 1888267) B1888267
theorem B2517767 : Blo 1678039 2517767 := bstep (se 1 (by rfl) ⟨1888325, by rfl⟩ : syracuseStep 2517767 = 3776651) B3776651
theorem B2124559 : Blo 1678039 2124559 := bstep (se 1 (by rfl) ⟨1593419, by rfl⟩ : syracuseStep 2124559 = 3186839) B3186839
theorem B8514337 : Blo 1678039 8514337 := bstep (se 2 (by rfl) ⟨3192876, by rfl⟩ : syracuseStep 8514337 = 6385753) B6385753
theorem B2517803 : Blo 1678039 2517803 := bstep (se 1 (by rfl) ⟨1888352, by rfl⟩ : syracuseStep 2517803 = 3776705) B3776705
theorem B9562931 : Blo 1678039 9562931 := bstep (se 1 (by rfl) ⟨7172198, by rfl⟩ : syracuseStep 9562931 = 14344397) B14344397
theorem B8063803 : Blo 1678039 8063803 := bstep (se 1 (by rfl) ⟨6047852, by rfl⟩ : syracuseStep 8063803 = 12095705) B12095705
theorem B3779387 : Blo 1678039 3779387 := bstep (se 1 (by rfl) ⟨2834540, by rfl⟩ : syracuseStep 3779387 = 5669081) B5669081
theorem B2517833 : Blo 1678039 2517833 := bstep (se 2 (by rfl) ⟨944187, by rfl⟩ : syracuseStep 2517833 = 1888375) B1888375
theorem B8063879 : Blo 1678039 8063879 := bstep (se 1 (by rfl) ⟨6047909, by rfl⟩ : syracuseStep 8063879 = 12095819) B12095819
theorem B4844441 : Blo 1678039 4844441 := bstep (se 2 (by rfl) ⟨1816665, by rfl⟩ : syracuseStep 4844441 = 3633331) B3633331
theorem B3779513 : Blo 1678039 3779513 := bstep (se 2 (by rfl) ⟨1417317, by rfl⟩ : syracuseStep 3779513 = 2834635) B2834635
theorem B2517947 : Blo 1678039 2517947 := bstep (se 1 (by rfl) ⟨1888460, by rfl⟩ : syracuseStep 2517947 = 3776921) B3776921
theorem B2124731 : Blo 1678039 2124731 := bstep (se 1 (by rfl) ⟨1593548, by rfl⟩ : syracuseStep 2124731 = 3187097) B3187097
theorem B2518007 : Blo 1678039 2518007 := bstep (se 1 (by rfl) ⟨1888505, by rfl⟩ : syracuseStep 2518007 = 3777011) B3777011
theorem B4033547 : Blo 1678039 4033547 := bstep (se 1 (by rfl) ⟨3025160, by rfl⟩ : syracuseStep 4033547 = 6050321) B6050321
theorem B2518031 : Blo 1678039 2518031 := bstep (se 1 (by rfl) ⟨1888523, by rfl⟩ : syracuseStep 2518031 = 3777047) B3777047
theorem B2518073 : Blo 1678039 2518073 := bstep (se 2 (by rfl) ⟨944277, by rfl⟩ : syracuseStep 2518073 = 1888555) B1888555
theorem B2518151 : Blo 1678039 2518151 := bstep (se 1 (by rfl) ⟨1888613, by rfl⟩ : syracuseStep 2518151 = 3777227) B3777227
theorem B2518187 : Blo 1678039 2518187 := bstep (se 1 (by rfl) ⟨1888640, by rfl⟩ : syracuseStep 2518187 = 3777281) B3777281
theorem B2518217 : Blo 1678039 2518217 := bstep (se 2 (by rfl) ⟨944331, by rfl⟩ : syracuseStep 2518217 = 1888663) B1888663
theorem B3230921 : Blo 1678039 3230921 := bstep (se 2 (by rfl) ⟨1211595, by rfl⟩ : syracuseStep 3230921 = 2423191) B2423191
theorem B3779855 : Blo 1678039 3779855 := bstep (se 1 (by rfl) ⟨2834891, by rfl⟩ : syracuseStep 3779855 = 5669783) B5669783
theorem B3779873 : Blo 1678039 3779873 := bstep (se 2 (by rfl) ⟨1417452, by rfl⟩ : syracuseStep 3779873 = 2834905) B2834905
theorem B5664059 : Blo 1678039 5664059 := bstep (se 1 (by rfl) ⟨4248044, by rfl⟩ : syracuseStep 5664059 = 8496089) B8496089
theorem B2518331 : Blo 1678039 2518331 := bstep (se 1 (by rfl) ⟨1888748, by rfl⟩ : syracuseStep 2518331 = 3777497) B3777497
theorem B2518391 : Blo 1678039 2518391 := bstep (se 1 (by rfl) ⟨1888793, by rfl⟩ : syracuseStep 2518391 = 3777587) B3777587
theorem B20417923 : Blo 1678039 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B2518415 : Blo 1678039 2518415 := bstep (se 1 (by rfl) ⟨1888811, by rfl⟩ : syracuseStep 2518415 = 3777623) B3777623
theorem B2518457 : Blo 1678039 2518457 := bstep (se 2 (by rfl) ⟨944421, by rfl⟩ : syracuseStep 2518457 = 1888843) B1888843
theorem B8613323 : Blo 1678039 8613323 := bstep (se 1 (by rfl) ⟨6459992, by rfl⟩ : syracuseStep 8613323 = 12919985) B12919985
theorem B6376913 : Blo 1678039 6376913 := bstep (se 2 (by rfl) ⟨2391342, by rfl⟩ : syracuseStep 6376913 = 4782685) B4782685
theorem B2518535 : Blo 1678039 2518535 := bstep (se 1 (by rfl) ⟨1888901, by rfl⟩ : syracuseStep 2518535 = 3777803) B3777803
theorem B2518571 : Blo 1678039 2518571 := bstep (se 1 (by rfl) ⟨1888928, by rfl⟩ : syracuseStep 2518571 = 3777857) B3777857
theorem B2518601 : Blo 1678039 2518601 := bstep (se 2 (by rfl) ⟨944475, by rfl⟩ : syracuseStep 2518601 = 1888951) B1888951
theorem B27233891 : Blo 1678039 27233891 := bstep (se 1 (by rfl) ⟨20425418, by rfl⟩ : syracuseStep 27233891 = 40850837) B40850837
theorem B2518715 : Blo 1678039 2518715 := bstep (se 1 (by rfl) ⟨1889036, by rfl⟩ : syracuseStep 2518715 = 3778073) B3778073
theorem B18149093 : Blo 1678039 18149093 := bstep (se 4 (by rfl) ⟨1701477, by rfl⟩ : syracuseStep 18149093 = 3402955) B3402955
theorem B2518775 : Blo 1678039 2518775 := bstep (se 1 (by rfl) ⟨1889081, by rfl⟩ : syracuseStep 2518775 = 3778163) B3778163
theorem B7171841 : Blo 1678039 7171841 := bstep (se 2 (by rfl) ⟨2689440, by rfl⟩ : syracuseStep 7171841 = 5378881) B5378881
theorem B1888015 : Blo 1678039 1888015 := bstep (se 1 (by rfl) ⟨1416011, by rfl⟩ : syracuseStep 1888015 = 2832023) B2832023
theorem B2518799 : Blo 1678039 2518799 := bstep (se 1 (by rfl) ⟨1889099, by rfl⟩ : syracuseStep 2518799 = 3778199) B3778199
theorem B6377231 : Blo 1678039 6377231 := bstep (se 1 (by rfl) ⟨4782923, by rfl⟩ : syracuseStep 6377231 = 9565847) B9565847
theorem B5664545 : Blo 1678039 5664545 := bstep (se 2 (by rfl) ⟨2124204, by rfl⟩ : syracuseStep 5664545 = 4248409) B4248409
theorem B5451553 : Blo 1678039 5451553 := bstep (se 2 (by rfl) ⟨2044332, by rfl⟩ : syracuseStep 5451553 = 4088665) B4088665
theorem B2518841 : Blo 1678039 2518841 := bstep (se 2 (by rfl) ⟨944565, by rfl⟩ : syracuseStep 2518841 = 1889131) B1889131
theorem B2518919 : Blo 1678039 2518919 := bstep (se 1 (by rfl) ⟨1889189, by rfl⟩ : syracuseStep 2518919 = 3778379) B3778379
theorem B2125703 : Blo 1678039 2125703 := bstep (se 1 (by rfl) ⟨1594277, by rfl⟩ : syracuseStep 2125703 = 3188555) B3188555
theorem B7171993 : Blo 1678039 7171993 := bstep (se 2 (by rfl) ⟨2689497, by rfl⟩ : syracuseStep 7171993 = 5378995) B5378995
theorem B2518955 : Blo 1678039 2518955 := bstep (se 1 (by rfl) ⟨1889216, by rfl⟩ : syracuseStep 2518955 = 3778433) B3778433
theorem B2518985 : Blo 1678039 2518985 := bstep (se 2 (by rfl) ⟨944619, by rfl⟩ : syracuseStep 2518985 = 1889239) B1889239
theorem B4780043 : Blo 1678039 4780043 := bstep (se 1 (by rfl) ⟨3585032, by rfl⟩ : syracuseStep 4780043 = 7170065) B7170065
theorem B3584015 : Blo 1678039 3584015 := bstep (se 1 (by rfl) ⟨2688011, by rfl⟩ : syracuseStep 3584015 = 5376023) B5376023
theorem B2519099 : Blo 1678039 2519099 := bstep (se 1 (by rfl) ⟨1889324, by rfl⟩ : syracuseStep 2519099 = 3778649) B3778649
theorem B2519159 : Blo 1678039 2519159 := bstep (se 1 (by rfl) ⟨1889369, by rfl⟩ : syracuseStep 2519159 = 3778739) B3778739
theorem B2519183 : Blo 1678039 2519183 := bstep (se 1 (by rfl) ⟨1889387, by rfl⟩ : syracuseStep 2519183 = 3778775) B3778775
theorem B2519225 : Blo 1678039 2519225 := bstep (se 2 (by rfl) ⟨944709, by rfl⟩ : syracuseStep 2519225 = 1889419) B1889419
theorem B24875209 : Blo 1678039 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B9564389 : Blo 1678039 9564389 := bstep (se 4 (by rfl) ⟨896661, by rfl⟩ : syracuseStep 9564389 = 1793323) B1793323
theorem B10907885 : Blo 1678039 10907885 := bstep (se 3 (by rfl) ⟨2045228, by rfl⟩ : syracuseStep 10907885 = 4090457) B4090457
theorem B1888519 : Blo 1678039 1888519 := bstep (se 1 (by rfl) ⟨1416389, by rfl⟩ : syracuseStep 1888519 = 2832779) B2832779
theorem B2519303 : Blo 1678039 2519303 := bstep (se 1 (by rfl) ⟨1889477, by rfl⟩ : syracuseStep 2519303 = 3778955) B3778955
theorem B2519339 : Blo 1678039 2519339 := bstep (se 1 (by rfl) ⟨1889504, by rfl⟩ : syracuseStep 2519339 = 3779009) B3779009
theorem B2519369 : Blo 1678039 2519369 := bstep (se 2 (by rfl) ⟨944763, by rfl⟩ : syracuseStep 2519369 = 1889527) B1889527
theorem B4247923 : Blo 1678039 4247923 := bstep (se 1 (by rfl) ⟨3185942, by rfl⟩ : syracuseStep 4247923 = 6371885) B6371885
theorem B5665139 : Blo 1678039 5665139 := bstep (se 1 (by rfl) ⟨4248854, by rfl⟩ : syracuseStep 5665139 = 8497709) B8497709
theorem B28684691 : Blo 1678039 28684691 := bstep (se 1 (by rfl) ⟨21513518, by rfl⟩ : syracuseStep 28684691 = 43027037) B43027037
theorem B10760633 : Blo 1678039 10760633 := bstep (se 2 (by rfl) ⟨4035237, by rfl⟩ : syracuseStep 10760633 = 8070475) B8070475
theorem B1888699 : Blo 1678039 1888699 := bstep (se 1 (by rfl) ⟨1416524, by rfl⟩ : syracuseStep 1888699 = 2833049) B2833049
theorem B2519483 : Blo 1678039 2519483 := bstep (se 1 (by rfl) ⟨1889612, by rfl⟩ : syracuseStep 2519483 = 3779225) B3779225
theorem B2519543 : Blo 1678039 2519543 := bstep (se 1 (by rfl) ⟨1889657, by rfl⟩ : syracuseStep 2519543 = 3779315) B3779315
theorem B4248065 : Blo 1678039 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B2519567 : Blo 1678039 2519567 := bstep (se 1 (by rfl) ⟨1889675, by rfl⟩ : syracuseStep 2519567 = 3779351) B3779351
theorem B2519609 : Blo 1678039 2519609 := bstep (se 2 (by rfl) ⟨944853, by rfl⟩ : syracuseStep 2519609 = 1889707) B1889707
theorem B2519687 : Blo 1678039 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B4780691 : Blo 1678039 4780691 := bstep (se 1 (by rfl) ⟨3585518, by rfl⟩ : syracuseStep 4780691 = 7171037) B7171037
theorem B2519723 : Blo 1678039 2519723 := bstep (se 1 (by rfl) ⟨1889792, by rfl⟩ : syracuseStep 2519723 = 3779585) B3779585
theorem B9695945 : Blo 1678039 9695945 := bstep (se 2 (by rfl) ⟨3635979, by rfl⟩ : syracuseStep 9695945 = 7271959) B7271959
theorem B2519753 : Blo 1678039 2519753 := bstep (se 2 (by rfl) ⟨944907, by rfl⟩ : syracuseStep 2519753 = 1889815) B1889815
theorem B12751667 : Blo 1678039 12751667 := bstep (se 1 (by rfl) ⟨9563750, by rfl⟩ : syracuseStep 12751667 = 19127501) B19127501
theorem B3584827 : Blo 1678039 3584827 := bstep (se 1 (by rfl) ⟨2688620, by rfl⟩ : syracuseStep 3584827 = 5377241) B5377241
theorem B2519867 : Blo 1678039 2519867 := bstep (se 1 (by rfl) ⟨1889900, by rfl⟩ : syracuseStep 2519867 = 3779801) B3779801
theorem B4780919 : Blo 1678039 4780919 := bstep (se 1 (by rfl) ⟨3585689, by rfl⟩ : syracuseStep 4780919 = 7171379) B7171379
theorem B2519927 : Blo 1678039 2519927 := bstep (se 1 (by rfl) ⟨1889945, by rfl⟩ : syracuseStep 2519927 = 3779891) B3779891
theorem B3584903 : Blo 1678039 3584903 := bstep (se 1 (by rfl) ⟨2688677, by rfl⟩ : syracuseStep 3584903 = 5377355) B5377355
theorem B1913743 : Blo 1678039 1913743 := bstep (se 1 (by rfl) ⟨1435307, by rfl⟩ : syracuseStep 1913743 = 2870615) B2870615
theorem B1889167 : Blo 1678039 1889167 := bstep (se 1 (by rfl) ⟨1416875, by rfl⟩ : syracuseStep 1889167 = 2833751) B2833751
theorem B9565073 : Blo 1678039 9565073 := bstep (se 2 (by rfl) ⟨3586902, by rfl⟩ : syracuseStep 9565073 = 7173805) B7173805
theorem B2519951 : Blo 1678039 2519951 := bstep (se 1 (by rfl) ⟨1889963, by rfl⟩ : syracuseStep 2519951 = 3779927) B3779927
theorem B2519993 : Blo 1678039 2519993 := bstep (se 2 (by rfl) ⟨944997, by rfl⟩ : syracuseStep 2519993 = 1889995) B1889995
theorem B4248521 : Blo 1678039 4248521 := bstep (se 2 (by rfl) ⟨1593195, by rfl⟩ : syracuseStep 4248521 = 3186391) B3186391
theorem B3830843 : Blo 1678039 3830843 := bstep (se 1 (by rfl) ⟨2873132, by rfl⟩ : syracuseStep 3830843 = 5746265) B5746265
theorem B3585143 : Blo 1678039 3585143 := bstep (se 1 (by rfl) ⟨2688857, by rfl⟩ : syracuseStep 3585143 = 5377715) B5377715
theorem B2045191 : Blo 1678039 2045191 := bstep (se 1 (by rfl) ⟨1533893, by rfl⟩ : syracuseStep 2045191 = 3067787) B3067787
theorem B3585313 : Blo 1678039 3585313 := bstep (se 2 (by rfl) ⟨1344492, by rfl⟩ : syracuseStep 3585313 = 2688985) B2688985
theorem B4248875 : Blo 1678039 4248875 := bstep (se 1 (by rfl) ⟨3186656, by rfl⟩ : syracuseStep 4248875 = 6373313) B6373313
theorem B1889671 : Blo 1678039 1889671 := bstep (se 1 (by rfl) ⟨1417253, by rfl⟩ : syracuseStep 1889671 = 2834507) B2834507
theorem B8500625 : Blo 1678039 8500625 := bstep (se 2 (by rfl) ⟨3187734, by rfl⟩ : syracuseStep 8500625 = 6375469) B6375469
theorem B16127531 : Blo 1678039 16127531 := bstep (se 1 (by rfl) ⟨12095648, by rfl⟩ : syracuseStep 16127531 = 24191297) B24191297
theorem B2831915 : Blo 1678039 2831915 := bstep (se 1 (by rfl) ⟨2123936, by rfl⟩ : syracuseStep 2831915 = 4247873) B4247873
theorem B2299435 : Blo 1678039 2299435 := bstep (se 1 (by rfl) ⟨1724576, by rfl⟩ : syracuseStep 2299435 = 3449153) B3449153
theorem B1889851 : Blo 1678039 1889851 := bstep (se 1 (by rfl) ⟨1417388, by rfl⟩ : syracuseStep 1889851 = 2834777) B2834777
theorem B3585655 : Blo 1678039 3585655 := bstep (se 1 (by rfl) ⟨2689241, by rfl⟩ : syracuseStep 3585655 = 5378483) B5378483
theorem B2873017 : Blo 1678039 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B4536107 : Blo 1678039 4536107 := bstep (se 1 (by rfl) ⟨3402080, by rfl⟩ : syracuseStep 4536107 = 6804161) B6804161
theorem B15324977 : Blo 1678039 15324977 := bstep (se 2 (by rfl) ⟨5746866, by rfl⟩ : syracuseStep 15324977 = 11493733) B11493733
theorem B39302981 : Blo 1678039 39302981 := bstep (se 4 (by rfl) ⟨3684654, by rfl⟩ : syracuseStep 39302981 = 7369309) B7369309
theorem B9566099 : Blo 1678039 9566099 := bstep (se 1 (by rfl) ⟨7174574, by rfl⟩ : syracuseStep 9566099 = 14349149) B14349149
theorem B2832313 : Blo 1678039 2832313 := bstep (se 2 (by rfl) ⟨1062117, by rfl⟩ : syracuseStep 2832313 = 2124235) B2124235
theorem B34453451 : Blo 1678039 34453451 := bstep (se 1 (by rfl) ⟨25840088, by rfl⟩ : syracuseStep 34453451 = 51680177) B51680177
theorem B4249867 : Blo 1678039 4249867 := bstep (se 1 (by rfl) ⟨3187400, by rfl⟩ : syracuseStep 4249867 = 6374801) B6374801
theorem B1792315 : Blo 1678039 1792315 := bstep (se 1 (by rfl) ⟨1344236, by rfl⟩ : syracuseStep 1792315 = 2688473) B2688473
theorem B11483527 : Blo 1678039 11483527 := bstep (se 1 (by rfl) ⟨8612645, by rfl⟩ : syracuseStep 11483527 = 17225291) B17225291
theorem B24205715 : Blo 1678039 24205715 := bstep (se 1 (by rfl) ⟨18154286, by rfl⟩ : syracuseStep 24205715 = 36308573) B36308573
theorem B4250009 : Blo 1678039 4250009 := bstep (se 2 (by rfl) ⟨1593753, by rfl⟩ : syracuseStep 4250009 = 3187507) B3187507
theorem B6461963 : Blo 1678039 6461963 := bstep (se 1 (by rfl) ⟨4846472, by rfl⟩ : syracuseStep 6461963 = 9692945) B9692945
theorem B9558557 : Blo 1678039 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B4250171 : Blo 1678039 4250171 := bstep (se 1 (by rfl) ⟨3187628, by rfl⟩ : syracuseStep 4250171 = 6375257) B6375257
theorem B2833015 : Blo 1678039 2833015 := bstep (se 1 (by rfl) ⟨2124761, by rfl⟩ : syracuseStep 2833015 = 4249523) B4249523
theorem B1678087 : Blo 1678039 1678087 := bstep (se 1 (by rfl) ⟨1258565, by rfl⟩ : syracuseStep 1678087 = 2517131) B2517131
theorem B1678095 : Blo 1678039 1678095 := bstep (se 1 (by rfl) ⟨1258571, by rfl⟩ : syracuseStep 1678095 = 2517143) B2517143
theorem B65461007 : Blo 1678039 65461007 := bstep (se 1 (by rfl) ⟨49095755, by rfl⟩ : syracuseStep 65461007 = 98191511) B98191511
theorem B1678139 : Blo 1678039 1678139 := bstep (se 1 (by rfl) ⟨1258604, by rfl⟩ : syracuseStep 1678139 = 2517209) B2517209
theorem B2833211 : Blo 1678039 2833211 := bstep (se 1 (by rfl) ⟨2124908, by rfl⟩ : syracuseStep 2833211 = 4249817) B4249817
theorem B1678215 : Blo 1678039 1678215 := bstep (se 1 (by rfl) ⟨1258661, by rfl⟩ : syracuseStep 1678215 = 2517323) B2517323
theorem B1678223 : Blo 1678039 1678223 := bstep (se 1 (by rfl) ⟨1258667, by rfl⟩ : syracuseStep 1678223 = 2517335) B2517335
theorem B4250515 : Blo 1678039 4250515 := bstep (se 1 (by rfl) ⟨3187886, by rfl⟩ : syracuseStep 4250515 = 6375773) B6375773
theorem B5667731 : Blo 1678039 5667731 := bstep (se 1 (by rfl) ⟨4250798, by rfl⟩ : syracuseStep 5667731 = 8501597) B8501597
theorem B17234851 : Blo 1678039 17234851 := bstep (se 1 (by rfl) ⟨12926138, by rfl⟩ : syracuseStep 17234851 = 25852277) B25852277
theorem B1678267 : Blo 1678039 1678267 := bstep (se 1 (by rfl) ⟨1258700, by rfl⟩ : syracuseStep 1678267 = 2517401) B2517401
theorem B1678343 : Blo 1678039 1678343 := bstep (se 1 (by rfl) ⟨1258757, by rfl⟩ : syracuseStep 1678343 = 2517515) B2517515
theorem B1678351 : Blo 1678039 1678351 := bstep (se 1 (by rfl) ⟨1258763, by rfl⟩ : syracuseStep 1678351 = 2517527) B2517527
theorem B4250657 : Blo 1678039 4250657 := bstep (se 2 (by rfl) ⟨1593996, by rfl⟩ : syracuseStep 4250657 = 3187993) B3187993
theorem B3185723 : Blo 1678039 3185723 := bstep (se 1 (by rfl) ⟨2389292, by rfl⟩ : syracuseStep 3185723 = 4778585) B4778585
theorem B1678395 : Blo 1678039 1678395 := bstep (se 1 (by rfl) ⟨1258796, by rfl⟩ : syracuseStep 1678395 = 2517593) B2517593
theorem B3775607 : Blo 1678039 3775607 := bstep (se 1 (by rfl) ⟨2831705, by rfl⟩ : syracuseStep 3775607 = 5663411) B5663411
theorem B1678471 : Blo 1678039 1678471 := bstep (se 1 (by rfl) ⟨1258853, by rfl⟩ : syracuseStep 1678471 = 2517707) B2517707
theorem B1678479 : Blo 1678039 1678479 := bstep (se 1 (by rfl) ⟨1258859, by rfl⟩ : syracuseStep 1678479 = 2517719) B2517719
theorem B2391211 : Blo 1678039 2391211 := bstep (se 1 (by rfl) ⟨1793408, by rfl⟩ : syracuseStep 2391211 = 3586817) B3586817
theorem B1678523 : Blo 1678039 1678523 := bstep (se 1 (by rfl) ⟨1258892, by rfl⟩ : syracuseStep 1678523 = 2517785) B2517785
theorem B6372553 : Blo 1678039 6372553 := bstep (se 2 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 6372553 = 4779415) B4779415
theorem B9559241 : Blo 1678039 9559241 := bstep (se 2 (by rfl) ⟨3584715, by rfl⟩ : syracuseStep 9559241 = 7169431) B7169431
theorem B2833609 : Blo 1678039 2833609 := bstep (se 2 (by rfl) ⟨1062603, by rfl⟩ : syracuseStep 2833609 = 2125207) B2125207
theorem B1678599 : Blo 1678039 1678599 := bstep (se 1 (by rfl) ⟨1258949, by rfl⟩ : syracuseStep 1678599 = 2517899) B2517899
theorem B1678607 : Blo 1678039 1678607 := bstep (se 1 (by rfl) ⟨1258955, by rfl⟩ : syracuseStep 1678607 = 2517911) B2517911
theorem B32275745 : Blo 1678039 32275745 := bstep (se 2 (by rfl) ⟨12103404, by rfl⟩ : syracuseStep 32275745 = 24206809) B24206809
theorem B3775787 : Blo 1678039 3775787 := bstep (se 1 (by rfl) ⟨2831840, by rfl⟩ : syracuseStep 3775787 = 5663681) B5663681
theorem B1678651 : Blo 1678039 1678651 := bstep (se 1 (by rfl) ⟨1258988, by rfl⟩ : syracuseStep 1678651 = 2517977) B2517977
theorem B1678727 : Blo 1678039 1678727 := bstep (se 1 (by rfl) ⟨1259045, by rfl⟩ : syracuseStep 1678727 = 2518091) B2518091
theorem B1678735 : Blo 1678039 1678735 := bstep (se 1 (by rfl) ⟨1259051, by rfl⟩ : syracuseStep 1678735 = 2518103) B2518103
theorem B2391439 : Blo 1678039 2391439 := bstep (se 1 (by rfl) ⟨1793579, by rfl⟩ : syracuseStep 2391439 = 3587159) B3587159
theorem B1678779 : Blo 1678039 1678779 := bstep (se 1 (by rfl) ⟨1259084, by rfl⟩ : syracuseStep 1678779 = 2518169) B2518169
theorem B9076171 : Blo 1678039 9076171 := bstep (se 1 (by rfl) ⟨6807128, by rfl⟩ : syracuseStep 9076171 = 13614257) B13614257
theorem B8502731 : Blo 1678039 8502731 := bstep (se 1 (by rfl) ⟨6377048, by rfl⟩ : syracuseStep 8502731 = 12754097) B12754097
theorem B1678855 : Blo 1678039 1678855 := bstep (se 1 (by rfl) ⟨1259141, by rfl⟩ : syracuseStep 1678855 = 2518283) B2518283
theorem B1678863 : Blo 1678039 1678863 := bstep (se 1 (by rfl) ⟨1259147, by rfl⟩ : syracuseStep 1678863 = 2518295) B2518295
theorem B3186209 : Blo 1678039 3186209 := bstep (se 2 (by rfl) ⟨1194828, by rfl⟩ : syracuseStep 3186209 = 2389657) B2389657
theorem B1678907 : Blo 1678039 1678907 := bstep (se 1 (by rfl) ⟨1259180, by rfl⟩ : syracuseStep 1678907 = 2518361) B2518361
theorem B1678983 : Blo 1678039 1678983 := bstep (se 1 (by rfl) ⟨1259237, by rfl⟩ : syracuseStep 1678983 = 2518475) B2518475
theorem B1678991 : Blo 1678039 1678991 := bstep (se 1 (by rfl) ⟨1259243, by rfl⟩ : syracuseStep 1678991 = 2518487) B2518487
theorem B3776147 : Blo 1678039 3776147 := bstep (se 1 (by rfl) ⟨2832110, by rfl⟩ : syracuseStep 3776147 = 5664221) B5664221
theorem B1679035 : Blo 1678039 1679035 := bstep (se 1 (by rfl) ⟨1259276, by rfl⟩ : syracuseStep 1679035 = 2518553) B2518553
theorem B3776201 : Blo 1678039 3776201 := bstep (se 2 (by rfl) ⟨1416075, by rfl⟩ : syracuseStep 3776201 = 2832151) B2832151
theorem B1679111 : Blo 1678039 1679111 := bstep (se 1 (by rfl) ⟨1259333, by rfl⟩ : syracuseStep 1679111 = 2518667) B2518667
theorem B2391815 : Blo 1678039 2391815 := bstep (se 1 (by rfl) ⟨1793861, by rfl⟩ : syracuseStep 2391815 = 3587723) B3587723
theorem B1679119 : Blo 1678039 1679119 := bstep (se 1 (by rfl) ⟨1259339, by rfl⟩ : syracuseStep 1679119 = 2518679) B2518679
theorem B8503055 : Blo 1678039 8503055 := bstep (se 1 (by rfl) ⟨6377291, by rfl⟩ : syracuseStep 8503055 = 12754583) B12754583
theorem B16146211 : Blo 1678039 16146211 := bstep (se 1 (by rfl) ⟨12109658, by rfl⟩ : syracuseStep 16146211 = 24219317) B24219317
theorem B1679163 : Blo 1678039 1679163 := bstep (se 1 (by rfl) ⟨1259372, by rfl⟩ : syracuseStep 1679163 = 2518745) B2518745
theorem B1679239 : Blo 1678039 1679239 := bstep (se 1 (by rfl) ⟨1259429, by rfl⟩ : syracuseStep 1679239 = 2518859) B2518859
theorem B2834311 : Blo 1678039 2834311 := bstep (se 1 (by rfl) ⟨2125733, by rfl⟩ : syracuseStep 2834311 = 4251467) B4251467
theorem B1679247 : Blo 1678039 1679247 := bstep (se 1 (by rfl) ⟨1259435, by rfl⟩ : syracuseStep 1679247 = 2518871) B2518871
theorem B1679291 : Blo 1678039 1679291 := bstep (se 1 (by rfl) ⟨1259468, by rfl⟩ : syracuseStep 1679291 = 2518937) B2518937
theorem B5668865 : Blo 1678039 5668865 := bstep (se 2 (by rfl) ⟨2125824, by rfl⟩ : syracuseStep 5668865 = 4251649) B4251649
theorem B3186695 : Blo 1678039 3186695 := bstep (se 1 (by rfl) ⟨2390021, by rfl⟩ : syracuseStep 3186695 = 4780043) B4780043
theorem B19382287 : Blo 1678039 19382287 := bstep (se 1 (by rfl) ⟨14536715, by rfl⟩ : syracuseStep 19382287 = 29073431) B29073431
theorem B1679399 : Blo 1678039 1679399 := bstep (se 1 (by rfl) ⟨1259549, by rfl⟩ : syracuseStep 1679399 = 2519099) B2519099
theorem B14352461 : Blo 1678039 14352461 := bstep (se 3 (by rfl) ⟨2691086, by rfl⟩ : syracuseStep 14352461 = 5382173) B5382173
theorem B1679439 : Blo 1678039 1679439 := bstep (se 1 (by rfl) ⟨1259579, by rfl⟩ : syracuseStep 1679439 = 2519159) B2519159
theorem B1679455 : Blo 1678039 1679455 := bstep (se 1 (by rfl) ⟨1259591, by rfl⟩ : syracuseStep 1679455 = 2519183) B2519183
theorem B1679483 : Blo 1678039 1679483 := bstep (se 1 (by rfl) ⟨1259612, by rfl⟩ : syracuseStep 1679483 = 2519225) B2519225
theorem B1679535 : Blo 1678039 1679535 := bstep (se 1 (by rfl) ⟨1259651, by rfl⟩ : syracuseStep 1679535 = 2519303) B2519303
theorem B1679559 : Blo 1678039 1679559 := bstep (se 1 (by rfl) ⟨1259669, by rfl⟩ : syracuseStep 1679559 = 2519339) B2519339
theorem B1679579 : Blo 1678039 1679579 := bstep (se 1 (by rfl) ⟨1259684, by rfl⟩ : syracuseStep 1679579 = 2519369) B2519369
theorem B12263653 : Blo 1678039 12263653 := bstep (se 4 (by rfl) ⟨1149717, by rfl⟩ : syracuseStep 12263653 = 2299435) B2299435
theorem B3776759 : Blo 1678039 3776759 := bstep (se 1 (by rfl) ⟨2832569, by rfl⟩ : syracuseStep 3776759 = 5665139) B5665139
theorem B1679655 : Blo 1678039 1679655 := bstep (se 1 (by rfl) ⟨1259741, by rfl⟩ : syracuseStep 1679655 = 2519483) B2519483
theorem B1679695 : Blo 1678039 1679695 := bstep (se 1 (by rfl) ⟨1259771, by rfl⟩ : syracuseStep 1679695 = 2519543) B2519543
theorem B1679711 : Blo 1678039 1679711 := bstep (se 1 (by rfl) ⟨1259783, by rfl⟩ : syracuseStep 1679711 = 2519567) B2519567
theorem B1679739 : Blo 1678039 1679739 := bstep (se 1 (by rfl) ⟨1259804, by rfl⟩ : syracuseStep 1679739 = 2519609) B2519609
theorem B2834831 : Blo 1678039 2834831 := bstep (se 1 (by rfl) ⟨2126123, by rfl⟩ : syracuseStep 2834831 = 4252247) B4252247
theorem B1679791 : Blo 1678039 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B3187127 : Blo 1678039 3187127 := bstep (se 1 (by rfl) ⟨2390345, by rfl⟩ : syracuseStep 3187127 = 4780691) B4780691
theorem B1679815 : Blo 1678039 1679815 := bstep (se 1 (by rfl) ⟨1259861, by rfl⟩ : syracuseStep 1679815 = 2519723) B2519723
theorem B6463963 : Blo 1678039 6463963 := bstep (se 1 (by rfl) ⟨4847972, by rfl⟩ : syracuseStep 6463963 = 9695945) B9695945
theorem B1679835 : Blo 1678039 1679835 := bstep (se 1 (by rfl) ⟨1259876, by rfl⟩ : syracuseStep 1679835 = 2519753) B2519753
theorem B15311369 : Blo 1678039 15311369 := bstep (se 2 (by rfl) ⟨5741763, by rfl⟩ : syracuseStep 15311369 = 11483527) B11483527
theorem B1679911 : Blo 1678039 1679911 := bstep (se 1 (by rfl) ⟨1259933, by rfl⟩ : syracuseStep 1679911 = 2519867) B2519867
theorem B3187279 : Blo 1678039 3187279 := bstep (se 1 (by rfl) ⟨2390459, by rfl⟩ : syracuseStep 3187279 = 4780919) B4780919
theorem B1679951 : Blo 1678039 1679951 := bstep (se 1 (by rfl) ⟨1259963, by rfl⟩ : syracuseStep 1679951 = 2519927) B2519927
theorem B1679967 : Blo 1678039 1679967 := bstep (se 1 (by rfl) ⟨1259975, by rfl⟩ : syracuseStep 1679967 = 2519951) B2519951
theorem B6374011 : Blo 1678039 6374011 := bstep (se 1 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 6374011 = 9561017) B9561017
theorem B1679995 : Blo 1678039 1679995 := bstep (se 1 (by rfl) ⟨1259996, by rfl⟩ : syracuseStep 1679995 = 2519993) B2519993
theorem B2835067 : Blo 1678039 2835067 := bstep (se 1 (by rfl) ⟨2126300, by rfl⟩ : syracuseStep 2835067 = 4252601) B4252601
theorem B10216145 : Blo 1678039 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B6808313 : Blo 1678039 6808313 := bstep (se 2 (by rfl) ⟨2553117, by rfl⟩ : syracuseStep 6808313 = 5106235) B5106235
theorem B4252409 : Blo 1678039 4252409 := bstep (se 2 (by rfl) ⟨1594653, by rfl⟩ : syracuseStep 4252409 = 3189307) B3189307
theorem B5669675 : Blo 1678039 5669675 := bstep (se 1 (by rfl) ⟨4252256, by rfl⟩ : syracuseStep 5669675 = 8504513) B8504513
theorem B3777353 : Blo 1678039 3777353 := bstep (se 2 (by rfl) ⟨1416507, by rfl⟩ : syracuseStep 3777353 = 2833015) B2833015
theorem B2016095 : Blo 1678039 2016095 := bstep (se 1 (by rfl) ⟨1512071, by rfl⟩ : syracuseStep 2016095 = 3024143) B3024143
theorem B5669945 : Blo 1678039 5669945 := bstep (se 2 (by rfl) ⟨2126229, by rfl⟩ : syracuseStep 5669945 = 4252459) B4252459
theorem B3024071 : Blo 1678039 3024071 := bstep (se 1 (by rfl) ⟨2268053, by rfl⟩ : syracuseStep 3024071 = 4536107) B4536107
theorem B10216651 : Blo 1678039 10216651 := bstep (se 1 (by rfl) ⟨7662488, by rfl⟩ : syracuseStep 10216651 = 15324977) B15324977
theorem B22979801 : Blo 1678039 22979801 := bstep (se 2 (by rfl) ⟨8617425, by rfl⟩ : syracuseStep 22979801 = 17234851) B17234851
theorem B2016619 : Blo 1678039 2016619 := bstep (se 1 (by rfl) ⟨1512464, by rfl⟩ : syracuseStep 2016619 = 3024929) B3024929
theorem B27608483 : Blo 1678039 27608483 := bstep (se 1 (by rfl) ⟨20706362, by rfl⟩ : syracuseStep 27608483 = 41412725) B41412725
theorem B5604851 : Blo 1678039 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B19121669 : Blo 1678039 19121669 := bstep (se 4 (by rfl) ⟨1792656, by rfl⟩ : syracuseStep 19121669 = 3585313) B3585313
theorem B8496737 : Blo 1678039 8496737 := bstep (se 2 (by rfl) ⟨3186276, by rfl⟩ : syracuseStep 8496737 = 6372553) B6372553
theorem B3778145 : Blo 1678039 3778145 := bstep (se 2 (by rfl) ⟨1416804, by rfl⟩ : syracuseStep 3778145 = 2833609) B2833609
theorem B13616855 : Blo 1678039 13616855 := bstep (se 1 (by rfl) ⟨10212641, by rfl⟩ : syracuseStep 13616855 = 20425283) B20425283
theorem B27223897 : Blo 1678039 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B3188585 : Blo 1678039 3188585 := bstep (se 2 (by rfl) ⟨1195719, by rfl⟩ : syracuseStep 3188585 = 2391439) B2391439
theorem B6375287 : Blo 1678039 6375287 := bstep (se 1 (by rfl) ⟨4781465, by rfl⟩ : syracuseStep 6375287 = 9562931) B9562931
theorem B3778487 : Blo 1678039 3778487 := bstep (se 1 (by rfl) ⟨2833865, by rfl⟩ : syracuseStep 3778487 = 5667731) B5667731
theorem B12101561 : Blo 1678039 12101561 := bstep (se 2 (by rfl) ⟨4538085, by rfl⟩ : syracuseStep 12101561 = 9076171) B9076171
theorem B3229627 : Blo 1678039 3229627 := bstep (se 1 (by rfl) ⟨2422220, by rfl⟩ : syracuseStep 3229627 = 4844441) B4844441
theorem B2689031 : Blo 1678039 2689031 := bstep (se 1 (by rfl) ⟨2016773, by rfl⟩ : syracuseStep 2689031 = 4033547) B4033547
theorem B2123815 : Blo 1678039 2123815 := bstep (se 1 (by rfl) ⟨1592861, by rfl⟩ : syracuseStep 2123815 = 3185723) B3185723
theorem B2517071 : Blo 1678039 2517071 := bstep (se 1 (by rfl) ⟨1887803, by rfl⟩ : syracuseStep 2517071 = 3775607) B3775607
theorem B2517191 : Blo 1678039 2517191 := bstep (se 1 (by rfl) ⟨1887893, by rfl⟩ : syracuseStep 2517191 = 3775787) B3775787
theorem B2517353 : Blo 1678039 2517353 := bstep (se 2 (by rfl) ⟨944007, by rfl⟩ : syracuseStep 2517353 = 1888015) B1888015
theorem B2124139 : Blo 1678039 2124139 := bstep (se 1 (by rfl) ⟨1593104, by rfl⟩ : syracuseStep 2124139 = 3186209) B3186209
theorem B7268737 : Blo 1678039 7268737 := bstep (se 2 (by rfl) ⟨2725776, by rfl⟩ : syracuseStep 7268737 = 5451553) B5451553
theorem B18155927 : Blo 1678039 18155927 := bstep (se 1 (by rfl) ⟨13616945, by rfl⟩ : syracuseStep 18155927 = 27233891) B27233891
theorem B2517431 : Blo 1678039 2517431 := bstep (se 1 (by rfl) ⟨1888073, by rfl⟩ : syracuseStep 2517431 = 3776147) B3776147
theorem B2517467 : Blo 1678039 2517467 := bstep (se 1 (by rfl) ⟨1888100, by rfl⟩ : syracuseStep 2517467 = 3776201) B3776201
theorem B3779081 : Blo 1678039 3779081 := bstep (se 2 (by rfl) ⟨1417155, by rfl⟩ : syracuseStep 3779081 = 2834311) B2834311
theorem B91875869 : Blo 1678039 91875869 := bstep (se 3 (by rfl) ⟨17226725, by rfl⟩ : syracuseStep 91875869 = 34453451) B34453451
theorem B9562657 : Blo 1678039 9562657 := bstep (se 2 (by rfl) ⟨3585996, by rfl⟩ : syracuseStep 9562657 = 7171993) B7171993
theorem B6376259 : Blo 1678039 6376259 := bstep (se 1 (by rfl) ⟨4782194, by rfl⟩ : syracuseStep 6376259 = 9564389) B9564389
theorem B5106527 : Blo 1678039 5106527 := bstep (se 1 (by rfl) ⟨3829895, by rfl⟩ : syracuseStep 5106527 = 7659791) B7659791
theorem B3779423 : Blo 1678039 3779423 := bstep (se 1 (by rfl) ⟨2834567, by rfl⟩ : syracuseStep 3779423 = 5669135) B5669135
theorem B2517935 : Blo 1678039 2517935 := bstep (se 1 (by rfl) ⟨1888451, by rfl⟩ : syracuseStep 2517935 = 3776903) B3776903
theorem B19123127 : Blo 1678039 19123127 := bstep (se 1 (by rfl) ⟨14342345, by rfl⟩ : syracuseStep 19123127 = 28684691) B28684691
theorem B6810551 : Blo 1678039 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B2518025 : Blo 1678039 2518025 := bstep (se 2 (by rfl) ⟨944259, by rfl⟩ : syracuseStep 2518025 = 1888519) B1888519
theorem B8498195 : Blo 1678039 8498195 := bstep (se 1 (by rfl) ⟨6373646, by rfl⟩ : syracuseStep 8498195 = 12747293) B12747293
theorem B3779603 : Blo 1678039 3779603 := bstep (se 1 (by rfl) ⟨2834702, by rfl⟩ : syracuseStep 3779603 = 5669405) B5669405
theorem B2518055 : Blo 1678039 2518055 := bstep (se 1 (by rfl) ⟨1888541, by rfl⟩ : syracuseStep 2518055 = 3777083) B3777083
theorem B2518139 : Blo 1678039 2518139 := bstep (se 1 (by rfl) ⟨1888604, by rfl⟩ : syracuseStep 2518139 = 3777209) B3777209
theorem B5663897 : Blo 1678039 5663897 := bstep (se 2 (by rfl) ⟨2123961, by rfl⟩ : syracuseStep 5663897 = 4247923) B4247923
theorem B2518265 : Blo 1678039 2518265 := bstep (se 2 (by rfl) ⟨944349, by rfl⟩ : syracuseStep 2518265 = 1888699) B1888699
theorem B6376715 : Blo 1678039 6376715 := bstep (se 1 (by rfl) ⟨4782536, by rfl⟩ : syracuseStep 6376715 = 9565073) B9565073
theorem B2518367 : Blo 1678039 2518367 := bstep (se 1 (by rfl) ⟨1888775, by rfl⟩ : syracuseStep 2518367 = 3777551) B3777551
theorem B3779945 : Blo 1678039 3779945 := bstep (se 2 (by rfl) ⟨1417479, by rfl⟩ : syracuseStep 3779945 = 2834959) B2834959
theorem B2518379 : Blo 1678039 2518379 := bstep (se 1 (by rfl) ⟨1888784, by rfl⟩ : syracuseStep 2518379 = 3777569) B3777569
theorem B2518607 : Blo 1678039 2518607 := bstep (se 1 (by rfl) ⟨1888955, by rfl⟩ : syracuseStep 2518607 = 3777911) B3777911
theorem B4779643 : Blo 1678039 4779643 := bstep (se 1 (by rfl) ⟨3584732, by rfl⟩ : syracuseStep 4779643 = 7169465) B7169465
theorem B2125435 : Blo 1678039 2125435 := bstep (se 1 (by rfl) ⟨1594076, by rfl⟩ : syracuseStep 2125435 = 3188153) B3188153
theorem B10751687 : Blo 1678039 10751687 := bstep (se 1 (by rfl) ⟨8063765, by rfl⟩ : syracuseStep 10751687 = 16127531) B16127531
theorem B1887943 : Blo 1678039 1887943 := bstep (se 1 (by rfl) ⟨1415957, by rfl⟩ : syracuseStep 1887943 = 2831915) B2831915
theorem B2518727 : Blo 1678039 2518727 := bstep (se 1 (by rfl) ⟨1889045, by rfl⟩ : syracuseStep 2518727 = 3778091) B3778091
theorem B3403475 : Blo 1678039 3403475 := bstep (se 1 (by rfl) ⟨2552606, by rfl⟩ : syracuseStep 3403475 = 5105213) B5105213
theorem B10751737 : Blo 1678039 10751737 := bstep (se 2 (by rfl) ⟨4031901, by rfl⟩ : syracuseStep 10751737 = 8063803) B8063803
theorem B4779769 : Blo 1678039 4779769 := bstep (se 2 (by rfl) ⟨1792413, by rfl⟩ : syracuseStep 4779769 = 3584827) B3584827
theorem B2551657 : Blo 1678039 2551657 := bstep (se 2 (by rfl) ⟨956871, by rfl⟩ : syracuseStep 2551657 = 1913743) B1913743
theorem B2518889 : Blo 1678039 2518889 := bstep (se 2 (by rfl) ⟨944583, by rfl⟩ : syracuseStep 2518889 = 1889167) B1889167
theorem B26201987 : Blo 1678039 26201987 := bstep (se 1 (by rfl) ⟨19651490, by rfl⟩ : syracuseStep 26201987 = 39302981) B39302981
theorem B2518967 : Blo 1678039 2518967 := bstep (se 1 (by rfl) ⟨1889225, by rfl⟩ : syracuseStep 2518967 = 3778451) B3778451
theorem B6377399 : Blo 1678039 6377399 := bstep (se 1 (by rfl) ⟨4783049, by rfl⟩ : syracuseStep 6377399 = 9566099) B9566099
theorem B2519003 : Blo 1678039 2519003 := bstep (se 1 (by rfl) ⟨1889252, by rfl⟩ : syracuseStep 2519003 = 3778505) B3778505
theorem B5665085 : Blo 1678039 5665085 := bstep (se 3 (by rfl) ⟨1062203, by rfl⟩ : syracuseStep 5665085 = 2124407) B2124407
theorem B5747087 : Blo 1678039 5747087 := bstep (se 1 (by rfl) ⟨4310315, by rfl⟩ : syracuseStep 5747087 = 8620631) B8620631
theorem B2519471 : Blo 1678039 2519471 := bstep (se 1 (by rfl) ⟨1889603, by rfl⟩ : syracuseStep 2519471 = 3779207) B3779207
theorem B2519561 : Blo 1678039 2519561 := bstep (se 2 (by rfl) ⟨944835, by rfl⟩ : syracuseStep 2519561 = 1889671) B1889671
theorem B1888807 : Blo 1678039 1888807 := bstep (se 1 (by rfl) ⟨1416605, by rfl⟩ : syracuseStep 1888807 = 2833211) B2833211
theorem B2519591 : Blo 1678039 2519591 := bstep (se 1 (by rfl) ⟨1889693, by rfl⟩ : syracuseStep 2519591 = 3779387) B3779387
theorem B2519675 : Blo 1678039 2519675 := bstep (se 1 (by rfl) ⟨1889756, by rfl⟩ : syracuseStep 2519675 = 3779513) B3779513
theorem B6378173 : Blo 1678039 6378173 := bstep (se 3 (by rfl) ⟨1195907, by rfl⟩ : syracuseStep 6378173 = 2391815) B2391815
theorem B2519801 : Blo 1678039 2519801 := bstep (se 2 (by rfl) ⟨944925, by rfl⟩ : syracuseStep 2519801 = 1889851) B1889851
theorem B4780873 : Blo 1678039 4780873 := bstep (se 2 (by rfl) ⟨1792827, by rfl⟩ : syracuseStep 4780873 = 3585655) B3585655
theorem B2519903 : Blo 1678039 2519903 := bstep (se 1 (by rfl) ⟨1889927, by rfl⟩ : syracuseStep 2519903 = 3779855) B3779855
theorem B21517163 : Blo 1678039 21517163 := bstep (se 1 (by rfl) ⟨16137872, by rfl⟩ : syracuseStep 21517163 = 32275745) B32275745
theorem B2519915 : Blo 1678039 2519915 := bstep (se 1 (by rfl) ⟨1889936, by rfl⟩ : syracuseStep 2519915 = 3779873) B3779873
theorem B3830689 : Blo 1678039 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B5665949 : Blo 1678039 5665949 := bstep (se 3 (by rfl) ⟨1062365, by rfl⟩ : syracuseStep 5665949 = 2124731) B2124731
theorem B4781227 : Blo 1678039 4781227 := bstep (se 1 (by rfl) ⟨3585920, by rfl⟩ : syracuseStep 4781227 = 7171841) B7171841
theorem B2389343 : Blo 1678039 2389343 := bstep (se 1 (by rfl) ⟨1792007, by rfl⟩ : syracuseStep 2389343 = 3584015) B3584015
theorem B6378857 : Blo 1678039 6378857 := bstep (se 2 (by rfl) ⟨2392071, by rfl⟩ : syracuseStep 6378857 = 4784143) B4784143
theorem B2831881 : Blo 1678039 2831881 := bstep (se 2 (by rfl) ⟨1061955, by rfl⟩ : syracuseStep 2831881 = 2123911) B2123911
theorem B33166945 : Blo 1678039 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B7173755 : Blo 1678039 7173755 := bstep (se 1 (by rfl) ⟨5380316, by rfl⟩ : syracuseStep 7173755 = 10760633) B10760633
theorem B2832043 : Blo 1678039 2832043 := bstep (se 1 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 2832043 = 4248065) B4248065
theorem B5666489 : Blo 1678039 5666489 := bstep (se 2 (by rfl) ⟨2124933, by rfl⟩ : syracuseStep 5666489 = 4249867) B4249867
theorem B2389753 : Blo 1678039 2389753 := bstep (se 2 (by rfl) ⟨896157, by rfl⟩ : syracuseStep 2389753 = 1792315) B1792315
theorem B8501111 : Blo 1678039 8501111 := bstep (se 1 (by rfl) ⟨6375833, by rfl⟩ : syracuseStep 8501111 = 12751667) B12751667
theorem B10762145 : Blo 1678039 10762145 := bstep (se 2 (by rfl) ⟨4035804, by rfl⟩ : syracuseStep 10762145 = 8071609) B8071609
theorem B29087693 : Blo 1678039 29087693 := bstep (se 3 (by rfl) ⟨5453942, by rfl⟩ : syracuseStep 29087693 = 10907885) B10907885
theorem B2832347 : Blo 1678039 2832347 := bstep (se 1 (by rfl) ⟨2124260, by rfl⟩ : syracuseStep 2832347 = 4248521) B4248521
theorem B2873351 : Blo 1678039 2873351 := bstep (se 1 (by rfl) ⟨2155013, by rfl⟩ : syracuseStep 2873351 = 4310027) B4310027
theorem B5380111 : Blo 1678039 5380111 := bstep (se 1 (by rfl) ⟨4035083, by rfl⟩ : syracuseStep 5380111 = 8070167) B8070167
theorem B181639189 : Blo 1678039 181639189 := bstep (se 6 (by rfl) ⟨4257168, by rfl⟩ : syracuseStep 181639189 = 8514337) B8514337
theorem B2553895 : Blo 1678039 2553895 := bstep (se 1 (by rfl) ⟨1915421, by rfl⟩ : syracuseStep 2553895 = 3830843) B3830843
theorem B2390095 : Blo 1678039 2390095 := bstep (se 1 (by rfl) ⟨1792571, by rfl⟩ : syracuseStep 2390095 = 3585143) B3585143
theorem B5380175 : Blo 1678039 5380175 := bstep (se 1 (by rfl) ⟨4035131, by rfl⟩ : syracuseStep 5380175 = 8070263) B8070263
theorem B5380253 : Blo 1678039 5380253 := bstep (se 3 (by rfl) ⟨1008797, by rfl⟩ : syracuseStep 5380253 = 2017595) B2017595
theorem B2832583 : Blo 1678039 2832583 := bstep (se 1 (by rfl) ⟨2124437, by rfl⟩ : syracuseStep 2832583 = 4248875) B4248875
theorem B12753125 : Blo 1678039 12753125 := bstep (se 4 (by rfl) ⟨1195605, by rfl⟩ : syracuseStep 12753125 = 2391211) B2391211
theorem B4249847 : Blo 1678039 4249847 := bstep (se 1 (by rfl) ⟨3187385, by rfl⟩ : syracuseStep 4249847 = 6374771) B6374771
theorem B9558283 : Blo 1678039 9558283 := bstep (se 1 (by rfl) ⟨7168712, by rfl⟩ : syracuseStep 9558283 = 14337425) B14337425
theorem B5667083 : Blo 1678039 5667083 := bstep (se 1 (by rfl) ⟨4250312, by rfl⟩ : syracuseStep 5667083 = 8500625) B8500625
theorem B13621553 : Blo 1678039 13621553 := bstep (se 2 (by rfl) ⟨5108082, by rfl⟩ : syracuseStep 13621553 = 10216165) B10216165
theorem B2832745 : Blo 1678039 2832745 := bstep (se 2 (by rfl) ⟨1062279, by rfl⟩ : syracuseStep 2832745 = 2124559) B2124559
theorem B5667353 : Blo 1678039 5667353 := bstep (se 2 (by rfl) ⟨2125257, by rfl⟩ : syracuseStep 5667353 = 4250515) B4250515
theorem B1678043 : Blo 1678039 1678043 := bstep (se 1 (by rfl) ⟨1258532, by rfl⟩ : syracuseStep 1678043 = 2517065) B2517065
theorem B1678119 : Blo 1678039 1678119 := bstep (se 1 (by rfl) ⟨1258589, by rfl⟩ : syracuseStep 1678119 = 2517179) B2517179
theorem B1678159 : Blo 1678039 1678159 := bstep (se 1 (by rfl) ⟨1258619, by rfl⟩ : syracuseStep 1678159 = 2517239) B2517239
theorem B2071391 : Blo 1678039 2071391 := bstep (se 1 (by rfl) ⟨1553543, by rfl⟩ : syracuseStep 2071391 = 3107087) B3107087
theorem B1678175 : Blo 1678039 1678175 := bstep (se 1 (by rfl) ⟨1258631, by rfl⟩ : syracuseStep 1678175 = 2517263) B2517263
theorem B1678203 : Blo 1678039 1678203 := bstep (se 1 (by rfl) ⟨1258652, by rfl⟩ : syracuseStep 1678203 = 2517305) B2517305
theorem B1678255 : Blo 1678039 1678255 := bstep (se 1 (by rfl) ⟨1258691, by rfl⟩ : syracuseStep 1678255 = 2517383) B2517383
theorem B16137143 : Blo 1678039 16137143 := bstep (se 1 (by rfl) ⟨12102857, by rfl⟩ : syracuseStep 16137143 = 24205715) B24205715
theorem B2833339 : Blo 1678039 2833339 := bstep (se 1 (by rfl) ⟨2125004, by rfl⟩ : syracuseStep 2833339 = 4250009) B4250009
theorem B1678279 : Blo 1678039 1678279 := bstep (se 1 (by rfl) ⟨1258709, by rfl⟩ : syracuseStep 1678279 = 2517419) B2517419
theorem B1678299 : Blo 1678039 1678299 := bstep (se 1 (by rfl) ⟨1258724, by rfl⟩ : syracuseStep 1678299 = 2517449) B2517449
theorem B4307975 : Blo 1678039 4307975 := bstep (se 1 (by rfl) ⟨3230981, by rfl⟩ : syracuseStep 4307975 = 6461963) B6461963
theorem B2726921 : Blo 1678039 2726921 := bstep (se 2 (by rfl) ⟨1022595, by rfl⟩ : syracuseStep 2726921 = 2045191) B2045191
theorem B6372371 : Blo 1678039 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B1678375 : Blo 1678039 1678375 := bstep (se 1 (by rfl) ⟨1258781, by rfl⟩ : syracuseStep 1678375 = 2517563) B2517563
theorem B2833447 : Blo 1678039 2833447 := bstep (se 1 (by rfl) ⟨2125085, by rfl⟩ : syracuseStep 2833447 = 4250171) B4250171
theorem B1793063 : Blo 1678039 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B1678415 : Blo 1678039 1678415 := bstep (se 1 (by rfl) ⟨1258811, by rfl⟩ : syracuseStep 1678415 = 2517623) B2517623
theorem B1678431 : Blo 1678039 1678431 := bstep (se 1 (by rfl) ⟨1258823, by rfl⟩ : syracuseStep 1678431 = 2517647) B2517647
theorem B1678459 : Blo 1678039 1678459 := bstep (se 1 (by rfl) ⟨1258844, by rfl⟩ : syracuseStep 1678459 = 2517689) B2517689
theorem B45964421 : Blo 1678039 45964421 := bstep (se 4 (by rfl) ⟨4309164, by rfl⟩ : syracuseStep 45964421 = 8618329) B8618329
theorem B1678511 : Blo 1678039 1678511 := bstep (se 1 (by rfl) ⟨1258883, by rfl⟩ : syracuseStep 1678511 = 2517767) B2517767
theorem B1678535 : Blo 1678039 1678535 := bstep (se 1 (by rfl) ⟨1258901, by rfl⟩ : syracuseStep 1678535 = 2517803) B2517803
theorem B1678555 : Blo 1678039 1678555 := bstep (se 1 (by rfl) ⟨1258916, by rfl⟩ : syracuseStep 1678555 = 2517833) B2517833
theorem B1678631 : Blo 1678039 1678631 := bstep (se 1 (by rfl) ⟨1258973, by rfl⟩ : syracuseStep 1678631 = 2517947) B2517947
theorem B1678671 : Blo 1678039 1678671 := bstep (se 1 (by rfl) ⟨1259003, by rfl⟩ : syracuseStep 1678671 = 2518007) B2518007
theorem B1678687 : Blo 1678039 1678687 := bstep (se 1 (by rfl) ⟨1259015, by rfl⟩ : syracuseStep 1678687 = 2518031) B2518031
theorem B2833771 : Blo 1678039 2833771 := bstep (se 1 (by rfl) ⟨2125328, by rfl⟩ : syracuseStep 2833771 = 4250657) B4250657
theorem B1678715 : Blo 1678039 1678715 := bstep (se 1 (by rfl) ⟨1259036, by rfl⟩ : syracuseStep 1678715 = 2518073) B2518073
theorem B174562685 : Blo 1678039 174562685 := bstep (se 3 (by rfl) ⟨32730503, by rfl⟩ : syracuseStep 174562685 = 65461007) B65461007
theorem B1678767 : Blo 1678039 1678767 := bstep (se 1 (by rfl) ⟨1259075, by rfl⟩ : syracuseStep 1678767 = 2518151) B2518151
theorem B1678791 : Blo 1678039 1678791 := bstep (se 1 (by rfl) ⟨1259093, by rfl⟩ : syracuseStep 1678791 = 2518187) B2518187
theorem B6372827 : Blo 1678039 6372827 := bstep (se 1 (by rfl) ⟨4779620, by rfl⟩ : syracuseStep 6372827 = 9559241) B9559241
theorem B1678811 : Blo 1678039 1678811 := bstep (se 1 (by rfl) ⟨1259108, by rfl⟩ : syracuseStep 1678811 = 2518217) B2518217
theorem B2153947 : Blo 1678039 2153947 := bstep (se 1 (by rfl) ⟨1615460, by rfl⟩ : syracuseStep 2153947 = 3230921) B3230921
theorem B3776039 : Blo 1678039 3776039 := bstep (se 1 (by rfl) ⟨2832029, by rfl⟩ : syracuseStep 3776039 = 5664059) B5664059
theorem B1678887 : Blo 1678039 1678887 := bstep (se 1 (by rfl) ⟨1259165, by rfl⟩ : syracuseStep 1678887 = 2518331) B2518331
theorem B1678927 : Blo 1678039 1678927 := bstep (se 1 (by rfl) ⟨1259195, by rfl⟩ : syracuseStep 1678927 = 2518391) B2518391
theorem B1678943 : Blo 1678039 1678943 := bstep (se 1 (by rfl) ⟨1259207, by rfl⟩ : syracuseStep 1678943 = 2518415) B2518415
theorem B1678971 : Blo 1678039 1678971 := bstep (se 1 (by rfl) ⟨1259228, by rfl⟩ : syracuseStep 1678971 = 2518457) B2518457
theorem B5742215 : Blo 1678039 5742215 := bstep (se 1 (by rfl) ⟨4306661, by rfl⟩ : syracuseStep 5742215 = 8613323) B8613323
theorem B5668487 : Blo 1678039 5668487 := bstep (se 1 (by rfl) ⟨4251365, by rfl⟩ : syracuseStep 5668487 = 8502731) B8502731
theorem B4251275 : Blo 1678039 4251275 := bstep (se 1 (by rfl) ⟨3188456, by rfl⟩ : syracuseStep 4251275 = 6376913) B6376913
theorem B1679023 : Blo 1678039 1679023 := bstep (se 1 (by rfl) ⟨1259267, by rfl⟩ : syracuseStep 1679023 = 2518535) B2518535
theorem B21503677 : Blo 1678039 21503677 := bstep (se 3 (by rfl) ⟨4031939, by rfl⟩ : syracuseStep 21503677 = 8063879) B8063879
theorem B9559741 : Blo 1678039 9559741 := bstep (se 3 (by rfl) ⟨1792451, by rfl⟩ : syracuseStep 9559741 = 3584903) B3584903
theorem B5668541 : Blo 1678039 5668541 := bstep (se 3 (by rfl) ⟨1062851, by rfl⟩ : syracuseStep 5668541 = 2125703) B2125703
theorem B1679047 : Blo 1678039 1679047 := bstep (se 1 (by rfl) ⟨1259285, by rfl⟩ : syracuseStep 1679047 = 2518571) B2518571
theorem B21528281 : Blo 1678039 21528281 := bstep (se 2 (by rfl) ⟨8073105, by rfl⟩ : syracuseStep 21528281 = 16146211) B16146211
theorem B1679067 : Blo 1678039 1679067 := bstep (se 1 (by rfl) ⟨1259300, by rfl⟩ : syracuseStep 1679067 = 2518601) B2518601
theorem B1679143 : Blo 1678039 1679143 := bstep (se 1 (by rfl) ⟨1259357, by rfl⟩ : syracuseStep 1679143 = 2518715) B2518715
theorem B12099395 : Blo 1678039 12099395 := bstep (se 1 (by rfl) ⟨9074546, by rfl⟩ : syracuseStep 12099395 = 18149093) B18149093
theorem B1679183 : Blo 1678039 1679183 := bstep (se 1 (by rfl) ⟨1259387, by rfl⟩ : syracuseStep 1679183 = 2518775) B2518775
theorem B1679199 : Blo 1678039 1679199 := bstep (se 1 (by rfl) ⟨1259399, by rfl⟩ : syracuseStep 1679199 = 2518799) B2518799
theorem B4251487 : Blo 1678039 4251487 := bstep (se 1 (by rfl) ⟨3188615, by rfl⟩ : syracuseStep 4251487 = 6377231) B6377231
theorem B5668703 : Blo 1678039 5668703 := bstep (se 1 (by rfl) ⟨4251527, by rfl⟩ : syracuseStep 5668703 = 8503055) B8503055
theorem B3776363 : Blo 1678039 3776363 := bstep (se 1 (by rfl) ⟨2832272, by rfl⟩ : syracuseStep 3776363 = 5664545) B5664545
theorem B1679227 : Blo 1678039 1679227 := bstep (se 1 (by rfl) ⟨1259420, by rfl⟩ : syracuseStep 1679227 = 2518841) B2518841
theorem B3776417 : Blo 1678039 3776417 := bstep (se 2 (by rfl) ⟨1416156, by rfl⟩ : syracuseStep 3776417 = 2832313) B2832313
theorem B1679279 : Blo 1678039 1679279 := bstep (se 1 (by rfl) ⟨1259459, by rfl⟩ : syracuseStep 1679279 = 2518919) B2518919
theorem B1679303 : Blo 1678039 1679303 := bstep (se 1 (by rfl) ⟨1259477, by rfl⟩ : syracuseStep 1679303 = 2518955) B2518955
theorem B1679323 : Blo 1678039 1679323 := bstep (se 1 (by rfl) ⟨1259492, by rfl⟩ : syracuseStep 1679323 = 2518985) B2518985
theorem B9568307 : Blo 1678039 9568307 := bstep (se 1 (by rfl) ⟨7176230, by rfl⟩ : syracuseStep 9568307 = 14352461) B14352461
theorem B3186793 : Blo 1678039 3186793 := bstep (se 2 (by rfl) ⟨1195047, by rfl⟩ : syracuseStep 3186793 = 2390095) B2390095
theorem B3776723 : Blo 1678039 3776723 := bstep (se 1 (by rfl) ⟨2832542, by rfl⟩ : syracuseStep 3776723 = 5665085) B5665085
theorem B3776777 : Blo 1678039 3776777 := bstep (se 2 (by rfl) ⟨1416291, by rfl⟩ : syracuseStep 3776777 = 2832583) B2832583
theorem B1679647 : Blo 1678039 1679647 := bstep (se 1 (by rfl) ⟨1259735, by rfl⟩ : syracuseStep 1679647 = 2519471) B2519471
theorem B10207579 : Blo 1678039 10207579 := bstep (se 1 (by rfl) ⟨7655684, by rfl⟩ : syracuseStep 10207579 = 15311369) B15311369
theorem B1679707 : Blo 1678039 1679707 := bstep (se 1 (by rfl) ⟨1259780, by rfl⟩ : syracuseStep 1679707 = 2519561) B2519561
theorem B1679727 : Blo 1678039 1679727 := bstep (se 1 (by rfl) ⟨1259795, by rfl⟩ : syracuseStep 1679727 = 2519591) B2519591
theorem B1679783 : Blo 1678039 1679783 := bstep (se 1 (by rfl) ⟨1259837, by rfl⟩ : syracuseStep 1679783 = 2519675) B2519675
theorem B4252115 : Blo 1678039 4252115 := bstep (se 1 (by rfl) ⟨3189086, by rfl⟩ : syracuseStep 4252115 = 6378173) B6378173
theorem B3776993 : Blo 1678039 3776993 := bstep (se 2 (by rfl) ⟨1416372, by rfl⟩ : syracuseStep 3776993 = 2832745) B2832745
theorem B4538875 : Blo 1678039 4538875 := bstep (se 1 (by rfl) ⟨3404156, by rfl⟩ : syracuseStep 4538875 = 6808313) B6808313
theorem B1679867 : Blo 1678039 1679867 := bstep (se 1 (by rfl) ⟨1259900, by rfl⟩ : syracuseStep 1679867 = 2519801) B2519801
theorem B9691649 : Blo 1678039 9691649 := bstep (se 2 (by rfl) ⟨3634368, by rfl⟩ : syracuseStep 9691649 = 7268737) B7268737
theorem B2834939 : Blo 1678039 2834939 := bstep (se 1 (by rfl) ⟨2126204, by rfl⟩ : syracuseStep 2834939 = 4252409) B4252409
theorem B1679935 : Blo 1678039 1679935 := bstep (se 1 (by rfl) ⟨1259951, by rfl⟩ : syracuseStep 1679935 = 2519903) B2519903
theorem B14344775 : Blo 1678039 14344775 := bstep (se 1 (by rfl) ⟨10758581, by rfl⟩ : syracuseStep 14344775 = 21517163) B21517163
theorem B1679943 : Blo 1678039 1679943 := bstep (se 1 (by rfl) ⟨1259957, by rfl⟩ : syracuseStep 1679943 = 2519915) B2519915
theorem B8618617 : Blo 1678039 8618617 := bstep (se 2 (by rfl) ⟨3231981, by rfl⟩ : syracuseStep 8618617 = 6463963) B6463963
theorem B3777299 : Blo 1678039 3777299 := bstep (se 1 (by rfl) ⟨2832974, by rfl⟩ : syracuseStep 3777299 = 5665949) B5665949
theorem B2016047 : Blo 1678039 2016047 := bstep (se 1 (by rfl) ⟨1512035, by rfl⟩ : syracuseStep 2016047 = 3024071) B3024071
theorem B15319867 : Blo 1678039 15319867 := bstep (se 1 (by rfl) ⟨11489900, by rfl⟩ : syracuseStep 15319867 = 22979801) B22979801
theorem B4252571 : Blo 1678039 4252571 := bstep (se 1 (by rfl) ⟨3189428, by rfl⟩ : syracuseStep 4252571 = 6378857) B6378857
theorem B21505013 : Blo 1678039 21505013 := bstep (se 5 (by rfl) ⟨1008047, by rfl⟩ : syracuseStep 21505013 = 2016095) B2016095
theorem B3736567 : Blo 1678039 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B12747779 : Blo 1678039 12747779 := bstep (se 1 (by rfl) ⟨9560834, by rfl⟩ : syracuseStep 12747779 = 19121669) B19121669
theorem B48415805 : Blo 1678039 48415805 := bstep (se 3 (by rfl) ⟨9077963, by rfl⟩ : syracuseStep 48415805 = 18155927) B18155927
theorem B73622621 : Blo 1678039 73622621 := bstep (se 3 (by rfl) ⟨13804241, by rfl⟩ : syracuseStep 73622621 = 27608483) B27608483
theorem B6374497 : Blo 1678039 6374497 := bstep (se 2 (by rfl) ⟨2390436, by rfl⟩ : syracuseStep 6374497 = 4780873) B4780873
theorem B3777659 : Blo 1678039 3777659 := bstep (se 1 (by rfl) ⟨2833244, by rfl⟩ : syracuseStep 3777659 = 5666489) B5666489
theorem B9077903 : Blo 1678039 9077903 := bstep (se 1 (by rfl) ⟨6808427, by rfl⟩ : syracuseStep 9077903 = 13616855) B13616855
theorem B65406149 : Blo 1678039 65406149 := bstep (se 4 (by rfl) ⟨6131826, by rfl⟩ : syracuseStep 65406149 = 12263653) B12263653
theorem B3777785 : Blo 1678039 3777785 := bstep (se 2 (by rfl) ⟨1416669, by rfl⟩ : syracuseStep 3777785 = 2833339) B2833339
theorem B19391795 : Blo 1678039 19391795 := bstep (se 1 (by rfl) ⟨14543846, by rfl⟩ : syracuseStep 19391795 = 29087693) B29087693
theorem B3777929 : Blo 1678039 3777929 := bstep (se 2 (by rfl) ⟨1416723, by rfl⟩ : syracuseStep 3777929 = 2833447) B2833447
theorem B3778055 : Blo 1678039 3778055 := bstep (se 1 (by rfl) ⟨2833541, by rfl⟩ : syracuseStep 3778055 = 5667083) B5667083
theorem B6374969 : Blo 1678039 6374969 := bstep (se 2 (by rfl) ⟨2390613, by rfl⟩ : syracuseStep 6374969 = 4781227) B4781227
theorem B3778235 : Blo 1678039 3778235 := bstep (se 1 (by rfl) ⟨2833676, by rfl⟩ : syracuseStep 3778235 = 5667353) B5667353
theorem B3778361 : Blo 1678039 3778361 := bstep (se 2 (by rfl) ⟨1416885, by rfl⟩ : syracuseStep 3778361 = 2833771) B2833771
theorem B12748751 : Blo 1678039 12748751 := bstep (se 1 (by rfl) ⟨9561563, by rfl⟩ : syracuseStep 12748751 = 19123127) B19123127
theorem B10758095 : Blo 1678039 10758095 := bstep (se 1 (by rfl) ⟨8068571, by rfl⟩ : syracuseStep 10758095 = 16137143) B16137143
theorem B4540367 : Blo 1678039 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B44222593 : Blo 1678039 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B5523709 : Blo 1678039 5523709 := bstep (se 3 (by rfl) ⟨1035695, by rfl⟩ : syracuseStep 5523709 = 2071391) B2071391
theorem B2517257 : Blo 1678039 2517257 := bstep (se 2 (by rfl) ⟨943971, by rfl⟩ : syracuseStep 2517257 = 1887943) B1887943
theorem B2517359 : Blo 1678039 2517359 := bstep (se 1 (by rfl) ⟨1888019, by rfl⟩ : syracuseStep 2517359 = 3776039) B3776039
theorem B3828143 : Blo 1678039 3828143 := bstep (se 1 (by rfl) ⟨2871107, by rfl⟩ : syracuseStep 3828143 = 5742215) B5742215
theorem B3778991 : Blo 1678039 3778991 := bstep (se 1 (by rfl) ⟨2834243, by rfl⟩ : syracuseStep 3778991 = 5668487) B5668487
theorem B3779027 : Blo 1678039 3779027 := bstep (se 1 (by rfl) ⟨2834270, by rfl⟩ : syracuseStep 3779027 = 5668541) B5668541
theorem B3402209 : Blo 1678039 3402209 := bstep (se 2 (by rfl) ⟨1275828, by rfl⟩ : syracuseStep 3402209 = 2551657) B2551657
theorem B3779135 : Blo 1678039 3779135 := bstep (se 1 (by rfl) ⟨2834351, by rfl⟩ : syracuseStep 3779135 = 5668703) B5668703
theorem B2517575 : Blo 1678039 2517575 := bstep (se 1 (by rfl) ⟨1888181, by rfl⟩ : syracuseStep 2517575 = 3776363) B3776363
theorem B17467991 : Blo 1678039 17467991 := bstep (se 1 (by rfl) ⟨13100993, by rfl⟩ : syracuseStep 17467991 = 26201987) B26201987
theorem B2517611 : Blo 1678039 2517611 := bstep (se 1 (by rfl) ⟨1888208, by rfl⟩ : syracuseStep 2517611 = 3776417) B3776417
theorem B3779243 : Blo 1678039 3779243 := bstep (se 1 (by rfl) ⟨2834432, by rfl⟩ : syracuseStep 3779243 = 5668865) B5668865
theorem B2124463 : Blo 1678039 2124463 := bstep (se 1 (by rfl) ⟨1593347, by rfl⟩ : syracuseStep 2124463 = 3186695) B3186695
theorem B7662269 : Blo 1678039 7662269 := bstep (se 3 (by rfl) ⟨1436675, by rfl⟩ : syracuseStep 7662269 = 2873351) B2873351
theorem B2517839 : Blo 1678039 2517839 := bstep (se 1 (by rfl) ⟨1888379, by rfl⟩ : syracuseStep 2517839 = 3776759) B3776759
theorem B6810763 : Blo 1678039 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B3779783 : Blo 1678039 3779783 := bstep (se 1 (by rfl) ⟨2834837, by rfl⟩ : syracuseStep 3779783 = 5669675) B5669675
theorem B2518235 : Blo 1678039 2518235 := bstep (se 1 (by rfl) ⟨1888676, by rfl⟩ : syracuseStep 2518235 = 3777353) B3777353
theorem B3779963 : Blo 1678039 3779963 := bstep (se 1 (by rfl) ⟨2834972, by rfl⟩ : syracuseStep 3779963 = 5669945) B5669945
theorem B12750209 : Blo 1678039 12750209 := bstep (se 2 (by rfl) ⟨4781328, by rfl⟩ : syracuseStep 12750209 = 9562657) B9562657
theorem B2518409 : Blo 1678039 2518409 := bstep (se 2 (by rfl) ⟨944403, by rfl⟩ : syracuseStep 2518409 = 1888807) B1888807
theorem B8498681 : Blo 1678039 8498681 := bstep (se 2 (by rfl) ⟨3187005, by rfl⟩ : syracuseStep 8498681 = 6374011) B6374011
theorem B3780089 : Blo 1678039 3780089 := bstep (se 2 (by rfl) ⟨1417533, by rfl⟩ : syracuseStep 3780089 = 2835067) B2835067
theorem B5664491 : Blo 1678039 5664491 := bstep (se 1 (by rfl) ⟨4248368, by rfl⟩ : syracuseStep 5664491 = 8496737) B8496737
theorem B2518763 : Blo 1678039 2518763 := bstep (se 1 (by rfl) ⟨1889072, by rfl⟩ : syracuseStep 2518763 = 3778145) B3778145
theorem B8499005 : Blo 1678039 8499005 := bstep (se 3 (by rfl) ⟨1593563, by rfl⟩ : syracuseStep 8499005 = 3187127) B3187127
theorem B5107585 : Blo 1678039 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B2518991 : Blo 1678039 2518991 := bstep (se 1 (by rfl) ⟨1889243, by rfl⟩ : syracuseStep 2518991 = 3778487) B3778487
theorem B1888231 : Blo 1678039 1888231 := bstep (se 1 (by rfl) ⟨1416173, by rfl⟩ : syracuseStep 1888231 = 2832347) B2832347
theorem B9081035 : Blo 1678039 9081035 := bstep (se 1 (by rfl) ⟨6810776, by rfl⟩ : syracuseStep 9081035 = 13621553) B13621553
theorem B2519387 : Blo 1678039 2519387 := bstep (se 1 (by rfl) ⟨1889540, by rfl⟩ : syracuseStep 2519387 = 3779081) B3779081
theorem B3404351 : Blo 1678039 3404351 := bstep (se 1 (by rfl) ⟨2553263, by rfl⟩ : syracuseStep 3404351 = 5106527) B5106527
theorem B2519615 : Blo 1678039 2519615 := bstep (se 1 (by rfl) ⟨1889711, by rfl⟩ : syracuseStep 2519615 = 3779423) B3779423
theorem B2871929 : Blo 1678039 2871929 := bstep (se 2 (by rfl) ⟨1076973, by rfl⟩ : syracuseStep 2871929 = 2153947) B2153947
theorem B2871983 : Blo 1678039 2871983 := bstep (se 1 (by rfl) ⟨2153987, by rfl⟩ : syracuseStep 2871983 = 4307975) B4307975
theorem B4248247 : Blo 1678039 4248247 := bstep (se 1 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 4248247 = 6372371) B6372371
theorem B5665463 : Blo 1678039 5665463 := bstep (se 1 (by rfl) ⟨4249097, by rfl⟩ : syracuseStep 5665463 = 8498195) B8498195
theorem B2519735 : Blo 1678039 2519735 := bstep (se 1 (by rfl) ⟨1889801, by rfl⟩ : syracuseStep 2519735 = 3779603) B3779603
theorem B30642947 : Blo 1678039 30642947 := bstep (se 1 (by rfl) ⟨22982210, by rfl⟩ : syracuseStep 30642947 = 45964421) B45964421
theorem B32265053 : Blo 1678039 32265053 := bstep (se 3 (by rfl) ⟨6049697, by rfl⟩ : syracuseStep 32265053 = 12099395) B12099395
theorem B2519963 : Blo 1678039 2519963 := bstep (se 1 (by rfl) ⟨1889972, by rfl⟩ : syracuseStep 2519963 = 3779945) B3779945
theorem B4248551 : Blo 1678039 4248551 := bstep (se 1 (by rfl) ⟨3186413, by rfl⟩ : syracuseStep 4248551 = 6372827) B6372827
theorem B4306169 : Blo 1678039 4306169 := bstep (se 2 (by rfl) ⟨1614813, by rfl⟩ : syracuseStep 4306169 = 3229627) B3229627
theorem B25843049 : Blo 1678039 25843049 := bstep (se 2 (by rfl) ⟨9691143, by rfl⟩ : syracuseStep 25843049 = 19382287) B19382287
theorem B7173481 : Blo 1678039 7173481 := bstep (se 2 (by rfl) ⟨2690055, by rfl⟩ : syracuseStep 7173481 = 5380111) B5380111
theorem B242185585 : Blo 1678039 242185585 := bstep (se 2 (by rfl) ⟨90819594, by rfl⟩ : syracuseStep 242185585 = 181639189) B181639189
theorem B2831753 : Blo 1678039 2831753 := bstep (se 2 (by rfl) ⟨1061907, by rfl⟩ : syracuseStep 2831753 = 2123815) B2123815
theorem B4781501 : Blo 1678039 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B13620773 : Blo 1678039 13620773 := bstep (se 4 (by rfl) ⟨1276947, by rfl⟩ : syracuseStep 13620773 = 2553895) B2553895
theorem B1889887 : Blo 1678039 1889887 := bstep (se 1 (by rfl) ⟨1417415, by rfl⟩ : syracuseStep 1889887 = 2834831) B2834831
theorem B3831391 : Blo 1678039 3831391 := bstep (se 1 (by rfl) ⟨2873543, by rfl⟩ : syracuseStep 3831391 = 5747087) B5747087
theorem B12744377 : Blo 1678039 12744377 := bstep (se 2 (by rfl) ⟨4779141, by rfl⟩ : syracuseStep 12744377 = 9558283) B9558283
theorem B2832185 : Blo 1678039 2832185 := bstep (se 2 (by rfl) ⟨1062069, by rfl⟩ : syracuseStep 2832185 = 2124139) B2124139
theorem B4249705 : Blo 1678039 4249705 := bstep (se 2 (by rfl) ⟨1593639, by rfl⟩ : syracuseStep 4249705 = 3187279) B3187279
theorem B6371581 : Blo 1678039 6371581 := bstep (se 3 (by rfl) ⟨1194671, by rfl⟩ : syracuseStep 6371581 = 2389343) B2389343
theorem B4782503 : Blo 1678039 4782503 := bstep (se 1 (by rfl) ⟨3586877, by rfl⟩ : syracuseStep 4782503 = 7173755) B7173755
theorem B4250191 : Blo 1678039 4250191 := bstep (se 1 (by rfl) ⟨3187643, by rfl⟩ : syracuseStep 4250191 = 6375287) B6375287
theorem B5667407 : Blo 1678039 5667407 := bstep (se 1 (by rfl) ⟨4250555, by rfl⟩ : syracuseStep 5667407 = 8501111) B8501111
theorem B7174763 : Blo 1678039 7174763 := bstep (se 1 (by rfl) ⟨5381072, by rfl⟩ : syracuseStep 7174763 = 10762145) B10762145
theorem B8067707 : Blo 1678039 8067707 := bstep (se 1 (by rfl) ⟨6050780, by rfl⟩ : syracuseStep 8067707 = 12101561) B12101561
theorem B12745349 : Blo 1678039 12745349 := bstep (se 4 (by rfl) ⟨1194876, by rfl⟩ : syracuseStep 12745349 = 2389753) B2389753
theorem B1792687 : Blo 1678039 1792687 := bstep (se 1 (by rfl) ⟨1344515, by rfl⟩ : syracuseStep 1792687 = 2689031) B2689031
theorem B1678047 : Blo 1678039 1678047 := bstep (se 1 (by rfl) ⟨1258535, by rfl⟩ : syracuseStep 1678047 = 2517071) B2517071
theorem B3586783 : Blo 1678039 3586783 := bstep (se 1 (by rfl) ⟨2690087, by rfl⟩ : syracuseStep 3586783 = 5380175) B5380175
theorem B3586835 : Blo 1678039 3586835 := bstep (se 1 (by rfl) ⟨2690126, by rfl⟩ : syracuseStep 3586835 = 5380253) B5380253
theorem B1678127 : Blo 1678039 1678127 := bstep (se 1 (by rfl) ⟨1258595, by rfl⟩ : syracuseStep 1678127 = 2517191) B2517191
theorem B8502083 : Blo 1678039 8502083 := bstep (se 1 (by rfl) ⟨6376562, by rfl⟩ : syracuseStep 8502083 = 12753125) B12753125
theorem B2833231 : Blo 1678039 2833231 := bstep (se 1 (by rfl) ⟨2124923, by rfl⟩ : syracuseStep 2833231 = 4249847) B4249847
theorem B1678235 : Blo 1678039 1678235 := bstep (se 1 (by rfl) ⟨1258676, by rfl⟩ : syracuseStep 1678235 = 2517353) B2517353
theorem B13622201 : Blo 1678039 13622201 := bstep (se 2 (by rfl) ⟨5108325, by rfl⟩ : syracuseStep 13622201 = 10216651) B10216651
theorem B1678287 : Blo 1678039 1678287 := bstep (se 1 (by rfl) ⟨1258715, by rfl⟩ : syracuseStep 1678287 = 2517431) B2517431
theorem B1678311 : Blo 1678039 1678311 := bstep (se 1 (by rfl) ⟨1258733, by rfl⟩ : syracuseStep 1678311 = 2517467) B2517467
theorem B61250579 : Blo 1678039 61250579 := bstep (se 1 (by rfl) ⟨45937934, by rfl⟩ : syracuseStep 61250579 = 91875869) B91875869
theorem B4250839 : Blo 1678039 4250839 := bstep (se 1 (by rfl) ⟨3188129, by rfl⟩ : syracuseStep 4250839 = 6376259) B6376259
theorem B10755301 : Blo 1678039 10755301 := bstep (se 4 (by rfl) ⟨1008309, by rfl⟩ : syracuseStep 10755301 = 2016619) B2016619
theorem B1678623 : Blo 1678039 1678623 := bstep (se 1 (by rfl) ⟨1258967, by rfl⟩ : syracuseStep 1678623 = 2517935) B2517935
theorem B1678683 : Blo 1678039 1678683 := bstep (se 1 (by rfl) ⟨1259012, by rfl⟩ : syracuseStep 1678683 = 2518025) B2518025
theorem B1817947 : Blo 1678039 1817947 := bstep (se 1 (by rfl) ⟨1363460, by rfl⟩ : syracuseStep 1817947 = 2726921) B2726921
theorem B3775841 : Blo 1678039 3775841 := bstep (se 2 (by rfl) ⟨1415940, by rfl⟩ : syracuseStep 3775841 = 2831881) B2831881
theorem B1678703 : Blo 1678039 1678703 := bstep (se 1 (by rfl) ⟨1259027, by rfl⟩ : syracuseStep 1678703 = 2518055) B2518055
theorem B1678759 : Blo 1678039 1678759 := bstep (se 1 (by rfl) ⟨1259069, by rfl⟩ : syracuseStep 1678759 = 2518139) B2518139
theorem B3775931 : Blo 1678039 3775931 := bstep (se 1 (by rfl) ⟨2831948, by rfl⟩ : syracuseStep 3775931 = 5663897) B5663897
theorem B6372857 : Blo 1678039 6372857 := bstep (se 2 (by rfl) ⟨2389821, by rfl⟩ : syracuseStep 6372857 = 4779643) B4779643
theorem B2833913 : Blo 1678039 2833913 := bstep (se 2 (by rfl) ⟨1062717, by rfl⟩ : syracuseStep 2833913 = 2125435) B2125435
theorem B1678843 : Blo 1678039 1678843 := bstep (se 1 (by rfl) ⟨1259132, by rfl⟩ : syracuseStep 1678843 = 2518265) B2518265
theorem B4251143 : Blo 1678039 4251143 := bstep (se 1 (by rfl) ⟨3188357, by rfl⟩ : syracuseStep 4251143 = 6376715) B6376715
theorem B3776057 : Blo 1678039 3776057 := bstep (se 2 (by rfl) ⟨1416021, by rfl⟩ : syracuseStep 3776057 = 2832043) B2832043
theorem B1678911 : Blo 1678039 1678911 := bstep (se 1 (by rfl) ⟨1259183, by rfl⟩ : syracuseStep 1678911 = 2518367) B2518367
theorem B1678919 : Blo 1678039 1678919 := bstep (se 1 (by rfl) ⟨1259189, by rfl⟩ : syracuseStep 1678919 = 2518379) B2518379
theorem B28671569 : Blo 1678039 28671569 := bstep (se 2 (by rfl) ⟨10751838, by rfl⟩ : syracuseStep 28671569 = 21503677) B21503677
theorem B12746321 : Blo 1678039 12746321 := bstep (se 2 (by rfl) ⟨4779870, by rfl⟩ : syracuseStep 12746321 = 9559741) B9559741
theorem B116375123 : Blo 1678039 116375123 := bstep (se 1 (by rfl) ⟨87281342, by rfl⟩ : syracuseStep 116375123 = 174562685) B174562685
theorem B8502893 : Blo 1678039 8502893 := bstep (se 3 (by rfl) ⟨1594292, by rfl⟩ : syracuseStep 8502893 = 3188585) B3188585
theorem B14335649 : Blo 1678039 14335649 := bstep (se 2 (by rfl) ⟨5375868, by rfl⟩ : syracuseStep 14335649 = 10751737) B10751737
theorem B6373025 : Blo 1678039 6373025 := bstep (se 2 (by rfl) ⟨2389884, by rfl⟩ : syracuseStep 6373025 = 4779769) B4779769
theorem B1679071 : Blo 1678039 1679071 := bstep (se 1 (by rfl) ⟨1259303, by rfl⟩ : syracuseStep 1679071 = 2518607) B2518607
theorem B2834183 : Blo 1678039 2834183 := bstep (se 1 (by rfl) ⟨2125637, by rfl⟩ : syracuseStep 2834183 = 4251275) B4251275
theorem B36298529 : Blo 1678039 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B5668649 : Blo 1678039 5668649 := bstep (se 2 (by rfl) ⟨2125743, by rfl⟩ : syracuseStep 5668649 = 4251487) B4251487
theorem B7167791 : Blo 1678039 7167791 := bstep (se 1 (by rfl) ⟨5375843, by rfl⟩ : syracuseStep 7167791 = 10751687) B10751687
theorem B1679151 : Blo 1678039 1679151 := bstep (se 1 (by rfl) ⟨1259363, by rfl⟩ : syracuseStep 1679151 = 2518727) B2518727
theorem B2268983 : Blo 1678039 2268983 := bstep (se 1 (by rfl) ⟨1701737, by rfl⟩ : syracuseStep 2268983 = 3403475) B3403475
theorem B14352187 : Blo 1678039 14352187 := bstep (se 1 (by rfl) ⟨10764140, by rfl⟩ : syracuseStep 14352187 = 21528281) B21528281
theorem B1679259 : Blo 1678039 1679259 := bstep (se 1 (by rfl) ⟨1259444, by rfl⟩ : syracuseStep 1679259 = 2518889) B2518889
theorem B1679311 : Blo 1678039 1679311 := bstep (se 1 (by rfl) ⟨1259483, by rfl⟩ : syracuseStep 1679311 = 2518967) B2518967
theorem B4251599 : Blo 1678039 4251599 := bstep (se 1 (by rfl) ⟨3188699, by rfl⟩ : syracuseStep 4251599 = 6377399) B6377399
theorem B1679335 : Blo 1678039 1679335 := bstep (se 1 (by rfl) ⟨1259501, by rfl⟩ : syracuseStep 1679335 = 2519003) B2519003
theorem B6054023 : Blo 1678039 6054023 := bstep (se 1 (by rfl) ⟨4540517, by rfl⟩ : syracuseStep 6054023 = 9081035) B9081035
theorem B1679591 : Blo 1678039 1679591 := bstep (se 1 (by rfl) ⟨1259693, by rfl⟩ : syracuseStep 1679591 = 2519387) B2519387
theorem B2834743 : Blo 1678039 2834743 := bstep (se 1 (by rfl) ⟨2126057, by rfl⟩ : syracuseStep 2834743 = 4252115) B4252115
theorem B7364945 : Blo 1678039 7364945 := bstep (se 2 (by rfl) ⟨2761854, by rfl⟩ : syracuseStep 7364945 = 5523709) B5523709
theorem B8495441 : Blo 1678039 8495441 := bstep (se 2 (by rfl) ⟨3185790, by rfl⟩ : syracuseStep 8495441 = 6371581) B6371581
theorem B2269567 : Blo 1678039 2269567 := bstep (se 1 (by rfl) ⟨1702175, by rfl⟩ : syracuseStep 2269567 = 3404351) B3404351
theorem B1679743 : Blo 1678039 1679743 := bstep (se 1 (by rfl) ⟨1259807, by rfl⟩ : syracuseStep 1679743 = 2519615) B2519615
theorem B3776975 : Blo 1678039 3776975 := bstep (se 1 (by rfl) ⟨2832731, by rfl⟩ : syracuseStep 3776975 = 5665463) B5665463
theorem B1679823 : Blo 1678039 1679823 := bstep (se 1 (by rfl) ⟨1259867, by rfl⟩ : syracuseStep 1679823 = 2519735) B2519735
theorem B1679975 : Blo 1678039 1679975 := bstep (se 1 (by rfl) ⟨1259981, by rfl⟩ : syracuseStep 1679975 = 2519963) B2519963
theorem B2835047 : Blo 1678039 2835047 := bstep (se 1 (by rfl) ⟨2126285, by rfl⟩ : syracuseStep 2835047 = 4252571) B4252571
theorem B14336675 : Blo 1678039 14336675 := bstep (se 1 (by rfl) ⟨10752506, by rfl⟩ : syracuseStep 14336675 = 21505013) B21505013
theorem B32277203 : Blo 1678039 32277203 := bstep (se 1 (by rfl) ⟨24207902, by rfl⟩ : syracuseStep 32277203 = 48415805) B48415805
theorem B12927863 : Blo 1678039 12927863 := bstep (se 1 (by rfl) ⟨9695897, by rfl⟩ : syracuseStep 12927863 = 19391795) B19391795
theorem B17228699 : Blo 1678039 17228699 := bstep (se 1 (by rfl) ⟨12921524, by rfl⟩ : syracuseStep 17228699 = 25843049) B25843049
theorem B3187667 : Blo 1678039 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B3777641 : Blo 1678039 3777641 := bstep (se 2 (by rfl) ⟨1416615, by rfl⟩ : syracuseStep 3777641 = 2833231) B2833231
theorem B8496251 : Blo 1678039 8496251 := bstep (se 1 (by rfl) ⟨6372188, by rfl⟩ : syracuseStep 8496251 = 12744377) B12744377
theorem B3188335 : Blo 1678039 3188335 := bstep (se 1 (by rfl) ⟨2391251, by rfl⟩ : syracuseStep 3188335 = 4782503) B4782503
theorem B3778271 : Blo 1678039 3778271 := bstep (se 1 (by rfl) ⟨2833703, by rfl⟩ : syracuseStep 3778271 = 5667407) B5667407
theorem B8496899 : Blo 1678039 8496899 := bstep (se 1 (by rfl) ⟨6372674, by rfl⟩ : syracuseStep 8496899 = 12745349) B12745349
theorem B322914113 : Blo 1678039 322914113 := bstep (se 2 (by rfl) ⟨121092792, by rfl⟩ : syracuseStep 322914113 = 242185585) B242185585
theorem B5376125 : Blo 1678039 5376125 := bstep (se 3 (by rfl) ⟨1008023, by rfl⟩ : syracuseStep 5376125 = 2016047) B2016047
theorem B2517227 : Blo 1678039 2517227 := bstep (se 1 (by rfl) ⟨1887920, by rfl⟩ : syracuseStep 2517227 = 3775841) B3775841
theorem B2517287 : Blo 1678039 2517287 := bstep (se 1 (by rfl) ⟨1887965, by rfl⟩ : syracuseStep 2517287 = 3775931) B3775931
theorem B2517371 : Blo 1678039 2517371 := bstep (se 1 (by rfl) ⟨1888028, by rfl⟩ : syracuseStep 2517371 = 3776057) B3776057
theorem B19114379 : Blo 1678039 19114379 := bstep (se 1 (by rfl) ⟨14335784, by rfl⟩ : syracuseStep 19114379 = 28671569) B28671569
theorem B8497547 : Blo 1678039 8497547 := bstep (se 1 (by rfl) ⟨6373160, by rfl⟩ : syracuseStep 8497547 = 12746321) B12746321
theorem B6810113 : Blo 1678039 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B3779099 : Blo 1678039 3779099 := bstep (se 1 (by rfl) ⟨2834324, by rfl⟩ : syracuseStep 3779099 = 5668649) B5668649
theorem B4778527 : Blo 1678039 4778527 := bstep (se 1 (by rfl) ⟨3583895, by rfl⟩ : syracuseStep 4778527 = 7167791) B7167791
theorem B2517641 : Blo 1678039 2517641 := bstep (se 2 (by rfl) ⟨944115, by rfl⟩ : syracuseStep 2517641 = 1888231) B1888231
theorem B2517815 : Blo 1678039 2517815 := bstep (se 1 (by rfl) ⟨1888361, by rfl⟩ : syracuseStep 2517815 = 3776723) B3776723
theorem B2517851 : Blo 1678039 2517851 := bstep (se 1 (by rfl) ⟨1888388, by rfl⟩ : syracuseStep 2517851 = 3776777) B3776777
theorem B2517995 : Blo 1678039 2517995 := bstep (se 1 (by rfl) ⟨1888496, by rfl⟩ : syracuseStep 2517995 = 3776993) B3776993
theorem B9563183 : Blo 1678039 9563183 := bstep (se 1 (by rfl) ⟨7172387, by rfl⟩ : syracuseStep 9563183 = 14344775) B14344775
theorem B13610105 : Blo 1678039 13610105 := bstep (se 2 (by rfl) ⟨5103789, by rfl⟩ : syracuseStep 13610105 = 10207579) B10207579
theorem B2518199 : Blo 1678039 2518199 := bstep (se 1 (by rfl) ⟨1888649, by rfl⟩ : syracuseStep 2518199 = 3777299) B3777299
theorem B8498519 : Blo 1678039 8498519 := bstep (se 1 (by rfl) ⟨6373889, by rfl⟩ : syracuseStep 8498519 = 12747779) B12747779
theorem B49081747 : Blo 1678039 49081747 := bstep (se 1 (by rfl) ⟨36811310, by rfl⟩ : syracuseStep 49081747 = 73622621) B73622621
theorem B2518439 : Blo 1678039 2518439 := bstep (se 1 (by rfl) ⟨1888829, by rfl⟩ : syracuseStep 2518439 = 3777659) B3777659
theorem B2518523 : Blo 1678039 2518523 := bstep (se 1 (by rfl) ⟨1888892, by rfl⟩ : syracuseStep 2518523 = 3777785) B3777785
theorem B5664329 : Blo 1678039 5664329 := bstep (se 2 (by rfl) ⟨2124123, by rfl⟩ : syracuseStep 5664329 = 4248247) B4248247
theorem B1887835 : Blo 1678039 1887835 := bstep (se 1 (by rfl) ⟨1415876, by rfl⟩ : syracuseStep 1887835 = 2831753) B2831753
theorem B2518619 : Blo 1678039 2518619 := bstep (se 1 (by rfl) ⟨1888964, by rfl⟩ : syracuseStep 2518619 = 3777929) B3777929
theorem B2518703 : Blo 1678039 2518703 := bstep (se 1 (by rfl) ⟨1889027, by rfl⟩ : syracuseStep 2518703 = 3778055) B3778055
theorem B9080515 : Blo 1678039 9080515 := bstep (se 1 (by rfl) ⟨6810386, by rfl⟩ : syracuseStep 9080515 = 13620773) B13620773
theorem B20426489 : Blo 1678039 20426489 := bstep (se 2 (by rfl) ⟨7659933, by rfl⟩ : syracuseStep 20426489 = 15319867) B15319867
theorem B2518823 : Blo 1678039 2518823 := bstep (se 1 (by rfl) ⟨1889117, by rfl⟩ : syracuseStep 2518823 = 3778235) B3778235
theorem B1888123 : Blo 1678039 1888123 := bstep (se 1 (by rfl) ⟨1416092, by rfl⟩ : syracuseStep 1888123 = 2832185) B2832185
theorem B2518907 : Blo 1678039 2518907 := bstep (se 1 (by rfl) ⟨1889180, by rfl⟩ : syracuseStep 2518907 = 3778361) B3778361
theorem B9072557 : Blo 1678039 9072557 := bstep (se 3 (by rfl) ⟨1701104, by rfl⟩ : syracuseStep 9072557 = 3402209) B3402209
theorem B8499167 : Blo 1678039 8499167 := bstep (se 1 (by rfl) ⟨6374375, by rfl⟩ : syracuseStep 8499167 = 12748751) B12748751
theorem B7172063 : Blo 1678039 7172063 := bstep (se 1 (by rfl) ⟨5379047, by rfl⟩ : syracuseStep 7172063 = 10758095) B10758095
theorem B3026911 : Blo 1678039 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B8499329 : Blo 1678039 8499329 := bstep (se 2 (by rfl) ⟨3187248, by rfl⟩ : syracuseStep 8499329 = 6374497) B6374497
theorem B9081017 : Blo 1678039 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B2552095 : Blo 1678039 2552095 := bstep (se 1 (by rfl) ⟨1914071, by rfl⟩ : syracuseStep 2552095 = 3828143) B3828143
theorem B2519327 : Blo 1678039 2519327 := bstep (se 1 (by rfl) ⟨1889495, by rfl⟩ : syracuseStep 2519327 = 3778991) B3778991
theorem B14340401 : Blo 1678039 14340401 := bstep (se 2 (by rfl) ⟨5377650, by rfl⟩ : syracuseStep 14340401 = 10755301) B10755301
theorem B2519351 : Blo 1678039 2519351 := bstep (se 1 (by rfl) ⟨1889513, by rfl⟩ : syracuseStep 2519351 = 3779027) B3779027
theorem B2519423 : Blo 1678039 2519423 := bstep (se 1 (by rfl) ⟨1889567, by rfl⟩ : syracuseStep 2519423 = 3779135) B3779135
theorem B11645327 : Blo 1678039 11645327 := bstep (se 1 (by rfl) ⟨8733995, by rfl⟩ : syracuseStep 11645327 = 17467991) B17467991
theorem B5378471 : Blo 1678039 5378471 := bstep (se 1 (by rfl) ⟨4033853, by rfl⟩ : syracuseStep 5378471 = 8067707) B8067707
theorem B2519495 : Blo 1678039 2519495 := bstep (se 1 (by rfl) ⟨1889621, by rfl⟩ : syracuseStep 2519495 = 3779243) B3779243
theorem B5108179 : Blo 1678039 5108179 := bstep (se 1 (by rfl) ⟨3831134, by rfl⟩ : syracuseStep 5108179 = 7662269) B7662269
theorem B9564641 : Blo 1678039 9564641 := bstep (se 2 (by rfl) ⟨3586740, by rfl⟩ : syracuseStep 9564641 = 7173481) B7173481
theorem B9081467 : Blo 1678039 9081467 := bstep (se 1 (by rfl) ⟨6811100, by rfl⟩ : syracuseStep 9081467 = 13622201) B13622201
theorem B40833719 : Blo 1678039 40833719 := bstep (se 1 (by rfl) ⟨30625289, by rfl⟩ : syracuseStep 40833719 = 61250579) B61250579
theorem B2519849 : Blo 1678039 2519849 := bstep (se 2 (by rfl) ⟨944943, by rfl⟩ : syracuseStep 2519849 = 1889887) B1889887
theorem B5108521 : Blo 1678039 5108521 := bstep (se 2 (by rfl) ⟨1915695, by rfl⟩ : syracuseStep 5108521 = 3831391) B3831391
theorem B2519855 : Blo 1678039 2519855 := bstep (se 1 (by rfl) ⟨1889891, by rfl⟩ : syracuseStep 2519855 = 3779783) B3779783
theorem B6050621 : Blo 1678039 6050621 := bstep (se 3 (by rfl) ⟨1134491, by rfl⟩ : syracuseStep 6050621 = 2268983) B2268983
theorem B2519975 : Blo 1678039 2519975 := bstep (se 1 (by rfl) ⟨1889981, by rfl⟩ : syracuseStep 2519975 = 3779963) B3779963
theorem B8500139 : Blo 1678039 8500139 := bstep (se 1 (by rfl) ⟨6375104, by rfl⟩ : syracuseStep 8500139 = 12750209) B12750209
theorem B4248571 : Blo 1678039 4248571 := bstep (se 1 (by rfl) ⟨3186428, by rfl⟩ : syracuseStep 4248571 = 6372857) B6372857
theorem B5665787 : Blo 1678039 5665787 := bstep (se 1 (by rfl) ⟨4249340, by rfl⟩ : syracuseStep 5665787 = 8498681) B8498681
theorem B1889275 : Blo 1678039 1889275 := bstep (se 1 (by rfl) ⟨1416956, by rfl⟩ : syracuseStep 1889275 = 2833913) B2833913
theorem B2520059 : Blo 1678039 2520059 := bstep (se 1 (by rfl) ⟨1890044, by rfl⟩ : syracuseStep 2520059 = 3780089) B3780089
theorem B77583415 : Blo 1678039 77583415 := bstep (se 1 (by rfl) ⟨58187561, by rfl⟩ : syracuseStep 77583415 = 116375123) B116375123
theorem B9557099 : Blo 1678039 9557099 := bstep (se 1 (by rfl) ⟨7167824, by rfl⟩ : syracuseStep 9557099 = 14335649) B14335649
theorem B4248683 : Blo 1678039 4248683 := bstep (se 1 (by rfl) ⟨3186512, by rfl⟩ : syracuseStep 4248683 = 6373025) B6373025
theorem B1889455 : Blo 1678039 1889455 := bstep (se 1 (by rfl) ⟨1417091, by rfl⟩ : syracuseStep 1889455 = 2834183) B2834183
theorem B5666003 : Blo 1678039 5666003 := bstep (se 1 (by rfl) ⟨4249502, by rfl⟩ : syracuseStep 5666003 = 8499005) B8499005
theorem B19928357 : Blo 1678039 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B6378871 : Blo 1678039 6378871 := bstep (se 1 (by rfl) ⟨4784153, by rfl⟩ : syracuseStep 6378871 = 9568307) B9568307
theorem B4249057 : Blo 1678039 4249057 := bstep (se 2 (by rfl) ⟨1593396, by rfl⟩ : syracuseStep 4249057 = 3186793) B3186793
theorem B5666273 : Blo 1678039 5666273 := bstep (se 2 (by rfl) ⟨2124852, by rfl⟩ : syracuseStep 5666273 = 4249705) B4249705
theorem B58963457 : Blo 1678039 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B1889959 : Blo 1678039 1889959 := bstep (se 1 (by rfl) ⟨1417469, by rfl⟩ : syracuseStep 1889959 = 2834939) B2834939
theorem B6461099 : Blo 1678039 6461099 := bstep (se 1 (by rfl) ⟨4845824, by rfl⟩ : syracuseStep 6461099 = 9691649) B9691649
theorem B1914619 : Blo 1678039 1914619 := bstep (se 1 (by rfl) ⟨1435964, by rfl⟩ : syracuseStep 1914619 = 2871929) B2871929
theorem B20428631 : Blo 1678039 20428631 := bstep (se 1 (by rfl) ⟨15321473, by rfl⟩ : syracuseStep 20428631 = 30642947) B30642947
theorem B21510035 : Blo 1678039 21510035 := bstep (se 1 (by rfl) ⟨16132526, by rfl⟩ : syracuseStep 21510035 = 32265053) B32265053
theorem B11483117 : Blo 1678039 11483117 := bstep (se 3 (by rfl) ⟨2153084, by rfl⟩ : syracuseStep 11483117 = 4306169) B4306169
theorem B2832367 : Blo 1678039 2832367 := bstep (se 1 (by rfl) ⟨2124275, by rfl⟩ : syracuseStep 2832367 = 4248551) B4248551
theorem B6051833 : Blo 1678039 6051833 := bstep (se 2 (by rfl) ⟨2269437, by rfl⟩ : syracuseStep 6051833 = 4538875) B4538875
theorem B6051935 : Blo 1678039 6051935 := bstep (se 1 (by rfl) ⟨4538951, by rfl⟩ : syracuseStep 6051935 = 9077903) B9077903
theorem B5666921 : Blo 1678039 5666921 := bstep (se 2 (by rfl) ⟨2125095, by rfl⟩ : syracuseStep 5666921 = 4250191) B4250191
theorem B43604099 : Blo 1678039 43604099 := bstep (se 1 (by rfl) ⟨32703074, by rfl⟩ : syracuseStep 43604099 = 65406149) B65406149
theorem B11491489 : Blo 1678039 11491489 := bstep (se 2 (by rfl) ⟨4309308, by rfl⟩ : syracuseStep 11491489 = 8618617) B8618617
theorem B2832617 : Blo 1678039 2832617 := bstep (se 2 (by rfl) ⟨1062231, by rfl⟩ : syracuseStep 2832617 = 2124463) B2124463
theorem B2390249 : Blo 1678039 2390249 := bstep (se 2 (by rfl) ⟨896343, by rfl⟩ : syracuseStep 2390249 = 1792687) B1792687
theorem B4782377 : Blo 1678039 4782377 := bstep (se 2 (by rfl) ⟨1793391, by rfl⟩ : syracuseStep 4782377 = 3586783) B3586783
theorem B4249979 : Blo 1678039 4249979 := bstep (se 1 (by rfl) ⟨3187484, by rfl⟩ : syracuseStep 4249979 = 6374969) B6374969
theorem B1678171 : Blo 1678039 1678171 := bstep (se 1 (by rfl) ⟨1258628, by rfl⟩ : syracuseStep 1678171 = 2517257) B2517257
theorem B1678239 : Blo 1678039 1678239 := bstep (se 1 (by rfl) ⟨1258679, by rfl⟩ : syracuseStep 1678239 = 2517359) B2517359
theorem B5667785 : Blo 1678039 5667785 := bstep (se 2 (by rfl) ⟨2125419, by rfl⟩ : syracuseStep 5667785 = 4250839) B4250839
theorem B1678383 : Blo 1678039 1678383 := bstep (se 1 (by rfl) ⟨1258787, by rfl⟩ : syracuseStep 1678383 = 2517575) B2517575
theorem B1678407 : Blo 1678039 1678407 := bstep (se 1 (by rfl) ⟨1258805, by rfl⟩ : syracuseStep 1678407 = 2517611) B2517611
theorem B4783175 : Blo 1678039 4783175 := bstep (se 1 (by rfl) ⟨3587381, by rfl⟩ : syracuseStep 4783175 = 7174763) B7174763
theorem B2423929 : Blo 1678039 2423929 := bstep (se 2 (by rfl) ⟨908973, by rfl⟩ : syracuseStep 2423929 = 1817947) B1817947
theorem B7658621 : Blo 1678039 7658621 := bstep (se 3 (by rfl) ⟨1435991, by rfl⟩ : syracuseStep 7658621 = 2871983) B2871983
theorem B2391223 : Blo 1678039 2391223 := bstep (se 1 (by rfl) ⟨1793417, by rfl⟩ : syracuseStep 2391223 = 3586835) B3586835
theorem B5668055 : Blo 1678039 5668055 := bstep (se 1 (by rfl) ⟨4251041, by rfl⟩ : syracuseStep 5668055 = 8502083) B8502083
theorem B1678559 : Blo 1678039 1678559 := bstep (se 1 (by rfl) ⟨1258919, by rfl⟩ : syracuseStep 1678559 = 2517839) B2517839
theorem B1678823 : Blo 1678039 1678823 := bstep (se 1 (by rfl) ⟨1259117, by rfl⟩ : syracuseStep 1678823 = 2518235) B2518235
theorem B1678939 : Blo 1678039 1678939 := bstep (se 1 (by rfl) ⟨1259204, by rfl⟩ : syracuseStep 1678939 = 2518409) B2518409
theorem B2834095 : Blo 1678039 2834095 := bstep (se 1 (by rfl) ⟨2125571, by rfl⟩ : syracuseStep 2834095 = 4251143) B4251143
theorem B5668595 : Blo 1678039 5668595 := bstep (se 1 (by rfl) ⟨4251446, by rfl⟩ : syracuseStep 5668595 = 8502893) B8502893
theorem B19136249 : Blo 1678039 19136249 := bstep (se 2 (by rfl) ⟨7176093, by rfl⟩ : syracuseStep 19136249 = 14352187) B14352187
theorem B3776327 : Blo 1678039 3776327 := bstep (se 1 (by rfl) ⟨2832245, by rfl⟩ : syracuseStep 3776327 = 5664491) B5664491
theorem B1679175 : Blo 1678039 1679175 := bstep (se 1 (by rfl) ⟨1259381, by rfl⟩ : syracuseStep 1679175 = 2518763) B2518763
theorem B24199019 : Blo 1678039 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B1679327 : Blo 1678039 1679327 := bstep (se 1 (by rfl) ⟨1259495, by rfl⟩ : syracuseStep 1679327 = 2518991) B2518991
theorem B2834399 : Blo 1678039 2834399 := bstep (se 1 (by rfl) ⟨2125799, by rfl⟩ : syracuseStep 2834399 = 4251599) B4251599
theorem B6054011 : Blo 1678039 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B1679551 : Blo 1678039 1679551 := bstep (se 1 (by rfl) ⟨1259663, by rfl⟩ : syracuseStep 1679551 = 2519327) B2519327
theorem B9560267 : Blo 1678039 9560267 := bstep (se 1 (by rfl) ⟨7170200, by rfl⟩ : syracuseStep 9560267 = 14340401) B14340401
theorem B1679567 : Blo 1678039 1679567 := bstep (se 1 (by rfl) ⟨1259675, by rfl⟩ : syracuseStep 1679567 = 2519351) B2519351
theorem B1679615 : Blo 1678039 1679615 := bstep (se 1 (by rfl) ⟨1259711, by rfl⟩ : syracuseStep 1679615 = 2519423) B2519423
theorem B1679663 : Blo 1678039 1679663 := bstep (se 1 (by rfl) ⟨1259747, by rfl⟩ : syracuseStep 1679663 = 2519495) B2519495
theorem B6054311 : Blo 1678039 6054311 := bstep (se 1 (by rfl) ⟨4540733, by rfl⟩ : syracuseStep 6054311 = 9081467) B9081467
theorem B27222479 : Blo 1678039 27222479 := bstep (se 1 (by rfl) ⟨20416859, by rfl⟩ : syracuseStep 27222479 = 40833719) B40833719
theorem B1679899 : Blo 1678039 1679899 := bstep (se 1 (by rfl) ⟨1259924, by rfl⟩ : syracuseStep 1679899 = 2519849) B2519849
theorem B1679903 : Blo 1678039 1679903 := bstep (se 1 (by rfl) ⟨1259927, by rfl⟩ : syracuseStep 1679903 = 2519855) B2519855
theorem B8618575 : Blo 1678039 8618575 := bstep (se 1 (by rfl) ⟨6463931, by rfl⟩ : syracuseStep 8618575 = 12927863) B12927863
theorem B11485799 : Blo 1678039 11485799 := bstep (se 1 (by rfl) ⟨8614349, by rfl⟩ : syracuseStep 11485799 = 17228699) B17228699
theorem B6373997 : Blo 1678039 6373997 := bstep (se 3 (by rfl) ⟨1195124, by rfl⟩ : syracuseStep 6373997 = 2390249) B2390249
theorem B1679983 : Blo 1678039 1679983 := bstep (se 1 (by rfl) ⟨1259987, by rfl⟩ : syracuseStep 1679983 = 2519975) B2519975
theorem B3777191 : Blo 1678039 3777191 := bstep (se 1 (by rfl) ⟨2832893, by rfl⟩ : syracuseStep 3777191 = 5665787) B5665787
theorem B1680039 : Blo 1678039 1680039 := bstep (se 1 (by rfl) ⟨1260029, by rfl⟩ : syracuseStep 1680039 = 2520059) B2520059
theorem B3777335 : Blo 1678039 3777335 := bstep (se 1 (by rfl) ⟨2833001, by rfl⟩ : syracuseStep 3777335 = 5666003) B5666003
theorem B3777515 : Blo 1678039 3777515 := bstep (se 1 (by rfl) ⟨2833136, by rfl⟩ : syracuseStep 3777515 = 5666273) B5666273
theorem B3777947 : Blo 1678039 3777947 := bstep (se 1 (by rfl) ⟨2833460, by rfl⟩ : syracuseStep 3777947 = 5666921) B5666921
theorem B3188251 : Blo 1678039 3188251 := bstep (se 1 (by rfl) ⟨2391188, by rfl⟩ : syracuseStep 3188251 = 4782377) B4782377
theorem B3188297 : Blo 1678039 3188297 := bstep (se 2 (by rfl) ⟨1195611, by rfl⟩ : syracuseStep 3188297 = 2391223) B2391223
theorem B8505161 : Blo 1678039 8505161 := bstep (se 2 (by rfl) ⟨3189435, by rfl⟩ : syracuseStep 8505161 = 6378871) B6378871
theorem B3778523 : Blo 1678039 3778523 := bstep (se 1 (by rfl) ⟨2833892, by rfl⟩ : syracuseStep 3778523 = 5667785) B5667785
theorem B6375455 : Blo 1678039 6375455 := bstep (se 1 (by rfl) ⟨4781591, by rfl⟩ : syracuseStep 6375455 = 9563183) B9563183
theorem B3188783 : Blo 1678039 3188783 := bstep (se 1 (by rfl) ⟨2391587, by rfl⟩ : syracuseStep 3188783 = 4783175) B4783175
theorem B5105747 : Blo 1678039 5105747 := bstep (se 1 (by rfl) ⟨3829310, by rfl⟩ : syracuseStep 5105747 = 7658621) B7658621
theorem B2517113 : Blo 1678039 2517113 := bstep (se 2 (by rfl) ⟨943917, by rfl⟩ : syracuseStep 2517113 = 1887835) B1887835
theorem B3778703 : Blo 1678039 3778703 := bstep (se 1 (by rfl) ⟨2834027, by rfl⟩ : syracuseStep 3778703 = 5668055) B5668055
theorem B3778793 : Blo 1678039 3778793 := bstep (se 2 (by rfl) ⟨1417047, by rfl⟩ : syracuseStep 3778793 = 2834095) B2834095
theorem B3779063 : Blo 1678039 3779063 := bstep (se 1 (by rfl) ⟨2834297, by rfl⟩ : syracuseStep 3779063 = 5668595) B5668595
theorem B2517497 : Blo 1678039 2517497 := bstep (se 2 (by rfl) ⟨944061, by rfl⟩ : syracuseStep 2517497 = 1888123) B1888123
theorem B13617659 : Blo 1678039 13617659 := bstep (se 1 (by rfl) ⟨10213244, by rfl⟩ : syracuseStep 13617659 = 20426489) B20426489
theorem B12757499 : Blo 1678039 12757499 := bstep (se 1 (by rfl) ⟨9568124, by rfl⟩ : syracuseStep 12757499 = 19136249) B19136249
theorem B2517551 : Blo 1678039 2517551 := bstep (se 1 (by rfl) ⟨1888163, by rfl⟩ : syracuseStep 2517551 = 3776327) B3776327
theorem B16132679 : Blo 1678039 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B6048371 : Blo 1678039 6048371 := bstep (se 1 (by rfl) ⟨4536278, by rfl⟩ : syracuseStep 6048371 = 9072557) B9072557
theorem B5663627 : Blo 1678039 5663627 := bstep (se 1 (by rfl) ⟨4247720, by rfl⟩ : syracuseStep 5663627 = 8495441) B8495441
theorem B2517983 : Blo 1678039 2517983 := bstep (se 1 (by rfl) ⟨1888487, by rfl⟩ : syracuseStep 2517983 = 3776975) B3776975
theorem B6376427 : Blo 1678039 6376427 := bstep (se 1 (by rfl) ⟨4782320, by rfl⟩ : syracuseStep 6376427 = 9564641) B9564641
theorem B3402793 : Blo 1678039 3402793 := bstep (se 2 (by rfl) ⟨1276047, by rfl⟩ : syracuseStep 3402793 = 2552095) B2552095
theorem B3779657 : Blo 1678039 3779657 := bstep (se 2 (by rfl) ⟨1417371, by rfl⟩ : syracuseStep 3779657 = 2834743) B2834743
theorem B3026089 : Blo 1678039 3026089 := bstep (se 2 (by rfl) ⟨1134783, by rfl⟩ : syracuseStep 3026089 = 2269567) B2269567
theorem B4033747 : Blo 1678039 4033747 := bstep (se 1 (by rfl) ⟨3025310, by rfl⟩ : syracuseStep 4033747 = 6050621) B6050621
theorem B6810905 : Blo 1678039 6810905 := bstep (se 2 (by rfl) ⟨2554089, by rfl⟩ : syracuseStep 6810905 = 5108179) B5108179
theorem B2125111 : Blo 1678039 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B2518427 : Blo 1678039 2518427 := bstep (se 1 (by rfl) ⟨1888820, by rfl⟩ : syracuseStep 2518427 = 3777641) B3777641
theorem B5664167 : Blo 1678039 5664167 := bstep (se 1 (by rfl) ⟨4248125, by rfl⟩ : syracuseStep 5664167 = 8496251) B8496251
theorem B61287941 : Blo 1678039 61287941 := bstep (se 4 (by rfl) ⟨5745744, by rfl⟩ : syracuseStep 61287941 = 11491489) B11491489
theorem B19639853 : Blo 1678039 19639853 := bstep (se 3 (by rfl) ⟨3682472, by rfl⟩ : syracuseStep 19639853 = 7364945) B7364945
theorem B39308971 : Blo 1678039 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B6811361 : Blo 1678039 6811361 := bstep (se 2 (by rfl) ⟨2554260, by rfl⟩ : syracuseStep 6811361 = 5108521) B5108521
theorem B2518847 : Blo 1678039 2518847 := bstep (se 1 (by rfl) ⟨1889135, by rfl⟩ : syracuseStep 2518847 = 3778271) B3778271
theorem B5664599 : Blo 1678039 5664599 := bstep (se 1 (by rfl) ⟨4248449, by rfl⟩ : syracuseStep 5664599 = 8496899) B8496899
theorem B13619087 : Blo 1678039 13619087 := bstep (se 1 (by rfl) ⟨10214315, by rfl⟩ : syracuseStep 13619087 = 20428631) B20428631
theorem B14340023 : Blo 1678039 14340023 := bstep (se 1 (by rfl) ⟨10755017, by rfl⟩ : syracuseStep 14340023 = 21510035) B21510035
theorem B7655411 : Blo 1678039 7655411 := bstep (se 1 (by rfl) ⟨5741558, by rfl⟩ : syracuseStep 7655411 = 11483117) B11483117
theorem B5664761 : Blo 1678039 5664761 := bstep (se 2 (by rfl) ⟨2124285, by rfl⟩ : syracuseStep 5664761 = 4248571) B4248571
theorem B4034555 : Blo 1678039 4034555 := bstep (se 1 (by rfl) ⟨3025916, by rfl⟩ : syracuseStep 4034555 = 6051833) B6051833
theorem B2519033 : Blo 1678039 2519033 := bstep (se 2 (by rfl) ⟨944637, by rfl⟩ : syracuseStep 2519033 = 1889275) B1889275
theorem B4034623 : Blo 1678039 4034623 := bstep (se 1 (by rfl) ⟨3025967, by rfl⟩ : syracuseStep 4034623 = 6051935) B6051935
theorem B103444553 : Blo 1678039 103444553 := bstep (se 2 (by rfl) ⟨38791707, by rfl⟩ : syracuseStep 103444553 = 77583415) B77583415
theorem B3584083 : Blo 1678039 3584083 := bstep (se 1 (by rfl) ⟨2688062, by rfl⟩ : syracuseStep 3584083 = 5376125) B5376125
theorem B29069399 : Blo 1678039 29069399 := bstep (se 1 (by rfl) ⟨21802049, by rfl⟩ : syracuseStep 29069399 = 43604099) B43604099
theorem B1888411 : Blo 1678039 1888411 := bstep (se 1 (by rfl) ⟨1416308, by rfl⟩ : syracuseStep 1888411 = 2832617) B2832617
theorem B3231905 : Blo 1678039 3231905 := bstep (se 2 (by rfl) ⟨1211964, by rfl⟩ : syracuseStep 3231905 = 2423929) B2423929
theorem B2519273 : Blo 1678039 2519273 := bstep (se 2 (by rfl) ⟨944727, by rfl⟩ : syracuseStep 2519273 = 1889455) B1889455
theorem B12742919 : Blo 1678039 12742919 := bstep (se 1 (by rfl) ⟨9557189, by rfl⟩ : syracuseStep 12742919 = 19114379) B19114379
theorem B5665031 : Blo 1678039 5665031 := bstep (se 1 (by rfl) ⟨4248773, by rfl⟩ : syracuseStep 5665031 = 8497547) B8497547
theorem B2519399 : Blo 1678039 2519399 := bstep (se 1 (by rfl) ⟨1889549, by rfl⟩ : syracuseStep 2519399 = 3779099) B3779099
theorem B65442329 : Blo 1678039 65442329 := bstep (se 2 (by rfl) ⟨24540873, by rfl⟩ : syracuseStep 65442329 = 49081747) B49081747
theorem B5665409 : Blo 1678039 5665409 := bstep (se 2 (by rfl) ⟨2124528, by rfl⟩ : syracuseStep 5665409 = 4249057) B4249057
theorem B9073403 : Blo 1678039 9073403 := bstep (se 1 (by rfl) ⟨6805052, by rfl⟩ : syracuseStep 9073403 = 13610105) B13610105
theorem B2519945 : Blo 1678039 2519945 := bstep (se 2 (by rfl) ⟨944979, by rfl⟩ : syracuseStep 2519945 = 1889959) B1889959
theorem B5665679 : Blo 1678039 5665679 := bstep (se 1 (by rfl) ⟨4249259, by rfl⟩ : syracuseStep 5665679 = 8498519) B8498519
theorem B2552825 : Blo 1678039 2552825 := bstep (se 2 (by rfl) ⟨957309, by rfl⟩ : syracuseStep 2552825 = 1914619) B1914619
theorem B4035881 : Blo 1678039 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B5666111 : Blo 1678039 5666111 := bstep (se 1 (by rfl) ⟨4249583, by rfl⟩ : syracuseStep 5666111 = 8499167) B8499167
theorem B4781375 : Blo 1678039 4781375 := bstep (se 1 (by rfl) ⟨3586031, by rfl⟩ : syracuseStep 4781375 = 7172063) B7172063
theorem B1889599 : Blo 1678039 1889599 := bstep (se 1 (by rfl) ⟨1417199, by rfl⟩ : syracuseStep 1889599 = 2834399) B2834399
theorem B5666219 : Blo 1678039 5666219 := bstep (se 1 (by rfl) ⟨4249664, by rfl⟩ : syracuseStep 5666219 = 8499329) B8499329
theorem B4036015 : Blo 1678039 4036015 := bstep (se 1 (by rfl) ⟨3027011, by rfl⟩ : syracuseStep 4036015 = 6054023) B6054023
theorem B7763551 : Blo 1678039 7763551 := bstep (se 1 (by rfl) ⟨5822663, by rfl⟩ : syracuseStep 7763551 = 11645327) B11645327
theorem B3585647 : Blo 1678039 3585647 := bstep (se 1 (by rfl) ⟨2689235, by rfl⟩ : syracuseStep 3585647 = 5378471) B5378471
theorem B1890031 : Blo 1678039 1890031 := bstep (se 1 (by rfl) ⟨1417523, by rfl⟩ : syracuseStep 1890031 = 2835047) B2835047
theorem B9557783 : Blo 1678039 9557783 := bstep (se 1 (by rfl) ⟨7168337, by rfl⟩ : syracuseStep 9557783 = 14336675) B14336675
theorem B21518135 : Blo 1678039 21518135 := bstep (se 1 (by rfl) ⟨16138601, by rfl⟩ : syracuseStep 21518135 = 32277203) B32277203
theorem B5666759 : Blo 1678039 5666759 := bstep (se 1 (by rfl) ⟨4250069, by rfl⟩ : syracuseStep 5666759 = 8500139) B8500139
theorem B6371369 : Blo 1678039 6371369 := bstep (se 2 (by rfl) ⟨2389263, by rfl⟩ : syracuseStep 6371369 = 4778527) B4778527
theorem B6371399 : Blo 1678039 6371399 := bstep (se 1 (by rfl) ⟨4778549, by rfl⟩ : syracuseStep 6371399 = 9557099) B9557099
theorem B2832455 : Blo 1678039 2832455 := bstep (se 1 (by rfl) ⟨2124341, by rfl⟩ : syracuseStep 2832455 = 4248683) B4248683
theorem B13285571 : Blo 1678039 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B4307399 : Blo 1678039 4307399 := bstep (se 1 (by rfl) ⟨3230549, by rfl⟩ : syracuseStep 4307399 = 6461099) B6461099
theorem B215276075 : Blo 1678039 215276075 := bstep (se 1 (by rfl) ⟨161457056, by rfl⟩ : syracuseStep 215276075 = 322914113) B322914113
theorem B18160301 : Blo 1678039 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B1678151 : Blo 1678039 1678151 := bstep (se 1 (by rfl) ⟨1258613, by rfl⟩ : syracuseStep 1678151 = 2517227) B2517227
theorem B1678191 : Blo 1678039 1678191 := bstep (se 1 (by rfl) ⟨1258643, by rfl⟩ : syracuseStep 1678191 = 2517287) B2517287
theorem B1678247 : Blo 1678039 1678247 := bstep (se 1 (by rfl) ⟨1258685, by rfl⟩ : syracuseStep 1678247 = 2517371) B2517371
theorem B2833319 : Blo 1678039 2833319 := bstep (se 1 (by rfl) ⟨2124989, by rfl⟩ : syracuseStep 2833319 = 4249979) B4249979
theorem B1678427 : Blo 1678039 1678427 := bstep (se 1 (by rfl) ⟨1258820, by rfl⟩ : syracuseStep 1678427 = 2517641) B2517641
theorem B1678543 : Blo 1678039 1678543 := bstep (se 1 (by rfl) ⟨1258907, by rfl⟩ : syracuseStep 1678543 = 2517815) B2517815
theorem B1678567 : Blo 1678039 1678567 := bstep (se 1 (by rfl) ⟨1258925, by rfl⟩ : syracuseStep 1678567 = 2517851) B2517851
theorem B1678663 : Blo 1678039 1678663 := bstep (se 1 (by rfl) ⟨1258997, by rfl⟩ : syracuseStep 1678663 = 2517995) B2517995
theorem B1678799 : Blo 1678039 1678799 := bstep (se 1 (by rfl) ⟨1259099, by rfl⟩ : syracuseStep 1678799 = 2518199) B2518199
theorem B4251113 : Blo 1678039 4251113 := bstep (se 2 (by rfl) ⟨1594167, by rfl⟩ : syracuseStep 4251113 = 3188335) B3188335
theorem B12107353 : Blo 1678039 12107353 := bstep (se 2 (by rfl) ⟨4540257, by rfl⟩ : syracuseStep 12107353 = 9080515) B9080515
theorem B1678959 : Blo 1678039 1678959 := bstep (se 1 (by rfl) ⟨1259219, by rfl⟩ : syracuseStep 1678959 = 2518439) B2518439
theorem B1679015 : Blo 1678039 1679015 := bstep (se 1 (by rfl) ⟨1259261, by rfl⟩ : syracuseStep 1679015 = 2518523) B2518523
theorem B3776219 : Blo 1678039 3776219 := bstep (se 1 (by rfl) ⟨2832164, by rfl⟩ : syracuseStep 3776219 = 5664329) B5664329
theorem B1679079 : Blo 1678039 1679079 := bstep (se 1 (by rfl) ⟨1259309, by rfl⟩ : syracuseStep 1679079 = 2518619) B2518619
theorem B1679135 : Blo 1678039 1679135 := bstep (se 1 (by rfl) ⟨1259351, by rfl⟩ : syracuseStep 1679135 = 2518703) B2518703
theorem B1679215 : Blo 1678039 1679215 := bstep (se 1 (by rfl) ⟨1259411, by rfl⟩ : syracuseStep 1679215 = 2518823) B2518823
theorem B1679271 : Blo 1678039 1679271 := bstep (se 1 (by rfl) ⟨1259453, by rfl⟩ : syracuseStep 1679271 = 2518907) B2518907
theorem B3776489 : Blo 1678039 3776489 := bstep (se 2 (by rfl) ⟨1416183, by rfl⟩ : syracuseStep 3776489 = 2832367) B2832367
theorem B6373511 : Blo 1678039 6373511 := bstep (se 1 (by rfl) ⟨4780133, by rfl⟩ : syracuseStep 6373511 = 9560267) B9560267
theorem B1679515 : Blo 1678039 1679515 := bstep (se 1 (by rfl) ⟨1259636, by rfl⟩ : syracuseStep 1679515 = 2519273) B2519273
theorem B8495279 : Blo 1678039 8495279 := bstep (se 1 (by rfl) ⟨6371459, by rfl⟩ : syracuseStep 8495279 = 12742919) B12742919
theorem B3776687 : Blo 1678039 3776687 := bstep (se 1 (by rfl) ⟨2832515, by rfl⟩ : syracuseStep 3776687 = 5665031) B5665031
theorem B1679599 : Blo 1678039 1679599 := bstep (se 1 (by rfl) ⟨1259699, by rfl⟩ : syracuseStep 1679599 = 2519399) B2519399
theorem B3776939 : Blo 1678039 3776939 := bstep (se 1 (by rfl) ⟨2832704, by rfl⟩ : syracuseStep 3776939 = 5665409) B5665409
theorem B8618413 : Blo 1678039 8618413 := bstep (se 3 (by rfl) ⟨1615952, by rfl⟩ : syracuseStep 8618413 = 3231905) B3231905
theorem B1679963 : Blo 1678039 1679963 := bstep (se 1 (by rfl) ⟨1259972, by rfl⟩ : syracuseStep 1679963 = 2519945) B2519945
theorem B3777119 : Blo 1678039 3777119 := bstep (se 1 (by rfl) ⟨2832839, by rfl⟩ : syracuseStep 3777119 = 5665679) B5665679
theorem B18162413 : Blo 1678039 18162413 := bstep (se 3 (by rfl) ⟨3405452, by rfl⟩ : syracuseStep 18162413 = 6810905) B6810905
theorem B3777407 : Blo 1678039 3777407 := bstep (se 1 (by rfl) ⟨2833055, by rfl⟩ : syracuseStep 3777407 = 5666111) B5666111
theorem B3187583 : Blo 1678039 3187583 := bstep (se 1 (by rfl) ⟨2390687, by rfl⟩ : syracuseStep 3187583 = 4781375) B4781375
theorem B3777479 : Blo 1678039 3777479 := bstep (se 1 (by rfl) ⟨2833109, by rfl⟩ : syracuseStep 3777479 = 5666219) B5666219
theorem B14345423 : Blo 1678039 14345423 := bstep (se 1 (by rfl) ⟨10759067, by rfl⟩ : syracuseStep 14345423 = 21518135) B21518135
theorem B5670107 : Blo 1678039 5670107 := bstep (se 1 (by rfl) ⟨4252580, by rfl⟩ : syracuseStep 5670107 = 8505161) B8505161
theorem B3777839 : Blo 1678039 3777839 := bstep (se 1 (by rfl) ⟨2833379, by rfl⟩ : syracuseStep 3777839 = 5666759) B5666759
theorem B9561725 : Blo 1678039 9561725 := bstep (se 3 (by rfl) ⟨1792823, by rfl⟩ : syracuseStep 9561725 = 3585647) B3585647
theorem B9078439 : Blo 1678039 9078439 := bstep (se 1 (by rfl) ⟨6808829, by rfl⟩ : syracuseStep 9078439 = 13617659) B13617659
theorem B8504999 : Blo 1678039 8504999 := bstep (se 1 (by rfl) ⟨6378749, by rfl⟩ : syracuseStep 8504999 = 12757499) B12757499
theorem B143517383 : Blo 1678039 143517383 := bstep (se 1 (by rfl) ⟨107638037, by rfl⟩ : syracuseStep 143517383 = 215276075) B215276075
theorem B13093235 : Blo 1678039 13093235 := bstep (se 1 (by rfl) ⟨9819926, by rfl⟩ : syracuseStep 13093235 = 19639853) B19639853
theorem B2517479 : Blo 1678039 2517479 := bstep (se 1 (by rfl) ⟨1888109, by rfl⟩ : syracuseStep 2517479 = 3776219) B3776219
theorem B4540907 : Blo 1678039 4540907 := bstep (se 1 (by rfl) ⟨3405680, by rfl⟩ : syracuseStep 4540907 = 6811361) B6811361
theorem B9079391 : Blo 1678039 9079391 := bstep (se 1 (by rfl) ⟨6809543, by rfl⟩ : syracuseStep 9079391 = 13619087) B13619087
theorem B2517659 : Blo 1678039 2517659 := bstep (se 1 (by rfl) ⟨1888244, by rfl⟩ : syracuseStep 2517659 = 3776489) B3776489
theorem B2689703 : Blo 1678039 2689703 := bstep (se 1 (by rfl) ⟨2017277, by rfl⟩ : syracuseStep 2689703 = 4034555) B4034555
theorem B4778777 : Blo 1678039 4778777 := bstep (se 2 (by rfl) ⟨1792041, by rfl⟩ : syracuseStep 4778777 = 3584083) B3584083
theorem B275852141 : Blo 1678039 275852141 := bstep (se 3 (by rfl) ⟨51722276, by rfl⟩ : syracuseStep 275852141 = 103444553) B103444553
theorem B2517881 : Blo 1678039 2517881 := bstep (se 2 (by rfl) ⟨944205, by rfl⟩ : syracuseStep 2517881 = 1888411) B1888411
theorem B18148319 : Blo 1678039 18148319 := bstep (se 1 (by rfl) ⟨13611239, by rfl⟩ : syracuseStep 18148319 = 27222479) B27222479
theorem B2518127 : Blo 1678039 2518127 := bstep (se 1 (by rfl) ⟨1888595, by rfl⟩ : syracuseStep 2518127 = 3777191) B3777191
theorem B6048935 : Blo 1678039 6048935 := bstep (se 1 (by rfl) ⟨4536701, by rfl⟩ : syracuseStep 6048935 = 9073403) B9073403
theorem B2518223 : Blo 1678039 2518223 := bstep (se 1 (by rfl) ⟨1888667, by rfl⟩ : syracuseStep 2518223 = 3777335) B3777335
theorem B1679355 : Blo 1678039 1679355 := bstep (se 1 (by rfl) ⟨1259516, by rfl⟩ : syracuseStep 1679355 = 2519033) B2519033
theorem B2518343 : Blo 1678039 2518343 := bstep (se 1 (by rfl) ⟨1888757, by rfl⟩ : syracuseStep 2518343 = 3777515) B3777515
theorem B2690587 : Blo 1678039 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B2518631 : Blo 1678039 2518631 := bstep (se 1 (by rfl) ⟨1888973, by rfl⟩ : syracuseStep 2518631 = 3777947) B3777947
theorem B2125531 : Blo 1678039 2125531 := bstep (se 1 (by rfl) ⟨1594148, by rfl⟩ : syracuseStep 2125531 = 3188297) B3188297
theorem B2519015 : Blo 1678039 2519015 := bstep (se 1 (by rfl) ⟨1889261, by rfl⟩ : syracuseStep 2519015 = 3778523) B3778523
theorem B4247579 : Blo 1678039 4247579 := bstep (se 1 (by rfl) ⟨3185684, by rfl⟩ : syracuseStep 4247579 = 6371369) B6371369
theorem B2125855 : Blo 1678039 2125855 := bstep (se 1 (by rfl) ⟨1594391, by rfl⟩ : syracuseStep 2125855 = 3188783) B3188783
theorem B4247599 : Blo 1678039 4247599 := bstep (se 1 (by rfl) ⟨3185699, by rfl⟩ : syracuseStep 4247599 = 6371399) B6371399
theorem B1888303 : Blo 1678039 1888303 := bstep (se 1 (by rfl) ⟨1416227, by rfl⟩ : syracuseStep 1888303 = 2832455) B2832455
theorem B3403831 : Blo 1678039 3403831 := bstep (se 1 (by rfl) ⟨2552873, by rfl⟩ : syracuseStep 3403831 = 5105747) B5105747
theorem B2519135 : Blo 1678039 2519135 := bstep (se 1 (by rfl) ⟨1889351, by rfl⟩ : syracuseStep 2519135 = 3778703) B3778703
theorem B2519195 : Blo 1678039 2519195 := bstep (se 1 (by rfl) ⟨1889396, by rfl⟩ : syracuseStep 2519195 = 3778793) B3778793
theorem B4034785 : Blo 1678039 4034785 := bstep (se 2 (by rfl) ⟨1513044, by rfl⟩ : syracuseStep 4034785 = 3026089) B3026089
theorem B5378329 : Blo 1678039 5378329 := bstep (se 2 (by rfl) ⟨2016873, by rfl⟩ : syracuseStep 5378329 = 4033747) B4033747
theorem B2871599 : Blo 1678039 2871599 := bstep (se 1 (by rfl) ⟨2153699, by rfl⟩ : syracuseStep 2871599 = 4307399) B4307399
theorem B2519375 : Blo 1678039 2519375 := bstep (se 1 (by rfl) ⟨1889531, by rfl⟩ : syracuseStep 2519375 = 3779063) B3779063
theorem B2519465 : Blo 1678039 2519465 := bstep (se 2 (by rfl) ⟨944799, by rfl⟩ : syracuseStep 2519465 = 1889599) B1889599
theorem B1888879 : Blo 1678039 1888879 := bstep (se 1 (by rfl) ⟨1416659, by rfl⟩ : syracuseStep 1888879 = 2833319) B2833319
theorem B165622421 : Blo 1678039 165622421 := bstep (se 6 (by rfl) ⟨3881775, by rfl⟩ : syracuseStep 165622421 = 7763551) B7763551
theorem B2519771 : Blo 1678039 2519771 := bstep (se 1 (by rfl) ⟨1889828, by rfl⟩ : syracuseStep 2519771 = 3779657) B3779657
theorem B16143137 : Blo 1678039 16143137 := bstep (se 2 (by rfl) ⟨6053676, by rfl⟩ : syracuseStep 16143137 = 12107353) B12107353
theorem B2520041 : Blo 1678039 2520041 := bstep (se 2 (by rfl) ⟨945015, by rfl⟩ : syracuseStep 2520041 = 1890031) B1890031
theorem B40858627 : Blo 1678039 40858627 := bstep (se 1 (by rfl) ⟨30643970, by rfl⟩ : syracuseStep 40858627 = 61287941) B61287941
theorem B4036007 : Blo 1678039 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B5379497 : Blo 1678039 5379497 := bstep (se 2 (by rfl) ⟨2017311, by rfl⟩ : syracuseStep 5379497 = 4034623) B4034623
theorem B77518397 : Blo 1678039 77518397 := bstep (se 3 (by rfl) ⟨14534699, by rfl⟩ : syracuseStep 77518397 = 29069399) B29069399
theorem B43628219 : Blo 1678039 43628219 := bstep (se 1 (by rfl) ⟨32721164, by rfl⟩ : syracuseStep 43628219 = 65442329) B65442329
theorem B7657199 : Blo 1678039 7657199 := bstep (se 1 (by rfl) ⟨5742899, by rfl⟩ : syracuseStep 7657199 = 11485799) B11485799
theorem B4249331 : Blo 1678039 4249331 := bstep (se 1 (by rfl) ⟨3186998, by rfl⟩ : syracuseStep 4249331 = 6373997) B6373997
theorem B1701883 : Blo 1678039 1701883 := bstep (se 1 (by rfl) ⟨1276412, by rfl⟩ : syracuseStep 1701883 = 2552825) B2552825
theorem B11491433 : Blo 1678039 11491433 := bstep (se 2 (by rfl) ⟨4309287, by rfl⟩ : syracuseStep 11491433 = 8618575) B8618575
theorem B16144829 : Blo 1678039 16144829 := bstep (se 3 (by rfl) ⟨3027155, by rfl⟩ : syracuseStep 16144829 = 6054311) B6054311
theorem B6371855 : Blo 1678039 6371855 := bstep (se 1 (by rfl) ⟨4778891, by rfl⟩ : syracuseStep 6371855 = 9557783) B9557783
theorem B4250303 : Blo 1678039 4250303 := bstep (se 1 (by rfl) ⟨3187727, by rfl⟩ : syracuseStep 4250303 = 6375455) B6375455
theorem B4537057 : Blo 1678039 4537057 := bstep (se 2 (by rfl) ⟨1701396, by rfl⟩ : syracuseStep 4537057 = 3402793) B3402793
theorem B1678075 : Blo 1678039 1678075 := bstep (se 1 (by rfl) ⟨1258556, by rfl⟩ : syracuseStep 1678075 = 2517113) B2517113
theorem B16128989 : Blo 1678039 16128989 := bstep (se 3 (by rfl) ⟨3024185, by rfl⟩ : syracuseStep 16128989 = 6048371) B6048371
theorem B1678331 : Blo 1678039 1678331 := bstep (se 1 (by rfl) ⟨1258748, by rfl⟩ : syracuseStep 1678331 = 2517497) B2517497
theorem B1678367 : Blo 1678039 1678367 := bstep (se 1 (by rfl) ⟨1258775, by rfl⟩ : syracuseStep 1678367 = 2517551) B2517551
theorem B10755119 : Blo 1678039 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B2833481 : Blo 1678039 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B12106867 : Blo 1678039 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B5381353 : Blo 1678039 5381353 := bstep (se 2 (by rfl) ⟨2018007, by rfl⟩ : syracuseStep 5381353 = 4036015) B4036015
theorem B3775751 : Blo 1678039 3775751 := bstep (se 1 (by rfl) ⟨2831813, by rfl⟩ : syracuseStep 3775751 = 5663627) B5663627
theorem B1678655 : Blo 1678039 1678655 := bstep (se 1 (by rfl) ⟨1258991, by rfl⟩ : syracuseStep 1678655 = 2517983) B2517983
theorem B4250951 : Blo 1678039 4250951 := bstep (se 1 (by rfl) ⟨3188213, by rfl⟩ : syracuseStep 4250951 = 6376427) B6376427
theorem B141712757 : Blo 1678039 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B4251001 : Blo 1678039 4251001 := bstep (se 2 (by rfl) ⟨1594125, by rfl⟩ : syracuseStep 4251001 = 3188251) B3188251
theorem B52411961 : Blo 1678039 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B1678951 : Blo 1678039 1678951 := bstep (se 1 (by rfl) ⟨1259213, by rfl⟩ : syracuseStep 1678951 = 2518427) B2518427
theorem B3776111 : Blo 1678039 3776111 := bstep (se 1 (by rfl) ⟨2832083, by rfl⟩ : syracuseStep 3776111 = 5664167) B5664167
theorem B2834075 : Blo 1678039 2834075 := bstep (se 1 (by rfl) ⟨2125556, by rfl⟩ : syracuseStep 2834075 = 4251113) B4251113
theorem B1679231 : Blo 1678039 1679231 := bstep (se 1 (by rfl) ⟨1259423, by rfl⟩ : syracuseStep 1679231 = 2518847) B2518847
theorem B3776399 : Blo 1678039 3776399 := bstep (se 1 (by rfl) ⟨2832299, by rfl⟩ : syracuseStep 3776399 = 5664599) B5664599
theorem B9560015 : Blo 1678039 9560015 := bstep (se 1 (by rfl) ⟨7170011, by rfl⟩ : syracuseStep 9560015 = 14340023) B14340023
theorem B20414429 : Blo 1678039 20414429 := bstep (se 3 (by rfl) ⟨3827705, by rfl⟩ : syracuseStep 20414429 = 7655411) B7655411
theorem B3776507 : Blo 1678039 3776507 := bstep (se 1 (by rfl) ⟨2832380, by rfl⟩ : syracuseStep 3776507 = 5664761) B5664761
theorem B2834473 : Blo 1678039 2834473 := bstep (se 2 (by rfl) ⟨1062927, by rfl⟩ : syracuseStep 2834473 = 2125855) B2125855
theorem B1679423 : Blo 1678039 1679423 := bstep (se 1 (by rfl) ⟨1259567, by rfl⟩ : syracuseStep 1679423 = 2519135) B2519135
theorem B4538441 : Blo 1678039 4538441 := bstep (se 2 (by rfl) ⟨1701915, by rfl⟩ : syracuseStep 4538441 = 3403831) B3403831
theorem B1679463 : Blo 1678039 1679463 := bstep (se 1 (by rfl) ⟨1259597, by rfl⟩ : syracuseStep 1679463 = 2519195) B2519195
theorem B28680317 : Blo 1678039 28680317 := bstep (se 3 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 28680317 = 10755119) B10755119
theorem B1679583 : Blo 1678039 1679583 := bstep (se 1 (by rfl) ⟨1259687, by rfl⟩ : syracuseStep 1679583 = 2519375) B2519375
theorem B1679643 : Blo 1678039 1679643 := bstep (se 1 (by rfl) ⟨1259732, by rfl⟩ : syracuseStep 1679643 = 2519465) B2519465
theorem B1679847 : Blo 1678039 1679847 := bstep (se 1 (by rfl) ⟨1259885, by rfl⟩ : syracuseStep 1679847 = 2519771) B2519771
theorem B12108275 : Blo 1678039 12108275 := bstep (se 1 (by rfl) ⟨9081206, by rfl⟩ : syracuseStep 12108275 = 18162413) B18162413
theorem B1680027 : Blo 1678039 1680027 := bstep (se 1 (by rfl) ⟨1260020, by rfl⟩ : syracuseStep 1680027 = 2520041) B2520041
theorem B6374483 : Blo 1678039 6374483 := bstep (se 1 (by rfl) ⟨4780862, by rfl⟩ : syracuseStep 6374483 = 9561725) B9561725
theorem B5669999 : Blo 1678039 5669999 := bstep (se 1 (by rfl) ⟨4252499, by rfl⟩ : syracuseStep 5669999 = 8504999) B8504999
theorem B5104799 : Blo 1678039 5104799 := bstep (se 1 (by rfl) ⟨3828599, by rfl⟩ : syracuseStep 5104799 = 7657199) B7657199
theorem B12109085 : Blo 1678039 12109085 := bstep (se 3 (by rfl) ⟨2270453, by rfl⟩ : syracuseStep 12109085 = 4540907) B4540907
theorem B54478169 : Blo 1678039 54478169 := bstep (se 2 (by rfl) ⟨20429313, by rfl⟩ : syracuseStep 54478169 = 40858627) B40858627
theorem B7660955 : Blo 1678039 7660955 := bstep (se 1 (by rfl) ⟨5745716, by rfl⟩ : syracuseStep 7660955 = 11491433) B11491433
theorem B4032623 : Blo 1678039 4032623 := bstep (se 1 (by rfl) ⟨3024467, by rfl⟩ : syracuseStep 4032623 = 6048935) B6048935
theorem B2517167 : Blo 1678039 2517167 := bstep (se 1 (by rfl) ⟨1887875, by rfl⟩ : syracuseStep 2517167 = 3775751) B3775751
theorem B34941307 : Blo 1678039 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B2517407 : Blo 1678039 2517407 := bstep (se 1 (by rfl) ⟨1888055, by rfl⟩ : syracuseStep 2517407 = 3776111) B3776111
theorem B2517599 : Blo 1678039 2517599 := bstep (se 1 (by rfl) ⟨1888199, by rfl⟩ : syracuseStep 2517599 = 3776399) B3776399
theorem B13609619 : Blo 1678039 13609619 := bstep (se 1 (by rfl) ⟨10207214, by rfl⟩ : syracuseStep 13609619 = 20414429) B20414429
theorem B2517671 : Blo 1678039 2517671 := bstep (se 1 (by rfl) ⟨1888253, by rfl⟩ : syracuseStep 2517671 = 3776507) B3776507
theorem B5663465 : Blo 1678039 5663465 := bstep (se 2 (by rfl) ⟨2123799, by rfl⟩ : syracuseStep 5663465 = 4247599) B4247599
theorem B2517737 : Blo 1678039 2517737 := bstep (se 2 (by rfl) ⟨944151, by rfl⟩ : syracuseStep 2517737 = 1888303) B1888303
theorem B5663519 : Blo 1678039 5663519 := bstep (se 1 (by rfl) ⟨4247639, by rfl⟩ : syracuseStep 5663519 = 8495279) B8495279
theorem B2517791 : Blo 1678039 2517791 := bstep (se 1 (by rfl) ⟨1888343, by rfl⟩ : syracuseStep 2517791 = 3776687) B3776687
theorem B2517959 : Blo 1678039 2517959 := bstep (se 1 (by rfl) ⟨1888469, by rfl⟩ : syracuseStep 2517959 = 3776939) B3776939
theorem B7171105 : Blo 1678039 7171105 := bstep (se 2 (by rfl) ⟨2689164, by rfl⟩ : syracuseStep 7171105 = 5378329) B5378329
theorem B2518079 : Blo 1678039 2518079 := bstep (se 1 (by rfl) ⟨1888559, by rfl⟩ : syracuseStep 2518079 = 3777119) B3777119
theorem B110414947 : Blo 1678039 110414947 := bstep (se 1 (by rfl) ⟨82811210, by rfl⟩ : syracuseStep 110414947 = 165622421) B165622421
theorem B2518271 : Blo 1678039 2518271 := bstep (se 1 (by rfl) ⟨1888703, by rfl⟩ : syracuseStep 2518271 = 3777407) B3777407
theorem B2125055 : Blo 1678039 2125055 := bstep (se 1 (by rfl) ⟨1593791, by rfl⟩ : syracuseStep 2125055 = 3187583) B3187583
theorem B2518319 : Blo 1678039 2518319 := bstep (se 1 (by rfl) ⟨1888739, by rfl⟩ : syracuseStep 2518319 = 3777479) B3777479
theorem B9563615 : Blo 1678039 9563615 := bstep (se 1 (by rfl) ⟨7172711, by rfl⟩ : syracuseStep 9563615 = 14345423) B14345423
theorem B3780071 : Blo 1678039 3780071 := bstep (se 1 (by rfl) ⟨2835053, by rfl⟩ : syracuseStep 3780071 = 5670107) B5670107
theorem B2518505 : Blo 1678039 2518505 := bstep (se 2 (by rfl) ⟨944439, by rfl⟩ : syracuseStep 2518505 = 1888879) B1888879
theorem B2518559 : Blo 1678039 2518559 := bstep (se 1 (by rfl) ⟨1888919, by rfl⟩ : syracuseStep 2518559 = 3777839) B3777839
theorem B2690671 : Blo 1678039 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B6049409 : Blo 1678039 6049409 := bstep (se 2 (by rfl) ⟨2268528, by rfl⟩ : syracuseStep 6049409 = 4537057) B4537057
theorem B51678931 : Blo 1678039 51678931 := bstep (se 1 (by rfl) ⟨38759198, by rfl⟩ : syracuseStep 51678931 = 77518397) B77518397
theorem B29085479 : Blo 1678039 29085479 := bstep (se 1 (by rfl) ⟨21814109, by rfl⟩ : syracuseStep 29085479 = 43628219) B43628219
theorem B95678255 : Blo 1678039 95678255 := bstep (se 1 (by rfl) ⟨71758691, by rfl⟩ : syracuseStep 95678255 = 143517383) B143517383
theorem B16142489 : Blo 1678039 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B8728823 : Blo 1678039 8728823 := bstep (se 1 (by rfl) ⟨6546617, by rfl⟩ : syracuseStep 8728823 = 13093235) B13093235
theorem B24211709 : Blo 1678039 24211709 := bstep (se 3 (by rfl) ⟨4539695, by rfl⟩ : syracuseStep 24211709 = 9079391) B9079391
theorem B4247903 : Blo 1678039 4247903 := bstep (se 1 (by rfl) ⟨3185927, by rfl⟩ : syracuseStep 4247903 = 6371855) B6371855
theorem B10752659 : Blo 1678039 10752659 := bstep (se 1 (by rfl) ⟨8064494, by rfl⟩ : syracuseStep 10752659 = 16128989) B16128989
theorem B1888987 : Blo 1678039 1888987 := bstep (se 1 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 1888987 = 2833481) B2833481
theorem B12743405 : Blo 1678039 12743405 := bstep (se 3 (by rfl) ⟨2389388, by rfl⟩ : syracuseStep 12743405 = 4778777) B4778777
theorem B12104585 : Blo 1678039 12104585 := bstep (se 2 (by rfl) ⟨4539219, by rfl⟩ : syracuseStep 12104585 = 9078439) B9078439
theorem B94475171 : Blo 1678039 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B1889383 : Blo 1678039 1889383 := bstep (se 1 (by rfl) ⟨1417037, by rfl⟩ : syracuseStep 1889383 = 2834075) B2834075
theorem B2831719 : Blo 1678039 2831719 := bstep (se 1 (by rfl) ⟨2123789, by rfl⟩ : syracuseStep 2831719 = 4247579) B4247579
theorem B4249007 : Blo 1678039 4249007 := bstep (se 1 (by rfl) ⟨3186755, by rfl⟩ : syracuseStep 4249007 = 6373511) B6373511
theorem B14349797 : Blo 1678039 14349797 := bstep (se 4 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 14349797 = 2690587) B2690587
theorem B5379713 : Blo 1678039 5379713 := bstep (se 2 (by rfl) ⟨2017392, by rfl⟩ : syracuseStep 5379713 = 4034785) B4034785
theorem B10762091 : Blo 1678039 10762091 := bstep (se 1 (by rfl) ⟨8071568, by rfl⟩ : syracuseStep 10762091 = 16143137) B16143137
theorem B11491217 : Blo 1678039 11491217 := bstep (se 2 (by rfl) ⟨4309206, by rfl⟩ : syracuseStep 11491217 = 8618413) B8618413
theorem B7657597 : Blo 1678039 7657597 := bstep (se 3 (by rfl) ⟨1435799, by rfl⟩ : syracuseStep 7657597 = 2871599) B2871599
theorem B3586331 : Blo 1678039 3586331 := bstep (se 1 (by rfl) ⟨2689748, by rfl⟩ : syracuseStep 3586331 = 5379497) B5379497
theorem B2832887 : Blo 1678039 2832887 := bstep (se 1 (by rfl) ⟨2124665, by rfl⟩ : syracuseStep 2832887 = 4249331) B4249331
theorem B10763219 : Blo 1678039 10763219 := bstep (se 1 (by rfl) ⟨8072414, by rfl⟩ : syracuseStep 10763219 = 16144829) B16144829
theorem B7175137 : Blo 1678039 7175137 := bstep (se 2 (by rfl) ⟨2690676, by rfl⟩ : syracuseStep 7175137 = 5381353) B5381353
theorem B1678319 : Blo 1678039 1678319 := bstep (se 1 (by rfl) ⟨1258739, by rfl⟩ : syracuseStep 1678319 = 2517479) B2517479
theorem B1678439 : Blo 1678039 1678439 := bstep (se 1 (by rfl) ⟨1258829, by rfl⟩ : syracuseStep 1678439 = 2517659) B2517659
theorem B1793135 : Blo 1678039 1793135 := bstep (se 1 (by rfl) ⟨1344851, by rfl⟩ : syracuseStep 1793135 = 2689703) B2689703
theorem B2833535 : Blo 1678039 2833535 := bstep (se 1 (by rfl) ⟨2125151, by rfl⟩ : syracuseStep 2833535 = 4250303) B4250303
theorem B5668001 : Blo 1678039 5668001 := bstep (se 2 (by rfl) ⟨2125500, by rfl⟩ : syracuseStep 5668001 = 4251001) B4251001
theorem B183901427 : Blo 1678039 183901427 := bstep (se 1 (by rfl) ⟨137926070, by rfl⟩ : syracuseStep 183901427 = 275852141) B275852141
theorem B1678587 : Blo 1678039 1678587 := bstep (se 1 (by rfl) ⟨1258940, by rfl⟩ : syracuseStep 1678587 = 2517881) B2517881
theorem B12098879 : Blo 1678039 12098879 := bstep (se 1 (by rfl) ⟨9074159, by rfl⟩ : syracuseStep 12098879 = 18148319) B18148319
theorem B1678751 : Blo 1678039 1678751 := bstep (se 1 (by rfl) ⟨1259063, by rfl⟩ : syracuseStep 1678751 = 2518127) B2518127
theorem B1678815 : Blo 1678039 1678815 := bstep (se 1 (by rfl) ⟨1259111, by rfl⟩ : syracuseStep 1678815 = 2518223) B2518223
theorem B1678895 : Blo 1678039 1678895 := bstep (se 1 (by rfl) ⟨1259171, by rfl⟩ : syracuseStep 1678895 = 2518343) B2518343
theorem B2833967 : Blo 1678039 2833967 := bstep (se 1 (by rfl) ⟨2125475, by rfl⟩ : syracuseStep 2833967 = 4250951) B4250951
theorem B2834041 : Blo 1678039 2834041 := bstep (se 2 (by rfl) ⟨1062765, by rfl⟩ : syracuseStep 2834041 = 2125531) B2125531
theorem B1679087 : Blo 1678039 1679087 := bstep (se 1 (by rfl) ⟨1259315, by rfl⟩ : syracuseStep 1679087 = 2518631) B2518631
theorem B6373343 : Blo 1678039 6373343 := bstep (se 1 (by rfl) ⟨4780007, by rfl⟩ : syracuseStep 6373343 = 9560015) B9560015
theorem B1679343 : Blo 1678039 1679343 := bstep (se 1 (by rfl) ⟨1259507, by rfl⟩ : syracuseStep 1679343 = 2519015) B2519015
theorem B2269177 : Blo 1678039 2269177 := bstep (se 2 (by rfl) ⟨850941, by rfl⟩ : syracuseStep 2269177 = 1701883) B1701883
theorem B19120211 : Blo 1678039 19120211 := bstep (se 1 (by rfl) ⟨14340158, by rfl⟩ : syracuseStep 19120211 = 28680317) B28680317
theorem B7168439 : Blo 1678039 7168439 := bstep (se 1 (by rfl) ⟨5376329, by rfl⟩ : syracuseStep 7168439 = 10752659) B10752659
theorem B8495603 : Blo 1678039 8495603 := bstep (se 1 (by rfl) ⟨6371702, by rfl⟩ : syracuseStep 8495603 = 12743405) B12743405
theorem B46588409 : Blo 1678039 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B8069723 : Blo 1678039 8069723 := bstep (se 1 (by rfl) ⟨6052292, by rfl⟩ : syracuseStep 8069723 = 12104585) B12104585
theorem B7660811 : Blo 1678039 7660811 := bstep (se 1 (by rfl) ⟨5745608, by rfl⟩ : syracuseStep 7660811 = 11491217) B11491217
theorem B9561473 : Blo 1678039 9561473 := bstep (se 2 (by rfl) ⟨3585552, by rfl⟩ : syracuseStep 9561473 = 7171105) B7171105
theorem B147219929 : Blo 1678039 147219929 := bstep (se 2 (by rfl) ⟨55207473, by rfl⟩ : syracuseStep 147219929 = 110414947) B110414947
theorem B16131757 : Blo 1678039 16131757 := bstep (se 3 (by rfl) ⟨3024704, by rfl⟩ : syracuseStep 16131757 = 6049409) B6049409
theorem B3778667 : Blo 1678039 3778667 := bstep (se 1 (by rfl) ⟨2834000, by rfl⟩ : syracuseStep 3778667 = 5668001) B5668001
theorem B3778721 : Blo 1678039 3778721 := bstep (se 2 (by rfl) ⟨1417020, by rfl⟩ : syracuseStep 3778721 = 2834041) B2834041
theorem B68905241 : Blo 1678039 68905241 := bstep (se 2 (by rfl) ⟨25839465, by rfl⟩ : syracuseStep 68905241 = 51678931) B51678931
theorem B6375743 : Blo 1678039 6375743 := bstep (se 1 (by rfl) ⟨4781807, by rfl⟩ : syracuseStep 6375743 = 9563615) B9563615
theorem B48409109 : Blo 1678039 48409109 := bstep (se 6 (by rfl) ⟨1134588, by rfl⟩ : syracuseStep 48409109 = 2269177) B2269177
theorem B63785503 : Blo 1678039 63785503 := bstep (se 1 (by rfl) ⟨47839127, by rfl⟩ : syracuseStep 63785503 = 95678255) B95678255
theorem B3779297 : Blo 1678039 3779297 := bstep (se 2 (by rfl) ⟨1417236, by rfl⟩ : syracuseStep 3779297 = 2834473) B2834473
theorem B5819215 : Blo 1678039 5819215 := bstep (se 1 (by rfl) ⟨4364411, by rfl⟩ : syracuseStep 5819215 = 8728823) B8728823
theorem B16141139 : Blo 1678039 16141139 := bstep (se 1 (by rfl) ⟨12105854, by rfl⟩ : syracuseStep 16141139 = 24211709) B24211709
theorem B12102509 : Blo 1678039 12102509 := bstep (se 3 (by rfl) ⟨2269220, by rfl⟩ : syracuseStep 12102509 = 4538441) B4538441
theorem B8072183 : Blo 1678039 8072183 := bstep (se 1 (by rfl) ⟨6054137, by rfl⟩ : syracuseStep 8072183 = 12108275) B12108275
theorem B40840517 : Blo 1678039 40840517 := bstep (se 4 (by rfl) ⟨3828798, by rfl⟩ : syracuseStep 40840517 = 7657597) B7657597
theorem B3779999 : Blo 1678039 3779999 := bstep (se 1 (by rfl) ⟨2834999, by rfl⟩ : syracuseStep 3779999 = 5669999) B5669999
theorem B3403199 : Blo 1678039 3403199 := bstep (se 1 (by rfl) ⟨2552399, by rfl⟩ : syracuseStep 3403199 = 5104799) B5104799
theorem B8072723 : Blo 1678039 8072723 := bstep (se 1 (by rfl) ⟨6054542, by rfl⟩ : syracuseStep 8072723 = 12109085) B12109085
theorem B36318779 : Blo 1678039 36318779 := bstep (se 1 (by rfl) ⟨27239084, by rfl⟩ : syracuseStep 36318779 = 54478169) B54478169
theorem B5107303 : Blo 1678039 5107303 := bstep (se 1 (by rfl) ⟨3830477, by rfl⟩ : syracuseStep 5107303 = 7660955) B7660955
theorem B2518649 : Blo 1678039 2518649 := bstep (se 2 (by rfl) ⟨944493, by rfl⟩ : syracuseStep 2518649 = 1888987) B1888987
theorem B2519177 : Blo 1678039 2519177 := bstep (se 2 (by rfl) ⟨944691, by rfl⟩ : syracuseStep 2519177 = 1889383) B1889383
theorem B1888591 : Blo 1678039 1888591 := bstep (se 1 (by rfl) ⟨1416443, by rfl⟩ : syracuseStep 1888591 = 2832887) B2832887
theorem B9073079 : Blo 1678039 9073079 := bstep (se 1 (by rfl) ⟨6804809, by rfl⟩ : syracuseStep 9073079 = 13609619) B13609619
theorem B1889023 : Blo 1678039 1889023 := bstep (se 1 (by rfl) ⟨1416767, by rfl⟩ : syracuseStep 1889023 = 2833535) B2833535
theorem B8065919 : Blo 1678039 8065919 := bstep (se 1 (by rfl) ⟨6049439, by rfl⟩ : syracuseStep 8065919 = 12098879) B12098879
theorem B2520047 : Blo 1678039 2520047 := bstep (se 1 (by rfl) ⟨1890035, by rfl⟩ : syracuseStep 2520047 = 3780071) B3780071
theorem B1889311 : Blo 1678039 1889311 := bstep (se 1 (by rfl) ⟨1416983, by rfl⟩ : syracuseStep 1889311 = 2833967) B2833967
theorem B251933789 : Blo 1678039 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B4248895 : Blo 1678039 4248895 := bstep (se 1 (by rfl) ⟨3186671, by rfl⟩ : syracuseStep 4248895 = 6373343) B6373343
theorem B10761659 : Blo 1678039 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B2831935 : Blo 1678039 2831935 := bstep (se 1 (by rfl) ⟨2123951, by rfl⟩ : syracuseStep 2831935 = 4247903) B4247903
theorem B10753661 : Blo 1678039 10753661 := bstep (se 3 (by rfl) ⟨2016311, by rfl⟩ : syracuseStep 10753661 = 4032623) B4032623
theorem B4781693 : Blo 1678039 4781693 := bstep (se 3 (by rfl) ⟨896567, by rfl⟩ : syracuseStep 4781693 = 1793135) B1793135
theorem B5666813 : Blo 1678039 5666813 := bstep (se 3 (by rfl) ⟨1062527, by rfl⟩ : syracuseStep 5666813 = 2125055) B2125055
theorem B4249655 : Blo 1678039 4249655 := bstep (se 1 (by rfl) ⟨3187241, by rfl⟩ : syracuseStep 4249655 = 6374483) B6374483
theorem B2832671 : Blo 1678039 2832671 := bstep (se 1 (by rfl) ⟨2124503, by rfl⟩ : syracuseStep 2832671 = 4249007) B4249007
theorem B9566531 : Blo 1678039 9566531 := bstep (se 1 (by rfl) ⟨7174898, by rfl⟩ : syracuseStep 9566531 = 14349797) B14349797
theorem B3586475 : Blo 1678039 3586475 := bstep (se 1 (by rfl) ⟨2689856, by rfl⟩ : syracuseStep 3586475 = 5379713) B5379713
theorem B7174727 : Blo 1678039 7174727 := bstep (se 1 (by rfl) ⟨5381045, by rfl⟩ : syracuseStep 7174727 = 10762091) B10762091
theorem B9566849 : Blo 1678039 9566849 := bstep (se 2 (by rfl) ⟨3587568, by rfl⟩ : syracuseStep 9566849 = 7175137) B7175137
theorem B1678111 : Blo 1678039 1678111 := bstep (se 1 (by rfl) ⟨1258583, by rfl⟩ : syracuseStep 1678111 = 2517167) B2517167
theorem B2390887 : Blo 1678039 2390887 := bstep (se 1 (by rfl) ⟨1793165, by rfl⟩ : syracuseStep 2390887 = 3586331) B3586331
theorem B1678271 : Blo 1678039 1678271 := bstep (se 1 (by rfl) ⟨1258703, by rfl⟩ : syracuseStep 1678271 = 2517407) B2517407
theorem B1678399 : Blo 1678039 1678399 := bstep (se 1 (by rfl) ⟨1258799, by rfl⟩ : syracuseStep 1678399 = 2517599) B2517599
theorem B1678447 : Blo 1678039 1678447 := bstep (se 1 (by rfl) ⟨1258835, by rfl⟩ : syracuseStep 1678447 = 2517671) B2517671
theorem B3775625 : Blo 1678039 3775625 := bstep (se 2 (by rfl) ⟨1415859, by rfl⟩ : syracuseStep 3775625 = 2831719) B2831719
theorem B3775643 : Blo 1678039 3775643 := bstep (se 1 (by rfl) ⟨2831732, by rfl⟩ : syracuseStep 3775643 = 5663465) B5663465
theorem B1678491 : Blo 1678039 1678491 := bstep (se 1 (by rfl) ⟨1258868, by rfl⟩ : syracuseStep 1678491 = 2517737) B2517737
theorem B3775679 : Blo 1678039 3775679 := bstep (se 1 (by rfl) ⟨2831759, by rfl⟩ : syracuseStep 3775679 = 5663519) B5663519
theorem B1678527 : Blo 1678039 1678527 := bstep (se 1 (by rfl) ⟨1258895, by rfl⟩ : syracuseStep 1678527 = 2517791) B2517791
theorem B1678639 : Blo 1678039 1678639 := bstep (se 1 (by rfl) ⟨1258979, by rfl⟩ : syracuseStep 1678639 = 2517959) B2517959
theorem B7175479 : Blo 1678039 7175479 := bstep (se 1 (by rfl) ⟨5381609, by rfl⟩ : syracuseStep 7175479 = 10763219) B10763219
theorem B1678719 : Blo 1678039 1678719 := bstep (se 1 (by rfl) ⟨1259039, by rfl⟩ : syracuseStep 1678719 = 2518079) B2518079
theorem B3587561 : Blo 1678039 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B122600951 : Blo 1678039 122600951 := bstep (se 1 (by rfl) ⟨91950713, by rfl⟩ : syracuseStep 122600951 = 183901427) B183901427
theorem B1678847 : Blo 1678039 1678847 := bstep (se 1 (by rfl) ⟨1259135, by rfl⟩ : syracuseStep 1678847 = 2518271) B2518271
theorem B1678879 : Blo 1678039 1678879 := bstep (se 1 (by rfl) ⟨1259159, by rfl⟩ : syracuseStep 1678879 = 2518319) B2518319
theorem B1679003 : Blo 1678039 1679003 := bstep (se 1 (by rfl) ⟨1259252, by rfl⟩ : syracuseStep 1679003 = 2518505) B2518505
theorem B1679039 : Blo 1678039 1679039 := bstep (se 1 (by rfl) ⟨1259279, by rfl⟩ : syracuseStep 1679039 = 2518559) B2518559
theorem B19390319 : Blo 1678039 19390319 := bstep (se 1 (by rfl) ⟨14542739, by rfl⟩ : syracuseStep 19390319 = 29085479) B29085479
theorem B12746807 : Blo 1678039 12746807 := bstep (se 1 (by rfl) ⟨9560105, by rfl⟩ : syracuseStep 12746807 = 19120211) B19120211
theorem B1679451 : Blo 1678039 1679451 := bstep (se 1 (by rfl) ⟨1259588, by rfl⟩ : syracuseStep 1679451 = 2519177) B2519177
theorem B27238949 : Blo 1678039 27238949 := bstep (se 4 (by rfl) ⟨2553651, by rfl⟩ : syracuseStep 27238949 = 5107303) B5107303
theorem B1680031 : Blo 1678039 1680031 := bstep (se 1 (by rfl) ⟨1260023, by rfl⟩ : syracuseStep 1680031 = 2520047) B2520047
theorem B6374315 : Blo 1678039 6374315 := bstep (se 1 (by rfl) ⟨4780736, by rfl⟩ : syracuseStep 6374315 = 9561473) B9561473
theorem B7169107 : Blo 1678039 7169107 := bstep (se 1 (by rfl) ⟨5376830, by rfl⟩ : syracuseStep 7169107 = 10753661) B10753661
theorem B7758953 : Blo 1678039 7758953 := bstep (se 2 (by rfl) ⟨2909607, by rfl⟩ : syracuseStep 7758953 = 5819215) B5819215
theorem B3187849 : Blo 1678039 3187849 := bstep (se 2 (by rfl) ⟨1195443, by rfl⟩ : syracuseStep 3187849 = 2390887) B2390887
theorem B3777875 : Blo 1678039 3777875 := bstep (se 1 (by rfl) ⟨2833406, by rfl⟩ : syracuseStep 3777875 = 5666813) B5666813
theorem B2517083 : Blo 1678039 2517083 := bstep (se 1 (by rfl) ⟨1887812, by rfl⟩ : syracuseStep 2517083 = 3775625) B3775625
theorem B2517095 : Blo 1678039 2517095 := bstep (se 1 (by rfl) ⟨1887821, by rfl⟩ : syracuseStep 2517095 = 3775643) B3775643
theorem B2517119 : Blo 1678039 2517119 := bstep (se 1 (by rfl) ⟨1887839, by rfl⟩ : syracuseStep 2517119 = 3775679) B3775679
theorem B81733967 : Blo 1678039 81733967 := bstep (se 1 (by rfl) ⟨61300475, by rfl⟩ : syracuseStep 81733967 = 122600951) B122600951
theorem B6048719 : Blo 1678039 6048719 := bstep (se 1 (by rfl) ⟨4536539, by rfl⟩ : syracuseStep 6048719 = 9073079) B9073079
theorem B5663735 : Blo 1678039 5663735 := bstep (se 1 (by rfl) ⟨4247801, by rfl⟩ : syracuseStep 5663735 = 8495603) B8495603
theorem B31058939 : Blo 1678039 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B2518121 : Blo 1678039 2518121 := bstep (se 2 (by rfl) ⟨944295, by rfl⟩ : syracuseStep 2518121 = 1888591) B1888591
theorem B5377279 : Blo 1678039 5377279 := bstep (se 1 (by rfl) ⟨4032959, by rfl⟩ : syracuseStep 5377279 = 8065919) B8065919
theorem B167955859 : Blo 1678039 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B5107207 : Blo 1678039 5107207 := bstep (se 1 (by rfl) ⟨3830405, by rfl⟩ : syracuseStep 5107207 = 7660811) B7660811
theorem B2518697 : Blo 1678039 2518697 := bstep (se 2 (by rfl) ⟨944511, by rfl⟩ : syracuseStep 2518697 = 1889023) B1889023
theorem B9563933 : Blo 1678039 9563933 := bstep (se 3 (by rfl) ⟨1793237, by rfl⟩ : syracuseStep 9563933 = 3586475) B3586475
theorem B19115837 : Blo 1678039 19115837 := bstep (se 3 (by rfl) ⟨3584219, by rfl⟩ : syracuseStep 19115837 = 7168439) B7168439
theorem B2519081 : Blo 1678039 2519081 := bstep (se 2 (by rfl) ⟨944655, by rfl⟩ : syracuseStep 2519081 = 1889311) B1889311
theorem B2519111 : Blo 1678039 2519111 := bstep (se 1 (by rfl) ⟨1889333, by rfl⟩ : syracuseStep 2519111 = 3778667) B3778667
theorem B2519147 : Blo 1678039 2519147 := bstep (se 1 (by rfl) ⟨1889360, by rfl⟩ : syracuseStep 2519147 = 3778721) B3778721
theorem B45936827 : Blo 1678039 45936827 := bstep (se 1 (by rfl) ⟨34452620, by rfl⟩ : syracuseStep 45936827 = 68905241) B68905241
theorem B1888447 : Blo 1678039 1888447 := bstep (se 1 (by rfl) ⟨1416335, by rfl⟩ : syracuseStep 1888447 = 2832671) B2832671
theorem B6377687 : Blo 1678039 6377687 := bstep (se 1 (by rfl) ⟨4783265, by rfl⟩ : syracuseStep 6377687 = 9566531) B9566531
theorem B12751181 : Blo 1678039 12751181 := bstep (se 3 (by rfl) ⟨2390846, by rfl⟩ : syracuseStep 12751181 = 4781693) B4781693
theorem B32272739 : Blo 1678039 32272739 := bstep (se 1 (by rfl) ⟨24204554, by rfl⟩ : syracuseStep 32272739 = 48409109) B48409109
theorem B5665193 : Blo 1678039 5665193 := bstep (se 2 (by rfl) ⟨2124447, by rfl⟩ : syracuseStep 5665193 = 4248895) B4248895
theorem B6377899 : Blo 1678039 6377899 := bstep (se 1 (by rfl) ⟨4783424, by rfl⟩ : syracuseStep 6377899 = 9566849) B9566849
theorem B2519531 : Blo 1678039 2519531 := bstep (se 1 (by rfl) ⟨1889648, by rfl⟩ : syracuseStep 2519531 = 3779297) B3779297
theorem B10760759 : Blo 1678039 10760759 := bstep (se 1 (by rfl) ⟨8070569, by rfl⟩ : syracuseStep 10760759 = 16141139) B16141139
theorem B27227011 : Blo 1678039 27227011 := bstep (se 1 (by rfl) ⟨20420258, by rfl⟩ : syracuseStep 27227011 = 40840517) B40840517
theorem B21509009 : Blo 1678039 21509009 := bstep (se 2 (by rfl) ⟨8065878, by rfl⟩ : syracuseStep 21509009 = 16131757) B16131757
theorem B2519999 : Blo 1678039 2519999 := bstep (se 1 (by rfl) ⟨1889999, by rfl⟩ : syracuseStep 2519999 = 3779999) B3779999
theorem B24212519 : Blo 1678039 24212519 := bstep (se 1 (by rfl) ⟨18159389, by rfl⟩ : syracuseStep 24212519 = 36318779) B36318779
theorem B21525821 : Blo 1678039 21525821 := bstep (se 3 (by rfl) ⟨4036091, by rfl⟩ : syracuseStep 21525821 = 8072183) B8072183
theorem B5379815 : Blo 1678039 5379815 := bstep (se 1 (by rfl) ⟨4034861, by rfl⟩ : syracuseStep 5379815 = 8069723) B8069723
theorem B85047337 : Blo 1678039 85047337 := bstep (se 2 (by rfl) ⟨31892751, by rfl⟩ : syracuseStep 85047337 = 63785503) B63785503
theorem B7174439 : Blo 1678039 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B98146619 : Blo 1678039 98146619 := bstep (se 1 (by rfl) ⟨73609964, by rfl⟩ : syracuseStep 98146619 = 147219929) B147219929
theorem B2833103 : Blo 1678039 2833103 := bstep (se 1 (by rfl) ⟨2124827, by rfl⟩ : syracuseStep 2833103 = 4249655) B4249655
theorem B4250495 : Blo 1678039 4250495 := bstep (se 1 (by rfl) ⟨3187871, by rfl⟩ : syracuseStep 4250495 = 6375743) B6375743
theorem B4783151 : Blo 1678039 4783151 := bstep (se 1 (by rfl) ⟨3587363, by rfl⟩ : syracuseStep 4783151 = 7174727) B7174727
theorem B9567305 : Blo 1678039 9567305 := bstep (se 2 (by rfl) ⟨3587739, by rfl⟩ : syracuseStep 9567305 = 7175479) B7175479
theorem B8068339 : Blo 1678039 8068339 := bstep (se 1 (by rfl) ⟨6051254, by rfl⟩ : syracuseStep 8068339 = 12102509) B12102509
theorem B3775913 : Blo 1678039 3775913 := bstep (se 2 (by rfl) ⟨1415967, by rfl⟩ : syracuseStep 3775913 = 2831935) B2831935
theorem B2268799 : Blo 1678039 2268799 := bstep (se 1 (by rfl) ⟨1701599, by rfl⟩ : syracuseStep 2268799 = 3403199) B3403199
theorem B2391707 : Blo 1678039 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B5381815 : Blo 1678039 5381815 := bstep (se 1 (by rfl) ⟨4036361, by rfl⟩ : syracuseStep 5381815 = 8072723) B8072723
theorem B1679099 : Blo 1678039 1679099 := bstep (se 1 (by rfl) ⟨1259324, by rfl⟩ : syracuseStep 1679099 = 2518649) B2518649
theorem B12926879 : Blo 1678039 12926879 := bstep (se 1 (by rfl) ⟨9695159, by rfl⟩ : syracuseStep 12926879 = 19390319) B19390319
theorem B1679387 : Blo 1678039 1679387 := bstep (se 1 (by rfl) ⟨1259540, by rfl⟩ : syracuseStep 1679387 = 2519081) B2519081
theorem B1679407 : Blo 1678039 1679407 := bstep (se 1 (by rfl) ⟨1259555, by rfl⟩ : syracuseStep 1679407 = 2519111) B2519111
theorem B1679431 : Blo 1678039 1679431 := bstep (se 1 (by rfl) ⟨1259573, by rfl⟩ : syracuseStep 1679431 = 2519147) B2519147
theorem B12755069 : Blo 1678039 12755069 := bstep (se 3 (by rfl) ⟨2391575, by rfl⟩ : syracuseStep 12755069 = 4783151) B4783151
theorem B4251791 : Blo 1678039 4251791 := bstep (se 1 (by rfl) ⟨3188843, by rfl⟩ : syracuseStep 4251791 = 6377687) B6377687
theorem B3776795 : Blo 1678039 3776795 := bstep (se 1 (by rfl) ⟨2832596, by rfl⟩ : syracuseStep 3776795 = 5665193) B5665193
theorem B1679687 : Blo 1678039 1679687 := bstep (se 1 (by rfl) ⟨1259765, by rfl⟩ : syracuseStep 1679687 = 2519531) B2519531
theorem B8503865 : Blo 1678039 8503865 := bstep (se 2 (by rfl) ⟨3188949, by rfl⟩ : syracuseStep 8503865 = 6377899) B6377899
theorem B1679999 : Blo 1678039 1679999 := bstep (se 1 (by rfl) ⟨1259999, by rfl⟩ : syracuseStep 1679999 = 2519999) B2519999
theorem B12100261 : Blo 1678039 12100261 := bstep (se 4 (by rfl) ⟨1134399, by rfl⟩ : syracuseStep 12100261 = 2268799) B2268799
theorem B65431079 : Blo 1678039 65431079 := bstep (se 1 (by rfl) ⟨49073309, by rfl⟩ : syracuseStep 65431079 = 98146619) B98146619
theorem B10757785 : Blo 1678039 10757785 := bstep (se 2 (by rfl) ⟨4034169, by rfl⟩ : syracuseStep 10757785 = 8068339) B8068339
theorem B7169705 : Blo 1678039 7169705 := bstep (se 2 (by rfl) ⟨2688639, by rfl⟩ : syracuseStep 7169705 = 5377279) B5377279
theorem B14346173 : Blo 1678039 14346173 := bstep (se 3 (by rfl) ⟨2689907, by rfl⟩ : syracuseStep 14346173 = 5379815) B5379815
theorem B4032479 : Blo 1678039 4032479 := bstep (se 1 (by rfl) ⟨3024359, by rfl⟩ : syracuseStep 4032479 = 6048719) B6048719
theorem B6809609 : Blo 1678039 6809609 := bstep (se 2 (by rfl) ⟨2553603, by rfl⟩ : syracuseStep 6809609 = 5107207) B5107207
theorem B2517275 : Blo 1678039 2517275 := bstep (se 1 (by rfl) ⟨1887956, by rfl⟩ : syracuseStep 2517275 = 3775913) B3775913
theorem B6375955 : Blo 1678039 6375955 := bstep (se 1 (by rfl) ⟨4781966, by rfl⟩ : syracuseStep 6375955 = 9563933) B9563933
theorem B8497871 : Blo 1678039 8497871 := bstep (se 1 (by rfl) ⟨6373403, by rfl⟩ : syracuseStep 8497871 = 12746807) B12746807
theorem B113396449 : Blo 1678039 113396449 := bstep (se 2 (by rfl) ⟨42523668, by rfl⟩ : syracuseStep 113396449 = 85047337) B85047337
theorem B30624551 : Blo 1678039 30624551 := bstep (se 1 (by rfl) ⟨22968413, by rfl⟩ : syracuseStep 30624551 = 45936827) B45936827
theorem B21515159 : Blo 1678039 21515159 := bstep (se 1 (by rfl) ⟨16136369, by rfl⟩ : syracuseStep 21515159 = 32272739) B32272739
theorem B2517929 : Blo 1678039 2517929 := bstep (se 2 (by rfl) ⟨944223, by rfl⟩ : syracuseStep 2517929 = 1888447) B1888447
theorem B14339339 : Blo 1678039 14339339 := bstep (se 1 (by rfl) ⟨10754504, by rfl⟩ : syracuseStep 14339339 = 21509009) B21509009
theorem B16141679 : Blo 1678039 16141679 := bstep (se 1 (by rfl) ⟨12106259, by rfl⟩ : syracuseStep 16141679 = 24212519) B24212519
theorem B5172635 : Blo 1678039 5172635 := bstep (se 1 (by rfl) ⟨3879476, by rfl⟩ : syracuseStep 5172635 = 7758953) B7758953
theorem B2518583 : Blo 1678039 2518583 := bstep (se 1 (by rfl) ⟨1888937, by rfl⟩ : syracuseStep 2518583 = 3777875) B3777875
theorem B36302681 : Blo 1678039 36302681 := bstep (se 2 (by rfl) ⟨13613505, by rfl⟩ : syracuseStep 36302681 = 27227011) B27227011
theorem B54489311 : Blo 1678039 54489311 := bstep (se 1 (by rfl) ⟨40866983, by rfl⟩ : syracuseStep 54489311 = 81733967) B81733967
theorem B6377885 : Blo 1678039 6377885 := bstep (se 3 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 6377885 = 2391707) B2391707
theorem B1888735 : Blo 1678039 1888735 := bstep (se 1 (by rfl) ⟨1416551, by rfl⟩ : syracuseStep 1888735 = 2833103) B2833103
theorem B223941145 : Blo 1678039 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B20705959 : Blo 1678039 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B6378203 : Blo 1678039 6378203 := bstep (se 1 (by rfl) ⟨4783652, by rfl⟩ : syracuseStep 6378203 = 9567305) B9567305
theorem B12743891 : Blo 1678039 12743891 := bstep (se 1 (by rfl) ⟨9557918, by rfl⟩ : syracuseStep 12743891 = 19115837) B19115837
theorem B8500787 : Blo 1678039 8500787 := bstep (se 1 (by rfl) ⟨6375590, by rfl⟩ : syracuseStep 8500787 = 12751181) B12751181
theorem B18159299 : Blo 1678039 18159299 := bstep (se 1 (by rfl) ⟨13619474, by rfl⟩ : syracuseStep 18159299 = 27238949) B27238949
theorem B7173839 : Blo 1678039 7173839 := bstep (se 1 (by rfl) ⟨5380379, by rfl⟩ : syracuseStep 7173839 = 10760759) B10760759
theorem B4249543 : Blo 1678039 4249543 := bstep (se 1 (by rfl) ⟨3187157, by rfl⟩ : syracuseStep 4249543 = 6374315) B6374315
theorem B14350547 : Blo 1678039 14350547 := bstep (se 1 (by rfl) ⟨10762910, by rfl⟩ : syracuseStep 14350547 = 21525821) B21525821
theorem B1678055 : Blo 1678039 1678055 := bstep (se 1 (by rfl) ⟨1258541, by rfl⟩ : syracuseStep 1678055 = 2517083) B2517083
theorem B1678063 : Blo 1678039 1678063 := bstep (se 1 (by rfl) ⟨1258547, by rfl⟩ : syracuseStep 1678063 = 2517095) B2517095
theorem B1678079 : Blo 1678039 1678079 := bstep (se 1 (by rfl) ⟨1258559, by rfl⟩ : syracuseStep 1678079 = 2517119) B2517119
theorem B9558809 : Blo 1678039 9558809 := bstep (se 2 (by rfl) ⟨3584553, by rfl⟩ : syracuseStep 9558809 = 7169107) B7169107
theorem B4250465 : Blo 1678039 4250465 := bstep (se 2 (by rfl) ⟨1593924, by rfl⟩ : syracuseStep 4250465 = 3187849) B3187849
theorem B4782959 : Blo 1678039 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B2833663 : Blo 1678039 2833663 := bstep (se 1 (by rfl) ⟨2125247, by rfl⟩ : syracuseStep 2833663 = 4250495) B4250495
theorem B3775823 : Blo 1678039 3775823 := bstep (se 1 (by rfl) ⟨2831867, by rfl⟩ : syracuseStep 3775823 = 5663735) B5663735
theorem B1678747 : Blo 1678039 1678747 := bstep (se 1 (by rfl) ⟨1259060, by rfl⟩ : syracuseStep 1678747 = 2518121) B2518121
theorem B7175753 : Blo 1678039 7175753 := bstep (se 2 (by rfl) ⟨2690907, by rfl⟩ : syracuseStep 7175753 = 5381815) B5381815
theorem B1679131 : Blo 1678039 1679131 := bstep (se 1 (by rfl) ⟨1259348, by rfl⟩ : syracuseStep 1679131 = 2518697) B2518697
theorem B8617919 : Blo 1678039 8617919 := bstep (se 1 (by rfl) ⟨6463439, by rfl⟩ : syracuseStep 8617919 = 12926879) B12926879
theorem B8503379 : Blo 1678039 8503379 := bstep (se 1 (by rfl) ⟨6377534, by rfl⟩ : syracuseStep 8503379 = 12755069) B12755069
theorem B2834527 : Blo 1678039 2834527 := bstep (se 1 (by rfl) ⟨2125895, by rfl⟩ : syracuseStep 2834527 = 4251791) B4251791
theorem B4251923 : Blo 1678039 4251923 := bstep (se 1 (by rfl) ⟨3188942, by rfl⟩ : syracuseStep 4251923 = 6377885) B6377885
theorem B5669243 : Blo 1678039 5669243 := bstep (se 1 (by rfl) ⟨4251932, by rfl⟩ : syracuseStep 5669243 = 8503865) B8503865
theorem B4252135 : Blo 1678039 4252135 := bstep (se 1 (by rfl) ⟨3189101, by rfl⟩ : syracuseStep 4252135 = 6378203) B6378203
theorem B8495927 : Blo 1678039 8495927 := bstep (se 1 (by rfl) ⟨6371945, by rfl⟩ : syracuseStep 8495927 = 12743891) B12743891
theorem B27607945 : Blo 1678039 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B2688319 : Blo 1678039 2688319 := bstep (se 1 (by rfl) ⟨2016239, by rfl⟩ : syracuseStep 2688319 = 4032479) B4032479
theorem B4539739 : Blo 1678039 4539739 := bstep (se 1 (by rfl) ⟨3404804, by rfl⟩ : syracuseStep 4539739 = 6809609) B6809609
theorem B3778217 : Blo 1678039 3778217 := bstep (se 2 (by rfl) ⟨1416831, by rfl⟩ : syracuseStep 3778217 = 2833663) B2833663
theorem B20416367 : Blo 1678039 20416367 := bstep (se 1 (by rfl) ⟨15312275, by rfl⟩ : syracuseStep 20416367 = 30624551) B30624551
theorem B3188639 : Blo 1678039 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B2517215 : Blo 1678039 2517215 := bstep (se 1 (by rfl) ⟨1887911, by rfl⟩ : syracuseStep 2517215 = 3775823) B3775823
theorem B22981117 : Blo 1678039 22981117 := bstep (se 3 (by rfl) ⟨4308959, by rfl⟩ : syracuseStep 22981117 = 8617919) B8617919
theorem B24201787 : Blo 1678039 24201787 := bstep (se 1 (by rfl) ⟨18151340, by rfl⟩ : syracuseStep 24201787 = 36302681) B36302681
theorem B36326207 : Blo 1678039 36326207 := bstep (se 1 (by rfl) ⟨27244655, by rfl⟩ : syracuseStep 36326207 = 54489311) B54489311
theorem B2517863 : Blo 1678039 2517863 := bstep (se 1 (by rfl) ⟨1888397, by rfl⟩ : syracuseStep 2517863 = 3776795) B3776795
theorem B2518313 : Blo 1678039 2518313 := bstep (se 2 (by rfl) ⟨944367, by rfl⟩ : syracuseStep 2518313 = 1888735) B1888735
theorem B16133681 : Blo 1678039 16133681 := bstep (se 2 (by rfl) ⟨6050130, by rfl⟩ : syracuseStep 16133681 = 12100261) B12100261
theorem B151195265 : Blo 1678039 151195265 := bstep (se 2 (by rfl) ⟨56698224, by rfl⟩ : syracuseStep 151195265 = 113396449) B113396449
theorem B4779803 : Blo 1678039 4779803 := bstep (se 1 (by rfl) ⟨3584852, by rfl⟩ : syracuseStep 4779803 = 7169705) B7169705
theorem B9564115 : Blo 1678039 9564115 := bstep (se 1 (by rfl) ⟨7173086, by rfl⟩ : syracuseStep 9564115 = 14346173) B14346173
theorem B5665247 : Blo 1678039 5665247 := bstep (se 1 (by rfl) ⟨4248935, by rfl⟩ : syracuseStep 5665247 = 8497871) B8497871
theorem B10761119 : Blo 1678039 10761119 := bstep (se 1 (by rfl) ⟨8070839, by rfl⟩ : syracuseStep 10761119 = 16141679) B16141679
theorem B5666057 : Blo 1678039 5666057 := bstep (se 2 (by rfl) ⟨2124771, by rfl⟩ : syracuseStep 5666057 = 4249543) B4249543
theorem B8501273 : Blo 1678039 8501273 := bstep (se 2 (by rfl) ⟨3187977, by rfl⟩ : syracuseStep 8501273 = 6375955) B6375955
theorem B298588193 : Blo 1678039 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B43620719 : Blo 1678039 43620719 := bstep (se 1 (by rfl) ⟨32715539, by rfl⟩ : syracuseStep 43620719 = 65431079) B65431079
theorem B5667191 : Blo 1678039 5667191 := bstep (se 1 (by rfl) ⟨4250393, by rfl⟩ : syracuseStep 5667191 = 8500787) B8500787
theorem B12106199 : Blo 1678039 12106199 := bstep (se 1 (by rfl) ⟨9079649, by rfl⟩ : syracuseStep 12106199 = 18159299) B18159299
theorem B4782559 : Blo 1678039 4782559 := bstep (se 1 (by rfl) ⟨3586919, by rfl⟩ : syracuseStep 4782559 = 7173839) B7173839
theorem B9567031 : Blo 1678039 9567031 := bstep (se 1 (by rfl) ⟨7175273, by rfl⟩ : syracuseStep 9567031 = 14350547) B14350547
theorem B1678183 : Blo 1678039 1678183 := bstep (se 1 (by rfl) ⟨1258637, by rfl⟩ : syracuseStep 1678183 = 2517275) B2517275
theorem B6372539 : Blo 1678039 6372539 := bstep (se 1 (by rfl) ⟨4779404, by rfl⟩ : syracuseStep 6372539 = 9558809) B9558809
theorem B2833643 : Blo 1678039 2833643 := bstep (se 1 (by rfl) ⟨2125232, by rfl⟩ : syracuseStep 2833643 = 4250465) B4250465
theorem B14343439 : Blo 1678039 14343439 := bstep (se 1 (by rfl) ⟨10757579, by rfl⟩ : syracuseStep 14343439 = 21515159) B21515159
theorem B1678619 : Blo 1678039 1678619 := bstep (se 1 (by rfl) ⟨1258964, by rfl⟩ : syracuseStep 1678619 = 2517929) B2517929
theorem B9559559 : Blo 1678039 9559559 := bstep (se 1 (by rfl) ⟨7169669, by rfl⟩ : syracuseStep 9559559 = 14339339) B14339339
theorem B14343713 : Blo 1678039 14343713 := bstep (se 2 (by rfl) ⟨5378892, by rfl⟩ : syracuseStep 14343713 = 10757785) B10757785
theorem B3448423 : Blo 1678039 3448423 := bstep (se 1 (by rfl) ⟨2586317, by rfl⟩ : syracuseStep 3448423 = 5172635) B5172635
theorem B1679055 : Blo 1678039 1679055 := bstep (se 1 (by rfl) ⟨1259291, by rfl⟩ : syracuseStep 1679055 = 2518583) B2518583
theorem B4783835 : Blo 1678039 4783835 := bstep (se 1 (by rfl) ⟨3587876, by rfl⟩ : syracuseStep 4783835 = 7175753) B7175753
theorem B5668919 : Blo 1678039 5668919 := bstep (se 1 (by rfl) ⟨4251689, by rfl⟩ : syracuseStep 5668919 = 8503379) B8503379
theorem B2834615 : Blo 1678039 2834615 := bstep (se 1 (by rfl) ⟨2125961, by rfl⟩ : syracuseStep 2834615 = 4251923) B4251923
theorem B3776831 : Blo 1678039 3776831 := bstep (se 1 (by rfl) ⟨2832623, by rfl⟩ : syracuseStep 3776831 = 5665247) B5665247
theorem B5669513 : Blo 1678039 5669513 := bstep (se 2 (by rfl) ⟨2126067, by rfl⟩ : syracuseStep 5669513 = 4252135) B4252135
theorem B32269049 : Blo 1678039 32269049 := bstep (se 2 (by rfl) ⟨12100893, by rfl⟩ : syracuseStep 32269049 = 24201787) B24201787
theorem B3777371 : Blo 1678039 3777371 := bstep (se 1 (by rfl) ⟨2833028, by rfl⟩ : syracuseStep 3777371 = 5666057) B5666057
theorem B12756041 : Blo 1678039 12756041 := bstep (se 2 (by rfl) ⟨4783515, by rfl⟩ : syracuseStep 12756041 = 9567031) B9567031
theorem B199058795 : Blo 1678039 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B3778127 : Blo 1678039 3778127 := bstep (se 1 (by rfl) ⟨2833595, by rfl⟩ : syracuseStep 3778127 = 5667191) B5667191
theorem B24217471 : Blo 1678039 24217471 := bstep (se 1 (by rfl) ⟨18163103, by rfl⟩ : syracuseStep 24217471 = 36326207) B36326207
theorem B4597897 : Blo 1678039 4597897 := bstep (se 2 (by rfl) ⟨1724211, by rfl⟩ : syracuseStep 4597897 = 3448423) B3448423
theorem B9562475 : Blo 1678039 9562475 := bstep (se 1 (by rfl) ⟨7171856, by rfl⟩ : syracuseStep 9562475 = 14343713) B14343713
theorem B100796843 : Blo 1678039 100796843 := bstep (se 1 (by rfl) ⟨75597632, by rfl⟩ : syracuseStep 100796843 = 151195265) B151195265
theorem B3189223 : Blo 1678039 3189223 := bstep (se 1 (by rfl) ⟨2391917, by rfl⟩ : syracuseStep 3189223 = 4783835) B4783835
theorem B3779369 : Blo 1678039 3779369 := bstep (se 2 (by rfl) ⟨1417263, by rfl⟩ : syracuseStep 3779369 = 2834527) B2834527
theorem B3779495 : Blo 1678039 3779495 := bstep (se 1 (by rfl) ⟨2834621, by rfl⟩ : syracuseStep 3779495 = 5669243) B5669243
theorem B5663951 : Blo 1678039 5663951 := bstep (se 1 (by rfl) ⟨4247963, by rfl⟩ : syracuseStep 5663951 = 8495927) B8495927
theorem B6376745 : Blo 1678039 6376745 := bstep (se 2 (by rfl) ⟨2391279, by rfl⟩ : syracuseStep 6376745 = 4782559) B4782559
theorem B30641489 : Blo 1678039 30641489 := bstep (se 2 (by rfl) ⟨11490558, by rfl⟩ : syracuseStep 30641489 = 22981117) B22981117
theorem B116321917 : Blo 1678039 116321917 := bstep (se 3 (by rfl) ⟨21810359, by rfl⟩ : syracuseStep 116321917 = 43620719) B43620719
theorem B2518811 : Blo 1678039 2518811 := bstep (se 1 (by rfl) ⟨1889108, by rfl⟩ : syracuseStep 2518811 = 3778217) B3778217
theorem B36810593 : Blo 1678039 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B13610911 : Blo 1678039 13610911 := bstep (se 1 (by rfl) ⟨10208183, by rfl⟩ : syracuseStep 13610911 = 20416367) B20416367
theorem B2125759 : Blo 1678039 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B19124585 : Blo 1678039 19124585 := bstep (se 2 (by rfl) ⟨7171719, by rfl⟩ : syracuseStep 19124585 = 14343439) B14343439
theorem B3584425 : Blo 1678039 3584425 := bstep (se 2 (by rfl) ⟨1344159, by rfl⟩ : syracuseStep 3584425 = 2688319) B2688319
theorem B4248359 : Blo 1678039 4248359 := bstep (se 1 (by rfl) ⟨3186269, by rfl⟩ : syracuseStep 4248359 = 6372539) B6372539
theorem B1889095 : Blo 1678039 1889095 := bstep (se 1 (by rfl) ⟨1416821, by rfl⟩ : syracuseStep 1889095 = 2833643) B2833643
theorem B12752153 : Blo 1678039 12752153 := bstep (se 2 (by rfl) ⟨4782057, by rfl⟩ : syracuseStep 12752153 = 9564115) B9564115
theorem B7174079 : Blo 1678039 7174079 := bstep (se 1 (by rfl) ⟨5380559, by rfl⟩ : syracuseStep 7174079 = 10761119) B10761119
theorem B32283197 : Blo 1678039 32283197 := bstep (se 3 (by rfl) ⟨6053099, by rfl⟩ : syracuseStep 32283197 = 12106199) B12106199
theorem B5667515 : Blo 1678039 5667515 := bstep (se 1 (by rfl) ⟨4250636, by rfl⟩ : syracuseStep 5667515 = 8501273) B8501273
theorem B1678143 : Blo 1678039 1678143 := bstep (se 1 (by rfl) ⟨1258607, by rfl⟩ : syracuseStep 1678143 = 2517215) B2517215
theorem B6052985 : Blo 1678039 6052985 := bstep (se 2 (by rfl) ⟨2269869, by rfl⟩ : syracuseStep 6052985 = 4539739) B4539739
theorem B1678575 : Blo 1678039 1678575 := bstep (se 1 (by rfl) ⟨1258931, by rfl⟩ : syracuseStep 1678575 = 2517863) B2517863
theorem B1678875 : Blo 1678039 1678875 := bstep (se 1 (by rfl) ⟨1259156, by rfl⟩ : syracuseStep 1678875 = 2518313) B2518313
theorem B6373039 : Blo 1678039 6373039 := bstep (se 1 (by rfl) ⟨4779779, by rfl⟩ : syracuseStep 6373039 = 9559559) B9559559
theorem B10755787 : Blo 1678039 10755787 := bstep (se 1 (by rfl) ⟨8066840, by rfl⟩ : syracuseStep 10755787 = 16133681) B16133681
theorem B3186535 : Blo 1678039 3186535 := bstep (se 1 (by rfl) ⟨2389901, by rfl⟩ : syracuseStep 3186535 = 4779803) B4779803
theorem B21512699 : Blo 1678039 21512699 := bstep (se 1 (by rfl) ⟨16134524, by rfl⟩ : syracuseStep 21512699 = 32269049) B32269049
theorem B4252297 : Blo 1678039 4252297 := bstep (se 2 (by rfl) ⟨1594611, by rfl⟩ : syracuseStep 4252297 = 3189223) B3189223
theorem B8504027 : Blo 1678039 8504027 := bstep (se 1 (by rfl) ⟨6378020, by rfl⟩ : syracuseStep 8504027 = 12756041) B12756041
theorem B6374983 : Blo 1678039 6374983 := bstep (se 1 (by rfl) ⟨4781237, by rfl⟩ : syracuseStep 6374983 = 9562475) B9562475
theorem B21522131 : Blo 1678039 21522131 := bstep (se 1 (by rfl) ⟨16141598, by rfl⟩ : syracuseStep 21522131 = 32283197) B32283197
theorem B3778343 : Blo 1678039 3778343 := bstep (se 1 (by rfl) ⟨2833757, by rfl⟩ : syracuseStep 3778343 = 5667515) B5667515
theorem B8497385 : Blo 1678039 8497385 := bstep (se 2 (by rfl) ⟨3186519, by rfl⟩ : syracuseStep 8497385 = 6373039) B6373039
theorem B18147881 : Blo 1678039 18147881 := bstep (se 2 (by rfl) ⟨6805455, by rfl⟩ : syracuseStep 18147881 = 13610911) B13610911
theorem B3779279 : Blo 1678039 3779279 := bstep (se 1 (by rfl) ⟨2834459, by rfl⟩ : syracuseStep 3779279 = 5668919) B5668919
theorem B6130529 : Blo 1678039 6130529 := bstep (se 2 (by rfl) ⟨2298948, by rfl⟩ : syracuseStep 6130529 = 4597897) B4597897
theorem B2517887 : Blo 1678039 2517887 := bstep (se 1 (by rfl) ⟨1888415, by rfl⟩ : syracuseStep 2517887 = 3776831) B3776831
theorem B12749723 : Blo 1678039 12749723 := bstep (se 1 (by rfl) ⟨9562292, by rfl⟩ : syracuseStep 12749723 = 19124585) B19124585
theorem B3779675 : Blo 1678039 3779675 := bstep (se 1 (by rfl) ⟨2834756, by rfl⟩ : syracuseStep 3779675 = 5669513) B5669513
theorem B4779233 : Blo 1678039 4779233 := bstep (se 2 (by rfl) ⟨1792212, by rfl⟩ : syracuseStep 4779233 = 3584425) B3584425
theorem B2518247 : Blo 1678039 2518247 := bstep (se 1 (by rfl) ⟨1888685, by rfl⟩ : syracuseStep 2518247 = 3777371) B3777371
theorem B132705863 : Blo 1678039 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B2518751 : Blo 1678039 2518751 := bstep (se 1 (by rfl) ⟨1889063, by rfl⟩ : syracuseStep 2518751 = 3778127) B3778127
theorem B2518793 : Blo 1678039 2518793 := bstep (se 2 (by rfl) ⟨944547, by rfl⟩ : syracuseStep 2518793 = 1889095) B1889095
theorem B2519579 : Blo 1678039 2519579 := bstep (se 1 (by rfl) ⟨1889684, by rfl⟩ : syracuseStep 2519579 = 3779369) B3779369
theorem B2519663 : Blo 1678039 2519663 := bstep (se 1 (by rfl) ⟨1889747, by rfl⟩ : syracuseStep 2519663 = 3779495) B3779495
theorem B4035323 : Blo 1678039 4035323 := bstep (se 1 (by rfl) ⟨3026492, by rfl⟩ : syracuseStep 4035323 = 6052985) B6052985
theorem B155095889 : Blo 1678039 155095889 := bstep (se 2 (by rfl) ⟨58160958, by rfl⟩ : syracuseStep 155095889 = 116321917) B116321917
theorem B20427659 : Blo 1678039 20427659 := bstep (se 1 (by rfl) ⟨15320744, by rfl⟩ : syracuseStep 20427659 = 30641489) B30641489
theorem B14341049 : Blo 1678039 14341049 := bstep (se 2 (by rfl) ⟨5377893, by rfl⟩ : syracuseStep 14341049 = 10755787) B10755787
theorem B4248713 : Blo 1678039 4248713 := bstep (se 2 (by rfl) ⟨1593267, by rfl⟩ : syracuseStep 4248713 = 3186535) B3186535
theorem B32289961 : Blo 1678039 32289961 := bstep (se 2 (by rfl) ⟨12108735, by rfl⟩ : syracuseStep 32289961 = 24217471) B24217471
theorem B24540395 : Blo 1678039 24540395 := bstep (se 1 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 24540395 = 36810593) B36810593
theorem B1889743 : Blo 1678039 1889743 := bstep (se 1 (by rfl) ⟨1417307, by rfl⟩ : syracuseStep 1889743 = 2834615) B2834615
theorem B2832239 : Blo 1678039 2832239 := bstep (se 1 (by rfl) ⟨2124179, by rfl⟩ : syracuseStep 2832239 = 4248359) B4248359
theorem B8501435 : Blo 1678039 8501435 := bstep (se 1 (by rfl) ⟨6376076, by rfl⟩ : syracuseStep 8501435 = 12752153) B12752153
theorem B4782719 : Blo 1678039 4782719 := bstep (se 1 (by rfl) ⟨3587039, by rfl⟩ : syracuseStep 4782719 = 7174079) B7174079
theorem B67197895 : Blo 1678039 67197895 := bstep (se 1 (by rfl) ⟨50398421, by rfl⟩ : syracuseStep 67197895 = 100796843) B100796843
theorem B3775967 : Blo 1678039 3775967 := bstep (se 1 (by rfl) ⟨2831975, by rfl⟩ : syracuseStep 3775967 = 5663951) B5663951
theorem B4251163 : Blo 1678039 4251163 := bstep (se 1 (by rfl) ⟨3188372, by rfl⟩ : syracuseStep 4251163 = 6376745) B6376745
theorem B1679207 : Blo 1678039 1679207 := bstep (se 1 (by rfl) ⟨1259405, by rfl⟩ : syracuseStep 1679207 = 2518811) B2518811
theorem B2834345 : Blo 1678039 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B1679719 : Blo 1678039 1679719 := bstep (se 1 (by rfl) ⟨1259789, by rfl⟩ : syracuseStep 1679719 = 2519579) B2519579
theorem B1679775 : Blo 1678039 1679775 := bstep (se 1 (by rfl) ⟨1259831, by rfl⟩ : syracuseStep 1679775 = 2519663) B2519663
theorem B5669351 : Blo 1678039 5669351 := bstep (se 1 (by rfl) ⟨4252013, by rfl⟩ : syracuseStep 5669351 = 8504027) B8504027
theorem B9560699 : Blo 1678039 9560699 := bstep (se 1 (by rfl) ⟨7170524, by rfl⟩ : syracuseStep 9560699 = 14341049) B14341049
theorem B5669729 : Blo 1678039 5669729 := bstep (se 2 (by rfl) ⟨2126148, by rfl⟩ : syracuseStep 5669729 = 4252297) B4252297
theorem B3188479 : Blo 1678039 3188479 := bstep (se 1 (by rfl) ⟨2391359, by rfl⟩ : syracuseStep 3188479 = 4782719) B4782719
theorem B2517311 : Blo 1678039 2517311 := bstep (se 1 (by rfl) ⟨1887983, by rfl⟩ : syracuseStep 2517311 = 3775967) B3775967
theorem B2690215 : Blo 1678039 2690215 := bstep (se 1 (by rfl) ⟨2017661, by rfl⟩ : syracuseStep 2690215 = 4035323) B4035323
theorem B13618439 : Blo 1678039 13618439 := bstep (se 1 (by rfl) ⟨10213829, by rfl⟩ : syracuseStep 13618439 = 20427659) B20427659
theorem B65441053 : Blo 1678039 65441053 := bstep (se 3 (by rfl) ⟨12270197, by rfl⟩ : syracuseStep 65441053 = 24540395) B24540395
theorem B14348087 : Blo 1678039 14348087 := bstep (se 1 (by rfl) ⟨10761065, by rfl⟩ : syracuseStep 14348087 = 21522131) B21522131
theorem B2518895 : Blo 1678039 2518895 := bstep (se 1 (by rfl) ⟨1889171, by rfl⟩ : syracuseStep 2518895 = 3778343) B3778343
theorem B1888159 : Blo 1678039 1888159 := bstep (se 1 (by rfl) ⟨1416119, by rfl⟩ : syracuseStep 1888159 = 2832239) B2832239
theorem B1433555093 : Blo 1678039 1433555093 := bstep (se 6 (by rfl) ⟨33598947, by rfl⟩ : syracuseStep 1433555093 = 67197895) B67197895
theorem B5664923 : Blo 1678039 5664923 := bstep (se 1 (by rfl) ⟨4248692, by rfl⟩ : syracuseStep 5664923 = 8497385) B8497385
theorem B43053281 : Blo 1678039 43053281 := bstep (se 2 (by rfl) ⟨16144980, by rfl⟩ : syracuseStep 43053281 = 32289961) B32289961
theorem B2519519 : Blo 1678039 2519519 := bstep (se 1 (by rfl) ⟨1889639, by rfl⟩ : syracuseStep 2519519 = 3779279) B3779279
theorem B8499815 : Blo 1678039 8499815 := bstep (se 1 (by rfl) ⟨6374861, by rfl⟩ : syracuseStep 8499815 = 12749723) B12749723
theorem B2519657 : Blo 1678039 2519657 := bstep (se 2 (by rfl) ⟨944871, by rfl⟩ : syracuseStep 2519657 = 1889743) B1889743
theorem B2519783 : Blo 1678039 2519783 := bstep (se 1 (by rfl) ⟨1889837, by rfl⟩ : syracuseStep 2519783 = 3779675) B3779675
theorem B8499977 : Blo 1678039 8499977 := bstep (se 2 (by rfl) ⟨3187491, by rfl⟩ : syracuseStep 8499977 = 6374983) B6374983
theorem B88470575 : Blo 1678039 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B1889563 : Blo 1678039 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B14341799 : Blo 1678039 14341799 := bstep (se 1 (by rfl) ⟨10756349, by rfl⟩ : syracuseStep 14341799 = 21512699) B21512699
theorem B2832475 : Blo 1678039 2832475 := bstep (se 1 (by rfl) ⟨2124356, by rfl⟩ : syracuseStep 2832475 = 4248713) B4248713
theorem B5667623 : Blo 1678039 5667623 := bstep (se 1 (by rfl) ⟨4250717, by rfl⟩ : syracuseStep 5667623 = 8501435) B8501435
theorem B12098587 : Blo 1678039 12098587 := bstep (se 1 (by rfl) ⟨9073940, by rfl⟩ : syracuseStep 12098587 = 18147881) B18147881
theorem B4087019 : Blo 1678039 4087019 := bstep (se 1 (by rfl) ⟨3065264, by rfl⟩ : syracuseStep 4087019 = 6130529) B6130529
theorem B1678591 : Blo 1678039 1678591 := bstep (se 1 (by rfl) ⟨1258943, by rfl⟩ : syracuseStep 1678591 = 2517887) B2517887
theorem B5668217 : Blo 1678039 5668217 := bstep (se 2 (by rfl) ⟨2125581, by rfl⟩ : syracuseStep 5668217 = 4251163) B4251163
theorem B3186155 : Blo 1678039 3186155 := bstep (se 1 (by rfl) ⟨2389616, by rfl⟩ : syracuseStep 3186155 = 4779233) B4779233
theorem B1678831 : Blo 1678039 1678831 := bstep (se 1 (by rfl) ⟨1259123, by rfl⟩ : syracuseStep 1678831 = 2518247) B2518247
theorem B413589037 : Blo 1678039 413589037 := bstep (se 3 (by rfl) ⟨77547944, by rfl⟩ : syracuseStep 413589037 = 155095889) B155095889
theorem B1679167 : Blo 1678039 1679167 := bstep (se 1 (by rfl) ⟨1259375, by rfl⟩ : syracuseStep 1679167 = 2518751) B2518751
theorem B1679195 : Blo 1678039 1679195 := bstep (se 1 (by rfl) ⟨1259396, by rfl⟩ : syracuseStep 1679195 = 2518793) B2518793
theorem B955703395 : Blo 1678039 955703395 := bstep (se 1 (by rfl) ⟨716777546, by rfl⟩ : syracuseStep 955703395 = 1433555093) B1433555093
theorem B3776615 : Blo 1678039 3776615 := bstep (se 1 (by rfl) ⟨2832461, by rfl⟩ : syracuseStep 3776615 = 5664923) B5664923
theorem B3776633 : Blo 1678039 3776633 := bstep (se 2 (by rfl) ⟨1416237, by rfl⟩ : syracuseStep 3776633 = 2832475) B2832475
theorem B1679679 : Blo 1678039 1679679 := bstep (se 1 (by rfl) ⟨1259759, by rfl⟩ : syracuseStep 1679679 = 2519519) B2519519
theorem B1679771 : Blo 1678039 1679771 := bstep (se 1 (by rfl) ⟨1259828, by rfl⟩ : syracuseStep 1679771 = 2519657) B2519657
theorem B6373799 : Blo 1678039 6373799 := bstep (se 1 (by rfl) ⟨4780349, by rfl⟩ : syracuseStep 6373799 = 9560699) B9560699
theorem B1679855 : Blo 1678039 1679855 := bstep (se 1 (by rfl) ⟨1259891, by rfl⟩ : syracuseStep 1679855 = 2519783) B2519783
theorem B9561199 : Blo 1678039 9561199 := bstep (se 1 (by rfl) ⟨7170899, by rfl⟩ : syracuseStep 9561199 = 14341799) B14341799
theorem B8496413 : Blo 1678039 8496413 := bstep (se 3 (by rfl) ⟨1593077, by rfl⟩ : syracuseStep 8496413 = 3186155) B3186155
theorem B16131449 : Blo 1678039 16131449 := bstep (se 2 (by rfl) ⟨6049293, by rfl⟩ : syracuseStep 16131449 = 12098587) B12098587
theorem B3778415 : Blo 1678039 3778415 := bstep (se 1 (by rfl) ⟨2833811, by rfl⟩ : syracuseStep 3778415 = 5667623) B5667623
theorem B9078959 : Blo 1678039 9078959 := bstep (se 1 (by rfl) ⟨6809219, by rfl⟩ : syracuseStep 9078959 = 13618439) B13618439
theorem B3778811 : Blo 1678039 3778811 := bstep (se 1 (by rfl) ⟨2834108, by rfl⟩ : syracuseStep 3778811 = 5668217) B5668217
theorem B2517545 : Blo 1678039 2517545 := bstep (se 2 (by rfl) ⟨944079, by rfl⟩ : syracuseStep 2517545 = 1888159) B1888159
theorem B3779567 : Blo 1678039 3779567 := bstep (se 1 (by rfl) ⟨2834675, by rfl⟩ : syracuseStep 3779567 = 5669351) B5669351
theorem B3779819 : Blo 1678039 3779819 := bstep (se 1 (by rfl) ⟨2834864, by rfl⟩ : syracuseStep 3779819 = 5669729) B5669729
theorem B14347813 : Blo 1678039 14347813 := bstep (se 4 (by rfl) ⟨1345107, by rfl⟩ : syracuseStep 14347813 = 2690215) B2690215
theorem B2519417 : Blo 1678039 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B2724679 : Blo 1678039 2724679 := bstep (se 1 (by rfl) ⟨2043509, by rfl⟩ : syracuseStep 2724679 = 4087019) B4087019
theorem B9565391 : Blo 1678039 9565391 := bstep (se 1 (by rfl) ⟨7174043, by rfl⟩ : syracuseStep 9565391 = 14348087) B14348087
theorem B28702187 : Blo 1678039 28702187 := bstep (se 1 (by rfl) ⟨21526640, by rfl⟩ : syracuseStep 28702187 = 43053281) B43053281
theorem B5666543 : Blo 1678039 5666543 := bstep (se 1 (by rfl) ⟨4249907, by rfl⟩ : syracuseStep 5666543 = 8499815) B8499815
theorem B5666651 : Blo 1678039 5666651 := bstep (se 1 (by rfl) ⟨4249988, by rfl⟩ : syracuseStep 5666651 = 8499977) B8499977
theorem B58980383 : Blo 1678039 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B349018949 : Blo 1678039 349018949 := bstep (se 4 (by rfl) ⟨32720526, by rfl⟩ : syracuseStep 349018949 = 65441053) B65441053
theorem B1678207 : Blo 1678039 1678207 := bstep (se 1 (by rfl) ⟨1258655, by rfl⟩ : syracuseStep 1678207 = 2517311) B2517311
theorem B551452049 : Blo 1678039 551452049 := bstep (se 2 (by rfl) ⟨206794518, by rfl⟩ : syracuseStep 551452049 = 413589037) B413589037
theorem B4251305 : Blo 1678039 4251305 := bstep (se 2 (by rfl) ⟨1594239, by rfl⟩ : syracuseStep 4251305 = 3188479) B3188479
theorem B1679263 : Blo 1678039 1679263 := bstep (se 1 (by rfl) ⟨1259447, by rfl⟩ : syracuseStep 1679263 = 2518895) B2518895
theorem B1679611 : Blo 1678039 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B3777695 : Blo 1678039 3777695 := bstep (se 1 (by rfl) ⟨2833271, by rfl⟩ : syracuseStep 3777695 = 5666543) B5666543
theorem B3777767 : Blo 1678039 3777767 := bstep (se 1 (by rfl) ⟨2833325, by rfl⟩ : syracuseStep 3777767 = 5666651) B5666651
theorem B12748265 : Blo 1678039 12748265 := bstep (se 2 (by rfl) ⟨4780599, by rfl⟩ : syracuseStep 12748265 = 9561199) B9561199
theorem B232679299 : Blo 1678039 232679299 := bstep (se 1 (by rfl) ⟨174509474, by rfl⟩ : syracuseStep 232679299 = 349018949) B349018949
theorem B19130417 : Blo 1678039 19130417 := bstep (se 2 (by rfl) ⟨7173906, by rfl⟩ : syracuseStep 19130417 = 14347813) B14347813
theorem B367634699 : Blo 1678039 367634699 := bstep (se 1 (by rfl) ⟨275726024, by rfl⟩ : syracuseStep 367634699 = 551452049) B551452049
theorem B2517743 : Blo 1678039 2517743 := bstep (se 1 (by rfl) ⟨1888307, by rfl⟩ : syracuseStep 2517743 = 3776615) B3776615
theorem B2517755 : Blo 1678039 2517755 := bstep (se 1 (by rfl) ⟨1888316, by rfl⟩ : syracuseStep 2517755 = 3776633) B3776633
theorem B6376927 : Blo 1678039 6376927 := bstep (se 1 (by rfl) ⟨4782695, by rfl⟩ : syracuseStep 6376927 = 9565391) B9565391
theorem B5664275 : Blo 1678039 5664275 := bstep (se 1 (by rfl) ⟨4248206, by rfl⟩ : syracuseStep 5664275 = 8496413) B8496413
theorem B3632905 : Blo 1678039 3632905 := bstep (se 2 (by rfl) ⟨1362339, by rfl⟩ : syracuseStep 3632905 = 2724679) B2724679
theorem B2518943 : Blo 1678039 2518943 := bstep (se 1 (by rfl) ⟨1889207, by rfl⟩ : syracuseStep 2518943 = 3778415) B3778415
theorem B2519207 : Blo 1678039 2519207 := bstep (se 1 (by rfl) ⟨1889405, by rfl⟩ : syracuseStep 2519207 = 3778811) B3778811
theorem B2519711 : Blo 1678039 2519711 := bstep (se 1 (by rfl) ⟨1889783, by rfl⟩ : syracuseStep 2519711 = 3779567) B3779567
theorem B2519879 : Blo 1678039 2519879 := bstep (se 1 (by rfl) ⟨1889909, by rfl⟩ : syracuseStep 2519879 = 3779819) B3779819
theorem B1274271193 : Blo 1678039 1274271193 := bstep (se 2 (by rfl) ⟨477851697, by rfl⟩ : syracuseStep 1274271193 = 955703395) B955703395
theorem B4249199 : Blo 1678039 4249199 := bstep (se 1 (by rfl) ⟨3186899, by rfl⟩ : syracuseStep 4249199 = 6373799) B6373799
theorem B10754299 : Blo 1678039 10754299 := bstep (se 1 (by rfl) ⟨8065724, by rfl⟩ : syracuseStep 10754299 = 16131449) B16131449
theorem B19134791 : Blo 1678039 19134791 := bstep (se 1 (by rfl) ⟨14351093, by rfl⟩ : syracuseStep 19134791 = 28702187) B28702187
theorem B39320255 : Blo 1678039 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B6052639 : Blo 1678039 6052639 := bstep (se 1 (by rfl) ⟨4539479, by rfl⟩ : syracuseStep 6052639 = 9078959) B9078959
theorem B1678363 : Blo 1678039 1678363 := bstep (se 1 (by rfl) ⟨1258772, by rfl⟩ : syracuseStep 1678363 = 2517545) B2517545
theorem B2834203 : Blo 1678039 2834203 := bstep (se 1 (by rfl) ⟨2125652, by rfl⟩ : syracuseStep 2834203 = 4251305) B4251305
theorem B1679471 : Blo 1678039 1679471 := bstep (se 1 (by rfl) ⟨1259603, by rfl⟩ : syracuseStep 1679471 = 2519207) B2519207
theorem B1679807 : Blo 1678039 1679807 := bstep (se 1 (by rfl) ⟨1259855, by rfl⟩ : syracuseStep 1679807 = 2519711) B2519711
theorem B1679919 : Blo 1678039 1679919 := bstep (se 1 (by rfl) ⟨1259939, by rfl⟩ : syracuseStep 1679919 = 2519879) B2519879
theorem B8070185 : Blo 1678039 8070185 := bstep (se 2 (by rfl) ⟨3026319, by rfl⟩ : syracuseStep 8070185 = 6052639) B6052639
theorem B245089799 : Blo 1678039 245089799 := bstep (se 1 (by rfl) ⟨183817349, by rfl⟩ : syracuseStep 245089799 = 367634699) B367634699
theorem B12756527 : Blo 1678039 12756527 := bstep (se 1 (by rfl) ⟨9567395, by rfl⟩ : syracuseStep 12756527 = 19134791) B19134791
theorem B4843873 : Blo 1678039 4843873 := bstep (se 2 (by rfl) ⟨1816452, by rfl⟩ : syracuseStep 4843873 = 3632905) B3632905
theorem B3778937 : Blo 1678039 3778937 := bstep (se 2 (by rfl) ⟨1417101, by rfl⟩ : syracuseStep 3778937 = 2834203) B2834203
theorem B14339065 : Blo 1678039 14339065 := bstep (se 2 (by rfl) ⟨5377149, by rfl⟩ : syracuseStep 14339065 = 10754299) B10754299
theorem B2518463 : Blo 1678039 2518463 := bstep (se 1 (by rfl) ⟨1888847, by rfl⟩ : syracuseStep 2518463 = 3777695) B3777695
theorem B2518511 : Blo 1678039 2518511 := bstep (se 1 (by rfl) ⟨1888883, by rfl⟩ : syracuseStep 2518511 = 3777767) B3777767
theorem B8498843 : Blo 1678039 8498843 := bstep (se 1 (by rfl) ⟨6374132, by rfl⟩ : syracuseStep 8498843 = 12748265) B12748265
theorem B2832799 : Blo 1678039 2832799 := bstep (se 1 (by rfl) ⟨2124599, by rfl⟩ : syracuseStep 2832799 = 4249199) B4249199
theorem B12753611 : Blo 1678039 12753611 := bstep (se 1 (by rfl) ⟨9565208, by rfl⟩ : syracuseStep 12753611 = 19130417) B19130417
theorem B26213503 : Blo 1678039 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B1678495 : Blo 1678039 1678495 := bstep (se 1 (by rfl) ⟨1258871, by rfl⟩ : syracuseStep 1678495 = 2517743) B2517743
theorem B1678503 : Blo 1678039 1678503 := bstep (se 1 (by rfl) ⟨1258877, by rfl⟩ : syracuseStep 1678503 = 2517755) B2517755
theorem B1699028257 : Blo 1678039 1699028257 := bstep (se 2 (by rfl) ⟨637135596, by rfl⟩ : syracuseStep 1699028257 = 1274271193) B1274271193
theorem B8502569 : Blo 1678039 8502569 := bstep (se 2 (by rfl) ⟨3188463, by rfl⟩ : syracuseStep 8502569 = 6376927) B6376927
theorem B3776183 : Blo 1678039 3776183 := bstep (se 1 (by rfl) ⟨2832137, by rfl⟩ : syracuseStep 3776183 = 5664275) B5664275
theorem B310239065 : Blo 1678039 310239065 := bstep (se 2 (by rfl) ⟨116339649, by rfl⟩ : syracuseStep 310239065 = 232679299) B232679299
theorem B1679295 : Blo 1678039 1679295 := bstep (se 1 (by rfl) ⟨1259471, by rfl⟩ : syracuseStep 1679295 = 2518943) B2518943
theorem B3777065 : Blo 1678039 3777065 := bstep (se 2 (by rfl) ⟨1416399, by rfl⟩ : syracuseStep 3777065 = 2832799) B2832799
theorem B8504351 : Blo 1678039 8504351 := bstep (se 1 (by rfl) ⟨6378263, by rfl⟩ : syracuseStep 8504351 = 12756527) B12756527
theorem B2517455 : Blo 1678039 2517455 := bstep (se 1 (by rfl) ⟨1888091, by rfl⟩ : syracuseStep 2517455 = 3776183) B3776183
theorem B206826043 : Blo 1678039 206826043 := bstep (se 1 (by rfl) ⟨155119532, by rfl⟩ : syracuseStep 206826043 = 310239065) B310239065
theorem B163393199 : Blo 1678039 163393199 := bstep (se 1 (by rfl) ⟨122544899, by rfl⟩ : syracuseStep 163393199 = 245089799) B245089799
theorem B34951337 : Blo 1678039 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B2519291 : Blo 1678039 2519291 := bstep (se 1 (by rfl) ⟨1889468, by rfl⟩ : syracuseStep 2519291 = 3778937) B3778937
theorem B2265371009 : Blo 1678039 2265371009 := bstep (se 2 (by rfl) ⟨849514128, by rfl⟩ : syracuseStep 2265371009 = 1699028257) B1699028257
theorem B25833989 : Blo 1678039 25833989 := bstep (se 4 (by rfl) ⟨2421936, by rfl⟩ : syracuseStep 25833989 = 4843873) B4843873
theorem B5665895 : Blo 1678039 5665895 := bstep (se 1 (by rfl) ⟨4249421, by rfl⟩ : syracuseStep 5665895 = 8498843) B8498843
theorem B5380123 : Blo 1678039 5380123 := bstep (se 1 (by rfl) ⟨4035092, by rfl⟩ : syracuseStep 5380123 = 8070185) B8070185
theorem B19118753 : Blo 1678039 19118753 := bstep (se 2 (by rfl) ⟨7169532, by rfl⟩ : syracuseStep 19118753 = 14339065) B14339065
theorem B8502407 : Blo 1678039 8502407 := bstep (se 1 (by rfl) ⟨6376805, by rfl⟩ : syracuseStep 8502407 = 12753611) B12753611
theorem B5668379 : Blo 1678039 5668379 := bstep (se 1 (by rfl) ⟨4251284, by rfl⟩ : syracuseStep 5668379 = 8502569) B8502569
theorem B1678975 : Blo 1678039 1678975 := bstep (se 1 (by rfl) ⟨1259231, by rfl⟩ : syracuseStep 1678975 = 2518463) B2518463
theorem B1679007 : Blo 1678039 1679007 := bstep (se 1 (by rfl) ⟨1259255, by rfl⟩ : syracuseStep 1679007 = 2518511) B2518511
theorem B1679527 : Blo 1678039 1679527 := bstep (se 1 (by rfl) ⟨1259645, by rfl⟩ : syracuseStep 1679527 = 2519291) B2519291
theorem B5669567 : Blo 1678039 5669567 := bstep (se 1 (by rfl) ⟨4252175, by rfl⟩ : syracuseStep 5669567 = 8504351) B8504351
theorem B3777263 : Blo 1678039 3777263 := bstep (se 1 (by rfl) ⟨2832947, by rfl⟩ : syracuseStep 3777263 = 5665895) B5665895
theorem B275768057 : Blo 1678039 275768057 := bstep (se 2 (by rfl) ⟨103413021, by rfl⟩ : syracuseStep 275768057 = 206826043) B206826043
theorem B3778919 : Blo 1678039 3778919 := bstep (se 1 (by rfl) ⟨2834189, by rfl⟩ : syracuseStep 3778919 = 5668379) B5668379
theorem B23300891 : Blo 1678039 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B1510247339 : Blo 1678039 1510247339 := bstep (se 1 (by rfl) ⟨1132685504, by rfl⟩ : syracuseStep 1510247339 = 2265371009) B2265371009
theorem B2518043 : Blo 1678039 2518043 := bstep (se 1 (by rfl) ⟨1888532, by rfl⟩ : syracuseStep 2518043 = 3777065) B3777065
theorem B68890637 : Blo 1678039 68890637 := bstep (se 3 (by rfl) ⟨12916994, by rfl⟩ : syracuseStep 68890637 = 25833989) B25833989
theorem B7173497 : Blo 1678039 7173497 := bstep (se 2 (by rfl) ⟨2690061, by rfl⟩ : syracuseStep 7173497 = 5380123) B5380123
theorem B1678303 : Blo 1678039 1678303 := bstep (se 1 (by rfl) ⟨1258727, by rfl⟩ : syracuseStep 1678303 = 2517455) B2517455
theorem B12745835 : Blo 1678039 12745835 := bstep (se 1 (by rfl) ⟨9559376, by rfl⟩ : syracuseStep 12745835 = 19118753) B19118753
theorem B5668271 : Blo 1678039 5668271 := bstep (se 1 (by rfl) ⟨4251203, by rfl⟩ : syracuseStep 5668271 = 8502407) B8502407
theorem B108928799 : Blo 1678039 108928799 := bstep (se 1 (by rfl) ⟨81696599, by rfl⟩ : syracuseStep 108928799 = 163393199) B163393199
theorem B183845371 : Blo 1678039 183845371 := bstep (se 1 (by rfl) ⟨137884028, by rfl⟩ : syracuseStep 183845371 = 275768057) B275768057
theorem B15533927 : Blo 1678039 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B1006831559 : Blo 1678039 1006831559 := bstep (se 1 (by rfl) ⟨755123669, by rfl⟩ : syracuseStep 1006831559 = 1510247339) B1510247339
theorem B8497223 : Blo 1678039 8497223 := bstep (se 1 (by rfl) ⟨6372917, by rfl⟩ : syracuseStep 8497223 = 12745835) B12745835
theorem B3778847 : Blo 1678039 3778847 := bstep (se 1 (by rfl) ⟨2834135, by rfl⟩ : syracuseStep 3778847 = 5668271) B5668271
theorem B45927091 : Blo 1678039 45927091 := bstep (se 1 (by rfl) ⟨34445318, by rfl⟩ : syracuseStep 45927091 = 68890637) B68890637
theorem B3779711 : Blo 1678039 3779711 := bstep (se 1 (by rfl) ⟨2834783, by rfl⟩ : syracuseStep 3779711 = 5669567) B5669567
theorem B2518175 : Blo 1678039 2518175 := bstep (se 1 (by rfl) ⟨1888631, by rfl⟩ : syracuseStep 2518175 = 3777263) B3777263
theorem B2519279 : Blo 1678039 2519279 := bstep (se 1 (by rfl) ⟨1889459, by rfl⟩ : syracuseStep 2519279 = 3778919) B3778919
theorem B72619199 : Blo 1678039 72619199 := bstep (se 1 (by rfl) ⟨54464399, by rfl⟩ : syracuseStep 72619199 = 108928799) B108928799
theorem B4782331 : Blo 1678039 4782331 := bstep (se 1 (by rfl) ⟨3586748, by rfl⟩ : syracuseStep 4782331 = 7173497) B7173497
theorem B1678695 : Blo 1678039 1678695 := bstep (se 1 (by rfl) ⟨1259021, by rfl⟩ : syracuseStep 1678695 = 2518043) B2518043
theorem B1679519 : Blo 1678039 1679519 := bstep (se 1 (by rfl) ⟨1259639, by rfl⟩ : syracuseStep 1679519 = 2519279) B2519279
theorem B61236121 : Blo 1678039 61236121 := bstep (se 2 (by rfl) ⟨22963545, by rfl⟩ : syracuseStep 61236121 = 45927091) B45927091
theorem B10355951 : Blo 1678039 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B671221039 : Blo 1678039 671221039 := bstep (se 1 (by rfl) ⟨503415779, by rfl⟩ : syracuseStep 671221039 = 1006831559) B1006831559
theorem B6376441 : Blo 1678039 6376441 := bstep (se 2 (by rfl) ⟨2391165, by rfl⟩ : syracuseStep 6376441 = 4782331) B4782331
theorem B5664815 : Blo 1678039 5664815 := bstep (se 1 (by rfl) ⟨4248611, by rfl⟩ : syracuseStep 5664815 = 8497223) B8497223
theorem B2519231 : Blo 1678039 2519231 := bstep (se 1 (by rfl) ⟨1889423, by rfl⟩ : syracuseStep 2519231 = 3778847) B3778847
theorem B2519807 : Blo 1678039 2519807 := bstep (se 1 (by rfl) ⟨1889855, by rfl⟩ : syracuseStep 2519807 = 3779711) B3779711
theorem B245127161 : Blo 1678039 245127161 := bstep (se 2 (by rfl) ⟨91922685, by rfl⟩ : syracuseStep 245127161 = 183845371) B183845371
theorem B48412799 : Blo 1678039 48412799 := bstep (se 1 (by rfl) ⟨36309599, by rfl⟩ : syracuseStep 48412799 = 72619199) B72619199
theorem B1678783 : Blo 1678039 1678783 := bstep (se 1 (by rfl) ⟨1259087, by rfl⟩ : syracuseStep 1678783 = 2518175) B2518175
theorem B3776543 : Blo 1678039 3776543 := bstep (se 1 (by rfl) ⟨2832407, by rfl⟩ : syracuseStep 3776543 = 5664815) B5664815
theorem B1679487 : Blo 1678039 1679487 := bstep (se 1 (by rfl) ⟨1259615, by rfl⟩ : syracuseStep 1679487 = 2519231) B2519231
theorem B1679871 : Blo 1678039 1679871 := bstep (se 1 (by rfl) ⟨1259903, by rfl⟩ : syracuseStep 1679871 = 2519807) B2519807
theorem B894961385 : Blo 1678039 894961385 := bstep (se 2 (by rfl) ⟨335610519, by rfl⟩ : syracuseStep 894961385 = 671221039) B671221039
theorem B163418107 : Blo 1678039 163418107 := bstep (se 1 (by rfl) ⟨122563580, by rfl⟩ : syracuseStep 163418107 = 245127161) B245127161
theorem B6903967 : Blo 1678039 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B81648161 : Blo 1678039 81648161 := bstep (se 2 (by rfl) ⟨30618060, by rfl⟩ : syracuseStep 81648161 = 61236121) B61236121
theorem B8501921 : Blo 1678039 8501921 := bstep (se 2 (by rfl) ⟨3188220, by rfl⟩ : syracuseStep 8501921 = 6376441) B6376441
theorem B32275199 : Blo 1678039 32275199 := bstep (se 1 (by rfl) ⟨24206399, by rfl⟩ : syracuseStep 32275199 = 48412799) B48412799
theorem B596640923 : Blo 1678039 596640923 := bstep (se 1 (by rfl) ⟨447480692, by rfl⟩ : syracuseStep 596640923 = 894961385) B894961385
theorem B217890809 : Blo 1678039 217890809 := bstep (se 2 (by rfl) ⟨81709053, by rfl⟩ : syracuseStep 217890809 = 163418107) B163418107
theorem B2517695 : Blo 1678039 2517695 := bstep (se 1 (by rfl) ⟨1888271, by rfl⟩ : syracuseStep 2517695 = 3776543) B3776543
theorem B54432107 : Blo 1678039 54432107 := bstep (se 1 (by rfl) ⟨40824080, by rfl⟩ : syracuseStep 54432107 = 81648161) B81648161
theorem B21516799 : Blo 1678039 21516799 := bstep (se 1 (by rfl) ⟨16137599, by rfl⟩ : syracuseStep 21516799 = 32275199) B32275199
theorem B9205289 : Blo 1678039 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B5667947 : Blo 1678039 5667947 := bstep (se 1 (by rfl) ⟨4250960, by rfl⟩ : syracuseStep 5667947 = 8501921) B8501921
theorem B28689065 : Blo 1678039 28689065 := bstep (se 2 (by rfl) ⟨10758399, by rfl⟩ : syracuseStep 28689065 = 21516799) B21516799
theorem B145260539 : Blo 1678039 145260539 := bstep (se 1 (by rfl) ⟨108945404, by rfl⟩ : syracuseStep 145260539 = 217890809) B217890809
theorem B6136859 : Blo 1678039 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B3778631 : Blo 1678039 3778631 := bstep (se 1 (by rfl) ⟨2833973, by rfl⟩ : syracuseStep 3778631 = 5667947) B5667947
theorem B36288071 : Blo 1678039 36288071 := bstep (se 1 (by rfl) ⟨27216053, by rfl⟩ : syracuseStep 36288071 = 54432107) B54432107
theorem B397760615 : Blo 1678039 397760615 := bstep (se 1 (by rfl) ⟨298320461, by rfl⟩ : syracuseStep 397760615 = 596640923) B596640923
theorem B1678463 : Blo 1678039 1678463 := bstep (se 1 (by rfl) ⟨1258847, by rfl⟩ : syracuseStep 1678463 = 2517695) B2517695
theorem B24192047 : Blo 1678039 24192047 := bstep (se 1 (by rfl) ⟨18144035, by rfl⟩ : syracuseStep 24192047 = 36288071) B36288071
theorem B96840359 : Blo 1678039 96840359 := bstep (se 1 (by rfl) ⟨72630269, by rfl⟩ : syracuseStep 96840359 = 145260539) B145260539
theorem B4091239 : Blo 1678039 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B2519087 : Blo 1678039 2519087 := bstep (se 1 (by rfl) ⟨1889315, by rfl⟩ : syracuseStep 2519087 = 3778631) B3778631
theorem B19126043 : Blo 1678039 19126043 := bstep (se 1 (by rfl) ⟨14344532, by rfl⟩ : syracuseStep 19126043 = 28689065) B28689065
theorem B265173743 : Blo 1678039 265173743 := bstep (se 1 (by rfl) ⟨198880307, by rfl⟩ : syracuseStep 265173743 = 397760615) B397760615
theorem B1679391 : Blo 1678039 1679391 := bstep (se 1 (by rfl) ⟨1259543, by rfl⟩ : syracuseStep 1679391 = 2519087) B2519087
theorem B12750695 : Blo 1678039 12750695 := bstep (se 1 (by rfl) ⟨9563021, by rfl⟩ : syracuseStep 12750695 = 19126043) B19126043
theorem B21819941 : Blo 1678039 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B16128031 : Blo 1678039 16128031 := bstep (se 1 (by rfl) ⟨12096023, by rfl⟩ : syracuseStep 16128031 = 24192047) B24192047
theorem B64560239 : Blo 1678039 64560239 := bstep (se 1 (by rfl) ⟨48420179, by rfl⟩ : syracuseStep 64560239 = 96840359) B96840359
theorem B176782495 : Blo 1678039 176782495 := bstep (se 1 (by rfl) ⟨132586871, by rfl⟩ : syracuseStep 176782495 = 265173743) B265173743
theorem B21504041 : Blo 1678039 21504041 := bstep (se 2 (by rfl) ⟨8064015, by rfl⟩ : syracuseStep 21504041 = 16128031) B16128031
theorem B235709993 : Blo 1678039 235709993 := bstep (se 2 (by rfl) ⟨88391247, by rfl⟩ : syracuseStep 235709993 = 176782495) B176782495
theorem B8500463 : Blo 1678039 8500463 := bstep (se 1 (by rfl) ⟨6375347, by rfl⟩ : syracuseStep 8500463 = 12750695) B12750695
theorem B14546627 : Blo 1678039 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B43040159 : Blo 1678039 43040159 := bstep (se 1 (by rfl) ⟨32280119, by rfl⟩ : syracuseStep 43040159 = 64560239) B64560239
theorem B14336027 : Blo 1678039 14336027 := bstep (se 1 (by rfl) ⟨10752020, by rfl⟩ : syracuseStep 14336027 = 21504041) B21504041
theorem B628559981 : Blo 1678039 628559981 := bstep (se 3 (by rfl) ⟨117854996, by rfl⟩ : syracuseStep 628559981 = 235709993) B235709993
theorem B28693439 : Blo 1678039 28693439 := bstep (se 1 (by rfl) ⟨21520079, by rfl⟩ : syracuseStep 28693439 = 43040159) B43040159
theorem B5666975 : Blo 1678039 5666975 := bstep (se 1 (by rfl) ⟨4250231, by rfl⟩ : syracuseStep 5666975 = 8500463) B8500463
theorem B9697751 : Blo 1678039 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B19128959 : Blo 1678039 19128959 := bstep (se 1 (by rfl) ⟨14346719, by rfl⟩ : syracuseStep 19128959 = 28693439) B28693439
theorem B3777983 : Blo 1678039 3777983 := bstep (se 1 (by rfl) ⟨2833487, by rfl⟩ : syracuseStep 3777983 = 5666975) B5666975
theorem B6465167 : Blo 1678039 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B419039987 : Blo 1678039 419039987 := bstep (se 1 (by rfl) ⟨314279990, by rfl⟩ : syracuseStep 419039987 = 628559981) B628559981
theorem B9557351 : Blo 1678039 9557351 := bstep (se 1 (by rfl) ⟨7168013, by rfl⟩ : syracuseStep 9557351 = 14336027) B14336027
theorem B4310111 : Blo 1678039 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B1117439965 : Blo 1678039 1117439965 := bstep (se 3 (by rfl) ⟨209519993, by rfl⟩ : syracuseStep 1117439965 = 419039987) B419039987
theorem B2518655 : Blo 1678039 2518655 := bstep (se 1 (by rfl) ⟨1888991, by rfl⟩ : syracuseStep 2518655 = 3777983) B3777983
theorem B12752639 : Blo 1678039 12752639 := bstep (se 1 (by rfl) ⟨9564479, by rfl⟩ : syracuseStep 12752639 = 19128959) B19128959
theorem B6371567 : Blo 1678039 6371567 := bstep (se 1 (by rfl) ⟨4778675, by rfl⟩ : syracuseStep 6371567 = 9557351) B9557351
theorem B4247711 : Blo 1678039 4247711 := bstep (se 1 (by rfl) ⟨3185783, by rfl⟩ : syracuseStep 4247711 = 6371567) B6371567
theorem B2873407 : Blo 1678039 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B8501759 : Blo 1678039 8501759 := bstep (se 1 (by rfl) ⟨6376319, by rfl⟩ : syracuseStep 8501759 = 12752639) B12752639
theorem B1679103 : Blo 1678039 1679103 := bstep (se 1 (by rfl) ⟨1259327, by rfl⟩ : syracuseStep 1679103 = 2518655) B2518655
theorem B1489919953 : Blo 1678039 1489919953 := bstep (se 2 (by rfl) ⟨558719982, by rfl⟩ : syracuseStep 1489919953 = 1117439965) B1117439965
theorem B3831209 : Blo 1678039 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B2831807 : Blo 1678039 2831807 := bstep (se 1 (by rfl) ⟨2123855, by rfl⟩ : syracuseStep 2831807 = 4247711) B4247711
theorem B5667839 : Blo 1678039 5667839 := bstep (se 1 (by rfl) ⟨4250879, by rfl⟩ : syracuseStep 5667839 = 8501759) B8501759
theorem B1986559937 : Blo 1678039 1986559937 := bstep (se 2 (by rfl) ⟨744959976, by rfl⟩ : syracuseStep 1986559937 = 1489919953) B1489919953
theorem B3778559 : Blo 1678039 3778559 := bstep (se 1 (by rfl) ⟨2833919, by rfl⟩ : syracuseStep 3778559 = 5667839) B5667839
theorem B1887871 : Blo 1678039 1887871 := bstep (se 1 (by rfl) ⟨1415903, by rfl⟩ : syracuseStep 1887871 = 2831807) B2831807
theorem B1324373291 : Blo 1678039 1324373291 := bstep (se 1 (by rfl) ⟨993279968, by rfl⟩ : syracuseStep 1324373291 = 1986559937) B1986559937
theorem B2554139 : Blo 1678039 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B2517161 : Blo 1678039 2517161 := bstep (se 2 (by rfl) ⟨943935, by rfl⟩ : syracuseStep 2517161 = 1887871) B1887871
theorem B6811037 : Blo 1678039 6811037 := bstep (se 3 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 6811037 = 2554139) B2554139
theorem B2519039 : Blo 1678039 2519039 := bstep (se 1 (by rfl) ⟨1889279, by rfl⟩ : syracuseStep 2519039 = 3778559) B3778559
theorem B882915527 : Blo 1678039 882915527 := bstep (se 1 (by rfl) ⟨662186645, by rfl⟩ : syracuseStep 882915527 = 1324373291) B1324373291
theorem B4540691 : Blo 1678039 4540691 := bstep (se 1 (by rfl) ⟨3405518, by rfl⟩ : syracuseStep 4540691 = 6811037) B6811037
theorem B1678107 : Blo 1678039 1678107 := bstep (se 1 (by rfl) ⟨1258580, by rfl⟩ : syracuseStep 1678107 = 2517161) B2517161
theorem B588610351 : Blo 1678039 588610351 := bstep (se 1 (by rfl) ⟨441457763, by rfl⟩ : syracuseStep 588610351 = 882915527) B882915527
theorem B1679359 : Blo 1678039 1679359 := bstep (se 1 (by rfl) ⟨1259519, by rfl⟩ : syracuseStep 1679359 = 2519039) B2519039
theorem B784813801 : Blo 1678039 784813801 := bstep (se 2 (by rfl) ⟨294305175, by rfl⟩ : syracuseStep 784813801 = 588610351) B588610351
theorem B3027127 : Blo 1678039 3027127 := bstep (se 1 (by rfl) ⟨2270345, by rfl⟩ : syracuseStep 3027127 = 4540691) B4540691
theorem B1046418401 : Blo 1678039 1046418401 := bstep (se 2 (by rfl) ⟨392406900, by rfl⟩ : syracuseStep 1046418401 = 784813801) B784813801
theorem B4036169 : Blo 1678039 4036169 := bstep (se 2 (by rfl) ⟨1513563, by rfl⟩ : syracuseStep 4036169 = 3027127) B3027127
theorem B697612267 : Blo 1678039 697612267 := bstep (se 1 (by rfl) ⟨523209200, by rfl⟩ : syracuseStep 697612267 = 1046418401) B1046418401
theorem B10763117 : Blo 1678039 10763117 := bstep (se 3 (by rfl) ⟨2018084, by rfl⟩ : syracuseStep 10763117 = 4036169) B4036169
theorem B930149689 : Blo 1678039 930149689 := bstep (se 2 (by rfl) ⟨348806133, by rfl⟩ : syracuseStep 930149689 = 697612267) B697612267
theorem B7175411 : Blo 1678039 7175411 := bstep (se 1 (by rfl) ⟨5381558, by rfl⟩ : syracuseStep 7175411 = 10763117) B10763117
theorem B1240199585 : Blo 1678039 1240199585 := bstep (se 2 (by rfl) ⟨465074844, by rfl⟩ : syracuseStep 1240199585 = 930149689) B930149689
theorem B4783607 : Blo 1678039 4783607 := bstep (se 1 (by rfl) ⟨3587705, by rfl⟩ : syracuseStep 4783607 = 7175411) B7175411
theorem B3189071 : Blo 1678039 3189071 := bstep (se 1 (by rfl) ⟨2391803, by rfl⟩ : syracuseStep 3189071 = 4783607) B4783607
theorem B826799723 : Blo 1678039 826799723 := bstep (se 1 (by rfl) ⟨620099792, by rfl⟩ : syracuseStep 826799723 = 1240199585) B1240199585
theorem B8504189 : Blo 1678039 8504189 := bstep (se 3 (by rfl) ⟨1594535, by rfl⟩ : syracuseStep 8504189 = 3189071) B3189071
theorem B551199815 : Blo 1678039 551199815 := bstep (se 1 (by rfl) ⟨413399861, by rfl⟩ : syracuseStep 551199815 = 826799723) B826799723
theorem B5669459 : Blo 1678039 5669459 := bstep (se 1 (by rfl) ⟨4252094, by rfl⟩ : syracuseStep 5669459 = 8504189) B8504189
theorem B367466543 : Blo 1678039 367466543 := bstep (se 1 (by rfl) ⟨275599907, by rfl⟩ : syracuseStep 367466543 = 551199815) B551199815
theorem B3779639 : Blo 1678039 3779639 := bstep (se 1 (by rfl) ⟨2834729, by rfl⟩ : syracuseStep 3779639 = 5669459) B5669459
theorem B244977695 : Blo 1678039 244977695 := bstep (se 1 (by rfl) ⟨183733271, by rfl⟩ : syracuseStep 244977695 = 367466543) B367466543
theorem B163318463 : Blo 1678039 163318463 := bstep (se 1 (by rfl) ⟨122488847, by rfl⟩ : syracuseStep 163318463 = 244977695) B244977695
theorem B2519759 : Blo 1678039 2519759 := bstep (se 1 (by rfl) ⟨1889819, by rfl⟩ : syracuseStep 2519759 = 3779639) B3779639
theorem B1679839 : Blo 1678039 1679839 := bstep (se 1 (by rfl) ⟨1259879, by rfl⟩ : syracuseStep 1679839 = 2519759) B2519759
theorem B108878975 : Blo 1678039 108878975 := bstep (se 1 (by rfl) ⟨81659231, by rfl⟩ : syracuseStep 108878975 = 163318463) B163318463
theorem B72585983 : Blo 1678039 72585983 := bstep (se 1 (by rfl) ⟨54439487, by rfl⟩ : syracuseStep 72585983 = 108878975) B108878975
theorem B48390655 : Blo 1678039 48390655 := bstep (se 1 (by rfl) ⟨36292991, by rfl⟩ : syracuseStep 48390655 = 72585983) B72585983
theorem B64520873 : Blo 1678039 64520873 := bstep (se 2 (by rfl) ⟨24195327, by rfl⟩ : syracuseStep 64520873 = 48390655) B48390655
theorem B43013915 : Blo 1678039 43013915 := bstep (se 1 (by rfl) ⟨32260436, by rfl⟩ : syracuseStep 43013915 = 64520873) B64520873
theorem B28675943 : Blo 1678039 28675943 := bstep (se 1 (by rfl) ⟨21506957, by rfl⟩ : syracuseStep 28675943 = 43013915) B43013915
theorem B19117295 : Blo 1678039 19117295 := bstep (se 1 (by rfl) ⟨14337971, by rfl⟩ : syracuseStep 19117295 = 28675943) B28675943
theorem B12744863 : Blo 1678039 12744863 := bstep (se 1 (by rfl) ⟨9558647, by rfl⟩ : syracuseStep 12744863 = 19117295) B19117295
theorem B8496575 : Blo 1678039 8496575 := bstep (se 1 (by rfl) ⟨6372431, by rfl⟩ : syracuseStep 8496575 = 12744863) B12744863
theorem B5664383 : Blo 1678039 5664383 := bstep (se 1 (by rfl) ⟨4248287, by rfl⟩ : syracuseStep 5664383 = 8496575) B8496575
theorem B3776255 : Blo 1678039 3776255 := bstep (se 1 (by rfl) ⟨2832191, by rfl⟩ : syracuseStep 3776255 = 5664383) B5664383
theorem B2517503 : Blo 1678039 2517503 := bstep (se 1 (by rfl) ⟨1888127, by rfl⟩ : syracuseStep 2517503 = 3776255) B3776255
theorem B1678335 : Blo 1678039 1678335 := bstep (se 1 (by rfl) ⟨1258751, by rfl⟩ : syracuseStep 1678335 = 2517503) B2517503

theorem C0 (j : ℕ) (h1 : 419509 ≤ j) (h2 : j ≤ 420009) : Blo 1678039 (4 * j + 3) := by
  interval_cases j
  · exact B1678039
  · exact B1678043
  · exact B1678047
  · exact B1678051
  · exact B1678055
  · exact B1678059
  · exact B1678063
  · exact B1678067
  · exact B1678071
  · exact B1678075
  · exact B1678079
  · exact B1678083
  · exact B1678087
  · exact B1678091
  · exact B1678095
  · exact B1678099
  · exact B1678103
  · exact B1678107
  · exact B1678111
  · exact B1678115
  · exact B1678119
  · exact B1678123
  · exact B1678127
  · exact B1678131
  · exact B1678135
  · exact B1678139
  · exact B1678143
  · exact B1678147
  · exact B1678151
  · exact B1678155
  · exact B1678159
  · exact B1678163
  · exact B1678167
  · exact B1678171
  · exact B1678175
  · exact B1678179
  · exact B1678183
  · exact B1678187
  · exact B1678191
  · exact B1678195
  · exact B1678199
  · exact B1678203
  · exact B1678207
  · exact B1678211
  · exact B1678215
  · exact B1678219
  · exact B1678223
  · exact B1678227
  · exact B1678231
  · exact B1678235
  · exact B1678239
  · exact B1678243
  · exact B1678247
  · exact B1678251
  · exact B1678255
  · exact B1678259
  · exact B1678263
  · exact B1678267
  · exact B1678271
  · exact B1678275
  · exact B1678279
  · exact B1678283
  · exact B1678287
  · exact B1678291
  · exact B1678295
  · exact B1678299
  · exact B1678303
  · exact B1678307
  · exact B1678311
  · exact B1678315
  · exact B1678319
  · exact B1678323
  · exact B1678327
  · exact B1678331
  · exact B1678335
  · exact B1678339
  · exact B1678343
  · exact B1678347
  · exact B1678351
  · exact B1678355
  · exact B1678359
  · exact B1678363
  · exact B1678367
  · exact B1678371
  · exact B1678375
  · exact B1678379
  · exact B1678383
  · exact B1678387
  · exact B1678391
  · exact B1678395
  · exact B1678399
  · exact B1678403
  · exact B1678407
  · exact B1678411
  · exact B1678415
  · exact B1678419
  · exact B1678423
  · exact B1678427
  · exact B1678431
  · exact B1678435
  · exact B1678439
  · exact B1678443
  · exact B1678447
  · exact B1678451
  · exact B1678455
  · exact B1678459
  · exact B1678463
  · exact B1678467
  · exact B1678471
  · exact B1678475
  · exact B1678479
  · exact B1678483
  · exact B1678487
  · exact B1678491
  · exact B1678495
  · exact B1678499
  · exact B1678503
  · exact B1678507
  · exact B1678511
  · exact B1678515
  · exact B1678519
  · exact B1678523
  · exact B1678527
  · exact B1678531
  · exact B1678535
  · exact B1678539
  · exact B1678543
  · exact B1678547
  · exact B1678551
  · exact B1678555
  · exact B1678559
  · exact B1678563
  · exact B1678567
  · exact B1678571
  · exact B1678575
  · exact B1678579
  · exact B1678583
  · exact B1678587
  · exact B1678591
  · exact B1678595
  · exact B1678599
  · exact B1678603
  · exact B1678607
  · exact B1678611
  · exact B1678615
  · exact B1678619
  · exact B1678623
  · exact B1678627
  · exact B1678631
  · exact B1678635
  · exact B1678639
  · exact B1678643
  · exact B1678647
  · exact B1678651
  · exact B1678655
  · exact B1678659
  · exact B1678663
  · exact B1678667
  · exact B1678671
  · exact B1678675
  · exact B1678679
  · exact B1678683
  · exact B1678687
  · exact B1678691
  · exact B1678695
  · exact B1678699
  · exact B1678703
  · exact B1678707
  · exact B1678711
  · exact B1678715
  · exact B1678719
  · exact B1678723
  · exact B1678727
  · exact B1678731
  · exact B1678735
  · exact B1678739
  · exact B1678743
  · exact B1678747
  · exact B1678751
  · exact B1678755
  · exact B1678759
  · exact B1678763
  · exact B1678767
  · exact B1678771
  · exact B1678775
  · exact B1678779
  · exact B1678783
  · exact B1678787
  · exact B1678791
  · exact B1678795
  · exact B1678799
  · exact B1678803
  · exact B1678807
  · exact B1678811
  · exact B1678815
  · exact B1678819
  · exact B1678823
  · exact B1678827
  · exact B1678831
  · exact B1678835
  · exact B1678839
  · exact B1678843
  · exact B1678847
  · exact B1678851
  · exact B1678855
  · exact B1678859
  · exact B1678863
  · exact B1678867
  · exact B1678871
  · exact B1678875
  · exact B1678879
  · exact B1678883
  · exact B1678887
  · exact B1678891
  · exact B1678895
  · exact B1678899
  · exact B1678903
  · exact B1678907
  · exact B1678911
  · exact B1678915
  · exact B1678919
  · exact B1678923
  · exact B1678927
  · exact B1678931
  · exact B1678935
  · exact B1678939
  · exact B1678943
  · exact B1678947
  · exact B1678951
  · exact B1678955
  · exact B1678959
  · exact B1678963
  · exact B1678967
  · exact B1678971
  · exact B1678975
  · exact B1678979
  · exact B1678983
  · exact B1678987
  · exact B1678991
  · exact B1678995
  · exact B1678999
  · exact B1679003
  · exact B1679007
  · exact B1679011
  · exact B1679015
  · exact B1679019
  · exact B1679023
  · exact B1679027
  · exact B1679031
  · exact B1679035
  · exact B1679039
  · exact B1679043
  · exact B1679047
  · exact B1679051
  · exact B1679055
  · exact B1679059
  · exact B1679063
  · exact B1679067
  · exact B1679071
  · exact B1679075
  · exact B1679079
  · exact B1679083
  · exact B1679087
  · exact B1679091
  · exact B1679095
  · exact B1679099
  · exact B1679103
  · exact B1679107
  · exact B1679111
  · exact B1679115
  · exact B1679119
  · exact B1679123
  · exact B1679127
  · exact B1679131
  · exact B1679135
  · exact B1679139
  · exact B1679143
  · exact B1679147
  · exact B1679151
  · exact B1679155
  · exact B1679159
  · exact B1679163
  · exact B1679167
  · exact B1679171
  · exact B1679175
  · exact B1679179
  · exact B1679183
  · exact B1679187
  · exact B1679191
  · exact B1679195
  · exact B1679199
  · exact B1679203
  · exact B1679207
  · exact B1679211
  · exact B1679215
  · exact B1679219
  · exact B1679223
  · exact B1679227
  · exact B1679231
  · exact B1679235
  · exact B1679239
  · exact B1679243
  · exact B1679247
  · exact B1679251
  · exact B1679255
  · exact B1679259
  · exact B1679263
  · exact B1679267
  · exact B1679271
  · exact B1679275
  · exact B1679279
  · exact B1679283
  · exact B1679287
  · exact B1679291
  · exact B1679295
  · exact B1679299
  · exact B1679303
  · exact B1679307
  · exact B1679311
  · exact B1679315
  · exact B1679319
  · exact B1679323
  · exact B1679327
  · exact B1679331
  · exact B1679335
  · exact B1679339
  · exact B1679343
  · exact B1679347
  · exact B1679351
  · exact B1679355
  · exact B1679359
  · exact B1679363
  · exact B1679367
  · exact B1679371
  · exact B1679375
  · exact B1679379
  · exact B1679383
  · exact B1679387
  · exact B1679391
  · exact B1679395
  · exact B1679399
  · exact B1679403
  · exact B1679407
  · exact B1679411
  · exact B1679415
  · exact B1679419
  · exact B1679423
  · exact B1679427
  · exact B1679431
  · exact B1679435
  · exact B1679439
  · exact B1679443
  · exact B1679447
  · exact B1679451
  · exact B1679455
  · exact B1679459
  · exact B1679463
  · exact B1679467
  · exact B1679471
  · exact B1679475
  · exact B1679479
  · exact B1679483
  · exact B1679487
  · exact B1679491
  · exact B1679495
  · exact B1679499
  · exact B1679503
  · exact B1679507
  · exact B1679511
  · exact B1679515
  · exact B1679519
  · exact B1679523
  · exact B1679527
  · exact B1679531
  · exact B1679535
  · exact B1679539
  · exact B1679543
  · exact B1679547
  · exact B1679551
  · exact B1679555
  · exact B1679559
  · exact B1679563
  · exact B1679567
  · exact B1679571
  · exact B1679575
  · exact B1679579
  · exact B1679583
  · exact B1679587
  · exact B1679591
  · exact B1679595
  · exact B1679599
  · exact B1679603
  · exact B1679607
  · exact B1679611
  · exact B1679615
  · exact B1679619
  · exact B1679623
  · exact B1679627
  · exact B1679631
  · exact B1679635
  · exact B1679639
  · exact B1679643
  · exact B1679647
  · exact B1679651
  · exact B1679655
  · exact B1679659
  · exact B1679663
  · exact B1679667
  · exact B1679671
  · exact B1679675
  · exact B1679679
  · exact B1679683
  · exact B1679687
  · exact B1679691
  · exact B1679695
  · exact B1679699
  · exact B1679703
  · exact B1679707
  · exact B1679711
  · exact B1679715
  · exact B1679719
  · exact B1679723
  · exact B1679727
  · exact B1679731
  · exact B1679735
  · exact B1679739
  · exact B1679743
  · exact B1679747
  · exact B1679751
  · exact B1679755
  · exact B1679759
  · exact B1679763
  · exact B1679767
  · exact B1679771
  · exact B1679775
  · exact B1679779
  · exact B1679783
  · exact B1679787
  · exact B1679791
  · exact B1679795
  · exact B1679799
  · exact B1679803
  · exact B1679807
  · exact B1679811
  · exact B1679815
  · exact B1679819
  · exact B1679823
  · exact B1679827
  · exact B1679831
  · exact B1679835
  · exact B1679839
  · exact B1679843
  · exact B1679847
  · exact B1679851
  · exact B1679855
  · exact B1679859
  · exact B1679863
  · exact B1679867
  · exact B1679871
  · exact B1679875
  · exact B1679879
  · exact B1679883
  · exact B1679887
  · exact B1679891
  · exact B1679895
  · exact B1679899
  · exact B1679903
  · exact B1679907
  · exact B1679911
  · exact B1679915
  · exact B1679919
  · exact B1679923
  · exact B1679927
  · exact B1679931
  · exact B1679935
  · exact B1679939
  · exact B1679943
  · exact B1679947
  · exact B1679951
  · exact B1679955
  · exact B1679959
  · exact B1679963
  · exact B1679967
  · exact B1679971
  · exact B1679975
  · exact B1679979
  · exact B1679983
  · exact B1679987
  · exact B1679991
  · exact B1679995
  · exact B1679999
  · exact B1680003
  · exact B1680007
  · exact B1680011
  · exact B1680015
  · exact B1680019
  · exact B1680023
  · exact B1680027
  · exact B1680031
  · exact B1680035
  · exact B1680039

theorem solution (m : ℕ) (hlo : 1678039 ≤ m) (hhi : m ≤ 1680039) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 419509 ≤ j := by omega
    have hj2 : j ≤ 420009 := by omega
    have hb : Blo 1678039 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
