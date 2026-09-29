-- Prove2me | solution 1 for syracuse_descends_range_558808_562808
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:36.909384+00:00
-- url     : https://prove2.me/submissions/d22a0207-f2c7-4cde-8286-a5e074c55baa

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


theorem B2162933 : Blo 558808 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B2687269 : Blo 558808 2687269 := bbase (se 4 (by rfl) ⟨251931, by rfl⟩ : syracuseStep 2687269 = 503863) (by norm_num)
theorem B1802533 : Blo 558808 1802533 := bbase (se 4 (by rfl) ⟨168987, by rfl⟩ : syracuseStep 1802533 = 337975) (by norm_num)
theorem B2130245 : Blo 558808 2130245 := bbase (se 4 (by rfl) ⟨199710, by rfl⟩ : syracuseStep 2130245 = 399421) (by norm_num)
theorem B2130533 : Blo 558808 2130533 := bbase (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) (by norm_num)
theorem B1442549 : Blo 558808 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B1344365 : Blo 558808 1344365 := bbase (se 3 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 1344365 = 504137) (by norm_num)
theorem B1344557 : Blo 558808 1344557 := bbase (se 3 (by rfl) ⟨252104, by rfl⟩ : syracuseStep 1344557 = 504209) (by norm_num)
theorem B10781909 : Blo 558808 10781909 := bbase (se 7 (by rfl) ⟨126350, by rfl⟩ : syracuseStep 10781909 = 252701) (by norm_num)
theorem B10257749 : Blo 558808 10257749 := bbase (se 12 (by rfl) ⟨3756, by rfl⟩ : syracuseStep 10257749 = 7513) (by norm_num)
theorem B2131717 : Blo 558808 2131717 := bbase (se 4 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 2131717 = 399697) (by norm_num)
theorem B755525 : Blo 558808 755525 := bbase (se 4 (by rfl) ⟨70830, by rfl⟩ : syracuseStep 755525 = 141661) (by norm_num)
theorem B2132021 : Blo 558808 2132021 := bbase (se 5 (by rfl) ⟨99938, by rfl⟩ : syracuseStep 2132021 = 199877) (by norm_num)
theorem B2427029 : Blo 558808 2427029 := bbase (se 6 (by rfl) ⟨56883, by rfl⟩ : syracuseStep 2427029 = 113767) (by norm_num)
theorem B854309 : Blo 558808 854309 := bbase (se 4 (by rfl) ⟨80091, by rfl⟩ : syracuseStep 854309 = 160183) (by norm_num)
theorem B2394629 : Blo 558808 2394629 := bbase (se 4 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 2394629 = 448993) (by norm_num)
theorem B2886533 : Blo 558808 2886533 := bbase (se 4 (by rfl) ⟨270612, by rfl⟩ : syracuseStep 2886533 = 541225) (by norm_num)
theorem B1346557 : Blo 558808 1346557 := bbase (se 3 (by rfl) ⟨252479, by rfl⟩ : syracuseStep 1346557 = 504959) (by norm_num)
theorem B14421077 : Blo 558808 14421077 := bbase (se 8 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 14421077 = 168997) (by norm_num)
theorem B855317 : Blo 558808 855317 := bbase (se 6 (by rfl) ⟨20046, by rfl⟩ : syracuseStep 855317 = 40093) (by norm_num)
theorem B2690405 : Blo 558808 2690405 := bbase (se 4 (by rfl) ⟨252225, by rfl⟩ : syracuseStep 2690405 = 504451) (by norm_num)
theorem B1347133 : Blo 558808 1347133 := bbase (se 3 (by rfl) ⟨252587, by rfl⟩ : syracuseStep 1347133 = 505175) (by norm_num)
theorem B2920133 : Blo 558808 2920133 := bbase (se 4 (by rfl) ⟨273762, by rfl⟩ : syracuseStep 2920133 = 547525) (by norm_num)
theorem B2723701 : Blo 558808 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B1347461 : Blo 558808 1347461 := bbase (se 4 (by rfl) ⟨126324, by rfl⟩ : syracuseStep 1347461 = 252649) (by norm_num)
theorem B1347517 : Blo 558808 1347517 := bbase (se 3 (by rfl) ⟨252659, by rfl⟩ : syracuseStep 1347517 = 505319) (by norm_num)
theorem B692173 : Blo 558808 692173 := bbase (se 3 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 692173 = 259565) (by norm_num)
theorem B3411925 : Blo 558808 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B2134133 : Blo 558808 2134133 := bbase (se 5 (by rfl) ⟨100037, by rfl⟩ : syracuseStep 2134133 = 200075) (by norm_num)
theorem B1347749 : Blo 558808 1347749 := bbase (se 4 (by rfl) ⟨126351, by rfl⟩ : syracuseStep 1347749 = 252703) (by norm_num)
theorem B2396405 : Blo 558808 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B1347941 : Blo 558808 1347941 := bbase (se 4 (by rfl) ⟨126369, by rfl⟩ : syracuseStep 1347941 = 252739) (by norm_num)
theorem B2560405 : Blo 558808 2560405 := bbase (se 6 (by rfl) ⟨60009, by rfl⟩ : syracuseStep 2560405 = 120019) (by norm_num)
theorem B2134421 : Blo 558808 2134421 := bbase (se 6 (by rfl) ⟨50025, by rfl⟩ : syracuseStep 2134421 = 100051) (by norm_num)
theorem B1708469 : Blo 558808 1708469 := bbase (se 5 (by rfl) ⟨80084, by rfl⟩ : syracuseStep 1708469 = 160169) (by norm_num)
theorem B1217045 : Blo 558808 1217045 := bbase (se 6 (by rfl) ⟨28524, by rfl⟩ : syracuseStep 1217045 = 57049) (by norm_num)
theorem B758693 : Blo 558808 758693 := bbase (se 4 (by rfl) ⟨71127, by rfl⟩ : syracuseStep 758693 = 142255) (by norm_num)
theorem B693257 : Blo 558808 693257 := bbase (se 2 (by rfl) ⟨259971, by rfl⟩ : syracuseStep 693257 = 519943) (by norm_num)
theorem B2397397 : Blo 558808 2397397 := bbase (se 7 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 2397397 = 56189) (by norm_num)
theorem B1348901 : Blo 558808 1348901 := bbase (se 4 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 1348901 = 252919) (by norm_num)
theorem B1414493 : Blo 558808 1414493 := bbase (se 3 (by rfl) ⟨265217, by rfl⟩ : syracuseStep 1414493 = 530435) (by norm_num)
theorem B1218053 : Blo 558808 1218053 := bbase (se 4 (by rfl) ⟨114192, by rfl⟩ : syracuseStep 1218053 = 228385) (by norm_num)
theorem B1414685 : Blo 558808 1414685 := bbase (se 3 (by rfl) ⟨265253, by rfl⟩ : syracuseStep 1414685 = 530507) (by norm_num)
theorem B3184181 : Blo 558808 3184181 := bbase (se 5 (by rfl) ⟨149258, by rfl⟩ : syracuseStep 3184181 = 298517) (by norm_num)
theorem B2135605 : Blo 558808 2135605 := bbase (se 5 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 2135605 = 200213) (by norm_num)
theorem B1513093 : Blo 558808 1513093 := bbase (se 4 (by rfl) ⟨141852, by rfl⟩ : syracuseStep 1513093 = 283705) (by norm_num)
theorem B4265621 : Blo 558808 4265621 := bbase (se 6 (by rfl) ⟨99975, by rfl⟩ : syracuseStep 4265621 = 199951) (by norm_num)
theorem B759493 : Blo 558808 759493 := bbase (se 4 (by rfl) ⟨71202, by rfl⟩ : syracuseStep 759493 = 142405) (by norm_num)
theorem B1513189 : Blo 558808 1513189 := bbase (se 4 (by rfl) ⟨141861, by rfl⟩ : syracuseStep 1513189 = 283723) (by norm_num)
theorem B694057 : Blo 558808 694057 := bbase (se 2 (by rfl) ⟨260271, by rfl⟩ : syracuseStep 694057 = 520543) (by norm_num)
theorem B2135909 : Blo 558808 2135909 := bbase (se 4 (by rfl) ⟨200241, by rfl⟩ : syracuseStep 2135909 = 400483) (by norm_num)
theorem B1415029 : Blo 558808 1415029 := bbase (se 5 (by rfl) ⟨66329, by rfl⟩ : syracuseStep 1415029 = 132659) (by norm_num)
theorem B628681 : Blo 558808 628681 := bbase (se 2 (by rfl) ⟨235755, by rfl⟩ : syracuseStep 628681 = 471511) (by norm_num)
theorem B1415141 : Blo 558808 1415141 := bbase (se 4 (by rfl) ⟨132669, by rfl⟩ : syracuseStep 1415141 = 265339) (by norm_num)
theorem B628717 : Blo 558808 628717 := bbase (se 3 (by rfl) ⟨117884, by rfl⟩ : syracuseStep 628717 = 235769) (by norm_num)
theorem B628753 : Blo 558808 628753 := bbase (se 2 (by rfl) ⟨235782, by rfl⟩ : syracuseStep 628753 = 471565) (by norm_num)
theorem B628789 : Blo 558808 628789 := bbase (se 5 (by rfl) ⟨29474, by rfl⟩ : syracuseStep 628789 = 58949) (by norm_num)
theorem B2693189 : Blo 558808 2693189 := bbase (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) (by norm_num)
theorem B25860181 : Blo 558808 25860181 := bbase (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) (by norm_num)
theorem B628825 : Blo 558808 628825 := bbase (se 2 (by rfl) ⟨235809, by rfl⟩ : syracuseStep 628825 = 471619) (by norm_num)
theorem B628861 : Blo 558808 628861 := bbase (se 3 (by rfl) ⟨117911, by rfl⟩ : syracuseStep 628861 = 235823) (by norm_num)
theorem B628897 : Blo 558808 628897 := bbase (se 2 (by rfl) ⟨235836, by rfl⟩ : syracuseStep 628897 = 471673) (by norm_num)
theorem B1415333 : Blo 558808 1415333 := bbase (se 4 (by rfl) ⟨132687, by rfl⟩ : syracuseStep 1415333 = 265375) (by norm_num)
theorem B628933 : Blo 558808 628933 := bbase (se 4 (by rfl) ⟨58962, by rfl⟩ : syracuseStep 628933 = 117925) (by norm_num)
theorem B5445845 : Blo 558808 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B628969 : Blo 558808 628969 := bbase (se 2 (by rfl) ⟨235863, by rfl⟩ : syracuseStep 628969 = 471727) (by norm_num)
theorem B629005 : Blo 558808 629005 := bbase (se 3 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 629005 = 235877) (by norm_num)
theorem B760109 : Blo 558808 760109 := bbase (se 3 (by rfl) ⟨142520, by rfl⟩ : syracuseStep 760109 = 285041) (by norm_num)
theorem B629041 : Blo 558808 629041 := bbase (se 2 (by rfl) ⟨235890, by rfl⟩ : syracuseStep 629041 = 471781) (by norm_num)
theorem B760141 : Blo 558808 760141 := bbase (se 3 (by rfl) ⟨142526, by rfl⟩ : syracuseStep 760141 = 285053) (by norm_num)
theorem B629077 : Blo 558808 629077 := bbase (se 10 (by rfl) ⟨921, by rfl⟩ : syracuseStep 629077 = 1843) (by norm_num)
theorem B6396245 : Blo 558808 6396245 := bbase (se 10 (by rfl) ⟨9369, by rfl⟩ : syracuseStep 6396245 = 18739) (by norm_num)
theorem B629113 : Blo 558808 629113 := bbase (se 2 (by rfl) ⟨235917, by rfl⟩ : syracuseStep 629113 = 471835) (by norm_num)
theorem B9083285 : Blo 558808 9083285 := bbase (se 6 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 9083285 = 425779) (by norm_num)
theorem B629149 : Blo 558808 629149 := bbase (se 3 (by rfl) ⟨117965, by rfl⟩ : syracuseStep 629149 = 235931) (by norm_num)
theorem B629185 : Blo 558808 629185 := bbase (se 2 (by rfl) ⟨235944, by rfl⟩ : syracuseStep 629185 = 471889) (by norm_num)
theorem B629221 : Blo 558808 629221 := bbase (se 4 (by rfl) ⟨58989, by rfl⟩ : syracuseStep 629221 = 117979) (by norm_num)
theorem B1415677 : Blo 558808 1415677 := bbase (se 3 (by rfl) ⟨265439, by rfl⟩ : syracuseStep 1415677 = 530879) (by norm_num)
theorem B629257 : Blo 558808 629257 := bbase (se 2 (by rfl) ⟨235971, by rfl⟩ : syracuseStep 629257 = 471943) (by norm_num)
theorem B629293 : Blo 558808 629293 := bbase (se 3 (by rfl) ⟨117992, by rfl⟩ : syracuseStep 629293 = 235985) (by norm_num)
theorem B3414581 : Blo 558808 3414581 := bbase (se 5 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 3414581 = 320117) (by norm_num)
theorem B629329 : Blo 558808 629329 := bbase (se 2 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 629329 = 471997) (by norm_num)
theorem B1415789 : Blo 558808 1415789 := bbase (se 3 (by rfl) ⟨265460, by rfl⟩ : syracuseStep 1415789 = 530921) (by norm_num)
theorem B629365 : Blo 558808 629365 := bbase (se 5 (by rfl) ⟨29501, by rfl⟩ : syracuseStep 629365 = 59003) (by norm_num)
theorem B727693 : Blo 558808 727693 := bbase (se 3 (by rfl) ⟨136442, by rfl⟩ : syracuseStep 727693 = 272885) (by norm_num)
theorem B629401 : Blo 558808 629401 := bbase (se 2 (by rfl) ⟨236025, by rfl⟩ : syracuseStep 629401 = 472051) (by norm_num)
theorem B629437 : Blo 558808 629437 := bbase (se 3 (by rfl) ⟨118019, by rfl⟩ : syracuseStep 629437 = 236039) (by norm_num)
theorem B3185365 : Blo 558808 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B629473 : Blo 558808 629473 := bbase (se 2 (by rfl) ⟨236052, by rfl⟩ : syracuseStep 629473 = 472105) (by norm_num)
theorem B629509 : Blo 558808 629509 := bbase (se 4 (by rfl) ⟨59016, by rfl⟩ : syracuseStep 629509 = 118033) (by norm_num)
theorem B1022725 : Blo 558808 1022725 := bbase (se 4 (by rfl) ⟨95880, by rfl⟩ : syracuseStep 1022725 = 191761) (by norm_num)
theorem B629545 : Blo 558808 629545 := bbase (se 2 (by rfl) ⟨236079, by rfl⟩ : syracuseStep 629545 = 472159) (by norm_num)
theorem B1415981 : Blo 558808 1415981 := bbase (se 3 (by rfl) ⟨265496, by rfl⟩ : syracuseStep 1415981 = 530993) (by norm_num)
theorem B629581 : Blo 558808 629581 := bbase (se 3 (by rfl) ⟨118046, by rfl⟩ : syracuseStep 629581 = 236093) (by norm_num)
theorem B8624981 : Blo 558808 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B629617 : Blo 558808 629617 := bbase (se 2 (by rfl) ⟨236106, by rfl⟩ : syracuseStep 629617 = 472213) (by norm_num)
theorem B629653 : Blo 558808 629653 := bbase (se 6 (by rfl) ⟨14757, by rfl⟩ : syracuseStep 629653 = 29515) (by norm_num)
theorem B629689 : Blo 558808 629689 := bbase (se 2 (by rfl) ⟨236133, by rfl⟩ : syracuseStep 629689 = 472267) (by norm_num)
theorem B629725 : Blo 558808 629725 := bbase (se 3 (by rfl) ⟨118073, by rfl⟩ : syracuseStep 629725 = 236147) (by norm_num)
theorem B629761 : Blo 558808 629761 := bbase (se 2 (by rfl) ⟨236160, by rfl⟩ : syracuseStep 629761 = 472321) (by norm_num)
theorem B597017 : Blo 558808 597017 := bbase (se 2 (by rfl) ⟨223881, by rfl⟩ : syracuseStep 597017 = 447763) (by norm_num)
theorem B629797 : Blo 558808 629797 := bbase (se 4 (by rfl) ⟨59043, by rfl⟩ : syracuseStep 629797 = 118087) (by norm_num)
theorem B629833 : Blo 558808 629833 := bbase (se 2 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 629833 = 472375) (by norm_num)
theorem B629869 : Blo 558808 629869 := bbase (se 3 (by rfl) ⟨118100, by rfl⟩ : syracuseStep 629869 = 236201) (by norm_num)
theorem B1416325 : Blo 558808 1416325 := bbase (se 4 (by rfl) ⟨132780, by rfl⟩ : syracuseStep 1416325 = 265561) (by norm_num)
theorem B629905 : Blo 558808 629905 := bbase (se 2 (by rfl) ⟨236214, by rfl⟩ : syracuseStep 629905 = 472429) (by norm_num)
theorem B629941 : Blo 558808 629941 := bbase (se 5 (by rfl) ⟨29528, by rfl⟩ : syracuseStep 629941 = 59057) (by norm_num)
theorem B629977 : Blo 558808 629977 := bbase (se 2 (by rfl) ⟨236241, by rfl⟩ : syracuseStep 629977 = 472483) (by norm_num)
theorem B1416437 : Blo 558808 1416437 := bbase (se 5 (by rfl) ⟨66395, by rfl⟩ : syracuseStep 1416437 = 132791) (by norm_num)
theorem B630013 : Blo 558808 630013 := bbase (se 3 (by rfl) ⟨118127, by rfl⟩ : syracuseStep 630013 = 236255) (by norm_num)
theorem B630049 : Blo 558808 630049 := bbase (se 2 (by rfl) ⟨236268, by rfl⟩ : syracuseStep 630049 = 472537) (by norm_num)
theorem B630085 : Blo 558808 630085 := bbase (se 4 (by rfl) ⟨59070, by rfl⟩ : syracuseStep 630085 = 118141) (by norm_num)
theorem B630121 : Blo 558808 630121 := bbase (se 2 (by rfl) ⟨236295, by rfl⟩ : syracuseStep 630121 = 472591) (by norm_num)
theorem B630157 : Blo 558808 630157 := bbase (se 3 (by rfl) ⟨118154, by rfl⟩ : syracuseStep 630157 = 236309) (by norm_num)
theorem B957853 : Blo 558808 957853 := bbase (se 3 (by rfl) ⟨179597, by rfl⟩ : syracuseStep 957853 = 359195) (by norm_num)
theorem B630193 : Blo 558808 630193 := bbase (se 2 (by rfl) ⟨236322, by rfl⟩ : syracuseStep 630193 = 472645) (by norm_num)
theorem B1416629 : Blo 558808 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B597461 : Blo 558808 597461 := bbase (se 7 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 597461 = 14003) (by norm_num)
theorem B630229 : Blo 558808 630229 := bbase (se 7 (by rfl) ⟨7385, by rfl⟩ : syracuseStep 630229 = 14771) (by norm_num)
theorem B630265 : Blo 558808 630265 := bbase (se 2 (by rfl) ⟨236349, by rfl⟩ : syracuseStep 630265 = 472699) (by norm_num)
theorem B630301 : Blo 558808 630301 := bbase (se 3 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 630301 = 236363) (by norm_num)
theorem B630337 : Blo 558808 630337 := bbase (se 2 (by rfl) ⟨236376, by rfl⟩ : syracuseStep 630337 = 472753) (by norm_num)
theorem B630373 : Blo 558808 630373 := bbase (se 4 (by rfl) ⟨59097, by rfl⟩ : syracuseStep 630373 = 118195) (by norm_num)
theorem B630409 : Blo 558808 630409 := bbase (se 2 (by rfl) ⟨236403, by rfl⟩ : syracuseStep 630409 = 472807) (by norm_num)
theorem B630445 : Blo 558808 630445 := bbase (se 3 (by rfl) ⟨118208, by rfl⟩ : syracuseStep 630445 = 236417) (by norm_num)
theorem B597709 : Blo 558808 597709 := bbase (se 3 (by rfl) ⟨112070, by rfl⟩ : syracuseStep 597709 = 224141) (by norm_num)
theorem B630481 : Blo 558808 630481 := bbase (se 2 (by rfl) ⟨236430, by rfl⟩ : syracuseStep 630481 = 472861) (by norm_num)
theorem B630517 : Blo 558808 630517 := bbase (se 5 (by rfl) ⟨29555, by rfl⟩ : syracuseStep 630517 = 59111) (by norm_num)
theorem B1416973 : Blo 558808 1416973 := bbase (se 3 (by rfl) ⟨265682, by rfl⟩ : syracuseStep 1416973 = 531365) (by norm_num)
theorem B630553 : Blo 558808 630553 := bbase (se 2 (by rfl) ⟨236457, by rfl⟩ : syracuseStep 630553 = 472915) (by norm_num)
theorem B630589 : Blo 558808 630589 := bbase (se 3 (by rfl) ⟨118235, by rfl⟩ : syracuseStep 630589 = 236471) (by norm_num)
theorem B630625 : Blo 558808 630625 := bbase (se 2 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 630625 = 472969) (by norm_num)
theorem B1417085 : Blo 558808 1417085 := bbase (se 3 (by rfl) ⟨265703, by rfl⟩ : syracuseStep 1417085 = 531407) (by norm_num)
theorem B630661 : Blo 558808 630661 := bbase (se 4 (by rfl) ⟨59124, by rfl⟩ : syracuseStep 630661 = 118249) (by norm_num)
theorem B630697 : Blo 558808 630697 := bbase (se 2 (by rfl) ⟨236511, by rfl⟩ : syracuseStep 630697 = 473023) (by norm_num)
theorem B630733 : Blo 558808 630733 := bbase (se 3 (by rfl) ⟨118262, by rfl⟩ : syracuseStep 630733 = 236525) (by norm_num)
theorem B630769 : Blo 558808 630769 := bbase (se 2 (by rfl) ⟨236538, by rfl⟩ : syracuseStep 630769 = 473077) (by norm_num)
theorem B1351669 : Blo 558808 1351669 := bbase (se 5 (by rfl) ⟨63359, by rfl⟩ : syracuseStep 1351669 = 126719) (by norm_num)
theorem B630805 : Blo 558808 630805 := bbase (se 6 (by rfl) ⟨14784, by rfl⟩ : syracuseStep 630805 = 29569) (by norm_num)
theorem B630841 : Blo 558808 630841 := bbase (se 2 (by rfl) ⟨236565, by rfl⟩ : syracuseStep 630841 = 473131) (by norm_num)
theorem B1417277 : Blo 558808 1417277 := bbase (se 3 (by rfl) ⟨265739, by rfl⟩ : syracuseStep 1417277 = 531479) (by norm_num)
theorem B630877 : Blo 558808 630877 := bbase (se 3 (by rfl) ⟨118289, by rfl⟩ : syracuseStep 630877 = 236579) (by norm_num)
theorem B598141 : Blo 558808 598141 := bbase (se 3 (by rfl) ⟨112151, by rfl⟩ : syracuseStep 598141 = 224303) (by norm_num)
theorem B630913 : Blo 558808 630913 := bbase (se 2 (by rfl) ⟨236592, by rfl⟩ : syracuseStep 630913 = 473185) (by norm_num)
theorem B630949 : Blo 558808 630949 := bbase (se 4 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 630949 = 118303) (by norm_num)
theorem B598213 : Blo 558808 598213 := bbase (se 4 (by rfl) ⟨56082, by rfl⟩ : syracuseStep 598213 = 112165) (by norm_num)
theorem B630985 : Blo 558808 630985 := bbase (se 2 (by rfl) ⟨236619, by rfl⟩ : syracuseStep 630985 = 473239) (by norm_num)
theorem B631021 : Blo 558808 631021 := bbase (se 3 (by rfl) ⟨118316, by rfl⟩ : syracuseStep 631021 = 236633) (by norm_num)
theorem B631057 : Blo 558808 631057 := bbase (se 2 (by rfl) ⟨236646, by rfl⟩ : syracuseStep 631057 = 473293) (by norm_num)
theorem B631093 : Blo 558808 631093 := bbase (se 5 (by rfl) ⟨29582, by rfl⟩ : syracuseStep 631093 = 59165) (by norm_num)
theorem B631129 : Blo 558808 631129 := bbase (se 2 (by rfl) ⟨236673, by rfl⟩ : syracuseStep 631129 = 473347) (by norm_num)
theorem B1352045 : Blo 558808 1352045 := bbase (se 3 (by rfl) ⟨253508, by rfl⟩ : syracuseStep 1352045 = 507017) (by norm_num)
theorem B631165 : Blo 558808 631165 := bbase (se 3 (by rfl) ⟨118343, by rfl⟩ : syracuseStep 631165 = 236687) (by norm_num)
theorem B1417621 : Blo 558808 1417621 := bbase (se 6 (by rfl) ⟨33225, by rfl⟩ : syracuseStep 1417621 = 66451) (by norm_num)
theorem B631201 : Blo 558808 631201 := bbase (se 2 (by rfl) ⟨236700, by rfl⟩ : syracuseStep 631201 = 473401) (by norm_num)
theorem B631237 : Blo 558808 631237 := bbase (se 4 (by rfl) ⟨59178, by rfl⟩ : syracuseStep 631237 = 118357) (by norm_num)
theorem B631273 : Blo 558808 631273 := bbase (se 2 (by rfl) ⟨236727, by rfl⟩ : syracuseStep 631273 = 473455) (by norm_num)
theorem B1417733 : Blo 558808 1417733 := bbase (se 4 (by rfl) ⟨132912, by rfl⟩ : syracuseStep 1417733 = 265825) (by norm_num)
theorem B1155589 : Blo 558808 1155589 := bbase (se 4 (by rfl) ⟨108336, by rfl⟩ : syracuseStep 1155589 = 216673) (by norm_num)
theorem B631309 : Blo 558808 631309 := bbase (se 3 (by rfl) ⟨118370, by rfl⟩ : syracuseStep 631309 = 236741) (by norm_num)
theorem B631345 : Blo 558808 631345 := bbase (se 2 (by rfl) ⟨236754, by rfl⟩ : syracuseStep 631345 = 473509) (by norm_num)
theorem B598585 : Blo 558808 598585 := bbase (se 2 (by rfl) ⟨224469, by rfl⟩ : syracuseStep 598585 = 448939) (by norm_num)
theorem B6824533 : Blo 558808 6824533 := bbase (se 8 (by rfl) ⟨39987, by rfl⟩ : syracuseStep 6824533 = 79975) (by norm_num)
theorem B631381 : Blo 558808 631381 := bbase (se 8 (by rfl) ⟨3699, by rfl⟩ : syracuseStep 631381 = 7399) (by norm_num)
theorem B631417 : Blo 558808 631417 := bbase (se 2 (by rfl) ⟨236781, by rfl⟩ : syracuseStep 631417 = 473563) (by norm_num)
theorem B3187349 : Blo 558808 3187349 := bbase (se 6 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 3187349 = 149407) (by norm_num)
theorem B631453 : Blo 558808 631453 := bbase (se 3 (by rfl) ⟨118397, by rfl⟩ : syracuseStep 631453 = 236795) (by norm_num)
theorem B631489 : Blo 558808 631489 := bbase (se 2 (by rfl) ⟨236808, by rfl⟩ : syracuseStep 631489 = 473617) (by norm_num)
theorem B1417925 : Blo 558808 1417925 := bbase (se 4 (by rfl) ⟨132930, by rfl⟩ : syracuseStep 1417925 = 265861) (by norm_num)
theorem B631525 : Blo 558808 631525 := bbase (se 4 (by rfl) ⟨59205, by rfl⟩ : syracuseStep 631525 = 118411) (by norm_num)
theorem B631561 : Blo 558808 631561 := bbase (se 2 (by rfl) ⟨236835, by rfl⟩ : syracuseStep 631561 = 473671) (by norm_num)
theorem B631597 : Blo 558808 631597 := bbase (se 3 (by rfl) ⟨118424, by rfl⟩ : syracuseStep 631597 = 236849) (by norm_num)
theorem B631633 : Blo 558808 631633 := bbase (se 2 (by rfl) ⟨236862, by rfl⟩ : syracuseStep 631633 = 473725) (by norm_num)
theorem B631669 : Blo 558808 631669 := bbase (se 5 (by rfl) ⟨29609, by rfl⟩ : syracuseStep 631669 = 59219) (by norm_num)
theorem B3449749 : Blo 558808 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B631705 : Blo 558808 631705 := bbase (se 2 (by rfl) ⟨236889, by rfl⟩ : syracuseStep 631705 = 473779) (by norm_num)
theorem B598961 : Blo 558808 598961 := bbase (se 2 (by rfl) ⟨224610, by rfl⟩ : syracuseStep 598961 = 449221) (by norm_num)
theorem B631741 : Blo 558808 631741 := bbase (se 3 (by rfl) ⟨118451, by rfl⟩ : syracuseStep 631741 = 236903) (by norm_num)
theorem B631777 : Blo 558808 631777 := bbase (se 2 (by rfl) ⟨236916, by rfl⟩ : syracuseStep 631777 = 473833) (by norm_num)
theorem B599033 : Blo 558808 599033 := bbase (se 2 (by rfl) ⟨224637, by rfl⟩ : syracuseStep 599033 = 449275) (by norm_num)
theorem B631813 : Blo 558808 631813 := bbase (se 4 (by rfl) ⟨59232, by rfl⟩ : syracuseStep 631813 = 118465) (by norm_num)
theorem B1418269 : Blo 558808 1418269 := bbase (se 3 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 1418269 = 531851) (by norm_num)
theorem B631849 : Blo 558808 631849 := bbase (se 2 (by rfl) ⟨236943, by rfl⟩ : syracuseStep 631849 = 473887) (by norm_num)
theorem B631885 : Blo 558808 631885 := bbase (se 3 (by rfl) ⟨118478, by rfl⟩ : syracuseStep 631885 = 236957) (by norm_num)
theorem B795749 : Blo 558808 795749 := bbase (se 4 (by rfl) ⟨74601, by rfl⟩ : syracuseStep 795749 = 149203) (by norm_num)
theorem B631921 : Blo 558808 631921 := bbase (se 2 (by rfl) ⟨236970, by rfl⟩ : syracuseStep 631921 = 473941) (by norm_num)
theorem B1418381 : Blo 558808 1418381 := bbase (se 3 (by rfl) ⟨265946, by rfl⟩ : syracuseStep 1418381 = 531893) (by norm_num)
theorem B631957 : Blo 558808 631957 := bbase (se 6 (by rfl) ⟨14811, by rfl⟩ : syracuseStep 631957 = 29623) (by norm_num)
theorem B599221 : Blo 558808 599221 := bbase (se 5 (by rfl) ⟨28088, by rfl⟩ : syracuseStep 599221 = 56177) (by norm_num)
theorem B631993 : Blo 558808 631993 := bbase (se 2 (by rfl) ⟨236997, by rfl⟩ : syracuseStep 631993 = 473995) (by norm_num)
theorem B632029 : Blo 558808 632029 := bbase (se 3 (by rfl) ⟨118505, by rfl⟩ : syracuseStep 632029 = 237011) (by norm_num)
theorem B632065 : Blo 558808 632065 := bbase (se 2 (by rfl) ⟨237024, by rfl⟩ : syracuseStep 632065 = 474049) (by norm_num)
theorem B2270501 : Blo 558808 2270501 := bbase (se 4 (by rfl) ⟨212859, by rfl⟩ : syracuseStep 2270501 = 425719) (by norm_num)
theorem B632101 : Blo 558808 632101 := bbase (se 4 (by rfl) ⟨59259, by rfl⟩ : syracuseStep 632101 = 118519) (by norm_num)
theorem B632137 : Blo 558808 632137 := bbase (se 2 (by rfl) ⟨237051, by rfl⟩ : syracuseStep 632137 = 474103) (by norm_num)
theorem B1418573 : Blo 558808 1418573 := bbase (se 3 (by rfl) ⟨265982, by rfl⟩ : syracuseStep 1418573 = 531965) (by norm_num)
theorem B599405 : Blo 558808 599405 := bbase (se 3 (by rfl) ⟨112388, by rfl⟩ : syracuseStep 599405 = 224777) (by norm_num)
theorem B632173 : Blo 558808 632173 := bbase (se 3 (by rfl) ⟨118532, by rfl⟩ : syracuseStep 632173 = 237065) (by norm_num)
theorem B632209 : Blo 558808 632209 := bbase (se 2 (by rfl) ⟨237078, by rfl⟩ : syracuseStep 632209 = 474157) (by norm_num)
theorem B632245 : Blo 558808 632245 := bbase (se 5 (by rfl) ⟨29636, by rfl⟩ : syracuseStep 632245 = 59273) (by norm_num)
theorem B632281 : Blo 558808 632281 := bbase (se 2 (by rfl) ⟨237105, by rfl⟩ : syracuseStep 632281 = 474211) (by norm_num)
theorem B632317 : Blo 558808 632317 := bbase (se 3 (by rfl) ⟨118559, by rfl⟩ : syracuseStep 632317 = 237119) (by norm_num)
theorem B2336261 : Blo 558808 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B632353 : Blo 558808 632353 := bbase (se 2 (by rfl) ⟨237132, by rfl⟩ : syracuseStep 632353 = 474265) (by norm_num)
theorem B1025597 : Blo 558808 1025597 := bbase (se 3 (by rfl) ⟨192299, by rfl⟩ : syracuseStep 1025597 = 384599) (by norm_num)
theorem B1517125 : Blo 558808 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B632389 : Blo 558808 632389 := bbase (se 4 (by rfl) ⟨59286, by rfl⟩ : syracuseStep 632389 = 118573) (by norm_num)
theorem B2565701 : Blo 558808 2565701 := bbase (se 4 (by rfl) ⟨240534, by rfl⟩ : syracuseStep 2565701 = 481069) (by norm_num)
theorem B632425 : Blo 558808 632425 := bbase (se 2 (by rfl) ⟨237159, by rfl⟩ : syracuseStep 632425 = 474319) (by norm_num)
theorem B632461 : Blo 558808 632461 := bbase (se 3 (by rfl) ⟨118586, by rfl⟩ : syracuseStep 632461 = 237173) (by norm_num)
theorem B1418917 : Blo 558808 1418917 := bbase (se 4 (by rfl) ⟨133023, by rfl⟩ : syracuseStep 1418917 = 266047) (by norm_num)
theorem B632497 : Blo 558808 632497 := bbase (se 2 (by rfl) ⟨237186, by rfl⟩ : syracuseStep 632497 = 474373) (by norm_num)
theorem B632533 : Blo 558808 632533 := bbase (se 7 (by rfl) ⟨7412, by rfl⟩ : syracuseStep 632533 = 14825) (by norm_num)
theorem B632569 : Blo 558808 632569 := bbase (se 2 (by rfl) ⟨237213, by rfl⟩ : syracuseStep 632569 = 474427) (by norm_num)
theorem B1419029 : Blo 558808 1419029 := bbase (se 6 (by rfl) ⟨33258, by rfl⟩ : syracuseStep 1419029 = 66517) (by norm_num)
theorem B632605 : Blo 558808 632605 := bbase (se 3 (by rfl) ⟨118613, by rfl⟩ : syracuseStep 632605 = 237227) (by norm_num)
theorem B632641 : Blo 558808 632641 := bbase (se 2 (by rfl) ⟨237240, by rfl⟩ : syracuseStep 632641 = 474481) (by norm_num)
theorem B796501 : Blo 558808 796501 := bbase (se 9 (by rfl) ⟨2333, by rfl⟩ : syracuseStep 796501 = 4667) (by norm_num)
theorem B632677 : Blo 558808 632677 := bbase (se 4 (by rfl) ⟨59313, by rfl⟩ : syracuseStep 632677 = 118627) (by norm_num)
theorem B1517429 : Blo 558808 1517429 := bbase (se 5 (by rfl) ⟨71129, by rfl⟩ : syracuseStep 1517429 = 142259) (by norm_num)
theorem B632713 : Blo 558808 632713 := bbase (se 2 (by rfl) ⟨237267, by rfl⟩ : syracuseStep 632713 = 474535) (by norm_num)
theorem B632749 : Blo 558808 632749 := bbase (se 3 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 632749 = 237281) (by norm_num)
theorem B632785 : Blo 558808 632785 := bbase (se 2 (by rfl) ⟨237294, by rfl⟩ : syracuseStep 632785 = 474589) (by norm_num)
theorem B1419221 : Blo 558808 1419221 := bbase (se 7 (by rfl) ⟨16631, by rfl⟩ : syracuseStep 1419221 = 33263) (by norm_num)
theorem B632821 : Blo 558808 632821 := bbase (se 5 (by rfl) ⟨29663, by rfl⟩ : syracuseStep 632821 = 59327) (by norm_num)
theorem B632857 : Blo 558808 632857 := bbase (se 2 (by rfl) ⟨237321, by rfl⟩ : syracuseStep 632857 = 474643) (by norm_num)
theorem B632893 : Blo 558808 632893 := bbase (se 3 (by rfl) ⟨118667, by rfl⟩ : syracuseStep 632893 = 237335) (by norm_num)
theorem B600157 : Blo 558808 600157 := bbase (se 3 (by rfl) ⟨112529, by rfl⟩ : syracuseStep 600157 = 225059) (by norm_num)
theorem B632929 : Blo 558808 632929 := bbase (se 2 (by rfl) ⟨237348, by rfl⟩ : syracuseStep 632929 = 474697) (by norm_num)
theorem B2402405 : Blo 558808 2402405 := bbase (se 4 (by rfl) ⟨225225, by rfl⟩ : syracuseStep 2402405 = 450451) (by norm_num)
theorem B632965 : Blo 558808 632965 := bbase (se 4 (by rfl) ⟨59340, by rfl⟩ : syracuseStep 632965 = 118681) (by norm_num)
theorem B895141 : Blo 558808 895141 := bbase (se 4 (by rfl) ⟨83919, by rfl⟩ : syracuseStep 895141 = 167839) (by norm_num)
theorem B600229 : Blo 558808 600229 := bbase (se 4 (by rfl) ⟨56271, by rfl⟩ : syracuseStep 600229 = 112543) (by norm_num)
theorem B633001 : Blo 558808 633001 := bbase (se 2 (by rfl) ⟨237375, by rfl⟩ : syracuseStep 633001 = 474751) (by norm_num)
theorem B633037 : Blo 558808 633037 := bbase (se 3 (by rfl) ⟨118694, by rfl⟩ : syracuseStep 633037 = 237389) (by norm_num)
theorem B633073 : Blo 558808 633073 := bbase (se 2 (by rfl) ⟨237402, by rfl⟩ : syracuseStep 633073 = 474805) (by norm_num)
theorem B633109 : Blo 558808 633109 := bbase (se 6 (by rfl) ⟨14838, by rfl⟩ : syracuseStep 633109 = 29677) (by norm_num)
theorem B1419565 : Blo 558808 1419565 := bbase (se 3 (by rfl) ⟨266168, by rfl⟩ : syracuseStep 1419565 = 532337) (by norm_num)
theorem B633145 : Blo 558808 633145 := bbase (se 2 (by rfl) ⟨237429, by rfl⟩ : syracuseStep 633145 = 474859) (by norm_num)
theorem B600409 : Blo 558808 600409 := bbase (se 2 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 600409 = 450307) (by norm_num)
theorem B2402693 : Blo 558808 2402693 := bbase (se 4 (by rfl) ⟨225252, by rfl⟩ : syracuseStep 2402693 = 450505) (by norm_num)
theorem B1419677 : Blo 558808 1419677 := bbase (se 3 (by rfl) ⟨266189, by rfl⟩ : syracuseStep 1419677 = 532379) (by norm_num)
theorem B2599445 : Blo 558808 2599445 := bbase (se 6 (by rfl) ⟨60924, by rfl⟩ : syracuseStep 2599445 = 121849) (by norm_num)
theorem B1419869 : Blo 558808 1419869 := bbase (se 3 (by rfl) ⟨266225, by rfl⟩ : syracuseStep 1419869 = 532451) (by norm_num)
theorem B797293 : Blo 558808 797293 := bbase (se 3 (by rfl) ⟨149492, by rfl⟩ : syracuseStep 797293 = 298985) (by norm_num)
theorem B4794997 : Blo 558808 4794997 := bbase (se 5 (by rfl) ⟨224765, by rfl⟩ : syracuseStep 4794997 = 449531) (by norm_num)
theorem B567929 : Blo 558808 567929 := bbase (se 2 (by rfl) ⟨212973, by rfl⟩ : syracuseStep 567929 = 425947) (by norm_num)
theorem B895693 : Blo 558808 895693 := bbase (se 3 (by rfl) ⟨167942, by rfl⟩ : syracuseStep 895693 = 335885) (by norm_num)
theorem B600853 : Blo 558808 600853 := bbase (se 6 (by rfl) ⟨14082, by rfl⟩ : syracuseStep 600853 = 28165) (by norm_num)
theorem B3189557 : Blo 558808 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B600977 : Blo 558808 600977 := bbase (se 2 (by rfl) ⟨225366, by rfl⟩ : syracuseStep 600977 = 450733) (by norm_num)
theorem B1420213 : Blo 558808 1420213 := bbase (se 5 (by rfl) ⟨66572, by rfl⟩ : syracuseStep 1420213 = 133145) (by norm_num)
theorem B797629 : Blo 558808 797629 := bbase (se 3 (by rfl) ⟨149555, by rfl⟩ : syracuseStep 797629 = 299111) (by norm_num)
theorem B895949 : Blo 558808 895949 := bbase (se 3 (by rfl) ⟨167990, by rfl⟩ : syracuseStep 895949 = 335981) (by norm_num)
theorem B1420325 : Blo 558808 1420325 := bbase (se 4 (by rfl) ⟨133155, by rfl⟩ : syracuseStep 1420325 = 266311) (by norm_num)
theorem B2403445 : Blo 558808 2403445 := bbase (se 5 (by rfl) ⟨112661, by rfl⟩ : syracuseStep 2403445 = 225323) (by norm_num)
theorem B1518725 : Blo 558808 1518725 := bbase (se 4 (by rfl) ⟨142380, by rfl⟩ : syracuseStep 1518725 = 284761) (by norm_num)
theorem B797845 : Blo 558808 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B1420517 : Blo 558808 1420517 := bbase (se 4 (by rfl) ⟨133173, by rfl⟩ : syracuseStep 1420517 = 266347) (by norm_num)
theorem B2829653 : Blo 558808 2829653 := bbase (se 11 (by rfl) ⟨2072, by rfl⟩ : syracuseStep 2829653 = 4145) (by norm_num)
theorem B568841 : Blo 558808 568841 := bbase (se 2 (by rfl) ⟨213315, by rfl⟩ : syracuseStep 568841 = 426631) (by norm_num)
theorem B798221 : Blo 558808 798221 := bbase (se 3 (by rfl) ⟨149666, by rfl⟩ : syracuseStep 798221 = 299333) (by norm_num)
theorem B1420861 : Blo 558808 1420861 := bbase (se 3 (by rfl) ⟨266411, by rfl⟩ : syracuseStep 1420861 = 532823) (by norm_num)
theorem B1617509 : Blo 558808 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B896653 : Blo 558808 896653 := bbase (se 3 (by rfl) ⟨168122, by rfl⟩ : syracuseStep 896653 = 336245) (by norm_num)
theorem B1420973 : Blo 558808 1420973 := bbase (se 3 (by rfl) ⟨266432, by rfl⟩ : syracuseStep 1420973 = 532865) (by norm_num)
theorem B2273093 : Blo 558808 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B1421165 : Blo 558808 1421165 := bbase (se 3 (by rfl) ⟨266468, by rfl⟩ : syracuseStep 1421165 = 532937) (by norm_num)
theorem B1257389 : Blo 558808 1257389 := bbase (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) (by norm_num)
theorem B3583925 : Blo 558808 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B1257461 : Blo 558808 1257461 := bbase (se 5 (by rfl) ⟨58943, by rfl⟩ : syracuseStep 1257461 = 117887) (by norm_num)
theorem B1060877 : Blo 558808 1060877 := bbase (se 3 (by rfl) ⟨198914, by rfl⟩ : syracuseStep 1060877 = 397829) (by norm_num)
theorem B897077 : Blo 558808 897077 := bbase (se 5 (by rfl) ⟨42050, by rfl⟩ : syracuseStep 897077 = 84101) (by norm_num)
theorem B1257533 : Blo 558808 1257533 := bbase (se 3 (by rfl) ⟨235787, by rfl⟩ : syracuseStep 1257533 = 471575) (by norm_num)
theorem B1257605 : Blo 558808 1257605 := bbase (se 4 (by rfl) ⟨117900, by rfl⟩ : syracuseStep 1257605 = 235801) (by norm_num)
theorem B1061029 : Blo 558808 1061029 := bbase (se 4 (by rfl) ⟨99471, by rfl⟩ : syracuseStep 1061029 = 198943) (by norm_num)
theorem B1421509 : Blo 558808 1421509 := bbase (se 4 (by rfl) ⟨133266, by rfl⟩ : syracuseStep 1421509 = 266533) (by norm_num)
theorem B1257677 : Blo 558808 1257677 := bbase (se 3 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 1257677 = 471629) (by norm_num)
theorem B2699477 : Blo 558808 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B1257749 : Blo 558808 1257749 := bbase (se 6 (by rfl) ⟨29478, by rfl⟩ : syracuseStep 1257749 = 58957) (by norm_num)
theorem B1421621 : Blo 558808 1421621 := bbase (se 5 (by rfl) ⟨66638, by rfl⟩ : syracuseStep 1421621 = 133277) (by norm_num)
theorem B897365 : Blo 558808 897365 := bbase (se 10 (by rfl) ⟨1314, by rfl⟩ : syracuseStep 897365 = 2629) (by norm_num)
theorem B1257821 : Blo 558808 1257821 := bbase (se 3 (by rfl) ⟨235841, by rfl⟩ : syracuseStep 1257821 = 471683) (by norm_num)
theorem B1257893 : Blo 558808 1257893 := bbase (se 4 (by rfl) ⟨117927, by rfl⟩ : syracuseStep 1257893 = 235855) (by norm_num)
theorem B1913269 : Blo 558808 1913269 := bbase (se 5 (by rfl) ⟨89684, by rfl⟩ : syracuseStep 1913269 = 179369) (by norm_num)
theorem B1061333 : Blo 558808 1061333 := bbase (se 7 (by rfl) ⟨12437, by rfl⟩ : syracuseStep 1061333 = 24875) (by norm_num)
theorem B1257965 : Blo 558808 1257965 := bbase (se 3 (by rfl) ⟨235868, by rfl⟩ : syracuseStep 1257965 = 471737) (by norm_num)
theorem B1421813 : Blo 558808 1421813 := bbase (se 5 (by rfl) ⟨66647, by rfl⟩ : syracuseStep 1421813 = 133295) (by norm_num)
theorem B4796981 : Blo 558808 4796981 := bbase (se 5 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 4796981 = 449717) (by norm_num)
theorem B1258037 : Blo 558808 1258037 := bbase (se 5 (by rfl) ⟨58970, by rfl⟩ : syracuseStep 1258037 = 117941) (by norm_num)
theorem B897589 : Blo 558808 897589 := bbase (se 5 (by rfl) ⟨42074, by rfl⟩ : syracuseStep 897589 = 84149) (by norm_num)
theorem B2830949 : Blo 558808 2830949 := bbase (se 4 (by rfl) ⟨265401, by rfl⟩ : syracuseStep 2830949 = 530803) (by norm_num)
theorem B1258109 : Blo 558808 1258109 := bbase (se 3 (by rfl) ⟨235895, by rfl⟩ : syracuseStep 1258109 = 471791) (by norm_num)
theorem B1258181 : Blo 558808 1258181 := bbase (se 4 (by rfl) ⟨117954, by rfl⟩ : syracuseStep 1258181 = 235909) (by norm_num)
theorem B1258253 : Blo 558808 1258253 := bbase (se 3 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 1258253 = 471845) (by norm_num)
theorem B2274101 : Blo 558808 2274101 := bbase (se 5 (by rfl) ⟨106598, by rfl⟩ : syracuseStep 2274101 = 213197) (by norm_num)
theorem B1422157 : Blo 558808 1422157 := bbase (se 3 (by rfl) ⟨266654, by rfl⟩ : syracuseStep 1422157 = 533309) (by norm_num)
theorem B1258325 : Blo 558808 1258325 := bbase (se 9 (by rfl) ⟨3686, by rfl⟩ : syracuseStep 1258325 = 7373) (by norm_num)
theorem B1258397 : Blo 558808 1258397 := bbase (se 3 (by rfl) ⟨235949, by rfl⟩ : syracuseStep 1258397 = 471899) (by norm_num)
theorem B799645 : Blo 558808 799645 := bbase (se 3 (by rfl) ⟨149933, by rfl⟩ : syracuseStep 799645 = 299867) (by norm_num)
theorem B1422269 : Blo 558808 1422269 := bbase (se 3 (by rfl) ⟨266675, by rfl⟩ : syracuseStep 1422269 = 533351) (by norm_num)
theorem B1258469 : Blo 558808 1258469 := bbase (se 4 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 1258469 = 235963) (by norm_num)
theorem B1258541 : Blo 558808 1258541 := bbase (se 3 (by rfl) ⟨235976, by rfl⟩ : syracuseStep 1258541 = 471953) (by norm_num)
theorem B1258613 : Blo 558808 1258613 := bbase (se 5 (by rfl) ⟨58997, by rfl⟩ : syracuseStep 1258613 = 117995) (by norm_num)
theorem B1422461 : Blo 558808 1422461 := bbase (se 3 (by rfl) ⟨266711, by rfl⟩ : syracuseStep 1422461 = 533423) (by norm_num)
theorem B1258685 : Blo 558808 1258685 := bbase (se 3 (by rfl) ⟨236003, by rfl⟩ : syracuseStep 1258685 = 472007) (by norm_num)
theorem B1062085 : Blo 558808 1062085 := bbase (se 4 (by rfl) ⟨99570, by rfl⟩ : syracuseStep 1062085 = 199141) (by norm_num)
theorem B4273397 : Blo 558808 4273397 := bbase (se 5 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 4273397 = 400631) (by norm_num)
theorem B1258757 : Blo 558808 1258757 := bbase (se 4 (by rfl) ⟨118008, by rfl⟩ : syracuseStep 1258757 = 236017) (by norm_num)
theorem B1258829 : Blo 558808 1258829 := bbase (se 3 (by rfl) ⟨236030, by rfl⟩ : syracuseStep 1258829 = 472061) (by norm_num)
theorem B1062229 : Blo 558808 1062229 := bbase (se 13 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1062229 = 389) (by norm_num)
theorem B1258901 : Blo 558808 1258901 := bbase (se 6 (by rfl) ⟨29505, by rfl⟩ : syracuseStep 1258901 = 59011) (by norm_num)
theorem B1422805 : Blo 558808 1422805 := bbase (se 7 (by rfl) ⟨16673, by rfl⟩ : syracuseStep 1422805 = 33347) (by norm_num)
theorem B1258973 : Blo 558808 1258973 := bbase (se 3 (by rfl) ⟨236057, by rfl⟩ : syracuseStep 1258973 = 472115) (by norm_num)
theorem B800237 : Blo 558808 800237 := bbase (se 3 (by rfl) ⟨150044, by rfl⟩ : syracuseStep 800237 = 300089) (by norm_num)
theorem B1062389 : Blo 558808 1062389 := bbase (se 5 (by rfl) ⟨49799, by rfl⟩ : syracuseStep 1062389 = 99599) (by norm_num)
theorem B1259045 : Blo 558808 1259045 := bbase (se 4 (by rfl) ⟨118035, by rfl⟩ : syracuseStep 1259045 = 236071) (by norm_num)
theorem B800317 : Blo 558808 800317 := bbase (se 3 (by rfl) ⟨150059, by rfl⟩ : syracuseStep 800317 = 300119) (by norm_num)
theorem B1422917 : Blo 558808 1422917 := bbase (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) (by norm_num)
theorem B1259117 : Blo 558808 1259117 := bbase (se 3 (by rfl) ⟨236084, by rfl⟩ : syracuseStep 1259117 = 472169) (by norm_num)
theorem B1062533 : Blo 558808 1062533 := bbase (se 4 (by rfl) ⟨99612, by rfl⟩ : syracuseStep 1062533 = 199225) (by norm_num)
theorem B898717 : Blo 558808 898717 := bbase (se 3 (by rfl) ⟨168509, by rfl⟩ : syracuseStep 898717 = 337019) (by norm_num)
theorem B1259189 : Blo 558808 1259189 := bbase (se 5 (by rfl) ⟨59024, by rfl⟩ : syracuseStep 1259189 = 118049) (by norm_num)
theorem B800437 : Blo 558808 800437 := bbase (se 5 (by rfl) ⟨37520, by rfl⟩ : syracuseStep 800437 = 75041) (by norm_num)
theorem B1259261 : Blo 558808 1259261 := bbase (se 3 (by rfl) ⟨236111, by rfl⟩ : syracuseStep 1259261 = 472223) (by norm_num)
theorem B1423109 : Blo 558808 1423109 := bbase (se 4 (by rfl) ⟨133416, by rfl⟩ : syracuseStep 1423109 = 266833) (by norm_num)
theorem B800533 : Blo 558808 800533 := bbase (se 6 (by rfl) ⟨18762, by rfl⟩ : syracuseStep 800533 = 37525) (by norm_num)
theorem B1259333 : Blo 558808 1259333 := bbase (se 4 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 1259333 = 236125) (by norm_num)
theorem B2832245 : Blo 558808 2832245 := bbase (se 5 (by rfl) ⟨132761, by rfl⟩ : syracuseStep 2832245 = 265523) (by norm_num)
theorem B1259405 : Blo 558808 1259405 := bbase (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) (by norm_num)
theorem B1062821 : Blo 558808 1062821 := bbase (se 4 (by rfl) ⟨99639, by rfl⟩ : syracuseStep 1062821 = 199279) (by norm_num)
theorem B1259477 : Blo 558808 1259477 := bbase (se 7 (by rfl) ⟨14759, by rfl⟩ : syracuseStep 1259477 = 29519) (by norm_num)
theorem B1259549 : Blo 558808 1259549 := bbase (se 3 (by rfl) ⟨236165, by rfl⟩ : syracuseStep 1259549 = 472331) (by norm_num)
theorem B1062973 : Blo 558808 1062973 := bbase (se 3 (by rfl) ⟨199307, by rfl⟩ : syracuseStep 1062973 = 398615) (by norm_num)
theorem B899165 : Blo 558808 899165 := bbase (se 3 (by rfl) ⟨168593, by rfl⟩ : syracuseStep 899165 = 337187) (by norm_num)
theorem B1423453 : Blo 558808 1423453 := bbase (se 3 (by rfl) ⟨266897, by rfl⟩ : syracuseStep 1423453 = 533795) (by norm_num)
theorem B1259621 : Blo 558808 1259621 := bbase (se 4 (by rfl) ⟨118089, by rfl⟩ : syracuseStep 1259621 = 236179) (by norm_num)
theorem B1259693 : Blo 558808 1259693 := bbase (se 3 (by rfl) ⟨236192, by rfl⟩ : syracuseStep 1259693 = 472385) (by norm_num)
theorem B1423565 : Blo 558808 1423565 := bbase (se 3 (by rfl) ⟨266918, by rfl⟩ : syracuseStep 1423565 = 533837) (by norm_num)
theorem B1194205 : Blo 558808 1194205 := bbase (se 3 (by rfl) ⟨223913, by rfl⟩ : syracuseStep 1194205 = 447827) (by norm_num)
theorem B1259765 : Blo 558808 1259765 := bbase (se 5 (by rfl) ⟨59051, by rfl⟩ : syracuseStep 1259765 = 118103) (by norm_num)
theorem B3029237 : Blo 558808 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B801029 : Blo 558808 801029 := bbase (se 4 (by rfl) ⟨75096, by rfl⟩ : syracuseStep 801029 = 150193) (by norm_num)
theorem B1259837 : Blo 558808 1259837 := bbase (se 3 (by rfl) ⟨236219, by rfl⟩ : syracuseStep 1259837 = 472439) (by norm_num)
theorem B36256085 : Blo 558808 36256085 := bbase (se 10 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 36256085 = 106219) (by norm_num)
theorem B1063277 : Blo 558808 1063277 := bbase (se 3 (by rfl) ⟨199364, by rfl⟩ : syracuseStep 1063277 = 398729) (by norm_num)
theorem B1259909 : Blo 558808 1259909 := bbase (se 4 (by rfl) ⟨118116, by rfl⟩ : syracuseStep 1259909 = 236233) (by norm_num)
theorem B1423757 : Blo 558808 1423757 := bbase (se 3 (by rfl) ⟨266954, by rfl⟩ : syracuseStep 1423757 = 533909) (by norm_num)
theorem B1259981 : Blo 558808 1259981 := bbase (se 3 (by rfl) ⟨236246, by rfl⟩ : syracuseStep 1259981 = 472493) (by norm_num)
theorem B1260053 : Blo 558808 1260053 := bbase (se 6 (by rfl) ⟨29532, by rfl⟩ : syracuseStep 1260053 = 59065) (by norm_num)
theorem B1194581 : Blo 558808 1194581 := bbase (se 8 (by rfl) ⟨6999, by rfl⟩ : syracuseStep 1194581 = 13999) (by norm_num)
theorem B1260125 : Blo 558808 1260125 := bbase (se 3 (by rfl) ⟨236273, by rfl⟩ : syracuseStep 1260125 = 472547) (by norm_num)
theorem B1260197 : Blo 558808 1260197 := bbase (se 4 (by rfl) ⟨118143, by rfl⟩ : syracuseStep 1260197 = 236287) (by norm_num)
theorem B1424101 : Blo 558808 1424101 := bbase (se 4 (by rfl) ⟨133509, by rfl⟩ : syracuseStep 1424101 = 267019) (by norm_num)
theorem B1260269 : Blo 558808 1260269 := bbase (se 3 (by rfl) ⟨236300, by rfl⟩ : syracuseStep 1260269 = 472601) (by norm_num)
theorem B1260341 : Blo 558808 1260341 := bbase (se 5 (by rfl) ⟨59078, by rfl⟩ : syracuseStep 1260341 = 118157) (by norm_num)
theorem B1424213 : Blo 558808 1424213 := bbase (se 9 (by rfl) ⟨4172, by rfl⟩ : syracuseStep 1424213 = 8345) (by norm_num)
theorem B4537205 : Blo 558808 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B1260413 : Blo 558808 1260413 := bbase (se 3 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 1260413 = 472655) (by norm_num)
theorem B2702261 : Blo 558808 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B1260485 : Blo 558808 1260485 := bbase (se 4 (by rfl) ⟨118170, by rfl⟩ : syracuseStep 1260485 = 236341) (by norm_num)
theorem B1260557 : Blo 558808 1260557 := bbase (se 3 (by rfl) ⟨236354, by rfl⟩ : syracuseStep 1260557 = 472709) (by norm_num)
theorem B1424405 : Blo 558808 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B3587125 : Blo 558808 3587125 := bbase (se 5 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 3587125 = 336293) (by norm_num)
theorem B1260629 : Blo 558808 1260629 := bbase (se 8 (by rfl) ⟨7386, by rfl⟩ : syracuseStep 1260629 = 14773) (by norm_num)
theorem B1064029 : Blo 558808 1064029 := bbase (se 3 (by rfl) ⟨199505, by rfl⟩ : syracuseStep 1064029 = 399011) (by norm_num)
theorem B2833541 : Blo 558808 2833541 := bbase (se 4 (by rfl) ⟨265644, by rfl⟩ : syracuseStep 2833541 = 531289) (by norm_num)
theorem B1260701 : Blo 558808 1260701 := bbase (se 3 (by rfl) ⟨236381, by rfl⟩ : syracuseStep 1260701 = 472763) (by norm_num)
theorem B1621205 : Blo 558808 1621205 := bbase (se 7 (by rfl) ⟨18998, by rfl⟩ : syracuseStep 1621205 = 37997) (by norm_num)
theorem B1260773 : Blo 558808 1260773 := bbase (se 4 (by rfl) ⟨118197, by rfl⟩ : syracuseStep 1260773 = 236395) (by norm_num)
theorem B1064173 : Blo 558808 1064173 := bbase (se 3 (by rfl) ⟨199532, by rfl⟩ : syracuseStep 1064173 = 399065) (by norm_num)
theorem B1260845 : Blo 558808 1260845 := bbase (se 3 (by rfl) ⟨236408, by rfl⟩ : syracuseStep 1260845 = 472817) (by norm_num)
theorem B1260917 : Blo 558808 1260917 := bbase (se 5 (by rfl) ⟨59105, by rfl⟩ : syracuseStep 1260917 = 118211) (by norm_num)
theorem B1064333 : Blo 558808 1064333 := bbase (se 3 (by rfl) ⟨199562, by rfl⟩ : syracuseStep 1064333 = 399125) (by norm_num)
theorem B769429 : Blo 558808 769429 := bbase (se 6 (by rfl) ⟨18033, by rfl⟩ : syracuseStep 769429 = 36067) (by norm_num)
theorem B1260989 : Blo 558808 1260989 := bbase (se 3 (by rfl) ⟨236435, by rfl⟩ : syracuseStep 1260989 = 472871) (by norm_num)
theorem B1261061 : Blo 558808 1261061 := bbase (se 4 (by rfl) ⟨118224, by rfl⟩ : syracuseStep 1261061 = 236449) (by norm_num)
theorem B1064477 : Blo 558808 1064477 := bbase (se 3 (by rfl) ⟨199589, by rfl⟩ : syracuseStep 1064477 = 399179) (by norm_num)
theorem B638533 : Blo 558808 638533 := bbase (se 4 (by rfl) ⟨59862, by rfl⟩ : syracuseStep 638533 = 119725) (by norm_num)
theorem B900677 : Blo 558808 900677 := bbase (se 4 (by rfl) ⟨84438, by rfl⟩ : syracuseStep 900677 = 168877) (by norm_num)
theorem B1261133 : Blo 558808 1261133 := bbase (se 3 (by rfl) ⟨236462, by rfl⟩ : syracuseStep 1261133 = 472925) (by norm_num)
theorem B1261205 : Blo 558808 1261205 := bbase (se 6 (by rfl) ⟨29559, by rfl⟩ : syracuseStep 1261205 = 59119) (by norm_num)
theorem B900805 : Blo 558808 900805 := bbase (se 4 (by rfl) ⟨84450, by rfl⟩ : syracuseStep 900805 = 168901) (by norm_num)
theorem B1261277 : Blo 558808 1261277 := bbase (se 3 (by rfl) ⟨236489, by rfl⟩ : syracuseStep 1261277 = 472979) (by norm_num)
theorem B1261349 : Blo 558808 1261349 := bbase (se 4 (by rfl) ⟨118251, by rfl⟩ : syracuseStep 1261349 = 236503) (by norm_num)
theorem B1064765 : Blo 558808 1064765 := bbase (se 3 (by rfl) ⟨199643, by rfl⟩ : syracuseStep 1064765 = 399287) (by norm_num)
theorem B1261421 : Blo 558808 1261421 := bbase (se 3 (by rfl) ⟨236516, by rfl⟩ : syracuseStep 1261421 = 473033) (by norm_num)
theorem B1261493 : Blo 558808 1261493 := bbase (se 5 (by rfl) ⟨59132, by rfl⟩ : syracuseStep 1261493 = 118265) (by norm_num)
theorem B1458109 : Blo 558808 1458109 := bbase (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) (by norm_num)
theorem B1064917 : Blo 558808 1064917 := bbase (se 7 (by rfl) ⟨12479, by rfl⟩ : syracuseStep 1064917 = 24959) (by norm_num)
theorem B1261565 : Blo 558808 1261565 := bbase (se 3 (by rfl) ⟨236543, by rfl⟩ : syracuseStep 1261565 = 473087) (by norm_num)
theorem B3227701 : Blo 558808 3227701 := bbase (se 5 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 3227701 = 302597) (by norm_num)
theorem B1261637 : Blo 558808 1261637 := bbase (se 4 (by rfl) ⟨118278, by rfl⟩ : syracuseStep 1261637 = 236557) (by norm_num)
theorem B606289 : Blo 558808 606289 := bbase (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) (by norm_num)
theorem B1261709 : Blo 558808 1261709 := bbase (se 3 (by rfl) ⟨236570, by rfl⟩ : syracuseStep 1261709 = 473141) (by norm_num)
theorem B2015381 : Blo 558808 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B671933 : Blo 558808 671933 := bbase (se 3 (by rfl) ⟨125987, by rfl⟩ : syracuseStep 671933 = 251975) (by norm_num)
theorem B1196221 : Blo 558808 1196221 := bbase (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) (by norm_num)
theorem B1261781 : Blo 558808 1261781 := bbase (se 7 (by rfl) ⟨14786, by rfl⟩ : syracuseStep 1261781 = 29573) (by norm_num)
theorem B1065221 : Blo 558808 1065221 := bbase (se 4 (by rfl) ⟨99864, by rfl⟩ : syracuseStep 1065221 = 199729) (by norm_num)
theorem B2015509 : Blo 558808 2015509 := bbase (se 6 (by rfl) ⟨47238, by rfl⟩ : syracuseStep 2015509 = 94477) (by norm_num)
theorem B1261853 : Blo 558808 1261853 := bbase (se 3 (by rfl) ⟨236597, by rfl⟩ : syracuseStep 1261853 = 473195) (by norm_num)
theorem B1261925 : Blo 558808 1261925 := bbase (se 4 (by rfl) ⟨118305, by rfl⟩ : syracuseStep 1261925 = 236611) (by norm_num)
theorem B2834837 : Blo 558808 2834837 := bbase (se 6 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 2834837 = 132883) (by norm_num)
theorem B1261997 : Blo 558808 1261997 := bbase (se 3 (by rfl) ⟨236624, by rfl⟩ : syracuseStep 1261997 = 473249) (by norm_num)
theorem B672241 : Blo 558808 672241 := bbase (se 2 (by rfl) ⟨252090, by rfl⟩ : syracuseStep 672241 = 504181) (by norm_num)
theorem B1262069 : Blo 558808 1262069 := bbase (se 5 (by rfl) ⟨59159, by rfl⟩ : syracuseStep 1262069 = 118319) (by norm_num)
theorem B6242837 : Blo 558808 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B1262141 : Blo 558808 1262141 := bbase (se 3 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 1262141 = 473303) (by norm_num)
theorem B1262213 : Blo 558808 1262213 := bbase (se 4 (by rfl) ⟨118332, by rfl⟩ : syracuseStep 1262213 = 236665) (by norm_num)
theorem B672409 : Blo 558808 672409 := bbase (se 2 (by rfl) ⟨252153, by rfl⟩ : syracuseStep 672409 = 504307) (by norm_num)
theorem B1262285 : Blo 558808 1262285 := bbase (se 3 (by rfl) ⟨236678, by rfl⟩ : syracuseStep 1262285 = 473357) (by norm_num)
theorem B1262357 : Blo 558808 1262357 := bbase (se 6 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 1262357 = 59173) (by norm_num)
theorem B672605 : Blo 558808 672605 := bbase (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) (by norm_num)
theorem B1262429 : Blo 558808 1262429 := bbase (se 3 (by rfl) ⟨236705, by rfl⟩ : syracuseStep 1262429 = 473411) (by norm_num)
theorem B1262501 : Blo 558808 1262501 := bbase (se 4 (by rfl) ⟨118359, by rfl⟩ : syracuseStep 1262501 = 236719) (by norm_num)
theorem B1262573 : Blo 558808 1262573 := bbase (se 3 (by rfl) ⟨236732, by rfl⟩ : syracuseStep 1262573 = 473465) (by norm_num)
theorem B1065973 : Blo 558808 1065973 := bbase (se 5 (by rfl) ⟨49967, by rfl⟩ : syracuseStep 1065973 = 99935) (by norm_num)
theorem B1197109 : Blo 558808 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B1262645 : Blo 558808 1262645 := bbase (se 5 (by rfl) ⟨59186, by rfl⟩ : syracuseStep 1262645 = 118373) (by norm_num)
theorem B1262717 : Blo 558808 1262717 := bbase (se 3 (by rfl) ⟨236759, by rfl⟩ : syracuseStep 1262717 = 473519) (by norm_num)
theorem B1066117 : Blo 558808 1066117 := bbase (se 4 (by rfl) ⟨99948, by rfl⟩ : syracuseStep 1066117 = 199897) (by norm_num)
theorem B1262789 : Blo 558808 1262789 := bbase (se 4 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 1262789 = 236773) (by norm_num)
theorem B1262861 : Blo 558808 1262861 := bbase (se 3 (by rfl) ⟨236786, by rfl⟩ : syracuseStep 1262861 = 473573) (by norm_num)
theorem B1066277 : Blo 558808 1066277 := bbase (se 4 (by rfl) ⟨99963, by rfl⟩ : syracuseStep 1066277 = 199927) (by norm_num)
theorem B1262933 : Blo 558808 1262933 := bbase (se 12 (by rfl) ⟨462, by rfl⟩ : syracuseStep 1262933 = 925) (by norm_num)
theorem B1263005 : Blo 558808 1263005 := bbase (se 3 (by rfl) ⟨236813, by rfl⟩ : syracuseStep 1263005 = 473627) (by norm_num)
theorem B1066421 : Blo 558808 1066421 := bbase (se 5 (by rfl) ⟨49988, by rfl⟩ : syracuseStep 1066421 = 99977) (by norm_num)
theorem B1263077 : Blo 558808 1263077 := bbase (se 4 (by rfl) ⟨118413, by rfl⟩ : syracuseStep 1263077 = 236827) (by norm_num)
theorem B1197605 : Blo 558808 1197605 := bbase (se 4 (by rfl) ⟨112275, by rfl⟩ : syracuseStep 1197605 = 224551) (by norm_num)
theorem B1263149 : Blo 558808 1263149 := bbase (se 3 (by rfl) ⟨236840, by rfl⟩ : syracuseStep 1263149 = 473681) (by norm_num)
theorem B1263221 : Blo 558808 1263221 := bbase (se 5 (by rfl) ⟨59213, by rfl⟩ : syracuseStep 1263221 = 118427) (by norm_num)
theorem B2836133 : Blo 558808 2836133 := bbase (se 4 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 2836133 = 531775) (by norm_num)
theorem B1263293 : Blo 558808 1263293 := bbase (se 3 (by rfl) ⟨236867, by rfl⟩ : syracuseStep 1263293 = 473735) (by norm_num)
theorem B1066709 : Blo 558808 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B2279125 : Blo 558808 2279125 := bbase (se 7 (by rfl) ⟨26708, by rfl⟩ : syracuseStep 2279125 = 53417) (by norm_num)
theorem B607969 : Blo 558808 607969 := bbase (se 2 (by rfl) ⟨227988, by rfl⟩ : syracuseStep 607969 = 455977) (by norm_num)
theorem B1263365 : Blo 558808 1263365 := bbase (se 4 (by rfl) ⟨118440, by rfl⟩ : syracuseStep 1263365 = 236881) (by norm_num)
theorem B1263437 : Blo 558808 1263437 := bbase (se 3 (by rfl) ⟨236894, by rfl⟩ : syracuseStep 1263437 = 473789) (by norm_num)
theorem B1066861 : Blo 558808 1066861 := bbase (se 3 (by rfl) ⟨200036, by rfl⟩ : syracuseStep 1066861 = 400073) (by norm_num)
theorem B1918853 : Blo 558808 1918853 := bbase (se 4 (by rfl) ⟨179892, by rfl⟩ : syracuseStep 1918853 = 359785) (by norm_num)
theorem B1263509 : Blo 558808 1263509 := bbase (se 6 (by rfl) ⟨29613, by rfl⟩ : syracuseStep 1263509 = 59227) (by norm_num)
theorem B1886165 : Blo 558808 1886165 := bbase (se 7 (by rfl) ⟨22103, by rfl⟩ : syracuseStep 1886165 = 44207) (by norm_num)
theorem B1263581 : Blo 558808 1263581 := bbase (se 3 (by rfl) ⟨236921, by rfl⟩ : syracuseStep 1263581 = 473843) (by norm_num)
theorem B1263653 : Blo 558808 1263653 := bbase (se 4 (by rfl) ⟨118467, by rfl⟩ : syracuseStep 1263653 = 236935) (by norm_num)
theorem B1591397 : Blo 558808 1591397 := bbase (se 4 (by rfl) ⟨149193, by rfl⟩ : syracuseStep 1591397 = 298387) (by norm_num)
theorem B1263725 : Blo 558808 1263725 := bbase (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) (by norm_num)
theorem B1067165 : Blo 558808 1067165 := bbase (se 3 (by rfl) ⟨200093, by rfl⟩ : syracuseStep 1067165 = 400187) (by norm_num)
theorem B1263797 : Blo 558808 1263797 := bbase (se 5 (by rfl) ⟨59240, by rfl⟩ : syracuseStep 1263797 = 118481) (by norm_num)
theorem B1263869 : Blo 558808 1263869 := bbase (se 3 (by rfl) ⟨236975, by rfl⟩ : syracuseStep 1263869 = 473951) (by norm_num)
theorem B1591589 : Blo 558808 1591589 := bbase (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) (by norm_num)
theorem B1263941 : Blo 558808 1263941 := bbase (se 4 (by rfl) ⟨118494, by rfl⟩ : syracuseStep 1263941 = 236989) (by norm_num)
theorem B674177 : Blo 558808 674177 := bbase (se 2 (by rfl) ⟨252816, by rfl⟩ : syracuseStep 674177 = 505633) (by norm_num)
theorem B1886597 : Blo 558808 1886597 := bbase (se 4 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 1886597 = 353737) (by norm_num)
theorem B1198469 : Blo 558808 1198469 := bbase (se 4 (by rfl) ⟨112356, by rfl⟩ : syracuseStep 1198469 = 224713) (by norm_num)
theorem B1264013 : Blo 558808 1264013 := bbase (se 3 (by rfl) ⟨237002, by rfl⟩ : syracuseStep 1264013 = 474005) (by norm_num)
theorem B674201 : Blo 558808 674201 := bbase (se 2 (by rfl) ⟨252825, by rfl⟩ : syracuseStep 674201 = 505651) (by norm_num)
theorem B1264085 : Blo 558808 1264085 := bbase (se 7 (by rfl) ⟨14813, by rfl⟩ : syracuseStep 1264085 = 29627) (by norm_num)
theorem B1198613 : Blo 558808 1198613 := bbase (se 6 (by rfl) ⟨28092, by rfl⟩ : syracuseStep 1198613 = 56185) (by norm_num)
theorem B1264157 : Blo 558808 1264157 := bbase (se 3 (by rfl) ⟨237029, by rfl⟩ : syracuseStep 1264157 = 474059) (by norm_num)
theorem B5130805 : Blo 558808 5130805 := bbase (se 5 (by rfl) ⟨240506, by rfl⟩ : syracuseStep 5130805 = 481013) (by norm_num)
theorem B838229 : Blo 558808 838229 := bbase (se 8 (by rfl) ⟨4911, by rfl⟩ : syracuseStep 838229 = 9823) (by norm_num)
theorem B1264229 : Blo 558808 1264229 := bbase (se 4 (by rfl) ⟨118521, by rfl⟩ : syracuseStep 1264229 = 237043) (by norm_num)
theorem B838253 : Blo 558808 838253 := bbase (se 3 (by rfl) ⟨157172, by rfl⟩ : syracuseStep 838253 = 314345) (by norm_num)
theorem B838277 : Blo 558808 838277 := bbase (se 4 (by rfl) ⟨78588, by rfl⟩ : syracuseStep 838277 = 157177) (by norm_num)
theorem B838301 : Blo 558808 838301 := bbase (se 3 (by rfl) ⟨157181, by rfl⟩ : syracuseStep 838301 = 314363) (by norm_num)
theorem B1264301 : Blo 558808 1264301 := bbase (se 3 (by rfl) ⟨237056, by rfl⟩ : syracuseStep 1264301 = 474113) (by norm_num)
theorem B838325 : Blo 558808 838325 := bbase (se 5 (by rfl) ⟨39296, by rfl⟩ : syracuseStep 838325 = 78593) (by norm_num)
theorem B838349 : Blo 558808 838349 := bbase (se 3 (by rfl) ⟨157190, by rfl⟩ : syracuseStep 838349 = 314381) (by norm_num)
theorem B674509 : Blo 558808 674509 := bbase (se 3 (by rfl) ⟨126470, by rfl⟩ : syracuseStep 674509 = 252941) (by norm_num)
theorem B838373 : Blo 558808 838373 := bbase (se 4 (by rfl) ⟨78597, by rfl⟩ : syracuseStep 838373 = 157195) (by norm_num)
theorem B1264373 : Blo 558808 1264373 := bbase (se 5 (by rfl) ⟨59267, by rfl⟩ : syracuseStep 1264373 = 118535) (by norm_num)
theorem B838397 : Blo 558808 838397 := bbase (se 3 (by rfl) ⟨157199, by rfl⟩ : syracuseStep 838397 = 314399) (by norm_num)
theorem B838421 : Blo 558808 838421 := bbase (se 6 (by rfl) ⟨19650, by rfl⟩ : syracuseStep 838421 = 39301) (by norm_num)
theorem B838445 : Blo 558808 838445 := bbase (se 3 (by rfl) ⟨157208, by rfl⟩ : syracuseStep 838445 = 314417) (by norm_num)
theorem B1887029 : Blo 558808 1887029 := bbase (se 5 (by rfl) ⟨88454, by rfl⟩ : syracuseStep 1887029 = 176909) (by norm_num)
theorem B1264445 : Blo 558808 1264445 := bbase (se 3 (by rfl) ⟨237083, by rfl⟩ : syracuseStep 1264445 = 474167) (by norm_num)
theorem B707393 : Blo 558808 707393 := bbase (se 2 (by rfl) ⟨265272, by rfl⟩ : syracuseStep 707393 = 530545) (by norm_num)
theorem B838469 : Blo 558808 838469 := bbase (se 4 (by rfl) ⟨78606, by rfl⟩ : syracuseStep 838469 = 157213) (by norm_num)
theorem B838493 : Blo 558808 838493 := bbase (se 3 (by rfl) ⟨157217, by rfl⟩ : syracuseStep 838493 = 314435) (by norm_num)
theorem B838517 : Blo 558808 838517 := bbase (se 5 (by rfl) ⟨39305, by rfl⟩ : syracuseStep 838517 = 78611) (by norm_num)
theorem B707449 : Blo 558808 707449 := bbase (se 2 (by rfl) ⟨265293, by rfl⟩ : syracuseStep 707449 = 530587) (by norm_num)
theorem B674681 : Blo 558808 674681 := bbase (se 2 (by rfl) ⟨253005, by rfl⟩ : syracuseStep 674681 = 506011) (by norm_num)
theorem B1264517 : Blo 558808 1264517 := bbase (se 4 (by rfl) ⟨118548, by rfl⟩ : syracuseStep 1264517 = 237097) (by norm_num)
theorem B838541 : Blo 558808 838541 := bbase (se 3 (by rfl) ⟨157226, by rfl⟩ : syracuseStep 838541 = 314453) (by norm_num)
theorem B1067917 : Blo 558808 1067917 := bbase (se 3 (by rfl) ⟨200234, by rfl⟩ : syracuseStep 1067917 = 400469) (by norm_num)
theorem B838565 : Blo 558808 838565 := bbase (se 4 (by rfl) ⟨78615, by rfl⟩ : syracuseStep 838565 = 157231) (by norm_num)
theorem B2837429 : Blo 558808 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B3034037 : Blo 558808 3034037 := bbase (se 5 (by rfl) ⟨142220, by rfl⟩ : syracuseStep 3034037 = 284441) (by norm_num)
theorem B838589 : Blo 558808 838589 := bbase (se 3 (by rfl) ⟨157235, by rfl⟩ : syracuseStep 838589 = 314471) (by norm_num)
theorem B1264589 : Blo 558808 1264589 := bbase (se 3 (by rfl) ⟨237110, by rfl⟩ : syracuseStep 1264589 = 474221) (by norm_num)
theorem B838613 : Blo 558808 838613 := bbase (se 7 (by rfl) ⟨9827, by rfl⟩ : syracuseStep 838613 = 19655) (by norm_num)
theorem B707545 : Blo 558808 707545 := bbase (se 2 (by rfl) ⟨265329, by rfl⟩ : syracuseStep 707545 = 530659) (by norm_num)
theorem B838637 : Blo 558808 838637 := bbase (se 3 (by rfl) ⟨157244, by rfl⟩ : syracuseStep 838637 = 314489) (by norm_num)
theorem B674797 : Blo 558808 674797 := bbase (se 3 (by rfl) ⟨126524, by rfl⟩ : syracuseStep 674797 = 253049) (by norm_num)
theorem B838661 : Blo 558808 838661 := bbase (se 4 (by rfl) ⟨78624, by rfl⟩ : syracuseStep 838661 = 157249) (by norm_num)
theorem B1264661 : Blo 558808 1264661 := bbase (se 6 (by rfl) ⟨29640, by rfl⟩ : syracuseStep 1264661 = 59281) (by norm_num)
theorem B838685 : Blo 558808 838685 := bbase (se 3 (by rfl) ⟨157253, by rfl⟩ : syracuseStep 838685 = 314507) (by norm_num)
theorem B1068061 : Blo 558808 1068061 := bbase (se 3 (by rfl) ⟨200261, by rfl⟩ : syracuseStep 1068061 = 400523) (by norm_num)
theorem B838709 : Blo 558808 838709 := bbase (se 5 (by rfl) ⟨39314, by rfl⟩ : syracuseStep 838709 = 78629) (by norm_num)
theorem B838733 : Blo 558808 838733 := bbase (se 3 (by rfl) ⟨157262, by rfl⟩ : syracuseStep 838733 = 314525) (by norm_num)
theorem B674893 : Blo 558808 674893 := bbase (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) (by norm_num)
theorem B1264733 : Blo 558808 1264733 := bbase (se 3 (by rfl) ⟨237137, by rfl⟩ : syracuseStep 1264733 = 474275) (by norm_num)
theorem B838757 : Blo 558808 838757 := bbase (se 4 (by rfl) ⟨78633, by rfl⟩ : syracuseStep 838757 = 157267) (by norm_num)
theorem B838781 : Blo 558808 838781 := bbase (se 3 (by rfl) ⟨157271, by rfl⟩ : syracuseStep 838781 = 314543) (by norm_num)
theorem B707717 : Blo 558808 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B838805 : Blo 558808 838805 := bbase (se 6 (by rfl) ⟨19659, by rfl⟩ : syracuseStep 838805 = 39319) (by norm_num)
theorem B1264805 : Blo 558808 1264805 := bbase (se 4 (by rfl) ⟨118575, by rfl⟩ : syracuseStep 1264805 = 237151) (by norm_num)
theorem B838829 : Blo 558808 838829 := bbase (se 3 (by rfl) ⟨157280, by rfl⟩ : syracuseStep 838829 = 314561) (by norm_num)
theorem B707773 : Blo 558808 707773 := bbase (se 3 (by rfl) ⟨132707, by rfl⟩ : syracuseStep 707773 = 265415) (by norm_num)
theorem B1068221 : Blo 558808 1068221 := bbase (se 3 (by rfl) ⟨200291, by rfl⟩ : syracuseStep 1068221 = 400583) (by norm_num)
theorem B838853 : Blo 558808 838853 := bbase (se 4 (by rfl) ⟨78642, by rfl⟩ : syracuseStep 838853 = 157285) (by norm_num)
theorem B838877 : Blo 558808 838877 := bbase (se 3 (by rfl) ⟨157289, by rfl⟩ : syracuseStep 838877 = 314579) (by norm_num)
theorem B675037 : Blo 558808 675037 := bbase (se 3 (by rfl) ⟨126569, by rfl⟩ : syracuseStep 675037 = 253139) (by norm_num)
theorem B1887461 : Blo 558808 1887461 := bbase (se 4 (by rfl) ⟨176949, by rfl⟩ : syracuseStep 1887461 = 353899) (by norm_num)
theorem B1264877 : Blo 558808 1264877 := bbase (se 3 (by rfl) ⟨237164, by rfl⟩ : syracuseStep 1264877 = 474329) (by norm_num)
theorem B838901 : Blo 558808 838901 := bbase (se 5 (by rfl) ⟨39323, by rfl⟩ : syracuseStep 838901 = 78647) (by norm_num)
theorem B1199357 : Blo 558808 1199357 := bbase (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) (by norm_num)
theorem B1592581 : Blo 558808 1592581 := bbase (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) (by norm_num)
theorem B838925 : Blo 558808 838925 := bbase (se 3 (by rfl) ⟨157298, by rfl⟩ : syracuseStep 838925 = 314597) (by norm_num)
theorem B707869 : Blo 558808 707869 := bbase (se 3 (by rfl) ⟨132725, by rfl⟩ : syracuseStep 707869 = 265451) (by norm_num)
theorem B838949 : Blo 558808 838949 := bbase (se 4 (by rfl) ⟨78651, by rfl⟩ : syracuseStep 838949 = 157303) (by norm_num)
theorem B1264949 : Blo 558808 1264949 := bbase (se 5 (by rfl) ⟨59294, by rfl⟩ : syracuseStep 1264949 = 118589) (by norm_num)
theorem B838973 : Blo 558808 838973 := bbase (se 3 (by rfl) ⟨157307, by rfl⟩ : syracuseStep 838973 = 314615) (by norm_num)
theorem B1068365 : Blo 558808 1068365 := bbase (se 3 (by rfl) ⟨200318, by rfl⟩ : syracuseStep 1068365 = 400637) (by norm_num)
theorem B838997 : Blo 558808 838997 := bbase (se 11 (by rfl) ⟨614, by rfl⟩ : syracuseStep 838997 = 1229) (by norm_num)
theorem B839021 : Blo 558808 839021 := bbase (se 3 (by rfl) ⟨157316, by rfl⟩ : syracuseStep 839021 = 314633) (by norm_num)
theorem B1265021 : Blo 558808 1265021 := bbase (se 3 (by rfl) ⟨237191, by rfl⟩ : syracuseStep 1265021 = 474383) (by norm_num)
theorem B839045 : Blo 558808 839045 := bbase (se 4 (by rfl) ⟨78660, by rfl⟩ : syracuseStep 839045 = 157321) (by norm_num)
theorem B839069 : Blo 558808 839069 := bbase (se 3 (by rfl) ⟨157325, by rfl⟩ : syracuseStep 839069 = 314651) (by norm_num)
theorem B839093 : Blo 558808 839093 := bbase (se 5 (by rfl) ⟨39332, by rfl⟩ : syracuseStep 839093 = 78665) (by norm_num)
theorem B1265093 : Blo 558808 1265093 := bbase (se 4 (by rfl) ⟨118602, by rfl⟩ : syracuseStep 1265093 = 237205) (by norm_num)
theorem B708041 : Blo 558808 708041 := bbase (se 2 (by rfl) ⟨265515, by rfl⟩ : syracuseStep 708041 = 531031) (by norm_num)
theorem B839117 : Blo 558808 839117 := bbase (se 3 (by rfl) ⟨157334, by rfl⟩ : syracuseStep 839117 = 314669) (by norm_num)
theorem B839141 : Blo 558808 839141 := bbase (se 4 (by rfl) ⟨78669, by rfl⟩ : syracuseStep 839141 = 157339) (by norm_num)
theorem B839165 : Blo 558808 839165 := bbase (se 3 (by rfl) ⟨157343, by rfl⟩ : syracuseStep 839165 = 314687) (by norm_num)
theorem B708097 : Blo 558808 708097 := bbase (se 2 (by rfl) ⟨265536, by rfl⟩ : syracuseStep 708097 = 531073) (by norm_num)
theorem B1265165 : Blo 558808 1265165 := bbase (se 3 (by rfl) ⟨237218, by rfl⟩ : syracuseStep 1265165 = 474437) (by norm_num)
theorem B839189 : Blo 558808 839189 := bbase (se 6 (by rfl) ⟨19668, by rfl⟩ : syracuseStep 839189 = 39337) (by norm_num)
theorem B839213 : Blo 558808 839213 := bbase (se 3 (by rfl) ⟨157352, by rfl⟩ : syracuseStep 839213 = 314705) (by norm_num)
theorem B839237 : Blo 558808 839237 := bbase (se 4 (by rfl) ⟨78678, by rfl⟩ : syracuseStep 839237 = 157357) (by norm_num)
theorem B1265237 : Blo 558808 1265237 := bbase (se 8 (by rfl) ⟨7413, by rfl⟩ : syracuseStep 1265237 = 14827) (by norm_num)
theorem B839261 : Blo 558808 839261 := bbase (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) (by norm_num)
theorem B708193 : Blo 558808 708193 := bbase (se 2 (by rfl) ⟨265572, by rfl⟩ : syracuseStep 708193 = 531145) (by norm_num)
theorem B839285 : Blo 558808 839285 := bbase (se 5 (by rfl) ⟨39341, by rfl⟩ : syracuseStep 839285 = 78683) (by norm_num)
theorem B1298045 : Blo 558808 1298045 := bbase (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) (by norm_num)
theorem B839309 : Blo 558808 839309 := bbase (se 3 (by rfl) ⟨157370, by rfl⟩ : syracuseStep 839309 = 314741) (by norm_num)
theorem B1887893 : Blo 558808 1887893 := bbase (se 6 (by rfl) ⟨44247, by rfl⟩ : syracuseStep 1887893 = 88495) (by norm_num)
theorem B1265309 : Blo 558808 1265309 := bbase (se 3 (by rfl) ⟨237245, by rfl⟩ : syracuseStep 1265309 = 474491) (by norm_num)
theorem B839333 : Blo 558808 839333 := bbase (se 4 (by rfl) ⟨78687, by rfl⟩ : syracuseStep 839333 = 157375) (by norm_num)
theorem B839357 : Blo 558808 839357 := bbase (se 3 (by rfl) ⟨157379, by rfl⟩ : syracuseStep 839357 = 314759) (by norm_num)
theorem B839381 : Blo 558808 839381 := bbase (se 7 (by rfl) ⟨9836, by rfl⟩ : syracuseStep 839381 = 19673) (by norm_num)
theorem B1265381 : Blo 558808 1265381 := bbase (se 4 (by rfl) ⟨118629, by rfl⟩ : syracuseStep 1265381 = 237259) (by norm_num)
theorem B839405 : Blo 558808 839405 := bbase (se 3 (by rfl) ⟨157388, by rfl⟩ : syracuseStep 839405 = 314777) (by norm_num)
theorem B839429 : Blo 558808 839429 := bbase (se 4 (by rfl) ⟨78696, by rfl⟩ : syracuseStep 839429 = 157393) (by norm_num)
theorem B708365 : Blo 558808 708365 := bbase (se 3 (by rfl) ⟨132818, by rfl⟩ : syracuseStep 708365 = 265637) (by norm_num)
theorem B839453 : Blo 558808 839453 := bbase (se 3 (by rfl) ⟨157397, by rfl⟩ : syracuseStep 839453 = 314795) (by norm_num)
theorem B1134373 : Blo 558808 1134373 := bbase (se 4 (by rfl) ⟨106347, by rfl⟩ : syracuseStep 1134373 = 212695) (by norm_num)
theorem B1265453 : Blo 558808 1265453 := bbase (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) (by norm_num)
theorem B839477 : Blo 558808 839477 := bbase (se 5 (by rfl) ⟨39350, by rfl⟩ : syracuseStep 839477 = 78701) (by norm_num)
theorem B708421 : Blo 558808 708421 := bbase (se 4 (by rfl) ⟨66414, by rfl⟩ : syracuseStep 708421 = 132829) (by norm_num)
theorem B839501 : Blo 558808 839501 := bbase (se 3 (by rfl) ⟨157406, by rfl⟩ : syracuseStep 839501 = 314813) (by norm_num)
theorem B839525 : Blo 558808 839525 := bbase (se 4 (by rfl) ⟨78705, by rfl⟩ : syracuseStep 839525 = 157411) (by norm_num)
theorem B1265525 : Blo 558808 1265525 := bbase (se 5 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 1265525 = 118643) (by norm_num)
theorem B839549 : Blo 558808 839549 := bbase (se 3 (by rfl) ⟨157415, by rfl⟩ : syracuseStep 839549 = 314831) (by norm_num)
theorem B839573 : Blo 558808 839573 := bbase (se 6 (by rfl) ⟨19677, by rfl⟩ : syracuseStep 839573 = 39355) (by norm_num)
theorem B708517 : Blo 558808 708517 := bbase (se 4 (by rfl) ⟨66423, by rfl⟩ : syracuseStep 708517 = 132847) (by norm_num)
theorem B839597 : Blo 558808 839597 := bbase (se 3 (by rfl) ⟨157424, by rfl⟩ : syracuseStep 839597 = 314849) (by norm_num)
theorem B1265597 : Blo 558808 1265597 := bbase (se 3 (by rfl) ⟨237299, by rfl⟩ : syracuseStep 1265597 = 474599) (by norm_num)
theorem B839621 : Blo 558808 839621 := bbase (se 4 (by rfl) ⟨78714, by rfl⟩ : syracuseStep 839621 = 157429) (by norm_num)
theorem B7655381 : Blo 558808 7655381 := bbase (se 7 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 7655381 = 179423) (by norm_num)
theorem B839645 : Blo 558808 839645 := bbase (se 3 (by rfl) ⟨157433, by rfl⟩ : syracuseStep 839645 = 314867) (by norm_num)
theorem B1200109 : Blo 558808 1200109 := bbase (se 3 (by rfl) ⟨225020, by rfl⟩ : syracuseStep 1200109 = 450041) (by norm_num)
theorem B839669 : Blo 558808 839669 := bbase (se 5 (by rfl) ⟨39359, by rfl⟩ : syracuseStep 839669 = 78719) (by norm_num)
theorem B1265669 : Blo 558808 1265669 := bbase (se 4 (by rfl) ⟨118656, by rfl⟩ : syracuseStep 1265669 = 237313) (by norm_num)
theorem B839693 : Blo 558808 839693 := bbase (se 3 (by rfl) ⟨157442, by rfl⟩ : syracuseStep 839693 = 314885) (by norm_num)
theorem B839717 : Blo 558808 839717 := bbase (se 4 (by rfl) ⟨78723, by rfl⟩ : syracuseStep 839717 = 157447) (by norm_num)
theorem B839741 : Blo 558808 839741 := bbase (se 3 (by rfl) ⟨157451, by rfl⟩ : syracuseStep 839741 = 314903) (by norm_num)
theorem B1888325 : Blo 558808 1888325 := bbase (se 4 (by rfl) ⟨177030, by rfl⟩ : syracuseStep 1888325 = 354061) (by norm_num)
theorem B1265741 : Blo 558808 1265741 := bbase (se 3 (by rfl) ⟨237326, by rfl⟩ : syracuseStep 1265741 = 474653) (by norm_num)
theorem B708689 : Blo 558808 708689 := bbase (se 2 (by rfl) ⟨265758, by rfl⟩ : syracuseStep 708689 = 531517) (by norm_num)
theorem B839765 : Blo 558808 839765 := bbase (se 8 (by rfl) ⟨4920, by rfl⟩ : syracuseStep 839765 = 9841) (by norm_num)
theorem B839789 : Blo 558808 839789 := bbase (se 3 (by rfl) ⟨157460, by rfl⟩ : syracuseStep 839789 = 314921) (by norm_num)
theorem B1200253 : Blo 558808 1200253 := bbase (se 3 (by rfl) ⟨225047, by rfl⟩ : syracuseStep 1200253 = 450095) (by norm_num)
theorem B839813 : Blo 558808 839813 := bbase (se 4 (by rfl) ⟨78732, by rfl⟩ : syracuseStep 839813 = 157465) (by norm_num)
theorem B708745 : Blo 558808 708745 := bbase (se 2 (by rfl) ⟨265779, by rfl⟩ : syracuseStep 708745 = 531559) (by norm_num)
theorem B1265813 : Blo 558808 1265813 := bbase (se 6 (by rfl) ⟨29667, by rfl⟩ : syracuseStep 1265813 = 59335) (by norm_num)
theorem B839837 : Blo 558808 839837 := bbase (se 3 (by rfl) ⟨157469, by rfl⟩ : syracuseStep 839837 = 314939) (by norm_num)
theorem B839861 : Blo 558808 839861 := bbase (se 5 (by rfl) ⟨39368, by rfl⟩ : syracuseStep 839861 = 78737) (by norm_num)
theorem B2838725 : Blo 558808 2838725 := bbase (se 4 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 2838725 = 532261) (by norm_num)
theorem B839885 : Blo 558808 839885 := bbase (se 3 (by rfl) ⟨157478, by rfl⟩ : syracuseStep 839885 = 314957) (by norm_num)
theorem B1265885 : Blo 558808 1265885 := bbase (se 3 (by rfl) ⟨237353, by rfl⟩ : syracuseStep 1265885 = 474707) (by norm_num)
theorem B839909 : Blo 558808 839909 := bbase (se 4 (by rfl) ⟨78741, by rfl⟩ : syracuseStep 839909 = 157483) (by norm_num)
theorem B708841 : Blo 558808 708841 := bbase (se 2 (by rfl) ⟨265815, by rfl⟩ : syracuseStep 708841 = 531631) (by norm_num)
theorem B839933 : Blo 558808 839933 := bbase (se 3 (by rfl) ⟨157487, by rfl⟩ : syracuseStep 839933 = 314975) (by norm_num)
theorem B3232021 : Blo 558808 3232021 := bbase (se 6 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 3232021 = 151501) (by norm_num)
theorem B839957 : Blo 558808 839957 := bbase (se 6 (by rfl) ⟨19686, by rfl⟩ : syracuseStep 839957 = 39373) (by norm_num)
theorem B1265957 : Blo 558808 1265957 := bbase (se 4 (by rfl) ⟨118683, by rfl⟩ : syracuseStep 1265957 = 237367) (by norm_num)
theorem B839981 : Blo 558808 839981 := bbase (se 3 (by rfl) ⟨157496, by rfl⟩ : syracuseStep 839981 = 314993) (by norm_num)
theorem B840005 : Blo 558808 840005 := bbase (se 4 (by rfl) ⟨78750, by rfl⟩ : syracuseStep 840005 = 157501) (by norm_num)
theorem B1593685 : Blo 558808 1593685 := bbase (se 10 (by rfl) ⟨2334, by rfl⟩ : syracuseStep 1593685 = 4669) (by norm_num)
theorem B840029 : Blo 558808 840029 := bbase (se 3 (by rfl) ⟨157505, by rfl⟩ : syracuseStep 840029 = 315011) (by norm_num)
theorem B1266029 : Blo 558808 1266029 := bbase (se 3 (by rfl) ⟨237380, by rfl⟩ : syracuseStep 1266029 = 474761) (by norm_num)
theorem B840053 : Blo 558808 840053 := bbase (se 5 (by rfl) ⟨39377, by rfl⟩ : syracuseStep 840053 = 78755) (by norm_num)
theorem B840077 : Blo 558808 840077 := bbase (se 3 (by rfl) ⟨157514, by rfl⟩ : syracuseStep 840077 = 315029) (by norm_num)
theorem B709013 : Blo 558808 709013 := bbase (se 6 (by rfl) ⟨16617, by rfl⟩ : syracuseStep 709013 = 33235) (by norm_num)
theorem B840101 : Blo 558808 840101 := bbase (se 4 (by rfl) ⟨78759, by rfl⟩ : syracuseStep 840101 = 157519) (by norm_num)
theorem B1266101 : Blo 558808 1266101 := bbase (se 5 (by rfl) ⟨59348, by rfl⟩ : syracuseStep 1266101 = 118697) (by norm_num)
theorem B840125 : Blo 558808 840125 := bbase (se 3 (by rfl) ⟨157523, by rfl⟩ : syracuseStep 840125 = 315047) (by norm_num)
theorem B709069 : Blo 558808 709069 := bbase (se 3 (by rfl) ⟨132950, by rfl⟩ : syracuseStep 709069 = 265901) (by norm_num)
theorem B840149 : Blo 558808 840149 := bbase (se 7 (by rfl) ⟨9845, by rfl⟩ : syracuseStep 840149 = 19691) (by norm_num)
theorem B3199445 : Blo 558808 3199445 := bbase (se 7 (by rfl) ⟨37493, by rfl⟩ : syracuseStep 3199445 = 74987) (by norm_num)
theorem B840173 : Blo 558808 840173 := bbase (se 3 (by rfl) ⟨157532, by rfl⟩ : syracuseStep 840173 = 315065) (by norm_num)
theorem B1888757 : Blo 558808 1888757 := bbase (se 5 (by rfl) ⟨88535, by rfl⟩ : syracuseStep 1888757 = 177071) (by norm_num)
theorem B1200629 : Blo 558808 1200629 := bbase (se 5 (by rfl) ⟨56279, by rfl⟩ : syracuseStep 1200629 = 112559) (by norm_num)
theorem B1266173 : Blo 558808 1266173 := bbase (se 3 (by rfl) ⟨237407, by rfl⟩ : syracuseStep 1266173 = 474815) (by norm_num)
theorem B840197 : Blo 558808 840197 := bbase (se 4 (by rfl) ⟨78768, by rfl⟩ : syracuseStep 840197 = 157537) (by norm_num)
theorem B840221 : Blo 558808 840221 := bbase (se 3 (by rfl) ⟨157541, by rfl⟩ : syracuseStep 840221 = 315083) (by norm_num)
theorem B709165 : Blo 558808 709165 := bbase (se 3 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 709165 = 265937) (by norm_num)
theorem B840245 : Blo 558808 840245 := bbase (se 5 (by rfl) ⟨39386, by rfl⟩ : syracuseStep 840245 = 78773) (by norm_num)
theorem B1266245 : Blo 558808 1266245 := bbase (se 4 (by rfl) ⟨118710, by rfl⟩ : syracuseStep 1266245 = 237421) (by norm_num)
theorem B840269 : Blo 558808 840269 := bbase (se 3 (by rfl) ⟨157550, by rfl⟩ : syracuseStep 840269 = 315101) (by norm_num)
theorem B840293 : Blo 558808 840293 := bbase (se 4 (by rfl) ⟨78777, by rfl⟩ : syracuseStep 840293 = 157555) (by norm_num)
theorem B840317 : Blo 558808 840317 := bbase (se 3 (by rfl) ⟨157559, by rfl⟩ : syracuseStep 840317 = 315119) (by norm_num)
theorem B1266317 : Blo 558808 1266317 := bbase (se 3 (by rfl) ⟨237434, by rfl⟩ : syracuseStep 1266317 = 474869) (by norm_num)
theorem B840341 : Blo 558808 840341 := bbase (se 6 (by rfl) ⟨19695, by rfl⟩ : syracuseStep 840341 = 39391) (by norm_num)
theorem B840365 : Blo 558808 840365 := bbase (se 3 (by rfl) ⟨157568, by rfl⟩ : syracuseStep 840365 = 315137) (by norm_num)
theorem B840389 : Blo 558808 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B709337 : Blo 558808 709337 := bbase (se 2 (by rfl) ⟨266001, by rfl⟩ : syracuseStep 709337 = 532003) (by norm_num)
theorem B840413 : Blo 558808 840413 := bbase (se 3 (by rfl) ⟨157577, by rfl⟩ : syracuseStep 840413 = 315155) (by norm_num)
theorem B1790693 : Blo 558808 1790693 := bbase (se 4 (by rfl) ⟨167877, by rfl⟩ : syracuseStep 1790693 = 335755) (by norm_num)
theorem B840437 : Blo 558808 840437 := bbase (se 5 (by rfl) ⟨39395, by rfl⟩ : syracuseStep 840437 = 78791) (by norm_num)
theorem B1921781 : Blo 558808 1921781 := bbase (se 5 (by rfl) ⟨90083, by rfl⟩ : syracuseStep 1921781 = 180167) (by norm_num)
theorem B3035893 : Blo 558808 3035893 := bbase (se 5 (by rfl) ⟨142307, by rfl⟩ : syracuseStep 3035893 = 284615) (by norm_num)
theorem B840461 : Blo 558808 840461 := bbase (se 3 (by rfl) ⟨157586, by rfl⟩ : syracuseStep 840461 = 315173) (by norm_num)
theorem B709393 : Blo 558808 709393 := bbase (se 2 (by rfl) ⟨266022, by rfl⟩ : syracuseStep 709393 = 532045) (by norm_num)
theorem B840485 : Blo 558808 840485 := bbase (se 4 (by rfl) ⟨78795, by rfl⟩ : syracuseStep 840485 = 157591) (by norm_num)
theorem B3068725 : Blo 558808 3068725 := bbase (se 5 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 3068725 = 287693) (by norm_num)
theorem B840509 : Blo 558808 840509 := bbase (se 3 (by rfl) ⟨157595, by rfl⟩ : syracuseStep 840509 = 315191) (by norm_num)
theorem B840533 : Blo 558808 840533 := bbase (se 9 (by rfl) ⟨2462, by rfl⟩ : syracuseStep 840533 = 4925) (by norm_num)
theorem B1200997 : Blo 558808 1200997 := bbase (se 4 (by rfl) ⟨112593, by rfl⟩ : syracuseStep 1200997 = 225187) (by norm_num)
theorem B840557 : Blo 558808 840557 := bbase (se 3 (by rfl) ⟨157604, by rfl⟩ : syracuseStep 840557 = 315209) (by norm_num)
theorem B709489 : Blo 558808 709489 := bbase (se 2 (by rfl) ⟨266058, by rfl⟩ : syracuseStep 709489 = 532117) (by norm_num)
theorem B840581 : Blo 558808 840581 := bbase (se 4 (by rfl) ⟨78804, by rfl⟩ : syracuseStep 840581 = 157609) (by norm_num)
theorem B840605 : Blo 558808 840605 := bbase (se 3 (by rfl) ⟨157613, by rfl⟩ : syracuseStep 840605 = 315227) (by norm_num)
theorem B1889189 : Blo 558808 1889189 := bbase (se 4 (by rfl) ⟨177111, by rfl⟩ : syracuseStep 1889189 = 354223) (by norm_num)
theorem B840629 : Blo 558808 840629 := bbase (se 5 (by rfl) ⟨39404, by rfl⟩ : syracuseStep 840629 = 78809) (by norm_num)
theorem B840653 : Blo 558808 840653 := bbase (se 3 (by rfl) ⟨157622, by rfl⟩ : syracuseStep 840653 = 315245) (by norm_num)
theorem B3593173 : Blo 558808 3593173 := bbase (se 7 (by rfl) ⟨42107, by rfl⟩ : syracuseStep 3593173 = 84215) (by norm_num)
theorem B840677 : Blo 558808 840677 := bbase (se 4 (by rfl) ⟨78813, by rfl⟩ : syracuseStep 840677 = 157627) (by norm_num)
theorem B1463269 : Blo 558808 1463269 := bbase (se 4 (by rfl) ⟨137181, by rfl⟩ : syracuseStep 1463269 = 274363) (by norm_num)
theorem B840701 : Blo 558808 840701 := bbase (se 3 (by rfl) ⟨157631, by rfl⟩ : syracuseStep 840701 = 315263) (by norm_num)
theorem B840725 : Blo 558808 840725 := bbase (se 6 (by rfl) ⟨19704, by rfl⟩ : syracuseStep 840725 = 39409) (by norm_num)
theorem B709661 : Blo 558808 709661 := bbase (se 3 (by rfl) ⟨133061, by rfl⟩ : syracuseStep 709661 = 266123) (by norm_num)
theorem B840749 : Blo 558808 840749 := bbase (se 3 (by rfl) ⟨157640, by rfl⟩ : syracuseStep 840749 = 315281) (by norm_num)
theorem B840773 : Blo 558808 840773 := bbase (se 4 (by rfl) ⟨78822, by rfl⟩ : syracuseStep 840773 = 157645) (by norm_num)
theorem B709717 : Blo 558808 709717 := bbase (se 8 (by rfl) ⟨4158, by rfl⟩ : syracuseStep 709717 = 8317) (by norm_num)
theorem B840797 : Blo 558808 840797 := bbase (se 3 (by rfl) ⟨157649, by rfl⟩ : syracuseStep 840797 = 315299) (by norm_num)
theorem B840821 : Blo 558808 840821 := bbase (se 5 (by rfl) ⟨39413, by rfl⟩ : syracuseStep 840821 = 78827) (by norm_num)
theorem B840845 : Blo 558808 840845 := bbase (se 3 (by rfl) ⟨157658, by rfl⟩ : syracuseStep 840845 = 315317) (by norm_num)
theorem B840869 : Blo 558808 840869 := bbase (se 4 (by rfl) ⟨78831, by rfl⟩ : syracuseStep 840869 = 157663) (by norm_num)
theorem B709813 : Blo 558808 709813 := bbase (se 5 (by rfl) ⟨33272, by rfl⟩ : syracuseStep 709813 = 66545) (by norm_num)
theorem B840893 : Blo 558808 840893 := bbase (se 3 (by rfl) ⟨157667, by rfl⟩ : syracuseStep 840893 = 315335) (by norm_num)
theorem B840917 : Blo 558808 840917 := bbase (se 7 (by rfl) ⟨9854, by rfl⟩ : syracuseStep 840917 = 19709) (by norm_num)
theorem B840941 : Blo 558808 840941 := bbase (se 3 (by rfl) ⟨157676, by rfl⟩ : syracuseStep 840941 = 315353) (by norm_num)
theorem B840965 : Blo 558808 840965 := bbase (se 4 (by rfl) ⟨78840, by rfl⟩ : syracuseStep 840965 = 157681) (by norm_num)
theorem B840989 : Blo 558808 840989 := bbase (se 3 (by rfl) ⟨157685, by rfl⟩ : syracuseStep 840989 = 315371) (by norm_num)
theorem B841013 : Blo 558808 841013 := bbase (se 5 (by rfl) ⟨39422, by rfl⟩ : syracuseStep 841013 = 78845) (by norm_num)
theorem B841037 : Blo 558808 841037 := bbase (se 3 (by rfl) ⟨157694, by rfl⟩ : syracuseStep 841037 = 315389) (by norm_num)
theorem B1889621 : Blo 558808 1889621 := bbase (se 15 (by rfl) ⟨86, by rfl⟩ : syracuseStep 1889621 = 173) (by norm_num)
theorem B709985 : Blo 558808 709985 := bbase (se 2 (by rfl) ⟨266244, by rfl⟩ : syracuseStep 709985 = 532489) (by norm_num)
theorem B841061 : Blo 558808 841061 := bbase (se 4 (by rfl) ⟨78849, by rfl⟩ : syracuseStep 841061 = 157699) (by norm_num)
theorem B841085 : Blo 558808 841085 := bbase (se 3 (by rfl) ⟨157703, by rfl⟩ : syracuseStep 841085 = 315407) (by norm_num)
theorem B841109 : Blo 558808 841109 := bbase (se 6 (by rfl) ⟨19713, by rfl⟩ : syracuseStep 841109 = 39427) (by norm_num)
theorem B710041 : Blo 558808 710041 := bbase (se 2 (by rfl) ⟨266265, by rfl⟩ : syracuseStep 710041 = 532531) (by norm_num)
theorem B841133 : Blo 558808 841133 := bbase (se 3 (by rfl) ⟨157712, by rfl⟩ : syracuseStep 841133 = 315425) (by norm_num)
theorem B1136053 : Blo 558808 1136053 := bbase (se 5 (by rfl) ⟨53252, by rfl⟩ : syracuseStep 1136053 = 106505) (by norm_num)
theorem B841157 : Blo 558808 841157 := bbase (se 4 (by rfl) ⟨78858, by rfl⟩ : syracuseStep 841157 = 157717) (by norm_num)
theorem B2840021 : Blo 558808 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B841181 : Blo 558808 841181 := bbase (se 3 (by rfl) ⟨157721, by rfl⟩ : syracuseStep 841181 = 315443) (by norm_num)
theorem B1136117 : Blo 558808 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B841205 : Blo 558808 841205 := bbase (se 5 (by rfl) ⟨39431, by rfl⟩ : syracuseStep 841205 = 78863) (by norm_num)
theorem B710137 : Blo 558808 710137 := bbase (se 2 (by rfl) ⟨266301, by rfl⟩ : syracuseStep 710137 = 532603) (by norm_num)
theorem B841229 : Blo 558808 841229 := bbase (se 3 (by rfl) ⟨157730, by rfl⟩ : syracuseStep 841229 = 315461) (by norm_num)
theorem B841253 : Blo 558808 841253 := bbase (se 4 (by rfl) ⟨78867, by rfl⟩ : syracuseStep 841253 = 157735) (by norm_num)
theorem B841277 : Blo 558808 841277 := bbase (se 3 (by rfl) ⟨157739, by rfl⟩ : syracuseStep 841277 = 315479) (by norm_num)
theorem B841301 : Blo 558808 841301 := bbase (se 8 (by rfl) ⟨4929, by rfl⟩ : syracuseStep 841301 = 9859) (by norm_num)
theorem B841325 : Blo 558808 841325 := bbase (se 3 (by rfl) ⟨157748, by rfl⟩ : syracuseStep 841325 = 315497) (by norm_num)
theorem B841349 : Blo 558808 841349 := bbase (se 4 (by rfl) ⟨78876, by rfl⟩ : syracuseStep 841349 = 157753) (by norm_num)
theorem B841373 : Blo 558808 841373 := bbase (se 3 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 841373 = 315515) (by norm_num)
theorem B710309 : Blo 558808 710309 := bbase (se 4 (by rfl) ⟨66591, by rfl⟩ : syracuseStep 710309 = 133183) (by norm_num)
theorem B841397 : Blo 558808 841397 := bbase (se 5 (by rfl) ⟨39440, by rfl⟩ : syracuseStep 841397 = 78881) (by norm_num)
theorem B841421 : Blo 558808 841421 := bbase (se 3 (by rfl) ⟨157766, by rfl⟩ : syracuseStep 841421 = 315533) (by norm_num)
theorem B710365 : Blo 558808 710365 := bbase (se 3 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 710365 = 266387) (by norm_num)
theorem B841445 : Blo 558808 841445 := bbase (se 4 (by rfl) ⟨78885, by rfl⟩ : syracuseStep 841445 = 157771) (by norm_num)
theorem B808685 : Blo 558808 808685 := bbase (se 3 (by rfl) ⟨151628, by rfl⟩ : syracuseStep 808685 = 303257) (by norm_num)
theorem B841469 : Blo 558808 841469 := bbase (se 3 (by rfl) ⟨157775, by rfl⟩ : syracuseStep 841469 = 315551) (by norm_num)
theorem B1890053 : Blo 558808 1890053 := bbase (se 4 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 1890053 = 354385) (by norm_num)
theorem B2152213 : Blo 558808 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B841493 : Blo 558808 841493 := bbase (se 6 (by rfl) ⟨19722, by rfl⟩ : syracuseStep 841493 = 39445) (by norm_num)
theorem B841517 : Blo 558808 841517 := bbase (se 3 (by rfl) ⟨157784, by rfl⟩ : syracuseStep 841517 = 315569) (by norm_num)
theorem B1595189 : Blo 558808 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B710461 : Blo 558808 710461 := bbase (se 3 (by rfl) ⟨133211, by rfl⟩ : syracuseStep 710461 = 266423) (by norm_num)
theorem B841541 : Blo 558808 841541 := bbase (se 4 (by rfl) ⟨78894, by rfl⟩ : syracuseStep 841541 = 157789) (by norm_num)
theorem B841565 : Blo 558808 841565 := bbase (se 3 (by rfl) ⟨157793, by rfl⟩ : syracuseStep 841565 = 315587) (by norm_num)
theorem B841589 : Blo 558808 841589 := bbase (se 5 (by rfl) ⟨39449, by rfl⟩ : syracuseStep 841589 = 78899) (by norm_num)
theorem B841613 : Blo 558808 841613 := bbase (se 3 (by rfl) ⟨157802, by rfl⟩ : syracuseStep 841613 = 315605) (by norm_num)
theorem B841637 : Blo 558808 841637 := bbase (se 4 (by rfl) ⟨78903, by rfl⟩ : syracuseStep 841637 = 157807) (by norm_num)
theorem B841661 : Blo 558808 841661 := bbase (se 3 (by rfl) ⟨157811, by rfl⟩ : syracuseStep 841661 = 315623) (by norm_num)
theorem B841685 : Blo 558808 841685 := bbase (se 7 (by rfl) ⟨9863, by rfl⟩ : syracuseStep 841685 = 19727) (by norm_num)
theorem B1791973 : Blo 558808 1791973 := bbase (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) (by norm_num)
theorem B710633 : Blo 558808 710633 := bbase (se 2 (by rfl) ⟨266487, by rfl⟩ : syracuseStep 710633 = 532975) (by norm_num)
theorem B841709 : Blo 558808 841709 := bbase (se 3 (by rfl) ⟨157820, by rfl⟩ : syracuseStep 841709 = 315641) (by norm_num)
theorem B1366021 : Blo 558808 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B841733 : Blo 558808 841733 := bbase (se 4 (by rfl) ⟨78912, by rfl⟩ : syracuseStep 841733 = 157825) (by norm_num)
theorem B841757 : Blo 558808 841757 := bbase (se 3 (by rfl) ⟨157829, by rfl⟩ : syracuseStep 841757 = 315659) (by norm_num)
theorem B710689 : Blo 558808 710689 := bbase (se 2 (by rfl) ⟨266508, by rfl⟩ : syracuseStep 710689 = 533017) (by norm_num)
theorem B841781 : Blo 558808 841781 := bbase (se 5 (by rfl) ⟨39458, by rfl⟩ : syracuseStep 841781 = 78917) (by norm_num)
theorem B841805 : Blo 558808 841805 := bbase (se 3 (by rfl) ⟨157838, by rfl⟩ : syracuseStep 841805 = 315677) (by norm_num)
theorem B841829 : Blo 558808 841829 := bbase (se 4 (by rfl) ⟨78921, by rfl⟩ : syracuseStep 841829 = 157843) (by norm_num)
theorem B841853 : Blo 558808 841853 := bbase (se 3 (by rfl) ⟨157847, by rfl⟩ : syracuseStep 841853 = 315695) (by norm_num)
theorem B710785 : Blo 558808 710785 := bbase (se 2 (by rfl) ⟨266544, by rfl⟩ : syracuseStep 710785 = 533089) (by norm_num)
theorem B841877 : Blo 558808 841877 := bbase (se 6 (by rfl) ⟨19731, by rfl⟩ : syracuseStep 841877 = 39463) (by norm_num)
theorem B841901 : Blo 558808 841901 := bbase (se 3 (by rfl) ⟨157856, by rfl⟩ : syracuseStep 841901 = 315713) (by norm_num)
theorem B1890485 : Blo 558808 1890485 := bbase (se 5 (by rfl) ⟨88616, by rfl⟩ : syracuseStep 1890485 = 177233) (by norm_num)
theorem B841925 : Blo 558808 841925 := bbase (se 4 (by rfl) ⟨78930, by rfl⟩ : syracuseStep 841925 = 157861) (by norm_num)
theorem B841949 : Blo 558808 841949 := bbase (se 3 (by rfl) ⟨157865, by rfl⟩ : syracuseStep 841949 = 315731) (by norm_num)
theorem B841973 : Blo 558808 841973 := bbase (se 5 (by rfl) ⟨39467, by rfl⟩ : syracuseStep 841973 = 78935) (by norm_num)
theorem B841997 : Blo 558808 841997 := bbase (se 3 (by rfl) ⟨157874, by rfl⟩ : syracuseStep 841997 = 315749) (by norm_num)
theorem B842021 : Blo 558808 842021 := bbase (se 4 (by rfl) ⟨78939, by rfl⟩ : syracuseStep 842021 = 157879) (by norm_num)
theorem B710957 : Blo 558808 710957 := bbase (se 3 (by rfl) ⟨133304, by rfl⟩ : syracuseStep 710957 = 266609) (by norm_num)
theorem B842045 : Blo 558808 842045 := bbase (se 3 (by rfl) ⟨157883, by rfl⟩ : syracuseStep 842045 = 315767) (by norm_num)
theorem B842069 : Blo 558808 842069 := bbase (se 10 (by rfl) ⟨1233, by rfl⟩ : syracuseStep 842069 = 2467) (by norm_num)
theorem B711013 : Blo 558808 711013 := bbase (se 4 (by rfl) ⟨66657, by rfl⟩ : syracuseStep 711013 = 133315) (by norm_num)
theorem B842093 : Blo 558808 842093 := bbase (se 3 (by rfl) ⟨157892, by rfl⟩ : syracuseStep 842093 = 315785) (by norm_num)
theorem B842117 : Blo 558808 842117 := bbase (se 4 (by rfl) ⟨78948, by rfl⟩ : syracuseStep 842117 = 157897) (by norm_num)
theorem B842141 : Blo 558808 842141 := bbase (se 3 (by rfl) ⟨157901, by rfl⟩ : syracuseStep 842141 = 315803) (by norm_num)
theorem B842165 : Blo 558808 842165 := bbase (se 5 (by rfl) ⟨39476, by rfl⟩ : syracuseStep 842165 = 78953) (by norm_num)
theorem B711109 : Blo 558808 711109 := bbase (se 4 (by rfl) ⟨66666, by rfl⟩ : syracuseStep 711109 = 133333) (by norm_num)
theorem B842189 : Blo 558808 842189 := bbase (se 3 (by rfl) ⟨157910, by rfl⟩ : syracuseStep 842189 = 315821) (by norm_num)
theorem B4250069 : Blo 558808 4250069 := bbase (se 7 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 4250069 = 99611) (by norm_num)
theorem B842213 : Blo 558808 842213 := bbase (se 4 (by rfl) ⟨78957, by rfl⟩ : syracuseStep 842213 = 157915) (by norm_num)
theorem B842237 : Blo 558808 842237 := bbase (se 3 (by rfl) ⟨157919, by rfl⟩ : syracuseStep 842237 = 315839) (by norm_num)
theorem B842261 : Blo 558808 842261 := bbase (se 6 (by rfl) ⟨19740, by rfl⟩ : syracuseStep 842261 = 39481) (by norm_num)
theorem B842285 : Blo 558808 842285 := bbase (se 3 (by rfl) ⟨157928, by rfl⟩ : syracuseStep 842285 = 315857) (by norm_num)
theorem B842309 : Blo 558808 842309 := bbase (se 4 (by rfl) ⟨78966, by rfl⟩ : syracuseStep 842309 = 157933) (by norm_num)
theorem B842333 : Blo 558808 842333 := bbase (se 3 (by rfl) ⟨157937, by rfl⟩ : syracuseStep 842333 = 315875) (by norm_num)
theorem B1890917 : Blo 558808 1890917 := bbase (se 4 (by rfl) ⟨177273, by rfl⟩ : syracuseStep 1890917 = 354547) (by norm_num)
theorem B711281 : Blo 558808 711281 := bbase (se 2 (by rfl) ⟨266730, by rfl⟩ : syracuseStep 711281 = 533461) (by norm_num)
theorem B842357 : Blo 558808 842357 := bbase (se 5 (by rfl) ⟨39485, by rfl⟩ : syracuseStep 842357 = 78971) (by norm_num)
theorem B842381 : Blo 558808 842381 := bbase (se 3 (by rfl) ⟨157946, by rfl⟩ : syracuseStep 842381 = 315893) (by norm_num)
theorem B842405 : Blo 558808 842405 := bbase (se 4 (by rfl) ⟨78975, by rfl⟩ : syracuseStep 842405 = 157951) (by norm_num)
theorem B711337 : Blo 558808 711337 := bbase (se 2 (by rfl) ⟨266751, by rfl⟩ : syracuseStep 711337 = 533503) (by norm_num)
theorem B842429 : Blo 558808 842429 := bbase (se 3 (by rfl) ⟨157955, by rfl⟩ : syracuseStep 842429 = 315911) (by norm_num)
theorem B842453 : Blo 558808 842453 := bbase (se 7 (by rfl) ⟨9872, by rfl⟩ : syracuseStep 842453 = 19745) (by norm_num)
theorem B2841317 : Blo 558808 2841317 := bbase (se 4 (by rfl) ⟨266373, by rfl⟩ : syracuseStep 2841317 = 532747) (by norm_num)
theorem B842477 : Blo 558808 842477 := bbase (se 3 (by rfl) ⟨157964, by rfl⟩ : syracuseStep 842477 = 315929) (by norm_num)
theorem B842501 : Blo 558808 842501 := bbase (se 4 (by rfl) ⟨78984, by rfl⟩ : syracuseStep 842501 = 157969) (by norm_num)
theorem B711433 : Blo 558808 711433 := bbase (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) (by norm_num)
theorem B3824405 : Blo 558808 3824405 := bbase (se 6 (by rfl) ⟨89634, by rfl⟩ : syracuseStep 3824405 = 179269) (by norm_num)
theorem B842525 : Blo 558808 842525 := bbase (se 3 (by rfl) ⟨157973, by rfl⟩ : syracuseStep 842525 = 315947) (by norm_num)
theorem B842549 : Blo 558808 842549 := bbase (se 5 (by rfl) ⟨39494, by rfl⟩ : syracuseStep 842549 = 78989) (by norm_num)
theorem B842573 : Blo 558808 842573 := bbase (se 3 (by rfl) ⟨157982, by rfl⟩ : syracuseStep 842573 = 315965) (by norm_num)
theorem B842597 : Blo 558808 842597 := bbase (se 4 (by rfl) ⟨78993, by rfl⟩ : syracuseStep 842597 = 157987) (by norm_num)
theorem B842621 : Blo 558808 842621 := bbase (se 3 (by rfl) ⟨157991, by rfl⟩ : syracuseStep 842621 = 315983) (by norm_num)
theorem B842645 : Blo 558808 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B842669 : Blo 558808 842669 := bbase (se 3 (by rfl) ⟨158000, by rfl⟩ : syracuseStep 842669 = 316001) (by norm_num)
theorem B711605 : Blo 558808 711605 := bbase (se 5 (by rfl) ⟨33356, by rfl⟩ : syracuseStep 711605 = 66713) (by norm_num)
theorem B842693 : Blo 558808 842693 := bbase (se 4 (by rfl) ⟨79002, by rfl⟩ : syracuseStep 842693 = 158005) (by norm_num)
theorem B842717 : Blo 558808 842717 := bbase (se 3 (by rfl) ⟨158009, by rfl⟩ : syracuseStep 842717 = 316019) (by norm_num)
theorem B711661 : Blo 558808 711661 := bbase (se 3 (by rfl) ⟨133436, by rfl⟩ : syracuseStep 711661 = 266873) (by norm_num)
theorem B842741 : Blo 558808 842741 := bbase (se 5 (by rfl) ⟨39503, by rfl⟩ : syracuseStep 842741 = 79007) (by norm_num)
theorem B842765 : Blo 558808 842765 := bbase (se 3 (by rfl) ⟨158018, by rfl⟩ : syracuseStep 842765 = 316037) (by norm_num)
theorem B1891349 : Blo 558808 1891349 := bbase (se 6 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 1891349 = 88657) (by norm_num)
theorem B842789 : Blo 558808 842789 := bbase (se 4 (by rfl) ⟨79011, by rfl⟩ : syracuseStep 842789 = 158023) (by norm_num)
theorem B842813 : Blo 558808 842813 := bbase (se 3 (by rfl) ⟨158027, by rfl⟩ : syracuseStep 842813 = 316055) (by norm_num)
theorem B711757 : Blo 558808 711757 := bbase (se 3 (by rfl) ⟨133454, by rfl⟩ : syracuseStep 711757 = 266909) (by norm_num)
theorem B842837 : Blo 558808 842837 := bbase (se 8 (by rfl) ⟨4938, by rfl⟩ : syracuseStep 842837 = 9877) (by norm_num)
theorem B842861 : Blo 558808 842861 := bbase (se 3 (by rfl) ⟨158036, by rfl⟩ : syracuseStep 842861 = 316073) (by norm_num)
theorem B842885 : Blo 558808 842885 := bbase (se 4 (by rfl) ⟨79020, by rfl⟩ : syracuseStep 842885 = 158041) (by norm_num)
theorem B842909 : Blo 558808 842909 := bbase (se 3 (by rfl) ⟨158045, by rfl⟩ : syracuseStep 842909 = 316091) (by norm_num)
theorem B842933 : Blo 558808 842933 := bbase (se 5 (by rfl) ⟨39512, by rfl⟩ : syracuseStep 842933 = 79025) (by norm_num)
theorem B842957 : Blo 558808 842957 := bbase (se 3 (by rfl) ⟨158054, by rfl⟩ : syracuseStep 842957 = 316109) (by norm_num)
theorem B842981 : Blo 558808 842981 := bbase (se 4 (by rfl) ⟨79029, by rfl⟩ : syracuseStep 842981 = 158059) (by norm_num)
theorem B711929 : Blo 558808 711929 := bbase (se 2 (by rfl) ⟨266973, by rfl⟩ : syracuseStep 711929 = 533947) (by norm_num)
theorem B843005 : Blo 558808 843005 := bbase (se 3 (by rfl) ⟨158063, by rfl⟩ : syracuseStep 843005 = 316127) (by norm_num)
theorem B1137941 : Blo 558808 1137941 := bbase (se 6 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 1137941 = 53341) (by norm_num)
theorem B843029 : Blo 558808 843029 := bbase (se 6 (by rfl) ⟨19758, by rfl⟩ : syracuseStep 843029 = 39517) (by norm_num)
theorem B843053 : Blo 558808 843053 := bbase (se 3 (by rfl) ⟨158072, by rfl⟩ : syracuseStep 843053 = 316145) (by norm_num)
theorem B711985 : Blo 558808 711985 := bbase (se 2 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 711985 = 533989) (by norm_num)
theorem B1793333 : Blo 558808 1793333 := bbase (se 5 (by rfl) ⟨84062, by rfl⟩ : syracuseStep 1793333 = 168125) (by norm_num)
theorem B843077 : Blo 558808 843077 := bbase (se 4 (by rfl) ⟨79038, by rfl⟩ : syracuseStep 843077 = 158077) (by norm_num)
theorem B843101 : Blo 558808 843101 := bbase (se 3 (by rfl) ⟨158081, by rfl⟩ : syracuseStep 843101 = 316163) (by norm_num)
theorem B1596773 : Blo 558808 1596773 := bbase (se 4 (by rfl) ⟨149697, by rfl⟩ : syracuseStep 1596773 = 299395) (by norm_num)
theorem B843125 : Blo 558808 843125 := bbase (se 5 (by rfl) ⟨39521, by rfl⟩ : syracuseStep 843125 = 79043) (by norm_num)
theorem B843149 : Blo 558808 843149 := bbase (se 3 (by rfl) ⟨158090, by rfl⟩ : syracuseStep 843149 = 316181) (by norm_num)
theorem B712081 : Blo 558808 712081 := bbase (se 2 (by rfl) ⟨267030, by rfl⟩ : syracuseStep 712081 = 534061) (by norm_num)
theorem B843173 : Blo 558808 843173 := bbase (se 4 (by rfl) ⟨79047, by rfl⟩ : syracuseStep 843173 = 158095) (by norm_num)
theorem B1793461 : Blo 558808 1793461 := bbase (se 5 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 1793461 = 168137) (by norm_num)
theorem B843197 : Blo 558808 843197 := bbase (se 3 (by rfl) ⟨158099, by rfl⟩ : syracuseStep 843197 = 316199) (by norm_num)
theorem B1891781 : Blo 558808 1891781 := bbase (se 4 (by rfl) ⟨177354, by rfl⟩ : syracuseStep 1891781 = 354709) (by norm_num)
theorem B843221 : Blo 558808 843221 := bbase (se 7 (by rfl) ⟨9881, by rfl⟩ : syracuseStep 843221 = 19763) (by norm_num)
theorem B843245 : Blo 558808 843245 := bbase (se 3 (by rfl) ⟨158108, by rfl⟩ : syracuseStep 843245 = 316217) (by norm_num)
theorem B843269 : Blo 558808 843269 := bbase (se 4 (by rfl) ⟨79056, by rfl⟩ : syracuseStep 843269 = 158113) (by norm_num)
theorem B843293 : Blo 558808 843293 := bbase (se 3 (by rfl) ⟨158117, by rfl⟩ : syracuseStep 843293 = 316235) (by norm_num)
theorem B843317 : Blo 558808 843317 := bbase (se 5 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 843317 = 79061) (by norm_num)
theorem B712253 : Blo 558808 712253 := bbase (se 3 (by rfl) ⟨133547, by rfl⟩ : syracuseStep 712253 = 267095) (by norm_num)
theorem B843341 : Blo 558808 843341 := bbase (se 3 (by rfl) ⟨158126, by rfl⟩ : syracuseStep 843341 = 316253) (by norm_num)
theorem B843365 : Blo 558808 843365 := bbase (se 4 (by rfl) ⟨79065, by rfl⟩ : syracuseStep 843365 = 158131) (by norm_num)
theorem B843389 : Blo 558808 843389 := bbase (se 3 (by rfl) ⟨158135, by rfl⟩ : syracuseStep 843389 = 316271) (by norm_num)
theorem B843413 : Blo 558808 843413 := bbase (se 6 (by rfl) ⟨19767, by rfl⟩ : syracuseStep 843413 = 39535) (by norm_num)
theorem B843437 : Blo 558808 843437 := bbase (se 3 (by rfl) ⟨158144, by rfl⟩ : syracuseStep 843437 = 316289) (by norm_num)
theorem B1793717 : Blo 558808 1793717 := bbase (se 5 (by rfl) ⟨84080, by rfl⟩ : syracuseStep 1793717 = 168161) (by norm_num)
theorem B843461 : Blo 558808 843461 := bbase (se 4 (by rfl) ⟨79074, by rfl⟩ : syracuseStep 843461 = 158149) (by norm_num)
theorem B843485 : Blo 558808 843485 := bbase (se 3 (by rfl) ⟨158153, by rfl⟩ : syracuseStep 843485 = 316307) (by norm_num)
theorem B3596021 : Blo 558808 3596021 := bbase (se 5 (by rfl) ⟨168563, by rfl⟩ : syracuseStep 3596021 = 337127) (by norm_num)
theorem B843509 : Blo 558808 843509 := bbase (se 5 (by rfl) ⟨39539, by rfl⟩ : syracuseStep 843509 = 79079) (by norm_num)
theorem B843533 : Blo 558808 843533 := bbase (se 3 (by rfl) ⟨158162, by rfl⟩ : syracuseStep 843533 = 316325) (by norm_num)
theorem B843557 : Blo 558808 843557 := bbase (se 4 (by rfl) ⟨79083, by rfl⟩ : syracuseStep 843557 = 158167) (by norm_num)
theorem B843581 : Blo 558808 843581 := bbase (se 3 (by rfl) ⟨158171, by rfl⟩ : syracuseStep 843581 = 316343) (by norm_num)
theorem B843605 : Blo 558808 843605 := bbase (se 9 (by rfl) ⟨2471, by rfl⟩ : syracuseStep 843605 = 4943) (by norm_num)
theorem B843629 : Blo 558808 843629 := bbase (se 3 (by rfl) ⟨158180, by rfl⟩ : syracuseStep 843629 = 316361) (by norm_num)
theorem B1892213 : Blo 558808 1892213 := bbase (se 5 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 1892213 = 177395) (by norm_num)
theorem B843653 : Blo 558808 843653 := bbase (se 4 (by rfl) ⟨79092, by rfl⟩ : syracuseStep 843653 = 158185) (by norm_num)
theorem B843677 : Blo 558808 843677 := bbase (se 3 (by rfl) ⟨158189, by rfl⟩ : syracuseStep 843677 = 316379) (by norm_num)
theorem B4775861 : Blo 558808 4775861 := bbase (se 5 (by rfl) ⟨223868, by rfl⟩ : syracuseStep 4775861 = 447737) (by norm_num)
theorem B843701 : Blo 558808 843701 := bbase (se 5 (by rfl) ⟨39548, by rfl⟩ : syracuseStep 843701 = 79097) (by norm_num)
theorem B843725 : Blo 558808 843725 := bbase (se 3 (by rfl) ⟨158198, by rfl⟩ : syracuseStep 843725 = 316397) (by norm_num)
theorem B843749 : Blo 558808 843749 := bbase (se 4 (by rfl) ⟨79101, by rfl⟩ : syracuseStep 843749 = 158203) (by norm_num)
theorem B2842613 : Blo 558808 2842613 := bbase (se 5 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 2842613 = 266495) (by norm_num)
theorem B843773 : Blo 558808 843773 := bbase (se 3 (by rfl) ⟨158207, by rfl⟩ : syracuseStep 843773 = 316415) (by norm_num)
theorem B1597445 : Blo 558808 1597445 := bbase (se 4 (by rfl) ⟨149760, by rfl⟩ : syracuseStep 1597445 = 299521) (by norm_num)
theorem B843797 : Blo 558808 843797 := bbase (se 6 (by rfl) ⟨19776, by rfl⟩ : syracuseStep 843797 = 39553) (by norm_num)
theorem B843821 : Blo 558808 843821 := bbase (se 3 (by rfl) ⟨158216, by rfl⟩ : syracuseStep 843821 = 316433) (by norm_num)
theorem B843845 : Blo 558808 843845 := bbase (se 4 (by rfl) ⟨79110, by rfl⟩ : syracuseStep 843845 = 158221) (by norm_num)
theorem B843869 : Blo 558808 843869 := bbase (se 3 (by rfl) ⟨158225, by rfl⟩ : syracuseStep 843869 = 316451) (by norm_num)
theorem B876653 : Blo 558808 876653 := bbase (se 3 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 876653 = 328745) (by norm_num)
theorem B843893 : Blo 558808 843893 := bbase (se 5 (by rfl) ⟨39557, by rfl⟩ : syracuseStep 843893 = 79115) (by norm_num)
theorem B843917 : Blo 558808 843917 := bbase (se 3 (by rfl) ⟨158234, by rfl⟩ : syracuseStep 843917 = 316469) (by norm_num)
theorem B843941 : Blo 558808 843941 := bbase (se 4 (by rfl) ⟨79119, by rfl⟩ : syracuseStep 843941 = 158239) (by norm_num)
theorem B843965 : Blo 558808 843965 := bbase (se 3 (by rfl) ⟨158243, by rfl⟩ : syracuseStep 843965 = 316487) (by norm_num)
theorem B843989 : Blo 558808 843989 := bbase (se 7 (by rfl) ⟨9890, by rfl⟩ : syracuseStep 843989 = 19781) (by norm_num)
theorem B844013 : Blo 558808 844013 := bbase (se 3 (by rfl) ⟨158252, by rfl⟩ : syracuseStep 844013 = 316505) (by norm_num)
theorem B844037 : Blo 558808 844037 := bbase (se 4 (by rfl) ⟨79128, by rfl⟩ : syracuseStep 844037 = 158257) (by norm_num)
theorem B844061 : Blo 558808 844061 := bbase (se 3 (by rfl) ⟨158261, by rfl⟩ : syracuseStep 844061 = 316523) (by norm_num)
theorem B1892645 : Blo 558808 1892645 := bbase (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) (by norm_num)
theorem B1138997 : Blo 558808 1138997 := bbase (se 5 (by rfl) ⟨53390, by rfl⟩ : syracuseStep 1138997 = 106781) (by norm_num)
theorem B844085 : Blo 558808 844085 := bbase (se 5 (by rfl) ⟨39566, by rfl⟩ : syracuseStep 844085 = 79133) (by norm_num)
theorem B844109 : Blo 558808 844109 := bbase (se 3 (by rfl) ⟨158270, by rfl⟩ : syracuseStep 844109 = 316541) (by norm_num)
theorem B844133 : Blo 558808 844133 := bbase (se 4 (by rfl) ⟨79137, by rfl⟩ : syracuseStep 844133 = 158275) (by norm_num)
theorem B844157 : Blo 558808 844157 := bbase (se 3 (by rfl) ⟨158279, by rfl⟩ : syracuseStep 844157 = 316559) (by norm_num)
theorem B844181 : Blo 558808 844181 := bbase (se 6 (by rfl) ⟨19785, by rfl⟩ : syracuseStep 844181 = 39571) (by norm_num)
theorem B844205 : Blo 558808 844205 := bbase (se 3 (by rfl) ⟨158288, by rfl⟩ : syracuseStep 844205 = 316577) (by norm_num)
theorem B1597877 : Blo 558808 1597877 := bbase (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) (by norm_num)
theorem B1139141 : Blo 558808 1139141 := bbase (se 4 (by rfl) ⟨106794, by rfl⟩ : syracuseStep 1139141 = 213589) (by norm_num)
theorem B1008101 : Blo 558808 1008101 := bbase (se 4 (by rfl) ⟨94509, by rfl⟩ : syracuseStep 1008101 = 189019) (by norm_num)
theorem B1139173 : Blo 558808 1139173 := bbase (se 4 (by rfl) ⟨106797, by rfl⟩ : syracuseStep 1139173 = 213595) (by norm_num)
theorem B1008173 : Blo 558808 1008173 := bbase (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) (by norm_num)
theorem B1893077 : Blo 558808 1893077 := bbase (se 7 (by rfl) ⟨22184, by rfl⟩ : syracuseStep 1893077 = 44369) (by norm_num)
theorem B910045 : Blo 558808 910045 := bbase (se 3 (by rfl) ⟨170633, by rfl⟩ : syracuseStep 910045 = 341267) (by norm_num)
theorem B2122469 : Blo 558808 2122469 := bbase (se 4 (by rfl) ⟨198981, by rfl⟩ : syracuseStep 2122469 = 397963) (by norm_num)
theorem B615281 : Blo 558808 615281 := bbase (se 2 (by rfl) ⟨230730, by rfl⟩ : syracuseStep 615281 = 461461) (by norm_num)
theorem B1139629 : Blo 558808 1139629 := bbase (se 3 (by rfl) ⟨213680, by rfl⟩ : syracuseStep 1139629 = 427361) (by norm_num)
theorem B943069 : Blo 558808 943069 := bbase (se 3 (by rfl) ⟨176825, by rfl⟩ : syracuseStep 943069 = 353651) (by norm_num)
theorem B2122757 : Blo 558808 2122757 := bbase (se 4 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 2122757 = 398017) (by norm_num)
theorem B1008677 : Blo 558808 1008677 := bbase (se 4 (by rfl) ⟨94563, by rfl⟩ : syracuseStep 1008677 = 189127) (by norm_num)
theorem B943157 : Blo 558808 943157 := bbase (se 5 (by rfl) ⟨44210, by rfl⟩ : syracuseStep 943157 = 88421) (by norm_num)
theorem B1893509 : Blo 558808 1893509 := bbase (se 4 (by rfl) ⟨177516, by rfl⟩ : syracuseStep 1893509 = 355033) (by norm_num)
theorem B1598629 : Blo 558808 1598629 := bbase (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) (by norm_num)
theorem B943285 : Blo 558808 943285 := bbase (se 5 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 943285 = 88433) (by norm_num)
theorem B4056277 : Blo 558808 4056277 := bbase (se 7 (by rfl) ⟨47534, by rfl⟩ : syracuseStep 4056277 = 95069) (by norm_num)
theorem B2843909 : Blo 558808 2843909 := bbase (se 4 (by rfl) ⟨266616, by rfl⟩ : syracuseStep 2843909 = 533233) (by norm_num)
theorem B943373 : Blo 558808 943373 := bbase (se 3 (by rfl) ⟨176882, by rfl⟩ : syracuseStep 943373 = 353765) (by norm_num)
theorem B2876725 : Blo 558808 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B943501 : Blo 558808 943501 := bbase (se 3 (by rfl) ⟨176906, by rfl⟩ : syracuseStep 943501 = 353813) (by norm_num)
theorem B1140149 : Blo 558808 1140149 := bbase (se 5 (by rfl) ⟨53444, by rfl⟩ : syracuseStep 1140149 = 106889) (by norm_num)
theorem B943589 : Blo 558808 943589 := bbase (se 4 (by rfl) ⟨88461, by rfl⟩ : syracuseStep 943589 = 176923) (by norm_num)
theorem B1893941 : Blo 558808 1893941 := bbase (se 5 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 1893941 = 177557) (by norm_num)
theorem B943717 : Blo 558808 943717 := bbase (se 4 (by rfl) ⟨88473, by rfl⟩ : syracuseStep 943717 = 176947) (by norm_num)
theorem B943805 : Blo 558808 943805 := bbase (se 3 (by rfl) ⟨176963, by rfl⟩ : syracuseStep 943805 = 353927) (by norm_num)
theorem B943933 : Blo 558808 943933 := bbase (se 3 (by rfl) ⟨176987, by rfl⟩ : syracuseStep 943933 = 353975) (by norm_num)
theorem B944021 : Blo 558808 944021 := bbase (se 6 (by rfl) ⟨22125, by rfl⟩ : syracuseStep 944021 = 44251) (by norm_num)
theorem B1894373 : Blo 558808 1894373 := bbase (se 4 (by rfl) ⟨177597, by rfl⟩ : syracuseStep 1894373 = 355195) (by norm_num)
theorem B944149 : Blo 558808 944149 := bbase (se 6 (by rfl) ⟨22128, by rfl⟩ : syracuseStep 944149 = 44257) (by norm_num)
theorem B1140797 : Blo 558808 1140797 := bbase (se 3 (by rfl) ⟨213899, by rfl⟩ : syracuseStep 1140797 = 427799) (by norm_num)
theorem B1796165 : Blo 558808 1796165 := bbase (se 4 (by rfl) ⟨168390, by rfl⟩ : syracuseStep 1796165 = 336781) (by norm_num)
theorem B1370189 : Blo 558808 1370189 := bbase (se 3 (by rfl) ⟨256910, by rfl⟩ : syracuseStep 1370189 = 513821) (by norm_num)
theorem B944237 : Blo 558808 944237 := bbase (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) (by norm_num)
theorem B2123941 : Blo 558808 2123941 := bbase (se 4 (by rfl) ⟨199119, by rfl⟩ : syracuseStep 2123941 = 398239) (by norm_num)
theorem B944365 : Blo 558808 944365 := bbase (se 3 (by rfl) ⟨177068, by rfl⟩ : syracuseStep 944365 = 354137) (by norm_num)
theorem B6056213 : Blo 558808 6056213 := bbase (se 6 (by rfl) ⟨141942, by rfl⟩ : syracuseStep 6056213 = 283885) (by norm_num)
theorem B944453 : Blo 558808 944453 := bbase (se 4 (by rfl) ⟨88542, by rfl⟩ : syracuseStep 944453 = 177085) (by norm_num)
theorem B1894805 : Blo 558808 1894805 := bbase (se 6 (by rfl) ⟨44409, by rfl⟩ : syracuseStep 1894805 = 88819) (by norm_num)
theorem B944581 : Blo 558808 944581 := bbase (se 4 (by rfl) ⟨88554, by rfl⟩ : syracuseStep 944581 = 177109) (by norm_num)
theorem B2124245 : Blo 558808 2124245 := bbase (se 7 (by rfl) ⟨24893, by rfl⟩ : syracuseStep 2124245 = 49787) (by norm_num)
theorem B2845205 : Blo 558808 2845205 := bbase (se 6 (by rfl) ⟨66684, by rfl⟩ : syracuseStep 2845205 = 133369) (by norm_num)
theorem B944669 : Blo 558808 944669 := bbase (se 3 (by rfl) ⟨177125, by rfl⟩ : syracuseStep 944669 = 354251) (by norm_num)
theorem B2878037 : Blo 558808 2878037 := bbase (se 8 (by rfl) ⟨16863, by rfl⟩ : syracuseStep 2878037 = 33727) (by norm_num)
theorem B944797 : Blo 558808 944797 := bbase (se 3 (by rfl) ⟨177149, by rfl⟩ : syracuseStep 944797 = 354299) (by norm_num)
theorem B944885 : Blo 558808 944885 := bbase (se 5 (by rfl) ⟨44291, by rfl⟩ : syracuseStep 944885 = 88583) (by norm_num)
theorem B682777 : Blo 558808 682777 := bbase (se 2 (by rfl) ⟨256041, by rfl⟩ : syracuseStep 682777 = 512083) (by norm_num)
theorem B1895237 : Blo 558808 1895237 := bbase (se 4 (by rfl) ⟨177678, by rfl⟩ : syracuseStep 1895237 = 355357) (by norm_num)
theorem B4778837 : Blo 558808 4778837 := bbase (se 9 (by rfl) ⟨14000, by rfl⟩ : syracuseStep 4778837 = 28001) (by norm_num)
theorem B945013 : Blo 558808 945013 := bbase (se 5 (by rfl) ⟨44297, by rfl⟩ : syracuseStep 945013 = 88595) (by norm_num)
theorem B5401525 : Blo 558808 5401525 := bbase (se 5 (by rfl) ⟨253196, by rfl⟩ : syracuseStep 5401525 = 506393) (by norm_num)
theorem B945101 : Blo 558808 945101 := bbase (se 3 (by rfl) ⟨177206, by rfl⟩ : syracuseStep 945101 = 354413) (by norm_num)
theorem B2026453 : Blo 558808 2026453 := bbase (se 7 (by rfl) ⟨23747, by rfl⟩ : syracuseStep 2026453 = 47495) (by norm_num)
theorem B1534997 : Blo 558808 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B945229 : Blo 558808 945229 := bbase (se 3 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 945229 = 354461) (by norm_num)
theorem B945317 : Blo 558808 945317 := bbase (se 4 (by rfl) ⟨88623, by rfl⟩ : syracuseStep 945317 = 177247) (by norm_num)
theorem B1895669 : Blo 558808 1895669 := bbase (se 5 (by rfl) ⟨88859, by rfl⟩ : syracuseStep 1895669 = 177719) (by norm_num)
theorem B945445 : Blo 558808 945445 := bbase (se 4 (by rfl) ⟨88635, by rfl⟩ : syracuseStep 945445 = 177271) (by norm_num)
theorem B945533 : Blo 558808 945533 := bbase (se 3 (by rfl) ⟨177287, by rfl⟩ : syracuseStep 945533 = 354575) (by norm_num)
theorem B1797509 : Blo 558808 1797509 := bbase (se 4 (by rfl) ⟨168516, by rfl⟩ : syracuseStep 1797509 = 337033) (by norm_num)
theorem B9498005 : Blo 558808 9498005 := bbase (se 6 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 9498005 = 445219) (by norm_num)
theorem B945661 : Blo 558808 945661 := bbase (se 3 (by rfl) ⟨177311, by rfl⟩ : syracuseStep 945661 = 354623) (by norm_num)
theorem B945749 : Blo 558808 945749 := bbase (se 8 (by rfl) ⟨5541, by rfl⟩ : syracuseStep 945749 = 11083) (by norm_num)
theorem B1896101 : Blo 558808 1896101 := bbase (se 4 (by rfl) ⟨177759, by rfl⟩ : syracuseStep 1896101 = 355519) (by norm_num)
theorem B945877 : Blo 558808 945877 := bbase (se 7 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 945877 = 22169) (by norm_num)
theorem B2846501 : Blo 558808 2846501 := bbase (se 4 (by rfl) ⟨266859, by rfl⟩ : syracuseStep 2846501 = 533719) (by norm_num)
theorem B945965 : Blo 558808 945965 := bbase (se 3 (by rfl) ⟨177368, by rfl⟩ : syracuseStep 945965 = 354737) (by norm_num)
theorem B946093 : Blo 558808 946093 := bbase (se 3 (by rfl) ⟨177392, by rfl⟩ : syracuseStep 946093 = 354785) (by norm_num)
theorem B1601477 : Blo 558808 1601477 := bbase (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) (by norm_num)
theorem B946181 : Blo 558808 946181 := bbase (se 4 (by rfl) ⟨88704, by rfl⟩ : syracuseStep 946181 = 177409) (by norm_num)
theorem B1896533 : Blo 558808 1896533 := bbase (se 8 (by rfl) ⟨11112, by rfl⟩ : syracuseStep 1896533 = 22225) (by norm_num)
theorem B684121 : Blo 558808 684121 := bbase (se 2 (by rfl) ⟨256545, by rfl⟩ : syracuseStep 684121 = 513091) (by norm_num)
theorem B946309 : Blo 558808 946309 := bbase (se 4 (by rfl) ⟨88716, by rfl⟩ : syracuseStep 946309 = 177433) (by norm_num)
theorem B946397 : Blo 558808 946397 := bbase (se 3 (by rfl) ⟨177449, by rfl⟩ : syracuseStep 946397 = 354899) (by norm_num)
theorem B1438013 : Blo 558808 1438013 := bbase (se 3 (by rfl) ⟨269627, by rfl⟩ : syracuseStep 1438013 = 539255) (by norm_num)
theorem B946525 : Blo 558808 946525 := bbase (se 3 (by rfl) ⟨177473, by rfl⟩ : syracuseStep 946525 = 354947) (by norm_num)
theorem B2388325 : Blo 558808 2388325 := bbase (se 4 (by rfl) ⟨223905, by rfl⟩ : syracuseStep 2388325 = 447811) (by norm_num)
theorem B2388341 : Blo 558808 2388341 := bbase (se 5 (by rfl) ⟨111953, by rfl⟩ : syracuseStep 2388341 = 223907) (by norm_num)
theorem B946613 : Blo 558808 946613 := bbase (se 5 (by rfl) ⟨44372, by rfl⟩ : syracuseStep 946613 = 88745) (by norm_num)
theorem B1012189 : Blo 558808 1012189 := bbase (se 3 (by rfl) ⟨189785, by rfl⟩ : syracuseStep 1012189 = 379571) (by norm_num)
theorem B1896965 : Blo 558808 1896965 := bbase (se 4 (by rfl) ⟨177840, by rfl⟩ : syracuseStep 1896965 = 355681) (by norm_num)
theorem B2126357 : Blo 558808 2126357 := bbase (se 6 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 2126357 = 99673) (by norm_num)
theorem B946741 : Blo 558808 946741 := bbase (se 5 (by rfl) ⟨44378, by rfl⟩ : syracuseStep 946741 = 88757) (by norm_num)
theorem B946829 : Blo 558808 946829 := bbase (se 3 (by rfl) ⟨177530, by rfl⟩ : syracuseStep 946829 = 355061) (by norm_num)
theorem B1077941 : Blo 558808 1077941 := bbase (se 5 (by rfl) ⟨50528, by rfl⟩ : syracuseStep 1077941 = 101057) (by norm_num)
theorem B946957 : Blo 558808 946957 := bbase (se 3 (by rfl) ⟨177554, by rfl⟩ : syracuseStep 946957 = 355109) (by norm_num)
theorem B2126645 : Blo 558808 2126645 := bbase (se 5 (by rfl) ⟨99686, by rfl⟩ : syracuseStep 2126645 = 199373) (by norm_num)
theorem B2028341 : Blo 558808 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B1078093 : Blo 558808 1078093 := bbase (se 3 (by rfl) ⟨202142, by rfl⟩ : syracuseStep 1078093 = 404285) (by norm_num)
theorem B947045 : Blo 558808 947045 := bbase (se 4 (by rfl) ⟨88785, by rfl⟩ : syracuseStep 947045 = 177571) (by norm_num)
theorem B1897397 : Blo 558808 1897397 := bbase (se 5 (by rfl) ⟨88940, by rfl⟩ : syracuseStep 1897397 = 177881) (by norm_num)
theorem B947173 : Blo 558808 947173 := bbase (se 4 (by rfl) ⟨88797, by rfl⟩ : syracuseStep 947173 = 177595) (by norm_num)
theorem B2847797 : Blo 558808 2847797 := bbase (se 5 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 2847797 = 266981) (by norm_num)
theorem B947261 : Blo 558808 947261 := bbase (se 3 (by rfl) ⟨177611, by rfl⟩ : syracuseStep 947261 = 355223) (by norm_num)
theorem B2421829 : Blo 558808 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B6157397 : Blo 558808 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B1012829 : Blo 558808 1012829 := bbase (se 3 (by rfl) ⟨189905, by rfl⟩ : syracuseStep 1012829 = 379811) (by norm_num)
theorem B1602661 : Blo 558808 1602661 := bbase (se 4 (by rfl) ⟨150249, by rfl⟩ : syracuseStep 1602661 = 300499) (by norm_num)
theorem B947389 : Blo 558808 947389 := bbase (se 3 (by rfl) ⟨177635, by rfl⟩ : syracuseStep 947389 = 355271) (by norm_num)
theorem B947477 : Blo 558808 947477 := bbase (se 6 (by rfl) ⟨22206, by rfl⟩ : syracuseStep 947477 = 44413) (by norm_num)
theorem B1799509 : Blo 558808 1799509 := bbase (se 13 (by rfl) ⟨329, by rfl⟩ : syracuseStep 1799509 = 659) (by norm_num)
theorem B1897829 : Blo 558808 1897829 := bbase (se 4 (by rfl) ⟨177921, by rfl⟩ : syracuseStep 1897829 = 355843) (by norm_num)
theorem B947605 : Blo 558808 947605 := bbase (se 6 (by rfl) ⟨22209, by rfl⟩ : syracuseStep 947605 = 44419) (by norm_num)
theorem B947693 : Blo 558808 947693 := bbase (se 3 (by rfl) ⟨177692, by rfl⟩ : syracuseStep 947693 = 355385) (by norm_num)
theorem B947821 : Blo 558808 947821 := bbase (se 3 (by rfl) ⟨177716, by rfl⟩ : syracuseStep 947821 = 355433) (by norm_num)
theorem B1275533 : Blo 558808 1275533 := bbase (se 3 (by rfl) ⟨239162, by rfl⟩ : syracuseStep 1275533 = 478325) (by norm_num)
theorem B947909 : Blo 558808 947909 := bbase (se 4 (by rfl) ⟨88866, by rfl⟩ : syracuseStep 947909 = 177733) (by norm_num)
theorem B1898261 : Blo 558808 1898261 := bbase (se 6 (by rfl) ⟨44490, by rfl⟩ : syracuseStep 1898261 = 88981) (by norm_num)
theorem B849709 : Blo 558808 849709 := bbase (se 3 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 849709 = 318641) (by norm_num)
theorem B948037 : Blo 558808 948037 := bbase (se 4 (by rfl) ⟨88878, by rfl⟩ : syracuseStep 948037 = 177757) (by norm_num)
theorem B24180565 : Blo 558808 24180565 := bbase (se 9 (by rfl) ⟨70841, by rfl⟩ : syracuseStep 24180565 = 141683) (by norm_num)
theorem B948125 : Blo 558808 948125 := bbase (se 3 (by rfl) ⟨177773, by rfl⟩ : syracuseStep 948125 = 355547) (by norm_num)
theorem B2127829 : Blo 558808 2127829 := bbase (se 7 (by rfl) ⟨24935, by rfl⟩ : syracuseStep 2127829 = 49871) (by norm_num)
theorem B948253 : Blo 558808 948253 := bbase (se 3 (by rfl) ⟨177797, by rfl⟩ : syracuseStep 948253 = 355595) (by norm_num)
theorem B4257845 : Blo 558808 4257845 := bbase (se 5 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 4257845 = 399173) (by norm_num)
theorem B718913 : Blo 558808 718913 := bbase (se 2 (by rfl) ⟨269592, by rfl⟩ : syracuseStep 718913 = 539185) (by norm_num)
theorem B948341 : Blo 558808 948341 := bbase (se 5 (by rfl) ⟨44453, by rfl⟩ : syracuseStep 948341 = 88907) (by norm_num)
theorem B1898693 : Blo 558808 1898693 := bbase (se 4 (by rfl) ⟨178002, by rfl⟩ : syracuseStep 1898693 = 356005) (by norm_num)
theorem B948469 : Blo 558808 948469 := bbase (se 5 (by rfl) ⟨44459, by rfl⟩ : syracuseStep 948469 = 88919) (by norm_num)
theorem B2128133 : Blo 558808 2128133 := bbase (se 4 (by rfl) ⟨199512, by rfl⟩ : syracuseStep 2128133 = 399025) (by norm_num)
theorem B2849093 : Blo 558808 2849093 := bbase (se 4 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 2849093 = 534205) (by norm_num)
theorem B948557 : Blo 558808 948557 := bbase (se 3 (by rfl) ⟨177854, by rfl⟩ : syracuseStep 948557 = 355709) (by norm_num)
theorem B948685 : Blo 558808 948685 := bbase (se 3 (by rfl) ⟨177878, by rfl⟩ : syracuseStep 948685 = 355757) (by norm_num)
theorem B948773 : Blo 558808 948773 := bbase (se 4 (by rfl) ⟨88947, by rfl⟩ : syracuseStep 948773 = 177895) (by norm_num)
theorem B2390597 : Blo 558808 2390597 := bbase (se 4 (by rfl) ⟨224118, by rfl⟩ : syracuseStep 2390597 = 448237) (by norm_num)
theorem B1899125 : Blo 558808 1899125 := bbase (se 5 (by rfl) ⟨89021, by rfl⟩ : syracuseStep 1899125 = 178043) (by norm_num)
theorem B1276573 : Blo 558808 1276573 := bbase (se 3 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 1276573 = 478715) (by norm_num)
theorem B948901 : Blo 558808 948901 := bbase (se 4 (by rfl) ⟨88959, by rfl⟩ : syracuseStep 948901 = 177919) (by norm_num)
theorem B1440445 : Blo 558808 1440445 := bbase (se 3 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 1440445 = 540167) (by norm_num)
theorem B4029173 : Blo 558808 4029173 := bbase (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) (by norm_num)
theorem B948989 : Blo 558808 948989 := bbase (se 3 (by rfl) ⟨177935, by rfl⟩ : syracuseStep 948989 = 355871) (by norm_num)
theorem B719689 : Blo 558808 719689 := bbase (se 2 (by rfl) ⟨269883, by rfl⟩ : syracuseStep 719689 = 539767) (by norm_num)
theorem B949117 : Blo 558808 949117 := bbase (se 3 (by rfl) ⟨177959, by rfl⟩ : syracuseStep 949117 = 355919) (by norm_num)
theorem B850877 : Blo 558808 850877 := bbase (se 3 (by rfl) ⟨159539, by rfl⟩ : syracuseStep 850877 = 319079) (by norm_num)
theorem B949205 : Blo 558808 949205 := bbase (se 7 (by rfl) ⟨11123, by rfl⟩ : syracuseStep 949205 = 22247) (by norm_num)
theorem B5405717 : Blo 558808 5405717 := bbase (se 6 (by rfl) ⟨126696, by rfl⟩ : syracuseStep 5405717 = 253393) (by norm_num)
theorem B949333 : Blo 558808 949333 := bbase (se 8 (by rfl) ⟨5562, by rfl⟩ : syracuseStep 949333 = 11125) (by norm_num)
theorem B949421 : Blo 558808 949421 := bbase (se 3 (by rfl) ⟨178016, by rfl⟩ : syracuseStep 949421 = 356033) (by norm_num)
theorem B1342693 : Blo 558808 1342693 := bbase (se 4 (by rfl) ⟨125877, by rfl⟩ : syracuseStep 1342693 = 251755) (by norm_num)
theorem B949549 : Blo 558808 949549 := bbase (se 3 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 949549 = 356081) (by norm_num)
theorem B949637 : Blo 558808 949637 := bbase (se 4 (by rfl) ⟨89028, by rfl⟩ : syracuseStep 949637 = 178057) (by norm_num)
theorem B1342925 : Blo 558808 1342925 := bbase (se 3 (by rfl) ⟨251798, by rfl⟩ : syracuseStep 1342925 = 503597) (by norm_num)
theorem B1342973 : Blo 558808 1342973 := bbase (se 3 (by rfl) ⟨251807, by rfl⟩ : syracuseStep 1342973 = 503615) (by norm_num)
theorem B1277549 : Blo 558808 1277549 := bbase (se 3 (by rfl) ⟨239540, by rfl⟩ : syracuseStep 1277549 = 479081) (by norm_num)
theorem B1703797 : Blo 558808 1703797 := bbase (se 5 (by rfl) ⟨79865, by rfl⟩ : syracuseStep 1703797 = 159731) (by norm_num)
theorem B1277869 : Blo 558808 1277869 := bbase (se 3 (by rfl) ⟨239600, by rfl⟩ : syracuseStep 1277869 = 479201) (by norm_num)
theorem B1441955 : Blo 558808 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B2687345 : Blo 558808 2687345 := bstep (se 2 (by rfl) ⟨1007754, by rfl⟩ : syracuseStep 2687345 = 2015509) B2015509
theorem B5374349 : Blo 558808 5374349 := bstep (se 3 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 5374349 = 2015381) B2015381
theorem B6390413 : Blo 558808 6390413 := bstep (se 3 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 6390413 = 2396405) B2396405
theorem B3834701 : Blo 558808 3834701 := bstep (se 3 (by rfl) ⟨719006, by rfl⟩ : syracuseStep 3834701 = 1438013) B1438013
theorem B2392973 : Blo 558808 2392973 := bstep (se 3 (by rfl) ⟨448682, by rfl⟩ : syracuseStep 2392973 = 897365) B897365
theorem B1213393 : Blo 558808 1213393 := bstep (se 2 (by rfl) ⟨455022, by rfl⟩ : syracuseStep 1213393 = 910045) B910045
theorem B1279235 : Blo 558808 1279235 := bstep (se 1 (by rfl) ⟨959426, by rfl⟩ : syracuseStep 1279235 = 1918853) B1918853
theorem B16647565 : Blo 558808 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B2688461 : Blo 558808 2688461 := bstep (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) B1008173
theorem B2131505 : Blo 558808 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B5408369 : Blo 558808 5408369 := bstep (se 2 (by rfl) ⟨2028138, by rfl⟩ : syracuseStep 5408369 = 4056277) B4056277
theorem B558819 : Blo 558808 558819 := bstep (se 1 (by rfl) ⟨419114, by rfl⟩ : syracuseStep 558819 = 838229) B838229
theorem B3835633 : Blo 558808 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B558835 : Blo 558808 558835 := bstep (se 1 (by rfl) ⟨419126, by rfl⟩ : syracuseStep 558835 = 838253) B838253
theorem B558851 : Blo 558808 558851 := bstep (se 1 (by rfl) ⟨419138, by rfl⟩ : syracuseStep 558851 = 838277) B838277
theorem B558867 : Blo 558808 558867 := bstep (se 1 (by rfl) ⟨419150, by rfl⟩ : syracuseStep 558867 = 838301) B838301
theorem B558883 : Blo 558808 558883 := bstep (se 1 (by rfl) ⟨419162, by rfl⟩ : syracuseStep 558883 = 838325) B838325
theorem B558899 : Blo 558808 558899 := bstep (se 1 (by rfl) ⟨419174, by rfl⟩ : syracuseStep 558899 = 838349) B838349
theorem B558915 : Blo 558808 558915 := bstep (se 1 (by rfl) ⟨419186, by rfl⟩ : syracuseStep 558915 = 838373) B838373
theorem B558931 : Blo 558808 558931 := bstep (se 1 (by rfl) ⟨419198, by rfl⟩ : syracuseStep 558931 = 838397) B838397
theorem B558947 : Blo 558808 558947 := bstep (se 1 (by rfl) ⟨419210, by rfl⟩ : syracuseStep 558947 = 838421) B838421
theorem B558963 : Blo 558808 558963 := bstep (se 1 (by rfl) ⟨419222, by rfl⟩ : syracuseStep 558963 = 838445) B838445
theorem B558979 : Blo 558808 558979 := bstep (se 1 (by rfl) ⟨419234, by rfl⟩ : syracuseStep 558979 = 838469) B838469
theorem B558995 : Blo 558808 558995 := bstep (se 1 (by rfl) ⟨419246, by rfl⟩ : syracuseStep 558995 = 838493) B838493
theorem B559011 : Blo 558808 559011 := bstep (se 1 (by rfl) ⟨419258, by rfl⟩ : syracuseStep 559011 = 838517) B838517
theorem B559027 : Blo 558808 559027 := bstep (se 1 (by rfl) ⟨419270, by rfl⟩ : syracuseStep 559027 = 838541) B838541
theorem B559043 : Blo 558808 559043 := bstep (se 1 (by rfl) ⟨419282, by rfl⟩ : syracuseStep 559043 = 838565) B838565
theorem B559059 : Blo 558808 559059 := bstep (se 1 (by rfl) ⟨419294, by rfl⟩ : syracuseStep 559059 = 838589) B838589
theorem B559075 : Blo 558808 559075 := bstep (se 1 (by rfl) ⟨419306, by rfl⟩ : syracuseStep 559075 = 838613) B838613
theorem B559091 : Blo 558808 559091 := bstep (se 1 (by rfl) ⟨419318, by rfl⟩ : syracuseStep 559091 = 838637) B838637
theorem B559107 : Blo 558808 559107 := bstep (se 1 (by rfl) ⟨419330, by rfl⟩ : syracuseStep 559107 = 838661) B838661
theorem B559123 : Blo 558808 559123 := bstep (se 1 (by rfl) ⟨419342, by rfl⟩ : syracuseStep 559123 = 838685) B838685
theorem B559139 : Blo 558808 559139 := bstep (se 1 (by rfl) ⟨419354, by rfl⟩ : syracuseStep 559139 = 838709) B838709
theorem B559155 : Blo 558808 559155 := bstep (se 1 (by rfl) ⟨419366, by rfl⟩ : syracuseStep 559155 = 838733) B838733
theorem B559171 : Blo 558808 559171 := bstep (se 1 (by rfl) ⟨419378, by rfl⟩ : syracuseStep 559171 = 838757) B838757
theorem B559187 : Blo 558808 559187 := bstep (se 1 (by rfl) ⟨419390, by rfl⟩ : syracuseStep 559187 = 838781) B838781
theorem B559203 : Blo 558808 559203 := bstep (se 1 (by rfl) ⟨419402, by rfl⟩ : syracuseStep 559203 = 838805) B838805
theorem B559219 : Blo 558808 559219 := bstep (se 1 (by rfl) ⟨419414, by rfl⟩ : syracuseStep 559219 = 838829) B838829
theorem B559235 : Blo 558808 559235 := bstep (se 1 (by rfl) ⟨419426, by rfl⟩ : syracuseStep 559235 = 838853) B838853
theorem B559251 : Blo 558808 559251 := bstep (se 1 (by rfl) ⟨419438, by rfl⟩ : syracuseStep 559251 = 838877) B838877
theorem B559267 : Blo 558808 559267 := bstep (se 1 (by rfl) ⟨419450, by rfl⟩ : syracuseStep 559267 = 838901) B838901
theorem B559283 : Blo 558808 559283 := bstep (se 1 (by rfl) ⟨419462, by rfl⟩ : syracuseStep 559283 = 838925) B838925
theorem B559299 : Blo 558808 559299 := bstep (se 1 (by rfl) ⟨419474, by rfl⟩ : syracuseStep 559299 = 838949) B838949
theorem B559315 : Blo 558808 559315 := bstep (se 1 (by rfl) ⟨419486, by rfl⟩ : syracuseStep 559315 = 838973) B838973
theorem B559331 : Blo 558808 559331 := bstep (se 1 (by rfl) ⟨419498, by rfl⟩ : syracuseStep 559331 = 838997) B838997
theorem B559347 : Blo 558808 559347 := bstep (se 1 (by rfl) ⟨419510, by rfl⟩ : syracuseStep 559347 = 839021) B839021
theorem B559363 : Blo 558808 559363 := bstep (se 1 (by rfl) ⟨419522, by rfl⟩ : syracuseStep 559363 = 839045) B839045
theorem B559379 : Blo 558808 559379 := bstep (se 1 (by rfl) ⟨419534, by rfl⟩ : syracuseStep 559379 = 839069) B839069
theorem B559395 : Blo 558808 559395 := bstep (se 1 (by rfl) ⟨419546, by rfl⟩ : syracuseStep 559395 = 839093) B839093
theorem B1640749 : Blo 558808 1640749 := bstep (se 3 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 1640749 = 615281) B615281
theorem B559411 : Blo 558808 559411 := bstep (se 1 (by rfl) ⟨419558, by rfl⟩ : syracuseStep 559411 = 839117) B839117
theorem B559427 : Blo 558808 559427 := bstep (se 1 (by rfl) ⟨419570, by rfl⟩ : syracuseStep 559427 = 839141) B839141
theorem B559443 : Blo 558808 559443 := bstep (se 1 (by rfl) ⟨419582, by rfl⟩ : syracuseStep 559443 = 839165) B839165
theorem B559459 : Blo 558808 559459 := bstep (se 1 (by rfl) ⟨419594, by rfl⟩ : syracuseStep 559459 = 839189) B839189
theorem B559475 : Blo 558808 559475 := bstep (se 1 (by rfl) ⟨419606, by rfl⟩ : syracuseStep 559475 = 839213) B839213
theorem B559491 : Blo 558808 559491 := bstep (se 1 (by rfl) ⟨419618, by rfl⟩ : syracuseStep 559491 = 839237) B839237
theorem B559507 : Blo 558808 559507 := bstep (se 1 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 559507 = 839261) B839261
theorem B559523 : Blo 558808 559523 := bstep (se 1 (by rfl) ⟨419642, by rfl⟩ : syracuseStep 559523 = 839285) B839285
theorem B559539 : Blo 558808 559539 := bstep (se 1 (by rfl) ⟨419654, by rfl⟩ : syracuseStep 559539 = 839309) B839309
theorem B559555 : Blo 558808 559555 := bstep (se 1 (by rfl) ⟨419666, by rfl⟩ : syracuseStep 559555 = 839333) B839333
theorem B559571 : Blo 558808 559571 := bstep (se 1 (by rfl) ⟨419678, by rfl⟩ : syracuseStep 559571 = 839357) B839357
theorem B559587 : Blo 558808 559587 := bstep (se 1 (by rfl) ⟨419690, by rfl⟩ : syracuseStep 559587 = 839381) B839381
theorem B559603 : Blo 558808 559603 := bstep (se 1 (by rfl) ⟨419702, by rfl⟩ : syracuseStep 559603 = 839405) B839405
theorem B559619 : Blo 558808 559619 := bstep (se 1 (by rfl) ⟨419714, by rfl⟩ : syracuseStep 559619 = 839429) B839429
theorem B559635 : Blo 558808 559635 := bstep (se 1 (by rfl) ⟨419726, by rfl⟩ : syracuseStep 559635 = 839453) B839453
theorem B559651 : Blo 558808 559651 := bstep (se 1 (by rfl) ⟨419738, by rfl⟩ : syracuseStep 559651 = 839477) B839477
theorem B559667 : Blo 558808 559667 := bstep (se 1 (by rfl) ⟨419750, by rfl⟩ : syracuseStep 559667 = 839501) B839501
theorem B559683 : Blo 558808 559683 := bstep (se 1 (by rfl) ⟨419762, by rfl⟩ : syracuseStep 559683 = 839525) B839525
theorem B559699 : Blo 558808 559699 := bstep (se 1 (by rfl) ⟨419774, by rfl⟩ : syracuseStep 559699 = 839549) B839549
theorem B559715 : Blo 558808 559715 := bstep (se 1 (by rfl) ⟨419786, by rfl⟩ : syracuseStep 559715 = 839573) B839573
theorem B559731 : Blo 558808 559731 := bstep (se 1 (by rfl) ⟨419798, by rfl⟩ : syracuseStep 559731 = 839597) B839597
theorem B559747 : Blo 558808 559747 := bstep (se 1 (by rfl) ⟨419810, by rfl⟩ : syracuseStep 559747 = 839621) B839621
theorem B559763 : Blo 558808 559763 := bstep (se 1 (by rfl) ⟨419822, by rfl⟩ : syracuseStep 559763 = 839645) B839645
theorem B559779 : Blo 558808 559779 := bstep (se 1 (by rfl) ⟨419834, by rfl⟩ : syracuseStep 559779 = 839669) B839669
theorem B559795 : Blo 558808 559795 := bstep (se 1 (by rfl) ⟨419846, by rfl⟩ : syracuseStep 559795 = 839693) B839693
theorem B559811 : Blo 558808 559811 := bstep (se 1 (by rfl) ⟨419858, by rfl⟩ : syracuseStep 559811 = 839717) B839717
theorem B6163141 : Blo 558808 6163141 := bstep (se 4 (by rfl) ⟨577794, by rfl⟩ : syracuseStep 6163141 = 1155589) B1155589
theorem B559827 : Blo 558808 559827 := bstep (se 1 (by rfl) ⟨419870, by rfl⟩ : syracuseStep 559827 = 839741) B839741
theorem B559843 : Blo 558808 559843 := bstep (se 1 (by rfl) ⟨419882, by rfl⟩ : syracuseStep 559843 = 839765) B839765
theorem B559859 : Blo 558808 559859 := bstep (se 1 (by rfl) ⟨419894, by rfl⟩ : syracuseStep 559859 = 839789) B839789
theorem B559875 : Blo 558808 559875 := bstep (se 1 (by rfl) ⟨419906, by rfl⟩ : syracuseStep 559875 = 839813) B839813
theorem B2689805 : Blo 558808 2689805 := bstep (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) B1008677
theorem B559891 : Blo 558808 559891 := bstep (se 1 (by rfl) ⟨419918, by rfl⟩ : syracuseStep 559891 = 839837) B839837
theorem B559907 : Blo 558808 559907 := bstep (se 1 (by rfl) ⟨419930, by rfl⟩ : syracuseStep 559907 = 839861) B839861
theorem B559923 : Blo 558808 559923 := bstep (se 1 (by rfl) ⟨419942, by rfl⟩ : syracuseStep 559923 = 839885) B839885
theorem B559939 : Blo 558808 559939 := bstep (se 1 (by rfl) ⟨419954, by rfl⟩ : syracuseStep 559939 = 839909) B839909
theorem B559955 : Blo 558808 559955 := bstep (se 1 (by rfl) ⟨419966, by rfl⟩ : syracuseStep 559955 = 839933) B839933
theorem B559971 : Blo 558808 559971 := bstep (se 1 (by rfl) ⟨419978, by rfl⟩ : syracuseStep 559971 = 839957) B839957
theorem B559987 : Blo 558808 559987 := bstep (se 1 (by rfl) ⟨419990, by rfl⟩ : syracuseStep 559987 = 839981) B839981
theorem B560003 : Blo 558808 560003 := bstep (se 1 (by rfl) ⟨420002, by rfl⟩ : syracuseStep 560003 = 840005) B840005
theorem B560019 : Blo 558808 560019 := bstep (se 1 (by rfl) ⟨420014, by rfl⟩ : syracuseStep 560019 = 840029) B840029
theorem B560035 : Blo 558808 560035 := bstep (se 1 (by rfl) ⟨420026, by rfl⟩ : syracuseStep 560035 = 840053) B840053
theorem B560051 : Blo 558808 560051 := bstep (se 1 (by rfl) ⟨420038, by rfl⟩ : syracuseStep 560051 = 840077) B840077
theorem B560067 : Blo 558808 560067 := bstep (se 1 (by rfl) ⟨420050, by rfl⟩ : syracuseStep 560067 = 840101) B840101
theorem B560083 : Blo 558808 560083 := bstep (se 1 (by rfl) ⟨420062, by rfl⟩ : syracuseStep 560083 = 840125) B840125
theorem B560099 : Blo 558808 560099 := bstep (se 1 (by rfl) ⟨420074, by rfl⟩ : syracuseStep 560099 = 840149) B840149
theorem B2132963 : Blo 558808 2132963 := bstep (se 1 (by rfl) ⟨1599722, by rfl⟩ : syracuseStep 2132963 = 3199445) B3199445
theorem B560115 : Blo 558808 560115 := bstep (se 1 (by rfl) ⟨420086, by rfl⟩ : syracuseStep 560115 = 840173) B840173
theorem B560131 : Blo 558808 560131 := bstep (se 1 (by rfl) ⟨420098, by rfl⟩ : syracuseStep 560131 = 840197) B840197
theorem B560147 : Blo 558808 560147 := bstep (se 1 (by rfl) ⟨420110, by rfl⟩ : syracuseStep 560147 = 840221) B840221
theorem B560163 : Blo 558808 560163 := bstep (se 1 (by rfl) ⟨420122, by rfl⟩ : syracuseStep 560163 = 840245) B840245
theorem B560179 : Blo 558808 560179 := bstep (se 1 (by rfl) ⟨420134, by rfl⟩ : syracuseStep 560179 = 840269) B840269
theorem B560195 : Blo 558808 560195 := bstep (se 1 (by rfl) ⟨420146, by rfl⟩ : syracuseStep 560195 = 840293) B840293
theorem B560211 : Blo 558808 560211 := bstep (se 1 (by rfl) ⟨420158, by rfl⟩ : syracuseStep 560211 = 840317) B840317
theorem B560227 : Blo 558808 560227 := bstep (se 1 (by rfl) ⟨420170, by rfl⟩ : syracuseStep 560227 = 840341) B840341
theorem B560243 : Blo 558808 560243 := bstep (se 1 (by rfl) ⟨420182, by rfl⟩ : syracuseStep 560243 = 840365) B840365
theorem B560259 : Blo 558808 560259 := bstep (se 1 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 560259 = 840389) B840389
theorem B560275 : Blo 558808 560275 := bstep (se 1 (by rfl) ⟨420206, by rfl⟩ : syracuseStep 560275 = 840413) B840413
theorem B560291 : Blo 558808 560291 := bstep (se 1 (by rfl) ⟨420218, by rfl⟩ : syracuseStep 560291 = 840437) B840437
theorem B1281187 : Blo 558808 1281187 := bstep (se 1 (by rfl) ⟨960890, by rfl⟩ : syracuseStep 1281187 = 1921781) B1921781
theorem B560307 : Blo 558808 560307 := bstep (se 1 (by rfl) ⟨420230, by rfl⟩ : syracuseStep 560307 = 840461) B840461
theorem B560323 : Blo 558808 560323 := bstep (se 1 (by rfl) ⟨420242, by rfl⟩ : syracuseStep 560323 = 840485) B840485
theorem B560339 : Blo 558808 560339 := bstep (se 1 (by rfl) ⟨420254, by rfl⟩ : syracuseStep 560339 = 840509) B840509
theorem B560355 : Blo 558808 560355 := bstep (se 1 (by rfl) ⟨420266, by rfl⟩ : syracuseStep 560355 = 840533) B840533
theorem B560371 : Blo 558808 560371 := bstep (se 1 (by rfl) ⟨420278, by rfl⟩ : syracuseStep 560371 = 840557) B840557
theorem B560387 : Blo 558808 560387 := bstep (se 1 (by rfl) ⟨420290, by rfl⟩ : syracuseStep 560387 = 840581) B840581
theorem B560403 : Blo 558808 560403 := bstep (se 1 (by rfl) ⟨420302, by rfl⟩ : syracuseStep 560403 = 840605) B840605
theorem B560419 : Blo 558808 560419 := bstep (se 1 (by rfl) ⟨420314, by rfl⟩ : syracuseStep 560419 = 840629) B840629
theorem B560435 : Blo 558808 560435 := bstep (se 1 (by rfl) ⟨420326, by rfl⟩ : syracuseStep 560435 = 840653) B840653
theorem B560451 : Blo 558808 560451 := bstep (se 1 (by rfl) ⟨420338, by rfl⟩ : syracuseStep 560451 = 840677) B840677
theorem B560467 : Blo 558808 560467 := bstep (se 1 (by rfl) ⟨420350, by rfl⟩ : syracuseStep 560467 = 840701) B840701
theorem B560483 : Blo 558808 560483 := bstep (se 1 (by rfl) ⟨420362, by rfl⟩ : syracuseStep 560483 = 840725) B840725
theorem B560499 : Blo 558808 560499 := bstep (se 1 (by rfl) ⟨420374, by rfl⟩ : syracuseStep 560499 = 840749) B840749
theorem B560515 : Blo 558808 560515 := bstep (se 1 (by rfl) ⟨420386, by rfl⟩ : syracuseStep 560515 = 840773) B840773
theorem B560531 : Blo 558808 560531 := bstep (se 1 (by rfl) ⟨420398, by rfl⟩ : syracuseStep 560531 = 840797) B840797
theorem B560547 : Blo 558808 560547 := bstep (se 1 (by rfl) ⟨420410, by rfl⟩ : syracuseStep 560547 = 840821) B840821
theorem B560563 : Blo 558808 560563 := bstep (se 1 (by rfl) ⟨420422, by rfl⟩ : syracuseStep 560563 = 840845) B840845
theorem B560579 : Blo 558808 560579 := bstep (se 1 (by rfl) ⟨420434, by rfl⟩ : syracuseStep 560579 = 840869) B840869
theorem B560595 : Blo 558808 560595 := bstep (se 1 (by rfl) ⟨420446, by rfl⟩ : syracuseStep 560595 = 840893) B840893
theorem B560611 : Blo 558808 560611 := bstep (se 1 (by rfl) ⟨420458, by rfl⟩ : syracuseStep 560611 = 840917) B840917
theorem B6393329 : Blo 558808 6393329 := bstep (se 2 (by rfl) ⟨2397498, by rfl⟩ : syracuseStep 6393329 = 4794997) B4794997
theorem B560627 : Blo 558808 560627 := bstep (se 1 (by rfl) ⟨420470, by rfl⟩ : syracuseStep 560627 = 840941) B840941
theorem B560643 : Blo 558808 560643 := bstep (se 1 (by rfl) ⟨420482, by rfl⟩ : syracuseStep 560643 = 840965) B840965
theorem B560659 : Blo 558808 560659 := bstep (se 1 (by rfl) ⟨420494, by rfl⟩ : syracuseStep 560659 = 840989) B840989
theorem B560675 : Blo 558808 560675 := bstep (se 1 (by rfl) ⟨420506, by rfl⟩ : syracuseStep 560675 = 841013) B841013
theorem B560691 : Blo 558808 560691 := bstep (se 1 (by rfl) ⟨420518, by rfl⟩ : syracuseStep 560691 = 841037) B841037
theorem B560707 : Blo 558808 560707 := bstep (se 1 (by rfl) ⟨420530, by rfl⟩ : syracuseStep 560707 = 841061) B841061
theorem B560723 : Blo 558808 560723 := bstep (se 1 (by rfl) ⟨420542, by rfl⟩ : syracuseStep 560723 = 841085) B841085
theorem B560739 : Blo 558808 560739 := bstep (se 1 (by rfl) ⟨420554, by rfl⟩ : syracuseStep 560739 = 841109) B841109
theorem B560755 : Blo 558808 560755 := bstep (se 1 (by rfl) ⟨420566, by rfl⟩ : syracuseStep 560755 = 841133) B841133
theorem B560771 : Blo 558808 560771 := bstep (se 1 (by rfl) ⟨420578, by rfl⟩ : syracuseStep 560771 = 841157) B841157
theorem B560787 : Blo 558808 560787 := bstep (se 1 (by rfl) ⟨420590, by rfl⟩ : syracuseStep 560787 = 841181) B841181
theorem B560803 : Blo 558808 560803 := bstep (se 1 (by rfl) ⟨420602, by rfl⟩ : syracuseStep 560803 = 841205) B841205
theorem B560819 : Blo 558808 560819 := bstep (se 1 (by rfl) ⟨420614, by rfl⟩ : syracuseStep 560819 = 841229) B841229
theorem B560835 : Blo 558808 560835 := bstep (se 1 (by rfl) ⟨420626, by rfl⟩ : syracuseStep 560835 = 841253) B841253
theorem B560851 : Blo 558808 560851 := bstep (se 1 (by rfl) ⟨420638, by rfl⟩ : syracuseStep 560851 = 841277) B841277
theorem B560867 : Blo 558808 560867 := bstep (se 1 (by rfl) ⟨420650, by rfl⟩ : syracuseStep 560867 = 841301) B841301
theorem B560883 : Blo 558808 560883 := bstep (se 1 (by rfl) ⟨420662, by rfl⟩ : syracuseStep 560883 = 841325) B841325
theorem B560899 : Blo 558808 560899 := bstep (se 1 (by rfl) ⟨420674, by rfl⟩ : syracuseStep 560899 = 841349) B841349
theorem B560915 : Blo 558808 560915 := bstep (se 1 (by rfl) ⟨420686, by rfl⟩ : syracuseStep 560915 = 841373) B841373
theorem B560931 : Blo 558808 560931 := bstep (se 1 (by rfl) ⟨420698, by rfl⟩ : syracuseStep 560931 = 841397) B841397
theorem B560947 : Blo 558808 560947 := bstep (se 1 (by rfl) ⟨420710, by rfl⟩ : syracuseStep 560947 = 841421) B841421
theorem B560963 : Blo 558808 560963 := bstep (se 1 (by rfl) ⟨420722, by rfl⟩ : syracuseStep 560963 = 841445) B841445
theorem B560979 : Blo 558808 560979 := bstep (se 1 (by rfl) ⟨420734, by rfl⟩ : syracuseStep 560979 = 841469) B841469
theorem B560995 : Blo 558808 560995 := bstep (se 1 (by rfl) ⟨420746, by rfl⟩ : syracuseStep 560995 = 841493) B841493
theorem B561011 : Blo 558808 561011 := bstep (se 1 (by rfl) ⟨420758, by rfl⟩ : syracuseStep 561011 = 841517) B841517
theorem B561027 : Blo 558808 561027 := bstep (se 1 (by rfl) ⟨420770, by rfl⟩ : syracuseStep 561027 = 841541) B841541
theorem B561043 : Blo 558808 561043 := bstep (se 1 (by rfl) ⟨420782, by rfl⟩ : syracuseStep 561043 = 841565) B841565
theorem B561059 : Blo 558808 561059 := bstep (se 1 (by rfl) ⟨420794, by rfl⟩ : syracuseStep 561059 = 841589) B841589
theorem B561075 : Blo 558808 561075 := bstep (se 1 (by rfl) ⟨420806, by rfl⟩ : syracuseStep 561075 = 841613) B841613
theorem B561091 : Blo 558808 561091 := bstep (se 1 (by rfl) ⟨420818, by rfl⟩ : syracuseStep 561091 = 841637) B841637
theorem B2133965 : Blo 558808 2133965 := bstep (se 3 (by rfl) ⟨400118, by rfl⟩ : syracuseStep 2133965 = 800237) B800237
theorem B561107 : Blo 558808 561107 := bstep (se 1 (by rfl) ⟨420830, by rfl⟩ : syracuseStep 561107 = 841661) B841661
theorem B561123 : Blo 558808 561123 := bstep (se 1 (by rfl) ⟨420842, by rfl⟩ : syracuseStep 561123 = 841685) B841685
theorem B561139 : Blo 558808 561139 := bstep (se 1 (by rfl) ⟨420854, by rfl⟩ : syracuseStep 561139 = 841709) B841709
theorem B561155 : Blo 558808 561155 := bstep (se 1 (by rfl) ⟨420866, by rfl⟩ : syracuseStep 561155 = 841733) B841733
theorem B6230029 : Blo 558808 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B561171 : Blo 558808 561171 := bstep (se 1 (by rfl) ⟨420878, by rfl⟩ : syracuseStep 561171 = 841757) B841757
theorem B561187 : Blo 558808 561187 := bstep (se 1 (by rfl) ⟨420890, by rfl⟩ : syracuseStep 561187 = 841781) B841781
theorem B561203 : Blo 558808 561203 := bstep (se 1 (by rfl) ⟨420902, by rfl⟩ : syracuseStep 561203 = 841805) B841805
theorem B561219 : Blo 558808 561219 := bstep (se 1 (by rfl) ⟨420914, by rfl⟩ : syracuseStep 561219 = 841829) B841829
theorem B561235 : Blo 558808 561235 := bstep (se 1 (by rfl) ⟨420926, by rfl⟩ : syracuseStep 561235 = 841853) B841853
theorem B561251 : Blo 558808 561251 := bstep (se 1 (by rfl) ⟨420938, by rfl⟩ : syracuseStep 561251 = 841877) B841877
theorem B561267 : Blo 558808 561267 := bstep (se 1 (by rfl) ⟨420950, by rfl⟩ : syracuseStep 561267 = 841901) B841901
theorem B561283 : Blo 558808 561283 := bstep (se 1 (by rfl) ⟨420962, by rfl⟩ : syracuseStep 561283 = 841925) B841925
theorem B561299 : Blo 558808 561299 := bstep (se 1 (by rfl) ⟨420974, by rfl⟩ : syracuseStep 561299 = 841949) B841949
theorem B561315 : Blo 558808 561315 := bstep (se 1 (by rfl) ⟨420986, by rfl⟩ : syracuseStep 561315 = 841973) B841973
theorem B561331 : Blo 558808 561331 := bstep (se 1 (by rfl) ⟨420998, by rfl⟩ : syracuseStep 561331 = 841997) B841997
theorem B561347 : Blo 558808 561347 := bstep (se 1 (by rfl) ⟨421010, by rfl⟩ : syracuseStep 561347 = 842021) B842021
theorem B561363 : Blo 558808 561363 := bstep (se 1 (by rfl) ⟨421022, by rfl⟩ : syracuseStep 561363 = 842045) B842045
theorem B561379 : Blo 558808 561379 := bstep (se 1 (by rfl) ⟨421034, by rfl⟩ : syracuseStep 561379 = 842069) B842069
theorem B4264163 : Blo 558808 4264163 := bstep (se 1 (by rfl) ⟨3198122, by rfl⟩ : syracuseStep 4264163 = 6396245) B6396245
theorem B561395 : Blo 558808 561395 := bstep (se 1 (by rfl) ⟨421046, by rfl⟩ : syracuseStep 561395 = 842093) B842093
theorem B561411 : Blo 558808 561411 := bstep (se 1 (by rfl) ⟨421058, by rfl⟩ : syracuseStep 561411 = 842117) B842117
theorem B561427 : Blo 558808 561427 := bstep (se 1 (by rfl) ⟨421070, by rfl⟩ : syracuseStep 561427 = 842141) B842141
theorem B561443 : Blo 558808 561443 := bstep (se 1 (by rfl) ⟨421082, by rfl⟩ : syracuseStep 561443 = 842165) B842165
theorem B561459 : Blo 558808 561459 := bstep (se 1 (by rfl) ⟨421094, by rfl⟩ : syracuseStep 561459 = 842189) B842189
theorem B561475 : Blo 558808 561475 := bstep (se 1 (by rfl) ⟨421106, by rfl⟩ : syracuseStep 561475 = 842213) B842213
theorem B561491 : Blo 558808 561491 := bstep (se 1 (by rfl) ⟨421118, by rfl⟩ : syracuseStep 561491 = 842237) B842237
theorem B561507 : Blo 558808 561507 := bstep (se 1 (by rfl) ⟨421130, by rfl⟩ : syracuseStep 561507 = 842261) B842261
theorem B561523 : Blo 558808 561523 := bstep (se 1 (by rfl) ⟨421142, by rfl⟩ : syracuseStep 561523 = 842285) B842285
theorem B561539 : Blo 558808 561539 := bstep (se 1 (by rfl) ⟨421154, by rfl⟩ : syracuseStep 561539 = 842309) B842309
theorem B561555 : Blo 558808 561555 := bstep (se 1 (by rfl) ⟨421166, by rfl⟩ : syracuseStep 561555 = 842333) B842333
theorem B561571 : Blo 558808 561571 := bstep (se 1 (by rfl) ⟨421178, by rfl⟩ : syracuseStep 561571 = 842357) B842357
theorem B561587 : Blo 558808 561587 := bstep (se 1 (by rfl) ⟨421190, by rfl⟩ : syracuseStep 561587 = 842381) B842381
theorem B561603 : Blo 558808 561603 := bstep (se 1 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 561603 = 842405) B842405
theorem B561619 : Blo 558808 561619 := bstep (se 1 (by rfl) ⟨421214, by rfl⟩ : syracuseStep 561619 = 842429) B842429
theorem B561635 : Blo 558808 561635 := bstep (se 1 (by rfl) ⟨421226, by rfl⟩ : syracuseStep 561635 = 842453) B842453
theorem B561651 : Blo 558808 561651 := bstep (se 1 (by rfl) ⟨421238, by rfl⟩ : syracuseStep 561651 = 842477) B842477
theorem B561667 : Blo 558808 561667 := bstep (se 1 (by rfl) ⟨421250, by rfl⟩ : syracuseStep 561667 = 842501) B842501
theorem B561683 : Blo 558808 561683 := bstep (se 1 (by rfl) ⟨421262, by rfl⟩ : syracuseStep 561683 = 842525) B842525
theorem B561699 : Blo 558808 561699 := bstep (se 1 (by rfl) ⟨421274, by rfl⟩ : syracuseStep 561699 = 842549) B842549
theorem B561715 : Blo 558808 561715 := bstep (se 1 (by rfl) ⟨421286, by rfl⟩ : syracuseStep 561715 = 842573) B842573
theorem B561731 : Blo 558808 561731 := bstep (se 1 (by rfl) ⟨421298, by rfl⟩ : syracuseStep 561731 = 842597) B842597
theorem B561747 : Blo 558808 561747 := bstep (se 1 (by rfl) ⟨421310, by rfl⟩ : syracuseStep 561747 = 842621) B842621
theorem B561763 : Blo 558808 561763 := bstep (se 1 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 561763 = 842645) B842645
theorem B561779 : Blo 558808 561779 := bstep (se 1 (by rfl) ⟨421334, by rfl⟩ : syracuseStep 561779 = 842669) B842669
theorem B561795 : Blo 558808 561795 := bstep (se 1 (by rfl) ⟨421346, by rfl⟩ : syracuseStep 561795 = 842693) B842693
theorem B561811 : Blo 558808 561811 := bstep (se 1 (by rfl) ⟨421358, by rfl⟩ : syracuseStep 561811 = 842717) B842717
theorem B561827 : Blo 558808 561827 := bstep (se 1 (by rfl) ⟨421370, by rfl⟩ : syracuseStep 561827 = 842741) B842741
theorem B561843 : Blo 558808 561843 := bstep (se 1 (by rfl) ⟨421382, by rfl⟩ : syracuseStep 561843 = 842765) B842765
theorem B561859 : Blo 558808 561859 := bstep (se 1 (by rfl) ⟨421394, by rfl⟩ : syracuseStep 561859 = 842789) B842789
theorem B561875 : Blo 558808 561875 := bstep (se 1 (by rfl) ⟨421406, by rfl⟩ : syracuseStep 561875 = 842813) B842813
theorem B561891 : Blo 558808 561891 := bstep (se 1 (by rfl) ⟨421418, by rfl⟩ : syracuseStep 561891 = 842837) B842837
theorem B561907 : Blo 558808 561907 := bstep (se 1 (by rfl) ⟨421430, by rfl⟩ : syracuseStep 561907 = 842861) B842861
theorem B561923 : Blo 558808 561923 := bstep (se 1 (by rfl) ⟨421442, by rfl⟩ : syracuseStep 561923 = 842885) B842885
theorem B561939 : Blo 558808 561939 := bstep (se 1 (by rfl) ⟨421454, by rfl⟩ : syracuseStep 561939 = 842909) B842909
theorem B561955 : Blo 558808 561955 := bstep (se 1 (by rfl) ⟨421466, by rfl⟩ : syracuseStep 561955 = 842933) B842933
theorem B561971 : Blo 558808 561971 := bstep (se 1 (by rfl) ⟨421478, by rfl⟩ : syracuseStep 561971 = 842957) B842957
theorem B561987 : Blo 558808 561987 := bstep (se 1 (by rfl) ⟨421490, by rfl⟩ : syracuseStep 561987 = 842981) B842981
theorem B562003 : Blo 558808 562003 := bstep (se 1 (by rfl) ⟨421502, by rfl⟩ : syracuseStep 562003 = 843005) B843005
theorem B758627 : Blo 558808 758627 := bstep (se 1 (by rfl) ⟨568970, by rfl⟩ : syracuseStep 758627 = 1137941) B1137941
theorem B562019 : Blo 558808 562019 := bstep (se 1 (by rfl) ⟨421514, by rfl⟩ : syracuseStep 562019 = 843029) B843029
theorem B562035 : Blo 558808 562035 := bstep (se 1 (by rfl) ⟨421526, by rfl⟩ : syracuseStep 562035 = 843053) B843053
theorem B562051 : Blo 558808 562051 := bstep (se 1 (by rfl) ⟨421538, by rfl⟩ : syracuseStep 562051 = 843077) B843077
theorem B562067 : Blo 558808 562067 := bstep (se 1 (by rfl) ⟨421550, by rfl⟩ : syracuseStep 562067 = 843101) B843101
theorem B562083 : Blo 558808 562083 := bstep (se 1 (by rfl) ⟨421562, by rfl⟩ : syracuseStep 562083 = 843125) B843125
theorem B562099 : Blo 558808 562099 := bstep (se 1 (by rfl) ⟨421574, by rfl⟩ : syracuseStep 562099 = 843149) B843149
theorem B562115 : Blo 558808 562115 := bstep (se 1 (by rfl) ⟨421586, by rfl⟩ : syracuseStep 562115 = 843173) B843173
theorem B562131 : Blo 558808 562131 := bstep (se 1 (by rfl) ⟨421598, by rfl⟩ : syracuseStep 562131 = 843197) B843197
theorem B562147 : Blo 558808 562147 := bstep (se 1 (by rfl) ⟨421610, by rfl⟩ : syracuseStep 562147 = 843221) B843221
theorem B562163 : Blo 558808 562163 := bstep (se 1 (by rfl) ⟨421622, by rfl⟩ : syracuseStep 562163 = 843245) B843245
theorem B562179 : Blo 558808 562179 := bstep (se 1 (by rfl) ⟨421634, by rfl⟩ : syracuseStep 562179 = 843269) B843269
theorem B562195 : Blo 558808 562195 := bstep (se 1 (by rfl) ⟨421646, by rfl⟩ : syracuseStep 562195 = 843293) B843293
theorem B562211 : Blo 558808 562211 := bstep (se 1 (by rfl) ⟨421658, by rfl⟩ : syracuseStep 562211 = 843317) B843317
theorem B1512497 : Blo 558808 1512497 := bstep (se 2 (by rfl) ⟨567186, by rfl⟩ : syracuseStep 1512497 = 1134373) B1134373
theorem B562227 : Blo 558808 562227 := bstep (se 1 (by rfl) ⟨421670, by rfl⟩ : syracuseStep 562227 = 843341) B843341
theorem B562243 : Blo 558808 562243 := bstep (se 1 (by rfl) ⟨421682, by rfl⟩ : syracuseStep 562243 = 843365) B843365
theorem B562259 : Blo 558808 562259 := bstep (se 1 (by rfl) ⟨421694, by rfl⟩ : syracuseStep 562259 = 843389) B843389
theorem B562275 : Blo 558808 562275 := bstep (se 1 (by rfl) ⟨421706, by rfl⟩ : syracuseStep 562275 = 843413) B843413
theorem B562291 : Blo 558808 562291 := bstep (se 1 (by rfl) ⟨421718, by rfl⟩ : syracuseStep 562291 = 843437) B843437
theorem B562307 : Blo 558808 562307 := bstep (se 1 (by rfl) ⟨421730, by rfl⟩ : syracuseStep 562307 = 843461) B843461
theorem B562323 : Blo 558808 562323 := bstep (se 1 (by rfl) ⟨421742, by rfl⟩ : syracuseStep 562323 = 843485) B843485
theorem B2397347 : Blo 558808 2397347 := bstep (se 1 (by rfl) ⟨1798010, by rfl⟩ : syracuseStep 2397347 = 3596021) B3596021
theorem B562339 : Blo 558808 562339 := bstep (se 1 (by rfl) ⟨421754, by rfl⟩ : syracuseStep 562339 = 843509) B843509
theorem B562355 : Blo 558808 562355 := bstep (se 1 (by rfl) ⟨421766, by rfl⟩ : syracuseStep 562355 = 843533) B843533
theorem B562371 : Blo 558808 562371 := bstep (se 1 (by rfl) ⟨421778, by rfl⟩ : syracuseStep 562371 = 843557) B843557
theorem B562387 : Blo 558808 562387 := bstep (se 1 (by rfl) ⟨421790, by rfl⟩ : syracuseStep 562387 = 843581) B843581
theorem B562403 : Blo 558808 562403 := bstep (se 1 (by rfl) ⟨421802, by rfl⟩ : syracuseStep 562403 = 843605) B843605
theorem B562419 : Blo 558808 562419 := bstep (se 1 (by rfl) ⟨421814, by rfl⟩ : syracuseStep 562419 = 843629) B843629
theorem B562435 : Blo 558808 562435 := bstep (se 1 (by rfl) ⟨421826, by rfl⟩ : syracuseStep 562435 = 843653) B843653
theorem B922897 : Blo 558808 922897 := bstep (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) B692173
theorem B562451 : Blo 558808 562451 := bstep (se 1 (by rfl) ⟨421838, by rfl⟩ : syracuseStep 562451 = 843677) B843677
theorem B3183907 : Blo 558808 3183907 := bstep (se 1 (by rfl) ⟨2387930, by rfl⟩ : syracuseStep 3183907 = 4775861) B4775861
theorem B562467 : Blo 558808 562467 := bstep (se 1 (by rfl) ⟨421850, by rfl⟩ : syracuseStep 562467 = 843701) B843701
theorem B562483 : Blo 558808 562483 := bstep (se 1 (by rfl) ⟨421862, by rfl⟩ : syracuseStep 562483 = 843725) B843725
theorem B562499 : Blo 558808 562499 := bstep (se 1 (by rfl) ⟨421874, by rfl⟩ : syracuseStep 562499 = 843749) B843749
theorem B562515 : Blo 558808 562515 := bstep (se 1 (by rfl) ⟨421886, by rfl⟩ : syracuseStep 562515 = 843773) B843773
theorem B562531 : Blo 558808 562531 := bstep (se 1 (by rfl) ⟨421898, by rfl⟩ : syracuseStep 562531 = 843797) B843797
theorem B562547 : Blo 558808 562547 := bstep (se 1 (by rfl) ⟨421910, by rfl⟩ : syracuseStep 562547 = 843821) B843821
theorem B562563 : Blo 558808 562563 := bstep (se 1 (by rfl) ⟨421922, by rfl⟩ : syracuseStep 562563 = 843845) B843845
theorem B562579 : Blo 558808 562579 := bstep (se 1 (by rfl) ⟨421934, by rfl⟩ : syracuseStep 562579 = 843869) B843869
theorem B562595 : Blo 558808 562595 := bstep (se 1 (by rfl) ⟨421946, by rfl⟩ : syracuseStep 562595 = 843893) B843893
theorem B562611 : Blo 558808 562611 := bstep (se 1 (by rfl) ⟨421958, by rfl⟩ : syracuseStep 562611 = 843917) B843917
theorem B562627 : Blo 558808 562627 := bstep (se 1 (by rfl) ⟨421970, by rfl⟩ : syracuseStep 562627 = 843941) B843941
theorem B562643 : Blo 558808 562643 := bstep (se 1 (by rfl) ⟨421982, by rfl⟩ : syracuseStep 562643 = 843965) B843965
theorem B562659 : Blo 558808 562659 := bstep (se 1 (by rfl) ⟨421994, by rfl⟩ : syracuseStep 562659 = 843989) B843989
theorem B562675 : Blo 558808 562675 := bstep (se 1 (by rfl) ⟨422006, by rfl⟩ : syracuseStep 562675 = 844013) B844013
theorem B562691 : Blo 558808 562691 := bstep (se 1 (by rfl) ⟨422018, by rfl⟩ : syracuseStep 562691 = 844037) B844037
theorem B562707 : Blo 558808 562707 := bstep (se 1 (by rfl) ⟨422030, by rfl⟩ : syracuseStep 562707 = 844061) B844061
theorem B759331 : Blo 558808 759331 := bstep (se 1 (by rfl) ⟨569498, by rfl⟩ : syracuseStep 759331 = 1138997) B1138997
theorem B562723 : Blo 558808 562723 := bstep (se 1 (by rfl) ⟨422042, by rfl⟩ : syracuseStep 562723 = 844085) B844085
theorem B1414705 : Blo 558808 1414705 := bstep (se 2 (by rfl) ⟨530514, by rfl⟩ : syracuseStep 1414705 = 1061029) B1061029
theorem B562739 : Blo 558808 562739 := bstep (se 1 (by rfl) ⟨422054, by rfl⟩ : syracuseStep 562739 = 844109) B844109
theorem B562755 : Blo 558808 562755 := bstep (se 1 (by rfl) ⟨422066, by rfl⟩ : syracuseStep 562755 = 844133) B844133
theorem B562771 : Blo 558808 562771 := bstep (se 1 (by rfl) ⟨422078, by rfl⟩ : syracuseStep 562771 = 844157) B844157
theorem B562787 : Blo 558808 562787 := bstep (se 1 (by rfl) ⟨422090, by rfl⟩ : syracuseStep 562787 = 844181) B844181
theorem B562803 : Blo 558808 562803 := bstep (se 1 (by rfl) ⟨422102, by rfl⟩ : syracuseStep 562803 = 844205) B844205
theorem B12916421 : Blo 558808 12916421 := bstep (se 4 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 12916421 = 2421829) B2421829
theorem B45913877 : Blo 558808 45913877 := bstep (se 6 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 45913877 = 2152213) B2152213
theorem B3184433 : Blo 558808 3184433 := bstep (se 2 (by rfl) ⟨1194162, by rfl⟩ : syracuseStep 3184433 = 2388325) B2388325
theorem B1414979 : Blo 558808 1414979 := bstep (se 1 (by rfl) ⟨1061234, by rfl⟩ : syracuseStep 1414979 = 2122469) B2122469
theorem B3413873 : Blo 558808 3413873 := bstep (se 2 (by rfl) ⟨1280202, by rfl⟩ : syracuseStep 3413873 = 2560405) B2560405
theorem B1349585 : Blo 558808 1349585 := bstep (se 2 (by rfl) ⟨506094, by rfl⟩ : syracuseStep 1349585 = 1012189) B1012189
theorem B1415171 : Blo 558808 1415171 := bstep (se 1 (by rfl) ⟨1061378, by rfl⟩ : syracuseStep 1415171 = 2122757) B2122757
theorem B2136077 : Blo 558808 2136077 := bstep (se 3 (by rfl) ⟨400514, by rfl⟩ : syracuseStep 2136077 = 801029) B801029
theorem B628771 : Blo 558808 628771 := bstep (se 1 (by rfl) ⟨471578, by rfl⟩ : syracuseStep 628771 = 943157) B943157
theorem B628915 : Blo 558808 628915 := bstep (se 1 (by rfl) ⟨471686, by rfl⟩ : syracuseStep 628915 = 943373) B943373
theorem B1513667 : Blo 558808 1513667 := bstep (se 1 (by rfl) ⟨1135250, by rfl⟩ : syracuseStep 1513667 = 2270501) B2270501
theorem B760099 : Blo 558808 760099 := bstep (se 1 (by rfl) ⟨570074, by rfl⟩ : syracuseStep 760099 = 1140149) B1140149
theorem B629059 : Blo 558808 629059 := bstep (se 1 (by rfl) ⟨471794, by rfl⟩ : syracuseStep 629059 = 943589) B943589
theorem B1710467 : Blo 558808 1710467 := bstep (se 1 (by rfl) ⟨1282850, by rfl⟩ : syracuseStep 1710467 = 2565701) B2565701
theorem B629203 : Blo 558808 629203 := bstep (se 1 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 629203 = 943805) B943805
theorem B629347 : Blo 558808 629347 := bstep (se 1 (by rfl) ⟨472010, by rfl⟩ : syracuseStep 629347 = 944021) B944021
theorem B4790897 : Blo 558808 4790897 := bstep (se 2 (by rfl) ⟨1796586, by rfl⟩ : syracuseStep 4790897 = 3593173) B3593173
theorem B760531 : Blo 558808 760531 := bstep (se 1 (by rfl) ⟨570398, by rfl⟩ : syracuseStep 760531 = 1140797) B1140797
theorem B629491 : Blo 558808 629491 := bstep (se 1 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 629491 = 944237) B944237
theorem B2136881 : Blo 558808 2136881 := bstep (se 2 (by rfl) ⟨801330, by rfl⟩ : syracuseStep 2136881 = 1602661) B1602661
theorem B629635 : Blo 558808 629635 := bstep (se 1 (by rfl) ⟨472226, by rfl⟩ : syracuseStep 629635 = 944453) B944453
theorem B1416113 : Blo 558808 1416113 := bstep (se 2 (by rfl) ⟨531042, by rfl⟩ : syracuseStep 1416113 = 1062085) B1062085
theorem B1416163 : Blo 558808 1416163 := bstep (se 1 (by rfl) ⟨1062122, by rfl⟩ : syracuseStep 1416163 = 2124245) B2124245
theorem B1514477 : Blo 558808 1514477 := bstep (se 3 (by rfl) ⟨283964, by rfl⟩ : syracuseStep 1514477 = 567929) B567929
theorem B629779 : Blo 558808 629779 := bstep (se 1 (by rfl) ⟨472334, by rfl⟩ : syracuseStep 629779 = 944669) B944669
theorem B1416305 : Blo 558808 1416305 := bstep (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) B1062229
theorem B2399345 : Blo 558808 2399345 := bstep (se 2 (by rfl) ⟨899754, by rfl⟩ : syracuseStep 2399345 = 1799509) B1799509
theorem B629923 : Blo 558808 629923 := bstep (se 1 (by rfl) ⟨472442, by rfl⟩ : syracuseStep 629923 = 944885) B944885
theorem B3185891 : Blo 558808 3185891 := bstep (se 1 (by rfl) ⟨2389418, by rfl⟩ : syracuseStep 3185891 = 4778837) B4778837
theorem B1514737 : Blo 558808 1514737 := bstep (se 2 (by rfl) ⟨568026, by rfl⟩ : syracuseStep 1514737 = 1136053) B1136053
theorem B597299 : Blo 558808 597299 := bstep (se 1 (by rfl) ⟨447974, by rfl⟩ : syracuseStep 597299 = 895949) B895949
theorem B630067 : Blo 558808 630067 := bstep (se 1 (by rfl) ⟨472550, by rfl⟩ : syracuseStep 630067 = 945101) B945101
theorem B1023331 : Blo 558808 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B630211 : Blo 558808 630211 := bstep (se 1 (by rfl) ⟨472658, by rfl⟩ : syracuseStep 630211 = 945317) B945317
theorem B630355 : Blo 558808 630355 := bstep (se 1 (by rfl) ⟨472766, by rfl⟩ : syracuseStep 630355 = 945533) B945533
theorem B6332003 : Blo 558808 6332003 := bstep (se 1 (by rfl) ⟨4749002, by rfl⟩ : syracuseStep 6332003 = 9498005) B9498005
theorem B925409 : Blo 558808 925409 := bstep (se 2 (by rfl) ⟨347028, by rfl⟩ : syracuseStep 925409 = 694057) B694057
theorem B630499 : Blo 558808 630499 := bstep (se 1 (by rfl) ⟨472874, by rfl⟩ : syracuseStep 630499 = 945749) B945749
theorem B8625973 : Blo 558808 8625973 := bstep (se 5 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 8625973 = 808685) B808685
theorem B630643 : Blo 558808 630643 := bstep (se 1 (by rfl) ⟨472982, by rfl⟩ : syracuseStep 630643 = 945965) B945965
theorem B1515395 : Blo 558808 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B630787 : Blo 558808 630787 := bstep (se 1 (by rfl) ⟨473090, by rfl⟩ : syracuseStep 630787 = 946181) B946181
theorem B598051 : Blo 558808 598051 := bstep (se 1 (by rfl) ⟨448538, by rfl⟩ : syracuseStep 598051 = 897077) B897077
theorem B1417297 : Blo 558808 1417297 := bstep (se 2 (by rfl) ⟨531486, by rfl⟩ : syracuseStep 1417297 = 1062973) B1062973
theorem B34480241 : Blo 558808 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B630931 : Blo 558808 630931 := bstep (se 1 (by rfl) ⟨473198, by rfl⟩ : syracuseStep 630931 = 946397) B946397
theorem B631075 : Blo 558808 631075 := bstep (se 1 (by rfl) ⟨473306, by rfl⟩ : syracuseStep 631075 = 946613) B946613
theorem B1417571 : Blo 558808 1417571 := bstep (se 1 (by rfl) ⟨1063178, by rfl⟩ : syracuseStep 1417571 = 2126357) B2126357
theorem B631219 : Blo 558808 631219 := bstep (se 1 (by rfl) ⟨473414, by rfl⟩ : syracuseStep 631219 = 946829) B946829
theorem B1417763 : Blo 558808 1417763 := bstep (se 1 (by rfl) ⟨1063322, by rfl⟩ : syracuseStep 1417763 = 2126645) B2126645
theorem B1516067 : Blo 558808 1516067 := bstep (se 1 (by rfl) ⟨1137050, by rfl⟩ : syracuseStep 1516067 = 2274101) B2274101
theorem B1352227 : Blo 558808 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B631363 : Blo 558808 631363 := bstep (se 1 (by rfl) ⟨473522, by rfl⟩ : syracuseStep 631363 = 947045) B947045
theorem B631507 : Blo 558808 631507 := bstep (se 1 (by rfl) ⟨473630, by rfl⟩ : syracuseStep 631507 = 947261) B947261
theorem B4104931 : Blo 558808 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B631651 : Blo 558808 631651 := bstep (se 1 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 631651 = 947477) B947477
theorem B631795 : Blo 558808 631795 := bstep (se 1 (by rfl) ⟨473846, by rfl⟩ : syracuseStep 631795 = 947693) B947693
theorem B4793357 : Blo 558808 4793357 := bstep (se 3 (by rfl) ⟨898754, by rfl⟩ : syracuseStep 4793357 = 1797509) B1797509
theorem B3187781 : Blo 558808 3187781 := bstep (se 4 (by rfl) ⟨298854, by rfl⟩ : syracuseStep 3187781 = 597709) B597709
theorem B959585 : Blo 558808 959585 := bstep (se 2 (by rfl) ⟨359844, by rfl⟩ : syracuseStep 959585 = 719689) B719689
theorem B631939 : Blo 558808 631939 := bstep (se 1 (by rfl) ⟨473954, by rfl⟩ : syracuseStep 631939 = 947909) B947909
theorem B632083 : Blo 558808 632083 := bstep (se 1 (by rfl) ⟨474062, by rfl⟩ : syracuseStep 632083 = 948125) B948125
theorem B1516909 : Blo 558808 1516909 := bstep (se 3 (by rfl) ⟨284420, by rfl⟩ : syracuseStep 1516909 = 568841) B568841
theorem B599443 : Blo 558808 599443 := bstep (se 1 (by rfl) ⟨449582, by rfl⟩ : syracuseStep 599443 = 899165) B899165
theorem B632227 : Blo 558808 632227 := bstep (se 1 (by rfl) ⟨474170, by rfl⟩ : syracuseStep 632227 = 948341) B948341
theorem B4269509 : Blo 558808 4269509 := bstep (se 4 (by rfl) ⟨400266, by rfl⟩ : syracuseStep 4269509 = 800533) B800533
theorem B1418705 : Blo 558808 1418705 := bstep (se 2 (by rfl) ⟨532014, by rfl⟩ : syracuseStep 1418705 = 1064029) B1064029
theorem B1418755 : Blo 558808 1418755 := bstep (se 1 (by rfl) ⟨1064066, by rfl⟩ : syracuseStep 1418755 = 2128133) B2128133
theorem B2401805 : Blo 558808 2401805 := bstep (se 3 (by rfl) ⟨450338, by rfl⟩ : syracuseStep 2401805 = 900677) B900677
theorem B632371 : Blo 558808 632371 := bstep (se 1 (by rfl) ⟨474278, by rfl⟩ : syracuseStep 632371 = 948557) B948557
theorem B4531781 : Blo 558808 4531781 := bstep (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) B849709
theorem B1418897 : Blo 558808 1418897 := bstep (se 2 (by rfl) ⟨532086, by rfl⟩ : syracuseStep 1418897 = 1064173) B1064173
theorem B632515 : Blo 558808 632515 := bstep (se 1 (by rfl) ⟨474386, by rfl⟩ : syracuseStep 632515 = 948773) B948773
theorem B796387 : Blo 558808 796387 := bstep (se 1 (by rfl) ⟨597290, by rfl⟩ : syracuseStep 796387 = 1194581) B1194581
theorem B632659 : Blo 558808 632659 := bstep (se 1 (by rfl) ⟨474494, by rfl⟩ : syracuseStep 632659 = 948989) B948989
theorem B1025905 : Blo 558808 1025905 := bstep (se 2 (by rfl) ⟨384714, by rfl⟩ : syracuseStep 1025905 = 769429) B769429
theorem B3024803 : Blo 558808 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B9086917 : Blo 558808 9086917 := bstep (se 4 (by rfl) ⟨851898, by rfl⟩ : syracuseStep 9086917 = 1703797) B1703797
theorem B567251 : Blo 558808 567251 := bstep (se 1 (by rfl) ⟨425438, by rfl⟩ : syracuseStep 567251 = 850877) B850877
theorem B632803 : Blo 558808 632803 := bstep (se 1 (by rfl) ⟨474602, by rfl⟩ : syracuseStep 632803 = 949205) B949205
theorem B632947 : Blo 558808 632947 := bstep (se 1 (by rfl) ⟨474710, by rfl⟩ : syracuseStep 632947 = 949421) B949421
theorem B633091 : Blo 558808 633091 := bstep (se 1 (by rfl) ⟨474818, by rfl⟩ : syracuseStep 633091 = 949637) B949637
theorem B895283 : Blo 558808 895283 := bstep (se 1 (by rfl) ⟨671462, by rfl⟩ : syracuseStep 895283 = 1342925) B1342925
theorem B895315 : Blo 558808 895315 := bstep (se 1 (by rfl) ⟨671486, by rfl⟩ : syracuseStep 895315 = 1342973) B1342973
theorem B18196933 : Blo 558808 18196933 := bstep (se 4 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 18196933 = 3411925) B3411925
theorem B1944145 : Blo 558808 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B1419889 : Blo 558808 1419889 := bstep (se 2 (by rfl) ⟨532458, by rfl⟩ : syracuseStep 1419889 = 1064917) B1064917
theorem B2829005 : Blo 558808 2829005 := bstep (se 3 (by rfl) ⟨530438, by rfl⟩ : syracuseStep 2829005 = 1060877) B1060877
theorem B4303601 : Blo 558808 4303601 := bstep (se 2 (by rfl) ⟨1613850, by rfl⟩ : syracuseStep 4303601 = 3227701) B3227701
theorem B797521 : Blo 558808 797521 := bstep (se 2 (by rfl) ⟨299070, by rfl⟩ : syracuseStep 797521 = 598141) B598141
theorem B1420163 : Blo 558808 1420163 := bstep (se 1 (by rfl) ⟨1065122, by rfl⟩ : syracuseStep 1420163 = 2130245) B2130245
theorem B797617 : Blo 558808 797617 := bstep (se 2 (by rfl) ⟨299106, by rfl⟩ : syracuseStep 797617 = 598213) B598213
theorem B3583025 : Blo 558808 3583025 := bstep (se 2 (by rfl) ⟨1343634, by rfl⟩ : syracuseStep 3583025 = 2687269) B2687269
theorem B2403377 : Blo 558808 2403377 := bstep (se 2 (by rfl) ⟨901266, by rfl⟩ : syracuseStep 2403377 = 1802533) B1802533
theorem B1420355 : Blo 558808 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B896243 : Blo 558808 896243 := bstep (se 1 (by rfl) ⟨672182, by rfl⟩ : syracuseStep 896243 = 1344365) B1344365
theorem B896321 : Blo 558808 896321 := bstep (se 2 (by rfl) ⟨336120, by rfl⟩ : syracuseStep 896321 = 672241) B672241
theorem B798113 : Blo 558808 798113 := bstep (se 2 (by rfl) ⟨299292, by rfl⟩ : syracuseStep 798113 = 598585) B598585
theorem B7187939 : Blo 558808 7187939 := bstep (se 1 (by rfl) ⟨5390954, by rfl⟩ : syracuseStep 7187939 = 10781909) B10781909
theorem B896545 : Blo 558808 896545 := bstep (se 2 (by rfl) ⟨336204, by rfl⟩ : syracuseStep 896545 = 672409) B672409
theorem B4599665 : Blo 558808 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B1519505 : Blo 558808 1519505 := bstep (se 2 (by rfl) ⟨569814, by rfl⟩ : syracuseStep 1519505 = 1139629) B1139629
theorem B1257425 : Blo 558808 1257425 := bstep (se 2 (by rfl) ⟨471534, by rfl⟩ : syracuseStep 1257425 = 943069) B943069
theorem B1257443 : Blo 558808 1257443 := bstep (se 1 (by rfl) ⟨943082, by rfl⟩ : syracuseStep 1257443 = 1886165) B1886165
theorem B1421297 : Blo 558808 1421297 := bstep (se 2 (by rfl) ⟨532986, by rfl⟩ : syracuseStep 1421297 = 1065973) B1065973
theorem B1421347 : Blo 558808 1421347 := bstep (se 1 (by rfl) ⟨1066010, by rfl⟩ : syracuseStep 1421347 = 2132021) B2132021
theorem B1060931 : Blo 558808 1060931 := bstep (se 1 (by rfl) ⟨795698, by rfl⟩ : syracuseStep 1060931 = 1591397) B1591397
theorem B1618019 : Blo 558808 1618019 := bstep (se 1 (by rfl) ⟨1213514, by rfl⟩ : syracuseStep 1618019 = 2427029) B2427029
theorem B1421489 : Blo 558808 1421489 := bstep (se 2 (by rfl) ⟨533058, by rfl⟩ : syracuseStep 1421489 = 1066117) B1066117
theorem B569539 : Blo 558808 569539 := bstep (se 1 (by rfl) ⟨427154, by rfl⟩ : syracuseStep 569539 = 854309) B854309
theorem B1257713 : Blo 558808 1257713 := bstep (se 2 (by rfl) ⟨471642, by rfl⟩ : syracuseStep 1257713 = 943285) B943285
theorem B1257731 : Blo 558808 1257731 := bstep (se 1 (by rfl) ⟨943298, by rfl⟩ : syracuseStep 1257731 = 1886597) B1886597
theorem B798979 : Blo 558808 798979 := bstep (se 1 (by rfl) ⟨599234, by rfl⟩ : syracuseStep 798979 = 1198469) B1198469
theorem B799075 : Blo 558808 799075 := bstep (se 1 (by rfl) ⟨599306, by rfl⟩ : syracuseStep 799075 = 1198613) B1198613
theorem B1258001 : Blo 558808 1258001 := bstep (se 2 (by rfl) ⟨471750, by rfl⟩ : syracuseStep 1258001 = 943501) B943501
theorem B1258019 : Blo 558808 1258019 := bstep (se 1 (by rfl) ⟨943514, by rfl⟩ : syracuseStep 1258019 = 1887029) B1887029
theorem B3846797 : Blo 558808 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B9614051 : Blo 558808 9614051 := bstep (se 1 (by rfl) ⟨7210538, by rfl⟩ : syracuseStep 9614051 = 14421077) B14421077
theorem B1258289 : Blo 558808 1258289 := bstep (se 2 (by rfl) ⟨471858, by rfl⟩ : syracuseStep 1258289 = 943717) B943717
theorem B1258307 : Blo 558808 1258307 := bstep (se 1 (by rfl) ⟨943730, by rfl⟩ : syracuseStep 1258307 = 1887461) B1887461
theorem B799571 : Blo 558808 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B1258577 : Blo 558808 1258577 := bstep (se 2 (by rfl) ⟨471966, by rfl⟩ : syracuseStep 1258577 = 943933) B943933
theorem B1258595 : Blo 558808 1258595 := bstep (se 1 (by rfl) ⟨943946, by rfl⟩ : syracuseStep 1258595 = 1887893) B1887893
theorem B1062001 : Blo 558808 1062001 := bstep (se 2 (by rfl) ⟨398250, by rfl⟩ : syracuseStep 1062001 = 796501) B796501
theorem B1946755 : Blo 558808 1946755 := bstep (se 1 (by rfl) ⟨1460066, by rfl⟩ : syracuseStep 1946755 = 2920133) B2920133
theorem B1422481 : Blo 558808 1422481 := bstep (se 2 (by rfl) ⟨533430, by rfl⟩ : syracuseStep 1422481 = 1066861) B1066861
theorem B6075589 : Blo 558808 6075589 := bstep (se 4 (by rfl) ⟨569586, by rfl⟩ : syracuseStep 6075589 = 1139173) B1139173
theorem B898307 : Blo 558808 898307 := bstep (se 1 (by rfl) ⟨673730, by rfl⟩ : syracuseStep 898307 = 1347461) B1347461
theorem B1848685 : Blo 558808 1848685 := bstep (se 3 (by rfl) ⟨346628, by rfl⟩ : syracuseStep 1848685 = 693257) B693257
theorem B1258865 : Blo 558808 1258865 := bstep (se 2 (by rfl) ⟨472074, by rfl⟩ : syracuseStep 1258865 = 944149) B944149
theorem B1258883 : Blo 558808 1258883 := bstep (se 1 (by rfl) ⟨944162, by rfl⟩ : syracuseStep 1258883 = 1888325) B1888325
theorem B1422755 : Blo 558808 1422755 := bstep (se 1 (by rfl) ⟨1067066, by rfl⟩ : syracuseStep 1422755 = 2134133) B2134133
theorem B898499 : Blo 558808 898499 := bstep (se 1 (by rfl) ⟨673874, by rfl⟩ : syracuseStep 898499 = 1347749) B1347749
theorem B3585485 : Blo 558808 3585485 := bstep (se 3 (by rfl) ⟨672278, by rfl⟩ : syracuseStep 3585485 = 1344557) B1344557
theorem B800209 : Blo 558808 800209 := bstep (se 2 (by rfl) ⟨300078, by rfl⟩ : syracuseStep 800209 = 600157) B600157
theorem B2831921 : Blo 558808 2831921 := bstep (se 2 (by rfl) ⟨1061970, by rfl⟩ : syracuseStep 2831921 = 2123941) B2123941
theorem B898627 : Blo 558808 898627 := bstep (se 1 (by rfl) ⟨673970, by rfl⟩ : syracuseStep 898627 = 1347941) B1347941
theorem B2700877 : Blo 558808 2700877 := bstep (se 3 (by rfl) ⟨506414, by rfl⟩ : syracuseStep 2700877 = 1012829) B1012829
theorem B1422947 : Blo 558808 1422947 := bstep (se 1 (by rfl) ⟨1067210, by rfl⟩ : syracuseStep 1422947 = 2134421) B2134421
theorem B1259153 : Blo 558808 1259153 := bstep (se 2 (by rfl) ⟨472182, by rfl⟩ : syracuseStep 1259153 = 944365) B944365
theorem B1259171 : Blo 558808 1259171 := bstep (se 1 (by rfl) ⟨944378, by rfl⟩ : syracuseStep 1259171 = 1888757) B1888757
theorem B800545 : Blo 558808 800545 := bstep (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) B600409
theorem B1193795 : Blo 558808 1193795 := bstep (se 1 (by rfl) ⟨895346, by rfl⟩ : syracuseStep 1193795 = 1790693) B1790693
theorem B1259441 : Blo 558808 1259441 := bstep (se 2 (by rfl) ⟨472290, by rfl⟩ : syracuseStep 1259441 = 944581) B944581
theorem B1259459 : Blo 558808 1259459 := bstep (se 1 (by rfl) ⟨944594, by rfl⟩ : syracuseStep 1259459 = 1889189) B1889189
theorem B3881029 : Blo 558808 3881029 := bstep (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) B727693
theorem B1063057 : Blo 558808 1063057 := bstep (se 2 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 1063057 = 797293) B797293
theorem B899267 : Blo 558808 899267 := bstep (se 1 (by rfl) ⟨674450, by rfl⟩ : syracuseStep 899267 = 1348901) B1348901
theorem B1259729 : Blo 558808 1259729 := bstep (se 2 (by rfl) ⟨472398, by rfl⟩ : syracuseStep 1259729 = 944797) B944797
theorem B1259747 : Blo 558808 1259747 := bstep (se 1 (by rfl) ⟨944810, by rfl⟩ : syracuseStep 1259747 = 1889621) B1889621
theorem B1194257 : Blo 558808 1194257 := bstep (se 2 (by rfl) ⟨447846, by rfl⟩ : syracuseStep 1194257 = 895693) B895693
theorem B899345 : Blo 558808 899345 := bstep (se 2 (by rfl) ⟨337254, by rfl⟩ : syracuseStep 899345 = 674509) B674509
theorem B801137 : Blo 558808 801137 := bstep (se 2 (by rfl) ⟨300426, by rfl⟩ : syracuseStep 801137 = 600853) B600853
theorem B1260017 : Blo 558808 1260017 := bstep (se 2 (by rfl) ⟨472506, by rfl⟩ : syracuseStep 1260017 = 945013) B945013
theorem B1260035 : Blo 558808 1260035 := bstep (se 1 (by rfl) ⟨945026, by rfl⟩ : syracuseStep 1260035 = 1890053) B1890053
theorem B1423889 : Blo 558808 1423889 := bstep (se 2 (by rfl) ⟨533958, by rfl⟩ : syracuseStep 1423889 = 1067917) B1067917
theorem B1063459 : Blo 558808 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B1423939 : Blo 558808 1423939 := bstep (se 1 (by rfl) ⟨1067954, by rfl⟩ : syracuseStep 1423939 = 2135909) B2135909
theorem B1063505 : Blo 558808 1063505 := bstep (se 2 (by rfl) ⟨398814, by rfl⟩ : syracuseStep 1063505 = 797629) B797629
theorem B2701937 : Blo 558808 2701937 := bstep (se 2 (by rfl) ⟨1013226, by rfl⟩ : syracuseStep 2701937 = 2026453) B2026453
theorem B3029645 : Blo 558808 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B899729 : Blo 558808 899729 := bstep (se 2 (by rfl) ⟨337398, by rfl⟩ : syracuseStep 899729 = 674797) B674797
theorem B5454533 : Blo 558808 5454533 := bstep (se 4 (by rfl) ⟨511362, by rfl⟩ : syracuseStep 5454533 = 1022725) B1022725
theorem B1424081 : Blo 558808 1424081 := bstep (se 2 (by rfl) ⟨534030, by rfl⟩ : syracuseStep 1424081 = 1068061) B1068061
theorem B3193613 : Blo 558808 3193613 := bstep (se 3 (by rfl) ⟨598802, by rfl⟩ : syracuseStep 3193613 = 1197605) B1197605
theorem B1260305 : Blo 558808 1260305 := bstep (se 2 (by rfl) ⟨472614, by rfl⟩ : syracuseStep 1260305 = 945229) B945229
theorem B899857 : Blo 558808 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B1260323 : Blo 558808 1260323 := bstep (se 1 (by rfl) ⟨945242, by rfl⟩ : syracuseStep 1260323 = 1890485) B1890485
theorem B1063793 : Blo 558808 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B2833379 : Blo 558808 2833379 := bstep (se 1 (by rfl) ⟨2125034, by rfl⟩ : syracuseStep 2833379 = 4250069) B4250069
theorem B2276387 : Blo 558808 2276387 := bstep (se 1 (by rfl) ⟨1707290, by rfl⟩ : syracuseStep 2276387 = 3414581) B3414581
theorem B1260593 : Blo 558808 1260593 := bstep (se 2 (by rfl) ⟨472722, by rfl⟩ : syracuseStep 1260593 = 945445) B945445
theorem B1260611 : Blo 558808 1260611 := bstep (se 1 (by rfl) ⟨945458, by rfl⟩ : syracuseStep 1260611 = 1890917) B1890917
theorem B5749829 : Blo 558808 5749829 := bstep (se 4 (by rfl) ⟨539046, by rfl⟩ : syracuseStep 5749829 = 1078093) B1078093
theorem B1260881 : Blo 558808 1260881 := bstep (se 2 (by rfl) ⟨472830, by rfl⟩ : syracuseStep 1260881 = 945661) B945661
theorem B1260899 : Blo 558808 1260899 := bstep (se 1 (by rfl) ⟨945674, by rfl⟩ : syracuseStep 1260899 = 1891349) B1891349
theorem B2014733 : Blo 558808 2014733 := bstep (se 3 (by rfl) ⟨377762, by rfl⟩ : syracuseStep 2014733 = 755525) B755525
theorem B1195555 : Blo 558808 1195555 := bstep (se 1 (by rfl) ⟨896666, by rfl⟩ : syracuseStep 1195555 = 1793333) B1793333
theorem B6372917 : Blo 558808 6372917 := bstep (se 5 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 6372917 = 597461) B597461
theorem B1064515 : Blo 558808 1064515 := bstep (se 1 (by rfl) ⟨798386, by rfl⟩ : syracuseStep 1064515 = 1596773) B1596773
theorem B1261169 : Blo 558808 1261169 := bstep (se 2 (by rfl) ⟨472938, by rfl⟩ : syracuseStep 1261169 = 945877) B945877
theorem B1261187 : Blo 558808 1261187 := bstep (se 1 (by rfl) ⟨945890, by rfl⟩ : syracuseStep 1261187 = 1891781) B1891781
theorem B2834189 : Blo 558808 2834189 := bstep (se 3 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 2834189 = 1062821) B1062821
theorem B1195811 : Blo 558808 1195811 := bstep (se 1 (by rfl) ⟨896858, by rfl⟩ : syracuseStep 1195811 = 1793717) B1793717
theorem B1261457 : Blo 558808 1261457 := bstep (se 2 (by rfl) ⟨473046, by rfl⟩ : syracuseStep 1261457 = 946093) B946093
theorem B1261475 : Blo 558808 1261475 := bstep (se 1 (by rfl) ⟨946106, by rfl⟩ : syracuseStep 1261475 = 1892213) B1892213
theorem B1064963 : Blo 558808 1064963 := bstep (se 1 (by rfl) ⟨798722, by rfl⟩ : syracuseStep 1064963 = 1597445) B1597445
theorem B1917101 : Blo 558808 1917101 := bstep (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) B718913
theorem B1261745 : Blo 558808 1261745 := bstep (se 2 (by rfl) ⟨473154, by rfl⟩ : syracuseStep 1261745 = 946309) B946309
theorem B1261763 : Blo 558808 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B3653837 : Blo 558808 3653837 := bstep (se 3 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 3653837 = 1370189) B1370189
theorem B901363 : Blo 558808 901363 := bstep (se 1 (by rfl) ⟨676022, by rfl⟩ : syracuseStep 901363 = 1352045) B1352045
theorem B1065251 : Blo 558808 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B672067 : Blo 558808 672067 := bstep (se 1 (by rfl) ⟨504050, by rfl⟩ : syracuseStep 672067 = 1008101) B1008101
theorem B4309361 : Blo 558808 4309361 := bstep (se 2 (by rfl) ⟨1616010, by rfl⟩ : syracuseStep 4309361 = 3232021) B3232021
theorem B1262033 : Blo 558808 1262033 := bstep (se 2 (by rfl) ⟨473262, by rfl⟩ : syracuseStep 1262033 = 946525) B946525
theorem B1262051 : Blo 558808 1262051 := bstep (se 1 (by rfl) ⟨946538, by rfl⟩ : syracuseStep 1262051 = 1893077) B1893077
theorem B1196785 : Blo 558808 1196785 := bstep (se 2 (by rfl) ⟨448794, by rfl⟩ : syracuseStep 1196785 = 897589) B897589
theorem B1262321 : Blo 558808 1262321 := bstep (se 2 (by rfl) ⟨473370, by rfl⟩ : syracuseStep 1262321 = 946741) B946741
theorem B1262339 : Blo 558808 1262339 := bstep (se 1 (by rfl) ⟨946754, by rfl⟩ : syracuseStep 1262339 = 1893509) B1893509
theorem B4244237 : Blo 558808 4244237 := bstep (se 3 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 4244237 = 1591589) B1591589
theorem B3195845 : Blo 558808 3195845 := bstep (se 4 (by rfl) ⟨299610, by rfl⟩ : syracuseStep 3195845 = 599221) B599221
theorem B4047857 : Blo 558808 4047857 := bstep (se 2 (by rfl) ⟨1517946, by rfl⟩ : syracuseStep 4047857 = 3035893) B3035893
theorem B1262609 : Blo 558808 1262609 := bstep (se 2 (by rfl) ⟨473478, by rfl⟩ : syracuseStep 1262609 = 946957) B946957
theorem B1262627 : Blo 558808 1262627 := bstep (se 1 (by rfl) ⟨946970, by rfl⟩ : syracuseStep 1262627 = 1893941) B1893941
theorem B1066193 : Blo 558808 1066193 := bstep (se 2 (by rfl) ⟨399822, by rfl⟩ : syracuseStep 1066193 = 799645) B799645
theorem B1262897 : Blo 558808 1262897 := bstep (se 2 (by rfl) ⟨473586, by rfl⟩ : syracuseStep 1262897 = 947173) B947173
theorem B1951025 : Blo 558808 1951025 := bstep (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) B1463269
theorem B1262915 : Blo 558808 1262915 := bstep (se 1 (by rfl) ⟨947186, by rfl⟩ : syracuseStep 1262915 = 1894373) B1894373
theorem B1197443 : Blo 558808 1197443 := bstep (se 1 (by rfl) ⟨898082, by rfl⟩ : syracuseStep 1197443 = 1796165) B1796165
theorem B1263185 : Blo 558808 1263185 := bstep (se 2 (by rfl) ⟨473694, by rfl⟩ : syracuseStep 1263185 = 947389) B947389
theorem B1263203 : Blo 558808 1263203 := bstep (se 1 (by rfl) ⟨947402, by rfl⟩ : syracuseStep 1263203 = 1894805) B1894805
theorem B3196529 : Blo 558808 3196529 := bstep (se 2 (by rfl) ⟨1198698, by rfl⟩ : syracuseStep 3196529 = 2397397) B2397397
theorem B1918691 : Blo 558808 1918691 := bstep (se 1 (by rfl) ⟨1439018, by rfl⟩ : syracuseStep 1918691 = 2878037) B2878037
theorem B1263473 : Blo 558808 1263473 := bstep (se 2 (by rfl) ⟨473802, by rfl⟩ : syracuseStep 1263473 = 947605) B947605
theorem B1263491 : Blo 558808 1263491 := bstep (se 1 (by rfl) ⟨947618, by rfl⟩ : syracuseStep 1263491 = 1895237) B1895237
theorem B1067089 : Blo 558808 1067089 := bstep (se 2 (by rfl) ⟨400158, by rfl⟩ : syracuseStep 1067089 = 800317) B800317
theorem B1263761 : Blo 558808 1263761 := bstep (se 2 (by rfl) ⟨473910, by rfl⟩ : syracuseStep 1263761 = 947821) B947821
theorem B1263779 : Blo 558808 1263779 := bstep (se 1 (by rfl) ⟨947834, by rfl⟩ : syracuseStep 1263779 = 1895669) B1895669
theorem B1886381 : Blo 558808 1886381 := bstep (se 3 (by rfl) ⟨353696, by rfl⟩ : syracuseStep 1886381 = 707393) B707393
theorem B2017457 : Blo 558808 2017457 := bstep (se 2 (by rfl) ⟨756546, by rfl⟩ : syracuseStep 2017457 = 1513093) B1513093
theorem B1198289 : Blo 558808 1198289 := bstep (se 2 (by rfl) ⟨449358, by rfl⟩ : syracuseStep 1198289 = 898717) B898717
theorem B1886435 : Blo 558808 1886435 := bstep (se 1 (by rfl) ⟨1414826, by rfl⟩ : syracuseStep 1886435 = 2829653) B2829653
theorem B1067249 : Blo 558808 1067249 := bstep (se 2 (by rfl) ⟨400218, by rfl⟩ : syracuseStep 1067249 = 800437) B800437
theorem B2017585 : Blo 558808 2017585 := bstep (se 2 (by rfl) ⟨756594, by rfl⟩ : syracuseStep 2017585 = 1513189) B1513189
theorem B1264049 : Blo 558808 1264049 := bstep (se 2 (by rfl) ⟨474018, by rfl⟩ : syracuseStep 1264049 = 948037) B948037
theorem B1264067 : Blo 558808 1264067 := bstep (se 1 (by rfl) ⟨948050, by rfl⟩ : syracuseStep 1264067 = 1896101) B1896101
theorem B1886705 : Blo 558808 1886705 := bstep (se 2 (by rfl) ⟨707514, by rfl⟩ : syracuseStep 1886705 = 1415029) B1415029
theorem B838241 : Blo 558808 838241 := bstep (se 2 (by rfl) ⟨314340, by rfl⟩ : syracuseStep 838241 = 628681) B628681
theorem B2837105 : Blo 558808 2837105 := bstep (se 2 (by rfl) ⟨1063914, by rfl⟩ : syracuseStep 2837105 = 2127829) B2127829
theorem B838259 : Blo 558808 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B1067651 : Blo 558808 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B838289 : Blo 558808 838289 := bstep (se 2 (by rfl) ⟨314358, by rfl⟩ : syracuseStep 838289 = 628717) B628717
theorem B838307 : Blo 558808 838307 := bstep (se 1 (by rfl) ⟨628730, by rfl⟩ : syracuseStep 838307 = 1257461) B1257461
theorem B1821361 : Blo 558808 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B838337 : Blo 558808 838337 := bstep (se 2 (by rfl) ⟨314376, by rfl⟩ : syracuseStep 838337 = 628753) B628753
theorem B1264337 : Blo 558808 1264337 := bstep (se 2 (by rfl) ⟨474126, by rfl⟩ : syracuseStep 1264337 = 948253) B948253
theorem B838355 : Blo 558808 838355 := bstep (se 1 (by rfl) ⟨628766, by rfl⟩ : syracuseStep 838355 = 1257533) B1257533
theorem B1264355 : Blo 558808 1264355 := bstep (se 1 (by rfl) ⟨948266, by rfl⟩ : syracuseStep 1264355 = 1896533) B1896533
theorem B1592045 : Blo 558808 1592045 := bstep (se 3 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 1592045 = 597017) B597017
theorem B838385 : Blo 558808 838385 := bstep (se 2 (by rfl) ⟨314394, by rfl⟩ : syracuseStep 838385 = 628789) B628789
theorem B838403 : Blo 558808 838403 := bstep (se 1 (by rfl) ⟨628802, by rfl⟩ : syracuseStep 838403 = 1257605) B1257605
theorem B838433 : Blo 558808 838433 := bstep (se 2 (by rfl) ⟨314412, by rfl⟩ : syracuseStep 838433 = 628825) B628825
theorem B838451 : Blo 558808 838451 := bstep (se 1 (by rfl) ⟨628838, by rfl⟩ : syracuseStep 838451 = 1257677) B1257677
theorem B838481 : Blo 558808 838481 := bstep (se 2 (by rfl) ⟨314430, by rfl⟩ : syracuseStep 838481 = 628861) B628861
theorem B838499 : Blo 558808 838499 := bstep (se 1 (by rfl) ⟨628874, by rfl⟩ : syracuseStep 838499 = 1257749) B1257749
theorem B838529 : Blo 558808 838529 := bstep (se 2 (by rfl) ⟨314448, by rfl⟩ : syracuseStep 838529 = 628897) B628897
theorem B838547 : Blo 558808 838547 := bstep (se 1 (by rfl) ⟨628910, by rfl⟩ : syracuseStep 838547 = 1257821) B1257821
theorem B1592227 : Blo 558808 1592227 := bstep (se 1 (by rfl) ⟨1194170, by rfl⟩ : syracuseStep 1592227 = 2388341) B2388341
theorem B838577 : Blo 558808 838577 := bstep (se 2 (by rfl) ⟨314466, by rfl⟩ : syracuseStep 838577 = 628933) B628933
theorem B838595 : Blo 558808 838595 := bstep (se 1 (by rfl) ⟨628946, by rfl⟩ : syracuseStep 838595 = 1257893) B1257893
theorem B1592273 : Blo 558808 1592273 := bstep (se 2 (by rfl) ⟨597102, by rfl⟩ : syracuseStep 1592273 = 1194205) B1194205
theorem B838625 : Blo 558808 838625 := bstep (se 2 (by rfl) ⟨314484, by rfl⟩ : syracuseStep 838625 = 628969) B628969
theorem B707555 : Blo 558808 707555 := bstep (se 1 (by rfl) ⟨530666, by rfl⟩ : syracuseStep 707555 = 1061333) B1061333
theorem B1264625 : Blo 558808 1264625 := bstep (se 2 (by rfl) ⟨474234, by rfl⟩ : syracuseStep 1264625 = 948469) B948469
theorem B838643 : Blo 558808 838643 := bstep (se 1 (by rfl) ⟨628982, by rfl⟩ : syracuseStep 838643 = 1257965) B1257965
theorem B1264643 : Blo 558808 1264643 := bstep (se 1 (by rfl) ⟨948482, by rfl⟩ : syracuseStep 1264643 = 1896965) B1896965
theorem B1887245 : Blo 558808 1887245 := bstep (se 3 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 1887245 = 707717) B707717
theorem B838673 : Blo 558808 838673 := bstep (se 2 (by rfl) ⟨314502, by rfl⟩ : syracuseStep 838673 = 629005) B629005
theorem B838691 : Blo 558808 838691 := bstep (se 1 (by rfl) ⟨629018, by rfl⟩ : syracuseStep 838691 = 1258037) B1258037
theorem B3197987 : Blo 558808 3197987 := bstep (se 1 (by rfl) ⟨2398490, by rfl⟩ : syracuseStep 3197987 = 4796981) B4796981
theorem B838721 : Blo 558808 838721 := bstep (se 2 (by rfl) ⟨314520, by rfl⟩ : syracuseStep 838721 = 629041) B629041
theorem B1887299 : Blo 558808 1887299 := bstep (se 1 (by rfl) ⟨1415474, by rfl⟩ : syracuseStep 1887299 = 2830949) B2830949
theorem B838739 : Blo 558808 838739 := bstep (se 1 (by rfl) ⟨629054, by rfl⟩ : syracuseStep 838739 = 1258109) B1258109
theorem B838769 : Blo 558808 838769 := bstep (se 2 (by rfl) ⟨314538, by rfl⟩ : syracuseStep 838769 = 629077) B629077
theorem B838787 : Blo 558808 838787 := bstep (se 1 (by rfl) ⟨629090, by rfl⟩ : syracuseStep 838787 = 1258181) B1258181
theorem B838817 : Blo 558808 838817 := bstep (se 2 (by rfl) ⟨314556, by rfl⟩ : syracuseStep 838817 = 629113) B629113
theorem B838835 : Blo 558808 838835 := bstep (se 1 (by rfl) ⟨629126, by rfl⟩ : syracuseStep 838835 = 1258253) B1258253
theorem B838865 : Blo 558808 838865 := bstep (se 2 (by rfl) ⟨314574, by rfl⟩ : syracuseStep 838865 = 629149) B629149
theorem B838883 : Blo 558808 838883 := bstep (se 1 (by rfl) ⟨629162, by rfl⟩ : syracuseStep 838883 = 1258325) B1258325
theorem B838913 : Blo 558808 838913 := bstep (se 2 (by rfl) ⟨314592, by rfl⟩ : syracuseStep 838913 = 629185) B629185
theorem B1264913 : Blo 558808 1264913 := bstep (se 2 (by rfl) ⟨474342, by rfl⟩ : syracuseStep 1264913 = 948685) B948685
theorem B838931 : Blo 558808 838931 := bstep (se 1 (by rfl) ⟨629198, by rfl⟩ : syracuseStep 838931 = 1258397) B1258397
theorem B1264931 : Blo 558808 1264931 := bstep (se 1 (by rfl) ⟨948698, by rfl⟩ : syracuseStep 1264931 = 1897397) B1897397
theorem B838961 : Blo 558808 838961 := bstep (se 2 (by rfl) ⟨314610, by rfl⟩ : syracuseStep 838961 = 629221) B629221
theorem B838979 : Blo 558808 838979 := bstep (se 1 (by rfl) ⟨629234, by rfl⟩ : syracuseStep 838979 = 1258469) B1258469
theorem B1887569 : Blo 558808 1887569 := bstep (se 2 (by rfl) ⟨707838, by rfl⟩ : syracuseStep 1887569 = 1415677) B1415677
theorem B839009 : Blo 558808 839009 := bstep (se 2 (by rfl) ⟨314628, by rfl⟩ : syracuseStep 839009 = 629257) B629257
theorem B839027 : Blo 558808 839027 := bstep (se 1 (by rfl) ⟨629270, by rfl⟩ : syracuseStep 839027 = 1258541) B1258541
theorem B2280845 : Blo 558808 2280845 := bstep (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) B855317
theorem B839057 : Blo 558808 839057 := bstep (se 2 (by rfl) ⟨314646, by rfl⟩ : syracuseStep 839057 = 629293) B629293
theorem B839075 : Blo 558808 839075 := bstep (se 1 (by rfl) ⟨629306, by rfl⟩ : syracuseStep 839075 = 1258613) B1258613
theorem B839105 : Blo 558808 839105 := bstep (se 2 (by rfl) ⟨314664, by rfl⟩ : syracuseStep 839105 = 629329) B629329
theorem B839123 : Blo 558808 839123 := bstep (se 1 (by rfl) ⟨629342, by rfl⟩ : syracuseStep 839123 = 1258685) B1258685
theorem B839153 : Blo 558808 839153 := bstep (se 2 (by rfl) ⟨314682, by rfl⟩ : syracuseStep 839153 = 629365) B629365
theorem B839171 : Blo 558808 839171 := bstep (se 1 (by rfl) ⟨629378, by rfl⟩ : syracuseStep 839171 = 1258757) B1258757
theorem B839201 : Blo 558808 839201 := bstep (se 2 (by rfl) ⟨314700, by rfl⟩ : syracuseStep 839201 = 629401) B629401
theorem B1265201 : Blo 558808 1265201 := bstep (se 2 (by rfl) ⟨474450, by rfl⟩ : syracuseStep 1265201 = 948901) B948901
theorem B839219 : Blo 558808 839219 := bstep (se 1 (by rfl) ⟨629414, by rfl⟩ : syracuseStep 839219 = 1258829) B1258829
theorem B1265219 : Blo 558808 1265219 := bstep (se 1 (by rfl) ⟨948914, by rfl⟩ : syracuseStep 1265219 = 1897829) B1897829
theorem B839249 : Blo 558808 839249 := bstep (se 2 (by rfl) ⟨314718, by rfl⟩ : syracuseStep 839249 = 629437) B629437
theorem B1920593 : Blo 558808 1920593 := bstep (se 2 (by rfl) ⟨720222, by rfl⟩ : syracuseStep 1920593 = 1440445) B1440445
theorem B839267 : Blo 558808 839267 := bstep (se 1 (by rfl) ⟨629450, by rfl⟩ : syracuseStep 839267 = 1258901) B1258901
theorem B4247153 : Blo 558808 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B839297 : Blo 558808 839297 := bstep (se 2 (by rfl) ⟨314736, by rfl⟩ : syracuseStep 839297 = 629473) B629473
theorem B839315 : Blo 558808 839315 := bstep (se 1 (by rfl) ⟨629486, by rfl⟩ : syracuseStep 839315 = 1258973) B1258973
theorem B708259 : Blo 558808 708259 := bstep (se 1 (by rfl) ⟨531194, by rfl⟩ : syracuseStep 708259 = 1062389) B1062389
theorem B839345 : Blo 558808 839345 := bstep (se 2 (by rfl) ⟨314754, by rfl⟩ : syracuseStep 839345 = 629509) B629509
theorem B839363 : Blo 558808 839363 := bstep (se 1 (by rfl) ⟨629522, by rfl⟩ : syracuseStep 839363 = 1259045) B1259045
theorem B839393 : Blo 558808 839393 := bstep (se 2 (by rfl) ⟨314772, by rfl⟩ : syracuseStep 839393 = 629545) B629545
theorem B839411 : Blo 558808 839411 := bstep (se 1 (by rfl) ⟨629558, by rfl⟩ : syracuseStep 839411 = 1259117) B1259117
theorem B708355 : Blo 558808 708355 := bstep (se 1 (by rfl) ⟨531266, by rfl⟩ : syracuseStep 708355 = 1062533) B1062533
theorem B839441 : Blo 558808 839441 := bstep (se 2 (by rfl) ⟨314790, by rfl⟩ : syracuseStep 839441 = 629581) B629581
theorem B839459 : Blo 558808 839459 := bstep (se 1 (by rfl) ⟨629594, by rfl⟩ : syracuseStep 839459 = 1259189) B1259189
theorem B839489 : Blo 558808 839489 := bstep (se 2 (by rfl) ⟨314808, by rfl⟩ : syracuseStep 839489 = 629617) B629617
theorem B1265489 : Blo 558808 1265489 := bstep (se 2 (by rfl) ⟨474558, by rfl⟩ : syracuseStep 1265489 = 949117) B949117
theorem B839507 : Blo 558808 839507 := bstep (se 1 (by rfl) ⟨629630, by rfl⟩ : syracuseStep 839507 = 1259261) B1259261
theorem B1265507 : Blo 558808 1265507 := bstep (se 1 (by rfl) ⟨949130, by rfl⟩ : syracuseStep 1265507 = 1898261) B1898261
theorem B1888109 : Blo 558808 1888109 := bstep (se 3 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 1888109 = 708041) B708041
theorem B839537 : Blo 558808 839537 := bstep (se 2 (by rfl) ⟨314826, by rfl⟩ : syracuseStep 839537 = 629653) B629653
theorem B839555 : Blo 558808 839555 := bstep (se 1 (by rfl) ⟨629666, by rfl⟩ : syracuseStep 839555 = 1259333) B1259333
theorem B839585 : Blo 558808 839585 := bstep (se 2 (by rfl) ⟨314844, by rfl⟩ : syracuseStep 839585 = 629689) B629689
theorem B1888163 : Blo 558808 1888163 := bstep (se 1 (by rfl) ⟨1416122, by rfl⟩ : syracuseStep 1888163 = 2832245) B2832245
theorem B839603 : Blo 558808 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B7196597 : Blo 558808 7196597 := bstep (se 5 (by rfl) ⟨337340, by rfl⟩ : syracuseStep 7196597 = 674681) B674681
theorem B839633 : Blo 558808 839633 := bstep (se 2 (by rfl) ⟨314862, by rfl⟩ : syracuseStep 839633 = 629725) B629725
theorem B839651 : Blo 558808 839651 := bstep (se 1 (by rfl) ⟨629738, by rfl⟩ : syracuseStep 839651 = 1259477) B1259477
theorem B839681 : Blo 558808 839681 := bstep (se 2 (by rfl) ⟨314880, by rfl⟩ : syracuseStep 839681 = 629761) B629761
theorem B839699 : Blo 558808 839699 := bstep (se 1 (by rfl) ⟨629774, by rfl⟩ : syracuseStep 839699 = 1259549) B1259549
theorem B2838563 : Blo 558808 2838563 := bstep (se 1 (by rfl) ⟨2128922, by rfl⟩ : syracuseStep 2838563 = 4257845) B4257845
theorem B839729 : Blo 558808 839729 := bstep (se 2 (by rfl) ⟨314898, by rfl⟩ : syracuseStep 839729 = 629797) B629797
theorem B839747 : Blo 558808 839747 := bstep (se 1 (by rfl) ⟨629810, by rfl⟩ : syracuseStep 839747 = 1259621) B1259621
theorem B839777 : Blo 558808 839777 := bstep (se 2 (by rfl) ⟨314916, by rfl⟩ : syracuseStep 839777 = 629833) B629833
theorem B1265777 : Blo 558808 1265777 := bstep (se 2 (by rfl) ⟨474666, by rfl⟩ : syracuseStep 1265777 = 949333) B949333
theorem B839795 : Blo 558808 839795 := bstep (se 1 (by rfl) ⟨629846, by rfl⟩ : syracuseStep 839795 = 1259693) B1259693
theorem B1265795 : Blo 558808 1265795 := bstep (se 1 (by rfl) ⟨949346, by rfl⟩ : syracuseStep 1265795 = 1898693) B1898693
theorem B839825 : Blo 558808 839825 := bstep (se 2 (by rfl) ⟨314934, by rfl⟩ : syracuseStep 839825 = 629869) B629869
theorem B839843 : Blo 558808 839843 := bstep (se 1 (by rfl) ⟨629882, by rfl⟩ : syracuseStep 839843 = 1259765) B1259765
theorem B2019491 : Blo 558808 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B1888433 : Blo 558808 1888433 := bstep (se 2 (by rfl) ⟨708162, by rfl⟩ : syracuseStep 1888433 = 1416325) B1416325
theorem B839873 : Blo 558808 839873 := bstep (se 2 (by rfl) ⟨314952, by rfl⟩ : syracuseStep 839873 = 629905) B629905
theorem B839891 : Blo 558808 839891 := bstep (se 1 (by rfl) ⟨629918, by rfl⟩ : syracuseStep 839891 = 1259837) B1259837
theorem B24170723 : Blo 558808 24170723 := bstep (se 1 (by rfl) ⟨18128042, by rfl⟩ : syracuseStep 24170723 = 36256085) B36256085
theorem B839921 : Blo 558808 839921 := bstep (se 2 (by rfl) ⟨314970, by rfl⟩ : syracuseStep 839921 = 629941) B629941
theorem B708851 : Blo 558808 708851 := bstep (se 1 (by rfl) ⟨531638, by rfl⟩ : syracuseStep 708851 = 1063277) B1063277
theorem B839939 : Blo 558808 839939 := bstep (se 1 (by rfl) ⟨629954, by rfl⟩ : syracuseStep 839939 = 1259909) B1259909
theorem B4313357 : Blo 558808 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B839969 : Blo 558808 839969 := bstep (se 2 (by rfl) ⟨314988, by rfl⟩ : syracuseStep 839969 = 629977) B629977
theorem B1790257 : Blo 558808 1790257 := bstep (se 2 (by rfl) ⟨671346, by rfl⟩ : syracuseStep 1790257 = 1342693) B1342693
theorem B839987 : Blo 558808 839987 := bstep (se 1 (by rfl) ⟨629990, by rfl⟩ : syracuseStep 839987 = 1259981) B1259981
theorem B3461453 : Blo 558808 3461453 := bstep (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) B1298045
theorem B840017 : Blo 558808 840017 := bstep (se 2 (by rfl) ⟨315006, by rfl⟩ : syracuseStep 840017 = 630013) B630013
theorem B840035 : Blo 558808 840035 := bstep (se 1 (by rfl) ⟨630026, by rfl⟩ : syracuseStep 840035 = 1260053) B1260053
theorem B840065 : Blo 558808 840065 := bstep (se 2 (by rfl) ⟨315024, by rfl⟩ : syracuseStep 840065 = 630049) B630049
theorem B1593731 : Blo 558808 1593731 := bstep (se 1 (by rfl) ⟨1195298, by rfl⟩ : syracuseStep 1593731 = 2390597) B2390597
theorem B1266065 : Blo 558808 1266065 := bstep (se 2 (by rfl) ⟨474774, by rfl⟩ : syracuseStep 1266065 = 949549) B949549
theorem B840083 : Blo 558808 840083 := bstep (se 1 (by rfl) ⟨630062, by rfl⟩ : syracuseStep 840083 = 1260125) B1260125
theorem B1266083 : Blo 558808 1266083 := bstep (se 1 (by rfl) ⟨949562, by rfl⟩ : syracuseStep 1266083 = 1899125) B1899125
theorem B840113 : Blo 558808 840113 := bstep (se 2 (by rfl) ⟨315042, by rfl⟩ : syracuseStep 840113 = 630085) B630085
theorem B840131 : Blo 558808 840131 := bstep (se 1 (by rfl) ⟨630098, by rfl⟩ : syracuseStep 840131 = 1260197) B1260197
theorem B840161 : Blo 558808 840161 := bstep (se 2 (by rfl) ⟨315060, by rfl⟩ : syracuseStep 840161 = 630121) B630121
theorem B840179 : Blo 558808 840179 := bstep (se 1 (by rfl) ⟨630134, by rfl⟩ : syracuseStep 840179 = 1260269) B1260269
theorem B840209 : Blo 558808 840209 := bstep (se 2 (by rfl) ⟨315078, by rfl⟩ : syracuseStep 840209 = 630157) B630157
theorem B840227 : Blo 558808 840227 := bstep (se 1 (by rfl) ⟨630170, by rfl⟩ : syracuseStep 840227 = 1260341) B1260341
theorem B840257 : Blo 558808 840257 := bstep (se 2 (by rfl) ⟨315096, by rfl⟩ : syracuseStep 840257 = 630193) B630193
theorem B840275 : Blo 558808 840275 := bstep (se 1 (by rfl) ⟨630206, by rfl⟩ : syracuseStep 840275 = 1260413) B1260413
theorem B840305 : Blo 558808 840305 := bstep (se 2 (by rfl) ⟨315114, by rfl⟩ : syracuseStep 840305 = 630229) B630229
theorem B840323 : Blo 558808 840323 := bstep (se 1 (by rfl) ⟨630242, by rfl⟩ : syracuseStep 840323 = 1260485) B1260485
theorem B840353 : Blo 558808 840353 := bstep (se 2 (by rfl) ⟨315132, by rfl⟩ : syracuseStep 840353 = 630265) B630265
theorem B840371 : Blo 558808 840371 := bstep (se 1 (by rfl) ⟨630278, by rfl⟩ : syracuseStep 840371 = 1260557) B1260557
theorem B1888973 : Blo 558808 1888973 := bstep (se 3 (by rfl) ⟨354182, by rfl⟩ : syracuseStep 1888973 = 708365) B708365
theorem B840401 : Blo 558808 840401 := bstep (se 2 (by rfl) ⟨315150, by rfl⟩ : syracuseStep 840401 = 630301) B630301
theorem B840419 : Blo 558808 840419 := bstep (se 1 (by rfl) ⟨630314, by rfl⟩ : syracuseStep 840419 = 1260629) B1260629
theorem B840449 : Blo 558808 840449 := bstep (se 2 (by rfl) ⟨315168, by rfl⟩ : syracuseStep 840449 = 630337) B630337
theorem B1889027 : Blo 558808 1889027 := bstep (se 1 (by rfl) ⟨1416770, by rfl⟩ : syracuseStep 1889027 = 2833541) B2833541
theorem B840467 : Blo 558808 840467 := bstep (se 1 (by rfl) ⟨630350, by rfl⟩ : syracuseStep 840467 = 1260701) B1260701
theorem B840497 : Blo 558808 840497 := bstep (se 2 (by rfl) ⟨315186, by rfl⟩ : syracuseStep 840497 = 630373) B630373
theorem B840515 : Blo 558808 840515 := bstep (se 1 (by rfl) ⟨630386, by rfl⟩ : syracuseStep 840515 = 1260773) B1260773
theorem B2839373 : Blo 558808 2839373 := bstep (se 3 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 2839373 = 1064765) B1064765
theorem B840545 : Blo 558808 840545 := bstep (se 2 (by rfl) ⟨315204, by rfl⟩ : syracuseStep 840545 = 630409) B630409
theorem B840563 : Blo 558808 840563 := bstep (se 1 (by rfl) ⟨630422, by rfl⟩ : syracuseStep 840563 = 1260845) B1260845
theorem B840593 : Blo 558808 840593 := bstep (se 2 (by rfl) ⟨315222, by rfl⟩ : syracuseStep 840593 = 630445) B630445
theorem B840611 : Blo 558808 840611 := bstep (se 1 (by rfl) ⟨630458, by rfl⟩ : syracuseStep 840611 = 1260917) B1260917
theorem B1201073 : Blo 558808 1201073 := bstep (se 2 (by rfl) ⟨450402, by rfl⟩ : syracuseStep 1201073 = 900805) B900805
theorem B709555 : Blo 558808 709555 := bstep (se 1 (by rfl) ⟨532166, by rfl⟩ : syracuseStep 709555 = 1064333) B1064333
theorem B840641 : Blo 558808 840641 := bstep (se 2 (by rfl) ⟨315240, by rfl⟩ : syracuseStep 840641 = 630481) B630481
theorem B840659 : Blo 558808 840659 := bstep (se 1 (by rfl) ⟨630494, by rfl⟩ : syracuseStep 840659 = 1260989) B1260989
theorem B840689 : Blo 558808 840689 := bstep (se 2 (by rfl) ⟨315258, by rfl⟩ : syracuseStep 840689 = 630517) B630517
theorem B840707 : Blo 558808 840707 := bstep (se 1 (by rfl) ⟨630530, by rfl⟩ : syracuseStep 840707 = 1261061) B1261061
theorem B1889297 : Blo 558808 1889297 := bstep (se 2 (by rfl) ⟨708486, by rfl⟩ : syracuseStep 1889297 = 1416973) B1416973
theorem B709651 : Blo 558808 709651 := bstep (se 1 (by rfl) ⟨532238, by rfl⟩ : syracuseStep 709651 = 1064477) B1064477
theorem B840737 : Blo 558808 840737 := bstep (se 2 (by rfl) ⟨315276, by rfl⟩ : syracuseStep 840737 = 630553) B630553
theorem B840755 : Blo 558808 840755 := bstep (se 1 (by rfl) ⟨630566, by rfl⟩ : syracuseStep 840755 = 1261133) B1261133
theorem B840785 : Blo 558808 840785 := bstep (se 2 (by rfl) ⟨315294, by rfl⟩ : syracuseStep 840785 = 630589) B630589
theorem B840803 : Blo 558808 840803 := bstep (se 1 (by rfl) ⟨630602, by rfl⟩ : syracuseStep 840803 = 1261205) B1261205
theorem B840833 : Blo 558808 840833 := bstep (se 2 (by rfl) ⟨315312, by rfl⟩ : syracuseStep 840833 = 630625) B630625
theorem B840851 : Blo 558808 840851 := bstep (se 1 (by rfl) ⟨630638, by rfl⟩ : syracuseStep 840851 = 1261277) B1261277
theorem B840881 : Blo 558808 840881 := bstep (se 2 (by rfl) ⟨315330, by rfl⟩ : syracuseStep 840881 = 630661) B630661
theorem B840899 : Blo 558808 840899 := bstep (se 1 (by rfl) ⟨630674, by rfl⟩ : syracuseStep 840899 = 1261349) B1261349
theorem B9557189 : Blo 558808 9557189 := bstep (se 4 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 9557189 = 1791973) B1791973
theorem B840929 : Blo 558808 840929 := bstep (se 2 (by rfl) ⟨315348, by rfl⟩ : syracuseStep 840929 = 630697) B630697
theorem B840947 : Blo 558808 840947 := bstep (se 1 (by rfl) ⟨630710, by rfl⟩ : syracuseStep 840947 = 1261421) B1261421
theorem B840977 : Blo 558808 840977 := bstep (se 2 (by rfl) ⟨315366, by rfl⟩ : syracuseStep 840977 = 630733) B630733
theorem B840995 : Blo 558808 840995 := bstep (se 1 (by rfl) ⟨630746, by rfl⟩ : syracuseStep 840995 = 1261493) B1261493
theorem B841025 : Blo 558808 841025 := bstep (se 2 (by rfl) ⟨315384, by rfl⟩ : syracuseStep 841025 = 630769) B630769
theorem B841043 : Blo 558808 841043 := bstep (se 1 (by rfl) ⟨630782, by rfl⟩ : syracuseStep 841043 = 1261565) B1261565
theorem B841073 : Blo 558808 841073 := bstep (se 2 (by rfl) ⟨315402, by rfl⟩ : syracuseStep 841073 = 630805) B630805
theorem B841091 : Blo 558808 841091 := bstep (se 1 (by rfl) ⟨630818, by rfl⟩ : syracuseStep 841091 = 1261637) B1261637
theorem B841121 : Blo 558808 841121 := bstep (se 2 (by rfl) ⟨315420, by rfl⟩ : syracuseStep 841121 = 630841) B630841
theorem B841139 : Blo 558808 841139 := bstep (se 1 (by rfl) ⟨630854, by rfl⟩ : syracuseStep 841139 = 1261709) B1261709
theorem B808385 : Blo 558808 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B841169 : Blo 558808 841169 := bstep (se 2 (by rfl) ⟨315438, by rfl⟩ : syracuseStep 841169 = 630877) B630877
theorem B841187 : Blo 558808 841187 := bstep (se 1 (by rfl) ⟨630890, by rfl⟩ : syracuseStep 841187 = 1261781) B1261781
theorem B841217 : Blo 558808 841217 := bstep (se 2 (by rfl) ⟨315456, by rfl⟩ : syracuseStep 841217 = 630913) B630913
theorem B710147 : Blo 558808 710147 := bstep (se 1 (by rfl) ⟨532610, by rfl⟩ : syracuseStep 710147 = 1065221) B1065221
theorem B841235 : Blo 558808 841235 := bstep (se 1 (by rfl) ⟨630926, by rfl⟩ : syracuseStep 841235 = 1261853) B1261853
theorem B1889837 : Blo 558808 1889837 := bstep (se 3 (by rfl) ⟨354344, by rfl⟩ : syracuseStep 1889837 = 708689) B708689
theorem B841265 : Blo 558808 841265 := bstep (se 2 (by rfl) ⟨315474, by rfl⟩ : syracuseStep 841265 = 630949) B630949
theorem B841283 : Blo 558808 841283 := bstep (se 1 (by rfl) ⟨630962, by rfl⟩ : syracuseStep 841283 = 1261925) B1261925
theorem B1594961 : Blo 558808 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B841313 : Blo 558808 841313 := bstep (se 2 (by rfl) ⟨315492, by rfl⟩ : syracuseStep 841313 = 630985) B630985
theorem B1889891 : Blo 558808 1889891 := bstep (se 1 (by rfl) ⟨1417418, by rfl⟩ : syracuseStep 1889891 = 2834837) B2834837
theorem B841331 : Blo 558808 841331 := bstep (se 1 (by rfl) ⟨630998, by rfl⟩ : syracuseStep 841331 = 1261997) B1261997
theorem B841361 : Blo 558808 841361 := bstep (se 2 (by rfl) ⟨315510, by rfl⟩ : syracuseStep 841361 = 631021) B631021
theorem B841379 : Blo 558808 841379 := bstep (se 1 (by rfl) ⟨631034, by rfl⟩ : syracuseStep 841379 = 1262069) B1262069
theorem B841409 : Blo 558808 841409 := bstep (se 2 (by rfl) ⟨315528, by rfl⟩ : syracuseStep 841409 = 631057) B631057
theorem B841427 : Blo 558808 841427 := bstep (se 1 (by rfl) ⟨631070, by rfl⟩ : syracuseStep 841427 = 1262141) B1262141
theorem B841457 : Blo 558808 841457 := bstep (se 2 (by rfl) ⟨315546, by rfl⟩ : syracuseStep 841457 = 631093) B631093
theorem B841475 : Blo 558808 841475 := bstep (se 1 (by rfl) ⟨631106, by rfl⟩ : syracuseStep 841475 = 1262213) B1262213
theorem B841505 : Blo 558808 841505 := bstep (se 2 (by rfl) ⟨315564, by rfl⟩ : syracuseStep 841505 = 631129) B631129
theorem B841523 : Blo 558808 841523 := bstep (se 1 (by rfl) ⟨631142, by rfl⟩ : syracuseStep 841523 = 1262285) B1262285
theorem B1791821 : Blo 558808 1791821 := bstep (se 3 (by rfl) ⟨335966, by rfl⟩ : syracuseStep 1791821 = 671933) B671933
theorem B841553 : Blo 558808 841553 := bstep (se 2 (by rfl) ⟨315582, by rfl⟩ : syracuseStep 841553 = 631165) B631165
theorem B841571 : Blo 558808 841571 := bstep (se 1 (by rfl) ⟨631178, by rfl⟩ : syracuseStep 841571 = 1262357) B1262357
theorem B1890161 : Blo 558808 1890161 := bstep (se 2 (by rfl) ⟨708810, by rfl⟩ : syracuseStep 1890161 = 1417621) B1417621
theorem B841601 : Blo 558808 841601 := bstep (se 2 (by rfl) ⟨315600, by rfl⟩ : syracuseStep 841601 = 631201) B631201
theorem B841619 : Blo 558808 841619 := bstep (se 1 (by rfl) ⟨631214, by rfl⟩ : syracuseStep 841619 = 1262429) B1262429
theorem B841649 : Blo 558808 841649 := bstep (se 2 (by rfl) ⟨315618, by rfl⟩ : syracuseStep 841649 = 631237) B631237
theorem B841667 : Blo 558808 841667 := bstep (se 1 (by rfl) ⟨631250, by rfl⟩ : syracuseStep 841667 = 1262501) B1262501
theorem B841697 : Blo 558808 841697 := bstep (se 2 (by rfl) ⟨315636, by rfl⟩ : syracuseStep 841697 = 631273) B631273
theorem B841715 : Blo 558808 841715 := bstep (se 1 (by rfl) ⟨631286, by rfl⟩ : syracuseStep 841715 = 1262573) B1262573
theorem B841745 : Blo 558808 841745 := bstep (se 2 (by rfl) ⟨315654, by rfl⟩ : syracuseStep 841745 = 631309) B631309
theorem B841763 : Blo 558808 841763 := bstep (se 1 (by rfl) ⟨631322, by rfl⟩ : syracuseStep 841763 = 1262645) B1262645
theorem B841793 : Blo 558808 841793 := bstep (se 2 (by rfl) ⟨315672, by rfl⟩ : syracuseStep 841793 = 631345) B631345
theorem B841811 : Blo 558808 841811 := bstep (se 1 (by rfl) ⟨631358, by rfl⟩ : syracuseStep 841811 = 1262717) B1262717
theorem B9099377 : Blo 558808 9099377 := bstep (se 2 (by rfl) ⟨3412266, by rfl⟩ : syracuseStep 9099377 = 6824533) B6824533
theorem B841841 : Blo 558808 841841 := bstep (se 2 (by rfl) ⟨315690, by rfl⟩ : syracuseStep 841841 = 631381) B631381
theorem B841859 : Blo 558808 841859 := bstep (se 1 (by rfl) ⟨631394, by rfl⟩ : syracuseStep 841859 = 1262789) B1262789
theorem B841889 : Blo 558808 841889 := bstep (se 2 (by rfl) ⟨315708, by rfl⟩ : syracuseStep 841889 = 631417) B631417
theorem B841907 : Blo 558808 841907 := bstep (se 1 (by rfl) ⟨631430, by rfl⟩ : syracuseStep 841907 = 1262861) B1262861
theorem B710851 : Blo 558808 710851 := bstep (se 1 (by rfl) ⟨533138, by rfl⟩ : syracuseStep 710851 = 1066277) B1066277
theorem B4774085 : Blo 558808 4774085 := bstep (se 4 (by rfl) ⟨447570, by rfl⟩ : syracuseStep 4774085 = 895141) B895141
theorem B3201221 : Blo 558808 3201221 := bstep (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) B600229
theorem B841937 : Blo 558808 841937 := bstep (se 2 (by rfl) ⟨315726, by rfl⟩ : syracuseStep 841937 = 631453) B631453
theorem B841955 : Blo 558808 841955 := bstep (se 1 (by rfl) ⟨631466, by rfl⟩ : syracuseStep 841955 = 1262933) B1262933
theorem B6838499 : Blo 558808 6838499 := bstep (se 1 (by rfl) ⟨5128874, by rfl⟩ : syracuseStep 6838499 = 10257749) B10257749
theorem B841985 : Blo 558808 841985 := bstep (se 2 (by rfl) ⟨315744, by rfl⟩ : syracuseStep 841985 = 631489) B631489
theorem B842003 : Blo 558808 842003 := bstep (se 1 (by rfl) ⟨631502, by rfl⟩ : syracuseStep 842003 = 1263005) B1263005
theorem B710947 : Blo 558808 710947 := bstep (se 1 (by rfl) ⟨533210, by rfl⟩ : syracuseStep 710947 = 1066421) B1066421
theorem B842033 : Blo 558808 842033 := bstep (se 2 (by rfl) ⟨315762, by rfl⟩ : syracuseStep 842033 = 631525) B631525
theorem B842051 : Blo 558808 842051 := bstep (se 1 (by rfl) ⟨631538, by rfl⟩ : syracuseStep 842051 = 1263077) B1263077
theorem B842081 : Blo 558808 842081 := bstep (se 2 (by rfl) ⟨315780, by rfl⟩ : syracuseStep 842081 = 631561) B631561
theorem B842099 : Blo 558808 842099 := bstep (se 1 (by rfl) ⟨631574, by rfl⟩ : syracuseStep 842099 = 1263149) B1263149
theorem B1890701 : Blo 558808 1890701 := bstep (se 3 (by rfl) ⟨354506, by rfl⟩ : syracuseStep 1890701 = 709013) B709013
theorem B842129 : Blo 558808 842129 := bstep (se 2 (by rfl) ⟨315798, by rfl⟩ : syracuseStep 842129 = 631597) B631597
theorem B842147 : Blo 558808 842147 := bstep (se 1 (by rfl) ⟨631610, by rfl⟩ : syracuseStep 842147 = 1263221) B1263221
theorem B842177 : Blo 558808 842177 := bstep (se 2 (by rfl) ⟨315816, by rfl⟩ : syracuseStep 842177 = 631633) B631633
theorem B1890755 : Blo 558808 1890755 := bstep (se 1 (by rfl) ⟨1418066, by rfl⟩ : syracuseStep 1890755 = 2836133) B2836133
theorem B842195 : Blo 558808 842195 := bstep (se 1 (by rfl) ⟨631646, by rfl⟩ : syracuseStep 842195 = 1263293) B1263293
theorem B842225 : Blo 558808 842225 := bstep (se 2 (by rfl) ⟨315834, by rfl⟩ : syracuseStep 842225 = 631669) B631669
theorem B842243 : Blo 558808 842243 := bstep (se 1 (by rfl) ⟨631682, by rfl⟩ : syracuseStep 842243 = 1263365) B1263365
theorem B3037709 : Blo 558808 3037709 := bstep (se 3 (by rfl) ⟨569570, by rfl⟩ : syracuseStep 3037709 = 1139141) B1139141
theorem B842273 : Blo 558808 842273 := bstep (se 2 (by rfl) ⟨315852, by rfl⟩ : syracuseStep 842273 = 631705) B631705
theorem B842291 : Blo 558808 842291 := bstep (se 1 (by rfl) ⟨631718, by rfl⟩ : syracuseStep 842291 = 1263437) B1263437
theorem B842321 : Blo 558808 842321 := bstep (se 2 (by rfl) ⟨315870, by rfl⟩ : syracuseStep 842321 = 631741) B631741
theorem B842339 : Blo 558808 842339 := bstep (se 1 (by rfl) ⟨631754, by rfl⟩ : syracuseStep 842339 = 1263509) B1263509
theorem B842369 : Blo 558808 842369 := bstep (se 2 (by rfl) ⟨315888, by rfl⟩ : syracuseStep 842369 = 631777) B631777
theorem B3201677 : Blo 558808 3201677 := bstep (se 3 (by rfl) ⟨600314, by rfl⟩ : syracuseStep 3201677 = 1200629) B1200629
theorem B842387 : Blo 558808 842387 := bstep (se 1 (by rfl) ⟨631790, by rfl⟩ : syracuseStep 842387 = 1263581) B1263581
theorem B842417 : Blo 558808 842417 := bstep (se 2 (by rfl) ⟨315906, by rfl⟩ : syracuseStep 842417 = 631813) B631813
theorem B842435 : Blo 558808 842435 := bstep (se 1 (by rfl) ⟨631826, by rfl⟩ : syracuseStep 842435 = 1263653) B1263653
theorem B1891025 : Blo 558808 1891025 := bstep (se 2 (by rfl) ⟨709134, by rfl⟩ : syracuseStep 1891025 = 1418269) B1418269
theorem B842465 : Blo 558808 842465 := bstep (se 2 (by rfl) ⟨315924, by rfl⟩ : syracuseStep 842465 = 631849) B631849
theorem B842483 : Blo 558808 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B842513 : Blo 558808 842513 := bstep (se 2 (by rfl) ⟨315942, by rfl⟩ : syracuseStep 842513 = 631885) B631885
theorem B711443 : Blo 558808 711443 := bstep (se 1 (by rfl) ⟨533582, by rfl⟩ : syracuseStep 711443 = 1067165) B1067165
theorem B842531 : Blo 558808 842531 := bstep (se 1 (by rfl) ⟨631898, by rfl⟩ : syracuseStep 842531 = 1263797) B1263797
theorem B842561 : Blo 558808 842561 := bstep (se 2 (by rfl) ⟨315960, by rfl⟩ : syracuseStep 842561 = 631921) B631921
theorem B842579 : Blo 558808 842579 := bstep (se 1 (by rfl) ⟨631934, by rfl⟩ : syracuseStep 842579 = 1263869) B1263869
theorem B842609 : Blo 558808 842609 := bstep (se 2 (by rfl) ⟨315978, by rfl⟩ : syracuseStep 842609 = 631957) B631957
theorem B842627 : Blo 558808 842627 := bstep (se 1 (by rfl) ⟨631970, by rfl⟩ : syracuseStep 842627 = 1263941) B1263941
theorem B842657 : Blo 558808 842657 := bstep (se 2 (by rfl) ⟨315996, by rfl⟩ : syracuseStep 842657 = 631993) B631993
theorem B842675 : Blo 558808 842675 := bstep (se 1 (by rfl) ⟨632006, by rfl⟩ : syracuseStep 842675 = 1264013) B1264013
theorem B842705 : Blo 558808 842705 := bstep (se 2 (by rfl) ⟨316014, by rfl⟩ : syracuseStep 842705 = 632029) B632029
theorem B842723 : Blo 558808 842723 := bstep (se 1 (by rfl) ⟨632042, by rfl⟩ : syracuseStep 842723 = 1264085) B1264085
theorem B842753 : Blo 558808 842753 := bstep (se 2 (by rfl) ⟨316032, by rfl⟩ : syracuseStep 842753 = 632065) B632065
theorem B1596419 : Blo 558808 1596419 := bstep (se 1 (by rfl) ⟨1197314, by rfl⟩ : syracuseStep 1596419 = 2394629) B2394629
theorem B842771 : Blo 558808 842771 := bstep (se 1 (by rfl) ⟨632078, by rfl⟩ : syracuseStep 842771 = 1264157) B1264157
theorem B842801 : Blo 558808 842801 := bstep (se 2 (by rfl) ⟨316050, by rfl⟩ : syracuseStep 842801 = 632101) B632101
theorem B842819 : Blo 558808 842819 := bstep (se 1 (by rfl) ⟨632114, by rfl⟩ : syracuseStep 842819 = 1264229) B1264229
theorem B842849 : Blo 558808 842849 := bstep (se 2 (by rfl) ⟨316068, by rfl⟩ : syracuseStep 842849 = 632137) B632137
theorem B842867 : Blo 558808 842867 := bstep (se 1 (by rfl) ⟨632150, by rfl⟩ : syracuseStep 842867 = 1264301) B1264301
theorem B842897 : Blo 558808 842897 := bstep (se 2 (by rfl) ⟨316086, by rfl⟩ : syracuseStep 842897 = 632173) B632173
theorem B842915 : Blo 558808 842915 := bstep (se 1 (by rfl) ⟨632186, by rfl⟩ : syracuseStep 842915 = 1264373) B1264373
theorem B842945 : Blo 558808 842945 := bstep (se 2 (by rfl) ⟨316104, by rfl⟩ : syracuseStep 842945 = 632209) B632209
theorem B842963 : Blo 558808 842963 := bstep (se 1 (by rfl) ⟨632222, by rfl⟩ : syracuseStep 842963 = 1264445) B1264445
theorem B1891565 : Blo 558808 1891565 := bstep (se 3 (by rfl) ⟨354668, by rfl⟩ : syracuseStep 1891565 = 709337) B709337
theorem B842993 : Blo 558808 842993 := bstep (se 2 (by rfl) ⟨316122, by rfl⟩ : syracuseStep 842993 = 632245) B632245
theorem B843011 : Blo 558808 843011 := bstep (se 1 (by rfl) ⟨632258, by rfl⟩ : syracuseStep 843011 = 1264517) B1264517
theorem B1924355 : Blo 558808 1924355 := bstep (se 1 (by rfl) ⟨1443266, by rfl⟩ : syracuseStep 1924355 = 2886533) B2886533
theorem B843041 : Blo 558808 843041 := bstep (se 2 (by rfl) ⟨316140, by rfl⟩ : syracuseStep 843041 = 632281) B632281
theorem B1891619 : Blo 558808 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B2022691 : Blo 558808 2022691 := bstep (se 1 (by rfl) ⟨1517018, by rfl⟩ : syracuseStep 2022691 = 3034037) B3034037
theorem B843059 : Blo 558808 843059 := bstep (se 1 (by rfl) ⟨632294, by rfl⟩ : syracuseStep 843059 = 1264589) B1264589
theorem B843089 : Blo 558808 843089 := bstep (se 2 (by rfl) ⟨316158, by rfl⟩ : syracuseStep 843089 = 632317) B632317
theorem B843107 : Blo 558808 843107 := bstep (se 1 (by rfl) ⟨632330, by rfl⟩ : syracuseStep 843107 = 1264661) B1264661
theorem B843137 : Blo 558808 843137 := bstep (se 2 (by rfl) ⟨316176, by rfl⟩ : syracuseStep 843137 = 632353) B632353
theorem B843155 : Blo 558808 843155 := bstep (se 1 (by rfl) ⟨632366, by rfl⟩ : syracuseStep 843155 = 1264733) B1264733
theorem B2022833 : Blo 558808 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B843185 : Blo 558808 843185 := bstep (se 2 (by rfl) ⟨316194, by rfl⟩ : syracuseStep 843185 = 632389) B632389
theorem B843203 : Blo 558808 843203 := bstep (se 1 (by rfl) ⟨632402, by rfl⟩ : syracuseStep 843203 = 1264805) B1264805
theorem B712147 : Blo 558808 712147 := bstep (se 1 (by rfl) ⟨534110, by rfl⟩ : syracuseStep 712147 = 1068221) B1068221
theorem B843233 : Blo 558808 843233 := bstep (se 2 (by rfl) ⟨316212, by rfl⟩ : syracuseStep 843233 = 632425) B632425
theorem B843251 : Blo 558808 843251 := bstep (se 1 (by rfl) ⟨632438, by rfl⟩ : syracuseStep 843251 = 1264877) B1264877
theorem B843281 : Blo 558808 843281 := bstep (se 2 (by rfl) ⟨316230, by rfl⟩ : syracuseStep 843281 = 632461) B632461
theorem B843299 : Blo 558808 843299 := bstep (se 1 (by rfl) ⟨632474, by rfl⟩ : syracuseStep 843299 = 1264949) B1264949
theorem B1891889 : Blo 558808 1891889 := bstep (se 2 (by rfl) ⟨709458, by rfl⟩ : syracuseStep 1891889 = 1418917) B1418917
theorem B712243 : Blo 558808 712243 := bstep (se 1 (by rfl) ⟨534182, by rfl⟩ : syracuseStep 712243 = 1068365) B1068365
theorem B843329 : Blo 558808 843329 := bstep (se 2 (by rfl) ⟨316248, by rfl⟩ : syracuseStep 843329 = 632497) B632497
theorem B1793603 : Blo 558808 1793603 := bstep (se 1 (by rfl) ⟨1345202, by rfl⟩ : syracuseStep 1793603 = 2690405) B2690405
theorem B843347 : Blo 558808 843347 := bstep (se 1 (by rfl) ⟨632510, by rfl⟩ : syracuseStep 843347 = 1265021) B1265021
theorem B3038833 : Blo 558808 3038833 := bstep (se 2 (by rfl) ⟨1139562, by rfl⟩ : syracuseStep 3038833 = 2279125) B2279125
theorem B843377 : Blo 558808 843377 := bstep (se 2 (by rfl) ⟨316266, by rfl⟩ : syracuseStep 843377 = 632533) B632533
theorem B843395 : Blo 558808 843395 := bstep (se 1 (by rfl) ⟨632546, by rfl⟩ : syracuseStep 843395 = 1265093) B1265093
theorem B843425 : Blo 558808 843425 := bstep (se 2 (by rfl) ⟨316284, by rfl⟩ : syracuseStep 843425 = 632569) B632569
theorem B2842289 : Blo 558808 2842289 := bstep (se 2 (by rfl) ⟨1065858, by rfl⟩ : syracuseStep 2842289 = 2131717) B2131717
theorem B843443 : Blo 558808 843443 := bstep (se 1 (by rfl) ⟨632582, by rfl⟩ : syracuseStep 843443 = 1265165) B1265165
theorem B843473 : Blo 558808 843473 := bstep (se 2 (by rfl) ⟨316302, by rfl⟩ : syracuseStep 843473 = 632605) B632605
theorem B843491 : Blo 558808 843491 := bstep (se 1 (by rfl) ⟨632618, by rfl⟩ : syracuseStep 843491 = 1265237) B1265237
theorem B843521 : Blo 558808 843521 := bstep (se 2 (by rfl) ⟨316320, by rfl⟩ : syracuseStep 843521 = 632641) B632641
theorem B2023181 : Blo 558808 2023181 := bstep (se 3 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 2023181 = 758693) B758693
theorem B843539 : Blo 558808 843539 := bstep (se 1 (by rfl) ⟨632654, by rfl⟩ : syracuseStep 843539 = 1265309) B1265309
theorem B1597229 : Blo 558808 1597229 := bstep (se 3 (by rfl) ⟨299480, by rfl⟩ : syracuseStep 1597229 = 598961) B598961
theorem B843569 : Blo 558808 843569 := bstep (se 2 (by rfl) ⟨316338, by rfl⟩ : syracuseStep 843569 = 632677) B632677
theorem B843587 : Blo 558808 843587 := bstep (se 1 (by rfl) ⟨632690, by rfl⟩ : syracuseStep 843587 = 1265381) B1265381
theorem B843617 : Blo 558808 843617 := bstep (se 2 (by rfl) ⟨316356, by rfl⟩ : syracuseStep 843617 = 632713) B632713
theorem B843635 : Blo 558808 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B843665 : Blo 558808 843665 := bstep (se 2 (by rfl) ⟨316374, by rfl⟩ : syracuseStep 843665 = 632749) B632749
theorem B843683 : Blo 558808 843683 := bstep (se 1 (by rfl) ⟨632762, by rfl⟩ : syracuseStep 843683 = 1265525) B1265525
theorem B843713 : Blo 558808 843713 := bstep (se 2 (by rfl) ⟨316392, by rfl⟩ : syracuseStep 843713 = 632785) B632785
theorem B843731 : Blo 558808 843731 := bstep (se 1 (by rfl) ⟨632798, by rfl⟩ : syracuseStep 843731 = 1265597) B1265597
theorem B5103587 : Blo 558808 5103587 := bstep (se 1 (by rfl) ⟨3827690, by rfl⟩ : syracuseStep 5103587 = 7655381) B7655381
theorem B1597421 : Blo 558808 1597421 := bstep (se 3 (by rfl) ⟨299516, by rfl⟩ : syracuseStep 1597421 = 599033) B599033
theorem B843761 : Blo 558808 843761 := bstep (se 2 (by rfl) ⟨316410, by rfl⟩ : syracuseStep 843761 = 632821) B632821
theorem B843779 : Blo 558808 843779 := bstep (se 1 (by rfl) ⟨632834, by rfl⟩ : syracuseStep 843779 = 1265669) B1265669
theorem B843809 : Blo 558808 843809 := bstep (se 2 (by rfl) ⟨316428, by rfl⟩ : syracuseStep 843809 = 632857) B632857
theorem B843827 : Blo 558808 843827 := bstep (se 1 (by rfl) ⟨632870, by rfl⟩ : syracuseStep 843827 = 1265741) B1265741
theorem B1892429 : Blo 558808 1892429 := bstep (se 3 (by rfl) ⟨354830, by rfl⟩ : syracuseStep 1892429 = 709661) B709661
theorem B843857 : Blo 558808 843857 := bstep (se 2 (by rfl) ⟨316446, by rfl⟩ : syracuseStep 843857 = 632893) B632893
theorem B843875 : Blo 558808 843875 := bstep (se 1 (by rfl) ⟨632906, by rfl⟩ : syracuseStep 843875 = 1265813) B1265813
theorem B843905 : Blo 558808 843905 := bstep (se 2 (by rfl) ⟨316464, by rfl⟩ : syracuseStep 843905 = 632929) B632929
theorem B1892483 : Blo 558808 1892483 := bstep (se 1 (by rfl) ⟨1419362, by rfl⟩ : syracuseStep 1892483 = 2838725) B2838725
theorem B843923 : Blo 558808 843923 := bstep (se 1 (by rfl) ⟨632942, by rfl⟩ : syracuseStep 843923 = 1265885) B1265885
theorem B843953 : Blo 558808 843953 := bstep (se 2 (by rfl) ⟨316482, by rfl⟩ : syracuseStep 843953 = 632965) B632965
theorem B843971 : Blo 558808 843971 := bstep (se 1 (by rfl) ⟨632978, by rfl⟩ : syracuseStep 843971 = 1265957) B1265957
theorem B844001 : Blo 558808 844001 := bstep (se 2 (by rfl) ⟨316500, by rfl⟩ : syracuseStep 844001 = 633001) B633001
theorem B844019 : Blo 558808 844019 := bstep (se 1 (by rfl) ⟨633014, by rfl⟩ : syracuseStep 844019 = 1266029) B1266029
theorem B2121997 : Blo 558808 2121997 := bstep (se 3 (by rfl) ⟨397874, by rfl⟩ : syracuseStep 2121997 = 795749) B795749
theorem B844049 : Blo 558808 844049 := bstep (se 2 (by rfl) ⟨316518, by rfl⟩ : syracuseStep 844049 = 633037) B633037
theorem B1138979 : Blo 558808 1138979 := bstep (se 1 (by rfl) ⟨854234, by rfl⟩ : syracuseStep 1138979 = 1708469) B1708469
theorem B844067 : Blo 558808 844067 := bstep (se 1 (by rfl) ⟨633050, by rfl⟩ : syracuseStep 844067 = 1266101) B1266101
theorem B844097 : Blo 558808 844097 := bstep (se 2 (by rfl) ⟨316536, by rfl⟩ : syracuseStep 844097 = 633073) B633073
theorem B844115 : Blo 558808 844115 := bstep (se 1 (by rfl) ⟨633086, by rfl⟩ : syracuseStep 844115 = 1266173) B1266173
theorem B811363 : Blo 558808 811363 := bstep (se 1 (by rfl) ⟨608522, by rfl⟩ : syracuseStep 811363 = 1217045) B1217045
theorem B844145 : Blo 558808 844145 := bstep (se 2 (by rfl) ⟨316554, by rfl⟩ : syracuseStep 844145 = 633109) B633109
theorem B844163 : Blo 558808 844163 := bstep (se 1 (by rfl) ⟨633122, by rfl⟩ : syracuseStep 844163 = 1266245) B1266245
theorem B1892753 : Blo 558808 1892753 := bstep (se 2 (by rfl) ⟨709782, by rfl⟩ : syracuseStep 1892753 = 1419565) B1419565
theorem B844193 : Blo 558808 844193 := bstep (se 2 (by rfl) ⟨316572, by rfl⟩ : syracuseStep 844193 = 633145) B633145
theorem B844211 : Blo 558808 844211 := bstep (se 1 (by rfl) ⟨633158, by rfl⟩ : syracuseStep 844211 = 1266317) B1266317
theorem B6841073 : Blo 558808 6841073 := bstep (se 2 (by rfl) ⟨2565402, by rfl⟩ : syracuseStep 6841073 = 5130805) B5130805
theorem B942995 : Blo 558808 942995 := bstep (se 1 (by rfl) ⟨707246, by rfl⟩ : syracuseStep 942995 = 1414493) B1414493
theorem B1893293 : Blo 558808 1893293 := bstep (se 3 (by rfl) ⟨354992, by rfl⟩ : syracuseStep 1893293 = 709985) B709985
theorem B1598413 : Blo 558808 1598413 := bstep (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) B599405
theorem B1893347 : Blo 558808 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B812035 : Blo 558808 812035 := bstep (se 1 (by rfl) ⟨609026, by rfl⟩ : syracuseStep 812035 = 1218053) B1218053
theorem B943123 : Blo 558808 943123 := bstep (se 1 (by rfl) ⟨707342, by rfl⟩ : syracuseStep 943123 = 1414685) B1414685
theorem B910369 : Blo 558808 910369 := bstep (se 2 (by rfl) ⟨341388, by rfl⟩ : syracuseStep 910369 = 682777) B682777
theorem B2122787 : Blo 558808 2122787 := bstep (se 1 (by rfl) ⟨1592090, by rfl⟩ : syracuseStep 2122787 = 3184181) B3184181
theorem B2843747 : Blo 558808 2843747 := bstep (se 1 (by rfl) ⟨2132810, by rfl⟩ : syracuseStep 2843747 = 4265621) B4265621
theorem B943265 : Blo 558808 943265 := bstep (se 2 (by rfl) ⟨353724, by rfl⟩ : syracuseStep 943265 = 707449) B707449
theorem B1893617 : Blo 558808 1893617 := bstep (se 2 (by rfl) ⟨710106, by rfl⟩ : syracuseStep 1893617 = 1420213) B1420213
theorem B7202033 : Blo 558808 7202033 := bstep (se 2 (by rfl) ⟨2700762, by rfl⟩ : syracuseStep 7202033 = 5401525) B5401525
theorem B943393 : Blo 558808 943393 := bstep (se 2 (by rfl) ⟨353772, by rfl⟩ : syracuseStep 943393 = 707545) B707545
theorem B943427 : Blo 558808 943427 := bstep (se 1 (by rfl) ⟨707570, by rfl⟩ : syracuseStep 943427 = 1415141) B1415141
theorem B1795409 : Blo 558808 1795409 := bstep (se 2 (by rfl) ⟨673278, by rfl⟩ : syracuseStep 1795409 = 1346557) B1346557
theorem B1795459 : Blo 558808 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B943555 : Blo 558808 943555 := bstep (se 1 (by rfl) ⟨707666, by rfl⟩ : syracuseStep 943555 = 1415333) B1415333
theorem B3630563 : Blo 558808 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B3204593 : Blo 558808 3204593 := bstep (se 2 (by rfl) ⟨1201722, by rfl⟩ : syracuseStep 3204593 = 2403445) B2403445
theorem B943697 : Blo 558808 943697 := bstep (se 2 (by rfl) ⟨353886, by rfl⟩ : syracuseStep 943697 = 707773) B707773
theorem B6055523 : Blo 558808 6055523 := bstep (se 1 (by rfl) ⟨4541642, by rfl⟩ : syracuseStep 6055523 = 9083285) B9083285
theorem B2123441 : Blo 558808 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B943825 : Blo 558808 943825 := bstep (se 2 (by rfl) ⟨353934, by rfl⟩ : syracuseStep 943825 = 707869) B707869
theorem B943859 : Blo 558808 943859 := bstep (se 1 (by rfl) ⟨707894, by rfl⟩ : syracuseStep 943859 = 1415789) B1415789
theorem B1894157 : Blo 558808 1894157 := bstep (se 3 (by rfl) ⟨355154, by rfl⟩ : syracuseStep 1894157 = 710309) B710309
theorem B1894211 : Blo 558808 1894211 := bstep (se 1 (by rfl) ⟨1420658, by rfl⟩ : syracuseStep 1894211 = 2841317) B2841317
theorem B2549603 : Blo 558808 2549603 := bstep (se 1 (by rfl) ⟨1912202, by rfl⟩ : syracuseStep 2549603 = 3824405) B3824405
theorem B943987 : Blo 558808 943987 := bstep (se 1 (by rfl) ⟨707990, by rfl⟩ : syracuseStep 943987 = 1415981) B1415981
theorem B2844557 : Blo 558808 2844557 := bstep (se 3 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 2844557 = 1066709) B1066709
theorem B944129 : Blo 558808 944129 := bstep (se 2 (by rfl) ⟨354048, by rfl⟩ : syracuseStep 944129 = 708097) B708097
theorem B1796177 : Blo 558808 1796177 := bstep (se 2 (by rfl) ⟨673566, by rfl⟩ : syracuseStep 1796177 = 1347133) B1347133
theorem B1894481 : Blo 558808 1894481 := bstep (se 2 (by rfl) ⟨710430, by rfl⟩ : syracuseStep 1894481 = 1420861) B1420861
theorem B944257 : Blo 558808 944257 := bstep (se 2 (by rfl) ⟨354096, by rfl⟩ : syracuseStep 944257 = 708193) B708193
theorem B944291 : Blo 558808 944291 := bstep (se 1 (by rfl) ⟨708218, by rfl⟩ : syracuseStep 944291 = 1416437) B1416437
theorem B944419 : Blo 558808 944419 := bstep (se 1 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 944419 = 1416629) B1416629
theorem B944561 : Blo 558808 944561 := bstep (se 2 (by rfl) ⟨354210, by rfl⟩ : syracuseStep 944561 = 708421) B708421
theorem B3631601 : Blo 558808 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B944689 : Blo 558808 944689 := bstep (se 2 (by rfl) ⟨354258, by rfl⟩ : syracuseStep 944689 = 708517) B708517
theorem B1796689 : Blo 558808 1796689 := bstep (se 2 (by rfl) ⟨673758, by rfl⟩ : syracuseStep 1796689 = 1347517) B1347517
theorem B944723 : Blo 558808 944723 := bstep (se 1 (by rfl) ⟨708542, by rfl⟩ : syracuseStep 944723 = 1417085) B1417085
theorem B1895021 : Blo 558808 1895021 := bstep (se 3 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 1895021 = 710633) B710633
theorem B1600145 : Blo 558808 1600145 := bstep (se 2 (by rfl) ⟨600054, by rfl⟩ : syracuseStep 1600145 = 1200109) B1200109
theorem B1895075 : Blo 558808 1895075 := bstep (se 1 (by rfl) ⟨1421306, by rfl⟩ : syracuseStep 1895075 = 2842613) B2842613
theorem B944851 : Blo 558808 944851 := bstep (se 1 (by rfl) ⟨708638, by rfl⟩ : syracuseStep 944851 = 1417277) B1417277
theorem B584435 : Blo 558808 584435 := bstep (se 1 (by rfl) ⟨438326, by rfl⟩ : syracuseStep 584435 = 876653) B876653
theorem B912161 : Blo 558808 912161 := bstep (se 2 (by rfl) ⟨342060, by rfl⟩ : syracuseStep 912161 = 684121) B684121
theorem B1600337 : Blo 558808 1600337 := bstep (se 2 (by rfl) ⟨600126, by rfl⟩ : syracuseStep 1600337 = 1200253) B1200253
theorem B944993 : Blo 558808 944993 := bstep (se 2 (by rfl) ⟨354372, by rfl⟩ : syracuseStep 944993 = 708745) B708745
theorem B1895345 : Blo 558808 1895345 := bstep (se 2 (by rfl) ⟨710754, by rfl⟩ : syracuseStep 1895345 = 1421509) B1421509
theorem B6384581 : Blo 558808 6384581 := bstep (se 4 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 6384581 = 1197109) B1197109
theorem B945121 : Blo 558808 945121 := bstep (se 2 (by rfl) ⟨354420, by rfl⟩ : syracuseStep 945121 = 708841) B708841
theorem B945155 : Blo 558808 945155 := bstep (se 1 (by rfl) ⟨708866, by rfl⟩ : syracuseStep 945155 = 1417733) B1417733
theorem B2124899 : Blo 558808 2124899 := bstep (se 1 (by rfl) ⟨1593674, by rfl⟩ : syracuseStep 2124899 = 3187349) B3187349
theorem B2124913 : Blo 558808 2124913 := bstep (se 2 (by rfl) ⟨796842, by rfl⟩ : syracuseStep 2124913 = 1593685) B1593685
theorem B945283 : Blo 558808 945283 := bstep (se 1 (by rfl) ⟨708962, by rfl⟩ : syracuseStep 945283 = 1417925) B1417925
theorem B2551025 : Blo 558808 2551025 := bstep (se 2 (by rfl) ⟨956634, by rfl⟩ : syracuseStep 2551025 = 1913269) B1913269
theorem B945425 : Blo 558808 945425 := bstep (se 2 (by rfl) ⟨354534, by rfl⟩ : syracuseStep 945425 = 709069) B709069
theorem B16149901 : Blo 558808 16149901 := bstep (se 3 (by rfl) ⟨3028106, by rfl⟩ : syracuseStep 16149901 = 6056213) B6056213
theorem B945553 : Blo 558808 945553 := bstep (se 2 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 945553 = 709165) B709165
theorem B945587 : Blo 558808 945587 := bstep (se 1 (by rfl) ⟨709190, by rfl⟩ : syracuseStep 945587 = 1418381) B1418381
theorem B1895885 : Blo 558808 1895885 := bstep (se 3 (by rfl) ⟨355478, by rfl⟩ : syracuseStep 1895885 = 710957) B710957
theorem B2026957 : Blo 558808 2026957 := bstep (se 3 (by rfl) ⟨380054, by rfl⟩ : syracuseStep 2026957 = 760109) B760109
theorem B1895939 : Blo 558808 1895939 := bstep (se 1 (by rfl) ⟨1421954, by rfl⟩ : syracuseStep 1895939 = 2843909) B2843909
theorem B945715 : Blo 558808 945715 := bstep (se 1 (by rfl) ⟨709286, by rfl⟩ : syracuseStep 945715 = 1418573) B1418573
theorem B1797805 : Blo 558808 1797805 := bstep (se 3 (by rfl) ⟨337088, by rfl⟩ : syracuseStep 1797805 = 674177) B674177
theorem B945857 : Blo 558808 945857 := bstep (se 2 (by rfl) ⟨354696, by rfl⟩ : syracuseStep 945857 = 709393) B709393
theorem B683731 : Blo 558808 683731 := bstep (se 1 (by rfl) ⟨512798, by rfl⟩ : syracuseStep 683731 = 1025597) B1025597
theorem B1797869 : Blo 558808 1797869 := bstep (se 3 (by rfl) ⟨337100, by rfl⟩ : syracuseStep 1797869 = 674201) B674201
theorem B4091633 : Blo 558808 4091633 := bstep (se 2 (by rfl) ⟨1534362, by rfl⟩ : syracuseStep 4091633 = 3068725) B3068725
theorem B1896209 : Blo 558808 1896209 := bstep (se 2 (by rfl) ⟨711078, by rfl⟩ : syracuseStep 1896209 = 1422157) B1422157
theorem B1601329 : Blo 558808 1601329 := bstep (se 2 (by rfl) ⟨600498, by rfl⟩ : syracuseStep 1601329 = 1200997) B1200997
theorem B945985 : Blo 558808 945985 := bstep (se 2 (by rfl) ⟨354744, by rfl⟩ : syracuseStep 945985 = 709489) B709489
theorem B3600197 : Blo 558808 3600197 := bstep (se 4 (by rfl) ⟨337518, by rfl⟩ : syracuseStep 3600197 = 675037) B675037
theorem B946019 : Blo 558808 946019 := bstep (se 1 (by rfl) ⟨709514, by rfl⟩ : syracuseStep 946019 = 1419029) B1419029
theorem B1011619 : Blo 558808 1011619 := bstep (se 1 (by rfl) ⟨758714, by rfl⟩ : syracuseStep 1011619 = 1517429) B1517429
theorem B946147 : Blo 558808 946147 := bstep (se 1 (by rfl) ⟨709610, by rfl⟩ : syracuseStep 946147 = 1419221) B1419221
theorem B1601603 : Blo 558808 1601603 := bstep (se 1 (by rfl) ⟨1201202, by rfl⟩ : syracuseStep 1601603 = 2402405) B2402405
theorem B946289 : Blo 558808 946289 := bstep (se 2 (by rfl) ⟨354858, by rfl⟩ : syracuseStep 946289 = 709717) B709717
theorem B946417 : Blo 558808 946417 := bstep (se 2 (by rfl) ⟨354906, by rfl⟩ : syracuseStep 946417 = 709813) B709813
theorem B1601795 : Blo 558808 1601795 := bstep (se 1 (by rfl) ⟨1201346, by rfl⟩ : syracuseStep 1601795 = 2402693) B2402693
theorem B946451 : Blo 558808 946451 := bstep (se 1 (by rfl) ⟨709838, by rfl⟩ : syracuseStep 946451 = 1419677) B1419677
theorem B1896749 : Blo 558808 1896749 := bstep (se 3 (by rfl) ⟨355640, by rfl⟩ : syracuseStep 1896749 = 711281) B711281
theorem B1732963 : Blo 558808 1732963 := bstep (se 1 (by rfl) ⟨1299722, by rfl⟩ : syracuseStep 1732963 = 2599445) B2599445
theorem B1896803 : Blo 558808 1896803 := bstep (se 1 (by rfl) ⟨1422602, by rfl⟩ : syracuseStep 1896803 = 2845205) B2845205
theorem B946579 : Blo 558808 946579 := bstep (se 1 (by rfl) ⟨709934, by rfl⟩ : syracuseStep 946579 = 1419869) B1419869
theorem B946721 : Blo 558808 946721 := bstep (se 2 (by rfl) ⟨355020, by rfl⟩ : syracuseStep 946721 = 710041) B710041
theorem B2126371 : Blo 558808 2126371 := bstep (se 1 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 2126371 = 3189557) B3189557
theorem B1897073 : Blo 558808 1897073 := bstep (se 2 (by rfl) ⟨711402, by rfl⟩ : syracuseStep 1897073 = 1422805) B1422805
theorem B946849 : Blo 558808 946849 := bstep (se 2 (by rfl) ⟨355068, by rfl⟩ : syracuseStep 946849 = 710137) B710137
theorem B946883 : Blo 558808 946883 := bstep (se 1 (by rfl) ⟨710162, by rfl⟩ : syracuseStep 946883 = 1420325) B1420325
theorem B2847473 : Blo 558808 2847473 := bstep (se 2 (by rfl) ⟨1067802, by rfl⟩ : syracuseStep 2847473 = 2135605) B2135605
theorem B1012483 : Blo 558808 1012483 := bstep (se 1 (by rfl) ⟨759362, by rfl⟩ : syracuseStep 1012483 = 1518725) B1518725
theorem B947011 : Blo 558808 947011 := bstep (se 1 (by rfl) ⟨710258, by rfl⟩ : syracuseStep 947011 = 1420517) B1420517
theorem B22999949 : Blo 558808 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B1012657 : Blo 558808 1012657 := bstep (se 2 (by rfl) ⟨379746, by rfl⟩ : syracuseStep 1012657 = 759493) B759493
theorem B947153 : Blo 558808 947153 := bstep (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) B710365
theorem B1602605 : Blo 558808 1602605 := bstep (se 3 (by rfl) ⟨300488, by rfl⟩ : syracuseStep 1602605 = 600977) B600977
theorem B947281 : Blo 558808 947281 := bstep (se 2 (by rfl) ⟨355230, by rfl⟩ : syracuseStep 947281 = 710461) B710461
theorem B32240753 : Blo 558808 32240753 := bstep (se 2 (by rfl) ⟨12090282, by rfl⟩ : syracuseStep 32240753 = 24180565) B24180565
theorem B947315 : Blo 558808 947315 := bstep (se 1 (by rfl) ⟨710486, by rfl⟩ : syracuseStep 947315 = 1420973) B1420973
theorem B1897613 : Blo 558808 1897613 := bstep (se 3 (by rfl) ⟨355802, by rfl⟩ : syracuseStep 1897613 = 711605) B711605
theorem B7206029 : Blo 558808 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B1897667 : Blo 558808 1897667 := bstep (se 1 (by rfl) ⟨1423250, by rfl⟩ : syracuseStep 1897667 = 2846501) B2846501
theorem B947443 : Blo 558808 947443 := bstep (se 1 (by rfl) ⟨710582, by rfl⟩ : syracuseStep 947443 = 1421165) B1421165
theorem B2389283 : Blo 558808 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B947585 : Blo 558808 947585 := bstep (se 2 (by rfl) ⟨355344, by rfl⟩ : syracuseStep 947585 = 710689) B710689
theorem B1897937 : Blo 558808 1897937 := bstep (se 2 (by rfl) ⟨711726, by rfl⟩ : syracuseStep 1897937 = 1423453) B1423453
theorem B1799651 : Blo 558808 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B947713 : Blo 558808 947713 := bstep (se 2 (by rfl) ⟨355392, by rfl⟩ : syracuseStep 947713 = 710785) B710785
theorem B947747 : Blo 558808 947747 := bstep (se 1 (by rfl) ⟨710810, by rfl⟩ : syracuseStep 947747 = 1421621) B1421621
theorem B947875 : Blo 558808 947875 := bstep (se 1 (by rfl) ⟨710906, by rfl⟩ : syracuseStep 947875 = 1421813) B1421813
theorem B3405509 : Blo 558808 3405509 := bstep (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) B638533
theorem B1013521 : Blo 558808 1013521 := bstep (se 2 (by rfl) ⟨380070, by rfl⟩ : syracuseStep 1013521 = 760141) B760141
theorem B718627 : Blo 558808 718627 := bstep (se 1 (by rfl) ⟨538970, by rfl⟩ : syracuseStep 718627 = 1077941) B1077941
theorem B948017 : Blo 558808 948017 := bstep (se 2 (by rfl) ⟨355506, by rfl⟩ : syracuseStep 948017 = 711013) B711013
theorem B948145 : Blo 558808 948145 := bstep (se 2 (by rfl) ⟨355554, by rfl⟩ : syracuseStep 948145 = 711109) B711109
theorem B948179 : Blo 558808 948179 := bstep (se 1 (by rfl) ⟨711134, by rfl⟩ : syracuseStep 948179 = 1422269) B1422269
theorem B1898477 : Blo 558808 1898477 := bstep (se 3 (by rfl) ⟨355964, by rfl⟩ : syracuseStep 1898477 = 711929) B711929
theorem B1898531 : Blo 558808 1898531 := bstep (se 1 (by rfl) ⟨1423898, by rfl⟩ : syracuseStep 1898531 = 2847797) B2847797
theorem B4782149 : Blo 558808 4782149 := bstep (se 4 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 4782149 = 896653) B896653
theorem B948307 : Blo 558808 948307 := bstep (se 1 (by rfl) ⟨711230, by rfl⟩ : syracuseStep 948307 = 1422461) B1422461
theorem B2848931 : Blo 558808 2848931 := bstep (se 1 (by rfl) ⟨2136698, by rfl⟩ : syracuseStep 2848931 = 4273397) B4273397
theorem B1702097 : Blo 558808 1702097 := bstep (se 2 (by rfl) ⟨638286, by rfl⟩ : syracuseStep 1702097 = 1276573) B1276573
theorem B948449 : Blo 558808 948449 := bstep (se 2 (by rfl) ⟨355668, by rfl⟩ : syracuseStep 948449 = 711337) B711337
theorem B1898801 : Blo 558808 1898801 := bstep (se 2 (by rfl) ⟨712050, by rfl⟩ : syracuseStep 1898801 = 1424101) B1424101
theorem B7174453 : Blo 558808 7174453 := bstep (se 5 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 7174453 = 672605) B672605
theorem B948577 : Blo 558808 948577 := bstep (se 2 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 948577 = 711433) B711433
theorem B948611 : Blo 558808 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B850355 : Blo 558808 850355 := bstep (se 1 (by rfl) ⟨637766, by rfl⟩ : syracuseStep 850355 = 1275533) B1275533
theorem B948739 : Blo 558808 948739 := bstep (se 1 (by rfl) ⟨711554, by rfl⟩ : syracuseStep 948739 = 1423109) B1423109
theorem B3242501 : Blo 558808 3242501 := bstep (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) B607969
theorem B948881 : Blo 558808 948881 := bstep (se 2 (by rfl) ⟨355830, by rfl⟩ : syracuseStep 948881 = 711661) B711661
theorem B2128589 : Blo 558808 2128589 := bstep (se 3 (by rfl) ⟨399110, by rfl⟩ : syracuseStep 2128589 = 798221) B798221
theorem B4782833 : Blo 558808 4782833 := bstep (se 2 (by rfl) ⟨1793562, by rfl⟩ : syracuseStep 4782833 = 3587125) B3587125
theorem B949009 : Blo 558808 949009 := bstep (se 2 (by rfl) ⟨355878, by rfl⟩ : syracuseStep 949009 = 711757) B711757
theorem B949043 : Blo 558808 949043 := bstep (se 1 (by rfl) ⟨711782, by rfl⟩ : syracuseStep 949043 = 1423565) B1423565
theorem B1899341 : Blo 558808 1899341 := bstep (se 3 (by rfl) ⟨356126, by rfl⟩ : syracuseStep 1899341 = 712253) B712253
theorem B1899395 : Blo 558808 1899395 := bstep (se 1 (by rfl) ⟨1424546, by rfl⟩ : syracuseStep 1899395 = 2849093) B2849093
theorem B949171 : Blo 558808 949171 := bstep (se 1 (by rfl) ⟨711878, by rfl⟩ : syracuseStep 949171 = 1423757) B1423757
theorem B949313 : Blo 558808 949313 := bstep (se 2 (by rfl) ⟨355992, by rfl⟩ : syracuseStep 949313 = 711985) B711985
theorem B2686115 : Blo 558808 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B949441 : Blo 558808 949441 := bstep (se 2 (by rfl) ⟨356040, by rfl⟩ : syracuseStep 949441 = 712081) B712081
theorem B1277137 : Blo 558808 1277137 := bstep (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) B957853
theorem B949475 : Blo 558808 949475 := bstep (se 1 (by rfl) ⟨712106, by rfl⟩ : syracuseStep 949475 = 1424213) B1424213
theorem B2391281 : Blo 558808 2391281 := bstep (se 2 (by rfl) ⟨896730, by rfl⟩ : syracuseStep 2391281 = 1793461) B1793461
theorem B3603811 : Blo 558808 3603811 := bstep (se 1 (by rfl) ⟨2702858, by rfl⟩ : syracuseStep 3603811 = 5405717) B5405717
theorem B949603 : Blo 558808 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B1080803 : Blo 558808 1080803 := bstep (se 1 (by rfl) ⟨810602, by rfl⟩ : syracuseStep 1080803 = 1621205) B1621205
theorem B851699 : Blo 558808 851699 := bstep (se 1 (by rfl) ⟨638774, by rfl⟩ : syracuseStep 851699 = 1277549) B1277549
theorem B1703825 : Blo 558808 1703825 := bstep (se 2 (by rfl) ⟨638934, by rfl⟩ : syracuseStep 1703825 = 1277869) B1277869
theorem B1802225 : Blo 558808 1802225 := bstep (se 2 (by rfl) ⟨675834, by rfl⟩ : syracuseStep 1802225 = 1351669) B1351669
theorem B1278067 : Blo 558808 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B4260275 : Blo 558808 4260275 := bstep (se 1 (by rfl) ⟨3195206, by rfl⟩ : syracuseStep 4260275 = 6390413) B6390413
theorem B1081817 : Blo 558808 1081817 := bstep (se 2 (by rfl) ⟨405681, by rfl⟩ : syracuseStep 1081817 = 811363) B811363
theorem B2556467 : Blo 558808 2556467 := bstep (se 1 (by rfl) ⟨1917350, by rfl⟩ : syracuseStep 2556467 = 3834701) B3834701
theorem B2130563 : Blo 558808 2130563 := bstep (se 1 (by rfl) ⟨1597922, by rfl⟩ : syracuseStep 2130563 = 3195845) B3195845
theorem B1802969 : Blo 558808 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B852823 : Blo 558808 852823 := bstep (se 1 (by rfl) ⟨639617, by rfl⟩ : syracuseStep 852823 = 1279235) B1279235
theorem B5473241 : Blo 558808 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B2131019 : Blo 558808 2131019 := bstep (se 1 (by rfl) ⟨1598264, by rfl⟩ : syracuseStep 2131019 = 3196529) B3196529
theorem B3605579 : Blo 558808 3605579 := bstep (se 1 (by rfl) ⟨2704184, by rfl⟩ : syracuseStep 3605579 = 5408369) B5408369
theorem B1279127 : Blo 558808 1279127 := bstep (se 1 (by rfl) ⟨959345, by rfl⟩ : syracuseStep 1279127 = 1918691) B1918691
theorem B2131217 : Blo 558808 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B1344971 : Blo 558808 1344971 := bstep (se 1 (by rfl) ⟨1008728, by rfl⟩ : syracuseStep 1344971 = 2017457) B2017457
theorem B558827 : Blo 558808 558827 := bstep (se 1 (by rfl) ⟨419120, by rfl⟩ : syracuseStep 558827 = 838241) B838241
theorem B558839 : Blo 558808 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B558859 : Blo 558808 558859 := bstep (se 1 (by rfl) ⟨419144, by rfl⟩ : syracuseStep 558859 = 838289) B838289
theorem B558871 : Blo 558808 558871 := bstep (se 1 (by rfl) ⟨419153, by rfl⟩ : syracuseStep 558871 = 838307) B838307
theorem B558891 : Blo 558808 558891 := bstep (se 1 (by rfl) ⟨419168, by rfl⟩ : syracuseStep 558891 = 838337) B838337
theorem B558903 : Blo 558808 558903 := bstep (se 1 (by rfl) ⟨419177, by rfl⟩ : syracuseStep 558903 = 838355) B838355
theorem B558923 : Blo 558808 558923 := bstep (se 1 (by rfl) ⟨419192, by rfl⟩ : syracuseStep 558923 = 838385) B838385
theorem B558935 : Blo 558808 558935 := bstep (se 1 (by rfl) ⟨419201, by rfl⟩ : syracuseStep 558935 = 838403) B838403
theorem B2393945 : Blo 558808 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B4261733 : Blo 558808 4261733 := bstep (se 4 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 4261733 = 799075) B799075
theorem B558955 : Blo 558808 558955 := bstep (se 1 (by rfl) ⟨419216, by rfl⟩ : syracuseStep 558955 = 838433) B838433
theorem B558967 : Blo 558808 558967 := bstep (se 1 (by rfl) ⟨419225, by rfl⟩ : syracuseStep 558967 = 838451) B838451
theorem B558987 : Blo 558808 558987 := bstep (se 1 (by rfl) ⟨419240, by rfl⟩ : syracuseStep 558987 = 838481) B838481
theorem B558999 : Blo 558808 558999 := bstep (se 1 (by rfl) ⟨419249, by rfl⟩ : syracuseStep 558999 = 838499) B838499
theorem B559019 : Blo 558808 559019 := bstep (se 1 (by rfl) ⟨419264, by rfl⟩ : syracuseStep 559019 = 838529) B838529
theorem B559031 : Blo 558808 559031 := bstep (se 1 (by rfl) ⟨419273, by rfl⟩ : syracuseStep 559031 = 838547) B838547
theorem B559051 : Blo 558808 559051 := bstep (se 1 (by rfl) ⟨419288, by rfl⟩ : syracuseStep 559051 = 838577) B838577
theorem B559063 : Blo 558808 559063 := bstep (se 1 (by rfl) ⟨419297, by rfl⟩ : syracuseStep 559063 = 838595) B838595
theorem B559083 : Blo 558808 559083 := bstep (se 1 (by rfl) ⟨419312, by rfl⟩ : syracuseStep 559083 = 838625) B838625
theorem B559095 : Blo 558808 559095 := bstep (se 1 (by rfl) ⟨419321, by rfl⟩ : syracuseStep 559095 = 838643) B838643
theorem B559115 : Blo 558808 559115 := bstep (se 1 (by rfl) ⟨419336, by rfl⟩ : syracuseStep 559115 = 838673) B838673
theorem B559127 : Blo 558808 559127 := bstep (se 1 (by rfl) ⟨419345, by rfl⟩ : syracuseStep 559127 = 838691) B838691
theorem B2131991 : Blo 558808 2131991 := bstep (se 1 (by rfl) ⟨1598993, by rfl⟩ : syracuseStep 2131991 = 3197987) B3197987
theorem B559147 : Blo 558808 559147 := bstep (se 1 (by rfl) ⟨419360, by rfl⟩ : syracuseStep 559147 = 838721) B838721
theorem B559159 : Blo 558808 559159 := bstep (se 1 (by rfl) ⟨419369, by rfl⟩ : syracuseStep 559159 = 838739) B838739
theorem B559179 : Blo 558808 559179 := bstep (se 1 (by rfl) ⟨419384, by rfl⟩ : syracuseStep 559179 = 838769) B838769
theorem B559191 : Blo 558808 559191 := bstep (se 1 (by rfl) ⟨419393, by rfl⟩ : syracuseStep 559191 = 838787) B838787
theorem B559211 : Blo 558808 559211 := bstep (se 1 (by rfl) ⟨419408, by rfl⟩ : syracuseStep 559211 = 838817) B838817
theorem B559223 : Blo 558808 559223 := bstep (se 1 (by rfl) ⟨419417, by rfl⟩ : syracuseStep 559223 = 838835) B838835
theorem B559243 : Blo 558808 559243 := bstep (se 1 (by rfl) ⟨419432, by rfl⟩ : syracuseStep 559243 = 838865) B838865
theorem B559255 : Blo 558808 559255 := bstep (se 1 (by rfl) ⟨419441, by rfl⟩ : syracuseStep 559255 = 838883) B838883
theorem B559275 : Blo 558808 559275 := bstep (se 1 (by rfl) ⟨419456, by rfl⟩ : syracuseStep 559275 = 838913) B838913
theorem B559287 : Blo 558808 559287 := bstep (se 1 (by rfl) ⟨419465, by rfl⟩ : syracuseStep 559287 = 838931) B838931
theorem B559307 : Blo 558808 559307 := bstep (se 1 (by rfl) ⟨419480, by rfl⟩ : syracuseStep 559307 = 838961) B838961
theorem B559319 : Blo 558808 559319 := bstep (se 1 (by rfl) ⟨419489, by rfl⟩ : syracuseStep 559319 = 838979) B838979
theorem B2132189 : Blo 558808 2132189 := bstep (se 3 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 2132189 = 799571) B799571
theorem B559339 : Blo 558808 559339 := bstep (se 1 (by rfl) ⟨419504, by rfl⟩ : syracuseStep 559339 = 839009) B839009
theorem B559351 : Blo 558808 559351 := bstep (se 1 (by rfl) ⟨419513, by rfl⟩ : syracuseStep 559351 = 839027) B839027
theorem B559371 : Blo 558808 559371 := bstep (se 1 (by rfl) ⟨419528, by rfl⟩ : syracuseStep 559371 = 839057) B839057
theorem B559383 : Blo 558808 559383 := bstep (se 1 (by rfl) ⟨419537, by rfl⟩ : syracuseStep 559383 = 839075) B839075
theorem B559403 : Blo 558808 559403 := bstep (se 1 (by rfl) ⟨419552, by rfl⟩ : syracuseStep 559403 = 839105) B839105
theorem B559415 : Blo 558808 559415 := bstep (se 1 (by rfl) ⟨419561, by rfl⟩ : syracuseStep 559415 = 839123) B839123
theorem B5114177 : Blo 558808 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B559435 : Blo 558808 559435 := bstep (se 1 (by rfl) ⟨419576, by rfl⟩ : syracuseStep 559435 = 839153) B839153
theorem B4262219 : Blo 558808 4262219 := bstep (se 1 (by rfl) ⟨3196664, by rfl⟩ : syracuseStep 4262219 = 6393329) B6393329
theorem B559447 : Blo 558808 559447 := bstep (se 1 (by rfl) ⟨419585, by rfl⟩ : syracuseStep 559447 = 839171) B839171
theorem B559467 : Blo 558808 559467 := bstep (se 1 (by rfl) ⟨419600, by rfl⟩ : syracuseStep 559467 = 839201) B839201
theorem B559479 : Blo 558808 559479 := bstep (se 1 (by rfl) ⟨419609, by rfl⟩ : syracuseStep 559479 = 839219) B839219
theorem B559499 : Blo 558808 559499 := bstep (se 1 (by rfl) ⟨419624, by rfl⟩ : syracuseStep 559499 = 839249) B839249
theorem B1280395 : Blo 558808 1280395 := bstep (se 1 (by rfl) ⟨960296, by rfl⟩ : syracuseStep 1280395 = 1920593) B1920593
theorem B559511 : Blo 558808 559511 := bstep (se 1 (by rfl) ⟨419633, by rfl⟩ : syracuseStep 559511 = 839267) B839267
theorem B559531 : Blo 558808 559531 := bstep (se 1 (by rfl) ⟨419648, by rfl⟩ : syracuseStep 559531 = 839297) B839297
theorem B559543 : Blo 558808 559543 := bstep (se 1 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 559543 = 839315) B839315
theorem B559563 : Blo 558808 559563 := bstep (se 1 (by rfl) ⟨419672, by rfl⟩ : syracuseStep 559563 = 839345) B839345
theorem B559575 : Blo 558808 559575 := bstep (se 1 (by rfl) ⟨419681, by rfl⟩ : syracuseStep 559575 = 839363) B839363
theorem B559595 : Blo 558808 559595 := bstep (se 1 (by rfl) ⟨419696, by rfl⟩ : syracuseStep 559595 = 839393) B839393
theorem B559607 : Blo 558808 559607 := bstep (se 1 (by rfl) ⟨419705, by rfl⟩ : syracuseStep 559607 = 839411) B839411
theorem B559627 : Blo 558808 559627 := bstep (se 1 (by rfl) ⟨419720, by rfl⟩ : syracuseStep 559627 = 839441) B839441
theorem B559639 : Blo 558808 559639 := bstep (se 1 (by rfl) ⟨419729, by rfl⟩ : syracuseStep 559639 = 839459) B839459
theorem B559659 : Blo 558808 559659 := bstep (se 1 (by rfl) ⟨419744, by rfl⟩ : syracuseStep 559659 = 839489) B839489
theorem B559671 : Blo 558808 559671 := bstep (se 1 (by rfl) ⟨419753, by rfl⟩ : syracuseStep 559671 = 839507) B839507
theorem B559691 : Blo 558808 559691 := bstep (se 1 (by rfl) ⟨419768, by rfl⟩ : syracuseStep 559691 = 839537) B839537
theorem B559703 : Blo 558808 559703 := bstep (se 1 (by rfl) ⟨419777, by rfl⟩ : syracuseStep 559703 = 839555) B839555
theorem B559723 : Blo 558808 559723 := bstep (se 1 (by rfl) ⟨419792, by rfl⟩ : syracuseStep 559723 = 839585) B839585
theorem B559735 : Blo 558808 559735 := bstep (se 1 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 559735 = 839603) B839603
theorem B559755 : Blo 558808 559755 := bstep (se 1 (by rfl) ⟨419816, by rfl⟩ : syracuseStep 559755 = 839633) B839633
theorem B559767 : Blo 558808 559767 := bstep (se 1 (by rfl) ⟨419825, by rfl⟩ : syracuseStep 559767 = 839651) B839651
theorem B559787 : Blo 558808 559787 := bstep (se 1 (by rfl) ⟨419840, by rfl⟩ : syracuseStep 559787 = 839681) B839681
theorem B559799 : Blo 558808 559799 := bstep (se 1 (by rfl) ⟨419849, by rfl⟩ : syracuseStep 559799 = 839699) B839699
theorem B559819 : Blo 558808 559819 := bstep (se 1 (by rfl) ⟨419864, by rfl⟩ : syracuseStep 559819 = 839729) B839729
theorem B559831 : Blo 558808 559831 := bstep (se 1 (by rfl) ⟨419873, by rfl⟩ : syracuseStep 559831 = 839747) B839747
theorem B559851 : Blo 558808 559851 := bstep (se 1 (by rfl) ⟨419888, by rfl⟩ : syracuseStep 559851 = 839777) B839777
theorem B559863 : Blo 558808 559863 := bstep (se 1 (by rfl) ⟨419897, by rfl⟩ : syracuseStep 559863 = 839795) B839795
theorem B559883 : Blo 558808 559883 := bstep (se 1 (by rfl) ⟨419912, by rfl⟩ : syracuseStep 559883 = 839825) B839825
theorem B559895 : Blo 558808 559895 := bstep (se 1 (by rfl) ⟨419921, by rfl⟩ : syracuseStep 559895 = 839843) B839843
theorem B1346327 : Blo 558808 1346327 := bstep (se 1 (by rfl) ⟨1009745, by rfl⟩ : syracuseStep 1346327 = 2019491) B2019491
theorem B559915 : Blo 558808 559915 := bstep (se 1 (by rfl) ⟨419936, by rfl⟩ : syracuseStep 559915 = 839873) B839873
theorem B559927 : Blo 558808 559927 := bstep (se 1 (by rfl) ⟨419945, by rfl⟩ : syracuseStep 559927 = 839891) B839891
theorem B559947 : Blo 558808 559947 := bstep (se 1 (by rfl) ⟨419960, by rfl⟩ : syracuseStep 559947 = 839921) B839921
theorem B559959 : Blo 558808 559959 := bstep (se 1 (by rfl) ⟨419969, by rfl⟩ : syracuseStep 559959 = 839939) B839939
theorem B559979 : Blo 558808 559979 := bstep (se 1 (by rfl) ⟨419984, by rfl⟩ : syracuseStep 559979 = 839969) B839969
theorem B559991 : Blo 558808 559991 := bstep (se 1 (by rfl) ⟨419993, by rfl⟩ : syracuseStep 559991 = 839987) B839987
theorem B560011 : Blo 558808 560011 := bstep (se 1 (by rfl) ⟨420008, by rfl⟩ : syracuseStep 560011 = 840017) B840017
theorem B560023 : Blo 558808 560023 := bstep (se 1 (by rfl) ⟨420017, by rfl⟩ : syracuseStep 560023 = 840035) B840035
theorem B560043 : Blo 558808 560043 := bstep (se 1 (by rfl) ⟨420032, by rfl⟩ : syracuseStep 560043 = 840065) B840065
theorem B2558893 : Blo 558808 2558893 := bstep (se 3 (by rfl) ⟨479792, by rfl⟩ : syracuseStep 2558893 = 959585) B959585
theorem B560055 : Blo 558808 560055 := bstep (se 1 (by rfl) ⟨420041, by rfl⟩ : syracuseStep 560055 = 840083) B840083
theorem B560075 : Blo 558808 560075 := bstep (se 1 (by rfl) ⟨420056, by rfl⟩ : syracuseStep 560075 = 840113) B840113
theorem B560087 : Blo 558808 560087 := bstep (se 1 (by rfl) ⟨420065, by rfl⟩ : syracuseStep 560087 = 840131) B840131
theorem B560107 : Blo 558808 560107 := bstep (se 1 (by rfl) ⟨420080, by rfl⟩ : syracuseStep 560107 = 840161) B840161
theorem B560119 : Blo 558808 560119 := bstep (se 1 (by rfl) ⟨420089, by rfl⟩ : syracuseStep 560119 = 840179) B840179
theorem B560139 : Blo 558808 560139 := bstep (se 1 (by rfl) ⟨420104, by rfl⟩ : syracuseStep 560139 = 840209) B840209
theorem B560151 : Blo 558808 560151 := bstep (se 1 (by rfl) ⟨420113, by rfl⟩ : syracuseStep 560151 = 840227) B840227
theorem B560171 : Blo 558808 560171 := bstep (se 1 (by rfl) ⟨420128, by rfl⟩ : syracuseStep 560171 = 840257) B840257
theorem B560183 : Blo 558808 560183 := bstep (se 1 (by rfl) ⟨420137, by rfl⟩ : syracuseStep 560183 = 840275) B840275
theorem B2690113 : Blo 558808 2690113 := bstep (se 2 (by rfl) ⟨1008792, by rfl⟩ : syracuseStep 2690113 = 2017585) B2017585
theorem B560203 : Blo 558808 560203 := bstep (se 1 (by rfl) ⟨420152, by rfl⟩ : syracuseStep 560203 = 840305) B840305
theorem B560215 : Blo 558808 560215 := bstep (se 1 (by rfl) ⟨420161, by rfl⟩ : syracuseStep 560215 = 840323) B840323
theorem B560235 : Blo 558808 560235 := bstep (se 1 (by rfl) ⟨420176, by rfl⟩ : syracuseStep 560235 = 840353) B840353
theorem B560247 : Blo 558808 560247 := bstep (se 1 (by rfl) ⟨420185, by rfl⟩ : syracuseStep 560247 = 840371) B840371
theorem B560267 : Blo 558808 560267 := bstep (se 1 (by rfl) ⟨420200, by rfl⟩ : syracuseStep 560267 = 840401) B840401
theorem B560279 : Blo 558808 560279 := bstep (se 1 (by rfl) ⟨420209, by rfl⟩ : syracuseStep 560279 = 840419) B840419
theorem B560299 : Blo 558808 560299 := bstep (se 1 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 560299 = 840449) B840449
theorem B560311 : Blo 558808 560311 := bstep (se 1 (by rfl) ⟨420233, by rfl⟩ : syracuseStep 560311 = 840467) B840467
theorem B560331 : Blo 558808 560331 := bstep (se 1 (by rfl) ⟨420248, by rfl⟩ : syracuseStep 560331 = 840497) B840497
theorem B560343 : Blo 558808 560343 := bstep (se 1 (by rfl) ⟨420257, by rfl⟩ : syracuseStep 560343 = 840515) B840515
theorem B560363 : Blo 558808 560363 := bstep (se 1 (by rfl) ⟨420272, by rfl⟩ : syracuseStep 560363 = 840545) B840545
theorem B560375 : Blo 558808 560375 := bstep (se 1 (by rfl) ⟨420281, by rfl⟩ : syracuseStep 560375 = 840563) B840563
theorem B560395 : Blo 558808 560395 := bstep (se 1 (by rfl) ⟨420296, by rfl⟩ : syracuseStep 560395 = 840593) B840593
theorem B560407 : Blo 558808 560407 := bstep (se 1 (by rfl) ⟨420305, by rfl⟩ : syracuseStep 560407 = 840611) B840611
theorem B560427 : Blo 558808 560427 := bstep (se 1 (by rfl) ⟨420320, by rfl⟩ : syracuseStep 560427 = 840641) B840641
theorem B560439 : Blo 558808 560439 := bstep (se 1 (by rfl) ⟨420329, by rfl⟩ : syracuseStep 560439 = 840659) B840659
theorem B560459 : Blo 558808 560459 := bstep (se 1 (by rfl) ⟨420344, by rfl⟩ : syracuseStep 560459 = 840689) B840689
theorem B560471 : Blo 558808 560471 := bstep (se 1 (by rfl) ⟨420353, by rfl⟩ : syracuseStep 560471 = 840707) B840707
theorem B560491 : Blo 558808 560491 := bstep (se 1 (by rfl) ⟨420368, by rfl⟩ : syracuseStep 560491 = 840737) B840737
theorem B560503 : Blo 558808 560503 := bstep (se 1 (by rfl) ⟨420377, by rfl⟩ : syracuseStep 560503 = 840755) B840755
theorem B560523 : Blo 558808 560523 := bstep (se 1 (by rfl) ⟨420392, by rfl⟩ : syracuseStep 560523 = 840785) B840785
theorem B560535 : Blo 558808 560535 := bstep (se 1 (by rfl) ⟨420401, by rfl⟩ : syracuseStep 560535 = 840803) B840803
theorem B560555 : Blo 558808 560555 := bstep (se 1 (by rfl) ⟨420416, by rfl⟩ : syracuseStep 560555 = 840833) B840833
theorem B560567 : Blo 558808 560567 := bstep (se 1 (by rfl) ⟨420425, by rfl⟩ : syracuseStep 560567 = 840851) B840851
theorem B2395585 : Blo 558808 2395585 := bstep (se 2 (by rfl) ⟨898344, by rfl⟩ : syracuseStep 2395585 = 1796689) B1796689
theorem B560587 : Blo 558808 560587 := bstep (se 1 (by rfl) ⟨420440, by rfl⟩ : syracuseStep 560587 = 840881) B840881
theorem B560599 : Blo 558808 560599 := bstep (se 1 (by rfl) ⟨420449, by rfl⟩ : syracuseStep 560599 = 840899) B840899
theorem B560619 : Blo 558808 560619 := bstep (se 1 (by rfl) ⟨420464, by rfl⟩ : syracuseStep 560619 = 840929) B840929
theorem B560631 : Blo 558808 560631 := bstep (se 1 (by rfl) ⟨420473, by rfl⟩ : syracuseStep 560631 = 840947) B840947
theorem B560651 : Blo 558808 560651 := bstep (se 1 (by rfl) ⟨420488, by rfl⟩ : syracuseStep 560651 = 840977) B840977
theorem B560663 : Blo 558808 560663 := bstep (se 1 (by rfl) ⟨420497, by rfl⟩ : syracuseStep 560663 = 840995) B840995
theorem B560683 : Blo 558808 560683 := bstep (se 1 (by rfl) ⟨420512, by rfl⟩ : syracuseStep 560683 = 841025) B841025
theorem B560695 : Blo 558808 560695 := bstep (se 1 (by rfl) ⟨420521, by rfl⟩ : syracuseStep 560695 = 841043) B841043
theorem B2428481 : Blo 558808 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B560715 : Blo 558808 560715 := bstep (se 1 (by rfl) ⟨420536, by rfl⟩ : syracuseStep 560715 = 841073) B841073
theorem B560727 : Blo 558808 560727 := bstep (se 1 (by rfl) ⟨420545, by rfl⟩ : syracuseStep 560727 = 841091) B841091
theorem B560747 : Blo 558808 560747 := bstep (se 1 (by rfl) ⟨420560, by rfl⟩ : syracuseStep 560747 = 841121) B841121
theorem B560759 : Blo 558808 560759 := bstep (se 1 (by rfl) ⟨420569, by rfl⟩ : syracuseStep 560759 = 841139) B841139
theorem B560779 : Blo 558808 560779 := bstep (se 1 (by rfl) ⟨420584, by rfl⟩ : syracuseStep 560779 = 841169) B841169
theorem B560791 : Blo 558808 560791 := bstep (se 1 (by rfl) ⟨420593, by rfl⟩ : syracuseStep 560791 = 841187) B841187
theorem B560811 : Blo 558808 560811 := bstep (se 1 (by rfl) ⟨420608, by rfl⟩ : syracuseStep 560811 = 841217) B841217
theorem B560823 : Blo 558808 560823 := bstep (se 1 (by rfl) ⟨420617, by rfl⟩ : syracuseStep 560823 = 841235) B841235
theorem B560843 : Blo 558808 560843 := bstep (se 1 (by rfl) ⟨420632, by rfl⟩ : syracuseStep 560843 = 841265) B841265
theorem B560855 : Blo 558808 560855 := bstep (se 1 (by rfl) ⟨420641, by rfl⟩ : syracuseStep 560855 = 841283) B841283
theorem B560875 : Blo 558808 560875 := bstep (se 1 (by rfl) ⟨420656, by rfl⟩ : syracuseStep 560875 = 841313) B841313
theorem B560887 : Blo 558808 560887 := bstep (se 1 (by rfl) ⟨420665, by rfl⟩ : syracuseStep 560887 = 841331) B841331
theorem B560907 : Blo 558808 560907 := bstep (se 1 (by rfl) ⟨420680, by rfl⟩ : syracuseStep 560907 = 841361) B841361
theorem B560919 : Blo 558808 560919 := bstep (se 1 (by rfl) ⟨420689, by rfl⟩ : syracuseStep 560919 = 841379) B841379
theorem B560939 : Blo 558808 560939 := bstep (se 1 (by rfl) ⟨420704, by rfl⟩ : syracuseStep 560939 = 841409) B841409
theorem B560951 : Blo 558808 560951 := bstep (se 1 (by rfl) ⟨420713, by rfl⟩ : syracuseStep 560951 = 841427) B841427
theorem B560971 : Blo 558808 560971 := bstep (se 1 (by rfl) ⟨420728, by rfl⟩ : syracuseStep 560971 = 841457) B841457
theorem B560983 : Blo 558808 560983 := bstep (se 1 (by rfl) ⟨420737, by rfl⟩ : syracuseStep 560983 = 841475) B841475
theorem B30609251 : Blo 558808 30609251 := bstep (se 1 (by rfl) ⟨22956938, by rfl⟩ : syracuseStep 30609251 = 45913877) B45913877
theorem B561003 : Blo 558808 561003 := bstep (se 1 (by rfl) ⟨420752, by rfl⟩ : syracuseStep 561003 = 841505) B841505
theorem B561015 : Blo 558808 561015 := bstep (se 1 (by rfl) ⟨420761, by rfl⟩ : syracuseStep 561015 = 841523) B841523
theorem B561035 : Blo 558808 561035 := bstep (se 1 (by rfl) ⟨420776, by rfl⟩ : syracuseStep 561035 = 841553) B841553
theorem B561047 : Blo 558808 561047 := bstep (se 1 (by rfl) ⟨420785, by rfl⟩ : syracuseStep 561047 = 841571) B841571
theorem B561067 : Blo 558808 561067 := bstep (se 1 (by rfl) ⟨420800, by rfl⟩ : syracuseStep 561067 = 841601) B841601
theorem B561079 : Blo 558808 561079 := bstep (se 1 (by rfl) ⟨420809, by rfl⟩ : syracuseStep 561079 = 841619) B841619
theorem B561099 : Blo 558808 561099 := bstep (se 1 (by rfl) ⟨420824, by rfl⟩ : syracuseStep 561099 = 841649) B841649
theorem B561111 : Blo 558808 561111 := bstep (se 1 (by rfl) ⟨420833, by rfl⟩ : syracuseStep 561111 = 841667) B841667
theorem B561131 : Blo 558808 561131 := bstep (se 1 (by rfl) ⟨420848, by rfl⟩ : syracuseStep 561131 = 841697) B841697
theorem B561143 : Blo 558808 561143 := bstep (se 1 (by rfl) ⟨420857, by rfl⟩ : syracuseStep 561143 = 841715) B841715
theorem B561163 : Blo 558808 561163 := bstep (se 1 (by rfl) ⟨420872, by rfl⟩ : syracuseStep 561163 = 841745) B841745
theorem B561175 : Blo 558808 561175 := bstep (se 1 (by rfl) ⟨420881, by rfl⟩ : syracuseStep 561175 = 841763) B841763
theorem B561195 : Blo 558808 561195 := bstep (se 1 (by rfl) ⟨420896, by rfl⟩ : syracuseStep 561195 = 841793) B841793
theorem B561207 : Blo 558808 561207 := bstep (se 1 (by rfl) ⟨420905, by rfl⟩ : syracuseStep 561207 = 841811) B841811
theorem B6066251 : Blo 558808 6066251 := bstep (se 1 (by rfl) ⟨4549688, by rfl⟩ : syracuseStep 6066251 = 9099377) B9099377
theorem B561227 : Blo 558808 561227 := bstep (se 1 (by rfl) ⟨420920, by rfl⟩ : syracuseStep 561227 = 841841) B841841
theorem B561239 : Blo 558808 561239 := bstep (se 1 (by rfl) ⟨420929, by rfl⟩ : syracuseStep 561239 = 841859) B841859
theorem B561259 : Blo 558808 561259 := bstep (se 1 (by rfl) ⟨420944, by rfl⟩ : syracuseStep 561259 = 841889) B841889
theorem B561271 : Blo 558808 561271 := bstep (se 1 (by rfl) ⟨420953, by rfl⟩ : syracuseStep 561271 = 841907) B841907
theorem B3182723 : Blo 558808 3182723 := bstep (se 1 (by rfl) ⟨2387042, by rfl⟩ : syracuseStep 3182723 = 4774085) B4774085
theorem B2134147 : Blo 558808 2134147 := bstep (se 1 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 2134147 = 3201221) B3201221
theorem B561291 : Blo 558808 561291 := bstep (se 1 (by rfl) ⟨420968, by rfl⟩ : syracuseStep 561291 = 841937) B841937
theorem B561303 : Blo 558808 561303 := bstep (se 1 (by rfl) ⟨420977, by rfl⟩ : syracuseStep 561303 = 841955) B841955
theorem B4558999 : Blo 558808 4558999 := bstep (se 1 (by rfl) ⟨3419249, by rfl⟩ : syracuseStep 4558999 = 6838499) B6838499
theorem B561323 : Blo 558808 561323 := bstep (se 1 (by rfl) ⟨420992, by rfl⟩ : syracuseStep 561323 = 841985) B841985
theorem B561335 : Blo 558808 561335 := bstep (se 1 (by rfl) ⟨421001, by rfl⟩ : syracuseStep 561335 = 842003) B842003
theorem B561355 : Blo 558808 561355 := bstep (se 1 (by rfl) ⟨421016, by rfl⟩ : syracuseStep 561355 = 842033) B842033
theorem B561367 : Blo 558808 561367 := bstep (se 1 (by rfl) ⟨421025, by rfl⟩ : syracuseStep 561367 = 842051) B842051
theorem B1708249 : Blo 558808 1708249 := bstep (se 2 (by rfl) ⟨640593, by rfl⟩ : syracuseStep 1708249 = 1281187) B1281187
theorem B561387 : Blo 558808 561387 := bstep (se 1 (by rfl) ⟨421040, by rfl⟩ : syracuseStep 561387 = 842081) B842081
theorem B561399 : Blo 558808 561399 := bstep (se 1 (by rfl) ⟨421049, by rfl⟩ : syracuseStep 561399 = 842099) B842099
theorem B561419 : Blo 558808 561419 := bstep (se 1 (by rfl) ⟨421064, by rfl⟩ : syracuseStep 561419 = 842129) B842129
theorem B561431 : Blo 558808 561431 := bstep (se 1 (by rfl) ⟨421073, by rfl⟩ : syracuseStep 561431 = 842147) B842147
theorem B561451 : Blo 558808 561451 := bstep (se 1 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 561451 = 842177) B842177
theorem B561463 : Blo 558808 561463 := bstep (se 1 (by rfl) ⟨421097, by rfl⟩ : syracuseStep 561463 = 842195) B842195
theorem B561483 : Blo 558808 561483 := bstep (se 1 (by rfl) ⟨421112, by rfl⟩ : syracuseStep 561483 = 842225) B842225
theorem B561495 : Blo 558808 561495 := bstep (se 1 (by rfl) ⟨421121, by rfl⟩ : syracuseStep 561495 = 842243) B842243
theorem B561515 : Blo 558808 561515 := bstep (se 1 (by rfl) ⟨421136, by rfl⟩ : syracuseStep 561515 = 842273) B842273
theorem B561527 : Blo 558808 561527 := bstep (se 1 (by rfl) ⟨421145, by rfl⟩ : syracuseStep 561527 = 842291) B842291
theorem B561547 : Blo 558808 561547 := bstep (se 1 (by rfl) ⟨421160, by rfl⟩ : syracuseStep 561547 = 842321) B842321
theorem B561559 : Blo 558808 561559 := bstep (se 1 (by rfl) ⟨421169, by rfl⟩ : syracuseStep 561559 = 842339) B842339
theorem B561579 : Blo 558808 561579 := bstep (se 1 (by rfl) ⟨421184, by rfl⟩ : syracuseStep 561579 = 842369) B842369
theorem B2134451 : Blo 558808 2134451 := bstep (se 1 (by rfl) ⟨1600838, by rfl⟩ : syracuseStep 2134451 = 3201677) B3201677
theorem B561591 : Blo 558808 561591 := bstep (se 1 (by rfl) ⟨421193, by rfl⟩ : syracuseStep 561591 = 842387) B842387
theorem B561611 : Blo 558808 561611 := bstep (se 1 (by rfl) ⟨421208, by rfl⟩ : syracuseStep 561611 = 842417) B842417
theorem B561623 : Blo 558808 561623 := bstep (se 1 (by rfl) ⟨421217, by rfl⟩ : syracuseStep 561623 = 842435) B842435
theorem B561643 : Blo 558808 561643 := bstep (se 1 (by rfl) ⟨421232, by rfl⟩ : syracuseStep 561643 = 842465) B842465
theorem B561655 : Blo 558808 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B561675 : Blo 558808 561675 := bstep (se 1 (by rfl) ⟨421256, by rfl⟩ : syracuseStep 561675 = 842513) B842513
theorem B21533201 : Blo 558808 21533201 := bstep (se 2 (by rfl) ⟨8074950, by rfl⟩ : syracuseStep 21533201 = 16149901) B16149901
theorem B561687 : Blo 558808 561687 := bstep (se 1 (by rfl) ⟨421265, by rfl⟩ : syracuseStep 561687 = 842531) B842531
theorem B561707 : Blo 558808 561707 := bstep (se 1 (by rfl) ⟨421280, by rfl⟩ : syracuseStep 561707 = 842561) B842561
theorem B561719 : Blo 558808 561719 := bstep (se 1 (by rfl) ⟨421289, by rfl⟩ : syracuseStep 561719 = 842579) B842579
theorem B561739 : Blo 558808 561739 := bstep (se 1 (by rfl) ⟨421304, by rfl⟩ : syracuseStep 561739 = 842609) B842609
theorem B561751 : Blo 558808 561751 := bstep (se 1 (by rfl) ⟨421313, by rfl⟩ : syracuseStep 561751 = 842627) B842627
theorem B561771 : Blo 558808 561771 := bstep (se 1 (by rfl) ⟨421328, by rfl⟩ : syracuseStep 561771 = 842657) B842657
theorem B561783 : Blo 558808 561783 := bstep (se 1 (by rfl) ⟨421337, by rfl⟩ : syracuseStep 561783 = 842675) B842675
theorem B561803 : Blo 558808 561803 := bstep (se 1 (by rfl) ⟨421352, by rfl⟩ : syracuseStep 561803 = 842705) B842705
theorem B561815 : Blo 558808 561815 := bstep (se 1 (by rfl) ⟨421361, by rfl⟩ : syracuseStep 561815 = 842723) B842723
theorem B561835 : Blo 558808 561835 := bstep (se 1 (by rfl) ⟨421376, by rfl⟩ : syracuseStep 561835 = 842753) B842753
theorem B8622773 : Blo 558808 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B561847 : Blo 558808 561847 := bstep (se 1 (by rfl) ⟨421385, by rfl⟩ : syracuseStep 561847 = 842771) B842771
theorem B561867 : Blo 558808 561867 := bstep (se 1 (by rfl) ⟨421400, by rfl⟩ : syracuseStep 561867 = 842801) B842801
theorem B561879 : Blo 558808 561879 := bstep (se 1 (by rfl) ⟨421409, by rfl⟩ : syracuseStep 561879 = 842819) B842819
theorem B561899 : Blo 558808 561899 := bstep (se 1 (by rfl) ⟨421424, by rfl⟩ : syracuseStep 561899 = 842849) B842849
theorem B561911 : Blo 558808 561911 := bstep (se 1 (by rfl) ⟨421433, by rfl⟩ : syracuseStep 561911 = 842867) B842867
theorem B561931 : Blo 558808 561931 := bstep (se 1 (by rfl) ⟨421448, by rfl⟩ : syracuseStep 561931 = 842897) B842897
theorem B561943 : Blo 558808 561943 := bstep (se 1 (by rfl) ⟨421457, by rfl⟩ : syracuseStep 561943 = 842915) B842915
theorem B561963 : Blo 558808 561963 := bstep (se 1 (by rfl) ⟨421472, by rfl⟩ : syracuseStep 561963 = 842945) B842945
theorem B561975 : Blo 558808 561975 := bstep (se 1 (by rfl) ⟨421481, by rfl⟩ : syracuseStep 561975 = 842963) B842963
theorem B561995 : Blo 558808 561995 := bstep (se 1 (by rfl) ⟨421496, by rfl⟩ : syracuseStep 561995 = 842993) B842993
theorem B562007 : Blo 558808 562007 := bstep (se 1 (by rfl) ⟨421505, by rfl⟩ : syracuseStep 562007 = 843011) B843011
theorem B562027 : Blo 558808 562027 := bstep (se 1 (by rfl) ⟨421520, by rfl⟩ : syracuseStep 562027 = 843041) B843041
theorem B562039 : Blo 558808 562039 := bstep (se 1 (by rfl) ⟨421529, by rfl⟩ : syracuseStep 562039 = 843059) B843059
theorem B562059 : Blo 558808 562059 := bstep (se 1 (by rfl) ⟨421544, by rfl⟩ : syracuseStep 562059 = 843089) B843089
theorem B2397073 : Blo 558808 2397073 := bstep (se 2 (by rfl) ⟨898902, by rfl⟩ : syracuseStep 2397073 = 1797805) B1797805
theorem B562071 : Blo 558808 562071 := bstep (se 1 (by rfl) ⟨421553, by rfl⟩ : syracuseStep 562071 = 843107) B843107
theorem B562091 : Blo 558808 562091 := bstep (se 1 (by rfl) ⟨421568, by rfl⟩ : syracuseStep 562091 = 843137) B843137
theorem B562103 : Blo 558808 562103 := bstep (se 1 (by rfl) ⟨421577, by rfl⟩ : syracuseStep 562103 = 843155) B843155
theorem B562123 : Blo 558808 562123 := bstep (se 1 (by rfl) ⟨421592, by rfl⟩ : syracuseStep 562123 = 843185) B843185
theorem B562135 : Blo 558808 562135 := bstep (se 1 (by rfl) ⟨421601, by rfl⟩ : syracuseStep 562135 = 843203) B843203
theorem B562155 : Blo 558808 562155 := bstep (se 1 (by rfl) ⟨421616, by rfl⟩ : syracuseStep 562155 = 843233) B843233
theorem B562167 : Blo 558808 562167 := bstep (se 1 (by rfl) ⟨421625, by rfl⟩ : syracuseStep 562167 = 843251) B843251
theorem B562187 : Blo 558808 562187 := bstep (se 1 (by rfl) ⟨421640, by rfl⟩ : syracuseStep 562187 = 843281) B843281
theorem B562199 : Blo 558808 562199 := bstep (se 1 (by rfl) ⟨421649, by rfl⟩ : syracuseStep 562199 = 843299) B843299
theorem B562219 : Blo 558808 562219 := bstep (se 1 (by rfl) ⟨421664, by rfl⟩ : syracuseStep 562219 = 843329) B843329
theorem B562231 : Blo 558808 562231 := bstep (se 1 (by rfl) ⟨421673, by rfl⟩ : syracuseStep 562231 = 843347) B843347
theorem B2135105 : Blo 558808 2135105 := bstep (se 2 (by rfl) ⟨800664, by rfl⟩ : syracuseStep 2135105 = 1601329) B1601329
theorem B562251 : Blo 558808 562251 := bstep (se 1 (by rfl) ⟨421688, by rfl⟩ : syracuseStep 562251 = 843377) B843377
theorem B562263 : Blo 558808 562263 := bstep (se 1 (by rfl) ⟨421697, by rfl⟩ : syracuseStep 562263 = 843395) B843395
theorem B562283 : Blo 558808 562283 := bstep (se 1 (by rfl) ⟨421712, by rfl⟩ : syracuseStep 562283 = 843425) B843425
theorem B562295 : Blo 558808 562295 := bstep (se 1 (by rfl) ⟨421721, by rfl⟩ : syracuseStep 562295 = 843443) B843443
theorem B562315 : Blo 558808 562315 := bstep (se 1 (by rfl) ⟨421736, by rfl⟩ : syracuseStep 562315 = 843473) B843473
theorem B562327 : Blo 558808 562327 := bstep (se 1 (by rfl) ⟨421745, by rfl⟩ : syracuseStep 562327 = 843491) B843491
theorem B562347 : Blo 558808 562347 := bstep (se 1 (by rfl) ⟨421760, by rfl⟩ : syracuseStep 562347 = 843521) B843521
theorem B1348787 : Blo 558808 1348787 := bstep (se 1 (by rfl) ⟨1011590, by rfl⟩ : syracuseStep 1348787 = 2023181) B2023181
theorem B562359 : Blo 558808 562359 := bstep (se 1 (by rfl) ⟨421769, by rfl⟩ : syracuseStep 562359 = 843539) B843539
theorem B562379 : Blo 558808 562379 := bstep (se 1 (by rfl) ⟨421784, by rfl⟩ : syracuseStep 562379 = 843569) B843569
theorem B562391 : Blo 558808 562391 := bstep (se 1 (by rfl) ⟨421793, by rfl⟩ : syracuseStep 562391 = 843587) B843587
theorem B1348825 : Blo 558808 1348825 := bstep (se 2 (by rfl) ⟨505809, by rfl⟩ : syracuseStep 1348825 = 1011619) B1011619
theorem B562411 : Blo 558808 562411 := bstep (se 1 (by rfl) ⟨421808, by rfl⟩ : syracuseStep 562411 = 843617) B843617
theorem B562423 : Blo 558808 562423 := bstep (se 1 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 562423 = 843635) B843635
theorem B562443 : Blo 558808 562443 := bstep (se 1 (by rfl) ⟨421832, by rfl⟩ : syracuseStep 562443 = 843665) B843665
theorem B562455 : Blo 558808 562455 := bstep (se 1 (by rfl) ⟨421841, by rfl⟩ : syracuseStep 562455 = 843683) B843683
theorem B562475 : Blo 558808 562475 := bstep (se 1 (by rfl) ⟨421856, by rfl⟩ : syracuseStep 562475 = 843713) B843713
theorem B562487 : Blo 558808 562487 := bstep (se 1 (by rfl) ⟨421865, by rfl⟩ : syracuseStep 562487 = 843731) B843731
theorem B562507 : Blo 558808 562507 := bstep (se 1 (by rfl) ⟨421880, by rfl⟩ : syracuseStep 562507 = 843761) B843761
theorem B562519 : Blo 558808 562519 := bstep (se 1 (by rfl) ⟨421889, by rfl⟩ : syracuseStep 562519 = 843779) B843779
theorem B4330853 : Blo 558808 4330853 := bstep (se 4 (by rfl) ⟨406017, by rfl⟩ : syracuseStep 4330853 = 812035) B812035
theorem B562539 : Blo 558808 562539 := bstep (se 1 (by rfl) ⟨421904, by rfl⟩ : syracuseStep 562539 = 843809) B843809
theorem B562551 : Blo 558808 562551 := bstep (se 1 (by rfl) ⟨421913, by rfl⟩ : syracuseStep 562551 = 843827) B843827
theorem B562571 : Blo 558808 562571 := bstep (se 1 (by rfl) ⟨421928, by rfl⟩ : syracuseStep 562571 = 843857) B843857
theorem B562583 : Blo 558808 562583 := bstep (se 1 (by rfl) ⟨421937, by rfl⟩ : syracuseStep 562583 = 843875) B843875
theorem B562603 : Blo 558808 562603 := bstep (se 1 (by rfl) ⟨421952, by rfl⟩ : syracuseStep 562603 = 843905) B843905
theorem B562615 : Blo 558808 562615 := bstep (se 1 (by rfl) ⟨421961, by rfl⟩ : syracuseStep 562615 = 843923) B843923
theorem B562635 : Blo 558808 562635 := bstep (se 1 (by rfl) ⟨421976, by rfl⟩ : syracuseStep 562635 = 843953) B843953
theorem B562647 : Blo 558808 562647 := bstep (se 1 (by rfl) ⟨421985, by rfl⟩ : syracuseStep 562647 = 843971) B843971
theorem B562667 : Blo 558808 562667 := bstep (se 1 (by rfl) ⟨422000, by rfl⟩ : syracuseStep 562667 = 844001) B844001
theorem B562679 : Blo 558808 562679 := bstep (se 1 (by rfl) ⟨422009, by rfl⟩ : syracuseStep 562679 = 844019) B844019
theorem B4855301 : Blo 558808 4855301 := bstep (se 4 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 4855301 = 910369) B910369
theorem B562699 : Blo 558808 562699 := bstep (se 1 (by rfl) ⟨422024, by rfl⟩ : syracuseStep 562699 = 844049) B844049
theorem B562711 : Blo 558808 562711 := bstep (se 1 (by rfl) ⟨422033, by rfl⟩ : syracuseStep 562711 = 844067) B844067
theorem B562731 : Blo 558808 562731 := bstep (se 1 (by rfl) ⟨422048, by rfl⟩ : syracuseStep 562731 = 844097) B844097
theorem B562743 : Blo 558808 562743 := bstep (se 1 (by rfl) ⟨422057, by rfl⟩ : syracuseStep 562743 = 844115) B844115
theorem B562763 : Blo 558808 562763 := bstep (se 1 (by rfl) ⟨422072, by rfl⟩ : syracuseStep 562763 = 844145) B844145
theorem B562775 : Blo 558808 562775 := bstep (se 1 (by rfl) ⟨422081, by rfl⟩ : syracuseStep 562775 = 844163) B844163
theorem B759385 : Blo 558808 759385 := bstep (se 2 (by rfl) ⟨284769, by rfl⟩ : syracuseStep 759385 = 569539) B569539
theorem B562795 : Blo 558808 562795 := bstep (se 1 (by rfl) ⟨422096, by rfl⟩ : syracuseStep 562795 = 844193) B844193
theorem B562807 : Blo 558808 562807 := bstep (se 1 (by rfl) ⟨422105, by rfl⟩ : syracuseStep 562807 = 844211) B844211
theorem B4560715 : Blo 558808 4560715 := bstep (se 1 (by rfl) ⟨3420536, by rfl⟩ : syracuseStep 4560715 = 6841073) B6841073
theorem B628663 : Blo 558808 628663 := bstep (se 1 (by rfl) ⟨471497, by rfl⟩ : syracuseStep 628663 = 942995) B942995
theorem B1415191 : Blo 558808 1415191 := bstep (se 1 (by rfl) ⟨1061393, by rfl⟩ : syracuseStep 1415191 = 2122787) B2122787
theorem B628843 : Blo 558808 628843 := bstep (se 1 (by rfl) ⟨471632, by rfl⟩ : syracuseStep 628843 = 943265) B943265
theorem B628951 : Blo 558808 628951 := bstep (se 1 (by rfl) ⟨471713, by rfl⟩ : syracuseStep 628951 = 943427) B943427
theorem B2136365 : Blo 558808 2136365 := bstep (se 3 (by rfl) ⟨400568, by rfl⟩ : syracuseStep 2136365 = 801137) B801137
theorem B2136395 : Blo 558808 2136395 := bstep (se 1 (by rfl) ⟨1602296, by rfl⟩ : syracuseStep 2136395 = 3204593) B3204593
theorem B3021187 : Blo 558808 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B629131 : Blo 558808 629131 := bstep (se 1 (by rfl) ⟨471848, by rfl⟩ : syracuseStep 629131 = 943697) B943697
theorem B4037015 : Blo 558808 4037015 := bstep (se 1 (by rfl) ⟨3027761, by rfl⟩ : syracuseStep 4037015 = 6055523) B6055523
theorem B1415627 : Blo 558808 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B629239 : Blo 558808 629239 := bstep (se 1 (by rfl) ⟨471929, by rfl⟩ : syracuseStep 629239 = 943859) B943859
theorem B1350209 : Blo 558808 1350209 := bstep (se 2 (by rfl) ⟨506328, by rfl⟩ : syracuseStep 1350209 = 1012657) B1012657
theorem B629419 : Blo 558808 629419 := bstep (se 1 (by rfl) ⟨472064, by rfl⟩ : syracuseStep 629419 = 944129) B944129
theorem B8100557 : Blo 558808 8100557 := bstep (se 3 (by rfl) ⟨1518854, by rfl⟩ : syracuseStep 8100557 = 3037709) B3037709
theorem B4922117 : Blo 558808 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B629527 : Blo 558808 629527 := bstep (se 1 (by rfl) ⟨472145, by rfl⟩ : syracuseStep 629527 = 944291) B944291
theorem B1416001 : Blo 558808 1416001 := bstep (se 2 (by rfl) ⟨531000, by rfl⟩ : syracuseStep 1416001 = 1062001) B1062001
theorem B2595673 : Blo 558808 2595673 := bstep (se 2 (by rfl) ⟨973377, by rfl⟩ : syracuseStep 2595673 = 1946755) B1946755
theorem B596855 : Blo 558808 596855 := bstep (se 1 (by rfl) ⟨447641, by rfl⟩ : syracuseStep 596855 = 895283) B895283
theorem B8100785 : Blo 558808 8100785 := bstep (se 2 (by rfl) ⟨3037794, by rfl⟩ : syracuseStep 8100785 = 6075589) B6075589
theorem B629707 : Blo 558808 629707 := bstep (se 1 (by rfl) ⟨472280, by rfl⟩ : syracuseStep 629707 = 944561) B944561
theorem B629815 : Blo 558808 629815 := bstep (se 1 (by rfl) ⟨472361, by rfl⟩ : syracuseStep 629815 = 944723) B944723
theorem B2464913 : Blo 558808 2464913 := bstep (se 2 (by rfl) ⟨924342, by rfl⟩ : syracuseStep 2464913 = 1848685) B1848685
theorem B629995 : Blo 558808 629995 := bstep (se 1 (by rfl) ⟨472496, by rfl⟩ : syracuseStep 629995 = 944993) B944993
theorem B630103 : Blo 558808 630103 := bstep (se 1 (by rfl) ⟨472577, by rfl⟩ : syracuseStep 630103 = 945155) B945155
theorem B1416599 : Blo 558808 1416599 := bstep (se 1 (by rfl) ⟨1062449, by rfl⟩ : syracuseStep 1416599 = 2124899) B2124899
theorem B2432429 : Blo 558808 2432429 := bstep (se 3 (by rfl) ⟨456080, by rfl⟩ : syracuseStep 2432429 = 912161) B912161
theorem B630283 : Blo 558808 630283 := bstep (se 1 (by rfl) ⟨472712, by rfl⟩ : syracuseStep 630283 = 945425) B945425
theorem B597547 : Blo 558808 597547 := bstep (se 1 (by rfl) ⟨448160, by rfl⟩ : syracuseStep 597547 = 896321) B896321
theorem B4267565 : Blo 558808 4267565 := bstep (se 3 (by rfl) ⟨800168, by rfl⟩ : syracuseStep 4267565 = 1600337) B1600337
theorem B630391 : Blo 558808 630391 := bstep (se 1 (by rfl) ⟨472793, by rfl⟩ : syracuseStep 630391 = 945587) B945587
theorem B4791959 : Blo 558808 4791959 := bstep (se 1 (by rfl) ⟨3593969, by rfl⟩ : syracuseStep 4791959 = 7187939) B7187939
theorem B1351361 : Blo 558808 1351361 := bstep (se 2 (by rfl) ⟨506760, by rfl⟩ : syracuseStep 1351361 = 1013521) B1013521
theorem B958169 : Blo 558808 958169 := bstep (se 2 (by rfl) ⟨359313, by rfl⟩ : syracuseStep 958169 = 718627) B718627
theorem B630571 : Blo 558808 630571 := bstep (se 1 (by rfl) ⟨472928, by rfl⟩ : syracuseStep 630571 = 945857) B945857
theorem B2727755 : Blo 558808 2727755 := bstep (se 1 (by rfl) ⟨2045816, by rfl⟩ : syracuseStep 2727755 = 4091633) B4091633
theorem B2400131 : Blo 558808 2400131 := bstep (se 1 (by rfl) ⟨1800098, by rfl⟩ : syracuseStep 2400131 = 3600197) B3600197
theorem B630679 : Blo 558808 630679 := bstep (se 1 (by rfl) ⟨473009, by rfl⟩ : syracuseStep 630679 = 946019) B946019
theorem B4038605 : Blo 558808 4038605 := bstep (se 3 (by rfl) ⟨757238, by rfl⟩ : syracuseStep 4038605 = 1514477) B1514477
theorem B630859 : Blo 558808 630859 := bstep (se 1 (by rfl) ⟨473144, by rfl⟩ : syracuseStep 630859 = 946289) B946289
theorem B630967 : Blo 558808 630967 := bstep (se 1 (by rfl) ⟨473225, by rfl⟩ : syracuseStep 630967 = 946451) B946451
theorem B1417409 : Blo 558808 1417409 := bstep (se 2 (by rfl) ⟨531528, by rfl⟩ : syracuseStep 1417409 = 1063057) B1063057
theorem B631147 : Blo 558808 631147 := bstep (se 1 (by rfl) ⟨473360, by rfl⟩ : syracuseStep 631147 = 946721) B946721
theorem B2564531 : Blo 558808 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B631255 : Blo 558808 631255 := bstep (se 1 (by rfl) ⟨473441, by rfl⟩ : syracuseStep 631255 = 946883) B946883
theorem B631435 : Blo 558808 631435 := bstep (se 1 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 631435 = 947153) B947153
theorem B1417945 : Blo 558808 1417945 := bstep (se 2 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 1417945 = 1063459) B1063459
theorem B631543 : Blo 558808 631543 := bstep (se 1 (by rfl) ⟨473657, by rfl⟩ : syracuseStep 631543 = 947315) B947315
theorem B598871 : Blo 558808 598871 := bstep (se 1 (by rfl) ⟨449153, by rfl⟩ : syracuseStep 598871 = 898307) B898307
theorem B631723 : Blo 558808 631723 := bstep (se 1 (by rfl) ⟨473792, by rfl⟩ : syracuseStep 631723 = 947585) B947585
theorem B598999 : Blo 558808 598999 := bstep (se 1 (by rfl) ⟨449249, by rfl⟩ : syracuseStep 598999 = 898499) B898499
theorem B631831 : Blo 558808 631831 := bstep (se 1 (by rfl) ⟨473873, by rfl⟩ : syracuseStep 631831 = 947747) B947747
theorem B3646565 : Blo 558808 3646565 := bstep (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) B683731
theorem B2270339 : Blo 558808 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B632011 : Blo 558808 632011 := bstep (se 1 (by rfl) ⟨474008, by rfl⟩ : syracuseStep 632011 = 948017) B948017
theorem B795863 : Blo 558808 795863 := bstep (se 1 (by rfl) ⟨596897, by rfl⟩ : syracuseStep 795863 = 1193795) B1193795
theorem B632119 : Blo 558808 632119 := bstep (se 1 (by rfl) ⟨474089, by rfl⟩ : syracuseStep 632119 = 948179) B948179
theorem B3188099 : Blo 558808 3188099 := bstep (se 1 (by rfl) ⟨2391074, by rfl⟩ : syracuseStep 3188099 = 4782149) B4782149
theorem B632299 : Blo 558808 632299 := bstep (se 1 (by rfl) ⟨474224, by rfl⟩ : syracuseStep 632299 = 948449) B948449
theorem B796171 : Blo 558808 796171 := bstep (se 1 (by rfl) ⟨597128, by rfl⟩ : syracuseStep 796171 = 1194257) B1194257
theorem B599563 : Blo 558808 599563 := bstep (se 1 (by rfl) ⟨449672, by rfl⟩ : syracuseStep 599563 = 899345) B899345
theorem B632407 : Blo 558808 632407 := bstep (se 1 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 632407 = 948611) B948611
theorem B566903 : Blo 558808 566903 := bstep (se 1 (by rfl) ⟨425177, by rfl⟩ : syracuseStep 566903 = 850355) B850355
theorem B2696921 : Blo 558808 2696921 := bstep (se 2 (by rfl) ⟨1011345, by rfl⟩ : syracuseStep 2696921 = 2022691) B2022691
theorem B599819 : Blo 558808 599819 := bstep (se 1 (by rfl) ⟨449864, by rfl⟩ : syracuseStep 599819 = 899729) B899729
theorem B632587 : Blo 558808 632587 := bstep (se 1 (by rfl) ⟨474440, by rfl⟩ : syracuseStep 632587 = 948881) B948881
theorem B1419059 : Blo 558808 1419059 := bstep (se 1 (by rfl) ⟨1064294, by rfl⟩ : syracuseStep 1419059 = 2128589) B2128589
theorem B3188555 : Blo 558808 3188555 := bstep (se 1 (by rfl) ⟨2391416, by rfl⟩ : syracuseStep 3188555 = 4782833) B4782833
theorem B632695 : Blo 558808 632695 := bstep (se 1 (by rfl) ⟨474521, by rfl⟩ : syracuseStep 632695 = 949043) B949043
theorem B2467757 : Blo 558808 2467757 := bstep (se 3 (by rfl) ⟨462704, by rfl⟩ : syracuseStep 2467757 = 925409) B925409
theorem B1517591 : Blo 558808 1517591 := bstep (se 1 (by rfl) ⟨1138193, by rfl⟩ : syracuseStep 1517591 = 2276387) B2276387
theorem B632875 : Blo 558808 632875 := bstep (se 1 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 632875 = 949313) B949313
theorem B1419353 : Blo 558808 1419353 := bstep (se 2 (by rfl) ⟨532257, by rfl⟩ : syracuseStep 1419353 = 1064515) B1064515
theorem B632983 : Blo 558808 632983 := bstep (se 1 (by rfl) ⟨474737, by rfl⟩ : syracuseStep 632983 = 949475) B949475
theorem B4041053 : Blo 558808 4041053 := bstep (se 3 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 4041053 = 1515395) B1515395
theorem B567799 : Blo 558808 567799 := bstep (se 1 (by rfl) ⟨425849, by rfl⟩ : syracuseStep 567799 = 851699) B851699
theorem B797207 : Blo 558808 797207 := bstep (se 1 (by rfl) ⟨597905, by rfl⟩ : syracuseStep 797207 = 1195811) B1195811
theorem B13609565 : Blo 558808 13609565 := bstep (se 3 (by rfl) ⟨2551793, by rfl⟩ : syracuseStep 13609565 = 5103587) B5103587
theorem B797401 : Blo 558808 797401 := bstep (se 2 (by rfl) ⟨299025, by rfl⟩ : syracuseStep 797401 = 598051) B598051
theorem B961303 : Blo 558808 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B2435891 : Blo 558808 2435891 := bstep (se 1 (by rfl) ⟨1826918, by rfl⟩ : syracuseStep 2435891 = 3653837) B3653837
theorem B3582899 : Blo 558808 3582899 := bstep (se 1 (by rfl) ⟨2687174, by rfl⟩ : syracuseStep 3582899 = 5374349) B5374349
theorem B2829329 : Blo 558808 2829329 := bstep (se 2 (by rfl) ⟨1060998, by rfl⟩ : syracuseStep 2829329 = 2121997) B2121997
theorem B2829491 : Blo 558808 2829491 := bstep (se 1 (by rfl) ⟨2122118, by rfl⟩ : syracuseStep 2829491 = 4244237) B4244237
theorem B2698571 : Blo 558808 2698571 := bstep (se 1 (by rfl) ⟨2023928, by rfl⟩ : syracuseStep 2698571 = 4047857) B4047857
theorem B4271453 : Blo 558808 4271453 := bstep (se 3 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 4271453 = 1601795) B1601795
theorem B1421003 : Blo 558808 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B1617857 : Blo 558808 1617857 := bstep (se 2 (by rfl) ⟨606696, by rfl⟩ : syracuseStep 1617857 = 1213393) B1213393
theorem B1257497 : Blo 558808 1257497 := bstep (se 2 (by rfl) ⟨471561, by rfl⟩ : syracuseStep 1257497 = 943123) B943123
theorem B1257587 : Blo 558808 1257587 := bstep (se 1 (by rfl) ⟨943190, by rfl⟩ : syracuseStep 1257587 = 1886381) B1886381
theorem B798859 : Blo 558808 798859 := bstep (se 1 (by rfl) ⟨599144, by rfl⟩ : syracuseStep 798859 = 1198289) B1198289
theorem B1257623 : Blo 558808 1257623 := bstep (se 1 (by rfl) ⟨943217, by rfl⟩ : syracuseStep 1257623 = 1886435) B1886435
theorem B1257803 : Blo 558808 1257803 := bstep (se 1 (by rfl) ⟨943352, by rfl⟩ : syracuseStep 1257803 = 1886705) B1886705
theorem B3584357 : Blo 558808 3584357 := bstep (se 4 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 3584357 = 672067) B672067
theorem B1257857 : Blo 558808 1257857 := bstep (se 2 (by rfl) ⟨471696, by rfl⟩ : syracuseStep 1257857 = 943393) B943393
theorem B1061363 : Blo 558808 1061363 := bstep (se 1 (by rfl) ⟨796022, by rfl⟩ : syracuseStep 1061363 = 1592045) B1592045
theorem B22196753 : Blo 558808 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B1258073 : Blo 558808 1258073 := bstep (se 2 (by rfl) ⟨471777, by rfl⟩ : syracuseStep 1258073 = 943555) B943555
theorem B1061515 : Blo 558808 1061515 := bstep (se 1 (by rfl) ⟨796136, by rfl⟩ : syracuseStep 1061515 = 1592273) B1592273
theorem B1421975 : Blo 558808 1421975 := bstep (se 1 (by rfl) ⟨1066481, by rfl⟩ : syracuseStep 1421975 = 2132963) B2132963
theorem B1258163 : Blo 558808 1258163 := bstep (se 1 (by rfl) ⟨943622, by rfl⟩ : syracuseStep 1258163 = 1887245) B1887245
theorem B1258199 : Blo 558808 1258199 := bstep (se 1 (by rfl) ⟨943649, by rfl⟩ : syracuseStep 1258199 = 1887299) B1887299
theorem B1258379 : Blo 558808 1258379 := bstep (se 1 (by rfl) ⟨943784, by rfl⟩ : syracuseStep 1258379 = 1887569) B1887569
theorem B1258433 : Blo 558808 1258433 := bstep (se 2 (by rfl) ⟨471912, by rfl⟩ : syracuseStep 1258433 = 943825) B943825
theorem B1061849 : Blo 558808 1061849 := bstep (se 2 (by rfl) ⟨398193, by rfl⟩ : syracuseStep 1061849 = 796387) B796387
theorem B2831435 : Blo 558808 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B1258649 : Blo 558808 1258649 := bstep (se 2 (by rfl) ⟨471993, by rfl⟩ : syracuseStep 1258649 = 943987) B943987
theorem B1258739 : Blo 558808 1258739 := bstep (se 1 (by rfl) ⟨944054, by rfl⟩ : syracuseStep 1258739 = 1888109) B1888109
theorem B1258775 : Blo 558808 1258775 := bstep (se 1 (by rfl) ⟨944081, by rfl⟩ : syracuseStep 1258775 = 1888163) B1888163
theorem B4797731 : Blo 558808 4797731 := bstep (se 1 (by rfl) ⟨3598298, by rfl⟩ : syracuseStep 4797731 = 7196597) B7196597
theorem B1422643 : Blo 558808 1422643 := bstep (se 1 (by rfl) ⟨1066982, by rfl⟩ : syracuseStep 1422643 = 2133965) B2133965
theorem B1422785 : Blo 558808 1422785 := bstep (se 2 (by rfl) ⟨533544, by rfl⟩ : syracuseStep 1422785 = 1067089) B1067089
theorem B1258955 : Blo 558808 1258955 := bstep (se 1 (by rfl) ⟨944216, by rfl⟩ : syracuseStep 1258955 = 1888433) B1888433
theorem B1259009 : Blo 558808 1259009 := bstep (se 2 (by rfl) ⟨472128, by rfl⟩ : syracuseStep 1259009 = 944257) B944257
theorem B2307635 : Blo 558808 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B1062487 : Blo 558808 1062487 := bstep (se 1 (by rfl) ⟨796865, by rfl⟩ : syracuseStep 1062487 = 1593731) B1593731
theorem B1259225 : Blo 558808 1259225 := bstep (se 2 (by rfl) ⟨472209, by rfl⟩ : syracuseStep 1259225 = 944419) B944419
theorem B10368773 : Blo 558808 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B1193753 : Blo 558808 1193753 := bstep (se 2 (by rfl) ⟨447657, by rfl⟩ : syracuseStep 1193753 = 895315) B895315
theorem B1259315 : Blo 558808 1259315 := bstep (se 1 (by rfl) ⟨944486, by rfl⟩ : syracuseStep 1259315 = 1888973) B1888973
theorem B1259351 : Blo 558808 1259351 := bstep (se 1 (by rfl) ⟨944513, by rfl⟩ : syracuseStep 1259351 = 1889027) B1889027
theorem B24262577 : Blo 558808 24262577 := bstep (se 2 (by rfl) ⟨9098466, by rfl⟩ : syracuseStep 24262577 = 18196933) B18196933
theorem B1259531 : Blo 558808 1259531 := bstep (se 1 (by rfl) ⟨944648, by rfl⟩ : syracuseStep 1259531 = 1889297) B1889297
theorem B1259585 : Blo 558808 1259585 := bstep (se 2 (by rfl) ⟨472344, by rfl⟩ : syracuseStep 1259585 = 944689) B944689
theorem B6371459 : Blo 558808 6371459 := bstep (se 1 (by rfl) ⟨4778594, by rfl⟩ : syracuseStep 6371459 = 9557189) B9557189
theorem B1259801 : Blo 558808 1259801 := bstep (se 2 (by rfl) ⟨472425, by rfl⟩ : syracuseStep 1259801 = 944851) B944851
theorem B3193181 : Blo 558808 3193181 := bstep (se 3 (by rfl) ⟨598721, by rfl⟩ : syracuseStep 3193181 = 1197443) B1197443
theorem B1259891 : Blo 558808 1259891 := bstep (se 1 (by rfl) ⟨944918, by rfl⟩ : syracuseStep 1259891 = 1889837) B1889837
theorem B1063307 : Blo 558808 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B1259927 : Blo 558808 1259927 := bstep (se 1 (by rfl) ⟨944945, by rfl⟩ : syracuseStep 1259927 = 1889891) B1889891
theorem B1063361 : Blo 558808 1063361 := bstep (se 2 (by rfl) ⟨398760, by rfl⟩ : syracuseStep 1063361 = 797521) B797521
theorem B1194547 : Blo 558808 1194547 := bstep (se 1 (by rfl) ⟨895910, by rfl⟩ : syracuseStep 1194547 = 1791821) B1791821
theorem B1260107 : Blo 558808 1260107 := bstep (se 1 (by rfl) ⟨945080, by rfl⟩ : syracuseStep 1260107 = 1890161) B1890161
theorem B1260161 : Blo 558808 1260161 := bstep (se 2 (by rfl) ⟨472560, by rfl⟩ : syracuseStep 1260161 = 945121) B945121
theorem B899723 : Blo 558808 899723 := bstep (se 1 (by rfl) ⟨674792, by rfl⟩ : syracuseStep 899723 = 1349585) B1349585
theorem B1424051 : Blo 558808 1424051 := bstep (se 1 (by rfl) ⟨1068038, by rfl⟩ : syracuseStep 1424051 = 2136077) B2136077
theorem B2833217 : Blo 558808 2833217 := bstep (se 2 (by rfl) ⟨1062456, by rfl⟩ : syracuseStep 2833217 = 2124913) B2124913
theorem B1260377 : Blo 558808 1260377 := bstep (se 2 (by rfl) ⟨472641, by rfl⟩ : syracuseStep 1260377 = 945283) B945283
theorem B1260467 : Blo 558808 1260467 := bstep (se 1 (by rfl) ⟨945350, by rfl⟩ : syracuseStep 1260467 = 1890701) B1890701
theorem B1260503 : Blo 558808 1260503 := bstep (se 1 (by rfl) ⟨945377, by rfl⟩ : syracuseStep 1260503 = 1890755) B1890755
theorem B3193931 : Blo 558808 3193931 := bstep (se 1 (by rfl) ⟨2395448, by rfl⟩ : syracuseStep 3193931 = 4790897) B4790897
theorem B1260683 : Blo 558808 1260683 := bstep (se 1 (by rfl) ⟨945512, by rfl⟩ : syracuseStep 1260683 = 1891025) B1891025
theorem B1260737 : Blo 558808 1260737 := bstep (se 2 (by rfl) ⟨472776, by rfl⟩ : syracuseStep 1260737 = 945553) B945553
theorem B1424587 : Blo 558808 1424587 := bstep (se 1 (by rfl) ⟨1068440, by rfl⟩ : syracuseStep 1424587 = 2136881) B2136881
theorem B2702609 : Blo 558808 2702609 := bstep (se 2 (by rfl) ⟨1013478, by rfl⟩ : syracuseStep 2702609 = 2026957) B2026957
theorem B1064279 : Blo 558808 1064279 := bstep (se 1 (by rfl) ⟨798209, by rfl⟩ : syracuseStep 1064279 = 1596419) B1596419
theorem B1195393 : Blo 558808 1195393 := bstep (se 2 (by rfl) ⟨448272, by rfl⟩ : syracuseStep 1195393 = 896545) B896545
theorem B1260953 : Blo 558808 1260953 := bstep (se 2 (by rfl) ⟨472857, by rfl⟩ : syracuseStep 1260953 = 945715) B945715
theorem B1261043 : Blo 558808 1261043 := bstep (se 1 (by rfl) ⟨945782, by rfl⟩ : syracuseStep 1261043 = 1891565) B1891565
theorem B1261079 : Blo 558808 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B1261259 : Blo 558808 1261259 := bstep (se 1 (by rfl) ⟨945944, by rfl⟩ : syracuseStep 1261259 = 1891889) B1891889
theorem B1195735 : Blo 558808 1195735 := bstep (se 1 (by rfl) ⟨896801, by rfl⟩ : syracuseStep 1195735 = 1793603) B1793603
theorem B1261313 : Blo 558808 1261313 := bstep (se 2 (by rfl) ⟨472992, by rfl⟩ : syracuseStep 1261313 = 945985) B945985
theorem B1064819 : Blo 558808 1064819 := bstep (se 1 (by rfl) ⟨798614, by rfl⟩ : syracuseStep 1064819 = 1597229) B1597229
theorem B1261529 : Blo 558808 1261529 := bstep (se 2 (by rfl) ⟨473073, by rfl⟩ : syracuseStep 1261529 = 946147) B946147
theorem B8306705 : Blo 558808 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B1261619 : Blo 558808 1261619 := bstep (se 1 (by rfl) ⟨946214, by rfl⟩ : syracuseStep 1261619 = 1892429) B1892429
theorem B22986827 : Blo 558808 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B1261655 : Blo 558808 1261655 := bstep (se 1 (by rfl) ⟨946241, by rfl⟩ : syracuseStep 1261655 = 1892483) B1892483
theorem B1261835 : Blo 558808 1261835 := bstep (se 1 (by rfl) ⟨946376, by rfl⟩ : syracuseStep 1261835 = 1892753) B1892753
theorem B1261889 : Blo 558808 1261889 := bstep (se 2 (by rfl) ⟨473208, by rfl⟩ : syracuseStep 1261889 = 946417) B946417
theorem B1065305 : Blo 558808 1065305 := bstep (se 2 (by rfl) ⟨399489, by rfl⟩ : syracuseStep 1065305 = 798979) B798979
theorem B2310617 : Blo 558808 2310617 := bstep (se 2 (by rfl) ⟨866481, by rfl⟩ : syracuseStep 2310617 = 1732963) B1732963
theorem B1262105 : Blo 558808 1262105 := bstep (se 2 (by rfl) ⟨473289, by rfl⟩ : syracuseStep 1262105 = 946579) B946579
theorem B1262195 : Blo 558808 1262195 := bstep (se 1 (by rfl) ⟨946646, by rfl⟩ : syracuseStep 1262195 = 1893293) B1893293
theorem B1262231 : Blo 558808 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B3195571 : Blo 558808 3195571 := bstep (se 1 (by rfl) ⟨2396678, by rfl⟩ : syracuseStep 3195571 = 4793357) B4793357
theorem B2835161 : Blo 558808 2835161 := bstep (se 2 (by rfl) ⟨1063185, by rfl⟩ : syracuseStep 2835161 = 2126371) B2126371
theorem B1262411 : Blo 558808 1262411 := bstep (se 1 (by rfl) ⟨946808, by rfl⟩ : syracuseStep 1262411 = 1893617) B1893617
theorem B4801355 : Blo 558808 4801355 := bstep (se 1 (by rfl) ⟨3601016, by rfl⟩ : syracuseStep 4801355 = 7202033) B7202033
theorem B1262465 : Blo 558808 1262465 := bstep (se 2 (by rfl) ⟨473424, by rfl⟩ : syracuseStep 1262465 = 946849) B946849
theorem B1196939 : Blo 558808 1196939 := bstep (se 1 (by rfl) ⟨897704, by rfl⟩ : syracuseStep 1196939 = 1795409) B1795409
theorem B1262681 : Blo 558808 1262681 := bstep (se 2 (by rfl) ⟨473505, by rfl⟩ : syracuseStep 1262681 = 947011) B947011
theorem B1262771 : Blo 558808 1262771 := bstep (se 1 (by rfl) ⟨947078, by rfl⟩ : syracuseStep 1262771 = 1894157) B1894157
theorem B1262807 : Blo 558808 1262807 := bstep (se 1 (by rfl) ⟨947105, by rfl⟩ : syracuseStep 1262807 = 1894211) B1894211
theorem B2016535 : Blo 558808 2016535 := bstep (se 1 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 2016535 = 3024803) B3024803
theorem B9684269 : Blo 558808 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B1197451 : Blo 558808 1197451 := bstep (se 1 (by rfl) ⟨898088, by rfl⟩ : syracuseStep 1197451 = 1796177) B1796177
theorem B1262987 : Blo 558808 1262987 := bstep (se 1 (by rfl) ⟨947240, by rfl⟩ : syracuseStep 1262987 = 1894481) B1894481
theorem B1263041 : Blo 558808 1263041 := bstep (se 2 (by rfl) ⟨473640, by rfl⟩ : syracuseStep 1263041 = 947281) B947281
theorem B1263257 : Blo 558808 1263257 := bstep (se 2 (by rfl) ⟨473721, by rfl⟩ : syracuseStep 1263257 = 947443) B947443
theorem B4245209 : Blo 558808 4245209 := bstep (se 2 (by rfl) ⟨1591953, by rfl⟩ : syracuseStep 4245209 = 3183907) B3183907
theorem B1263347 : Blo 558808 1263347 := bstep (se 1 (by rfl) ⟨947510, by rfl⟩ : syracuseStep 1263347 = 1895021) B1895021
theorem B1066763 : Blo 558808 1066763 := bstep (se 1 (by rfl) ⟨800072, by rfl⟩ : syracuseStep 1066763 = 1600145) B1600145
theorem B1263383 : Blo 558808 1263383 := bstep (se 1 (by rfl) ⟨947537, by rfl⟩ : syracuseStep 1263383 = 1895075) B1895075
theorem B1886003 : Blo 558808 1886003 := bstep (se 1 (by rfl) ⟨1414502, by rfl⟩ : syracuseStep 1886003 = 2829005) B2829005
theorem B2869067 : Blo 558808 2869067 := bstep (se 1 (by rfl) ⟨2151800, by rfl⟩ : syracuseStep 2869067 = 4303601) B4303601
theorem B1066945 : Blo 558808 1066945 := bstep (se 2 (by rfl) ⟨400104, by rfl⟩ : syracuseStep 1066945 = 800209) B800209
theorem B1263563 : Blo 558808 1263563 := bstep (se 1 (by rfl) ⟨947672, by rfl⟩ : syracuseStep 1263563 = 1895345) B1895345
theorem B1558493 : Blo 558808 1558493 := bstep (se 3 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 1558493 = 584435) B584435
theorem B1263617 : Blo 558808 1263617 := bstep (se 2 (by rfl) ⟨473856, by rfl⟩ : syracuseStep 1263617 = 947713) B947713
theorem B1886273 : Blo 558808 1886273 := bstep (se 2 (by rfl) ⟨707352, by rfl⟩ : syracuseStep 1886273 = 1414705) B1414705
theorem B1198169 : Blo 558808 1198169 := bstep (se 2 (by rfl) ⟨449313, by rfl⟩ : syracuseStep 1198169 = 898627) B898627
theorem B3197029 : Blo 558808 3197029 := bstep (se 4 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 3197029 = 599443) B599443
theorem B1263833 : Blo 558808 1263833 := bstep (se 2 (by rfl) ⟨473937, by rfl⟩ : syracuseStep 1263833 = 947875) B947875
theorem B2836781 : Blo 558808 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B1263923 : Blo 558808 1263923 := bstep (se 1 (by rfl) ⟨947942, by rfl⟩ : syracuseStep 1263923 = 1895885) B1895885
theorem B1263959 : Blo 558808 1263959 := bstep (se 1 (by rfl) ⟨947969, by rfl⟩ : syracuseStep 1263959 = 1895939) B1895939
theorem B1067393 : Blo 558808 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B1198579 : Blo 558808 1198579 := bstep (se 1 (by rfl) ⟨898934, by rfl⟩ : syracuseStep 1198579 = 1797869) B1797869
theorem B1264139 : Blo 558808 1264139 := bstep (se 1 (by rfl) ⟨948104, by rfl⟩ : syracuseStep 1264139 = 1896209) B1896209
theorem B1264193 : Blo 558808 1264193 := bstep (se 2 (by rfl) ⟨474072, by rfl⟩ : syracuseStep 1264193 = 948145) B948145
theorem B3066443 : Blo 558808 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B1886813 : Blo 558808 1886813 := bstep (se 3 (by rfl) ⟨353777, by rfl⟩ : syracuseStep 1886813 = 707555) B707555
theorem B838283 : Blo 558808 838283 := bstep (se 1 (by rfl) ⟨628712, by rfl⟩ : syracuseStep 838283 = 1257425) B1257425
theorem B838295 : Blo 558808 838295 := bstep (se 1 (by rfl) ⟨628721, by rfl⟩ : syracuseStep 838295 = 1257443) B1257443
theorem B707287 : Blo 558808 707287 := bstep (se 1 (by rfl) ⟨530465, by rfl⟩ : syracuseStep 707287 = 1060931) B1060931
theorem B1067735 : Blo 558808 1067735 := bstep (se 1 (by rfl) ⟨800801, by rfl⟩ : syracuseStep 1067735 = 1601603) B1601603
theorem B838361 : Blo 558808 838361 := bstep (se 2 (by rfl) ⟨314385, by rfl⟩ : syracuseStep 838361 = 628771) B628771
theorem B1264409 : Blo 558808 1264409 := bstep (se 2 (by rfl) ⟨474153, by rfl⟩ : syracuseStep 1264409 = 948307) B948307
theorem B838475 : Blo 558808 838475 := bstep (se 1 (by rfl) ⟨628856, by rfl⟩ : syracuseStep 838475 = 1257713) B1257713
theorem B838487 : Blo 558808 838487 := bstep (se 1 (by rfl) ⟨628865, by rfl⟩ : syracuseStep 838487 = 1257731) B1257731
theorem B1264499 : Blo 558808 1264499 := bstep (se 1 (by rfl) ⟨948374, by rfl⟩ : syracuseStep 1264499 = 1896749) B1896749
theorem B1264535 : Blo 558808 1264535 := bstep (se 1 (by rfl) ⟨948401, by rfl⟩ : syracuseStep 1264535 = 1896803) B1896803
theorem B838553 : Blo 558808 838553 := bstep (se 2 (by rfl) ⟨314457, by rfl⟩ : syracuseStep 838553 = 628915) B628915
theorem B838667 : Blo 558808 838667 := bstep (se 1 (by rfl) ⟨629000, by rfl⟩ : syracuseStep 838667 = 1258001) B1258001
theorem B838679 : Blo 558808 838679 := bstep (se 1 (by rfl) ⟨629009, by rfl⟩ : syracuseStep 838679 = 1258019) B1258019
theorem B1264715 : Blo 558808 1264715 := bstep (se 1 (by rfl) ⟨948536, by rfl⟩ : syracuseStep 1264715 = 1897073) B1897073
theorem B838745 : Blo 558808 838745 := bstep (se 2 (by rfl) ⟨314529, by rfl⟩ : syracuseStep 838745 = 629059) B629059
theorem B1264769 : Blo 558808 1264769 := bstep (se 2 (by rfl) ⟨474288, by rfl⟩ : syracuseStep 1264769 = 948577) B948577
theorem B6409367 : Blo 558808 6409367 := bstep (se 1 (by rfl) ⟨4807025, by rfl⟩ : syracuseStep 6409367 = 9614051) B9614051
theorem B838859 : Blo 558808 838859 := bstep (se 1 (by rfl) ⟨629144, by rfl⟩ : syracuseStep 838859 = 1258289) B1258289
theorem B838871 : Blo 558808 838871 := bstep (se 1 (by rfl) ⟨629153, by rfl⟩ : syracuseStep 838871 = 1258307) B1258307
theorem B838937 : Blo 558808 838937 := bstep (se 2 (by rfl) ⟨314601, by rfl⟩ : syracuseStep 838937 = 629203) B629203
theorem B1264985 : Blo 558808 1264985 := bstep (se 2 (by rfl) ⟨474369, by rfl⟩ : syracuseStep 1264985 = 948739) B948739
theorem B5131613 : Blo 558808 5131613 := bstep (se 3 (by rfl) ⟨962177, by rfl⟩ : syracuseStep 5131613 = 1924355) B1924355
theorem B1068403 : Blo 558808 1068403 := bstep (se 1 (by rfl) ⟨801302, by rfl⟩ : syracuseStep 1068403 = 1602605) B1602605
theorem B839051 : Blo 558808 839051 := bstep (se 1 (by rfl) ⟨629288, by rfl⟩ : syracuseStep 839051 = 1258577) B1258577
theorem B839063 : Blo 558808 839063 := bstep (se 1 (by rfl) ⟨629297, by rfl⟩ : syracuseStep 839063 = 1258595) B1258595
theorem B1265075 : Blo 558808 1265075 := bstep (se 1 (by rfl) ⟨948806, by rfl⟩ : syracuseStep 1265075 = 1897613) B1897613
theorem B4804019 : Blo 558808 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B24202709 : Blo 558808 24202709 := bstep (se 7 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 24202709 = 567251) B567251
theorem B1265111 : Blo 558808 1265111 := bstep (se 1 (by rfl) ⟨948833, by rfl⟩ : syracuseStep 1265111 = 1897667) B1897667
theorem B839129 : Blo 558808 839129 := bstep (se 2 (by rfl) ⟨314673, by rfl⟩ : syracuseStep 839129 = 629347) B629347
theorem B1592797 : Blo 558808 1592797 := bstep (se 3 (by rfl) ⟨298649, by rfl⟩ : syracuseStep 1592797 = 597299) B597299
theorem B1592855 : Blo 558808 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B839243 : Blo 558808 839243 := bstep (se 1 (by rfl) ⟨629432, by rfl⟩ : syracuseStep 839243 = 1258865) B1258865
theorem B839255 : Blo 558808 839255 := bstep (se 1 (by rfl) ⟨629441, by rfl⟩ : syracuseStep 839255 = 1258883) B1258883
theorem B1265291 : Blo 558808 1265291 := bstep (se 1 (by rfl) ⟨948968, by rfl⟩ : syracuseStep 1265291 = 1897937) B1897937
theorem B1199767 : Blo 558808 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B839321 : Blo 558808 839321 := bstep (se 2 (by rfl) ⟨314745, by rfl⟩ : syracuseStep 839321 = 629491) B629491
theorem B1199809 : Blo 558808 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B1265345 : Blo 558808 1265345 := bstep (se 2 (by rfl) ⟨474504, by rfl⟩ : syracuseStep 1265345 = 949009) B949009
theorem B1887947 : Blo 558808 1887947 := bstep (se 1 (by rfl) ⟨1415960, by rfl⟩ : syracuseStep 1887947 = 2831921) B2831921
theorem B6082253 : Blo 558808 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B839435 : Blo 558808 839435 := bstep (se 1 (by rfl) ⟨629576, by rfl⟩ : syracuseStep 839435 = 1259153) B1259153
theorem B839447 : Blo 558808 839447 := bstep (se 1 (by rfl) ⟨629585, by rfl⟩ : syracuseStep 839447 = 1259171) B1259171
theorem B5394221 : Blo 558808 5394221 := bstep (se 3 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 5394221 = 2022833) B2022833
theorem B839513 : Blo 558808 839513 := bstep (se 2 (by rfl) ⟨314817, by rfl⟩ : syracuseStep 839513 = 629635) B629635
theorem B1265561 : Blo 558808 1265561 := bstep (se 2 (by rfl) ⟨474585, by rfl⟩ : syracuseStep 1265561 = 949171) B949171
theorem B839627 : Blo 558808 839627 := bstep (se 1 (by rfl) ⟨629720, by rfl⟩ : syracuseStep 839627 = 1259441) B1259441
theorem B839639 : Blo 558808 839639 := bstep (se 1 (by rfl) ⟨629729, by rfl⟩ : syracuseStep 839639 = 1259459) B1259459
theorem B1888217 : Blo 558808 1888217 := bstep (se 2 (by rfl) ⟨708081, by rfl⟩ : syracuseStep 1888217 = 1416163) B1416163
theorem B1265651 : Blo 558808 1265651 := bstep (se 1 (by rfl) ⟨949238, by rfl⟩ : syracuseStep 1265651 = 1898477) B1898477
theorem B1265687 : Blo 558808 1265687 := bstep (se 1 (by rfl) ⟨949265, by rfl⟩ : syracuseStep 1265687 = 1898531) B1898531
theorem B839705 : Blo 558808 839705 := bstep (se 2 (by rfl) ⟨314889, by rfl⟩ : syracuseStep 839705 = 629779) B629779
theorem B1134731 : Blo 558808 1134731 := bstep (se 1 (by rfl) ⟨851048, by rfl⟩ : syracuseStep 1134731 = 1702097) B1702097
theorem B839819 : Blo 558808 839819 := bstep (se 1 (by rfl) ⟨629864, by rfl⟩ : syracuseStep 839819 = 1259729) B1259729
theorem B839831 : Blo 558808 839831 := bstep (se 1 (by rfl) ⟨629873, by rfl⟩ : syracuseStep 839831 = 1259747) B1259747
theorem B1265867 : Blo 558808 1265867 := bstep (se 1 (by rfl) ⟨949400, by rfl⟩ : syracuseStep 1265867 = 1898801) B1898801
theorem B839897 : Blo 558808 839897 := bstep (se 2 (by rfl) ⟨314961, by rfl⟩ : syracuseStep 839897 = 629923) B629923
theorem B1265921 : Blo 558808 1265921 := bstep (se 2 (by rfl) ⟨474720, by rfl⟩ : syracuseStep 1265921 = 949441) B949441
theorem B2019649 : Blo 558808 2019649 := bstep (se 2 (by rfl) ⟨757368, by rfl⟩ : syracuseStep 2019649 = 1514737) B1514737
theorem B840011 : Blo 558808 840011 := bstep (se 1 (by rfl) ⟨630008, by rfl⟩ : syracuseStep 840011 = 1260017) B1260017
theorem B840023 : Blo 558808 840023 := bstep (se 1 (by rfl) ⟨630017, by rfl⟩ : syracuseStep 840023 = 1260035) B1260035
theorem B709003 : Blo 558808 709003 := bstep (se 1 (by rfl) ⟨531752, by rfl⟩ : syracuseStep 709003 = 1063505) B1063505
theorem B840089 : Blo 558808 840089 := bstep (se 2 (by rfl) ⟨315033, by rfl⟩ : syracuseStep 840089 = 630067) B630067
theorem B2019763 : Blo 558808 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B1364441 : Blo 558808 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B4805081 : Blo 558808 4805081 := bstep (se 2 (by rfl) ⟨1801905, by rfl⟩ : syracuseStep 4805081 = 3603811) B3603811
theorem B1266137 : Blo 558808 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B840203 : Blo 558808 840203 := bstep (se 1 (by rfl) ⟨630152, by rfl⟩ : syracuseStep 840203 = 1260305) B1260305
theorem B840215 : Blo 558808 840215 := bstep (se 1 (by rfl) ⟨630161, by rfl⟩ : syracuseStep 840215 = 1260323) B1260323
theorem B1266227 : Blo 558808 1266227 := bstep (se 1 (by rfl) ⟨949670, by rfl⟩ : syracuseStep 1266227 = 1899341) B1899341
theorem B1266263 : Blo 558808 1266263 := bstep (se 1 (by rfl) ⟨949697, by rfl⟩ : syracuseStep 1266263 = 1899395) B1899395
theorem B840281 : Blo 558808 840281 := bstep (se 2 (by rfl) ⟨315105, by rfl⟩ : syracuseStep 840281 = 630211) B630211
theorem B1888919 : Blo 558808 1888919 := bstep (se 1 (by rfl) ⟨1416689, by rfl⟩ : syracuseStep 1888919 = 2833379) B2833379
theorem B840395 : Blo 558808 840395 := bstep (se 1 (by rfl) ⟨630296, by rfl⟩ : syracuseStep 840395 = 1260593) B1260593
theorem B840407 : Blo 558808 840407 := bstep (se 1 (by rfl) ⟨630305, by rfl⟩ : syracuseStep 840407 = 1260611) B1260611
theorem B1594073 : Blo 558808 1594073 := bstep (se 2 (by rfl) ⟨597777, by rfl⟩ : syracuseStep 1594073 = 1195555) B1195555
theorem B1790743 : Blo 558808 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B840473 : Blo 558808 840473 := bstep (se 2 (by rfl) ⟨315177, by rfl⟩ : syracuseStep 840473 = 630355) B630355
theorem B4051777 : Blo 558808 4051777 := bstep (se 2 (by rfl) ⟨1519416, by rfl⟩ : syracuseStep 4051777 = 3038833) B3038833
theorem B1594187 : Blo 558808 1594187 := bstep (se 1 (by rfl) ⟨1195640, by rfl⟩ : syracuseStep 1594187 = 2391281) B2391281
theorem B840587 : Blo 558808 840587 := bstep (se 1 (by rfl) ⟨630440, by rfl⟩ : syracuseStep 840587 = 1260881) B1260881
theorem B840599 : Blo 558808 840599 := bstep (se 1 (by rfl) ⟨630449, by rfl⟩ : syracuseStep 840599 = 1260899) B1260899
theorem B840665 : Blo 558808 840665 := bstep (se 2 (by rfl) ⟨315249, by rfl⟩ : syracuseStep 840665 = 630499) B630499
theorem B4248611 : Blo 558808 4248611 := bstep (se 1 (by rfl) ⟨3186458, by rfl⟩ : syracuseStep 4248611 = 6372917) B6372917
theorem B840779 : Blo 558808 840779 := bstep (se 1 (by rfl) ⟨630584, by rfl⟩ : syracuseStep 840779 = 1261169) B1261169
theorem B840791 : Blo 558808 840791 := bstep (se 1 (by rfl) ⟨630593, by rfl⟩ : syracuseStep 840791 = 1261187) B1261187
theorem B840857 : Blo 558808 840857 := bstep (se 2 (by rfl) ⟨315321, by rfl⟩ : syracuseStep 840857 = 630643) B630643
theorem B1889459 : Blo 558808 1889459 := bstep (se 1 (by rfl) ⟨1417094, by rfl⟩ : syracuseStep 1889459 = 2834189) B2834189
theorem B1135883 : Blo 558808 1135883 := bstep (se 1 (by rfl) ⟨851912, by rfl⟩ : syracuseStep 1135883 = 1703825) B1703825
theorem B840971 : Blo 558808 840971 := bstep (se 1 (by rfl) ⟨630728, by rfl⟩ : syracuseStep 840971 = 1261457) B1261457
theorem B840983 : Blo 558808 840983 := bstep (se 1 (by rfl) ⟨630737, by rfl⟩ : syracuseStep 840983 = 1261475) B1261475
theorem B1201483 : Blo 558808 1201483 := bstep (se 1 (by rfl) ⟨901112, by rfl⟩ : syracuseStep 1201483 = 1802225) B1802225
theorem B709975 : Blo 558808 709975 := bstep (se 1 (by rfl) ⟨532481, by rfl⟩ : syracuseStep 709975 = 1064963) B1064963
theorem B841049 : Blo 558808 841049 := bstep (se 2 (by rfl) ⟨315393, by rfl⟩ : syracuseStep 841049 = 630787) B630787
theorem B1889729 : Blo 558808 1889729 := bstep (se 2 (by rfl) ⟨708648, by rfl⟩ : syracuseStep 1889729 = 1417297) B1417297
theorem B841163 : Blo 558808 841163 := bstep (se 1 (by rfl) ⟨630872, by rfl⟩ : syracuseStep 841163 = 1261745) B1261745
theorem B841175 : Blo 558808 841175 := bstep (se 1 (by rfl) ⟨630881, by rfl⟩ : syracuseStep 841175 = 1261763) B1261763
theorem B841241 : Blo 558808 841241 := bstep (se 2 (by rfl) ⟨315465, by rfl⟩ : syracuseStep 841241 = 630931) B630931
theorem B1791563 : Blo 558808 1791563 := bstep (se 1 (by rfl) ⟨1343672, by rfl⟩ : syracuseStep 1791563 = 2687345) B2687345
theorem B2872907 : Blo 558808 2872907 := bstep (se 1 (by rfl) ⟨2154680, by rfl⟩ : syracuseStep 2872907 = 4309361) B4309361
theorem B841355 : Blo 558808 841355 := bstep (se 1 (by rfl) ⟨631016, by rfl⟩ : syracuseStep 841355 = 1262033) B1262033
theorem B841367 : Blo 558808 841367 := bstep (se 1 (by rfl) ⟨631025, by rfl⟩ : syracuseStep 841367 = 1262051) B1262051
theorem B1201817 : Blo 558808 1201817 := bstep (se 2 (by rfl) ⟨450681, by rfl⟩ : syracuseStep 1201817 = 901363) B901363
theorem B841433 : Blo 558808 841433 := bstep (se 2 (by rfl) ⟨315537, by rfl⟩ : syracuseStep 841433 = 631075) B631075
theorem B841547 : Blo 558808 841547 := bstep (se 1 (by rfl) ⟨631160, by rfl⟩ : syracuseStep 841547 = 1262321) B1262321
theorem B841559 : Blo 558808 841559 := bstep (se 1 (by rfl) ⟨631169, by rfl⟩ : syracuseStep 841559 = 1262339) B1262339
theorem B841625 : Blo 558808 841625 := bstep (se 2 (by rfl) ⟨315609, by rfl⟩ : syracuseStep 841625 = 631219) B631219
theorem B1595315 : Blo 558808 1595315 := bstep (se 1 (by rfl) ⟨1196486, by rfl⟩ : syracuseStep 1595315 = 2392973) B2392973
theorem B1890269 : Blo 558808 1890269 := bstep (se 3 (by rfl) ⟨354425, by rfl⟩ : syracuseStep 1890269 = 708851) B708851
theorem B841739 : Blo 558808 841739 := bstep (se 1 (by rfl) ⟨631304, by rfl⟩ : syracuseStep 841739 = 1262609) B1262609
theorem B841751 : Blo 558808 841751 := bstep (se 1 (by rfl) ⟨631313, by rfl⟩ : syracuseStep 841751 = 1262627) B1262627
theorem B841817 : Blo 558808 841817 := bstep (se 2 (by rfl) ⟨315681, by rfl⟩ : syracuseStep 841817 = 631363) B631363
theorem B2840669 : Blo 558808 2840669 := bstep (se 3 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 2840669 = 1065251) B1065251
theorem B3037277 : Blo 558808 3037277 := bstep (se 3 (by rfl) ⟨569489, by rfl⟩ : syracuseStep 3037277 = 1138979) B1138979
theorem B710795 : Blo 558808 710795 := bstep (se 1 (by rfl) ⟨533096, by rfl⟩ : syracuseStep 710795 = 1066193) B1066193
theorem B841931 : Blo 558808 841931 := bstep (se 1 (by rfl) ⟨631448, by rfl⟩ : syracuseStep 841931 = 1262897) B1262897
theorem B841943 : Blo 558808 841943 := bstep (se 1 (by rfl) ⟨631457, by rfl⟩ : syracuseStep 841943 = 1262915) B1262915
theorem B842009 : Blo 558808 842009 := bstep (se 2 (by rfl) ⟨315753, by rfl⟩ : syracuseStep 842009 = 631507) B631507
theorem B1792307 : Blo 558808 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B1595713 : Blo 558808 1595713 := bstep (se 2 (by rfl) ⟨598392, by rfl⟩ : syracuseStep 1595713 = 1196785) B1196785
theorem B842123 : Blo 558808 842123 := bstep (se 1 (by rfl) ⟨631592, by rfl⟩ : syracuseStep 842123 = 1263185) B1263185
theorem B842135 : Blo 558808 842135 := bstep (se 1 (by rfl) ⟨631601, by rfl⟩ : syracuseStep 842135 = 1263203) B1263203
theorem B842201 : Blo 558808 842201 := bstep (se 2 (by rfl) ⟨315825, by rfl⟩ : syracuseStep 842201 = 631651) B631651
theorem B842315 : Blo 558808 842315 := bstep (se 1 (by rfl) ⟨631736, by rfl⟩ : syracuseStep 842315 = 1263473) B1263473
theorem B842327 : Blo 558808 842327 := bstep (se 1 (by rfl) ⟨631745, by rfl⟩ : syracuseStep 842327 = 1263491) B1263491
theorem B842393 : Blo 558808 842393 := bstep (se 2 (by rfl) ⟨315897, by rfl⟩ : syracuseStep 842393 = 631795) B631795
theorem B842507 : Blo 558808 842507 := bstep (se 1 (by rfl) ⟨631880, by rfl⟩ : syracuseStep 842507 = 1263761) B1263761
theorem B842519 : Blo 558808 842519 := bstep (se 1 (by rfl) ⟨631889, by rfl⟩ : syracuseStep 842519 = 1263779) B1263779
theorem B711499 : Blo 558808 711499 := bstep (se 1 (by rfl) ⟨533624, by rfl⟩ : syracuseStep 711499 = 1067249) B1067249
theorem B842585 : Blo 558808 842585 := bstep (se 2 (by rfl) ⟨315969, by rfl⟩ : syracuseStep 842585 = 631939) B631939
theorem B842699 : Blo 558808 842699 := bstep (se 1 (by rfl) ⟨632024, by rfl⟩ : syracuseStep 842699 = 1264049) B1264049
theorem B842711 : Blo 558808 842711 := bstep (se 1 (by rfl) ⟨632033, by rfl⟩ : syracuseStep 842711 = 1264067) B1264067
theorem B842777 : Blo 558808 842777 := bstep (se 2 (by rfl) ⟨316041, by rfl⟩ : syracuseStep 842777 = 632083) B632083
theorem B1891403 : Blo 558808 1891403 := bstep (se 1 (by rfl) ⟨1418552, by rfl⟩ : syracuseStep 1891403 = 2837105) B2837105
theorem B711767 : Blo 558808 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B842891 : Blo 558808 842891 := bstep (se 1 (by rfl) ⟨632168, by rfl⟩ : syracuseStep 842891 = 1264337) B1264337
theorem B2022545 : Blo 558808 2022545 := bstep (se 2 (by rfl) ⟨758454, by rfl⟩ : syracuseStep 2022545 = 1516909) B1516909
theorem B842903 : Blo 558808 842903 := bstep (se 1 (by rfl) ⟨632177, by rfl⟩ : syracuseStep 842903 = 1264355) B1264355
theorem B842969 : Blo 558808 842969 := bstep (se 2 (by rfl) ⟨316113, by rfl⟩ : syracuseStep 842969 = 632227) B632227
theorem B843083 : Blo 558808 843083 := bstep (se 1 (by rfl) ⟨632312, by rfl⟩ : syracuseStep 843083 = 1264625) B1264625
theorem B843095 : Blo 558808 843095 := bstep (se 1 (by rfl) ⟨632321, by rfl⟩ : syracuseStep 843095 = 1264643) B1264643
theorem B1891673 : Blo 558808 1891673 := bstep (se 2 (by rfl) ⟨709377, by rfl⟩ : syracuseStep 1891673 = 1418755) B1418755
theorem B9592181 : Blo 558808 9592181 := bstep (se 5 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 9592181 = 899267) B899267
theorem B843161 : Blo 558808 843161 := bstep (se 2 (by rfl) ⟨316185, by rfl⟩ : syracuseStep 843161 = 632371) B632371
theorem B843275 : Blo 558808 843275 := bstep (se 1 (by rfl) ⟨632456, by rfl⟩ : syracuseStep 843275 = 1264913) B1264913
theorem B843287 : Blo 558808 843287 := bstep (se 1 (by rfl) ⟨632465, by rfl⟩ : syracuseStep 843287 = 1264931) B1264931
theorem B843353 : Blo 558808 843353 := bstep (se 2 (by rfl) ⟨316257, by rfl⟩ : syracuseStep 843353 = 632515) B632515
theorem B843467 : Blo 558808 843467 := bstep (se 1 (by rfl) ⟨632600, by rfl⟩ : syracuseStep 843467 = 1265201) B1265201
theorem B843479 : Blo 558808 843479 := bstep (se 1 (by rfl) ⟨632609, by rfl⟩ : syracuseStep 843479 = 1265219) B1265219
theorem B843545 : Blo 558808 843545 := bstep (se 2 (by rfl) ⟨316329, by rfl⟩ : syracuseStep 843545 = 632659) B632659
theorem B3202861 : Blo 558808 3202861 := bstep (se 3 (by rfl) ⟨600536, by rfl⟩ : syracuseStep 3202861 = 1201073) B1201073
theorem B1367873 : Blo 558808 1367873 := bstep (se 2 (by rfl) ⟨512952, by rfl⟩ : syracuseStep 1367873 = 1025905) B1025905
theorem B843659 : Blo 558808 843659 := bstep (se 1 (by rfl) ⟨632744, by rfl⟩ : syracuseStep 843659 = 1265489) B1265489
theorem B843671 : Blo 558808 843671 := bstep (se 1 (by rfl) ⟨632753, by rfl⟩ : syracuseStep 843671 = 1265507) B1265507
theorem B12115889 : Blo 558808 12115889 := bstep (se 2 (by rfl) ⟨4543458, by rfl⟩ : syracuseStep 12115889 = 9086917) B9086917
theorem B843737 : Blo 558808 843737 := bstep (se 2 (by rfl) ⟨316401, by rfl⟩ : syracuseStep 843737 = 632803) B632803
theorem B1892375 : Blo 558808 1892375 := bstep (se 1 (by rfl) ⟨1419281, by rfl⟩ : syracuseStep 1892375 = 2838563) B2838563
theorem B843851 : Blo 558808 843851 := bstep (se 1 (by rfl) ⟨632888, by rfl⟩ : syracuseStep 843851 = 1265777) B1265777
theorem B843863 : Blo 558808 843863 := bstep (se 1 (by rfl) ⟨632897, by rfl⟩ : syracuseStep 843863 = 1265795) B1265795
theorem B16113815 : Blo 558808 16113815 := bstep (se 1 (by rfl) ⟨12085361, by rfl⟩ : syracuseStep 16113815 = 24170723) B24170723
theorem B2842775 : Blo 558808 2842775 := bstep (se 1 (by rfl) ⟨2132081, by rfl⟩ : syracuseStep 2842775 = 4264163) B4264163
theorem B843929 : Blo 558808 843929 := bstep (se 2 (by rfl) ⟨316473, by rfl⟩ : syracuseStep 843929 = 632947) B632947
theorem B2875571 : Blo 558808 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B844043 : Blo 558808 844043 := bstep (se 1 (by rfl) ⟨633032, by rfl⟩ : syracuseStep 844043 = 1266065) B1266065
theorem B844055 : Blo 558808 844055 := bstep (se 1 (by rfl) ⟨633041, by rfl⟩ : syracuseStep 844055 = 1266083) B1266083
theorem B844121 : Blo 558808 844121 := bstep (se 2 (by rfl) ⟨316545, by rfl⟩ : syracuseStep 844121 = 633091) B633091
theorem B2187665 : Blo 558808 2187665 := bstep (se 2 (by rfl) ⟨820374, by rfl⟩ : syracuseStep 2187665 = 1640749) B1640749
theorem B1892915 : Blo 558808 1892915 := bstep (se 1 (by rfl) ⟨1419686, by rfl⟩ : syracuseStep 1892915 = 2839373) B2839373
theorem B1008331 : Blo 558808 1008331 := bstep (se 1 (by rfl) ⟨756248, by rfl⟩ : syracuseStep 1008331 = 1512497) B1512497
theorem B1598231 : Blo 558808 1598231 := bstep (se 1 (by rfl) ⟨1198673, by rfl⟩ : syracuseStep 1598231 = 2397347) B2397347
theorem B5202733 : Blo 558808 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B1893185 : Blo 558808 1893185 := bstep (se 2 (by rfl) ⟨709944, by rfl⟩ : syracuseStep 1893185 = 1419889) B1419889
theorem B8217521 : Blo 558808 8217521 := bstep (se 2 (by rfl) ⟨3081570, by rfl⟩ : syracuseStep 8217521 = 6163141) B6163141
theorem B8610947 : Blo 558808 8610947 := bstep (se 1 (by rfl) ⟨6458210, by rfl⟩ : syracuseStep 8610947 = 12916421) B12916421
theorem B2122955 : Blo 558808 2122955 := bstep (se 1 (by rfl) ⟨1592216, by rfl⟩ : syracuseStep 2122955 = 3184433) B3184433
theorem B943319 : Blo 558808 943319 := bstep (se 1 (by rfl) ⟨707489, by rfl⟩ : syracuseStep 943319 = 1414979) B1414979
theorem B2122969 : Blo 558808 2122969 := bstep (se 2 (by rfl) ⟨796113, by rfl⟩ : syracuseStep 2122969 = 1592227) B1592227
theorem B943447 : Blo 558808 943447 := bstep (se 1 (by rfl) ⟨707585, by rfl⟩ : syracuseStep 943447 = 1415171) B1415171
theorem B1893725 : Blo 558808 1893725 := bstep (se 3 (by rfl) ⟨355073, by rfl⟩ : syracuseStep 1893725 = 710147) B710147
theorem B5399909 : Blo 558808 5399909 := bstep (se 4 (by rfl) ⟨506241, by rfl⟩ : syracuseStep 5399909 = 1012483) B1012483
theorem B1009111 : Blo 558808 1009111 := bstep (se 1 (by rfl) ⟨756833, by rfl⟩ : syracuseStep 1009111 = 1513667) B1513667
theorem B1140311 : Blo 558808 1140311 := bstep (se 1 (by rfl) ⟨855233, by rfl⟩ : syracuseStep 1140311 = 1710467) B1710467
theorem B944075 : Blo 558808 944075 := bstep (se 1 (by rfl) ⟨708056, by rfl⟩ : syracuseStep 944075 = 1416113) B1416113
theorem B944203 : Blo 558808 944203 := bstep (se 1 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 944203 = 1416305) B1416305
theorem B1599563 : Blo 558808 1599563 := bstep (se 1 (by rfl) ⟨1199672, by rfl⟩ : syracuseStep 1599563 = 2399345) B2399345
theorem B2123927 : Blo 558808 2123927 := bstep (se 1 (by rfl) ⟨1592945, by rfl⟩ : syracuseStep 2123927 = 3185891) B3185891
theorem B944345 : Blo 558808 944345 := bstep (se 2 (by rfl) ⟨354129, by rfl⟩ : syracuseStep 944345 = 708259) B708259
theorem B4253957 : Blo 558808 4253957 := bstep (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) B797617
theorem B9103661 : Blo 558808 9103661 := bstep (se 3 (by rfl) ⟨1706936, by rfl⟩ : syracuseStep 9103661 = 3413873) B3413873
theorem B944473 : Blo 558808 944473 := bstep (se 2 (by rfl) ⟨354177, by rfl⟩ : syracuseStep 944473 = 708355) B708355
theorem B4221335 : Blo 558808 4221335 := bstep (se 1 (by rfl) ⟨3166001, by rfl⟩ : syracuseStep 4221335 = 6332003) B6332003
theorem B1894859 : Blo 558808 1894859 := bstep (se 1 (by rfl) ⟨1421144, by rfl⟩ : syracuseStep 1894859 = 2842289) B2842289
theorem B1895129 : Blo 558808 1895129 := bstep (se 2 (by rfl) ⟨710673, by rfl⟩ : syracuseStep 1895129 = 1421347) B1421347
theorem B945047 : Blo 558808 945047 := bstep (se 1 (by rfl) ⟨708785, by rfl⟩ : syracuseStep 945047 = 1417571) B1417571
theorem B945175 : Blo 558808 945175 := bstep (se 1 (by rfl) ⟨708881, by rfl⟩ : syracuseStep 945175 = 1417763) B1417763
theorem B1010711 : Blo 558808 1010711 := bstep (se 1 (by rfl) ⟨758033, by rfl⟩ : syracuseStep 1010711 = 1516067) B1516067
theorem B2387009 : Blo 558808 2387009 := bstep (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) B1790257
theorem B2125187 : Blo 558808 2125187 := bstep (se 1 (by rfl) ⟨1593890, by rfl⟩ : syracuseStep 2125187 = 3187781) B3187781
theorem B1895831 : Blo 558808 1895831 := bstep (se 1 (by rfl) ⟨1421873, by rfl⟩ : syracuseStep 1895831 = 2843747) B2843747
theorem B2846339 : Blo 558808 2846339 := bstep (se 1 (by rfl) ⟨2134754, by rfl⟩ : syracuseStep 2846339 = 4269509) B4269509
theorem B945803 : Blo 558808 945803 := bstep (se 1 (by rfl) ⟨709352, by rfl⟩ : syracuseStep 945803 = 1418705) B1418705
theorem B2420375 : Blo 558808 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B1601203 : Blo 558808 1601203 := bstep (se 1 (by rfl) ⟨1200902, by rfl⟩ : syracuseStep 1601203 = 2401805) B2401805
theorem B6811397 : Blo 558808 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B945931 : Blo 558808 945931 := bstep (se 1 (by rfl) ⟨709448, by rfl⟩ : syracuseStep 945931 = 1418897) B1418897
theorem B1699735 : Blo 558808 1699735 := bstep (se 1 (by rfl) ⟨1274801, by rfl⟩ : syracuseStep 1699735 = 2549603) B2549603
theorem B946073 : Blo 558808 946073 := bstep (se 2 (by rfl) ⟨354777, by rfl⟩ : syracuseStep 946073 = 709555) B709555
theorem B1896371 : Blo 558808 1896371 := bstep (se 1 (by rfl) ⟨1422278, by rfl⟩ : syracuseStep 1896371 = 2844557) B2844557
theorem B946201 : Blo 558808 946201 := bstep (se 2 (by rfl) ⟨354825, by rfl⟩ : syracuseStep 946201 = 709651) B709651
theorem B1896641 : Blo 558808 1896641 := bstep (se 2 (by rfl) ⟨711240, by rfl⟩ : syracuseStep 1896641 = 1422481) B1422481
theorem B946775 : Blo 558808 946775 := bstep (se 1 (by rfl) ⟨710081, by rfl⟩ : syracuseStep 946775 = 1420163) B1420163
theorem B4256387 : Blo 558808 4256387 := bstep (se 1 (by rfl) ⟨3192290, by rfl⟩ : syracuseStep 4256387 = 6384581) B6384581
theorem B2388683 : Blo 558808 2388683 := bstep (se 1 (by rfl) ⟨1791512, by rfl⟩ : syracuseStep 2388683 = 3583025) B3583025
theorem B1602251 : Blo 558808 1602251 := bstep (se 1 (by rfl) ⟨1201688, by rfl⟩ : syracuseStep 1602251 = 2403377) B2403377
theorem B7172813 : Blo 558808 7172813 := bstep (se 3 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 7172813 = 2689805) B2689805
theorem B946903 : Blo 558808 946903 := bstep (se 1 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 946903 = 1420355) B1420355
theorem B1012441 : Blo 558808 1012441 := bstep (se 2 (by rfl) ⟨379665, by rfl⟩ : syracuseStep 1012441 = 759331) B759331
theorem B1897181 : Blo 558808 1897181 := bstep (se 3 (by rfl) ⟨355721, by rfl⟩ : syracuseStep 1897181 = 711443) B711443
theorem B3601169 : Blo 558808 3601169 := bstep (se 2 (by rfl) ⟨1350438, by rfl⟩ : syracuseStep 3601169 = 2700877) B2700877
theorem B1700683 : Blo 558808 1700683 := bstep (se 1 (by rfl) ⟨1275512, by rfl⟩ : syracuseStep 1700683 = 2551025) B2551025
theorem B1013003 : Blo 558808 1013003 := bstep (se 1 (by rfl) ⟨759752, by rfl⟩ : syracuseStep 1013003 = 1519505) B1519505
theorem B947531 : Blo 558808 947531 := bstep (se 1 (by rfl) ⟨710648, by rfl⟩ : syracuseStep 947531 = 1421297) B1421297
theorem B1078679 : Blo 558808 1078679 := bstep (se 1 (by rfl) ⟨809009, by rfl⟩ : syracuseStep 1078679 = 1618019) B1618019
theorem B5174705 : Blo 558808 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B947659 : Blo 558808 947659 := bstep (se 1 (by rfl) ⟨710744, by rfl⟩ : syracuseStep 947659 = 1421489) B1421489
theorem B947801 : Blo 558808 947801 := bstep (se 2 (by rfl) ⟨355425, by rfl⟩ : syracuseStep 947801 = 710851) B710851
theorem B947929 : Blo 558808 947929 := bstep (se 2 (by rfl) ⟨355473, by rfl⟩ : syracuseStep 947929 = 710947) B710947
theorem B1013465 : Blo 558808 1013465 := bstep (se 2 (by rfl) ⟨380049, by rfl⟩ : syracuseStep 1013465 = 760099) B760099
theorem B9565937 : Blo 558808 9565937 := bstep (se 2 (by rfl) ⟨3587226, by rfl⟩ : syracuseStep 9565937 = 7174453) B7174453
theorem B1898315 : Blo 558808 1898315 := bstep (se 1 (by rfl) ⟨1423736, by rfl⟩ : syracuseStep 1898315 = 2847473) B2847473
theorem B15333299 : Blo 558808 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B2389981 : Blo 558808 2389981 := bstep (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) B896243
theorem B21493835 : Blo 558808 21493835 := bstep (se 1 (by rfl) ⟨16120376, by rfl⟩ : syracuseStep 21493835 = 32240753) B32240753
theorem B1898585 : Blo 558808 1898585 := bstep (se 2 (by rfl) ⟨711969, by rfl⟩ : syracuseStep 1898585 = 1423939) B1423939
theorem B948503 : Blo 558808 948503 := bstep (se 1 (by rfl) ⟨711377, by rfl⟩ : syracuseStep 948503 = 1422755) B1422755
theorem B1014041 : Blo 558808 1014041 := bstep (se 2 (by rfl) ⟨380265, by rfl⟩ : syracuseStep 1014041 = 760531) B760531
theorem B2390323 : Blo 558808 2390323 := bstep (se 1 (by rfl) ⟨1792742, by rfl⟩ : syracuseStep 2390323 = 3585485) B3585485
theorem B8092021 : Blo 558808 8092021 := bstep (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) B758627
theorem B948631 : Blo 558808 948631 := bstep (se 1 (by rfl) ⟨711473, by rfl⟩ : syracuseStep 948631 = 1422947) B1422947
theorem B2128301 : Blo 558808 2128301 := bstep (se 3 (by rfl) ⟨399056, by rfl⟩ : syracuseStep 2128301 = 798113) B798113
theorem B2882141 : Blo 558808 2882141 := bstep (se 3 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 2882141 = 1080803) B1080803
theorem B1899287 : Blo 558808 1899287 := bstep (se 1 (by rfl) ⟨1424465, by rfl⟩ : syracuseStep 1899287 = 2848931) B2848931
theorem B2161667 : Blo 558808 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B949259 : Blo 558808 949259 := bstep (se 1 (by rfl) ⟨711944, by rfl⟩ : syracuseStep 949259 = 1423889) B1423889
theorem B1801291 : Blo 558808 1801291 := bstep (se 1 (by rfl) ⟨1350968, by rfl⟩ : syracuseStep 1801291 = 2701937) B2701937
theorem B3636355 : Blo 558808 3636355 := bstep (se 1 (by rfl) ⟨2727266, by rfl⟩ : syracuseStep 3636355 = 5454533) B5454533
theorem B949387 : Blo 558808 949387 := bstep (se 1 (by rfl) ⟨712040, by rfl⟩ : syracuseStep 949387 = 1424081) B1424081
theorem B2129075 : Blo 558808 2129075 := bstep (se 1 (by rfl) ⟨1596806, by rfl⟩ : syracuseStep 2129075 = 3193613) B3193613
theorem B949529 : Blo 558808 949529 := bstep (se 2 (by rfl) ⟨356073, by rfl⟩ : syracuseStep 949529 = 712147) B712147
theorem B3833219 : Blo 558808 3833219 := bstep (se 1 (by rfl) ⟨2874914, by rfl⟩ : syracuseStep 3833219 = 5749829) B5749829
theorem B949657 : Blo 558808 949657 := bstep (se 2 (by rfl) ⟨356121, by rfl⟩ : syracuseStep 949657 = 712243) B712243
theorem B1343155 : Blo 558808 1343155 := bstep (se 1 (by rfl) ⟨1007366, by rfl⟩ : syracuseStep 1343155 = 2014733) B2014733
theorem B11501297 : Blo 558808 11501297 := bstep (se 2 (by rfl) ⟨4312986, by rfl⟩ : syracuseStep 11501297 = 8625973) B8625973
theorem B4259789 : Blo 558808 4259789 := bstep (se 3 (by rfl) ⟨798710, by rfl⟩ : syracuseStep 4259789 = 1597421) B1597421
theorem B5537803 : Blo 558808 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B1704089 : Blo 558808 1704089 := bstep (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) B1278067
theorem B1704311 : Blo 558808 1704311 := bstep (se 1 (by rfl) ⟨1278233, by rfl⟩ : syracuseStep 1704311 = 2556467) B2556467
theorem B852751 : Blo 558808 852751 := bstep (se 1 (by rfl) ⟨639563, by rfl⟩ : syracuseStep 852751 = 1279127) B1279127
theorem B6456179 : Blo 558808 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B4260761 : Blo 558808 4260761 := bstep (se 2 (by rfl) ⟨1597785, by rfl⟩ : syracuseStep 4260761 = 3195571) B3195571
theorem B6161645 : Blo 558808 6161645 := bstep (se 3 (by rfl) ⟨1155308, by rfl⟩ : syracuseStep 6161645 = 2310617) B2310617
theorem B3409451 : Blo 558808 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B2688713 : Blo 558808 2688713 := bstep (se 2 (by rfl) ⟨1008267, by rfl⟩ : syracuseStep 2688713 = 2016535) B2016535
theorem B558855 : Blo 558808 558855 := bstep (se 1 (by rfl) ⟨419141, by rfl⟩ : syracuseStep 558855 = 838283) B838283
theorem B558863 : Blo 558808 558863 := bstep (se 1 (by rfl) ⟨419147, by rfl⟩ : syracuseStep 558863 = 838295) B838295
theorem B558907 : Blo 558808 558907 := bstep (se 1 (by rfl) ⟨419180, by rfl⟩ : syracuseStep 558907 = 838361) B838361
theorem B558983 : Blo 558808 558983 := bstep (se 1 (by rfl) ⟨419237, by rfl⟩ : syracuseStep 558983 = 838475) B838475
theorem B558991 : Blo 558808 558991 := bstep (se 1 (by rfl) ⟨419243, by rfl⟩ : syracuseStep 558991 = 838487) B838487
theorem B559035 : Blo 558808 559035 := bstep (se 1 (by rfl) ⟨419276, by rfl⟩ : syracuseStep 559035 = 838553) B838553
theorem B1345481 : Blo 558808 1345481 := bstep (se 2 (by rfl) ⟨504555, by rfl⟩ : syracuseStep 1345481 = 1009111) B1009111
theorem B559111 : Blo 558808 559111 := bstep (se 1 (by rfl) ⟨419333, by rfl⟩ : syracuseStep 559111 = 838667) B838667
theorem B559119 : Blo 558808 559119 := bstep (se 1 (by rfl) ⟨419339, by rfl⟩ : syracuseStep 559119 = 838679) B838679
theorem B559163 : Blo 558808 559163 := bstep (se 1 (by rfl) ⟨419372, by rfl⟩ : syracuseStep 559163 = 838745) B838745
theorem B559239 : Blo 558808 559239 := bstep (se 1 (by rfl) ⟨419429, by rfl⟩ : syracuseStep 559239 = 838859) B838859
theorem B559247 : Blo 558808 559247 := bstep (se 1 (by rfl) ⟨419435, by rfl⟩ : syracuseStep 559247 = 838871) B838871
theorem B559291 : Blo 558808 559291 := bstep (se 1 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 559291 = 838937) B838937
theorem B559367 : Blo 558808 559367 := bstep (se 1 (by rfl) ⟨419525, by rfl⟩ : syracuseStep 559367 = 839051) B839051
theorem B559375 : Blo 558808 559375 := bstep (se 1 (by rfl) ⟨419531, by rfl⟩ : syracuseStep 559375 = 839063) B839063
theorem B559419 : Blo 558808 559419 := bstep (se 1 (by rfl) ⟨419564, by rfl⟩ : syracuseStep 559419 = 839129) B839129
theorem B559495 : Blo 558808 559495 := bstep (se 1 (by rfl) ⟨419621, by rfl⟩ : syracuseStep 559495 = 839243) B839243
theorem B559503 : Blo 558808 559503 := bstep (se 1 (by rfl) ⟨419627, by rfl⟩ : syracuseStep 559503 = 839255) B839255
theorem B559547 : Blo 558808 559547 := bstep (se 1 (by rfl) ⟨419660, by rfl⟩ : syracuseStep 559547 = 839321) B839321
theorem B559623 : Blo 558808 559623 := bstep (se 1 (by rfl) ⟨419717, by rfl⟩ : syracuseStep 559623 = 839435) B839435
theorem B559631 : Blo 558808 559631 := bstep (se 1 (by rfl) ⟨419723, by rfl⟩ : syracuseStep 559631 = 839447) B839447
theorem B559675 : Blo 558808 559675 := bstep (se 1 (by rfl) ⟨419756, by rfl⟩ : syracuseStep 559675 = 839513) B839513
theorem B559751 : Blo 558808 559751 := bstep (se 1 (by rfl) ⟨419813, by rfl⟩ : syracuseStep 559751 = 839627) B839627
theorem B559759 : Blo 558808 559759 := bstep (se 1 (by rfl) ⟨419819, by rfl⟩ : syracuseStep 559759 = 839639) B839639
theorem B559803 : Blo 558808 559803 := bstep (se 1 (by rfl) ⟨419852, by rfl⟩ : syracuseStep 559803 = 839705) B839705
theorem B756487 : Blo 558808 756487 := bstep (se 1 (by rfl) ⟨567365, by rfl⟩ : syracuseStep 756487 = 1134731) B1134731
theorem B559879 : Blo 558808 559879 := bstep (se 1 (by rfl) ⟨419909, by rfl⟩ : syracuseStep 559879 = 839819) B839819
theorem B559887 : Blo 558808 559887 := bstep (se 1 (by rfl) ⟨419915, by rfl⟩ : syracuseStep 559887 = 839831) B839831
theorem B4262705 : Blo 558808 4262705 := bstep (se 2 (by rfl) ⟨1598514, by rfl⟩ : syracuseStep 4262705 = 3197029) B3197029
theorem B559931 : Blo 558808 559931 := bstep (se 1 (by rfl) ⟨419948, by rfl⟩ : syracuseStep 559931 = 839897) B839897
theorem B560007 : Blo 558808 560007 := bstep (se 1 (by rfl) ⟨420005, by rfl⟩ : syracuseStep 560007 = 840011) B840011
theorem B560015 : Blo 558808 560015 := bstep (se 1 (by rfl) ⟨420011, by rfl⟩ : syracuseStep 560015 = 840023) B840023
theorem B560059 : Blo 558808 560059 := bstep (se 1 (by rfl) ⟨420044, by rfl⟩ : syracuseStep 560059 = 840089) B840089
theorem B560135 : Blo 558808 560135 := bstep (se 1 (by rfl) ⟨420101, by rfl⟩ : syracuseStep 560135 = 840203) B840203
theorem B14355467 : Blo 558808 14355467 := bstep (se 1 (by rfl) ⟨10766600, by rfl⟩ : syracuseStep 14355467 = 21533201) B21533201
theorem B560143 : Blo 558808 560143 := bstep (se 1 (by rfl) ⟨420107, by rfl⟩ : syracuseStep 560143 = 840215) B840215
theorem B560187 : Blo 558808 560187 := bstep (se 1 (by rfl) ⟨420140, by rfl⟩ : syracuseStep 560187 = 840281) B840281
theorem B560263 : Blo 558808 560263 := bstep (se 1 (by rfl) ⟨420197, by rfl⟩ : syracuseStep 560263 = 840395) B840395
theorem B560271 : Blo 558808 560271 := bstep (se 1 (by rfl) ⟨420203, by rfl⟩ : syracuseStep 560271 = 840407) B840407
theorem B1707193 : Blo 558808 1707193 := bstep (se 2 (by rfl) ⟨640197, by rfl⟩ : syracuseStep 1707193 = 1280395) B1280395
theorem B560315 : Blo 558808 560315 := bstep (se 1 (by rfl) ⟨420236, by rfl⟩ : syracuseStep 560315 = 840473) B840473
theorem B560391 : Blo 558808 560391 := bstep (se 1 (by rfl) ⟨420293, by rfl⟩ : syracuseStep 560391 = 840587) B840587
theorem B560399 : Blo 558808 560399 := bstep (se 1 (by rfl) ⟨420299, by rfl⟩ : syracuseStep 560399 = 840599) B840599
theorem B560443 : Blo 558808 560443 := bstep (se 1 (by rfl) ⟨420332, by rfl⟩ : syracuseStep 560443 = 840665) B840665
theorem B560519 : Blo 558808 560519 := bstep (se 1 (by rfl) ⟨420389, by rfl⟩ : syracuseStep 560519 = 840779) B840779
theorem B560527 : Blo 558808 560527 := bstep (se 1 (by rfl) ⟨420395, by rfl⟩ : syracuseStep 560527 = 840791) B840791
theorem B560571 : Blo 558808 560571 := bstep (se 1 (by rfl) ⟨420428, by rfl⟩ : syracuseStep 560571 = 840857) B840857
theorem B757255 : Blo 558808 757255 := bstep (se 1 (by rfl) ⟨567941, by rfl⟩ : syracuseStep 757255 = 1135883) B1135883
theorem B560647 : Blo 558808 560647 := bstep (se 1 (by rfl) ⟨420485, by rfl⟩ : syracuseStep 560647 = 840971) B840971
theorem B560655 : Blo 558808 560655 := bstep (se 1 (by rfl) ⟨420491, by rfl⟩ : syracuseStep 560655 = 840983) B840983
theorem B560699 : Blo 558808 560699 := bstep (se 1 (by rfl) ⟨420524, by rfl⟩ : syracuseStep 560699 = 841049) B841049
theorem B2887235 : Blo 558808 2887235 := bstep (se 1 (by rfl) ⟨2165426, by rfl⟩ : syracuseStep 2887235 = 4330853) B4330853
theorem B560775 : Blo 558808 560775 := bstep (se 1 (by rfl) ⟨420581, by rfl⟩ : syracuseStep 560775 = 841163) B841163
theorem B560783 : Blo 558808 560783 := bstep (se 1 (by rfl) ⟨420587, by rfl⟩ : syracuseStep 560783 = 841175) B841175
theorem B560827 : Blo 558808 560827 := bstep (se 1 (by rfl) ⟨420620, by rfl⟩ : syracuseStep 560827 = 841241) B841241
theorem B1281737 : Blo 558808 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B5377765 : Blo 558808 5377765 := bstep (se 4 (by rfl) ⟨504165, by rfl⟩ : syracuseStep 5377765 = 1008331) B1008331
theorem B560903 : Blo 558808 560903 := bstep (se 1 (by rfl) ⟨420677, by rfl⟩ : syracuseStep 560903 = 841355) B841355
theorem B560911 : Blo 558808 560911 := bstep (se 1 (by rfl) ⟨420683, by rfl⟩ : syracuseStep 560911 = 841367) B841367
theorem B560955 : Blo 558808 560955 := bstep (se 1 (by rfl) ⟨420716, by rfl⟩ : syracuseStep 560955 = 841433) B841433
theorem B561031 : Blo 558808 561031 := bstep (se 1 (by rfl) ⟨420773, by rfl⟩ : syracuseStep 561031 = 841547) B841547
theorem B561039 : Blo 558808 561039 := bstep (se 1 (by rfl) ⟨420779, by rfl⟩ : syracuseStep 561039 = 841559) B841559
theorem B3411857 : Blo 558808 3411857 := bstep (se 2 (by rfl) ⟨1279446, by rfl⟩ : syracuseStep 3411857 = 2558893) B2558893
theorem B561083 : Blo 558808 561083 := bstep (se 1 (by rfl) ⟨420812, by rfl⟩ : syracuseStep 561083 = 841625) B841625
theorem B561159 : Blo 558808 561159 := bstep (se 1 (by rfl) ⟨420869, by rfl⟩ : syracuseStep 561159 = 841739) B841739
theorem B561167 : Blo 558808 561167 := bstep (se 1 (by rfl) ⟨420875, by rfl⟩ : syracuseStep 561167 = 841751) B841751
theorem B561211 : Blo 558808 561211 := bstep (se 1 (by rfl) ⟨420908, by rfl⟩ : syracuseStep 561211 = 841817) B841817
theorem B561287 : Blo 558808 561287 := bstep (se 1 (by rfl) ⟨420965, by rfl⟩ : syracuseStep 561287 = 841931) B841931
theorem B561295 : Blo 558808 561295 := bstep (se 1 (by rfl) ⟨420971, by rfl⟩ : syracuseStep 561295 = 841943) B841943
theorem B561339 : Blo 558808 561339 := bstep (se 1 (by rfl) ⟨421004, by rfl⟩ : syracuseStep 561339 = 842009) B842009
theorem B561415 : Blo 558808 561415 := bstep (se 1 (by rfl) ⟨421061, by rfl⟩ : syracuseStep 561415 = 842123) B842123
theorem B2691343 : Blo 558808 2691343 := bstep (se 1 (by rfl) ⟨2018507, by rfl⟩ : syracuseStep 2691343 = 4037015) B4037015
theorem B561423 : Blo 558808 561423 := bstep (se 1 (by rfl) ⟨421067, by rfl⟩ : syracuseStep 561423 = 842135) B842135
theorem B561467 : Blo 558808 561467 := bstep (se 1 (by rfl) ⟨421100, by rfl⟩ : syracuseStep 561467 = 842201) B842201
theorem B1511741 : Blo 558808 1511741 := bstep (se 3 (by rfl) ⟨283451, by rfl⟩ : syracuseStep 1511741 = 566903) B566903
theorem B561543 : Blo 558808 561543 := bstep (se 1 (by rfl) ⟨421157, by rfl⟩ : syracuseStep 561543 = 842315) B842315
theorem B561551 : Blo 558808 561551 := bstep (se 1 (by rfl) ⟨421163, by rfl⟩ : syracuseStep 561551 = 842327) B842327
theorem B561595 : Blo 558808 561595 := bstep (se 1 (by rfl) ⟨421196, by rfl⟩ : syracuseStep 561595 = 842393) B842393
theorem B3281411 : Blo 558808 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B561671 : Blo 558808 561671 := bstep (se 1 (by rfl) ⟨421253, by rfl⟩ : syracuseStep 561671 = 842507) B842507
theorem B561679 : Blo 558808 561679 := bstep (se 1 (by rfl) ⟨421259, by rfl⟩ : syracuseStep 561679 = 842519) B842519
theorem B561723 : Blo 558808 561723 := bstep (se 1 (by rfl) ⟨421292, by rfl⟩ : syracuseStep 561723 = 842585) B842585
theorem B561799 : Blo 558808 561799 := bstep (se 1 (by rfl) ⟨421349, by rfl⟩ : syracuseStep 561799 = 842699) B842699
theorem B561807 : Blo 558808 561807 := bstep (se 1 (by rfl) ⟨421355, by rfl⟩ : syracuseStep 561807 = 842711) B842711
theorem B561851 : Blo 558808 561851 := bstep (se 1 (by rfl) ⟨421388, by rfl⟩ : syracuseStep 561851 = 842777) B842777
theorem B561927 : Blo 558808 561927 := bstep (se 1 (by rfl) ⟨421445, by rfl⟩ : syracuseStep 561927 = 842891) B842891
theorem B1348363 : Blo 558808 1348363 := bstep (se 1 (by rfl) ⟨1011272, by rfl⟩ : syracuseStep 1348363 = 2022545) B2022545
theorem B1643275 : Blo 558808 1643275 := bstep (se 1 (by rfl) ⟨1232456, by rfl⟩ : syracuseStep 1643275 = 2464913) B2464913
theorem B561935 : Blo 558808 561935 := bstep (se 1 (by rfl) ⟨421451, by rfl⟩ : syracuseStep 561935 = 842903) B842903
theorem B561979 : Blo 558808 561979 := bstep (se 1 (by rfl) ⟨421484, by rfl⟩ : syracuseStep 561979 = 842969) B842969
theorem B562055 : Blo 558808 562055 := bstep (se 1 (by rfl) ⟨421541, by rfl⟩ : syracuseStep 562055 = 843083) B843083
theorem B562063 : Blo 558808 562063 := bstep (se 1 (by rfl) ⟨421547, by rfl⟩ : syracuseStep 562063 = 843095) B843095
theorem B2134937 : Blo 558808 2134937 := bstep (se 2 (by rfl) ⟨800601, by rfl⟩ : syracuseStep 2134937 = 1601203) B1601203
theorem B6394787 : Blo 558808 6394787 := bstep (se 1 (by rfl) ⟨4796090, by rfl⟩ : syracuseStep 6394787 = 9592181) B9592181
theorem B14554037 : Blo 558808 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B562107 : Blo 558808 562107 := bstep (se 1 (by rfl) ⟨421580, by rfl⟩ : syracuseStep 562107 = 843161) B843161
theorem B562183 : Blo 558808 562183 := bstep (se 1 (by rfl) ⟨421637, by rfl⟩ : syracuseStep 562183 = 843275) B843275
theorem B562191 : Blo 558808 562191 := bstep (se 1 (by rfl) ⟨421643, by rfl⟩ : syracuseStep 562191 = 843287) B843287
theorem B562235 : Blo 558808 562235 := bstep (se 1 (by rfl) ⟨421676, by rfl⟩ : syracuseStep 562235 = 843353) B843353
theorem B562311 : Blo 558808 562311 := bstep (se 1 (by rfl) ⟨421733, by rfl⟩ : syracuseStep 562311 = 843467) B843467
theorem B562319 : Blo 558808 562319 := bstep (se 1 (by rfl) ⟨421739, by rfl⟩ : syracuseStep 562319 = 843479) B843479
theorem B562363 : Blo 558808 562363 := bstep (se 1 (by rfl) ⟨421772, by rfl⟩ : syracuseStep 562363 = 843545) B843545
theorem B2266313 : Blo 558808 2266313 := bstep (se 2 (by rfl) ⟨849867, by rfl⟩ : syracuseStep 2266313 = 1699735) B1699735
theorem B562439 : Blo 558808 562439 := bstep (se 1 (by rfl) ⟨421829, by rfl⟩ : syracuseStep 562439 = 843659) B843659
theorem B562447 : Blo 558808 562447 := bstep (se 1 (by rfl) ⟨421835, by rfl⟩ : syracuseStep 562447 = 843671) B843671
theorem B2692403 : Blo 558808 2692403 := bstep (se 1 (by rfl) ⟨2019302, by rfl⟩ : syracuseStep 2692403 = 4038605) B4038605
theorem B562491 : Blo 558808 562491 := bstep (se 1 (by rfl) ⟨421868, by rfl⟩ : syracuseStep 562491 = 843737) B843737
theorem B562567 : Blo 558808 562567 := bstep (se 1 (by rfl) ⟨421925, by rfl⟩ : syracuseStep 562567 = 843851) B843851
theorem B562575 : Blo 558808 562575 := bstep (se 1 (by rfl) ⟨421931, by rfl⟩ : syracuseStep 562575 = 843863) B843863
theorem B562619 : Blo 558808 562619 := bstep (se 1 (by rfl) ⟨421964, by rfl⟩ : syracuseStep 562619 = 843929) B843929
theorem B562695 : Blo 558808 562695 := bstep (se 1 (by rfl) ⟨422021, by rfl⟩ : syracuseStep 562695 = 844043) B844043
theorem B562703 : Blo 558808 562703 := bstep (se 1 (by rfl) ⟨422027, by rfl⟩ : syracuseStep 562703 = 844055) B844055
theorem B562747 : Blo 558808 562747 := bstep (se 1 (by rfl) ⟨422060, by rfl⟩ : syracuseStep 562747 = 844121) B844121
theorem B1709687 : Blo 558808 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B2692865 : Blo 558808 2692865 := bstep (se 2 (by rfl) ⟨1009824, by rfl⟩ : syracuseStep 2692865 = 2019649) B2019649
theorem B2693017 : Blo 558808 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B5478347 : Blo 558808 5478347 := bstep (se 1 (by rfl) ⟨4108760, by rfl⟩ : syracuseStep 5478347 = 8217521) B8217521
theorem B2431043 : Blo 558808 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B5740631 : Blo 558808 5740631 := bstep (se 1 (by rfl) ⟨4305473, by rfl⟩ : syracuseStep 5740631 = 8610947) B8610947
theorem B1513559 : Blo 558808 1513559 := bstep (se 1 (by rfl) ⟨1135169, by rfl⟩ : syracuseStep 1513559 = 2270339) B2270339
theorem B1415303 : Blo 558808 1415303 := bstep (se 1 (by rfl) ⟨1061477, by rfl⟩ : syracuseStep 1415303 = 2122955) B2122955
theorem B628879 : Blo 558808 628879 := bstep (se 1 (by rfl) ⟨471659, by rfl⟩ : syracuseStep 628879 = 943319) B943319
theorem B1415353 : Blo 558808 1415353 := bstep (se 2 (by rfl) ⟨530757, by rfl⟩ : syracuseStep 1415353 = 1061515) B1061515
theorem B1349921 : Blo 558808 1349921 := bstep (se 2 (by rfl) ⟨506220, by rfl⟩ : syracuseStep 1349921 = 1012441) B1012441
theorem B760207 : Blo 558808 760207 := bstep (se 1 (by rfl) ⟨570155, by rfl⟩ : syracuseStep 760207 = 1140311) B1140311
theorem B1645171 : Blo 558808 1645171 := bstep (se 1 (by rfl) ⟨1233878, by rfl⟩ : syracuseStep 1645171 = 2467757) B2467757
theorem B629383 : Blo 558808 629383 := bstep (se 1 (by rfl) ⟨472037, by rfl⟩ : syracuseStep 629383 = 944075) B944075
theorem B1415951 : Blo 558808 1415951 := bstep (se 1 (by rfl) ⟨1061963, by rfl⟩ : syracuseStep 1415951 = 2123927) B2123927
theorem B629563 : Blo 558808 629563 := bstep (se 1 (by rfl) ⟨472172, by rfl⟩ : syracuseStep 629563 = 944345) B944345
theorem B6069107 : Blo 558808 6069107 := bstep (se 1 (by rfl) ⟨4551830, by rfl⟩ : syracuseStep 6069107 = 9103661) B9103661
theorem B2694035 : Blo 558808 2694035 := bstep (se 1 (by rfl) ⟨2020526, by rfl⟩ : syracuseStep 2694035 = 4041053) B4041053
theorem B630031 : Blo 558808 630031 := bstep (se 1 (by rfl) ⟨472523, by rfl⟩ : syracuseStep 630031 = 945047) B945047
theorem B1416649 : Blo 558808 1416649 := bstep (se 2 (by rfl) ⟨531243, by rfl⟩ : syracuseStep 1416649 = 1062487) B1062487
theorem B6495709 : Blo 558808 6495709 := bstep (se 3 (by rfl) ⟨1217945, by rfl⟩ : syracuseStep 6495709 = 2435891) B2435891
theorem B1416791 : Blo 558808 1416791 := bstep (se 1 (by rfl) ⟨1062593, by rfl⟩ : syracuseStep 1416791 = 2125187) B2125187
theorem B630535 : Blo 558808 630535 := bstep (se 1 (by rfl) ⟨472901, by rfl⟩ : syracuseStep 630535 = 945803) B945803
theorem B630715 : Blo 558808 630715 := bstep (se 1 (by rfl) ⟨473036, by rfl⟩ : syracuseStep 630715 = 946073) B946073
theorem B3186641 : Blo 558808 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B631183 : Blo 558808 631183 := bstep (se 1 (by rfl) ⟨473387, by rfl⟩ : syracuseStep 631183 = 946775) B946775
theorem B3187097 : Blo 558808 3187097 := bstep (se 2 (by rfl) ⟨1195161, by rfl⟩ : syracuseStep 3187097 = 2390323) B2390323
theorem B10789361 : Blo 558808 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B2400779 : Blo 558808 2400779 := bstep (se 1 (by rfl) ⟨1800584, by rfl⟩ : syracuseStep 2400779 = 3601169) B3601169
theorem B631687 : Blo 558808 631687 := bstep (se 1 (by rfl) ⟨473765, by rfl⟩ : syracuseStep 631687 = 947531) B947531
theorem B3449803 : Blo 558808 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B631867 : Blo 558808 631867 := bstep (se 1 (by rfl) ⟨473900, by rfl⟩ : syracuseStep 631867 = 947801) B947801
theorem B795835 : Blo 558808 795835 := bstep (se 1 (by rfl) ⟨596876, by rfl⟩ : syracuseStep 795835 = 1193753) B1193753
theorem B14329223 : Blo 558808 14329223 := bstep (se 1 (by rfl) ⟨10746917, by rfl⟩ : syracuseStep 14329223 = 21493835) B21493835
theorem B2401721 : Blo 558808 2401721 := bstep (se 2 (by rfl) ⟨900645, by rfl⟩ : syracuseStep 2401721 = 1801291) B1801291
theorem B632335 : Blo 558808 632335 := bstep (se 1 (by rfl) ⟨474251, by rfl⟩ : syracuseStep 632335 = 948503) B948503
theorem B1418867 : Blo 558808 1418867 := bstep (se 1 (by rfl) ⟨1064150, by rfl⟩ : syracuseStep 1418867 = 2128301) B2128301
theorem B24323813 : Blo 558808 24323813 := bstep (se 4 (by rfl) ⟨2280357, by rfl⟩ : syracuseStep 24323813 = 4560715) B4560715
theorem B599815 : Blo 558808 599815 := bstep (se 1 (by rfl) ⟨449861, by rfl⟩ : syracuseStep 599815 = 899723) B899723
theorem B632839 : Blo 558808 632839 := bstep (se 1 (by rfl) ⟨474629, by rfl⟩ : syracuseStep 632839 = 949259) B949259
theorem B796729 : Blo 558808 796729 := bstep (se 2 (by rfl) ⟨298773, by rfl⟩ : syracuseStep 796729 = 597547) B597547
theorem B1419383 : Blo 558808 1419383 := bstep (se 1 (by rfl) ⟨1064537, by rfl⟩ : syracuseStep 1419383 = 2129075) B2129075
theorem B633019 : Blo 558808 633019 := bstep (se 1 (by rfl) ⟨474764, by rfl⟩ : syracuseStep 633019 = 949529) B949529
theorem B4270481 : Blo 558808 4270481 := bstep (se 2 (by rfl) ⟨1601430, by rfl⟩ : syracuseStep 4270481 = 3202861) B3202861
theorem B1420375 : Blo 558808 1420375 := bstep (se 1 (by rfl) ⟨1065281, by rfl⟩ : syracuseStep 1420375 = 2130563) B2130563
theorem B797959 : Blo 558808 797959 := bstep (se 1 (by rfl) ⟨598469, by rfl⟩ : syracuseStep 797959 = 1196939) B1196939
theorem B3648827 : Blo 558808 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B1420679 : Blo 558808 1420679 := bstep (se 1 (by rfl) ⟨1065509, by rfl⟩ : syracuseStep 1420679 = 2131019) B2131019
theorem B2403719 : Blo 558808 2403719 := bstep (se 1 (by rfl) ⟨1802789, by rfl⟩ : syracuseStep 2403719 = 3605579) B3605579
theorem B1420811 : Blo 558808 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B2830139 : Blo 558808 2830139 := bstep (se 1 (by rfl) ⟨2122604, by rfl⟩ : syracuseStep 2830139 = 4245209) B4245209
theorem B1257335 : Blo 558808 1257335 := bstep (se 1 (by rfl) ⟨943001, by rfl⟩ : syracuseStep 1257335 = 1886003) B1886003
theorem B798665 : Blo 558808 798665 := bstep (se 2 (by rfl) ⟨299499, by rfl⟩ : syracuseStep 798665 = 598999) B598999
theorem B2830301 : Blo 558808 2830301 := bstep (se 3 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 2830301 = 1061363) B1061363
theorem B1421327 : Blo 558808 1421327 := bstep (se 1 (by rfl) ⟨1065995, by rfl⟩ : syracuseStep 1421327 = 2131991) B2131991
theorem B1257515 : Blo 558808 1257515 := bstep (se 1 (by rfl) ⟨943136, by rfl⟩ : syracuseStep 1257515 = 1886273) B1886273
theorem B798779 : Blo 558808 798779 := bstep (se 1 (by rfl) ⟨599084, by rfl⟩ : syracuseStep 798779 = 1198169) B1198169
theorem B1421459 : Blo 558808 1421459 := bstep (se 1 (by rfl) ⟨1066094, by rfl⟩ : syracuseStep 1421459 = 2132189) B2132189
theorem B2830625 : Blo 558808 2830625 := bstep (se 2 (by rfl) ⟨1061484, by rfl⟩ : syracuseStep 2830625 = 2122969) B2122969
theorem B2044295 : Blo 558808 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B1257875 : Blo 558808 1257875 := bstep (se 1 (by rfl) ⟨943406, by rfl⟩ : syracuseStep 1257875 = 1886813) B1886813
theorem B1257929 : Blo 558808 1257929 := bstep (se 2 (by rfl) ⟨471723, by rfl⟩ : syracuseStep 1257929 = 943447) B943447
theorem B897551 : Blo 558808 897551 := bstep (se 1 (by rfl) ⟨673163, by rfl⟩ : syracuseStep 897551 = 1346327) B1346327
theorem B1061561 : Blo 558808 1061561 := bstep (se 2 (by rfl) ⟨398085, by rfl⟩ : syracuseStep 1061561 = 796171) B796171
theorem B799417 : Blo 558808 799417 := bstep (se 2 (by rfl) ⟨299781, by rfl⟩ : syracuseStep 799417 = 599563) B599563
theorem B4272911 : Blo 558808 4272911 := bstep (se 1 (by rfl) ⟨3204683, by rfl⟩ : syracuseStep 4272911 = 6409367) B6409367
theorem B16135139 : Blo 558808 16135139 := bstep (se 1 (by rfl) ⟨12101354, by rfl⟩ : syracuseStep 16135139 = 24202709) B24202709
theorem B1061903 : Blo 558808 1061903 := bstep (se 1 (by rfl) ⟨796427, by rfl⟩ : syracuseStep 1061903 = 1592855) B1592855
theorem B1258631 : Blo 558808 1258631 := bstep (se 1 (by rfl) ⟨943973, by rfl⟩ : syracuseStep 1258631 = 1887947) B1887947
theorem B2831597 : Blo 558808 2831597 := bstep (se 3 (by rfl) ⟨530924, by rfl⟩ : syracuseStep 2831597 = 1061849) B1061849
theorem B1422593 : Blo 558808 1422593 := bstep (se 2 (by rfl) ⟨533472, by rfl⟩ : syracuseStep 1422593 = 1066945) B1066945
theorem B3028261 : Blo 558808 3028261 := bstep (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) B567799
theorem B1258811 : Blo 558808 1258811 := bstep (se 1 (by rfl) ⟨944108, by rfl⟩ : syracuseStep 1258811 = 1888217) B1888217
theorem B4044167 : Blo 558808 4044167 := bstep (se 1 (by rfl) ⟨3033125, by rfl⟩ : syracuseStep 4044167 = 6066251) B6066251
theorem B1258937 : Blo 558808 1258937 := bstep (se 2 (by rfl) ⟨472101, by rfl⟩ : syracuseStep 1258937 = 944203) B944203
theorem B1422967 : Blo 558808 1422967 := bstep (se 1 (by rfl) ⟨1067225, by rfl⟩ : syracuseStep 1422967 = 2134451) B2134451
theorem B1259279 : Blo 558808 1259279 := bstep (se 1 (by rfl) ⟨944459, by rfl⟩ : syracuseStep 1259279 = 1888919) B1888919
theorem B1259297 : Blo 558808 1259297 := bstep (se 2 (by rfl) ⟨472236, by rfl⟩ : syracuseStep 1259297 = 944473) B944473
theorem B5748515 : Blo 558808 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B1062715 : Blo 558808 1062715 := bstep (se 1 (by rfl) ⟨797036, by rfl⟩ : syracuseStep 1062715 = 1594073) B1594073
theorem B1062791 : Blo 558808 1062791 := bstep (se 1 (by rfl) ⟨797093, by rfl⟩ : syracuseStep 1062791 = 1594187) B1594187
theorem B2832407 : Blo 558808 2832407 := bstep (se 1 (by rfl) ⟨2124305, by rfl⟩ : syracuseStep 2832407 = 4248611) B4248611
theorem B1423403 : Blo 558808 1423403 := bstep (se 1 (by rfl) ⟨1067552, by rfl⟩ : syracuseStep 1423403 = 2135105) B2135105
theorem B1259639 : Blo 558808 1259639 := bstep (se 1 (by rfl) ⟨944729, by rfl⟩ : syracuseStep 1259639 = 1889459) B1889459
theorem B899191 : Blo 558808 899191 := bstep (se 1 (by rfl) ⟨674393, by rfl⟩ : syracuseStep 899191 = 1348787) B1348787
theorem B1063201 : Blo 558808 1063201 := bstep (se 2 (by rfl) ⟨398700, by rfl⟩ : syracuseStep 1063201 = 797401) B797401
theorem B1259819 : Blo 558808 1259819 := bstep (se 1 (by rfl) ⟨944864, by rfl⟩ : syracuseStep 1259819 = 1889729) B1889729
theorem B1915271 : Blo 558808 1915271 := bstep (se 1 (by rfl) ⟨1436453, by rfl⟩ : syracuseStep 1915271 = 2872907) B2872907
theorem B3586589 : Blo 558808 3586589 := bstep (se 3 (by rfl) ⟨672485, by rfl⟩ : syracuseStep 3586589 = 1344971) B1344971
theorem B1063543 : Blo 558808 1063543 := bstep (se 1 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 1063543 = 1595315) B1595315
theorem B1260179 : Blo 558808 1260179 := bstep (se 1 (by rfl) ⟨945134, by rfl⟩ : syracuseStep 1260179 = 1890269) B1890269
theorem B1260233 : Blo 558808 1260233 := bstep (se 2 (by rfl) ⟨472587, by rfl⟩ : syracuseStep 1260233 = 945175) B945175
theorem B3586817 : Blo 558808 3586817 := bstep (se 2 (by rfl) ⟨1345056, by rfl⟩ : syracuseStep 3586817 = 2690113) B2690113
theorem B1424243 : Blo 558808 1424243 := bstep (se 1 (by rfl) ⟨1068182, by rfl⟩ : syracuseStep 1424243 = 2136365) B2136365
theorem B1424263 : Blo 558808 1424263 := bstep (se 1 (by rfl) ⟨1068197, by rfl⟩ : syracuseStep 1424263 = 2136395) B2136395
theorem B900139 : Blo 558808 900139 := bstep (se 1 (by rfl) ⟨675104, by rfl⟩ : syracuseStep 900139 = 1350209) B1350209
theorem B1424537 : Blo 558808 1424537 := bstep (se 2 (by rfl) ⟨534201, by rfl⟩ : syracuseStep 1424537 = 1068403) B1068403
theorem B3194113 : Blo 558808 3194113 := bstep (se 2 (by rfl) ⟨1197792, by rfl⟩ : syracuseStep 3194113 = 2395585) B2395585
theorem B1260935 : Blo 558808 1260935 := bstep (se 1 (by rfl) ⟨945701, by rfl⟩ : syracuseStep 1260935 = 1891403) B1891403
theorem B7650845 : Blo 558808 7650845 := bstep (se 3 (by rfl) ⟨1434533, by rfl⟩ : syracuseStep 7650845 = 2869067) B2869067
theorem B1261115 : Blo 558808 1261115 := bstep (se 1 (by rfl) ⟨945836, by rfl⟩ : syracuseStep 1261115 = 1891673) B1891673
theorem B1621619 : Blo 558808 1621619 := bstep (se 1 (by rfl) ⟨1216214, by rfl⟩ : syracuseStep 1621619 = 2432429) B2432429
theorem B1261241 : Blo 558808 1261241 := bstep (se 2 (by rfl) ⟨472965, by rfl⟩ : syracuseStep 1261241 = 945931) B945931
theorem B3194639 : Blo 558808 3194639 := bstep (se 1 (by rfl) ⟨2395979, by rfl⟩ : syracuseStep 3194639 = 4791959) B4791959
theorem B638779 : Blo 558808 638779 := bstep (se 1 (by rfl) ⟨479084, by rfl⟩ : syracuseStep 638779 = 958169) B958169
theorem B1818503 : Blo 558808 1818503 := bstep (se 1 (by rfl) ⟨1363877, by rfl⟩ : syracuseStep 1818503 = 2727755) B2727755
theorem B8077259 : Blo 558808 8077259 := bstep (se 1 (by rfl) ⟨6057944, by rfl⟩ : syracuseStep 8077259 = 12115889) B12115889
theorem B1261583 : Blo 558808 1261583 := bstep (se 1 (by rfl) ⟨946187, by rfl⟩ : syracuseStep 1261583 = 1892375) B1892375
theorem B1261601 : Blo 558808 1261601 := bstep (se 2 (by rfl) ⟨473100, by rfl⟩ : syracuseStep 1261601 = 946201) B946201
theorem B1917047 : Blo 558808 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B1065145 : Blo 558808 1065145 := bstep (se 2 (by rfl) ⟨399429, by rfl⟩ : syracuseStep 1065145 = 798859) B798859
theorem B6078665 : Blo 558808 6078665 := bstep (se 2 (by rfl) ⟨2279499, by rfl⟩ : syracuseStep 6078665 = 4558999) B4558999
theorem B1458443 : Blo 558808 1458443 := bstep (se 1 (by rfl) ⟨1093832, by rfl⟩ : syracuseStep 1458443 = 2187665) B2187665
theorem B2277665 : Blo 558808 2277665 := bstep (se 2 (by rfl) ⟨854124, by rfl⟩ : syracuseStep 2277665 = 1708249) B1708249
theorem B1261943 : Blo 558808 1261943 := bstep (se 1 (by rfl) ⟨946457, by rfl⟩ : syracuseStep 1261943 = 1892915) B1892915
theorem B1065487 : Blo 558808 1065487 := bstep (se 1 (by rfl) ⟨799115, by rfl⟩ : syracuseStep 1065487 = 1598231) B1598231
theorem B1262123 : Blo 558808 1262123 := bstep (se 1 (by rfl) ⟨946592, by rfl⟩ : syracuseStep 1262123 = 1893185) B1893185
theorem B1262483 : Blo 558808 1262483 := bstep (se 1 (by rfl) ⟨946862, by rfl⟩ : syracuseStep 1262483 = 1893725) B1893725
theorem B1262537 : Blo 558808 1262537 := bstep (se 2 (by rfl) ⟨473451, by rfl⟩ : syracuseStep 1262537 = 946903) B946903
theorem B2835485 : Blo 558808 2835485 := bstep (se 3 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 2835485 = 1063307) B1063307
theorem B11256893 : Blo 558808 11256893 := bstep (se 3 (by rfl) ⟨2110667, by rfl⟩ : syracuseStep 11256893 = 4221335) B4221335
theorem B3196097 : Blo 558808 3196097 := bstep (se 2 (by rfl) ⟨1198536, by rfl⟩ : syracuseStep 3196097 = 2397073) B2397073
theorem B1066375 : Blo 558808 1066375 := bstep (se 1 (by rfl) ⟨799781, by rfl⟩ : syracuseStep 1066375 = 1599563) B1599563
theorem B2835971 : Blo 558808 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B1263239 : Blo 558808 1263239 := bstep (se 1 (by rfl) ⟨947429, by rfl⟩ : syracuseStep 1263239 = 1894859) B1894859
theorem B6407909 : Blo 558808 6407909 := bstep (se 4 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 6407909 = 1201483) B1201483
theorem B1263419 : Blo 558808 1263419 := bstep (se 1 (by rfl) ⟨947564, by rfl⟩ : syracuseStep 1263419 = 1895129) B1895129
theorem B1263545 : Blo 558808 1263545 := bstep (se 2 (by rfl) ⟨473829, by rfl⟩ : syracuseStep 1263545 = 947659) B947659
theorem B1886219 : Blo 558808 1886219 := bstep (se 1 (by rfl) ⟨1414664, by rfl⟩ : syracuseStep 1886219 = 2829329) B2829329
theorem B673807 : Blo 558808 673807 := bstep (se 1 (by rfl) ⟨505355, by rfl⟩ : syracuseStep 673807 = 1010711) B1010711
theorem B1591339 : Blo 558808 1591339 := bstep (se 1 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 1591339 = 2387009) B2387009
theorem B1886327 : Blo 558808 1886327 := bstep (se 1 (by rfl) ⟨1414745, by rfl⟩ : syracuseStep 1886327 = 2829491) B2829491
theorem B1263887 : Blo 558808 1263887 := bstep (se 1 (by rfl) ⟨947915, by rfl⟩ : syracuseStep 1263887 = 1895831) B1895831
theorem B1263905 : Blo 558808 1263905 := bstep (se 2 (by rfl) ⟨473964, by rfl⟩ : syracuseStep 1263905 = 947929) B947929
theorem B1591613 : Blo 558808 1591613 := bstep (se 3 (by rfl) ⟨298427, by rfl⟩ : syracuseStep 1591613 = 596855) B596855
theorem B4540931 : Blo 558808 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B838217 : Blo 558808 838217 := bstep (se 2 (by rfl) ⟨314331, by rfl⟩ : syracuseStep 838217 = 628663) B628663
theorem B1264247 : Blo 558808 1264247 := bstep (se 1 (by rfl) ⟨948185, by rfl⟩ : syracuseStep 1264247 = 1896371) B1896371
theorem B838331 : Blo 558808 838331 := bstep (se 1 (by rfl) ⟨628748, by rfl⟩ : syracuseStep 838331 = 1257497) B1257497
theorem B1886921 : Blo 558808 1886921 := bstep (se 2 (by rfl) ⟨707595, by rfl⟩ : syracuseStep 1886921 = 1415191) B1415191
theorem B838391 : Blo 558808 838391 := bstep (se 1 (by rfl) ⟨628793, by rfl⟩ : syracuseStep 838391 = 1257587) B1257587
theorem B838415 : Blo 558808 838415 := bstep (se 1 (by rfl) ⟨628811, by rfl⟩ : syracuseStep 838415 = 1257623) B1257623
theorem B1264427 : Blo 558808 1264427 := bstep (se 1 (by rfl) ⟨948320, by rfl⟩ : syracuseStep 1264427 = 1896641) B1896641
theorem B838457 : Blo 558808 838457 := bstep (se 2 (by rfl) ⟨314421, by rfl⟩ : syracuseStep 838457 = 628843) B628843
theorem B838535 : Blo 558808 838535 := bstep (se 1 (by rfl) ⟨628901, by rfl⟩ : syracuseStep 838535 = 1257803) B1257803
theorem B838571 : Blo 558808 838571 := bstep (se 1 (by rfl) ⟨628928, by rfl⟩ : syracuseStep 838571 = 1257857) B1257857
theorem B838601 : Blo 558808 838601 := bstep (se 2 (by rfl) ⟨314475, by rfl⟩ : syracuseStep 838601 = 628951) B628951
theorem B14797835 : Blo 558808 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B838715 : Blo 558808 838715 := bstep (se 1 (by rfl) ⟨629036, by rfl⟩ : syracuseStep 838715 = 1258073) B1258073
theorem B2837591 : Blo 558808 2837591 := bstep (se 1 (by rfl) ⟨2128193, by rfl⟩ : syracuseStep 2837591 = 4256387) B4256387
theorem B838775 : Blo 558808 838775 := bstep (se 1 (by rfl) ⟨629081, by rfl⟩ : syracuseStep 838775 = 1258163) B1258163
theorem B1592455 : Blo 558808 1592455 := bstep (se 1 (by rfl) ⟨1194341, by rfl⟩ : syracuseStep 1592455 = 2388683) B2388683
theorem B1068167 : Blo 558808 1068167 := bstep (se 1 (by rfl) ⟨801125, by rfl⟩ : syracuseStep 1068167 = 1602251) B1602251
theorem B838799 : Blo 558808 838799 := bstep (se 1 (by rfl) ⟨629099, by rfl⟩ : syracuseStep 838799 = 1258199) B1258199
theorem B1264787 : Blo 558808 1264787 := bstep (se 1 (by rfl) ⟨948590, by rfl⟩ : syracuseStep 1264787 = 1897181) B1897181
theorem B838841 : Blo 558808 838841 := bstep (se 2 (by rfl) ⟨314565, by rfl⟩ : syracuseStep 838841 = 629131) B629131
theorem B1264841 : Blo 558808 1264841 := bstep (se 2 (by rfl) ⟨474315, by rfl⟩ : syracuseStep 1264841 = 948631) B948631
theorem B838919 : Blo 558808 838919 := bstep (se 1 (by rfl) ⟨629189, by rfl⟩ : syracuseStep 838919 = 1258379) B1258379
theorem B838955 : Blo 558808 838955 := bstep (se 1 (by rfl) ⟨629216, by rfl⟩ : syracuseStep 838955 = 1258433) B1258433
theorem B838985 : Blo 558808 838985 := bstep (se 2 (by rfl) ⟨314619, by rfl⟩ : syracuseStep 838985 = 629239) B629239
theorem B1887623 : Blo 558808 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B1592729 : Blo 558808 1592729 := bstep (se 2 (by rfl) ⟨597273, by rfl⟩ : syracuseStep 1592729 = 1194547) B1194547
theorem B839099 : Blo 558808 839099 := bstep (se 1 (by rfl) ⟨629324, by rfl⟩ : syracuseStep 839099 = 1258649) B1258649
theorem B839159 : Blo 558808 839159 := bstep (se 1 (by rfl) ⟨629369, by rfl⟩ : syracuseStep 839159 = 1258739) B1258739
theorem B675335 : Blo 558808 675335 := bstep (se 1 (by rfl) ⟨506501, by rfl⟩ : syracuseStep 675335 = 1013003) B1013003
theorem B839183 : Blo 558808 839183 := bstep (se 1 (by rfl) ⟨629387, by rfl⟩ : syracuseStep 839183 = 1258775) B1258775
theorem B3198487 : Blo 558808 3198487 := bstep (se 1 (by rfl) ⟨2398865, by rfl⟩ : syracuseStep 3198487 = 4797731) B4797731
theorem B839225 : Blo 558808 839225 := bstep (se 2 (by rfl) ⟨314709, by rfl⟩ : syracuseStep 839225 = 629419) B629419
theorem B2838077 : Blo 558808 2838077 := bstep (se 3 (by rfl) ⟨532139, by rfl⟩ : syracuseStep 2838077 = 1064279) B1064279
theorem B13684301 : Blo 558808 13684301 := bstep (se 3 (by rfl) ⟨2565806, by rfl⟩ : syracuseStep 13684301 = 5131613) B5131613
theorem B839303 : Blo 558808 839303 := bstep (se 1 (by rfl) ⟨629477, by rfl⟩ : syracuseStep 839303 = 1258955) B1258955
theorem B839339 : Blo 558808 839339 := bstep (se 1 (by rfl) ⟨629504, by rfl⟩ : syracuseStep 839339 = 1259009) B1259009
theorem B839369 : Blo 558808 839369 := bstep (se 2 (by rfl) ⟨314763, by rfl⟩ : syracuseStep 839369 = 629527) B629527
theorem B46157525 : Blo 558808 46157525 := bstep (se 7 (by rfl) ⟨540908, by rfl⟩ : syracuseStep 46157525 = 1081817) B1081817
theorem B1888001 : Blo 558808 1888001 := bstep (se 2 (by rfl) ⟨708000, by rfl⟩ : syracuseStep 1888001 = 1416001) B1416001
theorem B3460897 : Blo 558808 3460897 := bstep (se 2 (by rfl) ⟨1297836, by rfl⟩ : syracuseStep 3460897 = 2595673) B2595673
theorem B839483 : Blo 558808 839483 := bstep (se 1 (by rfl) ⟨629612, by rfl⟩ : syracuseStep 839483 = 1259225) B1259225
theorem B675643 : Blo 558808 675643 := bstep (se 1 (by rfl) ⟨506732, by rfl⟩ : syracuseStep 675643 = 1013465) B1013465
theorem B6377291 : Blo 558808 6377291 := bstep (se 1 (by rfl) ⟨4782968, by rfl⟩ : syracuseStep 6377291 = 9565937) B9565937
theorem B839543 : Blo 558808 839543 := bstep (se 1 (by rfl) ⟨629657, by rfl⟩ : syracuseStep 839543 = 1259315) B1259315
theorem B1265543 : Blo 558808 1265543 := bstep (se 1 (by rfl) ⟨949157, by rfl⟩ : syracuseStep 1265543 = 1898315) B1898315
theorem B839567 : Blo 558808 839567 := bstep (se 1 (by rfl) ⟨629675, by rfl⟩ : syracuseStep 839567 = 1259351) B1259351
theorem B839609 : Blo 558808 839609 := bstep (se 2 (by rfl) ⟨314853, by rfl⟩ : syracuseStep 839609 = 629707) B629707
theorem B16175051 : Blo 558808 16175051 := bstep (se 1 (by rfl) ⟨12131288, by rfl⟩ : syracuseStep 16175051 = 24262577) B24262577
theorem B839687 : Blo 558808 839687 := bstep (se 1 (by rfl) ⟨629765, by rfl⟩ : syracuseStep 839687 = 1259531) B1259531
theorem B839723 : Blo 558808 839723 := bstep (se 1 (by rfl) ⟨629792, by rfl⟩ : syracuseStep 839723 = 1259585) B1259585
theorem B1265723 : Blo 558808 1265723 := bstep (se 1 (by rfl) ⟨949292, by rfl⟩ : syracuseStep 1265723 = 1898585) B1898585
theorem B839753 : Blo 558808 839753 := bstep (se 2 (by rfl) ⟨314907, by rfl⟩ : syracuseStep 839753 = 629815) B629815
theorem B4247639 : Blo 558808 4247639 := bstep (se 1 (by rfl) ⟨3185729, by rfl⟩ : syracuseStep 4247639 = 6371459) B6371459
theorem B6475949 : Blo 558808 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B1265849 : Blo 558808 1265849 := bstep (se 2 (by rfl) ⟨474693, by rfl⟩ : syracuseStep 1265849 = 949387) B949387
theorem B839867 : Blo 558808 839867 := bstep (se 1 (by rfl) ⟨629900, by rfl⟩ : syracuseStep 839867 = 1259801) B1259801
theorem B676027 : Blo 558808 676027 := bstep (se 1 (by rfl) ⟨507020, by rfl⟩ : syracuseStep 676027 = 1014041) B1014041
theorem B839927 : Blo 558808 839927 := bstep (se 1 (by rfl) ⟨629945, by rfl⟩ : syracuseStep 839927 = 1259891) B1259891
theorem B839951 : Blo 558808 839951 := bstep (se 1 (by rfl) ⟨629963, by rfl⟩ : syracuseStep 839951 = 1259927) B1259927
theorem B708907 : Blo 558808 708907 := bstep (se 1 (by rfl) ⟨531680, by rfl⟩ : syracuseStep 708907 = 1063361) B1063361
theorem B839993 : Blo 558808 839993 := bstep (se 2 (by rfl) ⟨314997, by rfl⟩ : syracuseStep 839993 = 629995) B629995
theorem B840071 : Blo 558808 840071 := bstep (se 1 (by rfl) ⟨630053, by rfl⟩ : syracuseStep 840071 = 1260107) B1260107
theorem B1921427 : Blo 558808 1921427 := bstep (se 1 (by rfl) ⟨1441070, by rfl⟩ : syracuseStep 1921427 = 2882141) B2882141
theorem B840107 : Blo 558808 840107 := bstep (se 1 (by rfl) ⟨630080, by rfl⟩ : syracuseStep 840107 = 1260161) B1260161
theorem B840137 : Blo 558808 840137 := bstep (se 2 (by rfl) ⟨315051, by rfl⟩ : syracuseStep 840137 = 630103) B630103
theorem B1593857 : Blo 558808 1593857 := bstep (se 2 (by rfl) ⟨597696, by rfl⟩ : syracuseStep 1593857 = 1195393) B1195393
theorem B1266191 : Blo 558808 1266191 := bstep (se 1 (by rfl) ⟨949643, by rfl⟩ : syracuseStep 1266191 = 1899287) B1899287
theorem B1266209 : Blo 558808 1266209 := bstep (se 2 (by rfl) ⟨474828, by rfl⟩ : syracuseStep 1266209 = 949657) B949657
theorem B1888811 : Blo 558808 1888811 := bstep (se 1 (by rfl) ⟨1416608, by rfl⟩ : syracuseStep 1888811 = 2833217) B2833217
theorem B840251 : Blo 558808 840251 := bstep (se 1 (by rfl) ⟨630188, by rfl⟩ : syracuseStep 840251 = 1260377) B1260377
theorem B840311 : Blo 558808 840311 := bstep (se 1 (by rfl) ⟨630233, by rfl⟩ : syracuseStep 840311 = 1260467) B1260467
theorem B840335 : Blo 558808 840335 := bstep (se 1 (by rfl) ⟨630251, by rfl⟩ : syracuseStep 840335 = 1260503) B1260503
theorem B840377 : Blo 558808 840377 := bstep (se 2 (by rfl) ⟨315141, by rfl⟩ : syracuseStep 840377 = 630283) B630283
theorem B840455 : Blo 558808 840455 := bstep (se 1 (by rfl) ⟨630341, by rfl⟩ : syracuseStep 840455 = 1260683) B1260683
theorem B840491 : Blo 558808 840491 := bstep (se 1 (by rfl) ⟨630368, by rfl⟩ : syracuseStep 840491 = 1260737) B1260737
theorem B840521 : Blo 558808 840521 := bstep (se 2 (by rfl) ⟨315195, by rfl⟩ : syracuseStep 840521 = 630391) B630391
theorem B1790873 : Blo 558808 1790873 := bstep (se 2 (by rfl) ⟨671577, by rfl⟩ : syracuseStep 1790873 = 1343155) B1343155
theorem B840635 : Blo 558808 840635 := bstep (se 1 (by rfl) ⟨630476, by rfl⟩ : syracuseStep 840635 = 1260953) B1260953
theorem B1594313 : Blo 558808 1594313 := bstep (se 2 (by rfl) ⟨597867, by rfl⟩ : syracuseStep 1594313 = 1195735) B1195735
theorem B840695 : Blo 558808 840695 := bstep (se 1 (by rfl) ⟨630521, by rfl⟩ : syracuseStep 840695 = 1261043) B1261043
theorem B840719 : Blo 558808 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B840761 : Blo 558808 840761 := bstep (se 2 (by rfl) ⟨315285, by rfl⟩ : syracuseStep 840761 = 630571) B630571
theorem B840839 : Blo 558808 840839 := bstep (se 1 (by rfl) ⟨630629, by rfl⟩ : syracuseStep 840839 = 1261259) B1261259
theorem B840875 : Blo 558808 840875 := bstep (se 1 (by rfl) ⟨630656, by rfl⟩ : syracuseStep 840875 = 1261313) B1261313
theorem B840905 : Blo 558808 840905 := bstep (se 2 (by rfl) ⟨315339, by rfl⟩ : syracuseStep 840905 = 630679) B630679
theorem B709879 : Blo 558808 709879 := bstep (se 1 (by rfl) ⟨532409, by rfl⟩ : syracuseStep 709879 = 1064819) B1064819
theorem B2839859 : Blo 558808 2839859 := bstep (se 1 (by rfl) ⟨2129894, by rfl⟩ : syracuseStep 2839859 = 4259789) B4259789
theorem B841019 : Blo 558808 841019 := bstep (se 1 (by rfl) ⟨630764, by rfl⟩ : syracuseStep 841019 = 1261529) B1261529
theorem B841079 : Blo 558808 841079 := bstep (se 1 (by rfl) ⟨630809, by rfl⟩ : syracuseStep 841079 = 1261619) B1261619
theorem B15324551 : Blo 558808 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B841103 : Blo 558808 841103 := bstep (se 1 (by rfl) ⟨630827, by rfl⟩ : syracuseStep 841103 = 1261655) B1261655
theorem B841145 : Blo 558808 841145 := bstep (se 2 (by rfl) ⟨315429, by rfl⟩ : syracuseStep 841145 = 630859) B630859
theorem B841223 : Blo 558808 841223 := bstep (se 1 (by rfl) ⟨630917, by rfl⟩ : syracuseStep 841223 = 1261835) B1261835
theorem B841259 : Blo 558808 841259 := bstep (se 1 (by rfl) ⟨630944, by rfl⟩ : syracuseStep 841259 = 1261889) B1261889
theorem B710203 : Blo 558808 710203 := bstep (se 1 (by rfl) ⟨532652, by rfl⟩ : syracuseStep 710203 = 1065305) B1065305
theorem B841289 : Blo 558808 841289 := bstep (se 2 (by rfl) ⟨315483, by rfl⟩ : syracuseStep 841289 = 630967) B630967
theorem B2840183 : Blo 558808 2840183 := bstep (se 1 (by rfl) ⟨2130137, by rfl⟩ : syracuseStep 2840183 = 4260275) B4260275
theorem B841403 : Blo 558808 841403 := bstep (se 1 (by rfl) ⟨631052, by rfl⟩ : syracuseStep 841403 = 1262105) B1262105
theorem B841463 : Blo 558808 841463 := bstep (se 1 (by rfl) ⟨631097, by rfl⟩ : syracuseStep 841463 = 1262195) B1262195
theorem B841487 : Blo 558808 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B841529 : Blo 558808 841529 := bstep (se 2 (by rfl) ⟨315573, by rfl⟩ : syracuseStep 841529 = 631147) B631147
theorem B1890107 : Blo 558808 1890107 := bstep (se 1 (by rfl) ⟨1417580, by rfl⟩ : syracuseStep 1890107 = 2835161) B2835161
theorem B1201979 : Blo 558808 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B841607 : Blo 558808 841607 := bstep (se 1 (by rfl) ⟨631205, by rfl⟩ : syracuseStep 841607 = 1262411) B1262411
theorem B3200903 : Blo 558808 3200903 := bstep (se 1 (by rfl) ⟨2400677, by rfl⟩ : syracuseStep 3200903 = 4801355) B4801355
theorem B841643 : Blo 558808 841643 := bstep (se 1 (by rfl) ⟨631232, by rfl⟩ : syracuseStep 841643 = 1262465) B1262465
theorem B841673 : Blo 558808 841673 := bstep (se 2 (by rfl) ⟨315627, by rfl⟩ : syracuseStep 841673 = 631255) B631255
theorem B841787 : Blo 558808 841787 := bstep (se 1 (by rfl) ⟨631340, by rfl⟩ : syracuseStep 841787 = 1262681) B1262681
theorem B841847 : Blo 558808 841847 := bstep (se 1 (by rfl) ⟨631385, by rfl⟩ : syracuseStep 841847 = 1262771) B1262771
theorem B841871 : Blo 558808 841871 := bstep (se 1 (by rfl) ⟨631403, by rfl⟩ : syracuseStep 841871 = 1262807) B1262807
theorem B841913 : Blo 558808 841913 := bstep (se 2 (by rfl) ⟨315717, by rfl⟩ : syracuseStep 841913 = 631435) B631435
theorem B841991 : Blo 558808 841991 := bstep (se 1 (by rfl) ⟨631493, by rfl⟩ : syracuseStep 841991 = 1262987) B1262987
theorem B1890593 : Blo 558808 1890593 := bstep (se 2 (by rfl) ⟨708972, by rfl⟩ : syracuseStep 1890593 = 1417945) B1417945
theorem B842027 : Blo 558808 842027 := bstep (se 1 (by rfl) ⟨631520, by rfl⟩ : syracuseStep 842027 = 1263041) B1263041
theorem B842057 : Blo 558808 842057 := bstep (se 2 (by rfl) ⟨315771, by rfl⟩ : syracuseStep 842057 = 631543) B631543
theorem B6936977 : Blo 558808 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B842171 : Blo 558808 842171 := bstep (se 1 (by rfl) ⟨631628, by rfl⟩ : syracuseStep 842171 = 1263257) B1263257
theorem B1137097 : Blo 558808 1137097 := bstep (se 2 (by rfl) ⟨426411, by rfl⟩ : syracuseStep 1137097 = 852823) B852823
theorem B842231 : Blo 558808 842231 := bstep (se 1 (by rfl) ⟨631673, by rfl⟩ : syracuseStep 842231 = 1263347) B1263347
theorem B711175 : Blo 558808 711175 := bstep (se 1 (by rfl) ⟨533381, by rfl⟩ : syracuseStep 711175 = 1066763) B1066763
theorem B842255 : Blo 558808 842255 := bstep (se 1 (by rfl) ⟨631691, by rfl⟩ : syracuseStep 842255 = 1263383) B1263383
theorem B842297 : Blo 558808 842297 := bstep (se 2 (by rfl) ⟨315861, by rfl⟩ : syracuseStep 842297 = 631723) B631723
theorem B1595963 : Blo 558808 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B2841155 : Blo 558808 2841155 := bstep (se 1 (by rfl) ⟨2130866, by rfl⟩ : syracuseStep 2841155 = 4261733) B4261733
theorem B842375 : Blo 558808 842375 := bstep (se 1 (by rfl) ⟨631781, by rfl⟩ : syracuseStep 842375 = 1263563) B1263563
theorem B1038995 : Blo 558808 1038995 := bstep (se 1 (by rfl) ⟨779246, by rfl⟩ : syracuseStep 1038995 = 1558493) B1558493
theorem B842411 : Blo 558808 842411 := bstep (se 1 (by rfl) ⟨631808, by rfl⟩ : syracuseStep 842411 = 1263617) B1263617
theorem B842441 : Blo 558808 842441 := bstep (se 2 (by rfl) ⟨315915, by rfl⟩ : syracuseStep 842441 = 631831) B631831
theorem B842555 : Blo 558808 842555 := bstep (se 1 (by rfl) ⟨631916, by rfl⟩ : syracuseStep 842555 = 1263833) B1263833
theorem B1891187 : Blo 558808 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B842615 : Blo 558808 842615 := bstep (se 1 (by rfl) ⟨631961, by rfl⟩ : syracuseStep 842615 = 1263923) B1263923
theorem B2841479 : Blo 558808 2841479 := bstep (se 1 (by rfl) ⟨2131109, by rfl⟩ : syracuseStep 2841479 = 4262219) B4262219
theorem B842639 : Blo 558808 842639 := bstep (se 1 (by rfl) ⟨631979, by rfl⟩ : syracuseStep 842639 = 1263959) B1263959
theorem B711595 : Blo 558808 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B842681 : Blo 558808 842681 := bstep (se 2 (by rfl) ⟨316005, by rfl⟩ : syracuseStep 842681 = 632011) B632011
theorem B842759 : Blo 558808 842759 := bstep (se 1 (by rfl) ⟨632069, by rfl⟩ : syracuseStep 842759 = 1264139) B1264139
theorem B842795 : Blo 558808 842795 := bstep (se 1 (by rfl) ⟨632096, by rfl⟩ : syracuseStep 842795 = 1264193) B1264193
theorem B842825 : Blo 558808 842825 := bstep (se 2 (by rfl) ⟨316059, by rfl⟩ : syracuseStep 842825 = 632119) B632119
theorem B711823 : Blo 558808 711823 := bstep (se 1 (by rfl) ⟨533867, by rfl⟩ : syracuseStep 711823 = 1067735) B1067735
theorem B1596601 : Blo 558808 1596601 := bstep (se 2 (by rfl) ⟨598725, by rfl⟩ : syracuseStep 1596601 = 1197451) B1197451
theorem B842939 : Blo 558808 842939 := bstep (se 1 (by rfl) ⟨632204, by rfl⟩ : syracuseStep 842939 = 1264409) B1264409
theorem B842999 : Blo 558808 842999 := bstep (se 1 (by rfl) ⟨632249, by rfl⟩ : syracuseStep 842999 = 1264499) B1264499
theorem B843023 : Blo 558808 843023 := bstep (se 1 (by rfl) ⟨632267, by rfl⟩ : syracuseStep 843023 = 1264535) B1264535
theorem B843065 : Blo 558808 843065 := bstep (se 2 (by rfl) ⟨316149, by rfl⟩ : syracuseStep 843065 = 632299) B632299
theorem B843143 : Blo 558808 843143 := bstep (se 1 (by rfl) ⟨632357, by rfl⟩ : syracuseStep 843143 = 1264715) B1264715
theorem B843179 : Blo 558808 843179 := bstep (se 1 (by rfl) ⟨632384, by rfl⟩ : syracuseStep 843179 = 1264769) B1264769
theorem B843209 : Blo 558808 843209 := bstep (se 2 (by rfl) ⟨316203, by rfl⟩ : syracuseStep 843209 = 632407) B632407
theorem B843323 : Blo 558808 843323 := bstep (se 1 (by rfl) ⟨632492, by rfl⟩ : syracuseStep 843323 = 1264985) B1264985
theorem B1596989 : Blo 558808 1596989 := bstep (se 3 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 1596989 = 598871) B598871
theorem B843383 : Blo 558808 843383 := bstep (se 1 (by rfl) ⟨632537, by rfl⟩ : syracuseStep 843383 = 1265075) B1265075
theorem B3202679 : Blo 558808 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B843407 : Blo 558808 843407 := bstep (se 1 (by rfl) ⟨632555, by rfl⟩ : syracuseStep 843407 = 1265111) B1265111
theorem B843449 : Blo 558808 843449 := bstep (se 2 (by rfl) ⟨316293, by rfl⟩ : syracuseStep 843449 = 632587) B632587
theorem B843527 : Blo 558808 843527 := bstep (se 1 (by rfl) ⟨632645, by rfl⟩ : syracuseStep 843527 = 1265291) B1265291
theorem B843563 : Blo 558808 843563 := bstep (se 1 (by rfl) ⟨632672, by rfl⟩ : syracuseStep 843563 = 1265345) B1265345
theorem B4054835 : Blo 558808 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B843593 : Blo 558808 843593 := bstep (se 2 (by rfl) ⟨316347, by rfl⟩ : syracuseStep 843593 = 632695) B632695
theorem B3596147 : Blo 558808 3596147 := bstep (se 1 (by rfl) ⟨2697110, by rfl⟩ : syracuseStep 3596147 = 5394221) B5394221
theorem B20406167 : Blo 558808 20406167 := bstep (se 1 (by rfl) ⟨15304625, by rfl⟩ : syracuseStep 20406167 = 30609251) B30609251
theorem B843707 : Blo 558808 843707 := bstep (se 1 (by rfl) ⟨632780, by rfl⟩ : syracuseStep 843707 = 1265561) B1265561
theorem B843767 : Blo 558808 843767 := bstep (se 1 (by rfl) ⟨632825, by rfl⟩ : syracuseStep 843767 = 1265651) B1265651
theorem B843791 : Blo 558808 843791 := bstep (se 1 (by rfl) ⟨632843, by rfl⟩ : syracuseStep 843791 = 1265687) B1265687
theorem B843833 : Blo 558808 843833 := bstep (se 2 (by rfl) ⟨316437, by rfl⟩ : syracuseStep 843833 = 632875) B632875
theorem B2121815 : Blo 558808 2121815 := bstep (se 1 (by rfl) ⟨1591361, by rfl⟩ : syracuseStep 2121815 = 3182723) B3182723
theorem B843911 : Blo 558808 843911 := bstep (se 1 (by rfl) ⟨632933, by rfl⟩ : syracuseStep 843911 = 1265867) B1265867
theorem B843947 : Blo 558808 843947 := bstep (se 1 (by rfl) ⟨632960, by rfl⟩ : syracuseStep 843947 = 1265921) B1265921
theorem B843977 : Blo 558808 843977 := bstep (se 2 (by rfl) ⟨316491, by rfl⟩ : syracuseStep 843977 = 632983) B632983
theorem B3203387 : Blo 558808 3203387 := bstep (se 1 (by rfl) ⟨2402540, by rfl⟩ : syracuseStep 3203387 = 4805081) B4805081
theorem B844091 : Blo 558808 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B844151 : Blo 558808 844151 := bstep (se 1 (by rfl) ⟨633113, by rfl⟩ : syracuseStep 844151 = 1266227) B1266227
theorem B844175 : Blo 558808 844175 := bstep (se 1 (by rfl) ⟨633131, by rfl⟩ : syracuseStep 844175 = 1266263) B1266263
theorem B2122301 : Blo 558808 2122301 := bstep (se 3 (by rfl) ⟨397931, by rfl⟩ : syracuseStep 2122301 = 795863) B795863
theorem B1598105 : Blo 558808 1598105 := bstep (se 2 (by rfl) ⟨599289, by rfl⟩ : syracuseStep 1598105 = 1198579) B1198579
theorem B943049 : Blo 558808 943049 := bstep (se 2 (by rfl) ⟨353643, by rfl⟩ : syracuseStep 943049 = 707287) B707287
theorem B3236867 : Blo 558808 3236867 := bstep (se 1 (by rfl) ⟨2427650, by rfl⟩ : syracuseStep 3236867 = 4855301) B4855301
theorem B1893779 : Blo 558808 1893779 := bstep (se 1 (by rfl) ⟨1420334, by rfl⟩ : syracuseStep 1893779 = 2840669) B2840669
theorem B2024851 : Blo 558808 2024851 := bstep (se 1 (by rfl) ⟨1518638, by rfl⟩ : syracuseStep 2024851 = 3037277) B3037277
theorem B4777501 : Blo 558808 4777501 := bstep (se 3 (by rfl) ⟨895781, by rfl⟩ : syracuseStep 4777501 = 1791563) B1791563
theorem B943751 : Blo 558808 943751 := bstep (se 1 (by rfl) ⟨707813, by rfl⟩ : syracuseStep 943751 = 1415627) B1415627
theorem B9070309 : Blo 558808 9070309 := bstep (se 4 (by rfl) ⟨850341, by rfl⟩ : syracuseStep 9070309 = 1700683) B1700683
theorem B3204845 : Blo 558808 3204845 := bstep (se 3 (by rfl) ⟨600908, by rfl⟩ : syracuseStep 3204845 = 1201817) B1201817
theorem B5400371 : Blo 558808 5400371 := bstep (se 1 (by rfl) ⟨4050278, by rfl⟩ : syracuseStep 5400371 = 8100557) B8100557
theorem B5400523 : Blo 558808 5400523 := bstep (se 1 (by rfl) ⟨4050392, by rfl⟩ : syracuseStep 5400523 = 8100785) B8100785
theorem B2123729 : Blo 558808 2123729 := bstep (se 2 (by rfl) ⟨796398, by rfl⟩ : syracuseStep 2123729 = 1592797) B1592797
theorem B1599517 : Blo 558808 1599517 := bstep (se 3 (by rfl) ⟨299909, by rfl⟩ : syracuseStep 1599517 = 599819) B599819
theorem B1599689 : Blo 558808 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B1599745 : Blo 558808 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B944399 : Blo 558808 944399 := bstep (se 1 (by rfl) ⟨708299, by rfl⟩ : syracuseStep 944399 = 1416599) B1416599
theorem B2845043 : Blo 558808 2845043 := bstep (se 1 (by rfl) ⟨2133782, by rfl⟩ : syracuseStep 2845043 = 4267565) B4267565
theorem B911915 : Blo 558808 911915 := bstep (se 1 (by rfl) ⟨683936, by rfl⟩ : syracuseStep 911915 = 1367873) B1367873
theorem B1600087 : Blo 558808 1600087 := bstep (se 1 (by rfl) ⟨1200065, by rfl⟩ : syracuseStep 1600087 = 2400131) B2400131
theorem B10742543 : Blo 558808 10742543 := bstep (se 1 (by rfl) ⟨8056907, by rfl⟩ : syracuseStep 10742543 = 16113815) B16113815
theorem B1895183 : Blo 558808 1895183 := bstep (se 1 (by rfl) ⟨1421387, by rfl⟩ : syracuseStep 1895183 = 2842775) B2842775
theorem B944939 : Blo 558808 944939 := bstep (se 1 (by rfl) ⟨708704, by rfl⟩ : syracuseStep 944939 = 1417409) B1417409
theorem B2845529 : Blo 558808 2845529 := bstep (se 2 (by rfl) ⟨1067073, by rfl⟩ : syracuseStep 2845529 = 2134147) B2134147
theorem B1895453 : Blo 558808 1895453 := bstep (se 3 (by rfl) ⟨355397, by rfl⟩ : syracuseStep 1895453 = 710795) B710795
theorem B945337 : Blo 558808 945337 := bstep (se 2 (by rfl) ⟨354501, by rfl⟩ : syracuseStep 945337 = 709003) B709003
theorem B4779485 : Blo 558808 4779485 := bstep (se 3 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 4779485 = 1792307) B1792307
theorem B3599939 : Blo 558808 3599939 := bstep (se 1 (by rfl) ⟨2699954, by rfl⟩ : syracuseStep 3599939 = 5399909) B5399909
theorem B2125399 : Blo 558808 2125399 := bstep (se 1 (by rfl) ⟨1594049, by rfl⟩ : syracuseStep 2125399 = 3188099) B3188099
theorem B2387657 : Blo 558808 2387657 := bstep (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) B1790743
theorem B5402369 : Blo 558808 5402369 := bstep (se 2 (by rfl) ⟨2025888, by rfl⟩ : syracuseStep 5402369 = 4051777) B4051777
theorem B1797947 : Blo 558808 1797947 := bstep (se 1 (by rfl) ⟨1348460, by rfl⟩ : syracuseStep 1797947 = 2696921) B2696921
theorem B946039 : Blo 558808 946039 := bstep (se 1 (by rfl) ⟨709529, by rfl⟩ : syracuseStep 946039 = 1419059) B1419059
theorem B2125703 : Blo 558808 2125703 := bstep (se 1 (by rfl) ⟨1594277, by rfl⟩ : syracuseStep 2125703 = 3188555) B3188555
theorem B1011727 : Blo 558808 1011727 := bstep (se 1 (by rfl) ⟨758795, by rfl⟩ : syracuseStep 1011727 = 1517591) B1517591
theorem B946235 : Blo 558808 946235 := bstep (se 1 (by rfl) ⟨709676, by rfl⟩ : syracuseStep 946235 = 1419353) B1419353
theorem B2125885 : Blo 558808 2125885 := bstep (se 3 (by rfl) ⟨398603, by rfl⟩ : syracuseStep 2125885 = 797207) B797207
theorem B1798433 : Blo 558808 1798433 := bstep (se 2 (by rfl) ⟨674412, by rfl⟩ : syracuseStep 1798433 = 1348825) B1348825
theorem B9073043 : Blo 558808 9073043 := bstep (se 1 (by rfl) ⟨6804782, by rfl⟩ : syracuseStep 9073043 = 13609565) B13609565
theorem B1896857 : Blo 558808 1896857 := bstep (se 2 (by rfl) ⟨711321, by rfl⟩ : syracuseStep 1896857 = 1422643) B1422643
theorem B946633 : Blo 558808 946633 := bstep (se 2 (by rfl) ⟨354987, by rfl⟩ : syracuseStep 946633 = 709975) B709975
theorem B2388599 : Blo 558808 2388599 := bstep (se 1 (by rfl) ⟨1791449, by rfl⟩ : syracuseStep 2388599 = 3582899) B3582899
theorem B1012513 : Blo 558808 1012513 := bstep (se 2 (by rfl) ⟨379692, by rfl⟩ : syracuseStep 1012513 = 759385) B759385
theorem B1799047 : Blo 558808 1799047 := bstep (se 1 (by rfl) ⟨1349285, by rfl⟩ : syracuseStep 1799047 = 2698571) B2698571
theorem B2847635 : Blo 558808 2847635 := bstep (se 1 (by rfl) ⟨2135726, by rfl⟩ : syracuseStep 2847635 = 4271453) B4271453
theorem B1897559 : Blo 558808 1897559 := bstep (se 1 (by rfl) ⟨1423169, by rfl⟩ : syracuseStep 1897559 = 2846339) B2846339
theorem B947335 : Blo 558808 947335 := bstep (se 1 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 947335 = 1421003) B1421003
theorem B1078571 : Blo 558808 1078571 := bstep (se 1 (by rfl) ⟨808928, by rfl⟩ : syracuseStep 1078571 = 1617857) B1617857
theorem B1898045 : Blo 558808 1898045 := bstep (se 3 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 1898045 = 711767) B711767
theorem B2389571 : Blo 558808 2389571 := bstep (se 1 (by rfl) ⟨1792178, by rfl⟩ : syracuseStep 2389571 = 3584357) B3584357
theorem B2127617 : Blo 558808 2127617 := bstep (se 2 (by rfl) ⟨797856, by rfl⟩ : syracuseStep 2127617 = 1595713) B1595713
theorem B947983 : Blo 558808 947983 := bstep (se 1 (by rfl) ⟨710987, by rfl⟩ : syracuseStep 947983 = 1421975) B1421975
theorem B4781875 : Blo 558808 4781875 := bstep (se 1 (by rfl) ⟨3586406, by rfl⟩ : syracuseStep 4781875 = 7172813) B7172813
theorem B4028249 : Blo 558808 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B719119 : Blo 558808 719119 := bstep (se 1 (by rfl) ⟨539339, by rfl⟩ : syracuseStep 719119 = 1078679) B1078679
theorem B948523 : Blo 558808 948523 := bstep (se 1 (by rfl) ⟨711392, by rfl⟩ : syracuseStep 948523 = 1422785) B1422785
theorem B1538423 : Blo 558808 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B948665 : Blo 558808 948665 := bstep (se 2 (by rfl) ⟨355749, by rfl⟩ : syracuseStep 948665 = 711499) B711499
theorem B6912515 : Blo 558808 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B10222199 : Blo 558808 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B4848473 : Blo 558808 4848473 := bstep (se 2 (by rfl) ⟨1818177, by rfl⟩ : syracuseStep 4848473 = 3636355) B3636355
theorem B2128787 : Blo 558808 2128787 := bstep (se 1 (by rfl) ⟨1596590, by rfl⟩ : syracuseStep 2128787 = 3193181) B3193181
theorem B1899449 : Blo 558808 1899449 := bstep (se 2 (by rfl) ⟨712293, by rfl⟩ : syracuseStep 1899449 = 1424587) B1424587
theorem B6454333 : Blo 558808 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B949367 : Blo 558808 949367 := bstep (se 1 (by rfl) ⟨712025, by rfl⟩ : syracuseStep 949367 = 1424051) B1424051
theorem B3603629 : Blo 558808 3603629 := bstep (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) B1351361
theorem B1441111 : Blo 558808 1441111 := bstep (se 1 (by rfl) ⟨1080833, by rfl⟩ : syracuseStep 1441111 = 2161667) B2161667
theorem B2129287 : Blo 558808 2129287 := bstep (se 1 (by rfl) ⟨1596965, by rfl⟩ : syracuseStep 2129287 = 3193931) B3193931
theorem B1801739 : Blo 558808 1801739 := bstep (se 1 (by rfl) ⟨1351304, by rfl⟩ : syracuseStep 1801739 = 2702609) B2702609
theorem B2555479 : Blo 558808 2555479 := bstep (se 1 (by rfl) ⟨1916609, by rfl⟩ : syracuseStep 2555479 = 3833219) B3833219
theorem B7667531 : Blo 558808 7667531 := bstep (se 1 (by rfl) ⟨5750648, by rfl⟩ : syracuseStep 7667531 = 11501297) B11501297
theorem B1278031 : Blo 558808 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B2130077 : Blo 558808 2130077 := bstep (se 3 (by rfl) ⟨399389, by rfl⟩ : syracuseStep 2130077 = 798779) B798779
theorem B7504595 : Blo 558808 7504595 := bstep (se 1 (by rfl) ⟨5628446, by rfl⟩ : syracuseStep 7504595 = 11256893) B11256893
theorem B2130731 : Blo 558808 2130731 := bstep (se 1 (by rfl) ⟨1598048, by rfl⟩ : syracuseStep 2130731 = 3196097) B3196097
theorem B4031309 : Blo 558808 4031309 := bstep (se 3 (by rfl) ⟨755870, by rfl⟩ : syracuseStep 4031309 = 1511741) B1511741
theorem B8750429 : Blo 558808 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B558811 : Blo 558808 558811 := bstep (se 1 (by rfl) ⟨419108, by rfl⟩ : syracuseStep 558811 = 838217) B838217
theorem B558887 : Blo 558808 558887 := bstep (se 1 (by rfl) ⟨419165, by rfl⟩ : syracuseStep 558887 = 838331) B838331
theorem B558927 : Blo 558808 558927 := bstep (se 1 (by rfl) ⟨419195, by rfl⟩ : syracuseStep 558927 = 838391) B838391
theorem B558943 : Blo 558808 558943 := bstep (se 1 (by rfl) ⟨419207, by rfl⟩ : syracuseStep 558943 = 838415) B838415
theorem B558971 : Blo 558808 558971 := bstep (se 1 (by rfl) ⟨419228, by rfl⟩ : syracuseStep 558971 = 838457) B838457
theorem B559023 : Blo 558808 559023 := bstep (se 1 (by rfl) ⟨419267, by rfl⟩ : syracuseStep 559023 = 838535) B838535
theorem B559047 : Blo 558808 559047 := bstep (se 1 (by rfl) ⟨419285, by rfl⟩ : syracuseStep 559047 = 838571) B838571
theorem B559067 : Blo 558808 559067 := bstep (se 1 (by rfl) ⟨419300, by rfl⟩ : syracuseStep 559067 = 838601) B838601
theorem B9570311 : Blo 558808 9570311 := bstep (se 1 (by rfl) ⟨7177733, by rfl⟩ : syracuseStep 9570311 = 14355467) B14355467
theorem B9865223 : Blo 558808 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B559143 : Blo 558808 559143 := bstep (se 1 (by rfl) ⟨419357, by rfl⟩ : syracuseStep 559143 = 838715) B838715
theorem B559183 : Blo 558808 559183 := bstep (se 1 (by rfl) ⟨419387, by rfl⟩ : syracuseStep 559183 = 838775) B838775
theorem B559199 : Blo 558808 559199 := bstep (se 1 (by rfl) ⟨419399, by rfl⟩ : syracuseStep 559199 = 838799) B838799
theorem B559227 : Blo 558808 559227 := bstep (se 1 (by rfl) ⟨419420, by rfl⟩ : syracuseStep 559227 = 838841) B838841
theorem B559279 : Blo 558808 559279 := bstep (se 1 (by rfl) ⟨419459, by rfl⟩ : syracuseStep 559279 = 838919) B838919
theorem B559303 : Blo 558808 559303 := bstep (se 1 (by rfl) ⟨419477, by rfl⟩ : syracuseStep 559303 = 838955) B838955
theorem B559323 : Blo 558808 559323 := bstep (se 1 (by rfl) ⟨419492, by rfl⟩ : syracuseStep 559323 = 838985) B838985
theorem B559399 : Blo 558808 559399 := bstep (se 1 (by rfl) ⟨419549, by rfl⟩ : syracuseStep 559399 = 839099) B839099
theorem B12093745 : Blo 558808 12093745 := bstep (se 2 (by rfl) ⟨4535154, by rfl⟩ : syracuseStep 12093745 = 9070309) B9070309
theorem B559439 : Blo 558808 559439 := bstep (se 1 (by rfl) ⟨419579, by rfl⟩ : syracuseStep 559439 = 839159) B839159
theorem B559455 : Blo 558808 559455 := bstep (se 1 (by rfl) ⟨419591, by rfl⟩ : syracuseStep 559455 = 839183) B839183
theorem B559483 : Blo 558808 559483 := bstep (se 1 (by rfl) ⟨419612, by rfl⟩ : syracuseStep 559483 = 839225) B839225
theorem B6064517 : Blo 558808 6064517 := bstep (se 4 (by rfl) ⟨568548, by rfl⟩ : syracuseStep 6064517 = 1137097) B1137097
theorem B559535 : Blo 558808 559535 := bstep (se 1 (by rfl) ⟨419651, by rfl⟩ : syracuseStep 559535 = 839303) B839303
theorem B559559 : Blo 558808 559559 := bstep (se 1 (by rfl) ⟨419669, by rfl⟩ : syracuseStep 559559 = 839339) B839339
theorem B559579 : Blo 558808 559579 := bstep (se 1 (by rfl) ⟨419684, by rfl⟩ : syracuseStep 559579 = 839369) B839369
theorem B854491 : Blo 558808 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B30771683 : Blo 558808 30771683 := bstep (se 1 (by rfl) ⟨23078762, by rfl⟩ : syracuseStep 30771683 = 46157525) B46157525
theorem B559655 : Blo 558808 559655 := bstep (se 1 (by rfl) ⟨419741, by rfl⟩ : syracuseStep 559655 = 839483) B839483
theorem B559695 : Blo 558808 559695 := bstep (se 1 (by rfl) ⟨419771, by rfl⟩ : syracuseStep 559695 = 839543) B839543
theorem B559711 : Blo 558808 559711 := bstep (se 1 (by rfl) ⟨419783, by rfl⟩ : syracuseStep 559711 = 839567) B839567
theorem B559739 : Blo 558808 559739 := bstep (se 1 (by rfl) ⟨419804, by rfl⟩ : syracuseStep 559739 = 839609) B839609
theorem B10783367 : Blo 558808 10783367 := bstep (se 1 (by rfl) ⟨8087525, by rfl⟩ : syracuseStep 10783367 = 16175051) B16175051
theorem B559791 : Blo 558808 559791 := bstep (se 1 (by rfl) ⟨419843, by rfl⟩ : syracuseStep 559791 = 839687) B839687
theorem B559815 : Blo 558808 559815 := bstep (se 1 (by rfl) ⟨419861, by rfl⟩ : syracuseStep 559815 = 839723) B839723
theorem B2132689 : Blo 558808 2132689 := bstep (se 2 (by rfl) ⟨799758, by rfl⟩ : syracuseStep 2132689 = 1599517) B1599517
theorem B559835 : Blo 558808 559835 := bstep (se 1 (by rfl) ⟨419876, by rfl⟩ : syracuseStep 559835 = 839753) B839753
theorem B559911 : Blo 558808 559911 := bstep (se 1 (by rfl) ⟨419933, by rfl⟩ : syracuseStep 559911 = 839867) B839867
theorem B559951 : Blo 558808 559951 := bstep (se 1 (by rfl) ⟨419963, by rfl⟩ : syracuseStep 559951 = 839927) B839927
theorem B559967 : Blo 558808 559967 := bstep (se 1 (by rfl) ⟨419975, by rfl⟩ : syracuseStep 559967 = 839951) B839951
theorem B559995 : Blo 558808 559995 := bstep (se 1 (by rfl) ⟨419996, by rfl⟩ : syracuseStep 559995 = 839993) B839993
theorem B560047 : Blo 558808 560047 := bstep (se 1 (by rfl) ⟨420035, by rfl⟩ : syracuseStep 560047 = 840071) B840071
theorem B1280951 : Blo 558808 1280951 := bstep (se 1 (by rfl) ⟨960713, by rfl⟩ : syracuseStep 1280951 = 1921427) B1921427
theorem B560071 : Blo 558808 560071 := bstep (se 1 (by rfl) ⟨420053, by rfl⟩ : syracuseStep 560071 = 840107) B840107
theorem B560091 : Blo 558808 560091 := bstep (se 1 (by rfl) ⟨420068, by rfl⟩ : syracuseStep 560091 = 840137) B840137
theorem B2132993 : Blo 558808 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B560167 : Blo 558808 560167 := bstep (se 1 (by rfl) ⟨420125, by rfl⟩ : syracuseStep 560167 = 840251) B840251
theorem B560207 : Blo 558808 560207 := bstep (se 1 (by rfl) ⟨420155, by rfl⟩ : syracuseStep 560207 = 840311) B840311
theorem B560223 : Blo 558808 560223 := bstep (se 1 (by rfl) ⟨420167, by rfl⟩ : syracuseStep 560223 = 840335) B840335
theorem B560251 : Blo 558808 560251 := bstep (se 1 (by rfl) ⟨420188, by rfl⟩ : syracuseStep 560251 = 840377) B840377
theorem B560303 : Blo 558808 560303 := bstep (se 1 (by rfl) ⟨420227, by rfl⟩ : syracuseStep 560303 = 840455) B840455
theorem B560327 : Blo 558808 560327 := bstep (se 1 (by rfl) ⟨420245, by rfl⟩ : syracuseStep 560327 = 840491) B840491
theorem B560347 : Blo 558808 560347 := bstep (se 1 (by rfl) ⟨420260, by rfl⟩ : syracuseStep 560347 = 840521) B840521
theorem B4263191 : Blo 558808 4263191 := bstep (se 1 (by rfl) ⟨3197393, by rfl⟩ : syracuseStep 4263191 = 6394787) B6394787
theorem B560423 : Blo 558808 560423 := bstep (se 1 (by rfl) ⟨420317, by rfl⟩ : syracuseStep 560423 = 840635) B840635
theorem B560463 : Blo 558808 560463 := bstep (se 1 (by rfl) ⟨420347, by rfl⟩ : syracuseStep 560463 = 840695) B840695
theorem B560479 : Blo 558808 560479 := bstep (se 1 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 560479 = 840719) B840719
theorem B560507 : Blo 558808 560507 := bstep (se 1 (by rfl) ⟨420380, by rfl⟩ : syracuseStep 560507 = 840761) B840761
theorem B560559 : Blo 558808 560559 := bstep (se 1 (by rfl) ⟨420419, by rfl⟩ : syracuseStep 560559 = 840839) B840839
theorem B560583 : Blo 558808 560583 := bstep (se 1 (by rfl) ⟨420437, by rfl⟩ : syracuseStep 560583 = 840875) B840875
theorem B2133449 : Blo 558808 2133449 := bstep (se 2 (by rfl) ⟨800043, by rfl⟩ : syracuseStep 2133449 = 1600087) B1600087
theorem B560603 : Blo 558808 560603 := bstep (se 1 (by rfl) ⟨420452, by rfl⟩ : syracuseStep 560603 = 840905) B840905
theorem B560679 : Blo 558808 560679 := bstep (se 1 (by rfl) ⟨420509, by rfl⟩ : syracuseStep 560679 = 841019) B841019
theorem B560719 : Blo 558808 560719 := bstep (se 1 (by rfl) ⟨420539, by rfl⟩ : syracuseStep 560719 = 841079) B841079
theorem B560735 : Blo 558808 560735 := bstep (se 1 (by rfl) ⟨420551, by rfl⟩ : syracuseStep 560735 = 841103) B841103
theorem B560763 : Blo 558808 560763 := bstep (se 1 (by rfl) ⟨420572, by rfl⟩ : syracuseStep 560763 = 841145) B841145
theorem B560815 : Blo 558808 560815 := bstep (se 1 (by rfl) ⟨420611, by rfl⟩ : syracuseStep 560815 = 841223) B841223
theorem B560839 : Blo 558808 560839 := bstep (se 1 (by rfl) ⟨420629, by rfl⟩ : syracuseStep 560839 = 841259) B841259
theorem B560859 : Blo 558808 560859 := bstep (se 1 (by rfl) ⟨420644, by rfl⟩ : syracuseStep 560859 = 841289) B841289
theorem B560935 : Blo 558808 560935 := bstep (se 1 (by rfl) ⟨420701, by rfl⟩ : syracuseStep 560935 = 841403) B841403
theorem B560975 : Blo 558808 560975 := bstep (se 1 (by rfl) ⟨420731, by rfl⟩ : syracuseStep 560975 = 841463) B841463
theorem B560991 : Blo 558808 560991 := bstep (se 1 (by rfl) ⟨420743, by rfl⟩ : syracuseStep 560991 = 841487) B841487
theorem B561019 : Blo 558808 561019 := bstep (se 1 (by rfl) ⟨420764, by rfl⟩ : syracuseStep 561019 = 841529) B841529
theorem B561071 : Blo 558808 561071 := bstep (se 1 (by rfl) ⟨420803, by rfl⟩ : syracuseStep 561071 = 841607) B841607
theorem B2133935 : Blo 558808 2133935 := bstep (se 1 (by rfl) ⟨1600451, by rfl⟩ : syracuseStep 2133935 = 3200903) B3200903
theorem B561095 : Blo 558808 561095 := bstep (se 1 (by rfl) ⟨420821, by rfl⟩ : syracuseStep 561095 = 841643) B841643
theorem B561115 : Blo 558808 561115 := bstep (se 1 (by rfl) ⟨420836, by rfl⟩ : syracuseStep 561115 = 841673) B841673
theorem B561191 : Blo 558808 561191 := bstep (se 1 (by rfl) ⟨420893, by rfl⟩ : syracuseStep 561191 = 841787) B841787
theorem B561231 : Blo 558808 561231 := bstep (se 1 (by rfl) ⟨420923, by rfl⟩ : syracuseStep 561231 = 841847) B841847
theorem B561247 : Blo 558808 561247 := bstep (se 1 (by rfl) ⟨420935, by rfl⟩ : syracuseStep 561247 = 841871) B841871
theorem B561275 : Blo 558808 561275 := bstep (se 1 (by rfl) ⟨420956, by rfl⟩ : syracuseStep 561275 = 841913) B841913
theorem B561327 : Blo 558808 561327 := bstep (se 1 (by rfl) ⟨420995, by rfl⟩ : syracuseStep 561327 = 841991) B841991
theorem B561351 : Blo 558808 561351 := bstep (se 1 (by rfl) ⟨421013, by rfl⟩ : syracuseStep 561351 = 842027) B842027
theorem B561371 : Blo 558808 561371 := bstep (se 1 (by rfl) ⟨421028, by rfl⟩ : syracuseStep 561371 = 842057) B842057
theorem B4624651 : Blo 558808 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B561447 : Blo 558808 561447 := bstep (se 1 (by rfl) ⟨421085, by rfl⟩ : syracuseStep 561447 = 842171) B842171
theorem B4559165 : Blo 558808 4559165 := bstep (se 3 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 4559165 = 1709687) B1709687
theorem B561487 : Blo 558808 561487 := bstep (se 1 (by rfl) ⟨421115, by rfl⟩ : syracuseStep 561487 = 842231) B842231
theorem B561503 : Blo 558808 561503 := bstep (se 1 (by rfl) ⟨421127, by rfl⟩ : syracuseStep 561503 = 842255) B842255
theorem B561531 : Blo 558808 561531 := bstep (se 1 (by rfl) ⟨421148, by rfl⟩ : syracuseStep 561531 = 842297) B842297
theorem B561583 : Blo 558808 561583 := bstep (se 1 (by rfl) ⟨421187, by rfl⟩ : syracuseStep 561583 = 842375) B842375
theorem B561607 : Blo 558808 561607 := bstep (se 1 (by rfl) ⟨421205, by rfl⟩ : syracuseStep 561607 = 842411) B842411
theorem B561627 : Blo 558808 561627 := bstep (se 1 (by rfl) ⟨421220, by rfl⟩ : syracuseStep 561627 = 842441) B842441
theorem B561703 : Blo 558808 561703 := bstep (se 1 (by rfl) ⟨421277, by rfl⟩ : syracuseStep 561703 = 842555) B842555
theorem B561743 : Blo 558808 561743 := bstep (se 1 (by rfl) ⟨421307, by rfl⟩ : syracuseStep 561743 = 842615) B842615
theorem B561759 : Blo 558808 561759 := bstep (se 1 (by rfl) ⟨421319, by rfl⟩ : syracuseStep 561759 = 842639) B842639
theorem B561787 : Blo 558808 561787 := bstep (se 1 (by rfl) ⟨421340, by rfl⟩ : syracuseStep 561787 = 842681) B842681
theorem B561839 : Blo 558808 561839 := bstep (se 1 (by rfl) ⟨421379, by rfl⟩ : syracuseStep 561839 = 842759) B842759
theorem B561863 : Blo 558808 561863 := bstep (se 1 (by rfl) ⟨421397, by rfl⟩ : syracuseStep 561863 = 842795) B842795
theorem B4264649 : Blo 558808 4264649 := bstep (se 2 (by rfl) ⟨1599243, by rfl⟩ : syracuseStep 4264649 = 3198487) B3198487
theorem B561883 : Blo 558808 561883 := bstep (se 1 (by rfl) ⟨421412, by rfl⟩ : syracuseStep 561883 = 842825) B842825
theorem B561959 : Blo 558808 561959 := bstep (se 1 (by rfl) ⟨421469, by rfl⟩ : syracuseStep 561959 = 842939) B842939
theorem B561999 : Blo 558808 561999 := bstep (se 1 (by rfl) ⟨421499, by rfl⟩ : syracuseStep 561999 = 842999) B842999
theorem B562015 : Blo 558808 562015 := bstep (se 1 (by rfl) ⟨421511, by rfl⟩ : syracuseStep 562015 = 843023) B843023
theorem B562043 : Blo 558808 562043 := bstep (se 1 (by rfl) ⟨421532, by rfl⟩ : syracuseStep 562043 = 843065) B843065
theorem B562095 : Blo 558808 562095 := bstep (se 1 (by rfl) ⟨421571, by rfl⟩ : syracuseStep 562095 = 843143) B843143
theorem B562119 : Blo 558808 562119 := bstep (se 1 (by rfl) ⟨421589, by rfl⟩ : syracuseStep 562119 = 843179) B843179
theorem B562139 : Blo 558808 562139 := bstep (se 1 (by rfl) ⟨421604, by rfl⟩ : syracuseStep 562139 = 843209) B843209
theorem B562215 : Blo 558808 562215 := bstep (se 1 (by rfl) ⟨421661, by rfl⟩ : syracuseStep 562215 = 843323) B843323
theorem B562255 : Blo 558808 562255 := bstep (se 1 (by rfl) ⟨421691, by rfl⟩ : syracuseStep 562255 = 843383) B843383
theorem B2135119 : Blo 558808 2135119 := bstep (se 1 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 2135119 = 3202679) B3202679
theorem B562271 : Blo 558808 562271 := bstep (se 1 (by rfl) ⟨421703, by rfl⟩ : syracuseStep 562271 = 843407) B843407
theorem B562299 : Blo 558808 562299 := bstep (se 1 (by rfl) ⟨421724, by rfl⟩ : syracuseStep 562299 = 843449) B843449
theorem B562351 : Blo 558808 562351 := bstep (se 1 (by rfl) ⟨421763, by rfl⟩ : syracuseStep 562351 = 843527) B843527
theorem B562375 : Blo 558808 562375 := bstep (se 1 (by rfl) ⟨421781, by rfl⟩ : syracuseStep 562375 = 843563) B843563
theorem B562395 : Blo 558808 562395 := bstep (se 1 (by rfl) ⟨421796, by rfl⟩ : syracuseStep 562395 = 843593) B843593
theorem B2397431 : Blo 558808 2397431 := bstep (se 1 (by rfl) ⟨1798073, by rfl⟩ : syracuseStep 2397431 = 3596147) B3596147
theorem B13604111 : Blo 558808 13604111 := bstep (se 1 (by rfl) ⟨10203083, by rfl⟩ : syracuseStep 13604111 = 20406167) B20406167
theorem B562471 : Blo 558808 562471 := bstep (se 1 (by rfl) ⟨421853, by rfl⟩ : syracuseStep 562471 = 843707) B843707
theorem B562511 : Blo 558808 562511 := bstep (se 1 (by rfl) ⟨421883, by rfl⟩ : syracuseStep 562511 = 843767) B843767
theorem B562527 : Blo 558808 562527 := bstep (se 1 (by rfl) ⟨421895, by rfl⟩ : syracuseStep 562527 = 843791) B843791
theorem B1348969 : Blo 558808 1348969 := bstep (se 2 (by rfl) ⟨505863, by rfl⟩ : syracuseStep 1348969 = 1011727) B1011727
theorem B562555 : Blo 558808 562555 := bstep (se 1 (by rfl) ⟨421916, by rfl⟩ : syracuseStep 562555 = 843833) B843833
theorem B1414543 : Blo 558808 1414543 := bstep (se 1 (by rfl) ⟨1060907, by rfl⟩ : syracuseStep 1414543 = 2121815) B2121815
theorem B562607 : Blo 558808 562607 := bstep (se 1 (by rfl) ⟨421955, by rfl⟩ : syracuseStep 562607 = 843911) B843911
theorem B562631 : Blo 558808 562631 := bstep (se 1 (by rfl) ⟨421973, by rfl⟩ : syracuseStep 562631 = 843947) B843947
theorem B562651 : Blo 558808 562651 := bstep (se 1 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 562651 = 843977) B843977
theorem B2135591 : Blo 558808 2135591 := bstep (se 1 (by rfl) ⟨1601693, by rfl⟩ : syracuseStep 2135591 = 3203387) B3203387
theorem B562727 : Blo 558808 562727 := bstep (se 1 (by rfl) ⟨422045, by rfl⟩ : syracuseStep 562727 = 844091) B844091
theorem B562767 : Blo 558808 562767 := bstep (se 1 (by rfl) ⟨422075, by rfl⟩ : syracuseStep 562767 = 844151) B844151
theorem B562783 : Blo 558808 562783 := bstep (se 1 (by rfl) ⟨422087, by rfl⟩ : syracuseStep 562783 = 844175) B844175
theorem B1414867 : Blo 558808 1414867 := bstep (se 1 (by rfl) ⟨1061150, by rfl⟩ : syracuseStep 1414867 = 2122301) B2122301
theorem B628699 : Blo 558808 628699 := bstep (se 1 (by rfl) ⟨471524, by rfl⟩ : syracuseStep 628699 = 943049) B943049
theorem B1350017 : Blo 558808 1350017 := bstep (se 2 (by rfl) ⟨506256, by rfl⟩ : syracuseStep 1350017 = 1012513) B1012513
theorem B629167 : Blo 558808 629167 := bstep (se 1 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 629167 = 943751) B943751
theorem B2136563 : Blo 558808 2136563 := bstep (se 1 (by rfl) ⟨1602422, by rfl⟩ : syracuseStep 2136563 = 3204845) B3204845
theorem B2398729 : Blo 558808 2398729 := bstep (se 2 (by rfl) ⟨899523, by rfl⟩ : syracuseStep 2398729 = 1799047) B1799047
theorem B1415819 : Blo 558808 1415819 := bstep (se 1 (by rfl) ⟨1061864, by rfl⟩ : syracuseStep 1415819 = 2123729) B2123729
theorem B629599 : Blo 558808 629599 := bstep (se 1 (by rfl) ⟨472199, by rfl⟩ : syracuseStep 629599 = 944399) B944399
theorem B4037681 : Blo 558808 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B629959 : Blo 558808 629959 := bstep (se 1 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 629959 = 944939) B944939
theorem B3186323 : Blo 558808 3186323 := bstep (se 1 (by rfl) ⟨2389742, by rfl⟩ : syracuseStep 3186323 = 4779485) B4779485
theorem B2399959 : Blo 558808 2399959 := bstep (se 1 (by rfl) ⟨1799969, by rfl⟩ : syracuseStep 2399959 = 3599939) B3599939
theorem B1416953 : Blo 558808 1416953 := bstep (se 2 (by rfl) ⟨531357, by rfl⟩ : syracuseStep 1416953 = 1062715) B1062715
theorem B1417135 : Blo 558808 1417135 := bstep (se 1 (by rfl) ⟨1062851, by rfl⟩ : syracuseStep 1417135 = 2125703) B2125703
theorem B630823 : Blo 558808 630823 := bstep (se 1 (by rfl) ⟨473117, by rfl⟩ : syracuseStep 630823 = 946235) B946235
theorem B598367 : Blo 558808 598367 := bstep (se 1 (by rfl) ⟨448775, by rfl⟩ : syracuseStep 598367 = 897551) B897551
theorem B958825 : Blo 558808 958825 := bstep (se 2 (by rfl) ⟨359559, by rfl⟩ : syracuseStep 958825 = 719119) B719119
theorem B1417601 : Blo 558808 1417601 := bstep (se 2 (by rfl) ⟨531600, by rfl⟩ : syracuseStep 1417601 = 1063201) B1063201
theorem B9609677 : Blo 558808 9609677 := bstep (se 3 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 9609677 = 3603629) B3603629
theorem B10756759 : Blo 558808 10756759 := bstep (se 1 (by rfl) ⟨8067569, by rfl⟩ : syracuseStep 10756759 = 16135139) B16135139
theorem B1418057 : Blo 558808 1418057 := bstep (se 2 (by rfl) ⟨531771, by rfl⟩ : syracuseStep 1418057 = 1063543) B1063543
theorem B2696111 : Blo 558808 2696111 := bstep (se 1 (by rfl) ⟨2022083, by rfl⟩ : syracuseStep 2696111 = 4044167) B4044167
theorem B1418411 : Blo 558808 1418411 := bstep (se 1 (by rfl) ⟨1063808, by rfl⟩ : syracuseStep 1418411 = 2127617) B2127617
theorem B1025615 : Blo 558808 1025615 := bstep (se 1 (by rfl) ⟨769211, by rfl⟩ : syracuseStep 1025615 = 1538423) B1538423
theorem B632443 : Blo 558808 632443 := bstep (se 1 (by rfl) ⟨474332, by rfl⟩ : syracuseStep 632443 = 948665) B948665
theorem B6367085 : Blo 558808 6367085 := bstep (se 3 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 6367085 = 2387657) B2387657
theorem B1419191 : Blo 558808 1419191 := bstep (se 1 (by rfl) ⟨1064393, by rfl⟩ : syracuseStep 1419191 = 2128787) B2128787
theorem B8660945 : Blo 558808 8660945 := bstep (se 2 (by rfl) ⟨3247854, by rfl⟩ : syracuseStep 8660945 = 6495709) B6495709
theorem B632911 : Blo 558808 632911 := bstep (se 1 (by rfl) ⟨474683, by rfl⟩ : syracuseStep 632911 = 949367) B949367
theorem B5384839 : Blo 558808 5384839 := bstep (se 1 (by rfl) ⟨4038629, by rfl⟩ : syracuseStep 5384839 = 8077259) B8077259
theorem B7383737 : Blo 558808 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B1518443 : Blo 558808 1518443 := bstep (se 1 (by rfl) ⟨1138832, by rfl⟩ : syracuseStep 1518443 = 2277665) B2277665
theorem B1420193 : Blo 558808 1420193 := bstep (se 2 (by rfl) ⟨532572, by rfl⟩ : syracuseStep 1420193 = 1065145) B1065145
theorem B4304119 : Blo 558808 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B1420649 : Blo 558808 1420649 := bstep (se 2 (by rfl) ⟨532743, by rfl⟩ : syracuseStep 1420649 = 1065487) B1065487
theorem B4107763 : Blo 558808 4107763 := bstep (se 1 (by rfl) ⟨3080822, by rfl⟩ : syracuseStep 4107763 = 6161645) B6161645
theorem B2272967 : Blo 558808 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B4271939 : Blo 558808 4271939 := bstep (se 1 (by rfl) ⟨3203954, by rfl⟩ : syracuseStep 4271939 = 6407909) B6407909
theorem B4599737 : Blo 558808 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B896987 : Blo 558808 896987 := bstep (se 1 (by rfl) ⟨672740, by rfl⟩ : syracuseStep 896987 = 1345481) B1345481
theorem B1257479 : Blo 558808 1257479 := bstep (se 1 (by rfl) ⟨943109, by rfl⟩ : syracuseStep 1257479 = 1886219) B1886219
theorem B6402077 : Blo 558808 6402077 := bstep (se 3 (by rfl) ⟨1200389, by rfl⟩ : syracuseStep 6402077 = 2400779) B2400779
theorem B1257551 : Blo 558808 1257551 := bstep (se 1 (by rfl) ⟨943163, by rfl⟩ : syracuseStep 1257551 = 1886327) B1886327
theorem B1061075 : Blo 558808 1061075 := bstep (se 1 (by rfl) ⟨795806, by rfl⟩ : syracuseStep 1061075 = 1591613) B1591613
theorem B1061113 : Blo 558808 1061113 := bstep (se 2 (by rfl) ⟨397917, by rfl⟩ : syracuseStep 1061113 = 795835) B795835
theorem B3027287 : Blo 558808 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B1257947 : Blo 558808 1257947 := bstep (se 1 (by rfl) ⟨943460, by rfl⟩ : syracuseStep 1257947 = 1886921) B1886921
theorem B1421833 : Blo 558808 1421833 := bstep (se 2 (by rfl) ⟨533187, by rfl⟩ : syracuseStep 1421833 = 1066375) B1066375
theorem B2699801 : Blo 558808 2699801 := bstep (se 2 (by rfl) ⟨1012425, by rfl⟩ : syracuseStep 2699801 = 2024851) B2024851
theorem B6370001 : Blo 558808 6370001 := bstep (se 2 (by rfl) ⟨2388750, by rfl⟩ : syracuseStep 6370001 = 4777501) B4777501
theorem B1258415 : Blo 558808 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B1061819 : Blo 558808 1061819 := bstep (se 1 (by rfl) ⟨796364, by rfl⟩ : syracuseStep 1061819 = 1592729) B1592729
theorem B9122867 : Blo 558808 9122867 := bstep (se 1 (by rfl) ⟨6842150, by rfl⟩ : syracuseStep 9122867 = 13684301) B13684301
theorem B38810765 : Blo 558808 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B1258667 : Blo 558808 1258667 := bstep (se 1 (by rfl) ⟨944000, by rfl⟩ : syracuseStep 1258667 = 1888001) B1888001
theorem B2274571 : Blo 558808 2274571 := bstep (se 1 (by rfl) ⟨1705928, by rfl⟩ : syracuseStep 2274571 = 3411857) B3411857
theorem B898409 : Blo 558808 898409 := bstep (se 2 (by rfl) ⟨336903, by rfl⟩ : syracuseStep 898409 = 673807) B673807
theorem B2831759 : Blo 558808 2831759 := bstep (se 1 (by rfl) ⟨2123819, by rfl⟩ : syracuseStep 2831759 = 4247639) B4247639
theorem B1062305 : Blo 558808 1062305 := bstep (se 2 (by rfl) ⟨398364, by rfl⟩ : syracuseStep 1062305 = 796729) B796729
theorem B1062571 : Blo 558808 1062571 := bstep (se 1 (by rfl) ⟨796928, by rfl⟩ : syracuseStep 1062571 = 1593857) B1593857
theorem B1259207 : Blo 558808 1259207 := bstep (se 1 (by rfl) ⟨944405, by rfl⟩ : syracuseStep 1259207 = 1888811) B1888811
theorem B6043501 : Blo 558808 6043501 := bstep (se 3 (by rfl) ⟨1133156, by rfl⟩ : syracuseStep 6043501 = 2266313) B2266313
theorem B1193915 : Blo 558808 1193915 := bstep (se 1 (by rfl) ⟨895436, by rfl⟩ : syracuseStep 1193915 = 1790873) B1790873
theorem B1423291 : Blo 558808 1423291 := bstep (se 1 (by rfl) ⟨1067468, by rfl⟩ : syracuseStep 1423291 = 2134937) B2134937
theorem B1062875 : Blo 558808 1062875 := bstep (se 1 (by rfl) ⟨797156, by rfl⟩ : syracuseStep 1062875 = 1594313) B1594313
theorem B1260071 : Blo 558808 1260071 := bstep (se 1 (by rfl) ⟨945053, by rfl⟩ : syracuseStep 1260071 = 1890107) B1890107
theorem B3652231 : Blo 558808 3652231 := bstep (se 1 (by rfl) ⟨2739173, by rfl⟩ : syracuseStep 3652231 = 5478347) B5478347
theorem B1620695 : Blo 558808 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B1260395 : Blo 558808 1260395 := bstep (se 1 (by rfl) ⟨945296, by rfl⟩ : syracuseStep 1260395 = 1890593) B1890593
theorem B899947 : Blo 558808 899947 := bstep (se 1 (by rfl) ⟨674960, by rfl⟩ : syracuseStep 899947 = 1349921) B1349921
theorem B1260449 : Blo 558808 1260449 := bstep (se 2 (by rfl) ⟨472668, by rfl⟩ : syracuseStep 1260449 = 945337) B945337
theorem B2276257 : Blo 558808 2276257 := bstep (se 2 (by rfl) ⟨853596, by rfl⟩ : syracuseStep 2276257 = 1707193) B1707193
theorem B1063945 : Blo 558808 1063945 := bstep (se 2 (by rfl) ⟨398979, by rfl⟩ : syracuseStep 1063945 = 797959) B797959
theorem B1260791 : Blo 558808 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B4046071 : Blo 558808 4046071 := bstep (se 1 (by rfl) ⟨3034553, by rfl⟩ : syracuseStep 4046071 = 6069107) B6069107
theorem B2833865 : Blo 558808 2833865 := bstep (se 2 (by rfl) ⟨1062699, by rfl⟩ : syracuseStep 2833865 = 2125399) B2125399
theorem B1064659 : Blo 558808 1064659 := bstep (se 1 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 1064659 = 1596989) B1596989
theorem B900857 : Blo 558808 900857 := bstep (se 2 (by rfl) ⟨337821, by rfl⟩ : syracuseStep 900857 = 675643) B675643
theorem B1261385 : Blo 558808 1261385 := bstep (se 2 (by rfl) ⟨473019, by rfl⟩ : syracuseStep 1261385 = 946039) B946039
theorem B2703223 : Blo 558808 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B2834513 : Blo 558808 2834513 := bstep (se 2 (by rfl) ⟨1062942, by rfl⟩ : syracuseStep 2834513 = 2125885) B2125885
theorem B901369 : Blo 558808 901369 := bstep (se 2 (by rfl) ⟨338013, by rfl⟩ : syracuseStep 901369 = 676027) B676027
theorem B7192907 : Blo 558808 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B3588457 : Blo 558808 3588457 := bstep (se 2 (by rfl) ⟨1345671, by rfl⟩ : syracuseStep 3588457 = 2691343) B2691343
theorem B1065403 : Blo 558808 1065403 := bstep (se 1 (by rfl) ⟨799052, by rfl⟩ : syracuseStep 1065403 = 1598105) B1598105
theorem B1262177 : Blo 558808 1262177 := bstep (se 2 (by rfl) ⟨473316, by rfl⟩ : syracuseStep 1262177 = 946633) B946633
theorem B1065889 : Blo 558808 1065889 := bstep (se 2 (by rfl) ⟨399708, by rfl⟩ : syracuseStep 1065889 = 799417) B799417
theorem B9552815 : Blo 558808 9552815 := bstep (se 1 (by rfl) ⟨7164611, by rfl⟩ : syracuseStep 9552815 = 14329223) B14329223
theorem B1262519 : Blo 558808 1262519 := bstep (se 1 (by rfl) ⟨946889, by rfl⟩ : syracuseStep 1262519 = 1893779) B1893779
theorem B1066459 : Blo 558808 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B1263113 : Blo 558808 1263113 := bstep (se 2 (by rfl) ⟨473667, by rfl⟩ : syracuseStep 1263113 = 947335) B947335
theorem B607943 : Blo 558808 607943 := bstep (se 1 (by rfl) ⟨455957, by rfl⟩ : syracuseStep 607943 = 911915) B911915
theorem B7161695 : Blo 558808 7161695 := bstep (se 1 (by rfl) ⟨5371271, by rfl⟩ : syracuseStep 7161695 = 10742543) B10742543
theorem B1263455 : Blo 558808 1263455 := bstep (se 1 (by rfl) ⟨947591, by rfl⟩ : syracuseStep 1263455 = 1895183) B1895183
theorem B1263635 : Blo 558808 1263635 := bstep (se 1 (by rfl) ⟨947726, by rfl⟩ : syracuseStep 1263635 = 1895453) B1895453
theorem B1263977 : Blo 558808 1263977 := bstep (se 2 (by rfl) ⟨473991, by rfl⟩ : syracuseStep 1263977 = 947983) B947983
theorem B6375833 : Blo 558808 6375833 := bstep (se 2 (by rfl) ⟨2390937, by rfl⟩ : syracuseStep 6375833 = 4781875) B4781875
theorem B3590689 : Blo 558808 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B1886759 : Blo 558808 1886759 := bstep (se 1 (by rfl) ⟨1415069, by rfl⟩ : syracuseStep 1886759 = 2830139) B2830139
theorem B1198631 : Blo 558808 1198631 := bstep (se 1 (by rfl) ⟨898973, by rfl⟩ : syracuseStep 1198631 = 1797947) B1797947
theorem B838223 : Blo 558808 838223 := bstep (se 1 (by rfl) ⟨628667, by rfl⟩ : syracuseStep 838223 = 1257335) B1257335
theorem B1886867 : Blo 558808 1886867 := bstep (se 1 (by rfl) ⟨1415150, by rfl⟩ : syracuseStep 1886867 = 2830301) B2830301
theorem B838343 : Blo 558808 838343 := bstep (se 1 (by rfl) ⟨628757, by rfl⟩ : syracuseStep 838343 = 1257515) B1257515
theorem B1198921 : Blo 558808 1198921 := bstep (se 2 (by rfl) ⟨449595, by rfl⟩ : syracuseStep 1198921 = 899191) B899191
theorem B838505 : Blo 558808 838505 := bstep (se 2 (by rfl) ⟨314439, by rfl⟩ : syracuseStep 838505 = 628879) B628879
theorem B1887083 : Blo 558808 1887083 := bstep (se 1 (by rfl) ⟨1415312, by rfl⟩ : syracuseStep 1887083 = 2830625) B2830625
theorem B1198955 : Blo 558808 1198955 := bstep (se 1 (by rfl) ⟨899216, by rfl⟩ : syracuseStep 1198955 = 1798433) B1798433
theorem B1887137 : Blo 558808 1887137 := bstep (se 2 (by rfl) ⟨707676, by rfl⟩ : syracuseStep 1887137 = 1415353) B1415353
theorem B1362863 : Blo 558808 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B838583 : Blo 558808 838583 := bstep (se 1 (by rfl) ⟨628937, by rfl⟩ : syracuseStep 838583 = 1257875) B1257875
theorem B6048695 : Blo 558808 6048695 := bstep (se 1 (by rfl) ⟨4536521, by rfl⟩ : syracuseStep 6048695 = 9073043) B9073043
theorem B1264571 : Blo 558808 1264571 := bstep (se 1 (by rfl) ⟨948428, by rfl⟩ : syracuseStep 1264571 = 1896857) B1896857
theorem B838619 : Blo 558808 838619 := bstep (se 1 (by rfl) ⟨628964, by rfl⟩ : syracuseStep 838619 = 1257929) B1257929
theorem B1264697 : Blo 558808 1264697 := bstep (se 2 (by rfl) ⟨474261, by rfl⟩ : syracuseStep 1264697 = 948523) B948523
theorem B1592399 : Blo 558808 1592399 := bstep (se 1 (by rfl) ⟨1194299, by rfl⟩ : syracuseStep 1592399 = 2388599) B2388599
theorem B707707 : Blo 558808 707707 := bstep (se 1 (by rfl) ⟨530780, by rfl⟩ : syracuseStep 707707 = 1061561) B1061561
theorem B707935 : Blo 558808 707935 := bstep (se 1 (by rfl) ⟨530951, by rfl⟩ : syracuseStep 707935 = 1061903) B1061903
theorem B1265039 : Blo 558808 1265039 := bstep (se 1 (by rfl) ⟨948779, by rfl⟩ : syracuseStep 1265039 = 1897559) B1897559
theorem B839087 : Blo 558808 839087 := bstep (se 1 (by rfl) ⟨629315, by rfl⟩ : syracuseStep 839087 = 1258631) B1258631
theorem B1887731 : Blo 558808 1887731 := bstep (se 1 (by rfl) ⟨1415798, by rfl⟩ : syracuseStep 1887731 = 2831597) B2831597
theorem B839177 : Blo 558808 839177 := bstep (se 2 (by rfl) ⟨314691, by rfl⟩ : syracuseStep 839177 = 629383) B629383
theorem B839207 : Blo 558808 839207 := bstep (se 1 (by rfl) ⟨629405, by rfl⟩ : syracuseStep 839207 = 1258811) B1258811
theorem B839291 : Blo 558808 839291 := bstep (se 1 (by rfl) ⟨629468, by rfl⟩ : syracuseStep 839291 = 1258937) B1258937
theorem B1265363 : Blo 558808 1265363 := bstep (se 1 (by rfl) ⟨949022, by rfl⟩ : syracuseStep 1265363 = 1898045) B1898045
theorem B1593047 : Blo 558808 1593047 := bstep (se 1 (by rfl) ⟨1194785, by rfl⟩ : syracuseStep 1593047 = 2389571) B2389571
theorem B839417 : Blo 558808 839417 := bstep (se 2 (by rfl) ⟨314781, by rfl⟩ : syracuseStep 839417 = 629563) B629563
theorem B839519 : Blo 558808 839519 := bstep (se 1 (by rfl) ⟨629639, by rfl⟩ : syracuseStep 839519 = 1259279) B1259279
theorem B839531 : Blo 558808 839531 := bstep (se 1 (by rfl) ⟨629648, by rfl⟩ : syracuseStep 839531 = 1259297) B1259297
theorem B708527 : Blo 558808 708527 := bstep (se 1 (by rfl) ⟨531395, by rfl⟩ : syracuseStep 708527 = 1062791) B1062791
theorem B1888271 : Blo 558808 1888271 := bstep (se 1 (by rfl) ⟨1416203, by rfl⟩ : syracuseStep 1888271 = 2832407) B2832407
theorem B3199013 : Blo 558808 3199013 := bstep (se 4 (by rfl) ⟨299907, by rfl⟩ : syracuseStep 3199013 = 599815) B599815
theorem B1200185 : Blo 558808 1200185 := bstep (se 2 (by rfl) ⟨450069, by rfl⟩ : syracuseStep 1200185 = 900139) B900139
theorem B839759 : Blo 558808 839759 := bstep (se 1 (by rfl) ⟨629819, by rfl⟩ : syracuseStep 839759 = 1259639) B1259639
theorem B8605777 : Blo 558808 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B839879 : Blo 558808 839879 := bstep (se 1 (by rfl) ⟨629909, by rfl⟩ : syracuseStep 839879 = 1259819) B1259819
theorem B4608343 : Blo 558808 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B840041 : Blo 558808 840041 := bstep (se 2 (by rfl) ⟨315015, by rfl⟩ : syracuseStep 840041 = 630031) B630031
theorem B840119 : Blo 558808 840119 := bstep (se 1 (by rfl) ⟨630089, by rfl⟩ : syracuseStep 840119 = 1260179) B1260179
theorem B1921481 : Blo 558808 1921481 := bstep (se 2 (by rfl) ⟨720555, by rfl⟩ : syracuseStep 1921481 = 1441111) B1441111
theorem B840155 : Blo 558808 840155 := bstep (se 1 (by rfl) ⟨630116, by rfl⟩ : syracuseStep 840155 = 1260233) B1260233
theorem B2839049 : Blo 558808 2839049 := bstep (se 2 (by rfl) ⟨1064643, by rfl⟩ : syracuseStep 2839049 = 2129287) B2129287
theorem B3232315 : Blo 558808 3232315 := bstep (se 1 (by rfl) ⟨2424236, by rfl⟩ : syracuseStep 3232315 = 4848473) B4848473
theorem B1888865 : Blo 558808 1888865 := bstep (se 2 (by rfl) ⟨708324, by rfl⟩ : syracuseStep 1888865 = 1416649) B1416649
theorem B1266299 : Blo 558808 1266299 := bstep (se 1 (by rfl) ⟨949724, by rfl⟩ : syracuseStep 1266299 = 1899449) B1899449
theorem B840623 : Blo 558808 840623 := bstep (se 1 (by rfl) ⟨630467, by rfl⟩ : syracuseStep 840623 = 1260935) B1260935
theorem B1201159 : Blo 558808 1201159 := bstep (se 1 (by rfl) ⟨900869, by rfl⟩ : syracuseStep 1201159 = 1801739) B1801739
theorem B840713 : Blo 558808 840713 := bstep (se 2 (by rfl) ⟨315267, by rfl⟩ : syracuseStep 840713 = 630535) B630535
theorem B5100563 : Blo 558808 5100563 := bstep (se 1 (by rfl) ⟨3825422, by rfl⟩ : syracuseStep 5100563 = 7650845) B7650845
theorem B840743 : Blo 558808 840743 := bstep (se 1 (by rfl) ⟨630557, by rfl⟩ : syracuseStep 840743 = 1261115) B1261115
theorem B840827 : Blo 558808 840827 := bstep (se 1 (by rfl) ⟨630620, by rfl⟩ : syracuseStep 840827 = 1261241) B1261241
theorem B840953 : Blo 558808 840953 := bstep (se 2 (by rfl) ⟨315357, by rfl⟩ : syracuseStep 840953 = 630715) B630715
theorem B841055 : Blo 558808 841055 := bstep (se 1 (by rfl) ⟨630791, by rfl⟩ : syracuseStep 841055 = 1261583) B1261583
theorem B841067 : Blo 558808 841067 := bstep (se 1 (by rfl) ⟨630800, by rfl⟩ : syracuseStep 841067 = 1261601) B1261601
theorem B4052443 : Blo 558808 4052443 := bstep (se 1 (by rfl) ⟨3039332, by rfl⟩ : syracuseStep 4052443 = 6078665) B6078665
theorem B1136207 : Blo 558808 1136207 := bstep (se 1 (by rfl) ⟨852155, by rfl⟩ : syracuseStep 1136207 = 1704311) B1704311
theorem B841295 : Blo 558808 841295 := bstep (se 1 (by rfl) ⟨630971, by rfl⟩ : syracuseStep 841295 = 1261943) B1261943
theorem B841415 : Blo 558808 841415 := bstep (se 1 (by rfl) ⟨631061, by rfl⟩ : syracuseStep 841415 = 1262123) B1262123
theorem B4544237 : Blo 558808 4544237 := bstep (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) B1704089
theorem B841577 : Blo 558808 841577 := bstep (se 2 (by rfl) ⟨315591, by rfl⟩ : syracuseStep 841577 = 631183) B631183
theorem B841655 : Blo 558808 841655 := bstep (se 1 (by rfl) ⟨631241, by rfl⟩ : syracuseStep 841655 = 1262483) B1262483
theorem B2840507 : Blo 558808 2840507 := bstep (se 1 (by rfl) ⟨2130380, by rfl⟩ : syracuseStep 2840507 = 4260761) B4260761
theorem B841691 : Blo 558808 841691 := bstep (se 1 (by rfl) ⟨631268, by rfl⟩ : syracuseStep 841691 = 1262537) B1262537
theorem B1890323 : Blo 558808 1890323 := bstep (se 1 (by rfl) ⟨1417742, by rfl⟩ : syracuseStep 1890323 = 2835485) B2835485
theorem B3889181 : Blo 558808 3889181 := bstep (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) B1458443
theorem B1890647 : Blo 558808 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B1137001 : Blo 558808 1137001 := bstep (se 2 (by rfl) ⟨426375, by rfl⟩ : syracuseStep 1137001 = 852751) B852751
theorem B842159 : Blo 558808 842159 := bstep (se 1 (by rfl) ⟨631619, by rfl⟩ : syracuseStep 842159 = 1263239) B1263239
theorem B1792475 : Blo 558808 1792475 := bstep (se 1 (by rfl) ⟨1344356, by rfl⟩ : syracuseStep 1792475 = 2688713) B2688713
theorem B842249 : Blo 558808 842249 := bstep (se 2 (by rfl) ⟨315843, by rfl⟩ : syracuseStep 842249 = 631687) B631687
theorem B842279 : Blo 558808 842279 := bstep (se 1 (by rfl) ⟨631709, by rfl⟩ : syracuseStep 842279 = 1263419) B1263419
theorem B842363 : Blo 558808 842363 := bstep (se 1 (by rfl) ⟨631772, by rfl⟩ : syracuseStep 842363 = 1263545) B1263545
theorem B842489 : Blo 558808 842489 := bstep (se 2 (by rfl) ⟨315933, by rfl⟩ : syracuseStep 842489 = 631867) B631867
theorem B842591 : Blo 558808 842591 := bstep (se 1 (by rfl) ⟨631943, by rfl⟩ : syracuseStep 842591 = 1263887) B1263887
theorem B842603 : Blo 558808 842603 := bstep (se 1 (by rfl) ⟨631952, by rfl⟩ : syracuseStep 842603 = 1263905) B1263905
theorem B842831 : Blo 558808 842831 := bstep (se 1 (by rfl) ⟨632123, by rfl⟩ : syracuseStep 842831 = 1264247) B1264247
theorem B842951 : Blo 558808 842951 := bstep (se 1 (by rfl) ⟨632213, by rfl⟩ : syracuseStep 842951 = 1264427) B1264427
theorem B2841803 : Blo 558808 2841803 := bstep (se 1 (by rfl) ⟨2131352, by rfl⟩ : syracuseStep 2841803 = 4262705) B4262705
theorem B843113 : Blo 558808 843113 := bstep (se 2 (by rfl) ⟨316167, by rfl⟩ : syracuseStep 843113 = 632335) B632335
theorem B1891727 : Blo 558808 1891727 := bstep (se 1 (by rfl) ⟨1418795, by rfl⟩ : syracuseStep 1891727 = 2837591) B2837591
theorem B843191 : Blo 558808 843191 := bstep (se 1 (by rfl) ⟨632393, by rfl⟩ : syracuseStep 843191 = 1264787) B1264787
theorem B843227 : Blo 558808 843227 := bstep (se 1 (by rfl) ⟨632420, by rfl⟩ : syracuseStep 843227 = 1264841) B1264841
theorem B1892051 : Blo 558808 1892051 := bstep (se 1 (by rfl) ⟨1419038, by rfl⟩ : syracuseStep 1892051 = 2838077) B2838077
theorem B1924823 : Blo 558808 1924823 := bstep (se 1 (by rfl) ⟨1443617, by rfl⟩ : syracuseStep 1924823 = 2887235) B2887235
theorem B4251527 : Blo 558808 4251527 := bstep (se 1 (by rfl) ⟨3188645, by rfl⟩ : syracuseStep 4251527 = 6377291) B6377291
theorem B843695 : Blo 558808 843695 := bstep (se 1 (by rfl) ⟨632771, by rfl⟩ : syracuseStep 843695 = 1265543) B1265543
theorem B7200697 : Blo 558808 7200697 := bstep (se 2 (by rfl) ⟨2700261, by rfl⟩ : syracuseStep 7200697 = 5400523) B5400523
theorem B843785 : Blo 558808 843785 := bstep (se 2 (by rfl) ⟨316419, by rfl⟩ : syracuseStep 843785 = 632839) B632839
theorem B843815 : Blo 558808 843815 := bstep (se 1 (by rfl) ⟨632861, by rfl⟩ : syracuseStep 843815 = 1265723) B1265723
theorem B2121785 : Blo 558808 2121785 := bstep (se 2 (by rfl) ⟨795669, by rfl⟩ : syracuseStep 2121785 = 1591339) B1591339
theorem B4317299 : Blo 558808 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B843899 : Blo 558808 843899 := bstep (se 1 (by rfl) ⟨632924, by rfl⟩ : syracuseStep 843899 = 1265849) B1265849
theorem B844025 : Blo 558808 844025 := bstep (se 2 (by rfl) ⟨316509, by rfl⟩ : syracuseStep 844025 = 633019) B633019
theorem B844127 : Blo 558808 844127 := bstep (se 1 (by rfl) ⟨633095, by rfl⟩ : syracuseStep 844127 = 1266191) B1266191
theorem B844139 : Blo 558808 844139 := bstep (se 1 (by rfl) ⟨633104, by rfl⟩ : syracuseStep 844139 = 1266209) B1266209
theorem B8774245 : Blo 558808 8774245 := bstep (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) B1645171
theorem B1794935 : Blo 558808 1794935 := bstep (se 1 (by rfl) ⟨1346201, by rfl⟩ : syracuseStep 1794935 = 2692403) B2692403
theorem B1893239 : Blo 558808 1893239 := bstep (se 1 (by rfl) ⟨1419929, by rfl⟩ : syracuseStep 1893239 = 2839859) B2839859
theorem B10216367 : Blo 558808 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B1008649 : Blo 558808 1008649 := bstep (se 2 (by rfl) ⟨378243, by rfl⟩ : syracuseStep 1008649 = 756487) B756487
theorem B1893455 : Blo 558808 1893455 := bstep (se 1 (by rfl) ⟨1420091, by rfl⟩ : syracuseStep 1893455 = 2840183) B2840183
theorem B1795243 : Blo 558808 1795243 := bstep (se 1 (by rfl) ⟨1346432, by rfl⟩ : syracuseStep 1795243 = 2692865) B2692865
theorem B3827087 : Blo 558808 3827087 := bstep (se 1 (by rfl) ⟨2870315, by rfl⟩ : syracuseStep 3827087 = 5740631) B5740631
theorem B1009039 : Blo 558808 1009039 := bstep (se 1 (by rfl) ⟨756779, by rfl⟩ : syracuseStep 1009039 = 1513559) B1513559
theorem B943535 : Blo 558808 943535 := bstep (se 1 (by rfl) ⟨707651, by rfl⟩ : syracuseStep 943535 = 1415303) B1415303
theorem B1893833 : Blo 558808 1893833 := bstep (se 2 (by rfl) ⟨710187, by rfl⟩ : syracuseStep 1893833 = 1420375) B1420375
theorem B2123273 : Blo 558808 2123273 := bstep (se 2 (by rfl) ⟨796227, by rfl⟩ : syracuseStep 2123273 = 1592455) B1592455
theorem B1894103 : Blo 558808 1894103 := bstep (se 1 (by rfl) ⟨1420577, by rfl⟩ : syracuseStep 1894103 = 2841155) B2841155
theorem B943967 : Blo 558808 943967 := bstep (se 1 (by rfl) ⟨707975, by rfl⟩ : syracuseStep 943967 = 1415951) B1415951
theorem B1894319 : Blo 558808 1894319 := bstep (se 1 (by rfl) ⟨1420739, by rfl⟩ : syracuseStep 1894319 = 2841479) B2841479
theorem B1796023 : Blo 558808 1796023 := bstep (se 1 (by rfl) ⟨1347017, by rfl⟩ : syracuseStep 1796023 = 2694035) B2694035
theorem B1009673 : Blo 558808 1009673 := bstep (se 2 (by rfl) ⟨378627, by rfl⟩ : syracuseStep 1009673 = 757255) B757255
theorem B3205277 : Blo 558808 3205277 := bstep (se 3 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 3205277 = 1201979) B1201979
theorem B10741997 : Blo 558808 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B7170353 : Blo 558808 7170353 := bstep (se 2 (by rfl) ⟨2688882, by rfl⟩ : syracuseStep 7170353 = 5377765) B5377765
theorem B4614529 : Blo 558808 4614529 := bstep (se 2 (by rfl) ⟨1730448, by rfl⟩ : syracuseStep 4614529 = 3460897) B3460897
theorem B944527 : Blo 558808 944527 := bstep (se 1 (by rfl) ⟨708395, by rfl⟩ : syracuseStep 944527 = 1416791) B1416791
theorem B2124427 : Blo 558808 2124427 := bstep (se 1 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 2124427 = 3186641) B3186641
theorem B2124731 : Blo 558808 2124731 := bstep (se 1 (by rfl) ⟨1593548, by rfl⟩ : syracuseStep 2124731 = 3187097) B3187097
theorem B945209 : Blo 558808 945209 := bstep (se 2 (by rfl) ⟨354453, by rfl⟩ : syracuseStep 945209 = 708907) B708907
theorem B2157911 : Blo 558808 2157911 := bstep (se 1 (by rfl) ⟨1618433, by rfl⟩ : syracuseStep 2157911 = 3236867) B3236867
theorem B44330453 : Blo 558808 44330453 := bstep (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) B1038995
theorem B1601147 : Blo 558808 1601147 := bstep (se 1 (by rfl) ⟨1200860, by rfl⟩ : syracuseStep 1601147 = 2401721) B2401721
theorem B1797817 : Blo 558808 1797817 := bstep (se 2 (by rfl) ⟨674181, by rfl⟩ : syracuseStep 1797817 = 1348363) B1348363
theorem B2191033 : Blo 558808 2191033 := bstep (se 2 (by rfl) ⟨821637, by rfl⟩ : syracuseStep 2191033 = 1643275) B1643275
theorem B945911 : Blo 558808 945911 := bstep (se 1 (by rfl) ⟨709433, by rfl⟩ : syracuseStep 945911 = 1418867) B1418867
theorem B16215875 : Blo 558808 16215875 := bstep (se 1 (by rfl) ⟨12161906, by rfl⟩ : syracuseStep 16215875 = 24323813) B24323813
theorem B3600247 : Blo 558808 3600247 := bstep (se 1 (by rfl) ⟨2700185, by rfl⟩ : syracuseStep 3600247 = 5400371) B5400371
theorem B946255 : Blo 558808 946255 := bstep (se 1 (by rfl) ⟨709691, by rfl⟩ : syracuseStep 946255 = 1419383) B1419383
theorem B4255901 : Blo 558808 4255901 := bstep (se 3 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 4255901 = 1595963) B1595963
theorem B1896695 : Blo 558808 1896695 := bstep (se 1 (by rfl) ⟨1422521, by rfl⟩ : syracuseStep 1896695 = 2845043) B2845043
theorem B2846987 : Blo 558808 2846987 := bstep (se 1 (by rfl) ⟨2135240, by rfl⟩ : syracuseStep 2846987 = 4270481) B4270481
theorem B946505 : Blo 558808 946505 := bstep (se 2 (by rfl) ⟨354939, by rfl⟩ : syracuseStep 946505 = 709879) B709879
theorem B1897019 : Blo 558808 1897019 := bstep (se 1 (by rfl) ⟨1422764, by rfl⟩ : syracuseStep 1897019 = 2845529) B2845529
theorem B946937 : Blo 558808 946937 := bstep (se 2 (by rfl) ⟨355101, by rfl⟩ : syracuseStep 946937 = 710203) B710203
theorem B1897289 : Blo 558808 1897289 := bstep (se 2 (by rfl) ⟨711483, by rfl⟩ : syracuseStep 1897289 = 1422967) B1422967
theorem B947119 : Blo 558808 947119 := bstep (se 1 (by rfl) ⟨710339, by rfl⟩ : syracuseStep 947119 = 1420679) B1420679
theorem B1602479 : Blo 558808 1602479 := bstep (se 1 (by rfl) ⟨1201859, by rfl⟩ : syracuseStep 1602479 = 2403719) B2403719
theorem B947207 : Blo 558808 947207 := bstep (se 1 (by rfl) ⟨710405, by rfl⟩ : syracuseStep 947207 = 1420811) B1420811
theorem B3601579 : Blo 558808 3601579 := bstep (se 1 (by rfl) ⟨2701184, by rfl⟩ : syracuseStep 3601579 = 5402369) B5402369
theorem B947551 : Blo 558808 947551 := bstep (se 1 (by rfl) ⟨710663, by rfl⟩ : syracuseStep 947551 = 1421327) B1421327
theorem B947639 : Blo 558808 947639 := bstep (se 1 (by rfl) ⟨710729, by rfl⟩ : syracuseStep 947639 = 1421459) B1421459
theorem B2848445 : Blo 558808 2848445 := bstep (se 3 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 2848445 = 1068167) B1068167
theorem B2848607 : Blo 558808 2848607 := bstep (se 1 (by rfl) ⟨2136455, by rfl⟩ : syracuseStep 2848607 = 4272911) B4272911
theorem B1013609 : Blo 558808 1013609 := bstep (se 2 (by rfl) ⟨380103, by rfl⟩ : syracuseStep 1013609 = 760207) B760207
theorem B1898423 : Blo 558808 1898423 := bstep (se 1 (by rfl) ⟨1423817, by rfl⟩ : syracuseStep 1898423 = 2847635) B2847635
theorem B948233 : Blo 558808 948233 := bstep (se 2 (by rfl) ⟨355587, by rfl⟩ : syracuseStep 948233 = 711175) B711175
theorem B9730205 : Blo 558808 9730205 := bstep (se 3 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 9730205 = 3648827) B3648827
theorem B948395 : Blo 558808 948395 := bstep (se 1 (by rfl) ⟨711296, by rfl⟩ : syracuseStep 948395 = 1422593) B1422593
theorem B719047 : Blo 558808 719047 := bstep (se 1 (by rfl) ⟨539285, by rfl⟩ : syracuseStep 719047 = 1078571) B1078571
theorem B1899017 : Blo 558808 1899017 := bstep (se 2 (by rfl) ⟨712131, by rfl⟩ : syracuseStep 1899017 = 1424263) B1424263
theorem B3832343 : Blo 558808 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B948793 : Blo 558808 948793 := bstep (se 2 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 948793 = 711595) B711595
theorem B1800893 : Blo 558808 1800893 := bstep (se 3 (by rfl) ⟨337667, by rfl⟩ : syracuseStep 1800893 = 675335) B675335
theorem B948935 : Blo 558808 948935 := bstep (se 1 (by rfl) ⟨711701, by rfl⟩ : syracuseStep 948935 = 1423403) B1423403
theorem B949097 : Blo 558808 949097 := bstep (se 2 (by rfl) ⟨355911, by rfl⟩ : syracuseStep 949097 = 711823) B711823
theorem B2128801 : Blo 558808 2128801 := bstep (se 2 (by rfl) ⟨798300, by rfl⟩ : syracuseStep 2128801 = 1596601) B1596601
theorem B1276847 : Blo 558808 1276847 := bstep (se 1 (by rfl) ⟨957635, by rfl⟩ : syracuseStep 1276847 = 1915271) B1915271
theorem B4258817 : Blo 558808 4258817 := bstep (se 2 (by rfl) ⟨1597056, by rfl⟩ : syracuseStep 4258817 = 3194113) B3194113
theorem B2391059 : Blo 558808 2391059 := bstep (se 1 (by rfl) ⟨1793294, by rfl⟩ : syracuseStep 2391059 = 3586589) B3586589
theorem B6814799 : Blo 558808 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B2391211 : Blo 558808 2391211 := bstep (se 1 (by rfl) ⟨1793408, by rfl⟩ : syracuseStep 2391211 = 3586817) B3586817
theorem B949495 : Blo 558808 949495 := bstep (se 1 (by rfl) ⟨712121, by rfl⟩ : syracuseStep 949495 = 1424243) B1424243
theorem B949691 : Blo 558808 949691 := bstep (se 1 (by rfl) ⟨712268, by rfl⟩ : syracuseStep 949691 = 1424537) B1424537
theorem B3407305 : Blo 558808 3407305 := bstep (se 2 (by rfl) ⟨1277739, by rfl⟩ : syracuseStep 3407305 = 2555479) B2555479
theorem B1081079 : Blo 558808 1081079 := bstep (se 1 (by rfl) ⟨810809, by rfl⟩ : syracuseStep 1081079 = 1621619) B1621619
theorem B851705 : Blo 558808 851705 := bstep (se 2 (by rfl) ⟨319389, by rfl⟩ : syracuseStep 851705 = 638779) B638779
theorem B2129759 : Blo 558808 2129759 := bstep (se 1 (by rfl) ⟨1597319, by rfl⟩ : syracuseStep 2129759 = 3194639) B3194639
theorem B2129773 : Blo 558808 2129773 := bstep (se 3 (by rfl) ⟨399332, by rfl⟩ : syracuseStep 2129773 = 798665) B798665
theorem B5111687 : Blo 558808 5111687 := bstep (se 1 (by rfl) ⟨3833765, by rfl⟩ : syracuseStep 5111687 = 7667531) B7667531
theorem B1212335 : Blo 558808 1212335 := bstep (se 1 (by rfl) ⟨909251, by rfl⟩ : syracuseStep 1212335 = 1818503) B1818503
theorem B1704041 : Blo 558808 1704041 := bstep (se 2 (by rfl) ⟨639015, by rfl⟩ : syracuseStep 1704041 = 1278031) B1278031
theorem B4784609 : Blo 558808 4784609 := bstep (se 2 (by rfl) ⟨1794228, by rfl⟩ : syracuseStep 4784609 = 3588457) B3588457
theorem B1278433 : Blo 558808 1278433 := bstep (se 2 (by rfl) ⟨479412, by rfl⟩ : syracuseStep 1278433 = 958825) B958825
theorem B2687539 : Blo 558808 2687539 := bstep (se 1 (by rfl) ⟨2015654, by rfl⟩ : syracuseStep 2687539 = 4031309) B4031309
theorem B11698993 : Blo 558808 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B5833619 : Blo 558808 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B1344865 : Blo 558808 1344865 := bstep (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) B1008649
theorem B2393657 : Blo 558808 2393657 := bstep (se 2 (by rfl) ⟨897621, by rfl⟩ : syracuseStep 2393657 = 1795243) B1795243
theorem B20514455 : Blo 558808 20514455 := bstep (se 1 (by rfl) ⟨15385841, by rfl⟩ : syracuseStep 20514455 = 30771683) B30771683
theorem B558815 : Blo 558808 558815 := bstep (se 1 (by rfl) ⟨419111, by rfl⟩ : syracuseStep 558815 = 838223) B838223
theorem B558895 : Blo 558808 558895 := bstep (se 1 (by rfl) ⟨419171, by rfl⟩ : syracuseStep 558895 = 838343) B838343
theorem B1345385 : Blo 558808 1345385 := bstep (se 2 (by rfl) ⟨504519, by rfl⟩ : syracuseStep 1345385 = 1009039) B1009039
theorem B559003 : Blo 558808 559003 := bstep (se 1 (by rfl) ⟨419252, by rfl⟩ : syracuseStep 559003 = 838505) B838505
theorem B559055 : Blo 558808 559055 := bstep (se 1 (by rfl) ⟨419291, by rfl⟩ : syracuseStep 559055 = 838583) B838583
theorem B4032463 : Blo 558808 4032463 := bstep (se 1 (by rfl) ⟨3024347, by rfl⟩ : syracuseStep 4032463 = 6048695) B6048695
theorem B853967 : Blo 558808 853967 := bstep (se 1 (by rfl) ⟨640475, by rfl⟩ : syracuseStep 853967 = 1280951) B1280951
theorem B559079 : Blo 558808 559079 := bstep (se 1 (by rfl) ⟨419309, by rfl⟩ : syracuseStep 559079 = 838619) B838619
theorem B559391 : Blo 558808 559391 := bstep (se 1 (by rfl) ⟨419543, by rfl⟩ : syracuseStep 559391 = 839087) B839087
theorem B559451 : Blo 558808 559451 := bstep (se 1 (by rfl) ⟨419588, by rfl⟩ : syracuseStep 559451 = 839177) B839177
theorem B559471 : Blo 558808 559471 := bstep (se 1 (by rfl) ⟨419603, by rfl⟩ : syracuseStep 559471 = 839207) B839207
theorem B559527 : Blo 558808 559527 := bstep (se 1 (by rfl) ⟨419645, by rfl⟩ : syracuseStep 559527 = 839291) B839291
theorem B559611 : Blo 558808 559611 := bstep (se 1 (by rfl) ⟨419708, by rfl⟩ : syracuseStep 559611 = 839417) B839417
theorem B559679 : Blo 558808 559679 := bstep (se 1 (by rfl) ⟨419759, by rfl⟩ : syracuseStep 559679 = 839519) B839519
theorem B559687 : Blo 558808 559687 := bstep (se 1 (by rfl) ⟨419765, by rfl⟩ : syracuseStep 559687 = 839531) B839531
theorem B2394697 : Blo 558808 2394697 := bstep (se 2 (by rfl) ⟨898011, by rfl⟩ : syracuseStep 2394697 = 1796023) B1796023
theorem B2132675 : Blo 558808 2132675 := bstep (se 1 (by rfl) ⟨1599506, by rfl⟩ : syracuseStep 2132675 = 3199013) B3199013
theorem B559839 : Blo 558808 559839 := bstep (se 1 (by rfl) ⟨419879, by rfl⟩ : syracuseStep 559839 = 839759) B839759
theorem B559919 : Blo 558808 559919 := bstep (se 1 (by rfl) ⟨419939, by rfl⟩ : syracuseStep 559919 = 839879) B839879
theorem B560027 : Blo 558808 560027 := bstep (se 1 (by rfl) ⟨420020, by rfl⟩ : syracuseStep 560027 = 840041) B840041
theorem B560079 : Blo 558808 560079 := bstep (se 1 (by rfl) ⟨420059, by rfl⟩ : syracuseStep 560079 = 840119) B840119
theorem B1280987 : Blo 558808 1280987 := bstep (se 1 (by rfl) ⟨960740, by rfl⟩ : syracuseStep 1280987 = 1921481) B1921481
theorem B17239013 : Blo 558808 17239013 := bstep (se 4 (by rfl) ⟨1616157, by rfl⟩ : syracuseStep 17239013 = 3232315) B3232315
theorem B560103 : Blo 558808 560103 := bstep (se 1 (by rfl) ⟨420077, by rfl⟩ : syracuseStep 560103 = 840155) B840155
theorem B16124993 : Blo 558808 16124993 := bstep (se 2 (by rfl) ⟨6046872, by rfl⟩ : syracuseStep 16124993 = 12093745) B12093745
theorem B560415 : Blo 558808 560415 := bstep (se 1 (by rfl) ⟨420311, by rfl⟩ : syracuseStep 560415 = 840623) B840623
theorem B560475 : Blo 558808 560475 := bstep (se 1 (by rfl) ⟨420356, by rfl⟩ : syracuseStep 560475 = 840713) B840713
theorem B560495 : Blo 558808 560495 := bstep (se 1 (by rfl) ⟨420371, by rfl⟩ : syracuseStep 560495 = 840743) B840743
theorem B4787585 : Blo 558808 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B560551 : Blo 558808 560551 := bstep (se 1 (by rfl) ⟨420413, by rfl⟩ : syracuseStep 560551 = 840827) B840827
theorem B560635 : Blo 558808 560635 := bstep (se 1 (by rfl) ⟨420476, by rfl⟩ : syracuseStep 560635 = 840953) B840953
theorem B7179785 : Blo 558808 7179785 := bstep (se 2 (by rfl) ⟨2692419, by rfl⟩ : syracuseStep 7179785 = 5384839) B5384839
theorem B560703 : Blo 558808 560703 := bstep (se 1 (by rfl) ⟨420527, by rfl⟩ : syracuseStep 560703 = 841055) B841055
theorem B560711 : Blo 558808 560711 := bstep (se 1 (by rfl) ⟨420533, by rfl⟩ : syracuseStep 560711 = 841067) B841067
theorem B2395757 : Blo 558808 2395757 := bstep (se 3 (by rfl) ⟨449204, by rfl⟩ : syracuseStep 2395757 = 898409) B898409
theorem B560863 : Blo 558808 560863 := bstep (se 1 (by rfl) ⟨420647, by rfl⟩ : syracuseStep 560863 = 841295) B841295
theorem B560943 : Blo 558808 560943 := bstep (se 1 (by rfl) ⟨420707, by rfl⟩ : syracuseStep 560943 = 841415) B841415
theorem B561051 : Blo 558808 561051 := bstep (se 1 (by rfl) ⟨420788, by rfl⟩ : syracuseStep 561051 = 841577) B841577
theorem B561103 : Blo 558808 561103 := bstep (se 1 (by rfl) ⟨420827, by rfl⟩ : syracuseStep 561103 = 841655) B841655
theorem B561127 : Blo 558808 561127 := bstep (se 1 (by rfl) ⟨420845, by rfl⟩ : syracuseStep 561127 = 841691) B841691
theorem B561439 : Blo 558808 561439 := bstep (se 1 (by rfl) ⟨421079, by rfl⟩ : syracuseStep 561439 = 842159) B842159
theorem B5738825 : Blo 558808 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B561499 : Blo 558808 561499 := bstep (se 1 (by rfl) ⟨421124, by rfl⟩ : syracuseStep 561499 = 842249) B842249
theorem B561519 : Blo 558808 561519 := bstep (se 1 (by rfl) ⟨421139, by rfl⟩ : syracuseStep 561519 = 842279) B842279
theorem B561575 : Blo 558808 561575 := bstep (se 1 (by rfl) ⟨421181, by rfl⟩ : syracuseStep 561575 = 842363) B842363
theorem B561659 : Blo 558808 561659 := bstep (se 1 (by rfl) ⟨421244, by rfl⟩ : syracuseStep 561659 = 842489) B842489
theorem B561727 : Blo 558808 561727 := bstep (se 1 (by rfl) ⟨421295, by rfl⟩ : syracuseStep 561727 = 842591) B842591
theorem B561735 : Blo 558808 561735 := bstep (se 1 (by rfl) ⟨421301, by rfl⟩ : syracuseStep 561735 = 842603) B842603
theorem B2691787 : Blo 558808 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B561887 : Blo 558808 561887 := bstep (se 1 (by rfl) ⟨421415, by rfl⟩ : syracuseStep 561887 = 842831) B842831
theorem B561967 : Blo 558808 561967 := bstep (se 1 (by rfl) ⟨421475, by rfl⟩ : syracuseStep 561967 = 842951) B842951
theorem B562075 : Blo 558808 562075 := bstep (se 1 (by rfl) ⟨421556, by rfl⟩ : syracuseStep 562075 = 843113) B843113
theorem B2397089 : Blo 558808 2397089 := bstep (se 2 (by rfl) ⟨898908, by rfl⟩ : syracuseStep 2397089 = 1797817) B1797817
theorem B562127 : Blo 558808 562127 := bstep (se 1 (by rfl) ⟨421595, by rfl⟩ : syracuseStep 562127 = 843191) B843191
theorem B562151 : Blo 558808 562151 := bstep (se 1 (by rfl) ⟨421613, by rfl⟩ : syracuseStep 562151 = 843227) B843227
theorem B1283215 : Blo 558808 1283215 := bstep (se 1 (by rfl) ⟨962411, by rfl⟩ : syracuseStep 1283215 = 1924823) B1924823
theorem B562463 : Blo 558808 562463 := bstep (se 1 (by rfl) ⟨421847, by rfl⟩ : syracuseStep 562463 = 843695) B843695
theorem B562523 : Blo 558808 562523 := bstep (se 1 (by rfl) ⟨421892, by rfl⟩ : syracuseStep 562523 = 843785) B843785
theorem B562543 : Blo 558808 562543 := bstep (se 1 (by rfl) ⟨421907, by rfl⟩ : syracuseStep 562543 = 843815) B843815
theorem B1414523 : Blo 558808 1414523 := bstep (se 1 (by rfl) ⟨1060892, by rfl⟩ : syracuseStep 1414523 = 2121785) B2121785
theorem B562599 : Blo 558808 562599 := bstep (se 1 (by rfl) ⟨421949, by rfl⟩ : syracuseStep 562599 = 843899) B843899
theorem B11474369 : Blo 558808 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B562683 : Blo 558808 562683 := bstep (se 1 (by rfl) ⟨422012, by rfl⟩ : syracuseStep 562683 = 844025) B844025
theorem B562751 : Blo 558808 562751 := bstep (se 1 (by rfl) ⟨422063, by rfl⟩ : syracuseStep 562751 = 844127) B844127
theorem B562759 : Blo 558808 562759 := bstep (se 1 (by rfl) ⟨422069, by rfl⟩ : syracuseStep 562759 = 844139) B844139
theorem B1414817 : Blo 558808 1414817 := bstep (se 2 (by rfl) ⟨530556, by rfl⟩ : syracuseStep 1414817 = 1061113) B1061113
theorem B6166201 : Blo 558808 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B629023 : Blo 558808 629023 := bstep (se 1 (by rfl) ⟨471767, by rfl⟩ : syracuseStep 629023 = 943535) B943535
theorem B1415515 : Blo 558808 1415515 := bstep (se 1 (by rfl) ⟨1061636, by rfl⟩ : syracuseStep 1415515 = 2123273) B2123273
theorem B629311 : Blo 558808 629311 := bstep (se 1 (by rfl) ⟨471983, by rfl⟩ : syracuseStep 629311 = 943967) B943967
theorem B5773963 : Blo 558808 5773963 := bstep (se 1 (by rfl) ⟨4330472, by rfl⟩ : syracuseStep 5773963 = 8660945) B8660945
theorem B2136851 : Blo 558808 2136851 := bstep (se 1 (by rfl) ⟨1602638, by rfl⟩ : syracuseStep 2136851 = 3205277) B3205277
theorem B4922491 : Blo 558808 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B1416487 : Blo 558808 1416487 := bstep (se 1 (by rfl) ⟨1062365, by rfl⟩ : syracuseStep 1416487 = 2124731) B2124731
theorem B630139 : Blo 558808 630139 := bstep (se 1 (by rfl) ⟨472604, by rfl⟩ : syracuseStep 630139 = 945209) B945209
theorem B1416761 : Blo 558808 1416761 := bstep (se 2 (by rfl) ⟨531285, by rfl⟩ : syracuseStep 1416761 = 1062571) B1062571
theorem B1515311 : Blo 558808 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B630607 : Blo 558808 630607 := bstep (se 1 (by rfl) ⟨472955, by rfl⟩ : syracuseStep 630607 = 945911) B945911
theorem B597991 : Blo 558808 597991 := bstep (se 1 (by rfl) ⟨448493, by rfl⟩ : syracuseStep 597991 = 896987) B896987
theorem B4268051 : Blo 558808 4268051 := bstep (se 1 (by rfl) ⟨3201038, by rfl⟩ : syracuseStep 4268051 = 6402077) B6402077
theorem B631003 : Blo 558808 631003 := bstep (se 1 (by rfl) ⟨473252, by rfl⟩ : syracuseStep 631003 = 946505) B946505
theorem B958729 : Blo 558808 958729 := bstep (se 2 (by rfl) ⟨359523, by rfl⟩ : syracuseStep 958729 = 719047) B719047
theorem B1516001 : Blo 558808 1516001 := bstep (se 2 (by rfl) ⟨568500, by rfl⟩ : syracuseStep 1516001 = 1137001) B1137001
theorem B631291 : Blo 558808 631291 := bstep (se 1 (by rfl) ⟨473468, by rfl⟩ : syracuseStep 631291 = 946937) B946937
theorem B631471 : Blo 558808 631471 := bstep (se 1 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 631471 = 947207) B947207
theorem B631759 : Blo 558808 631759 := bstep (se 1 (by rfl) ⟨473819, by rfl⟩ : syracuseStep 631759 = 947639) B947639
theorem B795943 : Blo 558808 795943 := bstep (se 1 (by rfl) ⟨596957, by rfl⟩ : syracuseStep 795943 = 1193915) B1193915
theorem B632155 : Blo 558808 632155 := bstep (se 1 (by rfl) ⟨474116, by rfl⟩ : syracuseStep 632155 = 948233) B948233
theorem B1418593 : Blo 558808 1418593 := bstep (se 2 (by rfl) ⟨531972, by rfl⟩ : syracuseStep 1418593 = 1063945) B1063945
theorem B632263 : Blo 558808 632263 := bstep (se 1 (by rfl) ⟨474197, by rfl⟩ : syracuseStep 632263 = 948395) B948395
theorem B3188281 : Blo 558808 3188281 := bstep (se 2 (by rfl) ⟨1195605, by rfl⟩ : syracuseStep 3188281 = 2391211) B2391211
theorem B632623 : Blo 558808 632623 := bstep (se 1 (by rfl) ⟨474467, by rfl⟩ : syracuseStep 632623 = 948935) B948935
theorem B632731 : Blo 558808 632731 := bstep (se 1 (by rfl) ⟨474548, by rfl⟩ : syracuseStep 632731 = 949097) B949097
theorem B1419545 : Blo 558808 1419545 := bstep (se 2 (by rfl) ⟨532329, by rfl⟩ : syracuseStep 1419545 = 1064659) B1064659
theorem B633127 : Blo 558808 633127 := bstep (se 1 (by rfl) ⟨474845, by rfl⟩ : syracuseStep 633127 = 949691) B949691
theorem B567803 : Blo 558808 567803 := bstep (se 1 (by rfl) ⟨425852, by rfl⟩ : syracuseStep 567803 = 851705) B851705
theorem B600571 : Blo 558808 600571 := bstep (se 1 (by rfl) ⟨450428, by rfl⟩ : syracuseStep 600571 = 900857) B900857
theorem B1419839 : Blo 558808 1419839 := bstep (se 1 (by rfl) ⟨1064879, by rfl⟩ : syracuseStep 1419839 = 2129759) B2129759
theorem B1420051 : Blo 558808 1420051 := bstep (se 1 (by rfl) ⟨1065038, by rfl⟩ : syracuseStep 1420051 = 2130077) B2130077
theorem B4795271 : Blo 558808 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B1420487 : Blo 558808 1420487 := bstep (se 1 (by rfl) ⟨1065365, by rfl⟩ : syracuseStep 1420487 = 2130731) B2130731
theorem B1420537 : Blo 558808 1420537 := bstep (se 2 (by rfl) ⟨532701, by rfl⟩ : syracuseStep 1420537 = 1065403) B1065403
theorem B6368543 : Blo 558808 6368543 := bstep (se 1 (by rfl) ⟨4776407, by rfl⟩ : syracuseStep 6368543 = 9552815) B9552815
theorem B1421185 : Blo 558808 1421185 := bstep (se 2 (by rfl) ⟨532944, by rfl⟩ : syracuseStep 1421185 = 1065889) B1065889
theorem B1257839 : Blo 558808 1257839 := bstep (se 1 (by rfl) ⟨943379, by rfl⟩ : syracuseStep 1257839 = 1886759) B1886759
theorem B799087 : Blo 558808 799087 := bstep (se 1 (by rfl) ⟨599315, by rfl⟩ : syracuseStep 799087 = 1198631) B1198631
theorem B7188911 : Blo 558808 7188911 := bstep (se 1 (by rfl) ⟨5391683, by rfl⟩ : syracuseStep 7188911 = 10783367) B10783367
theorem B1257911 : Blo 558808 1257911 := bstep (se 1 (by rfl) ⟨943433, by rfl⟩ : syracuseStep 1257911 = 1886867) B1886867
theorem B1258055 : Blo 558808 1258055 := bstep (se 1 (by rfl) ⟨943541, by rfl⟩ : syracuseStep 1258055 = 1887083) B1887083
theorem B799303 : Blo 558808 799303 := bstep (se 1 (by rfl) ⟨599477, by rfl⟩ : syracuseStep 799303 = 1198955) B1198955
theorem B1258091 : Blo 558808 1258091 := bstep (se 1 (by rfl) ⟨943568, by rfl⟩ : syracuseStep 1258091 = 1887137) B1887137
theorem B1421945 : Blo 558808 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B1421995 : Blo 558808 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B1061599 : Blo 558808 1061599 := bstep (se 1 (by rfl) ⟨796199, by rfl⟩ : syracuseStep 1061599 = 1592399) B1592399
theorem B1422299 : Blo 558808 1422299 := bstep (se 1 (by rfl) ⟨1066724, by rfl⟩ : syracuseStep 1422299 = 2133449) B2133449
theorem B1258487 : Blo 558808 1258487 := bstep (se 1 (by rfl) ⟨943865, by rfl⟩ : syracuseStep 1258487 = 1887731) B1887731
theorem B1422623 : Blo 558808 1422623 := bstep (se 1 (by rfl) ⟨1066967, by rfl⟩ : syracuseStep 1422623 = 2133935) B2133935
theorem B1258847 : Blo 558808 1258847 := bstep (se 1 (by rfl) ⟨944135, by rfl⟩ : syracuseStep 1258847 = 1888271) B1888271
theorem B800123 : Blo 558808 800123 := bstep (se 1 (by rfl) ⟨600092, by rfl⟩ : syracuseStep 800123 = 1200185) B1200185
theorem B1259243 : Blo 558808 1259243 := bstep (se 1 (by rfl) ⟨944432, by rfl⟩ : syracuseStep 1259243 = 1888865) B1888865
theorem B1259369 : Blo 558808 1259369 := bstep (se 2 (by rfl) ⟨472263, by rfl⟩ : syracuseStep 1259369 = 944527) B944527
theorem B2832569 : Blo 558808 2832569 := bstep (se 2 (by rfl) ⟨1062213, by rfl⟩ : syracuseStep 2832569 = 2124427) B2124427
theorem B1423727 : Blo 558808 1423727 := bstep (se 1 (by rfl) ⟨1067795, by rfl⟩ : syracuseStep 1423727 = 2135591) B2135591
theorem B3029491 : Blo 558808 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B1260215 : Blo 558808 1260215 := bstep (se 1 (by rfl) ⟨945161, by rfl⟩ : syracuseStep 1260215 = 1890323) B1890323
theorem B3029885 : Blo 558808 3029885 := bstep (se 3 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 3029885 = 1136207) B1136207
theorem B1260431 : Blo 558808 1260431 := bstep (se 1 (by rfl) ⟨945323, by rfl⟩ : syracuseStep 1260431 = 1890647) B1890647
theorem B900011 : Blo 558808 900011 := bstep (se 1 (by rfl) ⟨675008, by rfl⟩ : syracuseStep 900011 = 1350017) B1350017
theorem B1194983 : Blo 558808 1194983 := bstep (se 1 (by rfl) ⟨896237, by rfl⟩ : syracuseStep 1194983 = 1792475) B1792475
theorem B1424375 : Blo 558808 1424375 := bstep (se 1 (by rfl) ⟨1068281, by rfl⟩ : syracuseStep 1424375 = 2136563) B2136563
theorem B1621181 : Blo 558808 1621181 := bstep (se 3 (by rfl) ⟨303971, by rfl⟩ : syracuseStep 1621181 = 607943) B607943
theorem B472858165 : Blo 558808 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B1261151 : Blo 558808 1261151 := bstep (se 1 (by rfl) ⟨945863, by rfl⟩ : syracuseStep 1261151 = 1891727) B1891727
theorem B1261367 : Blo 558808 1261367 := bstep (se 1 (by rfl) ⟨946025, by rfl⟩ : syracuseStep 1261367 = 1892051) B1892051
theorem B4800329 : Blo 558808 4800329 := bstep (se 2 (by rfl) ⟨1800123, by rfl⟩ : syracuseStep 4800329 = 3600247) B3600247
theorem B2834351 : Blo 558808 2834351 := bstep (se 1 (by rfl) ⟨2125763, by rfl⟩ : syracuseStep 2834351 = 4251527) B4251527
theorem B10371149 : Blo 558808 10371149 := bstep (se 3 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 10371149 = 3889181) B3889181
theorem B1261673 : Blo 558808 1261673 := bstep (se 2 (by rfl) ⟨473127, by rfl⟩ : syracuseStep 1261673 = 946255) B946255
theorem B6406451 : Blo 558808 6406451 := bstep (se 1 (by rfl) ⟨4804838, by rfl⟩ : syracuseStep 6406451 = 9609677) B9609677
theorem B6144457 : Blo 558808 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B1196623 : Blo 558808 1196623 := bstep (se 1 (by rfl) ⟨897467, by rfl⟩ : syracuseStep 1196623 = 1794935) B1794935
theorem B1262159 : Blo 558808 1262159 := bstep (se 1 (by rfl) ⟨946619, by rfl⟩ : syracuseStep 1262159 = 1893239) B1893239
theorem B1262303 : Blo 558808 1262303 := bstep (se 1 (by rfl) ⟨946727, by rfl⟩ : syracuseStep 1262303 = 1893455) B1893455
theorem B1262555 : Blo 558808 1262555 := bstep (se 1 (by rfl) ⟨946916, by rfl⟩ : syracuseStep 1262555 = 1893833) B1893833
theorem B16172045 : Blo 558808 16172045 := bstep (se 3 (by rfl) ⟨3032258, by rfl⟩ : syracuseStep 16172045 = 6064517) B6064517
theorem B1262735 : Blo 558808 1262735 := bstep (se 1 (by rfl) ⟨947051, by rfl⟩ : syracuseStep 1262735 = 1894103) B1894103
theorem B1262825 : Blo 558808 1262825 := bstep (se 2 (by rfl) ⟨473559, by rfl⟩ : syracuseStep 1262825 = 947119) B947119
theorem B4244723 : Blo 558808 4244723 := bstep (se 1 (by rfl) ⟨3183542, by rfl⟩ : syracuseStep 4244723 = 6367085) B6367085
theorem B1262879 : Blo 558808 1262879 := bstep (se 1 (by rfl) ⟨947159, by rfl⟩ : syracuseStep 1262879 = 1894319) B1894319
theorem B673115 : Blo 558808 673115 := bstep (se 1 (by rfl) ⟨504836, by rfl⟩ : syracuseStep 673115 = 1009673) B1009673
theorem B7161331 : Blo 558808 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B4802105 : Blo 558808 4802105 := bstep (se 2 (by rfl) ⟨1800789, by rfl⟩ : syracuseStep 4802105 = 3601579) B3601579
theorem B3032761 : Blo 558808 3032761 := bstep (se 2 (by rfl) ⟨1137285, by rfl⟩ : syracuseStep 3032761 = 2274571) B2274571
theorem B1263401 : Blo 558808 1263401 := bstep (se 2 (by rfl) ⟨473775, by rfl⟩ : syracuseStep 1263401 = 947551) B947551
theorem B1886057 : Blo 558808 1886057 := bstep (se 2 (by rfl) ⟨707271, by rfl⟩ : syracuseStep 1886057 = 1414543) B1414543
theorem B1886489 : Blo 558808 1886489 := bstep (se 2 (by rfl) ⟨707433, by rfl⟩ : syracuseStep 1886489 = 1414867) B1414867
theorem B1067431 : Blo 558808 1067431 := bstep (se 1 (by rfl) ⟨800573, by rfl⟩ : syracuseStep 1067431 = 1601147) B1601147
theorem B21908069 : Blo 558808 21908069 := bstep (se 4 (by rfl) ⟨2053881, by rfl⟩ : syracuseStep 21908069 = 4107763) B4107763
theorem B838265 : Blo 558808 838265 := bstep (se 2 (by rfl) ⟨314349, by rfl⟩ : syracuseStep 838265 = 628699) B628699
theorem B3066491 : Blo 558808 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B838319 : Blo 558808 838319 := bstep (se 1 (by rfl) ⟨628739, by rfl⟩ : syracuseStep 838319 = 1257479) B1257479
theorem B838367 : Blo 558808 838367 := bstep (se 1 (by rfl) ⟨628775, by rfl⟩ : syracuseStep 838367 = 1257551) B1257551
theorem B2837267 : Blo 558808 2837267 := bstep (se 1 (by rfl) ⟨2127950, by rfl⟩ : syracuseStep 2837267 = 4255901) B4255901
theorem B707383 : Blo 558808 707383 := bstep (se 1 (by rfl) ⟨530537, by rfl⟩ : syracuseStep 707383 = 1061075) B1061075
theorem B1264463 : Blo 558808 1264463 := bstep (se 1 (by rfl) ⟨948347, by rfl⟩ : syracuseStep 1264463 = 1896695) B1896695
theorem B2018191 : Blo 558808 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B838631 : Blo 558808 838631 := bstep (se 1 (by rfl) ⟨628973, by rfl⟩ : syracuseStep 838631 = 1257947) B1257947
theorem B1264679 : Blo 558808 1264679 := bstep (se 1 (by rfl) ⟨948509, by rfl⟩ : syracuseStep 1264679 = 1897019) B1897019
theorem B4246667 : Blo 558808 4246667 := bstep (se 1 (by rfl) ⟨3185000, by rfl⟩ : syracuseStep 4246667 = 6370001) B6370001
theorem B1264859 : Blo 558808 1264859 := bstep (se 1 (by rfl) ⟨948644, by rfl⟩ : syracuseStep 1264859 = 1897289) B1897289
theorem B838889 : Blo 558808 838889 := bstep (se 2 (by rfl) ⟨314583, by rfl⟩ : syracuseStep 838889 = 629167) B629167
theorem B838943 : Blo 558808 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B1068319 : Blo 558808 1068319 := bstep (se 1 (by rfl) ⟨801239, by rfl⟩ : syracuseStep 1068319 = 1602479) B1602479
theorem B707879 : Blo 558808 707879 := bstep (se 1 (by rfl) ⟨530909, by rfl⟩ : syracuseStep 707879 = 1061819) B1061819
theorem B3198305 : Blo 558808 3198305 := bstep (se 2 (by rfl) ⟨1199364, by rfl⟩ : syracuseStep 3198305 = 2398729) B2398729
theorem B6081911 : Blo 558808 6081911 := bstep (se 1 (by rfl) ⟨4561433, by rfl⟩ : syracuseStep 6081911 = 9122867) B9122867
theorem B1265057 : Blo 558808 1265057 := bstep (se 2 (by rfl) ⟨474396, by rfl⟩ : syracuseStep 1265057 = 948793) B948793
theorem B25873843 : Blo 558808 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B839111 : Blo 558808 839111 := bstep (se 1 (by rfl) ⟨629333, by rfl⟩ : syracuseStep 839111 = 1258667) B1258667
theorem B4869641 : Blo 558808 4869641 := bstep (se 2 (by rfl) ⟨1826115, by rfl⟩ : syracuseStep 4869641 = 3652231) B3652231
theorem B1887839 : Blo 558808 1887839 := bstep (se 1 (by rfl) ⟨1415879, by rfl⟩ : syracuseStep 1887839 = 2831759) B2831759
theorem B708203 : Blo 558808 708203 := bstep (se 1 (by rfl) ⟨531152, by rfl⟩ : syracuseStep 708203 = 1062305) B1062305
theorem B11685509 : Blo 558808 11685509 := bstep (se 4 (by rfl) ⟨1095516, by rfl⟩ : syracuseStep 11685509 = 2191033) B2191033
theorem B839465 : Blo 558808 839465 := bstep (se 2 (by rfl) ⟨314799, by rfl⟩ : syracuseStep 839465 = 629599) B629599
theorem B839471 : Blo 558808 839471 := bstep (se 1 (by rfl) ⟨629603, by rfl⟩ : syracuseStep 839471 = 1259207) B1259207
theorem B1199929 : Blo 558808 1199929 := bstep (se 2 (by rfl) ⟨449973, by rfl⟩ : syracuseStep 1199929 = 899947) B899947
theorem B2838401 : Blo 558808 2838401 := bstep (se 2 (by rfl) ⟨1064400, by rfl⟩ : syracuseStep 2838401 = 2128801) B2128801
theorem B3035009 : Blo 558808 3035009 := bstep (se 2 (by rfl) ⟨1138128, by rfl⟩ : syracuseStep 3035009 = 2276257) B2276257
theorem B675739 : Blo 558808 675739 := bstep (se 1 (by rfl) ⟨506804, by rfl⟩ : syracuseStep 675739 = 1013609) B1013609
theorem B1265615 : Blo 558808 1265615 := bstep (se 1 (by rfl) ⟨949211, by rfl⟩ : syracuseStep 1265615 = 1898423) B1898423
theorem B708583 : Blo 558808 708583 := bstep (se 1 (by rfl) ⟨531437, by rfl⟩ : syracuseStep 708583 = 1062875) B1062875
theorem B839945 : Blo 558808 839945 := bstep (se 2 (by rfl) ⟨314979, by rfl⟩ : syracuseStep 839945 = 629959) B629959
theorem B5394761 : Blo 558808 5394761 := bstep (se 2 (by rfl) ⟨2023035, by rfl⟩ : syracuseStep 5394761 = 4046071) B4046071
theorem B1265993 : Blo 558808 1265993 := bstep (se 2 (by rfl) ⟨474747, by rfl⟩ : syracuseStep 1265993 = 949495) B949495
theorem B1266011 : Blo 558808 1266011 := bstep (se 1 (by rfl) ⟨949508, by rfl⟩ : syracuseStep 1266011 = 1899017) B1899017
theorem B840047 : Blo 558808 840047 := bstep (se 1 (by rfl) ⟨630035, by rfl⟩ : syracuseStep 840047 = 1260071) B1260071
theorem B1200595 : Blo 558808 1200595 := bstep (se 1 (by rfl) ⟨900446, by rfl⟩ : syracuseStep 1200595 = 1800893) B1800893
theorem B4248125 : Blo 558808 4248125 := bstep (se 3 (by rfl) ⟨796523, by rfl⟩ : syracuseStep 4248125 = 1593047) B1593047
theorem B840263 : Blo 558808 840263 := bstep (se 1 (by rfl) ⟨630197, by rfl⟩ : syracuseStep 840263 = 1260395) B1260395
theorem B4543073 : Blo 558808 4543073 := bstep (se 2 (by rfl) ⟨1703652, by rfl⟩ : syracuseStep 4543073 = 3407305) B3407305
theorem B840299 : Blo 558808 840299 := bstep (se 1 (by rfl) ⟨630224, by rfl⟩ : syracuseStep 840299 = 1260449) B1260449
theorem B2839211 : Blo 558808 2839211 := bstep (se 1 (by rfl) ⟨2129408, by rfl⟩ : syracuseStep 2839211 = 4258817) B4258817
theorem B1594039 : Blo 558808 1594039 := bstep (se 1 (by rfl) ⟨1195529, by rfl⟩ : syracuseStep 1594039 = 2391059) B2391059
theorem B4543199 : Blo 558808 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B840527 : Blo 558808 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B3199945 : Blo 558808 3199945 := bstep (se 2 (by rfl) ⟨1199979, by rfl⟩ : syracuseStep 3199945 = 2399959) B2399959
theorem B1889243 : Blo 558808 1889243 := bstep (se 1 (by rfl) ⟨1416932, by rfl⟩ : syracuseStep 1889243 = 2833865) B2833865
theorem B1889405 : Blo 558808 1889405 := bstep (se 3 (by rfl) ⟨354263, by rfl⟩ : syracuseStep 1889405 = 708527) B708527
theorem B2839697 : Blo 558808 2839697 := bstep (se 2 (by rfl) ⟨1064886, by rfl⟩ : syracuseStep 2839697 = 2129773) B2129773
theorem B840923 : Blo 558808 840923 := bstep (se 1 (by rfl) ⟨630692, by rfl⟩ : syracuseStep 840923 = 1261385) B1261385
theorem B1889513 : Blo 558808 1889513 := bstep (se 2 (by rfl) ⟨708567, by rfl⟩ : syracuseStep 1889513 = 1417135) B1417135
theorem B808223 : Blo 558808 808223 := bstep (se 1 (by rfl) ⟨606167, by rfl⟩ : syracuseStep 808223 = 1212335) B1212335
theorem B841097 : Blo 558808 841097 := bstep (se 2 (by rfl) ⟨315411, by rfl⟩ : syracuseStep 841097 = 630823) B630823
theorem B1889675 : Blo 558808 1889675 := bstep (se 1 (by rfl) ⟨1417256, by rfl⟩ : syracuseStep 1889675 = 2834513) B2834513
theorem B1201825 : Blo 558808 1201825 := bstep (se 2 (by rfl) ⟨450684, by rfl⟩ : syracuseStep 1201825 = 901369) B901369
theorem B841451 : Blo 558808 841451 := bstep (se 1 (by rfl) ⟨631088, by rfl⟩ : syracuseStep 841451 = 1262177) B1262177
theorem B5003063 : Blo 558808 5003063 := bstep (se 1 (by rfl) ⟨3752297, by rfl⟩ : syracuseStep 5003063 = 7504595) B7504595
theorem B841679 : Blo 558808 841679 := bstep (se 1 (by rfl) ⟨631259, by rfl⟩ : syracuseStep 841679 = 1262519) B1262519
theorem B14342345 : Blo 558808 14342345 := bstep (se 2 (by rfl) ⟨5378379, by rfl⟩ : syracuseStep 14342345 = 10756759) B10756759
theorem B1595645 : Blo 558808 1595645 := bstep (se 3 (by rfl) ⟨299183, by rfl⟩ : syracuseStep 1595645 = 598367) B598367
theorem B842075 : Blo 558808 842075 := bstep (se 1 (by rfl) ⟨631556, by rfl⟩ : syracuseStep 842075 = 1263113) B1263113
theorem B4774463 : Blo 558808 4774463 := bstep (se 1 (by rfl) ⟨3580847, by rfl⟩ : syracuseStep 4774463 = 7161695) B7161695
theorem B842303 : Blo 558808 842303 := bstep (se 1 (by rfl) ⟨631727, by rfl⟩ : syracuseStep 842303 = 1263455) B1263455
theorem B6380207 : Blo 558808 6380207 := bstep (se 1 (by rfl) ⟨4785155, by rfl⟩ : syracuseStep 6380207 = 9570311) B9570311
theorem B6576815 : Blo 558808 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B842423 : Blo 558808 842423 := bstep (se 1 (by rfl) ⟨631817, by rfl⟩ : syracuseStep 842423 = 1263635) B1263635
theorem B842651 : Blo 558808 842651 := bstep (se 1 (by rfl) ⟨631988, by rfl⟩ : syracuseStep 842651 = 1263977) B1263977
theorem B4250555 : Blo 558808 4250555 := bstep (se 1 (by rfl) ⟨3187916, by rfl⟩ : syracuseStep 4250555 = 6375833) B6375833
theorem B843047 : Blo 558808 843047 := bstep (se 1 (by rfl) ⟨632285, by rfl⟩ : syracuseStep 843047 = 1264571) B1264571
theorem B843131 : Blo 558808 843131 := bstep (se 1 (by rfl) ⟨632348, by rfl⟩ : syracuseStep 843131 = 1264697) B1264697
theorem B843257 : Blo 558808 843257 := bstep (se 2 (by rfl) ⟨316221, by rfl⟩ : syracuseStep 843257 = 632443) B632443
theorem B2842127 : Blo 558808 2842127 := bstep (se 1 (by rfl) ⟨2131595, by rfl⟩ : syracuseStep 2842127 = 4263191) B4263191
theorem B843359 : Blo 558808 843359 := bstep (se 1 (by rfl) ⟨632519, by rfl⟩ : syracuseStep 843359 = 1265039) B1265039
theorem B843575 : Blo 558808 843575 := bstep (se 1 (by rfl) ⟨632681, by rfl⟩ : syracuseStep 843575 = 1265363) B1265363
theorem B843881 : Blo 558808 843881 := bstep (se 2 (by rfl) ⟨316455, by rfl⟩ : syracuseStep 843881 = 632911) B632911
theorem B3039443 : Blo 558808 3039443 := bstep (se 1 (by rfl) ⟨2279582, by rfl⟩ : syracuseStep 3039443 = 4559165) B4559165
theorem B1892699 : Blo 558808 1892699 := bstep (se 1 (by rfl) ⟨1419524, by rfl⟩ : syracuseStep 1892699 = 2839049) B2839049
theorem B844199 : Blo 558808 844199 := bstep (se 1 (by rfl) ⟨633149, by rfl⟩ : syracuseStep 844199 = 1266299) B1266299
theorem B2843099 : Blo 558808 2843099 := bstep (se 1 (by rfl) ⟨2132324, by rfl⟩ : syracuseStep 2843099 = 4264649) B4264649
theorem B6152705 : Blo 558808 6152705 := bstep (se 2 (by rfl) ⟨2307264, by rfl⟩ : syracuseStep 6152705 = 4614529) B4614529
theorem B1139321 : Blo 558808 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B3400375 : Blo 558808 3400375 := bstep (se 1 (by rfl) ⟨2550281, by rfl⟩ : syracuseStep 3400375 = 5100563) B5100563
theorem B1598287 : Blo 558808 1598287 := bstep (se 1 (by rfl) ⟨1198715, by rfl⟩ : syracuseStep 1598287 = 2397431) B2397431
theorem B9069407 : Blo 558808 9069407 := bstep (se 1 (by rfl) ⟨6802055, by rfl⟩ : syracuseStep 9069407 = 13604111) B13604111
theorem B2843585 : Blo 558808 2843585 := bstep (se 2 (by rfl) ⟨1066344, by rfl⟩ : syracuseStep 2843585 = 2132689) B2132689
theorem B1598561 : Blo 558808 1598561 := bstep (se 2 (by rfl) ⟨599460, by rfl⟩ : syracuseStep 1598561 = 1198921) B1198921
theorem B1893671 : Blo 558808 1893671 := bstep (se 1 (by rfl) ⟨1420253, by rfl⟩ : syracuseStep 1893671 = 2840507) B2840507
theorem B943609 : Blo 558808 943609 := bstep (se 2 (by rfl) ⟨353853, by rfl⟩ : syracuseStep 943609 = 707707) B707707
theorem B943879 : Blo 558808 943879 := bstep (se 1 (by rfl) ⟨707909, by rfl⟩ : syracuseStep 943879 = 1415819) B1415819
theorem B943913 : Blo 558808 943913 := bstep (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) B707935
theorem B1894535 : Blo 558808 1894535 := bstep (se 1 (by rfl) ⟨1420901, by rfl⟩ : syracuseStep 1894535 = 2841803) B2841803
theorem B2124215 : Blo 558808 2124215 := bstep (se 1 (by rfl) ⟨1593161, by rfl⟩ : syracuseStep 2124215 = 3186323) B3186323
theorem B944635 : Blo 558808 944635 := bstep (se 1 (by rfl) ⟨708476, by rfl⟩ : syracuseStep 944635 = 1416953) B1416953
theorem B2878199 : Blo 558808 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B945067 : Blo 558808 945067 := bstep (se 1 (by rfl) ⟨708800, by rfl⟩ : syracuseStep 945067 = 1417601) B1417601
theorem B945371 : Blo 558808 945371 := bstep (se 1 (by rfl) ⟨709028, by rfl⟩ : syracuseStep 945371 = 1418057) B1418057
theorem B6810911 : Blo 558808 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B1797407 : Blo 558808 1797407 := bstep (se 1 (by rfl) ⟨1348055, by rfl⟩ : syracuseStep 1797407 = 2696111) B2696111
theorem B1895777 : Blo 558808 1895777 := bstep (se 2 (by rfl) ⟨710916, by rfl⟩ : syracuseStep 1895777 = 1421833) B1421833
theorem B945607 : Blo 558808 945607 := bstep (se 1 (by rfl) ⟨709205, by rfl⟩ : syracuseStep 945607 = 1418411) B1418411
theorem B2551391 : Blo 558808 2551391 := bstep (se 1 (by rfl) ⟨1913543, by rfl⟩ : syracuseStep 2551391 = 3827087) B3827087
theorem B683743 : Blo 558808 683743 := bstep (se 1 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 683743 = 1025615) B1025615
theorem B946127 : Blo 558808 946127 := bstep (se 1 (by rfl) ⟨709595, by rfl⟩ : syracuseStep 946127 = 1419191) B1419191
theorem B1601545 : Blo 558808 1601545 := bstep (se 2 (by rfl) ⟨600579, by rfl⟩ : syracuseStep 1601545 = 1201159) B1201159
theorem B2846825 : Blo 558808 2846825 := bstep (se 2 (by rfl) ⟨1067559, by rfl⟩ : syracuseStep 2846825 = 2135119) B2135119
theorem B4780235 : Blo 558808 4780235 := bstep (se 1 (by rfl) ⟨3585176, by rfl⟩ : syracuseStep 4780235 = 7170353) B7170353
theorem B1798625 : Blo 558808 1798625 := bstep (se 2 (by rfl) ⟨674484, by rfl⟩ : syracuseStep 1798625 = 1348969) B1348969
theorem B1012295 : Blo 558808 1012295 := bstep (se 1 (by rfl) ⟨759221, by rfl⟩ : syracuseStep 1012295 = 1518443) B1518443
theorem B946795 : Blo 558808 946795 := bstep (se 1 (by rfl) ⟨710096, by rfl⟩ : syracuseStep 946795 = 1420193) B1420193
theorem B5403257 : Blo 558808 5403257 := bstep (se 2 (by rfl) ⟨2026221, by rfl⟩ : syracuseStep 5403257 = 4052443) B4052443
theorem B1438607 : Blo 558808 1438607 := bstep (se 1 (by rfl) ⟨1078955, by rfl⟩ : syracuseStep 1438607 = 2157911) B2157911
theorem B947099 : Blo 558808 947099 := bstep (se 1 (by rfl) ⟨710324, by rfl⟩ : syracuseStep 947099 = 1420649) B1420649
theorem B3634301 : Blo 558808 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B8058001 : Blo 558808 8058001 := bstep (se 2 (by rfl) ⟨3021750, by rfl⟩ : syracuseStep 8058001 = 6043501) B6043501
theorem B10810583 : Blo 558808 10810583 := bstep (se 1 (by rfl) ⟨8107937, by rfl⟩ : syracuseStep 10810583 = 16215875) B16215875
theorem B2847959 : Blo 558808 2847959 := bstep (se 1 (by rfl) ⟨2135969, by rfl⟩ : syracuseStep 2847959 = 4271939) B4271939
theorem B1897721 : Blo 558808 1897721 := bstep (se 2 (by rfl) ⟨711645, by rfl⟩ : syracuseStep 1897721 = 1423291) B1423291
theorem B1897991 : Blo 558808 1897991 := bstep (se 1 (by rfl) ⟨1423493, by rfl⟩ : syracuseStep 1897991 = 2846987) B2846987
theorem B1799867 : Blo 558808 1799867 := bstep (se 1 (by rfl) ⟨1349900, by rfl⟩ : syracuseStep 1799867 = 2699801) B2699801
theorem B1898963 : Blo 558808 1898963 := bstep (se 1 (by rfl) ⟨1424222, by rfl⟩ : syracuseStep 1898963 = 2848445) B2848445
theorem B1899071 : Blo 558808 1899071 := bstep (se 1 (by rfl) ⟨1424303, by rfl⟩ : syracuseStep 1899071 = 2848607) B2848607
theorem B6486803 : Blo 558808 6486803 := bstep (se 1 (by rfl) ⟨4865102, by rfl⟩ : syracuseStep 6486803 = 9730205) B9730205
theorem B2554895 : Blo 558808 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B1080463 : Blo 558808 1080463 := bstep (se 1 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 1080463 = 1620695) B1620695
theorem B851231 : Blo 558808 851231 := bstep (se 1 (by rfl) ⟨638423, by rfl⟩ : syracuseStep 851231 = 1276847) B1276847
theorem B3604297 : Blo 558808 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B720719 : Blo 558808 720719 := bstep (se 1 (by rfl) ⟨540539, by rfl⟩ : syracuseStep 720719 = 1081079) B1081079
theorem B9600929 : Blo 558808 9600929 := bstep (se 2 (by rfl) ⟨3600348, by rfl⟩ : syracuseStep 9600929 = 7200697) B7200697
theorem B3407791 : Blo 558808 3407791 := bstep (se 1 (by rfl) ⟨2555843, by rfl⟩ : syracuseStep 3407791 = 5111687) B5111687
theorem B6914099 : Blo 558808 6914099 := bstep (se 1 (by rfl) ⟨5185574, by rfl⟩ : syracuseStep 6914099 = 10371149) B10371149
theorem B1278305 : Blo 558808 1278305 := bstep (se 2 (by rfl) ⟨479364, by rfl⟩ : syracuseStep 1278305 = 958729) B958729
theorem B8192609 : Blo 558808 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B1704577 : Blo 558808 1704577 := bstep (se 2 (by rfl) ⟨639216, by rfl⟩ : syracuseStep 1704577 = 1278433) B1278433
theorem B10781363 : Blo 558808 10781363 := bstep (se 1 (by rfl) ⟨8086022, by rfl⟩ : syracuseStep 10781363 = 16172045) B16172045
theorem B15598657 : Blo 558808 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B2131049 : Blo 558808 2131049 := bstep (se 2 (by rfl) ⟨799143, by rfl⟩ : syracuseStep 2131049 = 1598287) B1598287
theorem B558843 : Blo 558808 558843 := bstep (se 1 (by rfl) ⟨419132, by rfl⟩ : syracuseStep 558843 = 838265) B838265
theorem B558879 : Blo 558808 558879 := bstep (se 1 (by rfl) ⟨419159, by rfl⟩ : syracuseStep 558879 = 838319) B838319
theorem B558911 : Blo 558808 558911 := bstep (se 1 (by rfl) ⟨419183, by rfl⟩ : syracuseStep 558911 = 838367) B838367
theorem B853991 : Blo 558808 853991 := bstep (se 1 (by rfl) ⟨640493, by rfl⟩ : syracuseStep 853991 = 1280987) B1280987
theorem B559087 : Blo 558808 559087 := bstep (se 1 (by rfl) ⟨419315, by rfl⟩ : syracuseStep 559087 = 838631) B838631
theorem B10749995 : Blo 558808 10749995 := bstep (se 1 (by rfl) ⟨8062496, by rfl⟩ : syracuseStep 10749995 = 16124993) B16124993
theorem B559259 : Blo 558808 559259 := bstep (se 1 (by rfl) ⟨419444, by rfl⟩ : syracuseStep 559259 = 838889) B838889
theorem B559295 : Blo 558808 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B2132203 : Blo 558808 2132203 := bstep (se 1 (by rfl) ⟨1599152, by rfl⟩ : syracuseStep 2132203 = 3198305) B3198305
theorem B559407 : Blo 558808 559407 := bstep (se 1 (by rfl) ⟨419555, by rfl⟩ : syracuseStep 559407 = 839111) B839111
theorem B4786523 : Blo 558808 4786523 := bstep (se 1 (by rfl) ⟨3589892, by rfl⟩ : syracuseStep 4786523 = 7179785) B7179785
theorem B3246427 : Blo 558808 3246427 := bstep (se 1 (by rfl) ⟨2434820, by rfl⟩ : syracuseStep 3246427 = 4869641) B4869641
theorem B559643 : Blo 558808 559643 := bstep (se 1 (by rfl) ⟨419732, by rfl⟩ : syracuseStep 559643 = 839465) B839465
theorem B559647 : Blo 558808 559647 := bstep (se 1 (by rfl) ⟨419735, by rfl⟩ : syracuseStep 559647 = 839471) B839471
theorem B5376617 : Blo 558808 5376617 := bstep (se 2 (by rfl) ⟨2016231, by rfl⟩ : syracuseStep 5376617 = 4032463) B4032463
theorem B559963 : Blo 558808 559963 := bstep (se 1 (by rfl) ⟨419972, by rfl⟩ : syracuseStep 559963 = 839945) B839945
theorem B560031 : Blo 558808 560031 := bstep (se 1 (by rfl) ⟨420023, by rfl⟩ : syracuseStep 560031 = 840047) B840047
theorem B560175 : Blo 558808 560175 := bstep (se 1 (by rfl) ⟨420131, by rfl⟩ : syracuseStep 560175 = 840263) B840263
theorem B560199 : Blo 558808 560199 := bstep (se 1 (by rfl) ⟨420149, by rfl⟩ : syracuseStep 560199 = 840299) B840299
theorem B560351 : Blo 558808 560351 := bstep (se 1 (by rfl) ⟨420263, by rfl⟩ : syracuseStep 560351 = 840527) B840527
theorem B560615 : Blo 558808 560615 := bstep (se 1 (by rfl) ⟨420461, by rfl⟩ : syracuseStep 560615 = 840923) B840923
theorem B560731 : Blo 558808 560731 := bstep (se 1 (by rfl) ⟨420548, by rfl⟩ : syracuseStep 560731 = 841097) B841097
theorem B2133661 : Blo 558808 2133661 := bstep (se 3 (by rfl) ⟨400061, by rfl⟩ : syracuseStep 2133661 = 800123) B800123
theorem B560967 : Blo 558808 560967 := bstep (se 1 (by rfl) ⟨420725, by rfl⟩ : syracuseStep 560967 = 841451) B841451
theorem B2690921 : Blo 558808 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B561119 : Blo 558808 561119 := bstep (se 1 (by rfl) ⟨420839, by rfl⟩ : syracuseStep 561119 = 841679) B841679
theorem B561383 : Blo 558808 561383 := bstep (se 1 (by rfl) ⟨421037, by rfl⟩ : syracuseStep 561383 = 842075) B842075
theorem B3182975 : Blo 558808 3182975 := bstep (se 1 (by rfl) ⟨2387231, by rfl⟩ : syracuseStep 3182975 = 4774463) B4774463
theorem B561535 : Blo 558808 561535 := bstep (se 1 (by rfl) ⟨421151, by rfl⟩ : syracuseStep 561535 = 842303) B842303
theorem B561615 : Blo 558808 561615 := bstep (se 1 (by rfl) ⟨421211, by rfl⟩ : syracuseStep 561615 = 842423) B842423
theorem B561767 : Blo 558808 561767 := bstep (se 1 (by rfl) ⟨421325, by rfl⟩ : syracuseStep 561767 = 842651) B842651
theorem B562031 : Blo 558808 562031 := bstep (se 1 (by rfl) ⟨421523, by rfl⟩ : syracuseStep 562031 = 843047) B843047
theorem B562087 : Blo 558808 562087 := bstep (se 1 (by rfl) ⟨421565, by rfl⟩ : syracuseStep 562087 = 843131) B843131
theorem B562171 : Blo 558808 562171 := bstep (se 1 (by rfl) ⟨421628, by rfl⟩ : syracuseStep 562171 = 843257) B843257
theorem B562239 : Blo 558808 562239 := bstep (se 1 (by rfl) ⟨421679, by rfl⟩ : syracuseStep 562239 = 843359) B843359
theorem B562383 : Blo 558808 562383 := bstep (se 1 (by rfl) ⟨421787, by rfl⟩ : syracuseStep 562383 = 843575) B843575
theorem B2135393 : Blo 558808 2135393 := bstep (se 2 (by rfl) ⟨800772, by rfl⟩ : syracuseStep 2135393 = 1601545) B1601545
theorem B562587 : Blo 558808 562587 := bstep (se 1 (by rfl) ⟨421940, by rfl⟩ : syracuseStep 562587 = 843881) B843881
theorem B562799 : Blo 558808 562799 := bstep (se 1 (by rfl) ⟨422099, by rfl⟩ : syracuseStep 562799 = 844199) B844199
theorem B4101803 : Blo 558808 4101803 := bstep (se 1 (by rfl) ⟨3076352, by rfl⟩ : syracuseStep 4101803 = 6152705) B6152705
theorem B759547 : Blo 558808 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B1415465 : Blo 558808 1415465 := bstep (se 2 (by rfl) ⟨530799, by rfl⟩ : syracuseStep 1415465 = 1061599) B1061599
theorem B629275 : Blo 558808 629275 := bstep (se 1 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 629275 = 943913) B943913
theorem B4266593 : Blo 558808 4266593 := bstep (se 2 (by rfl) ⟨1599972, by rfl⟩ : syracuseStep 4266593 = 3199945) B3199945
theorem B1514141 : Blo 558808 1514141 := bstep (se 3 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 1514141 = 567803) B567803
theorem B1710953 : Blo 558808 1710953 := bstep (se 2 (by rfl) ⟨641607, by rfl⟩ : syracuseStep 1710953 = 1283215) B1283215
theorem B1416143 : Blo 558808 1416143 := bstep (se 1 (by rfl) ⟨1062107, by rfl⟩ : syracuseStep 1416143 = 2124215) B2124215
theorem B630247 : Blo 558808 630247 := bstep (se 1 (by rfl) ⟨472685, by rfl⟩ : syracuseStep 630247 = 945371) B945371
theorem B2400029 : Blo 558808 2400029 := bstep (se 3 (by rfl) ⟨450005, by rfl⟩ : syracuseStep 2400029 = 900011) B900011
theorem B630751 : Blo 558808 630751 := bstep (se 1 (by rfl) ⟨473063, by rfl⟩ : syracuseStep 630751 = 946127) B946127
theorem B3186823 : Blo 558808 3186823 := bstep (se 1 (by rfl) ⟨2390117, by rfl⟩ : syracuseStep 3186823 = 4780235) B4780235
theorem B4792607 : Blo 558808 4792607 := bstep (se 1 (by rfl) ⟨3594455, by rfl⟩ : syracuseStep 4792607 = 7188911) B7188911
theorem B959071 : Blo 558808 959071 := bstep (se 1 (by rfl) ⟨719303, by rfl⟩ : syracuseStep 959071 = 1438607) B1438607
theorem B631399 : Blo 558808 631399 := bstep (se 1 (by rfl) ⟨473549, by rfl⟩ : syracuseStep 631399 = 947099) B947099
theorem B4039321 : Blo 558808 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B6563321 : Blo 558808 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B796655 : Blo 558808 796655 := bstep (se 1 (by rfl) ⟨597491, by rfl⟩ : syracuseStep 796655 = 1194983) B1194983
theorem B567487 : Blo 558808 567487 := bstep (se 1 (by rfl) ⟨425615, by rfl⟩ : syracuseStep 567487 = 851231) B851231
theorem B6400619 : Blo 558808 6400619 := bstep (se 1 (by rfl) ⟨4800464, by rfl⟩ : syracuseStep 6400619 = 9600929) B9600929
theorem B797321 : Blo 558808 797321 := bstep (se 2 (by rfl) ⟨298995, by rfl⟩ : syracuseStep 797321 = 597991) B597991
theorem B4270967 : Blo 558808 4270967 := bstep (se 1 (by rfl) ⟨3203225, by rfl⟩ : syracuseStep 4270967 = 6406451) B6406451
theorem B3189739 : Blo 558808 3189739 := bstep (se 1 (by rfl) ⟨2392304, by rfl⟩ : syracuseStep 3189739 = 4784609) B4784609
theorem B3583385 : Blo 558808 3583385 := bstep (se 2 (by rfl) ⟨1343769, by rfl⟩ : syracuseStep 3583385 = 2687539) B2687539
theorem B2829815 : Blo 558808 2829815 := bstep (se 1 (by rfl) ⟨2122361, by rfl⟩ : syracuseStep 2829815 = 4244723) B4244723
theorem B4533833 : Blo 558808 4533833 := bstep (se 2 (by rfl) ⟨1700187, by rfl⟩ : syracuseStep 4533833 = 3400375) B3400375
theorem B13676303 : Blo 558808 13676303 := bstep (se 1 (by rfl) ⟨10257227, by rfl⟩ : syracuseStep 13676303 = 20514455) B20514455
theorem B1257371 : Blo 558808 1257371 := bstep (se 1 (by rfl) ⟨943028, by rfl⟩ : syracuseStep 1257371 = 1886057) B1886057
theorem B896923 : Blo 558808 896923 := bstep (se 1 (by rfl) ⟨672692, by rfl⟩ : syracuseStep 896923 = 1345385) B1345385
theorem B4042669 : Blo 558808 4042669 := bstep (se 3 (by rfl) ⟨758000, by rfl⟩ : syracuseStep 4042669 = 1516001) B1516001
theorem B4796333 : Blo 558808 4796333 := bstep (se 3 (by rfl) ⟨899312, by rfl⟩ : syracuseStep 4796333 = 1798625) B1798625
theorem B569311 : Blo 558808 569311 := bstep (se 1 (by rfl) ⟨426983, by rfl⟩ : syracuseStep 569311 = 853967) B853967
theorem B1257659 : Blo 558808 1257659 := bstep (se 1 (by rfl) ⟨943244, by rfl⟩ : syracuseStep 1257659 = 1886489) B1886489
theorem B2699453 : Blo 558808 2699453 := bstep (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) B1012295
theorem B1061257 : Blo 558808 1061257 := bstep (se 2 (by rfl) ⟨397971, by rfl⟩ : syracuseStep 1061257 = 795943) B795943
theorem B2044327 : Blo 558808 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B1421783 : Blo 558808 1421783 := bstep (se 1 (by rfl) ⟨1066337, by rfl⟩ : syracuseStep 1421783 = 2132675) B2132675
theorem B9548441 : Blo 558808 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B1258145 : Blo 558808 1258145 := bstep (se 2 (by rfl) ⟨471804, by rfl⟩ : syracuseStep 1258145 = 943609) B943609
theorem B2831111 : Blo 558808 2831111 := bstep (se 1 (by rfl) ⟨2123333, by rfl⟩ : syracuseStep 2831111 = 4246667) B4246667
theorem B4043681 : Blo 558808 4043681 := bstep (se 2 (by rfl) ⟨1516380, by rfl⟩ : syracuseStep 4043681 = 3032761) B3032761
theorem B3191723 : Blo 558808 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B1258505 : Blo 558808 1258505 := bstep (se 2 (by rfl) ⟨471939, by rfl⟩ : syracuseStep 1258505 = 943879) B943879
theorem B1258559 : Blo 558808 1258559 := bstep (se 1 (by rfl) ⟨943919, by rfl⟩ : syracuseStep 1258559 = 1887839) B1887839
theorem B2832083 : Blo 558808 2832083 := bstep (se 1 (by rfl) ⟨2124062, by rfl⟩ : syracuseStep 2832083 = 4248125) B4248125
theorem B3028715 : Blo 558808 3028715 := bstep (se 1 (by rfl) ⟨2271536, by rfl⟩ : syracuseStep 3028715 = 4543073) B4543073
theorem B3028799 : Blo 558808 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B1423241 : Blo 558808 1423241 := bstep (se 2 (by rfl) ⟨533715, by rfl⟩ : syracuseStep 1423241 = 1067431) B1067431
theorem B1259495 : Blo 558808 1259495 := bstep (se 1 (by rfl) ⟨944621, by rfl⟩ : syracuseStep 1259495 = 1889243) B1889243
theorem B1259513 : Blo 558808 1259513 := bstep (se 2 (by rfl) ⟨472317, by rfl⟩ : syracuseStep 1259513 = 944635) B944635
theorem B800761 : Blo 558808 800761 := bstep (se 2 (by rfl) ⟨300285, by rfl⟩ : syracuseStep 800761 = 600571) B600571
theorem B1259603 : Blo 558808 1259603 := bstep (se 1 (by rfl) ⟨944702, by rfl⟩ : syracuseStep 1259603 = 1889405) B1889405
theorem B3192929 : Blo 558808 3192929 := bstep (se 2 (by rfl) ⟨1197348, by rfl⟩ : syracuseStep 3192929 = 2394697) B2394697
theorem B1259675 : Blo 558808 1259675 := bstep (se 1 (by rfl) ⟨944756, by rfl⟩ : syracuseStep 1259675 = 1889513) B1889513
theorem B1259783 : Blo 558808 1259783 := bstep (se 1 (by rfl) ⟨944837, by rfl⟩ : syracuseStep 1259783 = 1889675) B1889675
theorem B7649579 : Blo 558808 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B1260089 : Blo 558808 1260089 := bstep (se 2 (by rfl) ⟨472533, by rfl⟩ : syracuseStep 1260089 = 945067) B945067
theorem B1063763 : Blo 558808 1063763 := bstep (se 1 (by rfl) ⟨797822, by rfl⟩ : syracuseStep 1063763 = 1595645) B1595645
theorem B1424425 : Blo 558808 1424425 := bstep (se 2 (by rfl) ⟨534159, by rfl⟩ : syracuseStep 1424425 = 1068319) B1068319
theorem B4799645 : Blo 558808 4799645 := bstep (se 3 (by rfl) ⟨899933, by rfl⟩ : syracuseStep 4799645 = 1799867) B1799867
theorem B1424567 : Blo 558808 1424567 := bstep (se 1 (by rfl) ⟨1068425, by rfl⟩ : syracuseStep 1424567 = 2136851) B2136851
theorem B1260809 : Blo 558808 1260809 := bstep (se 2 (by rfl) ⟨472803, by rfl⟩ : syracuseStep 1260809 = 945607) B945607
theorem B2833703 : Blo 558808 2833703 := bstep (se 1 (by rfl) ⟨2125277, by rfl⟩ : syracuseStep 2833703 = 4250555) B4250555
theorem B900985 : Blo 558808 900985 := bstep (se 2 (by rfl) ⟨337869, by rfl⟩ : syracuseStep 900985 = 675739) B675739
theorem B1261799 : Blo 558808 1261799 := bstep (se 1 (by rfl) ⟨946349, by rfl⟩ : syracuseStep 1261799 = 1892699) B1892699
theorem B1065449 : Blo 558808 1065449 := bstep (se 2 (by rfl) ⟨399543, by rfl⟩ : syracuseStep 1065449 = 799087) B799087
theorem B6046271 : Blo 558808 6046271 := bstep (se 1 (by rfl) ⟨4534703, by rfl⟩ : syracuseStep 6046271 = 9069407) B9069407
theorem B1065707 : Blo 558808 1065707 := bstep (se 1 (by rfl) ⟨799280, by rfl⟩ : syracuseStep 1065707 = 1598561) B1598561
theorem B1065737 : Blo 558808 1065737 := bstep (se 2 (by rfl) ⟨399651, by rfl⟩ : syracuseStep 1065737 = 799303) B799303
theorem B1262393 : Blo 558808 1262393 := bstep (se 2 (by rfl) ⟨473397, by rfl⟩ : syracuseStep 1262393 = 946795) B946795
theorem B1262447 : Blo 558808 1262447 := bstep (se 1 (by rfl) ⟨946835, by rfl⟩ : syracuseStep 1262447 = 1893671) B1893671
theorem B3589049 : Blo 558808 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B1263023 : Blo 558808 1263023 := bstep (se 1 (by rfl) ⟨947267, by rfl⟩ : syracuseStep 1263023 = 1894535) B1894535
theorem B1918799 : Blo 558808 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B3196847 : Blo 558808 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B4245695 : Blo 558808 4245695 := bstep (se 1 (by rfl) ⟨3184271, by rfl⟩ : syracuseStep 4245695 = 6368543) B6368543
theorem B4540607 : Blo 558808 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B1198271 : Blo 558808 1198271 := bstep (se 1 (by rfl) ⟨898703, by rfl⟩ : syracuseStep 1198271 = 1797407) B1797407
theorem B1263851 : Blo 558808 1263851 := bstep (se 1 (by rfl) ⟨947888, by rfl⟩ : syracuseStep 1263851 = 1895777) B1895777
theorem B838559 : Blo 558808 838559 := bstep (se 1 (by rfl) ⟨628919, by rfl⟩ : syracuseStep 838559 = 1257839) B1257839
theorem B838607 : Blo 558808 838607 := bstep (se 1 (by rfl) ⟨628955, by rfl⟩ : syracuseStep 838607 = 1257911) B1257911
theorem B838697 : Blo 558808 838697 := bstep (se 2 (by rfl) ⟨314511, by rfl⟩ : syracuseStep 838697 = 629023) B629023
theorem B838703 : Blo 558808 838703 := bstep (se 1 (by rfl) ⟨629027, by rfl⟩ : syracuseStep 838703 = 1258055) B1258055
theorem B838727 : Blo 558808 838727 := bstep (se 1 (by rfl) ⟨629045, by rfl⟩ : syracuseStep 838727 = 1258091) B1258091
theorem B1887353 : Blo 558808 1887353 := bstep (se 2 (by rfl) ⟨707757, by rfl⟩ : syracuseStep 1887353 = 1415515) B1415515
theorem B838991 : Blo 558808 838991 := bstep (se 1 (by rfl) ⟨629243, by rfl⟩ : syracuseStep 838991 = 1258487) B1258487
theorem B839081 : Blo 558808 839081 := bstep (se 2 (by rfl) ⟨314655, by rfl⟩ : syracuseStep 839081 = 629311) B629311
theorem B1887677 : Blo 558808 1887677 := bstep (se 3 (by rfl) ⟨353939, by rfl⟩ : syracuseStep 1887677 = 707879) B707879
theorem B7687669 : Blo 558808 7687669 := bstep (se 5 (by rfl) ⟨360359, by rfl⟩ : syracuseStep 7687669 = 720719) B720719
theorem B1265147 : Blo 558808 1265147 := bstep (se 1 (by rfl) ⟨948860, by rfl⟩ : syracuseStep 1265147 = 1897721) B1897721
theorem B839231 : Blo 558808 839231 := bstep (se 1 (by rfl) ⟨629423, by rfl⟩ : syracuseStep 839231 = 1258847) B1258847
theorem B1265327 : Blo 558808 1265327 := bstep (se 1 (by rfl) ⟨948995, by rfl⟩ : syracuseStep 1265327 = 1897991) B1897991
theorem B839495 : Blo 558808 839495 := bstep (se 1 (by rfl) ⟨629621, by rfl⟩ : syracuseStep 839495 = 1259243) B1259243
theorem B839579 : Blo 558808 839579 := bstep (se 1 (by rfl) ⟨629684, by rfl⟩ : syracuseStep 839579 = 1259369) B1259369
theorem B1888379 : Blo 558808 1888379 := bstep (se 1 (by rfl) ⟨1416284, by rfl⟩ : syracuseStep 1888379 = 2832569) B2832569
theorem B1888541 : Blo 558808 1888541 := bstep (se 3 (by rfl) ⟨354101, by rfl⟩ : syracuseStep 1888541 = 708203) B708203
theorem B1265975 : Blo 558808 1265975 := bstep (se 1 (by rfl) ⟨949481, by rfl⟩ : syracuseStep 1265975 = 1898963) B1898963
theorem B1266047 : Blo 558808 1266047 := bstep (se 1 (by rfl) ⟨949535, by rfl⟩ : syracuseStep 1266047 = 1899071) B1899071
theorem B1888649 : Blo 558808 1888649 := bstep (se 2 (by rfl) ⟨708243, by rfl⟩ : syracuseStep 1888649 = 1416487) B1416487
theorem B840143 : Blo 558808 840143 := bstep (se 1 (by rfl) ⟨630107, by rfl⟩ : syracuseStep 840143 = 1260215) B1260215
theorem B840185 : Blo 558808 840185 := bstep (se 2 (by rfl) ⟨315069, by rfl⟩ : syracuseStep 840185 = 630139) B630139
theorem B2019923 : Blo 558808 2019923 := bstep (se 1 (by rfl) ⟨1514942, by rfl⟩ : syracuseStep 2019923 = 3029885) B3029885
theorem B840287 : Blo 558808 840287 := bstep (se 1 (by rfl) ⟨630215, by rfl⟩ : syracuseStep 840287 = 1260431) B1260431
theorem B630477553 : Blo 558808 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B840767 : Blo 558808 840767 := bstep (se 1 (by rfl) ⟨630575, by rfl⟩ : syracuseStep 840767 = 1261151) B1261151
theorem B4805729 : Blo 558808 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B840809 : Blo 558808 840809 := bstep (se 2 (by rfl) ⟨315303, by rfl⟩ : syracuseStep 840809 = 630607) B630607
theorem B840911 : Blo 558808 840911 := bstep (se 1 (by rfl) ⟨630683, by rfl⟩ : syracuseStep 840911 = 1261367) B1261367
theorem B3200219 : Blo 558808 3200219 := bstep (se 1 (by rfl) ⟨2400164, by rfl⟩ : syracuseStep 3200219 = 4800329) B4800329
theorem B4543721 : Blo 558808 4543721 := bstep (se 2 (by rfl) ⟨1703895, by rfl⟩ : syracuseStep 4543721 = 3407791) B3407791
theorem B1889567 : Blo 558808 1889567 := bstep (se 1 (by rfl) ⟨1417175, by rfl⟩ : syracuseStep 1889567 = 2834351) B2834351
theorem B1136027 : Blo 558808 1136027 := bstep (se 1 (by rfl) ⟨852020, by rfl⟩ : syracuseStep 1136027 = 1704041) B1704041
theorem B841115 : Blo 558808 841115 := bstep (se 1 (by rfl) ⟨630836, by rfl⟩ : syracuseStep 841115 = 1261673) B1261673
theorem B841337 : Blo 558808 841337 := bstep (se 2 (by rfl) ⟨315501, by rfl⟩ : syracuseStep 841337 = 631003) B631003
theorem B841439 : Blo 558808 841439 := bstep (se 1 (by rfl) ⟨631079, by rfl⟩ : syracuseStep 841439 = 1262159) B1262159
theorem B841535 : Blo 558808 841535 := bstep (se 1 (by rfl) ⟨631151, by rfl⟩ : syracuseStep 841535 = 1262303) B1262303
theorem B3889079 : Blo 558808 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B841703 : Blo 558808 841703 := bstep (se 1 (by rfl) ⟨631277, by rfl⟩ : syracuseStep 841703 = 1262555) B1262555
theorem B841721 : Blo 558808 841721 := bstep (se 2 (by rfl) ⟨315645, by rfl⟩ : syracuseStep 841721 = 631291) B631291
theorem B841823 : Blo 558808 841823 := bstep (se 1 (by rfl) ⟨631367, by rfl⟩ : syracuseStep 841823 = 1262735) B1262735
theorem B1595497 : Blo 558808 1595497 := bstep (se 2 (by rfl) ⟨598311, by rfl⟩ : syracuseStep 1595497 = 1196623) B1196623
theorem B841883 : Blo 558808 841883 := bstep (se 1 (by rfl) ⟨631412, by rfl⟩ : syracuseStep 841883 = 1262825) B1262825
theorem B841919 : Blo 558808 841919 := bstep (se 1 (by rfl) ⟨631439, by rfl⟩ : syracuseStep 841919 = 1262879) B1262879
theorem B841961 : Blo 558808 841961 := bstep (se 2 (by rfl) ⟨315735, by rfl⟩ : syracuseStep 841961 = 631471) B631471
theorem B1595771 : Blo 558808 1595771 := bstep (se 1 (by rfl) ⟨1196828, by rfl⟩ : syracuseStep 1595771 = 2393657) B2393657
theorem B3201403 : Blo 558808 3201403 := bstep (se 1 (by rfl) ⟨2401052, by rfl⟩ : syracuseStep 3201403 = 4802105) B4802105
theorem B842267 : Blo 558808 842267 := bstep (se 1 (by rfl) ⟨631700, by rfl⟩ : syracuseStep 842267 = 1263401) B1263401
theorem B842345 : Blo 558808 842345 := bstep (se 2 (by rfl) ⟨315879, by rfl⟩ : syracuseStep 842345 = 631759) B631759
theorem B14605379 : Blo 558808 14605379 := bstep (se 1 (by rfl) ⟨10954034, by rfl⟩ : syracuseStep 14605379 = 21908069) B21908069
theorem B842873 : Blo 558808 842873 := bstep (se 2 (by rfl) ⟨316077, by rfl⟩ : syracuseStep 842873 = 632155) B632155
theorem B1793153 : Blo 558808 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B1891457 : Blo 558808 1891457 := bstep (se 2 (by rfl) ⟨709296, by rfl⟩ : syracuseStep 1891457 = 1418593) B1418593
theorem B1891511 : Blo 558808 1891511 := bstep (se 1 (by rfl) ⟨1418633, by rfl⟩ : syracuseStep 1891511 = 2837267) B2837267
theorem B842975 : Blo 558808 842975 := bstep (se 1 (by rfl) ⟨632231, by rfl⟩ : syracuseStep 842975 = 1264463) B1264463
theorem B843017 : Blo 558808 843017 := bstep (se 2 (by rfl) ⟨316131, by rfl⟩ : syracuseStep 843017 = 632263) B632263
theorem B11492675 : Blo 558808 11492675 := bstep (se 1 (by rfl) ⟨8619506, by rfl⟩ : syracuseStep 11492675 = 17239013) B17239013
theorem B843119 : Blo 558808 843119 := bstep (se 1 (by rfl) ⟨632339, by rfl⟩ : syracuseStep 843119 = 1264679) B1264679
theorem B4251041 : Blo 558808 4251041 := bstep (se 2 (by rfl) ⟨1594140, by rfl⟩ : syracuseStep 4251041 = 3188281) B3188281
theorem B843239 : Blo 558808 843239 := bstep (se 1 (by rfl) ⟨632429, by rfl⟩ : syracuseStep 843239 = 1264859) B1264859
theorem B4054607 : Blo 558808 4054607 := bstep (se 1 (by rfl) ⟨3040955, by rfl⟩ : syracuseStep 4054607 = 6081911) B6081911
theorem B843371 : Blo 558808 843371 := bstep (se 1 (by rfl) ⟨632528, by rfl⟩ : syracuseStep 843371 = 1265057) B1265057
theorem B843497 : Blo 558808 843497 := bstep (se 2 (by rfl) ⟨316311, by rfl⟩ : syracuseStep 843497 = 632623) B632623
theorem B1597171 : Blo 558808 1597171 := bstep (se 1 (by rfl) ⟨1197878, by rfl⟩ : syracuseStep 1597171 = 2395757) B2395757
theorem B7790339 : Blo 558808 7790339 := bstep (se 1 (by rfl) ⟨5842754, by rfl⟩ : syracuseStep 7790339 = 11685509) B11685509
theorem B843641 : Blo 558808 843641 := bstep (se 2 (by rfl) ⟨316365, by rfl⟩ : syracuseStep 843641 = 632731) B632731
theorem B1892267 : Blo 558808 1892267 := bstep (se 1 (by rfl) ⟨1419200, by rfl⟩ : syracuseStep 1892267 = 2838401) B2838401
theorem B843743 : Blo 558808 843743 := bstep (se 1 (by rfl) ⟨632807, by rfl⟩ : syracuseStep 843743 = 1265615) B1265615
theorem B3825883 : Blo 558808 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B3596507 : Blo 558808 3596507 := bstep (se 1 (by rfl) ⟨2697380, by rfl⟩ : syracuseStep 3596507 = 5394761) B5394761
theorem B843995 : Blo 558808 843995 := bstep (se 1 (by rfl) ⟨632996, by rfl⟩ : syracuseStep 843995 = 1265993) B1265993
theorem B844007 : Blo 558808 844007 := bstep (se 1 (by rfl) ⟨633005, by rfl⟩ : syracuseStep 844007 = 1266011) B1266011
theorem B9691469 : Blo 558808 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B844169 : Blo 558808 844169 := bstep (se 2 (by rfl) ⟨316563, by rfl⟩ : syracuseStep 844169 = 633127) B633127
theorem B1892807 : Blo 558808 1892807 := bstep (se 1 (by rfl) ⟨1419605, by rfl⟩ : syracuseStep 1892807 = 2839211) B2839211
theorem B1598059 : Blo 558808 1598059 := bstep (se 1 (by rfl) ⟨1198544, by rfl⟩ : syracuseStep 1598059 = 2397089) B2397089
theorem B2155261 : Blo 558808 2155261 := bstep (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) B808223
theorem B1893131 : Blo 558808 1893131 := bstep (se 1 (by rfl) ⟨1419848, by rfl⟩ : syracuseStep 1893131 = 2839697) B2839697
theorem B1794973 : Blo 558808 1794973 := bstep (se 3 (by rfl) ⟨336557, by rfl⟩ : syracuseStep 1794973 = 673115) B673115
theorem B943015 : Blo 558808 943015 := bstep (se 1 (by rfl) ⟨707261, by rfl⟩ : syracuseStep 943015 = 1414523) B1414523
theorem B1893401 : Blo 558808 1893401 := bstep (se 2 (by rfl) ⟨710025, by rfl⟩ : syracuseStep 1893401 = 1420051) B1420051
theorem B943177 : Blo 558808 943177 := bstep (se 2 (by rfl) ⟨353691, by rfl⟩ : syracuseStep 943177 = 707383) B707383
theorem B943211 : Blo 558808 943211 := bstep (se 1 (by rfl) ⟨707408, by rfl⟩ : syracuseStep 943211 = 1414817) B1414817
theorem B3335375 : Blo 558808 3335375 := bstep (se 1 (by rfl) ⟨2501531, by rfl⟩ : syracuseStep 3335375 = 5003063) B5003063
theorem B9561563 : Blo 558808 9561563 := bstep (se 1 (by rfl) ⟨7171172, by rfl⟩ : syracuseStep 9561563 = 14342345) B14342345
theorem B1894049 : Blo 558808 1894049 := bstep (se 2 (by rfl) ⟨710268, by rfl⟩ : syracuseStep 1894049 = 1420537) B1420537
theorem B4253471 : Blo 558808 4253471 := bstep (se 1 (by rfl) ⟨3190103, by rfl⟩ : syracuseStep 4253471 = 6380207) B6380207
theorem B4384543 : Blo 558808 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B34498457 : Blo 558808 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B911657 : Blo 558808 911657 := bstep (se 2 (by rfl) ⟨341871, by rfl⟩ : syracuseStep 911657 = 683743) B683743
theorem B1894751 : Blo 558808 1894751 := bstep (se 1 (by rfl) ⟨1421063, by rfl⟩ : syracuseStep 1894751 = 2842127) B2842127
theorem B944507 : Blo 558808 944507 := bstep (se 1 (by rfl) ⟨708380, by rfl⟩ : syracuseStep 944507 = 1416761) B1416761
theorem B1599905 : Blo 558808 1599905 := bstep (se 2 (by rfl) ⟨599964, by rfl⟩ : syracuseStep 1599905 = 1199929) B1199929
theorem B1894913 : Blo 558808 1894913 := bstep (se 2 (by rfl) ⟨710592, by rfl⟩ : syracuseStep 1894913 = 1421185) B1421185
theorem B1010207 : Blo 558808 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B944777 : Blo 558808 944777 := bstep (se 2 (by rfl) ⟨354291, by rfl⟩ : syracuseStep 944777 = 708583) B708583
theorem B2845367 : Blo 558808 2845367 := bstep (se 1 (by rfl) ⟨2134025, by rfl⟩ : syracuseStep 2845367 = 4268051) B4268051
theorem B2026295 : Blo 558808 2026295 := bstep (se 1 (by rfl) ⟨1519721, by rfl⟩ : syracuseStep 2026295 = 3039443) B3039443
theorem B1895399 : Blo 558808 1895399 := bstep (se 1 (by rfl) ⟨1421549, by rfl⟩ : syracuseStep 1895399 = 2843099) B2843099
theorem B1600793 : Blo 558808 1600793 := bstep (se 2 (by rfl) ⟨600297, by rfl⟩ : syracuseStep 1600793 = 1200595) B1200595
theorem B1895723 : Blo 558808 1895723 := bstep (se 1 (by rfl) ⟨1421792, by rfl⟩ : syracuseStep 1895723 = 2843585) B2843585
theorem B1895993 : Blo 558808 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B2125385 : Blo 558808 2125385 := bstep (se 2 (by rfl) ⟨797019, by rfl⟩ : syracuseStep 2125385 = 1594039) B1594039
theorem B946363 : Blo 558808 946363 := bstep (se 1 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 946363 = 1419545) B1419545
theorem B10744001 : Blo 558808 10744001 := bstep (se 2 (by rfl) ⟨4029000, by rfl⟩ : syracuseStep 10744001 = 8058001) B8058001
theorem B946559 : Blo 558808 946559 := bstep (se 1 (by rfl) ⟨709919, by rfl⟩ : syracuseStep 946559 = 1419839) B1419839
theorem B946991 : Blo 558808 946991 := bstep (se 1 (by rfl) ⟨710243, by rfl⟩ : syracuseStep 946991 = 1420487) B1420487
theorem B1602433 : Blo 558808 1602433 := bstep (se 2 (by rfl) ⟨600912, by rfl⟩ : syracuseStep 1602433 = 1201825) B1201825
theorem B8221601 : Blo 558808 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B1700927 : Blo 558808 1700927 := bstep (se 1 (by rfl) ⟨1275695, by rfl⟩ : syracuseStep 1700927 = 2551391) B2551391
theorem B1897883 : Blo 558808 1897883 := bstep (se 1 (by rfl) ⟨1423412, by rfl⟩ : syracuseStep 1897883 = 2846825) B2846825
theorem B947963 : Blo 558808 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B3602171 : Blo 558808 3602171 := bstep (se 1 (by rfl) ⟨2701628, by rfl⟩ : syracuseStep 3602171 = 5403257) B5403257
theorem B4323149 : Blo 558808 4323149 := bstep (se 3 (by rfl) ⟨810590, by rfl⟩ : syracuseStep 4323149 = 1621181) B1621181
theorem B948199 : Blo 558808 948199 := bstep (se 1 (by rfl) ⟨711149, by rfl⟩ : syracuseStep 948199 = 1422299) B1422299
theorem B7207055 : Blo 558808 7207055 := bstep (se 1 (by rfl) ⟨5405291, by rfl⟩ : syracuseStep 7207055 = 10810583) B10810583
theorem B1898639 : Blo 558808 1898639 := bstep (se 1 (by rfl) ⟨1423979, by rfl⟩ : syracuseStep 1898639 = 2847959) B2847959
theorem B7698617 : Blo 558808 7698617 := bstep (se 2 (by rfl) ⟨2886981, by rfl⟩ : syracuseStep 7698617 = 5773963) B5773963
theorem B948415 : Blo 558808 948415 := bstep (se 1 (by rfl) ⟨711311, by rfl⟩ : syracuseStep 948415 = 1422623) B1422623
theorem B1440617 : Blo 558808 1440617 := bstep (se 2 (by rfl) ⟨540231, by rfl⟩ : syracuseStep 1440617 = 1080463) B1080463
theorem B949151 : Blo 558808 949151 := bstep (se 1 (by rfl) ⟨711863, by rfl⟩ : syracuseStep 949151 = 1423727) B1423727
theorem B4324535 : Blo 558808 4324535 := bstep (se 1 (by rfl) ⟨3243401, by rfl⟩ : syracuseStep 4324535 = 6486803) B6486803
theorem B949583 : Blo 558808 949583 := bstep (se 1 (by rfl) ⟨712187, by rfl⟩ : syracuseStep 949583 = 1424375) B1424375
theorem B1703263 : Blo 558808 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B8093357 : Blo 558808 8093357 := bstep (se 3 (by rfl) ⟨1517504, by rfl⟩ : syracuseStep 8093357 = 3035009) B3035009
theorem B852203 : Blo 558808 852203 := bstep (se 1 (by rfl) ⟨639152, by rfl⟩ : syracuseStep 852203 = 1278305) B1278305
theorem B4030847 : Blo 558808 4030847 := bstep (se 1 (by rfl) ⟨3023135, by rfl⟩ : syracuseStep 4030847 = 6046271) B6046271
theorem B2392699 : Blo 558808 2392699 := bstep (se 1 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 2392699 = 3589049) B3589049
theorem B1278761 : Blo 558808 1278761 := bstep (se 2 (by rfl) ⟨479535, by rfl⟩ : syracuseStep 1278761 = 959071) B959071
theorem B2130745 : Blo 558808 2130745 := bstep (se 2 (by rfl) ⟨799029, by rfl⟩ : syracuseStep 2130745 = 1598059) B1598059
theorem B2393297 : Blo 558808 2393297 := bstep (se 2 (by rfl) ⟨897486, by rfl⟩ : syracuseStep 2393297 = 1794973) B1794973
theorem B1279199 : Blo 558808 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B2131231 : Blo 558808 2131231 := bstep (se 1 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 2131231 = 3196847) B3196847
theorem B559039 : Blo 558808 559039 := bstep (se 1 (by rfl) ⟨419279, by rfl⟩ : syracuseStep 559039 = 838559) B838559
theorem B559071 : Blo 558808 559071 := bstep (se 1 (by rfl) ⟨419303, by rfl⟩ : syracuseStep 559071 = 838607) B838607
theorem B559131 : Blo 558808 559131 := bstep (se 1 (by rfl) ⟨419348, by rfl⟩ : syracuseStep 559131 = 838697) B838697
theorem B559135 : Blo 558808 559135 := bstep (se 1 (by rfl) ⟨419351, by rfl⟩ : syracuseStep 559135 = 838703) B838703
theorem B559151 : Blo 558808 559151 := bstep (se 1 (by rfl) ⟨419363, by rfl⟩ : syracuseStep 559151 = 838727) B838727
theorem B559327 : Blo 558808 559327 := bstep (se 1 (by rfl) ⟨419495, by rfl⟩ : syracuseStep 559327 = 838991) B838991
theorem B559387 : Blo 558808 559387 := bstep (se 1 (by rfl) ⟨419540, by rfl⟩ : syracuseStep 559387 = 839081) B839081
theorem B559487 : Blo 558808 559487 := bstep (se 1 (by rfl) ⟨419615, by rfl⟩ : syracuseStep 559487 = 839231) B839231
theorem B559663 : Blo 558808 559663 := bstep (se 1 (by rfl) ⟨419747, by rfl⟩ : syracuseStep 559663 = 839495) B839495
theorem B559719 : Blo 558808 559719 := bstep (se 1 (by rfl) ⟨419789, by rfl⟩ : syracuseStep 559719 = 839579) B839579
theorem B756649 : Blo 558808 756649 := bstep (se 2 (by rfl) ⟨283743, by rfl⟩ : syracuseStep 756649 = 567487) B567487
theorem B560095 : Blo 558808 560095 := bstep (se 1 (by rfl) ⟨420071, by rfl⟩ : syracuseStep 560095 = 840143) B840143
theorem B560123 : Blo 558808 560123 := bstep (se 1 (by rfl) ⟨420092, by rfl⟩ : syracuseStep 560123 = 840185) B840185
theorem B1346615 : Blo 558808 1346615 := bstep (se 1 (by rfl) ⟨1009961, by rfl⟩ : syracuseStep 1346615 = 2019923) B2019923
theorem B560191 : Blo 558808 560191 := bstep (se 1 (by rfl) ⟨420143, by rfl⟩ : syracuseStep 560191 = 840287) B840287
theorem B4328569 : Blo 558808 4328569 := bstep (se 2 (by rfl) ⟨1623213, by rfl⟩ : syracuseStep 4328569 = 3246427) B3246427
theorem B560511 : Blo 558808 560511 := bstep (se 1 (by rfl) ⟨420383, by rfl⟩ : syracuseStep 560511 = 840767) B840767
theorem B560539 : Blo 558808 560539 := bstep (se 1 (by rfl) ⟨420404, by rfl⟩ : syracuseStep 560539 = 840809) B840809
theorem B560607 : Blo 558808 560607 := bstep (se 1 (by rfl) ⟨420455, by rfl⟩ : syracuseStep 560607 = 840911) B840911
theorem B2133479 : Blo 558808 2133479 := bstep (se 1 (by rfl) ⟨1600109, by rfl⟩ : syracuseStep 2133479 = 3200219) B3200219
theorem B560743 : Blo 558808 560743 := bstep (se 1 (by rfl) ⟨420557, by rfl⟩ : syracuseStep 560743 = 841115) B841115
theorem B560891 : Blo 558808 560891 := bstep (se 1 (by rfl) ⟨420668, by rfl⟩ : syracuseStep 560891 = 841337) B841337
theorem B560959 : Blo 558808 560959 := bstep (se 1 (by rfl) ⟨420719, by rfl⟩ : syracuseStep 560959 = 841439) B841439
theorem B561023 : Blo 558808 561023 := bstep (se 1 (by rfl) ⟨420767, by rfl⟩ : syracuseStep 561023 = 841535) B841535
theorem B2592719 : Blo 558808 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B561135 : Blo 558808 561135 := bstep (se 1 (by rfl) ⟨420851, by rfl⟩ : syracuseStep 561135 = 841703) B841703
theorem B561147 : Blo 558808 561147 := bstep (se 1 (by rfl) ⟨420860, by rfl⟩ : syracuseStep 561147 = 841721) B841721
theorem B561215 : Blo 558808 561215 := bstep (se 1 (by rfl) ⟨420911, by rfl⟩ : syracuseStep 561215 = 841823) B841823
theorem B561255 : Blo 558808 561255 := bstep (se 1 (by rfl) ⟨420941, by rfl⟩ : syracuseStep 561255 = 841883) B841883
theorem B561279 : Blo 558808 561279 := bstep (se 1 (by rfl) ⟨420959, by rfl⟩ : syracuseStep 561279 = 841919) B841919
theorem B561307 : Blo 558808 561307 := bstep (se 1 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 561307 = 841961) B841961
theorem B561511 : Blo 558808 561511 := bstep (se 1 (by rfl) ⟨421133, by rfl⟩ : syracuseStep 561511 = 842267) B842267
theorem B561563 : Blo 558808 561563 := bstep (se 1 (by rfl) ⟨421172, by rfl⟩ : syracuseStep 561563 = 842345) B842345
theorem B9736919 : Blo 558808 9736919 := bstep (se 1 (by rfl) ⟨7302689, by rfl⟩ : syracuseStep 9736919 = 14605379) B14605379
theorem B561915 : Blo 558808 561915 := bstep (se 1 (by rfl) ⟨421436, by rfl⟩ : syracuseStep 561915 = 842873) B842873
theorem B561983 : Blo 558808 561983 := bstep (se 1 (by rfl) ⟨421487, by rfl⟩ : syracuseStep 561983 = 842975) B842975
theorem B562011 : Blo 558808 562011 := bstep (se 1 (by rfl) ⟨421508, by rfl⟩ : syracuseStep 562011 = 843017) B843017
theorem B562079 : Blo 558808 562079 := bstep (se 1 (by rfl) ⟨421559, by rfl⟩ : syracuseStep 562079 = 843119) B843119
theorem B562159 : Blo 558808 562159 := bstep (se 1 (by rfl) ⟨421619, by rfl⟩ : syracuseStep 562159 = 843239) B843239
theorem B562247 : Blo 558808 562247 := bstep (se 1 (by rfl) ⟨421685, by rfl⟩ : syracuseStep 562247 = 843371) B843371
theorem B562331 : Blo 558808 562331 := bstep (se 1 (by rfl) ⟨421748, by rfl⟩ : syracuseStep 562331 = 843497) B843497
theorem B562427 : Blo 558808 562427 := bstep (se 1 (by rfl) ⟨421820, by rfl⟩ : syracuseStep 562427 = 843641) B843641
theorem B562495 : Blo 558808 562495 := bstep (se 1 (by rfl) ⟨421871, by rfl⟩ : syracuseStep 562495 = 843743) B843743
theorem B2397671 : Blo 558808 2397671 := bstep (se 1 (by rfl) ⟨1798253, by rfl⟩ : syracuseStep 2397671 = 3596507) B3596507
theorem B562663 : Blo 558808 562663 := bstep (se 1 (by rfl) ⟨421997, by rfl⟩ : syracuseStep 562663 = 843995) B843995
theorem B562671 : Blo 558808 562671 := bstep (se 1 (by rfl) ⟨422003, by rfl⟩ : syracuseStep 562671 = 844007) B844007
theorem B6460979 : Blo 558808 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B562779 : Blo 558808 562779 := bstep (se 1 (by rfl) ⟨422084, by rfl⟩ : syracuseStep 562779 = 844169) B844169
theorem B1415009 : Blo 558808 1415009 := bstep (se 2 (by rfl) ⟨530628, by rfl⟩ : syracuseStep 1415009 = 1061257) B1061257
theorem B2725769 : Blo 558808 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B628807 : Blo 558808 628807 := bstep (se 1 (by rfl) ⟨471605, by rfl⟩ : syracuseStep 628807 = 943211) B943211
theorem B840636737 : Blo 558808 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B2136577 : Blo 558808 2136577 := bstep (se 2 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 2136577 = 1602433) B1602433
theorem B629671 : Blo 558808 629671 := bstep (se 1 (by rfl) ⟨472253, by rfl⟩ : syracuseStep 629671 = 944507) B944507
theorem B4267079 : Blo 558808 4267079 := bstep (se 1 (by rfl) ⟨3200309, by rfl⟩ : syracuseStep 4267079 = 6400619) B6400619
theorem B629851 : Blo 558808 629851 := bstep (se 1 (by rfl) ⟨472388, by rfl⟩ : syracuseStep 629851 = 944777) B944777
theorem B1350863 : Blo 558808 1350863 := bstep (se 1 (by rfl) ⟨1013147, by rfl⟩ : syracuseStep 1350863 = 2026295) B2026295
theorem B3022555 : Blo 558808 3022555 := bstep (se 1 (by rfl) ⟨2266916, by rfl⟩ : syracuseStep 3022555 = 4533833) B4533833
theorem B1416923 : Blo 558808 1416923 := bstep (se 1 (by rfl) ⟨1062692, by rfl⟩ : syracuseStep 1416923 = 2125385) B2125385
theorem B9117535 : Blo 558808 9117535 := bstep (se 1 (by rfl) ⟨6838151, by rfl⟩ : syracuseStep 9117535 = 13676303) B13676303
theorem B631039 : Blo 558808 631039 := bstep (se 1 (by rfl) ⟨473279, by rfl⟩ : syracuseStep 631039 = 946559) B946559
theorem B6365627 : Blo 558808 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B4268537 : Blo 558808 4268537 := bstep (se 2 (by rfl) ⟨1600701, by rfl⟩ : syracuseStep 4268537 = 3201403) B3201403
theorem B631327 : Blo 558808 631327 := bstep (se 1 (by rfl) ⟨473495, by rfl⟩ : syracuseStep 631327 = 946991) B946991
theorem B2695787 : Blo 558808 2695787 := bstep (se 1 (by rfl) ⟨2021840, by rfl⟩ : syracuseStep 2695787 = 4043681) B4043681
theorem B5481067 : Blo 558808 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B631975 : Blo 558808 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B2401447 : Blo 558808 2401447 := bstep (se 1 (by rfl) ⟨1801085, by rfl⟩ : syracuseStep 2401447 = 3602171) B3602171
theorem B2271017 : Blo 558808 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B632767 : Blo 558808 632767 := bstep (se 1 (by rfl) ⟨474575, by rfl⟩ : syracuseStep 632767 = 949151) B949151
theorem B633055 : Blo 558808 633055 := bstep (se 1 (by rfl) ⟨474791, by rfl⟩ : syracuseStep 633055 = 949583) B949583
theorem B7187575 : Blo 558808 7187575 := bstep (se 1 (by rfl) ⟨5390681, by rfl⟩ : syracuseStep 7187575 = 10781363) B10781363
theorem B1420699 : Blo 558808 1420699 := bstep (se 1 (by rfl) ⟨1065524, by rfl⟩ : syracuseStep 1420699 = 2131049) B2131049
theorem B2272769 : Blo 558808 2272769 := bstep (se 2 (by rfl) ⟨852288, by rfl⟩ : syracuseStep 2272769 = 1704577) B1704577
theorem B5385761 : Blo 558808 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B1257353 : Blo 558808 1257353 := bstep (se 2 (by rfl) ⟨471507, by rfl⟩ : syracuseStep 1257353 = 943015) B943015
theorem B569327 : Blo 558808 569327 := bstep (se 1 (by rfl) ⟨426995, by rfl⟩ : syracuseStep 569327 = 853991) B853991
theorem B1257569 : Blo 558808 1257569 := bstep (se 2 (by rfl) ⟨471588, by rfl⟩ : syracuseStep 1257569 = 943177) B943177
theorem B2830463 : Blo 558808 2830463 := bstep (se 1 (by rfl) ⟨2122847, by rfl⟩ : syracuseStep 2830463 = 4245695) B4245695
theorem B3027071 : Blo 558808 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B3191015 : Blo 558808 3191015 := bstep (se 1 (by rfl) ⟨2393261, by rfl⟩ : syracuseStep 3191015 = 4786523) B4786523
theorem B3584411 : Blo 558808 3584411 := bstep (se 1 (by rfl) ⟨2688308, by rfl⟩ : syracuseStep 3584411 = 5376617) B5376617
theorem B1258235 : Blo 558808 1258235 := bstep (se 1 (by rfl) ⟨943676, by rfl⟩ : syracuseStep 1258235 = 1887353) B1887353
theorem B1258451 : Blo 558808 1258451 := bstep (se 1 (by rfl) ⟨943838, by rfl⟩ : syracuseStep 1258451 = 1887677) B1887677
theorem B5846057 : Blo 558808 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B1258919 : Blo 558808 1258919 := bstep (se 1 (by rfl) ⟨944189, by rfl⟩ : syracuseStep 1258919 = 1888379) B1888379
theorem B1259027 : Blo 558808 1259027 := bstep (se 1 (by rfl) ⟨944270, by rfl⟩ : syracuseStep 1259027 = 1888541) B1888541
theorem B1259099 : Blo 558808 1259099 := bstep (se 1 (by rfl) ⟨944324, by rfl⟩ : syracuseStep 1259099 = 1888649) B1888649
theorem B8894333 : Blo 558808 8894333 := bstep (se 3 (by rfl) ⟨1667687, by rfl⟩ : syracuseStep 8894333 = 3335375) B3335375
theorem B3029147 : Blo 558808 3029147 := bstep (se 1 (by rfl) ⟨2271860, by rfl⟩ : syracuseStep 3029147 = 4543721) B4543721
theorem B1259711 : Blo 558808 1259711 := bstep (se 1 (by rfl) ⟨944783, by rfl⟩ : syracuseStep 1259711 = 1889567) B1889567
theorem B1423595 : Blo 558808 1423595 := bstep (se 1 (by rfl) ⟨1067696, by rfl⟩ : syracuseStep 1423595 = 2135393) B2135393
theorem B3029405 : Blo 558808 3029405 := bstep (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) B1136027
theorem B2734535 : Blo 558808 2734535 := bstep (se 1 (by rfl) ⟨2050901, by rfl⟩ : syracuseStep 2734535 = 4101803) B4101803
theorem B1063847 : Blo 558808 1063847 := bstep (se 1 (by rfl) ⟨797885, by rfl⟩ : syracuseStep 1063847 = 1595771) B1595771
theorem B1195435 : Blo 558808 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B1260971 : Blo 558808 1260971 := bstep (se 1 (by rfl) ⟨945728, by rfl⟩ : syracuseStep 1260971 = 1891457) B1891457
theorem B1261007 : Blo 558808 1261007 := bstep (se 1 (by rfl) ⟨945755, by rfl⟩ : syracuseStep 1261007 = 1891511) B1891511
theorem B8076797 : Blo 558808 8076797 := bstep (se 3 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 8076797 = 3028799) B3028799
theorem B2834027 : Blo 558808 2834027 := bstep (se 1 (by rfl) ⟨2125520, by rfl⟩ : syracuseStep 2834027 = 4251041) B4251041
theorem B2703071 : Blo 558808 2703071 := bstep (se 1 (by rfl) ⟨2027303, by rfl⟩ : syracuseStep 2703071 = 4054607) B4054607
theorem B5193559 : Blo 558808 5193559 := bstep (se 1 (by rfl) ⟨3895169, by rfl⟩ : syracuseStep 5193559 = 7790339) B7790339
theorem B1195897 : Blo 558808 1195897 := bstep (se 2 (by rfl) ⟨448461, by rfl⟩ : syracuseStep 1195897 = 896923) B896923
theorem B5390225 : Blo 558808 5390225 := bstep (se 2 (by rfl) ⟨2021334, by rfl⟩ : syracuseStep 5390225 = 4042669) B4042669
theorem B1261511 : Blo 558808 1261511 := bstep (se 1 (by rfl) ⟨946133, by rfl⟩ : syracuseStep 1261511 = 1892267) B1892267
theorem B3195071 : Blo 558808 3195071 := bstep (se 1 (by rfl) ⟨2396303, by rfl⟩ : syracuseStep 3195071 = 4792607) B4792607
theorem B1261817 : Blo 558808 1261817 := bstep (se 2 (by rfl) ⟨473181, by rfl⟩ : syracuseStep 1261817 = 946363) B946363
theorem B1261871 : Blo 558808 1261871 := bstep (se 1 (by rfl) ⟨946403, by rfl⟩ : syracuseStep 1261871 = 1892807) B1892807
theorem B3195389 : Blo 558808 3195389 := bstep (se 3 (by rfl) ⟨599135, by rfl⟩ : syracuseStep 3195389 = 1198271) B1198271
theorem B1262087 : Blo 558808 1262087 := bstep (se 1 (by rfl) ⟨946565, by rfl⟩ : syracuseStep 1262087 = 1893131) B1893131
theorem B1262267 : Blo 558808 1262267 := bstep (se 1 (by rfl) ⟨946700, by rfl⟩ : syracuseStep 1262267 = 1893401) B1893401
theorem B6374375 : Blo 558808 6374375 := bstep (se 1 (by rfl) ⟨4780781, by rfl⟩ : syracuseStep 6374375 = 9561563) B9561563
theorem B4375547 : Blo 558808 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B1262699 : Blo 558808 1262699 := bstep (se 1 (by rfl) ⟨947024, by rfl⟩ : syracuseStep 1262699 = 1894049) B1894049
theorem B2835647 : Blo 558808 2835647 := bstep (se 1 (by rfl) ⟨2126735, by rfl⟩ : syracuseStep 2835647 = 4253471) B4253471
theorem B607771 : Blo 558808 607771 := bstep (se 1 (by rfl) ⟨455828, by rfl⟩ : syracuseStep 607771 = 911657) B911657
theorem B1263167 : Blo 558808 1263167 := bstep (se 1 (by rfl) ⟨947375, by rfl⟩ : syracuseStep 1263167 = 1894751) B1894751
theorem B1066603 : Blo 558808 1066603 := bstep (se 1 (by rfl) ⟨799952, by rfl⟩ : syracuseStep 1066603 = 1599905) B1599905
theorem B1263275 : Blo 558808 1263275 := bstep (se 1 (by rfl) ⟨947456, by rfl⟩ : syracuseStep 1263275 = 1894913) B1894913
theorem B673471 : Blo 558808 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B1263599 : Blo 558808 1263599 := bstep (se 1 (by rfl) ⟨947699, by rfl⟩ : syracuseStep 1263599 = 1895399) B1895399
theorem B1067195 : Blo 558808 1067195 := bstep (se 1 (by rfl) ⟨800396, by rfl⟩ : syracuseStep 1067195 = 1600793) B1600793
theorem B1263815 : Blo 558808 1263815 := bstep (se 1 (by rfl) ⟨947861, by rfl⟩ : syracuseStep 1263815 = 1895723) B1895723
theorem B1886543 : Blo 558808 1886543 := bstep (se 1 (by rfl) ⟨1414907, by rfl⟩ : syracuseStep 1886543 = 2829815) B2829815
theorem B1263995 : Blo 558808 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B838247 : Blo 558808 838247 := bstep (se 1 (by rfl) ⟨628685, by rfl⟩ : syracuseStep 838247 = 1257371) B1257371
theorem B3197555 : Blo 558808 3197555 := bstep (se 1 (by rfl) ⟨2398166, by rfl⟩ : syracuseStep 3197555 = 4796333) B4796333
theorem B1264265 : Blo 558808 1264265 := bstep (se 2 (by rfl) ⟨474099, by rfl⟩ : syracuseStep 1264265 = 948199) B948199
theorem B1067681 : Blo 558808 1067681 := bstep (se 2 (by rfl) ⟨400380, by rfl⟩ : syracuseStep 1067681 = 800761) B800761
theorem B838439 : Blo 558808 838439 := bstep (se 1 (by rfl) ⟨628829, by rfl⟩ : syracuseStep 838439 = 1257659) B1257659
theorem B7162667 : Blo 558808 7162667 := bstep (se 1 (by rfl) ⟨5372000, by rfl⟩ : syracuseStep 7162667 = 10744001) B10744001
theorem B1264553 : Blo 558808 1264553 := bstep (se 2 (by rfl) ⟨474207, by rfl⟩ : syracuseStep 1264553 = 948415) B948415
theorem B838763 : Blo 558808 838763 := bstep (se 1 (by rfl) ⟨629072, by rfl⟩ : syracuseStep 838763 = 1258145) B1258145
theorem B1887407 : Blo 558808 1887407 := bstep (se 1 (by rfl) ⟨1415555, by rfl⟩ : syracuseStep 1887407 = 2831111) B2831111
theorem B839003 : Blo 558808 839003 := bstep (se 1 (by rfl) ⟨629252, by rfl⟩ : syracuseStep 839003 = 1258505) B1258505
theorem B839033 : Blo 558808 839033 := bstep (se 2 (by rfl) ⟨314637, by rfl⟩ : syracuseStep 839033 = 629275) B629275
theorem B1133951 : Blo 558808 1133951 := bstep (se 1 (by rfl) ⟨850463, by rfl⟩ : syracuseStep 1133951 = 1700927) B1700927
theorem B839039 : Blo 558808 839039 := bstep (se 1 (by rfl) ⟨629279, by rfl⟩ : syracuseStep 839039 = 1258559) B1258559
theorem B1265255 : Blo 558808 1265255 := bstep (se 1 (by rfl) ⟨948941, by rfl⟩ : syracuseStep 1265255 = 1897883) B1897883
theorem B1888055 : Blo 558808 1888055 := bstep (se 1 (by rfl) ⟨1416041, by rfl⟩ : syracuseStep 1888055 = 2832083) B2832083
theorem B2019143 : Blo 558808 2019143 := bstep (se 1 (by rfl) ⟨1514357, by rfl⟩ : syracuseStep 2019143 = 3028715) B3028715
theorem B4050917 : Blo 558808 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B839663 : Blo 558808 839663 := bstep (se 1 (by rfl) ⟨629747, by rfl⟩ : syracuseStep 839663 = 1259495) B1259495
theorem B839675 : Blo 558808 839675 := bstep (se 1 (by rfl) ⟨629756, by rfl⟩ : syracuseStep 839675 = 1259513) B1259513
theorem B839735 : Blo 558808 839735 := bstep (se 1 (by rfl) ⟨629801, by rfl⟩ : syracuseStep 839735 = 1259603) B1259603
theorem B4804703 : Blo 558808 4804703 := bstep (se 1 (by rfl) ⟨3603527, by rfl⟩ : syracuseStep 4804703 = 7207055) B7207055
theorem B1265759 : Blo 558808 1265759 := bstep (se 1 (by rfl) ⟨949319, by rfl⟩ : syracuseStep 1265759 = 1898639) B1898639
theorem B839783 : Blo 558808 839783 := bstep (se 1 (by rfl) ⟨629837, by rfl⟩ : syracuseStep 839783 = 1259675) B1259675
theorem B5132411 : Blo 558808 5132411 := bstep (se 1 (by rfl) ⟨3849308, by rfl⟩ : syracuseStep 5132411 = 7698617) B7698617
theorem B839855 : Blo 558808 839855 := bstep (se 1 (by rfl) ⟨629891, by rfl⟩ : syracuseStep 839855 = 1259783) B1259783
theorem B5099719 : Blo 558808 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B840059 : Blo 558808 840059 := bstep (se 1 (by rfl) ⟨630044, by rfl⟩ : syracuseStep 840059 = 1260089) B1260089
theorem B709175 : Blo 558808 709175 := bstep (se 1 (by rfl) ⟨531881, by rfl⟩ : syracuseStep 709175 = 1063763) B1063763
theorem B840329 : Blo 558808 840329 := bstep (se 2 (by rfl) ⟨315123, by rfl⟩ : syracuseStep 840329 = 630247) B630247
theorem B12145301 : Blo 558808 12145301 := bstep (se 6 (by rfl) ⟨284655, by rfl⟩ : syracuseStep 12145301 = 569311) B569311
theorem B3199763 : Blo 558808 3199763 := bstep (se 1 (by rfl) ⟨2399822, by rfl⟩ : syracuseStep 3199763 = 4799645) B4799645
theorem B840539 : Blo 558808 840539 := bstep (se 1 (by rfl) ⟨630404, by rfl⟩ : syracuseStep 840539 = 1260809) B1260809
theorem B1889135 : Blo 558808 1889135 := bstep (se 1 (by rfl) ⟨1416851, by rfl⟩ : syracuseStep 1889135 = 2833703) B2833703
theorem B5395571 : Blo 558808 5395571 := bstep (se 1 (by rfl) ⟨4046678, by rfl⟩ : syracuseStep 5395571 = 8093357) B8093357
theorem B1201313 : Blo 558808 1201313 := bstep (se 2 (by rfl) ⟨450492, by rfl⟩ : syracuseStep 1201313 = 900985) B900985
theorem B841001 : Blo 558808 841001 := bstep (se 2 (by rfl) ⟨315375, by rfl⟩ : syracuseStep 841001 = 630751) B630751
theorem B4609399 : Blo 558808 4609399 := bstep (se 1 (by rfl) ⟨3457049, by rfl⟩ : syracuseStep 4609399 = 6914099) B6914099
theorem B841199 : Blo 558808 841199 := bstep (se 1 (by rfl) ⟨630899, by rfl⟩ : syracuseStep 841199 = 1261799) B1261799
theorem B4249097 : Blo 558808 4249097 := bstep (se 2 (by rfl) ⟨1593411, by rfl⟩ : syracuseStep 4249097 = 3186823) B3186823
theorem B710299 : Blo 558808 710299 := bstep (se 1 (by rfl) ⟨532724, by rfl⟩ : syracuseStep 710299 = 1065449) B1065449
theorem B5461739 : Blo 558808 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B710471 : Blo 558808 710471 := bstep (se 1 (by rfl) ⟨532853, by rfl⟩ : syracuseStep 710471 = 1065707) B1065707
theorem B7198541 : Blo 558808 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B841595 : Blo 558808 841595 := bstep (se 1 (by rfl) ⟨631196, by rfl⟩ : syracuseStep 841595 = 1262393) B1262393
theorem B841631 : Blo 558808 841631 := bstep (se 1 (by rfl) ⟨631223, by rfl⟩ : syracuseStep 841631 = 1262447) B1262447
theorem B841865 : Blo 558808 841865 := bstep (se 2 (by rfl) ⟨315699, by rfl⟩ : syracuseStep 841865 = 631399) B631399
theorem B842015 : Blo 558808 842015 := bstep (se 1 (by rfl) ⟨631511, by rfl⟩ : syracuseStep 842015 = 1263023) B1263023
theorem B2873681 : Blo 558808 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B20404709 : Blo 558808 20404709 := bstep (se 4 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 20404709 = 3825883) B3825883
theorem B7166663 : Blo 558808 7166663 := bstep (se 1 (by rfl) ⟨5374997, by rfl⟩ : syracuseStep 7166663 = 10749995) B10749995
theorem B20798209 : Blo 558808 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B842567 : Blo 558808 842567 := bstep (se 1 (by rfl) ⟨631925, by rfl⟩ : syracuseStep 842567 = 1263851) B1263851
theorem B2841965 : Blo 558808 2841965 := bstep (se 3 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 2841965 = 1065737) B1065737
theorem B843431 : Blo 558808 843431 := bstep (se 1 (by rfl) ⟨632573, by rfl⟩ : syracuseStep 843431 = 1265147) B1265147
theorem B843551 : Blo 558808 843551 := bstep (se 1 (by rfl) ⟨632663, by rfl⟩ : syracuseStep 843551 = 1265327) B1265327
theorem B843983 : Blo 558808 843983 := bstep (se 1 (by rfl) ⟨632987, by rfl⟩ : syracuseStep 843983 = 1265975) B1265975
theorem B2121983 : Blo 558808 2121983 := bstep (se 1 (by rfl) ⟨1591487, by rfl⟩ : syracuseStep 2121983 = 3182975) B3182975
theorem B844031 : Blo 558808 844031 := bstep (se 1 (by rfl) ⟨633023, by rfl⟩ : syracuseStep 844031 = 1266047) B1266047
theorem B2842937 : Blo 558808 2842937 := bstep (se 2 (by rfl) ⟨1066101, by rfl⟩ : syracuseStep 2842937 = 2132203) B2132203
theorem B3203819 : Blo 558808 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B4252985 : Blo 558808 4252985 := bstep (se 2 (by rfl) ⟨1594869, by rfl⟩ : syracuseStep 4252985 = 3189739) B3189739
theorem B943643 : Blo 558808 943643 := bstep (se 1 (by rfl) ⟨707732, by rfl⟩ : syracuseStep 943643 = 1415465) B1415465
theorem B2844395 : Blo 558808 2844395 := bstep (se 1 (by rfl) ⟨2133296, by rfl⟩ : syracuseStep 2844395 = 4266593) B4266593
theorem B1009427 : Blo 558808 1009427 := bstep (se 1 (by rfl) ⟨757070, by rfl⟩ : syracuseStep 1009427 = 1514141) B1514141
theorem B1140635 : Blo 558808 1140635 := bstep (se 1 (by rfl) ⟨855476, by rfl⟩ : syracuseStep 1140635 = 1710953) B1710953
theorem B944095 : Blo 558808 944095 := bstep (se 1 (by rfl) ⟨708071, by rfl⟩ : syracuseStep 944095 = 1416143) B1416143
theorem B10250225 : Blo 558808 10250225 := bstep (se 2 (by rfl) ⟨3843834, by rfl⟩ : syracuseStep 10250225 = 7687669) B7687669
theorem B2844881 : Blo 558808 2844881 := bstep (se 2 (by rfl) ⟨1066830, by rfl⟩ : syracuseStep 2844881 = 2133661) B2133661
theorem B7661783 : Blo 558808 7661783 := bstep (se 1 (by rfl) ⟨5746337, by rfl⟩ : syracuseStep 7661783 = 11492675) B11492675
theorem B1600019 : Blo 558808 1600019 := bstep (se 1 (by rfl) ⟨1200014, by rfl⟩ : syracuseStep 1600019 = 2400029) B2400029
theorem B2124413 : Blo 558808 2124413 := bstep (se 3 (by rfl) ⟨398327, by rfl⟩ : syracuseStep 2124413 = 796655) B796655
theorem B22998971 : Blo 558808 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B2126189 : Blo 558808 2126189 := bstep (se 3 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 2126189 = 797321) B797321
theorem B1896911 : Blo 558808 1896911 := bstep (se 1 (by rfl) ⟨1422683, by rfl⟩ : syracuseStep 1896911 = 2845367) B2845367
theorem B2847311 : Blo 558808 2847311 := bstep (se 1 (by rfl) ⟨2135483, by rfl⟩ : syracuseStep 2847311 = 4270967) B4270967
theorem B2388923 : Blo 558808 2388923 := bstep (se 1 (by rfl) ⟨1791692, by rfl⟩ : syracuseStep 2388923 = 3583385) B3583385
theorem B2127329 : Blo 558808 2127329 := bstep (se 2 (by rfl) ⟨797748, by rfl⟩ : syracuseStep 2127329 = 1595497) B1595497
theorem B947855 : Blo 558808 947855 := bstep (se 1 (by rfl) ⟨710891, by rfl⟩ : syracuseStep 947855 = 1421783) B1421783
theorem B2127815 : Blo 558808 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B15366581 : Blo 558808 15366581 := bstep (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) B1440617
theorem B2882099 : Blo 558808 2882099 := bstep (se 1 (by rfl) ⟨2161574, by rfl⟩ : syracuseStep 2882099 = 4323149) B4323149
theorem B948827 : Blo 558808 948827 := bstep (se 1 (by rfl) ⟨711620, by rfl⟩ : syracuseStep 948827 = 1423241) B1423241
theorem B1899233 : Blo 558808 1899233 := bstep (se 2 (by rfl) ⟨712212, by rfl⟩ : syracuseStep 1899233 = 1424425) B1424425
theorem B2128619 : Blo 558808 2128619 := bstep (se 1 (by rfl) ⟨1596464, by rfl⟩ : syracuseStep 2128619 = 3192929) B3192929
theorem B2883023 : Blo 558808 2883023 := bstep (se 1 (by rfl) ⟨2162267, by rfl⟩ : syracuseStep 2883023 = 4324535) B4324535
theorem B949711 : Blo 558808 949711 := bstep (se 1 (by rfl) ⟨712283, by rfl⟩ : syracuseStep 949711 = 1424567) B1424567
theorem B7175789 : Blo 558808 7175789 := bstep (se 3 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 7175789 = 2690921) B2690921
theorem B2129561 : Blo 558808 2129561 := bstep (se 2 (by rfl) ⟨798585, by rfl⟩ : syracuseStep 2129561 = 1597171) B1597171
theorem B2130047 : Blo 558808 2130047 := bstep (se 1 (by rfl) ⟨1597535, by rfl⟩ : syracuseStep 2130047 = 3195071) B3195071
theorem B2687231 : Blo 558808 2687231 := bstep (se 1 (by rfl) ⟨2015423, by rfl⟩ : syracuseStep 2687231 = 4030847) B4030847
theorem B2130259 : Blo 558808 2130259 := bstep (se 1 (by rfl) ⟨1597694, by rfl⟩ : syracuseStep 2130259 = 3195389) B3195389
theorem B2917031 : Blo 558808 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B7308089 : Blo 558808 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B558831 : Blo 558808 558831 := bstep (se 1 (by rfl) ⟨419123, by rfl⟩ : syracuseStep 558831 = 838247) B838247
theorem B2131703 : Blo 558808 2131703 := bstep (se 1 (by rfl) ⟨1598777, by rfl⟩ : syracuseStep 2131703 = 3197555) B3197555
theorem B558959 : Blo 558808 558959 := bstep (se 1 (by rfl) ⟨419219, by rfl⟩ : syracuseStep 558959 = 838439) B838439
theorem B559175 : Blo 558808 559175 := bstep (se 1 (by rfl) ⟨419381, by rfl⟩ : syracuseStep 559175 = 838763) B838763
theorem B3410029 : Blo 558808 3410029 := bstep (se 3 (by rfl) ⟨639380, by rfl⟩ : syracuseStep 3410029 = 1278761) B1278761
theorem B559335 : Blo 558808 559335 := bstep (se 1 (by rfl) ⟨419501, by rfl⟩ : syracuseStep 559335 = 839003) B839003
theorem B559355 : Blo 558808 559355 := bstep (se 1 (by rfl) ⟨419516, by rfl⟩ : syracuseStep 559355 = 839033) B839033
theorem B559359 : Blo 558808 559359 := bstep (se 1 (by rfl) ⟨419519, by rfl⟩ : syracuseStep 559359 = 839039) B839039
theorem B1346095 : Blo 558808 1346095 := bstep (se 1 (by rfl) ⟨1009571, by rfl⟩ : syracuseStep 1346095 = 2019143) B2019143
theorem B559775 : Blo 558808 559775 := bstep (se 1 (by rfl) ⟨419831, by rfl⟩ : syracuseStep 559775 = 839663) B839663
theorem B559783 : Blo 558808 559783 := bstep (se 1 (by rfl) ⟨419837, by rfl⟩ : syracuseStep 559783 = 839675) B839675
theorem B559823 : Blo 558808 559823 := bstep (se 1 (by rfl) ⟨419867, by rfl⟩ : syracuseStep 559823 = 839735) B839735
theorem B559855 : Blo 558808 559855 := bstep (se 1 (by rfl) ⟨419891, by rfl⟩ : syracuseStep 559855 = 839783) B839783
theorem B559903 : Blo 558808 559903 := bstep (se 1 (by rfl) ⟨419927, by rfl⟩ : syracuseStep 559903 = 839855) B839855
theorem B560039 : Blo 558808 560039 := bstep (se 1 (by rfl) ⟨420029, by rfl⟩ : syracuseStep 560039 = 840059) B840059
theorem B560219 : Blo 558808 560219 := bstep (se 1 (by rfl) ⟨420164, by rfl⟩ : syracuseStep 560219 = 840329) B840329
theorem B8096867 : Blo 558808 8096867 := bstep (se 1 (by rfl) ⟨6072650, by rfl⟩ : syracuseStep 8096867 = 12145301) B12145301
theorem B6491279 : Blo 558808 6491279 := bstep (se 1 (by rfl) ⟨4868459, by rfl⟩ : syracuseStep 6491279 = 9736919) B9736919
theorem B2133175 : Blo 558808 2133175 := bstep (se 1 (by rfl) ⟨1599881, by rfl⟩ : syracuseStep 2133175 = 3199763) B3199763
theorem B560359 : Blo 558808 560359 := bstep (se 1 (by rfl) ⟨420269, by rfl⟩ : syracuseStep 560359 = 840539) B840539
theorem B3411197 : Blo 558808 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B560667 : Blo 558808 560667 := bstep (se 1 (by rfl) ⟨420500, by rfl⟩ : syracuseStep 560667 = 841001) B841001
theorem B560799 : Blo 558808 560799 := bstep (se 1 (by rfl) ⟨420599, by rfl⟩ : syracuseStep 560799 = 841199) B841199
theorem B3641159 : Blo 558808 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B561063 : Blo 558808 561063 := bstep (se 1 (by rfl) ⟨420797, by rfl⟩ : syracuseStep 561063 = 841595) B841595
theorem B561087 : Blo 558808 561087 := bstep (se 1 (by rfl) ⟨420815, by rfl⟩ : syracuseStep 561087 = 841631) B841631
theorem B12095477 : Blo 558808 12095477 := bstep (se 5 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 12095477 = 1133951) B1133951
theorem B561243 : Blo 558808 561243 := bstep (se 1 (by rfl) ⟨420932, by rfl⟩ : syracuseStep 561243 = 841865) B841865
theorem B5771425 : Blo 558808 5771425 := bstep (se 2 (by rfl) ⟨2164284, by rfl⟩ : syracuseStep 5771425 = 4328569) B4328569
theorem B561343 : Blo 558808 561343 := bstep (se 1 (by rfl) ⟨421007, by rfl⟩ : syracuseStep 561343 = 842015) B842015
theorem B13603139 : Blo 558808 13603139 := bstep (se 1 (by rfl) ⟨10202354, by rfl⟩ : syracuseStep 13603139 = 20404709) B20404709
theorem B561711 : Blo 558808 561711 := bstep (se 1 (by rfl) ⟨421283, by rfl⟩ : syracuseStep 561711 = 842567) B842567
theorem B2691805 : Blo 558808 2691805 := bstep (se 3 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 2691805 = 1009427) B1009427
theorem B562287 : Blo 558808 562287 := bstep (se 1 (by rfl) ⟨421715, by rfl⟩ : syracuseStep 562287 = 843431) B843431
theorem B562367 : Blo 558808 562367 := bstep (se 1 (by rfl) ⟨421775, by rfl⟩ : syracuseStep 562367 = 843551) B843551
theorem B562655 : Blo 558808 562655 := bstep (se 1 (by rfl) ⟨421991, by rfl⟩ : syracuseStep 562655 = 843983) B843983
theorem B1414655 : Blo 558808 1414655 := bstep (se 1 (by rfl) ⟨1060991, by rfl⟩ : syracuseStep 1414655 = 2121983) B2121983
theorem B562687 : Blo 558808 562687 := bstep (se 1 (by rfl) ⟨422015, by rfl⟩ : syracuseStep 562687 = 844031) B844031
theorem B2135879 : Blo 558808 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B629095 : Blo 558808 629095 := bstep (se 1 (by rfl) ⟨471821, by rfl⟩ : syracuseStep 629095 = 943643) B943643
theorem B760423 : Blo 558808 760423 := bstep (se 1 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 760423 = 1140635) B1140635
theorem B1416275 : Blo 558808 1416275 := bstep (se 1 (by rfl) ⟨1062206, by rfl⟩ : syracuseStep 1416275 = 2124413) B2124413
theorem B1515179 : Blo 558808 1515179 := bstep (se 1 (by rfl) ⟨1136384, by rfl⟩ : syracuseStep 1515179 = 2272769) B2272769
theorem B1417459 : Blo 558808 1417459 := bstep (se 1 (by rfl) ⟨1063094, by rfl⟩ : syracuseStep 1417459 = 2126189) B2126189
theorem B1418219 : Blo 558808 1418219 := bstep (se 1 (by rfl) ⟨1063664, by rfl⟩ : syracuseStep 1418219 = 2127329) B2127329
theorem B27730945 : Blo 558808 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B631903 : Blo 558808 631903 := bstep (se 1 (by rfl) ⟨473927, by rfl⟩ : syracuseStep 631903 = 947855) B947855
theorem B1418543 : Blo 558808 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B632551 : Blo 558808 632551 := bstep (se 1 (by rfl) ⟨474413, by rfl⟩ : syracuseStep 632551 = 948827) B948827
theorem B1419079 : Blo 558808 1419079 := bstep (se 1 (by rfl) ⟨1064309, by rfl⟩ : syracuseStep 1419079 = 2128619) B2128619
theorem B5384531 : Blo 558808 5384531 := bstep (se 1 (by rfl) ⟨4038398, by rfl⟩ : syracuseStep 5384531 = 8076797) B8076797
theorem B1419707 : Blo 558808 1419707 := bstep (se 1 (by rfl) ⟨1064780, by rfl⟩ : syracuseStep 1419707 = 2129561) B2129561
theorem B6924745 : Blo 558808 6924745 := bstep (se 2 (by rfl) ⟨2596779, by rfl⟩ : syracuseStep 6924745 = 5193559) B5193559
theorem B6072821 : Blo 558808 6072821 := bstep (se 5 (by rfl) ⟨284663, by rfl⟩ : syracuseStep 6072821 = 569327) B569327
theorem B2272541 : Blo 558808 2272541 := bstep (se 3 (by rfl) ⟨426101, by rfl⟩ : syracuseStep 2272541 = 852203) B852203
theorem B3190265 : Blo 558808 3190265 := bstep (se 2 (by rfl) ⟨1196349, by rfl⟩ : syracuseStep 3190265 = 2392699) B2392699
theorem B1257695 : Blo 558808 1257695 := bstep (se 1 (by rfl) ⟨943271, by rfl⟩ : syracuseStep 1257695 = 1886543) B1886543
theorem B897743 : Blo 558808 897743 := bstep (se 1 (by rfl) ⟨673307, by rfl⟩ : syracuseStep 897743 = 1346615) B1346615
theorem B1258271 : Blo 558808 1258271 := bstep (se 1 (by rfl) ⟨943703, by rfl⟩ : syracuseStep 1258271 = 1887407) B1887407
theorem B1422137 : Blo 558808 1422137 := bstep (se 2 (by rfl) ⟨533301, by rfl⟩ : syracuseStep 1422137 = 1066603) B1066603
theorem B897961 : Blo 558808 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B1422319 : Blo 558808 1422319 := bstep (se 1 (by rfl) ⟨1066739, by rfl⟩ : syracuseStep 1422319 = 2133479) B2133479
theorem B1258703 : Blo 558808 1258703 := bstep (se 1 (by rfl) ⟨944027, by rfl⟩ : syracuseStep 1258703 = 1888055) B1888055
theorem B1258793 : Blo 558808 1258793 := bstep (se 2 (by rfl) ⟨472047, by rfl⟩ : syracuseStep 1258793 = 944095) B944095
theorem B2700611 : Blo 558808 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B3421607 : Blo 558808 3421607 := bstep (se 1 (by rfl) ⟨2566205, by rfl⟩ : syracuseStep 3421607 = 5132411) B5132411
theorem B1259423 : Blo 558808 1259423 := bstep (se 1 (by rfl) ⟨944567, by rfl⟩ : syracuseStep 1259423 = 1889135) B1889135
theorem B800875 : Blo 558808 800875 := bstep (se 1 (by rfl) ⟨600656, by rfl⟩ : syracuseStep 800875 = 1201313) B1201313
theorem B2832731 : Blo 558808 2832731 := bstep (se 1 (by rfl) ⟨2124548, by rfl⟩ : syracuseStep 2832731 = 4249097) B4249097
theorem B4799027 : Blo 558808 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B9583433 : Blo 558808 9583433 := bstep (se 2 (by rfl) ⟨3593787, by rfl⟩ : syracuseStep 9583433 = 7187575) B7187575
theorem B1915787 : Blo 558808 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B900575 : Blo 558808 900575 := bstep (se 1 (by rfl) ⟨675431, by rfl⟩ : syracuseStep 900575 = 1350863) B1350863
theorem B6799625 : Blo 558808 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B4243751 : Blo 558808 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B2835323 : Blo 558808 2835323 := bstep (se 1 (by rfl) ⟨2126492, by rfl⟩ : syracuseStep 2835323 = 4252985) B4252985
theorem B8078413 : Blo 558808 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B6833483 : Blo 558808 6833483 := bstep (se 1 (by rfl) ⟨5125112, by rfl⟩ : syracuseStep 6833483 = 10250225) B10250225
theorem B7685597 : Blo 558808 7685597 := bstep (se 3 (by rfl) ⟨1441049, by rfl⟩ : syracuseStep 7685597 = 2882099) B2882099
theorem B1066679 : Blo 558808 1066679 := bstep (se 1 (by rfl) ⟨800009, by rfl⟩ : syracuseStep 1066679 = 1600019) B1600019
theorem B6145865 : Blo 558808 6145865 := bstep (se 2 (by rfl) ⟨2304699, by rfl⟩ : syracuseStep 6145865 = 4609399) B4609399
theorem B3590507 : Blo 558808 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B838235 : Blo 558808 838235 := bstep (se 1 (by rfl) ⟨628676, by rfl⟩ : syracuseStep 838235 = 1257353) B1257353
theorem B838379 : Blo 558808 838379 := bstep (se 1 (by rfl) ⟨628784, by rfl⟩ : syracuseStep 838379 = 1257569) B1257569
theorem B1886975 : Blo 558808 1886975 := bstep (se 1 (by rfl) ⟨1415231, by rfl⟩ : syracuseStep 1886975 = 2830463) B2830463
theorem B2018047 : Blo 558808 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B838409 : Blo 558808 838409 := bstep (se 2 (by rfl) ⟨314403, by rfl⟩ : syracuseStep 838409 = 628807) B628807
theorem B1264607 : Blo 558808 1264607 := bstep (se 1 (by rfl) ⟨948455, by rfl⟩ : syracuseStep 1264607 = 1896911) B1896911
theorem B838823 : Blo 558808 838823 := bstep (se 1 (by rfl) ⟨629117, by rfl⟩ : syracuseStep 838823 = 1258235) B1258235
theorem B1592615 : Blo 558808 1592615 := bstep (se 1 (by rfl) ⟨1194461, by rfl⟩ : syracuseStep 1592615 = 2388923) B2388923
theorem B838967 : Blo 558808 838967 := bstep (se 1 (by rfl) ⟨629225, by rfl⟩ : syracuseStep 838967 = 1258451) B1258451
theorem B839279 : Blo 558808 839279 := bstep (se 1 (by rfl) ⟨629459, by rfl⟩ : syracuseStep 839279 = 1258919) B1258919
theorem B839351 : Blo 558808 839351 := bstep (se 1 (by rfl) ⟨629513, by rfl⟩ : syracuseStep 839351 = 1259027) B1259027
theorem B839399 : Blo 558808 839399 := bstep (se 1 (by rfl) ⟨629549, by rfl⟩ : syracuseStep 839399 = 1259099) B1259099
theorem B839561 : Blo 558808 839561 := bstep (se 2 (by rfl) ⟨314835, by rfl⟩ : syracuseStep 839561 = 629671) B629671
theorem B2019431 : Blo 558808 2019431 := bstep (se 1 (by rfl) ⟨1514573, by rfl⟩ : syracuseStep 2019431 = 3029147) B3029147
theorem B839801 : Blo 558808 839801 := bstep (se 2 (by rfl) ⟨314925, by rfl⟩ : syracuseStep 839801 = 629851) B629851
theorem B839807 : Blo 558808 839807 := bstep (se 1 (by rfl) ⟨629855, by rfl⟩ : syracuseStep 839807 = 1259711) B1259711
theorem B10244387 : Blo 558808 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B1823023 : Blo 558808 1823023 := bstep (se 1 (by rfl) ⟨1367267, by rfl⟩ : syracuseStep 1823023 = 2734535) B2734535
theorem B1266155 : Blo 558808 1266155 := bstep (se 1 (by rfl) ⟨949616, by rfl⟩ : syracuseStep 1266155 = 1899233) B1899233
theorem B1593913 : Blo 558808 1593913 := bstep (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) B1195435
theorem B1266281 : Blo 558808 1266281 := bstep (se 2 (by rfl) ⟨474855, by rfl⟩ : syracuseStep 1266281 = 949711) B949711
theorem B709231 : Blo 558808 709231 := bstep (se 1 (by rfl) ⟨531923, by rfl⟩ : syracuseStep 709231 = 1063847) B1063847
theorem B840647 : Blo 558808 840647 := bstep (se 1 (by rfl) ⟨630485, by rfl⟩ : syracuseStep 840647 = 1260971) B1260971
theorem B840671 : Blo 558808 840671 := bstep (se 1 (by rfl) ⟨630503, by rfl⟩ : syracuseStep 840671 = 1261007) B1261007
theorem B1922015 : Blo 558808 1922015 := bstep (se 1 (by rfl) ⟨1441511, by rfl⟩ : syracuseStep 1922015 = 2883023) B2883023
theorem B1889351 : Blo 558808 1889351 := bstep (se 1 (by rfl) ⟨1417013, by rfl⟩ : syracuseStep 1889351 = 2834027) B2834027
theorem B1594529 : Blo 558808 1594529 := bstep (se 2 (by rfl) ⟨597948, by rfl⟩ : syracuseStep 1594529 = 1195897) B1195897
theorem B3593483 : Blo 558808 3593483 := bstep (se 1 (by rfl) ⟨2695112, by rfl⟩ : syracuseStep 3593483 = 5390225) B5390225
theorem B841007 : Blo 558808 841007 := bstep (se 1 (by rfl) ⟨630755, by rfl⟩ : syracuseStep 841007 = 1261511) B1261511
theorem B841211 : Blo 558808 841211 := bstep (se 1 (by rfl) ⟨630908, by rfl⟩ : syracuseStep 841211 = 1261817) B1261817
theorem B841247 : Blo 558808 841247 := bstep (se 1 (by rfl) ⟨630935, by rfl⟩ : syracuseStep 841247 = 1261871) B1261871
theorem B841385 : Blo 558808 841385 := bstep (se 2 (by rfl) ⟨315519, by rfl⟩ : syracuseStep 841385 = 631039) B631039
theorem B841391 : Blo 558808 841391 := bstep (se 1 (by rfl) ⟨631043, by rfl⟩ : syracuseStep 841391 = 1262087) B1262087
theorem B841511 : Blo 558808 841511 := bstep (se 1 (by rfl) ⟨631133, by rfl⟩ : syracuseStep 841511 = 1262267) B1262267
theorem B4249583 : Blo 558808 4249583 := bstep (se 1 (by rfl) ⟨3187187, by rfl⟩ : syracuseStep 4249583 = 6374375) B6374375
theorem B841769 : Blo 558808 841769 := bstep (se 2 (by rfl) ⟨315663, by rfl⟩ : syracuseStep 841769 = 631327) B631327
theorem B841799 : Blo 558808 841799 := bstep (se 1 (by rfl) ⟨631349, by rfl⟩ : syracuseStep 841799 = 1262699) B1262699
theorem B1890431 : Blo 558808 1890431 := bstep (se 1 (by rfl) ⟨1417823, by rfl⟩ : syracuseStep 1890431 = 2835647) B2835647
theorem B1595531 : Blo 558808 1595531 := bstep (se 1 (by rfl) ⟨1196648, by rfl⟩ : syracuseStep 1595531 = 2393297) B2393297
theorem B842111 : Blo 558808 842111 := bstep (se 1 (by rfl) ⟨631583, by rfl⟩ : syracuseStep 842111 = 1263167) B1263167
theorem B2840993 : Blo 558808 2840993 := bstep (se 2 (by rfl) ⟨1065372, by rfl⟩ : syracuseStep 2840993 = 2130745) B2130745
theorem B842183 : Blo 558808 842183 := bstep (se 1 (by rfl) ⟨631637, by rfl⟩ : syracuseStep 842183 = 1263275) B1263275
theorem B842399 : Blo 558808 842399 := bstep (se 1 (by rfl) ⟨631799, by rfl⟩ : syracuseStep 842399 = 1263599) B1263599
theorem B842543 : Blo 558808 842543 := bstep (se 1 (by rfl) ⟨631907, by rfl⟩ : syracuseStep 842543 = 1263815) B1263815
theorem B1891133 : Blo 558808 1891133 := bstep (se 3 (by rfl) ⟨354587, by rfl⟩ : syracuseStep 1891133 = 709175) B709175
theorem B842633 : Blo 558808 842633 := bstep (se 2 (by rfl) ⟨315987, by rfl⟩ : syracuseStep 842633 = 631975) B631975
theorem B3201929 : Blo 558808 3201929 := bstep (se 2 (by rfl) ⟨1200723, by rfl⟩ : syracuseStep 3201929 = 2401447) B2401447
theorem B842663 : Blo 558808 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B2841641 : Blo 558808 2841641 := bstep (se 2 (by rfl) ⟨1065615, by rfl⟩ : syracuseStep 2841641 = 2131231) B2131231
theorem B842843 : Blo 558808 842843 := bstep (se 1 (by rfl) ⟨632132, by rfl⟩ : syracuseStep 842843 = 1264265) B1264265
theorem B4775111 : Blo 558808 4775111 := bstep (se 1 (by rfl) ⟨3581333, by rfl⟩ : syracuseStep 4775111 = 7162667) B7162667
theorem B843035 : Blo 558808 843035 := bstep (se 1 (by rfl) ⟨632276, by rfl⟩ : syracuseStep 843035 = 1264553) B1264553
theorem B810361 : Blo 558808 810361 := bstep (se 2 (by rfl) ⟨303885, by rfl⟩ : syracuseStep 810361 = 607771) B607771
theorem B843503 : Blo 558808 843503 := bstep (se 1 (by rfl) ⟨632627, by rfl⟩ : syracuseStep 843503 = 1265255) B1265255
theorem B843689 : Blo 558808 843689 := bstep (se 2 (by rfl) ⟨316383, by rfl⟩ : syracuseStep 843689 = 632767) B632767
theorem B1728479 : Blo 558808 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B3203135 : Blo 558808 3203135 := bstep (se 1 (by rfl) ⟨2402351, by rfl⟩ : syracuseStep 3203135 = 4804703) B4804703
theorem B843839 : Blo 558808 843839 := bstep (se 1 (by rfl) ⟨632879, by rfl⟩ : syracuseStep 843839 = 1265759) B1265759
theorem B844073 : Blo 558808 844073 := bstep (se 2 (by rfl) ⟨316527, by rfl⟩ : syracuseStep 844073 = 633055) B633055
theorem B3597047 : Blo 558808 3597047 := bstep (se 1 (by rfl) ⟨2697785, by rfl⟩ : syracuseStep 3597047 = 5395571) B5395571
theorem B1598447 : Blo 558808 1598447 := bstep (se 1 (by rfl) ⟨1198835, by rfl⟩ : syracuseStep 1598447 = 2397671) B2397671
theorem B1008865 : Blo 558808 1008865 := bstep (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) B756649
theorem B943339 : Blo 558808 943339 := bstep (se 1 (by rfl) ⟨707504, by rfl⟩ : syracuseStep 943339 = 1415009) B1415009
theorem B17229277 : Blo 558808 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B560424491 : Blo 558808 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B4777775 : Blo 558808 4777775 := bstep (se 1 (by rfl) ⟨3583331, by rfl⟩ : syracuseStep 4777775 = 7166663) B7166663
theorem B1894265 : Blo 558808 1894265 := bstep (se 2 (by rfl) ⟨710349, by rfl⟩ : syracuseStep 1894265 = 1420699) B1420699
theorem B2844719 : Blo 558808 2844719 := bstep (se 1 (by rfl) ⟨2133539, by rfl⟩ : syracuseStep 2844719 = 4267079) B4267079
theorem B6056045 : Blo 558808 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B1894589 : Blo 558808 1894589 := bstep (se 3 (by rfl) ⟨355235, by rfl⟩ : syracuseStep 1894589 = 710471) B710471
theorem B1894643 : Blo 558808 1894643 := bstep (se 1 (by rfl) ⟨1420982, by rfl⟩ : syracuseStep 1894643 = 2841965) B2841965
theorem B23718221 : Blo 558808 23718221 := bstep (se 3 (by rfl) ⟨4447166, by rfl⟩ : syracuseStep 23718221 = 8894333) B8894333
theorem B7268717 : Blo 558808 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B944615 : Blo 558808 944615 := bstep (se 1 (by rfl) ⟨708461, by rfl⟩ : syracuseStep 944615 = 1416923) B1416923
theorem B1895291 : Blo 558808 1895291 := bstep (se 1 (by rfl) ⟨1421468, by rfl⟩ : syracuseStep 1895291 = 2842937) B2842937
theorem B2845691 : Blo 558808 2845691 := bstep (se 1 (by rfl) ⟨2134268, by rfl⟩ : syracuseStep 2845691 = 4268537) B4268537
theorem B1797191 : Blo 558808 1797191 := bstep (se 1 (by rfl) ⟨1347893, by rfl⟩ : syracuseStep 1797191 = 2695787) B2695787
theorem B2845853 : Blo 558808 2845853 := bstep (se 3 (by rfl) ⟨533597, by rfl⟩ : syracuseStep 2845853 = 1067195) B1067195
theorem B1896263 : Blo 558808 1896263 := bstep (se 1 (by rfl) ⟨1422197, by rfl⟩ : syracuseStep 1896263 = 2844395) B2844395
theorem B1896587 : Blo 558808 1896587 := bstep (se 1 (by rfl) ⟨1422440, by rfl⟩ : syracuseStep 1896587 = 2844881) B2844881
theorem B5107855 : Blo 558808 5107855 := bstep (se 1 (by rfl) ⟨3830891, by rfl⟩ : syracuseStep 5107855 = 7661783) B7661783
theorem B2847149 : Blo 558808 2847149 := bstep (se 3 (by rfl) ⟨533840, by rfl⟩ : syracuseStep 2847149 = 1067681) B1067681
theorem B947065 : Blo 558808 947065 := bstep (se 2 (by rfl) ⟨355149, by rfl⟩ : syracuseStep 947065 = 710299) B710299
theorem B15332647 : Blo 558808 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B2127343 : Blo 558808 2127343 := bstep (se 1 (by rfl) ⟨1595507, by rfl⟩ : syracuseStep 2127343 = 3191015) B3191015
theorem B2389607 : Blo 558808 2389607 := bstep (se 1 (by rfl) ⟨1792205, by rfl⟩ : syracuseStep 2389607 = 3584411) B3584411
theorem B1898207 : Blo 558808 1898207 := bstep (se 1 (by rfl) ⟨1423655, by rfl⟩ : syracuseStep 1898207 = 2847311) B2847311
theorem B2848769 : Blo 558808 2848769 := bstep (se 2 (by rfl) ⟨1068288, by rfl⟩ : syracuseStep 2848769 = 2136577) B2136577
theorem B3897371 : Blo 558808 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B949063 : Blo 558808 949063 := bstep (se 1 (by rfl) ⟨711797, by rfl⟩ : syracuseStep 949063 = 1423595) B1423595
theorem B4030073 : Blo 558808 4030073 := bstep (se 2 (by rfl) ⟨1511277, by rfl⟩ : syracuseStep 4030073 = 3022555) B3022555
theorem B4783859 : Blo 558808 4783859 := bstep (se 1 (by rfl) ⟨3587894, by rfl⟩ : syracuseStep 4783859 = 7175789) B7175789
theorem B12156713 : Blo 558808 12156713 := bstep (se 2 (by rfl) ⟨4558767, by rfl⟩ : syracuseStep 12156713 = 9117535) B9117535
theorem B1802047 : Blo 558808 1802047 := bstep (se 1 (by rfl) ⟨1351535, by rfl⟩ : syracuseStep 1802047 = 2703071) B2703071
theorem B4555655 : Blo 558808 4555655 := bstep (se 1 (by rfl) ⟨3416741, by rfl⟩ : syracuseStep 4555655 = 6833483) B6833483
theorem B4097243 : Blo 558808 4097243 := bstep (se 1 (by rfl) ⟨3072932, by rfl⟩ : syracuseStep 4097243 = 6145865) B6145865
theorem B558823 : Blo 558808 558823 := bstep (se 1 (by rfl) ⟨419117, by rfl⟩ : syracuseStep 558823 = 838235) B838235
theorem B558919 : Blo 558808 558919 := bstep (se 1 (by rfl) ⟨419189, by rfl⟩ : syracuseStep 558919 = 838379) B838379
theorem B558939 : Blo 558808 558939 := bstep (se 1 (by rfl) ⟨419204, by rfl⟩ : syracuseStep 558939 = 838409) B838409
theorem B2393981 : Blo 558808 2393981 := bstep (se 3 (by rfl) ⟨448871, by rfl⟩ : syracuseStep 2393981 = 897743) B897743
theorem B22972369 : Blo 558808 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B4327519 : Blo 558808 4327519 := bstep (se 1 (by rfl) ⟨3245639, by rfl⟩ : syracuseStep 4327519 = 6491279) B6491279
theorem B559215 : Blo 558808 559215 := bstep (se 1 (by rfl) ⟨419411, by rfl⟩ : syracuseStep 559215 = 838823) B838823
theorem B559311 : Blo 558808 559311 := bstep (se 1 (by rfl) ⟨419483, by rfl⟩ : syracuseStep 559311 = 838967) B838967
theorem B559519 : Blo 558808 559519 := bstep (se 1 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 559519 = 839279) B839279
theorem B559567 : Blo 558808 559567 := bstep (se 1 (by rfl) ⟨419675, by rfl⟩ : syracuseStep 559567 = 839351) B839351
theorem B559599 : Blo 558808 559599 := bstep (se 1 (by rfl) ⟨419699, by rfl⟩ : syracuseStep 559599 = 839399) B839399
theorem B559707 : Blo 558808 559707 := bstep (se 1 (by rfl) ⟨419780, by rfl⟩ : syracuseStep 559707 = 839561) B839561
theorem B8063651 : Blo 558808 8063651 := bstep (se 1 (by rfl) ⟨6047738, by rfl⟩ : syracuseStep 8063651 = 12095477) B12095477
theorem B1346287 : Blo 558808 1346287 := bstep (se 1 (by rfl) ⟨1009715, by rfl⟩ : syracuseStep 1346287 = 2019431) B2019431
theorem B559867 : Blo 558808 559867 := bstep (se 1 (by rfl) ⟨419900, by rfl⟩ : syracuseStep 559867 = 839801) B839801
theorem B559871 : Blo 558808 559871 := bstep (se 1 (by rfl) ⟨419903, by rfl⟩ : syracuseStep 559871 = 839807) B839807
theorem B560431 : Blo 558808 560431 := bstep (se 1 (by rfl) ⟨420323, by rfl⟩ : syracuseStep 560431 = 840647) B840647
theorem B560447 : Blo 558808 560447 := bstep (se 1 (by rfl) ⟨420335, by rfl⟩ : syracuseStep 560447 = 840671) B840671
theorem B1281343 : Blo 558808 1281343 := bstep (se 1 (by rfl) ⟨961007, by rfl⟩ : syracuseStep 1281343 = 1922015) B1922015
theorem B2395655 : Blo 558808 2395655 := bstep (se 1 (by rfl) ⟨1796741, by rfl⟩ : syracuseStep 2395655 = 3593483) B3593483
theorem B560671 : Blo 558808 560671 := bstep (se 1 (by rfl) ⟨420503, by rfl⟩ : syracuseStep 560671 = 841007) B841007
theorem B560807 : Blo 558808 560807 := bstep (se 1 (by rfl) ⟨420605, by rfl⟩ : syracuseStep 560807 = 841211) B841211
theorem B2690729 : Blo 558808 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B560831 : Blo 558808 560831 := bstep (se 1 (by rfl) ⟨420623, by rfl⟩ : syracuseStep 560831 = 841247) B841247
theorem B560923 : Blo 558808 560923 := bstep (se 1 (by rfl) ⟨420692, by rfl⟩ : syracuseStep 560923 = 841385) B841385
theorem B560927 : Blo 558808 560927 := bstep (se 1 (by rfl) ⟨420695, by rfl⟩ : syracuseStep 560927 = 841391) B841391
theorem B561007 : Blo 558808 561007 := bstep (se 1 (by rfl) ⟨420755, by rfl⟩ : syracuseStep 561007 = 841511) B841511
theorem B561179 : Blo 558808 561179 := bstep (se 1 (by rfl) ⟨420884, by rfl⟩ : syracuseStep 561179 = 841769) B841769
theorem B561199 : Blo 558808 561199 := bstep (se 1 (by rfl) ⟨420899, by rfl⟩ : syracuseStep 561199 = 841799) B841799
theorem B561407 : Blo 558808 561407 := bstep (se 1 (by rfl) ⟨421055, by rfl⟩ : syracuseStep 561407 = 842111) B842111
theorem B561455 : Blo 558808 561455 := bstep (se 1 (by rfl) ⟨421091, by rfl⟩ : syracuseStep 561455 = 842183) B842183
theorem B561599 : Blo 558808 561599 := bstep (se 1 (by rfl) ⟨421199, by rfl⟩ : syracuseStep 561599 = 842399) B842399
theorem B561695 : Blo 558808 561695 := bstep (se 1 (by rfl) ⟨421271, by rfl⟩ : syracuseStep 561695 = 842543) B842543
theorem B561755 : Blo 558808 561755 := bstep (se 1 (by rfl) ⟨421316, by rfl⟩ : syracuseStep 561755 = 842633) B842633
theorem B2134619 : Blo 558808 2134619 := bstep (se 1 (by rfl) ⟨1600964, by rfl⟩ : syracuseStep 2134619 = 3201929) B3201929
theorem B561775 : Blo 558808 561775 := bstep (se 1 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 561775 = 842663) B842663
theorem B561895 : Blo 558808 561895 := bstep (se 1 (by rfl) ⟨421421, by rfl⟩ : syracuseStep 561895 = 842843) B842843
theorem B3183407 : Blo 558808 3183407 := bstep (se 1 (by rfl) ⟨2387555, by rfl⟩ : syracuseStep 3183407 = 4775111) B4775111
theorem B562023 : Blo 558808 562023 := bstep (se 1 (by rfl) ⟨421517, by rfl⟩ : syracuseStep 562023 = 843035) B843035
theorem B562335 : Blo 558808 562335 := bstep (se 1 (by rfl) ⟨421751, by rfl⟩ : syracuseStep 562335 = 843503) B843503
theorem B562459 : Blo 558808 562459 := bstep (se 1 (by rfl) ⟨421844, by rfl⟩ : syracuseStep 562459 = 843689) B843689
theorem B1152319 : Blo 558808 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B2135423 : Blo 558808 2135423 := bstep (se 1 (by rfl) ⟨1601567, by rfl⟩ : syracuseStep 2135423 = 3203135) B3203135
theorem B562559 : Blo 558808 562559 := bstep (se 1 (by rfl) ⟨421919, by rfl⟩ : syracuseStep 562559 = 843839) B843839
theorem B562715 : Blo 558808 562715 := bstep (se 1 (by rfl) ⟨422036, by rfl⟩ : syracuseStep 562715 = 844073) B844073
theorem B2430697 : Blo 558808 2430697 := bstep (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) B1823023
theorem B2398031 : Blo 558808 2398031 := bstep (se 1 (by rfl) ⟨1798523, by rfl⟩ : syracuseStep 2398031 = 3597047) B3597047
theorem B9574685 : Blo 558808 9574685 := bstep (se 3 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 9574685 = 3590507) B3590507
theorem B5380613 : Blo 558808 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B3185183 : Blo 558808 3185183 := bstep (se 1 (by rfl) ⟨2388887, by rfl⟩ : syracuseStep 3185183 = 4777775) B4777775
theorem B4037363 : Blo 558808 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B629743 : Blo 558808 629743 := bstep (se 1 (by rfl) ⟨472307, by rfl⟩ : syracuseStep 629743 = 944615) B944615
theorem B2598247 : Blo 558808 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B9709757 : Blo 558808 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B600383 : Blo 558808 600383 := bstep (se 1 (by rfl) ⟨450287, by rfl⟩ : syracuseStep 600383 = 900575) B900575
theorem B2402729 : Blo 558808 2402729 := bstep (se 2 (by rfl) ⟨901023, by rfl⟩ : syracuseStep 2402729 = 1802047) B1802047
theorem B3189239 : Blo 558808 3189239 := bstep (se 1 (by rfl) ⟨2391929, by rfl⟩ : syracuseStep 3189239 = 4783859) B4783859
theorem B8104475 : Blo 558808 8104475 := bstep (se 1 (by rfl) ⟨6078356, by rfl⟩ : syracuseStep 8104475 = 12156713) B12156713
theorem B1420031 : Blo 558808 1420031 := bstep (se 1 (by rfl) ⟨1065023, by rfl⟩ : syracuseStep 1420031 = 2130047) B2130047
theorem B4533083 : Blo 558808 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B2829167 : Blo 558808 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B5123731 : Blo 558808 5123731 := bstep (se 1 (by rfl) ⟨3842798, by rfl⟩ : syracuseStep 5123731 = 7685597) B7685597
theorem B1421135 : Blo 558808 1421135 := bstep (se 1 (by rfl) ⟨1065851, by rfl⟩ : syracuseStep 1421135 = 2131703) B2131703
theorem B36974593 : Blo 558808 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B1257785 : Blo 558808 1257785 := bstep (se 2 (by rfl) ⟨471669, by rfl⟩ : syracuseStep 1257785 = 943339) B943339
theorem B7778749 : Blo 558808 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B1257983 : Blo 558808 1257983 := bstep (se 1 (by rfl) ⟨943487, by rfl⟩ : syracuseStep 1257983 = 1886975) B1886975
theorem B2274131 : Blo 558808 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B1061743 : Blo 558808 1061743 := bstep (se 1 (by rfl) ⟨796307, by rfl⟩ : syracuseStep 1061743 = 1592615) B1592615
theorem B6829591 : Blo 558808 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B1259567 : Blo 558808 1259567 := bstep (se 1 (by rfl) ⟨944675, by rfl⟩ : syracuseStep 1259567 = 1889351) B1889351
theorem B1063019 : Blo 558808 1063019 := bstep (se 1 (by rfl) ⟨797264, by rfl⟩ : syracuseStep 1063019 = 1594529) B1594529
theorem B9124285 : Blo 558808 9124285 := bstep (se 3 (by rfl) ⟨1710803, by rfl⟩ : syracuseStep 9124285 = 3421607) B3421607
theorem B1423919 : Blo 558808 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B2833055 : Blo 558808 2833055 := bstep (se 1 (by rfl) ⟨2124791, by rfl⟩ : syracuseStep 2833055 = 4249583) B4249583
theorem B1260287 : Blo 558808 1260287 := bstep (se 1 (by rfl) ⟨945215, by rfl⟩ : syracuseStep 1260287 = 1890431) B1890431
theorem B1063687 : Blo 558808 1063687 := bstep (se 1 (by rfl) ⟨797765, by rfl⟩ : syracuseStep 1063687 = 1595531) B1595531
theorem B1260755 : Blo 558808 1260755 := bstep (se 1 (by rfl) ⟨945566, by rfl⟩ : syracuseStep 1260755 = 1891133) B1891133
theorem B1065631 : Blo 558808 1065631 := bstep (se 1 (by rfl) ⟨799223, by rfl⟩ : syracuseStep 1065631 = 1598447) B1598447
theorem B19383245 : Blo 558808 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B3589073 : Blo 558808 3589073 := bstep (se 2 (by rfl) ⟨1345902, by rfl⟩ : syracuseStep 3589073 = 2691805) B2691805
theorem B1262753 : Blo 558808 1262753 := bstep (se 2 (by rfl) ⟨473532, by rfl⟩ : syracuseStep 1262753 = 947065) B947065
theorem B1197281 : Blo 558808 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B1262843 : Blo 558808 1262843 := bstep (se 1 (by rfl) ⟨947132, by rfl⟩ : syracuseStep 1262843 = 1894265) B1894265
theorem B1263059 : Blo 558808 1263059 := bstep (se 1 (by rfl) ⟨947294, by rfl⟩ : syracuseStep 1263059 = 1894589) B1894589
theorem B1263095 : Blo 558808 1263095 := bstep (se 1 (by rfl) ⟨947321, by rfl⟩ : syracuseStep 1263095 = 1894643) B1894643
theorem B15812147 : Blo 558808 15812147 := bstep (se 1 (by rfl) ⟨11859110, by rfl⟩ : syracuseStep 15812147 = 23718221) B23718221
theorem B3589687 : Blo 558808 3589687 := bstep (se 1 (by rfl) ⟨2692265, by rfl⟩ : syracuseStep 3589687 = 5384531) B5384531
theorem B4048547 : Blo 558808 4048547 := bstep (se 1 (by rfl) ⟨3036410, by rfl⟩ : syracuseStep 4048547 = 6072821) B6072821
theorem B1263527 : Blo 558808 1263527 := bstep (se 1 (by rfl) ⟨947645, by rfl⟩ : syracuseStep 1263527 = 1895291) B1895291
theorem B2836457 : Blo 558808 2836457 := bstep (se 2 (by rfl) ⟨1063671, by rfl⟩ : syracuseStep 2836457 = 2127343) B2127343
theorem B1198127 : Blo 558808 1198127 := bstep (se 1 (by rfl) ⟨898595, by rfl⟩ : syracuseStep 1198127 = 1797191) B1797191
theorem B1264175 : Blo 558808 1264175 := bstep (se 1 (by rfl) ⟨948131, by rfl⟩ : syracuseStep 1264175 = 1896263) B1896263
theorem B1264391 : Blo 558808 1264391 := bstep (se 1 (by rfl) ⟨948293, by rfl⟩ : syracuseStep 1264391 = 1896587) B1896587
theorem B1067833 : Blo 558808 1067833 := bstep (se 2 (by rfl) ⟨400437, by rfl⟩ : syracuseStep 1067833 = 800875) B800875
theorem B838463 : Blo 558808 838463 := bstep (se 1 (by rfl) ⟨628847, by rfl⟩ : syracuseStep 838463 = 1257695) B1257695
theorem B838793 : Blo 558808 838793 := bstep (se 2 (by rfl) ⟨314547, by rfl⟩ : syracuseStep 838793 = 629095) B629095
theorem B838847 : Blo 558808 838847 := bstep (se 1 (by rfl) ⟨629135, by rfl⟩ : syracuseStep 838847 = 1258271) B1258271
theorem B839135 : Blo 558808 839135 := bstep (se 1 (by rfl) ⟨629351, by rfl⟩ : syracuseStep 839135 = 1258703) B1258703
theorem B839195 : Blo 558808 839195 := bstep (se 1 (by rfl) ⟨629396, by rfl⟩ : syracuseStep 839195 = 1258793) B1258793
theorem B1593071 : Blo 558808 1593071 := bstep (se 1 (by rfl) ⟨1194803, by rfl⟩ : syracuseStep 1593071 = 2389607) B2389607
theorem B1265417 : Blo 558808 1265417 := bstep (se 2 (by rfl) ⟨474531, by rfl⟩ : syracuseStep 1265417 = 949063) B949063
theorem B1265471 : Blo 558808 1265471 := bstep (se 1 (by rfl) ⟨949103, by rfl⟩ : syracuseStep 1265471 = 1898207) B1898207
theorem B839615 : Blo 558808 839615 := bstep (se 1 (by rfl) ⟨629711, by rfl⟩ : syracuseStep 839615 = 1259423) B1259423
theorem B1888487 : Blo 558808 1888487 := bstep (se 1 (by rfl) ⟨1416365, by rfl⟩ : syracuseStep 1888487 = 2832731) B2832731
theorem B3199351 : Blo 558808 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B1791487 : Blo 558808 1791487 := bstep (se 1 (by rfl) ⟨1343615, by rfl⟩ : syracuseStep 1791487 = 2687231) B2687231
theorem B1889945 : Blo 558808 1889945 := bstep (se 2 (by rfl) ⟨708729, by rfl⟩ : syracuseStep 1889945 = 1417459) B1417459
theorem B2840345 : Blo 558808 2840345 := bstep (se 2 (by rfl) ⟨1065129, by rfl⟩ : syracuseStep 2840345 = 2130259) B2130259
theorem B4872059 : Blo 558808 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B1890215 : Blo 558808 1890215 := bstep (se 1 (by rfl) ⟨1417661, by rfl⟩ : syracuseStep 1890215 = 2835323) B2835323
theorem B711119 : Blo 558808 711119 := bstep (se 1 (by rfl) ⟨533339, by rfl⟩ : syracuseStep 711119 = 1066679) B1066679
theorem B10771217 : Blo 558808 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B842537 : Blo 558808 842537 := bstep (se 2 (by rfl) ⟨315951, by rfl⟩ : syracuseStep 842537 = 631903) B631903
theorem B843071 : Blo 558808 843071 := bstep (se 1 (by rfl) ⟨632303, by rfl⟩ : syracuseStep 843071 = 1264607) B1264607
theorem B5397911 : Blo 558808 5397911 := bstep (se 1 (by rfl) ⟨4048433, by rfl⟩ : syracuseStep 5397911 = 8096867) B8096867
theorem B843401 : Blo 558808 843401 := bstep (se 2 (by rfl) ⟨316275, by rfl⟩ : syracuseStep 843401 = 632551) B632551
theorem B1892105 : Blo 558808 1892105 := bstep (se 2 (by rfl) ⟨709539, by rfl⟩ : syracuseStep 1892105 = 1419079) B1419079
theorem B4546705 : Blo 558808 4546705 := bstep (se 2 (by rfl) ⟨1705014, by rfl⟩ : syracuseStep 4546705 = 3410029) B3410029
theorem B9068759 : Blo 558808 9068759 := bstep (se 1 (by rfl) ⟨6801569, by rfl⟩ : syracuseStep 9068759 = 13603139) B13603139
theorem B844103 : Blo 558808 844103 := bstep (se 1 (by rfl) ⟨633077, by rfl⟩ : syracuseStep 844103 = 1266155) B1266155
theorem B844187 : Blo 558808 844187 := bstep (se 1 (by rfl) ⟨633140, by rfl⟩ : syracuseStep 844187 = 1266281) B1266281
theorem B9232993 : Blo 558808 9232993 := bstep (se 2 (by rfl) ⟨3462372, by rfl⟩ : syracuseStep 9232993 = 6924745) B6924745
theorem B1794793 : Blo 558808 1794793 := bstep (se 2 (by rfl) ⟨673047, by rfl⟩ : syracuseStep 1794793 = 1346095) B1346095
theorem B943103 : Blo 558808 943103 := bstep (se 1 (by rfl) ⟨707327, by rfl⟩ : syracuseStep 943103 = 1414655) B1414655
theorem B2844233 : Blo 558808 2844233 := bstep (se 2 (by rfl) ⟨1066587, by rfl⟩ : syracuseStep 2844233 = 2133175) B2133175
theorem B1893995 : Blo 558808 1893995 := bstep (se 1 (by rfl) ⟨1420496, by rfl⟩ : syracuseStep 1893995 = 2840993) B2840993
theorem B1894427 : Blo 558808 1894427 := bstep (se 1 (by rfl) ⟨1420820, by rfl⟩ : syracuseStep 1894427 = 2841641) B2841641
theorem B944183 : Blo 558808 944183 := bstep (se 1 (by rfl) ⟨708137, by rfl⟩ : syracuseStep 944183 = 1416275) B1416275
theorem B1010119 : Blo 558808 1010119 := bstep (se 1 (by rfl) ⟨757589, by rfl⟩ : syracuseStep 1010119 = 1515179) B1515179
theorem B6810473 : Blo 558808 6810473 := bstep (se 2 (by rfl) ⟨2553927, by rfl⟩ : syracuseStep 6810473 = 5107855) B5107855
theorem B7695233 : Blo 558808 7695233 := bstep (se 2 (by rfl) ⟨2885712, by rfl⟩ : syracuseStep 7695233 = 5771425) B5771425
theorem B945479 : Blo 558808 945479 := bstep (se 1 (by rfl) ⟨709109, by rfl⟩ : syracuseStep 945479 = 1418219) B1418219
theorem B2125217 : Blo 558808 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B945641 : Blo 558808 945641 := bstep (se 2 (by rfl) ⟨354615, by rfl⟩ : syracuseStep 945641 = 709231) B709231
theorem B945695 : Blo 558808 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B373616327 : Blo 558808 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B1896425 : Blo 558808 1896425 := bstep (se 2 (by rfl) ⟨711159, by rfl⟩ : syracuseStep 1896425 = 1422319) B1422319
theorem B1896479 : Blo 558808 1896479 := bstep (se 1 (by rfl) ⟨1422359, by rfl⟩ : syracuseStep 1896479 = 2844719) B2844719
theorem B946471 : Blo 558808 946471 := bstep (se 1 (by rfl) ⟨709853, by rfl⟩ : syracuseStep 946471 = 1419707) B1419707
theorem B20443529 : Blo 558808 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B1897127 : Blo 558808 1897127 := bstep (se 1 (by rfl) ⟨1422845, by rfl⟩ : syracuseStep 1897127 = 2845691) B2845691
theorem B1897235 : Blo 558808 1897235 := bstep (se 1 (by rfl) ⟨1422926, by rfl⟩ : syracuseStep 1897235 = 2845853) B2845853
theorem B2126843 : Blo 558808 2126843 := bstep (se 1 (by rfl) ⟨1595132, by rfl⟩ : syracuseStep 2126843 = 3190265) B3190265
theorem B1898099 : Blo 558808 1898099 := bstep (se 1 (by rfl) ⟨1423574, by rfl⟩ : syracuseStep 1898099 = 2847149) B2847149
theorem B948091 : Blo 558808 948091 := bstep (se 1 (by rfl) ⟨711068, by rfl⟩ : syracuseStep 948091 = 1422137) B1422137
theorem B6060109 : Blo 558808 6060109 := bstep (se 3 (by rfl) ⟨1136270, by rfl⟩ : syracuseStep 6060109 = 2272541) B2272541
theorem B1013897 : Blo 558808 1013897 := bstep (se 2 (by rfl) ⟨380211, by rfl⟩ : syracuseStep 1013897 = 760423) B760423
theorem B1800407 : Blo 558808 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B1899179 : Blo 558808 1899179 := bstep (se 1 (by rfl) ⟨1424384, by rfl⟩ : syracuseStep 1899179 = 2848769) B2848769
theorem B1080481 : Blo 558808 1080481 := bstep (se 2 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 1080481 = 810361) B810361
theorem B6388955 : Blo 558808 6388955 := bstep (se 1 (by rfl) ⟨4791716, by rfl⟩ : syracuseStep 6388955 = 9583433) B9583433
theorem B1277191 : Blo 558808 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B2686715 : Blo 558808 2686715 := bstep (se 1 (by rfl) ⟨2015036, by rfl⟩ : syracuseStep 2686715 = 4030073) B4030073
theorem B6062273 : Blo 558808 6062273 := bstep (se 2 (by rfl) ⟨2273352, by rfl⟩ : syracuseStep 6062273 = 4546705) B4546705
theorem B2392715 : Blo 558808 2392715 := bstep (se 1 (by rfl) ⟨1794536, by rfl⟩ : syracuseStep 2392715 = 3589073) B3589073
theorem B2393057 : Blo 558808 2393057 := bstep (se 2 (by rfl) ⟨897396, by rfl⟩ : syracuseStep 2393057 = 1794793) B1794793
theorem B5375767 : Blo 558808 5375767 := bstep (se 1 (by rfl) ⟨4031825, by rfl⟩ : syracuseStep 5375767 = 8063651) B8063651
theorem B558975 : Blo 558808 558975 := bstep (se 1 (by rfl) ⟨419231, by rfl⟩ : syracuseStep 558975 = 838463) B838463
theorem B4786249 : Blo 558808 4786249 := bstep (se 2 (by rfl) ⟨1794843, by rfl⟩ : syracuseStep 4786249 = 3589687) B3589687
theorem B559195 : Blo 558808 559195 := bstep (se 1 (by rfl) ⟨419396, by rfl⟩ : syracuseStep 559195 = 838793) B838793
theorem B559231 : Blo 558808 559231 := bstep (se 1 (by rfl) ⟨419423, by rfl⟩ : syracuseStep 559231 = 838847) B838847
theorem B559423 : Blo 558808 559423 := bstep (se 1 (by rfl) ⟨419567, by rfl⟩ : syracuseStep 559423 = 839135) B839135
theorem B559463 : Blo 558808 559463 := bstep (se 1 (by rfl) ⟨419597, by rfl⟩ : syracuseStep 559463 = 839195) B839195
theorem B559743 : Blo 558808 559743 := bstep (se 1 (by rfl) ⟨419807, by rfl⟩ : syracuseStep 559743 = 839615) B839615
theorem B5770025 : Blo 558808 5770025 := bstep (se 2 (by rfl) ⟨2163759, by rfl⟩ : syracuseStep 5770025 = 4327519) B4327519
theorem B1346825 : Blo 558808 1346825 := bstep (se 2 (by rfl) ⟨505059, by rfl⟩ : syracuseStep 1346825 = 1010119) B1010119
theorem B3248039 : Blo 558808 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B1708457 : Blo 558808 1708457 := bstep (se 2 (by rfl) ⟨640671, by rfl⟩ : syracuseStep 1708457 = 1281343) B1281343
theorem B2691575 : Blo 558808 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B7180811 : Blo 558808 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B561691 : Blo 558808 561691 := bstep (se 1 (by rfl) ⟨421268, by rfl⟩ : syracuseStep 561691 = 842537) B842537
theorem B562047 : Blo 558808 562047 := bstep (se 1 (by rfl) ⟨421535, by rfl⟩ : syracuseStep 562047 = 843071) B843071
theorem B562267 : Blo 558808 562267 := bstep (se 1 (by rfl) ⟨421700, by rfl⟩ : syracuseStep 562267 = 843401) B843401
theorem B562735 : Blo 558808 562735 := bstep (se 1 (by rfl) ⟨422051, by rfl⟩ : syracuseStep 562735 = 844103) B844103
theorem B562791 : Blo 558808 562791 := bstep (se 1 (by rfl) ⟨422093, by rfl⟩ : syracuseStep 562791 = 844187) B844187
theorem B4265801 : Blo 558808 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B628735 : Blo 558808 628735 := bstep (se 1 (by rfl) ⟨471551, by rfl⟩ : syracuseStep 628735 = 943103) B943103
theorem B1415657 : Blo 558808 1415657 := bstep (se 2 (by rfl) ⟨530871, by rfl⟩ : syracuseStep 1415657 = 1061743) B1061743
theorem B629455 : Blo 558808 629455 := bstep (se 1 (by rfl) ⟨472091, by rfl⟩ : syracuseStep 629455 = 944183) B944183
theorem B3022055 : Blo 558808 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B630319 : Blo 558808 630319 := bstep (se 1 (by rfl) ⟨472739, by rfl⟩ : syracuseStep 630319 = 945479) B945479
theorem B1416811 : Blo 558808 1416811 := bstep (se 1 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 1416811 = 2125217) B2125217
theorem B630427 : Blo 558808 630427 := bstep (se 1 (by rfl) ⟨472820, by rfl⟩ : syracuseStep 630427 = 945641) B945641
theorem B630463 : Blo 558808 630463 := bstep (se 1 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 630463 = 945695) B945695
theorem B249077551 : Blo 558808 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B1516087 : Blo 558808 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B12165713 : Blo 558808 12165713 := bstep (se 2 (by rfl) ⟨4562142, by rfl⟩ : syracuseStep 12165713 = 9124285) B9124285
theorem B1417895 : Blo 558808 1417895 := bstep (se 1 (by rfl) ⟨1063421, by rfl⟩ : syracuseStep 1417895 = 2126843) B2126843
theorem B1418249 : Blo 558808 1418249 := bstep (se 2 (by rfl) ⟨531843, by rfl⟩ : syracuseStep 1418249 = 1063687) B1063687
theorem B12922163 : Blo 558808 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B2731495 : Blo 558808 2731495 := bstep (se 1 (by rfl) ⟨2048621, by rfl⟩ : syracuseStep 2731495 = 4097243) B4097243
theorem B798187 : Blo 558808 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B1420841 : Blo 558808 1420841 := bstep (se 2 (by rfl) ⟨532815, by rfl⟩ : syracuseStep 1420841 = 1065631) B1065631
theorem B798751 : Blo 558808 798751 := bstep (se 1 (by rfl) ⟨599063, by rfl⟩ : syracuseStep 798751 = 1198127) B1198127
theorem B1062047 : Blo 558808 1062047 := bstep (se 1 (by rfl) ⟨796535, by rfl⟩ : syracuseStep 1062047 = 1593071) B1593071
theorem B1258991 : Blo 558808 1258991 := bstep (se 1 (by rfl) ⟨944243, by rfl⟩ : syracuseStep 1258991 = 1888487) B1888487
theorem B1423079 : Blo 558808 1423079 := bstep (se 1 (by rfl) ⟨1067309, by rfl⟩ : syracuseStep 1423079 = 2134619) B2134619
theorem B1423615 : Blo 558808 1423615 := bstep (se 1 (by rfl) ⟨1067711, by rfl⟩ : syracuseStep 1423615 = 2135423) B2135423
theorem B1423777 : Blo 558808 1423777 := bstep (se 2 (by rfl) ⟨533916, by rfl⟩ : syracuseStep 1423777 = 1067833) B1067833
theorem B1259963 : Blo 558808 1259963 := bstep (se 1 (by rfl) ⟨944972, by rfl⟩ : syracuseStep 1259963 = 1889945) B1889945
theorem B1260143 : Blo 558808 1260143 := bstep (se 1 (by rfl) ⟨945107, by rfl⟩ : syracuseStep 1260143 = 1890215) B1890215
theorem B3587075 : Blo 558808 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B10796125 : Blo 558808 10796125 := bstep (se 3 (by rfl) ⟨2024273, by rfl⟩ : syracuseStep 10796125 = 4048547) B4048547
theorem B6831641 : Blo 558808 6831641 := bstep (se 2 (by rfl) ⟨2561865, by rfl⟩ : syracuseStep 6831641 = 5123731) B5123731
theorem B1261403 : Blo 558808 1261403 := bstep (se 1 (by rfl) ⟨946052, by rfl⟩ : syracuseStep 1261403 = 1892105) B1892105
theorem B49299457 : Blo 558808 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B6045839 : Blo 558808 6045839 := bstep (se 1 (by rfl) ⟨4534379, by rfl⟩ : syracuseStep 6045839 = 9068759) B9068759
theorem B2703725 : Blo 558808 2703725 := bstep (se 3 (by rfl) ⟨506948, by rfl⟩ : syracuseStep 2703725 = 1013897) B1013897
theorem B1261961 : Blo 558808 1261961 := bstep (se 2 (by rfl) ⟨473235, by rfl⟩ : syracuseStep 1261961 = 946471) B946471
theorem B10371665 : Blo 558808 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B1262663 : Blo 558808 1262663 := bstep (se 1 (by rfl) ⟨946997, by rfl⟩ : syracuseStep 1262663 = 1893995) B1893995
theorem B1262951 : Blo 558808 1262951 := bstep (se 1 (by rfl) ⟨947213, by rfl⟩ : syracuseStep 1262951 = 1894427) B1894427
theorem B21611933 : Blo 558808 21611933 := bstep (se 3 (by rfl) ⟨4052237, by rfl⟩ : syracuseStep 21611933 = 8104475) B8104475
theorem B6473171 : Blo 558808 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B4540315 : Blo 558808 4540315 := bstep (se 1 (by rfl) ⟨3405236, by rfl⟩ : syracuseStep 4540315 = 6810473) B6810473
theorem B1886111 : Blo 558808 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B5130155 : Blo 558808 5130155 := bstep (se 1 (by rfl) ⟨3847616, by rfl⟩ : syracuseStep 5130155 = 7695233) B7695233
theorem B1264121 : Blo 558808 1264121 := bstep (se 2 (by rfl) ⟨474045, by rfl⟩ : syracuseStep 1264121 = 948091) B948091
theorem B1264283 : Blo 558808 1264283 := bstep (se 1 (by rfl) ⟨948212, by rfl⟩ : syracuseStep 1264283 = 1896425) B1896425
theorem B1264319 : Blo 558808 1264319 := bstep (se 1 (by rfl) ⟨948239, by rfl⟩ : syracuseStep 1264319 = 1896479) B1896479
theorem B8080145 : Blo 558808 8080145 := bstep (se 2 (by rfl) ⟨3030054, by rfl⟩ : syracuseStep 8080145 = 6060109) B6060109
theorem B838523 : Blo 558808 838523 := bstep (se 1 (by rfl) ⟨628892, by rfl⟩ : syracuseStep 838523 = 1257785) B1257785
theorem B838655 : Blo 558808 838655 := bstep (se 1 (by rfl) ⟨628991, by rfl⟩ : syracuseStep 838655 = 1257983) B1257983
theorem B1264751 : Blo 558808 1264751 := bstep (se 1 (by rfl) ⟨948563, by rfl⟩ : syracuseStep 1264751 = 1897127) B1897127
theorem B1264823 : Blo 558808 1264823 := bstep (se 1 (by rfl) ⟨948617, by rfl⟩ : syracuseStep 1264823 = 1897235) B1897235
theorem B1265399 : Blo 558808 1265399 := bstep (se 1 (by rfl) ⟨949049, by rfl⟩ : syracuseStep 1265399 = 1898099) B1898099
theorem B839657 : Blo 558808 839657 := bstep (se 2 (by rfl) ⟨314871, by rfl⟩ : syracuseStep 839657 = 629743) B629743
theorem B839711 : Blo 558808 839711 := bstep (se 1 (by rfl) ⟨629783, by rfl⟩ : syracuseStep 839711 = 1259567) B1259567
theorem B708679 : Blo 558808 708679 := bstep (se 1 (by rfl) ⟨531509, by rfl⟩ : syracuseStep 708679 = 1063019) B1063019
theorem B1200271 : Blo 558808 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B1888703 : Blo 558808 1888703 := bstep (se 1 (by rfl) ⟨1416527, by rfl⟩ : syracuseStep 1888703 = 2833055) B2833055
theorem B1266119 : Blo 558808 1266119 := bstep (se 1 (by rfl) ⟨949589, by rfl⟩ : syracuseStep 1266119 = 1899179) B1899179
theorem B840191 : Blo 558808 840191 := bstep (se 1 (by rfl) ⟨630143, by rfl⟩ : syracuseStep 840191 = 1260287) B1260287
theorem B840503 : Blo 558808 840503 := bstep (se 1 (by rfl) ⟨630377, by rfl⟩ : syracuseStep 840503 = 1260755) B1260755
theorem B1791143 : Blo 558808 1791143 := bstep (se 1 (by rfl) ⟨1343357, by rfl⟩ : syracuseStep 1791143 = 2686715) B2686715
theorem B3037103 : Blo 558808 3037103 := bstep (se 1 (by rfl) ⟨2277827, by rfl⟩ : syracuseStep 3037103 = 4555655) B4555655
theorem B841835 : Blo 558808 841835 := bstep (se 1 (by rfl) ⟨631376, by rfl⟩ : syracuseStep 841835 = 1262753) B1262753
theorem B841895 : Blo 558808 841895 := bstep (se 1 (by rfl) ⟨631421, by rfl⟩ : syracuseStep 841895 = 1262843) B1262843
theorem B842039 : Blo 558808 842039 := bstep (se 1 (by rfl) ⟨631529, by rfl⟩ : syracuseStep 842039 = 1263059) B1263059
theorem B842063 : Blo 558808 842063 := bstep (se 1 (by rfl) ⟨631547, by rfl⟩ : syracuseStep 842063 = 1263095) B1263095
theorem B10541431 : Blo 558808 10541431 := bstep (se 1 (by rfl) ⟨7906073, by rfl⟩ : syracuseStep 10541431 = 15812147) B15812147
theorem B1595987 : Blo 558808 1595987 := bstep (se 1 (by rfl) ⟨1196990, by rfl⟩ : syracuseStep 1595987 = 2393981) B2393981
theorem B842351 : Blo 558808 842351 := bstep (se 1 (by rfl) ⟨631763, by rfl⟩ : syracuseStep 842351 = 1263527) B1263527
theorem B1890971 : Blo 558808 1890971 := bstep (se 1 (by rfl) ⟨1418228, by rfl⟩ : syracuseStep 1890971 = 2836457) B2836457
theorem B842783 : Blo 558808 842783 := bstep (se 1 (by rfl) ⟨632087, by rfl⟩ : syracuseStep 842783 = 1264175) B1264175
theorem B3464329 : Blo 558808 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B842927 : Blo 558808 842927 := bstep (se 1 (by rfl) ⟨632195, by rfl⟩ : syracuseStep 842927 = 1264391) B1264391
theorem B1597103 : Blo 558808 1597103 := bstep (se 1 (by rfl) ⟨1197827, by rfl⟩ : syracuseStep 1597103 = 2395655) B2395655
theorem B1793819 : Blo 558808 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B843611 : Blo 558808 843611 := bstep (se 1 (by rfl) ⟨632708, by rfl⟩ : syracuseStep 843611 = 1265417) B1265417
theorem B843647 : Blo 558808 843647 := bstep (se 1 (by rfl) ⟨632735, by rfl⟩ : syracuseStep 843647 = 1265471) B1265471
theorem B30629825 : Blo 558808 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B49242629 : Blo 558808 49242629 := bstep (se 4 (by rfl) ⟨4616496, by rfl⟩ : syracuseStep 49242629 = 9232993) B9232993
theorem B2122271 : Blo 558808 2122271 := bstep (se 1 (by rfl) ⟨1591703, by rfl⟩ : syracuseStep 2122271 = 3183407) B3183407
theorem B1795049 : Blo 558808 1795049 := bstep (se 2 (by rfl) ⟨673143, by rfl⟩ : syracuseStep 1795049 = 1346287) B1346287
theorem B1893563 : Blo 558808 1893563 := bstep (se 1 (by rfl) ⟨1420172, by rfl⟩ : syracuseStep 1893563 = 2840345) B2840345
theorem B1598687 : Blo 558808 1598687 := bstep (se 1 (by rfl) ⟨1199015, by rfl⟩ : syracuseStep 1598687 = 2398031) B2398031
theorem B6383123 : Blo 558808 6383123 := bstep (se 1 (by rfl) ⟨4787342, by rfl⟩ : syracuseStep 6383123 = 9574685) B9574685
theorem B2123455 : Blo 558808 2123455 := bstep (se 1 (by rfl) ⟨1592591, by rfl⟩ : syracuseStep 2123455 = 3185183) B3185183
theorem B3598607 : Blo 558808 3598607 := bstep (se 1 (by rfl) ⟨2698955, by rfl⟩ : syracuseStep 3598607 = 5397911) B5397911
theorem B1601021 : Blo 558808 1601021 := bstep (se 3 (by rfl) ⟨300191, by rfl⟩ : syracuseStep 1601021 = 600383) B600383
theorem B1896155 : Blo 558808 1896155 := bstep (se 1 (by rfl) ⟨1422116, by rfl⟩ : syracuseStep 1896155 = 2844233) B2844233
theorem B1896317 : Blo 558808 1896317 := bstep (se 3 (by rfl) ⟨355559, by rfl⟩ : syracuseStep 1896317 = 711119) B711119
theorem B6811685 : Blo 558808 6811685 := bstep (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) B1277191
theorem B1601819 : Blo 558808 1601819 := bstep (se 1 (by rfl) ⟨1201364, by rfl⟩ : syracuseStep 1601819 = 2402729) B2402729
theorem B2126159 : Blo 558808 2126159 := bstep (se 1 (by rfl) ⟨1594619, by rfl⟩ : syracuseStep 2126159 = 3189239) B3189239
theorem B1536425 : Blo 558808 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B946687 : Blo 558808 946687 := bstep (se 1 (by rfl) ⟨710015, by rfl⟩ : syracuseStep 946687 = 1420031) B1420031
theorem B2388649 : Blo 558808 2388649 := bstep (se 2 (by rfl) ⟨895743, by rfl⟩ : syracuseStep 2388649 = 1791487) B1791487
theorem B9106121 : Blo 558808 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B3240929 : Blo 558808 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B947423 : Blo 558808 947423 := bstep (se 1 (by rfl) ⟨710567, by rfl⟩ : syracuseStep 947423 = 1421135) B1421135
theorem B13629019 : Blo 558808 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B1440641 : Blo 558808 1440641 := bstep (se 2 (by rfl) ⟨540240, by rfl⟩ : syracuseStep 1440641 = 1080481) B1080481
theorem B949279 : Blo 558808 949279 := bstep (se 1 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 949279 = 1423919) B1423919
theorem B4259303 : Blo 558808 4259303 := bstep (se 1 (by rfl) ⟨3194477, by rfl⟩ : syracuseStep 4259303 = 6388955) B6388955
theorem B65732609 : Blo 558808 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B4030559 : Blo 558808 4030559 := bstep (se 1 (by rfl) ⟨3022919, by rfl⟩ : syracuseStep 4030559 = 6045839) B6045839
theorem B1802483 : Blo 558808 1802483 := bstep (se 1 (by rfl) ⟨1351862, by rfl⟩ : syracuseStep 1802483 = 2703725) B2703725
theorem B6914443 : Blo 558808 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B559015 : Blo 558808 559015 := bstep (se 1 (by rfl) ⟨419261, by rfl⟩ : syracuseStep 559015 = 838523) B838523
theorem B559103 : Blo 558808 559103 := bstep (se 1 (by rfl) ⟨419327, by rfl⟩ : syracuseStep 559103 = 838655) B838655
theorem B559771 : Blo 558808 559771 := bstep (se 1 (by rfl) ⟨419828, by rfl⟩ : syracuseStep 559771 = 839657) B839657
theorem B559807 : Blo 558808 559807 := bstep (se 1 (by rfl) ⟨419855, by rfl⟩ : syracuseStep 559807 = 839711) B839711
theorem B560127 : Blo 558808 560127 := bstep (se 1 (by rfl) ⟨420095, by rfl⟩ : syracuseStep 560127 = 840191) B840191
theorem B4787207 : Blo 558808 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B560335 : Blo 558808 560335 := bstep (se 1 (by rfl) ⟨420251, by rfl⟩ : syracuseStep 560335 = 840503) B840503
theorem B561223 : Blo 558808 561223 := bstep (se 1 (by rfl) ⟨420917, by rfl⟩ : syracuseStep 561223 = 841835) B841835
theorem B561263 : Blo 558808 561263 := bstep (se 1 (by rfl) ⟨420947, by rfl⟩ : syracuseStep 561263 = 841895) B841895
theorem B561359 : Blo 558808 561359 := bstep (se 1 (by rfl) ⟨421019, by rfl⟩ : syracuseStep 561359 = 842039) B842039
theorem B561375 : Blo 558808 561375 := bstep (se 1 (by rfl) ⟨421031, by rfl⟩ : syracuseStep 561375 = 842063) B842063
theorem B561567 : Blo 558808 561567 := bstep (se 1 (by rfl) ⟨421175, by rfl⟩ : syracuseStep 561567 = 842351) B842351
theorem B18223541 : Blo 558808 18223541 := bstep (se 5 (by rfl) ⟨854228, by rfl⟩ : syracuseStep 18223541 = 1708457) B1708457
theorem B3641993 : Blo 558808 3641993 := bstep (se 2 (by rfl) ⟨1365747, by rfl⟩ : syracuseStep 3641993 = 2731495) B2731495
theorem B561855 : Blo 558808 561855 := bstep (se 1 (by rfl) ⟨421391, by rfl⟩ : syracuseStep 561855 = 842783) B842783
theorem B561951 : Blo 558808 561951 := bstep (se 1 (by rfl) ⟨421463, by rfl⟩ : syracuseStep 561951 = 842927) B842927
theorem B562407 : Blo 558808 562407 := bstep (se 1 (by rfl) ⟨421805, by rfl⟩ : syracuseStep 562407 = 843611) B843611
theorem B562431 : Blo 558808 562431 := bstep (se 1 (by rfl) ⟨421823, by rfl⟩ : syracuseStep 562431 = 843647) B843647
theorem B20419883 : Blo 558808 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B1414847 : Blo 558808 1414847 := bstep (se 1 (by rfl) ⟨1061135, by rfl⟩ : syracuseStep 1414847 = 2122271) B2122271
theorem B3184865 : Blo 558808 3184865 := bstep (se 2 (by rfl) ⟨1194324, by rfl⟩ : syracuseStep 3184865 = 2388649) B2388649
theorem B2399071 : Blo 558808 2399071 := bstep (se 1 (by rfl) ⟨1799303, by rfl⟩ : syracuseStep 2399071 = 3598607) B3598607
theorem B1417439 : Blo 558808 1417439 := bstep (se 1 (by rfl) ⟨1063079, by rfl⟩ : syracuseStep 1417439 = 2126159) B2126159
theorem B1024283 : Blo 558808 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B6070747 : Blo 558808 6070747 := bstep (se 1 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 6070747 = 9106121) B9106121
theorem B631615 : Blo 558808 631615 := bstep (se 1 (by rfl) ⟨473711, by rfl⟩ : syracuseStep 631615 = 947423) B947423
theorem B14394833 : Blo 558808 14394833 := bstep (se 2 (by rfl) ⟨5398062, by rfl⟩ : syracuseStep 14394833 = 10796125) B10796125
theorem B960427 : Blo 558808 960427 := bstep (se 1 (by rfl) ⟨720320, by rfl⟩ : syracuseStep 960427 = 1440641) B1440641
theorem B8661437 : Blo 558808 8661437 := bstep (se 3 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 8661437 = 3248039) B3248039
theorem B4041515 : Blo 558808 4041515 := bstep (se 1 (by rfl) ⟨3031136, by rfl⟩ : syracuseStep 4041515 = 6062273) B6062273
theorem B1257407 : Blo 558808 1257407 := bstep (se 1 (by rfl) ⟨943055, by rfl⟩ : syracuseStep 1257407 = 1886111) B1886111
theorem B3420103 : Blo 558808 3420103 := bstep (se 1 (by rfl) ⟨2565077, by rfl⟩ : syracuseStep 3420103 = 5130155) B5130155
theorem B5386763 : Blo 558808 5386763 := bstep (se 1 (by rfl) ⟨4040072, by rfl⟩ : syracuseStep 5386763 = 8080145) B8080145
theorem B3846683 : Blo 558808 3846683 := bstep (se 1 (by rfl) ⟨2885012, by rfl⟩ : syracuseStep 3846683 = 5770025) B5770025
theorem B2831273 : Blo 558808 2831273 := bstep (se 2 (by rfl) ⟨1061727, by rfl⟩ : syracuseStep 2831273 = 2123455) B2123455
theorem B1259135 : Blo 558808 1259135 := bstep (se 1 (by rfl) ⟨944351, by rfl⟩ : syracuseStep 1259135 = 1888703) B1888703
theorem B1194095 : Blo 558808 1194095 := bstep (se 1 (by rfl) ⟨895571, by rfl⟩ : syracuseStep 1194095 = 1791143) B1791143
theorem B1063991 : Blo 558808 1063991 := bstep (se 1 (by rfl) ⟨797993, by rfl⟩ : syracuseStep 1063991 = 1595987) B1595987
theorem B1260647 : Blo 558808 1260647 := bstep (se 1 (by rfl) ⟨945485, by rfl⟩ : syracuseStep 1260647 = 1890971) B1890971
theorem B1064249 : Blo 558808 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B2014703 : Blo 558808 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B1064735 : Blo 558808 1064735 := bstep (se 1 (by rfl) ⟨798551, by rfl⟩ : syracuseStep 1064735 = 1597103) B1597103
theorem B1195879 : Blo 558808 1195879 := bstep (se 1 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 1195879 = 1793819) B1793819
theorem B1065001 : Blo 558808 1065001 := bstep (se 2 (by rfl) ⟨399375, by rfl⟩ : syracuseStep 1065001 = 798751) B798751
theorem B8110475 : Blo 558808 8110475 := bstep (se 1 (by rfl) ⟨6082856, by rfl⟩ : syracuseStep 8110475 = 12165713) B12165713
theorem B1196699 : Blo 558808 1196699 := bstep (se 1 (by rfl) ⟨897524, by rfl⟩ : syracuseStep 1196699 = 1795049) B1795049
theorem B1262249 : Blo 558808 1262249 := bstep (se 2 (by rfl) ⟨473343, by rfl⟩ : syracuseStep 1262249 = 946687) B946687
theorem B1262375 : Blo 558808 1262375 := bstep (se 1 (by rfl) ⟨946781, by rfl⟩ : syracuseStep 1262375 = 1893563) B1893563
theorem B1065791 : Blo 558808 1065791 := bstep (se 1 (by rfl) ⟨799343, by rfl⟩ : syracuseStep 1065791 = 1598687) B1598687
theorem B18172025 : Blo 558808 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B1067347 : Blo 558808 1067347 := bstep (se 1 (by rfl) ⟨800510, by rfl⟩ : syracuseStep 1067347 = 1601021) B1601021
theorem B1264103 : Blo 558808 1264103 := bstep (se 1 (by rfl) ⟨948077, by rfl⟩ : syracuseStep 1264103 = 1896155) B1896155
theorem B1264211 : Blo 558808 1264211 := bstep (se 1 (by rfl) ⟨948158, by rfl⟩ : syracuseStep 1264211 = 1896317) B1896317
theorem B838313 : Blo 558808 838313 := bstep (se 2 (by rfl) ⟨314367, by rfl⟩ : syracuseStep 838313 = 628735) B628735
theorem B4541123 : Blo 558808 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B1067879 : Blo 558808 1067879 := bstep (se 1 (by rfl) ⟨800909, by rfl⟩ : syracuseStep 1067879 = 1601819) B1601819
theorem B3591533 : Blo 558808 3591533 := bstep (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) B1346825
theorem B708031 : Blo 558808 708031 := bstep (se 1 (by rfl) ⟨531023, by rfl⟩ : syracuseStep 708031 = 1062047) B1062047
theorem B839273 : Blo 558808 839273 := bstep (se 2 (by rfl) ⟨314727, by rfl⟩ : syracuseStep 839273 = 629455) B629455
theorem B839327 : Blo 558808 839327 := bstep (se 1 (by rfl) ⟨629495, by rfl⟩ : syracuseStep 839327 = 1258991) B1258991
theorem B1265705 : Blo 558808 1265705 := bstep (se 2 (by rfl) ⟨474639, by rfl⟩ : syracuseStep 1265705 = 949279) B949279
theorem B839975 : Blo 558808 839975 := bstep (se 1 (by rfl) ⟨629981, by rfl⟩ : syracuseStep 839975 = 1259963) B1259963
theorem B840095 : Blo 558808 840095 := bstep (se 1 (by rfl) ⟨630071, by rfl⟩ : syracuseStep 840095 = 1260143) B1260143
theorem B840425 : Blo 558808 840425 := bstep (se 2 (by rfl) ⟨315159, by rfl⟩ : syracuseStep 840425 = 630319) B630319
theorem B1889081 : Blo 558808 1889081 := bstep (se 2 (by rfl) ⟨708405, by rfl⟩ : syracuseStep 1889081 = 1416811) B1416811
theorem B840569 : Blo 558808 840569 := bstep (se 2 (by rfl) ⟨315213, by rfl⟩ : syracuseStep 840569 = 630427) B630427
theorem B840617 : Blo 558808 840617 := bstep (se 2 (by rfl) ⟨315231, by rfl⟩ : syracuseStep 840617 = 630463) B630463
theorem B2839535 : Blo 558808 2839535 := bstep (se 1 (by rfl) ⟨2129651, by rfl⟩ : syracuseStep 2839535 = 4259303) B4259303
theorem B840935 : Blo 558808 840935 := bstep (se 1 (by rfl) ⟨630701, by rfl⟩ : syracuseStep 840935 = 1261403) B1261403
theorem B841307 : Blo 558808 841307 := bstep (se 1 (by rfl) ⟨630980, by rfl⟩ : syracuseStep 841307 = 1261961) B1261961
theorem B1595143 : Blo 558808 1595143 := bstep (se 1 (by rfl) ⟨1196357, by rfl⟩ : syracuseStep 1595143 = 2392715) B2392715
theorem B1595371 : Blo 558808 1595371 := bstep (se 1 (by rfl) ⟨1196528, by rfl⟩ : syracuseStep 1595371 = 2393057) B2393057
theorem B841775 : Blo 558808 841775 := bstep (se 1 (by rfl) ⟨631331, by rfl⟩ : syracuseStep 841775 = 1262663) B1262663
theorem B2021449 : Blo 558808 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B841967 : Blo 558808 841967 := bstep (se 1 (by rfl) ⟨631475, by rfl⟩ : syracuseStep 841967 = 1262951) B1262951
theorem B14407955 : Blo 558808 14407955 := bstep (se 1 (by rfl) ⟨10805966, by rfl⟩ : syracuseStep 14407955 = 21611933) B21611933
theorem B4315447 : Blo 558808 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B842747 : Blo 558808 842747 := bstep (se 1 (by rfl) ⟨632060, by rfl⟩ : syracuseStep 842747 = 1264121) B1264121
theorem B842855 : Blo 558808 842855 := bstep (se 1 (by rfl) ⟨632141, by rfl⟩ : syracuseStep 842855 = 1264283) B1264283
theorem B842879 : Blo 558808 842879 := bstep (se 1 (by rfl) ⟨632159, by rfl⟩ : syracuseStep 842879 = 1264319) B1264319
theorem B843167 : Blo 558808 843167 := bstep (se 1 (by rfl) ⟨632375, by rfl⟩ : syracuseStep 843167 = 1264751) B1264751
theorem B843215 : Blo 558808 843215 := bstep (se 1 (by rfl) ⟨632411, by rfl⟩ : syracuseStep 843215 = 1264823) B1264823
theorem B7167689 : Blo 558808 7167689 := bstep (se 2 (by rfl) ⟨2687883, by rfl⟩ : syracuseStep 7167689 = 5375767) B5375767
theorem B843599 : Blo 558808 843599 := bstep (se 1 (by rfl) ⟨632699, by rfl⟩ : syracuseStep 843599 = 1265399) B1265399
theorem B6053753 : Blo 558808 6053753 := bstep (se 2 (by rfl) ⟨2270157, by rfl⟩ : syracuseStep 6053753 = 4540315) B4540315
theorem B8642477 : Blo 558808 8642477 := bstep (se 3 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 8642477 = 3240929) B3240929
theorem B6381665 : Blo 558808 6381665 := bstep (se 2 (by rfl) ⟨2393124, by rfl⟩ : syracuseStep 6381665 = 4786249) B4786249
theorem B844079 : Blo 558808 844079 := bstep (se 1 (by rfl) ⟨633059, by rfl⟩ : syracuseStep 844079 = 1266119) B1266119
theorem B1794383 : Blo 558808 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B2843867 : Blo 558808 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B2024735 : Blo 558808 2024735 := bstep (se 1 (by rfl) ⟨1518551, by rfl⟩ : syracuseStep 2024735 = 3037103) B3037103
theorem B943771 : Blo 558808 943771 := bstep (se 1 (by rfl) ⟨707828, by rfl⟩ : syracuseStep 943771 = 1415657) B1415657
theorem B944905 : Blo 558808 944905 := bstep (se 2 (by rfl) ⟨354339, by rfl⟩ : syracuseStep 944905 = 708679) B708679
theorem B1600361 : Blo 558808 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B32828419 : Blo 558808 32828419 := bstep (se 1 (by rfl) ⟨24621314, by rfl⟩ : syracuseStep 32828419 = 49242629) B49242629
theorem B945263 : Blo 558808 945263 := bstep (se 1 (by rfl) ⟨708947, by rfl⟩ : syracuseStep 945263 = 1417895) B1417895
theorem B945499 : Blo 558808 945499 := bstep (se 1 (by rfl) ⟨709124, by rfl⟩ : syracuseStep 945499 = 1418249) B1418249
theorem B4255415 : Blo 558808 4255415 := bstep (se 1 (by rfl) ⟨3191561, by rfl⟩ : syracuseStep 4255415 = 6383123) B6383123
theorem B8614775 : Blo 558808 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B947227 : Blo 558808 947227 := bstep (se 1 (by rfl) ⟨710420, by rfl⟩ : syracuseStep 947227 = 1420841) B1420841
theorem B1898153 : Blo 558808 1898153 := bstep (se 2 (by rfl) ⟨711807, by rfl⟩ : syracuseStep 1898153 = 1423615) B1423615
theorem B14055241 : Blo 558808 14055241 := bstep (se 2 (by rfl) ⟨5270715, by rfl⟩ : syracuseStep 14055241 = 10541431) B10541431
theorem B1898369 : Blo 558808 1898369 := bstep (se 2 (by rfl) ⟨711888, by rfl⟩ : syracuseStep 1898369 = 1423777) B1423777
theorem B948719 : Blo 558808 948719 := bstep (se 1 (by rfl) ⟨711539, by rfl⟩ : syracuseStep 948719 = 1423079) B1423079
theorem B4619105 : Blo 558808 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B2391383 : Blo 558808 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B4554427 : Blo 558808 4554427 := bstep (se 1 (by rfl) ⟨3415820, by rfl⟩ : syracuseStep 4554427 = 6831641) B6831641
theorem B332103401 : Blo 558808 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B2687039 : Blo 558808 2687039 := bstep (se 1 (by rfl) ⟨2015279, by rfl⟩ : syracuseStep 2687039 = 4030559) B4030559
theorem B5406983 : Blo 558808 5406983 := bstep (se 1 (by rfl) ⟨4055237, by rfl⟩ : syracuseStep 5406983 = 8110475) B8110475
theorem B8094329 : Blo 558808 8094329 := bstep (se 2 (by rfl) ⟨3035373, by rfl⟩ : syracuseStep 8094329 = 6070747) B6070747
theorem B558875 : Blo 558808 558875 := bstep (se 1 (by rfl) ⟨419156, by rfl⟩ : syracuseStep 558875 = 838313) B838313
theorem B2394355 : Blo 558808 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B559515 : Blo 558808 559515 := bstep (se 1 (by rfl) ⟨419636, by rfl⟩ : syracuseStep 559515 = 839273) B839273
theorem B559551 : Blo 558808 559551 := bstep (se 1 (by rfl) ⟨419663, by rfl⟩ : syracuseStep 559551 = 839327) B839327
theorem B1280569 : Blo 558808 1280569 := bstep (se 2 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 1280569 = 960427) B960427
theorem B559983 : Blo 558808 559983 := bstep (se 1 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 559983 = 839975) B839975
theorem B560063 : Blo 558808 560063 := bstep (se 1 (by rfl) ⟨420047, by rfl⟩ : syracuseStep 560063 = 840095) B840095
theorem B2427995 : Blo 558808 2427995 := bstep (se 1 (by rfl) ⟨1820996, by rfl⟩ : syracuseStep 2427995 = 3641993) B3641993
theorem B560283 : Blo 558808 560283 := bstep (se 1 (by rfl) ⟨420212, by rfl⟩ : syracuseStep 560283 = 840425) B840425
theorem B560379 : Blo 558808 560379 := bstep (se 1 (by rfl) ⟨420284, by rfl⟩ : syracuseStep 560379 = 840569) B840569
theorem B560411 : Blo 558808 560411 := bstep (se 1 (by rfl) ⟨420308, by rfl⟩ : syracuseStep 560411 = 840617) B840617
theorem B560623 : Blo 558808 560623 := bstep (se 1 (by rfl) ⟨420467, by rfl⟩ : syracuseStep 560623 = 840935) B840935
theorem B560871 : Blo 558808 560871 := bstep (se 1 (by rfl) ⟨420653, by rfl⟩ : syracuseStep 560871 = 841307) B841307
theorem B561183 : Blo 558808 561183 := bstep (se 1 (by rfl) ⟨420887, by rfl⟩ : syracuseStep 561183 = 841775) B841775
theorem B561311 : Blo 558808 561311 := bstep (se 1 (by rfl) ⟨420983, by rfl⟩ : syracuseStep 561311 = 841967) B841967
theorem B9605303 : Blo 558808 9605303 := bstep (se 1 (by rfl) ⟨7203977, by rfl⟩ : syracuseStep 9605303 = 14407955) B14407955
theorem B561831 : Blo 558808 561831 := bstep (se 1 (by rfl) ⟨421373, by rfl⟩ : syracuseStep 561831 = 842747) B842747
theorem B561903 : Blo 558808 561903 := bstep (se 1 (by rfl) ⟨421427, by rfl⟩ : syracuseStep 561903 = 842855) B842855
theorem B561919 : Blo 558808 561919 := bstep (se 1 (by rfl) ⟨421439, by rfl⟩ : syracuseStep 561919 = 842879) B842879
theorem B562111 : Blo 558808 562111 := bstep (se 1 (by rfl) ⟨421583, by rfl⟩ : syracuseStep 562111 = 843167) B843167
theorem B562143 : Blo 558808 562143 := bstep (se 1 (by rfl) ⟨421607, by rfl⟩ : syracuseStep 562143 = 843215) B843215
theorem B562399 : Blo 558808 562399 := bstep (se 1 (by rfl) ⟨421799, by rfl⟩ : syracuseStep 562399 = 843599) B843599
theorem B4035835 : Blo 558808 4035835 := bstep (se 1 (by rfl) ⟨3026876, by rfl⟩ : syracuseStep 4035835 = 6053753) B6053753
theorem B4560137 : Blo 558808 4560137 := bstep (se 2 (by rfl) ⟨1710051, by rfl⟩ : syracuseStep 4560137 = 3420103) B3420103
theorem B175084901 : Blo 558808 175084901 := bstep (se 4 (by rfl) ⟨16414209, by rfl⟩ : syracuseStep 175084901 = 32828419) B32828419
theorem B562719 : Blo 558808 562719 := bstep (se 1 (by rfl) ⟨422039, by rfl⟩ : syracuseStep 562719 = 844079) B844079
theorem B5774291 : Blo 558808 5774291 := bstep (se 1 (by rfl) ⟨4330718, by rfl⟩ : syracuseStep 5774291 = 8661437) B8661437
theorem B2694343 : Blo 558808 2694343 := bstep (se 1 (by rfl) ⟨2020757, by rfl⟩ : syracuseStep 2694343 = 4041515) B4041515
theorem B630175 : Blo 558808 630175 := bstep (se 1 (by rfl) ⟨472631, by rfl⟩ : syracuseStep 630175 = 945263) B945263
theorem B2695265 : Blo 558808 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B2564455 : Blo 558808 2564455 := bstep (se 1 (by rfl) ⟨1923341, by rfl⟩ : syracuseStep 2564455 = 3846683) B3846683
theorem B5743183 : Blo 558808 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B796063 : Blo 558808 796063 := bstep (se 1 (by rfl) ⟨597047, by rfl⟩ : syracuseStep 796063 = 1194095) B1194095
theorem B632479 : Blo 558808 632479 := bstep (se 1 (by rfl) ⟨474359, by rfl⟩ : syracuseStep 632479 = 948719) B948719
theorem B6072569 : Blo 558808 6072569 := bstep (se 2 (by rfl) ⟨2277213, by rfl⟩ : syracuseStep 6072569 = 4554427) B4554427
theorem B43821739 : Blo 558808 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B1420001 : Blo 558808 1420001 := bstep (se 2 (by rfl) ⟨532500, by rfl⟩ : syracuseStep 1420001 = 1065001) B1065001
theorem B9219257 : Blo 558808 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B2731421 : Blo 558808 2731421 := bstep (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) B1024283
theorem B3191197 : Blo 558808 3191197 := bstep (se 3 (by rfl) ⟨598349, by rfl⟩ : syracuseStep 3191197 = 1196699) B1196699
theorem B3191471 : Blo 558808 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B1258361 : Blo 558808 1258361 := bstep (se 2 (by rfl) ⟨471885, by rfl⟩ : syracuseStep 1258361 = 943771) B943771
theorem B1423129 : Blo 558808 1423129 := bstep (se 2 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 1423129 = 1067347) B1067347
theorem B1259387 : Blo 558808 1259387 := bstep (se 1 (by rfl) ⟨944540, by rfl⟩ : syracuseStep 1259387 = 1889081) B1889081
theorem B7583645 : Blo 558808 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B13613255 : Blo 558808 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B1259873 : Blo 558808 1259873 := bstep (se 2 (by rfl) ⟨472452, by rfl⟩ : syracuseStep 1259873 = 944905) B944905
theorem B1260665 : Blo 558808 1260665 := bstep (se 2 (by rfl) ⟨472749, by rfl⟩ : syracuseStep 1260665 = 945499) B945499
theorem B1196255 : Blo 558808 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B1262969 : Blo 558808 1262969 := bstep (se 2 (by rfl) ⟨473613, by rfl⟩ : syracuseStep 1262969 = 947227) B947227
theorem B12109661 : Blo 558808 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B1066907 : Blo 558808 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B2836943 : Blo 558808 2836943 := bstep (se 1 (by rfl) ⟨2127707, by rfl⟩ : syracuseStep 2836943 = 4255415) B4255415
theorem B838271 : Blo 558808 838271 := bstep (se 1 (by rfl) ⟨628703, by rfl⟩ : syracuseStep 838271 = 1257407) B1257407
theorem B3591175 : Blo 558808 3591175 := bstep (se 1 (by rfl) ⟨2693381, by rfl⟩ : syracuseStep 3591175 = 5386763) B5386763
theorem B5753929 : Blo 558808 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B1887515 : Blo 558808 1887515 := bstep (se 1 (by rfl) ⟨1415636, by rfl⟩ : syracuseStep 1887515 = 2831273) B2831273
theorem B839423 : Blo 558808 839423 := bstep (se 1 (by rfl) ⟨629567, by rfl⟩ : syracuseStep 839423 = 1259135) B1259135
theorem B1265435 : Blo 558808 1265435 := bstep (se 1 (by rfl) ⟨949076, by rfl⟩ : syracuseStep 1265435 = 1898153) B1898153
theorem B3198761 : Blo 558808 3198761 := bstep (se 2 (by rfl) ⟨1199535, by rfl⟩ : syracuseStep 3198761 = 2399071) B2399071
theorem B1265579 : Blo 558808 1265579 := bstep (se 1 (by rfl) ⟨949184, by rfl⟩ : syracuseStep 1265579 = 1898369) B1898369
theorem B709327 : Blo 558808 709327 := bstep (se 1 (by rfl) ⟨531995, by rfl⟩ : syracuseStep 709327 = 1063991) B1063991
theorem B840431 : Blo 558808 840431 := bstep (se 1 (by rfl) ⟨630323, by rfl⟩ : syracuseStep 840431 = 1260647) B1260647
theorem B709499 : Blo 558808 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B1594255 : Blo 558808 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B1594505 : Blo 558808 1594505 := bstep (se 2 (by rfl) ⟨597939, by rfl⟩ : syracuseStep 1594505 = 1195879) B1195879
theorem B221402267 : Blo 558808 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B709823 : Blo 558808 709823 := bstep (se 1 (by rfl) ⟨532367, by rfl⟩ : syracuseStep 709823 = 1064735) B1064735
theorem B1201655 : Blo 558808 1201655 := bstep (se 1 (by rfl) ⟨901241, by rfl⟩ : syracuseStep 1201655 = 1802483) B1802483
theorem B841499 : Blo 558808 841499 := bstep (se 1 (by rfl) ⟨631124, by rfl⟩ : syracuseStep 841499 = 1262249) B1262249
theorem B841583 : Blo 558808 841583 := bstep (se 1 (by rfl) ⟨631187, by rfl⟩ : syracuseStep 841583 = 1262375) B1262375
theorem B710527 : Blo 558808 710527 := bstep (se 1 (by rfl) ⟨532895, by rfl⟩ : syracuseStep 710527 = 1065791) B1065791
theorem B842153 : Blo 558808 842153 := bstep (se 2 (by rfl) ⟨315807, by rfl⟩ : syracuseStep 842153 = 631615) B631615
theorem B12114683 : Blo 558808 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B842735 : Blo 558808 842735 := bstep (se 1 (by rfl) ⟨632051, by rfl⟩ : syracuseStep 842735 = 1264103) B1264103
theorem B842807 : Blo 558808 842807 := bstep (se 1 (by rfl) ⟨632105, by rfl⟩ : syracuseStep 842807 = 1264211) B1264211
theorem B711919 : Blo 558808 711919 := bstep (se 1 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 711919 = 1067879) B1067879
theorem B843803 : Blo 558808 843803 := bstep (se 1 (by rfl) ⟨632852, by rfl⟩ : syracuseStep 843803 = 1265705) B1265705
theorem B12149027 : Blo 558808 12149027 := bstep (se 1 (by rfl) ⟨9111770, by rfl⟩ : syracuseStep 12149027 = 18223541) B18223541
theorem B1893023 : Blo 558808 1893023 := bstep (se 1 (by rfl) ⟨1419767, by rfl⟩ : syracuseStep 1893023 = 2839535) B2839535
theorem B5399293 : Blo 558808 5399293 := bstep (se 3 (by rfl) ⟨1012367, by rfl⟩ : syracuseStep 5399293 = 2024735) B2024735
theorem B943231 : Blo 558808 943231 := bstep (se 1 (by rfl) ⟨707423, by rfl⟩ : syracuseStep 943231 = 1414847) B1414847
theorem B2123243 : Blo 558808 2123243 := bstep (se 1 (by rfl) ⟨1592432, by rfl⟩ : syracuseStep 2123243 = 3184865) B3184865
theorem B944041 : Blo 558808 944041 := bstep (se 2 (by rfl) ⟨354015, by rfl⟩ : syracuseStep 944041 = 708031) B708031
theorem B4778459 : Blo 558808 4778459 := bstep (se 1 (by rfl) ⟨3583844, by rfl⟩ : syracuseStep 4778459 = 7167689) B7167689
theorem B5761651 : Blo 558808 5761651 := bstep (se 1 (by rfl) ⟨4321238, by rfl⟩ : syracuseStep 5761651 = 8642477) B8642477
theorem B4254443 : Blo 558808 4254443 := bstep (se 1 (by rfl) ⟨3190832, by rfl⟩ : syracuseStep 4254443 = 6381665) B6381665
theorem B944959 : Blo 558808 944959 := bstep (se 1 (by rfl) ⟨708719, by rfl⟩ : syracuseStep 944959 = 1417439) B1417439
theorem B9596555 : Blo 558808 9596555 := bstep (se 1 (by rfl) ⟨7197416, by rfl⟩ : syracuseStep 9596555 = 14394833) B14394833
theorem B2126857 : Blo 558808 2126857 := bstep (se 2 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 2126857 = 1595143) B1595143
theorem B18740321 : Blo 558808 18740321 := bstep (se 2 (by rfl) ⟨7027620, by rfl⟩ : syracuseStep 18740321 = 14055241) B14055241
theorem B2127161 : Blo 558808 2127161 := bstep (se 2 (by rfl) ⟨797685, by rfl⟩ : syracuseStep 2127161 = 1595371) B1595371
theorem B3079403 : Blo 558808 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B1343135 : Blo 558808 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B3604655 : Blo 558808 3604655 := bstep (se 1 (by rfl) ⟨2703491, by rfl⟩ : syracuseStep 3604655 = 5406983) B5406983
theorem B558847 : Blo 558808 558847 := bstep (se 1 (by rfl) ⟨419135, by rfl⟩ : syracuseStep 558847 = 838271) B838271
theorem B559615 : Blo 558808 559615 := bstep (se 1 (by rfl) ⟨419711, by rfl⟩ : syracuseStep 559615 = 839423) B839423
theorem B2132507 : Blo 558808 2132507 := bstep (se 1 (by rfl) ⟨1599380, by rfl⟩ : syracuseStep 2132507 = 3198761) B3198761
theorem B560287 : Blo 558808 560287 := bstep (se 1 (by rfl) ⟨420215, by rfl⟩ : syracuseStep 560287 = 840431) B840431
theorem B1707425 : Blo 558808 1707425 := bstep (se 2 (by rfl) ⟨640284, by rfl⟩ : syracuseStep 1707425 = 1280569) B1280569
theorem B58428985 : Blo 558808 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B116723267 : Blo 558808 116723267 := bstep (se 1 (by rfl) ⟨87542450, by rfl⟩ : syracuseStep 116723267 = 175084901) B175084901
theorem B560999 : Blo 558808 560999 := bstep (se 1 (by rfl) ⟨420749, by rfl⟩ : syracuseStep 560999 = 841499) B841499
theorem B561055 : Blo 558808 561055 := bstep (se 1 (by rfl) ⟨420791, by rfl⟩ : syracuseStep 561055 = 841583) B841583
theorem B4788233 : Blo 558808 4788233 := bstep (se 2 (by rfl) ⟨1795587, by rfl⟩ : syracuseStep 4788233 = 3591175) B3591175
theorem B7671905 : Blo 558808 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B561435 : Blo 558808 561435 := bstep (se 1 (by rfl) ⟨421076, by rfl⟩ : syracuseStep 561435 = 842153) B842153
theorem B561823 : Blo 558808 561823 := bstep (se 1 (by rfl) ⟨421367, by rfl⟩ : syracuseStep 561823 = 842735) B842735
theorem B561871 : Blo 558808 561871 := bstep (se 1 (by rfl) ⟨421403, by rfl⟩ : syracuseStep 561871 = 842807) B842807
theorem B20223053 : Blo 558808 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B562535 : Blo 558808 562535 := bstep (se 1 (by rfl) ⟨421901, by rfl⟩ : syracuseStep 562535 = 843803) B843803
theorem B8099351 : Blo 558808 8099351 := bstep (se 1 (by rfl) ⟨6074513, by rfl⟩ : syracuseStep 8099351 = 12149027) B12149027
theorem B1415495 : Blo 558808 1415495 := bstep (se 1 (by rfl) ⟨1061621, by rfl⟩ : syracuseStep 1415495 = 2123243) B2123243
theorem B3185639 : Blo 558808 3185639 := bstep (se 1 (by rfl) ⟨2389229, by rfl⟩ : syracuseStep 3185639 = 4778459) B4778459
theorem B5381113 : Blo 558808 5381113 := bstep (se 2 (by rfl) ⟨2017917, by rfl⟩ : syracuseStep 5381113 = 4035835) B4035835
theorem B6397703 : Blo 558808 6397703 := bstep (se 1 (by rfl) ⟨4798277, by rfl⟩ : syracuseStep 6397703 = 9596555) B9596555
theorem B12493547 : Blo 558808 12493547 := bstep (se 1 (by rfl) ⟨9370160, by rfl⟩ : syracuseStep 12493547 = 18740321) B18740321
theorem B1418107 : Blo 558808 1418107 := bstep (se 1 (by rfl) ⟨1063580, by rfl⟩ : syracuseStep 1418107 = 2127161) B2127161
theorem B7283789 : Blo 558808 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B895423 : Blo 558808 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B3419273 : Blo 558808 3419273 := bstep (se 2 (by rfl) ⟨1282227, by rfl⟩ : syracuseStep 3419273 = 2564455) B2564455
theorem B3190013 : Blo 558808 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B8073107 : Blo 558808 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B1257641 : Blo 558808 1257641 := bstep (se 2 (by rfl) ⟨471615, by rfl⟩ : syracuseStep 1257641 = 943231) B943231
theorem B1061417 : Blo 558808 1061417 := bstep (se 2 (by rfl) ⟨398031, by rfl⟩ : syracuseStep 1061417 = 796063) B796063
theorem B1618663 : Blo 558808 1618663 := bstep (se 1 (by rfl) ⟨1213997, by rfl⟩ : syracuseStep 1618663 = 2427995) B2427995
theorem B1258343 : Blo 558808 1258343 := bstep (se 1 (by rfl) ⟨943757, by rfl⟩ : syracuseStep 1258343 = 1887515) B1887515
theorem B1258721 : Blo 558808 1258721 := bstep (se 2 (by rfl) ⟨472020, by rfl⟩ : syracuseStep 1258721 = 944041) B944041
theorem B6403535 : Blo 558808 6403535 := bstep (se 1 (by rfl) ⟨4802651, by rfl⟩ : syracuseStep 6403535 = 9605303) B9605303
theorem B3192473 : Blo 558808 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B147601511 : Blo 558808 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B7682201 : Blo 558808 7682201 := bstep (se 2 (by rfl) ⟨2880825, by rfl⟩ : syracuseStep 7682201 = 5761651) B5761651
theorem B801103 : Blo 558808 801103 := bstep (se 1 (by rfl) ⟨600827, by rfl⟩ : syracuseStep 801103 = 1201655) B1201655
theorem B1259945 : Blo 558808 1259945 := bstep (se 2 (by rfl) ⟨472479, by rfl⟩ : syracuseStep 1259945 = 944959) B944959
theorem B8076455 : Blo 558808 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B3849527 : Blo 558808 3849527 := bstep (se 1 (by rfl) ⟨2887145, by rfl⟩ : syracuseStep 3849527 = 5774291) B5774291
theorem B1262015 : Blo 558808 1262015 := bstep (se 1 (by rfl) ⟨946511, by rfl⟩ : syracuseStep 1262015 = 1893023) B1893023
theorem B2835809 : Blo 558808 2835809 := bstep (se 2 (by rfl) ⟨1063428, by rfl⟩ : syracuseStep 2835809 = 2126857) B2126857
theorem B4048379 : Blo 558808 4048379 := bstep (se 1 (by rfl) ⟨3036284, by rfl⟩ : syracuseStep 4048379 = 6072569) B6072569
theorem B2836295 : Blo 558808 2836295 := bstep (se 1 (by rfl) ⟨2127221, by rfl⟩ : syracuseStep 2836295 = 4254443) B4254443
theorem B6146171 : Blo 558808 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B838907 : Blo 558808 838907 := bstep (se 1 (by rfl) ⟨629180, by rfl⟩ : syracuseStep 838907 = 1258361) B1258361
theorem B839591 : Blo 558808 839591 := bstep (se 1 (by rfl) ⟨629693, by rfl⟩ : syracuseStep 839591 = 1259387) B1259387
theorem B839915 : Blo 558808 839915 := bstep (se 1 (by rfl) ⟨629936, by rfl⟩ : syracuseStep 839915 = 1259873) B1259873
theorem B3592457 : Blo 558808 3592457 := bstep (se 2 (by rfl) ⟨1347171, by rfl⟩ : syracuseStep 3592457 = 2694343) B2694343
theorem B840233 : Blo 558808 840233 := bstep (se 2 (by rfl) ⟨315087, by rfl⟩ : syracuseStep 840233 = 630175) B630175
theorem B840443 : Blo 558808 840443 := bstep (se 1 (by rfl) ⟨630332, by rfl⟩ : syracuseStep 840443 = 1260665) B1260665
theorem B2052935 : Blo 558808 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B1791359 : Blo 558808 1791359 := bstep (se 1 (by rfl) ⟨1343519, by rfl⟩ : syracuseStep 1791359 = 2687039) B2687039
theorem B5396219 : Blo 558808 5396219 := bstep (se 1 (by rfl) ⟨4047164, by rfl⟩ : syracuseStep 5396219 = 8094329) B8094329
theorem B7657577 : Blo 558808 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B841979 : Blo 558808 841979 := bstep (se 1 (by rfl) ⟨631484, by rfl⟩ : syracuseStep 841979 = 1262969) B1262969
theorem B7199057 : Blo 558808 7199057 := bstep (se 2 (by rfl) ⟨2699646, by rfl⟩ : syracuseStep 7199057 = 5399293) B5399293
theorem B711271 : Blo 558808 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B1891295 : Blo 558808 1891295 := bstep (se 1 (by rfl) ⟨1418471, by rfl⟩ : syracuseStep 1891295 = 2836943) B2836943
theorem B843305 : Blo 558808 843305 := bstep (se 2 (by rfl) ⟨316239, by rfl⟩ : syracuseStep 843305 = 632479) B632479
theorem B1891997 : Blo 558808 1891997 := bstep (se 3 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 1891997 = 709499) B709499
theorem B843623 : Blo 558808 843623 := bstep (se 1 (by rfl) ⟨632717, by rfl⟩ : syracuseStep 843623 = 1265435) B1265435
theorem B843719 : Blo 558808 843719 := bstep (se 1 (by rfl) ⟨632789, by rfl⟩ : syracuseStep 843719 = 1265579) B1265579
theorem B4252013 : Blo 558808 4252013 := bstep (se 3 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 4252013 = 1594505) B1594505
theorem B1892861 : Blo 558808 1892861 := bstep (se 3 (by rfl) ⟨354911, by rfl⟩ : syracuseStep 1892861 = 709823) B709823
theorem B3040091 : Blo 558808 3040091 := bstep (se 1 (by rfl) ⟨2280068, by rfl⟩ : syracuseStep 3040091 = 4560137) B4560137
theorem B1796843 : Blo 558808 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B4254929 : Blo 558808 4254929 := bstep (se 2 (by rfl) ⟨1595598, by rfl⟩ : syracuseStep 4254929 = 3191197) B3191197
theorem B945769 : Blo 558808 945769 := bstep (se 2 (by rfl) ⟨354663, by rfl⟩ : syracuseStep 945769 = 709327) B709327
theorem B2125673 : Blo 558808 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B946667 : Blo 558808 946667 := bstep (se 1 (by rfl) ⟨710000, by rfl⟩ : syracuseStep 946667 = 1420001) B1420001
theorem B1897505 : Blo 558808 1897505 := bstep (se 2 (by rfl) ⟨711564, by rfl⟩ : syracuseStep 1897505 = 1423129) B1423129
theorem B947369 : Blo 558808 947369 := bstep (se 2 (by rfl) ⟨355263, by rfl⟩ : syracuseStep 947369 = 710527) B710527
theorem B2127647 : Blo 558808 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B9075503 : Blo 558808 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B949225 : Blo 558808 949225 := bstep (se 2 (by rfl) ⟨355959, by rfl⟩ : syracuseStep 949225 = 711919) B711919
theorem B4097447 : Blo 558808 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B559271 : Blo 558808 559271 := bstep (se 1 (by rfl) ⟨419453, by rfl⟩ : syracuseStep 559271 = 838907) B838907
theorem B559727 : Blo 558808 559727 := bstep (se 1 (by rfl) ⟨419795, by rfl⟩ : syracuseStep 559727 = 839591) B839591
theorem B5114603 : Blo 558808 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B559943 : Blo 558808 559943 := bstep (se 1 (by rfl) ⟨419957, by rfl⟩ : syracuseStep 559943 = 839915) B839915
theorem B2394971 : Blo 558808 2394971 := bstep (se 1 (by rfl) ⟨1796228, by rfl⟩ : syracuseStep 2394971 = 3592457) B3592457
theorem B560155 : Blo 558808 560155 := bstep (se 1 (by rfl) ⟨420116, by rfl⟩ : syracuseStep 560155 = 840233) B840233
theorem B560295 : Blo 558808 560295 := bstep (se 1 (by rfl) ⟨420221, by rfl⟩ : syracuseStep 560295 = 840443) B840443
theorem B561319 : Blo 558808 561319 := bstep (se 1 (by rfl) ⟨420989, by rfl⟩ : syracuseStep 561319 = 841979) B841979
theorem B562203 : Blo 558808 562203 := bstep (se 1 (by rfl) ⟨421652, by rfl⟩ : syracuseStep 562203 = 843305) B843305
theorem B4265135 : Blo 558808 4265135 := bstep (se 1 (by rfl) ⟨3198851, by rfl⟩ : syracuseStep 4265135 = 6397703) B6397703
theorem B562415 : Blo 558808 562415 := bstep (se 1 (by rfl) ⟨421811, by rfl⟩ : syracuseStep 562415 = 843623) B843623
theorem B562479 : Blo 558808 562479 := bstep (se 1 (by rfl) ⟨421859, by rfl⟩ : syracuseStep 562479 = 843719) B843719
theorem B8329031 : Blo 558808 8329031 := bstep (se 1 (by rfl) ⟨6246773, by rfl⟩ : syracuseStep 8329031 = 12493547) B12493547
theorem B4855859 : Blo 558808 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B4791581 : Blo 558808 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B1417115 : Blo 558808 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B5382071 : Blo 558808 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B631111 : Blo 558808 631111 := bstep (se 1 (by rfl) ⟨473333, by rfl⟩ : syracuseStep 631111 = 946667) B946667
theorem B631579 : Blo 558808 631579 := bstep (se 1 (by rfl) ⟨473684, by rfl⟩ : syracuseStep 631579 = 947369) B947369
theorem B4269023 : Blo 558808 4269023 := bstep (se 1 (by rfl) ⟨3201767, by rfl⟩ : syracuseStep 4269023 = 6403535) B6403535
theorem B1418431 : Blo 558808 1418431 := bstep (se 1 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 1418431 = 2127647) B2127647
theorem B5121467 : Blo 558808 5121467 := bstep (se 1 (by rfl) ⟨3841100, by rfl⟩ : syracuseStep 5121467 = 7682201) B7682201
theorem B5384303 : Blo 558808 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B2566351 : Blo 558808 2566351 := bstep (se 1 (by rfl) ⟨1924763, by rfl⟩ : syracuseStep 2566351 = 3849527) B3849527
theorem B2403103 : Blo 558808 2403103 := bstep (se 1 (by rfl) ⟨1802327, by rfl⟩ : syracuseStep 2403103 = 3604655) B3604655
theorem B2698919 : Blo 558808 2698919 := bstep (se 1 (by rfl) ⟨2024189, by rfl⟩ : syracuseStep 2698919 = 4048379) B4048379
theorem B1421671 : Blo 558808 1421671 := bstep (se 1 (by rfl) ⟨1066253, by rfl⟩ : syracuseStep 1421671 = 2132507) B2132507
theorem B3192155 : Blo 558808 3192155 := bstep (se 1 (by rfl) ⟨2394116, by rfl⟩ : syracuseStep 3192155 = 4788233) B4788233
theorem B1193897 : Blo 558808 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B13482035 : Blo 558808 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B1194239 : Blo 558808 1194239 := bstep (se 1 (by rfl) ⟨895679, by rfl⟩ : syracuseStep 1194239 = 1791359) B1791359
theorem B4799371 : Blo 558808 4799371 := bstep (se 1 (by rfl) ⟨3599528, by rfl⟩ : syracuseStep 4799371 = 7199057) B7199057
theorem B1260863 : Blo 558808 1260863 := bstep (se 1 (by rfl) ⟨945647, by rfl⟩ : syracuseStep 1260863 = 1891295) B1891295
theorem B77905313 : Blo 558808 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B1261025 : Blo 558808 1261025 := bstep (se 2 (by rfl) ⟨472884, by rfl⟩ : syracuseStep 1261025 = 945769) B945769
theorem B1261331 : Blo 558808 1261331 := bstep (se 1 (by rfl) ⟨945998, by rfl⟩ : syracuseStep 1261331 = 1891997) B1891997
theorem B2834675 : Blo 558808 2834675 := bstep (se 1 (by rfl) ⟨2126006, by rfl⟩ : syracuseStep 2834675 = 4252013) B4252013
theorem B1261907 : Blo 558808 1261907 := bstep (se 1 (by rfl) ⟨946430, by rfl⟩ : syracuseStep 1261907 = 1892861) B1892861
theorem B2279515 : Blo 558808 2279515 := bstep (se 1 (by rfl) ⟨1709636, by rfl⟩ : syracuseStep 2279515 = 3419273) B3419273
theorem B2836619 : Blo 558808 2836619 := bstep (se 1 (by rfl) ⟨2127464, by rfl⟩ : syracuseStep 2836619 = 4254929) B4254929
theorem B838427 : Blo 558808 838427 := bstep (se 1 (by rfl) ⟨628820, by rfl⟩ : syracuseStep 838427 = 1257641) B1257641
theorem B707611 : Blo 558808 707611 := bstep (se 1 (by rfl) ⟨530708, by rfl⟩ : syracuseStep 707611 = 1061417) B1061417
theorem B1068137 : Blo 558808 1068137 := bstep (se 2 (by rfl) ⟨400551, by rfl⟩ : syracuseStep 1068137 = 801103) B801103
theorem B838895 : Blo 558808 838895 := bstep (se 1 (by rfl) ⟨629171, by rfl⟩ : syracuseStep 838895 = 1258343) B1258343
theorem B1265003 : Blo 558808 1265003 := bstep (se 1 (by rfl) ⟨948752, by rfl⟩ : syracuseStep 1265003 = 1897505) B1897505
theorem B839147 : Blo 558808 839147 := bstep (se 1 (by rfl) ⟨629360, by rfl⟩ : syracuseStep 839147 = 1258721) B1258721
theorem B1265633 : Blo 558808 1265633 := bstep (se 2 (by rfl) ⟨474612, by rfl⟩ : syracuseStep 1265633 = 949225) B949225
theorem B839963 : Blo 558808 839963 := bstep (se 1 (by rfl) ⟨629972, by rfl⟩ : syracuseStep 839963 = 1259945) B1259945
theorem B6050335 : Blo 558808 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B841343 : Blo 558808 841343 := bstep (se 1 (by rfl) ⟨631007, by rfl⟩ : syracuseStep 841343 = 1262015) B1262015
theorem B1890539 : Blo 558808 1890539 := bstep (se 1 (by rfl) ⟨1417904, by rfl⟩ : syracuseStep 1890539 = 2835809) B2835809
theorem B1890809 : Blo 558808 1890809 := bstep (se 2 (by rfl) ⟨709053, by rfl⟩ : syracuseStep 1890809 = 1418107) B1418107
theorem B1890863 : Blo 558808 1890863 := bstep (se 1 (by rfl) ⟨1418147, by rfl⟩ : syracuseStep 1890863 = 2836295) B2836295
theorem B1138283 : Blo 558808 1138283 := bstep (se 1 (by rfl) ⟨853712, by rfl⟩ : syracuseStep 1138283 = 1707425) B1707425
theorem B77815511 : Blo 558808 77815511 := bstep (se 1 (by rfl) ⟨58361633, by rfl⟩ : syracuseStep 77815511 = 116723267) B116723267
theorem B1368623 : Blo 558808 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B5399567 : Blo 558808 5399567 := bstep (se 1 (by rfl) ⟨4049675, by rfl⟩ : syracuseStep 5399567 = 8099351) B8099351
theorem B3597479 : Blo 558808 3597479 := bstep (se 1 (by rfl) ⟨2698109, by rfl⟩ : syracuseStep 3597479 = 5396219) B5396219
theorem B5105051 : Blo 558808 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B943663 : Blo 558808 943663 := bstep (se 1 (by rfl) ⟨707747, by rfl⟩ : syracuseStep 943663 = 1415495) B1415495
theorem B2123759 : Blo 558808 2123759 := bstep (se 1 (by rfl) ⟨1592819, by rfl⟩ : syracuseStep 2123759 = 3185639) B3185639
theorem B2026727 : Blo 558808 2026727 := bstep (se 1 (by rfl) ⟨1520045, by rfl⟩ : syracuseStep 2026727 = 3040091) B3040091
theorem B2158217 : Blo 558808 2158217 := bstep (se 2 (by rfl) ⟨809331, by rfl⟩ : syracuseStep 2158217 = 1618663) B1618663
theorem B2126675 : Blo 558808 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B948361 : Blo 558808 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B2128315 : Blo 558808 2128315 := bstep (se 1 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 2128315 = 3192473) B3192473
theorem B7174817 : Blo 558808 7174817 := bstep (se 2 (by rfl) ⟨2690556, by rfl⟩ : syracuseStep 7174817 = 5381113) B5381113
theorem B98401007 : Blo 558808 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B3409735 : Blo 558808 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B558951 : Blo 558808 558951 := bstep (se 1 (by rfl) ⟨419213, by rfl⟩ : syracuseStep 558951 = 838427) B838427
theorem B559263 : Blo 558808 559263 := bstep (se 1 (by rfl) ⟨419447, by rfl⟩ : syracuseStep 559263 = 838895) B838895
theorem B559431 : Blo 558808 559431 := bstep (se 1 (by rfl) ⟨419573, by rfl⟩ : syracuseStep 559431 = 839147) B839147
theorem B559975 : Blo 558808 559975 := bstep (se 1 (by rfl) ⟨419981, by rfl⟩ : syracuseStep 559975 = 839963) B839963
theorem B560895 : Blo 558808 560895 := bstep (se 1 (by rfl) ⟨420671, by rfl⟩ : syracuseStep 560895 = 841343) B841343
theorem B758855 : Blo 558808 758855 := bstep (se 1 (by rfl) ⟨569141, by rfl⟩ : syracuseStep 758855 = 1138283) B1138283
theorem B3183725 : Blo 558808 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B51877007 : Blo 558808 51877007 := bstep (se 1 (by rfl) ⟨38907755, by rfl⟩ : syracuseStep 51877007 = 77815511) B77815511
theorem B8067113 : Blo 558808 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B2398319 : Blo 558808 2398319 := bstep (se 1 (by rfl) ⟨1798739, by rfl⟩ : syracuseStep 2398319 = 3597479) B3597479
theorem B3414311 : Blo 558808 3414311 := bstep (se 1 (by rfl) ⟨2560733, by rfl⟩ : syracuseStep 3414311 = 5121467) B5121467
theorem B1415839 : Blo 558808 1415839 := bstep (se 1 (by rfl) ⟨1061879, by rfl⟩ : syracuseStep 1415839 = 2123759) B2123759
theorem B1351151 : Blo 558808 1351151 := bstep (se 1 (by rfl) ⟨1013363, by rfl⟩ : syracuseStep 1351151 = 2026727) B2026727
theorem B1417783 : Blo 558808 1417783 := bstep (se 1 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 1417783 = 2126675) B2126675
theorem B6399161 : Blo 558808 6399161 := bstep (se 2 (by rfl) ⟨2399685, by rfl⟩ : syracuseStep 6399161 = 4799371) B4799371
theorem B8988023 : Blo 558808 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B796159 : Blo 558808 796159 := bstep (se 1 (by rfl) ⟨597119, by rfl⟩ : syracuseStep 796159 = 1194239) B1194239
theorem B1258217 : Blo 558808 1258217 := bstep (se 2 (by rfl) ⟨471831, by rfl⟩ : syracuseStep 1258217 = 943663) B943663
theorem B3421801 : Blo 558808 3421801 := bstep (se 2 (by rfl) ⟨1283175, by rfl⟩ : syracuseStep 3421801 = 2566351) B2566351
theorem B5552687 : Blo 558808 5552687 := bstep (se 1 (by rfl) ⟨4164515, by rfl⟩ : syracuseStep 5552687 = 8329031) B8329031
theorem B1260359 : Blo 558808 1260359 := bstep (se 1 (by rfl) ⟨945269, by rfl⟩ : syracuseStep 1260359 = 1890539) B1890539
theorem B1260539 : Blo 558808 1260539 := bstep (se 1 (by rfl) ⟨945404, by rfl⟩ : syracuseStep 1260539 = 1890809) B1890809
theorem B1260575 : Blo 558808 1260575 := bstep (se 1 (by rfl) ⟨945431, by rfl⟩ : syracuseStep 1260575 = 1890863) B1890863
theorem B3194387 : Blo 558808 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B3588047 : Blo 558808 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B3589535 : Blo 558808 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B1264481 : Blo 558808 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B2837753 : Blo 558808 2837753 := bstep (se 2 (by rfl) ⟨1064157, by rfl⟩ : syracuseStep 2837753 = 2128315) B2128315
theorem B840575 : Blo 558808 840575 := bstep (se 1 (by rfl) ⟨630431, by rfl⟩ : syracuseStep 840575 = 1260863) B1260863
theorem B840683 : Blo 558808 840683 := bstep (se 1 (by rfl) ⟨630512, by rfl⟩ : syracuseStep 840683 = 1261025) B1261025
theorem B840887 : Blo 558808 840887 := bstep (se 1 (by rfl) ⟨630665, by rfl⟩ : syracuseStep 840887 = 1261331) B1261331
theorem B1889783 : Blo 558808 1889783 := bstep (se 1 (by rfl) ⟨1417337, by rfl⟩ : syracuseStep 1889783 = 2834675) B2834675
theorem B841271 : Blo 558808 841271 := bstep (se 1 (by rfl) ⟨630953, by rfl⟩ : syracuseStep 841271 = 1261907) B1261907
theorem B841481 : Blo 558808 841481 := bstep (se 2 (by rfl) ⟨315555, by rfl⟩ : syracuseStep 841481 = 631111) B631111
theorem B842105 : Blo 558808 842105 := bstep (se 2 (by rfl) ⟨315789, by rfl⟩ : syracuseStep 842105 = 631579) B631579
theorem B1891079 : Blo 558808 1891079 := bstep (se 1 (by rfl) ⟨1418309, by rfl⟩ : syracuseStep 1891079 = 2836619) B2836619
theorem B1891241 : Blo 558808 1891241 := bstep (se 2 (by rfl) ⟨709215, by rfl⟩ : syracuseStep 1891241 = 1418431) B1418431
theorem B1596647 : Blo 558808 1596647 := bstep (se 1 (by rfl) ⟨1197485, by rfl⟩ : syracuseStep 1596647 = 2394971) B2394971
theorem B712091 : Blo 558808 712091 := bstep (se 1 (by rfl) ⟨534068, by rfl⟩ : syracuseStep 712091 = 1068137) B1068137
theorem B843335 : Blo 558808 843335 := bstep (se 1 (by rfl) ⟨632501, by rfl⟩ : syracuseStep 843335 = 1265003) B1265003
theorem B843755 : Blo 558808 843755 := bstep (se 1 (by rfl) ⟨632816, by rfl⟩ : syracuseStep 843755 = 1265633) B1265633
theorem B3039353 : Blo 558808 3039353 := bstep (se 2 (by rfl) ⟨1139757, by rfl⟩ : syracuseStep 3039353 = 2279515) B2279515
theorem B2843423 : Blo 558808 2843423 := bstep (se 1 (by rfl) ⟨2132567, by rfl⟩ : syracuseStep 2843423 = 4265135) B4265135
theorem B3204137 : Blo 558808 3204137 := bstep (se 2 (by rfl) ⟨1201551, by rfl⟩ : syracuseStep 3204137 = 2403103) B2403103
theorem B3237239 : Blo 558808 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B943481 : Blo 558808 943481 := bstep (se 2 (by rfl) ⟨353805, by rfl⟩ : syracuseStep 943481 = 707611) B707611
theorem B43706101 : Blo 558808 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B944743 : Blo 558808 944743 := bstep (se 1 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 944743 = 1417115) B1417115
theorem B912415 : Blo 558808 912415 := bstep (se 1 (by rfl) ⟨684311, by rfl⟩ : syracuseStep 912415 = 1368623) B1368623
theorem B1895561 : Blo 558808 1895561 := bstep (se 2 (by rfl) ⟨710835, by rfl⟩ : syracuseStep 1895561 = 1421671) B1421671
theorem B2846015 : Blo 558808 2846015 := bstep (se 1 (by rfl) ⟨2134511, by rfl⟩ : syracuseStep 2846015 = 4269023) B4269023
theorem B3599711 : Blo 558808 3599711 := bstep (se 1 (by rfl) ⟨2699783, by rfl⟩ : syracuseStep 3599711 = 5399567) B5399567
theorem B3403367 : Blo 558808 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B262402685 : Blo 558808 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B1438811 : Blo 558808 1438811 := bstep (se 1 (by rfl) ⟨1079108, by rfl⟩ : syracuseStep 1438811 = 2158217) B2158217
theorem B1799279 : Blo 558808 1799279 := bstep (se 1 (by rfl) ⟨1349459, by rfl⟩ : syracuseStep 1799279 = 2698919) B2698919
theorem B2128103 : Blo 558808 2128103 := bstep (se 1 (by rfl) ⟨1596077, by rfl⟩ : syracuseStep 2128103 = 3192155) B3192155
theorem B4783211 : Blo 558808 4783211 := bstep (se 1 (by rfl) ⟨3587408, by rfl⟩ : syracuseStep 4783211 = 7174817) B7174817
theorem B51936875 : Blo 558808 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B2393023 : Blo 558808 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B560383 : Blo 558808 560383 := bstep (se 1 (by rfl) ⟨420287, by rfl⟩ : syracuseStep 560383 = 840575) B840575
theorem B560455 : Blo 558808 560455 := bstep (se 1 (by rfl) ⟨420341, by rfl⟩ : syracuseStep 560455 = 840683) B840683
theorem B560591 : Blo 558808 560591 := bstep (se 1 (by rfl) ⟨420443, by rfl⟩ : syracuseStep 560591 = 840887) B840887
theorem B560847 : Blo 558808 560847 := bstep (se 1 (by rfl) ⟨420635, by rfl⟩ : syracuseStep 560847 = 841271) B841271
theorem B560987 : Blo 558808 560987 := bstep (se 1 (by rfl) ⟨420740, by rfl⟩ : syracuseStep 560987 = 841481) B841481
theorem B5378075 : Blo 558808 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B1216553 : Blo 558808 1216553 := bstep (se 2 (by rfl) ⟨456207, by rfl⟩ : syracuseStep 1216553 = 912415) B912415
theorem B561403 : Blo 558808 561403 := bstep (se 1 (by rfl) ⟨421052, by rfl⟩ : syracuseStep 561403 = 842105) B842105
theorem B562223 : Blo 558808 562223 := bstep (se 1 (by rfl) ⟨421667, by rfl⟩ : syracuseStep 562223 = 843335) B843335
theorem B562503 : Blo 558808 562503 := bstep (se 1 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 562503 = 843755) B843755
theorem B2136091 : Blo 558808 2136091 := bstep (se 1 (by rfl) ⟨1602068, by rfl⟩ : syracuseStep 2136091 = 3204137) B3204137
theorem B4266107 : Blo 558808 4266107 := bstep (se 1 (by rfl) ⟨3199580, by rfl⟩ : syracuseStep 4266107 = 6399161) B6399161
theorem B628987 : Blo 558808 628987 := bstep (se 1 (by rfl) ⟨471740, by rfl⟩ : syracuseStep 628987 = 943481) B943481
theorem B4562401 : Blo 558808 4562401 := bstep (se 2 (by rfl) ⟨1710900, by rfl⟩ : syracuseStep 4562401 = 3421801) B3421801
theorem B2399807 : Blo 558808 2399807 := bstep (se 1 (by rfl) ⟨1799855, by rfl⟩ : syracuseStep 2399807 = 3599711) B3599711
theorem B2268911 : Blo 558808 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B959207 : Blo 558808 959207 := bstep (se 1 (by rfl) ⟨719405, by rfl⟩ : syracuseStep 959207 = 1438811) B1438811
theorem B1418735 : Blo 558808 1418735 := bstep (se 1 (by rfl) ⟨1064051, by rfl⟩ : syracuseStep 1418735 = 2128103) B2128103
theorem B3188807 : Blo 558808 3188807 := bstep (se 1 (by rfl) ⟨2391605, by rfl⟩ : syracuseStep 3188807 = 4783211) B4783211
theorem B58274801 : Blo 558808 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B34584671 : Blo 558808 34584671 := bstep (se 1 (by rfl) ⟨25938503, by rfl⟩ : syracuseStep 34584671 = 51877007) B51877007
theorem B1259657 : Blo 558808 1259657 := bstep (se 2 (by rfl) ⟨472371, by rfl⟩ : syracuseStep 1259657 = 944743) B944743
theorem B1259855 : Blo 558808 1259855 := bstep (se 1 (by rfl) ⟨944891, by rfl⟩ : syracuseStep 1259855 = 1889783) B1889783
theorem B2276207 : Blo 558808 2276207 := bstep (se 1 (by rfl) ⟨1707155, by rfl⟩ : syracuseStep 2276207 = 3414311) B3414311
theorem B1260719 : Blo 558808 1260719 := bstep (se 1 (by rfl) ⟨945539, by rfl⟩ : syracuseStep 1260719 = 1891079) B1891079
theorem B1260827 : Blo 558808 1260827 := bstep (se 1 (by rfl) ⟨945620, by rfl⟩ : syracuseStep 1260827 = 1891241) B1891241
theorem B1064431 : Blo 558808 1064431 := bstep (se 1 (by rfl) ⟨798323, by rfl⟩ : syracuseStep 1064431 = 1596647) B1596647
theorem B900767 : Blo 558808 900767 := bstep (se 1 (by rfl) ⟨675575, by rfl⟩ : syracuseStep 900767 = 1351151) B1351151
theorem B1263707 : Blo 558808 1263707 := bstep (se 1 (by rfl) ⟨947780, by rfl⟩ : syracuseStep 1263707 = 1895561) B1895561
theorem B4246181 : Blo 558808 4246181 := bstep (se 4 (by rfl) ⟨398079, by rfl⟩ : syracuseStep 4246181 = 796159) B796159
theorem B174935123 : Blo 558808 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B838811 : Blo 558808 838811 := bstep (se 1 (by rfl) ⟨629108, by rfl⟩ : syracuseStep 838811 = 1258217) B1258217
theorem B1199519 : Blo 558808 1199519 := bstep (se 1 (by rfl) ⟨899639, by rfl⟩ : syracuseStep 1199519 = 1799279) B1799279
theorem B1887785 : Blo 558808 1887785 := bstep (se 2 (by rfl) ⟨707919, by rfl⟩ : syracuseStep 1887785 = 1415839) B1415839
theorem B840239 : Blo 558808 840239 := bstep (se 1 (by rfl) ⟨630179, by rfl⟩ : syracuseStep 840239 = 1260359) B1260359
theorem B840359 : Blo 558808 840359 := bstep (se 1 (by rfl) ⟨630269, by rfl⟩ : syracuseStep 840359 = 1260539) B1260539
theorem B840383 : Blo 558808 840383 := bstep (se 1 (by rfl) ⟨630287, by rfl⟩ : syracuseStep 840383 = 1260575) B1260575
theorem B34624583 : Blo 558808 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B1890377 : Blo 558808 1890377 := bstep (se 2 (by rfl) ⟨708891, by rfl⟩ : syracuseStep 1890377 = 1417783) B1417783
theorem B842987 : Blo 558808 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B1891835 : Blo 558808 1891835 := bstep (se 1 (by rfl) ⟨1418876, by rfl⟩ : syracuseStep 1891835 = 2837753) B2837753
theorem B4546313 : Blo 558808 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B2023613 : Blo 558808 2023613 := bstep (se 3 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 2023613 = 758855) B758855
theorem B2122483 : Blo 558808 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B1598879 : Blo 558808 1598879 := bstep (se 1 (by rfl) ⟨1199159, by rfl⟩ : syracuseStep 1598879 = 2398319) B2398319
theorem B2026235 : Blo 558808 2026235 := bstep (se 1 (by rfl) ⟨1519676, by rfl⟩ : syracuseStep 2026235 = 3039353) B3039353
theorem B1895615 : Blo 558808 1895615 := bstep (se 1 (by rfl) ⟨1421711, by rfl⟩ : syracuseStep 1895615 = 2843423) B2843423
theorem B5992015 : Blo 558808 5992015 := bstep (se 1 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 5992015 = 8988023) B8988023
theorem B2158159 : Blo 558808 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B1897343 : Blo 558808 1897343 := bstep (se 1 (by rfl) ⟨1423007, by rfl⟩ : syracuseStep 1897343 = 2846015) B2846015
theorem B1898909 : Blo 558808 1898909 := bstep (se 3 (by rfl) ⟨356045, by rfl⟩ : syracuseStep 1898909 = 712091) B712091
theorem B3701791 : Blo 558808 3701791 := bstep (se 1 (by rfl) ⟨2776343, by rfl⟩ : syracuseStep 3701791 = 5552687) B5552687
theorem B2129591 : Blo 558808 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B2392031 : Blo 558808 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B3244141 : Blo 558808 3244141 := bstep (se 3 (by rfl) ⟨608276, by rfl⟩ : syracuseStep 3244141 = 1216553) B1216553
theorem B2557885 : Blo 558808 2557885 := bstep (se 3 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 2557885 = 959207) B959207
theorem B116623415 : Blo 558808 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B559207 : Blo 558808 559207 := bstep (se 1 (by rfl) ⟨419405, by rfl⟩ : syracuseStep 559207 = 838811) B838811
theorem B560159 : Blo 558808 560159 := bstep (se 1 (by rfl) ⟨420119, by rfl⟩ : syracuseStep 560159 = 840239) B840239
theorem B560239 : Blo 558808 560239 := bstep (se 1 (by rfl) ⟨420179, by rfl⟩ : syracuseStep 560239 = 840359) B840359
theorem B560255 : Blo 558808 560255 := bstep (se 1 (by rfl) ⟨420191, by rfl⟩ : syracuseStep 560255 = 840383) B840383
theorem B4263677 : Blo 558808 4263677 := bstep (se 3 (by rfl) ⟨799439, by rfl⟩ : syracuseStep 4263677 = 1598879) B1598879
theorem B561991 : Blo 558808 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B1512607 : Blo 558808 1512607 := bstep (se 1 (by rfl) ⟨1134455, by rfl⟩ : syracuseStep 1512607 = 2268911) B2268911
theorem B1349075 : Blo 558808 1349075 := bstep (se 1 (by rfl) ⟨1011806, by rfl⟩ : syracuseStep 1349075 = 2023613) B2023613
theorem B2402045 : Blo 558808 2402045 := bstep (se 3 (by rfl) ⟨450383, by rfl⟩ : syracuseStep 2402045 = 900767) B900767
theorem B1517471 : Blo 558808 1517471 := bstep (se 1 (by rfl) ⟨1138103, by rfl⟩ : syracuseStep 1517471 = 2276207) B2276207
theorem B1419241 : Blo 558808 1419241 := bstep (se 2 (by rfl) ⟨532215, by rfl⟩ : syracuseStep 1419241 = 1064431) B1064431
theorem B1419727 : Blo 558808 1419727 := bstep (se 1 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 1419727 = 2129591) B2129591
theorem B2829977 : Blo 558808 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B3190697 : Blo 558808 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B2830787 : Blo 558808 2830787 := bstep (se 1 (by rfl) ⟨2123090, by rfl⟩ : syracuseStep 2830787 = 4246181) B4246181
theorem B799679 : Blo 558808 799679 := bstep (se 1 (by rfl) ⟨599759, by rfl⟩ : syracuseStep 799679 = 1199519) B1199519
theorem B1258523 : Blo 558808 1258523 := bstep (se 1 (by rfl) ⟨943892, by rfl⟩ : syracuseStep 1258523 = 1887785) B1887785
theorem B3585383 : Blo 558808 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B23083055 : Blo 558808 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B1260251 : Blo 558808 1260251 := bstep (se 1 (by rfl) ⟨945188, by rfl⟩ : syracuseStep 1260251 = 1890377) B1890377
theorem B1261223 : Blo 558808 1261223 := bstep (se 1 (by rfl) ⟨945917, by rfl⟩ : syracuseStep 1261223 = 1891835) B1891835
theorem B3030875 : Blo 558808 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B19742885 : Blo 558808 19742885 := bstep (se 4 (by rfl) ⟨1850895, by rfl⟩ : syracuseStep 19742885 = 3701791) B3701791
theorem B1263743 : Blo 558808 1263743 := bstep (se 1 (by rfl) ⟨947807, by rfl⟩ : syracuseStep 1263743 = 1895615) B1895615
theorem B838649 : Blo 558808 838649 := bstep (se 2 (by rfl) ⟨314493, by rfl⟩ : syracuseStep 838649 = 628987) B628987
theorem B1264895 : Blo 558808 1264895 := bstep (se 1 (by rfl) ⟨948671, by rfl⟩ : syracuseStep 1264895 = 1897343) B1897343
theorem B38849867 : Blo 558808 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B23056447 : Blo 558808 23056447 := bstep (se 1 (by rfl) ⟨17292335, by rfl⟩ : syracuseStep 23056447 = 34584671) B34584671
theorem B839771 : Blo 558808 839771 := bstep (se 1 (by rfl) ⟨629828, by rfl⟩ : syracuseStep 839771 = 1259657) B1259657
theorem B839903 : Blo 558808 839903 := bstep (se 1 (by rfl) ⟨629927, by rfl⟩ : syracuseStep 839903 = 1259855) B1259855
theorem B1265939 : Blo 558808 1265939 := bstep (se 1 (by rfl) ⟨949454, by rfl⟩ : syracuseStep 1265939 = 1898909) B1898909
theorem B6083201 : Blo 558808 6083201 := bstep (se 2 (by rfl) ⟨2281200, by rfl⟩ : syracuseStep 6083201 = 4562401) B4562401
theorem B840479 : Blo 558808 840479 := bstep (se 1 (by rfl) ⟨630359, by rfl⟩ : syracuseStep 840479 = 1260719) B1260719
theorem B840551 : Blo 558808 840551 := bstep (se 1 (by rfl) ⟨630413, by rfl⟩ : syracuseStep 840551 = 1260827) B1260827
theorem B6378749 : Blo 558808 6378749 := bstep (se 3 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 6378749 = 2392031) B2392031
theorem B842471 : Blo 558808 842471 := bstep (se 1 (by rfl) ⟨631853, by rfl⟩ : syracuseStep 842471 = 1263707) B1263707
theorem B2844071 : Blo 558808 2844071 := bstep (se 1 (by rfl) ⟨2133053, by rfl⟩ : syracuseStep 2844071 = 4266107) B4266107
theorem B7989353 : Blo 558808 7989353 := bstep (se 2 (by rfl) ⟨2996007, by rfl⟩ : syracuseStep 7989353 = 5992015) B5992015
theorem B2877545 : Blo 558808 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B1599871 : Blo 558808 1599871 := bstep (se 1 (by rfl) ⟨1199903, by rfl⟩ : syracuseStep 1599871 = 2399807) B2399807
theorem B945823 : Blo 558808 945823 := bstep (se 1 (by rfl) ⟨709367, by rfl⟩ : syracuseStep 945823 = 1418735) B1418735
theorem B2125871 : Blo 558808 2125871 := bstep (se 1 (by rfl) ⟨1594403, by rfl⟩ : syracuseStep 2125871 = 3188807) B3188807
theorem B5403293 : Blo 558808 5403293 := bstep (se 3 (by rfl) ⟨1013117, by rfl⟩ : syracuseStep 5403293 = 2026235) B2026235
theorem B2848121 : Blo 558808 2848121 := bstep (se 2 (by rfl) ⟨1068045, by rfl⟩ : syracuseStep 2848121 = 2136091) B2136091
theorem B4325521 : Blo 558808 4325521 := bstep (se 2 (by rfl) ⟨1622070, by rfl⟩ : syracuseStep 4325521 = 3244141) B3244141
theorem B16221869 : Blo 558808 16221869 := bstep (se 3 (by rfl) ⟨3041600, by rfl⟩ : syracuseStep 16221869 = 6083201) B6083201
theorem B559099 : Blo 558808 559099 := bstep (se 1 (by rfl) ⟨419324, by rfl⟩ : syracuseStep 559099 = 838649) B838649
theorem B2132477 : Blo 558808 2132477 := bstep (se 3 (by rfl) ⟨399839, by rfl⟩ : syracuseStep 2132477 = 799679) B799679
theorem B3410513 : Blo 558808 3410513 := bstep (se 2 (by rfl) ⟨1278942, by rfl⟩ : syracuseStep 3410513 = 2557885) B2557885
theorem B559847 : Blo 558808 559847 := bstep (se 1 (by rfl) ⟨419885, by rfl⟩ : syracuseStep 559847 = 839771) B839771
theorem B559935 : Blo 558808 559935 := bstep (se 1 (by rfl) ⟨419951, by rfl⟩ : syracuseStep 559935 = 839903) B839903
theorem B2133161 : Blo 558808 2133161 := bstep (se 2 (by rfl) ⟨799935, by rfl⟩ : syracuseStep 2133161 = 1599871) B1599871
theorem B560319 : Blo 558808 560319 := bstep (se 1 (by rfl) ⟨420239, by rfl⟩ : syracuseStep 560319 = 840479) B840479
theorem B560367 : Blo 558808 560367 := bstep (se 1 (by rfl) ⟨420275, by rfl⟩ : syracuseStep 560367 = 840551) B840551
theorem B561647 : Blo 558808 561647 := bstep (se 1 (by rfl) ⟨421235, by rfl⟩ : syracuseStep 561647 = 842471) B842471
theorem B30741929 : Blo 558808 30741929 := bstep (se 2 (by rfl) ⟨11528223, by rfl⟩ : syracuseStep 30741929 = 23056447) B23056447
theorem B7673453 : Blo 558808 7673453 := bstep (se 3 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 7673453 = 2877545) B2877545
theorem B1417247 : Blo 558808 1417247 := bstep (se 1 (by rfl) ⟨1062935, by rfl⟩ : syracuseStep 1417247 = 2125871) B2125871
theorem B25899911 : Blo 558808 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B1261097 : Blo 558808 1261097 := bstep (se 2 (by rfl) ⟨472911, by rfl⟩ : syracuseStep 1261097 = 945823) B945823
theorem B5326235 : Blo 558808 5326235 := bstep (se 1 (by rfl) ⟨3994676, by rfl⟩ : syracuseStep 5326235 = 7989353) B7989353
theorem B2016809 : Blo 558808 2016809 := bstep (se 2 (by rfl) ⟨756303, by rfl⟩ : syracuseStep 2016809 = 1512607) B1512607
theorem B1886651 : Blo 558808 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B1887191 : Blo 558808 1887191 := bstep (se 1 (by rfl) ⟨1415393, by rfl⟩ : syracuseStep 1887191 = 2830787) B2830787
theorem B839015 : Blo 558808 839015 := bstep (se 1 (by rfl) ⟨629261, by rfl⟩ : syracuseStep 839015 = 1258523) B1258523
theorem B15388703 : Blo 558808 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B840167 : Blo 558808 840167 := bstep (se 1 (by rfl) ⟨630125, by rfl⟩ : syracuseStep 840167 = 1260251) B1260251
theorem B840815 : Blo 558808 840815 := bstep (se 1 (by rfl) ⟨630611, by rfl⟩ : syracuseStep 840815 = 1261223) B1261223
theorem B2020583 : Blo 558808 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B13161923 : Blo 558808 13161923 := bstep (se 1 (by rfl) ⟨9871442, by rfl⟩ : syracuseStep 13161923 = 19742885) B19742885
theorem B77748943 : Blo 558808 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B842495 : Blo 558808 842495 := bstep (se 1 (by rfl) ⟨631871, by rfl⟩ : syracuseStep 842495 = 1263743) B1263743
theorem B843263 : Blo 558808 843263 := bstep (se 1 (by rfl) ⟨632447, by rfl⟩ : syracuseStep 843263 = 1264895) B1264895
theorem B2842451 : Blo 558808 2842451 := bstep (se 1 (by rfl) ⟨2131838, by rfl⟩ : syracuseStep 2842451 = 4263677) B4263677
theorem B1892321 : Blo 558808 1892321 := bstep (se 2 (by rfl) ⟨709620, by rfl⟩ : syracuseStep 1892321 = 1419241) B1419241
theorem B843959 : Blo 558808 843959 := bstep (se 1 (by rfl) ⟨632969, by rfl⟩ : syracuseStep 843959 = 1265939) B1265939
theorem B1892969 : Blo 558808 1892969 := bstep (se 2 (by rfl) ⟨709863, by rfl⟩ : syracuseStep 1892969 = 1419727) B1419727
theorem B4252499 : Blo 558808 4252499 := bstep (se 1 (by rfl) ⟨3189374, by rfl⟩ : syracuseStep 4252499 = 6378749) B6378749
theorem B3597533 : Blo 558808 3597533 := bstep (se 3 (by rfl) ⟨674537, by rfl⟩ : syracuseStep 3597533 = 1349075) B1349075
theorem B1896047 : Blo 558808 1896047 := bstep (se 1 (by rfl) ⟨1422035, by rfl⟩ : syracuseStep 1896047 = 2844071) B2844071
theorem B1601363 : Blo 558808 1601363 := bstep (se 1 (by rfl) ⟨1201022, by rfl⟩ : syracuseStep 1601363 = 2402045) B2402045
theorem B1011647 : Blo 558808 1011647 := bstep (se 1 (by rfl) ⟨758735, by rfl⟩ : syracuseStep 1011647 = 1517471) B1517471
theorem B2127131 : Blo 558808 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B3602195 : Blo 558808 3602195 := bstep (se 1 (by rfl) ⟨2701646, by rfl⟩ : syracuseStep 3602195 = 5403293) B5403293
theorem B2390255 : Blo 558808 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B1898747 : Blo 558808 1898747 := bstep (se 1 (by rfl) ⟨1424060, by rfl⟩ : syracuseStep 1898747 = 2848121) B2848121
theorem B5767361 : Blo 558808 5767361 := bstep (se 2 (by rfl) ⟨2162760, by rfl⟩ : syracuseStep 5767361 = 4325521) B4325521
theorem B1344539 : Blo 558808 1344539 := bstep (se 1 (by rfl) ⟨1008404, by rfl⟩ : syracuseStep 1344539 = 2016809) B2016809
theorem B10814579 : Blo 558808 10814579 := bstep (se 1 (by rfl) ⟨8110934, by rfl⟩ : syracuseStep 10814579 = 16221869) B16221869
theorem B559343 : Blo 558808 559343 := bstep (se 1 (by rfl) ⟨419507, by rfl⟩ : syracuseStep 559343 = 839015) B839015
theorem B10259135 : Blo 558808 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B560111 : Blo 558808 560111 := bstep (se 1 (by rfl) ⟨420083, by rfl⟩ : syracuseStep 560111 = 840167) B840167
theorem B560543 : Blo 558808 560543 := bstep (se 1 (by rfl) ⟨420407, by rfl⟩ : syracuseStep 560543 = 840815) B840815
theorem B5115635 : Blo 558808 5115635 := bstep (se 1 (by rfl) ⟨3836726, by rfl⟩ : syracuseStep 5115635 = 7673453) B7673453
theorem B561663 : Blo 558808 561663 := bstep (se 1 (by rfl) ⟨421247, by rfl⟩ : syracuseStep 561663 = 842495) B842495
theorem B562175 : Blo 558808 562175 := bstep (se 1 (by rfl) ⟨421631, by rfl⟩ : syracuseStep 562175 = 843263) B843263
theorem B562639 : Blo 558808 562639 := bstep (se 1 (by rfl) ⟨421979, by rfl⟩ : syracuseStep 562639 = 843959) B843959
theorem B2398355 : Blo 558808 2398355 := bstep (se 1 (by rfl) ⟨1798766, by rfl⟩ : syracuseStep 2398355 = 3597533) B3597533
theorem B1418087 : Blo 558808 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B2401463 : Blo 558808 2401463 := bstep (se 1 (by rfl) ⟨1801097, by rfl⟩ : syracuseStep 2401463 = 3602195) B3602195
theorem B2697725 : Blo 558808 2697725 := bstep (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) B1011647
theorem B3550823 : Blo 558808 3550823 := bstep (se 1 (by rfl) ⟨2663117, by rfl⟩ : syracuseStep 3550823 = 5326235) B5326235
theorem B1257767 : Blo 558808 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B1421651 : Blo 558808 1421651 := bstep (se 1 (by rfl) ⟨1066238, by rfl⟩ : syracuseStep 1421651 = 2132477) B2132477
theorem B2273675 : Blo 558808 2273675 := bstep (se 1 (by rfl) ⟨1705256, by rfl⟩ : syracuseStep 2273675 = 3410513) B3410513
theorem B1258127 : Blo 558808 1258127 := bstep (se 1 (by rfl) ⟨943595, by rfl⟩ : syracuseStep 1258127 = 1887191) B1887191
theorem B1422107 : Blo 558808 1422107 := bstep (se 1 (by rfl) ⟨1066580, by rfl⟩ : syracuseStep 1422107 = 2133161) B2133161
theorem B5388221 : Blo 558808 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B20494619 : Blo 558808 20494619 := bstep (se 1 (by rfl) ⟨15370964, by rfl⟩ : syracuseStep 20494619 = 30741929) B30741929
theorem B1261547 : Blo 558808 1261547 := bstep (se 1 (by rfl) ⟨946160, by rfl⟩ : syracuseStep 1261547 = 1892321) B1892321
theorem B1261979 : Blo 558808 1261979 := bstep (se 1 (by rfl) ⟨946484, by rfl⟩ : syracuseStep 1261979 = 1892969) B1892969
theorem B2834999 : Blo 558808 2834999 := bstep (se 1 (by rfl) ⟨2126249, by rfl⟩ : syracuseStep 2834999 = 4252499) B4252499
theorem B1264031 : Blo 558808 1264031 := bstep (se 1 (by rfl) ⟨948023, by rfl⟩ : syracuseStep 1264031 = 1896047) B1896047
theorem B1067575 : Blo 558808 1067575 := bstep (se 1 (by rfl) ⟨800681, by rfl⟩ : syracuseStep 1067575 = 1601363) B1601363
theorem B103665257 : Blo 558808 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B1593503 : Blo 558808 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B1265831 : Blo 558808 1265831 := bstep (se 1 (by rfl) ⟨949373, by rfl⟩ : syracuseStep 1265831 = 1898747) B1898747
theorem B840731 : Blo 558808 840731 := bstep (se 1 (by rfl) ⟨630548, by rfl⟩ : syracuseStep 840731 = 1261097) B1261097
theorem B8774615 : Blo 558808 8774615 := bstep (se 1 (by rfl) ⟨6580961, by rfl⟩ : syracuseStep 8774615 = 13161923) B13161923
theorem B1894967 : Blo 558808 1894967 := bstep (se 1 (by rfl) ⟨1421225, by rfl⟩ : syracuseStep 1894967 = 2842451) B2842451
theorem B944831 : Blo 558808 944831 := bstep (se 1 (by rfl) ⟨708623, by rfl⟩ : syracuseStep 944831 = 1417247) B1417247
theorem B17266607 : Blo 558808 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B7209719 : Blo 558808 7209719 := bstep (se 1 (by rfl) ⟨5407289, by rfl⟩ : syracuseStep 7209719 = 10814579) B10814579
theorem B69110171 : Blo 558808 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B3410423 : Blo 558808 3410423 := bstep (se 1 (by rfl) ⟨2557817, by rfl⟩ : syracuseStep 3410423 = 5115635) B5115635
theorem B560487 : Blo 558808 560487 := bstep (se 1 (by rfl) ⟨420365, by rfl⟩ : syracuseStep 560487 = 840731) B840731
theorem B24252533 : Blo 558808 24252533 := bstep (se 5 (by rfl) ⟨1136837, by rfl⟩ : syracuseStep 24252533 = 2273675) B2273675
theorem B629887 : Blo 558808 629887 := bstep (se 1 (by rfl) ⟨472415, by rfl⟩ : syracuseStep 629887 = 944831) B944831
theorem B2367215 : Blo 558808 2367215 := bstep (se 1 (by rfl) ⟨1775411, by rfl⟩ : syracuseStep 2367215 = 3550823) B3550823
theorem B11511071 : Blo 558808 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B3844907 : Blo 558808 3844907 := bstep (se 1 (by rfl) ⟨2883680, by rfl⟩ : syracuseStep 3844907 = 5767361) B5767361
theorem B896359 : Blo 558808 896359 := bstep (se 1 (by rfl) ⟨672269, by rfl⟩ : syracuseStep 896359 = 1344539) B1344539
theorem B1062335 : Blo 558808 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B1423433 : Blo 558808 1423433 := bstep (se 2 (by rfl) ⟨533787, by rfl⟩ : syracuseStep 1423433 = 1067575) B1067575
theorem B14368589 : Blo 558808 14368589 := bstep (se 3 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 14368589 = 5388221) B5388221
theorem B5849743 : Blo 558808 5849743 := bstep (se 1 (by rfl) ⟨4387307, by rfl⟩ : syracuseStep 5849743 = 8774615) B8774615
theorem B7193933 : Blo 558808 7193933 := bstep (se 3 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 7193933 = 2697725) B2697725
theorem B1263311 : Blo 558808 1263311 := bstep (se 1 (by rfl) ⟨947483, by rfl⟩ : syracuseStep 1263311 = 1894967) B1894967
theorem B838511 : Blo 558808 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B838751 : Blo 558808 838751 := bstep (se 1 (by rfl) ⟨629063, by rfl⟩ : syracuseStep 838751 = 1258127) B1258127
theorem B841031 : Blo 558808 841031 := bstep (se 1 (by rfl) ⟨630773, by rfl⟩ : syracuseStep 841031 = 1261547) B1261547
theorem B841319 : Blo 558808 841319 := bstep (se 1 (by rfl) ⟨630989, by rfl⟩ : syracuseStep 841319 = 1261979) B1261979
theorem B1889999 : Blo 558808 1889999 := bstep (se 1 (by rfl) ⟨1417499, by rfl⟩ : syracuseStep 1889999 = 2834999) B2834999
theorem B842687 : Blo 558808 842687 := bstep (se 1 (by rfl) ⟨632015, by rfl⟩ : syracuseStep 842687 = 1264031) B1264031
theorem B6839423 : Blo 558808 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B843887 : Blo 558808 843887 := bstep (se 1 (by rfl) ⟨632915, by rfl⟩ : syracuseStep 843887 = 1265831) B1265831
theorem B1598903 : Blo 558808 1598903 := bstep (se 1 (by rfl) ⟨1199177, by rfl⟩ : syracuseStep 1598903 = 2398355) B2398355
theorem B945391 : Blo 558808 945391 := bstep (se 1 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 945391 = 1418087) B1418087
theorem B1600975 : Blo 558808 1600975 := bstep (se 1 (by rfl) ⟨1200731, by rfl⟩ : syracuseStep 1600975 = 2401463) B2401463
theorem B947767 : Blo 558808 947767 := bstep (se 1 (by rfl) ⟨710825, by rfl⟩ : syracuseStep 947767 = 1421651) B1421651
theorem B948071 : Blo 558808 948071 := bstep (se 1 (by rfl) ⟨711053, by rfl⟩ : syracuseStep 948071 = 1422107) B1422107
theorem B13663079 : Blo 558808 13663079 := bstep (se 1 (by rfl) ⟨10247309, by rfl⟩ : syracuseStep 13663079 = 20494619) B20494619
theorem B7799657 : Blo 558808 7799657 := bstep (se 2 (by rfl) ⟨2924871, by rfl⟩ : syracuseStep 7799657 = 5849743) B5849743
theorem B46073447 : Blo 558808 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B559007 : Blo 558808 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B559167 : Blo 558808 559167 := bstep (se 1 (by rfl) ⟨419375, by rfl⟩ : syracuseStep 559167 = 838751) B838751
theorem B560687 : Blo 558808 560687 := bstep (se 1 (by rfl) ⟨420515, by rfl⟩ : syracuseStep 560687 = 841031) B841031
theorem B560879 : Blo 558808 560879 := bstep (se 1 (by rfl) ⟨420659, by rfl⟩ : syracuseStep 560879 = 841319) B841319
theorem B2134633 : Blo 558808 2134633 := bstep (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) B1600975
theorem B561791 : Blo 558808 561791 := bstep (se 1 (by rfl) ⟨421343, by rfl⟩ : syracuseStep 561791 = 842687) B842687
theorem B4559615 : Blo 558808 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B1578143 : Blo 558808 1578143 := bstep (se 1 (by rfl) ⟨1183607, by rfl⟩ : syracuseStep 1578143 = 2367215) B2367215
theorem B562591 : Blo 558808 562591 := bstep (se 1 (by rfl) ⟨421943, by rfl⟩ : syracuseStep 562591 = 843887) B843887
theorem B7674047 : Blo 558808 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B2563271 : Blo 558808 2563271 := bstep (se 1 (by rfl) ⟨1922453, by rfl⟩ : syracuseStep 2563271 = 3844907) B3844907
theorem B632047 : Blo 558808 632047 := bstep (se 1 (by rfl) ⟨474035, by rfl⟩ : syracuseStep 632047 = 948071) B948071
theorem B9579059 : Blo 558808 9579059 := bstep (se 1 (by rfl) ⟨7184294, by rfl⟩ : syracuseStep 9579059 = 14368589) B14368589
theorem B4795955 : Blo 558808 4795955 := bstep (se 1 (by rfl) ⟨3596966, by rfl⟩ : syracuseStep 4795955 = 7193933) B7193933
theorem B2273615 : Blo 558808 2273615 := bstep (se 1 (by rfl) ⟨1705211, by rfl⟩ : syracuseStep 2273615 = 3410423) B3410423
theorem B16168355 : Blo 558808 16168355 := bstep (se 1 (by rfl) ⟨12126266, by rfl⟩ : syracuseStep 16168355 = 24252533) B24252533
theorem B1259999 : Blo 558808 1259999 := bstep (se 1 (by rfl) ⟨944999, by rfl⟩ : syracuseStep 1259999 = 1889999) B1889999
theorem B2832893 : Blo 558808 2832893 := bstep (se 3 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 2832893 = 1062335) B1062335
theorem B1260521 : Blo 558808 1260521 := bstep (se 2 (by rfl) ⟨472695, by rfl⟩ : syracuseStep 1260521 = 945391) B945391
theorem B1195145 : Blo 558808 1195145 := bstep (se 2 (by rfl) ⟨448179, by rfl⟩ : syracuseStep 1195145 = 896359) B896359
theorem B1065935 : Blo 558808 1065935 := bstep (se 1 (by rfl) ⟨799451, by rfl⟩ : syracuseStep 1065935 = 1598903) B1598903
theorem B1263689 : Blo 558808 1263689 := bstep (se 2 (by rfl) ⟨473883, by rfl⟩ : syracuseStep 1263689 = 947767) B947767
theorem B839849 : Blo 558808 839849 := bstep (se 2 (by rfl) ⟨314943, by rfl⟩ : syracuseStep 839849 = 629887) B629887
theorem B4806479 : Blo 558808 4806479 := bstep (se 1 (by rfl) ⟨3604859, by rfl⟩ : syracuseStep 4806479 = 7209719) B7209719
theorem B842207 : Blo 558808 842207 := bstep (se 1 (by rfl) ⟨631655, by rfl⟩ : syracuseStep 842207 = 1263311) B1263311
theorem B948955 : Blo 558808 948955 := bstep (se 1 (by rfl) ⟨711716, by rfl⟩ : syracuseStep 948955 = 1423433) B1423433
theorem B9108719 : Blo 558808 9108719 := bstep (se 1 (by rfl) ⟨6831539, by rfl⟩ : syracuseStep 9108719 = 13663079) B13663079
theorem B559899 : Blo 558808 559899 := bstep (se 1 (by rfl) ⟨419924, by rfl⟩ : syracuseStep 559899 = 839849) B839849
theorem B5116031 : Blo 558808 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B561471 : Blo 558808 561471 := bstep (se 1 (by rfl) ⟨421103, by rfl⟩ : syracuseStep 561471 = 842207) B842207
theorem B1708847 : Blo 558808 1708847 := bstep (se 1 (by rfl) ⟨1281635, by rfl⟩ : syracuseStep 1708847 = 2563271) B2563271
theorem B1515743 : Blo 558808 1515743 := bstep (se 1 (by rfl) ⟨1136807, by rfl⟩ : syracuseStep 1515743 = 2273615) B2273615
theorem B796763 : Blo 558808 796763 := bstep (se 1 (by rfl) ⟨597572, by rfl⟩ : syracuseStep 796763 = 1195145) B1195145
theorem B6072479 : Blo 558808 6072479 := bstep (se 1 (by rfl) ⟨4554359, by rfl⟩ : syracuseStep 6072479 = 9108719) B9108719
theorem B30715631 : Blo 558808 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B4208381 : Blo 558808 4208381 := bstep (se 3 (by rfl) ⟨789071, by rfl⟩ : syracuseStep 4208381 = 1578143) B1578143
theorem B3197303 : Blo 558808 3197303 := bstep (se 1 (by rfl) ⟨2397977, by rfl⟩ : syracuseStep 3197303 = 4795955) B4795955
theorem B1265273 : Blo 558808 1265273 := bstep (se 2 (by rfl) ⟨474477, by rfl⟩ : syracuseStep 1265273 = 948955) B948955
theorem B839999 : Blo 558808 839999 := bstep (se 1 (by rfl) ⟨629999, by rfl⟩ : syracuseStep 839999 = 1259999) B1259999
theorem B1888595 : Blo 558808 1888595 := bstep (se 1 (by rfl) ⟨1416446, by rfl⟩ : syracuseStep 1888595 = 2832893) B2832893
theorem B840347 : Blo 558808 840347 := bstep (se 1 (by rfl) ⟨630260, by rfl⟩ : syracuseStep 840347 = 1260521) B1260521
theorem B710623 : Blo 558808 710623 := bstep (se 1 (by rfl) ⟨532967, by rfl⟩ : syracuseStep 710623 = 1065935) B1065935
theorem B842459 : Blo 558808 842459 := bstep (se 1 (by rfl) ⟨631844, by rfl⟩ : syracuseStep 842459 = 1263689) B1263689
theorem B842729 : Blo 558808 842729 := bstep (se 2 (by rfl) ⟨316023, by rfl⟩ : syracuseStep 842729 = 632047) B632047
theorem B3039743 : Blo 558808 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B3204319 : Blo 558808 3204319 := bstep (se 1 (by rfl) ⟨2403239, by rfl⟩ : syracuseStep 3204319 = 4806479) B4806479
theorem B2846177 : Blo 558808 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B6386039 : Blo 558808 6386039 := bstep (se 1 (by rfl) ⟨4789529, by rfl⟩ : syracuseStep 6386039 = 9579059) B9579059
theorem B10778903 : Blo 558808 10778903 := bstep (se 1 (by rfl) ⟨8084177, by rfl⟩ : syracuseStep 10778903 = 16168355) B16168355
theorem B83196341 : Blo 558808 83196341 := bstep (se 5 (by rfl) ⟨3899828, by rfl⟩ : syracuseStep 83196341 = 7799657) B7799657
theorem B2131535 : Blo 558808 2131535 := bstep (se 1 (by rfl) ⟨1598651, by rfl⟩ : syracuseStep 2131535 = 3197303) B3197303
theorem B3410687 : Blo 558808 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B559999 : Blo 558808 559999 := bstep (se 1 (by rfl) ⟨419999, by rfl⟩ : syracuseStep 559999 = 839999) B839999
theorem B560231 : Blo 558808 560231 := bstep (se 1 (by rfl) ⟨420173, by rfl⟩ : syracuseStep 560231 = 840347) B840347
theorem B561639 : Blo 558808 561639 := bstep (se 1 (by rfl) ⟨421229, by rfl⟩ : syracuseStep 561639 = 842459) B842459
theorem B561819 : Blo 558808 561819 := bstep (se 1 (by rfl) ⟨421364, by rfl⟩ : syracuseStep 561819 = 842729) B842729
theorem B7185935 : Blo 558808 7185935 := bstep (se 1 (by rfl) ⟨5389451, by rfl⟩ : syracuseStep 7185935 = 10778903) B10778903
theorem B4272425 : Blo 558808 4272425 := bstep (se 2 (by rfl) ⟨1602159, by rfl⟩ : syracuseStep 4272425 = 3204319) B3204319
theorem B1259063 : Blo 558808 1259063 := bstep (se 1 (by rfl) ⟨944297, by rfl⟩ : syracuseStep 1259063 = 1888595) B1888595
theorem B4048319 : Blo 558808 4048319 := bstep (se 1 (by rfl) ⟨3036239, by rfl⟩ : syracuseStep 4048319 = 6072479) B6072479
theorem B2805587 : Blo 558808 2805587 := bstep (se 1 (by rfl) ⟨2104190, by rfl⟩ : syracuseStep 2805587 = 4208381) B4208381
theorem B55464227 : Blo 558808 55464227 := bstep (se 1 (by rfl) ⟨41598170, by rfl⟩ : syracuseStep 55464227 = 83196341) B83196341
theorem B843515 : Blo 558808 843515 := bstep (se 1 (by rfl) ⟨632636, by rfl⟩ : syracuseStep 843515 = 1265273) B1265273
theorem B1139231 : Blo 558808 1139231 := bstep (se 1 (by rfl) ⟨854423, by rfl⟩ : syracuseStep 1139231 = 1708847) B1708847
theorem B1010495 : Blo 558808 1010495 := bstep (se 1 (by rfl) ⟨757871, by rfl⟩ : syracuseStep 1010495 = 1515743) B1515743
theorem B2124701 : Blo 558808 2124701 := bstep (se 3 (by rfl) ⟨398381, by rfl⟩ : syracuseStep 2124701 = 796763) B796763
theorem B2026495 : Blo 558808 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B1897451 : Blo 558808 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B20477087 : Blo 558808 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B947497 : Blo 558808 947497 := bstep (se 2 (by rfl) ⟨355311, by rfl⟩ : syracuseStep 947497 = 710623) B710623
theorem B4257359 : Blo 558808 4257359 := bstep (se 1 (by rfl) ⟨3193019, by rfl⟩ : syracuseStep 4257359 = 6386039) B6386039
theorem B1870391 : Blo 558808 1870391 := bstep (se 1 (by rfl) ⟨1402793, by rfl⟩ : syracuseStep 1870391 = 2805587) B2805587
theorem B562343 : Blo 558808 562343 := bstep (se 1 (by rfl) ⟨421757, by rfl⟩ : syracuseStep 562343 = 843515) B843515
theorem B4790623 : Blo 558808 4790623 := bstep (se 1 (by rfl) ⟨3592967, by rfl⟩ : syracuseStep 4790623 = 7185935) B7185935
theorem B1416467 : Blo 558808 1416467 := bstep (se 1 (by rfl) ⟨1062350, by rfl⟩ : syracuseStep 1416467 = 2124701) B2124701
theorem B2698879 : Blo 558808 2698879 := bstep (se 1 (by rfl) ⟨2024159, by rfl⟩ : syracuseStep 2698879 = 4048319) B4048319
theorem B1421023 : Blo 558808 1421023 := bstep (se 1 (by rfl) ⟨1065767, by rfl⟩ : syracuseStep 1421023 = 2131535) B2131535
theorem B36976151 : Blo 558808 36976151 := bstep (se 1 (by rfl) ⟨27732113, by rfl⟩ : syracuseStep 36976151 = 55464227) B55464227
theorem B2701993 : Blo 558808 2701993 := bstep (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) B2026495
theorem B1263329 : Blo 558808 1263329 := bstep (se 2 (by rfl) ⟨473748, by rfl⟩ : syracuseStep 1263329 = 947497) B947497
theorem B673663 : Blo 558808 673663 := bstep (se 1 (by rfl) ⟨505247, by rfl⟩ : syracuseStep 673663 = 1010495) B1010495
theorem B9095165 : Blo 558808 9095165 := bstep (se 3 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 9095165 = 3410687) B3410687
theorem B1264967 : Blo 558808 1264967 := bstep (se 1 (by rfl) ⟨948725, by rfl⟩ : syracuseStep 1264967 = 1897451) B1897451
theorem B13651391 : Blo 558808 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B839375 : Blo 558808 839375 := bstep (se 1 (by rfl) ⟨629531, by rfl⟩ : syracuseStep 839375 = 1259063) B1259063
theorem B2838239 : Blo 558808 2838239 := bstep (se 1 (by rfl) ⟨2128679, by rfl⟩ : syracuseStep 2838239 = 4257359) B4257359
theorem B3037949 : Blo 558808 3037949 := bstep (se 3 (by rfl) ⟨569615, by rfl⟩ : syracuseStep 3037949 = 1139231) B1139231
theorem B2848283 : Blo 558808 2848283 := bstep (se 1 (by rfl) ⟨2136212, by rfl⟩ : syracuseStep 2848283 = 4272425) B4272425
theorem B6063443 : Blo 558808 6063443 := bstep (se 1 (by rfl) ⟨4547582, by rfl⟩ : syracuseStep 6063443 = 9095165) B9095165
theorem B1246927 : Blo 558808 1246927 := bstep (se 1 (by rfl) ⟨935195, by rfl⟩ : syracuseStep 1246927 = 1870391) B1870391
theorem B559583 : Blo 558808 559583 := bstep (se 1 (by rfl) ⟨419687, by rfl⟩ : syracuseStep 559583 = 839375) B839375
theorem B24650767 : Blo 558808 24650767 := bstep (se 1 (by rfl) ⟨18488075, by rfl⟩ : syracuseStep 24650767 = 36976151) B36976151
theorem B898217 : Blo 558808 898217 := bstep (se 2 (by rfl) ⟨336831, by rfl⟩ : syracuseStep 898217 = 673663) B673663
theorem B842219 : Blo 558808 842219 := bstep (se 1 (by rfl) ⟨631664, by rfl⟩ : syracuseStep 842219 = 1263329) B1263329
theorem B843311 : Blo 558808 843311 := bstep (se 1 (by rfl) ⟨632483, by rfl⟩ : syracuseStep 843311 = 1264967) B1264967
theorem B9100927 : Blo 558808 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B1892159 : Blo 558808 1892159 := bstep (se 1 (by rfl) ⟨1419119, by rfl⟩ : syracuseStep 1892159 = 2838239) B2838239
theorem B2025299 : Blo 558808 2025299 := bstep (se 1 (by rfl) ⟨1518974, by rfl⟩ : syracuseStep 2025299 = 3037949) B3037949
theorem B3598505 : Blo 558808 3598505 := bstep (se 2 (by rfl) ⟨1349439, by rfl⟩ : syracuseStep 3598505 = 2698879) B2698879
theorem B944311 : Blo 558808 944311 := bstep (se 1 (by rfl) ⟨708233, by rfl⟩ : syracuseStep 944311 = 1416467) B1416467
theorem B1894697 : Blo 558808 1894697 := bstep (se 2 (by rfl) ⟨710511, by rfl⟩ : syracuseStep 1894697 = 1421023) B1421023
theorem B6387497 : Blo 558808 6387497 := bstep (se 2 (by rfl) ⟨2395311, by rfl⟩ : syracuseStep 6387497 = 4790623) B4790623
theorem B3602657 : Blo 558808 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B1898855 : Blo 558808 1898855 := bstep (se 1 (by rfl) ⟨1424141, by rfl⟩ : syracuseStep 1898855 = 2848283) B2848283
theorem B32867689 : Blo 558808 32867689 := bstep (se 2 (by rfl) ⟨12325383, by rfl⟩ : syracuseStep 32867689 = 24650767) B24650767
theorem B561479 : Blo 558808 561479 := bstep (se 1 (by rfl) ⟨421109, by rfl⟩ : syracuseStep 561479 = 842219) B842219
theorem B562207 : Blo 558808 562207 := bstep (se 1 (by rfl) ⟨421655, by rfl⟩ : syracuseStep 562207 = 843311) B843311
theorem B1350199 : Blo 558808 1350199 := bstep (se 1 (by rfl) ⟨1012649, by rfl⟩ : syracuseStep 1350199 = 2025299) B2025299
theorem B2399003 : Blo 558808 2399003 := bstep (se 1 (by rfl) ⟨1799252, by rfl⟩ : syracuseStep 2399003 = 3598505) B3598505
theorem B48538277 : Blo 558808 48538277 := bstep (se 4 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 48538277 = 9100927) B9100927
theorem B598811 : Blo 558808 598811 := bstep (se 1 (by rfl) ⟨449108, by rfl⟩ : syracuseStep 598811 = 898217) B898217
theorem B2401771 : Blo 558808 2401771 := bstep (se 1 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 2401771 = 3602657) B3602657
theorem B4042295 : Blo 558808 4042295 := bstep (se 1 (by rfl) ⟨3031721, by rfl⟩ : syracuseStep 4042295 = 6063443) B6063443
theorem B1259081 : Blo 558808 1259081 := bstep (se 2 (by rfl) ⟨472155, by rfl⟩ : syracuseStep 1259081 = 944311) B944311
theorem B1261439 : Blo 558808 1261439 := bstep (se 1 (by rfl) ⟨946079, by rfl⟩ : syracuseStep 1261439 = 1892159) B1892159
theorem B1263131 : Blo 558808 1263131 := bstep (se 1 (by rfl) ⟨947348, by rfl⟩ : syracuseStep 1263131 = 1894697) B1894697
theorem B1265903 : Blo 558808 1265903 := bstep (se 1 (by rfl) ⟨949427, by rfl⟩ : syracuseStep 1265903 = 1898855) B1898855
theorem B1662569 : Blo 558808 1662569 := bstep (se 2 (by rfl) ⟨623463, by rfl⟩ : syracuseStep 1662569 = 1246927) B1246927
theorem B4258331 : Blo 558808 4258331 := bstep (se 1 (by rfl) ⟨3193748, by rfl⟩ : syracuseStep 4258331 = 6387497) B6387497
theorem B2694863 : Blo 558808 2694863 := bstep (se 1 (by rfl) ⟨2021147, by rfl⟩ : syracuseStep 2694863 = 4042295) B4042295
theorem B43823585 : Blo 558808 43823585 := bstep (se 2 (by rfl) ⟨16433844, by rfl⟩ : syracuseStep 43823585 = 32867689) B32867689
theorem B32358851 : Blo 558808 32358851 := bstep (se 1 (by rfl) ⟨24269138, by rfl⟩ : syracuseStep 32358851 = 48538277) B48538277
theorem B839387 : Blo 558808 839387 := bstep (se 1 (by rfl) ⟨629540, by rfl⟩ : syracuseStep 839387 = 1259081) B1259081
theorem B2838887 : Blo 558808 2838887 := bstep (se 1 (by rfl) ⟨2129165, by rfl⟩ : syracuseStep 2838887 = 4258331) B4258331
theorem B840959 : Blo 558808 840959 := bstep (se 1 (by rfl) ⟨630719, by rfl⟩ : syracuseStep 840959 = 1261439) B1261439
theorem B842087 : Blo 558808 842087 := bstep (se 1 (by rfl) ⟨631565, by rfl⟩ : syracuseStep 842087 = 1263131) B1263131
theorem B3202361 : Blo 558808 3202361 := bstep (se 2 (by rfl) ⟨1200885, by rfl⟩ : syracuseStep 3202361 = 2401771) B2401771
theorem B1596829 : Blo 558808 1596829 := bstep (se 3 (by rfl) ⟨299405, by rfl⟩ : syracuseStep 1596829 = 598811) B598811
theorem B843935 : Blo 558808 843935 := bstep (se 1 (by rfl) ⟨632951, by rfl⟩ : syracuseStep 843935 = 1265903) B1265903
theorem B7201061 : Blo 558808 7201061 := bstep (se 4 (by rfl) ⟨675099, by rfl⟩ : syracuseStep 7201061 = 1350199) B1350199
theorem B1599335 : Blo 558808 1599335 := bstep (se 1 (by rfl) ⟨1199501, by rfl⟩ : syracuseStep 1599335 = 2399003) B2399003
theorem B1108379 : Blo 558808 1108379 := bstep (se 1 (by rfl) ⟨831284, by rfl⟩ : syracuseStep 1108379 = 1662569) B1662569
theorem B559591 : Blo 558808 559591 := bstep (se 1 (by rfl) ⟨419693, by rfl⟩ : syracuseStep 559591 = 839387) B839387
theorem B560639 : Blo 558808 560639 := bstep (se 1 (by rfl) ⟨420479, by rfl⟩ : syracuseStep 560639 = 840959) B840959
theorem B561391 : Blo 558808 561391 := bstep (se 1 (by rfl) ⟨421043, by rfl⟩ : syracuseStep 561391 = 842087) B842087
theorem B2134907 : Blo 558808 2134907 := bstep (se 1 (by rfl) ⟨1601180, by rfl⟩ : syracuseStep 2134907 = 3202361) B3202361
theorem B562623 : Blo 558808 562623 := bstep (se 1 (by rfl) ⟨421967, by rfl⟩ : syracuseStep 562623 = 843935) B843935
theorem B21572567 : Blo 558808 21572567 := bstep (se 1 (by rfl) ⟨16179425, by rfl⟩ : syracuseStep 21572567 = 32358851) B32358851
theorem B4800707 : Blo 558808 4800707 := bstep (se 1 (by rfl) ⟨3600530, by rfl⟩ : syracuseStep 4800707 = 7201061) B7201061
theorem B1066223 : Blo 558808 1066223 := bstep (se 1 (by rfl) ⟨799667, by rfl⟩ : syracuseStep 1066223 = 1599335) B1599335
theorem B738919 : Blo 558808 738919 := bstep (se 1 (by rfl) ⟨554189, by rfl⟩ : syracuseStep 738919 = 1108379) B1108379
theorem B29215723 : Blo 558808 29215723 := bstep (se 1 (by rfl) ⟨21911792, by rfl⟩ : syracuseStep 29215723 = 43823585) B43823585
theorem B1892591 : Blo 558808 1892591 := bstep (se 1 (by rfl) ⟨1419443, by rfl⟩ : syracuseStep 1892591 = 2838887) B2838887
theorem B1796575 : Blo 558808 1796575 := bstep (se 1 (by rfl) ⟨1347431, by rfl⟩ : syracuseStep 1796575 = 2694863) B2694863
theorem B2129105 : Blo 558808 2129105 := bstep (se 2 (by rfl) ⟨798414, by rfl⟩ : syracuseStep 2129105 = 1596829) B1596829
theorem B985225 : Blo 558808 985225 := bstep (se 2 (by rfl) ⟨369459, by rfl⟩ : syracuseStep 985225 = 738919) B738919
theorem B2395433 : Blo 558808 2395433 := bstep (se 2 (by rfl) ⟨898287, by rfl⟩ : syracuseStep 2395433 = 1796575) B1796575
theorem B1419403 : Blo 558808 1419403 := bstep (se 1 (by rfl) ⟨1064552, by rfl⟩ : syracuseStep 1419403 = 2129105) B2129105
theorem B1423271 : Blo 558808 1423271 := bstep (se 1 (by rfl) ⟨1067453, by rfl⟩ : syracuseStep 1423271 = 2134907) B2134907
theorem B1261727 : Blo 558808 1261727 := bstep (se 1 (by rfl) ⟨946295, by rfl⟩ : syracuseStep 1261727 = 1892591) B1892591
theorem B3200471 : Blo 558808 3200471 := bstep (se 1 (by rfl) ⟨2400353, by rfl⟩ : syracuseStep 3200471 = 4800707) B4800707
theorem B2843261 : Blo 558808 2843261 := bstep (se 3 (by rfl) ⟨533111, by rfl⟩ : syracuseStep 2843261 = 1066223) B1066223
theorem B38954297 : Blo 558808 38954297 := bstep (se 2 (by rfl) ⟨14607861, by rfl⟩ : syracuseStep 38954297 = 29215723) B29215723
theorem B14381711 : Blo 558808 14381711 := bstep (se 1 (by rfl) ⟨10786283, by rfl⟩ : syracuseStep 14381711 = 21572567) B21572567
theorem B1313633 : Blo 558808 1313633 := bstep (se 2 (by rfl) ⟨492612, by rfl⟩ : syracuseStep 1313633 = 985225) B985225
theorem B2133647 : Blo 558808 2133647 := bstep (se 1 (by rfl) ⟨1600235, by rfl⟩ : syracuseStep 2133647 = 3200471) B3200471
theorem B25969531 : Blo 558808 25969531 := bstep (se 1 (by rfl) ⟨19477148, by rfl⟩ : syracuseStep 25969531 = 38954297) B38954297
theorem B9587807 : Blo 558808 9587807 := bstep (se 1 (by rfl) ⟨7190855, by rfl⟩ : syracuseStep 9587807 = 14381711) B14381711
theorem B841151 : Blo 558808 841151 := bstep (se 1 (by rfl) ⟨630863, by rfl⟩ : syracuseStep 841151 = 1261727) B1261727
theorem B1596955 : Blo 558808 1596955 := bstep (se 1 (by rfl) ⟨1197716, by rfl⟩ : syracuseStep 1596955 = 2395433) B2395433
theorem B1892537 : Blo 558808 1892537 := bstep (se 2 (by rfl) ⟨709701, by rfl⟩ : syracuseStep 1892537 = 1419403) B1419403
theorem B1895507 : Blo 558808 1895507 := bstep (se 1 (by rfl) ⟨1421630, by rfl⟩ : syracuseStep 1895507 = 2843261) B2843261
theorem B948847 : Blo 558808 948847 := bstep (se 1 (by rfl) ⟨711635, by rfl⟩ : syracuseStep 948847 = 1423271) B1423271
theorem B6391871 : Blo 558808 6391871 := bstep (se 1 (by rfl) ⟨4793903, by rfl⟩ : syracuseStep 6391871 = 9587807) B9587807
theorem B560767 : Blo 558808 560767 := bstep (se 1 (by rfl) ⟨420575, by rfl⟩ : syracuseStep 560767 = 841151) B841151
theorem B1422431 : Blo 558808 1422431 := bstep (se 1 (by rfl) ⟨1066823, by rfl⟩ : syracuseStep 1422431 = 2133647) B2133647
theorem B1261691 : Blo 558808 1261691 := bstep (se 1 (by rfl) ⟨946268, by rfl⟩ : syracuseStep 1261691 = 1892537) B1892537
theorem B1263671 : Blo 558808 1263671 := bstep (se 1 (by rfl) ⟨947753, by rfl⟩ : syracuseStep 1263671 = 1895507) B1895507
theorem B1265129 : Blo 558808 1265129 := bstep (se 2 (by rfl) ⟨474423, by rfl⟩ : syracuseStep 1265129 = 948847) B948847
theorem B34626041 : Blo 558808 34626041 := bstep (se 2 (by rfl) ⟨12984765, by rfl⟩ : syracuseStep 34626041 = 25969531) B25969531
theorem B875755 : Blo 558808 875755 := bstep (se 1 (by rfl) ⟨656816, by rfl⟩ : syracuseStep 875755 = 1313633) B1313633
theorem B2129273 : Blo 558808 2129273 := bstep (se 2 (by rfl) ⟨798477, by rfl⟩ : syracuseStep 2129273 = 1596955) B1596955
theorem B4261247 : Blo 558808 4261247 := bstep (se 1 (by rfl) ⟨3195935, by rfl⟩ : syracuseStep 4261247 = 6391871) B6391871
theorem B1419515 : Blo 558808 1419515 := bstep (se 1 (by rfl) ⟨1064636, by rfl⟩ : syracuseStep 1419515 = 2129273) B2129273
theorem B23084027 : Blo 558808 23084027 := bstep (se 1 (by rfl) ⟨17313020, by rfl⟩ : syracuseStep 23084027 = 34626041) B34626041
theorem B4670693 : Blo 558808 4670693 := bstep (se 4 (by rfl) ⟨437877, by rfl⟩ : syracuseStep 4670693 = 875755) B875755
theorem B841127 : Blo 558808 841127 := bstep (se 1 (by rfl) ⟨630845, by rfl⟩ : syracuseStep 841127 = 1261691) B1261691
theorem B842447 : Blo 558808 842447 := bstep (se 1 (by rfl) ⟨631835, by rfl⟩ : syracuseStep 842447 = 1263671) B1263671
theorem B843419 : Blo 558808 843419 := bstep (se 1 (by rfl) ⟨632564, by rfl⟩ : syracuseStep 843419 = 1265129) B1265129
theorem B948287 : Blo 558808 948287 := bstep (se 1 (by rfl) ⟨711215, by rfl⟩ : syracuseStep 948287 = 1422431) B1422431
theorem B3113795 : Blo 558808 3113795 := bstep (se 1 (by rfl) ⟨2335346, by rfl⟩ : syracuseStep 3113795 = 4670693) B4670693
theorem B560751 : Blo 558808 560751 := bstep (se 1 (by rfl) ⟨420563, by rfl⟩ : syracuseStep 560751 = 841127) B841127
theorem B561631 : Blo 558808 561631 := bstep (se 1 (by rfl) ⟨421223, by rfl⟩ : syracuseStep 561631 = 842447) B842447
theorem B562279 : Blo 558808 562279 := bstep (se 1 (by rfl) ⟨421709, by rfl⟩ : syracuseStep 562279 = 843419) B843419
theorem B632191 : Blo 558808 632191 := bstep (se 1 (by rfl) ⟨474143, by rfl⟩ : syracuseStep 632191 = 948287) B948287
theorem B15389351 : Blo 558808 15389351 := bstep (se 1 (by rfl) ⟨11542013, by rfl⟩ : syracuseStep 15389351 = 23084027) B23084027
theorem B2840831 : Blo 558808 2840831 := bstep (se 1 (by rfl) ⟨2130623, by rfl⟩ : syracuseStep 2840831 = 4261247) B4261247
theorem B946343 : Blo 558808 946343 := bstep (se 1 (by rfl) ⟨709757, by rfl⟩ : syracuseStep 946343 = 1419515) B1419515
theorem B10259567 : Blo 558808 10259567 := bstep (se 1 (by rfl) ⟨7694675, by rfl⟩ : syracuseStep 10259567 = 15389351) B15389351
theorem B630895 : Blo 558808 630895 := bstep (se 1 (by rfl) ⟨473171, by rfl⟩ : syracuseStep 630895 = 946343) B946343
theorem B2075863 : Blo 558808 2075863 := bstep (se 1 (by rfl) ⟨1556897, by rfl⟩ : syracuseStep 2075863 = 3113795) B3113795
theorem B842921 : Blo 558808 842921 := bstep (se 2 (by rfl) ⟨316095, by rfl⟩ : syracuseStep 842921 = 632191) B632191
theorem B1893887 : Blo 558808 1893887 := bstep (se 1 (by rfl) ⟨1420415, by rfl⟩ : syracuseStep 1893887 = 2840831) B2840831
theorem B561947 : Blo 558808 561947 := bstep (se 1 (by rfl) ⟨421460, by rfl⟩ : syracuseStep 561947 = 842921) B842921
theorem B2767817 : Blo 558808 2767817 := bstep (se 2 (by rfl) ⟨1037931, by rfl⟩ : syracuseStep 2767817 = 2075863) B2075863
theorem B1262591 : Blo 558808 1262591 := bstep (se 1 (by rfl) ⟨946943, by rfl⟩ : syracuseStep 1262591 = 1893887) B1893887
theorem B841193 : Blo 558808 841193 := bstep (se 2 (by rfl) ⟨315447, by rfl⟩ : syracuseStep 841193 = 630895) B630895
theorem B6839711 : Blo 558808 6839711 := bstep (se 1 (by rfl) ⟨5129783, by rfl⟩ : syracuseStep 6839711 = 10259567) B10259567
theorem B560795 : Blo 558808 560795 := bstep (se 1 (by rfl) ⟨420596, by rfl⟩ : syracuseStep 560795 = 841193) B841193
theorem B4559807 : Blo 558808 4559807 := bstep (se 1 (by rfl) ⟨3419855, by rfl⟩ : syracuseStep 4559807 = 6839711) B6839711
theorem B7380845 : Blo 558808 7380845 := bstep (se 3 (by rfl) ⟨1383908, by rfl⟩ : syracuseStep 7380845 = 2767817) B2767817
theorem B841727 : Blo 558808 841727 := bstep (se 1 (by rfl) ⟨631295, by rfl⟩ : syracuseStep 841727 = 1262591) B1262591
theorem B561151 : Blo 558808 561151 := bstep (se 1 (by rfl) ⟨420863, by rfl⟩ : syracuseStep 561151 = 841727) B841727
theorem B4920563 : Blo 558808 4920563 := bstep (se 1 (by rfl) ⟨3690422, by rfl⟩ : syracuseStep 4920563 = 7380845) B7380845
theorem B3039871 : Blo 558808 3039871 := bstep (se 1 (by rfl) ⟨2279903, by rfl⟩ : syracuseStep 3039871 = 4559807) B4559807
theorem B3280375 : Blo 558808 3280375 := bstep (se 1 (by rfl) ⟨2460281, by rfl⟩ : syracuseStep 3280375 = 4920563) B4920563
theorem B4053161 : Blo 558808 4053161 := bstep (se 2 (by rfl) ⟨1519935, by rfl⟩ : syracuseStep 4053161 = 3039871) B3039871
theorem B2702107 : Blo 558808 2702107 := bstep (se 1 (by rfl) ⟨2026580, by rfl⟩ : syracuseStep 2702107 = 4053161) B4053161
theorem B4373833 : Blo 558808 4373833 := bstep (se 2 (by rfl) ⟨1640187, by rfl⟩ : syracuseStep 4373833 = 3280375) B3280375
theorem B3602809 : Blo 558808 3602809 := bstep (se 2 (by rfl) ⟨1351053, by rfl⟩ : syracuseStep 3602809 = 2702107) B2702107
theorem B5831777 : Blo 558808 5831777 := bstep (se 2 (by rfl) ⟨2186916, by rfl⟩ : syracuseStep 5831777 = 4373833) B4373833
theorem B4803745 : Blo 558808 4803745 := bstep (se 2 (by rfl) ⟨1801404, by rfl⟩ : syracuseStep 4803745 = 3602809) B3602809
theorem B3887851 : Blo 558808 3887851 := bstep (se 1 (by rfl) ⟨2915888, by rfl⟩ : syracuseStep 3887851 = 5831777) B5831777
theorem B5183801 : Blo 558808 5183801 := bstep (se 2 (by rfl) ⟨1943925, by rfl⟩ : syracuseStep 5183801 = 3887851) B3887851
theorem B6404993 : Blo 558808 6404993 := bstep (se 2 (by rfl) ⟨2401872, by rfl⟩ : syracuseStep 6404993 = 4803745) B4803745
theorem B4269995 : Blo 558808 4269995 := bstep (se 1 (by rfl) ⟨3202496, by rfl⟩ : syracuseStep 4269995 = 6404993) B6404993
theorem B3455867 : Blo 558808 3455867 := bstep (se 1 (by rfl) ⟨2591900, by rfl⟩ : syracuseStep 3455867 = 5183801) B5183801
theorem B2303911 : Blo 558808 2303911 := bstep (se 1 (by rfl) ⟨1727933, by rfl⟩ : syracuseStep 2303911 = 3455867) B3455867
theorem B2846663 : Blo 558808 2846663 := bstep (se 1 (by rfl) ⟨2134997, by rfl⟩ : syracuseStep 2846663 = 4269995) B4269995
theorem B3071881 : Blo 558808 3071881 := bstep (se 2 (by rfl) ⟨1151955, by rfl⟩ : syracuseStep 3071881 = 2303911) B2303911
theorem B1897775 : Blo 558808 1897775 := bstep (se 1 (by rfl) ⟨1423331, by rfl⟩ : syracuseStep 1897775 = 2846663) B2846663
theorem B1265183 : Blo 558808 1265183 := bstep (se 1 (by rfl) ⟨948887, by rfl⟩ : syracuseStep 1265183 = 1897775) B1897775
theorem B4095841 : Blo 558808 4095841 := bstep (se 2 (by rfl) ⟨1535940, by rfl⟩ : syracuseStep 4095841 = 3071881) B3071881
theorem B5461121 : Blo 558808 5461121 := bstep (se 2 (by rfl) ⟨2047920, by rfl⟩ : syracuseStep 5461121 = 4095841) B4095841
theorem B843455 : Blo 558808 843455 := bstep (se 1 (by rfl) ⟨632591, by rfl⟩ : syracuseStep 843455 = 1265183) B1265183
theorem B3640747 : Blo 558808 3640747 := bstep (se 1 (by rfl) ⟨2730560, by rfl⟩ : syracuseStep 3640747 = 5461121) B5461121
theorem B562303 : Blo 558808 562303 := bstep (se 1 (by rfl) ⟨421727, by rfl⟩ : syracuseStep 562303 = 843455) B843455
theorem B4854329 : Blo 558808 4854329 := bstep (se 2 (by rfl) ⟨1820373, by rfl⟩ : syracuseStep 4854329 = 3640747) B3640747
theorem B3236219 : Blo 558808 3236219 := bstep (se 1 (by rfl) ⟨2427164, by rfl⟩ : syracuseStep 3236219 = 4854329) B4854329
theorem B2157479 : Blo 558808 2157479 := bstep (se 1 (by rfl) ⟨1618109, by rfl⟩ : syracuseStep 2157479 = 3236219) B3236219
theorem B1438319 : Blo 558808 1438319 := bstep (se 1 (by rfl) ⟨1078739, by rfl⟩ : syracuseStep 1438319 = 2157479) B2157479
theorem B958879 : Blo 558808 958879 := bstep (se 1 (by rfl) ⟨719159, by rfl⟩ : syracuseStep 958879 = 1438319) B1438319
theorem B1278505 : Blo 558808 1278505 := bstep (se 2 (by rfl) ⟨479439, by rfl⟩ : syracuseStep 1278505 = 958879) B958879
theorem B1704673 : Blo 558808 1704673 := bstep (se 2 (by rfl) ⟨639252, by rfl⟩ : syracuseStep 1704673 = 1278505) B1278505
theorem B2272897 : Blo 558808 2272897 := bstep (se 2 (by rfl) ⟨852336, by rfl⟩ : syracuseStep 2272897 = 1704673) B1704673
theorem B3030529 : Blo 558808 3030529 := bstep (se 2 (by rfl) ⟨1136448, by rfl⟩ : syracuseStep 3030529 = 2272897) B2272897
theorem B4040705 : Blo 558808 4040705 := bstep (se 2 (by rfl) ⟨1515264, by rfl⟩ : syracuseStep 4040705 = 3030529) B3030529
theorem B10775213 : Blo 558808 10775213 := bstep (se 3 (by rfl) ⟨2020352, by rfl⟩ : syracuseStep 10775213 = 4040705) B4040705
theorem B7183475 : Blo 558808 7183475 := bstep (se 1 (by rfl) ⟨5387606, by rfl⟩ : syracuseStep 7183475 = 10775213) B10775213
theorem B4788983 : Blo 558808 4788983 := bstep (se 1 (by rfl) ⟨3591737, by rfl⟩ : syracuseStep 4788983 = 7183475) B7183475
theorem B3192655 : Blo 558808 3192655 := bstep (se 1 (by rfl) ⟨2394491, by rfl⟩ : syracuseStep 3192655 = 4788983) B4788983
theorem B4256873 : Blo 558808 4256873 := bstep (se 2 (by rfl) ⟨1596327, by rfl⟩ : syracuseStep 4256873 = 3192655) B3192655
theorem B2837915 : Blo 558808 2837915 := bstep (se 1 (by rfl) ⟨2128436, by rfl⟩ : syracuseStep 2837915 = 4256873) B4256873
theorem B1891943 : Blo 558808 1891943 := bstep (se 1 (by rfl) ⟨1418957, by rfl⟩ : syracuseStep 1891943 = 2837915) B2837915
theorem B1261295 : Blo 558808 1261295 := bstep (se 1 (by rfl) ⟨945971, by rfl⟩ : syracuseStep 1261295 = 1891943) B1891943
theorem B840863 : Blo 558808 840863 := bstep (se 1 (by rfl) ⟨630647, by rfl⟩ : syracuseStep 840863 = 1261295) B1261295
theorem B560575 : Blo 558808 560575 := bstep (se 1 (by rfl) ⟨420431, by rfl⟩ : syracuseStep 560575 = 840863) B840863

theorem C0 (j : ℕ) (h1 : 139702 ≤ j) (h2 : j ≤ 140401) : Blo 558808 (4 * j + 3) := by
  interval_cases j
  · exact B558811
  · exact B558815
  · exact B558819
  · exact B558823
  · exact B558827
  · exact B558831
  · exact B558835
  · exact B558839
  · exact B558843
  · exact B558847
  · exact B558851
  · exact B558855
  · exact B558859
  · exact B558863
  · exact B558867
  · exact B558871
  · exact B558875
  · exact B558879
  · exact B558883
  · exact B558887
  · exact B558891
  · exact B558895
  · exact B558899
  · exact B558903
  · exact B558907
  · exact B558911
  · exact B558915
  · exact B558919
  · exact B558923
  · exact B558927
  · exact B558931
  · exact B558935
  · exact B558939
  · exact B558943
  · exact B558947
  · exact B558951
  · exact B558955
  · exact B558959
  · exact B558963
  · exact B558967
  · exact B558971
  · exact B558975
  · exact B558979
  · exact B558983
  · exact B558987
  · exact B558991
  · exact B558995
  · exact B558999
  · exact B559003
  · exact B559007
  · exact B559011
  · exact B559015
  · exact B559019
  · exact B559023
  · exact B559027
  · exact B559031
  · exact B559035
  · exact B559039
  · exact B559043
  · exact B559047
  · exact B559051
  · exact B559055
  · exact B559059
  · exact B559063
  · exact B559067
  · exact B559071
  · exact B559075
  · exact B559079
  · exact B559083
  · exact B559087
  · exact B559091
  · exact B559095
  · exact B559099
  · exact B559103
  · exact B559107
  · exact B559111
  · exact B559115
  · exact B559119
  · exact B559123
  · exact B559127
  · exact B559131
  · exact B559135
  · exact B559139
  · exact B559143
  · exact B559147
  · exact B559151
  · exact B559155
  · exact B559159
  · exact B559163
  · exact B559167
  · exact B559171
  · exact B559175
  · exact B559179
  · exact B559183
  · exact B559187
  · exact B559191
  · exact B559195
  · exact B559199
  · exact B559203
  · exact B559207
  · exact B559211
  · exact B559215
  · exact B559219
  · exact B559223
  · exact B559227
  · exact B559231
  · exact B559235
  · exact B559239
  · exact B559243
  · exact B559247
  · exact B559251
  · exact B559255
  · exact B559259
  · exact B559263
  · exact B559267
  · exact B559271
  · exact B559275
  · exact B559279
  · exact B559283
  · exact B559287
  · exact B559291
  · exact B559295
  · exact B559299
  · exact B559303
  · exact B559307
  · exact B559311
  · exact B559315
  · exact B559319
  · exact B559323
  · exact B559327
  · exact B559331
  · exact B559335
  · exact B559339
  · exact B559343
  · exact B559347
  · exact B559351
  · exact B559355
  · exact B559359
  · exact B559363
  · exact B559367
  · exact B559371
  · exact B559375
  · exact B559379
  · exact B559383
  · exact B559387
  · exact B559391
  · exact B559395
  · exact B559399
  · exact B559403
  · exact B559407
  · exact B559411
  · exact B559415
  · exact B559419
  · exact B559423
  · exact B559427
  · exact B559431
  · exact B559435
  · exact B559439
  · exact B559443
  · exact B559447
  · exact B559451
  · exact B559455
  · exact B559459
  · exact B559463
  · exact B559467
  · exact B559471
  · exact B559475
  · exact B559479
  · exact B559483
  · exact B559487
  · exact B559491
  · exact B559495
  · exact B559499
  · exact B559503
  · exact B559507
  · exact B559511
  · exact B559515
  · exact B559519
  · exact B559523
  · exact B559527
  · exact B559531
  · exact B559535
  · exact B559539
  · exact B559543
  · exact B559547
  · exact B559551
  · exact B559555
  · exact B559559
  · exact B559563
  · exact B559567
  · exact B559571
  · exact B559575
  · exact B559579
  · exact B559583
  · exact B559587
  · exact B559591
  · exact B559595
  · exact B559599
  · exact B559603
  · exact B559607
  · exact B559611
  · exact B559615
  · exact B559619
  · exact B559623
  · exact B559627
  · exact B559631
  · exact B559635
  · exact B559639
  · exact B559643
  · exact B559647
  · exact B559651
  · exact B559655
  · exact B559659
  · exact B559663
  · exact B559667
  · exact B559671
  · exact B559675
  · exact B559679
  · exact B559683
  · exact B559687
  · exact B559691
  · exact B559695
  · exact B559699
  · exact B559703
  · exact B559707
  · exact B559711
  · exact B559715
  · exact B559719
  · exact B559723
  · exact B559727
  · exact B559731
  · exact B559735
  · exact B559739
  · exact B559743
  · exact B559747
  · exact B559751
  · exact B559755
  · exact B559759
  · exact B559763
  · exact B559767
  · exact B559771
  · exact B559775
  · exact B559779
  · exact B559783
  · exact B559787
  · exact B559791
  · exact B559795
  · exact B559799
  · exact B559803
  · exact B559807
  · exact B559811
  · exact B559815
  · exact B559819
  · exact B559823
  · exact B559827
  · exact B559831
  · exact B559835
  · exact B559839
  · exact B559843
  · exact B559847
  · exact B559851
  · exact B559855
  · exact B559859
  · exact B559863
  · exact B559867
  · exact B559871
  · exact B559875
  · exact B559879
  · exact B559883
  · exact B559887
  · exact B559891
  · exact B559895
  · exact B559899
  · exact B559903
  · exact B559907
  · exact B559911
  · exact B559915
  · exact B559919
  · exact B559923
  · exact B559927
  · exact B559931
  · exact B559935
  · exact B559939
  · exact B559943
  · exact B559947
  · exact B559951
  · exact B559955
  · exact B559959
  · exact B559963
  · exact B559967
  · exact B559971
  · exact B559975
  · exact B559979
  · exact B559983
  · exact B559987
  · exact B559991
  · exact B559995
  · exact B559999
  · exact B560003
  · exact B560007
  · exact B560011
  · exact B560015
  · exact B560019
  · exact B560023
  · exact B560027
  · exact B560031
  · exact B560035
  · exact B560039
  · exact B560043
  · exact B560047
  · exact B560051
  · exact B560055
  · exact B560059
  · exact B560063
  · exact B560067
  · exact B560071
  · exact B560075
  · exact B560079
  · exact B560083
  · exact B560087
  · exact B560091
  · exact B560095
  · exact B560099
  · exact B560103
  · exact B560107
  · exact B560111
  · exact B560115
  · exact B560119
  · exact B560123
  · exact B560127
  · exact B560131
  · exact B560135
  · exact B560139
  · exact B560143
  · exact B560147
  · exact B560151
  · exact B560155
  · exact B560159
  · exact B560163
  · exact B560167
  · exact B560171
  · exact B560175
  · exact B560179
  · exact B560183
  · exact B560187
  · exact B560191
  · exact B560195
  · exact B560199
  · exact B560203
  · exact B560207
  · exact B560211
  · exact B560215
  · exact B560219
  · exact B560223
  · exact B560227
  · exact B560231
  · exact B560235
  · exact B560239
  · exact B560243
  · exact B560247
  · exact B560251
  · exact B560255
  · exact B560259
  · exact B560263
  · exact B560267
  · exact B560271
  · exact B560275
  · exact B560279
  · exact B560283
  · exact B560287
  · exact B560291
  · exact B560295
  · exact B560299
  · exact B560303
  · exact B560307
  · exact B560311
  · exact B560315
  · exact B560319
  · exact B560323
  · exact B560327
  · exact B560331
  · exact B560335
  · exact B560339
  · exact B560343
  · exact B560347
  · exact B560351
  · exact B560355
  · exact B560359
  · exact B560363
  · exact B560367
  · exact B560371
  · exact B560375
  · exact B560379
  · exact B560383
  · exact B560387
  · exact B560391
  · exact B560395
  · exact B560399
  · exact B560403
  · exact B560407
  · exact B560411
  · exact B560415
  · exact B560419
  · exact B560423
  · exact B560427
  · exact B560431
  · exact B560435
  · exact B560439
  · exact B560443
  · exact B560447
  · exact B560451
  · exact B560455
  · exact B560459
  · exact B560463
  · exact B560467
  · exact B560471
  · exact B560475
  · exact B560479
  · exact B560483
  · exact B560487
  · exact B560491
  · exact B560495
  · exact B560499
  · exact B560503
  · exact B560507
  · exact B560511
  · exact B560515
  · exact B560519
  · exact B560523
  · exact B560527
  · exact B560531
  · exact B560535
  · exact B560539
  · exact B560543
  · exact B560547
  · exact B560551
  · exact B560555
  · exact B560559
  · exact B560563
  · exact B560567
  · exact B560571
  · exact B560575
  · exact B560579
  · exact B560583
  · exact B560587
  · exact B560591
  · exact B560595
  · exact B560599
  · exact B560603
  · exact B560607
  · exact B560611
  · exact B560615
  · exact B560619
  · exact B560623
  · exact B560627
  · exact B560631
  · exact B560635
  · exact B560639
  · exact B560643
  · exact B560647
  · exact B560651
  · exact B560655
  · exact B560659
  · exact B560663
  · exact B560667
  · exact B560671
  · exact B560675
  · exact B560679
  · exact B560683
  · exact B560687
  · exact B560691
  · exact B560695
  · exact B560699
  · exact B560703
  · exact B560707
  · exact B560711
  · exact B560715
  · exact B560719
  · exact B560723
  · exact B560727
  · exact B560731
  · exact B560735
  · exact B560739
  · exact B560743
  · exact B560747
  · exact B560751
  · exact B560755
  · exact B560759
  · exact B560763
  · exact B560767
  · exact B560771
  · exact B560775
  · exact B560779
  · exact B560783
  · exact B560787
  · exact B560791
  · exact B560795
  · exact B560799
  · exact B560803
  · exact B560807
  · exact B560811
  · exact B560815
  · exact B560819
  · exact B560823
  · exact B560827
  · exact B560831
  · exact B560835
  · exact B560839
  · exact B560843
  · exact B560847
  · exact B560851
  · exact B560855
  · exact B560859
  · exact B560863
  · exact B560867
  · exact B560871
  · exact B560875
  · exact B560879
  · exact B560883
  · exact B560887
  · exact B560891
  · exact B560895
  · exact B560899
  · exact B560903
  · exact B560907
  · exact B560911
  · exact B560915
  · exact B560919
  · exact B560923
  · exact B560927
  · exact B560931
  · exact B560935
  · exact B560939
  · exact B560943
  · exact B560947
  · exact B560951
  · exact B560955
  · exact B560959
  · exact B560963
  · exact B560967
  · exact B560971
  · exact B560975
  · exact B560979
  · exact B560983
  · exact B560987
  · exact B560991
  · exact B560995
  · exact B560999
  · exact B561003
  · exact B561007
  · exact B561011
  · exact B561015
  · exact B561019
  · exact B561023
  · exact B561027
  · exact B561031
  · exact B561035
  · exact B561039
  · exact B561043
  · exact B561047
  · exact B561051
  · exact B561055
  · exact B561059
  · exact B561063
  · exact B561067
  · exact B561071
  · exact B561075
  · exact B561079
  · exact B561083
  · exact B561087
  · exact B561091
  · exact B561095
  · exact B561099
  · exact B561103
  · exact B561107
  · exact B561111
  · exact B561115
  · exact B561119
  · exact B561123
  · exact B561127
  · exact B561131
  · exact B561135
  · exact B561139
  · exact B561143
  · exact B561147
  · exact B561151
  · exact B561155
  · exact B561159
  · exact B561163
  · exact B561167
  · exact B561171
  · exact B561175
  · exact B561179
  · exact B561183
  · exact B561187
  · exact B561191
  · exact B561195
  · exact B561199
  · exact B561203
  · exact B561207
  · exact B561211
  · exact B561215
  · exact B561219
  · exact B561223
  · exact B561227
  · exact B561231
  · exact B561235
  · exact B561239
  · exact B561243
  · exact B561247
  · exact B561251
  · exact B561255
  · exact B561259
  · exact B561263
  · exact B561267
  · exact B561271
  · exact B561275
  · exact B561279
  · exact B561283
  · exact B561287
  · exact B561291
  · exact B561295
  · exact B561299
  · exact B561303
  · exact B561307
  · exact B561311
  · exact B561315
  · exact B561319
  · exact B561323
  · exact B561327
  · exact B561331
  · exact B561335
  · exact B561339
  · exact B561343
  · exact B561347
  · exact B561351
  · exact B561355
  · exact B561359
  · exact B561363
  · exact B561367
  · exact B561371
  · exact B561375
  · exact B561379
  · exact B561383
  · exact B561387
  · exact B561391
  · exact B561395
  · exact B561399
  · exact B561403
  · exact B561407
  · exact B561411
  · exact B561415
  · exact B561419
  · exact B561423
  · exact B561427
  · exact B561431
  · exact B561435
  · exact B561439
  · exact B561443
  · exact B561447
  · exact B561451
  · exact B561455
  · exact B561459
  · exact B561463
  · exact B561467
  · exact B561471
  · exact B561475
  · exact B561479
  · exact B561483
  · exact B561487
  · exact B561491
  · exact B561495
  · exact B561499
  · exact B561503
  · exact B561507
  · exact B561511
  · exact B561515
  · exact B561519
  · exact B561523
  · exact B561527
  · exact B561531
  · exact B561535
  · exact B561539
  · exact B561543
  · exact B561547
  · exact B561551
  · exact B561555
  · exact B561559
  · exact B561563
  · exact B561567
  · exact B561571
  · exact B561575
  · exact B561579
  · exact B561583
  · exact B561587
  · exact B561591
  · exact B561595
  · exact B561599
  · exact B561603
  · exact B561607

theorem C1 (j : ℕ) (h1 : 140402 ≤ j) (h2 : j ≤ 140701) : Blo 558808 (4 * j + 3) := by
  interval_cases j
  · exact B561611
  · exact B561615
  · exact B561619
  · exact B561623
  · exact B561627
  · exact B561631
  · exact B561635
  · exact B561639
  · exact B561643
  · exact B561647
  · exact B561651
  · exact B561655
  · exact B561659
  · exact B561663
  · exact B561667
  · exact B561671
  · exact B561675
  · exact B561679
  · exact B561683
  · exact B561687
  · exact B561691
  · exact B561695
  · exact B561699
  · exact B561703
  · exact B561707
  · exact B561711
  · exact B561715
  · exact B561719
  · exact B561723
  · exact B561727
  · exact B561731
  · exact B561735
  · exact B561739
  · exact B561743
  · exact B561747
  · exact B561751
  · exact B561755
  · exact B561759
  · exact B561763
  · exact B561767
  · exact B561771
  · exact B561775
  · exact B561779
  · exact B561783
  · exact B561787
  · exact B561791
  · exact B561795
  · exact B561799
  · exact B561803
  · exact B561807
  · exact B561811
  · exact B561815
  · exact B561819
  · exact B561823
  · exact B561827
  · exact B561831
  · exact B561835
  · exact B561839
  · exact B561843
  · exact B561847
  · exact B561851
  · exact B561855
  · exact B561859
  · exact B561863
  · exact B561867
  · exact B561871
  · exact B561875
  · exact B561879
  · exact B561883
  · exact B561887
  · exact B561891
  · exact B561895
  · exact B561899
  · exact B561903
  · exact B561907
  · exact B561911
  · exact B561915
  · exact B561919
  · exact B561923
  · exact B561927
  · exact B561931
  · exact B561935
  · exact B561939
  · exact B561943
  · exact B561947
  · exact B561951
  · exact B561955
  · exact B561959
  · exact B561963
  · exact B561967
  · exact B561971
  · exact B561975
  · exact B561979
  · exact B561983
  · exact B561987
  · exact B561991
  · exact B561995
  · exact B561999
  · exact B562003
  · exact B562007
  · exact B562011
  · exact B562015
  · exact B562019
  · exact B562023
  · exact B562027
  · exact B562031
  · exact B562035
  · exact B562039
  · exact B562043
  · exact B562047
  · exact B562051
  · exact B562055
  · exact B562059
  · exact B562063
  · exact B562067
  · exact B562071
  · exact B562075
  · exact B562079
  · exact B562083
  · exact B562087
  · exact B562091
  · exact B562095
  · exact B562099
  · exact B562103
  · exact B562107
  · exact B562111
  · exact B562115
  · exact B562119
  · exact B562123
  · exact B562127
  · exact B562131
  · exact B562135
  · exact B562139
  · exact B562143
  · exact B562147
  · exact B562151
  · exact B562155
  · exact B562159
  · exact B562163
  · exact B562167
  · exact B562171
  · exact B562175
  · exact B562179
  · exact B562183
  · exact B562187
  · exact B562191
  · exact B562195
  · exact B562199
  · exact B562203
  · exact B562207
  · exact B562211
  · exact B562215
  · exact B562219
  · exact B562223
  · exact B562227
  · exact B562231
  · exact B562235
  · exact B562239
  · exact B562243
  · exact B562247
  · exact B562251
  · exact B562255
  · exact B562259
  · exact B562263
  · exact B562267
  · exact B562271
  · exact B562275
  · exact B562279
  · exact B562283
  · exact B562287
  · exact B562291
  · exact B562295
  · exact B562299
  · exact B562303
  · exact B562307
  · exact B562311
  · exact B562315
  · exact B562319
  · exact B562323
  · exact B562327
  · exact B562331
  · exact B562335
  · exact B562339
  · exact B562343
  · exact B562347
  · exact B562351
  · exact B562355
  · exact B562359
  · exact B562363
  · exact B562367
  · exact B562371
  · exact B562375
  · exact B562379
  · exact B562383
  · exact B562387
  · exact B562391
  · exact B562395
  · exact B562399
  · exact B562403
  · exact B562407
  · exact B562411
  · exact B562415
  · exact B562419
  · exact B562423
  · exact B562427
  · exact B562431
  · exact B562435
  · exact B562439
  · exact B562443
  · exact B562447
  · exact B562451
  · exact B562455
  · exact B562459
  · exact B562463
  · exact B562467
  · exact B562471
  · exact B562475
  · exact B562479
  · exact B562483
  · exact B562487
  · exact B562491
  · exact B562495
  · exact B562499
  · exact B562503
  · exact B562507
  · exact B562511
  · exact B562515
  · exact B562519
  · exact B562523
  · exact B562527
  · exact B562531
  · exact B562535
  · exact B562539
  · exact B562543
  · exact B562547
  · exact B562551
  · exact B562555
  · exact B562559
  · exact B562563
  · exact B562567
  · exact B562571
  · exact B562575
  · exact B562579
  · exact B562583
  · exact B562587
  · exact B562591
  · exact B562595
  · exact B562599
  · exact B562603
  · exact B562607
  · exact B562611
  · exact B562615
  · exact B562619
  · exact B562623
  · exact B562627
  · exact B562631
  · exact B562635
  · exact B562639
  · exact B562643
  · exact B562647
  · exact B562651
  · exact B562655
  · exact B562659
  · exact B562663
  · exact B562667
  · exact B562671
  · exact B562675
  · exact B562679
  · exact B562683
  · exact B562687
  · exact B562691
  · exact B562695
  · exact B562699
  · exact B562703
  · exact B562707
  · exact B562711
  · exact B562715
  · exact B562719
  · exact B562723
  · exact B562727
  · exact B562731
  · exact B562735
  · exact B562739
  · exact B562743
  · exact B562747
  · exact B562751
  · exact B562755
  · exact B562759
  · exact B562763
  · exact B562767
  · exact B562771
  · exact B562775
  · exact B562779
  · exact B562783
  · exact B562787
  · exact B562791
  · exact B562795
  · exact B562799
  · exact B562803
  · exact B562807

theorem solution (m : ℕ) (hlo : 558808 ≤ m) (hhi : m ≤ 562808) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 139702 ≤ j := by omega
    have hj2 : j ≤ 140701 := by omega
    have hb : Blo 558808 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 140402 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
