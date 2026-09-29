-- Prove2me | solution 1 for syracuse_descends_range_1236436_1238436
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:07.16803+00:00
-- url     : https://prove2.me/submissions/551321e9-2248-4aef-b6e2-0be7ad84fc40

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


theorem B4177925 : Blo 1236436 4177925 := bbase (se 4 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 4177925 = 783361) (by norm_num)
theorem B2785301 : Blo 1236436 2785301 := bbase (se 6 (by rfl) ⟨65280, by rfl⟩ : syracuseStep 2785301 = 130561) (by norm_num)
theorem B1392673 : Blo 1236436 1392673 := bbase (se 2 (by rfl) ⟨522252, by rfl⟩ : syracuseStep 1392673 = 1044505) (by norm_num)
theorem B10027061 : Blo 1236436 10027061 := bbase (se 5 (by rfl) ⟨470018, by rfl⟩ : syracuseStep 10027061 = 940037) (by norm_num)
theorem B3964997 : Blo 1236436 3964997 := bbase (se 4 (by rfl) ⟨371718, by rfl⟩ : syracuseStep 3964997 = 743437) (by norm_num)
theorem B1392709 : Blo 1236436 1392709 := bbase (se 4 (by rfl) ⟨130566, by rfl⟩ : syracuseStep 1392709 = 261133) (by norm_num)
theorem B2089037 : Blo 1236436 2089037 := bbase (se 3 (by rfl) ⟨391694, by rfl⟩ : syracuseStep 2089037 = 783389) (by norm_num)
theorem B2785373 : Blo 1236436 2785373 := bbase (se 3 (by rfl) ⟨522257, by rfl⟩ : syracuseStep 2785373 = 1044515) (by norm_num)
theorem B1392745 : Blo 1236436 1392745 := bbase (se 2 (by rfl) ⟨522279, by rfl⟩ : syracuseStep 1392745 = 1044559) (by norm_num)
theorem B1392781 : Blo 1236436 1392781 := bbase (se 3 (by rfl) ⟨261146, by rfl⟩ : syracuseStep 1392781 = 522293) (by norm_num)
theorem B2785445 : Blo 1236436 2785445 := bbase (se 4 (by rfl) ⟨261135, by rfl⟩ : syracuseStep 2785445 = 522271) (by norm_num)
theorem B1392817 : Blo 1236436 1392817 := bbase (se 2 (by rfl) ⟨522306, by rfl⟩ : syracuseStep 1392817 = 1044613) (by norm_num)
theorem B2089165 : Blo 1236436 2089165 := bbase (se 3 (by rfl) ⟨391718, by rfl⟩ : syracuseStep 2089165 = 783437) (by norm_num)
theorem B1392853 : Blo 1236436 1392853 := bbase (se 7 (by rfl) ⟨16322, by rfl⟩ : syracuseStep 1392853 = 32645) (by norm_num)
theorem B2785517 : Blo 1236436 2785517 := bbase (se 3 (by rfl) ⟨522284, by rfl⟩ : syracuseStep 2785517 = 1044569) (by norm_num)
theorem B1392889 : Blo 1236436 1392889 := bbase (se 2 (by rfl) ⟨522333, by rfl⟩ : syracuseStep 1392889 = 1044667) (by norm_num)
theorem B1392925 : Blo 1236436 1392925 := bbase (se 3 (by rfl) ⟨261173, by rfl⟩ : syracuseStep 1392925 = 522347) (by norm_num)
theorem B2089253 : Blo 1236436 2089253 := bbase (se 4 (by rfl) ⟨195867, by rfl⟩ : syracuseStep 2089253 = 391735) (by norm_num)
theorem B2785589 : Blo 1236436 2785589 := bbase (se 5 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 2785589 = 261149) (by norm_num)
theorem B1392961 : Blo 1236436 1392961 := bbase (se 2 (by rfl) ⟨522360, by rfl⟩ : syracuseStep 1392961 = 1044721) (by norm_num)
theorem B1565021 : Blo 1236436 1565021 := bbase (se 3 (by rfl) ⟨293441, by rfl⟩ : syracuseStep 1565021 = 586883) (by norm_num)
theorem B1392997 : Blo 1236436 1392997 := bbase (se 4 (by rfl) ⟨130593, by rfl⟩ : syracuseStep 1392997 = 261187) (by norm_num)
theorem B2785661 : Blo 1236436 2785661 := bbase (se 3 (by rfl) ⟨522311, by rfl⟩ : syracuseStep 2785661 = 1044623) (by norm_num)
theorem B1393033 : Blo 1236436 1393033 := bbase (se 2 (by rfl) ⟨522387, by rfl⟩ : syracuseStep 1393033 = 1044775) (by norm_num)
theorem B3129749 : Blo 1236436 3129749 := bbase (se 6 (by rfl) ⟨73353, by rfl⟩ : syracuseStep 3129749 = 146707) (by norm_num)
theorem B1565077 : Blo 1236436 1565077 := bbase (se 6 (by rfl) ⟨36681, by rfl⟩ : syracuseStep 1565077 = 73363) (by norm_num)
theorem B2089381 : Blo 1236436 2089381 := bbase (se 4 (by rfl) ⟨195879, by rfl⟩ : syracuseStep 2089381 = 391759) (by norm_num)
theorem B1393069 : Blo 1236436 1393069 := bbase (se 3 (by rfl) ⟨261200, by rfl⟩ : syracuseStep 1393069 = 522401) (by norm_num)
theorem B2974133 : Blo 1236436 2974133 := bbase (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) (by norm_num)
theorem B4178357 : Blo 1236436 4178357 := bbase (se 5 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 4178357 = 391721) (by norm_num)
theorem B1982909 : Blo 1236436 1982909 := bbase (se 3 (by rfl) ⟨371795, by rfl⟩ : syracuseStep 1982909 = 743591) (by norm_num)
theorem B2785733 : Blo 1236436 2785733 := bbase (se 4 (by rfl) ⟨261162, by rfl⟩ : syracuseStep 2785733 = 522325) (by norm_num)
theorem B2507213 : Blo 1236436 2507213 := bbase (se 3 (by rfl) ⟨470102, by rfl⟩ : syracuseStep 2507213 = 940205) (by norm_num)
theorem B1393105 : Blo 1236436 1393105 := bbase (se 2 (by rfl) ⟨522414, by rfl⟩ : syracuseStep 1393105 = 1044829) (by norm_num)
theorem B1565173 : Blo 1236436 1565173 := bbase (se 5 (by rfl) ⟨73367, by rfl⟩ : syracuseStep 1565173 = 146735) (by norm_num)
theorem B1393141 : Blo 1236436 1393141 := bbase (se 5 (by rfl) ⟨65303, by rfl⟩ : syracuseStep 1393141 = 130607) (by norm_num)
theorem B2089469 : Blo 1236436 2089469 := bbase (se 3 (by rfl) ⟨391775, by rfl⟩ : syracuseStep 2089469 = 783551) (by norm_num)
theorem B2785805 : Blo 1236436 2785805 := bbase (se 3 (by rfl) ⟨522338, by rfl⟩ : syracuseStep 2785805 = 1044677) (by norm_num)
theorem B1393177 : Blo 1236436 1393177 := bbase (se 2 (by rfl) ⟨522441, by rfl⟩ : syracuseStep 1393177 = 1044883) (by norm_num)
theorem B1983037 : Blo 1236436 1983037 := bbase (se 3 (by rfl) ⟨371819, by rfl⟩ : syracuseStep 1983037 = 743639) (by norm_num)
theorem B1393213 : Blo 1236436 1393213 := bbase (se 3 (by rfl) ⟨261227, by rfl⟩ : syracuseStep 1393213 = 522455) (by norm_num)
theorem B3129941 : Blo 1236436 3129941 := bbase (se 8 (by rfl) ⟨18339, by rfl⟩ : syracuseStep 3129941 = 36679) (by norm_num)
theorem B2785877 : Blo 1236436 2785877 := bbase (se 8 (by rfl) ⟨16323, by rfl⟩ : syracuseStep 2785877 = 32647) (by norm_num)
theorem B3523189 : Blo 1236436 3523189 := bbase (se 5 (by rfl) ⟨165149, by rfl⟩ : syracuseStep 3523189 = 330299) (by norm_num)
theorem B2089597 : Blo 1236436 2089597 := bbase (se 3 (by rfl) ⟨391799, by rfl⟩ : syracuseStep 2089597 = 783599) (by norm_num)
theorem B1761925 : Blo 1236436 1761925 := bbase (se 4 (by rfl) ⟨165180, by rfl⟩ : syracuseStep 1761925 = 330361) (by norm_num)
theorem B2785949 : Blo 1236436 2785949 := bbase (se 3 (by rfl) ⟨522365, by rfl⟩ : syracuseStep 2785949 = 1044731) (by norm_num)
theorem B1565345 : Blo 1236436 1565345 := bbase (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) (by norm_num)
theorem B2089685 : Blo 1236436 2089685 := bbase (se 7 (by rfl) ⟨24488, by rfl⟩ : syracuseStep 2089685 = 48977) (by norm_num)
theorem B1565401 : Blo 1236436 1565401 := bbase (se 2 (by rfl) ⟨587025, by rfl⟩ : syracuseStep 1565401 = 1174051) (by norm_num)
theorem B2786021 : Blo 1236436 2786021 := bbase (se 4 (by rfl) ⟨261189, by rfl⟩ : syracuseStep 2786021 = 522379) (by norm_num)
theorem B1254125 : Blo 1236436 1254125 := bbase (se 3 (by rfl) ⟨235148, by rfl⟩ : syracuseStep 1254125 = 470297) (by norm_num)
theorem B2786093 : Blo 1236436 2786093 := bbase (se 3 (by rfl) ⟨522392, by rfl⟩ : syracuseStep 2786093 = 1044785) (by norm_num)
theorem B1565497 : Blo 1236436 1565497 := bbase (se 2 (by rfl) ⟨587061, by rfl⟩ : syracuseStep 1565497 = 1174123) (by norm_num)
theorem B2089813 : Blo 1236436 2089813 := bbase (se 9 (by rfl) ⟨6122, by rfl⟩ : syracuseStep 2089813 = 12245) (by norm_num)
theorem B4178789 : Blo 1236436 4178789 := bbase (se 4 (by rfl) ⟨391761, by rfl⟩ : syracuseStep 4178789 = 783523) (by norm_num)
theorem B2786165 : Blo 1236436 2786165 := bbase (se 5 (by rfl) ⟨130601, by rfl⟩ : syracuseStep 2786165 = 261203) (by norm_num)
theorem B3130285 : Blo 1236436 3130285 := bbase (se 3 (by rfl) ⟨586928, by rfl⟩ : syracuseStep 3130285 = 1173857) (by norm_num)
theorem B2786237 : Blo 1236436 2786237 := bbase (se 3 (by rfl) ⟨522419, by rfl⟩ : syracuseStep 2786237 = 1044839) (by norm_num)
theorem B1565669 : Blo 1236436 1565669 := bbase (se 4 (by rfl) ⟨146781, by rfl⟩ : syracuseStep 1565669 = 293563) (by norm_num)
theorem B2786309 : Blo 1236436 2786309 := bbase (se 4 (by rfl) ⟨261216, by rfl⟩ : syracuseStep 2786309 = 522433) (by norm_num)
theorem B3130397 : Blo 1236436 3130397 := bbase (se 3 (by rfl) ⟨586949, by rfl⟩ : syracuseStep 3130397 = 1173899) (by norm_num)
theorem B1565725 : Blo 1236436 1565725 := bbase (se 3 (by rfl) ⟨293573, by rfl⟩ : syracuseStep 1565725 = 587147) (by norm_num)
theorem B6267941 : Blo 1236436 6267941 := bbase (se 4 (by rfl) ⟨587619, by rfl⟩ : syracuseStep 6267941 = 1175239) (by norm_num)
theorem B2786381 : Blo 1236436 2786381 := bbase (se 3 (by rfl) ⟨522446, by rfl⟩ : syracuseStep 2786381 = 1044893) (by norm_num)
theorem B1565821 : Blo 1236436 1565821 := bbase (se 3 (by rfl) ⟨293591, by rfl⟩ : syracuseStep 1565821 = 587183) (by norm_num)
theorem B2786453 : Blo 1236436 2786453 := bbase (se 6 (by rfl) ⟨65307, by rfl⟩ : syracuseStep 2786453 = 130615) (by norm_num)
theorem B2974901 : Blo 1236436 2974901 := bbase (se 5 (by rfl) ⟨139448, by rfl⟩ : syracuseStep 2974901 = 278897) (by norm_num)
theorem B2507965 : Blo 1236436 2507965 := bbase (se 3 (by rfl) ⟨470243, by rfl⟩ : syracuseStep 2507965 = 940487) (by norm_num)
theorem B1762517 : Blo 1236436 1762517 := bbase (se 7 (by rfl) ⟨20654, by rfl⟩ : syracuseStep 1762517 = 41309) (by norm_num)
theorem B10175701 : Blo 1236436 10175701 := bbase (se 7 (by rfl) ⟨119246, by rfl⟩ : syracuseStep 10175701 = 238493) (by norm_num)
theorem B3130589 : Blo 1236436 3130589 := bbase (se 3 (by rfl) ⟨586985, by rfl⟩ : syracuseStep 3130589 = 1173971) (by norm_num)
theorem B4179221 : Blo 1236436 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B2229533 : Blo 1236436 2229533 := bbase (se 3 (by rfl) ⟨418037, by rfl⟩ : syracuseStep 2229533 = 836075) (by norm_num)
theorem B1762597 : Blo 1236436 1762597 := bbase (se 4 (by rfl) ⟨165243, by rfl⟩ : syracuseStep 1762597 = 330487) (by norm_num)
theorem B1565993 : Blo 1236436 1565993 := bbase (se 2 (by rfl) ⟨587247, by rfl⟩ : syracuseStep 1565993 = 1174495) (by norm_num)
theorem B1410385 : Blo 1236436 1410385 := bbase (se 2 (by rfl) ⟨528894, by rfl⟩ : syracuseStep 1410385 = 1057789) (by norm_num)
theorem B1566049 : Blo 1236436 1566049 := bbase (se 2 (by rfl) ⟨587268, by rfl⟩ : syracuseStep 1566049 = 1174537) (by norm_num)
theorem B1271149 : Blo 1236436 1271149 := bbase (se 3 (by rfl) ⟨238340, by rfl⟩ : syracuseStep 1271149 = 476681) (by norm_num)
theorem B6686069 : Blo 1236436 6686069 := bbase (se 5 (by rfl) ⟨313409, by rfl⟩ : syracuseStep 6686069 = 626819) (by norm_num)
theorem B1762717 : Blo 1236436 1762717 := bbase (se 3 (by rfl) ⟨330509, by rfl⟩ : syracuseStep 1762717 = 661019) (by norm_num)
theorem B3343781 : Blo 1236436 3343781 := bbase (se 4 (by rfl) ⟨313479, by rfl⟩ : syracuseStep 3343781 = 626959) (by norm_num)
theorem B2680229 : Blo 1236436 2680229 := bbase (se 4 (by rfl) ⟨251271, by rfl⟩ : syracuseStep 2680229 = 502543) (by norm_num)
theorem B1566145 : Blo 1236436 1566145 := bbase (se 2 (by rfl) ⟨587304, by rfl⟩ : syracuseStep 1566145 = 1174609) (by norm_num)
theorem B6260165 : Blo 1236436 6260165 := bbase (se 4 (by rfl) ⟨586890, by rfl⟩ : syracuseStep 6260165 = 1173781) (by norm_num)
theorem B4294085 : Blo 1236436 4294085 := bbase (se 4 (by rfl) ⟨402570, by rfl⟩ : syracuseStep 4294085 = 805141) (by norm_num)
theorem B3966421 : Blo 1236436 3966421 := bbase (se 7 (by rfl) ⟨46481, by rfl⟩ : syracuseStep 3966421 = 92963) (by norm_num)
theorem B12699125 : Blo 1236436 12699125 := bbase (se 5 (by rfl) ⟨595271, by rfl⟩ : syracuseStep 12699125 = 1190543) (by norm_num)
theorem B1762813 : Blo 1236436 1762813 := bbase (se 3 (by rfl) ⟨330527, by rfl⟩ : syracuseStep 1762813 = 661055) (by norm_num)
theorem B2115077 : Blo 1236436 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B9397781 : Blo 1236436 9397781 := bbase (se 6 (by rfl) ⟨220260, by rfl⟩ : syracuseStep 9397781 = 440521) (by norm_num)
theorem B3130933 : Blo 1236436 3130933 := bbase (se 5 (by rfl) ⟨146762, by rfl⟩ : syracuseStep 3130933 = 293525) (by norm_num)
theorem B1320521 : Blo 1236436 1320521 := bbase (se 2 (by rfl) ⟨495195, by rfl⟩ : syracuseStep 1320521 = 990391) (by norm_num)
theorem B1566317 : Blo 1236436 1566317 := bbase (se 3 (by rfl) ⟨293684, by rfl⟩ : syracuseStep 1566317 = 587369) (by norm_num)
theorem B1320581 : Blo 1236436 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B3131045 : Blo 1236436 3131045 := bbase (se 4 (by rfl) ⟨293535, by rfl⟩ : syracuseStep 3131045 = 587071) (by norm_num)
theorem B1566373 : Blo 1236436 1566373 := bbase (se 4 (by rfl) ⟨146847, by rfl⟩ : syracuseStep 1566373 = 293695) (by norm_num)
theorem B4179653 : Blo 1236436 4179653 := bbase (se 4 (by rfl) ⟨391842, by rfl⟩ : syracuseStep 4179653 = 783685) (by norm_num)
theorem B6694613 : Blo 1236436 6694613 := bbase (se 7 (by rfl) ⟨78452, by rfl⟩ : syracuseStep 6694613 = 156905) (by norm_num)
theorem B1320709 : Blo 1236436 1320709 := bbase (se 4 (by rfl) ⟨123816, by rfl⟩ : syracuseStep 1320709 = 247633) (by norm_num)
theorem B1566469 : Blo 1236436 1566469 := bbase (se 4 (by rfl) ⟨146856, by rfl⟩ : syracuseStep 1566469 = 293713) (by norm_num)
theorem B3131237 : Blo 1236436 3131237 := bbase (se 4 (by rfl) ⟨293553, by rfl⟩ : syracuseStep 3131237 = 587107) (by norm_num)
theorem B3966869 : Blo 1236436 3966869 := bbase (se 6 (by rfl) ⟨92973, by rfl⟩ : syracuseStep 3966869 = 185947) (by norm_num)
theorem B3762085 : Blo 1236436 3762085 := bbase (se 4 (by rfl) ⟨352695, by rfl⟩ : syracuseStep 3762085 = 705391) (by norm_num)
theorem B1566641 : Blo 1236436 1566641 := bbase (se 2 (by rfl) ⟨587490, by rfl⟩ : syracuseStep 1566641 = 1174981) (by norm_num)
theorem B9390005 : Blo 1236436 9390005 := bbase (se 5 (by rfl) ⟨440156, by rfl⟩ : syracuseStep 9390005 = 880313) (by norm_num)
theorem B1566697 : Blo 1236436 1566697 := bbase (se 2 (by rfl) ⟨587511, by rfl⟩ : syracuseStep 1566697 = 1175023) (by norm_num)
theorem B1763309 : Blo 1236436 1763309 := bbase (se 3 (by rfl) ⟨330620, by rfl⟩ : syracuseStep 1763309 = 661241) (by norm_num)
theorem B2820149 : Blo 1236436 2820149 := bbase (se 5 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 2820149 = 264389) (by norm_num)
theorem B1566793 : Blo 1236436 1566793 := bbase (se 2 (by rfl) ⟨587547, by rfl⟩ : syracuseStep 1566793 = 1175095) (by norm_num)
theorem B3131581 : Blo 1236436 3131581 := bbase (se 3 (by rfl) ⟨587171, by rfl⟩ : syracuseStep 3131581 = 1174343) (by norm_num)
theorem B1321153 : Blo 1236436 1321153 := bbase (se 2 (by rfl) ⟨495432, by rfl⟩ : syracuseStep 1321153 = 990865) (by norm_num)
theorem B1566965 : Blo 1236436 1566965 := bbase (se 5 (by rfl) ⟨73451, by rfl⟩ : syracuseStep 1566965 = 146903) (by norm_num)
theorem B4696325 : Blo 1236436 4696325 := bbase (se 4 (by rfl) ⟨440280, by rfl⟩ : syracuseStep 4696325 = 880561) (by norm_num)
theorem B2509093 : Blo 1236436 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B3131693 : Blo 1236436 3131693 := bbase (se 3 (by rfl) ⟨587192, by rfl⟩ : syracuseStep 3131693 = 1174385) (by norm_num)
theorem B1567021 : Blo 1236436 1567021 := bbase (se 3 (by rfl) ⟨293816, by rfl⟩ : syracuseStep 1567021 = 587633) (by norm_num)
theorem B6269237 : Blo 1236436 6269237 := bbase (se 5 (by rfl) ⟨293870, by rfl⟩ : syracuseStep 6269237 = 587741) (by norm_num)
theorem B1321273 : Blo 1236436 1321273 := bbase (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) (by norm_num)
theorem B2509165 : Blo 1236436 2509165 := bbase (se 3 (by rfl) ⟨470468, by rfl⟩ : syracuseStep 2509165 = 940937) (by norm_num)
theorem B1567117 : Blo 1236436 1567117 := bbase (se 3 (by rfl) ⟨293834, by rfl⟩ : syracuseStep 1567117 = 587669) (by norm_num)
theorem B3131885 : Blo 1236436 3131885 := bbase (se 3 (by rfl) ⟨587228, by rfl⟩ : syracuseStep 3131885 = 1174457) (by norm_num)
theorem B3574277 : Blo 1236436 3574277 := bbase (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) (by norm_num)
theorem B4696613 : Blo 1236436 4696613 := bbase (se 4 (by rfl) ⟨440307, by rfl⟩ : syracuseStep 4696613 = 880615) (by norm_num)
theorem B1411625 : Blo 1236436 1411625 := bbase (se 2 (by rfl) ⟨529359, by rfl⟩ : syracuseStep 1411625 = 1058719) (by norm_num)
theorem B1321525 : Blo 1236436 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B1321529 : Blo 1236436 1321529 := bbase (se 2 (by rfl) ⟨495573, by rfl⟩ : syracuseStep 1321529 = 991147) (by norm_num)
theorem B1567289 : Blo 1236436 1567289 := bbase (se 2 (by rfl) ⟨587733, by rfl⟩ : syracuseStep 1567289 = 1175467) (by norm_num)
theorem B1567345 : Blo 1236436 1567345 := bbase (se 2 (by rfl) ⟨587754, by rfl⟩ : syracuseStep 1567345 = 1175509) (by norm_num)
theorem B2714269 : Blo 1236436 2714269 := bbase (se 3 (by rfl) ⟨508925, by rfl⟩ : syracuseStep 2714269 = 1017851) (by norm_num)
theorem B6261461 : Blo 1236436 6261461 := bbase (se 7 (by rfl) ⟨73376, by rfl⟩ : syracuseStep 6261461 = 146753) (by norm_num)
theorem B1485577 : Blo 1236436 1485577 := bbase (se 2 (by rfl) ⟨557091, by rfl⟩ : syracuseStep 1485577 = 1114183) (by norm_num)
theorem B2231077 : Blo 1236436 2231077 := bbase (se 4 (by rfl) ⟨209163, by rfl⟩ : syracuseStep 2231077 = 418327) (by norm_num)
theorem B3132229 : Blo 1236436 3132229 := bbase (se 4 (by rfl) ⟨293646, by rfl⟩ : syracuseStep 3132229 = 587293) (by norm_num)
theorem B3763093 : Blo 1236436 3763093 := bbase (se 6 (by rfl) ⟨88197, by rfl⟩ : syracuseStep 3763093 = 176395) (by norm_num)
theorem B1608617 : Blo 1236436 1608617 := bbase (se 2 (by rfl) ⟨603231, by rfl⟩ : syracuseStep 1608617 = 1206463) (by norm_num)
theorem B3132341 : Blo 1236436 3132341 := bbase (se 5 (by rfl) ⟨146828, by rfl⟩ : syracuseStep 3132341 = 293657) (by norm_num)
theorem B5286869 : Blo 1236436 5286869 := bbase (se 7 (by rfl) ⟨61955, by rfl⟩ : syracuseStep 5286869 = 123911) (by norm_num)
theorem B7932917 : Blo 1236436 7932917 := bbase (se 5 (by rfl) ⟨371855, by rfl⟩ : syracuseStep 7932917 = 743711) (by norm_num)
theorem B5016629 : Blo 1236436 5016629 := bbase (se 5 (by rfl) ⟨235154, by rfl⟩ : syracuseStep 5016629 = 470309) (by norm_num)
theorem B1485913 : Blo 1236436 1485913 := bbase (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) (by norm_num)
theorem B1322093 : Blo 1236436 1322093 := bbase (se 3 (by rfl) ⟨247892, by rfl⟩ : syracuseStep 1322093 = 495785) (by norm_num)
theorem B3132533 : Blo 1236436 3132533 := bbase (se 5 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 3132533 = 293675) (by norm_num)
theorem B1412245 : Blo 1236436 1412245 := bbase (se 6 (by rfl) ⟨33099, by rfl⟩ : syracuseStep 1412245 = 66199) (by norm_num)
theorem B5016773 : Blo 1236436 5016773 := bbase (se 4 (by rfl) ⟨470322, by rfl⟩ : syracuseStep 5016773 = 940645) (by norm_num)
theorem B1854677 : Blo 1236436 1854677 := bbase (se 7 (by rfl) ⟨21734, by rfl⟩ : syracuseStep 1854677 = 43469) (by norm_num)
theorem B1854701 : Blo 1236436 1854701 := bbase (se 3 (by rfl) ⟨347756, by rfl⟩ : syracuseStep 1854701 = 695513) (by norm_num)
theorem B1854725 : Blo 1236436 1854725 := bbase (se 4 (by rfl) ⟨173880, by rfl⟩ : syracuseStep 1854725 = 347761) (by norm_num)
theorem B1854749 : Blo 1236436 1854749 := bbase (se 3 (by rfl) ⟨347765, by rfl⟩ : syracuseStep 1854749 = 695531) (by norm_num)
theorem B1322281 : Blo 1236436 1322281 := bbase (se 2 (by rfl) ⟨495855, by rfl⟩ : syracuseStep 1322281 = 991711) (by norm_num)
theorem B1854773 : Blo 1236436 1854773 := bbase (se 5 (by rfl) ⟨86942, by rfl⟩ : syracuseStep 1854773 = 173885) (by norm_num)
theorem B1854797 : Blo 1236436 1854797 := bbase (se 3 (by rfl) ⟨347774, by rfl⟩ : syracuseStep 1854797 = 695549) (by norm_num)
theorem B1854821 : Blo 1236436 1854821 := bbase (se 4 (by rfl) ⟨173889, by rfl⟩ : syracuseStep 1854821 = 347779) (by norm_num)
theorem B4173173 : Blo 1236436 4173173 := bbase (se 5 (by rfl) ⟨195617, by rfl⟩ : syracuseStep 4173173 = 391235) (by norm_num)
theorem B7048565 : Blo 1236436 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B1854845 : Blo 1236436 1854845 := bbase (se 3 (by rfl) ⟨347783, by rfl⟩ : syracuseStep 1854845 = 695567) (by norm_num)
theorem B1854869 : Blo 1236436 1854869 := bbase (se 6 (by rfl) ⟨43473, by rfl⟩ : syracuseStep 1854869 = 86947) (by norm_num)
theorem B3526037 : Blo 1236436 3526037 := bbase (se 6 (by rfl) ⟨82641, by rfl⟩ : syracuseStep 3526037 = 165283) (by norm_num)
theorem B1854893 : Blo 1236436 1854893 := bbase (se 3 (by rfl) ⟨347792, by rfl⟩ : syracuseStep 1854893 = 695585) (by norm_num)
theorem B1854917 : Blo 1236436 1854917 := bbase (se 4 (by rfl) ⟨173898, by rfl⟩ : syracuseStep 1854917 = 347797) (by norm_num)
theorem B3132877 : Blo 1236436 3132877 := bbase (se 3 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 3132877 = 1174829) (by norm_num)
theorem B1854941 : Blo 1236436 1854941 := bbase (se 3 (by rfl) ⟨347801, by rfl⟩ : syracuseStep 1854941 = 695603) (by norm_num)
theorem B1854965 : Blo 1236436 1854965 := bbase (se 5 (by rfl) ⟨86951, by rfl⟩ : syracuseStep 1854965 = 173903) (by norm_num)
theorem B1609205 : Blo 1236436 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B2510333 : Blo 1236436 2510333 := bbase (se 3 (by rfl) ⟨470687, by rfl⟩ : syracuseStep 2510333 = 941375) (by norm_num)
theorem B1854989 : Blo 1236436 1854989 := bbase (se 3 (by rfl) ⟨347810, by rfl⟩ : syracuseStep 1854989 = 695621) (by norm_num)
theorem B1855013 : Blo 1236436 1855013 := bbase (se 4 (by rfl) ⟨173907, by rfl⟩ : syracuseStep 1855013 = 347815) (by norm_num)
theorem B1855037 : Blo 1236436 1855037 := bbase (se 3 (by rfl) ⟨347819, by rfl⟩ : syracuseStep 1855037 = 695639) (by norm_num)
theorem B3132989 : Blo 1236436 3132989 := bbase (se 3 (by rfl) ⟨587435, by rfl⟩ : syracuseStep 3132989 = 1174871) (by norm_num)
theorem B1855061 : Blo 1236436 1855061 := bbase (se 8 (by rfl) ⟨10869, by rfl⟩ : syracuseStep 1855061 = 21739) (by norm_num)
theorem B1855085 : Blo 1236436 1855085 := bbase (se 3 (by rfl) ⟨347828, by rfl⟩ : syracuseStep 1855085 = 695657) (by norm_num)
theorem B1855109 : Blo 1236436 1855109 := bbase (se 4 (by rfl) ⟨173916, by rfl⟩ : syracuseStep 1855109 = 347833) (by norm_num)
theorem B1855133 : Blo 1236436 1855133 := bbase (se 3 (by rfl) ⟨347837, by rfl⟩ : syracuseStep 1855133 = 695675) (by norm_num)
theorem B1855157 : Blo 1236436 1855157 := bbase (se 5 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 1855157 = 173921) (by norm_num)
theorem B2641589 : Blo 1236436 2641589 := bbase (se 5 (by rfl) ⟨123824, by rfl⟩ : syracuseStep 2641589 = 247649) (by norm_num)
theorem B4697797 : Blo 1236436 4697797 := bbase (se 4 (by rfl) ⟨440418, by rfl⟩ : syracuseStep 4697797 = 880837) (by norm_num)
theorem B1855181 : Blo 1236436 1855181 := bbase (se 3 (by rfl) ⟨347846, by rfl⟩ : syracuseStep 1855181 = 695693) (by norm_num)
theorem B1855205 : Blo 1236436 1855205 := bbase (se 4 (by rfl) ⟨173925, by rfl⟩ : syracuseStep 1855205 = 347851) (by norm_num)
theorem B7147253 : Blo 1236436 7147253 := bbase (se 5 (by rfl) ⟨335027, by rfl⟩ : syracuseStep 7147253 = 670055) (by norm_num)
theorem B1855229 : Blo 1236436 1855229 := bbase (se 3 (by rfl) ⟨347855, by rfl⟩ : syracuseStep 1855229 = 695711) (by norm_num)
theorem B3133181 : Blo 1236436 3133181 := bbase (se 3 (by rfl) ⟨587471, by rfl⟩ : syracuseStep 3133181 = 1174943) (by norm_num)
theorem B1855253 : Blo 1236436 1855253 := bbase (se 6 (by rfl) ⟨43482, by rfl⟩ : syracuseStep 1855253 = 86965) (by norm_num)
theorem B4173605 : Blo 1236436 4173605 := bbase (se 4 (by rfl) ⟨391275, by rfl⟩ : syracuseStep 4173605 = 782551) (by norm_num)
theorem B1855277 : Blo 1236436 1855277 := bbase (se 3 (by rfl) ⟨347864, by rfl⟩ : syracuseStep 1855277 = 695729) (by norm_num)
theorem B2641709 : Blo 1236436 2641709 := bbase (se 3 (by rfl) ⟨495320, by rfl⟩ : syracuseStep 2641709 = 990641) (by norm_num)
theorem B1855301 : Blo 1236436 1855301 := bbase (se 4 (by rfl) ⟨173934, by rfl⟩ : syracuseStep 1855301 = 347869) (by norm_num)
theorem B76156757 : Blo 1236436 76156757 := bbase (se 9 (by rfl) ⟨223115, by rfl⟩ : syracuseStep 76156757 = 446231) (by norm_num)
theorem B1855325 : Blo 1236436 1855325 := bbase (se 3 (by rfl) ⟨347873, by rfl⟩ : syracuseStep 1855325 = 695747) (by norm_num)
theorem B1855349 : Blo 1236436 1855349 := bbase (se 5 (by rfl) ⟨86969, by rfl⟩ : syracuseStep 1855349 = 173939) (by norm_num)
theorem B2379653 : Blo 1236436 2379653 := bbase (se 4 (by rfl) ⟨223092, by rfl⟩ : syracuseStep 2379653 = 446185) (by norm_num)
theorem B1855373 : Blo 1236436 1855373 := bbase (se 3 (by rfl) ⟨347882, by rfl⟩ : syracuseStep 1855373 = 695765) (by norm_num)
theorem B2543501 : Blo 1236436 2543501 := bbase (se 3 (by rfl) ⟨476906, by rfl⟩ : syracuseStep 2543501 = 953813) (by norm_num)
theorem B1855397 : Blo 1236436 1855397 := bbase (se 4 (by rfl) ⟨173943, by rfl⟩ : syracuseStep 1855397 = 347887) (by norm_num)
theorem B6352805 : Blo 1236436 6352805 := bbase (se 4 (by rfl) ⟨595575, by rfl⟩ : syracuseStep 6352805 = 1191151) (by norm_num)
theorem B2379709 : Blo 1236436 2379709 := bbase (se 3 (by rfl) ⟨446195, by rfl⟩ : syracuseStep 2379709 = 892391) (by norm_num)
theorem B1855421 : Blo 1236436 1855421 := bbase (se 3 (by rfl) ⟨347891, by rfl⟩ : syracuseStep 1855421 = 695783) (by norm_num)
theorem B1486793 : Blo 1236436 1486793 := bbase (se 2 (by rfl) ⟨557547, by rfl⟩ : syracuseStep 1486793 = 1115095) (by norm_num)
theorem B1855445 : Blo 1236436 1855445 := bbase (se 7 (by rfl) ⟨21743, by rfl⟩ : syracuseStep 1855445 = 43487) (by norm_num)
theorem B6262757 : Blo 1236436 6262757 := bbase (se 4 (by rfl) ⟨587133, by rfl⟩ : syracuseStep 6262757 = 1174267) (by norm_num)
theorem B1855469 : Blo 1236436 1855469 := bbase (se 3 (by rfl) ⟨347900, by rfl⟩ : syracuseStep 1855469 = 695801) (by norm_num)
theorem B4698101 : Blo 1236436 4698101 := bbase (se 5 (by rfl) ⟨220223, by rfl⟩ : syracuseStep 4698101 = 440447) (by norm_num)
theorem B1855493 : Blo 1236436 1855493 := bbase (se 4 (by rfl) ⟨173952, by rfl⟩ : syracuseStep 1855493 = 347905) (by norm_num)
theorem B1855517 : Blo 1236436 1855517 := bbase (se 3 (by rfl) ⟨347909, by rfl⟩ : syracuseStep 1855517 = 695819) (by norm_num)
theorem B1855541 : Blo 1236436 1855541 := bbase (se 5 (by rfl) ⟨86978, by rfl⟩ : syracuseStep 1855541 = 173957) (by norm_num)
theorem B2715709 : Blo 1236436 2715709 := bbase (se 3 (by rfl) ⟨509195, by rfl⟩ : syracuseStep 2715709 = 1018391) (by norm_num)
theorem B1855565 : Blo 1236436 1855565 := bbase (se 3 (by rfl) ⟨347918, by rfl⟩ : syracuseStep 1855565 = 695837) (by norm_num)
theorem B21139541 : Blo 1236436 21139541 := bbase (se 8 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 21139541 = 247729) (by norm_num)
theorem B10719317 : Blo 1236436 10719317 := bbase (se 8 (by rfl) ⟨62808, by rfl⟩ : syracuseStep 10719317 = 125617) (by norm_num)
theorem B3133525 : Blo 1236436 3133525 := bbase (se 8 (by rfl) ⟨18360, by rfl⟩ : syracuseStep 3133525 = 36721) (by norm_num)
theorem B1855589 : Blo 1236436 1855589 := bbase (se 4 (by rfl) ⟨173961, by rfl⟩ : syracuseStep 1855589 = 347923) (by norm_num)
theorem B1855613 : Blo 1236436 1855613 := bbase (se 3 (by rfl) ⟨347927, by rfl⟩ : syracuseStep 1855613 = 695855) (by norm_num)
theorem B1339525 : Blo 1236436 1339525 := bbase (se 4 (by rfl) ⟨125580, by rfl⟩ : syracuseStep 1339525 = 251161) (by norm_num)
theorem B1855637 : Blo 1236436 1855637 := bbase (se 6 (by rfl) ⟨43491, by rfl⟩ : syracuseStep 1855637 = 86983) (by norm_num)
theorem B14094485 : Blo 1236436 14094485 := bbase (se 6 (by rfl) ⟨330339, by rfl⟩ : syracuseStep 14094485 = 660679) (by norm_num)
theorem B1855661 : Blo 1236436 1855661 := bbase (se 3 (by rfl) ⟨347936, by rfl⟩ : syracuseStep 1855661 = 695873) (by norm_num)
theorem B1855685 : Blo 1236436 1855685 := bbase (se 4 (by rfl) ⟨173970, by rfl⟩ : syracuseStep 1855685 = 347941) (by norm_num)
theorem B3133637 : Blo 1236436 3133637 := bbase (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) (by norm_num)
theorem B4174037 : Blo 1236436 4174037 := bbase (se 7 (by rfl) ⟨48914, by rfl⟩ : syracuseStep 4174037 = 97829) (by norm_num)
theorem B1855709 : Blo 1236436 1855709 := bbase (se 3 (by rfl) ⟨347945, by rfl⟩ : syracuseStep 1855709 = 695891) (by norm_num)
theorem B1855733 : Blo 1236436 1855733 := bbase (se 5 (by rfl) ⟨86987, by rfl⟩ : syracuseStep 1855733 = 173975) (by norm_num)
theorem B1880317 : Blo 1236436 1880317 := bbase (se 3 (by rfl) ⟨352559, by rfl⟩ : syracuseStep 1880317 = 705119) (by norm_num)
theorem B1487101 : Blo 1236436 1487101 := bbase (se 3 (by rfl) ⟨278831, by rfl⟩ : syracuseStep 1487101 = 557663) (by norm_num)
theorem B1855757 : Blo 1236436 1855757 := bbase (se 3 (by rfl) ⟨347954, by rfl⟩ : syracuseStep 1855757 = 695909) (by norm_num)
theorem B1855781 : Blo 1236436 1855781 := bbase (se 4 (by rfl) ⟨173979, by rfl⟩ : syracuseStep 1855781 = 347959) (by norm_num)
theorem B1855805 : Blo 1236436 1855805 := bbase (se 3 (by rfl) ⟨347963, by rfl⟩ : syracuseStep 1855805 = 695927) (by norm_num)
theorem B1855829 : Blo 1236436 1855829 := bbase (se 10 (by rfl) ⟨2718, by rfl⟩ : syracuseStep 1855829 = 5437) (by norm_num)
theorem B2347373 : Blo 1236436 2347373 := bbase (se 3 (by rfl) ⟨440132, by rfl⟩ : syracuseStep 2347373 = 880265) (by norm_num)
theorem B1855853 : Blo 1236436 1855853 := bbase (se 3 (by rfl) ⟨347972, by rfl⟩ : syracuseStep 1855853 = 695945) (by norm_num)
theorem B1855877 : Blo 1236436 1855877 := bbase (se 4 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 1855877 = 347977) (by norm_num)
theorem B3133829 : Blo 1236436 3133829 := bbase (se 4 (by rfl) ⟨293796, by rfl⟩ : syracuseStep 3133829 = 587593) (by norm_num)
theorem B1855901 : Blo 1236436 1855901 := bbase (se 3 (by rfl) ⟨347981, by rfl⟩ : syracuseStep 1855901 = 695963) (by norm_num)
theorem B2642341 : Blo 1236436 2642341 := bbase (se 4 (by rfl) ⟨247719, by rfl⟩ : syracuseStep 2642341 = 495439) (by norm_num)
theorem B1855925 : Blo 1236436 1855925 := bbase (se 5 (by rfl) ⟨86996, by rfl⟩ : syracuseStep 1855925 = 173993) (by norm_num)
theorem B1855949 : Blo 1236436 1855949 := bbase (se 3 (by rfl) ⟨347990, by rfl⟩ : syracuseStep 1855949 = 695981) (by norm_num)
theorem B13373909 : Blo 1236436 13373909 := bbase (se 7 (by rfl) ⟨156725, by rfl⟩ : syracuseStep 13373909 = 313451) (by norm_num)
theorem B1855973 : Blo 1236436 1855973 := bbase (se 4 (by rfl) ⟨173997, by rfl⟩ : syracuseStep 1855973 = 347995) (by norm_num)
theorem B2347517 : Blo 1236436 2347517 := bbase (se 3 (by rfl) ⟨440159, by rfl⟩ : syracuseStep 2347517 = 880319) (by norm_num)
theorem B1855997 : Blo 1236436 1855997 := bbase (se 3 (by rfl) ⟨347999, by rfl⟩ : syracuseStep 1855997 = 695999) (by norm_num)
theorem B1856021 : Blo 1236436 1856021 := bbase (se 6 (by rfl) ⟨43500, by rfl⟩ : syracuseStep 1856021 = 87001) (by norm_num)
theorem B1856045 : Blo 1236436 1856045 := bbase (se 3 (by rfl) ⟨348008, by rfl⟩ : syracuseStep 1856045 = 696017) (by norm_num)
theorem B1856069 : Blo 1236436 1856069 := bbase (se 4 (by rfl) ⟨174006, by rfl⟩ : syracuseStep 1856069 = 348013) (by norm_num)
theorem B10031701 : Blo 1236436 10031701 := bbase (se 8 (by rfl) ⟨58779, by rfl⟩ : syracuseStep 10031701 = 117559) (by norm_num)
theorem B1856093 : Blo 1236436 1856093 := bbase (se 3 (by rfl) ⟨348017, by rfl⟩ : syracuseStep 1856093 = 696035) (by norm_num)
theorem B1856117 : Blo 1236436 1856117 := bbase (se 5 (by rfl) ⟨87005, by rfl⟩ : syracuseStep 1856117 = 174011) (by norm_num)
theorem B1487485 : Blo 1236436 1487485 := bbase (se 3 (by rfl) ⟨278903, by rfl⟩ : syracuseStep 1487485 = 557807) (by norm_num)
theorem B1487489 : Blo 1236436 1487489 := bbase (se 2 (by rfl) ⟨557808, by rfl⟩ : syracuseStep 1487489 = 1115617) (by norm_num)
theorem B4174469 : Blo 1236436 4174469 := bbase (se 4 (by rfl) ⟨391356, by rfl⟩ : syracuseStep 4174469 = 782713) (by norm_num)
theorem B1856141 : Blo 1236436 1856141 := bbase (se 3 (by rfl) ⟨348026, by rfl⟩ : syracuseStep 1856141 = 696053) (by norm_num)
theorem B1856165 : Blo 1236436 1856165 := bbase (se 4 (by rfl) ⟨174015, by rfl⟩ : syracuseStep 1856165 = 348031) (by norm_num)
theorem B1856189 : Blo 1236436 1856189 := bbase (se 3 (by rfl) ⟨348035, by rfl⟩ : syracuseStep 1856189 = 696071) (by norm_num)
theorem B5288645 : Blo 1236436 5288645 := bbase (se 4 (by rfl) ⟨495810, by rfl⟩ : syracuseStep 5288645 = 991621) (by norm_num)
theorem B1856213 : Blo 1236436 1856213 := bbase (se 7 (by rfl) ⟨21752, by rfl⟩ : syracuseStep 1856213 = 43505) (by norm_num)
theorem B3134173 : Blo 1236436 3134173 := bbase (se 3 (by rfl) ⟨587657, by rfl⟩ : syracuseStep 3134173 = 1175315) (by norm_num)
theorem B1856237 : Blo 1236436 1856237 := bbase (se 3 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 1856237 = 696089) (by norm_num)
theorem B1856261 : Blo 1236436 1856261 := bbase (se 4 (by rfl) ⟨174024, by rfl⟩ : syracuseStep 1856261 = 348049) (by norm_num)
theorem B2347805 : Blo 1236436 2347805 := bbase (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) (by norm_num)
theorem B1856285 : Blo 1236436 1856285 := bbase (se 3 (by rfl) ⟨348053, by rfl⟩ : syracuseStep 1856285 = 696107) (by norm_num)
theorem B2781989 : Blo 1236436 2781989 := bbase (se 4 (by rfl) ⟨260811, by rfl⟩ : syracuseStep 2781989 = 521623) (by norm_num)
theorem B1856309 : Blo 1236436 1856309 := bbase (se 5 (by rfl) ⟨87014, by rfl⟩ : syracuseStep 1856309 = 174029) (by norm_num)
theorem B1528633 : Blo 1236436 1528633 := bbase (se 2 (by rfl) ⟨573237, by rfl⟩ : syracuseStep 1528633 = 1146475) (by norm_num)
theorem B1856333 : Blo 1236436 1856333 := bbase (se 3 (by rfl) ⟨348062, by rfl⟩ : syracuseStep 1856333 = 696125) (by norm_num)
theorem B3134285 : Blo 1236436 3134285 := bbase (se 3 (by rfl) ⟨587678, by rfl⟩ : syracuseStep 3134285 = 1175357) (by norm_num)
theorem B1856357 : Blo 1236436 1856357 := bbase (se 4 (by rfl) ⟨174033, by rfl⟩ : syracuseStep 1856357 = 348067) (by norm_num)
theorem B2782061 : Blo 1236436 2782061 := bbase (se 3 (by rfl) ⟨521636, by rfl⟩ : syracuseStep 2782061 = 1043273) (by norm_num)
theorem B1856381 : Blo 1236436 1856381 := bbase (se 3 (by rfl) ⟨348071, by rfl⟩ : syracuseStep 1856381 = 696143) (by norm_num)
theorem B1856405 : Blo 1236436 1856405 := bbase (se 6 (by rfl) ⟨43509, by rfl⟩ : syracuseStep 1856405 = 87019) (by norm_num)
theorem B1856429 : Blo 1236436 1856429 := bbase (se 3 (by rfl) ⟨348080, by rfl⟩ : syracuseStep 1856429 = 696161) (by norm_num)
theorem B2782133 : Blo 1236436 2782133 := bbase (se 5 (by rfl) ⟨130412, by rfl⟩ : syracuseStep 2782133 = 260825) (by norm_num)
theorem B2347957 : Blo 1236436 2347957 := bbase (se 5 (by rfl) ⟨110060, by rfl⟩ : syracuseStep 2347957 = 220121) (by norm_num)
theorem B5288885 : Blo 1236436 5288885 := bbase (se 5 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 5288885 = 495833) (by norm_num)
theorem B1856453 : Blo 1236436 1856453 := bbase (se 4 (by rfl) ⟨174042, by rfl⟩ : syracuseStep 1856453 = 348085) (by norm_num)
theorem B1856477 : Blo 1236436 1856477 := bbase (se 3 (by rfl) ⟨348089, by rfl⟩ : syracuseStep 1856477 = 696179) (by norm_num)
theorem B1856501 : Blo 1236436 1856501 := bbase (se 5 (by rfl) ⟨87023, by rfl⟩ : syracuseStep 1856501 = 174047) (by norm_num)
theorem B2782205 : Blo 1236436 2782205 := bbase (se 3 (by rfl) ⟨521663, by rfl⟩ : syracuseStep 2782205 = 1043327) (by norm_num)
theorem B1856525 : Blo 1236436 1856525 := bbase (se 3 (by rfl) ⟨348098, by rfl⟩ : syracuseStep 1856525 = 696197) (by norm_num)
theorem B3134477 : Blo 1236436 3134477 := bbase (se 3 (by rfl) ⟨587714, by rfl⟩ : syracuseStep 3134477 = 1175429) (by norm_num)
theorem B1856549 : Blo 1236436 1856549 := bbase (se 4 (by rfl) ⟨174051, by rfl⟩ : syracuseStep 1856549 = 348103) (by norm_num)
theorem B4174901 : Blo 1236436 4174901 := bbase (se 5 (by rfl) ⟨195698, by rfl⟩ : syracuseStep 4174901 = 391397) (by norm_num)
theorem B1856573 : Blo 1236436 1856573 := bbase (se 3 (by rfl) ⟨348107, by rfl⟩ : syracuseStep 1856573 = 696215) (by norm_num)
theorem B2782277 : Blo 1236436 2782277 := bbase (se 4 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 2782277 = 521677) (by norm_num)
theorem B1856597 : Blo 1236436 1856597 := bbase (se 8 (by rfl) ⟨10878, by rfl⟩ : syracuseStep 1856597 = 21757) (by norm_num)
theorem B5944421 : Blo 1236436 5944421 := bbase (se 4 (by rfl) ⟨557289, by rfl⟩ : syracuseStep 5944421 = 1114579) (by norm_num)
theorem B1856621 : Blo 1236436 1856621 := bbase (se 3 (by rfl) ⟨348116, by rfl⟩ : syracuseStep 1856621 = 696233) (by norm_num)
theorem B3961973 : Blo 1236436 3961973 := bbase (se 5 (by rfl) ⟨185717, by rfl⟩ : syracuseStep 3961973 = 371435) (by norm_num)
theorem B1856645 : Blo 1236436 1856645 := bbase (se 4 (by rfl) ⟨174060, by rfl⟩ : syracuseStep 1856645 = 348121) (by norm_num)
theorem B2782349 : Blo 1236436 2782349 := bbase (se 3 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 2782349 = 1043381) (by norm_num)
theorem B1856669 : Blo 1236436 1856669 := bbase (se 3 (by rfl) ⟨348125, by rfl⟩ : syracuseStep 1856669 = 696251) (by norm_num)
theorem B4232357 : Blo 1236436 4232357 := bbase (se 4 (by rfl) ⟨396783, by rfl⟩ : syracuseStep 4232357 = 793567) (by norm_num)
theorem B1856693 : Blo 1236436 1856693 := bbase (se 5 (by rfl) ⟨87032, by rfl⟩ : syracuseStep 1856693 = 174065) (by norm_num)
theorem B1856717 : Blo 1236436 1856717 := bbase (se 3 (by rfl) ⟨348134, by rfl⟩ : syracuseStep 1856717 = 696269) (by norm_num)
theorem B2782421 : Blo 1236436 2782421 := bbase (se 7 (by rfl) ⟨32606, by rfl⟩ : syracuseStep 2782421 = 65213) (by norm_num)
theorem B2348261 : Blo 1236436 2348261 := bbase (se 4 (by rfl) ⟨220149, by rfl⟩ : syracuseStep 2348261 = 440299) (by norm_num)
theorem B1856741 : Blo 1236436 1856741 := bbase (se 4 (by rfl) ⟨174069, by rfl⟩ : syracuseStep 1856741 = 348139) (by norm_num)
theorem B6264053 : Blo 1236436 6264053 := bbase (se 5 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 6264053 = 587255) (by norm_num)
theorem B1856765 : Blo 1236436 1856765 := bbase (se 3 (by rfl) ⟨348143, by rfl⟩ : syracuseStep 1856765 = 696287) (by norm_num)
theorem B5018885 : Blo 1236436 5018885 := bbase (se 4 (by rfl) ⟨470520, by rfl⟩ : syracuseStep 5018885 = 941041) (by norm_num)
theorem B1856789 : Blo 1236436 1856789 := bbase (se 6 (by rfl) ⟨43518, by rfl⟩ : syracuseStep 1856789 = 87037) (by norm_num)
theorem B2782493 : Blo 1236436 2782493 := bbase (se 3 (by rfl) ⟨521717, by rfl⟩ : syracuseStep 2782493 = 1043435) (by norm_num)
theorem B2643229 : Blo 1236436 2643229 := bbase (se 3 (by rfl) ⟨495605, by rfl⟩ : syracuseStep 2643229 = 991211) (by norm_num)
theorem B1856813 : Blo 1236436 1856813 := bbase (se 3 (by rfl) ⟨348152, by rfl⟩ : syracuseStep 1856813 = 696305) (by norm_num)
theorem B1856837 : Blo 1236436 1856837 := bbase (se 4 (by rfl) ⟨174078, by rfl⟩ : syracuseStep 1856837 = 348157) (by norm_num)
theorem B1856861 : Blo 1236436 1856861 := bbase (se 3 (by rfl) ⟨348161, by rfl⟩ : syracuseStep 1856861 = 696323) (by norm_num)
theorem B2782565 : Blo 1236436 2782565 := bbase (se 4 (by rfl) ⟨260865, by rfl⟩ : syracuseStep 2782565 = 521731) (by norm_num)
theorem B1856885 : Blo 1236436 1856885 := bbase (se 5 (by rfl) ⟨87041, by rfl⟩ : syracuseStep 1856885 = 174083) (by norm_num)
theorem B1881485 : Blo 1236436 1881485 := bbase (se 3 (by rfl) ⟨352778, by rfl⟩ : syracuseStep 1881485 = 705557) (by norm_num)
theorem B1856909 : Blo 1236436 1856909 := bbase (se 3 (by rfl) ⟨348170, by rfl⟩ : syracuseStep 1856909 = 696341) (by norm_num)
theorem B2643349 : Blo 1236436 2643349 := bbase (se 6 (by rfl) ⟨61953, by rfl⟩ : syracuseStep 2643349 = 123907) (by norm_num)
theorem B1856933 : Blo 1236436 1856933 := bbase (se 4 (by rfl) ⟨174087, by rfl⟩ : syracuseStep 1856933 = 348175) (by norm_num)
theorem B2782637 : Blo 1236436 2782637 := bbase (se 3 (by rfl) ⟨521744, by rfl⟩ : syracuseStep 2782637 = 1043489) (by norm_num)
theorem B1856957 : Blo 1236436 1856957 := bbase (se 3 (by rfl) ⟨348179, by rfl⟩ : syracuseStep 1856957 = 696359) (by norm_num)
theorem B1856981 : Blo 1236436 1856981 := bbase (se 7 (by rfl) ⟨21761, by rfl⟩ : syracuseStep 1856981 = 43523) (by norm_num)
theorem B3175901 : Blo 1236436 3175901 := bbase (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) (by norm_num)
theorem B4175333 : Blo 1236436 4175333 := bbase (se 4 (by rfl) ⟨391437, by rfl⟩ : syracuseStep 4175333 = 782875) (by norm_num)
theorem B1857005 : Blo 1236436 1857005 := bbase (se 3 (by rfl) ⟨348188, by rfl⟩ : syracuseStep 1857005 = 696377) (by norm_num)
theorem B2782709 : Blo 1236436 2782709 := bbase (se 5 (by rfl) ⟨130439, by rfl⟩ : syracuseStep 2782709 = 260879) (by norm_num)
theorem B1857029 : Blo 1236436 1857029 := bbase (se 4 (by rfl) ⟨174096, by rfl⟩ : syracuseStep 1857029 = 348193) (by norm_num)
theorem B1857053 : Blo 1236436 1857053 := bbase (se 3 (by rfl) ⟨348197, by rfl⟩ : syracuseStep 1857053 = 696395) (by norm_num)
theorem B1857077 : Blo 1236436 1857077 := bbase (se 5 (by rfl) ⟨87050, by rfl⟩ : syracuseStep 1857077 = 174101) (by norm_num)
theorem B2782781 : Blo 1236436 2782781 := bbase (se 3 (by rfl) ⟨521771, by rfl⟩ : syracuseStep 2782781 = 1043543) (by norm_num)
theorem B1857101 : Blo 1236436 1857101 := bbase (se 3 (by rfl) ⟨348206, by rfl⟩ : syracuseStep 1857101 = 696413) (by norm_num)
theorem B1857125 : Blo 1236436 1857125 := bbase (se 4 (by rfl) ⟨174105, by rfl⟩ : syracuseStep 1857125 = 348211) (by norm_num)
theorem B1857149 : Blo 1236436 1857149 := bbase (se 3 (by rfl) ⟨348215, by rfl⟩ : syracuseStep 1857149 = 696431) (by norm_num)
theorem B2782853 : Blo 1236436 2782853 := bbase (se 4 (by rfl) ⟨260892, by rfl⟩ : syracuseStep 2782853 = 521785) (by norm_num)
theorem B2643605 : Blo 1236436 2643605 := bbase (se 6 (by rfl) ⟨61959, by rfl⟩ : syracuseStep 2643605 = 123919) (by norm_num)
theorem B1857173 : Blo 1236436 1857173 := bbase (se 6 (by rfl) ⟨43527, by rfl⟩ : syracuseStep 1857173 = 87055) (by norm_num)
theorem B2086573 : Blo 1236436 2086573 := bbase (se 3 (by rfl) ⟨391232, by rfl⟩ : syracuseStep 2086573 = 782465) (by norm_num)
theorem B1857197 : Blo 1236436 1857197 := bbase (se 3 (by rfl) ⟨348224, by rfl⟩ : syracuseStep 1857197 = 696449) (by norm_num)
theorem B1857221 : Blo 1236436 1857221 := bbase (se 4 (by rfl) ⟨174114, by rfl⟩ : syracuseStep 1857221 = 348229) (by norm_num)
theorem B2782925 : Blo 1236436 2782925 := bbase (se 3 (by rfl) ⟨521798, by rfl⟩ : syracuseStep 2782925 = 1043597) (by norm_num)
theorem B1857245 : Blo 1236436 1857245 := bbase (se 3 (by rfl) ⟨348233, by rfl⟩ : syracuseStep 1857245 = 696467) (by norm_num)
theorem B1857269 : Blo 1236436 1857269 := bbase (se 5 (by rfl) ⟨87059, by rfl⟩ : syracuseStep 1857269 = 174119) (by norm_num)
theorem B2086661 : Blo 1236436 2086661 := bbase (se 4 (by rfl) ⟨195624, by rfl⟩ : syracuseStep 2086661 = 391249) (by norm_num)
theorem B1857293 : Blo 1236436 1857293 := bbase (se 3 (by rfl) ⟨348242, by rfl⟩ : syracuseStep 1857293 = 696485) (by norm_num)
theorem B2782997 : Blo 1236436 2782997 := bbase (se 6 (by rfl) ⟨65226, by rfl⟩ : syracuseStep 2782997 = 130453) (by norm_num)
theorem B1857317 : Blo 1236436 1857317 := bbase (se 4 (by rfl) ⟨174123, by rfl⟩ : syracuseStep 1857317 = 348247) (by norm_num)
theorem B1857341 : Blo 1236436 1857341 := bbase (se 3 (by rfl) ⟨348251, by rfl⟩ : syracuseStep 1857341 = 696503) (by norm_num)
theorem B1857365 : Blo 1236436 1857365 := bbase (se 9 (by rfl) ⟨5441, by rfl⟩ : syracuseStep 1857365 = 10883) (by norm_num)
theorem B2783069 : Blo 1236436 2783069 := bbase (se 3 (by rfl) ⟨521825, by rfl⟩ : syracuseStep 2783069 = 1043651) (by norm_num)
theorem B1857389 : Blo 1236436 1857389 := bbase (se 3 (by rfl) ⟨348260, by rfl⟩ : syracuseStep 1857389 = 696521) (by norm_num)
theorem B2086789 : Blo 1236436 2086789 := bbase (se 4 (by rfl) ⟨195636, by rfl⟩ : syracuseStep 2086789 = 391273) (by norm_num)
theorem B1857413 : Blo 1236436 1857413 := bbase (se 4 (by rfl) ⟨174132, by rfl⟩ : syracuseStep 1857413 = 348265) (by norm_num)
theorem B4175765 : Blo 1236436 4175765 := bbase (se 6 (by rfl) ⟨97869, by rfl⟩ : syracuseStep 4175765 = 195739) (by norm_num)
theorem B1857437 : Blo 1236436 1857437 := bbase (se 3 (by rfl) ⟨348269, by rfl⟩ : syracuseStep 1857437 = 696539) (by norm_num)
theorem B2783141 : Blo 1236436 2783141 := bbase (se 4 (by rfl) ⟨260919, by rfl⟩ : syracuseStep 2783141 = 521839) (by norm_num)
theorem B1857461 : Blo 1236436 1857461 := bbase (se 5 (by rfl) ⟨87068, by rfl⟩ : syracuseStep 1857461 = 174137) (by norm_num)
theorem B1857485 : Blo 1236436 1857485 := bbase (se 3 (by rfl) ⟨348278, by rfl⟩ : syracuseStep 1857485 = 696557) (by norm_num)
theorem B22566869 : Blo 1236436 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B2349013 : Blo 1236436 2349013 := bbase (se 7 (by rfl) ⟨27527, by rfl⟩ : syracuseStep 2349013 = 55055) (by norm_num)
theorem B2086877 : Blo 1236436 2086877 := bbase (se 3 (by rfl) ⟨391289, by rfl⟩ : syracuseStep 2086877 = 782579) (by norm_num)
theorem B1857509 : Blo 1236436 1857509 := bbase (se 4 (by rfl) ⟨174141, by rfl⟩ : syracuseStep 1857509 = 348283) (by norm_num)
theorem B2783213 : Blo 1236436 2783213 := bbase (se 3 (by rfl) ⟨521852, by rfl⟩ : syracuseStep 2783213 = 1043705) (by norm_num)
theorem B1857533 : Blo 1236436 1857533 := bbase (se 3 (by rfl) ⟨348287, by rfl⟩ : syracuseStep 1857533 = 696575) (by norm_num)
theorem B1587217 : Blo 1236436 1587217 := bbase (se 2 (by rfl) ⟨595206, by rfl⟩ : syracuseStep 1587217 = 1190413) (by norm_num)
theorem B1857557 : Blo 1236436 1857557 := bbase (se 6 (by rfl) ⟨43536, by rfl⟩ : syracuseStep 1857557 = 87073) (by norm_num)
theorem B1857581 : Blo 1236436 1857581 := bbase (se 3 (by rfl) ⟨348296, by rfl⟩ : syracuseStep 1857581 = 696593) (by norm_num)
theorem B2783285 : Blo 1236436 2783285 := bbase (se 5 (by rfl) ⟨130466, by rfl⟩ : syracuseStep 2783285 = 260933) (by norm_num)
theorem B4700213 : Blo 1236436 4700213 := bbase (se 5 (by rfl) ⟨220322, by rfl⟩ : syracuseStep 4700213 = 440645) (by norm_num)
theorem B1857605 : Blo 1236436 1857605 := bbase (se 4 (by rfl) ⟨174150, by rfl⟩ : syracuseStep 1857605 = 348301) (by norm_num)
theorem B2087005 : Blo 1236436 2087005 := bbase (se 3 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 2087005 = 782627) (by norm_num)
theorem B2971741 : Blo 1236436 2971741 := bbase (se 3 (by rfl) ⟨557201, by rfl⟩ : syracuseStep 2971741 = 1114403) (by norm_num)
theorem B1857629 : Blo 1236436 1857629 := bbase (se 3 (by rfl) ⟨348305, by rfl⟩ : syracuseStep 1857629 = 696611) (by norm_num)
theorem B2349157 : Blo 1236436 2349157 := bbase (se 4 (by rfl) ⟨220233, by rfl⟩ : syracuseStep 2349157 = 440467) (by norm_num)
theorem B1857653 : Blo 1236436 1857653 := bbase (se 5 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 1857653 = 174155) (by norm_num)
theorem B2783357 : Blo 1236436 2783357 := bbase (se 3 (by rfl) ⟨521879, by rfl⟩ : syracuseStep 2783357 = 1043759) (by norm_num)
theorem B2087093 : Blo 1236436 2087093 := bbase (se 5 (by rfl) ⟨97832, by rfl⟩ : syracuseStep 2087093 = 195665) (by norm_num)
theorem B3963077 : Blo 1236436 3963077 := bbase (se 4 (by rfl) ⟨371538, by rfl⟩ : syracuseStep 3963077 = 743077) (by norm_num)
theorem B2783429 : Blo 1236436 2783429 := bbase (se 4 (by rfl) ⟨260946, by rfl⟩ : syracuseStep 2783429 = 521893) (by norm_num)
theorem B1358057 : Blo 1236436 1358057 := bbase (se 2 (by rfl) ⟨509271, by rfl⟩ : syracuseStep 1358057 = 1018543) (by norm_num)
theorem B2349317 : Blo 1236436 2349317 := bbase (se 4 (by rfl) ⟨220248, by rfl⟩ : syracuseStep 2349317 = 440497) (by norm_num)
theorem B2783501 : Blo 1236436 2783501 := bbase (se 3 (by rfl) ⟨521906, by rfl⟩ : syracuseStep 2783501 = 1043813) (by norm_num)
theorem B2087221 : Blo 1236436 2087221 := bbase (se 5 (by rfl) ⟨97838, by rfl⟩ : syracuseStep 2087221 = 195677) (by norm_num)
theorem B4176197 : Blo 1236436 4176197 := bbase (se 4 (by rfl) ⟨391518, by rfl⟩ : syracuseStep 4176197 = 783037) (by norm_num)
theorem B2783573 : Blo 1236436 2783573 := bbase (se 10 (by rfl) ⟨4077, by rfl⟩ : syracuseStep 2783573 = 8155) (by norm_num)
theorem B4700501 : Blo 1236436 4700501 := bbase (se 10 (by rfl) ⟨6885, by rfl⟩ : syracuseStep 4700501 = 13771) (by norm_num)
theorem B2087309 : Blo 1236436 2087309 := bbase (se 3 (by rfl) ⟨391370, by rfl⟩ : syracuseStep 2087309 = 782741) (by norm_num)
theorem B2349461 : Blo 1236436 2349461 := bbase (se 6 (by rfl) ⟨55065, by rfl⟩ : syracuseStep 2349461 = 110131) (by norm_num)
theorem B2783645 : Blo 1236436 2783645 := bbase (se 3 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 2783645 = 1043867) (by norm_num)
theorem B1391017 : Blo 1236436 1391017 := bbase (se 2 (by rfl) ⟨521631, by rfl⟩ : syracuseStep 1391017 = 1043263) (by norm_num)
theorem B4463045 : Blo 1236436 4463045 := bbase (se 4 (by rfl) ⟨418410, by rfl⟩ : syracuseStep 4463045 = 836821) (by norm_num)
theorem B1391053 : Blo 1236436 1391053 := bbase (se 3 (by rfl) ⟨260822, by rfl⟩ : syracuseStep 1391053 = 521645) (by norm_num)
theorem B2783717 : Blo 1236436 2783717 := bbase (se 4 (by rfl) ⟨260973, by rfl⟩ : syracuseStep 2783717 = 521947) (by norm_num)
theorem B1391089 : Blo 1236436 1391089 := bbase (se 2 (by rfl) ⟨521658, by rfl⟩ : syracuseStep 1391089 = 1043317) (by norm_num)
theorem B5945845 : Blo 1236436 5945845 := bbase (se 5 (by rfl) ⟨278711, by rfl⟩ : syracuseStep 5945845 = 557423) (by norm_num)
theorem B6265349 : Blo 1236436 6265349 := bbase (se 4 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 6265349 = 1174753) (by norm_num)
theorem B2087437 : Blo 1236436 2087437 := bbase (se 3 (by rfl) ⟨391394, by rfl⟩ : syracuseStep 2087437 = 782789) (by norm_num)
theorem B2644493 : Blo 1236436 2644493 := bbase (se 3 (by rfl) ⟨495842, by rfl⟩ : syracuseStep 2644493 = 991685) (by norm_num)
theorem B1391125 : Blo 1236436 1391125 := bbase (se 6 (by rfl) ⟨32604, by rfl⟩ : syracuseStep 1391125 = 65209) (by norm_num)
theorem B2382365 : Blo 1236436 2382365 := bbase (se 3 (by rfl) ⟨446693, by rfl⟩ : syracuseStep 2382365 = 893387) (by norm_num)
theorem B2783789 : Blo 1236436 2783789 := bbase (se 3 (by rfl) ⟨521960, by rfl⟩ : syracuseStep 2783789 = 1043921) (by norm_num)
theorem B11893301 : Blo 1236436 11893301 := bbase (se 5 (by rfl) ⟨557498, by rfl⟩ : syracuseStep 11893301 = 1114997) (by norm_num)
theorem B1391161 : Blo 1236436 1391161 := bbase (se 2 (by rfl) ⟨521685, by rfl⟩ : syracuseStep 1391161 = 1043371) (by norm_num)
theorem B4463189 : Blo 1236436 4463189 := bbase (se 8 (by rfl) ⟨26151, by rfl⟩ : syracuseStep 4463189 = 52303) (by norm_num)
theorem B1391197 : Blo 1236436 1391197 := bbase (se 3 (by rfl) ⟨260849, by rfl⟩ : syracuseStep 1391197 = 521699) (by norm_num)
theorem B2087525 : Blo 1236436 2087525 := bbase (se 4 (by rfl) ⟨195705, by rfl⟩ : syracuseStep 2087525 = 391411) (by norm_num)
theorem B2783861 : Blo 1236436 2783861 := bbase (se 5 (by rfl) ⟨130493, by rfl⟩ : syracuseStep 2783861 = 260987) (by norm_num)
theorem B1391233 : Blo 1236436 1391233 := bbase (se 2 (by rfl) ⟨521712, by rfl⟩ : syracuseStep 1391233 = 1043425) (by norm_num)
theorem B1391269 : Blo 1236436 1391269 := bbase (se 4 (by rfl) ⟨130431, by rfl⟩ : syracuseStep 1391269 = 260863) (by norm_num)
theorem B2349749 : Blo 1236436 2349749 := bbase (se 5 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 2349749 = 220289) (by norm_num)
theorem B2783933 : Blo 1236436 2783933 := bbase (se 3 (by rfl) ⟨521987, by rfl⟩ : syracuseStep 2783933 = 1043975) (by norm_num)
theorem B1391305 : Blo 1236436 1391305 := bbase (se 2 (by rfl) ⟨521739, by rfl⟩ : syracuseStep 1391305 = 1043479) (by norm_num)
theorem B1587913 : Blo 1236436 1587913 := bbase (se 2 (by rfl) ⟨595467, by rfl⟩ : syracuseStep 1587913 = 1190935) (by norm_num)
theorem B2087653 : Blo 1236436 2087653 := bbase (se 4 (by rfl) ⟨195717, by rfl⟩ : syracuseStep 2087653 = 391435) (by norm_num)
theorem B1391341 : Blo 1236436 1391341 := bbase (se 3 (by rfl) ⟨260876, by rfl⟩ : syracuseStep 1391341 = 521753) (by norm_num)
theorem B4176629 : Blo 1236436 4176629 := bbase (se 5 (by rfl) ⟨195779, by rfl⟩ : syracuseStep 4176629 = 391559) (by norm_num)
theorem B2644733 : Blo 1236436 2644733 := bbase (se 3 (by rfl) ⟨495887, by rfl⟩ : syracuseStep 2644733 = 991775) (by norm_num)
theorem B2784005 : Blo 1236436 2784005 := bbase (se 4 (by rfl) ⟨261000, by rfl⟩ : syracuseStep 2784005 = 522001) (by norm_num)
theorem B1391377 : Blo 1236436 1391377 := bbase (se 2 (by rfl) ⟨521766, by rfl⟩ : syracuseStep 1391377 = 1043533) (by norm_num)
theorem B5282597 : Blo 1236436 5282597 := bbase (se 4 (by rfl) ⟨495243, by rfl⟩ : syracuseStep 5282597 = 990487) (by norm_num)
theorem B3521333 : Blo 1236436 3521333 := bbase (se 5 (by rfl) ⟨165062, by rfl⟩ : syracuseStep 3521333 = 330125) (by norm_num)
theorem B1391413 : Blo 1236436 1391413 := bbase (se 5 (by rfl) ⟨65222, by rfl⟩ : syracuseStep 1391413 = 130445) (by norm_num)
theorem B2087741 : Blo 1236436 2087741 := bbase (se 3 (by rfl) ⟨391451, by rfl⟩ : syracuseStep 2087741 = 782903) (by norm_num)
theorem B2784077 : Blo 1236436 2784077 := bbase (se 3 (by rfl) ⟨522014, by rfl⟩ : syracuseStep 2784077 = 1044029) (by norm_num)
theorem B2349901 : Blo 1236436 2349901 := bbase (se 3 (by rfl) ⟨440606, by rfl⟩ : syracuseStep 2349901 = 881213) (by norm_num)
theorem B1391449 : Blo 1236436 1391449 := bbase (se 2 (by rfl) ⟨521793, by rfl⟩ : syracuseStep 1391449 = 1043587) (by norm_num)
theorem B1391485 : Blo 1236436 1391485 := bbase (se 3 (by rfl) ⟨260903, by rfl⟩ : syracuseStep 1391485 = 521807) (by norm_num)
theorem B2784149 : Blo 1236436 2784149 := bbase (se 6 (by rfl) ⟨65253, by rfl⟩ : syracuseStep 2784149 = 130507) (by norm_num)
theorem B1391521 : Blo 1236436 1391521 := bbase (se 2 (by rfl) ⟨521820, by rfl⟩ : syracuseStep 1391521 = 1043641) (by norm_num)
theorem B2087869 : Blo 1236436 2087869 := bbase (se 3 (by rfl) ⟨391475, by rfl⟩ : syracuseStep 2087869 = 782951) (by norm_num)
theorem B1907645 : Blo 1236436 1907645 := bbase (se 3 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 1907645 = 715367) (by norm_num)
theorem B1391557 : Blo 1236436 1391557 := bbase (se 4 (by rfl) ⟨130458, by rfl⟩ : syracuseStep 1391557 = 260917) (by norm_num)
theorem B1981397 : Blo 1236436 1981397 := bbase (se 7 (by rfl) ⟨23219, by rfl⟩ : syracuseStep 1981397 = 46439) (by norm_num)
theorem B2784221 : Blo 1236436 2784221 := bbase (se 3 (by rfl) ⟨522041, by rfl⟩ : syracuseStep 2784221 = 1044083) (by norm_num)
theorem B1391593 : Blo 1236436 1391593 := bbase (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) (by norm_num)
theorem B1391629 : Blo 1236436 1391629 := bbase (se 3 (by rfl) ⟨260930, by rfl⟩ : syracuseStep 1391629 = 521861) (by norm_num)
theorem B2087957 : Blo 1236436 2087957 := bbase (se 6 (by rfl) ⟨48936, by rfl⟩ : syracuseStep 2087957 = 97873) (by norm_num)
theorem B2784293 : Blo 1236436 2784293 := bbase (se 4 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 2784293 = 522055) (by norm_num)
theorem B1391665 : Blo 1236436 1391665 := bbase (se 2 (by rfl) ⟨521874, by rfl⟩ : syracuseStep 1391665 = 1043749) (by norm_num)
theorem B1981525 : Blo 1236436 1981525 := bbase (se 8 (by rfl) ⟨11610, by rfl⟩ : syracuseStep 1981525 = 23221) (by norm_num)
theorem B1391701 : Blo 1236436 1391701 := bbase (se 8 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 1391701 = 16309) (by norm_num)
theorem B2784365 : Blo 1236436 2784365 := bbase (se 3 (by rfl) ⟨522068, by rfl⟩ : syracuseStep 2784365 = 1044137) (by norm_num)
theorem B1391737 : Blo 1236436 1391737 := bbase (se 2 (by rfl) ⟨521901, by rfl⟩ : syracuseStep 1391737 = 1043803) (by norm_num)
theorem B2350205 : Blo 1236436 2350205 := bbase (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) (by norm_num)
theorem B1981589 : Blo 1236436 1981589 := bbase (se 6 (by rfl) ⟨46443, by rfl⟩ : syracuseStep 1981589 = 92887) (by norm_num)
theorem B2088085 : Blo 1236436 2088085 := bbase (se 6 (by rfl) ⟨48939, by rfl⟩ : syracuseStep 2088085 = 97879) (by norm_num)
theorem B1391773 : Blo 1236436 1391773 := bbase (se 3 (by rfl) ⟨260957, by rfl⟩ : syracuseStep 1391773 = 521915) (by norm_num)
theorem B4177061 : Blo 1236436 4177061 := bbase (se 4 (by rfl) ⟨391599, by rfl⟩ : syracuseStep 4177061 = 783199) (by norm_num)
theorem B2784437 : Blo 1236436 2784437 := bbase (se 5 (by rfl) ⟨130520, by rfl⟩ : syracuseStep 2784437 = 261041) (by norm_num)
theorem B1391809 : Blo 1236436 1391809 := bbase (se 2 (by rfl) ⟨521928, by rfl⟩ : syracuseStep 1391809 = 1043857) (by norm_num)
theorem B1391845 : Blo 1236436 1391845 := bbase (se 4 (by rfl) ⟨130485, by rfl⟩ : syracuseStep 1391845 = 260971) (by norm_num)
theorem B2088173 : Blo 1236436 2088173 := bbase (se 3 (by rfl) ⟨391532, by rfl⟩ : syracuseStep 2088173 = 783065) (by norm_num)
theorem B1760501 : Blo 1236436 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B2784509 : Blo 1236436 2784509 := bbase (se 3 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 2784509 = 1044191) (by norm_num)
theorem B1391881 : Blo 1236436 1391881 := bbase (se 2 (by rfl) ⟨521955, by rfl⟩ : syracuseStep 1391881 = 1043911) (by norm_num)
theorem B1391917 : Blo 1236436 1391917 := bbase (se 3 (by rfl) ⟨260984, by rfl⟩ : syracuseStep 1391917 = 521969) (by norm_num)
theorem B2784581 : Blo 1236436 2784581 := bbase (se 4 (by rfl) ⟨261054, by rfl⟩ : syracuseStep 2784581 = 522109) (by norm_num)
theorem B1391953 : Blo 1236436 1391953 := bbase (se 2 (by rfl) ⟨521982, by rfl⟩ : syracuseStep 1391953 = 1043965) (by norm_num)
theorem B57105749 : Blo 1236436 57105749 := bbase (se 11 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 57105749 = 83651) (by norm_num)
theorem B13557077 : Blo 1236436 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B2088301 : Blo 1236436 2088301 := bbase (se 3 (by rfl) ⟨391556, by rfl⟩ : syracuseStep 2088301 = 783113) (by norm_num)
theorem B1391989 : Blo 1236436 1391989 := bbase (se 5 (by rfl) ⟨65249, by rfl⟩ : syracuseStep 1391989 = 130499) (by norm_num)
theorem B2784653 : Blo 1236436 2784653 := bbase (se 3 (by rfl) ⟨522122, by rfl⟩ : syracuseStep 2784653 = 1044245) (by norm_num)
theorem B4521365 : Blo 1236436 4521365 := bbase (se 6 (by rfl) ⟨105969, by rfl⟩ : syracuseStep 4521365 = 211939) (by norm_num)
theorem B10722709 : Blo 1236436 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B1392025 : Blo 1236436 1392025 := bbase (se 2 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 1392025 = 1044019) (by norm_num)
theorem B1392061 : Blo 1236436 1392061 := bbase (se 3 (by rfl) ⟨261011, by rfl⟩ : syracuseStep 1392061 = 522023) (by norm_num)
theorem B2973125 : Blo 1236436 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B2088389 : Blo 1236436 2088389 := bbase (se 4 (by rfl) ⟨195786, by rfl⟩ : syracuseStep 2088389 = 391573) (by norm_num)
theorem B2678221 : Blo 1236436 2678221 := bbase (se 3 (by rfl) ⟨502166, by rfl⟩ : syracuseStep 2678221 = 1004333) (by norm_num)
theorem B2973133 : Blo 1236436 2973133 := bbase (se 3 (by rfl) ⟨557462, by rfl⟩ : syracuseStep 2973133 = 1114925) (by norm_num)
theorem B3522005 : Blo 1236436 3522005 := bbase (se 7 (by rfl) ⟨41273, by rfl⟩ : syracuseStep 3522005 = 82547) (by norm_num)
theorem B2784725 : Blo 1236436 2784725 := bbase (se 7 (by rfl) ⟨32633, by rfl⟩ : syracuseStep 2784725 = 65267) (by norm_num)
theorem B1392097 : Blo 1236436 1392097 := bbase (se 2 (by rfl) ⟨522036, by rfl⟩ : syracuseStep 1392097 = 1044073) (by norm_num)
theorem B4701685 : Blo 1236436 4701685 := bbase (se 5 (by rfl) ⟨220391, by rfl⟩ : syracuseStep 4701685 = 440783) (by norm_num)
theorem B1392133 : Blo 1236436 1392133 := bbase (se 4 (by rfl) ⟨130512, by rfl⟩ : syracuseStep 1392133 = 261025) (by norm_num)
theorem B19037717 : Blo 1236436 19037717 := bbase (se 6 (by rfl) ⟨446196, by rfl⟩ : syracuseStep 19037717 = 892393) (by norm_num)
theorem B2784797 : Blo 1236436 2784797 := bbase (se 3 (by rfl) ⟨522149, by rfl⟩ : syracuseStep 2784797 = 1044299) (by norm_num)
theorem B1392169 : Blo 1236436 1392169 := bbase (se 2 (by rfl) ⟨522063, by rfl⟩ : syracuseStep 1392169 = 1044127) (by norm_num)
theorem B2088517 : Blo 1236436 2088517 := bbase (se 4 (by rfl) ⟨195798, by rfl⟩ : syracuseStep 2088517 = 391597) (by norm_num)
theorem B1392205 : Blo 1236436 1392205 := bbase (se 3 (by rfl) ⟨261038, by rfl⟩ : syracuseStep 1392205 = 522077) (by norm_num)
theorem B4177493 : Blo 1236436 4177493 := bbase (se 8 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 4177493 = 48955) (by norm_num)
theorem B2784869 : Blo 1236436 2784869 := bbase (se 4 (by rfl) ⟨261081, by rfl⟩ : syracuseStep 2784869 = 522163) (by norm_num)
theorem B1392241 : Blo 1236436 1392241 := bbase (se 2 (by rfl) ⟨522090, by rfl⟩ : syracuseStep 1392241 = 1044181) (by norm_num)
theorem B1392277 : Blo 1236436 1392277 := bbase (se 6 (by rfl) ⟨32631, by rfl⟩ : syracuseStep 1392277 = 65263) (by norm_num)
theorem B2088605 : Blo 1236436 2088605 := bbase (se 3 (by rfl) ⟨391613, by rfl⟩ : syracuseStep 2088605 = 783227) (by norm_num)
theorem B2784941 : Blo 1236436 2784941 := bbase (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) (by norm_num)
theorem B1392313 : Blo 1236436 1392313 := bbase (se 2 (by rfl) ⟨522117, by rfl⟩ : syracuseStep 1392313 = 1044235) (by norm_num)
theorem B1392349 : Blo 1236436 1392349 := bbase (se 3 (by rfl) ⟨261065, by rfl⟩ : syracuseStep 1392349 = 522131) (by norm_num)
theorem B2785013 : Blo 1236436 2785013 := bbase (se 5 (by rfl) ⟨130547, by rfl⟩ : syracuseStep 2785013 = 261095) (by norm_num)
theorem B1392385 : Blo 1236436 1392385 := bbase (se 2 (by rfl) ⟨522144, by rfl⟩ : syracuseStep 1392385 = 1044289) (by norm_num)
theorem B6266645 : Blo 1236436 6266645 := bbase (se 6 (by rfl) ⟨146874, by rfl⟩ : syracuseStep 6266645 = 293749) (by norm_num)
theorem B2088733 : Blo 1236436 2088733 := bbase (se 3 (by rfl) ⟨391637, by rfl⟩ : syracuseStep 2088733 = 783275) (by norm_num)
theorem B1859365 : Blo 1236436 1859365 := bbase (se 4 (by rfl) ⟨174315, by rfl⟩ : syracuseStep 1859365 = 348631) (by norm_num)
theorem B1392421 : Blo 1236436 1392421 := bbase (se 4 (by rfl) ⟨130539, by rfl⟩ : syracuseStep 1392421 = 261079) (by norm_num)
theorem B4701989 : Blo 1236436 4701989 := bbase (se 4 (by rfl) ⟨440811, by rfl⟩ : syracuseStep 4701989 = 881623) (by norm_num)
theorem B2785085 : Blo 1236436 2785085 := bbase (se 3 (by rfl) ⟨522203, by rfl⟩ : syracuseStep 2785085 = 1044407) (by norm_num)
theorem B1392457 : Blo 1236436 1392457 := bbase (se 2 (by rfl) ⟨522171, by rfl⟩ : syracuseStep 1392457 = 1044343) (by norm_num)
theorem B3342181 : Blo 1236436 3342181 := bbase (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) (by norm_num)
theorem B1392493 : Blo 1236436 1392493 := bbase (se 3 (by rfl) ⟨261092, by rfl⟩ : syracuseStep 1392493 = 522185) (by norm_num)
theorem B2350957 : Blo 1236436 2350957 := bbase (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) (by norm_num)
theorem B2088821 : Blo 1236436 2088821 := bbase (se 5 (by rfl) ⟨97913, by rfl⟩ : syracuseStep 2088821 = 195827) (by norm_num)
theorem B3522437 : Blo 1236436 3522437 := bbase (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) (by norm_num)
theorem B2785157 : Blo 1236436 2785157 := bbase (se 4 (by rfl) ⟨261108, by rfl⟩ : syracuseStep 2785157 = 522217) (by norm_num)
theorem B1392529 : Blo 1236436 1392529 := bbase (se 2 (by rfl) ⟨522198, by rfl⟩ : syracuseStep 1392529 = 1044397) (by norm_num)
theorem B2228149 : Blo 1236436 2228149 := bbase (se 5 (by rfl) ⟨104444, by rfl⟩ : syracuseStep 2228149 = 208889) (by norm_num)
theorem B1392565 : Blo 1236436 1392565 := bbase (se 5 (by rfl) ⟨65276, by rfl⟩ : syracuseStep 1392565 = 130553) (by norm_num)
theorem B2785229 : Blo 1236436 2785229 := bbase (se 3 (by rfl) ⟨522230, by rfl⟩ : syracuseStep 2785229 = 1044461) (by norm_num)
theorem B1392601 : Blo 1236436 1392601 := bbase (se 2 (by rfl) ⟨522225, by rfl⟩ : syracuseStep 1392601 = 1044451) (by norm_num)
theorem B5717989 : Blo 1236436 5717989 := bbase (se 4 (by rfl) ⟨536061, by rfl⟩ : syracuseStep 5717989 = 1072123) (by norm_num)
theorem B2088949 : Blo 1236436 2088949 := bbase (se 5 (by rfl) ⟨97919, by rfl⟩ : syracuseStep 2088949 = 195839) (by norm_num)
theorem B1392637 : Blo 1236436 1392637 := bbase (se 3 (by rfl) ⟨261119, by rfl⟩ : syracuseStep 1392637 = 522239) (by norm_num)
theorem B1236995 : Blo 1236436 1236995 := bstep (se 1 (by rfl) ⟨927746, by rfl⟩ : syracuseStep 1236995 = 1855493) B1855493
theorem B2785283 : Blo 1236436 2785283 := bstep (se 1 (by rfl) ⟨2088962, by rfl⟩ : syracuseStep 2785283 = 4177925) B4177925
theorem B1237011 : Blo 1236436 1237011 := bstep (se 1 (by rfl) ⟨927758, by rfl⟩ : syracuseStep 1237011 = 1855517) B1855517
theorem B6684707 : Blo 1236436 6684707 := bstep (se 1 (by rfl) ⟨5013530, by rfl⟩ : syracuseStep 6684707 = 10027061) B10027061
theorem B1237027 : Blo 1236436 1237027 := bstep (se 1 (by rfl) ⟨927770, by rfl⟩ : syracuseStep 1237027 = 1855541) B1855541
theorem B1237043 : Blo 1236436 1237043 := bstep (se 1 (by rfl) ⟨927782, by rfl⟩ : syracuseStep 1237043 = 1855565) B1855565
theorem B1392691 : Blo 1236436 1392691 := bstep (se 1 (by rfl) ⟨1044518, by rfl⟩ : syracuseStep 1392691 = 2089037) B2089037
theorem B1237059 : Blo 1236436 1237059 := bstep (se 1 (by rfl) ⟨927794, by rfl⟩ : syracuseStep 1237059 = 1855589) B1855589
theorem B3620945 : Blo 1236436 3620945 := bstep (se 2 (by rfl) ⟨1357854, by rfl⟩ : syracuseStep 3620945 = 2715709) B2715709
theorem B1237075 : Blo 1236436 1237075 := bstep (se 1 (by rfl) ⟨927806, by rfl⟩ : syracuseStep 1237075 = 1855613) B1855613
theorem B2089057 : Blo 1236436 2089057 := bstep (se 2 (by rfl) ⟨783396, by rfl⟩ : syracuseStep 2089057 = 1566793) B1566793
theorem B1237091 : Blo 1236436 1237091 := bstep (se 1 (by rfl) ⟨927818, by rfl⟩ : syracuseStep 1237091 = 1855637) B1855637
theorem B9396323 : Blo 1236436 9396323 := bstep (se 1 (by rfl) ⟨7047242, by rfl⟩ : syracuseStep 9396323 = 14094485) B14094485
theorem B4178033 : Blo 1236436 4178033 := bstep (se 2 (by rfl) ⟨1566762, by rfl⟩ : syracuseStep 4178033 = 3133525) B3133525
theorem B1237107 : Blo 1236436 1237107 := bstep (se 1 (by rfl) ⟨927830, by rfl⟩ : syracuseStep 1237107 = 1855661) B1855661
theorem B1237123 : Blo 1236436 1237123 := bstep (se 1 (by rfl) ⟨927842, by rfl⟩ : syracuseStep 1237123 = 1855685) B1855685
theorem B2089091 : Blo 1236436 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B1237139 : Blo 1236436 1237139 := bstep (se 1 (by rfl) ⟨927854, by rfl⟩ : syracuseStep 1237139 = 1855709) B1855709
theorem B1237155 : Blo 1236436 1237155 := bstep (se 1 (by rfl) ⟨927866, by rfl⟩ : syracuseStep 1237155 = 1855733) B1855733
theorem B1786033 : Blo 1236436 1786033 := bstep (se 2 (by rfl) ⟨669762, by rfl⟩ : syracuseStep 1786033 = 1339525) B1339525
theorem B1237171 : Blo 1236436 1237171 := bstep (se 1 (by rfl) ⟨927878, by rfl⟩ : syracuseStep 1237171 = 1855757) B1855757
theorem B1237187 : Blo 1236436 1237187 := bstep (se 1 (by rfl) ⟨927890, by rfl⟩ : syracuseStep 1237187 = 1855781) B1855781
theorem B1392835 : Blo 1236436 1392835 := bstep (se 1 (by rfl) ⟨1044626, by rfl⟩ : syracuseStep 1392835 = 2089253) B2089253
theorem B1237203 : Blo 1236436 1237203 := bstep (se 1 (by rfl) ⟨927902, by rfl⟩ : syracuseStep 1237203 = 1855805) B1855805
theorem B1237219 : Blo 1236436 1237219 := bstep (se 1 (by rfl) ⟨927914, by rfl⟩ : syracuseStep 1237219 = 1855829) B1855829
theorem B1564915 : Blo 1236436 1564915 := bstep (se 1 (by rfl) ⟨1173686, by rfl⟩ : syracuseStep 1564915 = 2347373) B2347373
theorem B1237235 : Blo 1236436 1237235 := bstep (se 1 (by rfl) ⟨927926, by rfl⟩ : syracuseStep 1237235 = 1855853) B1855853
theorem B1237251 : Blo 1236436 1237251 := bstep (se 1 (by rfl) ⟨927938, by rfl⟩ : syracuseStep 1237251 = 1855877) B1855877
theorem B2089219 : Blo 1236436 2089219 := bstep (se 1 (by rfl) ⟨1566914, by rfl⟩ : syracuseStep 2089219 = 3133829) B3133829
theorem B2785553 : Blo 1236436 2785553 := bstep (se 2 (by rfl) ⟨1044582, by rfl⟩ : syracuseStep 2785553 = 2089165) B2089165
theorem B1237267 : Blo 1236436 1237267 := bstep (se 1 (by rfl) ⟨927950, by rfl⟩ : syracuseStep 1237267 = 1855901) B1855901
theorem B1237283 : Blo 1236436 1237283 := bstep (se 1 (by rfl) ⟨927962, by rfl⟩ : syracuseStep 1237283 = 1855925) B1855925
theorem B1982755 : Blo 1236436 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B2785571 : Blo 1236436 2785571 := bstep (se 1 (by rfl) ⟨2089178, by rfl⟩ : syracuseStep 2785571 = 4178357) B4178357
theorem B1237299 : Blo 1236436 1237299 := bstep (se 1 (by rfl) ⟨927974, by rfl⟩ : syracuseStep 1237299 = 1855949) B1855949
theorem B1237315 : Blo 1236436 1237315 := bstep (se 1 (by rfl) ⟨927986, by rfl⟩ : syracuseStep 1237315 = 1855973) B1855973
theorem B1982801 : Blo 1236436 1982801 := bstep (se 2 (by rfl) ⟨743550, by rfl⟩ : syracuseStep 1982801 = 1487101) B1487101
theorem B1565011 : Blo 1236436 1565011 := bstep (se 1 (by rfl) ⟨1173758, by rfl⟩ : syracuseStep 1565011 = 2347517) B2347517
theorem B1237331 : Blo 1236436 1237331 := bstep (se 1 (by rfl) ⟨927998, by rfl⟩ : syracuseStep 1237331 = 1855997) B1855997
theorem B1392979 : Blo 1236436 1392979 := bstep (se 1 (by rfl) ⟨1044734, by rfl⟩ : syracuseStep 1392979 = 2089469) B2089469
theorem B1237347 : Blo 1236436 1237347 := bstep (se 1 (by rfl) ⟨928010, by rfl⟩ : syracuseStep 1237347 = 1856021) B1856021
theorem B1237363 : Blo 1236436 1237363 := bstep (se 1 (by rfl) ⟨928022, by rfl⟩ : syracuseStep 1237363 = 1856045) B1856045
theorem B1237379 : Blo 1236436 1237379 := bstep (se 1 (by rfl) ⟨928034, by rfl⟩ : syracuseStep 1237379 = 1856069) B1856069
theorem B5284237 : Blo 1236436 5284237 := bstep (se 3 (by rfl) ⟨990794, by rfl⟩ : syracuseStep 5284237 = 1981589) B1981589
theorem B2089361 : Blo 1236436 2089361 := bstep (se 2 (by rfl) ⟨783510, by rfl⟩ : syracuseStep 2089361 = 1567021) B1567021
theorem B1237395 : Blo 1236436 1237395 := bstep (se 1 (by rfl) ⟨928046, by rfl⟩ : syracuseStep 1237395 = 1856093) B1856093
theorem B1761697 : Blo 1236436 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B1237411 : Blo 1236436 1237411 := bstep (se 1 (by rfl) ⟨928058, by rfl⟩ : syracuseStep 1237411 = 1856117) B1856117
theorem B1237427 : Blo 1236436 1237427 := bstep (se 1 (by rfl) ⟨928070, by rfl⟩ : syracuseStep 1237427 = 1856141) B1856141
theorem B1237443 : Blo 1236436 1237443 := bstep (se 1 (by rfl) ⟨928082, by rfl⟩ : syracuseStep 1237443 = 1856165) B1856165
theorem B1237459 : Blo 1236436 1237459 := bstep (se 1 (by rfl) ⟨928094, by rfl⟩ : syracuseStep 1237459 = 1856189) B1856189
theorem B1237475 : Blo 1236436 1237475 := bstep (se 1 (by rfl) ⟨928106, by rfl⟩ : syracuseStep 1237475 = 1856213) B1856213
theorem B1393123 : Blo 1236436 1393123 := bstep (se 1 (by rfl) ⟨1044842, by rfl⟩ : syracuseStep 1393123 = 2089685) B2089685
theorem B1237491 : Blo 1236436 1237491 := bstep (se 1 (by rfl) ⟨928118, by rfl⟩ : syracuseStep 1237491 = 1856237) B1856237
theorem B1237507 : Blo 1236436 1237507 := bstep (se 1 (by rfl) ⟨928130, by rfl⟩ : syracuseStep 1237507 = 1856261) B1856261
theorem B13378061 : Blo 1236436 13378061 := bstep (se 3 (by rfl) ⟨2508386, by rfl⟩ : syracuseStep 13378061 = 5016773) B5016773
theorem B2089489 : Blo 1236436 2089489 := bstep (se 2 (by rfl) ⟨783558, by rfl⟩ : syracuseStep 2089489 = 1567117) B1567117
theorem B1237523 : Blo 1236436 1237523 := bstep (se 1 (by rfl) ⟨928142, by rfl⟩ : syracuseStep 1237523 = 1856285) B1856285
theorem B1237539 : Blo 1236436 1237539 := bstep (se 1 (by rfl) ⟨928154, by rfl⟩ : syracuseStep 1237539 = 1856309) B1856309
theorem B3523121 : Blo 1236436 3523121 := bstep (se 2 (by rfl) ⟨1321170, by rfl⟩ : syracuseStep 3523121 = 2642341) B2642341
theorem B2785841 : Blo 1236436 2785841 := bstep (se 2 (by rfl) ⟨1044690, by rfl⟩ : syracuseStep 2785841 = 2089381) B2089381
theorem B1237555 : Blo 1236436 1237555 := bstep (se 1 (by rfl) ⟨928166, by rfl⟩ : syracuseStep 1237555 = 1856333) B1856333
theorem B2089523 : Blo 1236436 2089523 := bstep (se 1 (by rfl) ⟨1567142, by rfl⟩ : syracuseStep 2089523 = 3134285) B3134285
theorem B1237571 : Blo 1236436 1237571 := bstep (se 1 (by rfl) ⟨928178, by rfl⟩ : syracuseStep 1237571 = 1856357) B1856357
theorem B2785859 : Blo 1236436 2785859 := bstep (se 1 (by rfl) ⟨2089394, by rfl⟩ : syracuseStep 2785859 = 4178789) B4178789
theorem B1237587 : Blo 1236436 1237587 := bstep (se 1 (by rfl) ⟨928190, by rfl⟩ : syracuseStep 1237587 = 1856381) B1856381
theorem B1237603 : Blo 1236436 1237603 := bstep (se 1 (by rfl) ⟨928202, by rfl⟩ : syracuseStep 1237603 = 1856405) B1856405
theorem B3621485 : Blo 1236436 3621485 := bstep (se 3 (by rfl) ⟨679028, by rfl⟩ : syracuseStep 3621485 = 1358057) B1358057
theorem B1237619 : Blo 1236436 1237619 := bstep (se 1 (by rfl) ⟨928214, by rfl⟩ : syracuseStep 1237619 = 1856429) B1856429
theorem B1237635 : Blo 1236436 1237635 := bstep (se 1 (by rfl) ⟨928226, by rfl⟩ : syracuseStep 1237635 = 1856453) B1856453
theorem B4694669 : Blo 1236436 4694669 := bstep (se 3 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 4694669 = 1760501) B1760501
theorem B4178573 : Blo 1236436 4178573 := bstep (se 3 (by rfl) ⟨783482, by rfl⟩ : syracuseStep 4178573 = 1566965) B1566965
theorem B1237651 : Blo 1236436 1237651 := bstep (se 1 (by rfl) ⟨928238, by rfl⟩ : syracuseStep 1237651 = 1856477) B1856477
theorem B1237667 : Blo 1236436 1237667 := bstep (se 1 (by rfl) ⟨928250, by rfl⟩ : syracuseStep 1237667 = 1856501) B1856501
theorem B1237683 : Blo 1236436 1237683 := bstep (se 1 (by rfl) ⟨928262, by rfl⟩ : syracuseStep 1237683 = 1856525) B1856525
theorem B2089651 : Blo 1236436 2089651 := bstep (se 1 (by rfl) ⟨1567238, by rfl⟩ : syracuseStep 2089651 = 3134477) B3134477
theorem B1237699 : Blo 1236436 1237699 := bstep (se 1 (by rfl) ⟨928274, by rfl⟩ : syracuseStep 1237699 = 1856549) B1856549
theorem B4178627 : Blo 1236436 4178627 := bstep (se 1 (by rfl) ⟨3133970, by rfl⟩ : syracuseStep 4178627 = 6267941) B6267941
theorem B1237715 : Blo 1236436 1237715 := bstep (se 1 (by rfl) ⟨928286, by rfl⟩ : syracuseStep 1237715 = 1856573) B1856573
theorem B1237731 : Blo 1236436 1237731 := bstep (se 1 (by rfl) ⟨928298, by rfl⟩ : syracuseStep 1237731 = 1856597) B1856597
theorem B1237747 : Blo 1236436 1237747 := bstep (se 1 (by rfl) ⟨928310, by rfl⟩ : syracuseStep 1237747 = 1856621) B1856621
theorem B1237763 : Blo 1236436 1237763 := bstep (se 1 (by rfl) ⟨928322, by rfl⟩ : syracuseStep 1237763 = 1856645) B1856645
theorem B1237779 : Blo 1236436 1237779 := bstep (se 1 (by rfl) ⟨928334, by rfl⟩ : syracuseStep 1237779 = 1856669) B1856669
theorem B1237795 : Blo 1236436 1237795 := bstep (se 1 (by rfl) ⟨928346, by rfl⟩ : syracuseStep 1237795 = 1856693) B1856693
theorem B1237811 : Blo 1236436 1237811 := bstep (se 1 (by rfl) ⟨928358, by rfl⟩ : syracuseStep 1237811 = 1856717) B1856717
theorem B2089793 : Blo 1236436 2089793 := bstep (se 2 (by rfl) ⟨783672, by rfl⟩ : syracuseStep 2089793 = 1567345) B1567345
theorem B1565507 : Blo 1236436 1565507 := bstep (se 1 (by rfl) ⟨1174130, by rfl⟩ : syracuseStep 1565507 = 2348261) B2348261
theorem B1237827 : Blo 1236436 1237827 := bstep (se 1 (by rfl) ⟨928370, by rfl⟩ : syracuseStep 1237827 = 1856741) B1856741
theorem B1983313 : Blo 1236436 1983313 := bstep (se 2 (by rfl) ⟨743742, by rfl⟩ : syracuseStep 1983313 = 1487485) B1487485
theorem B1237843 : Blo 1236436 1237843 := bstep (se 1 (by rfl) ⟨928382, by rfl⟩ : syracuseStep 1237843 = 1856765) B1856765
theorem B2786129 : Blo 1236436 2786129 := bstep (se 2 (by rfl) ⟨1044798, by rfl⟩ : syracuseStep 2786129 = 2089597) B2089597
theorem B1237859 : Blo 1236436 1237859 := bstep (se 1 (by rfl) ⟨928394, by rfl⟩ : syracuseStep 1237859 = 1856789) B1856789
theorem B2786147 : Blo 1236436 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B1237875 : Blo 1236436 1237875 := bstep (se 1 (by rfl) ⟨928406, by rfl⟩ : syracuseStep 1237875 = 1856813) B1856813
theorem B1237891 : Blo 1236436 1237891 := bstep (se 1 (by rfl) ⟨928418, by rfl⟩ : syracuseStep 1237891 = 1856837) B1856837
theorem B1237907 : Blo 1236436 1237907 := bstep (se 1 (by rfl) ⟨928430, by rfl⟩ : syracuseStep 1237907 = 1856861) B1856861
theorem B1237923 : Blo 1236436 1237923 := bstep (se 1 (by rfl) ⟨928442, by rfl⟩ : syracuseStep 1237923 = 1856885) B1856885
theorem B1254323 : Blo 1236436 1254323 := bstep (se 1 (by rfl) ⟨940742, by rfl⟩ : syracuseStep 1254323 = 1881485) B1881485
theorem B1237939 : Blo 1236436 1237939 := bstep (se 1 (by rfl) ⟨928454, by rfl⟩ : syracuseStep 1237939 = 1856909) B1856909
theorem B1237955 : Blo 1236436 1237955 := bstep (se 1 (by rfl) ⟨928466, by rfl⟩ : syracuseStep 1237955 = 1856933) B1856933
theorem B4178897 : Blo 1236436 4178897 := bstep (se 2 (by rfl) ⟨1567086, by rfl⟩ : syracuseStep 4178897 = 3134173) B3134173
theorem B1237971 : Blo 1236436 1237971 := bstep (se 1 (by rfl) ⟨928478, by rfl⟩ : syracuseStep 1237971 = 1856957) B1856957
theorem B1237987 : Blo 1236436 1237987 := bstep (se 1 (by rfl) ⟨928490, by rfl⟩ : syracuseStep 1237987 = 1856981) B1856981
theorem B1238003 : Blo 1236436 1238003 := bstep (se 1 (by rfl) ⟨928502, by rfl⟩ : syracuseStep 1238003 = 1857005) B1857005
theorem B1238019 : Blo 1236436 1238019 := bstep (se 1 (by rfl) ⟨928514, by rfl⟩ : syracuseStep 1238019 = 1857029) B1857029
theorem B7046149 : Blo 1236436 7046149 := bstep (se 4 (by rfl) ⟨660576, by rfl⟩ : syracuseStep 7046149 = 1321153) B1321153
theorem B1238035 : Blo 1236436 1238035 := bstep (se 1 (by rfl) ⟨928526, by rfl⟩ : syracuseStep 1238035 = 1857053) B1857053
theorem B1238051 : Blo 1236436 1238051 := bstep (se 1 (by rfl) ⟨928538, by rfl⟩ : syracuseStep 1238051 = 1857077) B1857077
theorem B2974769 : Blo 1236436 2974769 := bstep (se 2 (by rfl) ⟨1115538, by rfl⟩ : syracuseStep 2974769 = 2231077) B2231077
theorem B1238067 : Blo 1236436 1238067 := bstep (se 1 (by rfl) ⟨928550, by rfl⟩ : syracuseStep 1238067 = 1857101) B1857101
theorem B1238083 : Blo 1236436 1238083 := bstep (se 1 (by rfl) ⟨928562, by rfl⟩ : syracuseStep 1238083 = 1857125) B1857125
theorem B1238099 : Blo 1236436 1238099 := bstep (se 1 (by rfl) ⟨928574, by rfl⟩ : syracuseStep 1238099 = 1857149) B1857149
theorem B1762403 : Blo 1236436 1762403 := bstep (se 1 (by rfl) ⟨1321802, by rfl⟩ : syracuseStep 1762403 = 2643605) B2643605
theorem B1238115 : Blo 1236436 1238115 := bstep (se 1 (by rfl) ⟨928586, by rfl⟩ : syracuseStep 1238115 = 1857173) B1857173
theorem B2786417 : Blo 1236436 2786417 := bstep (se 2 (by rfl) ⟨1044906, by rfl⟩ : syracuseStep 2786417 = 2089813) B2089813
theorem B1238131 : Blo 1236436 1238131 := bstep (se 1 (by rfl) ⟨928598, by rfl⟩ : syracuseStep 1238131 = 1857197) B1857197
theorem B1238147 : Blo 1236436 1238147 := bstep (se 1 (by rfl) ⟨928610, by rfl⟩ : syracuseStep 1238147 = 1857221) B1857221
theorem B2786435 : Blo 1236436 2786435 := bstep (se 1 (by rfl) ⟨2089826, by rfl⟩ : syracuseStep 2786435 = 4179653) B4179653
theorem B1238163 : Blo 1236436 1238163 := bstep (se 1 (by rfl) ⟨928622, by rfl⟩ : syracuseStep 1238163 = 1857245) B1857245
theorem B1238179 : Blo 1236436 1238179 := bstep (se 1 (by rfl) ⟨928634, by rfl⟩ : syracuseStep 1238179 = 1857269) B1857269
theorem B1238195 : Blo 1236436 1238195 := bstep (se 1 (by rfl) ⟨928646, by rfl⟩ : syracuseStep 1238195 = 1857293) B1857293
theorem B1238211 : Blo 1236436 1238211 := bstep (se 1 (by rfl) ⟨928658, by rfl⟩ : syracuseStep 1238211 = 1857317) B1857317
theorem B6685901 : Blo 1236436 6685901 := bstep (se 3 (by rfl) ⟨1253606, by rfl⟩ : syracuseStep 6685901 = 2507213) B2507213
theorem B1238227 : Blo 1236436 1238227 := bstep (se 1 (by rfl) ⟨928670, by rfl⟩ : syracuseStep 1238227 = 1857341) B1857341
theorem B1238243 : Blo 1236436 1238243 := bstep (se 1 (by rfl) ⟨928682, by rfl⟩ : syracuseStep 1238243 = 1857365) B1857365
theorem B3130609 : Blo 1236436 3130609 := bstep (se 2 (by rfl) ⟨1173978, by rfl⟩ : syracuseStep 3130609 = 2347957) B2347957
theorem B1238259 : Blo 1236436 1238259 := bstep (se 1 (by rfl) ⟨928694, by rfl⟩ : syracuseStep 1238259 = 1857389) B1857389
theorem B1238275 : Blo 1236436 1238275 := bstep (se 1 (by rfl) ⟨928706, by rfl⟩ : syracuseStep 1238275 = 1857413) B1857413
theorem B1238291 : Blo 1236436 1238291 := bstep (se 1 (by rfl) ⟨928718, by rfl⟩ : syracuseStep 1238291 = 1857437) B1857437
theorem B6260003 : Blo 1236436 6260003 := bstep (se 1 (by rfl) ⟨4695002, by rfl⟩ : syracuseStep 6260003 = 9390005) B9390005
theorem B1238307 : Blo 1236436 1238307 := bstep (se 1 (by rfl) ⟨928730, by rfl⟩ : syracuseStep 1238307 = 1857461) B1857461
theorem B1238323 : Blo 1236436 1238323 := bstep (se 1 (by rfl) ⟨928742, by rfl⟩ : syracuseStep 1238323 = 1857485) B1857485
theorem B1238339 : Blo 1236436 1238339 := bstep (se 1 (by rfl) ⟨928754, by rfl⟩ : syracuseStep 1238339 = 1857509) B1857509
theorem B10028357 : Blo 1236436 10028357 := bstep (se 4 (by rfl) ⟨940158, by rfl⟩ : syracuseStep 10028357 = 1880317) B1880317
theorem B1238355 : Blo 1236436 1238355 := bstep (se 1 (by rfl) ⟨928766, by rfl⟩ : syracuseStep 1238355 = 1857533) B1857533
theorem B1238371 : Blo 1236436 1238371 := bstep (se 1 (by rfl) ⟨928778, by rfl⟩ : syracuseStep 1238371 = 1857557) B1857557
theorem B1238387 : Blo 1236436 1238387 := bstep (se 1 (by rfl) ⟨928790, by rfl⟩ : syracuseStep 1238387 = 1857581) B1857581
theorem B1238403 : Blo 1236436 1238403 := bstep (se 1 (by rfl) ⟨928802, by rfl⟩ : syracuseStep 1238403 = 1857605) B1857605
theorem B1238419 : Blo 1236436 1238419 := bstep (se 1 (by rfl) ⟨928814, by rfl⟩ : syracuseStep 1238419 = 1857629) B1857629
theorem B1238435 : Blo 1236436 1238435 := bstep (se 1 (by rfl) ⟨928826, by rfl⟩ : syracuseStep 1238435 = 1857653) B1857653
theorem B3524077 : Blo 1236436 3524077 := bstep (se 3 (by rfl) ⟨660764, by rfl⟩ : syracuseStep 3524077 = 1321529) B1321529
theorem B4179437 : Blo 1236436 4179437 := bstep (se 3 (by rfl) ⟨783644, by rfl⟩ : syracuseStep 4179437 = 1567289) B1567289
theorem B3130883 : Blo 1236436 3130883 := bstep (se 1 (by rfl) ⟨2348162, by rfl⟩ : syracuseStep 3130883 = 4696325) B4696325
theorem B1566211 : Blo 1236436 1566211 := bstep (se 1 (by rfl) ⟨1174658, by rfl⟩ : syracuseStep 1566211 = 2349317) B2349317
theorem B4179491 : Blo 1236436 4179491 := bstep (se 1 (by rfl) ⟨3134618, by rfl⟩ : syracuseStep 4179491 = 6269237) B6269237
theorem B1566307 : Blo 1236436 1566307 := bstep (se 1 (by rfl) ⟨1174730, by rfl⟩ : syracuseStep 1566307 = 2349461) B2349461
theorem B13567601 : Blo 1236436 13567601 := bstep (se 2 (by rfl) ⟨5087850, by rfl⟩ : syracuseStep 13567601 = 10175701) B10175701
theorem B2975363 : Blo 1236436 2975363 := bstep (se 1 (by rfl) ⟨2231522, by rfl⟩ : syracuseStep 2975363 = 4463045) B4463045
theorem B8152709 : Blo 1236436 8152709 := bstep (se 4 (by rfl) ⟨764316, by rfl⟩ : syracuseStep 8152709 = 1528633) B1528633
theorem B3131075 : Blo 1236436 3131075 := bstep (se 1 (by rfl) ⟨2348306, by rfl⟩ : syracuseStep 3131075 = 4696613) B4696613
theorem B3524305 : Blo 1236436 3524305 := bstep (se 2 (by rfl) ⟨1321614, by rfl⟩ : syracuseStep 3524305 = 2643229) B2643229
theorem B1763041 : Blo 1236436 1763041 := bstep (se 2 (by rfl) ⟨661140, by rfl⟩ : syracuseStep 1763041 = 1322281) B1322281
theorem B2975459 : Blo 1236436 2975459 := bstep (se 1 (by rfl) ⟨2231594, by rfl⟩ : syracuseStep 2975459 = 4463189) B4463189
theorem B1763155 : Blo 1236436 1763155 := bstep (se 1 (by rfl) ⟨1322366, by rfl⟩ : syracuseStep 1763155 = 2644733) B2644733
theorem B3524465 : Blo 1236436 3524465 := bstep (se 2 (by rfl) ⟨1321674, by rfl⟩ : syracuseStep 3524465 = 2643349) B2643349
theorem B3344333 : Blo 1236436 3344333 := bstep (se 3 (by rfl) ⟨627062, by rfl⟩ : syracuseStep 3344333 = 1254125) B1254125
theorem B1320931 : Blo 1236436 1320931 := bstep (se 1 (by rfl) ⟨990698, by rfl⟩ : syracuseStep 1320931 = 1981397) B1981397
theorem B3524579 : Blo 1236436 3524579 := bstep (se 1 (by rfl) ⟨2643434, by rfl⟩ : syracuseStep 3524579 = 5286869) B5286869
theorem B6268913 : Blo 1236436 6268913 := bstep (se 2 (by rfl) ⟨2350842, by rfl⟩ : syracuseStep 6268913 = 4701685) B4701685
theorem B3344419 : Blo 1236436 3344419 := bstep (se 1 (by rfl) ⟨2508314, by rfl⟩ : syracuseStep 3344419 = 5016629) B5016629
theorem B6260813 : Blo 1236436 6260813 := bstep (se 3 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 6260813 = 2347805) B2347805
theorem B1566803 : Blo 1236436 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B38070499 : Blo 1236436 38070499 := bstep (se 1 (by rfl) ⟨28552874, by rfl⟩ : syracuseStep 38070499 = 57105749) B57105749
theorem B9038051 : Blo 1236436 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B1673555 : Blo 1236436 1673555 := bstep (se 1 (by rfl) ⟨1255166, by rfl⟩ : syracuseStep 1673555 = 2510333) B2510333
theorem B12691811 : Blo 1236436 12691811 := bstep (se 1 (by rfl) ⟨9518858, by rfl⟩ : syracuseStep 12691811 = 19037717) B19037717
theorem B5016113 : Blo 1236436 5016113 := bstep (se 2 (by rfl) ⟨1881042, by rfl⟩ : syracuseStep 5016113 = 3762085) B3762085
theorem B3172945 : Blo 1236436 3172945 := bstep (se 2 (by rfl) ⟨1189854, by rfl⟩ : syracuseStep 3172945 = 2379709) B2379709
theorem B3132017 : Blo 1236436 3132017 := bstep (se 2 (by rfl) ⟨1174506, by rfl⟩ : syracuseStep 3132017 = 2349013) B2349013
theorem B3132067 : Blo 1236436 3132067 := bstep (se 1 (by rfl) ⟨2349050, by rfl⟩ : syracuseStep 3132067 = 4698101) B4698101
theorem B2116289 : Blo 1236436 2116289 := bstep (se 2 (by rfl) ⟨793608, by rfl⟩ : syracuseStep 2116289 = 1587217) B1587217
theorem B14093027 : Blo 1236436 14093027 := bstep (se 1 (by rfl) ⟨10569770, by rfl⟩ : syracuseStep 14093027 = 21139541) B21139541
theorem B7146211 : Blo 1236436 7146211 := bstep (se 1 (by rfl) ⟨5359658, by rfl⟩ : syracuseStep 7146211 = 10719317) B10719317
theorem B3132209 : Blo 1236436 3132209 := bstep (se 2 (by rfl) ⟨1174578, by rfl⟩ : syracuseStep 3132209 = 2349157) B2349157
theorem B7048133 : Blo 1236436 7048133 := bstep (se 4 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 7048133 = 1321525) B1321525
theorem B3525581 : Blo 1236436 3525581 := bstep (se 3 (by rfl) ⟨661046, by rfl⟩ : syracuseStep 3525581 = 1322093) B1322093
theorem B1321939 : Blo 1236436 1321939 := bstep (se 1 (by rfl) ⟨991454, by rfl⟩ : syracuseStep 1321939 = 1982909) B1982909
theorem B8915939 : Blo 1236436 8915939 := bstep (se 1 (by rfl) ⟨6686954, by rfl⟩ : syracuseStep 8915939 = 13373909) B13373909
theorem B3345457 : Blo 1236436 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B3525763 : Blo 1236436 3525763 := bstep (se 1 (by rfl) ⟨2644322, by rfl⟩ : syracuseStep 3525763 = 5288645) B5288645
theorem B7933069 : Blo 1236436 7933069 := bstep (se 3 (by rfl) ⟨1487450, by rfl⟩ : syracuseStep 7933069 = 2974901) B2974901
theorem B3345553 : Blo 1236436 3345553 := bstep (se 2 (by rfl) ⟨1254582, by rfl⟩ : syracuseStep 3345553 = 2509165) B2509165
theorem B1854659 : Blo 1236436 1854659 := bstep (se 1 (by rfl) ⟨1390994, by rfl⟩ : syracuseStep 1854659 = 2781989) B2781989
theorem B1854689 : Blo 1236436 1854689 := bstep (se 2 (by rfl) ⟨695508, by rfl⟩ : syracuseStep 1854689 = 1391017) B1391017
theorem B1854707 : Blo 1236436 1854707 := bstep (se 1 (by rfl) ⟨1391030, by rfl⟩ : syracuseStep 1854707 = 2782061) B2782061
theorem B1854737 : Blo 1236436 1854737 := bstep (se 2 (by rfl) ⟨695526, by rfl⟩ : syracuseStep 1854737 = 1391053) B1391053
theorem B1854755 : Blo 1236436 1854755 := bstep (se 1 (by rfl) ⟨1391066, by rfl⟩ : syracuseStep 1854755 = 2782133) B2782133
theorem B3525923 : Blo 1236436 3525923 := bstep (se 1 (by rfl) ⟨2644442, by rfl⟩ : syracuseStep 3525923 = 5288885) B5288885
theorem B1854785 : Blo 1236436 1854785 := bstep (se 2 (by rfl) ⟨695544, by rfl⟩ : syracuseStep 1854785 = 1391089) B1391089
theorem B1854803 : Blo 1236436 1854803 := bstep (se 1 (by rfl) ⟨1391102, by rfl⟩ : syracuseStep 1854803 = 2782205) B2782205
theorem B1854833 : Blo 1236436 1854833 := bstep (se 2 (by rfl) ⟨695562, by rfl⟩ : syracuseStep 1854833 = 1391125) B1391125
theorem B1854851 : Blo 1236436 1854851 := bstep (se 1 (by rfl) ⟨1391138, by rfl⟩ : syracuseStep 1854851 = 2782277) B2782277
theorem B1854881 : Blo 1236436 1854881 := bstep (se 2 (by rfl) ⟨695580, by rfl⟩ : syracuseStep 1854881 = 1391161) B1391161
theorem B1854899 : Blo 1236436 1854899 := bstep (se 1 (by rfl) ⟨1391174, by rfl⟩ : syracuseStep 1854899 = 2782349) B2782349
theorem B2821571 : Blo 1236436 2821571 := bstep (se 1 (by rfl) ⟨2116178, by rfl⟩ : syracuseStep 2821571 = 4232357) B4232357
theorem B7531973 : Blo 1236436 7531973 := bstep (se 4 (by rfl) ⟨706122, by rfl⟩ : syracuseStep 7531973 = 1412245) B1412245
theorem B1854929 : Blo 1236436 1854929 := bstep (se 2 (by rfl) ⟨695598, by rfl⟩ : syracuseStep 1854929 = 1391197) B1391197
theorem B1854947 : Blo 1236436 1854947 := bstep (se 1 (by rfl) ⟨1391210, by rfl⟩ : syracuseStep 1854947 = 2782421) B2782421
theorem B4697585 : Blo 1236436 4697585 := bstep (se 2 (by rfl) ⟨1761594, by rfl⟩ : syracuseStep 4697585 = 3523189) B3523189
theorem B1854977 : Blo 1236436 1854977 := bstep (se 2 (by rfl) ⟨695616, by rfl⟩ : syracuseStep 1854977 = 1391233) B1391233
theorem B3345923 : Blo 1236436 3345923 := bstep (se 1 (by rfl) ⟨2509442, by rfl⟩ : syracuseStep 3345923 = 5018885) B5018885
theorem B1854995 : Blo 1236436 1854995 := bstep (se 1 (by rfl) ⟨1391246, by rfl⟩ : syracuseStep 1854995 = 2782493) B2782493
theorem B1486355 : Blo 1236436 1486355 := bstep (se 1 (by rfl) ⟨1114766, by rfl⟩ : syracuseStep 1486355 = 2229533) B2229533
theorem B1855025 : Blo 1236436 1855025 := bstep (se 2 (by rfl) ⟨695634, by rfl⟩ : syracuseStep 1855025 = 1391269) B1391269
theorem B1855043 : Blo 1236436 1855043 := bstep (se 1 (by rfl) ⟨1391282, by rfl⟩ : syracuseStep 1855043 = 2782565) B2782565
theorem B4173389 : Blo 1236436 4173389 := bstep (se 3 (by rfl) ⟨782510, by rfl⟩ : syracuseStep 4173389 = 1565021) B1565021
theorem B1855073 : Blo 1236436 1855073 := bstep (se 2 (by rfl) ⟨695652, by rfl⟩ : syracuseStep 1855073 = 1391305) B1391305
theorem B1855091 : Blo 1236436 1855091 := bstep (se 1 (by rfl) ⟨1391318, by rfl⟩ : syracuseStep 1855091 = 2782637) B2782637
theorem B4173443 : Blo 1236436 4173443 := bstep (se 1 (by rfl) ⟨3130082, by rfl⟩ : syracuseStep 4173443 = 6260165) B6260165
theorem B17829517 : Blo 1236436 17829517 := bstep (se 3 (by rfl) ⟨3343034, by rfl⟩ : syracuseStep 17829517 = 6686069) B6686069
theorem B1855121 : Blo 1236436 1855121 := bstep (se 2 (by rfl) ⟨695670, by rfl⟩ : syracuseStep 1855121 = 1391341) B1391341
theorem B2117267 : Blo 1236436 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B1855139 : Blo 1236436 1855139 := bstep (se 1 (by rfl) ⟨1391354, by rfl⟩ : syracuseStep 1855139 = 2782709) B2782709
theorem B8466083 : Blo 1236436 8466083 := bstep (se 1 (by rfl) ⟨6349562, by rfl⟩ : syracuseStep 8466083 = 12699125) B12699125
theorem B1855169 : Blo 1236436 1855169 := bstep (se 2 (by rfl) ⟨695688, by rfl⟩ : syracuseStep 1855169 = 1391377) B1391377
theorem B1855187 : Blo 1236436 1855187 := bstep (se 1 (by rfl) ⟨1391390, by rfl⟩ : syracuseStep 1855187 = 2782781) B2782781
theorem B1855217 : Blo 1236436 1855217 := bstep (se 2 (by rfl) ⟨695706, by rfl⟩ : syracuseStep 1855217 = 1391413) B1391413
theorem B1855235 : Blo 1236436 1855235 := bstep (se 1 (by rfl) ⟨1391426, by rfl⟩ : syracuseStep 1855235 = 2782853) B2782853
theorem B8916749 : Blo 1236436 8916749 := bstep (se 3 (by rfl) ⟨1671890, by rfl⟩ : syracuseStep 8916749 = 3343781) B3343781
theorem B7147277 : Blo 1236436 7147277 := bstep (se 3 (by rfl) ⟨1340114, by rfl⟩ : syracuseStep 7147277 = 2680229) B2680229
theorem B3133201 : Blo 1236436 3133201 := bstep (se 2 (by rfl) ⟨1174950, by rfl⟩ : syracuseStep 3133201 = 2349901) B2349901
theorem B1855265 : Blo 1236436 1855265 := bstep (se 2 (by rfl) ⟨695724, by rfl⟩ : syracuseStep 1855265 = 1391449) B1391449
theorem B1855283 : Blo 1236436 1855283 := bstep (se 1 (by rfl) ⟨1391462, by rfl⟩ : syracuseStep 1855283 = 2782925) B2782925
theorem B1855313 : Blo 1236436 1855313 := bstep (se 2 (by rfl) ⟨695742, by rfl⟩ : syracuseStep 1855313 = 1391485) B1391485
theorem B1855331 : Blo 1236436 1855331 := bstep (se 1 (by rfl) ⟨1391498, by rfl⟩ : syracuseStep 1855331 = 2782997) B2782997
theorem B5017457 : Blo 1236436 5017457 := bstep (se 2 (by rfl) ⟨1881546, by rfl⟩ : syracuseStep 5017457 = 3763093) B3763093
theorem B1855361 : Blo 1236436 1855361 := bstep (se 2 (by rfl) ⟨695760, by rfl⟩ : syracuseStep 1855361 = 1391521) B1391521
theorem B4173713 : Blo 1236436 4173713 := bstep (se 2 (by rfl) ⟨1565142, by rfl⟩ : syracuseStep 4173713 = 3130285) B3130285
theorem B1855379 : Blo 1236436 1855379 := bstep (se 1 (by rfl) ⟨1391534, by rfl⟩ : syracuseStep 1855379 = 2783069) B2783069
theorem B1855409 : Blo 1236436 1855409 := bstep (se 2 (by rfl) ⟨695778, by rfl⟩ : syracuseStep 1855409 = 1391557) B1391557
theorem B1855427 : Blo 1236436 1855427 := bstep (se 1 (by rfl) ⟨1391570, by rfl⟩ : syracuseStep 1855427 = 2783141) B2783141
theorem B1855457 : Blo 1236436 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B15044579 : Blo 1236436 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B1855475 : Blo 1236436 1855475 := bstep (se 1 (by rfl) ⟨1391606, by rfl⟩ : syracuseStep 1855475 = 2783213) B2783213
theorem B5640205 : Blo 1236436 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B1855505 : Blo 1236436 1855505 := bstep (se 2 (by rfl) ⟨695814, by rfl⟩ : syracuseStep 1855505 = 1391629) B1391629
theorem B1880099 : Blo 1236436 1880099 := bstep (se 1 (by rfl) ⟨1410074, by rfl⟩ : syracuseStep 1880099 = 2820149) B2820149
theorem B1855523 : Blo 1236436 1855523 := bstep (se 1 (by rfl) ⟨1391642, by rfl⟩ : syracuseStep 1855523 = 2783285) B2783285
theorem B3133475 : Blo 1236436 3133475 := bstep (se 1 (by rfl) ⟨2350106, by rfl⟩ : syracuseStep 3133475 = 4700213) B4700213
theorem B1855553 : Blo 1236436 1855553 := bstep (se 2 (by rfl) ⟨695832, by rfl⟩ : syracuseStep 1855553 = 1391665) B1391665
theorem B1855571 : Blo 1236436 1855571 := bstep (se 1 (by rfl) ⟨1391678, by rfl⟩ : syracuseStep 1855571 = 2783357) B2783357
theorem B3764333 : Blo 1236436 3764333 := bstep (se 3 (by rfl) ⟨705812, by rfl⟩ : syracuseStep 3764333 = 1411625) B1411625
theorem B2642033 : Blo 1236436 2642033 := bstep (se 2 (by rfl) ⟨990762, by rfl⟩ : syracuseStep 2642033 = 1981525) B1981525
theorem B1855601 : Blo 1236436 1855601 := bstep (se 2 (by rfl) ⟨695850, by rfl⟩ : syracuseStep 1855601 = 1391701) B1391701
theorem B2642051 : Blo 1236436 2642051 := bstep (se 1 (by rfl) ⟨1981538, by rfl⟩ : syracuseStep 2642051 = 3963077) B3963077
theorem B1855619 : Blo 1236436 1855619 := bstep (se 1 (by rfl) ⟨1391714, by rfl⟩ : syracuseStep 1855619 = 2783429) B2783429
theorem B1855649 : Blo 1236436 1855649 := bstep (se 2 (by rfl) ⟨695868, by rfl⟩ : syracuseStep 1855649 = 1391737) B1391737
theorem B1855667 : Blo 1236436 1855667 := bstep (se 1 (by rfl) ⟨1391750, by rfl⟩ : syracuseStep 1855667 = 2783501) B2783501
theorem B1855697 : Blo 1236436 1855697 := bstep (se 2 (by rfl) ⟨695886, by rfl⟩ : syracuseStep 1855697 = 1391773) B1391773
theorem B1855715 : Blo 1236436 1855715 := bstep (se 1 (by rfl) ⟨1391786, by rfl⟩ : syracuseStep 1855715 = 2783573) B2783573
theorem B3133667 : Blo 1236436 3133667 := bstep (se 1 (by rfl) ⟨2350250, by rfl⟩ : syracuseStep 3133667 = 4700501) B4700501
theorem B1855745 : Blo 1236436 1855745 := bstep (se 2 (by rfl) ⟨695904, by rfl⟩ : syracuseStep 1855745 = 1391809) B1391809
theorem B1855763 : Blo 1236436 1855763 := bstep (se 1 (by rfl) ⟨1391822, by rfl⟩ : syracuseStep 1855763 = 2783645) B2783645
theorem B1855793 : Blo 1236436 1855793 := bstep (se 2 (by rfl) ⟨695922, by rfl⟩ : syracuseStep 1855793 = 1391845) B1391845
theorem B1855811 : Blo 1236436 1855811 := bstep (se 1 (by rfl) ⟨1391858, by rfl⟩ : syracuseStep 1855811 = 2783717) B2783717
theorem B1855841 : Blo 1236436 1855841 := bstep (se 2 (by rfl) ⟨695940, by rfl⟩ : syracuseStep 1855841 = 1391881) B1391881
theorem B1855859 : Blo 1236436 1855859 := bstep (se 1 (by rfl) ⟨1391894, by rfl⟩ : syracuseStep 1855859 = 2783789) B2783789
theorem B1855889 : Blo 1236436 1855889 := bstep (se 2 (by rfl) ⟨695958, by rfl⟩ : syracuseStep 1855889 = 1391917) B1391917
theorem B1855907 : Blo 1236436 1855907 := bstep (se 1 (by rfl) ⟨1391930, by rfl⟩ : syracuseStep 1855907 = 2783861) B2783861
theorem B4174253 : Blo 1236436 4174253 := bstep (se 3 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 4174253 = 1565345) B1565345
theorem B1880513 : Blo 1236436 1880513 := bstep (se 2 (by rfl) ⟨705192, by rfl⟩ : syracuseStep 1880513 = 1410385) B1410385
theorem B1855937 : Blo 1236436 1855937 := bstep (se 2 (by rfl) ⟨695976, by rfl⟩ : syracuseStep 1855937 = 1391953) B1391953
theorem B1855955 : Blo 1236436 1855955 := bstep (se 1 (by rfl) ⟨1391966, by rfl⟩ : syracuseStep 1855955 = 2783933) B2783933
theorem B4174307 : Blo 1236436 4174307 := bstep (se 1 (by rfl) ⟨3130730, by rfl⟩ : syracuseStep 4174307 = 6261461) B6261461
theorem B1855985 : Blo 1236436 1855985 := bstep (se 2 (by rfl) ⟨695994, by rfl⟩ : syracuseStep 1855985 = 1391989) B1391989
theorem B1856003 : Blo 1236436 1856003 := bstep (se 1 (by rfl) ⟨1392002, by rfl⟩ : syracuseStep 1856003 = 2784005) B2784005
theorem B1856033 : Blo 1236436 1856033 := bstep (se 2 (by rfl) ⟨696012, by rfl⟩ : syracuseStep 1856033 = 1392025) B1392025
theorem B2347555 : Blo 1236436 2347555 := bstep (se 1 (by rfl) ⟨1760666, by rfl⟩ : syracuseStep 2347555 = 3521333) B3521333
theorem B1856051 : Blo 1236436 1856051 := bstep (se 1 (by rfl) ⟨1392038, by rfl⟩ : syracuseStep 1856051 = 2784077) B2784077
theorem B6779461 : Blo 1236436 6779461 := bstep (se 4 (by rfl) ⟨635574, by rfl⟩ : syracuseStep 6779461 = 1271149) B1271149
theorem B1856081 : Blo 1236436 1856081 := bstep (se 2 (by rfl) ⟨696030, by rfl⟩ : syracuseStep 1856081 = 1392061) B1392061
theorem B1856099 : Blo 1236436 1856099 := bstep (se 1 (by rfl) ⟨1392074, by rfl⟩ : syracuseStep 1856099 = 2784149) B2784149
theorem B5288561 : Blo 1236436 5288561 := bstep (se 2 (by rfl) ⟨1983210, by rfl⟩ : syracuseStep 5288561 = 3966421) B3966421
theorem B1856129 : Blo 1236436 1856129 := bstep (se 2 (by rfl) ⟨696048, by rfl⟩ : syracuseStep 1856129 = 1392097) B1392097
theorem B1856147 : Blo 1236436 1856147 := bstep (se 1 (by rfl) ⟨1392110, by rfl⟩ : syracuseStep 1856147 = 2784221) B2784221
theorem B5288611 : Blo 1236436 5288611 := bstep (se 1 (by rfl) ⟨3966458, by rfl⟩ : syracuseStep 5288611 = 7932917) B7932917
theorem B1856177 : Blo 1236436 1856177 := bstep (se 2 (by rfl) ⟨696066, by rfl⟩ : syracuseStep 1856177 = 1392133) B1392133
theorem B1856195 : Blo 1236436 1856195 := bstep (se 1 (by rfl) ⟨1392146, by rfl⟩ : syracuseStep 1856195 = 2784293) B2784293
theorem B1856225 : Blo 1236436 1856225 := bstep (se 2 (by rfl) ⟨696084, by rfl⟩ : syracuseStep 1856225 = 1392169) B1392169
theorem B4174577 : Blo 1236436 4174577 := bstep (se 2 (by rfl) ⟨1565466, by rfl⟩ : syracuseStep 4174577 = 3130933) B3130933
theorem B1856243 : Blo 1236436 1856243 := bstep (se 1 (by rfl) ⟨1392182, by rfl⟩ : syracuseStep 1856243 = 2784365) B2784365
theorem B1856273 : Blo 1236436 1856273 := bstep (se 2 (by rfl) ⟨696102, by rfl⟩ : syracuseStep 1856273 = 1392205) B1392205
theorem B1856291 : Blo 1236436 1856291 := bstep (se 1 (by rfl) ⟨1392218, by rfl⟩ : syracuseStep 1856291 = 2784437) B2784437
theorem B1856321 : Blo 1236436 1856321 := bstep (se 2 (by rfl) ⟨696120, by rfl⟩ : syracuseStep 1856321 = 1392241) B1392241
theorem B1856339 : Blo 1236436 1856339 := bstep (se 1 (by rfl) ⟨1392254, by rfl⟩ : syracuseStep 1856339 = 2784509) B2784509
theorem B1856369 : Blo 1236436 1856369 := bstep (se 2 (by rfl) ⟨696138, by rfl⟩ : syracuseStep 1856369 = 1392277) B1392277
theorem B1856387 : Blo 1236436 1856387 := bstep (se 1 (by rfl) ⟨1392290, by rfl⟩ : syracuseStep 1856387 = 2784581) B2784581
theorem B2782097 : Blo 1236436 2782097 := bstep (se 2 (by rfl) ⟨1043286, by rfl⟩ : syracuseStep 2782097 = 2086573) B2086573
theorem B1856417 : Blo 1236436 1856417 := bstep (se 2 (by rfl) ⟨696156, by rfl⟩ : syracuseStep 1856417 = 1392313) B1392313
theorem B2782115 : Blo 1236436 2782115 := bstep (se 1 (by rfl) ⟨2086586, by rfl⟩ : syracuseStep 2782115 = 4173173) B4173173
theorem B4699043 : Blo 1236436 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B6263729 : Blo 1236436 6263729 := bstep (se 2 (by rfl) ⟨2348898, by rfl⟩ : syracuseStep 6263729 = 4697797) B4697797
theorem B1856435 : Blo 1236436 1856435 := bstep (se 1 (by rfl) ⟨1392326, by rfl⟩ : syracuseStep 1856435 = 2784653) B2784653
theorem B1856465 : Blo 1236436 1856465 := bstep (se 2 (by rfl) ⟨696174, by rfl⟩ : syracuseStep 1856465 = 1392349) B1392349
theorem B2348003 : Blo 1236436 2348003 := bstep (se 1 (by rfl) ⟨1761002, by rfl⟩ : syracuseStep 2348003 = 3522005) B3522005
theorem B1856483 : Blo 1236436 1856483 := bstep (se 1 (by rfl) ⟨1392362, by rfl⟩ : syracuseStep 1856483 = 2784725) B2784725
theorem B1856513 : Blo 1236436 1856513 := bstep (se 2 (by rfl) ⟨696192, by rfl⟩ : syracuseStep 1856513 = 1392385) B1392385
theorem B1856531 : Blo 1236436 1856531 := bstep (se 1 (by rfl) ⟨1392398, by rfl⟩ : syracuseStep 1856531 = 2784797) B2784797
theorem B2479153 : Blo 1236436 2479153 := bstep (se 2 (by rfl) ⟨929682, by rfl⟩ : syracuseStep 2479153 = 1859365) B1859365
theorem B1856561 : Blo 1236436 1856561 := bstep (se 2 (by rfl) ⟨696210, by rfl⟩ : syracuseStep 1856561 = 1392421) B1392421
theorem B1856579 : Blo 1236436 1856579 := bstep (se 1 (by rfl) ⟨1392434, by rfl⟩ : syracuseStep 1856579 = 2784869) B2784869
theorem B1856609 : Blo 1236436 1856609 := bstep (se 2 (by rfl) ⟨696228, by rfl⟩ : syracuseStep 1856609 = 1392457) B1392457
theorem B4289645 : Blo 1236436 4289645 := bstep (se 3 (by rfl) ⟨804308, by rfl⟩ : syracuseStep 4289645 = 1608617) B1608617
theorem B1856627 : Blo 1236436 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B1856657 : Blo 1236436 1856657 := bstep (se 2 (by rfl) ⟨696246, by rfl⟩ : syracuseStep 1856657 = 1392493) B1392493
theorem B3134609 : Blo 1236436 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B1856675 : Blo 1236436 1856675 := bstep (se 1 (by rfl) ⟨1392506, by rfl⟩ : syracuseStep 1856675 = 2785013) B2785013
theorem B4764835 : Blo 1236436 4764835 := bstep (se 1 (by rfl) ⟨3573626, by rfl⟩ : syracuseStep 4764835 = 7147253) B7147253
theorem B2782385 : Blo 1236436 2782385 := bstep (se 2 (by rfl) ⟨1043394, by rfl⟩ : syracuseStep 2782385 = 2086789) B2086789
theorem B1856705 : Blo 1236436 1856705 := bstep (se 2 (by rfl) ⟨696264, by rfl⟩ : syracuseStep 1856705 = 1392529) B1392529
theorem B2782403 : Blo 1236436 2782403 := bstep (se 1 (by rfl) ⟨2086802, by rfl⟩ : syracuseStep 2782403 = 4173605) B4173605
theorem B3134659 : Blo 1236436 3134659 := bstep (se 1 (by rfl) ⟨2350994, by rfl⟩ : syracuseStep 3134659 = 4701989) B4701989
theorem B1856723 : Blo 1236436 1856723 := bstep (se 1 (by rfl) ⟨1392542, by rfl⟩ : syracuseStep 1856723 = 2785085) B2785085
theorem B50771171 : Blo 1236436 50771171 := bstep (se 1 (by rfl) ⟨38078378, by rfl⟩ : syracuseStep 50771171 = 76156757) B76156757
theorem B2970865 : Blo 1236436 2970865 := bstep (se 2 (by rfl) ⟨1114074, by rfl⟩ : syracuseStep 2970865 = 2228149) B2228149
theorem B1856753 : Blo 1236436 1856753 := bstep (se 2 (by rfl) ⟨696282, by rfl⟩ : syracuseStep 1856753 = 1392565) B1392565
theorem B1586435 : Blo 1236436 1586435 := bstep (se 1 (by rfl) ⟨1189826, by rfl⟩ : syracuseStep 1586435 = 2379653) B2379653
theorem B2348291 : Blo 1236436 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B1856771 : Blo 1236436 1856771 := bstep (se 1 (by rfl) ⟨1392578, by rfl⟩ : syracuseStep 1856771 = 2785157) B2785157
theorem B4175117 : Blo 1236436 4175117 := bstep (se 3 (by rfl) ⟨782834, by rfl⟩ : syracuseStep 4175117 = 1565669) B1565669
theorem B1856801 : Blo 1236436 1856801 := bstep (se 2 (by rfl) ⟨696300, by rfl⟩ : syracuseStep 1856801 = 1392601) B1392601
theorem B7623985 : Blo 1236436 7623985 := bstep (se 2 (by rfl) ⟨2858994, by rfl⟩ : syracuseStep 7623985 = 5717989) B5717989
theorem B1856819 : Blo 1236436 1856819 := bstep (se 1 (by rfl) ⟨1392614, by rfl⟩ : syracuseStep 1856819 = 2785229) B2785229
theorem B4175171 : Blo 1236436 4175171 := bstep (se 1 (by rfl) ⟨3131378, by rfl⟩ : syracuseStep 4175171 = 6262757) B6262757
theorem B9401669 : Blo 1236436 9401669 := bstep (se 4 (by rfl) ⟨881406, by rfl⟩ : syracuseStep 9401669 = 1762813) B1762813
theorem B1856849 : Blo 1236436 1856849 := bstep (se 2 (by rfl) ⟨696318, by rfl⟩ : syracuseStep 1856849 = 1392637) B1392637
theorem B1856867 : Blo 1236436 1856867 := bstep (se 1 (by rfl) ⟨1392650, by rfl⟩ : syracuseStep 1856867 = 2785301) B2785301
theorem B1856897 : Blo 1236436 1856897 := bstep (se 2 (by rfl) ⟨696336, by rfl⟩ : syracuseStep 1856897 = 1392673) B1392673
theorem B1856915 : Blo 1236436 1856915 := bstep (se 1 (by rfl) ⟨1392686, by rfl⟩ : syracuseStep 1856915 = 2785373) B2785373
theorem B1856945 : Blo 1236436 1856945 := bstep (se 2 (by rfl) ⟨696354, by rfl⟩ : syracuseStep 1856945 = 1392709) B1392709
theorem B1856963 : Blo 1236436 1856963 := bstep (se 1 (by rfl) ⟨1392722, by rfl⟩ : syracuseStep 1856963 = 2785445) B2785445
theorem B2782673 : Blo 1236436 2782673 := bstep (se 2 (by rfl) ⟨1043502, by rfl⟩ : syracuseStep 2782673 = 2087005) B2087005
theorem B3962321 : Blo 1236436 3962321 := bstep (se 2 (by rfl) ⟨1485870, by rfl⟩ : syracuseStep 3962321 = 2971741) B2971741
theorem B1856993 : Blo 1236436 1856993 := bstep (se 2 (by rfl) ⟨696372, by rfl⟩ : syracuseStep 1856993 = 1392745) B1392745
theorem B2782691 : Blo 1236436 2782691 := bstep (se 1 (by rfl) ⟨2087018, by rfl⟩ : syracuseStep 2782691 = 4174037) B4174037
theorem B1857011 : Blo 1236436 1857011 := bstep (se 1 (by rfl) ⟨1392758, by rfl⟩ : syracuseStep 1857011 = 2785517) B2785517
theorem B10573325 : Blo 1236436 10573325 := bstep (se 3 (by rfl) ⟨1982498, by rfl⟩ : syracuseStep 10573325 = 3964997) B3964997
theorem B1857041 : Blo 1236436 1857041 := bstep (se 2 (by rfl) ⟨696390, by rfl⟩ : syracuseStep 1857041 = 1392781) B1392781
theorem B1857059 : Blo 1236436 1857059 := bstep (se 1 (by rfl) ⟨1392794, by rfl⟩ : syracuseStep 1857059 = 2785589) B2785589
theorem B1857089 : Blo 1236436 1857089 := bstep (se 2 (by rfl) ⟨696408, by rfl⟩ : syracuseStep 1857089 = 1392817) B1392817
theorem B4175441 : Blo 1236436 4175441 := bstep (se 2 (by rfl) ⟨1565790, by rfl⟩ : syracuseStep 4175441 = 3131581) B3131581
theorem B1857107 : Blo 1236436 1857107 := bstep (se 1 (by rfl) ⟨1392830, by rfl⟩ : syracuseStep 1857107 = 2785661) B2785661
theorem B2086499 : Blo 1236436 2086499 := bstep (se 1 (by rfl) ⟨1564874, by rfl⟩ : syracuseStep 2086499 = 3129749) B3129749
theorem B1857137 : Blo 1236436 1857137 := bstep (se 2 (by rfl) ⟨696426, by rfl⟩ : syracuseStep 1857137 = 1392853) B1392853
theorem B1857155 : Blo 1236436 1857155 := bstep (se 1 (by rfl) ⟨1392866, by rfl⟩ : syracuseStep 1857155 = 2785733) B2785733
theorem B10565261 : Blo 1236436 10565261 := bstep (se 3 (by rfl) ⟨1980986, by rfl⟩ : syracuseStep 10565261 = 3961973) B3961973
theorem B1857185 : Blo 1236436 1857185 := bstep (se 2 (by rfl) ⟨696444, by rfl⟩ : syracuseStep 1857185 = 1392889) B1392889
theorem B1857203 : Blo 1236436 1857203 := bstep (se 1 (by rfl) ⟨1392902, by rfl⟩ : syracuseStep 1857203 = 2785805) B2785805
theorem B1857233 : Blo 1236436 1857233 := bstep (se 2 (by rfl) ⟨696462, by rfl⟩ : syracuseStep 1857233 = 1392925) B1392925
theorem B2086627 : Blo 1236436 2086627 := bstep (se 1 (by rfl) ⟨1564970, by rfl⟩ : syracuseStep 2086627 = 3129941) B3129941
theorem B1857251 : Blo 1236436 1857251 := bstep (se 1 (by rfl) ⟨1392938, by rfl⟩ : syracuseStep 1857251 = 2785877) B2785877
theorem B2782961 : Blo 1236436 2782961 := bstep (se 2 (by rfl) ⟨1043610, by rfl⟩ : syracuseStep 2782961 = 2087221) B2087221
theorem B1857281 : Blo 1236436 1857281 := bstep (se 2 (by rfl) ⟨696480, by rfl⟩ : syracuseStep 1857281 = 1392961) B1392961
theorem B2782979 : Blo 1236436 2782979 := bstep (se 1 (by rfl) ⟨2087234, by rfl⟩ : syracuseStep 2782979 = 4174469) B4174469
theorem B1857299 : Blo 1236436 1857299 := bstep (se 1 (by rfl) ⟨1392974, by rfl⟩ : syracuseStep 1857299 = 2785949) B2785949
theorem B1857329 : Blo 1236436 1857329 := bstep (se 2 (by rfl) ⟨696498, by rfl⟩ : syracuseStep 1857329 = 1392997) B1392997
theorem B1857347 : Blo 1236436 1857347 := bstep (se 1 (by rfl) ⟨1393010, by rfl⟩ : syracuseStep 1857347 = 2786021) B2786021
theorem B1857377 : Blo 1236436 1857377 := bstep (se 2 (by rfl) ⟨696516, by rfl⟩ : syracuseStep 1857377 = 1393033) B1393033
theorem B2086769 : Blo 1236436 2086769 := bstep (se 2 (by rfl) ⟨782538, by rfl⟩ : syracuseStep 2086769 = 1565077) B1565077
theorem B1857395 : Blo 1236436 1857395 := bstep (se 1 (by rfl) ⟨1393046, by rfl⟩ : syracuseStep 1857395 = 2786093) B2786093
theorem B4700045 : Blo 1236436 4700045 := bstep (se 3 (by rfl) ⟨881258, by rfl⟩ : syracuseStep 4700045 = 1762517) B1762517
theorem B1857425 : Blo 1236436 1857425 := bstep (se 2 (by rfl) ⟨696534, by rfl⟩ : syracuseStep 1857425 = 1393069) B1393069
theorem B1857443 : Blo 1236436 1857443 := bstep (se 1 (by rfl) ⟨1393082, by rfl⟩ : syracuseStep 1857443 = 2786165) B2786165
theorem B1857473 : Blo 1236436 1857473 := bstep (se 2 (by rfl) ⟨696552, by rfl⟩ : syracuseStep 1857473 = 1393105) B1393105
theorem B1857491 : Blo 1236436 1857491 := bstep (se 1 (by rfl) ⟨1393118, by rfl⟩ : syracuseStep 1857491 = 2786237) B2786237
theorem B2086897 : Blo 1236436 2086897 := bstep (se 2 (by rfl) ⟨782586, by rfl⟩ : syracuseStep 2086897 = 1565173) B1565173
theorem B7927793 : Blo 1236436 7927793 := bstep (se 2 (by rfl) ⟨2972922, by rfl⟩ : syracuseStep 7927793 = 5945845) B5945845
theorem B1857521 : Blo 1236436 1857521 := bstep (se 2 (by rfl) ⟨696570, by rfl⟩ : syracuseStep 1857521 = 1393141) B1393141
theorem B1857539 : Blo 1236436 1857539 := bstep (se 1 (by rfl) ⟨1393154, by rfl⟩ : syracuseStep 1857539 = 2786309) B2786309
theorem B2783249 : Blo 1236436 2783249 := bstep (se 2 (by rfl) ⟨1043718, by rfl⟩ : syracuseStep 2783249 = 2087437) B2087437
theorem B2086931 : Blo 1236436 2086931 := bstep (se 1 (by rfl) ⟨1565198, by rfl⟩ : syracuseStep 2086931 = 3130397) B3130397
theorem B1857569 : Blo 1236436 1857569 := bstep (se 2 (by rfl) ⟨696588, by rfl⟩ : syracuseStep 1857569 = 1393177) B1393177
theorem B2783267 : Blo 1236436 2783267 := bstep (se 1 (by rfl) ⟨2087450, by rfl⟩ : syracuseStep 2783267 = 4174901) B4174901
theorem B1857587 : Blo 1236436 1857587 := bstep (se 1 (by rfl) ⟨1393190, by rfl⟩ : syracuseStep 1857587 = 2786381) B2786381
theorem B3962947 : Blo 1236436 3962947 := bstep (se 1 (by rfl) ⟨2972210, by rfl⟩ : syracuseStep 3962947 = 5944421) B5944421
theorem B2644049 : Blo 1236436 2644049 := bstep (se 2 (by rfl) ⟨991518, by rfl⟩ : syracuseStep 2644049 = 1983037) B1983037
theorem B1857617 : Blo 1236436 1857617 := bstep (se 2 (by rfl) ⟨696606, by rfl⟩ : syracuseStep 1857617 = 1393213) B1393213
theorem B1857635 : Blo 1236436 1857635 := bstep (se 1 (by rfl) ⟨1393226, by rfl⟩ : syracuseStep 1857635 = 2786453) B2786453
theorem B4175981 : Blo 1236436 4175981 := bstep (se 3 (by rfl) ⟨782996, by rfl⟩ : syracuseStep 4175981 = 1565993) B1565993
theorem B13375601 : Blo 1236436 13375601 := bstep (se 2 (by rfl) ⟨5015850, by rfl⟩ : syracuseStep 13375601 = 10031701) B10031701
theorem B2087059 : Blo 1236436 2087059 := bstep (se 1 (by rfl) ⟨1565294, by rfl⟩ : syracuseStep 2087059 = 3130589) B3130589
theorem B4176035 : Blo 1236436 4176035 := bstep (se 1 (by rfl) ⟨3132026, by rfl⟩ : syracuseStep 4176035 = 6264053) B6264053
theorem B2349233 : Blo 1236436 2349233 := bstep (se 2 (by rfl) ⟨880962, by rfl⟩ : syracuseStep 2349233 = 1761925) B1761925
theorem B3619025 : Blo 1236436 3619025 := bstep (se 2 (by rfl) ⟨1357134, by rfl⟩ : syracuseStep 3619025 = 2714269) B2714269
theorem B2087201 : Blo 1236436 2087201 := bstep (se 2 (by rfl) ⟨782700, by rfl⟩ : syracuseStep 2087201 = 1565401) B1565401
theorem B2783537 : Blo 1236436 2783537 := bstep (se 2 (by rfl) ⟨1043826, by rfl⟩ : syracuseStep 2783537 = 2087653) B2087653
theorem B2783555 : Blo 1236436 2783555 := bstep (se 1 (by rfl) ⟨2087666, by rfl⟩ : syracuseStep 2783555 = 4175333) B4175333
theorem B13375813 : Blo 1236436 13375813 := bstep (se 4 (by rfl) ⟨1253982, by rfl⟩ : syracuseStep 13375813 = 2507965) B2507965
theorem B1980769 : Blo 1236436 1980769 := bstep (se 2 (by rfl) ⟨742788, by rfl⟩ : syracuseStep 1980769 = 1485577) B1485577
theorem B6265187 : Blo 1236436 6265187 := bstep (se 1 (by rfl) ⟨4698890, by rfl⟩ : syracuseStep 6265187 = 9397781) B9397781
theorem B8468869 : Blo 1236436 8468869 := bstep (se 4 (by rfl) ⟨793956, by rfl⟩ : syracuseStep 8468869 = 1587913) B1587913
theorem B2087329 : Blo 1236436 2087329 := bstep (se 2 (by rfl) ⟨782748, by rfl⟩ : syracuseStep 2087329 = 1565497) B1565497
theorem B4176305 : Blo 1236436 4176305 := bstep (se 2 (by rfl) ⟨1566114, by rfl⟩ : syracuseStep 4176305 = 3132229) B3132229
theorem B2087363 : Blo 1236436 2087363 := bstep (se 1 (by rfl) ⟨1565522, by rfl⟩ : syracuseStep 2087363 = 3131045) B3131045
theorem B4463075 : Blo 1236436 4463075 := bstep (se 1 (by rfl) ⟨3347306, by rfl⟩ : syracuseStep 4463075 = 6694613) B6694613
theorem B1391107 : Blo 1236436 1391107 := bstep (se 1 (by rfl) ⟨1043330, by rfl⟩ : syracuseStep 1391107 = 2086661) B2086661
theorem B11450893 : Blo 1236436 11450893 := bstep (se 3 (by rfl) ⟨2147042, by rfl⟩ : syracuseStep 11450893 = 4294085) B4294085
theorem B2087491 : Blo 1236436 2087491 := bstep (se 1 (by rfl) ⟨1565618, by rfl⟩ : syracuseStep 2087491 = 3131237) B3131237
theorem B2783825 : Blo 1236436 2783825 := bstep (se 2 (by rfl) ⟨1043934, by rfl⟩ : syracuseStep 2783825 = 2087869) B2087869
theorem B2783843 : Blo 1236436 2783843 := bstep (se 1 (by rfl) ⟨2087882, by rfl⟩ : syracuseStep 2783843 = 4175765) B4175765
theorem B2644579 : Blo 1236436 2644579 := bstep (se 1 (by rfl) ⟨1983434, by rfl⟩ : syracuseStep 2644579 = 3966869) B3966869
theorem B4291213 : Blo 1236436 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B1391251 : Blo 1236436 1391251 := bstep (se 1 (by rfl) ⟨1043438, by rfl⟩ : syracuseStep 1391251 = 2086877) B2086877
theorem B15866549 : Blo 1236436 15866549 := bstep (se 5 (by rfl) ⟨743744, by rfl⟩ : syracuseStep 15866549 = 1487489) B1487489
theorem B7051981 : Blo 1236436 7051981 := bstep (se 3 (by rfl) ⟨1322246, by rfl⟩ : syracuseStep 7051981 = 2644493) B2644493
theorem B2087633 : Blo 1236436 2087633 := bstep (se 2 (by rfl) ⟨782862, by rfl⟩ : syracuseStep 2087633 = 1565725) B1565725
theorem B1981217 : Blo 1236436 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B1391395 : Blo 1236436 1391395 := bstep (se 1 (by rfl) ⟨1043546, by rfl⟩ : syracuseStep 1391395 = 2087093) B2087093
theorem B2087761 : Blo 1236436 2087761 := bstep (se 2 (by rfl) ⟨782910, by rfl⟩ : syracuseStep 2087761 = 1565821) B1565821
theorem B3521389 : Blo 1236436 3521389 := bstep (se 3 (by rfl) ⟨660260, by rfl⟩ : syracuseStep 3521389 = 1320521) B1320521
theorem B2784113 : Blo 1236436 2784113 := bstep (se 2 (by rfl) ⟨1044042, by rfl⟩ : syracuseStep 2784113 = 2088085) B2088085
theorem B2087795 : Blo 1236436 2087795 := bstep (se 1 (by rfl) ⟨1565846, by rfl⟩ : syracuseStep 2087795 = 3131693) B3131693
theorem B2784131 : Blo 1236436 2784131 := bstep (se 1 (by rfl) ⟨2088098, by rfl⟩ : syracuseStep 2784131 = 4176197) B4176197
theorem B1391539 : Blo 1236436 1391539 := bstep (se 1 (by rfl) ⟨1043654, by rfl⟩ : syracuseStep 1391539 = 2087309) B2087309
theorem B4176845 : Blo 1236436 4176845 := bstep (se 3 (by rfl) ⟨783158, by rfl⟩ : syracuseStep 4176845 = 1566317) B1566317
theorem B2087923 : Blo 1236436 2087923 := bstep (se 1 (by rfl) ⟨1565942, by rfl⟩ : syracuseStep 2087923 = 3131885) B3131885
theorem B4176899 : Blo 1236436 4176899 := bstep (se 1 (by rfl) ⟨3132674, by rfl⟩ : syracuseStep 4176899 = 6265349) B6265349
theorem B2382851 : Blo 1236436 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B3521549 : Blo 1236436 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B1588243 : Blo 1236436 1588243 := bstep (se 1 (by rfl) ⟨1191182, by rfl⟩ : syracuseStep 1588243 = 2382365) B2382365
theorem B7928867 : Blo 1236436 7928867 := bstep (se 1 (by rfl) ⟨5946650, by rfl⟩ : syracuseStep 7928867 = 11893301) B11893301
theorem B2350129 : Blo 1236436 2350129 := bstep (se 2 (by rfl) ⟨881298, by rfl⟩ : syracuseStep 2350129 = 1762597) B1762597
theorem B1391683 : Blo 1236436 1391683 := bstep (se 1 (by rfl) ⟨1043762, by rfl⟩ : syracuseStep 1391683 = 2087525) B2087525
theorem B2088065 : Blo 1236436 2088065 := bstep (se 2 (by rfl) ⟨783024, by rfl⟩ : syracuseStep 2088065 = 1566049) B1566049
theorem B6265997 : Blo 1236436 6265997 := bstep (se 3 (by rfl) ⟨1174874, by rfl⟩ : syracuseStep 6265997 = 2349749) B2349749
theorem B2784401 : Blo 1236436 2784401 := bstep (se 2 (by rfl) ⟨1044150, by rfl⟩ : syracuseStep 2784401 = 2088301) B2088301
theorem B2784419 : Blo 1236436 2784419 := bstep (se 1 (by rfl) ⟨2088314, by rfl⟩ : syracuseStep 2784419 = 4176629) B4176629
theorem B3521731 : Blo 1236436 3521731 := bstep (se 1 (by rfl) ⟨2641298, by rfl⟩ : syracuseStep 3521731 = 5282597) B5282597
theorem B2350289 : Blo 1236436 2350289 := bstep (se 2 (by rfl) ⟨881358, by rfl⟩ : syracuseStep 2350289 = 1762717) B1762717
theorem B1391827 : Blo 1236436 1391827 := bstep (se 1 (by rfl) ⟨1043870, by rfl⟩ : syracuseStep 1391827 = 2087741) B2087741
theorem B2088193 : Blo 1236436 2088193 := bstep (se 2 (by rfl) ⟨783072, by rfl⟩ : syracuseStep 2088193 = 1566145) B1566145
theorem B3570961 : Blo 1236436 3570961 := bstep (se 2 (by rfl) ⟨1339110, by rfl⟩ : syracuseStep 3570961 = 2678221) B2678221
theorem B3964177 : Blo 1236436 3964177 := bstep (se 2 (by rfl) ⟨1486566, by rfl⟩ : syracuseStep 3964177 = 2973133) B2973133
theorem B4177169 : Blo 1236436 4177169 := bstep (se 2 (by rfl) ⟨1566438, by rfl⟩ : syracuseStep 4177169 = 3132877) B3132877
theorem B2088227 : Blo 1236436 2088227 := bstep (se 1 (by rfl) ⟨1566170, by rfl⟩ : syracuseStep 2088227 = 3132341) B3132341
theorem B1391971 : Blo 1236436 1391971 := bstep (se 1 (by rfl) ⟨1043978, by rfl⟩ : syracuseStep 1391971 = 2087957) B2087957
theorem B2088355 : Blo 1236436 2088355 := bstep (se 1 (by rfl) ⟨1566266, by rfl⟩ : syracuseStep 2088355 = 3132533) B3132533
theorem B2784689 : Blo 1236436 2784689 := bstep (se 2 (by rfl) ⟨1044258, by rfl⟩ : syracuseStep 2784689 = 2088517) B2088517
theorem B2784707 : Blo 1236436 2784707 := bstep (se 1 (by rfl) ⟨2088530, by rfl⟩ : syracuseStep 2784707 = 4177061) B4177061
theorem B57187781 : Blo 1236436 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B1236451 : Blo 1236436 1236451 := bstep (se 1 (by rfl) ⟨927338, by rfl⟩ : syracuseStep 1236451 = 1854677) B1854677
theorem B1236467 : Blo 1236436 1236467 := bstep (se 1 (by rfl) ⟨927350, by rfl⟩ : syracuseStep 1236467 = 1854701) B1854701
theorem B1392115 : Blo 1236436 1392115 := bstep (se 1 (by rfl) ⟨1044086, by rfl⟩ : syracuseStep 1392115 = 2088173) B2088173
theorem B1236483 : Blo 1236436 1236483 := bstep (se 1 (by rfl) ⟨927362, by rfl⟩ : syracuseStep 1236483 = 1854725) B1854725
theorem B1236499 : Blo 1236436 1236499 := bstep (se 1 (by rfl) ⟨927374, by rfl⟩ : syracuseStep 1236499 = 1854749) B1854749
theorem B1236515 : Blo 1236436 1236515 := bstep (se 1 (by rfl) ⟨927386, by rfl⟩ : syracuseStep 1236515 = 1854773) B1854773
theorem B2088497 : Blo 1236436 2088497 := bstep (se 2 (by rfl) ⟨783186, by rfl⟩ : syracuseStep 2088497 = 1566373) B1566373
theorem B1236531 : Blo 1236436 1236531 := bstep (se 1 (by rfl) ⟨927398, by rfl⟩ : syracuseStep 1236531 = 1854797) B1854797
theorem B1236547 : Blo 1236436 1236547 := bstep (se 1 (by rfl) ⟨927410, by rfl⟩ : syracuseStep 1236547 = 1854821) B1854821
theorem B1236563 : Blo 1236436 1236563 := bstep (se 1 (by rfl) ⟨927422, by rfl⟩ : syracuseStep 1236563 = 1854845) B1854845
theorem B1236579 : Blo 1236436 1236579 := bstep (se 1 (by rfl) ⟨927434, by rfl⟩ : syracuseStep 1236579 = 1854869) B1854869
theorem B3014243 : Blo 1236436 3014243 := bstep (se 1 (by rfl) ⟨2260682, by rfl⟩ : syracuseStep 3014243 = 4521365) B4521365
theorem B2350691 : Blo 1236436 2350691 := bstep (se 1 (by rfl) ⟨1763018, by rfl⟩ : syracuseStep 2350691 = 3526037) B3526037
theorem B1236595 : Blo 1236436 1236595 := bstep (se 1 (by rfl) ⟨927446, by rfl⟩ : syracuseStep 1236595 = 1854893) B1854893
theorem B1236611 : Blo 1236436 1236611 := bstep (se 1 (by rfl) ⟨927458, by rfl⟩ : syracuseStep 1236611 = 1854917) B1854917
theorem B1982083 : Blo 1236436 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B1392259 : Blo 1236436 1392259 := bstep (se 1 (by rfl) ⟨1044194, by rfl⟩ : syracuseStep 1392259 = 2088389) B2088389
theorem B1236627 : Blo 1236436 1236627 := bstep (se 1 (by rfl) ⟨927470, by rfl⟩ : syracuseStep 1236627 = 1854941) B1854941
theorem B1236643 : Blo 1236436 1236643 := bstep (se 1 (by rfl) ⟨927482, by rfl⟩ : syracuseStep 1236643 = 1854965) B1854965
theorem B1760945 : Blo 1236436 1760945 := bstep (se 2 (by rfl) ⟨660354, by rfl⟩ : syracuseStep 1760945 = 1320709) B1320709
theorem B2088625 : Blo 1236436 2088625 := bstep (se 2 (by rfl) ⟨783234, by rfl⟩ : syracuseStep 2088625 = 1566469) B1566469
theorem B1236659 : Blo 1236436 1236659 := bstep (se 1 (by rfl) ⟨927494, by rfl⟩ : syracuseStep 1236659 = 1854989) B1854989
theorem B1236675 : Blo 1236436 1236675 := bstep (se 1 (by rfl) ⟨927506, by rfl⟩ : syracuseStep 1236675 = 1855013) B1855013
theorem B2784977 : Blo 1236436 2784977 := bstep (se 2 (by rfl) ⟨1044366, by rfl⟩ : syracuseStep 2784977 = 2088733) B2088733
theorem B1236691 : Blo 1236436 1236691 := bstep (se 1 (by rfl) ⟨927518, by rfl⟩ : syracuseStep 1236691 = 1855037) B1855037
theorem B2088659 : Blo 1236436 2088659 := bstep (se 1 (by rfl) ⟨1566494, by rfl⟩ : syracuseStep 2088659 = 3132989) B3132989
theorem B1236707 : Blo 1236436 1236707 := bstep (se 1 (by rfl) ⟨927530, by rfl⟩ : syracuseStep 1236707 = 1855061) B1855061
theorem B2784995 : Blo 1236436 2784995 := bstep (se 1 (by rfl) ⟨2088746, by rfl⟩ : syracuseStep 2784995 = 4177493) B4177493
theorem B1236723 : Blo 1236436 1236723 := bstep (se 1 (by rfl) ⟨927542, by rfl⟩ : syracuseStep 1236723 = 1855085) B1855085
theorem B1236739 : Blo 1236436 1236739 := bstep (se 1 (by rfl) ⟨927554, by rfl⟩ : syracuseStep 1236739 = 1855109) B1855109
theorem B1236755 : Blo 1236436 1236755 := bstep (se 1 (by rfl) ⟨927566, by rfl⟩ : syracuseStep 1236755 = 1855133) B1855133
theorem B1392403 : Blo 1236436 1392403 := bstep (se 1 (by rfl) ⟨1044302, by rfl⟩ : syracuseStep 1392403 = 2088605) B2088605
theorem B1236771 : Blo 1236436 1236771 := bstep (se 1 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 1236771 = 1855157) B1855157
theorem B1761059 : Blo 1236436 1761059 := bstep (se 1 (by rfl) ⟨1320794, by rfl⟩ : syracuseStep 1761059 = 2641589) B2641589
theorem B4177709 : Blo 1236436 4177709 := bstep (se 3 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 4177709 = 1566641) B1566641
theorem B4456241 : Blo 1236436 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B1236787 : Blo 1236436 1236787 := bstep (se 1 (by rfl) ⟨927590, by rfl⟩ : syracuseStep 1236787 = 1855181) B1855181
theorem B1236803 : Blo 1236436 1236803 := bstep (se 1 (by rfl) ⟨927602, by rfl⟩ : syracuseStep 1236803 = 1855205) B1855205
theorem B5087053 : Blo 1236436 5087053 := bstep (se 3 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 5087053 = 1907645) B1907645
theorem B1236819 : Blo 1236436 1236819 := bstep (se 1 (by rfl) ⟨927614, by rfl⟩ : syracuseStep 1236819 = 1855229) B1855229
theorem B2088787 : Blo 1236436 2088787 := bstep (se 1 (by rfl) ⟨1566590, by rfl⟩ : syracuseStep 2088787 = 3133181) B3133181
theorem B1236835 : Blo 1236436 1236835 := bstep (se 1 (by rfl) ⟨927626, by rfl⟩ : syracuseStep 1236835 = 1855253) B1855253
theorem B4177763 : Blo 1236436 4177763 := bstep (se 1 (by rfl) ⟨3133322, by rfl⟩ : syracuseStep 4177763 = 6266645) B6266645
theorem B3964781 : Blo 1236436 3964781 := bstep (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) B1486793
theorem B1236851 : Blo 1236436 1236851 := bstep (se 1 (by rfl) ⟨927638, by rfl⟩ : syracuseStep 1236851 = 1855277) B1855277
theorem B1761139 : Blo 1236436 1761139 := bstep (se 1 (by rfl) ⟨1320854, by rfl⟩ : syracuseStep 1761139 = 2641709) B2641709
theorem B1236867 : Blo 1236436 1236867 := bstep (se 1 (by rfl) ⟨927650, by rfl⟩ : syracuseStep 1236867 = 1855301) B1855301
theorem B1236883 : Blo 1236436 1236883 := bstep (se 1 (by rfl) ⟨927662, by rfl⟩ : syracuseStep 1236883 = 1855325) B1855325
theorem B1236899 : Blo 1236436 1236899 := bstep (se 1 (by rfl) ⟨927674, by rfl⟩ : syracuseStep 1236899 = 1855349) B1855349
theorem B1392547 : Blo 1236436 1392547 := bstep (se 1 (by rfl) ⟨1044410, by rfl⟩ : syracuseStep 1392547 = 2088821) B2088821
theorem B1236915 : Blo 1236436 1236915 := bstep (se 1 (by rfl) ⟨927686, by rfl⟩ : syracuseStep 1236915 = 1855373) B1855373
theorem B1695667 : Blo 1236436 1695667 := bstep (se 1 (by rfl) ⟨1271750, by rfl⟩ : syracuseStep 1695667 = 2543501) B2543501
theorem B1236931 : Blo 1236436 1236931 := bstep (se 1 (by rfl) ⟨927698, by rfl⟩ : syracuseStep 1236931 = 1855397) B1855397
theorem B4235203 : Blo 1236436 4235203 := bstep (se 1 (by rfl) ⟨3176402, by rfl⟩ : syracuseStep 4235203 = 6352805) B6352805
theorem B4702157 : Blo 1236436 4702157 := bstep (se 3 (by rfl) ⟨881654, by rfl⟩ : syracuseStep 4702157 = 1763309) B1763309
theorem B1236947 : Blo 1236436 1236947 := bstep (se 1 (by rfl) ⟨927710, by rfl⟩ : syracuseStep 1236947 = 1855421) B1855421
theorem B2088929 : Blo 1236436 2088929 := bstep (se 2 (by rfl) ⟨783348, by rfl⟩ : syracuseStep 2088929 = 1566697) B1566697
theorem B1236963 : Blo 1236436 1236963 := bstep (se 1 (by rfl) ⟨927722, by rfl⟩ : syracuseStep 1236963 = 1855445) B1855445
theorem B2785265 : Blo 1236436 2785265 := bstep (se 2 (by rfl) ⟨1044474, by rfl⟩ : syracuseStep 2785265 = 2088949) B2088949
theorem B1236979 : Blo 1236436 1236979 := bstep (se 1 (by rfl) ⟨927734, by rfl⟩ : syracuseStep 1236979 = 1855469) B1855469
theorem B1237003 : Blo 1236436 1237003 := bstep (se 1 (by rfl) ⟨927752, by rfl⟩ : syracuseStep 1237003 = 1855505) B1855505
theorem B7520273 : Blo 1236436 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B4456471 : Blo 1236436 4456471 := bstep (se 1 (by rfl) ⟨3342353, by rfl⟩ : syracuseStep 4456471 = 6684707) B6684707
theorem B1253399 : Blo 1236436 1253399 := bstep (se 1 (by rfl) ⟨940049, by rfl⟩ : syracuseStep 1253399 = 1880099) B1880099
theorem B1237015 : Blo 1236436 1237015 := bstep (se 1 (by rfl) ⟨927761, by rfl⟩ : syracuseStep 1237015 = 1855523) B1855523
theorem B2088983 : Blo 1236436 2088983 := bstep (se 1 (by rfl) ⟨1566737, by rfl⟩ : syracuseStep 2088983 = 3133475) B3133475
theorem B1237035 : Blo 1236436 1237035 := bstep (se 1 (by rfl) ⟨927776, by rfl⟩ : syracuseStep 1237035 = 1855553) B1855553
theorem B1237047 : Blo 1236436 1237047 := bstep (se 1 (by rfl) ⟨927785, by rfl⟩ : syracuseStep 1237047 = 1855571) B1855571
theorem B1761355 : Blo 1236436 1761355 := bstep (se 1 (by rfl) ⟨1321016, by rfl⟩ : syracuseStep 1761355 = 2642033) B2642033
theorem B1237067 : Blo 1236436 1237067 := bstep (se 1 (by rfl) ⟨927800, by rfl⟩ : syracuseStep 1237067 = 1855601) B1855601
theorem B2785355 : Blo 1236436 2785355 := bstep (se 1 (by rfl) ⟨2089016, by rfl⟩ : syracuseStep 2785355 = 4178033) B4178033
theorem B1761367 : Blo 1236436 1761367 := bstep (se 1 (by rfl) ⟨1321025, by rfl⟩ : syracuseStep 1761367 = 2642051) B2642051
theorem B1237079 : Blo 1236436 1237079 := bstep (se 1 (by rfl) ⟨927809, by rfl⟩ : syracuseStep 1237079 = 1855619) B1855619
theorem B5283929 : Blo 1236436 5283929 := bstep (se 2 (by rfl) ⟨1981473, by rfl⟩ : syracuseStep 5283929 = 3962947) B3962947
theorem B1392727 : Blo 1236436 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B1237099 : Blo 1236436 1237099 := bstep (se 1 (by rfl) ⟨927824, by rfl⟩ : syracuseStep 1237099 = 1855649) B1855649
theorem B1237111 : Blo 1236436 1237111 := bstep (se 1 (by rfl) ⟨927833, by rfl⟩ : syracuseStep 1237111 = 1855667) B1855667
theorem B2785409 : Blo 1236436 2785409 := bstep (se 2 (by rfl) ⟨1044528, by rfl⟩ : syracuseStep 2785409 = 2089057) B2089057
theorem B1237131 : Blo 1236436 1237131 := bstep (se 1 (by rfl) ⟨927848, by rfl⟩ : syracuseStep 1237131 = 1855697) B1855697
theorem B1237143 : Blo 1236436 1237143 := bstep (se 1 (by rfl) ⟨927857, by rfl⟩ : syracuseStep 1237143 = 1855715) B1855715
theorem B2089111 : Blo 1236436 2089111 := bstep (se 1 (by rfl) ⟨1566833, by rfl⟩ : syracuseStep 2089111 = 3133667) B3133667
theorem B1237163 : Blo 1236436 1237163 := bstep (se 1 (by rfl) ⟨927872, by rfl⟩ : syracuseStep 1237163 = 1855745) B1855745
theorem B1237175 : Blo 1236436 1237175 := bstep (se 1 (by rfl) ⟨927881, by rfl⟩ : syracuseStep 1237175 = 1855763) B1855763
theorem B1237195 : Blo 1236436 1237195 := bstep (se 1 (by rfl) ⟨927896, by rfl⟩ : syracuseStep 1237195 = 1855793) B1855793
theorem B1237207 : Blo 1236436 1237207 := bstep (se 1 (by rfl) ⟨927905, by rfl⟩ : syracuseStep 1237207 = 1855811) B1855811
theorem B4178141 : Blo 1236436 4178141 := bstep (se 3 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 4178141 = 1566803) B1566803
theorem B1237227 : Blo 1236436 1237227 := bstep (se 1 (by rfl) ⟨927920, by rfl⟩ : syracuseStep 1237227 = 1855841) B1855841
theorem B1237239 : Blo 1236436 1237239 := bstep (se 1 (by rfl) ⟨927929, by rfl⟩ : syracuseStep 1237239 = 1855859) B1855859
theorem B1237259 : Blo 1236436 1237259 := bstep (se 1 (by rfl) ⟨927944, by rfl⟩ : syracuseStep 1237259 = 1855889) B1855889
theorem B1392907 : Blo 1236436 1392907 := bstep (se 1 (by rfl) ⟨1044680, by rfl⟩ : syracuseStep 1392907 = 2089361) B2089361
theorem B1237271 : Blo 1236436 1237271 := bstep (se 1 (by rfl) ⟨927953, by rfl⟩ : syracuseStep 1237271 = 1855907) B1855907
theorem B1253675 : Blo 1236436 1253675 := bstep (se 1 (by rfl) ⟨940256, by rfl⟩ : syracuseStep 1253675 = 1880513) B1880513
theorem B1237291 : Blo 1236436 1237291 := bstep (se 1 (by rfl) ⟨927968, by rfl⟩ : syracuseStep 1237291 = 1855937) B1855937
theorem B1237303 : Blo 1236436 1237303 := bstep (se 1 (by rfl) ⟨927977, by rfl⟩ : syracuseStep 1237303 = 1855955) B1855955
theorem B1237323 : Blo 1236436 1237323 := bstep (se 1 (by rfl) ⟨927992, by rfl⟩ : syracuseStep 1237323 = 1855985) B1855985
theorem B1237335 : Blo 1236436 1237335 := bstep (se 1 (by rfl) ⟨928001, by rfl⟩ : syracuseStep 1237335 = 1856003) B1856003
theorem B2785625 : Blo 1236436 2785625 := bstep (se 2 (by rfl) ⟨1044609, by rfl⟩ : syracuseStep 2785625 = 2089219) B2089219
theorem B1237355 : Blo 1236436 1237355 := bstep (se 1 (by rfl) ⟨928016, by rfl⟩ : syracuseStep 1237355 = 1856033) B1856033
theorem B1237367 : Blo 1236436 1237367 := bstep (se 1 (by rfl) ⟨928025, by rfl⟩ : syracuseStep 1237367 = 1856051) B1856051
theorem B1393015 : Blo 1236436 1393015 := bstep (se 1 (by rfl) ⟨1044761, by rfl⟩ : syracuseStep 1393015 = 2089523) B2089523
theorem B1237387 : Blo 1236436 1237387 := bstep (se 1 (by rfl) ⟨928040, by rfl⟩ : syracuseStep 1237387 = 1856081) B1856081
theorem B1237399 : Blo 1236436 1237399 := bstep (se 1 (by rfl) ⟨928049, by rfl⟩ : syracuseStep 1237399 = 1856099) B1856099
theorem B1237419 : Blo 1236436 1237419 := bstep (se 1 (by rfl) ⟨928064, by rfl⟩ : syracuseStep 1237419 = 1856129) B1856129
theorem B17834417 : Blo 1236436 17834417 := bstep (se 2 (by rfl) ⟨6687906, by rfl⟩ : syracuseStep 17834417 = 13375813) B13375813
theorem B3129779 : Blo 1236436 3129779 := bstep (se 1 (by rfl) ⟨2347334, by rfl⟩ : syracuseStep 3129779 = 4694669) B4694669
theorem B1237431 : Blo 1236436 1237431 := bstep (se 1 (by rfl) ⟨928073, by rfl⟩ : syracuseStep 1237431 = 1856147) B1856147
theorem B2785715 : Blo 1236436 2785715 := bstep (se 1 (by rfl) ⟨2089286, by rfl⟩ : syracuseStep 2785715 = 4178573) B4178573
theorem B1237451 : Blo 1236436 1237451 := bstep (se 1 (by rfl) ⟨928088, by rfl⟩ : syracuseStep 1237451 = 1856177) B1856177
theorem B1237463 : Blo 1236436 1237463 := bstep (se 1 (by rfl) ⟨928097, by rfl⟩ : syracuseStep 1237463 = 1856195) B1856195
theorem B2785751 : Blo 1236436 2785751 := bstep (se 1 (by rfl) ⟨2089313, by rfl⟩ : syracuseStep 2785751 = 4178627) B4178627
theorem B1237483 : Blo 1236436 1237483 := bstep (se 1 (by rfl) ⟨928112, by rfl⟩ : syracuseStep 1237483 = 1856225) B1856225
theorem B1237495 : Blo 1236436 1237495 := bstep (se 1 (by rfl) ⟨928121, by rfl⟩ : syracuseStep 1237495 = 1856243) B1856243
theorem B1237515 : Blo 1236436 1237515 := bstep (se 1 (by rfl) ⟨928136, by rfl⟩ : syracuseStep 1237515 = 1856273) B1856273
theorem B7045649 : Blo 1236436 7045649 := bstep (se 2 (by rfl) ⟨2642118, by rfl⟩ : syracuseStep 7045649 = 5284237) B5284237
theorem B1237527 : Blo 1236436 1237527 := bstep (se 1 (by rfl) ⟨928145, by rfl⟩ : syracuseStep 1237527 = 1856291) B1856291
theorem B1237547 : Blo 1236436 1237547 := bstep (se 1 (by rfl) ⟨928160, by rfl⟩ : syracuseStep 1237547 = 1856321) B1856321
theorem B1393195 : Blo 1236436 1393195 := bstep (se 1 (by rfl) ⟨1044896, by rfl⟩ : syracuseStep 1393195 = 2089793) B2089793
theorem B1237559 : Blo 1236436 1237559 := bstep (se 1 (by rfl) ⟨928169, by rfl⟩ : syracuseStep 1237559 = 1856339) B1856339
theorem B1237579 : Blo 1236436 1237579 := bstep (se 1 (by rfl) ⟨928184, by rfl⟩ : syracuseStep 1237579 = 1856369) B1856369
theorem B1237591 : Blo 1236436 1237591 := bstep (se 1 (by rfl) ⟨928193, by rfl⟩ : syracuseStep 1237591 = 1856387) B1856387
theorem B135389789 : Blo 1236436 135389789 := bstep (se 3 (by rfl) ⟨25385585, by rfl⟩ : syracuseStep 135389789 = 50771171) B50771171
theorem B1237611 : Blo 1236436 1237611 := bstep (se 1 (by rfl) ⟨928208, by rfl⟩ : syracuseStep 1237611 = 1856417) B1856417
theorem B1237623 : Blo 1236436 1237623 := bstep (se 1 (by rfl) ⟨928217, by rfl⟩ : syracuseStep 1237623 = 1856435) B1856435
theorem B1237643 : Blo 1236436 1237643 := bstep (se 1 (by rfl) ⟨928232, by rfl⟩ : syracuseStep 1237643 = 1856465) B1856465
theorem B2785931 : Blo 1236436 2785931 := bstep (se 1 (by rfl) ⟨2089448, by rfl⟩ : syracuseStep 2785931 = 4178897) B4178897
theorem B1565335 : Blo 1236436 1565335 := bstep (se 1 (by rfl) ⟨1174001, by rfl⟩ : syracuseStep 1565335 = 2348003) B2348003
theorem B1237655 : Blo 1236436 1237655 := bstep (se 1 (by rfl) ⟨928241, by rfl⟩ : syracuseStep 1237655 = 1856483) B1856483
theorem B1237675 : Blo 1236436 1237675 := bstep (se 1 (by rfl) ⟨928256, by rfl⟩ : syracuseStep 1237675 = 1856513) B1856513
theorem B1237687 : Blo 1236436 1237687 := bstep (se 1 (by rfl) ⟨928265, by rfl⟩ : syracuseStep 1237687 = 1856531) B1856531
theorem B2785985 : Blo 1236436 2785985 := bstep (se 2 (by rfl) ⟨1044744, by rfl⟩ : syracuseStep 2785985 = 2089489) B2089489
theorem B1237707 : Blo 1236436 1237707 := bstep (se 1 (by rfl) ⟨928280, by rfl⟩ : syracuseStep 1237707 = 1856561) B1856561
theorem B1983179 : Blo 1236436 1983179 := bstep (se 1 (by rfl) ⟨1487384, by rfl⟩ : syracuseStep 1983179 = 2974769) B2974769
theorem B1237719 : Blo 1236436 1237719 := bstep (se 1 (by rfl) ⟨928289, by rfl⟩ : syracuseStep 1237719 = 1856579) B1856579
theorem B3130073 : Blo 1236436 3130073 := bstep (se 2 (by rfl) ⟨1173777, by rfl⟩ : syracuseStep 3130073 = 2347555) B2347555
theorem B1237739 : Blo 1236436 1237739 := bstep (se 1 (by rfl) ⟨928304, by rfl⟩ : syracuseStep 1237739 = 1856609) B1856609
theorem B1237751 : Blo 1236436 1237751 := bstep (se 1 (by rfl) ⟨928313, by rfl⟩ : syracuseStep 1237751 = 1856627) B1856627
theorem B17842949 : Blo 1236436 17842949 := bstep (se 4 (by rfl) ⟨1672776, by rfl⟩ : syracuseStep 17842949 = 3345553) B3345553
theorem B1237771 : Blo 1236436 1237771 := bstep (se 1 (by rfl) ⟨928328, by rfl⟩ : syracuseStep 1237771 = 1856657) B1856657
theorem B2089739 : Blo 1236436 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B1237783 : Blo 1236436 1237783 := bstep (se 1 (by rfl) ⟨928337, by rfl⟩ : syracuseStep 1237783 = 1856675) B1856675
theorem B1237803 : Blo 1236436 1237803 := bstep (se 1 (by rfl) ⟨928352, by rfl⟩ : syracuseStep 1237803 = 1856705) B1856705
theorem B4457267 : Blo 1236436 4457267 := bstep (se 1 (by rfl) ⟨3342950, by rfl⟩ : syracuseStep 4457267 = 6685901) B6685901
theorem B1237815 : Blo 1236436 1237815 := bstep (se 1 (by rfl) ⟨928361, by rfl⟩ : syracuseStep 1237815 = 1856723) B1856723
theorem B1237835 : Blo 1236436 1237835 := bstep (se 1 (by rfl) ⟨928376, by rfl⟩ : syracuseStep 1237835 = 1856753) B1856753
theorem B1237847 : Blo 1236436 1237847 := bstep (se 1 (by rfl) ⟨928385, by rfl⟩ : syracuseStep 1237847 = 1856771) B1856771
theorem B1237867 : Blo 1236436 1237867 := bstep (se 1 (by rfl) ⟨928400, by rfl⟩ : syracuseStep 1237867 = 1856801) B1856801
theorem B1237879 : Blo 1236436 1237879 := bstep (se 1 (by rfl) ⟨928409, by rfl⟩ : syracuseStep 1237879 = 1856819) B1856819
theorem B6685571 : Blo 1236436 6685571 := bstep (se 1 (by rfl) ⟨5014178, by rfl⟩ : syracuseStep 6685571 = 10028357) B10028357
theorem B6267779 : Blo 1236436 6267779 := bstep (se 1 (by rfl) ⟨4700834, by rfl⟩ : syracuseStep 6267779 = 9401669) B9401669
theorem B1237899 : Blo 1236436 1237899 := bstep (se 1 (by rfl) ⟨928424, by rfl⟩ : syracuseStep 1237899 = 1856849) B1856849
theorem B1237911 : Blo 1236436 1237911 := bstep (se 1 (by rfl) ⟨928433, by rfl⟩ : syracuseStep 1237911 = 1856867) B1856867
theorem B2786201 : Blo 1236436 2786201 := bstep (se 2 (by rfl) ⟨1044825, by rfl⟩ : syracuseStep 2786201 = 2089651) B2089651
theorem B1237931 : Blo 1236436 1237931 := bstep (se 1 (by rfl) ⟨928448, by rfl⟩ : syracuseStep 1237931 = 1856897) B1856897
theorem B1237943 : Blo 1236436 1237943 := bstep (se 1 (by rfl) ⟨928457, by rfl⟩ : syracuseStep 1237943 = 1856915) B1856915
theorem B1237963 : Blo 1236436 1237963 := bstep (se 1 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 1237963 = 1856945) B1856945
theorem B1237975 : Blo 1236436 1237975 := bstep (se 1 (by rfl) ⟨928481, by rfl⟩ : syracuseStep 1237975 = 1856963) B1856963
theorem B9528281 : Blo 1236436 9528281 := bstep (se 2 (by rfl) ⟨3573105, by rfl⟩ : syracuseStep 9528281 = 7146211) B7146211
theorem B1237995 : Blo 1236436 1237995 := bstep (se 1 (by rfl) ⟨928496, by rfl⟩ : syracuseStep 1237995 = 1856993) B1856993
theorem B2786291 : Blo 1236436 2786291 := bstep (se 1 (by rfl) ⟨2089718, by rfl⟩ : syracuseStep 2786291 = 4179437) B4179437
theorem B1238007 : Blo 1236436 1238007 := bstep (se 1 (by rfl) ⟨928505, by rfl⟩ : syracuseStep 1238007 = 1857011) B1857011
theorem B1238027 : Blo 1236436 1238027 := bstep (se 1 (by rfl) ⟨928520, by rfl⟩ : syracuseStep 1238027 = 1857041) B1857041
theorem B1238039 : Blo 1236436 1238039 := bstep (se 1 (by rfl) ⟨928529, by rfl⟩ : syracuseStep 1238039 = 1857059) B1857059
theorem B2786327 : Blo 1236436 2786327 := bstep (se 1 (by rfl) ⟨2089745, by rfl⟩ : syracuseStep 2786327 = 4179491) B4179491
theorem B1238059 : Blo 1236436 1238059 := bstep (se 1 (by rfl) ⟨928544, by rfl⟩ : syracuseStep 1238059 = 1857089) B1857089
theorem B1238071 : Blo 1236436 1238071 := bstep (se 1 (by rfl) ⟨928553, by rfl⟩ : syracuseStep 1238071 = 1857107) B1857107
theorem B9045067 : Blo 1236436 9045067 := bstep (se 1 (by rfl) ⟨6783800, by rfl⟩ : syracuseStep 9045067 = 13567601) B13567601
theorem B1238091 : Blo 1236436 1238091 := bstep (se 1 (by rfl) ⟨928568, by rfl⟩ : syracuseStep 1238091 = 1857137) B1857137
theorem B1238103 : Blo 1236436 1238103 := bstep (se 1 (by rfl) ⟨928577, by rfl⟩ : syracuseStep 1238103 = 1857155) B1857155
theorem B1983575 : Blo 1236436 1983575 := bstep (se 1 (by rfl) ⟨1487681, by rfl⟩ : syracuseStep 1983575 = 2975363) B2975363
theorem B1238123 : Blo 1236436 1238123 := bstep (se 1 (by rfl) ⟨928592, by rfl⟩ : syracuseStep 1238123 = 1857185) B1857185
theorem B1238135 : Blo 1236436 1238135 := bstep (se 1 (by rfl) ⟨928601, by rfl⟩ : syracuseStep 1238135 = 1857203) B1857203
theorem B1238155 : Blo 1236436 1238155 := bstep (se 1 (by rfl) ⟨928616, by rfl⟩ : syracuseStep 1238155 = 1857233) B1857233
theorem B4695185 : Blo 1236436 4695185 := bstep (se 2 (by rfl) ⟨1760694, by rfl⟩ : syracuseStep 4695185 = 3521389) B3521389
theorem B1238167 : Blo 1236436 1238167 := bstep (se 1 (by rfl) ⟨928625, by rfl⟩ : syracuseStep 1238167 = 1857251) B1857251
theorem B1238187 : Blo 1236436 1238187 := bstep (se 1 (by rfl) ⟨928640, by rfl⟩ : syracuseStep 1238187 = 1857281) B1857281
theorem B1238199 : Blo 1236436 1238199 := bstep (se 1 (by rfl) ⟨928649, by rfl⟩ : syracuseStep 1238199 = 1857299) B1857299
theorem B1238219 : Blo 1236436 1238219 := bstep (se 1 (by rfl) ⟨928664, by rfl⟩ : syracuseStep 1238219 = 1857329) B1857329
theorem B1238231 : Blo 1236436 1238231 := bstep (se 1 (by rfl) ⟨928673, by rfl⟩ : syracuseStep 1238231 = 1857347) B1857347
theorem B1238251 : Blo 1236436 1238251 := bstep (se 1 (by rfl) ⟨928688, by rfl⟩ : syracuseStep 1238251 = 1857377) B1857377
theorem B1238263 : Blo 1236436 1238263 := bstep (se 1 (by rfl) ⟨928697, by rfl⟩ : syracuseStep 1238263 = 1857395) B1857395
theorem B1238283 : Blo 1236436 1238283 := bstep (se 1 (by rfl) ⟨928712, by rfl⟩ : syracuseStep 1238283 = 1857425) B1857425
theorem B1238295 : Blo 1236436 1238295 := bstep (se 1 (by rfl) ⟨928721, by rfl⟩ : syracuseStep 1238295 = 1857443) B1857443
theorem B1238315 : Blo 1236436 1238315 := bstep (se 1 (by rfl) ⟨928736, by rfl⟩ : syracuseStep 1238315 = 1857473) B1857473
theorem B1238327 : Blo 1236436 1238327 := bstep (se 1 (by rfl) ⟨928745, by rfl⟩ : syracuseStep 1238327 = 1857491) B1857491
theorem B5285195 : Blo 1236436 5285195 := bstep (se 1 (by rfl) ⟨3963896, by rfl⟩ : syracuseStep 5285195 = 7927793) B7927793
theorem B4179275 : Blo 1236436 4179275 := bstep (se 1 (by rfl) ⟨3134456, by rfl⟩ : syracuseStep 4179275 = 6268913) B6268913
theorem B1238347 : Blo 1236436 1238347 := bstep (se 1 (by rfl) ⟨928760, by rfl⟩ : syracuseStep 1238347 = 1857521) B1857521
theorem B1238359 : Blo 1236436 1238359 := bstep (se 1 (by rfl) ⟨928769, by rfl⟩ : syracuseStep 1238359 = 1857539) B1857539
theorem B1238379 : Blo 1236436 1238379 := bstep (se 1 (by rfl) ⟨928784, by rfl⟩ : syracuseStep 1238379 = 1857569) B1857569
theorem B1238391 : Blo 1236436 1238391 := bstep (se 1 (by rfl) ⟨928793, by rfl⟩ : syracuseStep 1238391 = 1857587) B1857587
theorem B1238411 : Blo 1236436 1238411 := bstep (se 1 (by rfl) ⟨928808, by rfl⟩ : syracuseStep 1238411 = 1857617) B1857617
theorem B1238423 : Blo 1236436 1238423 := bstep (se 1 (by rfl) ⟨928817, by rfl⟩ : syracuseStep 1238423 = 1857635) B1857635
theorem B1566155 : Blo 1236436 1566155 := bstep (se 1 (by rfl) ⟨1174616, by rfl⟩ : syracuseStep 1566155 = 2349233) B2349233
theorem B10577425 : Blo 1236436 10577425 := bstep (se 2 (by rfl) ⟨3966534, by rfl⟩ : syracuseStep 10577425 = 7933069) B7933069
theorem B4695641 : Blo 1236436 4695641 := bstep (se 2 (by rfl) ⟨1760865, by rfl⟩ : syracuseStep 4695641 = 3521731) B3521731
theorem B4179545 : Blo 1236436 4179545 := bstep (se 2 (by rfl) ⟨1567329, by rfl⟩ : syracuseStep 4179545 = 3134659) B3134659
theorem B2975383 : Blo 1236436 2975383 := bstep (se 1 (by rfl) ⟨2231537, by rfl⟩ : syracuseStep 2975383 = 4463075) B4463075
theorem B4761281 : Blo 1236436 4761281 := bstep (se 2 (by rfl) ⟨1785480, by rfl⟩ : syracuseStep 4761281 = 3570961) B3570961
theorem B5285569 : Blo 1236436 5285569 := bstep (se 2 (by rfl) ⟨1982088, by rfl⟩ : syracuseStep 5285569 = 3964177) B3964177
theorem B3344075 : Blo 1236436 3344075 := bstep (se 1 (by rfl) ⟨2508056, by rfl⟩ : syracuseStep 3344075 = 5016113) B5016113
theorem B10577699 : Blo 1236436 10577699 := bstep (se 1 (by rfl) ⟨7933274, by rfl⟩ : syracuseStep 10577699 = 15866549) B15866549
theorem B1410859 : Blo 1236436 1410859 := bstep (se 1 (by rfl) ⟨1058144, by rfl⟩ : syracuseStep 1410859 = 2116289) B2116289
theorem B4695853 : Blo 1236436 4695853 := bstep (se 3 (by rfl) ⟨880472, by rfl⟩ : syracuseStep 4695853 = 1760945) B1760945
theorem B5285911 : Blo 1236436 5285911 := bstep (se 1 (by rfl) ⟨3964433, by rfl⟩ : syracuseStep 5285911 = 7928867) B7928867
theorem B4696157 : Blo 1236436 4696157 := bstep (se 3 (by rfl) ⟨880529, by rfl⟩ : syracuseStep 4696157 = 1761059) B1761059
theorem B1566859 : Blo 1236436 1566859 := bstep (se 1 (by rfl) ⟨1175144, by rfl⟩ : syracuseStep 1566859 = 2350289) B2350289
theorem B3131723 : Blo 1236436 3131723 := bstep (se 1 (by rfl) ⟨2348792, by rfl⟩ : syracuseStep 3131723 = 4697585) B4697585
theorem B2230615 : Blo 1236436 2230615 := bstep (se 1 (by rfl) ⟨1672961, by rfl⟩ : syracuseStep 2230615 = 3345923) B3345923
theorem B2009495 : Blo 1236436 2009495 := bstep (se 1 (by rfl) ⟨1507121, by rfl⟩ : syracuseStep 2009495 = 3014243) B3014243
theorem B1567127 : Blo 1236436 1567127 := bstep (se 1 (by rfl) ⟨1175345, by rfl⟩ : syracuseStep 1567127 = 2350691) B2350691
theorem B1411511 : Blo 1236436 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B3344861 : Blo 1236436 3344861 := bstep (se 3 (by rfl) ⟨627161, by rfl⟩ : syracuseStep 3344861 = 1254323) B1254323
theorem B3344971 : Blo 1236436 3344971 := bstep (se 1 (by rfl) ⟨2508728, by rfl⟩ : syracuseStep 3344971 = 5017457) B5017457
theorem B5646937 : Blo 1236436 5646937 := bstep (se 2 (by rfl) ⟨2117601, by rfl⟩ : syracuseStep 5646937 = 4235203) B4235203
theorem B10029719 : Blo 1236436 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B4459225 : Blo 1236436 4459225 := bstep (se 2 (by rfl) ⟨1672209, by rfl⟩ : syracuseStep 4459225 = 3344419) B3344419
theorem B2509555 : Blo 1236436 2509555 := bstep (se 1 (by rfl) ⟨1882166, by rfl⟩ : syracuseStep 2509555 = 3764333) B3764333
theorem B15854453 : Blo 1236436 15854453 := bstep (se 5 (by rfl) ⟨743177, by rfl⟩ : syracuseStep 15854453 = 1486355) B1486355
theorem B1321867 : Blo 1236436 1321867 := bstep (se 1 (by rfl) ⟨991400, by rfl⟩ : syracuseStep 1321867 = 1982801) B1982801
theorem B11439053 : Blo 1236436 11439053 := bstep (se 3 (by rfl) ⟨2144822, by rfl⟩ : syracuseStep 11439053 = 4289645) B4289645
theorem B50760665 : Blo 1236436 50760665 := bstep (se 2 (by rfl) ⟨19035249, by rfl⟩ : syracuseStep 50760665 = 38070499) B38070499
theorem B3525707 : Blo 1236436 3525707 := bstep (se 1 (by rfl) ⟨2644280, by rfl⟩ : syracuseStep 3525707 = 5288561) B5288561
theorem B2641025 : Blo 1236436 2641025 := bstep (se 2 (by rfl) ⟨990384, by rfl⟩ : syracuseStep 2641025 = 1980769) B1980769
theorem B11291825 : Blo 1236436 11291825 := bstep (se 2 (by rfl) ⟨4234434, by rfl⟩ : syracuseStep 11291825 = 8468869) B8468869
theorem B1854731 : Blo 1236436 1854731 := bstep (se 1 (by rfl) ⟨1391048, by rfl⟩ : syracuseStep 1854731 = 2782097) B2782097
theorem B1854743 : Blo 1236436 1854743 := bstep (se 1 (by rfl) ⟨1391057, by rfl⟩ : syracuseStep 1854743 = 2782115) B2782115
theorem B3132695 : Blo 1236436 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B1854809 : Blo 1236436 1854809 := bstep (se 2 (by rfl) ⟨695553, by rfl⟩ : syracuseStep 1854809 = 1391107) B1391107
theorem B6262109 : Blo 1236436 6262109 := bstep (se 3 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 6262109 = 2348291) B2348291
theorem B9039281 : Blo 1236436 9039281 := bstep (se 2 (by rfl) ⟨3389730, by rfl⟩ : syracuseStep 9039281 = 6779461) B6779461
theorem B4230593 : Blo 1236436 4230593 := bstep (se 2 (by rfl) ⟨1586472, by rfl⟩ : syracuseStep 4230593 = 3172945) B3172945
theorem B1854923 : Blo 1236436 1854923 := bstep (se 1 (by rfl) ⟨1391192, by rfl⟩ : syracuseStep 1854923 = 2782385) B2782385
theorem B1854935 : Blo 1236436 1854935 := bstep (se 1 (by rfl) ⟨1391201, by rfl⟩ : syracuseStep 1854935 = 2782403) B2782403
theorem B3526105 : Blo 1236436 3526105 := bstep (se 2 (by rfl) ⟨1322289, by rfl⟩ : syracuseStep 3526105 = 2644579) B2644579
theorem B5721617 : Blo 1236436 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B4173335 : Blo 1236436 4173335 := bstep (se 1 (by rfl) ⟨3130001, by rfl⟩ : syracuseStep 4173335 = 6260003) B6260003
theorem B1855001 : Blo 1236436 1855001 := bstep (se 2 (by rfl) ⟨695625, by rfl⟩ : syracuseStep 1855001 = 1391251) B1391251
theorem B1855115 : Blo 1236436 1855115 := bstep (se 1 (by rfl) ⟨1391336, by rfl⟩ : syracuseStep 1855115 = 2782673) B2782673
theorem B2641547 : Blo 1236436 2641547 := bstep (se 1 (by rfl) ⟨1981160, by rfl⟩ : syracuseStep 2641547 = 3962321) B3962321
theorem B1855127 : Blo 1236436 1855127 := bstep (se 1 (by rfl) ⟨1391345, by rfl⟩ : syracuseStep 1855127 = 2782691) B2782691
theorem B7048883 : Blo 1236436 7048883 := bstep (se 1 (by rfl) ⟨5286662, by rfl⟩ : syracuseStep 7048883 = 10573325) B10573325
theorem B1855193 : Blo 1236436 1855193 := bstep (se 2 (by rfl) ⟨695697, by rfl⟩ : syracuseStep 1855193 = 1391395) B1391395
theorem B1855307 : Blo 1236436 1855307 := bstep (se 1 (by rfl) ⟨1391480, by rfl⟩ : syracuseStep 1855307 = 2782961) B2782961
theorem B1855319 : Blo 1236436 1855319 := bstep (se 1 (by rfl) ⟨1391489, by rfl⟩ : syracuseStep 1855319 = 2782979) B2782979
theorem B1855385 : Blo 1236436 1855385 := bstep (se 2 (by rfl) ⟨695769, by rfl⟩ : syracuseStep 1855385 = 1391539) B1391539
theorem B3133363 : Blo 1236436 3133363 := bstep (se 1 (by rfl) ⟨2350022, by rfl⟩ : syracuseStep 3133363 = 4700045) B4700045
theorem B1855499 : Blo 1236436 1855499 := bstep (se 1 (by rfl) ⟨1391624, by rfl⟩ : syracuseStep 1855499 = 2783249) B2783249
theorem B1855511 : Blo 1236436 1855511 := bstep (se 1 (by rfl) ⟨1391633, by rfl⟩ : syracuseStep 1855511 = 2783267) B2783267
theorem B2117657 : Blo 1236436 2117657 := bstep (se 2 (by rfl) ⟨794121, by rfl⟩ : syracuseStep 2117657 = 1588243) B1588243
theorem B4173875 : Blo 1236436 4173875 := bstep (se 1 (by rfl) ⟨3130406, by rfl⟩ : syracuseStep 4173875 = 6260813) B6260813
theorem B3305537 : Blo 1236436 3305537 := bstep (se 2 (by rfl) ⟨1239576, by rfl⟩ : syracuseStep 3305537 = 2479153) B2479153
theorem B4460609 : Blo 1236436 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B3133505 : Blo 1236436 3133505 := bstep (se 2 (by rfl) ⟨1175064, by rfl⟩ : syracuseStep 3133505 = 2350129) B2350129
theorem B8917067 : Blo 1236436 8917067 := bstep (se 1 (by rfl) ⟨6687800, by rfl⟩ : syracuseStep 8917067 = 13375601) B13375601
theorem B1855577 : Blo 1236436 1855577 := bstep (se 2 (by rfl) ⟨695841, by rfl⟩ : syracuseStep 1855577 = 1391683) B1391683
theorem B2412683 : Blo 1236436 2412683 := bstep (se 1 (by rfl) ⟨1809512, by rfl⟩ : syracuseStep 2412683 = 3619025) B3619025
theorem B6025367 : Blo 1236436 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B1855691 : Blo 1236436 1855691 := bstep (se 1 (by rfl) ⟨1391768, by rfl⟩ : syracuseStep 1855691 = 2783537) B2783537
theorem B1855703 : Blo 1236436 1855703 := bstep (se 1 (by rfl) ⟨1391777, by rfl⟩ : syracuseStep 1855703 = 2783555) B2783555
theorem B6353113 : Blo 1236436 6353113 := bstep (se 2 (by rfl) ⟨2382417, by rfl⟩ : syracuseStep 6353113 = 4764835) B4764835
theorem B1855769 : Blo 1236436 1855769 := bstep (se 2 (by rfl) ⟨695913, by rfl⟩ : syracuseStep 1855769 = 1391827) B1391827
theorem B3961153 : Blo 1236436 3961153 := bstep (se 2 (by rfl) ⟨1485432, by rfl⟩ : syracuseStep 3961153 = 2970865) B2970865
theorem B4174145 : Blo 1236436 4174145 := bstep (se 2 (by rfl) ⟨1565304, by rfl⟩ : syracuseStep 4174145 = 3130609) B3130609
theorem B1855883 : Blo 1236436 1855883 := bstep (se 1 (by rfl) ⟨1391912, by rfl⟩ : syracuseStep 1855883 = 2783825) B2783825
theorem B1855895 : Blo 1236436 1855895 := bstep (se 1 (by rfl) ⟨1391921, by rfl⟩ : syracuseStep 1855895 = 2783843) B2783843
theorem B1855961 : Blo 1236436 1855961 := bstep (se 2 (by rfl) ⟨695985, by rfl⟩ : syracuseStep 1855961 = 1391971) B1391971
theorem B1856075 : Blo 1236436 1856075 := bstep (se 1 (by rfl) ⟨1392056, by rfl⟩ : syracuseStep 1856075 = 2784113) B2784113
theorem B1856087 : Blo 1236436 1856087 := bstep (se 1 (by rfl) ⟨1392065, by rfl⟩ : syracuseStep 1856087 = 2784131) B2784131
theorem B7934557 : Blo 1236436 7934557 := bstep (se 3 (by rfl) ⟨1487729, by rfl⟩ : syracuseStep 7934557 = 2975459) B2975459
theorem B4698755 : Blo 1236436 4698755 := bstep (se 1 (by rfl) ⟨3524066, by rfl⟩ : syracuseStep 4698755 = 7048133) B7048133
theorem B4698769 : Blo 1236436 4698769 := bstep (se 2 (by rfl) ⟨1762038, by rfl⟩ : syracuseStep 4698769 = 3524077) B3524077
theorem B5943959 : Blo 1236436 5943959 := bstep (se 1 (by rfl) ⟨4457969, by rfl⟩ : syracuseStep 5943959 = 8915939) B8915939
theorem B1856153 : Blo 1236436 1856153 := bstep (se 2 (by rfl) ⟨696057, by rfl⟩ : syracuseStep 1856153 = 1392115) B1392115
theorem B2347699 : Blo 1236436 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B1856267 : Blo 1236436 1856267 := bstep (se 1 (by rfl) ⟨1392200, by rfl⟩ : syracuseStep 1856267 = 2784401) B2784401
theorem B1856279 : Blo 1236436 1856279 := bstep (se 1 (by rfl) ⟨1392209, by rfl⟩ : syracuseStep 1856279 = 2784419) B2784419
theorem B2642777 : Blo 1236436 2642777 := bstep (se 2 (by rfl) ⟨991041, by rfl⟩ : syracuseStep 2642777 = 1982083) B1982083
theorem B1856345 : Blo 1236436 1856345 := bstep (se 2 (by rfl) ⟨696129, by rfl⟩ : syracuseStep 1856345 = 1392259) B1392259
theorem B4174685 : Blo 1236436 4174685 := bstep (se 3 (by rfl) ⟨782753, by rfl⟩ : syracuseStep 4174685 = 1565507) B1565507
theorem B4699073 : Blo 1236436 4699073 := bstep (se 2 (by rfl) ⟨1762152, by rfl⟩ : syracuseStep 4699073 = 3524305) B3524305
theorem B1856459 : Blo 1236436 1856459 := bstep (se 1 (by rfl) ⟨1392344, by rfl⟩ : syracuseStep 1856459 = 2784689) B2784689
theorem B1881047 : Blo 1236436 1881047 := bstep (se 1 (by rfl) ⟨1410785, by rfl⟩ : syracuseStep 1881047 = 2821571) B2821571
theorem B1856471 : Blo 1236436 1856471 := bstep (se 1 (by rfl) ⟨1392353, by rfl⟩ : syracuseStep 1856471 = 2784707) B2784707
theorem B2782169 : Blo 1236436 2782169 := bstep (se 2 (by rfl) ⟨1043313, by rfl⟩ : syracuseStep 2782169 = 2086627) B2086627
theorem B1856537 : Blo 1236436 1856537 := bstep (se 2 (by rfl) ⟨696201, by rfl⟩ : syracuseStep 1856537 = 1392403) B1392403
theorem B2782259 : Blo 1236436 2782259 := bstep (se 1 (by rfl) ⟨2086694, by rfl⟩ : syracuseStep 2782259 = 4173389) B4173389
theorem B2782295 : Blo 1236436 2782295 := bstep (se 1 (by rfl) ⟨2086721, by rfl⟩ : syracuseStep 2782295 = 4173443) B4173443
theorem B7050341 : Blo 1236436 7050341 := bstep (se 4 (by rfl) ⟨660969, by rfl⟩ : syracuseStep 7050341 = 1321939) B1321939
theorem B1856651 : Blo 1236436 1856651 := bstep (se 1 (by rfl) ⟨1392488, by rfl⟩ : syracuseStep 1856651 = 2784977) B2784977
theorem B1856663 : Blo 1236436 1856663 := bstep (se 1 (by rfl) ⟨1392497, by rfl⟩ : syracuseStep 1856663 = 2784995) B2784995
theorem B2348185 : Blo 1236436 2348185 := bstep (se 2 (by rfl) ⟨880569, by rfl⟩ : syracuseStep 2348185 = 1761139) B1761139
theorem B5944499 : Blo 1236436 5944499 := bstep (se 1 (by rfl) ⟨4458374, by rfl⟩ : syracuseStep 5944499 = 8916749) B8916749
theorem B4764851 : Blo 1236436 4764851 := bstep (se 1 (by rfl) ⟨3573638, by rfl⟩ : syracuseStep 4764851 = 7147277) B7147277
theorem B2970827 : Blo 1236436 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B8918221 : Blo 1236436 8918221 := bstep (se 3 (by rfl) ⟨1672166, by rfl⟩ : syracuseStep 8918221 = 3344333) B3344333
theorem B1856729 : Blo 1236436 1856729 := bstep (se 2 (by rfl) ⟨696273, by rfl⟩ : syracuseStep 1856729 = 1392547) B1392547
theorem B2643187 : Blo 1236436 2643187 := bstep (se 1 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 2643187 = 3964781) B3964781
theorem B2782475 : Blo 1236436 2782475 := bstep (se 1 (by rfl) ⟨2086856, by rfl⟩ : syracuseStep 2782475 = 4173713) B4173713
theorem B3134771 : Blo 1236436 3134771 := bstep (se 1 (by rfl) ⟨2351078, by rfl⟩ : syracuseStep 3134771 = 4702157) B4702157
theorem B2782529 : Blo 1236436 2782529 := bstep (se 2 (by rfl) ⟨1043448, by rfl⟩ : syracuseStep 2782529 = 2086897) B2086897
theorem B1856843 : Blo 1236436 1856843 := bstep (se 1 (by rfl) ⟨1392632, by rfl⟩ : syracuseStep 1856843 = 2785265) B2785265
theorem B1856855 : Blo 1236436 1856855 := bstep (se 1 (by rfl) ⟨1392641, by rfl⟩ : syracuseStep 1856855 = 2785283) B2785283
theorem B16921973 : Blo 1236436 16921973 := bstep (se 5 (by rfl) ⟨793217, by rfl⟩ : syracuseStep 16921973 = 1586435) B1586435
theorem B6264215 : Blo 1236436 6264215 := bstep (se 1 (by rfl) ⟨4698161, by rfl⟩ : syracuseStep 6264215 = 9396323) B9396323
theorem B1856921 : Blo 1236436 1856921 := bstep (se 2 (by rfl) ⟨696345, by rfl⟩ : syracuseStep 1856921 = 1392691) B1392691
theorem B1857035 : Blo 1236436 1857035 := bstep (se 1 (by rfl) ⟨1392776, by rfl⟩ : syracuseStep 1857035 = 2785553) B2785553
theorem B1857047 : Blo 1236436 1857047 := bstep (se 1 (by rfl) ⟨1392785, by rfl⟩ : syracuseStep 1857047 = 2785571) B2785571
theorem B2782745 : Blo 1236436 2782745 := bstep (se 2 (by rfl) ⟨1043529, by rfl⟩ : syracuseStep 2782745 = 2087059) B2087059
theorem B9655853 : Blo 1236436 9655853 := bstep (se 3 (by rfl) ⟨1810472, by rfl⟩ : syracuseStep 9655853 = 3620945) B3620945
theorem B7050797 : Blo 1236436 7050797 := bstep (se 3 (by rfl) ⟨1322024, by rfl⟩ : syracuseStep 7050797 = 2644049) B2644049
theorem B1857113 : Blo 1236436 1857113 := bstep (se 2 (by rfl) ⟨696417, by rfl⟩ : syracuseStep 1857113 = 1392835) B1392835
theorem B4699741 : Blo 1236436 4699741 := bstep (se 3 (by rfl) ⟨881201, by rfl⟩ : syracuseStep 4699741 = 1762403) B1762403
theorem B2782835 : Blo 1236436 2782835 := bstep (se 1 (by rfl) ⟨2087126, by rfl⟩ : syracuseStep 2782835 = 4174253) B4174253
theorem B2782871 : Blo 1236436 2782871 := bstep (se 1 (by rfl) ⟨2087153, by rfl⟩ : syracuseStep 2782871 = 4174307) B4174307
theorem B2086553 : Blo 1236436 2086553 := bstep (se 2 (by rfl) ⟨782457, by rfl⟩ : syracuseStep 2086553 = 1564915) B1564915
theorem B8918707 : Blo 1236436 8918707 := bstep (se 1 (by rfl) ⟨6689030, by rfl⟩ : syracuseStep 8918707 = 13378061) B13378061
theorem B2348747 : Blo 1236436 2348747 := bstep (se 1 (by rfl) ⟨1761560, by rfl⟩ : syracuseStep 2348747 = 3523121) B3523121
theorem B1857227 : Blo 1236436 1857227 := bstep (se 1 (by rfl) ⟨1392920, by rfl⟩ : syracuseStep 1857227 = 2785841) B2785841
theorem B1857239 : Blo 1236436 1857239 := bstep (se 1 (by rfl) ⟨1392929, by rfl⟩ : syracuseStep 1857239 = 2785859) B2785859
theorem B2643673 : Blo 1236436 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B2414323 : Blo 1236436 2414323 := bstep (se 1 (by rfl) ⟨1810742, by rfl⟩ : syracuseStep 2414323 = 3621485) B3621485
theorem B2086681 : Blo 1236436 2086681 := bstep (se 2 (by rfl) ⟨782505, by rfl⟩ : syracuseStep 2086681 = 1565011) B1565011
theorem B1857305 : Blo 1236436 1857305 := bstep (se 2 (by rfl) ⟨696489, by rfl⟩ : syracuseStep 1857305 = 1392979) B1392979
theorem B2783051 : Blo 1236436 2783051 := bstep (se 1 (by rfl) ⟨2087288, by rfl⟩ : syracuseStep 2783051 = 4174577) B4174577
theorem B2783105 : Blo 1236436 2783105 := bstep (se 2 (by rfl) ⟨1043664, by rfl⟩ : syracuseStep 2783105 = 2087329) B2087329
theorem B2348929 : Blo 1236436 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B1857419 : Blo 1236436 1857419 := bstep (se 1 (by rfl) ⟨1393064, by rfl⟩ : syracuseStep 1857419 = 2786129) B2786129
theorem B1857431 : Blo 1236436 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B4175819 : Blo 1236436 4175819 := bstep (se 1 (by rfl) ⟨3131864, by rfl⟩ : syracuseStep 4175819 = 6263729) B6263729
theorem B1857497 : Blo 1236436 1857497 := bstep (se 2 (by rfl) ⟨696561, by rfl⟩ : syracuseStep 1857497 = 1393123) B1393123
theorem B15267857 : Blo 1236436 15267857 := bstep (se 2 (by rfl) ⟨5725446, by rfl⟩ : syracuseStep 15267857 = 11450893) B11450893
theorem B1857611 : Blo 1236436 1857611 := bstep (se 1 (by rfl) ⟨1393208, by rfl⟩ : syracuseStep 1857611 = 2786417) B2786417
theorem B1857623 : Blo 1236436 1857623 := bstep (se 1 (by rfl) ⟨1393217, by rfl⟩ : syracuseStep 1857623 = 2786435) B2786435
theorem B2783321 : Blo 1236436 2783321 := bstep (se 2 (by rfl) ⟨1043745, by rfl⟩ : syracuseStep 2783321 = 2087491) B2087491
theorem B2783411 : Blo 1236436 2783411 := bstep (se 1 (by rfl) ⟨2087558, by rfl⟩ : syracuseStep 2783411 = 4175117) B4175117
theorem B2783447 : Blo 1236436 2783447 := bstep (se 1 (by rfl) ⟨2087585, by rfl⟩ : syracuseStep 2783447 = 4175171) B4175171
theorem B4176089 : Blo 1236436 4176089 := bstep (se 2 (by rfl) ⟨1566033, by rfl⟩ : syracuseStep 4176089 = 3132067) B3132067
theorem B7051481 : Blo 1236436 7051481 := bstep (se 2 (by rfl) ⟨2644305, by rfl⟩ : syracuseStep 7051481 = 5288611) B5288611
theorem B4462813 : Blo 1236436 4462813 := bstep (se 3 (by rfl) ⟨836777, by rfl⟩ : syracuseStep 4462813 = 1673555) B1673555
theorem B9525509 : Blo 1236436 9525509 := bstep (se 4 (by rfl) ⟨893016, by rfl⟩ : syracuseStep 9525509 = 1786033) B1786033
theorem B9402641 : Blo 1236436 9402641 := bstep (se 2 (by rfl) ⟨3525990, by rfl⟩ : syracuseStep 9402641 = 7051981) B7051981
theorem B2087255 : Blo 1236436 2087255 := bstep (se 1 (by rfl) ⟨1565441, by rfl⟩ : syracuseStep 2087255 = 3130883) B3130883
theorem B2783627 : Blo 1236436 2783627 := bstep (se 1 (by rfl) ⟨2087720, by rfl⟩ : syracuseStep 2783627 = 4175441) B4175441
theorem B1390999 : Blo 1236436 1390999 := bstep (se 1 (by rfl) ⟨1043249, by rfl⟩ : syracuseStep 1390999 = 2086499) B2086499
theorem B7043507 : Blo 1236436 7043507 := bstep (se 1 (by rfl) ⟨5282630, by rfl⟩ : syracuseStep 7043507 = 10565261) B10565261
theorem B2783681 : Blo 1236436 2783681 := bstep (se 2 (by rfl) ⟨1043880, by rfl⟩ : syracuseStep 2783681 = 2087761) B2087761
theorem B2644417 : Blo 1236436 2644417 := bstep (se 2 (by rfl) ⟨991656, by rfl⟩ : syracuseStep 2644417 = 1983313) B1983313
theorem B2087383 : Blo 1236436 2087383 := bstep (se 1 (by rfl) ⟨1565537, by rfl⟩ : syracuseStep 2087383 = 3131075) B3131075
theorem B1391179 : Blo 1236436 1391179 := bstep (se 1 (by rfl) ⟨1043384, by rfl⟩ : syracuseStep 1391179 = 2086769) B2086769
theorem B2349643 : Blo 1236436 2349643 := bstep (se 1 (by rfl) ⟨1762232, by rfl⟩ : syracuseStep 2349643 = 3524465) B3524465
theorem B2349719 : Blo 1236436 2349719 := bstep (se 1 (by rfl) ⟨1762289, by rfl⟩ : syracuseStep 2349719 = 3524579) B3524579
theorem B2783897 : Blo 1236436 2783897 := bstep (se 2 (by rfl) ⟨1043961, by rfl⟩ : syracuseStep 2783897 = 2087923) B2087923
theorem B9394865 : Blo 1236436 9394865 := bstep (se 2 (by rfl) ⟨3523074, by rfl⟩ : syracuseStep 9394865 = 7046149) B7046149
theorem B1391287 : Blo 1236436 1391287 := bstep (se 1 (by rfl) ⟨1043465, by rfl⟩ : syracuseStep 1391287 = 2086931) B2086931
theorem B2783987 : Blo 1236436 2783987 := bstep (se 1 (by rfl) ⟨2087990, by rfl⟩ : syracuseStep 2783987 = 4175981) B4175981
theorem B2784023 : Blo 1236436 2784023 := bstep (se 1 (by rfl) ⟨2088017, by rfl⟩ : syracuseStep 2784023 = 4176035) B4176035
theorem B4701017 : Blo 1236436 4701017 := bstep (se 2 (by rfl) ⟨1762881, by rfl⟩ : syracuseStep 4701017 = 3525763) B3525763
theorem B1391467 : Blo 1236436 1391467 := bstep (se 1 (by rfl) ⟨1043600, by rfl⟩ : syracuseStep 1391467 = 2087201) B2087201
theorem B8461207 : Blo 1236436 8461207 := bstep (se 1 (by rfl) ⟨6345905, by rfl⟩ : syracuseStep 8461207 = 12691811) B12691811
theorem B4176791 : Blo 1236436 4176791 := bstep (se 1 (by rfl) ⟨3132593, by rfl⟩ : syracuseStep 4176791 = 6265187) B6265187
theorem B2784203 : Blo 1236436 2784203 := bstep (se 1 (by rfl) ⟨2088152, by rfl⟩ : syracuseStep 2784203 = 4176305) B4176305
theorem B1391575 : Blo 1236436 1391575 := bstep (se 1 (by rfl) ⟨1043681, by rfl⟩ : syracuseStep 1391575 = 2087363) B2087363
theorem B2784257 : Blo 1236436 2784257 := bstep (se 2 (by rfl) ⟨1044096, by rfl⟩ : syracuseStep 2784257 = 2088193) B2088193
theorem B21740557 : Blo 1236436 21740557 := bstep (se 3 (by rfl) ⟨4076354, by rfl⟩ : syracuseStep 21740557 = 8152709) B8152709
theorem B10165313 : Blo 1236436 10165313 := bstep (se 2 (by rfl) ⟨3811992, by rfl⟩ : syracuseStep 10165313 = 7623985) B7623985
theorem B2088011 : Blo 1236436 2088011 := bstep (se 1 (by rfl) ⟨1566008, by rfl⟩ : syracuseStep 2088011 = 3132017) B3132017
theorem B1391755 : Blo 1236436 1391755 := bstep (se 1 (by rfl) ⟨1043816, by rfl⟩ : syracuseStep 1391755 = 2087633) B2087633
theorem B9395351 : Blo 1236436 9395351 := bstep (se 1 (by rfl) ⟨7046513, by rfl⟩ : syracuseStep 9395351 = 14093027) B14093027
theorem B2088139 : Blo 1236436 2088139 := bstep (se 1 (by rfl) ⟨1566104, by rfl⟩ : syracuseStep 2088139 = 3132209) B3132209
theorem B2784473 : Blo 1236436 2784473 := bstep (se 2 (by rfl) ⟨1044177, by rfl⟩ : syracuseStep 2784473 = 2088355) B2088355
theorem B1391863 : Blo 1236436 1391863 := bstep (se 1 (by rfl) ⟨1043897, by rfl⟩ : syracuseStep 1391863 = 2087795) B2087795
theorem B2784563 : Blo 1236436 2784563 := bstep (se 1 (by rfl) ⟨2088422, by rfl⟩ : syracuseStep 2784563 = 4176845) B4176845
theorem B2350387 : Blo 1236436 2350387 := bstep (se 1 (by rfl) ⟨1762790, by rfl⟩ : syracuseStep 2350387 = 3525581) B3525581
theorem B2784599 : Blo 1236436 2784599 := bstep (se 1 (by rfl) ⟨2088449, by rfl⟩ : syracuseStep 2784599 = 4176899) B4176899
theorem B1588567 : Blo 1236436 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B2088281 : Blo 1236436 2088281 := bstep (se 2 (by rfl) ⟨783105, by rfl⟩ : syracuseStep 2088281 = 1566211) B1566211
theorem B1392043 : Blo 1236436 1392043 := bstep (se 1 (by rfl) ⟨1044032, by rfl⟩ : syracuseStep 1392043 = 2088065) B2088065
theorem B5283245 : Blo 1236436 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B4177331 : Blo 1236436 4177331 := bstep (se 1 (by rfl) ⟨3132998, by rfl⟩ : syracuseStep 4177331 = 6265997) B6265997
theorem B1236439 : Blo 1236436 1236439 := bstep (se 1 (by rfl) ⟨927329, by rfl⟩ : syracuseStep 1236439 = 1854659) B1854659
theorem B2088409 : Blo 1236436 2088409 := bstep (se 2 (by rfl) ⟨783153, by rfl⟩ : syracuseStep 2088409 = 1566307) B1566307
theorem B1236459 : Blo 1236436 1236459 := bstep (se 1 (by rfl) ⟨927344, by rfl⟩ : syracuseStep 1236459 = 1854689) B1854689
theorem B1236471 : Blo 1236436 1236471 := bstep (se 1 (by rfl) ⟨927353, by rfl⟩ : syracuseStep 1236471 = 1854707) B1854707
theorem B1236491 : Blo 1236436 1236491 := bstep (se 1 (by rfl) ⟨927368, by rfl⟩ : syracuseStep 1236491 = 1854737) B1854737
theorem B2784779 : Blo 1236436 2784779 := bstep (se 1 (by rfl) ⟨2088584, by rfl⟩ : syracuseStep 2784779 = 4177169) B4177169
theorem B23772689 : Blo 1236436 23772689 := bstep (se 2 (by rfl) ⟨8914758, by rfl⟩ : syracuseStep 23772689 = 17829517) B17829517
theorem B1236503 : Blo 1236436 1236503 := bstep (se 1 (by rfl) ⟨927377, by rfl⟩ : syracuseStep 1236503 = 1854755) B1854755
theorem B1392151 : Blo 1236436 1392151 := bstep (se 1 (by rfl) ⟨1044113, by rfl⟩ : syracuseStep 1392151 = 2088227) B2088227
theorem B2350615 : Blo 1236436 2350615 := bstep (se 1 (by rfl) ⟨1762961, by rfl⟩ : syracuseStep 2350615 = 3525923) B3525923
theorem B1236523 : Blo 1236436 1236523 := bstep (se 1 (by rfl) ⟨927392, by rfl⟩ : syracuseStep 1236523 = 1854785) B1854785
theorem B1236535 : Blo 1236436 1236535 := bstep (se 1 (by rfl) ⟨927401, by rfl⟩ : syracuseStep 1236535 = 1854803) B1854803
theorem B2784833 : Blo 1236436 2784833 := bstep (se 2 (by rfl) ⟨1044312, by rfl⟩ : syracuseStep 2784833 = 2088625) B2088625
theorem B1236555 : Blo 1236436 1236555 := bstep (se 1 (by rfl) ⟨927416, by rfl⟩ : syracuseStep 1236555 = 1854833) B1854833
theorem B1236567 : Blo 1236436 1236567 := bstep (se 1 (by rfl) ⟨927425, by rfl⟩ : syracuseStep 1236567 = 1854851) B1854851
theorem B1236587 : Blo 1236436 1236587 := bstep (se 1 (by rfl) ⟨927440, by rfl⟩ : syracuseStep 1236587 = 1854881) B1854881
theorem B1236599 : Blo 1236436 1236599 := bstep (se 1 (by rfl) ⟨927449, by rfl⟩ : syracuseStep 1236599 = 1854899) B1854899
theorem B2350721 : Blo 1236436 2350721 := bstep (se 2 (by rfl) ⟨881520, by rfl⟩ : syracuseStep 2350721 = 1763041) B1763041
theorem B38125187 : Blo 1236436 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B5021315 : Blo 1236436 5021315 := bstep (se 1 (by rfl) ⟨3765986, by rfl⟩ : syracuseStep 5021315 = 7531973) B7531973
theorem B1236619 : Blo 1236436 1236619 := bstep (se 1 (by rfl) ⟨927464, by rfl⟩ : syracuseStep 1236619 = 1854929) B1854929
theorem B1236631 : Blo 1236436 1236631 := bstep (se 1 (by rfl) ⟨927473, by rfl⟩ : syracuseStep 1236631 = 1854947) B1854947
theorem B1236651 : Blo 1236436 1236651 := bstep (se 1 (by rfl) ⟨927488, by rfl⟩ : syracuseStep 1236651 = 1854977) B1854977
theorem B1236663 : Blo 1236436 1236663 := bstep (se 1 (by rfl) ⟨927497, by rfl⟩ : syracuseStep 1236663 = 1854995) B1854995
theorem B4177601 : Blo 1236436 4177601 := bstep (se 2 (by rfl) ⟨1566600, by rfl⟩ : syracuseStep 4177601 = 3133201) B3133201
theorem B1236683 : Blo 1236436 1236683 := bstep (se 1 (by rfl) ⟨927512, by rfl⟩ : syracuseStep 1236683 = 1855025) B1855025
theorem B1392331 : Blo 1236436 1392331 := bstep (se 1 (by rfl) ⟨1044248, by rfl⟩ : syracuseStep 1392331 = 2088497) B2088497
theorem B1236695 : Blo 1236436 1236695 := bstep (se 1 (by rfl) ⟨927521, by rfl⟩ : syracuseStep 1236695 = 1855043) B1855043
theorem B1236715 : Blo 1236436 1236715 := bstep (se 1 (by rfl) ⟨927536, by rfl⟩ : syracuseStep 1236715 = 1855073) B1855073
theorem B1236727 : Blo 1236436 1236727 := bstep (se 1 (by rfl) ⟨927545, by rfl⟩ : syracuseStep 1236727 = 1855091) B1855091
theorem B1236747 : Blo 1236436 1236747 := bstep (se 1 (by rfl) ⟨927560, by rfl⟩ : syracuseStep 1236747 = 1855121) B1855121
theorem B6782737 : Blo 1236436 6782737 := bstep (se 2 (by rfl) ⟨2543526, by rfl⟩ : syracuseStep 6782737 = 5087053) B5087053
theorem B1236759 : Blo 1236436 1236759 := bstep (se 1 (by rfl) ⟨927569, by rfl⟩ : syracuseStep 1236759 = 1855139) B1855139
theorem B5644055 : Blo 1236436 5644055 := bstep (se 1 (by rfl) ⟨4233041, by rfl⟩ : syracuseStep 5644055 = 8466083) B8466083
theorem B2785049 : Blo 1236436 2785049 := bstep (se 2 (by rfl) ⟨1044393, by rfl⟩ : syracuseStep 2785049 = 2088787) B2088787
theorem B2350873 : Blo 1236436 2350873 := bstep (se 2 (by rfl) ⟨881577, by rfl⟩ : syracuseStep 2350873 = 1763155) B1763155
theorem B1236779 : Blo 1236436 1236779 := bstep (se 1 (by rfl) ⟨927584, by rfl⟩ : syracuseStep 1236779 = 1855169) B1855169
theorem B1236791 : Blo 1236436 1236791 := bstep (se 1 (by rfl) ⟨927593, by rfl⟩ : syracuseStep 1236791 = 1855187) B1855187
theorem B1392439 : Blo 1236436 1392439 := bstep (se 1 (by rfl) ⟨1044329, by rfl⟩ : syracuseStep 1392439 = 2088659) B2088659
theorem B1236811 : Blo 1236436 1236811 := bstep (se 1 (by rfl) ⟨927608, by rfl⟩ : syracuseStep 1236811 = 1855217) B1855217
theorem B1236823 : Blo 1236436 1236823 := bstep (se 1 (by rfl) ⟨927617, by rfl⟩ : syracuseStep 1236823 = 1855235) B1855235
theorem B7044965 : Blo 1236436 7044965 := bstep (se 4 (by rfl) ⟨660465, by rfl⟩ : syracuseStep 7044965 = 1320931) B1320931
theorem B1236843 : Blo 1236436 1236843 := bstep (se 1 (by rfl) ⟨927632, by rfl⟩ : syracuseStep 1236843 = 1855265) B1855265
theorem B2785139 : Blo 1236436 2785139 := bstep (se 1 (by rfl) ⟨2088854, by rfl⟩ : syracuseStep 2785139 = 4177709) B4177709
theorem B1236855 : Blo 1236436 1236855 := bstep (se 1 (by rfl) ⟨927641, by rfl⟩ : syracuseStep 1236855 = 1855283) B1855283
theorem B1236875 : Blo 1236436 1236875 := bstep (se 1 (by rfl) ⟨927656, by rfl⟩ : syracuseStep 1236875 = 1855313) B1855313
theorem B1236887 : Blo 1236436 1236887 := bstep (se 1 (by rfl) ⟨927665, by rfl⟩ : syracuseStep 1236887 = 1855331) B1855331
theorem B2785175 : Blo 1236436 2785175 := bstep (se 1 (by rfl) ⟨2088881, by rfl⟩ : syracuseStep 2785175 = 4177763) B4177763
theorem B2260889 : Blo 1236436 2260889 := bstep (se 2 (by rfl) ⟨847833, by rfl⟩ : syracuseStep 2260889 = 1695667) B1695667
theorem B1236907 : Blo 1236436 1236907 := bstep (se 1 (by rfl) ⟨927680, by rfl⟩ : syracuseStep 1236907 = 1855361) B1855361
theorem B1236919 : Blo 1236436 1236919 := bstep (se 1 (by rfl) ⟨927689, by rfl⟩ : syracuseStep 1236919 = 1855379) B1855379
theorem B1236939 : Blo 1236436 1236939 := bstep (se 1 (by rfl) ⟨927704, by rfl⟩ : syracuseStep 1236939 = 1855409) B1855409
theorem B1236951 : Blo 1236436 1236951 := bstep (se 1 (by rfl) ⟨927713, by rfl⟩ : syracuseStep 1236951 = 1855427) B1855427
theorem B1236971 : Blo 1236436 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B1392619 : Blo 1236436 1392619 := bstep (se 1 (by rfl) ⟨1044464, by rfl⟩ : syracuseStep 1392619 = 2088929) B2088929
theorem B1236983 : Blo 1236436 1236983 := bstep (se 1 (by rfl) ⟨927737, by rfl⟩ : syracuseStep 1236983 = 1855475) B1855475
theorem B1236999 : Blo 1236436 1236999 := bstep (se 1 (by rfl) ⟨927749, by rfl⟩ : syracuseStep 1236999 = 1855499) B1855499
theorem B5013515 : Blo 1236436 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B1237007 : Blo 1236436 1237007 := bstep (se 1 (by rfl) ⟨927755, by rfl⟩ : syracuseStep 1237007 = 1855511) B1855511
theorem B1392655 : Blo 1236436 1392655 := bstep (se 1 (by rfl) ⟨1044491, by rfl⟩ : syracuseStep 1392655 = 2088983) B2088983
theorem B2203691 : Blo 1236436 2203691 := bstep (se 1 (by rfl) ⟨1652768, by rfl⟩ : syracuseStep 2203691 = 3305537) B3305537
theorem B2089003 : Blo 1236436 2089003 := bstep (se 1 (by rfl) ⟨1566752, by rfl⟩ : syracuseStep 2089003 = 3133505) B3133505
theorem B40714285 : Blo 1236436 40714285 := bstep (se 3 (by rfl) ⟨7633928, by rfl⟩ : syracuseStep 40714285 = 15267857) B15267857
theorem B3522619 : Blo 1236436 3522619 := bstep (se 1 (by rfl) ⟨2641964, by rfl⟩ : syracuseStep 3522619 = 5283929) B5283929
theorem B1237051 : Blo 1236436 1237051 := bstep (se 1 (by rfl) ⟨927788, by rfl⟩ : syracuseStep 1237051 = 1855577) B1855577
theorem B3342397 : Blo 1236436 3342397 := bstep (se 3 (by rfl) ⟨626699, by rfl⟩ : syracuseStep 3342397 = 1253399) B1253399
theorem B1237127 : Blo 1236436 1237127 := bstep (se 1 (by rfl) ⟨927845, by rfl⟩ : syracuseStep 1237127 = 1855691) B1855691
theorem B1237135 : Blo 1236436 1237135 := bstep (se 1 (by rfl) ⟨927851, by rfl⟩ : syracuseStep 1237135 = 1855703) B1855703
theorem B2785427 : Blo 1236436 2785427 := bstep (se 1 (by rfl) ⟨2089070, by rfl⟩ : syracuseStep 2785427 = 4178141) B4178141
theorem B11894957 : Blo 1236436 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B2089145 : Blo 1236436 2089145 := bstep (se 2 (by rfl) ⟨783429, by rfl⟩ : syracuseStep 2089145 = 1566859) B1566859
theorem B1237179 : Blo 1236436 1237179 := bstep (se 1 (by rfl) ⟨927884, by rfl⟩ : syracuseStep 1237179 = 1855769) B1855769
theorem B2785481 : Blo 1236436 2785481 := bstep (se 2 (by rfl) ⟨1044555, by rfl⟩ : syracuseStep 2785481 = 2089111) B2089111
theorem B1237255 : Blo 1236436 1237255 := bstep (se 1 (by rfl) ⟨927941, by rfl⟩ : syracuseStep 1237255 = 1855883) B1855883
theorem B1237263 : Blo 1236436 1237263 := bstep (se 1 (by rfl) ⟨927947, by rfl⟩ : syracuseStep 1237263 = 1855895) B1855895
theorem B8470817 : Blo 1236436 8470817 := bstep (se 2 (by rfl) ⟨3176556, by rfl⟩ : syracuseStep 8470817 = 6353113) B6353113
theorem B1237307 : Blo 1236436 1237307 := bstep (se 1 (by rfl) ⟨927980, by rfl⟩ : syracuseStep 1237307 = 1855961) B1855961
theorem B1237383 : Blo 1236436 1237383 := bstep (se 1 (by rfl) ⟨928037, by rfl⟩ : syracuseStep 1237383 = 1856075) B1856075
theorem B1237391 : Blo 1236436 1237391 := bstep (se 1 (by rfl) ⟨928043, by rfl⟩ : syracuseStep 1237391 = 1856087) B1856087
theorem B90259859 : Blo 1236436 90259859 := bstep (se 1 (by rfl) ⟨67694894, by rfl⟩ : syracuseStep 90259859 = 135389789) B135389789
theorem B1237435 : Blo 1236436 1237435 := bstep (se 1 (by rfl) ⟨928076, by rfl⟩ : syracuseStep 1237435 = 1856153) B1856153
theorem B2974153 : Blo 1236436 2974153 := bstep (se 2 (by rfl) ⟨1115307, by rfl⟩ : syracuseStep 2974153 = 2230615) B2230615
theorem B11895299 : Blo 1236436 11895299 := bstep (se 1 (by rfl) ⟨8921474, by rfl⟩ : syracuseStep 11895299 = 17842949) B17842949
theorem B1237511 : Blo 1236436 1237511 := bstep (se 1 (by rfl) ⟨928133, by rfl⟩ : syracuseStep 1237511 = 1856267) B1856267
theorem B1393159 : Blo 1236436 1393159 := bstep (se 1 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 1393159 = 2089739) B2089739
theorem B1237519 : Blo 1236436 1237519 := bstep (se 1 (by rfl) ⟨928139, by rfl⟩ : syracuseStep 1237519 = 1856279) B1856279
theorem B1761851 : Blo 1236436 1761851 := bstep (se 1 (by rfl) ⟨1321388, by rfl⟩ : syracuseStep 1761851 = 2642777) B2642777
theorem B1237563 : Blo 1236436 1237563 := bstep (se 1 (by rfl) ⟨928172, by rfl⟩ : syracuseStep 1237563 = 1856345) B1856345
theorem B4457047 : Blo 1236436 4457047 := bstep (se 1 (by rfl) ⟨3342785, by rfl⟩ : syracuseStep 4457047 = 6685571) B6685571
theorem B4178519 : Blo 1236436 4178519 := bstep (se 1 (by rfl) ⟨3133889, by rfl⟩ : syracuseStep 4178519 = 6267779) B6267779
theorem B1237639 : Blo 1236436 1237639 := bstep (se 1 (by rfl) ⟨928229, by rfl⟩ : syracuseStep 1237639 = 1856459) B1856459
theorem B1254031 : Blo 1236436 1254031 := bstep (se 1 (by rfl) ⟨940523, by rfl⟩ : syracuseStep 1254031 = 1881047) B1881047
theorem B1237647 : Blo 1236436 1237647 := bstep (se 1 (by rfl) ⟨928235, by rfl⟩ : syracuseStep 1237647 = 1856471) B1856471
theorem B1237691 : Blo 1236436 1237691 := bstep (se 1 (by rfl) ⟨928268, by rfl⟩ : syracuseStep 1237691 = 1856537) B1856537
theorem B1237767 : Blo 1236436 1237767 := bstep (se 1 (by rfl) ⟨928325, by rfl⟩ : syracuseStep 1237767 = 1856651) B1856651
theorem B3130123 : Blo 1236436 3130123 := bstep (se 1 (by rfl) ⟨2347592, by rfl⟩ : syracuseStep 3130123 = 4695185) B4695185
theorem B1237775 : Blo 1236436 1237775 := bstep (se 1 (by rfl) ⟨928331, by rfl⟩ : syracuseStep 1237775 = 1856663) B1856663
theorem B3343133 : Blo 1236436 3343133 := bstep (se 3 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 3343133 = 1253675) B1253675
theorem B7529249 : Blo 1236436 7529249 := bstep (se 2 (by rfl) ⟨2823468, by rfl⟩ : syracuseStep 7529249 = 5646937) B5646937
theorem B1237819 : Blo 1236436 1237819 := bstep (se 1 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 1237819 = 1856729) B1856729
theorem B2089847 : Blo 1236436 2089847 := bstep (se 1 (by rfl) ⟨1567385, by rfl⟩ : syracuseStep 2089847 = 3134771) B3134771
theorem B3523463 : Blo 1236436 3523463 := bstep (se 1 (by rfl) ⟨2642597, by rfl⟩ : syracuseStep 3523463 = 5285195) B5285195
theorem B1237895 : Blo 1236436 1237895 := bstep (se 1 (by rfl) ⟨928421, by rfl⟩ : syracuseStep 1237895 = 1856843) B1856843
theorem B2786183 : Blo 1236436 2786183 := bstep (se 1 (by rfl) ⟨2089637, by rfl⟩ : syracuseStep 2786183 = 4179275) B4179275
theorem B1237903 : Blo 1236436 1237903 := bstep (se 1 (by rfl) ⟨928427, by rfl⟩ : syracuseStep 1237903 = 1856855) B1856855
theorem B3130265 : Blo 1236436 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B1237947 : Blo 1236436 1237947 := bstep (se 1 (by rfl) ⟨928460, by rfl⟩ : syracuseStep 1237947 = 1856921) B1856921
theorem B1238023 : Blo 1236436 1238023 := bstep (se 1 (by rfl) ⟨928517, by rfl⟩ : syracuseStep 1238023 = 1857035) B1857035
theorem B1238031 : Blo 1236436 1238031 := bstep (se 1 (by rfl) ⟨928523, by rfl⟩ : syracuseStep 1238031 = 1857047) B1857047
theorem B3130427 : Blo 1236436 3130427 := bstep (se 1 (by rfl) ⟨2347820, by rfl⟩ : syracuseStep 3130427 = 4695641) B4695641
theorem B1238075 : Blo 1236436 1238075 := bstep (se 1 (by rfl) ⟨928556, by rfl⟩ : syracuseStep 1238075 = 1857113) B1857113
theorem B5358653 : Blo 1236436 5358653 := bstep (se 3 (by rfl) ⟨1004747, by rfl⟩ : syracuseStep 5358653 = 2009495) B2009495
theorem B4179005 : Blo 1236436 4179005 := bstep (se 3 (by rfl) ⟨783563, by rfl⟩ : syracuseStep 4179005 = 1567127) B1567127
theorem B2786363 : Blo 1236436 2786363 := bstep (se 1 (by rfl) ⟨2089772, by rfl⟩ : syracuseStep 2786363 = 4179545) B4179545
theorem B2229383 : Blo 1236436 2229383 := bstep (se 1 (by rfl) ⟨1672037, by rfl⟩ : syracuseStep 2229383 = 3344075) B3344075
theorem B1565831 : Blo 1236436 1565831 := bstep (se 1 (by rfl) ⟨1174373, by rfl⟩ : syracuseStep 1565831 = 2348747) B2348747
theorem B1238151 : Blo 1236436 1238151 := bstep (se 1 (by rfl) ⟨928613, by rfl⟩ : syracuseStep 1238151 = 1857227) B1857227
theorem B1238159 : Blo 1236436 1238159 := bstep (se 1 (by rfl) ⟨928619, by rfl⟩ : syracuseStep 1238159 = 1857239) B1857239
theorem B1762489 : Blo 1236436 1762489 := bstep (se 2 (by rfl) ⟨660933, by rfl⟩ : syracuseStep 1762489 = 1321867) B1321867
theorem B1238203 : Blo 1236436 1238203 := bstep (se 1 (by rfl) ⟨928652, by rfl⟩ : syracuseStep 1238203 = 1857305) B1857305
theorem B11281609 : Blo 1236436 11281609 := bstep (se 2 (by rfl) ⟨4230603, by rfl⟩ : syracuseStep 11281609 = 8461207) B8461207
theorem B1238279 : Blo 1236436 1238279 := bstep (se 1 (by rfl) ⟨928709, by rfl⟩ : syracuseStep 1238279 = 1857419) B1857419
theorem B1238287 : Blo 1236436 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B1238331 : Blo 1236436 1238331 := bstep (se 1 (by rfl) ⟨928748, by rfl⟩ : syracuseStep 1238331 = 1857497) B1857497
theorem B1238407 : Blo 1236436 1238407 := bstep (se 1 (by rfl) ⟨928805, by rfl⟩ : syracuseStep 1238407 = 1857611) B1857611
theorem B1238415 : Blo 1236436 1238415 := bstep (se 1 (by rfl) ⟨928811, by rfl⟩ : syracuseStep 1238415 = 1857623) B1857623
theorem B3130771 : Blo 1236436 3130771 := bstep (se 1 (by rfl) ⟨2348078, by rfl⟩ : syracuseStep 3130771 = 4696157) B4696157
theorem B12060089 : Blo 1236436 12060089 := bstep (se 2 (by rfl) ⟨4522533, by rfl⟩ : syracuseStep 12060089 = 9045067) B9045067
theorem B25748941 : Blo 1236436 25748941 := bstep (se 3 (by rfl) ⟨4827926, by rfl⟩ : syracuseStep 25748941 = 9655853) B9655853
theorem B6350339 : Blo 1236436 6350339 := bstep (se 1 (by rfl) ⟨4762754, by rfl⟩ : syracuseStep 6350339 = 9525509) B9525509
theorem B6268427 : Blo 1236436 6268427 := bstep (se 1 (by rfl) ⟨4701320, by rfl⟩ : syracuseStep 6268427 = 9402641) B9402641
theorem B3130913 : Blo 1236436 3130913 := bstep (se 2 (by rfl) ⟨1174092, by rfl⟩ : syracuseStep 3130913 = 2348185) B2348185
theorem B4695671 : Blo 1236436 4695671 := bstep (se 1 (by rfl) ⟨3521753, by rfl⟩ : syracuseStep 4695671 = 7043507) B7043507
theorem B3524249 : Blo 1236436 3524249 := bstep (se 2 (by rfl) ⟨1321593, by rfl⟩ : syracuseStep 3524249 = 2643187) B2643187
theorem B6268589 : Blo 1236436 6268589 := bstep (se 3 (by rfl) ⟨1175360, by rfl⟩ : syracuseStep 6268589 = 2350721) B2350721
theorem B6686479 : Blo 1236436 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B1566479 : Blo 1236436 1566479 := bstep (se 1 (by rfl) ⟨1174859, by rfl⟩ : syracuseStep 1566479 = 2349719) B2349719
theorem B10569635 : Blo 1236436 10569635 := bstep (se 1 (by rfl) ⟨7927226, by rfl⟩ : syracuseStep 10569635 = 15854453) B15854453
theorem B6776875 : Blo 1236436 6776875 := bstep (se 1 (by rfl) ⟨5082656, by rfl⟩ : syracuseStep 6776875 = 10165313) B10165313
theorem B3967177 : Blo 1236436 3967177 := bstep (se 2 (by rfl) ⟨1487691, by rfl⟩ : syracuseStep 3967177 = 2975383) B2975383
theorem B7047425 : Blo 1236436 7047425 := bstep (se 2 (by rfl) ⟨2642784, by rfl⟩ : syracuseStep 7047425 = 5285569) B5285569
theorem B3524897 : Blo 1236436 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B2820395 : Blo 1236436 2820395 := bstep (se 1 (by rfl) ⟨2115296, by rfl⟩ : syracuseStep 2820395 = 4230593) B4230593
theorem B6261137 : Blo 1236436 6261137 := bstep (se 2 (by rfl) ⟨2347926, by rfl⟩ : syracuseStep 6261137 = 4695853) B4695853
theorem B3131905 : Blo 1236436 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B3762703 : Blo 1236436 3762703 := bstep (se 1 (by rfl) ⟨2822027, by rfl⟩ : syracuseStep 3762703 = 5644055) B5644055
theorem B4696643 : Blo 1236436 4696643 := bstep (se 1 (by rfl) ⟨3522482, by rfl⟩ : syracuseStep 4696643 = 7044965) B7044965
theorem B1411771 : Blo 1236436 1411771 := bstep (se 1 (by rfl) ⟨1058828, by rfl⟩ : syracuseStep 1411771 = 2117657) B2117657
theorem B5941961 : Blo 1236436 5941961 := bstep (se 2 (by rfl) ⟨2228235, by rfl⟩ : syracuseStep 5941961 = 4456471) B4456471
theorem B7047881 : Blo 1236436 7047881 := bstep (se 2 (by rfl) ⟨2642955, by rfl⟩ : syracuseStep 7047881 = 5285911) B5285911
theorem B1608455 : Blo 1236436 1608455 := bstep (se 1 (by rfl) ⟨1206341, by rfl⟩ : syracuseStep 1608455 = 2412683) B2412683
theorem B11889611 : Blo 1236436 11889611 := bstep (se 1 (by rfl) ⟨8917208, by rfl⟩ : syracuseStep 11889611 = 17834417) B17834417
theorem B5950417 : Blo 1236436 5950417 := bstep (se 2 (by rfl) ⟨2231406, by rfl⟩ : syracuseStep 5950417 = 4462813) B4462813
theorem B4697099 : Blo 1236436 4697099 := bstep (se 1 (by rfl) ⟨3522824, by rfl⟩ : syracuseStep 4697099 = 7045649) B7045649
theorem B16067645 : Blo 1236436 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B3132503 : Blo 1236436 3132503 := bstep (se 1 (by rfl) ⟨2349377, by rfl⟩ : syracuseStep 3132503 = 4698755) B4698755
theorem B1322119 : Blo 1236436 1322119 := bstep (se 1 (by rfl) ⟨991589, by rfl⟩ : syracuseStep 1322119 = 1983179) B1983179
theorem B1854665 : Blo 1236436 1854665 := bstep (se 2 (by rfl) ⟨695499, by rfl⟩ : syracuseStep 1854665 = 1390999) B1390999
theorem B3525889 : Blo 1236436 3525889 := bstep (se 2 (by rfl) ⟨1322208, by rfl⟩ : syracuseStep 3525889 = 2644417) B2644417
theorem B3132715 : Blo 1236436 3132715 := bstep (se 1 (by rfl) ⟨2349536, by rfl⟩ : syracuseStep 3132715 = 4699073) B4699073
theorem B1854779 : Blo 1236436 1854779 := bstep (se 1 (by rfl) ⟨1391084, by rfl⟩ : syracuseStep 1854779 = 2782169) B2782169
theorem B6352187 : Blo 1236436 6352187 := bstep (se 1 (by rfl) ⟨4764140, by rfl⟩ : syracuseStep 6352187 = 9528281) B9528281
theorem B1854839 : Blo 1236436 1854839 := bstep (se 1 (by rfl) ⟨1391129, by rfl⟩ : syracuseStep 1854839 = 2782259) B2782259
theorem B1854863 : Blo 1236436 1854863 := bstep (se 1 (by rfl) ⟨1391147, by rfl⟩ : syracuseStep 1854863 = 2782295) B2782295
theorem B1854905 : Blo 1236436 1854905 := bstep (se 2 (by rfl) ⟨695589, by rfl⟩ : syracuseStep 1854905 = 1391179) B1391179
theorem B4459961 : Blo 1236436 4459961 := bstep (se 2 (by rfl) ⟨1672485, by rfl⟩ : syracuseStep 4459961 = 3344971) B3344971
theorem B3132857 : Blo 1236436 3132857 := bstep (se 2 (by rfl) ⟨1174821, by rfl⟩ : syracuseStep 3132857 = 2349643) B2349643
theorem B10579409 : Blo 1236436 10579409 := bstep (se 2 (by rfl) ⟨3967278, by rfl⟩ : syracuseStep 10579409 = 7934557) B7934557
theorem B1854983 : Blo 1236436 1854983 := bstep (se 1 (by rfl) ⟨1391237, by rfl⟩ : syracuseStep 1854983 = 2782475) B2782475
theorem B1855019 : Blo 1236436 1855019 := bstep (se 1 (by rfl) ⟨1391264, by rfl⟩ : syracuseStep 1855019 = 2782529) B2782529
theorem B1855049 : Blo 1236436 1855049 := bstep (se 2 (by rfl) ⟨695643, by rfl⟩ : syracuseStep 1855049 = 1391287) B1391287
theorem B45125261 : Blo 1236436 45125261 := bstep (se 3 (by rfl) ⟨8460986, by rfl⟩ : syracuseStep 45125261 = 16921973) B16921973
theorem B3346073 : Blo 1236436 3346073 := bstep (se 2 (by rfl) ⟨1254777, by rfl⟩ : syracuseStep 3346073 = 2509555) B2509555
theorem B1855163 : Blo 1236436 1855163 := bstep (se 1 (by rfl) ⟨1391372, by rfl⟩ : syracuseStep 1855163 = 2782745) B2782745
theorem B1855223 : Blo 1236436 1855223 := bstep (se 1 (by rfl) ⟨1391417, by rfl⟩ : syracuseStep 1855223 = 2782835) B2782835
theorem B1855247 : Blo 1236436 1855247 := bstep (se 1 (by rfl) ⟨1391435, by rfl⟩ : syracuseStep 1855247 = 2782871) B2782871
theorem B3174187 : Blo 1236436 3174187 := bstep (se 1 (by rfl) ⟨2380640, by rfl⟩ : syracuseStep 3174187 = 4761281) B4761281
theorem B24104749 : Blo 1236436 24104749 := bstep (se 3 (by rfl) ⟨4519640, by rfl⟩ : syracuseStep 24104749 = 9039281) B9039281
theorem B1855289 : Blo 1236436 1855289 := bstep (se 2 (by rfl) ⟨695733, by rfl⟩ : syracuseStep 1855289 = 1391467) B1391467
theorem B3764029 : Blo 1236436 3764029 := bstep (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) B1411511
theorem B1855367 : Blo 1236436 1855367 := bstep (se 1 (by rfl) ⟨1391525, by rfl⟩ : syracuseStep 1855367 = 2783051) B2783051
theorem B1855403 : Blo 1236436 1855403 := bstep (se 1 (by rfl) ⟨1391552, by rfl⟩ : syracuseStep 1855403 = 2783105) B2783105
theorem B1855433 : Blo 1236436 1855433 := bstep (se 2 (by rfl) ⟨695787, by rfl⟩ : syracuseStep 1855433 = 1391575) B1391575
theorem B28987409 : Blo 1236436 28987409 := bstep (se 2 (by rfl) ⟨10870278, by rfl⟩ : syracuseStep 28987409 = 21740557) B21740557
theorem B1855547 : Blo 1236436 1855547 := bstep (se 1 (by rfl) ⟨1391660, by rfl⟩ : syracuseStep 1855547 = 2783321) B2783321
theorem B1855607 : Blo 1236436 1855607 := bstep (se 1 (by rfl) ⟨1391705, by rfl⟩ : syracuseStep 1855607 = 2783411) B2783411
theorem B1855631 : Blo 1236436 1855631 := bstep (se 1 (by rfl) ⟨1391723, by rfl⟩ : syracuseStep 1855631 = 2783447) B2783447
theorem B1855673 : Blo 1236436 1855673 := bstep (se 2 (by rfl) ⟨695877, by rfl⟩ : syracuseStep 1855673 = 1391755) B1391755
theorem B1855751 : Blo 1236436 1855751 := bstep (se 1 (by rfl) ⟨1391813, by rfl⟩ : syracuseStep 1855751 = 2783627) B2783627
theorem B11890961 : Blo 1236436 11890961 := bstep (se 2 (by rfl) ⟨4459110, by rfl⟩ : syracuseStep 11890961 = 8918221) B8918221
theorem B1855787 : Blo 1236436 1855787 := bstep (se 1 (by rfl) ⟨1391840, by rfl⟩ : syracuseStep 1855787 = 2783681) B2783681
theorem B1855817 : Blo 1236436 1855817 := bstep (se 2 (by rfl) ⟨695931, by rfl⟩ : syracuseStep 1855817 = 1391863) B1391863
theorem B3133849 : Blo 1236436 3133849 := bstep (se 2 (by rfl) ⟨1175193, by rfl⟩ : syracuseStep 3133849 = 2350387) B2350387
theorem B1855931 : Blo 1236436 1855931 := bstep (se 1 (by rfl) ⟨1391948, by rfl⟩ : syracuseStep 1855931 = 2783897) B2783897
theorem B2118089 : Blo 1236436 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B6263243 : Blo 1236436 6263243 := bstep (se 1 (by rfl) ⟨4697432, by rfl⟩ : syracuseStep 6263243 = 9394865) B9394865
theorem B1855991 : Blo 1236436 1855991 := bstep (se 1 (by rfl) ⟨1391993, by rfl⟩ : syracuseStep 1855991 = 2783987) B2783987
theorem B1856015 : Blo 1236436 1856015 := bstep (se 1 (by rfl) ⟨1392011, by rfl⟩ : syracuseStep 1856015 = 2784023) B2784023
theorem B1856057 : Blo 1236436 1856057 := bstep (se 2 (by rfl) ⟨696021, by rfl⟩ : syracuseStep 1856057 = 1392043) B1392043
theorem B3134011 : Blo 1236436 3134011 := bstep (se 1 (by rfl) ⟨2350508, by rfl⟩ : syracuseStep 3134011 = 4701017) B4701017
theorem B1856135 : Blo 1236436 1856135 := bstep (se 1 (by rfl) ⟨1392101, by rfl⟩ : syracuseStep 1856135 = 2784203) B2784203
theorem B1856171 : Blo 1236436 1856171 := bstep (se 1 (by rfl) ⟨1392128, by rfl⟩ : syracuseStep 1856171 = 2784257) B2784257
theorem B14103233 : Blo 1236436 14103233 := bstep (se 2 (by rfl) ⟨5288712, by rfl⟩ : syracuseStep 14103233 = 10577425) B10577425
theorem B1856201 : Blo 1236436 1856201 := bstep (se 2 (by rfl) ⟨696075, by rfl⟩ : syracuseStep 1856201 = 1392151) B1392151
theorem B3134153 : Blo 1236436 3134153 := bstep (se 2 (by rfl) ⟨1175307, by rfl⟩ : syracuseStep 3134153 = 2350615) B2350615
theorem B6263567 : Blo 1236436 6263567 := bstep (se 1 (by rfl) ⟨4697675, by rfl⟩ : syracuseStep 6263567 = 9395351) B9395351
theorem B1856315 : Blo 1236436 1856315 := bstep (se 1 (by rfl) ⟨1392236, by rfl⟩ : syracuseStep 1856315 = 2784473) B2784473
theorem B1856375 : Blo 1236436 1856375 := bstep (se 1 (by rfl) ⟨1392281, by rfl⟩ : syracuseStep 1856375 = 2784563) B2784563
theorem B1856399 : Blo 1236436 1856399 := bstep (se 1 (by rfl) ⟨1392299, by rfl⟩ : syracuseStep 1856399 = 2784599) B2784599
theorem B4174739 : Blo 1236436 4174739 := bstep (se 1 (by rfl) ⟨3131054, by rfl⟩ : syracuseStep 4174739 = 6262109) B6262109
theorem B11891609 : Blo 1236436 11891609 := bstep (se 2 (by rfl) ⟨4459353, by rfl⟩ : syracuseStep 11891609 = 8918707) B8918707
theorem B1856441 : Blo 1236436 1856441 := bstep (se 2 (by rfl) ⟨696165, by rfl⟩ : syracuseStep 1856441 = 1392331) B1392331
theorem B1856519 : Blo 1236436 1856519 := bstep (se 1 (by rfl) ⟨1392389, by rfl⟩ : syracuseStep 1856519 = 2784779) B2784779
theorem B15848459 : Blo 1236436 15848459 := bstep (se 1 (by rfl) ⟨11886344, by rfl⟩ : syracuseStep 15848459 = 23772689) B23772689
theorem B3814411 : Blo 1236436 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B2782223 : Blo 1236436 2782223 := bstep (se 1 (by rfl) ⟨2086667, by rfl⟩ : syracuseStep 2782223 = 4173335) B4173335
theorem B2782241 : Blo 1236436 2782241 := bstep (se 2 (by rfl) ⟨1043340, by rfl⟩ : syracuseStep 2782241 = 2086681) B2086681
theorem B3134497 : Blo 1236436 3134497 := bstep (se 2 (by rfl) ⟨1175436, by rfl⟩ : syracuseStep 3134497 = 2350873) B2350873
theorem B1856555 : Blo 1236436 1856555 := bstep (se 1 (by rfl) ⟨1392416, by rfl⟩ : syracuseStep 1856555 = 2784833) B2784833
theorem B1881145 : Blo 1236436 1881145 := bstep (se 2 (by rfl) ⟨705429, by rfl⟩ : syracuseStep 1881145 = 1410859) B1410859
theorem B1856585 : Blo 1236436 1856585 := bstep (se 2 (by rfl) ⟨696219, by rfl⟩ : syracuseStep 1856585 = 1392439) B1392439
theorem B25416791 : Blo 1236436 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B3347543 : Blo 1236436 3347543 := bstep (se 1 (by rfl) ⟨2510657, by rfl⟩ : syracuseStep 3347543 = 5021315) B5021315
theorem B4699255 : Blo 1236436 4699255 := bstep (se 1 (by rfl) ⟨3524441, by rfl⟩ : syracuseStep 4699255 = 7048883) B7048883
theorem B1856699 : Blo 1236436 1856699 := bstep (se 1 (by rfl) ⟨1392524, by rfl⟩ : syracuseStep 1856699 = 2785049) B2785049
theorem B1856759 : Blo 1236436 1856759 := bstep (se 1 (by rfl) ⟨1392569, by rfl⟩ : syracuseStep 1856759 = 2785139) B2785139
theorem B1856783 : Blo 1236436 1856783 := bstep (se 1 (by rfl) ⟨1392587, by rfl⟩ : syracuseStep 1856783 = 2785175) B2785175
theorem B1856825 : Blo 1236436 1856825 := bstep (se 2 (by rfl) ⟨696309, by rfl⟩ : syracuseStep 1856825 = 1392619) B1392619
theorem B2782583 : Blo 1236436 2782583 := bstep (se 1 (by rfl) ⟨2086937, by rfl⟩ : syracuseStep 2782583 = 4173875) B4173875
theorem B5944711 : Blo 1236436 5944711 := bstep (se 1 (by rfl) ⟨4458533, by rfl⟩ : syracuseStep 5944711 = 8917067) B8917067
theorem B1856903 : Blo 1236436 1856903 := bstep (se 1 (by rfl) ⟨1392677, by rfl⟩ : syracuseStep 1856903 = 2785355) B2785355
theorem B1856939 : Blo 1236436 1856939 := bstep (se 1 (by rfl) ⟨1392704, by rfl⟩ : syracuseStep 1856939 = 2785409) B2785409
theorem B2348489 : Blo 1236436 2348489 := bstep (se 2 (by rfl) ⟨880683, by rfl⟩ : syracuseStep 2348489 = 1761367) B1761367
theorem B1856969 : Blo 1236436 1856969 := bstep (se 2 (by rfl) ⟨696363, by rfl⟩ : syracuseStep 1856969 = 1392727) B1392727
theorem B2782763 : Blo 1236436 2782763 := bstep (se 1 (by rfl) ⟨2087072, by rfl⟩ : syracuseStep 2782763 = 4174145) B4174145
theorem B1857083 : Blo 1236436 1857083 := bstep (se 1 (by rfl) ⟨1392812, by rfl⟩ : syracuseStep 1857083 = 2785625) B2785625
theorem B5289533 : Blo 1236436 5289533 := bstep (se 3 (by rfl) ⟨991787, by rfl⟩ : syracuseStep 5289533 = 1983575) B1983575
theorem B2086519 : Blo 1236436 2086519 := bstep (se 1 (by rfl) ⟨1564889, by rfl⟩ : syracuseStep 2086519 = 3129779) B3129779
theorem B1857143 : Blo 1236436 1857143 := bstep (se 1 (by rfl) ⟨1392857, by rfl⟩ : syracuseStep 1857143 = 2785715) B2785715
theorem B1857167 : Blo 1236436 1857167 := bstep (se 1 (by rfl) ⟨1392875, by rfl⟩ : syracuseStep 1857167 = 2785751) B2785751
theorem B7042733 : Blo 1236436 7042733 := bstep (se 3 (by rfl) ⟨1320512, by rfl⟩ : syracuseStep 7042733 = 2641025) B2641025
theorem B1857209 : Blo 1236436 1857209 := bstep (se 2 (by rfl) ⟨696453, by rfl⟩ : syracuseStep 1857209 = 1392907) B1392907
theorem B9393893 : Blo 1236436 9393893 := bstep (se 4 (by rfl) ⟨880677, by rfl⟩ : syracuseStep 9393893 = 1761355) B1761355
theorem B5281537 : Blo 1236436 5281537 := bstep (se 2 (by rfl) ⟨1980576, by rfl⟩ : syracuseStep 5281537 = 3961153) B3961153
theorem B1857287 : Blo 1236436 1857287 := bstep (se 1 (by rfl) ⟨1392965, by rfl⟩ : syracuseStep 1857287 = 2785931) B2785931
theorem B3962639 : Blo 1236436 3962639 := bstep (se 1 (by rfl) ⟨2971979, by rfl⟩ : syracuseStep 3962639 = 5943959) B5943959
theorem B30111533 : Blo 1236436 30111533 := bstep (se 3 (by rfl) ⟨5645912, by rfl⟩ : syracuseStep 30111533 = 11291825) B11291825
theorem B1857323 : Blo 1236436 1857323 := bstep (se 1 (by rfl) ⟨1392992, by rfl⟩ : syracuseStep 1857323 = 2785985) B2785985
theorem B2086715 : Blo 1236436 2086715 := bstep (se 1 (by rfl) ⟨1565036, by rfl⟩ : syracuseStep 2086715 = 3130073) B3130073
theorem B1857353 : Blo 1236436 1857353 := bstep (se 2 (by rfl) ⟨696507, by rfl⟩ : syracuseStep 1857353 = 1393015) B1393015
theorem B2971511 : Blo 1236436 2971511 := bstep (se 1 (by rfl) ⟨2228633, by rfl⟩ : syracuseStep 2971511 = 4457267) B4457267
theorem B2783123 : Blo 1236436 2783123 := bstep (se 1 (by rfl) ⟨2087342, by rfl⟩ : syracuseStep 2783123 = 4174685) B4174685
theorem B1857467 : Blo 1236436 1857467 := bstep (se 1 (by rfl) ⟨1393100, by rfl⟩ : syracuseStep 1857467 = 2786201) B2786201
theorem B2783177 : Blo 1236436 2783177 := bstep (se 2 (by rfl) ⟨1043691, by rfl⟩ : syracuseStep 2783177 = 2087383) B2087383
theorem B1857527 : Blo 1236436 1857527 := bstep (se 1 (by rfl) ⟨1393145, by rfl⟩ : syracuseStep 1857527 = 2786291) B2786291
theorem B1857551 : Blo 1236436 1857551 := bstep (se 1 (by rfl) ⟨1393163, by rfl⟩ : syracuseStep 1857551 = 2786327) B2786327
theorem B1857593 : Blo 1236436 1857593 := bstep (se 2 (by rfl) ⟨696597, by rfl⟩ : syracuseStep 1857593 = 1393195) B1393195
theorem B4700227 : Blo 1236436 4700227 := bstep (se 1 (by rfl) ⟨3525170, by rfl⟩ : syracuseStep 4700227 = 7050341) B7050341
theorem B3962999 : Blo 1236436 3962999 := bstep (se 1 (by rfl) ⟨2972249, by rfl⟩ : syracuseStep 3962999 = 5944499) B5944499
theorem B3176567 : Blo 1236436 3176567 := bstep (se 1 (by rfl) ⟨2382425, by rfl⟩ : syracuseStep 3176567 = 4764851) B4764851
theorem B1980551 : Blo 1236436 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B6265025 : Blo 1236436 6265025 := bstep (se 2 (by rfl) ⟨2349384, by rfl⟩ : syracuseStep 6265025 = 4698769) B4698769
theorem B2087113 : Blo 1236436 2087113 := bstep (se 2 (by rfl) ⟨782667, by rfl⟩ : syracuseStep 2087113 = 1565335) B1565335
theorem B4176143 : Blo 1236436 4176143 := bstep (se 1 (by rfl) ⟨3132107, by rfl⟩ : syracuseStep 4176143 = 6264215) B6264215
theorem B5945633 : Blo 1236436 5945633 := bstep (se 2 (by rfl) ⟨2229612, by rfl⟩ : syracuseStep 5945633 = 4459225) B4459225
theorem B4700531 : Blo 1236436 4700531 := bstep (se 1 (by rfl) ⟨3525398, by rfl⟩ : syracuseStep 4700531 = 7050797) B7050797
theorem B1391035 : Blo 1236436 1391035 := bstep (se 1 (by rfl) ⟨1043276, by rfl⟩ : syracuseStep 1391035 = 2086553) B2086553
theorem B14088653 : Blo 1236436 14088653 := bstep (se 3 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 14088653 = 5283245) B5283245
theorem B7051799 : Blo 1236436 7051799 := bstep (se 1 (by rfl) ⟨5288849, by rfl⟩ : syracuseStep 7051799 = 10577699) B10577699
theorem B4176413 : Blo 1236436 4176413 := bstep (se 3 (by rfl) ⟨783077, by rfl⟩ : syracuseStep 4176413 = 1566155) B1566155
theorem B8919629 : Blo 1236436 8919629 := bstep (se 3 (by rfl) ⟨1672430, by rfl⟩ : syracuseStep 8919629 = 3344861) B3344861
theorem B2783879 : Blo 1236436 2783879 := bstep (se 1 (by rfl) ⟨2087909, by rfl⟩ : syracuseStep 2783879 = 4175819) B4175819
theorem B2784059 : Blo 1236436 2784059 := bstep (se 1 (by rfl) ⟨2088044, by rfl⟩ : syracuseStep 2784059 = 4176089) B4176089
theorem B4700987 : Blo 1236436 4700987 := bstep (se 1 (by rfl) ⟨3525740, by rfl⟩ : syracuseStep 4700987 = 7051481) B7051481
theorem B2087815 : Blo 1236436 2087815 := bstep (se 1 (by rfl) ⟨1565861, by rfl⟩ : syracuseStep 2087815 = 3131723) B3131723
theorem B1391503 : Blo 1236436 1391503 := bstep (se 1 (by rfl) ⟨1043627, by rfl⟩ : syracuseStep 1391503 = 2087255) B2087255
theorem B2784185 : Blo 1236436 2784185 := bstep (se 2 (by rfl) ⟨1044069, by rfl⟩ : syracuseStep 2784185 = 2088139) B2088139
theorem B2784527 : Blo 1236436 2784527 := bstep (se 1 (by rfl) ⟨2088395, by rfl⟩ : syracuseStep 2784527 = 4176791) B4176791
theorem B2784545 : Blo 1236436 2784545 := bstep (se 2 (by rfl) ⟨1044204, by rfl⟩ : syracuseStep 2784545 = 2088409) B2088409
theorem B4701473 : Blo 1236436 4701473 := bstep (se 2 (by rfl) ⟨1763052, by rfl⟩ : syracuseStep 4701473 = 3526105) B3526105
theorem B7626035 : Blo 1236436 7626035 := bstep (se 1 (by rfl) ⟨5719526, by rfl⟩ : syracuseStep 7626035 = 11439053) B11439053
theorem B33840443 : Blo 1236436 33840443 := bstep (se 1 (by rfl) ⟨25380332, by rfl⟩ : syracuseStep 33840443 = 50760665) B50760665
theorem B1392007 : Blo 1236436 1392007 := bstep (se 1 (by rfl) ⟨1044005, by rfl⟩ : syracuseStep 1392007 = 2088011) B2088011
theorem B2350471 : Blo 1236436 2350471 := bstep (se 1 (by rfl) ⟨1762853, by rfl⟩ : syracuseStep 2350471 = 3525707) B3525707
theorem B6266321 : Blo 1236436 6266321 := bstep (se 2 (by rfl) ⟨2349870, by rfl⟩ : syracuseStep 6266321 = 4699741) B4699741
theorem B1236487 : Blo 1236436 1236487 := bstep (se 1 (by rfl) ⟨927365, by rfl⟩ : syracuseStep 1236487 = 1854731) B1854731
theorem B1236495 : Blo 1236436 1236495 := bstep (se 1 (by rfl) ⟨927371, by rfl⟩ : syracuseStep 1236495 = 1854743) B1854743
theorem B2088463 : Blo 1236436 2088463 := bstep (se 1 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 2088463 = 3132695) B3132695
theorem B1236539 : Blo 1236436 1236539 := bstep (se 1 (by rfl) ⟨927404, by rfl⟩ : syracuseStep 1236539 = 1854809) B1854809
theorem B1392187 : Blo 1236436 1392187 := bstep (se 1 (by rfl) ⟨1044140, by rfl⟩ : syracuseStep 1392187 = 2088281) B2088281
theorem B2784887 : Blo 1236436 2784887 := bstep (se 1 (by rfl) ⟨2088665, by rfl⟩ : syracuseStep 2784887 = 4177331) B4177331
theorem B1236615 : Blo 1236436 1236615 := bstep (se 1 (by rfl) ⟨927461, by rfl⟩ : syracuseStep 1236615 = 1854923) B1854923
theorem B1236623 : Blo 1236436 1236623 := bstep (se 1 (by rfl) ⟨927467, by rfl⟩ : syracuseStep 1236623 = 1854935) B1854935
theorem B3219097 : Blo 1236436 3219097 := bstep (se 2 (by rfl) ⟨1207161, by rfl⟩ : syracuseStep 3219097 = 2414323) B2414323
theorem B1236667 : Blo 1236436 1236667 := bstep (se 1 (by rfl) ⟨927500, by rfl⟩ : syracuseStep 1236667 = 1855001) B1855001
theorem B9043649 : Blo 1236436 9043649 := bstep (se 2 (by rfl) ⟨3391368, by rfl⟩ : syracuseStep 9043649 = 6782737) B6782737
theorem B1236743 : Blo 1236436 1236743 := bstep (se 1 (by rfl) ⟨927557, by rfl⟩ : syracuseStep 1236743 = 1855115) B1855115
theorem B1761031 : Blo 1236436 1761031 := bstep (se 1 (by rfl) ⟨1320773, by rfl⟩ : syracuseStep 1761031 = 2641547) B2641547
theorem B1236751 : Blo 1236436 1236751 := bstep (se 1 (by rfl) ⟨927563, by rfl⟩ : syracuseStep 1236751 = 1855127) B1855127
theorem B2785067 : Blo 1236436 2785067 := bstep (se 1 (by rfl) ⟨2088800, by rfl⟩ : syracuseStep 2785067 = 4177601) B4177601
theorem B1236795 : Blo 1236436 1236795 := bstep (se 1 (by rfl) ⟨927596, by rfl⟩ : syracuseStep 1236795 = 1855193) B1855193
theorem B1236871 : Blo 1236436 1236871 := bstep (se 1 (by rfl) ⟨927653, by rfl⟩ : syracuseStep 1236871 = 1855307) B1855307
theorem B1236879 : Blo 1236436 1236879 := bstep (se 1 (by rfl) ⟨927659, by rfl⟩ : syracuseStep 1236879 = 1855319) B1855319
theorem B4177817 : Blo 1236436 4177817 := bstep (se 2 (by rfl) ⟨1566681, by rfl⟩ : syracuseStep 4177817 = 3133363) B3133363
theorem B1236923 : Blo 1236436 1236923 := bstep (se 1 (by rfl) ⟨927692, by rfl⟩ : syracuseStep 1236923 = 1855385) B1855385
theorem B1507259 : Blo 1236436 1507259 := bstep (se 1 (by rfl) ⟨1130444, by rfl⟩ : syracuseStep 1507259 = 2260889) B2260889
theorem B13369373 : Blo 1236436 13369373 := bstep (se 3 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 13369373 = 5013515) B5013515
theorem B1237031 : Blo 1236436 1237031 := bstep (se 1 (by rfl) ⟨927773, by rfl⟩ : syracuseStep 1237031 = 1855547) B1855547
theorem B77299757 : Blo 1236436 77299757 := bstep (se 3 (by rfl) ⟨14493704, by rfl⟩ : syracuseStep 77299757 = 28987409) B28987409
theorem B2785337 : Blo 1236436 2785337 := bstep (se 2 (by rfl) ⟨1044501, by rfl⟩ : syracuseStep 2785337 = 2089003) B2089003
theorem B1237071 : Blo 1236436 1237071 := bstep (se 1 (by rfl) ⟨927803, by rfl⟩ : syracuseStep 1237071 = 1855607) B1855607
theorem B4456529 : Blo 1236436 4456529 := bstep (se 2 (by rfl) ⟨1671198, by rfl⟩ : syracuseStep 4456529 = 3342397) B3342397
theorem B6266969 : Blo 1236436 6266969 := bstep (se 2 (by rfl) ⟨2350113, by rfl⟩ : syracuseStep 6266969 = 4700227) B4700227
theorem B1237087 : Blo 1236436 1237087 := bstep (se 1 (by rfl) ⟨927815, by rfl⟩ : syracuseStep 1237087 = 1855631) B1855631
theorem B7929971 : Blo 1236436 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B1237115 : Blo 1236436 1237115 := bstep (se 1 (by rfl) ⟨927836, by rfl⟩ : syracuseStep 1237115 = 1855673) B1855673
theorem B1392763 : Blo 1236436 1392763 := bstep (se 1 (by rfl) ⟨1044572, by rfl⟩ : syracuseStep 1392763 = 2089145) B2089145
theorem B1237167 : Blo 1236436 1237167 := bstep (se 1 (by rfl) ⟨927875, by rfl⟩ : syracuseStep 1237167 = 1855751) B1855751
theorem B1237191 : Blo 1236436 1237191 := bstep (se 1 (by rfl) ⟨927893, by rfl⟩ : syracuseStep 1237191 = 1855787) B1855787
theorem B1237211 : Blo 1236436 1237211 := bstep (se 1 (by rfl) ⟨927908, by rfl⟩ : syracuseStep 1237211 = 1855817) B1855817
theorem B36143333 : Blo 1236436 36143333 := bstep (se 4 (by rfl) ⟨3388437, by rfl⟩ : syracuseStep 36143333 = 6776875) B6776875
theorem B1237287 : Blo 1236436 1237287 := bstep (se 1 (by rfl) ⟨927965, by rfl⟩ : syracuseStep 1237287 = 1855931) B1855931
theorem B1237327 : Blo 1236436 1237327 := bstep (se 1 (by rfl) ⟨927995, by rfl⟩ : syracuseStep 1237327 = 1855991) B1855991
theorem B7930199 : Blo 1236436 7930199 := bstep (se 1 (by rfl) ⟨5947649, by rfl⟩ : syracuseStep 7930199 = 11895299) B11895299
theorem B1237343 : Blo 1236436 1237343 := bstep (se 1 (by rfl) ⟨928007, by rfl⟩ : syracuseStep 1237343 = 1856015) B1856015
theorem B1237371 : Blo 1236436 1237371 := bstep (se 1 (by rfl) ⟨928028, by rfl⟩ : syracuseStep 1237371 = 1856057) B1856057
theorem B2785679 : Blo 1236436 2785679 := bstep (se 1 (by rfl) ⟨2089259, by rfl⟩ : syracuseStep 2785679 = 4178519) B4178519
theorem B1237423 : Blo 1236436 1237423 := bstep (se 1 (by rfl) ⟨928067, by rfl⟩ : syracuseStep 1237423 = 1856135) B1856135
theorem B1237447 : Blo 1236436 1237447 := bstep (se 1 (by rfl) ⟨928085, by rfl⟩ : syracuseStep 1237447 = 1856171) B1856171
theorem B1237467 : Blo 1236436 1237467 := bstep (se 1 (by rfl) ⟨928100, by rfl⟩ : syracuseStep 1237467 = 1856201) B1856201
theorem B2089435 : Blo 1236436 2089435 := bstep (se 1 (by rfl) ⟨1567076, by rfl⟩ : syracuseStep 2089435 = 3134153) B3134153
theorem B2228755 : Blo 1236436 2228755 := bstep (se 1 (by rfl) ⟨1671566, by rfl⟩ : syracuseStep 2228755 = 3343133) B3343133
theorem B4178465 : Blo 1236436 4178465 := bstep (se 2 (by rfl) ⟨1566924, by rfl⟩ : syracuseStep 4178465 = 3133849) B3133849
theorem B1237543 : Blo 1236436 1237543 := bstep (se 1 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 1237543 = 1856315) B1856315
theorem B1237583 : Blo 1236436 1237583 := bstep (se 1 (by rfl) ⟨928187, by rfl⟩ : syracuseStep 1237583 = 1856375) B1856375
theorem B1393231 : Blo 1236436 1393231 := bstep (se 1 (by rfl) ⟨1044923, by rfl⟩ : syracuseStep 1393231 = 2089847) B2089847
theorem B1237599 : Blo 1236436 1237599 := bstep (se 1 (by rfl) ⟨928199, by rfl⟩ : syracuseStep 1237599 = 1856399) B1856399
theorem B3965537 : Blo 1236436 3965537 := bstep (se 2 (by rfl) ⟨1487076, by rfl⟩ : syracuseStep 3965537 = 2974153) B2974153
theorem B1237627 : Blo 1236436 1237627 := bstep (se 1 (by rfl) ⟨928220, by rfl⟩ : syracuseStep 1237627 = 1856441) B1856441
theorem B1237679 : Blo 1236436 1237679 := bstep (se 1 (by rfl) ⟨928259, by rfl⟩ : syracuseStep 1237679 = 1856519) B1856519
theorem B1237703 : Blo 1236436 1237703 := bstep (se 1 (by rfl) ⟨928277, by rfl⟩ : syracuseStep 1237703 = 1856555) B1856555
theorem B3572435 : Blo 1236436 3572435 := bstep (se 1 (by rfl) ⟨2679326, by rfl⟩ : syracuseStep 3572435 = 5358653) B5358653
theorem B2786003 : Blo 1236436 2786003 := bstep (se 1 (by rfl) ⟨2089502, by rfl⟩ : syracuseStep 2786003 = 4179005) B4179005
theorem B1237723 : Blo 1236436 1237723 := bstep (se 1 (by rfl) ⟨928292, by rfl⟩ : syracuseStep 1237723 = 1856585) B1856585
theorem B4178681 : Blo 1236436 4178681 := bstep (se 2 (by rfl) ⟨1567005, by rfl⟩ : syracuseStep 4178681 = 3134011) B3134011
theorem B1237799 : Blo 1236436 1237799 := bstep (se 1 (by rfl) ⟨928349, by rfl⟩ : syracuseStep 1237799 = 1856699) B1856699
theorem B1237839 : Blo 1236436 1237839 := bstep (se 1 (by rfl) ⟨928379, by rfl⟩ : syracuseStep 1237839 = 1856759) B1856759
theorem B1237855 : Blo 1236436 1237855 := bstep (se 1 (by rfl) ⟨928391, by rfl⟩ : syracuseStep 1237855 = 1856783) B1856783
theorem B1237883 : Blo 1236436 1237883 := bstep (se 1 (by rfl) ⟨928412, by rfl⟩ : syracuseStep 1237883 = 1856825) B1856825
theorem B1237935 : Blo 1236436 1237935 := bstep (se 1 (by rfl) ⟨928451, by rfl⟩ : syracuseStep 1237935 = 1856903) B1856903
theorem B1237959 : Blo 1236436 1237959 := bstep (se 1 (by rfl) ⟨928469, by rfl⟩ : syracuseStep 1237959 = 1856939) B1856939
theorem B1565659 : Blo 1236436 1565659 := bstep (se 1 (by rfl) ⟨1174244, by rfl⟩ : syracuseStep 1565659 = 2348489) B2348489
theorem B1237979 : Blo 1236436 1237979 := bstep (se 1 (by rfl) ⟨928484, by rfl⟩ : syracuseStep 1237979 = 1856969) B1856969
theorem B4178951 : Blo 1236436 4178951 := bstep (se 1 (by rfl) ⟨3134213, by rfl⟩ : syracuseStep 4178951 = 6268427) B6268427
theorem B1238055 : Blo 1236436 1238055 := bstep (se 1 (by rfl) ⟨928541, by rfl⟩ : syracuseStep 1238055 = 1857083) B1857083
theorem B3130447 : Blo 1236436 3130447 := bstep (se 1 (by rfl) ⟨2347835, by rfl⟩ : syracuseStep 3130447 = 4695671) B4695671
theorem B1238095 : Blo 1236436 1238095 := bstep (se 1 (by rfl) ⟨928571, by rfl⟩ : syracuseStep 1238095 = 1857143) B1857143
theorem B1238111 : Blo 1236436 1238111 := bstep (se 1 (by rfl) ⟨928583, by rfl⟩ : syracuseStep 1238111 = 1857167) B1857167
theorem B4695155 : Blo 1236436 4695155 := bstep (se 1 (by rfl) ⟨3521366, by rfl⟩ : syracuseStep 4695155 = 7042733) B7042733
theorem B4179059 : Blo 1236436 4179059 := bstep (se 1 (by rfl) ⟨3134294, by rfl⟩ : syracuseStep 4179059 = 6268589) B6268589
theorem B1238139 : Blo 1236436 1238139 := bstep (se 1 (by rfl) ⟨928604, by rfl⟩ : syracuseStep 1238139 = 1857209) B1857209
theorem B1238191 : Blo 1236436 1238191 := bstep (se 1 (by rfl) ⟨928643, by rfl⟩ : syracuseStep 1238191 = 1857287) B1857287
theorem B1238215 : Blo 1236436 1238215 := bstep (se 1 (by rfl) ⟨928661, by rfl⟩ : syracuseStep 1238215 = 1857323) B1857323
theorem B1238235 : Blo 1236436 1238235 := bstep (se 1 (by rfl) ⟨928676, by rfl⟩ : syracuseStep 1238235 = 1857353) B1857353
theorem B7046423 : Blo 1236436 7046423 := bstep (se 1 (by rfl) ⟨5284817, by rfl⟩ : syracuseStep 7046423 = 10569635) B10569635
theorem B1238311 : Blo 1236436 1238311 := bstep (se 1 (by rfl) ⟨928733, by rfl⟩ : syracuseStep 1238311 = 1857467) B1857467
theorem B1238351 : Blo 1236436 1238351 := bstep (se 1 (by rfl) ⟨928763, by rfl⟩ : syracuseStep 1238351 = 1857527) B1857527
theorem B1238367 : Blo 1236436 1238367 := bstep (se 1 (by rfl) ⟨928775, by rfl⟩ : syracuseStep 1238367 = 1857551) B1857551
theorem B1238395 : Blo 1236436 1238395 := bstep (se 1 (by rfl) ⟨928796, by rfl⟩ : syracuseStep 1238395 = 1857593) B1857593
theorem B4179329 : Blo 1236436 4179329 := bstep (se 2 (by rfl) ⟨1567248, by rfl⟩ : syracuseStep 4179329 = 3134497) B3134497
theorem B2508193 : Blo 1236436 2508193 := bstep (se 2 (by rfl) ⟨940572, by rfl⟩ : syracuseStep 2508193 = 1881145) B1881145
theorem B35661221 : Blo 1236436 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B1762825 : Blo 1236436 1762825 := bstep (se 2 (by rfl) ⟨661059, by rfl⟩ : syracuseStep 1762825 = 1322119) B1322119
theorem B15042145 : Blo 1236436 15042145 := bstep (se 2 (by rfl) ⟨5640804, by rfl⟩ : syracuseStep 15042145 = 11281609) B11281609
theorem B3131095 : Blo 1236436 3131095 := bstep (se 1 (by rfl) ⟨2348321, by rfl⟩ : syracuseStep 3131095 = 4696643) B4696643
theorem B3131399 : Blo 1236436 3131399 := bstep (se 1 (by rfl) ⟨2348549, by rfl⟩ : syracuseStep 3131399 = 4697099) B4697099
theorem B32139665 : Blo 1236436 32139665 := bstep (se 2 (by rfl) ⟨12052374, by rfl⟩ : syracuseStep 32139665 = 24104749) B24104749
theorem B30083507 : Blo 1236436 30083507 := bstep (se 1 (by rfl) ⟨22562630, by rfl⟩ : syracuseStep 30083507 = 45125261) B45125261
theorem B2230715 : Blo 1236436 2230715 := bstep (se 1 (by rfl) ⟨1673036, by rfl⟩ : syracuseStep 2230715 = 3346073) B3346073
theorem B4696825 : Blo 1236436 4696825 := bstep (se 2 (by rfl) ⟨1761309, by rfl⟩ : syracuseStep 4696825 = 3522619) B3522619
theorem B5647211 : Blo 1236436 5647211 := bstep (se 1 (by rfl) ⟨4235408, by rfl⟩ : syracuseStep 5647211 = 8470817) B8470817
theorem B60173239 : Blo 1236436 60173239 := bstep (se 1 (by rfl) ⟨45129929, by rfl⟩ : syracuseStep 60173239 = 90259859) B90259859
theorem B23506037 : Blo 1236436 23506037 := bstep (se 5 (by rfl) ⟨1101845, by rfl⟩ : syracuseStep 23506037 = 2203691) B2203691
theorem B1854713 : Blo 1236436 1854713 := bstep (se 2 (by rfl) ⟨695517, by rfl⟩ : syracuseStep 1854713 = 1391035) B1391035
theorem B1854815 : Blo 1236436 1854815 := bstep (se 1 (by rfl) ⟨1391111, by rfl⟩ : syracuseStep 1854815 = 2782223) B2782223
theorem B5016937 : Blo 1236436 5016937 := bstep (se 2 (by rfl) ⟨1881351, by rfl⟩ : syracuseStep 5016937 = 3762703) B3762703
theorem B1854827 : Blo 1236436 1854827 := bstep (se 1 (by rfl) ⟨1391120, by rfl⟩ : syracuseStep 1854827 = 2782241) B2782241
theorem B16944527 : Blo 1236436 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B2231695 : Blo 1236436 2231695 := bstep (se 1 (by rfl) ⟨1673771, by rfl⟩ : syracuseStep 2231695 = 3347543) B3347543
theorem B6688165 : Blo 1236436 6688165 := bstep (se 4 (by rfl) ⟨627015, by rfl⟩ : syracuseStep 6688165 = 1254031) B1254031
theorem B9399725 : Blo 1236436 9399725 := bstep (se 3 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 9399725 = 3524897) B3524897
theorem B1486255 : Blo 1236436 1486255 := bstep (se 1 (by rfl) ⟨1114691, by rfl⟩ : syracuseStep 1486255 = 2229383) B2229383
theorem B5942729 : Blo 1236436 5942729 := bstep (se 2 (by rfl) ⟨2228523, by rfl⟩ : syracuseStep 5942729 = 4457047) B4457047
theorem B20336093 : Blo 1236436 20336093 := bstep (se 3 (by rfl) ⟨3813017, by rfl⟩ : syracuseStep 20336093 = 7626035) B7626035
theorem B1855055 : Blo 1236436 1855055 := bstep (se 1 (by rfl) ⟨1391291, by rfl⟩ : syracuseStep 1855055 = 2782583) B2782583
theorem B8040059 : Blo 1236436 8040059 := bstep (se 1 (by rfl) ⟨6030044, by rfl⟩ : syracuseStep 8040059 = 12060089) B12060089
theorem B4173497 : Blo 1236436 4173497 := bstep (se 2 (by rfl) ⟨1565061, by rfl⟩ : syracuseStep 4173497 = 3130123) B3130123
theorem B1855175 : Blo 1236436 1855175 := bstep (se 1 (by rfl) ⟨1391381, by rfl⟩ : syracuseStep 1855175 = 2782763) B2782763
theorem B3526355 : Blo 1236436 3526355 := bstep (se 1 (by rfl) ⟨2644766, by rfl⟩ : syracuseStep 3526355 = 5289533) B5289533
theorem B6262595 : Blo 1236436 6262595 := bstep (se 1 (by rfl) ⟨4696946, by rfl⟩ : syracuseStep 6262595 = 9393893) B9393893
theorem B1855337 : Blo 1236436 1855337 := bstep (se 2 (by rfl) ⟨695751, by rfl⟩ : syracuseStep 1855337 = 1391503) B1391503
theorem B5648237 : Blo 1236436 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B20074355 : Blo 1236436 20074355 := bstep (se 1 (by rfl) ⟨15055766, by rfl⟩ : syracuseStep 20074355 = 30111533) B30111533
theorem B1855415 : Blo 1236436 1855415 := bstep (se 1 (by rfl) ⟨1391561, by rfl⟩ : syracuseStep 1855415 = 2783123) B2783123
theorem B7933889 : Blo 1236436 7933889 := bstep (se 2 (by rfl) ⟨2975208, by rfl⟩ : syracuseStep 7933889 = 5950417) B5950417
theorem B1855451 : Blo 1236436 1855451 := bstep (se 1 (by rfl) ⟨1391588, by rfl⟩ : syracuseStep 1855451 = 2783177) B2783177
theorem B2641999 : Blo 1236436 2641999 := bstep (se 1 (by rfl) ⟨1981499, by rfl⟩ : syracuseStep 2641999 = 3962999) B3962999
theorem B2117711 : Blo 1236436 2117711 := bstep (se 1 (by rfl) ⟨1588283, by rfl⟩ : syracuseStep 2117711 = 3176567) B3176567
theorem B4698269 : Blo 1236436 4698269 := bstep (se 3 (by rfl) ⟨880925, by rfl⟩ : syracuseStep 4698269 = 1761851) B1761851
theorem B4698283 : Blo 1236436 4698283 := bstep (se 1 (by rfl) ⟨3523712, by rfl⟩ : syracuseStep 4698283 = 7047425) B7047425
theorem B1880263 : Blo 1236436 1880263 := bstep (se 1 (by rfl) ⟨1410197, by rfl⟩ : syracuseStep 1880263 = 2820395) B2820395
theorem B3133687 : Blo 1236436 3133687 := bstep (se 1 (by rfl) ⟨2350265, by rfl⟩ : syracuseStep 3133687 = 4700531) B4700531
theorem B4174091 : Blo 1236436 4174091 := bstep (se 1 (by rfl) ⟨3130568, by rfl⟩ : syracuseStep 4174091 = 6261137) B6261137
theorem B9392435 : Blo 1236436 9392435 := bstep (se 1 (by rfl) ⟨7044326, by rfl⟩ : syracuseStep 9392435 = 14088653) B14088653
theorem B1855919 : Blo 1236436 1855919 := bstep (se 1 (by rfl) ⟨1391939, by rfl⟩ : syracuseStep 1855919 = 2783879) B2783879
theorem B3961307 : Blo 1236436 3961307 := bstep (se 1 (by rfl) ⟨2970980, by rfl⟩ : syracuseStep 3961307 = 5941961) B5941961
theorem B4698587 : Blo 1236436 4698587 := bstep (se 1 (by rfl) ⟨3523940, by rfl⟩ : syracuseStep 4698587 = 7047881) B7047881
theorem B7926281 : Blo 1236436 7926281 := bstep (se 2 (by rfl) ⟨2972355, by rfl⟩ : syracuseStep 7926281 = 5944711) B5944711
theorem B1856009 : Blo 1236436 1856009 := bstep (se 2 (by rfl) ⟨696003, by rfl⟩ : syracuseStep 1856009 = 1392007) B1392007
theorem B3133961 : Blo 1236436 3133961 := bstep (se 2 (by rfl) ⟨1175235, by rfl⟩ : syracuseStep 3133961 = 2350471) B2350471
theorem B4174361 : Blo 1236436 4174361 := bstep (se 2 (by rfl) ⟨1565385, by rfl⟩ : syracuseStep 4174361 = 3130771) B3130771
theorem B1856039 : Blo 1236436 1856039 := bstep (se 1 (by rfl) ⟨1392029, by rfl⟩ : syracuseStep 1856039 = 2784059) B2784059
theorem B3133991 : Blo 1236436 3133991 := bstep (se 1 (by rfl) ⟨2350493, by rfl⟩ : syracuseStep 3133991 = 4700987) B4700987
theorem B1856123 : Blo 1236436 1856123 := bstep (se 1 (by rfl) ⟨1392092, by rfl⟩ : syracuseStep 1856123 = 2784185) B2784185
theorem B7926407 : Blo 1236436 7926407 := bstep (se 1 (by rfl) ⟨5944805, by rfl⟩ : syracuseStep 7926407 = 11889611) B11889611
theorem B4289213 : Blo 1236436 4289213 := bstep (se 3 (by rfl) ⟨804227, by rfl⟩ : syracuseStep 4289213 = 1608455) B1608455
theorem B10711763 : Blo 1236436 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B1856249 : Blo 1236436 1856249 := bstep (se 2 (by rfl) ⟨696093, by rfl⟩ : syracuseStep 1856249 = 1392187) B1392187
theorem B2782025 : Blo 1236436 2782025 := bstep (se 2 (by rfl) ⟨1043259, by rfl⟩ : syracuseStep 2782025 = 2086519) B2086519
theorem B1856351 : Blo 1236436 1856351 := bstep (se 1 (by rfl) ⟨1392263, by rfl⟩ : syracuseStep 1856351 = 2784527) B2784527
theorem B1856363 : Blo 1236436 1856363 := bstep (se 1 (by rfl) ⟨1392272, by rfl⟩ : syracuseStep 1856363 = 2784545) B2784545
theorem B3134315 : Blo 1236436 3134315 := bstep (se 1 (by rfl) ⟨2350736, by rfl⟩ : syracuseStep 3134315 = 4701473) B4701473
theorem B7042049 : Blo 1236436 7042049 := bstep (se 2 (by rfl) ⟨2640768, by rfl⟩ : syracuseStep 7042049 = 5281537) B5281537
theorem B2348041 : Blo 1236436 2348041 := bstep (se 2 (by rfl) ⟨880515, by rfl⟩ : syracuseStep 2348041 = 1761031) B1761031
theorem B4232249 : Blo 1236436 4232249 := bstep (se 2 (by rfl) ⟨1587093, by rfl⟩ : syracuseStep 4232249 = 3174187) B3174187
theorem B1856591 : Blo 1236436 1856591 := bstep (se 1 (by rfl) ⟨1392443, by rfl⟩ : syracuseStep 1856591 = 2784887) B2784887
theorem B5018705 : Blo 1236436 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B4019357 : Blo 1236436 4019357 := bstep (se 3 (by rfl) ⟨753629, by rfl⟩ : syracuseStep 4019357 = 1507259) B1507259
theorem B1856711 : Blo 1236436 1856711 := bstep (se 1 (by rfl) ⟨1392533, by rfl⟩ : syracuseStep 1856711 = 2785067) B2785067
theorem B1856873 : Blo 1236436 1856873 := bstep (se 2 (by rfl) ⟨696327, by rfl⟩ : syracuseStep 1856873 = 1392655) B1392655
theorem B54285713 : Blo 1236436 54285713 := bstep (se 2 (by rfl) ⟨20357142, by rfl⟩ : syracuseStep 54285713 = 40714285) B40714285
theorem B1856951 : Blo 1236436 1856951 := bstep (se 1 (by rfl) ⟨1392713, by rfl⟩ : syracuseStep 1856951 = 2785427) B2785427
theorem B1856987 : Blo 1236436 1856987 := bstep (se 1 (by rfl) ⟨1392740, by rfl⟩ : syracuseStep 1856987 = 2785481) B2785481
theorem B7927307 : Blo 1236436 7927307 := bstep (se 1 (by rfl) ⟨5945480, by rfl⟩ : syracuseStep 7927307 = 11890961) B11890961
theorem B2782817 : Blo 1236436 2782817 := bstep (se 2 (by rfl) ⟨1043556, by rfl⟩ : syracuseStep 2782817 = 2087113) B2087113
theorem B5289569 : Blo 1236436 5289569 := bstep (se 2 (by rfl) ⟨1983588, by rfl⟩ : syracuseStep 5289569 = 3967177) B3967177
theorem B4175495 : Blo 1236436 4175495 := bstep (se 1 (by rfl) ⟨3131621, by rfl⟩ : syracuseStep 4175495 = 6263243) B6263243
theorem B5281469 : Blo 1236436 5281469 := bstep (se 3 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 5281469 = 1980551) B1980551
theorem B4175549 : Blo 1236436 4175549 := bstep (se 3 (by rfl) ⟨782915, by rfl⟩ : syracuseStep 4175549 = 1565831) B1565831
theorem B9402155 : Blo 1236436 9402155 := bstep (se 1 (by rfl) ⟨7051616, by rfl⟩ : syracuseStep 9402155 = 14103233) B14103233
theorem B4175711 : Blo 1236436 4175711 := bstep (se 1 (by rfl) ⟨3131783, by rfl⟩ : syracuseStep 4175711 = 6263567) B6263567
theorem B5019499 : Blo 1236436 5019499 := bstep (se 1 (by rfl) ⟨3764624, by rfl⟩ : syracuseStep 5019499 = 7529249) B7529249
theorem B2348975 : Blo 1236436 2348975 := bstep (se 1 (by rfl) ⟨1761731, by rfl⟩ : syracuseStep 2348975 = 3523463) B3523463
theorem B1857455 : Blo 1236436 1857455 := bstep (se 1 (by rfl) ⟨1393091, by rfl⟩ : syracuseStep 1857455 = 2786183) B2786183
theorem B2783159 : Blo 1236436 2783159 := bstep (se 1 (by rfl) ⟨2087369, by rfl⟩ : syracuseStep 2783159 = 4174739) B4174739
theorem B2086843 : Blo 1236436 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B7927739 : Blo 1236436 7927739 := bstep (se 1 (by rfl) ⟨5945804, by rfl⟩ : syracuseStep 7927739 = 11891609) B11891609
theorem B4175873 : Blo 1236436 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B10565639 : Blo 1236436 10565639 := bstep (se 1 (by rfl) ⟨7924229, by rfl⟩ : syracuseStep 10565639 = 15848459) B15848459
theorem B1857545 : Blo 1236436 1857545 := bstep (se 2 (by rfl) ⟨696579, by rfl⟩ : syracuseStep 1857545 = 1393159) B1393159
theorem B2086951 : Blo 1236436 2086951 := bstep (se 1 (by rfl) ⟨1565213, by rfl⟩ : syracuseStep 2086951 = 3130427) B3130427
theorem B1857575 : Blo 1236436 1857575 := bstep (se 1 (by rfl) ⟨1393181, by rfl⟩ : syracuseStep 1857575 = 2786363) B2786363
theorem B16939165 : Blo 1236436 16939165 := bstep (se 3 (by rfl) ⟨3176093, by rfl⟩ : syracuseStep 16939165 = 6352187) B6352187
theorem B1882361 : Blo 1236436 1882361 := bstep (se 2 (by rfl) ⟨705885, by rfl⟩ : syracuseStep 1882361 = 1411771) B1411771
theorem B4233559 : Blo 1236436 4233559 := bstep (se 1 (by rfl) ⟨3175169, by rfl⟩ : syracuseStep 4233559 = 6350339) B6350339
theorem B2087275 : Blo 1236436 2087275 := bstep (se 1 (by rfl) ⟨1565456, by rfl⟩ : syracuseStep 2087275 = 3130913) B3130913
theorem B2349499 : Blo 1236436 2349499 := bstep (se 1 (by rfl) ⟨1762124, by rfl⟩ : syracuseStep 2349499 = 3524249) B3524249
theorem B2783753 : Blo 1236436 2783753 := bstep (se 2 (by rfl) ⟨1043907, by rfl⟩ : syracuseStep 2783753 = 2087815) B2087815
theorem B1391143 : Blo 1236436 1391143 := bstep (se 1 (by rfl) ⟨1043357, by rfl⟩ : syracuseStep 1391143 = 2086715) B2086715
theorem B1981007 : Blo 1236436 1981007 := bstep (se 1 (by rfl) ⟨1485755, by rfl⟩ : syracuseStep 1981007 = 2971511) B2971511
theorem B5085881 : Blo 1236436 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B4176683 : Blo 1236436 4176683 := bstep (se 1 (by rfl) ⟨3132512, by rfl⟩ : syracuseStep 4176683 = 6265025) B6265025
theorem B6265673 : Blo 1236436 6265673 := bstep (se 2 (by rfl) ⟨2349627, by rfl⟩ : syracuseStep 6265673 = 4699255) B4699255
theorem B2784095 : Blo 1236436 2784095 := bstep (se 1 (by rfl) ⟨2088071, by rfl⟩ : syracuseStep 2784095 = 4176143) B4176143
theorem B3963755 : Blo 1236436 3963755 := bstep (se 1 (by rfl) ⟨2972816, by rfl⟩ : syracuseStep 3963755 = 5945633) B5945633
theorem B2349985 : Blo 1236436 2349985 := bstep (se 2 (by rfl) ⟨881244, by rfl⟩ : syracuseStep 2349985 = 1762489) B1762489
theorem B4701185 : Blo 1236436 4701185 := bstep (se 2 (by rfl) ⟨1762944, by rfl⟩ : syracuseStep 4701185 = 3525889) B3525889
theorem B4701199 : Blo 1236436 4701199 := bstep (se 1 (by rfl) ⟨3525899, by rfl⟩ : syracuseStep 4701199 = 7051799) B7051799
theorem B2784275 : Blo 1236436 2784275 := bstep (se 1 (by rfl) ⟨2088206, by rfl⟩ : syracuseStep 2784275 = 4176413) B4176413
theorem B5946419 : Blo 1236436 5946419 := bstep (se 1 (by rfl) ⟨4459814, by rfl⟩ : syracuseStep 5946419 = 8919629) B8919629
theorem B4176953 : Blo 1236436 4176953 := bstep (se 2 (by rfl) ⟨1566357, by rfl⟩ : syracuseStep 4176953 = 3132715) B3132715
theorem B34331921 : Blo 1236436 34331921 := bstep (se 2 (by rfl) ⟨12874470, by rfl⟩ : syracuseStep 34331921 = 25748941) B25748941
theorem B2784617 : Blo 1236436 2784617 := bstep (se 2 (by rfl) ⟨1044231, by rfl⟩ : syracuseStep 2784617 = 2088463) B2088463
theorem B10567037 : Blo 1236436 10567037 := bstep (se 3 (by rfl) ⟨1981319, by rfl⟩ : syracuseStep 10567037 = 3962639) B3962639
theorem B4177277 : Blo 1236436 4177277 := bstep (se 3 (by rfl) ⟨783239, by rfl⟩ : syracuseStep 4177277 = 1566479) B1566479
theorem B2088335 : Blo 1236436 2088335 := bstep (se 1 (by rfl) ⟨1566251, by rfl⟩ : syracuseStep 2088335 = 3132503) B3132503
theorem B1236443 : Blo 1236436 1236443 := bstep (se 1 (by rfl) ⟨927332, by rfl⟩ : syracuseStep 1236443 = 1854665) B1854665
theorem B4292129 : Blo 1236436 4292129 := bstep (se 2 (by rfl) ⟨1609548, by rfl⟩ : syracuseStep 4292129 = 3219097) B3219097
theorem B22560295 : Blo 1236436 22560295 := bstep (se 1 (by rfl) ⟨16920221, by rfl⟩ : syracuseStep 22560295 = 33840443) B33840443
theorem B1236519 : Blo 1236436 1236519 := bstep (se 1 (by rfl) ⟨927389, by rfl⟩ : syracuseStep 1236519 = 1854779) B1854779
theorem B1236559 : Blo 1236436 1236559 := bstep (se 1 (by rfl) ⟨927419, by rfl⟩ : syracuseStep 1236559 = 1854839) B1854839
theorem B1236575 : Blo 1236436 1236575 := bstep (se 1 (by rfl) ⟨927431, by rfl⟩ : syracuseStep 1236575 = 1854863) B1854863
theorem B1236603 : Blo 1236436 1236603 := bstep (se 1 (by rfl) ⟨927452, by rfl⟩ : syracuseStep 1236603 = 1854905) B1854905
theorem B2973307 : Blo 1236436 2973307 := bstep (se 1 (by rfl) ⟨2229980, by rfl⟩ : syracuseStep 2973307 = 4459961) B4459961
theorem B2088571 : Blo 1236436 2088571 := bstep (se 1 (by rfl) ⟨1566428, by rfl⟩ : syracuseStep 2088571 = 3132857) B3132857
theorem B4177547 : Blo 1236436 4177547 := bstep (se 1 (by rfl) ⟨3133160, by rfl⟩ : syracuseStep 4177547 = 6266321) B6266321
theorem B7052939 : Blo 1236436 7052939 := bstep (se 1 (by rfl) ⟨5289704, by rfl⟩ : syracuseStep 7052939 = 10579409) B10579409
theorem B1236655 : Blo 1236436 1236655 := bstep (se 1 (by rfl) ⟨927491, by rfl⟩ : syracuseStep 1236655 = 1854983) B1854983
theorem B1236679 : Blo 1236436 1236679 := bstep (se 1 (by rfl) ⟨927509, by rfl⟩ : syracuseStep 1236679 = 1855019) B1855019
theorem B1236699 : Blo 1236436 1236699 := bstep (se 1 (by rfl) ⟨927524, by rfl⟩ : syracuseStep 1236699 = 1855049) B1855049
theorem B1236775 : Blo 1236436 1236775 := bstep (se 1 (by rfl) ⟨927581, by rfl⟩ : syracuseStep 1236775 = 1855163) B1855163
theorem B6029099 : Blo 1236436 6029099 := bstep (se 1 (by rfl) ⟨4521824, by rfl⟩ : syracuseStep 6029099 = 9043649) B9043649
theorem B1236815 : Blo 1236436 1236815 := bstep (se 1 (by rfl) ⟨927611, by rfl⟩ : syracuseStep 1236815 = 1855223) B1855223
theorem B1236831 : Blo 1236436 1236831 := bstep (se 1 (by rfl) ⟨927623, by rfl⟩ : syracuseStep 1236831 = 1855247) B1855247
theorem B1236859 : Blo 1236436 1236859 := bstep (se 1 (by rfl) ⟨927644, by rfl⟩ : syracuseStep 1236859 = 1855289) B1855289
theorem B1236911 : Blo 1236436 1236911 := bstep (se 1 (by rfl) ⟨927683, by rfl⟩ : syracuseStep 1236911 = 1855367) B1855367
theorem B2785211 : Blo 1236436 2785211 := bstep (se 1 (by rfl) ⟨2088908, by rfl⟩ : syracuseStep 2785211 = 4177817) B4177817
theorem B1236935 : Blo 1236436 1236935 := bstep (se 1 (by rfl) ⟨927701, by rfl⟩ : syracuseStep 1236935 = 1855403) B1855403
theorem B1236955 : Blo 1236436 1236955 := bstep (se 1 (by rfl) ⟨927716, by rfl⟩ : syracuseStep 1236955 = 1855433) B1855433
theorem B8912915 : Blo 1236436 8912915 := bstep (se 1 (by rfl) ⟨6684686, by rfl⟩ : syracuseStep 8912915 = 13369373) B13369373
theorem B4177979 : Blo 1236436 4177979 := bstep (se 1 (by rfl) ⟨3133484, by rfl⟩ : syracuseStep 4177979 = 6266969) B6266969
theorem B3522665 : Blo 1236436 3522665 := bstep (se 2 (by rfl) ⟨1320999, by rfl⟩ : syracuseStep 3522665 = 2641999) B2641999
theorem B22585553 : Blo 1236436 22585553 := bstep (se 2 (by rfl) ⟨8469582, by rfl⟩ : syracuseStep 22585553 = 16939165) B16939165
theorem B1237279 : Blo 1236436 1237279 := bstep (se 1 (by rfl) ⟨927959, by rfl⟩ : syracuseStep 1237279 = 1855919) B1855919
theorem B4178249 : Blo 1236436 4178249 := bstep (se 2 (by rfl) ⟨1566843, by rfl⟩ : syracuseStep 4178249 = 3133687) B3133687
theorem B5284187 : Blo 1236436 5284187 := bstep (se 1 (by rfl) ⟨3963140, by rfl⟩ : syracuseStep 5284187 = 7926281) B7926281
theorem B1237339 : Blo 1236436 1237339 := bstep (se 1 (by rfl) ⟨928004, by rfl⟩ : syracuseStep 1237339 = 1856009) B1856009
theorem B2089307 : Blo 1236436 2089307 := bstep (se 1 (by rfl) ⟨1566980, by rfl⟩ : syracuseStep 2089307 = 3133961) B3133961
theorem B2785643 : Blo 1236436 2785643 := bstep (se 1 (by rfl) ⟨2089232, by rfl⟩ : syracuseStep 2785643 = 4178465) B4178465
theorem B1237359 : Blo 1236436 1237359 := bstep (se 1 (by rfl) ⟨928019, by rfl⟩ : syracuseStep 1237359 = 1856039) B1856039
theorem B2089327 : Blo 1236436 2089327 := bstep (se 1 (by rfl) ⟨1566995, by rfl⟩ : syracuseStep 2089327 = 3133991) B3133991
theorem B1237415 : Blo 1236436 1237415 := bstep (se 1 (by rfl) ⟨928061, by rfl⟩ : syracuseStep 1237415 = 1856123) B1856123
theorem B5284271 : Blo 1236436 5284271 := bstep (se 1 (by rfl) ⟨3963203, by rfl⟩ : syracuseStep 5284271 = 7926407) B7926407
theorem B5644745 : Blo 1236436 5644745 := bstep (se 2 (by rfl) ⟨2116779, by rfl⟩ : syracuseStep 5644745 = 4233559) B4233559
theorem B2859475 : Blo 1236436 2859475 := bstep (se 1 (by rfl) ⟨2144606, by rfl⟩ : syracuseStep 2859475 = 4289213) B4289213
theorem B1237499 : Blo 1236436 1237499 := bstep (se 1 (by rfl) ⟨928124, by rfl⟩ : syracuseStep 1237499 = 1856249) B1856249
theorem B2785787 : Blo 1236436 2785787 := bstep (se 1 (by rfl) ⟨2089340, by rfl⟩ : syracuseStep 2785787 = 4178681) B4178681
theorem B1237567 : Blo 1236436 1237567 := bstep (se 1 (by rfl) ⟨928175, by rfl⟩ : syracuseStep 1237567 = 1856351) B1856351
theorem B1237575 : Blo 1236436 1237575 := bstep (se 1 (by rfl) ⟨928181, by rfl⟩ : syracuseStep 1237575 = 1856363) B1856363
theorem B2089543 : Blo 1236436 2089543 := bstep (se 1 (by rfl) ⟨1567157, by rfl⟩ : syracuseStep 2089543 = 3134315) B3134315
theorem B2785913 : Blo 1236436 2785913 := bstep (se 2 (by rfl) ⟨1044717, by rfl⟩ : syracuseStep 2785913 = 2089435) B2089435
theorem B4694699 : Blo 1236436 4694699 := bstep (se 1 (by rfl) ⟨3521024, by rfl⟩ : syracuseStep 4694699 = 7042049) B7042049
theorem B2785967 : Blo 1236436 2785967 := bstep (se 1 (by rfl) ⟨2089475, by rfl⟩ : syracuseStep 2785967 = 4178951) B4178951
theorem B1237727 : Blo 1236436 1237727 := bstep (se 1 (by rfl) ⟨928295, by rfl⟩ : syracuseStep 1237727 = 1856591) B1856591
theorem B3130103 : Blo 1236436 3130103 := bstep (se 1 (by rfl) ⟨2347577, by rfl⟩ : syracuseStep 3130103 = 4695155) B4695155
theorem B2786039 : Blo 1236436 2786039 := bstep (se 1 (by rfl) ⟨2089529, by rfl⟩ : syracuseStep 2786039 = 4179059) B4179059
theorem B2679571 : Blo 1236436 2679571 := bstep (se 1 (by rfl) ⟨2009678, by rfl⟩ : syracuseStep 2679571 = 4019357) B4019357
theorem B1237807 : Blo 1236436 1237807 := bstep (se 1 (by rfl) ⟨928355, by rfl⟩ : syracuseStep 1237807 = 1856711) B1856711
theorem B1237915 : Blo 1236436 1237915 := bstep (se 1 (by rfl) ⟨928436, by rfl⟩ : syracuseStep 1237915 = 1856873) B1856873
theorem B2786219 : Blo 1236436 2786219 := bstep (se 1 (by rfl) ⟨2089664, by rfl⟩ : syracuseStep 2786219 = 4179329) B4179329
theorem B23774147 : Blo 1236436 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B1237967 : Blo 1236436 1237967 := bstep (se 1 (by rfl) ⟨928475, by rfl⟩ : syracuseStep 1237967 = 1856951) B1856951
theorem B1237991 : Blo 1236436 1237991 := bstep (se 1 (by rfl) ⟨928493, by rfl⟩ : syracuseStep 1237991 = 1856987) B1856987
theorem B5284871 : Blo 1236436 5284871 := bstep (se 1 (by rfl) ⟨3963653, by rfl⟩ : syracuseStep 5284871 = 7927307) B7927307
theorem B10028069 : Blo 1236436 10028069 := bstep (se 4 (by rfl) ⟨940131, by rfl⟩ : syracuseStep 10028069 = 1880263) B1880263
theorem B6268103 : Blo 1236436 6268103 := bstep (se 1 (by rfl) ⟨4701077, by rfl⟩ : syracuseStep 6268103 = 9402155) B9402155
theorem B1565983 : Blo 1236436 1565983 := bstep (se 1 (by rfl) ⟨1174487, by rfl⟩ : syracuseStep 1565983 = 2348975) B2348975
theorem B1238303 : Blo 1236436 1238303 := bstep (se 1 (by rfl) ⟨928727, by rfl⟩ : syracuseStep 1238303 = 1857455) B1857455
theorem B5285159 : Blo 1236436 5285159 := bstep (se 1 (by rfl) ⟨3963869, by rfl⟩ : syracuseStep 5285159 = 7927739) B7927739
theorem B1238363 : Blo 1236436 1238363 := bstep (se 1 (by rfl) ⟨928772, by rfl⟩ : syracuseStep 1238363 = 1857545) B1857545
theorem B3130721 : Blo 1236436 3130721 := bstep (se 2 (by rfl) ⟨1174020, by rfl⟩ : syracuseStep 3130721 = 2348041) B2348041
theorem B6268265 : Blo 1236436 6268265 := bstep (se 2 (by rfl) ⟨2350599, by rfl⟩ : syracuseStep 6268265 = 4701199) B4701199
theorem B1238383 : Blo 1236436 1238383 := bstep (se 1 (by rfl) ⟨928787, by rfl⟩ : syracuseStep 1238383 = 1857575) B1857575
theorem B1254907 : Blo 1236436 1254907 := bstep (se 1 (by rfl) ⟨941180, by rfl⟩ : syracuseStep 1254907 = 1882361) B1882361
theorem B20055671 : Blo 1236436 20055671 := bstep (se 1 (by rfl) ⟨15041753, by rfl⟩ : syracuseStep 20055671 = 30083507) B30083507
theorem B1320671 : Blo 1236436 1320671 := bstep (se 1 (by rfl) ⟨990503, by rfl⟩ : syracuseStep 1320671 = 1981007) B1981007
theorem B3344257 : Blo 1236436 3344257 := bstep (se 2 (by rfl) ⟨1254096, by rfl⟩ : syracuseStep 3344257 = 2508193) B2508193
theorem B20056193 : Blo 1236436 20056193 := bstep (se 2 (by rfl) ⟨7521072, by rfl⟩ : syracuseStep 20056193 = 15042145) B15042145
theorem B10570013 : Blo 1236436 10570013 := bstep (se 3 (by rfl) ⟨1981877, by rfl⟩ : syracuseStep 10570013 = 3963755) B3963755
theorem B2861419 : Blo 1236436 2861419 := bstep (se 1 (by rfl) ⟨2146064, by rfl⟩ : syracuseStep 2861419 = 4292129) B4292129
theorem B5360039 : Blo 1236436 5360039 := bstep (se 1 (by rfl) ⟨4020029, by rfl⟩ : syracuseStep 5360039 = 8040059) B8040059
theorem B1411807 : Blo 1236436 1411807 := bstep (se 1 (by rfl) ⟨1058855, by rfl⟩ : syracuseStep 1411807 = 2117711) B2117711
theorem B5286647 : Blo 1236436 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B3132179 : Blo 1236436 3132179 := bstep (se 1 (by rfl) ⟨2349134, by rfl⟩ : syracuseStep 3132179 = 4698269) B4698269
theorem B24095555 : Blo 1236436 24095555 := bstep (se 1 (by rfl) ⟨18071666, by rfl⟩ : syracuseStep 24095555 = 36143333) B36143333
theorem B6261623 : Blo 1236436 6261623 := bstep (se 1 (by rfl) ⟨4696217, by rfl⟩ : syracuseStep 6261623 = 9392435) B9392435
theorem B5286799 : Blo 1236436 5286799 := bstep (se 1 (by rfl) ⟨3965099, by rfl⟩ : syracuseStep 5286799 = 7930199) B7930199
theorem B2640871 : Blo 1236436 2640871 := bstep (se 1 (by rfl) ⟨1980653, by rfl⟩ : syracuseStep 2640871 = 3961307) B3961307
theorem B3132391 : Blo 1236436 3132391 := bstep (se 1 (by rfl) ⟨2349293, by rfl⟩ : syracuseStep 3132391 = 4698587) B4698587
theorem B1854683 : Blo 1236436 1854683 := bstep (se 1 (by rfl) ⟨1391012, by rfl⟩ : syracuseStep 1854683 = 2782025) B2782025
theorem B3132665 : Blo 1236436 3132665 := bstep (se 2 (by rfl) ⟨1174749, by rfl⟩ : syracuseStep 3132665 = 2349499) B2349499
theorem B2821499 : Blo 1236436 2821499 := bstep (se 1 (by rfl) ⟨2116124, by rfl⟩ : syracuseStep 2821499 = 4232249) B4232249
theorem B1854857 : Blo 1236436 1854857 := bstep (se 2 (by rfl) ⟨695571, by rfl⟩ : syracuseStep 1854857 = 1391143) B1391143
theorem B3345803 : Blo 1236436 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B4697615 : Blo 1236436 4697615 := bstep (se 1 (by rfl) ⟨3523211, by rfl⟩ : syracuseStep 4697615 = 7046423) B7046423
theorem B6262433 : Blo 1236436 6262433 := bstep (se 2 (by rfl) ⟨2348412, by rfl⟩ : syracuseStep 6262433 = 4696825) B4696825
theorem B1855211 : Blo 1236436 1855211 := bstep (se 1 (by rfl) ⟨1391408, by rfl⟩ : syracuseStep 1855211 = 2782817) B2782817
theorem B3526379 : Blo 1236436 3526379 := bstep (se 1 (by rfl) ⟨2644784, by rfl⟩ : syracuseStep 3526379 = 5289569) B5289569
theorem B3133313 : Blo 1236436 3133313 := bstep (se 2 (by rfl) ⟨1174992, by rfl⟩ : syracuseStep 3133313 = 2349985) B2349985
theorem B1855439 : Blo 1236436 1855439 := bstep (se 1 (by rfl) ⟨1391579, by rfl⟩ : syracuseStep 1855439 = 2783159) B2783159
theorem B4173929 : Blo 1236436 4173929 := bstep (se 2 (by rfl) ⟨1565223, by rfl⟩ : syracuseStep 4173929 = 3130447) B3130447
theorem B21426443 : Blo 1236436 21426443 := bstep (se 1 (by rfl) ⟨16069832, by rfl⟩ : syracuseStep 21426443 = 32139665) B32139665
theorem B1487143 : Blo 1236436 1487143 := bstep (se 1 (by rfl) ⟨1115357, by rfl⟩ : syracuseStep 1487143 = 2230715) B2230715
theorem B1855835 : Blo 1236436 1855835 := bstep (se 1 (by rfl) ⟨1391876, by rfl⟩ : syracuseStep 1855835 = 2783753) B2783753
theorem B6689249 : Blo 1236436 6689249 := bstep (se 2 (by rfl) ⟨2508468, by rfl⟩ : syracuseStep 6689249 = 5016937) B5016937
theorem B8917553 : Blo 1236436 8917553 := bstep (se 2 (by rfl) ⟨3344082, by rfl⟩ : syracuseStep 8917553 = 6688165) B6688165
theorem B1856063 : Blo 1236436 1856063 := bstep (se 1 (by rfl) ⟨1392047, by rfl⟩ : syracuseStep 1856063 = 2784095) B2784095
theorem B3764807 : Blo 1236436 3764807 := bstep (se 1 (by rfl) ⟨2823605, by rfl⟩ : syracuseStep 3764807 = 5647211) B5647211
theorem B3134123 : Blo 1236436 3134123 := bstep (se 1 (by rfl) ⟨2350592, by rfl⟩ : syracuseStep 3134123 = 4701185) B4701185
theorem B1856183 : Blo 1236436 1856183 := bstep (se 1 (by rfl) ⟨1392137, by rfl⟩ : syracuseStep 1856183 = 2784275) B2784275
theorem B1856411 : Blo 1236436 1856411 := bstep (se 1 (by rfl) ⟨1392308, by rfl⟩ : syracuseStep 1856411 = 2784617) B2784617
theorem B4174793 : Blo 1236436 4174793 := bstep (se 2 (by rfl) ⟨1565547, by rfl⟩ : syracuseStep 4174793 = 3131095) B3131095
theorem B3961819 : Blo 1236436 3961819 := bstep (se 1 (by rfl) ⟨2971364, by rfl⟩ : syracuseStep 3961819 = 5942729) B5942729
theorem B2782331 : Blo 1236436 2782331 := bstep (se 1 (by rfl) ⟨2086748, by rfl⟩ : syracuseStep 2782331 = 4173497) B4173497
theorem B21157037 : Blo 1236436 21157037 := bstep (se 3 (by rfl) ⟨3966944, by rfl⟩ : syracuseStep 21157037 = 7933889) B7933889
theorem B4019399 : Blo 1236436 4019399 := bstep (se 1 (by rfl) ⟨3014549, by rfl⟩ : syracuseStep 4019399 = 6029099) B6029099
theorem B4175063 : Blo 1236436 4175063 := bstep (se 1 (by rfl) ⟨3131297, by rfl⟩ : syracuseStep 4175063 = 6262595) B6262595
theorem B3765491 : Blo 1236436 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B13382903 : Blo 1236436 13382903 := bstep (se 1 (by rfl) ⟨10037177, by rfl⟩ : syracuseStep 13382903 = 20074355) B20074355
theorem B2782457 : Blo 1236436 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B1856807 : Blo 1236436 1856807 := bstep (se 1 (by rfl) ⟨1392605, by rfl⟩ : syracuseStep 1856807 = 2785211) B2785211
theorem B51533171 : Blo 1236436 51533171 := bstep (se 1 (by rfl) ⟨38649878, by rfl⟩ : syracuseStep 51533171 = 77299757) B77299757
theorem B1856891 : Blo 1236436 1856891 := bstep (se 1 (by rfl) ⟨1392668, by rfl⟩ : syracuseStep 1856891 = 2785337) B2785337
theorem B2782601 : Blo 1236436 2782601 := bstep (se 2 (by rfl) ⟨1043475, by rfl⟩ : syracuseStep 2782601 = 2086951) B2086951
theorem B2971019 : Blo 1236436 2971019 := bstep (se 1 (by rfl) ⟨2228264, by rfl⟩ : syracuseStep 2971019 = 4456529) B4456529
theorem B15857117 : Blo 1236436 15857117 := bstep (se 3 (by rfl) ⟨2973209, by rfl⟩ : syracuseStep 15857117 = 5946419) B5946419
theorem B1857017 : Blo 1236436 1857017 := bstep (se 2 (by rfl) ⟨696381, by rfl⟩ : syracuseStep 1857017 = 1392763) B1392763
theorem B2782727 : Blo 1236436 2782727 := bstep (se 1 (by rfl) ⟨2087045, by rfl⟩ : syracuseStep 2782727 = 4174091) B4174091
theorem B6264377 : Blo 1236436 6264377 := bstep (se 2 (by rfl) ⟨2349141, by rfl⟩ : syracuseStep 6264377 = 4698283) B4698283
theorem B1857119 : Blo 1236436 1857119 := bstep (se 1 (by rfl) ⟨1392839, by rfl⟩ : syracuseStep 1857119 = 2785679) B2785679
theorem B2782907 : Blo 1236436 2782907 := bstep (se 1 (by rfl) ⟨2087180, by rfl⟩ : syracuseStep 2782907 = 4174361) B4174361
theorem B2643691 : Blo 1236436 2643691 := bstep (se 1 (by rfl) ⟨1982768, by rfl⟩ : syracuseStep 2643691 = 3965537) B3965537
theorem B7141175 : Blo 1236436 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B1857335 : Blo 1236436 1857335 := bstep (se 1 (by rfl) ⟨1393001, by rfl⟩ : syracuseStep 1857335 = 2786003) B2786003
theorem B2783033 : Blo 1236436 2783033 := bstep (se 2 (by rfl) ⟨1043637, by rfl⟩ : syracuseStep 2783033 = 2087275) B2087275
theorem B2971673 : Blo 1236436 2971673 := bstep (se 2 (by rfl) ⟨1114377, by rfl⟩ : syracuseStep 2971673 = 2228755) B2228755
theorem B1857641 : Blo 1236436 1857641 := bstep (se 2 (by rfl) ⟨696615, by rfl⟩ : syracuseStep 1857641 = 1393231) B1393231
theorem B36190475 : Blo 1236436 36190475 := bstep (se 1 (by rfl) ⟨27142856, by rfl⟩ : syracuseStep 36190475 = 54285713) B54285713
theorem B2783663 : Blo 1236436 2783663 := bstep (se 1 (by rfl) ⟨2087747, by rfl⟩ : syracuseStep 2783663 = 4175495) B4175495
theorem B3520979 : Blo 1236436 3520979 := bstep (se 1 (by rfl) ⟨2640734, by rfl⟩ : syracuseStep 3520979 = 5281469) B5281469
theorem B2783699 : Blo 1236436 2783699 := bstep (se 1 (by rfl) ⟨2087774, by rfl⟩ : syracuseStep 2783699 = 4175549) B4175549
theorem B2783807 : Blo 1236436 2783807 := bstep (se 1 (by rfl) ⟨2087855, by rfl⟩ : syracuseStep 2783807 = 4175711) B4175711
theorem B80230985 : Blo 1236436 80230985 := bstep (se 2 (by rfl) ⟨30086619, by rfl⟩ : syracuseStep 80230985 = 60173239) B60173239
theorem B2087545 : Blo 1236436 2087545 := bstep (se 2 (by rfl) ⟨782829, by rfl⟩ : syracuseStep 2087545 = 1565659) B1565659
theorem B2783915 : Blo 1236436 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B7043759 : Blo 1236436 7043759 := bstep (se 1 (by rfl) ⟨5282819, by rfl⟩ : syracuseStep 7043759 = 10565639) B10565639
theorem B2087599 : Blo 1236436 2087599 := bstep (se 1 (by rfl) ⟨1565699, by rfl⟩ : syracuseStep 2087599 = 3131399) B3131399
theorem B3390587 : Blo 1236436 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B2784455 : Blo 1236436 2784455 := bstep (se 1 (by rfl) ⟨2088341, by rfl⟩ : syracuseStep 2784455 = 4176683) B4176683
theorem B4177115 : Blo 1236436 4177115 := bstep (se 1 (by rfl) ⟨3132836, by rfl⟩ : syracuseStep 4177115 = 6265673) B6265673
theorem B9526493 : Blo 1236436 9526493 := bstep (se 3 (by rfl) ⟨1786217, by rfl⟩ : syracuseStep 9526493 = 3572435) B3572435
theorem B9403613 : Blo 1236436 9403613 := bstep (se 3 (by rfl) ⟨1763177, by rfl⟩ : syracuseStep 9403613 = 3526355) B3526355
theorem B1981673 : Blo 1236436 1981673 := bstep (se 2 (by rfl) ⟨743127, by rfl⟩ : syracuseStep 1981673 = 1486255) B1486255
theorem B2350433 : Blo 1236436 2350433 := bstep (se 2 (by rfl) ⟨881412, by rfl⟩ : syracuseStep 2350433 = 1762825) B1762825
theorem B2784635 : Blo 1236436 2784635 := bstep (se 1 (by rfl) ⟨2088476, by rfl⟩ : syracuseStep 2784635 = 4176953) B4176953
theorem B30080393 : Blo 1236436 30080393 := bstep (se 2 (by rfl) ⟨11280147, by rfl⟩ : syracuseStep 30080393 = 22560295) B22560295
theorem B15670691 : Blo 1236436 15670691 := bstep (se 1 (by rfl) ⟨11753018, by rfl⟩ : syracuseStep 15670691 = 23506037) B23506037
theorem B11902373 : Blo 1236436 11902373 := bstep (se 4 (by rfl) ⟨1115847, by rfl⟩ : syracuseStep 11902373 = 2231695) B2231695
theorem B3964409 : Blo 1236436 3964409 := bstep (se 2 (by rfl) ⟨1486653, by rfl⟩ : syracuseStep 3964409 = 2973307) B2973307
theorem B2784761 : Blo 1236436 2784761 := bstep (se 2 (by rfl) ⟨1044285, by rfl⟩ : syracuseStep 2784761 = 2088571) B2088571
theorem B1236475 : Blo 1236436 1236475 := bstep (se 1 (by rfl) ⟨927356, by rfl⟩ : syracuseStep 1236475 = 1854713) B1854713
theorem B22887947 : Blo 1236436 22887947 := bstep (se 1 (by rfl) ⟨17165960, by rfl⟩ : syracuseStep 22887947 = 34331921) B34331921
theorem B1236543 : Blo 1236436 1236543 := bstep (se 1 (by rfl) ⟨927407, by rfl⟩ : syracuseStep 1236543 = 1854815) B1854815
theorem B1236551 : Blo 1236436 1236551 := bstep (se 1 (by rfl) ⟨927413, by rfl⟩ : syracuseStep 1236551 = 1854827) B1854827
theorem B7044691 : Blo 1236436 7044691 := bstep (se 1 (by rfl) ⟨5283518, by rfl⟩ : syracuseStep 7044691 = 10567037) B10567037
theorem B2784851 : Blo 1236436 2784851 := bstep (se 1 (by rfl) ⟨2088638, by rfl⟩ : syracuseStep 2784851 = 4177277) B4177277
theorem B1392223 : Blo 1236436 1392223 := bstep (se 1 (by rfl) ⟨1044167, by rfl⟩ : syracuseStep 1392223 = 2088335) B2088335
theorem B11296351 : Blo 1236436 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B6266483 : Blo 1236436 6266483 := bstep (se 1 (by rfl) ⟨4699862, by rfl⟩ : syracuseStep 6266483 = 9399725) B9399725
theorem B13557395 : Blo 1236436 13557395 := bstep (se 1 (by rfl) ⟨10168046, by rfl⟩ : syracuseStep 13557395 = 20336093) B20336093
theorem B1236703 : Blo 1236436 1236703 := bstep (se 1 (by rfl) ⟨927527, by rfl⟩ : syracuseStep 1236703 = 1855055) B1855055
theorem B2785031 : Blo 1236436 2785031 := bstep (se 1 (by rfl) ⟨2088773, by rfl⟩ : syracuseStep 2785031 = 4177547) B4177547
theorem B4701959 : Blo 1236436 4701959 := bstep (se 1 (by rfl) ⟨3526469, by rfl⟩ : syracuseStep 4701959 = 7052939) B7052939
theorem B1236783 : Blo 1236436 1236783 := bstep (se 1 (by rfl) ⟨927587, by rfl⟩ : syracuseStep 1236783 = 1855175) B1855175
theorem B6692665 : Blo 1236436 6692665 := bstep (se 2 (by rfl) ⟨2509749, by rfl⟩ : syracuseStep 6692665 = 5019499) B5019499
theorem B1236891 : Blo 1236436 1236891 := bstep (se 1 (by rfl) ⟨927668, by rfl⟩ : syracuseStep 1236891 = 1855337) B1855337
theorem B1236943 : Blo 1236436 1236943 := bstep (se 1 (by rfl) ⟨927707, by rfl⟩ : syracuseStep 1236943 = 1855415) B1855415
theorem B1236967 : Blo 1236436 1236967 := bstep (se 1 (by rfl) ⟨927725, by rfl⟩ : syracuseStep 1236967 = 1855451) B1855451
theorem B2785319 : Blo 1236436 2785319 := bstep (se 1 (by rfl) ⟨2088989, by rfl⟩ : syracuseStep 2785319 = 4177979) B4177979
theorem B15057035 : Blo 1236436 15057035 := bstep (se 1 (by rfl) ⟨11292776, by rfl⟩ : syracuseStep 15057035 = 22585553) B22585553
theorem B2785499 : Blo 1236436 2785499 := bstep (se 1 (by rfl) ⟨2089124, by rfl⟩ : syracuseStep 2785499 = 4178249) B4178249
theorem B3522791 : Blo 1236436 3522791 := bstep (se 1 (by rfl) ⟨2642093, by rfl⟩ : syracuseStep 3522791 = 5284187) B5284187
theorem B1237223 : Blo 1236436 1237223 := bstep (se 1 (by rfl) ⟨927917, by rfl⟩ : syracuseStep 1237223 = 1855835) B1855835
theorem B1392871 : Blo 1236436 1392871 := bstep (se 1 (by rfl) ⟨1044653, by rfl⟩ : syracuseStep 1392871 = 2089307) B2089307
theorem B3522847 : Blo 1236436 3522847 := bstep (se 1 (by rfl) ⟨2642135, by rfl⟩ : syracuseStep 3522847 = 5284271) B5284271
theorem B1237375 : Blo 1236436 1237375 := bstep (se 1 (by rfl) ⟨928031, by rfl⟩ : syracuseStep 1237375 = 1856063) B1856063
theorem B3129799 : Blo 1236436 3129799 := bstep (se 1 (by rfl) ⟨2347349, by rfl⟩ : syracuseStep 3129799 = 4694699) B4694699
theorem B2089415 : Blo 1236436 2089415 := bstep (se 1 (by rfl) ⟨1567061, by rfl⟩ : syracuseStep 2089415 = 3134123) B3134123
theorem B1237455 : Blo 1236436 1237455 := bstep (se 1 (by rfl) ⟨928091, by rfl⟩ : syracuseStep 1237455 = 1856183) B1856183
theorem B2785769 : Blo 1236436 2785769 := bstep (se 2 (by rfl) ⟨1044663, by rfl⟩ : syracuseStep 2785769 = 2089327) B2089327
theorem B1237607 : Blo 1236436 1237607 := bstep (se 1 (by rfl) ⟨928205, by rfl⟩ : syracuseStep 1237607 = 1856411) B1856411
theorem B3523247 : Blo 1236436 3523247 := bstep (se 1 (by rfl) ⟨2642435, by rfl⟩ : syracuseStep 3523247 = 5284871) B5284871
theorem B6685379 : Blo 1236436 6685379 := bstep (se 1 (by rfl) ⟨5014034, by rfl⟩ : syracuseStep 6685379 = 10028069) B10028069
theorem B2786057 : Blo 1236436 2786057 := bstep (se 2 (by rfl) ⟨1044771, by rfl⟩ : syracuseStep 2786057 = 2089543) B2089543
theorem B2679599 : Blo 1236436 2679599 := bstep (se 1 (by rfl) ⟨2009699, by rfl⟩ : syracuseStep 2679599 = 4019399) B4019399
theorem B4178735 : Blo 1236436 4178735 := bstep (se 1 (by rfl) ⟨3134051, by rfl⟩ : syracuseStep 4178735 = 6268103) B6268103
theorem B8921935 : Blo 1236436 8921935 := bstep (se 1 (by rfl) ⟨6691451, by rfl⟩ : syracuseStep 8921935 = 13382903) B13382903
theorem B3523439 : Blo 1236436 3523439 := bstep (se 1 (by rfl) ⟨2642579, by rfl⟩ : syracuseStep 3523439 = 5285159) B5285159
theorem B1237871 : Blo 1236436 1237871 := bstep (se 1 (by rfl) ⟨928403, by rfl⟩ : syracuseStep 1237871 = 1856807) B1856807
theorem B4178843 : Blo 1236436 4178843 := bstep (se 1 (by rfl) ⟨3134132, by rfl⟩ : syracuseStep 4178843 = 6268265) B6268265
theorem B1237927 : Blo 1236436 1237927 := bstep (se 1 (by rfl) ⟨928445, by rfl⟩ : syracuseStep 1237927 = 1856891) B1856891
theorem B1238011 : Blo 1236436 1238011 := bstep (se 1 (by rfl) ⟨928508, by rfl⟩ : syracuseStep 1238011 = 1857017) B1857017
theorem B3572761 : Blo 1236436 3572761 := bstep (se 2 (by rfl) ⟨1339785, by rfl⟩ : syracuseStep 3572761 = 2679571) B2679571
theorem B7922717 : Blo 1236436 7922717 := bstep (se 3 (by rfl) ⟨1485509, by rfl⟩ : syracuseStep 7922717 = 2971019) B2971019
theorem B1238079 : Blo 1236436 1238079 := bstep (se 1 (by rfl) ⟨928559, by rfl⟩ : syracuseStep 1238079 = 1857119) B1857119
theorem B13370447 : Blo 1236436 13370447 := bstep (se 1 (by rfl) ⟨10027835, by rfl⟩ : syracuseStep 13370447 = 20055671) B20055671
theorem B4760783 : Blo 1236436 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B1238223 : Blo 1236436 1238223 := bstep (se 1 (by rfl) ⟨928667, by rfl⟩ : syracuseStep 1238223 = 1857335) B1857335
theorem B1238427 : Blo 1236436 1238427 := bstep (se 1 (by rfl) ⟨928820, by rfl⟩ : syracuseStep 1238427 = 1857641) B1857641
theorem B13370795 : Blo 1236436 13370795 := bstep (se 1 (by rfl) ⟨10028096, by rfl⟩ : syracuseStep 13370795 = 20056193) B20056193
theorem B24126983 : Blo 1236436 24126983 := bstep (se 1 (by rfl) ⟨18095237, by rfl⟩ : syracuseStep 24126983 = 36190475) B36190475
theorem B7046675 : Blo 1236436 7046675 := bstep (se 1 (by rfl) ⟨5285006, by rfl⟩ : syracuseStep 7046675 = 10570013) B10570013
theorem B7931429 : Blo 1236436 7931429 := bstep (se 4 (by rfl) ⟨743571, by rfl⟩ : syracuseStep 7931429 = 1487143) B1487143
theorem B3573359 : Blo 1236436 3573359 := bstep (se 1 (by rfl) ⟨2680019, by rfl⟩ : syracuseStep 3573359 = 5360039) B5360039
theorem B53487323 : Blo 1236436 53487323 := bstep (se 1 (by rfl) ⟨40115492, by rfl⟩ : syracuseStep 53487323 = 80230985) B80230985
theorem B4695839 : Blo 1236436 4695839 := bstep (se 1 (by rfl) ⟨3521879, by rfl⟩ : syracuseStep 4695839 = 7043759) B7043759
theorem B3524431 : Blo 1236436 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B1673209 : Blo 1236436 1673209 := bstep (se 2 (by rfl) ⟨627453, by rfl⟩ : syracuseStep 1673209 = 1254907) B1254907
theorem B6350995 : Blo 1236436 6350995 := bstep (se 1 (by rfl) ⟨4763246, by rfl⟩ : syracuseStep 6350995 = 9526493) B9526493
theorem B6269075 : Blo 1236436 6269075 := bstep (se 1 (by rfl) ⟨4701806, by rfl⟩ : syracuseStep 6269075 = 9403613) B9403613
theorem B1321115 : Blo 1236436 1321115 := bstep (se 1 (by rfl) ⟨990836, by rfl⟩ : syracuseStep 1321115 = 1981673) B1981673
theorem B1566955 : Blo 1236436 1566955 := bstep (se 1 (by rfl) ⟨1175216, by rfl⟩ : syracuseStep 1566955 = 2350433) B2350433
theorem B2230535 : Blo 1236436 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B10447127 : Blo 1236436 10447127 := bstep (se 1 (by rfl) ⟨7835345, by rfl⟩ : syracuseStep 10447127 = 15670691) B15670691
theorem B3524921 : Blo 1236436 3524921 := bstep (se 2 (by rfl) ⟨1321845, by rfl⟩ : syracuseStep 3524921 = 2643691) B2643691
theorem B3131743 : Blo 1236436 3131743 := bstep (se 1 (by rfl) ⟨2348807, by rfl⟩ : syracuseStep 3131743 = 4697615) B4697615
theorem B8923553 : Blo 1236436 8923553 := bstep (se 2 (by rfl) ⟨3346332, by rfl⟩ : syracuseStep 8923553 = 6692665) B6692665
theorem B9038263 : Blo 1236436 9038263 := bstep (se 1 (by rfl) ⟨6778697, by rfl⟩ : syracuseStep 9038263 = 13557395) B13557395
theorem B4459009 : Blo 1236436 4459009 := bstep (se 2 (by rfl) ⟨1672128, by rfl⟩ : syracuseStep 4459009 = 3344257) B3344257
theorem B5941943 : Blo 1236436 5941943 := bstep (se 1 (by rfl) ⟨4456457, by rfl⟩ : syracuseStep 5941943 = 8912915) B8912915
theorem B3763163 : Blo 1236436 3763163 := bstep (se 1 (by rfl) ⟨2822372, by rfl⟩ : syracuseStep 3763163 = 5644745) B5644745
theorem B4459499 : Blo 1236436 4459499 := bstep (se 1 (by rfl) ⟨3344624, by rfl⟩ : syracuseStep 4459499 = 6689249) B6689249
theorem B2509871 : Blo 1236436 2509871 := bstep (se 1 (by rfl) ⟨1882403, by rfl⟩ : syracuseStep 2509871 = 3764807) B3764807
theorem B3812633 : Blo 1236436 3812633 := bstep (se 2 (by rfl) ⟨1429737, by rfl⟩ : syracuseStep 3812633 = 2859475) B2859475
theorem B1854887 : Blo 1236436 1854887 := bstep (se 1 (by rfl) ⟨1391165, by rfl⟩ : syracuseStep 1854887 = 2782331) B2782331
theorem B2510327 : Blo 1236436 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B1854971 : Blo 1236436 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B1855067 : Blo 1236436 1855067 := bstep (se 1 (by rfl) ⟨1391300, by rfl⟩ : syracuseStep 1855067 = 2782601) B2782601
theorem B10571411 : Blo 1236436 10571411 := bstep (se 1 (by rfl) ⟨7928558, by rfl⟩ : syracuseStep 10571411 = 15857117) B15857117
theorem B1855151 : Blo 1236436 1855151 := bstep (se 1 (by rfl) ⟨1391363, by rfl⟩ : syracuseStep 1855151 = 2782727) B2782727
theorem B1855271 : Blo 1236436 1855271 := bstep (se 1 (by rfl) ⟨1391453, by rfl⟩ : syracuseStep 1855271 = 2782907) B2782907
theorem B7049065 : Blo 1236436 7049065 := bstep (se 2 (by rfl) ⟨2643399, by rfl⟩ : syracuseStep 7049065 = 5286799) B5286799
theorem B1855355 : Blo 1236436 1855355 := bstep (se 1 (by rfl) ⟨1391516, by rfl⟩ : syracuseStep 1855355 = 2783033) B2783033
theorem B1855775 : Blo 1236436 1855775 := bstep (se 1 (by rfl) ⟨1391831, by rfl⟩ : syracuseStep 1855775 = 2783663) B2783663
theorem B2347319 : Blo 1236436 2347319 := bstep (se 1 (by rfl) ⟨1760489, by rfl⟩ : syracuseStep 2347319 = 3520979) B3520979
theorem B1855799 : Blo 1236436 1855799 := bstep (se 1 (by rfl) ⟨1391849, by rfl⟩ : syracuseStep 1855799 = 2783699) B2783699
theorem B1855871 : Blo 1236436 1855871 := bstep (se 1 (by rfl) ⟨1391903, by rfl⟩ : syracuseStep 1855871 = 2783807) B2783807
theorem B1855943 : Blo 1236436 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B4174415 : Blo 1236436 4174415 := bstep (se 1 (by rfl) ⟨3130811, by rfl⟩ : syracuseStep 4174415 = 6261623) B6261623
theorem B9392921 : Blo 1236436 9392921 := bstep (se 2 (by rfl) ⟨3522345, by rfl⟩ : syracuseStep 9392921 = 7044691) B7044691
theorem B1856297 : Blo 1236436 1856297 := bstep (se 2 (by rfl) ⟨696111, by rfl⟩ : syracuseStep 1856297 = 1392223) B1392223
theorem B15061801 : Blo 1236436 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B1856303 : Blo 1236436 1856303 := bstep (se 1 (by rfl) ⟨1392227, by rfl⟩ : syracuseStep 1856303 = 2784455) B2784455
theorem B1880999 : Blo 1236436 1880999 := bstep (se 1 (by rfl) ⟨1410749, by rfl⟩ : syracuseStep 1880999 = 2821499) B2821499
theorem B1856423 : Blo 1236436 1856423 := bstep (se 1 (by rfl) ⟨1392317, by rfl⟩ : syracuseStep 1856423 = 2784635) B2784635
theorem B7934915 : Blo 1236436 7934915 := bstep (se 1 (by rfl) ⟨5951186, by rfl⟩ : syracuseStep 7934915 = 11902373) B11902373
theorem B2642939 : Blo 1236436 2642939 := bstep (se 1 (by rfl) ⟨1982204, by rfl⟩ : syracuseStep 2642939 = 3964409) B3964409
theorem B1856507 : Blo 1236436 1856507 := bstep (se 1 (by rfl) ⟨1392380, by rfl⟩ : syracuseStep 1856507 = 2784761) B2784761
theorem B15258631 : Blo 1236436 15258631 := bstep (se 1 (by rfl) ⟨11443973, by rfl⟩ : syracuseStep 15258631 = 22887947) B22887947
theorem B1856567 : Blo 1236436 1856567 := bstep (se 1 (by rfl) ⟨1392425, by rfl⟩ : syracuseStep 1856567 = 2784851) B2784851
theorem B4174955 : Blo 1236436 4174955 := bstep (se 1 (by rfl) ⟨3131216, by rfl⟩ : syracuseStep 4174955 = 6262433) B6262433
theorem B1856687 : Blo 1236436 1856687 := bstep (se 1 (by rfl) ⟨1392515, by rfl⟩ : syracuseStep 1856687 = 2785031) B2785031
theorem B3134639 : Blo 1236436 3134639 := bstep (se 1 (by rfl) ⟨2350979, by rfl⟩ : syracuseStep 3134639 = 4701959) B4701959
theorem B2782619 : Blo 1236436 2782619 := bstep (se 1 (by rfl) ⟨2086964, by rfl⟩ : syracuseStep 2782619 = 4173929) B4173929
theorem B2348443 : Blo 1236436 2348443 := bstep (se 1 (by rfl) ⟨1761332, by rfl⟩ : syracuseStep 2348443 = 3522665) B3522665
theorem B14284295 : Blo 1236436 14284295 := bstep (se 1 (by rfl) ⟨10713221, by rfl⟩ : syracuseStep 14284295 = 21426443) B21426443
theorem B1857095 : Blo 1236436 1857095 := bstep (se 1 (by rfl) ⟨1392821, by rfl⟩ : syracuseStep 1857095 = 2785643) B2785643
theorem B1857191 : Blo 1236436 1857191 := bstep (se 1 (by rfl) ⟨1392893, by rfl⟩ : syracuseStep 1857191 = 2785787) B2785787
theorem B1857275 : Blo 1236436 1857275 := bstep (se 1 (by rfl) ⟨1392956, by rfl⟩ : syracuseStep 1857275 = 2785913) B2785913
theorem B1857311 : Blo 1236436 1857311 := bstep (se 1 (by rfl) ⟨1392983, by rfl⟩ : syracuseStep 1857311 = 2785967) B2785967
theorem B3815225 : Blo 1236436 3815225 := bstep (se 2 (by rfl) ⟨1430709, by rfl⟩ : syracuseStep 3815225 = 2861419) B2861419
theorem B2086735 : Blo 1236436 2086735 := bstep (se 1 (by rfl) ⟨1565051, by rfl⟩ : syracuseStep 2086735 = 3130103) B3130103
theorem B1857359 : Blo 1236436 1857359 := bstep (se 1 (by rfl) ⟨1393019, by rfl⟩ : syracuseStep 1857359 = 2786039) B2786039
theorem B1857479 : Blo 1236436 1857479 := bstep (se 1 (by rfl) ⟨1393109, by rfl⟩ : syracuseStep 1857479 = 2786219) B2786219
theorem B15849431 : Blo 1236436 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B2783195 : Blo 1236436 2783195 := bstep (se 1 (by rfl) ⟨2087396, by rfl⟩ : syracuseStep 2783195 = 4174793) B4174793
theorem B14104691 : Blo 1236436 14104691 := bstep (se 1 (by rfl) ⟨10578518, by rfl⟩ : syracuseStep 14104691 = 21157037) B21157037
theorem B2783375 : Blo 1236436 2783375 := bstep (se 1 (by rfl) ⟨2087531, by rfl⟩ : syracuseStep 2783375 = 4175063) B4175063
theorem B2783393 : Blo 1236436 2783393 := bstep (se 2 (by rfl) ⟨1043772, by rfl⟩ : syracuseStep 2783393 = 2087545) B2087545
theorem B2783465 : Blo 1236436 2783465 := bstep (se 2 (by rfl) ⟨1043799, by rfl⟩ : syracuseStep 2783465 = 2087599) B2087599
theorem B2087147 : Blo 1236436 2087147 := bstep (se 1 (by rfl) ⟨1565360, by rfl⟩ : syracuseStep 2087147 = 3130721) B3130721
theorem B34355447 : Blo 1236436 34355447 := bstep (se 1 (by rfl) ⟨25766585, by rfl⟩ : syracuseStep 34355447 = 51533171) B51533171
theorem B1882409 : Blo 1236436 1882409 := bstep (se 2 (by rfl) ⟨705903, by rfl⟩ : syracuseStep 1882409 = 1411807) B1411807
theorem B4176251 : Blo 1236436 4176251 := bstep (se 1 (by rfl) ⟨3132188, by rfl⟩ : syracuseStep 4176251 = 6264377) B6264377
theorem B5282425 : Blo 1236436 5282425 := bstep (se 2 (by rfl) ⟨1980909, by rfl⟩ : syracuseStep 5282425 = 3961819) B3961819
theorem B3521161 : Blo 1236436 3521161 := bstep (se 2 (by rfl) ⟨1320435, by rfl⟩ : syracuseStep 3521161 = 2640871) B2640871
theorem B4176521 : Blo 1236436 4176521 := bstep (se 2 (by rfl) ⟨1566195, by rfl⟩ : syracuseStep 4176521 = 3132391) B3132391
theorem B1981115 : Blo 1236436 1981115 := bstep (se 1 (by rfl) ⟨1485836, by rfl⟩ : syracuseStep 1981115 = 2971673) B2971673
theorem B23780141 : Blo 1236436 23780141 := bstep (se 3 (by rfl) ⟨4458776, by rfl⟩ : syracuseStep 23780141 = 8917553) B8917553
theorem B2087977 : Blo 1236436 2087977 := bstep (se 2 (by rfl) ⟨782991, by rfl⟩ : syracuseStep 2087977 = 1565983) B1565983
theorem B2088119 : Blo 1236436 2088119 := bstep (se 1 (by rfl) ⟨1566089, by rfl⟩ : syracuseStep 2088119 = 3132179) B3132179
theorem B16063703 : Blo 1236436 16063703 := bstep (se 1 (by rfl) ⟨12047777, by rfl⟩ : syracuseStep 16063703 = 24095555) B24095555
theorem B3521789 : Blo 1236436 3521789 := bstep (se 3 (by rfl) ⟨660335, by rfl⟩ : syracuseStep 3521789 = 1320671) B1320671
theorem B2260391 : Blo 1236436 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B1236455 : Blo 1236436 1236455 := bstep (se 1 (by rfl) ⟨927341, by rfl⟩ : syracuseStep 1236455 = 1854683) B1854683
theorem B2784743 : Blo 1236436 2784743 := bstep (se 1 (by rfl) ⟨2088557, by rfl⟩ : syracuseStep 2784743 = 4177115) B4177115
theorem B2088443 : Blo 1236436 2088443 := bstep (se 1 (by rfl) ⟨1566332, by rfl⟩ : syracuseStep 2088443 = 3132665) B3132665
theorem B20053595 : Blo 1236436 20053595 := bstep (se 1 (by rfl) ⟨15040196, by rfl⟩ : syracuseStep 20053595 = 30080393) B30080393
theorem B1236571 : Blo 1236436 1236571 := bstep (se 1 (by rfl) ⟨927428, by rfl⟩ : syracuseStep 1236571 = 1854857) B1854857
theorem B4177655 : Blo 1236436 4177655 := bstep (se 1 (by rfl) ⟨3133241, by rfl⟩ : syracuseStep 4177655 = 6266483) B6266483
theorem B1236807 : Blo 1236436 1236807 := bstep (se 1 (by rfl) ⟨927605, by rfl⟩ : syracuseStep 1236807 = 1855211) B1855211
theorem B2350919 : Blo 1236436 2350919 := bstep (se 1 (by rfl) ⟨1763189, by rfl⟩ : syracuseStep 2350919 = 3526379) B3526379
theorem B2088875 : Blo 1236436 2088875 := bstep (se 1 (by rfl) ⟨1566656, by rfl⟩ : syracuseStep 2088875 = 3133313) B3133313
theorem B1236959 : Blo 1236436 1236959 := bstep (se 1 (by rfl) ⟨927719, by rfl⟩ : syracuseStep 1236959 = 1855439) B1855439
theorem B1237183 : Blo 1236436 1237183 := bstep (se 1 (by rfl) ⟨927887, by rfl⟩ : syracuseStep 1237183 = 1855775) B1855775
theorem B1237199 : Blo 1236436 1237199 := bstep (se 1 (by rfl) ⟨927899, by rfl⟩ : syracuseStep 1237199 = 1855799) B1855799
theorem B1237247 : Blo 1236436 1237247 := bstep (se 1 (by rfl) ⟨927935, by rfl⟩ : syracuseStep 1237247 = 1855871) B1855871
theorem B1237295 : Blo 1236436 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B1392943 : Blo 1236436 1392943 := bstep (se 1 (by rfl) ⟨1044707, by rfl⟩ : syracuseStep 1392943 = 2089415) B2089415
theorem B2089273 : Blo 1236436 2089273 := bstep (se 2 (by rfl) ⟨783477, by rfl⟩ : syracuseStep 2089273 = 1566955) B1566955
theorem B3522973 : Blo 1236436 3522973 := bstep (se 3 (by rfl) ⟨660557, by rfl⟩ : syracuseStep 3522973 = 1321115) B1321115
theorem B20079029 : Blo 1236436 20079029 := bstep (se 5 (by rfl) ⟨941204, by rfl⟩ : syracuseStep 20079029 = 1882409) B1882409
theorem B4456919 : Blo 1236436 4456919 := bstep (se 1 (by rfl) ⟨3342689, by rfl⟩ : syracuseStep 4456919 = 6685379) B6685379
theorem B26771957 : Blo 1236436 26771957 := bstep (se 5 (by rfl) ⟨1254935, by rfl⟩ : syracuseStep 26771957 = 2509871) B2509871
theorem B1237531 : Blo 1236436 1237531 := bstep (se 1 (by rfl) ⟨928148, by rfl⟩ : syracuseStep 1237531 = 1856297) B1856297
theorem B1237535 : Blo 1236436 1237535 := bstep (se 1 (by rfl) ⟨928151, by rfl⟩ : syracuseStep 1237535 = 1856303) B1856303
theorem B2785823 : Blo 1236436 2785823 := bstep (se 1 (by rfl) ⟨2089367, by rfl⟩ : syracuseStep 2785823 = 4178735) B4178735
theorem B12051017 : Blo 1236436 12051017 := bstep (se 2 (by rfl) ⟨4519131, by rfl⟩ : syracuseStep 12051017 = 9038263) B9038263
theorem B2785895 : Blo 1236436 2785895 := bstep (se 1 (by rfl) ⟨2089421, by rfl⟩ : syracuseStep 2785895 = 4178843) B4178843
theorem B1253999 : Blo 1236436 1253999 := bstep (se 1 (by rfl) ⟨940499, by rfl⟩ : syracuseStep 1253999 = 1880999) B1880999
theorem B1237615 : Blo 1236436 1237615 := bstep (se 1 (by rfl) ⟨928211, by rfl⟩ : syracuseStep 1237615 = 1856423) B1856423
theorem B1761959 : Blo 1236436 1761959 := bstep (se 1 (by rfl) ⟨1321469, by rfl⟩ : syracuseStep 1761959 = 2642939) B2642939
theorem B1237671 : Blo 1236436 1237671 := bstep (se 1 (by rfl) ⟨928253, by rfl⟩ : syracuseStep 1237671 = 1856507) B1856507
theorem B5948093 : Blo 1236436 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B1237711 : Blo 1236436 1237711 := bstep (se 1 (by rfl) ⟨928283, by rfl⟩ : syracuseStep 1237711 = 1856567) B1856567
theorem B1237791 : Blo 1236436 1237791 := bstep (se 1 (by rfl) ⟨928343, by rfl⟩ : syracuseStep 1237791 = 1856687) B1856687
theorem B2089759 : Blo 1236436 2089759 := bstep (se 1 (by rfl) ⟨1567319, by rfl⟩ : syracuseStep 2089759 = 3134639) B3134639
theorem B6259517 : Blo 1236436 6259517 := bstep (se 3 (by rfl) ⟨1173659, by rfl⟩ : syracuseStep 6259517 = 2347319) B2347319
theorem B4694881 : Blo 1236436 4694881 := bstep (se 2 (by rfl) ⟨1760580, by rfl⟩ : syracuseStep 4694881 = 3521161) B3521161
theorem B8913863 : Blo 1236436 8913863 := bstep (se 1 (by rfl) ⟨6685397, by rfl⟩ : syracuseStep 8913863 = 13370795) B13370795
theorem B1238063 : Blo 1236436 1238063 := bstep (se 1 (by rfl) ⟨928547, by rfl⟩ : syracuseStep 1238063 = 1857095) B1857095
theorem B11895913 : Blo 1236436 11895913 := bstep (se 2 (by rfl) ⟨4460967, by rfl⟩ : syracuseStep 11895913 = 8921935) B8921935
theorem B1238127 : Blo 1236436 1238127 := bstep (se 1 (by rfl) ⟨928595, by rfl⟩ : syracuseStep 1238127 = 1857191) B1857191
theorem B1238183 : Blo 1236436 1238183 := bstep (se 1 (by rfl) ⟨928637, by rfl⟩ : syracuseStep 1238183 = 1857275) B1857275
theorem B3130559 : Blo 1236436 3130559 := bstep (se 1 (by rfl) ⟨2347919, by rfl⟩ : syracuseStep 3130559 = 4695839) B4695839
theorem B1238207 : Blo 1236436 1238207 := bstep (se 1 (by rfl) ⟨928655, by rfl⟩ : syracuseStep 1238207 = 1857311) B1857311
theorem B1238239 : Blo 1236436 1238239 := bstep (se 1 (by rfl) ⟨928679, by rfl⟩ : syracuseStep 1238239 = 1857359) B1857359
theorem B1238319 : Blo 1236436 1238319 := bstep (se 1 (by rfl) ⟨928739, by rfl⟩ : syracuseStep 1238319 = 1857479) B1857479
theorem B4179383 : Blo 1236436 4179383 := bstep (se 1 (by rfl) ⟨3134537, by rfl⟩ : syracuseStep 4179383 = 6269075) B6269075
theorem B6964751 : Blo 1236436 6964751 := bstep (se 1 (by rfl) ⟨5223563, by rfl⟩ : syracuseStep 6964751 = 10447127) B10447127
theorem B5949035 : Blo 1236436 5949035 := bstep (se 1 (by rfl) ⟨4461776, by rfl⟩ : syracuseStep 5949035 = 8923553) B8923553
theorem B1320743 : Blo 1236436 1320743 := bstep (se 1 (by rfl) ⟨990557, by rfl⟩ : syracuseStep 1320743 = 1981115) B1981115
theorem B15853427 : Blo 1236436 15853427 := bstep (se 1 (by rfl) ⟨11890070, by rfl⟩ : syracuseStep 15853427 = 23780141) B23780141
theorem B3131257 : Blo 1236436 3131257 := bstep (se 2 (by rfl) ⟨1174221, by rfl⟩ : syracuseStep 3131257 = 2348443) B2348443
theorem B7145597 : Blo 1236436 7145597 := bstep (se 3 (by rfl) ⟨1339799, by rfl⟩ : syracuseStep 7145597 = 2679599) B2679599
theorem B10709135 : Blo 1236436 10709135 := bstep (se 1 (by rfl) ⟨8031851, by rfl⟩ : syracuseStep 10709135 = 16063703) B16063703
theorem B1673551 : Blo 1236436 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B7047607 : Blo 1236436 7047607 := bstep (se 1 (by rfl) ⟨5285705, by rfl⟩ : syracuseStep 7047607 = 10571411) B10571411
theorem B9398753 : Blo 1236436 9398753 := bstep (se 2 (by rfl) ⟨3524532, by rfl⟩ : syracuseStep 9398753 = 7049065) B7049065
theorem B1567279 : Blo 1236436 1567279 := bstep (se 1 (by rfl) ⟨1175459, by rfl⟩ : syracuseStep 1567279 = 2350919) B2350919
theorem B2230945 : Blo 1236436 2230945 := bstep (se 2 (by rfl) ⟨836604, by rfl⟩ : syracuseStep 2230945 = 1673209) B1673209
theorem B10038023 : Blo 1236436 10038023 := bstep (se 1 (by rfl) ⟨7528517, by rfl⟩ : syracuseStep 10038023 = 15057035) B15057035
theorem B35654525 : Blo 1236436 35654525 := bstep (se 3 (by rfl) ⟨6685223, by rfl⟩ : syracuseStep 35654525 = 13370447) B13370447
theorem B40668085 : Blo 1236436 40668085 := bstep (se 5 (by rfl) ⟨1906316, by rfl⟩ : syracuseStep 40668085 = 3812633) B3812633
theorem B4697129 : Blo 1236436 4697129 := bstep (se 2 (by rfl) ⟨1761423, by rfl⟩ : syracuseStep 4697129 = 3522847) B3522847
theorem B6261947 : Blo 1236436 6261947 := bstep (se 1 (by rfl) ⟨4696460, by rfl⟩ : syracuseStep 6261947 = 9392921) B9392921
theorem B4173065 : Blo 1236436 4173065 := bstep (se 2 (by rfl) ⟨1564899, by rfl⟩ : syracuseStep 4173065 = 3129799) B3129799
theorem B3173855 : Blo 1236436 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B1855079 : Blo 1236436 1855079 := bstep (se 1 (by rfl) ⟨1391309, by rfl⟩ : syracuseStep 1855079 = 2782619) B2782619
theorem B9522863 : Blo 1236436 9522863 := bstep (se 1 (by rfl) ⟨7142147, by rfl⟩ : syracuseStep 9522863 = 14284295) B14284295
theorem B16084655 : Blo 1236436 16084655 := bstep (se 1 (by rfl) ⟨12063491, by rfl⟩ : syracuseStep 16084655 = 24126983) B24126983
theorem B4697783 : Blo 1236436 4697783 := bstep (se 1 (by rfl) ⟨3523337, by rfl⟩ : syracuseStep 4697783 = 7046675) B7046675
theorem B5287619 : Blo 1236436 5287619 := bstep (se 1 (by rfl) ⟨3965714, by rfl⟩ : syracuseStep 5287619 = 7931429) B7931429
theorem B20082401 : Blo 1236436 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B2543483 : Blo 1236436 2543483 := bstep (se 1 (by rfl) ⟨1907612, by rfl⟩ : syracuseStep 2543483 = 3815225) B3815225
theorem B1855463 : Blo 1236436 1855463 := bstep (se 1 (by rfl) ⟨1391597, by rfl⟩ : syracuseStep 1855463 = 2783195) B2783195
theorem B20344841 : Blo 1236436 20344841 := bstep (se 2 (by rfl) ⟨7629315, by rfl⟩ : syracuseStep 20344841 = 15258631) B15258631
theorem B4763681 : Blo 1236436 4763681 := bstep (se 2 (by rfl) ⟨1786380, by rfl⟩ : syracuseStep 4763681 = 3572761) B3572761
theorem B1855583 : Blo 1236436 1855583 := bstep (se 1 (by rfl) ⟨1391687, by rfl⟩ : syracuseStep 1855583 = 2783375) B2783375
theorem B1855595 : Blo 1236436 1855595 := bstep (se 1 (by rfl) ⟨1391696, by rfl⟩ : syracuseStep 1855595 = 2783393) B2783393
theorem B1855643 : Blo 1236436 1855643 := bstep (se 1 (by rfl) ⟨1391732, by rfl⟩ : syracuseStep 1855643 = 2783465) B2783465
theorem B3961295 : Blo 1236436 3961295 := bstep (se 1 (by rfl) ⟨2970971, by rfl⟩ : syracuseStep 3961295 = 5941943) B5941943
theorem B2347859 : Blo 1236436 2347859 := bstep (se 1 (by rfl) ⟨1760894, by rfl⟩ : syracuseStep 2347859 = 3521789) B3521789
theorem B1856495 : Blo 1236436 1856495 := bstep (se 1 (by rfl) ⟨1392371, by rfl⟩ : syracuseStep 1856495 = 2784743) B2784743
theorem B2782313 : Blo 1236436 2782313 := bstep (se 2 (by rfl) ⟨1043367, by rfl⟩ : syracuseStep 2782313 = 2086735) B2086735
theorem B4699241 : Blo 1236436 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B1856879 : Blo 1236436 1856879 := bstep (se 1 (by rfl) ⟨1392659, by rfl⟩ : syracuseStep 1856879 = 2785319) B2785319
theorem B1856999 : Blo 1236436 1856999 := bstep (se 1 (by rfl) ⟨1392749, by rfl⟩ : syracuseStep 1856999 = 2785499) B2785499
theorem B2348527 : Blo 1236436 2348527 := bstep (se 1 (by rfl) ⟨1761395, by rfl⟩ : syracuseStep 2348527 = 3522791) B3522791
theorem B8467993 : Blo 1236436 8467993 := bstep (se 2 (by rfl) ⟨3175497, by rfl⟩ : syracuseStep 8467993 = 6350995) B6350995
theorem B1857161 : Blo 1236436 1857161 := bstep (se 2 (by rfl) ⟨696435, by rfl⟩ : syracuseStep 1857161 = 1392871) B1392871
theorem B1857179 : Blo 1236436 1857179 := bstep (se 1 (by rfl) ⟨1392884, by rfl⟩ : syracuseStep 1857179 = 2785769) B2785769
theorem B2782943 : Blo 1236436 2782943 := bstep (se 1 (by rfl) ⟨2087207, by rfl⟩ : syracuseStep 2782943 = 4174415) B4174415
theorem B2348831 : Blo 1236436 2348831 := bstep (se 1 (by rfl) ⟨1761623, by rfl⟩ : syracuseStep 2348831 = 3523247) B3523247
theorem B4175657 : Blo 1236436 4175657 := bstep (se 2 (by rfl) ⟨1565871, by rfl⟩ : syracuseStep 4175657 = 3131743) B3131743
theorem B1857371 : Blo 1236436 1857371 := bstep (se 1 (by rfl) ⟨1393028, by rfl⟩ : syracuseStep 1857371 = 2786057) B2786057
theorem B5289943 : Blo 1236436 5289943 := bstep (se 1 (by rfl) ⟨3967457, by rfl⟩ : syracuseStep 5289943 = 7934915) B7934915
theorem B5945345 : Blo 1236436 5945345 := bstep (se 2 (by rfl) ⟨2229504, by rfl⟩ : syracuseStep 5945345 = 4459009) B4459009
theorem B5281811 : Blo 1236436 5281811 := bstep (se 1 (by rfl) ⟨3961358, by rfl⟩ : syracuseStep 5281811 = 7922717) B7922717
theorem B2783303 : Blo 1236436 2783303 := bstep (se 1 (by rfl) ⟨2087477, by rfl⟩ : syracuseStep 2783303 = 4174955) B4174955
theorem B7043233 : Blo 1236436 7043233 := bstep (se 2 (by rfl) ⟨2641212, by rfl⟩ : syracuseStep 7043233 = 5282425) B5282425
theorem B2382239 : Blo 1236436 2382239 := bstep (se 1 (by rfl) ⟨1786679, by rfl⟩ : syracuseStep 2382239 = 3573359) B3573359
theorem B6027709 : Blo 1236436 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B35658215 : Blo 1236436 35658215 := bstep (se 1 (by rfl) ⟨26743661, by rfl⟩ : syracuseStep 35658215 = 53487323) B53487323
theorem B10566287 : Blo 1236436 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B2783969 : Blo 1236436 2783969 := bstep (se 2 (by rfl) ⟨1043988, by rfl⟩ : syracuseStep 2783969 = 2087977) B2087977
theorem B9403127 : Blo 1236436 9403127 := bstep (se 1 (by rfl) ⟨7052345, by rfl⟩ : syracuseStep 9403127 = 14104691) B14104691
theorem B1391431 : Blo 1236436 1391431 := bstep (se 1 (by rfl) ⟨1043573, by rfl⟩ : syracuseStep 1391431 = 2087147) B2087147
theorem B22903631 : Blo 1236436 22903631 := bstep (se 1 (by rfl) ⟨17177723, by rfl⟩ : syracuseStep 22903631 = 34355447) B34355447
theorem B2349947 : Blo 1236436 2349947 := bstep (se 1 (by rfl) ⟨1762460, by rfl⟩ : syracuseStep 2349947 = 3524921) B3524921
theorem B2784167 : Blo 1236436 2784167 := bstep (se 1 (by rfl) ⟨2088125, by rfl⟩ : syracuseStep 2784167 = 4176251) B4176251
theorem B2784347 : Blo 1236436 2784347 := bstep (se 1 (by rfl) ⟨2088260, by rfl⟩ : syracuseStep 2784347 = 4176521) B4176521
theorem B2972999 : Blo 1236436 2972999 := bstep (se 1 (by rfl) ⟨2229749, by rfl⟩ : syracuseStep 2972999 = 4459499) B4459499
theorem B1392079 : Blo 1236436 1392079 := bstep (se 1 (by rfl) ⟨1044059, by rfl⟩ : syracuseStep 1392079 = 2088119) B2088119
theorem B1236591 : Blo 1236436 1236591 := bstep (se 1 (by rfl) ⟨927443, by rfl⟩ : syracuseStep 1236591 = 1854887) B1854887
theorem B9395837 : Blo 1236436 9395837 := bstep (se 3 (by rfl) ⟨1761719, by rfl⟩ : syracuseStep 9395837 = 3523439) B3523439
theorem B1236647 : Blo 1236436 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B1392295 : Blo 1236436 1392295 := bstep (se 1 (by rfl) ⟨1044221, by rfl⟩ : syracuseStep 1392295 = 2088443) B2088443
theorem B13369063 : Blo 1236436 13369063 := bstep (se 1 (by rfl) ⟨10026797, by rfl⟩ : syracuseStep 13369063 = 20053595) B20053595
theorem B1236711 : Blo 1236436 1236711 := bstep (se 1 (by rfl) ⟨927533, by rfl⟩ : syracuseStep 1236711 = 1855067) B1855067
theorem B1236767 : Blo 1236436 1236767 := bstep (se 1 (by rfl) ⟨927575, by rfl⟩ : syracuseStep 1236767 = 1855151) B1855151
theorem B2785103 : Blo 1236436 2785103 := bstep (se 1 (by rfl) ⟨2088827, by rfl⟩ : syracuseStep 2785103 = 4177655) B4177655
theorem B1236847 : Blo 1236436 1236847 := bstep (se 1 (by rfl) ⟨927635, by rfl⟩ : syracuseStep 1236847 = 1855271) B1855271
theorem B10035101 : Blo 1236436 10035101 := bstep (se 3 (by rfl) ⟨1881581, by rfl⟩ : syracuseStep 10035101 = 3763163) B3763163
theorem B1236903 : Blo 1236436 1236903 := bstep (se 1 (by rfl) ⟨927677, by rfl⟩ : syracuseStep 1236903 = 1855355) B1855355
theorem B1392583 : Blo 1236436 1392583 := bstep (se 1 (by rfl) ⟨1044437, by rfl⟩ : syracuseStep 1392583 = 2088875) B2088875
theorem B1237055 : Blo 1236436 1237055 := bstep (se 1 (by rfl) ⟨927791, by rfl⟩ : syracuseStep 1237055 = 1855583) B1855583
theorem B1237063 : Blo 1236436 1237063 := bstep (se 1 (by rfl) ⟨927797, by rfl⟩ : syracuseStep 1237063 = 1855595) B1855595
theorem B1237095 : Blo 1236436 1237095 := bstep (se 1 (by rfl) ⟨927821, by rfl⟩ : syracuseStep 1237095 = 1855643) B1855643
theorem B45162629 : Blo 1236436 45162629 := bstep (se 4 (by rfl) ⟨4233996, by rfl⟩ : syracuseStep 45162629 = 8467993) B8467993
theorem B13386019 : Blo 1236436 13386019 := bstep (se 1 (by rfl) ⟨10039514, by rfl⟩ : syracuseStep 13386019 = 20079029) B20079029
theorem B2785697 : Blo 1236436 2785697 := bstep (se 2 (by rfl) ⟨1044636, by rfl⟩ : syracuseStep 2785697 = 2089273) B2089273
theorem B1565239 : Blo 1236436 1565239 := bstep (se 1 (by rfl) ⟨1173929, by rfl⟩ : syracuseStep 1565239 = 2347859) B2347859
theorem B9396809 : Blo 1236436 9396809 := bstep (se 2 (by rfl) ⟨3523803, by rfl⟩ : syracuseStep 9396809 = 7047607) B7047607
theorem B8036945 : Blo 1236436 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B1237663 : Blo 1236436 1237663 := bstep (se 1 (by rfl) ⟨928247, by rfl⟩ : syracuseStep 1237663 = 1856495) B1856495
theorem B2089705 : Blo 1236436 2089705 := bstep (se 2 (by rfl) ⟨783639, by rfl⟩ : syracuseStep 2089705 = 1567279) B1567279
theorem B1237919 : Blo 1236436 1237919 := bstep (se 1 (by rfl) ⟨928439, by rfl⟩ : syracuseStep 1237919 = 1856879) B1856879
theorem B2786255 : Blo 1236436 2786255 := bstep (se 1 (by rfl) ⟨2089691, by rfl⟩ : syracuseStep 2786255 = 4179383) B4179383
theorem B1237999 : Blo 1236436 1237999 := bstep (se 1 (by rfl) ⟨928499, by rfl⟩ : syracuseStep 1237999 = 1856999) B1856999
theorem B2786345 : Blo 1236436 2786345 := bstep (se 2 (by rfl) ⟨1044879, by rfl⟩ : syracuseStep 2786345 = 2089759) B2089759
theorem B3966023 : Blo 1236436 3966023 := bstep (se 1 (by rfl) ⟨2974517, by rfl⟩ : syracuseStep 3966023 = 5949035) B5949035
theorem B1238107 : Blo 1236436 1238107 := bstep (se 1 (by rfl) ⟨928580, by rfl⟩ : syracuseStep 1238107 = 1857161) B1857161
theorem B1238119 : Blo 1236436 1238119 := bstep (se 1 (by rfl) ⟨928589, by rfl⟩ : syracuseStep 1238119 = 1857179) B1857179
theorem B6259841 : Blo 1236436 6259841 := bstep (se 2 (by rfl) ⟨2347440, by rfl⟩ : syracuseStep 6259841 = 4694881) B4694881
theorem B1565887 : Blo 1236436 1565887 := bstep (se 1 (by rfl) ⟨1174415, by rfl⟩ : syracuseStep 1565887 = 2348831) B2348831
theorem B1238247 : Blo 1236436 1238247 := bstep (se 1 (by rfl) ⟨928685, by rfl⟩ : syracuseStep 1238247 = 1857371) B1857371
theorem B54224113 : Blo 1236436 54224113 := bstep (se 2 (by rfl) ⟨20334042, by rfl⟩ : syracuseStep 54224113 = 40668085) B40668085
theorem B10568951 : Blo 1236436 10568951 := bstep (se 1 (by rfl) ⟨7926713, by rfl⟩ : syracuseStep 10568951 = 15853427) B15853427
theorem B15861217 : Blo 1236436 15861217 := bstep (se 2 (by rfl) ⟨5947956, by rfl⟩ : syracuseStep 15861217 = 11895913) B11895913
theorem B3343997 : Blo 1236436 3343997 := bstep (se 3 (by rfl) ⟨626999, by rfl⟩ : syracuseStep 3343997 = 1253999) B1253999
theorem B15861581 : Blo 1236436 15861581 := bstep (se 3 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 15861581 = 5948093) B5948093
theorem B6268751 : Blo 1236436 6268751 := bstep (se 1 (by rfl) ⟨4701563, by rfl⟩ : syracuseStep 6268751 = 9403127) B9403127
theorem B14100317 : Blo 1236436 14100317 := bstep (se 3 (by rfl) ⟨2643809, by rfl⟩ : syracuseStep 14100317 = 5287619) B5287619
theorem B1566631 : Blo 1236436 1566631 := bstep (se 1 (by rfl) ⟨1174973, by rfl⟩ : syracuseStep 1566631 = 2349947) B2349947
theorem B3131369 : Blo 1236436 3131369 := bstep (se 2 (by rfl) ⟨1174263, by rfl⟩ : syracuseStep 3131369 = 2348527) B2348527
theorem B3131419 : Blo 1236436 3131419 := bstep (se 1 (by rfl) ⟨2348564, by rfl⟩ : syracuseStep 3131419 = 4697129) B4697129
theorem B3131855 : Blo 1236436 3131855 := bstep (se 1 (by rfl) ⟨2348891, by rfl⟩ : syracuseStep 3131855 = 4697783) B4697783
theorem B13388267 : Blo 1236436 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B9390977 : Blo 1236436 9390977 := bstep (se 2 (by rfl) ⟨3521616, by rfl⟩ : syracuseStep 9390977 = 7043233) B7043233
theorem B2640863 : Blo 1236436 2640863 := bstep (se 1 (by rfl) ⟨1980647, by rfl⟩ : syracuseStep 2640863 = 3961295) B3961295
theorem B2231401 : Blo 1236436 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B4697297 : Blo 1236436 4697297 := bstep (se 2 (by rfl) ⟨1761486, by rfl⟩ : syracuseStep 4697297 = 3522973) B3522973
theorem B4173011 : Blo 1236436 4173011 := bstep (se 1 (by rfl) ⟨3129758, by rfl⟩ : syracuseStep 4173011 = 6259517) B6259517
theorem B5942575 : Blo 1236436 5942575 := bstep (se 1 (by rfl) ⟨4456931, by rfl⟩ : syracuseStep 5942575 = 8913863) B8913863
theorem B1854875 : Blo 1236436 1854875 := bstep (se 1 (by rfl) ⟨1391156, by rfl⟩ : syracuseStep 1854875 = 2782313) B2782313
theorem B3132827 : Blo 1236436 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B6352637 : Blo 1236436 6352637 := bstep (se 3 (by rfl) ⟨1191119, by rfl⟩ : syracuseStep 6352637 = 2382239) B2382239
theorem B1855241 : Blo 1236436 1855241 := bstep (se 2 (by rfl) ⟨695715, by rfl⟩ : syracuseStep 1855241 = 1391431) B1391431
theorem B1855295 : Blo 1236436 1855295 := bstep (se 1 (by rfl) ⟨1391471, by rfl⟩ : syracuseStep 1855295 = 2782943) B2782943
theorem B1855535 : Blo 1236436 1855535 := bstep (se 1 (by rfl) ⟨1391651, by rfl⟩ : syracuseStep 1855535 = 2783303) B2783303
theorem B4763731 : Blo 1236436 4763731 := bstep (se 1 (by rfl) ⟨3572798, by rfl⟩ : syracuseStep 4763731 = 7145597) B7145597
theorem B7139423 : Blo 1236436 7139423 := bstep (se 1 (by rfl) ⟨5354567, by rfl⟩ : syracuseStep 7139423 = 10709135) B10709135
theorem B4698557 : Blo 1236436 4698557 := bstep (se 3 (by rfl) ⟨880979, by rfl⟩ : syracuseStep 4698557 = 1761959) B1761959
theorem B1855979 : Blo 1236436 1855979 := bstep (se 1 (by rfl) ⟨1391984, by rfl⟩ : syracuseStep 1855979 = 2783969) B2783969
theorem B23769683 : Blo 1236436 23769683 := bstep (se 1 (by rfl) ⟨17827262, by rfl⟩ : syracuseStep 23769683 = 35654525) B35654525
theorem B1856105 : Blo 1236436 1856105 := bstep (se 2 (by rfl) ⟨696039, by rfl⟩ : syracuseStep 1856105 = 1392079) B1392079
theorem B1856111 : Blo 1236436 1856111 := bstep (se 1 (by rfl) ⟨1392083, by rfl⟩ : syracuseStep 1856111 = 2784167) B2784167
theorem B1856231 : Blo 1236436 1856231 := bstep (se 1 (by rfl) ⟨1392173, by rfl⟩ : syracuseStep 1856231 = 2784347) B2784347
theorem B4174631 : Blo 1236436 4174631 := bstep (se 1 (by rfl) ⟨3130973, by rfl⟩ : syracuseStep 4174631 = 6261947) B6261947
theorem B2782043 : Blo 1236436 2782043 := bstep (se 1 (by rfl) ⟨2086532, by rfl⟩ : syracuseStep 2782043 = 4173065) B4173065
theorem B1856393 : Blo 1236436 1856393 := bstep (se 2 (by rfl) ⟨696147, by rfl⟩ : syracuseStep 1856393 = 1392295) B1392295
theorem B33854453 : Blo 1236436 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B26760269 : Blo 1236436 26760269 := bstep (se 3 (by rfl) ⟨5017550, by rfl⟩ : syracuseStep 26760269 = 10035101) B10035101
theorem B6263891 : Blo 1236436 6263891 := bstep (se 1 (by rfl) ⟨4697918, by rfl⟩ : syracuseStep 6263891 = 9395837) B9395837
theorem B4175009 : Blo 1236436 4175009 := bstep (se 2 (by rfl) ⟨1565628, by rfl⟩ : syracuseStep 4175009 = 3131257) B3131257
theorem B1856735 : Blo 1236436 1856735 := bstep (se 1 (by rfl) ⟨1392551, by rfl⟩ : syracuseStep 1856735 = 2785103) B2785103
theorem B1856777 : Blo 1236436 1856777 := bstep (se 2 (by rfl) ⟨696291, by rfl⟩ : syracuseStep 1856777 = 1392583) B1392583
theorem B13563227 : Blo 1236436 13563227 := bstep (se 1 (by rfl) ⟨10172420, by rfl⟩ : syracuseStep 13563227 = 20344841) B20344841
theorem B3175787 : Blo 1236436 3175787 := bstep (se 1 (by rfl) ⟨2381840, by rfl⟩ : syracuseStep 3175787 = 4763681) B4763681
theorem B2971279 : Blo 1236436 2971279 := bstep (se 1 (by rfl) ⟨2228459, by rfl⟩ : syracuseStep 2971279 = 4456919) B4456919
theorem B17847971 : Blo 1236436 17847971 := bstep (se 1 (by rfl) ⟨13385978, by rfl⟩ : syracuseStep 17847971 = 26771957) B26771957
theorem B1857215 : Blo 1236436 1857215 := bstep (se 1 (by rfl) ⟨1392911, by rfl⟩ : syracuseStep 1857215 = 2785823) B2785823
theorem B8034011 : Blo 1236436 8034011 := bstep (se 1 (by rfl) ⟨6025508, by rfl⟩ : syracuseStep 8034011 = 12051017) B12051017
theorem B1857257 : Blo 1236436 1857257 := bstep (se 2 (by rfl) ⟨696471, by rfl⟩ : syracuseStep 1857257 = 1392943) B1392943
theorem B1857263 : Blo 1236436 1857263 := bstep (se 1 (by rfl) ⟨1392947, by rfl⟩ : syracuseStep 1857263 = 2785895) B2785895
theorem B47593493 : Blo 1236436 47593493 := bstep (se 6 (by rfl) ⟨1115472, by rfl⟩ : syracuseStep 47593493 = 2230945) B2230945
theorem B2087039 : Blo 1236436 2087039 := bstep (se 1 (by rfl) ⟨1565279, by rfl⟩ : syracuseStep 2087039 = 3130559) B3130559
theorem B4643167 : Blo 1236436 4643167 := bstep (se 1 (by rfl) ⟨3482375, by rfl⟩ : syracuseStep 4643167 = 6964751) B6964751
theorem B2783771 : Blo 1236436 2783771 := bstep (se 1 (by rfl) ⟨2087828, by rfl⟩ : syracuseStep 2783771 = 4175657) B4175657
theorem B3963563 : Blo 1236436 3963563 := bstep (se 1 (by rfl) ⟨2972672, by rfl⟩ : syracuseStep 3963563 = 5945345) B5945345
theorem B3521207 : Blo 1236436 3521207 := bstep (se 1 (by rfl) ⟨2640905, by rfl⟩ : syracuseStep 3521207 = 5281811) B5281811
theorem B6265835 : Blo 1236436 6265835 := bstep (se 1 (by rfl) ⟨4699376, by rfl⟩ : syracuseStep 6265835 = 9398753) B9398753
theorem B23772143 : Blo 1236436 23772143 := bstep (se 1 (by rfl) ⟨17829107, by rfl⟩ : syracuseStep 23772143 = 35658215) B35658215
theorem B7044191 : Blo 1236436 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B6692015 : Blo 1236436 6692015 := bstep (se 1 (by rfl) ⟨5019011, by rfl⟩ : syracuseStep 6692015 = 10038023) B10038023
theorem B15269087 : Blo 1236436 15269087 := bstep (se 1 (by rfl) ⟨11451815, by rfl⟩ : syracuseStep 15269087 = 22903631) B22903631
theorem B3521981 : Blo 1236436 3521981 := bstep (se 3 (by rfl) ⟨660371, by rfl⟩ : syracuseStep 3521981 = 1320743) B1320743
theorem B1981999 : Blo 1236436 1981999 := bstep (se 1 (by rfl) ⟨1486499, by rfl⟩ : syracuseStep 1981999 = 2972999) B2972999
theorem B17825417 : Blo 1236436 17825417 := bstep (se 2 (by rfl) ⟨6684531, by rfl⟩ : syracuseStep 17825417 = 13369063) B13369063
theorem B1236719 : Blo 1236436 1236719 := bstep (se 1 (by rfl) ⟨927539, by rfl⟩ : syracuseStep 1236719 = 1855079) B1855079
theorem B6348575 : Blo 1236436 6348575 := bstep (se 1 (by rfl) ⟨4761431, by rfl⟩ : syracuseStep 6348575 = 9522863) B9522863
theorem B10723103 : Blo 1236436 10723103 := bstep (se 1 (by rfl) ⟨8042327, by rfl⟩ : syracuseStep 10723103 = 16084655) B16084655
theorem B1695655 : Blo 1236436 1695655 := bstep (se 1 (by rfl) ⟨1271741, by rfl⟩ : syracuseStep 1695655 = 2543483) B2543483
theorem B7053257 : Blo 1236436 7053257 := bstep (se 2 (by rfl) ⟨2644971, by rfl⟩ : syracuseStep 7053257 = 5289943) B5289943
theorem B1236975 : Blo 1236436 1236975 := bstep (se 1 (by rfl) ⟨927731, by rfl⟩ : syracuseStep 1236975 = 1855463) B1855463
theorem B1237023 : Blo 1236436 1237023 := bstep (se 1 (by rfl) ⟨927767, by rfl⟩ : syracuseStep 1237023 = 1855535) B1855535
theorem B4759615 : Blo 1236436 4759615 := bstep (se 1 (by rfl) ⟨3569711, by rfl⟩ : syracuseStep 4759615 = 7139423) B7139423
theorem B1237319 : Blo 1236436 1237319 := bstep (se 1 (by rfl) ⟨927989, by rfl⟩ : syracuseStep 1237319 = 1855979) B1855979
theorem B5357963 : Blo 1236436 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B1237403 : Blo 1236436 1237403 := bstep (se 1 (by rfl) ⟨928052, by rfl⟩ : syracuseStep 1237403 = 1856105) B1856105
theorem B1237407 : Blo 1236436 1237407 := bstep (se 1 (by rfl) ⟨928055, by rfl⟩ : syracuseStep 1237407 = 1856111) B1856111
theorem B1237487 : Blo 1236436 1237487 := bstep (se 1 (by rfl) ⟨928115, by rfl⟩ : syracuseStep 1237487 = 1856231) B1856231
theorem B1237595 : Blo 1236436 1237595 := bstep (se 1 (by rfl) ⟨928196, by rfl⟩ : syracuseStep 1237595 = 1856393) B1856393
theorem B22569635 : Blo 1236436 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B1237823 : Blo 1236436 1237823 := bstep (se 1 (by rfl) ⟨928367, by rfl⟩ : syracuseStep 1237823 = 1856735) B1856735
theorem B7045967 : Blo 1236436 7045967 := bstep (se 1 (by rfl) ⟨5284475, by rfl⟩ : syracuseStep 7045967 = 10568951) B10568951
theorem B1237851 : Blo 1236436 1237851 := bstep (se 1 (by rfl) ⟨928388, by rfl⟩ : syracuseStep 1237851 = 1856777) B1856777
theorem B2786273 : Blo 1236436 2786273 := bstep (se 2 (by rfl) ⟨1044852, by rfl⟩ : syracuseStep 2786273 = 2089705) B2089705
theorem B2229331 : Blo 1236436 2229331 := bstep (se 1 (by rfl) ⟨1671998, by rfl⟩ : syracuseStep 2229331 = 3343997) B3343997
theorem B1238143 : Blo 1236436 1238143 := bstep (se 1 (by rfl) ⟨928607, by rfl⟩ : syracuseStep 1238143 = 1857215) B1857215
theorem B1238171 : Blo 1236436 1238171 := bstep (se 1 (by rfl) ⟨928628, by rfl⟩ : syracuseStep 1238171 = 1857257) B1857257
theorem B1238175 : Blo 1236436 1238175 := bstep (se 1 (by rfl) ⟨928631, by rfl⟩ : syracuseStep 1238175 = 1857263) B1857263
theorem B4179167 : Blo 1236436 4179167 := bstep (se 1 (by rfl) ⟨3134375, by rfl⟩ : syracuseStep 4179167 = 6268751) B6268751
theorem B35702045 : Blo 1236436 35702045 := bstep (se 3 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 35702045 = 13388267) B13388267
theorem B31728995 : Blo 1236436 31728995 := bstep (se 1 (by rfl) ⟨23796746, by rfl⟩ : syracuseStep 31728995 = 47593493) B47593493
theorem B2975201 : Blo 1236436 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B7923433 : Blo 1236436 7923433 := bstep (se 2 (by rfl) ⟨2971287, by rfl⟩ : syracuseStep 7923433 = 5942575) B5942575
theorem B6260651 : Blo 1236436 6260651 := bstep (se 1 (by rfl) ⟨4695488, by rfl⟩ : syracuseStep 6260651 = 9390977) B9390977
theorem B4696127 : Blo 1236436 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B3131531 : Blo 1236436 3131531 := bstep (se 1 (by rfl) ⟨2348648, by rfl⟩ : syracuseStep 3131531 = 4697297) B4697297
theorem B30108419 : Blo 1236436 30108419 := bstep (se 1 (by rfl) ⟨22581314, by rfl⟩ : syracuseStep 30108419 = 45162629) B45162629
theorem B6351641 : Blo 1236436 6351641 := bstep (se 2 (by rfl) ⟨2381865, by rfl⟩ : syracuseStep 6351641 = 4763731) B4763731
theorem B10570661 : Blo 1236436 10570661 := bstep (se 4 (by rfl) ⟨990999, by rfl⟩ : syracuseStep 10570661 = 1981999) B1981999
theorem B3132371 : Blo 1236436 3132371 := bstep (se 1 (by rfl) ⟨2349278, by rfl⟩ : syracuseStep 3132371 = 4698557) B4698557
theorem B15846455 : Blo 1236436 15846455 := bstep (se 1 (by rfl) ⟨11884841, by rfl⟩ : syracuseStep 15846455 = 23769683) B23769683
theorem B17845373 : Blo 1236436 17845373 := bstep (se 3 (by rfl) ⟨3346007, by rfl⟩ : syracuseStep 17845373 = 6692015) B6692015
theorem B1854695 : Blo 1236436 1854695 := bstep (se 1 (by rfl) ⟨1391021, by rfl⟩ : syracuseStep 1854695 = 2782043) B2782043
theorem B40717565 : Blo 1236436 40717565 := bstep (se 3 (by rfl) ⟨7634543, by rfl⟩ : syracuseStep 40717565 = 15269087) B15269087
theorem B4173227 : Blo 1236436 4173227 := bstep (se 1 (by rfl) ⟨3129920, by rfl⟩ : syracuseStep 4173227 = 6259841) B6259841
theorem B2117191 : Blo 1236436 2117191 := bstep (se 1 (by rfl) ⟨1587893, by rfl⟩ : syracuseStep 2117191 = 3175787) B3175787
theorem B11898647 : Blo 1236436 11898647 := bstep (se 1 (by rfl) ⟨8923985, by rfl⟩ : syracuseStep 11898647 = 17847971) B17847971
theorem B9391949 : Blo 1236436 9391949 := bstep (se 3 (by rfl) ⟨1760990, by rfl⟩ : syracuseStep 9391949 = 3521981) B3521981
theorem B9400211 : Blo 1236436 9400211 := bstep (se 1 (by rfl) ⟨7050158, by rfl⟩ : syracuseStep 9400211 = 14100317) B14100317
theorem B72298817 : Blo 1236436 72298817 := bstep (se 2 (by rfl) ⟨27112056, by rfl⟩ : syracuseStep 72298817 = 54224113) B54224113
theorem B1855847 : Blo 1236436 1855847 := bstep (se 1 (by rfl) ⟨1391885, by rfl⟩ : syracuseStep 1855847 = 2783771) B2783771
theorem B2642375 : Blo 1236436 2642375 := bstep (se 1 (by rfl) ⟨1981781, by rfl⟩ : syracuseStep 2642375 = 3963563) B3963563
theorem B2347471 : Blo 1236436 2347471 := bstep (se 1 (by rfl) ⟨1760603, by rfl⟩ : syracuseStep 2347471 = 3521207) B3521207
theorem B21148289 : Blo 1236436 21148289 := bstep (se 2 (by rfl) ⟨7930608, by rfl⟩ : syracuseStep 21148289 = 15861217) B15861217
theorem B15848095 : Blo 1236436 15848095 := bstep (se 1 (by rfl) ⟨11886071, by rfl⟩ : syracuseStep 15848095 = 23772143) B23772143
theorem B16929533 : Blo 1236436 16929533 := bstep (se 3 (by rfl) ⟨3174287, by rfl⟩ : syracuseStep 16929533 = 6348575) B6348575
theorem B2782007 : Blo 1236436 2782007 := bstep (se 1 (by rfl) ⟨2086505, by rfl⟩ : syracuseStep 2782007 = 4173011) B4173011
theorem B3961705 : Blo 1236436 3961705 := bstep (se 2 (by rfl) ⟨1485639, by rfl⟩ : syracuseStep 3961705 = 2971279) B2971279
theorem B11883611 : Blo 1236436 11883611 := bstep (se 1 (by rfl) ⟨8912708, by rfl⟩ : syracuseStep 11883611 = 17825417) B17825417
theorem B7148735 : Blo 1236436 7148735 := bstep (se 1 (by rfl) ⟨5361551, by rfl⟩ : syracuseStep 7148735 = 10723103) B10723103
theorem B7042301 : Blo 1236436 7042301 := bstep (se 3 (by rfl) ⟨1320431, by rfl⟩ : syracuseStep 7042301 = 2640863) B2640863
theorem B67761461 : Blo 1236436 67761461 := bstep (se 5 (by rfl) ⟨3176318, by rfl⟩ : syracuseStep 67761461 = 6352637) B6352637
theorem B4175225 : Blo 1236436 4175225 := bstep (se 2 (by rfl) ⟨1565709, by rfl⟩ : syracuseStep 4175225 = 3131419) B3131419
theorem B1857131 : Blo 1236436 1857131 := bstep (se 1 (by rfl) ⟨1392848, by rfl⟩ : syracuseStep 1857131 = 2785697) B2785697
theorem B17848025 : Blo 1236436 17848025 := bstep (se 2 (by rfl) ⟨6693009, by rfl⟩ : syracuseStep 17848025 = 13386019) B13386019
theorem B6264539 : Blo 1236436 6264539 := bstep (se 1 (by rfl) ⟨4698404, by rfl⟩ : syracuseStep 6264539 = 9396809) B9396809
theorem B6190889 : Blo 1236436 6190889 := bstep (se 2 (by rfl) ⟨2321583, by rfl⟩ : syracuseStep 6190889 = 4643167) B4643167
theorem B2783087 : Blo 1236436 2783087 := bstep (se 1 (by rfl) ⟨2087315, by rfl⟩ : syracuseStep 2783087 = 4174631) B4174631
theorem B1857503 : Blo 1236436 1857503 := bstep (se 1 (by rfl) ⟨1393127, by rfl⟩ : syracuseStep 1857503 = 2786255) B2786255
theorem B1857563 : Blo 1236436 1857563 := bstep (se 1 (by rfl) ⟨1393172, by rfl⟩ : syracuseStep 1857563 = 2786345) B2786345
theorem B2644015 : Blo 1236436 2644015 := bstep (se 1 (by rfl) ⟨1983011, by rfl⟩ : syracuseStep 2644015 = 3966023) B3966023
theorem B17840179 : Blo 1236436 17840179 := bstep (se 1 (by rfl) ⟨13380134, by rfl⟩ : syracuseStep 17840179 = 26760269) B26760269
theorem B4175927 : Blo 1236436 4175927 := bstep (se 1 (by rfl) ⟨3131945, by rfl⟩ : syracuseStep 4175927 = 6263891) B6263891
theorem B2086985 : Blo 1236436 2086985 := bstep (se 2 (by rfl) ⟨782619, by rfl⟩ : syracuseStep 2086985 = 1565239) B1565239
theorem B2783339 : Blo 1236436 2783339 := bstep (se 1 (by rfl) ⟨2087504, by rfl⟩ : syracuseStep 2783339 = 4175009) B4175009
theorem B9042151 : Blo 1236436 9042151 := bstep (se 1 (by rfl) ⟨6781613, by rfl⟩ : syracuseStep 9042151 = 13563227) B13563227
theorem B5356007 : Blo 1236436 5356007 := bstep (se 1 (by rfl) ⟨4017005, by rfl⟩ : syracuseStep 5356007 = 8034011) B8034011
theorem B10574387 : Blo 1236436 10574387 := bstep (se 1 (by rfl) ⟨7930790, by rfl⟩ : syracuseStep 10574387 = 15861581) B15861581
theorem B2087579 : Blo 1236436 2087579 := bstep (se 1 (by rfl) ⟨1565684, by rfl⟩ : syracuseStep 2087579 = 3131369) B3131369
theorem B1391359 : Blo 1236436 1391359 := bstep (se 1 (by rfl) ⟨1043519, by rfl⟩ : syracuseStep 1391359 = 2087039) B2087039
theorem B2087849 : Blo 1236436 2087849 := bstep (se 2 (by rfl) ⟨782943, by rfl⟩ : syracuseStep 2087849 = 1565887) B1565887
theorem B2087903 : Blo 1236436 2087903 := bstep (se 1 (by rfl) ⟨1565927, by rfl⟩ : syracuseStep 2087903 = 3131855) B3131855
theorem B4177223 : Blo 1236436 4177223 := bstep (se 1 (by rfl) ⟨3132917, by rfl⟩ : syracuseStep 4177223 = 6265835) B6265835
theorem B9043493 : Blo 1236436 9043493 := bstep (se 4 (by rfl) ⟨847827, by rfl⟩ : syracuseStep 9043493 = 1695655) B1695655
theorem B1236583 : Blo 1236436 1236583 := bstep (se 1 (by rfl) ⟨927437, by rfl⟩ : syracuseStep 1236583 = 1854875) B1854875
theorem B2088551 : Blo 1236436 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B1236827 : Blo 1236436 1236827 := bstep (se 1 (by rfl) ⟨927620, by rfl⟩ : syracuseStep 1236827 = 1855241) B1855241
theorem B1236863 : Blo 1236436 1236863 := bstep (se 1 (by rfl) ⟨927647, by rfl⟩ : syracuseStep 1236863 = 1855295) B1855295
theorem B2088841 : Blo 1236436 2088841 := bstep (se 2 (by rfl) ⟨783315, by rfl⟩ : syracuseStep 2088841 = 1566631) B1566631
theorem B4702171 : Blo 1236436 4702171 := bstep (se 1 (by rfl) ⟨3526628, by rfl⟩ : syracuseStep 4702171 = 7053257) B7053257
theorem B1237231 : Blo 1236436 1237231 := bstep (se 1 (by rfl) ⟨927923, by rfl⟩ : syracuseStep 1237231 = 1855847) B1855847
theorem B3571975 : Blo 1236436 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B1761583 : Blo 1236436 1761583 := bstep (se 1 (by rfl) ⟨1321187, by rfl⟩ : syracuseStep 1761583 = 2642375) B2642375
theorem B14098859 : Blo 1236436 14098859 := bstep (se 1 (by rfl) ⟨10574144, by rfl⟩ : syracuseStep 14098859 = 21148289) B21148289
theorem B3129961 : Blo 1236436 3129961 := bstep (se 2 (by rfl) ⟨1173735, by rfl⟩ : syracuseStep 3129961 = 2347471) B2347471
theorem B2786111 : Blo 1236436 2786111 := bstep (se 1 (by rfl) ⟨2089583, by rfl⟩ : syracuseStep 2786111 = 4179167) B4179167
theorem B4694867 : Blo 1236436 4694867 := bstep (se 1 (by rfl) ⟨3521150, by rfl⟩ : syracuseStep 4694867 = 7042301) B7042301
theorem B21152663 : Blo 1236436 21152663 := bstep (se 1 (by rfl) ⟨15864497, by rfl⟩ : syracuseStep 21152663 = 31728995) B31728995
theorem B1983467 : Blo 1236436 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B1238087 : Blo 1236436 1238087 := bstep (se 1 (by rfl) ⟨928565, by rfl⟩ : syracuseStep 1238087 = 1857131) B1857131
theorem B1238335 : Blo 1236436 1238335 := bstep (se 1 (by rfl) ⟨928751, by rfl⟩ : syracuseStep 1238335 = 1857503) B1857503
theorem B1238375 : Blo 1236436 1238375 := bstep (se 1 (by rfl) ⟨928781, by rfl⟩ : syracuseStep 1238375 = 1857563) B1857563
theorem B3130751 : Blo 1236436 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B20072279 : Blo 1236436 20072279 := bstep (se 1 (by rfl) ⟨15054209, by rfl⟩ : syracuseStep 20072279 = 30108419) B30108419
theorem B7047107 : Blo 1236436 7047107 := bstep (se 1 (by rfl) ⟨5285330, by rfl⟩ : syracuseStep 7047107 = 10570661) B10570661
theorem B11896915 : Blo 1236436 11896915 := bstep (se 1 (by rfl) ⟨8922686, by rfl⟩ : syracuseStep 11896915 = 17845373) B17845373
theorem B16509037 : Blo 1236436 16509037 := bstep (se 3 (by rfl) ⟨3095444, by rfl⟩ : syracuseStep 16509037 = 6190889) B6190889
theorem B7932431 : Blo 1236436 7932431 := bstep (se 1 (by rfl) ⟨5949323, by rfl⟩ : syracuseStep 7932431 = 11898647) B11898647
theorem B6261299 : Blo 1236436 6261299 := bstep (se 1 (by rfl) ⟨4695974, by rfl⟩ : syracuseStep 6261299 = 9391949) B9391949
theorem B6269561 : Blo 1236436 6269561 := bstep (se 2 (by rfl) ⟨2351085, by rfl⟩ : syracuseStep 6269561 = 4702171) B4702171
theorem B3525353 : Blo 1236436 3525353 := bstep (se 2 (by rfl) ⟨1322007, by rfl⟩ : syracuseStep 3525353 = 2644015) B2644015
theorem B31689629 : Blo 1236436 31689629 := bstep (se 3 (by rfl) ⟨5941805, by rfl⟩ : syracuseStep 31689629 = 11883611) B11883611
theorem B1854671 : Blo 1236436 1854671 := bstep (se 1 (by rfl) ⟨1391003, by rfl⟩ : syracuseStep 1854671 = 2782007) B2782007
theorem B4697311 : Blo 1236436 4697311 := bstep (se 1 (by rfl) ⟨3522983, by rfl⟩ : syracuseStep 4697311 = 7045967) B7045967
theorem B23801363 : Blo 1236436 23801363 := bstep (se 1 (by rfl) ⟨17851022, by rfl⟩ : syracuseStep 23801363 = 35702045) B35702045
theorem B45174307 : Blo 1236436 45174307 := bstep (se 1 (by rfl) ⟨33880730, by rfl⟩ : syracuseStep 45174307 = 67761461) B67761461
theorem B21130793 : Blo 1236436 21130793 := bstep (se 2 (by rfl) ⟨7924047, by rfl⟩ : syracuseStep 21130793 = 15848095) B15848095
theorem B1855145 : Blo 1236436 1855145 := bstep (se 2 (by rfl) ⟨695679, by rfl⟩ : syracuseStep 1855145 = 1391359) B1391359
theorem B11898683 : Blo 1236436 11898683 := bstep (se 1 (by rfl) ⟨8924012, by rfl⟩ : syracuseStep 11898683 = 17848025) B17848025
theorem B1855391 : Blo 1236436 1855391 := bstep (se 1 (by rfl) ⟨1391543, by rfl⟩ : syracuseStep 1855391 = 2783087) B2783087
theorem B4173767 : Blo 1236436 4173767 := bstep (se 1 (by rfl) ⟨3130325, by rfl⟩ : syracuseStep 4173767 = 6260651) B6260651
theorem B1855559 : Blo 1236436 1855559 := bstep (se 1 (by rfl) ⟨1391669, by rfl⟩ : syracuseStep 1855559 = 2783339) B2783339
theorem B7049591 : Blo 1236436 7049591 := bstep (se 1 (by rfl) ⟨5287193, by rfl⟩ : syracuseStep 7049591 = 10574387) B10574387
theorem B10564303 : Blo 1236436 10564303 := bstep (se 1 (by rfl) ⟨7923227, by rfl⟩ : syracuseStep 10564303 = 15846455) B15846455
theorem B2822921 : Blo 1236436 2822921 := bstep (se 2 (by rfl) ⟨1058595, by rfl⟩ : syracuseStep 2822921 = 2117191) B2117191
theorem B27145043 : Blo 1236436 27145043 := bstep (se 1 (by rfl) ⟨20358782, by rfl⟩ : syracuseStep 27145043 = 40717565) B40717565
theorem B2782151 : Blo 1236436 2782151 := bstep (se 1 (by rfl) ⟨2086613, by rfl⟩ : syracuseStep 2782151 = 4173227) B4173227
theorem B10564577 : Blo 1236436 10564577 := bstep (se 2 (by rfl) ⟨3961716, by rfl⟩ : syracuseStep 10564577 = 7923433) B7923433
theorem B23786905 : Blo 1236436 23786905 := bstep (se 2 (by rfl) ⟨8920089, by rfl⟩ : syracuseStep 23786905 = 17840179) B17840179
theorem B6346153 : Blo 1236436 6346153 := bstep (se 2 (by rfl) ⟨2379807, by rfl⟩ : syracuseStep 6346153 = 4759615) B4759615
theorem B48199211 : Blo 1236436 48199211 := bstep (se 1 (by rfl) ⟨36149408, by rfl⟩ : syracuseStep 48199211 = 72298817) B72298817
theorem B12056201 : Blo 1236436 12056201 := bstep (se 2 (by rfl) ⟨4521075, by rfl⟩ : syracuseStep 12056201 = 9042151) B9042151
theorem B1857515 : Blo 1236436 1857515 := bstep (se 1 (by rfl) ⟨1393136, by rfl⟩ : syracuseStep 1857515 = 2786273) B2786273
theorem B4765823 : Blo 1236436 4765823 := bstep (se 1 (by rfl) ⟨3574367, by rfl⟩ : syracuseStep 4765823 = 7148735) B7148735
theorem B2783483 : Blo 1236436 2783483 := bstep (se 1 (by rfl) ⟨2087612, by rfl⟩ : syracuseStep 2783483 = 4175225) B4175225
theorem B5282273 : Blo 1236436 5282273 := bstep (se 2 (by rfl) ⟨1980852, by rfl⟩ : syracuseStep 5282273 = 3961705) B3961705
theorem B4176359 : Blo 1236436 4176359 := bstep (se 1 (by rfl) ⟨3132269, by rfl⟩ : syracuseStep 4176359 = 6264539) B6264539
theorem B2783951 : Blo 1236436 2783951 := bstep (se 1 (by rfl) ⟨2087963, by rfl⟩ : syracuseStep 2783951 = 4175927) B4175927
theorem B1391323 : Blo 1236436 1391323 := bstep (se 1 (by rfl) ⟨1043492, by rfl⟩ : syracuseStep 1391323 = 2086985) B2086985
theorem B2087687 : Blo 1236436 2087687 := bstep (se 1 (by rfl) ⟨1565765, by rfl⟩ : syracuseStep 2087687 = 3131531) B3131531
theorem B24115981 : Blo 1236436 24115981 := bstep (se 3 (by rfl) ⟨4521746, by rfl⟩ : syracuseStep 24115981 = 9043493) B9043493
theorem B2972441 : Blo 1236436 2972441 := bstep (se 2 (by rfl) ⟨1114665, by rfl⟩ : syracuseStep 2972441 = 2229331) B2229331
theorem B3570671 : Blo 1236436 3570671 := bstep (se 1 (by rfl) ⟨2678003, by rfl⟩ : syracuseStep 3570671 = 5356007) B5356007
theorem B60185693 : Blo 1236436 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B1391719 : Blo 1236436 1391719 := bstep (se 1 (by rfl) ⟨1043789, by rfl⟩ : syracuseStep 1391719 = 2087579) B2087579
theorem B4234427 : Blo 1236436 4234427 := bstep (se 1 (by rfl) ⟨3175820, by rfl⟩ : syracuseStep 4234427 = 6351641) B6351641
theorem B1391899 : Blo 1236436 1391899 := bstep (se 1 (by rfl) ⟨1043924, by rfl⟩ : syracuseStep 1391899 = 2087849) B2087849
theorem B2088247 : Blo 1236436 2088247 := bstep (se 1 (by rfl) ⟨1566185, by rfl⟩ : syracuseStep 2088247 = 3132371) B3132371
theorem B1391935 : Blo 1236436 1391935 := bstep (se 1 (by rfl) ⟨1043951, by rfl⟩ : syracuseStep 1391935 = 2087903) B2087903
theorem B45145421 : Blo 1236436 45145421 := bstep (se 3 (by rfl) ⟨8464766, by rfl⟩ : syracuseStep 45145421 = 16929533) B16929533
theorem B1236463 : Blo 1236436 1236463 := bstep (se 1 (by rfl) ⟨927347, by rfl⟩ : syracuseStep 1236463 = 1854695) B1854695
theorem B2784815 : Blo 1236436 2784815 := bstep (se 1 (by rfl) ⟨2088611, by rfl⟩ : syracuseStep 2784815 = 4177223) B4177223
theorem B1392367 : Blo 1236436 1392367 := bstep (se 1 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 1392367 = 2088551) B2088551
theorem B2785121 : Blo 1236436 2785121 := bstep (se 2 (by rfl) ⟨1044420, by rfl⟩ : syracuseStep 2785121 = 2088841) B2088841
theorem B6266807 : Blo 1236436 6266807 := bstep (se 1 (by rfl) ⟨4700105, by rfl⟩ : syracuseStep 6266807 = 9400211) B9400211
theorem B1237039 : Blo 1236436 1237039 := bstep (se 1 (by rfl) ⟨927779, by rfl⟩ : syracuseStep 1237039 = 1855559) B1855559
theorem B3129911 : Blo 1236436 3129911 := bstep (se 1 (by rfl) ⟨2347433, by rfl⟩ : syracuseStep 3129911 = 4694867) B4694867
theorem B18096695 : Blo 1236436 18096695 := bstep (se 1 (by rfl) ⟨13572521, by rfl⟩ : syracuseStep 18096695 = 27145043) B27145043
theorem B32154641 : Blo 1236436 32154641 := bstep (se 2 (by rfl) ⟨12057990, by rfl⟩ : syracuseStep 32154641 = 24115981) B24115981
theorem B8037467 : Blo 1236436 8037467 := bstep (se 1 (by rfl) ⟨6028100, by rfl⟩ : syracuseStep 8037467 = 12056201) B12056201
theorem B1238343 : Blo 1236436 1238343 := bstep (se 1 (by rfl) ⟨928757, by rfl⟩ : syracuseStep 1238343 = 1857515) B1857515
theorem B4179707 : Blo 1236436 4179707 := bstep (se 1 (by rfl) ⟨3134780, by rfl⟩ : syracuseStep 4179707 = 6269561) B6269561
theorem B352192789 : Blo 1236436 352192789 := bstep (se 6 (by rfl) ⟨8254518, by rfl⟩ : syracuseStep 352192789 = 16509037) B16509037
theorem B7932455 : Blo 1236436 7932455 := bstep (se 1 (by rfl) ⟨5949341, by rfl⟩ : syracuseStep 7932455 = 11898683) B11898683
theorem B15862553 : Blo 1236436 15862553 := bstep (se 2 (by rfl) ⟨5948457, by rfl⟩ : syracuseStep 15862553 = 11896915) B11896915
theorem B9399239 : Blo 1236436 9399239 := bstep (se 1 (by rfl) ⟨7049429, by rfl⟩ : syracuseStep 9399239 = 14098859) B14098859
theorem B4762633 : Blo 1236436 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B14101775 : Blo 1236436 14101775 := bstep (se 1 (by rfl) ⟨10576331, by rfl⟩ : syracuseStep 14101775 = 21152663) B21152663
theorem B1854767 : Blo 1236436 1854767 := bstep (se 1 (by rfl) ⟨1391075, by rfl⟩ : syracuseStep 1854767 = 2782151) B2782151
theorem B4173281 : Blo 1236436 4173281 := bstep (se 2 (by rfl) ⟨1564980, by rfl⟩ : syracuseStep 4173281 = 3129961) B3129961
theorem B14085737 : Blo 1236436 14085737 := bstep (se 2 (by rfl) ⟨5282151, by rfl⟩ : syracuseStep 14085737 = 10564303) B10564303
theorem B1855097 : Blo 1236436 1855097 := bstep (se 2 (by rfl) ⟨695661, by rfl⟩ : syracuseStep 1855097 = 1391323) B1391323
theorem B32132807 : Blo 1236436 32132807 := bstep (se 1 (by rfl) ⟨24099605, by rfl⟩ : syracuseStep 32132807 = 48199211) B48199211
theorem B13381519 : Blo 1236436 13381519 := bstep (se 1 (by rfl) ⟨10036139, by rfl⟩ : syracuseStep 13381519 = 20072279) B20072279
theorem B4698071 : Blo 1236436 4698071 := bstep (se 1 (by rfl) ⟨3523553, by rfl⟩ : syracuseStep 4698071 = 7047107) B7047107
theorem B1855625 : Blo 1236436 1855625 := bstep (se 2 (by rfl) ⟨695859, by rfl⟩ : syracuseStep 1855625 = 1391719) B1391719
theorem B1855655 : Blo 1236436 1855655 := bstep (se 1 (by rfl) ⟨1391741, by rfl⟩ : syracuseStep 1855655 = 2783483) B2783483
theorem B6263081 : Blo 1236436 6263081 := bstep (se 2 (by rfl) ⟨2348655, by rfl⟩ : syracuseStep 6263081 = 4697311) B4697311
theorem B5288287 : Blo 1236436 5288287 := bstep (se 1 (by rfl) ⟨3966215, by rfl⟩ : syracuseStep 5288287 = 7932431) B7932431
theorem B4174199 : Blo 1236436 4174199 := bstep (se 1 (by rfl) ⟨3130649, by rfl⟩ : syracuseStep 4174199 = 6261299) B6261299
theorem B1855865 : Blo 1236436 1855865 := bstep (se 2 (by rfl) ⟨695949, by rfl⟩ : syracuseStep 1855865 = 1391899) B1391899
theorem B1855913 : Blo 1236436 1855913 := bstep (se 2 (by rfl) ⟨695967, by rfl⟩ : syracuseStep 1855913 = 1391935) B1391935
theorem B1855967 : Blo 1236436 1855967 := bstep (se 1 (by rfl) ⟨1391975, by rfl⟩ : syracuseStep 1855967 = 2783951) B2783951
theorem B31715873 : Blo 1236436 31715873 := bstep (se 2 (by rfl) ⟨11893452, by rfl⟩ : syracuseStep 31715873 = 23786905) B23786905
theorem B2380447 : Blo 1236436 2380447 := bstep (se 1 (by rfl) ⟨1785335, by rfl⟩ : syracuseStep 2380447 = 3570671) B3570671
theorem B60232409 : Blo 1236436 60232409 := bstep (se 2 (by rfl) ⟨22587153, by rfl⟩ : syracuseStep 60232409 = 45174307) B45174307
theorem B2822951 : Blo 1236436 2822951 := bstep (se 1 (by rfl) ⟨2117213, by rfl⟩ : syracuseStep 2822951 = 4234427) B4234427
theorem B33846149 : Blo 1236436 33846149 := bstep (se 4 (by rfl) ⟨3173076, by rfl⟩ : syracuseStep 33846149 = 6346153) B6346153
theorem B1856489 : Blo 1236436 1856489 := bstep (se 2 (by rfl) ⟨696183, by rfl⟩ : syracuseStep 1856489 = 1392367) B1392367
theorem B14087195 : Blo 1236436 14087195 := bstep (se 1 (by rfl) ⟨10565396, by rfl⟩ : syracuseStep 14087195 = 21130793) B21130793
theorem B1856543 : Blo 1236436 1856543 := bstep (se 1 (by rfl) ⟨1392407, by rfl⟩ : syracuseStep 1856543 = 2784815) B2784815
theorem B1856747 : Blo 1236436 1856747 := bstep (se 1 (by rfl) ⟨1392560, by rfl⟩ : syracuseStep 1856747 = 2785121) B2785121
theorem B5289245 : Blo 1236436 5289245 := bstep (se 3 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 5289245 = 1983467) B1983467
theorem B2782511 : Blo 1236436 2782511 := bstep (se 1 (by rfl) ⟨2086883, by rfl⟩ : syracuseStep 2782511 = 4173767) B4173767
theorem B160495181 : Blo 1236436 160495181 := bstep (se 3 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 160495181 = 60185693) B60185693
theorem B4699727 : Blo 1236436 4699727 := bstep (se 1 (by rfl) ⟨3524795, by rfl⟩ : syracuseStep 4699727 = 7049591) B7049591
theorem B2348777 : Blo 1236436 2348777 := bstep (se 2 (by rfl) ⟨880791, by rfl⟩ : syracuseStep 2348777 = 1761583) B1761583
theorem B1881947 : Blo 1236436 1881947 := bstep (se 1 (by rfl) ⟨1411460, by rfl⟩ : syracuseStep 1881947 = 2822921) B2822921
theorem B1857407 : Blo 1236436 1857407 := bstep (se 1 (by rfl) ⟨1393055, by rfl⟩ : syracuseStep 1857407 = 2786111) B2786111
theorem B7043051 : Blo 1236436 7043051 := bstep (se 1 (by rfl) ⟨5282288, by rfl⟩ : syracuseStep 7043051 = 10564577) B10564577
theorem B2087167 : Blo 1236436 2087167 := bstep (se 1 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 2087167 = 3130751) B3130751
theorem B3177215 : Blo 1236436 3177215 := bstep (se 1 (by rfl) ⟨2382911, by rfl⟩ : syracuseStep 3177215 = 4765823) B4765823
theorem B3521515 : Blo 1236436 3521515 := bstep (se 1 (by rfl) ⟨2641136, by rfl⟩ : syracuseStep 3521515 = 5282273) B5282273
theorem B2784239 : Blo 1236436 2784239 := bstep (se 1 (by rfl) ⟨2088179, by rfl⟩ : syracuseStep 2784239 = 4176359) B4176359
theorem B2784329 : Blo 1236436 2784329 := bstep (se 2 (by rfl) ⟨1044123, by rfl⟩ : syracuseStep 2784329 = 2088247) B2088247
theorem B2350235 : Blo 1236436 2350235 := bstep (se 1 (by rfl) ⟨1762676, by rfl⟩ : syracuseStep 2350235 = 3525353) B3525353
theorem B1391791 : Blo 1236436 1391791 := bstep (se 1 (by rfl) ⟨1043843, by rfl⟩ : syracuseStep 1391791 = 2087687) B2087687
theorem B1981627 : Blo 1236436 1981627 := bstep (se 1 (by rfl) ⟨1486220, by rfl⟩ : syracuseStep 1981627 = 2972441) B2972441
theorem B21126419 : Blo 1236436 21126419 := bstep (se 1 (by rfl) ⟨15844814, by rfl⟩ : syracuseStep 21126419 = 31689629) B31689629
theorem B1236447 : Blo 1236436 1236447 := bstep (se 1 (by rfl) ⟨927335, by rfl⟩ : syracuseStep 1236447 = 1854671) B1854671
theorem B30096947 : Blo 1236436 30096947 := bstep (se 1 (by rfl) ⟨22572710, by rfl⟩ : syracuseStep 30096947 = 45145421) B45145421
theorem B15867575 : Blo 1236436 15867575 := bstep (se 1 (by rfl) ⟨11900681, by rfl⟩ : syracuseStep 15867575 = 23801363) B23801363
theorem B1236763 : Blo 1236436 1236763 := bstep (se 1 (by rfl) ⟨927572, by rfl⟩ : syracuseStep 1236763 = 1855145) B1855145
theorem B1236927 : Blo 1236436 1236927 := bstep (se 1 (by rfl) ⟨927695, by rfl⟩ : syracuseStep 1236927 = 1855391) B1855391
theorem B4177871 : Blo 1236436 4177871 := bstep (se 1 (by rfl) ⟨3133403, by rfl⟩ : syracuseStep 4177871 = 6266807) B6266807
theorem B1237083 : Blo 1236436 1237083 := bstep (se 1 (by rfl) ⟨927812, by rfl⟩ : syracuseStep 1237083 = 1855625) B1855625
theorem B1237103 : Blo 1236436 1237103 := bstep (se 1 (by rfl) ⟨927827, by rfl⟩ : syracuseStep 1237103 = 1855655) B1855655
theorem B1237243 : Blo 1236436 1237243 := bstep (se 1 (by rfl) ⟨927932, by rfl⟩ : syracuseStep 1237243 = 1855865) B1855865
theorem B1237275 : Blo 1236436 1237275 := bstep (se 1 (by rfl) ⟨927956, by rfl⟩ : syracuseStep 1237275 = 1855913) B1855913
theorem B1237311 : Blo 1236436 1237311 := bstep (se 1 (by rfl) ⟨927983, by rfl⟩ : syracuseStep 1237311 = 1855967) B1855967
theorem B21143915 : Blo 1236436 21143915 := bstep (se 1 (by rfl) ⟨15857936, by rfl⟩ : syracuseStep 21143915 = 31715873) B31715873
theorem B469590385 : Blo 1236436 469590385 := bstep (se 2 (by rfl) ⟨176096394, by rfl⟩ : syracuseStep 469590385 = 352192789) B352192789
theorem B6267293 : Blo 1236436 6267293 := bstep (se 3 (by rfl) ⟨1175117, by rfl⟩ : syracuseStep 6267293 = 2350235) B2350235
theorem B1237659 : Blo 1236436 1237659 := bstep (se 1 (by rfl) ⟨928244, by rfl⟩ : syracuseStep 1237659 = 1856489) B1856489
theorem B1237695 : Blo 1236436 1237695 := bstep (se 1 (by rfl) ⟨928271, by rfl⟩ : syracuseStep 1237695 = 1856543) B1856543
theorem B5358311 : Blo 1236436 5358311 := bstep (se 1 (by rfl) ⟨4018733, by rfl⟩ : syracuseStep 5358311 = 8037467) B8037467
theorem B1237831 : Blo 1236436 1237831 := bstep (se 1 (by rfl) ⟨928373, by rfl⟩ : syracuseStep 1237831 = 1856747) B1856747
theorem B10568677 : Blo 1236436 10568677 := bstep (se 4 (by rfl) ⟨990813, by rfl⟩ : syracuseStep 10568677 = 1981627) B1981627
theorem B106996787 : Blo 1236436 106996787 := bstep (se 1 (by rfl) ⟨80247590, by rfl⟩ : syracuseStep 106996787 = 160495181) B160495181
theorem B2786471 : Blo 1236436 2786471 := bstep (se 1 (by rfl) ⟨2089853, by rfl⟩ : syracuseStep 2786471 = 4179707) B4179707
theorem B1238271 : Blo 1236436 1238271 := bstep (se 1 (by rfl) ⟨928703, by rfl⟩ : syracuseStep 1238271 = 1857407) B1857407
theorem B4695353 : Blo 1236436 4695353 := bstep (se 2 (by rfl) ⟨1760757, by rfl⟩ : syracuseStep 4695353 = 3521515) B3521515
theorem B4695367 : Blo 1236436 4695367 := bstep (se 1 (by rfl) ⟨3521525, by rfl⟩ : syracuseStep 4695367 = 7043051) B7043051
theorem B6350177 : Blo 1236436 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B14084279 : Blo 1236436 14084279 := bstep (se 1 (by rfl) ⟨10563209, by rfl⟩ : syracuseStep 14084279 = 21126419) B21126419
theorem B20064631 : Blo 1236436 20064631 := bstep (se 1 (by rfl) ⟨15048473, by rfl⟩ : syracuseStep 20064631 = 30096947) B30096947
theorem B9390491 : Blo 1236436 9390491 := bstep (se 1 (by rfl) ⟨7042868, by rfl⟩ : syracuseStep 9390491 = 14085737) B14085737
theorem B10578383 : Blo 1236436 10578383 := bstep (se 1 (by rfl) ⟨7933787, by rfl⟩ : syracuseStep 10578383 = 15867575) B15867575
theorem B3132047 : Blo 1236436 3132047 := bstep (se 1 (by rfl) ⟨2349035, by rfl⟩ : syracuseStep 3132047 = 4698071) B4698071
theorem B22564099 : Blo 1236436 22564099 := bstep (se 1 (by rfl) ⟨16923074, by rfl⟩ : syracuseStep 22564099 = 33846149) B33846149
theorem B9391463 : Blo 1236436 9391463 := bstep (se 1 (by rfl) ⟨7043597, by rfl⟩ : syracuseStep 9391463 = 14087195) B14087195
theorem B3526163 : Blo 1236436 3526163 := bstep (se 1 (by rfl) ⟨2644622, by rfl⟩ : syracuseStep 3526163 = 5289245) B5289245
theorem B1855007 : Blo 1236436 1855007 := bstep (se 1 (by rfl) ⟨1391255, by rfl⟩ : syracuseStep 1855007 = 2782511) B2782511
theorem B3133151 : Blo 1236436 3133151 := bstep (se 1 (by rfl) ⟨2349863, by rfl⟩ : syracuseStep 3133151 = 4699727) B4699727
theorem B1855721 : Blo 1236436 1855721 := bstep (se 2 (by rfl) ⟨695895, by rfl⟩ : syracuseStep 1855721 = 1391791) B1391791
theorem B5288303 : Blo 1236436 5288303 := bstep (se 1 (by rfl) ⟨3966227, by rfl⟩ : syracuseStep 5288303 = 7932455) B7932455
theorem B2118143 : Blo 1236436 2118143 := bstep (se 1 (by rfl) ⟨1588607, by rfl⟩ : syracuseStep 2118143 = 3177215) B3177215
theorem B6263405 : Blo 1236436 6263405 := bstep (se 3 (by rfl) ⟨1174388, by rfl⟩ : syracuseStep 6263405 = 2348777) B2348777
theorem B1856159 : Blo 1236436 1856159 := bstep (se 1 (by rfl) ⟨1392119, by rfl⟩ : syracuseStep 1856159 = 2784239) B2784239
theorem B1856219 : Blo 1236436 1856219 := bstep (se 1 (by rfl) ⟨1392164, by rfl⟩ : syracuseStep 1856219 = 2784329) B2784329
theorem B9401183 : Blo 1236436 9401183 := bstep (se 1 (by rfl) ⟨7050887, by rfl⟩ : syracuseStep 9401183 = 14101775) B14101775
theorem B5018525 : Blo 1236436 5018525 := bstep (se 3 (by rfl) ⟨940973, by rfl⟩ : syracuseStep 5018525 = 1881947) B1881947
theorem B2782187 : Blo 1236436 2782187 := bstep (se 1 (by rfl) ⟨2086640, by rfl⟩ : syracuseStep 2782187 = 4173281) B4173281
theorem B4175387 : Blo 1236436 4175387 := bstep (se 1 (by rfl) ⟨3131540, by rfl⟩ : syracuseStep 4175387 = 6263081) B6263081
theorem B2782799 : Blo 1236436 2782799 := bstep (se 1 (by rfl) ⟨2087099, by rfl⟩ : syracuseStep 2782799 = 4174199) B4174199
theorem B2782889 : Blo 1236436 2782889 := bstep (se 2 (by rfl) ⟨1043583, by rfl⟩ : syracuseStep 2782889 = 2087167) B2087167
theorem B2086607 : Blo 1236436 2086607 := bstep (se 1 (by rfl) ⟨1564955, by rfl⟩ : syracuseStep 2086607 = 3129911) B3129911
theorem B12064463 : Blo 1236436 12064463 := bstep (se 1 (by rfl) ⟨9048347, by rfl⟩ : syracuseStep 12064463 = 18096695) B18096695
theorem B7051049 : Blo 1236436 7051049 := bstep (se 2 (by rfl) ⟨2644143, by rfl⟩ : syracuseStep 7051049 = 5288287) B5288287
theorem B40154939 : Blo 1236436 40154939 := bstep (se 1 (by rfl) ⟨30116204, by rfl⟩ : syracuseStep 40154939 = 60232409) B60232409
theorem B1881967 : Blo 1236436 1881967 := bstep (se 1 (by rfl) ⟨1411475, by rfl⟩ : syracuseStep 1881967 = 2822951) B2822951
theorem B21436427 : Blo 1236436 21436427 := bstep (se 1 (by rfl) ⟨16077320, by rfl⟩ : syracuseStep 21436427 = 32154641) B32154641
theorem B12695717 : Blo 1236436 12695717 := bstep (se 4 (by rfl) ⟨1190223, by rfl⟩ : syracuseStep 12695717 = 2380447) B2380447
theorem B10575035 : Blo 1236436 10575035 := bstep (se 1 (by rfl) ⟨7931276, by rfl⟩ : syracuseStep 10575035 = 15862553) B15862553
theorem B6266159 : Blo 1236436 6266159 := bstep (se 1 (by rfl) ⟨4699619, by rfl⟩ : syracuseStep 6266159 = 9399239) B9399239
theorem B1236511 : Blo 1236436 1236511 := bstep (se 1 (by rfl) ⟨927383, by rfl⟩ : syracuseStep 1236511 = 1854767) B1854767
theorem B1236731 : Blo 1236436 1236731 := bstep (se 1 (by rfl) ⟨927548, by rfl⟩ : syracuseStep 1236731 = 1855097) B1855097
theorem B21421871 : Blo 1236436 21421871 := bstep (se 1 (by rfl) ⟨16066403, by rfl⟩ : syracuseStep 21421871 = 32132807) B32132807
theorem B17842025 : Blo 1236436 17842025 := bstep (se 2 (by rfl) ⟨6690759, by rfl⟩ : syracuseStep 17842025 = 13381519) B13381519
theorem B2785247 : Blo 1236436 2785247 := bstep (se 1 (by rfl) ⟨2088935, by rfl⟩ : syracuseStep 2785247 = 4177871) B4177871
theorem B1237147 : Blo 1236436 1237147 := bstep (se 1 (by rfl) ⟨927860, by rfl⟩ : syracuseStep 1237147 = 1855721) B1855721
theorem B4178195 : Blo 1236436 4178195 := bstep (se 1 (by rfl) ⟨3133646, by rfl⟩ : syracuseStep 4178195 = 6267293) B6267293
theorem B1237439 : Blo 1236436 1237439 := bstep (se 1 (by rfl) ⟨928079, by rfl⟩ : syracuseStep 1237439 = 1856159) B1856159
theorem B1237479 : Blo 1236436 1237479 := bstep (se 1 (by rfl) ⟨928109, by rfl⟩ : syracuseStep 1237479 = 1856219) B1856219
theorem B3572207 : Blo 1236436 3572207 := bstep (se 1 (by rfl) ⟨2679155, by rfl⟩ : syracuseStep 3572207 = 5358311) B5358311
theorem B6267455 : Blo 1236436 6267455 := bstep (se 1 (by rfl) ⟨4700591, by rfl⟩ : syracuseStep 6267455 = 9401183) B9401183
theorem B3130235 : Blo 1236436 3130235 := bstep (se 1 (by rfl) ⟨2347676, by rfl⟩ : syracuseStep 3130235 = 4695353) B4695353
theorem B16933805 : Blo 1236436 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B14091569 : Blo 1236436 14091569 := bstep (se 2 (by rfl) ⟨5284338, by rfl⟩ : syracuseStep 14091569 = 10568677) B10568677
theorem B8463811 : Blo 1236436 8463811 := bstep (se 1 (by rfl) ⟨6347858, by rfl⟩ : syracuseStep 8463811 = 12695717) B12695717
theorem B9389519 : Blo 1236436 9389519 := bstep (se 1 (by rfl) ⟨7042139, by rfl⟩ : syracuseStep 9389519 = 14084279) B14084279
theorem B6260327 : Blo 1236436 6260327 := bstep (se 1 (by rfl) ⟨4695245, by rfl⟩ : syracuseStep 6260327 = 9390491) B9390491
theorem B6260489 : Blo 1236436 6260489 := bstep (se 2 (by rfl) ⟨2347683, by rfl⟩ : syracuseStep 6260489 = 4695367) B4695367
theorem B6260975 : Blo 1236436 6260975 := bstep (se 1 (by rfl) ⟨4695731, by rfl⟩ : syracuseStep 6260975 = 9391463) B9391463
theorem B2509289 : Blo 1236436 2509289 := bstep (se 2 (by rfl) ⟨940983, by rfl⟩ : syracuseStep 2509289 = 1881967) B1881967
theorem B14281247 : Blo 1236436 14281247 := bstep (se 1 (by rfl) ⟨10710935, by rfl⟩ : syracuseStep 14281247 = 21421871) B21421871
theorem B3525535 : Blo 1236436 3525535 := bstep (se 1 (by rfl) ⟨2644151, by rfl⟩ : syracuseStep 3525535 = 5288303) B5288303
theorem B1412095 : Blo 1236436 1412095 := bstep (se 1 (by rfl) ⟨1059071, by rfl⟩ : syracuseStep 1412095 = 2118143) B2118143
theorem B3345683 : Blo 1236436 3345683 := bstep (se 1 (by rfl) ⟨2509262, by rfl⟩ : syracuseStep 3345683 = 5018525) B5018525
theorem B1854791 : Blo 1236436 1854791 := bstep (se 1 (by rfl) ⟨1391093, by rfl⟩ : syracuseStep 1854791 = 2782187) B2782187
theorem B71331191 : Blo 1236436 71331191 := bstep (se 1 (by rfl) ⟨53498393, by rfl⟩ : syracuseStep 71331191 = 106996787) B106996787
theorem B1855199 : Blo 1236436 1855199 := bstep (se 1 (by rfl) ⟨1391399, by rfl⟩ : syracuseStep 1855199 = 2782799) B2782799
theorem B1855259 : Blo 1236436 1855259 := bstep (se 1 (by rfl) ⟨1391444, by rfl⟩ : syracuseStep 1855259 = 2782889) B2782889
theorem B14290951 : Blo 1236436 14290951 := bstep (se 1 (by rfl) ⟨10718213, by rfl⟩ : syracuseStep 14290951 = 21436427) B21436427
theorem B30085465 : Blo 1236436 30085465 := bstep (se 2 (by rfl) ⟨11282049, by rfl⟩ : syracuseStep 30085465 = 22564099) B22564099
theorem B7050023 : Blo 1236436 7050023 := bstep (se 1 (by rfl) ⟨5287517, by rfl⟩ : syracuseStep 7050023 = 10575035) B10575035
theorem B1856831 : Blo 1236436 1856831 := bstep (se 1 (by rfl) ⟨1392623, by rfl⟩ : syracuseStep 1856831 = 2785247) B2785247
theorem B14095943 : Blo 1236436 14095943 := bstep (se 1 (by rfl) ⟨10571957, by rfl⟩ : syracuseStep 14095943 = 21143915) B21143915
theorem B4175603 : Blo 1236436 4175603 := bstep (se 1 (by rfl) ⟨3131702, by rfl⟩ : syracuseStep 4175603 = 6263405) B6263405
theorem B626120513 : Blo 1236436 626120513 := bstep (se 2 (by rfl) ⟨234795192, by rfl⟩ : syracuseStep 626120513 = 469590385) B469590385
theorem B26752841 : Blo 1236436 26752841 := bstep (se 2 (by rfl) ⟨10032315, by rfl⟩ : syracuseStep 26752841 = 20064631) B20064631
theorem B1857647 : Blo 1236436 1857647 := bstep (se 1 (by rfl) ⟨1393235, by rfl⟩ : syracuseStep 1857647 = 2786471) B2786471
theorem B2783591 : Blo 1236436 2783591 := bstep (se 1 (by rfl) ⟨2087693, by rfl⟩ : syracuseStep 2783591 = 4175387) B4175387
theorem B1391071 : Blo 1236436 1391071 := bstep (se 1 (by rfl) ⟨1043303, by rfl⟩ : syracuseStep 1391071 = 2086607) B2086607
theorem B8042975 : Blo 1236436 8042975 := bstep (se 1 (by rfl) ⟨6032231, by rfl⟩ : syracuseStep 8042975 = 12064463) B12064463
theorem B4700699 : Blo 1236436 4700699 := bstep (se 1 (by rfl) ⟨3525524, by rfl⟩ : syracuseStep 4700699 = 7051049) B7051049
theorem B26769959 : Blo 1236436 26769959 := bstep (se 1 (by rfl) ⟨20077469, by rfl⟩ : syracuseStep 26769959 = 40154939) B40154939
theorem B7052255 : Blo 1236436 7052255 := bstep (se 1 (by rfl) ⟨5289191, by rfl⟩ : syracuseStep 7052255 = 10578383) B10578383
theorem B2088031 : Blo 1236436 2088031 := bstep (se 1 (by rfl) ⟨1566023, by rfl⟩ : syracuseStep 2088031 = 3132047) B3132047
theorem B4177439 : Blo 1236436 4177439 := bstep (se 1 (by rfl) ⟨3133079, by rfl⟩ : syracuseStep 4177439 = 6266159) B6266159
theorem B2350775 : Blo 1236436 2350775 := bstep (se 1 (by rfl) ⟨1763081, by rfl⟩ : syracuseStep 2350775 = 3526163) B3526163
theorem B1236671 : Blo 1236436 1236671 := bstep (se 1 (by rfl) ⟨927503, by rfl⟩ : syracuseStep 1236671 = 1855007) B1855007
theorem B2088767 : Blo 1236436 2088767 := bstep (se 1 (by rfl) ⟨1566575, by rfl⟩ : syracuseStep 2088767 = 3133151) B3133151
theorem B11894683 : Blo 1236436 11894683 := bstep (se 1 (by rfl) ⟨8921012, by rfl⟩ : syracuseStep 11894683 = 17842025) B17842025
theorem B19054601 : Blo 1236436 19054601 := bstep (se 2 (by rfl) ⟨7145475, by rfl⟩ : syracuseStep 19054601 = 14290951) B14290951
theorem B2785463 : Blo 1236436 2785463 := bstep (se 1 (by rfl) ⟨2089097, by rfl⟩ : syracuseStep 2785463 = 4178195) B4178195
theorem B4178303 : Blo 1236436 4178303 := bstep (se 1 (by rfl) ⟨3133727, by rfl⟩ : syracuseStep 4178303 = 6267455) B6267455
theorem B11289203 : Blo 1236436 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B8921821 : Blo 1236436 8921821 := bstep (se 3 (by rfl) ⟨1672841, by rfl⟩ : syracuseStep 8921821 = 3345683) B3345683
theorem B1237887 : Blo 1236436 1237887 := bstep (se 1 (by rfl) ⟨928415, by rfl⟩ : syracuseStep 1237887 = 1856831) B1856831
theorem B6259679 : Blo 1236436 6259679 := bstep (se 1 (by rfl) ⟨4694759, by rfl⟩ : syracuseStep 6259679 = 9389519) B9389519
theorem B9397295 : Blo 1236436 9397295 := bstep (se 1 (by rfl) ⟨7047971, by rfl⟩ : syracuseStep 9397295 = 14095943) B14095943
theorem B17835227 : Blo 1236436 17835227 := bstep (se 1 (by rfl) ⟨13376420, by rfl⟩ : syracuseStep 17835227 = 26752841) B26752841
theorem B1238431 : Blo 1236436 1238431 := bstep (se 1 (by rfl) ⟨928823, by rfl⟩ : syracuseStep 1238431 = 1857647) B1857647
theorem B1672859 : Blo 1236436 1672859 := bstep (se 1 (by rfl) ⟨1254644, by rfl⟩ : syracuseStep 1672859 = 2509289) B2509289
theorem B9520831 : Blo 1236436 9520831 := bstep (se 1 (by rfl) ⟨7140623, by rfl⟩ : syracuseStep 9520831 = 14281247) B14281247
theorem B1567183 : Blo 1236436 1567183 := bstep (se 1 (by rfl) ⟨1175387, by rfl⟩ : syracuseStep 1567183 = 2350775) B2350775
theorem B1854761 : Blo 1236436 1854761 := bstep (se 2 (by rfl) ⟨695535, by rfl⟩ : syracuseStep 1854761 = 1391071) B1391071
theorem B4173551 : Blo 1236436 4173551 := bstep (se 1 (by rfl) ⟨3130163, by rfl⟩ : syracuseStep 4173551 = 6260327) B6260327
theorem B4173659 : Blo 1236436 4173659 := bstep (se 1 (by rfl) ⟨3130244, by rfl⟩ : syracuseStep 4173659 = 6260489) B6260489
theorem B4173983 : Blo 1236436 4173983 := bstep (se 1 (by rfl) ⟨3130487, by rfl⟩ : syracuseStep 4173983 = 6260975) B6260975
theorem B1855727 : Blo 1236436 1855727 := bstep (se 1 (by rfl) ⟨1391795, by rfl⟩ : syracuseStep 1855727 = 2783591) B2783591
theorem B5361983 : Blo 1236436 5361983 := bstep (se 1 (by rfl) ⟨4021487, by rfl⟩ : syracuseStep 5361983 = 8042975) B8042975
theorem B3133799 : Blo 1236436 3133799 := bstep (se 1 (by rfl) ⟨2350349, by rfl⟩ : syracuseStep 3133799 = 4700699) B4700699
theorem B17846639 : Blo 1236436 17846639 := bstep (se 1 (by rfl) ⟨13384979, by rfl⟩ : syracuseStep 17846639 = 26769959) B26769959
theorem B11285081 : Blo 1236436 11285081 := bstep (se 2 (by rfl) ⟨4231905, by rfl⟩ : syracuseStep 11285081 = 8463811) B8463811
theorem B2381471 : Blo 1236436 2381471 := bstep (se 1 (by rfl) ⟨1786103, by rfl⟩ : syracuseStep 2381471 = 3572207) B3572207
theorem B40113953 : Blo 1236436 40113953 := bstep (se 2 (by rfl) ⟨15042732, by rfl⟩ : syracuseStep 40113953 = 30085465) B30085465
theorem B4700015 : Blo 1236436 4700015 := bstep (se 1 (by rfl) ⟨3525011, by rfl⟩ : syracuseStep 4700015 = 7050023) B7050023
theorem B2086823 : Blo 1236436 2086823 := bstep (se 1 (by rfl) ⟨1565117, by rfl⟩ : syracuseStep 2086823 = 3130235) B3130235
theorem B9394379 : Blo 1236436 9394379 := bstep (se 1 (by rfl) ⟨7045784, by rfl⟩ : syracuseStep 9394379 = 14091569) B14091569
theorem B2783735 : Blo 1236436 2783735 := bstep (se 1 (by rfl) ⟨2087801, by rfl⟩ : syracuseStep 2783735 = 4175603) B4175603
theorem B4700713 : Blo 1236436 4700713 := bstep (se 2 (by rfl) ⟨1762767, by rfl⟩ : syracuseStep 4700713 = 3525535) B3525535
theorem B417413675 : Blo 1236436 417413675 := bstep (se 1 (by rfl) ⟨313060256, by rfl⟩ : syracuseStep 417413675 = 626120513) B626120513
theorem B1882793 : Blo 1236436 1882793 := bstep (se 2 (by rfl) ⟨706047, by rfl⟩ : syracuseStep 1882793 = 1412095) B1412095
theorem B2784041 : Blo 1236436 2784041 := bstep (se 2 (by rfl) ⟨1044015, by rfl⟩ : syracuseStep 2784041 = 2088031) B2088031
theorem B4701503 : Blo 1236436 4701503 := bstep (se 1 (by rfl) ⟨3526127, by rfl⟩ : syracuseStep 4701503 = 7052255) B7052255
theorem B1236527 : Blo 1236436 1236527 := bstep (se 1 (by rfl) ⟨927395, by rfl⟩ : syracuseStep 1236527 = 1854791) B1854791
theorem B47554127 : Blo 1236436 47554127 := bstep (se 1 (by rfl) ⟨35665595, by rfl⟩ : syracuseStep 47554127 = 71331191) B71331191
theorem B2784959 : Blo 1236436 2784959 := bstep (se 1 (by rfl) ⟨2088719, by rfl⟩ : syracuseStep 2784959 = 4177439) B4177439
theorem B1236799 : Blo 1236436 1236799 := bstep (se 1 (by rfl) ⟨927599, by rfl⟩ : syracuseStep 1236799 = 1855199) B1855199
theorem B1236839 : Blo 1236436 1236839 := bstep (se 1 (by rfl) ⟨927629, by rfl⟩ : syracuseStep 1236839 = 1855259) B1855259
theorem B15859577 : Blo 1236436 15859577 := bstep (se 2 (by rfl) ⟨5947341, by rfl⟩ : syracuseStep 15859577 = 11894683) B11894683
theorem B1392511 : Blo 1236436 1392511 := bstep (se 1 (by rfl) ⟨1044383, by rfl⟩ : syracuseStep 1392511 = 2088767) B2088767
theorem B1237151 : Blo 1236436 1237151 := bstep (se 1 (by rfl) ⟨927863, by rfl⟩ : syracuseStep 1237151 = 1855727) B1855727
theorem B2089199 : Blo 1236436 2089199 := bstep (se 1 (by rfl) ⟨1566899, by rfl⟩ : syracuseStep 2089199 = 3133799) B3133799
theorem B2785535 : Blo 1236436 2785535 := bstep (se 1 (by rfl) ⟨2089151, by rfl⟩ : syracuseStep 2785535 = 4178303) B4178303
theorem B2089577 : Blo 1236436 2089577 := bstep (se 2 (by rfl) ⟨783591, by rfl⟩ : syracuseStep 2089577 = 1567183) B1567183
theorem B6267617 : Blo 1236436 6267617 := bstep (se 2 (by rfl) ⟨2350356, by rfl⟩ : syracuseStep 6267617 = 4700713) B4700713
theorem B11895761 : Blo 1236436 11895761 := bstep (se 2 (by rfl) ⟨4460910, by rfl⟩ : syracuseStep 11895761 = 8921821) B8921821
theorem B278275783 : Blo 1236436 278275783 := bstep (se 1 (by rfl) ⟨208706837, by rfl⟩ : syracuseStep 278275783 = 417413675) B417413675
theorem B1255195 : Blo 1236436 1255195 := bstep (se 1 (by rfl) ⟨941396, by rfl⟩ : syracuseStep 1255195 = 1882793) B1882793
theorem B3574655 : Blo 1236436 3574655 := bstep (se 1 (by rfl) ⟨2680991, by rfl⟩ : syracuseStep 3574655 = 5361983) B5361983
theorem B11897759 : Blo 1236436 11897759 := bstep (se 1 (by rfl) ⟨8923319, by rfl⟩ : syracuseStep 11897759 = 17846639) B17846639
theorem B7523387 : Blo 1236436 7523387 := bstep (se 1 (by rfl) ⟨5642540, by rfl⟩ : syracuseStep 7523387 = 11285081) B11285081
theorem B4173119 : Blo 1236436 4173119 := bstep (se 1 (by rfl) ⟨3129839, by rfl⟩ : syracuseStep 4173119 = 6259679) B6259679
theorem B11890151 : Blo 1236436 11890151 := bstep (se 1 (by rfl) ⟨8917613, by rfl⟩ : syracuseStep 11890151 = 17835227) B17835227
theorem B50777765 : Blo 1236436 50777765 := bstep (se 4 (by rfl) ⟨4760415, by rfl⟩ : syracuseStep 50777765 = 9520831) B9520831
theorem B26742635 : Blo 1236436 26742635 := bstep (se 1 (by rfl) ⟨20056976, by rfl⟩ : syracuseStep 26742635 = 40113953) B40113953
theorem B3133343 : Blo 1236436 3133343 := bstep (se 1 (by rfl) ⟨2350007, by rfl⟩ : syracuseStep 3133343 = 4700015) B4700015
theorem B6262919 : Blo 1236436 6262919 := bstep (se 1 (by rfl) ⟨4697189, by rfl⟩ : syracuseStep 6262919 = 9394379) B9394379
theorem B1855823 : Blo 1236436 1855823 := bstep (se 1 (by rfl) ⟨1391867, by rfl⟩ : syracuseStep 1855823 = 2783735) B2783735
theorem B4460957 : Blo 1236436 4460957 := bstep (se 3 (by rfl) ⟨836429, by rfl⟩ : syracuseStep 4460957 = 1672859) B1672859
theorem B1856027 : Blo 1236436 1856027 := bstep (se 1 (by rfl) ⟨1392020, by rfl⟩ : syracuseStep 1856027 = 2784041) B2784041
theorem B3134335 : Blo 1236436 3134335 := bstep (se 1 (by rfl) ⟨2350751, by rfl⟩ : syracuseStep 3134335 = 4701503) B4701503
theorem B1856639 : Blo 1236436 1856639 := bstep (se 1 (by rfl) ⟨1392479, by rfl⟩ : syracuseStep 1856639 = 2784959) B2784959
theorem B2782367 : Blo 1236436 2782367 := bstep (se 1 (by rfl) ⟨2086775, by rfl⟩ : syracuseStep 2782367 = 4173551) B4173551
theorem B1856681 : Blo 1236436 1856681 := bstep (se 2 (by rfl) ⟨696255, by rfl⟩ : syracuseStep 1856681 = 1392511) B1392511
theorem B2782439 : Blo 1236436 2782439 := bstep (se 1 (by rfl) ⟨2086829, by rfl⟩ : syracuseStep 2782439 = 4173659) B4173659
theorem B10573051 : Blo 1236436 10573051 := bstep (se 1 (by rfl) ⟨7929788, by rfl⟩ : syracuseStep 10573051 = 15859577) B15859577
theorem B12703067 : Blo 1236436 12703067 := bstep (se 1 (by rfl) ⟨9527300, by rfl⟩ : syracuseStep 12703067 = 19054601) B19054601
theorem B2782655 : Blo 1236436 2782655 := bstep (se 1 (by rfl) ⟨2086991, by rfl⟩ : syracuseStep 2782655 = 4173983) B4173983
theorem B1856975 : Blo 1236436 1856975 := bstep (se 1 (by rfl) ⟨1392731, by rfl⟩ : syracuseStep 1856975 = 2785463) B2785463
theorem B7526135 : Blo 1236436 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B6264863 : Blo 1236436 6264863 := bstep (se 1 (by rfl) ⟨4698647, by rfl⟩ : syracuseStep 6264863 = 9397295) B9397295
theorem B1587647 : Blo 1236436 1587647 := bstep (se 1 (by rfl) ⟨1190735, by rfl⟩ : syracuseStep 1587647 = 2381471) B2381471
theorem B1391215 : Blo 1236436 1391215 := bstep (se 1 (by rfl) ⟨1043411, by rfl⟩ : syracuseStep 1391215 = 2086823) B2086823
theorem B1236507 : Blo 1236436 1236507 := bstep (se 1 (by rfl) ⟨927380, by rfl⟩ : syracuseStep 1236507 = 1854761) B1854761
theorem B31702751 : Blo 1236436 31702751 := bstep (se 1 (by rfl) ⟨23777063, by rfl⟩ : syracuseStep 31702751 = 47554127) B47554127
theorem B1392799 : Blo 1236436 1392799 := bstep (se 1 (by rfl) ⟨1044599, by rfl⟩ : syracuseStep 1392799 = 2089199) B2089199
theorem B1237215 : Blo 1236436 1237215 := bstep (se 1 (by rfl) ⟨927911, by rfl⟩ : syracuseStep 1237215 = 1855823) B1855823
theorem B2973971 : Blo 1236436 2973971 := bstep (se 1 (by rfl) ⟨2230478, by rfl⟩ : syracuseStep 2973971 = 4460957) B4460957
theorem B1237351 : Blo 1236436 1237351 := bstep (se 1 (by rfl) ⟨928013, by rfl⟩ : syracuseStep 1237351 = 1856027) B1856027
theorem B1393051 : Blo 1236436 1393051 := bstep (se 1 (by rfl) ⟨1044788, by rfl⟩ : syracuseStep 1393051 = 2089577) B2089577
theorem B4178411 : Blo 1236436 4178411 := bstep (se 1 (by rfl) ⟨3133808, by rfl⟩ : syracuseStep 4178411 = 6267617) B6267617
theorem B7930507 : Blo 1236436 7930507 := bstep (se 1 (by rfl) ⟨5947880, by rfl⟩ : syracuseStep 7930507 = 11895761) B11895761
theorem B1237759 : Blo 1236436 1237759 := bstep (se 1 (by rfl) ⟨928319, by rfl⟩ : syracuseStep 1237759 = 1856639) B1856639
theorem B1237787 : Blo 1236436 1237787 := bstep (se 1 (by rfl) ⟨928340, by rfl⟩ : syracuseStep 1237787 = 1856681) B1856681
theorem B1237983 : Blo 1236436 1237983 := bstep (se 1 (by rfl) ⟨928487, by rfl⟩ : syracuseStep 1237983 = 1856975) B1856975
theorem B4179113 : Blo 1236436 4179113 := bstep (se 2 (by rfl) ⟨1567167, by rfl⟩ : syracuseStep 4179113 = 3134335) B3134335
theorem B6694373 : Blo 1236436 6694373 := bstep (se 4 (by rfl) ⟨627597, by rfl⟩ : syracuseStep 6694373 = 1255195) B1255195
theorem B7931839 : Blo 1236436 7931839 := bstep (se 1 (by rfl) ⟨5948879, by rfl⟩ : syracuseStep 7931839 = 11897759) B11897759
theorem B5015591 : Blo 1236436 5015591 := bstep (se 1 (by rfl) ⟨3761693, by rfl⟩ : syracuseStep 5015591 = 7523387) B7523387
theorem B371034377 : Blo 1236436 371034377 := bstep (se 2 (by rfl) ⟨139137891, by rfl⟩ : syracuseStep 371034377 = 278275783) B278275783
theorem B33851843 : Blo 1236436 33851843 := bstep (se 1 (by rfl) ⟨25388882, by rfl⟩ : syracuseStep 33851843 = 50777765) B50777765
theorem B17828423 : Blo 1236436 17828423 := bstep (se 1 (by rfl) ⟨13371317, by rfl⟩ : syracuseStep 17828423 = 26742635) B26742635
theorem B1854911 : Blo 1236436 1854911 := bstep (se 1 (by rfl) ⟨1391183, by rfl⟩ : syracuseStep 1854911 = 2782367) B2782367
theorem B1854953 : Blo 1236436 1854953 := bstep (se 2 (by rfl) ⟨695607, by rfl⟩ : syracuseStep 1854953 = 1391215) B1391215
theorem B1854959 : Blo 1236436 1854959 := bstep (se 1 (by rfl) ⟨1391219, by rfl⟩ : syracuseStep 1854959 = 2782439) B2782439
theorem B1855103 : Blo 1236436 1855103 := bstep (se 1 (by rfl) ⟨1391327, by rfl⟩ : syracuseStep 1855103 = 2782655) B2782655
theorem B5017423 : Blo 1236436 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B2782079 : Blo 1236436 2782079 := bstep (se 1 (by rfl) ⟨2086559, by rfl⟩ : syracuseStep 2782079 = 4173119) B4173119
theorem B7926767 : Blo 1236436 7926767 := bstep (se 1 (by rfl) ⟨5945075, by rfl⟩ : syracuseStep 7926767 = 11890151) B11890151
theorem B4175279 : Blo 1236436 4175279 := bstep (se 1 (by rfl) ⟨3131459, by rfl⟩ : syracuseStep 4175279 = 6262919) B6262919
theorem B1857023 : Blo 1236436 1857023 := bstep (se 1 (by rfl) ⟨1392767, by rfl⟩ : syracuseStep 1857023 = 2785535) B2785535
theorem B8468711 : Blo 1236436 8468711 := bstep (se 1 (by rfl) ⟨6351533, by rfl⟩ : syracuseStep 8468711 = 12703067) B12703067
theorem B4233725 : Blo 1236436 4233725 := bstep (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) B1587647
theorem B4176575 : Blo 1236436 4176575 := bstep (se 1 (by rfl) ⟨3132431, by rfl⟩ : syracuseStep 4176575 = 6264863) B6264863
theorem B14097401 : Blo 1236436 14097401 := bstep (se 2 (by rfl) ⟨5286525, by rfl⟩ : syracuseStep 14097401 = 10573051) B10573051
theorem B2383103 : Blo 1236436 2383103 := bstep (se 1 (by rfl) ⟨1787327, by rfl⟩ : syracuseStep 2383103 = 3574655) B3574655
theorem B21135167 : Blo 1236436 21135167 := bstep (se 1 (by rfl) ⟨15851375, by rfl⟩ : syracuseStep 21135167 = 31702751) B31702751
theorem B2088895 : Blo 1236436 2088895 := bstep (se 1 (by rfl) ⟨1566671, by rfl⟩ : syracuseStep 2088895 = 3133343) B3133343
theorem B1982647 : Blo 1236436 1982647 := bstep (se 1 (by rfl) ⟨1486985, by rfl⟩ : syracuseStep 1982647 = 2973971) B2973971
theorem B2785607 : Blo 1236436 2785607 := bstep (se 1 (by rfl) ⟨2089205, by rfl⟩ : syracuseStep 2785607 = 4178411) B4178411
theorem B5284511 : Blo 1236436 5284511 := bstep (se 1 (by rfl) ⟨3963383, by rfl⟩ : syracuseStep 5284511 = 7926767) B7926767
theorem B2786075 : Blo 1236436 2786075 := bstep (se 1 (by rfl) ⟨2089556, by rfl⟩ : syracuseStep 2786075 = 4179113) B4179113
theorem B1238015 : Blo 1236436 1238015 := bstep (se 1 (by rfl) ⟨928511, by rfl⟩ : syracuseStep 1238015 = 1857023) B1857023
theorem B17851661 : Blo 1236436 17851661 := bstep (se 3 (by rfl) ⟨3347186, by rfl⟩ : syracuseStep 17851661 = 6694373) B6694373
theorem B3343727 : Blo 1236436 3343727 := bstep (se 1 (by rfl) ⟨2507795, by rfl⟩ : syracuseStep 3343727 = 5015591) B5015591
theorem B5645807 : Blo 1236436 5645807 := bstep (se 1 (by rfl) ⟨4234355, by rfl⟩ : syracuseStep 5645807 = 8468711) B8468711
theorem B9398267 : Blo 1236436 9398267 := bstep (se 1 (by rfl) ⟨7048700, by rfl⟩ : syracuseStep 9398267 = 14097401) B14097401
theorem B1854719 : Blo 1236436 1854719 := bstep (se 1 (by rfl) ⟨1391039, by rfl⟩ : syracuseStep 1854719 = 2782079) B2782079
theorem B2822483 : Blo 1236436 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B6689897 : Blo 1236436 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B1857065 : Blo 1236436 1857065 := bstep (se 2 (by rfl) ⟨696399, by rfl⟩ : syracuseStep 1857065 = 1392799) B1392799
theorem B1857401 : Blo 1236436 1857401 := bstep (se 2 (by rfl) ⟨696525, by rfl⟩ : syracuseStep 1857401 = 1393051) B1393051
theorem B10574009 : Blo 1236436 10574009 := bstep (se 2 (by rfl) ⟨3965253, by rfl⟩ : syracuseStep 10574009 = 7930507) B7930507
theorem B2783519 : Blo 1236436 2783519 := bstep (se 1 (by rfl) ⟨2087639, by rfl⟩ : syracuseStep 2783519 = 4175279) B4175279
theorem B247356251 : Blo 1236436 247356251 := bstep (se 1 (by rfl) ⟨185517188, by rfl⟩ : syracuseStep 247356251 = 371034377) B371034377
theorem B22567895 : Blo 1236436 22567895 := bstep (se 1 (by rfl) ⟨16925921, by rfl⟩ : syracuseStep 22567895 = 33851843) B33851843
theorem B11885615 : Blo 1236436 11885615 := bstep (se 1 (by rfl) ⟨8914211, by rfl⟩ : syracuseStep 11885615 = 17828423) B17828423
theorem B2784383 : Blo 1236436 2784383 := bstep (se 1 (by rfl) ⟨2088287, by rfl⟩ : syracuseStep 2784383 = 4176575) B4176575
theorem B1588735 : Blo 1236436 1588735 := bstep (se 1 (by rfl) ⟨1191551, by rfl⟩ : syracuseStep 1588735 = 2383103) B2383103
theorem B1236607 : Blo 1236436 1236607 := bstep (se 1 (by rfl) ⟨927455, by rfl⟩ : syracuseStep 1236607 = 1854911) B1854911
theorem B1236635 : Blo 1236436 1236635 := bstep (se 1 (by rfl) ⟨927476, by rfl⟩ : syracuseStep 1236635 = 1854953) B1854953
theorem B1236639 : Blo 1236436 1236639 := bstep (se 1 (by rfl) ⟨927479, by rfl⟩ : syracuseStep 1236639 = 1854959) B1854959
theorem B1236735 : Blo 1236436 1236735 := bstep (se 1 (by rfl) ⟨927551, by rfl⟩ : syracuseStep 1236735 = 1855103) B1855103
theorem B14090111 : Blo 1236436 14090111 := bstep (se 1 (by rfl) ⟨10567583, by rfl⟩ : syracuseStep 14090111 = 21135167) B21135167
theorem B2785193 : Blo 1236436 2785193 := bstep (se 2 (by rfl) ⟨1044447, by rfl⟩ : syracuseStep 2785193 = 2088895) B2088895
theorem B10575785 : Blo 1236436 10575785 := bstep (se 2 (by rfl) ⟨3965919, by rfl⟩ : syracuseStep 10575785 = 7931839) B7931839
theorem B3523007 : Blo 1236436 3523007 := bstep (se 1 (by rfl) ⟨2642255, by rfl⟩ : syracuseStep 3523007 = 5284511) B5284511
theorem B1238043 : Blo 1236436 1238043 := bstep (se 1 (by rfl) ⟨928532, by rfl⟩ : syracuseStep 1238043 = 1857065) B1857065
theorem B1238267 : Blo 1236436 1238267 := bstep (se 1 (by rfl) ⟨928700, by rfl⟩ : syracuseStep 1238267 = 1857401) B1857401
theorem B7923743 : Blo 1236436 7923743 := bstep (se 1 (by rfl) ⟨5942807, by rfl⟩ : syracuseStep 7923743 = 11885615) B11885615
theorem B4459931 : Blo 1236436 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B8916605 : Blo 1236436 8916605 := bstep (se 3 (by rfl) ⟨1671863, by rfl⟩ : syracuseStep 8916605 = 3343727) B3343727
theorem B3763871 : Blo 1236436 3763871 := bstep (se 1 (by rfl) ⟨2822903, by rfl⟩ : syracuseStep 3763871 = 5645807) B5645807
theorem B7049339 : Blo 1236436 7049339 := bstep (se 1 (by rfl) ⟨5287004, by rfl⟩ : syracuseStep 7049339 = 10574009) B10574009
theorem B1855679 : Blo 1236436 1855679 := bstep (se 1 (by rfl) ⟨1391759, by rfl⟩ : syracuseStep 1855679 = 2783519) B2783519
theorem B15045263 : Blo 1236436 15045263 := bstep (se 1 (by rfl) ⟨11283947, by rfl⟩ : syracuseStep 15045263 = 22567895) B22567895
theorem B2118313 : Blo 1236436 2118313 := bstep (se 2 (by rfl) ⟨794367, by rfl⟩ : syracuseStep 2118313 = 1588735) B1588735
theorem B1856255 : Blo 1236436 1856255 := bstep (se 1 (by rfl) ⟨1392191, by rfl⟩ : syracuseStep 1856255 = 2784383) B2784383
theorem B9393407 : Blo 1236436 9393407 := bstep (se 1 (by rfl) ⟨7045055, by rfl⟩ : syracuseStep 9393407 = 14090111) B14090111
theorem B1856795 : Blo 1236436 1856795 := bstep (se 1 (by rfl) ⟨1392596, by rfl⟩ : syracuseStep 1856795 = 2785193) B2785193
theorem B7050523 : Blo 1236436 7050523 := bstep (se 1 (by rfl) ⟨5287892, by rfl⟩ : syracuseStep 7050523 = 10575785) B10575785
theorem B1857071 : Blo 1236436 1857071 := bstep (se 1 (by rfl) ⟨1392803, by rfl⟩ : syracuseStep 1857071 = 2785607) B2785607
theorem B2643529 : Blo 1236436 2643529 := bstep (se 2 (by rfl) ⟨991323, by rfl⟩ : syracuseStep 2643529 = 1982647) B1982647
theorem B1857383 : Blo 1236436 1857383 := bstep (se 1 (by rfl) ⟨1393037, by rfl⟩ : syracuseStep 1857383 = 2786075) B2786075
theorem B11901107 : Blo 1236436 11901107 := bstep (se 1 (by rfl) ⟨8925830, by rfl⟩ : syracuseStep 11901107 = 17851661) B17851661
theorem B7526621 : Blo 1236436 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B6265511 : Blo 1236436 6265511 := bstep (se 1 (by rfl) ⟨4699133, by rfl⟩ : syracuseStep 6265511 = 9398267) B9398267
theorem B164904167 : Blo 1236436 164904167 := bstep (se 1 (by rfl) ⟨123678125, by rfl⟩ : syracuseStep 164904167 = 247356251) B247356251
theorem B1236479 : Blo 1236436 1236479 := bstep (se 1 (by rfl) ⟨927359, by rfl⟩ : syracuseStep 1236479 = 1854719) B1854719
theorem B1237119 : Blo 1236436 1237119 := bstep (se 1 (by rfl) ⟨927839, by rfl⟩ : syracuseStep 1237119 = 1855679) B1855679
theorem B1237503 : Blo 1236436 1237503 := bstep (se 1 (by rfl) ⟨928127, by rfl⟩ : syracuseStep 1237503 = 1856255) B1856255
theorem B20070989 : Blo 1236436 20070989 := bstep (se 3 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 20070989 = 7526621) B7526621
theorem B1237863 : Blo 1236436 1237863 := bstep (se 1 (by rfl) ⟨928397, by rfl⟩ : syracuseStep 1237863 = 1856795) B1856795
theorem B1238047 : Blo 1236436 1238047 := bstep (se 1 (by rfl) ⟨928535, by rfl⟩ : syracuseStep 1238047 = 1857071) B1857071
theorem B1238255 : Blo 1236436 1238255 := bstep (se 1 (by rfl) ⟨928691, by rfl⟩ : syracuseStep 1238255 = 1857383) B1857383
theorem B3524705 : Blo 1236436 3524705 := bstep (se 2 (by rfl) ⟨1321764, by rfl⟩ : syracuseStep 3524705 = 2643529) B2643529
theorem B2509247 : Blo 1236436 2509247 := bstep (se 1 (by rfl) ⟨1881935, by rfl⟩ : syracuseStep 2509247 = 3763871) B3763871
theorem B10030175 : Blo 1236436 10030175 := bstep (se 1 (by rfl) ⟨7522631, by rfl⟩ : syracuseStep 10030175 = 15045263) B15045263
theorem B6262271 : Blo 1236436 6262271 := bstep (se 1 (by rfl) ⟨4696703, by rfl⟩ : syracuseStep 6262271 = 9393407) B9393407
theorem B7934071 : Blo 1236436 7934071 := bstep (se 1 (by rfl) ⟨5950553, by rfl⟩ : syracuseStep 7934071 = 11901107) B11901107
theorem B9400697 : Blo 1236436 9400697 := bstep (se 2 (by rfl) ⟨3525261, by rfl⟩ : syracuseStep 9400697 = 7050523) B7050523
theorem B5944403 : Blo 1236436 5944403 := bstep (se 1 (by rfl) ⟨4458302, by rfl⟩ : syracuseStep 5944403 = 8916605) B8916605
theorem B4699559 : Blo 1236436 4699559 := bstep (se 1 (by rfl) ⟨3524669, by rfl⟩ : syracuseStep 4699559 = 7049339) B7049339
theorem B2348671 : Blo 1236436 2348671 := bstep (se 1 (by rfl) ⟨1761503, by rfl⟩ : syracuseStep 2348671 = 3523007) B3523007
theorem B2824417 : Blo 1236436 2824417 := bstep (se 2 (by rfl) ⟨1059156, by rfl⟩ : syracuseStep 2824417 = 2118313) B2118313
theorem B5282495 : Blo 1236436 5282495 := bstep (se 1 (by rfl) ⟨3961871, by rfl⟩ : syracuseStep 5282495 = 7923743) B7923743
theorem B4177007 : Blo 1236436 4177007 := bstep (se 1 (by rfl) ⟨3132755, by rfl⟩ : syracuseStep 4177007 = 6265511) B6265511
theorem B109936111 : Blo 1236436 109936111 := bstep (se 1 (by rfl) ⟨82452083, by rfl⟩ : syracuseStep 109936111 = 164904167) B164904167
theorem B2973287 : Blo 1236436 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B6267131 : Blo 1236436 6267131 := bstep (se 1 (by rfl) ⟨4700348, by rfl⟩ : syracuseStep 6267131 = 9400697) B9400697
theorem B1672831 : Blo 1236436 1672831 := bstep (se 1 (by rfl) ⟨1254623, by rfl⟩ : syracuseStep 1672831 = 2509247) B2509247
theorem B146581481 : Blo 1236436 146581481 := bstep (se 2 (by rfl) ⟨54968055, by rfl⟩ : syracuseStep 146581481 = 109936111) B109936111
theorem B6686783 : Blo 1236436 6686783 := bstep (se 1 (by rfl) ⟨5015087, by rfl⟩ : syracuseStep 6686783 = 10030175) B10030175
theorem B3131561 : Blo 1236436 3131561 := bstep (se 2 (by rfl) ⟨1174335, by rfl⟩ : syracuseStep 3131561 = 2348671) B2348671
theorem B10578761 : Blo 1236436 10578761 := bstep (se 2 (by rfl) ⟨3967035, by rfl⟩ : syracuseStep 10578761 = 7934071) B7934071
theorem B13380659 : Blo 1236436 13380659 := bstep (se 1 (by rfl) ⟨10035494, by rfl⟩ : syracuseStep 13380659 = 20070989) B20070989
theorem B3133039 : Blo 1236436 3133039 := bstep (se 1 (by rfl) ⟨2349779, by rfl⟩ : syracuseStep 3133039 = 4699559) B4699559
theorem B4174847 : Blo 1236436 4174847 := bstep (se 1 (by rfl) ⟨3131135, by rfl⟩ : syracuseStep 4174847 = 6262271) B6262271
theorem B3765889 : Blo 1236436 3765889 := bstep (se 2 (by rfl) ⟨1412208, by rfl⟩ : syracuseStep 3765889 = 2824417) B2824417
theorem B3962935 : Blo 1236436 3962935 := bstep (se 1 (by rfl) ⟨2972201, by rfl⟩ : syracuseStep 3962935 = 5944403) B5944403
theorem B2349803 : Blo 1236436 2349803 := bstep (se 1 (by rfl) ⟨1762352, by rfl⟩ : syracuseStep 2349803 = 3524705) B3524705
theorem B7928765 : Blo 1236436 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B3521663 : Blo 1236436 3521663 := bstep (se 1 (by rfl) ⟨2641247, by rfl⟩ : syracuseStep 3521663 = 5282495) B5282495
theorem B2784671 : Blo 1236436 2784671 := bstep (se 1 (by rfl) ⟨2088503, by rfl⟩ : syracuseStep 2784671 = 4177007) B4177007
theorem B5283913 : Blo 1236436 5283913 := bstep (se 2 (by rfl) ⟨1981467, by rfl⟩ : syracuseStep 5283913 = 3962935) B3962935
theorem B4178087 : Blo 1236436 4178087 := bstep (se 1 (by rfl) ⟨3133565, by rfl⟩ : syracuseStep 4178087 = 6267131) B6267131
theorem B8921765 : Blo 1236436 8921765 := bstep (se 4 (by rfl) ⟨836415, by rfl⟩ : syracuseStep 8921765 = 1672831) B1672831
theorem B4457855 : Blo 1236436 4457855 := bstep (se 1 (by rfl) ⟨3343391, by rfl⟩ : syracuseStep 4457855 = 6686783) B6686783
theorem B1566535 : Blo 1236436 1566535 := bstep (se 1 (by rfl) ⟨1174901, by rfl⟩ : syracuseStep 1566535 = 2349803) B2349803
theorem B5285843 : Blo 1236436 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B2347775 : Blo 1236436 2347775 := bstep (se 1 (by rfl) ⟨1760831, by rfl⟩ : syracuseStep 2347775 = 3521663) B3521663
theorem B1856447 : Blo 1236436 1856447 := bstep (se 1 (by rfl) ⟨1392335, by rfl⟩ : syracuseStep 1856447 = 2784671) B2784671
theorem B2783231 : Blo 1236436 2783231 := bstep (se 1 (by rfl) ⟨2087423, by rfl⟩ : syracuseStep 2783231 = 4174847) B4174847
theorem B97720987 : Blo 1236436 97720987 := bstep (se 1 (by rfl) ⟨73290740, by rfl⟩ : syracuseStep 97720987 = 146581481) B146581481
theorem B2087707 : Blo 1236436 2087707 := bstep (se 1 (by rfl) ⟨1565780, by rfl⟩ : syracuseStep 2087707 = 3131561) B3131561
theorem B7052507 : Blo 1236436 7052507 := bstep (se 1 (by rfl) ⟨5289380, by rfl⟩ : syracuseStep 7052507 = 10578761) B10578761
theorem B8920439 : Blo 1236436 8920439 := bstep (se 1 (by rfl) ⟨6690329, by rfl⟩ : syracuseStep 8920439 = 13380659) B13380659
theorem B4177385 : Blo 1236436 4177385 := bstep (se 2 (by rfl) ⟨1566519, by rfl⟩ : syracuseStep 4177385 = 3133039) B3133039
theorem B5021185 : Blo 1236436 5021185 := bstep (se 2 (by rfl) ⟨1882944, by rfl⟩ : syracuseStep 5021185 = 3765889) B3765889
theorem B7045217 : Blo 1236436 7045217 := bstep (se 2 (by rfl) ⟨2641956, by rfl⟩ : syracuseStep 7045217 = 5283913) B5283913
theorem B2785391 : Blo 1236436 2785391 := bstep (se 1 (by rfl) ⟨2089043, by rfl⟩ : syracuseStep 2785391 = 4178087) B4178087
theorem B5947843 : Blo 1236436 5947843 := bstep (se 1 (by rfl) ⟨4460882, by rfl⟩ : syracuseStep 5947843 = 8921765) B8921765
theorem B1565183 : Blo 1236436 1565183 := bstep (se 1 (by rfl) ⟨1173887, by rfl⟩ : syracuseStep 1565183 = 2347775) B2347775
theorem B1237631 : Blo 1236436 1237631 := bstep (se 1 (by rfl) ⟨928223, by rfl⟩ : syracuseStep 1237631 = 1856447) B1856447
theorem B130294649 : Blo 1236436 130294649 := bstep (se 2 (by rfl) ⟨48860493, by rfl⟩ : syracuseStep 130294649 = 97720987) B97720987
theorem B3523895 : Blo 1236436 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B6694913 : Blo 1236436 6694913 := bstep (se 2 (by rfl) ⟨2510592, by rfl⟩ : syracuseStep 6694913 = 5021185) B5021185
theorem B1855487 : Blo 1236436 1855487 := bstep (se 1 (by rfl) ⟨1391615, by rfl⟩ : syracuseStep 1855487 = 2783231) B2783231
theorem B2971903 : Blo 1236436 2971903 := bstep (se 1 (by rfl) ⟨2228927, by rfl⟩ : syracuseStep 2971903 = 4457855) B4457855
theorem B2783609 : Blo 1236436 2783609 := bstep (se 2 (by rfl) ⟨1043853, by rfl⟩ : syracuseStep 2783609 = 2087707) B2087707
theorem B4701671 : Blo 1236436 4701671 := bstep (se 1 (by rfl) ⟨3526253, by rfl⟩ : syracuseStep 4701671 = 7052507) B7052507
theorem B5946959 : Blo 1236436 5946959 := bstep (se 1 (by rfl) ⟨4460219, by rfl⟩ : syracuseStep 5946959 = 8920439) B8920439
theorem B2784923 : Blo 1236436 2784923 := bstep (se 1 (by rfl) ⟨2088692, by rfl⟩ : syracuseStep 2784923 = 4177385) B4177385
theorem B2088713 : Blo 1236436 2088713 := bstep (se 2 (by rfl) ⟨783267, by rfl⟩ : syracuseStep 2088713 = 1566535) B1566535
theorem B7930457 : Blo 1236436 7930457 := bstep (se 2 (by rfl) ⟨2973921, by rfl⟩ : syracuseStep 7930457 = 5947843) B5947843
theorem B4696811 : Blo 1236436 4696811 := bstep (se 1 (by rfl) ⟨3522608, by rfl⟩ : syracuseStep 4696811 = 7045217) B7045217
theorem B86863099 : Blo 1236436 86863099 := bstep (se 1 (by rfl) ⟨65147324, by rfl⟩ : syracuseStep 86863099 = 130294649) B130294649
theorem B4173821 : Blo 1236436 4173821 := bstep (se 3 (by rfl) ⟨782591, by rfl⟩ : syracuseStep 4173821 = 1565183) B1565183
theorem B1855739 : Blo 1236436 1855739 := bstep (se 1 (by rfl) ⟨1391804, by rfl⟩ : syracuseStep 1855739 = 2783609) B2783609
theorem B3134447 : Blo 1236436 3134447 := bstep (se 1 (by rfl) ⟨2350835, by rfl⟩ : syracuseStep 3134447 = 4701671) B4701671
theorem B1856615 : Blo 1236436 1856615 := bstep (se 1 (by rfl) ⟨1392461, by rfl⟩ : syracuseStep 1856615 = 2784923) B2784923
theorem B1856927 : Blo 1236436 1856927 := bstep (se 1 (by rfl) ⟨1392695, by rfl⟩ : syracuseStep 1856927 = 2785391) B2785391
theorem B3962537 : Blo 1236436 3962537 := bstep (se 2 (by rfl) ⟨1485951, by rfl⟩ : syracuseStep 3962537 = 2971903) B2971903
theorem B2349263 : Blo 1236436 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B4463275 : Blo 1236436 4463275 := bstep (se 1 (by rfl) ⟨3347456, by rfl⟩ : syracuseStep 4463275 = 6694913) B6694913
theorem B3964639 : Blo 1236436 3964639 := bstep (se 1 (by rfl) ⟨2973479, by rfl⟩ : syracuseStep 3964639 = 5946959) B5946959
theorem B1392475 : Blo 1236436 1392475 := bstep (se 1 (by rfl) ⟨1044356, by rfl⟩ : syracuseStep 1392475 = 2088713) B2088713
theorem B1236991 : Blo 1236436 1236991 := bstep (se 1 (by rfl) ⟨927743, by rfl⟩ : syracuseStep 1236991 = 1855487) B1855487
theorem B1237159 : Blo 1236436 1237159 := bstep (se 1 (by rfl) ⟨927869, by rfl⟩ : syracuseStep 1237159 = 1855739) B1855739
theorem B2089631 : Blo 1236436 2089631 := bstep (se 1 (by rfl) ⟨1567223, by rfl⟩ : syracuseStep 2089631 = 3134447) B3134447
theorem B1237743 : Blo 1236436 1237743 := bstep (se 1 (by rfl) ⟨928307, by rfl⟩ : syracuseStep 1237743 = 1856615) B1856615
theorem B1237951 : Blo 1236436 1237951 := bstep (se 1 (by rfl) ⟨928463, by rfl⟩ : syracuseStep 1237951 = 1856927) B1856927
theorem B3131207 : Blo 1236436 3131207 := bstep (se 1 (by rfl) ⟨2348405, by rfl⟩ : syracuseStep 3131207 = 4696811) B4696811
theorem B5286185 : Blo 1236436 5286185 := bstep (se 2 (by rfl) ⟨1982319, by rfl⟩ : syracuseStep 5286185 = 3964639) B3964639
theorem B5286971 : Blo 1236436 5286971 := bstep (se 1 (by rfl) ⟨3965228, by rfl⟩ : syracuseStep 5286971 = 7930457) B7930457
theorem B5951033 : Blo 1236436 5951033 := bstep (se 2 (by rfl) ⟨2231637, by rfl⟩ : syracuseStep 5951033 = 4463275) B4463275
theorem B2641691 : Blo 1236436 2641691 := bstep (se 1 (by rfl) ⟨1981268, by rfl⟩ : syracuseStep 2641691 = 3962537) B3962537
theorem B1856633 : Blo 1236436 1856633 := bstep (se 2 (by rfl) ⟨696237, by rfl⟩ : syracuseStep 1856633 = 1392475) B1392475
theorem B2782547 : Blo 1236436 2782547 := bstep (se 1 (by rfl) ⟨2086910, by rfl⟩ : syracuseStep 2782547 = 4173821) B4173821
theorem B6264701 : Blo 1236436 6264701 := bstep (se 3 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 6264701 = 2349263) B2349263
theorem B115817465 : Blo 1236436 115817465 := bstep (se 2 (by rfl) ⟨43431549, by rfl⟩ : syracuseStep 115817465 = 86863099) B86863099
theorem B1393087 : Blo 1236436 1393087 := bstep (se 1 (by rfl) ⟨1044815, by rfl⟩ : syracuseStep 1393087 = 2089631) B2089631
theorem B1237755 : Blo 1236436 1237755 := bstep (se 1 (by rfl) ⟨928316, by rfl⟩ : syracuseStep 1237755 = 1856633) B1856633
theorem B3524123 : Blo 1236436 3524123 := bstep (se 1 (by rfl) ⟨2643092, by rfl⟩ : syracuseStep 3524123 = 5286185) B5286185
theorem B77211643 : Blo 1236436 77211643 := bstep (se 1 (by rfl) ⟨57908732, by rfl⟩ : syracuseStep 77211643 = 115817465) B115817465
theorem B3524647 : Blo 1236436 3524647 := bstep (se 1 (by rfl) ⟨2643485, by rfl⟩ : syracuseStep 3524647 = 5286971) B5286971
theorem B3967355 : Blo 1236436 3967355 := bstep (se 1 (by rfl) ⟨2975516, by rfl⟩ : syracuseStep 3967355 = 5951033) B5951033
theorem B1855031 : Blo 1236436 1855031 := bstep (se 1 (by rfl) ⟨1391273, by rfl⟩ : syracuseStep 1855031 = 2782547) B2782547
theorem B2087471 : Blo 1236436 2087471 := bstep (se 1 (by rfl) ⟨1565603, by rfl⟩ : syracuseStep 2087471 = 3131207) B3131207
theorem B4176467 : Blo 1236436 4176467 := bstep (se 1 (by rfl) ⟨3132350, by rfl⟩ : syracuseStep 4176467 = 6264701) B6264701
theorem B7044509 : Blo 1236436 7044509 := bstep (se 3 (by rfl) ⟨1320845, by rfl⟩ : syracuseStep 7044509 = 2641691) B2641691
theorem B4696339 : Blo 1236436 4696339 := bstep (se 1 (by rfl) ⟨3522254, by rfl⟩ : syracuseStep 4696339 = 7044509) B7044509
theorem B4699529 : Blo 1236436 4699529 := bstep (se 2 (by rfl) ⟨1762323, by rfl⟩ : syracuseStep 4699529 = 3524647) B3524647
theorem B1857449 : Blo 1236436 1857449 := bstep (se 2 (by rfl) ⟨696543, by rfl⟩ : syracuseStep 1857449 = 1393087) B1393087
theorem B2349415 : Blo 1236436 2349415 := bstep (se 1 (by rfl) ⟨1762061, by rfl⟩ : syracuseStep 2349415 = 3524123) B3524123
theorem B2644903 : Blo 1236436 2644903 := bstep (se 1 (by rfl) ⟨1983677, by rfl⟩ : syracuseStep 2644903 = 3967355) B3967355
theorem B1391647 : Blo 1236436 1391647 := bstep (se 1 (by rfl) ⟨1043735, by rfl⟩ : syracuseStep 1391647 = 2087471) B2087471
theorem B2784311 : Blo 1236436 2784311 := bstep (se 1 (by rfl) ⟨2088233, by rfl⟩ : syracuseStep 2784311 = 4176467) B4176467
theorem B1236687 : Blo 1236436 1236687 := bstep (se 1 (by rfl) ⟨927515, by rfl⟩ : syracuseStep 1236687 = 1855031) B1855031
theorem B102948857 : Blo 1236436 102948857 := bstep (se 2 (by rfl) ⟨38605821, by rfl⟩ : syracuseStep 102948857 = 77211643) B77211643
theorem B1238299 : Blo 1236436 1238299 := bstep (se 1 (by rfl) ⟨928724, by rfl⟩ : syracuseStep 1238299 = 1857449) B1857449
theorem B6261785 : Blo 1236436 6261785 := bstep (se 2 (by rfl) ⟨2348169, by rfl⟩ : syracuseStep 6261785 = 4696339) B4696339
theorem B3132553 : Blo 1236436 3132553 := bstep (se 2 (by rfl) ⟨1174707, by rfl⟩ : syracuseStep 3132553 = 2349415) B2349415
theorem B3133019 : Blo 1236436 3133019 := bstep (se 1 (by rfl) ⟨2349764, by rfl⟩ : syracuseStep 3133019 = 4699529) B4699529
theorem B1855529 : Blo 1236436 1855529 := bstep (se 2 (by rfl) ⟨695823, by rfl⟩ : syracuseStep 1855529 = 1391647) B1391647
theorem B1856207 : Blo 1236436 1856207 := bstep (se 1 (by rfl) ⟨1392155, by rfl⟩ : syracuseStep 1856207 = 2784311) B2784311
theorem B14106149 : Blo 1236436 14106149 := bstep (se 4 (by rfl) ⟨1322451, by rfl⟩ : syracuseStep 14106149 = 2644903) B2644903
theorem B68632571 : Blo 1236436 68632571 := bstep (se 1 (by rfl) ⟨51474428, by rfl⟩ : syracuseStep 68632571 = 102948857) B102948857
theorem B1237019 : Blo 1236436 1237019 := bstep (se 1 (by rfl) ⟨927764, by rfl⟩ : syracuseStep 1237019 = 1855529) B1855529
theorem B1237471 : Blo 1236436 1237471 := bstep (se 1 (by rfl) ⟨928103, by rfl⟩ : syracuseStep 1237471 = 1856207) B1856207
theorem B45755047 : Blo 1236436 45755047 := bstep (se 1 (by rfl) ⟨34316285, by rfl⟩ : syracuseStep 45755047 = 68632571) B68632571
theorem B4174523 : Blo 1236436 4174523 := bstep (se 1 (by rfl) ⟨3130892, by rfl⟩ : syracuseStep 4174523 = 6261785) B6261785
theorem B4176737 : Blo 1236436 4176737 := bstep (se 2 (by rfl) ⟨1566276, by rfl⟩ : syracuseStep 4176737 = 3132553) B3132553
theorem B9404099 : Blo 1236436 9404099 := bstep (se 1 (by rfl) ⟨7053074, by rfl⟩ : syracuseStep 9404099 = 14106149) B14106149
theorem B2088679 : Blo 1236436 2088679 := bstep (se 1 (by rfl) ⟨1566509, by rfl⟩ : syracuseStep 2088679 = 3133019) B3133019
theorem B6269399 : Blo 1236436 6269399 := bstep (se 1 (by rfl) ⟨4702049, by rfl⟩ : syracuseStep 6269399 = 9404099) B9404099
theorem B244026917 : Blo 1236436 244026917 := bstep (se 4 (by rfl) ⟨22877523, by rfl⟩ : syracuseStep 244026917 = 45755047) B45755047
theorem B2783015 : Blo 1236436 2783015 := bstep (se 1 (by rfl) ⟨2087261, by rfl⟩ : syracuseStep 2783015 = 4174523) B4174523
theorem B2784491 : Blo 1236436 2784491 := bstep (se 1 (by rfl) ⟨2088368, by rfl⟩ : syracuseStep 2784491 = 4176737) B4176737
theorem B2784905 : Blo 1236436 2784905 := bstep (se 2 (by rfl) ⟨1044339, by rfl⟩ : syracuseStep 2784905 = 2088679) B2088679
theorem B4179599 : Blo 1236436 4179599 := bstep (se 1 (by rfl) ⟨3134699, by rfl⟩ : syracuseStep 4179599 = 6269399) B6269399
theorem B1855343 : Blo 1236436 1855343 := bstep (se 1 (by rfl) ⟨1391507, by rfl⟩ : syracuseStep 1855343 = 2783015) B2783015
theorem B1856327 : Blo 1236436 1856327 := bstep (se 1 (by rfl) ⟨1392245, by rfl⟩ : syracuseStep 1856327 = 2784491) B2784491
theorem B1856603 : Blo 1236436 1856603 := bstep (se 1 (by rfl) ⟨1392452, by rfl⟩ : syracuseStep 1856603 = 2784905) B2784905
theorem B162684611 : Blo 1236436 162684611 := bstep (se 1 (by rfl) ⟨122013458, by rfl⟩ : syracuseStep 162684611 = 244026917) B244026917
theorem B1237551 : Blo 1236436 1237551 := bstep (se 1 (by rfl) ⟨928163, by rfl⟩ : syracuseStep 1237551 = 1856327) B1856327
theorem B1237735 : Blo 1236436 1237735 := bstep (se 1 (by rfl) ⟨928301, by rfl⟩ : syracuseStep 1237735 = 1856603) B1856603
theorem B2786399 : Blo 1236436 2786399 := bstep (se 1 (by rfl) ⟨2089799, by rfl⟩ : syracuseStep 2786399 = 4179599) B4179599
theorem B108456407 : Blo 1236436 108456407 := bstep (se 1 (by rfl) ⟨81342305, by rfl⟩ : syracuseStep 108456407 = 162684611) B162684611
theorem B1236895 : Blo 1236436 1236895 := bstep (se 1 (by rfl) ⟨927671, by rfl⟩ : syracuseStep 1236895 = 1855343) B1855343
theorem B72304271 : Blo 1236436 72304271 := bstep (se 1 (by rfl) ⟨54228203, by rfl⟩ : syracuseStep 72304271 = 108456407) B108456407
theorem B1857599 : Blo 1236436 1857599 := bstep (se 1 (by rfl) ⟨1393199, by rfl⟩ : syracuseStep 1857599 = 2786399) B2786399
theorem B48202847 : Blo 1236436 48202847 := bstep (se 1 (by rfl) ⟨36152135, by rfl⟩ : syracuseStep 48202847 = 72304271) B72304271
theorem B1238399 : Blo 1236436 1238399 := bstep (se 1 (by rfl) ⟨928799, by rfl⟩ : syracuseStep 1238399 = 1857599) B1857599
theorem B32135231 : Blo 1236436 32135231 := bstep (se 1 (by rfl) ⟨24101423, by rfl⟩ : syracuseStep 32135231 = 48202847) B48202847
theorem B21423487 : Blo 1236436 21423487 := bstep (se 1 (by rfl) ⟨16067615, by rfl⟩ : syracuseStep 21423487 = 32135231) B32135231
theorem B28564649 : Blo 1236436 28564649 := bstep (se 2 (by rfl) ⟨10711743, by rfl⟩ : syracuseStep 28564649 = 21423487) B21423487
theorem B19043099 : Blo 1236436 19043099 := bstep (se 1 (by rfl) ⟨14282324, by rfl⟩ : syracuseStep 19043099 = 28564649) B28564649
theorem B12695399 : Blo 1236436 12695399 := bstep (se 1 (by rfl) ⟨9521549, by rfl⟩ : syracuseStep 12695399 = 19043099) B19043099
theorem B8463599 : Blo 1236436 8463599 := bstep (se 1 (by rfl) ⟨6347699, by rfl⟩ : syracuseStep 8463599 = 12695399) B12695399
theorem B5642399 : Blo 1236436 5642399 := bstep (se 1 (by rfl) ⟨4231799, by rfl⟩ : syracuseStep 5642399 = 8463599) B8463599
theorem B3761599 : Blo 1236436 3761599 := bstep (se 1 (by rfl) ⟨2821199, by rfl⟩ : syracuseStep 3761599 = 5642399) B5642399
theorem B5015465 : Blo 1236436 5015465 := bstep (se 2 (by rfl) ⟨1880799, by rfl⟩ : syracuseStep 5015465 = 3761599) B3761599
theorem B3343643 : Blo 1236436 3343643 := bstep (se 1 (by rfl) ⟨2507732, by rfl⟩ : syracuseStep 3343643 = 5015465) B5015465
theorem B2229095 : Blo 1236436 2229095 := bstep (se 1 (by rfl) ⟨1671821, by rfl⟩ : syracuseStep 2229095 = 3343643) B3343643
theorem B1486063 : Blo 1236436 1486063 := bstep (se 1 (by rfl) ⟨1114547, by rfl⟩ : syracuseStep 1486063 = 2229095) B2229095
theorem B1981417 : Blo 1236436 1981417 := bstep (se 2 (by rfl) ⟨743031, by rfl⟩ : syracuseStep 1981417 = 1486063) B1486063
theorem B2641889 : Blo 1236436 2641889 := bstep (se 2 (by rfl) ⟨990708, by rfl⟩ : syracuseStep 2641889 = 1981417) B1981417
theorem B1761259 : Blo 1236436 1761259 := bstep (se 1 (by rfl) ⟨1320944, by rfl⟩ : syracuseStep 1761259 = 2641889) B2641889
theorem B2348345 : Blo 1236436 2348345 := bstep (se 2 (by rfl) ⟨880629, by rfl⟩ : syracuseStep 2348345 = 1761259) B1761259
theorem B1565563 : Blo 1236436 1565563 := bstep (se 1 (by rfl) ⟨1174172, by rfl⟩ : syracuseStep 1565563 = 2348345) B2348345
theorem B2087417 : Blo 1236436 2087417 := bstep (se 2 (by rfl) ⟨782781, by rfl⟩ : syracuseStep 2087417 = 1565563) B1565563
theorem B1391611 : Blo 1236436 1391611 := bstep (se 1 (by rfl) ⟨1043708, by rfl⟩ : syracuseStep 1391611 = 2087417) B2087417
theorem B1855481 : Blo 1236436 1855481 := bstep (se 2 (by rfl) ⟨695805, by rfl⟩ : syracuseStep 1855481 = 1391611) B1391611
theorem B1236987 : Blo 1236436 1236987 := bstep (se 1 (by rfl) ⟨927740, by rfl⟩ : syracuseStep 1236987 = 1855481) B1855481

theorem C0 (j : ℕ) (h1 : 309109 ≤ j) (h2 : j ≤ 309608) : Blo 1236436 (4 * j + 3) := by
  interval_cases j
  · exact B1236439
  · exact B1236443
  · exact B1236447
  · exact B1236451
  · exact B1236455
  · exact B1236459
  · exact B1236463
  · exact B1236467
  · exact B1236471
  · exact B1236475
  · exact B1236479
  · exact B1236483
  · exact B1236487
  · exact B1236491
  · exact B1236495
  · exact B1236499
  · exact B1236503
  · exact B1236507
  · exact B1236511
  · exact B1236515
  · exact B1236519
  · exact B1236523
  · exact B1236527
  · exact B1236531
  · exact B1236535
  · exact B1236539
  · exact B1236543
  · exact B1236547
  · exact B1236551
  · exact B1236555
  · exact B1236559
  · exact B1236563
  · exact B1236567
  · exact B1236571
  · exact B1236575
  · exact B1236579
  · exact B1236583
  · exact B1236587
  · exact B1236591
  · exact B1236595
  · exact B1236599
  · exact B1236603
  · exact B1236607
  · exact B1236611
  · exact B1236615
  · exact B1236619
  · exact B1236623
  · exact B1236627
  · exact B1236631
  · exact B1236635
  · exact B1236639
  · exact B1236643
  · exact B1236647
  · exact B1236651
  · exact B1236655
  · exact B1236659
  · exact B1236663
  · exact B1236667
  · exact B1236671
  · exact B1236675
  · exact B1236679
  · exact B1236683
  · exact B1236687
  · exact B1236691
  · exact B1236695
  · exact B1236699
  · exact B1236703
  · exact B1236707
  · exact B1236711
  · exact B1236715
  · exact B1236719
  · exact B1236723
  · exact B1236727
  · exact B1236731
  · exact B1236735
  · exact B1236739
  · exact B1236743
  · exact B1236747
  · exact B1236751
  · exact B1236755
  · exact B1236759
  · exact B1236763
  · exact B1236767
  · exact B1236771
  · exact B1236775
  · exact B1236779
  · exact B1236783
  · exact B1236787
  · exact B1236791
  · exact B1236795
  · exact B1236799
  · exact B1236803
  · exact B1236807
  · exact B1236811
  · exact B1236815
  · exact B1236819
  · exact B1236823
  · exact B1236827
  · exact B1236831
  · exact B1236835
  · exact B1236839
  · exact B1236843
  · exact B1236847
  · exact B1236851
  · exact B1236855
  · exact B1236859
  · exact B1236863
  · exact B1236867
  · exact B1236871
  · exact B1236875
  · exact B1236879
  · exact B1236883
  · exact B1236887
  · exact B1236891
  · exact B1236895
  · exact B1236899
  · exact B1236903
  · exact B1236907
  · exact B1236911
  · exact B1236915
  · exact B1236919
  · exact B1236923
  · exact B1236927
  · exact B1236931
  · exact B1236935
  · exact B1236939
  · exact B1236943
  · exact B1236947
  · exact B1236951
  · exact B1236955
  · exact B1236959
  · exact B1236963
  · exact B1236967
  · exact B1236971
  · exact B1236975
  · exact B1236979
  · exact B1236983
  · exact B1236987
  · exact B1236991
  · exact B1236995
  · exact B1236999
  · exact B1237003
  · exact B1237007
  · exact B1237011
  · exact B1237015
  · exact B1237019
  · exact B1237023
  · exact B1237027
  · exact B1237031
  · exact B1237035
  · exact B1237039
  · exact B1237043
  · exact B1237047
  · exact B1237051
  · exact B1237055
  · exact B1237059
  · exact B1237063
  · exact B1237067
  · exact B1237071
  · exact B1237075
  · exact B1237079
  · exact B1237083
  · exact B1237087
  · exact B1237091
  · exact B1237095
  · exact B1237099
  · exact B1237103
  · exact B1237107
  · exact B1237111
  · exact B1237115
  · exact B1237119
  · exact B1237123
  · exact B1237127
  · exact B1237131
  · exact B1237135
  · exact B1237139
  · exact B1237143
  · exact B1237147
  · exact B1237151
  · exact B1237155
  · exact B1237159
  · exact B1237163
  · exact B1237167
  · exact B1237171
  · exact B1237175
  · exact B1237179
  · exact B1237183
  · exact B1237187
  · exact B1237191
  · exact B1237195
  · exact B1237199
  · exact B1237203
  · exact B1237207
  · exact B1237211
  · exact B1237215
  · exact B1237219
  · exact B1237223
  · exact B1237227
  · exact B1237231
  · exact B1237235
  · exact B1237239
  · exact B1237243
  · exact B1237247
  · exact B1237251
  · exact B1237255
  · exact B1237259
  · exact B1237263
  · exact B1237267
  · exact B1237271
  · exact B1237275
  · exact B1237279
  · exact B1237283
  · exact B1237287
  · exact B1237291
  · exact B1237295
  · exact B1237299
  · exact B1237303
  · exact B1237307
  · exact B1237311
  · exact B1237315
  · exact B1237319
  · exact B1237323
  · exact B1237327
  · exact B1237331
  · exact B1237335
  · exact B1237339
  · exact B1237343
  · exact B1237347
  · exact B1237351
  · exact B1237355
  · exact B1237359
  · exact B1237363
  · exact B1237367
  · exact B1237371
  · exact B1237375
  · exact B1237379
  · exact B1237383
  · exact B1237387
  · exact B1237391
  · exact B1237395
  · exact B1237399
  · exact B1237403
  · exact B1237407
  · exact B1237411
  · exact B1237415
  · exact B1237419
  · exact B1237423
  · exact B1237427
  · exact B1237431
  · exact B1237435
  · exact B1237439
  · exact B1237443
  · exact B1237447
  · exact B1237451
  · exact B1237455
  · exact B1237459
  · exact B1237463
  · exact B1237467
  · exact B1237471
  · exact B1237475
  · exact B1237479
  · exact B1237483
  · exact B1237487
  · exact B1237491
  · exact B1237495
  · exact B1237499
  · exact B1237503
  · exact B1237507
  · exact B1237511
  · exact B1237515
  · exact B1237519
  · exact B1237523
  · exact B1237527
  · exact B1237531
  · exact B1237535
  · exact B1237539
  · exact B1237543
  · exact B1237547
  · exact B1237551
  · exact B1237555
  · exact B1237559
  · exact B1237563
  · exact B1237567
  · exact B1237571
  · exact B1237575
  · exact B1237579
  · exact B1237583
  · exact B1237587
  · exact B1237591
  · exact B1237595
  · exact B1237599
  · exact B1237603
  · exact B1237607
  · exact B1237611
  · exact B1237615
  · exact B1237619
  · exact B1237623
  · exact B1237627
  · exact B1237631
  · exact B1237635
  · exact B1237639
  · exact B1237643
  · exact B1237647
  · exact B1237651
  · exact B1237655
  · exact B1237659
  · exact B1237663
  · exact B1237667
  · exact B1237671
  · exact B1237675
  · exact B1237679
  · exact B1237683
  · exact B1237687
  · exact B1237691
  · exact B1237695
  · exact B1237699
  · exact B1237703
  · exact B1237707
  · exact B1237711
  · exact B1237715
  · exact B1237719
  · exact B1237723
  · exact B1237727
  · exact B1237731
  · exact B1237735
  · exact B1237739
  · exact B1237743
  · exact B1237747
  · exact B1237751
  · exact B1237755
  · exact B1237759
  · exact B1237763
  · exact B1237767
  · exact B1237771
  · exact B1237775
  · exact B1237779
  · exact B1237783
  · exact B1237787
  · exact B1237791
  · exact B1237795
  · exact B1237799
  · exact B1237803
  · exact B1237807
  · exact B1237811
  · exact B1237815
  · exact B1237819
  · exact B1237823
  · exact B1237827
  · exact B1237831
  · exact B1237835
  · exact B1237839
  · exact B1237843
  · exact B1237847
  · exact B1237851
  · exact B1237855
  · exact B1237859
  · exact B1237863
  · exact B1237867
  · exact B1237871
  · exact B1237875
  · exact B1237879
  · exact B1237883
  · exact B1237887
  · exact B1237891
  · exact B1237895
  · exact B1237899
  · exact B1237903
  · exact B1237907
  · exact B1237911
  · exact B1237915
  · exact B1237919
  · exact B1237923
  · exact B1237927
  · exact B1237931
  · exact B1237935
  · exact B1237939
  · exact B1237943
  · exact B1237947
  · exact B1237951
  · exact B1237955
  · exact B1237959
  · exact B1237963
  · exact B1237967
  · exact B1237971
  · exact B1237975
  · exact B1237979
  · exact B1237983
  · exact B1237987
  · exact B1237991
  · exact B1237995
  · exact B1237999
  · exact B1238003
  · exact B1238007
  · exact B1238011
  · exact B1238015
  · exact B1238019
  · exact B1238023
  · exact B1238027
  · exact B1238031
  · exact B1238035
  · exact B1238039
  · exact B1238043
  · exact B1238047
  · exact B1238051
  · exact B1238055
  · exact B1238059
  · exact B1238063
  · exact B1238067
  · exact B1238071
  · exact B1238075
  · exact B1238079
  · exact B1238083
  · exact B1238087
  · exact B1238091
  · exact B1238095
  · exact B1238099
  · exact B1238103
  · exact B1238107
  · exact B1238111
  · exact B1238115
  · exact B1238119
  · exact B1238123
  · exact B1238127
  · exact B1238131
  · exact B1238135
  · exact B1238139
  · exact B1238143
  · exact B1238147
  · exact B1238151
  · exact B1238155
  · exact B1238159
  · exact B1238163
  · exact B1238167
  · exact B1238171
  · exact B1238175
  · exact B1238179
  · exact B1238183
  · exact B1238187
  · exact B1238191
  · exact B1238195
  · exact B1238199
  · exact B1238203
  · exact B1238207
  · exact B1238211
  · exact B1238215
  · exact B1238219
  · exact B1238223
  · exact B1238227
  · exact B1238231
  · exact B1238235
  · exact B1238239
  · exact B1238243
  · exact B1238247
  · exact B1238251
  · exact B1238255
  · exact B1238259
  · exact B1238263
  · exact B1238267
  · exact B1238271
  · exact B1238275
  · exact B1238279
  · exact B1238283
  · exact B1238287
  · exact B1238291
  · exact B1238295
  · exact B1238299
  · exact B1238303
  · exact B1238307
  · exact B1238311
  · exact B1238315
  · exact B1238319
  · exact B1238323
  · exact B1238327
  · exact B1238331
  · exact B1238335
  · exact B1238339
  · exact B1238343
  · exact B1238347
  · exact B1238351
  · exact B1238355
  · exact B1238359
  · exact B1238363
  · exact B1238367
  · exact B1238371
  · exact B1238375
  · exact B1238379
  · exact B1238383
  · exact B1238387
  · exact B1238391
  · exact B1238395
  · exact B1238399
  · exact B1238403
  · exact B1238407
  · exact B1238411
  · exact B1238415
  · exact B1238419
  · exact B1238423
  · exact B1238427
  · exact B1238431
  · exact B1238435

theorem solution (m : ℕ) (hlo : 1236436 ≤ m) (hhi : m ≤ 1238436) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 309109 ≤ j := by omega
    have hj2 : j ≤ 309608 := by omega
    have hb : Blo 1236436 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
