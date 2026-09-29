-- Prove2me | solution 1 for syracuse_descends_range_838352_842352
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:51.283321+00:00
-- url     : https://prove2.me/submissions/68e23ca4-8b47-41c5-9642-2a0351219a5f

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


theorem B2130077 : Blo 838352 2130077 := bbase (se 3 (by rfl) ⟨399389, by rfl⟩ : syracuseStep 2130077 = 798779) (by norm_num)
theorem B7176437 : Blo 838352 7176437 := bbase (se 5 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 7176437 = 672791) (by norm_num)
theorem B2687269 : Blo 838352 2687269 := bbase (se 4 (by rfl) ⟨251931, by rfl⟩ : syracuseStep 2687269 = 503863) (by norm_num)
theorem B2130421 : Blo 838352 2130421 := bbase (se 5 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 2130421 = 199727) (by norm_num)
theorem B3408437 : Blo 838352 3408437 := bbase (se 5 (by rfl) ⟨159770, by rfl⟩ : syracuseStep 3408437 = 319541) (by norm_num)
theorem B9568853 : Blo 838352 9568853 := bbase (se 8 (by rfl) ⟨56067, by rfl⟩ : syracuseStep 9568853 = 112135) (by norm_num)
theorem B4260437 : Blo 838352 4260437 := bbase (se 8 (by rfl) ⟨24963, by rfl⟩ : syracuseStep 4260437 = 49927) (by norm_num)
theorem B2130533 : Blo 838352 2130533 := bbase (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) (by norm_num)
theorem B1344109 : Blo 838352 1344109 := bbase (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) (by norm_num)
theorem B2130725 : Blo 838352 2130725 := bbase (se 4 (by rfl) ⟨199755, by rfl⟩ : syracuseStep 2130725 = 399511) (by norm_num)
theorem B1344365 : Blo 838352 1344365 := bbase (se 3 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 1344365 = 504137) (by norm_num)
theorem B3277685 : Blo 838352 3277685 := bbase (se 5 (by rfl) ⟨153641, by rfl⟩ : syracuseStep 3277685 = 307283) (by norm_num)
theorem B2556805 : Blo 838352 2556805 := bbase (se 4 (by rfl) ⟨239700, by rfl⟩ : syracuseStep 2556805 = 479401) (by norm_num)
theorem B1704925 : Blo 838352 1704925 := bbase (se 3 (by rfl) ⟨319673, by rfl⟩ : syracuseStep 1704925 = 639347) (by norm_num)
theorem B4031461 : Blo 838352 4031461 := bbase (se 4 (by rfl) ⟨377949, by rfl⟩ : syracuseStep 4031461 = 755899) (by norm_num)
theorem B1344557 : Blo 838352 1344557 := bbase (se 3 (by rfl) ⟨252104, by rfl⟩ : syracuseStep 1344557 = 504209) (by norm_num)
theorem B41976917 : Blo 838352 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B2131069 : Blo 838352 2131069 := bbase (se 3 (by rfl) ⟨399575, by rfl⟩ : syracuseStep 2131069 = 799151) (by norm_num)
theorem B2557109 : Blo 838352 2557109 := bbase (se 5 (by rfl) ⟨119864, by rfl⟩ : syracuseStep 2557109 = 239729) (by norm_num)
theorem B2131181 : Blo 838352 2131181 := bbase (se 3 (by rfl) ⟨399596, by rfl⟩ : syracuseStep 2131181 = 799193) (by norm_num)
theorem B2131373 : Blo 838352 2131373 := bbase (se 3 (by rfl) ⟨399632, by rfl⟩ : syracuseStep 2131373 = 799265) (by norm_num)
theorem B1705445 : Blo 838352 1705445 := bbase (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) (by norm_num)
theorem B4785749 : Blo 838352 4785749 := bbase (se 8 (by rfl) ⟨28041, by rfl⟩ : syracuseStep 4785749 = 56083) (by norm_num)
theorem B2131717 : Blo 838352 2131717 := bbase (se 4 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 2131717 = 399697) (by norm_num)
theorem B4261733 : Blo 838352 4261733 := bbase (se 4 (by rfl) ⟨399537, by rfl⟩ : syracuseStep 4261733 = 799075) (by norm_num)
theorem B2131829 : Blo 838352 2131829 := bbase (se 5 (by rfl) ⟨99929, by rfl⟩ : syracuseStep 2131829 = 199859) (by norm_num)
theorem B1345493 : Blo 838352 1345493 := bbase (se 7 (by rfl) ⟨15767, by rfl⟩ : syracuseStep 1345493 = 31535) (by norm_num)
theorem B2132021 : Blo 838352 2132021 := bbase (se 5 (by rfl) ⟨99938, by rfl⟩ : syracuseStep 2132021 = 199877) (by norm_num)
theorem B985225 : Blo 838352 985225 := bbase (se 2 (by rfl) ⟨369459, by rfl⟩ : syracuseStep 985225 = 738919) (by norm_num)
theorem B1640749 : Blo 838352 1640749 := bbase (se 3 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 1640749 = 615281) (by norm_num)
theorem B1345877 : Blo 838352 1345877 := bbase (se 10 (by rfl) ⟨1971, by rfl⟩ : syracuseStep 1345877 = 3943) (by norm_num)
theorem B1346005 : Blo 838352 1346005 := bbase (se 7 (by rfl) ⟨15773, by rfl⟩ : syracuseStep 1346005 = 31547) (by norm_num)
theorem B2394629 : Blo 838352 2394629 := bbase (se 4 (by rfl) ⟨224496, by rfl⟩ : syracuseStep 2394629 = 448993) (by norm_num)
theorem B3410581 : Blo 838352 3410581 := bbase (se 6 (by rfl) ⟨79935, by rfl⟩ : syracuseStep 3410581 = 159871) (by norm_num)
theorem B2690101 : Blo 838352 2690101 := bbase (se 5 (by rfl) ⟨126098, by rfl⟩ : syracuseStep 2690101 = 252197) (by norm_num)
theorem B2690165 : Blo 838352 2690165 := bbase (se 5 (by rfl) ⟨126101, by rfl⟩ : syracuseStep 2690165 = 252203) (by norm_num)
theorem B4263029 : Blo 838352 4263029 := bbase (se 5 (by rfl) ⟨199829, by rfl⟩ : syracuseStep 4263029 = 399659) (by norm_num)
theorem B2428181 : Blo 838352 2428181 := bbase (se 6 (by rfl) ⟨56910, by rfl⟩ : syracuseStep 2428181 = 113821) (by norm_num)
theorem B1347005 : Blo 838352 1347005 := bbase (se 3 (by rfl) ⟨252563, by rfl⟩ : syracuseStep 1347005 = 505127) (by norm_num)
theorem B1347133 : Blo 838352 1347133 := bbase (se 3 (by rfl) ⟨252587, by rfl⟩ : syracuseStep 1347133 = 505175) (by norm_num)
theorem B2395813 : Blo 838352 2395813 := bbase (se 4 (by rfl) ⟨224607, by rfl⟩ : syracuseStep 2395813 = 449215) (by norm_num)
theorem B2920133 : Blo 838352 2920133 := bbase (se 4 (by rfl) ⟨273762, by rfl⟩ : syracuseStep 2920133 = 547525) (by norm_num)
theorem B2395973 : Blo 838352 2395973 := bbase (se 4 (by rfl) ⟨224622, by rfl⟩ : syracuseStep 2395973 = 449245) (by norm_num)
theorem B1347517 : Blo 838352 1347517 := bbase (se 3 (by rfl) ⟨252659, by rfl⟩ : syracuseStep 1347517 = 505319) (by norm_num)
theorem B3411925 : Blo 838352 3411925 := bbase (se 7 (by rfl) ⟨39983, by rfl⟩ : syracuseStep 3411925 = 79967) (by norm_num)
theorem B1511453 : Blo 838352 1511453 := bbase (se 3 (by rfl) ⟨283397, by rfl⟩ : syracuseStep 1511453 = 566795) (by norm_num)
theorem B2396213 : Blo 838352 2396213 := bbase (se 5 (by rfl) ⟨112322, by rfl⟩ : syracuseStep 2396213 = 224645) (by norm_num)
theorem B8065109 : Blo 838352 8065109 := bbase (se 8 (by rfl) ⟨47256, by rfl⟩ : syracuseStep 8065109 = 94513) (by norm_num)
theorem B1347773 : Blo 838352 1347773 := bbase (se 3 (by rfl) ⟨252707, by rfl⟩ : syracuseStep 1347773 = 505415) (by norm_num)
theorem B2396405 : Blo 838352 2396405 := bbase (se 5 (by rfl) ⟨112331, by rfl⟩ : syracuseStep 2396405 = 224663) (by norm_num)
theorem B1511741 : Blo 838352 1511741 := bbase (se 3 (by rfl) ⟨283451, by rfl⟩ : syracuseStep 1511741 = 566903) (by norm_num)
theorem B4264325 : Blo 838352 4264325 := bbase (se 4 (by rfl) ⟨399780, by rfl⟩ : syracuseStep 4264325 = 799561) (by norm_num)
theorem B2560405 : Blo 838352 2560405 := bbase (se 6 (by rfl) ⟨60009, by rfl⟩ : syracuseStep 2560405 = 120019) (by norm_num)
theorem B922097 : Blo 838352 922097 := bbase (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) (by norm_num)
theorem B8622773 : Blo 838352 8622773 := bbase (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) (by norm_num)
theorem B4035365 : Blo 838352 4035365 := bbase (se 4 (by rfl) ⟨378315, by rfl⟩ : syracuseStep 4035365 = 756631) (by norm_num)
theorem B2331605 : Blo 838352 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B1348645 : Blo 838352 1348645 := bbase (se 4 (by rfl) ⟨126435, by rfl⟩ : syracuseStep 1348645 = 252871) (by norm_num)
theorem B1348741 : Blo 838352 1348741 := bbase (se 4 (by rfl) ⟨126444, by rfl⟩ : syracuseStep 1348741 = 252889) (by norm_num)
theorem B2266325 : Blo 838352 2266325 := bbase (se 7 (by rfl) ⟨26558, by rfl⟩ : syracuseStep 2266325 = 53117) (by norm_num)
theorem B2397397 : Blo 838352 2397397 := bbase (se 7 (by rfl) ⟨28094, by rfl⟩ : syracuseStep 2397397 = 56189) (by norm_num)
theorem B3183893 : Blo 838352 3183893 := bbase (se 6 (by rfl) ⟨74622, by rfl⟩ : syracuseStep 3183893 = 149245) (by norm_num)
theorem B1348901 : Blo 838352 1348901 := bbase (se 4 (by rfl) ⟨126459, by rfl⟩ : syracuseStep 1348901 = 252919) (by norm_num)
theorem B1021397 : Blo 838352 1021397 := bbase (se 7 (by rfl) ⟨11969, by rfl⟩ : syracuseStep 1021397 = 23939) (by norm_num)
theorem B1021465 : Blo 838352 1021465 := bbase (se 2 (by rfl) ⟨383049, by rfl⟩ : syracuseStep 1021465 = 766099) (by norm_num)
theorem B3184181 : Blo 838352 3184181 := bbase (se 5 (by rfl) ⟨149258, by rfl⟩ : syracuseStep 3184181 = 298517) (by norm_num)
theorem B1414813 : Blo 838352 1414813 := bbase (se 3 (by rfl) ⟨265277, by rfl⟩ : syracuseStep 1414813 = 530555) (by norm_num)
theorem B1513189 : Blo 838352 1513189 := bbase (se 4 (by rfl) ⟨141861, by rfl⟩ : syracuseStep 1513189 = 283723) (by norm_num)
theorem B1414901 : Blo 838352 1414901 := bbase (se 5 (by rfl) ⟨66323, by rfl⟩ : syracuseStep 1414901 = 132647) (by norm_num)
theorem B1415029 : Blo 838352 1415029 := bbase (se 5 (by rfl) ⟨66329, by rfl⟩ : syracuseStep 1415029 = 132659) (by norm_num)
theorem B1513333 : Blo 838352 1513333 := bbase (se 5 (by rfl) ⟨70937, by rfl⟩ : syracuseStep 1513333 = 141875) (by norm_num)
theorem B1415117 : Blo 838352 1415117 := bbase (se 3 (by rfl) ⟨265334, by rfl⟩ : syracuseStep 1415117 = 530669) (by norm_num)
theorem B2693189 : Blo 838352 2693189 := bbase (se 4 (by rfl) ⟨252486, by rfl⟩ : syracuseStep 2693189 = 504973) (by norm_num)
theorem B1415245 : Blo 838352 1415245 := bbase (se 3 (by rfl) ⟨265358, by rfl⟩ : syracuseStep 1415245 = 530717) (by norm_num)
theorem B25860181 : Blo 838352 25860181 := bbase (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) (by norm_num)
theorem B1415333 : Blo 838352 1415333 := bbase (se 4 (by rfl) ⟨132687, by rfl⟩ : syracuseStep 1415333 = 265375) (by norm_num)
theorem B5445845 : Blo 838352 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B1415461 : Blo 838352 1415461 := bbase (se 4 (by rfl) ⟨132699, by rfl⟩ : syracuseStep 1415461 = 265399) (by norm_num)
theorem B2398501 : Blo 838352 2398501 := bbase (se 4 (by rfl) ⟨224859, by rfl⟩ : syracuseStep 2398501 = 449719) (by norm_num)
theorem B6396245 : Blo 838352 6396245 := bbase (se 10 (by rfl) ⟨9369, by rfl⟩ : syracuseStep 6396245 = 18739) (by norm_num)
theorem B1415549 : Blo 838352 1415549 := bbase (se 3 (by rfl) ⟨265415, by rfl⟩ : syracuseStep 1415549 = 530831) (by norm_num)
theorem B9083285 : Blo 838352 9083285 := bbase (se 6 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 9083285 = 425779) (by norm_num)
theorem B1415677 : Blo 838352 1415677 := bbase (se 3 (by rfl) ⟨265439, by rfl⟩ : syracuseStep 1415677 = 530879) (by norm_num)
theorem B2595349 : Blo 838352 2595349 := bbase (se 6 (by rfl) ⟨60828, by rfl⟩ : syracuseStep 2595349 = 121657) (by norm_num)
theorem B6068789 : Blo 838352 6068789 := bbase (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) (by norm_num)
theorem B1415765 : Blo 838352 1415765 := bbase (se 8 (by rfl) ⟨8295, by rfl⟩ : syracuseStep 1415765 = 16591) (by norm_num)
theorem B1514141 : Blo 838352 1514141 := bbase (se 3 (by rfl) ⟨283901, by rfl⟩ : syracuseStep 1514141 = 567803) (by norm_num)
theorem B3185365 : Blo 838352 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B1415893 : Blo 838352 1415893 := bbase (se 7 (by rfl) ⟨16592, by rfl⟩ : syracuseStep 1415893 = 33185) (by norm_num)
theorem B1415981 : Blo 838352 1415981 := bbase (se 3 (by rfl) ⟨265496, by rfl⟩ : syracuseStep 1415981 = 530993) (by norm_num)
theorem B3021637 : Blo 838352 3021637 := bbase (se 4 (by rfl) ⟨283278, by rfl⟩ : syracuseStep 3021637 = 566557) (by norm_num)
theorem B957269 : Blo 838352 957269 := bbase (se 9 (by rfl) ⟨2804, by rfl⟩ : syracuseStep 957269 = 5609) (by norm_num)
theorem B8624981 : Blo 838352 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B1416109 : Blo 838352 1416109 := bbase (se 3 (by rfl) ⟨265520, by rfl⟩ : syracuseStep 1416109 = 531041) (by norm_num)
theorem B1514501 : Blo 838352 1514501 := bbase (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) (by norm_num)
theorem B3185669 : Blo 838352 3185669 := bbase (se 4 (by rfl) ⟨298656, by rfl⟩ : syracuseStep 3185669 = 597313) (by norm_num)
theorem B1416197 : Blo 838352 1416197 := bbase (se 4 (by rfl) ⟨132768, by rfl⟩ : syracuseStep 1416197 = 265537) (by norm_num)
theorem B1416325 : Blo 838352 1416325 := bbase (se 4 (by rfl) ⟨132780, by rfl⟩ : syracuseStep 1416325 = 265561) (by norm_num)
theorem B1416413 : Blo 838352 1416413 := bbase (se 3 (by rfl) ⟨265577, by rfl⟩ : syracuseStep 1416413 = 531155) (by norm_num)
theorem B1416541 : Blo 838352 1416541 := bbase (se 3 (by rfl) ⟨265601, by rfl⟩ : syracuseStep 1416541 = 531203) (by norm_num)
theorem B957853 : Blo 838352 957853 := bbase (se 3 (by rfl) ⟨179597, by rfl⟩ : syracuseStep 957853 = 359195) (by norm_num)
theorem B1416629 : Blo 838352 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B1416757 : Blo 838352 1416757 := bbase (se 5 (by rfl) ⟨66410, by rfl⟩ : syracuseStep 1416757 = 132821) (by norm_num)
theorem B4038245 : Blo 838352 4038245 := bbase (se 4 (by rfl) ⟨378585, by rfl⟩ : syracuseStep 4038245 = 757171) (by norm_num)
theorem B1416845 : Blo 838352 1416845 := bbase (se 3 (by rfl) ⟨265658, by rfl⟩ : syracuseStep 1416845 = 531317) (by norm_num)
theorem B3546821 : Blo 838352 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B1416973 : Blo 838352 1416973 := bbase (se 3 (by rfl) ⟨265682, by rfl⟩ : syracuseStep 1416973 = 531365) (by norm_num)
theorem B8625973 : Blo 838352 8625973 := bbase (se 5 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 8625973 = 808685) (by norm_num)
theorem B92118869 : Blo 838352 92118869 := bbase (se 9 (by rfl) ⟨269879, by rfl⟩ : syracuseStep 92118869 = 539759) (by norm_num)
theorem B1417061 : Blo 838352 1417061 := bbase (se 4 (by rfl) ⟨132849, by rfl⟩ : syracuseStep 1417061 = 265699) (by norm_num)
theorem B2269093 : Blo 838352 2269093 := bbase (se 4 (by rfl) ⟨212727, by rfl⟩ : syracuseStep 2269093 = 425455) (by norm_num)
theorem B1417189 : Blo 838352 1417189 := bbase (se 4 (by rfl) ⟨132861, by rfl⟩ : syracuseStep 1417189 = 265723) (by norm_num)
theorem B1417277 : Blo 838352 1417277 := bbase (se 3 (by rfl) ⟨265739, by rfl⟩ : syracuseStep 1417277 = 531479) (by norm_num)
theorem B1417405 : Blo 838352 1417405 := bbase (se 3 (by rfl) ⟨265763, by rfl⟩ : syracuseStep 1417405 = 531527) (by norm_num)
theorem B958729 : Blo 838352 958729 := bbase (se 2 (by rfl) ⟨359523, by rfl⟩ : syracuseStep 958729 = 719047) (by norm_num)
theorem B1417493 : Blo 838352 1417493 := bbase (se 6 (by rfl) ⟨33222, by rfl⟩ : syracuseStep 1417493 = 66445) (by norm_num)
theorem B958825 : Blo 838352 958825 := bbase (se 2 (by rfl) ⟨359559, by rfl⟩ : syracuseStep 958825 = 719119) (by norm_num)
theorem B1417621 : Blo 838352 1417621 := bbase (se 6 (by rfl) ⟨33225, by rfl⟩ : syracuseStep 1417621 = 66451) (by norm_num)
theorem B1417709 : Blo 838352 1417709 := bbase (se 3 (by rfl) ⟨265820, by rfl⟩ : syracuseStep 1417709 = 531641) (by norm_num)
theorem B6824533 : Blo 838352 6824533 := bbase (se 8 (by rfl) ⟨39987, by rfl⟩ : syracuseStep 6824533 = 79975) (by norm_num)
theorem B1417837 : Blo 838352 1417837 := bbase (se 3 (by rfl) ⟨265844, by rfl⟩ : syracuseStep 1417837 = 531689) (by norm_num)
theorem B1417925 : Blo 838352 1417925 := bbase (se 4 (by rfl) ⟨132930, by rfl⟩ : syracuseStep 1417925 = 265861) (by norm_num)
theorem B5186261 : Blo 838352 5186261 := bbase (se 7 (by rfl) ⟨60776, by rfl⟩ : syracuseStep 5186261 = 121553) (by norm_num)
theorem B3023669 : Blo 838352 3023669 := bbase (se 5 (by rfl) ⟨141734, by rfl⟩ : syracuseStep 3023669 = 283469) (by norm_num)
theorem B1418053 : Blo 838352 1418053 := bbase (se 4 (by rfl) ⟨132942, by rfl⟩ : syracuseStep 1418053 = 265885) (by norm_num)
theorem B3449749 : Blo 838352 3449749 := bbase (se 6 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 3449749 = 161707) (by norm_num)
theorem B1418141 : Blo 838352 1418141 := bbase (se 3 (by rfl) ⟨265901, by rfl⟩ : syracuseStep 1418141 = 531803) (by norm_num)
theorem B1418269 : Blo 838352 1418269 := bbase (se 3 (by rfl) ⟨265925, by rfl⟩ : syracuseStep 1418269 = 531851) (by norm_num)
theorem B2270261 : Blo 838352 2270261 := bbase (se 5 (by rfl) ⟨106418, by rfl⟩ : syracuseStep 2270261 = 212837) (by norm_num)
theorem B959545 : Blo 838352 959545 := bbase (se 2 (by rfl) ⟨359829, by rfl⟩ : syracuseStep 959545 = 719659) (by norm_num)
theorem B3187781 : Blo 838352 3187781 := bbase (se 4 (by rfl) ⟨298854, by rfl⟩ : syracuseStep 3187781 = 597709) (by norm_num)
theorem B3646565 : Blo 838352 3646565 := bbase (se 4 (by rfl) ⟨341865, by rfl⟩ : syracuseStep 3646565 = 683731) (by norm_num)
theorem B1418357 : Blo 838352 1418357 := bbase (se 5 (by rfl) ⟨66485, by rfl⟩ : syracuseStep 1418357 = 132971) (by norm_num)
theorem B2270389 : Blo 838352 2270389 := bbase (se 5 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 2270389 = 212849) (by norm_num)
theorem B1516765 : Blo 838352 1516765 := bbase (se 3 (by rfl) ⟨284393, by rfl⟩ : syracuseStep 1516765 = 568787) (by norm_num)
theorem B1418485 : Blo 838352 1418485 := bbase (se 5 (by rfl) ⟨66491, by rfl⟩ : syracuseStep 1418485 = 132983) (by norm_num)
theorem B1418573 : Blo 838352 1418573 := bbase (se 3 (by rfl) ⟨265982, by rfl⟩ : syracuseStep 1418573 = 531965) (by norm_num)
theorem B3188069 : Blo 838352 3188069 := bbase (se 4 (by rfl) ⟨298881, by rfl⟩ : syracuseStep 3188069 = 597763) (by norm_num)
theorem B1516909 : Blo 838352 1516909 := bbase (se 3 (by rfl) ⟨284420, by rfl⟩ : syracuseStep 1516909 = 568841) (by norm_num)
theorem B959897 : Blo 838352 959897 := bbase (se 2 (by rfl) ⟨359961, by rfl⟩ : syracuseStep 959897 = 719923) (by norm_num)
theorem B1418701 : Blo 838352 1418701 := bbase (se 3 (by rfl) ⟨266006, by rfl⟩ : syracuseStep 1418701 = 532013) (by norm_num)
theorem B4793813 : Blo 838352 4793813 := bbase (se 7 (by rfl) ⟨56177, by rfl⟩ : syracuseStep 4793813 = 112355) (by norm_num)
theorem B1418789 : Blo 838352 1418789 := bbase (se 4 (by rfl) ⟨133011, by rfl⟩ : syracuseStep 1418789 = 266023) (by norm_num)
theorem B1517125 : Blo 838352 1517125 := bbase (se 4 (by rfl) ⟨142230, by rfl⟩ : syracuseStep 1517125 = 284461) (by norm_num)
theorem B3024533 : Blo 838352 3024533 := bbase (se 6 (by rfl) ⟨70887, by rfl⟩ : syracuseStep 3024533 = 141775) (by norm_num)
theorem B1418917 : Blo 838352 1418917 := bbase (se 4 (by rfl) ⟨133023, by rfl⟩ : syracuseStep 1418917 = 266047) (by norm_num)
theorem B3155669 : Blo 838352 3155669 := bbase (se 7 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 3155669 = 73961) (by norm_num)
theorem B960229 : Blo 838352 960229 := bbase (se 4 (by rfl) ⟨90021, by rfl⟩ : syracuseStep 960229 = 180043) (by norm_num)
theorem B4040437 : Blo 838352 4040437 := bbase (se 5 (by rfl) ⟨189395, by rfl⟩ : syracuseStep 4040437 = 378791) (by norm_num)
theorem B1419005 : Blo 838352 1419005 := bbase (se 3 (by rfl) ⟨266063, by rfl⟩ : syracuseStep 1419005 = 532127) (by norm_num)
theorem B2696981 : Blo 838352 2696981 := bbase (se 6 (by rfl) ⟨63210, by rfl⟩ : syracuseStep 2696981 = 126421) (by norm_num)
theorem B1615645 : Blo 838352 1615645 := bbase (se 3 (by rfl) ⟨302933, by rfl⟩ : syracuseStep 1615645 = 605867) (by norm_num)
theorem B1419133 : Blo 838352 1419133 := bbase (se 3 (by rfl) ⟨266087, by rfl⟩ : syracuseStep 1419133 = 532175) (by norm_num)
theorem B1419221 : Blo 838352 1419221 := bbase (se 7 (by rfl) ⟨16631, by rfl⟩ : syracuseStep 1419221 = 33263) (by norm_num)
theorem B862273 : Blo 838352 862273 := bbase (se 2 (by rfl) ⟨323352, by rfl⟩ : syracuseStep 862273 = 646705) (by norm_num)
theorem B1419349 : Blo 838352 1419349 := bbase (se 8 (by rfl) ⟨8316, by rfl⟩ : syracuseStep 1419349 = 16633) (by norm_num)
theorem B1419437 : Blo 838352 1419437 := bbase (se 3 (by rfl) ⟨266144, by rfl⟩ : syracuseStep 1419437 = 532289) (by norm_num)
theorem B3025109 : Blo 838352 3025109 := bbase (se 7 (by rfl) ⟨35450, by rfl⟩ : syracuseStep 3025109 = 70901) (by norm_num)
theorem B1419565 : Blo 838352 1419565 := bbase (se 3 (by rfl) ⟨266168, by rfl⟩ : syracuseStep 1419565 = 532337) (by norm_num)
theorem B1517933 : Blo 838352 1517933 := bbase (se 3 (by rfl) ⟨284612, by rfl⟩ : syracuseStep 1517933 = 569225) (by norm_num)
theorem B1419653 : Blo 838352 1419653 := bbase (se 4 (by rfl) ⟨133092, by rfl⟩ : syracuseStep 1419653 = 266185) (by norm_num)
theorem B3189253 : Blo 838352 3189253 := bbase (se 4 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 3189253 = 597985) (by norm_num)
theorem B1419781 : Blo 838352 1419781 := bbase (se 4 (by rfl) ⟨133104, by rfl⟩ : syracuseStep 1419781 = 266209) (by norm_num)
theorem B895573 : Blo 838352 895573 := bbase (se 8 (by rfl) ⟨5247, by rfl⟩ : syracuseStep 895573 = 10495) (by norm_num)
theorem B5384789 : Blo 838352 5384789 := bbase (se 8 (by rfl) ⟨31551, by rfl⟩ : syracuseStep 5384789 = 63103) (by norm_num)
theorem B1419869 : Blo 838352 1419869 := bbase (se 3 (by rfl) ⟨266225, by rfl⟩ : syracuseStep 1419869 = 532451) (by norm_num)
theorem B4794997 : Blo 838352 4794997 := bbase (se 5 (by rfl) ⟨224765, by rfl⟩ : syracuseStep 4794997 = 449531) (by norm_num)
theorem B895645 : Blo 838352 895645 := bbase (se 3 (by rfl) ⟨167933, by rfl⟩ : syracuseStep 895645 = 335867) (by norm_num)
theorem B2697893 : Blo 838352 2697893 := bbase (se 4 (by rfl) ⟨252927, by rfl⟩ : syracuseStep 2697893 = 505855) (by norm_num)
theorem B1419997 : Blo 838352 1419997 := bbase (se 3 (by rfl) ⟨266249, by rfl⟩ : syracuseStep 1419997 = 532499) (by norm_num)
theorem B3189557 : Blo 838352 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B1420085 : Blo 838352 1420085 := bbase (se 5 (by rfl) ⟨66566, by rfl⟩ : syracuseStep 1420085 = 133133) (by norm_num)
theorem B1420213 : Blo 838352 1420213 := bbase (se 5 (by rfl) ⟨66572, by rfl⟩ : syracuseStep 1420213 = 133145) (by norm_num)
theorem B1420301 : Blo 838352 1420301 := bbase (se 3 (by rfl) ⟨266306, by rfl⟩ : syracuseStep 1420301 = 532613) (by norm_num)
theorem B896017 : Blo 838352 896017 := bbase (se 2 (by rfl) ⟨336006, by rfl⟩ : syracuseStep 896017 = 672013) (by norm_num)
theorem B1420429 : Blo 838352 1420429 := bbase (se 3 (by rfl) ⟨266330, by rfl⟩ : syracuseStep 1420429 = 532661) (by norm_num)
theorem B1420517 : Blo 838352 1420517 := bbase (se 4 (by rfl) ⟨133173, by rfl⟩ : syracuseStep 1420517 = 266347) (by norm_num)
theorem B2829653 : Blo 838352 2829653 := bbase (se 11 (by rfl) ⟨2072, by rfl⟩ : syracuseStep 2829653 = 4145) (by norm_num)
theorem B1420645 : Blo 838352 1420645 := bbase (se 4 (by rfl) ⟨133185, by rfl⟩ : syracuseStep 1420645 = 266371) (by norm_num)
theorem B896393 : Blo 838352 896393 := bbase (se 2 (by rfl) ⟨336147, by rfl⟩ : syracuseStep 896393 = 672295) (by norm_num)
theorem B1420733 : Blo 838352 1420733 := bbase (se 3 (by rfl) ⟨266387, by rfl⟩ : syracuseStep 1420733 = 532775) (by norm_num)
theorem B896465 : Blo 838352 896465 := bbase (se 2 (by rfl) ⟨336174, by rfl⟩ : syracuseStep 896465 = 672349) (by norm_num)
theorem B6237653 : Blo 838352 6237653 := bbase (se 7 (by rfl) ⟨73097, by rfl⟩ : syracuseStep 6237653 = 146195) (by norm_num)
theorem B1420861 : Blo 838352 1420861 := bbase (se 3 (by rfl) ⟨266411, by rfl⟩ : syracuseStep 1420861 = 532823) (by norm_num)
theorem B1617509 : Blo 838352 1617509 := bbase (se 4 (by rfl) ⟨151641, by rfl⟩ : syracuseStep 1617509 = 303283) (by norm_num)
theorem B1912429 : Blo 838352 1912429 := bbase (se 3 (by rfl) ⟨358580, by rfl⟩ : syracuseStep 1912429 = 717161) (by norm_num)
theorem B896653 : Blo 838352 896653 := bbase (se 3 (by rfl) ⟨168122, by rfl⟩ : syracuseStep 896653 = 336245) (by norm_num)
theorem B1420949 : Blo 838352 1420949 := bbase (se 6 (by rfl) ⟨33303, by rfl⟩ : syracuseStep 1420949 = 66607) (by norm_num)
theorem B2830085 : Blo 838352 2830085 := bbase (se 4 (by rfl) ⟨265320, by rfl⟩ : syracuseStep 2830085 = 530641) (by norm_num)
theorem B1421077 : Blo 838352 1421077 := bbase (se 6 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 1421077 = 66613) (by norm_num)
theorem B896837 : Blo 838352 896837 := bbase (se 4 (by rfl) ⟨84078, by rfl⟩ : syracuseStep 896837 = 168157) (by norm_num)
theorem B2273093 : Blo 838352 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B2043749 : Blo 838352 2043749 := bbase (se 4 (by rfl) ⟨191601, by rfl⟩ : syracuseStep 2043749 = 383203) (by norm_num)
theorem B1421165 : Blo 838352 1421165 := bbase (se 3 (by rfl) ⟨266468, by rfl⟩ : syracuseStep 1421165 = 532937) (by norm_num)
theorem B1421293 : Blo 838352 1421293 := bbase (se 3 (by rfl) ⟨266492, by rfl⟩ : syracuseStep 1421293 = 532985) (by norm_num)
theorem B7188533 : Blo 838352 7188533 := bbase (se 5 (by rfl) ⟨336962, by rfl⟩ : syracuseStep 7188533 = 673925) (by norm_num)
theorem B1257533 : Blo 838352 1257533 := bbase (se 3 (by rfl) ⟨235787, by rfl⟩ : syracuseStep 1257533 = 471575) (by norm_num)
theorem B1421381 : Blo 838352 1421381 := bbase (se 4 (by rfl) ⟨133254, by rfl⟩ : syracuseStep 1421381 = 266509) (by norm_num)
theorem B1257557 : Blo 838352 1257557 := bbase (se 8 (by rfl) ⟨7368, by rfl⟩ : syracuseStep 1257557 = 14737) (by norm_num)
theorem B1257581 : Blo 838352 1257581 := bbase (se 3 (by rfl) ⟨235796, by rfl⟩ : syracuseStep 1257581 = 471593) (by norm_num)
theorem B1257605 : Blo 838352 1257605 := bbase (se 4 (by rfl) ⟨117900, by rfl⟩ : syracuseStep 1257605 = 235801) (by norm_num)
theorem B1257629 : Blo 838352 1257629 := bbase (se 3 (by rfl) ⟨235805, by rfl⟩ : syracuseStep 1257629 = 471611) (by norm_num)
theorem B1257653 : Blo 838352 1257653 := bbase (se 5 (by rfl) ⟨58952, by rfl⟩ : syracuseStep 1257653 = 117905) (by norm_num)
theorem B2830517 : Blo 838352 2830517 := bbase (se 5 (by rfl) ⟨132680, by rfl⟩ : syracuseStep 2830517 = 265361) (by norm_num)
theorem B1257677 : Blo 838352 1257677 := bbase (se 3 (by rfl) ⟨235814, by rfl⟩ : syracuseStep 1257677 = 471629) (by norm_num)
theorem B10367189 : Blo 838352 10367189 := bbase (se 7 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 10367189 = 242981) (by norm_num)
theorem B1257701 : Blo 838352 1257701 := bbase (se 4 (by rfl) ⟨117909, by rfl⟩ : syracuseStep 1257701 = 235819) (by norm_num)
theorem B1257725 : Blo 838352 1257725 := bbase (se 3 (by rfl) ⟨235823, by rfl⟩ : syracuseStep 1257725 = 471647) (by norm_num)
theorem B1257749 : Blo 838352 1257749 := bbase (se 6 (by rfl) ⟨29478, by rfl⟩ : syracuseStep 1257749 = 58957) (by norm_num)
theorem B1257773 : Blo 838352 1257773 := bbase (se 3 (by rfl) ⟨235832, by rfl⟩ : syracuseStep 1257773 = 471665) (by norm_num)
theorem B1257797 : Blo 838352 1257797 := bbase (se 4 (by rfl) ⟨117918, by rfl⟩ : syracuseStep 1257797 = 235837) (by norm_num)
theorem B1061201 : Blo 838352 1061201 := bbase (se 2 (by rfl) ⟨397950, by rfl⟩ : syracuseStep 1061201 = 795901) (by norm_num)
theorem B1257821 : Blo 838352 1257821 := bbase (se 3 (by rfl) ⟨235841, by rfl⟩ : syracuseStep 1257821 = 471683) (by norm_num)
theorem B3584357 : Blo 838352 3584357 := bbase (se 4 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 3584357 = 672067) (by norm_num)
theorem B1257845 : Blo 838352 1257845 := bbase (se 5 (by rfl) ⟨58961, by rfl⟩ : syracuseStep 1257845 = 117923) (by norm_num)
theorem B1061257 : Blo 838352 1061257 := bbase (se 2 (by rfl) ⟨397971, by rfl⟩ : syracuseStep 1061257 = 795943) (by norm_num)
theorem B1257869 : Blo 838352 1257869 := bbase (se 3 (by rfl) ⟨235850, by rfl⟩ : syracuseStep 1257869 = 471701) (by norm_num)
theorem B1257893 : Blo 838352 1257893 := bbase (se 4 (by rfl) ⟨117927, by rfl⟩ : syracuseStep 1257893 = 235855) (by norm_num)
theorem B1913269 : Blo 838352 1913269 := bbase (se 5 (by rfl) ⟨89684, by rfl⟩ : syracuseStep 1913269 = 179369) (by norm_num)
theorem B1257917 : Blo 838352 1257917 := bbase (se 3 (by rfl) ⟨235859, by rfl⟩ : syracuseStep 1257917 = 471719) (by norm_num)
theorem B1257941 : Blo 838352 1257941 := bbase (se 7 (by rfl) ⟨14741, by rfl⟩ : syracuseStep 1257941 = 29483) (by norm_num)
theorem B1061353 : Blo 838352 1061353 := bbase (se 2 (by rfl) ⟨398007, by rfl⟩ : syracuseStep 1061353 = 796015) (by norm_num)
theorem B1257965 : Blo 838352 1257965 := bbase (se 3 (by rfl) ⟨235868, by rfl⟩ : syracuseStep 1257965 = 471737) (by norm_num)
theorem B1257989 : Blo 838352 1257989 := bbase (se 4 (by rfl) ⟨117936, by rfl⟩ : syracuseStep 1257989 = 235873) (by norm_num)
theorem B1258013 : Blo 838352 1258013 := bbase (se 3 (by rfl) ⟨235877, by rfl⟩ : syracuseStep 1258013 = 471755) (by norm_num)
theorem B1258037 : Blo 838352 1258037 := bbase (se 5 (by rfl) ⟨58970, by rfl⟩ : syracuseStep 1258037 = 117941) (by norm_num)
theorem B897589 : Blo 838352 897589 := bbase (se 5 (by rfl) ⟨42074, by rfl⟩ : syracuseStep 897589 = 84149) (by norm_num)
theorem B4796981 : Blo 838352 4796981 := bbase (se 5 (by rfl) ⟨224858, by rfl⟩ : syracuseStep 4796981 = 449717) (by norm_num)
theorem B1258061 : Blo 838352 1258061 := bbase (se 3 (by rfl) ⟨235886, by rfl⟩ : syracuseStep 1258061 = 471773) (by norm_num)
theorem B1258085 : Blo 838352 1258085 := bbase (se 4 (by rfl) ⟨117945, by rfl⟩ : syracuseStep 1258085 = 235891) (by norm_num)
theorem B2830949 : Blo 838352 2830949 := bbase (se 4 (by rfl) ⟨265401, by rfl⟩ : syracuseStep 2830949 = 530803) (by norm_num)
theorem B1913453 : Blo 838352 1913453 := bbase (se 3 (by rfl) ⟨358772, by rfl⟩ : syracuseStep 1913453 = 717545) (by norm_num)
theorem B1258109 : Blo 838352 1258109 := bbase (se 3 (by rfl) ⟨235895, by rfl⟩ : syracuseStep 1258109 = 471791) (by norm_num)
theorem B897661 : Blo 838352 897661 := bbase (se 3 (by rfl) ⟨168311, by rfl⟩ : syracuseStep 897661 = 336623) (by norm_num)
theorem B1061525 : Blo 838352 1061525 := bbase (se 6 (by rfl) ⟨24879, by rfl⟩ : syracuseStep 1061525 = 49759) (by norm_num)
theorem B1258133 : Blo 838352 1258133 := bbase (se 6 (by rfl) ⟨29487, by rfl⟩ : syracuseStep 1258133 = 58975) (by norm_num)
theorem B1258157 : Blo 838352 1258157 := bbase (se 3 (by rfl) ⟨235904, by rfl⟩ : syracuseStep 1258157 = 471809) (by norm_num)
theorem B1258181 : Blo 838352 1258181 := bbase (se 4 (by rfl) ⟨117954, by rfl⟩ : syracuseStep 1258181 = 235909) (by norm_num)
theorem B1061581 : Blo 838352 1061581 := bbase (se 3 (by rfl) ⟨199046, by rfl⟩ : syracuseStep 1061581 = 398093) (by norm_num)
theorem B1258205 : Blo 838352 1258205 := bbase (se 3 (by rfl) ⟨235913, by rfl⟩ : syracuseStep 1258205 = 471827) (by norm_num)
theorem B1258229 : Blo 838352 1258229 := bbase (se 5 (by rfl) ⟨58979, by rfl⟩ : syracuseStep 1258229 = 117959) (by norm_num)
theorem B1258253 : Blo 838352 1258253 := bbase (se 3 (by rfl) ⟨235922, by rfl⟩ : syracuseStep 1258253 = 471845) (by norm_num)
theorem B1258277 : Blo 838352 1258277 := bbase (se 4 (by rfl) ⟨117963, by rfl⟩ : syracuseStep 1258277 = 235927) (by norm_num)
theorem B1061677 : Blo 838352 1061677 := bbase (se 3 (by rfl) ⟨199064, by rfl⟩ : syracuseStep 1061677 = 398129) (by norm_num)
theorem B897841 : Blo 838352 897841 := bbase (se 2 (by rfl) ⟨336690, by rfl⟩ : syracuseStep 897841 = 673381) (by norm_num)
theorem B1258301 : Blo 838352 1258301 := bbase (se 3 (by rfl) ⟨235931, by rfl⟩ : syracuseStep 1258301 = 471863) (by norm_num)
theorem B1258325 : Blo 838352 1258325 := bbase (se 9 (by rfl) ⟨3686, by rfl⟩ : syracuseStep 1258325 = 7373) (by norm_num)
theorem B1258349 : Blo 838352 1258349 := bbase (se 3 (by rfl) ⟨235940, by rfl⟩ : syracuseStep 1258349 = 471881) (by norm_num)
theorem B3191669 : Blo 838352 3191669 := bbase (se 5 (by rfl) ⟨149609, by rfl⟩ : syracuseStep 3191669 = 299219) (by norm_num)
theorem B1258373 : Blo 838352 1258373 := bbase (se 4 (by rfl) ⟨117972, by rfl⟩ : syracuseStep 1258373 = 235945) (by norm_num)
theorem B1258397 : Blo 838352 1258397 := bbase (se 3 (by rfl) ⟨235949, by rfl⟩ : syracuseStep 1258397 = 471899) (by norm_num)
theorem B1258421 : Blo 838352 1258421 := bbase (se 5 (by rfl) ⟨58988, by rfl⟩ : syracuseStep 1258421 = 117977) (by norm_num)
theorem B1258445 : Blo 838352 1258445 := bbase (se 3 (by rfl) ⟨235958, by rfl⟩ : syracuseStep 1258445 = 471917) (by norm_num)
theorem B1061849 : Blo 838352 1061849 := bbase (se 2 (by rfl) ⟨398193, by rfl⟩ : syracuseStep 1061849 = 796387) (by norm_num)
theorem B1258469 : Blo 838352 1258469 := bbase (se 4 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 1258469 = 235963) (by norm_num)
theorem B1258493 : Blo 838352 1258493 := bbase (se 3 (by rfl) ⟨235967, by rfl⟩ : syracuseStep 1258493 = 471935) (by norm_num)
theorem B1061905 : Blo 838352 1061905 := bbase (se 2 (by rfl) ⟨398214, by rfl⟩ : syracuseStep 1061905 = 796429) (by norm_num)
theorem B2831381 : Blo 838352 2831381 := bbase (se 6 (by rfl) ⟨66360, by rfl⟩ : syracuseStep 2831381 = 132721) (by norm_num)
theorem B1258517 : Blo 838352 1258517 := bbase (se 6 (by rfl) ⟨29496, by rfl⟩ : syracuseStep 1258517 = 58993) (by norm_num)
theorem B1258541 : Blo 838352 1258541 := bbase (se 3 (by rfl) ⟨235976, by rfl⟩ : syracuseStep 1258541 = 471953) (by norm_num)
theorem B1258565 : Blo 838352 1258565 := bbase (se 4 (by rfl) ⟨117990, by rfl⟩ : syracuseStep 1258565 = 235981) (by norm_num)
theorem B1258589 : Blo 838352 1258589 := bbase (se 3 (by rfl) ⟨235985, by rfl⟩ : syracuseStep 1258589 = 471971) (by norm_num)
theorem B1062001 : Blo 838352 1062001 := bbase (se 2 (by rfl) ⟨398250, by rfl⟩ : syracuseStep 1062001 = 796501) (by norm_num)
theorem B1258613 : Blo 838352 1258613 := bbase (se 5 (by rfl) ⟨58997, by rfl⟩ : syracuseStep 1258613 = 117995) (by norm_num)
theorem B1258637 : Blo 838352 1258637 := bbase (se 3 (by rfl) ⟨235994, by rfl⟩ : syracuseStep 1258637 = 471989) (by norm_num)
theorem B3191957 : Blo 838352 3191957 := bbase (se 6 (by rfl) ⟨74811, by rfl⟩ : syracuseStep 3191957 = 149623) (by norm_num)
theorem B1258661 : Blo 838352 1258661 := bbase (se 4 (by rfl) ⟨117999, by rfl⟩ : syracuseStep 1258661 = 235999) (by norm_num)
theorem B1258685 : Blo 838352 1258685 := bbase (se 3 (by rfl) ⟨236003, by rfl⟩ : syracuseStep 1258685 = 472007) (by norm_num)
theorem B1258709 : Blo 838352 1258709 := bbase (se 7 (by rfl) ⟨14750, by rfl⟩ : syracuseStep 1258709 = 29501) (by norm_num)
theorem B1258733 : Blo 838352 1258733 := bbase (se 3 (by rfl) ⟨236012, by rfl⟩ : syracuseStep 1258733 = 472025) (by norm_num)
theorem B898285 : Blo 838352 898285 := bbase (se 3 (by rfl) ⟨168428, by rfl⟩ : syracuseStep 898285 = 336857) (by norm_num)
theorem B1258757 : Blo 838352 1258757 := bbase (se 4 (by rfl) ⟨118008, by rfl⟩ : syracuseStep 1258757 = 236017) (by norm_num)
theorem B1258781 : Blo 838352 1258781 := bbase (se 3 (by rfl) ⟨236021, by rfl⟩ : syracuseStep 1258781 = 472043) (by norm_num)
theorem B1062173 : Blo 838352 1062173 := bbase (se 3 (by rfl) ⟨199157, by rfl⟩ : syracuseStep 1062173 = 398315) (by norm_num)
theorem B1258805 : Blo 838352 1258805 := bbase (se 5 (by rfl) ⟨59006, by rfl⟩ : syracuseStep 1258805 = 118013) (by norm_num)
theorem B1258829 : Blo 838352 1258829 := bbase (se 3 (by rfl) ⟨236030, by rfl⟩ : syracuseStep 1258829 = 472061) (by norm_num)
theorem B1062229 : Blo 838352 1062229 := bbase (se 13 (by rfl) ⟨194, by rfl⟩ : syracuseStep 1062229 = 389) (by norm_num)
theorem B1258853 : Blo 838352 1258853 := bbase (se 4 (by rfl) ⟨118017, by rfl⟩ : syracuseStep 1258853 = 236035) (by norm_num)
theorem B898409 : Blo 838352 898409 := bbase (se 2 (by rfl) ⟨336903, by rfl⟩ : syracuseStep 898409 = 673807) (by norm_num)
theorem B1258877 : Blo 838352 1258877 := bbase (se 3 (by rfl) ⟨236039, by rfl⟩ : syracuseStep 1258877 = 472079) (by norm_num)
theorem B1258901 : Blo 838352 1258901 := bbase (se 6 (by rfl) ⟨29505, by rfl⟩ : syracuseStep 1258901 = 59011) (by norm_num)
theorem B1258925 : Blo 838352 1258925 := bbase (se 3 (by rfl) ⟨236048, by rfl⟩ : syracuseStep 1258925 = 472097) (by norm_num)
theorem B1062325 : Blo 838352 1062325 := bbase (se 5 (by rfl) ⟨49796, by rfl⟩ : syracuseStep 1062325 = 99593) (by norm_num)
theorem B2831813 : Blo 838352 2831813 := bbase (se 4 (by rfl) ⟨265482, by rfl⟩ : syracuseStep 2831813 = 530965) (by norm_num)
theorem B1258949 : Blo 838352 1258949 := bbase (se 4 (by rfl) ⟨118026, by rfl⟩ : syracuseStep 1258949 = 236053) (by norm_num)
theorem B1258973 : Blo 838352 1258973 := bbase (se 3 (by rfl) ⟨236057, by rfl⟩ : syracuseStep 1258973 = 472115) (by norm_num)
theorem B1258997 : Blo 838352 1258997 := bbase (se 5 (by rfl) ⟨59015, by rfl⟩ : syracuseStep 1258997 = 118031) (by norm_num)
theorem B1259021 : Blo 838352 1259021 := bbase (se 3 (by rfl) ⟨236066, by rfl⟩ : syracuseStep 1259021 = 472133) (by norm_num)
theorem B1259045 : Blo 838352 1259045 := bbase (se 4 (by rfl) ⟨118035, by rfl⟩ : syracuseStep 1259045 = 236071) (by norm_num)
theorem B1259069 : Blo 838352 1259069 := bbase (se 3 (by rfl) ⟨236075, by rfl⟩ : syracuseStep 1259069 = 472151) (by norm_num)
theorem B1619525 : Blo 838352 1619525 := bbase (se 4 (by rfl) ⟨151830, by rfl⟩ : syracuseStep 1619525 = 303661) (by norm_num)
theorem B1095245 : Blo 838352 1095245 := bbase (se 3 (by rfl) ⟨205358, by rfl⟩ : syracuseStep 1095245 = 410717) (by norm_num)
theorem B1259093 : Blo 838352 1259093 := bbase (se 8 (by rfl) ⟨7377, by rfl⟩ : syracuseStep 1259093 = 14755) (by norm_num)
theorem B1062497 : Blo 838352 1062497 := bbase (se 2 (by rfl) ⟨398436, by rfl⟩ : syracuseStep 1062497 = 796873) (by norm_num)
theorem B898661 : Blo 838352 898661 := bbase (se 4 (by rfl) ⟨84249, by rfl⟩ : syracuseStep 898661 = 168499) (by norm_num)
theorem B1259117 : Blo 838352 1259117 := bbase (se 3 (by rfl) ⟨236084, by rfl⟩ : syracuseStep 1259117 = 472169) (by norm_num)
theorem B1259141 : Blo 838352 1259141 := bbase (se 4 (by rfl) ⟨118044, by rfl⟩ : syracuseStep 1259141 = 236089) (by norm_num)
theorem B4044437 : Blo 838352 4044437 := bbase (se 6 (by rfl) ⟨94791, by rfl⟩ : syracuseStep 4044437 = 189583) (by norm_num)
theorem B1062553 : Blo 838352 1062553 := bbase (se 2 (by rfl) ⟨398457, by rfl⟩ : syracuseStep 1062553 = 796915) (by norm_num)
theorem B1259165 : Blo 838352 1259165 := bbase (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) (by norm_num)
theorem B1259189 : Blo 838352 1259189 := bbase (se 5 (by rfl) ⟨59024, by rfl⟩ : syracuseStep 1259189 = 118049) (by norm_num)
theorem B1259213 : Blo 838352 1259213 := bbase (se 3 (by rfl) ⟨236102, by rfl⟩ : syracuseStep 1259213 = 472205) (by norm_num)
theorem B1259237 : Blo 838352 1259237 := bbase (se 4 (by rfl) ⟨118053, by rfl⟩ : syracuseStep 1259237 = 236107) (by norm_num)
theorem B1062649 : Blo 838352 1062649 := bbase (se 2 (by rfl) ⟨398493, by rfl⟩ : syracuseStep 1062649 = 796987) (by norm_num)
theorem B1259261 : Blo 838352 1259261 := bbase (se 3 (by rfl) ⟨236111, by rfl⟩ : syracuseStep 1259261 = 472223) (by norm_num)
theorem B1259285 : Blo 838352 1259285 := bbase (se 6 (by rfl) ⟨29514, by rfl⟩ : syracuseStep 1259285 = 59029) (by norm_num)
theorem B1259309 : Blo 838352 1259309 := bbase (se 3 (by rfl) ⟨236120, by rfl⟩ : syracuseStep 1259309 = 472241) (by norm_num)
theorem B1259333 : Blo 838352 1259333 := bbase (se 4 (by rfl) ⟨118062, by rfl⟩ : syracuseStep 1259333 = 236125) (by norm_num)
theorem B1259357 : Blo 838352 1259357 := bbase (se 3 (by rfl) ⟨236129, by rfl⟩ : syracuseStep 1259357 = 472259) (by norm_num)
theorem B2832245 : Blo 838352 2832245 := bbase (se 5 (by rfl) ⟨132761, by rfl⟩ : syracuseStep 2832245 = 265523) (by norm_num)
theorem B1259381 : Blo 838352 1259381 := bbase (se 5 (by rfl) ⟨59033, by rfl⟩ : syracuseStep 1259381 = 118067) (by norm_num)
theorem B1193869 : Blo 838352 1193869 := bbase (se 3 (by rfl) ⟨223850, by rfl⟩ : syracuseStep 1193869 = 447701) (by norm_num)
theorem B1259405 : Blo 838352 1259405 := bbase (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) (by norm_num)
theorem B1259429 : Blo 838352 1259429 := bbase (se 4 (by rfl) ⟨118071, by rfl⟩ : syracuseStep 1259429 = 236143) (by norm_num)
theorem B1062821 : Blo 838352 1062821 := bbase (se 4 (by rfl) ⟨99639, by rfl⟩ : syracuseStep 1062821 = 199279) (by norm_num)
theorem B1259453 : Blo 838352 1259453 := bbase (se 3 (by rfl) ⟨236147, by rfl⟩ : syracuseStep 1259453 = 472295) (by norm_num)
theorem B1259477 : Blo 838352 1259477 := bbase (se 7 (by rfl) ⟨14759, by rfl⟩ : syracuseStep 1259477 = 29519) (by norm_num)
theorem B1062877 : Blo 838352 1062877 := bbase (se 3 (by rfl) ⟨199289, by rfl⟩ : syracuseStep 1062877 = 398579) (by norm_num)
theorem B1259501 : Blo 838352 1259501 := bbase (se 3 (by rfl) ⟨236156, by rfl⟩ : syracuseStep 1259501 = 472313) (by norm_num)
theorem B1259525 : Blo 838352 1259525 := bbase (se 4 (by rfl) ⟨118080, by rfl⟩ : syracuseStep 1259525 = 236161) (by norm_num)
theorem B1259549 : Blo 838352 1259549 := bbase (se 3 (by rfl) ⟨236165, by rfl⟩ : syracuseStep 1259549 = 472331) (by norm_num)
theorem B899105 : Blo 838352 899105 := bbase (se 2 (by rfl) ⟨337164, by rfl⟩ : syracuseStep 899105 = 674329) (by norm_num)
theorem B1259573 : Blo 838352 1259573 := bbase (se 5 (by rfl) ⟨59042, by rfl⟩ : syracuseStep 1259573 = 118085) (by norm_num)
theorem B1062973 : Blo 838352 1062973 := bbase (se 3 (by rfl) ⟨199307, by rfl⟩ : syracuseStep 1062973 = 398615) (by norm_num)
theorem B1259597 : Blo 838352 1259597 := bbase (se 3 (by rfl) ⟨236174, by rfl⟩ : syracuseStep 1259597 = 472349) (by norm_num)
theorem B3586133 : Blo 838352 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B1259621 : Blo 838352 1259621 := bbase (se 4 (by rfl) ⟨118089, by rfl⟩ : syracuseStep 1259621 = 236179) (by norm_num)
theorem B1259645 : Blo 838352 1259645 := bbase (se 3 (by rfl) ⟨236183, by rfl⟩ : syracuseStep 1259645 = 472367) (by norm_num)
theorem B1259669 : Blo 838352 1259669 := bbase (se 6 (by rfl) ⟨29523, by rfl⟩ : syracuseStep 1259669 = 59047) (by norm_num)
theorem B1259693 : Blo 838352 1259693 := bbase (se 3 (by rfl) ⟨236192, by rfl⟩ : syracuseStep 1259693 = 472385) (by norm_num)
theorem B1259717 : Blo 838352 1259717 := bbase (se 4 (by rfl) ⟨118098, by rfl⟩ : syracuseStep 1259717 = 236197) (by norm_num)
theorem B1194205 : Blo 838352 1194205 := bbase (se 3 (by rfl) ⟨223913, by rfl⟩ : syracuseStep 1194205 = 447827) (by norm_num)
theorem B1259741 : Blo 838352 1259741 := bbase (se 3 (by rfl) ⟨236201, by rfl⟩ : syracuseStep 1259741 = 472403) (by norm_num)
theorem B1063145 : Blo 838352 1063145 := bbase (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) (by norm_num)
theorem B1259765 : Blo 838352 1259765 := bbase (se 5 (by rfl) ⟨59051, by rfl⟩ : syracuseStep 1259765 = 118103) (by norm_num)
theorem B1259789 : Blo 838352 1259789 := bbase (se 3 (by rfl) ⟨236210, by rfl⟩ : syracuseStep 1259789 = 472421) (by norm_num)
theorem B899353 : Blo 838352 899353 := bbase (se 2 (by rfl) ⟨337257, by rfl⟩ : syracuseStep 899353 = 674515) (by norm_num)
theorem B1063201 : Blo 838352 1063201 := bbase (se 2 (by rfl) ⟨398700, by rfl⟩ : syracuseStep 1063201 = 797401) (by norm_num)
theorem B2832677 : Blo 838352 2832677 := bbase (se 4 (by rfl) ⟨265563, by rfl⟩ : syracuseStep 2832677 = 531127) (by norm_num)
theorem B1259813 : Blo 838352 1259813 := bbase (se 4 (by rfl) ⟨118107, by rfl⟩ : syracuseStep 1259813 = 236215) (by norm_num)
theorem B3193141 : Blo 838352 3193141 := bbase (se 5 (by rfl) ⟨149678, by rfl⟩ : syracuseStep 3193141 = 299357) (by norm_num)
theorem B1259837 : Blo 838352 1259837 := bbase (se 3 (by rfl) ⟨236219, by rfl⟩ : syracuseStep 1259837 = 472439) (by norm_num)
theorem B1259861 : Blo 838352 1259861 := bbase (se 10 (by rfl) ⟨1845, by rfl⟩ : syracuseStep 1259861 = 3691) (by norm_num)
theorem B1259885 : Blo 838352 1259885 := bbase (se 3 (by rfl) ⟨236228, by rfl⟩ : syracuseStep 1259885 = 472457) (by norm_num)
theorem B1063297 : Blo 838352 1063297 := bbase (se 2 (by rfl) ⟨398736, by rfl⟩ : syracuseStep 1063297 = 797473) (by norm_num)
theorem B1259909 : Blo 838352 1259909 := bbase (se 4 (by rfl) ⟨118116, by rfl⟩ : syracuseStep 1259909 = 236233) (by norm_num)
theorem B1259933 : Blo 838352 1259933 := bbase (se 3 (by rfl) ⟨236237, by rfl⟩ : syracuseStep 1259933 = 472475) (by norm_num)
theorem B1194421 : Blo 838352 1194421 := bbase (se 5 (by rfl) ⟨55988, by rfl⟩ : syracuseStep 1194421 = 111977) (by norm_num)
theorem B1259957 : Blo 838352 1259957 := bbase (se 5 (by rfl) ⟨59060, by rfl⟩ : syracuseStep 1259957 = 118121) (by norm_num)
theorem B1259981 : Blo 838352 1259981 := bbase (se 3 (by rfl) ⟨236246, by rfl⟩ : syracuseStep 1259981 = 472493) (by norm_num)
theorem B1260005 : Blo 838352 1260005 := bbase (se 4 (by rfl) ⟨118125, by rfl⟩ : syracuseStep 1260005 = 236251) (by norm_num)
theorem B1260029 : Blo 838352 1260029 := bbase (se 3 (by rfl) ⟨236255, by rfl⟩ : syracuseStep 1260029 = 472511) (by norm_num)
theorem B1260053 : Blo 838352 1260053 := bbase (se 6 (by rfl) ⟨29532, by rfl⟩ : syracuseStep 1260053 = 59065) (by norm_num)
theorem B1260077 : Blo 838352 1260077 := bbase (se 3 (by rfl) ⟨236264, by rfl⟩ : syracuseStep 1260077 = 472529) (by norm_num)
theorem B1063469 : Blo 838352 1063469 := bbase (se 3 (by rfl) ⟨199400, by rfl⟩ : syracuseStep 1063469 = 398801) (by norm_num)
theorem B1260101 : Blo 838352 1260101 := bbase (se 4 (by rfl) ⟨118134, by rfl⟩ : syracuseStep 1260101 = 236269) (by norm_num)
theorem B1260125 : Blo 838352 1260125 := bbase (se 3 (by rfl) ⟨236273, by rfl⟩ : syracuseStep 1260125 = 472547) (by norm_num)
theorem B1063525 : Blo 838352 1063525 := bbase (se 4 (by rfl) ⟨99705, by rfl⟩ : syracuseStep 1063525 = 199411) (by norm_num)
theorem B3193445 : Blo 838352 3193445 := bbase (se 4 (by rfl) ⟨299385, by rfl⟩ : syracuseStep 3193445 = 598771) (by norm_num)
theorem B1260149 : Blo 838352 1260149 := bbase (se 5 (by rfl) ⟨59069, by rfl⟩ : syracuseStep 1260149 = 118139) (by norm_num)
theorem B1260173 : Blo 838352 1260173 := bbase (se 3 (by rfl) ⟨236282, by rfl⟩ : syracuseStep 1260173 = 472565) (by norm_num)
theorem B1260197 : Blo 838352 1260197 := bbase (se 4 (by rfl) ⟨118143, by rfl⟩ : syracuseStep 1260197 = 236287) (by norm_num)
theorem B1260221 : Blo 838352 1260221 := bbase (se 3 (by rfl) ⟨236291, by rfl⟩ : syracuseStep 1260221 = 472583) (by norm_num)
theorem B1063621 : Blo 838352 1063621 := bbase (se 4 (by rfl) ⟨99714, by rfl⟩ : syracuseStep 1063621 = 199429) (by norm_num)
theorem B2833109 : Blo 838352 2833109 := bbase (se 7 (by rfl) ⟨33200, by rfl⟩ : syracuseStep 2833109 = 66401) (by norm_num)
theorem B1260245 : Blo 838352 1260245 := bbase (se 7 (by rfl) ⟨14768, by rfl⟩ : syracuseStep 1260245 = 29537) (by norm_num)
theorem B1260269 : Blo 838352 1260269 := bbase (se 3 (by rfl) ⟨236300, by rfl⟩ : syracuseStep 1260269 = 472601) (by norm_num)
theorem B1260293 : Blo 838352 1260293 := bbase (se 4 (by rfl) ⟨118152, by rfl⟩ : syracuseStep 1260293 = 236305) (by norm_num)
theorem B1260317 : Blo 838352 1260317 := bbase (se 3 (by rfl) ⟨236309, by rfl⟩ : syracuseStep 1260317 = 472619) (by norm_num)
theorem B1194797 : Blo 838352 1194797 := bbase (se 3 (by rfl) ⟨224024, by rfl⟩ : syracuseStep 1194797 = 448049) (by norm_num)
theorem B1260341 : Blo 838352 1260341 := bbase (se 5 (by rfl) ⟨59078, by rfl⟩ : syracuseStep 1260341 = 118157) (by norm_num)
theorem B1260365 : Blo 838352 1260365 := bbase (se 3 (by rfl) ⟨236318, by rfl⟩ : syracuseStep 1260365 = 472637) (by norm_num)
theorem B1260389 : Blo 838352 1260389 := bbase (se 4 (by rfl) ⟨118161, by rfl⟩ : syracuseStep 1260389 = 236323) (by norm_num)
theorem B1063793 : Blo 838352 1063793 := bbase (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) (by norm_num)
theorem B1260413 : Blo 838352 1260413 := bbase (se 3 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 1260413 = 472655) (by norm_num)
theorem B1260437 : Blo 838352 1260437 := bbase (se 6 (by rfl) ⟨29541, by rfl⟩ : syracuseStep 1260437 = 59083) (by norm_num)
theorem B8076181 : Blo 838352 8076181 := bbase (se 6 (by rfl) ⟨189285, by rfl⟩ : syracuseStep 8076181 = 378571) (by norm_num)
theorem B1063849 : Blo 838352 1063849 := bbase (se 2 (by rfl) ⟨398943, by rfl⟩ : syracuseStep 1063849 = 797887) (by norm_num)
theorem B1260461 : Blo 838352 1260461 := bbase (se 3 (by rfl) ⟨236336, by rfl⟩ : syracuseStep 1260461 = 472673) (by norm_num)
theorem B1260485 : Blo 838352 1260485 := bbase (se 4 (by rfl) ⟨118170, by rfl⟩ : syracuseStep 1260485 = 236341) (by norm_num)
theorem B1260509 : Blo 838352 1260509 := bbase (se 3 (by rfl) ⟨236345, by rfl⟩ : syracuseStep 1260509 = 472691) (by norm_num)
theorem B1260533 : Blo 838352 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B1063945 : Blo 838352 1063945 := bbase (se 2 (by rfl) ⟨398979, by rfl⟩ : syracuseStep 1063945 = 797959) (by norm_num)
theorem B1260557 : Blo 838352 1260557 := bbase (se 3 (by rfl) ⟨236354, by rfl⟩ : syracuseStep 1260557 = 472709) (by norm_num)
theorem B1260581 : Blo 838352 1260581 := bbase (se 4 (by rfl) ⟨118179, by rfl⟩ : syracuseStep 1260581 = 236359) (by norm_num)
theorem B3587125 : Blo 838352 3587125 := bbase (se 5 (by rfl) ⟨168146, by rfl⟩ : syracuseStep 3587125 = 336293) (by norm_num)
theorem B1260605 : Blo 838352 1260605 := bbase (se 3 (by rfl) ⟨236363, by rfl⟩ : syracuseStep 1260605 = 472727) (by norm_num)
theorem B1260629 : Blo 838352 1260629 := bbase (se 8 (by rfl) ⟨7386, by rfl⟩ : syracuseStep 1260629 = 14773) (by norm_num)
theorem B1260653 : Blo 838352 1260653 := bbase (se 3 (by rfl) ⟨236372, by rfl⟩ : syracuseStep 1260653 = 472745) (by norm_num)
theorem B2833541 : Blo 838352 2833541 := bbase (se 4 (by rfl) ⟨265644, by rfl⟩ : syracuseStep 2833541 = 531289) (by norm_num)
theorem B1260677 : Blo 838352 1260677 := bbase (se 4 (by rfl) ⟨118188, by rfl⟩ : syracuseStep 1260677 = 236377) (by norm_num)
theorem B1260701 : Blo 838352 1260701 := bbase (se 3 (by rfl) ⟨236381, by rfl⟩ : syracuseStep 1260701 = 472763) (by norm_num)
theorem B1260725 : Blo 838352 1260725 := bbase (se 5 (by rfl) ⟨59096, by rfl⟩ : syracuseStep 1260725 = 118193) (by norm_num)
theorem B1064117 : Blo 838352 1064117 := bbase (se 5 (by rfl) ⟨49880, by rfl⟩ : syracuseStep 1064117 = 99761) (by norm_num)
theorem B1260749 : Blo 838352 1260749 := bbase (se 3 (by rfl) ⟨236390, by rfl⟩ : syracuseStep 1260749 = 472781) (by norm_num)
theorem B1260773 : Blo 838352 1260773 := bbase (se 4 (by rfl) ⟨118197, by rfl⟩ : syracuseStep 1260773 = 236395) (by norm_num)
theorem B1064173 : Blo 838352 1064173 := bbase (se 3 (by rfl) ⟨199532, by rfl⟩ : syracuseStep 1064173 = 399065) (by norm_num)
theorem B1260797 : Blo 838352 1260797 := bbase (se 3 (by rfl) ⟨236399, by rfl⟩ : syracuseStep 1260797 = 472799) (by norm_num)
theorem B1260821 : Blo 838352 1260821 := bbase (se 6 (by rfl) ⟨29550, by rfl⟩ : syracuseStep 1260821 = 59101) (by norm_num)
theorem B1260845 : Blo 838352 1260845 := bbase (se 3 (by rfl) ⟨236408, by rfl⟩ : syracuseStep 1260845 = 472817) (by norm_num)
theorem B1260869 : Blo 838352 1260869 := bbase (se 4 (by rfl) ⟨118206, by rfl⟩ : syracuseStep 1260869 = 236413) (by norm_num)
theorem B1064269 : Blo 838352 1064269 := bbase (se 3 (by rfl) ⟨199550, by rfl⟩ : syracuseStep 1064269 = 399101) (by norm_num)
theorem B1260893 : Blo 838352 1260893 := bbase (se 3 (by rfl) ⟨236417, by rfl⟩ : syracuseStep 1260893 = 472835) (by norm_num)
theorem B1260917 : Blo 838352 1260917 := bbase (se 5 (by rfl) ⟨59105, by rfl⟩ : syracuseStep 1260917 = 118211) (by norm_num)
theorem B1260941 : Blo 838352 1260941 := bbase (se 3 (by rfl) ⟨236426, by rfl⟩ : syracuseStep 1260941 = 472853) (by norm_num)
theorem B1260965 : Blo 838352 1260965 := bbase (se 4 (by rfl) ⟨118215, by rfl⟩ : syracuseStep 1260965 = 236431) (by norm_num)
theorem B1260989 : Blo 838352 1260989 := bbase (se 3 (by rfl) ⟨236435, by rfl⟩ : syracuseStep 1260989 = 472871) (by norm_num)
theorem B1261013 : Blo 838352 1261013 := bbase (se 7 (by rfl) ⟨14777, by rfl⟩ : syracuseStep 1261013 = 29555) (by norm_num)
theorem B1261037 : Blo 838352 1261037 := bbase (se 3 (by rfl) ⟨236444, by rfl⟩ : syracuseStep 1261037 = 472889) (by norm_num)
theorem B1064441 : Blo 838352 1064441 := bbase (se 2 (by rfl) ⟨399165, by rfl⟩ : syracuseStep 1064441 = 798331) (by norm_num)
theorem B1261061 : Blo 838352 1261061 := bbase (se 4 (by rfl) ⟨118224, by rfl⟩ : syracuseStep 1261061 = 236449) (by norm_num)
theorem B1261085 : Blo 838352 1261085 := bbase (se 3 (by rfl) ⟨236453, by rfl⟩ : syracuseStep 1261085 = 472907) (by norm_num)
theorem B1064497 : Blo 838352 1064497 := bbase (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) (by norm_num)
theorem B6372917 : Blo 838352 6372917 := bbase (se 5 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 6372917 = 597461) (by norm_num)
theorem B2833973 : Blo 838352 2833973 := bbase (se 5 (by rfl) ⟨132842, by rfl⟩ : syracuseStep 2833973 = 265685) (by norm_num)
theorem B1261109 : Blo 838352 1261109 := bbase (se 5 (by rfl) ⟨59114, by rfl⟩ : syracuseStep 1261109 = 118229) (by norm_num)
theorem B1818173 : Blo 838352 1818173 := bbase (se 3 (by rfl) ⟨340907, by rfl⟩ : syracuseStep 1818173 = 681815) (by norm_num)
theorem B1261133 : Blo 838352 1261133 := bbase (se 3 (by rfl) ⟨236462, by rfl⟩ : syracuseStep 1261133 = 472925) (by norm_num)
theorem B1261157 : Blo 838352 1261157 := bbase (se 4 (by rfl) ⟨118233, by rfl⟩ : syracuseStep 1261157 = 236467) (by norm_num)
theorem B1261181 : Blo 838352 1261181 := bbase (se 3 (by rfl) ⟨236471, by rfl⟩ : syracuseStep 1261181 = 472943) (by norm_num)
theorem B1064593 : Blo 838352 1064593 := bbase (se 2 (by rfl) ⟨399222, by rfl⟩ : syracuseStep 1064593 = 798445) (by norm_num)
theorem B1261205 : Blo 838352 1261205 := bbase (se 6 (by rfl) ⟨29559, by rfl⟩ : syracuseStep 1261205 = 59119) (by norm_num)
theorem B1261229 : Blo 838352 1261229 := bbase (se 3 (by rfl) ⟨236480, by rfl⟩ : syracuseStep 1261229 = 472961) (by norm_num)
theorem B1261253 : Blo 838352 1261253 := bbase (se 4 (by rfl) ⟨118242, by rfl⟩ : syracuseStep 1261253 = 236485) (by norm_num)
theorem B1261277 : Blo 838352 1261277 := bbase (se 3 (by rfl) ⟨236489, by rfl⟩ : syracuseStep 1261277 = 472979) (by norm_num)
theorem B1261301 : Blo 838352 1261301 := bbase (se 5 (by rfl) ⟨59123, by rfl⟩ : syracuseStep 1261301 = 118247) (by norm_num)
theorem B1261325 : Blo 838352 1261325 := bbase (se 3 (by rfl) ⟨236498, by rfl⟩ : syracuseStep 1261325 = 472997) (by norm_num)
theorem B1261349 : Blo 838352 1261349 := bbase (se 4 (by rfl) ⟨118251, by rfl⟩ : syracuseStep 1261349 = 236503) (by norm_num)
theorem B1261373 : Blo 838352 1261373 := bbase (se 3 (by rfl) ⟨236507, by rfl⟩ : syracuseStep 1261373 = 473015) (by norm_num)
theorem B1064765 : Blo 838352 1064765 := bbase (se 3 (by rfl) ⟨199643, by rfl⟩ : syracuseStep 1064765 = 399287) (by norm_num)
theorem B1261397 : Blo 838352 1261397 := bbase (se 9 (by rfl) ⟨3695, by rfl⟩ : syracuseStep 1261397 = 7391) (by norm_num)
theorem B1261421 : Blo 838352 1261421 := bbase (se 3 (by rfl) ⟨236516, by rfl⟩ : syracuseStep 1261421 = 473033) (by norm_num)
theorem B1064821 : Blo 838352 1064821 := bbase (se 5 (by rfl) ⟨49913, by rfl⟩ : syracuseStep 1064821 = 99827) (by norm_num)
theorem B1261445 : Blo 838352 1261445 := bbase (se 4 (by rfl) ⟨118260, by rfl⟩ : syracuseStep 1261445 = 236521) (by norm_num)
theorem B1261469 : Blo 838352 1261469 := bbase (se 3 (by rfl) ⟨236525, by rfl⟩ : syracuseStep 1261469 = 473051) (by norm_num)
theorem B1261493 : Blo 838352 1261493 := bbase (se 5 (by rfl) ⟨59132, by rfl⟩ : syracuseStep 1261493 = 118265) (by norm_num)
theorem B1458109 : Blo 838352 1458109 := bbase (se 3 (by rfl) ⟨273395, by rfl⟩ : syracuseStep 1458109 = 546791) (by norm_num)
theorem B1261517 : Blo 838352 1261517 := bbase (se 3 (by rfl) ⟨236534, by rfl⟩ : syracuseStep 1261517 = 473069) (by norm_num)
theorem B1064917 : Blo 838352 1064917 := bbase (se 7 (by rfl) ⟨12479, by rfl⟩ : syracuseStep 1064917 = 24959) (by norm_num)
theorem B2834405 : Blo 838352 2834405 := bbase (se 4 (by rfl) ⟨265725, by rfl⟩ : syracuseStep 2834405 = 531451) (by norm_num)
theorem B1261541 : Blo 838352 1261541 := bbase (se 4 (by rfl) ⟨118269, by rfl⟩ : syracuseStep 1261541 = 236539) (by norm_num)
theorem B1261565 : Blo 838352 1261565 := bbase (se 3 (by rfl) ⟨236543, by rfl⟩ : syracuseStep 1261565 = 473087) (by norm_num)
theorem B1261589 : Blo 838352 1261589 := bbase (se 6 (by rfl) ⟨29568, by rfl⟩ : syracuseStep 1261589 = 59137) (by norm_num)
theorem B1261613 : Blo 838352 1261613 := bbase (se 3 (by rfl) ⟨236552, by rfl⟩ : syracuseStep 1261613 = 473105) (by norm_num)
theorem B1261637 : Blo 838352 1261637 := bbase (se 4 (by rfl) ⟨118278, by rfl⟩ : syracuseStep 1261637 = 236557) (by norm_num)
theorem B2015317 : Blo 838352 2015317 := bbase (se 8 (by rfl) ⟨11808, by rfl⟩ : syracuseStep 2015317 = 23617) (by norm_num)
theorem B1261661 : Blo 838352 1261661 := bbase (se 3 (by rfl) ⟨236561, by rfl⟩ : syracuseStep 1261661 = 473123) (by norm_num)
theorem B1261685 : Blo 838352 1261685 := bbase (se 5 (by rfl) ⟨59141, by rfl⟩ : syracuseStep 1261685 = 118283) (by norm_num)
theorem B1065089 : Blo 838352 1065089 := bbase (se 2 (by rfl) ⟨399408, by rfl⟩ : syracuseStep 1065089 = 798817) (by norm_num)
theorem B1261709 : Blo 838352 1261709 := bbase (se 3 (by rfl) ⟨236570, by rfl⟩ : syracuseStep 1261709 = 473141) (by norm_num)
theorem B1261733 : Blo 838352 1261733 := bbase (se 4 (by rfl) ⟨118287, by rfl⟩ : syracuseStep 1261733 = 236575) (by norm_num)
theorem B1917101 : Blo 838352 1917101 := bbase (se 3 (by rfl) ⟨359456, by rfl⟩ : syracuseStep 1917101 = 718913) (by norm_num)
theorem B1065145 : Blo 838352 1065145 := bbase (se 2 (by rfl) ⟨399429, by rfl⟩ : syracuseStep 1065145 = 798859) (by norm_num)
theorem B1196221 : Blo 838352 1196221 := bbase (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) (by norm_num)
theorem B1261757 : Blo 838352 1261757 := bbase (se 3 (by rfl) ⟨236579, by rfl⟩ : syracuseStep 1261757 = 473159) (by norm_num)
theorem B1261781 : Blo 838352 1261781 := bbase (se 7 (by rfl) ⟨14786, by rfl⟩ : syracuseStep 1261781 = 29573) (by norm_num)
theorem B1261805 : Blo 838352 1261805 := bbase (se 3 (by rfl) ⟨236588, by rfl⟩ : syracuseStep 1261805 = 473177) (by norm_num)
theorem B1261829 : Blo 838352 1261829 := bbase (se 4 (by rfl) ⟨118296, by rfl⟩ : syracuseStep 1261829 = 236593) (by norm_num)
theorem B2015509 : Blo 838352 2015509 := bbase (se 6 (by rfl) ⟨47238, by rfl⟩ : syracuseStep 2015509 = 94477) (by norm_num)
theorem B1065241 : Blo 838352 1065241 := bbase (se 2 (by rfl) ⟨399465, by rfl⟩ : syracuseStep 1065241 = 798931) (by norm_num)
theorem B1261853 : Blo 838352 1261853 := bbase (se 3 (by rfl) ⟨236597, by rfl⟩ : syracuseStep 1261853 = 473195) (by norm_num)
theorem B1261877 : Blo 838352 1261877 := bbase (se 5 (by rfl) ⟨59150, by rfl⟩ : syracuseStep 1261877 = 118301) (by norm_num)
theorem B2015549 : Blo 838352 2015549 := bbase (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) (by norm_num)
theorem B1261901 : Blo 838352 1261901 := bbase (se 3 (by rfl) ⟨236606, by rfl⟩ : syracuseStep 1261901 = 473213) (by norm_num)
theorem B1261925 : Blo 838352 1261925 := bbase (se 4 (by rfl) ⟨118305, by rfl⟩ : syracuseStep 1261925 = 236611) (by norm_num)
theorem B1261949 : Blo 838352 1261949 := bbase (se 3 (by rfl) ⟨236615, by rfl⟩ : syracuseStep 1261949 = 473231) (by norm_num)
theorem B2834837 : Blo 838352 2834837 := bbase (se 6 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 2834837 = 132883) (by norm_num)
theorem B1261973 : Blo 838352 1261973 := bbase (se 6 (by rfl) ⟨29577, by rfl⟩ : syracuseStep 1261973 = 59155) (by norm_num)
theorem B1261997 : Blo 838352 1261997 := bbase (se 3 (by rfl) ⟨236624, by rfl⟩ : syracuseStep 1261997 = 473249) (by norm_num)
theorem B1262021 : Blo 838352 1262021 := bbase (se 4 (by rfl) ⟨118314, by rfl⟩ : syracuseStep 1262021 = 236629) (by norm_num)
theorem B1065413 : Blo 838352 1065413 := bbase (se 4 (by rfl) ⟨99882, by rfl⟩ : syracuseStep 1065413 = 199765) (by norm_num)
theorem B1262045 : Blo 838352 1262045 := bbase (se 3 (by rfl) ⟨236633, by rfl⟩ : syracuseStep 1262045 = 473267) (by norm_num)
theorem B1262069 : Blo 838352 1262069 := bbase (se 5 (by rfl) ⟨59159, by rfl⟩ : syracuseStep 1262069 = 118319) (by norm_num)
theorem B1065469 : Blo 838352 1065469 := bbase (se 3 (by rfl) ⟨199775, by rfl⟩ : syracuseStep 1065469 = 399551) (by norm_num)
theorem B1262093 : Blo 838352 1262093 := bbase (se 3 (by rfl) ⟨236642, by rfl⟩ : syracuseStep 1262093 = 473285) (by norm_num)
theorem B1262117 : Blo 838352 1262117 := bbase (se 4 (by rfl) ⟨118323, by rfl⟩ : syracuseStep 1262117 = 236647) (by norm_num)
theorem B1262141 : Blo 838352 1262141 := bbase (se 3 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 1262141 = 473303) (by norm_num)
theorem B1262165 : Blo 838352 1262165 := bbase (se 8 (by rfl) ⟨7395, by rfl⟩ : syracuseStep 1262165 = 14791) (by norm_num)
theorem B2015837 : Blo 838352 2015837 := bbase (se 3 (by rfl) ⟨377969, by rfl⟩ : syracuseStep 2015837 = 755939) (by norm_num)
theorem B1065565 : Blo 838352 1065565 := bbase (se 3 (by rfl) ⟨199793, by rfl⟩ : syracuseStep 1065565 = 399587) (by norm_num)
theorem B1262189 : Blo 838352 1262189 := bbase (se 3 (by rfl) ⟨236660, by rfl⟩ : syracuseStep 1262189 = 473321) (by norm_num)
theorem B1262213 : Blo 838352 1262213 := bbase (se 4 (by rfl) ⟨118332, by rfl⟩ : syracuseStep 1262213 = 236665) (by norm_num)
theorem B1262237 : Blo 838352 1262237 := bbase (se 3 (by rfl) ⟨236669, by rfl⟩ : syracuseStep 1262237 = 473339) (by norm_num)
theorem B3195557 : Blo 838352 3195557 := bbase (se 4 (by rfl) ⟨299583, by rfl⟩ : syracuseStep 3195557 = 599167) (by norm_num)
theorem B1262261 : Blo 838352 1262261 := bbase (se 5 (by rfl) ⟨59168, by rfl⟩ : syracuseStep 1262261 = 118337) (by norm_num)
theorem B1262285 : Blo 838352 1262285 := bbase (se 3 (by rfl) ⟨236678, by rfl⟩ : syracuseStep 1262285 = 473357) (by norm_num)
theorem B1262309 : Blo 838352 1262309 := bbase (se 4 (by rfl) ⟨118341, by rfl⟩ : syracuseStep 1262309 = 236683) (by norm_num)
theorem B1262333 : Blo 838352 1262333 := bbase (se 3 (by rfl) ⟨236687, by rfl⟩ : syracuseStep 1262333 = 473375) (by norm_num)
theorem B1065737 : Blo 838352 1065737 := bbase (se 2 (by rfl) ⟨399651, by rfl⟩ : syracuseStep 1065737 = 799303) (by norm_num)
theorem B1196813 : Blo 838352 1196813 := bbase (se 3 (by rfl) ⟨224402, by rfl⟩ : syracuseStep 1196813 = 448805) (by norm_num)
theorem B1262357 : Blo 838352 1262357 := bbase (se 6 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 1262357 = 59173) (by norm_num)
theorem B1262381 : Blo 838352 1262381 := bbase (se 3 (by rfl) ⟨236696, by rfl⟩ : syracuseStep 1262381 = 473393) (by norm_num)
theorem B1065793 : Blo 838352 1065793 := bbase (se 2 (by rfl) ⟨399672, by rfl⟩ : syracuseStep 1065793 = 799345) (by norm_num)
theorem B2835269 : Blo 838352 2835269 := bbase (se 4 (by rfl) ⟨265806, by rfl⟩ : syracuseStep 2835269 = 531613) (by norm_num)
theorem B1262405 : Blo 838352 1262405 := bbase (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) (by norm_num)
theorem B1196893 : Blo 838352 1196893 := bbase (se 3 (by rfl) ⟨224417, by rfl⟩ : syracuseStep 1196893 = 448835) (by norm_num)
theorem B1262429 : Blo 838352 1262429 := bbase (se 3 (by rfl) ⟨236705, by rfl⟩ : syracuseStep 1262429 = 473411) (by norm_num)
theorem B1262453 : Blo 838352 1262453 := bbase (se 5 (by rfl) ⟨59177, by rfl⟩ : syracuseStep 1262453 = 118355) (by norm_num)
theorem B1262477 : Blo 838352 1262477 := bbase (se 3 (by rfl) ⟨236714, by rfl⟩ : syracuseStep 1262477 = 473429) (by norm_num)
theorem B1065889 : Blo 838352 1065889 := bbase (se 2 (by rfl) ⟨399708, by rfl⟩ : syracuseStep 1065889 = 799417) (by norm_num)
theorem B1262501 : Blo 838352 1262501 := bbase (se 4 (by rfl) ⟨118359, by rfl⟩ : syracuseStep 1262501 = 236719) (by norm_num)
theorem B1262525 : Blo 838352 1262525 := bbase (se 3 (by rfl) ⟨236723, by rfl⟩ : syracuseStep 1262525 = 473447) (by norm_num)
theorem B3195845 : Blo 838352 3195845 := bbase (se 4 (by rfl) ⟨299610, by rfl⟩ : syracuseStep 3195845 = 599221) (by norm_num)
theorem B1197013 : Blo 838352 1197013 := bbase (se 7 (by rfl) ⟨14027, by rfl⟩ : syracuseStep 1197013 = 28055) (by norm_num)
theorem B1262549 : Blo 838352 1262549 := bbase (se 7 (by rfl) ⟨14795, by rfl⟩ : syracuseStep 1262549 = 29591) (by norm_num)
theorem B1262573 : Blo 838352 1262573 := bbase (se 3 (by rfl) ⟨236732, by rfl⟩ : syracuseStep 1262573 = 473465) (by norm_num)
theorem B1262597 : Blo 838352 1262597 := bbase (se 4 (by rfl) ⟨118368, by rfl⟩ : syracuseStep 1262597 = 236737) (by norm_num)
theorem B1262621 : Blo 838352 1262621 := bbase (se 3 (by rfl) ⟨236741, by rfl⟩ : syracuseStep 1262621 = 473483) (by norm_num)
theorem B1197109 : Blo 838352 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B1262645 : Blo 838352 1262645 := bbase (se 5 (by rfl) ⟨59186, by rfl⟩ : syracuseStep 1262645 = 118373) (by norm_num)
theorem B1262669 : Blo 838352 1262669 := bbase (se 3 (by rfl) ⟨236750, by rfl⟩ : syracuseStep 1262669 = 473501) (by norm_num)
theorem B1066061 : Blo 838352 1066061 := bbase (se 3 (by rfl) ⟨199886, by rfl⟩ : syracuseStep 1066061 = 399773) (by norm_num)
theorem B1262693 : Blo 838352 1262693 := bbase (se 4 (by rfl) ⟨118377, by rfl⟩ : syracuseStep 1262693 = 236755) (by norm_num)
theorem B1262717 : Blo 838352 1262717 := bbase (se 3 (by rfl) ⟨236759, by rfl⟩ : syracuseStep 1262717 = 473519) (by norm_num)
theorem B1262741 : Blo 838352 1262741 := bbase (se 6 (by rfl) ⟨29595, by rfl⟩ : syracuseStep 1262741 = 59191) (by norm_num)
theorem B1262765 : Blo 838352 1262765 := bbase (se 3 (by rfl) ⟨236768, by rfl⟩ : syracuseStep 1262765 = 473537) (by norm_num)
theorem B1262789 : Blo 838352 1262789 := bbase (se 4 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 1262789 = 236773) (by norm_num)
theorem B1262813 : Blo 838352 1262813 := bbase (se 3 (by rfl) ⟨236777, by rfl⟩ : syracuseStep 1262813 = 473555) (by norm_num)
theorem B2835701 : Blo 838352 2835701 := bbase (se 5 (by rfl) ⟨132923, by rfl⟩ : syracuseStep 2835701 = 265847) (by norm_num)
theorem B1262837 : Blo 838352 1262837 := bbase (se 5 (by rfl) ⟨59195, by rfl⟩ : syracuseStep 1262837 = 118391) (by norm_num)
theorem B1262861 : Blo 838352 1262861 := bbase (se 3 (by rfl) ⟨236786, by rfl⟩ : syracuseStep 1262861 = 473573) (by norm_num)
theorem B1262885 : Blo 838352 1262885 := bbase (se 4 (by rfl) ⟨118395, by rfl⟩ : syracuseStep 1262885 = 236791) (by norm_num)
theorem B1262909 : Blo 838352 1262909 := bbase (se 3 (by rfl) ⟨236795, by rfl⟩ : syracuseStep 1262909 = 473591) (by norm_num)
theorem B1262933 : Blo 838352 1262933 := bbase (se 12 (by rfl) ⟨462, by rfl⟩ : syracuseStep 1262933 = 925) (by norm_num)
theorem B1262957 : Blo 838352 1262957 := bbase (se 3 (by rfl) ⟨236804, by rfl⟩ : syracuseStep 1262957 = 473609) (by norm_num)
theorem B1262981 : Blo 838352 1262981 := bbase (se 4 (by rfl) ⟨118404, by rfl⟩ : syracuseStep 1262981 = 236809) (by norm_num)
theorem B4244885 : Blo 838352 4244885 := bbase (se 6 (by rfl) ⟨99489, by rfl⟩ : syracuseStep 4244885 = 198979) (by norm_num)
theorem B1263005 : Blo 838352 1263005 := bbase (se 3 (by rfl) ⟨236813, by rfl⟩ : syracuseStep 1263005 = 473627) (by norm_num)
theorem B1263029 : Blo 838352 1263029 := bbase (se 5 (by rfl) ⟨59204, by rfl⟩ : syracuseStep 1263029 = 118409) (by norm_num)
theorem B1263053 : Blo 838352 1263053 := bbase (se 3 (by rfl) ⟨236822, by rfl⟩ : syracuseStep 1263053 = 473645) (by norm_num)
theorem B10765781 : Blo 838352 10765781 := bbase (se 7 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 10765781 = 252323) (by norm_num)
theorem B3032549 : Blo 838352 3032549 := bbase (se 4 (by rfl) ⟨284301, by rfl⟩ : syracuseStep 3032549 = 568603) (by norm_num)
theorem B1263077 : Blo 838352 1263077 := bbase (se 4 (by rfl) ⟨118413, by rfl⟩ : syracuseStep 1263077 = 236827) (by norm_num)
theorem B1263101 : Blo 838352 1263101 := bbase (se 3 (by rfl) ⟨236831, by rfl⟩ : syracuseStep 1263101 = 473663) (by norm_num)
theorem B1263125 : Blo 838352 1263125 := bbase (se 6 (by rfl) ⟨29604, by rfl⟩ : syracuseStep 1263125 = 59209) (by norm_num)
theorem B1197605 : Blo 838352 1197605 := bbase (se 4 (by rfl) ⟨112275, by rfl⟩ : syracuseStep 1197605 = 224551) (by norm_num)
theorem B1263149 : Blo 838352 1263149 := bbase (se 3 (by rfl) ⟨236840, by rfl⟩ : syracuseStep 1263149 = 473681) (by norm_num)
theorem B1263173 : Blo 838352 1263173 := bbase (se 4 (by rfl) ⟨118422, by rfl⟩ : syracuseStep 1263173 = 236845) (by norm_num)
theorem B1263197 : Blo 838352 1263197 := bbase (se 3 (by rfl) ⟨236849, by rfl⟩ : syracuseStep 1263197 = 473699) (by norm_num)
theorem B1263221 : Blo 838352 1263221 := bbase (se 5 (by rfl) ⟨59213, by rfl⟩ : syracuseStep 1263221 = 118427) (by norm_num)
theorem B1263245 : Blo 838352 1263245 := bbase (se 3 (by rfl) ⟨236858, by rfl⟩ : syracuseStep 1263245 = 473717) (by norm_num)
theorem B2836133 : Blo 838352 2836133 := bbase (se 4 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 2836133 = 531775) (by norm_num)
theorem B1263269 : Blo 838352 1263269 := bbase (se 4 (by rfl) ⟨118431, by rfl⟩ : syracuseStep 1263269 = 236863) (by norm_num)
theorem B1263293 : Blo 838352 1263293 := bbase (se 3 (by rfl) ⟨236867, by rfl⟩ : syracuseStep 1263293 = 473735) (by norm_num)
theorem B1263317 : Blo 838352 1263317 := bbase (se 7 (by rfl) ⟨14804, by rfl⟩ : syracuseStep 1263317 = 29609) (by norm_num)
theorem B1263341 : Blo 838352 1263341 := bbase (se 3 (by rfl) ⟨236876, by rfl⟩ : syracuseStep 1263341 = 473753) (by norm_num)
theorem B1263365 : Blo 838352 1263365 := bbase (se 4 (by rfl) ⟨118440, by rfl⟩ : syracuseStep 1263365 = 236881) (by norm_num)
theorem B1263389 : Blo 838352 1263389 := bbase (se 3 (by rfl) ⟨236885, by rfl⟩ : syracuseStep 1263389 = 473771) (by norm_num)
theorem B1263413 : Blo 838352 1263413 := bbase (se 5 (by rfl) ⟨59222, by rfl⟩ : syracuseStep 1263413 = 118445) (by norm_num)
theorem B1263437 : Blo 838352 1263437 := bbase (se 3 (by rfl) ⟨236894, by rfl⟩ : syracuseStep 1263437 = 473789) (by norm_num)
theorem B1263461 : Blo 838352 1263461 := bbase (se 4 (by rfl) ⟨118449, by rfl⟩ : syracuseStep 1263461 = 236899) (by norm_num)
theorem B1263485 : Blo 838352 1263485 := bbase (se 3 (by rfl) ⟨236903, by rfl⟩ : syracuseStep 1263485 = 473807) (by norm_num)
theorem B1918853 : Blo 838352 1918853 := bbase (se 4 (by rfl) ⟨179892, by rfl⟩ : syracuseStep 1918853 = 359785) (by norm_num)
theorem B1263509 : Blo 838352 1263509 := bbase (se 6 (by rfl) ⟨29613, by rfl⟩ : syracuseStep 1263509 = 59227) (by norm_num)
theorem B1918925 : Blo 838352 1918925 := bbase (se 3 (by rfl) ⟨359798, by rfl⟩ : syracuseStep 1918925 = 719597) (by norm_num)
theorem B1558493 : Blo 838352 1558493 := bbase (se 3 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 1558493 = 584435) (by norm_num)
theorem B1198157 : Blo 838352 1198157 := bbase (se 3 (by rfl) ⟨224654, by rfl⟩ : syracuseStep 1198157 = 449309) (by norm_num)
theorem B2836565 : Blo 838352 2836565 := bbase (se 8 (by rfl) ⟨16620, by rfl⟩ : syracuseStep 2836565 = 33241) (by norm_num)
theorem B7784533 : Blo 838352 7784533 := bbase (se 8 (by rfl) ⟨45612, by rfl⟩ : syracuseStep 7784533 = 91225) (by norm_num)
theorem B1886309 : Blo 838352 1886309 := bbase (se 4 (by rfl) ⟨176841, by rfl⟩ : syracuseStep 1886309 = 353683) (by norm_num)
theorem B3197029 : Blo 838352 3197029 := bbase (se 4 (by rfl) ⟨299721, by rfl⟩ : syracuseStep 3197029 = 599443) (by norm_num)
theorem B1886381 : Blo 838352 1886381 := bbase (se 3 (by rfl) ⟨353696, by rfl⟩ : syracuseStep 1886381 = 707393) (by norm_num)
theorem B1886453 : Blo 838352 1886453 := bbase (se 5 (by rfl) ⟨88427, by rfl⟩ : syracuseStep 1886453 = 176855) (by norm_num)
theorem B1591589 : Blo 838352 1591589 := bbase (se 4 (by rfl) ⟨149211, by rfl⟩ : syracuseStep 1591589 = 298423) (by norm_num)
theorem B1886525 : Blo 838352 1886525 := bbase (se 3 (by rfl) ⟨353723, by rfl⟩ : syracuseStep 1886525 = 707447) (by norm_num)
theorem B3033413 : Blo 838352 3033413 := bbase (se 4 (by rfl) ⟨284382, by rfl⟩ : syracuseStep 3033413 = 568765) (by norm_num)
theorem B1886597 : Blo 838352 1886597 := bbase (se 4 (by rfl) ⟨176868, by rfl⟩ : syracuseStep 1886597 = 353737) (by norm_num)
theorem B1919381 : Blo 838352 1919381 := bbase (se 6 (by rfl) ⟨44985, by rfl⟩ : syracuseStep 1919381 = 89971) (by norm_num)
theorem B3197333 : Blo 838352 3197333 := bbase (se 6 (by rfl) ⟨74937, by rfl⟩ : syracuseStep 3197333 = 149875) (by norm_num)
theorem B1591741 : Blo 838352 1591741 := bbase (se 3 (by rfl) ⟨298451, by rfl⟩ : syracuseStep 1591741 = 596903) (by norm_num)
theorem B1886669 : Blo 838352 1886669 := bbase (se 3 (by rfl) ⟨353750, by rfl⟩ : syracuseStep 1886669 = 707501) (by norm_num)
theorem B2836997 : Blo 838352 2836997 := bbase (se 4 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 2836997 = 531937) (by norm_num)
theorem B1886741 : Blo 838352 1886741 := bbase (se 6 (by rfl) ⟨44220, by rfl⟩ : syracuseStep 1886741 = 88441) (by norm_num)
theorem B1886813 : Blo 838352 1886813 := bbase (se 3 (by rfl) ⟨353777, by rfl⟩ : syracuseStep 1886813 = 707555) (by norm_num)
theorem B1886885 : Blo 838352 1886885 := bbase (se 4 (by rfl) ⟨176895, by rfl⟩ : syracuseStep 1886885 = 353791) (by norm_num)
theorem B4246181 : Blo 838352 4246181 := bbase (se 4 (by rfl) ⟨398079, by rfl⟩ : syracuseStep 4246181 = 796159) (by norm_num)
theorem B1592045 : Blo 838352 1592045 := bbase (se 3 (by rfl) ⟨298508, by rfl⟩ : syracuseStep 1592045 = 597017) (by norm_num)
theorem B1886957 : Blo 838352 1886957 := bbase (se 3 (by rfl) ⟨353804, by rfl⟩ : syracuseStep 1886957 = 707609) (by norm_num)
theorem B1887029 : Blo 838352 1887029 := bbase (se 5 (by rfl) ⟨88454, by rfl⟩ : syracuseStep 1887029 = 176909) (by norm_num)
theorem B8080181 : Blo 838352 8080181 := bbase (se 5 (by rfl) ⟨378758, by rfl⟩ : syracuseStep 8080181 = 757517) (by norm_num)
theorem B1198909 : Blo 838352 1198909 := bbase (se 3 (by rfl) ⟨224795, by rfl⟩ : syracuseStep 1198909 = 449591) (by norm_num)
theorem B1887101 : Blo 838352 1887101 := bbase (se 3 (by rfl) ⟨353831, by rfl⟩ : syracuseStep 1887101 = 707663) (by norm_num)
theorem B2837429 : Blo 838352 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B1887173 : Blo 838352 1887173 := bbase (se 4 (by rfl) ⟨176922, by rfl⟩ : syracuseStep 1887173 = 353845) (by norm_num)
theorem B1887245 : Blo 838352 1887245 := bbase (se 3 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 1887245 = 707717) (by norm_num)
theorem B1887317 : Blo 838352 1887317 := bbase (se 8 (by rfl) ⟨11058, by rfl⟩ : syracuseStep 1887317 = 22117) (by norm_num)
theorem B1887389 : Blo 838352 1887389 := bbase (se 3 (by rfl) ⟨353885, by rfl⟩ : syracuseStep 1887389 = 707771) (by norm_num)
theorem B1887461 : Blo 838352 1887461 := bbase (se 4 (by rfl) ⟨176949, by rfl⟩ : syracuseStep 1887461 = 353899) (by norm_num)
theorem B1887533 : Blo 838352 1887533 := bbase (se 3 (by rfl) ⟨353912, by rfl⟩ : syracuseStep 1887533 = 707825) (by norm_num)
theorem B2837861 : Blo 838352 2837861 := bbase (se 4 (by rfl) ⟨266049, by rfl⟩ : syracuseStep 2837861 = 532099) (by norm_num)
theorem B1887605 : Blo 838352 1887605 := bbase (se 5 (by rfl) ⟨88481, by rfl⟩ : syracuseStep 1887605 = 176963) (by norm_num)
theorem B1887677 : Blo 838352 1887677 := bbase (se 3 (by rfl) ⟨353939, by rfl⟩ : syracuseStep 1887677 = 707879) (by norm_num)
theorem B24202709 : Blo 838352 24202709 := bbase (se 7 (by rfl) ⟨283625, by rfl⟩ : syracuseStep 24202709 = 567251) (by norm_num)
theorem B1592797 : Blo 838352 1592797 := bbase (se 3 (by rfl) ⟨298649, by rfl⟩ : syracuseStep 1592797 = 597299) (by norm_num)
theorem B1887749 : Blo 838352 1887749 := bbase (se 4 (by rfl) ⟨176976, by rfl⟩ : syracuseStep 1887749 = 353953) (by norm_num)
theorem B1887821 : Blo 838352 1887821 := bbase (se 3 (by rfl) ⟨353966, by rfl⟩ : syracuseStep 1887821 = 707933) (by norm_num)
theorem B1592941 : Blo 838352 1592941 := bbase (se 3 (by rfl) ⟨298676, by rfl⟩ : syracuseStep 1592941 = 597353) (by norm_num)
theorem B1887893 : Blo 838352 1887893 := bbase (se 6 (by rfl) ⟨44247, by rfl⟩ : syracuseStep 1887893 = 88495) (by norm_num)
theorem B1887965 : Blo 838352 1887965 := bbase (se 3 (by rfl) ⟨353993, by rfl⟩ : syracuseStep 1887965 = 707987) (by norm_num)
theorem B1593101 : Blo 838352 1593101 := bbase (se 3 (by rfl) ⟨298706, by rfl⟩ : syracuseStep 1593101 = 597413) (by norm_num)
theorem B2838293 : Blo 838352 2838293 := bbase (se 6 (by rfl) ⟨66522, by rfl⟩ : syracuseStep 2838293 = 133045) (by norm_num)
theorem B1888037 : Blo 838352 1888037 := bbase (se 4 (by rfl) ⟨177003, by rfl⟩ : syracuseStep 1888037 = 354007) (by norm_num)
theorem B1134373 : Blo 838352 1134373 := bbase (se 4 (by rfl) ⟨106347, by rfl⟩ : syracuseStep 1134373 = 212695) (by norm_num)
theorem B1888109 : Blo 838352 1888109 := bbase (se 3 (by rfl) ⟨354020, by rfl⟩ : syracuseStep 1888109 = 708041) (by norm_num)
theorem B1593245 : Blo 838352 1593245 := bbase (se 3 (by rfl) ⟨298733, by rfl⟩ : syracuseStep 1593245 = 597467) (by norm_num)
theorem B4247477 : Blo 838352 4247477 := bbase (se 5 (by rfl) ⟨199100, by rfl⟩ : syracuseStep 4247477 = 398201) (by norm_num)
theorem B1888181 : Blo 838352 1888181 := bbase (se 5 (by rfl) ⟨88508, by rfl⟩ : syracuseStep 1888181 = 177017) (by norm_num)
theorem B3592133 : Blo 838352 3592133 := bbase (se 4 (by rfl) ⟨336762, by rfl⟩ : syracuseStep 3592133 = 673525) (by norm_num)
theorem B1888253 : Blo 838352 1888253 := bbase (se 3 (by rfl) ⟨354047, by rfl⟩ : syracuseStep 1888253 = 708095) (by norm_num)
theorem B1888325 : Blo 838352 1888325 := bbase (se 4 (by rfl) ⟨177030, by rfl⟩ : syracuseStep 1888325 = 354061) (by norm_num)
theorem B2019421 : Blo 838352 2019421 := bbase (se 3 (by rfl) ⟨378641, by rfl⟩ : syracuseStep 2019421 = 757283) (by norm_num)
theorem B2871413 : Blo 838352 2871413 := bbase (se 5 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 2871413 = 269195) (by norm_num)
theorem B1888397 : Blo 838352 1888397 := bbase (se 3 (by rfl) ⟨354074, by rfl⟩ : syracuseStep 1888397 = 708149) (by norm_num)
theorem B1593533 : Blo 838352 1593533 := bbase (se 3 (by rfl) ⟨298787, by rfl⟩ : syracuseStep 1593533 = 597575) (by norm_num)
theorem B2838725 : Blo 838352 2838725 := bbase (se 4 (by rfl) ⟨266130, by rfl⟩ : syracuseStep 2838725 = 532261) (by norm_num)
theorem B1888469 : Blo 838352 1888469 := bbase (se 7 (by rfl) ⟨22130, by rfl⟩ : syracuseStep 1888469 = 44261) (by norm_num)
theorem B3592421 : Blo 838352 3592421 := bbase (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) (by norm_num)
theorem B1888541 : Blo 838352 1888541 := bbase (se 3 (by rfl) ⟨354101, by rfl⟩ : syracuseStep 1888541 = 708203) (by norm_num)
theorem B1593685 : Blo 838352 1593685 := bbase (se 10 (by rfl) ⟨2334, by rfl⟩ : syracuseStep 1593685 = 4669) (by norm_num)
theorem B1888613 : Blo 838352 1888613 := bbase (se 4 (by rfl) ⟨177057, by rfl⟩ : syracuseStep 1888613 = 354115) (by norm_num)
theorem B1888685 : Blo 838352 1888685 := bbase (se 3 (by rfl) ⟨354128, by rfl⟩ : syracuseStep 1888685 = 708257) (by norm_num)
theorem B1888757 : Blo 838352 1888757 := bbase (se 5 (by rfl) ⟨88535, by rfl⟩ : syracuseStep 1888757 = 177071) (by norm_num)
theorem B1888829 : Blo 838352 1888829 := bbase (se 3 (by rfl) ⟨354155, by rfl⟩ : syracuseStep 1888829 = 708311) (by norm_num)
theorem B2839157 : Blo 838352 2839157 := bbase (se 5 (by rfl) ⟨133085, by rfl⟩ : syracuseStep 2839157 = 266171) (by norm_num)
theorem B1888901 : Blo 838352 1888901 := bbase (se 4 (by rfl) ⟨177084, by rfl⟩ : syracuseStep 1888901 = 354169) (by norm_num)
theorem B1593989 : Blo 838352 1593989 := bbase (se 4 (by rfl) ⟨149436, by rfl⟩ : syracuseStep 1593989 = 298873) (by norm_num)
theorem B1888973 : Blo 838352 1888973 := bbase (se 3 (by rfl) ⟨354182, by rfl⟩ : syracuseStep 1888973 = 708365) (by norm_num)
theorem B2020085 : Blo 838352 2020085 := bbase (se 5 (by rfl) ⟨94691, by rfl⟩ : syracuseStep 2020085 = 189383) (by norm_num)
theorem B3035893 : Blo 838352 3035893 := bbase (se 5 (by rfl) ⟨142307, by rfl⟩ : syracuseStep 3035893 = 284615) (by norm_num)
theorem B1889045 : Blo 838352 1889045 := bbase (se 6 (by rfl) ⟨44274, by rfl⟩ : syracuseStep 1889045 = 88549) (by norm_num)
theorem B1889117 : Blo 838352 1889117 := bbase (se 3 (by rfl) ⟨354209, by rfl⟩ : syracuseStep 1889117 = 708419) (by norm_num)
theorem B1889189 : Blo 838352 1889189 := bbase (se 4 (by rfl) ⟨177111, by rfl⟩ : syracuseStep 1889189 = 354223) (by norm_num)
theorem B3593173 : Blo 838352 3593173 := bbase (se 7 (by rfl) ⟨42107, by rfl⟩ : syracuseStep 3593173 = 84215) (by norm_num)
theorem B1889261 : Blo 838352 1889261 := bbase (se 3 (by rfl) ⟨354236, by rfl⟩ : syracuseStep 1889261 = 708473) (by norm_num)
theorem B2020373 : Blo 838352 2020373 := bbase (se 6 (by rfl) ⟨47352, by rfl⟩ : syracuseStep 2020373 = 94705) (by norm_num)
theorem B2839589 : Blo 838352 2839589 := bbase (se 4 (by rfl) ⟨266211, by rfl⟩ : syracuseStep 2839589 = 532423) (by norm_num)
theorem B1889333 : Blo 838352 1889333 := bbase (se 5 (by rfl) ⟨88562, by rfl⟩ : syracuseStep 1889333 = 177125) (by norm_num)
theorem B1791085 : Blo 838352 1791085 := bbase (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) (by norm_num)
theorem B1889405 : Blo 838352 1889405 := bbase (se 3 (by rfl) ⟨354263, by rfl⟩ : syracuseStep 1889405 = 708527) (by norm_num)
theorem B4248773 : Blo 838352 4248773 := bbase (se 4 (by rfl) ⟨398322, by rfl⟩ : syracuseStep 4248773 = 796645) (by norm_num)
theorem B1889477 : Blo 838352 1889477 := bbase (se 4 (by rfl) ⟨177138, by rfl⟩ : syracuseStep 1889477 = 354277) (by norm_num)
theorem B1889549 : Blo 838352 1889549 := bbase (se 3 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 1889549 = 708581) (by norm_num)
theorem B1889621 : Blo 838352 1889621 := bbase (se 15 (by rfl) ⟨86, by rfl⟩ : syracuseStep 1889621 = 173) (by norm_num)
theorem B1594741 : Blo 838352 1594741 := bbase (se 5 (by rfl) ⟨74753, by rfl⟩ : syracuseStep 1594741 = 149507) (by norm_num)
theorem B1889693 : Blo 838352 1889693 := bbase (se 3 (by rfl) ⟨354317, by rfl⟩ : syracuseStep 1889693 = 708635) (by norm_num)
theorem B2840021 : Blo 838352 2840021 := bbase (se 7 (by rfl) ⟨33281, by rfl⟩ : syracuseStep 2840021 = 66563) (by norm_num)
theorem B1889765 : Blo 838352 1889765 := bbase (se 4 (by rfl) ⟨177165, by rfl⟩ : syracuseStep 1889765 = 354331) (by norm_num)
theorem B1594885 : Blo 838352 1594885 := bbase (se 4 (by rfl) ⟨149520, by rfl⟩ : syracuseStep 1594885 = 299041) (by norm_num)
theorem B1889837 : Blo 838352 1889837 := bbase (se 3 (by rfl) ⟨354344, by rfl⟩ : syracuseStep 1889837 = 708689) (by norm_num)
theorem B1889909 : Blo 838352 1889909 := bbase (se 5 (by rfl) ⟨88589, by rfl⟩ : syracuseStep 1889909 = 177179) (by norm_num)
theorem B1595045 : Blo 838352 1595045 := bbase (se 4 (by rfl) ⟨149535, by rfl⟩ : syracuseStep 1595045 = 299071) (by norm_num)
theorem B3593909 : Blo 838352 3593909 := bbase (se 5 (by rfl) ⟨168464, by rfl⟩ : syracuseStep 3593909 = 336929) (by norm_num)
theorem B1889981 : Blo 838352 1889981 := bbase (se 3 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 1889981 = 708743) (by norm_num)
theorem B1169093 : Blo 838352 1169093 := bbase (se 4 (by rfl) ⟨109602, by rfl⟩ : syracuseStep 1169093 = 219205) (by norm_num)
theorem B1890053 : Blo 838352 1890053 := bbase (se 4 (by rfl) ⟨177192, by rfl⟩ : syracuseStep 1890053 = 354385) (by norm_num)
theorem B2152213 : Blo 838352 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B1595189 : Blo 838352 1595189 := bbase (se 5 (by rfl) ⟨74774, by rfl⟩ : syracuseStep 1595189 = 149549) (by norm_num)
theorem B1890125 : Blo 838352 1890125 := bbase (se 3 (by rfl) ⟨354398, by rfl⟩ : syracuseStep 1890125 = 708797) (by norm_num)
theorem B2840453 : Blo 838352 2840453 := bbase (se 4 (by rfl) ⟨266292, by rfl⟩ : syracuseStep 2840453 = 532585) (by norm_num)
theorem B1890197 : Blo 838352 1890197 := bbase (se 6 (by rfl) ⟨44301, by rfl⟩ : syracuseStep 1890197 = 88603) (by norm_num)
theorem B1890269 : Blo 838352 1890269 := bbase (se 3 (by rfl) ⟨354425, by rfl⟩ : syracuseStep 1890269 = 708851) (by norm_num)
theorem B1791973 : Blo 838352 1791973 := bbase (se 4 (by rfl) ⟨167997, by rfl⟩ : syracuseStep 1791973 = 335995) (by norm_num)
theorem B1366021 : Blo 838352 1366021 := bbase (se 4 (by rfl) ⟨128064, by rfl⟩ : syracuseStep 1366021 = 256129) (by norm_num)
theorem B2152469 : Blo 838352 2152469 := bbase (se 6 (by rfl) ⟨50448, by rfl⟩ : syracuseStep 2152469 = 100897) (by norm_num)
theorem B1890341 : Blo 838352 1890341 := bbase (se 4 (by rfl) ⟨177219, by rfl⟩ : syracuseStep 1890341 = 354439) (by norm_num)
theorem B1595477 : Blo 838352 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B1890413 : Blo 838352 1890413 := bbase (se 3 (by rfl) ⟨354452, by rfl⟩ : syracuseStep 1890413 = 708905) (by norm_num)
theorem B1890485 : Blo 838352 1890485 := bbase (se 5 (by rfl) ⟨88616, by rfl⟩ : syracuseStep 1890485 = 177233) (by norm_num)
theorem B907493 : Blo 838352 907493 := bbase (se 4 (by rfl) ⟨85077, by rfl⟩ : syracuseStep 907493 = 170155) (by norm_num)
theorem B1595629 : Blo 838352 1595629 := bbase (se 3 (by rfl) ⟨299180, by rfl⟩ : syracuseStep 1595629 = 598361) (by norm_num)
theorem B1890557 : Blo 838352 1890557 := bbase (se 3 (by rfl) ⟨354479, by rfl⟩ : syracuseStep 1890557 = 708959) (by norm_num)
theorem B2840885 : Blo 838352 2840885 := bbase (se 5 (by rfl) ⟨133166, by rfl⟩ : syracuseStep 2840885 = 266333) (by norm_num)
theorem B1890629 : Blo 838352 1890629 := bbase (se 4 (by rfl) ⟨177246, by rfl⟩ : syracuseStep 1890629 = 354493) (by norm_num)
theorem B1890701 : Blo 838352 1890701 := bbase (se 3 (by rfl) ⟨354506, by rfl⟩ : syracuseStep 1890701 = 709013) (by norm_num)
theorem B1792469 : Blo 838352 1792469 := bbase (se 7 (by rfl) ⟨21005, by rfl⟩ : syracuseStep 1792469 = 42011) (by norm_num)
theorem B4250069 : Blo 838352 4250069 := bbase (se 7 (by rfl) ⟨49805, by rfl⟩ : syracuseStep 4250069 = 99611) (by norm_num)
theorem B1890773 : Blo 838352 1890773 := bbase (se 7 (by rfl) ⟨22157, by rfl⟩ : syracuseStep 1890773 = 44315) (by norm_num)
theorem B1890845 : Blo 838352 1890845 := bbase (se 3 (by rfl) ⟨354533, by rfl⟩ : syracuseStep 1890845 = 709067) (by norm_num)
theorem B1595933 : Blo 838352 1595933 := bbase (se 3 (by rfl) ⟨299237, by rfl⟩ : syracuseStep 1595933 = 598475) (by norm_num)
theorem B1890917 : Blo 838352 1890917 := bbase (se 4 (by rfl) ⟨177273, by rfl⟩ : syracuseStep 1890917 = 354547) (by norm_num)
theorem B1890989 : Blo 838352 1890989 := bbase (se 3 (by rfl) ⟨354560, by rfl⟩ : syracuseStep 1890989 = 709121) (by norm_num)
theorem B2841317 : Blo 838352 2841317 := bbase (se 4 (by rfl) ⟨266373, by rfl⟩ : syracuseStep 2841317 = 532747) (by norm_num)
theorem B1891061 : Blo 838352 1891061 := bbase (se 5 (by rfl) ⟨88643, by rfl⟩ : syracuseStep 1891061 = 177287) (by norm_num)
theorem B3824405 : Blo 838352 3824405 := bbase (se 6 (by rfl) ⟨89634, by rfl⟩ : syracuseStep 3824405 = 179269) (by norm_num)
theorem B1891133 : Blo 838352 1891133 := bbase (se 3 (by rfl) ⟨354587, by rfl⟩ : syracuseStep 1891133 = 709175) (by norm_num)
theorem B1891205 : Blo 838352 1891205 := bbase (se 4 (by rfl) ⟨177300, by rfl⟩ : syracuseStep 1891205 = 354601) (by norm_num)
theorem B1891277 : Blo 838352 1891277 := bbase (se 3 (by rfl) ⟨354614, by rfl⟩ : syracuseStep 1891277 = 709229) (by norm_num)
theorem B2153453 : Blo 838352 2153453 := bbase (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) (by norm_num)
theorem B908281 : Blo 838352 908281 := bbase (se 2 (by rfl) ⟨340605, by rfl⟩ : syracuseStep 908281 = 681211) (by norm_num)
theorem B1891349 : Blo 838352 1891349 := bbase (se 6 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 1891349 = 88657) (by norm_num)
theorem B2022421 : Blo 838352 2022421 := bbase (se 6 (by rfl) ⟨47400, by rfl⟩ : syracuseStep 2022421 = 94801) (by norm_num)
theorem B2874437 : Blo 838352 2874437 := bbase (se 4 (by rfl) ⟨269478, by rfl⟩ : syracuseStep 2874437 = 538957) (by norm_num)
theorem B1891421 : Blo 838352 1891421 := bbase (se 3 (by rfl) ⟨354641, by rfl⟩ : syracuseStep 1891421 = 709283) (by norm_num)
theorem B6380693 : Blo 838352 6380693 := bbase (se 6 (by rfl) ⟨149547, by rfl⟩ : syracuseStep 6380693 = 299095) (by norm_num)
theorem B2841749 : Blo 838352 2841749 := bbase (se 6 (by rfl) ⟨66603, by rfl⟩ : syracuseStep 2841749 = 133207) (by norm_num)
theorem B1891493 : Blo 838352 1891493 := bbase (se 4 (by rfl) ⟨177327, by rfl⟩ : syracuseStep 1891493 = 354655) (by norm_num)
theorem B1891565 : Blo 838352 1891565 := bbase (se 3 (by rfl) ⟨354668, by rfl⟩ : syracuseStep 1891565 = 709337) (by norm_num)
theorem B1596685 : Blo 838352 1596685 := bbase (se 3 (by rfl) ⟨299378, by rfl⟩ : syracuseStep 1596685 = 598757) (by norm_num)
theorem B1793333 : Blo 838352 1793333 := bbase (se 5 (by rfl) ⟨84062, by rfl⟩ : syracuseStep 1793333 = 168125) (by norm_num)
theorem B1891637 : Blo 838352 1891637 := bbase (se 5 (by rfl) ⟨88670, by rfl⟩ : syracuseStep 1891637 = 177341) (by norm_num)
theorem B1891709 : Blo 838352 1891709 := bbase (se 3 (by rfl) ⟨354695, by rfl⟩ : syracuseStep 1891709 = 709391) (by norm_num)
theorem B1596829 : Blo 838352 1596829 := bbase (se 3 (by rfl) ⟨299405, by rfl⟩ : syracuseStep 1596829 = 598811) (by norm_num)
theorem B1793477 : Blo 838352 1793477 := bbase (se 4 (by rfl) ⟨168138, by rfl⟩ : syracuseStep 1793477 = 336277) (by norm_num)
theorem B1891781 : Blo 838352 1891781 := bbase (se 4 (by rfl) ⟨177354, by rfl⟩ : syracuseStep 1891781 = 354709) (by norm_num)
theorem B1891853 : Blo 838352 1891853 := bbase (se 3 (by rfl) ⟨354722, by rfl⟩ : syracuseStep 1891853 = 709445) (by norm_num)
theorem B1596989 : Blo 838352 1596989 := bbase (se 3 (by rfl) ⟨299435, by rfl⟩ : syracuseStep 1596989 = 598871) (by norm_num)
theorem B2842181 : Blo 838352 2842181 := bbase (se 4 (by rfl) ⟨266454, by rfl⟩ : syracuseStep 2842181 = 532909) (by norm_num)
theorem B1891925 : Blo 838352 1891925 := bbase (se 8 (by rfl) ⟨11085, by rfl⟩ : syracuseStep 1891925 = 22171) (by norm_num)
theorem B1007197 : Blo 838352 1007197 := bbase (se 3 (by rfl) ⟨188849, by rfl⟩ : syracuseStep 1007197 = 377699) (by norm_num)
theorem B1891997 : Blo 838352 1891997 := bbase (se 3 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 1891997 = 709499) (by norm_num)
theorem B1597133 : Blo 838352 1597133 := bbase (se 3 (by rfl) ⟨299462, by rfl⟩ : syracuseStep 1597133 = 598925) (by norm_num)
theorem B1105633 : Blo 838352 1105633 := bbase (se 2 (by rfl) ⟨414612, by rfl⟩ : syracuseStep 1105633 = 829225) (by norm_num)
theorem B4251365 : Blo 838352 4251365 := bbase (se 4 (by rfl) ⟨398565, by rfl⟩ : syracuseStep 4251365 = 797131) (by norm_num)
theorem B1892069 : Blo 838352 1892069 := bbase (se 4 (by rfl) ⟨177381, by rfl⟩ : syracuseStep 1892069 = 354763) (by norm_num)
theorem B1892141 : Blo 838352 1892141 := bbase (se 3 (by rfl) ⟨354776, by rfl⟩ : syracuseStep 1892141 = 709553) (by norm_num)
theorem B1892213 : Blo 838352 1892213 := bbase (se 5 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 1892213 = 177395) (by norm_num)
theorem B9723797 : Blo 838352 9723797 := bbase (se 6 (by rfl) ⟨227901, by rfl⟩ : syracuseStep 9723797 = 455803) (by norm_num)
theorem B4775861 : Blo 838352 4775861 := bbase (se 5 (by rfl) ⟨223868, by rfl⟩ : syracuseStep 4775861 = 447737) (by norm_num)
theorem B1892285 : Blo 838352 1892285 := bbase (se 3 (by rfl) ⟨354803, by rfl⟩ : syracuseStep 1892285 = 709607) (by norm_num)
theorem B1597421 : Blo 838352 1597421 := bbase (se 3 (by rfl) ⟨299516, by rfl⟩ : syracuseStep 1597421 = 599033) (by norm_num)
theorem B2842613 : Blo 838352 2842613 := bbase (se 5 (by rfl) ⟨133247, by rfl⟩ : syracuseStep 2842613 = 266495) (by norm_num)
theorem B1892357 : Blo 838352 1892357 := bbase (se 4 (by rfl) ⟨177408, by rfl⟩ : syracuseStep 1892357 = 354817) (by norm_num)
theorem B1892429 : Blo 838352 1892429 := bbase (se 3 (by rfl) ⟨354830, by rfl⟩ : syracuseStep 1892429 = 709661) (by norm_num)
theorem B909425 : Blo 838352 909425 := bbase (se 2 (by rfl) ⟨341034, by rfl⟩ : syracuseStep 909425 = 682069) (by norm_num)
theorem B1597573 : Blo 838352 1597573 := bbase (se 4 (by rfl) ⟨149772, by rfl⟩ : syracuseStep 1597573 = 299545) (by norm_num)
theorem B12116117 : Blo 838352 12116117 := bbase (se 6 (by rfl) ⟨283971, by rfl⟩ : syracuseStep 12116117 = 567943) (by norm_num)
theorem B1892501 : Blo 838352 1892501 := bbase (se 6 (by rfl) ⟨44355, by rfl⟩ : syracuseStep 1892501 = 88711) (by norm_num)
theorem B1794221 : Blo 838352 1794221 := bbase (se 3 (by rfl) ⟨336416, by rfl⟩ : syracuseStep 1794221 = 672833) (by norm_num)
theorem B1892573 : Blo 838352 1892573 := bbase (se 3 (by rfl) ⟨354857, by rfl⟩ : syracuseStep 1892573 = 709715) (by norm_num)
theorem B1892645 : Blo 838352 1892645 := bbase (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) (by norm_num)
theorem B1892717 : Blo 838352 1892717 := bbase (se 3 (by rfl) ⟨354884, by rfl⟩ : syracuseStep 1892717 = 709769) (by norm_num)
theorem B2122109 : Blo 838352 2122109 := bbase (se 3 (by rfl) ⟨397895, by rfl⟩ : syracuseStep 2122109 = 795791) (by norm_num)
theorem B1892789 : Blo 838352 1892789 := bbase (se 5 (by rfl) ⟨88724, by rfl⟩ : syracuseStep 1892789 = 177449) (by norm_num)
theorem B1597877 : Blo 838352 1597877 := bbase (se 5 (by rfl) ⟨74900, by rfl⟩ : syracuseStep 1597877 = 149801) (by norm_num)
theorem B1892861 : Blo 838352 1892861 := bbase (se 3 (by rfl) ⟨354911, by rfl⟩ : syracuseStep 1892861 = 709823) (by norm_num)
theorem B1008173 : Blo 838352 1008173 := bbase (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) (by norm_num)
theorem B2122301 : Blo 838352 2122301 := bbase (se 3 (by rfl) ⟨397931, by rfl⟩ : syracuseStep 2122301 = 795863) (by norm_num)
theorem B1892933 : Blo 838352 1892933 := bbase (se 4 (by rfl) ⟨177462, by rfl⟩ : syracuseStep 1892933 = 354925) (by norm_num)
theorem B1893005 : Blo 838352 1893005 := bbase (se 3 (by rfl) ⟨354938, by rfl⟩ : syracuseStep 1893005 = 709877) (by norm_num)
theorem B1893077 : Blo 838352 1893077 := bbase (se 7 (by rfl) ⟨22184, by rfl⟩ : syracuseStep 1893077 = 44369) (by norm_num)
theorem B2155261 : Blo 838352 2155261 := bbase (se 3 (by rfl) ⟨404111, by rfl⟩ : syracuseStep 2155261 = 808223) (by norm_num)
theorem B1893149 : Blo 838352 1893149 := bbase (se 3 (by rfl) ⟨354965, by rfl⟩ : syracuseStep 1893149 = 709931) (by norm_num)
theorem B34530133 : Blo 838352 34530133 := bbase (se 9 (by rfl) ⟨101162, by rfl⟩ : syracuseStep 34530133 = 202325) (by norm_num)
theorem B1893221 : Blo 838352 1893221 := bbase (se 4 (by rfl) ⟨177489, by rfl⟩ : syracuseStep 1893221 = 354979) (by norm_num)
theorem B2122645 : Blo 838352 2122645 := bbase (se 6 (by rfl) ⟨49749, by rfl⟩ : syracuseStep 2122645 = 99499) (by norm_num)
theorem B3597205 : Blo 838352 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B1794973 : Blo 838352 1794973 := bbase (se 3 (by rfl) ⟨336557, by rfl⟩ : syracuseStep 1794973 = 673115) (by norm_num)
theorem B1893293 : Blo 838352 1893293 := bbase (se 3 (by rfl) ⟨354992, by rfl⟩ : syracuseStep 1893293 = 709985) (by norm_num)
theorem B4252661 : Blo 838352 4252661 := bbase (se 5 (by rfl) ⟨199343, by rfl⟩ : syracuseStep 4252661 = 398687) (by norm_num)
theorem B1893365 : Blo 838352 1893365 := bbase (se 5 (by rfl) ⟨88751, by rfl⟩ : syracuseStep 1893365 = 177503) (by norm_num)
theorem B2122757 : Blo 838352 2122757 := bbase (se 4 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 2122757 = 398017) (by norm_num)
theorem B1008649 : Blo 838352 1008649 := bbase (se 2 (by rfl) ⟨378243, by rfl⟩ : syracuseStep 1008649 = 756487) (by norm_num)
theorem B910369 : Blo 838352 910369 := bbase (se 2 (by rfl) ⟨341388, by rfl⟩ : syracuseStep 910369 = 682777) (by norm_num)
theorem B1008677 : Blo 838352 1008677 := bbase (se 4 (by rfl) ⟨94563, by rfl⟩ : syracuseStep 1008677 = 189127) (by norm_num)
theorem B1795117 : Blo 838352 1795117 := bbase (se 3 (by rfl) ⟨336584, by rfl⟩ : syracuseStep 1795117 = 673169) (by norm_num)
theorem B1893437 : Blo 838352 1893437 := bbase (se 3 (by rfl) ⟨355019, by rfl⟩ : syracuseStep 1893437 = 710039) (by norm_num)
theorem B943177 : Blo 838352 943177 := bbase (se 2 (by rfl) ⟨353691, by rfl⟩ : syracuseStep 943177 = 707383) (by norm_num)
theorem B943213 : Blo 838352 943213 := bbase (se 3 (by rfl) ⟨176852, by rfl⟩ : syracuseStep 943213 = 353705) (by norm_num)
theorem B1893509 : Blo 838352 1893509 := bbase (se 4 (by rfl) ⟨177516, by rfl⟩ : syracuseStep 1893509 = 355033) (by norm_num)
theorem B943249 : Blo 838352 943249 := bbase (se 2 (by rfl) ⟨353718, by rfl⟩ : syracuseStep 943249 = 707437) (by norm_num)
theorem B1598629 : Blo 838352 1598629 := bbase (se 4 (by rfl) ⟨149871, by rfl⟩ : syracuseStep 1598629 = 299743) (by norm_num)
theorem B943285 : Blo 838352 943285 := bbase (se 5 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 943285 = 88433) (by norm_num)
theorem B2122949 : Blo 838352 2122949 := bbase (se 4 (by rfl) ⟨199026, by rfl⟩ : syracuseStep 2122949 = 398053) (by norm_num)
theorem B1893581 : Blo 838352 1893581 := bbase (se 3 (by rfl) ⟨355046, by rfl⟩ : syracuseStep 1893581 = 710093) (by norm_num)
theorem B943321 : Blo 838352 943321 := bbase (se 2 (by rfl) ⟨353745, by rfl⟩ : syracuseStep 943321 = 707491) (by norm_num)
theorem B1008865 : Blo 838352 1008865 := bbase (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) (by norm_num)
theorem B943357 : Blo 838352 943357 := bbase (se 3 (by rfl) ⟨176879, by rfl⟩ : syracuseStep 943357 = 353759) (by norm_num)
theorem B1893653 : Blo 838352 1893653 := bbase (se 6 (by rfl) ⟨44382, by rfl⟩ : syracuseStep 1893653 = 88765) (by norm_num)
theorem B943393 : Blo 838352 943393 := bbase (se 2 (by rfl) ⟨353772, by rfl⟩ : syracuseStep 943393 = 707545) (by norm_num)
theorem B1598773 : Blo 838352 1598773 := bbase (se 5 (by rfl) ⟨74942, by rfl⟩ : syracuseStep 1598773 = 149885) (by norm_num)
theorem B943429 : Blo 838352 943429 := bbase (se 4 (by rfl) ⟨88446, by rfl⟩ : syracuseStep 943429 = 176893) (by norm_num)
theorem B1008985 : Blo 838352 1008985 := bbase (se 2 (by rfl) ⟨378369, by rfl⟩ : syracuseStep 1008985 = 756739) (by norm_num)
theorem B1893725 : Blo 838352 1893725 := bbase (se 3 (by rfl) ⟨355073, by rfl⟩ : syracuseStep 1893725 = 710147) (by norm_num)
theorem B943465 : Blo 838352 943465 := bbase (se 2 (by rfl) ⟨353799, by rfl⟩ : syracuseStep 943465 = 707599) (by norm_num)
theorem B943501 : Blo 838352 943501 := bbase (se 3 (by rfl) ⟨176906, by rfl⟩ : syracuseStep 943501 = 353813) (by norm_num)
theorem B1795493 : Blo 838352 1795493 := bbase (se 4 (by rfl) ⟨168327, by rfl⟩ : syracuseStep 1795493 = 336655) (by norm_num)
theorem B1893797 : Blo 838352 1893797 := bbase (se 4 (by rfl) ⟨177543, by rfl⟩ : syracuseStep 1893797 = 355087) (by norm_num)
theorem B943537 : Blo 838352 943537 := bbase (se 2 (by rfl) ⟨353826, by rfl⟩ : syracuseStep 943537 = 707653) (by norm_num)
theorem B943573 : Blo 838352 943573 := bbase (se 7 (by rfl) ⟨11057, by rfl⟩ : syracuseStep 943573 = 22115) (by norm_num)
theorem B1598933 : Blo 838352 1598933 := bbase (se 7 (by rfl) ⟨18737, by rfl⟩ : syracuseStep 1598933 = 37475) (by norm_num)
theorem B1893869 : Blo 838352 1893869 := bbase (se 3 (by rfl) ⟨355100, by rfl⟩ : syracuseStep 1893869 = 710201) (by norm_num)
theorem B943609 : Blo 838352 943609 := bbase (se 2 (by rfl) ⟨353853, by rfl⟩ : syracuseStep 943609 = 707707) (by norm_num)
theorem B943645 : Blo 838352 943645 := bbase (se 3 (by rfl) ⟨176933, by rfl⟩ : syracuseStep 943645 = 353867) (by norm_num)
theorem B2123293 : Blo 838352 2123293 := bbase (se 3 (by rfl) ⟨398117, by rfl⟩ : syracuseStep 2123293 = 796235) (by norm_num)
theorem B1893941 : Blo 838352 1893941 := bbase (se 5 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 1893941 = 177557) (by norm_num)
theorem B943681 : Blo 838352 943681 := bbase (se 2 (by rfl) ⟨353880, by rfl⟩ : syracuseStep 943681 = 707761) (by norm_num)
theorem B943717 : Blo 838352 943717 := bbase (se 4 (by rfl) ⟨88473, by rfl⟩ : syracuseStep 943717 = 176947) (by norm_num)
theorem B1599077 : Blo 838352 1599077 := bbase (se 4 (by rfl) ⟨149913, by rfl⟩ : syracuseStep 1599077 = 299827) (by norm_num)
theorem B1435253 : Blo 838352 1435253 := bbase (se 5 (by rfl) ⟨67277, by rfl⟩ : syracuseStep 1435253 = 134555) (by norm_num)
theorem B1894013 : Blo 838352 1894013 := bbase (se 3 (by rfl) ⟨355127, by rfl⟩ : syracuseStep 1894013 = 710255) (by norm_num)
theorem B943753 : Blo 838352 943753 := bbase (se 2 (by rfl) ⟨353907, by rfl⟩ : syracuseStep 943753 = 707815) (by norm_num)
theorem B2123405 : Blo 838352 2123405 := bbase (se 3 (by rfl) ⟨398138, by rfl⟩ : syracuseStep 2123405 = 796277) (by norm_num)
theorem B943789 : Blo 838352 943789 := bbase (se 3 (by rfl) ⟨176960, by rfl⟩ : syracuseStep 943789 = 353921) (by norm_num)
theorem B1894085 : Blo 838352 1894085 := bbase (se 4 (by rfl) ⟨177570, by rfl⟩ : syracuseStep 1894085 = 355141) (by norm_num)
theorem B943825 : Blo 838352 943825 := bbase (se 2 (by rfl) ⟨353934, by rfl⟩ : syracuseStep 943825 = 707869) (by norm_num)
theorem B943861 : Blo 838352 943861 := bbase (se 5 (by rfl) ⟨44243, by rfl⟩ : syracuseStep 943861 = 88487) (by norm_num)
theorem B1894157 : Blo 838352 1894157 := bbase (se 3 (by rfl) ⟨355154, by rfl⟩ : syracuseStep 1894157 = 710309) (by norm_num)
theorem B1795861 : Blo 838352 1795861 := bbase (se 6 (by rfl) ⟨42090, by rfl⟩ : syracuseStep 1795861 = 84181) (by norm_num)
theorem B943897 : Blo 838352 943897 := bbase (se 2 (by rfl) ⟨353961, by rfl⟩ : syracuseStep 943897 = 707923) (by norm_num)
theorem B943933 : Blo 838352 943933 := bbase (se 3 (by rfl) ⟨176987, by rfl⟩ : syracuseStep 943933 = 353975) (by norm_num)
theorem B2123597 : Blo 838352 2123597 := bbase (se 3 (by rfl) ⟨398174, by rfl⟩ : syracuseStep 2123597 = 796349) (by norm_num)
theorem B1894229 : Blo 838352 1894229 := bbase (se 9 (by rfl) ⟨5549, by rfl⟩ : syracuseStep 1894229 = 11099) (by norm_num)
theorem B943969 : Blo 838352 943969 := bbase (se 2 (by rfl) ⟨353988, by rfl⟩ : syracuseStep 943969 = 707977) (by norm_num)
theorem B944005 : Blo 838352 944005 := bbase (se 4 (by rfl) ⟨88500, by rfl⟩ : syracuseStep 944005 = 177001) (by norm_num)
theorem B1894301 : Blo 838352 1894301 := bbase (se 3 (by rfl) ⟨355181, by rfl⟩ : syracuseStep 1894301 = 710363) (by norm_num)
theorem B944041 : Blo 838352 944041 := bbase (se 2 (by rfl) ⟨354015, by rfl⟩ : syracuseStep 944041 = 708031) (by norm_num)
theorem B944077 : Blo 838352 944077 := bbase (se 3 (by rfl) ⟨177014, by rfl⟩ : syracuseStep 944077 = 354029) (by norm_num)
theorem B1894373 : Blo 838352 1894373 := bbase (se 4 (by rfl) ⟨177597, by rfl⟩ : syracuseStep 1894373 = 355195) (by norm_num)
theorem B944113 : Blo 838352 944113 := bbase (se 2 (by rfl) ⟨354042, by rfl⟩ : syracuseStep 944113 = 708085) (by norm_num)
theorem B944149 : Blo 838352 944149 := bbase (se 6 (by rfl) ⟨22128, by rfl⟩ : syracuseStep 944149 = 44257) (by norm_num)
theorem B1894445 : Blo 838352 1894445 := bbase (se 3 (by rfl) ⟨355208, by rfl⟩ : syracuseStep 1894445 = 710417) (by norm_num)
theorem B2156597 : Blo 838352 2156597 := bbase (se 5 (by rfl) ⟨101090, by rfl⟩ : syracuseStep 2156597 = 202181) (by norm_num)
theorem B944185 : Blo 838352 944185 := bbase (se 2 (by rfl) ⟨354069, by rfl⟩ : syracuseStep 944185 = 708139) (by norm_num)
theorem B944221 : Blo 838352 944221 := bbase (se 3 (by rfl) ⟨177041, by rfl⟩ : syracuseStep 944221 = 354083) (by norm_num)
theorem B1534069 : Blo 838352 1534069 := bbase (se 5 (by rfl) ⟨71909, by rfl⟩ : syracuseStep 1534069 = 143819) (by norm_num)
theorem B1894517 : Blo 838352 1894517 := bbase (se 5 (by rfl) ⟨88805, by rfl⟩ : syracuseStep 1894517 = 177611) (by norm_num)
theorem B944257 : Blo 838352 944257 := bbase (se 2 (by rfl) ⟨354096, by rfl⟩ : syracuseStep 944257 = 708193) (by norm_num)
theorem B2123941 : Blo 838352 2123941 := bbase (se 4 (by rfl) ⟨199119, by rfl⟩ : syracuseStep 2123941 = 398239) (by norm_num)
theorem B944293 : Blo 838352 944293 := bbase (se 4 (by rfl) ⟨88527, by rfl⟩ : syracuseStep 944293 = 177055) (by norm_num)
theorem B1894589 : Blo 838352 1894589 := bbase (se 3 (by rfl) ⟨355235, by rfl⟩ : syracuseStep 1894589 = 710471) (by norm_num)
theorem B944329 : Blo 838352 944329 := bbase (se 2 (by rfl) ⟨354123, by rfl⟩ : syracuseStep 944329 = 708247) (by norm_num)
theorem B944365 : Blo 838352 944365 := bbase (se 3 (by rfl) ⟨177068, by rfl⟩ : syracuseStep 944365 = 354137) (by norm_num)
theorem B4253957 : Blo 838352 4253957 := bbase (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) (by norm_num)
theorem B1894661 : Blo 838352 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B944401 : Blo 838352 944401 := bbase (se 2 (by rfl) ⟨354150, by rfl⟩ : syracuseStep 944401 = 708301) (by norm_num)
theorem B2124053 : Blo 838352 2124053 := bbase (se 6 (by rfl) ⟨49782, by rfl⟩ : syracuseStep 2124053 = 99565) (by norm_num)
theorem B6056213 : Blo 838352 6056213 := bbase (se 6 (by rfl) ⟨141942, by rfl⟩ : syracuseStep 6056213 = 283885) (by norm_num)
theorem B944437 : Blo 838352 944437 := bbase (se 5 (by rfl) ⟨44270, by rfl⟩ : syracuseStep 944437 = 88541) (by norm_num)
theorem B1894733 : Blo 838352 1894733 := bbase (se 3 (by rfl) ⟨355262, by rfl⟩ : syracuseStep 1894733 = 710525) (by norm_num)
theorem B944473 : Blo 838352 944473 := bbase (se 2 (by rfl) ⟨354177, by rfl⟩ : syracuseStep 944473 = 708355) (by norm_num)
theorem B944509 : Blo 838352 944509 := bbase (se 3 (by rfl) ⟨177095, by rfl⟩ : syracuseStep 944509 = 354191) (by norm_num)
theorem B1894805 : Blo 838352 1894805 := bbase (se 6 (by rfl) ⟨44409, by rfl⟩ : syracuseStep 1894805 = 88819) (by norm_num)
theorem B944545 : Blo 838352 944545 := bbase (se 2 (by rfl) ⟨354204, by rfl⟩ : syracuseStep 944545 = 708409) (by norm_num)
theorem B944581 : Blo 838352 944581 := bbase (se 4 (by rfl) ⟨88554, by rfl⟩ : syracuseStep 944581 = 177109) (by norm_num)
theorem B2124245 : Blo 838352 2124245 := bbase (se 7 (by rfl) ⟨24893, by rfl⟩ : syracuseStep 2124245 = 49787) (by norm_num)
theorem B1894877 : Blo 838352 1894877 := bbase (se 3 (by rfl) ⟨355289, by rfl⟩ : syracuseStep 1894877 = 710579) (by norm_num)
theorem B944617 : Blo 838352 944617 := bbase (se 2 (by rfl) ⟨354231, by rfl⟩ : syracuseStep 944617 = 708463) (by norm_num)
theorem B944653 : Blo 838352 944653 := bbase (se 3 (by rfl) ⟨177122, by rfl⟩ : syracuseStep 944653 = 354245) (by norm_num)
theorem B1894949 : Blo 838352 1894949 := bbase (se 4 (by rfl) ⟨177651, by rfl⟩ : syracuseStep 1894949 = 355303) (by norm_num)
theorem B944689 : Blo 838352 944689 := bbase (se 2 (by rfl) ⟨354258, by rfl⟩ : syracuseStep 944689 = 708517) (by norm_num)
theorem B944725 : Blo 838352 944725 := bbase (se 8 (by rfl) ⟨5535, by rfl⟩ : syracuseStep 944725 = 11071) (by norm_num)
theorem B1895021 : Blo 838352 1895021 := bbase (se 3 (by rfl) ⟨355316, by rfl⟩ : syracuseStep 1895021 = 710633) (by norm_num)
theorem B944761 : Blo 838352 944761 := bbase (se 2 (by rfl) ⟨354285, by rfl⟩ : syracuseStep 944761 = 708571) (by norm_num)
theorem B944797 : Blo 838352 944797 := bbase (se 3 (by rfl) ⟨177149, by rfl⟩ : syracuseStep 944797 = 354299) (by norm_num)
theorem B1895093 : Blo 838352 1895093 := bbase (se 5 (by rfl) ⟨88832, by rfl⟩ : syracuseStep 1895093 = 177665) (by norm_num)
theorem B944833 : Blo 838352 944833 := bbase (se 2 (by rfl) ⟨354312, by rfl⟩ : syracuseStep 944833 = 708625) (by norm_num)
theorem B944869 : Blo 838352 944869 := bbase (se 4 (by rfl) ⟨88581, by rfl⟩ : syracuseStep 944869 = 177163) (by norm_num)
theorem B1895165 : Blo 838352 1895165 := bbase (se 3 (by rfl) ⟨355343, by rfl⟩ : syracuseStep 1895165 = 710687) (by norm_num)
theorem B944905 : Blo 838352 944905 := bbase (se 2 (by rfl) ⟨354339, by rfl⟩ : syracuseStep 944905 = 708679) (by norm_num)
theorem B2124589 : Blo 838352 2124589 := bbase (se 3 (by rfl) ⟨398360, by rfl⟩ : syracuseStep 2124589 = 796721) (by norm_num)
theorem B944941 : Blo 838352 944941 := bbase (se 3 (by rfl) ⟨177176, by rfl⟩ : syracuseStep 944941 = 354353) (by norm_num)
theorem B1895237 : Blo 838352 1895237 := bbase (se 4 (by rfl) ⟨177678, by rfl⟩ : syracuseStep 1895237 = 355357) (by norm_num)
theorem B944977 : Blo 838352 944977 := bbase (se 2 (by rfl) ⟨354366, by rfl⟩ : syracuseStep 944977 = 708733) (by norm_num)
theorem B43608917 : Blo 838352 43608917 := bbase (se 9 (by rfl) ⟨127760, by rfl⟩ : syracuseStep 43608917 = 255521) (by norm_num)
theorem B945013 : Blo 838352 945013 := bbase (se 5 (by rfl) ⟨44297, by rfl⟩ : syracuseStep 945013 = 88595) (by norm_num)
theorem B1010561 : Blo 838352 1010561 := bbase (se 2 (by rfl) ⟨378960, by rfl⟩ : syracuseStep 1010561 = 757921) (by norm_num)
theorem B945049 : Blo 838352 945049 := bbase (se 2 (by rfl) ⟨354393, by rfl⟩ : syracuseStep 945049 = 708787) (by norm_num)
theorem B2124701 : Blo 838352 2124701 := bbase (se 3 (by rfl) ⟨398381, by rfl⟩ : syracuseStep 2124701 = 796763) (by norm_num)
theorem B945085 : Blo 838352 945085 := bbase (se 3 (by rfl) ⟨177203, by rfl⟩ : syracuseStep 945085 = 354407) (by norm_num)
theorem B945121 : Blo 838352 945121 := bbase (se 2 (by rfl) ⟨354420, by rfl⟩ : syracuseStep 945121 = 708841) (by norm_num)
theorem B945157 : Blo 838352 945157 := bbase (se 4 (by rfl) ⟨88608, by rfl⟩ : syracuseStep 945157 = 177217) (by norm_num)
theorem B1534997 : Blo 838352 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B945193 : Blo 838352 945193 := bbase (se 2 (by rfl) ⟨354447, by rfl⟩ : syracuseStep 945193 = 708895) (by norm_num)
theorem B1436725 : Blo 838352 1436725 := bbase (se 5 (by rfl) ⟨67346, by rfl⟩ : syracuseStep 1436725 = 134693) (by norm_num)
theorem B945229 : Blo 838352 945229 := bbase (se 3 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 945229 = 354461) (by norm_num)
theorem B2124893 : Blo 838352 2124893 := bbase (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) (by norm_num)
theorem B945265 : Blo 838352 945265 := bbase (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) (by norm_num)
theorem B945301 : Blo 838352 945301 := bbase (se 6 (by rfl) ⟨22155, by rfl⟩ : syracuseStep 945301 = 44311) (by norm_num)
theorem B945337 : Blo 838352 945337 := bbase (se 2 (by rfl) ⟨354501, by rfl⟩ : syracuseStep 945337 = 709003) (by norm_num)
theorem B945373 : Blo 838352 945373 := bbase (se 3 (by rfl) ⟨177257, by rfl⟩ : syracuseStep 945373 = 354515) (by norm_num)
theorem B1797365 : Blo 838352 1797365 := bbase (se 5 (by rfl) ⟨84251, by rfl⟩ : syracuseStep 1797365 = 168503) (by norm_num)
theorem B945409 : Blo 838352 945409 := bbase (se 2 (by rfl) ⟨354528, by rfl⟩ : syracuseStep 945409 = 709057) (by norm_num)
theorem B945445 : Blo 838352 945445 := bbase (se 4 (by rfl) ⟨88635, by rfl⟩ : syracuseStep 945445 = 177271) (by norm_num)
theorem B945481 : Blo 838352 945481 := bbase (se 2 (by rfl) ⟨354555, by rfl⟩ : syracuseStep 945481 = 709111) (by norm_num)
theorem B945517 : Blo 838352 945517 := bbase (se 3 (by rfl) ⟨177284, by rfl⟩ : syracuseStep 945517 = 354569) (by norm_num)
theorem B1797509 : Blo 838352 1797509 := bbase (se 4 (by rfl) ⟨168516, by rfl⟩ : syracuseStep 1797509 = 337033) (by norm_num)
theorem B945553 : Blo 838352 945553 := bbase (se 2 (by rfl) ⟨354582, by rfl⟩ : syracuseStep 945553 = 709165) (by norm_num)
theorem B2125237 : Blo 838352 2125237 := bbase (se 5 (by rfl) ⟨99620, by rfl⟩ : syracuseStep 2125237 = 199241) (by norm_num)
theorem B945589 : Blo 838352 945589 := bbase (se 5 (by rfl) ⟨44324, by rfl⟩ : syracuseStep 945589 = 88649) (by norm_num)
theorem B945625 : Blo 838352 945625 := bbase (se 2 (by rfl) ⟨354609, by rfl⟩ : syracuseStep 945625 = 709219) (by norm_num)
theorem B945661 : Blo 838352 945661 := bbase (se 3 (by rfl) ⟨177311, by rfl⟩ : syracuseStep 945661 = 354623) (by norm_num)
theorem B4255253 : Blo 838352 4255253 := bbase (se 6 (by rfl) ⟨99732, by rfl⟩ : syracuseStep 4255253 = 199465) (by norm_num)
theorem B945697 : Blo 838352 945697 := bbase (se 2 (by rfl) ⟨354636, by rfl⟩ : syracuseStep 945697 = 709273) (by norm_num)
theorem B2125349 : Blo 838352 2125349 := bbase (se 4 (by rfl) ⟨199251, by rfl⟩ : syracuseStep 2125349 = 398503) (by norm_num)
theorem B1011253 : Blo 838352 1011253 := bbase (se 5 (by rfl) ⟨47402, by rfl⟩ : syracuseStep 1011253 = 94805) (by norm_num)
theorem B945733 : Blo 838352 945733 := bbase (se 4 (by rfl) ⟨88662, by rfl⟩ : syracuseStep 945733 = 177325) (by norm_num)
theorem B945769 : Blo 838352 945769 := bbase (se 2 (by rfl) ⟨354663, by rfl⟩ : syracuseStep 945769 = 709327) (by norm_num)
theorem B945805 : Blo 838352 945805 := bbase (se 3 (by rfl) ⟨177338, by rfl⟩ : syracuseStep 945805 = 354677) (by norm_num)
theorem B1011349 : Blo 838352 1011349 := bbase (se 6 (by rfl) ⟨23703, by rfl⟩ : syracuseStep 1011349 = 47407) (by norm_num)
theorem B945841 : Blo 838352 945841 := bbase (se 2 (by rfl) ⟨354690, by rfl⟩ : syracuseStep 945841 = 709381) (by norm_num)
theorem B945877 : Blo 838352 945877 := bbase (se 7 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 945877 = 22169) (by norm_num)
theorem B2125541 : Blo 838352 2125541 := bbase (se 4 (by rfl) ⟨199269, by rfl⟩ : syracuseStep 2125541 = 398539) (by norm_num)
theorem B1797869 : Blo 838352 1797869 := bbase (se 3 (by rfl) ⟨337100, by rfl⟩ : syracuseStep 1797869 = 674201) (by norm_num)
theorem B945913 : Blo 838352 945913 := bbase (se 2 (by rfl) ⟨354717, by rfl⟩ : syracuseStep 945913 = 709435) (by norm_num)
theorem B945949 : Blo 838352 945949 := bbase (se 3 (by rfl) ⟨177365, by rfl⟩ : syracuseStep 945949 = 354731) (by norm_num)
theorem B1077025 : Blo 838352 1077025 := bbase (se 2 (by rfl) ⟨403884, by rfl⟩ : syracuseStep 1077025 = 807769) (by norm_num)
theorem B945985 : Blo 838352 945985 := bbase (se 2 (by rfl) ⟨354744, by rfl⟩ : syracuseStep 945985 = 709489) (by norm_num)
theorem B10743637 : Blo 838352 10743637 := bbase (se 9 (by rfl) ⟨31475, by rfl⟩ : syracuseStep 10743637 = 62951) (by norm_num)
theorem B946021 : Blo 838352 946021 := bbase (se 4 (by rfl) ⟨88689, by rfl⟩ : syracuseStep 946021 = 177379) (by norm_num)
theorem B946057 : Blo 838352 946057 := bbase (se 2 (by rfl) ⟨354771, by rfl⟩ : syracuseStep 946057 = 709543) (by norm_num)
theorem B946093 : Blo 838352 946093 := bbase (se 3 (by rfl) ⟨177392, by rfl⟩ : syracuseStep 946093 = 354785) (by norm_num)
theorem B946129 : Blo 838352 946129 := bbase (se 2 (by rfl) ⟨354798, by rfl⟩ : syracuseStep 946129 = 709597) (by norm_num)
theorem B946165 : Blo 838352 946165 := bbase (se 5 (by rfl) ⟨44351, by rfl⟩ : syracuseStep 946165 = 88703) (by norm_num)
theorem B946201 : Blo 838352 946201 := bbase (se 2 (by rfl) ⟨354825, by rfl⟩ : syracuseStep 946201 = 709651) (by norm_num)
theorem B2125885 : Blo 838352 2125885 := bbase (se 3 (by rfl) ⟨398603, by rfl⟩ : syracuseStep 2125885 = 797207) (by norm_num)
theorem B946237 : Blo 838352 946237 := bbase (se 3 (by rfl) ⟨177419, by rfl⟩ : syracuseStep 946237 = 354839) (by norm_num)
theorem B946273 : Blo 838352 946273 := bbase (se 2 (by rfl) ⟨354852, by rfl⟩ : syracuseStep 946273 = 709705) (by norm_num)
theorem B946309 : Blo 838352 946309 := bbase (se 4 (by rfl) ⟨88716, by rfl⟩ : syracuseStep 946309 = 177433) (by norm_num)
theorem B946345 : Blo 838352 946345 := bbase (se 2 (by rfl) ⟨354879, by rfl⟩ : syracuseStep 946345 = 709759) (by norm_num)
theorem B2125997 : Blo 838352 2125997 := bbase (se 3 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 2125997 = 797249) (by norm_num)
theorem B1700021 : Blo 838352 1700021 := bbase (se 5 (by rfl) ⟨79688, by rfl⟩ : syracuseStep 1700021 = 159377) (by norm_num)
theorem B946381 : Blo 838352 946381 := bbase (se 3 (by rfl) ⟨177446, by rfl⟩ : syracuseStep 946381 = 354893) (by norm_num)
theorem B946417 : Blo 838352 946417 := bbase (se 2 (by rfl) ⟨354906, by rfl⟩ : syracuseStep 946417 = 709813) (by norm_num)
theorem B946453 : Blo 838352 946453 := bbase (se 6 (by rfl) ⟨22182, by rfl⟩ : syracuseStep 946453 = 44365) (by norm_num)
theorem B946489 : Blo 838352 946489 := bbase (se 2 (by rfl) ⟨354933, by rfl⟩ : syracuseStep 946489 = 709867) (by norm_num)
theorem B1700165 : Blo 838352 1700165 := bbase (se 4 (by rfl) ⟨159390, by rfl⟩ : syracuseStep 1700165 = 318781) (by norm_num)
theorem B2879813 : Blo 838352 2879813 := bbase (se 4 (by rfl) ⟨269982, by rfl⟩ : syracuseStep 2879813 = 539965) (by norm_num)
theorem B1536349 : Blo 838352 1536349 := bbase (se 3 (by rfl) ⟨288065, by rfl⟩ : syracuseStep 1536349 = 576131) (by norm_num)
theorem B946525 : Blo 838352 946525 := bbase (se 3 (by rfl) ⟨177473, by rfl⟩ : syracuseStep 946525 = 354947) (by norm_num)
theorem B2126189 : Blo 838352 2126189 := bbase (se 3 (by rfl) ⟨398660, by rfl⟩ : syracuseStep 2126189 = 797321) (by norm_num)
theorem B2388341 : Blo 838352 2388341 := bbase (se 5 (by rfl) ⟨111953, by rfl⟩ : syracuseStep 2388341 = 223907) (by norm_num)
theorem B4551029 : Blo 838352 4551029 := bbase (se 5 (by rfl) ⟨213329, by rfl⟩ : syracuseStep 4551029 = 426659) (by norm_num)
theorem B946561 : Blo 838352 946561 := bbase (se 2 (by rfl) ⟨354960, by rfl⟩ : syracuseStep 946561 = 709921) (by norm_num)
theorem B946597 : Blo 838352 946597 := bbase (se 4 (by rfl) ⟨88743, by rfl⟩ : syracuseStep 946597 = 177487) (by norm_num)
theorem B946633 : Blo 838352 946633 := bbase (se 2 (by rfl) ⟨354987, by rfl⟩ : syracuseStep 946633 = 709975) (by norm_num)
theorem B946669 : Blo 838352 946669 := bbase (se 3 (by rfl) ⟨177500, by rfl⟩ : syracuseStep 946669 = 355001) (by norm_num)
theorem B946705 : Blo 838352 946705 := bbase (se 2 (by rfl) ⟨355014, by rfl⟩ : syracuseStep 946705 = 710029) (by norm_num)
theorem B946741 : Blo 838352 946741 := bbase (se 5 (by rfl) ⟨44378, by rfl⟩ : syracuseStep 946741 = 88757) (by norm_num)
theorem B946777 : Blo 838352 946777 := bbase (se 2 (by rfl) ⟨355041, by rfl⟩ : syracuseStep 946777 = 710083) (by norm_num)
theorem B1798757 : Blo 838352 1798757 := bbase (se 4 (by rfl) ⟨168633, by rfl⟩ : syracuseStep 1798757 = 337267) (by norm_num)
theorem B946813 : Blo 838352 946813 := bbase (se 3 (by rfl) ⟨177527, by rfl⟩ : syracuseStep 946813 = 355055) (by norm_num)
theorem B946849 : Blo 838352 946849 := bbase (se 2 (by rfl) ⟨355068, by rfl⟩ : syracuseStep 946849 = 710137) (by norm_num)
theorem B2126533 : Blo 838352 2126533 := bbase (se 4 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 2126533 = 398725) (by norm_num)
theorem B946885 : Blo 838352 946885 := bbase (se 4 (by rfl) ⟨88770, by rfl⟩ : syracuseStep 946885 = 177541) (by norm_num)
theorem B946921 : Blo 838352 946921 := bbase (se 2 (by rfl) ⟨355095, by rfl⟩ : syracuseStep 946921 = 710191) (by norm_num)
theorem B946957 : Blo 838352 946957 := bbase (se 3 (by rfl) ⟨177554, by rfl⟩ : syracuseStep 946957 = 355109) (by norm_num)
theorem B4256549 : Blo 838352 4256549 := bbase (se 4 (by rfl) ⟨399051, by rfl⟩ : syracuseStep 4256549 = 798103) (by norm_num)
theorem B946993 : Blo 838352 946993 := bbase (se 2 (by rfl) ⟨355122, by rfl⟩ : syracuseStep 946993 = 710245) (by norm_num)
theorem B2126645 : Blo 838352 2126645 := bbase (se 5 (by rfl) ⟨99686, by rfl⟩ : syracuseStep 2126645 = 199373) (by norm_num)
theorem B1700669 : Blo 838352 1700669 := bbase (se 3 (by rfl) ⟨318875, by rfl⟩ : syracuseStep 1700669 = 637751) (by norm_num)
theorem B1078093 : Blo 838352 1078093 := bbase (se 3 (by rfl) ⟨202142, by rfl⟩ : syracuseStep 1078093 = 404285) (by norm_num)
theorem B947029 : Blo 838352 947029 := bbase (se 9 (by rfl) ⟨2774, by rfl⟩ : syracuseStep 947029 = 5549) (by norm_num)
theorem B1799005 : Blo 838352 1799005 := bbase (se 3 (by rfl) ⟨337313, by rfl⟩ : syracuseStep 1799005 = 674627) (by norm_num)
theorem B3240805 : Blo 838352 3240805 := bbase (se 4 (by rfl) ⟨303825, by rfl⟩ : syracuseStep 3240805 = 607651) (by norm_num)
theorem B947065 : Blo 838352 947065 := bbase (se 2 (by rfl) ⟨355149, by rfl⟩ : syracuseStep 947065 = 710299) (by norm_num)
theorem B947101 : Blo 838352 947101 := bbase (se 3 (by rfl) ⟨177581, by rfl⟩ : syracuseStep 947101 = 355163) (by norm_num)
theorem B947137 : Blo 838352 947137 := bbase (se 2 (by rfl) ⟨355176, by rfl⟩ : syracuseStep 947137 = 710353) (by norm_num)
theorem B1438661 : Blo 838352 1438661 := bbase (se 4 (by rfl) ⟨134874, by rfl⟩ : syracuseStep 1438661 = 269749) (by norm_num)
theorem B947173 : Blo 838352 947173 := bbase (se 4 (by rfl) ⟨88797, by rfl⟩ : syracuseStep 947173 = 177595) (by norm_num)
theorem B1274869 : Blo 838352 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B2126837 : Blo 838352 2126837 := bbase (se 5 (by rfl) ⟨99695, by rfl⟩ : syracuseStep 2126837 = 199391) (by norm_num)
theorem B947209 : Blo 838352 947209 := bbase (se 2 (by rfl) ⟨355203, by rfl⟩ : syracuseStep 947209 = 710407) (by norm_num)
theorem B947245 : Blo 838352 947245 := bbase (se 3 (by rfl) ⟨177608, by rfl⟩ : syracuseStep 947245 = 355217) (by norm_num)
theorem B2421829 : Blo 838352 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B947281 : Blo 838352 947281 := bbase (se 2 (by rfl) ⟨355230, by rfl⟩ : syracuseStep 947281 = 710461) (by norm_num)
theorem B947317 : Blo 838352 947317 := bbase (se 5 (by rfl) ⟨44405, by rfl⟩ : syracuseStep 947317 = 88811) (by norm_num)
theorem B947353 : Blo 838352 947353 := bbase (se 2 (by rfl) ⟨355257, by rfl⟩ : syracuseStep 947353 = 710515) (by norm_num)
theorem B947389 : Blo 838352 947389 := bbase (se 3 (by rfl) ⟨177635, by rfl⟩ : syracuseStep 947389 = 355271) (by norm_num)
theorem B947425 : Blo 838352 947425 := bbase (se 2 (by rfl) ⟨355284, by rfl⟩ : syracuseStep 947425 = 710569) (by norm_num)
theorem B947461 : Blo 838352 947461 := bbase (se 4 (by rfl) ⟨88824, by rfl⟩ : syracuseStep 947461 = 177649) (by norm_num)
theorem B947497 : Blo 838352 947497 := bbase (se 2 (by rfl) ⟨355311, by rfl⟩ : syracuseStep 947497 = 710623) (by norm_num)
theorem B2127181 : Blo 838352 2127181 := bbase (se 3 (by rfl) ⟨398846, by rfl⟩ : syracuseStep 2127181 = 797693) (by norm_num)
theorem B947533 : Blo 838352 947533 := bbase (se 3 (by rfl) ⟨177662, by rfl⟩ : syracuseStep 947533 = 355325) (by norm_num)
theorem B947569 : Blo 838352 947569 := bbase (se 2 (by rfl) ⟨355338, by rfl⟩ : syracuseStep 947569 = 710677) (by norm_num)
theorem B947605 : Blo 838352 947605 := bbase (se 6 (by rfl) ⟨22209, by rfl⟩ : syracuseStep 947605 = 44419) (by norm_num)
theorem B947641 : Blo 838352 947641 := bbase (se 2 (by rfl) ⟨355365, by rfl⟩ : syracuseStep 947641 = 710731) (by norm_num)
theorem B2127293 : Blo 838352 2127293 := bbase (se 3 (by rfl) ⟨398867, by rfl⟩ : syracuseStep 2127293 = 797735) (by norm_num)
theorem B1078841 : Blo 838352 1078841 := bbase (se 2 (by rfl) ⟨404565, by rfl⟩ : syracuseStep 1078841 = 809131) (by norm_num)
theorem B2127485 : Blo 838352 2127485 := bbase (se 3 (by rfl) ⟨398903, by rfl⟩ : syracuseStep 2127485 = 797807) (by norm_num)
theorem B24180565 : Blo 838352 24180565 := bbase (se 9 (by rfl) ⟨70841, by rfl⟩ : syracuseStep 24180565 = 141683) (by norm_num)
theorem B2389925 : Blo 838352 2389925 := bbase (se 4 (by rfl) ⟨224055, by rfl⟩ : syracuseStep 2389925 = 448111) (by norm_num)
theorem B2127829 : Blo 838352 2127829 := bbase (se 7 (by rfl) ⟨24935, by rfl⟩ : syracuseStep 2127829 = 49871) (by norm_num)
theorem B4257845 : Blo 838352 4257845 := bbase (se 5 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 4257845 = 399173) (by norm_num)
theorem B2127941 : Blo 838352 2127941 := bbase (se 4 (by rfl) ⟨199494, by rfl⟩ : syracuseStep 2127941 = 398989) (by norm_num)
theorem B3930245 : Blo 838352 3930245 := bbase (se 4 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 3930245 = 736921) (by norm_num)
theorem B2128133 : Blo 838352 2128133 := bbase (se 4 (by rfl) ⟨199512, by rfl⟩ : syracuseStep 2128133 = 399025) (by norm_num)
theorem B7174453 : Blo 838352 7174453 := bbase (se 5 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 7174453 = 672605) (by norm_num)
theorem B8092021 : Blo 838352 8092021 := bbase (se 5 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 8092021 = 758627) (by norm_num)
theorem B2161133 : Blo 838352 2161133 := bbase (se 3 (by rfl) ⟨405212, by rfl⟩ : syracuseStep 2161133 = 810425) (by norm_num)
theorem B2423333 : Blo 838352 2423333 := bbase (se 4 (by rfl) ⟨227187, by rfl⟩ : syracuseStep 2423333 = 454375) (by norm_num)
theorem B2390597 : Blo 838352 2390597 := bbase (se 4 (by rfl) ⟨224118, by rfl⟩ : syracuseStep 2390597 = 448237) (by norm_num)
theorem B2128477 : Blo 838352 2128477 := bbase (se 3 (by rfl) ⟨399089, by rfl⟩ : syracuseStep 2128477 = 798179) (by norm_num)
theorem B2128589 : Blo 838352 2128589 := bbase (se 3 (by rfl) ⟨399110, by rfl⟩ : syracuseStep 2128589 = 798221) (by norm_num)
theorem B4029173 : Blo 838352 4029173 := bbase (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) (by norm_num)
theorem B6388469 : Blo 838352 6388469 := bbase (se 5 (by rfl) ⟨299459, by rfl⟩ : syracuseStep 6388469 = 598919) (by norm_num)
theorem B2128781 : Blo 838352 2128781 := bbase (se 3 (by rfl) ⟨399146, by rfl⟩ : syracuseStep 2128781 = 798293) (by norm_num)
theorem B850861 : Blo 838352 850861 := bbase (se 3 (by rfl) ⟨159536, by rfl⟩ : syracuseStep 850861 = 319073) (by norm_num)
theorem B4029365 : Blo 838352 4029365 := bbase (se 5 (by rfl) ⟨188876, by rfl⟩ : syracuseStep 4029365 = 377753) (by norm_num)
theorem B2391029 : Blo 838352 2391029 := bbase (se 5 (by rfl) ⟨112079, by rfl⟩ : syracuseStep 2391029 = 224159) (by norm_num)
theorem B3406997 : Blo 838352 3406997 := bbase (se 6 (by rfl) ⟨79851, by rfl⟩ : syracuseStep 3406997 = 159703) (by norm_num)
theorem B2129125 : Blo 838352 2129125 := bbase (se 4 (by rfl) ⟨199605, by rfl⟩ : syracuseStep 2129125 = 399211) (by norm_num)
theorem B4259141 : Blo 838352 4259141 := bbase (se 4 (by rfl) ⟨399294, by rfl⟩ : syracuseStep 4259141 = 798589) (by norm_num)
theorem B2129237 : Blo 838352 2129237 := bbase (se 11 (by rfl) ⟨1559, by rfl⟩ : syracuseStep 2129237 = 3119) (by norm_num)
theorem B10911125 : Blo 838352 10911125 := bbase (se 6 (by rfl) ⟨255729, by rfl⟩ : syracuseStep 10911125 = 511459) (by norm_num)
theorem B2129429 : Blo 838352 2129429 := bbase (se 6 (by rfl) ⟨49908, by rfl⟩ : syracuseStep 2129429 = 99817) (by norm_num)
theorem B15302357 : Blo 838352 15302357 := bbase (se 7 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 15302357 = 358649) (by norm_num)
theorem B2391781 : Blo 838352 2391781 := bbase (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) (by norm_num)
theorem B2129773 : Blo 838352 2129773 := bbase (se 3 (by rfl) ⟨399332, by rfl⟩ : syracuseStep 2129773 = 798665) (by norm_num)
theorem B1703797 : Blo 838352 1703797 := bbase (se 5 (by rfl) ⟨79865, by rfl⟩ : syracuseStep 1703797 = 159731) (by norm_num)
theorem B2129885 : Blo 838352 2129885 := bbase (se 3 (by rfl) ⟨399353, by rfl⟩ : syracuseStep 2129885 = 798707) (by norm_num)
theorem B2687089 : Blo 838352 2687089 := bstep (se 2 (by rfl) ⟨1007658, by rfl⟩ : syracuseStep 2687089 = 2015317) B2015317
theorem B1278067 : Blo 838352 1278067 := bstep (se 1 (by rfl) ⟨958550, by rfl⟩ : syracuseStep 1278067 = 1917101) B1917101
theorem B4784291 : Blo 838352 4784291 := bstep (se 1 (by rfl) ⟨3588218, by rfl⟩ : syracuseStep 4784291 = 7176437) B7176437
theorem B2130097 : Blo 838352 2130097 := bstep (se 2 (by rfl) ⟨798786, by rfl⟩ : syracuseStep 2130097 = 1597573) B1597573
theorem B1343699 : Blo 838352 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B2425133 : Blo 838352 2425133 := bstep (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) B909425
theorem B1278305 : Blo 838352 1278305 := bstep (se 2 (by rfl) ⟨479364, by rfl⟩ : syracuseStep 1278305 = 958729) B958729
theorem B2687345 : Blo 838352 2687345 := bstep (se 2 (by rfl) ⟨1007754, by rfl⟩ : syracuseStep 2687345 = 2015509) B2015509
theorem B1343891 : Blo 838352 1343891 := bstep (se 1 (by rfl) ⟨1007918, by rfl⟩ : syracuseStep 1343891 = 2015837) B2015837
theorem B2130371 : Blo 838352 2130371 := bstep (se 1 (by rfl) ⟨1597778, by rfl⟩ : syracuseStep 2130371 = 3195557) B3195557
theorem B1278433 : Blo 838352 1278433 := bstep (se 2 (by rfl) ⟨479412, by rfl⟩ : syracuseStep 1278433 = 958825) B958825
theorem B2130563 : Blo 838352 2130563 := bstep (se 1 (by rfl) ⟨1597922, by rfl⟩ : syracuseStep 2130563 = 3195845) B3195845
theorem B6390413 : Blo 838352 6390413 := bstep (se 3 (by rfl) ⟨1198202, by rfl⟩ : syracuseStep 6390413 = 2396405) B2396405
theorem B27984611 : Blo 838352 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B1704739 : Blo 838352 1704739 := bstep (se 1 (by rfl) ⟨1278554, by rfl⟩ : syracuseStep 1704739 = 2557109) B2557109
theorem B4031309 : Blo 838352 4031309 := bstep (se 3 (by rfl) ⟨755870, by rfl⟩ : syracuseStep 4031309 = 1511741) B1511741
theorem B7177187 : Blo 838352 7177187 := bstep (se 1 (by rfl) ⟨5382890, by rfl⟩ : syracuseStep 7177187 = 10765781) B10765781
theorem B46040177 : Blo 838352 46040177 := bstep (se 2 (by rfl) ⟨17265066, by rfl⟩ : syracuseStep 46040177 = 34530133) B34530133
theorem B3409073 : Blo 838352 3409073 := bstep (se 2 (by rfl) ⟨1278402, by rfl⟩ : syracuseStep 3409073 = 2556805) B2556805
theorem B2393297 : Blo 838352 2393297 := bstep (se 2 (by rfl) ⟨897486, by rfl⟩ : syracuseStep 2393297 = 1794973) B1794973
theorem B1279235 : Blo 838352 1279235 := bstep (se 1 (by rfl) ⟨959426, by rfl⟩ : syracuseStep 1279235 = 1918853) B1918853
theorem B2458925 : Blo 838352 2458925 := bstep (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) B922097
theorem B5375281 : Blo 838352 5375281 := bstep (se 2 (by rfl) ⟨2015730, by rfl⟩ : syracuseStep 5375281 = 4031461) B4031461
theorem B1279283 : Blo 838352 1279283 := bstep (se 1 (by rfl) ⟨959462, by rfl⟩ : syracuseStep 1279283 = 1918925) B1918925
theorem B1344865 : Blo 838352 1344865 := bstep (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) B1008649
theorem B2393489 : Blo 838352 2393489 := bstep (se 2 (by rfl) ⟨897558, by rfl⟩ : syracuseStep 2393489 = 1795117) B1795117
theorem B2688461 : Blo 838352 2688461 := bstep (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) B1008173
theorem B2131505 : Blo 838352 2131505 := bstep (se 2 (by rfl) ⟨799314, by rfl⟩ : syracuseStep 2131505 = 1598629) B1598629
theorem B2131555 : Blo 838352 2131555 := bstep (se 1 (by rfl) ⟨1598666, by rfl⟩ : syracuseStep 2131555 = 3197333) B3197333
theorem B2131697 : Blo 838352 2131697 := bstep (se 2 (by rfl) ⟨799386, by rfl⟩ : syracuseStep 2131697 = 1598773) B1598773
theorem B1345313 : Blo 838352 1345313 := bstep (se 2 (by rfl) ⟨504492, by rfl⟩ : syracuseStep 1345313 = 1008985) B1008985
theorem B1280305 : Blo 838352 1280305 := bstep (se 2 (by rfl) ⟨480114, by rfl⟩ : syracuseStep 1280305 = 960229) B960229
theorem B2394481 : Blo 838352 2394481 := bstep (se 2 (by rfl) ⟨897930, by rfl⟩ : syracuseStep 2394481 = 1795861) B1795861
theorem B3836429 : Blo 838352 3836429 := bstep (se 3 (by rfl) ⟨719330, by rfl⟩ : syracuseStep 3836429 = 1438661) B1438661
theorem B2394755 : Blo 838352 2394755 := bstep (se 1 (by rfl) ⟨1796066, by rfl⟩ : syracuseStep 2394755 = 3592133) B3592133
theorem B1149697 : Blo 838352 1149697 := bstep (se 2 (by rfl) ⟨431136, by rfl⟩ : syracuseStep 1149697 = 862273) B862273
theorem B2689805 : Blo 838352 2689805 := bstep (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) B1008677
theorem B4262705 : Blo 838352 4262705 := bstep (se 2 (by rfl) ⟨1598514, by rfl⟩ : syracuseStep 4262705 = 3197029) B3197029
theorem B2394947 : Blo 838352 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B1313633 : Blo 838352 1313633 := bstep (se 2 (by rfl) ⟨492612, by rfl⟩ : syracuseStep 1313633 = 985225) B985225
theorem B1346723 : Blo 838352 1346723 := bstep (se 1 (by rfl) ⟨1010042, by rfl⟩ : syracuseStep 1346723 = 2020085) B2020085
theorem B2690243 : Blo 838352 2690243 := bstep (se 1 (by rfl) ⟨2017682, by rfl⟩ : syracuseStep 2690243 = 4035365) B4035365
theorem B4787525 : Blo 838352 4787525 := bstep (se 4 (by rfl) ⟨448830, by rfl⟩ : syracuseStep 4787525 = 897661) B897661
theorem B1346915 : Blo 838352 1346915 := bstep (se 1 (by rfl) ⟨1010186, by rfl⟩ : syracuseStep 1346915 = 2020373) B2020373
theorem B1510883 : Blo 838352 1510883 := bstep (se 1 (by rfl) ⟨1133162, by rfl⟩ : syracuseStep 1510883 = 2266325) B2266325
theorem B6393329 : Blo 838352 6393329 := bstep (se 2 (by rfl) ⟨2397498, by rfl⟩ : syracuseStep 6393329 = 4794997) B4794997
theorem B2395757 : Blo 838352 2395757 := bstep (se 3 (by rfl) ⟨449204, by rfl⟩ : syracuseStep 2395757 = 898409) B898409
theorem B2559725 : Blo 838352 2559725 := bstep (se 3 (by rfl) ⟨479948, by rfl⟩ : syracuseStep 2559725 = 959897) B959897
theorem B4787981 : Blo 838352 4787981 := bstep (se 3 (by rfl) ⟨897746, by rfl⟩ : syracuseStep 4787981 = 1795493) B1795493
theorem B2395939 : Blo 838352 2395939 := bstep (se 1 (by rfl) ⟨1796954, by rfl⟩ : syracuseStep 2395939 = 3593909) B3593909
theorem B2723725 : Blo 838352 2723725 := bstep (se 3 (by rfl) ⟨510698, by rfl⟩ : syracuseStep 2723725 = 1021397) B1021397
theorem B4264163 : Blo 838352 4264163 := bstep (se 1 (by rfl) ⟨3198122, by rfl⟩ : syracuseStep 4264163 = 6396245) B6396245
theorem B2396429 : Blo 838352 2396429 := bstep (se 3 (by rfl) ⟨449330, by rfl⟩ : syracuseStep 2396429 = 898661) B898661
theorem B3117581 : Blo 838352 3117581 := bstep (se 3 (by rfl) ⟨584546, by rfl⟩ : syracuseStep 3117581 = 1169093) B1169093
theorem B1348337 : Blo 838352 1348337 := bstep (se 2 (by rfl) ⟨505626, by rfl⟩ : syracuseStep 1348337 = 1011253) B1011253
theorem B1512497 : Blo 838352 1512497 := bstep (se 2 (by rfl) ⟨567186, by rfl⟩ : syracuseStep 1512497 = 1134373) B1134373
theorem B2692163 : Blo 838352 2692163 := bstep (se 1 (by rfl) ⟨2019122, by rfl⟩ : syracuseStep 2692163 = 4038245) B4038245
theorem B14324849 : Blo 838352 14324849 := bstep (se 2 (by rfl) ⟨5371818, by rfl⟩ : syracuseStep 14324849 = 10743637) B10743637
theorem B2364547 : Blo 838352 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B61412579 : Blo 838352 61412579 := bstep (se 1 (by rfl) ⟨46059434, by rfl⟩ : syracuseStep 61412579 = 92118869) B92118869
theorem B3183907 : Blo 838352 3183907 := bstep (se 1 (by rfl) ⟨2387930, by rfl⟩ : syracuseStep 3183907 = 4775861) B4775861
theorem B2397613 : Blo 838352 2397613 := bstep (se 3 (by rfl) ⟨449552, by rfl⟩ : syracuseStep 2397613 = 899105) B899105
theorem B4855301 : Blo 838352 4855301 := bstep (se 4 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 4855301 = 910369) B910369
theorem B1414739 : Blo 838352 1414739 := bstep (se 1 (by rfl) ⟨1061054, by rfl⟩ : syracuseStep 1414739 = 2122109) B2122109
theorem B5117573 : Blo 838352 5117573 := bstep (se 4 (by rfl) ⟨479772, by rfl⟩ : syracuseStep 5117573 = 959545) B959545
theorem B12916421 : Blo 838352 12916421 := bstep (se 4 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 12916421 = 2421829) B2421829
theorem B1414867 : Blo 838352 1414867 := bstep (se 1 (by rfl) ⟨1061150, by rfl⟩ : syracuseStep 1414867 = 2122301) B2122301
theorem B45913877 : Blo 838352 45913877 := bstep (se 6 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 45913877 = 2152213) B2152213
theorem B1415009 : Blo 838352 1415009 := bstep (se 2 (by rfl) ⟨530628, by rfl⟩ : syracuseStep 1415009 = 1061257) B1061257
theorem B3413873 : Blo 838352 3413873 := bstep (se 2 (by rfl) ⟨1280202, by rfl⟩ : syracuseStep 3413873 = 2560405) B2560405
theorem B1415137 : Blo 838352 1415137 := bstep (se 2 (by rfl) ⟨530676, by rfl⟩ : syracuseStep 1415137 = 1061353) B1061353
theorem B1415171 : Blo 838352 1415171 := bstep (se 1 (by rfl) ⟨1061378, by rfl⟩ : syracuseStep 1415171 = 2122757) B2122757
theorem B1513507 : Blo 838352 1513507 := bstep (se 1 (by rfl) ⟨1135130, by rfl⟩ : syracuseStep 1513507 = 2270261) B2270261
theorem B2431043 : Blo 838352 2431043 := bstep (se 1 (by rfl) ⟨1823282, by rfl⟩ : syracuseStep 2431043 = 3646565) B3646565
theorem B1415299 : Blo 838352 1415299 := bstep (se 1 (by rfl) ⟨1061474, by rfl⟩ : syracuseStep 1415299 = 2122949) B2122949
theorem B1415441 : Blo 838352 1415441 := bstep (se 2 (by rfl) ⟨530790, by rfl⟩ : syracuseStep 1415441 = 1061581) B1061581
theorem B1415569 : Blo 838352 1415569 := bstep (se 2 (by rfl) ⟨530838, by rfl⟩ : syracuseStep 1415569 = 1061677) B1061677
theorem B1415603 : Blo 838352 1415603 := bstep (se 1 (by rfl) ⟨1061702, by rfl⟩ : syracuseStep 1415603 = 2123405) B2123405
theorem B2398673 : Blo 838352 2398673 := bstep (se 2 (by rfl) ⟨899502, by rfl⟩ : syracuseStep 2398673 = 1799005) B1799005
theorem B2103779 : Blo 838352 2103779 := bstep (se 1 (by rfl) ⟨1577834, by rfl⟩ : syracuseStep 2103779 = 3155669) B3155669
theorem B5380613 : Blo 838352 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B1415731 : Blo 838352 1415731 := bstep (se 1 (by rfl) ⟨1061798, by rfl⟩ : syracuseStep 1415731 = 2123597) B2123597
theorem B4790897 : Blo 838352 4790897 := bstep (se 2 (by rfl) ⟨1796586, by rfl⟩ : syracuseStep 4790897 = 3593173) B3593173
theorem B1415873 : Blo 838352 1415873 := bstep (se 2 (by rfl) ⟨530952, by rfl⟩ : syracuseStep 1415873 = 1061905) B1061905
theorem B1416001 : Blo 838352 1416001 := bstep (se 2 (by rfl) ⟨531000, by rfl⟩ : syracuseStep 1416001 = 1062001) B1062001
theorem B1416035 : Blo 838352 1416035 := bstep (se 1 (by rfl) ⟨1062026, by rfl⟩ : syracuseStep 1416035 = 2124053) B2124053
theorem B1416163 : Blo 838352 1416163 := bstep (se 1 (by rfl) ⟨1062122, by rfl⟩ : syracuseStep 1416163 = 2124245) B2124245
theorem B1416305 : Blo 838352 1416305 := bstep (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) B1062229
theorem B29072611 : Blo 838352 29072611 := bstep (se 1 (by rfl) ⟨21804458, by rfl⟩ : syracuseStep 29072611 = 43608917) B43608917
theorem B1416433 : Blo 838352 1416433 := bstep (se 2 (by rfl) ⟨531162, by rfl⟩ : syracuseStep 1416433 = 1062325) B1062325
theorem B1416467 : Blo 838352 1416467 := bstep (se 1 (by rfl) ⟨1062350, by rfl⟩ : syracuseStep 1416467 = 2124701) B2124701
theorem B1023331 : Blo 838352 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B1416595 : Blo 838352 1416595 := bstep (se 1 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 1416595 = 2124893) B2124893
theorem B3186125 : Blo 838352 3186125 := bstep (se 3 (by rfl) ⟨597398, by rfl⟩ : syracuseStep 3186125 = 1194797) B1194797
theorem B1416737 : Blo 838352 1416737 := bstep (se 2 (by rfl) ⟨531276, by rfl⟩ : syracuseStep 1416737 = 1062553) B1062553
theorem B1416865 : Blo 838352 1416865 := bstep (se 2 (by rfl) ⟨531324, by rfl⟩ : syracuseStep 1416865 = 1062649) B1062649
theorem B2694829 : Blo 838352 2694829 := bstep (se 3 (by rfl) ⟨505280, by rfl⟩ : syracuseStep 2694829 = 1010561) B1010561
theorem B1416899 : Blo 838352 1416899 := bstep (se 1 (by rfl) ⟨1062674, by rfl⟩ : syracuseStep 1416899 = 2125349) B2125349
theorem B1417027 : Blo 838352 1417027 := bstep (se 1 (by rfl) ⟨1062770, by rfl⟩ : syracuseStep 1417027 = 2125541) B2125541
theorem B1515395 : Blo 838352 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B5742541 : Blo 838352 5742541 := bstep (se 3 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 5742541 = 2153453) B2153453
theorem B1417169 : Blo 838352 1417169 := bstep (se 2 (by rfl) ⟨531438, by rfl⟩ : syracuseStep 1417169 = 1062877) B1062877
theorem B4792355 : Blo 838352 4792355 := bstep (se 1 (by rfl) ⟨3594266, by rfl⟩ : syracuseStep 4792355 = 7188533) B7188533
theorem B1417297 : Blo 838352 1417297 := bstep (se 2 (by rfl) ⟨531486, by rfl⟩ : syracuseStep 1417297 = 1062973) B1062973
theorem B34480241 : Blo 838352 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B1417331 : Blo 838352 1417331 := bstep (se 1 (by rfl) ⟨1062998, by rfl⟩ : syracuseStep 1417331 = 2125997) B2125997
theorem B1417459 : Blo 838352 1417459 := bstep (se 1 (by rfl) ⟨1063094, by rfl⟩ : syracuseStep 1417459 = 2126189) B2126189
theorem B1417601 : Blo 838352 1417601 := bstep (se 2 (by rfl) ⟨531600, by rfl⟩ : syracuseStep 1417601 = 1063201) B1063201
theorem B10789361 : Blo 838352 10789361 := bstep (se 2 (by rfl) ⟨4046010, by rfl⟩ : syracuseStep 10789361 = 8092021) B8092021
theorem B1417729 : Blo 838352 1417729 := bstep (se 2 (by rfl) ⟨531648, by rfl⟩ : syracuseStep 1417729 = 1063297) B1063297
theorem B1417763 : Blo 838352 1417763 := bstep (se 1 (by rfl) ⟨1063322, by rfl⟩ : syracuseStep 1417763 = 2126645) B2126645
theorem B10199621 : Blo 838352 10199621 := bstep (se 4 (by rfl) ⟨956214, by rfl⟩ : syracuseStep 10199621 = 1912429) B1912429
theorem B1417891 : Blo 838352 1417891 := bstep (se 1 (by rfl) ⟨1063418, by rfl⟩ : syracuseStep 1417891 = 2126837) B2126837
theorem B1418033 : Blo 838352 1418033 := bstep (se 2 (by rfl) ⟨531762, by rfl⟩ : syracuseStep 1418033 = 1063525) B1063525
theorem B1418161 : Blo 838352 1418161 := bstep (se 2 (by rfl) ⟨531810, by rfl⟩ : syracuseStep 1418161 = 1063621) B1063621
theorem B1418195 : Blo 838352 1418195 := bstep (se 1 (by rfl) ⟨1063646, by rfl⟩ : syracuseStep 1418195 = 2127293) B2127293
theorem B4793357 : Blo 838352 4793357 := bstep (se 3 (by rfl) ⟨898754, by rfl⟩ : syracuseStep 4793357 = 1797509) B1797509
theorem B1418323 : Blo 838352 1418323 := bstep (se 1 (by rfl) ⟨1063742, by rfl⟩ : syracuseStep 1418323 = 2127485) B2127485
theorem B2696291 : Blo 838352 2696291 := bstep (se 1 (by rfl) ⟨2022218, by rfl⟩ : syracuseStep 2696291 = 4044437) B4044437
theorem B1418465 : Blo 838352 1418465 := bstep (se 2 (by rfl) ⟨531924, by rfl⟩ : syracuseStep 1418465 = 1063849) B1063849
theorem B1418593 : Blo 838352 1418593 := bstep (se 2 (by rfl) ⟨531972, by rfl⟩ : syracuseStep 1418593 = 1063945) B1063945
theorem B2696561 : Blo 838352 2696561 := bstep (se 2 (by rfl) ⟨1011210, by rfl⟩ : syracuseStep 2696561 = 2022421) B2022421
theorem B1418627 : Blo 838352 1418627 := bstep (se 1 (by rfl) ⟨1063970, by rfl⟩ : syracuseStep 1418627 = 2127941) B2127941
theorem B1418755 : Blo 838352 1418755 := bstep (se 1 (by rfl) ⟨1064066, by rfl⟩ : syracuseStep 1418755 = 2128133) B2128133
theorem B1418897 : Blo 838352 1418897 := bstep (se 2 (by rfl) ⟨532086, by rfl⟩ : syracuseStep 1418897 = 1064173) B1064173
theorem B1615555 : Blo 838352 1615555 := bstep (se 1 (by rfl) ⟨1211666, by rfl⟩ : syracuseStep 1615555 = 2423333) B2423333
theorem B1419025 : Blo 838352 1419025 := bstep (se 2 (by rfl) ⟨532134, by rfl⟩ : syracuseStep 1419025 = 1064269) B1064269
theorem B1419059 : Blo 838352 1419059 := bstep (se 1 (by rfl) ⟨1064294, by rfl⟩ : syracuseStep 1419059 = 2128589) B2128589
theorem B1419187 : Blo 838352 1419187 := bstep (se 1 (by rfl) ⟨1064390, by rfl⟩ : syracuseStep 1419187 = 2128781) B2128781
theorem B8071109 : Blo 838352 8071109 := bstep (se 4 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 8071109 = 1513333) B1513333
theorem B9086917 : Blo 838352 9086917 := bstep (se 4 (by rfl) ⟨851898, by rfl⟩ : syracuseStep 9086917 = 1703797) B1703797
theorem B1419329 : Blo 838352 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B2271331 : Blo 838352 2271331 := bstep (se 1 (by rfl) ⟨1703498, by rfl⟩ : syracuseStep 2271331 = 3406997) B3406997
theorem B1419457 : Blo 838352 1419457 := bstep (se 2 (by rfl) ⟨532296, by rfl⟩ : syracuseStep 1419457 = 1064593) B1064593
theorem B1419491 : Blo 838352 1419491 := bstep (se 1 (by rfl) ⟨1064618, by rfl⟩ : syracuseStep 1419491 = 2129237) B2129237
theorem B5449997 : Blo 838352 5449997 := bstep (se 3 (by rfl) ⟨1021874, by rfl⟩ : syracuseStep 5449997 = 2043749) B2043749
theorem B3189041 : Blo 838352 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B1419619 : Blo 838352 1419619 := bstep (se 1 (by rfl) ⟨1064714, by rfl⟩ : syracuseStep 1419619 = 2129429) B2129429
theorem B18196933 : Blo 838352 18196933 := bstep (se 4 (by rfl) ⟨1705962, by rfl⟩ : syracuseStep 18196933 = 3411925) B3411925
theorem B10201571 : Blo 838352 10201571 := bstep (se 1 (by rfl) ⟨7651178, by rfl⟩ : syracuseStep 10201571 = 15302357) B15302357
theorem B1419761 : Blo 838352 1419761 := bstep (se 2 (by rfl) ⟨532410, by rfl⟩ : syracuseStep 1419761 = 1064821) B1064821
theorem B3025457 : Blo 838352 3025457 := bstep (se 2 (by rfl) ⟨1134546, by rfl⟩ : syracuseStep 3025457 = 2269093) B2269093
theorem B1944145 : Blo 838352 1944145 := bstep (se 2 (by rfl) ⟨729054, by rfl⟩ : syracuseStep 1944145 = 1458109) B1458109
theorem B1419889 : Blo 838352 1419889 := bstep (se 2 (by rfl) ⟨532458, by rfl⟩ : syracuseStep 1419889 = 1064917) B1064917
theorem B1419923 : Blo 838352 1419923 := bstep (se 1 (by rfl) ⟨1064942, by rfl⟩ : syracuseStep 1419923 = 2129885) B2129885
theorem B1420051 : Blo 838352 1420051 := bstep (se 1 (by rfl) ⟨1065038, by rfl⟩ : syracuseStep 1420051 = 2130077) B2130077
theorem B21506957 : Blo 838352 21506957 := bstep (se 3 (by rfl) ⟨4032554, by rfl⟩ : syracuseStep 21506957 = 8065109) B8065109
theorem B1420193 : Blo 838352 1420193 := bstep (se 2 (by rfl) ⟨532572, by rfl⟩ : syracuseStep 1420193 = 1065145) B1065145
theorem B1420321 : Blo 838352 1420321 := bstep (se 2 (by rfl) ⟨532620, by rfl⟩ : syracuseStep 1420321 = 1065241) B1065241
theorem B3583025 : Blo 838352 3583025 := bstep (se 2 (by rfl) ⟨1343634, by rfl⟩ : syracuseStep 3583025 = 2687269) B2687269
theorem B1420355 : Blo 838352 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B1420483 : Blo 838352 1420483 := bstep (se 1 (by rfl) ⟨1065362, by rfl⟩ : syracuseStep 1420483 = 2130725) B2130725
theorem B896243 : Blo 838352 896243 := bstep (se 1 (by rfl) ⟨672182, by rfl⟩ : syracuseStep 896243 = 1344365) B1344365
theorem B1420625 : Blo 838352 1420625 := bstep (se 2 (by rfl) ⟨532734, by rfl⟩ : syracuseStep 1420625 = 1065469) B1065469
theorem B1420753 : Blo 838352 1420753 := bstep (se 2 (by rfl) ⟨532782, by rfl⟩ : syracuseStep 1420753 = 1065565) B1065565
theorem B1420787 : Blo 838352 1420787 := bstep (se 1 (by rfl) ⟨1065590, by rfl⟩ : syracuseStep 1420787 = 2131181) B2131181
theorem B2829869 : Blo 838352 2829869 := bstep (se 3 (by rfl) ⟨530600, by rfl⟩ : syracuseStep 2829869 = 1061201) B1061201
theorem B2829923 : Blo 838352 2829923 := bstep (se 1 (by rfl) ⟨2122442, by rfl⟩ : syracuseStep 2829923 = 4244885) B4244885
theorem B1420915 : Blo 838352 1420915 := bstep (se 1 (by rfl) ⟨1065686, by rfl⟩ : syracuseStep 1420915 = 2131373) B2131373
theorem B3190499 : Blo 838352 3190499 := bstep (se 1 (by rfl) ⟨2392874, by rfl⟩ : syracuseStep 3190499 = 4785749) B4785749
theorem B1421057 : Blo 838352 1421057 := bstep (se 2 (by rfl) ⟨532896, by rfl⟩ : syracuseStep 1421057 = 1065793) B1065793
theorem B2830193 : Blo 838352 2830193 := bstep (se 2 (by rfl) ⟨1061322, by rfl⟩ : syracuseStep 2830193 = 2122645) B2122645
theorem B4599665 : Blo 838352 4599665 := bstep (se 2 (by rfl) ⟨1724874, by rfl⟩ : syracuseStep 4599665 = 3449749) B3449749
theorem B4796273 : Blo 838352 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B1421185 : Blo 838352 1421185 := bstep (se 2 (by rfl) ⟨532944, by rfl⟩ : syracuseStep 1421185 = 1065889) B1065889
theorem B1421219 : Blo 838352 1421219 := bstep (se 1 (by rfl) ⟨1065914, by rfl⟩ : syracuseStep 1421219 = 2131829) B2131829
theorem B2273233 : Blo 838352 2273233 := bstep (se 2 (by rfl) ⟨852462, by rfl⟩ : syracuseStep 2273233 = 1704925) B1704925
theorem B896995 : Blo 838352 896995 := bstep (se 1 (by rfl) ⟨672746, by rfl⟩ : syracuseStep 896995 = 1345493) B1345493
theorem B1421347 : Blo 838352 1421347 := bstep (se 1 (by rfl) ⟨1066010, by rfl⟩ : syracuseStep 1421347 = 2132021) B2132021
theorem B1257539 : Blo 838352 1257539 := bstep (se 1 (by rfl) ⟨943154, by rfl⟩ : syracuseStep 1257539 = 1886309) B1886309
theorem B1257569 : Blo 838352 1257569 := bstep (se 2 (by rfl) ⟨471588, by rfl⟩ : syracuseStep 1257569 = 943177) B943177
theorem B1257587 : Blo 838352 1257587 := bstep (se 1 (by rfl) ⟨943190, by rfl⟩ : syracuseStep 1257587 = 1886381) B1886381
theorem B9089165 : Blo 838352 9089165 := bstep (se 3 (by rfl) ⟨1704218, by rfl⟩ : syracuseStep 9089165 = 3408437) B3408437
theorem B1257617 : Blo 838352 1257617 := bstep (se 2 (by rfl) ⟨471606, by rfl⟩ : syracuseStep 1257617 = 943213) B943213
theorem B1257635 : Blo 838352 1257635 := bstep (se 1 (by rfl) ⟨943226, by rfl⟩ : syracuseStep 1257635 = 1886453) B1886453
theorem B1257665 : Blo 838352 1257665 := bstep (se 2 (by rfl) ⟨471624, by rfl⟩ : syracuseStep 1257665 = 943249) B943249
theorem B1257683 : Blo 838352 1257683 := bstep (se 1 (by rfl) ⟨943262, by rfl⟩ : syracuseStep 1257683 = 1886525) B1886525
theorem B897251 : Blo 838352 897251 := bstep (se 1 (by rfl) ⟨672938, by rfl⟩ : syracuseStep 897251 = 1345877) B1345877
theorem B1257713 : Blo 838352 1257713 := bstep (se 2 (by rfl) ⟨471642, by rfl⟩ : syracuseStep 1257713 = 943285) B943285
theorem B3027185 : Blo 838352 3027185 := bstep (se 2 (by rfl) ⟨1135194, by rfl⟩ : syracuseStep 3027185 = 2270389) B2270389
theorem B1257731 : Blo 838352 1257731 := bstep (se 1 (by rfl) ⟨943298, by rfl⟩ : syracuseStep 1257731 = 1886597) B1886597
theorem B1257761 : Blo 838352 1257761 := bstep (se 2 (by rfl) ⟨471660, by rfl⟩ : syracuseStep 1257761 = 943321) B943321
theorem B1257779 : Blo 838352 1257779 := bstep (se 1 (by rfl) ⟨943334, by rfl⟩ : syracuseStep 1257779 = 1886669) B1886669
theorem B1257809 : Blo 838352 1257809 := bstep (se 2 (by rfl) ⟨471678, by rfl⟩ : syracuseStep 1257809 = 943357) B943357
theorem B1257827 : Blo 838352 1257827 := bstep (se 1 (by rfl) ⟨943370, by rfl⟩ : syracuseStep 1257827 = 1886741) B1886741
theorem B1257857 : Blo 838352 1257857 := bstep (se 2 (by rfl) ⟨471696, by rfl⟩ : syracuseStep 1257857 = 943393) B943393
theorem B2830733 : Blo 838352 2830733 := bstep (se 3 (by rfl) ⟨530762, by rfl⟩ : syracuseStep 2830733 = 1061525) B1061525
theorem B1257875 : Blo 838352 1257875 := bstep (se 1 (by rfl) ⟨943406, by rfl⟩ : syracuseStep 1257875 = 1886813) B1886813
theorem B1257905 : Blo 838352 1257905 := bstep (se 2 (by rfl) ⟨471714, by rfl⟩ : syracuseStep 1257905 = 943429) B943429
theorem B1257923 : Blo 838352 1257923 := bstep (se 1 (by rfl) ⟨943442, by rfl⟩ : syracuseStep 1257923 = 1886885) B1886885
theorem B2830787 : Blo 838352 2830787 := bstep (se 1 (by rfl) ⟨2123090, by rfl⟩ : syracuseStep 2830787 = 4246181) B4246181
theorem B1257953 : Blo 838352 1257953 := bstep (se 2 (by rfl) ⟨471732, by rfl⟩ : syracuseStep 1257953 = 943465) B943465
theorem B1061363 : Blo 838352 1061363 := bstep (se 1 (by rfl) ⟨796022, by rfl⟩ : syracuseStep 1061363 = 1592045) B1592045
theorem B1257971 : Blo 838352 1257971 := bstep (se 1 (by rfl) ⟨943478, by rfl⟩ : syracuseStep 1257971 = 1886957) B1886957
theorem B1258001 : Blo 838352 1258001 := bstep (se 2 (by rfl) ⟨471750, by rfl⟩ : syracuseStep 1258001 = 943501) B943501
theorem B1258019 : Blo 838352 1258019 := bstep (se 1 (by rfl) ⟨943514, by rfl⟩ : syracuseStep 1258019 = 1887029) B1887029
theorem B5386787 : Blo 838352 5386787 := bstep (se 1 (by rfl) ⟨4040090, by rfl⟩ : syracuseStep 5386787 = 8080181) B8080181
theorem B1258049 : Blo 838352 1258049 := bstep (se 2 (by rfl) ⟨471768, by rfl⟩ : syracuseStep 1258049 = 943537) B943537
theorem B1258067 : Blo 838352 1258067 := bstep (se 1 (by rfl) ⟨943550, by rfl⟩ : syracuseStep 1258067 = 1887101) B1887101
theorem B1258097 : Blo 838352 1258097 := bstep (se 2 (by rfl) ⟨471786, by rfl⟩ : syracuseStep 1258097 = 943573) B943573
theorem B1258115 : Blo 838352 1258115 := bstep (se 1 (by rfl) ⟨943586, by rfl⟩ : syracuseStep 1258115 = 1887173) B1887173
theorem B1258145 : Blo 838352 1258145 := bstep (se 2 (by rfl) ⟨471804, by rfl⟩ : syracuseStep 1258145 = 943609) B943609
theorem B1258163 : Blo 838352 1258163 := bstep (se 1 (by rfl) ⟨943622, by rfl⟩ : syracuseStep 1258163 = 1887245) B1887245
theorem B3191501 : Blo 838352 3191501 := bstep (se 3 (by rfl) ⟨598406, by rfl⟩ : syracuseStep 3191501 = 1196813) B1196813
theorem B1258193 : Blo 838352 1258193 := bstep (se 2 (by rfl) ⟨471822, by rfl⟩ : syracuseStep 1258193 = 943645) B943645
theorem B2831057 : Blo 838352 2831057 := bstep (se 2 (by rfl) ⟨1061646, by rfl⟩ : syracuseStep 2831057 = 2123293) B2123293
theorem B1258211 : Blo 838352 1258211 := bstep (se 1 (by rfl) ⟨943658, by rfl⟩ : syracuseStep 1258211 = 1887317) B1887317
theorem B1258241 : Blo 838352 1258241 := bstep (se 2 (by rfl) ⟨471840, by rfl⟩ : syracuseStep 1258241 = 943681) B943681
theorem B1258259 : Blo 838352 1258259 := bstep (se 1 (by rfl) ⟨943694, by rfl⟩ : syracuseStep 1258259 = 1887389) B1887389
theorem B1258289 : Blo 838352 1258289 := bstep (se 2 (by rfl) ⟨471858, by rfl⟩ : syracuseStep 1258289 = 943717) B943717
theorem B1258307 : Blo 838352 1258307 := bstep (se 1 (by rfl) ⟨943730, by rfl⟩ : syracuseStep 1258307 = 1887461) B1887461
theorem B1258337 : Blo 838352 1258337 := bstep (se 2 (by rfl) ⟨471876, by rfl⟩ : syracuseStep 1258337 = 943753) B943753
theorem B1618787 : Blo 838352 1618787 := bstep (se 1 (by rfl) ⟨1214090, by rfl⟩ : syracuseStep 1618787 = 2428181) B2428181
theorem B1258355 : Blo 838352 1258355 := bstep (se 1 (by rfl) ⟨943766, by rfl⟩ : syracuseStep 1258355 = 1887533) B1887533
theorem B1258385 : Blo 838352 1258385 := bstep (se 2 (by rfl) ⟨471894, by rfl⟩ : syracuseStep 1258385 = 943789) B943789
theorem B1258403 : Blo 838352 1258403 := bstep (se 1 (by rfl) ⟨943802, by rfl⟩ : syracuseStep 1258403 = 1887605) B1887605
theorem B1258433 : Blo 838352 1258433 := bstep (se 2 (by rfl) ⟨471912, by rfl⟩ : syracuseStep 1258433 = 943825) B943825
theorem B898003 : Blo 838352 898003 := bstep (se 1 (by rfl) ⟨673502, by rfl⟩ : syracuseStep 898003 = 1347005) B1347005
theorem B1258451 : Blo 838352 1258451 := bstep (se 1 (by rfl) ⟨943838, by rfl⟩ : syracuseStep 1258451 = 1887677) B1887677
theorem B16135139 : Blo 838352 16135139 := bstep (se 1 (by rfl) ⟨12101354, by rfl⟩ : syracuseStep 16135139 = 24202709) B24202709
theorem B1258481 : Blo 838352 1258481 := bstep (se 2 (by rfl) ⟨471930, by rfl⟩ : syracuseStep 1258481 = 943861) B943861
theorem B5387249 : Blo 838352 5387249 := bstep (se 2 (by rfl) ⟨2020218, by rfl⟩ : syracuseStep 5387249 = 4040437) B4040437
theorem B1258499 : Blo 838352 1258499 := bstep (se 1 (by rfl) ⟨943874, by rfl⟩ : syracuseStep 1258499 = 1887749) B1887749
theorem B1258529 : Blo 838352 1258529 := bstep (se 2 (by rfl) ⟨471948, by rfl⟩ : syracuseStep 1258529 = 943897) B943897
theorem B1258547 : Blo 838352 1258547 := bstep (se 1 (by rfl) ⟨943910, by rfl⟩ : syracuseStep 1258547 = 1887821) B1887821
theorem B9679925 : Blo 838352 9679925 := bstep (se 5 (by rfl) ⟨453746, by rfl⟩ : syracuseStep 9679925 = 907493) B907493
theorem B1258577 : Blo 838352 1258577 := bstep (se 2 (by rfl) ⟨471966, by rfl⟩ : syracuseStep 1258577 = 943933) B943933
theorem B1258595 : Blo 838352 1258595 := bstep (se 1 (by rfl) ⟨943946, by rfl⟩ : syracuseStep 1258595 = 1887893) B1887893
theorem B1258625 : Blo 838352 1258625 := bstep (se 2 (by rfl) ⟨471984, by rfl⟩ : syracuseStep 1258625 = 943969) B943969
theorem B1946755 : Blo 838352 1946755 := bstep (se 1 (by rfl) ⟨1460066, by rfl⟩ : syracuseStep 1946755 = 2920133) B2920133
theorem B1258643 : Blo 838352 1258643 := bstep (se 1 (by rfl) ⟨943982, by rfl⟩ : syracuseStep 1258643 = 1887965) B1887965
theorem B1258673 : Blo 838352 1258673 := bstep (se 2 (by rfl) ⟨472002, by rfl⟩ : syracuseStep 1258673 = 944005) B944005
theorem B1062067 : Blo 838352 1062067 := bstep (se 1 (by rfl) ⟨796550, by rfl⟩ : syracuseStep 1062067 = 1593101) B1593101
theorem B1258691 : Blo 838352 1258691 := bstep (se 1 (by rfl) ⟨944018, by rfl⟩ : syracuseStep 1258691 = 1888037) B1888037
theorem B1258721 : Blo 838352 1258721 := bstep (se 2 (by rfl) ⟨472020, by rfl⟩ : syracuseStep 1258721 = 944041) B944041
theorem B2831597 : Blo 838352 2831597 := bstep (se 3 (by rfl) ⟨530924, by rfl⟩ : syracuseStep 2831597 = 1061849) B1061849
theorem B1258739 : Blo 838352 1258739 := bstep (se 1 (by rfl) ⟨944054, by rfl⟩ : syracuseStep 1258739 = 1888109) B1888109
theorem B1258769 : Blo 838352 1258769 := bstep (se 2 (by rfl) ⟨472038, by rfl⟩ : syracuseStep 1258769 = 944077) B944077
theorem B1062163 : Blo 838352 1062163 := bstep (se 1 (by rfl) ⟨796622, by rfl⟩ : syracuseStep 1062163 = 1593245) B1593245
theorem B2831651 : Blo 838352 2831651 := bstep (se 1 (by rfl) ⟨2123738, by rfl⟩ : syracuseStep 2831651 = 4247477) B4247477
theorem B1258787 : Blo 838352 1258787 := bstep (se 1 (by rfl) ⟨944090, by rfl⟩ : syracuseStep 1258787 = 1888181) B1888181
theorem B1258817 : Blo 838352 1258817 := bstep (se 2 (by rfl) ⟨472056, by rfl⟩ : syracuseStep 1258817 = 944113) B944113
theorem B1258835 : Blo 838352 1258835 := bstep (se 1 (by rfl) ⟨944126, by rfl⟩ : syracuseStep 1258835 = 1888253) B1888253
theorem B1258865 : Blo 838352 1258865 := bstep (se 2 (by rfl) ⟨472074, by rfl⟩ : syracuseStep 1258865 = 944149) B944149
theorem B1258883 : Blo 838352 1258883 := bstep (se 1 (by rfl) ⟨944162, by rfl⟩ : syracuseStep 1258883 = 1888325) B1888325
theorem B1258913 : Blo 838352 1258913 := bstep (se 2 (by rfl) ⟨472092, by rfl⟩ : syracuseStep 1258913 = 944185) B944185
theorem B1914275 : Blo 838352 1914275 := bstep (se 1 (by rfl) ⟨1435706, by rfl⟩ : syracuseStep 1914275 = 2871413) B2871413
theorem B1258931 : Blo 838352 1258931 := bstep (se 1 (by rfl) ⟨944198, by rfl⟩ : syracuseStep 1258931 = 1888397) B1888397
theorem B3585485 : Blo 838352 3585485 := bstep (se 3 (by rfl) ⟨672278, by rfl⟩ : syracuseStep 3585485 = 1344557) B1344557
theorem B1258961 : Blo 838352 1258961 := bstep (se 2 (by rfl) ⟨472110, by rfl⟩ : syracuseStep 1258961 = 944221) B944221
theorem B1258979 : Blo 838352 1258979 := bstep (se 1 (by rfl) ⟨944234, by rfl⟩ : syracuseStep 1258979 = 1888469) B1888469
theorem B2045425 : Blo 838352 2045425 := bstep (se 2 (by rfl) ⟨767034, by rfl⟩ : syracuseStep 2045425 = 1534069) B1534069
theorem B1259009 : Blo 838352 1259009 := bstep (se 2 (by rfl) ⟨472128, by rfl⟩ : syracuseStep 1259009 = 944257) B944257
theorem B1259027 : Blo 838352 1259027 := bstep (se 1 (by rfl) ⟨944270, by rfl⟩ : syracuseStep 1259027 = 1888541) B1888541
theorem B2831921 : Blo 838352 2831921 := bstep (se 2 (by rfl) ⟨1061970, by rfl⟩ : syracuseStep 2831921 = 2123941) B2123941
theorem B1259057 : Blo 838352 1259057 := bstep (se 2 (by rfl) ⟨472146, by rfl⟩ : syracuseStep 1259057 = 944293) B944293
theorem B1259075 : Blo 838352 1259075 := bstep (se 1 (by rfl) ⟨944306, by rfl⟩ : syracuseStep 1259075 = 1888613) B1888613
theorem B1259105 : Blo 838352 1259105 := bstep (se 2 (by rfl) ⟨472164, by rfl⟩ : syracuseStep 1259105 = 944329) B944329
theorem B1259123 : Blo 838352 1259123 := bstep (se 1 (by rfl) ⟨944342, by rfl⟩ : syracuseStep 1259123 = 1888685) B1888685
theorem B1259153 : Blo 838352 1259153 := bstep (se 2 (by rfl) ⟨472182, by rfl⟩ : syracuseStep 1259153 = 944365) B944365
theorem B1259171 : Blo 838352 1259171 := bstep (se 1 (by rfl) ⟨944378, by rfl⟩ : syracuseStep 1259171 = 1888757) B1888757
theorem B1259201 : Blo 838352 1259201 := bstep (se 2 (by rfl) ⟨472200, by rfl⟩ : syracuseStep 1259201 = 944401) B944401
theorem B1259219 : Blo 838352 1259219 := bstep (se 1 (by rfl) ⟨944414, by rfl⟩ : syracuseStep 1259219 = 1888829) B1888829
theorem B1259249 : Blo 838352 1259249 := bstep (se 2 (by rfl) ⟨472218, by rfl⟩ : syracuseStep 1259249 = 944437) B944437
theorem B1259267 : Blo 838352 1259267 := bstep (se 1 (by rfl) ⟨944450, by rfl⟩ : syracuseStep 1259267 = 1888901) B1888901
theorem B1062659 : Blo 838352 1062659 := bstep (se 1 (by rfl) ⟨796994, by rfl⟩ : syracuseStep 1062659 = 1593989) B1593989
theorem B1259297 : Blo 838352 1259297 := bstep (se 2 (by rfl) ⟨472236, by rfl⟩ : syracuseStep 1259297 = 944473) B944473
theorem B5748515 : Blo 838352 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B1259315 : Blo 838352 1259315 := bstep (se 1 (by rfl) ⟨944486, by rfl⟩ : syracuseStep 1259315 = 1888973) B1888973
theorem B1259345 : Blo 838352 1259345 := bstep (se 2 (by rfl) ⟨472254, by rfl⟩ : syracuseStep 1259345 = 944509) B944509
theorem B1259363 : Blo 838352 1259363 := bstep (se 1 (by rfl) ⟨944522, by rfl⟩ : syracuseStep 1259363 = 1889045) B1889045
theorem B1259393 : Blo 838352 1259393 := bstep (se 2 (by rfl) ⟨472272, by rfl⟩ : syracuseStep 1259393 = 944545) B944545
theorem B1259411 : Blo 838352 1259411 := bstep (se 1 (by rfl) ⟨944558, by rfl⟩ : syracuseStep 1259411 = 1889117) B1889117
theorem B1259441 : Blo 838352 1259441 := bstep (se 2 (by rfl) ⟨472290, by rfl⟩ : syracuseStep 1259441 = 944581) B944581
theorem B1259459 : Blo 838352 1259459 := bstep (se 1 (by rfl) ⟨944594, by rfl⟩ : syracuseStep 1259459 = 1889189) B1889189
theorem B1259489 : Blo 838352 1259489 := bstep (se 2 (by rfl) ⟨472308, by rfl⟩ : syracuseStep 1259489 = 944617) B944617
theorem B1554403 : Blo 838352 1554403 := bstep (se 1 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 1554403 = 2331605) B2331605
theorem B1259507 : Blo 838352 1259507 := bstep (se 1 (by rfl) ⟨944630, by rfl⟩ : syracuseStep 1259507 = 1889261) B1889261
theorem B1259537 : Blo 838352 1259537 := bstep (se 2 (by rfl) ⟨472326, by rfl⟩ : syracuseStep 1259537 = 944653) B944653
theorem B1259555 : Blo 838352 1259555 := bstep (se 1 (by rfl) ⟨944666, by rfl⟩ : syracuseStep 1259555 = 1889333) B1889333
theorem B1259585 : Blo 838352 1259585 := bstep (se 2 (by rfl) ⟨472344, by rfl⟩ : syracuseStep 1259585 = 944689) B944689
theorem B2832461 : Blo 838352 2832461 := bstep (se 3 (by rfl) ⟨531086, by rfl⟩ : syracuseStep 2832461 = 1062173) B1062173
theorem B1259603 : Blo 838352 1259603 := bstep (se 1 (by rfl) ⟨944702, by rfl⟩ : syracuseStep 1259603 = 1889405) B1889405
theorem B1194097 : Blo 838352 1194097 := bstep (se 2 (by rfl) ⟨447786, by rfl⟩ : syracuseStep 1194097 = 895573) B895573
theorem B1259633 : Blo 838352 1259633 := bstep (se 2 (by rfl) ⟨472362, by rfl⟩ : syracuseStep 1259633 = 944725) B944725
theorem B2832515 : Blo 838352 2832515 := bstep (se 1 (by rfl) ⟨2124386, by rfl⟩ : syracuseStep 2832515 = 4248773) B4248773
theorem B1259651 : Blo 838352 1259651 := bstep (se 1 (by rfl) ⟨944738, by rfl⟩ : syracuseStep 1259651 = 1889477) B1889477
theorem B1259681 : Blo 838352 1259681 := bstep (se 2 (by rfl) ⟨472380, by rfl⟩ : syracuseStep 1259681 = 944761) B944761
theorem B1259699 : Blo 838352 1259699 := bstep (se 1 (by rfl) ⟨944774, by rfl⟩ : syracuseStep 1259699 = 1889549) B1889549
theorem B899267 : Blo 838352 899267 := bstep (se 1 (by rfl) ⟨674450, by rfl⟩ : syracuseStep 899267 = 1348901) B1348901
theorem B1194193 : Blo 838352 1194193 := bstep (se 2 (by rfl) ⟨447822, by rfl⟩ : syracuseStep 1194193 = 895645) B895645
theorem B1259729 : Blo 838352 1259729 := bstep (se 2 (by rfl) ⟨472398, by rfl⟩ : syracuseStep 1259729 = 944797) B944797
theorem B1259747 : Blo 838352 1259747 := bstep (se 1 (by rfl) ⟨944810, by rfl⟩ : syracuseStep 1259747 = 1889621) B1889621
theorem B1259777 : Blo 838352 1259777 := bstep (se 2 (by rfl) ⟨472416, by rfl⟩ : syracuseStep 1259777 = 944833) B944833
theorem B1259795 : Blo 838352 1259795 := bstep (se 1 (by rfl) ⟨944846, by rfl⟩ : syracuseStep 1259795 = 1889693) B1889693
theorem B1259825 : Blo 838352 1259825 := bstep (se 2 (by rfl) ⟨472434, by rfl⟩ : syracuseStep 1259825 = 944869) B944869
theorem B1259843 : Blo 838352 1259843 := bstep (se 1 (by rfl) ⟨944882, by rfl⟩ : syracuseStep 1259843 = 1889765) B1889765
theorem B1259873 : Blo 838352 1259873 := bstep (se 2 (by rfl) ⟨472452, by rfl⟩ : syracuseStep 1259873 = 944905) B944905
theorem B1259891 : Blo 838352 1259891 := bstep (se 1 (by rfl) ⟨944918, by rfl⟩ : syracuseStep 1259891 = 1889837) B1889837
theorem B2832785 : Blo 838352 2832785 := bstep (se 2 (by rfl) ⟨1062294, by rfl⟩ : syracuseStep 2832785 = 2124589) B2124589
theorem B1259921 : Blo 838352 1259921 := bstep (se 2 (by rfl) ⟨472470, by rfl⟩ : syracuseStep 1259921 = 944941) B944941
theorem B1259939 : Blo 838352 1259939 := bstep (se 1 (by rfl) ⟨944954, by rfl⟩ : syracuseStep 1259939 = 1889909) B1889909
theorem B1259969 : Blo 838352 1259969 := bstep (se 2 (by rfl) ⟨472488, by rfl⟩ : syracuseStep 1259969 = 944977) B944977
theorem B1063363 : Blo 838352 1063363 := bstep (se 1 (by rfl) ⟨797522, by rfl⟩ : syracuseStep 1063363 = 1595045) B1595045
theorem B1259987 : Blo 838352 1259987 := bstep (se 1 (by rfl) ⟨944990, by rfl⟩ : syracuseStep 1259987 = 1889981) B1889981
theorem B1260017 : Blo 838352 1260017 := bstep (se 2 (by rfl) ⟨472506, by rfl⟩ : syracuseStep 1260017 = 945013) B945013
theorem B1260035 : Blo 838352 1260035 := bstep (se 1 (by rfl) ⟨945026, by rfl⟩ : syracuseStep 1260035 = 1890053) B1890053
theorem B1260065 : Blo 838352 1260065 := bstep (se 2 (by rfl) ⟨472524, by rfl⟩ : syracuseStep 1260065 = 945049) B945049
theorem B1063459 : Blo 838352 1063459 := bstep (se 1 (by rfl) ⟨797594, by rfl⟩ : syracuseStep 1063459 = 1595189) B1595189
theorem B1260083 : Blo 838352 1260083 := bstep (se 1 (by rfl) ⟨945062, by rfl⟩ : syracuseStep 1260083 = 1890125) B1890125
theorem B1260113 : Blo 838352 1260113 := bstep (se 2 (by rfl) ⟨472542, by rfl⟩ : syracuseStep 1260113 = 945085) B945085
theorem B1260131 : Blo 838352 1260131 := bstep (se 1 (by rfl) ⟨945098, by rfl⟩ : syracuseStep 1260131 = 1890197) B1890197
theorem B1260161 : Blo 838352 1260161 := bstep (se 2 (by rfl) ⟨472560, by rfl⟩ : syracuseStep 1260161 = 945121) B945121
theorem B1260179 : Blo 838352 1260179 := bstep (se 1 (by rfl) ⟨945134, by rfl⟩ : syracuseStep 1260179 = 1890269) B1890269
theorem B1260209 : Blo 838352 1260209 := bstep (se 2 (by rfl) ⟨472578, by rfl⟩ : syracuseStep 1260209 = 945157) B945157
theorem B1194689 : Blo 838352 1194689 := bstep (se 2 (by rfl) ⟨448008, by rfl⟩ : syracuseStep 1194689 = 896017) B896017
theorem B1260227 : Blo 838352 1260227 := bstep (se 1 (by rfl) ⟨945170, by rfl⟩ : syracuseStep 1260227 = 1890341) B1890341
theorem B1260257 : Blo 838352 1260257 := bstep (se 2 (by rfl) ⟨472596, by rfl⟩ : syracuseStep 1260257 = 945193) B945193
theorem B3586801 : Blo 838352 3586801 := bstep (se 2 (by rfl) ⟨1345050, by rfl⟩ : syracuseStep 3586801 = 2690101) B2690101
theorem B1915633 : Blo 838352 1915633 := bstep (se 2 (by rfl) ⟨718362, by rfl⟩ : syracuseStep 1915633 = 1436725) B1436725
theorem B1260275 : Blo 838352 1260275 := bstep (se 1 (by rfl) ⟨945206, by rfl⟩ : syracuseStep 1260275 = 1890413) B1890413
theorem B3193613 : Blo 838352 3193613 := bstep (se 3 (by rfl) ⟨598802, by rfl⟩ : syracuseStep 3193613 = 1197605) B1197605
theorem B1260305 : Blo 838352 1260305 := bstep (se 2 (by rfl) ⟨472614, by rfl⟩ : syracuseStep 1260305 = 945229) B945229
theorem B1260323 : Blo 838352 1260323 := bstep (se 1 (by rfl) ⟨945242, by rfl⟩ : syracuseStep 1260323 = 1890485) B1890485
theorem B1260353 : Blo 838352 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B1260371 : Blo 838352 1260371 := bstep (se 1 (by rfl) ⟨945278, by rfl⟩ : syracuseStep 1260371 = 1890557) B1890557
theorem B1260401 : Blo 838352 1260401 := bstep (se 2 (by rfl) ⟨472650, by rfl⟩ : syracuseStep 1260401 = 945301) B945301
theorem B1260419 : Blo 838352 1260419 := bstep (se 1 (by rfl) ⟨945314, by rfl⟩ : syracuseStep 1260419 = 1890629) B1890629
theorem B1260449 : Blo 838352 1260449 := bstep (se 2 (by rfl) ⟨472668, by rfl⟩ : syracuseStep 1260449 = 945337) B945337
theorem B2833325 : Blo 838352 2833325 := bstep (se 3 (by rfl) ⟨531248, by rfl⟩ : syracuseStep 2833325 = 1062497) B1062497
theorem B1260467 : Blo 838352 1260467 := bstep (se 1 (by rfl) ⟨945350, by rfl⟩ : syracuseStep 1260467 = 1890701) B1890701
theorem B1260497 : Blo 838352 1260497 := bstep (se 2 (by rfl) ⟨472686, by rfl⟩ : syracuseStep 1260497 = 945373) B945373
theorem B2833379 : Blo 838352 2833379 := bstep (se 1 (by rfl) ⟨2125034, by rfl⟩ : syracuseStep 2833379 = 4250069) B4250069
theorem B1260515 : Blo 838352 1260515 := bstep (se 1 (by rfl) ⟨945386, by rfl⟩ : syracuseStep 1260515 = 1890773) B1890773
theorem B1260545 : Blo 838352 1260545 := bstep (se 2 (by rfl) ⟨472704, by rfl⟩ : syracuseStep 1260545 = 945409) B945409
theorem B1260563 : Blo 838352 1260563 := bstep (se 1 (by rfl) ⟨945422, by rfl⟩ : syracuseStep 1260563 = 1890845) B1890845
theorem B1063955 : Blo 838352 1063955 := bstep (se 1 (by rfl) ⟨797966, by rfl⟩ : syracuseStep 1063955 = 1595933) B1595933
theorem B4045859 : Blo 838352 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B1260593 : Blo 838352 1260593 := bstep (se 2 (by rfl) ⟨472722, by rfl⟩ : syracuseStep 1260593 = 945445) B945445
theorem B1260611 : Blo 838352 1260611 := bstep (se 1 (by rfl) ⟨945458, by rfl⟩ : syracuseStep 1260611 = 1890917) B1890917
theorem B5749829 : Blo 838352 5749829 := bstep (se 4 (by rfl) ⟨539046, by rfl⟩ : syracuseStep 5749829 = 1078093) B1078093
theorem B1260641 : Blo 838352 1260641 := bstep (se 2 (by rfl) ⟨472740, by rfl⟩ : syracuseStep 1260641 = 945481) B945481
theorem B1260659 : Blo 838352 1260659 := bstep (se 1 (by rfl) ⟨945494, by rfl⟩ : syracuseStep 1260659 = 1890989) B1890989
theorem B1260689 : Blo 838352 1260689 := bstep (se 2 (by rfl) ⟨472758, by rfl⟩ : syracuseStep 1260689 = 945517) B945517
theorem B1260707 : Blo 838352 1260707 := bstep (se 1 (by rfl) ⟨945530, by rfl⟩ : syracuseStep 1260707 = 1891061) B1891061
theorem B1260737 : Blo 838352 1260737 := bstep (se 2 (by rfl) ⟨472776, by rfl⟩ : syracuseStep 1260737 = 945553) B945553
theorem B1260755 : Blo 838352 1260755 := bstep (se 1 (by rfl) ⟨945566, by rfl⟩ : syracuseStep 1260755 = 1891133) B1891133
theorem B2833649 : Blo 838352 2833649 := bstep (se 2 (by rfl) ⟨1062618, by rfl⟩ : syracuseStep 2833649 = 2125237) B2125237
theorem B1260785 : Blo 838352 1260785 := bstep (se 2 (by rfl) ⟨472794, by rfl⟩ : syracuseStep 1260785 = 945589) B945589
theorem B1260803 : Blo 838352 1260803 := bstep (se 1 (by rfl) ⟨945602, by rfl⟩ : syracuseStep 1260803 = 1891205) B1891205
theorem B1260833 : Blo 838352 1260833 := bstep (se 2 (by rfl) ⟨472812, by rfl⟩ : syracuseStep 1260833 = 945625) B945625
theorem B1260851 : Blo 838352 1260851 := bstep (se 1 (by rfl) ⟨945638, by rfl⟩ : syracuseStep 1260851 = 1891277) B1891277
theorem B1260881 : Blo 838352 1260881 := bstep (se 2 (by rfl) ⟨472830, by rfl⟩ : syracuseStep 1260881 = 945661) B945661
theorem B1260899 : Blo 838352 1260899 := bstep (se 1 (by rfl) ⟨945674, by rfl⟩ : syracuseStep 1260899 = 1891349) B1891349
theorem B1260929 : Blo 838352 1260929 := bstep (se 2 (by rfl) ⟨472848, by rfl⟩ : syracuseStep 1260929 = 945697) B945697
theorem B1916291 : Blo 838352 1916291 := bstep (se 1 (by rfl) ⟨1437218, by rfl⟩ : syracuseStep 1916291 = 2874437) B2874437
theorem B7191949 : Blo 838352 7191949 := bstep (se 3 (by rfl) ⟨1348490, by rfl⟩ : syracuseStep 7191949 = 2696981) B2696981
theorem B1260947 : Blo 838352 1260947 := bstep (se 1 (by rfl) ⟨945710, by rfl⟩ : syracuseStep 1260947 = 1891421) B1891421
theorem B1260977 : Blo 838352 1260977 := bstep (se 2 (by rfl) ⟨472866, by rfl⟩ : syracuseStep 1260977 = 945733) B945733
theorem B1260995 : Blo 838352 1260995 := bstep (se 1 (by rfl) ⟨945746, by rfl⟩ : syracuseStep 1260995 = 1891493) B1891493
theorem B1261025 : Blo 838352 1261025 := bstep (se 2 (by rfl) ⟨472884, by rfl⟩ : syracuseStep 1261025 = 945769) B945769
theorem B1261043 : Blo 838352 1261043 := bstep (se 1 (by rfl) ⟨945782, by rfl⟩ : syracuseStep 1261043 = 1891565) B1891565
theorem B1261073 : Blo 838352 1261073 := bstep (se 2 (by rfl) ⟨472902, by rfl⟩ : syracuseStep 1261073 = 945805) B945805
theorem B1195555 : Blo 838352 1195555 := bstep (se 1 (by rfl) ⟨896666, by rfl⟩ : syracuseStep 1195555 = 1793333) B1793333
theorem B1261091 : Blo 838352 1261091 := bstep (se 1 (by rfl) ⟨945818, by rfl⟩ : syracuseStep 1261091 = 1891637) B1891637
theorem B3194417 : Blo 838352 3194417 := bstep (se 2 (by rfl) ⟨1197906, by rfl⟩ : syracuseStep 3194417 = 2395813) B2395813
theorem B66534965 : Blo 838352 66534965 := bstep (se 5 (by rfl) ⟨3118826, by rfl⟩ : syracuseStep 66534965 = 6237653) B6237653
theorem B1261121 : Blo 838352 1261121 := bstep (se 2 (by rfl) ⟨472920, by rfl⟩ : syracuseStep 1261121 = 945841) B945841
theorem B1261139 : Blo 838352 1261139 := bstep (se 1 (by rfl) ⟨945854, by rfl⟩ : syracuseStep 1261139 = 1891709) B1891709
theorem B1261169 : Blo 838352 1261169 := bstep (se 2 (by rfl) ⟨472938, by rfl⟩ : syracuseStep 1261169 = 945877) B945877
theorem B1195651 : Blo 838352 1195651 := bstep (se 1 (by rfl) ⟨896738, by rfl⟩ : syracuseStep 1195651 = 1793477) B1793477
theorem B1261187 : Blo 838352 1261187 := bstep (se 1 (by rfl) ⟨945890, by rfl⟩ : syracuseStep 1261187 = 1891781) B1891781
theorem B1261217 : Blo 838352 1261217 := bstep (se 2 (by rfl) ⟨472956, by rfl⟩ : syracuseStep 1261217 = 945913) B945913
theorem B1261235 : Blo 838352 1261235 := bstep (se 1 (by rfl) ⟨945926, by rfl⟩ : syracuseStep 1261235 = 1891853) B1891853
theorem B1261265 : Blo 838352 1261265 := bstep (se 2 (by rfl) ⟨472974, by rfl⟩ : syracuseStep 1261265 = 945949) B945949
theorem B1064659 : Blo 838352 1064659 := bstep (se 1 (by rfl) ⟨798494, by rfl⟩ : syracuseStep 1064659 = 1596989) B1596989
theorem B1261283 : Blo 838352 1261283 := bstep (se 1 (by rfl) ⟨945962, by rfl⟩ : syracuseStep 1261283 = 1891925) B1891925
theorem B1261313 : Blo 838352 1261313 := bstep (se 2 (by rfl) ⟨472992, by rfl⟩ : syracuseStep 1261313 = 945985) B945985
theorem B2834189 : Blo 838352 2834189 := bstep (se 3 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 2834189 = 1062821) B1062821
theorem B1261331 : Blo 838352 1261331 := bstep (se 1 (by rfl) ⟨945998, by rfl⟩ : syracuseStep 1261331 = 1891997) B1891997
theorem B1261361 : Blo 838352 1261361 := bstep (se 2 (by rfl) ⟨473010, by rfl⟩ : syracuseStep 1261361 = 946021) B946021
theorem B1064755 : Blo 838352 1064755 := bstep (se 1 (by rfl) ⟨798566, by rfl⟩ : syracuseStep 1064755 = 1597133) B1597133
theorem B2834243 : Blo 838352 2834243 := bstep (se 1 (by rfl) ⟨2125682, by rfl⟩ : syracuseStep 2834243 = 4251365) B4251365
theorem B1261379 : Blo 838352 1261379 := bstep (se 1 (by rfl) ⟨946034, by rfl⟩ : syracuseStep 1261379 = 1892069) B1892069
theorem B1261409 : Blo 838352 1261409 := bstep (se 2 (by rfl) ⟨473028, by rfl⟩ : syracuseStep 1261409 = 946057) B946057
theorem B1261427 : Blo 838352 1261427 := bstep (se 1 (by rfl) ⟨946070, by rfl⟩ : syracuseStep 1261427 = 1892141) B1892141
theorem B1261457 : Blo 838352 1261457 := bstep (se 2 (by rfl) ⟨473046, by rfl⟩ : syracuseStep 1261457 = 946093) B946093
theorem B1261475 : Blo 838352 1261475 := bstep (se 1 (by rfl) ⟨946106, by rfl⟩ : syracuseStep 1261475 = 1892213) B1892213
theorem B1261505 : Blo 838352 1261505 := bstep (se 2 (by rfl) ⟨473064, by rfl⟩ : syracuseStep 1261505 = 946129) B946129
theorem B6799301 : Blo 838352 6799301 := bstep (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) B1274869
theorem B1261523 : Blo 838352 1261523 := bstep (se 1 (by rfl) ⟨946142, by rfl⟩ : syracuseStep 1261523 = 1892285) B1892285
theorem B1261553 : Blo 838352 1261553 := bstep (se 2 (by rfl) ⟨473082, by rfl⟩ : syracuseStep 1261553 = 946165) B946165
theorem B1261571 : Blo 838352 1261571 := bstep (se 1 (by rfl) ⟨946178, by rfl⟩ : syracuseStep 1261571 = 1892357) B1892357
theorem B1261601 : Blo 838352 1261601 := bstep (se 2 (by rfl) ⟨473100, by rfl⟩ : syracuseStep 1261601 = 946201) B946201
theorem B1261619 : Blo 838352 1261619 := bstep (se 1 (by rfl) ⟨946214, by rfl⟩ : syracuseStep 1261619 = 1892429) B1892429
theorem B2834513 : Blo 838352 2834513 := bstep (se 2 (by rfl) ⟨1062942, by rfl⟩ : syracuseStep 2834513 = 2125885) B2125885
theorem B1261649 : Blo 838352 1261649 := bstep (se 2 (by rfl) ⟨473118, by rfl⟩ : syracuseStep 1261649 = 946237) B946237
theorem B8077411 : Blo 838352 8077411 := bstep (se 1 (by rfl) ⟨6058058, by rfl⟩ : syracuseStep 8077411 = 12116117) B12116117
theorem B1261667 : Blo 838352 1261667 := bstep (se 1 (by rfl) ⟨946250, by rfl⟩ : syracuseStep 1261667 = 1892501) B1892501
theorem B1196147 : Blo 838352 1196147 := bstep (se 1 (by rfl) ⟨897110, by rfl⟩ : syracuseStep 1196147 = 1794221) B1794221
theorem B1261697 : Blo 838352 1261697 := bstep (se 2 (by rfl) ⟨473136, by rfl⟩ : syracuseStep 1261697 = 946273) B946273
theorem B1261715 : Blo 838352 1261715 := bstep (se 1 (by rfl) ⟨946286, by rfl⟩ : syracuseStep 1261715 = 1892573) B1892573
theorem B1261745 : Blo 838352 1261745 := bstep (se 2 (by rfl) ⟨473154, by rfl⟩ : syracuseStep 1261745 = 946309) B946309
theorem B1261763 : Blo 838352 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B3195085 : Blo 838352 3195085 := bstep (se 3 (by rfl) ⟨599078, by rfl⟩ : syracuseStep 3195085 = 1198157) B1198157
theorem B1261793 : Blo 838352 1261793 := bstep (se 2 (by rfl) ⟨473172, by rfl⟩ : syracuseStep 1261793 = 946345) B946345
theorem B1261811 : Blo 838352 1261811 := bstep (se 1 (by rfl) ⟨946358, by rfl⟩ : syracuseStep 1261811 = 1892717) B1892717
theorem B1261841 : Blo 838352 1261841 := bstep (se 2 (by rfl) ⟨473190, by rfl⟩ : syracuseStep 1261841 = 946381) B946381
theorem B1261859 : Blo 838352 1261859 := bstep (se 1 (by rfl) ⟨946394, by rfl⟩ : syracuseStep 1261859 = 1892789) B1892789
theorem B1065251 : Blo 838352 1065251 := bstep (se 1 (by rfl) ⟨798938, by rfl⟩ : syracuseStep 1065251 = 1597877) B1597877
theorem B1261889 : Blo 838352 1261889 := bstep (se 2 (by rfl) ⟨473208, by rfl⟩ : syracuseStep 1261889 = 946417) B946417
theorem B1261907 : Blo 838352 1261907 := bstep (se 1 (by rfl) ⟨946430, by rfl⟩ : syracuseStep 1261907 = 1892861) B1892861
theorem B1261937 : Blo 838352 1261937 := bstep (se 2 (by rfl) ⟨473226, by rfl⟩ : syracuseStep 1261937 = 946453) B946453
theorem B1261955 : Blo 838352 1261955 := bstep (se 1 (by rfl) ⟨946466, by rfl⟩ : syracuseStep 1261955 = 1892933) B1892933
theorem B1261985 : Blo 838352 1261985 := bstep (se 2 (by rfl) ⟨473244, by rfl⟩ : syracuseStep 1261985 = 946489) B946489
theorem B1262003 : Blo 838352 1262003 := bstep (se 1 (by rfl) ⟨946502, by rfl⟩ : syracuseStep 1262003 = 1893005) B1893005
theorem B2048465 : Blo 838352 2048465 := bstep (se 2 (by rfl) ⟨768174, by rfl⟩ : syracuseStep 2048465 = 1536349) B1536349
theorem B1262033 : Blo 838352 1262033 := bstep (se 2 (by rfl) ⟨473262, by rfl⟩ : syracuseStep 1262033 = 946525) B946525
theorem B3457507 : Blo 838352 3457507 := bstep (se 1 (by rfl) ⟨2593130, by rfl⟩ : syracuseStep 3457507 = 5186261) B5186261
theorem B1262051 : Blo 838352 1262051 := bstep (se 1 (by rfl) ⟨946538, by rfl⟩ : syracuseStep 1262051 = 1893077) B1893077
theorem B1262081 : Blo 838352 1262081 := bstep (se 2 (by rfl) ⟨473280, by rfl⟩ : syracuseStep 1262081 = 946561) B946561
theorem B1262099 : Blo 838352 1262099 := bstep (se 1 (by rfl) ⟨946574, by rfl⟩ : syracuseStep 1262099 = 1893149) B1893149
theorem B2015779 : Blo 838352 2015779 := bstep (se 1 (by rfl) ⟨1511834, by rfl⟩ : syracuseStep 2015779 = 3023669) B3023669
theorem B1262129 : Blo 838352 1262129 := bstep (se 2 (by rfl) ⟨473298, by rfl⟩ : syracuseStep 1262129 = 946597) B946597
theorem B1262147 : Blo 838352 1262147 := bstep (se 1 (by rfl) ⟨946610, by rfl⟩ : syracuseStep 1262147 = 1893221) B1893221
theorem B1262177 : Blo 838352 1262177 := bstep (se 2 (by rfl) ⟨473316, by rfl⟩ : syracuseStep 1262177 = 946633) B946633
theorem B2835053 : Blo 838352 2835053 := bstep (se 3 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 2835053 = 1063145) B1063145
theorem B1262195 : Blo 838352 1262195 := bstep (se 1 (by rfl) ⟨946646, by rfl⟩ : syracuseStep 1262195 = 1893293) B1893293
theorem B1262225 : Blo 838352 1262225 := bstep (se 2 (by rfl) ⟨473334, by rfl⟩ : syracuseStep 1262225 = 946669) B946669
theorem B2835107 : Blo 838352 2835107 := bstep (se 1 (by rfl) ⟨2126330, by rfl⟩ : syracuseStep 2835107 = 4252661) B4252661
theorem B1262243 : Blo 838352 1262243 := bstep (se 1 (by rfl) ⟨946682, by rfl⟩ : syracuseStep 1262243 = 1893365) B1893365
theorem B1262273 : Blo 838352 1262273 := bstep (se 2 (by rfl) ⟨473352, by rfl⟩ : syracuseStep 1262273 = 946705) B946705
theorem B7193285 : Blo 838352 7193285 := bstep (se 4 (by rfl) ⟨674370, by rfl⟩ : syracuseStep 7193285 = 1348741) B1348741
theorem B1262291 : Blo 838352 1262291 := bstep (se 1 (by rfl) ⟨946718, by rfl⟩ : syracuseStep 1262291 = 1893437) B1893437
theorem B1196785 : Blo 838352 1196785 := bstep (se 2 (by rfl) ⟨448794, by rfl⟩ : syracuseStep 1196785 = 897589) B897589
theorem B1262321 : Blo 838352 1262321 := bstep (se 2 (by rfl) ⟨473370, by rfl⟩ : syracuseStep 1262321 = 946741) B946741
theorem B1262339 : Blo 838352 1262339 := bstep (se 1 (by rfl) ⟨946754, by rfl⟩ : syracuseStep 1262339 = 1893509) B1893509
theorem B4244237 : Blo 838352 4244237 := bstep (se 3 (by rfl) ⟨795794, by rfl⟩ : syracuseStep 4244237 = 1591589) B1591589
theorem B1262369 : Blo 838352 1262369 := bstep (se 2 (by rfl) ⟨473388, by rfl⟩ : syracuseStep 1262369 = 946777) B946777
theorem B1262387 : Blo 838352 1262387 := bstep (se 1 (by rfl) ⟨946790, by rfl⟩ : syracuseStep 1262387 = 1893581) B1893581
theorem B11682613 : Blo 838352 11682613 := bstep (se 5 (by rfl) ⟨547622, by rfl⟩ : syracuseStep 11682613 = 1095245) B1095245
theorem B1262417 : Blo 838352 1262417 := bstep (se 2 (by rfl) ⟨473406, by rfl⟩ : syracuseStep 1262417 = 946813) B946813
theorem B1262435 : Blo 838352 1262435 := bstep (se 1 (by rfl) ⟨946826, by rfl⟩ : syracuseStep 1262435 = 1893653) B1893653
theorem B1262465 : Blo 838352 1262465 := bstep (se 2 (by rfl) ⟨473424, by rfl⟩ : syracuseStep 1262465 = 946849) B946849
theorem B1262483 : Blo 838352 1262483 := bstep (se 1 (by rfl) ⟨946862, by rfl⟩ : syracuseStep 1262483 = 1893725) B1893725
theorem B2835377 : Blo 838352 2835377 := bstep (se 2 (by rfl) ⟨1063266, by rfl⟩ : syracuseStep 2835377 = 2126533) B2126533
theorem B1262513 : Blo 838352 1262513 := bstep (se 2 (by rfl) ⟨473442, by rfl⟩ : syracuseStep 1262513 = 946885) B946885
theorem B1262531 : Blo 838352 1262531 := bstep (se 1 (by rfl) ⟨946898, by rfl⟩ : syracuseStep 1262531 = 1893797) B1893797
theorem B1262561 : Blo 838352 1262561 := bstep (se 2 (by rfl) ⟨473460, by rfl⟩ : syracuseStep 1262561 = 946921) B946921
theorem B3195875 : Blo 838352 3195875 := bstep (se 1 (by rfl) ⟨2396906, by rfl⟩ : syracuseStep 3195875 = 4793813) B4793813
theorem B1065955 : Blo 838352 1065955 := bstep (se 1 (by rfl) ⟨799466, by rfl⟩ : syracuseStep 1065955 = 1598933) B1598933
theorem B4047857 : Blo 838352 4047857 := bstep (se 2 (by rfl) ⟨1517946, by rfl⟩ : syracuseStep 4047857 = 3035893) B3035893
theorem B1262579 : Blo 838352 1262579 := bstep (se 1 (by rfl) ⟨946934, by rfl⟩ : syracuseStep 1262579 = 1893869) B1893869
theorem B1262609 : Blo 838352 1262609 := bstep (se 2 (by rfl) ⟨473478, by rfl⟩ : syracuseStep 1262609 = 946957) B946957
theorem B1262627 : Blo 838352 1262627 := bstep (se 1 (by rfl) ⟨946970, by rfl⟩ : syracuseStep 1262627 = 1893941) B1893941
theorem B1197121 : Blo 838352 1197121 := bstep (se 2 (by rfl) ⟨448920, by rfl⟩ : syracuseStep 1197121 = 897841) B897841
theorem B1262657 : Blo 838352 1262657 := bstep (se 2 (by rfl) ⟨473496, by rfl⟩ : syracuseStep 1262657 = 946993) B946993
theorem B1066051 : Blo 838352 1066051 := bstep (se 1 (by rfl) ⟨799538, by rfl⟩ : syracuseStep 1066051 = 1599077) B1599077
theorem B1262675 : Blo 838352 1262675 := bstep (se 1 (by rfl) ⟨947006, by rfl⟩ : syracuseStep 1262675 = 1894013) B1894013
theorem B2016355 : Blo 838352 2016355 := bstep (se 1 (by rfl) ⟨1512266, by rfl⟩ : syracuseStep 2016355 = 3024533) B3024533
theorem B1262705 : Blo 838352 1262705 := bstep (se 2 (by rfl) ⟨473514, by rfl⟩ : syracuseStep 1262705 = 947029) B947029
theorem B1262723 : Blo 838352 1262723 := bstep (se 1 (by rfl) ⟨947042, by rfl⟩ : syracuseStep 1262723 = 1894085) B1894085
theorem B1262753 : Blo 838352 1262753 := bstep (se 2 (by rfl) ⟨473532, by rfl⟩ : syracuseStep 1262753 = 947065) B947065
theorem B1262771 : Blo 838352 1262771 := bstep (se 1 (by rfl) ⟨947078, by rfl⟩ : syracuseStep 1262771 = 1894157) B1894157
theorem B1262801 : Blo 838352 1262801 := bstep (se 2 (by rfl) ⟨473550, by rfl⟩ : syracuseStep 1262801 = 947101) B947101
theorem B1262819 : Blo 838352 1262819 := bstep (se 1 (by rfl) ⟨947114, by rfl⟩ : syracuseStep 1262819 = 1894229) B1894229
theorem B1262849 : Blo 838352 1262849 := bstep (se 2 (by rfl) ⟨473568, by rfl⟩ : syracuseStep 1262849 = 947137) B947137
theorem B1262867 : Blo 838352 1262867 := bstep (se 1 (by rfl) ⟨947150, by rfl⟩ : syracuseStep 1262867 = 1894301) B1894301
theorem B1262897 : Blo 838352 1262897 := bstep (se 2 (by rfl) ⟨473586, by rfl⟩ : syracuseStep 1262897 = 947173) B947173
theorem B1262915 : Blo 838352 1262915 := bstep (se 1 (by rfl) ⟨947186, by rfl⟩ : syracuseStep 1262915 = 1894373) B1894373
theorem B1262945 : Blo 838352 1262945 := bstep (se 2 (by rfl) ⟨473604, by rfl⟩ : syracuseStep 1262945 = 947209) B947209
theorem B1262963 : Blo 838352 1262963 := bstep (se 1 (by rfl) ⟨947222, by rfl⟩ : syracuseStep 1262963 = 1894445) B1894445
theorem B1262993 : Blo 838352 1262993 := bstep (se 2 (by rfl) ⟨473622, by rfl⟩ : syracuseStep 1262993 = 947245) B947245
theorem B1263011 : Blo 838352 1263011 := bstep (se 1 (by rfl) ⟨947258, by rfl⟩ : syracuseStep 1263011 = 1894517) B1894517
theorem B1263041 : Blo 838352 1263041 := bstep (se 2 (by rfl) ⟨473640, by rfl⟩ : syracuseStep 1263041 = 947281) B947281
theorem B2835917 : Blo 838352 2835917 := bstep (se 3 (by rfl) ⟨531734, by rfl⟩ : syracuseStep 2835917 = 1063469) B1063469
theorem B1263059 : Blo 838352 1263059 := bstep (se 1 (by rfl) ⟨947294, by rfl⟩ : syracuseStep 1263059 = 1894589) B1894589
theorem B2016739 : Blo 838352 2016739 := bstep (se 1 (by rfl) ⟨1512554, by rfl⟩ : syracuseStep 2016739 = 3025109) B3025109
theorem B1263089 : Blo 838352 1263089 := bstep (se 2 (by rfl) ⟨473658, by rfl⟩ : syracuseStep 1263089 = 947317) B947317
theorem B2835971 : Blo 838352 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B1263107 : Blo 838352 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B1263137 : Blo 838352 1263137 := bstep (se 2 (by rfl) ⟨473676, by rfl⟩ : syracuseStep 1263137 = 947353) B947353
theorem B1263155 : Blo 838352 1263155 := bstep (se 1 (by rfl) ⟨947366, by rfl⟩ : syracuseStep 1263155 = 1894733) B1894733
theorem B1263185 : Blo 838352 1263185 := bstep (se 2 (by rfl) ⟨473694, by rfl⟩ : syracuseStep 1263185 = 947389) B947389
theorem B1263203 : Blo 838352 1263203 := bstep (se 1 (by rfl) ⟨947402, by rfl⟩ : syracuseStep 1263203 = 1894805) B1894805
theorem B3196529 : Blo 838352 3196529 := bstep (se 2 (by rfl) ⟨1198698, by rfl⟩ : syracuseStep 3196529 = 2397397) B2397397
theorem B1263233 : Blo 838352 1263233 := bstep (se 2 (by rfl) ⟨473712, by rfl⟩ : syracuseStep 1263233 = 947425) B947425
theorem B1197713 : Blo 838352 1197713 := bstep (se 2 (by rfl) ⟨449142, by rfl⟩ : syracuseStep 1197713 = 898285) B898285
theorem B1263251 : Blo 838352 1263251 := bstep (se 1 (by rfl) ⟨947438, by rfl⟩ : syracuseStep 1263251 = 1894877) B1894877
theorem B1263281 : Blo 838352 1263281 := bstep (se 2 (by rfl) ⟨473730, by rfl⟩ : syracuseStep 1263281 = 947461) B947461
theorem B1263299 : Blo 838352 1263299 := bstep (se 1 (by rfl) ⟨947474, by rfl⟩ : syracuseStep 1263299 = 1894949) B1894949
theorem B1263329 : Blo 838352 1263329 := bstep (se 2 (by rfl) ⟨473748, by rfl⟩ : syracuseStep 1263329 = 947497) B947497
theorem B3589859 : Blo 838352 3589859 := bstep (se 1 (by rfl) ⟨2692394, by rfl⟩ : syracuseStep 3589859 = 5384789) B5384789
theorem B1263347 : Blo 838352 1263347 := bstep (se 1 (by rfl) ⟨947510, by rfl⟩ : syracuseStep 1263347 = 1895021) B1895021
theorem B2836241 : Blo 838352 2836241 := bstep (se 2 (by rfl) ⟨1063590, by rfl⟩ : syracuseStep 2836241 = 2127181) B2127181
theorem B1263377 : Blo 838352 1263377 := bstep (se 2 (by rfl) ⟨473766, by rfl⟩ : syracuseStep 1263377 = 947533) B947533
theorem B1263395 : Blo 838352 1263395 := bstep (se 1 (by rfl) ⟨947546, by rfl⟩ : syracuseStep 1263395 = 1895093) B1895093
theorem B1263425 : Blo 838352 1263425 := bstep (se 2 (by rfl) ⟨473784, by rfl⟩ : syracuseStep 1263425 = 947569) B947569
theorem B1263443 : Blo 838352 1263443 := bstep (se 1 (by rfl) ⟨947582, by rfl⟩ : syracuseStep 1263443 = 1895165) B1895165
theorem B1263473 : Blo 838352 1263473 := bstep (se 2 (by rfl) ⟨473802, by rfl⟩ : syracuseStep 1263473 = 947605) B947605
theorem B1263491 : Blo 838352 1263491 := bstep (se 1 (by rfl) ⟨947618, by rfl⟩ : syracuseStep 1263491 = 1895237) B1895237
theorem B1263521 : Blo 838352 1263521 := bstep (se 2 (by rfl) ⟨473820, by rfl⟩ : syracuseStep 1263521 = 947641) B947641
theorem B1361953 : Blo 838352 1361953 := bstep (se 2 (by rfl) ⟨510732, by rfl⟩ : syracuseStep 1361953 = 1021465) B1021465
theorem B1198243 : Blo 838352 1198243 := bstep (se 1 (by rfl) ⟨898682, by rfl⟩ : syracuseStep 1198243 = 1797365) B1797365
theorem B1886417 : Blo 838352 1886417 := bstep (se 2 (by rfl) ⟨707406, by rfl⟩ : syracuseStep 1886417 = 1414813) B1414813
theorem B1886435 : Blo 838352 1886435 := bstep (se 1 (by rfl) ⟨1414826, by rfl⟩ : syracuseStep 1886435 = 2829653) B2829653
theorem B2836781 : Blo 838352 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B2017585 : Blo 838352 2017585 := bstep (se 2 (by rfl) ⟨756594, by rfl⟩ : syracuseStep 2017585 = 1513189) B1513189
theorem B2836835 : Blo 838352 2836835 := bstep (se 1 (by rfl) ⟨2127626, by rfl⟩ : syracuseStep 2836835 = 4255253) B4255253
theorem B1886705 : Blo 838352 1886705 := bstep (se 2 (by rfl) ⟨707514, by rfl⟩ : syracuseStep 1886705 = 1415029) B1415029
theorem B1198579 : Blo 838352 1198579 := bstep (se 1 (by rfl) ⟨898934, by rfl⟩ : syracuseStep 1198579 = 1797869) B1797869
theorem B1886723 : Blo 838352 1886723 := bstep (se 1 (by rfl) ⟨1415042, by rfl⟩ : syracuseStep 1886723 = 2830085) B2830085
theorem B1591825 : Blo 838352 1591825 := bstep (se 2 (by rfl) ⟨596934, by rfl⟩ : syracuseStep 1591825 = 1193869) B1193869
theorem B2837105 : Blo 838352 2837105 := bstep (se 2 (by rfl) ⟨1063914, by rfl⟩ : syracuseStep 2837105 = 2127829) B2127829
theorem B1821361 : Blo 838352 1821361 := bstep (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) B1366021
theorem B838355 : Blo 838352 838355 := bstep (se 1 (by rfl) ⟨628766, by rfl⟩ : syracuseStep 838355 = 1257533) B1257533
theorem B838371 : Blo 838352 838371 := bstep (se 1 (by rfl) ⟨628778, by rfl⟩ : syracuseStep 838371 = 1257557) B1257557
theorem B838387 : Blo 838352 838387 := bstep (se 1 (by rfl) ⟨628790, by rfl⟩ : syracuseStep 838387 = 1257581) B1257581
theorem B838403 : Blo 838352 838403 := bstep (se 1 (by rfl) ⟨628802, by rfl⟩ : syracuseStep 838403 = 1257605) B1257605
theorem B1886993 : Blo 838352 1886993 := bstep (se 2 (by rfl) ⟨707622, by rfl⟩ : syracuseStep 1886993 = 1415245) B1415245
theorem B838419 : Blo 838352 838419 := bstep (se 1 (by rfl) ⟨628814, by rfl⟩ : syracuseStep 838419 = 1257629) B1257629
theorem B838435 : Blo 838352 838435 := bstep (se 1 (by rfl) ⟨628826, by rfl⟩ : syracuseStep 838435 = 1257653) B1257653
theorem B1133347 : Blo 838352 1133347 := bstep (se 1 (by rfl) ⟨850010, by rfl⟩ : syracuseStep 1133347 = 1700021) B1700021
theorem B1887011 : Blo 838352 1887011 := bstep (se 1 (by rfl) ⟨1415258, by rfl⟩ : syracuseStep 1887011 = 2830517) B2830517
theorem B838451 : Blo 838352 838451 := bstep (se 1 (by rfl) ⟨628838, by rfl⟩ : syracuseStep 838451 = 1257677) B1257677
theorem B838467 : Blo 838352 838467 := bstep (se 1 (by rfl) ⟨628850, by rfl⟩ : syracuseStep 838467 = 1257701) B1257701
theorem B838483 : Blo 838352 838483 := bstep (se 1 (by rfl) ⟨628862, by rfl⟩ : syracuseStep 838483 = 1257725) B1257725
theorem B838499 : Blo 838352 838499 := bstep (se 1 (by rfl) ⟨628874, by rfl⟩ : syracuseStep 838499 = 1257749) B1257749
theorem B838515 : Blo 838352 838515 := bstep (se 1 (by rfl) ⟨628886, by rfl⟩ : syracuseStep 838515 = 1257773) B1257773
theorem B838531 : Blo 838352 838531 := bstep (se 1 (by rfl) ⟨628898, by rfl⟩ : syracuseStep 838531 = 1257797) B1257797
theorem B1133443 : Blo 838352 1133443 := bstep (se 1 (by rfl) ⟨850082, by rfl⟩ : syracuseStep 1133443 = 1700165) B1700165
theorem B1919875 : Blo 838352 1919875 := bstep (se 1 (by rfl) ⟨1439906, by rfl⟩ : syracuseStep 1919875 = 2879813) B2879813
theorem B838547 : Blo 838352 838547 := bstep (se 1 (by rfl) ⟨628910, by rfl⟩ : syracuseStep 838547 = 1257821) B1257821
theorem B838563 : Blo 838352 838563 := bstep (se 1 (by rfl) ⟨628922, by rfl⟩ : syracuseStep 838563 = 1257845) B1257845
theorem B1592227 : Blo 838352 1592227 := bstep (se 1 (by rfl) ⟨1194170, by rfl⟩ : syracuseStep 1592227 = 2388341) B2388341
theorem B3034019 : Blo 838352 3034019 := bstep (se 1 (by rfl) ⟨2275514, by rfl⟩ : syracuseStep 3034019 = 4551029) B4551029
theorem B838579 : Blo 838352 838579 := bstep (se 1 (by rfl) ⟨628934, by rfl⟩ : syracuseStep 838579 = 1257869) B1257869
theorem B838595 : Blo 838352 838595 := bstep (se 1 (by rfl) ⟨628946, by rfl⟩ : syracuseStep 838595 = 1257893) B1257893
theorem B1592273 : Blo 838352 1592273 := bstep (se 2 (by rfl) ⟨597102, by rfl⟩ : syracuseStep 1592273 = 1194205) B1194205
theorem B838611 : Blo 838352 838611 := bstep (se 1 (by rfl) ⟨628958, by rfl⟩ : syracuseStep 838611 = 1257917) B1257917
theorem B838627 : Blo 838352 838627 := bstep (se 1 (by rfl) ⟨628970, by rfl⟩ : syracuseStep 838627 = 1257941) B1257941
theorem B838643 : Blo 838352 838643 := bstep (se 1 (by rfl) ⟨628982, by rfl⟩ : syracuseStep 838643 = 1257965) B1257965
theorem B838659 : Blo 838352 838659 := bstep (se 1 (by rfl) ⟨628994, by rfl⟩ : syracuseStep 838659 = 1257989) B1257989
theorem B838675 : Blo 838352 838675 := bstep (se 1 (by rfl) ⟨629006, by rfl⟩ : syracuseStep 838675 = 1258013) B1258013
theorem B1199137 : Blo 838352 1199137 := bstep (se 2 (by rfl) ⟨449676, by rfl⟩ : syracuseStep 1199137 = 899353) B899353
theorem B838691 : Blo 838352 838691 := bstep (se 1 (by rfl) ⟨629018, by rfl⟩ : syracuseStep 838691 = 1258037) B1258037
theorem B3197987 : Blo 838352 3197987 := bstep (se 1 (by rfl) ⟨2398490, by rfl⟩ : syracuseStep 3197987 = 4796981) B4796981
theorem B1887281 : Blo 838352 1887281 := bstep (se 2 (by rfl) ⟨707730, by rfl⟩ : syracuseStep 1887281 = 1415461) B1415461
theorem B3198001 : Blo 838352 3198001 := bstep (se 2 (by rfl) ⟨1199250, by rfl⟩ : syracuseStep 3198001 = 2398501) B2398501
theorem B838707 : Blo 838352 838707 := bstep (se 1 (by rfl) ⟨629030, by rfl⟩ : syracuseStep 838707 = 1258061) B1258061
theorem B838723 : Blo 838352 838723 := bstep (se 1 (by rfl) ⟨629042, by rfl⟩ : syracuseStep 838723 = 1258085) B1258085
theorem B1887299 : Blo 838352 1887299 := bstep (se 1 (by rfl) ⟨1415474, by rfl⟩ : syracuseStep 1887299 = 2830949) B2830949
theorem B1199171 : Blo 838352 1199171 := bstep (se 1 (by rfl) ⟨899378, by rfl⟩ : syracuseStep 1199171 = 1798757) B1798757
theorem B838739 : Blo 838352 838739 := bstep (se 1 (by rfl) ⟨629054, by rfl⟩ : syracuseStep 838739 = 1258109) B1258109
theorem B838755 : Blo 838352 838755 := bstep (se 1 (by rfl) ⟨629066, by rfl⟩ : syracuseStep 838755 = 1258133) B1258133
theorem B838771 : Blo 838352 838771 := bstep (se 1 (by rfl) ⟨629078, by rfl⟩ : syracuseStep 838771 = 1258157) B1258157
theorem B838787 : Blo 838352 838787 := bstep (se 1 (by rfl) ⟨629090, by rfl⟩ : syracuseStep 838787 = 1258181) B1258181
theorem B2837645 : Blo 838352 2837645 := bstep (se 3 (by rfl) ⟨532058, by rfl⟩ : syracuseStep 2837645 = 1064117) B1064117
theorem B838803 : Blo 838352 838803 := bstep (se 1 (by rfl) ⟨629102, by rfl⟩ : syracuseStep 838803 = 1258205) B1258205
theorem B838819 : Blo 838352 838819 := bstep (se 1 (by rfl) ⟨629114, by rfl⟩ : syracuseStep 838819 = 1258229) B1258229
theorem B838835 : Blo 838352 838835 := bstep (se 1 (by rfl) ⟨629126, by rfl⟩ : syracuseStep 838835 = 1258253) B1258253
theorem B838851 : Blo 838352 838851 := bstep (se 1 (by rfl) ⟨629138, by rfl⟩ : syracuseStep 838851 = 1258277) B1258277
theorem B2837699 : Blo 838352 2837699 := bstep (se 1 (by rfl) ⟨2128274, by rfl⟩ : syracuseStep 2837699 = 4256549) B4256549
theorem B838867 : Blo 838352 838867 := bstep (se 1 (by rfl) ⟨629150, by rfl⟩ : syracuseStep 838867 = 1258301) B1258301
theorem B1133779 : Blo 838352 1133779 := bstep (se 1 (by rfl) ⟨850334, by rfl⟩ : syracuseStep 1133779 = 1700669) B1700669
theorem B838883 : Blo 838352 838883 := bstep (se 1 (by rfl) ⟨629162, by rfl⟩ : syracuseStep 838883 = 1258325) B1258325
theorem B1592561 : Blo 838352 1592561 := bstep (se 2 (by rfl) ⟨597210, by rfl⟩ : syracuseStep 1592561 = 1194421) B1194421
theorem B838899 : Blo 838352 838899 := bstep (se 1 (by rfl) ⟨629174, by rfl⟩ : syracuseStep 838899 = 1258349) B1258349
theorem B838915 : Blo 838352 838915 := bstep (se 1 (by rfl) ⟨629186, by rfl⟩ : syracuseStep 838915 = 1258373) B1258373
theorem B838931 : Blo 838352 838931 := bstep (se 1 (by rfl) ⟨629198, by rfl⟩ : syracuseStep 838931 = 1258397) B1258397
theorem B838947 : Blo 838352 838947 := bstep (se 1 (by rfl) ⟨629210, by rfl⟩ : syracuseStep 838947 = 1258421) B1258421
theorem B838963 : Blo 838352 838963 := bstep (se 1 (by rfl) ⟨629222, by rfl⟩ : syracuseStep 838963 = 1258445) B1258445
theorem B838979 : Blo 838352 838979 := bstep (se 1 (by rfl) ⟨629234, by rfl⟩ : syracuseStep 838979 = 1258469) B1258469
theorem B1887569 : Blo 838352 1887569 := bstep (se 2 (by rfl) ⟨707838, by rfl⟩ : syracuseStep 1887569 = 1415677) B1415677
theorem B838995 : Blo 838352 838995 := bstep (se 1 (by rfl) ⟨629246, by rfl⟩ : syracuseStep 838995 = 1258493) B1258493
theorem B1887587 : Blo 838352 1887587 := bstep (se 1 (by rfl) ⟨1415690, by rfl⟩ : syracuseStep 1887587 = 2831381) B2831381
theorem B839011 : Blo 838352 839011 := bstep (se 1 (by rfl) ⟨629258, by rfl⟩ : syracuseStep 839011 = 1258517) B1258517
theorem B3460465 : Blo 838352 3460465 := bstep (se 2 (by rfl) ⟨1297674, by rfl⟩ : syracuseStep 3460465 = 2595349) B2595349
theorem B839027 : Blo 838352 839027 := bstep (se 1 (by rfl) ⟨629270, by rfl⟩ : syracuseStep 839027 = 1258541) B1258541
theorem B839043 : Blo 838352 839043 := bstep (se 1 (by rfl) ⟨629282, by rfl⟩ : syracuseStep 839043 = 1258565) B1258565
theorem B839059 : Blo 838352 839059 := bstep (se 1 (by rfl) ⟨629294, by rfl⟩ : syracuseStep 839059 = 1258589) B1258589
theorem B839075 : Blo 838352 839075 := bstep (se 1 (by rfl) ⟨629306, by rfl⟩ : syracuseStep 839075 = 1258613) B1258613
theorem B839091 : Blo 838352 839091 := bstep (se 1 (by rfl) ⟨629318, by rfl⟩ : syracuseStep 839091 = 1258637) B1258637
theorem B839107 : Blo 838352 839107 := bstep (se 1 (by rfl) ⟨629330, by rfl⟩ : syracuseStep 839107 = 1258661) B1258661
theorem B5393861 : Blo 838352 5393861 := bstep (se 4 (by rfl) ⟨505674, by rfl⟩ : syracuseStep 5393861 = 1011349) B1011349
theorem B2837969 : Blo 838352 2837969 := bstep (se 2 (by rfl) ⟨1064238, by rfl⟩ : syracuseStep 2837969 = 2128477) B2128477
theorem B839123 : Blo 838352 839123 := bstep (se 1 (by rfl) ⟨629342, by rfl⟩ : syracuseStep 839123 = 1258685) B1258685
theorem B839139 : Blo 838352 839139 := bstep (se 1 (by rfl) ⟨629354, by rfl⟩ : syracuseStep 839139 = 1258709) B1258709
theorem B839155 : Blo 838352 839155 := bstep (se 1 (by rfl) ⟨629366, by rfl⟩ : syracuseStep 839155 = 1258733) B1258733
theorem B839171 : Blo 838352 839171 := bstep (se 1 (by rfl) ⟨629378, by rfl⟩ : syracuseStep 839171 = 1258757) B1258757
theorem B839187 : Blo 838352 839187 := bstep (se 1 (by rfl) ⟨629390, by rfl⟩ : syracuseStep 839187 = 1258781) B1258781
theorem B839203 : Blo 838352 839203 := bstep (se 1 (by rfl) ⟨629402, by rfl⟩ : syracuseStep 839203 = 1258805) B1258805
theorem B839219 : Blo 838352 839219 := bstep (se 1 (by rfl) ⟨629414, by rfl⟩ : syracuseStep 839219 = 1258829) B1258829
theorem B839235 : Blo 838352 839235 := bstep (se 1 (by rfl) ⟨629426, by rfl⟩ : syracuseStep 839235 = 1258853) B1258853
theorem B839251 : Blo 838352 839251 := bstep (se 1 (by rfl) ⟨629438, by rfl⟩ : syracuseStep 839251 = 1258877) B1258877
theorem B839267 : Blo 838352 839267 := bstep (se 1 (by rfl) ⟨629450, by rfl⟩ : syracuseStep 839267 = 1258901) B1258901
theorem B4247153 : Blo 838352 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B1887857 : Blo 838352 1887857 := bstep (se 2 (by rfl) ⟨707946, by rfl⟩ : syracuseStep 1887857 = 1415893) B1415893
theorem B839283 : Blo 838352 839283 := bstep (se 1 (by rfl) ⟨629462, by rfl⟩ : syracuseStep 839283 = 1258925) B1258925
theorem B1887875 : Blo 838352 1887875 := bstep (se 1 (by rfl) ⟨1415906, by rfl⟩ : syracuseStep 1887875 = 2831813) B2831813
theorem B839299 : Blo 838352 839299 := bstep (se 1 (by rfl) ⟨629474, by rfl⟩ : syracuseStep 839299 = 1258949) B1258949
theorem B839315 : Blo 838352 839315 := bstep (se 1 (by rfl) ⟨629486, by rfl⟩ : syracuseStep 839315 = 1258973) B1258973
theorem B839331 : Blo 838352 839331 := bstep (se 1 (by rfl) ⟨629498, by rfl⟩ : syracuseStep 839331 = 1258997) B1258997
theorem B839347 : Blo 838352 839347 := bstep (se 1 (by rfl) ⟨629510, by rfl⟩ : syracuseStep 839347 = 1259021) B1259021
theorem B839363 : Blo 838352 839363 := bstep (se 1 (by rfl) ⟨629522, by rfl⟩ : syracuseStep 839363 = 1259045) B1259045
theorem B839379 : Blo 838352 839379 := bstep (se 1 (by rfl) ⟨629534, by rfl⟩ : syracuseStep 839379 = 1259069) B1259069
theorem B839395 : Blo 838352 839395 := bstep (se 1 (by rfl) ⟨629546, by rfl⟩ : syracuseStep 839395 = 1259093) B1259093
theorem B839411 : Blo 838352 839411 := bstep (se 1 (by rfl) ⟨629558, by rfl⟩ : syracuseStep 839411 = 1259117) B1259117
theorem B839427 : Blo 838352 839427 := bstep (se 1 (by rfl) ⟨629570, by rfl⟩ : syracuseStep 839427 = 1259141) B1259141
theorem B839443 : Blo 838352 839443 := bstep (se 1 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 839443 = 1259165) B1259165
theorem B839459 : Blo 838352 839459 := bstep (se 1 (by rfl) ⟨629594, by rfl⟩ : syracuseStep 839459 = 1259189) B1259189
theorem B839475 : Blo 838352 839475 := bstep (se 1 (by rfl) ⟨629606, by rfl⟩ : syracuseStep 839475 = 1259213) B1259213
theorem B839491 : Blo 838352 839491 := bstep (se 1 (by rfl) ⟨629618, by rfl⟩ : syracuseStep 839491 = 1259237) B1259237
theorem B839507 : Blo 838352 839507 := bstep (se 1 (by rfl) ⟨629630, by rfl⟩ : syracuseStep 839507 = 1259261) B1259261
theorem B839523 : Blo 838352 839523 := bstep (se 1 (by rfl) ⟨629642, by rfl⟩ : syracuseStep 839523 = 1259285) B1259285
theorem B10768241 : Blo 838352 10768241 := bstep (se 2 (by rfl) ⟨4038090, by rfl⟩ : syracuseStep 10768241 = 8076181) B8076181
theorem B839539 : Blo 838352 839539 := bstep (se 1 (by rfl) ⟨629654, by rfl⟩ : syracuseStep 839539 = 1259309) B1259309
theorem B839555 : Blo 838352 839555 := bstep (se 1 (by rfl) ⟨629666, by rfl⟩ : syracuseStep 839555 = 1259333) B1259333
theorem B1888145 : Blo 838352 1888145 := bstep (se 2 (by rfl) ⟨708054, by rfl⟩ : syracuseStep 1888145 = 1416109) B1416109
theorem B1134481 : Blo 838352 1134481 := bstep (se 2 (by rfl) ⟨425430, by rfl⟩ : syracuseStep 1134481 = 850861) B850861
theorem B839571 : Blo 838352 839571 := bstep (se 1 (by rfl) ⟨629678, by rfl⟩ : syracuseStep 839571 = 1259357) B1259357
theorem B1888163 : Blo 838352 1888163 := bstep (se 1 (by rfl) ⟨1416122, by rfl⟩ : syracuseStep 1888163 = 2832245) B2832245
theorem B839587 : Blo 838352 839587 := bstep (se 1 (by rfl) ⟨629690, by rfl⟩ : syracuseStep 839587 = 1259381) B1259381
theorem B839603 : Blo 838352 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B1593283 : Blo 838352 1593283 := bstep (se 1 (by rfl) ⟨1194962, by rfl⟩ : syracuseStep 1593283 = 2389925) B2389925
theorem B839619 : Blo 838352 839619 := bstep (se 1 (by rfl) ⟨629714, by rfl⟩ : syracuseStep 839619 = 1259429) B1259429
theorem B839635 : Blo 838352 839635 := bstep (se 1 (by rfl) ⟨629726, by rfl⟩ : syracuseStep 839635 = 1259453) B1259453
theorem B839651 : Blo 838352 839651 := bstep (se 1 (by rfl) ⟨629738, by rfl⟩ : syracuseStep 839651 = 1259477) B1259477
theorem B2838509 : Blo 838352 2838509 := bstep (se 3 (by rfl) ⟨532220, by rfl⟩ : syracuseStep 2838509 = 1064441) B1064441
theorem B839667 : Blo 838352 839667 := bstep (se 1 (by rfl) ⟨629750, by rfl⟩ : syracuseStep 839667 = 1259501) B1259501
theorem B839683 : Blo 838352 839683 := bstep (se 1 (by rfl) ⟨629762, by rfl⟩ : syracuseStep 839683 = 1259525) B1259525
theorem B839699 : Blo 838352 839699 := bstep (se 1 (by rfl) ⟨629774, by rfl⟩ : syracuseStep 839699 = 1259549) B1259549
theorem B839715 : Blo 838352 839715 := bstep (se 1 (by rfl) ⟨629786, by rfl⟩ : syracuseStep 839715 = 1259573) B1259573
theorem B2838563 : Blo 838352 2838563 := bstep (se 1 (by rfl) ⟨2128922, by rfl⟩ : syracuseStep 2838563 = 4257845) B4257845
theorem B839731 : Blo 838352 839731 := bstep (se 1 (by rfl) ⟨629798, by rfl⟩ : syracuseStep 839731 = 1259597) B1259597
theorem B839747 : Blo 838352 839747 := bstep (se 1 (by rfl) ⟨629810, by rfl⟩ : syracuseStep 839747 = 1259621) B1259621
theorem B839763 : Blo 838352 839763 := bstep (se 1 (by rfl) ⟨629822, by rfl⟩ : syracuseStep 839763 = 1259645) B1259645
theorem B839779 : Blo 838352 839779 := bstep (se 1 (by rfl) ⟨629834, by rfl⟩ : syracuseStep 839779 = 1259669) B1259669
theorem B839795 : Blo 838352 839795 := bstep (se 1 (by rfl) ⟨629846, by rfl⟩ : syracuseStep 839795 = 1259693) B1259693
theorem B839811 : Blo 838352 839811 := bstep (se 1 (by rfl) ⟨629858, by rfl⟩ : syracuseStep 839811 = 1259717) B1259717
theorem B839827 : Blo 838352 839827 := bstep (se 1 (by rfl) ⟨629870, by rfl⟩ : syracuseStep 839827 = 1259741) B1259741
theorem B839843 : Blo 838352 839843 := bstep (se 1 (by rfl) ⟨629882, by rfl⟩ : syracuseStep 839843 = 1259765) B1259765
theorem B1888433 : Blo 838352 1888433 := bstep (se 2 (by rfl) ⟨708162, by rfl⟩ : syracuseStep 1888433 = 1416325) B1416325
theorem B839859 : Blo 838352 839859 := bstep (se 1 (by rfl) ⟨629894, by rfl⟩ : syracuseStep 839859 = 1259789) B1259789
theorem B1888451 : Blo 838352 1888451 := bstep (se 1 (by rfl) ⟨1416338, by rfl⟩ : syracuseStep 1888451 = 2832677) B2832677
theorem B839875 : Blo 838352 839875 := bstep (se 1 (by rfl) ⟨629906, by rfl⟩ : syracuseStep 839875 = 1259813) B1259813
theorem B839891 : Blo 838352 839891 := bstep (se 1 (by rfl) ⟨629918, by rfl⟩ : syracuseStep 839891 = 1259837) B1259837
theorem B839907 : Blo 838352 839907 := bstep (se 1 (by rfl) ⟨629930, by rfl⟩ : syracuseStep 839907 = 1259861) B1259861
theorem B839923 : Blo 838352 839923 := bstep (se 1 (by rfl) ⟨629942, by rfl⟩ : syracuseStep 839923 = 1259885) B1259885
theorem B839939 : Blo 838352 839939 := bstep (se 1 (by rfl) ⟨629954, by rfl⟩ : syracuseStep 839939 = 1259909) B1259909
theorem B4313357 : Blo 838352 4313357 := bstep (se 3 (by rfl) ⟨808754, by rfl⟩ : syracuseStep 4313357 = 1617509) B1617509
theorem B839955 : Blo 838352 839955 := bstep (se 1 (by rfl) ⟨629966, by rfl⟩ : syracuseStep 839955 = 1259933) B1259933
theorem B839971 : Blo 838352 839971 := bstep (se 1 (by rfl) ⟨629978, by rfl⟩ : syracuseStep 839971 = 1259957) B1259957
theorem B2838833 : Blo 838352 2838833 := bstep (se 2 (by rfl) ⟨1064562, by rfl⟩ : syracuseStep 2838833 = 2129125) B2129125
theorem B839987 : Blo 838352 839987 := bstep (se 1 (by rfl) ⟨629990, by rfl⟩ : syracuseStep 839987 = 1259981) B1259981
theorem B840003 : Blo 838352 840003 := bstep (se 1 (by rfl) ⟨630002, by rfl⟩ : syracuseStep 840003 = 1260005) B1260005
theorem B840019 : Blo 838352 840019 := bstep (se 1 (by rfl) ⟨630014, by rfl⟩ : syracuseStep 840019 = 1260029) B1260029
theorem B840035 : Blo 838352 840035 := bstep (se 1 (by rfl) ⟨630026, by rfl⟩ : syracuseStep 840035 = 1260053) B1260053
theorem B840051 : Blo 838352 840051 := bstep (se 1 (by rfl) ⟨630038, by rfl⟩ : syracuseStep 840051 = 1260077) B1260077
theorem B1593731 : Blo 838352 1593731 := bstep (se 1 (by rfl) ⟨1195298, by rfl⟩ : syracuseStep 1593731 = 2390597) B2390597
theorem B840067 : Blo 838352 840067 := bstep (se 1 (by rfl) ⟨630050, by rfl⟩ : syracuseStep 840067 = 1260101) B1260101
theorem B840083 : Blo 838352 840083 := bstep (se 1 (by rfl) ⟨630062, by rfl⟩ : syracuseStep 840083 = 1260125) B1260125
theorem B840099 : Blo 838352 840099 := bstep (se 1 (by rfl) ⟨630074, by rfl⟩ : syracuseStep 840099 = 1260149) B1260149
theorem B840115 : Blo 838352 840115 := bstep (se 1 (by rfl) ⟨630086, by rfl⟩ : syracuseStep 840115 = 1260173) B1260173
theorem B840131 : Blo 838352 840131 := bstep (se 1 (by rfl) ⟨630098, by rfl⟩ : syracuseStep 840131 = 1260197) B1260197
theorem B1888721 : Blo 838352 1888721 := bstep (se 2 (by rfl) ⟨708270, by rfl⟩ : syracuseStep 1888721 = 1416541) B1416541
theorem B840147 : Blo 838352 840147 := bstep (se 1 (by rfl) ⟨630110, by rfl⟩ : syracuseStep 840147 = 1260221) B1260221
theorem B1888739 : Blo 838352 1888739 := bstep (se 1 (by rfl) ⟨1416554, by rfl⟩ : syracuseStep 1888739 = 2833109) B2833109
theorem B840163 : Blo 838352 840163 := bstep (se 1 (by rfl) ⟨630122, by rfl⟩ : syracuseStep 840163 = 1260245) B1260245
theorem B840179 : Blo 838352 840179 := bstep (se 1 (by rfl) ⟨630134, by rfl⟩ : syracuseStep 840179 = 1260269) B1260269
theorem B840195 : Blo 838352 840195 := bstep (se 1 (by rfl) ⟨630146, by rfl⟩ : syracuseStep 840195 = 1260293) B1260293
theorem B840211 : Blo 838352 840211 := bstep (se 1 (by rfl) ⟨630158, by rfl⟩ : syracuseStep 840211 = 1260317) B1260317
theorem B840227 : Blo 838352 840227 := bstep (se 1 (by rfl) ⟨630170, by rfl⟩ : syracuseStep 840227 = 1260341) B1260341
theorem B840243 : Blo 838352 840243 := bstep (se 1 (by rfl) ⟨630182, by rfl⟩ : syracuseStep 840243 = 1260365) B1260365
theorem B840259 : Blo 838352 840259 := bstep (se 1 (by rfl) ⟨630194, by rfl⟩ : syracuseStep 840259 = 1260389) B1260389
theorem B840275 : Blo 838352 840275 := bstep (se 1 (by rfl) ⟨630206, by rfl⟩ : syracuseStep 840275 = 1260413) B1260413
theorem B840291 : Blo 838352 840291 := bstep (se 1 (by rfl) ⟨630218, by rfl⟩ : syracuseStep 840291 = 1260437) B1260437
theorem B840307 : Blo 838352 840307 := bstep (se 1 (by rfl) ⟨630230, by rfl⟩ : syracuseStep 840307 = 1260461) B1260461
theorem B840323 : Blo 838352 840323 := bstep (se 1 (by rfl) ⟨630242, by rfl⟩ : syracuseStep 840323 = 1260485) B1260485
theorem B840339 : Blo 838352 840339 := bstep (se 1 (by rfl) ⟨630254, by rfl⟩ : syracuseStep 840339 = 1260509) B1260509
theorem B1594019 : Blo 838352 1594019 := bstep (se 1 (by rfl) ⟨1195514, by rfl⟩ : syracuseStep 1594019 = 2391029) B2391029
theorem B840355 : Blo 838352 840355 := bstep (se 1 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 840355 = 1260533) B1260533
theorem B840371 : Blo 838352 840371 := bstep (se 1 (by rfl) ⟨630278, by rfl⟩ : syracuseStep 840371 = 1260557) B1260557
theorem B840387 : Blo 838352 840387 := bstep (se 1 (by rfl) ⟨630290, by rfl⟩ : syracuseStep 840387 = 1260581) B1260581
theorem B840403 : Blo 838352 840403 := bstep (se 1 (by rfl) ⟨630302, by rfl⟩ : syracuseStep 840403 = 1260605) B1260605
theorem B840419 : Blo 838352 840419 := bstep (se 1 (by rfl) ⟨630314, by rfl⟩ : syracuseStep 840419 = 1260629) B1260629
theorem B1889009 : Blo 838352 1889009 := bstep (se 2 (by rfl) ⟨708378, by rfl⟩ : syracuseStep 1889009 = 1416757) B1416757
theorem B840435 : Blo 838352 840435 := bstep (se 1 (by rfl) ⟨630326, by rfl⟩ : syracuseStep 840435 = 1260653) B1260653
theorem B1889027 : Blo 838352 1889027 := bstep (se 1 (by rfl) ⟨1416770, by rfl⟩ : syracuseStep 1889027 = 2833541) B2833541
theorem B840451 : Blo 838352 840451 := bstep (se 1 (by rfl) ⟨630338, by rfl⟩ : syracuseStep 840451 = 1260677) B1260677
theorem B840467 : Blo 838352 840467 := bstep (se 1 (by rfl) ⟨630350, by rfl⟩ : syracuseStep 840467 = 1260701) B1260701
theorem B840483 : Blo 838352 840483 := bstep (se 1 (by rfl) ⟨630362, by rfl⟩ : syracuseStep 840483 = 1260725) B1260725
theorem B840499 : Blo 838352 840499 := bstep (se 1 (by rfl) ⟨630374, by rfl⟩ : syracuseStep 840499 = 1260749) B1260749
theorem B840515 : Blo 838352 840515 := bstep (se 1 (by rfl) ⟨630386, by rfl⟩ : syracuseStep 840515 = 1260773) B1260773
theorem B2839373 : Blo 838352 2839373 := bstep (se 3 (by rfl) ⟨532382, by rfl⟩ : syracuseStep 2839373 = 1064765) B1064765
theorem B840531 : Blo 838352 840531 := bstep (se 1 (by rfl) ⟨630398, by rfl⟩ : syracuseStep 840531 = 1260797) B1260797
theorem B840547 : Blo 838352 840547 := bstep (se 1 (by rfl) ⟨630410, by rfl⟩ : syracuseStep 840547 = 1260821) B1260821
theorem B840563 : Blo 838352 840563 := bstep (se 1 (by rfl) ⟨630422, by rfl⟩ : syracuseStep 840563 = 1260845) B1260845
theorem B840579 : Blo 838352 840579 := bstep (se 1 (by rfl) ⟨630434, by rfl⟩ : syracuseStep 840579 = 1260869) B1260869
theorem B2839427 : Blo 838352 2839427 := bstep (se 1 (by rfl) ⟨2129570, by rfl⟩ : syracuseStep 2839427 = 4259141) B4259141
theorem B840595 : Blo 838352 840595 := bstep (se 1 (by rfl) ⟨630446, by rfl⟩ : syracuseStep 840595 = 1260893) B1260893
theorem B840611 : Blo 838352 840611 := bstep (se 1 (by rfl) ⟨630458, by rfl⟩ : syracuseStep 840611 = 1260917) B1260917
theorem B840627 : Blo 838352 840627 := bstep (se 1 (by rfl) ⟨630470, by rfl⟩ : syracuseStep 840627 = 1260941) B1260941
theorem B840643 : Blo 838352 840643 := bstep (se 1 (by rfl) ⟨630482, by rfl⟩ : syracuseStep 840643 = 1260965) B1260965
theorem B840659 : Blo 838352 840659 := bstep (se 1 (by rfl) ⟨630494, by rfl⟩ : syracuseStep 840659 = 1260989) B1260989
theorem B840675 : Blo 838352 840675 := bstep (se 1 (by rfl) ⟨630506, by rfl⟩ : syracuseStep 840675 = 1261013) B1261013
theorem B840691 : Blo 838352 840691 := bstep (se 1 (by rfl) ⟨630518, by rfl⟩ : syracuseStep 840691 = 1261037) B1261037
theorem B840707 : Blo 838352 840707 := bstep (se 1 (by rfl) ⟨630530, by rfl⟩ : syracuseStep 840707 = 1261061) B1261061
theorem B1889297 : Blo 838352 1889297 := bstep (se 2 (by rfl) ⟨708486, by rfl⟩ : syracuseStep 1889297 = 1416973) B1416973
theorem B840723 : Blo 838352 840723 := bstep (se 1 (by rfl) ⟨630542, by rfl⟩ : syracuseStep 840723 = 1261085) B1261085
theorem B4248611 : Blo 838352 4248611 := bstep (se 1 (by rfl) ⟨3186458, by rfl⟩ : syracuseStep 4248611 = 6372917) B6372917
theorem B1889315 : Blo 838352 1889315 := bstep (se 1 (by rfl) ⟨1416986, by rfl⟩ : syracuseStep 1889315 = 2833973) B2833973
theorem B840739 : Blo 838352 840739 := bstep (se 1 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 840739 = 1261109) B1261109
theorem B840755 : Blo 838352 840755 := bstep (se 1 (by rfl) ⟨630566, by rfl⟩ : syracuseStep 840755 = 1261133) B1261133
theorem B840771 : Blo 838352 840771 := bstep (se 1 (by rfl) ⟨630578, by rfl⟩ : syracuseStep 840771 = 1261157) B1261157
theorem B840787 : Blo 838352 840787 := bstep (se 1 (by rfl) ⟨630590, by rfl⟩ : syracuseStep 840787 = 1261181) B1261181
theorem B840803 : Blo 838352 840803 := bstep (se 1 (by rfl) ⟨630602, by rfl⟩ : syracuseStep 840803 = 1261205) B1261205
theorem B840819 : Blo 838352 840819 := bstep (se 1 (by rfl) ⟨630614, by rfl⟩ : syracuseStep 840819 = 1261229) B1261229
theorem B840835 : Blo 838352 840835 := bstep (se 1 (by rfl) ⟨630626, by rfl⟩ : syracuseStep 840835 = 1261253) B1261253
theorem B2839697 : Blo 838352 2839697 := bstep (se 2 (by rfl) ⟨1064886, by rfl⟩ : syracuseStep 2839697 = 2129773) B2129773
theorem B840851 : Blo 838352 840851 := bstep (se 1 (by rfl) ⟨630638, by rfl⟩ : syracuseStep 840851 = 1261277) B1261277
theorem B840867 : Blo 838352 840867 := bstep (se 1 (by rfl) ⟨630650, by rfl⟩ : syracuseStep 840867 = 1261301) B1261301
theorem B840883 : Blo 838352 840883 := bstep (se 1 (by rfl) ⟨630662, by rfl⟩ : syracuseStep 840883 = 1261325) B1261325
theorem B840899 : Blo 838352 840899 := bstep (se 1 (by rfl) ⟨630674, by rfl⟩ : syracuseStep 840899 = 1261349) B1261349
theorem B9557189 : Blo 838352 9557189 := bstep (se 4 (by rfl) ⟨895986, by rfl⟩ : syracuseStep 9557189 = 1791973) B1791973
theorem B840915 : Blo 838352 840915 := bstep (se 1 (by rfl) ⟨630686, by rfl⟩ : syracuseStep 840915 = 1261373) B1261373
theorem B840931 : Blo 838352 840931 := bstep (se 1 (by rfl) ⟨630698, by rfl⟩ : syracuseStep 840931 = 1261397) B1261397
theorem B840947 : Blo 838352 840947 := bstep (se 1 (by rfl) ⟨630710, by rfl⟩ : syracuseStep 840947 = 1261421) B1261421
theorem B840963 : Blo 838352 840963 := bstep (se 1 (by rfl) ⟨630722, by rfl⟩ : syracuseStep 840963 = 1261445) B1261445
theorem B840979 : Blo 838352 840979 := bstep (se 1 (by rfl) ⟨630734, by rfl⟩ : syracuseStep 840979 = 1261469) B1261469
theorem B840995 : Blo 838352 840995 := bstep (se 1 (by rfl) ⟨630746, by rfl⟩ : syracuseStep 840995 = 1261493) B1261493
theorem B1889585 : Blo 838352 1889585 := bstep (se 2 (by rfl) ⟨708594, by rfl⟩ : syracuseStep 1889585 = 1417189) B1417189
theorem B841011 : Blo 838352 841011 := bstep (se 1 (by rfl) ⟨630758, by rfl⟩ : syracuseStep 841011 = 1261517) B1261517
theorem B1889603 : Blo 838352 1889603 := bstep (se 1 (by rfl) ⟨1417202, by rfl⟩ : syracuseStep 1889603 = 2834405) B2834405
theorem B841027 : Blo 838352 841027 := bstep (se 1 (by rfl) ⟨630770, by rfl⟩ : syracuseStep 841027 = 1261541) B1261541
theorem B841043 : Blo 838352 841043 := bstep (se 1 (by rfl) ⟨630782, by rfl⟩ : syracuseStep 841043 = 1261565) B1261565
theorem B841059 : Blo 838352 841059 := bstep (se 1 (by rfl) ⟨630794, by rfl⟩ : syracuseStep 841059 = 1261589) B1261589
theorem B841075 : Blo 838352 841075 := bstep (se 1 (by rfl) ⟨630806, by rfl⟩ : syracuseStep 841075 = 1261613) B1261613
theorem B841091 : Blo 838352 841091 := bstep (se 1 (by rfl) ⟨630818, by rfl⟩ : syracuseStep 841091 = 1261637) B1261637
theorem B841107 : Blo 838352 841107 := bstep (se 1 (by rfl) ⟨630830, by rfl⟩ : syracuseStep 841107 = 1261661) B1261661
theorem B841123 : Blo 838352 841123 := bstep (se 1 (by rfl) ⟨630842, by rfl⟩ : syracuseStep 841123 = 1261685) B1261685
theorem B841139 : Blo 838352 841139 := bstep (se 1 (by rfl) ⟨630854, by rfl⟩ : syracuseStep 841139 = 1261709) B1261709
theorem B841155 : Blo 838352 841155 := bstep (se 1 (by rfl) ⟨630866, by rfl⟩ : syracuseStep 841155 = 1261733) B1261733
theorem B841171 : Blo 838352 841171 := bstep (se 1 (by rfl) ⟨630878, by rfl⟩ : syracuseStep 841171 = 1261757) B1261757
theorem B841187 : Blo 838352 841187 := bstep (se 1 (by rfl) ⟨630890, by rfl⟩ : syracuseStep 841187 = 1261781) B1261781
theorem B841203 : Blo 838352 841203 := bstep (se 1 (by rfl) ⟨630902, by rfl⟩ : syracuseStep 841203 = 1261805) B1261805
theorem B841219 : Blo 838352 841219 := bstep (se 1 (by rfl) ⟨630914, by rfl⟩ : syracuseStep 841219 = 1261829) B1261829
theorem B841235 : Blo 838352 841235 := bstep (se 1 (by rfl) ⟨630926, by rfl⟩ : syracuseStep 841235 = 1261853) B1261853
theorem B841251 : Blo 838352 841251 := bstep (se 1 (by rfl) ⟨630938, by rfl⟩ : syracuseStep 841251 = 1261877) B1261877
theorem B841267 : Blo 838352 841267 := bstep (se 1 (by rfl) ⟨630950, by rfl⟩ : syracuseStep 841267 = 1261901) B1261901
theorem B841283 : Blo 838352 841283 := bstep (se 1 (by rfl) ⟨630962, by rfl⟩ : syracuseStep 841283 = 1261925) B1261925
theorem B1889873 : Blo 838352 1889873 := bstep (se 2 (by rfl) ⟨708702, by rfl⟩ : syracuseStep 1889873 = 1417405) B1417405
theorem B1594961 : Blo 838352 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B841299 : Blo 838352 841299 := bstep (se 1 (by rfl) ⟨630974, by rfl⟩ : syracuseStep 841299 = 1261949) B1261949
theorem B1889891 : Blo 838352 1889891 := bstep (se 1 (by rfl) ⟨1417418, by rfl⟩ : syracuseStep 1889891 = 2834837) B2834837
theorem B841315 : Blo 838352 841315 := bstep (se 1 (by rfl) ⟨630986, by rfl⟩ : syracuseStep 841315 = 1261973) B1261973
theorem B841331 : Blo 838352 841331 := bstep (se 1 (by rfl) ⟨630998, by rfl⟩ : syracuseStep 841331 = 1261997) B1261997
theorem B841347 : Blo 838352 841347 := bstep (se 1 (by rfl) ⟨631010, by rfl⟩ : syracuseStep 841347 = 1262021) B1262021
theorem B841363 : Blo 838352 841363 := bstep (se 1 (by rfl) ⟨631022, by rfl⟩ : syracuseStep 841363 = 1262045) B1262045
theorem B841379 : Blo 838352 841379 := bstep (se 1 (by rfl) ⟨631034, by rfl⟩ : syracuseStep 841379 = 1262069) B1262069
theorem B2840237 : Blo 838352 2840237 := bstep (se 3 (by rfl) ⟨532544, by rfl⟩ : syracuseStep 2840237 = 1065089) B1065089
theorem B841395 : Blo 838352 841395 := bstep (se 1 (by rfl) ⟨631046, by rfl⟩ : syracuseStep 841395 = 1262093) B1262093
theorem B841411 : Blo 838352 841411 := bstep (se 1 (by rfl) ⟨631058, by rfl⟩ : syracuseStep 841411 = 1262117) B1262117
theorem B841427 : Blo 838352 841427 := bstep (se 1 (by rfl) ⟨631070, by rfl⟩ : syracuseStep 841427 = 1262141) B1262141
theorem B6379235 : Blo 838352 6379235 := bstep (se 1 (by rfl) ⟨4784426, by rfl⟩ : syracuseStep 6379235 = 9568853) B9568853
theorem B841443 : Blo 838352 841443 := bstep (se 1 (by rfl) ⟨631082, by rfl⟩ : syracuseStep 841443 = 1262165) B1262165
theorem B2840291 : Blo 838352 2840291 := bstep (se 1 (by rfl) ⟨2130218, by rfl⟩ : syracuseStep 2840291 = 4260437) B4260437
theorem B841459 : Blo 838352 841459 := bstep (se 1 (by rfl) ⟨631094, by rfl⟩ : syracuseStep 841459 = 1262189) B1262189
theorem B841475 : Blo 838352 841475 := bstep (se 1 (by rfl) ⟨631106, by rfl⟩ : syracuseStep 841475 = 1262213) B1262213
theorem B841491 : Blo 838352 841491 := bstep (se 1 (by rfl) ⟨631118, by rfl⟩ : syracuseStep 841491 = 1262237) B1262237
theorem B841507 : Blo 838352 841507 := bstep (se 1 (by rfl) ⟨631130, by rfl⟩ : syracuseStep 841507 = 1262261) B1262261
theorem B841523 : Blo 838352 841523 := bstep (se 1 (by rfl) ⟨631142, by rfl⟩ : syracuseStep 841523 = 1262285) B1262285
theorem B841539 : Blo 838352 841539 := bstep (se 1 (by rfl) ⟨631154, by rfl⟩ : syracuseStep 841539 = 1262309) B1262309
theorem B10770245 : Blo 838352 10770245 := bstep (se 4 (by rfl) ⟨1009710, by rfl⟩ : syracuseStep 10770245 = 2019421) B2019421
theorem B4249421 : Blo 838352 4249421 := bstep (se 3 (by rfl) ⟨796766, by rfl⟩ : syracuseStep 4249421 = 1593533) B1593533
theorem B3594061 : Blo 838352 3594061 := bstep (se 3 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 3594061 = 1347773) B1347773
theorem B841555 : Blo 838352 841555 := bstep (se 1 (by rfl) ⟨631166, by rfl⟩ : syracuseStep 841555 = 1262333) B1262333
theorem B841571 : Blo 838352 841571 := bstep (se 1 (by rfl) ⟨631178, by rfl⟩ : syracuseStep 841571 = 1262357) B1262357
theorem B1890161 : Blo 838352 1890161 := bstep (se 2 (by rfl) ⟨708810, by rfl⟩ : syracuseStep 1890161 = 1417621) B1417621
theorem B841587 : Blo 838352 841587 := bstep (se 1 (by rfl) ⟨631190, by rfl⟩ : syracuseStep 841587 = 1262381) B1262381
theorem B1890179 : Blo 838352 1890179 := bstep (se 1 (by rfl) ⟨1417634, by rfl⟩ : syracuseStep 1890179 = 2835269) B2835269
theorem B841603 : Blo 838352 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B841619 : Blo 838352 841619 := bstep (se 1 (by rfl) ⟨631214, by rfl⟩ : syracuseStep 841619 = 1262429) B1262429
theorem B841635 : Blo 838352 841635 := bstep (se 1 (by rfl) ⟨631226, by rfl⟩ : syracuseStep 841635 = 1262453) B1262453
theorem B841651 : Blo 838352 841651 := bstep (se 1 (by rfl) ⟨631238, by rfl⟩ : syracuseStep 841651 = 1262477) B1262477
theorem B841667 : Blo 838352 841667 := bstep (se 1 (by rfl) ⟨631250, by rfl⟩ : syracuseStep 841667 = 1262501) B1262501
theorem B841683 : Blo 838352 841683 := bstep (se 1 (by rfl) ⟨631262, by rfl⟩ : syracuseStep 841683 = 1262525) B1262525
theorem B841699 : Blo 838352 841699 := bstep (se 1 (by rfl) ⟨631274, by rfl⟩ : syracuseStep 841699 = 1262549) B1262549
theorem B2840561 : Blo 838352 2840561 := bstep (se 2 (by rfl) ⟨1065210, by rfl⟩ : syracuseStep 2840561 = 2130421) B2130421
theorem B841715 : Blo 838352 841715 := bstep (se 1 (by rfl) ⟨631286, by rfl⟩ : syracuseStep 841715 = 1262573) B1262573
theorem B841731 : Blo 838352 841731 := bstep (se 1 (by rfl) ⟨631298, by rfl⟩ : syracuseStep 841731 = 1262597) B1262597
theorem B841747 : Blo 838352 841747 := bstep (se 1 (by rfl) ⟨631310, by rfl⟩ : syracuseStep 841747 = 1262621) B1262621
theorem B841763 : Blo 838352 841763 := bstep (se 1 (by rfl) ⟨631322, by rfl⟩ : syracuseStep 841763 = 1262645) B1262645
theorem B841779 : Blo 838352 841779 := bstep (se 1 (by rfl) ⟨631334, by rfl⟩ : syracuseStep 841779 = 1262669) B1262669
theorem B841795 : Blo 838352 841795 := bstep (se 1 (by rfl) ⟨631346, by rfl⟩ : syracuseStep 841795 = 1262693) B1262693
theorem B841811 : Blo 838352 841811 := bstep (se 1 (by rfl) ⟨631358, by rfl⟩ : syracuseStep 841811 = 1262717) B1262717
theorem B841827 : Blo 838352 841827 := bstep (se 1 (by rfl) ⟨631370, by rfl⟩ : syracuseStep 841827 = 1262741) B1262741
theorem B9099377 : Blo 838352 9099377 := bstep (se 2 (by rfl) ⟨3412266, by rfl⟩ : syracuseStep 9099377 = 6824533) B6824533
theorem B841843 : Blo 838352 841843 := bstep (se 1 (by rfl) ⟨631382, by rfl⟩ : syracuseStep 841843 = 1262765) B1262765
theorem B841859 : Blo 838352 841859 := bstep (se 1 (by rfl) ⟨631394, by rfl⟩ : syracuseStep 841859 = 1262789) B1262789
theorem B1792145 : Blo 838352 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B1890449 : Blo 838352 1890449 := bstep (se 2 (by rfl) ⟨708918, by rfl⟩ : syracuseStep 1890449 = 1417837) B1417837
theorem B841875 : Blo 838352 841875 := bstep (se 1 (by rfl) ⟨631406, by rfl⟩ : syracuseStep 841875 = 1262813) B1262813
theorem B1890467 : Blo 838352 1890467 := bstep (se 1 (by rfl) ⟨1417850, by rfl⟩ : syracuseStep 1890467 = 2835701) B2835701
theorem B841891 : Blo 838352 841891 := bstep (se 1 (by rfl) ⟨631418, by rfl⟩ : syracuseStep 841891 = 1262837) B1262837
theorem B841907 : Blo 838352 841907 := bstep (se 1 (by rfl) ⟨631430, by rfl⟩ : syracuseStep 841907 = 1262861) B1262861
theorem B841923 : Blo 838352 841923 := bstep (se 1 (by rfl) ⟨631442, by rfl⟩ : syracuseStep 841923 = 1262885) B1262885
theorem B841939 : Blo 838352 841939 := bstep (se 1 (by rfl) ⟨631454, by rfl⟩ : syracuseStep 841939 = 1262909) B1262909
theorem B841955 : Blo 838352 841955 := bstep (se 1 (by rfl) ⟨631466, by rfl⟩ : syracuseStep 841955 = 1262933) B1262933
theorem B841971 : Blo 838352 841971 := bstep (se 1 (by rfl) ⟨631478, by rfl⟩ : syracuseStep 841971 = 1262957) B1262957
theorem B841987 : Blo 838352 841987 := bstep (se 1 (by rfl) ⟨631490, by rfl⟩ : syracuseStep 841987 = 1262981) B1262981
theorem B842003 : Blo 838352 842003 := bstep (se 1 (by rfl) ⟨631502, by rfl⟩ : syracuseStep 842003 = 1263005) B1263005
theorem B842019 : Blo 838352 842019 := bstep (se 1 (by rfl) ⟨631514, by rfl⟩ : syracuseStep 842019 = 1263029) B1263029
theorem B842035 : Blo 838352 842035 := bstep (se 1 (by rfl) ⟨631526, by rfl⟩ : syracuseStep 842035 = 1263053) B1263053
theorem B1136963 : Blo 838352 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B2021699 : Blo 838352 2021699 := bstep (se 1 (by rfl) ⟨1516274, by rfl⟩ : syracuseStep 2021699 = 3032549) B3032549
theorem B842051 : Blo 838352 842051 := bstep (se 1 (by rfl) ⟨631538, by rfl⟩ : syracuseStep 842051 = 1263077) B1263077
theorem B2873681 : Blo 838352 2873681 := bstep (se 2 (by rfl) ⟨1077630, by rfl⟩ : syracuseStep 2873681 = 2155261) B2155261
theorem B842067 : Blo 838352 842067 := bstep (se 1 (by rfl) ⟨631550, by rfl⟩ : syracuseStep 842067 = 1263101) B1263101
theorem B842083 : Blo 838352 842083 := bstep (se 1 (by rfl) ⟨631562, by rfl⟩ : syracuseStep 842083 = 1263125) B1263125
theorem B842099 : Blo 838352 842099 := bstep (se 1 (by rfl) ⟨631574, by rfl⟩ : syracuseStep 842099 = 1263149) B1263149
theorem B842115 : Blo 838352 842115 := bstep (se 1 (by rfl) ⟨631586, by rfl⟩ : syracuseStep 842115 = 1263173) B1263173
theorem B842131 : Blo 838352 842131 := bstep (se 1 (by rfl) ⟨631598, by rfl⟩ : syracuseStep 842131 = 1263197) B1263197
theorem B842147 : Blo 838352 842147 := bstep (se 1 (by rfl) ⟨631610, by rfl⟩ : syracuseStep 842147 = 1263221) B1263221
theorem B1890737 : Blo 838352 1890737 := bstep (se 2 (by rfl) ⟨709026, by rfl⟩ : syracuseStep 1890737 = 1418053) B1418053
theorem B842163 : Blo 838352 842163 := bstep (se 1 (by rfl) ⟨631622, by rfl⟩ : syracuseStep 842163 = 1263245) B1263245
theorem B1890755 : Blo 838352 1890755 := bstep (se 1 (by rfl) ⟨1418066, by rfl⟩ : syracuseStep 1890755 = 2836133) B2836133
theorem B842179 : Blo 838352 842179 := bstep (se 1 (by rfl) ⟨631634, by rfl⟩ : syracuseStep 842179 = 1263269) B1263269
theorem B1595857 : Blo 838352 1595857 := bstep (se 2 (by rfl) ⟨598446, by rfl⟩ : syracuseStep 1595857 = 1196893) B1196893
theorem B842195 : Blo 838352 842195 := bstep (se 1 (by rfl) ⟨631646, by rfl⟩ : syracuseStep 842195 = 1263293) B1263293
theorem B842211 : Blo 838352 842211 := bstep (se 1 (by rfl) ⟨631658, by rfl⟩ : syracuseStep 842211 = 1263317) B1263317
theorem B842227 : Blo 838352 842227 := bstep (se 1 (by rfl) ⟨631670, by rfl⟩ : syracuseStep 842227 = 1263341) B1263341
theorem B842243 : Blo 838352 842243 := bstep (se 1 (by rfl) ⟨631682, by rfl⟩ : syracuseStep 842243 = 1263365) B1263365
theorem B2841101 : Blo 838352 2841101 := bstep (se 3 (by rfl) ⟨532706, by rfl⟩ : syracuseStep 2841101 = 1065413) B1065413
theorem B842259 : Blo 838352 842259 := bstep (se 1 (by rfl) ⟨631694, by rfl⟩ : syracuseStep 842259 = 1263389) B1263389
theorem B842275 : Blo 838352 842275 := bstep (se 1 (by rfl) ⟨631706, by rfl⟩ : syracuseStep 842275 = 1263413) B1263413
theorem B842291 : Blo 838352 842291 := bstep (se 1 (by rfl) ⟨631718, by rfl⟩ : syracuseStep 842291 = 1263437) B1263437
theorem B2841155 : Blo 838352 2841155 := bstep (se 1 (by rfl) ⟨2130866, by rfl⟩ : syracuseStep 2841155 = 4261733) B4261733
theorem B842307 : Blo 838352 842307 := bstep (se 1 (by rfl) ⟨631730, by rfl⟩ : syracuseStep 842307 = 1263461) B1263461
theorem B842323 : Blo 838352 842323 := bstep (se 1 (by rfl) ⟨631742, by rfl⟩ : syracuseStep 842323 = 1263485) B1263485
theorem B842339 : Blo 838352 842339 := bstep (se 1 (by rfl) ⟨631754, by rfl⟩ : syracuseStep 842339 = 1263509) B1263509
theorem B1596017 : Blo 838352 1596017 := bstep (se 2 (by rfl) ⟨598506, by rfl⟩ : syracuseStep 1596017 = 1197013) B1197013
theorem B1038995 : Blo 838352 1038995 := bstep (se 1 (by rfl) ⟨779246, by rfl⟩ : syracuseStep 1038995 = 1558493) B1558493
theorem B1891025 : Blo 838352 1891025 := bstep (se 2 (by rfl) ⟨709134, by rfl⟩ : syracuseStep 1891025 = 1418269) B1418269
theorem B1891043 : Blo 838352 1891043 := bstep (se 1 (by rfl) ⟨1418282, by rfl⟩ : syracuseStep 1891043 = 2836565) B2836565
theorem B2841425 : Blo 838352 2841425 := bstep (se 2 (by rfl) ⟨1065534, by rfl⟩ : syracuseStep 2841425 = 2131069) B2131069
theorem B2022275 : Blo 838352 2022275 := bstep (se 1 (by rfl) ⟨1516706, by rfl⟩ : syracuseStep 2022275 = 3033413) B3033413
theorem B2022353 : Blo 838352 2022353 := bstep (se 2 (by rfl) ⟨758382, by rfl⟩ : syracuseStep 2022353 = 1516765) B1516765
theorem B1891313 : Blo 838352 1891313 := bstep (se 2 (by rfl) ⟨709242, by rfl⟩ : syracuseStep 1891313 = 1418485) B1418485
theorem B1596419 : Blo 838352 1596419 := bstep (se 1 (by rfl) ⟨1197314, by rfl⟩ : syracuseStep 1596419 = 2394629) B2394629
theorem B1891331 : Blo 838352 1891331 := bstep (se 1 (by rfl) ⟨1418498, by rfl⟩ : syracuseStep 1891331 = 2836997) B2836997
theorem B2022545 : Blo 838352 2022545 := bstep (se 2 (by rfl) ⟨758454, by rfl⟩ : syracuseStep 2022545 = 1516909) B1516909
theorem B1891601 : Blo 838352 1891601 := bstep (se 2 (by rfl) ⟨709350, by rfl⟩ : syracuseStep 1891601 = 1418701) B1418701
theorem B1891619 : Blo 838352 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B2841965 : Blo 838352 2841965 := bstep (se 3 (by rfl) ⟨532868, by rfl⟩ : syracuseStep 2841965 = 1065737) B1065737
theorem B1793443 : Blo 838352 1793443 := bstep (se 1 (by rfl) ⟨1345082, by rfl⟩ : syracuseStep 1793443 = 2690165) B2690165
theorem B2842019 : Blo 838352 2842019 := bstep (se 1 (by rfl) ⟨2131514, by rfl⟩ : syracuseStep 2842019 = 4263029) B4263029
theorem B2022833 : Blo 838352 2022833 := bstep (se 2 (by rfl) ⟨758562, by rfl⟩ : syracuseStep 2022833 = 1517125) B1517125
theorem B1891889 : Blo 838352 1891889 := bstep (se 2 (by rfl) ⟨709458, by rfl⟩ : syracuseStep 1891889 = 1418917) B1418917
theorem B1891907 : Blo 838352 1891907 := bstep (se 1 (by rfl) ⟨1418930, by rfl⟩ : syracuseStep 1891907 = 2837861) B2837861
theorem B8740493 : Blo 838352 8740493 := bstep (se 3 (by rfl) ⟨1638842, by rfl⟩ : syracuseStep 8740493 = 3277685) B3277685
theorem B2842289 : Blo 838352 2842289 := bstep (se 2 (by rfl) ⟨1065858, by rfl⟩ : syracuseStep 2842289 = 2131717) B2131717
theorem B1892177 : Blo 838352 1892177 := bstep (se 2 (by rfl) ⟨709566, by rfl⟩ : syracuseStep 1892177 = 1419133) B1419133
theorem B1892195 : Blo 838352 1892195 := bstep (se 1 (by rfl) ⟨1419146, by rfl⟩ : syracuseStep 1892195 = 2838293) B2838293
theorem B1597315 : Blo 838352 1597315 := bstep (se 1 (by rfl) ⟨1197986, by rfl⟩ : syracuseStep 1597315 = 2395973) B2395973
theorem B1007635 : Blo 838352 1007635 := bstep (se 1 (by rfl) ⟨755726, by rfl⟩ : syracuseStep 1007635 = 1511453) B1511453
theorem B1597475 : Blo 838352 1597475 := bstep (se 1 (by rfl) ⟨1198106, by rfl⟩ : syracuseStep 1597475 = 2396213) B2396213
theorem B1892465 : Blo 838352 1892465 := bstep (se 2 (by rfl) ⟨709674, by rfl⟩ : syracuseStep 1892465 = 1419349) B1419349
theorem B10379377 : Blo 838352 10379377 := bstep (se 2 (by rfl) ⟨3892266, by rfl⟩ : syracuseStep 10379377 = 7784533) B7784533
theorem B1892483 : Blo 838352 1892483 := bstep (se 1 (by rfl) ⟨1419362, by rfl⟩ : syracuseStep 1892483 = 2838725) B2838725
theorem B2842829 : Blo 838352 2842829 := bstep (se 3 (by rfl) ⟨533030, by rfl⟩ : syracuseStep 2842829 = 1066061) B1066061
theorem B2842883 : Blo 838352 2842883 := bstep (se 1 (by rfl) ⟨2132162, by rfl⟩ : syracuseStep 2842883 = 4264325) B4264325
theorem B2187665 : Blo 838352 2187665 := bstep (se 2 (by rfl) ⟨820374, by rfl⟩ : syracuseStep 2187665 = 1640749) B1640749
theorem B1892753 : Blo 838352 1892753 := bstep (se 2 (by rfl) ⟨709782, by rfl⟩ : syracuseStep 1892753 = 1419565) B1419565
theorem B1892771 : Blo 838352 1892771 := bstep (se 1 (by rfl) ⟨1419578, by rfl⟩ : syracuseStep 1892771 = 2839157) B2839157
theorem B2122321 : Blo 838352 2122321 := bstep (se 2 (by rfl) ⟨795870, by rfl⟩ : syracuseStep 2122321 = 1591741) B1591741
theorem B1794673 : Blo 838352 1794673 := bstep (se 2 (by rfl) ⟨673002, by rfl⟩ : syracuseStep 1794673 = 1346005) B1346005
theorem B4252337 : Blo 838352 4252337 := bstep (se 2 (by rfl) ⟨1594626, by rfl⟩ : syracuseStep 4252337 = 3189253) B3189253
theorem B1893041 : Blo 838352 1893041 := bstep (se 2 (by rfl) ⟨709890, by rfl⟩ : syracuseStep 1893041 = 1419781) B1419781
theorem B1893059 : Blo 838352 1893059 := bstep (se 1 (by rfl) ⟨1419794, by rfl⟩ : syracuseStep 1893059 = 2839589) B2839589
theorem B2122595 : Blo 838352 2122595 := bstep (se 1 (by rfl) ⟨1591946, by rfl⟩ : syracuseStep 2122595 = 3183893) B3183893
theorem B4547441 : Blo 838352 4547441 := bstep (se 2 (by rfl) ⟨1705290, by rfl⟩ : syracuseStep 4547441 = 3410581) B3410581
theorem B1893329 : Blo 838352 1893329 := bstep (se 2 (by rfl) ⟨709998, by rfl⟩ : syracuseStep 1893329 = 1419997) B1419997
theorem B1893347 : Blo 838352 1893347 := bstep (se 1 (by rfl) ⟨1420010, by rfl⟩ : syracuseStep 1893347 = 2840021) B2840021
theorem B2122787 : Blo 838352 2122787 := bstep (se 1 (by rfl) ⟨1592090, by rfl⟩ : syracuseStep 2122787 = 3184181) B3184181
theorem B1598545 : Blo 838352 1598545 := bstep (se 2 (by rfl) ⟨599454, by rfl⟩ : syracuseStep 1598545 = 1198909) B1198909
theorem B943267 : Blo 838352 943267 := bstep (se 1 (by rfl) ⟨707450, by rfl⟩ : syracuseStep 943267 = 1414901) B1414901
theorem B1893617 : Blo 838352 1893617 := bstep (se 2 (by rfl) ⟨710106, by rfl⟩ : syracuseStep 1893617 = 1420213) B1420213
theorem B1893635 : Blo 838352 1893635 := bstep (se 1 (by rfl) ⟨1420226, by rfl⟩ : syracuseStep 1893635 = 2840453) B2840453
theorem B943411 : Blo 838352 943411 := bstep (se 1 (by rfl) ⟨707558, by rfl⟩ : syracuseStep 943411 = 1415117) B1415117
theorem B1434979 : Blo 838352 1434979 := bstep (se 1 (by rfl) ⟨1076234, by rfl⟩ : syracuseStep 1434979 = 2152469) B2152469
theorem B1795459 : Blo 838352 1795459 := bstep (se 1 (by rfl) ⟨1346594, by rfl⟩ : syracuseStep 1795459 = 2693189) B2693189
theorem B943555 : Blo 838352 943555 := bstep (se 1 (by rfl) ⟨707666, by rfl⟩ : syracuseStep 943555 = 1415333) B1415333
theorem B3630563 : Blo 838352 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B2876909 : Blo 838352 2876909 := bstep (se 3 (by rfl) ⟨539420, by rfl⟩ : syracuseStep 2876909 = 1078841) B1078841
theorem B4318733 : Blo 838352 4318733 := bstep (se 3 (by rfl) ⟨809762, by rfl⟩ : syracuseStep 4318733 = 1619525) B1619525
theorem B1893905 : Blo 838352 1893905 := bstep (se 2 (by rfl) ⟨710214, by rfl⟩ : syracuseStep 1893905 = 1420429) B1420429
theorem B1893923 : Blo 838352 1893923 := bstep (se 1 (by rfl) ⟨1420442, by rfl⟩ : syracuseStep 1893923 = 2840885) B2840885
theorem B20473397 : Blo 838352 20473397 := bstep (se 5 (by rfl) ⟨959690, by rfl⟩ : syracuseStep 20473397 = 1919381) B1919381
theorem B943699 : Blo 838352 943699 := bstep (se 1 (by rfl) ⟨707774, by rfl⟩ : syracuseStep 943699 = 1415549) B1415549
theorem B6055523 : Blo 838352 6055523 := bstep (se 1 (by rfl) ⟨4541642, by rfl⟩ : syracuseStep 6055523 = 9083285) B9083285
theorem B3827341 : Blo 838352 3827341 := bstep (se 3 (by rfl) ⟨717626, by rfl⟩ : syracuseStep 3827341 = 1435253) B1435253
theorem B943843 : Blo 838352 943843 := bstep (se 1 (by rfl) ⟨707882, by rfl⟩ : syracuseStep 943843 = 1415765) B1415765
theorem B1009427 : Blo 838352 1009427 := bstep (se 1 (by rfl) ⟨757070, by rfl⟩ : syracuseStep 1009427 = 1514141) B1514141
theorem B1894193 : Blo 838352 1894193 := bstep (se 2 (by rfl) ⟨710322, by rfl⟩ : syracuseStep 1894193 = 1420645) B1420645
theorem B1894211 : Blo 838352 1894211 := bstep (se 1 (by rfl) ⟨1420658, by rfl⟩ : syracuseStep 1894211 = 2841317) B2841317
theorem B2549603 : Blo 838352 2549603 := bstep (se 1 (by rfl) ⟨1912202, by rfl⟩ : syracuseStep 2549603 = 3824405) B3824405
theorem B943987 : Blo 838352 943987 := bstep (se 1 (by rfl) ⟨707990, by rfl⟩ : syracuseStep 943987 = 1415981) B1415981
theorem B2123729 : Blo 838352 2123729 := bstep (se 2 (by rfl) ⟨796398, by rfl⟩ : syracuseStep 2123729 = 1592797) B1592797
theorem B1009667 : Blo 838352 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B2123779 : Blo 838352 2123779 := bstep (se 1 (by rfl) ⟨1592834, by rfl⟩ : syracuseStep 2123779 = 3185669) B3185669
theorem B944131 : Blo 838352 944131 := bstep (se 1 (by rfl) ⟨708098, by rfl⟩ : syracuseStep 944131 = 1416197) B1416197
theorem B1796177 : Blo 838352 1796177 := bstep (se 2 (by rfl) ⟨673566, by rfl⟩ : syracuseStep 1796177 = 1347133) B1347133
theorem B1894481 : Blo 838352 1894481 := bstep (se 2 (by rfl) ⟨710430, by rfl⟩ : syracuseStep 1894481 = 1420861) B1420861
theorem B4253795 : Blo 838352 4253795 := bstep (se 1 (by rfl) ⟨3190346, by rfl⟩ : syracuseStep 4253795 = 6380693) B6380693
theorem B1894499 : Blo 838352 1894499 := bstep (se 1 (by rfl) ⟨1420874, by rfl⟩ : syracuseStep 1894499 = 2841749) B2841749
theorem B2123921 : Blo 838352 2123921 := bstep (se 2 (by rfl) ⟨796470, by rfl⟩ : syracuseStep 2123921 = 1592941) B1592941
theorem B944275 : Blo 838352 944275 := bstep (se 1 (by rfl) ⟨708206, by rfl⟩ : syracuseStep 944275 = 1416413) B1416413
theorem B944419 : Blo 838352 944419 := bstep (se 1 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 944419 = 1416629) B1416629
theorem B1894769 : Blo 838352 1894769 := bstep (se 2 (by rfl) ⟨710538, by rfl⟩ : syracuseStep 1894769 = 1421077) B1421077
theorem B1436033 : Blo 838352 1436033 := bstep (se 2 (by rfl) ⟨538512, by rfl⟩ : syracuseStep 1436033 = 1077025) B1077025
theorem B1894787 : Blo 838352 1894787 := bstep (se 1 (by rfl) ⟨1421090, by rfl⟩ : syracuseStep 1894787 = 2842181) B2842181
theorem B944563 : Blo 838352 944563 := bstep (se 1 (by rfl) ⟨708422, by rfl⟩ : syracuseStep 944563 = 1416845) B1416845
theorem B944707 : Blo 838352 944707 := bstep (se 1 (by rfl) ⟨708530, by rfl⟩ : syracuseStep 944707 = 1417061) B1417061
theorem B1796689 : Blo 838352 1796689 := bstep (se 2 (by rfl) ⟨673758, by rfl⟩ : syracuseStep 1796689 = 1347517) B1347517
theorem B6482531 : Blo 838352 6482531 := bstep (se 1 (by rfl) ⟨4861898, by rfl⟩ : syracuseStep 6482531 = 9723797) B9723797
theorem B1895057 : Blo 838352 1895057 := bstep (se 2 (by rfl) ⟨710646, by rfl⟩ : syracuseStep 1895057 = 1421293) B1421293
theorem B1895075 : Blo 838352 1895075 := bstep (se 1 (by rfl) ⟨1421306, by rfl⟩ : syracuseStep 1895075 = 2842613) B2842613
theorem B944851 : Blo 838352 944851 := bstep (se 1 (by rfl) ⟨708638, by rfl⟩ : syracuseStep 944851 = 1417277) B1417277
theorem B944995 : Blo 838352 944995 := bstep (se 1 (by rfl) ⟨708746, by rfl⟩ : syracuseStep 944995 = 1417493) B1417493
theorem B9563021 : Blo 838352 9563021 := bstep (se 3 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 9563021 = 3586133) B3586133
theorem B4254605 : Blo 838352 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B6384581 : Blo 838352 6384581 := bstep (se 4 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 6384581 = 1197109) B1197109
theorem B945139 : Blo 838352 945139 := bstep (se 1 (by rfl) ⟨708854, by rfl⟩ : syracuseStep 945139 = 1417709) B1417709
theorem B2124913 : Blo 838352 2124913 := bstep (se 2 (by rfl) ⟨796842, by rfl⟩ : syracuseStep 2124913 = 1593685) B1593685
theorem B945283 : Blo 838352 945283 := bstep (se 1 (by rfl) ⟨708962, by rfl⟩ : syracuseStep 945283 = 1417925) B1417925
theorem B2551025 : Blo 838352 2551025 := bstep (se 2 (by rfl) ⟨956634, by rfl⟩ : syracuseStep 2551025 = 1913269) B1913269
theorem B945427 : Blo 838352 945427 := bstep (se 1 (by rfl) ⟨709070, by rfl⟩ : syracuseStep 945427 = 1418141) B1418141
theorem B2125187 : Blo 838352 2125187 := bstep (se 1 (by rfl) ⟨1593890, by rfl⟩ : syracuseStep 2125187 = 3187781) B3187781
theorem B16149901 : Blo 838352 16149901 := bstep (se 3 (by rfl) ⟨3028106, by rfl⟩ : syracuseStep 16149901 = 6056213) B6056213
theorem B945571 : Blo 838352 945571 := bstep (se 1 (by rfl) ⟨709178, by rfl⟩ : syracuseStep 945571 = 1418357) B1418357
theorem B945715 : Blo 838352 945715 := bstep (se 1 (by rfl) ⟨709286, by rfl⟩ : syracuseStep 945715 = 1418573) B1418573
theorem B2125379 : Blo 838352 2125379 := bstep (se 1 (by rfl) ⟨1594034, by rfl⟩ : syracuseStep 2125379 = 3188069) B3188069
theorem B945859 : Blo 838352 945859 := bstep (se 1 (by rfl) ⟨709394, by rfl⟩ : syracuseStep 945859 = 1418789) B1418789
theorem B4321073 : Blo 838352 4321073 := bstep (se 2 (by rfl) ⟨1620402, by rfl⟩ : syracuseStep 4321073 = 3240805) B3240805
theorem B946003 : Blo 838352 946003 := bstep (se 1 (by rfl) ⟨709502, by rfl⟩ : syracuseStep 946003 = 1419005) B1419005
theorem B4779917 : Blo 838352 4779917 := bstep (se 3 (by rfl) ⟨896234, by rfl⟩ : syracuseStep 4779917 = 1792469) B1792469
theorem B946147 : Blo 838352 946147 := bstep (se 1 (by rfl) ⟨709610, by rfl⟩ : syracuseStep 946147 = 1419221) B1419221
theorem B1437731 : Blo 838352 1437731 := bstep (se 1 (by rfl) ⟨1078298, by rfl⟩ : syracuseStep 1437731 = 2156597) B2156597
theorem B1798193 : Blo 838352 1798193 := bstep (se 2 (by rfl) ⟨674322, by rfl⟩ : syracuseStep 1798193 = 1348645) B1348645
theorem B946291 : Blo 838352 946291 := bstep (se 1 (by rfl) ⟨709718, by rfl⟩ : syracuseStep 946291 = 1419437) B1419437
theorem B2388113 : Blo 838352 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B1011955 : Blo 838352 1011955 := bstep (se 1 (by rfl) ⟨758966, by rfl⟩ : syracuseStep 1011955 = 1517933) B1517933
theorem B946435 : Blo 838352 946435 := bstep (se 1 (by rfl) ⟨709826, by rfl⟩ : syracuseStep 946435 = 1419653) B1419653
theorem B946579 : Blo 838352 946579 := bstep (se 1 (by rfl) ⟨709934, by rfl⟩ : syracuseStep 946579 = 1419869) B1419869
theorem B1798595 : Blo 838352 1798595 := bstep (se 1 (by rfl) ⟨1348946, by rfl⟩ : syracuseStep 1798595 = 2697893) B2697893
theorem B2126321 : Blo 838352 2126321 := bstep (se 2 (by rfl) ⟨797370, by rfl⟩ : syracuseStep 2126321 = 1594741) B1594741
theorem B2126371 : Blo 838352 2126371 := bstep (se 1 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 2126371 = 3189557) B3189557
theorem B946723 : Blo 838352 946723 := bstep (se 1 (by rfl) ⟨710042, by rfl⟩ : syracuseStep 946723 = 1420085) B1420085
theorem B2126513 : Blo 838352 2126513 := bstep (se 2 (by rfl) ⟨797442, by rfl⟩ : syracuseStep 2126513 = 1594885) B1594885
theorem B946867 : Blo 838352 946867 := bstep (se 1 (by rfl) ⟨710150, by rfl⟩ : syracuseStep 946867 = 1420301) B1420301
theorem B947011 : Blo 838352 947011 := bstep (se 1 (by rfl) ⟨710258, by rfl⟩ : syracuseStep 947011 = 1420517) B1420517
theorem B2552717 : Blo 838352 2552717 := bstep (se 3 (by rfl) ⟨478634, by rfl⟩ : syracuseStep 2552717 = 957269) B957269
theorem B22999949 : Blo 838352 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B947155 : Blo 838352 947155 := bstep (se 1 (by rfl) ⟨710366, by rfl⟩ : syracuseStep 947155 = 1420733) B1420733
theorem B947299 : Blo 838352 947299 := bstep (se 1 (by rfl) ⟨710474, by rfl⟩ : syracuseStep 947299 = 1420949) B1420949
theorem B32240753 : Blo 838352 32240753 := bstep (se 2 (by rfl) ⟨12090282, by rfl⟩ : syracuseStep 32240753 = 24180565) B24180565
theorem B10744973 : Blo 838352 10744973 := bstep (se 3 (by rfl) ⟨2014682, by rfl⟩ : syracuseStep 10744973 = 4029365) B4029365
theorem B947443 : Blo 838352 947443 := bstep (se 1 (by rfl) ⟨710582, by rfl⟩ : syracuseStep 947443 = 1421165) B1421165
theorem B947587 : Blo 838352 947587 := bstep (se 1 (by rfl) ⟨710690, by rfl⟩ : syracuseStep 947587 = 1421381) B1421381
theorem B6911459 : Blo 838352 6911459 := bstep (se 1 (by rfl) ⟨5183594, by rfl⟩ : syracuseStep 6911459 = 10367189) B10367189
theorem B2389571 : Blo 838352 2389571 := bstep (se 1 (by rfl) ⟨1792178, by rfl⟩ : syracuseStep 2389571 = 3584357) B3584357
theorem B2127505 : Blo 838352 2127505 := bstep (se 2 (by rfl) ⟨797814, by rfl⟩ : syracuseStep 2127505 = 1595629) B1595629
theorem B9565937 : Blo 838352 9565937 := bstep (se 2 (by rfl) ⟨3587226, by rfl⟩ : syracuseStep 9565937 = 7174453) B7174453
theorem B4257521 : Blo 838352 4257521 := bstep (se 2 (by rfl) ⟨1596570, by rfl⟩ : syracuseStep 4257521 = 3193141) B3193141
theorem B1275635 : Blo 838352 1275635 := bstep (se 1 (by rfl) ⟨956726, by rfl⟩ : syracuseStep 1275635 = 1913453) B1913453
theorem B5371717 : Blo 838352 5371717 := bstep (se 4 (by rfl) ⟨503598, by rfl⟩ : syracuseStep 5371717 = 1007197) B1007197
theorem B2127779 : Blo 838352 2127779 := bstep (se 1 (by rfl) ⟨1595834, by rfl⟩ : syracuseStep 2127779 = 3191669) B3191669
theorem B4782149 : Blo 838352 4782149 := bstep (se 4 (by rfl) ⟨448326, by rfl⟩ : syracuseStep 4782149 = 896653) B896653
theorem B2127971 : Blo 838352 2127971 := bstep (se 1 (by rfl) ⟨1595978, by rfl⟩ : syracuseStep 2127971 = 3191957) B3191957
theorem B2390381 : Blo 838352 2390381 := bstep (se 3 (by rfl) ⟨448196, by rfl⟩ : syracuseStep 2390381 = 896393) B896393
theorem B4028849 : Blo 838352 4028849 := bstep (se 2 (by rfl) ⟨1510818, by rfl⟩ : syracuseStep 4028849 = 3021637) B3021637
theorem B5896709 : Blo 838352 5896709 := bstep (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) B1105633
theorem B2390573 : Blo 838352 2390573 := bstep (se 3 (by rfl) ⟨448232, by rfl⟩ : syracuseStep 2390573 = 896465) B896465
theorem B1211041 : Blo 838352 1211041 := bstep (se 2 (by rfl) ⟨454140, by rfl⟩ : syracuseStep 1211041 = 908281) B908281
theorem B4782833 : Blo 838352 4782833 := bstep (se 2 (by rfl) ⟨1793562, by rfl⟩ : syracuseStep 4782833 = 3587125) B3587125
theorem B2620163 : Blo 838352 2620163 := bstep (se 1 (by rfl) ⟨1965122, by rfl⟩ : syracuseStep 2620163 = 3930245) B3930245
theorem B8616773 : Blo 838352 8616773 := bstep (se 4 (by rfl) ⟨807822, by rfl⟩ : syracuseStep 8616773 = 1615645) B1615645
theorem B4848461 : Blo 838352 4848461 := bstep (se 3 (by rfl) ⟨909086, by rfl⟩ : syracuseStep 4848461 = 1818173) B1818173
theorem B1440755 : Blo 838352 1440755 := bstep (se 1 (by rfl) ⟨1080566, by rfl⟩ : syracuseStep 1440755 = 2161133) B2161133
theorem B2128913 : Blo 838352 2128913 := bstep (se 2 (by rfl) ⟨798342, by rfl⟩ : syracuseStep 2128913 = 1596685) B1596685
theorem B2128963 : Blo 838352 2128963 := bstep (se 1 (by rfl) ⟨1596722, by rfl⟩ : syracuseStep 2128963 = 3193445) B3193445
theorem B2686115 : Blo 838352 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B4258979 : Blo 838352 4258979 := bstep (se 1 (by rfl) ⟨3194234, by rfl⟩ : syracuseStep 4258979 = 6388469) B6388469
theorem B1277137 : Blo 838352 1277137 := bstep (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) B957853
theorem B2129105 : Blo 838352 2129105 := bstep (se 2 (by rfl) ⟨798414, by rfl⟩ : syracuseStep 2129105 = 1596829) B1596829
theorem B2391565 : Blo 838352 2391565 := bstep (se 3 (by rfl) ⟨448418, by rfl⟩ : syracuseStep 2391565 = 896837) B896837
theorem B7274083 : Blo 838352 7274083 := bstep (se 1 (by rfl) ⟨5455562, by rfl⟩ : syracuseStep 7274083 = 10911125) B10911125
theorem B11501297 : Blo 838352 11501297 := bstep (se 2 (by rfl) ⟨4312986, by rfl⟩ : syracuseStep 11501297 = 8625973) B8625973
theorem B4259789 : Blo 838352 4259789 := bstep (se 3 (by rfl) ⟨798710, by rfl⟩ : syracuseStep 4259789 = 1597421) B1597421
theorem B1343513 : Blo 838352 1343513 := bstep (se 2 (by rfl) ⟨503817, by rfl⟩ : syracuseStep 1343513 = 1007635) B1007635
theorem B1704089 : Blo 838352 1704089 := bstep (se 2 (by rfl) ⟨639033, by rfl⟩ : syracuseStep 1704089 = 1278067) B1278067
theorem B852203 : Blo 838352 852203 := bstep (se 1 (by rfl) ⟨639152, by rfl⟩ : syracuseStep 852203 = 1278305) B1278305
theorem B4260113 : Blo 838352 4260113 := bstep (se 2 (by rfl) ⟨1597542, by rfl⟩ : syracuseStep 4260113 = 3195085) B3195085
theorem B4260275 : Blo 838352 4260275 := bstep (se 1 (by rfl) ⟨3195206, by rfl⟩ : syracuseStep 4260275 = 6390413) B6390413
theorem B2687539 : Blo 838352 2687539 := bstep (se 1 (by rfl) ⟨2015654, by rfl⟩ : syracuseStep 2687539 = 4031309) B4031309
theorem B2392669 : Blo 838352 2392669 := bstep (se 3 (by rfl) ⟨448625, by rfl⟩ : syracuseStep 2392669 = 897251) B897251
theorem B1704577 : Blo 838352 1704577 := bstep (se 2 (by rfl) ⟨639216, by rfl⟩ : syracuseStep 1704577 = 1278433) B1278433
theorem B4784791 : Blo 838352 4784791 := bstep (se 1 (by rfl) ⟨3588593, by rfl⟩ : syracuseStep 4784791 = 7177187) B7177187
theorem B2130583 : Blo 838352 2130583 := bstep (se 1 (by rfl) ⟨1597937, by rfl⟩ : syracuseStep 2130583 = 3195875) B3195875
theorem B2687705 : Blo 838352 2687705 := bstep (se 2 (by rfl) ⟨1007889, by rfl⟩ : syracuseStep 2687705 = 2015779) B2015779
theorem B2392897 : Blo 838352 2392897 := bstep (se 2 (by rfl) ⟨897336, by rfl⟩ : syracuseStep 2392897 = 1794673) B1794673
theorem B852823 : Blo 838352 852823 := bstep (se 1 (by rfl) ⟨639617, by rfl⟩ : syracuseStep 852823 = 1279235) B1279235
theorem B1639283 : Blo 838352 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B2131019 : Blo 838352 2131019 := bstep (se 1 (by rfl) ⟨1598264, by rfl⟩ : syracuseStep 2131019 = 3196529) B3196529
theorem B2393239 : Blo 838352 2393239 := bstep (se 1 (by rfl) ⟨1794929, by rfl⟩ : syracuseStep 2393239 = 3589859) B3589859
theorem B2131393 : Blo 838352 2131393 := bstep (se 2 (by rfl) ⟨799272, by rfl⟩ : syracuseStep 2131393 = 1598545) B1598545
theorem B2688473 : Blo 838352 2688473 := bstep (se 2 (by rfl) ⟨1008177, by rfl⟩ : syracuseStep 2688473 = 2016355) B2016355
theorem B27198989 : Blo 838352 27198989 := bstep (se 3 (by rfl) ⟨5099810, by rfl⟩ : syracuseStep 27198989 = 10199621) B10199621
theorem B2557619 : Blo 838352 2557619 := bstep (se 1 (by rfl) ⟨1918214, by rfl⟩ : syracuseStep 2557619 = 3836429) B3836429
theorem B2393945 : Blo 838352 2393945 := bstep (se 2 (by rfl) ⟨897729, by rfl⟩ : syracuseStep 2393945 = 1795459) B1795459
theorem B2688985 : Blo 838352 2688985 := bstep (se 2 (by rfl) ⟨1008369, by rfl⟩ : syracuseStep 2688985 = 2016739) B2016739
theorem B2131991 : Blo 838352 2131991 := bstep (se 1 (by rfl) ⟨1598993, by rfl⟩ : syracuseStep 2131991 = 3197987) B3197987
theorem B4262219 : Blo 838352 4262219 := bstep (se 1 (by rfl) ⟨3196664, by rfl⟩ : syracuseStep 4262219 = 6393329) B6393329
theorem B1706483 : Blo 838352 1706483 := bstep (se 1 (by rfl) ⟨1279862, by rfl⟩ : syracuseStep 1706483 = 2559725) B2559725
theorem B7178827 : Blo 838352 7178827 := bstep (se 1 (by rfl) ⟨5384120, by rfl⟩ : syracuseStep 7178827 = 10768241) B10768241
theorem B7179101 : Blo 838352 7179101 := bstep (se 3 (by rfl) ⟨1346081, by rfl⟩ : syracuseStep 7179101 = 2692163) B2692163
theorem B2690113 : Blo 838352 2690113 := bstep (se 2 (by rfl) ⟨1008792, by rfl⟩ : syracuseStep 2690113 = 2017585) B2017585
theorem B2395585 : Blo 838352 2395585 := bstep (se 2 (by rfl) ⟨898344, by rfl⟩ : syracuseStep 2395585 = 1796689) B1796689
theorem B6458885 : Blo 838352 6458885 := bstep (se 4 (by rfl) ⟨605520, by rfl⟩ : syracuseStep 6458885 = 1211041) B1211041
theorem B2428481 : Blo 838352 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B1511129 : Blo 838352 1511129 := bstep (se 2 (by rfl) ⟨566673, by rfl⟩ : syracuseStep 1511129 = 1133347) B1133347
theorem B3411715 : Blo 838352 3411715 := bstep (se 1 (by rfl) ⟨2558786, by rfl⟩ : syracuseStep 3411715 = 5117573) B5117573
theorem B2559833 : Blo 838352 2559833 := bstep (se 2 (by rfl) ⟨959937, by rfl⟩ : syracuseStep 2559833 = 1919875) B1919875
theorem B30609251 : Blo 838352 30609251 := bstep (se 1 (by rfl) ⟨22956938, by rfl⟩ : syracuseStep 30609251 = 45913877) B45913877
theorem B7180163 : Blo 838352 7180163 := bstep (se 1 (by rfl) ⟨5385122, by rfl⟩ : syracuseStep 7180163 = 10770245) B10770245
theorem B7671757 : Blo 838352 7671757 := bstep (se 3 (by rfl) ⟨1438454, by rfl⟩ : syracuseStep 7671757 = 2876909) B2876909
theorem B6131717 : Blo 838352 6131717 := bstep (se 4 (by rfl) ⟨574848, by rfl⟩ : syracuseStep 6131717 = 1149697) B1149697
theorem B4264001 : Blo 838352 4264001 := bstep (se 2 (by rfl) ⟨1599000, by rfl⟩ : syracuseStep 4264001 = 3198001) B3198001
theorem B6066251 : Blo 838352 6066251 := bstep (se 1 (by rfl) ⟨4549688, by rfl⟩ : syracuseStep 6066251 = 9099377) B9099377
theorem B1511705 : Blo 838352 1511705 := bstep (se 2 (by rfl) ⟨566889, by rfl⟩ : syracuseStep 1511705 = 1133779) B1133779
theorem B21533201 : Blo 838352 21533201 := bstep (se 2 (by rfl) ⟨8074950, by rfl⟩ : syracuseStep 21533201 = 16149901) B16149901
theorem B1348183 : Blo 838352 1348183 := bstep (se 1 (by rfl) ⟨1011137, by rfl⟩ : syracuseStep 1348183 = 2022275) B2022275
theorem B1348235 : Blo 838352 1348235 := bstep (se 1 (by rfl) ⟨1011176, by rfl⟩ : syracuseStep 1348235 = 2022353) B2022353
theorem B2691805 : Blo 838352 2691805 := bstep (se 3 (by rfl) ⟨504713, by rfl⟩ : syracuseStep 2691805 = 1009427) B1009427
theorem B1348363 : Blo 838352 1348363 := bstep (se 1 (by rfl) ⟨1011272, by rfl⟩ : syracuseStep 1348363 = 2022545) B2022545
theorem B1512641 : Blo 838352 1512641 := bstep (se 2 (by rfl) ⟨567240, by rfl⟩ : syracuseStep 1512641 = 1134481) B1134481
theorem B2692445 : Blo 838352 2692445 := bstep (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) B1009667
theorem B1349273 : Blo 838352 1349273 := bstep (se 2 (by rfl) ⟨505977, by rfl⟩ : syracuseStep 1349273 = 1011955) B1011955
theorem B1415063 : Blo 838352 1415063 := bstep (se 1 (by rfl) ⟨1061297, by rfl⟩ : syracuseStep 1415063 = 2122595) B2122595
theorem B1415191 : Blo 838352 1415191 := bstep (se 1 (by rfl) ⟨1061393, by rfl⟩ : syracuseStep 1415191 = 2122787) B2122787
theorem B4037015 : Blo 838352 4037015 := bstep (se 1 (by rfl) ⟨3027761, by rfl⟩ : syracuseStep 4037015 = 6055523) B6055523
theorem B5380739 : Blo 838352 5380739 := bstep (se 1 (by rfl) ⟨4035554, by rfl⟩ : syracuseStep 5380739 = 8071109) B8071109
theorem B1415819 : Blo 838352 1415819 := bstep (se 1 (by rfl) ⟨1061864, by rfl⟩ : syracuseStep 1415819 = 2123729) B2123729
theorem B1415947 : Blo 838352 1415947 := bstep (se 1 (by rfl) ⟨1061960, by rfl⟩ : syracuseStep 1415947 = 2123921) B2123921
theorem B3152729 : Blo 838352 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B2595673 : Blo 838352 2595673 := bstep (se 2 (by rfl) ⟨973377, by rfl⟩ : syracuseStep 2595673 = 1946755) B1946755
theorem B1416089 : Blo 838352 1416089 := bstep (se 2 (by rfl) ⟨531033, by rfl⟩ : syracuseStep 1416089 = 1062067) B1062067
theorem B957355 : Blo 838352 957355 := bstep (se 1 (by rfl) ⟨718016, by rfl⟩ : syracuseStep 957355 = 1436033) B1436033
theorem B1416217 : Blo 838352 1416217 := bstep (se 2 (by rfl) ⟨531081, by rfl⟩ : syracuseStep 1416217 = 1062163) B1062163
theorem B3185837 : Blo 838352 3185837 := bstep (se 3 (by rfl) ⟨597344, by rfl⟩ : syracuseStep 3185837 = 1194689) B1194689
theorem B18455813 : Blo 838352 18455813 := bstep (se 4 (by rfl) ⟨1730232, by rfl⟩ : syracuseStep 18455813 = 3460465) B3460465
theorem B2727233 : Blo 838352 2727233 := bstep (se 2 (by rfl) ⟨1022712, by rfl⟩ : syracuseStep 2727233 = 2045425) B2045425
theorem B1416791 : Blo 838352 1416791 := bstep (se 1 (by rfl) ⟨1062593, by rfl⟩ : syracuseStep 1416791 = 2125187) B2125187
theorem B1416919 : Blo 838352 1416919 := bstep (se 1 (by rfl) ⟨1062689, by rfl⟩ : syracuseStep 1416919 = 2125379) B2125379
theorem B4792081 : Blo 838352 4792081 := bstep (se 2 (by rfl) ⟨1797030, by rfl⟩ : syracuseStep 4792081 = 3594061) B3594061
theorem B3186611 : Blo 838352 3186611 := bstep (se 1 (by rfl) ⟨2389958, by rfl⟩ : syracuseStep 3186611 = 4779917) B4779917
theorem B2072537 : Blo 838352 2072537 := bstep (se 2 (by rfl) ⟨777201, by rfl⟩ : syracuseStep 2072537 = 1554403) B1554403
theorem B958487 : Blo 838352 958487 := bstep (se 1 (by rfl) ⟨718865, by rfl⟩ : syracuseStep 958487 = 1437731) B1437731
theorem B1417547 : Blo 838352 1417547 := bstep (se 1 (by rfl) ⟨1063160, by rfl⟩ : syracuseStep 1417547 = 2126321) B2126321
theorem B1417675 : Blo 838352 1417675 := bstep (se 1 (by rfl) ⟨1063256, by rfl⟩ : syracuseStep 1417675 = 2126513) B2126513
theorem B1417817 : Blo 838352 1417817 := bstep (se 2 (by rfl) ⟨531681, by rfl⟩ : syracuseStep 1417817 = 1063363) B1063363
theorem B10756759 : Blo 838352 10756759 := bstep (se 1 (by rfl) ⟨8067569, by rfl⟩ : syracuseStep 10756759 = 16135139) B16135139
theorem B1417945 : Blo 838352 1417945 := bstep (se 2 (by rfl) ⟨531729, by rfl⟩ : syracuseStep 1417945 = 1063459) B1063459
theorem B1418519 : Blo 838352 1418519 := bstep (se 1 (by rfl) ⟨1063889, by rfl⟩ : syracuseStep 1418519 = 2127779) B2127779
theorem B3188099 : Blo 838352 3188099 := bstep (se 1 (by rfl) ⟨2391074, by rfl⟩ : syracuseStep 3188099 = 4782149) B4782149
theorem B1418647 : Blo 838352 1418647 := bstep (se 1 (by rfl) ⟨1063985, by rfl⟩ : syracuseStep 1418647 = 2127971) B2127971
theorem B3188555 : Blo 838352 3188555 := bstep (se 1 (by rfl) ⟨2391416, by rfl⟩ : syracuseStep 3188555 = 4782833) B4782833
theorem B1746775 : Blo 838352 1746775 := bstep (se 1 (by rfl) ⟨1310081, by rfl⟩ : syracuseStep 1746775 = 2620163) B2620163
theorem B5744515 : Blo 838352 5744515 := bstep (se 1 (by rfl) ⟨4308386, by rfl⟩ : syracuseStep 5744515 = 8616773) B8616773
theorem B960503 : Blo 838352 960503 := bstep (se 1 (by rfl) ⟨720377, by rfl⟩ : syracuseStep 960503 = 1440755) B1440755
theorem B1419275 : Blo 838352 1419275 := bstep (se 1 (by rfl) ⟨1064456, by rfl⟩ : syracuseStep 1419275 = 2128913) B2128913
theorem B3188753 : Blo 838352 3188753 := bstep (se 2 (by rfl) ⟨1195782, by rfl⟩ : syracuseStep 3188753 = 2391565) B2391565
theorem B2697239 : Blo 838352 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B14526533 : Blo 838352 14526533 := bstep (se 4 (by rfl) ⟨1361862, by rfl⟩ : syracuseStep 14526533 = 2723725) B2723725
theorem B1419403 : Blo 838352 1419403 := bstep (se 1 (by rfl) ⟨1064552, by rfl⟩ : syracuseStep 1419403 = 2129105) B2129105
theorem B1419545 : Blo 838352 1419545 := bstep (se 2 (by rfl) ⟨532329, by rfl⟩ : syracuseStep 1419545 = 1064659) B1064659
theorem B4041053 : Blo 838352 4041053 := bstep (se 3 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 4041053 = 1515395) B1515395
theorem B1419673 : Blo 838352 1419673 := bstep (se 2 (by rfl) ⟨532377, by rfl⟩ : syracuseStep 1419673 = 1064755) B1064755
theorem B4532867 : Blo 838352 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B3189527 : Blo 838352 3189527 := bstep (se 1 (by rfl) ⟨2392145, by rfl⟩ : syracuseStep 3189527 = 4784291) B4784291
theorem B895799 : Blo 838352 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B3582785 : Blo 838352 3582785 := bstep (se 2 (by rfl) ⟨1343544, by rfl⟩ : syracuseStep 3582785 = 2687089) B2687089
theorem B13839169 : Blo 838352 13839169 := bstep (se 2 (by rfl) ⟨5189688, by rfl⟩ : syracuseStep 13839169 = 10379377) B10379377
theorem B1616755 : Blo 838352 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B1420247 : Blo 838352 1420247 := bstep (se 1 (by rfl) ⟨1065185, by rfl⟩ : syracuseStep 1420247 = 2130371) B2130371
theorem B3189725 : Blo 838352 3189725 := bstep (se 3 (by rfl) ⟨598073, by rfl⟩ : syracuseStep 3189725 = 1196147) B1196147
theorem B1420375 : Blo 838352 1420375 := bstep (se 1 (by rfl) ⟨1065281, by rfl⟩ : syracuseStep 1420375 = 2130563) B2130563
theorem B4795523 : Blo 838352 4795523 := bstep (se 1 (by rfl) ⟨3596642, by rfl⟩ : syracuseStep 4795523 = 7193285) B7193285
theorem B18656407 : Blo 838352 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B2829491 : Blo 838352 2829491 := bstep (se 1 (by rfl) ⟨2122118, by rfl⟩ : syracuseStep 2829491 = 4244237) B4244237
theorem B2698571 : Blo 838352 2698571 := bstep (se 1 (by rfl) ⟨2023928, by rfl⟩ : syracuseStep 2698571 = 4047857) B4047857
theorem B2829761 : Blo 838352 2829761 := bstep (se 2 (by rfl) ⟨1061160, by rfl⟩ : syracuseStep 2829761 = 2122321) B2122321
theorem B2272715 : Blo 838352 2272715 := bstep (se 1 (by rfl) ⟨1704536, by rfl⟩ : syracuseStep 2272715 = 3409073) B3409073
theorem B1421003 : Blo 838352 1421003 := bstep (se 1 (by rfl) ⟨1065752, by rfl⟩ : syracuseStep 1421003 = 2131505) B2131505
theorem B2272985 : Blo 838352 2272985 := bstep (se 2 (by rfl) ⟨852369, by rfl⟩ : syracuseStep 2272985 = 1704739) B1704739
theorem B3583709 : Blo 838352 3583709 := bstep (se 3 (by rfl) ⟨671945, by rfl⟩ : syracuseStep 3583709 = 1343891) B1343891
theorem B6369029 : Blo 838352 6369029 := bstep (se 4 (by rfl) ⟨597096, by rfl⟩ : syracuseStep 6369029 = 1194193) B1194193
theorem B1421131 : Blo 838352 1421131 := bstep (se 1 (by rfl) ⟨1065848, by rfl⟩ : syracuseStep 1421131 = 2131697) B2131697
theorem B896875 : Blo 838352 896875 := bstep (se 1 (by rfl) ⟨672656, by rfl⟩ : syracuseStep 896875 = 1345313) B1345313
theorem B1421273 : Blo 838352 1421273 := bstep (se 2 (by rfl) ⟨532977, by rfl⟩ : syracuseStep 1421273 = 1065955) B1065955
theorem B2830301 : Blo 838352 2830301 := bstep (se 3 (by rfl) ⟨530681, by rfl⟩ : syracuseStep 2830301 = 1061363) B1061363
theorem B1421401 : Blo 838352 1421401 := bstep (se 2 (by rfl) ⟨533025, by rfl⟩ : syracuseStep 1421401 = 1066051) B1066051
theorem B1257611 : Blo 838352 1257611 := bstep (se 1 (by rfl) ⟨943208, by rfl⟩ : syracuseStep 1257611 = 1886417) B1886417
theorem B1257623 : Blo 838352 1257623 := bstep (se 1 (by rfl) ⟨943217, by rfl⟩ : syracuseStep 1257623 = 1886435) B1886435
theorem B1257689 : Blo 838352 1257689 := bstep (se 2 (by rfl) ⟨471633, by rfl⟩ : syracuseStep 1257689 = 943267) B943267
theorem B6828293 : Blo 838352 6828293 := bstep (se 4 (by rfl) ⟨640152, by rfl⟩ : syracuseStep 6828293 = 1280305) B1280305
theorem B1257803 : Blo 838352 1257803 := bstep (se 1 (by rfl) ⟨943352, by rfl⟩ : syracuseStep 1257803 = 1886705) B1886705
theorem B1257815 : Blo 838352 1257815 := bstep (se 1 (by rfl) ⟨943361, by rfl⟩ : syracuseStep 1257815 = 1886723) B1886723
theorem B1257881 : Blo 838352 1257881 := bstep (se 2 (by rfl) ⟨471705, by rfl⟩ : syracuseStep 1257881 = 943411) B943411
theorem B1913305 : Blo 838352 1913305 := bstep (se 2 (by rfl) ⟨717489, by rfl⟩ : syracuseStep 1913305 = 1434979) B1434979
theorem B1257995 : Blo 838352 1257995 := bstep (se 1 (by rfl) ⟨943496, by rfl⟩ : syracuseStep 1257995 = 1886993) B1886993
theorem B1258007 : Blo 838352 1258007 := bstep (se 1 (by rfl) ⟨943505, by rfl⟩ : syracuseStep 1258007 = 1887011) B1887011
theorem B1258073 : Blo 838352 1258073 := bstep (se 2 (by rfl) ⟨471777, by rfl⟩ : syracuseStep 1258073 = 943555) B943555
theorem B1061515 : Blo 838352 1061515 := bstep (se 1 (by rfl) ⟨796136, by rfl⟩ : syracuseStep 1061515 = 1592273) B1592273
theorem B1258187 : Blo 838352 1258187 := bstep (se 1 (by rfl) ⟨943640, by rfl⟩ : syracuseStep 1258187 = 1887281) B1887281
theorem B1258199 : Blo 838352 1258199 := bstep (se 1 (by rfl) ⟨943649, by rfl⟩ : syracuseStep 1258199 = 1887299) B1887299
theorem B897815 : Blo 838352 897815 := bstep (se 1 (by rfl) ⟨673361, by rfl⟩ : syracuseStep 897815 = 1346723) B1346723
theorem B1258265 : Blo 838352 1258265 := bstep (se 2 (by rfl) ⟨471849, by rfl⟩ : syracuseStep 1258265 = 943699) B943699
theorem B3191683 : Blo 838352 3191683 := bstep (se 1 (by rfl) ⟨2393762, by rfl⟩ : syracuseStep 3191683 = 4787525) B4787525
theorem B1258379 : Blo 838352 1258379 := bstep (se 1 (by rfl) ⟨943784, by rfl⟩ : syracuseStep 1258379 = 1887569) B1887569
theorem B1258391 : Blo 838352 1258391 := bstep (se 1 (by rfl) ⟨943793, by rfl⟩ : syracuseStep 1258391 = 1887587) B1887587
theorem B1258457 : Blo 838352 1258457 := bstep (se 2 (by rfl) ⟨471921, by rfl⟩ : syracuseStep 1258457 = 943843) B943843
theorem B2831435 : Blo 838352 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B1258571 : Blo 838352 1258571 := bstep (se 1 (by rfl) ⟨943928, by rfl⟩ : syracuseStep 1258571 = 1887857) B1887857
theorem B1258583 : Blo 838352 1258583 := bstep (se 1 (by rfl) ⟨943937, by rfl⟩ : syracuseStep 1258583 = 1887875) B1887875
theorem B1258649 : Blo 838352 1258649 := bstep (se 2 (by rfl) ⟨471993, by rfl⟩ : syracuseStep 1258649 = 943987) B943987
theorem B3191987 : Blo 838352 3191987 := bstep (se 1 (by rfl) ⟨2393990, by rfl⟩ : syracuseStep 3191987 = 4787981) B4787981
theorem B1258763 : Blo 838352 1258763 := bstep (se 1 (by rfl) ⟨944072, by rfl⟩ : syracuseStep 1258763 = 1888145) B1888145
theorem B1258775 : Blo 838352 1258775 := bstep (se 1 (by rfl) ⟨944081, by rfl⟩ : syracuseStep 1258775 = 1888163) B1888163
theorem B2831705 : Blo 838352 2831705 := bstep (se 2 (by rfl) ⟨1061889, by rfl⟩ : syracuseStep 2831705 = 2123779) B2123779
theorem B1258841 : Blo 838352 1258841 := bstep (se 2 (by rfl) ⟨472065, by rfl⟩ : syracuseStep 1258841 = 944131) B944131
theorem B1258955 : Blo 838352 1258955 := bstep (se 1 (by rfl) ⟨944216, by rfl⟩ : syracuseStep 1258955 = 1888433) B1888433
theorem B1258967 : Blo 838352 1258967 := bstep (se 1 (by rfl) ⟨944225, by rfl⟩ : syracuseStep 1258967 = 1888451) B1888451
theorem B3028441 : Blo 838352 3028441 := bstep (se 2 (by rfl) ⟨1135665, by rfl⟩ : syracuseStep 3028441 = 2271331) B2271331
theorem B1259033 : Blo 838352 1259033 := bstep (se 2 (by rfl) ⟨472137, by rfl⟩ : syracuseStep 1259033 = 944275) B944275
theorem B1062487 : Blo 838352 1062487 := bstep (se 1 (by rfl) ⟨796865, by rfl⟩ : syracuseStep 1062487 = 1593731) B1593731
theorem B1259147 : Blo 838352 1259147 := bstep (se 1 (by rfl) ⟨944360, by rfl⟩ : syracuseStep 1259147 = 1888721) B1888721
theorem B1259159 : Blo 838352 1259159 := bstep (se 1 (by rfl) ⟨944369, by rfl⟩ : syracuseStep 1259159 = 1888739) B1888739
theorem B2078387 : Blo 838352 2078387 := bstep (se 1 (by rfl) ⟨1558790, by rfl⟩ : syracuseStep 2078387 = 3117581) B3117581
theorem B1259225 : Blo 838352 1259225 := bstep (se 2 (by rfl) ⟨472209, by rfl⟩ : syracuseStep 1259225 = 944419) B944419
theorem B10368773 : Blo 838352 10368773 := bstep (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) B1944145
theorem B3192641 : Blo 838352 3192641 := bstep (se 2 (by rfl) ⟨1197240, by rfl⟩ : syracuseStep 3192641 = 2394481) B2394481
theorem B1259339 : Blo 838352 1259339 := bstep (se 1 (by rfl) ⟨944504, by rfl⟩ : syracuseStep 1259339 = 1889009) B1889009
theorem B1259351 : Blo 838352 1259351 := bstep (se 1 (by rfl) ⟨944513, by rfl⟩ : syracuseStep 1259351 = 1889027) B1889027
theorem B13645685 : Blo 838352 13645685 := bstep (se 5 (by rfl) ⟨639641, by rfl⟩ : syracuseStep 13645685 = 1279283) B1279283
theorem B1259417 : Blo 838352 1259417 := bstep (se 2 (by rfl) ⟨472281, by rfl⟩ : syracuseStep 1259417 = 944563) B944563
theorem B24262577 : Blo 838352 24262577 := bstep (se 2 (by rfl) ⟨9098466, by rfl⟩ : syracuseStep 24262577 = 18196933) B18196933
theorem B1259531 : Blo 838352 1259531 := bstep (se 1 (by rfl) ⟨944648, by rfl⟩ : syracuseStep 1259531 = 1889297) B1889297
theorem B2832407 : Blo 838352 2832407 := bstep (se 1 (by rfl) ⟨2124305, by rfl⟩ : syracuseStep 2832407 = 4248611) B4248611
theorem B1259543 : Blo 838352 1259543 := bstep (se 1 (by rfl) ⟨944657, by rfl⟩ : syracuseStep 1259543 = 1889315) B1889315
theorem B9549899 : Blo 838352 9549899 := bstep (se 1 (by rfl) ⟨7162424, by rfl⟩ : syracuseStep 9549899 = 14324849) B14324849
theorem B1259609 : Blo 838352 1259609 := bstep (se 2 (by rfl) ⟨472353, by rfl⟩ : syracuseStep 1259609 = 944707) B944707
theorem B6371459 : Blo 838352 6371459 := bstep (se 1 (by rfl) ⟨4778594, by rfl⟩ : syracuseStep 6371459 = 9557189) B9557189
theorem B40941719 : Blo 838352 40941719 := bstep (se 1 (by rfl) ⟨30706289, by rfl⟩ : syracuseStep 40941719 = 61412579) B61412579
theorem B1259723 : Blo 838352 1259723 := bstep (se 1 (by rfl) ⟨944792, by rfl⟩ : syracuseStep 1259723 = 1889585) B1889585
theorem B1259735 : Blo 838352 1259735 := bstep (se 1 (by rfl) ⟨944801, by rfl⟩ : syracuseStep 1259735 = 1889603) B1889603
theorem B1259801 : Blo 838352 1259801 := bstep (se 2 (by rfl) ⟨472425, by rfl⟩ : syracuseStep 1259801 = 944851) B944851
theorem B1259915 : Blo 838352 1259915 := bstep (se 1 (by rfl) ⟨944936, by rfl⟩ : syracuseStep 1259915 = 1889873) B1889873
theorem B1063307 : Blo 838352 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B1259927 : Blo 838352 1259927 := bstep (se 1 (by rfl) ⟨944945, by rfl⟩ : syracuseStep 1259927 = 1889891) B1889891
theorem B1259993 : Blo 838352 1259993 := bstep (se 2 (by rfl) ⟨472497, by rfl⟩ : syracuseStep 1259993 = 944995) B944995
theorem B2832947 : Blo 838352 2832947 := bstep (se 1 (by rfl) ⟨2124710, by rfl⟩ : syracuseStep 2832947 = 4249421) B4249421
theorem B1260107 : Blo 838352 1260107 := bstep (se 1 (by rfl) ⟨945080, by rfl⟩ : syracuseStep 1260107 = 1890161) B1890161
theorem B1260119 : Blo 838352 1260119 := bstep (se 1 (by rfl) ⟨945089, by rfl⟩ : syracuseStep 1260119 = 1890179) B1890179
theorem B1260185 : Blo 838352 1260185 := bstep (se 2 (by rfl) ⟨472569, by rfl⟩ : syracuseStep 1260185 = 945139) B945139
theorem B1620695 : Blo 838352 1620695 := bstep (se 1 (by rfl) ⟨1215521, by rfl⟩ : syracuseStep 1620695 = 2431043) B2431043
theorem B1194763 : Blo 838352 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B1260299 : Blo 838352 1260299 := bstep (se 1 (by rfl) ⟨945224, by rfl⟩ : syracuseStep 1260299 = 1890449) B1890449
theorem B1260311 : Blo 838352 1260311 := bstep (se 1 (by rfl) ⟨945233, by rfl⟩ : syracuseStep 1260311 = 1890467) B1890467
theorem B2833217 : Blo 838352 2833217 := bstep (se 2 (by rfl) ⟨1062456, by rfl⟩ : syracuseStep 2833217 = 2124913) B2124913
theorem B1260377 : Blo 838352 1260377 := bstep (se 2 (by rfl) ⟨472641, by rfl⟩ : syracuseStep 1260377 = 945283) B945283
theorem B1915787 : Blo 838352 1915787 := bstep (se 1 (by rfl) ⟨1436840, by rfl⟩ : syracuseStep 1915787 = 2873681) B2873681
theorem B62307269 : Blo 838352 62307269 := bstep (se 4 (by rfl) ⟨5841306, by rfl⟩ : syracuseStep 62307269 = 11682613) B11682613
theorem B1260491 : Blo 838352 1260491 := bstep (se 1 (by rfl) ⟨945368, by rfl⟩ : syracuseStep 1260491 = 1890737) B1890737
theorem B1260503 : Blo 838352 1260503 := bstep (se 1 (by rfl) ⟨945377, by rfl⟩ : syracuseStep 1260503 = 1890755) B1890755
theorem B3587075 : Blo 838352 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B1260569 : Blo 838352 1260569 := bstep (se 2 (by rfl) ⟨472713, by rfl⟩ : syracuseStep 1260569 = 945427) B945427
theorem B3193901 : Blo 838352 3193901 := bstep (se 3 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 3193901 = 1197713) B1197713
theorem B1064011 : Blo 838352 1064011 := bstep (se 1 (by rfl) ⟨798008, by rfl⟩ : syracuseStep 1064011 = 1596017) B1596017
theorem B3193931 : Blo 838352 3193931 := bstep (se 1 (by rfl) ⟨2395448, by rfl⟩ : syracuseStep 3193931 = 4790897) B4790897
theorem B1260683 : Blo 838352 1260683 := bstep (se 1 (by rfl) ⟨945512, by rfl⟩ : syracuseStep 1260683 = 1891025) B1891025
theorem B1260695 : Blo 838352 1260695 := bstep (se 1 (by rfl) ⟨945521, by rfl⟩ : syracuseStep 1260695 = 1891043) B1891043
theorem B1260761 : Blo 838352 1260761 := bstep (se 2 (by rfl) ⟨472785, by rfl⟩ : syracuseStep 1260761 = 945571) B945571
theorem B1260875 : Blo 838352 1260875 := bstep (se 1 (by rfl) ⟨945656, by rfl⟩ : syracuseStep 1260875 = 1891313) B1891313
theorem B1064279 : Blo 838352 1064279 := bstep (se 1 (by rfl) ⟨798209, by rfl⟩ : syracuseStep 1064279 = 1596419) B1596419
theorem B1260887 : Blo 838352 1260887 := bstep (se 1 (by rfl) ⟨945665, by rfl⟩ : syracuseStep 1260887 = 1891331) B1891331
theorem B2833757 : Blo 838352 2833757 := bstep (se 3 (by rfl) ⟨531329, by rfl⟩ : syracuseStep 2833757 = 1062659) B1062659
theorem B6045029 : Blo 838352 6045029 := bstep (se 4 (by rfl) ⟨566721, by rfl⟩ : syracuseStep 6045029 = 1133443) B1133443
theorem B1260953 : Blo 838352 1260953 := bstep (se 2 (by rfl) ⟨472857, by rfl⟩ : syracuseStep 1260953 = 945715) B945715
theorem B1261067 : Blo 838352 1261067 := bstep (se 1 (by rfl) ⟨945800, by rfl⟩ : syracuseStep 1261067 = 1891601) B1891601
theorem B1261079 : Blo 838352 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B1261145 : Blo 838352 1261145 := bstep (se 2 (by rfl) ⟨472929, by rfl⟩ : syracuseStep 1261145 = 945859) B945859
theorem B1261259 : Blo 838352 1261259 := bstep (se 1 (by rfl) ⟨945944, by rfl⟩ : syracuseStep 1261259 = 1891889) B1891889
theorem B1261271 : Blo 838352 1261271 := bstep (se 1 (by rfl) ⟨945953, by rfl⟩ : syracuseStep 1261271 = 1891907) B1891907
theorem B3194585 : Blo 838352 3194585 := bstep (se 2 (by rfl) ⟨1197969, by rfl⟩ : syracuseStep 3194585 = 2395939) B2395939
theorem B1261337 : Blo 838352 1261337 := bstep (se 2 (by rfl) ⟨473001, by rfl⟩ : syracuseStep 1261337 = 946003) B946003
theorem B1261451 : Blo 838352 1261451 := bstep (se 1 (by rfl) ⟨946088, by rfl⟩ : syracuseStep 1261451 = 1892177) B1892177
theorem B1261463 : Blo 838352 1261463 := bstep (se 1 (by rfl) ⟨946097, by rfl⟩ : syracuseStep 1261463 = 1892195) B1892195
theorem B3030977 : Blo 838352 3030977 := bstep (se 2 (by rfl) ⟨1136616, by rfl⟩ : syracuseStep 3030977 = 2273233) B2273233
theorem B1195993 : Blo 838352 1195993 := bstep (se 2 (by rfl) ⟨448497, by rfl⟩ : syracuseStep 1195993 = 896995) B896995
theorem B1261529 : Blo 838352 1261529 := bstep (se 2 (by rfl) ⟨473073, by rfl⟩ : syracuseStep 1261529 = 946147) B946147
theorem B3194903 : Blo 838352 3194903 := bstep (se 1 (by rfl) ⟨2396177, by rfl⟩ : syracuseStep 3194903 = 4792355) B4792355
theorem B1064983 : Blo 838352 1064983 := bstep (se 1 (by rfl) ⟨798737, by rfl⟩ : syracuseStep 1064983 = 1597475) B1597475
theorem B22986827 : Blo 838352 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B1261643 : Blo 838352 1261643 := bstep (se 1 (by rfl) ⟨946232, by rfl⟩ : syracuseStep 1261643 = 1892465) B1892465
theorem B1261655 : Blo 838352 1261655 := bstep (se 1 (by rfl) ⟨946241, by rfl⟩ : syracuseStep 1261655 = 1892483) B1892483
theorem B1261721 : Blo 838352 1261721 := bstep (se 2 (by rfl) ⟨473145, by rfl⟩ : syracuseStep 1261721 = 946291) B946291
theorem B1458443 : Blo 838352 1458443 := bstep (se 1 (by rfl) ⟨1093832, by rfl⟩ : syracuseStep 1458443 = 2187665) B2187665
theorem B1261835 : Blo 838352 1261835 := bstep (se 1 (by rfl) ⟨946376, by rfl⟩ : syracuseStep 1261835 = 1892753) B1892753
theorem B1261847 : Blo 838352 1261847 := bstep (se 1 (by rfl) ⟨946385, by rfl⟩ : syracuseStep 1261847 = 1892771) B1892771
theorem B7192907 : Blo 838352 7192907 := bstep (se 1 (by rfl) ⟨5394680, by rfl⟩ : syracuseStep 7192907 = 10789361) B10789361
theorem B1261913 : Blo 838352 1261913 := bstep (se 2 (by rfl) ⟨473217, by rfl⟩ : syracuseStep 1261913 = 946435) B946435
theorem B2834891 : Blo 838352 2834891 := bstep (se 1 (by rfl) ⟨2126168, by rfl⟩ : syracuseStep 2834891 = 4252337) B4252337
theorem B1262027 : Blo 838352 1262027 := bstep (se 1 (by rfl) ⟨946520, by rfl⟩ : syracuseStep 1262027 = 1893041) B1893041
theorem B1262039 : Blo 838352 1262039 := bstep (se 1 (by rfl) ⟨946529, by rfl⟩ : syracuseStep 1262039 = 1893059) B1893059
theorem B1262105 : Blo 838352 1262105 := bstep (se 2 (by rfl) ⟨473289, by rfl⟩ : syracuseStep 1262105 = 946579) B946579
theorem B3031627 : Blo 838352 3031627 := bstep (se 1 (by rfl) ⟨2273720, by rfl⟩ : syracuseStep 3031627 = 4547441) B4547441
theorem B1262219 : Blo 838352 1262219 := bstep (se 1 (by rfl) ⟨946664, by rfl⟩ : syracuseStep 1262219 = 1893329) B1893329
theorem B1262231 : Blo 838352 1262231 := bstep (se 1 (by rfl) ⟨946673, by rfl⟩ : syracuseStep 1262231 = 1893347) B1893347
theorem B3195571 : Blo 838352 3195571 := bstep (se 1 (by rfl) ⟨2396678, by rfl⟩ : syracuseStep 3195571 = 4793357) B4793357
theorem B2835161 : Blo 838352 2835161 := bstep (se 2 (by rfl) ⟨1063185, by rfl⟩ : syracuseStep 2835161 = 2126371) B2126371
theorem B1262297 : Blo 838352 1262297 := bstep (se 2 (by rfl) ⟨473361, by rfl⟩ : syracuseStep 1262297 = 946723) B946723
theorem B1262411 : Blo 838352 1262411 := bstep (se 1 (by rfl) ⟨946808, by rfl⟩ : syracuseStep 1262411 = 1893617) B1893617
theorem B1262423 : Blo 838352 1262423 := bstep (se 1 (by rfl) ⟨946817, by rfl⟩ : syracuseStep 1262423 = 1893635) B1893635
theorem B3031901 : Blo 838352 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B5391197 : Blo 838352 5391197 := bstep (se 3 (by rfl) ⟨1010849, by rfl⟩ : syracuseStep 5391197 = 2021699) B2021699
theorem B1262489 : Blo 838352 1262489 := bstep (se 2 (by rfl) ⟨473433, by rfl⟩ : syracuseStep 1262489 = 946867) B946867
theorem B1262603 : Blo 838352 1262603 := bstep (se 1 (by rfl) ⟨946952, by rfl⟩ : syracuseStep 1262603 = 1893905) B1893905
theorem B1262615 : Blo 838352 1262615 := bstep (se 1 (by rfl) ⟨946961, by rfl⟩ : syracuseStep 1262615 = 1893923) B1893923
theorem B13648931 : Blo 838352 13648931 := bstep (se 1 (by rfl) ⟨10236698, by rfl⟩ : syracuseStep 13648931 = 20473397) B20473397
theorem B1262681 : Blo 838352 1262681 := bstep (se 2 (by rfl) ⟨473505, by rfl⟩ : syracuseStep 1262681 = 947011) B947011
theorem B1262795 : Blo 838352 1262795 := bstep (se 1 (by rfl) ⟨947096, by rfl⟩ : syracuseStep 1262795 = 1894193) B1894193
theorem B1262807 : Blo 838352 1262807 := bstep (se 1 (by rfl) ⟨947105, by rfl⟩ : syracuseStep 1262807 = 1894211) B1894211
theorem B1197337 : Blo 838352 1197337 := bstep (se 2 (by rfl) ⟨449001, by rfl⟩ : syracuseStep 1197337 = 898003) B898003
theorem B1262873 : Blo 838352 1262873 := bstep (se 2 (by rfl) ⟨473577, by rfl⟩ : syracuseStep 1262873 = 947155) B947155
theorem B1197451 : Blo 838352 1197451 := bstep (se 1 (by rfl) ⟨898088, by rfl⟩ : syracuseStep 1197451 = 1796177) B1796177
theorem B1262987 : Blo 838352 1262987 := bstep (se 1 (by rfl) ⟨947240, by rfl⟩ : syracuseStep 1262987 = 1894481) B1894481
theorem B2835863 : Blo 838352 2835863 := bstep (se 1 (by rfl) ⟨2126897, by rfl⟩ : syracuseStep 2835863 = 4253795) B4253795
theorem B1262999 : Blo 838352 1262999 := bstep (se 1 (by rfl) ⟨947249, by rfl⟩ : syracuseStep 1262999 = 1894499) B1894499
theorem B6374861 : Blo 838352 6374861 := bstep (se 3 (by rfl) ⟨1195286, by rfl⟩ : syracuseStep 6374861 = 2390573) B2390573
theorem B1263065 : Blo 838352 1263065 := bstep (se 2 (by rfl) ⟨473649, by rfl⟩ : syracuseStep 1263065 = 947299) B947299
theorem B1263179 : Blo 838352 1263179 := bstep (se 1 (by rfl) ⟨947384, by rfl⟩ : syracuseStep 1263179 = 1894769) B1894769
theorem B1263191 : Blo 838352 1263191 := bstep (se 1 (by rfl) ⟨947393, by rfl⟩ : syracuseStep 1263191 = 1894787) B1894787
theorem B6801047 : Blo 838352 6801047 := bstep (se 1 (by rfl) ⟨5100785, by rfl⟩ : syracuseStep 6801047 = 10201571) B10201571
theorem B1263257 : Blo 838352 1263257 := bstep (se 2 (by rfl) ⟨473721, by rfl⟩ : syracuseStep 1263257 = 947443) B947443
theorem B2016971 : Blo 838352 2016971 := bstep (se 1 (by rfl) ⟨1512728, by rfl⟩ : syracuseStep 2016971 = 3025457) B3025457
theorem B4245209 : Blo 838352 4245209 := bstep (se 2 (by rfl) ⟨1591953, by rfl⟩ : syracuseStep 4245209 = 3183907) B3183907
theorem B1263371 : Blo 838352 1263371 := bstep (se 1 (by rfl) ⟨947528, by rfl⟩ : syracuseStep 1263371 = 1895057) B1895057
theorem B1263383 : Blo 838352 1263383 := bstep (se 1 (by rfl) ⟨947537, by rfl⟩ : syracuseStep 1263383 = 1895075) B1895075
theorem B1263449 : Blo 838352 1263449 := bstep (se 2 (by rfl) ⟨473793, by rfl⟩ : syracuseStep 1263449 = 947587) B947587
theorem B3196817 : Blo 838352 3196817 := bstep (se 2 (by rfl) ⟨1198806, by rfl⟩ : syracuseStep 3196817 = 2397613) B2397613
theorem B14337971 : Blo 838352 14337971 := bstep (se 1 (by rfl) ⟨10753478, by rfl⟩ : syracuseStep 14337971 = 21506957) B21506957
theorem B6375347 : Blo 838352 6375347 := bstep (se 1 (by rfl) ⟨4781510, by rfl⟩ : syracuseStep 6375347 = 9563021) B9563021
theorem B2836403 : Blo 838352 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B2836673 : Blo 838352 2836673 := bstep (se 2 (by rfl) ⟨1063752, by rfl⟩ : syracuseStep 2836673 = 2127505) B2127505
theorem B1886489 : Blo 838352 1886489 := bstep (se 2 (by rfl) ⟨707433, by rfl⟩ : syracuseStep 1886489 = 1414867) B1414867
theorem B1886579 : Blo 838352 1886579 := bstep (se 1 (by rfl) ⟨1414934, by rfl⟩ : syracuseStep 1886579 = 2829869) B2829869
theorem B1886615 : Blo 838352 1886615 := bstep (se 1 (by rfl) ⟨1414961, by rfl⟩ : syracuseStep 1886615 = 2829923) B2829923
theorem B7162289 : Blo 838352 7162289 := bstep (se 2 (by rfl) ⟨2685858, by rfl⟩ : syracuseStep 7162289 = 5371717) B5371717
theorem B1886795 : Blo 838352 1886795 := bstep (se 1 (by rfl) ⟨1415096, by rfl⟩ : syracuseStep 1886795 = 2830193) B2830193
theorem B3066443 : Blo 838352 3066443 := bstep (se 1 (by rfl) ⟨2299832, by rfl⟩ : syracuseStep 3066443 = 4599665) B4599665
theorem B3197515 : Blo 838352 3197515 := bstep (se 1 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 3197515 = 4796273) B4796273
theorem B1886849 : Blo 838352 1886849 := bstep (se 2 (by rfl) ⟨707568, by rfl⟩ : syracuseStep 1886849 = 1415137) B1415137
theorem B1198795 : Blo 838352 1198795 := bstep (se 1 (by rfl) ⟨899096, by rfl⟩ : syracuseStep 1198795 = 1798193) B1798193
theorem B838359 : Blo 838352 838359 := bstep (se 1 (by rfl) ⟨628769, by rfl⟩ : syracuseStep 838359 = 1257539) B1257539
theorem B2018009 : Blo 838352 2018009 := bstep (se 2 (by rfl) ⟨756753, by rfl⟩ : syracuseStep 2018009 = 1513507) B1513507
theorem B2837213 : Blo 838352 2837213 := bstep (se 3 (by rfl) ⟨531977, by rfl⟩ : syracuseStep 2837213 = 1063955) B1063955
theorem B838379 : Blo 838352 838379 := bstep (se 1 (by rfl) ⟨628784, by rfl⟩ : syracuseStep 838379 = 1257569) B1257569
theorem B838391 : Blo 838352 838391 := bstep (se 1 (by rfl) ⟨628793, by rfl⟩ : syracuseStep 838391 = 1257587) B1257587
theorem B838411 : Blo 838352 838411 := bstep (se 1 (by rfl) ⟨628808, by rfl⟩ : syracuseStep 838411 = 1257617) B1257617
theorem B1592075 : Blo 838352 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B838423 : Blo 838352 838423 := bstep (se 1 (by rfl) ⟨628817, by rfl⟩ : syracuseStep 838423 = 1257635) B1257635
theorem B838443 : Blo 838352 838443 := bstep (se 1 (by rfl) ⟨628832, by rfl⟩ : syracuseStep 838443 = 1257665) B1257665
theorem B838455 : Blo 838352 838455 := bstep (se 1 (by rfl) ⟨628841, by rfl⟩ : syracuseStep 838455 = 1257683) B1257683
theorem B1592129 : Blo 838352 1592129 := bstep (se 2 (by rfl) ⟨597048, by rfl⟩ : syracuseStep 1592129 = 1194097) B1194097
theorem B838475 : Blo 838352 838475 := bstep (se 1 (by rfl) ⟨628856, by rfl⟩ : syracuseStep 838475 = 1257713) B1257713
theorem B2018123 : Blo 838352 2018123 := bstep (se 1 (by rfl) ⟨1513592, by rfl⟩ : syracuseStep 2018123 = 3027185) B3027185
theorem B838487 : Blo 838352 838487 := bstep (se 1 (by rfl) ⟨628865, by rfl⟩ : syracuseStep 838487 = 1257731) B1257731
theorem B1887065 : Blo 838352 1887065 := bstep (se 2 (by rfl) ⟨707649, by rfl⟩ : syracuseStep 1887065 = 1415299) B1415299
theorem B3197789 : Blo 838352 3197789 := bstep (se 3 (by rfl) ⟨599585, by rfl⟩ : syracuseStep 3197789 = 1199171) B1199171
theorem B838507 : Blo 838352 838507 := bstep (se 1 (by rfl) ⟨628880, by rfl⟩ : syracuseStep 838507 = 1257761) B1257761
theorem B838519 : Blo 838352 838519 := bstep (se 1 (by rfl) ⟨628889, by rfl⟩ : syracuseStep 838519 = 1257779) B1257779
theorem B838539 : Blo 838352 838539 := bstep (se 1 (by rfl) ⟨628904, by rfl⟩ : syracuseStep 838539 = 1257809) B1257809
theorem B838551 : Blo 838352 838551 := bstep (se 1 (by rfl) ⟨628913, by rfl⟩ : syracuseStep 838551 = 1257827) B1257827
theorem B838571 : Blo 838352 838571 := bstep (se 1 (by rfl) ⟨628928, by rfl⟩ : syracuseStep 838571 = 1257857) B1257857
theorem B1887155 : Blo 838352 1887155 := bstep (se 1 (by rfl) ⟨1415366, by rfl⟩ : syracuseStep 1887155 = 2830733) B2830733
theorem B838583 : Blo 838352 838583 := bstep (se 1 (by rfl) ⟨628937, by rfl⟩ : syracuseStep 838583 = 1257875) B1257875
theorem B838603 : Blo 838352 838603 := bstep (se 1 (by rfl) ⟨628952, by rfl⟩ : syracuseStep 838603 = 1257905) B1257905
theorem B838615 : Blo 838352 838615 := bstep (se 1 (by rfl) ⟨628961, by rfl⟩ : syracuseStep 838615 = 1257923) B1257923
theorem B1887191 : Blo 838352 1887191 := bstep (se 1 (by rfl) ⟨1415393, by rfl⟩ : syracuseStep 1887191 = 2830787) B2830787
theorem B1199063 : Blo 838352 1199063 := bstep (se 1 (by rfl) ⟨899297, by rfl⟩ : syracuseStep 1199063 = 1798595) B1798595
theorem B838635 : Blo 838352 838635 := bstep (se 1 (by rfl) ⟨628976, by rfl⟩ : syracuseStep 838635 = 1257953) B1257953
theorem B838647 : Blo 838352 838647 := bstep (se 1 (by rfl) ⟨628985, by rfl⟩ : syracuseStep 838647 = 1257971) B1257971
theorem B838667 : Blo 838352 838667 := bstep (se 1 (by rfl) ⟨629000, by rfl⟩ : syracuseStep 838667 = 1258001) B1258001
theorem B838679 : Blo 838352 838679 := bstep (se 1 (by rfl) ⟨629009, by rfl⟩ : syracuseStep 838679 = 1258019) B1258019
theorem B3591191 : Blo 838352 3591191 := bstep (se 1 (by rfl) ⟨2693393, by rfl⟩ : syracuseStep 3591191 = 5386787) B5386787
theorem B838699 : Blo 838352 838699 := bstep (se 1 (by rfl) ⟨629024, by rfl⟩ : syracuseStep 838699 = 1258049) B1258049
theorem B838711 : Blo 838352 838711 := bstep (se 1 (by rfl) ⟨629033, by rfl⟩ : syracuseStep 838711 = 1258067) B1258067
theorem B838731 : Blo 838352 838731 := bstep (se 1 (by rfl) ⟨629048, by rfl⟩ : syracuseStep 838731 = 1258097) B1258097
theorem B838743 : Blo 838352 838743 := bstep (se 1 (by rfl) ⟨629057, by rfl⟩ : syracuseStep 838743 = 1258115) B1258115
theorem B838763 : Blo 838352 838763 := bstep (se 1 (by rfl) ⟨629072, by rfl⟩ : syracuseStep 838763 = 1258145) B1258145
theorem B838775 : Blo 838352 838775 := bstep (se 1 (by rfl) ⟨629081, by rfl⟩ : syracuseStep 838775 = 1258163) B1258163
theorem B838795 : Blo 838352 838795 := bstep (se 1 (by rfl) ⟨629096, by rfl⟩ : syracuseStep 838795 = 1258193) B1258193
theorem B1887371 : Blo 838352 1887371 := bstep (se 1 (by rfl) ⟨1415528, by rfl⟩ : syracuseStep 1887371 = 2831057) B2831057
theorem B838807 : Blo 838352 838807 := bstep (se 1 (by rfl) ⟨629105, by rfl⟩ : syracuseStep 838807 = 1258211) B1258211
theorem B838827 : Blo 838352 838827 := bstep (se 1 (by rfl) ⟨629120, by rfl⟩ : syracuseStep 838827 = 1258241) B1258241
theorem B838839 : Blo 838352 838839 := bstep (se 1 (by rfl) ⟨629129, by rfl⟩ : syracuseStep 838839 = 1258259) B1258259
theorem B1887425 : Blo 838352 1887425 := bstep (se 2 (by rfl) ⟨707784, by rfl⟩ : syracuseStep 1887425 = 1415569) B1415569
theorem B838859 : Blo 838352 838859 := bstep (se 1 (by rfl) ⟨629144, by rfl⟩ : syracuseStep 838859 = 1258289) B1258289
theorem B838871 : Blo 838352 838871 := bstep (se 1 (by rfl) ⟨629153, by rfl⟩ : syracuseStep 838871 = 1258307) B1258307
theorem B838891 : Blo 838352 838891 := bstep (se 1 (by rfl) ⟨629168, by rfl⟩ : syracuseStep 838891 = 1258337) B1258337
theorem B838903 : Blo 838352 838903 := bstep (se 1 (by rfl) ⟨629177, by rfl⟩ : syracuseStep 838903 = 1258355) B1258355
theorem B838923 : Blo 838352 838923 := bstep (se 1 (by rfl) ⟨629192, by rfl⟩ : syracuseStep 838923 = 1258385) B1258385
theorem B838935 : Blo 838352 838935 := bstep (se 1 (by rfl) ⟨629201, by rfl⟩ : syracuseStep 838935 = 1258403) B1258403
theorem B838955 : Blo 838352 838955 := bstep (se 1 (by rfl) ⟨629216, by rfl⟩ : syracuseStep 838955 = 1258433) B1258433
theorem B4246829 : Blo 838352 4246829 := bstep (se 3 (by rfl) ⟨796280, by rfl⟩ : syracuseStep 4246829 = 1592561) B1592561
theorem B838967 : Blo 838352 838967 := bstep (se 1 (by rfl) ⟨629225, by rfl⟩ : syracuseStep 838967 = 1258451) B1258451
theorem B838987 : Blo 838352 838987 := bstep (se 1 (by rfl) ⟨629240, by rfl⟩ : syracuseStep 838987 = 1258481) B1258481
theorem B3591499 : Blo 838352 3591499 := bstep (se 1 (by rfl) ⟨2693624, by rfl⟩ : syracuseStep 3591499 = 5387249) B5387249
theorem B838999 : Blo 838352 838999 := bstep (se 1 (by rfl) ⟨629249, by rfl⟩ : syracuseStep 838999 = 1258499) B1258499
theorem B6376805 : Blo 838352 6376805 := bstep (se 4 (by rfl) ⟨597825, by rfl⟩ : syracuseStep 6376805 = 1195651) B1195651
theorem B839019 : Blo 838352 839019 := bstep (se 1 (by rfl) ⟨629264, by rfl⟩ : syracuseStep 839019 = 1258529) B1258529
theorem B839031 : Blo 838352 839031 := bstep (se 1 (by rfl) ⟨629273, by rfl⟩ : syracuseStep 839031 = 1258547) B1258547
theorem B839051 : Blo 838352 839051 := bstep (se 1 (by rfl) ⟨629288, by rfl⟩ : syracuseStep 839051 = 1258577) B1258577
theorem B839063 : Blo 838352 839063 := bstep (se 1 (by rfl) ⟨629297, by rfl⟩ : syracuseStep 839063 = 1258595) B1258595
theorem B1887641 : Blo 838352 1887641 := bstep (se 2 (by rfl) ⟨707865, by rfl⟩ : syracuseStep 1887641 = 1415731) B1415731
theorem B839083 : Blo 838352 839083 := bstep (se 1 (by rfl) ⟨629312, by rfl⟩ : syracuseStep 839083 = 1258625) B1258625
theorem B7163315 : Blo 838352 7163315 := bstep (se 1 (by rfl) ⟨5372486, by rfl⟩ : syracuseStep 7163315 = 10744973) B10744973
theorem B839095 : Blo 838352 839095 := bstep (se 1 (by rfl) ⟨629321, by rfl⟩ : syracuseStep 839095 = 1258643) B1258643
theorem B839115 : Blo 838352 839115 := bstep (se 1 (by rfl) ⟨629336, by rfl⟩ : syracuseStep 839115 = 1258673) B1258673
theorem B839127 : Blo 838352 839127 := bstep (se 1 (by rfl) ⟨629345, by rfl⟩ : syracuseStep 839127 = 1258691) B1258691
theorem B839147 : Blo 838352 839147 := bstep (se 1 (by rfl) ⟨629360, by rfl⟩ : syracuseStep 839147 = 1258721) B1258721
theorem B1887731 : Blo 838352 1887731 := bstep (se 1 (by rfl) ⟨1415798, by rfl⟩ : syracuseStep 1887731 = 2831597) B2831597
theorem B839159 : Blo 838352 839159 := bstep (se 1 (by rfl) ⟨629369, by rfl⟩ : syracuseStep 839159 = 1258739) B1258739
theorem B839179 : Blo 838352 839179 := bstep (se 1 (by rfl) ⟨629384, by rfl⟩ : syracuseStep 839179 = 1258769) B1258769
theorem B1887767 : Blo 838352 1887767 := bstep (se 1 (by rfl) ⟨1415825, by rfl⟩ : syracuseStep 1887767 = 2831651) B2831651
theorem B839191 : Blo 838352 839191 := bstep (se 1 (by rfl) ⟨629393, by rfl⟩ : syracuseStep 839191 = 1258787) B1258787
theorem B839211 : Blo 838352 839211 := bstep (se 1 (by rfl) ⟨629408, by rfl⟩ : syracuseStep 839211 = 1258817) B1258817
theorem B839223 : Blo 838352 839223 := bstep (se 1 (by rfl) ⟨629417, by rfl⟩ : syracuseStep 839223 = 1258835) B1258835
theorem B839243 : Blo 838352 839243 := bstep (se 1 (by rfl) ⟨629432, by rfl⟩ : syracuseStep 839243 = 1258865) B1258865
theorem B839255 : Blo 838352 839255 := bstep (se 1 (by rfl) ⟨629441, by rfl⟩ : syracuseStep 839255 = 1258883) B1258883
theorem B3591773 : Blo 838352 3591773 := bstep (se 3 (by rfl) ⟨673457, by rfl⟩ : syracuseStep 3591773 = 1346915) B1346915
theorem B839275 : Blo 838352 839275 := bstep (se 1 (by rfl) ⟨629456, by rfl⟩ : syracuseStep 839275 = 1258913) B1258913
theorem B839287 : Blo 838352 839287 := bstep (se 1 (by rfl) ⟨629465, by rfl⟩ : syracuseStep 839287 = 1258931) B1258931
theorem B839307 : Blo 838352 839307 := bstep (se 1 (by rfl) ⟨629480, by rfl⟩ : syracuseStep 839307 = 1258961) B1258961
theorem B839319 : Blo 838352 839319 := bstep (se 1 (by rfl) ⟨629489, by rfl⟩ : syracuseStep 839319 = 1258979) B1258979
theorem B4607639 : Blo 838352 4607639 := bstep (se 1 (by rfl) ⟨3455729, by rfl⟩ : syracuseStep 4607639 = 6911459) B6911459
theorem B839339 : Blo 838352 839339 := bstep (se 1 (by rfl) ⟨629504, by rfl⟩ : syracuseStep 839339 = 1259009) B1259009
theorem B839351 : Blo 838352 839351 := bstep (se 1 (by rfl) ⟨629513, by rfl⟩ : syracuseStep 839351 = 1259027) B1259027
theorem B1887947 : Blo 838352 1887947 := bstep (se 1 (by rfl) ⟨1415960, by rfl⟩ : syracuseStep 1887947 = 2831921) B2831921
theorem B839371 : Blo 838352 839371 := bstep (se 1 (by rfl) ⟨629528, by rfl⟩ : syracuseStep 839371 = 1259057) B1259057
theorem B1593047 : Blo 838352 1593047 := bstep (se 1 (by rfl) ⟨1194785, by rfl⟩ : syracuseStep 1593047 = 2389571) B2389571
theorem B839383 : Blo 838352 839383 := bstep (se 1 (by rfl) ⟨629537, by rfl⟩ : syracuseStep 839383 = 1259075) B1259075
theorem B839403 : Blo 838352 839403 := bstep (se 1 (by rfl) ⟨629552, by rfl⟩ : syracuseStep 839403 = 1259105) B1259105
theorem B839415 : Blo 838352 839415 := bstep (se 1 (by rfl) ⟨629561, by rfl⟩ : syracuseStep 839415 = 1259123) B1259123
theorem B1888001 : Blo 838352 1888001 := bstep (se 2 (by rfl) ⟨708000, by rfl⟩ : syracuseStep 1888001 = 1416001) B1416001
theorem B839435 : Blo 838352 839435 := bstep (se 1 (by rfl) ⟨629576, by rfl⟩ : syracuseStep 839435 = 1259153) B1259153
theorem B839447 : Blo 838352 839447 := bstep (se 1 (by rfl) ⟨629585, by rfl⟩ : syracuseStep 839447 = 1259171) B1259171
theorem B839467 : Blo 838352 839467 := bstep (se 1 (by rfl) ⟨629600, by rfl⟩ : syracuseStep 839467 = 1259201) B1259201
theorem B5394221 : Blo 838352 5394221 := bstep (se 3 (by rfl) ⟨1011416, by rfl⟩ : syracuseStep 5394221 = 2022833) B2022833
theorem B839479 : Blo 838352 839479 := bstep (se 1 (by rfl) ⟨629609, by rfl⟩ : syracuseStep 839479 = 1259219) B1259219
theorem B839499 : Blo 838352 839499 := bstep (se 1 (by rfl) ⟨629624, by rfl⟩ : syracuseStep 839499 = 1259249) B1259249
theorem B6377291 : Blo 838352 6377291 := bstep (se 1 (by rfl) ⟨4782968, by rfl⟩ : syracuseStep 6377291 = 9565937) B9565937
theorem B2838347 : Blo 838352 2838347 := bstep (se 1 (by rfl) ⟨2128760, by rfl⟩ : syracuseStep 2838347 = 4257521) B4257521
theorem B839511 : Blo 838352 839511 := bstep (se 1 (by rfl) ⟨629633, by rfl⟩ : syracuseStep 839511 = 1259267) B1259267
theorem B839531 : Blo 838352 839531 := bstep (se 1 (by rfl) ⟨629648, by rfl⟩ : syracuseStep 839531 = 1259297) B1259297
theorem B839543 : Blo 838352 839543 := bstep (se 1 (by rfl) ⟨629657, by rfl⟩ : syracuseStep 839543 = 1259315) B1259315
theorem B839563 : Blo 838352 839563 := bstep (se 1 (by rfl) ⟨629672, by rfl⟩ : syracuseStep 839563 = 1259345) B1259345
theorem B839575 : Blo 838352 839575 := bstep (se 1 (by rfl) ⟨629681, by rfl⟩ : syracuseStep 839575 = 1259363) B1259363
theorem B839595 : Blo 838352 839595 := bstep (se 1 (by rfl) ⟨629696, by rfl⟩ : syracuseStep 839595 = 1259393) B1259393
theorem B839607 : Blo 838352 839607 := bstep (se 1 (by rfl) ⟨629705, by rfl⟩ : syracuseStep 839607 = 1259411) B1259411
theorem B839627 : Blo 838352 839627 := bstep (se 1 (by rfl) ⟨629720, by rfl⟩ : syracuseStep 839627 = 1259441) B1259441
theorem B839639 : Blo 838352 839639 := bstep (se 1 (by rfl) ⟨629729, by rfl⟩ : syracuseStep 839639 = 1259459) B1259459
theorem B1888217 : Blo 838352 1888217 := bstep (se 2 (by rfl) ⟨708081, by rfl⟩ : syracuseStep 1888217 = 1416163) B1416163
theorem B839659 : Blo 838352 839659 := bstep (se 1 (by rfl) ⟨629744, by rfl⟩ : syracuseStep 839659 = 1259489) B1259489
theorem B839671 : Blo 838352 839671 := bstep (se 1 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 839671 = 1259507) B1259507
theorem B839691 : Blo 838352 839691 := bstep (se 1 (by rfl) ⟨629768, by rfl⟩ : syracuseStep 839691 = 1259537) B1259537
theorem B839703 : Blo 838352 839703 := bstep (se 1 (by rfl) ⟨629777, by rfl⟩ : syracuseStep 839703 = 1259555) B1259555
theorem B839723 : Blo 838352 839723 := bstep (se 1 (by rfl) ⟨629792, by rfl⟩ : syracuseStep 839723 = 1259585) B1259585
theorem B1888307 : Blo 838352 1888307 := bstep (se 1 (by rfl) ⟨1416230, by rfl⟩ : syracuseStep 1888307 = 2832461) B2832461
theorem B839735 : Blo 838352 839735 := bstep (se 1 (by rfl) ⟨629801, by rfl⟩ : syracuseStep 839735 = 1259603) B1259603
theorem B839755 : Blo 838352 839755 := bstep (se 1 (by rfl) ⟨629816, by rfl⟩ : syracuseStep 839755 = 1259633) B1259633
theorem B1888343 : Blo 838352 1888343 := bstep (se 1 (by rfl) ⟨1416257, by rfl⟩ : syracuseStep 1888343 = 2832515) B2832515
theorem B839767 : Blo 838352 839767 := bstep (se 1 (by rfl) ⟨629825, by rfl⟩ : syracuseStep 839767 = 1259651) B1259651
theorem B2838617 : Blo 838352 2838617 := bstep (se 2 (by rfl) ⟨1064481, by rfl⟩ : syracuseStep 2838617 = 2128963) B2128963
theorem B839787 : Blo 838352 839787 := bstep (se 1 (by rfl) ⟨629840, by rfl⟩ : syracuseStep 839787 = 1259681) B1259681
theorem B839799 : Blo 838352 839799 := bstep (se 1 (by rfl) ⟨629849, by rfl⟩ : syracuseStep 839799 = 1259699) B1259699
theorem B839819 : Blo 838352 839819 := bstep (se 1 (by rfl) ⟨629864, by rfl⟩ : syracuseStep 839819 = 1259729) B1259729
theorem B839831 : Blo 838352 839831 := bstep (se 1 (by rfl) ⟨629873, by rfl⟩ : syracuseStep 839831 = 1259747) B1259747
theorem B839851 : Blo 838352 839851 := bstep (se 1 (by rfl) ⟨629888, by rfl⟩ : syracuseStep 839851 = 1259777) B1259777
theorem B839863 : Blo 838352 839863 := bstep (se 1 (by rfl) ⟨629897, by rfl⟩ : syracuseStep 839863 = 1259795) B1259795
theorem B839883 : Blo 838352 839883 := bstep (se 1 (by rfl) ⟨629912, by rfl⟩ : syracuseStep 839883 = 1259825) B1259825
theorem B839895 : Blo 838352 839895 := bstep (se 1 (by rfl) ⟨629921, by rfl⟩ : syracuseStep 839895 = 1259843) B1259843
theorem B839915 : Blo 838352 839915 := bstep (se 1 (by rfl) ⟨629936, by rfl⟩ : syracuseStep 839915 = 1259873) B1259873
theorem B1593587 : Blo 838352 1593587 := bstep (se 1 (by rfl) ⟨1195190, by rfl⟩ : syracuseStep 1593587 = 2390381) B2390381
theorem B839927 : Blo 838352 839927 := bstep (se 1 (by rfl) ⟨629945, by rfl⟩ : syracuseStep 839927 = 1259891) B1259891
theorem B1888523 : Blo 838352 1888523 := bstep (se 1 (by rfl) ⟨1416392, by rfl⟩ : syracuseStep 1888523 = 2832785) B2832785
theorem B839947 : Blo 838352 839947 := bstep (se 1 (by rfl) ⟨629960, by rfl⟩ : syracuseStep 839947 = 1259921) B1259921
theorem B839959 : Blo 838352 839959 := bstep (se 1 (by rfl) ⟨629969, by rfl⟩ : syracuseStep 839959 = 1259939) B1259939
theorem B839979 : Blo 838352 839979 := bstep (se 1 (by rfl) ⟨629984, by rfl⟩ : syracuseStep 839979 = 1259969) B1259969
theorem B839991 : Blo 838352 839991 := bstep (se 1 (by rfl) ⟨629993, by rfl⟩ : syracuseStep 839991 = 1259987) B1259987
theorem B1888577 : Blo 838352 1888577 := bstep (se 2 (by rfl) ⟨708216, by rfl⟩ : syracuseStep 1888577 = 1416433) B1416433
theorem B840011 : Blo 838352 840011 := bstep (se 1 (by rfl) ⟨630008, by rfl⟩ : syracuseStep 840011 = 1260017) B1260017
theorem B840023 : Blo 838352 840023 := bstep (se 1 (by rfl) ⟨630017, by rfl⟩ : syracuseStep 840023 = 1260035) B1260035
theorem B840043 : Blo 838352 840043 := bstep (se 1 (by rfl) ⟨630032, by rfl⟩ : syracuseStep 840043 = 1260065) B1260065
theorem B840055 : Blo 838352 840055 := bstep (se 1 (by rfl) ⟨630041, by rfl⟩ : syracuseStep 840055 = 1260083) B1260083
theorem B840075 : Blo 838352 840075 := bstep (se 1 (by rfl) ⟨630056, by rfl⟩ : syracuseStep 840075 = 1260113) B1260113
theorem B840087 : Blo 838352 840087 := bstep (se 1 (by rfl) ⟨630065, by rfl⟩ : syracuseStep 840087 = 1260131) B1260131
theorem B840107 : Blo 838352 840107 := bstep (se 1 (by rfl) ⟨630080, by rfl⟩ : syracuseStep 840107 = 1260161) B1260161
theorem B840119 : Blo 838352 840119 := bstep (se 1 (by rfl) ⟨630089, by rfl⟩ : syracuseStep 840119 = 1260179) B1260179
theorem B840139 : Blo 838352 840139 := bstep (se 1 (by rfl) ⟨630104, by rfl⟩ : syracuseStep 840139 = 1260209) B1260209
theorem B840151 : Blo 838352 840151 := bstep (se 1 (by rfl) ⟨630113, by rfl⟩ : syracuseStep 840151 = 1260227) B1260227
theorem B1364441 : Blo 838352 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B840171 : Blo 838352 840171 := bstep (se 1 (by rfl) ⟨630128, by rfl⟩ : syracuseStep 840171 = 1260257) B1260257
theorem B840183 : Blo 838352 840183 := bstep (se 1 (by rfl) ⟨630137, by rfl⟩ : syracuseStep 840183 = 1260275) B1260275
theorem B840203 : Blo 838352 840203 := bstep (se 1 (by rfl) ⟨630152, by rfl⟩ : syracuseStep 840203 = 1260305) B1260305
theorem B9589265 : Blo 838352 9589265 := bstep (se 2 (by rfl) ⟨3595974, by rfl⟩ : syracuseStep 9589265 = 7191949) B7191949
theorem B840215 : Blo 838352 840215 := bstep (se 1 (by rfl) ⟨630161, by rfl⟩ : syracuseStep 840215 = 1260323) B1260323
theorem B1888793 : Blo 838352 1888793 := bstep (se 2 (by rfl) ⟨708297, by rfl⟩ : syracuseStep 1888793 = 1416595) B1416595
theorem B840235 : Blo 838352 840235 := bstep (se 1 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 840235 = 1260353) B1260353
theorem B3232307 : Blo 838352 3232307 := bstep (se 1 (by rfl) ⟨2424230, by rfl⟩ : syracuseStep 3232307 = 4848461) B4848461
theorem B840247 : Blo 838352 840247 := bstep (se 1 (by rfl) ⟨630185, by rfl⟩ : syracuseStep 840247 = 1260371) B1260371
theorem B840267 : Blo 838352 840267 := bstep (se 1 (by rfl) ⟨630200, by rfl⟩ : syracuseStep 840267 = 1260401) B1260401
theorem B840279 : Blo 838352 840279 := bstep (se 1 (by rfl) ⟨630209, by rfl⟩ : syracuseStep 840279 = 1260419) B1260419
theorem B840299 : Blo 838352 840299 := bstep (se 1 (by rfl) ⟨630224, by rfl⟩ : syracuseStep 840299 = 1260449) B1260449
theorem B1888883 : Blo 838352 1888883 := bstep (se 1 (by rfl) ⟨1416662, by rfl⟩ : syracuseStep 1888883 = 2833325) B2833325
theorem B840311 : Blo 838352 840311 := bstep (se 1 (by rfl) ⟨630233, by rfl⟩ : syracuseStep 840311 = 1260467) B1260467
theorem B840331 : Blo 838352 840331 := bstep (se 1 (by rfl) ⟨630248, by rfl⟩ : syracuseStep 840331 = 1260497) B1260497
theorem B1888919 : Blo 838352 1888919 := bstep (se 1 (by rfl) ⟨1416689, by rfl⟩ : syracuseStep 1888919 = 2833379) B2833379
theorem B840343 : Blo 838352 840343 := bstep (se 1 (by rfl) ⟨630257, by rfl⟩ : syracuseStep 840343 = 1260515) B1260515
theorem B840363 : Blo 838352 840363 := bstep (se 1 (by rfl) ⟨630272, by rfl⟩ : syracuseStep 840363 = 1260545) B1260545
theorem B840375 : Blo 838352 840375 := bstep (se 1 (by rfl) ⟨630281, by rfl⟩ : syracuseStep 840375 = 1260563) B1260563
theorem B840395 : Blo 838352 840395 := bstep (se 1 (by rfl) ⟨630296, by rfl⟩ : syracuseStep 840395 = 1260593) B1260593
theorem B840407 : Blo 838352 840407 := bstep (se 1 (by rfl) ⟨630305, by rfl⟩ : syracuseStep 840407 = 1260611) B1260611
theorem B1594073 : Blo 838352 1594073 := bstep (se 2 (by rfl) ⟨597777, by rfl⟩ : syracuseStep 1594073 = 1195555) B1195555
theorem B840427 : Blo 838352 840427 := bstep (se 1 (by rfl) ⟨630320, by rfl⟩ : syracuseStep 840427 = 1260641) B1260641
theorem B840439 : Blo 838352 840439 := bstep (se 1 (by rfl) ⟨630329, by rfl⟩ : syracuseStep 840439 = 1260659) B1260659
theorem B840459 : Blo 838352 840459 := bstep (se 1 (by rfl) ⟨630344, by rfl⟩ : syracuseStep 840459 = 1260689) B1260689
theorem B1790743 : Blo 838352 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B840471 : Blo 838352 840471 := bstep (se 1 (by rfl) ⟨630353, by rfl⟩ : syracuseStep 840471 = 1260707) B1260707
theorem B2839319 : Blo 838352 2839319 := bstep (se 1 (by rfl) ⟨2129489, by rfl⟩ : syracuseStep 2839319 = 4258979) B4258979
theorem B840491 : Blo 838352 840491 := bstep (se 1 (by rfl) ⟨630368, by rfl⟩ : syracuseStep 840491 = 1260737) B1260737
theorem B840503 : Blo 838352 840503 := bstep (se 1 (by rfl) ⟨630377, by rfl⟩ : syracuseStep 840503 = 1260755) B1260755
theorem B1889099 : Blo 838352 1889099 := bstep (se 1 (by rfl) ⟨1416824, by rfl⟩ : syracuseStep 1889099 = 2833649) B2833649
theorem B840523 : Blo 838352 840523 := bstep (se 1 (by rfl) ⟨630392, by rfl⟩ : syracuseStep 840523 = 1260785) B1260785
theorem B840535 : Blo 838352 840535 := bstep (se 1 (by rfl) ⟨630401, by rfl⟩ : syracuseStep 840535 = 1260803) B1260803
theorem B840555 : Blo 838352 840555 := bstep (se 1 (by rfl) ⟨630416, by rfl⟩ : syracuseStep 840555 = 1260833) B1260833
theorem B840567 : Blo 838352 840567 := bstep (se 1 (by rfl) ⟨630425, by rfl⟩ : syracuseStep 840567 = 1260851) B1260851
theorem B1889153 : Blo 838352 1889153 := bstep (se 2 (by rfl) ⟨708432, by rfl⟩ : syracuseStep 1889153 = 1416865) B1416865
theorem B840587 : Blo 838352 840587 := bstep (se 1 (by rfl) ⟨630440, by rfl⟩ : syracuseStep 840587 = 1260881) B1260881
theorem B3593105 : Blo 838352 3593105 := bstep (se 2 (by rfl) ⟨1347414, by rfl⟩ : syracuseStep 3593105 = 2694829) B2694829
theorem B840599 : Blo 838352 840599 := bstep (se 1 (by rfl) ⟨630449, by rfl⟩ : syracuseStep 840599 = 1260899) B1260899
theorem B840619 : Blo 838352 840619 := bstep (se 1 (by rfl) ⟨630464, by rfl⟩ : syracuseStep 840619 = 1260929) B1260929
theorem B840631 : Blo 838352 840631 := bstep (se 1 (by rfl) ⟨630473, by rfl⟩ : syracuseStep 840631 = 1260947) B1260947
theorem B840651 : Blo 838352 840651 := bstep (se 1 (by rfl) ⟨630488, by rfl⟩ : syracuseStep 840651 = 1260977) B1260977
theorem B840663 : Blo 838352 840663 := bstep (se 1 (by rfl) ⟨630497, by rfl⟩ : syracuseStep 840663 = 1260995) B1260995
theorem B840683 : Blo 838352 840683 := bstep (se 1 (by rfl) ⟨630512, by rfl⟩ : syracuseStep 840683 = 1261025) B1261025
theorem B840695 : Blo 838352 840695 := bstep (se 1 (by rfl) ⟨630521, by rfl⟩ : syracuseStep 840695 = 1261043) B1261043
theorem B840715 : Blo 838352 840715 := bstep (se 1 (by rfl) ⟨630536, by rfl⟩ : syracuseStep 840715 = 1261073) B1261073
theorem B840727 : Blo 838352 840727 := bstep (se 1 (by rfl) ⟨630545, by rfl⟩ : syracuseStep 840727 = 1261091) B1261091
theorem B44356643 : Blo 838352 44356643 := bstep (se 1 (by rfl) ⟨33267482, by rfl⟩ : syracuseStep 44356643 = 66534965) B66534965
theorem B840747 : Blo 838352 840747 := bstep (se 1 (by rfl) ⟨630560, by rfl⟩ : syracuseStep 840747 = 1261121) B1261121
theorem B840759 : Blo 838352 840759 := bstep (se 1 (by rfl) ⟨630569, by rfl⟩ : syracuseStep 840759 = 1261139) B1261139
theorem B30626885 : Blo 838352 30626885 := bstep (se 4 (by rfl) ⟨2871270, by rfl⟩ : syracuseStep 30626885 = 5742541) B5742541
theorem B840779 : Blo 838352 840779 := bstep (se 1 (by rfl) ⟨630584, by rfl⟩ : syracuseStep 840779 = 1261169) B1261169
theorem B840791 : Blo 838352 840791 := bstep (se 1 (by rfl) ⟨630593, by rfl⟩ : syracuseStep 840791 = 1261187) B1261187
theorem B1889369 : Blo 838352 1889369 := bstep (se 2 (by rfl) ⟨708513, by rfl⟩ : syracuseStep 1889369 = 1417027) B1417027
theorem B840811 : Blo 838352 840811 := bstep (se 1 (by rfl) ⟨630608, by rfl⟩ : syracuseStep 840811 = 1261217) B1261217
theorem B840823 : Blo 838352 840823 := bstep (se 1 (by rfl) ⟨630617, by rfl⟩ : syracuseStep 840823 = 1261235) B1261235
theorem B840843 : Blo 838352 840843 := bstep (se 1 (by rfl) ⟨630632, by rfl⟩ : syracuseStep 840843 = 1261265) B1261265
theorem B840855 : Blo 838352 840855 := bstep (se 1 (by rfl) ⟨630641, by rfl⟩ : syracuseStep 840855 = 1261283) B1261283
theorem B840875 : Blo 838352 840875 := bstep (se 1 (by rfl) ⟨630656, by rfl⟩ : syracuseStep 840875 = 1261313) B1261313
theorem B1889459 : Blo 838352 1889459 := bstep (se 1 (by rfl) ⟨1417094, by rfl⟩ : syracuseStep 1889459 = 2834189) B2834189
theorem B840887 : Blo 838352 840887 := bstep (se 1 (by rfl) ⟨630665, by rfl⟩ : syracuseStep 840887 = 1261331) B1261331
theorem B840907 : Blo 838352 840907 := bstep (se 1 (by rfl) ⟨630680, by rfl⟩ : syracuseStep 840907 = 1261361) B1261361
theorem B1889495 : Blo 838352 1889495 := bstep (se 1 (by rfl) ⟨1417121, by rfl⟩ : syracuseStep 1889495 = 2834243) B2834243
theorem B840919 : Blo 838352 840919 := bstep (se 1 (by rfl) ⟨630689, by rfl⟩ : syracuseStep 840919 = 1261379) B1261379
theorem B840939 : Blo 838352 840939 := bstep (se 1 (by rfl) ⟨630704, by rfl⟩ : syracuseStep 840939 = 1261409) B1261409
theorem B840951 : Blo 838352 840951 := bstep (se 1 (by rfl) ⟨630713, by rfl⟩ : syracuseStep 840951 = 1261427) B1261427
theorem B840971 : Blo 838352 840971 := bstep (se 1 (by rfl) ⟨630728, by rfl⟩ : syracuseStep 840971 = 1261457) B1261457
theorem B840983 : Blo 838352 840983 := bstep (se 1 (by rfl) ⟨630737, by rfl⟩ : syracuseStep 840983 = 1261475) B1261475
theorem B841003 : Blo 838352 841003 := bstep (se 1 (by rfl) ⟨630752, by rfl⟩ : syracuseStep 841003 = 1261505) B1261505
theorem B2839859 : Blo 838352 2839859 := bstep (se 1 (by rfl) ⟨2129894, by rfl⟩ : syracuseStep 2839859 = 4259789) B4259789
theorem B841015 : Blo 838352 841015 := bstep (se 1 (by rfl) ⟨630761, by rfl⟩ : syracuseStep 841015 = 1261523) B1261523
theorem B841035 : Blo 838352 841035 := bstep (se 1 (by rfl) ⟨630776, by rfl⟩ : syracuseStep 841035 = 1261553) B1261553
theorem B841047 : Blo 838352 841047 := bstep (se 1 (by rfl) ⟨630785, by rfl⟩ : syracuseStep 841047 = 1261571) B1261571
theorem B841067 : Blo 838352 841067 := bstep (se 1 (by rfl) ⟨630800, by rfl⟩ : syracuseStep 841067 = 1261601) B1261601
theorem B841079 : Blo 838352 841079 := bstep (se 1 (by rfl) ⟨630809, by rfl⟩ : syracuseStep 841079 = 1261619) B1261619
theorem B1889675 : Blo 838352 1889675 := bstep (se 1 (by rfl) ⟨1417256, by rfl⟩ : syracuseStep 1889675 = 2834513) B2834513
theorem B841099 : Blo 838352 841099 := bstep (se 1 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 841099 = 1261649) B1261649
theorem B841111 : Blo 838352 841111 := bstep (se 1 (by rfl) ⟨630833, by rfl⟩ : syracuseStep 841111 = 1261667) B1261667
theorem B841131 : Blo 838352 841131 := bstep (se 1 (by rfl) ⟨630848, by rfl⟩ : syracuseStep 841131 = 1261697) B1261697
theorem B841143 : Blo 838352 841143 := bstep (se 1 (by rfl) ⟨630857, by rfl⟩ : syracuseStep 841143 = 1261715) B1261715
theorem B1889729 : Blo 838352 1889729 := bstep (se 2 (by rfl) ⟨708648, by rfl⟩ : syracuseStep 1889729 = 1417297) B1417297
theorem B841163 : Blo 838352 841163 := bstep (se 1 (by rfl) ⟨630872, by rfl⟩ : syracuseStep 841163 = 1261745) B1261745
theorem B841175 : Blo 838352 841175 := bstep (se 1 (by rfl) ⟨630881, by rfl⟩ : syracuseStep 841175 = 1261763) B1261763
theorem B10769881 : Blo 838352 10769881 := bstep (se 2 (by rfl) ⟨4038705, by rfl⟩ : syracuseStep 10769881 = 8077411) B8077411
theorem B841195 : Blo 838352 841195 := bstep (se 1 (by rfl) ⟨630896, by rfl⟩ : syracuseStep 841195 = 1261793) B1261793
theorem B841207 : Blo 838352 841207 := bstep (se 1 (by rfl) ⟨630905, by rfl⟩ : syracuseStep 841207 = 1261811) B1261811
theorem B7263749 : Blo 838352 7263749 := bstep (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) B1361953
theorem B841227 : Blo 838352 841227 := bstep (se 1 (by rfl) ⟨630920, by rfl⟩ : syracuseStep 841227 = 1261841) B1261841
theorem B841239 : Blo 838352 841239 := bstep (se 1 (by rfl) ⟨630929, by rfl⟩ : syracuseStep 841239 = 1261859) B1261859
theorem B841259 : Blo 838352 841259 := bstep (se 1 (by rfl) ⟨630944, by rfl⟩ : syracuseStep 841259 = 1261889) B1261889
theorem B841271 : Blo 838352 841271 := bstep (se 1 (by rfl) ⟨630953, by rfl⟩ : syracuseStep 841271 = 1261907) B1261907
theorem B2840129 : Blo 838352 2840129 := bstep (se 2 (by rfl) ⟨1065048, by rfl⟩ : syracuseStep 2840129 = 2130097) B2130097
theorem B1791563 : Blo 838352 1791563 := bstep (se 1 (by rfl) ⟨1343672, by rfl⟩ : syracuseStep 1791563 = 2687345) B2687345
theorem B841291 : Blo 838352 841291 := bstep (se 1 (by rfl) ⟨630968, by rfl⟩ : syracuseStep 841291 = 1261937) B1261937
theorem B841303 : Blo 838352 841303 := bstep (se 1 (by rfl) ⟨630977, by rfl⟩ : syracuseStep 841303 = 1261955) B1261955
theorem B841323 : Blo 838352 841323 := bstep (se 1 (by rfl) ⟨630992, by rfl⟩ : syracuseStep 841323 = 1261985) B1261985
theorem B841335 : Blo 838352 841335 := bstep (se 1 (by rfl) ⟨631001, by rfl⟩ : syracuseStep 841335 = 1262003) B1262003
theorem B1365643 : Blo 838352 1365643 := bstep (se 1 (by rfl) ⟨1024232, by rfl⟩ : syracuseStep 1365643 = 2048465) B2048465
theorem B841355 : Blo 838352 841355 := bstep (se 1 (by rfl) ⟨631016, by rfl⟩ : syracuseStep 841355 = 1262033) B1262033
theorem B841367 : Blo 838352 841367 := bstep (se 1 (by rfl) ⟨631025, by rfl⟩ : syracuseStep 841367 = 1262051) B1262051
theorem B1889945 : Blo 838352 1889945 := bstep (se 2 (by rfl) ⟨708729, by rfl⟩ : syracuseStep 1889945 = 1417459) B1417459
theorem B841387 : Blo 838352 841387 := bstep (se 1 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 841387 = 1262081) B1262081
theorem B841399 : Blo 838352 841399 := bstep (se 1 (by rfl) ⟨631049, by rfl⟩ : syracuseStep 841399 = 1262099) B1262099
theorem B841419 : Blo 838352 841419 := bstep (se 1 (by rfl) ⟨631064, by rfl⟩ : syracuseStep 841419 = 1262129) B1262129
theorem B841431 : Blo 838352 841431 := bstep (se 1 (by rfl) ⟨631073, by rfl⟩ : syracuseStep 841431 = 1262147) B1262147
theorem B841451 : Blo 838352 841451 := bstep (se 1 (by rfl) ⟨631088, by rfl⟩ : syracuseStep 841451 = 1262177) B1262177
theorem B1890035 : Blo 838352 1890035 := bstep (se 1 (by rfl) ⟨1417526, by rfl⟩ : syracuseStep 1890035 = 2835053) B2835053
theorem B841463 : Blo 838352 841463 := bstep (se 1 (by rfl) ⟨631097, by rfl⟩ : syracuseStep 841463 = 1262195) B1262195
theorem B841483 : Blo 838352 841483 := bstep (se 1 (by rfl) ⟨631112, by rfl⟩ : syracuseStep 841483 = 1262225) B1262225
theorem B1890071 : Blo 838352 1890071 := bstep (se 1 (by rfl) ⟨1417553, by rfl⟩ : syracuseStep 1890071 = 2835107) B2835107
theorem B841495 : Blo 838352 841495 := bstep (se 1 (by rfl) ⟨631121, by rfl⟩ : syracuseStep 841495 = 1262243) B1262243
theorem B841515 : Blo 838352 841515 := bstep (se 1 (by rfl) ⟨631136, by rfl⟩ : syracuseStep 841515 = 1262273) B1262273
theorem B841527 : Blo 838352 841527 := bstep (se 1 (by rfl) ⟨631145, by rfl⟩ : syracuseStep 841527 = 1262291) B1262291
theorem B841547 : Blo 838352 841547 := bstep (se 1 (by rfl) ⟨631160, by rfl⟩ : syracuseStep 841547 = 1262321) B1262321
theorem B841559 : Blo 838352 841559 := bstep (se 1 (by rfl) ⟨631169, by rfl⟩ : syracuseStep 841559 = 1262339) B1262339
theorem B841579 : Blo 838352 841579 := bstep (se 1 (by rfl) ⟨631184, by rfl⟩ : syracuseStep 841579 = 1262369) B1262369
theorem B841591 : Blo 838352 841591 := bstep (se 1 (by rfl) ⟨631193, by rfl⟩ : syracuseStep 841591 = 1262387) B1262387
theorem B841611 : Blo 838352 841611 := bstep (se 1 (by rfl) ⟨631208, by rfl⟩ : syracuseStep 841611 = 1262417) B1262417
theorem B841623 : Blo 838352 841623 := bstep (se 1 (by rfl) ⟨631217, by rfl⟩ : syracuseStep 841623 = 1262435) B1262435
theorem B841643 : Blo 838352 841643 := bstep (se 1 (by rfl) ⟨631232, by rfl⟩ : syracuseStep 841643 = 1262465) B1262465
theorem B841655 : Blo 838352 841655 := bstep (se 1 (by rfl) ⟨631241, by rfl⟩ : syracuseStep 841655 = 1262483) B1262483
theorem B1890251 : Blo 838352 1890251 := bstep (se 1 (by rfl) ⟨1417688, by rfl⟩ : syracuseStep 1890251 = 2835377) B2835377
theorem B841675 : Blo 838352 841675 := bstep (se 1 (by rfl) ⟨631256, by rfl⟩ : syracuseStep 841675 = 1262513) B1262513
theorem B841687 : Blo 838352 841687 := bstep (se 1 (by rfl) ⟨631265, by rfl⟩ : syracuseStep 841687 = 1262531) B1262531
theorem B4610009 : Blo 838352 4610009 := bstep (se 2 (by rfl) ⟨1728753, by rfl⟩ : syracuseStep 4610009 = 3457507) B3457507
theorem B841707 : Blo 838352 841707 := bstep (se 1 (by rfl) ⟨631280, by rfl⟩ : syracuseStep 841707 = 1262561) B1262561
theorem B841719 : Blo 838352 841719 := bstep (se 1 (by rfl) ⟨631289, by rfl⟩ : syracuseStep 841719 = 1262579) B1262579
theorem B1890305 : Blo 838352 1890305 := bstep (se 2 (by rfl) ⟨708864, by rfl⟩ : syracuseStep 1890305 = 1417729) B1417729
theorem B841739 : Blo 838352 841739 := bstep (se 1 (by rfl) ⟨631304, by rfl⟩ : syracuseStep 841739 = 1262609) B1262609
theorem B841751 : Blo 838352 841751 := bstep (se 1 (by rfl) ⟨631313, by rfl⟩ : syracuseStep 841751 = 1262627) B1262627
theorem B841771 : Blo 838352 841771 := bstep (se 1 (by rfl) ⟨631328, by rfl⟩ : syracuseStep 841771 = 1262657) B1262657
theorem B841783 : Blo 838352 841783 := bstep (se 1 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 841783 = 1262675) B1262675
theorem B30693451 : Blo 838352 30693451 := bstep (se 1 (by rfl) ⟨23020088, by rfl⟩ : syracuseStep 30693451 = 46040177) B46040177
theorem B841803 : Blo 838352 841803 := bstep (se 1 (by rfl) ⟨631352, by rfl⟩ : syracuseStep 841803 = 1262705) B1262705
theorem B841815 : Blo 838352 841815 := bstep (se 1 (by rfl) ⟨631361, by rfl⟩ : syracuseStep 841815 = 1262723) B1262723
theorem B2840669 : Blo 838352 2840669 := bstep (se 3 (by rfl) ⟨532625, by rfl⟩ : syracuseStep 2840669 = 1065251) B1065251
theorem B841835 : Blo 838352 841835 := bstep (se 1 (by rfl) ⟨631376, by rfl⟩ : syracuseStep 841835 = 1262753) B1262753
theorem B841847 : Blo 838352 841847 := bstep (se 1 (by rfl) ⟨631385, by rfl⟩ : syracuseStep 841847 = 1262771) B1262771
theorem B1595531 : Blo 838352 1595531 := bstep (se 1 (by rfl) ⟨1196648, by rfl⟩ : syracuseStep 1595531 = 2393297) B2393297
theorem B841867 : Blo 838352 841867 := bstep (se 1 (by rfl) ⟨631400, by rfl⟩ : syracuseStep 841867 = 1262801) B1262801
theorem B841879 : Blo 838352 841879 := bstep (se 1 (by rfl) ⟨631409, by rfl⟩ : syracuseStep 841879 = 1262819) B1262819
theorem B841899 : Blo 838352 841899 := bstep (se 1 (by rfl) ⟨631424, by rfl⟩ : syracuseStep 841899 = 1262849) B1262849
theorem B841911 : Blo 838352 841911 := bstep (se 1 (by rfl) ⟨631433, by rfl⟩ : syracuseStep 841911 = 1262867) B1262867
theorem B841931 : Blo 838352 841931 := bstep (se 1 (by rfl) ⟨631448, by rfl⟩ : syracuseStep 841931 = 1262897) B1262897
theorem B841943 : Blo 838352 841943 := bstep (se 1 (by rfl) ⟨631457, by rfl⟩ : syracuseStep 841943 = 1262915) B1262915
theorem B1890521 : Blo 838352 1890521 := bstep (se 2 (by rfl) ⟨708945, by rfl⟩ : syracuseStep 1890521 = 1417891) B1417891
theorem B841963 : Blo 838352 841963 := bstep (se 1 (by rfl) ⟨631472, by rfl⟩ : syracuseStep 841963 = 1262945) B1262945
theorem B841975 : Blo 838352 841975 := bstep (se 1 (by rfl) ⟨631481, by rfl⟩ : syracuseStep 841975 = 1262963) B1262963
theorem B841995 : Blo 838352 841995 := bstep (se 1 (by rfl) ⟨631496, by rfl⟩ : syracuseStep 841995 = 1262993) B1262993
theorem B842007 : Blo 838352 842007 := bstep (se 1 (by rfl) ⟨631505, by rfl⟩ : syracuseStep 842007 = 1263011) B1263011
theorem B842027 : Blo 838352 842027 := bstep (se 1 (by rfl) ⟨631520, by rfl⟩ : syracuseStep 842027 = 1263041) B1263041
theorem B1792307 : Blo 838352 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B1890611 : Blo 838352 1890611 := bstep (se 1 (by rfl) ⟨1417958, by rfl⟩ : syracuseStep 1890611 = 2835917) B2835917
theorem B842039 : Blo 838352 842039 := bstep (se 1 (by rfl) ⟨631529, by rfl⟩ : syracuseStep 842039 = 1263059) B1263059
theorem B1595713 : Blo 838352 1595713 := bstep (se 2 (by rfl) ⟨598392, by rfl⟩ : syracuseStep 1595713 = 1196785) B1196785
theorem B842059 : Blo 838352 842059 := bstep (se 1 (by rfl) ⟨631544, by rfl⟩ : syracuseStep 842059 = 1263089) B1263089
theorem B1890647 : Blo 838352 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B842071 : Blo 838352 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B842091 : Blo 838352 842091 := bstep (se 1 (by rfl) ⟨631568, by rfl⟩ : syracuseStep 842091 = 1263137) B1263137
theorem B842103 : Blo 838352 842103 := bstep (se 1 (by rfl) ⟨631577, by rfl⟩ : syracuseStep 842103 = 1263155) B1263155
theorem B842123 : Blo 838352 842123 := bstep (se 1 (by rfl) ⟨631592, by rfl⟩ : syracuseStep 842123 = 1263185) B1263185
theorem B842135 : Blo 838352 842135 := bstep (se 1 (by rfl) ⟨631601, by rfl⟩ : syracuseStep 842135 = 1263203) B1263203
theorem B842155 : Blo 838352 842155 := bstep (se 1 (by rfl) ⟨631616, by rfl⟩ : syracuseStep 842155 = 1263233) B1263233
theorem B842167 : Blo 838352 842167 := bstep (se 1 (by rfl) ⟨631625, by rfl⟩ : syracuseStep 842167 = 1263251) B1263251
theorem B842187 : Blo 838352 842187 := bstep (se 1 (by rfl) ⟨631640, by rfl⟩ : syracuseStep 842187 = 1263281) B1263281
theorem B842199 : Blo 838352 842199 := bstep (se 1 (by rfl) ⟨631649, by rfl⟩ : syracuseStep 842199 = 1263299) B1263299
theorem B842219 : Blo 838352 842219 := bstep (se 1 (by rfl) ⟨631664, by rfl⟩ : syracuseStep 842219 = 1263329) B1263329
theorem B842231 : Blo 838352 842231 := bstep (se 1 (by rfl) ⟨631673, by rfl⟩ : syracuseStep 842231 = 1263347) B1263347
theorem B1890827 : Blo 838352 1890827 := bstep (se 1 (by rfl) ⟨1418120, by rfl⟩ : syracuseStep 1890827 = 2836241) B2836241
theorem B842251 : Blo 838352 842251 := bstep (se 1 (by rfl) ⟨631688, by rfl⟩ : syracuseStep 842251 = 1263377) B1263377
theorem B842263 : Blo 838352 842263 := bstep (se 1 (by rfl) ⟨631697, by rfl⟩ : syracuseStep 842263 = 1263395) B1263395
theorem B842283 : Blo 838352 842283 := bstep (se 1 (by rfl) ⟨631712, by rfl⟩ : syracuseStep 842283 = 1263425) B1263425
theorem B842295 : Blo 838352 842295 := bstep (se 1 (by rfl) ⟨631721, by rfl⟩ : syracuseStep 842295 = 1263443) B1263443
theorem B1890881 : Blo 838352 1890881 := bstep (se 2 (by rfl) ⟨709080, by rfl⟩ : syracuseStep 1890881 = 1418161) B1418161
theorem B842315 : Blo 838352 842315 := bstep (se 1 (by rfl) ⟨631736, by rfl⟩ : syracuseStep 842315 = 1263473) B1263473
theorem B842327 : Blo 838352 842327 := bstep (se 1 (by rfl) ⟨631745, by rfl⟩ : syracuseStep 842327 = 1263491) B1263491
theorem B842347 : Blo 838352 842347 := bstep (se 1 (by rfl) ⟨631760, by rfl⟩ : syracuseStep 842347 = 1263521) B1263521
theorem B1596161 : Blo 838352 1596161 := bstep (se 2 (by rfl) ⟨598560, by rfl⟩ : syracuseStep 1596161 = 1197121) B1197121
theorem B1891097 : Blo 838352 1891097 := bstep (se 2 (by rfl) ⟨709161, by rfl⟩ : syracuseStep 1891097 = 1418323) B1418323
theorem B1891187 : Blo 838352 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B1891223 : Blo 838352 1891223 := bstep (se 1 (by rfl) ⟨1418417, by rfl⟩ : syracuseStep 1891223 = 2836835) B2836835
theorem B7167041 : Blo 838352 7167041 := bstep (se 2 (by rfl) ⟨2687640, by rfl⟩ : syracuseStep 7167041 = 5375281) B5375281
theorem B1891403 : Blo 838352 1891403 := bstep (se 1 (by rfl) ⟨1418552, by rfl⟩ : syracuseStep 1891403 = 2837105) B2837105
theorem B1596503 : Blo 838352 1596503 := bstep (se 1 (by rfl) ⟨1197377, by rfl⟩ : syracuseStep 1596503 = 2394755) B2394755
theorem B4250717 : Blo 838352 4250717 := bstep (se 3 (by rfl) ⟨797009, by rfl⟩ : syracuseStep 4250717 = 1594019) B1594019
theorem B1793153 : Blo 838352 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B1891457 : Blo 838352 1891457 := bstep (se 2 (by rfl) ⟨709296, by rfl⟩ : syracuseStep 1891457 = 1418593) B1418593
theorem B2841803 : Blo 838352 2841803 := bstep (se 1 (by rfl) ⟨2131352, by rfl⟩ : syracuseStep 2841803 = 4262705) B4262705
theorem B875755 : Blo 838352 875755 := bstep (se 1 (by rfl) ⟨656816, by rfl⟩ : syracuseStep 875755 = 1313633) B1313633
theorem B2022679 : Blo 838352 2022679 := bstep (se 1 (by rfl) ⟨1517009, by rfl⟩ : syracuseStep 2022679 = 3034019) B3034019
theorem B3595565 : Blo 838352 3595565 := bstep (se 3 (by rfl) ⟨674168, by rfl⟩ : syracuseStep 3595565 = 1348337) B1348337
theorem B1891673 : Blo 838352 1891673 := bstep (se 2 (by rfl) ⟨709377, by rfl⟩ : syracuseStep 1891673 = 1418755) B1418755
theorem B9592181 : Blo 838352 9592181 := bstep (se 5 (by rfl) ⟨449633, by rfl⟩ : syracuseStep 9592181 = 899267) B899267
theorem B1891763 : Blo 838352 1891763 := bstep (se 1 (by rfl) ⟨1418822, by rfl⟩ : syracuseStep 1891763 = 2837645) B2837645
theorem B1793495 : Blo 838352 1793495 := bstep (se 1 (by rfl) ⟨1345121, by rfl⟩ : syracuseStep 1793495 = 2690243) B2690243
theorem B1891799 : Blo 838352 1891799 := bstep (se 1 (by rfl) ⟨1418849, by rfl⟩ : syracuseStep 1891799 = 2837699) B2837699
theorem B2842073 : Blo 838352 2842073 := bstep (se 2 (by rfl) ⟨1065777, by rfl⟩ : syracuseStep 2842073 = 2131555) B2131555
theorem B5103121 : Blo 838352 5103121 := bstep (se 2 (by rfl) ⟨1913670, by rfl⟩ : syracuseStep 5103121 = 3827341) B3827341
theorem B2154073 : Blo 838352 2154073 := bstep (se 2 (by rfl) ⟨807777, by rfl⟩ : syracuseStep 2154073 = 1615555) B1615555
theorem B3595907 : Blo 838352 3595907 := bstep (se 1 (by rfl) ⟨2696930, by rfl⟩ : syracuseStep 3595907 = 5393861) B5393861
theorem B1891979 : Blo 838352 1891979 := bstep (se 1 (by rfl) ⟨1418984, by rfl⟩ : syracuseStep 1891979 = 2837969) B2837969
theorem B1007255 : Blo 838352 1007255 := bstep (se 1 (by rfl) ⟨755441, by rfl⟩ : syracuseStep 1007255 = 1510883) B1510883
theorem B1892033 : Blo 838352 1892033 := bstep (se 2 (by rfl) ⟨709512, by rfl⟩ : syracuseStep 1892033 = 1419025) B1419025
theorem B1597171 : Blo 838352 1597171 := bstep (se 1 (by rfl) ⟨1197878, by rfl⟩ : syracuseStep 1597171 = 2395757) B2395757
theorem B1892249 : Blo 838352 1892249 := bstep (se 2 (by rfl) ⟨709593, by rfl⟩ : syracuseStep 1892249 = 1419187) B1419187
theorem B12115889 : Blo 838352 12115889 := bstep (se 2 (by rfl) ⟨4543458, by rfl⟩ : syracuseStep 12115889 = 9086917) B9086917
theorem B1892339 : Blo 838352 1892339 := bstep (se 1 (by rfl) ⟨1419254, by rfl⟩ : syracuseStep 1892339 = 2838509) B2838509
theorem B1892375 : Blo 838352 1892375 := bstep (se 1 (by rfl) ⟨1419281, by rfl⟩ : syracuseStep 1892375 = 2838563) B2838563
theorem B2842775 : Blo 838352 2842775 := bstep (se 1 (by rfl) ⟨2132081, by rfl⟩ : syracuseStep 2842775 = 4264163) B4264163
theorem B2875571 : Blo 838352 2875571 := bstep (se 1 (by rfl) ⟨2156678, by rfl⟩ : syracuseStep 2875571 = 4313357) B4313357
theorem B1597619 : Blo 838352 1597619 := bstep (se 1 (by rfl) ⟨1198214, by rfl⟩ : syracuseStep 1597619 = 2396429) B2396429
theorem B1892555 : Blo 838352 1892555 := bstep (se 1 (by rfl) ⟨1419416, by rfl⟩ : syracuseStep 1892555 = 2838833) B2838833
theorem B1597657 : Blo 838352 1597657 := bstep (se 2 (by rfl) ⟨599121, by rfl⟩ : syracuseStep 1597657 = 1198243) B1198243
theorem B1892609 : Blo 838352 1892609 := bstep (se 2 (by rfl) ⟨709728, by rfl⟩ : syracuseStep 1892609 = 1419457) B1419457
theorem B1892825 : Blo 838352 1892825 := bstep (se 2 (by rfl) ⟨709809, by rfl⟩ : syracuseStep 1892825 = 1419619) B1419619
theorem B1892915 : Blo 838352 1892915 := bstep (se 1 (by rfl) ⟨1419686, by rfl⟩ : syracuseStep 1892915 = 2839373) B2839373
theorem B1892951 : Blo 838352 1892951 := bstep (se 1 (by rfl) ⟨1419713, by rfl⟩ : syracuseStep 1892951 = 2839427) B2839427
theorem B1598105 : Blo 838352 1598105 := bstep (se 2 (by rfl) ⟨599289, by rfl⟩ : syracuseStep 1598105 = 1198579) B1198579
theorem B2122433 : Blo 838352 2122433 := bstep (se 2 (by rfl) ⟨795912, by rfl⟩ : syracuseStep 2122433 = 1591825) B1591825
theorem B1008331 : Blo 838352 1008331 := bstep (se 1 (by rfl) ⟨756248, by rfl⟩ : syracuseStep 1008331 = 1512497) B1512497
theorem B1893131 : Blo 838352 1893131 := bstep (se 1 (by rfl) ⟨1419848, by rfl⟩ : syracuseStep 1893131 = 2839697) B2839697
theorem B1893185 : Blo 838352 1893185 := bstep (se 2 (by rfl) ⟨709944, by rfl⟩ : syracuseStep 1893185 = 1419889) B1419889
theorem B3236867 : Blo 838352 3236867 := bstep (se 1 (by rfl) ⟨2427650, by rfl⟩ : syracuseStep 3236867 = 4855301) B4855301
theorem B1893401 : Blo 838352 1893401 := bstep (se 2 (by rfl) ⟨710025, by rfl⟩ : syracuseStep 1893401 = 1420051) B1420051
theorem B6382637 : Blo 838352 6382637 := bstep (se 3 (by rfl) ⟨1196744, by rfl⟩ : syracuseStep 6382637 = 2393489) B2393489
theorem B943159 : Blo 838352 943159 := bstep (se 1 (by rfl) ⟨707369, by rfl⟩ : syracuseStep 943159 = 1414739) B1414739
theorem B1893491 : Blo 838352 1893491 := bstep (se 1 (by rfl) ⟨1420118, by rfl⟩ : syracuseStep 1893491 = 2840237) B2840237
theorem B8610947 : Blo 838352 8610947 := bstep (se 1 (by rfl) ⟨6458210, by rfl⟩ : syracuseStep 8610947 = 12916421) B12916421
theorem B4252823 : Blo 838352 4252823 := bstep (se 1 (by rfl) ⟨3189617, by rfl⟩ : syracuseStep 4252823 = 6379235) B6379235
theorem B1893527 : Blo 838352 1893527 := bstep (se 1 (by rfl) ⟨1420145, by rfl⟩ : syracuseStep 1893527 = 2840291) B2840291
theorem B2122969 : Blo 838352 2122969 := bstep (se 2 (by rfl) ⟨796113, by rfl⟩ : syracuseStep 2122969 = 1592227) B1592227
theorem B943339 : Blo 838352 943339 := bstep (se 1 (by rfl) ⟨707504, by rfl⟩ : syracuseStep 943339 = 1415009) B1415009
theorem B1893707 : Blo 838352 1893707 := bstep (se 1 (by rfl) ⟨1420280, by rfl⟩ : syracuseStep 1893707 = 2840561) B2840561
theorem B943447 : Blo 838352 943447 := bstep (se 1 (by rfl) ⟨707585, by rfl⟩ : syracuseStep 943447 = 1415171) B1415171
theorem B1893761 : Blo 838352 1893761 := bstep (se 2 (by rfl) ⟨710160, by rfl⟩ : syracuseStep 1893761 = 1420321) B1420321
theorem B1598849 : Blo 838352 1598849 := bstep (se 2 (by rfl) ⟨599568, by rfl⟩ : syracuseStep 1598849 = 1199137) B1199137
theorem B943627 : Blo 838352 943627 := bstep (se 1 (by rfl) ⟨707720, by rfl⟩ : syracuseStep 943627 = 1415441) B1415441
theorem B1893977 : Blo 838352 1893977 := bstep (se 2 (by rfl) ⟨710241, by rfl⟩ : syracuseStep 1893977 = 1420483) B1420483
theorem B943735 : Blo 838352 943735 := bstep (se 1 (by rfl) ⟨707801, by rfl⟩ : syracuseStep 943735 = 1415603) B1415603
theorem B1599115 : Blo 838352 1599115 := bstep (se 1 (by rfl) ⟨1199336, by rfl⟩ : syracuseStep 1599115 = 2398673) B2398673
theorem B1402519 : Blo 838352 1402519 := bstep (se 1 (by rfl) ⟨1051889, by rfl⟩ : syracuseStep 1402519 = 2103779) B2103779
theorem B1894067 : Blo 838352 1894067 := bstep (se 1 (by rfl) ⟨1420550, by rfl⟩ : syracuseStep 1894067 = 2841101) B2841101
theorem B1894103 : Blo 838352 1894103 := bstep (se 1 (by rfl) ⟨1420577, by rfl⟩ : syracuseStep 1894103 = 2841155) B2841155
theorem B943915 : Blo 838352 943915 := bstep (se 1 (by rfl) ⟨707936, by rfl⟩ : syracuseStep 943915 = 1415873) B1415873
theorem B1894283 : Blo 838352 1894283 := bstep (se 1 (by rfl) ⟨1420712, by rfl⟩ : syracuseStep 1894283 = 2841425) B2841425
theorem B944023 : Blo 838352 944023 := bstep (se 1 (by rfl) ⟨708017, by rfl⟩ : syracuseStep 944023 = 1416035) B1416035
theorem B1894337 : Blo 838352 1894337 := bstep (se 2 (by rfl) ⟨710376, by rfl⟩ : syracuseStep 1894337 = 1420753) B1420753
theorem B944203 : Blo 838352 944203 := bstep (se 1 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 944203 = 1416305) B1416305
theorem B1894553 : Blo 838352 1894553 := bstep (se 2 (by rfl) ⟨710457, by rfl⟩ : syracuseStep 1894553 = 1420915) B1420915
theorem B944311 : Blo 838352 944311 := bstep (se 1 (by rfl) ⟨708233, by rfl⟩ : syracuseStep 944311 = 1416467) B1416467
theorem B1894643 : Blo 838352 1894643 := bstep (se 1 (by rfl) ⟨1420982, by rfl⟩ : syracuseStep 1894643 = 2841965) B2841965
theorem B1894679 : Blo 838352 1894679 := bstep (se 1 (by rfl) ⟨1421009, by rfl⟩ : syracuseStep 1894679 = 2842019) B2842019
theorem B9103661 : Blo 838352 9103661 := bstep (se 3 (by rfl) ⟨1706936, by rfl⟩ : syracuseStep 9103661 = 3413873) B3413873
theorem B2124083 : Blo 838352 2124083 := bstep (se 1 (by rfl) ⟨1593062, by rfl⟩ : syracuseStep 2124083 = 3186125) B3186125
theorem B944491 : Blo 838352 944491 := bstep (se 1 (by rfl) ⟨708368, by rfl⟩ : syracuseStep 944491 = 1416737) B1416737
theorem B5826995 : Blo 838352 5826995 := bstep (se 1 (by rfl) ⟨4370246, by rfl⟩ : syracuseStep 5826995 = 8740493) B8740493
theorem B1894859 : Blo 838352 1894859 := bstep (se 1 (by rfl) ⟨1421144, by rfl⟩ : syracuseStep 1894859 = 2842289) B2842289
theorem B944599 : Blo 838352 944599 := bstep (se 1 (by rfl) ⟨708449, by rfl⟩ : syracuseStep 944599 = 1416899) B1416899
theorem B1894913 : Blo 838352 1894913 := bstep (se 2 (by rfl) ⟨710592, by rfl⟩ : syracuseStep 1894913 = 1421185) B1421185
theorem B2124377 : Blo 838352 2124377 := bstep (se 2 (by rfl) ⟨796641, by rfl⟩ : syracuseStep 2124377 = 1593283) B1593283
theorem B944779 : Blo 838352 944779 := bstep (se 1 (by rfl) ⟨708584, by rfl⟩ : syracuseStep 944779 = 1417169) B1417169
theorem B1895129 : Blo 838352 1895129 := bstep (se 2 (by rfl) ⟨710673, by rfl⟩ : syracuseStep 1895129 = 1421347) B1421347
theorem B944887 : Blo 838352 944887 := bstep (se 1 (by rfl) ⟨708665, by rfl⟩ : syracuseStep 944887 = 1417331) B1417331
theorem B1895219 : Blo 838352 1895219 := bstep (se 1 (by rfl) ⟨1421414, by rfl⟩ : syracuseStep 1895219 = 2842829) B2842829
theorem B1895255 : Blo 838352 1895255 := bstep (se 1 (by rfl) ⟨1421441, by rfl⟩ : syracuseStep 1895255 = 2842883) B2842883
theorem B945067 : Blo 838352 945067 := bstep (se 1 (by rfl) ⟨708800, by rfl⟩ : syracuseStep 945067 = 1417601) B1417601
theorem B945175 : Blo 838352 945175 := bstep (se 1 (by rfl) ⟨708881, by rfl⟩ : syracuseStep 945175 = 1417763) B1417763
theorem B945355 : Blo 838352 945355 := bstep (se 1 (by rfl) ⟨709016, by rfl⟩ : syracuseStep 945355 = 1418033) B1418033
theorem B945463 : Blo 838352 945463 := bstep (se 1 (by rfl) ⟨709097, by rfl⟩ : syracuseStep 945463 = 1418195) B1418195
theorem B1797527 : Blo 838352 1797527 := bstep (se 1 (by rfl) ⟨1348145, by rfl⟩ : syracuseStep 1797527 = 2696291) B2696291
theorem B44330453 : Blo 838352 44330453 := bstep (se 7 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 44330453 = 1038995) B1038995
theorem B945643 : Blo 838352 945643 := bstep (se 1 (by rfl) ⟨709232, by rfl⟩ : syracuseStep 945643 = 1418465) B1418465
theorem B1797707 : Blo 838352 1797707 := bstep (se 1 (by rfl) ⟨1348280, by rfl⟩ : syracuseStep 1797707 = 2696561) B2696561
theorem B945751 : Blo 838352 945751 := bstep (se 1 (by rfl) ⟨709313, by rfl⟩ : syracuseStep 945751 = 1418627) B1418627
theorem B2420375 : Blo 838352 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B2879155 : Blo 838352 2879155 := bstep (se 1 (by rfl) ⟨2159366, by rfl⟩ : syracuseStep 2879155 = 4318733) B4318733
theorem B6811397 : Blo 838352 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B945931 : Blo 838352 945931 := bstep (se 1 (by rfl) ⟨709448, by rfl⟩ : syracuseStep 945931 = 1418897) B1418897
theorem B946039 : Blo 838352 946039 := bstep (se 1 (by rfl) ⟨709529, by rfl⟩ : syracuseStep 946039 = 1419059) B1419059
theorem B1699735 : Blo 838352 1699735 := bstep (se 1 (by rfl) ⟨1274801, by rfl⟩ : syracuseStep 1699735 = 2549603) B2549603
theorem B946219 : Blo 838352 946219 := bstep (se 1 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 946219 = 1419329) B1419329
theorem B946327 : Blo 838352 946327 := bstep (se 1 (by rfl) ⟨709745, by rfl⟩ : syracuseStep 946327 = 1419491) B1419491
theorem B3633331 : Blo 838352 3633331 := bstep (se 1 (by rfl) ⟨2724998, by rfl⟩ : syracuseStep 3633331 = 5449997) B5449997
theorem B2126027 : Blo 838352 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B946507 : Blo 838352 946507 := bstep (se 1 (by rfl) ⟨709880, by rfl⟩ : syracuseStep 946507 = 1419761) B1419761
theorem B4321687 : Blo 838352 4321687 := bstep (se 1 (by rfl) ⟨3241265, by rfl⟩ : syracuseStep 4321687 = 6482531) B6482531
theorem B946615 : Blo 838352 946615 := bstep (se 1 (by rfl) ⟨709961, by rfl⟩ : syracuseStep 946615 = 1419923) B1419923
theorem B946795 : Blo 838352 946795 := bstep (se 1 (by rfl) ⟨710096, by rfl⟩ : syracuseStep 946795 = 1420193) B1420193
theorem B4256387 : Blo 838352 4256387 := bstep (se 1 (by rfl) ⟨3192290, by rfl⟩ : syracuseStep 4256387 = 6384581) B6384581
theorem B2388683 : Blo 838352 2388683 := bstep (se 1 (by rfl) ⟨1791512, by rfl⟩ : syracuseStep 2388683 = 3583025) B3583025
theorem B7172813 : Blo 838352 7172813 := bstep (se 3 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 7172813 = 2689805) B2689805
theorem B946903 : Blo 838352 946903 := bstep (se 1 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 946903 = 1420355) B1420355
theorem B1700683 : Blo 838352 1700683 := bstep (se 1 (by rfl) ⟨1275512, by rfl⟩ : syracuseStep 1700683 = 2551025) B2551025
theorem B6386525 : Blo 838352 6386525 := bstep (se 3 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 6386525 = 2394947) B2394947
theorem B947083 : Blo 838352 947083 := bstep (se 1 (by rfl) ⟨710312, by rfl⟩ : syracuseStep 947083 = 1420625) B1420625
theorem B947191 : Blo 838352 947191 := bstep (se 1 (by rfl) ⟨710393, by rfl⟩ : syracuseStep 947191 = 1420787) B1420787
theorem B2126999 : Blo 838352 2126999 := bstep (se 1 (by rfl) ⟨1595249, by rfl⟩ : syracuseStep 2126999 = 3190499) B3190499
theorem B947371 : Blo 838352 947371 := bstep (se 1 (by rfl) ⟨710528, by rfl⟩ : syracuseStep 947371 = 1421057) B1421057
theorem B2880715 : Blo 838352 2880715 := bstep (se 1 (by rfl) ⟨2160536, by rfl⟩ : syracuseStep 2880715 = 4321073) B4321073
theorem B947479 : Blo 838352 947479 := bstep (se 1 (by rfl) ⟨710609, by rfl⟩ : syracuseStep 947479 = 1421219) B1421219
theorem B6059443 : Blo 838352 6059443 := bstep (se 1 (by rfl) ⟨4544582, by rfl⟩ : syracuseStep 6059443 = 9089165) B9089165
theorem B2127667 : Blo 838352 2127667 := bstep (se 1 (by rfl) ⟨1595750, by rfl⟩ : syracuseStep 2127667 = 3191501) B3191501
theorem B1079191 : Blo 838352 1079191 := bstep (se 1 (by rfl) ⟨809393, by rfl⟩ : syracuseStep 1079191 = 1618787) B1618787
theorem B1701811 : Blo 838352 1701811 := bstep (se 1 (by rfl) ⟨1276358, by rfl⟩ : syracuseStep 1701811 = 2552717) B2552717
theorem B15333299 : Blo 838352 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B2127809 : Blo 838352 2127809 := bstep (se 2 (by rfl) ⟨797928, by rfl⟩ : syracuseStep 2127809 = 1595857) B1595857
theorem B2389981 : Blo 838352 2389981 := bstep (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) B896243
theorem B6453283 : Blo 838352 6453283 := bstep (se 1 (by rfl) ⟨4839962, by rfl⟩ : syracuseStep 6453283 = 9679925) B9679925
theorem B21493835 : Blo 838352 21493835 := bstep (se 1 (by rfl) ⟨16120376, by rfl⟩ : syracuseStep 21493835 = 32240753) B32240753
theorem B1276183 : Blo 838352 1276183 := bstep (se 1 (by rfl) ⟨957137, by rfl⟩ : syracuseStep 1276183 = 1914275) B1914275
theorem B2390323 : Blo 838352 2390323 := bstep (se 1 (by rfl) ⟨1792742, by rfl⟩ : syracuseStep 2390323 = 3585485) B3585485
theorem B4782401 : Blo 838352 4782401 := bstep (se 2 (by rfl) ⟨1793400, by rfl⟩ : syracuseStep 4782401 = 3586801) B3586801
theorem B2554177 : Blo 838352 2554177 := bstep (se 2 (by rfl) ⟨957816, by rfl⟩ : syracuseStep 2554177 = 1915633) B1915633
theorem B850423 : Blo 838352 850423 := bstep (se 1 (by rfl) ⟨637817, by rfl⟩ : syracuseStep 850423 = 1275635) B1275635
theorem B3832343 : Blo 838352 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B2685899 : Blo 838352 2685899 := bstep (se 1 (by rfl) ⟨2014424, by rfl⟩ : syracuseStep 2685899 = 4028849) B4028849
theorem B38763481 : Blo 838352 38763481 := bstep (se 2 (by rfl) ⟨14536305, by rfl⟩ : syracuseStep 38763481 = 29072611) B29072611
theorem B3931139 : Blo 838352 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B2129075 : Blo 838352 2129075 := bstep (se 1 (by rfl) ⟨1596806, by rfl⟩ : syracuseStep 2129075 = 3193613) B3193613
theorem B2391257 : Blo 838352 2391257 := bstep (se 2 (by rfl) ⟨896721, by rfl⟩ : syracuseStep 2391257 = 1793443) B1793443
theorem B3833219 : Blo 838352 3833219 := bstep (se 1 (by rfl) ⟨2874914, by rfl⟩ : syracuseStep 3833219 = 5749829) B5749829
theorem B9698777 : Blo 838352 9698777 := bstep (se 2 (by rfl) ⟨3637041, by rfl⟩ : syracuseStep 9698777 = 7274083) B7274083
theorem B1277527 : Blo 838352 1277527 := bstep (se 1 (by rfl) ⟨958145, by rfl⟩ : syracuseStep 1277527 = 1916291) B1916291
theorem B2129611 : Blo 838352 2129611 := bstep (se 1 (by rfl) ⟨1597208, by rfl⟩ : syracuseStep 2129611 = 3194417) B3194417
theorem B7667531 : Blo 838352 7667531 := bstep (se 1 (by rfl) ⟨5750648, by rfl⟩ : syracuseStep 7667531 = 11501297) B11501297
theorem B2129753 : Blo 838352 2129753 := bstep (se 2 (by rfl) ⟨798657, by rfl⟩ : syracuseStep 2129753 = 1597315) B1597315
theorem B2129935 : Blo 838352 2129935 := bstep (se 1 (by rfl) ⟨1597451, by rfl⟩ : syracuseStep 2129935 = 3194903) B3194903
theorem B2555965 : Blo 838352 2555965 := bstep (se 3 (by rfl) ⟨479243, by rfl⟩ : syracuseStep 2555965 = 958487) B958487
theorem B2130209 : Blo 838352 2130209 := bstep (se 2 (by rfl) ⟨798828, by rfl⟩ : syracuseStep 2130209 = 1597657) B1597657
theorem B4260761 : Blo 838352 4260761 := bstep (se 2 (by rfl) ⟨1597785, by rfl⟩ : syracuseStep 4260761 = 3195571) B3195571
theorem B1705079 : Blo 838352 1705079 := bstep (se 1 (by rfl) ⟨1278809, by rfl⟩ : syracuseStep 1705079 = 2557619) B2557619
theorem B1344647 : Blo 838352 1344647 := bstep (se 1 (by rfl) ⟨1008485, by rfl⟩ : syracuseStep 1344647 = 2016971) B2016971
theorem B2131211 : Blo 838352 2131211 := bstep (se 1 (by rfl) ⟨1598408, by rfl⟩ : syracuseStep 2131211 = 3196817) B3196817
theorem B1345339 : Blo 838352 1345339 := bstep (se 1 (by rfl) ⟨1009004, by rfl⟩ : syracuseStep 1345339 = 2018009) B2018009
theorem B1345415 : Blo 838352 1345415 := bstep (se 1 (by rfl) ⟨1009061, by rfl⟩ : syracuseStep 1345415 = 2018123) B2018123
theorem B4786067 : Blo 838352 4786067 := bstep (se 1 (by rfl) ⟨3589550, by rfl⟩ : syracuseStep 4786067 = 7179101) B7179101
theorem B2131859 : Blo 838352 2131859 := bstep (se 1 (by rfl) ⟨1598894, by rfl⟩ : syracuseStep 2131859 = 3197789) B3197789
theorem B2394127 : Blo 838352 2394127 := bstep (se 1 (by rfl) ⟨1795595, by rfl⟩ : syracuseStep 2394127 = 3591191) B3591191
theorem B2394173 : Blo 838352 2394173 := bstep (se 3 (by rfl) ⟨448907, by rfl⟩ : syracuseStep 2394173 = 897815) B897815
theorem B2132153 : Blo 838352 2132153 := bstep (se 2 (by rfl) ⟨799557, by rfl⟩ : syracuseStep 2132153 = 1599115) B1599115
theorem B1870025 : Blo 838352 1870025 := bstep (se 2 (by rfl) ⟨701259, by rfl⟩ : syracuseStep 1870025 = 1402519) B1402519
theorem B2394515 : Blo 838352 2394515 := bstep (se 1 (by rfl) ⟨1795886, by rfl⟩ : syracuseStep 2394515 = 3591773) B3591773
theorem B2329033 : Blo 838352 2329033 := bstep (se 2 (by rfl) ⟨873387, by rfl⟩ : syracuseStep 2329033 = 1746775) B1746775
theorem B1706555 : Blo 838352 1706555 := bstep (se 1 (by rfl) ⟨1279916, by rfl⟩ : syracuseStep 1706555 = 2559833) B2559833
theorem B4786775 : Blo 838352 4786775 := bstep (se 1 (by rfl) ⟨3590081, by rfl⟩ : syracuseStep 4786775 = 7180163) B7180163
theorem B14355467 : Blo 838352 14355467 := bstep (se 1 (by rfl) ⟨10766600, by rfl⟩ : syracuseStep 14355467 = 21533201) B21533201
theorem B6392843 : Blo 838352 6392843 := bstep (se 1 (by rfl) ⟨4794632, by rfl⟩ : syracuseStep 6392843 = 9589265) B9589265
theorem B4033709 : Blo 838352 4033709 := bstep (se 3 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 4033709 = 1512641) B1512641
theorem B2395403 : Blo 838352 2395403 := bstep (se 1 (by rfl) ⟨1796552, by rfl⟩ : syracuseStep 2395403 = 3593105) B3593105
theorem B20417923 : Blo 838352 20417923 := bstep (se 1 (by rfl) ⟨15313442, by rfl⟩ : syracuseStep 20417923 = 30626885) B30626885
theorem B9571769 : Blo 838352 9571769 := bstep (se 2 (by rfl) ⟨3589413, by rfl⟩ : syracuseStep 9571769 = 7178827) B7178827
theorem B4263353 : Blo 838352 4263353 := bstep (se 2 (by rfl) ⟨1598757, by rfl⟩ : syracuseStep 4263353 = 3197515) B3197515
theorem B7179853 : Blo 838352 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B5377765 : Blo 838352 5377765 := bstep (se 4 (by rfl) ⟨504165, by rfl⟩ : syracuseStep 5377765 = 1008331) B1008331
theorem B18452225 : Blo 838352 18452225 := bstep (se 2 (by rfl) ⟨6919584, by rfl⟩ : syracuseStep 18452225 = 13839169) B13839169
theorem B24875209 : Blo 838352 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B2691343 : Blo 838352 2691343 := bstep (se 1 (by rfl) ⟨2018507, by rfl⟩ : syracuseStep 2691343 = 4037015) B4037015
theorem B4788665 : Blo 838352 4788665 := bstep (se 2 (by rfl) ⟨1795749, by rfl⟩ : syracuseStep 4788665 = 3591499) B3591499
theorem B2397043 : Blo 838352 2397043 := bstep (se 1 (by rfl) ⟨1797782, by rfl⟩ : syracuseStep 2397043 = 3595565) B3595565
theorem B3838873 : Blo 838352 3838873 := bstep (se 2 (by rfl) ⟨1439577, by rfl⟩ : syracuseStep 3838873 = 2879155) B2879155
theorem B6394787 : Blo 838352 6394787 := bstep (se 1 (by rfl) ⟨4796090, by rfl⟩ : syracuseStep 6394787 = 9592181) B9592181
theorem B14554037 : Blo 838352 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B2397271 : Blo 838352 2397271 := bstep (se 1 (by rfl) ⟨1797953, by rfl⟩ : syracuseStep 2397271 = 3595907) B3595907
theorem B2266313 : Blo 838352 2266313 := bstep (se 2 (by rfl) ⟨849867, by rfl⟩ : syracuseStep 2266313 = 1699735) B1699735
theorem B10229009 : Blo 838352 10229009 := bstep (se 2 (by rfl) ⟨3835878, by rfl⟩ : syracuseStep 10229009 = 7671757) B7671757
theorem B1381691 : Blo 838352 1381691 := bstep (se 1 (by rfl) ⟨1036268, by rfl⟩ : syracuseStep 1381691 = 2072537) B2072537
theorem B1414955 : Blo 838352 1414955 := bstep (se 1 (by rfl) ⟨1061216, by rfl⟩ : syracuseStep 1414955 = 2122433) B2122433
theorem B5740631 : Blo 838352 5740631 := bstep (se 1 (by rfl) ⟨4305473, by rfl⟩ : syracuseStep 5740631 = 8610947) B8610947
theorem B1415353 : Blo 838352 1415353 := bstep (se 2 (by rfl) ⟨530757, by rfl⟩ : syracuseStep 1415353 = 1061515) B1061515
theorem B6069107 : Blo 838352 6069107 := bstep (se 1 (by rfl) ⟨4551830, by rfl⟩ : syracuseStep 6069107 = 9103661) B9103661
theorem B1416055 : Blo 838352 1416055 := bstep (se 1 (by rfl) ⟨1062041, by rfl⟩ : syracuseStep 1416055 = 2124083) B2124083
theorem B2694035 : Blo 838352 2694035 := bstep (se 1 (by rfl) ⟨2020526, by rfl⟩ : syracuseStep 2694035 = 4041053) B4041053
theorem B3840953 : Blo 838352 3840953 := bstep (se 2 (by rfl) ⟨1440357, by rfl⟩ : syracuseStep 3840953 = 2880715) B2880715
theorem B1416251 : Blo 838352 1416251 := bstep (se 1 (by rfl) ⟨1062188, by rfl⟩ : syracuseStep 1416251 = 2124377) B2124377
theorem B3021911 : Blo 838352 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B4037921 : Blo 838352 4037921 := bstep (se 2 (by rfl) ⟨1514220, by rfl⟩ : syracuseStep 4037921 = 3028441) B3028441
theorem B14359841 : Blo 838352 14359841 := bstep (se 2 (by rfl) ⟨5384940, by rfl⟩ : syracuseStep 14359841 = 10769881) B10769881
theorem B1416649 : Blo 838352 1416649 := bstep (se 2 (by rfl) ⟨531243, by rfl⟩ : syracuseStep 1416649 = 1062487) B1062487
theorem B1515143 : Blo 838352 1515143 := bstep (se 1 (by rfl) ⟨1136357, by rfl⟩ : syracuseStep 1515143 = 2272715) B2272715
theorem B1515323 : Blo 838352 1515323 := bstep (se 1 (by rfl) ⟨1136492, by rfl⟩ : syracuseStep 1515323 = 2272985) B2272985
theorem B2269081 : Blo 838352 2269081 := bstep (se 2 (by rfl) ⟨850905, by rfl⟩ : syracuseStep 2269081 = 1701811) B1701811
theorem B3186641 : Blo 838352 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B1417351 : Blo 838352 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B3187097 : Blo 838352 3187097 := bstep (se 2 (by rfl) ⟨1195161, by rfl⟩ : syracuseStep 3187097 = 2390323) B2390323
theorem B7283429 : Blo 838352 7283429 := bstep (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) B1365643
theorem B1417999 : Blo 838352 1417999 := bstep (se 1 (by rfl) ⟨1063499, by rfl⟩ : syracuseStep 1417999 = 2126999) B2126999
theorem B20423573 : Blo 838352 20423573 := bstep (se 6 (by rfl) ⟨478677, by rfl⟩ : syracuseStep 20423573 = 957355) B957355
theorem B1385591 : Blo 838352 1385591 := bstep (se 1 (by rfl) ⟨1039193, by rfl⟩ : syracuseStep 1385591 = 2078387) B2078387
theorem B51684641 : Blo 838352 51684641 := bstep (se 2 (by rfl) ⟨19381740, by rfl⟩ : syracuseStep 51684641 = 38763481) B38763481
theorem B1418539 : Blo 838352 1418539 := bstep (se 1 (by rfl) ⟨1063904, by rfl⟩ : syracuseStep 1418539 = 2127809) B2127809
theorem B6366599 : Blo 838352 6366599 := bstep (se 1 (by rfl) ⟨4774949, by rfl⟩ : syracuseStep 6366599 = 9549899) B9549899
theorem B14329223 : Blo 838352 14329223 := bstep (se 1 (by rfl) ⟨10746917, by rfl⟩ : syracuseStep 14329223 = 21493835) B21493835
theorem B1418681 : Blo 838352 1418681 := bstep (se 2 (by rfl) ⟨532005, by rfl⟩ : syracuseStep 1418681 = 1064011) B1064011
theorem B3188267 : Blo 838352 3188267 := bstep (se 1 (by rfl) ⟨2391200, by rfl⟩ : syracuseStep 3188267 = 4782401) B4782401
theorem B2696905 : Blo 838352 2696905 := bstep (se 2 (by rfl) ⟨1011339, by rfl⟩ : syracuseStep 2696905 = 2022679) B2022679
theorem B1419383 : Blo 838352 1419383 := bstep (se 1 (by rfl) ⟨1064537, by rfl⟩ : syracuseStep 1419383 = 2129075) B2129075
theorem B6465851 : Blo 838352 6465851 := bstep (se 1 (by rfl) ⟨4849388, by rfl⟩ : syracuseStep 6465851 = 9698777) B9698777
theorem B1419835 : Blo 838352 1419835 := bstep (se 1 (by rfl) ⟨1064876, by rfl⟩ : syracuseStep 1419835 = 2129753) B2129753
theorem B1419977 : Blo 838352 1419977 := bstep (se 2 (by rfl) ⟨532491, by rfl⟩ : syracuseStep 1419977 = 1064983) B1064983
theorem B3582701 : Blo 838352 3582701 := bstep (se 3 (by rfl) ⟨671756, by rfl⟩ : syracuseStep 3582701 = 1343513) B1343513
theorem B4795271 : Blo 838352 4795271 := bstep (se 1 (by rfl) ⟨3596453, by rfl⟩ : syracuseStep 4795271 = 7192907) B7192907
theorem B2272541 : Blo 838352 2272541 := bstep (se 3 (by rfl) ⟨426101, by rfl⟩ : syracuseStep 2272541 = 852203) B852203
theorem B1420679 : Blo 838352 1420679 := bstep (se 1 (by rfl) ⟨1065509, by rfl⟩ : syracuseStep 1420679 = 2131019) B2131019
theorem B3583385 : Blo 838352 3583385 := bstep (se 2 (by rfl) ⟨1343769, by rfl⟩ : syracuseStep 3583385 = 2687539) B2687539
theorem B4042169 : Blo 838352 4042169 := bstep (se 2 (by rfl) ⟨1515813, by rfl⟩ : syracuseStep 4042169 = 3031627) B3031627
theorem B3190225 : Blo 838352 3190225 := bstep (se 2 (by rfl) ⟨1196334, by rfl⟩ : syracuseStep 3190225 = 2392669) B2392669
theorem B2272769 : Blo 838352 2272769 := bstep (se 2 (by rfl) ⟨852288, by rfl⟩ : syracuseStep 2272769 = 1704577) B1704577
theorem B18132659 : Blo 838352 18132659 := bstep (se 1 (by rfl) ⟨13599494, by rfl⟩ : syracuseStep 18132659 = 27198989) B27198989
theorem B3190529 : Blo 838352 3190529 := bstep (se 2 (by rfl) ⟨1196448, by rfl⟩ : syracuseStep 3190529 = 2392897) B2392897
theorem B4534031 : Blo 838352 4534031 := bstep (se 1 (by rfl) ⟨3400523, by rfl⟩ : syracuseStep 4534031 = 6801047) B6801047
theorem B2830139 : Blo 838352 2830139 := bstep (se 1 (by rfl) ⟨2122604, by rfl⟩ : syracuseStep 2830139 = 4245209) B4245209
theorem B1421327 : Blo 838352 1421327 := bstep (se 1 (by rfl) ⟨1065995, by rfl⟩ : syracuseStep 1421327 = 2131991) B2131991
theorem B1257545 : Blo 838352 1257545 := bstep (se 2 (by rfl) ⟨471579, by rfl⟩ : syracuseStep 1257545 = 943159) B943159
theorem B1257659 : Blo 838352 1257659 := bstep (se 1 (by rfl) ⟨943244, by rfl⟩ : syracuseStep 1257659 = 1886489) B1886489
theorem B3190985 : Blo 838352 3190985 := bstep (se 2 (by rfl) ⟨1196619, by rfl⟩ : syracuseStep 3190985 = 2393239) B2393239
theorem B1257719 : Blo 838352 1257719 := bstep (se 1 (by rfl) ⟨943289, by rfl⟩ : syracuseStep 1257719 = 1886579) B1886579
theorem B1257743 : Blo 838352 1257743 := bstep (se 1 (by rfl) ⟨943307, by rfl⟩ : syracuseStep 1257743 = 1886615) B1886615
theorem B2830625 : Blo 838352 2830625 := bstep (se 2 (by rfl) ⟨1061484, by rfl⟩ : syracuseStep 2830625 = 2122969) B2122969
theorem B1257785 : Blo 838352 1257785 := bstep (se 2 (by rfl) ⟨471669, by rfl⟩ : syracuseStep 1257785 = 943339) B943339
theorem B1257863 : Blo 838352 1257863 := bstep (se 1 (by rfl) ⟨943397, by rfl⟩ : syracuseStep 1257863 = 1886795) B1886795
theorem B2044295 : Blo 838352 2044295 := bstep (se 1 (by rfl) ⟨1533221, by rfl⟩ : syracuseStep 2044295 = 3066443) B3066443
theorem B1257899 : Blo 838352 1257899 := bstep (se 1 (by rfl) ⟨943424, by rfl⟩ : syracuseStep 1257899 = 1886849) B1886849
theorem B1257929 : Blo 838352 1257929 := bstep (se 2 (by rfl) ⟨471723, by rfl⟩ : syracuseStep 1257929 = 943447) B943447
theorem B1061419 : Blo 838352 1061419 := bstep (se 1 (by rfl) ⟨796064, by rfl⟩ : syracuseStep 1061419 = 1592129) B1592129
theorem B1258043 : Blo 838352 1258043 := bstep (se 1 (by rfl) ⟨943532, by rfl⟩ : syracuseStep 1258043 = 1887065) B1887065
theorem B1258103 : Blo 838352 1258103 := bstep (se 1 (by rfl) ⟨943577, by rfl⟩ : syracuseStep 1258103 = 1887155) B1887155
theorem B1258127 : Blo 838352 1258127 := bstep (se 1 (by rfl) ⟨943595, by rfl⟩ : syracuseStep 1258127 = 1887191) B1887191
theorem B1258169 : Blo 838352 1258169 := bstep (se 2 (by rfl) ⟨471813, by rfl⟩ : syracuseStep 1258169 = 943627) B943627
theorem B1258247 : Blo 838352 1258247 := bstep (se 1 (by rfl) ⟨943685, by rfl⟩ : syracuseStep 1258247 = 1887371) B1887371
theorem B1258283 : Blo 838352 1258283 := bstep (se 1 (by rfl) ⟨943712, by rfl⟩ : syracuseStep 1258283 = 1887425) B1887425
theorem B1258313 : Blo 838352 1258313 := bstep (se 2 (by rfl) ⟨471867, by rfl⟩ : syracuseStep 1258313 = 943735) B943735
theorem B2831219 : Blo 838352 2831219 := bstep (se 1 (by rfl) ⟨2123414, by rfl⟩ : syracuseStep 2831219 = 4246829) B4246829
theorem B1258427 : Blo 838352 1258427 := bstep (se 1 (by rfl) ⟨943820, by rfl⟩ : syracuseStep 1258427 = 1887641) B1887641
theorem B4371421 : Blo 838352 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B1258487 : Blo 838352 1258487 := bstep (se 1 (by rfl) ⟨943865, by rfl⟩ : syracuseStep 1258487 = 1887731) B1887731
theorem B4305923 : Blo 838352 4305923 := bstep (se 1 (by rfl) ⟨3229442, by rfl⟩ : syracuseStep 4305923 = 6458885) B6458885
theorem B1258511 : Blo 838352 1258511 := bstep (se 1 (by rfl) ⟨943883, by rfl⟩ : syracuseStep 1258511 = 1887767) B1887767
theorem B1258553 : Blo 838352 1258553 := bstep (se 2 (by rfl) ⟨471957, by rfl⟩ : syracuseStep 1258553 = 943915) B943915
theorem B1258631 : Blo 838352 1258631 := bstep (se 1 (by rfl) ⟨943973, by rfl⟩ : syracuseStep 1258631 = 1887947) B1887947
theorem B1258667 : Blo 838352 1258667 := bstep (se 1 (by rfl) ⟨944000, by rfl⟩ : syracuseStep 1258667 = 1888001) B1888001
theorem B1258697 : Blo 838352 1258697 := bstep (se 2 (by rfl) ⟨472011, by rfl⟩ : syracuseStep 1258697 = 944023) B944023
theorem B3585313 : Blo 838352 3585313 := bstep (se 2 (by rfl) ⟨1344492, by rfl⟩ : syracuseStep 3585313 = 2688985) B2688985
theorem B1258811 : Blo 838352 1258811 := bstep (se 1 (by rfl) ⟨944108, by rfl⟩ : syracuseStep 1258811 = 1888217) B1888217
theorem B1258871 : Blo 838352 1258871 := bstep (se 1 (by rfl) ⟨944153, by rfl⟩ : syracuseStep 1258871 = 1888307) B1888307
theorem B4044167 : Blo 838352 4044167 := bstep (se 1 (by rfl) ⟨3033125, by rfl⟩ : syracuseStep 4044167 = 6066251) B6066251
theorem B1258895 : Blo 838352 1258895 := bstep (se 1 (by rfl) ⟨944171, by rfl⟩ : syracuseStep 1258895 = 1888343) B1888343
theorem B1258937 : Blo 838352 1258937 := bstep (se 2 (by rfl) ⟨472101, by rfl⟩ : syracuseStep 1258937 = 944203) B944203
theorem B1062391 : Blo 838352 1062391 := bstep (se 1 (by rfl) ⟨796793, by rfl⟩ : syracuseStep 1062391 = 1593587) B1593587
theorem B1259015 : Blo 838352 1259015 := bstep (se 1 (by rfl) ⟨944261, by rfl⟩ : syracuseStep 1259015 = 1888523) B1888523
theorem B1259051 : Blo 838352 1259051 := bstep (se 1 (by rfl) ⟨944288, by rfl⟩ : syracuseStep 1259051 = 1888577) B1888577
theorem B1259081 : Blo 838352 1259081 := bstep (se 2 (by rfl) ⟨472155, by rfl⟩ : syracuseStep 1259081 = 944311) B944311
theorem B1259195 : Blo 838352 1259195 := bstep (se 1 (by rfl) ⟨944396, by rfl⟩ : syracuseStep 1259195 = 1888793) B1888793
theorem B1259255 : Blo 838352 1259255 := bstep (se 1 (by rfl) ⟨944441, by rfl⟩ : syracuseStep 1259255 = 1888883) B1888883
theorem B898823 : Blo 838352 898823 := bstep (se 1 (by rfl) ⟨674117, by rfl⟩ : syracuseStep 898823 = 1348235) B1348235
theorem B1259279 : Blo 838352 1259279 := bstep (se 1 (by rfl) ⟨944459, by rfl⟩ : syracuseStep 1259279 = 1888919) B1888919
theorem B7190309 : Blo 838352 7190309 := bstep (se 4 (by rfl) ⟨674091, by rfl⟩ : syracuseStep 7190309 = 1348183) B1348183
theorem B1259321 : Blo 838352 1259321 := bstep (se 2 (by rfl) ⟨472245, by rfl⟩ : syracuseStep 1259321 = 944491) B944491
theorem B1062715 : Blo 838352 1062715 := bstep (se 1 (by rfl) ⟨797036, by rfl⟩ : syracuseStep 1062715 = 1594073) B1594073
theorem B1259399 : Blo 838352 1259399 := bstep (se 1 (by rfl) ⟨944549, by rfl⟩ : syracuseStep 1259399 = 1889099) B1889099
theorem B1259435 : Blo 838352 1259435 := bstep (se 1 (by rfl) ⟨944576, by rfl⟩ : syracuseStep 1259435 = 1889153) B1889153
theorem B1259465 : Blo 838352 1259465 := bstep (se 2 (by rfl) ⟨472299, by rfl⟩ : syracuseStep 1259465 = 944599) B944599
theorem B29571095 : Blo 838352 29571095 := bstep (se 1 (by rfl) ⟨22178321, by rfl⟩ : syracuseStep 29571095 = 44356643) B44356643
theorem B1259579 : Blo 838352 1259579 := bstep (se 1 (by rfl) ⟨944684, by rfl⟩ : syracuseStep 1259579 = 1889369) B1889369
theorem B1259639 : Blo 838352 1259639 := bstep (se 1 (by rfl) ⟨944729, by rfl⟩ : syracuseStep 1259639 = 1889459) B1889459
theorem B1259663 : Blo 838352 1259663 := bstep (se 1 (by rfl) ⟨944747, by rfl⟩ : syracuseStep 1259663 = 1889495) B1889495
theorem B1259705 : Blo 838352 1259705 := bstep (se 2 (by rfl) ⟨472389, by rfl⟩ : syracuseStep 1259705 = 944779) B944779
theorem B1259783 : Blo 838352 1259783 := bstep (se 1 (by rfl) ⟨944837, by rfl⟩ : syracuseStep 1259783 = 1889675) B1889675
theorem B1259819 : Blo 838352 1259819 := bstep (se 1 (by rfl) ⟨944864, by rfl⟩ : syracuseStep 1259819 = 1889729) B1889729
theorem B1259849 : Blo 838352 1259849 := bstep (se 2 (by rfl) ⟨472443, by rfl⟩ : syracuseStep 1259849 = 944887) B944887
theorem B1259963 : Blo 838352 1259963 := bstep (se 1 (by rfl) ⟨944972, by rfl⟩ : syracuseStep 1259963 = 1889945) B1889945
theorem B899515 : Blo 838352 899515 := bstep (se 1 (by rfl) ⟨674636, by rfl⟩ : syracuseStep 899515 = 1349273) B1349273
theorem B1260023 : Blo 838352 1260023 := bstep (se 1 (by rfl) ⟨945017, by rfl⟩ : syracuseStep 1260023 = 1890035) B1890035
theorem B1260047 : Blo 838352 1260047 := bstep (se 1 (by rfl) ⟨945035, by rfl⟩ : syracuseStep 1260047 = 1890071) B1890071
theorem B1260089 : Blo 838352 1260089 := bstep (se 2 (by rfl) ⟨472533, by rfl⟩ : syracuseStep 1260089 = 945067) B945067
theorem B1260167 : Blo 838352 1260167 := bstep (se 1 (by rfl) ⟨945125, by rfl⟩ : syracuseStep 1260167 = 1890251) B1890251
theorem B1260203 : Blo 838352 1260203 := bstep (se 1 (by rfl) ⟨945152, by rfl⟩ : syracuseStep 1260203 = 1890305) B1890305
theorem B1260233 : Blo 838352 1260233 := bstep (se 2 (by rfl) ⟨472587, by rfl⟩ : syracuseStep 1260233 = 945175) B945175
theorem B3586817 : Blo 838352 3586817 := bstep (se 2 (by rfl) ⟨1345056, by rfl⟩ : syracuseStep 3586817 = 2690113) B2690113
theorem B1063687 : Blo 838352 1063687 := bstep (se 1 (by rfl) ⟨797765, by rfl⟩ : syracuseStep 1063687 = 1595531) B1595531
theorem B1260347 : Blo 838352 1260347 := bstep (se 1 (by rfl) ⟨945260, by rfl⟩ : syracuseStep 1260347 = 1890521) B1890521
theorem B1260407 : Blo 838352 1260407 := bstep (se 1 (by rfl) ⟨945305, by rfl⟩ : syracuseStep 1260407 = 1890611) B1890611
theorem B1260431 : Blo 838352 1260431 := bstep (se 1 (by rfl) ⟨945323, by rfl⟩ : syracuseStep 1260431 = 1890647) B1890647
theorem B1260473 : Blo 838352 1260473 := bstep (se 2 (by rfl) ⟨472677, by rfl⟩ : syracuseStep 1260473 = 945355) B945355
theorem B1260551 : Blo 838352 1260551 := bstep (se 1 (by rfl) ⟨945413, by rfl⟩ : syracuseStep 1260551 = 1890827) B1890827
theorem B1260587 : Blo 838352 1260587 := bstep (se 1 (by rfl) ⟨945440, by rfl⟩ : syracuseStep 1260587 = 1890881) B1890881
theorem B1260617 : Blo 838352 1260617 := bstep (se 2 (by rfl) ⟨472731, by rfl⟩ : syracuseStep 1260617 = 945463) B945463
theorem B3587159 : Blo 838352 3587159 := bstep (se 1 (by rfl) ⟨2690369, by rfl⟩ : syracuseStep 3587159 = 5380739) B5380739
theorem B1064107 : Blo 838352 1064107 := bstep (se 1 (by rfl) ⟨798080, by rfl⟩ : syracuseStep 1064107 = 1596161) B1596161
theorem B1260731 : Blo 838352 1260731 := bstep (se 1 (by rfl) ⟨945548, by rfl⟩ : syracuseStep 1260731 = 1891097) B1891097
theorem B1260791 : Blo 838352 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B3194113 : Blo 838352 3194113 := bstep (se 2 (by rfl) ⟨1197792, by rfl⟩ : syracuseStep 3194113 = 2395585) B2395585
theorem B1260815 : Blo 838352 1260815 := bstep (se 1 (by rfl) ⟨945611, by rfl⟩ : syracuseStep 1260815 = 1891223) B1891223
theorem B1260857 : Blo 838352 1260857 := bstep (se 2 (by rfl) ⟨472821, by rfl⟩ : syracuseStep 1260857 = 945643) B945643
theorem B1260935 : Blo 838352 1260935 := bstep (se 1 (by rfl) ⟨945701, by rfl⟩ : syracuseStep 1260935 = 1891403) B1891403
theorem B1064335 : Blo 838352 1064335 := bstep (se 1 (by rfl) ⟨798251, by rfl⟩ : syracuseStep 1064335 = 1596503) B1596503
theorem B2833811 : Blo 838352 2833811 := bstep (se 1 (by rfl) ⟨2125358, by rfl⟩ : syracuseStep 2833811 = 4250717) B4250717
theorem B1195435 : Blo 838352 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B1260971 : Blo 838352 1260971 := bstep (se 1 (by rfl) ⟨945728, by rfl⟩ : syracuseStep 1260971 = 1891457) B1891457
theorem B1261001 : Blo 838352 1261001 := bstep (se 2 (by rfl) ⟨472875, by rfl⟩ : syracuseStep 1261001 = 945751) B945751
theorem B12303875 : Blo 838352 12303875 := bstep (se 1 (by rfl) ⟨9227906, by rfl⟩ : syracuseStep 12303875 = 18455813) B18455813
theorem B1818155 : Blo 838352 1818155 := bstep (se 1 (by rfl) ⟨1363616, by rfl⟩ : syracuseStep 1818155 = 2727233) B2727233
theorem B472858165 : Blo 838352 472858165 := bstep (se 5 (by rfl) ⟨22165226, by rfl⟩ : syracuseStep 472858165 = 44330453) B44330453
theorem B1261115 : Blo 838352 1261115 := bstep (se 1 (by rfl) ⟨945836, by rfl⟩ : syracuseStep 1261115 = 1891673) B1891673
theorem B1261175 : Blo 838352 1261175 := bstep (se 1 (by rfl) ⟨945881, by rfl⟩ : syracuseStep 1261175 = 1891763) B1891763
theorem B1195663 : Blo 838352 1195663 := bstep (se 1 (by rfl) ⟨896747, by rfl⟩ : syracuseStep 1195663 = 1793495) B1793495
theorem B1261199 : Blo 838352 1261199 := bstep (se 1 (by rfl) ⟨945899, by rfl⟩ : syracuseStep 1261199 = 1891799) B1891799
theorem B1261241 : Blo 838352 1261241 := bstep (se 2 (by rfl) ⟨472965, by rfl⟩ : syracuseStep 1261241 = 945931) B945931
theorem B1261319 : Blo 838352 1261319 := bstep (se 1 (by rfl) ⟨945989, by rfl⟩ : syracuseStep 1261319 = 1891979) B1891979
theorem B1261355 : Blo 838352 1261355 := bstep (se 1 (by rfl) ⟨946016, by rfl⟩ : syracuseStep 1261355 = 1892033) B1892033
theorem B1261385 : Blo 838352 1261385 := bstep (se 2 (by rfl) ⟨473019, by rfl⟩ : syracuseStep 1261385 = 946039) B946039
theorem B1261499 : Blo 838352 1261499 := bstep (se 1 (by rfl) ⟨946124, by rfl⟩ : syracuseStep 1261499 = 1892249) B1892249
theorem B8077259 : Blo 838352 8077259 := bstep (se 1 (by rfl) ⟨6057944, by rfl⟩ : syracuseStep 8077259 = 12115889) B12115889
theorem B1261559 : Blo 838352 1261559 := bstep (se 1 (by rfl) ⟨946169, by rfl⟩ : syracuseStep 1261559 = 1892339) B1892339
theorem B1261583 : Blo 838352 1261583 := bstep (se 1 (by rfl) ⟨946187, by rfl⟩ : syracuseStep 1261583 = 1892375) B1892375
theorem B1261625 : Blo 838352 1261625 := bstep (se 2 (by rfl) ⟨473109, by rfl⟩ : syracuseStep 1261625 = 946219) B946219
theorem B1917047 : Blo 838352 1917047 := bstep (se 1 (by rfl) ⟨1437785, by rfl⟩ : syracuseStep 1917047 = 2875571) B2875571
theorem B1065079 : Blo 838352 1065079 := bstep (se 1 (by rfl) ⟨798809, by rfl⟩ : syracuseStep 1065079 = 1597619) B1597619
theorem B1261703 : Blo 838352 1261703 := bstep (se 1 (by rfl) ⟨946277, by rfl⟩ : syracuseStep 1261703 = 1892555) B1892555
theorem B1261739 : Blo 838352 1261739 := bstep (se 1 (by rfl) ⟨946304, by rfl⟩ : syracuseStep 1261739 = 1892609) B1892609
theorem B1261769 : Blo 838352 1261769 := bstep (se 2 (by rfl) ⟨473163, by rfl⟩ : syracuseStep 1261769 = 946327) B946327
theorem B1261883 : Blo 838352 1261883 := bstep (se 1 (by rfl) ⟨946412, by rfl⟩ : syracuseStep 1261883 = 1892825) B1892825
theorem B1261943 : Blo 838352 1261943 := bstep (se 1 (by rfl) ⟨946457, by rfl⟩ : syracuseStep 1261943 = 1892915) B1892915
theorem B1261967 : Blo 838352 1261967 := bstep (se 1 (by rfl) ⟨946475, by rfl⟩ : syracuseStep 1261967 = 1892951) B1892951
theorem B1262009 : Blo 838352 1262009 := bstep (se 2 (by rfl) ⟨473253, by rfl⟩ : syracuseStep 1262009 = 946507) B946507
theorem B1065403 : Blo 838352 1065403 := bstep (se 1 (by rfl) ⟨799052, by rfl⟩ : syracuseStep 1065403 = 1598105) B1598105
theorem B1262087 : Blo 838352 1262087 := bstep (se 1 (by rfl) ⟨946565, by rfl⟩ : syracuseStep 1262087 = 1893131) B1893131
theorem B1262123 : Blo 838352 1262123 := bstep (se 1 (by rfl) ⟨946592, by rfl⟩ : syracuseStep 1262123 = 1893185) B1893185
theorem B1262153 : Blo 838352 1262153 := bstep (se 2 (by rfl) ⟨473307, by rfl⟩ : syracuseStep 1262153 = 946615) B946615
theorem B1262267 : Blo 838352 1262267 := bstep (se 1 (by rfl) ⟨946700, by rfl⟩ : syracuseStep 1262267 = 1893401) B1893401
theorem B1262327 : Blo 838352 1262327 := bstep (se 1 (by rfl) ⟨946745, by rfl⟩ : syracuseStep 1262327 = 1893491) B1893491
theorem B2835215 : Blo 838352 2835215 := bstep (se 1 (by rfl) ⟨2126411, by rfl⟩ : syracuseStep 2835215 = 4252823) B4252823
theorem B1262351 : Blo 838352 1262351 := bstep (se 1 (by rfl) ⟨946763, by rfl⟩ : syracuseStep 1262351 = 1893527) B1893527
theorem B1262393 : Blo 838352 1262393 := bstep (se 2 (by rfl) ⟨473397, by rfl⟩ : syracuseStep 1262393 = 946795) B946795
theorem B1262471 : Blo 838352 1262471 := bstep (se 1 (by rfl) ⟨946853, by rfl⟩ : syracuseStep 1262471 = 1893707) B1893707
theorem B1262507 : Blo 838352 1262507 := bstep (se 1 (by rfl) ⟨946880, by rfl⟩ : syracuseStep 1262507 = 1893761) B1893761
theorem B1065899 : Blo 838352 1065899 := bstep (se 1 (by rfl) ⟨799424, by rfl⟩ : syracuseStep 1065899 = 1598849) B1598849
theorem B1262537 : Blo 838352 1262537 := bstep (se 2 (by rfl) ⟨473451, by rfl⟩ : syracuseStep 1262537 = 946903) B946903
theorem B3589073 : Blo 838352 3589073 := bstep (se 2 (by rfl) ⟨1345902, by rfl⟩ : syracuseStep 3589073 = 2691805) B2691805
theorem B2835485 : Blo 838352 2835485 := bstep (se 3 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 2835485 = 1063307) B1063307
theorem B1262651 : Blo 838352 1262651 := bstep (se 1 (by rfl) ⟨946988, by rfl⟩ : syracuseStep 1262651 = 1893977) B1893977
theorem B1262711 : Blo 838352 1262711 := bstep (se 1 (by rfl) ⟨947033, by rfl⟩ : syracuseStep 1262711 = 1894067) B1894067
theorem B1262735 : Blo 838352 1262735 := bstep (se 1 (by rfl) ⟨947051, by rfl⟩ : syracuseStep 1262735 = 1894103) B1894103
theorem B1262777 : Blo 838352 1262777 := bstep (se 2 (by rfl) ⟨473541, by rfl⟩ : syracuseStep 1262777 = 947083) B947083
theorem B4670693 : Blo 838352 4670693 := bstep (se 4 (by rfl) ⟨437877, by rfl⟩ : syracuseStep 4670693 = 875755) B875755
theorem B1262855 : Blo 838352 1262855 := bstep (se 1 (by rfl) ⟨947141, by rfl⟩ : syracuseStep 1262855 = 1894283) B1894283
theorem B1262891 : Blo 838352 1262891 := bstep (se 1 (by rfl) ⟨947168, by rfl⟩ : syracuseStep 1262891 = 1894337) B1894337
theorem B1262921 : Blo 838352 1262921 := bstep (se 2 (by rfl) ⟨473595, by rfl⟩ : syracuseStep 1262921 = 947191) B947191
theorem B9684355 : Blo 838352 9684355 := bstep (se 1 (by rfl) ⟨7263266, by rfl⟩ : syracuseStep 9684355 = 14526533) B14526533
theorem B1263035 : Blo 838352 1263035 := bstep (se 1 (by rfl) ⟨947276, by rfl⟩ : syracuseStep 1263035 = 1894553) B1894553
theorem B1263095 : Blo 838352 1263095 := bstep (se 1 (by rfl) ⟨947321, by rfl⟩ : syracuseStep 1263095 = 1894643) B1894643
theorem B1263119 : Blo 838352 1263119 := bstep (se 1 (by rfl) ⟨947339, by rfl⟩ : syracuseStep 1263119 = 1894679) B1894679
theorem B1263161 : Blo 838352 1263161 := bstep (se 2 (by rfl) ⟨473685, by rfl⟩ : syracuseStep 1263161 = 947371) B947371
theorem B3884663 : Blo 838352 3884663 := bstep (se 1 (by rfl) ⟨2913497, by rfl⟩ : syracuseStep 3884663 = 5826995) B5826995
theorem B1263239 : Blo 838352 1263239 := bstep (se 1 (by rfl) ⟨947429, by rfl⟩ : syracuseStep 1263239 = 1894859) B1894859
theorem B1263275 : Blo 838352 1263275 := bstep (se 1 (by rfl) ⟨947456, by rfl⟩ : syracuseStep 1263275 = 1894913) B1894913
theorem B1263305 : Blo 838352 1263305 := bstep (se 2 (by rfl) ⟨473739, by rfl⟩ : syracuseStep 1263305 = 947479) B947479
theorem B1263419 : Blo 838352 1263419 := bstep (se 1 (by rfl) ⟨947564, by rfl⟩ : syracuseStep 1263419 = 1895129) B1895129
theorem B1263479 : Blo 838352 1263479 := bstep (se 1 (by rfl) ⟨947609, by rfl⟩ : syracuseStep 1263479 = 1895219) B1895219
theorem B1263503 : Blo 838352 1263503 := bstep (se 1 (by rfl) ⟨947627, by rfl⟩ : syracuseStep 1263503 = 1895255) B1895255
theorem B8079257 : Blo 838352 8079257 := bstep (se 2 (by rfl) ⟨3029721, by rfl⟩ : syracuseStep 8079257 = 6059443) B6059443
theorem B4245533 : Blo 838352 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B3197015 : Blo 838352 3197015 := bstep (se 1 (by rfl) ⟨2397761, by rfl⟩ : syracuseStep 3197015 = 4795523) B4795523
theorem B1886327 : Blo 838352 1886327 := bstep (se 1 (by rfl) ⟨1414745, by rfl⟩ : syracuseStep 1886327 = 2829491) B2829491
theorem B8407277 : Blo 838352 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B1198351 : Blo 838352 1198351 := bstep (se 1 (by rfl) ⟨898763, by rfl⟩ : syracuseStep 1198351 = 1797527) B1797527
theorem B1886507 : Blo 838352 1886507 := bstep (se 1 (by rfl) ⟨1414880, by rfl⟩ : syracuseStep 1886507 = 2829761) B2829761
theorem B1198471 : Blo 838352 1198471 := bstep (se 1 (by rfl) ⟨898853, by rfl⟩ : syracuseStep 1198471 = 1797707) B1797707
theorem B2836889 : Blo 838352 2836889 := bstep (se 2 (by rfl) ⟨1063833, by rfl⟩ : syracuseStep 2836889 = 2127667) B2127667
theorem B4246019 : Blo 838352 4246019 := bstep (se 1 (by rfl) ⟨3184514, by rfl⟩ : syracuseStep 4246019 = 6369029) B6369029
theorem B4540931 : Blo 838352 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B3197501 : Blo 838352 3197501 := bstep (se 3 (by rfl) ⟨599531, by rfl⟩ : syracuseStep 3197501 = 1199063) B1199063
theorem B1886867 : Blo 838352 1886867 := bstep (se 1 (by rfl) ⟨1415150, by rfl⟩ : syracuseStep 1886867 = 2830301) B2830301
theorem B1886921 : Blo 838352 1886921 := bstep (se 2 (by rfl) ⟨707595, by rfl⟩ : syracuseStep 1886921 = 1415191) B1415191
theorem B8604377 : Blo 838352 8604377 := bstep (se 2 (by rfl) ⟨3226641, by rfl⟩ : syracuseStep 8604377 = 6453283) B6453283
theorem B838407 : Blo 838352 838407 := bstep (se 1 (by rfl) ⟨628805, by rfl⟩ : syracuseStep 838407 = 1257611) B1257611
theorem B838415 : Blo 838352 838415 := bstep (se 1 (by rfl) ⟨628811, by rfl⟩ : syracuseStep 838415 = 1257623) B1257623
theorem B838459 : Blo 838352 838459 := bstep (se 1 (by rfl) ⟨628844, by rfl⟩ : syracuseStep 838459 = 1257689) B1257689
theorem B838535 : Blo 838352 838535 := bstep (se 1 (by rfl) ⟨628901, by rfl⟩ : syracuseStep 838535 = 1257803) B1257803
theorem B838543 : Blo 838352 838543 := bstep (se 1 (by rfl) ⟨628907, by rfl⟩ : syracuseStep 838543 = 1257815) B1257815
theorem B838587 : Blo 838352 838587 := bstep (se 1 (by rfl) ⟨628940, by rfl⟩ : syracuseStep 838587 = 1257881) B1257881
theorem B838663 : Blo 838352 838663 := bstep (se 1 (by rfl) ⟨628997, by rfl⟩ : syracuseStep 838663 = 1257995) B1257995
theorem B838671 : Blo 838352 838671 := bstep (se 1 (by rfl) ⟨629003, by rfl⟩ : syracuseStep 838671 = 1258007) B1258007
theorem B838715 : Blo 838352 838715 := bstep (se 1 (by rfl) ⟨629036, by rfl⟩ : syracuseStep 838715 = 1258073) B1258073
theorem B2837591 : Blo 838352 2837591 := bstep (se 1 (by rfl) ⟨2128193, by rfl⟩ : syracuseStep 2837591 = 4256387) B4256387
theorem B838791 : Blo 838352 838791 := bstep (se 1 (by rfl) ⟨629093, by rfl⟩ : syracuseStep 838791 = 1258187) B1258187
theorem B1592455 : Blo 838352 1592455 := bstep (se 1 (by rfl) ⟨1194341, by rfl⟩ : syracuseStep 1592455 = 2388683) B2388683
theorem B838799 : Blo 838352 838799 := bstep (se 1 (by rfl) ⟨629099, by rfl⟩ : syracuseStep 838799 = 1258199) B1258199
theorem B838843 : Blo 838352 838843 := bstep (se 1 (by rfl) ⟨629132, by rfl⟩ : syracuseStep 838843 = 1258265) B1258265
theorem B838919 : Blo 838352 838919 := bstep (se 1 (by rfl) ⟨629189, by rfl⟩ : syracuseStep 838919 = 1258379) B1258379
theorem B838927 : Blo 838352 838927 := bstep (se 1 (by rfl) ⟨629195, by rfl⟩ : syracuseStep 838927 = 1258391) B1258391
theorem B838971 : Blo 838352 838971 := bstep (se 1 (by rfl) ⟨629228, by rfl⟩ : syracuseStep 838971 = 1258457) B1258457
theorem B1133897 : Blo 838352 1133897 := bstep (se 2 (by rfl) ⟨425211, by rfl⟩ : syracuseStep 1133897 = 850423) B850423
theorem B1887623 : Blo 838352 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B839047 : Blo 838352 839047 := bstep (se 1 (by rfl) ⟨629285, by rfl⟩ : syracuseStep 839047 = 1258571) B1258571
theorem B839055 : Blo 838352 839055 := bstep (se 1 (by rfl) ⟨629291, by rfl⟩ : syracuseStep 839055 = 1258583) B1258583
theorem B839099 : Blo 838352 839099 := bstep (se 1 (by rfl) ⟨629324, by rfl⟩ : syracuseStep 839099 = 1258649) B1258649
theorem B839175 : Blo 838352 839175 := bstep (se 1 (by rfl) ⟨629381, by rfl⟩ : syracuseStep 839175 = 1258763) B1258763
theorem B839183 : Blo 838352 839183 := bstep (se 1 (by rfl) ⟨629387, by rfl⟩ : syracuseStep 839183 = 1258775) B1258775
theorem B1887803 : Blo 838352 1887803 := bstep (se 1 (by rfl) ⟨1415852, by rfl⟩ : syracuseStep 1887803 = 2831705) B2831705
theorem B839227 : Blo 838352 839227 := bstep (se 1 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 839227 = 1258841) B1258841
theorem B2838077 : Blo 838352 2838077 := bstep (se 3 (by rfl) ⟨532139, by rfl⟩ : syracuseStep 2838077 = 1064279) B1064279
theorem B839303 : Blo 838352 839303 := bstep (se 1 (by rfl) ⟨629477, by rfl⟩ : syracuseStep 839303 = 1258955) B1258955
theorem B839311 : Blo 838352 839311 := bstep (se 1 (by rfl) ⟨629483, by rfl⟩ : syracuseStep 839311 = 1258967) B1258967
theorem B1887929 : Blo 838352 1887929 := bstep (se 2 (by rfl) ⟨707973, by rfl⟩ : syracuseStep 1887929 = 1415947) B1415947
theorem B1593017 : Blo 838352 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B839355 : Blo 838352 839355 := bstep (se 1 (by rfl) ⟨629516, by rfl⟩ : syracuseStep 839355 = 1259033) B1259033
theorem B839431 : Blo 838352 839431 := bstep (se 1 (by rfl) ⟨629573, by rfl⟩ : syracuseStep 839431 = 1259147) B1259147
theorem B839439 : Blo 838352 839439 := bstep (se 1 (by rfl) ⟨629579, by rfl⟩ : syracuseStep 839439 = 1259159) B1259159
theorem B3460897 : Blo 838352 3460897 := bstep (se 2 (by rfl) ⟨1297836, by rfl⟩ : syracuseStep 3460897 = 2595673) B2595673
theorem B839483 : Blo 838352 839483 := bstep (se 1 (by rfl) ⟨629612, by rfl⟩ : syracuseStep 839483 = 1259225) B1259225
theorem B839559 : Blo 838352 839559 := bstep (se 1 (by rfl) ⟨629669, by rfl⟩ : syracuseStep 839559 = 1259339) B1259339
theorem B839567 : Blo 838352 839567 := bstep (se 1 (by rfl) ⟨629675, by rfl⟩ : syracuseStep 839567 = 1259351) B1259351
theorem B9097123 : Blo 838352 9097123 := bstep (se 1 (by rfl) ⟨6822842, by rfl⟩ : syracuseStep 9097123 = 13645685) B13645685
theorem B839611 : Blo 838352 839611 := bstep (se 1 (by rfl) ⟨629708, by rfl⟩ : syracuseStep 839611 = 1259417) B1259417
theorem B16175051 : Blo 838352 16175051 := bstep (se 1 (by rfl) ⟨12131288, by rfl⟩ : syracuseStep 16175051 = 24262577) B24262577
theorem B839687 : Blo 838352 839687 := bstep (se 1 (by rfl) ⟨629765, by rfl⟩ : syracuseStep 839687 = 1259531) B1259531
theorem B1888271 : Blo 838352 1888271 := bstep (se 1 (by rfl) ⟨1416203, by rfl⟩ : syracuseStep 1888271 = 2832407) B2832407
theorem B839695 : Blo 838352 839695 := bstep (se 1 (by rfl) ⟨629771, by rfl⟩ : syracuseStep 839695 = 1259543) B1259543
theorem B1888289 : Blo 838352 1888289 := bstep (se 2 (by rfl) ⟨708108, by rfl⟩ : syracuseStep 1888289 = 1416217) B1416217
theorem B839739 : Blo 838352 839739 := bstep (se 1 (by rfl) ⟨629804, by rfl⟩ : syracuseStep 839739 = 1259609) B1259609
theorem B4247639 : Blo 838352 4247639 := bstep (se 1 (by rfl) ⟨3185729, by rfl⟩ : syracuseStep 4247639 = 6371459) B6371459
theorem B839815 : Blo 838352 839815 := bstep (se 1 (by rfl) ⟨629861, by rfl⟩ : syracuseStep 839815 = 1259723) B1259723
theorem B839823 : Blo 838352 839823 := bstep (se 1 (by rfl) ⟨629867, by rfl⟩ : syracuseStep 839823 = 1259735) B1259735
theorem B6475949 : Blo 838352 6475949 := bstep (se 3 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 6475949 = 2428481) B2428481
theorem B839867 : Blo 838352 839867 := bstep (se 1 (by rfl) ⟨629900, by rfl⟩ : syracuseStep 839867 = 1259801) B1259801
theorem B839943 : Blo 838352 839943 := bstep (se 1 (by rfl) ⟨629957, by rfl⟩ : syracuseStep 839943 = 1259915) B1259915
theorem B839951 : Blo 838352 839951 := bstep (se 1 (by rfl) ⟨629963, by rfl⟩ : syracuseStep 839951 = 1259927) B1259927
theorem B839995 : Blo 838352 839995 := bstep (se 1 (by rfl) ⟨629996, by rfl⟩ : syracuseStep 839995 = 1259993) B1259993
theorem B1888631 : Blo 838352 1888631 := bstep (se 1 (by rfl) ⟨1416473, by rfl⟩ : syracuseStep 1888631 = 2832947) B2832947
theorem B840071 : Blo 838352 840071 := bstep (se 1 (by rfl) ⟨630053, by rfl⟩ : syracuseStep 840071 = 1260107) B1260107
theorem B840079 : Blo 838352 840079 := bstep (se 1 (by rfl) ⟨630059, by rfl⟩ : syracuseStep 840079 = 1260119) B1260119
theorem B840123 : Blo 838352 840123 := bstep (se 1 (by rfl) ⟨630092, by rfl⟩ : syracuseStep 840123 = 1260185) B1260185
theorem B840199 : Blo 838352 840199 := bstep (se 1 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 840199 = 1260299) B1260299
theorem B840207 : Blo 838352 840207 := bstep (se 1 (by rfl) ⟨630155, by rfl⟩ : syracuseStep 840207 = 1260311) B1260311
theorem B1888811 : Blo 838352 1888811 := bstep (se 1 (by rfl) ⟨1416608, by rfl⟩ : syracuseStep 1888811 = 2833217) B2833217
theorem B840251 : Blo 838352 840251 := bstep (se 1 (by rfl) ⟨630188, by rfl⟩ : syracuseStep 840251 = 1260377) B1260377
theorem B4248125 : Blo 838352 4248125 := bstep (se 3 (by rfl) ⟨796523, by rfl⟩ : syracuseStep 4248125 = 1593047) B1593047
theorem B41538179 : Blo 838352 41538179 := bstep (se 1 (by rfl) ⟨31153634, by rfl⟩ : syracuseStep 41538179 = 62307269) B62307269
theorem B1790599 : Blo 838352 1790599 := bstep (se 1 (by rfl) ⟨1342949, by rfl⟩ : syracuseStep 1790599 = 2685899) B2685899
theorem B840327 : Blo 838352 840327 := bstep (se 1 (by rfl) ⟨630245, by rfl⟩ : syracuseStep 840327 = 1260491) B1260491
theorem B840335 : Blo 838352 840335 := bstep (se 1 (by rfl) ⟨630251, by rfl⟩ : syracuseStep 840335 = 1260503) B1260503
theorem B840379 : Blo 838352 840379 := bstep (se 1 (by rfl) ⟨630284, by rfl⟩ : syracuseStep 840379 = 1260569) B1260569
theorem B6804161 : Blo 838352 6804161 := bstep (se 2 (by rfl) ⟨2551560, by rfl⟩ : syracuseStep 6804161 = 5103121) B5103121
theorem B840455 : Blo 838352 840455 := bstep (se 1 (by rfl) ⟨630341, by rfl⟩ : syracuseStep 840455 = 1260683) B1260683
theorem B840463 : Blo 838352 840463 := bstep (se 1 (by rfl) ⟨630347, by rfl⟩ : syracuseStep 840463 = 1260695) B1260695
theorem B2872097 : Blo 838352 2872097 := bstep (se 2 (by rfl) ⟨1077036, by rfl⟩ : syracuseStep 2872097 = 2154073) B2154073
theorem B1594171 : Blo 838352 1594171 := bstep (se 1 (by rfl) ⟨1195628, by rfl⟩ : syracuseStep 1594171 = 2391257) B2391257
theorem B840507 : Blo 838352 840507 := bstep (se 1 (by rfl) ⟨630380, by rfl⟩ : syracuseStep 840507 = 1260761) B1260761
theorem B840583 : Blo 838352 840583 := bstep (se 1 (by rfl) ⟨630437, by rfl⟩ : syracuseStep 840583 = 1260875) B1260875
theorem B840591 : Blo 838352 840591 := bstep (se 1 (by rfl) ⟨630443, by rfl⟩ : syracuseStep 840591 = 1260887) B1260887
theorem B1889171 : Blo 838352 1889171 := bstep (se 1 (by rfl) ⟨1416878, by rfl⟩ : syracuseStep 1889171 = 2833757) B2833757
theorem B2839481 : Blo 838352 2839481 := bstep (se 2 (by rfl) ⟨1064805, by rfl⟩ : syracuseStep 2839481 = 2129611) B2129611
theorem B840635 : Blo 838352 840635 := bstep (se 1 (by rfl) ⟨630476, by rfl⟩ : syracuseStep 840635 = 1260953) B1260953
theorem B1889225 : Blo 838352 1889225 := bstep (se 2 (by rfl) ⟨708459, by rfl⟩ : syracuseStep 1889225 = 1416919) B1416919
theorem B840711 : Blo 838352 840711 := bstep (se 1 (by rfl) ⟨630533, by rfl⟩ : syracuseStep 840711 = 1261067) B1261067
theorem B840719 : Blo 838352 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B840763 : Blo 838352 840763 := bstep (se 1 (by rfl) ⟨630572, by rfl⟩ : syracuseStep 840763 = 1261145) B1261145
theorem B840839 : Blo 838352 840839 := bstep (se 1 (by rfl) ⟨630629, by rfl⟩ : syracuseStep 840839 = 1261259) B1261259
theorem B840847 : Blo 838352 840847 := bstep (se 1 (by rfl) ⟨630635, by rfl⟩ : syracuseStep 840847 = 1261271) B1261271
theorem B8082605 : Blo 838352 8082605 := bstep (se 3 (by rfl) ⟨1515488, by rfl⟩ : syracuseStep 8082605 = 3030977) B3030977
theorem B840891 : Blo 838352 840891 := bstep (se 1 (by rfl) ⟨630668, by rfl⟩ : syracuseStep 840891 = 1261337) B1261337
theorem B10245365 : Blo 838352 10245365 := bstep (se 5 (by rfl) ⟨480251, by rfl⟩ : syracuseStep 10245365 = 960503) B960503
theorem B840967 : Blo 838352 840967 := bstep (se 1 (by rfl) ⟨630725, by rfl⟩ : syracuseStep 840967 = 1261451) B1261451
theorem B840975 : Blo 838352 840975 := bstep (se 1 (by rfl) ⟨630731, by rfl⟩ : syracuseStep 840975 = 1261463) B1261463
theorem B1594657 : Blo 838352 1594657 := bstep (se 2 (by rfl) ⟨597996, by rfl⟩ : syracuseStep 1594657 = 1195993) B1195993
theorem B841019 : Blo 838352 841019 := bstep (se 1 (by rfl) ⟨630764, by rfl⟩ : syracuseStep 841019 = 1261529) B1261529
theorem B15324551 : Blo 838352 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B841095 : Blo 838352 841095 := bstep (se 1 (by rfl) ⟨630821, by rfl⟩ : syracuseStep 841095 = 1261643) B1261643
theorem B841103 : Blo 838352 841103 := bstep (se 1 (by rfl) ⟨630827, by rfl⟩ : syracuseStep 841103 = 1261655) B1261655
theorem B841147 : Blo 838352 841147 := bstep (se 1 (by rfl) ⟨630860, by rfl⟩ : syracuseStep 841147 = 1261721) B1261721
theorem B841223 : Blo 838352 841223 := bstep (se 1 (by rfl) ⟨630917, by rfl⟩ : syracuseStep 841223 = 1261835) B1261835
theorem B2840075 : Blo 838352 2840075 := bstep (se 1 (by rfl) ⟨2130056, by rfl⟩ : syracuseStep 2840075 = 4260113) B4260113
theorem B841231 : Blo 838352 841231 := bstep (se 1 (by rfl) ⟨630923, by rfl⟩ : syracuseStep 841231 = 1261847) B1261847
theorem B841275 : Blo 838352 841275 := bstep (se 1 (by rfl) ⟨630956, by rfl⟩ : syracuseStep 841275 = 1261913) B1261913
theorem B2840183 : Blo 838352 2840183 := bstep (se 1 (by rfl) ⟨2130137, by rfl⟩ : syracuseStep 2840183 = 4260275) B4260275
theorem B1889927 : Blo 838352 1889927 := bstep (se 1 (by rfl) ⟨1417445, by rfl⟩ : syracuseStep 1889927 = 2834891) B2834891
theorem B841351 : Blo 838352 841351 := bstep (se 1 (by rfl) ⟨631013, by rfl⟩ : syracuseStep 841351 = 1262027) B1262027
theorem B841359 : Blo 838352 841359 := bstep (se 1 (by rfl) ⟨631019, by rfl⟩ : syracuseStep 841359 = 1262039) B1262039
theorem B841403 : Blo 838352 841403 := bstep (se 1 (by rfl) ⟨631052, by rfl⟩ : syracuseStep 841403 = 1262105) B1262105
theorem B4544237 : Blo 838352 4544237 := bstep (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) B1704089
theorem B841479 : Blo 838352 841479 := bstep (se 1 (by rfl) ⟨631109, by rfl⟩ : syracuseStep 841479 = 1262219) B1262219
theorem B841487 : Blo 838352 841487 := bstep (se 1 (by rfl) ⟨631115, by rfl⟩ : syracuseStep 841487 = 1262231) B1262231
theorem B1791803 : Blo 838352 1791803 := bstep (se 1 (by rfl) ⟨1343852, by rfl⟩ : syracuseStep 1791803 = 2687705) B2687705
theorem B1890107 : Blo 838352 1890107 := bstep (se 1 (by rfl) ⟨1417580, by rfl⟩ : syracuseStep 1890107 = 2835161) B2835161
theorem B841531 : Blo 838352 841531 := bstep (se 1 (by rfl) ⟨631148, by rfl⟩ : syracuseStep 841531 = 1262297) B1262297
theorem B841607 : Blo 838352 841607 := bstep (se 1 (by rfl) ⟨631205, by rfl⟩ : syracuseStep 841607 = 1262411) B1262411
theorem B841615 : Blo 838352 841615 := bstep (se 1 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 841615 = 1262423) B1262423
theorem B2021267 : Blo 838352 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B3594131 : Blo 838352 3594131 := bstep (se 1 (by rfl) ⟨2695598, by rfl⟩ : syracuseStep 3594131 = 5391197) B5391197
theorem B1890233 : Blo 838352 1890233 := bstep (se 2 (by rfl) ⟨708837, by rfl⟩ : syracuseStep 1890233 = 1417675) B1417675
theorem B841659 : Blo 838352 841659 := bstep (se 1 (by rfl) ⟨631244, by rfl⟩ : syracuseStep 841659 = 1262489) B1262489
theorem B841735 : Blo 838352 841735 := bstep (se 1 (by rfl) ⟨631301, by rfl⟩ : syracuseStep 841735 = 1262603) B1262603
theorem B841743 : Blo 838352 841743 := bstep (se 1 (by rfl) ⟨631307, by rfl⟩ : syracuseStep 841743 = 1262615) B1262615
theorem B9099287 : Blo 838352 9099287 := bstep (se 1 (by rfl) ⟨6824465, by rfl⟩ : syracuseStep 9099287 = 13648931) B13648931
theorem B3889181 : Blo 838352 3889181 := bstep (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) B1458443
theorem B841787 : Blo 838352 841787 := bstep (se 1 (by rfl) ⟨631340, by rfl⟩ : syracuseStep 841787 = 1262681) B1262681
theorem B841863 : Blo 838352 841863 := bstep (se 1 (by rfl) ⟨631397, by rfl⟩ : syracuseStep 841863 = 1262795) B1262795
theorem B841871 : Blo 838352 841871 := bstep (se 1 (by rfl) ⟨631403, by rfl⟩ : syracuseStep 841871 = 1262807) B1262807
theorem B841915 : Blo 838352 841915 := bstep (se 1 (by rfl) ⟨631436, by rfl⟩ : syracuseStep 841915 = 1262873) B1262873
theorem B14342345 : Blo 838352 14342345 := bstep (se 2 (by rfl) ⟨5378379, by rfl⟩ : syracuseStep 14342345 = 10756759) B10756759
theorem B6379721 : Blo 838352 6379721 := bstep (se 2 (by rfl) ⟨2392395, by rfl⟩ : syracuseStep 6379721 = 4784791) B4784791
theorem B2840777 : Blo 838352 2840777 := bstep (se 2 (by rfl) ⟨1065291, by rfl⟩ : syracuseStep 2840777 = 2130583) B2130583
theorem B841991 : Blo 838352 841991 := bstep (se 1 (by rfl) ⟨631493, by rfl⟩ : syracuseStep 841991 = 1262987) B1262987
theorem B1890575 : Blo 838352 1890575 := bstep (se 1 (by rfl) ⟨1417931, by rfl⟩ : syracuseStep 1890575 = 2835863) B2835863
theorem B841999 : Blo 838352 841999 := bstep (se 1 (by rfl) ⟨631499, by rfl⟩ : syracuseStep 841999 = 1262999) B1262999
theorem B1890593 : Blo 838352 1890593 := bstep (se 2 (by rfl) ⟨708972, by rfl⟩ : syracuseStep 1890593 = 1417945) B1417945
theorem B4249907 : Blo 838352 4249907 := bstep (se 1 (by rfl) ⟨3187430, by rfl⟩ : syracuseStep 4249907 = 6374861) B6374861
theorem B1792315 : Blo 838352 1792315 := bstep (se 1 (by rfl) ⟨1344236, by rfl⟩ : syracuseStep 1792315 = 2688473) B2688473
theorem B842043 : Blo 838352 842043 := bstep (se 1 (by rfl) ⟨631532, by rfl⟩ : syracuseStep 842043 = 1263065) B1263065
theorem B842119 : Blo 838352 842119 := bstep (se 1 (by rfl) ⟨631589, by rfl⟩ : syracuseStep 842119 = 1263179) B1263179
theorem B842127 : Blo 838352 842127 := bstep (se 1 (by rfl) ⟨631595, by rfl⟩ : syracuseStep 842127 = 1263191) B1263191
theorem B842171 : Blo 838352 842171 := bstep (se 1 (by rfl) ⟨631628, by rfl⟩ : syracuseStep 842171 = 1263257) B1263257
theorem B1137097 : Blo 838352 1137097 := bstep (se 2 (by rfl) ⟨426411, by rfl⟩ : syracuseStep 1137097 = 852823) B852823
theorem B842247 : Blo 838352 842247 := bstep (se 1 (by rfl) ⟨631685, by rfl⟩ : syracuseStep 842247 = 1263371) B1263371
theorem B842255 : Blo 838352 842255 := bstep (se 1 (by rfl) ⟨631691, by rfl⟩ : syracuseStep 842255 = 1263383) B1263383
theorem B1595963 : Blo 838352 1595963 := bstep (se 1 (by rfl) ⟨1196972, by rfl⟩ : syracuseStep 1595963 = 2393945) B2393945
theorem B842299 : Blo 838352 842299 := bstep (se 1 (by rfl) ⟨631724, by rfl⟩ : syracuseStep 842299 = 1263449) B1263449
theorem B9558647 : Blo 838352 9558647 := bstep (se 1 (by rfl) ⟨7168985, by rfl⟩ : syracuseStep 9558647 = 14337971) B14337971
theorem B4250231 : Blo 838352 4250231 := bstep (se 1 (by rfl) ⟨3187673, by rfl⟩ : syracuseStep 4250231 = 6375347) B6375347
theorem B1890935 : Blo 838352 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B1891115 : Blo 838352 1891115 := bstep (se 1 (by rfl) ⟨1418336, by rfl⟩ : syracuseStep 1891115 = 2836673) B2836673
theorem B2841479 : Blo 838352 2841479 := bstep (se 1 (by rfl) ⟨2131109, by rfl⟩ : syracuseStep 2841479 = 4262219) B4262219
theorem B4774859 : Blo 838352 4774859 := bstep (se 1 (by rfl) ⟨3581144, by rfl⟩ : syracuseStep 4774859 = 7162289) B7162289
theorem B1137655 : Blo 838352 1137655 := bstep (se 1 (by rfl) ⟨853241, by rfl⟩ : syracuseStep 1137655 = 1706483) B1706483
theorem B1596449 : Blo 838352 1596449 := bstep (se 2 (by rfl) ⟨598668, by rfl⟩ : syracuseStep 1596449 = 1197337) B1197337
theorem B1891475 : Blo 838352 1891475 := bstep (se 1 (by rfl) ⟨1418606, by rfl⟩ : syracuseStep 1891475 = 2837213) B2837213
theorem B1596601 : Blo 838352 1596601 := bstep (se 2 (by rfl) ⟨598725, by rfl⟩ : syracuseStep 1596601 = 1197451) B1197451
theorem B1891529 : Blo 838352 1891529 := bstep (se 2 (by rfl) ⟨709323, by rfl⟩ : syracuseStep 1891529 = 1418647) B1418647
theorem B2841857 : Blo 838352 2841857 := bstep (se 2 (by rfl) ⟨1065696, by rfl⟩ : syracuseStep 2841857 = 2131393) B2131393
theorem B4251203 : Blo 838352 4251203 := bstep (se 1 (by rfl) ⟨3188402, by rfl⟩ : syracuseStep 4251203 = 6376805) B6376805
theorem B4775543 : Blo 838352 4775543 := bstep (se 1 (by rfl) ⟨3581657, by rfl⟩ : syracuseStep 4775543 = 7163315) B7163315
theorem B3071759 : Blo 838352 3071759 := bstep (se 1 (by rfl) ⟨2303819, by rfl⟩ : syracuseStep 3071759 = 4607639) B4607639
theorem B1007419 : Blo 838352 1007419 := bstep (se 1 (by rfl) ⟨755564, by rfl⟩ : syracuseStep 1007419 = 1511129) B1511129
theorem B7659353 : Blo 838352 7659353 := bstep (se 2 (by rfl) ⟨2872257, by rfl⟩ : syracuseStep 7659353 = 5744515) B5744515
theorem B3596147 : Blo 838352 3596147 := bstep (se 1 (by rfl) ⟨2697110, by rfl⟩ : syracuseStep 3596147 = 5394221) B5394221
theorem B4251527 : Blo 838352 4251527 := bstep (se 1 (by rfl) ⟨3188645, by rfl⟩ : syracuseStep 4251527 = 6377291) B6377291
theorem B1892231 : Blo 838352 1892231 := bstep (se 1 (by rfl) ⟨1419173, by rfl⟩ : syracuseStep 1892231 = 2838347) B2838347
theorem B20406167 : Blo 838352 20406167 := bstep (se 1 (by rfl) ⟨15304625, by rfl⟩ : syracuseStep 20406167 = 30609251) B30609251
theorem B4087811 : Blo 838352 4087811 := bstep (se 1 (by rfl) ⟨3065858, by rfl⟩ : syracuseStep 4087811 = 6131717) B6131717
theorem B2842667 : Blo 838352 2842667 := bstep (se 1 (by rfl) ⟨2132000, by rfl⟩ : syracuseStep 2842667 = 4264001) B4264001
theorem B1892411 : Blo 838352 1892411 := bstep (se 1 (by rfl) ⟨1419308, by rfl⟩ : syracuseStep 1892411 = 2838617) B2838617
theorem B1892537 : Blo 838352 1892537 := bstep (se 2 (by rfl) ⟨709701, by rfl⟩ : syracuseStep 1892537 = 1419403) B1419403
theorem B1007803 : Blo 838352 1007803 := bstep (se 1 (by rfl) ⟨755852, by rfl⟩ : syracuseStep 1007803 = 1511705) B1511705
theorem B2154871 : Blo 838352 2154871 := bstep (se 1 (by rfl) ⟨1616153, by rfl⟩ : syracuseStep 2154871 = 3232307) B3232307
theorem B1892879 : Blo 838352 1892879 := bstep (se 1 (by rfl) ⟨1419659, by rfl⟩ : syracuseStep 1892879 = 2839319) B2839319
theorem B1892897 : Blo 838352 1892897 := bstep (se 2 (by rfl) ⟨709836, by rfl⟩ : syracuseStep 1892897 = 1419673) B1419673
theorem B1893239 : Blo 838352 1893239 := bstep (se 1 (by rfl) ⟨1419929, by rfl⟩ : syracuseStep 1893239 = 2839859) B2839859
theorem B1598393 : Blo 838352 1598393 := bstep (se 2 (by rfl) ⟨599397, by rfl⟩ : syracuseStep 1598393 = 1198795) B1198795
theorem B4842499 : Blo 838352 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B1893419 : Blo 838352 1893419 := bstep (se 1 (by rfl) ⟨1420064, by rfl⟩ : syracuseStep 1893419 = 2840129) B2840129
theorem B2155673 : Blo 838352 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B943375 : Blo 838352 943375 := bstep (se 1 (by rfl) ⟨707531, by rfl⟩ : syracuseStep 943375 = 1415063) B1415063
theorem B3073339 : Blo 838352 3073339 := bstep (se 1 (by rfl) ⟨2305004, by rfl⟩ : syracuseStep 3073339 = 4610009) B4610009
theorem B1893779 : Blo 838352 1893779 := bstep (se 1 (by rfl) ⟨1420334, by rfl⟩ : syracuseStep 1893779 = 2840669) B2840669
theorem B1893833 : Blo 838352 1893833 := bstep (se 2 (by rfl) ⟨710187, by rfl⟩ : syracuseStep 1893833 = 1420375) B1420375
theorem B4777501 : Blo 838352 4777501 := bstep (se 3 (by rfl) ⟨895781, by rfl⟩ : syracuseStep 4777501 = 1791563) B1791563
theorem B9070309 : Blo 838352 9070309 := bstep (se 4 (by rfl) ⟨850341, by rfl⟩ : syracuseStep 9070309 = 1700683) B1700683
theorem B943879 : Blo 838352 943879 := bstep (se 1 (by rfl) ⟨707909, by rfl⟩ : syracuseStep 943879 = 1415819) B1415819
theorem B944059 : Blo 838352 944059 := bstep (se 1 (by rfl) ⟨708044, by rfl⟩ : syracuseStep 944059 = 1416089) B1416089
theorem B4778027 : Blo 838352 4778027 := bstep (se 1 (by rfl) ⟨3583520, by rfl⟩ : syracuseStep 4778027 = 7167041) B7167041
theorem B2123891 : Blo 838352 2123891 := bstep (se 1 (by rfl) ⟨1592918, by rfl⟩ : syracuseStep 2123891 = 3185837) B3185837
theorem B1894535 : Blo 838352 1894535 := bstep (se 1 (by rfl) ⟨1420901, by rfl⟩ : syracuseStep 1894535 = 2841803) B2841803
theorem B1894715 : Blo 838352 1894715 := bstep (se 1 (by rfl) ⟨1421036, by rfl⟩ : syracuseStep 1894715 = 2842073) B2842073
theorem B4548953 : Blo 838352 4548953 := bstep (se 2 (by rfl) ⟨1705857, by rfl⟩ : syracuseStep 4548953 = 3411715) B3411715
theorem B944527 : Blo 838352 944527 := bstep (se 1 (by rfl) ⟨708395, by rfl⟩ : syracuseStep 944527 = 1416791) B1416791
theorem B1894841 : Blo 838352 1894841 := bstep (se 2 (by rfl) ⟨710565, by rfl⟩ : syracuseStep 1894841 = 1421131) B1421131
theorem B2124407 : Blo 838352 2124407 := bstep (se 1 (by rfl) ⟨1593305, by rfl⟩ : syracuseStep 2124407 = 3186611) B3186611
theorem B1895183 : Blo 838352 1895183 := bstep (se 1 (by rfl) ⟨1421387, by rfl⟩ : syracuseStep 1895183 = 2842775) B2842775
theorem B1895201 : Blo 838352 1895201 := bstep (se 2 (by rfl) ⟨710700, by rfl⟩ : syracuseStep 1895201 = 1421401) B1421401
theorem B945031 : Blo 838352 945031 := bstep (se 1 (by rfl) ⟨708773, by rfl⟩ : syracuseStep 945031 = 1417547) B1417547
theorem B4844441 : Blo 838352 4844441 := bstep (se 2 (by rfl) ⟨1816665, by rfl⟩ : syracuseStep 4844441 = 3633331) B3633331
theorem B945211 : Blo 838352 945211 := bstep (se 1 (by rfl) ⟨708908, by rfl⟩ : syracuseStep 945211 = 1417817) B1417817
theorem B5762249 : Blo 838352 5762249 := bstep (se 2 (by rfl) ⟨2160843, by rfl⟩ : syracuseStep 5762249 = 4321687) B4321687
theorem B2551073 : Blo 838352 2551073 := bstep (se 2 (by rfl) ⟨956652, by rfl⟩ : syracuseStep 2551073 = 1913305) B1913305
theorem B2157911 : Blo 838352 2157911 := bstep (se 1 (by rfl) ⟨1618433, by rfl⟩ : syracuseStep 2157911 = 3236867) B3236867
theorem B4255091 : Blo 838352 4255091 := bstep (se 1 (by rfl) ⟨3191318, by rfl⟩ : syracuseStep 4255091 = 6382637) B6382637
theorem B4779485 : Blo 838352 4779485 := bstep (se 3 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 4779485 = 1792307) B1792307
theorem B945679 : Blo 838352 945679 := bstep (se 1 (by rfl) ⟨709259, by rfl⟩ : syracuseStep 945679 = 1418519) B1418519
theorem B2125399 : Blo 838352 2125399 := bstep (se 1 (by rfl) ⟨1594049, by rfl⟩ : syracuseStep 2125399 = 3188099) B3188099
theorem B1797817 : Blo 838352 1797817 := bstep (se 2 (by rfl) ⟨674181, by rfl⟩ : syracuseStep 1797817 = 1348363) B1348363
theorem B2387657 : Blo 838352 2387657 := bstep (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) B1790743
theorem B4255577 : Blo 838352 4255577 := bstep (se 2 (by rfl) ⟨1595841, by rfl⟩ : syracuseStep 4255577 = 3191683) B3191683
theorem B2125703 : Blo 838352 2125703 := bstep (se 1 (by rfl) ⟨1594277, by rfl⟩ : syracuseStep 2125703 = 3188555) B3188555
theorem B946183 : Blo 838352 946183 := bstep (se 1 (by rfl) ⟨709637, by rfl⟩ : syracuseStep 946183 = 1419275) B1419275
theorem B2125835 : Blo 838352 2125835 := bstep (se 1 (by rfl) ⟨1594376, by rfl⟩ : syracuseStep 2125835 = 3188753) B3188753
theorem B1798159 : Blo 838352 1798159 := bstep (se 1 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 1798159 = 2697239) B2697239
theorem B946363 : Blo 838352 946363 := bstep (se 1 (by rfl) ⟨709772, by rfl⟩ : syracuseStep 946363 = 1419545) B1419545
theorem B2126351 : Blo 838352 2126351 := bstep (se 1 (by rfl) ⟨1594763, by rfl⟩ : syracuseStep 2126351 = 3189527) B3189527
theorem B2388523 : Blo 838352 2388523 := bstep (se 1 (by rfl) ⟨1791392, by rfl⟩ : syracuseStep 2388523 = 3582785) B3582785
theorem B946831 : Blo 838352 946831 := bstep (se 1 (by rfl) ⟨710123, by rfl⟩ : syracuseStep 946831 = 1420247) B1420247
theorem B2126483 : Blo 838352 2126483 := bstep (se 1 (by rfl) ⟨1594862, by rfl⟩ : syracuseStep 2126483 = 3189725) B3189725
theorem B2388797 : Blo 838352 2388797 := bstep (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) B895799
theorem B1799047 : Blo 838352 1799047 := bstep (se 1 (by rfl) ⟨1349285, by rfl⟩ : syracuseStep 1799047 = 2698571) B2698571
theorem B947335 : Blo 838352 947335 := bstep (se 1 (by rfl) ⟨710501, by rfl⟩ : syracuseStep 947335 = 1421003) B1421003
theorem B2389139 : Blo 838352 2389139 := bstep (se 1 (by rfl) ⟨1791854, by rfl⟩ : syracuseStep 2389139 = 3583709) B3583709
theorem B1438921 : Blo 838352 1438921 := bstep (se 2 (by rfl) ⟨539595, by rfl⟩ : syracuseStep 1438921 = 1079191) B1079191
theorem B947515 : Blo 838352 947515 := bstep (se 1 (by rfl) ⟨710636, by rfl⟩ : syracuseStep 947515 = 1421273) B1421273
theorem B40924601 : Blo 838352 40924601 := bstep (se 2 (by rfl) ⟨15346725, by rfl⟩ : syracuseStep 40924601 = 30693451) B30693451
theorem B4552195 : Blo 838352 4552195 := bstep (se 1 (by rfl) ⟨3414146, by rfl⟩ : syracuseStep 4552195 = 6828293) B6828293
theorem B1701577 : Blo 838352 1701577 := bstep (se 2 (by rfl) ⟨638091, by rfl⟩ : syracuseStep 1701577 = 1276183) B1276183
theorem B3405569 : Blo 838352 3405569 := bstep (se 2 (by rfl) ⟨1277088, by rfl⟩ : syracuseStep 3405569 = 2554177) B2554177
theorem B2127617 : Blo 838352 2127617 := bstep (se 2 (by rfl) ⟨797856, by rfl⟩ : syracuseStep 2127617 = 1595713) B1595713
theorem B4781875 : Blo 838352 4781875 := bstep (se 1 (by rfl) ⟨3586406, by rfl⟩ : syracuseStep 4781875 = 7172813) B7172813
theorem B4257683 : Blo 838352 4257683 := bstep (se 1 (by rfl) ⟨3193262, by rfl⟩ : syracuseStep 4257683 = 6386525) B6386525
theorem B2127991 : Blo 838352 2127991 := bstep (se 1 (by rfl) ⟨1595993, by rfl⟩ : syracuseStep 2127991 = 3191987) B3191987
theorem B6912515 : Blo 838352 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B2128427 : Blo 838352 2128427 := bstep (se 1 (by rfl) ⟨1596320, by rfl⟩ : syracuseStep 2128427 = 3192641) B3192641
theorem B10222199 : Blo 838352 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B27294479 : Blo 838352 27294479 := bstep (se 1 (by rfl) ⟨20470859, by rfl⟩ : syracuseStep 27294479 = 40941719) B40941719
theorem B2554895 : Blo 838352 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B2686013 : Blo 838352 2686013 := bstep (se 3 (by rfl) ⟨503627, by rfl⟩ : syracuseStep 2686013 = 1007255) B1007255
theorem B6454333 : Blo 838352 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B1080463 : Blo 838352 1080463 := bstep (se 1 (by rfl) ⟨810347, by rfl⟩ : syracuseStep 1080463 = 1620695) B1620695
theorem B4783333 : Blo 838352 4783333 := bstep (se 4 (by rfl) ⟨448437, by rfl⟩ : syracuseStep 4783333 = 896875) B896875
theorem B1277191 : Blo 838352 1277191 := bstep (se 1 (by rfl) ⟨957893, by rfl⟩ : syracuseStep 1277191 = 1915787) B1915787
theorem B2620759 : Blo 838352 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B2391383 : Blo 838352 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B2129267 : Blo 838352 2129267 := bstep (se 1 (by rfl) ⟨1596950, by rfl⟩ : syracuseStep 2129267 = 3193901) B3193901
theorem B2129287 : Blo 838352 2129287 := bstep (se 1 (by rfl) ⟨1596965, by rfl⟩ : syracuseStep 2129287 = 3193931) B3193931
theorem B1703369 : Blo 838352 1703369 := bstep (se 2 (by rfl) ⟨638763, by rfl⟩ : syracuseStep 1703369 = 1277527) B1277527
theorem B4030019 : Blo 838352 4030019 := bstep (se 1 (by rfl) ⟨3022514, by rfl⟩ : syracuseStep 4030019 = 6045029) B6045029
theorem B2555479 : Blo 838352 2555479 := bstep (se 1 (by rfl) ⟨1916609, by rfl⟩ : syracuseStep 2555479 = 3833219) B3833219
theorem B2129561 : Blo 838352 2129561 := bstep (se 2 (by rfl) ⟨798585, by rfl⟩ : syracuseStep 2129561 = 1597171) B1597171
theorem B6389441 : Blo 838352 6389441 := bstep (se 2 (by rfl) ⟨2396040, by rfl⟩ : syracuseStep 6389441 = 4792081) B4792081
theorem B2129723 : Blo 838352 2129723 := bstep (se 1 (by rfl) ⟨1597292, by rfl⟩ : syracuseStep 2129723 = 3194585) B3194585
theorem B5111687 : Blo 838352 5111687 := bstep (se 1 (by rfl) ⟨3833765, by rfl⟩ : syracuseStep 5111687 = 7667531) B7667531
theorem B1278031 : Blo 838352 1278031 := bstep (se 1 (by rfl) ⟨958523, by rfl⟩ : syracuseStep 1278031 = 1917047) B1917047
theorem B1343737 : Blo 838352 1343737 := bstep (se 2 (by rfl) ⟨503901, by rfl⟩ : syracuseStep 1343737 = 1007803) B1007803
theorem B13631813 : Blo 838352 13631813 := bstep (se 4 (by rfl) ⟨1277982, by rfl⟩ : syracuseStep 13631813 = 2555965) B2555965
theorem B2392715 : Blo 838352 2392715 := bstep (se 1 (by rfl) ⟨1794536, by rfl⟩ : syracuseStep 2392715 = 3589073) B3589073
theorem B3113795 : Blo 838352 3113795 := bstep (se 1 (by rfl) ⟨2335346, by rfl⟩ : syracuseStep 3113795 = 4670693) B4670693
theorem B2589775 : Blo 838352 2589775 := bstep (se 1 (by rfl) ⟨1942331, by rfl⟩ : syracuseStep 2589775 = 3884663) B3884663
theorem B6456665 : Blo 838352 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B2131343 : Blo 838352 2131343 := bstep (se 1 (by rfl) ⟨1598507, by rfl⟩ : syracuseStep 2131343 = 3197015) B3197015
theorem B5604851 : Blo 838352 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B2131667 : Blo 838352 2131667 := bstep (se 1 (by rfl) ⟨1598750, by rfl⟩ : syracuseStep 2131667 = 3197501) B3197501
theorem B4097785 : Blo 838352 4097785 := bstep (se 2 (by rfl) ⟨1536669, by rfl⟩ : syracuseStep 4097785 = 3073339) B3073339
theorem B5736251 : Blo 838352 5736251 := bstep (se 1 (by rfl) ⟨4302188, by rfl⟩ : syracuseStep 5736251 = 8604377) B8604377
theorem B12912473 : Blo 838352 12912473 := bstep (se 2 (by rfl) ⟨4842177, by rfl⟩ : syracuseStep 12912473 = 9684355) B9684355
theorem B9570311 : Blo 838352 9570311 := bstep (se 1 (by rfl) ⟨7177733, by rfl⟩ : syracuseStep 9570311 = 14355467) B14355467
theorem B4261895 : Blo 838352 4261895 := bstep (se 1 (by rfl) ⟨3196421, by rfl⟩ : syracuseStep 4261895 = 6392843) B6392843
theorem B2689139 : Blo 838352 2689139 := bstep (se 1 (by rfl) ⟨2016854, by rfl⟩ : syracuseStep 2689139 = 4033709) B4033709
theorem B12093745 : Blo 838352 12093745 := bstep (se 2 (by rfl) ⟨4535154, by rfl⟩ : syracuseStep 12093745 = 9070309) B9070309
theorem B6064517 : Blo 838352 6064517 := bstep (se 4 (by rfl) ⟨568548, by rfl⟩ : syracuseStep 6064517 = 1137097) B1137097
theorem B4262381 : Blo 838352 4262381 := bstep (se 3 (by rfl) ⟨799196, by rfl⟩ : syracuseStep 4262381 = 1598393) B1598393
theorem B10783367 : Blo 838352 10783367 := bstep (se 1 (by rfl) ⟨8087525, by rfl⟩ : syracuseStep 10783367 = 16175051) B16175051
theorem B27692119 : Blo 838352 27692119 := bstep (se 1 (by rfl) ⟨20769089, by rfl⟩ : syracuseStep 27692119 = 41538179) B41538179
theorem B4263191 : Blo 838352 4263191 := bstep (se 1 (by rfl) ⟨3197393, by rfl⟩ : syracuseStep 4263191 = 6394787) B6394787
theorem B921127 : Blo 838352 921127 := bstep (se 1 (by rfl) ⟨690845, by rfl⟩ : syracuseStep 921127 = 1381691) B1381691
theorem B1347511 : Blo 838352 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B2396087 : Blo 838352 2396087 := bstep (se 1 (by rfl) ⟨1797065, by rfl⟩ : syracuseStep 2396087 = 3594131) B3594131
theorem B6066191 : Blo 838352 6066191 := bstep (se 1 (by rfl) ⟨4549643, by rfl⟩ : syracuseStep 6066191 = 9099287) B9099287
theorem B3183239 : Blo 838352 3183239 := bstep (se 1 (by rfl) ⟨2387429, by rfl⟩ : syracuseStep 3183239 = 4774859) B4774859
theorem B9081517 : Blo 838352 9081517 := bstep (se 3 (by rfl) ⟨1702784, by rfl⟩ : syracuseStep 9081517 = 3405569) B3405569
theorem B2396861 : Blo 838352 2396861 := bstep (se 3 (by rfl) ⟨449411, by rfl⟩ : syracuseStep 2396861 = 898823) B898823
theorem B9573137 : Blo 838352 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B2691947 : Blo 838352 2691947 := bstep (se 1 (by rfl) ⟨2018960, by rfl⟩ : syracuseStep 2691947 = 4037921) B4037921
theorem B9573227 : Blo 838352 9573227 := bstep (se 1 (by rfl) ⟨7179920, by rfl⟩ : syracuseStep 9573227 = 14359841) B14359841
theorem B2397089 : Blo 838352 2397089 := bstep (se 2 (by rfl) ⟨898908, by rfl⟩ : syracuseStep 2397089 = 1797817) B1797817
theorem B3183695 : Blo 838352 3183695 := bstep (se 1 (by rfl) ⟨2387771, by rfl⟩ : syracuseStep 3183695 = 4775543) B4775543
theorem B12129497 : Blo 838352 12129497 := bstep (se 2 (by rfl) ⟨4548561, by rfl⟩ : syracuseStep 12129497 = 9097123) B9097123
theorem B2397431 : Blo 838352 2397431 := bstep (se 1 (by rfl) ⟨1798073, by rfl⟩ : syracuseStep 2397431 = 3596147) B3596147
theorem B13604111 : Blo 838352 13604111 := bstep (se 1 (by rfl) ⟨10203083, by rfl⟩ : syracuseStep 13604111 = 20406167) B20406167
theorem B2725207 : Blo 838352 2725207 := bstep (se 1 (by rfl) ⟨2043905, by rfl⟩ : syracuseStep 2725207 = 4087811) B4087811
theorem B2397545 : Blo 838352 2397545 := bstep (se 2 (by rfl) ⟨899079, by rfl⟩ : syracuseStep 2397545 = 1798159) B1798159
theorem B33166945 : Blo 838352 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B4855619 : Blo 838352 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B1415225 : Blo 838352 1415225 := bstep (se 2 (by rfl) ⟨530709, by rfl⟩ : syracuseStep 1415225 = 1061419) B1061419
theorem B3184697 : Blo 838352 3184697 := bstep (se 2 (by rfl) ⟨1194261, by rfl⟩ : syracuseStep 3184697 = 2388523) B2388523
theorem B2398729 : Blo 838352 2398729 := bstep (se 2 (by rfl) ⟨899523, by rfl⟩ : syracuseStep 2398729 = 1799047) B1799047
theorem B5118497 : Blo 838352 5118497 := bstep (se 2 (by rfl) ⟨1919436, by rfl⟩ : syracuseStep 5118497 = 3838873) B3838873
theorem B3185351 : Blo 838352 3185351 := bstep (se 1 (by rfl) ⟨2389013, by rfl⟩ : syracuseStep 3185351 = 4778027) B4778027
theorem B1415927 : Blo 838352 1415927 := bstep (se 1 (by rfl) ⟨1061945, by rfl⟩ : syracuseStep 1415927 = 2123891) B2123891
theorem B1416271 : Blo 838352 1416271 := bstep (se 1 (by rfl) ⟨1062203, by rfl⟩ : syracuseStep 1416271 = 2124407) B2124407
theorem B1416521 : Blo 838352 1416521 := bstep (se 2 (by rfl) ⟨531195, by rfl⟩ : syracuseStep 1416521 = 1062391) B1062391
theorem B6069593 : Blo 838352 6069593 := bstep (se 2 (by rfl) ⟨2276097, by rfl⟩ : syracuseStep 6069593 = 4552195) B4552195
theorem B3841499 : Blo 838352 3841499 := bstep (se 1 (by rfl) ⟨2881124, by rfl⟩ : syracuseStep 3841499 = 5762249) B5762249
theorem B2268769 : Blo 838352 2268769 := bstep (se 2 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 2268769 = 1701577) B1701577
theorem B2694779 : Blo 838352 2694779 := bstep (se 1 (by rfl) ⟨2021084, by rfl⟩ : syracuseStep 2694779 = 4042169) B4042169
theorem B3186323 : Blo 838352 3186323 := bstep (se 1 (by rfl) ⟨2389742, by rfl⟩ : syracuseStep 3186323 = 4779485) B4779485
theorem B1515179 : Blo 838352 1515179 := bstep (se 1 (by rfl) ⟨1136384, by rfl⟩ : syracuseStep 1515179 = 2272769) B2272769
theorem B1416953 : Blo 838352 1416953 := bstep (se 2 (by rfl) ⟨531357, by rfl⟩ : syracuseStep 1416953 = 1062715) B1062715
theorem B3022687 : Blo 838352 3022687 := bstep (se 1 (by rfl) ⟨2267015, by rfl⟩ : syracuseStep 3022687 = 4534031) B4534031
theorem B1417135 : Blo 838352 1417135 := bstep (se 1 (by rfl) ⟨1062851, by rfl⟩ : syracuseStep 1417135 = 2125703) B2125703
theorem B1417223 : Blo 838352 1417223 := bstep (se 1 (by rfl) ⟨1062917, by rfl⟩ : syracuseStep 1417223 = 2125835) B2125835
theorem B1417567 : Blo 838352 1417567 := bstep (se 1 (by rfl) ⟨1063175, by rfl⟩ : syracuseStep 1417567 = 2126351) B2126351
theorem B1417655 : Blo 838352 1417655 := bstep (se 1 (by rfl) ⟨1063241, by rfl⟩ : syracuseStep 1417655 = 2126483) B2126483
theorem B3023725 : Blo 838352 3023725 := bstep (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) B1133897
theorem B2696111 : Blo 838352 2696111 := bstep (se 1 (by rfl) ⟨2022083, by rfl⟩ : syracuseStep 2696111 = 4044167) B4044167
theorem B1418249 : Blo 838352 1418249 := bstep (se 2 (by rfl) ⟨531843, by rfl⟩ : syracuseStep 1418249 = 1063687) B1063687
theorem B1418411 : Blo 838352 1418411 := bstep (se 1 (by rfl) ⟨1063808, by rfl⟩ : syracuseStep 1418411 = 2127617) B2127617
theorem B4793539 : Blo 838352 4793539 := bstep (se 1 (by rfl) ⟨3595154, by rfl⟩ : syracuseStep 4793539 = 7190309) B7190309
theorem B1516873 : Blo 838352 1516873 := bstep (se 2 (by rfl) ⟨568827, by rfl⟩ : syracuseStep 1516873 = 1137655) B1137655
theorem B1418809 : Blo 838352 1418809 := bstep (se 2 (by rfl) ⟨532053, by rfl⟩ : syracuseStep 1418809 = 1064107) B1064107
theorem B4040381 : Blo 838352 4040381 := bstep (se 3 (by rfl) ⟨757571, by rfl⟩ : syracuseStep 4040381 = 1515143) B1515143
theorem B1418951 : Blo 838352 1418951 := bstep (se 1 (by rfl) ⟨1064213, by rfl⟩ : syracuseStep 1418951 = 2128427) B2128427
theorem B18196319 : Blo 838352 18196319 := bstep (se 1 (by rfl) ⟨13647239, by rfl⟩ : syracuseStep 18196319 = 27294479) B27294479
theorem B1419113 : Blo 838352 1419113 := bstep (se 2 (by rfl) ⟨532167, by rfl⟩ : syracuseStep 1419113 = 1064335) B1064335
theorem B6367085 : Blo 838352 6367085 := bstep (se 3 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 6367085 = 2387657) B2387657
theorem B1419511 : Blo 838352 1419511 := bstep (se 1 (by rfl) ⟨1064633, by rfl⟩ : syracuseStep 1419511 = 2129267) B2129267
theorem B8202583 : Blo 838352 8202583 := bstep (se 1 (by rfl) ⟨6151937, by rfl⟩ : syracuseStep 8202583 = 12303875) B12303875
theorem B1419707 : Blo 838352 1419707 := bstep (se 1 (by rfl) ⟨1064780, by rfl⟩ : syracuseStep 1419707 = 2129561) B2129561
theorem B3025441 : Blo 838352 3025441 := bstep (se 2 (by rfl) ⟨1134540, by rfl⟩ : syracuseStep 3025441 = 2269081) B2269081
theorem B1419815 : Blo 838352 1419815 := bstep (se 1 (by rfl) ⟨1064861, by rfl⟩ : syracuseStep 1419815 = 2129723) B2129723
theorem B5384839 : Blo 838352 5384839 := bstep (se 1 (by rfl) ⟨4038629, by rfl⟩ : syracuseStep 5384839 = 8077259) B8077259
theorem B1420105 : Blo 838352 1420105 := bstep (se 2 (by rfl) ⟨532539, by rfl⟩ : syracuseStep 1420105 = 1065079) B1065079
theorem B1420139 : Blo 838352 1420139 := bstep (se 1 (by rfl) ⟨1065104, by rfl⟩ : syracuseStep 1420139 = 2130209) B2130209
theorem B1420537 : Blo 838352 1420537 := bstep (se 2 (by rfl) ⟨532701, by rfl⟩ : syracuseStep 1420537 = 1065403) B1065403
theorem B896431 : Blo 838352 896431 := bstep (se 1 (by rfl) ⟨672323, by rfl⟩ : syracuseStep 896431 = 1344647) B1344647
theorem B1420807 : Blo 838352 1420807 := bstep (se 1 (by rfl) ⟨1065605, by rfl⟩ : syracuseStep 1420807 = 2131211) B2131211
theorem B3190711 : Blo 838352 3190711 := bstep (se 1 (by rfl) ⟨2393033, by rfl⟩ : syracuseStep 3190711 = 4786067) B4786067
theorem B1421239 : Blo 838352 1421239 := bstep (se 1 (by rfl) ⟨1065929, by rfl⟩ : syracuseStep 1421239 = 2131859) B2131859
theorem B5386171 : Blo 838352 5386171 := bstep (se 1 (by rfl) ⟨4039628, by rfl⟩ : syracuseStep 5386171 = 8079257) B8079257
theorem B2830355 : Blo 838352 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B1257551 : Blo 838352 1257551 := bstep (se 1 (by rfl) ⟨943163, by rfl⟩ : syracuseStep 1257551 = 1886327) B1886327
theorem B1421435 : Blo 838352 1421435 := bstep (se 1 (by rfl) ⟨1066076, by rfl⟩ : syracuseStep 1421435 = 2132153) B2132153
theorem B1257671 : Blo 838352 1257671 := bstep (se 1 (by rfl) ⟨943253, by rfl⟩ : syracuseStep 1257671 = 1886507) B1886507
theorem B2830679 : Blo 838352 2830679 := bstep (se 1 (by rfl) ⟨2123009, by rfl⟩ : syracuseStep 2830679 = 4246019) B4246019
theorem B3027287 : Blo 838352 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B1257833 : Blo 838352 1257833 := bstep (se 2 (by rfl) ⟨471687, by rfl⟩ : syracuseStep 1257833 = 943375) B943375
theorem B3191183 : Blo 838352 3191183 := bstep (se 1 (by rfl) ⟨2393387, by rfl⟩ : syracuseStep 3191183 = 4786775) B4786775
theorem B1257911 : Blo 838352 1257911 := bstep (se 1 (by rfl) ⟨943433, by rfl⟩ : syracuseStep 1257911 = 1886867) B1886867
theorem B1257947 : Blo 838352 1257947 := bstep (se 1 (by rfl) ⟨943460, by rfl⟩ : syracuseStep 1257947 = 1886921) B1886921
theorem B6370001 : Blo 838352 6370001 := bstep (se 2 (by rfl) ⟨2388750, by rfl⟩ : syracuseStep 6370001 = 4777501) B4777501
theorem B1258415 : Blo 838352 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B4797413 : Blo 838352 4797413 := bstep (se 4 (by rfl) ⟨449757, by rfl⟩ : syracuseStep 4797413 = 899515) B899515
theorem B1258505 : Blo 838352 1258505 := bstep (se 2 (by rfl) ⟨471939, by rfl⟩ : syracuseStep 1258505 = 943879) B943879
theorem B1258535 : Blo 838352 1258535 := bstep (se 1 (by rfl) ⟨943901, by rfl⟩ : syracuseStep 1258535 = 1887803) B1887803
theorem B1062011 : Blo 838352 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B1258619 : Blo 838352 1258619 := bstep (se 1 (by rfl) ⟨943964, by rfl⟩ : syracuseStep 1258619 = 1887929) B1887929
theorem B38810765 : Blo 838352 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B12301483 : Blo 838352 12301483 := bstep (se 1 (by rfl) ⟨9226112, by rfl⟩ : syracuseStep 12301483 = 18452225) B18452225
theorem B1258745 : Blo 838352 1258745 := bstep (se 2 (by rfl) ⟨472029, by rfl⟩ : syracuseStep 1258745 = 944059) B944059
theorem B1258847 : Blo 838352 1258847 := bstep (se 1 (by rfl) ⟨944135, by rfl⟩ : syracuseStep 1258847 = 1888271) B1888271
theorem B3192169 : Blo 838352 3192169 := bstep (se 2 (by rfl) ⟨1197063, by rfl⟩ : syracuseStep 3192169 = 2394127) B2394127
theorem B1258859 : Blo 838352 1258859 := bstep (se 1 (by rfl) ⟨944144, by rfl⟩ : syracuseStep 1258859 = 1888289) B1888289
theorem B2831759 : Blo 838352 2831759 := bstep (se 1 (by rfl) ⟨2123819, by rfl⟩ : syracuseStep 2831759 = 4247639) B4247639
theorem B1259087 : Blo 838352 1259087 := bstep (se 1 (by rfl) ⟨944315, by rfl⟩ : syracuseStep 1259087 = 1888631) B1888631
theorem B3192443 : Blo 838352 3192443 := bstep (se 1 (by rfl) ⟨2394332, by rfl⟩ : syracuseStep 3192443 = 4788665) B4788665
theorem B1259207 : Blo 838352 1259207 := bstep (se 1 (by rfl) ⟨944405, by rfl⟩ : syracuseStep 1259207 = 1888811) B1888811
theorem B2832083 : Blo 838352 2832083 := bstep (se 1 (by rfl) ⟨2124062, by rfl⟩ : syracuseStep 2832083 = 4248125) B4248125
theorem B4536107 : Blo 838352 4536107 := bstep (se 1 (by rfl) ⟨3402080, by rfl⟩ : syracuseStep 4536107 = 6804161) B6804161
theorem B1259369 : Blo 838352 1259369 := bstep (se 2 (by rfl) ⟨472263, by rfl⟩ : syracuseStep 1259369 = 944527) B944527
theorem B1914731 : Blo 838352 1914731 := bstep (se 1 (by rfl) ⟨1436048, by rfl⟩ : syracuseStep 1914731 = 2872097) B2872097
theorem B6043501 : Blo 838352 6043501 := bstep (se 3 (by rfl) ⟨1133156, by rfl⟩ : syracuseStep 6043501 = 2266313) B2266313
theorem B1259447 : Blo 838352 1259447 := bstep (se 1 (by rfl) ⟨944585, by rfl⟩ : syracuseStep 1259447 = 1889171) B1889171
theorem B1259483 : Blo 838352 1259483 := bstep (se 1 (by rfl) ⟨944612, by rfl⟩ : syracuseStep 1259483 = 1889225) B1889225
theorem B27277357 : Blo 838352 27277357 := bstep (se 3 (by rfl) ⟨5114504, by rfl⟩ : syracuseStep 27277357 = 10229009) B10229009
theorem B5388403 : Blo 838352 5388403 := bstep (se 1 (by rfl) ⟨4041302, by rfl⟩ : syracuseStep 5388403 = 8082605) B8082605
theorem B6830243 : Blo 838352 6830243 := bstep (se 1 (by rfl) ⟨5122682, by rfl⟩ : syracuseStep 6830243 = 10245365) B10245365
theorem B1259951 : Blo 838352 1259951 := bstep (se 1 (by rfl) ⟨944963, by rfl⟩ : syracuseStep 1259951 = 1889927) B1889927
theorem B3029491 : Blo 838352 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B1260041 : Blo 838352 1260041 := bstep (se 2 (by rfl) ⟨472515, by rfl⟩ : syracuseStep 1260041 = 945031) B945031
theorem B1194535 : Blo 838352 1194535 := bstep (se 1 (by rfl) ⟨895901, by rfl⟩ : syracuseStep 1194535 = 1791803) B1791803
theorem B1260071 : Blo 838352 1260071 := bstep (se 1 (by rfl) ⟨945053, by rfl⟩ : syracuseStep 1260071 = 1890107) B1890107
theorem B1260155 : Blo 838352 1260155 := bstep (se 1 (by rfl) ⟨945116, by rfl⟩ : syracuseStep 1260155 = 1890233) B1890233
theorem B1260281 : Blo 838352 1260281 := bstep (se 2 (by rfl) ⟨472605, by rfl⟩ : syracuseStep 1260281 = 945211) B945211
theorem B1260383 : Blo 838352 1260383 := bstep (se 1 (by rfl) ⟨945287, by rfl⟩ : syracuseStep 1260383 = 1890575) B1890575
theorem B1260395 : Blo 838352 1260395 := bstep (se 1 (by rfl) ⟨945296, by rfl⟩ : syracuseStep 1260395 = 1890593) B1890593
theorem B2833271 : Blo 838352 2833271 := bstep (se 1 (by rfl) ⟨2124953, by rfl⟩ : syracuseStep 2833271 = 4249907) B4249907
theorem B6372431 : Blo 838352 6372431 := bstep (se 1 (by rfl) ⟨4779323, by rfl⟩ : syracuseStep 6372431 = 9558647) B9558647
theorem B2833487 : Blo 838352 2833487 := bstep (se 1 (by rfl) ⟨2125115, by rfl⟩ : syracuseStep 2833487 = 4250231) B4250231
theorem B1260623 : Blo 838352 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B1260743 : Blo 838352 1260743 := bstep (se 1 (by rfl) ⟨945557, by rfl⟩ : syracuseStep 1260743 = 1891115) B1891115
theorem B4046071 : Blo 838352 4046071 := bstep (se 1 (by rfl) ⟨3034553, by rfl⟩ : syracuseStep 4046071 = 6069107) B6069107
theorem B1260905 : Blo 838352 1260905 := bstep (se 2 (by rfl) ⟨472839, by rfl⟩ : syracuseStep 1260905 = 945679) B945679
theorem B2014607 : Blo 838352 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B1260983 : Blo 838352 1260983 := bstep (se 1 (by rfl) ⟨945737, by rfl⟩ : syracuseStep 1260983 = 1891475) B1891475
theorem B2833865 : Blo 838352 2833865 := bstep (se 2 (by rfl) ⟨1062699, by rfl⟩ : syracuseStep 2833865 = 2125399) B2125399
theorem B1261019 : Blo 838352 1261019 := bstep (se 1 (by rfl) ⟨945764, by rfl⟩ : syracuseStep 1261019 = 1891529) B1891529
theorem B2834135 : Blo 838352 2834135 := bstep (se 1 (by rfl) ⟨2125601, by rfl⟩ : syracuseStep 2834135 = 4251203) B4251203
theorem B2834351 : Blo 838352 2834351 := bstep (se 1 (by rfl) ⟨2125763, by rfl⟩ : syracuseStep 2834351 = 4251527) B4251527
theorem B1261487 : Blo 838352 1261487 := bstep (se 1 (by rfl) ⟨946115, by rfl⟩ : syracuseStep 1261487 = 1892231) B1892231
theorem B1261577 : Blo 838352 1261577 := bstep (se 2 (by rfl) ⟨473091, by rfl⟩ : syracuseStep 1261577 = 946183) B946183
theorem B1261607 : Blo 838352 1261607 := bstep (se 1 (by rfl) ⟨946205, by rfl⟩ : syracuseStep 1261607 = 1892411) B1892411
theorem B10371149 : Blo 838352 10371149 := bstep (se 3 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 10371149 = 3889181) B3889181
theorem B1261691 : Blo 838352 1261691 := bstep (se 1 (by rfl) ⟨946268, by rfl⟩ : syracuseStep 1261691 = 1892537) B1892537
theorem B1261817 : Blo 838352 1261817 := bstep (se 2 (by rfl) ⟨473181, by rfl⟩ : syracuseStep 1261817 = 946363) B946363
theorem B1261919 : Blo 838352 1261919 := bstep (se 1 (by rfl) ⟨946439, by rfl⟩ : syracuseStep 1261919 = 1892879) B1892879
theorem B3588457 : Blo 838352 3588457 := bstep (se 2 (by rfl) ⟨1345671, by rfl⟩ : syracuseStep 3588457 = 2691343) B2691343
theorem B1261931 : Blo 838352 1261931 := bstep (se 1 (by rfl) ⟨946448, by rfl⟩ : syracuseStep 1261931 = 1892897) B1892897
theorem B1262159 : Blo 838352 1262159 := bstep (se 1 (by rfl) ⟨946619, by rfl⟩ : syracuseStep 1262159 = 1893239) B1893239
theorem B13615715 : Blo 838352 13615715 := bstep (se 1 (by rfl) ⟨10211786, by rfl⟩ : syracuseStep 13615715 = 20423573) B20423573
theorem B1262279 : Blo 838352 1262279 := bstep (se 1 (by rfl) ⟨946709, by rfl⟩ : syracuseStep 1262279 = 1893419) B1893419
theorem B1262441 : Blo 838352 1262441 := bstep (se 2 (by rfl) ⟨473415, by rfl⟩ : syracuseStep 1262441 = 946831) B946831
theorem B34456427 : Blo 838352 34456427 := bstep (se 1 (by rfl) ⟨25842320, by rfl⟩ : syracuseStep 34456427 = 51684641) B51684641
theorem B4244399 : Blo 838352 4244399 := bstep (se 1 (by rfl) ⟨3183299, by rfl⟩ : syracuseStep 4244399 = 6366599) B6366599
theorem B9552815 : Blo 838352 9552815 := bstep (se 1 (by rfl) ⟨7164611, by rfl⟩ : syracuseStep 9552815 = 14329223) B14329223
theorem B1262519 : Blo 838352 1262519 := bstep (se 1 (by rfl) ⟨946889, by rfl⟩ : syracuseStep 1262519 = 1893779) B1893779
theorem B1262555 : Blo 838352 1262555 := bstep (se 1 (by rfl) ⟨946916, by rfl⟩ : syracuseStep 1262555 = 1893833) B1893833
theorem B3196057 : Blo 838352 3196057 := bstep (se 2 (by rfl) ⟨1198521, by rfl⟩ : syracuseStep 3196057 = 2397043) B2397043
theorem B1263023 : Blo 838352 1263023 := bstep (se 1 (by rfl) ⟨947267, by rfl⟩ : syracuseStep 1263023 = 1894535) B1894535
theorem B3196361 : Blo 838352 3196361 := bstep (se 2 (by rfl) ⟨1198635, by rfl⟩ : syracuseStep 3196361 = 2397271) B2397271
theorem B1263113 : Blo 838352 1263113 := bstep (se 2 (by rfl) ⟨473667, by rfl⟩ : syracuseStep 1263113 = 947335) B947335
theorem B4310567 : Blo 838352 4310567 := bstep (se 1 (by rfl) ⟨3232925, by rfl⟩ : syracuseStep 4310567 = 6465851) B6465851
theorem B1263143 : Blo 838352 1263143 := bstep (se 1 (by rfl) ⟨947357, by rfl⟩ : syracuseStep 1263143 = 1894715) B1894715
theorem B3032635 : Blo 838352 3032635 := bstep (se 1 (by rfl) ⟨2274476, by rfl⟩ : syracuseStep 3032635 = 4548953) B4548953
theorem B1918561 : Blo 838352 1918561 := bstep (se 2 (by rfl) ⟨719460, by rfl⟩ : syracuseStep 1918561 = 1438921) B1438921
theorem B1263227 : Blo 838352 1263227 := bstep (se 1 (by rfl) ⟨947420, by rfl⟩ : syracuseStep 1263227 = 1894841) B1894841
theorem B1263353 : Blo 838352 1263353 := bstep (se 2 (by rfl) ⟨473757, by rfl⟩ : syracuseStep 1263353 = 947515) B947515
theorem B1263455 : Blo 838352 1263455 := bstep (se 1 (by rfl) ⟨947591, by rfl⟩ : syracuseStep 1263455 = 1895183) B1895183
theorem B1263467 : Blo 838352 1263467 := bstep (se 1 (by rfl) ⟨947600, by rfl⟩ : syracuseStep 1263467 = 1895201) B1895201
theorem B3196847 : Blo 838352 3196847 := bstep (se 1 (by rfl) ⟨2397635, by rfl⟩ : syracuseStep 3196847 = 4795271) B4795271
theorem B3229627 : Blo 838352 3229627 := bstep (se 1 (by rfl) ⟨2422220, by rfl⟩ : syracuseStep 3229627 = 4844441) B4844441
theorem B2836727 : Blo 838352 2836727 := bstep (se 1 (by rfl) ⟨2127545, by rfl⟩ : syracuseStep 2836727 = 4255091) B4255091
theorem B6375833 : Blo 838352 6375833 := bstep (se 2 (by rfl) ⟨2390937, by rfl⟩ : syracuseStep 6375833 = 4781875) B4781875
theorem B10242541 : Blo 838352 10242541 := bstep (se 3 (by rfl) ⟨1920476, by rfl⟩ : syracuseStep 10242541 = 3840953) B3840953
theorem B1886759 : Blo 838352 1886759 := bstep (se 1 (by rfl) ⟨1415069, by rfl⟩ : syracuseStep 1886759 = 2830139) B2830139
theorem B2837051 : Blo 838352 2837051 := bstep (se 1 (by rfl) ⟨2127788, by rfl⟩ : syracuseStep 2837051 = 4255577) B4255577
theorem B838363 : Blo 838352 838363 := bstep (se 1 (by rfl) ⟨628772, by rfl⟩ : syracuseStep 838363 = 1257545) B1257545
theorem B838439 : Blo 838352 838439 := bstep (se 1 (by rfl) ⟨628829, by rfl⟩ : syracuseStep 838439 = 1257659) B1257659
theorem B2837321 : Blo 838352 2837321 := bstep (se 2 (by rfl) ⟨1063995, by rfl⟩ : syracuseStep 2837321 = 2127991) B2127991
theorem B838479 : Blo 838352 838479 := bstep (se 1 (by rfl) ⟨628859, by rfl⟩ : syracuseStep 838479 = 1257719) B1257719
theorem B838495 : Blo 838352 838495 := bstep (se 1 (by rfl) ⟨628871, by rfl⟩ : syracuseStep 838495 = 1257743) B1257743
theorem B1887083 : Blo 838352 1887083 := bstep (se 1 (by rfl) ⟨1415312, by rfl⟩ : syracuseStep 1887083 = 2830625) B2830625
theorem B838523 : Blo 838352 838523 := bstep (se 1 (by rfl) ⟨628892, by rfl⟩ : syracuseStep 838523 = 1257785) B1257785
theorem B1887137 : Blo 838352 1887137 := bstep (se 2 (by rfl) ⟨707676, by rfl⟩ : syracuseStep 1887137 = 1415353) B1415353
theorem B838575 : Blo 838352 838575 := bstep (se 1 (by rfl) ⟨628931, by rfl⟩ : syracuseStep 838575 = 1257863) B1257863
theorem B1362863 : Blo 838352 1362863 := bstep (se 1 (by rfl) ⟨1022147, by rfl⟩ : syracuseStep 1362863 = 2044295) B2044295
theorem B838599 : Blo 838352 838599 := bstep (se 1 (by rfl) ⟨628949, by rfl⟩ : syracuseStep 838599 = 1257899) B1257899
theorem B838619 : Blo 838352 838619 := bstep (se 1 (by rfl) ⟨628964, by rfl⟩ : syracuseStep 838619 = 1257929) B1257929
theorem B838695 : Blo 838352 838695 := bstep (se 1 (by rfl) ⟨629021, by rfl⟩ : syracuseStep 838695 = 1258043) B1258043
theorem B838735 : Blo 838352 838735 := bstep (se 1 (by rfl) ⟨629051, by rfl⟩ : syracuseStep 838735 = 1258103) B1258103
theorem B838751 : Blo 838352 838751 := bstep (se 1 (by rfl) ⟨629063, by rfl⟩ : syracuseStep 838751 = 1258127) B1258127
theorem B838779 : Blo 838352 838779 := bstep (se 1 (by rfl) ⟨629084, by rfl⟩ : syracuseStep 838779 = 1258169) B1258169
theorem B838831 : Blo 838352 838831 := bstep (se 1 (by rfl) ⟨629123, by rfl⟩ : syracuseStep 838831 = 1258247) B1258247
theorem B838855 : Blo 838352 838855 := bstep (se 1 (by rfl) ⟨629141, by rfl⟩ : syracuseStep 838855 = 1258283) B1258283
theorem B1592531 : Blo 838352 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B838875 : Blo 838352 838875 := bstep (se 1 (by rfl) ⟨629156, by rfl⟩ : syracuseStep 838875 = 1258313) B1258313
theorem B1887479 : Blo 838352 1887479 := bstep (se 1 (by rfl) ⟨1415609, by rfl⟩ : syracuseStep 1887479 = 2831219) B2831219
theorem B838951 : Blo 838352 838951 := bstep (se 1 (by rfl) ⟨629213, by rfl⟩ : syracuseStep 838951 = 1258427) B1258427
theorem B838991 : Blo 838352 838991 := bstep (se 1 (by rfl) ⟨629243, by rfl⟩ : syracuseStep 838991 = 1258487) B1258487
theorem B2870615 : Blo 838352 2870615 := bstep (se 1 (by rfl) ⟨2152961, by rfl⟩ : syracuseStep 2870615 = 4305923) B4305923
theorem B839007 : Blo 838352 839007 := bstep (se 1 (by rfl) ⟨629255, by rfl⟩ : syracuseStep 839007 = 1258511) B1258511
theorem B839035 : Blo 838352 839035 := bstep (se 1 (by rfl) ⟨629276, by rfl⟩ : syracuseStep 839035 = 1258553) B1258553
theorem B6802861 : Blo 838352 6802861 := bstep (se 3 (by rfl) ⟨1275536, by rfl⟩ : syracuseStep 6802861 = 2551073) B2551073
theorem B839087 : Blo 838352 839087 := bstep (se 1 (by rfl) ⟨629315, by rfl⟩ : syracuseStep 839087 = 1258631) B1258631
theorem B1592759 : Blo 838352 1592759 := bstep (se 1 (by rfl) ⟨1194569, by rfl⟩ : syracuseStep 1592759 = 2389139) B2389139
theorem B839111 : Blo 838352 839111 := bstep (se 1 (by rfl) ⟨629333, by rfl⟩ : syracuseStep 839111 = 1258667) B1258667
theorem B839131 : Blo 838352 839131 := bstep (se 1 (by rfl) ⟨629348, by rfl⟩ : syracuseStep 839131 = 1258697) B1258697
theorem B839207 : Blo 838352 839207 := bstep (se 1 (by rfl) ⟨629405, by rfl⟩ : syracuseStep 839207 = 1258811) B1258811
theorem B839247 : Blo 838352 839247 := bstep (se 1 (by rfl) ⟨629435, by rfl⟩ : syracuseStep 839247 = 1258871) B1258871
theorem B839263 : Blo 838352 839263 := bstep (se 1 (by rfl) ⟨629447, by rfl⟩ : syracuseStep 839263 = 1258895) B1258895
theorem B839291 : Blo 838352 839291 := bstep (se 1 (by rfl) ⟨629468, by rfl⟩ : syracuseStep 839291 = 1258937) B1258937
theorem B27283067 : Blo 838352 27283067 := bstep (se 1 (by rfl) ⟨20462300, by rfl⟩ : syracuseStep 27283067 = 40924601) B40924601
theorem B839343 : Blo 838352 839343 := bstep (se 1 (by rfl) ⟨629507, by rfl⟩ : syracuseStep 839343 = 1259015) B1259015
theorem B839367 : Blo 838352 839367 := bstep (se 1 (by rfl) ⟨629525, by rfl⟩ : syracuseStep 839367 = 1259051) B1259051
theorem B839387 : Blo 838352 839387 := bstep (se 1 (by rfl) ⟨629540, by rfl⟩ : syracuseStep 839387 = 1259081) B1259081
theorem B839463 : Blo 838352 839463 := bstep (se 1 (by rfl) ⟨629597, by rfl⟩ : syracuseStep 839463 = 1259195) B1259195
theorem B1888073 : Blo 838352 1888073 := bstep (se 2 (by rfl) ⟨708027, by rfl⟩ : syracuseStep 1888073 = 1416055) B1416055
theorem B839503 : Blo 838352 839503 := bstep (se 1 (by rfl) ⟨629627, by rfl⟩ : syracuseStep 839503 = 1259255) B1259255
theorem B839519 : Blo 838352 839519 := bstep (se 1 (by rfl) ⟨629639, by rfl⟩ : syracuseStep 839519 = 1259279) B1259279
theorem B4542317 : Blo 838352 4542317 := bstep (se 3 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 4542317 = 1703369) B1703369
theorem B839547 : Blo 838352 839547 := bstep (se 1 (by rfl) ⟨629660, by rfl⟩ : syracuseStep 839547 = 1259321) B1259321
theorem B839599 : Blo 838352 839599 := bstep (se 1 (by rfl) ⟨629699, by rfl⟩ : syracuseStep 839599 = 1259399) B1259399
theorem B2838455 : Blo 838352 2838455 := bstep (se 1 (by rfl) ⟨2128841, by rfl⟩ : syracuseStep 2838455 = 4257683) B4257683
theorem B839623 : Blo 838352 839623 := bstep (se 1 (by rfl) ⟨629717, by rfl⟩ : syracuseStep 839623 = 1259435) B1259435
theorem B839643 : Blo 838352 839643 := bstep (se 1 (by rfl) ⟨629732, by rfl⟩ : syracuseStep 839643 = 1259465) B1259465
theorem B19714063 : Blo 838352 19714063 := bstep (se 1 (by rfl) ⟨14785547, by rfl⟩ : syracuseStep 19714063 = 29571095) B29571095
theorem B839719 : Blo 838352 839719 := bstep (se 1 (by rfl) ⟨629789, by rfl⟩ : syracuseStep 839719 = 1259579) B1259579
theorem B839759 : Blo 838352 839759 := bstep (se 1 (by rfl) ⟨629819, by rfl⟩ : syracuseStep 839759 = 1259639) B1259639
theorem B8605777 : Blo 838352 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B839775 : Blo 838352 839775 := bstep (se 1 (by rfl) ⟨629831, by rfl⟩ : syracuseStep 839775 = 1259663) B1259663
theorem B839803 : Blo 838352 839803 := bstep (se 1 (by rfl) ⟨629852, by rfl⟩ : syracuseStep 839803 = 1259705) B1259705
theorem B839855 : Blo 838352 839855 := bstep (se 1 (by rfl) ⟨629891, by rfl⟩ : syracuseStep 839855 = 1259783) B1259783
theorem B839879 : Blo 838352 839879 := bstep (se 1 (by rfl) ⟨629909, by rfl⟩ : syracuseStep 839879 = 1259819) B1259819
theorem B839899 : Blo 838352 839899 := bstep (se 1 (by rfl) ⟨629924, by rfl⟩ : syracuseStep 839899 = 1259849) B1259849
theorem B839975 : Blo 838352 839975 := bstep (se 1 (by rfl) ⟨629981, by rfl⟩ : syracuseStep 839975 = 1259963) B1259963
theorem B6377777 : Blo 838352 6377777 := bstep (se 2 (by rfl) ⟨2391666, by rfl⟩ : syracuseStep 6377777 = 4783333) B4783333
theorem B840015 : Blo 838352 840015 := bstep (se 1 (by rfl) ⟨630011, by rfl⟩ : syracuseStep 840015 = 1260023) B1260023
theorem B4608343 : Blo 838352 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B840031 : Blo 838352 840031 := bstep (se 1 (by rfl) ⟨630023, by rfl⟩ : syracuseStep 840031 = 1260047) B1260047
theorem B840059 : Blo 838352 840059 := bstep (se 1 (by rfl) ⟨630044, by rfl⟩ : syracuseStep 840059 = 1260089) B1260089
theorem B840111 : Blo 838352 840111 := bstep (se 1 (by rfl) ⟨630083, by rfl⟩ : syracuseStep 840111 = 1260167) B1260167
theorem B840135 : Blo 838352 840135 := bstep (se 1 (by rfl) ⟨630101, by rfl⟩ : syracuseStep 840135 = 1260203) B1260203
theorem B3494345 : Blo 838352 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B840155 : Blo 838352 840155 := bstep (se 1 (by rfl) ⟨630116, by rfl⟩ : syracuseStep 840155 = 1260233) B1260233
theorem B2839049 : Blo 838352 2839049 := bstep (se 2 (by rfl) ⟨1064643, by rfl⟩ : syracuseStep 2839049 = 2129287) B2129287
theorem B840231 : Blo 838352 840231 := bstep (se 1 (by rfl) ⟨630173, by rfl⟩ : syracuseStep 840231 = 1260347) B1260347
theorem B1593913 : Blo 838352 1593913 := bstep (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) B1195435
theorem B840271 : Blo 838352 840271 := bstep (se 1 (by rfl) ⟨630203, by rfl⟩ : syracuseStep 840271 = 1260407) B1260407
theorem B840287 : Blo 838352 840287 := bstep (se 1 (by rfl) ⟨630215, by rfl⟩ : syracuseStep 840287 = 1260431) B1260431
theorem B1888865 : Blo 838352 1888865 := bstep (se 2 (by rfl) ⟨708324, by rfl⟩ : syracuseStep 1888865 = 1416649) B1416649
theorem B840315 : Blo 838352 840315 := bstep (se 1 (by rfl) ⟨630236, by rfl⟩ : syracuseStep 840315 = 1260473) B1260473
theorem B840367 : Blo 838352 840367 := bstep (se 1 (by rfl) ⟨630275, by rfl⟩ : syracuseStep 840367 = 1260551) B1260551
theorem B840391 : Blo 838352 840391 := bstep (se 1 (by rfl) ⟨630293, by rfl⟩ : syracuseStep 840391 = 1260587) B1260587
theorem B1790675 : Blo 838352 1790675 := bstep (se 1 (by rfl) ⟨1343006, by rfl⟩ : syracuseStep 1790675 = 2686013) B2686013
theorem B840411 : Blo 838352 840411 := bstep (se 1 (by rfl) ⟨630308, by rfl⟩ : syracuseStep 840411 = 1260617) B1260617
theorem B630477553 : Blo 838352 630477553 := bstep (se 2 (by rfl) ⟨236429082, by rfl⟩ : syracuseStep 630477553 = 472858165) B472858165
theorem B840487 : Blo 838352 840487 := bstep (se 1 (by rfl) ⟨630365, by rfl⟩ : syracuseStep 840487 = 1260731) B1260731
theorem B840527 : Blo 838352 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B840543 : Blo 838352 840543 := bstep (se 1 (by rfl) ⟨630407, by rfl⟩ : syracuseStep 840543 = 1260815) B1260815
theorem B1594217 : Blo 838352 1594217 := bstep (se 2 (by rfl) ⟨597831, by rfl⟩ : syracuseStep 1594217 = 1195663) B1195663
theorem B840571 : Blo 838352 840571 := bstep (se 1 (by rfl) ⟨630428, by rfl⟩ : syracuseStep 840571 = 1260857) B1260857
theorem B1594255 : Blo 838352 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B840623 : Blo 838352 840623 := bstep (se 1 (by rfl) ⟨630467, by rfl⟩ : syracuseStep 840623 = 1260935) B1260935
theorem B1889207 : Blo 838352 1889207 := bstep (se 1 (by rfl) ⟨1416905, by rfl⟩ : syracuseStep 1889207 = 2833811) B2833811
theorem B840647 : Blo 838352 840647 := bstep (se 1 (by rfl) ⟨630485, by rfl⟩ : syracuseStep 840647 = 1260971) B1260971
theorem B840667 : Blo 838352 840667 := bstep (se 1 (by rfl) ⟨630500, by rfl⟩ : syracuseStep 840667 = 1261001) B1261001
theorem B840743 : Blo 838352 840743 := bstep (se 1 (by rfl) ⟨630557, by rfl⟩ : syracuseStep 840743 = 1261115) B1261115
theorem B840783 : Blo 838352 840783 := bstep (se 1 (by rfl) ⟨630587, by rfl⟩ : syracuseStep 840783 = 1261175) B1261175
theorem B840799 : Blo 838352 840799 := bstep (se 1 (by rfl) ⟨630599, by rfl⟩ : syracuseStep 840799 = 1261199) B1261199
theorem B840827 : Blo 838352 840827 := bstep (se 1 (by rfl) ⟨630620, by rfl⟩ : syracuseStep 840827 = 1261241) B1261241
theorem B840879 : Blo 838352 840879 := bstep (se 1 (by rfl) ⟨630659, by rfl⟩ : syracuseStep 840879 = 1261319) B1261319
theorem B840903 : Blo 838352 840903 := bstep (se 1 (by rfl) ⟨630677, by rfl⟩ : syracuseStep 840903 = 1261355) B1261355
theorem B840923 : Blo 838352 840923 := bstep (se 1 (by rfl) ⟨630692, by rfl⟩ : syracuseStep 840923 = 1261385) B1261385
theorem B840999 : Blo 838352 840999 := bstep (se 1 (by rfl) ⟨630749, by rfl⟩ : syracuseStep 840999 = 1261499) B1261499
theorem B841039 : Blo 838352 841039 := bstep (se 1 (by rfl) ⟨630779, by rfl⟩ : syracuseStep 841039 = 1261559) B1261559
theorem B841055 : Blo 838352 841055 := bstep (se 1 (by rfl) ⟨630791, by rfl⟩ : syracuseStep 841055 = 1261583) B1261583
theorem B2839913 : Blo 838352 2839913 := bstep (se 2 (by rfl) ⟨1064967, by rfl⟩ : syracuseStep 2839913 = 2129935) B2129935
theorem B841083 : Blo 838352 841083 := bstep (se 1 (by rfl) ⟨630812, by rfl⟩ : syracuseStep 841083 = 1261625) B1261625
theorem B841135 : Blo 838352 841135 := bstep (se 1 (by rfl) ⟨630851, by rfl⟩ : syracuseStep 841135 = 1261703) B1261703
theorem B841159 : Blo 838352 841159 := bstep (se 1 (by rfl) ⟨630869, by rfl⟩ : syracuseStep 841159 = 1261739) B1261739
theorem B841179 : Blo 838352 841179 := bstep (se 1 (by rfl) ⟨630884, by rfl⟩ : syracuseStep 841179 = 1261769) B1261769
theorem B1889801 : Blo 838352 1889801 := bstep (se 2 (by rfl) ⟨708675, by rfl⟩ : syracuseStep 1889801 = 1417351) B1417351
theorem B841255 : Blo 838352 841255 := bstep (se 1 (by rfl) ⟨630941, by rfl⟩ : syracuseStep 841255 = 1261883) B1261883
theorem B841295 : Blo 838352 841295 := bstep (se 1 (by rfl) ⟨630971, by rfl⟩ : syracuseStep 841295 = 1261943) B1261943
theorem B841311 : Blo 838352 841311 := bstep (se 1 (by rfl) ⟨630983, by rfl⟩ : syracuseStep 841311 = 1261967) B1261967
theorem B841339 : Blo 838352 841339 := bstep (se 1 (by rfl) ⟨631004, by rfl⟩ : syracuseStep 841339 = 1262009) B1262009
theorem B841391 : Blo 838352 841391 := bstep (se 1 (by rfl) ⟨631043, by rfl⟩ : syracuseStep 841391 = 1262087) B1262087
theorem B841415 : Blo 838352 841415 := bstep (se 1 (by rfl) ⟨631061, by rfl⟩ : syracuseStep 841415 = 1262123) B1262123
theorem B841435 : Blo 838352 841435 := bstep (se 1 (by rfl) ⟨631076, by rfl⟩ : syracuseStep 841435 = 1262153) B1262153
theorem B841511 : Blo 838352 841511 := bstep (se 1 (by rfl) ⟨631133, by rfl⟩ : syracuseStep 841511 = 1262267) B1262267
theorem B2873161 : Blo 838352 2873161 := bstep (se 2 (by rfl) ⟨1077435, by rfl⟩ : syracuseStep 2873161 = 2154871) B2154871
theorem B841551 : Blo 838352 841551 := bstep (se 1 (by rfl) ⟨631163, by rfl⟩ : syracuseStep 841551 = 1262327) B1262327
theorem B1890143 : Blo 838352 1890143 := bstep (se 1 (by rfl) ⟨1417607, by rfl⟩ : syracuseStep 1890143 = 2835215) B2835215
theorem B841567 : Blo 838352 841567 := bstep (se 1 (by rfl) ⟨631175, by rfl⟩ : syracuseStep 841567 = 1262351) B1262351
theorem B841595 : Blo 838352 841595 := bstep (se 1 (by rfl) ⟨631196, by rfl⟩ : syracuseStep 841595 = 1262393) B1262393
theorem B841647 : Blo 838352 841647 := bstep (se 1 (by rfl) ⟨631235, by rfl⟩ : syracuseStep 841647 = 1262471) B1262471
theorem B2840507 : Blo 838352 2840507 := bstep (se 1 (by rfl) ⟨2130380, by rfl⟩ : syracuseStep 2840507 = 4260761) B4260761
theorem B841671 : Blo 838352 841671 := bstep (se 1 (by rfl) ⟨631253, by rfl⟩ : syracuseStep 841671 = 1262507) B1262507
theorem B841691 : Blo 838352 841691 := bstep (se 1 (by rfl) ⟨631268, by rfl⟩ : syracuseStep 841691 = 1262537) B1262537
theorem B1890323 : Blo 838352 1890323 := bstep (se 1 (by rfl) ⟨1417742, by rfl⟩ : syracuseStep 1890323 = 2835485) B2835485
theorem B841767 : Blo 838352 841767 := bstep (se 1 (by rfl) ⟨631325, by rfl⟩ : syracuseStep 841767 = 1262651) B1262651
theorem B1136719 : Blo 838352 1136719 := bstep (se 1 (by rfl) ⟨852539, by rfl⟩ : syracuseStep 1136719 = 1705079) B1705079
theorem B841807 : Blo 838352 841807 := bstep (se 1 (by rfl) ⟨631355, by rfl⟩ : syracuseStep 841807 = 1262711) B1262711
theorem B841823 : Blo 838352 841823 := bstep (se 1 (by rfl) ⟨631367, by rfl⟩ : syracuseStep 841823 = 1262735) B1262735
theorem B841851 : Blo 838352 841851 := bstep (se 1 (by rfl) ⟨631388, by rfl⟩ : syracuseStep 841851 = 1262777) B1262777
theorem B841903 : Blo 838352 841903 := bstep (se 1 (by rfl) ⟨631427, by rfl⟩ : syracuseStep 841903 = 1262855) B1262855
theorem B841927 : Blo 838352 841927 := bstep (se 1 (by rfl) ⟨631445, by rfl⟩ : syracuseStep 841927 = 1262891) B1262891
theorem B841947 : Blo 838352 841947 := bstep (se 1 (by rfl) ⟨631460, by rfl⟩ : syracuseStep 841947 = 1262921) B1262921
theorem B842023 : Blo 838352 842023 := bstep (se 1 (by rfl) ⟨631517, by rfl⟩ : syracuseStep 842023 = 1263035) B1263035
theorem B842063 : Blo 838352 842063 := bstep (se 1 (by rfl) ⟨631547, by rfl⟩ : syracuseStep 842063 = 1263095) B1263095
theorem B842079 : Blo 838352 842079 := bstep (se 1 (by rfl) ⟨631559, by rfl⟩ : syracuseStep 842079 = 1263119) B1263119
theorem B1890665 : Blo 838352 1890665 := bstep (se 2 (by rfl) ⟨708999, by rfl⟩ : syracuseStep 1890665 = 1417999) B1417999
theorem B842107 : Blo 838352 842107 := bstep (se 1 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 842107 = 1263161) B1263161
theorem B842159 : Blo 838352 842159 := bstep (se 1 (by rfl) ⟨631619, by rfl⟩ : syracuseStep 842159 = 1263239) B1263239
theorem B842183 : Blo 838352 842183 := bstep (se 1 (by rfl) ⟨631637, by rfl⟩ : syracuseStep 842183 = 1263275) B1263275
theorem B842203 : Blo 838352 842203 := bstep (se 1 (by rfl) ⟨631652, by rfl⟩ : syracuseStep 842203 = 1263305) B1263305
theorem B842279 : Blo 838352 842279 := bstep (se 1 (by rfl) ⟨631709, by rfl⟩ : syracuseStep 842279 = 1263419) B1263419
theorem B842319 : Blo 838352 842319 := bstep (se 1 (by rfl) ⟨631739, by rfl⟩ : syracuseStep 842319 = 1263479) B1263479
theorem B842335 : Blo 838352 842335 := bstep (se 1 (by rfl) ⟨631751, by rfl⟩ : syracuseStep 842335 = 1263503) B1263503
theorem B1596115 : Blo 838352 1596115 := bstep (se 1 (by rfl) ⟨1197086, by rfl⟩ : syracuseStep 1596115 = 2394173) B2394173
theorem B1596343 : Blo 838352 1596343 := bstep (se 1 (by rfl) ⟨1197257, by rfl⟩ : syracuseStep 1596343 = 2394515) B2394515
theorem B1891259 : Blo 838352 1891259 := bstep (se 1 (by rfl) ⟨1418444, by rfl⟩ : syracuseStep 1891259 = 2836889) B2836889
theorem B1891385 : Blo 838352 1891385 := bstep (se 2 (by rfl) ⟨709269, by rfl⟩ : syracuseStep 1891385 = 1418539) B1418539
theorem B1891727 : Blo 838352 1891727 := bstep (se 1 (by rfl) ⟨1418795, by rfl⟩ : syracuseStep 1891727 = 2837591) B2837591
theorem B19946933 : Blo 838352 19946933 := bstep (se 5 (by rfl) ⟨935012, by rfl⟩ : syracuseStep 19946933 = 1870025) B1870025
theorem B1596935 : Blo 838352 1596935 := bstep (se 1 (by rfl) ⟨1197701, by rfl⟩ : syracuseStep 1596935 = 2395403) B2395403
theorem B3595873 : Blo 838352 3595873 := bstep (se 2 (by rfl) ⟨1348452, by rfl⟩ : syracuseStep 3595873 = 2696905) B2696905
theorem B6381179 : Blo 838352 6381179 := bstep (se 1 (by rfl) ⟨4785884, by rfl⟩ : syracuseStep 6381179 = 9571769) B9571769
theorem B2842235 : Blo 838352 2842235 := bstep (se 1 (by rfl) ⟨2131676, by rfl⟩ : syracuseStep 2842235 = 4263353) B4263353
theorem B1892051 : Blo 838352 1892051 := bstep (se 1 (by rfl) ⟨1419038, by rfl⟩ : syracuseStep 1892051 = 2838077) B2838077
theorem B1793785 : Blo 838352 1793785 := bstep (se 2 (by rfl) ⟨672669, by rfl⟩ : syracuseStep 1793785 = 1345339) B1345339
theorem B2842397 : Blo 838352 2842397 := bstep (se 3 (by rfl) ⟨532949, by rfl⟩ : syracuseStep 2842397 = 1065899) B1065899
theorem B4317299 : Blo 838352 4317299 := bstep (se 1 (by rfl) ⟨3237974, by rfl⟩ : syracuseStep 4317299 = 6475949) B6475949
theorem B3694909 : Blo 838352 3694909 := bstep (se 3 (by rfl) ⟨692795, by rfl⟩ : syracuseStep 3694909 = 1385591) B1385591
theorem B1597801 : Blo 838352 1597801 := bstep (se 2 (by rfl) ⟨599175, by rfl⟩ : syracuseStep 1597801 = 1198351) B1198351
theorem B1597961 : Blo 838352 1597961 := bstep (se 2 (by rfl) ⟨599235, by rfl⟩ : syracuseStep 1597961 = 1198471) B1198471
theorem B3105377 : Blo 838352 3105377 := bstep (se 2 (by rfl) ⟨1164516, by rfl⟩ : syracuseStep 3105377 = 2329033) B2329033
theorem B1892987 : Blo 838352 1892987 := bstep (se 1 (by rfl) ⟨1419740, by rfl⟩ : syracuseStep 1892987 = 2839481) B2839481
theorem B1893113 : Blo 838352 1893113 := bstep (se 2 (by rfl) ⟨709917, by rfl⟩ : syracuseStep 1893113 = 1419835) B1419835
theorem B10216367 : Blo 838352 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B1893383 : Blo 838352 1893383 := bstep (se 1 (by rfl) ⟨1420037, by rfl⟩ : syracuseStep 1893383 = 2840075) B2840075
theorem B1893455 : Blo 838352 1893455 := bstep (se 1 (by rfl) ⟨1420091, by rfl⟩ : syracuseStep 1893455 = 2840183) B2840183
theorem B943303 : Blo 838352 943303 := bstep (se 1 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 943303 = 1414955) B1414955
theorem B3827087 : Blo 838352 3827087 := bstep (se 1 (by rfl) ⟨2870315, by rfl⟩ : syracuseStep 3827087 = 5740631) B5740631
theorem B9561563 : Blo 838352 9561563 := bstep (se 1 (by rfl) ⟨7171172, by rfl⟩ : syracuseStep 9561563 = 14342345) B14342345
theorem B4253147 : Blo 838352 4253147 := bstep (se 1 (by rfl) ⟨3189860, by rfl⟩ : syracuseStep 4253147 = 6379721) B6379721
theorem B1893851 : Blo 838352 1893851 := bstep (se 1 (by rfl) ⟨1420388, by rfl⟩ : syracuseStep 1893851 = 2840777) B2840777
theorem B2123273 : Blo 838352 2123273 := bstep (se 2 (by rfl) ⟨796227, by rfl⟩ : syracuseStep 2123273 = 1592455) B1592455
theorem B27223897 : Blo 838352 27223897 := bstep (se 2 (by rfl) ⟨10208961, by rfl⟩ : syracuseStep 27223897 = 20417923) B20417923
theorem B1894319 : Blo 838352 1894319 := bstep (se 1 (by rfl) ⟨1420739, by rfl⟩ : syracuseStep 1894319 = 2841479) B2841479
theorem B1796023 : Blo 838352 1796023 := bstep (se 1 (by rfl) ⟨1347017, by rfl⟩ : syracuseStep 1796023 = 2694035) B2694035
theorem B4253633 : Blo 838352 4253633 := bstep (se 2 (by rfl) ⟨1595112, by rfl⟩ : syracuseStep 4253633 = 3190225) B3190225
theorem B944167 : Blo 838352 944167 := bstep (se 1 (by rfl) ⟨708125, by rfl⟩ : syracuseStep 944167 = 1416251) B1416251
theorem B1894571 : Blo 838352 1894571 := bstep (se 1 (by rfl) ⟨1420928, by rfl⟩ : syracuseStep 1894571 = 2841857) B2841857
theorem B7170353 : Blo 838352 7170353 := bstep (se 2 (by rfl) ⟨2688882, by rfl⟩ : syracuseStep 7170353 = 5377765) B5377765
theorem B4614529 : Blo 838352 4614529 := bstep (se 2 (by rfl) ⟨1730448, by rfl⟩ : syracuseStep 4614529 = 3460897) B3460897
theorem B1010215 : Blo 838352 1010215 := bstep (se 1 (by rfl) ⟨757661, by rfl⟩ : syracuseStep 1010215 = 1515323) B1515323
theorem B5106235 : Blo 838352 5106235 := bstep (se 1 (by rfl) ⟨3829676, by rfl⟩ : syracuseStep 5106235 = 7659353) B7659353
theorem B2124427 : Blo 838352 2124427 := bstep (se 1 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 2124427 = 3186641) B3186641
theorem B1895111 : Blo 838352 1895111 := bstep (se 1 (by rfl) ⟨1421333, by rfl⟩ : syracuseStep 1895111 = 2842667) B2842667
theorem B2124731 : Blo 838352 2124731 := bstep (se 1 (by rfl) ⟨1593548, by rfl⟩ : syracuseStep 2124731 = 3187097) B3187097
theorem B1437115 : Blo 838352 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B2387465 : Blo 838352 2387465 := bstep (se 2 (by rfl) ⟨895299, by rfl⟩ : syracuseStep 2387465 = 1790599) B1790599
theorem B945787 : Blo 838352 945787 := bstep (se 1 (by rfl) ⟨709340, by rfl⟩ : syracuseStep 945787 = 1418681) B1418681
theorem B2125511 : Blo 838352 2125511 := bstep (se 1 (by rfl) ⟨1594133, by rfl⟩ : syracuseStep 2125511 = 3188267) B3188267
theorem B2125561 : Blo 838352 2125561 := bstep (se 2 (by rfl) ⟨797085, by rfl⟩ : syracuseStep 2125561 = 1594171) B1594171
theorem B5828561 : Blo 838352 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B6811685 : Blo 838352 6811685 := bstep (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) B1277191
theorem B946255 : Blo 838352 946255 := bstep (se 1 (by rfl) ⟨709691, by rfl⟩ : syracuseStep 946255 = 1419383) B1419383
theorem B4255901 : Blo 838352 4255901 := bstep (se 3 (by rfl) ⟨797981, by rfl⟩ : syracuseStep 4255901 = 1595963) B1595963
theorem B4550813 : Blo 838352 4550813 := bstep (se 3 (by rfl) ⟨853277, by rfl⟩ : syracuseStep 4550813 = 1706555) B1706555
theorem B4780417 : Blo 838352 4780417 := bstep (se 2 (by rfl) ⟨1792656, by rfl⟩ : syracuseStep 4780417 = 3585313) B3585313
theorem B2126209 : Blo 838352 2126209 := bstep (se 2 (by rfl) ⟨797328, by rfl⟩ : syracuseStep 2126209 = 1594657) B1594657
theorem B946651 : Blo 838352 946651 := bstep (se 1 (by rfl) ⟨709988, by rfl⟩ : syracuseStep 946651 = 1419977) B1419977
theorem B2388467 : Blo 838352 2388467 := bstep (se 1 (by rfl) ⟨1791350, by rfl⟩ : syracuseStep 2388467 = 3582701) B3582701
theorem B1438607 : Blo 838352 1438607 := bstep (se 1 (by rfl) ⟨1078955, by rfl⟩ : syracuseStep 1438607 = 2157911) B2157911
theorem B947119 : Blo 838352 947119 := bstep (se 1 (by rfl) ⟨710339, by rfl⟩ : syracuseStep 947119 = 1420679) B1420679
theorem B2388923 : Blo 838352 2388923 := bstep (se 1 (by rfl) ⟨1791692, by rfl⟩ : syracuseStep 2388923 = 3583385) B3583385
theorem B12088439 : Blo 838352 12088439 := bstep (se 1 (by rfl) ⟨9066329, by rfl⟩ : syracuseStep 12088439 = 18132659) B18132659
theorem B2127019 : Blo 838352 2127019 := bstep (se 1 (by rfl) ⟨1595264, by rfl⟩ : syracuseStep 2127019 = 3190529) B3190529
theorem B947551 : Blo 838352 947551 := bstep (se 1 (by rfl) ⟨710663, by rfl⟩ : syracuseStep 947551 = 1421327) B1421327
theorem B4257197 : Blo 838352 4257197 := bstep (se 3 (by rfl) ⟨798224, by rfl⟩ : syracuseStep 4257197 = 1596449) B1596449
theorem B2127323 : Blo 838352 2127323 := bstep (se 1 (by rfl) ⟨1595492, by rfl⟩ : syracuseStep 2127323 = 3190985) B3190985
theorem B32765429 : Blo 838352 32765429 := bstep (se 5 (by rfl) ⟨1535879, by rfl⟩ : syracuseStep 32765429 = 3071759) B3071759
theorem B2389753 : Blo 838352 2389753 := bstep (se 2 (by rfl) ⟨896157, by rfl⟩ : syracuseStep 2389753 = 1792315) B1792315
theorem B6060109 : Blo 838352 6060109 := bstep (se 3 (by rfl) ⟨1136270, by rfl⟩ : syracuseStep 6060109 = 2272541) B2272541
theorem B14351093 : Blo 838352 14351093 := bstep (se 5 (by rfl) ⟨672707, by rfl⟩ : syracuseStep 14351093 = 1345415) B1345415
theorem B1440617 : Blo 838352 1440617 := bstep (se 2 (by rfl) ⟨540231, by rfl⟩ : syracuseStep 1440617 = 1080463) B1080463
theorem B2128801 : Blo 838352 2128801 := bstep (se 2 (by rfl) ⟨798300, by rfl⟩ : syracuseStep 2128801 = 1596601) B1596601
theorem B4258817 : Blo 838352 4258817 := bstep (se 2 (by rfl) ⟨1597056, by rfl⟩ : syracuseStep 4258817 = 3194113) B3194113
theorem B6814799 : Blo 838352 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B2391211 : Blo 838352 2391211 := bstep (se 1 (by rfl) ⟨1793408, by rfl⟩ : syracuseStep 2391211 = 3586817) B3586817
theorem B1703263 : Blo 838352 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B2391439 : Blo 838352 2391439 := bstep (se 1 (by rfl) ⟨1793579, by rfl⟩ : syracuseStep 2391439 = 3587159) B3587159
theorem B3407305 : Blo 838352 3407305 := bstep (se 2 (by rfl) ⟨1277739, by rfl⟩ : syracuseStep 3407305 = 2555479) B2555479
theorem B1212103 : Blo 838352 1212103 := bstep (se 1 (by rfl) ⟨909077, by rfl⟩ : syracuseStep 1212103 = 1818155) B1818155
theorem B2686679 : Blo 838352 2686679 := bstep (se 1 (by rfl) ⟨2015009, by rfl⟩ : syracuseStep 2686679 = 4030019) B4030019
theorem B1343225 : Blo 838352 1343225 := bstep (se 2 (by rfl) ⟨503709, by rfl⟩ : syracuseStep 1343225 = 1007419) B1007419
theorem B4259627 : Blo 838352 4259627 := bstep (se 1 (by rfl) ⟨3194720, by rfl⟩ : syracuseStep 4259627 = 6389441) B6389441
theorem B3407791 : Blo 838352 3407791 := bstep (se 1 (by rfl) ⟨2555843, by rfl⟩ : syracuseStep 3407791 = 5111687) B5111687
theorem B6914099 : Blo 838352 6914099 := bstep (se 1 (by rfl) ⟨5185574, by rfl⟩ : syracuseStep 6914099 = 10371149) B10371149
theorem B1704041 : Blo 838352 1704041 := bstep (se 2 (by rfl) ⟨639015, by rfl⟩ : syracuseStep 1704041 = 1278031) B1278031
theorem B6062501 : Blo 838352 6062501 := bstep (se 4 (by rfl) ⟨568359, by rfl⟩ : syracuseStep 6062501 = 1136719) B1136719
theorem B4784609 : Blo 838352 4784609 := bstep (se 2 (by rfl) ⟨1794228, by rfl⟩ : syracuseStep 4784609 = 3588457) B3588457
theorem B2130401 : Blo 838352 2130401 := bstep (se 2 (by rfl) ⟨798900, by rfl⟩ : syracuseStep 2130401 = 1597801) B1597801
theorem B22970951 : Blo 838352 22970951 := bstep (se 1 (by rfl) ⟨17228213, by rfl⟩ : syracuseStep 22970951 = 34456427) B34456427
theorem B2130907 : Blo 838352 2130907 := bstep (se 1 (by rfl) ⟨1598180, by rfl⟩ : syracuseStep 2130907 = 3196361) B3196361
theorem B3736567 : Blo 838352 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B4031633 : Blo 838352 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B2131231 : Blo 838352 2131231 := bstep (se 1 (by rfl) ⟨1598423, by rfl⟩ : syracuseStep 2131231 = 3196847) B3196847
theorem B4261409 : Blo 838352 4261409 := bstep (se 2 (by rfl) ⟨1598028, by rfl⟩ : syracuseStep 4261409 = 3196057) B3196057
theorem B6391385 : Blo 838352 6391385 := bstep (se 2 (by rfl) ⟨2396769, by rfl⟩ : syracuseStep 6391385 = 4793539) B4793539
theorem B36308573 : Blo 838352 36308573 := bstep (se 3 (by rfl) ⟨6807857, by rfl⟩ : syracuseStep 36308573 = 13615715) B13615715
theorem B2558081 : Blo 838352 2558081 := bstep (se 2 (by rfl) ⟨959280, by rfl⟩ : syracuseStep 2558081 = 1918561) B1918561
theorem B18188711 : Blo 838352 18188711 := bstep (se 1 (by rfl) ⟨13641533, by rfl⟩ : syracuseStep 18188711 = 27283067) B27283067
theorem B2394697 : Blo 838352 2394697 := bstep (se 2 (by rfl) ⟨898011, by rfl⟩ : syracuseStep 2394697 = 1796023) B1796023
theorem B16124993 : Blo 838352 16124993 := bstep (se 2 (by rfl) ⟨6046872, by rfl⟩ : syracuseStep 16124993 = 12093745) B12093745
theorem B1346953 : Blo 838352 1346953 := bstep (se 2 (by rfl) ⟨505107, by rfl⟩ : syracuseStep 1346953 = 1010215) B1010215
theorem B7179785 : Blo 838352 7179785 := bstep (se 2 (by rfl) ⟨2692419, by rfl⟩ : syracuseStep 7179785 = 5384839) B5384839
theorem B3412331 : Blo 838352 3412331 := bstep (se 1 (by rfl) ⟨2559248, by rfl⟩ : syracuseStep 3412331 = 5118497) B5118497
theorem B2560999 : Blo 838352 2560999 := bstep (se 1 (by rfl) ⟨1920749, by rfl⟩ : syracuseStep 2560999 = 3841499) B3841499
theorem B7181561 : Blo 838352 7181561 := bstep (se 2 (by rfl) ⟨2693085, by rfl⟩ : syracuseStep 7181561 = 5386171) B5386171
theorem B26285417 : Blo 838352 26285417 := bstep (se 2 (by rfl) ⟨9857031, by rfl⟩ : syracuseStep 26285417 = 19714063) B19714063
theorem B11474369 : Blo 838352 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B2070251 : Blo 838352 2070251 := bstep (se 1 (by rfl) ⟨1552688, by rfl⟩ : syracuseStep 2070251 = 3105377) B3105377
theorem B840636737 : Blo 838352 840636737 := bstep (se 2 (by rfl) ⟨315238776, by rfl⟩ : syracuseStep 840636737 = 630477553) B630477553
theorem B1415515 : Blo 838352 1415515 := bstep (se 1 (by rfl) ⟨1061636, by rfl⟩ : syracuseStep 1415515 = 2123273) B2123273
theorem B2693587 : Blo 838352 2693587 := bstep (se 1 (by rfl) ⟨2020190, by rfl⟩ : syracuseStep 2693587 = 4040381) B4040381
theorem B12130879 : Blo 838352 12130879 := bstep (se 1 (by rfl) ⟨9098159, by rfl⟩ : syracuseStep 12130879 = 18196319) B18196319
theorem B1416487 : Blo 838352 1416487 := bstep (se 1 (by rfl) ⟨1062365, by rfl⟩ : syracuseStep 1416487 = 2124731) B2124731
theorem B3186337 : Blo 838352 3186337 := bstep (se 2 (by rfl) ⟨1194876, by rfl⟩ : syracuseStep 3186337 = 2389753) B2389753
theorem B1417007 : Blo 838352 1417007 := bstep (se 1 (by rfl) ⟨1062755, by rfl⟩ : syracuseStep 1417007 = 2125511) B2125511
theorem B7184537 : Blo 838352 7184537 := bstep (se 2 (by rfl) ⟨2694201, by rfl⟩ : syracuseStep 7184537 = 5388403) B5388403
theorem B959071 : Blo 838352 959071 := bstep (se 1 (by rfl) ⟨719303, by rfl⟩ : syracuseStep 959071 = 1438607) B1438607
theorem B4039321 : Blo 838352 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B1418215 : Blo 838352 1418215 := bstep (se 1 (by rfl) ⟨1063661, by rfl⟩ : syracuseStep 1418215 = 2127323) B2127323
theorem B6464549 : Blo 838352 6464549 := bstep (se 4 (by rfl) ⟨606051, by rfl⟩ : syracuseStep 6464549 = 1212103) B1212103
theorem B3024071 : Blo 838352 3024071 := bstep (se 1 (by rfl) ⟨2268053, by rfl⟩ : syracuseStep 3024071 = 4536107) B4536107
theorem B3188281 : Blo 838352 3188281 := bstep (se 2 (by rfl) ⟨1195605, by rfl⟩ : syracuseStep 3188281 = 2391211) B2391211
theorem B2271017 : Blo 838352 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B3188585 : Blo 838352 3188585 := bstep (se 2 (by rfl) ⟨1195719, by rfl⟩ : syracuseStep 3188585 = 2391439) B2391439
theorem B3025025 : Blo 838352 3025025 := bstep (se 2 (by rfl) ⟨1134384, by rfl⟩ : syracuseStep 3025025 = 2268769) B2268769
theorem B4794497 : Blo 838352 4794497 := bstep (se 2 (by rfl) ⟨1797936, by rfl⟩ : syracuseStep 4794497 = 3595873) B3595873
theorem B895483 : Blo 838352 895483 := bstep (se 1 (by rfl) ⟨671612, by rfl⟩ : syracuseStep 895483 = 1343225) B1343225
theorem B9087875 : Blo 838352 9087875 := bstep (se 1 (by rfl) ⟨6815906, by rfl⟩ : syracuseStep 9087875 = 13631813) B13631813
theorem B4926545 : Blo 838352 4926545 := bstep (se 2 (by rfl) ⟨1847454, by rfl⟩ : syracuseStep 4926545 = 3694909) B3694909
theorem B2075863 : Blo 838352 2075863 := bstep (se 1 (by rfl) ⟨1556897, by rfl⟩ : syracuseStep 2075863 = 3113795) B3113795
theorem B2829599 : Blo 838352 2829599 := bstep (se 1 (by rfl) ⟨2122199, by rfl⟩ : syracuseStep 2829599 = 4244399) B4244399
theorem B6368543 : Blo 838352 6368543 := bstep (se 1 (by rfl) ⟨4776407, by rfl⟩ : syracuseStep 6368543 = 9552815) B9552815
theorem B1420895 : Blo 838352 1420895 := bstep (se 1 (by rfl) ⟨1065671, by rfl⟩ : syracuseStep 1420895 = 2131343) B2131343
theorem B1421111 : Blo 838352 1421111 := bstep (se 1 (by rfl) ⟨1065833, by rfl⟩ : syracuseStep 1421111 = 2131667) B2131667
theorem B9318253 : Blo 838352 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B1257737 : Blo 838352 1257737 := bstep (se 2 (by rfl) ⟨471651, by rfl⟩ : syracuseStep 1257737 = 943303) B943303
theorem B1257839 : Blo 838352 1257839 := bstep (se 1 (by rfl) ⟨943379, by rfl⟩ : syracuseStep 1257839 = 1886759) B1886759
theorem B7188911 : Blo 838352 7188911 := bstep (se 1 (by rfl) ⟨5391683, by rfl⟩ : syracuseStep 7188911 = 10783367) B10783367
theorem B1258055 : Blo 838352 1258055 := bstep (se 1 (by rfl) ⟨943541, by rfl⟩ : syracuseStep 1258055 = 1887083) B1887083
theorem B1258091 : Blo 838352 1258091 := bstep (se 1 (by rfl) ⟨943568, by rfl⟩ : syracuseStep 1258091 = 1887137) B1887137
theorem B4043513 : Blo 838352 4043513 := bstep (se 2 (by rfl) ⟨1516317, by rfl⟩ : syracuseStep 4043513 = 3032635) B3032635
theorem B1061687 : Blo 838352 1061687 := bstep (se 1 (by rfl) ⟨796265, by rfl⟩ : syracuseStep 1061687 = 1592531) B1592531
theorem B1258319 : Blo 838352 1258319 := bstep (se 1 (by rfl) ⟨943739, by rfl⟩ : syracuseStep 1258319 = 1887479) B1887479
theorem B1913743 : Blo 838352 1913743 := bstep (se 1 (by rfl) ⟨1435307, by rfl⟩ : syracuseStep 1913743 = 2870615) B2870615
theorem B1061839 : Blo 838352 1061839 := bstep (se 1 (by rfl) ⟨796379, by rfl⟩ : syracuseStep 1061839 = 1592759) B1592759
theorem B1258715 : Blo 838352 1258715 := bstep (se 1 (by rfl) ⟨944036, by rfl⟩ : syracuseStep 1258715 = 1888073) B1888073
theorem B3028211 : Blo 838352 3028211 := bstep (se 1 (by rfl) ⟨2271158, by rfl⟩ : syracuseStep 3028211 = 4542317) B4542317
theorem B4306169 : Blo 838352 4306169 := bstep (se 2 (by rfl) ⟨1614813, by rfl⟩ : syracuseStep 4306169 = 3229627) B3229627
theorem B1258889 : Blo 838352 1258889 := bstep (se 2 (by rfl) ⟨472083, by rfl⟩ : syracuseStep 1258889 = 944167) B944167
theorem B16135685 : Blo 838352 16135685 := bstep (se 4 (by rfl) ⟨1512720, by rfl⟩ : syracuseStep 16135685 = 3025441) B3025441
theorem B2832029 : Blo 838352 2832029 := bstep (se 3 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 2832029 = 1062011) B1062011
theorem B1259243 : Blo 838352 1259243 := bstep (se 1 (by rfl) ⟨944432, by rfl⟩ : syracuseStep 1259243 = 1888865) B1888865
theorem B1193783 : Blo 838352 1193783 := bstep (se 1 (by rfl) ⟨895337, by rfl⟩ : syracuseStep 1193783 = 1790675) B1790675
theorem B1062811 : Blo 838352 1062811 := bstep (se 1 (by rfl) ⟨797108, by rfl⟩ : syracuseStep 1062811 = 1594217) B1594217
theorem B1259471 : Blo 838352 1259471 := bstep (se 1 (by rfl) ⟨944603, by rfl⟩ : syracuseStep 1259471 = 1889207) B1889207
theorem B2832569 : Blo 838352 2832569 := bstep (se 2 (by rfl) ⟨1062213, by rfl⟩ : syracuseStep 2832569 = 2124427) B2124427
theorem B17217773 : Blo 838352 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B1259867 : Blo 838352 1259867 := bstep (se 1 (by rfl) ⟨944900, by rfl⟩ : syracuseStep 1259867 = 1889801) B1889801
theorem B1260095 : Blo 838352 1260095 := bstep (se 1 (by rfl) ⟨945071, by rfl⟩ : syracuseStep 1260095 = 1890143) B1890143
theorem B87374477 : Blo 838352 87374477 := bstep (se 3 (by rfl) ⟨16382714, by rfl⟩ : syracuseStep 87374477 = 32765429) B32765429
theorem B1260215 : Blo 838352 1260215 := bstep (se 1 (by rfl) ⟨945161, by rfl⟩ : syracuseStep 1260215 = 1890323) B1890323
theorem B1260443 : Blo 838352 1260443 := bstep (se 1 (by rfl) ⟨945332, by rfl⟩ : syracuseStep 1260443 = 1890665) B1890665
theorem B1195241 : Blo 838352 1195241 := bstep (se 2 (by rfl) ⟨448215, by rfl⟩ : syracuseStep 1195241 = 896431) B896431
theorem B1916153 : Blo 838352 1916153 := bstep (se 2 (by rfl) ⟨718557, by rfl⟩ : syracuseStep 1916153 = 1437115) B1437115
theorem B1260839 : Blo 838352 1260839 := bstep (se 1 (by rfl) ⟨945629, by rfl⟩ : syracuseStep 1260839 = 1891259) B1891259
theorem B1260923 : Blo 838352 1260923 := bstep (se 1 (by rfl) ⟨945692, by rfl⟩ : syracuseStep 1260923 = 1891385) B1891385
theorem B1228169 : Blo 838352 1228169 := bstep (se 2 (by rfl) ⟨460563, by rfl⟩ : syracuseStep 1228169 = 921127) B921127
theorem B1261049 : Blo 838352 1261049 := bstep (se 2 (by rfl) ⟨472893, by rfl⟩ : syracuseStep 1261049 = 945787) B945787
theorem B4046395 : Blo 838352 4046395 := bstep (se 1 (by rfl) ⟨3034796, by rfl⟩ : syracuseStep 4046395 = 6069593) B6069593
theorem B1261151 : Blo 838352 1261151 := bstep (se 1 (by rfl) ⟨945863, by rfl⟩ : syracuseStep 1261151 = 1891727) B1891727
theorem B2834081 : Blo 838352 2834081 := bstep (se 2 (by rfl) ⟨1062780, by rfl⟩ : syracuseStep 2834081 = 2125561) B2125561
theorem B1261367 : Blo 838352 1261367 := bstep (se 1 (by rfl) ⟨946025, by rfl⟩ : syracuseStep 1261367 = 1892051) B1892051
theorem B1261673 : Blo 838352 1261673 := bstep (se 2 (by rfl) ⟨473127, by rfl⟩ : syracuseStep 1261673 = 946255) B946255
theorem B1065307 : Blo 838352 1065307 := bstep (se 1 (by rfl) ⟨798980, by rfl⟩ : syracuseStep 1065307 = 1597961) B1597961
theorem B13812133 : Blo 838352 13812133 := bstep (se 4 (by rfl) ⟨1294887, by rfl⟩ : syracuseStep 13812133 = 2589775) B2589775
theorem B1261991 : Blo 838352 1261991 := bstep (se 1 (by rfl) ⟨946493, by rfl⟩ : syracuseStep 1261991 = 1892987) B1892987
theorem B6144457 : Blo 838352 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B1262075 : Blo 838352 1262075 := bstep (se 1 (by rfl) ⟨946556, by rfl⟩ : syracuseStep 1262075 = 1893113) B1893113
theorem B6373889 : Blo 838352 6373889 := bstep (se 2 (by rfl) ⟨2390208, by rfl⟩ : syracuseStep 6373889 = 4780417) B4780417
theorem B2834945 : Blo 838352 2834945 := bstep (se 2 (by rfl) ⟨1063104, by rfl⟩ : syracuseStep 2834945 = 2126209) B2126209
theorem B1262201 : Blo 838352 1262201 := bstep (se 2 (by rfl) ⟨473325, by rfl⟩ : syracuseStep 1262201 = 946651) B946651
theorem B1262255 : Blo 838352 1262255 := bstep (se 1 (by rfl) ⟨946691, by rfl⟩ : syracuseStep 1262255 = 1893383) B1893383
theorem B1262303 : Blo 838352 1262303 := bstep (se 1 (by rfl) ⟨946727, by rfl⟩ : syracuseStep 1262303 = 1893455) B1893455
theorem B12108689 : Blo 838352 12108689 := bstep (se 2 (by rfl) ⟨4540758, by rfl⟩ : syracuseStep 12108689 = 9081517) B9081517
theorem B6374375 : Blo 838352 6374375 := bstep (se 1 (by rfl) ⟨4780781, by rfl⟩ : syracuseStep 6374375 = 9561563) B9561563
theorem B2835431 : Blo 838352 2835431 := bstep (se 1 (by rfl) ⟨2126573, by rfl⟩ : syracuseStep 2835431 = 4253147) B4253147
theorem B1262567 : Blo 838352 1262567 := bstep (se 1 (by rfl) ⟨946925, by rfl⟩ : syracuseStep 1262567 = 1893851) B1893851
theorem B16172045 : Blo 838352 16172045 := bstep (se 3 (by rfl) ⟨3032258, by rfl⟩ : syracuseStep 16172045 = 6064517) B6064517
theorem B1262825 : Blo 838352 1262825 := bstep (se 2 (by rfl) ⟨473559, by rfl⟩ : syracuseStep 1262825 = 947119) B947119
theorem B4244723 : Blo 838352 4244723 := bstep (se 1 (by rfl) ⟨3183542, by rfl⟩ : syracuseStep 4244723 = 6367085) B6367085
theorem B1262879 : Blo 838352 1262879 := bstep (se 1 (by rfl) ⟨947159, by rfl⟩ : syracuseStep 1262879 = 1894319) B1894319
theorem B2835755 : Blo 838352 2835755 := bstep (se 1 (by rfl) ⟨2126816, by rfl⟩ : syracuseStep 2835755 = 4253633) B4253633
theorem B1263047 : Blo 838352 1263047 := bstep (se 1 (by rfl) ⟨947285, by rfl⟩ : syracuseStep 1263047 = 1894571) B1894571
theorem B2836025 : Blo 838352 2836025 := bstep (se 2 (by rfl) ⟨1063509, by rfl⟩ : syracuseStep 2836025 = 2127019) B2127019
theorem B16401977 : Blo 838352 16401977 := bstep (se 2 (by rfl) ⟨6150741, by rfl⟩ : syracuseStep 16401977 = 12301483) B12301483
theorem B14534437 : Blo 838352 14534437 := bstep (se 4 (by rfl) ⟨1362603, by rfl⟩ : syracuseStep 14534437 = 2725207) B2725207
theorem B1263401 : Blo 838352 1263401 := bstep (se 2 (by rfl) ⟨473775, by rfl⟩ : syracuseStep 1263401 = 947551) B947551
theorem B1263407 : Blo 838352 1263407 := bstep (se 1 (by rfl) ⟨947555, by rfl⟩ : syracuseStep 1263407 = 1895111) B1895111
theorem B44222593 : Blo 838352 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B1591643 : Blo 838352 1591643 := bstep (se 1 (by rfl) ⟨1193732, by rfl⟩ : syracuseStep 1591643 = 2387465) B2387465
theorem B3885707 : Blo 838352 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B1886903 : Blo 838352 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B4541123 : Blo 838352 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B838367 : Blo 838352 838367 := bstep (se 1 (by rfl) ⟨628775, by rfl⟩ : syracuseStep 838367 = 1257551) B1257551
theorem B8080145 : Blo 838352 8080145 := bstep (se 2 (by rfl) ⟨3030054, by rfl⟩ : syracuseStep 8080145 = 6060109) B6060109
theorem B2837267 : Blo 838352 2837267 := bstep (se 1 (by rfl) ⟨2127950, by rfl⟩ : syracuseStep 2837267 = 4255901) B4255901
theorem B3033875 : Blo 838352 3033875 := bstep (se 1 (by rfl) ⟨2275406, by rfl⟩ : syracuseStep 3033875 = 4550813) B4550813
theorem B838447 : Blo 838352 838447 := bstep (se 1 (by rfl) ⟨628835, by rfl⟩ : syracuseStep 838447 = 1257671) B1257671
theorem B1887119 : Blo 838352 1887119 := bstep (se 1 (by rfl) ⟨1415339, by rfl⟩ : syracuseStep 1887119 = 2830679) B2830679
theorem B2018191 : Blo 838352 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B838555 : Blo 838352 838555 := bstep (se 1 (by rfl) ⟨628916, by rfl⟩ : syracuseStep 838555 = 1257833) B1257833
theorem B838607 : Blo 838352 838607 := bstep (se 1 (by rfl) ⟨628955, by rfl⟩ : syracuseStep 838607 = 1257911) B1257911
theorem B838631 : Blo 838352 838631 := bstep (se 1 (by rfl) ⟨628973, by rfl⟩ : syracuseStep 838631 = 1257947) B1257947
theorem B1592311 : Blo 838352 1592311 := bstep (se 1 (by rfl) ⟨1194233, by rfl⟩ : syracuseStep 1592311 = 2388467) B2388467
theorem B4246667 : Blo 838352 4246667 := bstep (se 1 (by rfl) ⟨3185000, by rfl⟩ : syracuseStep 4246667 = 6370001) B6370001
theorem B838943 : Blo 838352 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B1592615 : Blo 838352 1592615 := bstep (se 1 (by rfl) ⟨1194461, by rfl⟩ : syracuseStep 1592615 = 2388923) B2388923
theorem B3198275 : Blo 838352 3198275 := bstep (se 1 (by rfl) ⟨2398706, by rfl⟩ : syracuseStep 3198275 = 4797413) B4797413
theorem B839003 : Blo 838352 839003 := bstep (se 1 (by rfl) ⟨629252, by rfl⟩ : syracuseStep 839003 = 1258505) B1258505
theorem B3198305 : Blo 838352 3198305 := bstep (se 2 (by rfl) ⟨1199364, by rfl⟩ : syracuseStep 3198305 = 2398729) B2398729
theorem B839023 : Blo 838352 839023 := bstep (se 1 (by rfl) ⟨629267, by rfl⟩ : syracuseStep 839023 = 1258535) B1258535
theorem B1592713 : Blo 838352 1592713 := bstep (se 2 (by rfl) ⟨597267, by rfl⟩ : syracuseStep 1592713 = 1194535) B1194535
theorem B839079 : Blo 838352 839079 := bstep (se 1 (by rfl) ⟨629309, by rfl⟩ : syracuseStep 839079 = 1258619) B1258619
theorem B25873843 : Blo 838352 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B839163 : Blo 838352 839163 := bstep (se 1 (by rfl) ⟨629372, by rfl⟩ : syracuseStep 839163 = 1258745) B1258745
theorem B839231 : Blo 838352 839231 := bstep (se 1 (by rfl) ⟨629423, by rfl⟩ : syracuseStep 839231 = 1258847) B1258847
theorem B839239 : Blo 838352 839239 := bstep (se 1 (by rfl) ⟨629429, by rfl⟩ : syracuseStep 839239 = 1258859) B1258859
theorem B1887839 : Blo 838352 1887839 := bstep (se 1 (by rfl) ⟨1415879, by rfl⟩ : syracuseStep 1887839 = 2831759) B2831759
theorem B2838131 : Blo 838352 2838131 := bstep (se 1 (by rfl) ⟨2128598, by rfl⟩ : syracuseStep 2838131 = 4257197) B4257197
theorem B839391 : Blo 838352 839391 := bstep (se 1 (by rfl) ⟨629543, by rfl⟩ : syracuseStep 839391 = 1259087) B1259087
theorem B839471 : Blo 838352 839471 := bstep (se 1 (by rfl) ⟨629603, by rfl⟩ : syracuseStep 839471 = 1259207) B1259207
theorem B1888055 : Blo 838352 1888055 := bstep (se 1 (by rfl) ⟨1416041, by rfl⟩ : syracuseStep 1888055 = 2832083) B2832083
theorem B2838401 : Blo 838352 2838401 := bstep (se 2 (by rfl) ⟨1064400, by rfl⟩ : syracuseStep 2838401 = 2128801) B2128801
theorem B839579 : Blo 838352 839579 := bstep (se 1 (by rfl) ⟨629684, by rfl⟩ : syracuseStep 839579 = 1259369) B1259369
theorem B839631 : Blo 838352 839631 := bstep (se 1 (by rfl) ⟨629723, by rfl⟩ : syracuseStep 839631 = 1259447) B1259447
theorem B839655 : Blo 838352 839655 := bstep (se 1 (by rfl) ⟨629741, by rfl⟩ : syracuseStep 839655 = 1259483) B1259483
theorem B1888361 : Blo 838352 1888361 := bstep (se 2 (by rfl) ⟨708135, by rfl⟩ : syracuseStep 1888361 = 1416271) B1416271
theorem B839967 : Blo 838352 839967 := bstep (se 1 (by rfl) ⟨629975, by rfl⟩ : syracuseStep 839967 = 1259951) B1259951
theorem B5394761 : Blo 838352 5394761 := bstep (se 2 (by rfl) ⟨2023035, by rfl⟩ : syracuseStep 5394761 = 4046071) B4046071
theorem B840027 : Blo 838352 840027 := bstep (se 1 (by rfl) ⟨630020, by rfl⟩ : syracuseStep 840027 = 1260041) B1260041
theorem B840047 : Blo 838352 840047 := bstep (se 1 (by rfl) ⟨630035, by rfl⟩ : syracuseStep 840047 = 1260071) B1260071
theorem B15323525 : Blo 838352 15323525 := bstep (se 4 (by rfl) ⟨1436580, by rfl⟩ : syracuseStep 15323525 = 2873161) B2873161
theorem B840103 : Blo 838352 840103 := bstep (se 1 (by rfl) ⟨630077, by rfl⟩ : syracuseStep 840103 = 1260155) B1260155
theorem B840187 : Blo 838352 840187 := bstep (se 1 (by rfl) ⟨630140, by rfl⟩ : syracuseStep 840187 = 1260281) B1260281
theorem B840255 : Blo 838352 840255 := bstep (se 1 (by rfl) ⟨630191, by rfl⟩ : syracuseStep 840255 = 1260383) B1260383
theorem B840263 : Blo 838352 840263 := bstep (se 1 (by rfl) ⟨630197, by rfl⟩ : syracuseStep 840263 = 1260395) B1260395
theorem B1888847 : Blo 838352 1888847 := bstep (se 1 (by rfl) ⟨1416635, by rfl⟩ : syracuseStep 1888847 = 2833271) B2833271
theorem B4543073 : Blo 838352 4543073 := bstep (se 2 (by rfl) ⟨1703652, by rfl⟩ : syracuseStep 4543073 = 3407305) B3407305
theorem B2839211 : Blo 838352 2839211 := bstep (se 1 (by rfl) ⟨2129408, by rfl⟩ : syracuseStep 2839211 = 4258817) B4258817
theorem B4248287 : Blo 838352 4248287 := bstep (se 1 (by rfl) ⟨3186215, by rfl⟩ : syracuseStep 4248287 = 6372431) B6372431
theorem B1888991 : Blo 838352 1888991 := bstep (se 1 (by rfl) ⟨1416743, by rfl⟩ : syracuseStep 1888991 = 2833487) B2833487
theorem B4543199 : Blo 838352 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B840415 : Blo 838352 840415 := bstep (se 1 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 840415 = 1260623) B1260623
theorem B840495 : Blo 838352 840495 := bstep (se 1 (by rfl) ⟨630371, by rfl⟩ : syracuseStep 840495 = 1260743) B1260743
theorem B840603 : Blo 838352 840603 := bstep (se 1 (by rfl) ⟨630452, by rfl⟩ : syracuseStep 840603 = 1260905) B1260905
theorem B840655 : Blo 838352 840655 := bstep (se 1 (by rfl) ⟨630491, by rfl⟩ : syracuseStep 840655 = 1260983) B1260983
theorem B1889243 : Blo 838352 1889243 := bstep (se 1 (by rfl) ⟨1416932, by rfl⟩ : syracuseStep 1889243 = 2833865) B2833865
theorem B840679 : Blo 838352 840679 := bstep (se 1 (by rfl) ⟨630509, by rfl⟩ : syracuseStep 840679 = 1261019) B1261019
theorem B1791119 : Blo 838352 1791119 := bstep (se 1 (by rfl) ⟨1343339, by rfl⟩ : syracuseStep 1791119 = 2686679) B2686679
theorem B1889423 : Blo 838352 1889423 := bstep (se 1 (by rfl) ⟨1417067, by rfl⟩ : syracuseStep 1889423 = 2834135) B2834135
theorem B2839751 : Blo 838352 2839751 := bstep (se 1 (by rfl) ⟨2129813, by rfl⟩ : syracuseStep 2839751 = 4259627) B4259627
theorem B1889513 : Blo 838352 1889513 := bstep (se 2 (by rfl) ⟨708567, by rfl⟩ : syracuseStep 1889513 = 1417135) B1417135
theorem B4543721 : Blo 838352 4543721 := bstep (se 2 (by rfl) ⟨1703895, by rfl⟩ : syracuseStep 4543721 = 3407791) B3407791
theorem B840991 : Blo 838352 840991 := bstep (se 1 (by rfl) ⟨630743, by rfl⟩ : syracuseStep 840991 = 1261487) B1261487
theorem B1889567 : Blo 838352 1889567 := bstep (se 1 (by rfl) ⟨1417175, by rfl⟩ : syracuseStep 1889567 = 2834351) B2834351
theorem B841051 : Blo 838352 841051 := bstep (se 1 (by rfl) ⟨630788, by rfl⟩ : syracuseStep 841051 = 1261577) B1261577
theorem B841071 : Blo 838352 841071 := bstep (se 1 (by rfl) ⟨630803, by rfl⟩ : syracuseStep 841071 = 1261607) B1261607
theorem B16176509 : Blo 838352 16176509 := bstep (se 3 (by rfl) ⟨3033095, by rfl⟩ : syracuseStep 16176509 = 6066191) B6066191
theorem B841127 : Blo 838352 841127 := bstep (se 1 (by rfl) ⟨630845, by rfl⟩ : syracuseStep 841127 = 1261691) B1261691
theorem B841211 : Blo 838352 841211 := bstep (se 1 (by rfl) ⟨630908, by rfl⟩ : syracuseStep 841211 = 1261817) B1261817
theorem B841279 : Blo 838352 841279 := bstep (se 1 (by rfl) ⟨630959, by rfl⟩ : syracuseStep 841279 = 1261919) B1261919
theorem B841287 : Blo 838352 841287 := bstep (se 1 (by rfl) ⟨630965, by rfl⟩ : syracuseStep 841287 = 1261931) B1261931
theorem B1791649 : Blo 838352 1791649 := bstep (se 2 (by rfl) ⟨671868, by rfl⟩ : syracuseStep 1791649 = 1343737) B1343737
theorem B841439 : Blo 838352 841439 := bstep (se 1 (by rfl) ⟨631079, by rfl⟩ : syracuseStep 841439 = 1262159) B1262159
theorem B1595143 : Blo 838352 1595143 := bstep (se 1 (by rfl) ⟨1196357, by rfl⟩ : syracuseStep 1595143 = 2392715) B2392715
theorem B1890089 : Blo 838352 1890089 := bstep (se 2 (by rfl) ⟨708783, by rfl⟩ : syracuseStep 1890089 = 1417567) B1417567
theorem B841519 : Blo 838352 841519 := bstep (se 1 (by rfl) ⟨631139, by rfl⟩ : syracuseStep 841519 = 1262279) B1262279
theorem B841627 : Blo 838352 841627 := bstep (se 1 (by rfl) ⟨631220, by rfl⟩ : syracuseStep 841627 = 1262441) B1262441
theorem B841679 : Blo 838352 841679 := bstep (se 1 (by rfl) ⟨631259, by rfl⟩ : syracuseStep 841679 = 1262519) B1262519
theorem B841703 : Blo 838352 841703 := bstep (se 1 (by rfl) ⟨631277, by rfl⟩ : syracuseStep 841703 = 1262555) B1262555
theorem B842015 : Blo 838352 842015 := bstep (se 1 (by rfl) ⟨631511, by rfl⟩ : syracuseStep 842015 = 1263023) B1263023
theorem B842075 : Blo 838352 842075 := bstep (se 1 (by rfl) ⟨631556, by rfl⟩ : syracuseStep 842075 = 1263113) B1263113
theorem B2873711 : Blo 838352 2873711 := bstep (se 1 (by rfl) ⟨2155283, by rfl⟩ : syracuseStep 2873711 = 4310567) B4310567
theorem B842095 : Blo 838352 842095 := bstep (se 1 (by rfl) ⟨631571, by rfl⟩ : syracuseStep 842095 = 1263143) B1263143
theorem B842151 : Blo 838352 842151 := bstep (se 1 (by rfl) ⟨631613, by rfl⟩ : syracuseStep 842151 = 1263227) B1263227
theorem B842235 : Blo 838352 842235 := bstep (se 1 (by rfl) ⟨631676, by rfl⟩ : syracuseStep 842235 = 1263353) B1263353
theorem B3824167 : Blo 838352 3824167 := bstep (se 1 (by rfl) ⟨2868125, by rfl⟩ : syracuseStep 3824167 = 5736251) B5736251
theorem B8608315 : Blo 838352 8608315 := bstep (se 1 (by rfl) ⟨6456236, by rfl⟩ : syracuseStep 8608315 = 12912473) B12912473
theorem B842303 : Blo 838352 842303 := bstep (se 1 (by rfl) ⟨631727, by rfl⟩ : syracuseStep 842303 = 1263455) B1263455
theorem B842311 : Blo 838352 842311 := bstep (se 1 (by rfl) ⟨631733, by rfl⟩ : syracuseStep 842311 = 1263467) B1263467
theorem B6380207 : Blo 838352 6380207 := bstep (se 1 (by rfl) ⟨4785155, by rfl⟩ : syracuseStep 6380207 = 9570311) B9570311
theorem B2841263 : Blo 838352 2841263 := bstep (se 1 (by rfl) ⟨2130947, by rfl⟩ : syracuseStep 2841263 = 4261895) B4261895
theorem B1891151 : Blo 838352 1891151 := bstep (se 1 (by rfl) ⟨1418363, by rfl⟩ : syracuseStep 1891151 = 2836727) B2836727
theorem B4250555 : Blo 838352 4250555 := bstep (se 1 (by rfl) ⟨3187916, by rfl⟩ : syracuseStep 4250555 = 6375833) B6375833
theorem B2841587 : Blo 838352 2841587 := bstep (se 1 (by rfl) ⟨2131190, by rfl⟩ : syracuseStep 2841587 = 4262381) B4262381
theorem B1891367 : Blo 838352 1891367 := bstep (se 1 (by rfl) ⟨1418525, by rfl⟩ : syracuseStep 1891367 = 2837051) B2837051
theorem B2022497 : Blo 838352 2022497 := bstep (se 2 (by rfl) ⟨758436, by rfl⟩ : syracuseStep 2022497 = 1516873) B1516873
theorem B1891547 : Blo 838352 1891547 := bstep (se 1 (by rfl) ⟨1418660, by rfl⟩ : syracuseStep 1891547 = 2837321) B2837321
theorem B1891745 : Blo 838352 1891745 := bstep (se 2 (by rfl) ⟨709404, by rfl⟩ : syracuseStep 1891745 = 1418809) B1418809
theorem B2842127 : Blo 838352 2842127 := bstep (se 1 (by rfl) ⟨2131595, by rfl⟩ : syracuseStep 2842127 = 4263191) B4263191
theorem B5463713 : Blo 838352 5463713 := bstep (se 2 (by rfl) ⟨2048892, by rfl⟩ : syracuseStep 5463713 = 4097785) B4097785
theorem B36298529 : Blo 838352 36298529 := bstep (se 2 (by rfl) ⟨13611948, by rfl⟩ : syracuseStep 36298529 = 27223897) B27223897
theorem B1892303 : Blo 838352 1892303 := bstep (se 1 (by rfl) ⟨1419227, by rfl⟩ : syracuseStep 1892303 = 2838455) B2838455
theorem B1597391 : Blo 838352 1597391 := bstep (se 1 (by rfl) ⟨1198043, by rfl⟩ : syracuseStep 1597391 = 2396087) B2396087
theorem B4251851 : Blo 838352 4251851 := bstep (se 1 (by rfl) ⟨3188888, by rfl⟩ : syracuseStep 4251851 = 6377777) B6377777
theorem B1892681 : Blo 838352 1892681 := bstep (se 2 (by rfl) ⟨709755, by rfl⟩ : syracuseStep 1892681 = 1419511) B1419511
theorem B1892699 : Blo 838352 1892699 := bstep (se 1 (by rfl) ⟨1419524, by rfl⟩ : syracuseStep 1892699 = 2839049) B2839049
theorem B2122159 : Blo 838352 2122159 := bstep (se 1 (by rfl) ⟨1591619, by rfl⟩ : syracuseStep 2122159 = 3183239) B3183239
theorem B10936777 : Blo 838352 10936777 := bstep (se 2 (by rfl) ⟨4101291, by rfl⟩ : syracuseStep 10936777 = 8202583) B8202583
theorem B1597907 : Blo 838352 1597907 := bstep (se 1 (by rfl) ⟨1198430, by rfl⟩ : syracuseStep 1597907 = 2396861) B2396861
theorem B6152705 : Blo 838352 6152705 := bstep (se 2 (by rfl) ⟨2307264, by rfl⟩ : syracuseStep 6152705 = 4614529) B4614529
theorem B6382091 : Blo 838352 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B1794631 : Blo 838352 1794631 := bstep (se 1 (by rfl) ⟨1345973, by rfl⟩ : syracuseStep 1794631 = 2691947) B2691947
theorem B6382151 : Blo 838352 6382151 := bstep (se 1 (by rfl) ⟨4786613, by rfl⟩ : syracuseStep 6382151 = 9573227) B9573227
theorem B1598059 : Blo 838352 1598059 := bstep (se 1 (by rfl) ⟨1198544, by rfl⟩ : syracuseStep 1598059 = 2397089) B2397089
theorem B13656721 : Blo 838352 13656721 := bstep (se 2 (by rfl) ⟨5121270, by rfl⟩ : syracuseStep 13656721 = 10242541) B10242541
theorem B2122463 : Blo 838352 2122463 := bstep (se 1 (by rfl) ⟨1591847, by rfl⟩ : syracuseStep 2122463 = 3183695) B3183695
theorem B6808313 : Blo 838352 6808313 := bstep (se 2 (by rfl) ⟨2553117, by rfl⟩ : syracuseStep 6808313 = 5106235) B5106235
theorem B8086331 : Blo 838352 8086331 := bstep (se 1 (by rfl) ⟨6064748, by rfl⟩ : syracuseStep 8086331 = 12129497) B12129497
theorem B1598287 : Blo 838352 1598287 := bstep (se 1 (by rfl) ⟨1198715, by rfl⟩ : syracuseStep 1598287 = 2397431) B2397431
theorem B9069407 : Blo 838352 9069407 := bstep (se 1 (by rfl) ⟨6802055, by rfl⟩ : syracuseStep 9069407 = 13604111) B13604111
theorem B1893275 : Blo 838352 1893275 := bstep (se 1 (by rfl) ⟨1419956, by rfl⟩ : syracuseStep 1893275 = 2839913) B2839913
theorem B1598363 : Blo 838352 1598363 := bstep (se 1 (by rfl) ⟨1198772, by rfl⟩ : syracuseStep 1598363 = 2397545) B2397545
theorem B1893473 : Blo 838352 1893473 := bstep (se 2 (by rfl) ⟨710052, by rfl⟩ : syracuseStep 1893473 = 1420105) B1420105
theorem B3237079 : Blo 838352 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B1893671 : Blo 838352 1893671 := bstep (se 1 (by rfl) ⟨1420253, by rfl⟩ : syracuseStep 1893671 = 2840507) B2840507
theorem B943483 : Blo 838352 943483 := bstep (se 1 (by rfl) ⟨707612, by rfl⟩ : syracuseStep 943483 = 1415225) B1415225
theorem B2123131 : Blo 838352 2123131 := bstep (se 1 (by rfl) ⟨1592348, by rfl⟩ : syracuseStep 2123131 = 3184697) B3184697
theorem B36922825 : Blo 838352 36922825 := bstep (se 2 (by rfl) ⟨13846059, by rfl⟩ : syracuseStep 36922825 = 27692119) B27692119
theorem B1894049 : Blo 838352 1894049 := bstep (se 2 (by rfl) ⟨710268, by rfl⟩ : syracuseStep 1894049 = 1420537) B1420537
theorem B2123567 : Blo 838352 2123567 := bstep (se 1 (by rfl) ⟨1592675, by rfl⟩ : syracuseStep 2123567 = 3185351) B3185351
theorem B943951 : Blo 838352 943951 := bstep (se 1 (by rfl) ⟨707963, by rfl⟩ : syracuseStep 943951 = 1415927) B1415927
theorem B9070481 : Blo 838352 9070481 := bstep (se 2 (by rfl) ⟨3401430, by rfl⟩ : syracuseStep 9070481 = 6802861) B6802861
theorem B1894409 : Blo 838352 1894409 := bstep (se 2 (by rfl) ⟨710403, by rfl⟩ : syracuseStep 1894409 = 1420807) B1420807
theorem B944347 : Blo 838352 944347 := bstep (se 1 (by rfl) ⟨708260, by rfl⟩ : syracuseStep 944347 = 1416521) B1416521
theorem B13297955 : Blo 838352 13297955 := bstep (se 1 (by rfl) ⟨9973466, by rfl⟩ : syracuseStep 13297955 = 19946933) B19946933
theorem B4254119 : Blo 838352 4254119 := bstep (se 1 (by rfl) ⟨3190589, by rfl⟩ : syracuseStep 4254119 = 6381179) B6381179
theorem B1796519 : Blo 838352 1796519 := bstep (se 1 (by rfl) ⟨1347389, by rfl⟩ : syracuseStep 1796519 = 2694779) B2694779
theorem B1894823 : Blo 838352 1894823 := bstep (se 1 (by rfl) ⟨1421117, by rfl⟩ : syracuseStep 1894823 = 2842235) B2842235
theorem B2124215 : Blo 838352 2124215 := bstep (se 1 (by rfl) ⟨1593161, by rfl⟩ : syracuseStep 2124215 = 3186323) B3186323
theorem B1010119 : Blo 838352 1010119 := bstep (se 1 (by rfl) ⟨757589, by rfl⟩ : syracuseStep 1010119 = 1515179) B1515179
theorem B944635 : Blo 838352 944635 := bstep (se 1 (by rfl) ⟨708476, by rfl⟩ : syracuseStep 944635 = 1416953) B1416953
theorem B1894931 : Blo 838352 1894931 := bstep (se 1 (by rfl) ⟨1421198, by rfl⟩ : syracuseStep 1894931 = 2842397) B2842397
theorem B4254281 : Blo 838352 4254281 := bstep (se 2 (by rfl) ⟨1595355, by rfl⟩ : syracuseStep 4254281 = 3190711) B3190711
theorem B1796681 : Blo 838352 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B1894985 : Blo 838352 1894985 := bstep (se 2 (by rfl) ⟨710619, by rfl⟩ : syracuseStep 1894985 = 1421239) B1421239
theorem B944815 : Blo 838352 944815 := bstep (se 1 (by rfl) ⟨708611, by rfl⟩ : syracuseStep 944815 = 1417223) B1417223
theorem B2878199 : Blo 838352 2878199 := bstep (se 1 (by rfl) ⟨2158649, by rfl⟩ : syracuseStep 2878199 = 4317299) B4317299
theorem B945103 : Blo 838352 945103 := bstep (se 1 (by rfl) ⟨708827, by rfl⟩ : syracuseStep 945103 = 1417655) B1417655
theorem B7171037 : Blo 838352 7171037 := bstep (se 3 (by rfl) ⟨1344569, by rfl⟩ : syracuseStep 7171037 = 2689139) B2689139
theorem B6810911 : Blo 838352 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B1797407 : Blo 838352 1797407 := bstep (se 1 (by rfl) ⟨1348055, by rfl⟩ : syracuseStep 1797407 = 2696111) B2696111
theorem B945499 : Blo 838352 945499 := bstep (se 1 (by rfl) ⟨709124, by rfl⟩ : syracuseStep 945499 = 1418249) B1418249
theorem B2125217 : Blo 838352 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B945607 : Blo 838352 945607 := bstep (se 1 (by rfl) ⟨709205, by rfl⟩ : syracuseStep 945607 = 1418411) B1418411
theorem B2551391 : Blo 838352 2551391 := bstep (se 1 (by rfl) ⟨1913543, by rfl⟩ : syracuseStep 2551391 = 3827087) B3827087
theorem B945967 : Blo 838352 945967 := bstep (se 1 (by rfl) ⟨709475, by rfl⟩ : syracuseStep 945967 = 1418951) B1418951
theorem B2125673 : Blo 838352 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B946075 : Blo 838352 946075 := bstep (se 1 (by rfl) ⟨709556, by rfl⟩ : syracuseStep 946075 = 1419113) B1419113
theorem B4780235 : Blo 838352 4780235 := bstep (se 1 (by rfl) ⟨3585176, by rfl⟩ : syracuseStep 4780235 = 7170353) B7170353
theorem B946471 : Blo 838352 946471 := bstep (se 1 (by rfl) ⟨709853, by rfl⟩ : syracuseStep 946471 = 1419707) B1419707
theorem B946543 : Blo 838352 946543 := bstep (se 1 (by rfl) ⟨709907, by rfl⟩ : syracuseStep 946543 = 1419815) B1419815
theorem B4256225 : Blo 838352 4256225 := bstep (se 2 (by rfl) ⟨1596084, by rfl⟩ : syracuseStep 4256225 = 3192169) B3192169
theorem B946759 : Blo 838352 946759 := bstep (se 1 (by rfl) ⟨710069, by rfl⟩ : syracuseStep 946759 = 1420139) B1420139
theorem B3634301 : Blo 838352 3634301 := bstep (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) B1362863
theorem B8058001 : Blo 838352 8058001 := bstep (se 2 (by rfl) ⟨3021750, by rfl⟩ : syracuseStep 8058001 = 6043501) B6043501
theorem B36369809 : Blo 838352 36369809 := bstep (se 2 (by rfl) ⟨13638678, by rfl⟩ : syracuseStep 36369809 = 27277357) B27277357
theorem B947623 : Blo 838352 947623 := bstep (se 1 (by rfl) ⟨710717, by rfl⟩ : syracuseStep 947623 = 1421435) B1421435
theorem B2127455 : Blo 838352 2127455 := bstep (se 1 (by rfl) ⟨1595591, by rfl⟩ : syracuseStep 2127455 = 3191183) B3191183
theorem B8058959 : Blo 838352 8058959 := bstep (se 1 (by rfl) ⟨6044219, by rfl⟩ : syracuseStep 8058959 = 12088439) B12088439
theorem B2128153 : Blo 838352 2128153 := bstep (se 2 (by rfl) ⟨798057, by rfl⟩ : syracuseStep 2128153 = 1596115) B1596115
theorem B2128295 : Blo 838352 2128295 := bstep (se 1 (by rfl) ⟨1596221, by rfl⟩ : syracuseStep 2128295 = 3192443) B3192443
theorem B15366581 : Blo 838352 15366581 := bstep (se 5 (by rfl) ⟨720308, by rfl⟩ : syracuseStep 15366581 = 1440617) B1440617
theorem B1276487 : Blo 838352 1276487 := bstep (se 1 (by rfl) ⟨957365, by rfl⟩ : syracuseStep 1276487 = 1914731) B1914731
theorem B2128457 : Blo 838352 2128457 := bstep (se 2 (by rfl) ⟨798171, by rfl⟩ : syracuseStep 2128457 = 1596343) B1596343
theorem B4258493 : Blo 838352 4258493 := bstep (se 3 (by rfl) ⟨798467, by rfl⟩ : syracuseStep 4258493 = 1596935) B1596935
theorem B4553495 : Blo 838352 4553495 := bstep (se 1 (by rfl) ⟨3415121, by rfl⟩ : syracuseStep 4553495 = 6830243) B6830243
theorem B9567395 : Blo 838352 9567395 := bstep (se 1 (by rfl) ⟨7175546, by rfl⟩ : syracuseStep 9567395 = 14351093) B14351093
theorem B1343071 : Blo 838352 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B2391713 : Blo 838352 2391713 := bstep (se 2 (by rfl) ⟨896892, by rfl⟩ : syracuseStep 2391713 = 1793785) B1793785
theorem B4030249 : Blo 838352 4030249 := bstep (se 2 (by rfl) ⟨1511343, by rfl⟩ : syracuseStep 4030249 = 3022687) B3022687
theorem B18416177 : Blo 838352 18416177 := bstep (se 2 (by rfl) ⟨6906066, by rfl⟩ : syracuseStep 18416177 = 13812133) B13812133
theorem B8192609 : Blo 838352 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B14582369 : Blo 838352 14582369 := bstep (se 2 (by rfl) ⟨5468388, by rfl⟩ : syracuseStep 14582369 = 10936777) B10936777
theorem B10781363 : Blo 838352 10781363 := bstep (se 1 (by rfl) ⟨8086022, by rfl⟩ : syracuseStep 10781363 = 16172045) B16172045
theorem B2392841 : Blo 838352 2392841 := bstep (se 2 (by rfl) ⟨897315, by rfl⟩ : syracuseStep 2392841 = 1794631) B1794631
theorem B2687755 : Blo 838352 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B1278761 : Blo 838352 1278761 := bstep (se 2 (by rfl) ⟨479535, by rfl⟩ : syracuseStep 1278761 = 959071) B959071
theorem B2130745 : Blo 838352 2130745 := bstep (se 2 (by rfl) ⟨799029, by rfl⟩ : syracuseStep 2130745 = 1598059) B1598059
theorem B4260923 : Blo 838352 4260923 := bstep (se 1 (by rfl) ⟨3195692, by rfl⟩ : syracuseStep 4260923 = 6391385) B6391385
theorem B2131049 : Blo 838352 2131049 := bstep (se 2 (by rfl) ⟨799143, by rfl⟩ : syracuseStep 2131049 = 1598287) B1598287
theorem B4261085 : Blo 838352 4261085 := bstep (se 3 (by rfl) ⟨798953, by rfl⟩ : syracuseStep 4261085 = 1597907) B1597907
theorem B1705387 : Blo 838352 1705387 := bstep (se 1 (by rfl) ⟨1279040, by rfl⟩ : syracuseStep 1705387 = 2558081) B2558081
theorem B12125807 : Blo 838352 12125807 := bstep (se 1 (by rfl) ⟨9094355, by rfl⟩ : syracuseStep 12125807 = 18188711) B18188711
theorem B2590471 : Blo 838352 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B10749995 : Blo 838352 10749995 := bstep (se 1 (by rfl) ⟨8062496, by rfl⟩ : syracuseStep 10749995 = 16124993) B16124993
theorem B2132183 : Blo 838352 2132183 := bstep (se 1 (by rfl) ⟨1599137, by rfl⟩ : syracuseStep 2132183 = 3198275) B3198275
theorem B2132203 : Blo 838352 2132203 := bstep (se 1 (by rfl) ⟨1599152, by rfl⟩ : syracuseStep 2132203 = 3198305) B3198305
theorem B4786523 : Blo 838352 4786523 := bstep (se 1 (by rfl) ⟨3589892, by rfl⟩ : syracuseStep 4786523 = 7179785) B7179785
theorem B1346825 : Blo 838352 1346825 := bstep (se 2 (by rfl) ⟨505059, by rfl⟩ : syracuseStep 1346825 = 1010119) B1010119
theorem B4787707 : Blo 838352 4787707 := bstep (se 1 (by rfl) ⟨3590780, by rfl⟩ : syracuseStep 4787707 = 7181561) B7181561
theorem B10784339 : Blo 838352 10784339 := bstep (se 1 (by rfl) ⟨8088254, by rfl⟩ : syracuseStep 10784339 = 16176509) B16176509
theorem B1380167 : Blo 838352 1380167 := bstep (se 1 (by rfl) ⟨1035125, by rfl⟩ : syracuseStep 1380167 = 2070251) B2070251
theorem B2690921 : Blo 838352 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B1348331 : Blo 838352 1348331 := bstep (se 1 (by rfl) ⟨1011248, by rfl⟩ : syracuseStep 1348331 = 2022497) B2022497
theorem B3183421 : Blo 838352 3183421 := bstep (se 3 (by rfl) ⟨596891, by rfl⟩ : syracuseStep 3183421 = 1193783) B1193783
theorem B12424337 : Blo 838352 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B19928357 : Blo 838352 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B4789691 : Blo 838352 4789691 := bstep (se 1 (by rfl) ⟨3592268, by rfl⟩ : syracuseStep 4789691 = 7184537) B7184537
theorem B4101803 : Blo 838352 4101803 := bstep (se 1 (by rfl) ⟨3076352, by rfl⟩ : syracuseStep 4101803 = 6152705) B6152705
theorem B1414975 : Blo 838352 1414975 := bstep (se 1 (by rfl) ⟨1061231, by rfl⟩ : syracuseStep 1414975 = 2122463) B2122463
theorem B1415711 : Blo 838352 1415711 := bstep (se 1 (by rfl) ⟨1061783, by rfl⟩ : syracuseStep 1415711 = 2123567) B2123567
theorem B1415785 : Blo 838352 1415785 := bstep (se 2 (by rfl) ⟨530919, by rfl⟩ : syracuseStep 1415785 = 1061839) B1061839
theorem B3414665 : Blo 838352 3414665 := bstep (se 2 (by rfl) ⟨1280499, by rfl⟩ : syracuseStep 3414665 = 2560999) B2560999
theorem B4791149 : Blo 838352 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B1416143 : Blo 838352 1416143 := bstep (se 1 (by rfl) ⟨1062107, by rfl⟩ : syracuseStep 1416143 = 2124215) B2124215
theorem B3284363 : Blo 838352 3284363 := bstep (se 1 (by rfl) ⟨2463272, by rfl⟩ : syracuseStep 3284363 = 4926545) B4926545
theorem B1416811 : Blo 838352 1416811 := bstep (se 1 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 1416811 = 2125217) B2125217
theorem B1417081 : Blo 838352 1417081 := bstep (se 2 (by rfl) ⟨531405, by rfl⟩ : syracuseStep 1417081 = 1062811) B1062811
theorem B1417115 : Blo 838352 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B3186823 : Blo 838352 3186823 := bstep (se 1 (by rfl) ⟨2390117, by rfl⟩ : syracuseStep 3186823 = 4780235) B4780235
theorem B4792607 : Blo 838352 4792607 := bstep (se 1 (by rfl) ⟨3594455, by rfl⟩ : syracuseStep 4792607 = 7188911) B7188911
theorem B2695675 : Blo 838352 2695675 := bstep (se 1 (by rfl) ⟨2021756, by rfl⟩ : syracuseStep 2695675 = 4043513) B4043513
theorem B3187309 : Blo 838352 3187309 := bstep (se 3 (by rfl) ⟨597620, by rfl⟩ : syracuseStep 3187309 = 1195241) B1195241
theorem B11477753 : Blo 838352 11477753 := bstep (se 2 (by rfl) ⟨4304157, by rfl⟩ : syracuseStep 11477753 = 8608315) B8608315
theorem B10757123 : Blo 838352 10757123 := bstep (se 1 (by rfl) ⟨8067842, by rfl⟩ : syracuseStep 10757123 = 16135685) B16135685
theorem B1418303 : Blo 838352 1418303 := bstep (se 1 (by rfl) ⟨1063727, by rfl⟩ : syracuseStep 1418303 = 2127455) B2127455
theorem B11478515 : Blo 838352 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B1418863 : Blo 838352 1418863 := bstep (se 1 (by rfl) ⟨1064147, by rfl⟩ : syracuseStep 1418863 = 2128295) B2128295
theorem B1418971 : Blo 838352 1418971 := bstep (se 1 (by rfl) ⟨1064228, by rfl⟩ : syracuseStep 1418971 = 2128457) B2128457
theorem B4041667 : Blo 838352 4041667 := bstep (se 1 (by rfl) ⟨3031250, by rfl⟩ : syracuseStep 4041667 = 6062501) B6062501
theorem B3189739 : Blo 838352 3189739 := bstep (se 1 (by rfl) ⟨2392304, by rfl⟩ : syracuseStep 3189739 = 4784609) B4784609
theorem B1420267 : Blo 838352 1420267 := bstep (se 1 (by rfl) ⟨1065200, by rfl⟩ : syracuseStep 1420267 = 2130401) B2130401
theorem B15313967 : Blo 838352 15313967 := bstep (se 1 (by rfl) ⟨11485475, by rfl⟩ : syracuseStep 15313967 = 22970951) B22970951
theorem B1420409 : Blo 838352 1420409 := bstep (se 2 (by rfl) ⟨532653, by rfl⟩ : syracuseStep 1420409 = 1065307) B1065307
theorem B2829545 : Blo 838352 2829545 := bstep (se 2 (by rfl) ⟨1061079, by rfl⟩ : syracuseStep 2829545 = 2122159) B2122159
theorem B8072459 : Blo 838352 8072459 := bstep (se 1 (by rfl) ⟨6054344, by rfl⟩ : syracuseStep 8072459 = 12108689) B12108689
theorem B2829815 : Blo 838352 2829815 := bstep (se 1 (by rfl) ⟨2122361, by rfl⟩ : syracuseStep 2829815 = 4244723) B4244723
theorem B5385761 : Blo 838352 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B17018909 : Blo 838352 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B1061095 : Blo 838352 1061095 := bstep (se 1 (by rfl) ⟨795821, by rfl⟩ : syracuseStep 1061095 = 1591643) B1591643
theorem B1257935 : Blo 838352 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B1257977 : Blo 838352 1257977 := bstep (se 2 (by rfl) ⟨471741, by rfl⟩ : syracuseStep 1257977 = 943483) B943483
theorem B2830841 : Blo 838352 2830841 := bstep (se 2 (by rfl) ⟨1061565, by rfl⟩ : syracuseStep 2830841 = 2123131) B2123131
theorem B5386763 : Blo 838352 5386763 := bstep (se 1 (by rfl) ⟨4040072, by rfl⟩ : syracuseStep 5386763 = 8080145) B8080145
theorem B1258079 : Blo 838352 1258079 := bstep (se 1 (by rfl) ⟨943559, by rfl⟩ : syracuseStep 1258079 = 1887119) B1887119
theorem B49230433 : Blo 838352 49230433 := bstep (se 2 (by rfl) ⟨18461412, by rfl⟩ : syracuseStep 49230433 = 36922825) B36922825
theorem B2831111 : Blo 838352 2831111 := bstep (se 1 (by rfl) ⟨2123333, by rfl⟩ : syracuseStep 2831111 = 4246667) B4246667
theorem B2831165 : Blo 838352 2831165 := bstep (se 3 (by rfl) ⟨530843, by rfl⟩ : syracuseStep 2831165 = 1061687) B1061687
theorem B1061743 : Blo 838352 1061743 := bstep (se 1 (by rfl) ⟨796307, by rfl⟩ : syracuseStep 1061743 = 1592615) B1592615
theorem B19379249 : Blo 838352 19379249 := bstep (se 2 (by rfl) ⟨7267218, by rfl⟩ : syracuseStep 19379249 = 14534437) B14534437
theorem B1258559 : Blo 838352 1258559 := bstep (se 1 (by rfl) ⟨943919, by rfl⟩ : syracuseStep 1258559 = 1887839) B1887839
theorem B1258601 : Blo 838352 1258601 := bstep (se 2 (by rfl) ⟨471975, by rfl⟩ : syracuseStep 1258601 = 943951) B943951
theorem B1258703 : Blo 838352 1258703 := bstep (se 1 (by rfl) ⟨944027, by rfl⟩ : syracuseStep 1258703 = 1888055) B1888055
theorem B1258907 : Blo 838352 1258907 := bstep (se 1 (by rfl) ⟨944180, by rfl⟩ : syracuseStep 1258907 = 1888361) B1888361
theorem B58963457 : Blo 838352 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B2274887 : Blo 838352 2274887 := bstep (se 1 (by rfl) ⟨1706165, by rfl⟩ : syracuseStep 2274887 = 3412331) B3412331
theorem B1259129 : Blo 838352 1259129 := bstep (se 2 (by rfl) ⟨472173, by rfl⟩ : syracuseStep 1259129 = 944347) B944347
theorem B1259231 : Blo 838352 1259231 := bstep (se 1 (by rfl) ⟨944423, by rfl⟩ : syracuseStep 1259231 = 1888847) B1888847
theorem B3028715 : Blo 838352 3028715 := bstep (se 1 (by rfl) ⟨2271536, by rfl⟩ : syracuseStep 3028715 = 4543073) B4543073
theorem B2832191 : Blo 838352 2832191 := bstep (se 1 (by rfl) ⟨2124143, by rfl⟩ : syracuseStep 2832191 = 4248287) B4248287
theorem B1259327 : Blo 838352 1259327 := bstep (se 1 (by rfl) ⟨944495, by rfl⟩ : syracuseStep 1259327 = 1888991) B1888991
theorem B3028799 : Blo 838352 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B1259495 : Blo 838352 1259495 := bstep (se 1 (by rfl) ⟨944621, by rfl⟩ : syracuseStep 1259495 = 1889243) B1889243
theorem B11483117 : Blo 838352 11483117 := bstep (se 3 (by rfl) ⟨2153084, by rfl⟩ : syracuseStep 11483117 = 4306169) B4306169
theorem B1193977 : Blo 838352 1193977 := bstep (se 2 (by rfl) ⟨447741, by rfl⟩ : syracuseStep 1193977 = 895483) B895483
theorem B1259513 : Blo 838352 1259513 := bstep (se 2 (by rfl) ⟨472317, by rfl⟩ : syracuseStep 1259513 = 944635) B944635
theorem B1259615 : Blo 838352 1259615 := bstep (se 1 (by rfl) ⟨944711, by rfl⟩ : syracuseStep 1259615 = 1889423) B1889423
theorem B3192929 : Blo 838352 3192929 := bstep (se 2 (by rfl) ⟨1197348, by rfl⟩ : syracuseStep 3192929 = 2394697) B2394697
theorem B1259675 : Blo 838352 1259675 := bstep (se 1 (by rfl) ⟨944756, by rfl⟩ : syracuseStep 1259675 = 1889513) B1889513
theorem B3029147 : Blo 838352 3029147 := bstep (se 1 (by rfl) ⟨2271860, by rfl⟩ : syracuseStep 3029147 = 4543721) B4543721
theorem B1259711 : Blo 838352 1259711 := bstep (se 1 (by rfl) ⟨944783, by rfl⟩ : syracuseStep 1259711 = 1889567) B1889567
theorem B1259753 : Blo 838352 1259753 := bstep (se 2 (by rfl) ⟨472407, by rfl⟩ : syracuseStep 1259753 = 944815) B944815
theorem B7649579 : Blo 838352 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B1260059 : Blo 838352 1260059 := bstep (se 1 (by rfl) ⟨945044, by rfl⟩ : syracuseStep 1260059 = 1890089) B1890089
theorem B1260137 : Blo 838352 1260137 := bstep (se 2 (by rfl) ⟨472551, by rfl⟩ : syracuseStep 1260137 = 945103) B945103
theorem B1915807 : Blo 838352 1915807 := bstep (se 1 (by rfl) ⟨1436855, by rfl⟩ : syracuseStep 1915807 = 2873711) B2873711
theorem B2767817 : Blo 838352 2767817 := bstep (se 2 (by rfl) ⟨1037931, by rfl⟩ : syracuseStep 2767817 = 2075863) B2075863
theorem B1260665 : Blo 838352 1260665 := bstep (se 2 (by rfl) ⟨472749, by rfl⟩ : syracuseStep 1260665 = 945499) B945499
theorem B1260767 : Blo 838352 1260767 := bstep (se 1 (by rfl) ⟨945575, by rfl⟩ : syracuseStep 1260767 = 1891151) B1891151
theorem B1260809 : Blo 838352 1260809 := bstep (se 2 (by rfl) ⟨472803, by rfl⟩ : syracuseStep 1260809 = 945607) B945607
theorem B2833703 : Blo 838352 2833703 := bstep (se 1 (by rfl) ⟨2125277, by rfl⟩ : syracuseStep 2833703 = 4250555) B4250555
theorem B1260911 : Blo 838352 1260911 := bstep (se 1 (by rfl) ⟨945683, by rfl⟩ : syracuseStep 1260911 = 1891367) B1891367
theorem B1261031 : Blo 838352 1261031 := bstep (se 1 (by rfl) ⟨945773, by rfl⟩ : syracuseStep 1261031 = 1891547) B1891547
theorem B1261163 : Blo 838352 1261163 := bstep (se 1 (by rfl) ⟨945872, by rfl⟩ : syracuseStep 1261163 = 1891745) B1891745
theorem B1261289 : Blo 838352 1261289 := bstep (se 2 (by rfl) ⟨472983, by rfl⟩ : syracuseStep 1261289 = 945967) B945967
theorem B24199019 : Blo 838352 24199019 := bstep (se 1 (by rfl) ⟨18149264, by rfl⟩ : syracuseStep 24199019 = 36298529) B36298529
theorem B1261433 : Blo 838352 1261433 := bstep (se 2 (by rfl) ⟨473037, by rfl⟩ : syracuseStep 1261433 = 946075) B946075
theorem B1261535 : Blo 838352 1261535 := bstep (se 1 (by rfl) ⟨946151, by rfl⟩ : syracuseStep 1261535 = 1892303) B1892303
theorem B1064927 : Blo 838352 1064927 := bstep (se 1 (by rfl) ⟨798695, by rfl⟩ : syracuseStep 1064927 = 1597391) B1597391
theorem B2834567 : Blo 838352 2834567 := bstep (se 1 (by rfl) ⟨2125925, by rfl⟩ : syracuseStep 2834567 = 4251851) B4251851
theorem B1261787 : Blo 838352 1261787 := bstep (se 1 (by rfl) ⟨946340, by rfl⟩ : syracuseStep 1261787 = 1892681) B1892681
theorem B1261799 : Blo 838352 1261799 := bstep (se 1 (by rfl) ⟨946349, by rfl⟩ : syracuseStep 1261799 = 1892699) B1892699
theorem B1261961 : Blo 838352 1261961 := bstep (se 2 (by rfl) ⟨473235, by rfl⟩ : syracuseStep 1261961 = 946471) B946471
theorem B1262057 : Blo 838352 1262057 := bstep (se 2 (by rfl) ⟨473271, by rfl⟩ : syracuseStep 1262057 = 946543) B946543
theorem B4538875 : Blo 838352 4538875 := bstep (se 1 (by rfl) ⟨3404156, by rfl⟩ : syracuseStep 4538875 = 6808313) B6808313
theorem B5390887 : Blo 838352 5390887 := bstep (se 1 (by rfl) ⟨4043165, by rfl⟩ : syracuseStep 5390887 = 8086331) B8086331
theorem B6046271 : Blo 838352 6046271 := bstep (se 1 (by rfl) ⟨4534703, by rfl⟩ : syracuseStep 6046271 = 9069407) B9069407
theorem B1262183 : Blo 838352 1262183 := bstep (se 1 (by rfl) ⟨946637, by rfl⟩ : syracuseStep 1262183 = 1893275) B1893275
theorem B1065575 : Blo 838352 1065575 := bstep (se 1 (by rfl) ⟨799181, by rfl⟩ : syracuseStep 1065575 = 1598363) B1598363
theorem B4309699 : Blo 838352 4309699 := bstep (se 1 (by rfl) ⟨3232274, by rfl⟩ : syracuseStep 4309699 = 6464549) B6464549
theorem B1262315 : Blo 838352 1262315 := bstep (se 1 (by rfl) ⟨946736, by rfl⟩ : syracuseStep 1262315 = 1893473) B1893473
theorem B1262345 : Blo 838352 1262345 := bstep (se 2 (by rfl) ⟨473379, by rfl⟩ : syracuseStep 1262345 = 946759) B946759
theorem B2016047 : Blo 838352 2016047 := bstep (se 1 (by rfl) ⟨1512035, by rfl⟩ : syracuseStep 2016047 = 3024071) B3024071
theorem B1262447 : Blo 838352 1262447 := bstep (se 1 (by rfl) ⟨946835, by rfl⟩ : syracuseStep 1262447 = 1893671) B1893671
theorem B1262699 : Blo 838352 1262699 := bstep (se 1 (by rfl) ⟨947024, by rfl⟩ : syracuseStep 1262699 = 1894049) B1894049
theorem B6046987 : Blo 838352 6046987 := bstep (se 1 (by rfl) ⟨4535240, by rfl⟩ : syracuseStep 6046987 = 9070481) B9070481
theorem B1262939 : Blo 838352 1262939 := bstep (se 1 (by rfl) ⟨947204, by rfl⟩ : syracuseStep 1262939 = 1894409) B1894409
theorem B2016683 : Blo 838352 2016683 := bstep (se 1 (by rfl) ⟨1512512, by rfl⟩ : syracuseStep 2016683 = 3025025) B3025025
theorem B3196331 : Blo 838352 3196331 := bstep (se 1 (by rfl) ⟨2397248, by rfl⟩ : syracuseStep 3196331 = 4794497) B4794497
theorem B2836079 : Blo 838352 2836079 := bstep (se 1 (by rfl) ⟨2127059, by rfl⟩ : syracuseStep 2836079 = 4254119) B4254119
theorem B1197679 : Blo 838352 1197679 := bstep (se 1 (by rfl) ⟨898259, by rfl⟩ : syracuseStep 1197679 = 1796519) B1796519
theorem B1263215 : Blo 838352 1263215 := bstep (se 1 (by rfl) ⟨947411, by rfl⟩ : syracuseStep 1263215 = 1894823) B1894823
theorem B1263287 : Blo 838352 1263287 := bstep (se 1 (by rfl) ⟨947465, by rfl⟩ : syracuseStep 1263287 = 1894931) B1894931
theorem B2836187 : Blo 838352 2836187 := bstep (se 1 (by rfl) ⟨2127140, by rfl⟩ : syracuseStep 2836187 = 4254281) B4254281
theorem B1263323 : Blo 838352 1263323 := bstep (se 1 (by rfl) ⟨947492, by rfl⟩ : syracuseStep 1263323 = 1894985) B1894985
theorem B1918799 : Blo 838352 1918799 := bstep (se 1 (by rfl) ⟨1439099, by rfl⟩ : syracuseStep 1918799 = 2878199) B2878199
theorem B12109661 : Blo 838352 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B1263497 : Blo 838352 1263497 := bstep (se 2 (by rfl) ⟨473811, by rfl⟩ : syracuseStep 1263497 = 947623) B947623
theorem B1886399 : Blo 838352 1886399 := bstep (se 1 (by rfl) ⟨1414799, by rfl⟩ : syracuseStep 1886399 = 2829599) B2829599
theorem B4245695 : Blo 838352 4245695 := bstep (se 1 (by rfl) ⟨3184271, by rfl⟩ : syracuseStep 4245695 = 6368543) B6368543
theorem B4540607 : Blo 838352 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B1198271 : Blo 838352 1198271 := bstep (se 1 (by rfl) ⟨898703, by rfl⟩ : syracuseStep 1198271 = 1797407) B1797407
theorem B838491 : Blo 838352 838491 := bstep (se 1 (by rfl) ⟨628868, by rfl⟩ : syracuseStep 838491 = 1257737) B1257737
theorem B838559 : Blo 838352 838559 := bstep (se 1 (by rfl) ⟨628919, by rfl⟩ : syracuseStep 838559 = 1257839) B1257839
theorem B2837483 : Blo 838352 2837483 := bstep (se 1 (by rfl) ⟨2128112, by rfl⟩ : syracuseStep 2837483 = 4256225) B4256225
theorem B2837537 : Blo 838352 2837537 := bstep (se 2 (by rfl) ⟨1064076, by rfl⟩ : syracuseStep 2837537 = 2128153) B2128153
theorem B838703 : Blo 838352 838703 := bstep (se 1 (by rfl) ⟨629027, by rfl⟩ : syracuseStep 838703 = 1258055) B1258055
theorem B838727 : Blo 838352 838727 := bstep (se 1 (by rfl) ⟨629045, by rfl⟩ : syracuseStep 838727 = 1258091) B1258091
theorem B1887353 : Blo 838352 1887353 := bstep (se 2 (by rfl) ⟨707757, by rfl⟩ : syracuseStep 1887353 = 1415515) B1415515
theorem B838879 : Blo 838352 838879 := bstep (se 1 (by rfl) ⟨629159, by rfl⟩ : syracuseStep 838879 = 1258319) B1258319
theorem B3591449 : Blo 838352 3591449 := bstep (se 2 (by rfl) ⟨1346793, by rfl⟩ : syracuseStep 3591449 = 2693587) B2693587
theorem B5098889 : Blo 838352 5098889 := bstep (se 2 (by rfl) ⟨1912083, by rfl⟩ : syracuseStep 5098889 = 3824167) B3824167
theorem B16174505 : Blo 838352 16174505 := bstep (se 2 (by rfl) ⟨6065439, by rfl⟩ : syracuseStep 16174505 = 12130879) B12130879
theorem B839143 : Blo 838352 839143 := bstep (se 1 (by rfl) ⟨629357, by rfl⟩ : syracuseStep 839143 = 1258715) B1258715
theorem B2018807 : Blo 838352 2018807 := bstep (se 1 (by rfl) ⟨1514105, by rfl⟩ : syracuseStep 2018807 = 3028211) B3028211
theorem B839259 : Blo 838352 839259 := bstep (se 1 (by rfl) ⟨629444, by rfl⟩ : syracuseStep 839259 = 1258889) B1258889
theorem B1888019 : Blo 838352 1888019 := bstep (se 1 (by rfl) ⟨1416014, by rfl⟩ : syracuseStep 1888019 = 2832029) B2832029
theorem B839495 : Blo 838352 839495 := bstep (se 1 (by rfl) ⟨629621, by rfl⟩ : syracuseStep 839495 = 1259243) B1259243
theorem B839647 : Blo 838352 839647 := bstep (se 1 (by rfl) ⟨629735, by rfl⟩ : syracuseStep 839647 = 1259471) B1259471
theorem B1888379 : Blo 838352 1888379 := bstep (se 1 (by rfl) ⟨1416284, by rfl⟩ : syracuseStep 1888379 = 2832569) B2832569
theorem B839911 : Blo 838352 839911 := bstep (se 1 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 839911 = 1259867) B1259867
theorem B10244387 : Blo 838352 10244387 := bstep (se 1 (by rfl) ⟨7683290, by rfl⟩ : syracuseStep 10244387 = 15366581) B15366581
theorem B840063 : Blo 838352 840063 := bstep (se 1 (by rfl) ⟨630047, by rfl⟩ : syracuseStep 840063 = 1260095) B1260095
theorem B1888649 : Blo 838352 1888649 := bstep (se 2 (by rfl) ⟨708243, by rfl⟩ : syracuseStep 1888649 = 1416487) B1416487
theorem B14569901 : Blo 838352 14569901 := bstep (se 3 (by rfl) ⟨2731856, by rfl⟩ : syracuseStep 14569901 = 5463713) B5463713
theorem B58249651 : Blo 838352 58249651 := bstep (se 1 (by rfl) ⟨43687238, by rfl⟩ : syracuseStep 58249651 = 87374477) B87374477
theorem B840143 : Blo 838352 840143 := bstep (se 1 (by rfl) ⟨630107, by rfl⟩ : syracuseStep 840143 = 1260215) B1260215
theorem B2838995 : Blo 838352 2838995 := bstep (se 1 (by rfl) ⟨2129246, by rfl⟩ : syracuseStep 2838995 = 4258493) B4258493
theorem B3035663 : Blo 838352 3035663 := bstep (se 1 (by rfl) ⟨2276747, by rfl⟩ : syracuseStep 3035663 = 4553495) B4553495
theorem B840295 : Blo 838352 840295 := bstep (se 1 (by rfl) ⟨630221, by rfl⟩ : syracuseStep 840295 = 1260443) B1260443
theorem B5395193 : Blo 838352 5395193 := bstep (se 2 (by rfl) ⟨2023197, by rfl⟩ : syracuseStep 5395193 = 4046395) B4046395
theorem B6378263 : Blo 838352 6378263 := bstep (se 1 (by rfl) ⟨4783697, by rfl⟩ : syracuseStep 6378263 = 9567395) B9567395
theorem B1790761 : Blo 838352 1790761 := bstep (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) B1343071
theorem B840559 : Blo 838352 840559 := bstep (se 1 (by rfl) ⟨630419, by rfl⟩ : syracuseStep 840559 = 1260839) B1260839
theorem B4248449 : Blo 838352 4248449 := bstep (se 2 (by rfl) ⟨1593168, by rfl⟩ : syracuseStep 4248449 = 3186337) B3186337
theorem B840615 : Blo 838352 840615 := bstep (se 1 (by rfl) ⟨630461, by rfl⟩ : syracuseStep 840615 = 1260923) B1260923
theorem B840699 : Blo 838352 840699 := bstep (se 1 (by rfl) ⟨630524, by rfl⟩ : syracuseStep 840699 = 1261049) B1261049
theorem B840767 : Blo 838352 840767 := bstep (se 1 (by rfl) ⟨630575, by rfl⟩ : syracuseStep 840767 = 1261151) B1261151
theorem B1889387 : Blo 838352 1889387 := bstep (se 1 (by rfl) ⟨1417040, by rfl⟩ : syracuseStep 1889387 = 2834081) B2834081
theorem B1594475 : Blo 838352 1594475 := bstep (se 1 (by rfl) ⟨1195856, by rfl⟩ : syracuseStep 1594475 = 2391713) B2391713
theorem B840911 : Blo 838352 840911 := bstep (se 1 (by rfl) ⟨630683, by rfl⟩ : syracuseStep 840911 = 1261367) B1261367
theorem B4609399 : Blo 838352 4609399 := bstep (se 1 (by rfl) ⟨3457049, by rfl⟩ : syracuseStep 4609399 = 6914099) B6914099
theorem B1136027 : Blo 838352 1136027 := bstep (se 1 (by rfl) ⟨852020, by rfl⟩ : syracuseStep 1136027 = 1704041) B1704041
theorem B841115 : Blo 838352 841115 := bstep (se 1 (by rfl) ⟨630836, by rfl⟩ : syracuseStep 841115 = 1261673) B1261673
theorem B841327 : Blo 838352 841327 := bstep (se 1 (by rfl) ⟨630995, by rfl⟩ : syracuseStep 841327 = 1261991) B1261991
theorem B841383 : Blo 838352 841383 := bstep (se 1 (by rfl) ⟨631037, by rfl⟩ : syracuseStep 841383 = 1262075) B1262075
theorem B4249259 : Blo 838352 4249259 := bstep (se 1 (by rfl) ⟨3186944, by rfl⟩ : syracuseStep 4249259 = 6373889) B6373889
theorem B1889963 : Blo 838352 1889963 := bstep (se 1 (by rfl) ⟨1417472, by rfl⟩ : syracuseStep 1889963 = 2834945) B2834945
theorem B841467 : Blo 838352 841467 := bstep (se 1 (by rfl) ⟨631100, by rfl⟩ : syracuseStep 841467 = 1262201) B1262201
theorem B841503 : Blo 838352 841503 := bstep (se 1 (by rfl) ⟨631127, by rfl⟩ : syracuseStep 841503 = 1262255) B1262255
theorem B841535 : Blo 838352 841535 := bstep (se 1 (by rfl) ⟨631151, by rfl⟩ : syracuseStep 841535 = 1262303) B1262303
theorem B4249583 : Blo 838352 4249583 := bstep (se 1 (by rfl) ⟨3187187, by rfl⟩ : syracuseStep 4249583 = 6374375) B6374375
theorem B1890287 : Blo 838352 1890287 := bstep (se 1 (by rfl) ⟨1417715, by rfl⟩ : syracuseStep 1890287 = 2835431) B2835431
theorem B841711 : Blo 838352 841711 := bstep (se 1 (by rfl) ⟨631283, by rfl⟩ : syracuseStep 841711 = 1262567) B1262567
theorem B841883 : Blo 838352 841883 := bstep (se 1 (by rfl) ⟨631412, by rfl⟩ : syracuseStep 841883 = 1262825) B1262825
theorem B841919 : Blo 838352 841919 := bstep (se 1 (by rfl) ⟨631439, by rfl⟩ : syracuseStep 841919 = 1262879) B1262879
theorem B18208961 : Blo 838352 18208961 := bstep (se 2 (by rfl) ⟨6828360, by rfl⟩ : syracuseStep 18208961 = 13656721) B13656721
theorem B1890503 : Blo 838352 1890503 := bstep (se 1 (by rfl) ⟨1417877, by rfl⟩ : syracuseStep 1890503 = 2835755) B2835755
theorem B842031 : Blo 838352 842031 := bstep (se 1 (by rfl) ⟨631523, by rfl⟩ : syracuseStep 842031 = 1263047) B1263047
theorem B2840939 : Blo 838352 2840939 := bstep (se 1 (by rfl) ⟨2130704, by rfl⟩ : syracuseStep 2840939 = 4261409) B4261409
theorem B1890683 : Blo 838352 1890683 := bstep (se 1 (by rfl) ⟨1418012, by rfl⟩ : syracuseStep 1890683 = 2836025) B2836025
theorem B10934651 : Blo 838352 10934651 := bstep (se 1 (by rfl) ⟨8200988, by rfl⟩ : syracuseStep 10934651 = 16401977) B16401977
theorem B24205715 : Blo 838352 24205715 := bstep (se 1 (by rfl) ⟨18154286, by rfl⟩ : syracuseStep 24205715 = 36308573) B36308573
theorem B842267 : Blo 838352 842267 := bstep (se 1 (by rfl) ⟨631700, by rfl⟩ : syracuseStep 842267 = 1263401) B1263401
theorem B842271 : Blo 838352 842271 := bstep (se 1 (by rfl) ⟨631703, by rfl⟩ : syracuseStep 842271 = 1263407) B1263407
theorem B2841209 : Blo 838352 2841209 := bstep (se 2 (by rfl) ⟨1065453, by rfl⟩ : syracuseStep 2841209 = 2130907) B2130907
theorem B1890953 : Blo 838352 1890953 := bstep (se 2 (by rfl) ⟨709107, by rfl⟩ : syracuseStep 1890953 = 1418215) B1418215
theorem B4316105 : Blo 838352 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B2841641 : Blo 838352 2841641 := bstep (se 2 (by rfl) ⟨1065615, by rfl⟩ : syracuseStep 2841641 = 2131231) B2131231
theorem B1891511 : Blo 838352 1891511 := bstep (se 1 (by rfl) ⟨1418633, by rfl⟩ : syracuseStep 1891511 = 2837267) B2837267
theorem B2022583 : Blo 838352 2022583 := bstep (se 1 (by rfl) ⟨1516937, by rfl⟩ : syracuseStep 2022583 = 3033875) B3033875
theorem B4251041 : Blo 838352 4251041 := bstep (se 2 (by rfl) ⟨1594140, by rfl⟩ : syracuseStep 4251041 = 3188281) B3188281
theorem B1892087 : Blo 838352 1892087 := bstep (se 1 (by rfl) ⟨1419065, by rfl⟩ : syracuseStep 1892087 = 2838131) B2838131
theorem B1892267 : Blo 838352 1892267 := bstep (se 1 (by rfl) ⟨1419200, by rfl⟩ : syracuseStep 1892267 = 2838401) B2838401
theorem B3596507 : Blo 838352 3596507 := bstep (se 1 (by rfl) ⟨2697380, by rfl⟩ : syracuseStep 3596507 = 5394761) B5394761
theorem B10215683 : Blo 838352 10215683 := bstep (se 1 (by rfl) ⟨7661762, by rfl⟩ : syracuseStep 10215683 = 15323525) B15323525
theorem B9691469 : Blo 838352 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B141844853 : Blo 838352 141844853 := bstep (se 5 (by rfl) ⟨6648977, by rfl⟩ : syracuseStep 141844853 = 13297955) B13297955
theorem B4776317 : Blo 838352 4776317 := bstep (se 3 (by rfl) ⟨895559, by rfl⟩ : syracuseStep 4776317 = 1791119) B1791119
theorem B1892807 : Blo 838352 1892807 := bstep (se 1 (by rfl) ⟨1419605, by rfl⟩ : syracuseStep 1892807 = 2839211) B2839211
theorem B1893167 : Blo 838352 1893167 := bstep (se 1 (by rfl) ⟨1419875, by rfl⟩ : syracuseStep 1893167 = 2839751) B2839751
theorem B17523611 : Blo 838352 17523611 := bstep (se 1 (by rfl) ⟨13142708, by rfl⟩ : syracuseStep 17523611 = 26285417) B26285417
theorem B2123081 : Blo 838352 2123081 := bstep (se 2 (by rfl) ⟨796155, by rfl⟩ : syracuseStep 2123081 = 1592311) B1592311
theorem B560424491 : Blo 838352 560424491 := bstep (se 1 (by rfl) ⟨420318368, by rfl⟩ : syracuseStep 560424491 = 840636737) B840636737
theorem B4253471 : Blo 838352 4253471 := bstep (se 1 (by rfl) ⟨3190103, by rfl⟩ : syracuseStep 4253471 = 6380207) B6380207
theorem B1894175 : Blo 838352 1894175 := bstep (se 1 (by rfl) ⟨1420631, by rfl⟩ : syracuseStep 1894175 = 2841263) B2841263
theorem B2123617 : Blo 838352 2123617 := bstep (se 2 (by rfl) ⟨796356, by rfl⟩ : syracuseStep 2123617 = 1592713) B1592713
theorem B1795937 : Blo 838352 1795937 := bstep (se 2 (by rfl) ⟨673476, by rfl⟩ : syracuseStep 1795937 = 1346953) B1346953
theorem B34498457 : Blo 838352 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B1894391 : Blo 838352 1894391 := bstep (se 1 (by rfl) ⟨1420793, by rfl⟩ : syracuseStep 1894391 = 2841587) B2841587
theorem B6056045 : Blo 838352 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B1894751 : Blo 838352 1894751 := bstep (se 1 (by rfl) ⟨1421063, by rfl⟩ : syracuseStep 1894751 = 2842127) B2842127
theorem B944671 : Blo 838352 944671 := bstep (se 1 (by rfl) ⟨708503, by rfl⟩ : syracuseStep 944671 = 1417007) B1417007
theorem B4254767 : Blo 838352 4254767 := bstep (se 1 (by rfl) ⟨3191075, by rfl⟩ : syracuseStep 4254767 = 6382151) B6382151
theorem B2551657 : Blo 838352 2551657 := bstep (se 2 (by rfl) ⟨956871, by rfl⟩ : syracuseStep 2551657 = 1913743) B1913743
theorem B2125723 : Blo 838352 2125723 := bstep (se 1 (by rfl) ⟨1594292, by rfl⟩ : syracuseStep 2125723 = 3188585) B3188585
theorem B10744001 : Blo 838352 10744001 := bstep (se 2 (by rfl) ⟨4029000, by rfl⟩ : syracuseStep 10744001 = 8058001) B8058001
theorem B6058583 : Blo 838352 6058583 := bstep (se 1 (by rfl) ⟨4543937, by rfl⟩ : syracuseStep 6058583 = 9087875) B9087875
theorem B4780691 : Blo 838352 4780691 := bstep (se 1 (by rfl) ⟨3585518, by rfl⟩ : syracuseStep 4780691 = 7171037) B7171037
theorem B2388865 : Blo 838352 2388865 := bstep (se 2 (by rfl) ⟨895824, by rfl⟩ : syracuseStep 2388865 = 1791649) B1791649
theorem B2126857 : Blo 838352 2126857 := bstep (se 2 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 2126857 = 1595143) B1595143
theorem B1700927 : Blo 838352 1700927 := bstep (se 1 (by rfl) ⟨1275695, by rfl⟩ : syracuseStep 1700927 = 2551391) B2551391
theorem B947263 : Blo 838352 947263 := bstep (se 1 (by rfl) ⟨710447, by rfl⟩ : syracuseStep 947263 = 1420895) B1420895
theorem B947407 : Blo 838352 947407 := bstep (se 1 (by rfl) ⟨710555, by rfl⟩ : syracuseStep 947407 = 1421111) B1421111
theorem B24246539 : Blo 838352 24246539 := bstep (se 1 (by rfl) ⟨18184904, by rfl⟩ : syracuseStep 24246539 = 36369809) B36369809
theorem B3275117 : Blo 838352 3275117 := bstep (se 3 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 3275117 = 1228169) B1228169
theorem B5372639 : Blo 838352 5372639 := bstep (se 1 (by rfl) ⟨4029479, by rfl⟩ : syracuseStep 5372639 = 8058959) B8058959
theorem B850991 : Blo 838352 850991 := bstep (se 1 (by rfl) ⟨638243, by rfl⟩ : syracuseStep 850991 = 1276487) B1276487
theorem B1277435 : Blo 838352 1277435 := bstep (se 1 (by rfl) ⟨958076, by rfl⟩ : syracuseStep 1277435 = 1916153) B1916153
theorem B5373665 : Blo 838352 5373665 := bstep (se 2 (by rfl) ⟨2015124, by rfl⟩ : syracuseStep 5373665 = 4030249) B4030249
theorem B4030847 : Blo 838352 4030847 := bstep (se 1 (by rfl) ⟨3023135, by rfl⟩ : syracuseStep 4030847 = 6046271) B6046271
theorem B1344455 : Blo 838352 1344455 := bstep (se 1 (by rfl) ⟨1008341, by rfl⟩ : syracuseStep 1344455 = 2016683) B2016683
theorem B2130887 : Blo 838352 2130887 := bstep (se 1 (by rfl) ⟨1598165, by rfl⟩ : syracuseStep 2130887 = 3196331) B3196331
theorem B1279199 : Blo 838352 1279199 := bstep (se 1 (by rfl) ⟨959399, by rfl⟩ : syracuseStep 1279199 = 1918799) B1918799
theorem B8062649 : Blo 838352 8062649 := bstep (se 2 (by rfl) ⟨3023493, by rfl⟩ : syracuseStep 8062649 = 6046987) B6046987
theorem B3410029 : Blo 838352 3410029 := bstep (se 3 (by rfl) ⟨639380, by rfl⟩ : syracuseStep 3410029 = 1278761) B1278761
theorem B5376125 : Blo 838352 5376125 := bstep (se 3 (by rfl) ⟨1008023, by rfl⟩ : syracuseStep 5376125 = 2016047) B2016047
theorem B2394299 : Blo 838352 2394299 := bstep (se 1 (by rfl) ⟨1795724, by rfl⟩ : syracuseStep 2394299 = 3591449) B3591449
theorem B10783003 : Blo 838352 10783003 := bstep (se 1 (by rfl) ⟨8087252, by rfl⟩ : syracuseStep 10783003 = 16174505) B16174505
theorem B1345871 : Blo 838352 1345871 := bstep (se 1 (by rfl) ⟨1009403, by rfl⟩ : syracuseStep 1345871 = 2018807) B2018807
theorem B920111 : Blo 838352 920111 := bstep (se 1 (by rfl) ⟨690083, by rfl⟩ : syracuseStep 920111 = 1380167) B1380167
theorem B30609373 : Blo 838352 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B4789165 : Blo 838352 4789165 := bstep (se 3 (by rfl) ⟨897968, by rfl⟩ : syracuseStep 4789165 = 1795937) B1795937
theorem B2397671 : Blo 838352 2397671 := bstep (se 1 (by rfl) ⟨1798253, by rfl⟩ : syracuseStep 2397671 = 3596507) B3596507
theorem B6460979 : Blo 838352 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B3184211 : Blo 838352 3184211 := bstep (se 1 (by rfl) ⟨2388158, by rfl⟩ : syracuseStep 3184211 = 4776317) B4776317
theorem B1414793 : Blo 838352 1414793 := bstep (se 2 (by rfl) ⟨530547, by rfl⟩ : syracuseStep 1414793 = 1061095) B1061095
theorem B77666201 : Blo 838352 77666201 := bstep (se 2 (by rfl) ⟨29124825, by rfl⟩ : syracuseStep 77666201 = 58249651) B58249651
theorem B65640577 : Blo 838352 65640577 := bstep (se 2 (by rfl) ⟨24615216, by rfl⟩ : syracuseStep 65640577 = 49230433) B49230433
theorem B1415387 : Blo 838352 1415387 := bstep (se 1 (by rfl) ⟨1061540, by rfl⟩ : syracuseStep 1415387 = 2123081) B2123081
theorem B1415657 : Blo 838352 1415657 := bstep (se 2 (by rfl) ⟨530871, by rfl⟩ : syracuseStep 1415657 = 1061743) B1061743
theorem B3185153 : Blo 838352 3185153 := bstep (se 2 (by rfl) ⟨1194432, by rfl⟩ : syracuseStep 3185153 = 2388865) B2388865
theorem B4037363 : Blo 838352 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B5381639 : Blo 838352 5381639 := bstep (se 1 (by rfl) ⟨4036229, by rfl⟩ : syracuseStep 5381639 = 8072459) B8072459
theorem B7380845 : Blo 838352 7380845 := bstep (se 3 (by rfl) ⟨1383908, by rfl⟩ : syracuseStep 7380845 = 2767817) B2767817
theorem B11509613 : Blo 838352 11509613 := bstep (se 3 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 11509613 = 4316105) B4316105
theorem B11345939 : Blo 838352 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B2269309 : Blo 838352 2269309 := bstep (se 3 (by rfl) ⟨425495, by rfl⟩ : syracuseStep 2269309 = 850991) B850991
theorem B4039055 : Blo 838352 4039055 := bstep (se 1 (by rfl) ⟨3029291, by rfl⟩ : syracuseStep 4039055 = 6058583) B6058583
theorem B3187127 : Blo 838352 3187127 := bstep (se 1 (by rfl) ⟨2390345, by rfl⟩ : syracuseStep 3187127 = 4780691) B4780691
theorem B12919499 : Blo 838352 12919499 := bstep (se 1 (by rfl) ⟨9689624, by rfl⟩ : syracuseStep 12919499 = 19379249) B19379249
theorem B1516591 : Blo 838352 1516591 := bstep (se 1 (by rfl) ⟨1137443, by rfl⟩ : syracuseStep 1516591 = 2274887) B2274887
theorem B16164359 : Blo 838352 16164359 := bstep (se 1 (by rfl) ⟨12123269, by rfl⟩ : syracuseStep 16164359 = 24246539) B24246539
theorem B2696777 : Blo 838352 2696777 := bstep (se 2 (by rfl) ⟨1011291, by rfl⟩ : syracuseStep 2696777 = 2022583) B2022583
theorem B3581759 : Blo 838352 3581759 := bstep (se 1 (by rfl) ⟨2686319, by rfl⟩ : syracuseStep 3581759 = 5372639) B5372639
theorem B3582443 : Blo 838352 3582443 := bstep (se 1 (by rfl) ⟨2686832, by rfl⟩ : syracuseStep 3582443 = 5373665) B5373665
theorem B16132679 : Blo 838352 16132679 := bstep (se 1 (by rfl) ⟨12099509, by rfl⟩ : syracuseStep 16132679 = 24199019) B24199019
theorem B7187575 : Blo 838352 7187575 := bstep (se 1 (by rfl) ⟨5390681, by rfl⟩ : syracuseStep 7187575 = 10781363) B10781363
theorem B7187849 : Blo 838352 7187849 := bstep (se 2 (by rfl) ⟨2695443, by rfl⟩ : syracuseStep 7187849 = 5390887) B5390887
theorem B1420699 : Blo 838352 1420699 := bstep (se 1 (by rfl) ⟨1065524, by rfl⟩ : syracuseStep 1420699 = 2131049) B2131049
theorem B5746265 : Blo 838352 5746265 := bstep (se 2 (by rfl) ⟨2154849, by rfl⟩ : syracuseStep 5746265 = 4309699) B4309699
theorem B3583673 : Blo 838352 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B8073107 : Blo 838352 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B1257599 : Blo 838352 1257599 := bstep (se 1 (by rfl) ⟨943199, by rfl⟩ : syracuseStep 1257599 = 1886399) B1886399
theorem B2830463 : Blo 838352 2830463 := bstep (se 1 (by rfl) ⟨2122847, by rfl⟩ : syracuseStep 2830463 = 4245695) B4245695
theorem B3027071 : Blo 838352 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B1421455 : Blo 838352 1421455 := bstep (se 1 (by rfl) ⟨1066091, by rfl⟩ : syracuseStep 1421455 = 2132183) B2132183
theorem B3191015 : Blo 838352 3191015 := bstep (se 1 (by rfl) ⟨2393261, by rfl⟩ : syracuseStep 3191015 = 4786523) B4786523
theorem B2273849 : Blo 838352 2273849 := bstep (se 2 (by rfl) ⟨852693, by rfl⟩ : syracuseStep 2273849 = 1705387) B1705387
theorem B1258235 : Blo 838352 1258235 := bstep (se 1 (by rfl) ⟨943676, by rfl⟩ : syracuseStep 1258235 = 1887353) B1887353
theorem B3453961 : Blo 838352 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B7189559 : Blo 838352 7189559 := bstep (se 1 (by rfl) ⟨5392169, by rfl⟩ : syracuseStep 7189559 = 10784339) B10784339
theorem B2831489 : Blo 838352 2831489 := bstep (se 2 (by rfl) ⟨1061808, by rfl⟩ : syracuseStep 2831489 = 2123617) B2123617
theorem B1258679 : Blo 838352 1258679 := bstep (se 1 (by rfl) ⟨944009, by rfl⟩ : syracuseStep 1258679 = 1888019) B1888019
theorem B1258919 : Blo 838352 1258919 := bstep (se 1 (by rfl) ⟨944189, by rfl⟩ : syracuseStep 1258919 = 1888379) B1888379
theorem B6829591 : Blo 838352 6829591 := bstep (se 1 (by rfl) ⟨5122193, by rfl⟩ : syracuseStep 6829591 = 10244387) B10244387
theorem B1259099 : Blo 838352 1259099 := bstep (se 1 (by rfl) ⟨944324, by rfl⟩ : syracuseStep 1259099 = 1888649) B1888649
theorem B9713267 : Blo 838352 9713267 := bstep (se 1 (by rfl) ⟨7284950, by rfl⟩ : syracuseStep 9713267 = 14569901) B14569901
theorem B2832299 : Blo 838352 2832299 := bstep (se 1 (by rfl) ⟨2124224, by rfl⟩ : syracuseStep 2832299 = 4248449) B4248449
theorem B1259561 : Blo 838352 1259561 := bstep (se 2 (by rfl) ⟨472335, by rfl⟩ : syracuseStep 1259561 = 944671) B944671
theorem B1259591 : Blo 838352 1259591 := bstep (se 1 (by rfl) ⟨944693, by rfl⟩ : syracuseStep 1259591 = 1889387) B1889387
theorem B1062983 : Blo 838352 1062983 := bstep (se 1 (by rfl) ⟨797237, by rfl⟩ : syracuseStep 1062983 = 1594475) B1594475
theorem B13285571 : Blo 838352 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B3193127 : Blo 838352 3193127 := bstep (se 1 (by rfl) ⟨2394845, by rfl⟩ : syracuseStep 3193127 = 4789691) B4789691
theorem B3029405 : Blo 838352 3029405 := bstep (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) B1136027
theorem B2832839 : Blo 838352 2832839 := bstep (se 1 (by rfl) ⟨2124629, by rfl⟩ : syracuseStep 2832839 = 4249259) B4249259
theorem B1259975 : Blo 838352 1259975 := bstep (se 1 (by rfl) ⟨944981, by rfl⟩ : syracuseStep 1259975 = 1889963) B1889963
theorem B2734535 : Blo 838352 2734535 := bstep (se 1 (by rfl) ⟨2050901, by rfl⟩ : syracuseStep 2734535 = 4101803) B4101803
theorem B5388889 : Blo 838352 5388889 := bstep (se 2 (by rfl) ⟨2020833, by rfl⟩ : syracuseStep 5388889 = 4041667) B4041667
theorem B2833055 : Blo 838352 2833055 := bstep (se 1 (by rfl) ⟨2124791, by rfl⟩ : syracuseStep 2833055 = 4249583) B4249583
theorem B1260191 : Blo 838352 1260191 := bstep (se 1 (by rfl) ⟨945143, by rfl⟩ : syracuseStep 1260191 = 1890287) B1890287
theorem B12139307 : Blo 838352 12139307 := bstep (se 1 (by rfl) ⟨9104480, by rfl⟩ : syracuseStep 12139307 = 18208961) B18208961
theorem B1260335 : Blo 838352 1260335 := bstep (se 1 (by rfl) ⟨945251, by rfl⟩ : syracuseStep 1260335 = 1890503) B1890503
theorem B1260455 : Blo 838352 1260455 := bstep (se 1 (by rfl) ⟨945341, by rfl⟩ : syracuseStep 1260455 = 1890683) B1890683
theorem B7289767 : Blo 838352 7289767 := bstep (se 1 (by rfl) ⟨5467325, by rfl⟩ : syracuseStep 7289767 = 10934651) B10934651
theorem B16137143 : Blo 838352 16137143 := bstep (se 1 (by rfl) ⟨12102857, by rfl⟩ : syracuseStep 16137143 = 24205715) B24205715
theorem B1260635 : Blo 838352 1260635 := bstep (se 1 (by rfl) ⟨945476, by rfl⟩ : syracuseStep 1260635 = 1890953) B1890953
theorem B2276443 : Blo 838352 2276443 := bstep (se 1 (by rfl) ⟨1707332, by rfl⟩ : syracuseStep 2276443 = 3414665) B3414665
theorem B3194099 : Blo 838352 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B1261007 : Blo 838352 1261007 := bstep (se 1 (by rfl) ⟨945755, by rfl⟩ : syracuseStep 1261007 = 1891511) B1891511
theorem B8076797 : Blo 838352 8076797 := bstep (se 3 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 8076797 = 3028799) B3028799
theorem B2834027 : Blo 838352 2834027 := bstep (se 1 (by rfl) ⟨2125520, by rfl⟩ : syracuseStep 2834027 = 4251041) B4251041
theorem B1261391 : Blo 838352 1261391 := bstep (se 1 (by rfl) ⟨946043, by rfl⟩ : syracuseStep 1261391 = 1892087) B1892087
theorem B2834297 : Blo 838352 2834297 := bstep (se 2 (by rfl) ⟨1062861, by rfl⟩ : syracuseStep 2834297 = 2125723) B2125723
theorem B1261511 : Blo 838352 1261511 := bstep (se 1 (by rfl) ⟨946133, by rfl⟩ : syracuseStep 1261511 = 1892267) B1892267
theorem B3195071 : Blo 838352 3195071 := bstep (se 1 (by rfl) ⟨2396303, by rfl⟩ : syracuseStep 3195071 = 4792607) B4792607
theorem B1261871 : Blo 838352 1261871 := bstep (se 1 (by rfl) ⟨946403, by rfl⟩ : syracuseStep 1261871 = 1892807) B1892807
theorem B7651835 : Blo 838352 7651835 := bstep (se 1 (by rfl) ⟨5738876, by rfl⟩ : syracuseStep 7651835 = 11477753) B11477753
theorem B3195389 : Blo 838352 3195389 := bstep (se 3 (by rfl) ⟨599135, by rfl⟩ : syracuseStep 3195389 = 1198271) B1198271
theorem B1262111 : Blo 838352 1262111 := bstep (se 1 (by rfl) ⟨946583, by rfl⟩ : syracuseStep 1262111 = 1893167) B1893167
theorem B11682407 : Blo 838352 11682407 := bstep (se 1 (by rfl) ⟨8761805, by rfl⟩ : syracuseStep 11682407 = 17523611) B17523611
theorem B4244561 : Blo 838352 4244561 := bstep (se 2 (by rfl) ⟨1591710, by rfl⟩ : syracuseStep 4244561 = 3183421) B3183421
theorem B2835647 : Blo 838352 2835647 := bstep (se 1 (by rfl) ⟨2126735, by rfl⟩ : syracuseStep 2835647 = 4253471) B4253471
theorem B1262783 : Blo 838352 1262783 := bstep (se 1 (by rfl) ⟨947087, by rfl⟩ : syracuseStep 1262783 = 1894175) B1894175
theorem B1262927 : Blo 838352 1262927 := bstep (se 1 (by rfl) ⟨947195, by rfl⟩ : syracuseStep 1262927 = 1894391) B1894391
theorem B2835809 : Blo 838352 2835809 := bstep (se 2 (by rfl) ⟨1063428, by rfl⟩ : syracuseStep 2835809 = 2126857) B2126857
theorem B1263017 : Blo 838352 1263017 := bstep (se 2 (by rfl) ⟨473631, by rfl⟩ : syracuseStep 1263017 = 947263) B947263
theorem B1263167 : Blo 838352 1263167 := bstep (se 1 (by rfl) ⟨947375, by rfl⟩ : syracuseStep 1263167 = 1894751) B1894751
theorem B1263209 : Blo 838352 1263209 := bstep (se 2 (by rfl) ⟨473703, by rfl⟩ : syracuseStep 1263209 = 947407) B947407
theorem B6145865 : Blo 838352 6145865 := bstep (se 2 (by rfl) ⟨2304699, by rfl⟩ : syracuseStep 6145865 = 4609399) B4609399
theorem B10209311 : Blo 838352 10209311 := bstep (se 1 (by rfl) ⟨7656983, by rfl⟩ : syracuseStep 10209311 = 15313967) B15313967
theorem B2836511 : Blo 838352 2836511 := bstep (se 1 (by rfl) ⟨2127383, by rfl⟩ : syracuseStep 2836511 = 4254767) B4254767
theorem B1886363 : Blo 838352 1886363 := bstep (se 1 (by rfl) ⟨1414772, by rfl⟩ : syracuseStep 1886363 = 2829545) B2829545
theorem B1886543 : Blo 838352 1886543 := bstep (se 1 (by rfl) ⟨1414907, by rfl⟩ : syracuseStep 1886543 = 2829815) B2829815
theorem B3590507 : Blo 838352 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B1886633 : Blo 838352 1886633 := bstep (se 2 (by rfl) ⟨707487, by rfl⟩ : syracuseStep 1886633 = 1414975) B1414975
theorem B1591969 : Blo 838352 1591969 := bstep (se 2 (by rfl) ⟨596988, by rfl⟩ : syracuseStep 1591969 = 1193977) B1193977
theorem B7162667 : Blo 838352 7162667 := bstep (se 1 (by rfl) ⟨5372000, by rfl⟩ : syracuseStep 7162667 = 10744001) B10744001
theorem B838623 : Blo 838352 838623 := bstep (se 1 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 838623 = 1257935) B1257935
theorem B838651 : Blo 838352 838651 := bstep (se 1 (by rfl) ⟨628988, by rfl⟩ : syracuseStep 838651 = 1257977) B1257977
theorem B1887227 : Blo 838352 1887227 := bstep (se 1 (by rfl) ⟨1415420, by rfl⟩ : syracuseStep 1887227 = 2830841) B2830841
theorem B3591175 : Blo 838352 3591175 := bstep (se 1 (by rfl) ⟨2693381, by rfl⟩ : syracuseStep 3591175 = 5386763) B5386763
theorem B838719 : Blo 838352 838719 := bstep (se 1 (by rfl) ⟨629039, by rfl⟩ : syracuseStep 838719 = 1258079) B1258079
theorem B1887407 : Blo 838352 1887407 := bstep (se 1 (by rfl) ⟨1415555, by rfl⟩ : syracuseStep 1887407 = 2831111) B2831111
theorem B1887443 : Blo 838352 1887443 := bstep (se 1 (by rfl) ⟨1415582, by rfl⟩ : syracuseStep 1887443 = 2831165) B2831165
theorem B3591533 : Blo 838352 3591533 := bstep (se 3 (by rfl) ⟨673412, by rfl⟩ : syracuseStep 3591533 = 1346825) B1346825
theorem B1133951 : Blo 838352 1133951 := bstep (se 1 (by rfl) ⟨850463, by rfl⟩ : syracuseStep 1133951 = 1700927) B1700927
theorem B839039 : Blo 838352 839039 := bstep (se 1 (by rfl) ⟨629279, by rfl⟩ : syracuseStep 839039 = 1258559) B1258559
theorem B839067 : Blo 838352 839067 := bstep (se 1 (by rfl) ⟨629300, by rfl⟩ : syracuseStep 839067 = 1258601) B1258601
theorem B839135 : Blo 838352 839135 := bstep (se 1 (by rfl) ⟨629351, by rfl⟩ : syracuseStep 839135 = 1258703) B1258703
theorem B1887713 : Blo 838352 1887713 := bstep (se 2 (by rfl) ⟨707892, by rfl⟩ : syracuseStep 1887713 = 1415785) B1415785
theorem B839271 : Blo 838352 839271 := bstep (se 1 (by rfl) ⟨629453, by rfl⟩ : syracuseStep 839271 = 1258907) B1258907
theorem B39308971 : Blo 838352 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B839419 : Blo 838352 839419 := bstep (se 1 (by rfl) ⟨629564, by rfl⟩ : syracuseStep 839419 = 1259129) B1259129
theorem B839487 : Blo 838352 839487 := bstep (se 1 (by rfl) ⟨629615, by rfl⟩ : syracuseStep 839487 = 1259231) B1259231
theorem B2019143 : Blo 838352 2019143 := bstep (se 1 (by rfl) ⟨1514357, by rfl⟩ : syracuseStep 2019143 = 3028715) B3028715
theorem B1888127 : Blo 838352 1888127 := bstep (se 1 (by rfl) ⟨1416095, by rfl⟩ : syracuseStep 1888127 = 2832191) B2832191
theorem B839551 : Blo 838352 839551 := bstep (se 1 (by rfl) ⟨629663, by rfl⟩ : syracuseStep 839551 = 1259327) B1259327
theorem B839663 : Blo 838352 839663 := bstep (se 1 (by rfl) ⟨629747, by rfl⟩ : syracuseStep 839663 = 1259495) B1259495
theorem B7655411 : Blo 838352 7655411 := bstep (se 1 (by rfl) ⟨5741558, by rfl⟩ : syracuseStep 7655411 = 11483117) B11483117
theorem B839675 : Blo 838352 839675 := bstep (se 1 (by rfl) ⟨629756, by rfl⟩ : syracuseStep 839675 = 1259513) B1259513
theorem B839743 : Blo 838352 839743 := bstep (se 1 (by rfl) ⟨629807, by rfl⟩ : syracuseStep 839743 = 1259615) B1259615
theorem B839783 : Blo 838352 839783 := bstep (se 1 (by rfl) ⟨629837, by rfl⟩ : syracuseStep 839783 = 1259675) B1259675
theorem B2019431 : Blo 838352 2019431 := bstep (se 1 (by rfl) ⟨1514573, by rfl⟩ : syracuseStep 2019431 = 3029147) B3029147
theorem B839807 : Blo 838352 839807 := bstep (se 1 (by rfl) ⟨629855, by rfl⟩ : syracuseStep 839807 = 1259711) B1259711
theorem B839835 : Blo 838352 839835 := bstep (se 1 (by rfl) ⟨629876, by rfl⟩ : syracuseStep 839835 = 1259753) B1259753
theorem B5099719 : Blo 838352 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B2183411 : Blo 838352 2183411 := bstep (se 1 (by rfl) ⟨1637558, by rfl⟩ : syracuseStep 2183411 = 3275117) B3275117
theorem B840039 : Blo 838352 840039 := bstep (se 1 (by rfl) ⟨630029, by rfl⟩ : syracuseStep 840039 = 1260059) B1260059
theorem B840091 : Blo 838352 840091 := bstep (se 1 (by rfl) ⟨630068, by rfl⟩ : syracuseStep 840091 = 1260137) B1260137
theorem B840443 : Blo 838352 840443 := bstep (se 1 (by rfl) ⟨630332, by rfl⟩ : syracuseStep 840443 = 1260665) B1260665
theorem B1889081 : Blo 838352 1889081 := bstep (se 2 (by rfl) ⟨708405, by rfl⟩ : syracuseStep 1889081 = 1416811) B1416811
theorem B840511 : Blo 838352 840511 := bstep (se 1 (by rfl) ⟨630383, by rfl⟩ : syracuseStep 840511 = 1260767) B1260767
theorem B840539 : Blo 838352 840539 := bstep (se 1 (by rfl) ⟨630404, by rfl⟩ : syracuseStep 840539 = 1260809) B1260809
theorem B1889135 : Blo 838352 1889135 := bstep (se 1 (by rfl) ⟨1416851, by rfl⟩ : syracuseStep 1889135 = 2833703) B2833703
theorem B840607 : Blo 838352 840607 := bstep (se 1 (by rfl) ⟨630455, by rfl⟩ : syracuseStep 840607 = 1260911) B1260911
theorem B840687 : Blo 838352 840687 := bstep (se 1 (by rfl) ⟨630515, by rfl⟩ : syracuseStep 840687 = 1261031) B1261031
theorem B840775 : Blo 838352 840775 := bstep (se 1 (by rfl) ⟨630581, by rfl⟩ : syracuseStep 840775 = 1261163) B1261163
theorem B840859 : Blo 838352 840859 := bstep (se 1 (by rfl) ⟨630644, by rfl⟩ : syracuseStep 840859 = 1261289) B1261289
theorem B1889441 : Blo 838352 1889441 := bstep (se 2 (by rfl) ⟨708540, by rfl⟩ : syracuseStep 1889441 = 1417081) B1417081
theorem B840955 : Blo 838352 840955 := bstep (se 1 (by rfl) ⟨630716, by rfl⟩ : syracuseStep 840955 = 1261433) B1261433
theorem B2839805 : Blo 838352 2839805 := bstep (se 3 (by rfl) ⟨532463, by rfl⟩ : syracuseStep 2839805 = 1064927) B1064927
theorem B841023 : Blo 838352 841023 := bstep (se 1 (by rfl) ⟨630767, by rfl⟩ : syracuseStep 841023 = 1261535) B1261535
theorem B1889711 : Blo 838352 1889711 := bstep (se 1 (by rfl) ⟨1417283, by rfl⟩ : syracuseStep 1889711 = 2834567) B2834567
theorem B841191 : Blo 838352 841191 := bstep (se 1 (by rfl) ⟨630893, by rfl⟩ : syracuseStep 841191 = 1261787) B1261787
theorem B841199 : Blo 838352 841199 := bstep (se 1 (by rfl) ⟨630899, by rfl⟩ : syracuseStep 841199 = 1261799) B1261799
theorem B4249097 : Blo 838352 4249097 := bstep (se 2 (by rfl) ⟨1593411, by rfl⟩ : syracuseStep 4249097 = 3186823) B3186823
theorem B841307 : Blo 838352 841307 := bstep (se 1 (by rfl) ⟨630980, by rfl⟩ : syracuseStep 841307 = 1261961) B1261961
theorem B841371 : Blo 838352 841371 := bstep (se 1 (by rfl) ⟨631028, by rfl⟩ : syracuseStep 841371 = 1262057) B1262057
theorem B12277451 : Blo 838352 12277451 := bstep (se 1 (by rfl) ⟨9208088, by rfl⟩ : syracuseStep 12277451 = 18416177) B18416177
theorem B5461739 : Blo 838352 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B9721579 : Blo 838352 9721579 := bstep (se 1 (by rfl) ⟨7291184, by rfl⟩ : syracuseStep 9721579 = 14582369) B14582369
theorem B841455 : Blo 838352 841455 := bstep (se 1 (by rfl) ⟨631091, by rfl⟩ : syracuseStep 841455 = 1262183) B1262183
theorem B841543 : Blo 838352 841543 := bstep (se 1 (by rfl) ⟨631157, by rfl⟩ : syracuseStep 841543 = 1262315) B1262315
theorem B1595227 : Blo 838352 1595227 := bstep (se 1 (by rfl) ⟨1196420, by rfl⟩ : syracuseStep 1595227 = 2392841) B2392841
theorem B841563 : Blo 838352 841563 := bstep (se 1 (by rfl) ⟨631172, by rfl⟩ : syracuseStep 841563 = 1262345) B1262345
theorem B841631 : Blo 838352 841631 := bstep (se 1 (by rfl) ⟨631223, by rfl⟩ : syracuseStep 841631 = 1262447) B1262447
theorem B6051833 : Blo 838352 6051833 := bstep (se 2 (by rfl) ⟨2269437, by rfl⟩ : syracuseStep 6051833 = 4538875) B4538875
theorem B3594233 : Blo 838352 3594233 := bstep (se 2 (by rfl) ⟨1347837, by rfl⟩ : syracuseStep 3594233 = 2695675) B2695675
theorem B2840615 : Blo 838352 2840615 := bstep (se 1 (by rfl) ⟨2130461, by rfl⟩ : syracuseStep 2840615 = 4260923) B4260923
theorem B841799 : Blo 838352 841799 := bstep (se 1 (by rfl) ⟨631349, by rfl⟩ : syracuseStep 841799 = 1262699) B1262699
theorem B4249745 : Blo 838352 4249745 := bstep (se 2 (by rfl) ⟨1593654, by rfl⟩ : syracuseStep 4249745 = 3187309) B3187309
theorem B2840723 : Blo 838352 2840723 := bstep (se 1 (by rfl) ⟨2130542, by rfl⟩ : syracuseStep 2840723 = 4261085) B4261085
theorem B841959 : Blo 838352 841959 := bstep (se 1 (by rfl) ⟨631469, by rfl⟩ : syracuseStep 841959 = 1262939) B1262939
theorem B1890719 : Blo 838352 1890719 := bstep (se 1 (by rfl) ⟨1418039, by rfl⟩ : syracuseStep 1890719 = 2836079) B2836079
theorem B8083871 : Blo 838352 8083871 := bstep (se 1 (by rfl) ⟨6062903, by rfl⟩ : syracuseStep 8083871 = 12125807) B12125807
theorem B2840993 : Blo 838352 2840993 := bstep (se 2 (by rfl) ⟨1065372, by rfl⟩ : syracuseStep 2840993 = 2130745) B2130745
theorem B842143 : Blo 838352 842143 := bstep (se 1 (by rfl) ⟨631607, by rfl⟩ : syracuseStep 842143 = 1263215) B1263215
theorem B842191 : Blo 838352 842191 := bstep (se 1 (by rfl) ⟨631643, by rfl⟩ : syracuseStep 842191 = 1263287) B1263287
theorem B1890791 : Blo 838352 1890791 := bstep (se 1 (by rfl) ⟨1418093, by rfl⟩ : syracuseStep 1890791 = 2836187) B2836187
theorem B842215 : Blo 838352 842215 := bstep (se 1 (by rfl) ⟨631661, by rfl⟩ : syracuseStep 842215 = 1263323) B1263323
theorem B842331 : Blo 838352 842331 := bstep (se 1 (by rfl) ⟨631748, by rfl⟩ : syracuseStep 842331 = 1263497) B1263497
theorem B7166663 : Blo 838352 7166663 := bstep (se 1 (by rfl) ⟨5374997, by rfl⟩ : syracuseStep 7166663 = 10749995) B10749995
theorem B2841533 : Blo 838352 2841533 := bstep (se 3 (by rfl) ⟨532787, by rfl⟩ : syracuseStep 2841533 = 1065575) B1065575
theorem B3595549 : Blo 838352 3595549 := bstep (se 3 (by rfl) ⟨674165, by rfl⟩ : syracuseStep 3595549 = 1348331) B1348331
theorem B1891655 : Blo 838352 1891655 := bstep (se 1 (by rfl) ⟨1418741, by rfl⟩ : syracuseStep 1891655 = 2837483) B2837483
theorem B1891691 : Blo 838352 1891691 := bstep (se 1 (by rfl) ⟨1418768, by rfl⟩ : syracuseStep 1891691 = 2837537) B2837537
theorem B1891817 : Blo 838352 1891817 := bstep (se 2 (by rfl) ⟨709431, by rfl⟩ : syracuseStep 1891817 = 1418863) B1418863
theorem B1596905 : Blo 838352 1596905 := bstep (se 2 (by rfl) ⟨598839, by rfl⟩ : syracuseStep 1596905 = 1197679) B1197679
theorem B3399259 : Blo 838352 3399259 := bstep (se 1 (by rfl) ⟨2549444, by rfl⟩ : syracuseStep 3399259 = 5098889) B5098889
theorem B1891961 : Blo 838352 1891961 := bstep (se 2 (by rfl) ⟨709485, by rfl⟩ : syracuseStep 1891961 = 1418971) B1418971
theorem B1892663 : Blo 838352 1892663 := bstep (se 1 (by rfl) ⟨1419497, by rfl⟩ : syracuseStep 1892663 = 2838995) B2838995
theorem B2842937 : Blo 838352 2842937 := bstep (se 2 (by rfl) ⟨1066101, by rfl⟩ : syracuseStep 2842937 = 2132203) B2132203
theorem B2023775 : Blo 838352 2023775 := bstep (se 1 (by rfl) ⟨1517831, by rfl⟩ : syracuseStep 2023775 = 3035663) B3035663
theorem B3596795 : Blo 838352 3596795 := bstep (se 1 (by rfl) ⟨2697596, by rfl⟩ : syracuseStep 3596795 = 5395193) B5395193
theorem B4252175 : Blo 838352 4252175 := bstep (se 1 (by rfl) ⟨3189131, by rfl⟩ : syracuseStep 4252175 = 6378263) B6378263
theorem B8282891 : Blo 838352 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B4252985 : Blo 838352 4252985 := bstep (se 2 (by rfl) ⟨1594869, by rfl⟩ : syracuseStep 4252985 = 3189739) B3189739
theorem B1893689 : Blo 838352 1893689 := bstep (se 2 (by rfl) ⟨710133, by rfl⟩ : syracuseStep 1893689 = 1420267) B1420267
theorem B1893959 : Blo 838352 1893959 := bstep (se 1 (by rfl) ⟨1420469, by rfl⟩ : syracuseStep 1893959 = 2840939) B2840939
theorem B943807 : Blo 838352 943807 := bstep (se 1 (by rfl) ⟨707855, by rfl⟩ : syracuseStep 943807 = 1415711) B1415711
theorem B1894139 : Blo 838352 1894139 := bstep (se 1 (by rfl) ⟨1420604, by rfl⟩ : syracuseStep 1894139 = 2841209) B2841209
theorem B944095 : Blo 838352 944095 := bstep (se 1 (by rfl) ⟨708071, by rfl⟩ : syracuseStep 944095 = 1416143) B1416143
theorem B6383609 : Blo 838352 6383609 := bstep (se 2 (by rfl) ⟨2393853, by rfl⟩ : syracuseStep 6383609 = 4787707) B4787707
theorem B1894427 : Blo 838352 1894427 := bstep (se 1 (by rfl) ⟨1420820, by rfl⟩ : syracuseStep 1894427 = 2841641) B2841641
theorem B2189575 : Blo 838352 2189575 := bstep (se 1 (by rfl) ⟨1642181, by rfl⟩ : syracuseStep 2189575 = 3284363) B3284363
theorem B3402209 : Blo 838352 3402209 := bstep (se 2 (by rfl) ⟨1275828, by rfl⟩ : syracuseStep 3402209 = 2551657) B2551657
theorem B944743 : Blo 838352 944743 := bstep (se 1 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 944743 = 1417115) B1417115
theorem B6810455 : Blo 838352 6810455 := bstep (se 1 (by rfl) ⟨5107841, by rfl⟩ : syracuseStep 6810455 = 10215683) B10215683
theorem B94563235 : Blo 838352 94563235 := bstep (se 1 (by rfl) ⟨70922426, by rfl⟩ : syracuseStep 94563235 = 141844853) B141844853
theorem B7171415 : Blo 838352 7171415 := bstep (se 1 (by rfl) ⟨5378561, by rfl⟩ : syracuseStep 7171415 = 10757123) B10757123
theorem B945535 : Blo 838352 945535 := bstep (se 1 (by rfl) ⟨709151, by rfl⟩ : syracuseStep 945535 = 1418303) B1418303
theorem B373616327 : Blo 838352 373616327 := bstep (se 1 (by rfl) ⟨280212245, by rfl⟩ : syracuseStep 373616327 = 560424491) B560424491
theorem B2387681 : Blo 838352 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B22998971 : Blo 838352 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B946939 : Blo 838352 946939 := bstep (se 1 (by rfl) ⟨710204, by rfl⟩ : syracuseStep 946939 = 1420409) B1420409
theorem B2554409 : Blo 838352 2554409 := bstep (se 2 (by rfl) ⟨957903, by rfl⟩ : syracuseStep 2554409 = 1915807) B1915807
theorem B2128619 : Blo 838352 2128619 := bstep (se 1 (by rfl) ⟨1596464, by rfl⟩ : syracuseStep 2128619 = 3192929) B3192929
theorem B7175789 : Blo 838352 7175789 := bstep (se 3 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 7175789 = 2690921) B2690921
theorem B851623 : Blo 838352 851623 := bstep (se 1 (by rfl) ⟨638717, by rfl⟩ : syracuseStep 851623 = 1277435) B1277435
theorem B2130047 : Blo 838352 2130047 := bstep (se 1 (by rfl) ⟨1597535, by rfl⟩ : syracuseStep 2130047 = 3195071) B3195071
theorem B2687231 : Blo 838352 2687231 := bstep (se 1 (by rfl) ⟨2015423, by rfl⟩ : syracuseStep 2687231 = 4030847) B4030847
theorem B2130259 : Blo 838352 2130259 := bstep (se 1 (by rfl) ⟨1597694, by rfl⟩ : syracuseStep 2130259 = 3195389) B3195389
theorem B5375099 : Blo 838352 5375099 := bstep (se 1 (by rfl) ⟨4031324, by rfl⟩ : syracuseStep 5375099 = 8062649) B8062649
theorem B4097243 : Blo 838352 4097243 := bstep (se 1 (by rfl) ⟨3072932, by rfl⟩ : syracuseStep 4097243 = 6145865) B6145865
theorem B22087709 : Blo 838352 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B2394355 : Blo 838352 2394355 := bstep (se 1 (by rfl) ⟨1795766, by rfl⟩ : syracuseStep 2394355 = 3591533) B3591533
theorem B1346095 : Blo 838352 1346095 := bstep (se 1 (by rfl) ⟨1009571, by rfl⟩ : syracuseStep 1346095 = 2019143) B2019143
theorem B1346287 : Blo 838352 1346287 := bstep (se 1 (by rfl) ⟨1009715, by rfl⟩ : syracuseStep 1346287 = 2019431) B2019431
theorem B3411197 : Blo 838352 3411197 := bstep (se 3 (by rfl) ⟨639599, by rfl⟩ : syracuseStep 3411197 = 1279199) B1279199
theorem B3641159 : Blo 838352 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B51777467 : Blo 838352 51777467 := bstep (se 1 (by rfl) ⟨38833100, by rfl⟩ : syracuseStep 51777467 = 77666201) B77666201
theorem B12095477 : Blo 838352 12095477 := bstep (se 5 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 12095477 = 1133951) B1133951
theorem B4034555 : Blo 838352 4034555 := bstep (se 1 (by rfl) ⟨3025916, by rfl⟩ : syracuseStep 4034555 = 6051833) B6051833
theorem B2396155 : Blo 838352 2396155 := bstep (se 1 (by rfl) ⟨1797116, by rfl⟩ : syracuseStep 2396155 = 3594233) B3594233
theorem B4788233 : Blo 838352 4788233 := bstep (se 2 (by rfl) ⟨1795587, by rfl⟩ : syracuseStep 4788233 = 3591175) B3591175
theorem B2691575 : Blo 838352 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B32739869 : Blo 838352 32739869 := bstep (se 3 (by rfl) ⟨6138725, by rfl⟩ : syracuseStep 32739869 = 12277451) B12277451
theorem B4920563 : Blo 838352 4920563 := bstep (se 1 (by rfl) ⟨3690422, by rfl⟩ : syracuseStep 4920563 = 7380845) B7380845
theorem B7673075 : Blo 838352 7673075 := bstep (se 1 (by rfl) ⟨5754806, by rfl⟩ : syracuseStep 7673075 = 11509613) B11509613
theorem B1349183 : Blo 838352 1349183 := bstep (se 1 (by rfl) ⟨1011887, by rfl⟩ : syracuseStep 1349183 = 2023775) B2023775
theorem B2692703 : Blo 838352 2692703 := bstep (se 1 (by rfl) ⟨2019527, by rfl⟩ : syracuseStep 2692703 = 4039055) B4039055
theorem B2397863 : Blo 838352 2397863 := bstep (se 1 (by rfl) ⟨1798397, by rfl⟩ : syracuseStep 2397863 = 3596795) B3596795
theorem B9574685 : Blo 838352 9574685 := bstep (se 3 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 9574685 = 3590507) B3590507
theorem B10755119 : Blo 838352 10755119 := bstep (se 1 (by rfl) ⟨8066339, by rfl⟩ : syracuseStep 10755119 = 16132679) B16132679
theorem B4791899 : Blo 838352 4791899 := bstep (se 1 (by rfl) ⟨3593924, by rfl⟩ : syracuseStep 4791899 = 7187849) B7187849
theorem B249077551 : Blo 838352 249077551 := bstep (se 1 (by rfl) ⟨186808163, by rfl⟩ : syracuseStep 249077551 = 373616327) B373616327
theorem B5382071 : Blo 838352 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B1515899 : Blo 838352 1515899 := bstep (se 1 (by rfl) ⟨1136924, by rfl⟩ : syracuseStep 1515899 = 2273849) B2273849
theorem B4793039 : Blo 838352 4793039 := bstep (se 1 (by rfl) ⟨3594779, by rfl⟩ : syracuseStep 4793039 = 7189559) B7189559
theorem B7185185 : Blo 838352 7185185 := bstep (se 2 (by rfl) ⟨2694444, by rfl⟩ : syracuseStep 7185185 = 5388889) B5388889
theorem B4794065 : Blo 838352 4794065 := bstep (se 2 (by rfl) ⟨1797774, by rfl⟩ : syracuseStep 4794065 = 3595549) B3595549
theorem B1419079 : Blo 838352 1419079 := bstep (se 1 (by rfl) ⟨1064309, by rfl⟩ : syracuseStep 1419079 = 2128619) B2128619
theorem B10758095 : Blo 838352 10758095 := bstep (se 1 (by rfl) ⟨8068571, by rfl⟩ : syracuseStep 10758095 = 16137143) B16137143
theorem B4532345 : Blo 838352 4532345 := bstep (se 2 (by rfl) ⟨1699629, by rfl⟩ : syracuseStep 4532345 = 3399259) B3399259
theorem B5384531 : Blo 838352 5384531 := bstep (se 1 (by rfl) ⟨4038398, by rfl⟩ : syracuseStep 5384531 = 8076797) B8076797
theorem B3025745 : Blo 838352 3025745 := bstep (se 2 (by rfl) ⟨1134654, by rfl⟩ : syracuseStep 3025745 = 2269309) B2269309
theorem B896303 : Blo 838352 896303 := bstep (se 1 (by rfl) ⟨672227, by rfl⟩ : syracuseStep 896303 = 1344455) B1344455
theorem B1420591 : Blo 838352 1420591 := bstep (se 1 (by rfl) ⟨1065443, by rfl⟩ : syracuseStep 1420591 = 2130887) B2130887
theorem B2829707 : Blo 838352 2829707 := bstep (se 1 (by rfl) ⟨2122280, by rfl⟩ : syracuseStep 2829707 = 4244561) B4244561
theorem B11677733 : Blo 838352 11677733 := bstep (se 4 (by rfl) ⟨1094787, by rfl⟩ : syracuseStep 11677733 = 2189575) B2189575
theorem B3584083 : Blo 838352 3584083 := bstep (se 1 (by rfl) ⟨2688062, by rfl⟩ : syracuseStep 3584083 = 5376125) B5376125
theorem B1257575 : Blo 838352 1257575 := bstep (se 1 (by rfl) ⟨943181, by rfl⟩ : syracuseStep 1257575 = 1886363) B1886363
theorem B1257695 : Blo 838352 1257695 := bstep (se 1 (by rfl) ⟨943271, by rfl⟩ : syracuseStep 1257695 = 1886543) B1886543
theorem B897247 : Blo 838352 897247 := bstep (se 1 (by rfl) ⟨672935, by rfl⟩ : syracuseStep 897247 = 1345871) B1345871
theorem B1257755 : Blo 838352 1257755 := bstep (se 1 (by rfl) ⟨943316, by rfl⟩ : syracuseStep 1257755 = 1886633) B1886633
theorem B1258151 : Blo 838352 1258151 := bstep (se 1 (by rfl) ⟨943613, by rfl⟩ : syracuseStep 1258151 = 1887227) B1887227
theorem B1258271 : Blo 838352 1258271 := bstep (se 1 (by rfl) ⟨943703, by rfl⟩ : syracuseStep 1258271 = 1887407) B1887407
theorem B1258295 : Blo 838352 1258295 := bstep (se 1 (by rfl) ⟨943721, by rfl⟩ : syracuseStep 1258295 = 1887443) B1887443
theorem B1258409 : Blo 838352 1258409 := bstep (se 2 (by rfl) ⟨471903, by rfl⟩ : syracuseStep 1258409 = 943807) B943807
theorem B1258475 : Blo 838352 1258475 := bstep (se 1 (by rfl) ⟨943856, by rfl⟩ : syracuseStep 1258475 = 1887713) B1887713
theorem B1258751 : Blo 838352 1258751 := bstep (se 1 (by rfl) ⟨944063, by rfl⟩ : syracuseStep 1258751 = 1888127) B1888127
theorem B1258793 : Blo 838352 1258793 := bstep (se 2 (by rfl) ⟨472047, by rfl⟩ : syracuseStep 1258793 = 944095) B944095
theorem B1455607 : Blo 838352 1455607 := bstep (se 1 (by rfl) ⟨1091705, by rfl⟩ : syracuseStep 1455607 = 2183411) B2183411
theorem B1259387 : Blo 838352 1259387 := bstep (se 1 (by rfl) ⟨944540, by rfl⟩ : syracuseStep 1259387 = 1889081) B1889081
theorem B1259423 : Blo 838352 1259423 := bstep (se 1 (by rfl) ⟨944567, by rfl⟩ : syracuseStep 1259423 = 1889135) B1889135
theorem B1259627 : Blo 838352 1259627 := bstep (se 1 (by rfl) ⟨944720, by rfl⟩ : syracuseStep 1259627 = 1889441) B1889441
theorem B1259657 : Blo 838352 1259657 := bstep (se 2 (by rfl) ⟨472371, by rfl⟩ : syracuseStep 1259657 = 944743) B944743
theorem B1259807 : Blo 838352 1259807 := bstep (se 1 (by rfl) ⟨944855, by rfl⟩ : syracuseStep 1259807 = 1889711) B1889711
theorem B2832731 : Blo 838352 2832731 := bstep (se 1 (by rfl) ⟨2124548, by rfl⟩ : syracuseStep 2832731 = 4249097) B4249097
theorem B2833163 : Blo 838352 2833163 := bstep (se 1 (by rfl) ⟨2124872, by rfl⟩ : syracuseStep 2833163 = 4249745) B4249745
theorem B9583433 : Blo 838352 9583433 := bstep (se 2 (by rfl) ⟨3593787, by rfl⟩ : syracuseStep 9583433 = 7187575) B7187575
theorem B1260479 : Blo 838352 1260479 := bstep (se 1 (by rfl) ⟨945359, by rfl⟩ : syracuseStep 1260479 = 1890719) B1890719
theorem B5389247 : Blo 838352 5389247 := bstep (se 1 (by rfl) ⟨4041935, by rfl⟩ : syracuseStep 5389247 = 8083871) B8083871
theorem B1260527 : Blo 838352 1260527 := bstep (se 1 (by rfl) ⟨945395, by rfl⟩ : syracuseStep 1260527 = 1890791) B1890791
theorem B1260713 : Blo 838352 1260713 := bstep (se 2 (by rfl) ⟨472767, by rfl⟩ : syracuseStep 1260713 = 945535) B945535
theorem B9551357 : Blo 838352 9551357 := bstep (se 3 (by rfl) ⟨1790879, by rfl⟩ : syracuseStep 9551357 = 3581759) B3581759
theorem B1261103 : Blo 838352 1261103 := bstep (se 1 (by rfl) ⟨945827, by rfl⟩ : syracuseStep 1261103 = 1891655) B1891655
theorem B52411961 : Blo 838352 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B1261127 : Blo 838352 1261127 := bstep (se 1 (by rfl) ⟨945845, by rfl⟩ : syracuseStep 1261127 = 1891691) B1891691
theorem B1261211 : Blo 838352 1261211 := bstep (se 1 (by rfl) ⟨945908, by rfl⟩ : syracuseStep 1261211 = 1891817) B1891817
theorem B1064603 : Blo 838352 1064603 := bstep (se 1 (by rfl) ⟨798452, by rfl⟩ : syracuseStep 1064603 = 1596905) B1596905
theorem B3587759 : Blo 838352 3587759 := bstep (se 1 (by rfl) ⟨2690819, by rfl⟩ : syracuseStep 3587759 = 5381639) B5381639
theorem B1261307 : Blo 838352 1261307 := bstep (se 1 (by rfl) ⟨945980, by rfl⟩ : syracuseStep 1261307 = 1891961) B1891961
theorem B40812497 : Blo 838352 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B2834621 : Blo 838352 2834621 := bstep (se 3 (by rfl) ⟨531491, by rfl⟩ : syracuseStep 2834621 = 1062983) B1062983
theorem B1261775 : Blo 838352 1261775 := bstep (se 1 (by rfl) ⟨946331, by rfl⟩ : syracuseStep 1261775 = 1892663) B1892663
theorem B6799625 : Blo 838352 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B2834783 : Blo 838352 2834783 := bstep (se 1 (by rfl) ⟨2126087, by rfl⟩ : syracuseStep 2834783 = 4252175) B4252175
theorem B12141029 : Blo 838352 12141029 := bstep (se 4 (by rfl) ⟨1138221, by rfl⟩ : syracuseStep 12141029 = 2276443) B2276443
theorem B9814517 : Blo 838352 9814517 := bstep (se 5 (by rfl) ⟨460055, by rfl⟩ : syracuseStep 9814517 = 920111) B920111
theorem B2835323 : Blo 838352 2835323 := bstep (se 1 (by rfl) ⟨2126492, by rfl⟩ : syracuseStep 2835323 = 4252985) B4252985
theorem B1262459 : Blo 838352 1262459 := bstep (se 1 (by rfl) ⟨946844, by rfl⟩ : syracuseStep 1262459 = 1893689) B1893689
theorem B1262585 : Blo 838352 1262585 := bstep (se 2 (by rfl) ⟨473469, by rfl⟩ : syracuseStep 1262585 = 946939) B946939
theorem B1262639 : Blo 838352 1262639 := bstep (se 1 (by rfl) ⟨946979, by rfl⟩ : syracuseStep 1262639 = 1893959) B1893959
theorem B8078413 : Blo 838352 8078413 := bstep (se 3 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 8078413 = 3029405) B3029405
theorem B1262759 : Blo 838352 1262759 := bstep (se 1 (by rfl) ⟨947069, by rfl⟩ : syracuseStep 1262759 = 1894139) B1894139
theorem B4605281 : Blo 838352 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B1262951 : Blo 838352 1262951 := bstep (se 1 (by rfl) ⟨947213, by rfl⟩ : syracuseStep 1262951 = 1894427) B1894427
theorem B4540303 : Blo 838352 4540303 := bstep (se 1 (by rfl) ⟨3405227, by rfl⟩ : syracuseStep 4540303 = 6810455) B6810455
theorem B12962105 : Blo 838352 12962105 := bstep (se 2 (by rfl) ⟨4860789, by rfl⟩ : syracuseStep 12962105 = 9721579) B9721579
theorem B1591787 : Blo 838352 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B838399 : Blo 838352 838399 := bstep (se 1 (by rfl) ⟨628799, by rfl⟩ : syracuseStep 838399 = 1257599) B1257599
theorem B1886975 : Blo 838352 1886975 := bstep (se 1 (by rfl) ⟨1415231, by rfl⟩ : syracuseStep 1886975 = 2830463) B2830463
theorem B2018047 : Blo 838352 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B838823 : Blo 838352 838823 := bstep (se 1 (by rfl) ⟨629117, by rfl⟩ : syracuseStep 838823 = 1258235) B1258235
theorem B1887659 : Blo 838352 1887659 := bstep (se 1 (by rfl) ⟨1415744, by rfl⟩ : syracuseStep 1887659 = 2831489) B2831489
theorem B839119 : Blo 838352 839119 := bstep (se 1 (by rfl) ⟨629339, by rfl⟩ : syracuseStep 839119 = 1258679) B1258679
theorem B4541989 : Blo 838352 4541989 := bstep (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) B851623
theorem B839279 : Blo 838352 839279 := bstep (se 1 (by rfl) ⟨629459, by rfl⟩ : syracuseStep 839279 = 1258919) B1258919
theorem B839399 : Blo 838352 839399 := bstep (se 1 (by rfl) ⟨629549, by rfl⟩ : syracuseStep 839399 = 1259099) B1259099
theorem B6475511 : Blo 838352 6475511 := bstep (se 1 (by rfl) ⟨4856633, by rfl⟩ : syracuseStep 6475511 = 9713267) B9713267
theorem B9719689 : Blo 838352 9719689 := bstep (se 2 (by rfl) ⟨3644883, by rfl⟩ : syracuseStep 9719689 = 7289767) B7289767
theorem B1888199 : Blo 838352 1888199 := bstep (se 1 (by rfl) ⟨1416149, by rfl⟩ : syracuseStep 1888199 = 2832299) B2832299
theorem B839707 : Blo 838352 839707 := bstep (se 1 (by rfl) ⟨629780, by rfl⟩ : syracuseStep 839707 = 1259561) B1259561
theorem B839727 : Blo 838352 839727 := bstep (se 1 (by rfl) ⟨629795, by rfl⟩ : syracuseStep 839727 = 1259591) B1259591
theorem B1888559 : Blo 838352 1888559 := bstep (se 1 (by rfl) ⟨1416419, by rfl⟩ : syracuseStep 1888559 = 2832839) B2832839
theorem B839983 : Blo 838352 839983 := bstep (se 1 (by rfl) ⟨629987, by rfl⟩ : syracuseStep 839983 = 1259975) B1259975
theorem B1823023 : Blo 838352 1823023 := bstep (se 1 (by rfl) ⟨1367267, by rfl⟩ : syracuseStep 1823023 = 2734535) B2734535
theorem B1888703 : Blo 838352 1888703 := bstep (se 1 (by rfl) ⟨1416527, by rfl⟩ : syracuseStep 1888703 = 2833055) B2833055
theorem B840127 : Blo 838352 840127 := bstep (se 1 (by rfl) ⟨630095, by rfl⟩ : syracuseStep 840127 = 1260191) B1260191
theorem B840223 : Blo 838352 840223 := bstep (se 1 (by rfl) ⟨630167, by rfl⟩ : syracuseStep 840223 = 1260335) B1260335
theorem B840303 : Blo 838352 840303 := bstep (se 1 (by rfl) ⟨630227, by rfl⟩ : syracuseStep 840303 = 1260455) B1260455
theorem B840423 : Blo 838352 840423 := bstep (se 1 (by rfl) ⟨630317, by rfl⟩ : syracuseStep 840423 = 1260635) B1260635
theorem B840671 : Blo 838352 840671 := bstep (se 1 (by rfl) ⟨630503, by rfl⟩ : syracuseStep 840671 = 1261007) B1261007
theorem B1889351 : Blo 838352 1889351 := bstep (se 1 (by rfl) ⟨1417013, by rfl⟩ : syracuseStep 1889351 = 2834027) B2834027
theorem B840927 : Blo 838352 840927 := bstep (se 1 (by rfl) ⟨630695, by rfl⟩ : syracuseStep 840927 = 1261391) B1261391
theorem B1889531 : Blo 838352 1889531 := bstep (se 1 (by rfl) ⟨1417148, by rfl⟩ : syracuseStep 1889531 = 2834297) B2834297
theorem B841007 : Blo 838352 841007 := bstep (se 1 (by rfl) ⟨630755, by rfl⟩ : syracuseStep 841007 = 1261511) B1261511
theorem B841247 : Blo 838352 841247 := bstep (se 1 (by rfl) ⟨630935, by rfl⟩ : syracuseStep 841247 = 1261871) B1261871
theorem B5101223 : Blo 838352 5101223 := bstep (se 1 (by rfl) ⟨3825917, by rfl⟩ : syracuseStep 5101223 = 7651835) B7651835
theorem B841407 : Blo 838352 841407 := bstep (se 1 (by rfl) ⟨631055, by rfl⟩ : syracuseStep 841407 = 1262111) B1262111
theorem B1890431 : Blo 838352 1890431 := bstep (se 1 (by rfl) ⟨1417823, by rfl⟩ : syracuseStep 1890431 = 2835647) B2835647
theorem B841855 : Blo 838352 841855 := bstep (se 1 (by rfl) ⟨631391, by rfl⟩ : syracuseStep 841855 = 1262783) B1262783
theorem B841951 : Blo 838352 841951 := bstep (se 1 (by rfl) ⟨631463, by rfl⟩ : syracuseStep 841951 = 1262927) B1262927
theorem B1890539 : Blo 838352 1890539 := bstep (se 1 (by rfl) ⟨1417904, by rfl⟩ : syracuseStep 1890539 = 2835809) B2835809
theorem B842011 : Blo 838352 842011 := bstep (se 1 (by rfl) ⟨631508, by rfl⟩ : syracuseStep 842011 = 1263017) B1263017
theorem B842111 : Blo 838352 842111 := bstep (se 1 (by rfl) ⟨631583, by rfl⟩ : syracuseStep 842111 = 1263167) B1263167
theorem B842139 : Blo 838352 842139 := bstep (se 1 (by rfl) ⟨631604, by rfl⟩ : syracuseStep 842139 = 1263209) B1263209
theorem B6806207 : Blo 838352 6806207 := bstep (se 1 (by rfl) ⟨5104655, by rfl⟩ : syracuseStep 6806207 = 10209311) B10209311
theorem B1891007 : Blo 838352 1891007 := bstep (se 1 (by rfl) ⟨1418255, by rfl⟩ : syracuseStep 1891007 = 2836511) B2836511
theorem B2022121 : Blo 838352 2022121 := bstep (se 2 (by rfl) ⟨758295, by rfl⟩ : syracuseStep 2022121 = 1516591) B1516591
theorem B1596199 : Blo 838352 1596199 := bstep (se 1 (by rfl) ⟨1197149, by rfl⟩ : syracuseStep 1596199 = 2394299) B2394299
theorem B31153085 : Blo 838352 31153085 := bstep (se 3 (by rfl) ⟨5841203, by rfl⟩ : syracuseStep 31153085 = 11682407) B11682407
theorem B4775111 : Blo 838352 4775111 := bstep (se 1 (by rfl) ⟨3581333, by rfl⟩ : syracuseStep 4775111 = 7162667) B7162667
theorem B141712757 : Blo 838352 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B4546705 : Blo 838352 4546705 := bstep (se 2 (by rfl) ⟨1705014, by rfl⟩ : syracuseStep 4546705 = 3410029) B3410029
theorem B14377337 : Blo 838352 14377337 := bstep (se 2 (by rfl) ⟨5391501, by rfl⟩ : syracuseStep 14377337 = 10783003) B10783003
theorem B1893203 : Blo 838352 1893203 := bstep (se 1 (by rfl) ⟨1419902, by rfl⟩ : syracuseStep 1893203 = 2839805) B2839805
theorem B2122625 : Blo 838352 2122625 := bstep (se 2 (by rfl) ⟨795984, by rfl⟩ : syracuseStep 2122625 = 1591969) B1591969
theorem B1598447 : Blo 838352 1598447 := bstep (se 1 (by rfl) ⟨1198835, by rfl⟩ : syracuseStep 1598447 = 2397671) B2397671
theorem B2122807 : Blo 838352 2122807 := bstep (se 1 (by rfl) ⟨1592105, by rfl⟩ : syracuseStep 2122807 = 3184211) B3184211
theorem B943195 : Blo 838352 943195 := bstep (se 1 (by rfl) ⟨707396, by rfl⟩ : syracuseStep 943195 = 1414793) B1414793
theorem B126084313 : Blo 838352 126084313 := bstep (se 2 (by rfl) ⟨47281617, by rfl⟩ : syracuseStep 126084313 = 94563235) B94563235
theorem B1893743 : Blo 838352 1893743 := bstep (se 1 (by rfl) ⟨1420307, by rfl⟩ : syracuseStep 1893743 = 2840615) B2840615
theorem B1893815 : Blo 838352 1893815 := bstep (se 1 (by rfl) ⟨1420361, by rfl⟩ : syracuseStep 1893815 = 2840723) B2840723
theorem B17229277 : Blo 838352 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B943591 : Blo 838352 943591 := bstep (se 1 (by rfl) ⟨707693, by rfl⟩ : syracuseStep 943591 = 1415387) B1415387
theorem B1893995 : Blo 838352 1893995 := bstep (se 1 (by rfl) ⟨1420496, by rfl⟩ : syracuseStep 1893995 = 2840993) B2840993
theorem B943771 : Blo 838352 943771 := bstep (se 1 (by rfl) ⟨707828, by rfl⟩ : syracuseStep 943771 = 1415657) B1415657
theorem B2123435 : Blo 838352 2123435 := bstep (se 1 (by rfl) ⟨1592576, by rfl⟩ : syracuseStep 2123435 = 3185153) B3185153
theorem B4777775 : Blo 838352 4777775 := bstep (se 1 (by rfl) ⟨3583331, by rfl⟩ : syracuseStep 4777775 = 7166663) B7166663
theorem B1894265 : Blo 838352 1894265 := bstep (se 2 (by rfl) ⟨710349, by rfl⟩ : syracuseStep 1894265 = 1420699) B1420699
theorem B1894355 : Blo 838352 1894355 := bstep (se 1 (by rfl) ⟨1420766, by rfl⟩ : syracuseStep 1894355 = 2841533) B2841533
theorem B7563959 : Blo 838352 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B1895273 : Blo 838352 1895273 := bstep (se 2 (by rfl) ⟨710727, by rfl⟩ : syracuseStep 1895273 = 1421455) B1421455
theorem B1895291 : Blo 838352 1895291 := bstep (se 1 (by rfl) ⟨1421468, by rfl⟩ : syracuseStep 1895291 = 2842937) B2842937
theorem B2124751 : Blo 838352 2124751 := bstep (se 1 (by rfl) ⟨1593563, by rfl⟩ : syracuseStep 2124751 = 3187127) B3187127
theorem B8612999 : Blo 838352 8612999 := bstep (se 1 (by rfl) ⟨6459749, by rfl⟩ : syracuseStep 8612999 = 12919499) B12919499
theorem B10776239 : Blo 838352 10776239 := bstep (se 1 (by rfl) ⟨8082179, by rfl⟩ : syracuseStep 10776239 = 16164359) B16164359
theorem B1797851 : Blo 838352 1797851 := bstep (se 1 (by rfl) ⟨1348388, by rfl⟩ : syracuseStep 1797851 = 2696777) B2696777
theorem B6385553 : Blo 838352 6385553 := bstep (se 2 (by rfl) ⟨2394582, by rfl⟩ : syracuseStep 6385553 = 4789165) B4789165
theorem B9072557 : Blo 838352 9072557 := bstep (se 3 (by rfl) ⟨1701104, by rfl⟩ : syracuseStep 9072557 = 3402209) B3402209
theorem B4255739 : Blo 838352 4255739 := bstep (se 1 (by rfl) ⟨3191804, by rfl⟩ : syracuseStep 4255739 = 6383609) B6383609
theorem B2388295 : Blo 838352 2388295 := bstep (se 1 (by rfl) ⟨1791221, by rfl⟩ : syracuseStep 2388295 = 3582443) B3582443
theorem B9106121 : Blo 838352 9106121 := bstep (se 2 (by rfl) ⟨3414795, by rfl⟩ : syracuseStep 9106121 = 6829591) B6829591
theorem B4780943 : Blo 838352 4780943 := bstep (se 1 (by rfl) ⟨3585707, by rfl⟩ : syracuseStep 4780943 = 7171415) B7171415
theorem B3830843 : Blo 838352 3830843 := bstep (se 1 (by rfl) ⟨2873132, by rfl⟩ : syracuseStep 3830843 = 5746265) B5746265
theorem B2126969 : Blo 838352 2126969 := bstep (se 2 (by rfl) ⟨797613, by rfl⟩ : syracuseStep 2126969 = 1595227) B1595227
theorem B2389115 : Blo 838352 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B15332647 : Blo 838352 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B2127343 : Blo 838352 2127343 := bstep (se 1 (by rfl) ⟨1595507, by rfl⟩ : syracuseStep 2127343 = 3191015) B3191015
theorem B87520769 : Blo 838352 87520769 := bstep (se 2 (by rfl) ⟨32820288, by rfl⟩ : syracuseStep 87520769 = 65640577) B65640577
theorem B2128751 : Blo 838352 2128751 := bstep (se 1 (by rfl) ⟨1596563, by rfl⟩ : syracuseStep 2128751 = 3193127) B3193127
theorem B1702939 : Blo 838352 1702939 := bstep (se 1 (by rfl) ⟨1277204, by rfl⟩ : syracuseStep 1702939 = 2554409) B2554409
theorem B8092871 : Blo 838352 8092871 := bstep (se 1 (by rfl) ⟨6069653, by rfl⟩ : syracuseStep 8092871 = 12139307) B12139307
theorem B2129399 : Blo 838352 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B4783859 : Blo 838352 4783859 := bstep (se 1 (by rfl) ⟨3587894, by rfl⟩ : syracuseStep 4783859 = 7175789) B7175789
theorem B20414429 : Blo 838352 20414429 := bstep (se 3 (by rfl) ⟨3827705, by rfl⟩ : syracuseStep 20414429 = 7655411) B7655411
theorem B6062273 : Blo 838352 6062273 := bstep (se 2 (by rfl) ⟨2273352, by rfl⟩ : syracuseStep 6062273 = 4546705) B4546705
theorem B235602229 : Blo 838352 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B8094019 : Blo 838352 8094019 := bstep (se 1 (by rfl) ⟨6070514, by rfl⟩ : syracuseStep 8094019 = 12141029) B12141029
theorem B4785317 : Blo 838352 4785317 := bstep (se 4 (by rfl) ⟨448623, by rfl⟩ : syracuseStep 4785317 = 897247) B897247
theorem B22972369 : Blo 838352 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B8063651 : Blo 838352 8063651 := bstep (se 1 (by rfl) ⟨6047738, by rfl⟩ : syracuseStep 8063651 = 12095477) B12095477
theorem B2689703 : Blo 838352 2689703 := bstep (se 1 (by rfl) ⟨2017277, by rfl⟩ : syracuseStep 2689703 = 4034555) B4034555
theorem B21826579 : Blo 838352 21826579 := bstep (se 1 (by rfl) ⟨16369934, by rfl⟩ : syracuseStep 21826579 = 32739869) B32739869
theorem B3280375 : Blo 838352 3280375 := bstep (se 1 (by rfl) ⟨2460281, by rfl⟩ : syracuseStep 3280375 = 4920563) B4920563
theorem B5115383 : Blo 838352 5115383 := bstep (se 1 (by rfl) ⟨3836537, by rfl⟩ : syracuseStep 5115383 = 7673075) B7673075
theorem B2690729 : Blo 838352 2690729 := bstep (se 2 (by rfl) ⟨1009023, by rfl⟩ : syracuseStep 2690729 = 2018047) B2018047
theorem B13603261 : Blo 838352 13603261 := bstep (se 3 (by rfl) ⟨2550611, by rfl⟩ : syracuseStep 13603261 = 5101223) B5101223
theorem B6394301 : Blo 838352 6394301 := bstep (se 3 (by rfl) ⟨1198931, by rfl⟩ : syracuseStep 6394301 = 2397863) B2397863
theorem B3183407 : Blo 838352 3183407 := bstep (se 1 (by rfl) ⟨2387555, by rfl⟩ : syracuseStep 3183407 = 4775111) B4775111
theorem B94475171 : Blo 838352 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B2430697 : Blo 838352 2430697 := bstep (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) B1823023
theorem B3184393 : Blo 838352 3184393 := bstep (se 2 (by rfl) ⟨1194147, by rfl⟩ : syracuseStep 3184393 = 2388295) B2388295
theorem B4790123 : Blo 838352 4790123 := bstep (se 1 (by rfl) ⟨3592592, by rfl⟩ : syracuseStep 4790123 = 7185185) B7185185
theorem B1415083 : Blo 838352 1415083 := bstep (se 1 (by rfl) ⟨1061312, by rfl⟩ : syracuseStep 1415083 = 2122625) B2122625
theorem B1415623 : Blo 838352 1415623 := bstep (se 1 (by rfl) ⟨1061717, by rfl⟩ : syracuseStep 1415623 = 2123435) B2123435
theorem B3185183 : Blo 838352 3185183 := bstep (se 1 (by rfl) ⟨2388887, by rfl⟩ : syracuseStep 3185183 = 4777775) B4777775
theorem B3021563 : Blo 838352 3021563 := bstep (se 1 (by rfl) ⟨2266172, by rfl⟩ : syracuseStep 3021563 = 4532345) B4532345
theorem B1940809 : Blo 838352 1940809 := bstep (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) B1455607
theorem B5741999 : Blo 838352 5741999 := bstep (se 1 (by rfl) ⟨4306499, by rfl⟩ : syracuseStep 5741999 = 8612999) B8612999
theorem B7184159 : Blo 838352 7184159 := bstep (se 1 (by rfl) ⟨5388119, by rfl⟩ : syracuseStep 7184159 = 10776239) B10776239
theorem B6070747 : Blo 838352 6070747 := bstep (se 1 (by rfl) ⟨4553060, by rfl⟩ : syracuseStep 6070747 = 9106121) B9106121
theorem B3187295 : Blo 838352 3187295 := bstep (se 1 (by rfl) ⟨2390471, by rfl⟩ : syracuseStep 3187295 = 4780943) B4780943
theorem B1417979 : Blo 838352 1417979 := bstep (se 1 (by rfl) ⟨1063484, by rfl⟩ : syracuseStep 1417979 = 2126969) B2126969
theorem B2696161 : Blo 838352 2696161 := bstep (se 2 (by rfl) ⟨1011060, by rfl⟩ : syracuseStep 2696161 = 2022121) B2022121
theorem B2270585 : Blo 838352 2270585 := bstep (se 2 (by rfl) ⟨851469, by rfl⟩ : syracuseStep 2270585 = 1702939) B1702939
theorem B1419167 : Blo 838352 1419167 := bstep (se 1 (by rfl) ⟨1064375, by rfl⟩ : syracuseStep 1419167 = 2128751) B2128751
theorem B9709757 : Blo 838352 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B1419599 : Blo 838352 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B6367571 : Blo 838352 6367571 := bstep (se 1 (by rfl) ⟨4775678, by rfl⟩ : syracuseStep 6367571 = 9551357) B9551357
theorem B34941307 : Blo 838352 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B3189239 : Blo 838352 3189239 := bstep (se 1 (by rfl) ⟨2391929, by rfl⟩ : syracuseStep 3189239 = 4783859) B4783859
theorem B27208331 : Blo 838352 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B13609619 : Blo 838352 13609619 := bstep (se 1 (by rfl) ⟨10207214, by rfl⟩ : syracuseStep 13609619 = 20414429) B20414429
theorem B1420031 : Blo 838352 1420031 := bstep (se 1 (by rfl) ⟨1065023, by rfl⟩ : syracuseStep 1420031 = 2130047) B2130047
theorem B4533083 : Blo 838352 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B2731495 : Blo 838352 2731495 := bstep (se 1 (by rfl) ⟨2048621, by rfl⟩ : syracuseStep 2731495 = 4097243) B4097243
theorem B2830409 : Blo 838352 2830409 := bstep (se 2 (by rfl) ⟨1061403, by rfl⟩ : syracuseStep 2830409 = 2122807) B2122807
theorem B1257593 : Blo 838352 1257593 := bstep (se 2 (by rfl) ⟨471597, by rfl⟩ : syracuseStep 1257593 = 943195) B943195
theorem B168112417 : Blo 838352 168112417 := bstep (se 2 (by rfl) ⟨63042156, by rfl⟩ : syracuseStep 168112417 = 126084313) B126084313
theorem B1061191 : Blo 838352 1061191 := bstep (se 1 (by rfl) ⟨795893, by rfl⟩ : syracuseStep 1061191 = 1591787) B1591787
theorem B1257983 : Blo 838352 1257983 := bstep (se 1 (by rfl) ⟨943487, by rfl⟩ : syracuseStep 1257983 = 1886975) B1886975
theorem B1258121 : Blo 838352 1258121 := bstep (se 2 (by rfl) ⟨471795, by rfl⟩ : syracuseStep 1258121 = 943591) B943591
theorem B2274131 : Blo 838352 2274131 := bstep (se 1 (by rfl) ⟨1705598, by rfl⟩ : syracuseStep 2274131 = 3411197) B3411197
theorem B1258361 : Blo 838352 1258361 := bstep (se 2 (by rfl) ⟨471885, by rfl⟩ : syracuseStep 1258361 = 943771) B943771
theorem B1258439 : Blo 838352 1258439 := bstep (se 1 (by rfl) ⟨943829, by rfl⟩ : syracuseStep 1258439 = 1887659) B1887659
theorem B34518311 : Blo 838352 34518311 := bstep (se 1 (by rfl) ⟨25888733, by rfl⟩ : syracuseStep 34518311 = 51777467) B51777467
theorem B1258799 : Blo 838352 1258799 := bstep (se 1 (by rfl) ⟨944099, by rfl⟩ : syracuseStep 1258799 = 1888199) B1888199
theorem B3192155 : Blo 838352 3192155 := bstep (se 1 (by rfl) ⟨2394116, by rfl⟩ : syracuseStep 3192155 = 4788233) B4788233
theorem B1259039 : Blo 838352 1259039 := bstep (se 1 (by rfl) ⟨944279, by rfl⟩ : syracuseStep 1259039 = 1888559) B1888559
theorem B1259135 : Blo 838352 1259135 := bstep (se 1 (by rfl) ⟨944351, by rfl⟩ : syracuseStep 1259135 = 1888703) B1888703
theorem B3192473 : Blo 838352 3192473 := bstep (se 2 (by rfl) ⟨1197177, by rfl⟩ : syracuseStep 3192473 = 2394355) B2394355
theorem B14333597 : Blo 838352 14333597 := bstep (se 3 (by rfl) ⟨2687549, by rfl⟩ : syracuseStep 14333597 = 5375099) B5375099
theorem B6370973 : Blo 838352 6370973 := bstep (se 3 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 6370973 = 2389115) B2389115
theorem B1259567 : Blo 838352 1259567 := bstep (se 1 (by rfl) ⟨944675, by rfl⟩ : syracuseStep 1259567 = 1889351) B1889351
theorem B1259687 : Blo 838352 1259687 := bstep (se 1 (by rfl) ⟨944765, by rfl⟩ : syracuseStep 1259687 = 1889531) B1889531
theorem B2833001 : Blo 838352 2833001 := bstep (se 2 (by rfl) ⟨1062375, by rfl⟩ : syracuseStep 2833001 = 2124751) B2124751
theorem B1260287 : Blo 838352 1260287 := bstep (se 1 (by rfl) ⟨945215, by rfl⟩ : syracuseStep 1260287 = 1890431) B1890431
theorem B1260359 : Blo 838352 1260359 := bstep (se 1 (by rfl) ⟨945269, by rfl⟩ : syracuseStep 1260359 = 1890539) B1890539
theorem B4537471 : Blo 838352 4537471 := bstep (se 1 (by rfl) ⟨3403103, by rfl⟩ : syracuseStep 4537471 = 6806207) B6806207
theorem B1260671 : Blo 838352 1260671 := bstep (se 1 (by rfl) ⟨945503, by rfl⟩ : syracuseStep 1260671 = 1891007) B1891007
theorem B3194599 : Blo 838352 3194599 := bstep (se 1 (by rfl) ⟨2395949, by rfl⟩ : syracuseStep 3194599 = 4791899) B4791899
theorem B12959585 : Blo 838352 12959585 := bstep (se 2 (by rfl) ⟨4859844, by rfl⟩ : syracuseStep 12959585 = 9719689) B9719689
theorem B3588047 : Blo 838352 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B3194873 : Blo 838352 3194873 := bstep (se 2 (by rfl) ⟨1198077, by rfl⟩ : syracuseStep 3194873 = 2396155) B2396155
theorem B9584891 : Blo 838352 9584891 := bstep (se 1 (by rfl) ⟨7188668, by rfl⟩ : syracuseStep 9584891 = 14377337) B14377337
theorem B3195359 : Blo 838352 3195359 := bstep (se 1 (by rfl) ⟨2396519, by rfl⟩ : syracuseStep 3195359 = 4793039) B4793039
theorem B1262135 : Blo 838352 1262135 := bstep (se 1 (by rfl) ⟨946601, by rfl⟩ : syracuseStep 1262135 = 1893203) B1893203
theorem B1065631 : Blo 838352 1065631 := bstep (se 1 (by rfl) ⟨799223, by rfl⟩ : syracuseStep 1065631 = 1598447) B1598447
theorem B1262495 : Blo 838352 1262495 := bstep (se 1 (by rfl) ⟨946871, by rfl⟩ : syracuseStep 1262495 = 1893743) B1893743
theorem B1262543 : Blo 838352 1262543 := bstep (se 1 (by rfl) ⟨946907, by rfl⟩ : syracuseStep 1262543 = 1893815) B1893815
theorem B1262663 : Blo 838352 1262663 := bstep (se 1 (by rfl) ⟨946997, by rfl⟩ : syracuseStep 1262663 = 1893995) B1893995
theorem B3196043 : Blo 838352 3196043 := bstep (se 1 (by rfl) ⟨2397032, by rfl⟩ : syracuseStep 3196043 = 4794065) B4794065
theorem B1262843 : Blo 838352 1262843 := bstep (se 1 (by rfl) ⟨947132, by rfl⟩ : syracuseStep 1262843 = 1894265) B1894265
theorem B1262903 : Blo 838352 1262903 := bstep (se 1 (by rfl) ⟨947177, by rfl⟩ : syracuseStep 1262903 = 1894355) B1894355
theorem B3589687 : Blo 838352 3589687 := bstep (se 1 (by rfl) ⟨2692265, by rfl⟩ : syracuseStep 3589687 = 5384531) B5384531
theorem B2017163 : Blo 838352 2017163 := bstep (se 1 (by rfl) ⟨1512872, by rfl⟩ : syracuseStep 2017163 = 3025745) B3025745
theorem B1263515 : Blo 838352 1263515 := bstep (se 1 (by rfl) ⟨947636, by rfl⟩ : syracuseStep 1263515 = 1895273) B1895273
theorem B1263527 : Blo 838352 1263527 := bstep (se 1 (by rfl) ⟨947645, by rfl⟩ : syracuseStep 1263527 = 1895291) B1895291
theorem B2836457 : Blo 838352 2836457 := bstep (se 2 (by rfl) ⟨1063671, by rfl⟩ : syracuseStep 2836457 = 2127343) B2127343
theorem B1886471 : Blo 838352 1886471 := bstep (se 1 (by rfl) ⟨1414853, by rfl⟩ : syracuseStep 1886471 = 2829707) B2829707
theorem B1198567 : Blo 838352 1198567 := bstep (se 1 (by rfl) ⟨898925, by rfl⟩ : syracuseStep 1198567 = 1797851) B1797851
theorem B6048371 : Blo 838352 6048371 := bstep (se 1 (by rfl) ⟨4536278, by rfl⟩ : syracuseStep 6048371 = 9072557) B9072557
theorem B2837159 : Blo 838352 2837159 := bstep (se 1 (by rfl) ⟨2127869, by rfl⟩ : syracuseStep 2837159 = 4255739) B4255739
theorem B7785155 : Blo 838352 7785155 := bstep (se 1 (by rfl) ⟨5838866, by rfl⟩ : syracuseStep 7785155 = 11677733) B11677733
theorem B838383 : Blo 838352 838383 := bstep (se 1 (by rfl) ⟨628787, by rfl⟩ : syracuseStep 838383 = 1257575) B1257575
theorem B838463 : Blo 838352 838463 := bstep (se 1 (by rfl) ⟨628847, by rfl⟩ : syracuseStep 838463 = 1257695) B1257695
theorem B838503 : Blo 838352 838503 := bstep (se 1 (by rfl) ⟨628877, by rfl⟩ : syracuseStep 838503 = 1257755) B1257755
theorem B838767 : Blo 838352 838767 := bstep (se 1 (by rfl) ⟨629075, by rfl⟩ : syracuseStep 838767 = 1258151) B1258151
theorem B838847 : Blo 838352 838847 := bstep (se 1 (by rfl) ⟨629135, by rfl⟩ : syracuseStep 838847 = 1258271) B1258271
theorem B838863 : Blo 838352 838863 := bstep (se 1 (by rfl) ⟨629147, by rfl⟩ : syracuseStep 838863 = 1258295) B1258295
theorem B838939 : Blo 838352 838939 := bstep (se 1 (by rfl) ⟨629204, by rfl⟩ : syracuseStep 838939 = 1258409) B1258409
theorem B838983 : Blo 838352 838983 := bstep (se 1 (by rfl) ⟨629237, by rfl⟩ : syracuseStep 838983 = 1258475) B1258475
theorem B839167 : Blo 838352 839167 := bstep (se 1 (by rfl) ⟨629375, by rfl⟩ : syracuseStep 839167 = 1258751) B1258751
theorem B839195 : Blo 838352 839195 := bstep (se 1 (by rfl) ⟨629396, by rfl⟩ : syracuseStep 839195 = 1258793) B1258793
theorem B58347179 : Blo 838352 58347179 := bstep (se 1 (by rfl) ⟨43760384, by rfl⟩ : syracuseStep 58347179 = 87520769) B87520769
theorem B839591 : Blo 838352 839591 := bstep (se 1 (by rfl) ⟨629693, by rfl⟩ : syracuseStep 839591 = 1259387) B1259387
theorem B839615 : Blo 838352 839615 := bstep (se 1 (by rfl) ⟨629711, by rfl⟩ : syracuseStep 839615 = 1259423) B1259423
theorem B839751 : Blo 838352 839751 := bstep (se 1 (by rfl) ⟨629813, by rfl⟩ : syracuseStep 839751 = 1259627) B1259627
theorem B839771 : Blo 838352 839771 := bstep (se 1 (by rfl) ⟨629828, by rfl⟩ : syracuseStep 839771 = 1259657) B1259657
theorem B839871 : Blo 838352 839871 := bstep (se 1 (by rfl) ⟨629903, by rfl⟩ : syracuseStep 839871 = 1259807) B1259807
theorem B1888487 : Blo 838352 1888487 := bstep (se 1 (by rfl) ⟨1416365, by rfl⟩ : syracuseStep 1888487 = 2832731) B2832731
theorem B2838941 : Blo 838352 2838941 := bstep (se 3 (by rfl) ⟨532301, by rfl⟩ : syracuseStep 2838941 = 1064603) B1064603
theorem B1888775 : Blo 838352 1888775 := bstep (se 1 (by rfl) ⟨1416581, by rfl⟩ : syracuseStep 1888775 = 2833163) B2833163
theorem B840319 : Blo 838352 840319 := bstep (se 1 (by rfl) ⟨630239, by rfl⟩ : syracuseStep 840319 = 1260479) B1260479
theorem B3592831 : Blo 838352 3592831 := bstep (se 1 (by rfl) ⟨2694623, by rfl⟩ : syracuseStep 3592831 = 5389247) B5389247
theorem B840351 : Blo 838352 840351 := bstep (se 1 (by rfl) ⟨630263, by rfl⟩ : syracuseStep 840351 = 1260527) B1260527
theorem B840475 : Blo 838352 840475 := bstep (se 1 (by rfl) ⟨630356, by rfl⟩ : syracuseStep 840475 = 1260713) B1260713
theorem B5395247 : Blo 838352 5395247 := bstep (se 1 (by rfl) ⟨4046435, by rfl⟩ : syracuseStep 5395247 = 8092871) B8092871
theorem B840735 : Blo 838352 840735 := bstep (se 1 (by rfl) ⟨630551, by rfl⟩ : syracuseStep 840735 = 1261103) B1261103
theorem B840751 : Blo 838352 840751 := bstep (se 1 (by rfl) ⟨630563, by rfl⟩ : syracuseStep 840751 = 1261127) B1261127
theorem B840807 : Blo 838352 840807 := bstep (se 1 (by rfl) ⟨630605, by rfl⟩ : syracuseStep 840807 = 1261211) B1261211
theorem B840871 : Blo 838352 840871 := bstep (se 1 (by rfl) ⟨630653, by rfl⟩ : syracuseStep 840871 = 1261307) B1261307
theorem B1889747 : Blo 838352 1889747 := bstep (se 1 (by rfl) ⟨1417310, by rfl⟩ : syracuseStep 1889747 = 2834621) B2834621
theorem B841183 : Blo 838352 841183 := bstep (se 1 (by rfl) ⟨630887, by rfl⟩ : syracuseStep 841183 = 1261775) B1261775
theorem B1791487 : Blo 838352 1791487 := bstep (se 1 (by rfl) ⟨1343615, by rfl⟩ : syracuseStep 1791487 = 2687231) B2687231
theorem B1889855 : Blo 838352 1889855 := bstep (se 1 (by rfl) ⟨1417391, by rfl⟩ : syracuseStep 1889855 = 2834783) B2834783
theorem B6543011 : Blo 838352 6543011 := bstep (se 1 (by rfl) ⟨4907258, by rfl⟩ : syracuseStep 6543011 = 9814517) B9814517
theorem B2840345 : Blo 838352 2840345 := bstep (se 2 (by rfl) ⟨1065129, by rfl⟩ : syracuseStep 2840345 = 2130259) B2130259
theorem B1890215 : Blo 838352 1890215 := bstep (se 1 (by rfl) ⟨1417661, by rfl⟩ : syracuseStep 1890215 = 2835323) B2835323
theorem B841639 : Blo 838352 841639 := bstep (se 1 (by rfl) ⟨631229, by rfl⟩ : syracuseStep 841639 = 1262459) B1262459
theorem B841723 : Blo 838352 841723 := bstep (se 1 (by rfl) ⟨631292, by rfl⟩ : syracuseStep 841723 = 1262585) B1262585
theorem B841759 : Blo 838352 841759 := bstep (se 1 (by rfl) ⟨631319, by rfl⟩ : syracuseStep 841759 = 1262639) B1262639
theorem B841839 : Blo 838352 841839 := bstep (se 1 (by rfl) ⟨631379, by rfl⟩ : syracuseStep 841839 = 1262759) B1262759
theorem B3070187 : Blo 838352 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B841967 : Blo 838352 841967 := bstep (se 1 (by rfl) ⟨631475, by rfl⟩ : syracuseStep 841967 = 1262951) B1262951
theorem B10771217 : Blo 838352 10771217 := bstep (se 2 (by rfl) ⟨4039206, by rfl⟩ : syracuseStep 10771217 = 8078413) B8078413
theorem B8641403 : Blo 838352 8641403 := bstep (se 1 (by rfl) ⟨6481052, by rfl⟩ : syracuseStep 8641403 = 12962105) B12962105
theorem B1892105 : Blo 838352 1892105 := bstep (se 2 (by rfl) ⟨709539, by rfl⟩ : syracuseStep 1892105 = 1419079) B1419079
theorem B6053737 : Blo 838352 6053737 := bstep (se 2 (by rfl) ⟨2270151, by rfl⟩ : syracuseStep 6053737 = 4540303) B4540303
theorem B1794383 : Blo 838352 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B1794793 : Blo 838352 1794793 := bstep (se 2 (by rfl) ⟨673047, by rfl⟩ : syracuseStep 1794793 = 1346095) B1346095
theorem B1795049 : Blo 838352 1795049 := bstep (se 2 (by rfl) ⟨673143, by rfl⟩ : syracuseStep 1795049 = 1346287) B1346287
theorem B1795135 : Blo 838352 1795135 := bstep (se 1 (by rfl) ⟨1346351, by rfl⟩ : syracuseStep 1795135 = 2692703) B2692703
theorem B3597821 : Blo 838352 3597821 := bstep (se 3 (by rfl) ⟨674591, by rfl⟩ : syracuseStep 3597821 = 1349183) B1349183
theorem B6383123 : Blo 838352 6383123 := bstep (se 1 (by rfl) ⟨4787342, by rfl⟩ : syracuseStep 6383123 = 9574685) B9574685
theorem B1894121 : Blo 838352 1894121 := bstep (se 2 (by rfl) ⟨710295, by rfl⟩ : syracuseStep 1894121 = 1420591) B1420591
theorem B20768723 : Blo 838352 20768723 := bstep (se 1 (by rfl) ⟨15576542, by rfl⟩ : syracuseStep 20768723 = 31153085) B31153085
theorem B7170079 : Blo 838352 7170079 := bstep (se 1 (by rfl) ⟨5377559, by rfl⟩ : syracuseStep 7170079 = 10755119) B10755119
theorem B6055985 : Blo 838352 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B4778777 : Blo 838352 4778777 := bstep (se 2 (by rfl) ⟨1792041, by rfl⟩ : syracuseStep 4778777 = 3584083) B3584083
theorem B1010599 : Blo 838352 1010599 := bstep (se 1 (by rfl) ⟨757949, by rfl⟩ : syracuseStep 1010599 = 1515899) B1515899
theorem B7172063 : Blo 838352 7172063 := bstep (se 1 (by rfl) ⟨5379047, by rfl⟩ : syracuseStep 7172063 = 10758095) B10758095
theorem B20443529 : Blo 838352 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B5042639 : Blo 838352 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B4257035 : Blo 838352 4257035 := bstep (se 1 (by rfl) ⟨3192776, by rfl⟩ : syracuseStep 4257035 = 6385553) B6385553
theorem B2553895 : Blo 838352 2553895 := bstep (se 1 (by rfl) ⟨1915421, by rfl⟩ : syracuseStep 2553895 = 3830843) B3830843
theorem B2390141 : Blo 838352 2390141 := bstep (se 3 (by rfl) ⟨448151, by rfl⟩ : syracuseStep 2390141 = 896303) B896303
theorem B2128265 : Blo 838352 2128265 := bstep (se 2 (by rfl) ⟨798099, by rfl⟩ : syracuseStep 2128265 = 1596199) B1596199
theorem B6388955 : Blo 838352 6388955 := bstep (se 1 (by rfl) ⟨4791716, by rfl⟩ : syracuseStep 6388955 = 9583433) B9583433
theorem B17268029 : Blo 838352 17268029 := bstep (se 3 (by rfl) ⟨3237755, by rfl⟩ : syracuseStep 17268029 = 6475511) B6475511
theorem B332103401 : Blo 838352 332103401 := bstep (se 2 (by rfl) ⟨124538775, by rfl⟩ : syracuseStep 332103401 = 249077551) B249077551
theorem B2391839 : Blo 838352 2391839 := bstep (se 1 (by rfl) ⟨1793879, by rfl⟩ : syracuseStep 2391839 = 3587759) B3587759
theorem B6389927 : Blo 838352 6389927 := bstep (se 1 (by rfl) ⟨4792445, by rfl⟩ : syracuseStep 6389927 = 9584891) B9584891
theorem B2130239 : Blo 838352 2130239 := bstep (se 1 (by rfl) ⟨1597679, by rfl⟩ : syracuseStep 2130239 = 3195359) B3195359
theorem B8094329 : Blo 838352 8094329 := bstep (se 2 (by rfl) ⟨3035373, by rfl⟩ : syracuseStep 8094329 = 6070747) B6070747
theorem B2130695 : Blo 838352 2130695 := bstep (se 1 (by rfl) ⟨1598021, by rfl⟩ : syracuseStep 2130695 = 3196043) B3196043
theorem B2393057 : Blo 838352 2393057 := bstep (se 2 (by rfl) ⟨897396, by rfl⟩ : syracuseStep 2393057 = 1794793) B1794793
theorem B1344775 : Blo 838352 1344775 := bstep (se 1 (by rfl) ⟨1008581, by rfl⟩ : syracuseStep 1344775 = 2017163) B2017163
theorem B2393513 : Blo 838352 2393513 := bstep (se 2 (by rfl) ⟨897567, by rfl⟩ : syracuseStep 2393513 = 1795135) B1795135
theorem B5375767 : Blo 838352 5375767 := bstep (se 1 (by rfl) ⟨4031825, by rfl⟩ : syracuseStep 5375767 = 8063651) B8063651
theorem B4786249 : Blo 838352 4786249 := bstep (se 2 (by rfl) ⟨1794843, by rfl⟩ : syracuseStep 4786249 = 3589687) B3589687
theorem B3410255 : Blo 838352 3410255 := bstep (se 1 (by rfl) ⟨2557691, by rfl⟩ : syracuseStep 3410255 = 5115383) B5115383
theorem B38898119 : Blo 838352 38898119 := bstep (se 1 (by rfl) ⟨29173589, by rfl⟩ : syracuseStep 38898119 = 58347179) B58347179
theorem B6392357 : Blo 838352 6392357 := bstep (se 4 (by rfl) ⟨599283, by rfl⟩ : syracuseStep 6392357 = 1198567) B1198567
theorem B4262867 : Blo 838352 4262867 := bstep (se 1 (by rfl) ⟨3197150, by rfl⟩ : syracuseStep 4262867 = 6394301) B6394301
theorem B29102105 : Blo 838352 29102105 := bstep (se 2 (by rfl) ⟨10913289, by rfl⟩ : syracuseStep 29102105 = 21826579) B21826579
theorem B7180811 : Blo 838352 7180811 := bstep (se 1 (by rfl) ⟨5385608, by rfl⟩ : syracuseStep 7180811 = 10771217) B10771217
theorem B3641993 : Blo 838352 3641993 := bstep (se 2 (by rfl) ⟨1365747, by rfl⟩ : syracuseStep 3641993 = 2731495) B2731495
theorem B4789439 : Blo 838352 4789439 := bstep (se 1 (by rfl) ⟨3592079, by rfl⟩ : syracuseStep 4789439 = 7184159) B7184159
theorem B1414921 : Blo 838352 1414921 := bstep (se 2 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 1414921 = 1061191) B1061191
theorem B4790441 : Blo 838352 4790441 := bstep (se 2 (by rfl) ⟨1796415, by rfl⟩ : syracuseStep 4790441 = 3592831) B3592831
theorem B1513723 : Blo 838352 1513723 := bstep (se 1 (by rfl) ⟨1135292, by rfl⟩ : syracuseStep 1513723 = 2270585) B2270585
theorem B2398547 : Blo 838352 2398547 := bstep (se 1 (by rfl) ⟨1798910, by rfl⟩ : syracuseStep 2398547 = 3597821) B3597821
theorem B4037323 : Blo 838352 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B16128989 : Blo 838352 16128989 := bstep (se 3 (by rfl) ⟨3024185, by rfl⟩ : syracuseStep 16128989 = 6048371) B6048371
theorem B3185851 : Blo 838352 3185851 := bstep (se 1 (by rfl) ⟨2389388, by rfl⟩ : syracuseStep 3185851 = 4778777) B4778777
theorem B3022055 : Blo 838352 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B1516087 : Blo 838352 1516087 := bstep (se 1 (by rfl) ⟨1137065, by rfl⟩ : syracuseStep 1516087 = 2274131) B2274131
theorem B23012207 : Blo 838352 23012207 := bstep (se 1 (by rfl) ⟨17259155, by rfl⟩ : syracuseStep 23012207 = 34518311) B34518311
theorem B1418843 : Blo 838352 1418843 := bstep (se 1 (by rfl) ⟨1064132, by rfl⟩ : syracuseStep 1418843 = 2128265) B2128265
theorem B11512019 : Blo 838352 11512019 := bstep (se 1 (by rfl) ⟨8634014, by rfl⟩ : syracuseStep 11512019 = 17268029) B17268029
theorem B8071649 : Blo 838352 8071649 := bstep (se 2 (by rfl) ⟨3026868, by rfl⟩ : syracuseStep 8071649 = 6053737) B6053737
theorem B4041515 : Blo 838352 4041515 := bstep (se 1 (by rfl) ⟨3031136, by rfl⟩ : syracuseStep 4041515 = 6062273) B6062273
theorem B10792025 : Blo 838352 10792025 := bstep (se 2 (by rfl) ⟨4047009, by rfl⟩ : syracuseStep 10792025 = 8094019) B8094019
theorem B3190211 : Blo 838352 3190211 := bstep (se 1 (by rfl) ⟨2392658, by rfl⟩ : syracuseStep 3190211 = 4785317) B4785317
theorem B1420841 : Blo 838352 1420841 := bstep (se 2 (by rfl) ⟨532815, by rfl⟩ : syracuseStep 1420841 = 1065631) B1065631
theorem B13447037 : Blo 838352 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B1257647 : Blo 838352 1257647 := bstep (se 1 (by rfl) ⟨943235, by rfl⟩ : syracuseStep 1257647 = 1886471) B1886471
theorem B5190103 : Blo 838352 5190103 := bstep (se 1 (by rfl) ⟨3892577, by rfl⟩ : syracuseStep 5190103 = 7785155) B7785155
theorem B251933789 : Blo 838352 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B1258991 : Blo 838352 1258991 := bstep (se 1 (by rfl) ⟨944243, by rfl⟩ : syracuseStep 1258991 = 1888487) B1888487
theorem B1259183 : Blo 838352 1259183 := bstep (se 1 (by rfl) ⟨944387, by rfl⟩ : syracuseStep 1259183 = 1888775) B1888775
theorem B1259831 : Blo 838352 1259831 := bstep (se 1 (by rfl) ⟨944873, by rfl⟩ : syracuseStep 1259831 = 1889747) B1889747
theorem B1259903 : Blo 838352 1259903 := bstep (se 1 (by rfl) ⟨944927, by rfl⟩ : syracuseStep 1259903 = 1889855) B1889855
theorem B3193415 : Blo 838352 3193415 := bstep (se 1 (by rfl) ⟨2395061, by rfl⟩ : syracuseStep 3193415 = 4790123) B4790123
theorem B1260143 : Blo 838352 1260143 := bstep (se 1 (by rfl) ⟨945107, by rfl⟩ : syracuseStep 1260143 = 1890215) B1890215
theorem B2046791 : Blo 838352 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B17448029 : Blo 838352 17448029 := bstep (se 3 (by rfl) ⟨3271505, by rfl⟩ : syracuseStep 17448029 = 6543011) B6543011
theorem B4373833 : Blo 838352 4373833 := bstep (se 2 (by rfl) ⟨1640187, by rfl⟩ : syracuseStep 4373833 = 3280375) B3280375
theorem B1261403 : Blo 838352 1261403 := bstep (se 1 (by rfl) ⟨946052, by rfl⟩ : syracuseStep 1261403 = 1892105) B1892105
theorem B1196255 : Blo 838352 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B224149889 : Blo 838352 224149889 := bstep (se 2 (by rfl) ⟨84056208, by rfl⟩ : syracuseStep 224149889 = 168112417) B168112417
theorem B18137681 : Blo 838352 18137681 := bstep (se 2 (by rfl) ⟨6801630, by rfl⟩ : syracuseStep 18137681 = 13603261) B13603261
theorem B1196699 : Blo 838352 1196699 := bstep (se 1 (by rfl) ⟨897524, by rfl⟩ : syracuseStep 1196699 = 1795049) B1795049
theorem B1262747 : Blo 838352 1262747 := bstep (se 1 (by rfl) ⟨947060, by rfl⟩ : syracuseStep 1262747 = 1894121) B1894121
theorem B13845815 : Blo 838352 13845815 := bstep (se 1 (by rfl) ⟨10384361, by rfl⟩ : syracuseStep 13845815 = 20768723) B20768723
theorem B6473171 : Blo 838352 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B4245047 : Blo 838352 4245047 := bstep (se 1 (by rfl) ⟨3183785, by rfl⟩ : syracuseStep 4245047 = 6367571) B6367571
theorem B18138887 : Blo 838352 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B4245857 : Blo 838352 4245857 := bstep (se 2 (by rfl) ⟨1592196, by rfl⟩ : syracuseStep 4245857 = 3184393) B3184393
theorem B1886777 : Blo 838352 1886777 := bstep (se 2 (by rfl) ⟨707541, by rfl⟩ : syracuseStep 1886777 = 1415083) B1415083
theorem B1886939 : Blo 838352 1886939 := bstep (se 1 (by rfl) ⟨1415204, by rfl⟩ : syracuseStep 1886939 = 2830409) B2830409
theorem B838395 : Blo 838352 838395 := bstep (se 1 (by rfl) ⟨628796, by rfl⟩ : syracuseStep 838395 = 1257593) B1257593
theorem B838655 : Blo 838352 838655 := bstep (se 1 (by rfl) ⟨628991, by rfl⟩ : syracuseStep 838655 = 1257983) B1257983
theorem B838747 : Blo 838352 838747 := bstep (se 1 (by rfl) ⟨629060, by rfl⟩ : syracuseStep 838747 = 1258121) B1258121
theorem B838907 : Blo 838352 838907 := bstep (se 1 (by rfl) ⟨629180, by rfl⟩ : syracuseStep 838907 = 1258361) B1258361
theorem B1887497 : Blo 838352 1887497 := bstep (se 2 (by rfl) ⟨707811, by rfl⟩ : syracuseStep 1887497 = 1415623) B1415623
theorem B838959 : Blo 838352 838959 := bstep (se 1 (by rfl) ⟨629219, by rfl⟩ : syracuseStep 838959 = 1258439) B1258439
theorem B2838023 : Blo 838352 2838023 := bstep (se 1 (by rfl) ⟨2128517, by rfl⟩ : syracuseStep 2838023 = 4257035) B4257035
theorem B839199 : Blo 838352 839199 := bstep (se 1 (by rfl) ⟨629399, by rfl⟩ : syracuseStep 839199 = 1258799) B1258799
theorem B839359 : Blo 838352 839359 := bstep (se 1 (by rfl) ⟨629519, by rfl⟩ : syracuseStep 839359 = 1259039) B1259039
theorem B839423 : Blo 838352 839423 := bstep (se 1 (by rfl) ⟨629567, by rfl⟩ : syracuseStep 839423 = 1259135) B1259135
theorem B9555731 : Blo 838352 9555731 := bstep (se 1 (by rfl) ⟨7166798, by rfl⟩ : syracuseStep 9555731 = 14333597) B14333597
theorem B4247315 : Blo 838352 4247315 := bstep (se 1 (by rfl) ⟨3185486, by rfl⟩ : syracuseStep 4247315 = 6370973) B6370973
theorem B839711 : Blo 838352 839711 := bstep (se 1 (by rfl) ⟨629783, by rfl⟩ : syracuseStep 839711 = 1259567) B1259567
theorem B1593427 : Blo 838352 1593427 := bstep (se 1 (by rfl) ⟨1195070, by rfl⟩ : syracuseStep 1593427 = 2390141) B2390141
theorem B839791 : Blo 838352 839791 := bstep (se 1 (by rfl) ⟨629843, by rfl⟩ : syracuseStep 839791 = 1259687) B1259687
theorem B6049961 : Blo 838352 6049961 := bstep (se 2 (by rfl) ⟨2268735, by rfl⟩ : syracuseStep 6049961 = 4537471) B4537471
theorem B1888667 : Blo 838352 1888667 := bstep (se 1 (by rfl) ⟨1416500, by rfl⟩ : syracuseStep 1888667 = 2833001) B2833001
theorem B840191 : Blo 838352 840191 := bstep (se 1 (by rfl) ⟨630143, by rfl⟩ : syracuseStep 840191 = 1260287) B1260287
theorem B840239 : Blo 838352 840239 := bstep (se 1 (by rfl) ⟨630179, by rfl⟩ : syracuseStep 840239 = 1260359) B1260359
theorem B840447 : Blo 838352 840447 := bstep (se 1 (by rfl) ⟨630335, by rfl⟩ : syracuseStep 840447 = 1260671) B1260671
theorem B221402267 : Blo 838352 221402267 := bstep (se 1 (by rfl) ⟨166051700, by rfl⟩ : syracuseStep 221402267 = 332103401) B332103401
theorem B1594559 : Blo 838352 1594559 := bstep (se 1 (by rfl) ⟨1195919, by rfl⟩ : syracuseStep 1594559 = 2391839) B2391839
theorem B8639723 : Blo 838352 8639723 := bstep (se 1 (by rfl) ⟨6479792, by rfl⟩ : syracuseStep 8639723 = 12959585) B12959585
theorem B13620773 : Blo 838352 13620773 := bstep (se 4 (by rfl) ⟨1276947, by rfl⟩ : syracuseStep 13620773 = 2553895) B2553895
theorem B841423 : Blo 838352 841423 := bstep (se 1 (by rfl) ⟨631067, by rfl⟩ : syracuseStep 841423 = 1262135) B1262135
theorem B314136305 : Blo 838352 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B841663 : Blo 838352 841663 := bstep (se 1 (by rfl) ⟨631247, by rfl⟩ : syracuseStep 841663 = 1262495) B1262495
theorem B841695 : Blo 838352 841695 := bstep (se 1 (by rfl) ⟨631271, by rfl⟩ : syracuseStep 841695 = 1262543) B1262543
theorem B841775 : Blo 838352 841775 := bstep (se 1 (by rfl) ⟨631331, by rfl⟩ : syracuseStep 841775 = 1262663) B1262663
theorem B841895 : Blo 838352 841895 := bstep (se 1 (by rfl) ⟨631421, by rfl⟩ : syracuseStep 841895 = 1262843) B1262843
theorem B841935 : Blo 838352 841935 := bstep (se 1 (by rfl) ⟨631451, by rfl⟩ : syracuseStep 841935 = 1262903) B1262903
theorem B842343 : Blo 838352 842343 := bstep (se 1 (by rfl) ⟨631757, by rfl⟩ : syracuseStep 842343 = 1263515) B1263515
theorem B842351 : Blo 838352 842351 := bstep (se 1 (by rfl) ⟨631763, by rfl⟩ : syracuseStep 842351 = 1263527) B1263527
theorem B3594881 : Blo 838352 3594881 := bstep (se 2 (by rfl) ⟨1348080, by rfl⟩ : syracuseStep 3594881 = 2696161) B2696161
theorem B1890971 : Blo 838352 1890971 := bstep (se 1 (by rfl) ⟨1418228, by rfl⟩ : syracuseStep 1890971 = 2836457) B2836457
theorem B1793135 : Blo 838352 1793135 := bstep (se 1 (by rfl) ⟨1344851, by rfl⟩ : syracuseStep 1793135 = 2689703) B2689703
theorem B1891439 : Blo 838352 1891439 := bstep (se 1 (by rfl) ⟨1418579, by rfl⟩ : syracuseStep 1891439 = 2837159) B2837159
theorem B1793819 : Blo 838352 1793819 := bstep (se 1 (by rfl) ⟨1345364, by rfl⟩ : syracuseStep 1793819 = 2690729) B2690729
theorem B30629825 : Blo 838352 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B9560105 : Blo 838352 9560105 := bstep (se 2 (by rfl) ⟨3585039, by rfl⟩ : syracuseStep 9560105 = 7170079) B7170079
theorem B1892627 : Blo 838352 1892627 := bstep (se 1 (by rfl) ⟨1419470, by rfl⟩ : syracuseStep 1892627 = 2838941) B2838941
theorem B46588409 : Blo 838352 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B2122271 : Blo 838352 2122271 := bstep (se 1 (by rfl) ⟨1591703, by rfl⟩ : syracuseStep 2122271 = 3183407) B3183407
theorem B3596831 : Blo 838352 3596831 := bstep (se 1 (by rfl) ⟨2697623, by rfl⟩ : syracuseStep 3596831 = 5395247) B5395247
theorem B1893563 : Blo 838352 1893563 := bstep (se 1 (by rfl) ⟨1420172, by rfl⟩ : syracuseStep 1893563 = 2840345) B2840345
theorem B2123455 : Blo 838352 2123455 := bstep (se 1 (by rfl) ⟨1592591, by rfl⟩ : syracuseStep 2123455 = 3185183) B3185183
theorem B5760935 : Blo 838352 5760935 := bstep (se 1 (by rfl) ⟨4320701, by rfl⟩ : syracuseStep 5760935 = 8641403) B8641403
theorem B3827999 : Blo 838352 3827999 := bstep (se 1 (by rfl) ⟨2870999, by rfl⟩ : syracuseStep 3827999 = 5741999) B5741999
theorem B2124863 : Blo 838352 2124863 := bstep (se 1 (by rfl) ⟨1593647, by rfl⟩ : syracuseStep 2124863 = 3187295) B3187295
theorem B945319 : Blo 838352 945319 := bstep (se 1 (by rfl) ⟨708989, by rfl⟩ : syracuseStep 945319 = 1417979) B1417979
theorem B4255415 : Blo 838352 4255415 := bstep (se 1 (by rfl) ⟨3191561, by rfl⟩ : syracuseStep 4255415 = 6383123) B6383123
theorem B946111 : Blo 838352 946111 := bstep (se 1 (by rfl) ⟨709583, by rfl⟩ : syracuseStep 946111 = 1419167) B1419167
theorem B946399 : Blo 838352 946399 := bstep (se 1 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 946399 = 1419599) B1419599
theorem B2126159 : Blo 838352 2126159 := bstep (se 1 (by rfl) ⟨1594619, by rfl⟩ : syracuseStep 2126159 = 3189239) B3189239
theorem B9073079 : Blo 838352 9073079 := bstep (se 1 (by rfl) ⟨6804809, by rfl⟩ : syracuseStep 9073079 = 13609619) B13609619
theorem B946687 : Blo 838352 946687 := bstep (se 1 (by rfl) ⟨710015, by rfl⟩ : syracuseStep 946687 = 1420031) B1420031
theorem B8057501 : Blo 838352 8057501 := bstep (se 3 (by rfl) ⟨1510781, by rfl⟩ : syracuseStep 8057501 = 3021563) B3021563
theorem B2388649 : Blo 838352 2388649 := bstep (se 2 (by rfl) ⟨895743, by rfl⟩ : syracuseStep 2388649 = 1791487) B1791487
theorem B3240929 : Blo 838352 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B4781375 : Blo 838352 4781375 := bstep (se 1 (by rfl) ⟨3586031, by rfl⟩ : syracuseStep 4781375 = 7172063) B7172063
theorem B13629019 : Blo 838352 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B21559445 : Blo 838352 21559445 := bstep (se 6 (by rfl) ⟨505299, by rfl⟩ : syracuseStep 21559445 = 1010599) B1010599
theorem B2128103 : Blo 838352 2128103 := bstep (se 1 (by rfl) ⟨1596077, by rfl⟩ : syracuseStep 2128103 = 3192155) B3192155
theorem B2128315 : Blo 838352 2128315 := bstep (se 1 (by rfl) ⟨1596236, by rfl⟩ : syracuseStep 2128315 = 3192473) B3192473
theorem B2587745 : Blo 838352 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B4259303 : Blo 838352 4259303 := bstep (se 1 (by rfl) ⟨3194477, by rfl⟩ : syracuseStep 4259303 = 6388955) B6388955
theorem B4259465 : Blo 838352 4259465 := bstep (se 2 (by rfl) ⟨1597299, by rfl⟩ : syracuseStep 4259465 = 3194599) B3194599
theorem B2392031 : Blo 838352 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B2129915 : Blo 838352 2129915 := bstep (se 1 (by rfl) ⟨1597436, by rfl⟩ : syracuseStep 2129915 = 3194873) B3194873
theorem B4259951 : Blo 838352 4259951 := bstep (se 1 (by rfl) ⟨3194963, by rfl⟩ : syracuseStep 4259951 = 6389927) B6389927
theorem B12091787 : Blo 838352 12091787 := bstep (se 1 (by rfl) ⟨9068840, by rfl⟩ : syracuseStep 12091787 = 18137681) B18137681
theorem B12092591 : Blo 838352 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B4261571 : Blo 838352 4261571 := bstep (se 1 (by rfl) ⟨3196178, by rfl⟩ : syracuseStep 4261571 = 6392357) B6392357
theorem B4033307 : Blo 838352 4033307 := bstep (se 1 (by rfl) ⟨3024980, by rfl⟩ : syracuseStep 4033307 = 6049961) B6049961
theorem B4787207 : Blo 838352 4787207 := bstep (se 1 (by rfl) ⟨3590405, by rfl⟩ : syracuseStep 4787207 = 7180811) B7180811
theorem B2427995 : Blo 838352 2427995 := bstep (se 1 (by rfl) ⟨1820996, by rfl⟩ : syracuseStep 2427995 = 3641993) B3641993
theorem B23039261 : Blo 838352 23039261 := bstep (se 3 (by rfl) ⟨4319861, by rfl⟩ : syracuseStep 23039261 = 8639723) B8639723
theorem B9080515 : Blo 838352 9080515 := bstep (se 1 (by rfl) ⟨6810386, by rfl⟩ : syracuseStep 9080515 = 13620773) B13620773
theorem B209424203 : Blo 838352 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B10752659 : Blo 838352 10752659 := bstep (se 1 (by rfl) ⟨8064494, by rfl⟩ : syracuseStep 10752659 = 16128989) B16128989
theorem B20419883 : Blo 838352 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B1414847 : Blo 838352 1414847 := bstep (se 1 (by rfl) ⟨1061135, by rfl⟩ : syracuseStep 1414847 = 2122271) B2122271
theorem B2397887 : Blo 838352 2397887 := bstep (se 1 (by rfl) ⟨1798415, by rfl⟩ : syracuseStep 2397887 = 3596831) B3596831
theorem B15341471 : Blo 838352 15341471 := bstep (se 1 (by rfl) ⟨11506103, by rfl⟩ : syracuseStep 15341471 = 23012207) B23012207
theorem B6920137 : Blo 838352 6920137 := bstep (se 2 (by rfl) ⟨2595051, by rfl⟩ : syracuseStep 6920137 = 5190103) B5190103
theorem B3184865 : Blo 838352 3184865 := bstep (se 2 (by rfl) ⟨1194324, by rfl⟩ : syracuseStep 3184865 = 2388649) B2388649
theorem B3840623 : Blo 838352 3840623 := bstep (se 1 (by rfl) ⟨2880467, by rfl⟩ : syracuseStep 3840623 = 5760935) B5760935
theorem B7674679 : Blo 838352 7674679 := bstep (se 1 (by rfl) ⟨5756009, by rfl⟩ : syracuseStep 7674679 = 11512019) B11512019
theorem B5381099 : Blo 838352 5381099 := bstep (se 1 (by rfl) ⟨4035824, by rfl⟩ : syracuseStep 5381099 = 8071649) B8071649
theorem B2694343 : Blo 838352 2694343 := bstep (se 1 (by rfl) ⟨2020757, by rfl⟩ : syracuseStep 2694343 = 4041515) B4041515
theorem B1416575 : Blo 838352 1416575 := bstep (se 1 (by rfl) ⟨1062431, by rfl⟩ : syracuseStep 1416575 = 2124863) B2124863
theorem B1417439 : Blo 838352 1417439 := bstep (se 1 (by rfl) ⟨1063079, by rfl⟩ : syracuseStep 1417439 = 2126159) B2126159
theorem B3187583 : Blo 838352 3187583 := bstep (se 1 (by rfl) ⟨2390687, by rfl⟩ : syracuseStep 3187583 = 4781375) B4781375
theorem B5383097 : Blo 838352 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B1418735 : Blo 838352 1418735 := bstep (se 1 (by rfl) ⟨1064051, by rfl⟩ : syracuseStep 1418735 = 2128103) B2128103
theorem B35858765 : Blo 838352 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B1419943 : Blo 838352 1419943 := bstep (se 1 (by rfl) ⟨1064957, by rfl⟩ : syracuseStep 1419943 = 2129915) B2129915
theorem B77605613 : Blo 838352 77605613 := bstep (se 3 (by rfl) ⟨14551052, by rfl⟩ : syracuseStep 77605613 = 29102105) B29102105
theorem B1420159 : Blo 838352 1420159 := bstep (se 1 (by rfl) ⟨1065119, by rfl⟩ : syracuseStep 1420159 = 2130239) B2130239
theorem B1420463 : Blo 838352 1420463 := bstep (se 1 (by rfl) ⟨1065347, by rfl⟩ : syracuseStep 1420463 = 2130695) B2130695
theorem B3190013 : Blo 838352 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B597733037 : Blo 838352 597733037 := bstep (se 3 (by rfl) ⟨112074944, by rfl⟩ : syracuseStep 597733037 = 224149889) B224149889
theorem B2830031 : Blo 838352 2830031 := bstep (se 1 (by rfl) ⟨2122523, by rfl⟩ : syracuseStep 2830031 = 4245047) B4245047
theorem B2273503 : Blo 838352 2273503 := bstep (se 1 (by rfl) ⟨1705127, by rfl⟩ : syracuseStep 2273503 = 3410255) B3410255
theorem B2830571 : Blo 838352 2830571 := bstep (se 1 (by rfl) ⟨2122928, by rfl⟩ : syracuseStep 2830571 = 4245857) B4245857
theorem B25932079 : Blo 838352 25932079 := bstep (se 1 (by rfl) ⟨19449059, by rfl⟩ : syracuseStep 25932079 = 38898119) B38898119
theorem B1257851 : Blo 838352 1257851 := bstep (se 1 (by rfl) ⟨943388, by rfl⟩ : syracuseStep 1257851 = 1886777) B1886777
theorem B3191197 : Blo 838352 3191197 := bstep (se 3 (by rfl) ⟨598349, by rfl⟩ : syracuseStep 3191197 = 1196699) B1196699
theorem B1257959 : Blo 838352 1257959 := bstep (se 1 (by rfl) ⟨943469, by rfl⟩ : syracuseStep 1257959 = 1886939) B1886939
theorem B1258331 : Blo 838352 1258331 := bstep (se 1 (by rfl) ⟨943748, by rfl⟩ : syracuseStep 1258331 = 1887497) B1887497
theorem B2831273 : Blo 838352 2831273 := bstep (se 2 (by rfl) ⟨1061727, by rfl⟩ : syracuseStep 2831273 = 2123455) B2123455
theorem B6370487 : Blo 838352 6370487 := bstep (se 1 (by rfl) ⟨4777865, by rfl⟩ : syracuseStep 6370487 = 9555731) B9555731
theorem B2831543 : Blo 838352 2831543 := bstep (se 1 (by rfl) ⟨2123657, by rfl⟩ : syracuseStep 2831543 = 4247315) B4247315
theorem B1259111 : Blo 838352 1259111 := bstep (se 1 (by rfl) ⟨944333, by rfl⟩ : syracuseStep 1259111 = 1888667) B1888667
theorem B147601511 : Blo 838352 147601511 := bstep (se 1 (by rfl) ⟨110701133, by rfl⟩ : syracuseStep 147601511 = 221402267) B221402267
theorem B1063039 : Blo 838352 1063039 := bstep (se 1 (by rfl) ⟨797279, by rfl⟩ : syracuseStep 1063039 = 1594559) B1594559
theorem B3192959 : Blo 838352 3192959 := bstep (se 1 (by rfl) ⟨2394719, by rfl⟩ : syracuseStep 3192959 = 4789439) B4789439
theorem B3193627 : Blo 838352 3193627 := bstep (se 1 (by rfl) ⟨2395220, by rfl⟩ : syracuseStep 3193627 = 4790441) B4790441
theorem B1260425 : Blo 838352 1260425 := bstep (se 2 (by rfl) ⟨472659, by rfl⟩ : syracuseStep 1260425 = 945319) B945319
theorem B1260647 : Blo 838352 1260647 := bstep (se 1 (by rfl) ⟨945485, by rfl⟩ : syracuseStep 1260647 = 1890971) B1890971
theorem B1260959 : Blo 838352 1260959 := bstep (se 1 (by rfl) ⟨945719, by rfl⟩ : syracuseStep 1260959 = 1891439) B1891439
theorem B2014703 : Blo 838352 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B1195879 : Blo 838352 1195879 := bstep (se 1 (by rfl) ⟨896909, by rfl⟩ : syracuseStep 1195879 = 1793819) B1793819
theorem B1261481 : Blo 838352 1261481 := bstep (se 2 (by rfl) ⟨473055, by rfl⟩ : syracuseStep 1261481 = 946111) B946111
theorem B6373403 : Blo 838352 6373403 := bstep (se 1 (by rfl) ⟨4780052, by rfl⟩ : syracuseStep 6373403 = 9560105) B9560105
theorem B1261751 : Blo 838352 1261751 := bstep (se 1 (by rfl) ⟨946313, by rfl⟩ : syracuseStep 1261751 = 1892627) B1892627
theorem B1261865 : Blo 838352 1261865 := bstep (se 2 (by rfl) ⟨473199, by rfl⟩ : syracuseStep 1261865 = 946399) B946399
theorem B1262249 : Blo 838352 1262249 := bstep (se 2 (by rfl) ⟨473343, by rfl⟩ : syracuseStep 1262249 = 946687) B946687
theorem B1262375 : Blo 838352 1262375 := bstep (se 1 (by rfl) ⟨946781, by rfl⟩ : syracuseStep 1262375 = 1893563) B1893563
theorem B9586349 : Blo 838352 9586349 := bstep (se 3 (by rfl) ⟨1797440, by rfl⟩ : syracuseStep 9586349 = 3594881) B3594881
theorem B7194683 : Blo 838352 7194683 := bstep (se 1 (by rfl) ⟨5396012, by rfl⟩ : syracuseStep 7194683 = 10792025) B10792025
theorem B18172025 : Blo 838352 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B1886561 : Blo 838352 1886561 := bstep (se 2 (by rfl) ⟨707460, by rfl⟩ : syracuseStep 1886561 = 1414921) B1414921
theorem B2836943 : Blo 838352 2836943 := bstep (se 1 (by rfl) ⟨2127707, by rfl⟩ : syracuseStep 2836943 = 4255415) B4255415
theorem B838431 : Blo 838352 838431 := bstep (se 1 (by rfl) ⟨628823, by rfl⟩ : syracuseStep 838431 = 1257647) B1257647
theorem B6900653 : Blo 838352 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B6048719 : Blo 838352 6048719 := bstep (se 1 (by rfl) ⟨4536539, by rfl⟩ : syracuseStep 6048719 = 9073079) B9073079
theorem B2018297 : Blo 838352 2018297 := bstep (se 2 (by rfl) ⟨756861, by rfl⟩ : syracuseStep 2018297 = 1513723) B1513723
theorem B2837753 : Blo 838352 2837753 := bstep (se 2 (by rfl) ⟨1064157, by rfl⟩ : syracuseStep 2837753 = 2128315) B2128315
theorem B167955859 : Blo 838352 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B839327 : Blo 838352 839327 := bstep (se 1 (by rfl) ⟨629495, by rfl⟩ : syracuseStep 839327 = 1258991) B1258991
theorem B839455 : Blo 838352 839455 := bstep (se 1 (by rfl) ⟨629591, by rfl⟩ : syracuseStep 839455 = 1259183) B1259183
theorem B14372963 : Blo 838352 14372963 := bstep (se 1 (by rfl) ⟨10779722, by rfl⟩ : syracuseStep 14372963 = 21559445) B21559445
theorem B839887 : Blo 838352 839887 := bstep (se 1 (by rfl) ⟨629915, by rfl⟩ : syracuseStep 839887 = 1259831) B1259831
theorem B4247801 : Blo 838352 4247801 := bstep (se 2 (by rfl) ⟨1592925, by rfl⟩ : syracuseStep 4247801 = 3185851) B3185851
theorem B839935 : Blo 838352 839935 := bstep (se 1 (by rfl) ⟨629951, by rfl⟩ : syracuseStep 839935 = 1259903) B1259903
theorem B840095 : Blo 838352 840095 := bstep (se 1 (by rfl) ⟨630071, by rfl⟩ : syracuseStep 840095 = 1260143) B1260143
theorem B1364527 : Blo 838352 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B2839535 : Blo 838352 2839535 := bstep (se 1 (by rfl) ⟨2129651, by rfl⟩ : syracuseStep 2839535 = 4259303) B4259303
theorem B2839643 : Blo 838352 2839643 := bstep (se 1 (by rfl) ⟨2129732, by rfl⟩ : syracuseStep 2839643 = 4259465) B4259465
theorem B840935 : Blo 838352 840935 := bstep (se 1 (by rfl) ⟨630701, by rfl⟩ : syracuseStep 840935 = 1261403) B1261403
theorem B6378749 : Blo 838352 6378749 := bstep (se 3 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 6378749 = 2392031) B2392031
theorem B5396219 : Blo 838352 5396219 := bstep (se 1 (by rfl) ⟨4047164, by rfl⟩ : syracuseStep 5396219 = 8094329) B8094329
theorem B1595371 : Blo 838352 1595371 := bstep (se 1 (by rfl) ⟨1196528, by rfl⟩ : syracuseStep 1595371 = 2393057) B2393057
theorem B2021449 : Blo 838352 2021449 := bstep (se 2 (by rfl) ⟨758043, by rfl⟩ : syracuseStep 2021449 = 1516087) B1516087
theorem B841831 : Blo 838352 841831 := bstep (se 1 (by rfl) ⟨631373, by rfl⟩ : syracuseStep 841831 = 1262747) B1262747
theorem B9230543 : Blo 838352 9230543 := bstep (se 1 (by rfl) ⟨6922907, by rfl⟩ : syracuseStep 9230543 = 13845815) B13845815
theorem B1595675 : Blo 838352 1595675 := bstep (se 1 (by rfl) ⟨1196756, by rfl⟩ : syracuseStep 1595675 = 2393513) B2393513
theorem B4315447 : Blo 838352 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B1793033 : Blo 838352 1793033 := bstep (se 2 (by rfl) ⟨672387, by rfl⟩ : syracuseStep 1793033 = 1344775) B1344775
theorem B2841911 : Blo 838352 2841911 := bstep (se 1 (by rfl) ⟨2131433, by rfl⟩ : syracuseStep 2841911 = 4262867) B4262867
theorem B1892015 : Blo 838352 1892015 := bstep (se 1 (by rfl) ⟨1419011, by rfl⟩ : syracuseStep 1892015 = 2838023) B2838023
theorem B7167689 : Blo 838352 7167689 := bstep (se 2 (by rfl) ⟨2687883, by rfl⟩ : syracuseStep 7167689 = 5375767) B5375767
theorem B8642477 : Blo 838352 8642477 := bstep (se 3 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 8642477 = 3240929) B3240929
theorem B6381665 : Blo 838352 6381665 := bstep (se 2 (by rfl) ⟨2393124, by rfl⟩ : syracuseStep 6381665 = 4786249) B4786249
theorem B1599031 : Blo 838352 1599031 := bstep (se 1 (by rfl) ⟨1199273, by rfl⟩ : syracuseStep 1599031 = 2398547) B2398547
theorem B2124569 : Blo 838352 2124569 := bstep (se 2 (by rfl) ⟨796713, by rfl⟩ : syracuseStep 2124569 = 1593427) B1593427
theorem B31058939 : Blo 838352 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B945895 : Blo 838352 945895 := bstep (se 1 (by rfl) ⟨709421, by rfl⟩ : syracuseStep 945895 = 1418843) B1418843
theorem B2551999 : Blo 838352 2551999 := bstep (se 1 (by rfl) ⟨1913999, by rfl⟩ : syracuseStep 2551999 = 3827999) B3827999
theorem B2126807 : Blo 838352 2126807 := bstep (se 1 (by rfl) ⟨1595105, by rfl⟩ : syracuseStep 2126807 = 3190211) B3190211
theorem B947227 : Blo 838352 947227 := bstep (se 1 (by rfl) ⟨710420, by rfl⟩ : syracuseStep 947227 = 1420841) B1420841
theorem B4781693 : Blo 838352 4781693 := bstep (se 3 (by rfl) ⟨896567, by rfl⟩ : syracuseStep 4781693 = 1793135) B1793135
theorem B5371667 : Blo 838352 5371667 := bstep (se 1 (by rfl) ⟨4028750, by rfl⟩ : syracuseStep 5371667 = 8057501) B8057501
theorem B2128943 : Blo 838352 2128943 := bstep (se 1 (by rfl) ⟨1596707, by rfl⟩ : syracuseStep 2128943 = 3193415) B3193415
theorem B5831777 : Blo 838352 5831777 := bstep (se 2 (by rfl) ⟨2186916, by rfl⟩ : syracuseStep 5831777 = 4373833) B4373833
theorem B11632019 : Blo 838352 11632019 := bstep (se 1 (by rfl) ⟨8724014, by rfl⟩ : syracuseStep 11632019 = 17448029) B17448029
theorem B8061191 : Blo 838352 8061191 := bstep (se 1 (by rfl) ⟨6045893, by rfl⟩ : syracuseStep 8061191 = 12091787) B12091787
theorem B8061727 : Blo 838352 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B6390899 : Blo 838352 6390899 := bstep (se 1 (by rfl) ⟨4793174, by rfl⟩ : syracuseStep 6390899 = 9586349) B9586349
theorem B2688871 : Blo 838352 2688871 := bstep (se 1 (by rfl) ⟨2016653, by rfl⟩ : syracuseStep 2688871 = 4033307) B4033307
theorem B4032479 : Blo 838352 4032479 := bstep (se 1 (by rfl) ⟨3024359, by rfl⟩ : syracuseStep 4032479 = 6048719) B6048719
theorem B2132041 : Blo 838352 2132041 := bstep (se 2 (by rfl) ⟨799515, by rfl⟩ : syracuseStep 2132041 = 1599031) B1599031
theorem B10227647 : Blo 838352 10227647 := bstep (se 1 (by rfl) ⟨7670735, by rfl⟩ : syracuseStep 10227647 = 15341471) B15341471
theorem B2560415 : Blo 838352 2560415 := bstep (se 1 (by rfl) ⟨1920311, by rfl⟩ : syracuseStep 2560415 = 3840623) B3840623
theorem B223941145 : Blo 838352 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B34576105 : Blo 838352 34576105 := bstep (se 2 (by rfl) ⟨12966039, by rfl⟩ : syracuseStep 34576105 = 25932079) B25932079
theorem B1416379 : Blo 838352 1416379 := bstep (se 1 (by rfl) ⟨1062284, by rfl⟩ : syracuseStep 1416379 = 2124569) B2124569
theorem B5382125 : Blo 838352 5382125 := bstep (se 3 (by rfl) ⟨1009148, by rfl⟩ : syracuseStep 5382125 = 2018297) B2018297
theorem B2695265 : Blo 838352 2695265 := bstep (se 2 (by rfl) ⟨1010724, by rfl⟩ : syracuseStep 2695265 = 2021449) B2021449
theorem B1417385 : Blo 838352 1417385 := bstep (se 2 (by rfl) ⟨531519, by rfl⟩ : syracuseStep 1417385 = 1063039) B1063039
theorem B1417871 : Blo 838352 1417871 := bstep (se 1 (by rfl) ⟨1063403, by rfl⟩ : syracuseStep 1417871 = 2126807) B2126807
theorem B10232905 : Blo 838352 10232905 := bstep (se 2 (by rfl) ⟨3837339, by rfl⟩ : syracuseStep 10232905 = 7674679) B7674679
theorem B3187795 : Blo 838352 3187795 := bstep (se 1 (by rfl) ⟨2390846, by rfl⟩ : syracuseStep 3187795 = 4781693) B4781693
theorem B3581111 : Blo 838352 3581111 := bstep (se 1 (by rfl) ⟨2685833, by rfl⟩ : syracuseStep 3581111 = 5371667) B5371667
theorem B1419295 : Blo 838352 1419295 := bstep (se 1 (by rfl) ⟨1064471, by rfl⟩ : syracuseStep 1419295 = 2128943) B2128943
theorem B36907397 : Blo 838352 36907397 := bstep (se 4 (by rfl) ⟨3460068, by rfl⟩ : syracuseStep 36907397 = 6920137) B6920137
theorem B4796455 : Blo 838352 4796455 := bstep (se 1 (by rfl) ⟨3597341, by rfl⟩ : syracuseStep 4796455 = 7194683) B7194683
theorem B1257707 : Blo 838352 1257707 := bstep (se 1 (by rfl) ⟨943280, by rfl⟩ : syracuseStep 1257707 = 1886561) B1886561
theorem B4600435 : Blo 838352 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B3191471 : Blo 838352 3191471 := bstep (se 1 (by rfl) ⟨2393603, by rfl⟩ : syracuseStep 3191471 = 4787207) B4787207
theorem B1618663 : Blo 838352 1618663 := bstep (se 1 (by rfl) ⟨1213997, by rfl⟩ : syracuseStep 1618663 = 2427995) B2427995
theorem B9581975 : Blo 838352 9581975 := bstep (se 1 (by rfl) ⟨7186481, by rfl⟩ : syracuseStep 9581975 = 14372963) B14372963
theorem B2831867 : Blo 838352 2831867 := bstep (se 1 (by rfl) ⟨2123900, by rfl⟩ : syracuseStep 2831867 = 4247801) B4247801
theorem B13613255 : Blo 838352 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B1063783 : Blo 838352 1063783 := bstep (se 1 (by rfl) ⟨797837, by rfl⟩ : syracuseStep 1063783 = 1595675) B1595675
theorem B3587399 : Blo 838352 3587399 := bstep (se 1 (by rfl) ⟨2690549, by rfl⟩ : syracuseStep 3587399 = 5381099) B5381099
theorem B1195355 : Blo 838352 1195355 := bstep (se 1 (by rfl) ⟨896516, by rfl⟩ : syracuseStep 1195355 = 1793033) B1793033
theorem B12107353 : Blo 838352 12107353 := bstep (se 2 (by rfl) ⟨4540257, by rfl⟩ : syracuseStep 12107353 = 9080515) B9080515
theorem B1261193 : Blo 838352 1261193 := bstep (se 2 (by rfl) ⟨472947, by rfl⟩ : syracuseStep 1261193 = 945895) B945895
theorem B1261343 : Blo 838352 1261343 := bstep (se 1 (by rfl) ⟨946007, by rfl⟩ : syracuseStep 1261343 = 1892015) B1892015
theorem B3031337 : Blo 838352 3031337 := bstep (se 2 (by rfl) ⟨1136751, by rfl⟩ : syracuseStep 3031337 = 2273503) B2273503
theorem B3588731 : Blo 838352 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B1819369 : Blo 838352 1819369 := bstep (se 2 (by rfl) ⟨682263, by rfl⟩ : syracuseStep 1819369 = 1364527) B1364527
theorem B1262969 : Blo 838352 1262969 := bstep (se 2 (by rfl) ⟨473613, by rfl⟩ : syracuseStep 1262969 = 947227) B947227
theorem B23905843 : Blo 838352 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B1886687 : Blo 838352 1886687 := bstep (se 1 (by rfl) ⟨1415015, by rfl⟩ : syracuseStep 1886687 = 2830031) B2830031
theorem B1887047 : Blo 838352 1887047 := bstep (se 1 (by rfl) ⟨1415285, by rfl⟩ : syracuseStep 1887047 = 2830571) B2830571
theorem B838567 : Blo 838352 838567 := bstep (se 1 (by rfl) ⟨628925, by rfl⟩ : syracuseStep 838567 = 1257851) B1257851
theorem B838639 : Blo 838352 838639 := bstep (se 1 (by rfl) ⟨628979, by rfl⟩ : syracuseStep 838639 = 1257959) B1257959
theorem B5753929 : Blo 838352 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B838887 : Blo 838352 838887 := bstep (se 1 (by rfl) ⟨629165, by rfl⟩ : syracuseStep 838887 = 1258331) B1258331
theorem B1887515 : Blo 838352 1887515 := bstep (se 1 (by rfl) ⟨1415636, by rfl⟩ : syracuseStep 1887515 = 2831273) B2831273
theorem B4246991 : Blo 838352 4246991 := bstep (se 1 (by rfl) ⟨3185243, by rfl⟩ : syracuseStep 4246991 = 6370487) B6370487
theorem B1887695 : Blo 838352 1887695 := bstep (se 1 (by rfl) ⟨1415771, by rfl⟩ : syracuseStep 1887695 = 2831543) B2831543
theorem B31018717 : Blo 838352 31018717 := bstep (se 3 (by rfl) ⟨5816009, by rfl⟩ : syracuseStep 31018717 = 11632019) B11632019
theorem B839407 : Blo 838352 839407 := bstep (se 1 (by rfl) ⟨629555, by rfl⟩ : syracuseStep 839407 = 1259111) B1259111
theorem B3592457 : Blo 838352 3592457 := bstep (se 2 (by rfl) ⟨1347171, by rfl⟩ : syracuseStep 3592457 = 2694343) B2694343
theorem B840283 : Blo 838352 840283 := bstep (se 1 (by rfl) ⟨630212, by rfl⟩ : syracuseStep 840283 = 1260425) B1260425
theorem B3887851 : Blo 838352 3887851 := bstep (se 1 (by rfl) ⟨2915888, by rfl⟩ : syracuseStep 3887851 = 5831777) B5831777
theorem B840431 : Blo 838352 840431 := bstep (se 1 (by rfl) ⟨630323, by rfl⟩ : syracuseStep 840431 = 1260647) B1260647
theorem B840639 : Blo 838352 840639 := bstep (se 1 (by rfl) ⟨630479, by rfl⟩ : syracuseStep 840639 = 1260959) B1260959
theorem B1594505 : Blo 838352 1594505 := bstep (se 2 (by rfl) ⟨597939, by rfl⟩ : syracuseStep 1594505 = 1195879) B1195879
theorem B840987 : Blo 838352 840987 := bstep (se 1 (by rfl) ⟨630740, by rfl⟩ : syracuseStep 840987 = 1261481) B1261481
theorem B4248935 : Blo 838352 4248935 := bstep (se 1 (by rfl) ⟨3186701, by rfl⟩ : syracuseStep 4248935 = 6373403) B6373403
theorem B2839967 : Blo 838352 2839967 := bstep (se 1 (by rfl) ⟨2129975, by rfl⟩ : syracuseStep 2839967 = 4259951) B4259951
theorem B841167 : Blo 838352 841167 := bstep (se 1 (by rfl) ⟨630875, by rfl⟩ : syracuseStep 841167 = 1261751) B1261751
theorem B841243 : Blo 838352 841243 := bstep (se 1 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 841243 = 1261865) B1261865
theorem B841499 : Blo 838352 841499 := bstep (se 1 (by rfl) ⟨631124, by rfl⟩ : syracuseStep 841499 = 1262249) B1262249
theorem B841583 : Blo 838352 841583 := bstep (se 1 (by rfl) ⟨631187, by rfl⟩ : syracuseStep 841583 = 1262375) B1262375
theorem B2841047 : Blo 838352 2841047 := bstep (se 1 (by rfl) ⟨2130785, by rfl⟩ : syracuseStep 2841047 = 4261571) B4261571
theorem B12114683 : Blo 838352 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B1891295 : Blo 838352 1891295 := bstep (se 1 (by rfl) ⟨1418471, by rfl⟩ : syracuseStep 1891295 = 2836943) B2836943
theorem B1891835 : Blo 838352 1891835 := bstep (se 1 (by rfl) ⟨1418876, by rfl⟩ : syracuseStep 1891835 = 2837753) B2837753
theorem B15359507 : Blo 838352 15359507 := bstep (se 1 (by rfl) ⟨11519630, by rfl⟩ : syracuseStep 15359507 = 23039261) B23039261
theorem B139616135 : Blo 838352 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B7168439 : Blo 838352 7168439 := bstep (se 1 (by rfl) ⟨5376329, by rfl⟩ : syracuseStep 7168439 = 10752659) B10752659
theorem B1893023 : Blo 838352 1893023 := bstep (se 1 (by rfl) ⟨1419767, by rfl⟩ : syracuseStep 1893023 = 2839535) B2839535
theorem B1893095 : Blo 838352 1893095 := bstep (se 1 (by rfl) ⟨1419821, by rfl⟩ : syracuseStep 1893095 = 2839643) B2839643
theorem B4252499 : Blo 838352 4252499 := bstep (se 1 (by rfl) ⟨3189374, by rfl⟩ : syracuseStep 4252499 = 6378749) B6378749
theorem B1893257 : Blo 838352 1893257 := bstep (se 2 (by rfl) ⟨709971, by rfl⟩ : syracuseStep 1893257 = 1419943) B1419943
theorem B943231 : Blo 838352 943231 := bstep (se 1 (by rfl) ⟨707423, by rfl⟩ : syracuseStep 943231 = 1414847) B1414847
theorem B1598591 : Blo 838352 1598591 := bstep (se 1 (by rfl) ⟨1198943, by rfl⟩ : syracuseStep 1598591 = 2397887) B2397887
theorem B3597479 : Blo 838352 3597479 := bstep (se 1 (by rfl) ⟨2698109, by rfl⟩ : syracuseStep 3597479 = 5396219) B5396219
theorem B1893545 : Blo 838352 1893545 := bstep (se 2 (by rfl) ⟨710079, by rfl⟩ : syracuseStep 1893545 = 1420159) B1420159
theorem B6153695 : Blo 838352 6153695 := bstep (se 1 (by rfl) ⟨4615271, by rfl⟩ : syracuseStep 6153695 = 9230543) B9230543
theorem B2123243 : Blo 838352 2123243 := bstep (se 1 (by rfl) ⟨1592432, by rfl⟩ : syracuseStep 2123243 = 3184865) B3184865
theorem B1894607 : Blo 838352 1894607 := bstep (se 1 (by rfl) ⟨1420955, by rfl⟩ : syracuseStep 1894607 = 2841911) B2841911
theorem B944383 : Blo 838352 944383 := bstep (se 1 (by rfl) ⟨708287, by rfl⟩ : syracuseStep 944383 = 1416575) B1416575
theorem B4778459 : Blo 838352 4778459 := bstep (se 1 (by rfl) ⟨3583844, by rfl⟩ : syracuseStep 4778459 = 7167689) B7167689
theorem B5761651 : Blo 838352 5761651 := bstep (se 1 (by rfl) ⟨4321238, by rfl⟩ : syracuseStep 5761651 = 8642477) B8642477
theorem B4254443 : Blo 838352 4254443 := bstep (se 1 (by rfl) ⟨3190832, by rfl⟩ : syracuseStep 4254443 = 6381665) B6381665
theorem B944959 : Blo 838352 944959 := bstep (se 1 (by rfl) ⟨708719, by rfl⟩ : syracuseStep 944959 = 1417439) B1417439
theorem B3402665 : Blo 838352 3402665 := bstep (se 2 (by rfl) ⟨1275999, by rfl⟩ : syracuseStep 3402665 = 2551999) B2551999
theorem B4254929 : Blo 838352 4254929 := bstep (se 2 (by rfl) ⟨1595598, by rfl⟩ : syracuseStep 4254929 = 3191197) B3191197
theorem B2125055 : Blo 838352 2125055 := bstep (se 1 (by rfl) ⟨1593791, by rfl⟩ : syracuseStep 2125055 = 3187583) B3187583
theorem B945823 : Blo 838352 945823 := bstep (se 1 (by rfl) ⟨709367, by rfl⟩ : syracuseStep 945823 = 1418735) B1418735
theorem B51737075 : Blo 838352 51737075 := bstep (se 1 (by rfl) ⟨38802806, by rfl⟩ : syracuseStep 51737075 = 77605613) B77605613
theorem B20705959 : Blo 838352 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B946975 : Blo 838352 946975 := bstep (se 1 (by rfl) ⟨710231, by rfl⟩ : syracuseStep 946975 = 1420463) B1420463
theorem B2126675 : Blo 838352 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B398488691 : Blo 838352 398488691 := bstep (se 1 (by rfl) ⟨298866518, by rfl⟩ : syracuseStep 398488691 = 597733037) B597733037
theorem B2127161 : Blo 838352 2127161 := bstep (se 2 (by rfl) ⟨797685, by rfl⟩ : syracuseStep 2127161 = 1595371) B1595371
theorem B4258169 : Blo 838352 4258169 := bstep (se 2 (by rfl) ⟨1596813, by rfl⟩ : syracuseStep 4258169 = 3193627) B3193627
theorem B98401007 : Blo 838352 98401007 := bstep (se 1 (by rfl) ⟨73800755, by rfl⟩ : syracuseStep 98401007 = 147601511) B147601511
theorem B2128639 : Blo 838352 2128639 := bstep (se 1 (by rfl) ⟨1596479, by rfl⟩ : syracuseStep 2128639 = 3192959) B3192959
theorem B1343135 : Blo 838352 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B5374127 : Blo 838352 5374127 := bstep (se 1 (by rfl) ⟨4030595, by rfl⟩ : syracuseStep 5374127 = 8061191) B8061191
theorem B2392487 : Blo 838352 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B4260599 : Blo 838352 4260599 := bstep (se 1 (by rfl) ⟨3195449, by rfl⟩ : syracuseStep 4260599 = 6390899) B6390899
theorem B2425825 : Blo 838352 2425825 := bstep (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) B1819369
theorem B10748969 : Blo 838352 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B2688319 : Blo 838352 2688319 := bstep (se 1 (by rfl) ⟨2016239, by rfl⟩ : syracuseStep 2688319 = 4032479) B4032479
theorem B6818431 : Blo 838352 6818431 := bstep (se 1 (by rfl) ⟨5113823, by rfl⟩ : syracuseStep 6818431 = 10227647) B10227647
theorem B2394971 : Blo 838352 2394971 := bstep (se 1 (by rfl) ⟨1796228, by rfl⟩ : syracuseStep 2394971 = 3592457) B3592457
theorem B1062636509 : Blo 838352 1062636509 := bstep (se 3 (by rfl) ⟨199244345, by rfl⟩ : syracuseStep 1062636509 = 398488691) B398488691
theorem B7671905 : Blo 838352 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B41358289 : Blo 838352 41358289 := bstep (se 2 (by rfl) ⟨15509358, by rfl⟩ : syracuseStep 41358289 = 31018717) B31018717
theorem B6395273 : Blo 838352 6395273 := bstep (se 2 (by rfl) ⟨2398227, by rfl⟩ : syracuseStep 6395273 = 4796455) B4796455
theorem B298588193 : Blo 838352 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B2398319 : Blo 838352 2398319 := bstep (se 1 (by rfl) ⟨1798739, by rfl⟩ : syracuseStep 2398319 = 3597479) B3597479
theorem B6133913 : Blo 838352 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B5183801 : Blo 838352 5183801 := bstep (se 2 (by rfl) ⟨1943925, by rfl⟩ : syracuseStep 5183801 = 3887851) B3887851
theorem B4102463 : Blo 838352 4102463 := bstep (se 1 (by rfl) ⟨3076847, by rfl⟩ : syracuseStep 4102463 = 6153695) B6153695
theorem B1415495 : Blo 838352 1415495 := bstep (se 1 (by rfl) ⟨1061621, by rfl⟩ : syracuseStep 1415495 = 2123243) B2123243
theorem B3185639 : Blo 838352 3185639 := bstep (se 1 (by rfl) ⟨2389229, by rfl⟩ : syracuseStep 3185639 = 4778459) B4778459
theorem B2268443 : Blo 838352 2268443 := bstep (se 1 (by rfl) ⟨1701332, by rfl⟩ : syracuseStep 2268443 = 3402665) B3402665
theorem B1416703 : Blo 838352 1416703 := bstep (se 1 (by rfl) ⟨1062527, by rfl⟩ : syracuseStep 1416703 = 2125055) B2125055
theorem B1417783 : Blo 838352 1417783 := bstep (se 1 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 1417783 = 2126675) B2126675
theorem B1418107 : Blo 838352 1418107 := bstep (se 1 (by rfl) ⟨1063580, by rfl⟩ : syracuseStep 1418107 = 2127161) B2127161
theorem B3187613 : Blo 838352 3187613 := bstep (se 3 (by rfl) ⟨597677, by rfl⟩ : syracuseStep 3187613 = 1195355) B1195355
theorem B1418377 : Blo 838352 1418377 := bstep (se 2 (by rfl) ⟨531891, by rfl⟩ : syracuseStep 1418377 = 1063783) B1063783
theorem B895423 : Blo 838352 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B6827773 : Blo 838352 6827773 := bstep (se 3 (by rfl) ⟨1280207, by rfl⟩ : syracuseStep 6827773 = 2560415) B2560415
theorem B13643873 : Blo 838352 13643873 := bstep (se 2 (by rfl) ⟨5116452, by rfl⟩ : syracuseStep 13643873 = 10232905) B10232905
theorem B1257641 : Blo 838352 1257641 := bstep (se 2 (by rfl) ⟨471615, by rfl⟩ : syracuseStep 1257641 = 943231) B943231
theorem B1257791 : Blo 838352 1257791 := bstep (se 1 (by rfl) ⟨943343, by rfl⟩ : syracuseStep 1257791 = 1886687) B1886687
theorem B1258031 : Blo 838352 1258031 := bstep (se 1 (by rfl) ⟨943523, by rfl⟩ : syracuseStep 1258031 = 1887047) B1887047
theorem B1258343 : Blo 838352 1258343 := bstep (se 1 (by rfl) ⟨943757, by rfl⟩ : syracuseStep 1258343 = 1887515) B1887515
theorem B2831327 : Blo 838352 2831327 := bstep (se 1 (by rfl) ⟨2123495, by rfl⟩ : syracuseStep 2831327 = 4246991) B4246991
theorem B1258463 : Blo 838352 1258463 := bstep (se 1 (by rfl) ⟨943847, by rfl⟩ : syracuseStep 1258463 = 1887695) B1887695
theorem B3585161 : Blo 838352 3585161 := bstep (se 2 (by rfl) ⟨1344435, by rfl⟩ : syracuseStep 3585161 = 2688871) B2688871
theorem B1259177 : Blo 838352 1259177 := bstep (se 2 (by rfl) ⟨472191, by rfl⟩ : syracuseStep 1259177 = 944383) B944383
theorem B7682201 : Blo 838352 7682201 := bstep (se 2 (by rfl) ⟨2880825, by rfl⟩ : syracuseStep 7682201 = 5761651) B5761651
theorem B2832623 : Blo 838352 2832623 := bstep (se 1 (by rfl) ⟨2124467, by rfl⟩ : syracuseStep 2832623 = 4248935) B4248935
theorem B1259945 : Blo 838352 1259945 := bstep (se 2 (by rfl) ⟨472479, by rfl⟩ : syracuseStep 1259945 = 944959) B944959
theorem B8076455 : Blo 838352 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B1260863 : Blo 838352 1260863 := bstep (se 1 (by rfl) ⟨945647, by rfl⟩ : syracuseStep 1260863 = 1891295) B1891295
theorem B1261097 : Blo 838352 1261097 := bstep (se 2 (by rfl) ⟨472911, by rfl⟩ : syracuseStep 1261097 = 945823) B945823
theorem B1261223 : Blo 838352 1261223 := bstep (se 1 (by rfl) ⟨945917, by rfl⟩ : syracuseStep 1261223 = 1891835) B1891835
theorem B10239671 : Blo 838352 10239671 := bstep (se 1 (by rfl) ⟨7679753, by rfl⟩ : syracuseStep 10239671 = 15359507) B15359507
theorem B93077423 : Blo 838352 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B3588083 : Blo 838352 3588083 := bstep (se 1 (by rfl) ⟨2691062, by rfl⟩ : syracuseStep 3588083 = 5382125) B5382125
theorem B1262015 : Blo 838352 1262015 := bstep (se 1 (by rfl) ⟨946511, by rfl⟩ : syracuseStep 1262015 = 1893023) B1893023
theorem B1262063 : Blo 838352 1262063 := bstep (se 1 (by rfl) ⟨946547, by rfl⟩ : syracuseStep 1262063 = 1893095) B1893095
theorem B2834999 : Blo 838352 2834999 := bstep (se 1 (by rfl) ⟨2126249, by rfl⟩ : syracuseStep 2834999 = 4252499) B4252499
theorem B1262171 : Blo 838352 1262171 := bstep (se 1 (by rfl) ⟨946628, by rfl⟩ : syracuseStep 1262171 = 1893257) B1893257
theorem B1065727 : Blo 838352 1065727 := bstep (se 1 (by rfl) ⟨799295, by rfl⟩ : syracuseStep 1065727 = 1598591) B1598591
theorem B1262363 : Blo 838352 1262363 := bstep (se 1 (by rfl) ⟨946772, by rfl⟩ : syracuseStep 1262363 = 1893545) B1893545
theorem B27607945 : Blo 838352 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B1262633 : Blo 838352 1262633 := bstep (se 2 (by rfl) ⟨473487, by rfl⟩ : syracuseStep 1262633 = 946975) B946975
theorem B1263071 : Blo 838352 1263071 := bstep (se 1 (by rfl) ⟨947303, by rfl⟩ : syracuseStep 1263071 = 1894607) B1894607
theorem B2836295 : Blo 838352 2836295 := bstep (se 1 (by rfl) ⟨2127221, by rfl⟩ : syracuseStep 2836295 = 4254443) B4254443
theorem B2836619 : Blo 838352 2836619 := bstep (se 1 (by rfl) ⟨2127464, by rfl⟩ : syracuseStep 2836619 = 4254929) B4254929
theorem B838471 : Blo 838352 838471 := bstep (se 1 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 838471 = 1257707) B1257707
theorem B34491383 : Blo 838352 34491383 := bstep (se 1 (by rfl) ⟨25868537, by rfl⟩ : syracuseStep 34491383 = 51737075) B51737075
theorem B1887911 : Blo 838352 1887911 := bstep (se 1 (by rfl) ⟨1415933, by rfl⟩ : syracuseStep 1887911 = 2831867) B2831867
theorem B2838185 : Blo 838352 2838185 := bstep (se 2 (by rfl) ⟨1064319, by rfl⟩ : syracuseStep 2838185 = 2128639) B2128639
theorem B1888505 : Blo 838352 1888505 := bstep (se 2 (by rfl) ⟨708189, by rfl⟩ : syracuseStep 1888505 = 1416379) B1416379
theorem B2838779 : Blo 838352 2838779 := bstep (se 1 (by rfl) ⟨2129084, by rfl⟩ : syracuseStep 2838779 = 4258169) B4258169
theorem B16143137 : Blo 838352 16143137 := bstep (se 2 (by rfl) ⟨6053676, by rfl⟩ : syracuseStep 16143137 = 12107353) B12107353
theorem B840795 : Blo 838352 840795 := bstep (se 1 (by rfl) ⟨630596, by rfl⟩ : syracuseStep 840795 = 1261193) B1261193
theorem B840895 : Blo 838352 840895 := bstep (se 1 (by rfl) ⟨630671, by rfl⟩ : syracuseStep 840895 = 1261343) B1261343
theorem B2020891 : Blo 838352 2020891 := bstep (se 1 (by rfl) ⟨1515668, by rfl⟩ : syracuseStep 2020891 = 3031337) B3031337
theorem B841979 : Blo 838352 841979 := bstep (se 1 (by rfl) ⟨631484, by rfl⟩ : syracuseStep 841979 = 1262969) B1262969
theorem B4250393 : Blo 838352 4250393 := bstep (se 2 (by rfl) ⟨1593897, by rfl⟩ : syracuseStep 4250393 = 3187795) B3187795
theorem B1892393 : Blo 838352 1892393 := bstep (se 2 (by rfl) ⟨709647, by rfl⟩ : syracuseStep 1892393 = 1419295) B1419295
theorem B2842721 : Blo 838352 2842721 := bstep (se 2 (by rfl) ⟨1066020, by rfl⟩ : syracuseStep 2842721 = 2132041) B2132041
theorem B4252013 : Blo 838352 4252013 := bstep (se 3 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 4252013 = 1594505) B1594505
theorem B1893311 : Blo 838352 1893311 := bstep (se 1 (by rfl) ⟨1419983, by rfl⟩ : syracuseStep 1893311 = 2839967) B2839967
theorem B1894031 : Blo 838352 1894031 := bstep (se 1 (by rfl) ⟨1420523, by rfl⟩ : syracuseStep 1894031 = 2841047) B2841047
theorem B1796843 : Blo 838352 1796843 := bstep (se 1 (by rfl) ⟨1347632, by rfl⟩ : syracuseStep 1796843 = 2695265) B2695265
theorem B944923 : Blo 838352 944923 := bstep (se 1 (by rfl) ⟨708692, by rfl⟩ : syracuseStep 944923 = 1417385) B1417385
theorem B4778959 : Blo 838352 4778959 := bstep (se 1 (by rfl) ⟨3584219, by rfl⟩ : syracuseStep 4778959 = 7168439) B7168439
theorem B945247 : Blo 838352 945247 := bstep (se 1 (by rfl) ⟨708935, by rfl⟩ : syracuseStep 945247 = 1417871) B1417871
theorem B2387407 : Blo 838352 2387407 := bstep (se 1 (by rfl) ⟨1790555, by rfl⟩ : syracuseStep 2387407 = 3581111) B3581111
theorem B2158217 : Blo 838352 2158217 := bstep (se 2 (by rfl) ⟨809331, by rfl⟩ : syracuseStep 2158217 = 1618663) B1618663
theorem B24604931 : Blo 838352 24604931 := bstep (se 1 (by rfl) ⟨18453698, by rfl⟩ : syracuseStep 24604931 = 36907397) B36907397
theorem B262402685 : Blo 838352 262402685 := bstep (se 3 (by rfl) ⟨49200503, by rfl⟩ : syracuseStep 262402685 = 98401007) B98401007
theorem B46101473 : Blo 838352 46101473 := bstep (se 2 (by rfl) ⟨17288052, by rfl⟩ : syracuseStep 46101473 = 34576105) B34576105
theorem B127497829 : Blo 838352 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B2127647 : Blo 838352 2127647 := bstep (se 1 (by rfl) ⟨1595735, by rfl⟩ : syracuseStep 2127647 = 3191471) B3191471
theorem B6387983 : Blo 838352 6387983 := bstep (se 1 (by rfl) ⟨4790987, by rfl⟩ : syracuseStep 6387983 = 9581975) B9581975
theorem B9075503 : Blo 838352 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B2391599 : Blo 838352 2391599 := bstep (se 1 (by rfl) ⟨1793699, by rfl⟩ : syracuseStep 2391599 = 3587399) B3587399
theorem B5114603 : Blo 838352 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B4263515 : Blo 838352 4263515 := bstep (se 1 (by rfl) ⟨3197636, by rfl⟩ : syracuseStep 4263515 = 6395273) B6395273
theorem B3183209 : Blo 838352 3183209 := bstep (se 2 (by rfl) ⟨1193703, by rfl⟩ : syracuseStep 3183209 = 2387407) B2387407
theorem B4791581 : Blo 838352 4791581 := bstep (se 3 (by rfl) ⟨898421, by rfl⟩ : syracuseStep 4791581 = 1796843) B1796843
theorem B2694521 : Blo 838352 2694521 := bstep (se 2 (by rfl) ⟨1010445, by rfl⟩ : syracuseStep 2694521 = 2020891) B2020891
theorem B1418431 : Blo 838352 1418431 := bstep (se 1 (by rfl) ⟨1063823, by rfl⟩ : syracuseStep 1418431 = 2127647) B2127647
theorem B5121467 : Blo 838352 5121467 := bstep (se 1 (by rfl) ⟨3841100, by rfl⟩ : syracuseStep 5121467 = 7682201) B7682201
theorem B5384303 : Blo 838352 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B6826447 : Blo 838352 6826447 := bstep (se 1 (by rfl) ⟨5119835, by rfl⟩ : syracuseStep 6826447 = 10239671) B10239671
theorem B3582751 : Blo 838352 3582751 := bstep (se 1 (by rfl) ⟨2687063, by rfl⟩ : syracuseStep 3582751 = 5374127) B5374127
theorem B65613149 : Blo 838352 65613149 := bstep (se 3 (by rfl) ⟨12302465, by rfl⟩ : syracuseStep 65613149 = 24604931) B24604931
theorem B1420969 : Blo 838352 1420969 := bstep (se 2 (by rfl) ⟨532863, by rfl⟩ : syracuseStep 1420969 = 1065727) B1065727
theorem B36810593 : Blo 838352 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B3584425 : Blo 838352 3584425 := bstep (se 2 (by rfl) ⟨1344159, by rfl⟩ : syracuseStep 3584425 = 2688319) B2688319
theorem B1258607 : Blo 838352 1258607 := bstep (se 1 (by rfl) ⟨943955, by rfl⟩ : syracuseStep 1258607 = 1887911) B1887911
theorem B1259003 : Blo 838352 1259003 := bstep (se 1 (by rfl) ⟨944252, by rfl⟩ : syracuseStep 1259003 = 1888505) B1888505
theorem B10762091 : Blo 838352 10762091 := bstep (se 1 (by rfl) ⟨8071568, by rfl⟩ : syracuseStep 10762091 = 16143137) B16143137
theorem B1193897 : Blo 838352 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B9091241 : Blo 838352 9091241 := bstep (se 2 (by rfl) ⟨3409215, by rfl⟩ : syracuseStep 9091241 = 6818431) B6818431
theorem B1259897 : Blo 838352 1259897 := bstep (se 2 (by rfl) ⟨472461, by rfl⟩ : syracuseStep 1259897 = 944923) B944923
theorem B6371945 : Blo 838352 6371945 := bstep (se 2 (by rfl) ⟨2389479, by rfl⟩ : syracuseStep 6371945 = 4778959) B4778959
theorem B1260329 : Blo 838352 1260329 := bstep (se 2 (by rfl) ⟨472623, by rfl⟩ : syracuseStep 1260329 = 945247) B945247
theorem B3455867 : Blo 838352 3455867 := bstep (se 1 (by rfl) ⟨2591900, by rfl⟩ : syracuseStep 3455867 = 5183801) B5183801
theorem B2734975 : Blo 838352 2734975 := bstep (se 1 (by rfl) ⟨2051231, by rfl⟩ : syracuseStep 2734975 = 4102463) B4102463
theorem B2833595 : Blo 838352 2833595 := bstep (se 1 (by rfl) ⟨2125196, by rfl⟩ : syracuseStep 2833595 = 4250393) B4250393
theorem B1261595 : Blo 838352 1261595 := bstep (se 1 (by rfl) ⟨946196, by rfl⟩ : syracuseStep 1261595 = 1892393) B1892393
theorem B2834675 : Blo 838352 2834675 := bstep (se 1 (by rfl) ⟨2126006, by rfl⟩ : syracuseStep 2834675 = 4252013) B4252013
theorem B1262207 : Blo 838352 1262207 := bstep (se 1 (by rfl) ⟨946655, by rfl⟩ : syracuseStep 1262207 = 1893311) B1893311
theorem B1262687 : Blo 838352 1262687 := bstep (se 1 (by rfl) ⟨947015, by rfl⟩ : syracuseStep 1262687 = 1894031) B1894031
theorem B2833697357 : Blo 838352 2833697357 := bstep (se 3 (by rfl) ⟨531318254, by rfl⟩ : syracuseStep 2833697357 = 1062636509) B1062636509
theorem B9095915 : Blo 838352 9095915 := bstep (se 1 (by rfl) ⟨6821936, by rfl⟩ : syracuseStep 9095915 = 13643873) B13643873
theorem B838427 : Blo 838352 838427 := bstep (se 1 (by rfl) ⟨628820, by rfl⟩ : syracuseStep 838427 = 1257641) B1257641
theorem B838527 : Blo 838352 838527 := bstep (se 1 (by rfl) ⟨628895, by rfl⟩ : syracuseStep 838527 = 1257791) B1257791
theorem B838687 : Blo 838352 838687 := bstep (se 1 (by rfl) ⟨629015, by rfl⟩ : syracuseStep 838687 = 1258031) B1258031
theorem B174935123 : Blo 838352 174935123 := bstep (se 1 (by rfl) ⟨131201342, by rfl⟩ : syracuseStep 174935123 = 262402685) B262402685
theorem B838895 : Blo 838352 838895 := bstep (se 1 (by rfl) ⟨629171, by rfl⟩ : syracuseStep 838895 = 1258343) B1258343
theorem B1887551 : Blo 838352 1887551 := bstep (se 1 (by rfl) ⟨1415663, by rfl⟩ : syracuseStep 1887551 = 2831327) B2831327
theorem B838975 : Blo 838352 838975 := bstep (se 1 (by rfl) ⟨629231, by rfl⟩ : syracuseStep 838975 = 1258463) B1258463
theorem B6049181 : Blo 838352 6049181 := bstep (se 3 (by rfl) ⟨1134221, by rfl⟩ : syracuseStep 6049181 = 2268443) B2268443
theorem B839451 : Blo 838352 839451 := bstep (se 1 (by rfl) ⟨629588, by rfl⟩ : syracuseStep 839451 = 1259177) B1259177
theorem B1888415 : Blo 838352 1888415 := bstep (se 1 (by rfl) ⟨1416311, by rfl⟩ : syracuseStep 1888415 = 2832623) B2832623
theorem B839963 : Blo 838352 839963 := bstep (se 1 (by rfl) ⟨629972, by rfl⟩ : syracuseStep 839963 = 1259945) B1259945
theorem B6050335 : Blo 838352 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B1888937 : Blo 838352 1888937 := bstep (se 2 (by rfl) ⟨708351, by rfl⟩ : syracuseStep 1888937 = 1416703) B1416703
theorem B840575 : Blo 838352 840575 := bstep (se 1 (by rfl) ⟨630431, by rfl⟩ : syracuseStep 840575 = 1260863) B1260863
theorem B840731 : Blo 838352 840731 := bstep (se 1 (by rfl) ⟨630548, by rfl⟩ : syracuseStep 840731 = 1261097) B1261097
theorem B1594399 : Blo 838352 1594399 := bstep (se 1 (by rfl) ⟨1195799, by rfl⟩ : syracuseStep 1594399 = 2391599) B2391599
theorem B840815 : Blo 838352 840815 := bstep (se 1 (by rfl) ⟨630611, by rfl⟩ : syracuseStep 840815 = 1261223) B1261223
theorem B62051615 : Blo 838352 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B1594991 : Blo 838352 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B841343 : Blo 838352 841343 := bstep (se 1 (by rfl) ⟨631007, by rfl⟩ : syracuseStep 841343 = 1262015) B1262015
theorem B841375 : Blo 838352 841375 := bstep (se 1 (by rfl) ⟨631031, by rfl⟩ : syracuseStep 841375 = 1262063) B1262063
theorem B1889999 : Blo 838352 1889999 := bstep (se 1 (by rfl) ⟨1417499, by rfl⟩ : syracuseStep 1889999 = 2834999) B2834999
theorem B841447 : Blo 838352 841447 := bstep (se 1 (by rfl) ⟨631085, by rfl⟩ : syracuseStep 841447 = 1262171) B1262171
theorem B2840399 : Blo 838352 2840399 := bstep (se 1 (by rfl) ⟨2130299, by rfl⟩ : syracuseStep 2840399 = 4260599) B4260599
theorem B841575 : Blo 838352 841575 := bstep (se 1 (by rfl) ⟨631181, by rfl⟩ : syracuseStep 841575 = 1262363) B1262363
theorem B7165979 : Blo 838352 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B841755 : Blo 838352 841755 := bstep (se 1 (by rfl) ⟨631316, by rfl⟩ : syracuseStep 841755 = 1262633) B1262633
theorem B1890377 : Blo 838352 1890377 := bstep (se 2 (by rfl) ⟨708891, by rfl⟩ : syracuseStep 1890377 = 1417783) B1417783
theorem B842047 : Blo 838352 842047 := bstep (se 1 (by rfl) ⟨631535, by rfl⟩ : syracuseStep 842047 = 1263071) B1263071
theorem B1890809 : Blo 838352 1890809 := bstep (se 2 (by rfl) ⟨709053, by rfl⟩ : syracuseStep 1890809 = 1418107) B1418107
theorem B1890863 : Blo 838352 1890863 := bstep (se 1 (by rfl) ⟨1418147, by rfl⟩ : syracuseStep 1890863 = 2836295) B2836295
theorem B3234433 : Blo 838352 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B1891079 : Blo 838352 1891079 := bstep (se 1 (by rfl) ⟨1418309, by rfl⟩ : syracuseStep 1891079 = 2836619) B2836619
theorem B1891169 : Blo 838352 1891169 := bstep (se 2 (by rfl) ⟨709188, by rfl⟩ : syracuseStep 1891169 = 1418377) B1418377
theorem B1596647 : Blo 838352 1596647 := bstep (se 1 (by rfl) ⟨1197485, by rfl⟩ : syracuseStep 1596647 = 2394971) B2394971
theorem B22994255 : Blo 838352 22994255 := bstep (se 1 (by rfl) ⟨17245691, by rfl⟩ : syracuseStep 22994255 = 34491383) B34491383
theorem B1892123 : Blo 838352 1892123 := bstep (se 1 (by rfl) ⟨1419092, by rfl⟩ : syracuseStep 1892123 = 2838185) B2838185
theorem B1892519 : Blo 838352 1892519 := bstep (se 1 (by rfl) ⟨1419389, by rfl⟩ : syracuseStep 1892519 = 2838779) B2838779
theorem B199058795 : Blo 838352 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B1598879 : Blo 838352 1598879 := bstep (se 1 (by rfl) ⟨1199159, by rfl⟩ : syracuseStep 1598879 = 2398319) B2398319
theorem B4089275 : Blo 838352 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B943663 : Blo 838352 943663 := bstep (se 1 (by rfl) ⟨707747, by rfl⟩ : syracuseStep 943663 = 1415495) B1415495
theorem B2123759 : Blo 838352 2123759 := bstep (se 1 (by rfl) ⟨1592819, by rfl⟩ : syracuseStep 2123759 = 3185639) B3185639
theorem B9103697 : Blo 838352 9103697 := bstep (se 2 (by rfl) ⟨3413886, by rfl⟩ : syracuseStep 9103697 = 6827773) B6827773
theorem B1895147 : Blo 838352 1895147 := bstep (se 1 (by rfl) ⟨1421360, by rfl⟩ : syracuseStep 1895147 = 2842721) B2842721
theorem B2125075 : Blo 838352 2125075 := bstep (se 1 (by rfl) ⟨1593806, by rfl⟩ : syracuseStep 2125075 = 3187613) B3187613
theorem B55144385 : Blo 838352 55144385 := bstep (se 2 (by rfl) ⟨20679144, by rfl⟩ : syracuseStep 55144385 = 41358289) B41358289
theorem B169997105 : Blo 838352 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B1438811 : Blo 838352 1438811 := bstep (se 1 (by rfl) ⟨1079108, by rfl⟩ : syracuseStep 1438811 = 2158217) B2158217
theorem B30734315 : Blo 838352 30734315 := bstep (se 1 (by rfl) ⟨23050736, by rfl⟩ : syracuseStep 30734315 = 46101473) B46101473
theorem B2390107 : Blo 838352 2390107 := bstep (se 1 (by rfl) ⟨1792580, by rfl⟩ : syracuseStep 2390107 = 3585161) B3585161
theorem B4258655 : Blo 838352 4258655 := bstep (se 1 (by rfl) ⟨3193991, by rfl⟩ : syracuseStep 4258655 = 6387983) B6387983
theorem B2392055 : Blo 838352 2392055 := bstep (se 1 (by rfl) ⟨1794041, by rfl⟩ : syracuseStep 2392055 = 3588083) B3588083
theorem B3409735 : Blo 838352 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B6063943 : Blo 838352 6063943 := bstep (se 1 (by rfl) ⟨4547957, by rfl⟩ : syracuseStep 6063943 = 9095915) B9095915
theorem B116623415 : Blo 838352 116623415 := bstep (se 1 (by rfl) ⟨87467561, by rfl⟩ : syracuseStep 116623415 = 174935123) B174935123
theorem B4032787 : Blo 838352 4032787 := bstep (se 1 (by rfl) ⟨3024590, by rfl⟩ : syracuseStep 4032787 = 6049181) B6049181
theorem B4263677 : Blo 838352 4263677 := bstep (se 3 (by rfl) ⟨799439, by rfl⟩ : syracuseStep 4263677 = 1598879) B1598879
theorem B3183725 : Blo 838352 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B8067113 : Blo 838352 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B2726183 : Blo 838352 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B3414311 : Blo 838352 3414311 := bstep (se 1 (by rfl) ⟨2560733, by rfl⟩ : syracuseStep 3414311 = 5121467) B5121467
theorem B1415839 : Blo 838352 1415839 := bstep (se 1 (by rfl) ⟨1061879, by rfl⟩ : syracuseStep 1415839 = 2123759) B2123759
theorem B6069131 : Blo 838352 6069131 := bstep (se 1 (by rfl) ⟨4551848, by rfl⟩ : syracuseStep 6069131 = 9103697) B9103697
theorem B3186809 : Blo 838352 3186809 := bstep (se 2 (by rfl) ⟨1195053, by rfl⟩ : syracuseStep 3186809 = 2390107) B2390107
theorem B959207 : Blo 838352 959207 := bstep (se 1 (by rfl) ⟨719405, by rfl⟩ : syracuseStep 959207 = 1438811) B1438811
theorem B3646633 : Blo 838352 3646633 := bstep (se 2 (by rfl) ⟨1367487, by rfl⟩ : syracuseStep 3646633 = 2734975) B2734975
theorem B20489543 : Blo 838352 20489543 := bstep (se 1 (by rfl) ⟨15367157, by rfl⟩ : syracuseStep 20489543 = 30734315) B30734315
theorem B2303911 : Blo 838352 2303911 := bstep (se 1 (by rfl) ⟨1727933, by rfl⟩ : syracuseStep 2303911 = 3455867) B3455867
theorem B1258217 : Blo 838352 1258217 := bstep (se 2 (by rfl) ⟨471831, by rfl⟩ : syracuseStep 1258217 = 943663) B943663
theorem B1258367 : Blo 838352 1258367 := bstep (se 1 (by rfl) ⟨943775, by rfl⟩ : syracuseStep 1258367 = 1887551) B1887551
theorem B1258943 : Blo 838352 1258943 := bstep (se 1 (by rfl) ⟨944207, by rfl⟩ : syracuseStep 1258943 = 1888415) B1888415
theorem B1259291 : Blo 838352 1259291 := bstep (se 1 (by rfl) ⟨944468, by rfl⟩ : syracuseStep 1259291 = 1888937) B1888937
theorem B41367743 : Blo 838352 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B1259999 : Blo 838352 1259999 := bstep (se 1 (by rfl) ⟨944999, by rfl⟩ : syracuseStep 1259999 = 1889999) B1889999
theorem B1570585301 : Blo 838352 1570585301 := bstep (se 7 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 1570585301 = 36810593) B36810593
theorem B1260251 : Blo 838352 1260251 := bstep (se 1 (by rfl) ⟨945188, by rfl⟩ : syracuseStep 1260251 = 1890377) B1890377
theorem B1260539 : Blo 838352 1260539 := bstep (se 1 (by rfl) ⟨945404, by rfl⟩ : syracuseStep 1260539 = 1890809) B1890809
theorem B2833433 : Blo 838352 2833433 := bstep (se 2 (by rfl) ⟨1062537, by rfl⟩ : syracuseStep 2833433 = 2125075) B2125075
theorem B1260575 : Blo 838352 1260575 := bstep (se 1 (by rfl) ⟨945431, by rfl⟩ : syracuseStep 1260575 = 1890863) B1890863
theorem B1260719 : Blo 838352 1260719 := bstep (se 1 (by rfl) ⟨945539, by rfl⟩ : syracuseStep 1260719 = 1891079) B1891079
theorem B1260779 : Blo 838352 1260779 := bstep (se 1 (by rfl) ⟨945584, by rfl⟩ : syracuseStep 1260779 = 1891169) B1891169
theorem B1064431 : Blo 838352 1064431 := bstep (se 1 (by rfl) ⟨798323, by rfl⟩ : syracuseStep 1064431 = 1596647) B1596647
theorem B3194387 : Blo 838352 3194387 := bstep (se 1 (by rfl) ⟨2395790, by rfl⟩ : syracuseStep 3194387 = 4791581) B4791581
theorem B1261415 : Blo 838352 1261415 := bstep (se 1 (by rfl) ⟨946061, by rfl⟩ : syracuseStep 1261415 = 1892123) B1892123
theorem B1261679 : Blo 838352 1261679 := bstep (se 1 (by rfl) ⟨946259, by rfl⟩ : syracuseStep 1261679 = 1892519) B1892519
theorem B3589535 : Blo 838352 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B1263431 : Blo 838352 1263431 := bstep (se 1 (by rfl) ⟨947573, by rfl⟩ : syracuseStep 1263431 = 1895147) B1895147
theorem B113331403 : Blo 838352 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B839071 : Blo 838352 839071 := bstep (se 1 (by rfl) ⟨629303, by rfl⟩ : syracuseStep 839071 = 1258607) B1258607
theorem B4312577 : Blo 838352 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B839335 : Blo 838352 839335 := bstep (se 1 (by rfl) ⟨629501, by rfl⟩ : syracuseStep 839335 = 1259003) B1259003
theorem B839931 : Blo 838352 839931 := bstep (se 1 (by rfl) ⟨629948, by rfl⟩ : syracuseStep 839931 = 1259897) B1259897
theorem B4247963 : Blo 838352 4247963 := bstep (se 1 (by rfl) ⟨3185972, by rfl⟩ : syracuseStep 4247963 = 6371945) B6371945
theorem B840219 : Blo 838352 840219 := bstep (se 1 (by rfl) ⟨630164, by rfl⟩ : syracuseStep 840219 = 1260329) B1260329
theorem B2839103 : Blo 838352 2839103 := bstep (se 1 (by rfl) ⟨2129327, by rfl⟩ : syracuseStep 2839103 = 4258655) B4258655
theorem B1889063 : Blo 838352 1889063 := bstep (se 1 (by rfl) ⟨1416797, by rfl⟩ : syracuseStep 1889063 = 2833595) B2833595
theorem B1594703 : Blo 838352 1594703 := bstep (se 1 (by rfl) ⟨1196027, by rfl⟩ : syracuseStep 1594703 = 2392055) B2392055
theorem B841063 : Blo 838352 841063 := bstep (se 1 (by rfl) ⟨630797, by rfl⟩ : syracuseStep 841063 = 1261595) B1261595
theorem B1889783 : Blo 838352 1889783 := bstep (se 1 (by rfl) ⟨1417337, by rfl⟩ : syracuseStep 1889783 = 2834675) B2834675
theorem B841471 : Blo 838352 841471 := bstep (se 1 (by rfl) ⟨631103, by rfl⟩ : syracuseStep 841471 = 1262207) B1262207
theorem B841791 : Blo 838352 841791 := bstep (se 1 (by rfl) ⟨631343, by rfl⟩ : syracuseStep 841791 = 1262687) B1262687
theorem B1891241 : Blo 838352 1891241 := bstep (se 2 (by rfl) ⟨709215, by rfl⟩ : syracuseStep 1891241 = 1418431) B1418431
theorem B1889131571 : Blo 838352 1889131571 := bstep (se 1 (by rfl) ⟨1416848678, by rfl⟩ : syracuseStep 1889131571 = 2833697357) B2833697357
theorem B2842343 : Blo 838352 2842343 := bstep (se 1 (by rfl) ⟨2131757, by rfl⟩ : syracuseStep 2842343 = 4263515) B4263515
theorem B2122139 : Blo 838352 2122139 := bstep (se 1 (by rfl) ⟨1591604, by rfl⟩ : syracuseStep 2122139 = 3183209) B3183209
theorem B9101929 : Blo 838352 9101929 := bstep (se 2 (by rfl) ⟨3413223, by rfl⟩ : syracuseStep 9101929 = 6826447) B6826447
theorem B4777001 : Blo 838352 4777001 := bstep (se 2 (by rfl) ⟨1791375, by rfl⟩ : syracuseStep 4777001 = 3582751) B3582751
theorem B1893599 : Blo 838352 1893599 := bstep (se 1 (by rfl) ⟨1420199, by rfl⟩ : syracuseStep 1893599 = 2840399) B2840399
theorem B4777319 : Blo 838352 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B4253309 : Blo 838352 4253309 := bstep (se 3 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 4253309 = 1594991) B1594991
theorem B15329503 : Blo 838352 15329503 := bstep (se 1 (by rfl) ⟨11497127, by rfl⟩ : syracuseStep 15329503 = 22994255) B22994255
theorem B1894625 : Blo 838352 1894625 := bstep (se 2 (by rfl) ⟨710484, by rfl⟩ : syracuseStep 1894625 = 1420969) B1420969
theorem B1796347 : Blo 838352 1796347 := bstep (se 1 (by rfl) ⟨1347260, by rfl⟩ : syracuseStep 1796347 = 2694521) B2694521
theorem B4779233 : Blo 838352 4779233 := bstep (se 2 (by rfl) ⟨1792212, by rfl⟩ : syracuseStep 4779233 = 3584425) B3584425
theorem B132705863 : Blo 838352 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B2125865 : Blo 838352 2125865 := bstep (se 2 (by rfl) ⟨797199, by rfl⟩ : syracuseStep 2125865 = 1594399) B1594399
theorem B43742099 : Blo 838352 43742099 := bstep (se 1 (by rfl) ⟨32806574, by rfl⟩ : syracuseStep 43742099 = 65613149) B65613149
theorem B36762923 : Blo 838352 36762923 := bstep (se 1 (by rfl) ⟨27572192, by rfl⟩ : syracuseStep 36762923 = 55144385) B55144385
theorem B7174727 : Blo 838352 7174727 := bstep (se 1 (by rfl) ⟨5381045, by rfl⟩ : syracuseStep 7174727 = 10762091) B10762091
theorem B6060827 : Blo 838352 6060827 := bstep (se 1 (by rfl) ⟨4545620, by rfl⟩ : syracuseStep 6060827 = 9091241) B9091241
theorem B2393023 : Blo 838352 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B2557885 : Blo 838352 2557885 := bstep (se 3 (by rfl) ⟨479603, by rfl⟩ : syracuseStep 2557885 = 959207) B959207
theorem B5377049 : Blo 838352 5377049 := bstep (se 2 (by rfl) ⟨2016393, by rfl⟩ : syracuseStep 5377049 = 4032787) B4032787
theorem B5378075 : Blo 838352 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B1414759 : Blo 838352 1414759 := bstep (se 1 (by rfl) ⟨1061069, by rfl⟩ : syracuseStep 1414759 = 2122139) B2122139
theorem B3184667 : Blo 838352 3184667 := bstep (se 1 (by rfl) ⟨2388500, by rfl⟩ : syracuseStep 3184667 = 4777001) B4777001
theorem B3184879 : Blo 838352 3184879 := bstep (se 1 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 3184879 = 4777319) B4777319
theorem B3186155 : Blo 838352 3186155 := bstep (se 1 (by rfl) ⟨2389616, by rfl⟩ : syracuseStep 3186155 = 4779233) B4779233
theorem B1417243 : Blo 838352 1417243 := bstep (se 1 (by rfl) ⟨1062932, by rfl⟩ : syracuseStep 1417243 = 2125865) B2125865
theorem B4040551 : Blo 838352 4040551 := bstep (se 1 (by rfl) ⟨3030413, by rfl⟩ : syracuseStep 4040551 = 6060827) B6060827
theorem B1419241 : Blo 838352 1419241 := bstep (se 2 (by rfl) ⟨532215, by rfl⟩ : syracuseStep 1419241 = 1064431) B1064431
theorem B12135905 : Blo 838352 12135905 := bstep (se 2 (by rfl) ⟨4550964, by rfl⟩ : syracuseStep 12135905 = 9101929) B9101929
theorem B9580517 : Blo 838352 9580517 := bstep (se 4 (by rfl) ⟨898173, by rfl⟩ : syracuseStep 9580517 = 1796347) B1796347
theorem B4862177 : Blo 838352 4862177 := bstep (se 2 (by rfl) ⟨1823316, by rfl⟩ : syracuseStep 4862177 = 3646633) B3646633
theorem B2831975 : Blo 838352 2831975 := bstep (se 1 (by rfl) ⟨2123981, by rfl⟩ : syracuseStep 2831975 = 4247963) B4247963
theorem B1259375 : Blo 838352 1259375 := bstep (se 1 (by rfl) ⟨944531, by rfl⟩ : syracuseStep 1259375 = 1889063) B1889063
theorem B1063135 : Blo 838352 1063135 := bstep (se 1 (by rfl) ⟨797351, by rfl⟩ : syracuseStep 1063135 = 1594703) B1594703
theorem B1259855 : Blo 838352 1259855 := bstep (se 1 (by rfl) ⟨944891, by rfl⟩ : syracuseStep 1259855 = 1889783) B1889783
theorem B2276207 : Blo 838352 2276207 := bstep (se 1 (by rfl) ⟨1707155, by rfl⟩ : syracuseStep 2276207 = 3414311) B3414311
theorem B151108537 : Blo 838352 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B4046087 : Blo 838352 4046087 := bstep (se 1 (by rfl) ⟨3034565, by rfl⟩ : syracuseStep 4046087 = 6069131) B6069131
theorem B1260827 : Blo 838352 1260827 := bstep (se 1 (by rfl) ⟨945620, by rfl⟩ : syracuseStep 1260827 = 1891241) B1891241
theorem B1259421047 : Blo 838352 1259421047 := bstep (se 1 (by rfl) ⟨944565785, by rfl⟩ : syracuseStep 1259421047 = 1889131571) B1889131571
theorem B1262399 : Blo 838352 1262399 := bstep (se 1 (by rfl) ⟨946799, by rfl⟩ : syracuseStep 1262399 = 1893599) B1893599
theorem B2835539 : Blo 838352 2835539 := bstep (se 1 (by rfl) ⟨2126654, by rfl⟩ : syracuseStep 2835539 = 4253309) B4253309
theorem B1263083 : Blo 838352 1263083 := bstep (se 1 (by rfl) ⟨947312, by rfl⟩ : syracuseStep 1263083 = 1894625) B1894625
theorem B838811 : Blo 838352 838811 := bstep (se 1 (by rfl) ⟨629108, by rfl⟩ : syracuseStep 838811 = 1258217) B1258217
theorem B838911 : Blo 838352 838911 := bstep (se 1 (by rfl) ⟨629183, by rfl⟩ : syracuseStep 838911 = 1258367) B1258367
theorem B1887785 : Blo 838352 1887785 := bstep (se 2 (by rfl) ⟨707919, by rfl⟩ : syracuseStep 1887785 = 1415839) B1415839
theorem B839295 : Blo 838352 839295 := bstep (se 1 (by rfl) ⟨629471, by rfl⟩ : syracuseStep 839295 = 1258943) B1258943
theorem B839527 : Blo 838352 839527 := bstep (se 1 (by rfl) ⟨629645, by rfl⟩ : syracuseStep 839527 = 1259291) B1259291
theorem B27578495 : Blo 838352 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B839999 : Blo 838352 839999 := bstep (se 1 (by rfl) ⟨629999, by rfl⟩ : syracuseStep 839999 = 1259999) B1259999
theorem B1047056867 : Blo 838352 1047056867 := bstep (se 1 (by rfl) ⟨785292650, by rfl⟩ : syracuseStep 1047056867 = 1570585301) B1570585301
theorem B840167 : Blo 838352 840167 := bstep (se 1 (by rfl) ⟨630125, by rfl⟩ : syracuseStep 840167 = 1260251) B1260251
theorem B840359 : Blo 838352 840359 := bstep (se 1 (by rfl) ⟨630269, by rfl⟩ : syracuseStep 840359 = 1260539) B1260539
theorem B1888955 : Blo 838352 1888955 := bstep (se 1 (by rfl) ⟨1416716, by rfl⟩ : syracuseStep 1888955 = 2833433) B2833433
theorem B840383 : Blo 838352 840383 := bstep (se 1 (by rfl) ⟨630287, by rfl⟩ : syracuseStep 840383 = 1260575) B1260575
theorem B840479 : Blo 838352 840479 := bstep (se 1 (by rfl) ⟨630359, by rfl⟩ : syracuseStep 840479 = 1260719) B1260719
theorem B840519 : Blo 838352 840519 := bstep (se 1 (by rfl) ⟨630389, by rfl⟩ : syracuseStep 840519 = 1260779) B1260779
theorem B840943 : Blo 838352 840943 := bstep (se 1 (by rfl) ⟨630707, by rfl⟩ : syracuseStep 840943 = 1261415) B1261415
theorem B841119 : Blo 838352 841119 := bstep (se 1 (by rfl) ⟨630839, by rfl⟩ : syracuseStep 841119 = 1261679) B1261679
theorem B842287 : Blo 838352 842287 := bstep (se 1 (by rfl) ⟨631715, by rfl⟩ : syracuseStep 842287 = 1263431) B1263431
theorem B77748943 : Blo 838352 77748943 := bstep (se 1 (by rfl) ⟨58311707, by rfl⟩ : syracuseStep 77748943 = 116623415) B116623415
theorem B2875051 : Blo 838352 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B4546313 : Blo 838352 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B8085257 : Blo 838352 8085257 := bstep (se 2 (by rfl) ⟨3031971, by rfl⟩ : syracuseStep 8085257 = 6063943) B6063943
theorem B2842451 : Blo 838352 2842451 := bstep (se 1 (by rfl) ⟨2131838, by rfl⟩ : syracuseStep 2842451 = 4263677) B4263677
theorem B3071881 : Blo 838352 3071881 := bstep (se 2 (by rfl) ⟨1151955, by rfl⟩ : syracuseStep 3071881 = 2303911) B2303911
theorem B20439337 : Blo 838352 20439337 := bstep (se 2 (by rfl) ⟨7664751, by rfl⟩ : syracuseStep 20439337 = 15329503) B15329503
theorem B1892735 : Blo 838352 1892735 := bstep (se 1 (by rfl) ⟨1419551, by rfl⟩ : syracuseStep 1892735 = 2839103) B2839103
theorem B2122483 : Blo 838352 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B1894895 : Blo 838352 1894895 := bstep (se 1 (by rfl) ⟨1421171, by rfl⟩ : syracuseStep 1894895 = 2842343) B2842343
theorem B2124539 : Blo 838352 2124539 := bstep (se 1 (by rfl) ⟨1593404, by rfl⟩ : syracuseStep 2124539 = 3186809) B3186809
theorem B7269821 : Blo 838352 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B13659695 : Blo 838352 13659695 := bstep (se 1 (by rfl) ⟨10244771, by rfl⟩ : syracuseStep 13659695 = 20489543) B20489543
theorem B88470575 : Blo 838352 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B29161399 : Blo 838352 29161399 := bstep (se 1 (by rfl) ⟨21871049, by rfl⟩ : syracuseStep 29161399 = 43742099) B43742099
theorem B24508615 : Blo 838352 24508615 := bstep (se 1 (by rfl) ⟨18381461, by rfl⟩ : syracuseStep 24508615 = 36762923) B36762923
theorem B4783151 : Blo 838352 4783151 := bstep (se 1 (by rfl) ⟨3587363, by rfl⟩ : syracuseStep 4783151 = 7174727) B7174727
theorem B2129591 : Blo 838352 2129591 := bstep (se 1 (by rfl) ⟨1597193, by rfl⟩ : syracuseStep 2129591 = 3194387) B3194387
theorem B3410513 : Blo 838352 3410513 := bstep (se 2 (by rfl) ⟨1278942, by rfl⟩ : syracuseStep 3410513 = 2557885) B2557885
theorem B18385663 : Blo 838352 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B1416359 : Blo 838352 1416359 := bstep (se 1 (by rfl) ⟨1062269, by rfl⟩ : syracuseStep 1416359 = 2124539) B2124539
theorem B32678153 : Blo 838352 32678153 := bstep (se 2 (by rfl) ⟨12254307, by rfl⟩ : syracuseStep 32678153 = 24508615) B24508615
theorem B1417513 : Blo 838352 1417513 := bstep (se 2 (by rfl) ⟨531567, by rfl⟩ : syracuseStep 1417513 = 1063135) B1063135
theorem B1517471 : Blo 838352 1517471 := bstep (se 1 (by rfl) ⟨1138103, by rfl⟩ : syracuseStep 1517471 = 2276207) B2276207
theorem B3188767 : Blo 838352 3188767 := bstep (se 1 (by rfl) ⟨2391575, by rfl⟩ : syracuseStep 3188767 = 4783151) B4783151
theorem B2697391 : Blo 838352 2697391 := bstep (se 1 (by rfl) ⟨2023043, by rfl⟩ : syracuseStep 2697391 = 4046087) B4046087
theorem B1419727 : Blo 838352 1419727 := bstep (se 1 (by rfl) ⟨1064795, by rfl⟩ : syracuseStep 1419727 = 2129591) B2129591
theorem B2829977 : Blo 838352 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B3190697 : Blo 838352 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B3584699 : Blo 838352 3584699 := bstep (se 1 (by rfl) ⟨2688524, by rfl⟩ : syracuseStep 3584699 = 5377049) B5377049
theorem B1258523 : Blo 838352 1258523 := bstep (se 1 (by rfl) ⟨943892, by rfl⟩ : syracuseStep 1258523 = 1887785) B1887785
theorem B5387401 : Blo 838352 5387401 := bstep (se 2 (by rfl) ⟨2020275, by rfl⟩ : syracuseStep 5387401 = 4040551) B4040551
theorem B3585383 : Blo 838352 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B698037911 : Blo 838352 698037911 := bstep (se 1 (by rfl) ⟨523528433, by rfl⟩ : syracuseStep 698037911 = 1047056867) B1047056867
theorem B1259303 : Blo 838352 1259303 := bstep (se 1 (by rfl) ⟨944477, by rfl⟩ : syracuseStep 1259303 = 1888955) B1888955
theorem B3030875 : Blo 838352 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B5390171 : Blo 838352 5390171 := bstep (se 1 (by rfl) ⟨4042628, by rfl⟩ : syracuseStep 5390171 = 8085257) B8085257
theorem B1261823 : Blo 838352 1261823 := bstep (se 1 (by rfl) ⟨946367, by rfl⟩ : syracuseStep 1261823 = 1892735) B1892735
theorem B1263263 : Blo 838352 1263263 := bstep (se 1 (by rfl) ⟨947447, by rfl⟩ : syracuseStep 1263263 = 1894895) B1894895
theorem B1886345 : Blo 838352 1886345 := bstep (se 2 (by rfl) ⟨707379, by rfl⟩ : syracuseStep 1886345 = 1414759) B1414759
theorem B38881865 : Blo 838352 38881865 := bstep (se 2 (by rfl) ⟨14580699, by rfl⟩ : syracuseStep 38881865 = 29161399) B29161399
theorem B4246505 : Blo 838352 4246505 := bstep (se 2 (by rfl) ⟨1592439, by rfl⟩ : syracuseStep 4246505 = 3184879) B3184879
theorem B103665257 : Blo 838352 103665257 := bstep (se 2 (by rfl) ⟨38874471, by rfl⟩ : syracuseStep 103665257 = 77748943) B77748943
theorem B1887983 : Blo 838352 1887983 := bstep (se 1 (by rfl) ⟨1415987, by rfl⟩ : syracuseStep 1887983 = 2831975) B2831975
theorem B839583 : Blo 838352 839583 := bstep (se 1 (by rfl) ⟨629687, by rfl⟩ : syracuseStep 839583 = 1259375) B1259375
theorem B201478049 : Blo 838352 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B839903 : Blo 838352 839903 := bstep (se 1 (by rfl) ⟨629927, by rfl⟩ : syracuseStep 839903 = 1259855) B1259855
theorem B840551 : Blo 838352 840551 := bstep (se 1 (by rfl) ⟨630413, by rfl⟩ : syracuseStep 840551 = 1260827) B1260827
theorem B1889657 : Blo 838352 1889657 := bstep (se 2 (by rfl) ⟨708621, by rfl⟩ : syracuseStep 1889657 = 1417243) B1417243
theorem B27252449 : Blo 838352 27252449 := bstep (se 2 (by rfl) ⟨10219668, by rfl⟩ : syracuseStep 27252449 = 20439337) B20439337
theorem B841599 : Blo 838352 841599 := bstep (se 1 (by rfl) ⟨631199, by rfl⟩ : syracuseStep 841599 = 1262399) B1262399
theorem B1890359 : Blo 838352 1890359 := bstep (se 1 (by rfl) ⟨1417769, by rfl⟩ : syracuseStep 1890359 = 2835539) B2835539
theorem B842055 : Blo 838352 842055 := bstep (se 1 (by rfl) ⟨631541, by rfl⟩ : syracuseStep 842055 = 1263083) B1263083
theorem B1892321 : Blo 838352 1892321 := bstep (se 2 (by rfl) ⟨709620, by rfl⟩ : syracuseStep 1892321 = 1419241) B1419241
theorem B2123111 : Blo 838352 2123111 := bstep (se 1 (by rfl) ⟨1592333, by rfl⟩ : syracuseStep 2123111 = 3184667) B3184667
theorem B2124103 : Blo 838352 2124103 := bstep (se 1 (by rfl) ⟨1593077, by rfl⟩ : syracuseStep 2124103 = 3186155) B3186155
theorem B1894967 : Blo 838352 1894967 := bstep (se 1 (by rfl) ⟨1421225, by rfl⟩ : syracuseStep 1894967 = 2842451) B2842451
theorem B4846547 : Blo 838352 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B8090603 : Blo 838352 8090603 := bstep (se 1 (by rfl) ⟨6067952, by rfl⟩ : syracuseStep 8090603 = 12135905) B12135905
theorem B9106463 : Blo 838352 9106463 := bstep (se 1 (by rfl) ⟨6829847, by rfl⟩ : syracuseStep 9106463 = 13659695) B13659695
theorem B6387011 : Blo 838352 6387011 := bstep (se 1 (by rfl) ⟨4790258, by rfl⟩ : syracuseStep 6387011 = 9580517) B9580517
theorem B3241451 : Blo 838352 3241451 := bstep (se 1 (by rfl) ⟨2431088, by rfl⟩ : syracuseStep 3241451 = 4862177) B4862177
theorem B58980383 : Blo 838352 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B3833401 : Blo 838352 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B839614031 : Blo 838352 839614031 := bstep (se 1 (by rfl) ⟨629710523, by rfl⟩ : syracuseStep 839614031 = 1259421047) B1259421047
theorem B4095841 : Blo 838352 4095841 := bstep (se 2 (by rfl) ⟨1535940, by rfl⟩ : syracuseStep 4095841 = 3071881) B3071881
theorem B14386085 : Blo 838352 14386085 := bstep (se 4 (by rfl) ⟨1348695, by rfl⟩ : syracuseStep 14386085 = 2697391) B2697391
theorem B25921243 : Blo 838352 25921243 := bstep (se 1 (by rfl) ⟨19440932, by rfl⟩ : syracuseStep 25921243 = 38881865) B38881865
theorem B69110171 : Blo 838352 69110171 := bstep (se 1 (by rfl) ⟨51832628, by rfl⟩ : syracuseStep 69110171 = 103665257) B103665257
theorem B134318699 : Blo 838352 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B24283901 : Blo 838352 24283901 := bstep (se 3 (by rfl) ⟨4553231, by rfl⟩ : syracuseStep 24283901 = 9106463) B9106463
theorem B24514217 : Blo 838352 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B1415407 : Blo 838352 1415407 := bstep (se 1 (by rfl) ⟨1061555, by rfl⟩ : syracuseStep 1415407 = 2123111) B2123111
theorem B7183201 : Blo 838352 7183201 := bstep (se 2 (by rfl) ⟨2693700, by rfl⟩ : syracuseStep 7183201 = 5387401) B5387401
theorem B1257563 : Blo 838352 1257563 := bstep (se 1 (by rfl) ⟨943172, by rfl⟩ : syracuseStep 1257563 = 1886345) B1886345
theorem B2273675 : Blo 838352 2273675 := bstep (se 1 (by rfl) ⟨1705256, by rfl⟩ : syracuseStep 2273675 = 3410513) B3410513
theorem B2831003 : Blo 838352 2831003 := bstep (se 1 (by rfl) ⟨2123252, by rfl⟩ : syracuseStep 2831003 = 4246505) B4246505
theorem B1258655 : Blo 838352 1258655 := bstep (se 1 (by rfl) ⟨943991, by rfl⟩ : syracuseStep 1258655 = 1887983) B1887983
theorem B2832137 : Blo 838352 2832137 := bstep (se 2 (by rfl) ⟨1062051, by rfl⟩ : syracuseStep 2832137 = 2124103) B2124103
theorem B1259771 : Blo 838352 1259771 := bstep (se 1 (by rfl) ⟨944828, by rfl⟩ : syracuseStep 1259771 = 1889657) B1889657
theorem B18168299 : Blo 838352 18168299 := bstep (se 1 (by rfl) ⟨13626224, by rfl⟩ : syracuseStep 18168299 = 27252449) B27252449
theorem B1260239 : Blo 838352 1260239 := bstep (se 1 (by rfl) ⟨945179, by rfl⟩ : syracuseStep 1260239 = 1890359) B1890359
theorem B1261547 : Blo 838352 1261547 := bstep (se 1 (by rfl) ⟨946160, by rfl⟩ : syracuseStep 1261547 = 1892321) B1892321
theorem B1263311 : Blo 838352 1263311 := bstep (se 1 (by rfl) ⟨947483, by rfl⟩ : syracuseStep 1263311 = 1894967) B1894967
theorem B1886651 : Blo 838352 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B3231031 : Blo 838352 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B5393735 : Blo 838352 5393735 := bstep (se 1 (by rfl) ⟨4045301, by rfl⟩ : syracuseStep 5393735 = 8090603) B8090603
theorem B839015 : Blo 838352 839015 := bstep (se 1 (by rfl) ⟨629261, by rfl⟩ : syracuseStep 839015 = 1258523) B1258523
theorem B465358607 : Blo 838352 465358607 := bstep (se 1 (by rfl) ⟨349018955, by rfl⟩ : syracuseStep 465358607 = 698037911) B698037911
theorem B839535 : Blo 838352 839535 := bstep (se 1 (by rfl) ⟨629651, by rfl⟩ : syracuseStep 839535 = 1259303) B1259303
theorem B5461121 : Blo 838352 5461121 := bstep (se 2 (by rfl) ⟨2047920, by rfl⟩ : syracuseStep 5461121 = 4095841) B4095841
theorem B2020583 : Blo 838352 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B3593447 : Blo 838352 3593447 := bstep (se 1 (by rfl) ⟨2695085, by rfl⟩ : syracuseStep 3593447 = 5390171) B5390171
theorem B841215 : Blo 838352 841215 := bstep (se 1 (by rfl) ⟨630911, by rfl⟩ : syracuseStep 841215 = 1261823) B1261823
theorem B1890017 : Blo 838352 1890017 := bstep (se 2 (by rfl) ⟨708756, by rfl⟩ : syracuseStep 1890017 = 1417513) B1417513
theorem B842175 : Blo 838352 842175 := bstep (se 1 (by rfl) ⟨631631, by rfl⟩ : syracuseStep 842175 = 1263263) B1263263
theorem B4251689 : Blo 838352 4251689 := bstep (se 2 (by rfl) ⟨1594383, by rfl⟩ : syracuseStep 4251689 = 3188767) B3188767
theorem B1892969 : Blo 838352 1892969 := bstep (se 2 (by rfl) ⟨709863, by rfl⟩ : syracuseStep 1892969 = 1419727) B1419727
theorem B944239 : Blo 838352 944239 := bstep (se 1 (by rfl) ⟨708179, by rfl⟩ : syracuseStep 944239 = 1416359) B1416359
theorem B21785435 : Blo 838352 21785435 := bstep (se 1 (by rfl) ⟨16339076, by rfl⟩ : syracuseStep 21785435 = 32678153) B32678153
theorem B1011647 : Blo 838352 1011647 := bstep (se 1 (by rfl) ⟨758735, by rfl⟩ : syracuseStep 1011647 = 1517471) B1517471
theorem B2127131 : Blo 838352 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B2389799 : Blo 838352 2389799 := bstep (se 1 (by rfl) ⟨1792349, by rfl⟩ : syracuseStep 2389799 = 3584699) B3584699
theorem B4258007 : Blo 838352 4258007 := bstep (se 1 (by rfl) ⟨3193505, by rfl⟩ : syracuseStep 4258007 = 6387011) B6387011
theorem B2390255 : Blo 838352 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B2160967 : Blo 838352 2160967 := bstep (se 1 (by rfl) ⟨1620725, by rfl⟩ : syracuseStep 2160967 = 3241451) B3241451
theorem B39320255 : Blo 838352 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B5111201 : Blo 838352 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B559742687 : Blo 838352 559742687 := bstep (se 1 (by rfl) ⟨419807015, by rfl⟩ : syracuseStep 559742687 = 839614031) B839614031
theorem B46073447 : Blo 838352 46073447 := bstep (se 1 (by rfl) ⟨34555085, by rfl⟩ : syracuseStep 46073447 = 69110171) B69110171
theorem B16189267 : Blo 838352 16189267 := bstep (se 1 (by rfl) ⟨12141950, by rfl⟩ : syracuseStep 16189267 = 24283901) B24283901
theorem B3640747 : Blo 838352 3640747 := bstep (se 1 (by rfl) ⟨2730560, by rfl⟩ : syracuseStep 3640747 = 5461121) B5461121
theorem B2395631 : Blo 838352 2395631 := bstep (se 1 (by rfl) ⟨1796723, by rfl⟩ : syracuseStep 2395631 = 3593447) B3593447
theorem B24252533 : Blo 838352 24252533 := bstep (se 5 (by rfl) ⟨1136837, by rfl⟩ : syracuseStep 24252533 = 2273675) B2273675
theorem B14523623 : Blo 838352 14523623 := bstep (se 1 (by rfl) ⟨10892717, by rfl⟩ : syracuseStep 14523623 = 21785435) B21785435
theorem B1418087 : Blo 838352 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B9577601 : Blo 838352 9577601 := bstep (se 2 (by rfl) ⟨3591600, by rfl⟩ : syracuseStep 9577601 = 7183201) B7183201
theorem B2697725 : Blo 838352 2697725 := bstep (se 3 (by rfl) ⟨505823, by rfl⟩ : syracuseStep 2697725 = 1011647) B1011647
theorem B1257767 : Blo 838352 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B1258985 : Blo 838352 1258985 := bstep (se 2 (by rfl) ⟨472119, by rfl⟩ : syracuseStep 1258985 = 944239) B944239
theorem B5388221 : Blo 838352 5388221 := bstep (se 3 (by rfl) ⟨1010291, by rfl⟩ : syracuseStep 5388221 = 2020583) B2020583
theorem B1260011 : Blo 838352 1260011 := bstep (se 1 (by rfl) ⟨945008, by rfl⟩ : syracuseStep 1260011 = 1890017) B1890017
theorem B4308041 : Blo 838352 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B2834459 : Blo 838352 2834459 := bstep (se 1 (by rfl) ⟨2125844, by rfl⟩ : syracuseStep 2834459 = 4251689) B4251689
theorem B1261979 : Blo 838352 1261979 := bstep (se 1 (by rfl) ⟨946484, by rfl⟩ : syracuseStep 1261979 = 1892969) B1892969
theorem B838375 : Blo 838352 838375 := bstep (se 1 (by rfl) ⟨628781, by rfl⟩ : syracuseStep 838375 = 1257563) B1257563
theorem B1887209 : Blo 838352 1887209 := bstep (se 2 (by rfl) ⟨707703, by rfl⟩ : syracuseStep 1887209 = 1415407) B1415407
theorem B1887335 : Blo 838352 1887335 := bstep (se 1 (by rfl) ⟨1415501, by rfl⟩ : syracuseStep 1887335 = 2831003) B2831003
theorem B839103 : Blo 838352 839103 := bstep (se 1 (by rfl) ⟨629327, by rfl⟩ : syracuseStep 839103 = 1258655) B1258655
theorem B1888091 : Blo 838352 1888091 := bstep (se 1 (by rfl) ⟨1416068, by rfl⟩ : syracuseStep 1888091 = 2832137) B2832137
theorem B1593199 : Blo 838352 1593199 := bstep (se 1 (by rfl) ⟨1194899, by rfl⟩ : syracuseStep 1593199 = 2389799) B2389799
theorem B2838671 : Blo 838352 2838671 := bstep (se 1 (by rfl) ⟨2129003, by rfl⟩ : syracuseStep 2838671 = 4258007) B4258007
theorem B1593503 : Blo 838352 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B839847 : Blo 838352 839847 := bstep (se 1 (by rfl) ⟨629885, by rfl⟩ : syracuseStep 839847 = 1259771) B1259771
theorem B12112199 : Blo 838352 12112199 := bstep (se 1 (by rfl) ⟨9084149, by rfl⟩ : syracuseStep 12112199 = 18168299) B18168299
theorem B840159 : Blo 838352 840159 := bstep (se 1 (by rfl) ⟨630119, by rfl⟩ : syracuseStep 840159 = 1260239) B1260239
theorem B841031 : Blo 838352 841031 := bstep (se 1 (by rfl) ⟨630773, by rfl⟩ : syracuseStep 841031 = 1261547) B1261547
theorem B9590723 : Blo 838352 9590723 := bstep (se 1 (by rfl) ⟨7193042, by rfl⟩ : syracuseStep 9590723 = 14386085) B14386085
theorem B842207 : Blo 838352 842207 := bstep (se 1 (by rfl) ⟨631655, by rfl⟩ : syracuseStep 842207 = 1263311) B1263311
theorem B89545799 : Blo 838352 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B3595823 : Blo 838352 3595823 := bstep (se 1 (by rfl) ⟨2696867, by rfl⟩ : syracuseStep 3595823 = 5393735) B5393735
theorem B34561657 : Blo 838352 34561657 := bstep (se 2 (by rfl) ⟨12960621, by rfl⟩ : syracuseStep 34561657 = 25921243) B25921243
theorem B16342811 : Blo 838352 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B310239071 : Blo 838352 310239071 := bstep (se 1 (by rfl) ⟨232679303, by rfl⟩ : syracuseStep 310239071 = 465358607) B465358607
theorem B2881289 : Blo 838352 2881289 := bstep (se 2 (by rfl) ⟨1080483, by rfl⟩ : syracuseStep 2881289 = 2160967) B2160967
theorem B26213503 : Blo 838352 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B3407467 : Blo 838352 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B373161791 : Blo 838352 373161791 := bstep (se 1 (by rfl) ⟨279871343, by rfl⟩ : syracuseStep 373161791 = 559742687) B559742687
theorem B6393815 : Blo 838352 6393815 := bstep (se 1 (by rfl) ⟨4795361, by rfl⟩ : syracuseStep 6393815 = 9590723) B9590723
theorem B4854329 : Blo 838352 4854329 := bstep (se 2 (by rfl) ⟨1820373, by rfl⟩ : syracuseStep 4854329 = 3640747) B3640747
theorem B2397215 : Blo 838352 2397215 := bstep (se 1 (by rfl) ⟨1797911, by rfl⟩ : syracuseStep 2397215 = 3595823) B3595823
theorem B46082209 : Blo 838352 46082209 := bstep (se 2 (by rfl) ⟨17280828, by rfl⟩ : syracuseStep 46082209 = 34561657) B34561657
theorem B30715631 : Blo 838352 30715631 := bstep (se 1 (by rfl) ⟨23036723, by rfl⟩ : syracuseStep 30715631 = 46073447) B46073447
theorem B1258139 : Blo 838352 1258139 := bstep (se 1 (by rfl) ⟨943604, by rfl⟩ : syracuseStep 1258139 = 1887209) B1887209
theorem B1258223 : Blo 838352 1258223 := bstep (se 1 (by rfl) ⟨943667, by rfl⟩ : syracuseStep 1258223 = 1887335) B1887335
theorem B1258727 : Blo 838352 1258727 := bstep (se 1 (by rfl) ⟨944045, by rfl⟩ : syracuseStep 1258727 = 1888091) B1888091
theorem B16168355 : Blo 838352 16168355 := bstep (se 1 (by rfl) ⟨12126266, by rfl⟩ : syracuseStep 16168355 = 24252533) B24252533
theorem B1062335 : Blo 838352 1062335 := bstep (se 1 (by rfl) ⟨796751, by rfl⟩ : syracuseStep 1062335 = 1593503) B1593503
theorem B8074799 : Blo 838352 8074799 := bstep (se 1 (by rfl) ⟨6056099, by rfl⟩ : syracuseStep 8074799 = 12112199) B12112199
theorem B7683437 : Blo 838352 7683437 := bstep (se 3 (by rfl) ⟨1440644, by rfl⟩ : syracuseStep 7683437 = 2881289) B2881289
theorem B9682415 : Blo 838352 9682415 := bstep (se 1 (by rfl) ⟨7261811, by rfl⟩ : syracuseStep 9682415 = 14523623) B14523623
theorem B14368589 : Blo 838352 14368589 := bstep (se 3 (by rfl) ⟨2694110, by rfl⟩ : syracuseStep 14368589 = 5388221) B5388221
theorem B10895207 : Blo 838352 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B7193933 : Blo 838352 7193933 := bstep (se 3 (by rfl) ⟨1348862, by rfl⟩ : syracuseStep 7193933 = 2697725) B2697725
theorem B838511 : Blo 838352 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B839323 : Blo 838352 839323 := bstep (se 1 (by rfl) ⟨629492, by rfl⟩ : syracuseStep 839323 = 1258985) B1258985
theorem B34951337 : Blo 838352 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B840007 : Blo 838352 840007 := bstep (se 1 (by rfl) ⟨630005, by rfl⟩ : syracuseStep 840007 = 1260011) B1260011
theorem B2872027 : Blo 838352 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B4543289 : Blo 838352 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B1889639 : Blo 838352 1889639 := bstep (se 1 (by rfl) ⟨1417229, by rfl⟩ : syracuseStep 1889639 = 2834459) B2834459
theorem B841319 : Blo 838352 841319 := bstep (se 1 (by rfl) ⟨630989, by rfl⟩ : syracuseStep 841319 = 1261979) B1261979
theorem B1597087 : Blo 838352 1597087 := bstep (se 1 (by rfl) ⟨1197815, by rfl⟩ : syracuseStep 1597087 = 2395631) B2395631
theorem B21585689 : Blo 838352 21585689 := bstep (se 2 (by rfl) ⟨8094633, by rfl⟩ : syracuseStep 21585689 = 16189267) B16189267
theorem B1892447 : Blo 838352 1892447 := bstep (se 1 (by rfl) ⟨1419335, by rfl⟩ : syracuseStep 1892447 = 2838671) B2838671
theorem B59697199 : Blo 838352 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B2124265 : Blo 838352 2124265 := bstep (se 2 (by rfl) ⟨796599, by rfl⟩ : syracuseStep 2124265 = 1593199) B1593199
theorem B206826047 : Blo 838352 206826047 := bstep (se 1 (by rfl) ⟨155119535, by rfl⟩ : syracuseStep 206826047 = 310239071) B310239071
theorem B945391 : Blo 838352 945391 := bstep (se 1 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 945391 = 1418087) B1418087
theorem B6385067 : Blo 838352 6385067 := bstep (se 1 (by rfl) ⟨4788800, by rfl⟩ : syracuseStep 6385067 = 9577601) B9577601
theorem B248774527 : Blo 838352 248774527 := bstep (se 1 (by rfl) ⟨186580895, by rfl⟩ : syracuseStep 248774527 = 373161791) B373161791
theorem B4262543 : Blo 838352 4262543 := bstep (se 1 (by rfl) ⟨3196907, by rfl⟩ : syracuseStep 4262543 = 6393815) B6393815
theorem B79596265 : Blo 838352 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B23300891 : Blo 838352 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B61442945 : Blo 838352 61442945 := bstep (se 2 (by rfl) ⟨23041104, by rfl⟩ : syracuseStep 61442945 = 46082209) B46082209
theorem B14390459 : Blo 838352 14390459 := bstep (se 1 (by rfl) ⟨10792844, by rfl⟩ : syracuseStep 14390459 = 21585689) B21585689
theorem B5383199 : Blo 838352 5383199 := bstep (se 1 (by rfl) ⟨4037399, by rfl⟩ : syracuseStep 5383199 = 8074799) B8074799
theorem B5122291 : Blo 838352 5122291 := bstep (se 1 (by rfl) ⟨3841718, by rfl⟩ : syracuseStep 5122291 = 7683437) B7683437
theorem B9579059 : Blo 838352 9579059 := bstep (se 1 (by rfl) ⟨7184294, by rfl⟩ : syracuseStep 9579059 = 14368589) B14368589
theorem B4795955 : Blo 838352 4795955 := bstep (se 1 (by rfl) ⟨3596966, by rfl⟩ : syracuseStep 4795955 = 7193933) B7193933
theorem B3028859 : Blo 838352 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B2832353 : Blo 838352 2832353 := bstep (se 2 (by rfl) ⟨1062132, by rfl⟩ : syracuseStep 2832353 = 2124265) B2124265
theorem B1259759 : Blo 838352 1259759 := bstep (se 1 (by rfl) ⟨944819, by rfl⟩ : syracuseStep 1259759 = 1889639) B1889639
theorem B2832893 : Blo 838352 2832893 := bstep (se 3 (by rfl) ⟨531167, by rfl⟩ : syracuseStep 2832893 = 1062335) B1062335
theorem B1260521 : Blo 838352 1260521 := bstep (se 2 (by rfl) ⟨472695, by rfl⟩ : syracuseStep 1260521 = 945391) B945391
theorem B1261631 : Blo 838352 1261631 := bstep (se 1 (by rfl) ⟨946223, by rfl⟩ : syracuseStep 1261631 = 1892447) B1892447
theorem B838759 : Blo 838352 838759 := bstep (se 1 (by rfl) ⟨629069, by rfl⟩ : syracuseStep 838759 = 1258139) B1258139
theorem B838815 : Blo 838352 838815 := bstep (se 1 (by rfl) ⟨629111, by rfl⟩ : syracuseStep 838815 = 1258223) B1258223
theorem B839151 : Blo 838352 839151 := bstep (se 1 (by rfl) ⟨629363, by rfl⟩ : syracuseStep 839151 = 1258727) B1258727
theorem B29053885 : Blo 838352 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B331699369 : Blo 838352 331699369 := bstep (se 2 (by rfl) ⟨124387263, by rfl⟩ : syracuseStep 331699369 = 248774527) B248774527
theorem B3236219 : Blo 838352 3236219 := bstep (se 1 (by rfl) ⟨2427164, by rfl⟩ : syracuseStep 3236219 = 4854329) B4854329
theorem B1598143 : Blo 838352 1598143 := bstep (se 1 (by rfl) ⟨1198607, by rfl⟩ : syracuseStep 1598143 = 2397215) B2397215
theorem B3829369 : Blo 838352 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B137884031 : Blo 838352 137884031 := bstep (se 1 (by rfl) ⟨103413023, by rfl⟩ : syracuseStep 137884031 = 206826047) B206826047
theorem B4256711 : Blo 838352 4256711 := bstep (se 1 (by rfl) ⟨3192533, by rfl⟩ : syracuseStep 4256711 = 6385067) B6385067
theorem B20477087 : Blo 838352 20477087 := bstep (se 1 (by rfl) ⟨15357815, by rfl⟩ : syracuseStep 20477087 = 30715631) B30715631
theorem B10778903 : Blo 838352 10778903 := bstep (se 1 (by rfl) ⟨8084177, by rfl⟩ : syracuseStep 10778903 = 16168355) B16168355
theorem B2129449 : Blo 838352 2129449 := bstep (se 2 (by rfl) ⟨798543, by rfl⟩ : syracuseStep 2129449 = 1597087) B1597087
theorem B6454943 : Blo 838352 6454943 := bstep (se 1 (by rfl) ⟨4841207, by rfl⟩ : syracuseStep 6454943 = 9682415) B9682415
theorem B2130857 : Blo 838352 2130857 := bstep (se 2 (by rfl) ⟨799071, by rfl⟩ : syracuseStep 2130857 = 1598143) B1598143
theorem B15533927 : Blo 838352 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B40961963 : Blo 838352 40961963 := bstep (se 1 (by rfl) ⟨30721472, by rfl⟩ : syracuseStep 40961963 = 61442945) B61442945
theorem B38738513 : Blo 838352 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B91922687 : Blo 838352 91922687 := bstep (se 1 (by rfl) ⟨68942015, by rfl⟩ : syracuseStep 91922687 = 137884031) B137884031
theorem B7185935 : Blo 838352 7185935 := bstep (se 1 (by rfl) ⟨5389451, by rfl⟩ : syracuseStep 7185935 = 10778903) B10778903
theorem B4303295 : Blo 838352 4303295 := bstep (se 1 (by rfl) ⟨3227471, by rfl⟩ : syracuseStep 4303295 = 6454943) B6454943
theorem B6829721 : Blo 838352 6829721 := bstep (se 2 (by rfl) ⟨2561145, by rfl⟩ : syracuseStep 6829721 = 5122291) B5122291
theorem B3588799 : Blo 838352 3588799 := bstep (se 1 (by rfl) ⟨2691599, by rfl⟩ : syracuseStep 3588799 = 5383199) B5383199
theorem B3197303 : Blo 838352 3197303 := bstep (se 1 (by rfl) ⟨2397977, by rfl⟩ : syracuseStep 3197303 = 4795955) B4795955
theorem B2837807 : Blo 838352 2837807 := bstep (se 1 (by rfl) ⟨2128355, by rfl⟩ : syracuseStep 2837807 = 4256711) B4256711
theorem B13651391 : Blo 838352 13651391 := bstep (se 1 (by rfl) ⟨10238543, by rfl⟩ : syracuseStep 13651391 = 20477087) B20477087
theorem B2019239 : Blo 838352 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B1888235 : Blo 838352 1888235 := bstep (se 1 (by rfl) ⟨1416176, by rfl⟩ : syracuseStep 1888235 = 2832353) B2832353
theorem B839839 : Blo 838352 839839 := bstep (se 1 (by rfl) ⟨629879, by rfl⟩ : syracuseStep 839839 = 1259759) B1259759
theorem B1888595 : Blo 838352 1888595 := bstep (se 1 (by rfl) ⟨1416446, by rfl⟩ : syracuseStep 1888595 = 2832893) B2832893
theorem B840347 : Blo 838352 840347 := bstep (se 1 (by rfl) ⟨630260, by rfl⟩ : syracuseStep 840347 = 1260521) B1260521
theorem B2839265 : Blo 838352 2839265 := bstep (se 2 (by rfl) ⟨1064724, by rfl⟩ : syracuseStep 2839265 = 2129449) B2129449
theorem B841087 : Blo 838352 841087 := bstep (se 1 (by rfl) ⟨630815, by rfl⟩ : syracuseStep 841087 = 1261631) B1261631
theorem B2841695 : Blo 838352 2841695 := bstep (se 1 (by rfl) ⟨2131271, by rfl⟩ : syracuseStep 2841695 = 4262543) B4262543
theorem B9593639 : Blo 838352 9593639 := bstep (se 1 (by rfl) ⟨7195229, by rfl⟩ : syracuseStep 9593639 = 14390459) B14390459
theorem B106128353 : Blo 838352 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B5105825 : Blo 838352 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B2157479 : Blo 838352 2157479 := bstep (se 1 (by rfl) ⟨1618109, by rfl⟩ : syracuseStep 2157479 = 3236219) B3236219
theorem B442265825 : Blo 838352 442265825 := bstep (se 2 (by rfl) ⟨165849684, by rfl⟩ : syracuseStep 442265825 = 331699369) B331699369
theorem B6386039 : Blo 838352 6386039 := bstep (se 1 (by rfl) ⟨4789529, by rfl⟩ : syracuseStep 6386039 = 9579059) B9579059
theorem B4785065 : Blo 838352 4785065 := bstep (se 2 (by rfl) ⟨1794399, by rfl⟩ : syracuseStep 4785065 = 3588799) B3588799
theorem B10355951 : Blo 838352 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B2131535 : Blo 838352 2131535 := bstep (se 1 (by rfl) ⟨1598651, by rfl⟩ : syracuseStep 2131535 = 3197303) B3197303
theorem B1346159 : Blo 838352 1346159 := bstep (se 1 (by rfl) ⟨1009619, by rfl⟩ : syracuseStep 1346159 = 2019239) B2019239
theorem B25825675 : Blo 838352 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B61281791 : Blo 838352 61281791 := bstep (se 1 (by rfl) ⟨45961343, by rfl⟩ : syracuseStep 61281791 = 91922687) B91922687
theorem B6395759 : Blo 838352 6395759 := bstep (se 1 (by rfl) ⟨4796819, by rfl⟩ : syracuseStep 6395759 = 9593639) B9593639
theorem B4790623 : Blo 838352 4790623 := bstep (se 1 (by rfl) ⟨3592967, by rfl⟩ : syracuseStep 4790623 = 7185935) B7185935
theorem B1420571 : Blo 838352 1420571 := bstep (se 1 (by rfl) ⟨1065428, by rfl⟩ : syracuseStep 1420571 = 2130857) B2130857
theorem B27307975 : Blo 838352 27307975 := bstep (se 1 (by rfl) ⟨20480981, by rfl⟩ : syracuseStep 27307975 = 40961963) B40961963
theorem B1258823 : Blo 838352 1258823 := bstep (se 1 (by rfl) ⟨944117, by rfl⟩ : syracuseStep 1258823 = 1888235) B1888235
theorem B1259063 : Blo 838352 1259063 := bstep (se 1 (by rfl) ⟨944297, by rfl⟩ : syracuseStep 1259063 = 1888595) B1888595
theorem B2868863 : Blo 838352 2868863 := bstep (se 1 (by rfl) ⟨2151647, by rfl⟩ : syracuseStep 2868863 = 4303295) B4303295
theorem B1891871 : Blo 838352 1891871 := bstep (se 1 (by rfl) ⟨1418903, by rfl⟩ : syracuseStep 1891871 = 2837807) B2837807
theorem B9100927 : Blo 838352 9100927 := bstep (se 1 (by rfl) ⟨6825695, by rfl⟩ : syracuseStep 9100927 = 13651391) B13651391
theorem B283008941 : Blo 838352 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B1892843 : Blo 838352 1892843 := bstep (se 1 (by rfl) ⟨1419632, by rfl⟩ : syracuseStep 1892843 = 2839265) B2839265
theorem B1894463 : Blo 838352 1894463 := bstep (se 1 (by rfl) ⟨1420847, by rfl⟩ : syracuseStep 1894463 = 2841695) B2841695
theorem B3403883 : Blo 838352 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B1438319 : Blo 838352 1438319 := bstep (se 1 (by rfl) ⟨1078739, by rfl⟩ : syracuseStep 1438319 = 2157479) B2157479
theorem B294843883 : Blo 838352 294843883 := bstep (se 1 (by rfl) ⟨221132912, by rfl⟩ : syracuseStep 294843883 = 442265825) B442265825
theorem B4257359 : Blo 838352 4257359 := bstep (se 1 (by rfl) ⟨3193019, by rfl⟩ : syracuseStep 4257359 = 6386039) B6386039
theorem B4553147 : Blo 838352 4553147 := bstep (se 1 (by rfl) ⟨3414860, by rfl⟩ : syracuseStep 4553147 = 6829721) B6829721
theorem B9077021 : Blo 838352 9077021 := bstep (se 3 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 9077021 = 3403883) B3403883
theorem B4263839 : Blo 838352 4263839 := bstep (se 1 (by rfl) ⟨3197879, by rfl⟩ : syracuseStep 4263839 = 6395759) B6395759
theorem B36410633 : Blo 838352 36410633 := bstep (se 2 (by rfl) ⟨13653987, by rfl⟩ : syracuseStep 36410633 = 27307975) B27307975
theorem B393125177 : Blo 838352 393125177 := bstep (se 2 (by rfl) ⟨147421941, by rfl⟩ : syracuseStep 393125177 = 294843883) B294843883
theorem B958879 : Blo 838352 958879 := bstep (se 1 (by rfl) ⟨719159, by rfl⟩ : syracuseStep 958879 = 1438319) B1438319
theorem B48538277 : Blo 838352 48538277 := bstep (se 4 (by rfl) ⟨4550463, by rfl⟩ : syracuseStep 48538277 = 9100927) B9100927
theorem B3190043 : Blo 838352 3190043 := bstep (se 1 (by rfl) ⟨2392532, by rfl⟩ : syracuseStep 3190043 = 4785065) B4785065
theorem B1421023 : Blo 838352 1421023 := bstep (se 1 (by rfl) ⟨1065767, by rfl⟩ : syracuseStep 1421023 = 2131535) B2131535
theorem B7650301 : Blo 838352 7650301 := bstep (se 3 (by rfl) ⟨1434431, by rfl⟩ : syracuseStep 7650301 = 2868863) B2868863
theorem B1261247 : Blo 838352 1261247 := bstep (se 1 (by rfl) ⟨945935, by rfl⟩ : syracuseStep 1261247 = 1891871) B1891871
theorem B1261895 : Blo 838352 1261895 := bstep (se 1 (by rfl) ⟨946421, by rfl⟩ : syracuseStep 1261895 = 1892843) B1892843
theorem B1262975 : Blo 838352 1262975 := bstep (se 1 (by rfl) ⟨947231, by rfl⟩ : syracuseStep 1262975 = 1894463) B1894463
theorem B3589757 : Blo 838352 3589757 := bstep (se 3 (by rfl) ⟨673079, by rfl⟩ : syracuseStep 3589757 = 1346159) B1346159
theorem B839215 : Blo 838352 839215 := bstep (se 1 (by rfl) ⟨629411, by rfl⟩ : syracuseStep 839215 = 1258823) B1258823
theorem B839375 : Blo 838352 839375 := bstep (se 1 (by rfl) ⟨629531, by rfl⟩ : syracuseStep 839375 = 1259063) B1259063
theorem B2838239 : Blo 838352 2838239 := bstep (se 1 (by rfl) ⟨2128679, by rfl⟩ : syracuseStep 2838239 = 4257359) B4257359
theorem B3035431 : Blo 838352 3035431 := bstep (se 1 (by rfl) ⟨2276573, by rfl⟩ : syracuseStep 3035431 = 4553147) B4553147
theorem B6903967 : Blo 838352 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B40854527 : Blo 838352 40854527 := bstep (se 1 (by rfl) ⟨30640895, by rfl⟩ : syracuseStep 40854527 = 61281791) B61281791
theorem B188672627 : Blo 838352 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B34434233 : Blo 838352 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B947047 : Blo 838352 947047 := bstep (se 1 (by rfl) ⟨710285, by rfl⟩ : syracuseStep 947047 = 1420571) B1420571
theorem B6387497 : Blo 838352 6387497 := bstep (se 2 (by rfl) ⟨2395311, by rfl⟩ : syracuseStep 6387497 = 4790623) B4790623
theorem B1278505 : Blo 838352 1278505 := bstep (se 2 (by rfl) ⟨479439, by rfl⟩ : syracuseStep 1278505 = 958879) B958879
theorem B2393171 : Blo 838352 2393171 := bstep (se 1 (by rfl) ⟨1794878, by rfl⟩ : syracuseStep 2393171 = 3589757) B3589757
theorem B262083451 : Blo 838352 262083451 := bstep (se 1 (by rfl) ⟨196562588, by rfl⟩ : syracuseStep 262083451 = 393125177) B393125177
theorem B27236351 : Blo 838352 27236351 := bstep (se 1 (by rfl) ⟨20427263, by rfl⟩ : syracuseStep 27236351 = 40854527) B40854527
theorem B10200401 : Blo 838352 10200401 := bstep (se 2 (by rfl) ⟨3825150, by rfl⟩ : syracuseStep 10200401 = 7650301) B7650301
theorem B4047241 : Blo 838352 4047241 := bstep (se 2 (by rfl) ⟨1517715, by rfl⟩ : syracuseStep 4047241 = 3035431) B3035431
theorem B32358851 : Blo 838352 32358851 := bstep (se 1 (by rfl) ⟨24269138, by rfl⟩ : syracuseStep 32358851 = 48538277) B48538277
theorem B1262729 : Blo 838352 1262729 := bstep (se 2 (by rfl) ⟨473523, by rfl⟩ : syracuseStep 1262729 = 947047) B947047
theorem B125781751 : Blo 838352 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B22956155 : Blo 838352 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B840831 : Blo 838352 840831 := bstep (se 1 (by rfl) ⟨630623, by rfl⟩ : syracuseStep 840831 = 1261247) B1261247
theorem B6051347 : Blo 838352 6051347 := bstep (se 1 (by rfl) ⟨4538510, by rfl⟩ : syracuseStep 6051347 = 9077021) B9077021
theorem B841263 : Blo 838352 841263 := bstep (se 1 (by rfl) ⟨630947, by rfl⟩ : syracuseStep 841263 = 1261895) B1261895
theorem B841983 : Blo 838352 841983 := bstep (se 1 (by rfl) ⟨631487, by rfl⟩ : syracuseStep 841983 = 1262975) B1262975
theorem B1892159 : Blo 838352 1892159 := bstep (se 1 (by rfl) ⟨1419119, by rfl⟩ : syracuseStep 1892159 = 2838239) B2838239
theorem B2842559 : Blo 838352 2842559 := bstep (se 1 (by rfl) ⟨2131919, by rfl⟩ : syracuseStep 2842559 = 4263839) B4263839
theorem B24273755 : Blo 838352 24273755 := bstep (se 1 (by rfl) ⟨18205316, by rfl⟩ : syracuseStep 24273755 = 36410633) B36410633
theorem B1894697 : Blo 838352 1894697 := bstep (se 2 (by rfl) ⟨710511, by rfl⟩ : syracuseStep 1894697 = 1421023) B1421023
theorem B2126695 : Blo 838352 2126695 := bstep (se 1 (by rfl) ⟨1595021, by rfl⟩ : syracuseStep 2126695 = 3190043) B3190043
theorem B9205289 : Blo 838352 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B4258331 : Blo 838352 4258331 := bstep (se 1 (by rfl) ⟨3193748, by rfl⟩ : syracuseStep 4258331 = 6387497) B6387497
theorem B1704673 : Blo 838352 1704673 := bstep (se 2 (by rfl) ⟨639252, by rfl⟩ : syracuseStep 1704673 = 1278505) B1278505
theorem B15304103 : Blo 838352 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B167709001 : Blo 838352 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B4034231 : Blo 838352 4034231 := bstep (se 1 (by rfl) ⟨3025673, by rfl⟩ : syracuseStep 4034231 = 6051347) B6051347
theorem B349444601 : Blo 838352 349444601 := bstep (se 2 (by rfl) ⟨131041725, by rfl⟩ : syracuseStep 349444601 = 262083451) B262083451
theorem B6136859 : Blo 838352 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B21572567 : Blo 838352 21572567 := bstep (se 1 (by rfl) ⟨16179425, by rfl⟩ : syracuseStep 21572567 = 32358851) B32358851
theorem B1261439 : Blo 838352 1261439 := bstep (se 1 (by rfl) ⟨946079, by rfl⟩ : syracuseStep 1261439 = 1892159) B1892159
theorem B72630269 : Blo 838352 72630269 := bstep (se 3 (by rfl) ⟨13618175, by rfl⟩ : syracuseStep 72630269 = 27236351) B27236351
theorem B6800267 : Blo 838352 6800267 := bstep (se 1 (by rfl) ⟨5100200, by rfl⟩ : syracuseStep 6800267 = 10200401) B10200401
theorem B2835593 : Blo 838352 2835593 := bstep (se 2 (by rfl) ⟨1063347, by rfl⟩ : syracuseStep 2835593 = 2126695) B2126695
theorem B1263131 : Blo 838352 1263131 := bstep (se 1 (by rfl) ⟨947348, by rfl⟩ : syracuseStep 1263131 = 1894697) B1894697
theorem B2838887 : Blo 838352 2838887 := bstep (se 1 (by rfl) ⟨2129165, by rfl⟩ : syracuseStep 2838887 = 4258331) B4258331
theorem B5396321 : Blo 838352 5396321 := bstep (se 2 (by rfl) ⟨2023620, by rfl⟩ : syracuseStep 5396321 = 4047241) B4047241
theorem B1595447 : Blo 838352 1595447 := bstep (se 1 (by rfl) ⟨1196585, by rfl⟩ : syracuseStep 1595447 = 2393171) B2393171
theorem B841819 : Blo 838352 841819 := bstep (se 1 (by rfl) ⟨631364, by rfl⟩ : syracuseStep 841819 = 1262729) B1262729
theorem B1895039 : Blo 838352 1895039 := bstep (se 1 (by rfl) ⟨1421279, by rfl⟩ : syracuseStep 1895039 = 2842559) B2842559
theorem B16182503 : Blo 838352 16182503 := bstep (se 1 (by rfl) ⟨12136877, by rfl⟩ : syracuseStep 16182503 = 24273755) B24273755
theorem B2689487 : Blo 838352 2689487 := bstep (se 1 (by rfl) ⟨2017115, by rfl⟩ : syracuseStep 2689487 = 4034231) B4034231
theorem B223612001 : Blo 838352 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B10788335 : Blo 838352 10788335 := bstep (se 1 (by rfl) ⟨8091251, by rfl⟩ : syracuseStep 10788335 = 16182503) B16182503
theorem B4533511 : Blo 838352 4533511 := bstep (se 1 (by rfl) ⟨3400133, by rfl⟩ : syracuseStep 4533511 = 6800267) B6800267
theorem B10202735 : Blo 838352 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B2272897 : Blo 838352 2272897 := bstep (se 2 (by rfl) ⟨852336, by rfl⟩ : syracuseStep 2272897 = 1704673) B1704673
theorem B1063631 : Blo 838352 1063631 := bstep (se 1 (by rfl) ⟨797723, by rfl⟩ : syracuseStep 1063631 = 1595447) B1595447
theorem B232963067 : Blo 838352 232963067 := bstep (se 1 (by rfl) ⟨174722300, by rfl⟩ : syracuseStep 232963067 = 349444601) B349444601
theorem B1263359 : Blo 838352 1263359 := bstep (se 1 (by rfl) ⟨947519, by rfl⟩ : syracuseStep 1263359 = 1895039) B1895039
theorem B840959 : Blo 838352 840959 := bstep (se 1 (by rfl) ⟨630719, by rfl⟩ : syracuseStep 840959 = 1261439) B1261439
theorem B48420179 : Blo 838352 48420179 := bstep (se 1 (by rfl) ⟨36315134, by rfl⟩ : syracuseStep 48420179 = 72630269) B72630269
theorem B1890395 : Blo 838352 1890395 := bstep (se 1 (by rfl) ⟨1417796, by rfl⟩ : syracuseStep 1890395 = 2835593) B2835593
theorem B842087 : Blo 838352 842087 := bstep (se 1 (by rfl) ⟨631565, by rfl⟩ : syracuseStep 842087 = 1263131) B1263131
theorem B1892591 : Blo 838352 1892591 := bstep (se 1 (by rfl) ⟨1419443, by rfl⟩ : syracuseStep 1892591 = 2838887) B2838887
theorem B3597547 : Blo 838352 3597547 := bstep (se 1 (by rfl) ⟨2698160, by rfl⟩ : syracuseStep 3597547 = 5396321) B5396321
theorem B4091239 : Blo 838352 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B14381711 : Blo 838352 14381711 := bstep (se 1 (by rfl) ⟨10786283, by rfl⟩ : syracuseStep 14381711 = 21572567) B21572567
theorem B32280119 : Blo 838352 32280119 := bstep (se 1 (by rfl) ⟨24210089, by rfl⟩ : syracuseStep 32280119 = 48420179) B48420179
theorem B4796729 : Blo 838352 4796729 := bstep (se 2 (by rfl) ⟨1798773, by rfl⟩ : syracuseStep 4796729 = 3597547) B3597547
theorem B149074667 : Blo 838352 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B1260263 : Blo 838352 1260263 := bstep (se 1 (by rfl) ⟨945197, by rfl⟩ : syracuseStep 1260263 = 1890395) B1890395
theorem B6044681 : Blo 838352 6044681 := bstep (se 2 (by rfl) ⟨2266755, by rfl⟩ : syracuseStep 6044681 = 4533511) B4533511
theorem B3030529 : Blo 838352 3030529 := bstep (se 2 (by rfl) ⟨1136448, by rfl⟩ : syracuseStep 3030529 = 2272897) B2272897
theorem B7192223 : Blo 838352 7192223 := bstep (se 1 (by rfl) ⟨5394167, by rfl⟩ : syracuseStep 7192223 = 10788335) B10788335
theorem B1261727 : Blo 838352 1261727 := bstep (se 1 (by rfl) ⟨946295, by rfl⟩ : syracuseStep 1261727 = 1892591) B1892591
theorem B2836349 : Blo 838352 2836349 := bstep (se 3 (by rfl) ⟨531815, by rfl⟩ : syracuseStep 2836349 = 1063631) B1063631
theorem B6801823 : Blo 838352 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B9587807 : Blo 838352 9587807 := bstep (se 1 (by rfl) ⟨7190855, by rfl⟩ : syracuseStep 9587807 = 14381711) B14381711
theorem B155308711 : Blo 838352 155308711 := bstep (se 1 (by rfl) ⟨116481533, by rfl⟩ : syracuseStep 155308711 = 232963067) B232963067
theorem B842239 : Blo 838352 842239 := bstep (se 1 (by rfl) ⟨631679, by rfl⟩ : syracuseStep 842239 = 1263359) B1263359
theorem B1792991 : Blo 838352 1792991 := bstep (se 1 (by rfl) ⟨1344743, by rfl⟩ : syracuseStep 1792991 = 2689487) B2689487
theorem B21819941 : Blo 838352 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B6391871 : Blo 838352 6391871 := bstep (se 1 (by rfl) ⟨4793903, by rfl⟩ : syracuseStep 6391871 = 9587807) B9587807
theorem B4040705 : Blo 838352 4040705 := bstep (se 2 (by rfl) ⟨1515264, by rfl⟩ : syracuseStep 4040705 = 3030529) B3030529
theorem B4794815 : Blo 838352 4794815 := bstep (se 1 (by rfl) ⟨3596111, by rfl⟩ : syracuseStep 4794815 = 7192223) B7192223
theorem B1195327 : Blo 838352 1195327 := bstep (se 1 (by rfl) ⟨896495, by rfl⟩ : syracuseStep 1195327 = 1792991) B1792991
theorem B207078281 : Blo 838352 207078281 := bstep (se 2 (by rfl) ⟨77654355, by rfl⟩ : syracuseStep 207078281 = 155308711) B155308711
theorem B3197819 : Blo 838352 3197819 := bstep (se 1 (by rfl) ⟨2398364, by rfl⟩ : syracuseStep 3197819 = 4796729) B4796729
theorem B840175 : Blo 838352 840175 := bstep (se 1 (by rfl) ⟨630131, by rfl⟩ : syracuseStep 840175 = 1260263) B1260263
theorem B841151 : Blo 838352 841151 := bstep (se 1 (by rfl) ⟨630863, by rfl⟩ : syracuseStep 841151 = 1261727) B1261727
theorem B1890899 : Blo 838352 1890899 := bstep (se 1 (by rfl) ⟨1418174, by rfl⟩ : syracuseStep 1890899 = 2836349) B2836349
theorem B21520079 : Blo 838352 21520079 := bstep (se 1 (by rfl) ⟨16140059, by rfl⟩ : syracuseStep 21520079 = 32280119) B32280119
theorem B9069097 : Blo 838352 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B14546627 : Blo 838352 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B99383111 : Blo 838352 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B4029787 : Blo 838352 4029787 := bstep (se 1 (by rfl) ⟨3022340, by rfl⟩ : syracuseStep 4029787 = 6044681) B6044681
theorem B138052187 : Blo 838352 138052187 := bstep (se 1 (by rfl) ⟨103539140, by rfl⟩ : syracuseStep 138052187 = 207078281) B207078281
theorem B12092129 : Blo 838352 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B4261247 : Blo 838352 4261247 := bstep (se 1 (by rfl) ⟨3195935, by rfl⟩ : syracuseStep 4261247 = 6391871) B6391871
theorem B2131879 : Blo 838352 2131879 := bstep (se 1 (by rfl) ⟨1598909, by rfl⟩ : syracuseStep 2131879 = 3197819) B3197819
theorem B1260599 : Blo 838352 1260599 := bstep (se 1 (by rfl) ⟨945449, by rfl⟩ : syracuseStep 1260599 = 1890899) B1890899
theorem B3196543 : Blo 838352 3196543 := bstep (se 1 (by rfl) ⟨2397407, by rfl⟩ : syracuseStep 3196543 = 4794815) B4794815
theorem B1593769 : Blo 838352 1593769 := bstep (se 2 (by rfl) ⟨597663, by rfl⟩ : syracuseStep 1593769 = 1195327) B1195327
theorem B14346719 : Blo 838352 14346719 := bstep (se 1 (by rfl) ⟨10760039, by rfl⟩ : syracuseStep 14346719 = 21520079) B21520079
theorem B10775213 : Blo 838352 10775213 := bstep (se 3 (by rfl) ⟨2020352, by rfl⟩ : syracuseStep 10775213 = 4040705) B4040705
theorem B9697751 : Blo 838352 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B66255407 : Blo 838352 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B5373049 : Blo 838352 5373049 := bstep (se 2 (by rfl) ⟨2014893, by rfl⟩ : syracuseStep 5373049 = 4029787) B4029787
theorem B8061419 : Blo 838352 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B4262057 : Blo 838352 4262057 := bstep (se 2 (by rfl) ⟨1598271, by rfl⟩ : syracuseStep 4262057 = 3196543) B3196543
theorem B7183475 : Blo 838352 7183475 := bstep (se 1 (by rfl) ⟨5387606, by rfl⟩ : syracuseStep 7183475 = 10775213) B10775213
theorem B6465167 : Blo 838352 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B7164065 : Blo 838352 7164065 := bstep (se 2 (by rfl) ⟨2686524, by rfl⟩ : syracuseStep 7164065 = 5373049) B5373049
theorem B840399 : Blo 838352 840399 := bstep (se 1 (by rfl) ⟨630299, by rfl⟩ : syracuseStep 840399 = 1260599) B1260599
theorem B92034791 : Blo 838352 92034791 := bstep (se 1 (by rfl) ⟨69026093, by rfl⟩ : syracuseStep 92034791 = 138052187) B138052187
theorem B2840831 : Blo 838352 2840831 := bstep (se 1 (by rfl) ⟨2130623, by rfl⟩ : syracuseStep 2840831 = 4261247) B4261247
theorem B2842505 : Blo 838352 2842505 := bstep (se 2 (by rfl) ⟨1065939, by rfl⟩ : syracuseStep 2842505 = 2131879) B2131879
theorem B2125025 : Blo 838352 2125025 := bstep (se 2 (by rfl) ⟨796884, by rfl⟩ : syracuseStep 2125025 = 1593769) B1593769
theorem B9564479 : Blo 838352 9564479 := bstep (se 1 (by rfl) ⟨7173359, by rfl⟩ : syracuseStep 9564479 = 14346719) B14346719
theorem B44170271 : Blo 838352 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B5374279 : Blo 838352 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B4788983 : Blo 838352 4788983 := bstep (se 1 (by rfl) ⟨3591737, by rfl⟩ : syracuseStep 4788983 = 7183475) B7183475
theorem B1416683 : Blo 838352 1416683 := bstep (se 1 (by rfl) ⟨1062512, by rfl⟩ : syracuseStep 1416683 = 2125025) B2125025
theorem B61356527 : Blo 838352 61356527 := bstep (se 1 (by rfl) ⟨46017395, by rfl⟩ : syracuseStep 61356527 = 92034791) B92034791
theorem B4310111 : Blo 838352 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B6376319 : Blo 838352 6376319 := bstep (se 1 (by rfl) ⟨4782239, by rfl⟩ : syracuseStep 6376319 = 9564479) B9564479
theorem B29446847 : Blo 838352 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B2841371 : Blo 838352 2841371 := bstep (se 1 (by rfl) ⟨2131028, by rfl⟩ : syracuseStep 2841371 = 4262057) B4262057
theorem B4776043 : Blo 838352 4776043 := bstep (se 1 (by rfl) ⟨3582032, by rfl⟩ : syracuseStep 4776043 = 7164065) B7164065
theorem B1893887 : Blo 838352 1893887 := bstep (se 1 (by rfl) ⟨1420415, by rfl⟩ : syracuseStep 1893887 = 2840831) B2840831
theorem B1895003 : Blo 838352 1895003 := bstep (se 1 (by rfl) ⟨1421252, by rfl⟩ : syracuseStep 1895003 = 2842505) B2842505
theorem B19631231 : Blo 838352 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B40904351 : Blo 838352 40904351 := bstep (se 1 (by rfl) ⟨30678263, by rfl⟩ : syracuseStep 40904351 = 61356527) B61356527
theorem B6368057 : Blo 838352 6368057 := bstep (se 2 (by rfl) ⟨2388021, by rfl⟩ : syracuseStep 6368057 = 4776043) B4776043
theorem B3192655 : Blo 838352 3192655 := bstep (se 1 (by rfl) ⟨2394491, by rfl⟩ : syracuseStep 3192655 = 4788983) B4788983
theorem B1262591 : Blo 838352 1262591 := bstep (se 1 (by rfl) ⟨946943, by rfl⟩ : syracuseStep 1262591 = 1893887) B1893887
theorem B1263335 : Blo 838352 1263335 := bstep (se 1 (by rfl) ⟨947501, by rfl⟩ : syracuseStep 1263335 = 1895003) B1895003
theorem B7165705 : Blo 838352 7165705 := bstep (se 2 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 7165705 = 5374279) B5374279
theorem B2873407 : Blo 838352 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B4250879 : Blo 838352 4250879 := bstep (se 1 (by rfl) ⟨3188159, by rfl⟩ : syracuseStep 4250879 = 6376319) B6376319
theorem B1894247 : Blo 838352 1894247 := bstep (se 1 (by rfl) ⟨1420685, by rfl⟩ : syracuseStep 1894247 = 2841371) B2841371
theorem B944455 : Blo 838352 944455 := bstep (se 1 (by rfl) ⟨708341, by rfl⟩ : syracuseStep 944455 = 1416683) B1416683
theorem B27269567 : Blo 838352 27269567 := bstep (se 1 (by rfl) ⟨20452175, by rfl⟩ : syracuseStep 27269567 = 40904351) B40904351
theorem B13087487 : Blo 838352 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B1259273 : Blo 838352 1259273 := bstep (se 2 (by rfl) ⟨472227, by rfl⟩ : syracuseStep 1259273 = 944455) B944455
theorem B2833919 : Blo 838352 2833919 := bstep (se 1 (by rfl) ⟨2125439, by rfl⟩ : syracuseStep 2833919 = 4250879) B4250879
theorem B1262831 : Blo 838352 1262831 := bstep (se 1 (by rfl) ⟨947123, by rfl⟩ : syracuseStep 1262831 = 1894247) B1894247
theorem B4245371 : Blo 838352 4245371 := bstep (se 1 (by rfl) ⟨3184028, by rfl⟩ : syracuseStep 4245371 = 6368057) B6368057
theorem B9554273 : Blo 838352 9554273 := bstep (se 2 (by rfl) ⟨3582852, by rfl⟩ : syracuseStep 9554273 = 7165705) B7165705
theorem B841727 : Blo 838352 841727 := bstep (se 1 (by rfl) ⟨631295, by rfl⟩ : syracuseStep 841727 = 1262591) B1262591
theorem B842223 : Blo 838352 842223 := bstep (se 1 (by rfl) ⟨631667, by rfl⟩ : syracuseStep 842223 = 1263335) B1263335
theorem B4256873 : Blo 838352 4256873 := bstep (se 2 (by rfl) ⟨1596327, by rfl⟩ : syracuseStep 4256873 = 3192655) B3192655
theorem B3831209 : Blo 838352 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B8724991 : Blo 838352 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B2830247 : Blo 838352 2830247 := bstep (se 1 (by rfl) ⟨2122685, by rfl⟩ : syracuseStep 2830247 = 4245371) B4245371
theorem B6369515 : Blo 838352 6369515 := bstep (se 1 (by rfl) ⟨4777136, by rfl⟩ : syracuseStep 6369515 = 9554273) B9554273
theorem B2837915 : Blo 838352 2837915 := bstep (se 1 (by rfl) ⟨2128436, by rfl⟩ : syracuseStep 2837915 = 4256873) B4256873
theorem B839515 : Blo 838352 839515 := bstep (se 1 (by rfl) ⟨629636, by rfl⟩ : syracuseStep 839515 = 1259273) B1259273
theorem B1889279 : Blo 838352 1889279 := bstep (se 1 (by rfl) ⟨1416959, by rfl⟩ : syracuseStep 1889279 = 2833919) B2833919
theorem B841887 : Blo 838352 841887 := bstep (se 1 (by rfl) ⟨631415, by rfl⟩ : syracuseStep 841887 = 1262831) B1262831
theorem B18179711 : Blo 838352 18179711 := bstep (se 1 (by rfl) ⟨13634783, by rfl⟩ : syracuseStep 18179711 = 27269567) B27269567
theorem B2554139 : Blo 838352 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B11633321 : Blo 838352 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B1259519 : Blo 838352 1259519 := bstep (se 1 (by rfl) ⟨944639, by rfl⟩ : syracuseStep 1259519 = 1889279) B1889279
theorem B1886831 : Blo 838352 1886831 := bstep (se 1 (by rfl) ⟨1415123, by rfl⟩ : syracuseStep 1886831 = 2830247) B2830247
theorem B4246343 : Blo 838352 4246343 := bstep (se 1 (by rfl) ⟨3184757, by rfl⟩ : syracuseStep 4246343 = 6369515) B6369515
theorem B1891943 : Blo 838352 1891943 := bstep (se 1 (by rfl) ⟨1418957, by rfl⟩ : syracuseStep 1891943 = 2837915) B2837915
theorem B6811037 : Blo 838352 6811037 := bstep (se 3 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 6811037 = 2554139) B2554139
theorem B12119807 : Blo 838352 12119807 := bstep (se 1 (by rfl) ⟨9089855, by rfl⟩ : syracuseStep 12119807 = 18179711) B18179711
theorem B32319485 : Blo 838352 32319485 := bstep (se 3 (by rfl) ⟨6059903, by rfl⟩ : syracuseStep 32319485 = 12119807) B12119807
theorem B1257887 : Blo 838352 1257887 := bstep (se 1 (by rfl) ⟨943415, by rfl⟩ : syracuseStep 1257887 = 1886831) B1886831
theorem B2830895 : Blo 838352 2830895 := bstep (se 1 (by rfl) ⟨2123171, by rfl⟩ : syracuseStep 2830895 = 4246343) B4246343
theorem B1261295 : Blo 838352 1261295 := bstep (se 1 (by rfl) ⟨945971, by rfl⟩ : syracuseStep 1261295 = 1891943) B1891943
theorem B4540691 : Blo 838352 4540691 := bstep (se 1 (by rfl) ⟨3405518, by rfl⟩ : syracuseStep 4540691 = 6811037) B6811037
theorem B839679 : Blo 838352 839679 := bstep (se 1 (by rfl) ⟨629759, by rfl⟩ : syracuseStep 839679 = 1259519) B1259519
theorem B7755547 : Blo 838352 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B3027127 : Blo 838352 3027127 := bstep (se 1 (by rfl) ⟨2270345, by rfl⟩ : syracuseStep 3027127 = 4540691) B4540691
theorem B21546323 : Blo 838352 21546323 := bstep (se 1 (by rfl) ⟨16159742, by rfl⟩ : syracuseStep 21546323 = 32319485) B32319485
theorem B10340729 : Blo 838352 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B838591 : Blo 838352 838591 := bstep (se 1 (by rfl) ⟨628943, by rfl⟩ : syracuseStep 838591 = 1257887) B1257887
theorem B1887263 : Blo 838352 1887263 := bstep (se 1 (by rfl) ⟨1415447, by rfl⟩ : syracuseStep 1887263 = 2830895) B2830895
theorem B840863 : Blo 838352 840863 := bstep (se 1 (by rfl) ⟨630647, by rfl⟩ : syracuseStep 840863 = 1261295) B1261295
theorem B4036169 : Blo 838352 4036169 := bstep (se 2 (by rfl) ⟨1513563, by rfl⟩ : syracuseStep 4036169 = 3027127) B3027127
theorem B14364215 : Blo 838352 14364215 := bstep (se 1 (by rfl) ⟨10773161, by rfl⟩ : syracuseStep 14364215 = 21546323) B21546323
theorem B6893819 : Blo 838352 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B1258175 : Blo 838352 1258175 := bstep (se 1 (by rfl) ⟨943631, by rfl⟩ : syracuseStep 1258175 = 1887263) B1887263
theorem B9576143 : Blo 838352 9576143 := bstep (se 1 (by rfl) ⟨7182107, by rfl⟩ : syracuseStep 9576143 = 14364215) B14364215
theorem B4595879 : Blo 838352 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B10763117 : Blo 838352 10763117 := bstep (se 3 (by rfl) ⟨2018084, by rfl⟩ : syracuseStep 10763117 = 4036169) B4036169
theorem B838783 : Blo 838352 838783 := bstep (se 1 (by rfl) ⟨629087, by rfl⟩ : syracuseStep 838783 = 1258175) B1258175
theorem B3063919 : Blo 838352 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B6384095 : Blo 838352 6384095 := bstep (se 1 (by rfl) ⟨4788071, by rfl⟩ : syracuseStep 6384095 = 9576143) B9576143
theorem B7175411 : Blo 838352 7175411 := bstep (se 1 (by rfl) ⟨5381558, by rfl⟩ : syracuseStep 7175411 = 10763117) B10763117
theorem B4085225 : Blo 838352 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B4256063 : Blo 838352 4256063 := bstep (se 1 (by rfl) ⟨3192047, by rfl⟩ : syracuseStep 4256063 = 6384095) B6384095
theorem B4783607 : Blo 838352 4783607 := bstep (se 1 (by rfl) ⟨3587705, by rfl⟩ : syracuseStep 4783607 = 7175411) B7175411
theorem B2723483 : Blo 838352 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B3189071 : Blo 838352 3189071 := bstep (se 1 (by rfl) ⟨2391803, by rfl⟩ : syracuseStep 3189071 = 4783607) B4783607
theorem B2837375 : Blo 838352 2837375 := bstep (se 1 (by rfl) ⟨2128031, by rfl⟩ : syracuseStep 2837375 = 4256063) B4256063
theorem B1815655 : Blo 838352 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B1891583 : Blo 838352 1891583 := bstep (se 1 (by rfl) ⟨1418687, by rfl⟩ : syracuseStep 1891583 = 2837375) B2837375
theorem B2126047 : Blo 838352 2126047 := bstep (se 1 (by rfl) ⟨1594535, by rfl⟩ : syracuseStep 2126047 = 3189071) B3189071
theorem B1261055 : Blo 838352 1261055 := bstep (se 1 (by rfl) ⟨945791, by rfl⟩ : syracuseStep 1261055 = 1891583) B1891583
theorem B2834729 : Blo 838352 2834729 := bstep (se 2 (by rfl) ⟨1063023, by rfl⟩ : syracuseStep 2834729 = 2126047) B2126047
theorem B2420873 : Blo 838352 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B1613915 : Blo 838352 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B840703 : Blo 838352 840703 := bstep (se 1 (by rfl) ⟨630527, by rfl⟩ : syracuseStep 840703 = 1261055) B1261055
theorem B1889819 : Blo 838352 1889819 := bstep (se 1 (by rfl) ⟨1417364, by rfl⟩ : syracuseStep 1889819 = 2834729) B2834729
theorem B1259879 : Blo 838352 1259879 := bstep (se 1 (by rfl) ⟨944909, by rfl⟩ : syracuseStep 1259879 = 1889819) B1889819
theorem B1075943 : Blo 838352 1075943 := bstep (se 1 (by rfl) ⟨806957, by rfl⟩ : syracuseStep 1075943 = 1613915) B1613915
theorem B2869181 : Blo 838352 2869181 := bstep (se 3 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 2869181 = 1075943) B1075943
theorem B839919 : Blo 838352 839919 := bstep (se 1 (by rfl) ⟨629939, by rfl⟩ : syracuseStep 839919 = 1259879) B1259879
theorem B1912787 : Blo 838352 1912787 := bstep (se 1 (by rfl) ⟨1434590, by rfl⟩ : syracuseStep 1912787 = 2869181) B2869181
theorem B1275191 : Blo 838352 1275191 := bstep (se 1 (by rfl) ⟨956393, by rfl⟩ : syracuseStep 1275191 = 1912787) B1912787
theorem B850127 : Blo 838352 850127 := bstep (se 1 (by rfl) ⟨637595, by rfl⟩ : syracuseStep 850127 = 1275191) B1275191
theorem B9068021 : Blo 838352 9068021 := bstep (se 5 (by rfl) ⟨425063, by rfl⟩ : syracuseStep 9068021 = 850127) B850127
theorem B6045347 : Blo 838352 6045347 := bstep (se 1 (by rfl) ⟨4534010, by rfl⟩ : syracuseStep 6045347 = 9068021) B9068021
theorem B4030231 : Blo 838352 4030231 := bstep (se 1 (by rfl) ⟨3022673, by rfl⟩ : syracuseStep 4030231 = 6045347) B6045347
theorem B5373641 : Blo 838352 5373641 := bstep (se 2 (by rfl) ⟨2015115, by rfl⟩ : syracuseStep 5373641 = 4030231) B4030231
theorem B3582427 : Blo 838352 3582427 := bstep (se 1 (by rfl) ⟨2686820, by rfl⟩ : syracuseStep 3582427 = 5373641) B5373641
theorem B4776569 : Blo 838352 4776569 := bstep (se 2 (by rfl) ⟨1791213, by rfl⟩ : syracuseStep 4776569 = 3582427) B3582427
theorem B3184379 : Blo 838352 3184379 := bstep (se 1 (by rfl) ⟨2388284, by rfl⟩ : syracuseStep 3184379 = 4776569) B4776569
theorem B2122919 : Blo 838352 2122919 := bstep (se 1 (by rfl) ⟨1592189, by rfl⟩ : syracuseStep 2122919 = 3184379) B3184379
theorem B1415279 : Blo 838352 1415279 := bstep (se 1 (by rfl) ⟨1061459, by rfl⟩ : syracuseStep 1415279 = 2122919) B2122919
theorem B943519 : Blo 838352 943519 := bstep (se 1 (by rfl) ⟨707639, by rfl⟩ : syracuseStep 943519 = 1415279) B1415279
theorem B1258025 : Blo 838352 1258025 := bstep (se 2 (by rfl) ⟨471759, by rfl⟩ : syracuseStep 1258025 = 943519) B943519
theorem B838683 : Blo 838352 838683 := bstep (se 1 (by rfl) ⟨629012, by rfl⟩ : syracuseStep 838683 = 1258025) B1258025

theorem C0 (j : ℕ) (h1 : 209588 ≤ j) (h2 : j ≤ 210287) : Blo 838352 (4 * j + 3) := by
  interval_cases j
  · exact B838355
  · exact B838359
  · exact B838363
  · exact B838367
  · exact B838371
  · exact B838375
  · exact B838379
  · exact B838383
  · exact B838387
  · exact B838391
  · exact B838395
  · exact B838399
  · exact B838403
  · exact B838407
  · exact B838411
  · exact B838415
  · exact B838419
  · exact B838423
  · exact B838427
  · exact B838431
  · exact B838435
  · exact B838439
  · exact B838443
  · exact B838447
  · exact B838451
  · exact B838455
  · exact B838459
  · exact B838463
  · exact B838467
  · exact B838471
  · exact B838475
  · exact B838479
  · exact B838483
  · exact B838487
  · exact B838491
  · exact B838495
  · exact B838499
  · exact B838503
  · exact B838507
  · exact B838511
  · exact B838515
  · exact B838519
  · exact B838523
  · exact B838527
  · exact B838531
  · exact B838535
  · exact B838539
  · exact B838543
  · exact B838547
  · exact B838551
  · exact B838555
  · exact B838559
  · exact B838563
  · exact B838567
  · exact B838571
  · exact B838575
  · exact B838579
  · exact B838583
  · exact B838587
  · exact B838591
  · exact B838595
  · exact B838599
  · exact B838603
  · exact B838607
  · exact B838611
  · exact B838615
  · exact B838619
  · exact B838623
  · exact B838627
  · exact B838631
  · exact B838635
  · exact B838639
  · exact B838643
  · exact B838647
  · exact B838651
  · exact B838655
  · exact B838659
  · exact B838663
  · exact B838667
  · exact B838671
  · exact B838675
  · exact B838679
  · exact B838683
  · exact B838687
  · exact B838691
  · exact B838695
  · exact B838699
  · exact B838703
  · exact B838707
  · exact B838711
  · exact B838715
  · exact B838719
  · exact B838723
  · exact B838727
  · exact B838731
  · exact B838735
  · exact B838739
  · exact B838743
  · exact B838747
  · exact B838751
  · exact B838755
  · exact B838759
  · exact B838763
  · exact B838767
  · exact B838771
  · exact B838775
  · exact B838779
  · exact B838783
  · exact B838787
  · exact B838791
  · exact B838795
  · exact B838799
  · exact B838803
  · exact B838807
  · exact B838811
  · exact B838815
  · exact B838819
  · exact B838823
  · exact B838827
  · exact B838831
  · exact B838835
  · exact B838839
  · exact B838843
  · exact B838847
  · exact B838851
  · exact B838855
  · exact B838859
  · exact B838863
  · exact B838867
  · exact B838871
  · exact B838875
  · exact B838879
  · exact B838883
  · exact B838887
  · exact B838891
  · exact B838895
  · exact B838899
  · exact B838903
  · exact B838907
  · exact B838911
  · exact B838915
  · exact B838919
  · exact B838923
  · exact B838927
  · exact B838931
  · exact B838935
  · exact B838939
  · exact B838943
  · exact B838947
  · exact B838951
  · exact B838955
  · exact B838959
  · exact B838963
  · exact B838967
  · exact B838971
  · exact B838975
  · exact B838979
  · exact B838983
  · exact B838987
  · exact B838991
  · exact B838995
  · exact B838999
  · exact B839003
  · exact B839007
  · exact B839011
  · exact B839015
  · exact B839019
  · exact B839023
  · exact B839027
  · exact B839031
  · exact B839035
  · exact B839039
  · exact B839043
  · exact B839047
  · exact B839051
  · exact B839055
  · exact B839059
  · exact B839063
  · exact B839067
  · exact B839071
  · exact B839075
  · exact B839079
  · exact B839083
  · exact B839087
  · exact B839091
  · exact B839095
  · exact B839099
  · exact B839103
  · exact B839107
  · exact B839111
  · exact B839115
  · exact B839119
  · exact B839123
  · exact B839127
  · exact B839131
  · exact B839135
  · exact B839139
  · exact B839143
  · exact B839147
  · exact B839151
  · exact B839155
  · exact B839159
  · exact B839163
  · exact B839167
  · exact B839171
  · exact B839175
  · exact B839179
  · exact B839183
  · exact B839187
  · exact B839191
  · exact B839195
  · exact B839199
  · exact B839203
  · exact B839207
  · exact B839211
  · exact B839215
  · exact B839219
  · exact B839223
  · exact B839227
  · exact B839231
  · exact B839235
  · exact B839239
  · exact B839243
  · exact B839247
  · exact B839251
  · exact B839255
  · exact B839259
  · exact B839263
  · exact B839267
  · exact B839271
  · exact B839275
  · exact B839279
  · exact B839283
  · exact B839287
  · exact B839291
  · exact B839295
  · exact B839299
  · exact B839303
  · exact B839307
  · exact B839311
  · exact B839315
  · exact B839319
  · exact B839323
  · exact B839327
  · exact B839331
  · exact B839335
  · exact B839339
  · exact B839343
  · exact B839347
  · exact B839351
  · exact B839355
  · exact B839359
  · exact B839363
  · exact B839367
  · exact B839371
  · exact B839375
  · exact B839379
  · exact B839383
  · exact B839387
  · exact B839391
  · exact B839395
  · exact B839399
  · exact B839403
  · exact B839407
  · exact B839411
  · exact B839415
  · exact B839419
  · exact B839423
  · exact B839427
  · exact B839431
  · exact B839435
  · exact B839439
  · exact B839443
  · exact B839447
  · exact B839451
  · exact B839455
  · exact B839459
  · exact B839463
  · exact B839467
  · exact B839471
  · exact B839475
  · exact B839479
  · exact B839483
  · exact B839487
  · exact B839491
  · exact B839495
  · exact B839499
  · exact B839503
  · exact B839507
  · exact B839511
  · exact B839515
  · exact B839519
  · exact B839523
  · exact B839527
  · exact B839531
  · exact B839535
  · exact B839539
  · exact B839543
  · exact B839547
  · exact B839551
  · exact B839555
  · exact B839559
  · exact B839563
  · exact B839567
  · exact B839571
  · exact B839575
  · exact B839579
  · exact B839583
  · exact B839587
  · exact B839591
  · exact B839595
  · exact B839599
  · exact B839603
  · exact B839607
  · exact B839611
  · exact B839615
  · exact B839619
  · exact B839623
  · exact B839627
  · exact B839631
  · exact B839635
  · exact B839639
  · exact B839643
  · exact B839647
  · exact B839651
  · exact B839655
  · exact B839659
  · exact B839663
  · exact B839667
  · exact B839671
  · exact B839675
  · exact B839679
  · exact B839683
  · exact B839687
  · exact B839691
  · exact B839695
  · exact B839699
  · exact B839703
  · exact B839707
  · exact B839711
  · exact B839715
  · exact B839719
  · exact B839723
  · exact B839727
  · exact B839731
  · exact B839735
  · exact B839739
  · exact B839743
  · exact B839747
  · exact B839751
  · exact B839755
  · exact B839759
  · exact B839763
  · exact B839767
  · exact B839771
  · exact B839775
  · exact B839779
  · exact B839783
  · exact B839787
  · exact B839791
  · exact B839795
  · exact B839799
  · exact B839803
  · exact B839807
  · exact B839811
  · exact B839815
  · exact B839819
  · exact B839823
  · exact B839827
  · exact B839831
  · exact B839835
  · exact B839839
  · exact B839843
  · exact B839847
  · exact B839851
  · exact B839855
  · exact B839859
  · exact B839863
  · exact B839867
  · exact B839871
  · exact B839875
  · exact B839879
  · exact B839883
  · exact B839887
  · exact B839891
  · exact B839895
  · exact B839899
  · exact B839903
  · exact B839907
  · exact B839911
  · exact B839915
  · exact B839919
  · exact B839923
  · exact B839927
  · exact B839931
  · exact B839935
  · exact B839939
  · exact B839943
  · exact B839947
  · exact B839951
  · exact B839955
  · exact B839959
  · exact B839963
  · exact B839967
  · exact B839971
  · exact B839975
  · exact B839979
  · exact B839983
  · exact B839987
  · exact B839991
  · exact B839995
  · exact B839999
  · exact B840003
  · exact B840007
  · exact B840011
  · exact B840015
  · exact B840019
  · exact B840023
  · exact B840027
  · exact B840031
  · exact B840035
  · exact B840039
  · exact B840043
  · exact B840047
  · exact B840051
  · exact B840055
  · exact B840059
  · exact B840063
  · exact B840067
  · exact B840071
  · exact B840075
  · exact B840079
  · exact B840083
  · exact B840087
  · exact B840091
  · exact B840095
  · exact B840099
  · exact B840103
  · exact B840107
  · exact B840111
  · exact B840115
  · exact B840119
  · exact B840123
  · exact B840127
  · exact B840131
  · exact B840135
  · exact B840139
  · exact B840143
  · exact B840147
  · exact B840151
  · exact B840155
  · exact B840159
  · exact B840163
  · exact B840167
  · exact B840171
  · exact B840175
  · exact B840179
  · exact B840183
  · exact B840187
  · exact B840191
  · exact B840195
  · exact B840199
  · exact B840203
  · exact B840207
  · exact B840211
  · exact B840215
  · exact B840219
  · exact B840223
  · exact B840227
  · exact B840231
  · exact B840235
  · exact B840239
  · exact B840243
  · exact B840247
  · exact B840251
  · exact B840255
  · exact B840259
  · exact B840263
  · exact B840267
  · exact B840271
  · exact B840275
  · exact B840279
  · exact B840283
  · exact B840287
  · exact B840291
  · exact B840295
  · exact B840299
  · exact B840303
  · exact B840307
  · exact B840311
  · exact B840315
  · exact B840319
  · exact B840323
  · exact B840327
  · exact B840331
  · exact B840335
  · exact B840339
  · exact B840343
  · exact B840347
  · exact B840351
  · exact B840355
  · exact B840359
  · exact B840363
  · exact B840367
  · exact B840371
  · exact B840375
  · exact B840379
  · exact B840383
  · exact B840387
  · exact B840391
  · exact B840395
  · exact B840399
  · exact B840403
  · exact B840407
  · exact B840411
  · exact B840415
  · exact B840419
  · exact B840423
  · exact B840427
  · exact B840431
  · exact B840435
  · exact B840439
  · exact B840443
  · exact B840447
  · exact B840451
  · exact B840455
  · exact B840459
  · exact B840463
  · exact B840467
  · exact B840471
  · exact B840475
  · exact B840479
  · exact B840483
  · exact B840487
  · exact B840491
  · exact B840495
  · exact B840499
  · exact B840503
  · exact B840507
  · exact B840511
  · exact B840515
  · exact B840519
  · exact B840523
  · exact B840527
  · exact B840531
  · exact B840535
  · exact B840539
  · exact B840543
  · exact B840547
  · exact B840551
  · exact B840555
  · exact B840559
  · exact B840563
  · exact B840567
  · exact B840571
  · exact B840575
  · exact B840579
  · exact B840583
  · exact B840587
  · exact B840591
  · exact B840595
  · exact B840599
  · exact B840603
  · exact B840607
  · exact B840611
  · exact B840615
  · exact B840619
  · exact B840623
  · exact B840627
  · exact B840631
  · exact B840635
  · exact B840639
  · exact B840643
  · exact B840647
  · exact B840651
  · exact B840655
  · exact B840659
  · exact B840663
  · exact B840667
  · exact B840671
  · exact B840675
  · exact B840679
  · exact B840683
  · exact B840687
  · exact B840691
  · exact B840695
  · exact B840699
  · exact B840703
  · exact B840707
  · exact B840711
  · exact B840715
  · exact B840719
  · exact B840723
  · exact B840727
  · exact B840731
  · exact B840735
  · exact B840739
  · exact B840743
  · exact B840747
  · exact B840751
  · exact B840755
  · exact B840759
  · exact B840763
  · exact B840767
  · exact B840771
  · exact B840775
  · exact B840779
  · exact B840783
  · exact B840787
  · exact B840791
  · exact B840795
  · exact B840799
  · exact B840803
  · exact B840807
  · exact B840811
  · exact B840815
  · exact B840819
  · exact B840823
  · exact B840827
  · exact B840831
  · exact B840835
  · exact B840839
  · exact B840843
  · exact B840847
  · exact B840851
  · exact B840855
  · exact B840859
  · exact B840863
  · exact B840867
  · exact B840871
  · exact B840875
  · exact B840879
  · exact B840883
  · exact B840887
  · exact B840891
  · exact B840895
  · exact B840899
  · exact B840903
  · exact B840907
  · exact B840911
  · exact B840915
  · exact B840919
  · exact B840923
  · exact B840927
  · exact B840931
  · exact B840935
  · exact B840939
  · exact B840943
  · exact B840947
  · exact B840951
  · exact B840955
  · exact B840959
  · exact B840963
  · exact B840967
  · exact B840971
  · exact B840975
  · exact B840979
  · exact B840983
  · exact B840987
  · exact B840991
  · exact B840995
  · exact B840999
  · exact B841003
  · exact B841007
  · exact B841011
  · exact B841015
  · exact B841019
  · exact B841023
  · exact B841027
  · exact B841031
  · exact B841035
  · exact B841039
  · exact B841043
  · exact B841047
  · exact B841051
  · exact B841055
  · exact B841059
  · exact B841063
  · exact B841067
  · exact B841071
  · exact B841075
  · exact B841079
  · exact B841083
  · exact B841087
  · exact B841091
  · exact B841095
  · exact B841099
  · exact B841103
  · exact B841107
  · exact B841111
  · exact B841115
  · exact B841119
  · exact B841123
  · exact B841127
  · exact B841131
  · exact B841135
  · exact B841139
  · exact B841143
  · exact B841147
  · exact B841151

theorem C1 (j : ℕ) (h1 : 210288 ≤ j) (h2 : j ≤ 210587) : Blo 838352 (4 * j + 3) := by
  interval_cases j
  · exact B841155
  · exact B841159
  · exact B841163
  · exact B841167
  · exact B841171
  · exact B841175
  · exact B841179
  · exact B841183
  · exact B841187
  · exact B841191
  · exact B841195
  · exact B841199
  · exact B841203
  · exact B841207
  · exact B841211
  · exact B841215
  · exact B841219
  · exact B841223
  · exact B841227
  · exact B841231
  · exact B841235
  · exact B841239
  · exact B841243
  · exact B841247
  · exact B841251
  · exact B841255
  · exact B841259
  · exact B841263
  · exact B841267
  · exact B841271
  · exact B841275
  · exact B841279
  · exact B841283
  · exact B841287
  · exact B841291
  · exact B841295
  · exact B841299
  · exact B841303
  · exact B841307
  · exact B841311
  · exact B841315
  · exact B841319
  · exact B841323
  · exact B841327
  · exact B841331
  · exact B841335
  · exact B841339
  · exact B841343
  · exact B841347
  · exact B841351
  · exact B841355
  · exact B841359
  · exact B841363
  · exact B841367
  · exact B841371
  · exact B841375
  · exact B841379
  · exact B841383
  · exact B841387
  · exact B841391
  · exact B841395
  · exact B841399
  · exact B841403
  · exact B841407
  · exact B841411
  · exact B841415
  · exact B841419
  · exact B841423
  · exact B841427
  · exact B841431
  · exact B841435
  · exact B841439
  · exact B841443
  · exact B841447
  · exact B841451
  · exact B841455
  · exact B841459
  · exact B841463
  · exact B841467
  · exact B841471
  · exact B841475
  · exact B841479
  · exact B841483
  · exact B841487
  · exact B841491
  · exact B841495
  · exact B841499
  · exact B841503
  · exact B841507
  · exact B841511
  · exact B841515
  · exact B841519
  · exact B841523
  · exact B841527
  · exact B841531
  · exact B841535
  · exact B841539
  · exact B841543
  · exact B841547
  · exact B841551
  · exact B841555
  · exact B841559
  · exact B841563
  · exact B841567
  · exact B841571
  · exact B841575
  · exact B841579
  · exact B841583
  · exact B841587
  · exact B841591
  · exact B841595
  · exact B841599
  · exact B841603
  · exact B841607
  · exact B841611
  · exact B841615
  · exact B841619
  · exact B841623
  · exact B841627
  · exact B841631
  · exact B841635
  · exact B841639
  · exact B841643
  · exact B841647
  · exact B841651
  · exact B841655
  · exact B841659
  · exact B841663
  · exact B841667
  · exact B841671
  · exact B841675
  · exact B841679
  · exact B841683
  · exact B841687
  · exact B841691
  · exact B841695
  · exact B841699
  · exact B841703
  · exact B841707
  · exact B841711
  · exact B841715
  · exact B841719
  · exact B841723
  · exact B841727
  · exact B841731
  · exact B841735
  · exact B841739
  · exact B841743
  · exact B841747
  · exact B841751
  · exact B841755
  · exact B841759
  · exact B841763
  · exact B841767
  · exact B841771
  · exact B841775
  · exact B841779
  · exact B841783
  · exact B841787
  · exact B841791
  · exact B841795
  · exact B841799
  · exact B841803
  · exact B841807
  · exact B841811
  · exact B841815
  · exact B841819
  · exact B841823
  · exact B841827
  · exact B841831
  · exact B841835
  · exact B841839
  · exact B841843
  · exact B841847
  · exact B841851
  · exact B841855
  · exact B841859
  · exact B841863
  · exact B841867
  · exact B841871
  · exact B841875
  · exact B841879
  · exact B841883
  · exact B841887
  · exact B841891
  · exact B841895
  · exact B841899
  · exact B841903
  · exact B841907
  · exact B841911
  · exact B841915
  · exact B841919
  · exact B841923
  · exact B841927
  · exact B841931
  · exact B841935
  · exact B841939
  · exact B841943
  · exact B841947
  · exact B841951
  · exact B841955
  · exact B841959
  · exact B841963
  · exact B841967
  · exact B841971
  · exact B841975
  · exact B841979
  · exact B841983
  · exact B841987
  · exact B841991
  · exact B841995
  · exact B841999
  · exact B842003
  · exact B842007
  · exact B842011
  · exact B842015
  · exact B842019
  · exact B842023
  · exact B842027
  · exact B842031
  · exact B842035
  · exact B842039
  · exact B842043
  · exact B842047
  · exact B842051
  · exact B842055
  · exact B842059
  · exact B842063
  · exact B842067
  · exact B842071
  · exact B842075
  · exact B842079
  · exact B842083
  · exact B842087
  · exact B842091
  · exact B842095
  · exact B842099
  · exact B842103
  · exact B842107
  · exact B842111
  · exact B842115
  · exact B842119
  · exact B842123
  · exact B842127
  · exact B842131
  · exact B842135
  · exact B842139
  · exact B842143
  · exact B842147
  · exact B842151
  · exact B842155
  · exact B842159
  · exact B842163
  · exact B842167
  · exact B842171
  · exact B842175
  · exact B842179
  · exact B842183
  · exact B842187
  · exact B842191
  · exact B842195
  · exact B842199
  · exact B842203
  · exact B842207
  · exact B842211
  · exact B842215
  · exact B842219
  · exact B842223
  · exact B842227
  · exact B842231
  · exact B842235
  · exact B842239
  · exact B842243
  · exact B842247
  · exact B842251
  · exact B842255
  · exact B842259
  · exact B842263
  · exact B842267
  · exact B842271
  · exact B842275
  · exact B842279
  · exact B842283
  · exact B842287
  · exact B842291
  · exact B842295
  · exact B842299
  · exact B842303
  · exact B842307
  · exact B842311
  · exact B842315
  · exact B842319
  · exact B842323
  · exact B842327
  · exact B842331
  · exact B842335
  · exact B842339
  · exact B842343
  · exact B842347
  · exact B842351

theorem solution (m : ℕ) (hlo : 838352 ≤ m) (hhi : m ≤ 842352) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 209588 ≤ j := by omega
    have hj2 : j ≤ 210587 := by omega
    have hb : Blo 838352 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 210288 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
