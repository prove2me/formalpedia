-- Prove2me | solution 1 for syracuse_descends_range_1248442_1250442
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:15.34636+00:00
-- url     : https://prove2.me/submissions/f89592ba-fba3-44e0-ac9d-37b1b74ff84b

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


theorem B3424277 : Blo 1248442 3424277 := bbase (se 6 (by rfl) ⟨80256, by rfl⟩ : syracuseStep 3424277 = 160513) (by norm_num)
theorem B3162149 : Blo 1248442 3162149 := bbase (se 4 (by rfl) ⟨296451, by rfl⟩ : syracuseStep 3162149 = 592903) (by norm_num)
theorem B2809925 : Blo 1248442 2809925 := bbase (se 4 (by rfl) ⟨263430, by rfl⟩ : syracuseStep 2809925 = 526861) (by norm_num)
theorem B4218965 : Blo 1248442 4218965 := bbase (se 8 (by rfl) ⟨24720, by rfl⟩ : syracuseStep 4218965 = 49441) (by norm_num)
theorem B4743269 : Blo 1248442 4743269 := bbase (se 4 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 4743269 = 889363) (by norm_num)
theorem B2809997 : Blo 1248442 2809997 := bbase (se 3 (by rfl) ⟨526874, by rfl⟩ : syracuseStep 2809997 = 1053749) (by norm_num)
theorem B1581221 : Blo 1248442 1581221 := bbase (se 4 (by rfl) ⟨148239, by rfl⟩ : syracuseStep 1581221 = 296479) (by norm_num)
theorem B4276421 : Blo 1248442 4276421 := bbase (se 4 (by rfl) ⟨400914, by rfl⟩ : syracuseStep 4276421 = 801829) (by norm_num)
theorem B2810069 : Blo 1248442 2810069 := bbase (se 7 (by rfl) ⟨32930, by rfl⟩ : syracuseStep 2810069 = 65861) (by norm_num)
theorem B1581277 : Blo 1248442 1581277 := bbase (se 3 (by rfl) ⟨296489, by rfl⟩ : syracuseStep 1581277 = 592979) (by norm_num)
theorem B1900765 : Blo 1248442 1900765 := bbase (se 3 (by rfl) ⟨356393, by rfl⟩ : syracuseStep 1900765 = 712787) (by norm_num)
theorem B3162341 : Blo 1248442 3162341 := bbase (se 4 (by rfl) ⟨296469, by rfl⟩ : syracuseStep 3162341 = 592939) (by norm_num)
theorem B2810141 : Blo 1248442 2810141 := bbase (se 3 (by rfl) ⟨526901, by rfl⟩ : syracuseStep 2810141 = 1053803) (by norm_num)
theorem B1581373 : Blo 1248442 1581373 := bbase (se 3 (by rfl) ⟨296507, by rfl⟩ : syracuseStep 1581373 = 593015) (by norm_num)
theorem B1777997 : Blo 1248442 1777997 := bbase (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) (by norm_num)
theorem B12165461 : Blo 1248442 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B8552789 : Blo 1248442 8552789 := bbase (se 10 (by rfl) ⟨12528, by rfl⟩ : syracuseStep 8552789 = 25057) (by norm_num)
theorem B2531677 : Blo 1248442 2531677 := bbase (se 3 (by rfl) ⟨474689, by rfl⟩ : syracuseStep 2531677 = 949379) (by norm_num)
theorem B2810213 : Blo 1248442 2810213 := bbase (se 4 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 2810213 = 526915) (by norm_num)
theorem B6414709 : Blo 1248442 6414709 := bbase (se 5 (by rfl) ⟨300689, by rfl⟩ : syracuseStep 6414709 = 601379) (by norm_num)
theorem B2810285 : Blo 1248442 2810285 := bbase (se 3 (by rfl) ⟨526928, by rfl⟩ : syracuseStep 2810285 = 1053857) (by norm_num)
theorem B1581545 : Blo 1248442 1581545 := bbase (se 2 (by rfl) ⟨593079, by rfl⟩ : syracuseStep 1581545 = 1186159) (by norm_num)
theorem B2810357 : Blo 1248442 2810357 := bbase (se 5 (by rfl) ⟨131735, by rfl⟩ : syracuseStep 2810357 = 263471) (by norm_num)
theorem B4219397 : Blo 1248442 4219397 := bbase (se 4 (by rfl) ⟨395568, by rfl⟩ : syracuseStep 4219397 = 791137) (by norm_num)
theorem B1425929 : Blo 1248442 1425929 := bbase (se 2 (by rfl) ⟨534723, by rfl⟩ : syracuseStep 1425929 = 1069447) (by norm_num)
theorem B1581601 : Blo 1248442 1581601 := bbase (se 2 (by rfl) ⟨593100, by rfl⟩ : syracuseStep 1581601 = 1186201) (by norm_num)
theorem B1688125 : Blo 1248442 1688125 := bbase (se 3 (by rfl) ⟨316523, by rfl⟩ : syracuseStep 1688125 = 633047) (by norm_num)
theorem B2810429 : Blo 1248442 2810429 := bbase (se 3 (by rfl) ⟨526955, by rfl⟩ : syracuseStep 2810429 = 1053911) (by norm_num)
theorem B3162685 : Blo 1248442 3162685 := bbase (se 3 (by rfl) ⟨593003, by rfl⟩ : syracuseStep 3162685 = 1186007) (by norm_num)
theorem B1581697 : Blo 1248442 1581697 := bbase (se 2 (by rfl) ⟨593136, by rfl⟩ : syracuseStep 1581697 = 1186273) (by norm_num)
theorem B2810501 : Blo 1248442 2810501 := bbase (se 4 (by rfl) ⟨263484, by rfl⟩ : syracuseStep 2810501 = 526969) (by norm_num)
theorem B3162797 : Blo 1248442 3162797 := bbase (se 3 (by rfl) ⟨593024, by rfl⟩ : syracuseStep 3162797 = 1186049) (by norm_num)
theorem B9011893 : Blo 1248442 9011893 := bbase (se 5 (by rfl) ⟨422432, by rfl⟩ : syracuseStep 9011893 = 844865) (by norm_num)
theorem B4506293 : Blo 1248442 4506293 := bbase (se 5 (by rfl) ⟨211232, by rfl⟩ : syracuseStep 4506293 = 422465) (by norm_num)
theorem B2810573 : Blo 1248442 2810573 := bbase (se 3 (by rfl) ⟨526982, by rfl⟩ : syracuseStep 2810573 = 1053965) (by norm_num)
theorem B6324965 : Blo 1248442 6324965 := bbase (se 4 (by rfl) ⟨592965, by rfl⟩ : syracuseStep 6324965 = 1185931) (by norm_num)
theorem B6087413 : Blo 1248442 6087413 := bbase (se 5 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 6087413 = 570695) (by norm_num)
theorem B9003797 : Blo 1248442 9003797 := bbase (se 6 (by rfl) ⟨211026, by rfl⟩ : syracuseStep 9003797 = 422053) (by norm_num)
theorem B2810645 : Blo 1248442 2810645 := bbase (se 6 (by rfl) ⟨65874, by rfl⟩ : syracuseStep 2810645 = 131749) (by norm_num)
theorem B1581869 : Blo 1248442 1581869 := bbase (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) (by norm_num)
theorem B2810717 : Blo 1248442 2810717 := bbase (se 3 (by rfl) ⟨527009, by rfl⟩ : syracuseStep 2810717 = 1054019) (by norm_num)
theorem B2532197 : Blo 1248442 2532197 := bbase (se 4 (by rfl) ⟨237393, by rfl⟩ : syracuseStep 2532197 = 474787) (by norm_num)
theorem B1581925 : Blo 1248442 1581925 := bbase (se 4 (by rfl) ⟨148305, by rfl⟩ : syracuseStep 1581925 = 296611) (by norm_num)
theorem B3162989 : Blo 1248442 3162989 := bbase (se 3 (by rfl) ⟨593060, by rfl⟩ : syracuseStep 3162989 = 1186121) (by norm_num)
theorem B2810789 : Blo 1248442 2810789 := bbase (se 4 (by rfl) ⟨263511, by rfl⟩ : syracuseStep 2810789 = 527023) (by norm_num)
theorem B4219829 : Blo 1248442 4219829 := bbase (se 5 (by rfl) ⟨197804, by rfl⟩ : syracuseStep 4219829 = 395609) (by norm_num)
theorem B5333957 : Blo 1248442 5333957 := bbase (se 4 (by rfl) ⟨500058, by rfl⟩ : syracuseStep 5333957 = 1000117) (by norm_num)
theorem B1582021 : Blo 1248442 1582021 := bbase (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) (by norm_num)
theorem B1999837 : Blo 1248442 1999837 := bbase (se 3 (by rfl) ⟨374969, by rfl⟩ : syracuseStep 1999837 = 749939) (by norm_num)
theorem B3556325 : Blo 1248442 3556325 := bbase (se 4 (by rfl) ⟨333405, by rfl⟩ : syracuseStep 3556325 = 666811) (by norm_num)
theorem B2810861 : Blo 1248442 2810861 := bbase (se 3 (by rfl) ⟨527036, by rfl⟩ : syracuseStep 2810861 = 1054073) (by norm_num)
theorem B1500157 : Blo 1248442 1500157 := bbase (se 3 (by rfl) ⟨281279, by rfl⟩ : syracuseStep 1500157 = 562559) (by norm_num)
theorem B2810933 : Blo 1248442 2810933 := bbase (se 5 (by rfl) ⟨131762, by rfl⟩ : syracuseStep 2810933 = 263525) (by norm_num)
theorem B7603253 : Blo 1248442 7603253 := bbase (se 5 (by rfl) ⟨356402, by rfl⟩ : syracuseStep 7603253 = 712805) (by norm_num)
theorem B58491989 : Blo 1248442 58491989 := bbase (se 8 (by rfl) ⟨342726, by rfl⟩ : syracuseStep 58491989 = 685453) (by norm_num)
theorem B1582193 : Blo 1248442 1582193 := bbase (se 2 (by rfl) ⟨593322, by rfl⟩ : syracuseStep 1582193 = 1186645) (by norm_num)
theorem B2811005 : Blo 1248442 2811005 := bbase (se 3 (by rfl) ⟨527063, by rfl⟩ : syracuseStep 2811005 = 1054127) (by norm_num)
theorem B1582249 : Blo 1248442 1582249 := bbase (se 2 (by rfl) ⟨593343, by rfl⟩ : syracuseStep 1582249 = 1186687) (by norm_num)
theorem B1500349 : Blo 1248442 1500349 := bbase (se 3 (by rfl) ⟨281315, by rfl⟩ : syracuseStep 1500349 = 562631) (by norm_num)
theorem B2811077 : Blo 1248442 2811077 := bbase (se 4 (by rfl) ⟨263538, by rfl⟩ : syracuseStep 2811077 = 527077) (by norm_num)
theorem B3163333 : Blo 1248442 3163333 := bbase (se 4 (by rfl) ⟨296562, by rfl⟩ : syracuseStep 3163333 = 593125) (by norm_num)
theorem B4744453 : Blo 1248442 4744453 := bbase (se 4 (by rfl) ⟨444792, by rfl⟩ : syracuseStep 4744453 = 889585) (by norm_num)
theorem B1582345 : Blo 1248442 1582345 := bbase (se 2 (by rfl) ⟨593379, by rfl⟩ : syracuseStep 1582345 = 1186759) (by norm_num)
theorem B2811149 : Blo 1248442 2811149 := bbase (se 3 (by rfl) ⟨527090, by rfl⟩ : syracuseStep 2811149 = 1054181) (by norm_num)
theorem B1688845 : Blo 1248442 1688845 := bbase (se 3 (by rfl) ⟨316658, by rfl⟩ : syracuseStep 1688845 = 633317) (by norm_num)
theorem B3802405 : Blo 1248442 3802405 := bbase (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) (by norm_num)
theorem B3163445 : Blo 1248442 3163445 := bbase (se 5 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 3163445 = 296573) (by norm_num)
theorem B1500493 : Blo 1248442 1500493 := bbase (se 3 (by rfl) ⟨281342, by rfl⟩ : syracuseStep 1500493 = 562685) (by norm_num)
theorem B2811221 : Blo 1248442 2811221 := bbase (se 12 (by rfl) ⟨1029, by rfl⟩ : syracuseStep 2811221 = 2059) (by norm_num)
theorem B2106749 : Blo 1248442 2106749 := bbase (se 3 (by rfl) ⟨395015, by rfl⟩ : syracuseStep 2106749 = 790031) (by norm_num)
theorem B8005013 : Blo 1248442 8005013 := bbase (se 6 (by rfl) ⟨187617, by rfl⟩ : syracuseStep 8005013 = 375235) (by norm_num)
theorem B2811293 : Blo 1248442 2811293 := bbase (se 3 (by rfl) ⟨527117, by rfl⟩ : syracuseStep 2811293 = 1054235) (by norm_num)
theorem B10675637 : Blo 1248442 10675637 := bbase (se 5 (by rfl) ⟨500420, by rfl⟩ : syracuseStep 10675637 = 1000841) (by norm_num)
theorem B1582517 : Blo 1248442 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B2532797 : Blo 1248442 2532797 := bbase (se 3 (by rfl) ⟨474899, by rfl⟩ : syracuseStep 2532797 = 949799) (by norm_num)
theorem B2811365 : Blo 1248442 2811365 := bbase (se 4 (by rfl) ⟨263565, by rfl⟩ : syracuseStep 2811365 = 527131) (by norm_num)
theorem B1582573 : Blo 1248442 1582573 := bbase (se 3 (by rfl) ⟨296732, by rfl⟩ : syracuseStep 1582573 = 593465) (by norm_num)
theorem B3163637 : Blo 1248442 3163637 := bbase (se 5 (by rfl) ⟨148295, by rfl⟩ : syracuseStep 3163637 = 296591) (by norm_num)
theorem B2106877 : Blo 1248442 2106877 := bbase (se 3 (by rfl) ⟨395039, by rfl⟩ : syracuseStep 2106877 = 790079) (by norm_num)
theorem B2811437 : Blo 1248442 2811437 := bbase (se 3 (by rfl) ⟨527144, by rfl⟩ : syracuseStep 2811437 = 1054289) (by norm_num)
theorem B4744757 : Blo 1248442 4744757 := bbase (se 5 (by rfl) ⟨222410, by rfl⟩ : syracuseStep 4744757 = 444821) (by norm_num)
theorem B2106965 : Blo 1248442 2106965 := bbase (se 8 (by rfl) ⟨12345, by rfl⟩ : syracuseStep 2106965 = 24691) (by norm_num)
theorem B2811509 : Blo 1248442 2811509 := bbase (se 5 (by rfl) ⟨131789, by rfl⟩ : syracuseStep 2811509 = 263579) (by norm_num)
theorem B3556997 : Blo 1248442 3556997 := bbase (se 4 (by rfl) ⟨333468, by rfl⟩ : syracuseStep 3556997 = 666937) (by norm_num)
theorem B2811581 : Blo 1248442 2811581 := bbase (se 3 (by rfl) ⟨527171, by rfl⟩ : syracuseStep 2811581 = 1054343) (by norm_num)
theorem B1689277 : Blo 1248442 1689277 := bbase (se 3 (by rfl) ⟨316739, by rfl⟩ : syracuseStep 1689277 = 633479) (by norm_num)
theorem B2107093 : Blo 1248442 2107093 := bbase (se 7 (by rfl) ⟨24692, by rfl⟩ : syracuseStep 2107093 = 49385) (by norm_num)
theorem B14436053 : Blo 1248442 14436053 := bbase (se 7 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 14436053 = 338345) (by norm_num)
theorem B1779421 : Blo 1248442 1779421 := bbase (se 3 (by rfl) ⟨333641, by rfl⟩ : syracuseStep 1779421 = 667283) (by norm_num)
theorem B1689341 : Blo 1248442 1689341 := bbase (se 3 (by rfl) ⟨316751, by rfl⟩ : syracuseStep 1689341 = 633503) (by norm_num)
theorem B2811653 : Blo 1248442 2811653 := bbase (se 4 (by rfl) ⟨263592, by rfl⟩ : syracuseStep 2811653 = 527185) (by norm_num)
theorem B2107181 : Blo 1248442 2107181 := bbase (se 3 (by rfl) ⟨395096, by rfl⟩ : syracuseStep 2107181 = 790193) (by norm_num)
theorem B2811725 : Blo 1248442 2811725 := bbase (se 3 (by rfl) ⟨527198, by rfl⟩ : syracuseStep 2811725 = 1054397) (by norm_num)
theorem B3163981 : Blo 1248442 3163981 := bbase (se 3 (by rfl) ⟨593246, by rfl⟩ : syracuseStep 3163981 = 1186493) (by norm_num)
theorem B3376997 : Blo 1248442 3376997 := bbase (se 4 (by rfl) ⟨316593, by rfl⟩ : syracuseStep 3376997 = 633187) (by norm_num)
theorem B3000197 : Blo 1248442 3000197 := bbase (se 4 (by rfl) ⟨281268, by rfl⟩ : syracuseStep 3000197 = 562537) (by norm_num)
theorem B2811797 : Blo 1248442 2811797 := bbase (se 6 (by rfl) ⟨65901, by rfl⟩ : syracuseStep 2811797 = 131803) (by norm_num)
theorem B1689509 : Blo 1248442 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B2107309 : Blo 1248442 2107309 := bbase (se 3 (by rfl) ⟨395120, by rfl⟩ : syracuseStep 2107309 = 790241) (by norm_num)
theorem B3164093 : Blo 1248442 3164093 := bbase (se 3 (by rfl) ⟨593267, by rfl⟩ : syracuseStep 3164093 = 1186535) (by norm_num)
theorem B2811869 : Blo 1248442 2811869 := bbase (se 3 (by rfl) ⟨527225, by rfl⟩ : syracuseStep 2811869 = 1054451) (by norm_num)
theorem B6326261 : Blo 1248442 6326261 := bbase (se 5 (by rfl) ⟨296543, by rfl⟩ : syracuseStep 6326261 = 593087) (by norm_num)
theorem B2107397 : Blo 1248442 2107397 := bbase (se 4 (by rfl) ⟨197568, by rfl⟩ : syracuseStep 2107397 = 395137) (by norm_num)
theorem B2811941 : Blo 1248442 2811941 := bbase (se 4 (by rfl) ⟨263619, by rfl⟩ : syracuseStep 2811941 = 527239) (by norm_num)
theorem B3557429 : Blo 1248442 3557429 := bbase (se 5 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 3557429 = 333509) (by norm_num)
theorem B2000965 : Blo 1248442 2000965 := bbase (se 4 (by rfl) ⟨187590, by rfl⟩ : syracuseStep 2000965 = 375181) (by norm_num)
theorem B2812013 : Blo 1248442 2812013 := bbase (se 3 (by rfl) ⟨527252, by rfl⟩ : syracuseStep 2812013 = 1054505) (by norm_num)
theorem B2533493 : Blo 1248442 2533493 := bbase (se 5 (by rfl) ⟨118757, by rfl⟩ : syracuseStep 2533493 = 237515) (by norm_num)
theorem B3164285 : Blo 1248442 3164285 := bbase (se 3 (by rfl) ⟨593303, by rfl⟩ : syracuseStep 3164285 = 1186607) (by norm_num)
theorem B2107525 : Blo 1248442 2107525 := bbase (se 4 (by rfl) ⟨197580, by rfl⟩ : syracuseStep 2107525 = 395161) (by norm_num)
theorem B2812085 : Blo 1248442 2812085 := bbase (se 5 (by rfl) ⟨131816, by rfl⟩ : syracuseStep 2812085 = 263633) (by norm_num)
theorem B2107613 : Blo 1248442 2107613 := bbase (se 3 (by rfl) ⟨395177, by rfl⟩ : syracuseStep 2107613 = 790355) (by norm_num)
theorem B2705653 : Blo 1248442 2705653 := bbase (se 5 (by rfl) ⟨126827, by rfl⟩ : syracuseStep 2705653 = 253655) (by norm_num)
theorem B2812157 : Blo 1248442 2812157 := bbase (se 3 (by rfl) ⟨527279, by rfl⟩ : syracuseStep 2812157 = 1054559) (by norm_num)
theorem B1780013 : Blo 1248442 1780013 := bbase (se 3 (by rfl) ⟨333752, by rfl⟩ : syracuseStep 1780013 = 667505) (by norm_num)
theorem B2812229 : Blo 1248442 2812229 := bbase (se 4 (by rfl) ⟨263646, by rfl⟩ : syracuseStep 2812229 = 527293) (by norm_num)
theorem B2107741 : Blo 1248442 2107741 := bbase (se 3 (by rfl) ⟨395201, by rfl⟩ : syracuseStep 2107741 = 790403) (by norm_num)
theorem B1780093 : Blo 1248442 1780093 := bbase (se 3 (by rfl) ⟨333767, by rfl⟩ : syracuseStep 1780093 = 667535) (by norm_num)
theorem B2812301 : Blo 1248442 2812301 := bbase (se 3 (by rfl) ⟨527306, by rfl⟩ : syracuseStep 2812301 = 1054613) (by norm_num)
theorem B2107829 : Blo 1248442 2107829 := bbase (se 5 (by rfl) ⟨98804, by rfl⟩ : syracuseStep 2107829 = 197609) (by norm_num)
theorem B2812373 : Blo 1248442 2812373 := bbase (se 7 (by rfl) ⟨32957, by rfl⟩ : syracuseStep 2812373 = 65915) (by norm_num)
theorem B3164629 : Blo 1248442 3164629 := bbase (se 7 (by rfl) ⟨37085, by rfl⟩ : syracuseStep 3164629 = 74171) (by norm_num)
theorem B1780213 : Blo 1248442 1780213 := bbase (se 5 (by rfl) ⟨83447, by rfl⟩ : syracuseStep 1780213 = 166895) (by norm_num)
theorem B2001413 : Blo 1248442 2001413 := bbase (se 4 (by rfl) ⟨187632, by rfl⟩ : syracuseStep 2001413 = 375265) (by norm_num)
theorem B2812445 : Blo 1248442 2812445 := bbase (se 3 (by rfl) ⟨527333, by rfl⟩ : syracuseStep 2812445 = 1054667) (by norm_num)
theorem B3041837 : Blo 1248442 3041837 := bbase (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) (by norm_num)
theorem B2107957 : Blo 1248442 2107957 := bbase (se 5 (by rfl) ⟨98810, by rfl⟩ : syracuseStep 2107957 = 197621) (by norm_num)
theorem B3164741 : Blo 1248442 3164741 := bbase (se 4 (by rfl) ⟨296694, by rfl⟩ : syracuseStep 3164741 = 593389) (by norm_num)
theorem B1780309 : Blo 1248442 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B2812517 : Blo 1248442 2812517 := bbase (se 4 (by rfl) ⟨263673, by rfl⟩ : syracuseStep 2812517 = 527347) (by norm_num)
theorem B2312813 : Blo 1248442 2312813 := bbase (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) (by norm_num)
theorem B2108045 : Blo 1248442 2108045 := bbase (se 3 (by rfl) ⟨395258, by rfl⟩ : syracuseStep 2108045 = 790517) (by norm_num)
theorem B2812589 : Blo 1248442 2812589 := bbase (se 3 (by rfl) ⟨527360, by rfl⟩ : syracuseStep 2812589 = 1054721) (by norm_num)
theorem B5335733 : Blo 1248442 5335733 := bbase (se 5 (by rfl) ⟨250112, by rfl⟩ : syracuseStep 5335733 = 500225) (by norm_num)
theorem B2927285 : Blo 1248442 2927285 := bbase (se 5 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 2927285 = 274433) (by norm_num)
theorem B11553461 : Blo 1248442 11553461 := bbase (se 5 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 11553461 = 1083137) (by norm_num)
theorem B5065429 : Blo 1248442 5065429 := bbase (se 7 (by rfl) ⟨59360, by rfl⟩ : syracuseStep 5065429 = 118721) (by norm_num)
theorem B2812661 : Blo 1248442 2812661 := bbase (se 5 (by rfl) ⟨131843, by rfl⟩ : syracuseStep 2812661 = 263687) (by norm_num)
theorem B3164933 : Blo 1248442 3164933 := bbase (se 4 (by rfl) ⟨296712, by rfl⟩ : syracuseStep 3164933 = 593425) (by norm_num)
theorem B2108173 : Blo 1248442 2108173 := bbase (se 3 (by rfl) ⟨395282, by rfl⟩ : syracuseStep 2108173 = 790565) (by norm_num)
theorem B3558181 : Blo 1248442 3558181 := bbase (se 4 (by rfl) ⟨333579, by rfl⟩ : syracuseStep 3558181 = 667159) (by norm_num)
theorem B2812733 : Blo 1248442 2812733 := bbase (se 3 (by rfl) ⟨527387, by rfl⟩ : syracuseStep 2812733 = 1054775) (by norm_num)
theorem B6007621 : Blo 1248442 6007621 := bbase (se 4 (by rfl) ⟨563214, by rfl⟩ : syracuseStep 6007621 = 1126429) (by norm_num)
theorem B1502021 : Blo 1248442 1502021 := bbase (se 4 (by rfl) ⟨140814, by rfl⟩ : syracuseStep 1502021 = 281629) (by norm_num)
theorem B2370397 : Blo 1248442 2370397 := bbase (se 3 (by rfl) ⟨444449, by rfl⟩ : syracuseStep 2370397 = 888899) (by norm_num)
theorem B2108261 : Blo 1248442 2108261 := bbase (se 4 (by rfl) ⟨197649, by rfl⟩ : syracuseStep 2108261 = 395299) (by norm_num)
theorem B2812805 : Blo 1248442 2812805 := bbase (se 4 (by rfl) ⟨263700, by rfl⟩ : syracuseStep 2812805 = 527401) (by norm_num)
theorem B4000661 : Blo 1248442 4000661 := bbase (se 6 (by rfl) ⟨93765, by rfl⟩ : syracuseStep 4000661 = 187531) (by norm_num)
theorem B2812877 : Blo 1248442 2812877 := bbase (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) (by norm_num)
theorem B1444825 : Blo 1248442 1444825 := bbase (se 2 (by rfl) ⟨541809, by rfl⟩ : syracuseStep 1444825 = 1083619) (by norm_num)
theorem B2108389 : Blo 1248442 2108389 := bbase (se 4 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 2108389 = 395323) (by norm_num)
theorem B2370541 : Blo 1248442 2370541 := bbase (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) (by norm_num)
theorem B4213781 : Blo 1248442 4213781 := bbase (se 6 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 4213781 = 197521) (by norm_num)
theorem B2812949 : Blo 1248442 2812949 := bbase (se 6 (by rfl) ⟨65928, by rfl⟩ : syracuseStep 2812949 = 131857) (by norm_num)
theorem B2108477 : Blo 1248442 2108477 := bbase (se 3 (by rfl) ⟨395339, by rfl⟩ : syracuseStep 2108477 = 790679) (by norm_num)
theorem B2813021 : Blo 1248442 2813021 := bbase (se 3 (by rfl) ⟨527441, by rfl⟩ : syracuseStep 2813021 = 1054883) (by norm_num)
theorem B2370701 : Blo 1248442 2370701 := bbase (se 3 (by rfl) ⟨444506, by rfl⟩ : syracuseStep 2370701 = 889013) (by norm_num)
theorem B2813093 : Blo 1248442 2813093 := bbase (se 4 (by rfl) ⟨263727, by rfl⟩ : syracuseStep 2813093 = 527455) (by norm_num)
theorem B2108605 : Blo 1248442 2108605 := bbase (se 3 (by rfl) ⟨395363, by rfl⟩ : syracuseStep 2108605 = 790727) (by norm_num)
theorem B2813165 : Blo 1248442 2813165 := bbase (se 3 (by rfl) ⟨527468, by rfl⟩ : syracuseStep 2813165 = 1054937) (by norm_num)
theorem B6327557 : Blo 1248442 6327557 := bbase (se 4 (by rfl) ⟨593208, by rfl⟩ : syracuseStep 6327557 = 1186417) (by norm_num)
theorem B2108693 : Blo 1248442 2108693 := bbase (se 6 (by rfl) ⟨49422, by rfl⟩ : syracuseStep 2108693 = 98845) (by norm_num)
theorem B2370845 : Blo 1248442 2370845 := bbase (se 3 (by rfl) ⟨444533, by rfl⟩ : syracuseStep 2370845 = 889067) (by norm_num)
theorem B3042613 : Blo 1248442 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B2813237 : Blo 1248442 2813237 := bbase (se 5 (by rfl) ⟨131870, by rfl⟩ : syracuseStep 2813237 = 263741) (by norm_num)
theorem B2813309 : Blo 1248442 2813309 := bbase (se 3 (by rfl) ⟨527495, by rfl⟩ : syracuseStep 2813309 = 1054991) (by norm_num)
theorem B2108821 : Blo 1248442 2108821 := bbase (se 6 (by rfl) ⟨49425, by rfl⟩ : syracuseStep 2108821 = 98851) (by norm_num)
theorem B4214213 : Blo 1248442 4214213 := bbase (se 4 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 4214213 = 790165) (by norm_num)
theorem B2813381 : Blo 1248442 2813381 := bbase (se 4 (by rfl) ⟨263754, by rfl⟩ : syracuseStep 2813381 = 527509) (by norm_num)
theorem B2108909 : Blo 1248442 2108909 := bbase (se 3 (by rfl) ⟨395420, by rfl⟩ : syracuseStep 2108909 = 790841) (by norm_num)
theorem B2813453 : Blo 1248442 2813453 := bbase (se 3 (by rfl) ⟨527522, by rfl⟩ : syracuseStep 2813453 = 1055045) (by norm_num)
theorem B2371133 : Blo 1248442 2371133 := bbase (se 3 (by rfl) ⟨444587, by rfl⟩ : syracuseStep 2371133 = 889175) (by norm_num)
theorem B1404517 : Blo 1248442 1404517 := bbase (se 4 (by rfl) ⟨131673, by rfl⟩ : syracuseStep 1404517 = 263347) (by norm_num)
theorem B2109037 : Blo 1248442 2109037 := bbase (se 3 (by rfl) ⟨395444, by rfl⟩ : syracuseStep 2109037 = 790889) (by norm_num)
theorem B4746869 : Blo 1248442 4746869 := bbase (se 5 (by rfl) ⟨222509, by rfl⟩ : syracuseStep 4746869 = 445019) (by norm_num)
theorem B1404553 : Blo 1248442 1404553 := bbase (se 2 (by rfl) ⟨526707, by rfl⟩ : syracuseStep 1404553 = 1053415) (by norm_num)
theorem B5336725 : Blo 1248442 5336725 := bbase (se 6 (by rfl) ⟨125079, by rfl⟩ : syracuseStep 5336725 = 250159) (by norm_num)
theorem B1404589 : Blo 1248442 1404589 := bbase (se 3 (by rfl) ⟨263360, by rfl⟩ : syracuseStep 1404589 = 526721) (by norm_num)
theorem B2109125 : Blo 1248442 2109125 := bbase (se 4 (by rfl) ⟨197730, by rfl⟩ : syracuseStep 2109125 = 395461) (by norm_num)
theorem B1404625 : Blo 1248442 1404625 := bbase (se 2 (by rfl) ⟨526734, by rfl⟩ : syracuseStep 1404625 = 1053469) (by norm_num)
theorem B2371285 : Blo 1248442 2371285 := bbase (se 7 (by rfl) ⟨27788, by rfl⟩ : syracuseStep 2371285 = 55577) (by norm_num)
theorem B1404661 : Blo 1248442 1404661 := bbase (se 5 (by rfl) ⟨65843, by rfl⟩ : syracuseStep 1404661 = 131687) (by norm_num)
theorem B1404697 : Blo 1248442 1404697 := bbase (se 2 (by rfl) ⟨526761, by rfl⟩ : syracuseStep 1404697 = 1053523) (by norm_num)
theorem B1404733 : Blo 1248442 1404733 := bbase (se 3 (by rfl) ⟨263387, by rfl⟩ : syracuseStep 1404733 = 526775) (by norm_num)
theorem B2109253 : Blo 1248442 2109253 := bbase (se 4 (by rfl) ⟨197742, by rfl⟩ : syracuseStep 2109253 = 395485) (by norm_num)
theorem B3002197 : Blo 1248442 3002197 := bbase (se 9 (by rfl) ⟨8795, by rfl⟩ : syracuseStep 3002197 = 17591) (by norm_num)
theorem B12013397 : Blo 1248442 12013397 := bbase (se 9 (by rfl) ⟨35195, by rfl⟩ : syracuseStep 12013397 = 70391) (by norm_num)
theorem B1404769 : Blo 1248442 1404769 := bbase (se 2 (by rfl) ⟨526788, by rfl⟩ : syracuseStep 1404769 = 1053577) (by norm_num)
theorem B4214645 : Blo 1248442 4214645 := bbase (se 5 (by rfl) ⟨197561, by rfl⟩ : syracuseStep 4214645 = 395123) (by norm_num)
theorem B1404805 : Blo 1248442 1404805 := bbase (se 4 (by rfl) ⟨131700, by rfl⟩ : syracuseStep 1404805 = 263401) (by norm_num)
theorem B4747157 : Blo 1248442 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B2109341 : Blo 1248442 2109341 := bbase (se 3 (by rfl) ⟨395501, by rfl⟩ : syracuseStep 2109341 = 791003) (by norm_num)
theorem B1404841 : Blo 1248442 1404841 := bbase (se 2 (by rfl) ⟨526815, by rfl⟩ : syracuseStep 1404841 = 1053631) (by norm_num)
theorem B1404877 : Blo 1248442 1404877 := bbase (se 3 (by rfl) ⟨263414, by rfl⟩ : syracuseStep 1404877 = 526829) (by norm_num)
theorem B3002341 : Blo 1248442 3002341 := bbase (se 4 (by rfl) ⟨281469, by rfl⟩ : syracuseStep 3002341 = 562939) (by norm_num)
theorem B2002925 : Blo 1248442 2002925 := bbase (se 3 (by rfl) ⟨375548, by rfl⟩ : syracuseStep 2002925 = 751097) (by norm_num)
theorem B1404913 : Blo 1248442 1404913 := bbase (se 2 (by rfl) ⟨526842, by rfl⟩ : syracuseStep 1404913 = 1053685) (by norm_num)
theorem B2371589 : Blo 1248442 2371589 := bbase (se 4 (by rfl) ⟨222336, by rfl⟩ : syracuseStep 2371589 = 444673) (by norm_num)
theorem B1404949 : Blo 1248442 1404949 := bbase (se 6 (by rfl) ⟨32928, by rfl⟩ : syracuseStep 1404949 = 65857) (by norm_num)
theorem B2109469 : Blo 1248442 2109469 := bbase (se 3 (by rfl) ⟨395525, by rfl⟩ : syracuseStep 2109469 = 791051) (by norm_num)
theorem B1404985 : Blo 1248442 1404985 := bbase (se 2 (by rfl) ⟨526869, by rfl⟩ : syracuseStep 1404985 = 1053739) (by norm_num)
theorem B1405021 : Blo 1248442 1405021 := bbase (se 3 (by rfl) ⟨263441, by rfl⟩ : syracuseStep 1405021 = 526883) (by norm_num)
theorem B2109557 : Blo 1248442 2109557 := bbase (se 5 (by rfl) ⟨98885, by rfl⟩ : syracuseStep 2109557 = 197771) (by norm_num)
theorem B1405057 : Blo 1248442 1405057 := bbase (se 2 (by rfl) ⟨526896, by rfl⟩ : syracuseStep 1405057 = 1053793) (by norm_num)
theorem B1405093 : Blo 1248442 1405093 := bbase (se 4 (by rfl) ⟨131727, by rfl⟩ : syracuseStep 1405093 = 263455) (by norm_num)
theorem B1405129 : Blo 1248442 1405129 := bbase (se 2 (by rfl) ⟨526923, by rfl⟩ : syracuseStep 1405129 = 1053847) (by norm_num)
theorem B4002005 : Blo 1248442 4002005 := bbase (se 7 (by rfl) ⟨46898, by rfl⟩ : syracuseStep 4002005 = 93797) (by norm_num)
theorem B1405165 : Blo 1248442 1405165 := bbase (se 3 (by rfl) ⟨263468, by rfl⟩ : syracuseStep 1405165 = 526937) (by norm_num)
theorem B12824821 : Blo 1248442 12824821 := bbase (se 5 (by rfl) ⟨601163, by rfl⟩ : syracuseStep 12824821 = 1202327) (by norm_num)
theorem B2109685 : Blo 1248442 2109685 := bbase (se 5 (by rfl) ⟨98891, by rfl⟩ : syracuseStep 2109685 = 197783) (by norm_num)
theorem B1405201 : Blo 1248442 1405201 := bbase (se 2 (by rfl) ⟨526950, by rfl⟩ : syracuseStep 1405201 = 1053901) (by norm_num)
theorem B2666773 : Blo 1248442 2666773 := bbase (se 6 (by rfl) ⟨62502, by rfl⟩ : syracuseStep 2666773 = 125005) (by norm_num)
theorem B4215077 : Blo 1248442 4215077 := bbase (se 4 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 4215077 = 790327) (by norm_num)
theorem B1405237 : Blo 1248442 1405237 := bbase (se 5 (by rfl) ⟨65870, by rfl⟩ : syracuseStep 1405237 = 131741) (by norm_num)
theorem B1265977 : Blo 1248442 1265977 := bbase (se 2 (by rfl) ⟨474741, by rfl⟩ : syracuseStep 1265977 = 949483) (by norm_num)
theorem B2109773 : Blo 1248442 2109773 := bbase (se 3 (by rfl) ⟨395582, by rfl⟩ : syracuseStep 2109773 = 791165) (by norm_num)
theorem B1405273 : Blo 1248442 1405273 := bbase (se 2 (by rfl) ⟨526977, by rfl⟩ : syracuseStep 1405273 = 1053955) (by norm_num)
theorem B1405309 : Blo 1248442 1405309 := bbase (se 3 (by rfl) ⟨263495, by rfl⟩ : syracuseStep 1405309 = 526991) (by norm_num)
theorem B1266049 : Blo 1248442 1266049 := bbase (se 2 (by rfl) ⟨474768, by rfl⟩ : syracuseStep 1266049 = 949537) (by norm_num)
theorem B1405345 : Blo 1248442 1405345 := bbase (se 2 (by rfl) ⟨527004, by rfl⟩ : syracuseStep 1405345 = 1054009) (by norm_num)
theorem B1405381 : Blo 1248442 1405381 := bbase (se 4 (by rfl) ⟨131754, by rfl⟩ : syracuseStep 1405381 = 263509) (by norm_num)
theorem B2109901 : Blo 1248442 2109901 := bbase (se 3 (by rfl) ⟨395606, by rfl⟩ : syracuseStep 2109901 = 791213) (by norm_num)
theorem B1405417 : Blo 1248442 1405417 := bbase (se 2 (by rfl) ⟨527031, by rfl⟩ : syracuseStep 1405417 = 1054063) (by norm_num)
theorem B1405453 : Blo 1248442 1405453 := bbase (se 3 (by rfl) ⟨263522, by rfl⟩ : syracuseStep 1405453 = 527045) (by norm_num)
theorem B6328853 : Blo 1248442 6328853 := bbase (se 6 (by rfl) ⟨148332, by rfl⟩ : syracuseStep 6328853 = 296665) (by norm_num)
theorem B2109989 : Blo 1248442 2109989 := bbase (se 4 (by rfl) ⟨197811, by rfl⟩ : syracuseStep 2109989 = 395623) (by norm_num)
theorem B1405489 : Blo 1248442 1405489 := bbase (se 2 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 1405489 = 1054117) (by norm_num)
theorem B3379765 : Blo 1248442 3379765 := bbase (se 5 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 3379765 = 316853) (by norm_num)
theorem B3002957 : Blo 1248442 3002957 := bbase (se 3 (by rfl) ⟨563054, by rfl⟩ : syracuseStep 3002957 = 1126109) (by norm_num)
theorem B1405525 : Blo 1248442 1405525 := bbase (se 8 (by rfl) ⟨8235, by rfl⟩ : syracuseStep 1405525 = 16471) (by norm_num)
theorem B1405561 : Blo 1248442 1405561 := bbase (se 2 (by rfl) ⟨527085, by rfl⟩ : syracuseStep 1405561 = 1054171) (by norm_num)
theorem B9491093 : Blo 1248442 9491093 := bbase (se 6 (by rfl) ⟨222447, by rfl⟩ : syracuseStep 9491093 = 444895) (by norm_num)
theorem B1405597 : Blo 1248442 1405597 := bbase (se 3 (by rfl) ⟨263549, by rfl⟩ : syracuseStep 1405597 = 527099) (by norm_num)
theorem B6410917 : Blo 1248442 6410917 := bbase (se 4 (by rfl) ⟨601023, by rfl⟩ : syracuseStep 6410917 = 1202047) (by norm_num)
theorem B2110117 : Blo 1248442 2110117 := bbase (se 4 (by rfl) ⟨197823, by rfl⟩ : syracuseStep 2110117 = 395647) (by norm_num)
theorem B1405633 : Blo 1248442 1405633 := bbase (se 2 (by rfl) ⟨527112, by rfl⟩ : syracuseStep 1405633 = 1054225) (by norm_num)
theorem B4215509 : Blo 1248442 4215509 := bbase (se 7 (by rfl) ⟨49400, by rfl⟩ : syracuseStep 4215509 = 98801) (by norm_num)
theorem B1405669 : Blo 1248442 1405669 := bbase (se 4 (by rfl) ⟨131781, by rfl⟩ : syracuseStep 1405669 = 263563) (by norm_num)
theorem B3420917 : Blo 1248442 3420917 := bbase (se 5 (by rfl) ⟨160355, by rfl⟩ : syracuseStep 3420917 = 320711) (by norm_num)
theorem B2372341 : Blo 1248442 2372341 := bbase (se 5 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 2372341 = 222407) (by norm_num)
theorem B2667269 : Blo 1248442 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B1405705 : Blo 1248442 1405705 := bbase (se 2 (by rfl) ⟨527139, by rfl⟩ : syracuseStep 1405705 = 1054279) (by norm_num)
theorem B1872677 : Blo 1248442 1872677 := bbase (se 4 (by rfl) ⟨175563, by rfl⟩ : syracuseStep 1872677 = 351127) (by norm_num)
theorem B1405741 : Blo 1248442 1405741 := bbase (se 3 (by rfl) ⟨263576, by rfl⟩ : syracuseStep 1405741 = 527153) (by norm_num)
theorem B1872701 : Blo 1248442 1872701 := bbase (se 3 (by rfl) ⟨351131, by rfl⟩ : syracuseStep 1872701 = 702263) (by norm_num)
theorem B1405777 : Blo 1248442 1405777 := bbase (se 2 (by rfl) ⟨527166, by rfl⟩ : syracuseStep 1405777 = 1054333) (by norm_num)
theorem B1872725 : Blo 1248442 1872725 := bbase (se 9 (by rfl) ⟨5486, by rfl⟩ : syracuseStep 1872725 = 10973) (by norm_num)
theorem B14234453 : Blo 1248442 14234453 := bbase (se 9 (by rfl) ⟨41702, by rfl⟩ : syracuseStep 14234453 = 83405) (by norm_num)
theorem B1872749 : Blo 1248442 1872749 := bbase (se 3 (by rfl) ⟨351140, by rfl⟩ : syracuseStep 1872749 = 702281) (by norm_num)
theorem B1405813 : Blo 1248442 1405813 := bbase (se 5 (by rfl) ⟨65897, by rfl⟩ : syracuseStep 1405813 = 131795) (by norm_num)
theorem B1872773 : Blo 1248442 1872773 := bbase (se 4 (by rfl) ⟨175572, by rfl⟩ : syracuseStep 1872773 = 351145) (by norm_num)
theorem B2372485 : Blo 1248442 2372485 := bbase (se 4 (by rfl) ⟨222420, by rfl⟩ : syracuseStep 2372485 = 444841) (by norm_num)
theorem B1405849 : Blo 1248442 1405849 := bbase (se 2 (by rfl) ⟨527193, by rfl⟩ : syracuseStep 1405849 = 1054387) (by norm_num)
theorem B1872797 : Blo 1248442 1872797 := bbase (se 3 (by rfl) ⟨351149, by rfl⟩ : syracuseStep 1872797 = 702299) (by norm_num)
theorem B3003293 : Blo 1248442 3003293 := bbase (se 3 (by rfl) ⟨563117, by rfl⟩ : syracuseStep 3003293 = 1126235) (by norm_num)
theorem B1872821 : Blo 1248442 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B6321077 : Blo 1248442 6321077 := bbase (se 5 (by rfl) ⟨296300, by rfl⟩ : syracuseStep 6321077 = 592601) (by norm_num)
theorem B1405885 : Blo 1248442 1405885 := bbase (se 3 (by rfl) ⟨263603, by rfl⟩ : syracuseStep 1405885 = 527207) (by norm_num)
theorem B1872845 : Blo 1248442 1872845 := bbase (se 3 (by rfl) ⟨351158, by rfl⟩ : syracuseStep 1872845 = 702317) (by norm_num)
theorem B1602509 : Blo 1248442 1602509 := bbase (se 3 (by rfl) ⟨300470, by rfl⟩ : syracuseStep 1602509 = 600941) (by norm_num)
theorem B1405921 : Blo 1248442 1405921 := bbase (se 2 (by rfl) ⟨527220, by rfl⟩ : syracuseStep 1405921 = 1054441) (by norm_num)
theorem B1872869 : Blo 1248442 1872869 := bbase (se 4 (by rfl) ⟨175581, by rfl⟩ : syracuseStep 1872869 = 351163) (by norm_num)
theorem B1872893 : Blo 1248442 1872893 := bbase (se 3 (by rfl) ⟨351167, by rfl⟩ : syracuseStep 1872893 = 702335) (by norm_num)
theorem B3003389 : Blo 1248442 3003389 := bbase (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) (by norm_num)
theorem B1405957 : Blo 1248442 1405957 := bbase (se 4 (by rfl) ⟨131808, by rfl⟩ : syracuseStep 1405957 = 263617) (by norm_num)
theorem B1872917 : Blo 1248442 1872917 := bbase (se 6 (by rfl) ⟨43896, by rfl⟩ : syracuseStep 1872917 = 87793) (by norm_num)
theorem B2372645 : Blo 1248442 2372645 := bbase (se 4 (by rfl) ⟨222435, by rfl⟩ : syracuseStep 2372645 = 444871) (by norm_num)
theorem B1405993 : Blo 1248442 1405993 := bbase (se 2 (by rfl) ⟨527247, by rfl⟩ : syracuseStep 1405993 = 1054495) (by norm_num)
theorem B1872941 : Blo 1248442 1872941 := bbase (se 3 (by rfl) ⟨351176, by rfl⟩ : syracuseStep 1872941 = 702353) (by norm_num)
theorem B9483317 : Blo 1248442 9483317 := bbase (se 5 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 9483317 = 889061) (by norm_num)
theorem B1872965 : Blo 1248442 1872965 := bbase (se 4 (by rfl) ⟨175590, by rfl⟩ : syracuseStep 1872965 = 351181) (by norm_num)
theorem B1406029 : Blo 1248442 1406029 := bbase (se 3 (by rfl) ⟨263630, by rfl⟩ : syracuseStep 1406029 = 527261) (by norm_num)
theorem B1872989 : Blo 1248442 1872989 := bbase (se 3 (by rfl) ⟨351185, by rfl⟩ : syracuseStep 1872989 = 702371) (by norm_num)
theorem B1520741 : Blo 1248442 1520741 := bbase (se 4 (by rfl) ⟨142569, by rfl⟩ : syracuseStep 1520741 = 285139) (by norm_num)
theorem B1406065 : Blo 1248442 1406065 := bbase (se 2 (by rfl) ⟨527274, by rfl⟩ : syracuseStep 1406065 = 1054549) (by norm_num)
theorem B1873013 : Blo 1248442 1873013 := bbase (se 5 (by rfl) ⟨87797, by rfl⟩ : syracuseStep 1873013 = 175595) (by norm_num)
theorem B5067893 : Blo 1248442 5067893 := bbase (se 5 (by rfl) ⟨237557, by rfl⟩ : syracuseStep 5067893 = 475115) (by norm_num)
theorem B4215941 : Blo 1248442 4215941 := bbase (se 4 (by rfl) ⟨395244, by rfl⟩ : syracuseStep 4215941 = 790489) (by norm_num)
theorem B1873037 : Blo 1248442 1873037 := bbase (se 3 (by rfl) ⟨351194, by rfl⟩ : syracuseStep 1873037 = 702389) (by norm_num)
theorem B1406101 : Blo 1248442 1406101 := bbase (se 6 (by rfl) ⟨32955, by rfl⟩ : syracuseStep 1406101 = 65911) (by norm_num)
theorem B1873061 : Blo 1248442 1873061 := bbase (se 4 (by rfl) ⟨175599, by rfl⟩ : syracuseStep 1873061 = 351199) (by norm_num)
theorem B2372789 : Blo 1248442 2372789 := bbase (se 5 (by rfl) ⟨111224, by rfl⟩ : syracuseStep 2372789 = 222449) (by norm_num)
theorem B1406137 : Blo 1248442 1406137 := bbase (se 2 (by rfl) ⟨527301, by rfl⟩ : syracuseStep 1406137 = 1054603) (by norm_num)
theorem B1873085 : Blo 1248442 1873085 := bbase (se 3 (by rfl) ⟨351203, by rfl⟩ : syracuseStep 1873085 = 702407) (by norm_num)
theorem B1266877 : Blo 1248442 1266877 := bbase (se 3 (by rfl) ⟨237539, by rfl⟩ : syracuseStep 1266877 = 475079) (by norm_num)
theorem B3003581 : Blo 1248442 3003581 := bbase (se 3 (by rfl) ⟨563171, by rfl⟩ : syracuseStep 3003581 = 1126343) (by norm_num)
theorem B1873109 : Blo 1248442 1873109 := bbase (se 7 (by rfl) ⟨21950, by rfl⟩ : syracuseStep 1873109 = 43901) (by norm_num)
theorem B1406173 : Blo 1248442 1406173 := bbase (se 3 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 1406173 = 527315) (by norm_num)
theorem B1873133 : Blo 1248442 1873133 := bbase (se 3 (by rfl) ⟨351212, by rfl⟩ : syracuseStep 1873133 = 702425) (by norm_num)
theorem B1406209 : Blo 1248442 1406209 := bbase (se 2 (by rfl) ⟨527328, by rfl⟩ : syracuseStep 1406209 = 1054657) (by norm_num)
theorem B1873157 : Blo 1248442 1873157 := bbase (se 4 (by rfl) ⟨175608, by rfl⟩ : syracuseStep 1873157 = 351217) (by norm_num)
theorem B1873181 : Blo 1248442 1873181 := bbase (se 3 (by rfl) ⟨351221, by rfl⟩ : syracuseStep 1873181 = 702443) (by norm_num)
theorem B1406245 : Blo 1248442 1406245 := bbase (se 4 (by rfl) ⟨131835, by rfl⟩ : syracuseStep 1406245 = 263671) (by norm_num)
theorem B1873205 : Blo 1248442 1873205 := bbase (se 5 (by rfl) ⟨87806, by rfl⟩ : syracuseStep 1873205 = 175613) (by norm_num)
theorem B1406281 : Blo 1248442 1406281 := bbase (se 2 (by rfl) ⟨527355, by rfl⟩ : syracuseStep 1406281 = 1054711) (by norm_num)
theorem B1873229 : Blo 1248442 1873229 := bbase (se 3 (by rfl) ⟨351230, by rfl⟩ : syracuseStep 1873229 = 702461) (by norm_num)
theorem B1873253 : Blo 1248442 1873253 := bbase (se 4 (by rfl) ⟨175617, by rfl⟩ : syracuseStep 1873253 = 351235) (by norm_num)
theorem B1406317 : Blo 1248442 1406317 := bbase (se 3 (by rfl) ⟨263684, by rfl⟩ : syracuseStep 1406317 = 527369) (by norm_num)
theorem B1873277 : Blo 1248442 1873277 := bbase (se 3 (by rfl) ⟨351239, by rfl⟩ : syracuseStep 1873277 = 702479) (by norm_num)
theorem B1406353 : Blo 1248442 1406353 := bbase (se 2 (by rfl) ⟨527382, by rfl⟩ : syracuseStep 1406353 = 1054765) (by norm_num)
theorem B1873301 : Blo 1248442 1873301 := bbase (se 6 (by rfl) ⟨43905, by rfl⟩ : syracuseStep 1873301 = 87811) (by norm_num)
theorem B1873325 : Blo 1248442 1873325 := bbase (se 3 (by rfl) ⟨351248, by rfl⟩ : syracuseStep 1873325 = 702497) (by norm_num)
theorem B1406389 : Blo 1248442 1406389 := bbase (se 5 (by rfl) ⟨65924, by rfl⟩ : syracuseStep 1406389 = 131849) (by norm_num)
theorem B1873349 : Blo 1248442 1873349 := bbase (se 4 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 1873349 = 351253) (by norm_num)
theorem B2135501 : Blo 1248442 2135501 := bbase (se 3 (by rfl) ⟨400406, by rfl⟩ : syracuseStep 2135501 = 800813) (by norm_num)
theorem B4740565 : Blo 1248442 4740565 := bbase (se 7 (by rfl) ⟨55553, by rfl⟩ : syracuseStep 4740565 = 111107) (by norm_num)
theorem B2373077 : Blo 1248442 2373077 := bbase (se 7 (by rfl) ⟨27809, by rfl⟩ : syracuseStep 2373077 = 55619) (by norm_num)
theorem B1406425 : Blo 1248442 1406425 := bbase (se 2 (by rfl) ⟨527409, by rfl⟩ : syracuseStep 1406425 = 1054819) (by norm_num)
theorem B1873373 : Blo 1248442 1873373 := bbase (se 3 (by rfl) ⟨351257, by rfl⟩ : syracuseStep 1873373 = 702515) (by norm_num)
theorem B1873397 : Blo 1248442 1873397 := bbase (se 5 (by rfl) ⟨87815, by rfl⟩ : syracuseStep 1873397 = 175631) (by norm_num)
theorem B1406461 : Blo 1248442 1406461 := bbase (se 3 (by rfl) ⟨263711, by rfl⟩ : syracuseStep 1406461 = 527423) (by norm_num)
theorem B1873421 : Blo 1248442 1873421 := bbase (se 3 (by rfl) ⟨351266, by rfl⟩ : syracuseStep 1873421 = 702533) (by norm_num)
theorem B1406497 : Blo 1248442 1406497 := bbase (se 2 (by rfl) ⟨527436, by rfl⟩ : syracuseStep 1406497 = 1054873) (by norm_num)
theorem B1873445 : Blo 1248442 1873445 := bbase (se 4 (by rfl) ⟨175635, by rfl⟩ : syracuseStep 1873445 = 351271) (by norm_num)
theorem B4216373 : Blo 1248442 4216373 := bbase (se 5 (by rfl) ⟨197642, by rfl⟩ : syracuseStep 4216373 = 395285) (by norm_num)
theorem B1873469 : Blo 1248442 1873469 := bbase (se 3 (by rfl) ⟨351275, by rfl⟩ : syracuseStep 1873469 = 702551) (by norm_num)
theorem B1406533 : Blo 1248442 1406533 := bbase (se 4 (by rfl) ⟨131862, by rfl⟩ : syracuseStep 1406533 = 263725) (by norm_num)
theorem B1873493 : Blo 1248442 1873493 := bbase (se 8 (by rfl) ⟨10977, by rfl⟩ : syracuseStep 1873493 = 21955) (by norm_num)
theorem B5781077 : Blo 1248442 5781077 := bbase (se 8 (by rfl) ⟨33873, by rfl⟩ : syracuseStep 5781077 = 67747) (by norm_num)
theorem B2668133 : Blo 1248442 2668133 := bbase (se 4 (by rfl) ⟨250137, by rfl⟩ : syracuseStep 2668133 = 500275) (by norm_num)
theorem B1406569 : Blo 1248442 1406569 := bbase (se 2 (by rfl) ⟨527463, by rfl⟩ : syracuseStep 1406569 = 1054927) (by norm_num)
theorem B1873517 : Blo 1248442 1873517 := bbase (se 3 (by rfl) ⟨351284, by rfl⟩ : syracuseStep 1873517 = 702569) (by norm_num)
theorem B2373229 : Blo 1248442 2373229 := bbase (se 3 (by rfl) ⟨444980, by rfl⟩ : syracuseStep 2373229 = 889961) (by norm_num)
theorem B1873541 : Blo 1248442 1873541 := bbase (se 4 (by rfl) ⟨175644, by rfl⟩ : syracuseStep 1873541 = 351289) (by norm_num)
theorem B2135693 : Blo 1248442 2135693 := bbase (se 3 (by rfl) ⟨400442, by rfl⟩ : syracuseStep 2135693 = 800885) (by norm_num)
theorem B1406605 : Blo 1248442 1406605 := bbase (se 3 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 1406605 = 527477) (by norm_num)
theorem B1873565 : Blo 1248442 1873565 := bbase (se 3 (by rfl) ⟨351293, by rfl⟩ : syracuseStep 1873565 = 702587) (by norm_num)
theorem B1406641 : Blo 1248442 1406641 := bbase (se 2 (by rfl) ⟨527490, by rfl⟩ : syracuseStep 1406641 = 1054981) (by norm_num)
theorem B1873589 : Blo 1248442 1873589 := bbase (se 5 (by rfl) ⟨87824, by rfl⟩ : syracuseStep 1873589 = 175649) (by norm_num)
theorem B1873613 : Blo 1248442 1873613 := bbase (se 3 (by rfl) ⟨351302, by rfl⟩ : syracuseStep 1873613 = 702605) (by norm_num)
theorem B1406677 : Blo 1248442 1406677 := bbase (se 7 (by rfl) ⟨16484, by rfl⟩ : syracuseStep 1406677 = 32969) (by norm_num)
theorem B1873637 : Blo 1248442 1873637 := bbase (se 4 (by rfl) ⟨175653, by rfl⟩ : syracuseStep 1873637 = 351307) (by norm_num)
theorem B1603309 : Blo 1248442 1603309 := bbase (se 3 (by rfl) ⟨300620, by rfl⟩ : syracuseStep 1603309 = 601241) (by norm_num)
theorem B2668277 : Blo 1248442 2668277 := bbase (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) (by norm_num)
theorem B1406713 : Blo 1248442 1406713 := bbase (se 2 (by rfl) ⟨527517, by rfl⟩ : syracuseStep 1406713 = 1055035) (by norm_num)
theorem B1873661 : Blo 1248442 1873661 := bbase (se 3 (by rfl) ⟨351311, by rfl⟩ : syracuseStep 1873661 = 702623) (by norm_num)
theorem B4740869 : Blo 1248442 4740869 := bbase (se 4 (by rfl) ⟨444456, by rfl⟩ : syracuseStep 4740869 = 888913) (by norm_num)
theorem B1873685 : Blo 1248442 1873685 := bbase (se 6 (by rfl) ⟨43914, by rfl⟩ : syracuseStep 1873685 = 87829) (by norm_num)
theorem B6330149 : Blo 1248442 6330149 := bbase (se 4 (by rfl) ⟨593451, by rfl⟩ : syracuseStep 6330149 = 1186903) (by norm_num)
theorem B1873709 : Blo 1248442 1873709 := bbase (se 3 (by rfl) ⟨351320, by rfl⟩ : syracuseStep 1873709 = 702641) (by norm_num)
theorem B1873733 : Blo 1248442 1873733 := bbase (se 4 (by rfl) ⟨175662, by rfl⟩ : syracuseStep 1873733 = 351325) (by norm_num)
theorem B5699413 : Blo 1248442 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B1873757 : Blo 1248442 1873757 := bbase (se 3 (by rfl) ⟨351329, by rfl⟩ : syracuseStep 1873757 = 702659) (by norm_num)
theorem B1873781 : Blo 1248442 1873781 := bbase (se 5 (by rfl) ⟨87833, by rfl⟩ : syracuseStep 1873781 = 175667) (by norm_num)
theorem B9000821 : Blo 1248442 9000821 := bbase (se 5 (by rfl) ⟨421913, by rfl⟩ : syracuseStep 9000821 = 843827) (by norm_num)
theorem B1873805 : Blo 1248442 1873805 := bbase (se 3 (by rfl) ⟨351338, by rfl⟩ : syracuseStep 1873805 = 702677) (by norm_num)
theorem B2373533 : Blo 1248442 2373533 := bbase (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) (by norm_num)
theorem B1873829 : Blo 1248442 1873829 := bbase (se 4 (by rfl) ⟨175671, by rfl⟩ : syracuseStep 1873829 = 351343) (by norm_num)
theorem B1873853 : Blo 1248442 1873853 := bbase (se 3 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 1873853 = 702695) (by norm_num)
theorem B1873877 : Blo 1248442 1873877 := bbase (se 7 (by rfl) ⟨21959, by rfl⟩ : syracuseStep 1873877 = 43919) (by norm_num)
theorem B4216805 : Blo 1248442 4216805 := bbase (se 4 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 4216805 = 790651) (by norm_num)
theorem B1873901 : Blo 1248442 1873901 := bbase (se 3 (by rfl) ⟨351356, by rfl⟩ : syracuseStep 1873901 = 702713) (by norm_num)
theorem B1873925 : Blo 1248442 1873925 := bbase (se 4 (by rfl) ⟨175680, by rfl⟩ : syracuseStep 1873925 = 351361) (by norm_num)
theorem B1873949 : Blo 1248442 1873949 := bbase (se 3 (by rfl) ⟨351365, by rfl⟩ : syracuseStep 1873949 = 702731) (by norm_num)
theorem B1873973 : Blo 1248442 1873973 := bbase (se 5 (by rfl) ⟨87842, by rfl⟩ : syracuseStep 1873973 = 175685) (by norm_num)
theorem B1873997 : Blo 1248442 1873997 := bbase (se 3 (by rfl) ⟨351374, by rfl⟩ : syracuseStep 1873997 = 702749) (by norm_num)
theorem B1874021 : Blo 1248442 1874021 := bbase (se 4 (by rfl) ⟨175689, by rfl⟩ : syracuseStep 1874021 = 351379) (by norm_num)
theorem B1874045 : Blo 1248442 1874045 := bbase (se 3 (by rfl) ⟨351383, by rfl⟩ : syracuseStep 1874045 = 702767) (by norm_num)
theorem B3160205 : Blo 1248442 3160205 := bbase (se 3 (by rfl) ⟨592538, by rfl⟩ : syracuseStep 3160205 = 1185077) (by norm_num)
theorem B1874069 : Blo 1248442 1874069 := bbase (se 6 (by rfl) ⟨43923, by rfl⟩ : syracuseStep 1874069 = 87847) (by norm_num)
theorem B4004005 : Blo 1248442 4004005 := bbase (se 4 (by rfl) ⟨375375, by rfl⟩ : syracuseStep 4004005 = 750751) (by norm_num)
theorem B1333417 : Blo 1248442 1333417 := bbase (se 2 (by rfl) ⟨500031, by rfl⟩ : syracuseStep 1333417 = 1000063) (by norm_num)
theorem B1874093 : Blo 1248442 1874093 := bbase (se 3 (by rfl) ⟨351392, by rfl⟩ : syracuseStep 1874093 = 702785) (by norm_num)
theorem B6322373 : Blo 1248442 6322373 := bbase (se 4 (by rfl) ⟨592722, by rfl⟩ : syracuseStep 6322373 = 1185445) (by norm_num)
theorem B1874117 : Blo 1248442 1874117 := bbase (se 4 (by rfl) ⟨175698, by rfl⟩ : syracuseStep 1874117 = 351397) (by norm_num)
theorem B1874141 : Blo 1248442 1874141 := bbase (se 3 (by rfl) ⟨351401, by rfl⟩ : syracuseStep 1874141 = 702803) (by norm_num)
theorem B1874165 : Blo 1248442 1874165 := bbase (se 5 (by rfl) ⟨87851, by rfl⟩ : syracuseStep 1874165 = 175703) (by norm_num)
theorem B1874189 : Blo 1248442 1874189 := bbase (se 3 (by rfl) ⟨351410, by rfl⟩ : syracuseStep 1874189 = 702821) (by norm_num)
theorem B1874213 : Blo 1248442 1874213 := bbase (se 4 (by rfl) ⟨175707, by rfl⟩ : syracuseStep 1874213 = 351415) (by norm_num)
theorem B1874237 : Blo 1248442 1874237 := bbase (se 3 (by rfl) ⟨351419, by rfl⟩ : syracuseStep 1874237 = 702839) (by norm_num)
theorem B3160397 : Blo 1248442 3160397 := bbase (se 3 (by rfl) ⟨592574, by rfl⟩ : syracuseStep 3160397 = 1185149) (by norm_num)
theorem B1874261 : Blo 1248442 1874261 := bbase (se 10 (by rfl) ⟨2745, by rfl⟩ : syracuseStep 1874261 = 5491) (by norm_num)
theorem B1874285 : Blo 1248442 1874285 := bbase (se 3 (by rfl) ⟨351428, by rfl⟩ : syracuseStep 1874285 = 702857) (by norm_num)
theorem B1874309 : Blo 1248442 1874309 := bbase (se 4 (by rfl) ⟨175716, by rfl⟩ : syracuseStep 1874309 = 351433) (by norm_num)
theorem B4217237 : Blo 1248442 4217237 := bbase (se 6 (by rfl) ⟨98841, by rfl⟩ : syracuseStep 4217237 = 197683) (by norm_num)
theorem B1874333 : Blo 1248442 1874333 := bbase (se 3 (by rfl) ⟨351437, by rfl⟩ : syracuseStep 1874333 = 702875) (by norm_num)
theorem B2136485 : Blo 1248442 2136485 := bbase (se 4 (by rfl) ⟨200295, by rfl⟩ : syracuseStep 2136485 = 400591) (by norm_num)
theorem B10131893 : Blo 1248442 10131893 := bbase (se 5 (by rfl) ⟨474932, by rfl⟩ : syracuseStep 10131893 = 949865) (by norm_num)
theorem B1874357 : Blo 1248442 1874357 := bbase (se 5 (by rfl) ⟨87860, by rfl⟩ : syracuseStep 1874357 = 175721) (by norm_num)
theorem B1423813 : Blo 1248442 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B1874381 : Blo 1248442 1874381 := bbase (se 3 (by rfl) ⟨351446, by rfl⟩ : syracuseStep 1874381 = 702893) (by norm_num)
theorem B2669021 : Blo 1248442 2669021 := bbase (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) (by norm_num)
theorem B1874405 : Blo 1248442 1874405 := bbase (se 4 (by rfl) ⟨175725, by rfl⟩ : syracuseStep 1874405 = 351451) (by norm_num)
theorem B1874429 : Blo 1248442 1874429 := bbase (se 3 (by rfl) ⟨351455, by rfl⟩ : syracuseStep 1874429 = 702911) (by norm_num)
theorem B1874453 : Blo 1248442 1874453 := bbase (se 6 (by rfl) ⟨43932, by rfl⟩ : syracuseStep 1874453 = 87865) (by norm_num)
theorem B1604125 : Blo 1248442 1604125 := bbase (se 3 (by rfl) ⟨300773, by rfl⟩ : syracuseStep 1604125 = 601547) (by norm_num)
theorem B1333793 : Blo 1248442 1333793 := bbase (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) (by norm_num)
theorem B1874477 : Blo 1248442 1874477 := bbase (se 3 (by rfl) ⟨351464, by rfl⟩ : syracuseStep 1874477 = 702929) (by norm_num)
theorem B1874501 : Blo 1248442 1874501 := bbase (se 4 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 1874501 = 351469) (by norm_num)
theorem B1874525 : Blo 1248442 1874525 := bbase (se 3 (by rfl) ⟨351473, by rfl⟩ : syracuseStep 1874525 = 702947) (by norm_num)
theorem B1333865 : Blo 1248442 1333865 := bbase (se 2 (by rfl) ⟨500199, by rfl⟩ : syracuseStep 1333865 = 1000399) (by norm_num)
theorem B8002165 : Blo 1248442 8002165 := bbase (se 5 (by rfl) ⟨375101, by rfl⟩ : syracuseStep 8002165 = 750203) (by norm_num)
theorem B1874549 : Blo 1248442 1874549 := bbase (se 5 (by rfl) ⟨87869, by rfl⟩ : syracuseStep 1874549 = 175739) (by norm_num)
theorem B1874573 : Blo 1248442 1874573 := bbase (se 3 (by rfl) ⟨351482, by rfl⟩ : syracuseStep 1874573 = 702965) (by norm_num)
theorem B2054813 : Blo 1248442 2054813 := bbase (se 3 (by rfl) ⟨385277, by rfl⟩ : syracuseStep 2054813 = 770555) (by norm_num)
theorem B3160741 : Blo 1248442 3160741 := bbase (se 4 (by rfl) ⟨296319, by rfl⟩ : syracuseStep 3160741 = 592639) (by norm_num)
theorem B1874597 : Blo 1248442 1874597 := bbase (se 4 (by rfl) ⟨175743, by rfl⟩ : syracuseStep 1874597 = 351487) (by norm_num)
theorem B1874621 : Blo 1248442 1874621 := bbase (se 3 (by rfl) ⟨351491, by rfl⟩ : syracuseStep 1874621 = 702983) (by norm_num)
theorem B1268437 : Blo 1248442 1268437 := bbase (se 7 (by rfl) ⟨14864, by rfl⟩ : syracuseStep 1268437 = 29729) (by norm_num)
theorem B1874645 : Blo 1248442 1874645 := bbase (se 7 (by rfl) ⟨21968, by rfl⟩ : syracuseStep 1874645 = 43937) (by norm_num)
theorem B1874669 : Blo 1248442 1874669 := bbase (se 3 (by rfl) ⟨351500, by rfl⟩ : syracuseStep 1874669 = 703001) (by norm_num)
theorem B1874693 : Blo 1248442 1874693 := bbase (se 4 (by rfl) ⟨175752, by rfl⟩ : syracuseStep 1874693 = 351505) (by norm_num)
theorem B3160853 : Blo 1248442 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B1874717 : Blo 1248442 1874717 := bbase (se 3 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 1874717 = 703019) (by norm_num)
theorem B1334053 : Blo 1248442 1334053 := bbase (se 4 (by rfl) ⟨125067, by rfl⟩ : syracuseStep 1334053 = 250135) (by norm_num)
theorem B1424177 : Blo 1248442 1424177 := bbase (se 2 (by rfl) ⟨534066, by rfl⟩ : syracuseStep 1424177 = 1068133) (by norm_num)
theorem B1874741 : Blo 1248442 1874741 := bbase (se 5 (by rfl) ⟨87878, by rfl⟩ : syracuseStep 1874741 = 175757) (by norm_num)
theorem B4217669 : Blo 1248442 4217669 := bbase (se 4 (by rfl) ⟨395406, by rfl⟩ : syracuseStep 4217669 = 790813) (by norm_num)
theorem B1874765 : Blo 1248442 1874765 := bbase (se 3 (by rfl) ⟨351518, by rfl⟩ : syracuseStep 1874765 = 703037) (by norm_num)
theorem B1874789 : Blo 1248442 1874789 := bbase (se 4 (by rfl) ⟨175761, by rfl⟩ : syracuseStep 1874789 = 351523) (by norm_num)
theorem B1874813 : Blo 1248442 1874813 := bbase (se 3 (by rfl) ⟨351527, by rfl⟩ : syracuseStep 1874813 = 703055) (by norm_num)
theorem B1424269 : Blo 1248442 1424269 := bbase (se 3 (by rfl) ⟨267050, by rfl⟩ : syracuseStep 1424269 = 534101) (by norm_num)
theorem B1874837 : Blo 1248442 1874837 := bbase (se 6 (by rfl) ⟨43941, by rfl⟩ : syracuseStep 1874837 = 87883) (by norm_num)
theorem B3799973 : Blo 1248442 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B1874861 : Blo 1248442 1874861 := bbase (se 3 (by rfl) ⟨351536, by rfl⟩ : syracuseStep 1874861 = 703073) (by norm_num)
theorem B1874885 : Blo 1248442 1874885 := bbase (se 4 (by rfl) ⟨175770, by rfl⟩ : syracuseStep 1874885 = 351541) (by norm_num)
theorem B3161045 : Blo 1248442 3161045 := bbase (se 7 (by rfl) ⟨37043, by rfl⟩ : syracuseStep 3161045 = 74087) (by norm_num)
theorem B1334237 : Blo 1248442 1334237 := bbase (se 3 (by rfl) ⟨250169, by rfl⟩ : syracuseStep 1334237 = 500339) (by norm_num)
theorem B1874909 : Blo 1248442 1874909 := bbase (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) (by norm_num)
theorem B1874933 : Blo 1248442 1874933 := bbase (se 5 (by rfl) ⟨87887, by rfl⟩ : syracuseStep 1874933 = 175775) (by norm_num)
theorem B1874957 : Blo 1248442 1874957 := bbase (se 3 (by rfl) ⟨351554, by rfl⟩ : syracuseStep 1874957 = 703109) (by norm_num)
theorem B1874981 : Blo 1248442 1874981 := bbase (se 4 (by rfl) ⟨175779, by rfl⟩ : syracuseStep 1874981 = 351559) (by norm_num)
theorem B1580077 : Blo 1248442 1580077 := bbase (se 3 (by rfl) ⟨296264, by rfl⟩ : syracuseStep 1580077 = 592529) (by norm_num)
theorem B1875005 : Blo 1248442 1875005 := bbase (se 3 (by rfl) ⟨351563, by rfl⟩ : syracuseStep 1875005 = 703127) (by norm_num)
theorem B1875029 : Blo 1248442 1875029 := bbase (se 8 (by rfl) ⟨10986, by rfl⟩ : syracuseStep 1875029 = 21973) (by norm_num)
theorem B1875053 : Blo 1248442 1875053 := bbase (se 3 (by rfl) ⟨351572, by rfl⟩ : syracuseStep 1875053 = 703145) (by norm_num)
theorem B1875077 : Blo 1248442 1875077 := bbase (se 4 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 1875077 = 351577) (by norm_num)
theorem B1875101 : Blo 1248442 1875101 := bbase (se 3 (by rfl) ⟨351581, by rfl⟩ : syracuseStep 1875101 = 703163) (by norm_num)
theorem B1875125 : Blo 1248442 1875125 := bbase (se 5 (by rfl) ⟨87896, by rfl⟩ : syracuseStep 1875125 = 175793) (by norm_num)
theorem B2669773 : Blo 1248442 2669773 := bbase (se 3 (by rfl) ⟨500582, by rfl⟩ : syracuseStep 2669773 = 1001165) (by norm_num)
theorem B1875149 : Blo 1248442 1875149 := bbase (se 3 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 1875149 = 703181) (by norm_num)
theorem B1580249 : Blo 1248442 1580249 := bbase (se 2 (by rfl) ⟨592593, by rfl⟩ : syracuseStep 1580249 = 1185187) (by norm_num)
theorem B2809061 : Blo 1248442 2809061 := bbase (se 4 (by rfl) ⟨263349, by rfl⟩ : syracuseStep 2809061 = 526699) (by norm_num)
theorem B1875173 : Blo 1248442 1875173 := bbase (se 4 (by rfl) ⟨175797, by rfl⟩ : syracuseStep 1875173 = 351595) (by norm_num)
theorem B4218101 : Blo 1248442 4218101 := bbase (se 5 (by rfl) ⟨197723, by rfl⟩ : syracuseStep 4218101 = 395447) (by norm_num)
theorem B1875197 : Blo 1248442 1875197 := bbase (se 3 (by rfl) ⟨351599, by rfl⟩ : syracuseStep 1875197 = 703199) (by norm_num)
theorem B1580305 : Blo 1248442 1580305 := bbase (se 2 (by rfl) ⟨592614, by rfl⟩ : syracuseStep 1580305 = 1185229) (by norm_num)
theorem B1875221 : Blo 1248442 1875221 := bbase (se 6 (by rfl) ⟨43950, by rfl⟩ : syracuseStep 1875221 = 87901) (by norm_num)
theorem B2809133 : Blo 1248442 2809133 := bbase (se 3 (by rfl) ⟨526712, by rfl⟩ : syracuseStep 2809133 = 1053425) (by norm_num)
theorem B3161389 : Blo 1248442 3161389 := bbase (se 3 (by rfl) ⟨592760, by rfl⟩ : syracuseStep 3161389 = 1185521) (by norm_num)
theorem B1875245 : Blo 1248442 1875245 := bbase (se 3 (by rfl) ⟨351608, by rfl⟩ : syracuseStep 1875245 = 703217) (by norm_num)
theorem B1875269 : Blo 1248442 1875269 := bbase (se 4 (by rfl) ⟨175806, by rfl⟩ : syracuseStep 1875269 = 351613) (by norm_num)
theorem B2669917 : Blo 1248442 2669917 := bbase (se 3 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 2669917 = 1001219) (by norm_num)
theorem B1875293 : Blo 1248442 1875293 := bbase (se 3 (by rfl) ⟨351617, by rfl⟩ : syracuseStep 1875293 = 703235) (by norm_num)
theorem B1899877 : Blo 1248442 1899877 := bbase (se 4 (by rfl) ⟨178113, by rfl⟩ : syracuseStep 1899877 = 356227) (by norm_num)
theorem B1580401 : Blo 1248442 1580401 := bbase (se 2 (by rfl) ⟨592650, by rfl⟩ : syracuseStep 1580401 = 1185301) (by norm_num)
theorem B2809205 : Blo 1248442 2809205 := bbase (se 5 (by rfl) ⟨131681, by rfl⟩ : syracuseStep 2809205 = 263363) (by norm_num)
theorem B9125237 : Blo 1248442 9125237 := bbase (se 5 (by rfl) ⟨427745, by rfl⟩ : syracuseStep 9125237 = 855491) (by norm_num)
theorem B1875317 : Blo 1248442 1875317 := bbase (se 5 (by rfl) ⟨87905, by rfl⟩ : syracuseStep 1875317 = 175811) (by norm_num)
theorem B1875341 : Blo 1248442 1875341 := bbase (se 3 (by rfl) ⟨351626, by rfl⟩ : syracuseStep 1875341 = 703253) (by norm_num)
theorem B18013589 : Blo 1248442 18013589 := bbase (se 6 (by rfl) ⟨422193, by rfl⟩ : syracuseStep 18013589 = 844387) (by norm_num)
theorem B3161501 : Blo 1248442 3161501 := bbase (se 3 (by rfl) ⟨592781, by rfl⟩ : syracuseStep 3161501 = 1185563) (by norm_num)
theorem B1875365 : Blo 1248442 1875365 := bbase (se 4 (by rfl) ⟨175815, by rfl⟩ : syracuseStep 1875365 = 351631) (by norm_num)
theorem B2809277 : Blo 1248442 2809277 := bbase (se 3 (by rfl) ⟨526739, by rfl⟩ : syracuseStep 2809277 = 1053479) (by norm_num)
theorem B1875389 : Blo 1248442 1875389 := bbase (se 3 (by rfl) ⟨351635, by rfl⟩ : syracuseStep 1875389 = 703271) (by norm_num)
theorem B6323669 : Blo 1248442 6323669 := bbase (se 7 (by rfl) ⟨74105, by rfl⟩ : syracuseStep 6323669 = 148211) (by norm_num)
theorem B1875413 : Blo 1248442 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B1875437 : Blo 1248442 1875437 := bbase (se 3 (by rfl) ⟨351644, by rfl⟩ : syracuseStep 1875437 = 703289) (by norm_num)
theorem B10673653 : Blo 1248442 10673653 := bbase (se 5 (by rfl) ⟨500327, by rfl⟩ : syracuseStep 10673653 = 1000655) (by norm_num)
theorem B2809349 : Blo 1248442 2809349 := bbase (se 4 (by rfl) ⟨263376, by rfl⟩ : syracuseStep 2809349 = 526753) (by norm_num)
theorem B1875461 : Blo 1248442 1875461 := bbase (se 4 (by rfl) ⟨175824, by rfl⟩ : syracuseStep 1875461 = 351649) (by norm_num)
theorem B1580573 : Blo 1248442 1580573 := bbase (se 3 (by rfl) ⟨296357, by rfl⟩ : syracuseStep 1580573 = 592715) (by norm_num)
theorem B1875485 : Blo 1248442 1875485 := bbase (se 3 (by rfl) ⟨351653, by rfl⟩ : syracuseStep 1875485 = 703307) (by norm_num)
theorem B2252333 : Blo 1248442 2252333 := bbase (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) (by norm_num)
theorem B1875509 : Blo 1248442 1875509 := bbase (se 5 (by rfl) ⟨87914, by rfl⟩ : syracuseStep 1875509 = 175829) (by norm_num)
theorem B2809421 : Blo 1248442 2809421 := bbase (se 3 (by rfl) ⟨526766, by rfl⟩ : syracuseStep 2809421 = 1053533) (by norm_num)
theorem B1875533 : Blo 1248442 1875533 := bbase (se 3 (by rfl) ⟨351662, by rfl⟩ : syracuseStep 1875533 = 703325) (by norm_num)
theorem B1580629 : Blo 1248442 1580629 := bbase (se 8 (by rfl) ⟨9261, by rfl⟩ : syracuseStep 1580629 = 18523) (by norm_num)
theorem B3161693 : Blo 1248442 3161693 := bbase (se 3 (by rfl) ⟨592817, by rfl⟩ : syracuseStep 3161693 = 1185635) (by norm_num)
theorem B1875557 : Blo 1248442 1875557 := bbase (se 4 (by rfl) ⟨175833, by rfl⟩ : syracuseStep 1875557 = 351667) (by norm_num)
theorem B1875581 : Blo 1248442 1875581 := bbase (se 3 (by rfl) ⟨351671, by rfl⟩ : syracuseStep 1875581 = 703343) (by norm_num)
theorem B2809493 : Blo 1248442 2809493 := bbase (se 6 (by rfl) ⟨65847, by rfl⟩ : syracuseStep 2809493 = 131695) (by norm_num)
theorem B1875605 : Blo 1248442 1875605 := bbase (se 6 (by rfl) ⟨43959, by rfl⟩ : syracuseStep 1875605 = 87919) (by norm_num)
theorem B4218533 : Blo 1248442 4218533 := bbase (se 4 (by rfl) ⟨395487, by rfl⟩ : syracuseStep 4218533 = 790975) (by norm_num)
theorem B1875629 : Blo 1248442 1875629 := bbase (se 3 (by rfl) ⟨351680, by rfl⟩ : syracuseStep 1875629 = 703361) (by norm_num)
theorem B2530997 : Blo 1248442 2530997 := bbase (se 5 (by rfl) ⟨118640, by rfl⟩ : syracuseStep 2530997 = 237281) (by norm_num)
theorem B1580725 : Blo 1248442 1580725 := bbase (se 5 (by rfl) ⟨74096, by rfl⟩ : syracuseStep 1580725 = 148193) (by norm_num)
theorem B3374789 : Blo 1248442 3374789 := bbase (se 4 (by rfl) ⟨316386, by rfl⟩ : syracuseStep 3374789 = 632773) (by norm_num)
theorem B1875653 : Blo 1248442 1875653 := bbase (se 4 (by rfl) ⟨175842, by rfl⟩ : syracuseStep 1875653 = 351685) (by norm_num)
theorem B1334989 : Blo 1248442 1334989 := bbase (se 3 (by rfl) ⟨250310, by rfl⟩ : syracuseStep 1334989 = 500621) (by norm_num)
theorem B7118549 : Blo 1248442 7118549 := bbase (se 7 (by rfl) ⟨83420, by rfl⟩ : syracuseStep 7118549 = 166841) (by norm_num)
theorem B2670293 : Blo 1248442 2670293 := bbase (se 7 (by rfl) ⟨31292, by rfl⟩ : syracuseStep 2670293 = 62585) (by norm_num)
theorem B2809565 : Blo 1248442 2809565 := bbase (se 3 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 2809565 = 1053587) (by norm_num)
theorem B6004469 : Blo 1248442 6004469 := bbase (se 5 (by rfl) ⟨281459, by rfl⟩ : syracuseStep 6004469 = 562919) (by norm_num)
theorem B1335061 : Blo 1248442 1335061 := bbase (se 6 (by rfl) ⟨31290, by rfl⟩ : syracuseStep 1335061 = 62581) (by norm_num)
theorem B1425181 : Blo 1248442 1425181 := bbase (se 3 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 1425181 = 534443) (by norm_num)
theorem B2809637 : Blo 1248442 2809637 := bbase (se 4 (by rfl) ⟨263403, by rfl⟩ : syracuseStep 2809637 = 526807) (by norm_num)
theorem B4742981 : Blo 1248442 4742981 := bbase (se 4 (by rfl) ⟨444654, by rfl⟩ : syracuseStep 4742981 = 889309) (by norm_num)
theorem B1687373 : Blo 1248442 1687373 := bbase (se 3 (by rfl) ⟨316382, by rfl⟩ : syracuseStep 1687373 = 632765) (by norm_num)
theorem B1580897 : Blo 1248442 1580897 := bbase (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) (by norm_num)
theorem B2809709 : Blo 1248442 2809709 := bbase (se 3 (by rfl) ⟨526820, by rfl⟩ : syracuseStep 2809709 = 1053641) (by norm_num)
theorem B1351553 : Blo 1248442 1351553 := bbase (se 2 (by rfl) ⟨506832, by rfl⟩ : syracuseStep 1351553 = 1013665) (by norm_num)
theorem B1580953 : Blo 1248442 1580953 := bbase (se 2 (by rfl) ⟨592857, by rfl⟩ : syracuseStep 1580953 = 1185715) (by norm_num)
theorem B2809781 : Blo 1248442 2809781 := bbase (se 5 (by rfl) ⟨131708, by rfl⟩ : syracuseStep 2809781 = 263417) (by norm_num)
theorem B3162037 : Blo 1248442 3162037 := bbase (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) (by norm_num)
theorem B1687493 : Blo 1248442 1687493 := bbase (se 4 (by rfl) ⟨158202, by rfl⟩ : syracuseStep 1687493 = 316405) (by norm_num)
theorem B1335241 : Blo 1248442 1335241 := bbase (se 2 (by rfl) ⟨500715, by rfl⟩ : syracuseStep 1335241 = 1001431) (by norm_num)
theorem B1777621 : Blo 1248442 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B1581049 : Blo 1248442 1581049 := bbase (se 2 (by rfl) ⟨592893, by rfl⟩ : syracuseStep 1581049 = 1185787) (by norm_num)
theorem B2809853 : Blo 1248442 2809853 := bbase (se 3 (by rfl) ⟨526847, by rfl⟩ : syracuseStep 2809853 = 1053695) (by norm_num)
theorem B1581059 : Blo 1248442 1581059 := bstep (se 1 (by rfl) ⟨1185794, by rfl⟩ : syracuseStep 1581059 = 2371589) B2371589
theorem B3162179 : Blo 1248442 3162179 := bstep (se 1 (by rfl) ⟨2371634, by rfl⟩ : syracuseStep 3162179 = 4743269) B4743269
theorem B2850947 : Blo 1248442 2850947 := bstep (se 1 (by rfl) ⟨2138210, by rfl⟩ : syracuseStep 2850947 = 4276421) B4276421
theorem B2810033 : Blo 1248442 2810033 := bstep (se 2 (by rfl) ⟨1053762, by rfl⟩ : syracuseStep 2810033 = 2107525) B2107525
theorem B2810051 : Blo 1248442 2810051 := bstep (se 1 (by rfl) ⟨2107538, by rfl⟩ : syracuseStep 2810051 = 4215077) B4215077
theorem B1777889 : Blo 1248442 1777889 := bstep (se 2 (by rfl) ⟨666708, by rfl⟩ : syracuseStep 1777889 = 1333417) B1333417
theorem B8110307 : Blo 1248442 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B5701859 : Blo 1248442 5701859 := bstep (se 1 (by rfl) ⟨4276394, by rfl⟩ : syracuseStep 5701859 = 8552789) B8552789
theorem B4055309 : Blo 1248442 4055309 := bstep (se 3 (by rfl) ⟨760370, by rfl⟩ : syracuseStep 4055309 = 1520741) B1520741
theorem B4219181 : Blo 1248442 4219181 := bstep (se 3 (by rfl) ⟨791096, by rfl⟩ : syracuseStep 4219181 = 1582193) B1582193
theorem B4219235 : Blo 1248442 4219235 := bstep (se 1 (by rfl) ⟨3164426, by rfl⟩ : syracuseStep 4219235 = 6328853) B6328853
theorem B1687969 : Blo 1248442 1687969 := bstep (se 2 (by rfl) ⟨632988, by rfl⟩ : syracuseStep 1687969 = 1265977) B1265977
theorem B9494981 : Blo 1248442 9494981 := bstep (se 4 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 9494981 = 1780309) B1780309
theorem B3375569 : Blo 1248442 3375569 := bstep (se 2 (by rfl) ⟨1265838, by rfl⟩ : syracuseStep 3375569 = 2531677) B2531677
theorem B2810321 : Blo 1248442 2810321 := bstep (se 2 (by rfl) ⟨1053870, by rfl⟩ : syracuseStep 2810321 = 2107741) B2107741
theorem B2810339 : Blo 1248442 2810339 := bstep (se 1 (by rfl) ⟨2107754, by rfl⟩ : syracuseStep 2810339 = 4215509) B4215509
theorem B8552945 : Blo 1248442 8552945 := bstep (se 2 (by rfl) ⟨3207354, by rfl⟩ : syracuseStep 8552945 = 6414709) B6414709
theorem B1688131 : Blo 1248442 1688131 := bstep (se 1 (by rfl) ⟨1266098, by rfl⟩ : syracuseStep 1688131 = 2532197) B2532197
theorem B4219505 : Blo 1248442 4219505 := bstep (se 2 (by rfl) ⟨1582314, by rfl⟩ : syracuseStep 4219505 = 3164629) B3164629
theorem B3555971 : Blo 1248442 3555971 := bstep (se 1 (by rfl) ⟨2666978, by rfl⟩ : syracuseStep 3555971 = 5333957) B5333957
theorem B1581763 : Blo 1248442 1581763 := bstep (se 1 (by rfl) ⟨1186322, by rfl⟩ : syracuseStep 1581763 = 2372645) B2372645
theorem B2138833 : Blo 1248442 2138833 := bstep (se 2 (by rfl) ⟨802062, by rfl⟩ : syracuseStep 2138833 = 1604125) B1604125
theorem B38994659 : Blo 1248442 38994659 := bstep (se 1 (by rfl) ⟨29245994, by rfl⟩ : syracuseStep 38994659 = 58491989) B58491989
theorem B2810609 : Blo 1248442 2810609 := bstep (se 2 (by rfl) ⟨1053978, by rfl⟩ : syracuseStep 2810609 = 2107957) B2107957
theorem B4506353 : Blo 1248442 4506353 := bstep (se 2 (by rfl) ⟨1689882, by rfl⟩ : syracuseStep 4506353 = 3379765) B3379765
theorem B2810627 : Blo 1248442 2810627 := bstep (se 1 (by rfl) ⟨2107970, by rfl⟩ : syracuseStep 2810627 = 4215941) B4215941
theorem B1581859 : Blo 1248442 1581859 := bstep (se 1 (by rfl) ⟨1186394, by rfl⟩ : syracuseStep 1581859 = 2372789) B2372789
theorem B17998645 : Blo 1248442 17998645 := bstep (se 5 (by rfl) ⟨843686, by rfl⟩ : syracuseStep 17998645 = 1687373) B1687373
theorem B1688531 : Blo 1248442 1688531 := bstep (se 1 (by rfl) ⟨1266398, by rfl⟩ : syracuseStep 1688531 = 2532797) B2532797
theorem B3163121 : Blo 1248442 3163121 := bstep (se 2 (by rfl) ⟨1186170, by rfl⟩ : syracuseStep 3163121 = 2372341) B2372341
theorem B2810897 : Blo 1248442 2810897 := bstep (se 2 (by rfl) ⟨1054086, by rfl⟩ : syracuseStep 2810897 = 2108173) B2108173
theorem B2810915 : Blo 1248442 2810915 := bstep (se 1 (by rfl) ⟨2108186, by rfl⟩ : syracuseStep 2810915 = 4216373) B4216373
theorem B3163171 : Blo 1248442 3163171 := bstep (se 1 (by rfl) ⟨2372378, by rfl⟩ : syracuseStep 3163171 = 4744757) B4744757
theorem B4744241 : Blo 1248442 4744241 := bstep (se 2 (by rfl) ⟨1779090, by rfl⟩ : syracuseStep 4744241 = 3558181) B3558181
theorem B1778755 : Blo 1248442 1778755 := bstep (se 1 (by rfl) ⟨1334066, by rfl⟩ : syracuseStep 1778755 = 2668133) B2668133
theorem B4220045 : Blo 1248442 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B1778851 : Blo 1248442 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B3163313 : Blo 1248442 3163313 := bstep (se 2 (by rfl) ⟨1186242, by rfl⟩ : syracuseStep 3163313 = 2372485) B2372485
theorem B4220099 : Blo 1248442 4220099 := bstep (se 1 (by rfl) ⟨3165074, by rfl⟩ : syracuseStep 4220099 = 6330149) B6330149
theorem B1582355 : Blo 1248442 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B1926433 : Blo 1248442 1926433 := bstep (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) B1444825
theorem B2811185 : Blo 1248442 2811185 := bstep (se 2 (by rfl) ⟨1054194, by rfl⟩ : syracuseStep 2811185 = 2108389) B2108389
theorem B2811203 : Blo 1248442 2811203 := bstep (se 1 (by rfl) ⟨2108402, by rfl⟩ : syracuseStep 2811203 = 4216805) B4216805
theorem B2000209 : Blo 1248442 2000209 := bstep (se 2 (by rfl) ⟨750078, by rfl⟩ : syracuseStep 2000209 = 1500157) B1500157
theorem B3802477 : Blo 1248442 3802477 := bstep (se 3 (by rfl) ⟨712964, by rfl⟩ : syracuseStep 3802477 = 1425929) B1425929
theorem B2106769 : Blo 1248442 2106769 := bstep (se 2 (by rfl) ⟨790038, by rfl⟩ : syracuseStep 2106769 = 1580077) B1580077
theorem B1688995 : Blo 1248442 1688995 := bstep (se 1 (by rfl) ⟨1266746, by rfl⟩ : syracuseStep 1688995 = 2533493) B2533493
theorem B3556781 : Blo 1248442 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B2106803 : Blo 1248442 2106803 := bstep (se 1 (by rfl) ⟨1580102, by rfl⟩ : syracuseStep 2106803 = 3160205) B3160205
theorem B14222789 : Blo 1248442 14222789 := bstep (se 4 (by rfl) ⟨1333386, by rfl⟩ : syracuseStep 14222789 = 2666773) B2666773
theorem B7120325 : Blo 1248442 7120325 := bstep (se 4 (by rfl) ⟨667530, by rfl⟩ : syracuseStep 7120325 = 1335061) B1335061
theorem B6006221 : Blo 1248442 6006221 := bstep (se 3 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 6006221 = 2252333) B2252333
theorem B2106931 : Blo 1248442 2106931 := bstep (se 1 (by rfl) ⟨1580198, by rfl⟩ : syracuseStep 2106931 = 3160397) B3160397
theorem B2000465 : Blo 1248442 2000465 := bstep (se 2 (by rfl) ⟨750174, by rfl⟩ : syracuseStep 2000465 = 1500349) B1500349
theorem B2811473 : Blo 1248442 2811473 := bstep (se 2 (by rfl) ⟨1054302, by rfl⟩ : syracuseStep 2811473 = 2108605) B2108605
theorem B1689169 : Blo 1248442 1689169 := bstep (se 2 (by rfl) ⟨633438, by rfl⟩ : syracuseStep 1689169 = 1266877) B1266877
theorem B2811491 : Blo 1248442 2811491 := bstep (se 1 (by rfl) ⟨2108618, by rfl⟩ : syracuseStep 2811491 = 4217237) B4217237
theorem B3556973 : Blo 1248442 3556973 := bstep (se 3 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 3556973 = 1333865) B1333865
theorem B1779347 : Blo 1248442 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B6325937 : Blo 1248442 6325937 := bstep (se 2 (by rfl) ⟨2372226, by rfl⟩ : syracuseStep 6325937 = 4744453) B4744453
theorem B2107073 : Blo 1248442 2107073 := bstep (se 2 (by rfl) ⟨790152, by rfl⟩ : syracuseStep 2107073 = 1580305) B1580305
theorem B5695181 : Blo 1248442 5695181 := bstep (se 3 (by rfl) ⟨1067846, by rfl⟩ : syracuseStep 5695181 = 2135693) B2135693
theorem B4056817 : Blo 1248442 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B2000657 : Blo 1248442 2000657 := bstep (se 2 (by rfl) ⟨750246, by rfl⟩ : syracuseStep 2000657 = 1500493) B1500493
theorem B1951523 : Blo 1248442 1951523 := bstep (se 1 (by rfl) ⟨1463642, by rfl⟩ : syracuseStep 1951523 = 2927285) B2927285
theorem B7702307 : Blo 1248442 7702307 := bstep (se 1 (by rfl) ⟨5776730, by rfl⟩ : syracuseStep 7702307 = 11553461) B11553461
theorem B2533169 : Blo 1248442 2533169 := bstep (se 2 (by rfl) ⟨949938, by rfl⟩ : syracuseStep 2533169 = 1899877) B1899877
theorem B2107201 : Blo 1248442 2107201 := bstep (se 2 (by rfl) ⟨790200, by rfl⟩ : syracuseStep 2107201 = 1580401) B1580401
theorem B2107235 : Blo 1248442 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B2811761 : Blo 1248442 2811761 := bstep (se 2 (by rfl) ⟨1054410, by rfl⟩ : syracuseStep 2811761 = 2108821) B2108821
theorem B2811779 : Blo 1248442 2811779 := bstep (se 1 (by rfl) ⟨2108834, by rfl⟩ : syracuseStep 2811779 = 4217669) B4217669
theorem B7120781 : Blo 1248442 7120781 := bstep (se 3 (by rfl) ⟨1335146, by rfl⟩ : syracuseStep 7120781 = 2670293) B2670293
theorem B2107363 : Blo 1248442 2107363 := bstep (se 1 (by rfl) ⟨1580522, by rfl⟩ : syracuseStep 2107363 = 3161045) B3161045
theorem B14231537 : Blo 1248442 14231537 := bstep (se 2 (by rfl) ⟨5336826, by rfl⟩ : syracuseStep 14231537 = 10673653) B10673653
theorem B6752261 : Blo 1248442 6752261 := bstep (se 4 (by rfl) ⟨633024, by rfl⟩ : syracuseStep 6752261 = 1266049) B1266049
theorem B7112717 : Blo 1248442 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B7596101 : Blo 1248442 7596101 := bstep (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) B1424269
theorem B2107505 : Blo 1248442 2107505 := bstep (se 2 (by rfl) ⟨790314, by rfl⟩ : syracuseStep 2107505 = 1580629) B1580629
theorem B2812049 : Blo 1248442 2812049 := bstep (se 2 (by rfl) ⟨1054518, by rfl⟩ : syracuseStep 2812049 = 2109037) B2109037
theorem B3164305 : Blo 1248442 3164305 := bstep (se 2 (by rfl) ⟨1186614, by rfl⟩ : syracuseStep 3164305 = 2373229) B2373229
theorem B2812067 : Blo 1248442 2812067 := bstep (se 1 (by rfl) ⟨2109050, by rfl⟩ : syracuseStep 2812067 = 4218101) B4218101
theorem B2107633 : Blo 1248442 2107633 := bstep (se 2 (by rfl) ⟨790362, by rfl⟩ : syracuseStep 2107633 = 1580725) B1580725
theorem B1779985 : Blo 1248442 1779985 := bstep (se 2 (by rfl) ⟨667494, by rfl⟩ : syracuseStep 1779985 = 1334989) B1334989
theorem B2107667 : Blo 1248442 2107667 := bstep (se 1 (by rfl) ⟨1580750, by rfl⟩ : syracuseStep 2107667 = 3161501) B3161501
theorem B2107795 : Blo 1248442 2107795 := bstep (se 1 (by rfl) ⟨1580846, by rfl⟩ : syracuseStep 2107795 = 3161693) B3161693
theorem B3164579 : Blo 1248442 3164579 := bstep (se 1 (by rfl) ⟨2373434, by rfl⟩ : syracuseStep 3164579 = 4746869) B4746869
theorem B2812337 : Blo 1248442 2812337 := bstep (se 2 (by rfl) ⟨1054626, by rfl⟩ : syracuseStep 2812337 = 2109253) B2109253
theorem B2812355 : Blo 1248442 2812355 := bstep (se 1 (by rfl) ⟨2109266, by rfl⟩ : syracuseStep 2812355 = 4218533) B4218533
theorem B4745699 : Blo 1248442 4745699 := bstep (se 1 (by rfl) ⟨3559274, by rfl⟩ : syracuseStep 4745699 = 7118549) B7118549
theorem B4499981 : Blo 1248442 4499981 := bstep (se 3 (by rfl) ⟨843746, by rfl⟩ : syracuseStep 4499981 = 1687493) B1687493
theorem B2107937 : Blo 1248442 2107937 := bstep (se 2 (by rfl) ⟨790476, by rfl⟩ : syracuseStep 2107937 = 1580953) B1580953
theorem B3557965 : Blo 1248442 3557965 := bstep (se 3 (by rfl) ⟨667118, by rfl⟩ : syracuseStep 3557965 = 1334237) B1334237
theorem B1780321 : Blo 1248442 1780321 := bstep (se 2 (by rfl) ⟨667620, by rfl⟩ : syracuseStep 1780321 = 1335241) B1335241
theorem B3164771 : Blo 1248442 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B2370161 : Blo 1248442 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B2108065 : Blo 1248442 2108065 := bstep (se 2 (by rfl) ⟨790524, by rfl⟩ : syracuseStep 2108065 = 1581049) B1581049
theorem B2108099 : Blo 1248442 2108099 := bstep (se 1 (by rfl) ⟨1581074, by rfl⟩ : syracuseStep 2108099 = 3162149) B3162149
theorem B2812625 : Blo 1248442 2812625 := bstep (se 2 (by rfl) ⟨1054734, by rfl⟩ : syracuseStep 2812625 = 2109469) B2109469
theorem B2812643 : Blo 1248442 2812643 := bstep (se 1 (by rfl) ⟨2109482, by rfl⟩ : syracuseStep 2812643 = 4218965) B4218965
theorem B2108227 : Blo 1248442 2108227 := bstep (se 1 (by rfl) ⟨1581170, by rfl⟩ : syracuseStep 2108227 = 3162341) B3162341
theorem B2108369 : Blo 1248442 2108369 := bstep (se 2 (by rfl) ⟨790638, by rfl⟩ : syracuseStep 2108369 = 1581277) B1581277
theorem B17099761 : Blo 1248442 17099761 := bstep (se 2 (by rfl) ⟨6412410, by rfl⟩ : syracuseStep 17099761 = 12824821) B12824821
theorem B3607537 : Blo 1248442 3607537 := bstep (se 2 (by rfl) ⟨1352826, by rfl⟩ : syracuseStep 3607537 = 2705653) B2705653
theorem B2812913 : Blo 1248442 2812913 := bstep (se 2 (by rfl) ⟨1054842, by rfl⟩ : syracuseStep 2812913 = 2109685) B2109685
theorem B2812931 : Blo 1248442 2812931 := bstep (se 1 (by rfl) ⟨2109698, by rfl⟩ : syracuseStep 2812931 = 4219397) B4219397
theorem B2001971 : Blo 1248442 2001971 := bstep (se 1 (by rfl) ⟨1501478, by rfl⟩ : syracuseStep 2001971 = 3002957) B3002957
theorem B2108497 : Blo 1248442 2108497 := bstep (se 2 (by rfl) ⟨790686, by rfl⟩ : syracuseStep 2108497 = 1581373) B1581373
theorem B6327395 : Blo 1248442 6327395 := bstep (se 1 (by rfl) ⟨4745546, by rfl⟩ : syracuseStep 6327395 = 9491093) B9491093
theorem B2108531 : Blo 1248442 2108531 := bstep (se 1 (by rfl) ⟨1581398, by rfl⟩ : syracuseStep 2108531 = 3162797) B3162797
theorem B2280611 : Blo 1248442 2280611 := bstep (se 1 (by rfl) ⟨1710458, by rfl⟩ : syracuseStep 2280611 = 3420917) B3420917
theorem B4058275 : Blo 1248442 4058275 := bstep (se 1 (by rfl) ⟨3043706, by rfl⟩ : syracuseStep 4058275 = 6087413) B6087413
theorem B15191221 : Blo 1248442 15191221 := bstep (se 5 (by rfl) ⟨712088, by rfl⟩ : syracuseStep 15191221 = 1424177) B1424177
theorem B1248451 : Blo 1248442 1248451 := bstep (se 1 (by rfl) ⟨936338, by rfl⟩ : syracuseStep 1248451 = 1872677) B1872677
theorem B1248467 : Blo 1248442 1248467 := bstep (se 1 (by rfl) ⟨936350, by rfl⟩ : syracuseStep 1248467 = 1872701) B1872701
theorem B1248483 : Blo 1248442 1248483 := bstep (se 1 (by rfl) ⟨936362, by rfl⟩ : syracuseStep 1248483 = 1872725) B1872725
theorem B9489635 : Blo 1248442 9489635 := bstep (se 1 (by rfl) ⟨7117226, by rfl⟩ : syracuseStep 9489635 = 14234453) B14234453
theorem B4213997 : Blo 1248442 4213997 := bstep (se 3 (by rfl) ⟨790124, by rfl⟩ : syracuseStep 4213997 = 1580249) B1580249
theorem B1248499 : Blo 1248442 1248499 := bstep (se 1 (by rfl) ⟨936374, by rfl⟩ : syracuseStep 1248499 = 1872749) B1872749
theorem B2108659 : Blo 1248442 2108659 := bstep (se 1 (by rfl) ⟨1581494, by rfl⟩ : syracuseStep 2108659 = 3162989) B3162989
theorem B1248515 : Blo 1248442 1248515 := bstep (se 1 (by rfl) ⟨936386, by rfl⟩ : syracuseStep 1248515 = 1872773) B1872773
theorem B2813201 : Blo 1248442 2813201 := bstep (se 2 (by rfl) ⟨1054950, by rfl⟩ : syracuseStep 2813201 = 2109901) B2109901
theorem B1248531 : Blo 1248442 1248531 := bstep (se 1 (by rfl) ⟨936398, by rfl⟩ : syracuseStep 1248531 = 1872797) B1872797
theorem B2002195 : Blo 1248442 2002195 := bstep (se 1 (by rfl) ⟨1501646, by rfl⟩ : syracuseStep 2002195 = 3003293) B3003293
theorem B1248547 : Blo 1248442 1248547 := bstep (se 1 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 1248547 = 1872821) B1872821
theorem B4214051 : Blo 1248442 4214051 := bstep (se 1 (by rfl) ⟨3160538, by rfl⟩ : syracuseStep 4214051 = 6321077) B6321077
theorem B2813219 : Blo 1248442 2813219 := bstep (se 1 (by rfl) ⟨2109914, by rfl⟩ : syracuseStep 2813219 = 4219829) B4219829
theorem B1248563 : Blo 1248442 1248563 := bstep (se 1 (by rfl) ⟨936422, by rfl⟩ : syracuseStep 1248563 = 1872845) B1872845
theorem B1248579 : Blo 1248442 1248579 := bstep (se 1 (by rfl) ⟨936434, by rfl⟩ : syracuseStep 1248579 = 1872869) B1872869
theorem B2370883 : Blo 1248442 2370883 := bstep (se 1 (by rfl) ⟨1778162, by rfl⟩ : syracuseStep 2370883 = 3556325) B3556325
theorem B1248595 : Blo 1248442 1248595 := bstep (se 1 (by rfl) ⟨936446, by rfl⟩ : syracuseStep 1248595 = 1872893) B1872893
theorem B2002259 : Blo 1248442 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B1248611 : Blo 1248442 1248611 := bstep (se 1 (by rfl) ⟨936458, by rfl⟩ : syracuseStep 1248611 = 1872917) B1872917
theorem B1248627 : Blo 1248442 1248627 := bstep (se 1 (by rfl) ⟨936470, by rfl⟩ : syracuseStep 1248627 = 1872941) B1872941
theorem B2108801 : Blo 1248442 2108801 := bstep (se 2 (by rfl) ⟨790800, by rfl⟩ : syracuseStep 2108801 = 1581601) B1581601
theorem B1248643 : Blo 1248442 1248643 := bstep (se 1 (by rfl) ⟨936482, by rfl⟩ : syracuseStep 1248643 = 1872965) B1872965
theorem B1248659 : Blo 1248442 1248659 := bstep (se 1 (by rfl) ⟨936494, by rfl⟩ : syracuseStep 1248659 = 1872989) B1872989
theorem B1248675 : Blo 1248442 1248675 := bstep (se 1 (by rfl) ⟨936506, by rfl⟩ : syracuseStep 1248675 = 1873013) B1873013
theorem B3378595 : Blo 1248442 3378595 := bstep (se 1 (by rfl) ⟨2533946, by rfl⟩ : syracuseStep 3378595 = 5067893) B5067893
theorem B1248691 : Blo 1248442 1248691 := bstep (se 1 (by rfl) ⟨936518, by rfl⟩ : syracuseStep 1248691 = 1873037) B1873037
theorem B1248707 : Blo 1248442 1248707 := bstep (se 1 (by rfl) ⟨936530, by rfl⟩ : syracuseStep 1248707 = 1873061) B1873061
theorem B4746701 : Blo 1248442 4746701 := bstep (se 3 (by rfl) ⟨890006, by rfl⟩ : syracuseStep 4746701 = 1780013) B1780013
theorem B1248723 : Blo 1248442 1248723 := bstep (se 1 (by rfl) ⟨936542, by rfl⟩ : syracuseStep 1248723 = 1873085) B1873085
theorem B2002387 : Blo 1248442 2002387 := bstep (se 1 (by rfl) ⟨1501790, by rfl⟩ : syracuseStep 2002387 = 3003581) B3003581
theorem B1248739 : Blo 1248442 1248739 := bstep (se 1 (by rfl) ⟨936554, by rfl⟩ : syracuseStep 1248739 = 1873109) B1873109
theorem B10669553 : Blo 1248442 10669553 := bstep (se 2 (by rfl) ⟨4001082, by rfl⟩ : syracuseStep 10669553 = 8002165) B8002165
theorem B1248755 : Blo 1248442 1248755 := bstep (se 1 (by rfl) ⟨936566, by rfl⟩ : syracuseStep 1248755 = 1873133) B1873133
theorem B2108929 : Blo 1248442 2108929 := bstep (se 2 (by rfl) ⟨790848, by rfl⟩ : syracuseStep 2108929 = 1581697) B1581697
theorem B1248771 : Blo 1248442 1248771 := bstep (se 1 (by rfl) ⟨936578, by rfl⟩ : syracuseStep 1248771 = 1873157) B1873157
theorem B1248787 : Blo 1248442 1248787 := bstep (se 1 (by rfl) ⟨936590, by rfl⟩ : syracuseStep 1248787 = 1873181) B1873181
theorem B1248803 : Blo 1248442 1248803 := bstep (se 1 (by rfl) ⟨936602, by rfl⟩ : syracuseStep 1248803 = 1873205) B1873205
theorem B2108963 : Blo 1248442 2108963 := bstep (se 1 (by rfl) ⟨1581722, by rfl⟩ : syracuseStep 2108963 = 3163445) B3163445
theorem B4214321 : Blo 1248442 4214321 := bstep (se 2 (by rfl) ⟨1580370, by rfl⟩ : syracuseStep 4214321 = 3160741) B3160741
theorem B8547889 : Blo 1248442 8547889 := bstep (se 2 (by rfl) ⟨3205458, by rfl⟩ : syracuseStep 8547889 = 6410917) B6410917
theorem B1248819 : Blo 1248442 1248819 := bstep (se 1 (by rfl) ⟨936614, by rfl⟩ : syracuseStep 1248819 = 1873229) B1873229
theorem B2813489 : Blo 1248442 2813489 := bstep (se 2 (by rfl) ⟨1055058, by rfl⟩ : syracuseStep 2813489 = 2110117) B2110117
theorem B1248835 : Blo 1248442 1248835 := bstep (se 1 (by rfl) ⟨936626, by rfl⟩ : syracuseStep 1248835 = 1873253) B1873253
theorem B1404499 : Blo 1248442 1404499 := bstep (se 1 (by rfl) ⟨1053374, by rfl⟩ : syracuseStep 1404499 = 2106749) B2106749
theorem B1248851 : Blo 1248442 1248851 := bstep (se 1 (by rfl) ⟨936638, by rfl⟩ : syracuseStep 1248851 = 1873277) B1873277
theorem B1248867 : Blo 1248442 1248867 := bstep (se 1 (by rfl) ⟨936650, by rfl⟩ : syracuseStep 1248867 = 1873301) B1873301
theorem B5336675 : Blo 1248442 5336675 := bstep (se 1 (by rfl) ⟨4002506, by rfl⟩ : syracuseStep 5336675 = 8005013) B8005013
theorem B1691249 : Blo 1248442 1691249 := bstep (se 2 (by rfl) ⟨634218, by rfl⟩ : syracuseStep 1691249 = 1268437) B1268437
theorem B6753905 : Blo 1248442 6753905 := bstep (se 2 (by rfl) ⟨2532714, by rfl⟩ : syracuseStep 6753905 = 5065429) B5065429
theorem B1248883 : Blo 1248442 1248883 := bstep (se 1 (by rfl) ⟨936662, by rfl⟩ : syracuseStep 1248883 = 1873325) B1873325
theorem B1248899 : Blo 1248442 1248899 := bstep (se 1 (by rfl) ⟨936674, by rfl⟩ : syracuseStep 1248899 = 1873349) B1873349
theorem B24333965 : Blo 1248442 24333965 := bstep (se 3 (by rfl) ⟨4562618, by rfl⟩ : syracuseStep 24333965 = 9125237) B9125237
theorem B1248915 : Blo 1248442 1248915 := bstep (se 1 (by rfl) ⟨936686, by rfl⟩ : syracuseStep 1248915 = 1873373) B1873373
theorem B1248931 : Blo 1248442 1248931 := bstep (se 1 (by rfl) ⟨936698, by rfl⟩ : syracuseStep 1248931 = 1873397) B1873397
theorem B2109091 : Blo 1248442 2109091 := bstep (se 1 (by rfl) ⟨1581818, by rfl⟩ : syracuseStep 2109091 = 3163637) B3163637
theorem B1248947 : Blo 1248442 1248947 := bstep (se 1 (by rfl) ⟨936710, by rfl⟩ : syracuseStep 1248947 = 1873421) B1873421
theorem B1248963 : Blo 1248442 1248963 := bstep (se 1 (by rfl) ⟨936722, by rfl⟩ : syracuseStep 1248963 = 1873445) B1873445
theorem B1248979 : Blo 1248442 1248979 := bstep (se 1 (by rfl) ⟨936734, by rfl⟩ : syracuseStep 1248979 = 1873469) B1873469
theorem B1404643 : Blo 1248442 1404643 := bstep (se 1 (by rfl) ⟨1053482, by rfl⟩ : syracuseStep 1404643 = 2106965) B2106965
theorem B1248995 : Blo 1248442 1248995 := bstep (se 1 (by rfl) ⟨936746, by rfl⟩ : syracuseStep 1248995 = 1873493) B1873493
theorem B3854051 : Blo 1248442 3854051 := bstep (se 1 (by rfl) ⟨2890538, by rfl⟩ : syracuseStep 3854051 = 5781077) B5781077
theorem B1249011 : Blo 1248442 1249011 := bstep (se 1 (by rfl) ⟨936758, by rfl⟩ : syracuseStep 1249011 = 1873517) B1873517
theorem B1249027 : Blo 1248442 1249027 := bstep (se 1 (by rfl) ⟨936770, by rfl⟩ : syracuseStep 1249027 = 1873541) B1873541
theorem B2371331 : Blo 1248442 2371331 := bstep (se 1 (by rfl) ⟨1778498, by rfl⟩ : syracuseStep 2371331 = 3556997) B3556997
theorem B1249043 : Blo 1248442 1249043 := bstep (se 1 (by rfl) ⟨936782, by rfl⟩ : syracuseStep 1249043 = 1873565) B1873565
theorem B1249059 : Blo 1248442 1249059 := bstep (se 1 (by rfl) ⟨936794, by rfl⟩ : syracuseStep 1249059 = 1873589) B1873589
theorem B2109233 : Blo 1248442 2109233 := bstep (se 2 (by rfl) ⟨790962, by rfl⟩ : syracuseStep 2109233 = 1581925) B1581925
theorem B1249075 : Blo 1248442 1249075 := bstep (se 1 (by rfl) ⟨936806, by rfl⟩ : syracuseStep 1249075 = 1873613) B1873613
theorem B1249091 : Blo 1248442 1249091 := bstep (se 1 (by rfl) ⟨936818, by rfl⟩ : syracuseStep 1249091 = 1873637) B1873637
theorem B10137413 : Blo 1248442 10137413 := bstep (se 4 (by rfl) ⟨950382, by rfl⟩ : syracuseStep 10137413 = 1900765) B1900765
theorem B1249107 : Blo 1248442 1249107 := bstep (se 1 (by rfl) ⟨936830, by rfl⟩ : syracuseStep 1249107 = 1873661) B1873661
theorem B1249123 : Blo 1248442 1249123 := bstep (se 1 (by rfl) ⟨936842, by rfl⟩ : syracuseStep 1249123 = 1873685) B1873685
theorem B1404787 : Blo 1248442 1404787 := bstep (se 1 (by rfl) ⟨1053590, by rfl⟩ : syracuseStep 1404787 = 2107181) B2107181
theorem B1249139 : Blo 1248442 1249139 := bstep (se 1 (by rfl) ⟨936854, by rfl⟩ : syracuseStep 1249139 = 1873709) B1873709
theorem B1249155 : Blo 1248442 1249155 := bstep (se 1 (by rfl) ⟨936866, by rfl⟩ : syracuseStep 1249155 = 1873733) B1873733
theorem B6328205 : Blo 1248442 6328205 := bstep (se 3 (by rfl) ⟨1186538, by rfl⟩ : syracuseStep 6328205 = 2373077) B2373077
theorem B1249171 : Blo 1248442 1249171 := bstep (se 1 (by rfl) ⟨936878, by rfl⟩ : syracuseStep 1249171 = 1873757) B1873757
theorem B1249187 : Blo 1248442 1249187 := bstep (se 1 (by rfl) ⟨936890, by rfl⟩ : syracuseStep 1249187 = 1873781) B1873781
theorem B2109361 : Blo 1248442 2109361 := bstep (se 2 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 2109361 = 1582021) B1582021
theorem B1249203 : Blo 1248442 1249203 := bstep (se 1 (by rfl) ⟨936902, by rfl⟩ : syracuseStep 1249203 = 1873805) B1873805
theorem B1249219 : Blo 1248442 1249219 := bstep (se 1 (by rfl) ⟨936914, by rfl⟩ : syracuseStep 1249219 = 1873829) B1873829
theorem B2666449 : Blo 1248442 2666449 := bstep (se 2 (by rfl) ⟨999918, by rfl⟩ : syracuseStep 2666449 = 1999837) B1999837
theorem B1249235 : Blo 1248442 1249235 := bstep (se 1 (by rfl) ⟨936926, by rfl⟩ : syracuseStep 1249235 = 1873853) B1873853
theorem B2109395 : Blo 1248442 2109395 := bstep (se 1 (by rfl) ⟨1582046, by rfl⟩ : syracuseStep 2109395 = 3164093) B3164093
theorem B1249251 : Blo 1248442 1249251 := bstep (se 1 (by rfl) ⟨936938, by rfl⟩ : syracuseStep 1249251 = 1873877) B1873877
theorem B1249267 : Blo 1248442 1249267 := bstep (se 1 (by rfl) ⟨936950, by rfl⟩ : syracuseStep 1249267 = 1873901) B1873901
theorem B1404931 : Blo 1248442 1404931 := bstep (se 1 (by rfl) ⟨1053698, by rfl⟩ : syracuseStep 1404931 = 2107397) B2107397
theorem B1249283 : Blo 1248442 1249283 := bstep (se 1 (by rfl) ⟨936962, by rfl⟩ : syracuseStep 1249283 = 1873925) B1873925
theorem B1249299 : Blo 1248442 1249299 := bstep (se 1 (by rfl) ⟨936974, by rfl⟩ : syracuseStep 1249299 = 1873949) B1873949
theorem B2371619 : Blo 1248442 2371619 := bstep (se 1 (by rfl) ⟨1778714, by rfl⟩ : syracuseStep 2371619 = 3557429) B3557429
theorem B1249315 : Blo 1248442 1249315 := bstep (se 1 (by rfl) ⟨936986, by rfl⟩ : syracuseStep 1249315 = 1873973) B1873973
theorem B1249331 : Blo 1248442 1249331 := bstep (se 1 (by rfl) ⟨936998, by rfl⟩ : syracuseStep 1249331 = 1873997) B1873997
theorem B1249347 : Blo 1248442 1249347 := bstep (se 1 (by rfl) ⟨937010, by rfl⟩ : syracuseStep 1249347 = 1874021) B1874021
theorem B4214861 : Blo 1248442 4214861 := bstep (se 3 (by rfl) ⟨790286, by rfl⟩ : syracuseStep 4214861 = 1580573) B1580573
theorem B1249363 : Blo 1248442 1249363 := bstep (se 1 (by rfl) ⟨937022, by rfl⟩ : syracuseStep 1249363 = 1874045) B1874045
theorem B2109523 : Blo 1248442 2109523 := bstep (se 1 (by rfl) ⟨1582142, by rfl⟩ : syracuseStep 2109523 = 3164285) B3164285
theorem B1249379 : Blo 1248442 1249379 := bstep (se 1 (by rfl) ⟨937034, by rfl⟩ : syracuseStep 1249379 = 1874069) B1874069
theorem B1249395 : Blo 1248442 1249395 := bstep (se 1 (by rfl) ⟨937046, by rfl⟩ : syracuseStep 1249395 = 1874093) B1874093
theorem B4214915 : Blo 1248442 4214915 := bstep (se 1 (by rfl) ⟨3161186, by rfl⟩ : syracuseStep 4214915 = 6322373) B6322373
theorem B1249411 : Blo 1248442 1249411 := bstep (se 1 (by rfl) ⟨937058, by rfl⟩ : syracuseStep 1249411 = 1874117) B1874117
theorem B1405075 : Blo 1248442 1405075 := bstep (se 1 (by rfl) ⟨1053806, by rfl⟩ : syracuseStep 1405075 = 2107613) B2107613
theorem B1249427 : Blo 1248442 1249427 := bstep (se 1 (by rfl) ⟨937070, by rfl⟩ : syracuseStep 1249427 = 1874141) B1874141
theorem B1249443 : Blo 1248442 1249443 := bstep (se 1 (by rfl) ⟨937082, by rfl⟩ : syracuseStep 1249443 = 1874165) B1874165
theorem B1249459 : Blo 1248442 1249459 := bstep (se 1 (by rfl) ⟨937094, by rfl⟩ : syracuseStep 1249459 = 1874189) B1874189
theorem B1249475 : Blo 1248442 1249475 := bstep (se 1 (by rfl) ⟨937106, by rfl⟩ : syracuseStep 1249475 = 1874213) B1874213
theorem B7114949 : Blo 1248442 7114949 := bstep (se 4 (by rfl) ⟨667026, by rfl⟩ : syracuseStep 7114949 = 1334053) B1334053
theorem B1249491 : Blo 1248442 1249491 := bstep (se 1 (by rfl) ⟨937118, by rfl⟩ : syracuseStep 1249491 = 1874237) B1874237
theorem B2109665 : Blo 1248442 2109665 := bstep (se 2 (by rfl) ⟨791124, by rfl⟩ : syracuseStep 2109665 = 1582249) B1582249
theorem B1249507 : Blo 1248442 1249507 := bstep (se 1 (by rfl) ⟨937130, by rfl⟩ : syracuseStep 1249507 = 1874261) B1874261
theorem B1249523 : Blo 1248442 1249523 := bstep (se 1 (by rfl) ⟨937142, by rfl⟩ : syracuseStep 1249523 = 1874285) B1874285
theorem B1249539 : Blo 1248442 1249539 := bstep (se 1 (by rfl) ⟨937154, by rfl⟩ : syracuseStep 1249539 = 1874309) B1874309
theorem B1249555 : Blo 1248442 1249555 := bstep (se 1 (by rfl) ⟨937166, by rfl⟩ : syracuseStep 1249555 = 1874333) B1874333
theorem B3559697 : Blo 1248442 3559697 := bstep (se 2 (by rfl) ⟨1334886, by rfl⟩ : syracuseStep 3559697 = 2669773) B2669773
theorem B1405219 : Blo 1248442 1405219 := bstep (se 1 (by rfl) ⟨1053914, by rfl⟩ : syracuseStep 1405219 = 2107829) B2107829
theorem B6754595 : Blo 1248442 6754595 := bstep (se 1 (by rfl) ⟨5065946, by rfl⟩ : syracuseStep 6754595 = 10131893) B10131893
theorem B1249571 : Blo 1248442 1249571 := bstep (se 1 (by rfl) ⟨937178, by rfl⟩ : syracuseStep 1249571 = 1874357) B1874357
theorem B1249587 : Blo 1248442 1249587 := bstep (se 1 (by rfl) ⟨937190, by rfl⟩ : syracuseStep 1249587 = 1874381) B1874381
theorem B1249603 : Blo 1248442 1249603 := bstep (se 1 (by rfl) ⟨937202, by rfl⟩ : syracuseStep 1249603 = 1874405) B1874405
theorem B1249619 : Blo 1248442 1249619 := bstep (se 1 (by rfl) ⟨937214, by rfl⟩ : syracuseStep 1249619 = 1874429) B1874429
theorem B2109793 : Blo 1248442 2109793 := bstep (se 2 (by rfl) ⟨791172, by rfl⟩ : syracuseStep 2109793 = 1582345) B1582345
theorem B1249635 : Blo 1248442 1249635 := bstep (se 1 (by rfl) ⟨937226, by rfl⟩ : syracuseStep 1249635 = 1874453) B1874453
theorem B2027891 : Blo 1248442 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B1249651 : Blo 1248442 1249651 := bstep (se 1 (by rfl) ⟨937238, by rfl⟩ : syracuseStep 1249651 = 1874477) B1874477
theorem B1249667 : Blo 1248442 1249667 := bstep (se 1 (by rfl) ⟨937250, by rfl⟩ : syracuseStep 1249667 = 1874501) B1874501
theorem B2109827 : Blo 1248442 2109827 := bstep (se 1 (by rfl) ⟨1582370, by rfl⟩ : syracuseStep 2109827 = 3164741) B3164741
theorem B4215185 : Blo 1248442 4215185 := bstep (se 2 (by rfl) ⟨1580694, by rfl⟩ : syracuseStep 4215185 = 3161389) B3161389
theorem B1249683 : Blo 1248442 1249683 := bstep (se 1 (by rfl) ⟨937262, by rfl⟩ : syracuseStep 1249683 = 1874525) B1874525
theorem B1249699 : Blo 1248442 1249699 := bstep (se 1 (by rfl) ⟨937274, by rfl⟩ : syracuseStep 1249699 = 1874549) B1874549
theorem B1405363 : Blo 1248442 1405363 := bstep (se 1 (by rfl) ⟨1054022, by rfl⟩ : syracuseStep 1405363 = 2108045) B2108045
theorem B1249715 : Blo 1248442 1249715 := bstep (se 1 (by rfl) ⟨937286, by rfl⟩ : syracuseStep 1249715 = 1874573) B1874573
theorem B1249731 : Blo 1248442 1249731 := bstep (se 1 (by rfl) ⟨937298, by rfl⟩ : syracuseStep 1249731 = 1874597) B1874597
theorem B3559889 : Blo 1248442 3559889 := bstep (se 2 (by rfl) ⟨1334958, by rfl⟩ : syracuseStep 3559889 = 2669917) B2669917
theorem B1249747 : Blo 1248442 1249747 := bstep (se 1 (by rfl) ⟨937310, by rfl⟩ : syracuseStep 1249747 = 1874621) B1874621
theorem B1249763 : Blo 1248442 1249763 := bstep (se 1 (by rfl) ⟨937322, by rfl⟩ : syracuseStep 1249763 = 1874645) B1874645
theorem B1249779 : Blo 1248442 1249779 := bstep (se 1 (by rfl) ⟨937334, by rfl⟩ : syracuseStep 1249779 = 1874669) B1874669
theorem B1249795 : Blo 1248442 1249795 := bstep (se 1 (by rfl) ⟨937346, by rfl⟩ : syracuseStep 1249795 = 1874693) B1874693
theorem B2109955 : Blo 1248442 2109955 := bstep (se 1 (by rfl) ⟨1582466, by rfl⟩ : syracuseStep 2109955 = 3164933) B3164933
theorem B8999437 : Blo 1248442 8999437 := bstep (se 3 (by rfl) ⟨1687394, by rfl⟩ : syracuseStep 8999437 = 3374789) B3374789
theorem B1249811 : Blo 1248442 1249811 := bstep (se 1 (by rfl) ⟨937358, by rfl⟩ : syracuseStep 1249811 = 1874717) B1874717
theorem B1249827 : Blo 1248442 1249827 := bstep (se 1 (by rfl) ⟨937370, by rfl⟩ : syracuseStep 1249827 = 1874741) B1874741
theorem B1249843 : Blo 1248442 1249843 := bstep (se 1 (by rfl) ⟨937382, by rfl⟩ : syracuseStep 1249843 = 1874765) B1874765
theorem B1405507 : Blo 1248442 1405507 := bstep (se 1 (by rfl) ⟨1054130, by rfl⟩ : syracuseStep 1405507 = 2108261) B2108261
theorem B1249859 : Blo 1248442 1249859 := bstep (se 1 (by rfl) ⟨937394, by rfl⟩ : syracuseStep 1249859 = 1874789) B1874789
theorem B1249875 : Blo 1248442 1249875 := bstep (se 1 (by rfl) ⟨937406, by rfl⟩ : syracuseStep 1249875 = 1874813) B1874813
theorem B2667107 : Blo 1248442 2667107 := bstep (se 1 (by rfl) ⟨2000330, by rfl⟩ : syracuseStep 2667107 = 4000661) B4000661
theorem B1249891 : Blo 1248442 1249891 := bstep (se 1 (by rfl) ⟨937418, by rfl⟩ : syracuseStep 1249891 = 1874837) B1874837
theorem B6320753 : Blo 1248442 6320753 := bstep (se 2 (by rfl) ⟨2370282, by rfl⟩ : syracuseStep 6320753 = 4740565) B4740565
theorem B1249907 : Blo 1248442 1249907 := bstep (se 1 (by rfl) ⟨937430, by rfl⟩ : syracuseStep 1249907 = 1874861) B1874861
theorem B1249923 : Blo 1248442 1249923 := bstep (se 1 (by rfl) ⟨937442, by rfl⟩ : syracuseStep 1249923 = 1874885) B1874885
theorem B16011917 : Blo 1248442 16011917 := bstep (se 3 (by rfl) ⟨3002234, by rfl⟩ : syracuseStep 16011917 = 6004469) B6004469
theorem B2110097 : Blo 1248442 2110097 := bstep (se 2 (by rfl) ⟨791286, by rfl⟩ : syracuseStep 2110097 = 1582573) B1582573
theorem B1249939 : Blo 1248442 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B1249955 : Blo 1248442 1249955 := bstep (se 1 (by rfl) ⟨937466, by rfl⟩ : syracuseStep 1249955 = 1874933) B1874933
theorem B1249971 : Blo 1248442 1249971 := bstep (se 1 (by rfl) ⟨937478, by rfl⟩ : syracuseStep 1249971 = 1874957) B1874957
theorem B1249987 : Blo 1248442 1249987 := bstep (se 1 (by rfl) ⟨937490, by rfl⟩ : syracuseStep 1249987 = 1874981) B1874981
theorem B1405651 : Blo 1248442 1405651 := bstep (se 1 (by rfl) ⟨1054238, by rfl⟩ : syracuseStep 1405651 = 2108477) B2108477
theorem B1250003 : Blo 1248442 1250003 := bstep (se 1 (by rfl) ⟨937502, by rfl⟩ : syracuseStep 1250003 = 1875005) B1875005
theorem B1250019 : Blo 1248442 1250019 := bstep (se 1 (by rfl) ⟨937514, by rfl⟩ : syracuseStep 1250019 = 1875029) B1875029
theorem B1250035 : Blo 1248442 1250035 := bstep (se 1 (by rfl) ⟨937526, by rfl⟩ : syracuseStep 1250035 = 1875053) B1875053
theorem B1250051 : Blo 1248442 1250051 := bstep (se 1 (by rfl) ⟨937538, by rfl⟩ : syracuseStep 1250051 = 1875077) B1875077
theorem B1250067 : Blo 1248442 1250067 := bstep (se 1 (by rfl) ⟨937550, by rfl⟩ : syracuseStep 1250067 = 1875101) B1875101
theorem B1250083 : Blo 1248442 1250083 := bstep (se 1 (by rfl) ⟨937562, by rfl⟩ : syracuseStep 1250083 = 1875125) B1875125
theorem B1872689 : Blo 1248442 1872689 := bstep (se 2 (by rfl) ⟨702258, by rfl⟩ : syracuseStep 1872689 = 1404517) B1404517
theorem B1250099 : Blo 1248442 1250099 := bstep (se 1 (by rfl) ⟨937574, by rfl⟩ : syracuseStep 1250099 = 1875149) B1875149
theorem B1872707 : Blo 1248442 1872707 := bstep (se 1 (by rfl) ⟨1404530, by rfl⟩ : syracuseStep 1872707 = 2809061) B2809061
theorem B1250115 : Blo 1248442 1250115 := bstep (se 1 (by rfl) ⟨937586, by rfl⟩ : syracuseStep 1250115 = 1875173) B1875173
theorem B1250131 : Blo 1248442 1250131 := bstep (se 1 (by rfl) ⟨937598, by rfl⟩ : syracuseStep 1250131 = 1875197) B1875197
theorem B1872737 : Blo 1248442 1872737 := bstep (se 2 (by rfl) ⟨702276, by rfl⟩ : syracuseStep 1872737 = 1404553) B1404553
theorem B1405795 : Blo 1248442 1405795 := bstep (se 1 (by rfl) ⟨1054346, by rfl⟩ : syracuseStep 1405795 = 2108693) B2108693
theorem B1250147 : Blo 1248442 1250147 := bstep (se 1 (by rfl) ⟨937610, by rfl⟩ : syracuseStep 1250147 = 1875221) B1875221
theorem B7115633 : Blo 1248442 7115633 := bstep (se 2 (by rfl) ⟨2668362, by rfl⟩ : syracuseStep 7115633 = 5336725) B5336725
theorem B1872755 : Blo 1248442 1872755 := bstep (se 1 (by rfl) ⟨1404566, by rfl⟩ : syracuseStep 1872755 = 2809133) B2809133
theorem B1250163 : Blo 1248442 1250163 := bstep (se 1 (by rfl) ⟨937622, by rfl⟩ : syracuseStep 1250163 = 1875245) B1875245
theorem B1250179 : Blo 1248442 1250179 := bstep (se 1 (by rfl) ⟨937634, by rfl⟩ : syracuseStep 1250179 = 1875269) B1875269
theorem B1872785 : Blo 1248442 1872785 := bstep (se 2 (by rfl) ⟨702294, by rfl⟩ : syracuseStep 1872785 = 1404589) B1404589
theorem B1250195 : Blo 1248442 1250195 := bstep (se 1 (by rfl) ⟨937646, by rfl⟩ : syracuseStep 1250195 = 1875293) B1875293
theorem B1872803 : Blo 1248442 1872803 := bstep (se 1 (by rfl) ⟨1404602, by rfl⟩ : syracuseStep 1872803 = 2809205) B2809205
theorem B1250211 : Blo 1248442 1250211 := bstep (se 1 (by rfl) ⟨937658, by rfl⟩ : syracuseStep 1250211 = 1875317) B1875317
theorem B4215725 : Blo 1248442 4215725 := bstep (se 3 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 4215725 = 1580897) B1580897
theorem B1250227 : Blo 1248442 1250227 := bstep (se 1 (by rfl) ⟨937670, by rfl⟩ : syracuseStep 1250227 = 1875341) B1875341
theorem B1872833 : Blo 1248442 1872833 := bstep (se 2 (by rfl) ⟨702312, by rfl⟩ : syracuseStep 1872833 = 1404625) B1404625
theorem B1250243 : Blo 1248442 1250243 := bstep (se 1 (by rfl) ⟨937682, by rfl⟩ : syracuseStep 1250243 = 1875365) B1875365
theorem B2372561 : Blo 1248442 2372561 := bstep (se 2 (by rfl) ⟨889710, by rfl⟩ : syracuseStep 2372561 = 1779421) B1779421
theorem B1872851 : Blo 1248442 1872851 := bstep (se 1 (by rfl) ⟨1404638, by rfl⟩ : syracuseStep 1872851 = 2809277) B2809277
theorem B1250259 : Blo 1248442 1250259 := bstep (se 1 (by rfl) ⟨937694, by rfl⟩ : syracuseStep 1250259 = 1875389) B1875389
theorem B4215779 : Blo 1248442 4215779 := bstep (se 1 (by rfl) ⟨3161834, by rfl⟩ : syracuseStep 4215779 = 6323669) B6323669
theorem B1250275 : Blo 1248442 1250275 := bstep (se 1 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 1250275 = 1875413) B1875413
theorem B1872881 : Blo 1248442 1872881 := bstep (se 2 (by rfl) ⟨702330, by rfl⟩ : syracuseStep 1872881 = 1404661) B1404661
theorem B1405939 : Blo 1248442 1405939 := bstep (se 1 (by rfl) ⟨1054454, by rfl⟩ : syracuseStep 1405939 = 2108909) B2108909
theorem B1250291 : Blo 1248442 1250291 := bstep (se 1 (by rfl) ⟨937718, by rfl⟩ : syracuseStep 1250291 = 1875437) B1875437
theorem B1872899 : Blo 1248442 1872899 := bstep (se 1 (by rfl) ⟨1404674, by rfl⟩ : syracuseStep 1872899 = 2809349) B2809349
theorem B1250307 : Blo 1248442 1250307 := bstep (se 1 (by rfl) ⟨937730, by rfl⟩ : syracuseStep 1250307 = 1875461) B1875461
theorem B8000525 : Blo 1248442 8000525 := bstep (se 3 (by rfl) ⟨1500098, by rfl⟩ : syracuseStep 8000525 = 3000197) B3000197
theorem B1250323 : Blo 1248442 1250323 := bstep (se 1 (by rfl) ⟨937742, by rfl⟩ : syracuseStep 1250323 = 1875485) B1875485
theorem B1872929 : Blo 1248442 1872929 := bstep (se 2 (by rfl) ⟨702348, by rfl⟩ : syracuseStep 1872929 = 1404697) B1404697
theorem B1250339 : Blo 1248442 1250339 := bstep (se 1 (by rfl) ⟨937754, by rfl⟩ : syracuseStep 1250339 = 1875509) B1875509
theorem B1872947 : Blo 1248442 1872947 := bstep (se 1 (by rfl) ⟨1404710, by rfl⟩ : syracuseStep 1872947 = 2809421) B2809421
theorem B1250355 : Blo 1248442 1250355 := bstep (se 1 (by rfl) ⟨937766, by rfl⟩ : syracuseStep 1250355 = 1875533) B1875533
theorem B1250371 : Blo 1248442 1250371 := bstep (se 1 (by rfl) ⟨937778, by rfl⟩ : syracuseStep 1250371 = 1875557) B1875557
theorem B1872977 : Blo 1248442 1872977 := bstep (se 2 (by rfl) ⟨702366, by rfl⟩ : syracuseStep 1872977 = 1404733) B1404733
theorem B1250387 : Blo 1248442 1250387 := bstep (se 1 (by rfl) ⟨937790, by rfl⟩ : syracuseStep 1250387 = 1875581) B1875581
theorem B1872995 : Blo 1248442 1872995 := bstep (se 1 (by rfl) ⟨1404746, by rfl⟩ : syracuseStep 1872995 = 2809493) B2809493
theorem B1250403 : Blo 1248442 1250403 := bstep (se 1 (by rfl) ⟨937802, by rfl⟩ : syracuseStep 1250403 = 1875605) B1875605
theorem B7599217 : Blo 1248442 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B4002929 : Blo 1248442 4002929 := bstep (se 2 (by rfl) ⟨1501098, by rfl⟩ : syracuseStep 4002929 = 3002197) B3002197
theorem B1250419 : Blo 1248442 1250419 := bstep (se 1 (by rfl) ⟨937814, by rfl⟩ : syracuseStep 1250419 = 1875629) B1875629
theorem B1873025 : Blo 1248442 1873025 := bstep (se 2 (by rfl) ⟨702384, by rfl⟩ : syracuseStep 1873025 = 1404769) B1404769
theorem B1406083 : Blo 1248442 1406083 := bstep (se 1 (by rfl) ⟨1054562, by rfl⟩ : syracuseStep 1406083 = 2109125) B2109125
theorem B1250435 : Blo 1248442 1250435 := bstep (se 1 (by rfl) ⟨937826, by rfl⟩ : syracuseStep 1250435 = 1875653) B1875653
theorem B1873043 : Blo 1248442 1873043 := bstep (se 1 (by rfl) ⟨1404782, by rfl⟩ : syracuseStep 1873043 = 2809565) B2809565
theorem B1873073 : Blo 1248442 1873073 := bstep (se 2 (by rfl) ⟨702402, by rfl⟩ : syracuseStep 1873073 = 1404805) B1404805
theorem B1873091 : Blo 1248442 1873091 := bstep (se 1 (by rfl) ⟨1404818, by rfl⟩ : syracuseStep 1873091 = 2809637) B2809637
theorem B4273357 : Blo 1248442 4273357 := bstep (se 3 (by rfl) ⟨801254, by rfl⟩ : syracuseStep 4273357 = 1602509) B1602509
theorem B1873121 : Blo 1248442 1873121 := bstep (se 2 (by rfl) ⟨702420, by rfl⟩ : syracuseStep 1873121 = 1404841) B1404841
theorem B8008931 : Blo 1248442 8008931 := bstep (se 1 (by rfl) ⟨6006698, by rfl⟩ : syracuseStep 8008931 = 12013397) B12013397
theorem B4216049 : Blo 1248442 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B1873139 : Blo 1248442 1873139 := bstep (se 1 (by rfl) ⟨1404854, by rfl⟩ : syracuseStep 1873139 = 2809709) B2809709
theorem B1873169 : Blo 1248442 1873169 := bstep (se 2 (by rfl) ⟨702438, by rfl⟩ : syracuseStep 1873169 = 1404877) B1404877
theorem B1406227 : Blo 1248442 1406227 := bstep (se 1 (by rfl) ⟨1054670, by rfl⟩ : syracuseStep 1406227 = 2109341) B2109341
theorem B1873187 : Blo 1248442 1873187 := bstep (se 1 (by rfl) ⟨1404890, by rfl⟩ : syracuseStep 1873187 = 2809781) B2809781
theorem B4003121 : Blo 1248442 4003121 := bstep (se 2 (by rfl) ⟨1501170, by rfl⟩ : syracuseStep 4003121 = 3002341) B3002341
theorem B1873217 : Blo 1248442 1873217 := bstep (se 2 (by rfl) ⟨702456, by rfl⟩ : syracuseStep 1873217 = 1404913) B1404913
theorem B1873235 : Blo 1248442 1873235 := bstep (se 1 (by rfl) ⟨1404926, by rfl⟩ : syracuseStep 1873235 = 2809853) B2809853
theorem B2282851 : Blo 1248442 2282851 := bstep (se 1 (by rfl) ⟨1712138, by rfl⟩ : syracuseStep 2282851 = 3424277) B3424277
theorem B1873265 : Blo 1248442 1873265 := bstep (se 2 (by rfl) ⟨702474, by rfl⟩ : syracuseStep 1873265 = 1404949) B1404949
theorem B1873283 : Blo 1248442 1873283 := bstep (se 1 (by rfl) ⟨1404962, by rfl⟩ : syracuseStep 1873283 = 2809925) B2809925
theorem B1873313 : Blo 1248442 1873313 := bstep (se 2 (by rfl) ⟨702492, by rfl⟩ : syracuseStep 1873313 = 1404985) B1404985
theorem B1406371 : Blo 1248442 1406371 := bstep (se 1 (by rfl) ⟨1054778, by rfl⟩ : syracuseStep 1406371 = 2109557) B2109557
theorem B2667953 : Blo 1248442 2667953 := bstep (se 2 (by rfl) ⟨1000482, by rfl⟩ : syracuseStep 2667953 = 2000965) B2000965
theorem B1873331 : Blo 1248442 1873331 := bstep (se 1 (by rfl) ⟨1404998, by rfl⟩ : syracuseStep 1873331 = 2809997) B2809997
theorem B1873361 : Blo 1248442 1873361 := bstep (se 2 (by rfl) ⟨702510, by rfl⟩ : syracuseStep 1873361 = 1405021) B1405021
theorem B1873379 : Blo 1248442 1873379 := bstep (se 1 (by rfl) ⟨1405034, by rfl⟩ : syracuseStep 1873379 = 2810069) B2810069
theorem B1873409 : Blo 1248442 1873409 := bstep (se 2 (by rfl) ⟨702528, by rfl⟩ : syracuseStep 1873409 = 1405057) B1405057
theorem B1873427 : Blo 1248442 1873427 := bstep (se 1 (by rfl) ⟨1405070, by rfl⟩ : syracuseStep 1873427 = 2810141) B2810141
theorem B1873457 : Blo 1248442 1873457 := bstep (se 2 (by rfl) ⟨702546, by rfl⟩ : syracuseStep 1873457 = 1405093) B1405093
theorem B5338673 : Blo 1248442 5338673 := bstep (se 2 (by rfl) ⟨2002002, by rfl⟩ : syracuseStep 5338673 = 4004005) B4004005
theorem B1406515 : Blo 1248442 1406515 := bstep (se 1 (by rfl) ⟨1054886, by rfl⟩ : syracuseStep 1406515 = 2109773) B2109773
theorem B1873475 : Blo 1248442 1873475 := bstep (se 1 (by rfl) ⟨1405106, by rfl⟩ : syracuseStep 1873475 = 2810213) B2810213
theorem B1873505 : Blo 1248442 1873505 := bstep (se 2 (by rfl) ⟨702564, by rfl⟩ : syracuseStep 1873505 = 1405129) B1405129
theorem B1873523 : Blo 1248442 1873523 := bstep (se 1 (by rfl) ⟨1405142, by rfl⟩ : syracuseStep 1873523 = 2810285) B2810285
theorem B1873553 : Blo 1248442 1873553 := bstep (se 2 (by rfl) ⟨702582, by rfl⟩ : syracuseStep 1873553 = 1405165) B1405165
theorem B1873571 : Blo 1248442 1873571 := bstep (se 1 (by rfl) ⟨1405178, by rfl⟩ : syracuseStep 1873571 = 2810357) B2810357
theorem B1873601 : Blo 1248442 1873601 := bstep (se 2 (by rfl) ⟨702600, by rfl⟩ : syracuseStep 1873601 = 1405201) B1405201
theorem B1406659 : Blo 1248442 1406659 := bstep (se 1 (by rfl) ⟨1054994, by rfl⟩ : syracuseStep 1406659 = 2109989) B2109989
theorem B1873619 : Blo 1248442 1873619 := bstep (se 1 (by rfl) ⟨1405214, by rfl⟩ : syracuseStep 1873619 = 2810429) B2810429
theorem B1873649 : Blo 1248442 1873649 := bstep (se 2 (by rfl) ⟨702618, by rfl⟩ : syracuseStep 1873649 = 1405237) B1405237
theorem B1873667 : Blo 1248442 1873667 := bstep (se 1 (by rfl) ⟨1405250, by rfl⟩ : syracuseStep 1873667 = 2810501) B2810501
theorem B4216589 : Blo 1248442 4216589 := bstep (se 3 (by rfl) ⟨790610, by rfl⟩ : syracuseStep 4216589 = 1581221) B1581221
theorem B1873697 : Blo 1248442 1873697 := bstep (se 2 (by rfl) ⟨702636, by rfl⟩ : syracuseStep 1873697 = 1405273) B1405273
theorem B1873715 : Blo 1248442 1873715 := bstep (se 1 (by rfl) ⟨1405286, by rfl⟩ : syracuseStep 1873715 = 2810573) B2810573
theorem B4216643 : Blo 1248442 4216643 := bstep (se 1 (by rfl) ⟨3162482, by rfl⟩ : syracuseStep 4216643 = 6324965) B6324965
theorem B1873745 : Blo 1248442 1873745 := bstep (se 2 (by rfl) ⟨702654, by rfl⟩ : syracuseStep 1873745 = 1405309) B1405309
theorem B2373457 : Blo 1248442 2373457 := bstep (se 2 (by rfl) ⟨890046, by rfl⟩ : syracuseStep 2373457 = 1780093) B1780093
theorem B6002531 : Blo 1248442 6002531 := bstep (se 1 (by rfl) ⟨4501898, by rfl⟩ : syracuseStep 6002531 = 9003797) B9003797
theorem B1873763 : Blo 1248442 1873763 := bstep (se 1 (by rfl) ⟨1405322, by rfl⟩ : syracuseStep 1873763 = 2810645) B2810645
theorem B1873793 : Blo 1248442 1873793 := bstep (se 2 (by rfl) ⟨702672, by rfl⟩ : syracuseStep 1873793 = 1405345) B1405345
theorem B10672013 : Blo 1248442 10672013 := bstep (se 3 (by rfl) ⟨2001002, by rfl⟩ : syracuseStep 10672013 = 4002005) B4002005
theorem B1873811 : Blo 1248442 1873811 := bstep (se 1 (by rfl) ⟨1405358, by rfl⟩ : syracuseStep 1873811 = 2810717) B2810717
theorem B1898417 : Blo 1248442 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B1873841 : Blo 1248442 1873841 := bstep (se 2 (by rfl) ⟨702690, by rfl⟩ : syracuseStep 1873841 = 1405381) B1405381
theorem B1873859 : Blo 1248442 1873859 := bstep (se 1 (by rfl) ⟨1405394, by rfl⟩ : syracuseStep 1873859 = 2810789) B2810789
theorem B1873889 : Blo 1248442 1873889 := bstep (se 2 (by rfl) ⟨702708, by rfl⟩ : syracuseStep 1873889 = 1405417) B1405417
theorem B2373617 : Blo 1248442 2373617 := bstep (se 2 (by rfl) ⟨890106, by rfl⟩ : syracuseStep 2373617 = 1780213) B1780213
theorem B1873907 : Blo 1248442 1873907 := bstep (se 1 (by rfl) ⟨1405430, by rfl⟩ : syracuseStep 1873907 = 2810861) B2810861
theorem B1873937 : Blo 1248442 1873937 := bstep (se 2 (by rfl) ⟨702726, by rfl⟩ : syracuseStep 1873937 = 1405453) B1405453
theorem B6322211 : Blo 1248442 6322211 := bstep (se 1 (by rfl) ⟨4741658, by rfl⟩ : syracuseStep 6322211 = 9483317) B9483317
theorem B1873955 : Blo 1248442 1873955 := bstep (se 1 (by rfl) ⟨1405466, by rfl⟩ : syracuseStep 1873955 = 2810933) B2810933
theorem B5068835 : Blo 1248442 5068835 := bstep (se 1 (by rfl) ⟨3801626, by rfl⟩ : syracuseStep 5068835 = 7603253) B7603253
theorem B1873985 : Blo 1248442 1873985 := bstep (se 2 (by rfl) ⟨702744, by rfl⟩ : syracuseStep 1873985 = 1405489) B1405489
theorem B2250833 : Blo 1248442 2250833 := bstep (se 2 (by rfl) ⟨844062, by rfl⟩ : syracuseStep 2250833 = 1688125) B1688125
theorem B4216913 : Blo 1248442 4216913 := bstep (se 2 (by rfl) ⟨1581342, by rfl⟩ : syracuseStep 4216913 = 3162685) B3162685
theorem B1874003 : Blo 1248442 1874003 := bstep (se 1 (by rfl) ⟨1405502, by rfl⟩ : syracuseStep 1874003 = 2811005) B2811005
theorem B1874033 : Blo 1248442 1874033 := bstep (se 2 (by rfl) ⟨702762, by rfl⟩ : syracuseStep 1874033 = 1405525) B1405525
theorem B1874051 : Blo 1248442 1874051 := bstep (se 1 (by rfl) ⟨1405538, by rfl⟩ : syracuseStep 1874051 = 2811077) B2811077
theorem B1874081 : Blo 1248442 1874081 := bstep (se 2 (by rfl) ⟨702780, by rfl⟩ : syracuseStep 1874081 = 1405561) B1405561
theorem B1874099 : Blo 1248442 1874099 := bstep (se 1 (by rfl) ⟨1405574, by rfl⟩ : syracuseStep 1874099 = 2811149) B2811149
theorem B4741325 : Blo 1248442 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B1874129 : Blo 1248442 1874129 := bstep (se 2 (by rfl) ⟨702798, by rfl⟩ : syracuseStep 1874129 = 1405597) B1405597
theorem B1874147 : Blo 1248442 1874147 := bstep (se 1 (by rfl) ⟨1405610, by rfl⟩ : syracuseStep 1874147 = 2811221) B2811221
theorem B12015857 : Blo 1248442 12015857 := bstep (se 2 (by rfl) ⟨4505946, by rfl⟩ : syracuseStep 12015857 = 9011893) B9011893
theorem B1874177 : Blo 1248442 1874177 := bstep (se 2 (by rfl) ⟨702816, by rfl⟩ : syracuseStep 1874177 = 1405633) B1405633
theorem B1874195 : Blo 1248442 1874195 := bstep (se 1 (by rfl) ⟨1405646, by rfl⟩ : syracuseStep 1874195 = 2811293) B2811293
theorem B7117091 : Blo 1248442 7117091 := bstep (se 1 (by rfl) ⟨5337818, by rfl⟩ : syracuseStep 7117091 = 10675637) B10675637
theorem B1874225 : Blo 1248442 1874225 := bstep (se 2 (by rfl) ⟨702834, by rfl⟩ : syracuseStep 1874225 = 1405669) B1405669
theorem B1423667 : Blo 1248442 1423667 := bstep (se 1 (by rfl) ⟨1067750, by rfl⟩ : syracuseStep 1423667 = 2135501) B2135501
theorem B1874243 : Blo 1248442 1874243 := bstep (se 1 (by rfl) ⟨1405682, by rfl⟩ : syracuseStep 1874243 = 2811365) B2811365
theorem B1874273 : Blo 1248442 1874273 := bstep (se 2 (by rfl) ⟨702852, by rfl⟩ : syracuseStep 1874273 = 1405705) B1405705
theorem B1874291 : Blo 1248442 1874291 := bstep (se 1 (by rfl) ⟨1405718, by rfl⟩ : syracuseStep 1874291 = 2811437) B2811437
theorem B1874321 : Blo 1248442 1874321 := bstep (se 2 (by rfl) ⟨702870, by rfl⟩ : syracuseStep 1874321 = 1405741) B1405741
theorem B1874339 : Blo 1248442 1874339 := bstep (se 1 (by rfl) ⟨1405754, by rfl⟩ : syracuseStep 1874339 = 2811509) B2811509
theorem B8010161 : Blo 1248442 8010161 := bstep (se 2 (by rfl) ⟨3003810, by rfl⟩ : syracuseStep 8010161 = 6007621) B6007621
theorem B1874369 : Blo 1248442 1874369 := bstep (se 2 (by rfl) ⟨702888, by rfl⟩ : syracuseStep 1874369 = 1405777) B1405777
theorem B3160529 : Blo 1248442 3160529 := bstep (se 2 (by rfl) ⟨1185198, by rfl⟩ : syracuseStep 3160529 = 2370397) B2370397
theorem B1874387 : Blo 1248442 1874387 := bstep (se 1 (by rfl) ⟨1405790, by rfl⟩ : syracuseStep 1874387 = 2811581) B2811581
theorem B9624035 : Blo 1248442 9624035 := bstep (se 1 (by rfl) ⟨7218026, by rfl⟩ : syracuseStep 9624035 = 14436053) B14436053
theorem B1874417 : Blo 1248442 1874417 := bstep (se 2 (by rfl) ⟨702906, by rfl⟩ : syracuseStep 1874417 = 1405813) B1405813
theorem B3160579 : Blo 1248442 3160579 := bstep (se 1 (by rfl) ⟨2370434, by rfl⟩ : syracuseStep 3160579 = 4740869) B4740869
theorem B1874435 : Blo 1248442 1874435 := bstep (se 1 (by rfl) ⟨1405826, by rfl⟩ : syracuseStep 1874435 = 2811653) B2811653
theorem B1874465 : Blo 1248442 1874465 := bstep (se 2 (by rfl) ⟨702924, by rfl⟩ : syracuseStep 1874465 = 1405849) B1405849
theorem B1874483 : Blo 1248442 1874483 := bstep (se 1 (by rfl) ⟨1405862, by rfl⟩ : syracuseStep 1874483 = 2811725) B2811725
theorem B2251331 : Blo 1248442 2251331 := bstep (se 1 (by rfl) ⟨1688498, by rfl⟩ : syracuseStep 2251331 = 3376997) B3376997
theorem B1874513 : Blo 1248442 1874513 := bstep (se 2 (by rfl) ⟨702942, by rfl⟩ : syracuseStep 1874513 = 1405885) B1405885
theorem B1874531 : Blo 1248442 1874531 := bstep (se 1 (by rfl) ⟨1405898, by rfl⟩ : syracuseStep 1874531 = 2811797) B2811797
theorem B4217453 : Blo 1248442 4217453 := bstep (se 3 (by rfl) ⟨790772, by rfl⟩ : syracuseStep 4217453 = 1581545) B1581545
theorem B1874561 : Blo 1248442 1874561 := bstep (se 2 (by rfl) ⟨702960, by rfl⟩ : syracuseStep 1874561 = 1405921) B1405921
theorem B3160721 : Blo 1248442 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B1874579 : Blo 1248442 1874579 := bstep (se 1 (by rfl) ⟨1405934, by rfl⟩ : syracuseStep 1874579 = 2811869) B2811869
theorem B4217507 : Blo 1248442 4217507 := bstep (se 1 (by rfl) ⟨3163130, by rfl⟩ : syracuseStep 4217507 = 6326261) B6326261
theorem B1874609 : Blo 1248442 1874609 := bstep (se 2 (by rfl) ⟨702978, by rfl⟩ : syracuseStep 1874609 = 1405957) B1405957
theorem B1874627 : Blo 1248442 1874627 := bstep (se 1 (by rfl) ⟨1405970, by rfl⟩ : syracuseStep 1874627 = 2811941) B2811941
theorem B1874657 : Blo 1248442 1874657 := bstep (se 2 (by rfl) ⟨702996, by rfl⟩ : syracuseStep 1874657 = 1405993) B1405993
theorem B1874675 : Blo 1248442 1874675 := bstep (se 1 (by rfl) ⟨1406006, by rfl⟩ : syracuseStep 1874675 = 2812013) B2812013
theorem B1874705 : Blo 1248442 1874705 := bstep (se 2 (by rfl) ⟨703014, by rfl⟩ : syracuseStep 1874705 = 1406029) B1406029
theorem B1874723 : Blo 1248442 1874723 := bstep (se 1 (by rfl) ⟨1406042, by rfl⟩ : syracuseStep 1874723 = 2812085) B2812085
theorem B1874753 : Blo 1248442 1874753 := bstep (se 2 (by rfl) ⟨703032, by rfl⟩ : syracuseStep 1874753 = 1406065) B1406065
theorem B6323021 : Blo 1248442 6323021 := bstep (se 3 (by rfl) ⟨1185566, by rfl⟩ : syracuseStep 6323021 = 2371133) B2371133
theorem B1874771 : Blo 1248442 1874771 := bstep (se 1 (by rfl) ⟨1406078, by rfl⟩ : syracuseStep 1874771 = 2812157) B2812157
theorem B1874801 : Blo 1248442 1874801 := bstep (se 2 (by rfl) ⟨703050, by rfl⟩ : syracuseStep 1874801 = 1406101) B1406101
theorem B1874819 : Blo 1248442 1874819 := bstep (se 1 (by rfl) ⟨1406114, by rfl⟩ : syracuseStep 1874819 = 2812229) B2812229
theorem B1874849 : Blo 1248442 1874849 := bstep (se 2 (by rfl) ⟨703068, by rfl⟩ : syracuseStep 1874849 = 1406137) B1406137
theorem B4217777 : Blo 1248442 4217777 := bstep (se 2 (by rfl) ⟨1581666, by rfl⟩ : syracuseStep 4217777 = 3163333) B3163333
theorem B1874867 : Blo 1248442 1874867 := bstep (se 1 (by rfl) ⟨1406150, by rfl⟩ : syracuseStep 1874867 = 2812301) B2812301
theorem B1424323 : Blo 1248442 1424323 := bstep (se 1 (by rfl) ⟨1068242, by rfl⟩ : syracuseStep 1424323 = 2136485) B2136485
theorem B6167501 : Blo 1248442 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B1874897 : Blo 1248442 1874897 := bstep (se 2 (by rfl) ⟨703086, by rfl⟩ : syracuseStep 1874897 = 1406173) B1406173
theorem B1874915 : Blo 1248442 1874915 := bstep (se 1 (by rfl) ⟨1406186, by rfl⟩ : syracuseStep 1874915 = 2812373) B2812373
theorem B1874945 : Blo 1248442 1874945 := bstep (se 2 (by rfl) ⟨703104, by rfl⟩ : syracuseStep 1874945 = 1406209) B1406209
theorem B1334275 : Blo 1248442 1334275 := bstep (se 1 (by rfl) ⟨1000706, by rfl⟩ : syracuseStep 1334275 = 2001413) B2001413
theorem B2251793 : Blo 1248442 2251793 := bstep (se 2 (by rfl) ⟨844422, by rfl⟩ : syracuseStep 2251793 = 1688845) B1688845
theorem B1874963 : Blo 1248442 1874963 := bstep (se 1 (by rfl) ⟨1406222, by rfl⟩ : syracuseStep 1874963 = 2812445) B2812445
theorem B1874993 : Blo 1248442 1874993 := bstep (se 2 (by rfl) ⟨703122, by rfl⟩ : syracuseStep 1874993 = 1406245) B1406245
theorem B5069873 : Blo 1248442 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B1875011 : Blo 1248442 1875011 := bstep (se 1 (by rfl) ⟨1406258, by rfl⟩ : syracuseStep 1875011 = 2812517) B2812517
theorem B5479501 : Blo 1248442 5479501 := bstep (se 3 (by rfl) ⟨1027406, by rfl⟩ : syracuseStep 5479501 = 2054813) B2054813
theorem B1875041 : Blo 1248442 1875041 := bstep (se 2 (by rfl) ⟨703140, by rfl⟩ : syracuseStep 1875041 = 1406281) B1406281
theorem B1875059 : Blo 1248442 1875059 := bstep (se 1 (by rfl) ⟨1406294, by rfl⟩ : syracuseStep 1875059 = 2812589) B2812589
theorem B14228621 : Blo 1248442 14228621 := bstep (se 3 (by rfl) ⟨2667866, by rfl⟩ : syracuseStep 14228621 = 5335733) B5335733
theorem B12016781 : Blo 1248442 12016781 := bstep (se 3 (by rfl) ⟨2253146, by rfl⟩ : syracuseStep 12016781 = 4506293) B4506293
theorem B1875089 : Blo 1248442 1875089 := bstep (se 2 (by rfl) ⟨703158, by rfl⟩ : syracuseStep 1875089 = 1406317) B1406317
theorem B1875107 : Blo 1248442 1875107 := bstep (se 1 (by rfl) ⟨1406330, by rfl⟩ : syracuseStep 1875107 = 2812661) B2812661
theorem B1875137 : Blo 1248442 1875137 := bstep (se 2 (by rfl) ⟨703176, by rfl⟩ : syracuseStep 1875137 = 1406353) B1406353
theorem B1875155 : Blo 1248442 1875155 := bstep (se 1 (by rfl) ⟨1406366, by rfl⟩ : syracuseStep 1875155 = 2812733) B2812733
theorem B1875185 : Blo 1248442 1875185 := bstep (se 2 (by rfl) ⟨703194, by rfl⟩ : syracuseStep 1875185 = 1406389) B1406389
theorem B1875203 : Blo 1248442 1875203 := bstep (se 1 (by rfl) ⟨1406402, by rfl⟩ : syracuseStep 1875203 = 2812805) B2812805
theorem B1875233 : Blo 1248442 1875233 := bstep (se 2 (by rfl) ⟨703212, by rfl⟩ : syracuseStep 1875233 = 1406425) B1406425
theorem B1875251 : Blo 1248442 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B4504909 : Blo 1248442 4504909 := bstep (se 3 (by rfl) ⟨844670, by rfl⟩ : syracuseStep 4504909 = 1689341) B1689341
theorem B2809169 : Blo 1248442 2809169 := bstep (se 2 (by rfl) ⟨1053438, by rfl⟩ : syracuseStep 2809169 = 2106877) B2106877
theorem B1875281 : Blo 1248442 1875281 := bstep (se 2 (by rfl) ⟨703230, by rfl⟩ : syracuseStep 1875281 = 1406461) B1406461
theorem B2809187 : Blo 1248442 2809187 := bstep (se 1 (by rfl) ⟨2106890, by rfl⟩ : syracuseStep 2809187 = 4213781) B4213781
theorem B1875299 : Blo 1248442 1875299 := bstep (se 1 (by rfl) ⟨1406474, by rfl⟩ : syracuseStep 1875299 = 2812949) B2812949
theorem B1875329 : Blo 1248442 1875329 := bstep (se 2 (by rfl) ⟨703248, by rfl⟩ : syracuseStep 1875329 = 1406497) B1406497
theorem B1875347 : Blo 1248442 1875347 := bstep (se 1 (by rfl) ⟨1406510, by rfl⟩ : syracuseStep 1875347 = 2813021) B2813021
theorem B1875377 : Blo 1248442 1875377 := bstep (se 2 (by rfl) ⟨703266, by rfl⟩ : syracuseStep 1875377 = 1406533) B1406533
theorem B1580467 : Blo 1248442 1580467 := bstep (se 1 (by rfl) ⟨1185350, by rfl⟩ : syracuseStep 1580467 = 2370701) B2370701
theorem B1875395 : Blo 1248442 1875395 := bstep (se 1 (by rfl) ⟨1406546, by rfl⟩ : syracuseStep 1875395 = 2813093) B2813093
theorem B4218317 : Blo 1248442 4218317 := bstep (se 3 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 4218317 = 1581869) B1581869
theorem B1875425 : Blo 1248442 1875425 := bstep (se 2 (by rfl) ⟨703284, by rfl⟩ : syracuseStep 1875425 = 1406569) B1406569
theorem B1875443 : Blo 1248442 1875443 := bstep (se 1 (by rfl) ⟨1406582, by rfl⟩ : syracuseStep 1875443 = 2813165) B2813165
theorem B4218371 : Blo 1248442 4218371 := bstep (se 1 (by rfl) ⟨3163778, by rfl⟩ : syracuseStep 4218371 = 6327557) B6327557
theorem B4005389 : Blo 1248442 4005389 := bstep (se 3 (by rfl) ⟨751010, by rfl⟩ : syracuseStep 4005389 = 1502021) B1502021
theorem B1875473 : Blo 1248442 1875473 := bstep (se 2 (by rfl) ⟨703302, by rfl⟩ : syracuseStep 1875473 = 1406605) B1406605
theorem B1580563 : Blo 1248442 1580563 := bstep (se 1 (by rfl) ⟨1185422, by rfl⟩ : syracuseStep 1580563 = 2370845) B2370845
theorem B1875491 : Blo 1248442 1875491 := bstep (se 1 (by rfl) ⟨1406618, by rfl⟩ : syracuseStep 1875491 = 2813237) B2813237
theorem B1875521 : Blo 1248442 1875521 := bstep (se 2 (by rfl) ⟨703320, by rfl⟩ : syracuseStep 1875521 = 1406641) B1406641
theorem B2252369 : Blo 1248442 2252369 := bstep (se 2 (by rfl) ⟨844638, by rfl⟩ : syracuseStep 2252369 = 1689277) B1689277
theorem B1875539 : Blo 1248442 1875539 := bstep (se 1 (by rfl) ⟨1406654, by rfl⟩ : syracuseStep 1875539 = 2813309) B2813309
theorem B12009059 : Blo 1248442 12009059 := bstep (se 1 (by rfl) ⟨9006794, by rfl⟩ : syracuseStep 12009059 = 18013589) B18013589
theorem B2809457 : Blo 1248442 2809457 := bstep (se 2 (by rfl) ⟨1053546, by rfl⟩ : syracuseStep 2809457 = 2107093) B2107093
theorem B3161713 : Blo 1248442 3161713 := bstep (se 2 (by rfl) ⟨1185642, by rfl⟩ : syracuseStep 3161713 = 2371285) B2371285
theorem B1875569 : Blo 1248442 1875569 := bstep (se 2 (by rfl) ⟨703338, by rfl⟩ : syracuseStep 1875569 = 1406677) B1406677
theorem B2809475 : Blo 1248442 2809475 := bstep (se 1 (by rfl) ⟨2107106, by rfl⟩ : syracuseStep 2809475 = 4214213) B4214213
theorem B1875587 : Blo 1248442 1875587 := bstep (se 1 (by rfl) ⟨1406690, by rfl⟩ : syracuseStep 1875587 = 2813381) B2813381
theorem B24002189 : Blo 1248442 24002189 := bstep (se 3 (by rfl) ⟨4500410, by rfl⟩ : syracuseStep 24002189 = 9000821) B9000821
theorem B2137745 : Blo 1248442 2137745 := bstep (se 2 (by rfl) ⟨801654, by rfl⟩ : syracuseStep 2137745 = 1603309) B1603309
theorem B1875617 : Blo 1248442 1875617 := bstep (se 2 (by rfl) ⟨703356, by rfl⟩ : syracuseStep 1875617 = 1406713) B1406713
theorem B3604141 : Blo 1248442 3604141 := bstep (se 3 (by rfl) ⟨675776, by rfl⟩ : syracuseStep 3604141 = 1351553) B1351553
theorem B1875635 : Blo 1248442 1875635 := bstep (se 1 (by rfl) ⟨1406726, by rfl⟩ : syracuseStep 1875635 = 2813453) B2813453
theorem B1900241 : Blo 1248442 1900241 := bstep (se 2 (by rfl) ⟨712590, by rfl⟩ : syracuseStep 1900241 = 1425181) B1425181
theorem B10133261 : Blo 1248442 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B4505357 : Blo 1248442 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B4218641 : Blo 1248442 4218641 := bstep (se 2 (by rfl) ⟨1581990, by rfl⟩ : syracuseStep 4218641 = 3163981) B3163981
theorem B1687331 : Blo 1248442 1687331 := bstep (se 1 (by rfl) ⟨1265498, by rfl⟩ : syracuseStep 1687331 = 2530997) B2530997
theorem B3161987 : Blo 1248442 3161987 := bstep (se 1 (by rfl) ⟨2371490, by rfl⟩ : syracuseStep 3161987 = 4742981) B4742981
theorem B2809745 : Blo 1248442 2809745 := bstep (se 2 (by rfl) ⟨1053654, by rfl⟩ : syracuseStep 2809745 = 2107309) B2107309
theorem B2809763 : Blo 1248442 2809763 := bstep (se 1 (by rfl) ⟨2107322, by rfl⟩ : syracuseStep 2809763 = 4214645) B4214645
theorem B5341133 : Blo 1248442 5341133 := bstep (se 3 (by rfl) ⟨1001462, by rfl⟩ : syracuseStep 5341133 = 2002925) B2002925
theorem B2809907 : Blo 1248442 2809907 := bstep (se 1 (by rfl) ⟨2107430, by rfl⟩ : syracuseStep 2809907 = 4214861) B4214861
theorem B2809943 : Blo 1248442 2809943 := bstep (se 1 (by rfl) ⟨2107457, by rfl⟩ : syracuseStep 2809943 = 4214915) B4214915
theorem B1900631 : Blo 1248442 1900631 := bstep (se 1 (by rfl) ⟨1425473, by rfl⟩ : syracuseStep 1900631 = 2850947) B2850947
theorem B6324317 : Blo 1248442 6324317 := bstep (se 3 (by rfl) ⟨1185809, by rfl⟩ : syracuseStep 6324317 = 2371619) B2371619
theorem B4743299 : Blo 1248442 4743299 := bstep (se 1 (by rfl) ⟨3557474, by rfl⟩ : syracuseStep 4743299 = 7114949) B7114949
theorem B3801239 : Blo 1248442 3801239 := bstep (se 1 (by rfl) ⟨2850929, by rfl⟩ : syracuseStep 3801239 = 5701859) B5701859
theorem B2703539 : Blo 1248442 2703539 := bstep (se 1 (by rfl) ⟨2027654, by rfl⟩ : syracuseStep 2703539 = 4055309) B4055309
theorem B4219073 : Blo 1248442 4219073 := bstep (se 2 (by rfl) ⟨1582152, by rfl⟩ : syracuseStep 4219073 = 3164305) B3164305
theorem B1351927 : Blo 1248442 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B2810123 : Blo 1248442 2810123 := bstep (se 1 (by rfl) ⟨2107592, by rfl⟩ : syracuseStep 2810123 = 4215185) B4215185
theorem B2810177 : Blo 1248442 2810177 := bstep (se 2 (by rfl) ⟨1053816, by rfl⟩ : syracuseStep 2810177 = 2107633) B2107633
theorem B5701963 : Blo 1248442 5701963 := bstep (se 1 (by rfl) ⟨4276472, by rfl⟩ : syracuseStep 5701963 = 8552945) B8552945
theorem B10674611 : Blo 1248442 10674611 := bstep (se 1 (by rfl) ⟨8005958, by rfl⟩ : syracuseStep 10674611 = 16011917) B16011917
theorem B2810393 : Blo 1248442 2810393 := bstep (se 2 (by rfl) ⟨1053897, by rfl⟩ : syracuseStep 2810393 = 2107795) B2107795
theorem B4743755 : Blo 1248442 4743755 := bstep (se 1 (by rfl) ⟨3557816, by rfl⟩ : syracuseStep 4743755 = 7115633) B7115633
theorem B21627485 : Blo 1248442 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B2810483 : Blo 1248442 2810483 := bstep (se 1 (by rfl) ⟨2107862, by rfl⟩ : syracuseStep 2810483 = 4215725) B4215725
theorem B1581707 : Blo 1248442 1581707 := bstep (se 1 (by rfl) ⟨1186280, by rfl⟩ : syracuseStep 1581707 = 2372561) B2372561
theorem B2810519 : Blo 1248442 2810519 := bstep (se 1 (by rfl) ⟨2107889, by rfl⟩ : syracuseStep 2810519 = 4215779) B4215779
theorem B5333683 : Blo 1248442 5333683 := bstep (se 1 (by rfl) ⟨4000262, by rfl⟩ : syracuseStep 5333683 = 8000525) B8000525
theorem B3162827 : Blo 1248442 3162827 := bstep (se 1 (by rfl) ⟨2372120, by rfl⟩ : syracuseStep 3162827 = 4744241) B4744241
theorem B4219613 : Blo 1248442 4219613 := bstep (se 3 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 4219613 = 1582355) B1582355
theorem B4743953 : Blo 1248442 4743953 := bstep (se 2 (by rfl) ⟨1778982, by rfl⟩ : syracuseStep 4743953 = 3557965) B3557965
theorem B10674989 : Blo 1248442 10674989 := bstep (se 3 (by rfl) ⟨2001560, by rfl⟩ : syracuseStep 10674989 = 4003121) B4003121
theorem B2810699 : Blo 1248442 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B9487205 : Blo 1248442 9487205 := bstep (se 4 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 9487205 = 1778851) B1778851
theorem B2810753 : Blo 1248442 2810753 := bstep (se 2 (by rfl) ⟨1054032, by rfl⟩ : syracuseStep 2810753 = 2108065) B2108065
theorem B2851777 : Blo 1248442 2851777 := bstep (se 2 (by rfl) ⟨1069416, by rfl⟩ : syracuseStep 2851777 = 2138833) B2138833
theorem B1778635 : Blo 1248442 1778635 := bstep (se 1 (by rfl) ⟨1333976, by rfl⟩ : syracuseStep 1778635 = 2667953) B2667953
theorem B2810969 : Blo 1248442 2810969 := bstep (se 2 (by rfl) ⟨1054113, by rfl⟩ : syracuseStep 2810969 = 2108227) B2108227
theorem B2811059 : Blo 1248442 2811059 := bstep (se 1 (by rfl) ⟨2108294, by rfl⟩ : syracuseStep 2811059 = 4216589) B4216589
theorem B1688779 : Blo 1248442 1688779 := bstep (se 1 (by rfl) ⟨1266584, by rfl⟩ : syracuseStep 1688779 = 2533169) B2533169
theorem B2811095 : Blo 1248442 2811095 := bstep (se 1 (by rfl) ⟨2108321, by rfl⟩ : syracuseStep 2811095 = 4216643) B4216643
theorem B22799681 : Blo 1248442 22799681 := bstep (se 2 (by rfl) ⟨8549880, by rfl⟩ : syracuseStep 22799681 = 17099761) B17099761
theorem B4810049 : Blo 1248442 4810049 := bstep (se 2 (by rfl) ⟨1803768, by rfl⟩ : syracuseStep 4810049 = 3607537) B3607537
theorem B9487691 : Blo 1248442 9487691 := bstep (se 1 (by rfl) ⟨7115768, by rfl⟩ : syracuseStep 9487691 = 14231537) B14231537
theorem B1582411 : Blo 1248442 1582411 := bstep (se 1 (by rfl) ⟨1186808, by rfl⟩ : syracuseStep 1582411 = 2373617) B2373617
theorem B5064067 : Blo 1248442 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B2811275 : Blo 1248442 2811275 := bstep (se 1 (by rfl) ⟨2108456, by rfl⟩ : syracuseStep 2811275 = 4216913) B4216913
theorem B2811329 : Blo 1248442 2811329 := bstep (se 2 (by rfl) ⟨1054248, by rfl⟩ : syracuseStep 2811329 = 2108497) B2108497
theorem B4744727 : Blo 1248442 4744727 := bstep (se 1 (by rfl) ⟨3558545, by rfl⟩ : syracuseStep 4744727 = 7117091) B7117091
theorem B7112285 : Blo 1248442 7112285 := bstep (se 3 (by rfl) ⟨1333553, by rfl⟩ : syracuseStep 7112285 = 2667107) B2667107
theorem B2107019 : Blo 1248442 2107019 := bstep (se 1 (by rfl) ⟨1580264, by rfl⟩ : syracuseStep 2107019 = 3160529) B3160529
theorem B3163799 : Blo 1248442 3163799 := bstep (se 1 (by rfl) ⟨2372849, by rfl⟩ : syracuseStep 3163799 = 4745699) B4745699
theorem B6416023 : Blo 1248442 6416023 := bstep (se 1 (by rfl) ⟨4812017, by rfl⟩ : syracuseStep 6416023 = 9624035) B9624035
theorem B2811545 : Blo 1248442 2811545 := bstep (se 2 (by rfl) ⟨1054329, by rfl⟩ : syracuseStep 2811545 = 2108659) B2108659
theorem B2999987 : Blo 1248442 2999987 := bstep (se 1 (by rfl) ⟨2249990, by rfl⟩ : syracuseStep 2999987 = 4499981) B4499981
theorem B1500887 : Blo 1248442 1500887 := bstep (se 1 (by rfl) ⟨1125665, by rfl⟩ : syracuseStep 1500887 = 2251331) B2251331
theorem B4744925 : Blo 1248442 4744925 := bstep (se 3 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 4744925 = 1779347) B1779347
theorem B2811635 : Blo 1248442 2811635 := bstep (se 1 (by rfl) ⟨2108726, by rfl⟩ : syracuseStep 2811635 = 4217453) B4217453
theorem B2107147 : Blo 1248442 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B6006545 : Blo 1248442 6006545 := bstep (se 2 (by rfl) ⟨2252454, by rfl⟩ : syracuseStep 6006545 = 4504909) B4504909
theorem B2811671 : Blo 1248442 2811671 := bstep (se 1 (by rfl) ⟨2108753, by rfl⟩ : syracuseStep 2811671 = 4217507) B4217507
theorem B2107289 : Blo 1248442 2107289 := bstep (se 2 (by rfl) ⟨790233, by rfl⟩ : syracuseStep 2107289 = 1580467) B1580467
theorem B2811851 : Blo 1248442 2811851 := bstep (se 1 (by rfl) ⟨2108888, by rfl⟩ : syracuseStep 2811851 = 4217777) B4217777
theorem B2811905 : Blo 1248442 2811905 := bstep (se 2 (by rfl) ⟨1054464, by rfl⟩ : syracuseStep 2811905 = 2108929) B2108929
theorem B1501195 : Blo 1248442 1501195 := bstep (se 1 (by rfl) ⟨1125896, by rfl⟩ : syracuseStep 1501195 = 2251793) B2251793
theorem B2107417 : Blo 1248442 2107417 := bstep (se 2 (by rfl) ⟨790281, by rfl⟩ : syracuseStep 2107417 = 1580563) B1580563
theorem B5335085 : Blo 1248442 5335085 := bstep (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) B2000657
theorem B11397185 : Blo 1248442 11397185 := bstep (se 2 (by rfl) ⟨4273944, by rfl⟩ : syracuseStep 11397185 = 8547889) B8547889
theorem B4499549 : Blo 1248442 4499549 := bstep (se 3 (by rfl) ⟨843665, by rfl⟩ : syracuseStep 4499549 = 1687331) B1687331
theorem B6326423 : Blo 1248442 6326423 := bstep (se 1 (by rfl) ⟨4744817, by rfl⟩ : syracuseStep 6326423 = 9489635) B9489635
theorem B20269237 : Blo 1248442 20269237 := bstep (se 5 (by rfl) ⟨950120, by rfl⟩ : syracuseStep 20269237 = 1900241) B1900241
theorem B2812121 : Blo 1248442 2812121 := bstep (se 2 (by rfl) ⟨1054545, by rfl⟩ : syracuseStep 2812121 = 2109091) B2109091
theorem B2812211 : Blo 1248442 2812211 := bstep (se 1 (by rfl) ⟨2109158, by rfl⟩ : syracuseStep 2812211 = 4218317) B4218317
theorem B3164467 : Blo 1248442 3164467 := bstep (se 1 (by rfl) ⟨2373350, by rfl⟩ : syracuseStep 3164467 = 4746701) B4746701
theorem B5409089 : Blo 1248442 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B7113035 : Blo 1248442 7113035 := bstep (se 1 (by rfl) ⟨5334776, by rfl⟩ : syracuseStep 7113035 = 10669553) B10669553
theorem B2812247 : Blo 1248442 2812247 := bstep (se 1 (by rfl) ⟨2109185, by rfl⟩ : syracuseStep 2812247 = 4218371) B4218371
theorem B7596389 : Blo 1248442 7596389 := bstep (se 4 (by rfl) ⟨712161, by rfl⟩ : syracuseStep 7596389 = 1424323) B1424323
theorem B1501579 : Blo 1248442 1501579 := bstep (se 1 (by rfl) ⟨1126184, by rfl⟩ : syracuseStep 1501579 = 2252369) B2252369
theorem B3557783 : Blo 1248442 3557783 := bstep (se 1 (by rfl) ⟨2668337, by rfl⟩ : syracuseStep 3557783 = 5336675) B5336675
theorem B8006039 : Blo 1248442 8006039 := bstep (se 1 (by rfl) ⟨6004529, by rfl⟩ : syracuseStep 8006039 = 12009059) B12009059
theorem B16001459 : Blo 1248442 16001459 := bstep (se 1 (by rfl) ⟨12001094, by rfl⟩ : syracuseStep 16001459 = 24002189) B24002189
theorem B16222643 : Blo 1248442 16222643 := bstep (se 1 (by rfl) ⟨12166982, by rfl⟩ : syracuseStep 16222643 = 24333965) B24333965
theorem B3164609 : Blo 1248442 3164609 := bstep (se 2 (by rfl) ⟨1186728, by rfl⟩ : syracuseStep 3164609 = 2373457) B2373457
theorem B2812427 : Blo 1248442 2812427 := bstep (se 1 (by rfl) ⟨2109320, by rfl⟩ : syracuseStep 2812427 = 4218641) B4218641
theorem B2812481 : Blo 1248442 2812481 := bstep (se 2 (by rfl) ⟨1054680, by rfl⟩ : syracuseStep 2812481 = 2109361) B2109361
theorem B2107991 : Blo 1248442 2107991 := bstep (se 1 (by rfl) ⟨1580993, by rfl⟩ : syracuseStep 2107991 = 3161987) B3161987
theorem B2108119 : Blo 1248442 2108119 := bstep (se 1 (by rfl) ⟨1581089, by rfl⟩ : syracuseStep 2108119 = 3162179) B3162179
theorem B2812697 : Blo 1248442 2812697 := bstep (se 2 (by rfl) ⟨1054761, by rfl⟩ : syracuseStep 2812697 = 2109523) B2109523
theorem B2812787 : Blo 1248442 2812787 := bstep (se 1 (by rfl) ⟨2109590, by rfl⟩ : syracuseStep 2812787 = 4219181) B4219181
theorem B2812823 : Blo 1248442 2812823 := bstep (se 1 (by rfl) ⟨2109617, by rfl⟩ : syracuseStep 2812823 = 4219235) B4219235
theorem B4213835 : Blo 1248442 4213835 := bstep (se 1 (by rfl) ⟨3160376, by rfl⟩ : syracuseStep 4213835 = 6320753) B6320753
theorem B2813003 : Blo 1248442 2813003 := bstep (se 1 (by rfl) ⟨2109752, by rfl⟩ : syracuseStep 2813003 = 4219505) B4219505
theorem B2370647 : Blo 1248442 2370647 := bstep (se 1 (by rfl) ⟨1777985, by rfl⟩ : syracuseStep 2370647 = 3555971) B3555971
theorem B2813057 : Blo 1248442 2813057 := bstep (se 2 (by rfl) ⟨1054896, by rfl⟩ : syracuseStep 2813057 = 2109793) B2109793
theorem B25996439 : Blo 1248442 25996439 := bstep (se 1 (by rfl) ⟨19497329, by rfl⟩ : syracuseStep 25996439 = 38994659) B38994659
theorem B1248459 : Blo 1248442 1248459 := bstep (se 1 (by rfl) ⟨936344, by rfl⟩ : syracuseStep 1248459 = 1872689) B1872689
theorem B1248471 : Blo 1248442 1248471 := bstep (se 1 (by rfl) ⟨936353, by rfl⟩ : syracuseStep 1248471 = 1872707) B1872707
theorem B1248491 : Blo 1248442 1248491 := bstep (se 1 (by rfl) ⟨936368, by rfl⟩ : syracuseStep 1248491 = 1872737) B1872737
theorem B1248503 : Blo 1248442 1248503 := bstep (se 1 (by rfl) ⟨936377, by rfl⟩ : syracuseStep 1248503 = 1872755) B1872755
theorem B1248523 : Blo 1248442 1248523 := bstep (se 1 (by rfl) ⟨936392, by rfl⟩ : syracuseStep 1248523 = 1872785) B1872785
theorem B1248535 : Blo 1248442 1248535 := bstep (se 1 (by rfl) ⟨936401, by rfl⟩ : syracuseStep 1248535 = 1872803) B1872803
theorem B1248555 : Blo 1248442 1248555 := bstep (se 1 (by rfl) ⟨936416, by rfl⟩ : syracuseStep 1248555 = 1872833) B1872833
theorem B1248567 : Blo 1248442 1248567 := bstep (se 1 (by rfl) ⟨936425, by rfl⟩ : syracuseStep 1248567 = 1872851) B1872851
theorem B1248587 : Blo 1248442 1248587 := bstep (se 1 (by rfl) ⟨936440, by rfl⟩ : syracuseStep 1248587 = 1872881) B1872881
theorem B2108747 : Blo 1248442 2108747 := bstep (se 1 (by rfl) ⟨1581560, by rfl⟩ : syracuseStep 2108747 = 3163121) B3163121
theorem B1248599 : Blo 1248442 1248599 := bstep (se 1 (by rfl) ⟨936449, by rfl⟩ : syracuseStep 1248599 = 1872899) B1872899
theorem B4214105 : Blo 1248442 4214105 := bstep (se 2 (by rfl) ⟨1580289, by rfl⟩ : syracuseStep 4214105 = 3160579) B3160579
theorem B2813273 : Blo 1248442 2813273 := bstep (se 2 (by rfl) ⟨1054977, by rfl⟩ : syracuseStep 2813273 = 2109955) B2109955
theorem B1248619 : Blo 1248442 1248619 := bstep (se 1 (by rfl) ⟨936464, by rfl⟩ : syracuseStep 1248619 = 1872929) B1872929
theorem B1248631 : Blo 1248442 1248631 := bstep (se 1 (by rfl) ⟨936473, by rfl⟩ : syracuseStep 1248631 = 1872947) B1872947
theorem B1248651 : Blo 1248442 1248651 := bstep (se 1 (by rfl) ⟨936488, by rfl⟩ : syracuseStep 1248651 = 1872977) B1872977
theorem B1248663 : Blo 1248442 1248663 := bstep (se 1 (by rfl) ⟨936497, by rfl⟩ : syracuseStep 1248663 = 1872995) B1872995
theorem B1248683 : Blo 1248442 1248683 := bstep (se 1 (by rfl) ⟨936512, by rfl⟩ : syracuseStep 1248683 = 1873025) B1873025
theorem B2813363 : Blo 1248442 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B1248695 : Blo 1248442 1248695 := bstep (se 1 (by rfl) ⟨936521, by rfl⟩ : syracuseStep 1248695 = 1873043) B1873043
theorem B1248715 : Blo 1248442 1248715 := bstep (se 1 (by rfl) ⟨936536, by rfl⟩ : syracuseStep 1248715 = 1873073) B1873073
theorem B2108875 : Blo 1248442 2108875 := bstep (se 1 (by rfl) ⟨1581656, by rfl⟩ : syracuseStep 2108875 = 3163313) B3163313
theorem B1248727 : Blo 1248442 1248727 := bstep (se 1 (by rfl) ⟨936545, by rfl⟩ : syracuseStep 1248727 = 1873091) B1873091
theorem B2813399 : Blo 1248442 2813399 := bstep (se 1 (by rfl) ⟨2110049, by rfl⟩ : syracuseStep 2813399 = 4220099) B4220099
theorem B3796445 : Blo 1248442 3796445 := bstep (se 3 (by rfl) ⟨711833, by rfl⟩ : syracuseStep 3796445 = 1423667) B1423667
theorem B1248747 : Blo 1248442 1248747 := bstep (se 1 (by rfl) ⟨936560, by rfl⟩ : syracuseStep 1248747 = 1873121) B1873121
theorem B1248759 : Blo 1248442 1248759 := bstep (se 1 (by rfl) ⟨936569, by rfl⟩ : syracuseStep 1248759 = 1873139) B1873139
theorem B1248779 : Blo 1248442 1248779 := bstep (se 1 (by rfl) ⟨936584, by rfl⟩ : syracuseStep 1248779 = 1873169) B1873169
theorem B1248791 : Blo 1248442 1248791 := bstep (se 1 (by rfl) ⟨936593, by rfl⟩ : syracuseStep 1248791 = 1873187) B1873187
theorem B1248811 : Blo 1248442 1248811 := bstep (se 1 (by rfl) ⟨936608, by rfl⟩ : syracuseStep 1248811 = 1873217) B1873217
theorem B1248823 : Blo 1248442 1248823 := bstep (se 1 (by rfl) ⟨936617, by rfl⟩ : syracuseStep 1248823 = 1873235) B1873235
theorem B19222085 : Blo 1248442 19222085 := bstep (se 4 (by rfl) ⟨1802070, by rfl⟩ : syracuseStep 19222085 = 3604141) B3604141
theorem B1248843 : Blo 1248442 1248843 := bstep (se 1 (by rfl) ⟨936632, by rfl⟩ : syracuseStep 1248843 = 1873265) B1873265
theorem B1248855 : Blo 1248442 1248855 := bstep (se 1 (by rfl) ⟨936641, by rfl⟩ : syracuseStep 1248855 = 1873283) B1873283
theorem B2109017 : Blo 1248442 2109017 := bstep (se 2 (by rfl) ⟨790881, by rfl⟩ : syracuseStep 2109017 = 1581763) B1581763
theorem B1248875 : Blo 1248442 1248875 := bstep (se 1 (by rfl) ⟨936656, by rfl⟩ : syracuseStep 1248875 = 1873313) B1873313
theorem B2371187 : Blo 1248442 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B1404535 : Blo 1248442 1404535 := bstep (se 1 (by rfl) ⟨1053401, by rfl⟩ : syracuseStep 1404535 = 2106803) B2106803
theorem B1248887 : Blo 1248442 1248887 := bstep (se 1 (by rfl) ⟨936665, by rfl⟩ : syracuseStep 1248887 = 1873331) B1873331
theorem B9481859 : Blo 1248442 9481859 := bstep (se 1 (by rfl) ⟨7111394, by rfl⟩ : syracuseStep 9481859 = 14222789) B14222789
theorem B4746883 : Blo 1248442 4746883 := bstep (se 1 (by rfl) ⟨3560162, by rfl⟩ : syracuseStep 4746883 = 7120325) B7120325
theorem B1248907 : Blo 1248442 1248907 := bstep (se 1 (by rfl) ⟨936680, by rfl⟩ : syracuseStep 1248907 = 1873361) B1873361
theorem B1248919 : Blo 1248442 1248919 := bstep (se 1 (by rfl) ⟨936689, by rfl⟩ : syracuseStep 1248919 = 1873379) B1873379
theorem B1248939 : Blo 1248442 1248939 := bstep (se 1 (by rfl) ⟨936704, by rfl⟩ : syracuseStep 1248939 = 1873409) B1873409
theorem B1248951 : Blo 1248442 1248951 := bstep (se 1 (by rfl) ⟨936713, by rfl⟩ : syracuseStep 1248951 = 1873427) B1873427
theorem B1248971 : Blo 1248442 1248971 := bstep (se 1 (by rfl) ⟨936728, by rfl⟩ : syracuseStep 1248971 = 1873457) B1873457
theorem B3559115 : Blo 1248442 3559115 := bstep (se 1 (by rfl) ⟨2669336, by rfl⟩ : syracuseStep 3559115 = 5338673) B5338673
theorem B1248983 : Blo 1248442 1248983 := bstep (se 1 (by rfl) ⟨936737, by rfl⟩ : syracuseStep 1248983 = 1873475) B1873475
theorem B2109145 : Blo 1248442 2109145 := bstep (se 2 (by rfl) ⟨790929, by rfl⟩ : syracuseStep 2109145 = 1581859) B1581859
theorem B1249003 : Blo 1248442 1249003 := bstep (se 1 (by rfl) ⟨936752, by rfl⟩ : syracuseStep 1249003 = 1873505) B1873505
theorem B23998193 : Blo 1248442 23998193 := bstep (se 2 (by rfl) ⟨8999322, by rfl⟩ : syracuseStep 23998193 = 17998645) B17998645
theorem B1249015 : Blo 1248442 1249015 := bstep (se 1 (by rfl) ⟨936761, by rfl⟩ : syracuseStep 1249015 = 1873523) B1873523
theorem B1249035 : Blo 1248442 1249035 := bstep (se 1 (by rfl) ⟨936776, by rfl⟩ : syracuseStep 1249035 = 1873553) B1873553
theorem B1249047 : Blo 1248442 1249047 := bstep (se 1 (by rfl) ⟨936785, by rfl⟩ : syracuseStep 1249047 = 1873571) B1873571
theorem B1404715 : Blo 1248442 1404715 := bstep (se 1 (by rfl) ⟨1053536, by rfl⟩ : syracuseStep 1404715 = 2107073) B2107073
theorem B1249067 : Blo 1248442 1249067 := bstep (se 1 (by rfl) ⟨936800, by rfl⟩ : syracuseStep 1249067 = 1873601) B1873601
theorem B3796787 : Blo 1248442 3796787 := bstep (se 1 (by rfl) ⟨2847590, by rfl⟩ : syracuseStep 3796787 = 5695181) B5695181
theorem B1249079 : Blo 1248442 1249079 := bstep (se 1 (by rfl) ⟨936809, by rfl⟩ : syracuseStep 1249079 = 1873619) B1873619
theorem B1249099 : Blo 1248442 1249099 := bstep (se 1 (by rfl) ⟨936824, by rfl⟩ : syracuseStep 1249099 = 1873649) B1873649
theorem B1249111 : Blo 1248442 1249111 := bstep (se 1 (by rfl) ⟨936833, by rfl⟩ : syracuseStep 1249111 = 1873667) B1873667
theorem B1249131 : Blo 1248442 1249131 := bstep (se 1 (by rfl) ⟨936848, by rfl⟩ : syracuseStep 1249131 = 1873697) B1873697
theorem B1249143 : Blo 1248442 1249143 := bstep (se 1 (by rfl) ⟨936857, by rfl⟩ : syracuseStep 1249143 = 1873715) B1873715
theorem B1249163 : Blo 1248442 1249163 := bstep (se 1 (by rfl) ⟨936872, by rfl⟩ : syracuseStep 1249163 = 1873745) B1873745
theorem B1404823 : Blo 1248442 1404823 := bstep (se 1 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 1404823 = 2107235) B2107235
theorem B4001687 : Blo 1248442 4001687 := bstep (se 1 (by rfl) ⟨3001265, by rfl⟩ : syracuseStep 4001687 = 6002531) B6002531
theorem B1249175 : Blo 1248442 1249175 := bstep (se 1 (by rfl) ⟨936881, by rfl⟩ : syracuseStep 1249175 = 1873763) B1873763
theorem B1249195 : Blo 1248442 1249195 := bstep (se 1 (by rfl) ⟨936896, by rfl⟩ : syracuseStep 1249195 = 1873793) B1873793
theorem B7114675 : Blo 1248442 7114675 := bstep (se 1 (by rfl) ⟨5336006, by rfl⟩ : syracuseStep 7114675 = 10672013) B10672013
theorem B4747187 : Blo 1248442 4747187 := bstep (se 1 (by rfl) ⟨3560390, by rfl⟩ : syracuseStep 4747187 = 7120781) B7120781
theorem B1249207 : Blo 1248442 1249207 := bstep (se 1 (by rfl) ⟨936905, by rfl⟩ : syracuseStep 1249207 = 1873811) B1873811
theorem B1249227 : Blo 1248442 1249227 := bstep (se 1 (by rfl) ⟨936920, by rfl⟩ : syracuseStep 1249227 = 1873841) B1873841
theorem B1249239 : Blo 1248442 1249239 := bstep (se 1 (by rfl) ⟨936929, by rfl⟩ : syracuseStep 1249239 = 1873859) B1873859
theorem B1249259 : Blo 1248442 1249259 := bstep (se 1 (by rfl) ⟨936944, by rfl⟩ : syracuseStep 1249259 = 1873889) B1873889
theorem B1249271 : Blo 1248442 1249271 := bstep (se 1 (by rfl) ⟨936953, by rfl⟩ : syracuseStep 1249271 = 1873907) B1873907
theorem B4501507 : Blo 1248442 4501507 := bstep (se 1 (by rfl) ⟨3376130, by rfl⟩ : syracuseStep 4501507 = 6752261) B6752261
theorem B1249291 : Blo 1248442 1249291 := bstep (se 1 (by rfl) ⟨936968, by rfl⟩ : syracuseStep 1249291 = 1873937) B1873937
theorem B4214807 : Blo 1248442 4214807 := bstep (se 1 (by rfl) ⟨3161105, by rfl⟩ : syracuseStep 4214807 = 6322211) B6322211
theorem B1249303 : Blo 1248442 1249303 := bstep (se 1 (by rfl) ⟨936977, by rfl⟩ : syracuseStep 1249303 = 1873955) B1873955
theorem B3379223 : Blo 1248442 3379223 := bstep (se 1 (by rfl) ⟨2534417, by rfl⟩ : syracuseStep 3379223 = 5068835) B5068835
theorem B1249323 : Blo 1248442 1249323 := bstep (se 1 (by rfl) ⟨936992, by rfl⟩ : syracuseStep 1249323 = 1873985) B1873985
theorem B1249335 : Blo 1248442 1249335 := bstep (se 1 (by rfl) ⟨937001, by rfl⟩ : syracuseStep 1249335 = 1874003) B1874003
theorem B1405003 : Blo 1248442 1405003 := bstep (se 1 (by rfl) ⟨1053752, by rfl⟩ : syracuseStep 1405003 = 2107505) B2107505
theorem B1249355 : Blo 1248442 1249355 := bstep (se 1 (by rfl) ⟨937016, by rfl⟩ : syracuseStep 1249355 = 1874033) B1874033
theorem B1249367 : Blo 1248442 1249367 := bstep (se 1 (by rfl) ⟨937025, by rfl⟩ : syracuseStep 1249367 = 1874051) B1874051
theorem B2371673 : Blo 1248442 2371673 := bstep (se 2 (by rfl) ⟨889377, by rfl⟩ : syracuseStep 2371673 = 1778755) B1778755
theorem B1249387 : Blo 1248442 1249387 := bstep (se 1 (by rfl) ⟨937040, by rfl⟩ : syracuseStep 1249387 = 1874081) B1874081
theorem B1249399 : Blo 1248442 1249399 := bstep (se 1 (by rfl) ⟨937049, by rfl⟩ : syracuseStep 1249399 = 1874099) B1874099
theorem B1249419 : Blo 1248442 1249419 := bstep (se 1 (by rfl) ⟨937064, by rfl⟩ : syracuseStep 1249419 = 1874129) B1874129
theorem B1249431 : Blo 1248442 1249431 := bstep (se 1 (by rfl) ⟨937073, by rfl⟩ : syracuseStep 1249431 = 1874147) B1874147
theorem B1249451 : Blo 1248442 1249451 := bstep (se 1 (by rfl) ⟨937088, by rfl⟩ : syracuseStep 1249451 = 1874177) B1874177
theorem B1405111 : Blo 1248442 1405111 := bstep (se 1 (by rfl) ⟨1053833, by rfl⟩ : syracuseStep 1405111 = 2107667) B2107667
theorem B1249463 : Blo 1248442 1249463 := bstep (se 1 (by rfl) ⟨937097, by rfl⟩ : syracuseStep 1249463 = 1874195) B1874195
theorem B1249483 : Blo 1248442 1249483 := bstep (se 1 (by rfl) ⟨937112, by rfl⟩ : syracuseStep 1249483 = 1874225) B1874225
theorem B1249495 : Blo 1248442 1249495 := bstep (se 1 (by rfl) ⟨937121, by rfl⟩ : syracuseStep 1249495 = 1874243) B1874243
theorem B5411033 : Blo 1248442 5411033 := bstep (se 2 (by rfl) ⟨2029137, by rfl⟩ : syracuseStep 5411033 = 4058275) B4058275
theorem B1249515 : Blo 1248442 1249515 := bstep (se 1 (by rfl) ⟨937136, by rfl⟩ : syracuseStep 1249515 = 1874273) B1874273
theorem B20254961 : Blo 1248442 20254961 := bstep (se 2 (by rfl) ⟨7595610, by rfl⟩ : syracuseStep 20254961 = 15191221) B15191221
theorem B1249527 : Blo 1248442 1249527 := bstep (se 1 (by rfl) ⟨937145, by rfl⟩ : syracuseStep 1249527 = 1874291) B1874291
theorem B1249547 : Blo 1248442 1249547 := bstep (se 1 (by rfl) ⟨937160, by rfl⟩ : syracuseStep 1249547 = 1874321) B1874321
theorem B5697809 : Blo 1248442 5697809 := bstep (se 2 (by rfl) ⟨2136678, by rfl⟩ : syracuseStep 5697809 = 4273357) B4273357
theorem B1249559 : Blo 1248442 1249559 := bstep (se 1 (by rfl) ⟨937169, by rfl⟩ : syracuseStep 1249559 = 1874339) B1874339
theorem B2109719 : Blo 1248442 2109719 := bstep (se 1 (by rfl) ⟨1582289, by rfl⟩ : syracuseStep 2109719 = 3164579) B3164579
theorem B1249579 : Blo 1248442 1249579 := bstep (se 1 (by rfl) ⟨937184, by rfl⟩ : syracuseStep 1249579 = 1874369) B1874369
theorem B6320429 : Blo 1248442 6320429 := bstep (se 3 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 6320429 = 2370161) B2370161
theorem B4509997 : Blo 1248442 4509997 := bstep (se 3 (by rfl) ⟨845624, by rfl⟩ : syracuseStep 4509997 = 1691249) B1691249
theorem B1249591 : Blo 1248442 1249591 := bstep (se 1 (by rfl) ⟨937193, by rfl⟩ : syracuseStep 1249591 = 1874387) B1874387
theorem B1249611 : Blo 1248442 1249611 := bstep (se 1 (by rfl) ⟨937208, by rfl⟩ : syracuseStep 1249611 = 1874417) B1874417
theorem B1249623 : Blo 1248442 1249623 := bstep (se 1 (by rfl) ⟨937217, by rfl⟩ : syracuseStep 1249623 = 1874435) B1874435
theorem B1405291 : Blo 1248442 1405291 := bstep (se 1 (by rfl) ⟨1053968, by rfl⟩ : syracuseStep 1405291 = 2107937) B2107937
theorem B1249643 : Blo 1248442 1249643 := bstep (se 1 (by rfl) ⟨937232, by rfl⟩ : syracuseStep 1249643 = 1874465) B1874465
theorem B1249655 : Blo 1248442 1249655 := bstep (se 1 (by rfl) ⟨937241, by rfl⟩ : syracuseStep 1249655 = 1874483) B1874483
theorem B2568577 : Blo 1248442 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B1249675 : Blo 1248442 1249675 := bstep (se 1 (by rfl) ⟨937256, by rfl⟩ : syracuseStep 1249675 = 1874513) B1874513
theorem B1249687 : Blo 1248442 1249687 := bstep (se 1 (by rfl) ⟨937265, by rfl⟩ : syracuseStep 1249687 = 1874531) B1874531
theorem B2109847 : Blo 1248442 2109847 := bstep (se 1 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 2109847 = 3164771) B3164771
theorem B1249707 : Blo 1248442 1249707 := bstep (se 1 (by rfl) ⟨937280, by rfl⟩ : syracuseStep 1249707 = 1874561) B1874561
theorem B1249719 : Blo 1248442 1249719 := bstep (se 1 (by rfl) ⟨937289, by rfl⟩ : syracuseStep 1249719 = 1874579) B1874579
theorem B2666945 : Blo 1248442 2666945 := bstep (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) B2000209
theorem B1249739 : Blo 1248442 1249739 := bstep (se 1 (by rfl) ⟨937304, by rfl⟩ : syracuseStep 1249739 = 1874609) B1874609
theorem B1405399 : Blo 1248442 1405399 := bstep (se 1 (by rfl) ⟨1054049, by rfl⟩ : syracuseStep 1405399 = 2108099) B2108099
theorem B1249751 : Blo 1248442 1249751 := bstep (se 1 (by rfl) ⟨937313, by rfl⟩ : syracuseStep 1249751 = 1874627) B1874627
theorem B3043801 : Blo 1248442 3043801 := bstep (se 2 (by rfl) ⟨1141425, by rfl⟩ : syracuseStep 3043801 = 2282851) B2282851
theorem B1249771 : Blo 1248442 1249771 := bstep (se 1 (by rfl) ⟨937328, by rfl⟩ : syracuseStep 1249771 = 1874657) B1874657
theorem B1249783 : Blo 1248442 1249783 := bstep (se 1 (by rfl) ⟨937337, by rfl⟩ : syracuseStep 1249783 = 1874675) B1874675
theorem B1249803 : Blo 1248442 1249803 := bstep (se 1 (by rfl) ⟨937352, by rfl⟩ : syracuseStep 1249803 = 1874705) B1874705
theorem B1249815 : Blo 1248442 1249815 := bstep (se 1 (by rfl) ⟨937361, by rfl⟩ : syracuseStep 1249815 = 1874723) B1874723
theorem B1249835 : Blo 1248442 1249835 := bstep (se 1 (by rfl) ⟨937376, by rfl⟩ : syracuseStep 1249835 = 1874753) B1874753
theorem B4215347 : Blo 1248442 4215347 := bstep (se 1 (by rfl) ⟨3161510, by rfl⟩ : syracuseStep 4215347 = 6323021) B6323021
theorem B1249847 : Blo 1248442 1249847 := bstep (se 1 (by rfl) ⟨937385, by rfl⟩ : syracuseStep 1249847 = 1874771) B1874771
theorem B1249867 : Blo 1248442 1249867 := bstep (se 1 (by rfl) ⟨937400, by rfl⟩ : syracuseStep 1249867 = 1874801) B1874801
theorem B1249879 : Blo 1248442 1249879 := bstep (se 1 (by rfl) ⟨937409, by rfl⟩ : syracuseStep 1249879 = 1874819) B1874819
theorem B1249899 : Blo 1248442 1249899 := bstep (se 1 (by rfl) ⟨937424, by rfl⟩ : syracuseStep 1249899 = 1874849) B1874849
theorem B1249911 : Blo 1248442 1249911 := bstep (se 1 (by rfl) ⟨937433, by rfl⟩ : syracuseStep 1249911 = 1874867) B1874867
theorem B1405579 : Blo 1248442 1405579 := bstep (se 1 (by rfl) ⟨1054184, by rfl⟩ : syracuseStep 1405579 = 2108369) B2108369
theorem B1249931 : Blo 1248442 1249931 := bstep (se 1 (by rfl) ⟨937448, by rfl⟩ : syracuseStep 1249931 = 1874897) B1874897
theorem B1249943 : Blo 1248442 1249943 := bstep (se 1 (by rfl) ⟨937457, by rfl⟩ : syracuseStep 1249943 = 1874915) B1874915
theorem B1249963 : Blo 1248442 1249963 := bstep (se 1 (by rfl) ⟨937472, by rfl⟩ : syracuseStep 1249963 = 1874945) B1874945
theorem B1249975 : Blo 1248442 1249975 := bstep (se 1 (by rfl) ⟨937481, by rfl⟩ : syracuseStep 1249975 = 1874963) B1874963
theorem B1249995 : Blo 1248442 1249995 := bstep (se 1 (by rfl) ⟨937496, by rfl⟩ : syracuseStep 1249995 = 1874993) B1874993
theorem B3379915 : Blo 1248442 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B1250007 : Blo 1248442 1250007 := bstep (se 1 (by rfl) ⟨937505, by rfl⟩ : syracuseStep 1250007 = 1875011) B1875011
theorem B1250027 : Blo 1248442 1250027 := bstep (se 1 (by rfl) ⟨937520, by rfl⟩ : syracuseStep 1250027 = 1875041) B1875041
theorem B1405687 : Blo 1248442 1405687 := bstep (se 1 (by rfl) ⟨1054265, by rfl⟩ : syracuseStep 1405687 = 2108531) B2108531
theorem B1250039 : Blo 1248442 1250039 := bstep (se 1 (by rfl) ⟨937529, by rfl⟩ : syracuseStep 1250039 = 1875059) B1875059
theorem B1250059 : Blo 1248442 1250059 := bstep (se 1 (by rfl) ⟨937544, by rfl⟩ : syracuseStep 1250059 = 1875089) B1875089
theorem B1520407 : Blo 1248442 1520407 := bstep (se 1 (by rfl) ⟨1140305, by rfl⟩ : syracuseStep 1520407 = 2280611) B2280611
theorem B1250071 : Blo 1248442 1250071 := bstep (se 1 (by rfl) ⟨937553, by rfl⟩ : syracuseStep 1250071 = 1875107) B1875107
theorem B1872665 : Blo 1248442 1872665 := bstep (se 2 (by rfl) ⟨702249, by rfl⟩ : syracuseStep 1872665 = 1404499) B1404499
theorem B1250091 : Blo 1248442 1250091 := bstep (se 1 (by rfl) ⟨937568, by rfl⟩ : syracuseStep 1250091 = 1875137) B1875137
theorem B1250103 : Blo 1248442 1250103 := bstep (se 1 (by rfl) ⟨937577, by rfl⟩ : syracuseStep 1250103 = 1875155) B1875155
theorem B4215617 : Blo 1248442 4215617 := bstep (se 2 (by rfl) ⟨1580856, by rfl⟩ : syracuseStep 4215617 = 3161713) B3161713
theorem B1250123 : Blo 1248442 1250123 := bstep (se 1 (by rfl) ⟨937592, by rfl⟩ : syracuseStep 1250123 = 1875185) B1875185
theorem B1250135 : Blo 1248442 1250135 := bstep (se 1 (by rfl) ⟨937601, by rfl⟩ : syracuseStep 1250135 = 1875203) B1875203
theorem B9007973 : Blo 1248442 9007973 := bstep (se 4 (by rfl) ⟨844497, by rfl⟩ : syracuseStep 9007973 = 1688995) B1688995
theorem B1250155 : Blo 1248442 1250155 := bstep (se 1 (by rfl) ⟨937616, by rfl⟩ : syracuseStep 1250155 = 1875233) B1875233
theorem B1250167 : Blo 1248442 1250167 := bstep (se 1 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 1250167 = 1875251) B1875251
theorem B1872779 : Blo 1248442 1872779 := bstep (se 1 (by rfl) ⟨1404584, by rfl⟩ : syracuseStep 1872779 = 2809169) B2809169
theorem B1250187 : Blo 1248442 1250187 := bstep (se 1 (by rfl) ⟨937640, by rfl⟩ : syracuseStep 1250187 = 1875281) B1875281
theorem B1872791 : Blo 1248442 1872791 := bstep (se 1 (by rfl) ⟨1404593, by rfl⟩ : syracuseStep 1872791 = 2809187) B2809187
theorem B1250199 : Blo 1248442 1250199 := bstep (se 1 (by rfl) ⟨937649, by rfl⟩ : syracuseStep 1250199 = 1875299) B1875299
theorem B1405867 : Blo 1248442 1405867 := bstep (se 1 (by rfl) ⟨1054400, by rfl⟩ : syracuseStep 1405867 = 2108801) B2108801
theorem B1250219 : Blo 1248442 1250219 := bstep (se 1 (by rfl) ⟨937664, by rfl⟩ : syracuseStep 1250219 = 1875329) B1875329
theorem B1250231 : Blo 1248442 1250231 := bstep (se 1 (by rfl) ⟨937673, by rfl⟩ : syracuseStep 1250231 = 1875347) B1875347
theorem B1250251 : Blo 1248442 1250251 := bstep (se 1 (by rfl) ⟨937688, by rfl⟩ : syracuseStep 1250251 = 1875377) B1875377
theorem B1250263 : Blo 1248442 1250263 := bstep (se 1 (by rfl) ⟨937697, by rfl⟩ : syracuseStep 1250263 = 1875395) B1875395
theorem B1872857 : Blo 1248442 1872857 := bstep (se 2 (by rfl) ⟨702321, by rfl⟩ : syracuseStep 1872857 = 1404643) B1404643
theorem B1250283 : Blo 1248442 1250283 := bstep (se 1 (by rfl) ⟨937712, by rfl⟩ : syracuseStep 1250283 = 1875425) B1875425
theorem B1250295 : Blo 1248442 1250295 := bstep (se 1 (by rfl) ⟨937721, by rfl⟩ : syracuseStep 1250295 = 1875443) B1875443
theorem B1250315 : Blo 1248442 1250315 := bstep (se 1 (by rfl) ⟨937736, by rfl⟩ : syracuseStep 1250315 = 1875473) B1875473
theorem B1405975 : Blo 1248442 1405975 := bstep (se 1 (by rfl) ⟨1054481, by rfl⟩ : syracuseStep 1405975 = 2108963) B2108963
theorem B1250327 : Blo 1248442 1250327 := bstep (se 1 (by rfl) ⟨937745, by rfl⟩ : syracuseStep 1250327 = 1875491) B1875491
theorem B1250347 : Blo 1248442 1250347 := bstep (se 1 (by rfl) ⟨937760, by rfl⟩ : syracuseStep 1250347 = 1875521) B1875521
theorem B1250359 : Blo 1248442 1250359 := bstep (se 1 (by rfl) ⟨937769, by rfl⟩ : syracuseStep 1250359 = 1875539) B1875539
theorem B1872971 : Blo 1248442 1872971 := bstep (se 1 (by rfl) ⟨1404728, by rfl⟩ : syracuseStep 1872971 = 2809457) B2809457
theorem B4502603 : Blo 1248442 4502603 := bstep (se 1 (by rfl) ⟨3376952, by rfl⟩ : syracuseStep 4502603 = 6753905) B6753905
theorem B1250379 : Blo 1248442 1250379 := bstep (se 1 (by rfl) ⟨937784, by rfl⟩ : syracuseStep 1250379 = 1875569) B1875569
theorem B1872983 : Blo 1248442 1872983 := bstep (se 1 (by rfl) ⟨1404737, by rfl⟩ : syracuseStep 1872983 = 2809475) B2809475
theorem B1250391 : Blo 1248442 1250391 := bstep (se 1 (by rfl) ⟨937793, by rfl⟩ : syracuseStep 1250391 = 1875587) B1875587
theorem B1250411 : Blo 1248442 1250411 := bstep (se 1 (by rfl) ⟨937808, by rfl⟩ : syracuseStep 1250411 = 1875617) B1875617
theorem B1250423 : Blo 1248442 1250423 := bstep (se 1 (by rfl) ⟨937817, by rfl⟩ : syracuseStep 1250423 = 1875635) B1875635
theorem B2569367 : Blo 1248442 2569367 := bstep (se 1 (by rfl) ⟨1927025, by rfl⟩ : syracuseStep 2569367 = 3854051) B3854051
theorem B1873049 : Blo 1248442 1873049 := bstep (se 2 (by rfl) ⟨702393, by rfl⟩ : syracuseStep 1873049 = 1404787) B1404787
theorem B6755507 : Blo 1248442 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B3003571 : Blo 1248442 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B1406155 : Blo 1248442 1406155 := bstep (se 1 (by rfl) ⟨1054616, by rfl⟩ : syracuseStep 1406155 = 2109233) B2109233
theorem B4502749 : Blo 1248442 4502749 := bstep (se 3 (by rfl) ⟨844265, by rfl⟩ : syracuseStep 4502749 = 1688531) B1688531
theorem B1873163 : Blo 1248442 1873163 := bstep (se 1 (by rfl) ⟨1404872, by rfl⟩ : syracuseStep 1873163 = 2809745) B2809745
theorem B1873175 : Blo 1248442 1873175 := bstep (se 1 (by rfl) ⟨1404881, by rfl⟩ : syracuseStep 1873175 = 2809763) B2809763
theorem B3560755 : Blo 1248442 3560755 := bstep (se 1 (by rfl) ⟨2670566, by rfl⟩ : syracuseStep 3560755 = 5341133) B5341133
theorem B1406263 : Blo 1248442 1406263 := bstep (se 1 (by rfl) ⟨1054697, by rfl⟩ : syracuseStep 1406263 = 2109395) B2109395
theorem B1873241 : Blo 1248442 1873241 := bstep (se 2 (by rfl) ⟨702465, by rfl⟩ : syracuseStep 1873241 = 1404931) B1404931
theorem B4216157 : Blo 1248442 4216157 := bstep (se 3 (by rfl) ⟨790529, by rfl⟩ : syracuseStep 4216157 = 1581059) B1581059
theorem B7116133 : Blo 1248442 7116133 := bstep (se 4 (by rfl) ⟨667137, by rfl⟩ : syracuseStep 7116133 = 1334275) B1334275
theorem B1873355 : Blo 1248442 1873355 := bstep (se 1 (by rfl) ⟨1405016, by rfl⟩ : syracuseStep 1873355 = 2810033) B2810033
theorem B1873367 : Blo 1248442 1873367 := bstep (se 1 (by rfl) ⟨1405025, by rfl⟩ : syracuseStep 1873367 = 2810051) B2810051
theorem B1406443 : Blo 1248442 1406443 := bstep (se 1 (by rfl) ⟨1054832, by rfl⟩ : syracuseStep 1406443 = 2109665) B2109665
theorem B2373131 : Blo 1248442 2373131 := bstep (se 1 (by rfl) ⟨1779848, by rfl⟩ : syracuseStep 2373131 = 3559697) B3559697
theorem B1873433 : Blo 1248442 1873433 := bstep (se 2 (by rfl) ⟨702537, by rfl⟩ : syracuseStep 1873433 = 1405075) B1405075
theorem B1406551 : Blo 1248442 1406551 := bstep (se 1 (by rfl) ⟨1054913, by rfl⟩ : syracuseStep 1406551 = 2109827) B2109827
theorem B6329987 : Blo 1248442 6329987 := bstep (se 1 (by rfl) ⟨4747490, by rfl⟩ : syracuseStep 6329987 = 9494981) B9494981
theorem B2250379 : Blo 1248442 2250379 := bstep (se 1 (by rfl) ⟨1687784, by rfl⟩ : syracuseStep 2250379 = 3375569) B3375569
theorem B1873547 : Blo 1248442 1873547 := bstep (se 1 (by rfl) ⟨1405160, by rfl⟩ : syracuseStep 1873547 = 2810321) B2810321
theorem B1873559 : Blo 1248442 1873559 := bstep (se 1 (by rfl) ⟨1405169, by rfl⟩ : syracuseStep 1873559 = 2810339) B2810339
theorem B2373313 : Blo 1248442 2373313 := bstep (se 2 (by rfl) ⟨889992, by rfl⟩ : syracuseStep 2373313 = 1779985) B1779985
theorem B1873625 : Blo 1248442 1873625 := bstep (se 2 (by rfl) ⟨702609, by rfl⟩ : syracuseStep 1873625 = 1405219) B1405219
theorem B1406731 : Blo 1248442 1406731 := bstep (se 1 (by rfl) ⟨1055048, by rfl⟩ : syracuseStep 1406731 = 2110097) B2110097
theorem B1873739 : Blo 1248442 1873739 := bstep (se 1 (by rfl) ⟨1405304, by rfl⟩ : syracuseStep 1873739 = 2810609) B2810609
theorem B3004235 : Blo 1248442 3004235 := bstep (se 1 (by rfl) ⟨2253176, by rfl⟩ : syracuseStep 3004235 = 4506353) B4506353
theorem B1873751 : Blo 1248442 1873751 := bstep (se 1 (by rfl) ⟨1405313, by rfl⟩ : syracuseStep 1873751 = 2810627) B2810627
theorem B2250625 : Blo 1248442 2250625 := bstep (se 2 (by rfl) ⟨843984, by rfl⟩ : syracuseStep 2250625 = 1687969) B1687969
theorem B1873817 : Blo 1248442 1873817 := bstep (se 2 (by rfl) ⟨702681, by rfl⟩ : syracuseStep 1873817 = 1405363) B1405363
theorem B4741037 : Blo 1248442 4741037 := bstep (se 3 (by rfl) ⟨888944, by rfl⟩ : syracuseStep 4741037 = 1777889) B1777889
theorem B1873931 : Blo 1248442 1873931 := bstep (se 1 (by rfl) ⟨1405448, by rfl⟩ : syracuseStep 1873931 = 2810897) B2810897
theorem B11999249 : Blo 1248442 11999249 := bstep (se 2 (by rfl) ⟨4499718, by rfl⟩ : syracuseStep 11999249 = 8999437) B8999437
theorem B1873943 : Blo 1248442 1873943 := bstep (se 1 (by rfl) ⟨1405457, by rfl⟩ : syracuseStep 1873943 = 2810915) B2810915
theorem B2668619 : Blo 1248442 2668619 := bstep (se 1 (by rfl) ⟨2001464, by rfl⟩ : syracuseStep 2668619 = 4002929) B4002929
theorem B2250841 : Blo 1248442 2250841 := bstep (se 2 (by rfl) ⟨844065, by rfl⟩ : syracuseStep 2250841 = 1688131) B1688131
theorem B1874009 : Blo 1248442 1874009 := bstep (se 2 (by rfl) ⟨702753, by rfl⟩ : syracuseStep 1874009 = 1405507) B1405507
theorem B18012253 : Blo 1248442 18012253 := bstep (se 3 (by rfl) ⟨3377297, by rfl⟩ : syracuseStep 18012253 = 6754595) B6754595
theorem B2373761 : Blo 1248442 2373761 := bstep (se 2 (by rfl) ⟨890160, by rfl⟩ : syracuseStep 2373761 = 1780321) B1780321
theorem B5339287 : Blo 1248442 5339287 := bstep (se 1 (by rfl) ⟨4004465, by rfl⟩ : syracuseStep 5339287 = 8008931) B8008931
theorem B24008885 : Blo 1248442 24008885 := bstep (se 5 (by rfl) ⟨1125416, by rfl⟩ : syracuseStep 24008885 = 2250833) B2250833
theorem B1874123 : Blo 1248442 1874123 := bstep (se 1 (by rfl) ⟨1405592, by rfl⟩ : syracuseStep 1874123 = 2811185) B2811185
theorem B1874135 : Blo 1248442 1874135 := bstep (se 1 (by rfl) ⟨1405601, by rfl⟩ : syracuseStep 1874135 = 2811203) B2811203
theorem B5339357 : Blo 1248442 5339357 := bstep (se 3 (by rfl) ⟨1001129, by rfl⟩ : syracuseStep 5339357 = 2002259) B2002259
theorem B1874201 : Blo 1248442 1874201 := bstep (se 2 (by rfl) ⟨702825, by rfl⟩ : syracuseStep 1874201 = 1405651) B1405651
theorem B4004147 : Blo 1248442 4004147 := bstep (se 1 (by rfl) ⟨3003110, by rfl⟩ : syracuseStep 4004147 = 6006221) B6006221
theorem B1333643 : Blo 1248442 1333643 := bstep (se 1 (by rfl) ⟨1000232, by rfl⟩ : syracuseStep 1333643 = 2000465) B2000465
theorem B1874315 : Blo 1248442 1874315 := bstep (se 1 (by rfl) ⟨1405736, by rfl⟩ : syracuseStep 1874315 = 2811473) B2811473
theorem B1874327 : Blo 1248442 1874327 := bstep (se 1 (by rfl) ⟨1405745, by rfl⟩ : syracuseStep 1874327 = 2811491) B2811491
theorem B4217291 : Blo 1248442 4217291 := bstep (se 1 (by rfl) ⟨3162968, by rfl⟩ : syracuseStep 4217291 = 6325937) B6325937
theorem B1874393 : Blo 1248442 1874393 := bstep (se 2 (by rfl) ⟨702897, by rfl⟩ : syracuseStep 1874393 = 1405795) B1405795
theorem B1301015 : Blo 1248442 1301015 := bstep (se 1 (by rfl) ⟨975761, by rfl⟩ : syracuseStep 1301015 = 1951523) B1951523
theorem B5134871 : Blo 1248442 5134871 := bstep (se 1 (by rfl) ⟨3851153, by rfl⟩ : syracuseStep 5134871 = 7702307) B7702307
theorem B9493037 : Blo 1248442 9493037 := bstep (se 3 (by rfl) ⟨1779944, by rfl⟩ : syracuseStep 9493037 = 3559889) B3559889
theorem B1874507 : Blo 1248442 1874507 := bstep (se 1 (by rfl) ⟨1405880, by rfl⟩ : syracuseStep 1874507 = 2811761) B2811761
theorem B1874519 : Blo 1248442 1874519 := bstep (se 1 (by rfl) ⟨1405889, by rfl⟩ : syracuseStep 1874519 = 2811779) B2811779
theorem B1874585 : Blo 1248442 1874585 := bstep (se 2 (by rfl) ⟨702969, by rfl⟩ : syracuseStep 1874585 = 1405939) B1405939
theorem B4741811 : Blo 1248442 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B4217561 : Blo 1248442 4217561 := bstep (se 2 (by rfl) ⟨1581585, by rfl⟩ : syracuseStep 4217561 = 3163171) B3163171
theorem B1874699 : Blo 1248442 1874699 := bstep (se 1 (by rfl) ⟨1406024, by rfl⟩ : syracuseStep 1874699 = 2812049) B2812049
theorem B7306001 : Blo 1248442 7306001 := bstep (se 2 (by rfl) ⟨2739750, by rfl⟩ : syracuseStep 7306001 = 5479501) B5479501
theorem B1874711 : Blo 1248442 1874711 := bstep (se 1 (by rfl) ⟨1406033, by rfl⟩ : syracuseStep 1874711 = 2812067) B2812067
theorem B3160883 : Blo 1248442 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B10132289 : Blo 1248442 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B8010571 : Blo 1248442 8010571 := bstep (se 1 (by rfl) ⟨6007928, by rfl⟩ : syracuseStep 8010571 = 12015857) B12015857
theorem B1874777 : Blo 1248442 1874777 := bstep (se 2 (by rfl) ⟨703041, by rfl⟩ : syracuseStep 1874777 = 1406083) B1406083
theorem B1874891 : Blo 1248442 1874891 := bstep (se 1 (by rfl) ⟨1406168, by rfl⟩ : syracuseStep 1874891 = 2812337) B2812337
theorem B5340107 : Blo 1248442 5340107 := bstep (se 1 (by rfl) ⟨4005080, by rfl⟩ : syracuseStep 5340107 = 8010161) B8010161
theorem B9485261 : Blo 1248442 9485261 := bstep (se 3 (by rfl) ⟨1778486, by rfl⟩ : syracuseStep 9485261 = 3556973) B3556973
theorem B1874903 : Blo 1248442 1874903 := bstep (se 1 (by rfl) ⟨1406177, by rfl⟩ : syracuseStep 1874903 = 2812355) B2812355
theorem B2669593 : Blo 1248442 2669593 := bstep (se 2 (by rfl) ⟨1001097, by rfl⟩ : syracuseStep 2669593 = 2002195) B2002195
theorem B1874969 : Blo 1248442 1874969 := bstep (se 2 (by rfl) ⟨703113, by rfl⟩ : syracuseStep 1874969 = 1406227) B1406227
theorem B3161177 : Blo 1248442 3161177 := bstep (se 2 (by rfl) ⟨1185441, by rfl⟩ : syracuseStep 3161177 = 2370883) B2370883
theorem B1875083 : Blo 1248442 1875083 := bstep (se 1 (by rfl) ⟨1406312, by rfl⟩ : syracuseStep 1875083 = 2812625) B2812625
theorem B5069969 : Blo 1248442 5069969 := bstep (se 2 (by rfl) ⟨1901238, by rfl⟩ : syracuseStep 5069969 = 3802477) B3802477
theorem B1875095 : Blo 1248442 1875095 := bstep (se 1 (by rfl) ⟨1406321, by rfl⟩ : syracuseStep 1875095 = 2812643) B2812643
theorem B2809025 : Blo 1248442 2809025 := bstep (se 2 (by rfl) ⟨1053384, by rfl⟩ : syracuseStep 2809025 = 2106769) B2106769
theorem B4504793 : Blo 1248442 4504793 := bstep (se 2 (by rfl) ⟨1689297, by rfl⟩ : syracuseStep 4504793 = 3378595) B3378595
theorem B1875161 : Blo 1248442 1875161 := bstep (se 2 (by rfl) ⟨703185, by rfl⟩ : syracuseStep 1875161 = 1406371) B1406371
theorem B2669849 : Blo 1248442 2669849 := bstep (se 2 (by rfl) ⟨1001193, by rfl⟩ : syracuseStep 2669849 = 2002387) B2002387
theorem B4111667 : Blo 1248442 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B1875275 : Blo 1248442 1875275 := bstep (se 1 (by rfl) ⟨1406456, by rfl⟩ : syracuseStep 1875275 = 2812913) B2812913
theorem B1875287 : Blo 1248442 1875287 := bstep (se 1 (by rfl) ⟨1406465, by rfl⟩ : syracuseStep 1875287 = 2812931) B2812931
theorem B1334647 : Blo 1248442 1334647 := bstep (se 1 (by rfl) ⟨1000985, by rfl⟩ : syracuseStep 1334647 = 2001971) B2001971
theorem B4218263 : Blo 1248442 4218263 := bstep (se 1 (by rfl) ⟨3163697, by rfl⟩ : syracuseStep 4218263 = 6327395) B6327395
theorem B2809241 : Blo 1248442 2809241 := bstep (se 2 (by rfl) ⟨1053465, by rfl⟩ : syracuseStep 2809241 = 2106931) B2106931
theorem B1875353 : Blo 1248442 1875353 := bstep (se 2 (by rfl) ⟨703257, by rfl⟩ : syracuseStep 1875353 = 1406515) B1406515
theorem B9485747 : Blo 1248442 9485747 := bstep (se 1 (by rfl) ⟨7114310, by rfl⟩ : syracuseStep 9485747 = 14228621) B14228621
theorem B8011187 : Blo 1248442 8011187 := bstep (se 1 (by rfl) ⟨6008390, by rfl⟩ : syracuseStep 8011187 = 12016781) B12016781
theorem B2252225 : Blo 1248442 2252225 := bstep (se 2 (by rfl) ⟨844584, by rfl⟩ : syracuseStep 2252225 = 1689169) B1689169
theorem B2809331 : Blo 1248442 2809331 := bstep (se 1 (by rfl) ⟨2106998, by rfl⟩ : syracuseStep 2809331 = 4213997) B4213997
theorem B1875467 : Blo 1248442 1875467 := bstep (se 1 (by rfl) ⟨1406600, by rfl⟩ : syracuseStep 1875467 = 2813201) B2813201
theorem B2809367 : Blo 1248442 2809367 := bstep (se 1 (by rfl) ⟨2107025, by rfl⟩ : syracuseStep 2809367 = 4214051) B4214051
theorem B1875479 : Blo 1248442 1875479 := bstep (se 1 (by rfl) ⟨1406609, by rfl⟩ : syracuseStep 1875479 = 2813219) B2813219
theorem B1875545 : Blo 1248442 1875545 := bstep (se 2 (by rfl) ⟨703329, by rfl⟩ : syracuseStep 1875545 = 1406659) B1406659
theorem B2670259 : Blo 1248442 2670259 := bstep (se 1 (by rfl) ⟨2002694, by rfl⟩ : syracuseStep 2670259 = 4005389) B4005389
theorem B2809547 : Blo 1248442 2809547 := bstep (se 1 (by rfl) ⟨2107160, by rfl⟩ : syracuseStep 2809547 = 4214321) B4214321
theorem B1875659 : Blo 1248442 1875659 := bstep (se 1 (by rfl) ⟨1406744, by rfl⟩ : syracuseStep 1875659 = 2813489) B2813489
theorem B2809601 : Blo 1248442 2809601 := bstep (se 2 (by rfl) ⟨1053600, by rfl⟩ : syracuseStep 2809601 = 2107201) B2107201
theorem B1425163 : Blo 1248442 1425163 := bstep (se 1 (by rfl) ⟨1068872, by rfl⟩ : syracuseStep 1425163 = 2137745) B2137745
theorem B5062445 : Blo 1248442 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B1580887 : Blo 1248442 1580887 := bstep (se 1 (by rfl) ⟨1185665, by rfl⟩ : syracuseStep 1580887 = 2371331) B2371331
theorem B6758275 : Blo 1248442 6758275 := bstep (se 1 (by rfl) ⟨5068706, by rfl⟩ : syracuseStep 6758275 = 10137413) B10137413
theorem B4218803 : Blo 1248442 4218803 := bstep (se 1 (by rfl) ⟨3164102, by rfl⟩ : syracuseStep 4218803 = 6328205) B6328205
theorem B3555265 : Blo 1248442 3555265 := bstep (se 2 (by rfl) ⟨1333224, by rfl⟩ : syracuseStep 3555265 = 2666449) B2666449
theorem B2809817 : Blo 1248442 2809817 := bstep (se 2 (by rfl) ⟨1053681, by rfl⟩ : syracuseStep 2809817 = 2107363) B2107363
theorem B2809871 : Blo 1248442 2809871 := bstep (se 1 (by rfl) ⟨2107403, by rfl⟩ : syracuseStep 2809871 = 4214807) B4214807
theorem B2252815 : Blo 1248442 2252815 := bstep (se 1 (by rfl) ⟨1689611, by rfl⟩ : syracuseStep 2252815 = 3379223) B3379223
theorem B2809889 : Blo 1248442 2809889 := bstep (se 2 (by rfl) ⟨1053708, by rfl⟩ : syracuseStep 2809889 = 2107417) B2107417
theorem B1581115 : Blo 1248442 1581115 := bstep (se 1 (by rfl) ⟨1185836, by rfl⟩ : syracuseStep 1581115 = 2371673) B2371673
theorem B3162199 : Blo 1248442 3162199 := bstep (se 1 (by rfl) ⟨2371649, by rfl⟩ : syracuseStep 3162199 = 4743299) B4743299
theorem B7119049 : Blo 1248442 7119049 := bstep (se 2 (by rfl) ⟨2669643, by rfl⟩ : syracuseStep 7119049 = 5339287) B5339287
theorem B27025649 : Blo 1248442 27025649 := bstep (se 2 (by rfl) ⟨10134618, by rfl⟩ : syracuseStep 27025649 = 20269237) B20269237
theorem B1777963 : Blo 1248442 1777963 := bstep (se 1 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 1777963 = 2666945) B2666945
theorem B1802569 : Blo 1248442 1802569 := bstep (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) B1351927
theorem B2810231 : Blo 1248442 2810231 := bstep (se 1 (by rfl) ⟨2107673, by rfl⟩ : syracuseStep 2810231 = 4215347) B4215347
theorem B3162503 : Blo 1248442 3162503 := bstep (se 1 (by rfl) ⟨2371877, by rfl⟩ : syracuseStep 3162503 = 4743755) B4743755
theorem B14418323 : Blo 1248442 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B4219289 : Blo 1248442 4219289 := bstep (se 2 (by rfl) ⟨1582233, by rfl⟩ : syracuseStep 4219289 = 3164467) B3164467
theorem B7602617 : Blo 1248442 7602617 := bstep (se 2 (by rfl) ⟨2850981, by rfl⟩ : syracuseStep 7602617 = 5701963) B5701963
theorem B7209437 : Blo 1248442 7209437 := bstep (se 3 (by rfl) ⟨1351769, by rfl⟩ : syracuseStep 7209437 = 2703539) B2703539
theorem B3424769 : Blo 1248442 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B3162635 : Blo 1248442 3162635 := bstep (se 1 (by rfl) ⟨2371976, by rfl⟩ : syracuseStep 3162635 = 4743953) B4743953
theorem B2810411 : Blo 1248442 2810411 := bstep (se 1 (by rfl) ⟨2107808, by rfl⟩ : syracuseStep 2810411 = 4215617) B4215617
theorem B6324803 : Blo 1248442 6324803 := bstep (se 1 (by rfl) ⟨4743602, by rfl⟩ : syracuseStep 6324803 = 9487205) B9487205
theorem B6005315 : Blo 1248442 6005315 := bstep (se 1 (by rfl) ⟨4503986, by rfl⟩ : syracuseStep 6005315 = 9007973) B9007973
theorem B1712911 : Blo 1248442 1712911 := bstep (se 1 (by rfl) ⟨1284683, by rfl⟩ : syracuseStep 1712911 = 2569367) B2569367
theorem B6325127 : Blo 1248442 6325127 := bstep (se 1 (by rfl) ⟨4743845, by rfl⟩ : syracuseStep 6325127 = 9487691) B9487691
theorem B2810771 : Blo 1248442 2810771 := bstep (se 1 (by rfl) ⟨2108078, by rfl⟩ : syracuseStep 2810771 = 4216157) B4216157
theorem B7111577 : Blo 1248442 7111577 := bstep (se 2 (by rfl) ⟨2666841, by rfl⟩ : syracuseStep 7111577 = 5333683) B5333683
theorem B4506553 : Blo 1248442 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B2810825 : Blo 1248442 2810825 := bstep (se 2 (by rfl) ⟨1054059, by rfl⟩ : syracuseStep 2810825 = 2108119) B2108119
theorem B1582087 : Blo 1248442 1582087 := bstep (se 1 (by rfl) ⟨1186565, by rfl⟩ : syracuseStep 1582087 = 2373131) B2373131
theorem B3163151 : Blo 1248442 3163151 := bstep (se 1 (by rfl) ⟨2372363, by rfl⟩ : syracuseStep 3163151 = 4744727) B4744727
theorem B3556381 : Blo 1248442 3556381 := bstep (se 3 (by rfl) ⟨666821, by rfl⟩ : syracuseStep 3556381 = 1333643) B1333643
theorem B4219991 : Blo 1248442 4219991 := bstep (se 1 (by rfl) ⟨3164993, by rfl⟩ : syracuseStep 4219991 = 6329987) B6329987
theorem B1999991 : Blo 1248442 1999991 := bstep (se 1 (by rfl) ⟨1499993, by rfl⟩ : syracuseStep 1999991 = 2999987) B2999987
theorem B3163283 : Blo 1248442 3163283 := bstep (se 1 (by rfl) ⟨2372462, by rfl⟩ : syracuseStep 3163283 = 4744925) B4744925
theorem B3556723 : Blo 1248442 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B1779079 : Blo 1248442 1779079 := bstep (se 1 (by rfl) ⟨1334309, by rfl⟩ : syracuseStep 1779079 = 2668619) B2668619
theorem B2999699 : Blo 1248442 2999699 := bstep (se 1 (by rfl) ⟨2249774, by rfl⟩ : syracuseStep 2999699 = 4499549) B4499549
theorem B1582507 : Blo 1248442 1582507 := bstep (se 1 (by rfl) ⟨1186880, by rfl⟩ : syracuseStep 1582507 = 2373761) B2373761
theorem B3606059 : Blo 1248442 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B24053317 : Blo 1248442 24053317 := bstep (se 4 (by rfl) ⟨2254998, by rfl⟩ : syracuseStep 24053317 = 4509997) B4509997
theorem B10667639 : Blo 1248442 10667639 := bstep (se 1 (by rfl) ⟨8000729, by rfl⟩ : syracuseStep 10667639 = 16001459) B16001459
theorem B10815095 : Blo 1248442 10815095 := bstep (se 1 (by rfl) ⟨8111321, by rfl⟩ : syracuseStep 10815095 = 16222643) B16222643
theorem B2811527 : Blo 1248442 2811527 := bstep (se 1 (by rfl) ⟨2108645, by rfl⟩ : syracuseStep 2811527 = 4217291) B4217291
theorem B9488177 : Blo 1248442 9488177 := bstep (se 2 (by rfl) ⟨3558066, by rfl⟩ : syracuseStep 9488177 = 7116133) B7116133
theorem B2811707 : Blo 1248442 2811707 := bstep (se 1 (by rfl) ⟨2108780, by rfl⟩ : syracuseStep 2811707 = 4217561) B4217561
theorem B6752089 : Blo 1248442 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B2107255 : Blo 1248442 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B2811833 : Blo 1248442 2811833 := bstep (se 2 (by rfl) ⟨1054437, by rfl⟩ : syracuseStep 2811833 = 2108875) B2108875
theorem B2107451 : Blo 1248442 2107451 := bstep (se 1 (by rfl) ⟨1580588, by rfl⟩ : syracuseStep 2107451 = 3161177) B3161177
theorem B3000505 : Blo 1248442 3000505 := bstep (se 2 (by rfl) ⟨1125189, by rfl⟩ : syracuseStep 3000505 = 2250379) B2250379
theorem B1779899 : Blo 1248442 1779899 := bstep (se 1 (by rfl) ⟨1334924, by rfl⟩ : syracuseStep 1779899 = 2669849) B2669849
theorem B8554697 : Blo 1248442 8554697 := bstep (se 2 (by rfl) ⟨3208011, by rfl⟩ : syracuseStep 8554697 = 6416023) B6416023
theorem B3164417 : Blo 1248442 3164417 := bstep (se 2 (by rfl) ⟨1186656, by rfl⟩ : syracuseStep 3164417 = 2373313) B2373313
theorem B2812175 : Blo 1248442 2812175 := bstep (se 1 (by rfl) ⟨2109131, by rfl⟩ : syracuseStep 2812175 = 4218263) B4218263
theorem B2812193 : Blo 1248442 2812193 := bstep (se 2 (by rfl) ⟨1054572, by rfl⟩ : syracuseStep 2812193 = 2109145) B2109145
theorem B1501483 : Blo 1248442 1501483 := bstep (se 1 (by rfl) ⟨1126112, by rfl⟩ : syracuseStep 1501483 = 2252225) B2252225
theorem B12814723 : Blo 1248442 12814723 := bstep (se 1 (by rfl) ⟨9611042, by rfl⟩ : syracuseStep 12814723 = 19222085) B19222085
theorem B2107849 : Blo 1248442 2107849 := bstep (se 2 (by rfl) ⟨790443, by rfl⟩ : syracuseStep 2107849 = 1580887) B1580887
theorem B3000833 : Blo 1248442 3000833 := bstep (se 2 (by rfl) ⟨1125312, by rfl⟩ : syracuseStep 3000833 = 2250625) B2250625
theorem B14240285 : Blo 1248442 14240285 := bstep (se 3 (by rfl) ⟨2670053, by rfl⟩ : syracuseStep 14240285 = 5340107) B5340107
theorem B2812535 : Blo 1248442 2812535 := bstep (se 1 (by rfl) ⟨2109401, by rfl⟩ : syracuseStep 2812535 = 4218803) B4218803
theorem B3164791 : Blo 1248442 3164791 := bstep (se 1 (by rfl) ⟨2373593, by rfl⟩ : syracuseStep 3164791 = 4747187) B4747187
theorem B2001593 : Blo 1248442 2001593 := bstep (se 2 (by rfl) ⟨750597, by rfl⟩ : syracuseStep 2001593 = 1501195) B1501195
theorem B2534159 : Blo 1248442 2534159 := bstep (se 1 (by rfl) ⟨1900619, by rfl⟩ : syracuseStep 2534159 = 3801239) B3801239
theorem B3001121 : Blo 1248442 3001121 := bstep (se 2 (by rfl) ⟨1125420, by rfl⟩ : syracuseStep 3001121 = 2250841) B2250841
theorem B2812715 : Blo 1248442 2812715 := bstep (se 1 (by rfl) ⟨2109536, by rfl⟩ : syracuseStep 2812715 = 4219073) B4219073
theorem B3607355 : Blo 1248442 3607355 := bstep (se 1 (by rfl) ⟨2705516, by rfl⟩ : syracuseStep 3607355 = 5411033) B5411033
theorem B4213619 : Blo 1248442 4213619 := bstep (se 1 (by rfl) ⟨3160214, by rfl⟩ : syracuseStep 4213619 = 6320429) B6320429
theorem B2108551 : Blo 1248442 2108551 := bstep (se 1 (by rfl) ⟨1581413, by rfl⟩ : syracuseStep 2108551 = 3162827) B3162827
theorem B2813075 : Blo 1248442 2813075 := bstep (se 1 (by rfl) ⟨2109806, by rfl⟩ : syracuseStep 2813075 = 4219613) B4219613
theorem B2002105 : Blo 1248442 2002105 := bstep (se 2 (by rfl) ⟨750789, by rfl⟩ : syracuseStep 2002105 = 1501579) B1501579
theorem B1248443 : Blo 1248442 1248443 := bstep (se 1 (by rfl) ⟨936332, by rfl⟩ : syracuseStep 1248443 = 1872665) B1872665
theorem B2813129 : Blo 1248442 2813129 := bstep (se 2 (by rfl) ⟨1054923, by rfl⟩ : syracuseStep 2813129 = 2109847) B2109847
theorem B12012781 : Blo 1248442 12012781 := bstep (se 3 (by rfl) ⟨2252396, by rfl⟩ : syracuseStep 12012781 = 4504793) B4504793
theorem B1248519 : Blo 1248442 1248519 := bstep (se 1 (by rfl) ⟨936389, by rfl⟩ : syracuseStep 1248519 = 1872779) B1872779
theorem B1248527 : Blo 1248442 1248527 := bstep (se 1 (by rfl) ⟨936395, by rfl⟩ : syracuseStep 1248527 = 1872791) B1872791
theorem B54013229 : Blo 1248442 54013229 := bstep (se 3 (by rfl) ⟨10127480, by rfl⟩ : syracuseStep 54013229 = 20254961) B20254961
theorem B1248571 : Blo 1248442 1248571 := bstep (se 1 (by rfl) ⟨936428, by rfl⟩ : syracuseStep 1248571 = 1872857) B1872857
theorem B1248647 : Blo 1248442 1248647 := bstep (se 1 (by rfl) ⟨936485, by rfl⟩ : syracuseStep 1248647 = 1872971) B1872971
theorem B3001735 : Blo 1248442 3001735 := bstep (se 1 (by rfl) ⟨2251301, by rfl⟩ : syracuseStep 3001735 = 4502603) B4502603
theorem B1248655 : Blo 1248442 1248655 := bstep (se 1 (by rfl) ⟨936491, by rfl⟩ : syracuseStep 1248655 = 1872983) B1872983
theorem B1248699 : Blo 1248442 1248699 := bstep (se 1 (by rfl) ⟨936524, by rfl⟩ : syracuseStep 1248699 = 1873049) B1873049
theorem B1248775 : Blo 1248442 1248775 := bstep (se 1 (by rfl) ⟨936581, by rfl⟩ : syracuseStep 1248775 = 1873163) B1873163
theorem B1248783 : Blo 1248442 1248783 := bstep (se 1 (by rfl) ⟨936587, by rfl⟩ : syracuseStep 1248783 = 1873175) B1873175
theorem B15199787 : Blo 1248442 15199787 := bstep (se 1 (by rfl) ⟨11399840, by rfl⟩ : syracuseStep 15199787 = 22799681) B22799681
theorem B3206699 : Blo 1248442 3206699 := bstep (se 1 (by rfl) ⟨2405024, by rfl⟩ : syracuseStep 3206699 = 4810049) B4810049
theorem B1248827 : Blo 1248442 1248827 := bstep (se 1 (by rfl) ⟨936620, by rfl⟩ : syracuseStep 1248827 = 1873241) B1873241
theorem B16019045 : Blo 1248442 16019045 := bstep (se 4 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 16019045 = 3003571) B3003571
theorem B1248903 : Blo 1248442 1248903 := bstep (se 1 (by rfl) ⟨936677, by rfl⟩ : syracuseStep 1248903 = 1873355) B1873355
theorem B1248911 : Blo 1248442 1248911 := bstep (se 1 (by rfl) ⟨936683, by rfl⟩ : syracuseStep 1248911 = 1873367) B1873367
theorem B1248955 : Blo 1248442 1248955 := bstep (se 1 (by rfl) ⟨936716, by rfl⟩ : syracuseStep 1248955 = 1873433) B1873433
theorem B2027209 : Blo 1248442 2027209 := bstep (se 2 (by rfl) ⟨760203, by rfl⟩ : syracuseStep 2027209 = 1520407) B1520407
theorem B1404679 : Blo 1248442 1404679 := bstep (se 1 (by rfl) ⟨1053509, by rfl⟩ : syracuseStep 1404679 = 2107019) B2107019
theorem B1249031 : Blo 1248442 1249031 := bstep (se 1 (by rfl) ⟨936773, by rfl⟩ : syracuseStep 1249031 = 1873547) B1873547
theorem B1249039 : Blo 1248442 1249039 := bstep (se 1 (by rfl) ⟨936779, by rfl⟩ : syracuseStep 1249039 = 1873559) B1873559
theorem B2109199 : Blo 1248442 2109199 := bstep (se 1 (by rfl) ⟨1581899, by rfl⟩ : syracuseStep 2109199 = 3163799) B3163799
theorem B1249083 : Blo 1248442 1249083 := bstep (se 1 (by rfl) ⟨936812, by rfl⟩ : syracuseStep 1249083 = 1873625) B1873625
theorem B1249159 : Blo 1248442 1249159 := bstep (se 1 (by rfl) ⟨936869, by rfl⟩ : syracuseStep 1249159 = 1873739) B1873739
theorem B2002823 : Blo 1248442 2002823 := bstep (se 1 (by rfl) ⟨1502117, by rfl⟩ : syracuseStep 2002823 = 3004235) B3004235
theorem B1249167 : Blo 1248442 1249167 := bstep (se 1 (by rfl) ⟨936875, by rfl⟩ : syracuseStep 1249167 = 1873751) B1873751
theorem B2371513 : Blo 1248442 2371513 := bstep (se 2 (by rfl) ⟨889317, by rfl⟩ : syracuseStep 2371513 = 1778635) B1778635
theorem B1404859 : Blo 1248442 1404859 := bstep (se 1 (by rfl) ⟨1053644, by rfl⟩ : syracuseStep 1404859 = 2107289) B2107289
theorem B1249211 : Blo 1248442 1249211 := bstep (se 1 (by rfl) ⟨936908, by rfl⟩ : syracuseStep 1249211 = 1873817) B1873817
theorem B1249287 : Blo 1248442 1249287 := bstep (se 1 (by rfl) ⟨936965, by rfl⟩ : syracuseStep 1249287 = 1873931) B1873931
theorem B7999499 : Blo 1248442 7999499 := bstep (se 1 (by rfl) ⟨5999624, by rfl⟩ : syracuseStep 7999499 = 11999249) B11999249
theorem B1249295 : Blo 1248442 1249295 := bstep (se 1 (by rfl) ⟨936971, by rfl⟩ : syracuseStep 1249295 = 1873943) B1873943
theorem B3559457 : Blo 1248442 3559457 := bstep (se 2 (by rfl) ⟨1334796, by rfl⟩ : syracuseStep 3559457 = 2669593) B2669593
theorem B7598123 : Blo 1248442 7598123 := bstep (se 1 (by rfl) ⟨5698592, by rfl⟩ : syracuseStep 7598123 = 11397185) B11397185
theorem B1249339 : Blo 1248442 1249339 := bstep (se 1 (by rfl) ⟨937004, by rfl⟩ : syracuseStep 1249339 = 1874009) B1874009
theorem B3469373 : Blo 1248442 3469373 := bstep (se 3 (by rfl) ⟨650507, by rfl⟩ : syracuseStep 3469373 = 1301015) B1301015
theorem B13692989 : Blo 1248442 13692989 := bstep (se 3 (by rfl) ⟨2567435, by rfl⟩ : syracuseStep 13692989 = 5134871) B5134871
theorem B1249415 : Blo 1248442 1249415 := bstep (se 1 (by rfl) ⟨937061, by rfl⟩ : syracuseStep 1249415 = 1874123) B1874123
theorem B1249423 : Blo 1248442 1249423 := bstep (se 1 (by rfl) ⟨937067, by rfl⟩ : syracuseStep 1249423 = 1874135) B1874135
theorem B3559571 : Blo 1248442 3559571 := bstep (se 1 (by rfl) ⟨2669678, by rfl⟩ : syracuseStep 3559571 = 5339357) B5339357
theorem B1249467 : Blo 1248442 1249467 := bstep (se 1 (by rfl) ⟨937100, by rfl⟩ : syracuseStep 1249467 = 1874201) B1874201
theorem B1249543 : Blo 1248442 1249543 := bstep (se 1 (by rfl) ⟨937157, by rfl⟩ : syracuseStep 1249543 = 1874315) B1874315
theorem B2371855 : Blo 1248442 2371855 := bstep (se 1 (by rfl) ⟨1778891, by rfl⟩ : syracuseStep 2371855 = 3557783) B3557783
theorem B5337359 : Blo 1248442 5337359 := bstep (se 1 (by rfl) ⟨4003019, by rfl⟩ : syracuseStep 5337359 = 8006039) B8006039
theorem B1249551 : Blo 1248442 1249551 := bstep (se 1 (by rfl) ⟨937163, by rfl⟩ : syracuseStep 1249551 = 1874327) B1874327
theorem B2109739 : Blo 1248442 2109739 := bstep (se 1 (by rfl) ⟨1582304, by rfl⟩ : syracuseStep 2109739 = 3164609) B3164609
theorem B1249595 : Blo 1248442 1249595 := bstep (se 1 (by rfl) ⟨937196, by rfl⟩ : syracuseStep 1249595 = 1874393) B1874393
theorem B6328691 : Blo 1248442 6328691 := bstep (se 1 (by rfl) ⟨4746518, by rfl⟩ : syracuseStep 6328691 = 9493037) B9493037
theorem B1249671 : Blo 1248442 1249671 := bstep (se 1 (by rfl) ⟨937253, by rfl⟩ : syracuseStep 1249671 = 1874507) B1874507
theorem B1405327 : Blo 1248442 1405327 := bstep (se 1 (by rfl) ⟨1053995, by rfl⟩ : syracuseStep 1405327 = 2107991) B2107991
theorem B1249679 : Blo 1248442 1249679 := bstep (se 1 (by rfl) ⟨937259, by rfl⟩ : syracuseStep 1249679 = 1874519) B1874519
theorem B4747673 : Blo 1248442 4747673 := bstep (se 2 (by rfl) ⟨1780377, by rfl⟩ : syracuseStep 4747673 = 3560755) B3560755
theorem B2109881 : Blo 1248442 2109881 := bstep (se 2 (by rfl) ⟨791205, by rfl⟩ : syracuseStep 2109881 = 1582411) B1582411
theorem B1249723 : Blo 1248442 1249723 := bstep (se 1 (by rfl) ⟨937292, by rfl⟩ : syracuseStep 1249723 = 1874585) B1874585
theorem B1249799 : Blo 1248442 1249799 := bstep (se 1 (by rfl) ⟨937349, by rfl⟩ : syracuseStep 1249799 = 1874699) B1874699
theorem B4870667 : Blo 1248442 4870667 := bstep (se 1 (by rfl) ⟨3653000, by rfl⟩ : syracuseStep 4870667 = 7306001) B7306001
theorem B1249807 : Blo 1248442 1249807 := bstep (se 1 (by rfl) ⟨937355, by rfl⟩ : syracuseStep 1249807 = 1874711) B1874711
theorem B6754859 : Blo 1248442 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B1249851 : Blo 1248442 1249851 := bstep (se 1 (by rfl) ⟨937388, by rfl⟩ : syracuseStep 1249851 = 1874777) B1874777
theorem B4002365 : Blo 1248442 4002365 := bstep (se 3 (by rfl) ⟨750443, by rfl⟩ : syracuseStep 4002365 = 1500887) B1500887
theorem B1249927 : Blo 1248442 1249927 := bstep (se 1 (by rfl) ⟨937445, by rfl⟩ : syracuseStep 1249927 = 1874891) B1874891
theorem B1249935 : Blo 1248442 1249935 := bstep (se 1 (by rfl) ⟨937451, by rfl⟩ : syracuseStep 1249935 = 1874903) B1874903
theorem B1249979 : Blo 1248442 1249979 := bstep (se 1 (by rfl) ⟨937484, by rfl⟩ : syracuseStep 1249979 = 1874969) B1874969
theorem B1250055 : Blo 1248442 1250055 := bstep (se 1 (by rfl) ⟨937541, by rfl⟩ : syracuseStep 1250055 = 1875083) B1875083
theorem B3379979 : Blo 1248442 3379979 := bstep (se 1 (by rfl) ⟨2534984, by rfl⟩ : syracuseStep 3379979 = 5069969) B5069969
theorem B17330959 : Blo 1248442 17330959 := bstep (se 1 (by rfl) ⟨12998219, by rfl⟩ : syracuseStep 17330959 = 25996439) B25996439
theorem B1250063 : Blo 1248442 1250063 := bstep (se 1 (by rfl) ⟨937547, by rfl⟩ : syracuseStep 1250063 = 1875095) B1875095
theorem B1872683 : Blo 1248442 1872683 := bstep (se 1 (by rfl) ⟨1404512, by rfl⟩ : syracuseStep 1872683 = 2809025) B2809025
theorem B1250107 : Blo 1248442 1250107 := bstep (se 1 (by rfl) ⟨937580, by rfl⟩ : syracuseStep 1250107 = 1875161) B1875161
theorem B1872713 : Blo 1248442 1872713 := bstep (se 2 (by rfl) ⟨702267, by rfl⟩ : syracuseStep 1872713 = 1404535) B1404535
theorem B6329177 : Blo 1248442 6329177 := bstep (se 2 (by rfl) ⟨2373441, by rfl⟩ : syracuseStep 6329177 = 4746883) B4746883
theorem B2741111 : Blo 1248442 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B1405831 : Blo 1248442 1405831 := bstep (se 1 (by rfl) ⟨1054373, by rfl⟩ : syracuseStep 1405831 = 2108747) B2108747
theorem B1250183 : Blo 1248442 1250183 := bstep (se 1 (by rfl) ⟨937637, by rfl⟩ : syracuseStep 1250183 = 1875275) B1875275
theorem B1250191 : Blo 1248442 1250191 := bstep (se 1 (by rfl) ⟨937643, by rfl⟩ : syracuseStep 1250191 = 1875287) B1875287
theorem B3560345 : Blo 1248442 3560345 := bstep (se 2 (by rfl) ⟨1335129, by rfl⟩ : syracuseStep 3560345 = 2670259) B2670259
theorem B1872827 : Blo 1248442 1872827 := bstep (se 1 (by rfl) ⟨1404620, by rfl⟩ : syracuseStep 1872827 = 2809241) B2809241
theorem B1250235 : Blo 1248442 1250235 := bstep (se 1 (by rfl) ⟨937676, by rfl⟩ : syracuseStep 1250235 = 1875353) B1875353
theorem B1872887 : Blo 1248442 1872887 := bstep (se 1 (by rfl) ⟨1404665, by rfl⟩ : syracuseStep 1872887 = 2809331) B2809331
theorem B1250311 : Blo 1248442 1250311 := bstep (se 1 (by rfl) ⟨937733, by rfl⟩ : syracuseStep 1250311 = 1875467) B1875467
theorem B15209477 : Blo 1248442 15209477 := bstep (se 4 (by rfl) ⟨1425888, by rfl⟩ : syracuseStep 15209477 = 2851777) B2851777
theorem B1872911 : Blo 1248442 1872911 := bstep (se 1 (by rfl) ⟨1404683, by rfl⟩ : syracuseStep 1872911 = 2809367) B2809367
theorem B1250319 : Blo 1248442 1250319 := bstep (se 1 (by rfl) ⟨937739, by rfl⟩ : syracuseStep 1250319 = 1875479) B1875479
theorem B1872953 : Blo 1248442 1872953 := bstep (se 2 (by rfl) ⟨702357, by rfl⟩ : syracuseStep 1872953 = 1404715) B1404715
theorem B1406011 : Blo 1248442 1406011 := bstep (se 1 (by rfl) ⟨1054508, by rfl⟩ : syracuseStep 1406011 = 2109017) B2109017
theorem B1250363 : Blo 1248442 1250363 := bstep (se 1 (by rfl) ⟨937772, by rfl⟩ : syracuseStep 1250363 = 1875545) B1875545
theorem B6321239 : Blo 1248442 6321239 := bstep (se 1 (by rfl) ⟨4740929, by rfl⟩ : syracuseStep 6321239 = 9481859) B9481859
theorem B16233605 : Blo 1248442 16233605 := bstep (se 4 (by rfl) ⟨1521900, by rfl⟩ : syracuseStep 16233605 = 3043801) B3043801
theorem B1873031 : Blo 1248442 1873031 := bstep (se 1 (by rfl) ⟨1404773, by rfl⟩ : syracuseStep 1873031 = 2809547) B2809547
theorem B2372743 : Blo 1248442 2372743 := bstep (se 1 (by rfl) ⟨1779557, by rfl⟩ : syracuseStep 2372743 = 3559115) B3559115
theorem B1250439 : Blo 1248442 1250439 := bstep (se 1 (by rfl) ⟨937829, by rfl⟩ : syracuseStep 1250439 = 1875659) B1875659
theorem B1873067 : Blo 1248442 1873067 := bstep (se 1 (by rfl) ⟨1404800, by rfl⟩ : syracuseStep 1873067 = 2809601) B2809601
theorem B1873097 : Blo 1248442 1873097 := bstep (se 2 (by rfl) ⟨702411, by rfl⟩ : syracuseStep 1873097 = 1404823) B1404823
theorem B4740353 : Blo 1248442 4740353 := bstep (se 2 (by rfl) ⟨1777632, by rfl⟩ : syracuseStep 4740353 = 3555265) B3555265
theorem B2667791 : Blo 1248442 2667791 := bstep (se 1 (by rfl) ⟨2000843, by rfl⟩ : syracuseStep 2667791 = 4001687) B4001687
theorem B1873211 : Blo 1248442 1873211 := bstep (se 1 (by rfl) ⟨1404908, by rfl⟩ : syracuseStep 1873211 = 2809817) B2809817
theorem B6002009 : Blo 1248442 6002009 := bstep (se 2 (by rfl) ⟨2250753, by rfl⟩ : syracuseStep 6002009 = 4501507) B4501507
theorem B1873271 : Blo 1248442 1873271 := bstep (se 1 (by rfl) ⟨1404953, by rfl⟩ : syracuseStep 1873271 = 2809907) B2809907
theorem B1873295 : Blo 1248442 1873295 := bstep (se 1 (by rfl) ⟨1404971, by rfl⟩ : syracuseStep 1873295 = 2809943) B2809943
theorem B1267087 : Blo 1248442 1267087 := bstep (se 1 (by rfl) ⟨950315, by rfl⟩ : syracuseStep 1267087 = 1900631) B1900631
theorem B4216211 : Blo 1248442 4216211 := bstep (se 1 (by rfl) ⟨3162158, by rfl⟩ : syracuseStep 4216211 = 6324317) B6324317
theorem B1873337 : Blo 1248442 1873337 := bstep (se 2 (by rfl) ⟨702501, by rfl⟩ : syracuseStep 1873337 = 1405003) B1405003
theorem B24016337 : Blo 1248442 24016337 := bstep (se 2 (by rfl) ⟨9006126, by rfl⟩ : syracuseStep 24016337 = 18012253) B18012253
theorem B1873415 : Blo 1248442 1873415 := bstep (se 1 (by rfl) ⟨1405061, by rfl⟩ : syracuseStep 1873415 = 2810123) B2810123
theorem B3798539 : Blo 1248442 3798539 := bstep (se 1 (by rfl) ⟨2848904, by rfl⟩ : syracuseStep 3798539 = 5697809) B5697809
theorem B1406479 : Blo 1248442 1406479 := bstep (se 1 (by rfl) ⟨1054859, by rfl⟩ : syracuseStep 1406479 = 2109719) B2109719
theorem B1873451 : Blo 1248442 1873451 := bstep (se 1 (by rfl) ⟨1405088, by rfl⟩ : syracuseStep 1873451 = 2810177) B2810177
theorem B6321725 : Blo 1248442 6321725 := bstep (se 3 (by rfl) ⟨1185323, by rfl⟩ : syracuseStep 6321725 = 2370647) B2370647
theorem B1873481 : Blo 1248442 1873481 := bstep (se 2 (by rfl) ⟨702555, by rfl⟩ : syracuseStep 1873481 = 1405111) B1405111
theorem B7116407 : Blo 1248442 7116407 := bstep (se 1 (by rfl) ⟨5337305, by rfl⟩ : syracuseStep 7116407 = 10674611) B10674611
theorem B1873595 : Blo 1248442 1873595 := bstep (se 1 (by rfl) ⟨1405196, by rfl⟩ : syracuseStep 1873595 = 2810393) B2810393
theorem B1873655 : Blo 1248442 1873655 := bstep (se 1 (by rfl) ⟨1405241, by rfl⟩ : syracuseStep 1873655 = 2810483) B2810483
theorem B1873679 : Blo 1248442 1873679 := bstep (se 1 (by rfl) ⟨1405259, by rfl⟩ : syracuseStep 1873679 = 2810519) B2810519
theorem B1873721 : Blo 1248442 1873721 := bstep (se 2 (by rfl) ⟨702645, by rfl⟩ : syracuseStep 1873721 = 1405291) B1405291
theorem B7116659 : Blo 1248442 7116659 := bstep (se 1 (by rfl) ⟨5337494, by rfl⟩ : syracuseStep 7116659 = 10674989) B10674989
theorem B1873799 : Blo 1248442 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B1873835 : Blo 1248442 1873835 := bstep (se 1 (by rfl) ⟨1405376, by rfl⟩ : syracuseStep 1873835 = 2810753) B2810753
theorem B1873865 : Blo 1248442 1873865 := bstep (se 2 (by rfl) ⟨702699, by rfl⟩ : syracuseStep 1873865 = 1405399) B1405399
theorem B1873979 : Blo 1248442 1873979 := bstep (se 1 (by rfl) ⟨1405484, by rfl⟩ : syracuseStep 1873979 = 2810969) B2810969
theorem B1874039 : Blo 1248442 1874039 := bstep (se 1 (by rfl) ⟨1405529, by rfl⟩ : syracuseStep 1874039 = 2811059) B2811059
theorem B4503671 : Blo 1248442 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B1874063 : Blo 1248442 1874063 := bstep (se 1 (by rfl) ⟨1405547, by rfl⟩ : syracuseStep 1874063 = 2811095) B2811095
theorem B1874105 : Blo 1248442 1874105 := bstep (se 2 (by rfl) ⟨702789, by rfl⟩ : syracuseStep 1874105 = 1405579) B1405579
theorem B1874183 : Blo 1248442 1874183 := bstep (se 1 (by rfl) ⟨1405637, by rfl⟩ : syracuseStep 1874183 = 2811275) B2811275
theorem B20257037 : Blo 1248442 20257037 := bstep (se 3 (by rfl) ⟨3798194, by rfl⟩ : syracuseStep 20257037 = 7596389) B7596389
theorem B1874219 : Blo 1248442 1874219 := bstep (se 1 (by rfl) ⟨1405664, by rfl⟩ : syracuseStep 1874219 = 2811329) B2811329
theorem B1874249 : Blo 1248442 1874249 := bstep (se 2 (by rfl) ⟨702843, by rfl⟩ : syracuseStep 1874249 = 1405687) B1405687
theorem B4741523 : Blo 1248442 4741523 := bstep (se 1 (by rfl) ⟨3556142, by rfl⟩ : syracuseStep 4741523 = 7112285) B7112285
theorem B10680761 : Blo 1248442 10680761 := bstep (se 2 (by rfl) ⟨4005285, by rfl⟩ : syracuseStep 10680761 = 8010571) B8010571
theorem B1874363 : Blo 1248442 1874363 := bstep (se 1 (by rfl) ⟨1405772, by rfl⟩ : syracuseStep 1874363 = 2811545) B2811545
theorem B1874423 : Blo 1248442 1874423 := bstep (se 1 (by rfl) ⟨1405817, by rfl⟩ : syracuseStep 1874423 = 2811635) B2811635
theorem B4004363 : Blo 1248442 4004363 := bstep (se 1 (by rfl) ⟨3003272, by rfl⟩ : syracuseStep 4004363 = 6006545) B6006545
theorem B1874447 : Blo 1248442 1874447 := bstep (se 1 (by rfl) ⟨1405835, by rfl⟩ : syracuseStep 1874447 = 2811671) B2811671
theorem B1874489 : Blo 1248442 1874489 := bstep (se 2 (by rfl) ⟨702933, by rfl⟩ : syracuseStep 1874489 = 1405867) B1405867
theorem B3160691 : Blo 1248442 3160691 := bstep (se 1 (by rfl) ⟨2370518, by rfl⟩ : syracuseStep 3160691 = 4741037) B4741037
theorem B1874567 : Blo 1248442 1874567 := bstep (se 1 (by rfl) ⟨1405925, by rfl⟩ : syracuseStep 1874567 = 2811851) B2811851
theorem B1874603 : Blo 1248442 1874603 := bstep (se 1 (by rfl) ⟨1405952, by rfl⟩ : syracuseStep 1874603 = 2811905) B2811905
theorem B1874633 : Blo 1248442 1874633 := bstep (se 2 (by rfl) ⟨702987, by rfl⟩ : syracuseStep 1874633 = 1405975) B1405975
theorem B4217615 : Blo 1248442 4217615 := bstep (se 1 (by rfl) ⟨3163211, by rfl⟩ : syracuseStep 4217615 = 6326423) B6326423
theorem B16005923 : Blo 1248442 16005923 := bstep (se 1 (by rfl) ⟨12004442, by rfl⟩ : syracuseStep 16005923 = 24008885) B24008885
theorem B1874747 : Blo 1248442 1874747 := bstep (se 1 (by rfl) ⟨1406060, by rfl⟩ : syracuseStep 1874747 = 2812121) B2812121
theorem B1874807 : Blo 1248442 1874807 := bstep (se 1 (by rfl) ⟨1406105, by rfl⟩ : syracuseStep 1874807 = 2812211) B2812211
theorem B2669431 : Blo 1248442 2669431 := bstep (se 1 (by rfl) ⟨2002073, by rfl⟩ : syracuseStep 2669431 = 4004147) B4004147
theorem B4742023 : Blo 1248442 4742023 := bstep (se 1 (by rfl) ⟨3556517, by rfl⟩ : syracuseStep 4742023 = 7113035) B7113035
theorem B1874831 : Blo 1248442 1874831 := bstep (se 1 (by rfl) ⟨1406123, by rfl⟩ : syracuseStep 1874831 = 2812247) B2812247
theorem B2251705 : Blo 1248442 2251705 := bstep (se 2 (by rfl) ⟨844389, by rfl⟩ : syracuseStep 2251705 = 1688779) B1688779
theorem B1874873 : Blo 1248442 1874873 := bstep (se 2 (by rfl) ⟨703077, by rfl⟩ : syracuseStep 1874873 = 1406155) B1406155
theorem B6003665 : Blo 1248442 6003665 := bstep (se 2 (by rfl) ⟨2251374, by rfl⟩ : syracuseStep 6003665 = 4502749) B4502749
theorem B1874951 : Blo 1248442 1874951 := bstep (se 1 (by rfl) ⟨1406213, by rfl⟩ : syracuseStep 1874951 = 2812427) B2812427
theorem B4217885 : Blo 1248442 4217885 := bstep (se 3 (by rfl) ⟨790853, by rfl⟩ : syracuseStep 4217885 = 1581707) B1581707
theorem B1874987 : Blo 1248442 1874987 := bstep (se 1 (by rfl) ⟨1406240, by rfl⟩ : syracuseStep 1874987 = 2812481) B2812481
theorem B1875017 : Blo 1248442 1875017 := bstep (se 2 (by rfl) ⟨703131, by rfl⟩ : syracuseStep 1875017 = 1406263) B1406263
theorem B3161207 : Blo 1248442 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B1875131 : Blo 1248442 1875131 := bstep (se 1 (by rfl) ⟨1406348, by rfl⟩ : syracuseStep 1875131 = 2812697) B2812697
theorem B1875191 : Blo 1248442 1875191 := bstep (se 1 (by rfl) ⟨1406393, by rfl⟩ : syracuseStep 1875191 = 2812787) B2812787
theorem B1875215 : Blo 1248442 1875215 := bstep (se 1 (by rfl) ⟨1406411, by rfl⟩ : syracuseStep 1875215 = 2812823) B2812823
theorem B7118117 : Blo 1248442 7118117 := bstep (se 4 (by rfl) ⟨667323, by rfl⟩ : syracuseStep 7118117 = 1334647) B1334647
theorem B6323507 : Blo 1248442 6323507 := bstep (se 1 (by rfl) ⟨4742630, by rfl⟩ : syracuseStep 6323507 = 9485261) B9485261
theorem B1875257 : Blo 1248442 1875257 := bstep (se 2 (by rfl) ⟨703221, by rfl⟩ : syracuseStep 1875257 = 1406443) B1406443
theorem B2809223 : Blo 1248442 2809223 := bstep (se 1 (by rfl) ⟨2106917, by rfl⟩ : syracuseStep 2809223 = 4213835) B4213835
theorem B1875335 : Blo 1248442 1875335 := bstep (se 1 (by rfl) ⟨1406501, by rfl⟩ : syracuseStep 1875335 = 2813003) B2813003
theorem B1875371 : Blo 1248442 1875371 := bstep (se 1 (by rfl) ⟨1406528, by rfl⟩ : syracuseStep 1875371 = 2813057) B2813057
theorem B1875401 : Blo 1248442 1875401 := bstep (se 2 (by rfl) ⟨703275, by rfl⟩ : syracuseStep 1875401 = 1406551) B1406551
theorem B2809403 : Blo 1248442 2809403 := bstep (se 1 (by rfl) ⟨2107052, by rfl⟩ : syracuseStep 2809403 = 4214105) B4214105
theorem B1875515 : Blo 1248442 1875515 := bstep (se 1 (by rfl) ⟨1406636, by rfl⟩ : syracuseStep 1875515 = 2813273) B2813273
theorem B6323831 : Blo 1248442 6323831 := bstep (se 1 (by rfl) ⟨4742873, by rfl⟩ : syracuseStep 6323831 = 9485747) B9485747
theorem B5340791 : Blo 1248442 5340791 := bstep (se 1 (by rfl) ⟨4005593, by rfl⟩ : syracuseStep 5340791 = 8011187) B8011187
theorem B1875575 : Blo 1248442 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B1875599 : Blo 1248442 1875599 := bstep (se 1 (by rfl) ⟨1406699, by rfl⟩ : syracuseStep 1875599 = 2813399) B2813399
theorem B2530963 : Blo 1248442 2530963 := bstep (se 1 (by rfl) ⟨1898222, by rfl⟩ : syracuseStep 2530963 = 3796445) B3796445
theorem B2809529 : Blo 1248442 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B1900217 : Blo 1248442 1900217 := bstep (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) B1425163
theorem B1875641 : Blo 1248442 1875641 := bstep (se 2 (by rfl) ⟨703365, by rfl⟩ : syracuseStep 1875641 = 1406731) B1406731
theorem B1580791 : Blo 1248442 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B15998795 : Blo 1248442 15998795 := bstep (se 1 (by rfl) ⟨11999096, by rfl⟩ : syracuseStep 15998795 = 23998193) B23998193
theorem B9011033 : Blo 1248442 9011033 := bstep (se 2 (by rfl) ⟨3379137, by rfl⟩ : syracuseStep 9011033 = 6758275) B6758275
theorem B3374963 : Blo 1248442 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B2531191 : Blo 1248442 2531191 := bstep (se 1 (by rfl) ⟨1898393, by rfl⟩ : syracuseStep 2531191 = 3796787) B3796787
theorem B9486233 : Blo 1248442 9486233 := bstep (se 2 (by rfl) ⟨3557337, by rfl⟩ : syracuseStep 9486233 = 7114675) B7114675
theorem B21331997 : Blo 1248442 21331997 := bstep (se 3 (by rfl) ⟨3999749, by rfl⟩ : syracuseStep 21331997 = 7999499) B7999499
theorem B4219127 : Blo 1248442 4219127 := bstep (se 1 (by rfl) ⟨3164345, by rfl⟩ : syracuseStep 4219127 = 6328691) B6328691
theorem B5333309 : Blo 1248442 5333309 := bstep (se 3 (by rfl) ⟨999995, by rfl⟩ : syracuseStep 5333309 = 1999991) B1999991
theorem B3162473 : Blo 1248442 3162473 := bstep (se 2 (by rfl) ⟨1185927, by rfl⟩ : syracuseStep 3162473 = 2371855) B2371855
theorem B4219451 : Blo 1248442 4219451 := bstep (se 1 (by rfl) ⟨3164588, by rfl⟩ : syracuseStep 4219451 = 6329177) B6329177
theorem B1827407 : Blo 1248442 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B2810465 : Blo 1248442 2810465 := bstep (se 2 (by rfl) ⟨1053924, by rfl⟩ : syracuseStep 2810465 = 2107849) B2107849
theorem B10822403 : Blo 1248442 10822403 := bstep (se 1 (by rfl) ⟨8116802, by rfl⟩ : syracuseStep 10822403 = 16233605) B16233605
theorem B4219721 : Blo 1248442 4219721 := bstep (se 2 (by rfl) ⟨1582395, by rfl⟩ : syracuseStep 4219721 = 3164791) B3164791
theorem B1778527 : Blo 1248442 1778527 := bstep (se 1 (by rfl) ⟨1333895, by rfl⟩ : syracuseStep 1778527 = 2667791) B2667791
theorem B1999799 : Blo 1248442 1999799 := bstep (se 1 (by rfl) ⟨1499849, by rfl⟩ : syracuseStep 1999799 = 2999699) B2999699
theorem B2810807 : Blo 1248442 2810807 := bstep (se 1 (by rfl) ⟨2108105, by rfl⟩ : syracuseStep 2810807 = 4216211) B4216211
theorem B2532359 : Blo 1248442 2532359 := bstep (se 1 (by rfl) ⟨1899269, by rfl⟩ : syracuseStep 2532359 = 3798539) B3798539
theorem B7111759 : Blo 1248442 7111759 := bstep (se 1 (by rfl) ⟨5333819, by rfl⟩ : syracuseStep 7111759 = 10667639) B10667639
theorem B7210063 : Blo 1248442 7210063 := bstep (se 1 (by rfl) ⟨5407547, by rfl⟩ : syracuseStep 7210063 = 10815095) B10815095
theorem B4744271 : Blo 1248442 4744271 := bstep (se 1 (by rfl) ⟨3558203, by rfl⟩ : syracuseStep 4744271 = 7116407) B7116407
theorem B6325451 : Blo 1248442 6325451 := bstep (se 1 (by rfl) ⟨4744088, by rfl⟩ : syracuseStep 6325451 = 9488177) B9488177
theorem B4744439 : Blo 1248442 4744439 := bstep (se 1 (by rfl) ⟨3558329, by rfl⟩ : syracuseStep 4744439 = 7116659) B7116659
theorem B5703131 : Blo 1248442 5703131 := bstep (se 1 (by rfl) ⟨4277348, by rfl⟩ : syracuseStep 5703131 = 8554697) B8554697
theorem B2811401 : Blo 1248442 2811401 := bstep (se 2 (by rfl) ⟨1054275, by rfl⟩ : syracuseStep 2811401 = 2108551) B2108551
theorem B3163657 : Blo 1248442 3163657 := bstep (se 2 (by rfl) ⟨1186371, by rfl⟩ : syracuseStep 3163657 = 2372743) B2372743
theorem B7120507 : Blo 1248442 7120507 := bstep (se 1 (by rfl) ⟨5340380, by rfl⟩ : syracuseStep 7120507 = 10680761) B10680761
theorem B16017041 : Blo 1248442 16017041 := bstep (se 2 (by rfl) ⟨6006390, by rfl⟩ : syracuseStep 16017041 = 12012781) B12012781
theorem B2000555 : Blo 1248442 2000555 := bstep (se 1 (by rfl) ⟨1500416, by rfl⟩ : syracuseStep 2000555 = 3000833) B3000833
theorem B2107127 : Blo 1248442 2107127 := bstep (se 1 (by rfl) ⟨1580345, by rfl⟩ : syracuseStep 2107127 = 3160691) B3160691
theorem B2811743 : Blo 1248442 2811743 := bstep (se 1 (by rfl) ⟨2108807, by rfl⟩ : syracuseStep 2811743 = 4217615) B4217615
theorem B1689439 : Blo 1248442 1689439 := bstep (se 1 (by rfl) ⟨1267079, by rfl⟩ : syracuseStep 1689439 = 2534159) B2534159
theorem B1689449 : Blo 1248442 1689449 := bstep (se 2 (by rfl) ⟨633543, by rfl⟩ : syracuseStep 1689449 = 1267087) B1267087
theorem B2000747 : Blo 1248442 2000747 := bstep (se 1 (by rfl) ⟨1500560, by rfl⟩ : syracuseStep 2000747 = 3001121) B3001121
theorem B2811923 : Blo 1248442 2811923 := bstep (se 1 (by rfl) ⟨2108942, by rfl⟩ : syracuseStep 2811923 = 4217885) B4217885
theorem B9013277 : Blo 1248442 9013277 := bstep (se 3 (by rfl) ⟨1689989, by rfl⟩ : syracuseStep 9013277 = 3379979) B3379979
theorem B2107471 : Blo 1248442 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B4745411 : Blo 1248442 4745411 := bstep (se 1 (by rfl) ⟨3559058, by rfl⟩ : syracuseStep 4745411 = 7118117) B7118117
theorem B76900661 : Blo 1248442 76900661 := bstep (se 5 (by rfl) ⟨3604718, by rfl⟩ : syracuseStep 76900661 = 7209437) B7209437
theorem B2107721 : Blo 1248442 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B2812265 : Blo 1248442 2812265 := bstep (se 2 (by rfl) ⟨1054599, by rfl⟩ : syracuseStep 2812265 = 2109199) B2109199
theorem B6007355 : Blo 1248442 6007355 := bstep (se 1 (by rfl) ⟨4505516, by rfl⟩ : syracuseStep 6007355 = 9011033) B9011033
theorem B5065415 : Blo 1248442 5065415 := bstep (se 1 (by rfl) ⟨3799061, by rfl⟩ : syracuseStep 5065415 = 7598123) B7598123
theorem B2312915 : Blo 1248442 2312915 := bstep (se 1 (by rfl) ⟨1734686, by rfl⟩ : syracuseStep 2312915 = 3469373) B3469373
theorem B9128659 : Blo 1248442 9128659 := bstep (se 1 (by rfl) ⟨6846494, by rfl⟩ : syracuseStep 9128659 = 13692989) B13692989
theorem B2108153 : Blo 1248442 2108153 := bstep (se 2 (by rfl) ⟨790557, by rfl⟩ : syracuseStep 2108153 = 1581115) B1581115
theorem B18017099 : Blo 1248442 18017099 := bstep (se 1 (by rfl) ⟨13512824, by rfl⟩ : syracuseStep 18017099 = 27025649) B27025649
theorem B3558239 : Blo 1248442 3558239 := bstep (se 1 (by rfl) ⟨2668679, by rfl⟩ : syracuseStep 3558239 = 5337359) B5337359
theorem B4000673 : Blo 1248442 4000673 := bstep (se 2 (by rfl) ⟨1500252, by rfl⟩ : syracuseStep 4000673 = 3000505) B3000505
theorem B2108335 : Blo 1248442 2108335 := bstep (se 1 (by rfl) ⟨1581251, by rfl⟩ : syracuseStep 2108335 = 3162503) B3162503
theorem B9612215 : Blo 1248442 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B2812859 : Blo 1248442 2812859 := bstep (se 1 (by rfl) ⟨2109644, by rfl⟩ : syracuseStep 2812859 = 4219289) B4219289
theorem B3165115 : Blo 1248442 3165115 := bstep (se 1 (by rfl) ⟨2373836, by rfl⟩ : syracuseStep 3165115 = 4747673) B4747673
theorem B2108423 : Blo 1248442 2108423 := bstep (se 1 (by rfl) ⟨1581317, by rfl⟩ : syracuseStep 2108423 = 3162635) B3162635
theorem B2370617 : Blo 1248442 2370617 := bstep (se 2 (by rfl) ⟨888981, by rfl⟩ : syracuseStep 2370617 = 1777963) B1777963
theorem B2001977 : Blo 1248442 2001977 := bstep (se 2 (by rfl) ⟨750741, by rfl⟩ : syracuseStep 2001977 = 1501483) B1501483
theorem B2812985 : Blo 1248442 2812985 := bstep (se 2 (by rfl) ⟨1054869, by rfl⟩ : syracuseStep 2812985 = 2109739) B2109739
theorem B2403425 : Blo 1248442 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B4746397 : Blo 1248442 4746397 := bstep (se 3 (by rfl) ⟨889949, by rfl⟩ : syracuseStep 4746397 = 1779899) B1779899
theorem B1248455 : Blo 1248442 1248455 := bstep (se 1 (by rfl) ⟨936341, by rfl⟩ : syracuseStep 1248455 = 1872683) B1872683
theorem B1248475 : Blo 1248442 1248475 := bstep (se 1 (by rfl) ⟨936356, by rfl⟩ : syracuseStep 1248475 = 1872713) B1872713
theorem B1248551 : Blo 1248442 1248551 := bstep (se 1 (by rfl) ⟨936413, by rfl⟩ : syracuseStep 1248551 = 1872827) B1872827
theorem B1248591 : Blo 1248442 1248591 := bstep (se 1 (by rfl) ⟨936443, by rfl⟩ : syracuseStep 1248591 = 1872887) B1872887
theorem B1248607 : Blo 1248442 1248607 := bstep (se 1 (by rfl) ⟨936455, by rfl⟩ : syracuseStep 1248607 = 1872911) B1872911
theorem B2108767 : Blo 1248442 2108767 := bstep (se 1 (by rfl) ⟨1581575, by rfl⟩ : syracuseStep 2108767 = 3163151) B3163151
theorem B1248635 : Blo 1248442 1248635 := bstep (se 1 (by rfl) ⟨936476, by rfl⟩ : syracuseStep 1248635 = 1872953) B1872953
theorem B4214159 : Blo 1248442 4214159 := bstep (se 1 (by rfl) ⟨3160619, by rfl⟩ : syracuseStep 4214159 = 6321239) B6321239
theorem B2813327 : Blo 1248442 2813327 := bstep (se 1 (by rfl) ⟨2109995, by rfl⟩ : syracuseStep 2813327 = 4219991) B4219991
theorem B1248687 : Blo 1248442 1248687 := bstep (se 1 (by rfl) ⟨936515, by rfl⟩ : syracuseStep 1248687 = 1873031) B1873031
theorem B2108855 : Blo 1248442 2108855 := bstep (se 1 (by rfl) ⟨1581641, by rfl⟩ : syracuseStep 2108855 = 3163283) B3163283
theorem B1248711 : Blo 1248442 1248711 := bstep (se 1 (by rfl) ⟨936533, by rfl⟩ : syracuseStep 1248711 = 1873067) B1873067
theorem B1248731 : Blo 1248442 1248731 := bstep (se 1 (by rfl) ⟨936548, by rfl⟩ : syracuseStep 1248731 = 1873097) B1873097
theorem B1248807 : Blo 1248442 1248807 := bstep (se 1 (by rfl) ⟨936605, by rfl⟩ : syracuseStep 1248807 = 1873211) B1873211
theorem B4001339 : Blo 1248442 4001339 := bstep (se 1 (by rfl) ⟨3001004, by rfl⟩ : syracuseStep 4001339 = 6002009) B6002009
theorem B1248847 : Blo 1248442 1248847 := bstep (se 1 (by rfl) ⟨936635, by rfl⟩ : syracuseStep 1248847 = 1873271) B1873271
theorem B1248863 : Blo 1248442 1248863 := bstep (se 1 (by rfl) ⟨936647, by rfl⟩ : syracuseStep 1248863 = 1873295) B1873295
theorem B1248891 : Blo 1248442 1248891 := bstep (se 1 (by rfl) ⟨936668, by rfl⟩ : syracuseStep 1248891 = 1873337) B1873337
theorem B16010891 : Blo 1248442 16010891 := bstep (se 1 (by rfl) ⟨12008168, by rfl⟩ : syracuseStep 16010891 = 24016337) B24016337
theorem B1248943 : Blo 1248442 1248943 := bstep (se 1 (by rfl) ⟨936707, by rfl⟩ : syracuseStep 1248943 = 1873415) B1873415
theorem B1248967 : Blo 1248442 1248967 := bstep (se 1 (by rfl) ⟨936725, by rfl⟩ : syracuseStep 1248967 = 1873451) B1873451
theorem B2404039 : Blo 1248442 2404039 := bstep (se 1 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 2404039 = 3606059) B3606059
theorem B4214483 : Blo 1248442 4214483 := bstep (se 1 (by rfl) ⟨3160862, by rfl⟩ : syracuseStep 4214483 = 6321725) B6321725
theorem B1248987 : Blo 1248442 1248987 := bstep (se 1 (by rfl) ⟨936740, by rfl⟩ : syracuseStep 1248987 = 1873481) B1873481
theorem B1249063 : Blo 1248442 1249063 := bstep (se 1 (by rfl) ⟨936797, by rfl⟩ : syracuseStep 1249063 = 1873595) B1873595
theorem B3559241 : Blo 1248442 3559241 := bstep (se 2 (by rfl) ⟨1334715, by rfl⟩ : syracuseStep 3559241 = 2669431) B2669431
theorem B1249103 : Blo 1248442 1249103 := bstep (se 1 (by rfl) ⟨936827, by rfl⟩ : syracuseStep 1249103 = 1873655) B1873655
theorem B1249119 : Blo 1248442 1249119 := bstep (se 1 (by rfl) ⟨936839, by rfl⟩ : syracuseStep 1249119 = 1873679) B1873679
theorem B1249147 : Blo 1248442 1249147 := bstep (se 1 (by rfl) ⟨936860, by rfl⟩ : syracuseStep 1249147 = 1873721) B1873721
theorem B3002273 : Blo 1248442 3002273 := bstep (se 2 (by rfl) ⟨1125852, by rfl⟩ : syracuseStep 3002273 = 2251705) B2251705
theorem B6008737 : Blo 1248442 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B1249199 : Blo 1248442 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B1249223 : Blo 1248442 1249223 := bstep (se 1 (by rfl) ⟨936917, by rfl⟩ : syracuseStep 1249223 = 1873835) B1873835
theorem B1249243 : Blo 1248442 1249243 := bstep (se 1 (by rfl) ⟨936932, by rfl⟩ : syracuseStep 1249243 = 1873865) B1873865
theorem B2109449 : Blo 1248442 2109449 := bstep (se 2 (by rfl) ⟨791043, by rfl⟩ : syracuseStep 2109449 = 1582087) B1582087
theorem B12988445 : Blo 1248442 12988445 := bstep (se 3 (by rfl) ⟨2435333, by rfl⟩ : syracuseStep 12988445 = 4870667) B4870667
theorem B10678301 : Blo 1248442 10678301 := bstep (se 3 (by rfl) ⟨2002181, by rfl⟩ : syracuseStep 10678301 = 4004363) B4004363
theorem B1404967 : Blo 1248442 1404967 := bstep (se 1 (by rfl) ⟨1053725, by rfl⟩ : syracuseStep 1404967 = 2107451) B2107451
theorem B1249319 : Blo 1248442 1249319 := bstep (se 1 (by rfl) ⟨936989, by rfl⟩ : syracuseStep 1249319 = 1873979) B1873979
theorem B1249359 : Blo 1248442 1249359 := bstep (se 1 (by rfl) ⟨937019, by rfl⟩ : syracuseStep 1249359 = 1874039) B1874039
theorem B3002447 : Blo 1248442 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B1249375 : Blo 1248442 1249375 := bstep (se 1 (by rfl) ⟨937031, by rfl⟩ : syracuseStep 1249375 = 1874063) B1874063
theorem B1249403 : Blo 1248442 1249403 := bstep (se 1 (by rfl) ⟨937052, by rfl⟩ : syracuseStep 1249403 = 1874105) B1874105
theorem B2109611 : Blo 1248442 2109611 := bstep (se 1 (by rfl) ⟨1582208, by rfl⟩ : syracuseStep 2109611 = 3164417) B3164417
theorem B1249455 : Blo 1248442 1249455 := bstep (se 1 (by rfl) ⟨937091, by rfl⟩ : syracuseStep 1249455 = 1874183) B1874183
theorem B13504691 : Blo 1248442 13504691 := bstep (se 1 (by rfl) ⟨10128518, by rfl⟩ : syracuseStep 13504691 = 20257037) B20257037
theorem B1249479 : Blo 1248442 1249479 := bstep (se 1 (by rfl) ⟨937109, by rfl⟩ : syracuseStep 1249479 = 1874219) B1874219
theorem B1249499 : Blo 1248442 1249499 := bstep (se 1 (by rfl) ⟨937124, by rfl⟩ : syracuseStep 1249499 = 1874249) B1874249
theorem B1249575 : Blo 1248442 1249575 := bstep (se 1 (by rfl) ⟨937181, by rfl⟩ : syracuseStep 1249575 = 1874363) B1874363
theorem B1249615 : Blo 1248442 1249615 := bstep (se 1 (by rfl) ⟨937211, by rfl⟩ : syracuseStep 1249615 = 1874423) B1874423
theorem B1249631 : Blo 1248442 1249631 := bstep (se 1 (by rfl) ⟨937223, by rfl⟩ : syracuseStep 1249631 = 1874447) B1874447
theorem B1249659 : Blo 1248442 1249659 := bstep (se 1 (by rfl) ⟨937244, by rfl⟩ : syracuseStep 1249659 = 1874489) B1874489
theorem B1249711 : Blo 1248442 1249711 := bstep (se 1 (by rfl) ⟨937283, by rfl⟩ : syracuseStep 1249711 = 1874567) B1874567
theorem B1249735 : Blo 1248442 1249735 := bstep (se 1 (by rfl) ⟨937301, by rfl⟩ : syracuseStep 1249735 = 1874603) B1874603
theorem B1249755 : Blo 1248442 1249755 := bstep (se 1 (by rfl) ⟨937316, by rfl⟩ : syracuseStep 1249755 = 1874633) B1874633
theorem B5067245 : Blo 1248442 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B4002313 : Blo 1248442 4002313 := bstep (se 2 (by rfl) ⟨1500867, by rfl⟩ : syracuseStep 4002313 = 3001735) B3001735
theorem B2372105 : Blo 1248442 2372105 := bstep (se 2 (by rfl) ⟨889539, by rfl⟩ : syracuseStep 2372105 = 1779079) B1779079
theorem B10670615 : Blo 1248442 10670615 := bstep (se 1 (by rfl) ⟨8002961, by rfl⟩ : syracuseStep 10670615 = 16005923) B16005923
theorem B2404903 : Blo 1248442 2404903 := bstep (se 1 (by rfl) ⟨1803677, by rfl⟩ : syracuseStep 2404903 = 3607355) B3607355
theorem B1249831 : Blo 1248442 1249831 := bstep (se 1 (by rfl) ⟨937373, by rfl⟩ : syracuseStep 1249831 = 1874747) B1874747
theorem B2110009 : Blo 1248442 2110009 := bstep (se 2 (by rfl) ⟨791253, by rfl⟩ : syracuseStep 2110009 = 1582507) B1582507
theorem B1249871 : Blo 1248442 1249871 := bstep (se 1 (by rfl) ⟨937403, by rfl⟩ : syracuseStep 1249871 = 1874807) B1874807
theorem B1249887 : Blo 1248442 1249887 := bstep (se 1 (by rfl) ⟨937415, by rfl⟩ : syracuseStep 1249887 = 1874831) B1874831
theorem B1249915 : Blo 1248442 1249915 := bstep (se 1 (by rfl) ⟨937436, by rfl⟩ : syracuseStep 1249915 = 1874873) B1874873
theorem B4002443 : Blo 1248442 4002443 := bstep (se 1 (by rfl) ⟨3001832, by rfl⟩ : syracuseStep 4002443 = 6003665) B6003665
theorem B1249967 : Blo 1248442 1249967 := bstep (se 1 (by rfl) ⟨937475, by rfl⟩ : syracuseStep 1249967 = 1874951) B1874951
theorem B1249991 : Blo 1248442 1249991 := bstep (se 1 (by rfl) ⟨937493, by rfl⟩ : syracuseStep 1249991 = 1874987) B1874987
theorem B1250011 : Blo 1248442 1250011 := bstep (se 1 (by rfl) ⟨937508, by rfl⟩ : syracuseStep 1250011 = 1875017) B1875017
theorem B1250087 : Blo 1248442 1250087 := bstep (se 1 (by rfl) ⟨937565, by rfl⟩ : syracuseStep 1250087 = 1875131) B1875131
theorem B1250127 : Blo 1248442 1250127 := bstep (se 1 (by rfl) ⟨937595, by rfl⟩ : syracuseStep 1250127 = 1875191) B1875191
theorem B1250143 : Blo 1248442 1250143 := bstep (se 1 (by rfl) ⟨937607, by rfl⟩ : syracuseStep 1250143 = 1875215) B1875215
theorem B36008819 : Blo 1248442 36008819 := bstep (se 1 (by rfl) ⟨27006614, by rfl⟩ : syracuseStep 36008819 = 54013229) B54013229
theorem B4215671 : Blo 1248442 4215671 := bstep (se 1 (by rfl) ⟨3161753, by rfl⟩ : syracuseStep 4215671 = 6323507) B6323507
theorem B1250171 : Blo 1248442 1250171 := bstep (se 1 (by rfl) ⟨937628, by rfl⟩ : syracuseStep 1250171 = 1875257) B1875257
theorem B1872815 : Blo 1248442 1872815 := bstep (se 1 (by rfl) ⟨1404611, by rfl⟩ : syracuseStep 1872815 = 2809223) B2809223
theorem B1250223 : Blo 1248442 1250223 := bstep (se 1 (by rfl) ⟨937667, by rfl⟩ : syracuseStep 1250223 = 1875335) B1875335
theorem B1250247 : Blo 1248442 1250247 := bstep (se 1 (by rfl) ⟨937685, by rfl⟩ : syracuseStep 1250247 = 1875371) B1875371
theorem B1250267 : Blo 1248442 1250267 := bstep (se 1 (by rfl) ⟨937700, by rfl⟩ : syracuseStep 1250267 = 1875401) B1875401
theorem B1872905 : Blo 1248442 1872905 := bstep (se 2 (by rfl) ⟨702339, by rfl⟩ : syracuseStep 1872905 = 1404679) B1404679
theorem B1872935 : Blo 1248442 1872935 := bstep (se 1 (by rfl) ⟨1404701, by rfl⟩ : syracuseStep 1872935 = 2809403) B2809403
theorem B1250343 : Blo 1248442 1250343 := bstep (se 1 (by rfl) ⟨937757, by rfl⟩ : syracuseStep 1250343 = 1875515) B1875515
theorem B10679363 : Blo 1248442 10679363 := bstep (se 1 (by rfl) ⟨8009522, by rfl⟩ : syracuseStep 10679363 = 16019045) B16019045
theorem B4215887 : Blo 1248442 4215887 := bstep (se 1 (by rfl) ⟨3161915, by rfl⟩ : syracuseStep 4215887 = 6323831) B6323831
theorem B3560527 : Blo 1248442 3560527 := bstep (se 1 (by rfl) ⟨2670395, by rfl⟩ : syracuseStep 3560527 = 5340791) B5340791
theorem B1250383 : Blo 1248442 1250383 := bstep (se 1 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 1250383 = 1875575) B1875575
theorem B1250399 : Blo 1248442 1250399 := bstep (se 1 (by rfl) ⟨937799, by rfl⟩ : syracuseStep 1250399 = 1875599) B1875599
theorem B1873019 : Blo 1248442 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B1250427 : Blo 1248442 1250427 := bstep (se 1 (by rfl) ⟨937820, by rfl⟩ : syracuseStep 1250427 = 1875641) B1875641
theorem B2249975 : Blo 1248442 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B1873145 : Blo 1248442 1873145 := bstep (se 2 (by rfl) ⟨702429, by rfl⟩ : syracuseStep 1873145 = 1404859) B1404859
theorem B1873247 : Blo 1248442 1873247 := bstep (se 1 (by rfl) ⟨1404935, by rfl⟩ : syracuseStep 1873247 = 2809871) B2809871
theorem B1873259 : Blo 1248442 1873259 := bstep (se 1 (by rfl) ⟨1404944, by rfl⟩ : syracuseStep 1873259 = 2809889) B2809889
theorem B2372971 : Blo 1248442 2372971 := bstep (se 1 (by rfl) ⟨1779728, by rfl⟩ : syracuseStep 2372971 = 3559457) B3559457
theorem B12015013 : Blo 1248442 12015013 := bstep (se 4 (by rfl) ⟨1126407, by rfl⟩ : syracuseStep 12015013 = 2252815) B2252815
theorem B2373047 : Blo 1248442 2373047 := bstep (se 1 (by rfl) ⟨1779785, by rfl⟩ : syracuseStep 2373047 = 3559571) B3559571
theorem B4216265 : Blo 1248442 4216265 := bstep (se 2 (by rfl) ⟨1581099, by rfl⟩ : syracuseStep 4216265 = 3162199) B3162199
theorem B1873487 : Blo 1248442 1873487 := bstep (se 1 (by rfl) ⟨1405115, by rfl⟩ : syracuseStep 1873487 = 2810231) B2810231
theorem B9492065 : Blo 1248442 9492065 := bstep (se 2 (by rfl) ⟨3559524, by rfl⟩ : syracuseStep 9492065 = 7119049) B7119049
theorem B1406587 : Blo 1248442 1406587 := bstep (se 1 (by rfl) ⟨1054940, by rfl⟩ : syracuseStep 1406587 = 2109881) B2109881
theorem B2283179 : Blo 1248442 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B1873607 : Blo 1248442 1873607 := bstep (se 1 (by rfl) ⟨1405205, by rfl⟩ : syracuseStep 1873607 = 2810411) B2810411
theorem B4503239 : Blo 1248442 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B2668243 : Blo 1248442 2668243 := bstep (se 1 (by rfl) ⟨2001182, by rfl⟩ : syracuseStep 2668243 = 4002365) B4002365
theorem B4216535 : Blo 1248442 4216535 := bstep (se 1 (by rfl) ⟨3162401, by rfl⟩ : syracuseStep 4216535 = 6324803) B6324803
theorem B4003543 : Blo 1248442 4003543 := bstep (se 1 (by rfl) ⟨3002657, by rfl⟩ : syracuseStep 4003543 = 6005315) B6005315
theorem B17086297 : Blo 1248442 17086297 := bstep (se 2 (by rfl) ⟨6407361, by rfl⟩ : syracuseStep 17086297 = 12814723) B12814723
theorem B1873769 : Blo 1248442 1873769 := bstep (se 2 (by rfl) ⟨702663, by rfl⟩ : syracuseStep 1873769 = 1405327) B1405327
theorem B4216751 : Blo 1248442 4216751 := bstep (se 1 (by rfl) ⟨3162563, by rfl⟩ : syracuseStep 4216751 = 6325127) B6325127
theorem B1873847 : Blo 1248442 1873847 := bstep (se 1 (by rfl) ⟨1405385, by rfl⟩ : syracuseStep 1873847 = 2810771) B2810771
theorem B4741051 : Blo 1248442 4741051 := bstep (se 1 (by rfl) ⟨3555788, by rfl⟩ : syracuseStep 4741051 = 7111577) B7111577
theorem B2373563 : Blo 1248442 2373563 := bstep (se 1 (by rfl) ⟨1780172, by rfl⟩ : syracuseStep 2373563 = 3560345) B3560345
theorem B1873883 : Blo 1248442 1873883 := bstep (se 1 (by rfl) ⟨1405412, by rfl⟩ : syracuseStep 1873883 = 2810825) B2810825
theorem B10139651 : Blo 1248442 10139651 := bstep (se 1 (by rfl) ⟨7604738, by rfl⟩ : syracuseStep 10139651 = 15209477) B15209477
theorem B3160235 : Blo 1248442 3160235 := bstep (se 1 (by rfl) ⟨2370176, by rfl⟩ : syracuseStep 3160235 = 4740353) B4740353
theorem B23107945 : Blo 1248442 23107945 := bstep (se 2 (by rfl) ⟨8665479, by rfl⟩ : syracuseStep 23107945 = 17330959) B17330959
theorem B2283881 : Blo 1248442 2283881 := bstep (se 2 (by rfl) ⟨856455, by rfl⟩ : syracuseStep 2283881 = 1712911) B1712911
theorem B1874351 : Blo 1248442 1874351 := bstep (se 1 (by rfl) ⟨1405763, by rfl⟩ : syracuseStep 1874351 = 2811527) B2811527
theorem B20273645 : Blo 1248442 20273645 := bstep (se 3 (by rfl) ⟨3801308, by rfl⟩ : syracuseStep 20273645 = 7602617) B7602617
theorem B6322697 : Blo 1248442 6322697 := bstep (se 2 (by rfl) ⟨2371011, by rfl⟩ : syracuseStep 6322697 = 4742023) B4742023
theorem B1874441 : Blo 1248442 1874441 := bstep (se 2 (by rfl) ⟨702915, by rfl⟩ : syracuseStep 1874441 = 1405831) B1405831
theorem B1874471 : Blo 1248442 1874471 := bstep (se 1 (by rfl) ⟨1405853, by rfl⟩ : syracuseStep 1874471 = 2811707) B2811707
theorem B1874555 : Blo 1248442 1874555 := bstep (se 1 (by rfl) ⟨1405916, by rfl⟩ : syracuseStep 1874555 = 2811833) B2811833
theorem B4741841 : Blo 1248442 4741841 := bstep (se 2 (by rfl) ⟨1778190, by rfl⟩ : syracuseStep 4741841 = 3556381) B3556381
theorem B1874681 : Blo 1248442 1874681 := bstep (se 2 (by rfl) ⟨703005, by rfl⟩ : syracuseStep 1874681 = 1406011) B1406011
theorem B513137429 : Blo 1248442 513137429 := bstep (se 6 (by rfl) ⟨12026658, by rfl⟩ : syracuseStep 513137429 = 24053317) B24053317
theorem B1874783 : Blo 1248442 1874783 := bstep (se 1 (by rfl) ⟨1406087, by rfl⟩ : syracuseStep 1874783 = 2812175) B2812175
theorem B1874795 : Blo 1248442 1874795 := bstep (se 1 (by rfl) ⟨1406096, by rfl⟩ : syracuseStep 1874795 = 2812193) B2812193
theorem B2669473 : Blo 1248442 2669473 := bstep (se 2 (by rfl) ⟨1001052, by rfl⟩ : syracuseStep 2669473 = 2002105) B2002105
theorem B3161015 : Blo 1248442 3161015 := bstep (se 1 (by rfl) ⟨2370761, by rfl⟩ : syracuseStep 3161015 = 4741523) B4741523
theorem B9493523 : Blo 1248442 9493523 := bstep (se 1 (by rfl) ⟨7120142, by rfl⟩ : syracuseStep 9493523 = 14240285) B14240285
theorem B1875023 : Blo 1248442 1875023 := bstep (se 1 (by rfl) ⟨1406267, by rfl⟩ : syracuseStep 1875023 = 2812535) B2812535
theorem B1334395 : Blo 1248442 1334395 := bstep (se 1 (by rfl) ⟨1000796, by rfl⟩ : syracuseStep 1334395 = 2001593) B2001593
theorem B4742297 : Blo 1248442 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B1875143 : Blo 1248442 1875143 := bstep (se 1 (by rfl) ⟨1406357, by rfl⟩ : syracuseStep 1875143 = 2812715) B2812715
theorem B2809079 : Blo 1248442 2809079 := bstep (se 1 (by rfl) ⟨2106809, by rfl⟩ : syracuseStep 2809079 = 4213619) B4213619
theorem B1875305 : Blo 1248442 1875305 := bstep (se 2 (by rfl) ⟨703239, by rfl⟩ : syracuseStep 1875305 = 1406479) B1406479
theorem B1875383 : Blo 1248442 1875383 := bstep (se 1 (by rfl) ⟨1406537, by rfl⟩ : syracuseStep 1875383 = 2813075) B2813075
theorem B1875419 : Blo 1248442 1875419 := bstep (se 1 (by rfl) ⟨1406564, by rfl⟩ : syracuseStep 1875419 = 2813129) B2813129
theorem B3374617 : Blo 1248442 3374617 := bstep (se 2 (by rfl) ⟨1265481, by rfl⟩ : syracuseStep 3374617 = 2530963) B2530963
theorem B2702945 : Blo 1248442 2702945 := bstep (se 2 (by rfl) ⟨1013604, by rfl⟩ : syracuseStep 2702945 = 2027209) B2027209
theorem B10133191 : Blo 1248442 10133191 := bstep (se 1 (by rfl) ⟨7599893, by rfl⟩ : syracuseStep 10133191 = 15199787) B15199787
theorem B2137799 : Blo 1248442 2137799 := bstep (se 1 (by rfl) ⟨1603349, by rfl⟩ : syracuseStep 2137799 = 3206699) B3206699
theorem B9002785 : Blo 1248442 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B3374921 : Blo 1248442 3374921 := bstep (se 2 (by rfl) ⟨1265595, by rfl⟩ : syracuseStep 3374921 = 2531191) B2531191
theorem B2809673 : Blo 1248442 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B10665863 : Blo 1248442 10665863 := bstep (se 1 (by rfl) ⟨7999397, by rfl⟩ : syracuseStep 10665863 = 15998795) B15998795
theorem B3162017 : Blo 1248442 3162017 := bstep (se 2 (by rfl) ⟨1185756, by rfl⟩ : syracuseStep 3162017 = 2371513) B2371513
theorem B1335215 : Blo 1248442 1335215 := bstep (se 1 (by rfl) ⟨1001411, by rfl⟩ : syracuseStep 1335215 = 2002823) B2002823
theorem B6324155 : Blo 1248442 6324155 := bstep (se 1 (by rfl) ⟨4743116, by rfl⟩ : syracuseStep 6324155 = 9486233) B9486233
theorem B14221331 : Blo 1248442 14221331 := bstep (se 1 (by rfl) ⟨10665998, by rfl⟩ : syracuseStep 14221331 = 21331997) B21331997
theorem B7118867 : Blo 1248442 7118867 := bstep (se 1 (by rfl) ⟨5339150, by rfl⟩ : syracuseStep 7118867 = 10678301) B10678301
theorem B34635853 : Blo 1248442 34635853 := bstep (se 3 (by rfl) ⟨6494222, by rfl⟩ : syracuseStep 34635853 = 12988445) B12988445
theorem B2809961 : Blo 1248442 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B3555539 : Blo 1248442 3555539 := bstep (se 1 (by rfl) ⟨2666654, by rfl⟩ : syracuseStep 3555539 = 5333309) B5333309
theorem B36012509 : Blo 1248442 36012509 := bstep (se 3 (by rfl) ⟨6752345, by rfl⟩ : syracuseStep 36012509 = 13504691) B13504691
theorem B30810593 : Blo 1248442 30810593 := bstep (se 2 (by rfl) ⟨11553972, by rfl⟩ : syracuseStep 30810593 = 23107945) B23107945
theorem B2810447 : Blo 1248442 2810447 := bstep (se 1 (by rfl) ⟨2107835, by rfl⟩ : syracuseStep 2810447 = 4215671) B4215671
theorem B1688239 : Blo 1248442 1688239 := bstep (se 1 (by rfl) ⟨1266179, by rfl⟩ : syracuseStep 1688239 = 2532359) B2532359
theorem B7119575 : Blo 1248442 7119575 := bstep (se 1 (by rfl) ⟨5339681, by rfl⟩ : syracuseStep 7119575 = 10679363) B10679363
theorem B2810591 : Blo 1248442 2810591 := bstep (se 1 (by rfl) ⟨2107943, by rfl⟩ : syracuseStep 2810591 = 4215887) B4215887
theorem B3162847 : Blo 1248442 3162847 := bstep (se 1 (by rfl) ⟨2372135, by rfl⟩ : syracuseStep 3162847 = 4744271) B4744271
theorem B3162959 : Blo 1248442 3162959 := bstep (se 1 (by rfl) ⟨2372219, by rfl⟩ : syracuseStep 3162959 = 4744439) B4744439
theorem B1582031 : Blo 1248442 1582031 := bstep (se 1 (by rfl) ⟨1186523, by rfl⟩ : syracuseStep 1582031 = 2373047) B2373047
theorem B2810843 : Blo 1248442 2810843 := bstep (se 1 (by rfl) ⟨2108132, by rfl⟩ : syracuseStep 2810843 = 4216265) B4216265
theorem B3802087 : Blo 1248442 3802087 := bstep (se 1 (by rfl) ⟨2851565, by rfl⟩ : syracuseStep 3802087 = 5703131) B5703131
theorem B2811023 : Blo 1248442 2811023 := bstep (se 1 (by rfl) ⟨2108267, by rfl⟩ : syracuseStep 2811023 = 4216535) B4216535
theorem B2811113 : Blo 1248442 2811113 := bstep (se 2 (by rfl) ⟨1054167, by rfl⟩ : syracuseStep 2811113 = 2108335) B2108335
theorem B4220153 : Blo 1248442 4220153 := bstep (se 2 (by rfl) ⟨1582557, by rfl⟩ : syracuseStep 4220153 = 3165115) B3165115
theorem B2811167 : Blo 1248442 2811167 := bstep (se 1 (by rfl) ⟨2108375, by rfl⟩ : syracuseStep 2811167 = 4216751) B4216751
theorem B6759767 : Blo 1248442 6759767 := bstep (se 1 (by rfl) ⟨5069825, by rfl⟩ : syracuseStep 6759767 = 10139651) B10139651
theorem B6325613 : Blo 1248442 6325613 := bstep (se 3 (by rfl) ⟨1186052, by rfl⟩ : syracuseStep 6325613 = 2372105) B2372105
theorem B2106823 : Blo 1248442 2106823 := bstep (se 1 (by rfl) ⟨1580117, by rfl⟩ : syracuseStep 2106823 = 3160235) B3160235
theorem B3163607 : Blo 1248442 3163607 := bstep (se 1 (by rfl) ⟨2372705, by rfl⟩ : syracuseStep 3163607 = 4745411) B4745411
theorem B1779193 : Blo 1248442 1779193 := bstep (se 2 (by rfl) ⟨667197, by rfl⟩ : syracuseStep 1779193 = 1334395) B1334395
theorem B51267107 : Blo 1248442 51267107 := bstep (se 1 (by rfl) ⟨38450330, by rfl⟩ : syracuseStep 51267107 = 76900661) B76900661
theorem B6088477 : Blo 1248442 6088477 := bstep (se 3 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 6088477 = 2283179) B2283179
theorem B2811689 : Blo 1248442 2811689 := bstep (se 2 (by rfl) ⟨1054383, by rfl⟩ : syracuseStep 2811689 = 2108767) B2108767
theorem B3376943 : Blo 1248442 3376943 := bstep (se 1 (by rfl) ⟨2532707, by rfl⟩ : syracuseStep 3376943 = 5065415) B5065415
theorem B3163961 : Blo 1248442 3163961 := bstep (se 2 (by rfl) ⟨1186485, by rfl⟩ : syracuseStep 3163961 = 2372971) B2372971
theorem B342091619 : Blo 1248442 342091619 := bstep (se 1 (by rfl) ⟨256568714, by rfl⟩ : syracuseStep 342091619 = 513137429) B513137429
theorem B12011399 : Blo 1248442 12011399 := bstep (se 1 (by rfl) ⟨9008549, by rfl⟩ : syracuseStep 12011399 = 18017099) B18017099
theorem B6408143 : Blo 1248442 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B2107343 : Blo 1248442 2107343 := bstep (se 1 (by rfl) ⟨1580507, by rfl⟩ : syracuseStep 2107343 = 3161015) B3161015
theorem B4499489 : Blo 1248442 4499489 := bstep (se 2 (by rfl) ⟨1687308, by rfl⟩ : syracuseStep 4499489 = 3374617) B3374617
theorem B3205385 : Blo 1248442 3205385 := bstep (se 2 (by rfl) ⟨1202019, by rfl⟩ : syracuseStep 3205385 = 2404039) B2404039
theorem B13510921 : Blo 1248442 13510921 := bstep (se 2 (by rfl) ⟨5066595, by rfl⟩ : syracuseStep 13510921 = 10133191) B10133191
theorem B3557657 : Blo 1248442 3557657 := bstep (se 2 (by rfl) ⟨1334121, by rfl⟩ : syracuseStep 3557657 = 2668243) B2668243
theorem B12003713 : Blo 1248442 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B2108011 : Blo 1248442 2108011 := bstep (se 1 (by rfl) ⟨1581008, by rfl⟩ : syracuseStep 2108011 = 3162017) B3162017
theorem B2001515 : Blo 1248442 2001515 := bstep (se 1 (by rfl) ⟨1501136, by rfl⟩ : syracuseStep 2001515 = 3002273) B3002273
theorem B2812751 : Blo 1248442 2812751 := bstep (se 1 (by rfl) ⟨2109563, by rfl⟩ : syracuseStep 2812751 = 4219127) B4219127
theorem B8006525 : Blo 1248442 8006525 := bstep (se 3 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 8006525 = 3002447) B3002447
theorem B2108315 : Blo 1248442 2108315 := bstep (se 1 (by rfl) ⟨1581236, by rfl⟩ : syracuseStep 2108315 = 3162473) B3162473
theorem B7113743 : Blo 1248442 7113743 := bstep (se 1 (by rfl) ⟨5335307, by rfl⟩ : syracuseStep 7113743 = 10670615) B10670615
theorem B2812967 : Blo 1248442 2812967 := bstep (se 1 (by rfl) ⟨2109725, by rfl⟩ : syracuseStep 2812967 = 4219451) B4219451
theorem B2813147 : Blo 1248442 2813147 := bstep (se 1 (by rfl) ⟨2109860, by rfl⟩ : syracuseStep 2813147 = 4219721) B4219721
theorem B24005879 : Blo 1248442 24005879 := bstep (se 1 (by rfl) ⟨18004409, by rfl⟩ : syracuseStep 24005879 = 36008819) B36008819
theorem B1248543 : Blo 1248442 1248543 := bstep (se 1 (by rfl) ⟨936407, by rfl⟩ : syracuseStep 1248543 = 1872815) B1872815
theorem B5999933 : Blo 1248442 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B1248603 : Blo 1248442 1248603 := bstep (se 1 (by rfl) ⟨936452, by rfl⟩ : syracuseStep 1248603 = 1872905) B1872905
theorem B5336417 : Blo 1248442 5336417 := bstep (se 2 (by rfl) ⟨2001156, by rfl⟩ : syracuseStep 5336417 = 4002313) B4002313
theorem B1248623 : Blo 1248442 1248623 := bstep (se 1 (by rfl) ⟨936467, by rfl⟩ : syracuseStep 1248623 = 1872935) B1872935
theorem B3206537 : Blo 1248442 3206537 := bstep (se 2 (by rfl) ⟨1202451, by rfl⟩ : syracuseStep 3206537 = 2404903) B2404903
theorem B2813345 : Blo 1248442 2813345 := bstep (se 2 (by rfl) ⟨1055004, by rfl⟩ : syracuseStep 2813345 = 2110009) B2110009
theorem B1248679 : Blo 1248442 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B1248763 : Blo 1248442 1248763 := bstep (se 1 (by rfl) ⟨936572, by rfl⟩ : syracuseStep 1248763 = 1873145) B1873145
theorem B1248831 : Blo 1248442 1248831 := bstep (se 1 (by rfl) ⟨936623, by rfl⟩ : syracuseStep 1248831 = 1873247) B1873247
theorem B1248839 : Blo 1248442 1248839 := bstep (se 1 (by rfl) ⟨936629, by rfl⟩ : syracuseStep 1248839 = 1873259) B1873259
theorem B6090349 : Blo 1248442 6090349 := bstep (se 3 (by rfl) ⟨1141940, by rfl⟩ : syracuseStep 6090349 = 2283881) B2283881
theorem B1248991 : Blo 1248442 1248991 := bstep (se 1 (by rfl) ⟨936743, by rfl⟩ : syracuseStep 1248991 = 1873487) B1873487
theorem B6328043 : Blo 1248442 6328043 := bstep (se 1 (by rfl) ⟨4746032, by rfl⟩ : syracuseStep 6328043 = 9492065) B9492065
theorem B10678027 : Blo 1248442 10678027 := bstep (se 1 (by rfl) ⟨8008520, by rfl⟩ : syracuseStep 10678027 = 16017041) B16017041
theorem B2371369 : Blo 1248442 2371369 := bstep (se 2 (by rfl) ⟨889263, by rfl⟩ : syracuseStep 2371369 = 1778527) B1778527
theorem B1249071 : Blo 1248442 1249071 := bstep (se 1 (by rfl) ⟨936803, by rfl⟩ : syracuseStep 1249071 = 1873607) B1873607
theorem B3002159 : Blo 1248442 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B1404751 : Blo 1248442 1404751 := bstep (se 1 (by rfl) ⟨1053563, by rfl⟩ : syracuseStep 1404751 = 2107127) B2107127
theorem B3559297 : Blo 1248442 3559297 := bstep (se 2 (by rfl) ⟨1334736, by rfl⟩ : syracuseStep 3559297 = 2669473) B2669473
theorem B1249179 : Blo 1248442 1249179 := bstep (se 1 (by rfl) ⟨936884, by rfl⟩ : syracuseStep 1249179 = 1873769) B1873769
theorem B13512653 : Blo 1248442 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B1249231 : Blo 1248442 1249231 := bstep (se 1 (by rfl) ⟨936923, by rfl⟩ : syracuseStep 1249231 = 1873847) B1873847
theorem B1249255 : Blo 1248442 1249255 := bstep (se 1 (by rfl) ⟨936941, by rfl⟩ : syracuseStep 1249255 = 1873883) B1873883
theorem B6008851 : Blo 1248442 6008851 := bstep (se 1 (by rfl) ⟨4506638, by rfl⟩ : syracuseStep 6008851 = 9013277) B9013277
theorem B9482345 : Blo 1248442 9482345 := bstep (se 2 (by rfl) ⟨3555879, by rfl⟩ : syracuseStep 9482345 = 7111759) B7111759
theorem B9613417 : Blo 1248442 9613417 := bstep (se 2 (by rfl) ⟨3605031, by rfl⟩ : syracuseStep 9613417 = 7210063) B7210063
theorem B4747369 : Blo 1248442 4747369 := bstep (se 2 (by rfl) ⟨1780263, by rfl⟩ : syracuseStep 4747369 = 3560527) B3560527
theorem B10670237 : Blo 1248442 10670237 := bstep (se 3 (by rfl) ⟨2000669, by rfl⟩ : syracuseStep 10670237 = 4001339) B4001339
theorem B6328529 : Blo 1248442 6328529 := bstep (se 2 (by rfl) ⟨2373198, by rfl⟩ : syracuseStep 6328529 = 4746397) B4746397
theorem B1405147 : Blo 1248442 1405147 := bstep (se 1 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 1405147 = 2107721) B2107721
theorem B1249567 : Blo 1248442 1249567 := bstep (se 1 (by rfl) ⟨937175, by rfl⟩ : syracuseStep 1249567 = 1874351) B1874351
theorem B4215131 : Blo 1248442 4215131 := bstep (se 1 (by rfl) ⟨3161348, by rfl⟩ : syracuseStep 4215131 = 6322697) B6322697
theorem B1249627 : Blo 1248442 1249627 := bstep (se 1 (by rfl) ⟨937220, by rfl⟩ : syracuseStep 1249627 = 1874441) B1874441
theorem B1249647 : Blo 1248442 1249647 := bstep (se 1 (by rfl) ⟨937235, by rfl⟩ : syracuseStep 1249647 = 1874471) B1874471
theorem B1249703 : Blo 1248442 1249703 := bstep (se 1 (by rfl) ⟨937277, by rfl⟩ : syracuseStep 1249703 = 1874555) B1874555
theorem B1405435 : Blo 1248442 1405435 := bstep (se 1 (by rfl) ⟨1054076, by rfl⟩ : syracuseStep 1405435 = 2108153) B2108153
theorem B1249787 : Blo 1248442 1249787 := bstep (se 1 (by rfl) ⟨937340, by rfl⟩ : syracuseStep 1249787 = 1874681) B1874681
theorem B16020017 : Blo 1248442 16020017 := bstep (se 2 (by rfl) ⟨6007506, by rfl⟩ : syracuseStep 16020017 = 12015013) B12015013
theorem B2372159 : Blo 1248442 2372159 := bstep (se 1 (by rfl) ⟨1779119, by rfl⟩ : syracuseStep 2372159 = 3558239) B3558239
theorem B1249855 : Blo 1248442 1249855 := bstep (se 1 (by rfl) ⟨937391, by rfl⟩ : syracuseStep 1249855 = 1874783) B1874783
theorem B1249863 : Blo 1248442 1249863 := bstep (se 1 (by rfl) ⟨937397, by rfl⟩ : syracuseStep 1249863 = 1874795) B1874795
theorem B2667115 : Blo 1248442 2667115 := bstep (se 1 (by rfl) ⟨2000336, by rfl⟩ : syracuseStep 2667115 = 4000673) B4000673
theorem B1405615 : Blo 1248442 1405615 := bstep (se 1 (by rfl) ⟨1054211, by rfl⟩ : syracuseStep 1405615 = 2108423) B2108423
theorem B6329015 : Blo 1248442 6329015 := bstep (se 1 (by rfl) ⟨4746761, by rfl⟩ : syracuseStep 6329015 = 9493523) B9493523
theorem B1250015 : Blo 1248442 1250015 := bstep (se 1 (by rfl) ⟨937511, by rfl⟩ : syracuseStep 1250015 = 1875023) B1875023
theorem B1602283 : Blo 1248442 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B1250095 : Blo 1248442 1250095 := bstep (se 1 (by rfl) ⟨937571, by rfl⟩ : syracuseStep 1250095 = 1875143) B1875143
theorem B1872719 : Blo 1248442 1872719 := bstep (se 1 (by rfl) ⟨1404539, by rfl⟩ : syracuseStep 1872719 = 2809079) B2809079
theorem B1250203 : Blo 1248442 1250203 := bstep (se 1 (by rfl) ⟨937652, by rfl⟩ : syracuseStep 1250203 = 1875305) B1875305
theorem B5338057 : Blo 1248442 5338057 := bstep (se 2 (by rfl) ⟨2001771, by rfl⟩ : syracuseStep 5338057 = 4003543) B4003543
theorem B1405903 : Blo 1248442 1405903 := bstep (se 1 (by rfl) ⟨1054427, by rfl⟩ : syracuseStep 1405903 = 2108855) B2108855
theorem B1250255 : Blo 1248442 1250255 := bstep (se 1 (by rfl) ⟨937691, by rfl⟩ : syracuseStep 1250255 = 1875383) B1875383
theorem B1250279 : Blo 1248442 1250279 := bstep (se 1 (by rfl) ⟨937709, by rfl⟩ : syracuseStep 1250279 = 1875419) B1875419
theorem B3560573 : Blo 1248442 3560573 := bstep (se 3 (by rfl) ⟨667607, by rfl⟩ : syracuseStep 3560573 = 1335215) B1335215
theorem B6329501 : Blo 1248442 6329501 := bstep (se 3 (by rfl) ⟨1186781, by rfl⟩ : syracuseStep 6329501 = 2373563) B2373563
theorem B2249947 : Blo 1248442 2249947 := bstep (se 1 (by rfl) ⟨1687460, by rfl⟩ : syracuseStep 2249947 = 3374921) B3374921
theorem B1873115 : Blo 1248442 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B2372827 : Blo 1248442 2372827 := bstep (se 1 (by rfl) ⟨1779620, by rfl⟩ : syracuseStep 2372827 = 3559241) B3559241
theorem B6321401 : Blo 1248442 6321401 := bstep (se 2 (by rfl) ⟨2370525, by rfl⟩ : syracuseStep 6321401 = 4741051) B4741051
theorem B4216103 : Blo 1248442 4216103 := bstep (se 1 (by rfl) ⟨3162077, by rfl⟩ : syracuseStep 4216103 = 6324155) B6324155
theorem B1406299 : Blo 1248442 1406299 := bstep (se 1 (by rfl) ⟨1054724, by rfl⟩ : syracuseStep 1406299 = 2109449) B2109449
theorem B1873289 : Blo 1248442 1873289 := bstep (se 2 (by rfl) ⟨702483, by rfl⟩ : syracuseStep 1873289 = 1404967) B1404967
theorem B1406407 : Blo 1248442 1406407 := bstep (se 1 (by rfl) ⟨1054805, by rfl⟩ : syracuseStep 1406407 = 2109611) B2109611
theorem B1873643 : Blo 1248442 1873643 := bstep (se 1 (by rfl) ⟨1405232, by rfl⟩ : syracuseStep 1873643 = 2810465) B2810465
theorem B2668295 : Blo 1248442 2668295 := bstep (se 1 (by rfl) ⟨2001221, by rfl⟩ : syracuseStep 2668295 = 4002443) B4002443
theorem B7214935 : Blo 1248442 7214935 := bstep (se 1 (by rfl) ⟨5411201, by rfl⟩ : syracuseStep 7214935 = 10822403) B10822403
theorem B1333199 : Blo 1248442 1333199 := bstep (se 1 (by rfl) ⟨999899, by rfl⟩ : syracuseStep 1333199 = 1999799) B1999799
theorem B1873871 : Blo 1248442 1873871 := bstep (se 1 (by rfl) ⟨1405403, by rfl⟩ : syracuseStep 1873871 = 2810807) B2810807
theorem B4216967 : Blo 1248442 4216967 := bstep (se 1 (by rfl) ⟨3162725, by rfl⟩ : syracuseStep 4216967 = 6325451) B6325451
theorem B12171545 : Blo 1248442 12171545 := bstep (se 2 (by rfl) ⟨4564329, by rfl⟩ : syracuseStep 12171545 = 9128659) B9128659
theorem B1874267 : Blo 1248442 1874267 := bstep (se 1 (by rfl) ⟨1405700, by rfl⟩ : syracuseStep 1874267 = 2811401) B2811401
theorem B18020789 : Blo 1248442 18020789 := bstep (se 5 (by rfl) ⟨844724, by rfl⟩ : syracuseStep 18020789 = 1689449) B1689449
theorem B1333703 : Blo 1248442 1333703 := bstep (se 1 (by rfl) ⟨1000277, by rfl⟩ : syracuseStep 1333703 = 2000555) B2000555
theorem B1874495 : Blo 1248442 1874495 := bstep (se 1 (by rfl) ⟨1405871, by rfl⟩ : syracuseStep 1874495 = 2811743) B2811743
theorem B1333831 : Blo 1248442 1333831 := bstep (se 1 (by rfl) ⟨1000373, by rfl⟩ : syracuseStep 1333831 = 2000747) B2000747
theorem B1874615 : Blo 1248442 1874615 := bstep (se 1 (by rfl) ⟨1405961, by rfl⟩ : syracuseStep 1874615 = 2811923) B2811923
theorem B4873085 : Blo 1248442 4873085 := bstep (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) B1827407
theorem B1874843 : Blo 1248442 1874843 := bstep (se 1 (by rfl) ⟨1406132, by rfl⟩ : syracuseStep 1874843 = 2812265) B2812265
theorem B13515763 : Blo 1248442 13515763 := bstep (se 1 (by rfl) ⟨10136822, by rfl⟩ : syracuseStep 13515763 = 20273645) B20273645
theorem B4004903 : Blo 1248442 4004903 := bstep (se 1 (by rfl) ⟨3003677, by rfl⟩ : syracuseStep 4004903 = 6007355) B6007355
theorem B3161227 : Blo 1248442 3161227 := bstep (se 1 (by rfl) ⟨2370920, by rfl⟩ : syracuseStep 3161227 = 4741841) B4741841
theorem B6167773 : Blo 1248442 6167773 := bstep (se 3 (by rfl) ⟨1156457, by rfl⟩ : syracuseStep 6167773 = 2312915) B2312915
theorem B1875239 : Blo 1248442 1875239 := bstep (se 1 (by rfl) ⟨1406429, by rfl⟩ : syracuseStep 1875239 = 2812859) B2812859
theorem B4218209 : Blo 1248442 4218209 := bstep (se 2 (by rfl) ⟨1581828, by rfl⟩ : syracuseStep 4218209 = 3163657) B3163657
theorem B1580411 : Blo 1248442 1580411 := bstep (se 1 (by rfl) ⟨1185308, by rfl⟩ : syracuseStep 1580411 = 2370617) B2370617
theorem B1334651 : Blo 1248442 1334651 := bstep (se 1 (by rfl) ⟨1000988, by rfl⟩ : syracuseStep 1334651 = 2001977) B2001977
theorem B1875323 : Blo 1248442 1875323 := bstep (se 1 (by rfl) ⟨1406492, by rfl⟩ : syracuseStep 1875323 = 2812985) B2812985
theorem B3161531 : Blo 1248442 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B9494009 : Blo 1248442 9494009 := bstep (se 2 (by rfl) ⟨3560253, by rfl⟩ : syracuseStep 9494009 = 7120507) B7120507
theorem B1875449 : Blo 1248442 1875449 := bstep (se 2 (by rfl) ⟨703293, by rfl⟩ : syracuseStep 1875449 = 1406587) B1406587
theorem B2809439 : Blo 1248442 2809439 := bstep (se 1 (by rfl) ⟨2107079, by rfl⟩ : syracuseStep 2809439 = 4214159) B4214159
theorem B1875551 : Blo 1248442 1875551 := bstep (se 1 (by rfl) ⟨1406663, by rfl⟩ : syracuseStep 1875551 = 2813327) B2813327
theorem B1801963 : Blo 1248442 1801963 := bstep (se 1 (by rfl) ⟨1351472, by rfl⟩ : syracuseStep 1801963 = 2702945) B2702945
theorem B10673927 : Blo 1248442 10673927 := bstep (se 1 (by rfl) ⟨8005445, by rfl⟩ : syracuseStep 10673927 = 16010891) B16010891
theorem B22781729 : Blo 1248442 22781729 := bstep (se 2 (by rfl) ⟨8543148, by rfl⟩ : syracuseStep 22781729 = 17086297) B17086297
theorem B2252585 : Blo 1248442 2252585 := bstep (se 2 (by rfl) ⟨844719, by rfl⟩ : syracuseStep 2252585 = 1689439) B1689439
theorem B1425199 : Blo 1248442 1425199 := bstep (se 1 (by rfl) ⟨1068899, by rfl⟩ : syracuseStep 1425199 = 2137799) B2137799
theorem B2809655 : Blo 1248442 2809655 := bstep (se 1 (by rfl) ⟨2107241, by rfl⟩ : syracuseStep 2809655 = 4214483) B4214483
theorem B8011649 : Blo 1248442 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B7110575 : Blo 1248442 7110575 := bstep (se 1 (by rfl) ⟨5332931, by rfl⟩ : syracuseStep 7110575 = 10665863) B10665863
theorem B8011801 : Blo 1248442 8011801 := bstep (se 2 (by rfl) ⟨3004425, by rfl⟩ : syracuseStep 8011801 = 6008851) B6008851
theorem B4219019 : Blo 1248442 4219019 := bstep (se 1 (by rfl) ⟨3164264, by rfl⟩ : syracuseStep 4219019 = 6328529) B6328529
theorem B2810087 : Blo 1248442 2810087 := bstep (se 1 (by rfl) ⟨2107565, by rfl⟩ : syracuseStep 2810087 = 4215131) B4215131
theorem B18014561 : Blo 1248442 18014561 := bstep (se 2 (by rfl) ⟨6755460, by rfl⟩ : syracuseStep 18014561 = 13510921) B13510921
theorem B1581439 : Blo 1248442 1581439 := bstep (se 1 (by rfl) ⟨1186079, by rfl⟩ : syracuseStep 1581439 = 2372159) B2372159
theorem B4219343 : Blo 1248442 4219343 := bstep (se 1 (by rfl) ⟨3164507, by rfl⟩ : syracuseStep 4219343 = 6329015) B6329015
theorem B1778441 : Blo 1248442 1778441 := bstep (se 2 (by rfl) ⟨666915, by rfl⟩ : syracuseStep 1778441 = 1333831) B1333831
theorem B4219667 : Blo 1248442 4219667 := bstep (se 1 (by rfl) ⟨3164750, by rfl⟩ : syracuseStep 4219667 = 6329501) B6329501
theorem B3556153 : Blo 1248442 3556153 := bstep (se 2 (by rfl) ⟨1333557, by rfl⟩ : syracuseStep 3556153 = 2667115) B2667115
theorem B2810681 : Blo 1248442 2810681 := bstep (se 2 (by rfl) ⟨1054005, by rfl⟩ : syracuseStep 2810681 = 2108011) B2108011
theorem B2810735 : Blo 1248442 2810735 := bstep (se 1 (by rfl) ⟨2108051, by rfl⟩ : syracuseStep 2810735 = 4216103) B4216103
theorem B4506511 : Blo 1248442 4506511 := bstep (se 1 (by rfl) ⟨3379883, by rfl⟩ : syracuseStep 4506511 = 6759767) B6759767
theorem B34178071 : Blo 1248442 34178071 := bstep (se 1 (by rfl) ⟨25633553, by rfl⟩ : syracuseStep 34178071 = 51267107) B51267107
theorem B21349493 : Blo 1248442 21349493 := bstep (se 5 (by rfl) ⟨1000757, by rfl⟩ : syracuseStep 21349493 = 2001515) B2001515
theorem B1778863 : Blo 1248442 1778863 := bstep (se 1 (by rfl) ⟨1334147, by rfl⟩ : syracuseStep 1778863 = 2668295) B2668295
theorem B3556541 : Blo 1248442 3556541 := bstep (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) B1333703
theorem B2999659 : Blo 1248442 2999659 := bstep (se 1 (by rfl) ⟨2249744, by rfl⟩ : syracuseStep 2999659 = 4499489) B4499489
theorem B2811311 : Blo 1248442 2811311 := bstep (se 1 (by rfl) ⟨2108483, by rfl⟩ : syracuseStep 2811311 = 4216967) B4216967
theorem B2999929 : Blo 1248442 2999929 := bstep (se 2 (by rfl) ⟨1124973, by rfl⟩ : syracuseStep 2999929 = 2249947) B2249947
theorem B3163769 : Blo 1248442 3163769 := bstep (se 2 (by rfl) ⟨1186413, by rfl⟩ : syracuseStep 3163769 = 2372827) B2372827
theorem B8120465 : Blo 1248442 8120465 := bstep (se 2 (by rfl) ⟨3045174, by rfl⟩ : syracuseStep 8120465 = 6090349) B6090349
theorem B3999955 : Blo 1248442 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B3557611 : Blo 1248442 3557611 := bstep (se 1 (by rfl) ⟨2668208, by rfl⟩ : syracuseStep 3557611 = 5336417) B5336417
theorem B2812139 : Blo 1248442 2812139 := bstep (se 1 (by rfl) ⟨2109104, by rfl⟩ : syracuseStep 2812139 = 4218209) B4218209
theorem B2107687 : Blo 1248442 2107687 := bstep (se 1 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 2107687 = 3161531) B3161531
theorem B2402617 : Blo 1248442 2402617 := bstep (se 2 (by rfl) ⟨900981, by rfl⟩ : syracuseStep 2402617 = 1801963) B1801963
theorem B9619913 : Blo 1248442 9619913 := bstep (se 2 (by rfl) ⟨3607467, by rfl⟩ : syracuseStep 9619913 = 7214935) B7214935
theorem B4745729 : Blo 1248442 4745729 := bstep (se 2 (by rfl) ⟨1779648, by rfl⟩ : syracuseStep 4745729 = 3559297) B3559297
theorem B1501723 : Blo 1248442 1501723 := bstep (se 1 (by rfl) ⟨1126292, by rfl⟩ : syracuseStep 1501723 = 2252585) B2252585
theorem B2001439 : Blo 1248442 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B9480887 : Blo 1248442 9480887 := bstep (se 1 (by rfl) ⟨7110665, by rfl⟩ : syracuseStep 9480887 = 14221331) B14221331
theorem B4745911 : Blo 1248442 4745911 := bstep (se 1 (by rfl) ⟨3559433, by rfl⟩ : syracuseStep 4745911 = 7118867) B7118867
theorem B46181137 : Blo 1248442 46181137 := bstep (se 2 (by rfl) ⟨17317926, by rfl⟩ : syracuseStep 46181137 = 34635853) B34635853
theorem B7113491 : Blo 1248442 7113491 := bstep (se 1 (by rfl) ⟨5335118, by rfl⟩ : syracuseStep 7113491 = 10670237) B10670237
theorem B2370359 : Blo 1248442 2370359 := bstep (se 1 (by rfl) ⟨1777769, by rfl⟩ : syracuseStep 2370359 = 3555539) B3555539
theorem B20540395 : Blo 1248442 20540395 := bstep (se 1 (by rfl) ⟨15405296, by rfl⟩ : syracuseStep 20540395 = 30810593) B30810593
theorem B4746383 : Blo 1248442 4746383 := bstep (se 1 (by rfl) ⟨3559787, by rfl⟩ : syracuseStep 4746383 = 7119575) B7119575
theorem B1248479 : Blo 1248442 1248479 := bstep (se 1 (by rfl) ⟨936359, by rfl⟩ : syracuseStep 1248479 = 1872719) B1872719
theorem B2108639 : Blo 1248442 2108639 := bstep (se 1 (by rfl) ⟨1581479, by rfl⟩ : syracuseStep 2108639 = 3162959) B3162959
theorem B1248743 : Blo 1248442 1248743 := bstep (se 1 (by rfl) ⟨936557, by rfl⟩ : syracuseStep 1248743 = 1873115) B1873115
theorem B4214267 : Blo 1248442 4214267 := bstep (se 1 (by rfl) ⟨3160700, by rfl⟩ : syracuseStep 4214267 = 6321401) B6321401
theorem B2813435 : Blo 1248442 2813435 := bstep (se 1 (by rfl) ⟨2110076, by rfl⟩ : syracuseStep 2813435 = 4220153) B4220153
theorem B1248859 : Blo 1248442 1248859 := bstep (se 1 (by rfl) ⟨936644, by rfl⟩ : syracuseStep 1248859 = 1873289) B1873289
theorem B2109071 : Blo 1248442 2109071 := bstep (se 1 (by rfl) ⟨1581803, by rfl⟩ : syracuseStep 2109071 = 3163607) B3163607
theorem B4214429 : Blo 1248442 4214429 := bstep (se 3 (by rfl) ⟨790205, by rfl⟩ : syracuseStep 4214429 = 1580411) B1580411
theorem B3559069 : Blo 1248442 3559069 := bstep (se 3 (by rfl) ⟨667325, by rfl⟩ : syracuseStep 3559069 = 1334651) B1334651
theorem B1249095 : Blo 1248442 1249095 := bstep (se 1 (by rfl) ⟨936821, by rfl⟩ : syracuseStep 1249095 = 1873643) B1873643
theorem B2109307 : Blo 1248442 2109307 := bstep (se 1 (by rfl) ⟨1581980, by rfl⟩ : syracuseStep 2109307 = 3163961) B3163961
theorem B228061079 : Blo 1248442 228061079 := bstep (se 1 (by rfl) ⟨171045809, by rfl⟩ : syracuseStep 228061079 = 342091619) B342091619
theorem B8007599 : Blo 1248442 8007599 := bstep (se 1 (by rfl) ⟨6005699, by rfl⟩ : syracuseStep 8007599 = 12011399) B12011399
theorem B4272095 : Blo 1248442 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B1404895 : Blo 1248442 1404895 := bstep (se 1 (by rfl) ⟨1053671, by rfl⟩ : syracuseStep 1404895 = 2107343) B2107343
theorem B1249247 : Blo 1248442 1249247 := bstep (se 1 (by rfl) ⟨936935, by rfl⟩ : syracuseStep 1249247 = 1873871) B1873871
theorem B4214969 : Blo 1248442 4214969 := bstep (se 2 (by rfl) ⟨1580613, by rfl⟩ : syracuseStep 4214969 = 3161227) B3161227
theorem B2371771 : Blo 1248442 2371771 := bstep (se 1 (by rfl) ⟨1778828, by rfl⟩ : syracuseStep 2371771 = 3557657) B3557657
theorem B8114363 : Blo 1248442 8114363 := bstep (se 1 (by rfl) ⟨6085772, by rfl⟩ : syracuseStep 8114363 = 12171545) B12171545
theorem B1249511 : Blo 1248442 1249511 := bstep (se 1 (by rfl) ⟨937133, by rfl⟩ : syracuseStep 1249511 = 1874267) B1874267
theorem B12013859 : Blo 1248442 12013859 := bstep (se 1 (by rfl) ⟨9010394, by rfl⟩ : syracuseStep 12013859 = 18020789) B18020789
theorem B1249663 : Blo 1248442 1249663 := bstep (se 1 (by rfl) ⟨937247, by rfl⟩ : syracuseStep 1249663 = 1874495) B1874495
theorem B1249743 : Blo 1248442 1249743 := bstep (se 1 (by rfl) ⟨937307, by rfl⟩ : syracuseStep 1249743 = 1874615) B1874615
theorem B3248723 : Blo 1248442 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B5337683 : Blo 1248442 5337683 := bstep (se 1 (by rfl) ⟨4003262, by rfl⟩ : syracuseStep 5337683 = 8006525) B8006525
theorem B1405543 : Blo 1248442 1405543 := bstep (se 1 (by rfl) ⟨1054157, by rfl⟩ : syracuseStep 1405543 = 2108315) B2108315
theorem B1249895 : Blo 1248442 1249895 := bstep (se 1 (by rfl) ⟨937421, by rfl⟩ : syracuseStep 1249895 = 1874843) B1874843
theorem B2372257 : Blo 1248442 2372257 := bstep (se 2 (by rfl) ⟨889596, by rfl⟩ : syracuseStep 2372257 = 1779193) B1779193
theorem B16003919 : Blo 1248442 16003919 := bstep (se 1 (by rfl) ⟨12002939, by rfl⟩ : syracuseStep 16003919 = 24005879) B24005879
theorem B1250159 : Blo 1248442 1250159 := bstep (se 1 (by rfl) ⟨937619, by rfl⟩ : syracuseStep 1250159 = 1875239) B1875239
theorem B1250215 : Blo 1248442 1250215 := bstep (se 1 (by rfl) ⟨937661, by rfl⟩ : syracuseStep 1250215 = 1875323) B1875323
theorem B6329339 : Blo 1248442 6329339 := bstep (se 1 (by rfl) ⟨4747004, by rfl⟩ : syracuseStep 6329339 = 9494009) B9494009
theorem B1250299 : Blo 1248442 1250299 := bstep (se 1 (by rfl) ⟨937724, by rfl⟩ : syracuseStep 1250299 = 1875449) B1875449
theorem B1872959 : Blo 1248442 1872959 := bstep (se 1 (by rfl) ⟨1404719, by rfl⟩ : syracuseStep 1872959 = 2809439) B2809439
theorem B1250367 : Blo 1248442 1250367 := bstep (se 1 (by rfl) ⟨937775, by rfl⟩ : syracuseStep 1250367 = 1875551) B1875551
theorem B1873001 : Blo 1248442 1873001 := bstep (se 2 (by rfl) ⟨702375, by rfl⟩ : syracuseStep 1873001 = 1404751) B1404751
theorem B7115951 : Blo 1248442 7115951 := bstep (se 1 (by rfl) ⟨5336963, by rfl⟩ : syracuseStep 7115951 = 10673927) B10673927
theorem B1873103 : Blo 1248442 1873103 := bstep (se 1 (by rfl) ⟨1404827, by rfl⟩ : syracuseStep 1873103 = 2809655) B2809655
theorem B4740383 : Blo 1248442 4740383 := bstep (se 1 (by rfl) ⟨3555287, by rfl⟩ : syracuseStep 4740383 = 7110575) B7110575
theorem B9008435 : Blo 1248442 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B6321563 : Blo 1248442 6321563 := bstep (se 1 (by rfl) ⟨4741172, by rfl⟩ : syracuseStep 6321563 = 9482345) B9482345
theorem B1873307 : Blo 1248442 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B12817889 : Blo 1248442 12817889 := bstep (se 2 (by rfl) ⟨4806708, by rfl⟩ : syracuseStep 12817889 = 9613417) B9613417
theorem B6329825 : Blo 1248442 6329825 := bstep (se 2 (by rfl) ⟨2373684, by rfl⟩ : syracuseStep 6329825 = 4747369) B4747369
theorem B1873529 : Blo 1248442 1873529 := bstep (se 2 (by rfl) ⟨702573, by rfl⟩ : syracuseStep 1873529 = 1405147) B1405147
theorem B24008339 : Blo 1248442 24008339 := bstep (se 1 (by rfl) ⟨18006254, by rfl⟩ : syracuseStep 24008339 = 36012509) B36012509
theorem B10680011 : Blo 1248442 10680011 := bstep (se 1 (by rfl) ⟨8010008, by rfl⟩ : syracuseStep 10680011 = 16020017) B16020017
theorem B1873631 : Blo 1248442 1873631 := bstep (se 1 (by rfl) ⟨1405223, by rfl⟩ : syracuseStep 1873631 = 2810447) B2810447
theorem B1873727 : Blo 1248442 1873727 := bstep (se 1 (by rfl) ⟨1405295, by rfl⟩ : syracuseStep 1873727 = 2810591) B2810591
theorem B1873895 : Blo 1248442 1873895 := bstep (se 1 (by rfl) ⟨1405421, by rfl⟩ : syracuseStep 1873895 = 2810843) B2810843
theorem B1873913 : Blo 1248442 1873913 := bstep (se 2 (by rfl) ⟨702717, by rfl⟩ : syracuseStep 1873913 = 1405435) B1405435
theorem B2373715 : Blo 1248442 2373715 := bstep (se 1 (by rfl) ⟨1780286, by rfl⟩ : syracuseStep 2373715 = 3560573) B3560573
theorem B1874015 : Blo 1248442 1874015 := bstep (se 1 (by rfl) ⟨1405511, by rfl⟩ : syracuseStep 1874015 = 2811023) B2811023
theorem B1874075 : Blo 1248442 1874075 := bstep (se 1 (by rfl) ⟨1405556, by rfl⟩ : syracuseStep 1874075 = 2811113) B2811113
theorem B1874111 : Blo 1248442 1874111 := bstep (se 1 (by rfl) ⟨1405583, by rfl⟩ : syracuseStep 1874111 = 2811167) B2811167
theorem B2250985 : Blo 1248442 2250985 := bstep (se 2 (by rfl) ⟨844119, by rfl⟩ : syracuseStep 2250985 = 1688239) B1688239
theorem B1874153 : Blo 1248442 1874153 := bstep (se 2 (by rfl) ⟨702807, by rfl⟩ : syracuseStep 1874153 = 1405615) B1405615
theorem B4217075 : Blo 1248442 4217075 := bstep (se 1 (by rfl) ⟨3162806, by rfl⟩ : syracuseStep 4217075 = 6325613) B6325613
theorem B4217129 : Blo 1248442 4217129 := bstep (se 2 (by rfl) ⟨1581423, by rfl⟩ : syracuseStep 4217129 = 3162847) B3162847
theorem B2136377 : Blo 1248442 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B1874459 : Blo 1248442 1874459 := bstep (se 1 (by rfl) ⟨1405844, by rfl⟩ : syracuseStep 1874459 = 2811689) B2811689
theorem B2251295 : Blo 1248442 2251295 := bstep (se 1 (by rfl) ⟨1688471, by rfl⟩ : syracuseStep 2251295 = 3376943) B3376943
theorem B7117409 : Blo 1248442 7117409 := bstep (se 2 (by rfl) ⟨2669028, by rfl⟩ : syracuseStep 7117409 = 5338057) B5338057
theorem B1874537 : Blo 1248442 1874537 := bstep (se 2 (by rfl) ⟨702951, by rfl⟩ : syracuseStep 1874537 = 1405903) B1405903
theorem B5069449 : Blo 1248442 5069449 := bstep (se 2 (by rfl) ⟨1901043, by rfl⟩ : syracuseStep 5069449 = 3802087) B3802087
theorem B18021017 : Blo 1248442 18021017 := bstep (se 2 (by rfl) ⟨6757881, by rfl⟩ : syracuseStep 18021017 = 13515763) B13515763
theorem B2136923 : Blo 1248442 2136923 := bstep (se 1 (by rfl) ⟨1602692, by rfl⟩ : syracuseStep 2136923 = 3205385) B3205385
theorem B8002475 : Blo 1248442 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B8223697 : Blo 1248442 8223697 := bstep (se 2 (by rfl) ⟨3083886, by rfl⟩ : syracuseStep 8223697 = 6167773) B6167773
theorem B1875065 : Blo 1248442 1875065 := bstep (se 2 (by rfl) ⟨703149, by rfl⟩ : syracuseStep 1875065 = 1406299) B1406299
theorem B1875167 : Blo 1248442 1875167 := bstep (se 1 (by rfl) ⟨1406375, by rfl⟩ : syracuseStep 1875167 = 2812751) B2812751
theorem B2809097 : Blo 1248442 2809097 := bstep (se 2 (by rfl) ⟨1053411, by rfl⟩ : syracuseStep 2809097 = 2106823) B2106823
theorem B1875209 : Blo 1248442 1875209 := bstep (se 2 (by rfl) ⟨703203, by rfl⟩ : syracuseStep 1875209 = 1406407) B1406407
theorem B4742495 : Blo 1248442 4742495 := bstep (se 1 (by rfl) ⟨3556871, by rfl⟩ : syracuseStep 4742495 = 7113743) B7113743
theorem B2669935 : Blo 1248442 2669935 := bstep (se 1 (by rfl) ⟨2002451, by rfl⟩ : syracuseStep 2669935 = 4004903) B4004903
theorem B1875311 : Blo 1248442 1875311 := bstep (se 1 (by rfl) ⟨1406483, by rfl⟩ : syracuseStep 1875311 = 2812967) B2812967
theorem B1875431 : Blo 1248442 1875431 := bstep (se 1 (by rfl) ⟨1406573, by rfl⟩ : syracuseStep 1875431 = 2813147) B2813147
theorem B2137691 : Blo 1248442 2137691 := bstep (se 1 (by rfl) ⟨1603268, by rfl⟩ : syracuseStep 2137691 = 3206537) B3206537
theorem B1875563 : Blo 1248442 1875563 := bstep (se 1 (by rfl) ⟨1406672, by rfl⟩ : syracuseStep 1875563 = 2813345) B2813345
theorem B14237369 : Blo 1248442 14237369 := bstep (se 2 (by rfl) ⟨5339013, by rfl⟩ : syracuseStep 14237369 = 10678027) B10678027
theorem B8117969 : Blo 1248442 8117969 := bstep (se 2 (by rfl) ⟨3044238, by rfl⟩ : syracuseStep 8117969 = 6088477) B6088477
theorem B3161825 : Blo 1248442 3161825 := bstep (se 2 (by rfl) ⟨1185684, by rfl⟩ : syracuseStep 3161825 = 2371369) B2371369
theorem B1900265 : Blo 1248442 1900265 := bstep (se 2 (by rfl) ⟨712599, by rfl⟩ : syracuseStep 1900265 = 1425199) B1425199
theorem B4218695 : Blo 1248442 4218695 := bstep (se 1 (by rfl) ⟨3164021, by rfl⟩ : syracuseStep 4218695 = 6328043) B6328043
theorem B15187819 : Blo 1248442 15187819 := bstep (se 1 (by rfl) ⟨11390864, by rfl⟩ : syracuseStep 15187819 = 22781729) B22781729
theorem B3555197 : Blo 1248442 3555197 := bstep (se 3 (by rfl) ⟨666599, by rfl⟩ : syracuseStep 3555197 = 1333199) B1333199
theorem B4218749 : Blo 1248442 4218749 := bstep (se 3 (by rfl) ⟨791015, by rfl⟩ : syracuseStep 4218749 = 1582031) B1582031
theorem B5341099 : Blo 1248442 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B10682401 : Blo 1248442 10682401 := bstep (se 2 (by rfl) ⟨4005900, by rfl⟩ : syracuseStep 10682401 = 8011801) B8011801
theorem B2809979 : Blo 1248442 2809979 := bstep (se 1 (by rfl) ⟨2107484, by rfl⟩ : syracuseStep 2809979 = 4214969) B4214969
theorem B12009707 : Blo 1248442 12009707 := bstep (se 1 (by rfl) ⟨9007280, by rfl⟩ : syracuseStep 12009707 = 18014561) B18014561
theorem B3162361 : Blo 1248442 3162361 := bstep (se 2 (by rfl) ⟨1185885, by rfl⟩ : syracuseStep 3162361 = 2371771) B2371771
theorem B5333273 : Blo 1248442 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B4743481 : Blo 1248442 4743481 := bstep (se 2 (by rfl) ⟨1778805, by rfl⟩ : syracuseStep 4743481 = 3557611) B3557611
theorem B2810249 : Blo 1248442 2810249 := bstep (se 2 (by rfl) ⟨1053843, by rfl⟩ : syracuseStep 2810249 = 2107687) B2107687
theorem B3203489 : Blo 1248442 3203489 := bstep (se 2 (by rfl) ⟨1201308, by rfl⟩ : syracuseStep 3203489 = 2402617) B2402617
theorem B4219559 : Blo 1248442 4219559 := bstep (se 1 (by rfl) ⟨3164669, by rfl⟩ : syracuseStep 4219559 = 6329339) B6329339
theorem B4743967 : Blo 1248442 4743967 := bstep (se 1 (by rfl) ⟨3557975, by rfl⟩ : syracuseStep 4743967 = 7115951) B7115951
theorem B6005623 : Blo 1248442 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B3163009 : Blo 1248442 3163009 := bstep (se 2 (by rfl) ⟨1186128, by rfl⟩ : syracuseStep 3163009 = 2372257) B2372257
theorem B8545259 : Blo 1248442 8545259 := bstep (se 1 (by rfl) ⟨6408944, by rfl⟩ : syracuseStep 8545259 = 12817889) B12817889
theorem B4219883 : Blo 1248442 4219883 := bstep (se 1 (by rfl) ⟨3164912, by rfl⟩ : syracuseStep 4219883 = 6329825) B6329825
theorem B7120007 : Blo 1248442 7120007 := bstep (se 1 (by rfl) ⟨5340005, by rfl⟩ : syracuseStep 7120007 = 10680011) B10680011
theorem B27387193 : Blo 1248442 27387193 := bstep (se 2 (by rfl) ⟨10270197, by rfl⟩ : syracuseStep 27387193 = 20540395) B20540395
theorem B2811383 : Blo 1248442 2811383 := bstep (se 1 (by rfl) ⟨2108537, by rfl⟩ : syracuseStep 2811383 = 4217075) B4217075
theorem B2811419 : Blo 1248442 2811419 := bstep (se 1 (by rfl) ⟨2108564, by rfl⟩ : syracuseStep 2811419 = 4217129) B4217129
theorem B3163819 : Blo 1248442 3163819 := bstep (se 1 (by rfl) ⟨2372864, by rfl⟩ : syracuseStep 3163819 = 4745729) B4745729
theorem B1500863 : Blo 1248442 1500863 := bstep (se 1 (by rfl) ⟨1125647, by rfl⟩ : syracuseStep 1500863 = 2251295) B2251295
theorem B4744939 : Blo 1248442 4744939 := bstep (se 1 (by rfl) ⟨3558704, by rfl⟩ : syracuseStep 4744939 = 7117409) B7117409
theorem B3999545 : Blo 1248442 3999545 := bstep (se 2 (by rfl) ⟨1499829, by rfl⟩ : syracuseStep 3999545 = 2999659) B2999659
theorem B5334983 : Blo 1248442 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B3164255 : Blo 1248442 3164255 := bstep (se 1 (by rfl) ⟨2373191, by rfl⟩ : syracuseStep 3164255 = 4746383) B4746383
theorem B3999905 : Blo 1248442 3999905 := bstep (se 2 (by rfl) ⟨1499964, by rfl⟩ : syracuseStep 3999905 = 2999929) B2999929
theorem B4745425 : Blo 1248442 4745425 := bstep (se 2 (by rfl) ⟨1779534, by rfl⟩ : syracuseStep 4745425 = 3559069) B3559069
theorem B20269493 : Blo 1248442 20269493 := bstep (se 5 (by rfl) ⟨950132, by rfl⟩ : syracuseStep 20269493 = 1900265) B1900265
theorem B2107883 : Blo 1248442 2107883 := bstep (se 1 (by rfl) ⟨1580912, by rfl⟩ : syracuseStep 2107883 = 3161825) B3161825
theorem B2812409 : Blo 1248442 2812409 := bstep (se 2 (by rfl) ⟨1054653, by rfl⟩ : syracuseStep 2812409 = 2109307) B2109307
theorem B2812463 : Blo 1248442 2812463 := bstep (se 1 (by rfl) ⟨2109347, by rfl⟩ : syracuseStep 2812463 = 4218695) B4218695
theorem B7121465 : Blo 1248442 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B2370131 : Blo 1248442 2370131 := bstep (se 1 (by rfl) ⟨1777598, by rfl⟩ : syracuseStep 2370131 = 3555197) B3555197
theorem B2812499 : Blo 1248442 2812499 := bstep (se 1 (by rfl) ⟨2109374, by rfl⟩ : syracuseStep 2812499 = 4218749) B4218749
theorem B2812679 : Blo 1248442 2812679 := bstep (se 1 (by rfl) ⟨2109509, by rfl⟩ : syracuseStep 2812679 = 4219019) B4219019
theorem B3164953 : Blo 1248442 3164953 := bstep (se 2 (by rfl) ⟨1186857, by rfl⟩ : syracuseStep 3164953 = 2373715) B2373715
theorem B5409575 : Blo 1248442 5409575 := bstep (se 1 (by rfl) ⟨4057181, by rfl⟩ : syracuseStep 5409575 = 8114363) B8114363
theorem B2812895 : Blo 1248442 2812895 := bstep (se 1 (by rfl) ⟨2109671, by rfl⟩ : syracuseStep 2812895 = 4219343) B4219343
theorem B3001313 : Blo 1248442 3001313 := bstep (se 2 (by rfl) ⟨1125492, by rfl⟩ : syracuseStep 3001313 = 2250985) B2250985
theorem B2165815 : Blo 1248442 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B3558455 : Blo 1248442 3558455 := bstep (se 1 (by rfl) ⟨2668841, by rfl⟩ : syracuseStep 3558455 = 5337683) B5337683
theorem B2108585 : Blo 1248442 2108585 := bstep (se 2 (by rfl) ⟨790719, by rfl⟩ : syracuseStep 2108585 = 1581439) B1581439
theorem B2813111 : Blo 1248442 2813111 := bstep (se 1 (by rfl) ⟨2109833, by rfl⟩ : syracuseStep 2813111 = 4219667) B4219667
theorem B10669279 : Blo 1248442 10669279 := bstep (se 1 (by rfl) ⟨8001959, by rfl⟩ : syracuseStep 10669279 = 16003919) B16003919
theorem B1248639 : Blo 1248442 1248639 := bstep (se 1 (by rfl) ⟨936479, by rfl⟩ : syracuseStep 1248639 = 1872959) B1872959
theorem B27037061 : Blo 1248442 27037061 := bstep (se 4 (by rfl) ⟨2534724, by rfl⟩ : syracuseStep 27037061 = 5069449) B5069449
theorem B1248667 : Blo 1248442 1248667 := bstep (se 1 (by rfl) ⟨936500, by rfl⟩ : syracuseStep 1248667 = 1873001) B1873001
theorem B14232995 : Blo 1248442 14232995 := bstep (se 1 (by rfl) ⟨10674746, by rfl⟩ : syracuseStep 14232995 = 21349493) B21349493
theorem B2371027 : Blo 1248442 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B1248735 : Blo 1248442 1248735 := bstep (se 1 (by rfl) ⟨936551, by rfl⟩ : syracuseStep 1248735 = 1873103) B1873103
theorem B6327881 : Blo 1248442 6327881 := bstep (se 2 (by rfl) ⟨2372955, by rfl⟩ : syracuseStep 6327881 = 4745911) B4745911
theorem B4214375 : Blo 1248442 4214375 := bstep (se 1 (by rfl) ⟨3160781, by rfl⟩ : syracuseStep 4214375 = 6321563) B6321563
theorem B1248871 : Blo 1248442 1248871 := bstep (se 1 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 1248871 = 1873307) B1873307
theorem B61574849 : Blo 1248442 61574849 := bstep (se 2 (by rfl) ⟨23090568, by rfl⟩ : syracuseStep 61574849 = 46181137) B46181137
theorem B1249019 : Blo 1248442 1249019 := bstep (se 1 (by rfl) ⟨936764, by rfl⟩ : syracuseStep 1249019 = 1873529) B1873529
theorem B2109179 : Blo 1248442 2109179 := bstep (se 1 (by rfl) ⟨1581884, by rfl⟩ : syracuseStep 2109179 = 3163769) B3163769
theorem B1249087 : Blo 1248442 1249087 := bstep (se 1 (by rfl) ⟨936815, by rfl⟩ : syracuseStep 1249087 = 1873631) B1873631
theorem B6008681 : Blo 1248442 6008681 := bstep (se 2 (by rfl) ⟨2253255, by rfl⟩ : syracuseStep 6008681 = 4506511) B4506511
theorem B1249151 : Blo 1248442 1249151 := bstep (se 1 (by rfl) ⟨936863, by rfl⟩ : syracuseStep 1249151 = 1873727) B1873727
theorem B1249263 : Blo 1248442 1249263 := bstep (se 1 (by rfl) ⟨936947, by rfl⟩ : syracuseStep 1249263 = 1873895) B1873895
theorem B1249275 : Blo 1248442 1249275 := bstep (se 1 (by rfl) ⟨936956, by rfl⟩ : syracuseStep 1249275 = 1873913) B1873913
theorem B1249343 : Blo 1248442 1249343 := bstep (se 1 (by rfl) ⟨937007, by rfl⟩ : syracuseStep 1249343 = 1874015) B1874015
theorem B1249383 : Blo 1248442 1249383 := bstep (se 1 (by rfl) ⟨937037, by rfl⟩ : syracuseStep 1249383 = 1874075) B1874075
theorem B1249407 : Blo 1248442 1249407 := bstep (se 1 (by rfl) ⟨937055, by rfl⟩ : syracuseStep 1249407 = 1874111) B1874111
theorem B1249435 : Blo 1248442 1249435 := bstep (se 1 (by rfl) ⟨937076, by rfl⟩ : syracuseStep 1249435 = 1874153) B1874153
theorem B2371817 : Blo 1248442 2371817 := bstep (se 2 (by rfl) ⟨889431, by rfl⟩ : syracuseStep 2371817 = 1778863) B1778863
theorem B1249639 : Blo 1248442 1249639 := bstep (se 1 (by rfl) ⟨937229, by rfl⟩ : syracuseStep 1249639 = 1874459) B1874459
theorem B1249691 : Blo 1248442 1249691 := bstep (se 1 (by rfl) ⟨937268, by rfl⟩ : syracuseStep 1249691 = 1874537) B1874537
theorem B12014011 : Blo 1248442 12014011 := bstep (se 1 (by rfl) ⟨9010508, by rfl⟩ : syracuseStep 12014011 = 18021017) B18021017
theorem B6320591 : Blo 1248442 6320591 := bstep (se 1 (by rfl) ⟨4740443, by rfl⟩ : syracuseStep 6320591 = 9480887) B9480887
theorem B3559913 : Blo 1248442 3559913 := bstep (se 2 (by rfl) ⟨1334967, by rfl⟩ : syracuseStep 3559913 = 2669935) B2669935
theorem B21647917 : Blo 1248442 21647917 := bstep (se 3 (by rfl) ⟨4058984, by rfl⟩ : syracuseStep 21647917 = 8117969) B8117969
theorem B1250043 : Blo 1248442 1250043 := bstep (se 1 (by rfl) ⟨937532, by rfl⟩ : syracuseStep 1250043 = 1875065) B1875065
theorem B1405759 : Blo 1248442 1405759 := bstep (se 1 (by rfl) ⟨1054319, by rfl⟩ : syracuseStep 1405759 = 2108639) B2108639
theorem B1250111 : Blo 1248442 1250111 := bstep (se 1 (by rfl) ⟨937583, by rfl⟩ : syracuseStep 1250111 = 1875167) B1875167
theorem B1872731 : Blo 1248442 1872731 := bstep (se 1 (by rfl) ⟨1404548, by rfl⟩ : syracuseStep 1872731 = 2809097) B2809097
theorem B1250139 : Blo 1248442 1250139 := bstep (se 1 (by rfl) ⟨937604, by rfl⟩ : syracuseStep 1250139 = 1875209) B1875209
theorem B1250207 : Blo 1248442 1250207 := bstep (se 1 (by rfl) ⟨937655, by rfl⟩ : syracuseStep 1250207 = 1875311) B1875311
theorem B1250287 : Blo 1248442 1250287 := bstep (se 1 (by rfl) ⟨937715, by rfl⟩ : syracuseStep 1250287 = 1875431) B1875431
theorem B1250375 : Blo 1248442 1250375 := bstep (se 1 (by rfl) ⟨937781, by rfl⟩ : syracuseStep 1250375 = 1875563) B1875563
theorem B1406047 : Blo 1248442 1406047 := bstep (se 1 (by rfl) ⟨1054535, by rfl⟩ : syracuseStep 1406047 = 2109071) B2109071
theorem B9491579 : Blo 1248442 9491579 := bstep (se 1 (by rfl) ⟨7118684, by rfl⟩ : syracuseStep 9491579 = 14237369) B14237369
theorem B152040719 : Blo 1248442 152040719 := bstep (se 1 (by rfl) ⟨114030539, by rfl⟩ : syracuseStep 152040719 = 228061079) B228061079
theorem B5338399 : Blo 1248442 5338399 := bstep (se 1 (by rfl) ⟨4003799, by rfl⟩ : syracuseStep 5338399 = 8007599) B8007599
theorem B1873193 : Blo 1248442 1873193 := bstep (se 2 (by rfl) ⟨702447, by rfl⟩ : syracuseStep 1873193 = 1404895) B1404895
theorem B2848063 : Blo 1248442 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B8009189 : Blo 1248442 8009189 := bstep (se 4 (by rfl) ⟨750861, by rfl⟩ : syracuseStep 8009189 = 1501723) B1501723
theorem B1873391 : Blo 1248442 1873391 := bstep (se 1 (by rfl) ⟨1405043, by rfl⟩ : syracuseStep 1873391 = 2810087) B2810087
theorem B8009239 : Blo 1248442 8009239 := bstep (se 1 (by rfl) ⟨6006929, by rfl⟩ : syracuseStep 8009239 = 12013859) B12013859
theorem B1873787 : Blo 1248442 1873787 := bstep (se 1 (by rfl) ⟨1405340, by rfl⟩ : syracuseStep 1873787 = 2810681) B2810681
theorem B1873823 : Blo 1248442 1873823 := bstep (se 1 (by rfl) ⟨1405367, by rfl⟩ : syracuseStep 1873823 = 2810735) B2810735
theorem B2668585 : Blo 1248442 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B1874057 : Blo 1248442 1874057 := bstep (se 2 (by rfl) ⟨702771, by rfl⟩ : syracuseStep 1874057 = 1405543) B1405543
theorem B3160255 : Blo 1248442 3160255 := bstep (se 1 (by rfl) ⟨2370191, by rfl⟩ : syracuseStep 3160255 = 4740383) B4740383
theorem B1874207 : Blo 1248442 1874207 := bstep (se 1 (by rfl) ⟨1405655, by rfl⟩ : syracuseStep 1874207 = 2811311) B2811311
theorem B4741537 : Blo 1248442 4741537 := bstep (se 2 (by rfl) ⟨1778076, by rfl⟩ : syracuseStep 4741537 = 3556153) B3556153
theorem B16005559 : Blo 1248442 16005559 := bstep (se 1 (by rfl) ⟨12004169, by rfl⟩ : syracuseStep 16005559 = 24008339) B24008339
theorem B45570761 : Blo 1248442 45570761 := bstep (se 2 (by rfl) ⟨17089035, by rfl⟩ : syracuseStep 45570761 = 34178071) B34178071
theorem B5413643 : Blo 1248442 5413643 := bstep (se 1 (by rfl) ⟨4060232, by rfl⟩ : syracuseStep 5413643 = 8120465) B8120465
theorem B1874759 : Blo 1248442 1874759 := bstep (se 1 (by rfl) ⟨1406069, by rfl⟩ : syracuseStep 1874759 = 2812139) B2812139
theorem B1424251 : Blo 1248442 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B6413275 : Blo 1248442 6413275 := bstep (se 1 (by rfl) ⟨4809956, by rfl⟩ : syracuseStep 6413275 = 9619913) B9619913
theorem B4742327 : Blo 1248442 4742327 := bstep (se 1 (by rfl) ⟨3556745, by rfl⟩ : syracuseStep 4742327 = 7113491) B7113491
theorem B1580239 : Blo 1248442 1580239 := bstep (se 1 (by rfl) ⟨1185179, by rfl⟩ : syracuseStep 1580239 = 2370359) B2370359
theorem B1424615 : Blo 1248442 1424615 := bstep (se 1 (by rfl) ⟨1068461, by rfl⟩ : syracuseStep 1424615 = 2136923) B2136923
theorem B4742509 : Blo 1248442 4742509 := bstep (se 3 (by rfl) ⟨889220, by rfl⟩ : syracuseStep 4742509 = 1778441) B1778441
theorem B3161663 : Blo 1248442 3161663 := bstep (se 1 (by rfl) ⟨2371247, by rfl⟩ : syracuseStep 3161663 = 4742495) B4742495
theorem B2809511 : Blo 1248442 2809511 := bstep (se 1 (by rfl) ⟨2107133, by rfl⟩ : syracuseStep 2809511 = 4214267) B4214267
theorem B1875623 : Blo 1248442 1875623 := bstep (se 1 (by rfl) ⟨1406717, by rfl⟩ : syracuseStep 1875623 = 2813435) B2813435
theorem B1425127 : Blo 1248442 1425127 := bstep (se 1 (by rfl) ⟨1068845, by rfl⟩ : syracuseStep 1425127 = 2137691) B2137691
theorem B43859717 : Blo 1248442 43859717 := bstep (se 4 (by rfl) ⟨4111848, by rfl⟩ : syracuseStep 43859717 = 8223697) B8223697
theorem B2809619 : Blo 1248442 2809619 := bstep (se 1 (by rfl) ⟨2107214, by rfl⟩ : syracuseStep 2809619 = 4214429) B4214429
theorem B20250425 : Blo 1248442 20250425 := bstep (se 2 (by rfl) ⟨7593909, by rfl⟩ : syracuseStep 20250425 = 15187819) B15187819
theorem B1581211 : Blo 1248442 1581211 := bstep (se 1 (by rfl) ⟨1185908, by rfl⟩ : syracuseStep 1581211 = 2371817) B2371817
theorem B3555515 : Blo 1248442 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B6324641 : Blo 1248442 6324641 := bstep (se 2 (by rfl) ⟨2371740, by rfl⟩ : syracuseStep 6324641 = 4743481) B4743481
theorem B21340745 : Blo 1248442 21340745 := bstep (se 2 (by rfl) ⟨8002779, by rfl⟩ : syracuseStep 21340745 = 16005559) B16005559
theorem B101360479 : Blo 1248442 101360479 := bstep (se 1 (by rfl) ⟨76020359, by rfl⟩ : syracuseStep 101360479 = 152040719) B152040719
theorem B4219937 : Blo 1248442 4219937 := bstep (se 2 (by rfl) ⟨1582476, by rfl⟩ : syracuseStep 4219937 = 3164953) B3164953
theorem B6325289 : Blo 1248442 6325289 := bstep (se 2 (by rfl) ⟨2371983, by rfl⟩ : syracuseStep 6325289 = 4743967) B4743967
theorem B3556655 : Blo 1248442 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B2106985 : Blo 1248442 2106985 := bstep (se 2 (by rfl) ⟨790119, by rfl⟩ : syracuseStep 2106985 = 1580239) B1580239
theorem B3606383 : Blo 1248442 3606383 := bstep (se 1 (by rfl) ⟨2704787, by rfl⟩ : syracuseStep 3606383 = 5409575) B5409575
theorem B2000875 : Blo 1248442 2000875 := bstep (se 1 (by rfl) ⟨1500656, by rfl⟩ : syracuseStep 2000875 = 3001313) B3001313
theorem B18024707 : Blo 1248442 18024707 := bstep (se 1 (by rfl) ⟨13518530, by rfl⟩ : syracuseStep 18024707 = 27037061) B27037061
theorem B9488663 : Blo 1248442 9488663 := bstep (se 1 (by rfl) ⟨7116497, by rfl⟩ : syracuseStep 9488663 = 14232995) B14232995
theorem B6326585 : Blo 1248442 6326585 := bstep (se 2 (by rfl) ⟨2372469, by rfl⟩ : syracuseStep 6326585 = 4744939) B4744939
theorem B2107775 : Blo 1248442 2107775 := bstep (se 1 (by rfl) ⟨1580831, by rfl⟩ : syracuseStep 2107775 = 3161663) B3161663
theorem B34204133 : Blo 1248442 34204133 := bstep (se 4 (by rfl) ⟨3206637, by rfl⟩ : syracuseStep 34204133 = 6413275) B6413275
theorem B29239811 : Blo 1248442 29239811 := bstep (se 1 (by rfl) ⟨21929858, by rfl⟩ : syracuseStep 29239811 = 43859717) B43859717
theorem B3558113 : Blo 1248442 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B8006471 : Blo 1248442 8006471 := bstep (se 1 (by rfl) ⟨6004853, by rfl⟩ : syracuseStep 8006471 = 12009707) B12009707
theorem B4213673 : Blo 1248442 4213673 := bstep (se 2 (by rfl) ⟨1580127, by rfl⟩ : syracuseStep 4213673 = 3160255) B3160255
theorem B6327233 : Blo 1248442 6327233 := bstep (se 2 (by rfl) ⟨2372712, by rfl⟩ : syracuseStep 6327233 = 4745425) B4745425
theorem B4213727 : Blo 1248442 4213727 := bstep (se 1 (by rfl) ⟨3160295, by rfl⟩ : syracuseStep 4213727 = 6320591) B6320591
theorem B2813039 : Blo 1248442 2813039 := bstep (se 1 (by rfl) ⟨2109779, by rfl⟩ : syracuseStep 2813039 = 4219559) B4219559
theorem B1248487 : Blo 1248442 1248487 := bstep (se 1 (by rfl) ⟨936365, by rfl⟩ : syracuseStep 1248487 = 1872731) B1872731
theorem B16018681 : Blo 1248442 16018681 := bstep (se 2 (by rfl) ⟨6007005, by rfl⟩ : syracuseStep 16018681 = 12014011) B12014011
theorem B5696839 : Blo 1248442 5696839 := bstep (se 1 (by rfl) ⟨4272629, by rfl⟩ : syracuseStep 5696839 = 8545259) B8545259
theorem B2813255 : Blo 1248442 2813255 := bstep (se 1 (by rfl) ⟨2109941, by rfl⟩ : syracuseStep 2813255 = 4219883) B4219883
theorem B6327719 : Blo 1248442 6327719 := bstep (se 1 (by rfl) ⟨4745789, by rfl⟩ : syracuseStep 6327719 = 9491579) B9491579
theorem B4746671 : Blo 1248442 4746671 := bstep (se 1 (by rfl) ⟨3560003, by rfl⟩ : syracuseStep 4746671 = 7120007) B7120007
theorem B1248795 : Blo 1248442 1248795 := bstep (se 1 (by rfl) ⟨936596, by rfl⟩ : syracuseStep 1248795 = 1873193) B1873193
theorem B1248927 : Blo 1248442 1248927 := bstep (se 1 (by rfl) ⟨936695, by rfl⟩ : syracuseStep 1248927 = 1873391) B1873391
theorem B8007497 : Blo 1248442 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B2666363 : Blo 1248442 2666363 := bstep (se 1 (by rfl) ⟨1999772, by rfl⟩ : syracuseStep 2666363 = 3999545) B3999545
theorem B1249191 : Blo 1248442 1249191 := bstep (se 1 (by rfl) ⟨936893, by rfl⟩ : syracuseStep 1249191 = 1873787) B1873787
theorem B1249215 : Blo 1248442 1249215 := bstep (se 1 (by rfl) ⟨936911, by rfl⟩ : syracuseStep 1249215 = 1873823) B1873823
theorem B2109503 : Blo 1248442 2109503 := bstep (se 1 (by rfl) ⟨1582127, by rfl⟩ : syracuseStep 2109503 = 3164255) B3164255
theorem B2887753 : Blo 1248442 2887753 := bstep (se 2 (by rfl) ⟨1082907, by rfl⟩ : syracuseStep 2887753 = 2165815) B2165815
theorem B1249371 : Blo 1248442 1249371 := bstep (se 1 (by rfl) ⟨937028, by rfl⟩ : syracuseStep 1249371 = 1874057) B1874057
theorem B2666603 : Blo 1248442 2666603 := bstep (se 1 (by rfl) ⟨1999952, by rfl⟩ : syracuseStep 2666603 = 3999905) B3999905
theorem B1249471 : Blo 1248442 1249471 := bstep (se 1 (by rfl) ⟨937103, by rfl⟩ : syracuseStep 1249471 = 1874207) B1874207
theorem B14225705 : Blo 1248442 14225705 := bstep (se 2 (by rfl) ⟨5334639, by rfl⟩ : syracuseStep 14225705 = 10669279) B10669279
theorem B13512995 : Blo 1248442 13512995 := bstep (se 1 (by rfl) ⟨10134746, by rfl⟩ : syracuseStep 13512995 = 20269493) B20269493
theorem B1405255 : Blo 1248442 1405255 := bstep (se 1 (by rfl) ⟨1053941, by rfl⟩ : syracuseStep 1405255 = 2107883) B2107883
theorem B4747643 : Blo 1248442 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B36516257 : Blo 1248442 36516257 := bstep (se 2 (by rfl) ⟨13693596, by rfl⟩ : syracuseStep 36516257 = 27387193) B27387193
theorem B3797417 : Blo 1248442 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B30380507 : Blo 1248442 30380507 := bstep (se 1 (by rfl) ⟨22785380, by rfl⟩ : syracuseStep 30380507 = 45570761) B45570761
theorem B4002301 : Blo 1248442 4002301 := bstep (se 3 (by rfl) ⟨750431, by rfl⟩ : syracuseStep 4002301 = 1500863) B1500863
theorem B3609095 : Blo 1248442 3609095 := bstep (se 1 (by rfl) ⟨2706821, by rfl⟩ : syracuseStep 3609095 = 5413643) B5413643
theorem B1249839 : Blo 1248442 1249839 := bstep (se 1 (by rfl) ⟨937379, by rfl⟩ : syracuseStep 1249839 = 1874759) B1874759
theorem B10678985 : Blo 1248442 10678985 := bstep (se 2 (by rfl) ⟨4004619, by rfl⟩ : syracuseStep 10678985 = 8009239) B8009239
theorem B2372303 : Blo 1248442 2372303 := bstep (se 1 (by rfl) ⟨1779227, by rfl⟩ : syracuseStep 2372303 = 3558455) B3558455
theorem B1405723 : Blo 1248442 1405723 := bstep (se 1 (by rfl) ⟨1054292, by rfl⟩ : syracuseStep 1405723 = 2108585) B2108585
theorem B1873007 : Blo 1248442 1873007 := bstep (se 1 (by rfl) ⟨1404755, by rfl⟩ : syracuseStep 1873007 = 2809511) B2809511
theorem B1250415 : Blo 1248442 1250415 := bstep (se 1 (by rfl) ⟨937811, by rfl⟩ : syracuseStep 1250415 = 1875623) B1875623
theorem B1406119 : Blo 1248442 1406119 := bstep (se 1 (by rfl) ⟨1054589, by rfl⟩ : syracuseStep 1406119 = 2109179) B2109179
theorem B1873079 : Blo 1248442 1873079 := bstep (se 1 (by rfl) ⟨1404809, by rfl⟩ : syracuseStep 1873079 = 2809619) B2809619
theorem B14243201 : Blo 1248442 14243201 := bstep (se 2 (by rfl) ⟨5341200, by rfl⟩ : syracuseStep 14243201 = 10682401) B10682401
theorem B1873319 : Blo 1248442 1873319 := bstep (se 1 (by rfl) ⟨1404989, by rfl⟩ : syracuseStep 1873319 = 2809979) B2809979
theorem B115455557 : Blo 1248442 115455557 := bstep (se 4 (by rfl) ⟨10823958, by rfl⟩ : syracuseStep 115455557 = 21647917) B21647917
theorem B1873499 : Blo 1248442 1873499 := bstep (se 1 (by rfl) ⟨1405124, by rfl⟩ : syracuseStep 1873499 = 2810249) B2810249
theorem B2135659 : Blo 1248442 2135659 := bstep (se 1 (by rfl) ⟨1601744, by rfl⟩ : syracuseStep 2135659 = 3203489) B3203489
theorem B2373275 : Blo 1248442 2373275 := bstep (se 1 (by rfl) ⟨1779956, by rfl⟩ : syracuseStep 2373275 = 3559913) B3559913
theorem B4216481 : Blo 1248442 4216481 := bstep (se 2 (by rfl) ⟨1581180, by rfl⟩ : syracuseStep 4216481 = 3162361) B3162361
theorem B6322049 : Blo 1248442 6322049 := bstep (se 2 (by rfl) ⟨2370768, by rfl⟩ : syracuseStep 6322049 = 4741537) B4741537
theorem B3798973 : Blo 1248442 3798973 := bstep (se 3 (by rfl) ⟨712307, by rfl⟩ : syracuseStep 3798973 = 1424615) B1424615
theorem B5339459 : Blo 1248442 5339459 := bstep (se 1 (by rfl) ⟨4004594, by rfl⟩ : syracuseStep 5339459 = 8009189) B8009189
theorem B1874255 : Blo 1248442 1874255 := bstep (se 1 (by rfl) ⟨1405691, by rfl⟩ : syracuseStep 1874255 = 2811383) B2811383
theorem B1874279 : Blo 1248442 1874279 := bstep (se 1 (by rfl) ⟨1405709, by rfl⟩ : syracuseStep 1874279 = 2811419) B2811419
theorem B1874345 : Blo 1248442 1874345 := bstep (se 2 (by rfl) ⟨702879, by rfl⟩ : syracuseStep 1874345 = 1405759) B1405759
theorem B1899001 : Blo 1248442 1899001 := bstep (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) B1424251
theorem B4217345 : Blo 1248442 4217345 := bstep (se 2 (by rfl) ⟨1581504, by rfl⟩ : syracuseStep 4217345 = 3163009) B3163009
theorem B1874729 : Blo 1248442 1874729 := bstep (se 2 (by rfl) ⟨703023, by rfl⟩ : syracuseStep 1874729 = 1406047) B1406047
theorem B1874939 : Blo 1248442 1874939 := bstep (se 1 (by rfl) ⟨1406204, by rfl⟩ : syracuseStep 1874939 = 2812409) B2812409
theorem B1874975 : Blo 1248442 1874975 := bstep (se 1 (by rfl) ⟨1406231, by rfl⟩ : syracuseStep 1874975 = 2812463) B2812463
theorem B7117865 : Blo 1248442 7117865 := bstep (se 2 (by rfl) ⟨2669199, by rfl⟩ : syracuseStep 7117865 = 5338399) B5338399
theorem B1580087 : Blo 1248442 1580087 := bstep (se 1 (by rfl) ⟨1185065, by rfl⟩ : syracuseStep 1580087 = 2370131) B2370131
theorem B1874999 : Blo 1248442 1874999 := bstep (se 1 (by rfl) ⟨1406249, by rfl⟩ : syracuseStep 1874999 = 2812499) B2812499
theorem B6323345 : Blo 1248442 6323345 := bstep (se 2 (by rfl) ⟨2371254, by rfl⟩ : syracuseStep 6323345 = 4742509) B4742509
theorem B1875119 : Blo 1248442 1875119 := bstep (se 1 (by rfl) ⟨1406339, by rfl⟩ : syracuseStep 1875119 = 2812679) B2812679
theorem B3161369 : Blo 1248442 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B1875263 : Blo 1248442 1875263 := bstep (se 1 (by rfl) ⟨1406447, by rfl⟩ : syracuseStep 1875263 = 2812895) B2812895
theorem B3161551 : Blo 1248442 3161551 := bstep (se 1 (by rfl) ⟨2371163, by rfl⟩ : syracuseStep 3161551 = 4742327) B4742327
theorem B1875407 : Blo 1248442 1875407 := bstep (se 1 (by rfl) ⟨1406555, by rfl⟩ : syracuseStep 1875407 = 2813111) B2813111
theorem B4218425 : Blo 1248442 4218425 := bstep (se 2 (by rfl) ⟨1581909, by rfl⟩ : syracuseStep 4218425 = 3163819) B3163819
theorem B1900169 : Blo 1248442 1900169 := bstep (se 2 (by rfl) ⟨712563, by rfl⟩ : syracuseStep 1900169 = 1425127) B1425127
theorem B4218587 : Blo 1248442 4218587 := bstep (se 1 (by rfl) ⟨3163940, by rfl⟩ : syracuseStep 4218587 = 6327881) B6327881
theorem B2809583 : Blo 1248442 2809583 := bstep (se 1 (by rfl) ⟨2107187, by rfl⟩ : syracuseStep 2809583 = 4214375) B4214375
theorem B41049899 : Blo 1248442 41049899 := bstep (se 1 (by rfl) ⟨30787424, by rfl⟩ : syracuseStep 41049899 = 61574849) B61574849
theorem B13500283 : Blo 1248442 13500283 := bstep (se 1 (by rfl) ⟨10125212, by rfl⟩ : syracuseStep 13500283 = 20250425) B20250425
theorem B4005787 : Blo 1248442 4005787 := bstep (se 1 (by rfl) ⟨3004340, by rfl⟩ : syracuseStep 4005787 = 6008681) B6008681
theorem B1777735 : Blo 1248442 1777735 := bstep (se 1 (by rfl) ⟨1333301, by rfl⟩ : syracuseStep 1777735 = 2666603) B2666603
theorem B3850337 : Blo 1248442 3850337 := bstep (se 2 (by rfl) ⟨1443876, by rfl⟩ : syracuseStep 3850337 = 2887753) B2887753
theorem B2531611 : Blo 1248442 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B7119323 : Blo 1248442 7119323 := bstep (se 1 (by rfl) ⟨5339492, by rfl⟩ : syracuseStep 7119323 = 10678985) B10678985
theorem B1581535 : Blo 1248442 1581535 := bstep (se 1 (by rfl) ⟨1186151, by rfl⟩ : syracuseStep 1581535 = 2372303) B2372303
theorem B2532001 : Blo 1248442 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B9495467 : Blo 1248442 9495467 := bstep (se 1 (by rfl) ⟨7121600, by rfl⟩ : syracuseStep 9495467 = 14243201) B14243201
theorem B1582183 : Blo 1248442 1582183 := bstep (se 1 (by rfl) ⟨1186637, by rfl⟩ : syracuseStep 1582183 = 2373275) B2373275
theorem B2810987 : Blo 1248442 2810987 := bstep (se 1 (by rfl) ⟨2108240, by rfl⟩ : syracuseStep 2810987 = 4216481) B4216481
theorem B307881485 : Blo 1248442 307881485 := bstep (se 3 (by rfl) ⟨57727778, by rfl⟩ : syracuseStep 307881485 = 115455557) B115455557
theorem B6325775 : Blo 1248442 6325775 := bstep (se 1 (by rfl) ⟨4744331, by rfl⟩ : syracuseStep 6325775 = 9488663) B9488663
theorem B21358241 : Blo 1248442 21358241 := bstep (se 2 (by rfl) ⟨8009340, by rfl⟩ : syracuseStep 21358241 = 16018681) B16018681
theorem B2811563 : Blo 1248442 2811563 := bstep (se 1 (by rfl) ⟨2108672, by rfl⟩ : syracuseStep 2811563 = 4217345) B4217345
theorem B7595785 : Blo 1248442 7595785 := bstep (se 2 (by rfl) ⟨2848419, by rfl⟩ : syracuseStep 7595785 = 5696839) B5696839
theorem B4745243 : Blo 1248442 4745243 := bstep (se 1 (by rfl) ⟨3558932, by rfl⟩ : syracuseStep 4745243 = 7117865) B7117865
theorem B2107579 : Blo 1248442 2107579 := bstep (se 1 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 2107579 = 3161369) B3161369
theorem B3164447 : Blo 1248442 3164447 := bstep (se 1 (by rfl) ⟨2373335, by rfl⟩ : syracuseStep 3164447 = 4746671) B4746671
theorem B2812283 : Blo 1248442 2812283 := bstep (se 1 (by rfl) ⟨2109212, by rfl⟩ : syracuseStep 2812283 = 4218425) B4218425
theorem B2812391 : Blo 1248442 2812391 := bstep (se 1 (by rfl) ⟨2109293, by rfl⟩ : syracuseStep 2812391 = 4218587) B4218587
theorem B18000377 : Blo 1248442 18000377 := bstep (se 2 (by rfl) ⟨6750141, by rfl⟩ : syracuseStep 18000377 = 13500283) B13500283
theorem B5065297 : Blo 1248442 5065297 := bstep (se 2 (by rfl) ⟨1899486, by rfl⟩ : syracuseStep 5065297 = 3798973) B3798973
theorem B4213565 : Blo 1248442 4213565 := bstep (se 3 (by rfl) ⟨790043, by rfl⟩ : syracuseStep 4213565 = 1580087) B1580087
theorem B2108281 : Blo 1248442 2108281 := bstep (se 2 (by rfl) ⟨790605, by rfl⟩ : syracuseStep 2108281 = 1581211) B1581211
theorem B3165095 : Blo 1248442 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B20253671 : Blo 1248442 20253671 := bstep (se 1 (by rfl) ⟨15190253, by rfl⟩ : syracuseStep 20253671 = 30380507) B30380507
theorem B9481373 : Blo 1248442 9481373 := bstep (se 3 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 9481373 = 3555515) B3555515
theorem B5336401 : Blo 1248442 5336401 := bstep (se 2 (by rfl) ⟨2001150, by rfl⟩ : syracuseStep 5336401 = 4002301) B4002301
theorem B48065885 : Blo 1248442 48065885 := bstep (se 3 (by rfl) ⟨9012353, by rfl⟩ : syracuseStep 48065885 = 18024707) B18024707
theorem B2813291 : Blo 1248442 2813291 := bstep (se 1 (by rfl) ⟨2109968, by rfl⟩ : syracuseStep 2813291 = 4219937) B4219937
theorem B1248671 : Blo 1248442 1248671 := bstep (se 1 (by rfl) ⟨936503, by rfl⟩ : syracuseStep 1248671 = 1873007) B1873007
theorem B1248719 : Blo 1248442 1248719 := bstep (se 1 (by rfl) ⟨936539, by rfl⟩ : syracuseStep 1248719 = 1873079) B1873079
theorem B2371103 : Blo 1248442 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B1248879 : Blo 1248442 1248879 := bstep (se 1 (by rfl) ⟨936659, by rfl⟩ : syracuseStep 1248879 = 1873319) B1873319
theorem B1248999 : Blo 1248442 1248999 := bstep (se 1 (by rfl) ⟨936749, by rfl⟩ : syracuseStep 1248999 = 1873499) B1873499
theorem B135147305 : Blo 1248442 135147305 := bstep (se 2 (by rfl) ⟨50680239, by rfl⟩ : syracuseStep 135147305 = 101360479) B101360479
theorem B2404255 : Blo 1248442 2404255 := bstep (se 1 (by rfl) ⟨1803191, by rfl⟩ : syracuseStep 2404255 = 3606383) B3606383
theorem B4214699 : Blo 1248442 4214699 := bstep (se 1 (by rfl) ⟨3161024, by rfl⟩ : syracuseStep 4214699 = 6322049) B6322049
theorem B3559639 : Blo 1248442 3559639 := bstep (se 1 (by rfl) ⟨2669729, by rfl⟩ : syracuseStep 3559639 = 5339459) B5339459
theorem B1249503 : Blo 1248442 1249503 := bstep (se 1 (by rfl) ⟨937127, by rfl⟩ : syracuseStep 1249503 = 1874255) B1874255
theorem B1249519 : Blo 1248442 1249519 := bstep (se 1 (by rfl) ⟨937139, by rfl⟩ : syracuseStep 1249519 = 1874279) B1874279
theorem B1405183 : Blo 1248442 1405183 := bstep (se 1 (by rfl) ⟨1053887, by rfl⟩ : syracuseStep 1405183 = 2107775) B2107775
theorem B1249563 : Blo 1248442 1249563 := bstep (se 1 (by rfl) ⟨937172, by rfl⟩ : syracuseStep 1249563 = 1874345) B1874345
theorem B22802755 : Blo 1248442 22802755 := bstep (se 1 (by rfl) ⟨17102066, by rfl⟩ : syracuseStep 22802755 = 34204133) B34204133
theorem B19493207 : Blo 1248442 19493207 := bstep (se 1 (by rfl) ⟨14619905, by rfl⟩ : syracuseStep 19493207 = 29239811) B29239811
theorem B2372075 : Blo 1248442 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B1249819 : Blo 1248442 1249819 := bstep (se 1 (by rfl) ⟨937364, by rfl⟩ : syracuseStep 1249819 = 1874729) B1874729
theorem B5337647 : Blo 1248442 5337647 := bstep (se 1 (by rfl) ⟨4003235, by rfl⟩ : syracuseStep 5337647 = 8006471) B8006471
theorem B4215401 : Blo 1248442 4215401 := bstep (se 2 (by rfl) ⟨1580775, by rfl⟩ : syracuseStep 4215401 = 3161551) B3161551
theorem B1249959 : Blo 1248442 1249959 := bstep (se 1 (by rfl) ⟨937469, by rfl⟩ : syracuseStep 1249959 = 1874939) B1874939
theorem B1249983 : Blo 1248442 1249983 := bstep (se 1 (by rfl) ⟨937487, by rfl⟩ : syracuseStep 1249983 = 1874975) B1874975
theorem B1249999 : Blo 1248442 1249999 := bstep (se 1 (by rfl) ⟨937499, by rfl⟩ : syracuseStep 1249999 = 1874999) B1874999
theorem B4215563 : Blo 1248442 4215563 := bstep (se 1 (by rfl) ⟨3161672, by rfl⟩ : syracuseStep 4215563 = 6323345) B6323345
theorem B1250079 : Blo 1248442 1250079 := bstep (se 1 (by rfl) ⟨937559, by rfl⟩ : syracuseStep 1250079 = 1875119) B1875119
theorem B2847545 : Blo 1248442 2847545 := bstep (se 2 (by rfl) ⟨1067829, by rfl⟩ : syracuseStep 2847545 = 2135659) B2135659
theorem B1250175 : Blo 1248442 1250175 := bstep (se 1 (by rfl) ⟨937631, by rfl⟩ : syracuseStep 1250175 = 1875263) B1875263
theorem B1250271 : Blo 1248442 1250271 := bstep (se 1 (by rfl) ⟨937703, by rfl⟩ : syracuseStep 1250271 = 1875407) B1875407
theorem B1266779 : Blo 1248442 1266779 := bstep (se 1 (by rfl) ⟨950084, by rfl⟩ : syracuseStep 1266779 = 1900169) B1900169
theorem B1873055 : Blo 1248442 1873055 := bstep (se 1 (by rfl) ⟨1404791, by rfl⟩ : syracuseStep 1873055 = 2809583) B2809583
theorem B27366599 : Blo 1248442 27366599 := bstep (se 1 (by rfl) ⟨20524949, by rfl⟩ : syracuseStep 27366599 = 41049899) B41049899
theorem B5338331 : Blo 1248442 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B2667833 : Blo 1248442 2667833 := bstep (se 2 (by rfl) ⟨1000437, by rfl⟩ : syracuseStep 2667833 = 2000875) B2000875
theorem B1406335 : Blo 1248442 1406335 := bstep (se 1 (by rfl) ⟨1054751, by rfl⟩ : syracuseStep 1406335 = 2109503) B2109503
theorem B9008663 : Blo 1248442 9008663 := bstep (se 1 (by rfl) ⟨6756497, by rfl⟩ : syracuseStep 9008663 = 13512995) B13512995
theorem B9483803 : Blo 1248442 9483803 := bstep (se 1 (by rfl) ⟨7112852, by rfl⟩ : syracuseStep 9483803 = 14225705) B14225705
theorem B4216427 : Blo 1248442 4216427 := bstep (se 1 (by rfl) ⟨3162320, by rfl⟩ : syracuseStep 4216427 = 6324641) B6324641
theorem B24344171 : Blo 1248442 24344171 := bstep (se 1 (by rfl) ⟨18258128, by rfl⟩ : syracuseStep 24344171 = 36516257) B36516257
theorem B14227163 : Blo 1248442 14227163 := bstep (se 1 (by rfl) ⟨10670372, by rfl⟩ : syracuseStep 14227163 = 21340745) B21340745
theorem B1873673 : Blo 1248442 1873673 := bstep (se 2 (by rfl) ⟨702627, by rfl⟩ : syracuseStep 1873673 = 1405255) B1405255
theorem B4216859 : Blo 1248442 4216859 := bstep (se 1 (by rfl) ⟨3162644, by rfl⟩ : syracuseStep 4216859 = 6325289) B6325289
theorem B1874297 : Blo 1248442 1874297 := bstep (se 2 (by rfl) ⟨702861, by rfl⟩ : syracuseStep 1874297 = 1405723) B1405723
theorem B9624253 : Blo 1248442 9624253 := bstep (se 3 (by rfl) ⟨1804547, by rfl⟩ : syracuseStep 9624253 = 3609095) B3609095
theorem B4217723 : Blo 1248442 4217723 := bstep (se 1 (by rfl) ⟨3163292, by rfl⟩ : syracuseStep 4217723 = 6326585) B6326585
theorem B1874825 : Blo 1248442 1874825 := bstep (se 2 (by rfl) ⟨703059, by rfl⟩ : syracuseStep 1874825 = 1406119) B1406119
theorem B2809115 : Blo 1248442 2809115 := bstep (se 1 (by rfl) ⟨2106836, by rfl⟩ : syracuseStep 2809115 = 4213673) B4213673
theorem B4218155 : Blo 1248442 4218155 := bstep (se 1 (by rfl) ⟨3163616, by rfl⟩ : syracuseStep 4218155 = 6327233) B6327233
theorem B2809151 : Blo 1248442 2809151 := bstep (se 1 (by rfl) ⟨2106863, by rfl⟩ : syracuseStep 2809151 = 4213727) B4213727
theorem B1875359 : Blo 1248442 1875359 := bstep (se 1 (by rfl) ⟨1406519, by rfl⟩ : syracuseStep 1875359 = 2813039) B2813039
theorem B2809313 : Blo 1248442 2809313 := bstep (se 2 (by rfl) ⟨1053492, by rfl⟩ : syracuseStep 2809313 = 2106985) B2106985
theorem B1875503 : Blo 1248442 1875503 := bstep (se 1 (by rfl) ⟨1406627, by rfl⟩ : syracuseStep 1875503 = 2813255) B2813255
theorem B4218479 : Blo 1248442 4218479 := bstep (se 1 (by rfl) ⟨3163859, by rfl⟩ : syracuseStep 4218479 = 6327719) B6327719
theorem B7110301 : Blo 1248442 7110301 := bstep (se 3 (by rfl) ⟨1333181, by rfl⟩ : syracuseStep 7110301 = 2666363) B2666363
theorem B5341049 : Blo 1248442 5341049 := bstep (se 2 (by rfl) ⟨2002893, by rfl⟩ : syracuseStep 5341049 = 4005787) B4005787
theorem B2810105 : Blo 1248442 2810105 := bstep (se 2 (by rfl) ⟨1053789, by rfl⟩ : syracuseStep 2810105 = 2107579) B2107579
theorem B1581383 : Blo 1248442 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B3375481 : Blo 1248442 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B2810267 : Blo 1248442 2810267 := bstep (se 1 (by rfl) ⟨2107700, by rfl⟩ : syracuseStep 2810267 = 4215401) B4215401
theorem B2810375 : Blo 1248442 2810375 := bstep (se 1 (by rfl) ⟨2107781, by rfl⟩ : syracuseStep 2810375 = 4215563) B4215563
theorem B18244399 : Blo 1248442 18244399 := bstep (se 1 (by rfl) ⟨13683299, by rfl⟩ : syracuseStep 18244399 = 27366599) B27366599
theorem B1778555 : Blo 1248442 1778555 := bstep (se 1 (by rfl) ⟨1333916, by rfl⟩ : syracuseStep 1778555 = 2667833) B2667833
theorem B3376001 : Blo 1248442 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B2810951 : Blo 1248442 2810951 := bstep (se 1 (by rfl) ⟨2108213, by rfl⟩ : syracuseStep 2810951 = 4216427) B4216427
theorem B16229447 : Blo 1248442 16229447 := bstep (se 1 (by rfl) ⟨12172085, by rfl⟩ : syracuseStep 16229447 = 24344171) B24344171
theorem B14238827 : Blo 1248442 14238827 := bstep (se 1 (by rfl) ⟨10679120, by rfl⟩ : syracuseStep 14238827 = 21358241) B21358241
theorem B2811041 : Blo 1248442 2811041 := bstep (se 2 (by rfl) ⟨1054140, by rfl⟩ : syracuseStep 2811041 = 2108281) B2108281
theorem B2811239 : Blo 1248442 2811239 := bstep (se 1 (by rfl) ⟨2108429, by rfl⟩ : syracuseStep 2811239 = 4216859) B4216859
theorem B3163495 : Blo 1248442 3163495 := bstep (se 1 (by rfl) ⟨2372621, by rfl⟩ : syracuseStep 3163495 = 4745243) B4745243
theorem B2811815 : Blo 1248442 2811815 := bstep (se 1 (by rfl) ⟨2108861, by rfl⟩ : syracuseStep 2811815 = 4217723) B4217723
theorem B13502447 : Blo 1248442 13502447 := bstep (se 1 (by rfl) ⟨10126835, by rfl⟩ : syracuseStep 13502447 = 20253671) B20253671
theorem B360392813 : Blo 1248442 360392813 := bstep (se 3 (by rfl) ⟨67573652, by rfl⟩ : syracuseStep 360392813 = 135147305) B135147305
theorem B2812103 : Blo 1248442 2812103 := bstep (se 1 (by rfl) ⟨2109077, by rfl⟩ : syracuseStep 2812103 = 4218155) B4218155
theorem B9480401 : Blo 1248442 9480401 := bstep (se 2 (by rfl) ⟨3555150, by rfl⟩ : syracuseStep 9480401 = 7110301) B7110301
theorem B10127713 : Blo 1248442 10127713 := bstep (se 2 (by rfl) ⟨3797892, by rfl⟩ : syracuseStep 10127713 = 7595785) B7595785
theorem B2812319 : Blo 1248442 2812319 := bstep (se 1 (by rfl) ⟨2109239, by rfl⟩ : syracuseStep 2812319 = 4218479) B4218479
theorem B3205673 : Blo 1248442 3205673 := bstep (se 2 (by rfl) ⟨1202127, by rfl⟩ : syracuseStep 3205673 = 2404255) B2404255
theorem B2566891 : Blo 1248442 2566891 := bstep (se 1 (by rfl) ⟨1925168, by rfl⟩ : syracuseStep 2566891 = 3850337) B3850337
theorem B2370313 : Blo 1248442 2370313 := bstep (se 2 (by rfl) ⟨888867, by rfl⟩ : syracuseStep 2370313 = 1777735) B1777735
theorem B12995471 : Blo 1248442 12995471 := bstep (se 1 (by rfl) ⟨9746603, by rfl⟩ : syracuseStep 12995471 = 19493207) B19493207
theorem B3378077 : Blo 1248442 3378077 := bstep (se 3 (by rfl) ⟨633389, by rfl⟩ : syracuseStep 3378077 = 1266779) B1266779
theorem B4746185 : Blo 1248442 4746185 := bstep (se 2 (by rfl) ⟨1779819, by rfl⟩ : syracuseStep 4746185 = 3559639) B3559639
theorem B4746215 : Blo 1248442 4746215 := bstep (se 1 (by rfl) ⟨3559661, by rfl⟩ : syracuseStep 4746215 = 7119323) B7119323
theorem B3558431 : Blo 1248442 3558431 := bstep (se 1 (by rfl) ⟨2668823, by rfl⟩ : syracuseStep 3558431 = 5337647) B5337647
theorem B30403673 : Blo 1248442 30403673 := bstep (se 2 (by rfl) ⟨11401377, by rfl⟩ : syracuseStep 30403673 = 22802755) B22802755
theorem B2108713 : Blo 1248442 2108713 := bstep (se 2 (by rfl) ⟨790767, by rfl⟩ : syracuseStep 2108713 = 1581535) B1581535
theorem B1248703 : Blo 1248442 1248703 := bstep (se 1 (by rfl) ⟨936527, by rfl⟩ : syracuseStep 1248703 = 1873055) B1873055
theorem B3558887 : Blo 1248442 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B12832337 : Blo 1248442 12832337 := bstep (se 2 (by rfl) ⟨4812126, by rfl⟩ : syracuseStep 12832337 = 9624253) B9624253
theorem B205254323 : Blo 1248442 205254323 := bstep (se 1 (by rfl) ⟨153940742, by rfl⟩ : syracuseStep 205254323 = 307881485) B307881485
theorem B1249115 : Blo 1248442 1249115 := bstep (se 1 (by rfl) ⟨936836, by rfl⟩ : syracuseStep 1249115 = 1873673) B1873673
theorem B24023101 : Blo 1248442 24023101 := bstep (se 3 (by rfl) ⟨4504331, by rfl⟩ : syracuseStep 24023101 = 9008663) B9008663
theorem B2109577 : Blo 1248442 2109577 := bstep (se 2 (by rfl) ⟨791091, by rfl⟩ : syracuseStep 2109577 = 1582183) B1582183
theorem B2109631 : Blo 1248442 2109631 := bstep (se 1 (by rfl) ⟨1582223, by rfl⟩ : syracuseStep 2109631 = 3164447) B3164447
theorem B1249531 : Blo 1248442 1249531 := bstep (se 1 (by rfl) ⟨937148, by rfl⟩ : syracuseStep 1249531 = 1874297) B1874297
theorem B7115201 : Blo 1248442 7115201 := bstep (se 2 (by rfl) ⟨2668200, by rfl⟩ : syracuseStep 7115201 = 5336401) B5336401
theorem B1249883 : Blo 1248442 1249883 := bstep (se 1 (by rfl) ⟨937412, by rfl⟩ : syracuseStep 1249883 = 1874825) B1874825
theorem B2110063 : Blo 1248442 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B6320915 : Blo 1248442 6320915 := bstep (se 1 (by rfl) ⟨4740686, by rfl⟩ : syracuseStep 6320915 = 9481373) B9481373
theorem B1872743 : Blo 1248442 1872743 := bstep (se 1 (by rfl) ⟨1404557, by rfl⟩ : syracuseStep 1872743 = 2809115) B2809115
theorem B1872767 : Blo 1248442 1872767 := bstep (se 1 (by rfl) ⟨1404575, by rfl⟩ : syracuseStep 1872767 = 2809151) B2809151
theorem B32043923 : Blo 1248442 32043923 := bstep (se 1 (by rfl) ⟨24032942, by rfl⟩ : syracuseStep 32043923 = 48065885) B48065885
theorem B1250239 : Blo 1248442 1250239 := bstep (se 1 (by rfl) ⟨937679, by rfl⟩ : syracuseStep 1250239 = 1875359) B1875359
theorem B1872875 : Blo 1248442 1872875 := bstep (se 1 (by rfl) ⟨1404656, by rfl⟩ : syracuseStep 1872875 = 2809313) B2809313
theorem B1250335 : Blo 1248442 1250335 := bstep (se 1 (by rfl) ⟨937751, by rfl⟩ : syracuseStep 1250335 = 1875503) B1875503
theorem B3560699 : Blo 1248442 3560699 := bstep (se 1 (by rfl) ⟨2670524, by rfl⟩ : syracuseStep 3560699 = 5341049) B5341049
theorem B1873577 : Blo 1248442 1873577 := bstep (se 2 (by rfl) ⟨702591, by rfl⟩ : syracuseStep 1873577 = 1405183) B1405183
theorem B1898363 : Blo 1248442 1898363 := bstep (se 1 (by rfl) ⟨1423772, by rfl⟩ : syracuseStep 1898363 = 2847545) B2847545
theorem B6330311 : Blo 1248442 6330311 := bstep (se 1 (by rfl) ⟨4747733, by rfl⟩ : syracuseStep 6330311 = 9495467) B9495467
theorem B1873991 : Blo 1248442 1873991 := bstep (se 1 (by rfl) ⟨1405493, by rfl⟩ : syracuseStep 1873991 = 2810987) B2810987
theorem B4217183 : Blo 1248442 4217183 := bstep (se 1 (by rfl) ⟨3162887, by rfl⟩ : syracuseStep 4217183 = 6325775) B6325775
theorem B6322535 : Blo 1248442 6322535 := bstep (se 1 (by rfl) ⟨4741901, by rfl⟩ : syracuseStep 6322535 = 9483803) B9483803
theorem B1874375 : Blo 1248442 1874375 := bstep (se 1 (by rfl) ⟨1405781, by rfl⟩ : syracuseStep 1874375 = 2811563) B2811563
theorem B9484775 : Blo 1248442 9484775 := bstep (se 1 (by rfl) ⟨7113581, by rfl⟩ : syracuseStep 9484775 = 14227163) B14227163
theorem B1874855 : Blo 1248442 1874855 := bstep (se 1 (by rfl) ⟨1406141, by rfl⟩ : syracuseStep 1874855 = 2812283) B2812283
theorem B1874927 : Blo 1248442 1874927 := bstep (se 1 (by rfl) ⟨1406195, by rfl⟩ : syracuseStep 1874927 = 2812391) B2812391
theorem B12000251 : Blo 1248442 12000251 := bstep (se 1 (by rfl) ⟨9000188, by rfl⟩ : syracuseStep 12000251 = 18000377) B18000377
theorem B108059669 : Blo 1248442 108059669 := bstep (se 6 (by rfl) ⟨2532648, by rfl⟩ : syracuseStep 108059669 = 5065297) B5065297
theorem B1875113 : Blo 1248442 1875113 := bstep (se 2 (by rfl) ⟨703167, by rfl⟩ : syracuseStep 1875113 = 1406335) B1406335
theorem B2809043 : Blo 1248442 2809043 := bstep (se 1 (by rfl) ⟨2106782, by rfl⟩ : syracuseStep 2809043 = 4213565) B4213565
theorem B1875527 : Blo 1248442 1875527 := bstep (se 1 (by rfl) ⟨1406645, by rfl⟩ : syracuseStep 1875527 = 2813291) B2813291
theorem B1580735 : Blo 1248442 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B2809799 : Blo 1248442 2809799 := bstep (se 1 (by rfl) ⟨2107349, by rfl⟩ : syracuseStep 2809799 = 4214699) B4214699
theorem B32030801 : Blo 1248442 32030801 := bstep (se 2 (by rfl) ⟨12011550, by rfl⟩ : syracuseStep 32030801 = 24023101) B24023101
theorem B4743467 : Blo 1248442 4743467 := bstep (se 1 (by rfl) ⟨3557600, by rfl⟩ : syracuseStep 4743467 = 7115201) B7115201
theorem B4220207 : Blo 1248442 4220207 := bstep (se 1 (by rfl) ⟨3165155, by rfl⟩ : syracuseStep 4220207 = 6330311) B6330311
theorem B2811455 : Blo 1248442 2811455 := bstep (se 1 (by rfl) ⟨2108591, by rfl⟩ : syracuseStep 2811455 = 4217183) B4217183
theorem B2811617 : Blo 1248442 2811617 := bstep (se 2 (by rfl) ⟨1054356, by rfl⟩ : syracuseStep 2811617 = 2108713) B2108713
theorem B3164123 : Blo 1248442 3164123 := bstep (se 1 (by rfl) ⟨2373092, by rfl⟩ : syracuseStep 3164123 = 4746185) B4746185
theorem B3164143 : Blo 1248442 3164143 := bstep (se 1 (by rfl) ⟨2373107, by rfl⟩ : syracuseStep 3164143 = 4746215) B4746215
theorem B20269115 : Blo 1248442 20269115 := bstep (se 1 (by rfl) ⟨15201836, by rfl⟩ : syracuseStep 20269115 = 30403673) B30403673
theorem B8554891 : Blo 1248442 8554891 := bstep (se 1 (by rfl) ⟨6416168, by rfl⟩ : syracuseStep 8554891 = 12832337) B12832337
theorem B9489149 : Blo 1248442 9489149 := bstep (se 3 (by rfl) ⟨1779215, by rfl⟩ : syracuseStep 9489149 = 3558431) B3558431
theorem B2812769 : Blo 1248442 2812769 := bstep (se 2 (by rfl) ⟨1054788, by rfl⟩ : syracuseStep 2812769 = 2109577) B2109577
theorem B2812841 : Blo 1248442 2812841 := bstep (se 2 (by rfl) ⟨1054815, by rfl⟩ : syracuseStep 2812841 = 2109631) B2109631
theorem B13503617 : Blo 1248442 13503617 := bstep (se 2 (by rfl) ⟨5063856, by rfl⟩ : syracuseStep 13503617 = 10127713) B10127713
theorem B4500641 : Blo 1248442 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B4213943 : Blo 1248442 4213943 := bstep (se 1 (by rfl) ⟨3160457, by rfl⟩ : syracuseStep 4213943 = 6320915) B6320915
theorem B1248495 : Blo 1248442 1248495 := bstep (se 1 (by rfl) ⟨936371, by rfl⟩ : syracuseStep 1248495 = 1872743) B1872743
theorem B1248511 : Blo 1248442 1248511 := bstep (se 1 (by rfl) ⟨936383, by rfl⟩ : syracuseStep 1248511 = 1872767) B1872767
theorem B1248583 : Blo 1248442 1248583 := bstep (se 1 (by rfl) ⟨936437, by rfl⟩ : syracuseStep 1248583 = 1872875) B1872875
theorem B2813417 : Blo 1248442 2813417 := bstep (se 2 (by rfl) ⟨1055031, by rfl⟩ : syracuseStep 2813417 = 2110063) B2110063
theorem B24325865 : Blo 1248442 24325865 := bstep (se 2 (by rfl) ⟨9122199, by rfl⟩ : syracuseStep 24325865 = 18244399) B18244399
theorem B1249051 : Blo 1248442 1249051 := bstep (se 1 (by rfl) ⟨936788, by rfl⟩ : syracuseStep 1249051 = 1873577) B1873577
theorem B1265575 : Blo 1248442 1265575 := bstep (se 1 (by rfl) ⟨949181, by rfl⟩ : syracuseStep 1265575 = 1898363) B1898363
theorem B1249327 : Blo 1248442 1249327 := bstep (se 1 (by rfl) ⟨936995, by rfl⟩ : syracuseStep 1249327 = 1873991) B1873991
theorem B6320267 : Blo 1248442 6320267 := bstep (se 1 (by rfl) ⟨4740200, by rfl⟩ : syracuseStep 6320267 = 9480401) B9480401
theorem B4215023 : Blo 1248442 4215023 := bstep (se 1 (by rfl) ⟨3161267, by rfl⟩ : syracuseStep 4215023 = 6322535) B6322535
theorem B1249583 : Blo 1248442 1249583 := bstep (se 1 (by rfl) ⟨937187, by rfl⟩ : syracuseStep 1249583 = 1874375) B1874375
theorem B4215293 : Blo 1248442 4215293 := bstep (se 3 (by rfl) ⟨790367, by rfl⟩ : syracuseStep 4215293 = 1580735) B1580735
theorem B8663647 : Blo 1248442 8663647 := bstep (se 1 (by rfl) ⟨6497735, by rfl⟩ : syracuseStep 8663647 = 12995471) B12995471
theorem B1249903 : Blo 1248442 1249903 := bstep (se 1 (by rfl) ⟨937427, by rfl⟩ : syracuseStep 1249903 = 1874855) B1874855
theorem B1249951 : Blo 1248442 1249951 := bstep (se 1 (by rfl) ⟨937463, by rfl⟩ : syracuseStep 1249951 = 1874927) B1874927
theorem B8000167 : Blo 1248442 8000167 := bstep (se 1 (by rfl) ⟨6000125, by rfl⟩ : syracuseStep 8000167 = 12000251) B12000251
theorem B1250075 : Blo 1248442 1250075 := bstep (se 1 (by rfl) ⟨937556, by rfl⟩ : syracuseStep 1250075 = 1875113) B1875113
theorem B1872695 : Blo 1248442 1872695 := bstep (se 1 (by rfl) ⟨1404521, by rfl⟩ : syracuseStep 1872695 = 2809043) B2809043
theorem B2372591 : Blo 1248442 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B1250351 : Blo 1248442 1250351 := bstep (se 1 (by rfl) ⟨937763, by rfl⟩ : syracuseStep 1250351 = 1875527) B1875527
theorem B136836215 : Blo 1248442 136836215 := bstep (se 1 (by rfl) ⟨102627161, by rfl⟩ : syracuseStep 136836215 = 205254323) B205254323
theorem B1873199 : Blo 1248442 1873199 := bstep (se 1 (by rfl) ⟨1404899, by rfl⟩ : syracuseStep 1873199 = 2809799) B2809799
theorem B1873403 : Blo 1248442 1873403 := bstep (se 1 (by rfl) ⟨1405052, by rfl⟩ : syracuseStep 1873403 = 2810105) B2810105
theorem B1873511 : Blo 1248442 1873511 := bstep (se 1 (by rfl) ⟨1405133, by rfl⟩ : syracuseStep 1873511 = 2810267) B2810267
theorem B1873583 : Blo 1248442 1873583 := bstep (se 1 (by rfl) ⟨1405187, by rfl⟩ : syracuseStep 1873583 = 2810375) B2810375
theorem B2250667 : Blo 1248442 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B21362615 : Blo 1248442 21362615 := bstep (se 1 (by rfl) ⟨16021961, by rfl⟩ : syracuseStep 21362615 = 32043923) B32043923
theorem B1873967 : Blo 1248442 1873967 := bstep (se 1 (by rfl) ⟨1405475, by rfl⟩ : syracuseStep 1873967 = 2810951) B2810951
theorem B10819631 : Blo 1248442 10819631 := bstep (se 1 (by rfl) ⟨8114723, by rfl⟩ : syracuseStep 10819631 = 16229447) B16229447
theorem B9492551 : Blo 1248442 9492551 := bstep (se 1 (by rfl) ⟨7119413, by rfl⟩ : syracuseStep 9492551 = 14238827) B14238827
theorem B1874027 : Blo 1248442 1874027 := bstep (se 1 (by rfl) ⟨1405520, by rfl⟩ : syracuseStep 1874027 = 2811041) B2811041
theorem B2373799 : Blo 1248442 2373799 := bstep (se 1 (by rfl) ⟨1780349, by rfl⟩ : syracuseStep 2373799 = 3560699) B3560699
theorem B4217021 : Blo 1248442 4217021 := bstep (se 3 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 4217021 = 1581383) B1581383
theorem B1874159 : Blo 1248442 1874159 := bstep (se 1 (by rfl) ⟨1405619, by rfl⟩ : syracuseStep 1874159 = 2811239) B2811239
theorem B3422521 : Blo 1248442 3422521 := bstep (se 2 (by rfl) ⟨1283445, by rfl⟩ : syracuseStep 3422521 = 2566891) B2566891
theorem B3160417 : Blo 1248442 3160417 := bstep (se 2 (by rfl) ⟨1185156, by rfl⟩ : syracuseStep 3160417 = 2370313) B2370313
theorem B1874543 : Blo 1248442 1874543 := bstep (se 1 (by rfl) ⟨1405907, by rfl⟩ : syracuseStep 1874543 = 2811815) B2811815
theorem B9001631 : Blo 1248442 9001631 := bstep (se 1 (by rfl) ⟨6751223, by rfl⟩ : syracuseStep 9001631 = 13502447) B13502447
theorem B240261875 : Blo 1248442 240261875 := bstep (se 1 (by rfl) ⟨180196406, by rfl⟩ : syracuseStep 240261875 = 360392813) B360392813
theorem B1874735 : Blo 1248442 1874735 := bstep (se 1 (by rfl) ⟨1406051, by rfl⟩ : syracuseStep 1874735 = 2812103) B2812103
theorem B1874879 : Blo 1248442 1874879 := bstep (se 1 (by rfl) ⟨1406159, by rfl⟩ : syracuseStep 1874879 = 2812319) B2812319
theorem B6323183 : Blo 1248442 6323183 := bstep (se 1 (by rfl) ⟨4742387, by rfl⟩ : syracuseStep 6323183 = 9484775) B9484775
theorem B2137115 : Blo 1248442 2137115 := bstep (se 1 (by rfl) ⟨1602836, by rfl⟩ : syracuseStep 2137115 = 3205673) B3205673
theorem B4217993 : Blo 1248442 4217993 := bstep (se 2 (by rfl) ⟨1581747, by rfl⟩ : syracuseStep 4217993 = 3163495) B3163495
theorem B2252051 : Blo 1248442 2252051 := bstep (se 1 (by rfl) ⟨1689038, by rfl⟩ : syracuseStep 2252051 = 3378077) B3378077
theorem B72039779 : Blo 1248442 72039779 := bstep (se 1 (by rfl) ⟨54029834, by rfl⟩ : syracuseStep 72039779 = 108059669) B108059669
theorem B4742813 : Blo 1248442 4742813 := bstep (se 3 (by rfl) ⟨889277, by rfl⟩ : syracuseStep 4742813 = 1778555) B1778555
theorem B2810015 : Blo 1248442 2810015 := bstep (se 1 (by rfl) ⟨2107511, by rfl⟩ : syracuseStep 2810015 = 4215023) B4215023
theorem B3162311 : Blo 1248442 3162311 := bstep (se 1 (by rfl) ⟨2371733, by rfl⟩ : syracuseStep 3162311 = 4743467) B4743467
theorem B2810195 : Blo 1248442 2810195 := bstep (se 1 (by rfl) ⟨2107646, by rfl⟩ : syracuseStep 2810195 = 4215293) B4215293
theorem B4563361 : Blo 1248442 4563361 := bstep (se 2 (by rfl) ⟨1711260, by rfl⟩ : syracuseStep 4563361 = 3422521) B3422521
theorem B12001709 : Blo 1248442 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B11551529 : Blo 1248442 11551529 := bstep (se 2 (by rfl) ⟨4331823, by rfl⟩ : syracuseStep 11551529 = 8663647) B8663647
theorem B10666889 : Blo 1248442 10666889 := bstep (se 2 (by rfl) ⟨4000083, by rfl⟩ : syracuseStep 10666889 = 8000167) B8000167
theorem B2811347 : Blo 1248442 2811347 := bstep (se 1 (by rfl) ⟨2108510, by rfl⟩ : syracuseStep 2811347 = 4217021) B4217021
theorem B6326099 : Blo 1248442 6326099 := bstep (se 1 (by rfl) ⟨4744574, by rfl⟩ : syracuseStep 6326099 = 9489149) B9489149
theorem B2811995 : Blo 1248442 2811995 := bstep (se 1 (by rfl) ⟨2108996, by rfl⟩ : syracuseStep 2811995 = 4217993) B4217993
theorem B1501367 : Blo 1248442 1501367 := bstep (se 1 (by rfl) ⟨1126025, by rfl⟩ : syracuseStep 1501367 = 2252051) B2252051
theorem B3000889 : Blo 1248442 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B6326909 : Blo 1248442 6326909 := bstep (se 3 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 6326909 = 2372591) B2372591
theorem B4213511 : Blo 1248442 4213511 := bstep (se 1 (by rfl) ⟨3160133, by rfl⟩ : syracuseStep 4213511 = 6320267) B6320267
theorem B3165065 : Blo 1248442 3165065 := bstep (se 2 (by rfl) ⟨1186899, by rfl⟩ : syracuseStep 3165065 = 2373799) B2373799
theorem B4213889 : Blo 1248442 4213889 := bstep (se 2 (by rfl) ⟨1580208, by rfl⟩ : syracuseStep 4213889 = 3160417) B3160417
theorem B11406521 : Blo 1248442 11406521 := bstep (se 2 (by rfl) ⟨4277445, by rfl⟩ : syracuseStep 11406521 = 8554891) B8554891
theorem B1248463 : Blo 1248442 1248463 := bstep (se 1 (by rfl) ⟨936347, by rfl⟩ : syracuseStep 1248463 = 1872695) B1872695
theorem B1248799 : Blo 1248442 1248799 := bstep (se 1 (by rfl) ⟨936599, by rfl⟩ : syracuseStep 1248799 = 1873199) B1873199
theorem B2813471 : Blo 1248442 2813471 := bstep (se 1 (by rfl) ⟨2110103, by rfl⟩ : syracuseStep 2813471 = 4220207) B4220207
theorem B1248935 : Blo 1248442 1248935 := bstep (se 1 (by rfl) ⟨936701, by rfl⟩ : syracuseStep 1248935 = 1873403) B1873403
theorem B1249007 : Blo 1248442 1249007 := bstep (se 1 (by rfl) ⟨936755, by rfl⟩ : syracuseStep 1249007 = 1873511) B1873511
theorem B1249055 : Blo 1248442 1249055 := bstep (se 1 (by rfl) ⟨936791, by rfl⟩ : syracuseStep 1249055 = 1873583) B1873583
theorem B14241743 : Blo 1248442 14241743 := bstep (se 1 (by rfl) ⟨10681307, by rfl⟩ : syracuseStep 14241743 = 21362615) B21362615
theorem B2109415 : Blo 1248442 2109415 := bstep (se 1 (by rfl) ⟨1582061, by rfl⟩ : syracuseStep 2109415 = 3164123) B3164123
theorem B1249311 : Blo 1248442 1249311 := bstep (se 1 (by rfl) ⟨936983, by rfl⟩ : syracuseStep 1249311 = 1873967) B1873967
theorem B7213087 : Blo 1248442 7213087 := bstep (se 1 (by rfl) ⟨5409815, by rfl⟩ : syracuseStep 7213087 = 10819631) B10819631
theorem B13512743 : Blo 1248442 13512743 := bstep (se 1 (by rfl) ⟨10134557, by rfl⟩ : syracuseStep 13512743 = 20269115) B20269115
theorem B6328367 : Blo 1248442 6328367 := bstep (se 1 (by rfl) ⟨4746275, by rfl⟩ : syracuseStep 6328367 = 9492551) B9492551
theorem B1249351 : Blo 1248442 1249351 := bstep (se 1 (by rfl) ⟨937013, by rfl⟩ : syracuseStep 1249351 = 1874027) B1874027
theorem B1249439 : Blo 1248442 1249439 := bstep (se 1 (by rfl) ⟨937079, by rfl⟩ : syracuseStep 1249439 = 1874159) B1874159
theorem B1249695 : Blo 1248442 1249695 := bstep (se 1 (by rfl) ⟨937271, by rfl⟩ : syracuseStep 1249695 = 1874543) B1874543
theorem B6001087 : Blo 1248442 6001087 := bstep (se 1 (by rfl) ⟨4500815, by rfl⟩ : syracuseStep 6001087 = 9001631) B9001631
theorem B160174583 : Blo 1248442 160174583 := bstep (se 1 (by rfl) ⟨120130937, by rfl⟩ : syracuseStep 160174583 = 240261875) B240261875
theorem B1249823 : Blo 1248442 1249823 := bstep (se 1 (by rfl) ⟨937367, by rfl⟩ : syracuseStep 1249823 = 1874735) B1874735
theorem B1249919 : Blo 1248442 1249919 := bstep (se 1 (by rfl) ⟨937439, by rfl⟩ : syracuseStep 1249919 = 1874879) B1874879
theorem B4215455 : Blo 1248442 4215455 := bstep (se 1 (by rfl) ⟨3161591, by rfl⟩ : syracuseStep 4215455 = 6323183) B6323183
theorem B48026519 : Blo 1248442 48026519 := bstep (se 1 (by rfl) ⟨36019889, by rfl⟩ : syracuseStep 48026519 = 72039779) B72039779
theorem B16217243 : Blo 1248442 16217243 := bstep (se 1 (by rfl) ⟨12162932, by rfl⟩ : syracuseStep 16217243 = 24325865) B24325865
theorem B21353867 : Blo 1248442 21353867 := bstep (se 1 (by rfl) ⟨16015400, by rfl⟩ : syracuseStep 21353867 = 32030801) B32030801
theorem B5698973 : Blo 1248442 5698973 := bstep (se 3 (by rfl) ⟨1068557, by rfl⟩ : syracuseStep 5698973 = 2137115) B2137115
theorem B91224143 : Blo 1248442 91224143 := bstep (se 1 (by rfl) ⟨68418107, by rfl⟩ : syracuseStep 91224143 = 136836215) B136836215
theorem B1874303 : Blo 1248442 1874303 := bstep (se 1 (by rfl) ⟨1405727, by rfl⟩ : syracuseStep 1874303 = 2811455) B2811455
theorem B1874411 : Blo 1248442 1874411 := bstep (se 1 (by rfl) ⟨1405808, by rfl⟩ : syracuseStep 1874411 = 2811617) B2811617
theorem B1875179 : Blo 1248442 1875179 := bstep (se 1 (by rfl) ⟨1406384, by rfl⟩ : syracuseStep 1875179 = 2812769) B2812769
theorem B1875227 : Blo 1248442 1875227 := bstep (se 1 (by rfl) ⟨1406420, by rfl⟩ : syracuseStep 1875227 = 2812841) B2812841
theorem B9002411 : Blo 1248442 9002411 := bstep (se 1 (by rfl) ⟨6751808, by rfl⟩ : syracuseStep 9002411 = 13503617) B13503617
theorem B2809295 : Blo 1248442 2809295 := bstep (se 1 (by rfl) ⟨2106971, by rfl⟩ : syracuseStep 2809295 = 4213943) B4213943
theorem B1875611 : Blo 1248442 1875611 := bstep (se 1 (by rfl) ⟨1406708, by rfl⟩ : syracuseStep 1875611 = 2813417) B2813417
theorem B3161875 : Blo 1248442 3161875 := bstep (se 1 (by rfl) ⟨2371406, by rfl⟩ : syracuseStep 3161875 = 4742813) B4742813
theorem B1687433 : Blo 1248442 1687433 := bstep (se 2 (by rfl) ⟨632787, by rfl⟩ : syracuseStep 1687433 = 1265575) B1265575
theorem B4218857 : Blo 1248442 4218857 := bstep (se 2 (by rfl) ⟨1582071, by rfl⟩ : syracuseStep 4218857 = 3164143) B3164143
theorem B4218911 : Blo 1248442 4218911 := bstep (se 1 (by rfl) ⟨3164183, by rfl⟩ : syracuseStep 4218911 = 6328367) B6328367
theorem B9617449 : Blo 1248442 9617449 := bstep (se 2 (by rfl) ⟨3606543, by rfl⟩ : syracuseStep 9617449 = 7213087) B7213087
theorem B106783055 : Blo 1248442 106783055 := bstep (se 1 (by rfl) ⟨80087291, by rfl⟩ : syracuseStep 106783055 = 160174583) B160174583
theorem B2810303 : Blo 1248442 2810303 := bstep (se 1 (by rfl) ⟨2107727, by rfl⟩ : syracuseStep 2810303 = 4215455) B4215455
theorem B30417389 : Blo 1248442 30417389 := bstep (se 3 (by rfl) ⟨5703260, by rfl⟩ : syracuseStep 30417389 = 11406521) B11406521
theorem B7111259 : Blo 1248442 7111259 := bstep (se 1 (by rfl) ⟨5333444, by rfl⟩ : syracuseStep 7111259 = 10666889) B10666889
theorem B30804077 : Blo 1248442 30804077 := bstep (se 3 (by rfl) ⟨5775764, by rfl⟩ : syracuseStep 30804077 = 11551529) B11551529
theorem B4499821 : Blo 1248442 4499821 := bstep (se 3 (by rfl) ⟨843716, by rfl⟩ : syracuseStep 4499821 = 1687433) B1687433
theorem B2812553 : Blo 1248442 2812553 := bstep (se 2 (by rfl) ⟨1054707, by rfl⟩ : syracuseStep 2812553 = 2109415) B2109415
theorem B2812571 : Blo 1248442 2812571 := bstep (se 1 (by rfl) ⟨2109428, by rfl⟩ : syracuseStep 2812571 = 4218857) B4218857
theorem B2108207 : Blo 1248442 2108207 := bstep (se 1 (by rfl) ⟨1581155, by rfl⟩ : syracuseStep 2108207 = 3162311) B3162311
theorem B32017679 : Blo 1248442 32017679 := bstep (se 1 (by rfl) ⟨24013259, by rfl⟩ : syracuseStep 32017679 = 48026519) B48026519
theorem B4001185 : Blo 1248442 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B1249535 : Blo 1248442 1249535 := bstep (se 1 (by rfl) ⟨937151, by rfl⟩ : syracuseStep 1249535 = 1874303) B1874303
theorem B1249607 : Blo 1248442 1249607 := bstep (se 1 (by rfl) ⟨937205, by rfl⟩ : syracuseStep 1249607 = 1874411) B1874411
theorem B2110043 : Blo 1248442 2110043 := bstep (se 1 (by rfl) ⟨1582532, by rfl⟩ : syracuseStep 2110043 = 3165065) B3165065
theorem B1250119 : Blo 1248442 1250119 := bstep (se 1 (by rfl) ⟨937589, by rfl⟩ : syracuseStep 1250119 = 1875179) B1875179
theorem B1250151 : Blo 1248442 1250151 := bstep (se 1 (by rfl) ⟨937613, by rfl⟩ : syracuseStep 1250151 = 1875227) B1875227
theorem B6001607 : Blo 1248442 6001607 := bstep (se 1 (by rfl) ⟨4501205, by rfl⟩ : syracuseStep 6001607 = 9002411) B9002411
theorem B1872863 : Blo 1248442 1872863 := bstep (se 1 (by rfl) ⟨1404647, by rfl⟩ : syracuseStep 1872863 = 2809295) B2809295
theorem B4215833 : Blo 1248442 4215833 := bstep (se 2 (by rfl) ⟨1580937, by rfl⟩ : syracuseStep 4215833 = 3161875) B3161875
theorem B1250407 : Blo 1248442 1250407 := bstep (se 1 (by rfl) ⟨937805, by rfl⟩ : syracuseStep 1250407 = 1875611) B1875611
theorem B9008495 : Blo 1248442 9008495 := bstep (se 1 (by rfl) ⟨6756371, by rfl⟩ : syracuseStep 9008495 = 13512743) B13512743
theorem B1873343 : Blo 1248442 1873343 := bstep (se 1 (by rfl) ⟨1405007, by rfl⟩ : syracuseStep 1873343 = 2810015) B2810015
theorem B1873463 : Blo 1248442 1873463 := bstep (se 1 (by rfl) ⟨1405097, by rfl⟩ : syracuseStep 1873463 = 2810195) B2810195
theorem B8001449 : Blo 1248442 8001449 := bstep (se 2 (by rfl) ⟨3000543, by rfl⟩ : syracuseStep 8001449 = 6001087) B6001087
theorem B10811495 : Blo 1248442 10811495 := bstep (se 1 (by rfl) ⟨8108621, by rfl⟩ : syracuseStep 10811495 = 16217243) B16217243
theorem B14235911 : Blo 1248442 14235911 := bstep (se 1 (by rfl) ⟨10676933, by rfl⟩ : syracuseStep 14235911 = 21353867) B21353867
theorem B3799315 : Blo 1248442 3799315 := bstep (se 1 (by rfl) ⟨2849486, by rfl⟩ : syracuseStep 3799315 = 5698973) B5698973
theorem B1874231 : Blo 1248442 1874231 := bstep (se 1 (by rfl) ⟨1405673, by rfl⟩ : syracuseStep 1874231 = 2811347) B2811347
theorem B32004557 : Blo 1248442 32004557 := bstep (se 3 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 32004557 = 12001709) B12001709
theorem B4217399 : Blo 1248442 4217399 := bstep (se 1 (by rfl) ⟨3163049, by rfl⟩ : syracuseStep 4217399 = 6326099) B6326099
theorem B60816095 : Blo 1248442 60816095 := bstep (se 1 (by rfl) ⟨45612071, by rfl⟩ : syracuseStep 60816095 = 91224143) B91224143
theorem B1874663 : Blo 1248442 1874663 := bstep (se 1 (by rfl) ⟨1405997, by rfl⟩ : syracuseStep 1874663 = 2811995) B2811995
theorem B4217939 : Blo 1248442 4217939 := bstep (se 1 (by rfl) ⟨3163454, by rfl⟩ : syracuseStep 4217939 = 6326909) B6326909
theorem B2809007 : Blo 1248442 2809007 := bstep (se 1 (by rfl) ⟨2106755, by rfl⟩ : syracuseStep 2809007 = 4213511) B4213511
theorem B16014581 : Blo 1248442 16014581 := bstep (se 5 (by rfl) ⟨750683, by rfl⟩ : syracuseStep 16014581 = 1501367) B1501367
theorem B2809259 : Blo 1248442 2809259 := bstep (se 1 (by rfl) ⟨2106944, by rfl⟩ : syracuseStep 2809259 = 4213889) B4213889
theorem B24337925 : Blo 1248442 24337925 := bstep (se 4 (by rfl) ⟨2281680, by rfl⟩ : syracuseStep 24337925 = 4563361) B4563361
theorem B1875647 : Blo 1248442 1875647 := bstep (se 1 (by rfl) ⟨1406735, by rfl⟩ : syracuseStep 1875647 = 2813471) B2813471
theorem B9494495 : Blo 1248442 9494495 := bstep (se 1 (by rfl) ⟨7120871, by rfl⟩ : syracuseStep 9494495 = 14241743) B14241743
theorem B71188703 : Blo 1248442 71188703 := bstep (se 1 (by rfl) ⟨53391527, by rfl⟩ : syracuseStep 71188703 = 106783055) B106783055
theorem B2810555 : Blo 1248442 2810555 := bstep (se 1 (by rfl) ⟨2107916, by rfl⟩ : syracuseStep 2810555 = 4215833) B4215833
theorem B6005663 : Blo 1248442 6005663 := bstep (se 1 (by rfl) ⟨4504247, by rfl⟩ : syracuseStep 6005663 = 9008495) B9008495
theorem B5334299 : Blo 1248442 5334299 := bstep (se 1 (by rfl) ⟨4000724, by rfl⟩ : syracuseStep 5334299 = 8001449) B8001449
theorem B2811599 : Blo 1248442 2811599 := bstep (se 1 (by rfl) ⟨2108699, by rfl⟩ : syracuseStep 2811599 = 4217399) B4217399
theorem B40544063 : Blo 1248442 40544063 := bstep (se 1 (by rfl) ⟨30408047, by rfl⟩ : syracuseStep 40544063 = 60816095) B60816095
theorem B5334913 : Blo 1248442 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B2811959 : Blo 1248442 2811959 := bstep (se 1 (by rfl) ⟨2108969, by rfl⟩ : syracuseStep 2811959 = 4217939) B4217939
theorem B10676387 : Blo 1248442 10676387 := bstep (se 1 (by rfl) ⟨8007290, by rfl⟩ : syracuseStep 10676387 = 16014581) B16014581
theorem B2812607 : Blo 1248442 2812607 := bstep (se 1 (by rfl) ⟨2109455, by rfl⟩ : syracuseStep 2812607 = 4218911) B4218911
theorem B12823265 : Blo 1248442 12823265 := bstep (se 2 (by rfl) ⟨4808724, by rfl⟩ : syracuseStep 12823265 = 9617449) B9617449
theorem B28830653 : Blo 1248442 28830653 := bstep (se 3 (by rfl) ⟨5405747, by rfl⟩ : syracuseStep 28830653 = 10811495) B10811495
theorem B20278259 : Blo 1248442 20278259 := bstep (se 1 (by rfl) ⟨15208694, by rfl⟩ : syracuseStep 20278259 = 30417389) B30417389
theorem B5065753 : Blo 1248442 5065753 := bstep (se 2 (by rfl) ⟨1899657, by rfl⟩ : syracuseStep 5065753 = 3799315) B3799315
theorem B5999761 : Blo 1248442 5999761 := bstep (se 2 (by rfl) ⟨2249910, by rfl⟩ : syracuseStep 5999761 = 4499821) B4499821
theorem B4001071 : Blo 1248442 4001071 := bstep (se 1 (by rfl) ⟨3000803, by rfl⟩ : syracuseStep 4001071 = 6001607) B6001607
theorem B1248575 : Blo 1248442 1248575 := bstep (se 1 (by rfl) ⟨936431, by rfl⟩ : syracuseStep 1248575 = 1872863) B1872863
theorem B1248895 : Blo 1248442 1248895 := bstep (se 1 (by rfl) ⟨936671, by rfl⟩ : syracuseStep 1248895 = 1873343) B1873343
theorem B1248975 : Blo 1248442 1248975 := bstep (se 1 (by rfl) ⟨936731, by rfl⟩ : syracuseStep 1248975 = 1873463) B1873463
theorem B9490607 : Blo 1248442 9490607 := bstep (se 1 (by rfl) ⟨7117955, by rfl⟩ : syracuseStep 9490607 = 14235911) B14235911
theorem B1249487 : Blo 1248442 1249487 := bstep (se 1 (by rfl) ⟨937115, by rfl⟩ : syracuseStep 1249487 = 1874231) B1874231
theorem B21336371 : Blo 1248442 21336371 := bstep (se 1 (by rfl) ⟨16002278, by rfl⟩ : syracuseStep 21336371 = 32004557) B32004557
theorem B1249775 : Blo 1248442 1249775 := bstep (se 1 (by rfl) ⟨937331, by rfl⟩ : syracuseStep 1249775 = 1874663) B1874663
theorem B1405471 : Blo 1248442 1405471 := bstep (se 1 (by rfl) ⟨1054103, by rfl⟩ : syracuseStep 1405471 = 2108207) B2108207
theorem B1872671 : Blo 1248442 1872671 := bstep (se 1 (by rfl) ⟨1404503, by rfl⟩ : syracuseStep 1872671 = 2809007) B2809007
theorem B21345119 : Blo 1248442 21345119 := bstep (se 1 (by rfl) ⟨16008839, by rfl⟩ : syracuseStep 21345119 = 32017679) B32017679
theorem B1872839 : Blo 1248442 1872839 := bstep (se 1 (by rfl) ⟨1404629, by rfl⟩ : syracuseStep 1872839 = 2809259) B2809259
theorem B16225283 : Blo 1248442 16225283 := bstep (se 1 (by rfl) ⟨12168962, by rfl⟩ : syracuseStep 16225283 = 24337925) B24337925
theorem B1250431 : Blo 1248442 1250431 := bstep (se 1 (by rfl) ⟨937823, by rfl⟩ : syracuseStep 1250431 = 1875647) B1875647
theorem B6329663 : Blo 1248442 6329663 := bstep (se 1 (by rfl) ⟨4747247, by rfl⟩ : syracuseStep 6329663 = 9494495) B9494495
theorem B1873535 : Blo 1248442 1873535 := bstep (se 1 (by rfl) ⟨1405151, by rfl⟩ : syracuseStep 1873535 = 2810303) B2810303
theorem B4740839 : Blo 1248442 4740839 := bstep (se 1 (by rfl) ⟨3555629, by rfl⟩ : syracuseStep 4740839 = 7111259) B7111259
theorem B1406695 : Blo 1248442 1406695 := bstep (se 1 (by rfl) ⟨1055021, by rfl⟩ : syracuseStep 1406695 = 2110043) B2110043
theorem B20536051 : Blo 1248442 20536051 := bstep (se 1 (by rfl) ⟨15402038, by rfl⟩ : syracuseStep 20536051 = 30804077) B30804077
theorem B1875035 : Blo 1248442 1875035 := bstep (se 1 (by rfl) ⟨1406276, by rfl⟩ : syracuseStep 1875035 = 2812553) B2812553
theorem B1875047 : Blo 1248442 1875047 := bstep (se 1 (by rfl) ⟨1406285, by rfl⟩ : syracuseStep 1875047 = 2812571) B2812571
theorem B14230079 : Blo 1248442 14230079 := bstep (se 1 (by rfl) ⟨10672559, by rfl⟩ : syracuseStep 14230079 = 21345119) B21345119
theorem B3556199 : Blo 1248442 3556199 := bstep (se 1 (by rfl) ⟨2667149, by rfl⟩ : syracuseStep 3556199 = 5334299) B5334299
theorem B4219775 : Blo 1248442 4219775 := bstep (se 1 (by rfl) ⟨3164831, by rfl⟩ : syracuseStep 4219775 = 6329663) B6329663
theorem B5334761 : Blo 1248442 5334761 := bstep (se 2 (by rfl) ⟨2000535, by rfl⟩ : syracuseStep 5334761 = 4001071) B4001071
theorem B19220435 : Blo 1248442 19220435 := bstep (se 1 (by rfl) ⟨14415326, by rfl⟩ : syracuseStep 19220435 = 28830653) B28830653
theorem B13518839 : Blo 1248442 13518839 := bstep (se 1 (by rfl) ⟨10139129, by rfl⟩ : syracuseStep 13518839 = 20278259) B20278259
theorem B7113217 : Blo 1248442 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B6327071 : Blo 1248442 6327071 := bstep (se 1 (by rfl) ⟨4745303, by rfl⟩ : syracuseStep 6327071 = 9490607) B9490607
theorem B47459135 : Blo 1248442 47459135 := bstep (se 1 (by rfl) ⟨35594351, by rfl⟩ : syracuseStep 47459135 = 71188703) B71188703
theorem B14224247 : Blo 1248442 14224247 := bstep (se 1 (by rfl) ⟨10668185, by rfl⟩ : syracuseStep 14224247 = 21336371) B21336371
theorem B1248447 : Blo 1248442 1248447 := bstep (se 1 (by rfl) ⟨936335, by rfl⟩ : syracuseStep 1248447 = 1872671) B1872671
theorem B1248559 : Blo 1248442 1248559 := bstep (se 1 (by rfl) ⟨936419, by rfl⟩ : syracuseStep 1248559 = 1872839) B1872839
theorem B27381401 : Blo 1248442 27381401 := bstep (se 2 (by rfl) ⟨10268025, by rfl⟩ : syracuseStep 27381401 = 20536051) B20536051
theorem B1249023 : Blo 1248442 1249023 := bstep (se 1 (by rfl) ⟨936767, by rfl⟩ : syracuseStep 1249023 = 1873535) B1873535
theorem B27029375 : Blo 1248442 27029375 := bstep (se 1 (by rfl) ⟨20272031, by rfl⟩ : syracuseStep 27029375 = 40544063) B40544063
theorem B6754337 : Blo 1248442 6754337 := bstep (se 2 (by rfl) ⟨2532876, by rfl⟩ : syracuseStep 6754337 = 5065753) B5065753
theorem B7999681 : Blo 1248442 7999681 := bstep (se 2 (by rfl) ⟨2999880, by rfl⟩ : syracuseStep 7999681 = 5999761) B5999761
theorem B8548843 : Blo 1248442 8548843 := bstep (se 1 (by rfl) ⟨6411632, by rfl⟩ : syracuseStep 8548843 = 12823265) B12823265
theorem B1250023 : Blo 1248442 1250023 := bstep (se 1 (by rfl) ⟨937517, by rfl⟩ : syracuseStep 1250023 = 1875035) B1875035
theorem B1250031 : Blo 1248442 1250031 := bstep (se 1 (by rfl) ⟨937523, by rfl⟩ : syracuseStep 1250031 = 1875047) B1875047
theorem B43267421 : Blo 1248442 43267421 := bstep (se 3 (by rfl) ⟨8112641, by rfl⟩ : syracuseStep 43267421 = 16225283) B16225283
theorem B1873703 : Blo 1248442 1873703 := bstep (se 1 (by rfl) ⟨1405277, by rfl⟩ : syracuseStep 1873703 = 2810555) B2810555
theorem B4003775 : Blo 1248442 4003775 := bstep (se 1 (by rfl) ⟨3002831, by rfl⟩ : syracuseStep 4003775 = 6005663) B6005663
theorem B1873961 : Blo 1248442 1873961 := bstep (se 2 (by rfl) ⟨702735, by rfl⟩ : syracuseStep 1873961 = 1405471) B1405471
theorem B1874399 : Blo 1248442 1874399 := bstep (se 1 (by rfl) ⟨1405799, by rfl⟩ : syracuseStep 1874399 = 2811599) B2811599
theorem B3160559 : Blo 1248442 3160559 := bstep (se 1 (by rfl) ⟨2370419, by rfl⟩ : syracuseStep 3160559 = 4740839) B4740839
theorem B1874639 : Blo 1248442 1874639 := bstep (se 1 (by rfl) ⟨1405979, by rfl⟩ : syracuseStep 1874639 = 2811959) B2811959
theorem B7117591 : Blo 1248442 7117591 := bstep (se 1 (by rfl) ⟨5338193, by rfl⟩ : syracuseStep 7117591 = 10676387) B10676387
theorem B1875071 : Blo 1248442 1875071 := bstep (se 1 (by rfl) ⟨1406303, by rfl⟩ : syracuseStep 1875071 = 2812607) B2812607
theorem B1875593 : Blo 1248442 1875593 := bstep (se 2 (by rfl) ⟨703347, by rfl⟩ : syracuseStep 1875593 = 1406695) B1406695
theorem B10666241 : Blo 1248442 10666241 := bstep (se 2 (by rfl) ⟨3999840, by rfl⟩ : syracuseStep 10666241 = 7999681) B7999681
theorem B9486719 : Blo 1248442 9486719 := bstep (se 1 (by rfl) ⟨7115039, by rfl⟩ : syracuseStep 9486719 = 14230079) B14230079
theorem B28844947 : Blo 1248442 28844947 := bstep (se 1 (by rfl) ⟨21633710, by rfl⟩ : syracuseStep 28844947 = 43267421) B43267421
theorem B3556507 : Blo 1248442 3556507 := bstep (se 1 (by rfl) ⟨2667380, by rfl⟩ : syracuseStep 3556507 = 5334761) B5334761
theorem B12813623 : Blo 1248442 12813623 := bstep (se 1 (by rfl) ⟨9610217, by rfl⟩ : syracuseStep 12813623 = 19220435) B19220435
theorem B9012559 : Blo 1248442 9012559 := bstep (se 1 (by rfl) ⟨6759419, by rfl⟩ : syracuseStep 9012559 = 13518839) B13518839
theorem B2107039 : Blo 1248442 2107039 := bstep (se 1 (by rfl) ⟨1580279, by rfl⟩ : syracuseStep 2107039 = 3160559) B3160559
theorem B31639423 : Blo 1248442 31639423 := bstep (se 1 (by rfl) ⟨23729567, by rfl⟩ : syracuseStep 31639423 = 47459135) B47459135
theorem B18254267 : Blo 1248442 18254267 := bstep (se 1 (by rfl) ⟨13690700, by rfl⟩ : syracuseStep 18254267 = 27381401) B27381401
theorem B2370799 : Blo 1248442 2370799 := bstep (se 1 (by rfl) ⟨1778099, by rfl⟩ : syracuseStep 2370799 = 3556199) B3556199
theorem B2813183 : Blo 1248442 2813183 := bstep (se 1 (by rfl) ⟨2109887, by rfl⟩ : syracuseStep 2813183 = 4219775) B4219775
theorem B11398457 : Blo 1248442 11398457 := bstep (se 2 (by rfl) ⟨4274421, by rfl⟩ : syracuseStep 11398457 = 8548843) B8548843
theorem B9490121 : Blo 1248442 9490121 := bstep (se 2 (by rfl) ⟨3558795, by rfl⟩ : syracuseStep 9490121 = 7117591) B7117591
theorem B1249135 : Blo 1248442 1249135 := bstep (se 1 (by rfl) ⟨936851, by rfl⟩ : syracuseStep 1249135 = 1873703) B1873703
theorem B1249307 : Blo 1248442 1249307 := bstep (se 1 (by rfl) ⟨936980, by rfl⟩ : syracuseStep 1249307 = 1873961) B1873961
theorem B1249599 : Blo 1248442 1249599 := bstep (se 1 (by rfl) ⟨937199, by rfl⟩ : syracuseStep 1249599 = 1874399) B1874399
theorem B1249759 : Blo 1248442 1249759 := bstep (se 1 (by rfl) ⟨937319, by rfl⟩ : syracuseStep 1249759 = 1874639) B1874639
theorem B9482831 : Blo 1248442 9482831 := bstep (se 1 (by rfl) ⟨7112123, by rfl⟩ : syracuseStep 9482831 = 14224247) B14224247
theorem B1250047 : Blo 1248442 1250047 := bstep (se 1 (by rfl) ⟨937535, by rfl⟩ : syracuseStep 1250047 = 1875071) B1875071
theorem B1250395 : Blo 1248442 1250395 := bstep (se 1 (by rfl) ⟨937796, by rfl⟩ : syracuseStep 1250395 = 1875593) B1875593
theorem B18019583 : Blo 1248442 18019583 := bstep (se 1 (by rfl) ⟨13514687, by rfl⟩ : syracuseStep 18019583 = 27029375) B27029375
theorem B4502891 : Blo 1248442 4502891 := bstep (se 1 (by rfl) ⟨3377168, by rfl⟩ : syracuseStep 4502891 = 6754337) B6754337
theorem B9484289 : Blo 1248442 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B2669183 : Blo 1248442 2669183 := bstep (se 1 (by rfl) ⟨2001887, by rfl⟩ : syracuseStep 2669183 = 4003775) B4003775
theorem B4218047 : Blo 1248442 4218047 := bstep (se 1 (by rfl) ⟨3163535, by rfl⟩ : syracuseStep 4218047 = 6327071) B6327071
theorem B7110827 : Blo 1248442 7110827 := bstep (se 1 (by rfl) ⟨5333120, by rfl⟩ : syracuseStep 7110827 = 10666241) B10666241
theorem B6324479 : Blo 1248442 6324479 := bstep (se 1 (by rfl) ⟨4743359, by rfl⟩ : syracuseStep 6324479 = 9486719) B9486719
theorem B1779455 : Blo 1248442 1779455 := bstep (se 1 (by rfl) ⟨1334591, by rfl⟩ : syracuseStep 1779455 = 2669183) B2669183
theorem B2812031 : Blo 1248442 2812031 := bstep (se 1 (by rfl) ⟨2109023, by rfl⟩ : syracuseStep 2812031 = 4218047) B4218047
theorem B6326747 : Blo 1248442 6326747 := bstep (se 1 (by rfl) ⟨4745060, by rfl⟩ : syracuseStep 6326747 = 9490121) B9490121
theorem B12013055 : Blo 1248442 12013055 := bstep (se 1 (by rfl) ⟨9009791, by rfl⟩ : syracuseStep 12013055 = 18019583) B18019583
theorem B12169511 : Blo 1248442 12169511 := bstep (se 1 (by rfl) ⟨9127133, by rfl⟩ : syracuseStep 12169511 = 18254267) B18254267
theorem B7598971 : Blo 1248442 7598971 := bstep (se 1 (by rfl) ⟨5699228, by rfl⟩ : syracuseStep 7598971 = 11398457) B11398457
theorem B42185897 : Blo 1248442 42185897 := bstep (se 2 (by rfl) ⟨15819711, by rfl⟩ : syracuseStep 42185897 = 31639423) B31639423
theorem B6321887 : Blo 1248442 6321887 := bstep (se 1 (by rfl) ⟨4741415, by rfl⟩ : syracuseStep 6321887 = 9482831) B9482831
theorem B8542415 : Blo 1248442 8542415 := bstep (se 1 (by rfl) ⟨6406811, by rfl⟩ : syracuseStep 8542415 = 12813623) B12813623
theorem B12007709 : Blo 1248442 12007709 := bstep (se 3 (by rfl) ⟨2251445, by rfl⟩ : syracuseStep 12007709 = 4502891) B4502891
theorem B38459929 : Blo 1248442 38459929 := bstep (se 2 (by rfl) ⟨14422473, by rfl⟩ : syracuseStep 38459929 = 28844947) B28844947
theorem B6322859 : Blo 1248442 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B4742009 : Blo 1248442 4742009 := bstep (se 2 (by rfl) ⟨1778253, by rfl⟩ : syracuseStep 4742009 = 3556507) B3556507
theorem B3161065 : Blo 1248442 3161065 := bstep (se 2 (by rfl) ⟨1185399, by rfl⟩ : syracuseStep 3161065 = 2370799) B2370799
theorem B12016745 : Blo 1248442 12016745 := bstep (se 2 (by rfl) ⟨4506279, by rfl⟩ : syracuseStep 12016745 = 9012559) B9012559
theorem B1875455 : Blo 1248442 1875455 := bstep (se 1 (by rfl) ⟨1406591, by rfl⟩ : syracuseStep 1875455 = 2813183) B2813183
theorem B2809385 : Blo 1248442 2809385 := bstep (se 2 (by rfl) ⟨1053519, by rfl⟩ : syracuseStep 2809385 = 2107039) B2107039
theorem B28123931 : Blo 1248442 28123931 := bstep (se 1 (by rfl) ⟨21092948, by rfl⟩ : syracuseStep 28123931 = 42185897) B42185897
theorem B5694943 : Blo 1248442 5694943 := bstep (se 1 (by rfl) ⟨4271207, by rfl⟩ : syracuseStep 5694943 = 8542415) B8542415
theorem B8005139 : Blo 1248442 8005139 := bstep (se 1 (by rfl) ⟨6003854, by rfl⟩ : syracuseStep 8005139 = 12007709) B12007709
theorem B4745213 : Blo 1248442 4745213 := bstep (se 3 (by rfl) ⟨889727, by rfl⟩ : syracuseStep 4745213 = 1779455) B1779455
theorem B8113007 : Blo 1248442 8113007 := bstep (se 1 (by rfl) ⟨6084755, by rfl⟩ : syracuseStep 8113007 = 12169511) B12169511
theorem B4214591 : Blo 1248442 4214591 := bstep (se 1 (by rfl) ⟨3160943, by rfl⟩ : syracuseStep 4214591 = 6321887) B6321887
theorem B4214753 : Blo 1248442 4214753 := bstep (se 2 (by rfl) ⟨1580532, by rfl⟩ : syracuseStep 4214753 = 3161065) B3161065
theorem B4215239 : Blo 1248442 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B8008703 : Blo 1248442 8008703 := bstep (se 1 (by rfl) ⟨6006527, by rfl⟩ : syracuseStep 8008703 = 12013055) B12013055
theorem B1250303 : Blo 1248442 1250303 := bstep (se 1 (by rfl) ⟨937727, by rfl⟩ : syracuseStep 1250303 = 1875455) B1875455
theorem B1872923 : Blo 1248442 1872923 := bstep (se 1 (by rfl) ⟨1404692, by rfl⟩ : syracuseStep 1872923 = 2809385) B2809385
theorem B4740551 : Blo 1248442 4740551 := bstep (se 1 (by rfl) ⟨3555413, by rfl⟩ : syracuseStep 4740551 = 7110827) B7110827
theorem B4216319 : Blo 1248442 4216319 := bstep (se 1 (by rfl) ⟨3162239, by rfl⟩ : syracuseStep 4216319 = 6324479) B6324479
theorem B51279905 : Blo 1248442 51279905 := bstep (se 2 (by rfl) ⟨19229964, by rfl⟩ : syracuseStep 51279905 = 38459929) B38459929
theorem B10131961 : Blo 1248442 10131961 := bstep (se 2 (by rfl) ⟨3799485, by rfl⟩ : syracuseStep 10131961 = 7598971) B7598971
theorem B1874687 : Blo 1248442 1874687 := bstep (se 1 (by rfl) ⟨1406015, by rfl⟩ : syracuseStep 1874687 = 2812031) B2812031
theorem B4217831 : Blo 1248442 4217831 := bstep (se 1 (by rfl) ⟨3163373, by rfl⟩ : syracuseStep 4217831 = 6326747) B6326747
theorem B3161339 : Blo 1248442 3161339 := bstep (se 1 (by rfl) ⟨2371004, by rfl⟩ : syracuseStep 3161339 = 4742009) B4742009
theorem B8011163 : Blo 1248442 8011163 := bstep (se 1 (by rfl) ⟨6008372, by rfl⟩ : syracuseStep 8011163 = 12016745) B12016745
theorem B2810159 : Blo 1248442 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B13509281 : Blo 1248442 13509281 := bstep (se 2 (by rfl) ⟨5065980, by rfl⟩ : syracuseStep 13509281 = 10131961) B10131961
theorem B2810879 : Blo 1248442 2810879 := bstep (se 1 (by rfl) ⟨2108159, by rfl⟩ : syracuseStep 2810879 = 4216319) B4216319
theorem B3163475 : Blo 1248442 3163475 := bstep (se 1 (by rfl) ⟨2372606, by rfl⟩ : syracuseStep 3163475 = 4745213) B4745213
theorem B2811887 : Blo 1248442 2811887 := bstep (se 1 (by rfl) ⟨2108915, by rfl⟩ : syracuseStep 2811887 = 4217831) B4217831
theorem B2107559 : Blo 1248442 2107559 := bstep (se 1 (by rfl) ⟨1580669, by rfl⟩ : syracuseStep 2107559 = 3161339) B3161339
theorem B1248615 : Blo 1248442 1248615 := bstep (se 1 (by rfl) ⟨936461, by rfl⟩ : syracuseStep 1248615 = 1872923) B1872923
theorem B5336759 : Blo 1248442 5336759 := bstep (se 1 (by rfl) ⟨4002569, by rfl⟩ : syracuseStep 5336759 = 8005139) B8005139
theorem B1249791 : Blo 1248442 1249791 := bstep (se 1 (by rfl) ⟨937343, by rfl⟩ : syracuseStep 1249791 = 1874687) B1874687
theorem B136746413 : Blo 1248442 136746413 := bstep (se 3 (by rfl) ⟨25639952, by rfl⟩ : syracuseStep 136746413 = 51279905) B51279905
theorem B18749287 : Blo 1248442 18749287 := bstep (se 1 (by rfl) ⟨14061965, by rfl⟩ : syracuseStep 18749287 = 28123931) B28123931
theorem B5339135 : Blo 1248442 5339135 := bstep (se 1 (by rfl) ⟨4004351, by rfl⟩ : syracuseStep 5339135 = 8008703) B8008703
theorem B3160367 : Blo 1248442 3160367 := bstep (se 1 (by rfl) ⟨2370275, by rfl⟩ : syracuseStep 3160367 = 4740551) B4740551
theorem B7593257 : Blo 1248442 7593257 := bstep (se 2 (by rfl) ⟨2847471, by rfl⟩ : syracuseStep 7593257 = 5694943) B5694943
theorem B5340775 : Blo 1248442 5340775 := bstep (se 1 (by rfl) ⟨4005581, by rfl⟩ : syracuseStep 5340775 = 8011163) B8011163
theorem B21634685 : Blo 1248442 21634685 := bstep (se 3 (by rfl) ⟨4056503, by rfl⟩ : syracuseStep 21634685 = 8113007) B8113007
theorem B2809727 : Blo 1248442 2809727 := bstep (se 1 (by rfl) ⟨2107295, by rfl⟩ : syracuseStep 2809727 = 4214591) B4214591
theorem B2809835 : Blo 1248442 2809835 := bstep (se 1 (by rfl) ⟨2107376, by rfl⟩ : syracuseStep 2809835 = 4214753) B4214753
theorem B2106911 : Blo 1248442 2106911 := bstep (se 1 (by rfl) ⟨1580183, by rfl⟩ : syracuseStep 2106911 = 3160367) B3160367
theorem B7121033 : Blo 1248442 7121033 := bstep (se 2 (by rfl) ⟨2670387, by rfl⟩ : syracuseStep 7121033 = 5340775) B5340775
theorem B3557839 : Blo 1248442 3557839 := bstep (se 1 (by rfl) ⟨2668379, by rfl⟩ : syracuseStep 3557839 = 5336759) B5336759
theorem B9006187 : Blo 1248442 9006187 := bstep (se 1 (by rfl) ⟨6754640, by rfl⟩ : syracuseStep 9006187 = 13509281) B13509281
theorem B2108983 : Blo 1248442 2108983 := bstep (se 1 (by rfl) ⟨1581737, by rfl⟩ : syracuseStep 2108983 = 3163475) B3163475
theorem B91164275 : Blo 1248442 91164275 := bstep (se 1 (by rfl) ⟨68373206, by rfl⟩ : syracuseStep 91164275 = 136746413) B136746413
theorem B3559423 : Blo 1248442 3559423 := bstep (se 1 (by rfl) ⟨2669567, by rfl⟩ : syracuseStep 3559423 = 5339135) B5339135
theorem B1405039 : Blo 1248442 1405039 := bstep (se 1 (by rfl) ⟨1053779, by rfl⟩ : syracuseStep 1405039 = 2107559) B2107559
theorem B14423123 : Blo 1248442 14423123 := bstep (se 1 (by rfl) ⟨10817342, by rfl⟩ : syracuseStep 14423123 = 21634685) B21634685
theorem B24999049 : Blo 1248442 24999049 := bstep (se 2 (by rfl) ⟨9374643, by rfl⟩ : syracuseStep 24999049 = 18749287) B18749287
theorem B1873151 : Blo 1248442 1873151 := bstep (se 1 (by rfl) ⟨1404863, by rfl⟩ : syracuseStep 1873151 = 2809727) B2809727
theorem B1873223 : Blo 1248442 1873223 := bstep (se 1 (by rfl) ⟨1404917, by rfl⟩ : syracuseStep 1873223 = 2809835) B2809835
theorem B1873439 : Blo 1248442 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B1873919 : Blo 1248442 1873919 := bstep (se 1 (by rfl) ⟨1405439, by rfl⟩ : syracuseStep 1873919 = 2810879) B2810879
theorem B1874591 : Blo 1248442 1874591 := bstep (se 1 (by rfl) ⟨1405943, by rfl⟩ : syracuseStep 1874591 = 2811887) B2811887
theorem B5062171 : Blo 1248442 5062171 := bstep (se 1 (by rfl) ⟨3796628, by rfl⟩ : syracuseStep 5062171 = 7593257) B7593257
theorem B38461661 : Blo 1248442 38461661 := bstep (se 3 (by rfl) ⟨7211561, by rfl⟩ : syracuseStep 38461661 = 14423123) B14423123
theorem B4743785 : Blo 1248442 4743785 := bstep (se 2 (by rfl) ⟨1778919, by rfl⟩ : syracuseStep 4743785 = 3557839) B3557839
theorem B2811977 : Blo 1248442 2811977 := bstep (se 2 (by rfl) ⟨1054491, by rfl⟩ : syracuseStep 2811977 = 2108983) B2108983
theorem B4745897 : Blo 1248442 4745897 := bstep (se 2 (by rfl) ⟨1779711, by rfl⟩ : syracuseStep 4745897 = 3559423) B3559423
theorem B133328261 : Blo 1248442 133328261 := bstep (se 4 (by rfl) ⟨12499524, by rfl⟩ : syracuseStep 133328261 = 24999049) B24999049
theorem B1248767 : Blo 1248442 1248767 := bstep (se 1 (by rfl) ⟨936575, by rfl⟩ : syracuseStep 1248767 = 1873151) B1873151
theorem B1248815 : Blo 1248442 1248815 := bstep (se 1 (by rfl) ⟨936611, by rfl⟩ : syracuseStep 1248815 = 1873223) B1873223
theorem B1404607 : Blo 1248442 1404607 := bstep (se 1 (by rfl) ⟨1053455, by rfl⟩ : syracuseStep 1404607 = 2106911) B2106911
theorem B1248959 : Blo 1248442 1248959 := bstep (se 1 (by rfl) ⟨936719, by rfl⟩ : syracuseStep 1248959 = 1873439) B1873439
theorem B1249279 : Blo 1248442 1249279 := bstep (se 1 (by rfl) ⟨936959, by rfl⟩ : syracuseStep 1249279 = 1873919) B1873919
theorem B4747355 : Blo 1248442 4747355 := bstep (se 1 (by rfl) ⟨3560516, by rfl⟩ : syracuseStep 4747355 = 7121033) B7121033
theorem B1249727 : Blo 1248442 1249727 := bstep (se 1 (by rfl) ⟨937295, by rfl⟩ : syracuseStep 1249727 = 1874591) B1874591
theorem B1873385 : Blo 1248442 1873385 := bstep (se 2 (by rfl) ⟨702519, by rfl⟩ : syracuseStep 1873385 = 1405039) B1405039
theorem B12008249 : Blo 1248442 12008249 := bstep (se 2 (by rfl) ⟨4503093, by rfl⟩ : syracuseStep 12008249 = 9006187) B9006187
theorem B6749561 : Blo 1248442 6749561 := bstep (se 2 (by rfl) ⟨2531085, by rfl⟩ : syracuseStep 6749561 = 5062171) B5062171
theorem B60776183 : Blo 1248442 60776183 := bstep (se 1 (by rfl) ⟨45582137, by rfl⟩ : syracuseStep 60776183 = 91164275) B91164275
theorem B25641107 : Blo 1248442 25641107 := bstep (se 1 (by rfl) ⟨19230830, by rfl⟩ : syracuseStep 25641107 = 38461661) B38461661
theorem B3162523 : Blo 1248442 3162523 := bstep (se 1 (by rfl) ⟨2371892, by rfl⟩ : syracuseStep 3162523 = 4743785) B4743785
theorem B3163931 : Blo 1248442 3163931 := bstep (se 1 (by rfl) ⟨2372948, by rfl⟩ : syracuseStep 3163931 = 4745897) B4745897
theorem B8005499 : Blo 1248442 8005499 := bstep (se 1 (by rfl) ⟨6004124, by rfl⟩ : syracuseStep 8005499 = 12008249) B12008249
theorem B4499707 : Blo 1248442 4499707 := bstep (se 1 (by rfl) ⟨3374780, by rfl⟩ : syracuseStep 4499707 = 6749561) B6749561
theorem B88885507 : Blo 1248442 88885507 := bstep (se 1 (by rfl) ⟨66664130, by rfl⟩ : syracuseStep 88885507 = 133328261) B133328261
theorem B3164903 : Blo 1248442 3164903 := bstep (se 1 (by rfl) ⟨2373677, by rfl⟩ : syracuseStep 3164903 = 4747355) B4747355
theorem B1248923 : Blo 1248442 1248923 := bstep (se 1 (by rfl) ⟨936692, by rfl⟩ : syracuseStep 1248923 = 1873385) B1873385
theorem B1872809 : Blo 1248442 1872809 := bstep (se 2 (by rfl) ⟨702303, by rfl⟩ : syracuseStep 1872809 = 1404607) B1404607
theorem B1874651 : Blo 1248442 1874651 := bstep (se 1 (by rfl) ⟨1405988, by rfl⟩ : syracuseStep 1874651 = 2811977) B2811977
theorem B40517455 : Blo 1248442 40517455 := bstep (se 1 (by rfl) ⟨30388091, by rfl⟩ : syracuseStep 40517455 = 60776183) B60776183
theorem B118514009 : Blo 1248442 118514009 := bstep (se 2 (by rfl) ⟨44442753, by rfl⟩ : syracuseStep 118514009 = 88885507) B88885507
theorem B5999609 : Blo 1248442 5999609 := bstep (se 2 (by rfl) ⟨2249853, by rfl⟩ : syracuseStep 5999609 = 4499707) B4499707
theorem B1248539 : Blo 1248442 1248539 := bstep (se 1 (by rfl) ⟨936404, by rfl⟩ : syracuseStep 1248539 = 1872809) B1872809
theorem B2109287 : Blo 1248442 2109287 := bstep (se 1 (by rfl) ⟨1581965, by rfl⟩ : syracuseStep 2109287 = 3163931) B3163931
theorem B5336999 : Blo 1248442 5336999 := bstep (se 1 (by rfl) ⟨4002749, by rfl⟩ : syracuseStep 5336999 = 8005499) B8005499
theorem B1249767 : Blo 1248442 1249767 := bstep (se 1 (by rfl) ⟨937325, by rfl⟩ : syracuseStep 1249767 = 1874651) B1874651
theorem B2109935 : Blo 1248442 2109935 := bstep (se 1 (by rfl) ⟨1582451, by rfl⟩ : syracuseStep 2109935 = 3164903) B3164903
theorem B54023273 : Blo 1248442 54023273 := bstep (se 2 (by rfl) ⟨20258727, by rfl⟩ : syracuseStep 54023273 = 40517455) B40517455
theorem B17094071 : Blo 1248442 17094071 := bstep (se 1 (by rfl) ⟨12820553, by rfl⟩ : syracuseStep 17094071 = 25641107) B25641107
theorem B4216697 : Blo 1248442 4216697 := bstep (se 2 (by rfl) ⟨1581261, by rfl⟩ : syracuseStep 4216697 = 3162523) B3162523
theorem B11396047 : Blo 1248442 11396047 := bstep (se 1 (by rfl) ⟨8547035, by rfl⟩ : syracuseStep 11396047 = 17094071) B17094071
theorem B2811131 : Blo 1248442 2811131 := bstep (se 1 (by rfl) ⟨2108348, by rfl⟩ : syracuseStep 2811131 = 4216697) B4216697
theorem B3999739 : Blo 1248442 3999739 := bstep (se 1 (by rfl) ⟨2999804, by rfl⟩ : syracuseStep 3999739 = 5999609) B5999609
theorem B3557999 : Blo 1248442 3557999 := bstep (se 1 (by rfl) ⟨2668499, by rfl⟩ : syracuseStep 3557999 = 5336999) B5336999
theorem B36015515 : Blo 1248442 36015515 := bstep (se 1 (by rfl) ⟨27011636, by rfl⟩ : syracuseStep 36015515 = 54023273) B54023273
theorem B1406191 : Blo 1248442 1406191 := bstep (se 1 (by rfl) ⟨1054643, by rfl⟩ : syracuseStep 1406191 = 2109287) B2109287
theorem B79009339 : Blo 1248442 79009339 := bstep (se 1 (by rfl) ⟨59257004, by rfl⟩ : syracuseStep 79009339 = 118514009) B118514009
theorem B1406623 : Blo 1248442 1406623 := bstep (se 1 (by rfl) ⟨1054967, by rfl⟩ : syracuseStep 1406623 = 2109935) B2109935
theorem B5332985 : Blo 1248442 5332985 := bstep (se 2 (by rfl) ⟨1999869, by rfl⟩ : syracuseStep 5332985 = 3999739) B3999739
theorem B2371999 : Blo 1248442 2371999 := bstep (se 1 (by rfl) ⟨1778999, by rfl⟩ : syracuseStep 2371999 = 3557999) B3557999
theorem B105345785 : Blo 1248442 105345785 := bstep (se 2 (by rfl) ⟨39504669, by rfl⟩ : syracuseStep 105345785 = 79009339) B79009339
theorem B1874087 : Blo 1248442 1874087 := bstep (se 1 (by rfl) ⟨1405565, by rfl⟩ : syracuseStep 1874087 = 2811131) B2811131
theorem B15194729 : Blo 1248442 15194729 := bstep (se 2 (by rfl) ⟨5698023, by rfl⟩ : syracuseStep 15194729 = 11396047) B11396047
theorem B1874921 : Blo 1248442 1874921 := bstep (se 2 (by rfl) ⟨703095, by rfl⟩ : syracuseStep 1874921 = 1406191) B1406191
theorem B1875497 : Blo 1248442 1875497 := bstep (se 2 (by rfl) ⟨703311, by rfl⟩ : syracuseStep 1875497 = 1406623) B1406623
theorem B24010343 : Blo 1248442 24010343 := bstep (se 1 (by rfl) ⟨18007757, by rfl⟩ : syracuseStep 24010343 = 36015515) B36015515
theorem B70230523 : Blo 1248442 70230523 := bstep (se 1 (by rfl) ⟨52672892, by rfl⟩ : syracuseStep 70230523 = 105345785) B105345785
theorem B3162665 : Blo 1248442 3162665 := bstep (se 2 (by rfl) ⟨1185999, by rfl⟩ : syracuseStep 3162665 = 2371999) B2371999
theorem B1249391 : Blo 1248442 1249391 := bstep (se 1 (by rfl) ⟨937043, by rfl⟩ : syracuseStep 1249391 = 1874087) B1874087
theorem B10129819 : Blo 1248442 10129819 := bstep (se 1 (by rfl) ⟨7597364, by rfl⟩ : syracuseStep 10129819 = 15194729) B15194729
theorem B1249947 : Blo 1248442 1249947 := bstep (se 1 (by rfl) ⟨937460, by rfl⟩ : syracuseStep 1249947 = 1874921) B1874921
theorem B1250331 : Blo 1248442 1250331 := bstep (se 1 (by rfl) ⟨937748, by rfl⟩ : syracuseStep 1250331 = 1875497) B1875497
theorem B16006895 : Blo 1248442 16006895 := bstep (se 1 (by rfl) ⟨12005171, by rfl⟩ : syracuseStep 16006895 = 24010343) B24010343
theorem B3555323 : Blo 1248442 3555323 := bstep (se 1 (by rfl) ⟨2666492, by rfl⟩ : syracuseStep 3555323 = 5332985) B5332985
theorem B2370215 : Blo 1248442 2370215 := bstep (se 1 (by rfl) ⟨1777661, by rfl⟩ : syracuseStep 2370215 = 3555323) B3555323
theorem B2108443 : Blo 1248442 2108443 := bstep (se 1 (by rfl) ⟨1581332, by rfl⟩ : syracuseStep 2108443 = 3162665) B3162665
theorem B10671263 : Blo 1248442 10671263 := bstep (se 1 (by rfl) ⟨8003447, by rfl⟩ : syracuseStep 10671263 = 16006895) B16006895
theorem B13506425 : Blo 1248442 13506425 := bstep (se 2 (by rfl) ⟨5064909, by rfl⟩ : syracuseStep 13506425 = 10129819) B10129819
theorem B93640697 : Blo 1248442 93640697 := bstep (se 2 (by rfl) ⟨35115261, by rfl⟩ : syracuseStep 93640697 = 70230523) B70230523
theorem B9004283 : Blo 1248442 9004283 := bstep (se 1 (by rfl) ⟨6753212, by rfl⟩ : syracuseStep 9004283 = 13506425) B13506425
theorem B2811257 : Blo 1248442 2811257 := bstep (se 2 (by rfl) ⟨1054221, by rfl⟩ : syracuseStep 2811257 = 2108443) B2108443
theorem B7114175 : Blo 1248442 7114175 := bstep (se 1 (by rfl) ⟨5335631, by rfl⟩ : syracuseStep 7114175 = 10671263) B10671263
theorem B62427131 : Blo 1248442 62427131 := bstep (se 1 (by rfl) ⟨46820348, by rfl⟩ : syracuseStep 62427131 = 93640697) B93640697
theorem B1580143 : Blo 1248442 1580143 := bstep (se 1 (by rfl) ⟨1185107, by rfl⟩ : syracuseStep 1580143 = 2370215) B2370215
theorem B2106857 : Blo 1248442 2106857 := bstep (se 2 (by rfl) ⟨790071, by rfl⟩ : syracuseStep 2106857 = 1580143) B1580143
theorem B41618087 : Blo 1248442 41618087 := bstep (se 1 (by rfl) ⟨31213565, by rfl⟩ : syracuseStep 41618087 = 62427131) B62427131
theorem B6002855 : Blo 1248442 6002855 := bstep (se 1 (by rfl) ⟨4502141, by rfl⟩ : syracuseStep 6002855 = 9004283) B9004283
theorem B1874171 : Blo 1248442 1874171 := bstep (se 1 (by rfl) ⟨1405628, by rfl⟩ : syracuseStep 1874171 = 2811257) B2811257
theorem B4742783 : Blo 1248442 4742783 := bstep (se 1 (by rfl) ⟨3557087, by rfl⟩ : syracuseStep 4742783 = 7114175) B7114175
theorem B1404571 : Blo 1248442 1404571 := bstep (se 1 (by rfl) ⟨1053428, by rfl⟩ : syracuseStep 1404571 = 2106857) B2106857
theorem B4001903 : Blo 1248442 4001903 := bstep (se 1 (by rfl) ⟨3001427, by rfl⟩ : syracuseStep 4001903 = 6002855) B6002855
theorem B1249447 : Blo 1248442 1249447 := bstep (se 1 (by rfl) ⟨937085, by rfl⟩ : syracuseStep 1249447 = 1874171) B1874171
theorem B27745391 : Blo 1248442 27745391 := bstep (se 1 (by rfl) ⟨20809043, by rfl⟩ : syracuseStep 27745391 = 41618087) B41618087
theorem B3161855 : Blo 1248442 3161855 := bstep (se 1 (by rfl) ⟨2371391, by rfl⟩ : syracuseStep 3161855 = 4742783) B4742783
theorem B2107903 : Blo 1248442 2107903 := bstep (se 1 (by rfl) ⟨1580927, by rfl⟩ : syracuseStep 2107903 = 3161855) B3161855
theorem B1872761 : Blo 1248442 1872761 := bstep (se 2 (by rfl) ⟨702285, by rfl⟩ : syracuseStep 1872761 = 1404571) B1404571
theorem B2667935 : Blo 1248442 2667935 := bstep (se 1 (by rfl) ⟨2000951, by rfl⟩ : syracuseStep 2667935 = 4001903) B4001903
theorem B18496927 : Blo 1248442 18496927 := bstep (se 1 (by rfl) ⟨13872695, by rfl⟩ : syracuseStep 18496927 = 27745391) B27745391
theorem B2810537 : Blo 1248442 2810537 := bstep (se 2 (by rfl) ⟨1053951, by rfl⟩ : syracuseStep 2810537 = 2107903) B2107903
theorem B1248507 : Blo 1248442 1248507 := bstep (se 1 (by rfl) ⟨936380, by rfl⟩ : syracuseStep 1248507 = 1872761) B1872761
theorem B7114493 : Blo 1248442 7114493 := bstep (se 3 (by rfl) ⟨1333967, by rfl⟩ : syracuseStep 7114493 = 2667935) B2667935
theorem B24662569 : Blo 1248442 24662569 := bstep (se 2 (by rfl) ⟨9248463, by rfl⟩ : syracuseStep 24662569 = 18496927) B18496927
theorem B32883425 : Blo 1248442 32883425 := bstep (se 2 (by rfl) ⟨12331284, by rfl⟩ : syracuseStep 32883425 = 24662569) B24662569
theorem B1873691 : Blo 1248442 1873691 := bstep (se 1 (by rfl) ⟨1405268, by rfl⟩ : syracuseStep 1873691 = 2810537) B2810537
theorem B4742995 : Blo 1248442 4742995 := bstep (se 1 (by rfl) ⟨3557246, by rfl⟩ : syracuseStep 4742995 = 7114493) B7114493
theorem B21922283 : Blo 1248442 21922283 := bstep (se 1 (by rfl) ⟨16441712, by rfl⟩ : syracuseStep 21922283 = 32883425) B32883425
theorem B1249127 : Blo 1248442 1249127 := bstep (se 1 (by rfl) ⟨936845, by rfl⟩ : syracuseStep 1249127 = 1873691) B1873691
theorem B6323993 : Blo 1248442 6323993 := bstep (se 2 (by rfl) ⟨2371497, by rfl⟩ : syracuseStep 6323993 = 4742995) B4742995
theorem B58459421 : Blo 1248442 58459421 := bstep (se 3 (by rfl) ⟨10961141, by rfl⟩ : syracuseStep 58459421 = 21922283) B21922283
theorem B4215995 : Blo 1248442 4215995 := bstep (se 1 (by rfl) ⟨3161996, by rfl⟩ : syracuseStep 4215995 = 6323993) B6323993
theorem B2810663 : Blo 1248442 2810663 := bstep (se 1 (by rfl) ⟨2107997, by rfl⟩ : syracuseStep 2810663 = 4215995) B4215995
theorem B155891789 : Blo 1248442 155891789 := bstep (se 3 (by rfl) ⟨29229710, by rfl⟩ : syracuseStep 155891789 = 58459421) B58459421
theorem B103927859 : Blo 1248442 103927859 := bstep (se 1 (by rfl) ⟨77945894, by rfl⟩ : syracuseStep 103927859 = 155891789) B155891789
theorem B1873775 : Blo 1248442 1873775 := bstep (se 1 (by rfl) ⟨1405331, by rfl⟩ : syracuseStep 1873775 = 2810663) B2810663
theorem B1249183 : Blo 1248442 1249183 := bstep (se 1 (by rfl) ⟨936887, by rfl⟩ : syracuseStep 1249183 = 1873775) B1873775
theorem B69285239 : Blo 1248442 69285239 := bstep (se 1 (by rfl) ⟨51963929, by rfl⟩ : syracuseStep 69285239 = 103927859) B103927859
theorem B46190159 : Blo 1248442 46190159 := bstep (se 1 (by rfl) ⟨34642619, by rfl⟩ : syracuseStep 46190159 = 69285239) B69285239
theorem B30793439 : Blo 1248442 30793439 := bstep (se 1 (by rfl) ⟨23095079, by rfl⟩ : syracuseStep 30793439 = 46190159) B46190159
theorem B20528959 : Blo 1248442 20528959 := bstep (se 1 (by rfl) ⟨15396719, by rfl⟩ : syracuseStep 20528959 = 30793439) B30793439
theorem B27371945 : Blo 1248442 27371945 := bstep (se 2 (by rfl) ⟨10264479, by rfl⟩ : syracuseStep 27371945 = 20528959) B20528959
theorem B18247963 : Blo 1248442 18247963 := bstep (se 1 (by rfl) ⟨13685972, by rfl⟩ : syracuseStep 18247963 = 27371945) B27371945
theorem B24330617 : Blo 1248442 24330617 := bstep (se 2 (by rfl) ⟨9123981, by rfl⟩ : syracuseStep 24330617 = 18247963) B18247963
theorem B16220411 : Blo 1248442 16220411 := bstep (se 1 (by rfl) ⟨12165308, by rfl⟩ : syracuseStep 16220411 = 24330617) B24330617
theorem B10813607 : Blo 1248442 10813607 := bstep (se 1 (by rfl) ⟨8110205, by rfl⟩ : syracuseStep 10813607 = 16220411) B16220411
theorem B7209071 : Blo 1248442 7209071 := bstep (se 1 (by rfl) ⟨5406803, by rfl⟩ : syracuseStep 7209071 = 10813607) B10813607
theorem B4806047 : Blo 1248442 4806047 := bstep (se 1 (by rfl) ⟨3604535, by rfl⟩ : syracuseStep 4806047 = 7209071) B7209071
theorem B3204031 : Blo 1248442 3204031 := bstep (se 1 (by rfl) ⟨2403023, by rfl⟩ : syracuseStep 3204031 = 4806047) B4806047
theorem B4272041 : Blo 1248442 4272041 := bstep (se 2 (by rfl) ⟨1602015, by rfl⟩ : syracuseStep 4272041 = 3204031) B3204031
theorem B2848027 : Blo 1248442 2848027 := bstep (se 1 (by rfl) ⟨2136020, by rfl⟩ : syracuseStep 2848027 = 4272041) B4272041
theorem B3797369 : Blo 1248442 3797369 := bstep (se 2 (by rfl) ⟨1424013, by rfl⟩ : syracuseStep 3797369 = 2848027) B2848027
theorem B2531579 : Blo 1248442 2531579 := bstep (se 1 (by rfl) ⟨1898684, by rfl⟩ : syracuseStep 2531579 = 3797369) B3797369
theorem B6750877 : Blo 1248442 6750877 := bstep (se 3 (by rfl) ⟨1265789, by rfl⟩ : syracuseStep 6750877 = 2531579) B2531579
theorem B9001169 : Blo 1248442 9001169 := bstep (se 2 (by rfl) ⟨3375438, by rfl⟩ : syracuseStep 9001169 = 6750877) B6750877
theorem B6000779 : Blo 1248442 6000779 := bstep (se 1 (by rfl) ⟨4500584, by rfl⟩ : syracuseStep 6000779 = 9001169) B9001169
theorem B4000519 : Blo 1248442 4000519 := bstep (se 1 (by rfl) ⟨3000389, by rfl⟩ : syracuseStep 4000519 = 6000779) B6000779
theorem B5334025 : Blo 1248442 5334025 := bstep (se 2 (by rfl) ⟨2000259, by rfl⟩ : syracuseStep 5334025 = 4000519) B4000519
theorem B7112033 : Blo 1248442 7112033 := bstep (se 2 (by rfl) ⟨2667012, by rfl⟩ : syracuseStep 7112033 = 5334025) B5334025
theorem B4741355 : Blo 1248442 4741355 := bstep (se 1 (by rfl) ⟨3556016, by rfl⟩ : syracuseStep 4741355 = 7112033) B7112033
theorem B3160903 : Blo 1248442 3160903 := bstep (se 1 (by rfl) ⟨2370677, by rfl⟩ : syracuseStep 3160903 = 4741355) B4741355
theorem B4214537 : Blo 1248442 4214537 := bstep (se 2 (by rfl) ⟨1580451, by rfl⟩ : syracuseStep 4214537 = 3160903) B3160903
theorem B2809691 : Blo 1248442 2809691 := bstep (se 1 (by rfl) ⟨2107268, by rfl⟩ : syracuseStep 2809691 = 4214537) B4214537
theorem B1873127 : Blo 1248442 1873127 := bstep (se 1 (by rfl) ⟨1404845, by rfl⟩ : syracuseStep 1873127 = 2809691) B2809691
theorem B1248751 : Blo 1248442 1248751 := bstep (se 1 (by rfl) ⟨936563, by rfl⟩ : syracuseStep 1248751 = 1873127) B1873127

theorem C0 (j : ℕ) (h1 : 312110 ≤ j) (h2 : j ≤ 312609) : Blo 1248442 (4 * j + 3) := by
  interval_cases j
  · exact B1248443
  · exact B1248447
  · exact B1248451
  · exact B1248455
  · exact B1248459
  · exact B1248463
  · exact B1248467
  · exact B1248471
  · exact B1248475
  · exact B1248479
  · exact B1248483
  · exact B1248487
  · exact B1248491
  · exact B1248495
  · exact B1248499
  · exact B1248503
  · exact B1248507
  · exact B1248511
  · exact B1248515
  · exact B1248519
  · exact B1248523
  · exact B1248527
  · exact B1248531
  · exact B1248535
  · exact B1248539
  · exact B1248543
  · exact B1248547
  · exact B1248551
  · exact B1248555
  · exact B1248559
  · exact B1248563
  · exact B1248567
  · exact B1248571
  · exact B1248575
  · exact B1248579
  · exact B1248583
  · exact B1248587
  · exact B1248591
  · exact B1248595
  · exact B1248599
  · exact B1248603
  · exact B1248607
  · exact B1248611
  · exact B1248615
  · exact B1248619
  · exact B1248623
  · exact B1248627
  · exact B1248631
  · exact B1248635
  · exact B1248639
  · exact B1248643
  · exact B1248647
  · exact B1248651
  · exact B1248655
  · exact B1248659
  · exact B1248663
  · exact B1248667
  · exact B1248671
  · exact B1248675
  · exact B1248679
  · exact B1248683
  · exact B1248687
  · exact B1248691
  · exact B1248695
  · exact B1248699
  · exact B1248703
  · exact B1248707
  · exact B1248711
  · exact B1248715
  · exact B1248719
  · exact B1248723
  · exact B1248727
  · exact B1248731
  · exact B1248735
  · exact B1248739
  · exact B1248743
  · exact B1248747
  · exact B1248751
  · exact B1248755
  · exact B1248759
  · exact B1248763
  · exact B1248767
  · exact B1248771
  · exact B1248775
  · exact B1248779
  · exact B1248783
  · exact B1248787
  · exact B1248791
  · exact B1248795
  · exact B1248799
  · exact B1248803
  · exact B1248807
  · exact B1248811
  · exact B1248815
  · exact B1248819
  · exact B1248823
  · exact B1248827
  · exact B1248831
  · exact B1248835
  · exact B1248839
  · exact B1248843
  · exact B1248847
  · exact B1248851
  · exact B1248855
  · exact B1248859
  · exact B1248863
  · exact B1248867
  · exact B1248871
  · exact B1248875
  · exact B1248879
  · exact B1248883
  · exact B1248887
  · exact B1248891
  · exact B1248895
  · exact B1248899
  · exact B1248903
  · exact B1248907
  · exact B1248911
  · exact B1248915
  · exact B1248919
  · exact B1248923
  · exact B1248927
  · exact B1248931
  · exact B1248935
  · exact B1248939
  · exact B1248943
  · exact B1248947
  · exact B1248951
  · exact B1248955
  · exact B1248959
  · exact B1248963
  · exact B1248967
  · exact B1248971
  · exact B1248975
  · exact B1248979
  · exact B1248983
  · exact B1248987
  · exact B1248991
  · exact B1248995
  · exact B1248999
  · exact B1249003
  · exact B1249007
  · exact B1249011
  · exact B1249015
  · exact B1249019
  · exact B1249023
  · exact B1249027
  · exact B1249031
  · exact B1249035
  · exact B1249039
  · exact B1249043
  · exact B1249047
  · exact B1249051
  · exact B1249055
  · exact B1249059
  · exact B1249063
  · exact B1249067
  · exact B1249071
  · exact B1249075
  · exact B1249079
  · exact B1249083
  · exact B1249087
  · exact B1249091
  · exact B1249095
  · exact B1249099
  · exact B1249103
  · exact B1249107
  · exact B1249111
  · exact B1249115
  · exact B1249119
  · exact B1249123
  · exact B1249127
  · exact B1249131
  · exact B1249135
  · exact B1249139
  · exact B1249143
  · exact B1249147
  · exact B1249151
  · exact B1249155
  · exact B1249159
  · exact B1249163
  · exact B1249167
  · exact B1249171
  · exact B1249175
  · exact B1249179
  · exact B1249183
  · exact B1249187
  · exact B1249191
  · exact B1249195
  · exact B1249199
  · exact B1249203
  · exact B1249207
  · exact B1249211
  · exact B1249215
  · exact B1249219
  · exact B1249223
  · exact B1249227
  · exact B1249231
  · exact B1249235
  · exact B1249239
  · exact B1249243
  · exact B1249247
  · exact B1249251
  · exact B1249255
  · exact B1249259
  · exact B1249263
  · exact B1249267
  · exact B1249271
  · exact B1249275
  · exact B1249279
  · exact B1249283
  · exact B1249287
  · exact B1249291
  · exact B1249295
  · exact B1249299
  · exact B1249303
  · exact B1249307
  · exact B1249311
  · exact B1249315
  · exact B1249319
  · exact B1249323
  · exact B1249327
  · exact B1249331
  · exact B1249335
  · exact B1249339
  · exact B1249343
  · exact B1249347
  · exact B1249351
  · exact B1249355
  · exact B1249359
  · exact B1249363
  · exact B1249367
  · exact B1249371
  · exact B1249375
  · exact B1249379
  · exact B1249383
  · exact B1249387
  · exact B1249391
  · exact B1249395
  · exact B1249399
  · exact B1249403
  · exact B1249407
  · exact B1249411
  · exact B1249415
  · exact B1249419
  · exact B1249423
  · exact B1249427
  · exact B1249431
  · exact B1249435
  · exact B1249439
  · exact B1249443
  · exact B1249447
  · exact B1249451
  · exact B1249455
  · exact B1249459
  · exact B1249463
  · exact B1249467
  · exact B1249471
  · exact B1249475
  · exact B1249479
  · exact B1249483
  · exact B1249487
  · exact B1249491
  · exact B1249495
  · exact B1249499
  · exact B1249503
  · exact B1249507
  · exact B1249511
  · exact B1249515
  · exact B1249519
  · exact B1249523
  · exact B1249527
  · exact B1249531
  · exact B1249535
  · exact B1249539
  · exact B1249543
  · exact B1249547
  · exact B1249551
  · exact B1249555
  · exact B1249559
  · exact B1249563
  · exact B1249567
  · exact B1249571
  · exact B1249575
  · exact B1249579
  · exact B1249583
  · exact B1249587
  · exact B1249591
  · exact B1249595
  · exact B1249599
  · exact B1249603
  · exact B1249607
  · exact B1249611
  · exact B1249615
  · exact B1249619
  · exact B1249623
  · exact B1249627
  · exact B1249631
  · exact B1249635
  · exact B1249639
  · exact B1249643
  · exact B1249647
  · exact B1249651
  · exact B1249655
  · exact B1249659
  · exact B1249663
  · exact B1249667
  · exact B1249671
  · exact B1249675
  · exact B1249679
  · exact B1249683
  · exact B1249687
  · exact B1249691
  · exact B1249695
  · exact B1249699
  · exact B1249703
  · exact B1249707
  · exact B1249711
  · exact B1249715
  · exact B1249719
  · exact B1249723
  · exact B1249727
  · exact B1249731
  · exact B1249735
  · exact B1249739
  · exact B1249743
  · exact B1249747
  · exact B1249751
  · exact B1249755
  · exact B1249759
  · exact B1249763
  · exact B1249767
  · exact B1249771
  · exact B1249775
  · exact B1249779
  · exact B1249783
  · exact B1249787
  · exact B1249791
  · exact B1249795
  · exact B1249799
  · exact B1249803
  · exact B1249807
  · exact B1249811
  · exact B1249815
  · exact B1249819
  · exact B1249823
  · exact B1249827
  · exact B1249831
  · exact B1249835
  · exact B1249839
  · exact B1249843
  · exact B1249847
  · exact B1249851
  · exact B1249855
  · exact B1249859
  · exact B1249863
  · exact B1249867
  · exact B1249871
  · exact B1249875
  · exact B1249879
  · exact B1249883
  · exact B1249887
  · exact B1249891
  · exact B1249895
  · exact B1249899
  · exact B1249903
  · exact B1249907
  · exact B1249911
  · exact B1249915
  · exact B1249919
  · exact B1249923
  · exact B1249927
  · exact B1249931
  · exact B1249935
  · exact B1249939
  · exact B1249943
  · exact B1249947
  · exact B1249951
  · exact B1249955
  · exact B1249959
  · exact B1249963
  · exact B1249967
  · exact B1249971
  · exact B1249975
  · exact B1249979
  · exact B1249983
  · exact B1249987
  · exact B1249991
  · exact B1249995
  · exact B1249999
  · exact B1250003
  · exact B1250007
  · exact B1250011
  · exact B1250015
  · exact B1250019
  · exact B1250023
  · exact B1250027
  · exact B1250031
  · exact B1250035
  · exact B1250039
  · exact B1250043
  · exact B1250047
  · exact B1250051
  · exact B1250055
  · exact B1250059
  · exact B1250063
  · exact B1250067
  · exact B1250071
  · exact B1250075
  · exact B1250079
  · exact B1250083
  · exact B1250087
  · exact B1250091
  · exact B1250095
  · exact B1250099
  · exact B1250103
  · exact B1250107
  · exact B1250111
  · exact B1250115
  · exact B1250119
  · exact B1250123
  · exact B1250127
  · exact B1250131
  · exact B1250135
  · exact B1250139
  · exact B1250143
  · exact B1250147
  · exact B1250151
  · exact B1250155
  · exact B1250159
  · exact B1250163
  · exact B1250167
  · exact B1250171
  · exact B1250175
  · exact B1250179
  · exact B1250183
  · exact B1250187
  · exact B1250191
  · exact B1250195
  · exact B1250199
  · exact B1250203
  · exact B1250207
  · exact B1250211
  · exact B1250215
  · exact B1250219
  · exact B1250223
  · exact B1250227
  · exact B1250231
  · exact B1250235
  · exact B1250239
  · exact B1250243
  · exact B1250247
  · exact B1250251
  · exact B1250255
  · exact B1250259
  · exact B1250263
  · exact B1250267
  · exact B1250271
  · exact B1250275
  · exact B1250279
  · exact B1250283
  · exact B1250287
  · exact B1250291
  · exact B1250295
  · exact B1250299
  · exact B1250303
  · exact B1250307
  · exact B1250311
  · exact B1250315
  · exact B1250319
  · exact B1250323
  · exact B1250327
  · exact B1250331
  · exact B1250335
  · exact B1250339
  · exact B1250343
  · exact B1250347
  · exact B1250351
  · exact B1250355
  · exact B1250359
  · exact B1250363
  · exact B1250367
  · exact B1250371
  · exact B1250375
  · exact B1250379
  · exact B1250383
  · exact B1250387
  · exact B1250391
  · exact B1250395
  · exact B1250399
  · exact B1250403
  · exact B1250407
  · exact B1250411
  · exact B1250415
  · exact B1250419
  · exact B1250423
  · exact B1250427
  · exact B1250431
  · exact B1250435
  · exact B1250439

theorem solution (m : ℕ) (hlo : 1248442 ≤ m) (hhi : m ≤ 1250442) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 312110 ≤ j := by omega
    have hj2 : j ≤ 312609 := by omega
    have hb : Blo 1248442 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
