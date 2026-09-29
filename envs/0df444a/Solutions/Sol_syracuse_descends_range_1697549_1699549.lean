-- Prove2me | solution 1 for syracuse_descends_range_1697549_1699549
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:25:13.536337+00:00
-- url     : https://prove2.me/submissions/cbfac7ba-8bff-485f-ae51-82090ca38d71

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


theorem B2547725 : Blo 1697549 2547725 := bbase (se 3 (by rfl) ⟨477698, by rfl⟩ : syracuseStep 2547725 = 955397) (by norm_num)
theorem B5734421 : Blo 1697549 5734421 := bbase (se 6 (by rfl) ⟨134400, by rfl⟩ : syracuseStep 5734421 = 268801) (by norm_num)
theorem B2547749 : Blo 1697549 2547749 := bbase (se 4 (by rfl) ⟨238851, by rfl⟩ : syracuseStep 2547749 = 477703) (by norm_num)
theorem B2547773 : Blo 1697549 2547773 := bbase (se 3 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 2547773 = 955415) (by norm_num)
theorem B3268669 : Blo 1697549 3268669 := bbase (se 3 (by rfl) ⟨612875, by rfl⟩ : syracuseStep 3268669 = 1225751) (by norm_num)
theorem B4358213 : Blo 1697549 4358213 := bbase (se 4 (by rfl) ⟨408582, by rfl⟩ : syracuseStep 4358213 = 817165) (by norm_num)
theorem B4300877 : Blo 1697549 4300877 := bbase (se 3 (by rfl) ⟨806414, by rfl⟩ : syracuseStep 4300877 = 1612829) (by norm_num)
theorem B2179153 : Blo 1697549 2179153 := bbase (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) (by norm_num)
theorem B2547797 : Blo 1697549 2547797 := bbase (se 8 (by rfl) ⟨14928, by rfl⟩ : syracuseStep 2547797 = 29857) (by norm_num)
theorem B2867285 : Blo 1697549 2867285 := bbase (se 8 (by rfl) ⟨16800, by rfl⟩ : syracuseStep 2867285 = 33601) (by norm_num)
theorem B2547821 : Blo 1697549 2547821 := bbase (se 3 (by rfl) ⟨477716, by rfl⟩ : syracuseStep 2547821 = 955433) (by norm_num)
theorem B2547845 : Blo 1697549 2547845 := bbase (se 4 (by rfl) ⟨238860, by rfl⟩ : syracuseStep 2547845 = 477721) (by norm_num)
theorem B2547869 : Blo 1697549 2547869 := bbase (se 3 (by rfl) ⟨477725, by rfl⟩ : syracuseStep 2547869 = 955451) (by norm_num)
theorem B8159413 : Blo 1697549 8159413 := bbase (se 5 (by rfl) ⟨382472, by rfl⟩ : syracuseStep 8159413 = 764945) (by norm_num)
theorem B2547893 : Blo 1697549 2547893 := bbase (se 5 (by rfl) ⟨119432, by rfl⟩ : syracuseStep 2547893 = 238865) (by norm_num)
theorem B2547917 : Blo 1697549 2547917 := bbase (se 3 (by rfl) ⟨477734, by rfl⟩ : syracuseStep 2547917 = 955469) (by norm_num)
theorem B2867413 : Blo 1697549 2867413 := bbase (se 7 (by rfl) ⟨33602, by rfl⟩ : syracuseStep 2867413 = 67205) (by norm_num)
theorem B2547941 : Blo 1697549 2547941 := bbase (se 4 (by rfl) ⟨238869, by rfl⟩ : syracuseStep 2547941 = 477739) (by norm_num)
theorem B4079861 : Blo 1697549 4079861 := bbase (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) (by norm_num)
theorem B2547965 : Blo 1697549 2547965 := bbase (se 3 (by rfl) ⟨477743, by rfl⟩ : syracuseStep 2547965 = 955487) (by norm_num)
theorem B2547989 : Blo 1697549 2547989 := bbase (se 6 (by rfl) ⟨59718, by rfl⟩ : syracuseStep 2547989 = 119437) (by norm_num)
theorem B4079909 : Blo 1697549 4079909 := bbase (se 4 (by rfl) ⟨382491, by rfl⟩ : syracuseStep 4079909 = 764983) (by norm_num)
theorem B6447397 : Blo 1697549 6447397 := bbase (se 4 (by rfl) ⟨604443, by rfl⟩ : syracuseStep 6447397 = 1208887) (by norm_num)
theorem B4079917 : Blo 1697549 4079917 := bbase (se 3 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 4079917 = 1529969) (by norm_num)
theorem B2548013 : Blo 1697549 2548013 := bbase (se 3 (by rfl) ⟨477752, by rfl⟩ : syracuseStep 2548013 = 955505) (by norm_num)
theorem B2867501 : Blo 1697549 2867501 := bbase (se 3 (by rfl) ⟨537656, by rfl⟩ : syracuseStep 2867501 = 1075313) (by norm_num)
theorem B2548037 : Blo 1697549 2548037 := bbase (se 4 (by rfl) ⟨238878, by rfl⟩ : syracuseStep 2548037 = 477757) (by norm_num)
theorem B235266389 : Blo 1697549 235266389 := bbase (se 10 (by rfl) ⟨344628, by rfl⟩ : syracuseStep 235266389 = 689257) (by norm_num)
theorem B2548061 : Blo 1697549 2548061 := bbase (se 3 (by rfl) ⟨477761, by rfl⟩ : syracuseStep 2548061 = 955523) (by norm_num)
theorem B2548085 : Blo 1697549 2548085 := bbase (se 5 (by rfl) ⟨119441, by rfl⟩ : syracuseStep 2548085 = 238883) (by norm_num)
theorem B2548109 : Blo 1697549 2548109 := bbase (se 3 (by rfl) ⟨477770, by rfl⟩ : syracuseStep 2548109 = 955541) (by norm_num)
theorem B2417045 : Blo 1697549 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B7258517 : Blo 1697549 7258517 := bbase (se 6 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 7258517 = 340243) (by norm_num)
theorem B2548133 : Blo 1697549 2548133 := bbase (se 4 (by rfl) ⟨238887, by rfl⟩ : syracuseStep 2548133 = 477775) (by norm_num)
theorem B4301221 : Blo 1697549 4301221 := bbase (se 4 (by rfl) ⟨403239, by rfl⟩ : syracuseStep 4301221 = 806479) (by norm_num)
theorem B2867629 : Blo 1697549 2867629 := bbase (se 3 (by rfl) ⟨537680, by rfl⟩ : syracuseStep 2867629 = 1075361) (by norm_num)
theorem B8602037 : Blo 1697549 8602037 := bbase (se 5 (by rfl) ⟨403220, by rfl⟩ : syracuseStep 8602037 = 806441) (by norm_num)
theorem B2548157 : Blo 1697549 2548157 := bbase (se 3 (by rfl) ⟨477779, by rfl⟩ : syracuseStep 2548157 = 955559) (by norm_num)
theorem B5734853 : Blo 1697549 5734853 := bbase (se 4 (by rfl) ⟨537642, by rfl⟩ : syracuseStep 5734853 = 1075285) (by norm_num)
theorem B2548181 : Blo 1697549 2548181 := bbase (se 7 (by rfl) ⟨29861, by rfl⟩ : syracuseStep 2548181 = 59723) (by norm_num)
theorem B2548205 : Blo 1697549 2548205 := bbase (se 3 (by rfl) ⟨477788, by rfl⟩ : syracuseStep 2548205 = 955577) (by norm_num)
theorem B3629549 : Blo 1697549 3629549 := bbase (se 3 (by rfl) ⟨680540, by rfl⟩ : syracuseStep 3629549 = 1361081) (by norm_num)
theorem B2548229 : Blo 1697549 2548229 := bbase (se 4 (by rfl) ⟨238896, by rfl⟩ : syracuseStep 2548229 = 477793) (by norm_num)
theorem B2867717 : Blo 1697549 2867717 := bbase (se 4 (by rfl) ⟨268848, by rfl⟩ : syracuseStep 2867717 = 537697) (by norm_num)
theorem B6291989 : Blo 1697549 6291989 := bbase (se 6 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 6291989 = 294937) (by norm_num)
theorem B4301333 : Blo 1697549 4301333 := bbase (se 6 (by rfl) ⟨100812, by rfl⟩ : syracuseStep 4301333 = 201625) (by norm_num)
theorem B2548253 : Blo 1697549 2548253 := bbase (se 3 (by rfl) ⟨477797, by rfl⟩ : syracuseStep 2548253 = 955595) (by norm_num)
theorem B2548277 : Blo 1697549 2548277 := bbase (se 5 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 2548277 = 238901) (by norm_num)
theorem B2720317 : Blo 1697549 2720317 := bbase (se 3 (by rfl) ⟨510059, by rfl⟩ : syracuseStep 2720317 = 1020119) (by norm_num)
theorem B2548301 : Blo 1697549 2548301 := bbase (se 3 (by rfl) ⟨477806, by rfl⟩ : syracuseStep 2548301 = 955613) (by norm_num)
theorem B2040401 : Blo 1697549 2040401 := bbase (se 2 (by rfl) ⟨765150, by rfl⟩ : syracuseStep 2040401 = 1530301) (by norm_num)
theorem B6447701 : Blo 1697549 6447701 := bbase (se 8 (by rfl) ⟨37779, by rfl⟩ : syracuseStep 6447701 = 75559) (by norm_num)
theorem B2548325 : Blo 1697549 2548325 := bbase (se 4 (by rfl) ⟨238905, by rfl⟩ : syracuseStep 2548325 = 477811) (by norm_num)
theorem B2548349 : Blo 1697549 2548349 := bbase (se 3 (by rfl) ⟨477815, by rfl⟩ : syracuseStep 2548349 = 955631) (by norm_num)
theorem B5808773 : Blo 1697549 5808773 := bbase (se 4 (by rfl) ⟨544572, by rfl⟩ : syracuseStep 5808773 = 1089145) (by norm_num)
theorem B2867845 : Blo 1697549 2867845 := bbase (se 4 (by rfl) ⟨268860, by rfl⟩ : syracuseStep 2867845 = 537721) (by norm_num)
theorem B2548373 : Blo 1697549 2548373 := bbase (se 6 (by rfl) ⟨59727, by rfl⟩ : syracuseStep 2548373 = 119455) (by norm_num)
theorem B2548397 : Blo 1697549 2548397 := bbase (se 3 (by rfl) ⟨477824, by rfl⟩ : syracuseStep 2548397 = 955649) (by norm_num)
theorem B1721021 : Blo 1697549 1721021 := bbase (se 3 (by rfl) ⟨322691, by rfl⟩ : syracuseStep 1721021 = 645383) (by norm_num)
theorem B2548421 : Blo 1697549 2548421 := bbase (se 4 (by rfl) ⟨238914, by rfl⟩ : syracuseStep 2548421 = 477829) (by norm_num)
theorem B4301525 : Blo 1697549 4301525 := bbase (se 7 (by rfl) ⟨50408, by rfl⟩ : syracuseStep 4301525 = 100817) (by norm_num)
theorem B2548445 : Blo 1697549 2548445 := bbase (se 3 (by rfl) ⟨477833, by rfl⟩ : syracuseStep 2548445 = 955667) (by norm_num)
theorem B2867933 : Blo 1697549 2867933 := bbase (se 3 (by rfl) ⟨537737, by rfl⟩ : syracuseStep 2867933 = 1075475) (by norm_num)
theorem B2548469 : Blo 1697549 2548469 := bbase (se 5 (by rfl) ⟨119459, by rfl⟩ : syracuseStep 2548469 = 238919) (by norm_num)
theorem B2548493 : Blo 1697549 2548493 := bbase (se 3 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 2548493 = 955685) (by norm_num)
theorem B2548517 : Blo 1697549 2548517 := bbase (se 4 (by rfl) ⟨238923, by rfl⟩ : syracuseStep 2548517 = 477847) (by norm_num)
theorem B2548541 : Blo 1697549 2548541 := bbase (se 3 (by rfl) ⟨477851, by rfl⟩ : syracuseStep 2548541 = 955703) (by norm_num)
theorem B8594261 : Blo 1697549 8594261 := bbase (se 9 (by rfl) ⟨25178, by rfl⟩ : syracuseStep 8594261 = 50357) (by norm_num)
theorem B11027285 : Blo 1697549 11027285 := bbase (se 9 (by rfl) ⟨32306, by rfl⟩ : syracuseStep 11027285 = 64613) (by norm_num)
theorem B2040661 : Blo 1697549 2040661 := bbase (se 9 (by rfl) ⟨5978, by rfl⟩ : syracuseStep 2040661 = 11957) (by norm_num)
theorem B2548565 : Blo 1697549 2548565 := bbase (se 9 (by rfl) ⟨7466, by rfl⟩ : syracuseStep 2548565 = 14933) (by norm_num)
theorem B2548589 : Blo 1697549 2548589 := bbase (se 3 (by rfl) ⟨477860, by rfl⟩ : syracuseStep 2548589 = 955721) (by norm_num)
theorem B5735285 : Blo 1697549 5735285 := bbase (se 5 (by rfl) ⟨268841, by rfl⟩ : syracuseStep 5735285 = 537683) (by norm_num)
theorem B4834181 : Blo 1697549 4834181 := bbase (se 4 (by rfl) ⟨453204, by rfl⟩ : syracuseStep 4834181 = 906409) (by norm_num)
theorem B3441541 : Blo 1697549 3441541 := bbase (se 4 (by rfl) ⟨322644, by rfl⟩ : syracuseStep 3441541 = 645289) (by norm_num)
theorem B2040709 : Blo 1697549 2040709 := bbase (se 4 (by rfl) ⟨191316, by rfl⟩ : syracuseStep 2040709 = 382633) (by norm_num)
theorem B2548613 : Blo 1697549 2548613 := bbase (se 4 (by rfl) ⟨238932, by rfl⟩ : syracuseStep 2548613 = 477865) (by norm_num)
theorem B2548637 : Blo 1697549 2548637 := bbase (se 3 (by rfl) ⟨477869, by rfl⟩ : syracuseStep 2548637 = 955739) (by norm_num)
theorem B2548661 : Blo 1697549 2548661 := bbase (se 5 (by rfl) ⟨119468, by rfl⟩ : syracuseStep 2548661 = 238937) (by norm_num)
theorem B2548685 : Blo 1697549 2548685 := bbase (se 3 (by rfl) ⟨477878, by rfl⟩ : syracuseStep 2548685 = 955757) (by norm_num)
theorem B2548709 : Blo 1697549 2548709 := bbase (se 4 (by rfl) ⟨238941, by rfl⟩ : syracuseStep 2548709 = 477883) (by norm_num)
theorem B2327549 : Blo 1697549 2327549 := bbase (se 3 (by rfl) ⟨436415, by rfl⟩ : syracuseStep 2327549 = 872831) (by norm_num)
theorem B2548733 : Blo 1697549 2548733 := bbase (se 3 (by rfl) ⟨477887, by rfl⟩ : syracuseStep 2548733 = 955775) (by norm_num)
theorem B1909777 : Blo 1697549 1909777 := bbase (se 2 (by rfl) ⟨716166, by rfl⟩ : syracuseStep 1909777 = 1432333) (by norm_num)
theorem B2548757 : Blo 1697549 2548757 := bbase (se 6 (by rfl) ⟨59736, by rfl⟩ : syracuseStep 2548757 = 119473) (by norm_num)
theorem B2548781 : Blo 1697549 2548781 := bbase (se 3 (by rfl) ⟨477896, by rfl⟩ : syracuseStep 2548781 = 955793) (by norm_num)
theorem B4301869 : Blo 1697549 4301869 := bbase (se 3 (by rfl) ⟨806600, by rfl⟩ : syracuseStep 4301869 = 1613201) (by norm_num)
theorem B1909813 : Blo 1697549 1909813 := bbase (se 5 (by rfl) ⟨89522, by rfl⟩ : syracuseStep 1909813 = 179045) (by norm_num)
theorem B4138037 : Blo 1697549 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B2548805 : Blo 1697549 2548805 := bbase (se 4 (by rfl) ⟨238950, by rfl⟩ : syracuseStep 2548805 = 477901) (by norm_num)
theorem B1909849 : Blo 1697549 1909849 := bbase (se 2 (by rfl) ⟨716193, by rfl⟩ : syracuseStep 1909849 = 1432387) (by norm_num)
theorem B2548829 : Blo 1697549 2548829 := bbase (se 3 (by rfl) ⟨477905, by rfl⟩ : syracuseStep 2548829 = 955811) (by norm_num)
theorem B2548853 : Blo 1697549 2548853 := bbase (se 5 (by rfl) ⟨119477, by rfl⟩ : syracuseStep 2548853 = 238955) (by norm_num)
theorem B1909885 : Blo 1697549 1909885 := bbase (se 3 (by rfl) ⟨358103, by rfl⟩ : syracuseStep 1909885 = 716207) (by norm_num)
theorem B2417797 : Blo 1697549 2417797 := bbase (se 4 (by rfl) ⟨226668, by rfl⟩ : syracuseStep 2417797 = 453337) (by norm_num)
theorem B2548877 : Blo 1697549 2548877 := bbase (se 3 (by rfl) ⟨477914, by rfl⟩ : syracuseStep 2548877 = 955829) (by norm_num)
theorem B4301981 : Blo 1697549 4301981 := bbase (se 3 (by rfl) ⟨806621, by rfl⟩ : syracuseStep 4301981 = 1613243) (by norm_num)
theorem B1909921 : Blo 1697549 1909921 := bbase (se 2 (by rfl) ⟨716220, by rfl⟩ : syracuseStep 1909921 = 1432441) (by norm_num)
theorem B2548901 : Blo 1697549 2548901 := bbase (se 4 (by rfl) ⟨238959, by rfl⟩ : syracuseStep 2548901 = 477919) (by norm_num)
theorem B6120629 : Blo 1697549 6120629 := bbase (se 5 (by rfl) ⟨286904, by rfl⟩ : syracuseStep 6120629 = 573809) (by norm_num)
theorem B2548925 : Blo 1697549 2548925 := bbase (se 3 (by rfl) ⟨477923, by rfl⟩ : syracuseStep 2548925 = 955847) (by norm_num)
theorem B1909957 : Blo 1697549 1909957 := bbase (se 4 (by rfl) ⟨179058, by rfl⟩ : syracuseStep 1909957 = 358117) (by norm_num)
theorem B2548949 : Blo 1697549 2548949 := bbase (se 7 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 2548949 = 59741) (by norm_num)
theorem B1721569 : Blo 1697549 1721569 := bbase (se 2 (by rfl) ⟨645588, by rfl⟩ : syracuseStep 1721569 = 1291177) (by norm_num)
theorem B1909993 : Blo 1697549 1909993 := bbase (se 2 (by rfl) ⟨716247, by rfl⟩ : syracuseStep 1909993 = 1432495) (by norm_num)
theorem B2548973 : Blo 1697549 2548973 := bbase (se 3 (by rfl) ⟨477932, by rfl⟩ : syracuseStep 2548973 = 955865) (by norm_num)
theorem B2548997 : Blo 1697549 2548997 := bbase (se 4 (by rfl) ⟨238968, by rfl⟩ : syracuseStep 2548997 = 477937) (by norm_num)
theorem B1910029 : Blo 1697549 1910029 := bbase (se 3 (by rfl) ⟨358130, by rfl⟩ : syracuseStep 1910029 = 716261) (by norm_num)
theorem B4080917 : Blo 1697549 4080917 := bbase (se 6 (by rfl) ⟨95646, by rfl⟩ : syracuseStep 4080917 = 191293) (by norm_num)
theorem B2549021 : Blo 1697549 2549021 := bbase (se 3 (by rfl) ⟨477941, by rfl⟩ : syracuseStep 2549021 = 955883) (by norm_num)
theorem B5735717 : Blo 1697549 5735717 := bbase (se 4 (by rfl) ⟨537723, by rfl⟩ : syracuseStep 5735717 = 1075447) (by norm_num)
theorem B1910065 : Blo 1697549 1910065 := bbase (se 2 (by rfl) ⟨716274, by rfl⟩ : syracuseStep 1910065 = 1432549) (by norm_num)
theorem B2549045 : Blo 1697549 2549045 := bbase (se 5 (by rfl) ⟨119486, by rfl⟩ : syracuseStep 2549045 = 238973) (by norm_num)
theorem B2549069 : Blo 1697549 2549069 := bbase (se 3 (by rfl) ⟨477950, by rfl⟩ : syracuseStep 2549069 = 955901) (by norm_num)
theorem B1910101 : Blo 1697549 1910101 := bbase (se 12 (by rfl) ⟨699, by rfl⟩ : syracuseStep 1910101 = 1399) (by norm_num)
theorem B2549093 : Blo 1697549 2549093 := bbase (se 4 (by rfl) ⟨238977, by rfl⟩ : syracuseStep 2549093 = 477955) (by norm_num)
theorem B1910137 : Blo 1697549 1910137 := bbase (se 2 (by rfl) ⟨716301, by rfl⟩ : syracuseStep 1910137 = 1432603) (by norm_num)
theorem B2549117 : Blo 1697549 2549117 := bbase (se 3 (by rfl) ⟨477959, by rfl⟩ : syracuseStep 2549117 = 955919) (by norm_num)
theorem B2549141 : Blo 1697549 2549141 := bbase (se 6 (by rfl) ⟨59745, by rfl⟩ : syracuseStep 2549141 = 119491) (by norm_num)
theorem B5670293 : Blo 1697549 5670293 := bbase (se 6 (by rfl) ⟨132897, by rfl⟩ : syracuseStep 5670293 = 265795) (by norm_num)
theorem B1910173 : Blo 1697549 1910173 := bbase (se 3 (by rfl) ⟨358157, by rfl⟩ : syracuseStep 1910173 = 716315) (by norm_num)
theorem B5162405 : Blo 1697549 5162405 := bbase (se 4 (by rfl) ⟨483975, by rfl⟩ : syracuseStep 5162405 = 967951) (by norm_num)
theorem B2549165 : Blo 1697549 2549165 := bbase (se 3 (by rfl) ⟨477968, by rfl⟩ : syracuseStep 2549165 = 955937) (by norm_num)
theorem B1910209 : Blo 1697549 1910209 := bbase (se 2 (by rfl) ⟨716328, by rfl⟩ : syracuseStep 1910209 = 1432657) (by norm_num)
theorem B2549189 : Blo 1697549 2549189 := bbase (se 4 (by rfl) ⟨238986, by rfl⟩ : syracuseStep 2549189 = 477973) (by norm_num)
theorem B4081109 : Blo 1697549 4081109 := bbase (se 7 (by rfl) ⟨47825, by rfl⟩ : syracuseStep 4081109 = 95651) (by norm_num)
theorem B2549213 : Blo 1697549 2549213 := bbase (se 3 (by rfl) ⟨477977, by rfl⟩ : syracuseStep 2549213 = 955955) (by norm_num)
theorem B1910245 : Blo 1697549 1910245 := bbase (se 4 (by rfl) ⟨179085, by rfl⟩ : syracuseStep 1910245 = 358171) (by norm_num)
theorem B2549237 : Blo 1697549 2549237 := bbase (se 5 (by rfl) ⟨119495, by rfl⟩ : syracuseStep 2549237 = 238991) (by norm_num)
theorem B1910281 : Blo 1697549 1910281 := bbase (se 2 (by rfl) ⟨716355, by rfl⟩ : syracuseStep 1910281 = 1432711) (by norm_num)
theorem B2549261 : Blo 1697549 2549261 := bbase (se 3 (by rfl) ⟨477986, by rfl⟩ : syracuseStep 2549261 = 955973) (by norm_num)
theorem B2041381 : Blo 1697549 2041381 := bbase (se 4 (by rfl) ⟨191379, by rfl⟩ : syracuseStep 2041381 = 382759) (by norm_num)
theorem B2549285 : Blo 1697549 2549285 := bbase (se 4 (by rfl) ⟨238995, by rfl⟩ : syracuseStep 2549285 = 477991) (by norm_num)
theorem B1910317 : Blo 1697549 1910317 := bbase (se 3 (by rfl) ⟨358184, by rfl⟩ : syracuseStep 1910317 = 716369) (by norm_num)
theorem B2549309 : Blo 1697549 2549309 := bbase (se 3 (by rfl) ⟨477995, by rfl⟩ : syracuseStep 2549309 = 955991) (by norm_num)
theorem B1721929 : Blo 1697549 1721929 := bbase (se 2 (by rfl) ⟨645723, by rfl⟩ : syracuseStep 1721929 = 1291447) (by norm_num)
theorem B1910353 : Blo 1697549 1910353 := bbase (se 2 (by rfl) ⟨716382, by rfl⟩ : syracuseStep 1910353 = 1432765) (by norm_num)
theorem B1910389 : Blo 1697549 1910389 := bbase (se 5 (by rfl) ⟨89549, by rfl⟩ : syracuseStep 1910389 = 179099) (by norm_num)
theorem B1910425 : Blo 1697549 1910425 := bbase (se 2 (by rfl) ⟨716409, by rfl⟩ : syracuseStep 1910425 = 1432819) (by norm_num)
theorem B2582189 : Blo 1697549 2582189 := bbase (se 3 (by rfl) ⟨484160, by rfl⟩ : syracuseStep 2582189 = 968321) (by norm_num)
theorem B1910461 : Blo 1697549 1910461 := bbase (se 3 (by rfl) ⟨358211, by rfl⟩ : syracuseStep 1910461 = 716423) (by norm_num)
theorem B8603333 : Blo 1697549 8603333 := bbase (se 4 (by rfl) ⟨806562, by rfl⟩ : syracuseStep 8603333 = 1613125) (by norm_num)
theorem B1910497 : Blo 1697549 1910497 := bbase (se 2 (by rfl) ⟨716436, by rfl⟩ : syracuseStep 1910497 = 1432873) (by norm_num)
theorem B2721509 : Blo 1697549 2721509 := bbase (se 4 (by rfl) ⟨255141, by rfl⟩ : syracuseStep 2721509 = 510283) (by norm_num)
theorem B1910533 : Blo 1697549 1910533 := bbase (se 4 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 1910533 = 358225) (by norm_num)
theorem B1910569 : Blo 1697549 1910569 := bbase (se 2 (by rfl) ⟨716463, by rfl⟩ : syracuseStep 1910569 = 1432927) (by norm_num)
theorem B1910605 : Blo 1697549 1910605 := bbase (se 3 (by rfl) ⟨358238, by rfl⟩ : syracuseStep 1910605 = 716477) (by norm_num)
theorem B4835173 : Blo 1697549 4835173 := bbase (se 4 (by rfl) ⟨453297, by rfl⟩ : syracuseStep 4835173 = 906595) (by norm_num)
theorem B1910641 : Blo 1697549 1910641 := bbase (se 2 (by rfl) ⟨716490, by rfl⟩ : syracuseStep 1910641 = 1432981) (by norm_num)
theorem B1910677 : Blo 1697549 1910677 := bbase (se 6 (by rfl) ⟨44781, by rfl⟩ : syracuseStep 1910677 = 89563) (by norm_num)
theorem B2418589 : Blo 1697549 2418589 := bbase (se 3 (by rfl) ⟨453485, by rfl⟩ : syracuseStep 2418589 = 906971) (by norm_num)
theorem B2721701 : Blo 1697549 2721701 := bbase (se 4 (by rfl) ⟨255159, by rfl⟩ : syracuseStep 2721701 = 510319) (by norm_num)
theorem B1910713 : Blo 1697549 1910713 := bbase (se 2 (by rfl) ⟨716517, by rfl⟩ : syracuseStep 1910713 = 1433035) (by norm_num)
theorem B1910749 : Blo 1697549 1910749 := bbase (se 3 (by rfl) ⟨358265, by rfl⟩ : syracuseStep 1910749 = 716531) (by norm_num)
theorem B3819509 : Blo 1697549 3819509 := bbase (se 5 (by rfl) ⟨179039, by rfl⟩ : syracuseStep 3819509 = 358079) (by norm_num)
theorem B1910785 : Blo 1697549 1910785 := bbase (se 2 (by rfl) ⟨716544, by rfl⟩ : syracuseStep 1910785 = 1433089) (by norm_num)
theorem B1910821 : Blo 1697549 1910821 := bbase (se 4 (by rfl) ⟨179139, by rfl⟩ : syracuseStep 1910821 = 358279) (by norm_num)
theorem B3819581 : Blo 1697549 3819581 := bbase (se 3 (by rfl) ⟨716171, by rfl⟩ : syracuseStep 3819581 = 1432343) (by norm_num)
theorem B1910857 : Blo 1697549 1910857 := bbase (se 2 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 1910857 = 1433143) (by norm_num)
theorem B8595557 : Blo 1697549 8595557 := bbase (se 4 (by rfl) ⟨805833, by rfl⟩ : syracuseStep 8595557 = 1611667) (by norm_num)
theorem B1910893 : Blo 1697549 1910893 := bbase (se 3 (by rfl) ⟨358292, by rfl⟩ : syracuseStep 1910893 = 716585) (by norm_num)
theorem B3819653 : Blo 1697549 3819653 := bbase (se 4 (by rfl) ⟨358092, by rfl⟩ : syracuseStep 3819653 = 716185) (by norm_num)
theorem B1910929 : Blo 1697549 1910929 := bbase (se 2 (by rfl) ⟨716598, by rfl⟩ : syracuseStep 1910929 = 1433197) (by norm_num)
theorem B1910965 : Blo 1697549 1910965 := bbase (se 5 (by rfl) ⟨89576, by rfl⟩ : syracuseStep 1910965 = 179153) (by norm_num)
theorem B2148545 : Blo 1697549 2148545 := bbase (se 2 (by rfl) ⟨805704, by rfl⟩ : syracuseStep 2148545 = 1611409) (by norm_num)
theorem B3819725 : Blo 1697549 3819725 := bbase (se 3 (by rfl) ⟨716198, by rfl⟩ : syracuseStep 3819725 = 1432397) (by norm_num)
theorem B1911001 : Blo 1697549 1911001 := bbase (se 2 (by rfl) ⟨716625, by rfl⟩ : syracuseStep 1911001 = 1433251) (by norm_num)
theorem B2418925 : Blo 1697549 2418925 := bbase (se 3 (by rfl) ⟨453548, by rfl⟩ : syracuseStep 2418925 = 907097) (by norm_num)
theorem B7252213 : Blo 1697549 7252213 := bbase (se 5 (by rfl) ⟨339947, by rfl⟩ : syracuseStep 7252213 = 679895) (by norm_num)
theorem B2148601 : Blo 1697549 2148601 := bbase (se 2 (by rfl) ⟨805725, by rfl⟩ : syracuseStep 2148601 = 1611451) (by norm_num)
theorem B1911037 : Blo 1697549 1911037 := bbase (se 3 (by rfl) ⟨358319, by rfl⟩ : syracuseStep 1911037 = 716639) (by norm_num)
theorem B7252229 : Blo 1697549 7252229 := bbase (se 4 (by rfl) ⟨679896, by rfl⟩ : syracuseStep 7252229 = 1359793) (by norm_num)
theorem B3819797 : Blo 1697549 3819797 := bbase (se 6 (by rfl) ⟨89526, by rfl⟩ : syracuseStep 3819797 = 179053) (by norm_num)
theorem B1911073 : Blo 1697549 1911073 := bbase (se 2 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 1911073 = 1433305) (by norm_num)
theorem B2296117 : Blo 1697549 2296117 := bbase (se 5 (by rfl) ⟨107630, by rfl⟩ : syracuseStep 2296117 = 215261) (by norm_num)
theorem B12904757 : Blo 1697549 12904757 := bbase (se 5 (by rfl) ⟨604910, by rfl⟩ : syracuseStep 12904757 = 1209821) (by norm_num)
theorem B1911109 : Blo 1697549 1911109 := bbase (se 4 (by rfl) ⟨179166, by rfl⟩ : syracuseStep 1911109 = 358333) (by norm_num)
theorem B2148697 : Blo 1697549 2148697 := bbase (se 2 (by rfl) ⟨805761, by rfl⟩ : syracuseStep 2148697 = 1611523) (by norm_num)
theorem B3819869 : Blo 1697549 3819869 := bbase (se 3 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 3819869 = 1432451) (by norm_num)
theorem B1911145 : Blo 1697549 1911145 := bbase (se 2 (by rfl) ⟨716679, by rfl⟩ : syracuseStep 1911145 = 1433359) (by norm_num)
theorem B1911181 : Blo 1697549 1911181 := bbase (se 3 (by rfl) ⟨358346, by rfl⟩ : syracuseStep 1911181 = 716693) (by norm_num)
theorem B3819941 : Blo 1697549 3819941 := bbase (se 4 (by rfl) ⟨358119, by rfl⟩ : syracuseStep 3819941 = 716239) (by norm_num)
theorem B1911217 : Blo 1697549 1911217 := bbase (se 2 (by rfl) ⟨716706, by rfl⟩ : syracuseStep 1911217 = 1433413) (by norm_num)
theorem B2419141 : Blo 1697549 2419141 := bbase (se 4 (by rfl) ⟨226794, by rfl⟩ : syracuseStep 2419141 = 453589) (by norm_num)
theorem B1837513 : Blo 1697549 1837513 := bbase (se 2 (by rfl) ⟨689067, by rfl⟩ : syracuseStep 1837513 = 1378135) (by norm_num)
theorem B1911253 : Blo 1697549 1911253 := bbase (se 7 (by rfl) ⟨22397, by rfl⟩ : syracuseStep 1911253 = 44795) (by norm_num)
theorem B3820013 : Blo 1697549 3820013 := bbase (se 3 (by rfl) ⟨716252, by rfl⟩ : syracuseStep 3820013 = 1432505) (by norm_num)
theorem B1911289 : Blo 1697549 1911289 := bbase (se 2 (by rfl) ⟨716733, by rfl⟩ : syracuseStep 1911289 = 1433467) (by norm_num)
theorem B1812989 : Blo 1697549 1812989 := bbase (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) (by norm_num)
theorem B2148869 : Blo 1697549 2148869 := bbase (se 4 (by rfl) ⟨201456, by rfl⟩ : syracuseStep 2148869 = 402913) (by norm_num)
theorem B2296333 : Blo 1697549 2296333 := bbase (se 3 (by rfl) ⟨430562, by rfl⟩ : syracuseStep 2296333 = 861125) (by norm_num)
theorem B1911325 : Blo 1697549 1911325 := bbase (se 3 (by rfl) ⟨358373, by rfl⟩ : syracuseStep 1911325 = 716747) (by norm_num)
theorem B3820085 : Blo 1697549 3820085 := bbase (se 5 (by rfl) ⟨179066, by rfl⟩ : syracuseStep 3820085 = 358133) (by norm_num)
theorem B2148925 : Blo 1697549 2148925 := bbase (se 3 (by rfl) ⟨402923, by rfl⟩ : syracuseStep 2148925 = 805847) (by norm_num)
theorem B1911361 : Blo 1697549 1911361 := bbase (se 2 (by rfl) ⟨716760, by rfl⟩ : syracuseStep 1911361 = 1433521) (by norm_num)
theorem B1911397 : Blo 1697549 1911397 := bbase (se 4 (by rfl) ⟨179193, by rfl⟩ : syracuseStep 1911397 = 358387) (by norm_num)
theorem B2583149 : Blo 1697549 2583149 := bbase (se 3 (by rfl) ⟨484340, by rfl⟩ : syracuseStep 2583149 = 968681) (by norm_num)
theorem B3820157 : Blo 1697549 3820157 := bbase (se 3 (by rfl) ⟨716279, by rfl⟩ : syracuseStep 3820157 = 1432559) (by norm_num)
theorem B1911433 : Blo 1697549 1911433 := bbase (se 2 (by rfl) ⟨716787, by rfl⟩ : syracuseStep 1911433 = 1433575) (by norm_num)
theorem B6449813 : Blo 1697549 6449813 := bbase (se 6 (by rfl) ⟨151167, by rfl⟩ : syracuseStep 6449813 = 302335) (by norm_num)
theorem B2149021 : Blo 1697549 2149021 := bbase (se 3 (by rfl) ⟨402941, by rfl⟩ : syracuseStep 2149021 = 805883) (by norm_num)
theorem B1911469 : Blo 1697549 1911469 := bbase (se 3 (by rfl) ⟨358400, by rfl⟩ : syracuseStep 1911469 = 716801) (by norm_num)
theorem B3820229 : Blo 1697549 3820229 := bbase (se 4 (by rfl) ⟨358146, by rfl⟩ : syracuseStep 3820229 = 716293) (by norm_num)
theorem B1911505 : Blo 1697549 1911505 := bbase (se 2 (by rfl) ⟨716814, by rfl⟩ : syracuseStep 1911505 = 1433629) (by norm_num)
theorem B12896981 : Blo 1697549 12896981 := bbase (se 7 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 12896981 = 302273) (by norm_num)
theorem B9669365 : Blo 1697549 9669365 := bbase (se 5 (by rfl) ⟨453251, by rfl⟩ : syracuseStep 9669365 = 906503) (by norm_num)
theorem B1911541 : Blo 1697549 1911541 := bbase (se 5 (by rfl) ⟨89603, by rfl⟩ : syracuseStep 1911541 = 179207) (by norm_num)
theorem B4590341 : Blo 1697549 4590341 := bbase (se 4 (by rfl) ⟨430344, by rfl⟩ : syracuseStep 4590341 = 860689) (by norm_num)
theorem B3820301 : Blo 1697549 3820301 := bbase (se 3 (by rfl) ⟨716306, by rfl⟩ : syracuseStep 3820301 = 1432613) (by norm_num)
theorem B2296597 : Blo 1697549 2296597 := bbase (se 6 (by rfl) ⟨53826, by rfl⟩ : syracuseStep 2296597 = 107653) (by norm_num)
theorem B1911577 : Blo 1697549 1911577 := bbase (se 2 (by rfl) ⟨716841, by rfl⟩ : syracuseStep 1911577 = 1433683) (by norm_num)
theorem B1936181 : Blo 1697549 1936181 := bbase (se 5 (by rfl) ⟨90758, by rfl⟩ : syracuseStep 1936181 = 181517) (by norm_num)
theorem B1911613 : Blo 1697549 1911613 := bbase (se 3 (by rfl) ⟨358427, by rfl⟩ : syracuseStep 1911613 = 716855) (by norm_num)
theorem B2419517 : Blo 1697549 2419517 := bbase (se 3 (by rfl) ⟨453659, by rfl⟩ : syracuseStep 2419517 = 907319) (by norm_num)
theorem B2149193 : Blo 1697549 2149193 := bbase (se 2 (by rfl) ⟨805947, by rfl⟩ : syracuseStep 2149193 = 1611895) (by norm_num)
theorem B3820373 : Blo 1697549 3820373 := bbase (se 9 (by rfl) ⟨11192, by rfl⟩ : syracuseStep 3820373 = 22385) (by norm_num)
theorem B1911649 : Blo 1697549 1911649 := bbase (se 2 (by rfl) ⟨716868, by rfl⟩ : syracuseStep 1911649 = 1433737) (by norm_num)
theorem B2149249 : Blo 1697549 2149249 := bbase (se 2 (by rfl) ⟨805968, by rfl⟩ : syracuseStep 2149249 = 1611937) (by norm_num)
theorem B1911685 : Blo 1697549 1911685 := bbase (se 4 (by rfl) ⟨179220, by rfl⟩ : syracuseStep 1911685 = 358441) (by norm_num)
theorem B3820445 : Blo 1697549 3820445 := bbase (se 3 (by rfl) ⟨716333, by rfl⟩ : syracuseStep 3820445 = 1432667) (by norm_num)
theorem B1911721 : Blo 1697549 1911721 := bbase (se 2 (by rfl) ⟨716895, by rfl⟩ : syracuseStep 1911721 = 1433791) (by norm_num)
theorem B4836277 : Blo 1697549 4836277 := bbase (se 5 (by rfl) ⟨226700, by rfl⟩ : syracuseStep 4836277 = 453401) (by norm_num)
theorem B6450101 : Blo 1697549 6450101 := bbase (se 5 (by rfl) ⟨302348, by rfl⟩ : syracuseStep 6450101 = 604697) (by norm_num)
theorem B1813433 : Blo 1697549 1813433 := bbase (se 2 (by rfl) ⟨680037, by rfl⟩ : syracuseStep 1813433 = 1360075) (by norm_num)
theorem B1911757 : Blo 1697549 1911757 := bbase (se 3 (by rfl) ⟨358454, by rfl⟩ : syracuseStep 1911757 = 716909) (by norm_num)
theorem B5729237 : Blo 1697549 5729237 := bbase (se 7 (by rfl) ⟨67139, by rfl⟩ : syracuseStep 5729237 = 134279) (by norm_num)
theorem B9563093 : Blo 1697549 9563093 := bbase (se 7 (by rfl) ⟨112067, by rfl⟩ : syracuseStep 9563093 = 224135) (by norm_num)
theorem B2149345 : Blo 1697549 2149345 := bbase (se 2 (by rfl) ⟨806004, by rfl⟩ : syracuseStep 2149345 = 1612009) (by norm_num)
theorem B3820517 : Blo 1697549 3820517 := bbase (se 4 (by rfl) ⟨358173, by rfl⟩ : syracuseStep 3820517 = 716347) (by norm_num)
theorem B1911793 : Blo 1697549 1911793 := bbase (se 2 (by rfl) ⟨716922, by rfl⟩ : syracuseStep 1911793 = 1433845) (by norm_num)
theorem B1911829 : Blo 1697549 1911829 := bbase (se 6 (by rfl) ⟨44808, by rfl⟩ : syracuseStep 1911829 = 89617) (by norm_num)
theorem B3820589 : Blo 1697549 3820589 := bbase (se 3 (by rfl) ⟨716360, by rfl⟩ : syracuseStep 3820589 = 1432721) (by norm_num)
theorem B1911865 : Blo 1697549 1911865 := bbase (se 2 (by rfl) ⟨716949, by rfl⟩ : syracuseStep 1911865 = 1433899) (by norm_num)
theorem B1911901 : Blo 1697549 1911901 := bbase (se 3 (by rfl) ⟨358481, by rfl⟩ : syracuseStep 1911901 = 716963) (by norm_num)
theorem B3820661 : Blo 1697549 3820661 := bbase (se 5 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 3820661 = 358187) (by norm_num)
theorem B1911937 : Blo 1697549 1911937 := bbase (se 2 (by rfl) ⟨716976, by rfl⟩ : syracuseStep 1911937 = 1433953) (by norm_num)
theorem B2149517 : Blo 1697549 2149517 := bbase (se 3 (by rfl) ⟨403034, by rfl⟩ : syracuseStep 2149517 = 806069) (by norm_num)
theorem B5442709 : Blo 1697549 5442709 := bbase (se 6 (by rfl) ⟨127563, by rfl⟩ : syracuseStep 5442709 = 255127) (by norm_num)
theorem B5590181 : Blo 1697549 5590181 := bbase (se 4 (by rfl) ⟨524079, by rfl⟩ : syracuseStep 5590181 = 1048159) (by norm_num)
theorem B1911973 : Blo 1697549 1911973 := bbase (se 4 (by rfl) ⟨179247, by rfl⟩ : syracuseStep 1911973 = 358495) (by norm_num)
theorem B1813681 : Blo 1697549 1813681 := bbase (se 2 (by rfl) ⟨680130, by rfl⟩ : syracuseStep 1813681 = 1360261) (by norm_num)
theorem B3820733 : Blo 1697549 3820733 := bbase (se 3 (by rfl) ⟨716387, by rfl⟩ : syracuseStep 3820733 = 1432775) (by norm_num)
theorem B2149573 : Blo 1697549 2149573 := bbase (se 4 (by rfl) ⟨201522, by rfl⟩ : syracuseStep 2149573 = 403045) (by norm_num)
theorem B3222757 : Blo 1697549 3222757 := bbase (se 4 (by rfl) ⟨302133, by rfl⟩ : syracuseStep 3222757 = 604267) (by norm_num)
theorem B3820805 : Blo 1697549 3820805 := bbase (se 4 (by rfl) ⟨358200, by rfl⟩ : syracuseStep 3820805 = 716401) (by norm_num)
theorem B2149669 : Blo 1697549 2149669 := bbase (se 4 (by rfl) ⟨201531, by rfl⟩ : syracuseStep 2149669 = 403063) (by norm_num)
theorem B2452789 : Blo 1697549 2452789 := bbase (se 5 (by rfl) ⟨114974, by rfl⟩ : syracuseStep 2452789 = 229949) (by norm_num)
theorem B3820877 : Blo 1697549 3820877 := bbase (se 3 (by rfl) ⟨716414, by rfl⟩ : syracuseStep 3820877 = 1432829) (by norm_num)
theorem B8596853 : Blo 1697549 8596853 := bbase (se 5 (by rfl) ⟨402977, by rfl⟩ : syracuseStep 8596853 = 805955) (by norm_num)
theorem B10882421 : Blo 1697549 10882421 := bbase (se 5 (by rfl) ⟨510113, by rfl⟩ : syracuseStep 10882421 = 1020227) (by norm_num)
theorem B4083061 : Blo 1697549 4083061 := bbase (se 5 (by rfl) ⟨191393, by rfl⟩ : syracuseStep 4083061 = 382787) (by norm_num)
theorem B5729669 : Blo 1697549 5729669 := bbase (se 4 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 5729669 = 1074313) (by norm_num)
theorem B3820949 : Blo 1697549 3820949 := bbase (se 6 (by rfl) ⟨89553, by rfl⟩ : syracuseStep 3820949 = 179107) (by norm_num)
theorem B5442965 : Blo 1697549 5442965 := bbase (se 6 (by rfl) ⟨127569, by rfl⟩ : syracuseStep 5442965 = 255139) (by norm_num)
theorem B1936805 : Blo 1697549 1936805 := bbase (se 4 (by rfl) ⟨181575, by rfl⟩ : syracuseStep 1936805 = 363151) (by norm_num)
theorem B4656565 : Blo 1697549 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B2149841 : Blo 1697549 2149841 := bbase (se 2 (by rfl) ⟨806190, by rfl⟩ : syracuseStep 2149841 = 1612381) (by norm_num)
theorem B3821021 : Blo 1697549 3821021 := bbase (se 3 (by rfl) ⟨716441, by rfl⟩ : syracuseStep 3821021 = 1432883) (by norm_num)
theorem B2149897 : Blo 1697549 2149897 := bbase (se 2 (by rfl) ⟨806211, by rfl⟩ : syracuseStep 2149897 = 1612423) (by norm_num)
theorem B3223061 : Blo 1697549 3223061 := bbase (se 6 (by rfl) ⟨75540, by rfl⟩ : syracuseStep 3223061 = 151081) (by norm_num)
theorem B3821093 : Blo 1697549 3821093 := bbase (se 4 (by rfl) ⟨358227, by rfl⟩ : syracuseStep 3821093 = 716455) (by norm_num)
theorem B1814113 : Blo 1697549 1814113 := bbase (se 2 (by rfl) ⟨680292, by rfl⟩ : syracuseStep 1814113 = 1360585) (by norm_num)
theorem B2149993 : Blo 1697549 2149993 := bbase (se 2 (by rfl) ⟨806247, by rfl⟩ : syracuseStep 2149993 = 1612495) (by norm_num)
theorem B3821165 : Blo 1697549 3821165 := bbase (se 3 (by rfl) ⟨716468, by rfl⟩ : syracuseStep 3821165 = 1432937) (by norm_num)
theorem B1814185 : Blo 1697549 1814185 := bbase (se 2 (by rfl) ⟨680319, by rfl⟩ : syracuseStep 1814185 = 1360639) (by norm_num)
theorem B3821237 : Blo 1697549 3821237 := bbase (se 5 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 3821237 = 358241) (by norm_num)
theorem B14503637 : Blo 1697549 14503637 := bbase (se 7 (by rfl) ⟨169964, by rfl⟩ : syracuseStep 14503637 = 339929) (by norm_num)
theorem B10325717 : Blo 1697549 10325717 := bbase (se 7 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 10325717 = 242009) (by norm_num)
theorem B10333909 : Blo 1697549 10333909 := bbase (se 7 (by rfl) ⟨121100, by rfl⟩ : syracuseStep 10333909 = 242201) (by norm_num)
theorem B3821309 : Blo 1697549 3821309 := bbase (se 3 (by rfl) ⟨716495, by rfl⟩ : syracuseStep 3821309 = 1432991) (by norm_num)
theorem B2150165 : Blo 1697549 2150165 := bbase (se 6 (by rfl) ⟨50394, by rfl⟩ : syracuseStep 2150165 = 100789) (by norm_num)
theorem B5730101 : Blo 1697549 5730101 := bbase (se 5 (by rfl) ⟨268598, by rfl⟩ : syracuseStep 5730101 = 537197) (by norm_num)
theorem B3821381 : Blo 1697549 3821381 := bbase (se 4 (by rfl) ⟨358254, by rfl⟩ : syracuseStep 3821381 = 716509) (by norm_num)
theorem B2150221 : Blo 1697549 2150221 := bbase (se 3 (by rfl) ⟨403166, by rfl⟩ : syracuseStep 2150221 = 806333) (by norm_num)
theorem B3821453 : Blo 1697549 3821453 := bbase (se 3 (by rfl) ⟨716522, by rfl⟩ : syracuseStep 3821453 = 1433045) (by norm_num)
theorem B9670549 : Blo 1697549 9670549 := bbase (se 6 (by rfl) ⟨226653, by rfl⟩ : syracuseStep 9670549 = 453307) (by norm_num)
theorem B2150317 : Blo 1697549 2150317 := bbase (se 3 (by rfl) ⟨403184, by rfl⟩ : syracuseStep 2150317 = 806369) (by norm_num)
theorem B3821525 : Blo 1697549 3821525 := bbase (se 7 (by rfl) ⟨44783, by rfl⟩ : syracuseStep 3821525 = 89567) (by norm_num)
theorem B1937389 : Blo 1697549 1937389 := bbase (se 3 (by rfl) ⟨363260, by rfl⟩ : syracuseStep 1937389 = 726521) (by norm_num)
theorem B8720389 : Blo 1697549 8720389 := bbase (se 4 (by rfl) ⟨817536, by rfl⟩ : syracuseStep 8720389 = 1635073) (by norm_num)
theorem B3821597 : Blo 1697549 3821597 := bbase (se 3 (by rfl) ⟨716549, by rfl⟩ : syracuseStep 3821597 = 1433099) (by norm_num)
theorem B1814557 : Blo 1697549 1814557 := bbase (se 3 (by rfl) ⟨340229, by rfl⟩ : syracuseStep 1814557 = 680459) (by norm_num)
theorem B6451285 : Blo 1697549 6451285 := bbase (se 8 (by rfl) ⟨37800, by rfl⟩ : syracuseStep 6451285 = 75601) (by norm_num)
theorem B2150489 : Blo 1697549 2150489 := bbase (se 2 (by rfl) ⟨806433, by rfl⟩ : syracuseStep 2150489 = 1612867) (by norm_num)
theorem B3821669 : Blo 1697549 3821669 := bbase (se 4 (by rfl) ⟨358281, by rfl⟩ : syracuseStep 3821669 = 716563) (by norm_num)
theorem B2150545 : Blo 1697549 2150545 := bbase (se 2 (by rfl) ⟨806454, by rfl⟩ : syracuseStep 2150545 = 1612909) (by norm_num)
theorem B3821741 : Blo 1697549 3821741 := bbase (se 3 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 3821741 = 1433153) (by norm_num)
theorem B5730533 : Blo 1697549 5730533 := bbase (se 4 (by rfl) ⟨537237, by rfl⟩ : syracuseStep 5730533 = 1074475) (by norm_num)
theorem B2150641 : Blo 1697549 2150641 := bbase (se 2 (by rfl) ⟨806490, by rfl⟩ : syracuseStep 2150641 = 1612981) (by norm_num)
theorem B3821813 : Blo 1697549 3821813 := bbase (se 5 (by rfl) ⟨179147, by rfl⟩ : syracuseStep 3821813 = 358295) (by norm_num)
theorem B3223813 : Blo 1697549 3223813 := bbase (se 4 (by rfl) ⟨302232, by rfl⟩ : syracuseStep 3223813 = 604465) (by norm_num)
theorem B4296989 : Blo 1697549 4296989 := bbase (se 3 (by rfl) ⟨805685, by rfl⟩ : syracuseStep 4296989 = 1611371) (by norm_num)
theorem B3821885 : Blo 1697549 3821885 := bbase (se 3 (by rfl) ⟨716603, by rfl⟩ : syracuseStep 3821885 = 1433207) (by norm_num)
theorem B3821957 : Blo 1697549 3821957 := bbase (se 4 (by rfl) ⟨358308, by rfl⟩ : syracuseStep 3821957 = 716617) (by norm_num)
theorem B6451589 : Blo 1697549 6451589 := bbase (se 4 (by rfl) ⟨604836, by rfl⟩ : syracuseStep 6451589 = 1209673) (by norm_num)
theorem B3223957 : Blo 1697549 3223957 := bbase (se 6 (by rfl) ⟨75561, by rfl⟩ : syracuseStep 3223957 = 151123) (by norm_num)
theorem B4837781 : Blo 1697549 4837781 := bbase (se 6 (by rfl) ⟨113385, by rfl⟩ : syracuseStep 4837781 = 226771) (by norm_num)
theorem B2150813 : Blo 1697549 2150813 := bbase (se 3 (by rfl) ⟨403277, by rfl⟩ : syracuseStep 2150813 = 806555) (by norm_num)
theorem B2068921 : Blo 1697549 2068921 := bbase (se 2 (by rfl) ⟨775845, by rfl⟩ : syracuseStep 2068921 = 1551691) (by norm_num)
theorem B3822029 : Blo 1697549 3822029 := bbase (se 3 (by rfl) ⟨716630, by rfl⟩ : syracuseStep 3822029 = 1433261) (by norm_num)
theorem B7254485 : Blo 1697549 7254485 := bbase (se 7 (by rfl) ⟨85013, by rfl⟩ : syracuseStep 7254485 = 170027) (by norm_num)
theorem B2150869 : Blo 1697549 2150869 := bbase (se 7 (by rfl) ⟨25205, by rfl⟩ : syracuseStep 2150869 = 50411) (by norm_num)
theorem B3822101 : Blo 1697549 3822101 := bbase (se 6 (by rfl) ⟨89580, by rfl⟩ : syracuseStep 3822101 = 179161) (by norm_num)
theorem B3224117 : Blo 1697549 3224117 := bbase (se 5 (by rfl) ⟨151130, by rfl⟩ : syracuseStep 3224117 = 302261) (by norm_num)
theorem B2150965 : Blo 1697549 2150965 := bbase (se 5 (by rfl) ⟨100826, by rfl⟩ : syracuseStep 2150965 = 201653) (by norm_num)
theorem B2904661 : Blo 1697549 2904661 := bbase (se 8 (by rfl) ⟨17019, by rfl⟩ : syracuseStep 2904661 = 34039) (by norm_num)
theorem B3822173 : Blo 1697549 3822173 := bbase (se 3 (by rfl) ⟨716657, by rfl⟩ : syracuseStep 3822173 = 1433315) (by norm_num)
theorem B4297333 : Blo 1697549 4297333 := bbase (se 5 (by rfl) ⟨201437, by rfl⟩ : syracuseStep 4297333 = 402875) (by norm_num)
theorem B8598149 : Blo 1697549 8598149 := bbase (se 4 (by rfl) ⟨806076, by rfl⟩ : syracuseStep 8598149 = 1612153) (by norm_num)
theorem B5730965 : Blo 1697549 5730965 := bbase (se 6 (by rfl) ⟨134319, by rfl⟩ : syracuseStep 5730965 = 268639) (by norm_num)
theorem B3822245 : Blo 1697549 3822245 := bbase (se 4 (by rfl) ⟨358335, by rfl⟩ : syracuseStep 3822245 = 716671) (by norm_num)
theorem B3224261 : Blo 1697549 3224261 := bbase (se 4 (by rfl) ⟨302274, by rfl⟩ : syracuseStep 3224261 = 604549) (by norm_num)
theorem B4297445 : Blo 1697549 4297445 := bbase (se 4 (by rfl) ⟨402885, by rfl⟩ : syracuseStep 4297445 = 805771) (by norm_num)
theorem B3822317 : Blo 1697549 3822317 := bbase (se 3 (by rfl) ⟨716684, by rfl⟩ : syracuseStep 3822317 = 1433369) (by norm_num)
theorem B3822389 : Blo 1697549 3822389 := bbase (se 5 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 3822389 = 358349) (by norm_num)
theorem B3822461 : Blo 1697549 3822461 := bbase (se 3 (by rfl) ⟨716711, by rfl⟩ : syracuseStep 3822461 = 1433423) (by norm_num)
theorem B4297637 : Blo 1697549 4297637 := bbase (se 4 (by rfl) ⟨402903, by rfl⟩ : syracuseStep 4297637 = 805807) (by norm_num)
theorem B8164277 : Blo 1697549 8164277 := bbase (se 5 (by rfl) ⟨382700, by rfl⟩ : syracuseStep 8164277 = 765401) (by norm_num)
theorem B3822533 : Blo 1697549 3822533 := bbase (se 4 (by rfl) ⟨358362, by rfl⟩ : syracuseStep 3822533 = 716725) (by norm_num)
theorem B3224549 : Blo 1697549 3224549 := bbase (se 4 (by rfl) ⟨302301, by rfl⟩ : syracuseStep 3224549 = 604603) (by norm_num)
theorem B2208769 : Blo 1697549 2208769 := bbase (se 2 (by rfl) ⟨828288, by rfl⟩ : syracuseStep 2208769 = 1656577) (by norm_num)
theorem B3822605 : Blo 1697549 3822605 := bbase (se 3 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 3822605 = 1433477) (by norm_num)
theorem B5731397 : Blo 1697549 5731397 := bbase (se 4 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 5731397 = 1074637) (by norm_num)
theorem B3822677 : Blo 1697549 3822677 := bbase (se 8 (by rfl) ⟨22398, by rfl⟩ : syracuseStep 3822677 = 44797) (by norm_num)
theorem B3224701 : Blo 1697549 3224701 := bbase (se 3 (by rfl) ⟨604631, by rfl⟩ : syracuseStep 3224701 = 1209263) (by norm_num)
theorem B3822749 : Blo 1697549 3822749 := bbase (se 3 (by rfl) ⟨716765, by rfl⟩ : syracuseStep 3822749 = 1433531) (by norm_num)
theorem B3626149 : Blo 1697549 3626149 := bbase (se 4 (by rfl) ⟨339951, by rfl⟩ : syracuseStep 3626149 = 679903) (by norm_num)
theorem B3822821 : Blo 1697549 3822821 := bbase (se 4 (by rfl) ⟨358389, by rfl⟩ : syracuseStep 3822821 = 716779) (by norm_num)
theorem B4297981 : Blo 1697549 4297981 := bbase (se 3 (by rfl) ⟨805871, by rfl⟩ : syracuseStep 4297981 = 1611743) (by norm_num)
theorem B3822893 : Blo 1697549 3822893 := bbase (se 3 (by rfl) ⟨716792, by rfl⟩ : syracuseStep 3822893 = 1433585) (by norm_num)
theorem B2905421 : Blo 1697549 2905421 := bbase (se 3 (by rfl) ⟨544766, by rfl⟩ : syracuseStep 2905421 = 1089533) (by norm_num)
theorem B4298093 : Blo 1697549 4298093 := bbase (se 3 (by rfl) ⟨805892, by rfl⟩ : syracuseStep 4298093 = 1611785) (by norm_num)
theorem B3822965 : Blo 1697549 3822965 := bbase (se 5 (by rfl) ⟨179201, by rfl⟩ : syracuseStep 3822965 = 358403) (by norm_num)
theorem B3061165 : Blo 1697549 3061165 := bbase (se 3 (by rfl) ⟨573968, by rfl⟩ : syracuseStep 3061165 = 1147937) (by norm_num)
theorem B3225005 : Blo 1697549 3225005 := bbase (se 3 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 3225005 = 1209377) (by norm_num)
theorem B3823037 : Blo 1697549 3823037 := bbase (se 3 (by rfl) ⟨716819, by rfl⟩ : syracuseStep 3823037 = 1433639) (by norm_num)
theorem B9180661 : Blo 1697549 9180661 := bbase (se 5 (by rfl) ⟨430343, by rfl⟩ : syracuseStep 9180661 = 860687) (by norm_num)
theorem B5731829 : Blo 1697549 5731829 := bbase (se 5 (by rfl) ⟨268679, by rfl⟩ : syracuseStep 5731829 = 537359) (by norm_num)
theorem B3823109 : Blo 1697549 3823109 := bbase (se 4 (by rfl) ⟨358416, by rfl⟩ : syracuseStep 3823109 = 716833) (by norm_num)
theorem B3626525 : Blo 1697549 3626525 := bbase (se 3 (by rfl) ⟨679973, by rfl⟩ : syracuseStep 3626525 = 1359947) (by norm_num)
theorem B4298285 : Blo 1697549 4298285 := bbase (se 3 (by rfl) ⟨805928, by rfl⟩ : syracuseStep 4298285 = 1611857) (by norm_num)
theorem B2864693 : Blo 1697549 2864693 := bbase (se 5 (by rfl) ⟨134282, by rfl⟩ : syracuseStep 2864693 = 268565) (by norm_num)
theorem B3823181 : Blo 1697549 3823181 := bbase (se 3 (by rfl) ⟨716846, by rfl⟩ : syracuseStep 3823181 = 1433693) (by norm_num)
theorem B3061373 : Blo 1697549 3061373 := bbase (se 3 (by rfl) ⟨574007, by rfl⟩ : syracuseStep 3061373 = 1148015) (by norm_num)
theorem B3872389 : Blo 1697549 3872389 := bbase (se 4 (by rfl) ⟨363036, by rfl⟩ : syracuseStep 3872389 = 726073) (by norm_num)
theorem B3675797 : Blo 1697549 3675797 := bbase (se 6 (by rfl) ⟨86151, by rfl⟩ : syracuseStep 3675797 = 172303) (by norm_num)
theorem B3823253 : Blo 1697549 3823253 := bbase (se 6 (by rfl) ⟨89607, by rfl⟩ : syracuseStep 3823253 = 179215) (by norm_num)
theorem B2864821 : Blo 1697549 2864821 := bbase (se 5 (by rfl) ⟨134288, by rfl⟩ : syracuseStep 2864821 = 268577) (by norm_num)
theorem B10327733 : Blo 1697549 10327733 := bbase (se 5 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 10327733 = 968225) (by norm_num)
theorem B3823325 : Blo 1697549 3823325 := bbase (se 3 (by rfl) ⟨716873, by rfl⟩ : syracuseStep 3823325 = 1433747) (by norm_num)
theorem B2864909 : Blo 1697549 2864909 := bbase (se 3 (by rfl) ⟨537170, by rfl⟩ : syracuseStep 2864909 = 1074341) (by norm_num)
theorem B3823397 : Blo 1697549 3823397 := bbase (se 4 (by rfl) ⟨358443, by rfl⟩ : syracuseStep 3823397 = 716887) (by norm_num)
theorem B2389813 : Blo 1697549 2389813 := bbase (se 5 (by rfl) ⟨112022, by rfl⟩ : syracuseStep 2389813 = 224045) (by norm_num)
theorem B11032373 : Blo 1697549 11032373 := bbase (se 5 (by rfl) ⟨517142, by rfl⟩ : syracuseStep 11032373 = 1034285) (by norm_num)
theorem B9672533 : Blo 1697549 9672533 := bbase (se 9 (by rfl) ⟨28337, by rfl⟩ : syracuseStep 9672533 = 56675) (by norm_num)
theorem B3823469 : Blo 1697549 3823469 := bbase (se 3 (by rfl) ⟨716900, by rfl⟩ : syracuseStep 3823469 = 1433801) (by norm_num)
theorem B10327925 : Blo 1697549 10327925 := bbase (se 5 (by rfl) ⟨484121, by rfl⟩ : syracuseStep 10327925 = 968243) (by norm_num)
theorem B4298629 : Blo 1697549 4298629 := bbase (se 4 (by rfl) ⟨402996, by rfl⟩ : syracuseStep 4298629 = 805993) (by norm_num)
theorem B2865037 : Blo 1697549 2865037 := bbase (se 3 (by rfl) ⟨537194, by rfl⟩ : syracuseStep 2865037 = 1074389) (by norm_num)
theorem B8599445 : Blo 1697549 8599445 := bbase (se 6 (by rfl) ⟨201549, by rfl⟩ : syracuseStep 8599445 = 403099) (by norm_num)
theorem B5732261 : Blo 1697549 5732261 := bbase (se 4 (by rfl) ⟨537399, by rfl⟩ : syracuseStep 5732261 = 1074799) (by norm_num)
theorem B3823541 : Blo 1697549 3823541 := bbase (se 5 (by rfl) ⟨179228, by rfl⟩ : syracuseStep 3823541 = 358457) (by norm_num)
theorem B4839365 : Blo 1697549 4839365 := bbase (se 4 (by rfl) ⟨453690, by rfl⟩ : syracuseStep 4839365 = 907381) (by norm_num)
theorem B2865125 : Blo 1697549 2865125 := bbase (se 4 (by rfl) ⟨268605, by rfl⟩ : syracuseStep 2865125 = 537211) (by norm_num)
theorem B3061741 : Blo 1697549 3061741 := bbase (se 3 (by rfl) ⟨574076, by rfl⟩ : syracuseStep 3061741 = 1148153) (by norm_num)
theorem B4298741 : Blo 1697549 4298741 := bbase (se 5 (by rfl) ⟨201503, by rfl⟩ : syracuseStep 4298741 = 403007) (by norm_num)
theorem B3823613 : Blo 1697549 3823613 := bbase (se 3 (by rfl) ⟨716927, by rfl⟩ : syracuseStep 3823613 = 1433855) (by norm_num)
theorem B7747589 : Blo 1697549 7747589 := bbase (se 4 (by rfl) ⟨726336, by rfl⟩ : syracuseStep 7747589 = 1452673) (by norm_num)
theorem B14710805 : Blo 1697549 14710805 := bbase (se 6 (by rfl) ⟨344784, by rfl⟩ : syracuseStep 14710805 = 689569) (by norm_num)
theorem B3823685 : Blo 1697549 3823685 := bbase (se 4 (by rfl) ⟨358470, by rfl⟩ : syracuseStep 3823685 = 716941) (by norm_num)
theorem B2865253 : Blo 1697549 2865253 := bbase (se 4 (by rfl) ⟨268617, by rfl⟩ : syracuseStep 2865253 = 537235) (by norm_num)
theorem B3823757 : Blo 1697549 3823757 := bbase (se 3 (by rfl) ⟨716954, by rfl⟩ : syracuseStep 3823757 = 1433909) (by norm_num)
theorem B6715541 : Blo 1697549 6715541 := bbase (se 6 (by rfl) ⟨157395, by rfl⟩ : syracuseStep 6715541 = 314791) (by norm_num)
theorem B3225757 : Blo 1697549 3225757 := bbase (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) (by norm_num)
theorem B4298933 : Blo 1697549 4298933 := bbase (se 5 (by rfl) ⟨201512, by rfl⟩ : syracuseStep 4298933 = 403025) (by norm_num)
theorem B2865341 : Blo 1697549 2865341 := bbase (se 3 (by rfl) ⟨537251, by rfl⟩ : syracuseStep 2865341 = 1074503) (by norm_num)
theorem B3823829 : Blo 1697549 3823829 := bbase (se 7 (by rfl) ⟨44810, by rfl⟩ : syracuseStep 3823829 = 89621) (by norm_num)
theorem B3823901 : Blo 1697549 3823901 := bbase (se 3 (by rfl) ⟨716981, by rfl⟩ : syracuseStep 3823901 = 1433963) (by norm_num)
theorem B3225901 : Blo 1697549 3225901 := bbase (se 3 (by rfl) ⟨604856, by rfl⟩ : syracuseStep 3225901 = 1209713) (by norm_num)
theorem B2865469 : Blo 1697549 2865469 := bbase (se 3 (by rfl) ⟨537275, by rfl⟩ : syracuseStep 2865469 = 1074551) (by norm_num)
theorem B4479301 : Blo 1697549 4479301 := bbase (se 4 (by rfl) ⟨419934, by rfl⟩ : syracuseStep 4479301 = 839869) (by norm_num)
theorem B5732693 : Blo 1697549 5732693 := bbase (se 10 (by rfl) ⟨8397, by rfl⟩ : syracuseStep 5732693 = 16795) (by norm_num)
theorem B3823973 : Blo 1697549 3823973 := bbase (se 4 (by rfl) ⟨358497, by rfl⟩ : syracuseStep 3823973 = 716995) (by norm_num)
theorem B6207877 : Blo 1697549 6207877 := bbase (se 4 (by rfl) ⟨581988, by rfl⟩ : syracuseStep 6207877 = 1163977) (by norm_num)
theorem B2865557 : Blo 1697549 2865557 := bbase (se 6 (by rfl) ⟨67161, by rfl⟩ : syracuseStep 2865557 = 134323) (by norm_num)
theorem B3226061 : Blo 1697549 3226061 := bbase (se 3 (by rfl) ⟨604886, by rfl⟩ : syracuseStep 3226061 = 1209773) (by norm_num)
theorem B4299277 : Blo 1697549 4299277 := bbase (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) (by norm_num)
theorem B2865685 : Blo 1697549 2865685 := bbase (se 6 (by rfl) ⟨67164, by rfl⟩ : syracuseStep 2865685 = 134329) (by norm_num)
theorem B8165909 : Blo 1697549 8165909 := bbase (se 6 (by rfl) ⟨191388, by rfl⟩ : syracuseStep 8165909 = 382777) (by norm_num)
theorem B5167685 : Blo 1697549 5167685 := bbase (se 4 (by rfl) ⟨484470, by rfl⟩ : syracuseStep 5167685 = 968941) (by norm_num)
theorem B3226205 : Blo 1697549 3226205 := bbase (se 3 (by rfl) ⟨604913, by rfl⟩ : syracuseStep 3226205 = 1209827) (by norm_num)
theorem B2865773 : Blo 1697549 2865773 := bbase (se 3 (by rfl) ⟨537332, by rfl⟩ : syracuseStep 2865773 = 1074665) (by norm_num)
theorem B14506613 : Blo 1697549 14506613 := bbase (se 5 (by rfl) ⟨679997, by rfl⟩ : syracuseStep 14506613 = 1359995) (by norm_num)
theorem B2906741 : Blo 1697549 2906741 := bbase (se 5 (by rfl) ⟨136253, by rfl⟩ : syracuseStep 2906741 = 272507) (by norm_num)
theorem B4299389 : Blo 1697549 4299389 := bbase (se 3 (by rfl) ⟨806135, by rfl⟩ : syracuseStep 4299389 = 1612271) (by norm_num)
theorem B2546333 : Blo 1697549 2546333 := bbase (se 3 (by rfl) ⟨477437, by rfl⟩ : syracuseStep 2546333 = 954875) (by norm_num)
theorem B2546357 : Blo 1697549 2546357 := bbase (se 5 (by rfl) ⟨119360, by rfl⟩ : syracuseStep 2546357 = 238721) (by norm_num)
theorem B2546381 : Blo 1697549 2546381 := bbase (se 3 (by rfl) ⟨477446, by rfl⟩ : syracuseStep 2546381 = 954893) (by norm_num)
theorem B15497941 : Blo 1697549 15497941 := bbase (se 7 (by rfl) ⟨181616, by rfl⟩ : syracuseStep 15497941 = 363233) (by norm_num)
theorem B2546405 : Blo 1697549 2546405 := bbase (se 4 (by rfl) ⟨238725, by rfl⟩ : syracuseStep 2546405 = 477451) (by norm_num)
theorem B2865901 : Blo 1697549 2865901 := bbase (se 3 (by rfl) ⟨537356, by rfl⟩ : syracuseStep 2865901 = 1074713) (by norm_num)
theorem B3629053 : Blo 1697549 3629053 := bbase (se 3 (by rfl) ⟨680447, by rfl⟩ : syracuseStep 3629053 = 1360895) (by norm_num)
theorem B2546429 : Blo 1697549 2546429 := bbase (se 3 (by rfl) ⟨477455, by rfl⟩ : syracuseStep 2546429 = 954911) (by norm_num)
theorem B5733125 : Blo 1697549 5733125 := bbase (se 4 (by rfl) ⟨537480, by rfl⟩ : syracuseStep 5733125 = 1074961) (by norm_num)
theorem B3062533 : Blo 1697549 3062533 := bbase (se 4 (by rfl) ⟨287112, by rfl⟩ : syracuseStep 3062533 = 574225) (by norm_num)
theorem B2546453 : Blo 1697549 2546453 := bbase (se 6 (by rfl) ⟨59682, by rfl⟩ : syracuseStep 2546453 = 119365) (by norm_num)
theorem B3062549 : Blo 1697549 3062549 := bbase (se 6 (by rfl) ⟨71778, by rfl⟩ : syracuseStep 3062549 = 143557) (by norm_num)
theorem B8157989 : Blo 1697549 8157989 := bbase (se 4 (by rfl) ⟨764811, by rfl⟩ : syracuseStep 8157989 = 1529623) (by norm_num)
theorem B2546477 : Blo 1697549 2546477 := bbase (se 3 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 2546477 = 954929) (by norm_num)
theorem B2906933 : Blo 1697549 2906933 := bbase (se 5 (by rfl) ⟨136262, by rfl⟩ : syracuseStep 2906933 = 272525) (by norm_num)
theorem B4299581 : Blo 1697549 4299581 := bbase (se 3 (by rfl) ⟨806171, by rfl⟩ : syracuseStep 4299581 = 1612343) (by norm_num)
theorem B2546501 : Blo 1697549 2546501 := bbase (se 4 (by rfl) ⟨238734, by rfl⟩ : syracuseStep 2546501 = 477469) (by norm_num)
theorem B2865989 : Blo 1697549 2865989 := bbase (se 4 (by rfl) ⟨268686, by rfl⟩ : syracuseStep 2865989 = 537373) (by norm_num)
theorem B2546525 : Blo 1697549 2546525 := bbase (se 3 (by rfl) ⟨477473, by rfl⟩ : syracuseStep 2546525 = 954947) (by norm_num)
theorem B6445925 : Blo 1697549 6445925 := bbase (se 4 (by rfl) ⟨604305, by rfl⟩ : syracuseStep 6445925 = 1208611) (by norm_num)
theorem B2546549 : Blo 1697549 2546549 := bbase (se 5 (by rfl) ⟨119369, by rfl⟩ : syracuseStep 2546549 = 238739) (by norm_num)
theorem B2546573 : Blo 1697549 2546573 := bbase (se 3 (by rfl) ⟨477482, by rfl⟩ : syracuseStep 2546573 = 954965) (by norm_num)
theorem B2546597 : Blo 1697549 2546597 := bbase (se 4 (by rfl) ⟨238743, by rfl⟩ : syracuseStep 2546597 = 477487) (by norm_num)
theorem B2546621 : Blo 1697549 2546621 := bbase (se 3 (by rfl) ⟨477491, by rfl⟩ : syracuseStep 2546621 = 954983) (by norm_num)
theorem B2866117 : Blo 1697549 2866117 := bbase (se 4 (by rfl) ⟨268698, by rfl⟩ : syracuseStep 2866117 = 537397) (by norm_num)
theorem B2546645 : Blo 1697549 2546645 := bbase (se 7 (by rfl) ⟨29843, by rfl⟩ : syracuseStep 2546645 = 59687) (by norm_num)
theorem B3873757 : Blo 1697549 3873757 := bbase (se 3 (by rfl) ⟨726329, by rfl⟩ : syracuseStep 3873757 = 1452659) (by norm_num)
theorem B2546669 : Blo 1697549 2546669 := bbase (se 3 (by rfl) ⟨477500, by rfl⟩ : syracuseStep 2546669 = 955001) (by norm_num)
theorem B2546693 : Blo 1697549 2546693 := bbase (se 4 (by rfl) ⟨238752, by rfl⟩ : syracuseStep 2546693 = 477505) (by norm_num)
theorem B2546717 : Blo 1697549 2546717 := bbase (se 3 (by rfl) ⟨477509, by rfl⟩ : syracuseStep 2546717 = 955019) (by norm_num)
theorem B2866205 : Blo 1697549 2866205 := bbase (se 3 (by rfl) ⟨537413, by rfl⟩ : syracuseStep 2866205 = 1074827) (by norm_num)
theorem B2546741 : Blo 1697549 2546741 := bbase (se 5 (by rfl) ⟨119378, by rfl⟩ : syracuseStep 2546741 = 238757) (by norm_num)
theorem B12581941 : Blo 1697549 12581941 := bbase (se 5 (by rfl) ⟨589778, by rfl⟩ : syracuseStep 12581941 = 1179557) (by norm_num)
theorem B2546765 : Blo 1697549 2546765 := bbase (se 3 (by rfl) ⟨477518, by rfl⟩ : syracuseStep 2546765 = 955037) (by norm_num)
theorem B2546789 : Blo 1697549 2546789 := bbase (se 4 (by rfl) ⟨238761, by rfl⟩ : syracuseStep 2546789 = 477523) (by norm_num)
theorem B2546813 : Blo 1697549 2546813 := bbase (se 3 (by rfl) ⟨477527, by rfl⟩ : syracuseStep 2546813 = 955055) (by norm_num)
theorem B6446213 : Blo 1697549 6446213 := bbase (se 4 (by rfl) ⟨604332, by rfl⟩ : syracuseStep 6446213 = 1208665) (by norm_num)
theorem B3628165 : Blo 1697549 3628165 := bbase (se 4 (by rfl) ⟨340140, by rfl⟩ : syracuseStep 3628165 = 680281) (by norm_num)
theorem B2546837 : Blo 1697549 2546837 := bbase (se 6 (by rfl) ⟨59691, by rfl⟩ : syracuseStep 2546837 = 119383) (by norm_num)
theorem B4299925 : Blo 1697549 4299925 := bbase (se 6 (by rfl) ⟨100779, by rfl⟩ : syracuseStep 4299925 = 201559) (by norm_num)
theorem B16333973 : Blo 1697549 16333973 := bbase (se 6 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 16333973 = 765655) (by norm_num)
theorem B2866333 : Blo 1697549 2866333 := bbase (se 3 (by rfl) ⟨537437, by rfl⟩ : syracuseStep 2866333 = 1074875) (by norm_num)
theorem B8600741 : Blo 1697549 8600741 := bbase (se 4 (by rfl) ⟨806319, by rfl⟩ : syracuseStep 8600741 = 1612639) (by norm_num)
theorem B2546861 : Blo 1697549 2546861 := bbase (se 3 (by rfl) ⟨477536, by rfl⟩ : syracuseStep 2546861 = 955073) (by norm_num)
theorem B5733557 : Blo 1697549 5733557 := bbase (se 5 (by rfl) ⟨268760, by rfl⟩ : syracuseStep 5733557 = 537521) (by norm_num)
theorem B2546885 : Blo 1697549 2546885 := bbase (se 4 (by rfl) ⟨238770, by rfl⟩ : syracuseStep 2546885 = 477541) (by norm_num)
theorem B2546909 : Blo 1697549 2546909 := bbase (se 3 (by rfl) ⟨477545, by rfl⟩ : syracuseStep 2546909 = 955091) (by norm_num)
theorem B2546933 : Blo 1697549 2546933 := bbase (se 5 (by rfl) ⟨119387, by rfl⟩ : syracuseStep 2546933 = 238775) (by norm_num)
theorem B2866421 : Blo 1697549 2866421 := bbase (se 5 (by rfl) ⟨134363, by rfl⟩ : syracuseStep 2866421 = 268727) (by norm_num)
theorem B4300037 : Blo 1697549 4300037 := bbase (se 4 (by rfl) ⟨403128, by rfl⟩ : syracuseStep 4300037 = 806257) (by norm_num)
theorem B2546957 : Blo 1697549 2546957 := bbase (se 3 (by rfl) ⟨477554, by rfl⟩ : syracuseStep 2546957 = 955109) (by norm_num)
theorem B2546981 : Blo 1697549 2546981 := bbase (se 4 (by rfl) ⟨238779, by rfl⟩ : syracuseStep 2546981 = 477559) (by norm_num)
theorem B2178353 : Blo 1697549 2178353 := bbase (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) (by norm_num)
theorem B2547005 : Blo 1697549 2547005 := bbase (se 3 (by rfl) ⟨477563, by rfl⟩ : syracuseStep 2547005 = 955127) (by norm_num)
theorem B5438789 : Blo 1697549 5438789 := bbase (se 4 (by rfl) ⟨509886, by rfl⟩ : syracuseStep 5438789 = 1019773) (by norm_num)
theorem B2547029 : Blo 1697549 2547029 := bbase (se 11 (by rfl) ⟨1865, by rfl⟩ : syracuseStep 2547029 = 3731) (by norm_num)
theorem B4078957 : Blo 1697549 4078957 := bbase (se 3 (by rfl) ⟨764804, by rfl⟩ : syracuseStep 4078957 = 1529609) (by norm_num)
theorem B2547053 : Blo 1697549 2547053 := bbase (se 3 (by rfl) ⟨477572, by rfl⟩ : syracuseStep 2547053 = 955145) (by norm_num)
theorem B2866549 : Blo 1697549 2866549 := bbase (se 5 (by rfl) ⟨134369, by rfl⟩ : syracuseStep 2866549 = 268739) (by norm_num)
theorem B2547077 : Blo 1697549 2547077 := bbase (se 4 (by rfl) ⟨238788, by rfl⟩ : syracuseStep 2547077 = 477577) (by norm_num)
theorem B2547101 : Blo 1697549 2547101 := bbase (se 3 (by rfl) ⟨477581, by rfl⟩ : syracuseStep 2547101 = 955163) (by norm_num)
theorem B2547125 : Blo 1697549 2547125 := bbase (se 5 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 2547125 = 238793) (by norm_num)
theorem B4300229 : Blo 1697549 4300229 := bbase (se 4 (by rfl) ⟨403146, by rfl⟩ : syracuseStep 4300229 = 806293) (by norm_num)
theorem B2547149 : Blo 1697549 2547149 := bbase (se 3 (by rfl) ⟨477590, by rfl⟩ : syracuseStep 2547149 = 955181) (by norm_num)
theorem B2866637 : Blo 1697549 2866637 := bbase (se 3 (by rfl) ⟨537494, by rfl⟩ : syracuseStep 2866637 = 1074989) (by norm_num)
theorem B47095253 : Blo 1697549 47095253 := bbase (se 7 (by rfl) ⟨551897, by rfl⟩ : syracuseStep 47095253 = 1103795) (by norm_num)
theorem B61971925 : Blo 1697549 61971925 := bbase (se 7 (by rfl) ⟨726233, by rfl⟩ : syracuseStep 61971925 = 1452467) (by norm_num)
theorem B2547173 : Blo 1697549 2547173 := bbase (se 4 (by rfl) ⟨238797, by rfl⟩ : syracuseStep 2547173 = 477595) (by norm_num)
theorem B2867197 : Blo 1697549 2867197 := bbase (se 3 (by rfl) ⟨537599, by rfl⟩ : syracuseStep 2867197 = 1075199) (by norm_num)
theorem B2547197 : Blo 1697549 2547197 := bbase (se 3 (by rfl) ⟨477599, by rfl⟩ : syracuseStep 2547197 = 955199) (by norm_num)
theorem B2547221 : Blo 1697549 2547221 := bbase (se 6 (by rfl) ⟨59700, by rfl⟩ : syracuseStep 2547221 = 119401) (by norm_num)
theorem B2653717 : Blo 1697549 2653717 := bbase (se 6 (by rfl) ⟨62196, by rfl⟩ : syracuseStep 2653717 = 124393) (by norm_num)
theorem B2547245 : Blo 1697549 2547245 := bbase (se 3 (by rfl) ⟨477608, by rfl⟩ : syracuseStep 2547245 = 955217) (by norm_num)
theorem B6889013 : Blo 1697549 6889013 := bbase (se 5 (by rfl) ⟨322922, by rfl⟩ : syracuseStep 6889013 = 645845) (by norm_num)
theorem B2547269 : Blo 1697549 2547269 := bbase (se 4 (by rfl) ⟨238806, by rfl⟩ : syracuseStep 2547269 = 477613) (by norm_num)
theorem B2866765 : Blo 1697549 2866765 := bbase (se 3 (by rfl) ⟨537518, by rfl⟩ : syracuseStep 2866765 = 1075037) (by norm_num)
theorem B2547293 : Blo 1697549 2547293 := bbase (se 3 (by rfl) ⟨477617, by rfl⟩ : syracuseStep 2547293 = 955235) (by norm_num)
theorem B5733989 : Blo 1697549 5733989 := bbase (se 4 (by rfl) ⟨537561, by rfl⟩ : syracuseStep 5733989 = 1075123) (by norm_num)
theorem B2547317 : Blo 1697549 2547317 := bbase (se 5 (by rfl) ⟨119405, by rfl⟩ : syracuseStep 2547317 = 238811) (by norm_num)
theorem B2547341 : Blo 1697549 2547341 := bbase (se 3 (by rfl) ⟨477626, by rfl⟩ : syracuseStep 2547341 = 955253) (by norm_num)
theorem B2719381 : Blo 1697549 2719381 := bbase (se 6 (by rfl) ⟨63735, by rfl⟩ : syracuseStep 2719381 = 127471) (by norm_num)
theorem B2547365 : Blo 1697549 2547365 := bbase (se 4 (by rfl) ⟨238815, by rfl⟩ : syracuseStep 2547365 = 477631) (by norm_num)
theorem B2866853 : Blo 1697549 2866853 := bbase (se 4 (by rfl) ⟨268767, by rfl⟩ : syracuseStep 2866853 = 537535) (by norm_num)
theorem B2547389 : Blo 1697549 2547389 := bbase (se 3 (by rfl) ⟨477635, by rfl⟩ : syracuseStep 2547389 = 955271) (by norm_num)
theorem B2547413 : Blo 1697549 2547413 := bbase (se 7 (by rfl) ⟨29852, by rfl⟩ : syracuseStep 2547413 = 59705) (by norm_num)
theorem B55115477 : Blo 1697549 55115477 := bbase (se 7 (by rfl) ⟨645884, by rfl⟩ : syracuseStep 55115477 = 1291769) (by norm_num)
theorem B2547437 : Blo 1697549 2547437 := bbase (se 3 (by rfl) ⟨477644, by rfl⟩ : syracuseStep 2547437 = 955289) (by norm_num)
theorem B2547461 : Blo 1697549 2547461 := bbase (se 4 (by rfl) ⟨238824, by rfl⟩ : syracuseStep 2547461 = 477649) (by norm_num)
theorem B2547485 : Blo 1697549 2547485 := bbase (se 3 (by rfl) ⟨477653, by rfl⟩ : syracuseStep 2547485 = 955307) (by norm_num)
theorem B4300573 : Blo 1697549 4300573 := bbase (se 3 (by rfl) ⟨806357, by rfl⟩ : syracuseStep 4300573 = 1612715) (by norm_num)
theorem B2866981 : Blo 1697549 2866981 := bbase (se 4 (by rfl) ⟨268779, by rfl⟩ : syracuseStep 2866981 = 537559) (by norm_num)
theorem B2547509 : Blo 1697549 2547509 := bbase (se 5 (by rfl) ⟨119414, by rfl⟩ : syracuseStep 2547509 = 238829) (by norm_num)
theorem B2547533 : Blo 1697549 2547533 := bbase (se 3 (by rfl) ⟨477662, by rfl⟩ : syracuseStep 2547533 = 955325) (by norm_num)
theorem B2547557 : Blo 1697549 2547557 := bbase (se 4 (by rfl) ⟨238833, by rfl⟩ : syracuseStep 2547557 = 477667) (by norm_num)
theorem B4079477 : Blo 1697549 4079477 := bbase (se 5 (by rfl) ⟨191225, by rfl⟩ : syracuseStep 4079477 = 382451) (by norm_num)
theorem B2547581 : Blo 1697549 2547581 := bbase (se 3 (by rfl) ⟨477671, by rfl⟩ : syracuseStep 2547581 = 955343) (by norm_num)
theorem B2867069 : Blo 1697549 2867069 := bbase (se 3 (by rfl) ⟨537575, by rfl⟩ : syracuseStep 2867069 = 1075151) (by norm_num)
theorem B4300685 : Blo 1697549 4300685 := bbase (se 3 (by rfl) ⟨806378, by rfl⟩ : syracuseStep 4300685 = 1612757) (by norm_num)
theorem B2547605 : Blo 1697549 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B2547629 : Blo 1697549 2547629 := bbase (se 3 (by rfl) ⟨477680, by rfl⟩ : syracuseStep 2547629 = 955361) (by norm_num)
theorem B2547653 : Blo 1697549 2547653 := bbase (se 4 (by rfl) ⟨238842, by rfl⟩ : syracuseStep 2547653 = 477685) (by norm_num)
theorem B2547677 : Blo 1697549 2547677 := bbase (se 3 (by rfl) ⟨477689, by rfl⟩ : syracuseStep 2547677 = 955379) (by norm_num)
theorem B2547701 : Blo 1697549 2547701 := bbase (se 5 (by rfl) ⟨119423, by rfl⟩ : syracuseStep 2547701 = 238847) (by norm_num)
theorem B9674741 : Blo 1697549 9674741 := bbase (se 5 (by rfl) ⟨453503, by rfl⟩ : syracuseStep 9674741 = 907007) (by norm_num)
theorem B4358141 : Blo 1697549 4358141 := bbase (se 3 (by rfl) ⟨817151, by rfl⟩ : syracuseStep 4358141 = 1634303) (by norm_num)
theorem B2547713 : Blo 1697549 2547713 := bstep (se 2 (by rfl) ⟨955392, by rfl⟩ : syracuseStep 2547713 = 1910785) B1910785
theorem B11780101 : Blo 1697549 11780101 := bstep (se 4 (by rfl) ⟨1104384, by rfl⟩ : syracuseStep 11780101 = 2208769) B2208769
theorem B2547731 : Blo 1697549 2547731 := bstep (se 1 (by rfl) ⟨1910798, by rfl⟩ : syracuseStep 2547731 = 3821597) B3821597
theorem B2547761 : Blo 1697549 2547761 := bstep (se 2 (by rfl) ⟨955410, by rfl⟩ : syracuseStep 2547761 = 1910821) B1910821
theorem B2867251 : Blo 1697549 2867251 := bstep (se 1 (by rfl) ⟨2150438, by rfl⟩ : syracuseStep 2867251 = 4300877) B4300877
theorem B2547779 : Blo 1697549 2547779 := bstep (se 1 (by rfl) ⟨1910834, by rfl⟩ : syracuseStep 2547779 = 3821669) B3821669
theorem B12247109 : Blo 1697549 12247109 := bstep (se 4 (by rfl) ⟨1148166, by rfl⟩ : syracuseStep 12247109 = 2296333) B2296333
theorem B4358225 : Blo 1697549 4358225 := bstep (se 2 (by rfl) ⟨1634334, by rfl⟩ : syracuseStep 4358225 = 3268669) B3268669
theorem B2547809 : Blo 1697549 2547809 := bstep (se 2 (by rfl) ⟨955428, by rfl⟩ : syracuseStep 2547809 = 1910857) B1910857
theorem B8601713 : Blo 1697549 8601713 := bstep (se 2 (by rfl) ⟨3225642, by rfl⟩ : syracuseStep 8601713 = 6451285) B6451285
theorem B2547827 : Blo 1697549 2547827 := bstep (se 1 (by rfl) ⟨1910870, by rfl⟩ : syracuseStep 2547827 = 3821741) B3821741
theorem B2547857 : Blo 1697549 2547857 := bstep (se 2 (by rfl) ⟨955446, by rfl⟩ : syracuseStep 2547857 = 1910893) B1910893
theorem B2719907 : Blo 1697549 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B2547875 : Blo 1697549 2547875 := bstep (se 1 (by rfl) ⟨1910906, by rfl⟩ : syracuseStep 2547875 = 3821813) B3821813
theorem B2547905 : Blo 1697549 2547905 := bstep (se 2 (by rfl) ⟨955464, by rfl⟩ : syracuseStep 2547905 = 1910929) B1910929
theorem B2867393 : Blo 1697549 2867393 := bstep (se 2 (by rfl) ⟨1075272, by rfl⟩ : syracuseStep 2867393 = 2150545) B2150545
theorem B10887365 : Blo 1697549 10887365 := bstep (se 4 (by rfl) ⟨1020690, by rfl⟩ : syracuseStep 10887365 = 2041381) B2041381
theorem B4301009 : Blo 1697549 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B2547923 : Blo 1697549 2547923 := bstep (se 1 (by rfl) ⟨1910942, by rfl⟩ : syracuseStep 2547923 = 3821885) B3821885
theorem B156844259 : Blo 1697549 156844259 := bstep (se 1 (by rfl) ⟨117633194, by rfl⟩ : syracuseStep 156844259 = 235266389) B235266389
theorem B5734637 : Blo 1697549 5734637 := bstep (se 3 (by rfl) ⟨1075244, by rfl⟩ : syracuseStep 5734637 = 2150489) B2150489
theorem B10879217 : Blo 1697549 10879217 := bstep (se 2 (by rfl) ⟨4079706, by rfl⟩ : syracuseStep 10879217 = 8159413) B8159413
theorem B2547953 : Blo 1697549 2547953 := bstep (se 2 (by rfl) ⟨955482, by rfl⟩ : syracuseStep 2547953 = 1910965) B1910965
theorem B2547971 : Blo 1697549 2547971 := bstep (se 1 (by rfl) ⟨1910978, by rfl⟩ : syracuseStep 2547971 = 3821957) B3821957
theorem B4301059 : Blo 1697549 4301059 := bstep (se 1 (by rfl) ⟨3225794, by rfl⟩ : syracuseStep 4301059 = 6451589) B6451589
theorem B2548001 : Blo 1697549 2548001 := bstep (se 2 (by rfl) ⟨955500, by rfl⟩ : syracuseStep 2548001 = 1911001) B1911001
theorem B5734691 : Blo 1697549 5734691 := bstep (se 1 (by rfl) ⟨4301018, by rfl⟩ : syracuseStep 5734691 = 8602037) B8602037
theorem B2548019 : Blo 1697549 2548019 := bstep (se 1 (by rfl) ⟨1911014, by rfl⟩ : syracuseStep 2548019 = 3822029) B3822029
theorem B2867521 : Blo 1697549 2867521 := bstep (se 2 (by rfl) ⟨1075320, by rfl⟩ : syracuseStep 2867521 = 2150641) B2150641
theorem B2548049 : Blo 1697549 2548049 := bstep (se 2 (by rfl) ⟨955518, by rfl⟩ : syracuseStep 2548049 = 1911037) B1911037
theorem B2548067 : Blo 1697549 2548067 := bstep (se 1 (by rfl) ⟨1911050, by rfl⟩ : syracuseStep 2548067 = 3822101) B3822101
theorem B4194659 : Blo 1697549 4194659 := bstep (se 1 (by rfl) ⟨3145994, by rfl⟩ : syracuseStep 4194659 = 6291989) B6291989
theorem B2867555 : Blo 1697549 2867555 := bstep (se 1 (by rfl) ⟨2150666, by rfl⟩ : syracuseStep 2867555 = 4301333) B4301333
theorem B2548097 : Blo 1697549 2548097 := bstep (se 2 (by rfl) ⟨955536, by rfl⟩ : syracuseStep 2548097 = 1911073) B1911073
theorem B5439889 : Blo 1697549 5439889 := bstep (se 2 (by rfl) ⟨2039958, by rfl⟩ : syracuseStep 5439889 = 4079917) B4079917
theorem B4301201 : Blo 1697549 4301201 := bstep (se 2 (by rfl) ⟨1612950, by rfl⟩ : syracuseStep 4301201 = 3225901) B3225901
theorem B2548115 : Blo 1697549 2548115 := bstep (se 1 (by rfl) ⟨1911086, by rfl⟩ : syracuseStep 2548115 = 3822173) B3822173
theorem B2548145 : Blo 1697549 2548145 := bstep (se 2 (by rfl) ⟨955554, by rfl⟩ : syracuseStep 2548145 = 1911109) B1911109
theorem B5972401 : Blo 1697549 5972401 := bstep (se 2 (by rfl) ⟨2239650, by rfl⟩ : syracuseStep 5972401 = 4479301) B4479301
theorem B2548163 : Blo 1697549 2548163 := bstep (se 1 (by rfl) ⟨1911122, by rfl⟩ : syracuseStep 2548163 = 3822245) B3822245
theorem B2548193 : Blo 1697549 2548193 := bstep (se 2 (by rfl) ⟨955572, by rfl⟩ : syracuseStep 2548193 = 1911145) B1911145
theorem B2867683 : Blo 1697549 2867683 := bstep (se 1 (by rfl) ⟨2150762, by rfl⟩ : syracuseStep 2867683 = 4301525) B4301525
theorem B2548211 : Blo 1697549 2548211 := bstep (se 1 (by rfl) ⟨1911158, by rfl⟩ : syracuseStep 2548211 = 3822317) B3822317
theorem B2548241 : Blo 1697549 2548241 := bstep (se 2 (by rfl) ⟨955590, by rfl⟩ : syracuseStep 2548241 = 1911181) B1911181
theorem B2548259 : Blo 1697549 2548259 := bstep (se 1 (by rfl) ⟨1911194, by rfl⟩ : syracuseStep 2548259 = 3822389) B3822389
theorem B5734961 : Blo 1697549 5734961 := bstep (se 2 (by rfl) ⟨2150610, by rfl⟩ : syracuseStep 5734961 = 4301221) B4301221
theorem B31007285 : Blo 1697549 31007285 := bstep (se 5 (by rfl) ⟨1453466, by rfl⟩ : syracuseStep 31007285 = 2906933) B2906933
theorem B2548289 : Blo 1697549 2548289 := bstep (se 2 (by rfl) ⟨955608, by rfl⟩ : syracuseStep 2548289 = 1911217) B1911217
theorem B2548307 : Blo 1697549 2548307 := bstep (se 1 (by rfl) ⟨1911230, by rfl⟩ : syracuseStep 2548307 = 3822461) B3822461
theorem B2450017 : Blo 1697549 2450017 := bstep (se 2 (by rfl) ⟨918756, by rfl⟩ : syracuseStep 2450017 = 1837513) B1837513
theorem B2548337 : Blo 1697549 2548337 := bstep (se 2 (by rfl) ⟨955626, by rfl⟩ : syracuseStep 2548337 = 1911253) B1911253
theorem B2867825 : Blo 1697549 2867825 := bstep (se 2 (by rfl) ⟨1075434, by rfl⟩ : syracuseStep 2867825 = 2150869) B2150869
theorem B2548355 : Blo 1697549 2548355 := bstep (se 1 (by rfl) ⟨1911266, by rfl⟩ : syracuseStep 2548355 = 3822533) B3822533
theorem B2548385 : Blo 1697549 2548385 := bstep (se 2 (by rfl) ⟨955644, by rfl⟩ : syracuseStep 2548385 = 1911289) B1911289
theorem B2548403 : Blo 1697549 2548403 := bstep (se 1 (by rfl) ⟨1911302, by rfl⟩ : syracuseStep 2548403 = 3822605) B3822605
theorem B2548433 : Blo 1697549 2548433 := bstep (se 2 (by rfl) ⟨955662, by rfl⟩ : syracuseStep 2548433 = 1911325) B1911325
theorem B2548451 : Blo 1697549 2548451 := bstep (se 1 (by rfl) ⟨1911338, by rfl⟩ : syracuseStep 2548451 = 3822677) B3822677
theorem B2867953 : Blo 1697549 2867953 := bstep (se 2 (by rfl) ⟨1075482, by rfl⟩ : syracuseStep 2867953 = 2150965) B2150965
theorem B2548481 : Blo 1697549 2548481 := bstep (se 2 (by rfl) ⟨955680, by rfl⟩ : syracuseStep 2548481 = 1911361) B1911361
theorem B10879757 : Blo 1697549 10879757 := bstep (se 3 (by rfl) ⟨2039954, by rfl⟩ : syracuseStep 10879757 = 4079909) B4079909
theorem B2548499 : Blo 1697549 2548499 := bstep (se 1 (by rfl) ⟨1911374, by rfl⟩ : syracuseStep 2548499 = 3822749) B3822749
theorem B2867987 : Blo 1697549 2867987 := bstep (se 1 (by rfl) ⟨2150990, by rfl⟩ : syracuseStep 2867987 = 4301981) B4301981
theorem B4080419 : Blo 1697549 4080419 := bstep (se 1 (by rfl) ⟨3060314, by rfl⟩ : syracuseStep 4080419 = 6120629) B6120629
theorem B5808941 : Blo 1697549 5808941 := bstep (se 3 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 5808941 = 2178353) B2178353
theorem B2548529 : Blo 1697549 2548529 := bstep (se 2 (by rfl) ⟨955698, by rfl⟩ : syracuseStep 2548529 = 1911397) B1911397
theorem B30991157 : Blo 1697549 30991157 := bstep (se 5 (by rfl) ⟨1452710, by rfl⟩ : syracuseStep 30991157 = 2905421) B2905421
theorem B2548547 : Blo 1697549 2548547 := bstep (se 1 (by rfl) ⟨1911410, by rfl⟩ : syracuseStep 2548547 = 3822821) B3822821
theorem B2548577 : Blo 1697549 2548577 := bstep (se 2 (by rfl) ⟨955716, by rfl⟩ : syracuseStep 2548577 = 1911433) B1911433
theorem B2720611 : Blo 1697549 2720611 := bstep (se 1 (by rfl) ⟨2040458, by rfl⟩ : syracuseStep 2720611 = 4080917) B4080917
theorem B2548595 : Blo 1697549 2548595 := bstep (se 1 (by rfl) ⟨1911446, by rfl⟩ : syracuseStep 2548595 = 3822893) B3822893
theorem B2548625 : Blo 1697549 2548625 := bstep (se 2 (by rfl) ⟨955734, by rfl⟩ : syracuseStep 2548625 = 1911469) B1911469
theorem B2548643 : Blo 1697549 2548643 := bstep (se 1 (by rfl) ⟨1911482, by rfl⟩ : syracuseStep 2548643 = 3822965) B3822965
theorem B2548673 : Blo 1697549 2548673 := bstep (se 2 (by rfl) ⟨955752, by rfl⟩ : syracuseStep 2548673 = 1911505) B1911505
theorem B2548691 : Blo 1697549 2548691 := bstep (se 1 (by rfl) ⟨1911518, by rfl⟩ : syracuseStep 2548691 = 3823037) B3823037
theorem B2548721 : Blo 1697549 2548721 := bstep (se 2 (by rfl) ⟨955770, by rfl⟩ : syracuseStep 2548721 = 1911541) B1911541
theorem B2548739 : Blo 1697549 2548739 := bstep (se 1 (by rfl) ⟨1911554, by rfl⟩ : syracuseStep 2548739 = 3823109) B3823109
theorem B2417683 : Blo 1697549 2417683 := bstep (se 1 (by rfl) ⟨1813262, by rfl⟩ : syracuseStep 2417683 = 3626525) B3626525
theorem B2548769 : Blo 1697549 2548769 := bstep (se 2 (by rfl) ⟨955788, by rfl⟩ : syracuseStep 2548769 = 1911577) B1911577
theorem B1909795 : Blo 1697549 1909795 := bstep (se 1 (by rfl) ⟨1432346, by rfl⟩ : syracuseStep 1909795 = 2864693) B2864693
theorem B2548787 : Blo 1697549 2548787 := bstep (se 1 (by rfl) ⟨1911590, by rfl⟩ : syracuseStep 2548787 = 3823181) B3823181
theorem B5735501 : Blo 1697549 5735501 := bstep (se 3 (by rfl) ⟨1075406, by rfl⟩ : syracuseStep 5735501 = 2150813) B2150813
theorem B2548817 : Blo 1697549 2548817 := bstep (se 2 (by rfl) ⟨955806, by rfl⟩ : syracuseStep 2548817 = 1911613) B1911613
theorem B2450531 : Blo 1697549 2450531 := bstep (se 1 (by rfl) ⟨1837898, by rfl⟩ : syracuseStep 2450531 = 3675797) B3675797
theorem B2548835 : Blo 1697549 2548835 := bstep (se 1 (by rfl) ⟨1911626, by rfl⟩ : syracuseStep 2548835 = 3823253) B3823253
theorem B2720881 : Blo 1697549 2720881 := bstep (se 2 (by rfl) ⟨1020330, by rfl⟩ : syracuseStep 2720881 = 2040661) B2040661
theorem B1721459 : Blo 1697549 1721459 := bstep (se 1 (by rfl) ⟨1291094, by rfl⟩ : syracuseStep 1721459 = 2582189) B2582189
theorem B2548865 : Blo 1697549 2548865 := bstep (se 2 (by rfl) ⟨955824, by rfl⟩ : syracuseStep 2548865 = 1911649) B1911649
theorem B5735555 : Blo 1697549 5735555 := bstep (se 1 (by rfl) ⟨4301666, by rfl⟩ : syracuseStep 5735555 = 8603333) B8603333
theorem B2548883 : Blo 1697549 2548883 := bstep (se 1 (by rfl) ⟨1911662, by rfl⟩ : syracuseStep 2548883 = 3823325) B3823325
theorem B4588721 : Blo 1697549 4588721 := bstep (se 2 (by rfl) ⟨1720770, by rfl⟩ : syracuseStep 4588721 = 3441541) B3441541
theorem B2720945 : Blo 1697549 2720945 := bstep (se 2 (by rfl) ⟨1020354, by rfl⟩ : syracuseStep 2720945 = 2040709) B2040709
theorem B1909939 : Blo 1697549 1909939 := bstep (se 1 (by rfl) ⟨1432454, by rfl⟩ : syracuseStep 1909939 = 2864909) B2864909
theorem B2548913 : Blo 1697549 2548913 := bstep (se 2 (by rfl) ⟨955842, by rfl⟩ : syracuseStep 2548913 = 1911685) B1911685
theorem B2548931 : Blo 1697549 2548931 := bstep (se 1 (by rfl) ⟨1911698, by rfl⟩ : syracuseStep 2548931 = 3823397) B3823397
theorem B2548961 : Blo 1697549 2548961 := bstep (se 2 (by rfl) ⟨955860, by rfl⟩ : syracuseStep 2548961 = 1911721) B1911721
theorem B6448355 : Blo 1697549 6448355 := bstep (se 1 (by rfl) ⟨4836266, by rfl⟩ : syracuseStep 6448355 = 9672533) B9672533
theorem B6448369 : Blo 1697549 6448369 := bstep (se 2 (by rfl) ⟨2418138, by rfl⟩ : syracuseStep 6448369 = 4836277) B4836277
theorem B2548979 : Blo 1697549 2548979 := bstep (se 1 (by rfl) ⟨1911734, by rfl⟩ : syracuseStep 2548979 = 3823469) B3823469
theorem B2549009 : Blo 1697549 2549009 := bstep (se 2 (by rfl) ⟨955878, by rfl⟩ : syracuseStep 2549009 = 1911757) B1911757
theorem B2549027 : Blo 1697549 2549027 := bstep (se 1 (by rfl) ⟨1911770, by rfl⟩ : syracuseStep 2549027 = 3823541) B3823541
theorem B2549057 : Blo 1697549 2549057 := bstep (se 2 (by rfl) ⟨955896, by rfl⟩ : syracuseStep 2549057 = 1911793) B1911793
theorem B1910083 : Blo 1697549 1910083 := bstep (se 1 (by rfl) ⟨1432562, by rfl⟩ : syracuseStep 1910083 = 2865125) B2865125
theorem B4834637 : Blo 1697549 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B2549075 : Blo 1697549 2549075 := bstep (se 1 (by rfl) ⟨1911806, by rfl⟩ : syracuseStep 2549075 = 3823613) B3823613
theorem B9807203 : Blo 1697549 9807203 := bstep (se 1 (by rfl) ⟨7355402, by rfl⟩ : syracuseStep 9807203 = 14710805) B14710805
theorem B2549105 : Blo 1697549 2549105 := bstep (se 2 (by rfl) ⟨955914, by rfl⟩ : syracuseStep 2549105 = 1911829) B1911829
theorem B2549123 : Blo 1697549 2549123 := bstep (se 1 (by rfl) ⟨1911842, by rfl⟩ : syracuseStep 2549123 = 3823685) B3823685
theorem B5735825 : Blo 1697549 5735825 := bstep (se 2 (by rfl) ⟨2150934, by rfl⟩ : syracuseStep 5735825 = 4301869) B4301869
theorem B2549153 : Blo 1697549 2549153 := bstep (se 2 (by rfl) ⟨955932, by rfl⟩ : syracuseStep 2549153 = 1911865) B1911865
theorem B2549171 : Blo 1697549 2549171 := bstep (se 1 (by rfl) ⟨1911878, by rfl⟩ : syracuseStep 2549171 = 3823757) B3823757
theorem B2549201 : Blo 1697549 2549201 := bstep (se 2 (by rfl) ⟨955950, by rfl⟩ : syracuseStep 2549201 = 1911901) B1911901
theorem B1910227 : Blo 1697549 1910227 := bstep (se 1 (by rfl) ⟨1432670, by rfl⟩ : syracuseStep 1910227 = 2865341) B2865341
theorem B2549219 : Blo 1697549 2549219 := bstep (se 1 (by rfl) ⟨1911914, by rfl⟩ : syracuseStep 2549219 = 3823829) B3823829
theorem B2549249 : Blo 1697549 2549249 := bstep (se 2 (by rfl) ⟨955968, by rfl⟩ : syracuseStep 2549249 = 1911937) B1911937
theorem B4834819 : Blo 1697549 4834819 := bstep (se 1 (by rfl) ⟨3626114, by rfl⟩ : syracuseStep 4834819 = 7252229) B7252229
theorem B13780493 : Blo 1697549 13780493 := bstep (se 3 (by rfl) ⟨2583842, by rfl⟩ : syracuseStep 13780493 = 5167685) B5167685
theorem B2549267 : Blo 1697549 2549267 := bstep (se 1 (by rfl) ⟨1911950, by rfl⟩ : syracuseStep 2549267 = 3823901) B3823901
theorem B8603171 : Blo 1697549 8603171 := bstep (se 1 (by rfl) ⟨6452378, by rfl⟩ : syracuseStep 8603171 = 12904757) B12904757
theorem B5441069 : Blo 1697549 5441069 := bstep (se 3 (by rfl) ⟨1020200, by rfl⟩ : syracuseStep 5441069 = 2040401) B2040401
theorem B4834865 : Blo 1697549 4834865 := bstep (se 2 (by rfl) ⟨1813074, by rfl⟩ : syracuseStep 4834865 = 3626149) B3626149
theorem B2549297 : Blo 1697549 2549297 := bstep (se 2 (by rfl) ⟨955986, by rfl⟩ : syracuseStep 2549297 = 1911973) B1911973
theorem B60483125 : Blo 1697549 60483125 := bstep (se 5 (by rfl) ⟨2835146, by rfl⟩ : syracuseStep 60483125 = 5670293) B5670293
theorem B2549315 : Blo 1697549 2549315 := bstep (se 1 (by rfl) ⟨1911986, by rfl⟩ : syracuseStep 2549315 = 3823973) B3823973
theorem B1910371 : Blo 1697549 1910371 := bstep (se 1 (by rfl) ⟨1432778, by rfl⟩ : syracuseStep 1910371 = 2865557) B2865557
theorem B2295425 : Blo 1697549 2295425 := bstep (se 2 (by rfl) ⟨860784, by rfl⟩ : syracuseStep 2295425 = 1721569) B1721569
theorem B3270385 : Blo 1697549 3270385 := bstep (se 2 (by rfl) ⟨1226394, by rfl⟩ : syracuseStep 3270385 = 2452789) B2452789
theorem B1910515 : Blo 1697549 1910515 := bstep (se 1 (by rfl) ⟨1432886, by rfl⟩ : syracuseStep 1910515 = 2865773) B2865773
theorem B1697555 : Blo 1697549 1697555 := bstep (se 1 (by rfl) ⟨1273166, by rfl⟩ : syracuseStep 1697555 = 2546333) B2546333
theorem B1697571 : Blo 1697549 1697571 := bstep (se 1 (by rfl) ⟨1273178, by rfl⟩ : syracuseStep 1697571 = 2546357) B2546357
theorem B1697587 : Blo 1697549 1697587 := bstep (se 1 (by rfl) ⟨1273190, by rfl⟩ : syracuseStep 1697587 = 2546381) B2546381
theorem B1697603 : Blo 1697549 1697603 := bstep (se 1 (by rfl) ⟨1273202, by rfl⟩ : syracuseStep 1697603 = 2546405) B2546405
theorem B4589389 : Blo 1697549 4589389 := bstep (se 3 (by rfl) ⟨860510, by rfl⟩ : syracuseStep 4589389 = 1721021) B1721021
theorem B1697619 : Blo 1697549 1697619 := bstep (se 1 (by rfl) ⟨1273214, by rfl⟩ : syracuseStep 1697619 = 2546429) B2546429
theorem B1697635 : Blo 1697549 1697635 := bstep (se 1 (by rfl) ⟨1273226, by rfl⟩ : syracuseStep 1697635 = 2546453) B2546453
theorem B2041699 : Blo 1697549 2041699 := bstep (se 1 (by rfl) ⟨1531274, by rfl⟩ : syracuseStep 2041699 = 3062549) B3062549
theorem B1697651 : Blo 1697549 1697651 := bstep (se 1 (by rfl) ⟨1273238, by rfl⟩ : syracuseStep 1697651 = 2546477) B2546477
theorem B1697667 : Blo 1697549 1697667 := bstep (se 1 (by rfl) ⟨1273250, by rfl⟩ : syracuseStep 1697667 = 2546501) B2546501
theorem B1910659 : Blo 1697549 1910659 := bstep (se 1 (by rfl) ⟨1432994, by rfl⟩ : syracuseStep 1910659 = 2865989) B2865989
theorem B4081553 : Blo 1697549 4081553 := bstep (se 2 (by rfl) ⟨1530582, by rfl⟩ : syracuseStep 4081553 = 3061165) B3061165
theorem B1697683 : Blo 1697549 1697683 := bstep (se 1 (by rfl) ⟨1273262, by rfl⟩ : syracuseStep 1697683 = 2546525) B2546525
theorem B1697699 : Blo 1697549 1697699 := bstep (se 1 (by rfl) ⟨1273274, by rfl⟩ : syracuseStep 1697699 = 2546549) B2546549
theorem B1697715 : Blo 1697549 1697715 := bstep (se 1 (by rfl) ⟨1273286, by rfl⟩ : syracuseStep 1697715 = 2546573) B2546573
theorem B19343285 : Blo 1697549 19343285 := bstep (se 5 (by rfl) ⟨906716, by rfl⟩ : syracuseStep 19343285 = 1813433) B1813433
theorem B1697731 : Blo 1697549 1697731 := bstep (se 1 (by rfl) ⟨1273298, by rfl⟩ : syracuseStep 1697731 = 2546597) B2546597
theorem B1697747 : Blo 1697549 1697747 := bstep (se 1 (by rfl) ⟨1273310, by rfl⟩ : syracuseStep 1697747 = 2546621) B2546621
theorem B3819491 : Blo 1697549 3819491 := bstep (se 1 (by rfl) ⟨2864618, by rfl⟩ : syracuseStep 3819491 = 5729237) B5729237
theorem B1697763 : Blo 1697549 1697763 := bstep (se 1 (by rfl) ⟨1273322, by rfl⟩ : syracuseStep 1697763 = 2546645) B2546645
theorem B6375395 : Blo 1697549 6375395 := bstep (se 1 (by rfl) ⟨4781546, by rfl⟩ : syracuseStep 6375395 = 9563093) B9563093
theorem B12240881 : Blo 1697549 12240881 := bstep (se 2 (by rfl) ⟨4590330, by rfl⟩ : syracuseStep 12240881 = 9180661) B9180661
theorem B1697779 : Blo 1697549 1697779 := bstep (se 1 (by rfl) ⟨1273334, by rfl⟩ : syracuseStep 1697779 = 2546669) B2546669
theorem B1697795 : Blo 1697549 1697795 := bstep (se 1 (by rfl) ⟨1273346, by rfl⟩ : syracuseStep 1697795 = 2546693) B2546693
theorem B1697811 : Blo 1697549 1697811 := bstep (se 1 (by rfl) ⟨1273358, by rfl⟩ : syracuseStep 1697811 = 2546717) B2546717
theorem B1910803 : Blo 1697549 1910803 := bstep (se 1 (by rfl) ⟨1433102, by rfl⟩ : syracuseStep 1910803 = 2866205) B2866205
theorem B1697827 : Blo 1697549 1697827 := bstep (se 1 (by rfl) ⟨1273370, by rfl⟩ : syracuseStep 1697827 = 2546741) B2546741
theorem B1697843 : Blo 1697549 1697843 := bstep (se 1 (by rfl) ⟨1273382, by rfl⟩ : syracuseStep 1697843 = 2546765) B2546765
theorem B1697859 : Blo 1697549 1697859 := bstep (se 1 (by rfl) ⟨1273394, by rfl⟩ : syracuseStep 1697859 = 2546789) B2546789
theorem B1697875 : Blo 1697549 1697875 := bstep (se 1 (by rfl) ⟨1273406, by rfl⟩ : syracuseStep 1697875 = 2546813) B2546813
theorem B1697891 : Blo 1697549 1697891 := bstep (se 1 (by rfl) ⟨1273418, by rfl⟩ : syracuseStep 1697891 = 2546837) B2546837
theorem B2295905 : Blo 1697549 2295905 := bstep (se 2 (by rfl) ⟨860964, by rfl⟩ : syracuseStep 2295905 = 1721929) B1721929
theorem B10889315 : Blo 1697549 10889315 := bstep (se 1 (by rfl) ⟨8166986, by rfl⟩ : syracuseStep 10889315 = 16333973) B16333973
theorem B1697907 : Blo 1697549 1697907 := bstep (se 1 (by rfl) ⟨1273430, by rfl⟩ : syracuseStep 1697907 = 2546861) B2546861
theorem B2418817 : Blo 1697549 2418817 := bstep (se 2 (by rfl) ⟨907056, by rfl⟩ : syracuseStep 2418817 = 1814113) B1814113
theorem B1697923 : Blo 1697549 1697923 := bstep (se 1 (by rfl) ⟨1273442, by rfl⟩ : syracuseStep 1697923 = 2546885) B2546885
theorem B5163149 : Blo 1697549 5163149 := bstep (se 3 (by rfl) ⟨968090, by rfl⟩ : syracuseStep 5163149 = 1936181) B1936181
theorem B29419661 : Blo 1697549 29419661 := bstep (se 3 (by rfl) ⟨5516186, by rfl⟩ : syracuseStep 29419661 = 11032373) B11032373
theorem B1697939 : Blo 1697549 1697939 := bstep (se 1 (by rfl) ⟨1273454, by rfl⟩ : syracuseStep 1697939 = 2546909) B2546909
theorem B1697955 : Blo 1697549 1697955 := bstep (se 1 (by rfl) ⟨1273466, by rfl⟩ : syracuseStep 1697955 = 2546933) B2546933
theorem B1910947 : Blo 1697549 1910947 := bstep (se 1 (by rfl) ⟨1433210, by rfl⟩ : syracuseStep 1910947 = 2866421) B2866421
theorem B5163185 : Blo 1697549 5163185 := bstep (se 2 (by rfl) ⟨1936194, by rfl⟩ : syracuseStep 5163185 = 3872389) B3872389
theorem B1697971 : Blo 1697549 1697971 := bstep (se 1 (by rfl) ⟨1273478, by rfl⟩ : syracuseStep 1697971 = 2546957) B2546957
theorem B1697987 : Blo 1697549 1697987 := bstep (se 1 (by rfl) ⟨1273490, by rfl⟩ : syracuseStep 1697987 = 2546981) B2546981
theorem B1698003 : Blo 1697549 1698003 := bstep (se 1 (by rfl) ⟨1273502, by rfl⟩ : syracuseStep 1698003 = 2547005) B2547005
theorem B2418913 : Blo 1697549 2418913 := bstep (se 2 (by rfl) ⟨907092, by rfl⟩ : syracuseStep 2418913 = 1814185) B1814185
theorem B1698019 : Blo 1697549 1698019 := bstep (se 1 (by rfl) ⟨1273514, by rfl⟩ : syracuseStep 1698019 = 2547029) B2547029
theorem B3819761 : Blo 1697549 3819761 := bstep (se 2 (by rfl) ⟨1432410, by rfl⟩ : syracuseStep 3819761 = 2864821) B2864821
theorem B1698035 : Blo 1697549 1698035 := bstep (se 1 (by rfl) ⟨1273526, by rfl⟩ : syracuseStep 1698035 = 2547053) B2547053
theorem B3819779 : Blo 1697549 3819779 := bstep (se 1 (by rfl) ⟨2864834, by rfl⟩ : syracuseStep 3819779 = 5729669) B5729669
theorem B1698051 : Blo 1697549 1698051 := bstep (se 1 (by rfl) ⟨1273538, by rfl⟩ : syracuseStep 1698051 = 2547077) B2547077
theorem B1698067 : Blo 1697549 1698067 := bstep (se 1 (by rfl) ⟨1273550, by rfl⟩ : syracuseStep 1698067 = 2547101) B2547101
theorem B1698083 : Blo 1697549 1698083 := bstep (se 1 (by rfl) ⟨1273562, by rfl⟩ : syracuseStep 1698083 = 2547125) B2547125
theorem B1698099 : Blo 1697549 1698099 := bstep (se 1 (by rfl) ⟨1273574, by rfl⟩ : syracuseStep 1698099 = 2547149) B2547149
theorem B1911091 : Blo 1697549 1911091 := bstep (se 1 (by rfl) ⟨1433318, by rfl⟩ : syracuseStep 1911091 = 2866637) B2866637
theorem B1698115 : Blo 1697549 1698115 := bstep (se 1 (by rfl) ⟨1273586, by rfl⟩ : syracuseStep 1698115 = 2547173) B2547173
theorem B1698131 : Blo 1697549 1698131 := bstep (se 1 (by rfl) ⟨1273598, by rfl⟩ : syracuseStep 1698131 = 2547197) B2547197
theorem B2148707 : Blo 1697549 2148707 := bstep (se 1 (by rfl) ⟨1611530, by rfl⟩ : syracuseStep 2148707 = 3223061) B3223061
theorem B1698147 : Blo 1697549 1698147 := bstep (se 1 (by rfl) ⟨1273610, by rfl⟩ : syracuseStep 1698147 = 2547221) B2547221
theorem B1698163 : Blo 1697549 1698163 := bstep (se 1 (by rfl) ⟨1273622, by rfl⟩ : syracuseStep 1698163 = 2547245) B2547245
theorem B1698179 : Blo 1697549 1698179 := bstep (se 1 (by rfl) ⟨1273634, by rfl⟩ : syracuseStep 1698179 = 2547269) B2547269
theorem B1698195 : Blo 1697549 1698195 := bstep (se 1 (by rfl) ⟨1273646, by rfl⟩ : syracuseStep 1698195 = 2547293) B2547293
theorem B1698211 : Blo 1697549 1698211 := bstep (se 1 (by rfl) ⟨1273658, by rfl⟩ : syracuseStep 1698211 = 2547317) B2547317
theorem B1698227 : Blo 1697549 1698227 := bstep (se 1 (by rfl) ⟨1273670, by rfl⟩ : syracuseStep 1698227 = 2547341) B2547341
theorem B1698243 : Blo 1697549 1698243 := bstep (se 1 (by rfl) ⟨1273682, by rfl⟩ : syracuseStep 1698243 = 2547365) B2547365
theorem B1911235 : Blo 1697549 1911235 := bstep (se 1 (by rfl) ⟨1433426, by rfl⟩ : syracuseStep 1911235 = 2866853) B2866853
theorem B1698259 : Blo 1697549 1698259 := bstep (se 1 (by rfl) ⟨1273694, by rfl⟩ : syracuseStep 1698259 = 2547389) B2547389
theorem B9669091 : Blo 1697549 9669091 := bstep (se 1 (by rfl) ⟨7251818, by rfl⟩ : syracuseStep 9669091 = 14503637) B14503637
theorem B6883811 : Blo 1697549 6883811 := bstep (se 1 (by rfl) ⟨5162858, by rfl⟩ : syracuseStep 6883811 = 10325717) B10325717
theorem B1698275 : Blo 1697549 1698275 := bstep (se 1 (by rfl) ⟨1273706, by rfl⟩ : syracuseStep 1698275 = 2547413) B2547413
theorem B36743651 : Blo 1697549 36743651 := bstep (se 1 (by rfl) ⟨27557738, by rfl⟩ : syracuseStep 36743651 = 55115477) B55115477
theorem B1698291 : Blo 1697549 1698291 := bstep (se 1 (by rfl) ⟨1273718, by rfl⟩ : syracuseStep 1698291 = 2547437) B2547437
theorem B1698307 : Blo 1697549 1698307 := bstep (se 1 (by rfl) ⟨1273730, by rfl⟩ : syracuseStep 1698307 = 2547461) B2547461
theorem B3820049 : Blo 1697549 3820049 := bstep (se 2 (by rfl) ⟨1432518, by rfl⟩ : syracuseStep 3820049 = 2865037) B2865037
theorem B1698323 : Blo 1697549 1698323 := bstep (se 1 (by rfl) ⟨1273742, by rfl⟩ : syracuseStep 1698323 = 2547485) B2547485
theorem B3820067 : Blo 1697549 3820067 := bstep (se 1 (by rfl) ⟨2865050, by rfl⟩ : syracuseStep 3820067 = 5730101) B5730101
theorem B1698339 : Blo 1697549 1698339 := bstep (se 1 (by rfl) ⟨1273754, by rfl⟩ : syracuseStep 1698339 = 2547509) B2547509
theorem B1698355 : Blo 1697549 1698355 := bstep (se 1 (by rfl) ⟨1273766, by rfl⟩ : syracuseStep 1698355 = 2547533) B2547533
theorem B1698371 : Blo 1697549 1698371 := bstep (se 1 (by rfl) ⟨1273778, by rfl⟩ : syracuseStep 1698371 = 2547557) B2547557
theorem B1698387 : Blo 1697549 1698387 := bstep (se 1 (by rfl) ⟨1273790, by rfl⟩ : syracuseStep 1698387 = 2547581) B2547581
theorem B1911379 : Blo 1697549 1911379 := bstep (se 1 (by rfl) ⟨1433534, by rfl⟩ : syracuseStep 1911379 = 2867069) B2867069
theorem B1698403 : Blo 1697549 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B1698419 : Blo 1697549 1698419 := bstep (se 1 (by rfl) ⟨1273814, by rfl⟩ : syracuseStep 1698419 = 2547629) B2547629
theorem B1698435 : Blo 1697549 1698435 := bstep (se 1 (by rfl) ⟨1273826, by rfl⟩ : syracuseStep 1698435 = 2547653) B2547653
theorem B2583185 : Blo 1697549 2583185 := bstep (se 2 (by rfl) ⟨968694, by rfl⟩ : syracuseStep 2583185 = 1937389) B1937389
theorem B4082321 : Blo 1697549 4082321 := bstep (se 2 (by rfl) ⟨1530870, by rfl⟩ : syracuseStep 4082321 = 3061741) B3061741
theorem B1698451 : Blo 1697549 1698451 := bstep (se 1 (by rfl) ⟨1273838, by rfl⟩ : syracuseStep 1698451 = 2547677) B2547677
theorem B1698467 : Blo 1697549 1698467 := bstep (se 1 (by rfl) ⟨1273850, by rfl⟩ : syracuseStep 1698467 = 2547701) B2547701
theorem B6449827 : Blo 1697549 6449827 := bstep (se 1 (by rfl) ⟨4837370, by rfl⟩ : syracuseStep 6449827 = 9674741) B9674741
theorem B11627185 : Blo 1697549 11627185 := bstep (se 2 (by rfl) ⟨4360194, by rfl⟩ : syracuseStep 11627185 = 8720389) B8720389
theorem B1698483 : Blo 1697549 1698483 := bstep (se 1 (by rfl) ⟨1273862, by rfl⟩ : syracuseStep 1698483 = 2547725) B2547725
theorem B1698499 : Blo 1697549 1698499 := bstep (se 1 (by rfl) ⟨1273874, by rfl⟩ : syracuseStep 1698499 = 2547749) B2547749
theorem B2419409 : Blo 1697549 2419409 := bstep (se 2 (by rfl) ⟨907278, by rfl⟩ : syracuseStep 2419409 = 1814557) B1814557
theorem B1698515 : Blo 1697549 1698515 := bstep (se 1 (by rfl) ⟨1273886, by rfl⟩ : syracuseStep 1698515 = 2547773) B2547773
theorem B1698531 : Blo 1697549 1698531 := bstep (se 1 (by rfl) ⟨1273898, by rfl⟩ : syracuseStep 1698531 = 2547797) B2547797
theorem B1911523 : Blo 1697549 1911523 := bstep (se 1 (by rfl) ⟨1433642, by rfl⟩ : syracuseStep 1911523 = 2867285) B2867285
theorem B1698547 : Blo 1697549 1698547 := bstep (se 1 (by rfl) ⟨1273910, by rfl⟩ : syracuseStep 1698547 = 2547821) B2547821
theorem B1698563 : Blo 1697549 1698563 := bstep (se 1 (by rfl) ⟨1273922, by rfl⟩ : syracuseStep 1698563 = 2547845) B2547845
theorem B1698579 : Blo 1697549 1698579 := bstep (se 1 (by rfl) ⟨1273934, by rfl⟩ : syracuseStep 1698579 = 2547869) B2547869
theorem B1698595 : Blo 1697549 1698595 := bstep (se 1 (by rfl) ⟨1273946, by rfl⟩ : syracuseStep 1698595 = 2547893) B2547893
theorem B3820337 : Blo 1697549 3820337 := bstep (se 2 (by rfl) ⟨1432626, by rfl⟩ : syracuseStep 3820337 = 2865253) B2865253
theorem B1698611 : Blo 1697549 1698611 := bstep (se 1 (by rfl) ⟨1273958, by rfl⟩ : syracuseStep 1698611 = 2547917) B2547917
theorem B3820355 : Blo 1697549 3820355 := bstep (se 1 (by rfl) ⟨2865266, by rfl⟩ : syracuseStep 3820355 = 5730533) B5730533
theorem B1698627 : Blo 1697549 1698627 := bstep (se 1 (by rfl) ⟨1273970, by rfl⟩ : syracuseStep 1698627 = 2547941) B2547941
theorem B1698643 : Blo 1697549 1698643 := bstep (se 1 (by rfl) ⟨1273982, by rfl⟩ : syracuseStep 1698643 = 2547965) B2547965
theorem B1698659 : Blo 1697549 1698659 := bstep (se 1 (by rfl) ⟨1273994, by rfl⟩ : syracuseStep 1698659 = 2547989) B2547989
theorem B1698675 : Blo 1697549 1698675 := bstep (se 1 (by rfl) ⟨1274006, by rfl⟩ : syracuseStep 1698675 = 2548013) B2548013
theorem B1911667 : Blo 1697549 1911667 := bstep (se 1 (by rfl) ⟨1433750, by rfl⟩ : syracuseStep 1911667 = 2867501) B2867501
theorem B1698691 : Blo 1697549 1698691 := bstep (se 1 (by rfl) ⟨1274018, by rfl⟩ : syracuseStep 1698691 = 2548037) B2548037
theorem B1698707 : Blo 1697549 1698707 := bstep (se 1 (by rfl) ⟨1274030, by rfl⟩ : syracuseStep 1698707 = 2548061) B2548061
theorem B1698723 : Blo 1697549 1698723 := bstep (se 1 (by rfl) ⟨1274042, by rfl⟩ : syracuseStep 1698723 = 2548085) B2548085
theorem B1698739 : Blo 1697549 1698739 := bstep (se 1 (by rfl) ⟨1274054, by rfl⟩ : syracuseStep 1698739 = 2548109) B2548109
theorem B1698755 : Blo 1697549 1698755 := bstep (se 1 (by rfl) ⟨1274066, by rfl⟩ : syracuseStep 1698755 = 2548133) B2548133
theorem B1698771 : Blo 1697549 1698771 := bstep (se 1 (by rfl) ⟨1274078, by rfl⟩ : syracuseStep 1698771 = 2548157) B2548157
theorem B4836323 : Blo 1697549 4836323 := bstep (se 1 (by rfl) ⟨3627242, by rfl⟩ : syracuseStep 4836323 = 7254485) B7254485
theorem B1698787 : Blo 1697549 1698787 := bstep (se 1 (by rfl) ⟨1274090, by rfl⟩ : syracuseStep 1698787 = 2548181) B2548181
theorem B9669617 : Blo 1697549 9669617 := bstep (se 2 (by rfl) ⟨3626106, by rfl⟩ : syracuseStep 9669617 = 7252213) B7252213
theorem B1698803 : Blo 1697549 1698803 := bstep (se 1 (by rfl) ⟨1274102, by rfl⟩ : syracuseStep 1698803 = 2548205) B2548205
theorem B1698819 : Blo 1697549 1698819 := bstep (se 1 (by rfl) ⟨1274114, by rfl⟩ : syracuseStep 1698819 = 2548229) B2548229
theorem B1911811 : Blo 1697549 1911811 := bstep (se 1 (by rfl) ⟨1433858, by rfl⟩ : syracuseStep 1911811 = 2867717) B2867717
theorem B1698835 : Blo 1697549 1698835 := bstep (se 1 (by rfl) ⟨1274126, by rfl⟩ : syracuseStep 1698835 = 2548253) B2548253
theorem B2149411 : Blo 1697549 2149411 := bstep (se 1 (by rfl) ⟨1612058, by rfl⟩ : syracuseStep 2149411 = 3224117) B3224117
theorem B1698851 : Blo 1697549 1698851 := bstep (se 1 (by rfl) ⟨1274138, by rfl⟩ : syracuseStep 1698851 = 2548277) B2548277
theorem B8596529 : Blo 1697549 8596529 := bstep (se 2 (by rfl) ⟨3223698, by rfl⟩ : syracuseStep 8596529 = 6447397) B6447397
theorem B1698867 : Blo 1697549 1698867 := bstep (se 1 (by rfl) ⟨1274150, by rfl⟩ : syracuseStep 1698867 = 2548301) B2548301
theorem B1698883 : Blo 1697549 1698883 := bstep (se 1 (by rfl) ⟨1274162, by rfl⟩ : syracuseStep 1698883 = 2548325) B2548325
theorem B3820625 : Blo 1697549 3820625 := bstep (se 2 (by rfl) ⟨1432734, by rfl⟩ : syracuseStep 3820625 = 2865469) B2865469
theorem B1698899 : Blo 1697549 1698899 := bstep (se 1 (by rfl) ⟨1274174, by rfl⟩ : syracuseStep 1698899 = 2548349) B2548349
theorem B3820643 : Blo 1697549 3820643 := bstep (se 1 (by rfl) ⟨2865482, by rfl⟩ : syracuseStep 3820643 = 5730965) B5730965
theorem B1698915 : Blo 1697549 1698915 := bstep (se 1 (by rfl) ⟨1274186, by rfl⟩ : syracuseStep 1698915 = 2548373) B2548373
theorem B1698931 : Blo 1697549 1698931 := bstep (se 1 (by rfl) ⟨1274198, by rfl⟩ : syracuseStep 1698931 = 2548397) B2548397
theorem B2149507 : Blo 1697549 2149507 := bstep (se 1 (by rfl) ⟨1612130, by rfl⟩ : syracuseStep 2149507 = 3224261) B3224261
theorem B1698947 : Blo 1697549 1698947 := bstep (se 1 (by rfl) ⟨1274210, by rfl⟩ : syracuseStep 1698947 = 2548421) B2548421
theorem B1698963 : Blo 1697549 1698963 := bstep (se 1 (by rfl) ⟨1274222, by rfl⟩ : syracuseStep 1698963 = 2548445) B2548445
theorem B1911955 : Blo 1697549 1911955 := bstep (se 1 (by rfl) ⟨1433966, by rfl⟩ : syracuseStep 1911955 = 2867933) B2867933
theorem B1698979 : Blo 1697549 1698979 := bstep (se 1 (by rfl) ⟨1274234, by rfl⟩ : syracuseStep 1698979 = 2548469) B2548469
theorem B5729453 : Blo 1697549 5729453 := bstep (se 3 (by rfl) ⟨1074272, by rfl⟩ : syracuseStep 5729453 = 2148545) B2148545
theorem B8277169 : Blo 1697549 8277169 := bstep (se 2 (by rfl) ⟨3103938, by rfl⟩ : syracuseStep 8277169 = 6207877) B6207877
theorem B1698995 : Blo 1697549 1698995 := bstep (se 1 (by rfl) ⟨1274246, by rfl⟩ : syracuseStep 1698995 = 2548493) B2548493
theorem B1699011 : Blo 1697549 1699011 := bstep (se 1 (by rfl) ⟨1274258, by rfl⟩ : syracuseStep 1699011 = 2548517) B2548517
theorem B1699027 : Blo 1697549 1699027 := bstep (se 1 (by rfl) ⟨1274270, by rfl⟩ : syracuseStep 1699027 = 2548541) B2548541
theorem B5729507 : Blo 1697549 5729507 := bstep (se 1 (by rfl) ⟨4297130, by rfl⟩ : syracuseStep 5729507 = 8594261) B8594261
theorem B7351523 : Blo 1697549 7351523 := bstep (se 1 (by rfl) ⟨5513642, by rfl⟩ : syracuseStep 7351523 = 11027285) B11027285
theorem B1699043 : Blo 1697549 1699043 := bstep (se 1 (by rfl) ⟨1274282, by rfl⟩ : syracuseStep 1699043 = 2548565) B2548565
theorem B1699059 : Blo 1697549 1699059 := bstep (se 1 (by rfl) ⟨1274294, by rfl⟩ : syracuseStep 1699059 = 2548589) B2548589
theorem B1699075 : Blo 1697549 1699075 := bstep (se 1 (by rfl) ⟨1274306, by rfl⟩ : syracuseStep 1699075 = 2548613) B2548613
theorem B1699091 : Blo 1697549 1699091 := bstep (se 1 (by rfl) ⟨1274318, by rfl⟩ : syracuseStep 1699091 = 2548637) B2548637
theorem B5442851 : Blo 1697549 5442851 := bstep (se 1 (by rfl) ⟨4082138, by rfl⟩ : syracuseStep 5442851 = 8164277) B8164277
theorem B1699107 : Blo 1697549 1699107 := bstep (se 1 (by rfl) ⟨1274330, by rfl⟩ : syracuseStep 1699107 = 2548661) B2548661
theorem B1699123 : Blo 1697549 1699123 := bstep (se 1 (by rfl) ⟨1274342, by rfl⟩ : syracuseStep 1699123 = 2548685) B2548685
theorem B1699139 : Blo 1697549 1699139 := bstep (se 1 (by rfl) ⟨1274354, by rfl⟩ : syracuseStep 1699139 = 2548709) B2548709
theorem B1699155 : Blo 1697549 1699155 := bstep (se 1 (by rfl) ⟨1274366, by rfl⟩ : syracuseStep 1699155 = 2548733) B2548733
theorem B1699171 : Blo 1697549 1699171 := bstep (se 1 (by rfl) ⟨1274378, by rfl⟩ : syracuseStep 1699171 = 2548757) B2548757
theorem B3820913 : Blo 1697549 3820913 := bstep (se 2 (by rfl) ⟨1432842, by rfl⟩ : syracuseStep 3820913 = 2865685) B2865685
theorem B1699187 : Blo 1697549 1699187 := bstep (se 1 (by rfl) ⟨1274390, by rfl⟩ : syracuseStep 1699187 = 2548781) B2548781
theorem B3820931 : Blo 1697549 3820931 := bstep (se 1 (by rfl) ⟨2865698, by rfl⟩ : syracuseStep 3820931 = 5731397) B5731397
theorem B1699203 : Blo 1697549 1699203 := bstep (se 1 (by rfl) ⟨1274402, by rfl⟩ : syracuseStep 1699203 = 2548805) B2548805
theorem B1699219 : Blo 1697549 1699219 := bstep (se 1 (by rfl) ⟨1274414, by rfl⟩ : syracuseStep 1699219 = 2548829) B2548829
theorem B1699235 : Blo 1697549 1699235 := bstep (se 1 (by rfl) ⟨1274426, by rfl⟩ : syracuseStep 1699235 = 2548853) B2548853
theorem B1699251 : Blo 1697549 1699251 := bstep (se 1 (by rfl) ⟨1274438, by rfl⟩ : syracuseStep 1699251 = 2548877) B2548877
theorem B1699267 : Blo 1697549 1699267 := bstep (se 1 (by rfl) ⟨1274450, by rfl⟩ : syracuseStep 1699267 = 2548901) B2548901
theorem B1699283 : Blo 1697549 1699283 := bstep (se 1 (by rfl) ⟨1274462, by rfl⟩ : syracuseStep 1699283 = 2548925) B2548925
theorem B1699299 : Blo 1697549 1699299 := bstep (se 1 (by rfl) ⟨1274474, by rfl⟩ : syracuseStep 1699299 = 2548949) B2548949
theorem B5729777 : Blo 1697549 5729777 := bstep (se 2 (by rfl) ⟨2148666, by rfl⟩ : syracuseStep 5729777 = 4297333) B4297333
theorem B1699315 : Blo 1697549 1699315 := bstep (se 1 (by rfl) ⟨1274486, by rfl⟩ : syracuseStep 1699315 = 2548973) B2548973
theorem B1699331 : Blo 1697549 1699331 := bstep (se 1 (by rfl) ⟨1274498, by rfl⟩ : syracuseStep 1699331 = 2548997) B2548997
theorem B1699347 : Blo 1697549 1699347 := bstep (se 1 (by rfl) ⟨1274510, by rfl⟩ : syracuseStep 1699347 = 2549021) B2549021
theorem B1699363 : Blo 1697549 1699363 := bstep (se 1 (by rfl) ⟨1274522, by rfl⟩ : syracuseStep 1699363 = 2549045) B2549045
theorem B1699379 : Blo 1697549 1699379 := bstep (se 1 (by rfl) ⟨1274534, by rfl⟩ : syracuseStep 1699379 = 2549069) B2549069
theorem B1699395 : Blo 1697549 1699395 := bstep (se 1 (by rfl) ⟨1274546, by rfl⟩ : syracuseStep 1699395 = 2549093) B2549093
theorem B1699411 : Blo 1697549 1699411 := bstep (se 1 (by rfl) ⟨1274558, by rfl⟩ : syracuseStep 1699411 = 2549117) B2549117
theorem B1699427 : Blo 1697549 1699427 := bstep (se 1 (by rfl) ⟨1274570, by rfl⟩ : syracuseStep 1699427 = 2549141) B2549141
theorem B20663921 : Blo 1697549 20663921 := bstep (se 2 (by rfl) ⟨7748970, by rfl⟩ : syracuseStep 20663921 = 15497941) B15497941
theorem B2150003 : Blo 1697549 2150003 := bstep (se 1 (by rfl) ⟨1612502, by rfl⟩ : syracuseStep 2150003 = 3225005) B3225005
theorem B1699443 : Blo 1697549 1699443 := bstep (se 1 (by rfl) ⟨1274582, by rfl⟩ : syracuseStep 1699443 = 2549165) B2549165
theorem B1699459 : Blo 1697549 1699459 := bstep (se 1 (by rfl) ⟨1274594, by rfl⟩ : syracuseStep 1699459 = 2549189) B2549189
theorem B3821201 : Blo 1697549 3821201 := bstep (se 2 (by rfl) ⟨1432950, by rfl⟩ : syracuseStep 3821201 = 2865901) B2865901
theorem B1699475 : Blo 1697549 1699475 := bstep (se 1 (by rfl) ⟨1274606, by rfl⟩ : syracuseStep 1699475 = 2549213) B2549213
theorem B3821219 : Blo 1697549 3821219 := bstep (se 1 (by rfl) ⟨2865914, by rfl⟩ : syracuseStep 3821219 = 5731829) B5731829
theorem B1699491 : Blo 1697549 1699491 := bstep (se 1 (by rfl) ⟨1274618, by rfl⟩ : syracuseStep 1699491 = 2549237) B2549237
theorem B4083377 : Blo 1697549 4083377 := bstep (se 2 (by rfl) ⟨1531266, by rfl⟩ : syracuseStep 4083377 = 3062533) B3062533
theorem B1699507 : Blo 1697549 1699507 := bstep (se 1 (by rfl) ⟨1274630, by rfl⟩ : syracuseStep 1699507 = 2549261) B2549261
theorem B1699523 : Blo 1697549 1699523 := bstep (se 1 (by rfl) ⟨1274642, by rfl⟩ : syracuseStep 1699523 = 2549285) B2549285
theorem B1699539 : Blo 1697549 1699539 := bstep (se 1 (by rfl) ⟨1274654, by rfl⟩ : syracuseStep 1699539 = 2549309) B2549309
theorem B5164813 : Blo 1697549 5164813 := bstep (se 3 (by rfl) ⟨968402, by rfl⟩ : syracuseStep 5164813 = 1936805) B1936805
theorem B6885155 : Blo 1697549 6885155 := bstep (se 1 (by rfl) ⟨5163866, by rfl⟩ : syracuseStep 6885155 = 10327733) B10327733
theorem B1814339 : Blo 1697549 1814339 := bstep (se 1 (by rfl) ⟨1360754, by rfl⟩ : syracuseStep 1814339 = 2721509) B2721509
theorem B10882957 : Blo 1697549 10882957 := bstep (se 3 (by rfl) ⟨2040554, by rfl⟩ : syracuseStep 10882957 = 4081109) B4081109
theorem B3821489 : Blo 1697549 3821489 := bstep (se 2 (by rfl) ⟨1433058, by rfl⟩ : syracuseStep 3821489 = 2866117) B2866117
theorem B3821507 : Blo 1697549 3821507 := bstep (se 1 (by rfl) ⟨2866130, by rfl⟩ : syracuseStep 3821507 = 5732261) B5732261
theorem B9678797 : Blo 1697549 9678797 := bstep (se 3 (by rfl) ⟨1814774, by rfl⟩ : syracuseStep 9678797 = 3629549) B3629549
theorem B5165009 : Blo 1697549 5165009 := bstep (se 2 (by rfl) ⟨1936878, by rfl⟩ : syracuseStep 5165009 = 3873757) B3873757
theorem B5165059 : Blo 1697549 5165059 := bstep (se 1 (by rfl) ⟨3873794, by rfl⟩ : syracuseStep 5165059 = 7747589) B7747589
theorem B5730317 : Blo 1697549 5730317 := bstep (se 3 (by rfl) ⟨1074434, by rfl⟩ : syracuseStep 5730317 = 2148869) B2148869
theorem B5730371 : Blo 1697549 5730371 := bstep (se 1 (by rfl) ⟨4297778, by rfl⟩ : syracuseStep 5730371 = 8595557) B8595557
theorem B4477027 : Blo 1697549 4477027 := bstep (se 1 (by rfl) ⟨3357770, by rfl⟩ : syracuseStep 4477027 = 6715541) B6715541
theorem B3223729 : Blo 1697549 3223729 := bstep (se 2 (by rfl) ⟨1208898, by rfl⟩ : syracuseStep 3223729 = 2417797) B2417797
theorem B4837553 : Blo 1697549 4837553 := bstep (se 2 (by rfl) ⟨1814082, by rfl⟩ : syracuseStep 4837553 = 3628165) B3628165
theorem B3821777 : Blo 1697549 3821777 := bstep (se 2 (by rfl) ⟨1433166, by rfl⟩ : syracuseStep 3821777 = 2866333) B2866333
theorem B3821795 : Blo 1697549 3821795 := bstep (se 1 (by rfl) ⟨2866346, by rfl⟩ : syracuseStep 3821795 = 5732693) B5732693
theorem B4297009 : Blo 1697549 4297009 := bstep (se 2 (by rfl) ⟨1611378, by rfl⟩ : syracuseStep 4297009 = 3222757) B3222757
theorem B2150707 : Blo 1697549 2150707 := bstep (se 1 (by rfl) ⟨1613030, by rfl⟩ : syracuseStep 2150707 = 3226061) B3226061
theorem B8163661 : Blo 1697549 8163661 := bstep (se 3 (by rfl) ⟨1530686, by rfl⟩ : syracuseStep 8163661 = 3061373) B3061373
theorem B5730641 : Blo 1697549 5730641 := bstep (se 2 (by rfl) ⟨2148990, by rfl⟩ : syracuseStep 5730641 = 4297981) B4297981
theorem B5443939 : Blo 1697549 5443939 := bstep (se 1 (by rfl) ⟨4082954, by rfl⟩ : syracuseStep 5443939 = 8165909) B8165909
theorem B2150803 : Blo 1697549 2150803 := bstep (se 1 (by rfl) ⟨1613102, by rfl⟩ : syracuseStep 2150803 = 3226205) B3226205
theorem B9671075 : Blo 1697549 9671075 := bstep (se 1 (by rfl) ⟨7253306, by rfl⟩ : syracuseStep 9671075 = 14506613) B14506613
theorem B1937827 : Blo 1697549 1937827 := bstep (se 1 (by rfl) ⟨1453370, by rfl⟩ : syracuseStep 1937827 = 2906741) B2906741
theorem B8597987 : Blo 1697549 8597987 := bstep (se 1 (by rfl) ⟨6448490, by rfl⟩ : syracuseStep 8597987 = 12896981) B12896981
theorem B3822065 : Blo 1697549 3822065 := bstep (se 2 (by rfl) ⟨1433274, by rfl⟩ : syracuseStep 3822065 = 2866549) B2866549
theorem B5444081 : Blo 1697549 5444081 := bstep (se 2 (by rfl) ⟨2041530, by rfl⟩ : syracuseStep 5444081 = 4083061) B4083061
theorem B3060227 : Blo 1697549 3060227 := bstep (se 1 (by rfl) ⟨2295170, by rfl⟩ : syracuseStep 3060227 = 4590341) B4590341
theorem B3822083 : Blo 1697549 3822083 := bstep (se 1 (by rfl) ⟨2866562, by rfl⟩ : syracuseStep 3822083 = 5733125) B5733125
theorem B4297283 : Blo 1697549 4297283 := bstep (se 1 (by rfl) ⟨3222962, by rfl⟩ : syracuseStep 4297283 = 6445925) B6445925
theorem B82629233 : Blo 1697549 82629233 := bstep (se 2 (by rfl) ⟨30985962, by rfl⟩ : syracuseStep 82629233 = 61971925) B61971925
theorem B4297475 : Blo 1697549 4297475 := bstep (se 1 (by rfl) ⟨3223106, by rfl⟩ : syracuseStep 4297475 = 6446213) B6446213
theorem B3822353 : Blo 1697549 3822353 := bstep (se 2 (by rfl) ⟨1433382, by rfl⟩ : syracuseStep 3822353 = 2866765) B2866765
theorem B3822371 : Blo 1697549 3822371 := bstep (se 1 (by rfl) ⟨2866778, by rfl⟩ : syracuseStep 3822371 = 5733557) B5733557
theorem B6452045 : Blo 1697549 6452045 := bstep (se 3 (by rfl) ⟨1209758, by rfl⟩ : syracuseStep 6452045 = 2419517) B2419517
theorem B5731181 : Blo 1697549 5731181 := bstep (se 3 (by rfl) ⟨1074596, by rfl⟩ : syracuseStep 5731181 = 2149193) B2149193
theorem B3625841 : Blo 1697549 3625841 := bstep (se 2 (by rfl) ⟨1359690, by rfl⟩ : syracuseStep 3625841 = 2719381) B2719381
theorem B3625859 : Blo 1697549 3625859 := bstep (se 1 (by rfl) ⟨2719394, by rfl⟩ : syracuseStep 3625859 = 5438789) B5438789
theorem B5731235 : Blo 1697549 5731235 := bstep (se 1 (by rfl) ⟨4298426, by rfl⟩ : syracuseStep 5731235 = 8596853) B8596853
theorem B7254947 : Blo 1697549 7254947 := bstep (se 1 (by rfl) ⟨5441210, by rfl⟩ : syracuseStep 7254947 = 10882421) B10882421
theorem B31396835 : Blo 1697549 31396835 := bstep (se 1 (by rfl) ⟨23547626, by rfl⟩ : syracuseStep 31396835 = 47095253) B47095253
theorem B12891149 : Blo 1697549 12891149 := bstep (se 3 (by rfl) ⟨2417090, by rfl⟩ : syracuseStep 12891149 = 4834181) B4834181
theorem B4592675 : Blo 1697549 4592675 := bstep (se 1 (by rfl) ⟨3444506, by rfl⟩ : syracuseStep 4592675 = 6889013) B6889013
theorem B3822641 : Blo 1697549 3822641 := bstep (se 2 (by rfl) ⟨1433490, by rfl⟩ : syracuseStep 3822641 = 2866981) B2866981
theorem B3822659 : Blo 1697549 3822659 := bstep (se 1 (by rfl) ⟨2866994, by rfl⟩ : syracuseStep 3822659 = 5733989) B5733989
theorem B5731505 : Blo 1697549 5731505 := bstep (se 2 (by rfl) ⟨2149314, by rfl⟩ : syracuseStep 5731505 = 4298629) B4298629
theorem B3224785 : Blo 1697549 3224785 := bstep (se 2 (by rfl) ⟨1209294, by rfl⟩ : syracuseStep 3224785 = 2418589) B2418589
theorem B8598797 : Blo 1697549 8598797 := bstep (se 3 (by rfl) ⟨1612274, by rfl⟩ : syracuseStep 8598797 = 3224549) B3224549
theorem B19354949 : Blo 1697549 19354949 := bstep (se 4 (by rfl) ⟨1814526, by rfl⟩ : syracuseStep 19354949 = 3629053) B3629053
theorem B6206797 : Blo 1697549 6206797 := bstep (se 3 (by rfl) ⟨1163774, by rfl⟩ : syracuseStep 6206797 = 2327549) B2327549
theorem B3822929 : Blo 1697549 3822929 := bstep (se 2 (by rfl) ⟨1433598, by rfl⟩ : syracuseStep 3822929 = 2867197) B2867197
theorem B2905427 : Blo 1697549 2905427 := bstep (se 1 (by rfl) ⟨2179070, by rfl⟩ : syracuseStep 2905427 = 4358141) B4358141
theorem B3822947 : Blo 1697549 3822947 := bstep (se 1 (by rfl) ⟨2867210, by rfl⟩ : syracuseStep 3822947 = 5734421) B5734421
theorem B2905475 : Blo 1697549 2905475 := bstep (se 1 (by rfl) ⟨2179106, by rfl⟩ : syracuseStep 2905475 = 4358213) B4358213
theorem B2905537 : Blo 1697549 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B2864659 : Blo 1697549 2864659 := bstep (se 1 (by rfl) ⟨2148494, by rfl⟩ : syracuseStep 2864659 = 4296989) B4296989
theorem B3225187 : Blo 1697549 3225187 := bstep (se 1 (by rfl) ⟨2418890, by rfl⟩ : syracuseStep 3225187 = 4837781) B4837781
theorem B4839011 : Blo 1697549 4839011 := bstep (se 1 (by rfl) ⟨3629258, by rfl⟩ : syracuseStep 4839011 = 7258517) B7258517
theorem B3823217 : Blo 1697549 3823217 := bstep (se 2 (by rfl) ⟨1433706, by rfl⟩ : syracuseStep 3823217 = 2867413) B2867413
theorem B3823235 : Blo 1697549 3823235 := bstep (se 1 (by rfl) ⟨2867426, by rfl⟩ : syracuseStep 3823235 = 5734853) B5734853
theorem B3225233 : Blo 1697549 3225233 := bstep (se 2 (by rfl) ⟨1209462, by rfl⟩ : syracuseStep 3225233 = 2418925) B2418925
theorem B2864801 : Blo 1697549 2864801 := bstep (se 2 (by rfl) ⟨1074300, by rfl⟩ : syracuseStep 2864801 = 2148601) B2148601
theorem B4298417 : Blo 1697549 4298417 := bstep (se 2 (by rfl) ⟨1611906, by rfl⟩ : syracuseStep 4298417 = 3223813) B3223813
theorem B5732045 : Blo 1697549 5732045 := bstep (se 3 (by rfl) ⟨1074758, by rfl⟩ : syracuseStep 5732045 = 2149517) B2149517
theorem B4298467 : Blo 1697549 4298467 := bstep (se 1 (by rfl) ⟨3223850, by rfl⟩ : syracuseStep 4298467 = 6447701) B6447701
theorem B3061489 : Blo 1697549 3061489 := bstep (se 2 (by rfl) ⟨1148058, by rfl⟩ : syracuseStep 3061489 = 2296117) B2296117
theorem B5732099 : Blo 1697549 5732099 := bstep (se 1 (by rfl) ⟨4299074, by rfl⟩ : syracuseStep 5732099 = 8598149) B8598149
theorem B14907149 : Blo 1697549 14907149 := bstep (se 3 (by rfl) ⟨2795090, by rfl⟩ : syracuseStep 14907149 = 5590181) B5590181
theorem B2864929 : Blo 1697549 2864929 := bstep (se 2 (by rfl) ⟨1074348, by rfl⟩ : syracuseStep 2864929 = 2148697) B2148697
theorem B2864963 : Blo 1697549 2864963 := bstep (se 1 (by rfl) ⟨2148722, by rfl⟩ : syracuseStep 2864963 = 4297445) B4297445
theorem B4298609 : Blo 1697549 4298609 := bstep (se 2 (by rfl) ⟨1611978, by rfl⟩ : syracuseStep 4298609 = 3223957) B3223957
theorem B3823505 : Blo 1697549 3823505 := bstep (se 2 (by rfl) ⟨1433814, by rfl⟩ : syracuseStep 3823505 = 2867629) B2867629
theorem B3823523 : Blo 1697549 3823523 := bstep (se 1 (by rfl) ⟨2867642, by rfl⟩ : syracuseStep 3823523 = 5735285) B5735285
theorem B3225521 : Blo 1697549 3225521 := bstep (se 2 (by rfl) ⟨1209570, by rfl⟩ : syracuseStep 3225521 = 2419141) B2419141
theorem B2865091 : Blo 1697549 2865091 := bstep (se 1 (by rfl) ⟨2148818, by rfl⟩ : syracuseStep 2865091 = 4297637) B4297637
theorem B5732369 : Blo 1697549 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B2758691 : Blo 1697549 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B2865233 : Blo 1697549 2865233 := bstep (se 2 (by rfl) ⟨1074462, by rfl⟩ : syracuseStep 2865233 = 2148925) B2148925
theorem B3627089 : Blo 1697549 3627089 := bstep (se 2 (by rfl) ⟨1360158, by rfl⟩ : syracuseStep 3627089 = 2720317) B2720317
theorem B3872881 : Blo 1697549 3872881 := bstep (se 2 (by rfl) ⟨1452330, by rfl⟩ : syracuseStep 3872881 = 2904661) B2904661
theorem B3823793 : Blo 1697549 3823793 := bstep (se 2 (by rfl) ⟨1433922, by rfl⟩ : syracuseStep 3823793 = 2867845) B2867845
theorem B3823811 : Blo 1697549 3823811 := bstep (se 1 (by rfl) ⟨2867858, by rfl⟩ : syracuseStep 3823811 = 5735717) B5735717
theorem B2865361 : Blo 1697549 2865361 := bstep (se 2 (by rfl) ⟨1074510, by rfl⟩ : syracuseStep 2865361 = 2149021) B2149021
theorem B2865395 : Blo 1697549 2865395 := bstep (se 1 (by rfl) ⟨2149046, by rfl⟩ : syracuseStep 2865395 = 4298093) B4298093
theorem B9672965 : Blo 1697549 9672965 := bstep (se 4 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 9672965 = 1813681) B1813681
theorem B3062129 : Blo 1697549 3062129 := bstep (se 2 (by rfl) ⟨1148298, by rfl⟩ : syracuseStep 3062129 = 2296597) B2296597
theorem B2865523 : Blo 1697549 2865523 := bstep (se 1 (by rfl) ⟨2149142, by rfl⟩ : syracuseStep 2865523 = 4298285) B4298285
theorem B6445453 : Blo 1697549 6445453 := bstep (se 3 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 6445453 = 2417045) B2417045
theorem B2865665 : Blo 1697549 2865665 := bstep (se 2 (by rfl) ⟨1074624, by rfl⟩ : syracuseStep 2865665 = 2149249) B2149249
theorem B5732909 : Blo 1697549 5732909 := bstep (se 3 (by rfl) ⟨1074920, by rfl⟩ : syracuseStep 5732909 = 2149841) B2149841
theorem B5732963 : Blo 1697549 5732963 := bstep (se 1 (by rfl) ⟨4299722, by rfl⟩ : syracuseStep 5732963 = 8599445) B8599445
theorem B2865793 : Blo 1697549 2865793 := bstep (se 2 (by rfl) ⟨1074672, by rfl⟩ : syracuseStep 2865793 = 2149345) B2149345
theorem B3226243 : Blo 1697549 3226243 := bstep (se 1 (by rfl) ⟨2419682, by rfl⟩ : syracuseStep 3226243 = 4839365) B4839365
theorem B2546339 : Blo 1697549 2546339 := bstep (se 1 (by rfl) ⟨1909754, by rfl⟩ : syracuseStep 2546339 = 3819509) B3819509
theorem B2865827 : Blo 1697549 2865827 := bstep (se 1 (by rfl) ⟨2149370, by rfl⟩ : syracuseStep 2865827 = 4298741) B4298741
theorem B2546369 : Blo 1697549 2546369 := bstep (se 2 (by rfl) ⟨954888, by rfl⟩ : syracuseStep 2546369 = 1909777) B1909777
theorem B2546387 : Blo 1697549 2546387 := bstep (se 1 (by rfl) ⟨1909790, by rfl⟩ : syracuseStep 2546387 = 3819581) B3819581
theorem B2546417 : Blo 1697549 2546417 := bstep (se 2 (by rfl) ⟨954906, by rfl⟩ : syracuseStep 2546417 = 1909813) B1909813
theorem B16775921 : Blo 1697549 16775921 := bstep (se 2 (by rfl) ⟨6290970, by rfl⟩ : syracuseStep 16775921 = 12581941) B12581941
theorem B2546435 : Blo 1697549 2546435 := bstep (se 1 (by rfl) ⟨1909826, by rfl⟩ : syracuseStep 2546435 = 3819653) B3819653
theorem B2546465 : Blo 1697549 2546465 := bstep (se 2 (by rfl) ⟨954924, by rfl⟩ : syracuseStep 2546465 = 1909849) B1909849
theorem B2865955 : Blo 1697549 2865955 := bstep (se 1 (by rfl) ⟨2149466, by rfl⟩ : syracuseStep 2865955 = 4298933) B4298933
theorem B2546483 : Blo 1697549 2546483 := bstep (se 1 (by rfl) ⟨1909862, by rfl⟩ : syracuseStep 2546483 = 3819725) B3819725
theorem B2546513 : Blo 1697549 2546513 := bstep (se 2 (by rfl) ⟨954942, by rfl⟩ : syracuseStep 2546513 = 1909885) B1909885
theorem B4299601 : Blo 1697549 4299601 := bstep (se 2 (by rfl) ⟨1612350, by rfl⟩ : syracuseStep 4299601 = 3224701) B3224701
theorem B2546531 : Blo 1697549 2546531 := bstep (se 1 (by rfl) ⟨1909898, by rfl⟩ : syracuseStep 2546531 = 3819797) B3819797
theorem B5733233 : Blo 1697549 5733233 := bstep (se 2 (by rfl) ⟨2149962, by rfl⟩ : syracuseStep 5733233 = 4299925) B4299925
theorem B7256945 : Blo 1697549 7256945 := bstep (se 2 (by rfl) ⟨2721354, by rfl⟩ : syracuseStep 7256945 = 5442709) B5442709
theorem B2546561 : Blo 1697549 2546561 := bstep (se 2 (by rfl) ⟨954960, by rfl⟩ : syracuseStep 2546561 = 1909921) B1909921
theorem B2546579 : Blo 1697549 2546579 := bstep (se 1 (by rfl) ⟨1909934, by rfl⟩ : syracuseStep 2546579 = 3819869) B3819869
theorem B2546609 : Blo 1697549 2546609 := bstep (se 2 (by rfl) ⟨954978, by rfl⟩ : syracuseStep 2546609 = 1909957) B1909957
theorem B2866097 : Blo 1697549 2866097 := bstep (se 2 (by rfl) ⟨1074786, by rfl⟩ : syracuseStep 2866097 = 2149573) B2149573
theorem B2546627 : Blo 1697549 2546627 := bstep (se 1 (by rfl) ⟨1909970, by rfl⟩ : syracuseStep 2546627 = 3819941) B3819941
theorem B12745669 : Blo 1697549 12745669 := bstep (se 4 (by rfl) ⟨1194906, by rfl⟩ : syracuseStep 12745669 = 2389813) B2389813
theorem B6888397 : Blo 1697549 6888397 := bstep (se 3 (by rfl) ⟨1291574, by rfl⟩ : syracuseStep 6888397 = 2583149) B2583149
theorem B2546657 : Blo 1697549 2546657 := bstep (se 2 (by rfl) ⟨954996, by rfl⟩ : syracuseStep 2546657 = 1909993) B1909993
theorem B2546675 : Blo 1697549 2546675 := bstep (se 1 (by rfl) ⟨1910006, by rfl⟩ : syracuseStep 2546675 = 3820013) B3820013
theorem B15490061 : Blo 1697549 15490061 := bstep (se 3 (by rfl) ⟨2904386, by rfl⟩ : syracuseStep 15490061 = 5808773) B5808773
theorem B2546705 : Blo 1697549 2546705 := bstep (se 2 (by rfl) ⟨955014, by rfl⟩ : syracuseStep 2546705 = 1910029) B1910029
theorem B2546723 : Blo 1697549 2546723 := bstep (se 1 (by rfl) ⟨1910042, by rfl⟩ : syracuseStep 2546723 = 3820085) B3820085
theorem B2866225 : Blo 1697549 2866225 := bstep (se 2 (by rfl) ⟨1074834, by rfl⟩ : syracuseStep 2866225 = 2149669) B2149669
theorem B55065653 : Blo 1697549 55065653 := bstep (se 5 (by rfl) ⟨2581202, by rfl⟩ : syracuseStep 55065653 = 5162405) B5162405
theorem B2546753 : Blo 1697549 2546753 := bstep (se 2 (by rfl) ⟨955032, by rfl⟩ : syracuseStep 2546753 = 1910065) B1910065
theorem B2546771 : Blo 1697549 2546771 := bstep (se 1 (by rfl) ⟨1910078, by rfl⟩ : syracuseStep 2546771 = 3820157) B3820157
theorem B2866259 : Blo 1697549 2866259 := bstep (se 1 (by rfl) ⟨2149694, by rfl⟩ : syracuseStep 2866259 = 4299389) B4299389
theorem B4299875 : Blo 1697549 4299875 := bstep (se 1 (by rfl) ⟨3224906, by rfl⟩ : syracuseStep 4299875 = 6449813) B6449813
theorem B2546801 : Blo 1697549 2546801 := bstep (se 2 (by rfl) ⟨955050, by rfl⟩ : syracuseStep 2546801 = 1910101) B1910101
theorem B2546819 : Blo 1697549 2546819 := bstep (se 1 (by rfl) ⟨1910114, by rfl⟩ : syracuseStep 2546819 = 3820229) B3820229
theorem B5438609 : Blo 1697549 5438609 := bstep (se 2 (by rfl) ⟨2039478, by rfl⟩ : syracuseStep 5438609 = 4078957) B4078957
theorem B2546849 : Blo 1697549 2546849 := bstep (se 2 (by rfl) ⟨955068, by rfl⟩ : syracuseStep 2546849 = 1910137) B1910137
theorem B6446243 : Blo 1697549 6446243 := bstep (se 1 (by rfl) ⟨4834682, by rfl⟩ : syracuseStep 6446243 = 9669365) B9669365
theorem B2546867 : Blo 1697549 2546867 := bstep (se 1 (by rfl) ⟨1910150, by rfl⟩ : syracuseStep 2546867 = 3820301) B3820301
theorem B5438659 : Blo 1697549 5438659 := bstep (se 1 (by rfl) ⟨4078994, by rfl⟩ : syracuseStep 5438659 = 8157989) B8157989
theorem B2546897 : Blo 1697549 2546897 := bstep (se 2 (by rfl) ⟨955086, by rfl⟩ : syracuseStep 2546897 = 1910173) B1910173
theorem B2866387 : Blo 1697549 2866387 := bstep (se 1 (by rfl) ⟨2149790, by rfl⟩ : syracuseStep 2866387 = 4299581) B4299581
theorem B2546915 : Blo 1697549 2546915 := bstep (se 1 (by rfl) ⟨1910186, by rfl⟩ : syracuseStep 2546915 = 3820373) B3820373
theorem B6208753 : Blo 1697549 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B2546945 : Blo 1697549 2546945 := bstep (se 2 (by rfl) ⟨955104, by rfl⟩ : syracuseStep 2546945 = 1910209) B1910209
theorem B2546963 : Blo 1697549 2546963 := bstep (se 1 (by rfl) ⟨1910222, by rfl⟩ : syracuseStep 2546963 = 3820445) B3820445
theorem B4300067 : Blo 1697549 4300067 := bstep (se 1 (by rfl) ⟨3225050, by rfl⟩ : syracuseStep 4300067 = 6450101) B6450101
theorem B2546993 : Blo 1697549 2546993 := bstep (se 2 (by rfl) ⟨955122, by rfl⟩ : syracuseStep 2546993 = 1910245) B1910245
theorem B2547011 : Blo 1697549 2547011 := bstep (se 1 (by rfl) ⟨1910258, by rfl⟩ : syracuseStep 2547011 = 3820517) B3820517
theorem B2547041 : Blo 1697549 2547041 := bstep (se 2 (by rfl) ⟨955140, by rfl⟩ : syracuseStep 2547041 = 1910281) B1910281
theorem B2866529 : Blo 1697549 2866529 := bstep (se 2 (by rfl) ⟨1074948, by rfl⟩ : syracuseStep 2866529 = 2149897) B2149897
theorem B3538289 : Blo 1697549 3538289 := bstep (se 2 (by rfl) ⟨1326858, by rfl⟩ : syracuseStep 3538289 = 2653717) B2653717
theorem B2547059 : Blo 1697549 2547059 := bstep (se 1 (by rfl) ⟨1910294, by rfl⟩ : syracuseStep 2547059 = 3820589) B3820589
theorem B5733773 : Blo 1697549 5733773 := bstep (se 3 (by rfl) ⟨1075082, by rfl⟩ : syracuseStep 5733773 = 2150165) B2150165
theorem B2547089 : Blo 1697549 2547089 := bstep (se 2 (by rfl) ⟨955158, by rfl⟩ : syracuseStep 2547089 = 1910317) B1910317
theorem B2547107 : Blo 1697549 2547107 := bstep (se 1 (by rfl) ⟨1910330, by rfl⟩ : syracuseStep 2547107 = 3820661) B3820661
theorem B2547137 : Blo 1697549 2547137 := bstep (se 2 (by rfl) ⟨955176, by rfl⟩ : syracuseStep 2547137 = 1910353) B1910353
theorem B5733827 : Blo 1697549 5733827 := bstep (se 1 (by rfl) ⟨4300370, by rfl⟩ : syracuseStep 5733827 = 8600741) B8600741
theorem B2547155 : Blo 1697549 2547155 := bstep (se 1 (by rfl) ⟨1910366, by rfl⟩ : syracuseStep 2547155 = 3820733) B3820733
theorem B2866657 : Blo 1697549 2866657 := bstep (se 2 (by rfl) ⟨1074996, by rfl⟩ : syracuseStep 2866657 = 2149993) B2149993
theorem B2547185 : Blo 1697549 2547185 := bstep (se 2 (by rfl) ⟨955194, by rfl⟩ : syracuseStep 2547185 = 1910389) B1910389
theorem B2547203 : Blo 1697549 2547203 := bstep (se 1 (by rfl) ⟨1910402, by rfl⟩ : syracuseStep 2547203 = 3820805) B3820805
theorem B2866691 : Blo 1697549 2866691 := bstep (se 1 (by rfl) ⟨2150018, by rfl⟩ : syracuseStep 2866691 = 4300037) B4300037
theorem B2547233 : Blo 1697549 2547233 := bstep (se 2 (by rfl) ⟨955212, by rfl⟩ : syracuseStep 2547233 = 1910425) B1910425
theorem B2547251 : Blo 1697549 2547251 := bstep (se 1 (by rfl) ⟨1910438, by rfl⟩ : syracuseStep 2547251 = 3820877) B3820877
theorem B2547281 : Blo 1697549 2547281 := bstep (se 2 (by rfl) ⟨955230, by rfl⟩ : syracuseStep 2547281 = 1910461) B1910461
theorem B2547299 : Blo 1697549 2547299 := bstep (se 1 (by rfl) ⟨1910474, by rfl⟩ : syracuseStep 2547299 = 3820949) B3820949
theorem B3628643 : Blo 1697549 3628643 := bstep (se 1 (by rfl) ⟨2721482, by rfl⟩ : syracuseStep 3628643 = 5442965) B5442965
theorem B13778545 : Blo 1697549 13778545 := bstep (se 2 (by rfl) ⟨5166954, by rfl⟩ : syracuseStep 13778545 = 10333909) B10333909
theorem B2547329 : Blo 1697549 2547329 := bstep (se 2 (by rfl) ⟨955248, by rfl⟩ : syracuseStep 2547329 = 1910497) B1910497
theorem B2866819 : Blo 1697549 2866819 := bstep (se 1 (by rfl) ⟨2150114, by rfl⟩ : syracuseStep 2866819 = 4300229) B4300229
theorem B11034245 : Blo 1697549 11034245 := bstep (se 4 (by rfl) ⟨1034460, by rfl⟩ : syracuseStep 11034245 = 2068921) B2068921
theorem B27541133 : Blo 1697549 27541133 := bstep (se 3 (by rfl) ⟨5163962, by rfl⟩ : syracuseStep 27541133 = 10327925) B10327925
theorem B2547347 : Blo 1697549 2547347 := bstep (se 1 (by rfl) ⟨1910510, by rfl⟩ : syracuseStep 2547347 = 3821021) B3821021
theorem B2547377 : Blo 1697549 2547377 := bstep (se 2 (by rfl) ⟨955266, by rfl⟩ : syracuseStep 2547377 = 1910533) B1910533
theorem B2547395 : Blo 1697549 2547395 := bstep (se 1 (by rfl) ⟨1910546, by rfl⟩ : syracuseStep 2547395 = 3821093) B3821093
theorem B5734097 : Blo 1697549 5734097 := bstep (se 2 (by rfl) ⟨2150286, by rfl⟩ : syracuseStep 5734097 = 4300573) B4300573
theorem B2547425 : Blo 1697549 2547425 := bstep (se 2 (by rfl) ⟨955284, by rfl⟩ : syracuseStep 2547425 = 1910569) B1910569
theorem B2547443 : Blo 1697549 2547443 := bstep (se 1 (by rfl) ⟨1910582, by rfl⟩ : syracuseStep 2547443 = 3821165) B3821165
theorem B7257869 : Blo 1697549 7257869 := bstep (se 3 (by rfl) ⟨1360850, by rfl⟩ : syracuseStep 7257869 = 2721701) B2721701
theorem B2547473 : Blo 1697549 2547473 := bstep (se 2 (by rfl) ⟨955302, by rfl⟩ : syracuseStep 2547473 = 1910605) B1910605
theorem B2866961 : Blo 1697549 2866961 := bstep (se 2 (by rfl) ⟨1075110, by rfl⟩ : syracuseStep 2866961 = 2150221) B2150221
theorem B2547491 : Blo 1697549 2547491 := bstep (se 1 (by rfl) ⟨1910618, by rfl⟩ : syracuseStep 2547491 = 3821237) B3821237
theorem B6446897 : Blo 1697549 6446897 := bstep (se 2 (by rfl) ⟨2417586, by rfl⟩ : syracuseStep 6446897 = 4835173) B4835173
theorem B2547521 : Blo 1697549 2547521 := bstep (se 2 (by rfl) ⟨955320, by rfl⟩ : syracuseStep 2547521 = 1910641) B1910641
theorem B2547539 : Blo 1697549 2547539 := bstep (se 1 (by rfl) ⟨1910654, by rfl⟩ : syracuseStep 2547539 = 3821309) B3821309
theorem B2547569 : Blo 1697549 2547569 := bstep (se 2 (by rfl) ⟨955338, by rfl⟩ : syracuseStep 2547569 = 1910677) B1910677
theorem B12894065 : Blo 1697549 12894065 := bstep (se 2 (by rfl) ⟨4835274, by rfl⟩ : syracuseStep 12894065 = 9670549) B9670549
theorem B2547587 : Blo 1697549 2547587 := bstep (se 1 (by rfl) ⟨1910690, by rfl⟩ : syracuseStep 2547587 = 3821381) B3821381
theorem B2867089 : Blo 1697549 2867089 := bstep (se 2 (by rfl) ⟨1075158, by rfl⟩ : syracuseStep 2867089 = 2150317) B2150317
theorem B2547617 : Blo 1697549 2547617 := bstep (se 2 (by rfl) ⟨955356, by rfl⟩ : syracuseStep 2547617 = 1910713) B1910713
theorem B2719651 : Blo 1697549 2719651 := bstep (se 1 (by rfl) ⟨2039738, by rfl⟩ : syracuseStep 2719651 = 4079477) B4079477
theorem B2547635 : Blo 1697549 2547635 := bstep (se 1 (by rfl) ⟨1910726, by rfl⟩ : syracuseStep 2547635 = 3821453) B3821453
theorem B2867123 : Blo 1697549 2867123 := bstep (se 1 (by rfl) ⟨2150342, by rfl⟩ : syracuseStep 2867123 = 4300685) B4300685
theorem B2547665 : Blo 1697549 2547665 := bstep (se 2 (by rfl) ⟨955374, by rfl⟩ : syracuseStep 2547665 = 1910749) B1910749
theorem B2547683 : Blo 1697549 2547683 := bstep (se 1 (by rfl) ⟨1910762, by rfl⟩ : syracuseStep 2547683 = 3821525) B3821525
theorem B2547737 : Blo 1697549 2547737 := bstep (se 2 (by rfl) ⟨955401, by rfl⟩ : syracuseStep 2547737 = 1910803) B1910803
theorem B5734475 : Blo 1697549 5734475 := bstep (se 1 (by rfl) ⟨4300856, by rfl⟩ : syracuseStep 5734475 = 8601713) B8601713
theorem B7356509 : Blo 1697549 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B7258243 : Blo 1697549 7258243 := bstep (se 1 (by rfl) ⟨5443682, by rfl⟩ : syracuseStep 7258243 = 10887365) B10887365
theorem B2547851 : Blo 1697549 2547851 := bstep (se 1 (by rfl) ⟨1910888, by rfl⟩ : syracuseStep 2547851 = 3821777) B3821777
theorem B2867339 : Blo 1697549 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B104562839 : Blo 1697549 104562839 := bstep (se 1 (by rfl) ⟨78422129, by rfl⟩ : syracuseStep 104562839 = 156844259) B156844259
theorem B2547863 : Blo 1697549 2547863 := bstep (se 1 (by rfl) ⟨1910897, by rfl⟩ : syracuseStep 2547863 = 3821795) B3821795
theorem B2547929 : Blo 1697549 2547929 := bstep (se 2 (by rfl) ⟨955473, by rfl⟩ : syracuseStep 2547929 = 1910947) B1910947
theorem B2867467 : Blo 1697549 2867467 := bstep (se 1 (by rfl) ⟨2150600, by rfl⟩ : syracuseStep 2867467 = 4301201) B4301201
theorem B6447383 : Blo 1697549 6447383 := bstep (se 1 (by rfl) ⟨4835537, by rfl⟩ : syracuseStep 6447383 = 9671075) B9671075
theorem B2548043 : Blo 1697549 2548043 := bstep (se 1 (by rfl) ⟨1911032, by rfl⟩ : syracuseStep 2548043 = 3822065) B3822065
theorem B3629387 : Blo 1697549 3629387 := bstep (se 1 (by rfl) ⟨2722040, by rfl⟩ : syracuseStep 3629387 = 5444081) B5444081
theorem B2040151 : Blo 1697549 2040151 := bstep (se 1 (by rfl) ⟨1530113, by rfl⟩ : syracuseStep 2040151 = 3060227) B3060227
theorem B2548055 : Blo 1697549 2548055 := bstep (se 1 (by rfl) ⟨1911041, by rfl⟩ : syracuseStep 2548055 = 3822083) B3822083
theorem B5734745 : Blo 1697549 5734745 := bstep (se 2 (by rfl) ⟨2150529, by rfl⟩ : syracuseStep 5734745 = 4301059) B4301059
theorem B2548121 : Blo 1697549 2548121 := bstep (se 2 (by rfl) ⟨955545, by rfl⟩ : syracuseStep 2548121 = 1911091) B1911091
theorem B2867609 : Blo 1697549 2867609 := bstep (se 2 (by rfl) ⟨1075353, by rfl⟩ : syracuseStep 2867609 = 2150707) B2150707
theorem B7258585 : Blo 1697549 7258585 := bstep (se 2 (by rfl) ⟨2721969, by rfl⟩ : syracuseStep 7258585 = 5443939) B5443939
theorem B13066757 : Blo 1697549 13066757 := bstep (se 4 (by rfl) ⟨1225008, by rfl⟩ : syracuseStep 13066757 = 2450017) B2450017
theorem B2548235 : Blo 1697549 2548235 := bstep (se 1 (by rfl) ⟨1911176, by rfl⟩ : syracuseStep 2548235 = 3822353) B3822353
theorem B8593937 : Blo 1697549 8593937 := bstep (se 2 (by rfl) ⟨3222726, by rfl⟩ : syracuseStep 8593937 = 6445453) B6445453
theorem B2720279 : Blo 1697549 2720279 := bstep (se 1 (by rfl) ⟨2040209, by rfl⟩ : syracuseStep 2720279 = 4080419) B4080419
theorem B2548247 : Blo 1697549 2548247 := bstep (se 1 (by rfl) ⟨1911185, by rfl⟩ : syracuseStep 2548247 = 3822371) B3822371
theorem B2867737 : Blo 1697549 2867737 := bstep (se 2 (by rfl) ⟨1075401, by rfl⟩ : syracuseStep 2867737 = 2150803) B2150803
theorem B20660771 : Blo 1697549 20660771 := bstep (se 1 (by rfl) ⟨15495578, by rfl⟩ : syracuseStep 20660771 = 30991157) B30991157
theorem B4301363 : Blo 1697549 4301363 := bstep (se 1 (by rfl) ⟨3226022, by rfl⟩ : syracuseStep 4301363 = 6452045) B6452045
theorem B7963201 : Blo 1697549 7963201 := bstep (se 2 (by rfl) ⟨2986200, by rfl⟩ : syracuseStep 7963201 = 5972401) B5972401
theorem B2417239 : Blo 1697549 2417239 := bstep (se 1 (by rfl) ⟨1812929, by rfl⟩ : syracuseStep 2417239 = 3625859) B3625859
theorem B2548313 : Blo 1697549 2548313 := bstep (se 2 (by rfl) ⟨955617, by rfl⟩ : syracuseStep 2548313 = 1911235) B1911235
theorem B20931223 : Blo 1697549 20931223 := bstep (se 1 (by rfl) ⟨15698417, by rfl⟩ : syracuseStep 20931223 = 31396835) B31396835
theorem B8594099 : Blo 1697549 8594099 := bstep (se 1 (by rfl) ⟨6445574, by rfl⟩ : syracuseStep 8594099 = 12891149) B12891149
theorem B2548427 : Blo 1697549 2548427 := bstep (se 1 (by rfl) ⟨1911320, by rfl⟩ : syracuseStep 2548427 = 3822641) B3822641
theorem B2548439 : Blo 1697549 2548439 := bstep (se 1 (by rfl) ⟨1911329, by rfl⟩ : syracuseStep 2548439 = 3822659) B3822659
theorem B2548505 : Blo 1697549 2548505 := bstep (se 2 (by rfl) ⟨955689, by rfl⟩ : syracuseStep 2548505 = 1911379) B1911379
theorem B4301657 : Blo 1697549 4301657 := bstep (se 2 (by rfl) ⟨1613121, by rfl⟩ : syracuseStep 4301657 = 3226243) B3226243
theorem B12903299 : Blo 1697549 12903299 := bstep (se 1 (by rfl) ⟨9677474, by rfl⟩ : syracuseStep 12903299 = 19354949) B19354949
theorem B2548619 : Blo 1697549 2548619 := bstep (se 1 (by rfl) ⟨1911464, by rfl⟩ : syracuseStep 2548619 = 3822929) B3822929
theorem B2548631 : Blo 1697549 2548631 := bstep (se 1 (by rfl) ⟨1911473, by rfl⟩ : syracuseStep 2548631 = 3822947) B3822947
theorem B2548697 : Blo 1697549 2548697 := bstep (se 2 (by rfl) ⟨955761, by rfl⟩ : syracuseStep 2548697 = 1911523) B1911523
theorem B5735447 : Blo 1697549 5735447 := bstep (se 1 (by rfl) ⟨4301585, by rfl⟩ : syracuseStep 5735447 = 8603171) B8603171
theorem B2548811 : Blo 1697549 2548811 := bstep (se 1 (by rfl) ⟨1911608, by rfl⟩ : syracuseStep 2548811 = 3823217) B3823217
theorem B2548823 : Blo 1697549 2548823 := bstep (se 1 (by rfl) ⟨1911617, by rfl⟩ : syracuseStep 2548823 = 3823235) B3823235
theorem B1909867 : Blo 1697549 1909867 := bstep (se 1 (by rfl) ⟨1432400, by rfl⟩ : syracuseStep 1909867 = 2864801) B2864801
theorem B2548889 : Blo 1697549 2548889 := bstep (se 2 (by rfl) ⟨955833, by rfl⟩ : syracuseStep 2548889 = 1911667) B1911667
theorem B9938099 : Blo 1697549 9938099 := bstep (se 1 (by rfl) ⟨7453574, by rfl⟩ : syracuseStep 9938099 = 14907149) B14907149
theorem B32662709 : Blo 1697549 32662709 := bstep (se 5 (by rfl) ⟨1531064, by rfl⟩ : syracuseStep 32662709 = 3062129) B3062129
theorem B1909975 : Blo 1697549 1909975 := bstep (se 1 (by rfl) ⟨1432481, by rfl⟩ : syracuseStep 1909975 = 2864963) B2864963
theorem B17442053 : Blo 1697549 17442053 := bstep (se 4 (by rfl) ⟨1635192, by rfl⟩ : syracuseStep 17442053 = 3270385) B3270385
theorem B2721035 : Blo 1697549 2721035 := bstep (se 1 (by rfl) ⟨2040776, by rfl⟩ : syracuseStep 2721035 = 4081553) B4081553
theorem B2549003 : Blo 1697549 2549003 := bstep (se 1 (by rfl) ⟨1911752, by rfl⟩ : syracuseStep 2549003 = 3823505) B3823505
theorem B9184529 : Blo 1697549 9184529 := bstep (se 2 (by rfl) ⟨3444198, by rfl⟩ : syracuseStep 9184529 = 6888397) B6888397
theorem B2549015 : Blo 1697549 2549015 := bstep (se 1 (by rfl) ⟨1911761, by rfl⟩ : syracuseStep 2549015 = 3823523) B3823523
theorem B12895523 : Blo 1697549 12895523 := bstep (se 1 (by rfl) ⟨9671642, by rfl⟩ : syracuseStep 12895523 = 19343285) B19343285
theorem B8160587 : Blo 1697549 8160587 := bstep (se 1 (by rfl) ⟨6120440, by rfl⟩ : syracuseStep 8160587 = 12240881) B12240881
theorem B2549081 : Blo 1697549 2549081 := bstep (se 2 (by rfl) ⟨955905, by rfl⟩ : syracuseStep 2549081 = 1911811) B1911811
theorem B30991733 : Blo 1697549 30991733 := bstep (se 5 (by rfl) ⟨1452737, by rfl⟩ : syracuseStep 30991733 = 2905475) B2905475
theorem B1910155 : Blo 1697549 1910155 := bstep (se 1 (by rfl) ⟨1432616, by rfl⟩ : syracuseStep 1910155 = 2865233) B2865233
theorem B2418059 : Blo 1697549 2418059 := bstep (se 1 (by rfl) ⟨1813544, by rfl⟩ : syracuseStep 2418059 = 3627089) B3627089
theorem B7259543 : Blo 1697549 7259543 := bstep (se 1 (by rfl) ⟨5444657, by rfl⟩ : syracuseStep 7259543 = 10889315) B10889315
theorem B3442099 : Blo 1697549 3442099 := bstep (se 1 (by rfl) ⟨2581574, by rfl⟩ : syracuseStep 3442099 = 5163149) B5163149
theorem B19613107 : Blo 1697549 19613107 := bstep (se 1 (by rfl) ⟨14709830, by rfl⟩ : syracuseStep 19613107 = 29419661) B29419661
theorem B3442123 : Blo 1697549 3442123 := bstep (se 1 (by rfl) ⟨2581592, by rfl⟩ : syracuseStep 3442123 = 5163185) B5163185
theorem B2549195 : Blo 1697549 2549195 := bstep (se 1 (by rfl) ⟨1911896, by rfl⟩ : syracuseStep 2549195 = 3823793) B3823793
theorem B2549207 : Blo 1697549 2549207 := bstep (se 1 (by rfl) ⟨1911905, by rfl⟩ : syracuseStep 2549207 = 3823811) B3823811
theorem B1910263 : Blo 1697549 1910263 := bstep (se 1 (by rfl) ⟨1432697, by rfl⟩ : syracuseStep 1910263 = 2865395) B2865395
theorem B6448643 : Blo 1697549 6448643 := bstep (se 1 (by rfl) ⟨4836482, by rfl⟩ : syracuseStep 6448643 = 9672965) B9672965
theorem B2549273 : Blo 1697549 2549273 := bstep (se 2 (by rfl) ⟨955977, by rfl⟩ : syracuseStep 2549273 = 1911955) B1911955
theorem B11036225 : Blo 1697549 11036225 := bstep (se 2 (by rfl) ⟨4138584, by rfl⟩ : syracuseStep 11036225 = 8277169) B8277169
theorem B7251545 : Blo 1697549 7251545 := bstep (se 2 (by rfl) ⟨2719329, by rfl⟩ : syracuseStep 7251545 = 5438659) B5438659
theorem B9676381 : Blo 1697549 9676381 := bstep (se 3 (by rfl) ⟨1814321, by rfl⟩ : syracuseStep 9676381 = 3628643) B3628643
theorem B4589207 : Blo 1697549 4589207 := bstep (se 1 (by rfl) ⟨3441905, by rfl⟩ : syracuseStep 4589207 = 6883811) B6883811
theorem B24495767 : Blo 1697549 24495767 := bstep (se 1 (by rfl) ⟨18371825, by rfl⟩ : syracuseStep 24495767 = 36743651) B36743651
theorem B1910443 : Blo 1697549 1910443 := bstep (se 1 (by rfl) ⟨1432832, by rfl⟩ : syracuseStep 1910443 = 2865665) B2865665
theorem B6121133 : Blo 1697549 6121133 := bstep (se 3 (by rfl) ⟨1147712, by rfl⟩ : syracuseStep 6121133 = 2295425) B2295425
theorem B2721547 : Blo 1697549 2721547 := bstep (se 1 (by rfl) ⟨2041160, by rfl⟩ : syracuseStep 2721547 = 4082321) B4082321
theorem B8275729 : Blo 1697549 8275729 := bstep (se 2 (by rfl) ⟨3103398, by rfl⟩ : syracuseStep 8275729 = 6206797) B6206797
theorem B1697559 : Blo 1697549 1697559 := bstep (se 1 (by rfl) ⟨1273169, by rfl⟩ : syracuseStep 1697559 = 2546339) B2546339
theorem B1910551 : Blo 1697549 1910551 := bstep (se 1 (by rfl) ⟨1432913, by rfl⟩ : syracuseStep 1910551 = 2865827) B2865827
theorem B1697579 : Blo 1697549 1697579 := bstep (se 1 (by rfl) ⟨1273184, by rfl⟩ : syracuseStep 1697579 = 2546369) B2546369
theorem B10889005 : Blo 1697549 10889005 := bstep (se 3 (by rfl) ⟨2041688, by rfl⟩ : syracuseStep 10889005 = 4083377) B4083377
theorem B1697591 : Blo 1697549 1697591 := bstep (se 1 (by rfl) ⟨1273193, by rfl⟩ : syracuseStep 1697591 = 2546387) B2546387
theorem B1697611 : Blo 1697549 1697611 := bstep (se 1 (by rfl) ⟨1273208, by rfl⟩ : syracuseStep 1697611 = 2546417) B2546417
theorem B11183947 : Blo 1697549 11183947 := bstep (se 1 (by rfl) ⟨8387960, by rfl⟩ : syracuseStep 11183947 = 16775921) B16775921
theorem B1697623 : Blo 1697549 1697623 := bstep (se 1 (by rfl) ⟨1273217, by rfl⟩ : syracuseStep 1697623 = 2546435) B2546435
theorem B14509925 : Blo 1697549 14509925 := bstep (se 4 (by rfl) ⟨1360305, by rfl⟩ : syracuseStep 14509925 = 2720611) B2720611
theorem B1697643 : Blo 1697549 1697643 := bstep (se 1 (by rfl) ⟨1273232, by rfl⟩ : syracuseStep 1697643 = 2546465) B2546465
theorem B1697655 : Blo 1697549 1697655 := bstep (se 1 (by rfl) ⟨1273241, by rfl⟩ : syracuseStep 1697655 = 2546483) B2546483
theorem B1697675 : Blo 1697549 1697675 := bstep (se 1 (by rfl) ⟨1273256, by rfl⟩ : syracuseStep 1697675 = 2546513) B2546513
theorem B1697687 : Blo 1697549 1697687 := bstep (se 1 (by rfl) ⟨1273265, by rfl⟩ : syracuseStep 1697687 = 2546531) B2546531
theorem B1697707 : Blo 1697549 1697707 := bstep (se 1 (by rfl) ⟨1273280, by rfl⟩ : syracuseStep 1697707 = 2546561) B2546561
theorem B1697719 : Blo 1697549 1697719 := bstep (se 1 (by rfl) ⟨1273289, by rfl⟩ : syracuseStep 1697719 = 2546579) B2546579
theorem B1697739 : Blo 1697549 1697739 := bstep (se 1 (by rfl) ⟨1273304, by rfl⟩ : syracuseStep 1697739 = 2546609) B2546609
theorem B1910731 : Blo 1697549 1910731 := bstep (se 1 (by rfl) ⟨1433048, by rfl⟩ : syracuseStep 1910731 = 2866097) B2866097
theorem B1697751 : Blo 1697549 1697751 := bstep (se 1 (by rfl) ⟨1273313, by rfl⟩ : syracuseStep 1697751 = 2546627) B2546627
theorem B1697771 : Blo 1697549 1697771 := bstep (se 1 (by rfl) ⟨1273328, by rfl⟩ : syracuseStep 1697771 = 2546657) B2546657
theorem B1697783 : Blo 1697549 1697783 := bstep (se 1 (by rfl) ⟨1273337, by rfl⟩ : syracuseStep 1697783 = 2546675) B2546675
theorem B1697803 : Blo 1697549 1697803 := bstep (se 1 (by rfl) ⟨1273352, by rfl⟩ : syracuseStep 1697803 = 2546705) B2546705
theorem B1697815 : Blo 1697549 1697815 := bstep (se 1 (by rfl) ⟨1273361, by rfl⟩ : syracuseStep 1697815 = 2546723) B2546723
theorem B3819545 : Blo 1697549 3819545 := bstep (se 2 (by rfl) ⟨1432329, by rfl⟩ : syracuseStep 3819545 = 2864659) B2864659
theorem B36710435 : Blo 1697549 36710435 := bstep (se 1 (by rfl) ⟨27532826, by rfl⟩ : syracuseStep 36710435 = 55065653) B55065653
theorem B1697835 : Blo 1697549 1697835 := bstep (se 1 (by rfl) ⟨1273376, by rfl⟩ : syracuseStep 1697835 = 2546753) B2546753
theorem B1697847 : Blo 1697549 1697847 := bstep (se 1 (by rfl) ⟨1273385, by rfl⟩ : syracuseStep 1697847 = 2546771) B2546771
theorem B1910839 : Blo 1697549 1910839 := bstep (se 1 (by rfl) ⟨1433129, by rfl⟩ : syracuseStep 1910839 = 2866259) B2866259
theorem B1697867 : Blo 1697549 1697867 := bstep (se 1 (by rfl) ⟨1273400, by rfl⟩ : syracuseStep 1697867 = 2546801) B2546801
theorem B1697879 : Blo 1697549 1697879 := bstep (se 1 (by rfl) ⟨1273409, by rfl⟩ : syracuseStep 1697879 = 2546819) B2546819
theorem B1697899 : Blo 1697549 1697899 := bstep (se 1 (by rfl) ⟨1273424, by rfl⟩ : syracuseStep 1697899 = 2546849) B2546849
theorem B3819635 : Blo 1697549 3819635 := bstep (se 1 (by rfl) ⟨2864726, by rfl⟩ : syracuseStep 3819635 = 5729453) B5729453
theorem B1697911 : Blo 1697549 1697911 := bstep (se 1 (by rfl) ⟨1273433, by rfl⟩ : syracuseStep 1697911 = 2546867) B2546867
theorem B1697931 : Blo 1697549 1697931 := bstep (se 1 (by rfl) ⟨1273448, by rfl⟩ : syracuseStep 1697931 = 2546897) B2546897
theorem B3819671 : Blo 1697549 3819671 := bstep (se 1 (by rfl) ⟨2864753, by rfl⟩ : syracuseStep 3819671 = 5729507) B5729507
theorem B4901015 : Blo 1697549 4901015 := bstep (se 1 (by rfl) ⟨3675761, by rfl⟩ : syracuseStep 4901015 = 7351523) B7351523
theorem B1697943 : Blo 1697549 1697943 := bstep (se 1 (by rfl) ⟨1273457, by rfl⟩ : syracuseStep 1697943 = 2546915) B2546915
theorem B1697963 : Blo 1697549 1697963 := bstep (se 1 (by rfl) ⟨1273472, by rfl⟩ : syracuseStep 1697963 = 2546945) B2546945
theorem B1697975 : Blo 1697549 1697975 := bstep (se 1 (by rfl) ⟨1273481, by rfl⟩ : syracuseStep 1697975 = 2546963) B2546963
theorem B1697995 : Blo 1697549 1697995 := bstep (se 1 (by rfl) ⟨1273496, by rfl⟩ : syracuseStep 1697995 = 2546993) B2546993
theorem B1698007 : Blo 1697549 1698007 := bstep (se 1 (by rfl) ⟨1273505, by rfl⟩ : syracuseStep 1698007 = 2547011) B2547011
theorem B1698027 : Blo 1697549 1698027 := bstep (se 1 (by rfl) ⟨1273520, by rfl⟩ : syracuseStep 1698027 = 2547041) B2547041
theorem B1911019 : Blo 1697549 1911019 := bstep (se 1 (by rfl) ⟨1433264, by rfl⟩ : syracuseStep 1911019 = 2866529) B2866529
theorem B1698039 : Blo 1697549 1698039 := bstep (se 1 (by rfl) ⟨1273529, by rfl⟩ : syracuseStep 1698039 = 2547059) B2547059
theorem B1698059 : Blo 1697549 1698059 := bstep (se 1 (by rfl) ⟨1273544, by rfl⟩ : syracuseStep 1698059 = 2547089) B2547089
theorem B1698071 : Blo 1697549 1698071 := bstep (se 1 (by rfl) ⟨1273553, by rfl⟩ : syracuseStep 1698071 = 2547107) B2547107
theorem B1698091 : Blo 1697549 1698091 := bstep (se 1 (by rfl) ⟨1273568, by rfl⟩ : syracuseStep 1698091 = 2547137) B2547137
theorem B9668909 : Blo 1697549 9668909 := bstep (se 3 (by rfl) ⟨1812920, by rfl⟩ : syracuseStep 9668909 = 3625841) B3625841
theorem B1698103 : Blo 1697549 1698103 := bstep (se 1 (by rfl) ⟨1273577, by rfl⟩ : syracuseStep 1698103 = 2547155) B2547155
theorem B4081985 : Blo 1697549 4081985 := bstep (se 2 (by rfl) ⟨1530744, by rfl⟩ : syracuseStep 4081985 = 3061489) B3061489
theorem B3819851 : Blo 1697549 3819851 := bstep (se 1 (by rfl) ⟨2864888, by rfl⟩ : syracuseStep 3819851 = 5729777) B5729777
theorem B1698123 : Blo 1697549 1698123 := bstep (se 1 (by rfl) ⟨1273592, by rfl⟩ : syracuseStep 1698123 = 2547185) B2547185
theorem B1698135 : Blo 1697549 1698135 := bstep (se 1 (by rfl) ⟨1273601, by rfl⟩ : syracuseStep 1698135 = 2547203) B2547203
theorem B1911127 : Blo 1697549 1911127 := bstep (se 1 (by rfl) ⟨1433345, by rfl⟩ : syracuseStep 1911127 = 2866691) B2866691
theorem B1698155 : Blo 1697549 1698155 := bstep (se 1 (by rfl) ⟨1273616, by rfl⟩ : syracuseStep 1698155 = 2547233) B2547233
theorem B1698167 : Blo 1697549 1698167 := bstep (se 1 (by rfl) ⟨1273625, by rfl⟩ : syracuseStep 1698167 = 2547251) B2547251
theorem B3819905 : Blo 1697549 3819905 := bstep (se 2 (by rfl) ⟨1432464, by rfl⟩ : syracuseStep 3819905 = 2864929) B2864929
theorem B1698187 : Blo 1697549 1698187 := bstep (se 1 (by rfl) ⟨1273640, by rfl⟩ : syracuseStep 1698187 = 2547281) B2547281
theorem B1698199 : Blo 1697549 1698199 := bstep (se 1 (by rfl) ⟨1273649, by rfl⟩ : syracuseStep 1698199 = 2547299) B2547299
theorem B1698219 : Blo 1697549 1698219 := bstep (se 1 (by rfl) ⟨1273664, by rfl⟩ : syracuseStep 1698219 = 2547329) B2547329
theorem B18360755 : Blo 1697549 18360755 := bstep (se 1 (by rfl) ⟨13770566, by rfl⟩ : syracuseStep 18360755 = 27541133) B27541133
theorem B1698231 : Blo 1697549 1698231 := bstep (se 1 (by rfl) ⟨1273673, by rfl⟩ : syracuseStep 1698231 = 2547347) B2547347
theorem B1698251 : Blo 1697549 1698251 := bstep (se 1 (by rfl) ⟨1273688, by rfl⟩ : syracuseStep 1698251 = 2547377) B2547377
theorem B1698263 : Blo 1697549 1698263 := bstep (se 1 (by rfl) ⟨1273697, by rfl⟩ : syracuseStep 1698263 = 2547395) B2547395
theorem B2722265 : Blo 1697549 2722265 := bstep (se 2 (by rfl) ⟨1020849, by rfl⟩ : syracuseStep 2722265 = 2041699) B2041699
theorem B1698283 : Blo 1697549 1698283 := bstep (se 1 (by rfl) ⟨1273712, by rfl⟩ : syracuseStep 1698283 = 2547425) B2547425
theorem B1698295 : Blo 1697549 1698295 := bstep (se 1 (by rfl) ⟨1273721, by rfl⟩ : syracuseStep 1698295 = 2547443) B2547443
theorem B1698315 : Blo 1697549 1698315 := bstep (se 1 (by rfl) ⟨1273736, by rfl⟩ : syracuseStep 1698315 = 2547473) B2547473
theorem B1911307 : Blo 1697549 1911307 := bstep (se 1 (by rfl) ⟨1433480, by rfl⟩ : syracuseStep 1911307 = 2866961) B2866961
theorem B14510609 : Blo 1697549 14510609 := bstep (se 2 (by rfl) ⟨5441478, by rfl⟩ : syracuseStep 14510609 = 10882957) B10882957
theorem B4590103 : Blo 1697549 4590103 := bstep (se 1 (by rfl) ⟨3442577, by rfl⟩ : syracuseStep 4590103 = 6885155) B6885155
theorem B1698327 : Blo 1697549 1698327 := bstep (se 1 (by rfl) ⟨1273745, by rfl⟩ : syracuseStep 1698327 = 2547491) B2547491
theorem B1698347 : Blo 1697549 1698347 := bstep (se 1 (by rfl) ⟨1273760, by rfl⟩ : syracuseStep 1698347 = 2547521) B2547521
theorem B1698359 : Blo 1697549 1698359 := bstep (se 1 (by rfl) ⟨1273769, by rfl⟩ : syracuseStep 1698359 = 2547539) B2547539
theorem B8596043 : Blo 1697549 8596043 := bstep (se 1 (by rfl) ⟨6447032, by rfl⟩ : syracuseStep 8596043 = 12894065) B12894065
theorem B1698379 : Blo 1697549 1698379 := bstep (se 1 (by rfl) ⟨1273784, by rfl⟩ : syracuseStep 1698379 = 2547569) B2547569
theorem B1698391 : Blo 1697549 1698391 := bstep (se 1 (by rfl) ⟨1273793, by rfl⟩ : syracuseStep 1698391 = 2547587) B2547587
theorem B3820121 : Blo 1697549 3820121 := bstep (se 2 (by rfl) ⟨1432545, by rfl⟩ : syracuseStep 3820121 = 2865091) B2865091
theorem B17001053 : Blo 1697549 17001053 := bstep (se 3 (by rfl) ⟨3187697, by rfl⟩ : syracuseStep 17001053 = 6375395) B6375395
theorem B1698411 : Blo 1697549 1698411 := bstep (se 1 (by rfl) ⟨1273808, by rfl⟩ : syracuseStep 1698411 = 2547617) B2547617
theorem B1698423 : Blo 1697549 1698423 := bstep (se 1 (by rfl) ⟨1273817, by rfl⟩ : syracuseStep 1698423 = 2547635) B2547635
theorem B1911415 : Blo 1697549 1911415 := bstep (se 1 (by rfl) ⟨1433561, by rfl⟩ : syracuseStep 1911415 = 2867123) B2867123
theorem B1698443 : Blo 1697549 1698443 := bstep (se 1 (by rfl) ⟨1273832, by rfl⟩ : syracuseStep 1698443 = 2547665) B2547665
theorem B3443339 : Blo 1697549 3443339 := bstep (se 1 (by rfl) ⟨2582504, by rfl⟩ : syracuseStep 3443339 = 5165009) B5165009
theorem B1698455 : Blo 1697549 1698455 := bstep (se 1 (by rfl) ⟨1273841, by rfl⟩ : syracuseStep 1698455 = 2547683) B2547683
theorem B1698475 : Blo 1697549 1698475 := bstep (se 1 (by rfl) ⟨1273856, by rfl⟩ : syracuseStep 1698475 = 2547713) B2547713
theorem B15706801 : Blo 1697549 15706801 := bstep (se 2 (by rfl) ⟨5890050, by rfl⟩ : syracuseStep 15706801 = 11780101) B11780101
theorem B3820211 : Blo 1697549 3820211 := bstep (se 1 (by rfl) ⟨2865158, by rfl⟩ : syracuseStep 3820211 = 5730317) B5730317
theorem B1698487 : Blo 1697549 1698487 := bstep (se 1 (by rfl) ⟨1273865, by rfl⟩ : syracuseStep 1698487 = 2547731) B2547731
theorem B1698507 : Blo 1697549 1698507 := bstep (se 1 (by rfl) ⟨1273880, by rfl⟩ : syracuseStep 1698507 = 2547761) B2547761
theorem B3820247 : Blo 1697549 3820247 := bstep (se 1 (by rfl) ⟨2865185, by rfl⟩ : syracuseStep 3820247 = 5730371) B5730371
theorem B1698519 : Blo 1697549 1698519 := bstep (se 1 (by rfl) ⟨1273889, by rfl⟩ : syracuseStep 1698519 = 2547779) B2547779
theorem B1698539 : Blo 1697549 1698539 := bstep (se 1 (by rfl) ⟨1273904, by rfl⟩ : syracuseStep 1698539 = 2547809) B2547809
theorem B1698551 : Blo 1697549 1698551 := bstep (se 1 (by rfl) ⟨1273913, by rfl⟩ : syracuseStep 1698551 = 2547827) B2547827
theorem B1698571 : Blo 1697549 1698571 := bstep (se 1 (by rfl) ⟨1273928, by rfl⟩ : syracuseStep 1698571 = 2547857) B2547857
theorem B1813271 : Blo 1697549 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B1698583 : Blo 1697549 1698583 := bstep (se 1 (by rfl) ⟨1273937, by rfl⟩ : syracuseStep 1698583 = 2547875) B2547875
theorem B1698603 : Blo 1697549 1698603 := bstep (se 1 (by rfl) ⟨1273952, by rfl⟩ : syracuseStep 1698603 = 2547905) B2547905
theorem B1911595 : Blo 1697549 1911595 := bstep (se 1 (by rfl) ⟨1433696, by rfl⟩ : syracuseStep 1911595 = 2867393) B2867393
theorem B1698615 : Blo 1697549 1698615 := bstep (se 1 (by rfl) ⟨1273961, by rfl⟩ : syracuseStep 1698615 = 2547923) B2547923
theorem B5163841 : Blo 1697549 5163841 := bstep (se 2 (by rfl) ⟨1936440, by rfl⟩ : syracuseStep 5163841 = 3872881) B3872881
theorem B7252811 : Blo 1697549 7252811 := bstep (se 1 (by rfl) ⟨5439608, by rfl⟩ : syracuseStep 7252811 = 10879217) B10879217
theorem B1698635 : Blo 1697549 1698635 := bstep (se 1 (by rfl) ⟨1273976, by rfl⟩ : syracuseStep 1698635 = 2547953) B2547953
theorem B1698647 : Blo 1697549 1698647 := bstep (se 1 (by rfl) ⟨1273985, by rfl⟩ : syracuseStep 1698647 = 2547971) B2547971
theorem B1698667 : Blo 1697549 1698667 := bstep (se 1 (by rfl) ⟨1274000, by rfl⟩ : syracuseStep 1698667 = 2548001) B2548001
theorem B1698679 : Blo 1697549 1698679 := bstep (se 1 (by rfl) ⟨1274009, by rfl⟩ : syracuseStep 1698679 = 2548019) B2548019
theorem B3820427 : Blo 1697549 3820427 := bstep (se 1 (by rfl) ⟨2865320, by rfl⟩ : syracuseStep 3820427 = 5730641) B5730641
theorem B1698699 : Blo 1697549 1698699 := bstep (se 1 (by rfl) ⟨1274024, by rfl⟩ : syracuseStep 1698699 = 2548049) B2548049
theorem B1698711 : Blo 1697549 1698711 := bstep (se 1 (by rfl) ⟨1274033, by rfl⟩ : syracuseStep 1698711 = 2548067) B2548067
theorem B2796439 : Blo 1697549 2796439 := bstep (se 1 (by rfl) ⟨2097329, by rfl⟩ : syracuseStep 2796439 = 4194659) B4194659
theorem B1911703 : Blo 1697549 1911703 := bstep (se 1 (by rfl) ⟨1433777, by rfl⟩ : syracuseStep 1911703 = 2867555) B2867555
theorem B1698731 : Blo 1697549 1698731 := bstep (se 1 (by rfl) ⟨1274048, by rfl⟩ : syracuseStep 1698731 = 2548097) B2548097
theorem B6122413 : Blo 1697549 6122413 := bstep (se 3 (by rfl) ⟨1147952, by rfl⟩ : syracuseStep 6122413 = 2295905) B2295905
theorem B1698743 : Blo 1697549 1698743 := bstep (se 1 (by rfl) ⟨1274057, by rfl⟩ : syracuseStep 1698743 = 2548115) B2548115
theorem B3820481 : Blo 1697549 3820481 := bstep (se 2 (by rfl) ⟨1432680, by rfl⟩ : syracuseStep 3820481 = 2865361) B2865361
theorem B1698763 : Blo 1697549 1698763 := bstep (se 1 (by rfl) ⟨1274072, by rfl⟩ : syracuseStep 1698763 = 2548145) B2548145
theorem B1698775 : Blo 1697549 1698775 := bstep (se 1 (by rfl) ⟨1274081, by rfl⟩ : syracuseStep 1698775 = 2548163) B2548163
theorem B4590557 : Blo 1697549 4590557 := bstep (se 3 (by rfl) ⟨860729, by rfl⟩ : syracuseStep 4590557 = 1721459) B1721459
theorem B1698795 : Blo 1697549 1698795 := bstep (se 1 (by rfl) ⟨1274096, by rfl⟩ : syracuseStep 1698795 = 2548193) B2548193
theorem B1698807 : Blo 1697549 1698807 := bstep (se 1 (by rfl) ⟨1274105, by rfl⟩ : syracuseStep 1698807 = 2548211) B2548211
theorem B1698827 : Blo 1697549 1698827 := bstep (se 1 (by rfl) ⟨1274120, by rfl⟩ : syracuseStep 1698827 = 2548241) B2548241
theorem B1698839 : Blo 1697549 1698839 := bstep (se 1 (by rfl) ⟨1274129, by rfl⟩ : syracuseStep 1698839 = 2548259) B2548259
theorem B20671523 : Blo 1697549 20671523 := bstep (se 1 (by rfl) ⟨15503642, by rfl⟩ : syracuseStep 20671523 = 31007285) B31007285
theorem B1698859 : Blo 1697549 1698859 := bstep (se 1 (by rfl) ⟨1274144, by rfl⟩ : syracuseStep 1698859 = 2548289) B2548289
theorem B1698871 : Blo 1697549 1698871 := bstep (se 1 (by rfl) ⟨1274153, by rfl⟩ : syracuseStep 1698871 = 2548307) B2548307
theorem B5729345 : Blo 1697549 5729345 := bstep (se 2 (by rfl) ⟨2148504, by rfl⟩ : syracuseStep 5729345 = 4297009) B4297009
theorem B55086155 : Blo 1697549 55086155 := bstep (se 1 (by rfl) ⟨41314616, by rfl⟩ : syracuseStep 55086155 = 82629233) B82629233
theorem B1698891 : Blo 1697549 1698891 := bstep (se 1 (by rfl) ⟨1274168, by rfl⟩ : syracuseStep 1698891 = 2548337) B2548337
theorem B1911883 : Blo 1697549 1911883 := bstep (se 1 (by rfl) ⟨1433912, by rfl⟩ : syracuseStep 1911883 = 2867825) B2867825
theorem B1698903 : Blo 1697549 1698903 := bstep (se 1 (by rfl) ⟨1274177, by rfl⟩ : syracuseStep 1698903 = 2548355) B2548355
theorem B1698923 : Blo 1697549 1698923 := bstep (se 1 (by rfl) ⟨1274192, by rfl⟩ : syracuseStep 1698923 = 2548385) B2548385
theorem B1698935 : Blo 1697549 1698935 := bstep (se 1 (by rfl) ⟨1274201, by rfl⟩ : syracuseStep 1698935 = 2548403) B2548403
theorem B1698955 : Blo 1697549 1698955 := bstep (se 1 (by rfl) ⟨1274216, by rfl⟩ : syracuseStep 1698955 = 2548433) B2548433
theorem B1698967 : Blo 1697549 1698967 := bstep (se 1 (by rfl) ⟨1274225, by rfl⟩ : syracuseStep 1698967 = 2548451) B2548451
theorem B3820697 : Blo 1697549 3820697 := bstep (se 2 (by rfl) ⟨1432761, by rfl⟩ : syracuseStep 3820697 = 2865523) B2865523
theorem B1698987 : Blo 1697549 1698987 := bstep (se 1 (by rfl) ⟨1274240, by rfl⟩ : syracuseStep 1698987 = 2548481) B2548481
theorem B7253171 : Blo 1697549 7253171 := bstep (se 1 (by rfl) ⟨5439878, by rfl⟩ : syracuseStep 7253171 = 10879757) B10879757
theorem B1698999 : Blo 1697549 1698999 := bstep (se 1 (by rfl) ⟨1274249, by rfl⟩ : syracuseStep 1698999 = 2548499) B2548499
theorem B1911991 : Blo 1697549 1911991 := bstep (se 1 (by rfl) ⟨1433993, by rfl⟩ : syracuseStep 1911991 = 2867987) B2867987
theorem B1699019 : Blo 1697549 1699019 := bstep (se 1 (by rfl) ⟨1274264, by rfl⟩ : syracuseStep 1699019 = 2548529) B2548529
theorem B1699031 : Blo 1697549 1699031 := bstep (se 1 (by rfl) ⟨1274273, by rfl⟩ : syracuseStep 1699031 = 2548547) B2548547
theorem B2583769 : Blo 1697549 2583769 := bstep (se 2 (by rfl) ⟨968913, by rfl⟩ : syracuseStep 2583769 = 1937827) B1937827
theorem B1699051 : Blo 1697549 1699051 := bstep (se 1 (by rfl) ⟨1274288, by rfl⟩ : syracuseStep 1699051 = 2548577) B2548577
theorem B3820787 : Blo 1697549 3820787 := bstep (se 1 (by rfl) ⟨2865590, by rfl⟩ : syracuseStep 3820787 = 5731181) B5731181
theorem B1699063 : Blo 1697549 1699063 := bstep (se 1 (by rfl) ⟨1274297, by rfl⟩ : syracuseStep 1699063 = 2548595) B2548595
theorem B1699083 : Blo 1697549 1699083 := bstep (se 1 (by rfl) ⟨1274312, by rfl⟩ : syracuseStep 1699083 = 2548625) B2548625
theorem B3820823 : Blo 1697549 3820823 := bstep (se 1 (by rfl) ⟨2865617, by rfl⟩ : syracuseStep 3820823 = 5731235) B5731235
theorem B4836631 : Blo 1697549 4836631 := bstep (se 1 (by rfl) ⟨3627473, by rfl⟩ : syracuseStep 4836631 = 7254947) B7254947
theorem B1699095 : Blo 1697549 1699095 := bstep (se 1 (by rfl) ⟨1274321, by rfl⟩ : syracuseStep 1699095 = 2548643) B2548643
theorem B1699115 : Blo 1697549 1699115 := bstep (se 1 (by rfl) ⟨1274336, by rfl⟩ : syracuseStep 1699115 = 2548673) B2548673
theorem B1699127 : Blo 1697549 1699127 := bstep (se 1 (by rfl) ⟨1274345, by rfl⟩ : syracuseStep 1699127 = 2548691) B2548691
theorem B1699147 : Blo 1697549 1699147 := bstep (se 1 (by rfl) ⟨1274360, by rfl⟩ : syracuseStep 1699147 = 2548721) B2548721
theorem B1699159 : Blo 1697549 1699159 := bstep (se 1 (by rfl) ⟨1274369, by rfl⟩ : syracuseStep 1699159 = 2548739) B2548739
theorem B1699179 : Blo 1697549 1699179 := bstep (se 1 (by rfl) ⟨1274384, by rfl⟩ : syracuseStep 1699179 = 2548769) B2548769
theorem B1699191 : Blo 1697549 1699191 := bstep (se 1 (by rfl) ⟨1274393, by rfl⟩ : syracuseStep 1699191 = 2548787) B2548787
theorem B1699211 : Blo 1697549 1699211 := bstep (se 1 (by rfl) ⟨1274408, by rfl⟩ : syracuseStep 1699211 = 2548817) B2548817
theorem B1699223 : Blo 1697549 1699223 := bstep (se 1 (by rfl) ⟨1274417, by rfl⟩ : syracuseStep 1699223 = 2548835) B2548835
theorem B1699243 : Blo 1697549 1699243 := bstep (se 1 (by rfl) ⟨1274432, by rfl⟩ : syracuseStep 1699243 = 2548865) B2548865
theorem B1699255 : Blo 1697549 1699255 := bstep (se 1 (by rfl) ⟨1274441, by rfl⟩ : syracuseStep 1699255 = 2548883) B2548883
theorem B3059147 : Blo 1697549 3059147 := bstep (se 1 (by rfl) ⟨2294360, by rfl⟩ : syracuseStep 3059147 = 4588721) B4588721
theorem B3821003 : Blo 1697549 3821003 := bstep (se 1 (by rfl) ⟨2865752, by rfl⟩ : syracuseStep 3821003 = 5731505) B5731505
theorem B1813963 : Blo 1697549 1813963 := bstep (se 1 (by rfl) ⟨1360472, by rfl⟩ : syracuseStep 1813963 = 2720945) B2720945
theorem B1699275 : Blo 1697549 1699275 := bstep (se 1 (by rfl) ⟨1274456, by rfl⟩ : syracuseStep 1699275 = 2548913) B2548913
theorem B1699287 : Blo 1697549 1699287 := bstep (se 1 (by rfl) ⟨1274465, by rfl⟩ : syracuseStep 1699287 = 2548931) B2548931
theorem B1699307 : Blo 1697549 1699307 := bstep (se 1 (by rfl) ⟨1274480, by rfl⟩ : syracuseStep 1699307 = 2548961) B2548961
theorem B1699319 : Blo 1697549 1699319 := bstep (se 1 (by rfl) ⟨1274489, by rfl⟩ : syracuseStep 1699319 = 2548979) B2548979
theorem B3821057 : Blo 1697549 3821057 := bstep (se 2 (by rfl) ⟨1432896, by rfl⟩ : syracuseStep 3821057 = 2865793) B2865793
theorem B1699339 : Blo 1697549 1699339 := bstep (se 1 (by rfl) ⟨1274504, by rfl⟩ : syracuseStep 1699339 = 2549009) B2549009
theorem B1699351 : Blo 1697549 1699351 := bstep (se 1 (by rfl) ⟨1274513, by rfl⟩ : syracuseStep 1699351 = 2549027) B2549027
theorem B1699371 : Blo 1697549 1699371 := bstep (se 1 (by rfl) ⟨1274528, by rfl⟩ : syracuseStep 1699371 = 2549057) B2549057
theorem B3223091 : Blo 1697549 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B1699383 : Blo 1697549 1699383 := bstep (se 1 (by rfl) ⟨1274537, by rfl⟩ : syracuseStep 1699383 = 2549075) B2549075
theorem B15502913 : Blo 1697549 15502913 := bstep (se 2 (by rfl) ⟨5813592, by rfl⟩ : syracuseStep 15502913 = 11627185) B11627185
theorem B1699403 : Blo 1697549 1699403 := bstep (se 1 (by rfl) ⟨1274552, by rfl⟩ : syracuseStep 1699403 = 2549105) B2549105
theorem B1699415 : Blo 1697549 1699415 := bstep (se 1 (by rfl) ⟨1274561, by rfl⟩ : syracuseStep 1699415 = 2549123) B2549123
theorem B5729885 : Blo 1697549 5729885 := bstep (se 3 (by rfl) ⟨1074353, by rfl⟩ : syracuseStep 5729885 = 2148707) B2148707
theorem B26152541 : Blo 1697549 26152541 := bstep (se 3 (by rfl) ⟨4903601, by rfl⟩ : syracuseStep 26152541 = 9807203) B9807203
theorem B1699435 : Blo 1697549 1699435 := bstep (se 1 (by rfl) ⟨1274576, by rfl⟩ : syracuseStep 1699435 = 2549153) B2549153
theorem B1699447 : Blo 1697549 1699447 := bstep (se 1 (by rfl) ⟨1274585, by rfl⟩ : syracuseStep 1699447 = 2549171) B2549171
theorem B1699467 : Blo 1697549 1699467 := bstep (se 1 (by rfl) ⟨1274600, by rfl⟩ : syracuseStep 1699467 = 2549201) B2549201
theorem B1699479 : Blo 1697549 1699479 := bstep (se 1 (by rfl) ⟨1274609, by rfl⟩ : syracuseStep 1699479 = 2549219) B2549219
theorem B1699499 : Blo 1697549 1699499 := bstep (se 1 (by rfl) ⟨1274624, by rfl⟩ : syracuseStep 1699499 = 2549249) B2549249
theorem B9186995 : Blo 1697549 9186995 := bstep (se 1 (by rfl) ⟨6890246, by rfl⟩ : syracuseStep 9186995 = 13780493) B13780493
theorem B1699511 : Blo 1697549 1699511 := bstep (se 1 (by rfl) ⟨1274633, by rfl⟩ : syracuseStep 1699511 = 2549267) B2549267
theorem B3223243 : Blo 1697549 3223243 := bstep (se 1 (by rfl) ⟨2417432, by rfl⟩ : syracuseStep 3223243 = 4834865) B4834865
theorem B1699531 : Blo 1697549 1699531 := bstep (se 1 (by rfl) ⟨1274648, by rfl⟩ : syracuseStep 1699531 = 2549297) B2549297
theorem B1699543 : Blo 1697549 1699543 := bstep (se 1 (by rfl) ⟨1274657, by rfl⟩ : syracuseStep 1699543 = 2549315) B2549315
theorem B3821273 : Blo 1697549 3821273 := bstep (se 2 (by rfl) ⟨1432977, by rfl⟩ : syracuseStep 3821273 = 2865955) B2865955
theorem B2150155 : Blo 1697549 2150155 := bstep (se 1 (by rfl) ⟨1612616, by rfl⟩ : syracuseStep 2150155 = 3225233) B3225233
theorem B3821363 : Blo 1697549 3821363 := bstep (se 1 (by rfl) ⟨2866022, by rfl⟩ : syracuseStep 3821363 = 5732045) B5732045
theorem B3821399 : Blo 1697549 3821399 := bstep (se 1 (by rfl) ⟨2866049, by rfl⟩ : syracuseStep 3821399 = 5732099) B5732099
theorem B16994225 : Blo 1697549 16994225 := bstep (se 2 (by rfl) ⟨6372834, by rfl⟩ : syracuseStep 16994225 = 12745669) B12745669
theorem B3821579 : Blo 1697549 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B3223577 : Blo 1697549 3223577 := bstep (se 2 (by rfl) ⟨1208841, by rfl⟩ : syracuseStep 3223577 = 2417683) B2417683
theorem B3821633 : Blo 1697549 3821633 := bstep (se 2 (by rfl) ⟨1433112, by rfl⟩ : syracuseStep 3821633 = 2866225) B2866225
theorem B27545669 : Blo 1697549 27545669 := bstep (se 4 (by rfl) ⟨2582406, by rfl⟩ : syracuseStep 27545669 = 5164813) B5164813
theorem B161288333 : Blo 1697549 161288333 := bstep (se 3 (by rfl) ⟨30241562, by rfl⟩ : syracuseStep 161288333 = 60483125) B60483125
theorem B3821849 : Blo 1697549 3821849 := bstep (se 2 (by rfl) ⟨1433193, by rfl⟩ : syracuseStep 3821849 = 2866387) B2866387
theorem B55103789 : Blo 1697549 55103789 := bstep (se 3 (by rfl) ⟨10331960, by rfl⟩ : syracuseStep 55103789 = 20663921) B20663921
theorem B8597825 : Blo 1697549 8597825 := bstep (se 2 (by rfl) ⟨3224184, by rfl⟩ : syracuseStep 8597825 = 6448369) B6448369
theorem B8278337 : Blo 1697549 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B3821939 : Blo 1697549 3821939 := bstep (se 1 (by rfl) ⟨2866454, by rfl⟩ : syracuseStep 3821939 = 5732909) B5732909
theorem B3821975 : Blo 1697549 3821975 := bstep (se 1 (by rfl) ⟨2866481, by rfl⟩ : syracuseStep 3821975 = 5732963) B5732963
theorem B6451757 : Blo 1697549 6451757 := bstep (se 3 (by rfl) ⟨1209704, by rfl⟩ : syracuseStep 6451757 = 2419409) B2419409
theorem B3822155 : Blo 1697549 3822155 := bstep (se 1 (by rfl) ⟨2866616, by rfl⟩ : syracuseStep 3822155 = 5733233) B5733233
theorem B4837963 : Blo 1697549 4837963 := bstep (se 1 (by rfl) ⟨3628472, by rfl⟩ : syracuseStep 4837963 = 7256945) B7256945
theorem B3822209 : Blo 1697549 3822209 := bstep (se 2 (by rfl) ⟨1433328, by rfl⟩ : syracuseStep 3822209 = 2866657) B2866657
theorem B3224215 : Blo 1697549 3224215 := bstep (se 1 (by rfl) ⟨2418161, by rfl⟩ : syracuseStep 3224215 = 4836323) B4836323
theorem B10326707 : Blo 1697549 10326707 := bstep (se 1 (by rfl) ⟨7745030, by rfl⟩ : syracuseStep 10326707 = 15490061) B15490061
theorem B5731019 : Blo 1697549 5731019 := bstep (se 1 (by rfl) ⟨4298264, by rfl⟩ : syracuseStep 5731019 = 8596529) B8596529
theorem B29012741 : Blo 1697549 29012741 := bstep (se 4 (by rfl) ⟨2719944, by rfl⟩ : syracuseStep 29012741 = 5439889) B5439889
theorem B3625739 : Blo 1697549 3625739 := bstep (se 1 (by rfl) ⟨2719304, by rfl⟩ : syracuseStep 3625739 = 5438609) B5438609
theorem B4297495 : Blo 1697549 4297495 := bstep (se 1 (by rfl) ⟨3223121, by rfl⟩ : syracuseStep 4297495 = 6446243) B6446243
theorem B18371393 : Blo 1697549 18371393 := bstep (se 2 (by rfl) ⟨6889272, by rfl⟩ : syracuseStep 18371393 = 13778545) B13778545
theorem B3822425 : Blo 1697549 3822425 := bstep (se 2 (by rfl) ⟨1433409, by rfl⟩ : syracuseStep 3822425 = 2866819) B2866819
theorem B4838237 : Blo 1697549 4838237 := bstep (se 3 (by rfl) ⟨907169, by rfl⟩ : syracuseStep 4838237 = 1814339) B1814339
theorem B3822515 : Blo 1697549 3822515 := bstep (se 1 (by rfl) ⟨2866886, by rfl⟩ : syracuseStep 3822515 = 5733773) B5733773
theorem B3822551 : Blo 1697549 3822551 := bstep (se 1 (by rfl) ⟨2866913, by rfl⟩ : syracuseStep 3822551 = 5733827) B5733827
theorem B5731289 : Blo 1697549 5731289 := bstep (se 2 (by rfl) ⟨2149233, by rfl⟩ : syracuseStep 5731289 = 4298467) B4298467
theorem B3822731 : Blo 1697549 3822731 := bstep (se 1 (by rfl) ⟨2867048, by rfl⟩ : syracuseStep 3822731 = 5734097) B5734097
theorem B4838579 : Blo 1697549 4838579 := bstep (se 1 (by rfl) ⟨3628934, by rfl⟩ : syracuseStep 4838579 = 7257869) B7257869
theorem B3822785 : Blo 1697549 3822785 := bstep (se 2 (by rfl) ⟨1433544, by rfl⟩ : syracuseStep 3822785 = 2867089) B2867089
theorem B4297931 : Blo 1697549 4297931 := bstep (se 1 (by rfl) ⟨3223448, by rfl⟩ : syracuseStep 4297931 = 6446897) B6446897
theorem B3626201 : Blo 1697549 3626201 := bstep (se 2 (by rfl) ⟨1359825, by rfl⟩ : syracuseStep 3626201 = 2719651) B2719651
theorem B6452531 : Blo 1697549 6452531 := bstep (se 1 (by rfl) ⟨4839398, by rfl⟩ : syracuseStep 6452531 = 9678797) B9678797
theorem B6886745 : Blo 1697549 6886745 := bstep (se 2 (by rfl) ⟨2582529, by rfl⟩ : syracuseStep 6886745 = 5165059) B5165059
theorem B8164739 : Blo 1697549 8164739 := bstep (se 1 (by rfl) ⟨6123554, by rfl⟩ : syracuseStep 8164739 = 12247109) B12247109
theorem B2905483 : Blo 1697549 2905483 := bstep (se 1 (by rfl) ⟨2179112, by rfl⟩ : syracuseStep 2905483 = 4358225) B4358225
theorem B3823001 : Blo 1697549 3823001 := bstep (se 2 (by rfl) ⟨1433625, by rfl⟩ : syracuseStep 3823001 = 2867251) B2867251
theorem B3225035 : Blo 1697549 3225035 := bstep (se 1 (by rfl) ⟨2418776, by rfl⟩ : syracuseStep 3225035 = 4837553) B4837553
theorem B5969369 : Blo 1697549 5969369 := bstep (se 2 (by rfl) ⟨2238513, by rfl⟩ : syracuseStep 5969369 = 4477027) B4477027
theorem B3823091 : Blo 1697549 3823091 := bstep (se 1 (by rfl) ⟨2867318, by rfl⟩ : syracuseStep 3823091 = 5734637) B5734637
theorem B3225089 : Blo 1697549 3225089 := bstep (se 2 (by rfl) ⟨1209408, by rfl⟩ : syracuseStep 3225089 = 2418817) B2418817
theorem B3823127 : Blo 1697549 3823127 := bstep (se 1 (by rfl) ⟨2867345, by rfl⟩ : syracuseStep 3823127 = 5734691) B5734691
theorem B4298305 : Blo 1697549 4298305 := bstep (se 2 (by rfl) ⟨1611864, by rfl⟩ : syracuseStep 4298305 = 3223729) B3223729
theorem B6534749 : Blo 1697549 6534749 := bstep (se 3 (by rfl) ⟨1225265, by rfl⟩ : syracuseStep 6534749 = 2450531) B2450531
theorem B5731991 : Blo 1697549 5731991 := bstep (se 1 (by rfl) ⟨4298993, by rfl⟩ : syracuseStep 5731991 = 8597987) B8597987
theorem B3823307 : Blo 1697549 3823307 := bstep (se 1 (by rfl) ⟨2867480, by rfl⟩ : syracuseStep 3823307 = 5734961) B5734961
theorem B2864855 : Blo 1697549 2864855 := bstep (se 1 (by rfl) ⟨2148641, by rfl⟩ : syracuseStep 2864855 = 4297283) B4297283
theorem B3823361 : Blo 1697549 3823361 := bstep (se 2 (by rfl) ⟨1433760, by rfl⟩ : syracuseStep 3823361 = 2867521) B2867521
theorem B10884881 : Blo 1697549 10884881 := bstep (se 2 (by rfl) ⟨4081830, by rfl⟩ : syracuseStep 10884881 = 8163661) B8163661
theorem B2864983 : Blo 1697549 2864983 := bstep (se 1 (by rfl) ⟨2148737, by rfl⟩ : syracuseStep 2864983 = 4297475) B4297475
theorem B3872627 : Blo 1697549 3872627 := bstep (se 1 (by rfl) ⟨2904470, by rfl⟩ : syracuseStep 3872627 = 5808941) B5808941
theorem B12892121 : Blo 1697549 12892121 := bstep (se 2 (by rfl) ⟨4834545, by rfl⟩ : syracuseStep 12892121 = 9669091) B9669091
theorem B3823577 : Blo 1697549 3823577 := bstep (se 2 (by rfl) ⟨1433841, by rfl⟩ : syracuseStep 3823577 = 2867683) B2867683
theorem B3061783 : Blo 1697549 3061783 := bstep (se 1 (by rfl) ⟨2296337, by rfl⟩ : syracuseStep 3061783 = 4592675) B4592675
theorem B3823667 : Blo 1697549 3823667 := bstep (se 1 (by rfl) ⟨2867750, by rfl⟩ : syracuseStep 3823667 = 5735501) B5735501
theorem B3823703 : Blo 1697549 3823703 := bstep (se 1 (by rfl) ⟨2867777, by rfl⟩ : syracuseStep 3823703 = 5735555) B5735555
theorem B4298903 : Blo 1697549 4298903 := bstep (se 1 (by rfl) ⟨3224177, by rfl⟩ : syracuseStep 4298903 = 6448355) B6448355
theorem B5732531 : Blo 1697549 5732531 := bstep (se 1 (by rfl) ⟨4299398, by rfl⟩ : syracuseStep 5732531 = 8598797) B8598797
theorem B8599769 : Blo 1697549 8599769 := bstep (se 2 (by rfl) ⟨3224913, by rfl⟩ : syracuseStep 8599769 = 6449827) B6449827
theorem B7747805 : Blo 1697549 7747805 := bstep (se 3 (by rfl) ⟨1452713, by rfl⟩ : syracuseStep 7747805 = 2905427) B2905427
theorem B3823883 : Blo 1697549 3823883 := bstep (se 1 (by rfl) ⟨2867912, by rfl⟩ : syracuseStep 3823883 = 5735825) B5735825
theorem B9435437 : Blo 1697549 9435437 := bstep (se 3 (by rfl) ⟨1769144, by rfl⟩ : syracuseStep 9435437 = 3538289) B3538289
theorem B3823937 : Blo 1697549 3823937 := bstep (se 2 (by rfl) ⟨1433976, by rfl⟩ : syracuseStep 3823937 = 2867953) B2867953
theorem B3627379 : Blo 1697549 3627379 := bstep (se 1 (by rfl) ⟨2720534, by rfl⟩ : syracuseStep 3627379 = 5441069) B5441069
theorem B3226007 : Blo 1697549 3226007 := bstep (se 1 (by rfl) ⟨2419505, by rfl⟩ : syracuseStep 3226007 = 4839011) B4839011
theorem B5732801 : Blo 1697549 5732801 := bstep (se 2 (by rfl) ⟨2149800, by rfl⟩ : syracuseStep 5732801 = 4299601) B4299601
theorem B2865611 : Blo 1697549 2865611 := bstep (se 1 (by rfl) ⟨2149208, by rfl⟩ : syracuseStep 2865611 = 4298417) B4298417
theorem B12900869 : Blo 1697549 12900869 := bstep (se 4 (by rfl) ⟨1209456, by rfl⟩ : syracuseStep 12900869 = 2418913) B2418913
theorem B2865739 : Blo 1697549 2865739 := bstep (se 1 (by rfl) ⟨2149304, by rfl⟩ : syracuseStep 2865739 = 4298609) B4298609
theorem B2546327 : Blo 1697549 2546327 := bstep (se 1 (by rfl) ⟨1909745, by rfl⟩ : syracuseStep 2546327 = 3819491) B3819491
theorem B2546393 : Blo 1697549 2546393 := bstep (se 2 (by rfl) ⟨954897, by rfl⟩ : syracuseStep 2546393 = 1909795) B1909795
theorem B2865881 : Blo 1697549 2865881 := bstep (se 2 (by rfl) ⟨1074705, by rfl⟩ : syracuseStep 2865881 = 2149411) B2149411
theorem B3627841 : Blo 1697549 3627841 := bstep (se 2 (by rfl) ⟨1360440, by rfl⟩ : syracuseStep 3627841 = 2720881) B2720881
theorem B2546507 : Blo 1697549 2546507 := bstep (se 1 (by rfl) ⟨1909880, by rfl⟩ : syracuseStep 2546507 = 3819761) B3819761
theorem B2546519 : Blo 1697549 2546519 := bstep (se 1 (by rfl) ⟨1909889, by rfl⟩ : syracuseStep 2546519 = 3819779) B3819779
theorem B2866009 : Blo 1697549 2866009 := bstep (se 2 (by rfl) ⟨1074753, by rfl⟩ : syracuseStep 2866009 = 2149507) B2149507
theorem B2546585 : Blo 1697549 2546585 := bstep (se 2 (by rfl) ⟨954969, by rfl⟩ : syracuseStep 2546585 = 1909939) B1909939
theorem B4299713 : Blo 1697549 4299713 := bstep (se 2 (by rfl) ⟨1612392, by rfl⟩ : syracuseStep 4299713 = 3224785) B3224785
theorem B5733341 : Blo 1697549 5733341 := bstep (se 3 (by rfl) ⟨1075001, by rfl⟩ : syracuseStep 5733341 = 2150003) B2150003
theorem B2546699 : Blo 1697549 2546699 := bstep (se 1 (by rfl) ⟨1910024, by rfl⟩ : syracuseStep 2546699 = 3820049) B3820049
theorem B2546711 : Blo 1697549 2546711 := bstep (se 1 (by rfl) ⟨1910033, by rfl⟩ : syracuseStep 2546711 = 3820067) B3820067
theorem B6888493 : Blo 1697549 6888493 := bstep (se 3 (by rfl) ⟨1291592, by rfl⟩ : syracuseStep 6888493 = 2583185) B2583185
theorem B2546777 : Blo 1697549 2546777 := bstep (se 2 (by rfl) ⟨955041, by rfl⟩ : syracuseStep 2546777 = 1910083) B1910083
theorem B2546891 : Blo 1697549 2546891 := bstep (se 1 (by rfl) ⟨1910168, by rfl⟩ : syracuseStep 2546891 = 3820337) B3820337
theorem B2546903 : Blo 1697549 2546903 := bstep (se 1 (by rfl) ⟨1910177, by rfl⟩ : syracuseStep 2546903 = 3820355) B3820355
theorem B3874049 : Blo 1697549 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B2546969 : Blo 1697549 2546969 := bstep (se 2 (by rfl) ⟨955113, by rfl⟩ : syracuseStep 2546969 = 1910227) B1910227
theorem B6446411 : Blo 1697549 6446411 := bstep (se 1 (by rfl) ⟨4834808, by rfl⟩ : syracuseStep 6446411 = 9669617) B9669617
theorem B6446425 : Blo 1697549 6446425 := bstep (se 2 (by rfl) ⟨2417409, by rfl⟩ : syracuseStep 6446425 = 4834819) B4834819
theorem B2547083 : Blo 1697549 2547083 := bstep (se 1 (by rfl) ⟨1910312, by rfl⟩ : syracuseStep 2547083 = 3820625) B3820625
theorem B2547095 : Blo 1697549 2547095 := bstep (se 1 (by rfl) ⟨1910321, by rfl⟩ : syracuseStep 2547095 = 3820643) B3820643
theorem B2866583 : Blo 1697549 2866583 := bstep (se 1 (by rfl) ⟨2149937, by rfl⟩ : syracuseStep 2866583 = 4299875) B4299875
theorem B2547161 : Blo 1697549 2547161 := bstep (se 2 (by rfl) ⟨955185, by rfl⟩ : syracuseStep 2547161 = 1910371) B1910371
theorem B4300249 : Blo 1697549 4300249 := bstep (se 2 (by rfl) ⟨1612593, by rfl⟩ : syracuseStep 4300249 = 3225187) B3225187
theorem B2866711 : Blo 1697549 2866711 := bstep (se 1 (by rfl) ⟨2150033, by rfl⟩ : syracuseStep 2866711 = 4300067) B4300067
theorem B3628567 : Blo 1697549 3628567 := bstep (se 1 (by rfl) ⟨2721425, by rfl⟩ : syracuseStep 3628567 = 5442851) B5442851
theorem B2547275 : Blo 1697549 2547275 := bstep (se 1 (by rfl) ⟨1910456, by rfl⟩ : syracuseStep 2547275 = 3820913) B3820913
theorem B2547287 : Blo 1697549 2547287 := bstep (se 1 (by rfl) ⟨1910465, by rfl⟩ : syracuseStep 2547287 = 3820931) B3820931
theorem B2547353 : Blo 1697549 2547353 := bstep (se 2 (by rfl) ⟨955257, by rfl⟩ : syracuseStep 2547353 = 1910515) B1910515
theorem B7356163 : Blo 1697549 7356163 := bstep (se 1 (by rfl) ⟨5517122, by rfl⟩ : syracuseStep 7356163 = 11034245) B11034245
theorem B2547467 : Blo 1697549 2547467 := bstep (se 1 (by rfl) ⟨1910600, by rfl⟩ : syracuseStep 2547467 = 3821201) B3821201
theorem B6119185 : Blo 1697549 6119185 := bstep (se 2 (by rfl) ⟨2294694, by rfl⟩ : syracuseStep 6119185 = 4589389) B4589389
theorem B2547479 : Blo 1697549 2547479 := bstep (se 1 (by rfl) ⟨1910609, by rfl⟩ : syracuseStep 2547479 = 3821219) B3821219
theorem B8601389 : Blo 1697549 8601389 := bstep (se 3 (by rfl) ⟨1612760, by rfl⟩ : syracuseStep 8601389 = 3225521) B3225521
theorem B2547545 : Blo 1697549 2547545 := bstep (se 2 (by rfl) ⟨955329, by rfl⟩ : syracuseStep 2547545 = 1910659) B1910659
theorem B2547659 : Blo 1697549 2547659 := bstep (se 1 (by rfl) ⟨1910744, by rfl⟩ : syracuseStep 2547659 = 3821489) B3821489
theorem B2547671 : Blo 1697549 2547671 := bstep (se 1 (by rfl) ⟨1910753, by rfl⟩ : syracuseStep 2547671 = 3821507) B3821507
theorem B2547719 : Blo 1697549 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B2547755 : Blo 1697549 2547755 := bstep (se 1 (by rfl) ⟨1910816, by rfl⟩ : syracuseStep 2547755 = 3821633) B3821633
theorem B2547785 : Blo 1697549 2547785 := bstep (se 2 (by rfl) ⟨955419, by rfl⟩ : syracuseStep 2547785 = 1910839) B1910839
theorem B2547899 : Blo 1697549 2547899 := bstep (se 1 (by rfl) ⟨1910924, by rfl⟩ : syracuseStep 2547899 = 3821849) B3821849
theorem B2547959 : Blo 1697549 2547959 := bstep (se 1 (by rfl) ⟨1910969, by rfl⟩ : syracuseStep 2547959 = 3821939) B3821939
theorem B2547983 : Blo 1697549 2547983 := bstep (se 1 (by rfl) ⟨1910987, by rfl⟩ : syracuseStep 2547983 = 3821975) B3821975
theorem B2548025 : Blo 1697549 2548025 := bstep (se 2 (by rfl) ⟨955509, by rfl⟩ : syracuseStep 2548025 = 1911019) B1911019
theorem B4301171 : Blo 1697549 4301171 := bstep (se 1 (by rfl) ⟨3225878, by rfl⟩ : syracuseStep 4301171 = 6451757) B6451757
theorem B2867575 : Blo 1697549 2867575 := bstep (se 1 (by rfl) ⟨2150681, by rfl⟩ : syracuseStep 2867575 = 4301363) B4301363
theorem B2548103 : Blo 1697549 2548103 := bstep (se 1 (by rfl) ⟨1911077, by rfl⟩ : syracuseStep 2548103 = 3822155) B3822155
theorem B2548139 : Blo 1697549 2548139 := bstep (se 1 (by rfl) ⟨1911104, by rfl⟩ : syracuseStep 2548139 = 3822209) B3822209
theorem B2720201 : Blo 1697549 2720201 := bstep (se 2 (by rfl) ⟨1020075, by rfl⟩ : syracuseStep 2720201 = 2040151) B2040151
theorem B2548169 : Blo 1697549 2548169 := bstep (se 2 (by rfl) ⟨955563, by rfl⟩ : syracuseStep 2548169 = 1911127) B1911127
theorem B26501597 : Blo 1697549 26501597 := bstep (se 3 (by rfl) ⟨4969049, by rfl⟩ : syracuseStep 26501597 = 9938099) B9938099
theorem B19341827 : Blo 1697549 19341827 := bstep (se 1 (by rfl) ⟨14506370, by rfl⟩ : syracuseStep 19341827 = 29012741) B29012741
theorem B2417159 : Blo 1697549 2417159 := bstep (se 1 (by rfl) ⟨1812869, by rfl⟩ : syracuseStep 2417159 = 3625739) B3625739
theorem B12247595 : Blo 1697549 12247595 := bstep (se 1 (by rfl) ⟨9185696, by rfl⟩ : syracuseStep 12247595 = 18371393) B18371393
theorem B2548283 : Blo 1697549 2548283 := bstep (se 1 (by rfl) ⟨1911212, by rfl⟩ : syracuseStep 2548283 = 3822425) B3822425
theorem B2867771 : Blo 1697549 2867771 := bstep (se 1 (by rfl) ⟨2150828, by rfl⟩ : syracuseStep 2867771 = 4301657) B4301657
theorem B8602199 : Blo 1697549 8602199 := bstep (se 1 (by rfl) ⟨6451649, by rfl⟩ : syracuseStep 8602199 = 12903299) B12903299
theorem B2548343 : Blo 1697549 2548343 := bstep (se 1 (by rfl) ⟨1911257, by rfl⟩ : syracuseStep 2548343 = 3822515) B3822515
theorem B2548367 : Blo 1697549 2548367 := bstep (se 1 (by rfl) ⟨1911275, by rfl⟩ : syracuseStep 2548367 = 3822551) B3822551
theorem B2548409 : Blo 1697549 2548409 := bstep (se 2 (by rfl) ⟨955653, by rfl⟩ : syracuseStep 2548409 = 1911307) B1911307
theorem B6120137 : Blo 1697549 6120137 := bstep (se 2 (by rfl) ⟨2295051, by rfl⟩ : syracuseStep 6120137 = 4590103) B4590103
theorem B10617601 : Blo 1697549 10617601 := bstep (se 2 (by rfl) ⟨3981600, by rfl⟩ : syracuseStep 10617601 = 7963201) B7963201
theorem B2548487 : Blo 1697549 2548487 := bstep (se 1 (by rfl) ⟨1911365, by rfl⟩ : syracuseStep 2548487 = 3822731) B3822731
theorem B21775139 : Blo 1697549 21775139 := bstep (se 1 (by rfl) ⟨16331354, by rfl⟩ : syracuseStep 21775139 = 32662709) B32662709
theorem B2548523 : Blo 1697549 2548523 := bstep (se 1 (by rfl) ⟨1911392, by rfl⟩ : syracuseStep 2548523 = 3822785) B3822785
theorem B2417467 : Blo 1697549 2417467 := bstep (se 1 (by rfl) ⟨1813100, by rfl⟩ : syracuseStep 2417467 = 3626201) B3626201
theorem B2548553 : Blo 1697549 2548553 := bstep (se 2 (by rfl) ⟨955707, by rfl⟩ : syracuseStep 2548553 = 1911415) B1911415
theorem B4301687 : Blo 1697549 4301687 := bstep (se 1 (by rfl) ⟨3226265, by rfl⟩ : syracuseStep 4301687 = 6452531) B6452531
theorem B5440391 : Blo 1697549 5440391 := bstep (se 1 (by rfl) ⟨4080293, by rfl⟩ : syracuseStep 5440391 = 8160587) B8160587
theorem B20661155 : Blo 1697549 20661155 := bstep (se 1 (by rfl) ⟨15495866, by rfl⟩ : syracuseStep 20661155 = 30991733) B30991733
theorem B2548667 : Blo 1697549 2548667 := bstep (se 1 (by rfl) ⟨1911500, by rfl⟩ : syracuseStep 2548667 = 3823001) B3823001
theorem B2548727 : Blo 1697549 2548727 := bstep (se 1 (by rfl) ⟨1911545, by rfl⟩ : syracuseStep 2548727 = 3823091) B3823091
theorem B2548751 : Blo 1697549 2548751 := bstep (se 1 (by rfl) ⟨1911563, by rfl⟩ : syracuseStep 2548751 = 3823127) B3823127
theorem B6448157 : Blo 1697549 6448157 := bstep (se 3 (by rfl) ⟨1209029, by rfl⟩ : syracuseStep 6448157 = 2418059) B2418059
theorem B7357483 : Blo 1697549 7357483 := bstep (se 1 (by rfl) ⟨5518112, by rfl⟩ : syracuseStep 7357483 = 11036225) B11036225
theorem B2548793 : Blo 1697549 2548793 := bstep (se 2 (by rfl) ⟨955797, by rfl⟩ : syracuseStep 2548793 = 1911595) B1911595
theorem B8602685 : Blo 1697549 8602685 := bstep (se 3 (by rfl) ⟨1613003, by rfl⟩ : syracuseStep 8602685 = 3226007) B3226007
theorem B4080755 : Blo 1697549 4080755 := bstep (se 1 (by rfl) ⟨3060566, by rfl⟩ : syracuseStep 4080755 = 6121133) B6121133
theorem B2548871 : Blo 1697549 2548871 := bstep (se 1 (by rfl) ⟨1911653, by rfl⟩ : syracuseStep 2548871 = 3823307) B3823307
theorem B1909903 : Blo 1697549 1909903 := bstep (se 1 (by rfl) ⟨1432427, by rfl⟩ : syracuseStep 1909903 = 2864855) B2864855
theorem B2548907 : Blo 1697549 2548907 := bstep (se 1 (by rfl) ⟨1911680, by rfl⟩ : syracuseStep 2548907 = 3823361) B3823361
theorem B3728585 : Blo 1697549 3728585 := bstep (se 2 (by rfl) ⟨1398219, by rfl⟩ : syracuseStep 3728585 = 2796439) B2796439
theorem B2548937 : Blo 1697549 2548937 := bstep (se 2 (by rfl) ⟨955851, by rfl⟩ : syracuseStep 2548937 = 1911703) B1911703
theorem B2581751 : Blo 1697549 2581751 := bstep (se 1 (by rfl) ⟨1936313, by rfl⟩ : syracuseStep 2581751 = 3872627) B3872627
theorem B8594747 : Blo 1697549 8594747 := bstep (se 1 (by rfl) ⟨6446060, by rfl⟩ : syracuseStep 8594747 = 12892121) B12892121
theorem B2549051 : Blo 1697549 2549051 := bstep (se 1 (by rfl) ⟨1911788, by rfl⟩ : syracuseStep 2549051 = 3823577) B3823577
theorem B2549111 : Blo 1697549 2549111 := bstep (se 1 (by rfl) ⟨1911833, by rfl⟩ : syracuseStep 2549111 = 3823667) B3823667
theorem B2549135 : Blo 1697549 2549135 := bstep (se 1 (by rfl) ⟨1911851, by rfl⟩ : syracuseStep 2549135 = 3823703) B3823703
theorem B2549177 : Blo 1697549 2549177 := bstep (se 2 (by rfl) ⟨955941, by rfl⟩ : syracuseStep 2549177 = 1911883) B1911883
theorem B8594909 : Blo 1697549 8594909 := bstep (se 3 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 8594909 = 3223091) B3223091
theorem B2549255 : Blo 1697549 2549255 := bstep (se 1 (by rfl) ⟨1911941, by rfl⟩ : syracuseStep 2549255 = 3823883) B3823883
theorem B2721323 : Blo 1697549 2721323 := bstep (se 1 (by rfl) ⟨2040992, by rfl⟩ : syracuseStep 2721323 = 4081985) B4081985
theorem B2549291 : Blo 1697549 2549291 := bstep (se 1 (by rfl) ⟨1911968, by rfl⟩ : syracuseStep 2549291 = 3823937) B3823937
theorem B2549321 : Blo 1697549 2549321 := bstep (se 2 (by rfl) ⟨955995, by rfl⟩ : syracuseStep 2549321 = 1911991) B1911991
theorem B12240503 : Blo 1697549 12240503 := bstep (se 1 (by rfl) ⟨9180377, by rfl⟩ : syracuseStep 12240503 = 18360755) B18360755
theorem B1910407 : Blo 1697549 1910407 := bstep (se 1 (by rfl) ⟨1432805, by rfl⟩ : syracuseStep 1910407 = 2865611) B2865611
theorem B6448841 : Blo 1697549 6448841 := bstep (se 2 (by rfl) ⟨2418315, by rfl⟩ : syracuseStep 6448841 = 4836631) B4836631
theorem B59647717 : Blo 1697549 59647717 := bstep (se 4 (by rfl) ⟨5591973, by rfl⟩ : syracuseStep 59647717 = 11183947) B11183947
theorem B2295559 : Blo 1697549 2295559 := bstep (se 1 (by rfl) ⟨1721669, by rfl⟩ : syracuseStep 2295559 = 3443339) B3443339
theorem B1697551 : Blo 1697549 1697551 := bstep (se 1 (by rfl) ⟨1273163, by rfl⟩ : syracuseStep 1697551 = 2546327) B2546327
theorem B8595233 : Blo 1697549 8595233 := bstep (se 2 (by rfl) ⟨3223212, by rfl⟩ : syracuseStep 8595233 = 6446425) B6446425
theorem B1697595 : Blo 1697549 1697595 := bstep (se 1 (by rfl) ⟨1273196, by rfl⟩ : syracuseStep 1697595 = 2546393) B2546393
theorem B1910587 : Blo 1697549 1910587 := bstep (se 1 (by rfl) ⟨1432940, by rfl⟩ : syracuseStep 1910587 = 2865881) B2865881
theorem B1697671 : Blo 1697549 1697671 := bstep (se 1 (by rfl) ⟨1273253, by rfl⟩ : syracuseStep 1697671 = 2546507) B2546507
theorem B4835207 : Blo 1697549 4835207 := bstep (se 1 (by rfl) ⟨3626405, by rfl⟩ : syracuseStep 4835207 = 7252811) B7252811
theorem B1697679 : Blo 1697549 1697679 := bstep (se 1 (by rfl) ⟨1273259, by rfl⟩ : syracuseStep 1697679 = 2546519) B2546519
theorem B4589465 : Blo 1697549 4589465 := bstep (se 2 (by rfl) ⟨1721049, by rfl⟩ : syracuseStep 4589465 = 3442099) B3442099
theorem B26150809 : Blo 1697549 26150809 := bstep (se 2 (by rfl) ⟨9806553, by rfl⟩ : syracuseStep 26150809 = 19613107) B19613107
theorem B4589497 : Blo 1697549 4589497 := bstep (se 2 (by rfl) ⟨1721061, by rfl⟩ : syracuseStep 4589497 = 3442123) B3442123
theorem B1697723 : Blo 1697549 1697723 := bstep (se 1 (by rfl) ⟨1273292, by rfl⟩ : syracuseStep 1697723 = 2546585) B2546585
theorem B2418617 : Blo 1697549 2418617 := bstep (se 2 (by rfl) ⟨906981, by rfl⟩ : syracuseStep 2418617 = 1813963) B1813963
theorem B1697799 : Blo 1697549 1697799 := bstep (se 1 (by rfl) ⟨1273349, by rfl⟩ : syracuseStep 1697799 = 2546699) B2546699
theorem B1697807 : Blo 1697549 1697807 := bstep (se 1 (by rfl) ⟨1273355, by rfl⟩ : syracuseStep 1697807 = 2546711) B2546711
theorem B13781015 : Blo 1697549 13781015 := bstep (se 1 (by rfl) ⟨10335761, by rfl⟩ : syracuseStep 13781015 = 20671523) B20671523
theorem B3819563 : Blo 1697549 3819563 := bstep (se 1 (by rfl) ⟨2864672, by rfl⟩ : syracuseStep 3819563 = 5729345) B5729345
theorem B1697851 : Blo 1697549 1697851 := bstep (se 1 (by rfl) ⟨1273388, by rfl⟩ : syracuseStep 1697851 = 2546777) B2546777
theorem B4835389 : Blo 1697549 4835389 := bstep (se 3 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 4835389 = 1813271) B1813271
theorem B4835447 : Blo 1697549 4835447 := bstep (se 1 (by rfl) ⟨3626585, by rfl⟩ : syracuseStep 4835447 = 7253171) B7253171
theorem B1697927 : Blo 1697549 1697927 := bstep (se 1 (by rfl) ⟨1273445, by rfl⟩ : syracuseStep 1697927 = 2546891) B2546891
theorem B1697935 : Blo 1697549 1697935 := bstep (se 1 (by rfl) ⟨1273451, by rfl⟩ : syracuseStep 1697935 = 2546903) B2546903
theorem B2582699 : Blo 1697549 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B1697979 : Blo 1697549 1697979 := bstep (se 1 (by rfl) ⟨1273484, by rfl⟩ : syracuseStep 1697979 = 2546969) B2546969
theorem B1698055 : Blo 1697549 1698055 := bstep (se 1 (by rfl) ⟨1273541, by rfl⟩ : syracuseStep 1698055 = 2547083) B2547083
theorem B1698063 : Blo 1697549 1698063 := bstep (se 1 (by rfl) ⟨1273547, by rfl⟩ : syracuseStep 1698063 = 2547095) B2547095
theorem B1911055 : Blo 1697549 1911055 := bstep (se 1 (by rfl) ⟨1433291, by rfl⟩ : syracuseStep 1911055 = 2866583) B2866583
theorem B1698107 : Blo 1697549 1698107 := bstep (se 1 (by rfl) ⟨1273580, by rfl⟩ : syracuseStep 1698107 = 2547161) B2547161
theorem B9808217 : Blo 1697549 9808217 := bstep (se 2 (by rfl) ⟨3678081, by rfl⟩ : syracuseStep 9808217 = 7356163) B7356163
theorem B1698183 : Blo 1697549 1698183 := bstep (se 1 (by rfl) ⟨1273637, by rfl⟩ : syracuseStep 1698183 = 2547275) B2547275
theorem B1698191 : Blo 1697549 1698191 := bstep (se 1 (by rfl) ⟨1273643, by rfl⟩ : syracuseStep 1698191 = 2547287) B2547287
theorem B14518673 : Blo 1697549 14518673 := bstep (se 2 (by rfl) ⟨5444502, by rfl⟩ : syracuseStep 14518673 = 10889005) B10889005
theorem B3819923 : Blo 1697549 3819923 := bstep (se 1 (by rfl) ⟨2864942, by rfl⟩ : syracuseStep 3819923 = 5729885) B5729885
theorem B17435027 : Blo 1697549 17435027 := bstep (se 1 (by rfl) ⟨13076270, by rfl⟩ : syracuseStep 17435027 = 26152541) B26152541
theorem B1698235 : Blo 1697549 1698235 := bstep (se 1 (by rfl) ⟨1273676, by rfl⟩ : syracuseStep 1698235 = 2547353) B2547353
theorem B3819977 : Blo 1697549 3819977 := bstep (se 2 (by rfl) ⟨1432491, by rfl⟩ : syracuseStep 3819977 = 2864983) B2864983
theorem B1698311 : Blo 1697549 1698311 := bstep (se 1 (by rfl) ⟨1273733, by rfl⟩ : syracuseStep 1698311 = 2547467) B2547467
theorem B1698319 : Blo 1697549 1698319 := bstep (se 1 (by rfl) ⟨1273739, by rfl⟩ : syracuseStep 1698319 = 2547479) B2547479
theorem B1698363 : Blo 1697549 1698363 := bstep (se 1 (by rfl) ⟨1273772, by rfl⟩ : syracuseStep 1698363 = 2547545) B2547545
theorem B1698439 : Blo 1697549 1698439 := bstep (se 1 (by rfl) ⟨1273829, by rfl⟩ : syracuseStep 1698439 = 2547659) B2547659
theorem B1698447 : Blo 1697549 1698447 := bstep (se 1 (by rfl) ⟨1273835, by rfl⟩ : syracuseStep 1698447 = 2547671) B2547671
theorem B1698491 : Blo 1697549 1698491 := bstep (se 1 (by rfl) ⟨1273868, by rfl⟩ : syracuseStep 1698491 = 2547737) B2547737
theorem B8596205 : Blo 1697549 8596205 := bstep (se 3 (by rfl) ⟨1611788, by rfl⟩ : syracuseStep 8596205 = 3223577) B3223577
theorem B1698567 : Blo 1697549 1698567 := bstep (se 1 (by rfl) ⟨1273925, by rfl⟩ : syracuseStep 1698567 = 2547851) B2547851
theorem B1911559 : Blo 1697549 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B69708559 : Blo 1697549 69708559 := bstep (se 1 (by rfl) ⟨52281419, by rfl⟩ : syracuseStep 69708559 = 104562839) B104562839
theorem B1698575 : Blo 1697549 1698575 := bstep (se 1 (by rfl) ⟨1273931, by rfl⟩ : syracuseStep 1698575 = 2547863) B2547863
theorem B16329509 : Blo 1697549 16329509 := bstep (se 4 (by rfl) ⟨1530891, by rfl⟩ : syracuseStep 16329509 = 3061783) B3061783
theorem B1698619 : Blo 1697549 1698619 := bstep (se 1 (by rfl) ⟨1273964, by rfl⟩ : syracuseStep 1698619 = 2547929) B2547929
theorem B9677657 : Blo 1697549 9677657 := bstep (se 2 (by rfl) ⟨3629121, by rfl⟩ : syracuseStep 9677657 = 7258243) B7258243
theorem B36735859 : Blo 1697549 36735859 := bstep (se 1 (by rfl) ⟨27551894, by rfl⟩ : syracuseStep 36735859 = 55103789) B55103789
theorem B1698695 : Blo 1697549 1698695 := bstep (se 1 (by rfl) ⟨1274021, by rfl⟩ : syracuseStep 1698695 = 2548043) B2548043
theorem B1698703 : Blo 1697549 1698703 := bstep (se 1 (by rfl) ⟨1274027, by rfl⟩ : syracuseStep 1698703 = 2548055) B2548055
theorem B1698747 : Blo 1697549 1698747 := bstep (se 1 (by rfl) ⟨1274060, by rfl⟩ : syracuseStep 1698747 = 2548121) B2548121
theorem B1911739 : Blo 1697549 1911739 := bstep (se 1 (by rfl) ⟨1433804, by rfl⟩ : syracuseStep 1911739 = 2867609) B2867609
theorem B8711171 : Blo 1697549 8711171 := bstep (se 1 (by rfl) ⟨6533378, by rfl⟩ : syracuseStep 8711171 = 13066757) B13066757
theorem B1698823 : Blo 1697549 1698823 := bstep (se 1 (by rfl) ⟨1274117, by rfl⟩ : syracuseStep 1698823 = 2548235) B2548235
theorem B5729291 : Blo 1697549 5729291 := bstep (se 1 (by rfl) ⟨4296968, by rfl⟩ : syracuseStep 5729291 = 8593937) B8593937
theorem B1813519 : Blo 1697549 1813519 := bstep (se 1 (by rfl) ⟨1360139, by rfl⟩ : syracuseStep 1813519 = 2720279) B2720279
theorem B1698831 : Blo 1697549 1698831 := bstep (se 1 (by rfl) ⟨1274123, by rfl⟩ : syracuseStep 1698831 = 2548247) B2548247
theorem B13773847 : Blo 1697549 13773847 := bstep (se 1 (by rfl) ⟨10330385, by rfl⟩ : syracuseStep 13773847 = 20660771) B20660771
theorem B1698875 : Blo 1697549 1698875 := bstep (se 1 (by rfl) ⟨1274156, by rfl⟩ : syracuseStep 1698875 = 2548313) B2548313
theorem B5729399 : Blo 1697549 5729399 := bstep (se 1 (by rfl) ⟨4297049, by rfl⟩ : syracuseStep 5729399 = 8594099) B8594099
theorem B6884471 : Blo 1697549 6884471 := bstep (se 1 (by rfl) ⟨5163353, by rfl⟩ : syracuseStep 6884471 = 10326707) B10326707
theorem B3820679 : Blo 1697549 3820679 := bstep (se 1 (by rfl) ⟨2865509, by rfl⟩ : syracuseStep 3820679 = 5731019) B5731019
theorem B1698951 : Blo 1697549 1698951 := bstep (se 1 (by rfl) ⟨1274213, by rfl⟩ : syracuseStep 1698951 = 2548427) B2548427
theorem B1698959 : Blo 1697549 1698959 := bstep (se 1 (by rfl) ⟨1274219, by rfl⟩ : syracuseStep 1698959 = 2548439) B2548439
theorem B4836505 : Blo 1697549 4836505 := bstep (se 2 (by rfl) ⟨1813689, by rfl⟩ : syracuseStep 4836505 = 3627379) B3627379
theorem B1699003 : Blo 1697549 1699003 := bstep (se 1 (by rfl) ⟨1274252, by rfl⟩ : syracuseStep 1699003 = 2548505) B2548505
theorem B1699079 : Blo 1697549 1699079 := bstep (se 1 (by rfl) ⟨1274309, by rfl⟩ : syracuseStep 1699079 = 2548619) B2548619
theorem B1699087 : Blo 1697549 1699087 := bstep (se 1 (by rfl) ⟨1274315, by rfl⟩ : syracuseStep 1699087 = 2548631) B2548631
theorem B9678113 : Blo 1697549 9678113 := bstep (se 2 (by rfl) ⟨3629292, by rfl⟩ : syracuseStep 9678113 = 7258585) B7258585
theorem B3820859 : Blo 1697549 3820859 := bstep (se 1 (by rfl) ⟨2865644, by rfl⟩ : syracuseStep 3820859 = 5731289) B5731289
theorem B1699131 : Blo 1697549 1699131 := bstep (se 1 (by rfl) ⟨1274348, by rfl⟩ : syracuseStep 1699131 = 2548697) B2548697
theorem B1699207 : Blo 1697549 1699207 := bstep (se 1 (by rfl) ⟨1274405, by rfl⟩ : syracuseStep 1699207 = 2548811) B2548811
theorem B1699215 : Blo 1697549 1699215 := bstep (se 1 (by rfl) ⟨1274411, by rfl⟩ : syracuseStep 1699215 = 2548823) B2548823
theorem B3820985 : Blo 1697549 3820985 := bstep (se 2 (by rfl) ⟨1432869, by rfl⟩ : syracuseStep 3820985 = 2865739) B2865739
theorem B6450617 : Blo 1697549 6450617 := bstep (se 2 (by rfl) ⟨2418981, by rfl⟩ : syracuseStep 6450617 = 4837963) B4837963
theorem B1699259 : Blo 1697549 1699259 := bstep (se 1 (by rfl) ⟨1274444, by rfl⟩ : syracuseStep 1699259 = 2548889) B2548889
theorem B3222985 : Blo 1697549 3222985 := bstep (se 2 (by rfl) ⟨1208619, by rfl⟩ : syracuseStep 3222985 = 2417239) B2417239
theorem B11628035 : Blo 1697549 11628035 := bstep (se 1 (by rfl) ⟨8721026, by rfl⟩ : syracuseStep 11628035 = 17442053) B17442053
theorem B1814023 : Blo 1697549 1814023 := bstep (se 1 (by rfl) ⟨1360517, by rfl⟩ : syracuseStep 1814023 = 2721035) B2721035
theorem B1699335 : Blo 1697549 1699335 := bstep (se 1 (by rfl) ⟨1274501, by rfl⟩ : syracuseStep 1699335 = 2549003) B2549003
theorem B1699343 : Blo 1697549 1699343 := bstep (se 1 (by rfl) ⟨1274507, by rfl⟩ : syracuseStep 1699343 = 2549015) B2549015
theorem B8597015 : Blo 1697549 8597015 := bstep (se 1 (by rfl) ⟨6447761, by rfl⟩ : syracuseStep 8597015 = 12895523) B12895523
theorem B9678365 : Blo 1697549 9678365 := bstep (se 3 (by rfl) ⟨1814693, by rfl⟩ : syracuseStep 9678365 = 3629387) B3629387
theorem B4591163 : Blo 1697549 4591163 := bstep (se 1 (by rfl) ⟨3443372, by rfl⟩ : syracuseStep 4591163 = 6886745) B6886745
theorem B1699387 : Blo 1697549 1699387 := bstep (se 1 (by rfl) ⟨1274540, by rfl⟩ : syracuseStep 1699387 = 2549081) B2549081
theorem B20942401 : Blo 1697549 20942401 := bstep (se 2 (by rfl) ⟨7853400, by rfl⟩ : syracuseStep 20942401 = 15706801) B15706801
theorem B5443159 : Blo 1697549 5443159 := bstep (se 1 (by rfl) ⟨4082369, by rfl⟩ : syracuseStep 5443159 = 8164739) B8164739
theorem B1699463 : Blo 1697549 1699463 := bstep (se 1 (by rfl) ⟨1274597, by rfl⟩ : syracuseStep 1699463 = 2549195) B2549195
theorem B1699471 : Blo 1697549 1699471 := bstep (se 1 (by rfl) ⟨1274603, by rfl⟩ : syracuseStep 1699471 = 2549207) B2549207
theorem B2150059 : Blo 1697549 2150059 := bstep (se 1 (by rfl) ⟨1612544, by rfl⟩ : syracuseStep 2150059 = 3225089) B3225089
theorem B1699515 : Blo 1697549 1699515 := bstep (se 1 (by rfl) ⟨1274636, by rfl⟩ : syracuseStep 1699515 = 2549273) B2549273
theorem B5729993 : Blo 1697549 5729993 := bstep (se 2 (by rfl) ⟨2148747, by rfl⟩ : syracuseStep 5729993 = 4297495) B4297495
theorem B6885121 : Blo 1697549 6885121 := bstep (se 2 (by rfl) ⟨2581920, by rfl⟩ : syracuseStep 6885121 = 5163841) B5163841
theorem B4837121 : Blo 1697549 4837121 := bstep (se 2 (by rfl) ⟨1813920, by rfl⟩ : syracuseStep 4837121 = 3627841) B3627841
theorem B3059471 : Blo 1697549 3059471 := bstep (se 1 (by rfl) ⟨2294603, by rfl⟩ : syracuseStep 3059471 = 4589207) B4589207
theorem B3821327 : Blo 1697549 3821327 := bstep (se 1 (by rfl) ⟨2865995, by rfl⟩ : syracuseStep 3821327 = 5731991) B5731991
theorem B16330511 : Blo 1697549 16330511 := bstep (se 1 (by rfl) ⟨12247883, by rfl⟩ : syracuseStep 16330511 = 24495767) B24495767
theorem B3821345 : Blo 1697549 3821345 := bstep (se 2 (by rfl) ⟨1433004, by rfl⟩ : syracuseStep 3821345 = 2866009) B2866009
theorem B8163217 : Blo 1697549 8163217 := bstep (se 2 (by rfl) ⟨3061206, by rfl⟩ : syracuseStep 8163217 = 6122413) B6122413
theorem B24473623 : Blo 1697549 24473623 := bstep (se 1 (by rfl) ⟨18355217, by rfl⟩ : syracuseStep 24473623 = 36710435) B36710435
theorem B3821687 : Blo 1697549 3821687 := bstep (se 1 (by rfl) ⟨2866265, by rfl⟩ : syracuseStep 3821687 = 5732531) B5732531
theorem B5165203 : Blo 1697549 5165203 := bstep (se 1 (by rfl) ⟨3873902, by rfl⟩ : syracuseStep 5165203 = 7747805) B7747805
theorem B19337453 : Blo 1697549 19337453 := bstep (se 3 (by rfl) ⟨3625772, by rfl⟩ : syracuseStep 19337453 = 7251545) B7251545
theorem B3445025 : Blo 1697549 3445025 := bstep (se 2 (by rfl) ⟨1291884, by rfl⟩ : syracuseStep 3445025 = 2583769) B2583769
theorem B3821867 : Blo 1697549 3821867 := bstep (se 1 (by rfl) ⟨2866400, by rfl⟩ : syracuseStep 3821867 = 5732801) B5732801
theorem B1814843 : Blo 1697549 1814843 := bstep (se 1 (by rfl) ⟨1361132, by rfl⟩ : syracuseStep 1814843 = 2722265) B2722265
theorem B5730695 : Blo 1697549 5730695 := bstep (se 1 (by rfl) ⟨4298021, by rfl⟩ : syracuseStep 5730695 = 8596043) B8596043
theorem B11334035 : Blo 1697549 11334035 := bstep (se 1 (by rfl) ⟨8500526, by rfl⟩ : syracuseStep 11334035 = 17001053) B17001053
theorem B3060371 : Blo 1697549 3060371 := bstep (se 1 (by rfl) ⟨2295278, by rfl⟩ : syracuseStep 3060371 = 4590557) B4590557
theorem B3822227 : Blo 1697549 3822227 := bstep (se 1 (by rfl) ⟨2866670, by rfl⟩ : syracuseStep 3822227 = 5733341) B5733341
theorem B3822281 : Blo 1697549 3822281 := bstep (se 2 (by rfl) ⟨1433355, by rfl⟩ : syracuseStep 3822281 = 2866711) B2866711
theorem B4838089 : Blo 1697549 4838089 := bstep (se 2 (by rfl) ⟨1814283, by rfl⟩ : syracuseStep 4838089 = 3628567) B3628567
theorem B5731073 : Blo 1697549 5731073 := bstep (se 2 (by rfl) ⟨2149152, by rfl⟩ : syracuseStep 5731073 = 4298305) B4298305
theorem B4297607 : Blo 1697549 4297607 := bstep (se 1 (by rfl) ⟨3223205, by rfl⟩ : syracuseStep 4297607 = 6446411) B6446411
theorem B4297657 : Blo 1697549 4297657 := bstep (se 2 (by rfl) ⟨1611621, by rfl⟩ : syracuseStep 4297657 = 3223243) B3223243
theorem B10335275 : Blo 1697549 10335275 := bstep (se 1 (by rfl) ⟨7751456, by rfl⟩ : syracuseStep 10335275 = 15502913) B15502913
theorem B6124663 : Blo 1697549 6124663 := bstep (se 1 (by rfl) ⟨4593497, by rfl⟩ : syracuseStep 6124663 = 9186995) B9186995
theorem B18363779 : Blo 1697549 18363779 := bstep (se 1 (by rfl) ⟨13772834, by rfl⟩ : syracuseStep 18363779 = 27545669) B27545669
theorem B3822983 : Blo 1697549 3822983 := bstep (se 1 (by rfl) ⟨2867237, by rfl⟩ : syracuseStep 3822983 = 5734475) B5734475
theorem B4904339 : Blo 1697549 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B107525555 : Blo 1697549 107525555 := bstep (se 1 (by rfl) ⟨80644166, by rfl⟩ : syracuseStep 107525555 = 161288333) B161288333
theorem B4298255 : Blo 1697549 4298255 := bstep (se 1 (by rfl) ⟨3223691, by rfl⟩ : syracuseStep 4298255 = 6447383) B6447383
theorem B5731883 : Blo 1697549 5731883 := bstep (se 1 (by rfl) ⟨4298912, by rfl⟩ : syracuseStep 5731883 = 8597825) B8597825
theorem B5518891 : Blo 1697549 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B3823163 : Blo 1697549 3823163 := bstep (se 1 (by rfl) ⟨2867372, by rfl⟩ : syracuseStep 3823163 = 5734745) B5734745
theorem B36738629 : Blo 1697549 36738629 := bstep (se 4 (by rfl) ⟨3444246, by rfl⟩ : syracuseStep 36738629 = 6888493) B6888493
theorem B3823289 : Blo 1697549 3823289 := bstep (se 2 (by rfl) ⟨1433733, by rfl⟩ : syracuseStep 3823289 = 2867467) B2867467
theorem B3225491 : Blo 1697549 3225491 := bstep (se 1 (by rfl) ⟨2419118, by rfl⟩ : syracuseStep 3225491 = 4838237) B4838237
theorem B3823631 : Blo 1697549 3823631 := bstep (se 1 (by rfl) ⟨2867723, by rfl⟩ : syracuseStep 3823631 = 5735447) B5735447
theorem B3823649 : Blo 1697549 3823649 := bstep (se 2 (by rfl) ⟨1433868, by rfl⟩ : syracuseStep 3823649 = 2867737) B2867737
theorem B24492077 : Blo 1697549 24492077 := bstep (se 3 (by rfl) ⟨4592264, by rfl⟩ : syracuseStep 24492077 = 9184529) B9184529
theorem B3225719 : Blo 1697549 3225719 := bstep (se 1 (by rfl) ⟨2419289, by rfl⟩ : syracuseStep 3225719 = 4838579) B4838579
theorem B2865287 : Blo 1697549 2865287 := bstep (se 1 (by rfl) ⟨2148965, by rfl⟩ : syracuseStep 2865287 = 4297931) B4297931
theorem B27908297 : Blo 1697549 27908297 := bstep (se 2 (by rfl) ⟨10465611, by rfl⟩ : syracuseStep 27908297 = 20931223) B20931223
theorem B4298953 : Blo 1697549 4298953 := bstep (se 2 (by rfl) ⟨1612107, by rfl⟩ : syracuseStep 4298953 = 3224215) B3224215
theorem B4839695 : Blo 1697549 4839695 := bstep (se 1 (by rfl) ⟨3629771, by rfl⟩ : syracuseStep 4839695 = 7259543) B7259543
theorem B3979579 : Blo 1697549 3979579 := bstep (se 1 (by rfl) ⟨2984684, by rfl⟩ : syracuseStep 3979579 = 5969369) B5969369
theorem B4299095 : Blo 1697549 4299095 := bstep (se 1 (by rfl) ⟨3224321, by rfl⟩ : syracuseStep 4299095 = 6448643) B6448643
theorem B4356499 : Blo 1697549 4356499 := bstep (se 1 (by rfl) ⟨3267374, by rfl⟩ : syracuseStep 4356499 = 6534749) B6534749
theorem B7256587 : Blo 1697549 7256587 := bstep (se 1 (by rfl) ⟨5442440, by rfl⟩ : syracuseStep 7256587 = 10884881) B10884881
theorem B8600093 : Blo 1697549 8600093 := bstep (se 3 (by rfl) ⟨1612517, by rfl⟩ : syracuseStep 8600093 = 3225035) B3225035
theorem B9673283 : Blo 1697549 9673283 := bstep (se 1 (by rfl) ⟨7254962, by rfl⟩ : syracuseStep 9673283 = 14509925) B14509925
theorem B2546363 : Blo 1697549 2546363 := bstep (se 1 (by rfl) ⟨1909772, by rfl⟩ : syracuseStep 2546363 = 3819545) B3819545
theorem B2546423 : Blo 1697549 2546423 := bstep (se 1 (by rfl) ⟨1909817, by rfl⟩ : syracuseStep 2546423 = 3819635) B3819635
theorem B2546447 : Blo 1697549 2546447 := bstep (se 1 (by rfl) ⟨1909835, by rfl⟩ : syracuseStep 2546447 = 3819671) B3819671
theorem B3267343 : Blo 1697549 3267343 := bstep (se 1 (by rfl) ⟨2450507, by rfl⟩ : syracuseStep 3267343 = 4901015) B4901015
theorem B2865935 : Blo 1697549 2865935 := bstep (se 1 (by rfl) ⟨2149451, by rfl⟩ : syracuseStep 2865935 = 4298903) B4298903
theorem B2546489 : Blo 1697549 2546489 := bstep (se 2 (by rfl) ⟨954933, by rfl⟩ : syracuseStep 2546489 = 1909867) B1909867
theorem B5733179 : Blo 1697549 5733179 := bstep (se 1 (by rfl) ⟨4299884, by rfl⟩ : syracuseStep 5733179 = 8599769) B8599769
theorem B6445939 : Blo 1697549 6445939 := bstep (se 1 (by rfl) ⟨4834454, by rfl⟩ : syracuseStep 6445939 = 9668909) B9668909
theorem B6290291 : Blo 1697549 6290291 := bstep (se 1 (by rfl) ⟨4717718, by rfl⟩ : syracuseStep 6290291 = 9435437) B9435437
theorem B2546567 : Blo 1697549 2546567 := bstep (se 1 (by rfl) ⟨1909925, by rfl⟩ : syracuseStep 2546567 = 3819851) B3819851
theorem B2546603 : Blo 1697549 2546603 := bstep (se 1 (by rfl) ⟨1909952, by rfl⟩ : syracuseStep 2546603 = 3819905) B3819905
theorem B2546633 : Blo 1697549 2546633 := bstep (se 2 (by rfl) ⟨954987, by rfl⟩ : syracuseStep 2546633 = 1909975) B1909975
theorem B8600579 : Blo 1697549 8600579 := bstep (se 1 (by rfl) ⟨6450434, by rfl⟩ : syracuseStep 8600579 = 12900869) B12900869
theorem B9673739 : Blo 1697549 9673739 := bstep (se 1 (by rfl) ⟨7255304, by rfl⟩ : syracuseStep 9673739 = 14510609) B14510609
theorem B2546747 : Blo 1697549 2546747 := bstep (se 1 (by rfl) ⟨1910060, by rfl⟩ : syracuseStep 2546747 = 3820121) B3820121
theorem B2546807 : Blo 1697549 2546807 := bstep (se 1 (by rfl) ⟨1910105, by rfl⟩ : syracuseStep 2546807 = 3820211) B3820211
theorem B2546831 : Blo 1697549 2546831 := bstep (se 1 (by rfl) ⟨1910123, by rfl⟩ : syracuseStep 2546831 = 3820247) B3820247
theorem B2546873 : Blo 1697549 2546873 := bstep (se 2 (by rfl) ⟨955077, by rfl⟩ : syracuseStep 2546873 = 1910155) B1910155
theorem B3873977 : Blo 1697549 3873977 := bstep (se 2 (by rfl) ⟨1452741, by rfl⟩ : syracuseStep 3873977 = 2905483) B2905483
theorem B2546951 : Blo 1697549 2546951 := bstep (se 1 (by rfl) ⟨1910213, by rfl⟩ : syracuseStep 2546951 = 3820427) B3820427
theorem B5733665 : Blo 1697549 5733665 := bstep (se 2 (by rfl) ⟨2150124, by rfl⟩ : syracuseStep 5733665 = 4300249) B4300249
theorem B2546987 : Blo 1697549 2546987 := bstep (se 1 (by rfl) ⟨1910240, by rfl⟩ : syracuseStep 2546987 = 3820481) B3820481
theorem B2866475 : Blo 1697549 2866475 := bstep (se 1 (by rfl) ⟨2149856, by rfl⟩ : syracuseStep 2866475 = 4299713) B4299713
theorem B2547017 : Blo 1697549 2547017 := bstep (se 2 (by rfl) ⟨955131, by rfl⟩ : syracuseStep 2547017 = 1910263) B1910263
theorem B36724103 : Blo 1697549 36724103 := bstep (se 1 (by rfl) ⟨27543077, by rfl⟩ : syracuseStep 36724103 = 55086155) B55086155
theorem B2547131 : Blo 1697549 2547131 := bstep (se 1 (by rfl) ⟨1910348, by rfl⟩ : syracuseStep 2547131 = 3820697) B3820697
theorem B12901841 : Blo 1697549 12901841 := bstep (se 2 (by rfl) ⟨4838190, by rfl⟩ : syracuseStep 12901841 = 9676381) B9676381
theorem B2547191 : Blo 1697549 2547191 := bstep (se 1 (by rfl) ⟨1910393, by rfl⟩ : syracuseStep 2547191 = 3820787) B3820787
theorem B2547215 : Blo 1697549 2547215 := bstep (se 1 (by rfl) ⟨1910411, by rfl⟩ : syracuseStep 2547215 = 3820823) B3820823
theorem B2547257 : Blo 1697549 2547257 := bstep (se 2 (by rfl) ⟨955221, by rfl⟩ : syracuseStep 2547257 = 1910443) B1910443
theorem B2039431 : Blo 1697549 2039431 := bstep (se 1 (by rfl) ⟨1529573, by rfl⟩ : syracuseStep 2039431 = 3059147) B3059147
theorem B2547335 : Blo 1697549 2547335 := bstep (se 1 (by rfl) ⟨1910501, by rfl⟩ : syracuseStep 2547335 = 3821003) B3821003
theorem B2547371 : Blo 1697549 2547371 := bstep (se 1 (by rfl) ⟨1910528, by rfl⟩ : syracuseStep 2547371 = 3821057) B3821057
theorem B2866873 : Blo 1697549 2866873 := bstep (se 2 (by rfl) ⟨1075077, by rfl⟩ : syracuseStep 2866873 = 2150155) B2150155
theorem B3628729 : Blo 1697549 3628729 := bstep (se 2 (by rfl) ⟨1360773, by rfl⟩ : syracuseStep 3628729 = 2721547) B2721547
theorem B8158913 : Blo 1697549 8158913 := bstep (se 2 (by rfl) ⟨3059592, by rfl⟩ : syracuseStep 8158913 = 6119185) B6119185
theorem B11034305 : Blo 1697549 11034305 := bstep (se 2 (by rfl) ⟨4137864, by rfl⟩ : syracuseStep 11034305 = 8275729) B8275729
theorem B2547401 : Blo 1697549 2547401 := bstep (se 2 (by rfl) ⟨955275, by rfl⟩ : syracuseStep 2547401 = 1910551) B1910551
theorem B45317933 : Blo 1697549 45317933 := bstep (se 3 (by rfl) ⟨8497112, by rfl⟩ : syracuseStep 45317933 = 16994225) B16994225
theorem B2547515 : Blo 1697549 2547515 := bstep (se 1 (by rfl) ⟨1910636, by rfl⟩ : syracuseStep 2547515 = 3821273) B3821273
theorem B5734259 : Blo 1697549 5734259 := bstep (se 1 (by rfl) ⟨4300694, by rfl⟩ : syracuseStep 5734259 = 8601389) B8601389
theorem B2547575 : Blo 1697549 2547575 := bstep (se 1 (by rfl) ⟨1910681, by rfl⟩ : syracuseStep 2547575 = 3821363) B3821363
theorem B2547599 : Blo 1697549 2547599 := bstep (se 1 (by rfl) ⟨1910699, by rfl⟩ : syracuseStep 2547599 = 3821399) B3821399
theorem B2547641 : Blo 1697549 2547641 := bstep (se 2 (by rfl) ⟨955365, by rfl⟩ : syracuseStep 2547641 = 1910731) B1910731
theorem B2547791 : Blo 1697549 2547791 := bstep (se 1 (by rfl) ⟨1910843, by rfl⟩ : syracuseStep 2547791 = 3821687) B3821687
theorem B6447185 : Blo 1697549 6447185 := bstep (se 2 (by rfl) ⟨2417694, by rfl⟩ : syracuseStep 6447185 = 4835389) B4835389
theorem B2547911 : Blo 1697549 2547911 := bstep (se 1 (by rfl) ⟨1910933, by rfl⟩ : syracuseStep 2547911 = 3821867) B3821867
theorem B2867447 : Blo 1697549 2867447 := bstep (se 1 (by rfl) ⟨2150585, by rfl⟩ : syracuseStep 2867447 = 4301171) B4301171
theorem B18358589 : Blo 1697549 18358589 := bstep (se 3 (by rfl) ⟨3442235, by rfl⟩ : syracuseStep 18358589 = 6884471) B6884471
theorem B12894551 : Blo 1697549 12894551 := bstep (se 1 (by rfl) ⟨9670913, by rfl⟩ : syracuseStep 12894551 = 19341827) B19341827
theorem B2548073 : Blo 1697549 2548073 := bstep (se 2 (by rfl) ⟨955527, by rfl⟩ : syracuseStep 2548073 = 1911055) B1911055
theorem B5734799 : Blo 1697549 5734799 := bstep (se 1 (by rfl) ⟨4301099, by rfl⟩ : syracuseStep 5734799 = 8602199) B8602199
theorem B2040247 : Blo 1697549 2040247 := bstep (se 1 (by rfl) ⟨1530185, by rfl⟩ : syracuseStep 2040247 = 3060371) B3060371
theorem B2548151 : Blo 1697549 2548151 := bstep (se 1 (by rfl) ⟨1911113, by rfl⟩ : syracuseStep 2548151 = 3822227) B3822227
theorem B2548187 : Blo 1697549 2548187 := bstep (se 1 (by rfl) ⟨1911140, by rfl⟩ : syracuseStep 2548187 = 3822281) B3822281
theorem B5808665 : Blo 1697549 5808665 := bstep (se 2 (by rfl) ⟨2178249, by rfl⟩ : syracuseStep 5808665 = 4356499) B4356499
theorem B14516759 : Blo 1697549 14516759 := bstep (se 1 (by rfl) ⟨10887569, by rfl⟩ : syracuseStep 14516759 = 21775139) B21775139
theorem B2867791 : Blo 1697549 2867791 := bstep (se 1 (by rfl) ⟨2150843, by rfl⟩ : syracuseStep 2867791 = 4301687) B4301687
theorem B9675449 : Blo 1697549 9675449 := bstep (se 2 (by rfl) ⟨3628293, by rfl⟩ : syracuseStep 9675449 = 7256587) B7256587
theorem B6890183 : Blo 1697549 6890183 := bstep (se 1 (by rfl) ⟨5167637, by rfl⟩ : syracuseStep 6890183 = 10335275) B10335275
theorem B5735123 : Blo 1697549 5735123 := bstep (se 1 (by rfl) ⟨4301342, by rfl⟩ : syracuseStep 5735123 = 8602685) B8602685
theorem B2720503 : Blo 1697549 2720503 := bstep (se 1 (by rfl) ⟨2040377, by rfl⟩ : syracuseStep 2720503 = 4080755) B4080755
theorem B2548655 : Blo 1697549 2548655 := bstep (se 1 (by rfl) ⟨1911491, by rfl⟩ : syracuseStep 2548655 = 3822983) B3822983
theorem B14156801 : Blo 1697549 14156801 := bstep (se 2 (by rfl) ⟨5308800, by rfl⟩ : syracuseStep 14156801 = 10617601) B10617601
theorem B2548745 : Blo 1697549 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B2548775 : Blo 1697549 2548775 := bstep (se 1 (by rfl) ⟨1911581, by rfl⟩ : syracuseStep 2548775 = 3823163) B3823163
theorem B8160335 : Blo 1697549 8160335 := bstep (se 1 (by rfl) ⟨6120251, by rfl⟩ : syracuseStep 8160335 = 12240503) B12240503
theorem B2548859 : Blo 1697549 2548859 := bstep (se 1 (by rfl) ⟨1911644, by rfl⟩ : syracuseStep 2548859 = 3823289) B3823289
theorem B8594585 : Blo 1697549 8594585 := bstep (se 2 (by rfl) ⟨3222969, by rfl⟩ : syracuseStep 8594585 = 6445939) B6445939
theorem B48981145 : Blo 1697549 48981145 := bstep (se 2 (by rfl) ⟨18367929, by rfl⟩ : syracuseStep 48981145 = 36735859) B36735859
theorem B318121157 : Blo 1697549 318121157 := bstep (se 4 (by rfl) ⟨29823858, by rfl⟩ : syracuseStep 318121157 = 59647717) B59647717
theorem B2548985 : Blo 1697549 2548985 := bstep (se 2 (by rfl) ⟨955869, by rfl⟩ : syracuseStep 2548985 = 1911739) B1911739
theorem B2549087 : Blo 1697549 2549087 := bstep (se 1 (by rfl) ⟨1911815, by rfl⟩ : syracuseStep 2549087 = 3823631) B3823631
theorem B2418025 : Blo 1697549 2418025 := bstep (se 2 (by rfl) ⟨906759, by rfl⟩ : syracuseStep 2418025 = 1813519) B1813519
theorem B2549099 : Blo 1697549 2549099 := bstep (se 1 (by rfl) ⟨1911824, by rfl⟩ : syracuseStep 2549099 = 3823649) B3823649
theorem B16328051 : Blo 1697549 16328051 := bstep (se 1 (by rfl) ⟨12246038, by rfl⟩ : syracuseStep 16328051 = 24492077) B24492077
theorem B17425829 : Blo 1697549 17425829 := bstep (se 4 (by rfl) ⟨1633671, by rfl⟩ : syracuseStep 17425829 = 3267343) B3267343
theorem B1910191 : Blo 1697549 1910191 := bstep (se 1 (by rfl) ⟨1432643, by rfl⟩ : syracuseStep 1910191 = 2865287) B2865287
theorem B18605531 : Blo 1697549 18605531 := bstep (se 1 (by rfl) ⟨13954148, by rfl⟩ : syracuseStep 18605531 = 27908297) B27908297
theorem B6448673 : Blo 1697549 6448673 := bstep (se 2 (by rfl) ⟨2418252, by rfl⟩ : syracuseStep 6448673 = 4836505) B4836505
theorem B6538811 : Blo 1697549 6538811 := bstep (se 1 (by rfl) ⟨4904108, by rfl⟩ : syracuseStep 6538811 = 9808217) B9808217
theorem B6448855 : Blo 1697549 6448855 := bstep (se 1 (by rfl) ⟨4836641, by rfl⟩ : syracuseStep 6448855 = 9673283) B9673283
theorem B1697575 : Blo 1697549 1697575 := bstep (se 1 (by rfl) ⟨1273181, by rfl⟩ : syracuseStep 1697575 = 2546363) B2546363
theorem B1697615 : Blo 1697549 1697615 := bstep (se 1 (by rfl) ⟨1273211, by rfl⟩ : syracuseStep 1697615 = 2546423) B2546423
theorem B1697631 : Blo 1697549 1697631 := bstep (se 1 (by rfl) ⟨1273223, by rfl⟩ : syracuseStep 1697631 = 2546447) B2546447
theorem B1910623 : Blo 1697549 1910623 := bstep (se 1 (by rfl) ⟨1432967, by rfl⟩ : syracuseStep 1910623 = 2865935) B2865935
theorem B16320365 : Blo 1697549 16320365 := bstep (se 3 (by rfl) ⟨3060068, by rfl⟩ : syracuseStep 16320365 = 6120137) B6120137
theorem B1697659 : Blo 1697549 1697659 := bstep (se 1 (by rfl) ⟨1273244, by rfl⟩ : syracuseStep 1697659 = 2546489) B2546489
theorem B1697711 : Blo 1697549 1697711 := bstep (se 1 (by rfl) ⟨1273283, by rfl⟩ : syracuseStep 1697711 = 2546567) B2546567
theorem B1697735 : Blo 1697549 1697735 := bstep (se 1 (by rfl) ⟨1273301, by rfl⟩ : syracuseStep 1697735 = 2546603) B2546603
theorem B1697755 : Blo 1697549 1697755 := bstep (se 1 (by rfl) ⟨1273316, by rfl⟩ : syracuseStep 1697755 = 2546633) B2546633
theorem B3819527 : Blo 1697549 3819527 := bstep (se 1 (by rfl) ⟨2864645, by rfl⟩ : syracuseStep 3819527 = 5729291) B5729291
theorem B6449159 : Blo 1697549 6449159 := bstep (se 1 (by rfl) ⟨4836869, by rfl⟩ : syracuseStep 6449159 = 9673739) B9673739
theorem B2418697 : Blo 1697549 2418697 := bstep (se 2 (by rfl) ⟨907011, by rfl⟩ : syracuseStep 2418697 = 1814023) B1814023
theorem B1697831 : Blo 1697549 1697831 := bstep (se 1 (by rfl) ⟨1273373, by rfl⟩ : syracuseStep 1697831 = 2546747) B2546747
theorem B7358521 : Blo 1697549 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B3819599 : Blo 1697549 3819599 := bstep (se 1 (by rfl) ⟨2864699, by rfl⟩ : syracuseStep 3819599 = 5729399) B5729399
theorem B1697871 : Blo 1697549 1697871 := bstep (se 1 (by rfl) ⟨1273403, by rfl⟩ : syracuseStep 1697871 = 2546807) B2546807
theorem B1697887 : Blo 1697549 1697887 := bstep (se 1 (by rfl) ⟨1273415, by rfl⟩ : syracuseStep 1697887 = 2546831) B2546831
theorem B1697915 : Blo 1697549 1697915 := bstep (se 1 (by rfl) ⟨1273436, by rfl⟩ : syracuseStep 1697915 = 2546873) B2546873
theorem B2582651 : Blo 1697549 2582651 := bstep (se 1 (by rfl) ⟨1936988, by rfl⟩ : syracuseStep 2582651 = 3873977) B3873977
theorem B1697967 : Blo 1697549 1697967 := bstep (se 1 (by rfl) ⟨1273475, by rfl⟩ : syracuseStep 1697967 = 2546951) B2546951
theorem B1697991 : Blo 1697549 1697991 := bstep (se 1 (by rfl) ⟨1273493, by rfl⟩ : syracuseStep 1697991 = 2546987) B2546987
theorem B1910983 : Blo 1697549 1910983 := bstep (se 1 (by rfl) ⟨1433237, by rfl⟩ : syracuseStep 1910983 = 2866475) B2866475
theorem B1698011 : Blo 1697549 1698011 := bstep (se 1 (by rfl) ⟨1273508, by rfl⟩ : syracuseStep 1698011 = 2547017) B2547017
theorem B1698087 : Blo 1697549 1698087 := bstep (se 1 (by rfl) ⟨1273565, by rfl⟩ : syracuseStep 1698087 = 2547131) B2547131
theorem B1698127 : Blo 1697549 1698127 := bstep (se 1 (by rfl) ⟨1273595, by rfl⟩ : syracuseStep 1698127 = 2547191) B2547191
theorem B7752023 : Blo 1697549 7752023 := bstep (se 1 (by rfl) ⟨5814017, by rfl⟩ : syracuseStep 7752023 = 11628035) B11628035
theorem B1698143 : Blo 1697549 1698143 := bstep (se 1 (by rfl) ⟨1273607, by rfl⟩ : syracuseStep 1698143 = 2547215) B2547215
theorem B1698171 : Blo 1697549 1698171 := bstep (se 1 (by rfl) ⟨1273628, by rfl⟩ : syracuseStep 1698171 = 2547257) B2547257
theorem B1698223 : Blo 1697549 1698223 := bstep (se 1 (by rfl) ⟨1273667, by rfl⟩ : syracuseStep 1698223 = 2547335) B2547335
theorem B1698247 : Blo 1697549 1698247 := bstep (se 1 (by rfl) ⟨1273685, by rfl⟩ : syracuseStep 1698247 = 2547371) B2547371
theorem B3819995 : Blo 1697549 3819995 := bstep (se 1 (by rfl) ⟨2864996, by rfl⟩ : syracuseStep 3819995 = 5729993) B5729993
theorem B1698267 : Blo 1697549 1698267 := bstep (se 1 (by rfl) ⟨1273700, by rfl⟩ : syracuseStep 1698267 = 2547401) B2547401
theorem B6449645 : Blo 1697549 6449645 := bstep (se 3 (by rfl) ⟨1209308, by rfl⟩ : syracuseStep 6449645 = 2418617) B2418617
theorem B34867745 : Blo 1697549 34867745 := bstep (se 2 (by rfl) ⟨13075404, by rfl⟩ : syracuseStep 34867745 = 26150809) B26150809
theorem B1698343 : Blo 1697549 1698343 := bstep (se 1 (by rfl) ⟨1273757, by rfl⟩ : syracuseStep 1698343 = 2547515) B2547515
theorem B1698383 : Blo 1697549 1698383 := bstep (se 1 (by rfl) ⟨1273787, by rfl⟩ : syracuseStep 1698383 = 2547575) B2547575
theorem B1698399 : Blo 1697549 1698399 := bstep (se 1 (by rfl) ⟨1273799, by rfl⟩ : syracuseStep 1698399 = 2547599) B2547599
theorem B1698427 : Blo 1697549 1698427 := bstep (se 1 (by rfl) ⟨1273820, by rfl⟩ : syracuseStep 1698427 = 2547641) B2547641
theorem B1698479 : Blo 1697549 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B1698503 : Blo 1697549 1698503 := bstep (se 1 (by rfl) ⟨1273877, by rfl⟩ : syracuseStep 1698503 = 2547755) B2547755
theorem B32631497 : Blo 1697549 32631497 := bstep (se 2 (by rfl) ⟨12236811, by rfl⟩ : syracuseStep 32631497 = 24473623) B24473623
theorem B1698523 : Blo 1697549 1698523 := bstep (se 1 (by rfl) ⟨1273892, by rfl⟩ : syracuseStep 1698523 = 2547785) B2547785
theorem B1698599 : Blo 1697549 1698599 := bstep (se 1 (by rfl) ⟨1273949, by rfl⟩ : syracuseStep 1698599 = 2547899) B2547899
theorem B1698639 : Blo 1697549 1698639 := bstep (se 1 (by rfl) ⟨1273979, by rfl⟩ : syracuseStep 1698639 = 2547959) B2547959
theorem B1698655 : Blo 1697549 1698655 := bstep (se 1 (by rfl) ⟨1273991, by rfl⟩ : syracuseStep 1698655 = 2547983) B2547983
theorem B1698683 : Blo 1697549 1698683 := bstep (se 1 (by rfl) ⟨1274012, by rfl⟩ : syracuseStep 1698683 = 2548025) B2548025
theorem B3820463 : Blo 1697549 3820463 := bstep (se 1 (by rfl) ⟨2865347, by rfl⟩ : syracuseStep 3820463 = 5730695) B5730695
theorem B1698735 : Blo 1697549 1698735 := bstep (se 1 (by rfl) ⟨1274051, by rfl⟩ : syracuseStep 1698735 = 2548103) B2548103
theorem B7556023 : Blo 1697549 7556023 := bstep (se 1 (by rfl) ⟨5667017, by rfl⟩ : syracuseStep 7556023 = 11334035) B11334035
theorem B1698759 : Blo 1697549 1698759 := bstep (se 1 (by rfl) ⟨1274069, by rfl⟩ : syracuseStep 1698759 = 2548139) B2548139
theorem B1698779 : Blo 1697549 1698779 := bstep (se 1 (by rfl) ⟨1274084, by rfl⟩ : syracuseStep 1698779 = 2548169) B2548169
theorem B1698855 : Blo 1697549 1698855 := bstep (se 1 (by rfl) ⟨1274141, by rfl⟩ : syracuseStep 1698855 = 2548283) B2548283
theorem B1911847 : Blo 1697549 1911847 := bstep (se 1 (by rfl) ⟨1433885, by rfl⟩ : syracuseStep 1911847 = 2867771) B2867771
theorem B1698895 : Blo 1697549 1698895 := bstep (se 1 (by rfl) ⟨1274171, by rfl⟩ : syracuseStep 1698895 = 2548343) B2548343
theorem B1698911 : Blo 1697549 1698911 := bstep (se 1 (by rfl) ⟨1274183, by rfl⟩ : syracuseStep 1698911 = 2548367) B2548367
theorem B1698939 : Blo 1697549 1698939 := bstep (se 1 (by rfl) ⟨1274204, by rfl⟩ : syracuseStep 1698939 = 2548409) B2548409
theorem B3820715 : Blo 1697549 3820715 := bstep (se 1 (by rfl) ⟨2865536, by rfl⟩ : syracuseStep 3820715 = 5731073) B5731073
theorem B1698991 : Blo 1697549 1698991 := bstep (se 1 (by rfl) ⟨1274243, by rfl⟩ : syracuseStep 1698991 = 2548487) B2548487
theorem B1699015 : Blo 1697549 1699015 := bstep (se 1 (by rfl) ⟨1274261, by rfl⟩ : syracuseStep 1699015 = 2548523) B2548523
theorem B1699035 : Blo 1697549 1699035 := bstep (se 1 (by rfl) ⟨1274276, by rfl⟩ : syracuseStep 1699035 = 2548553) B2548553
theorem B13774103 : Blo 1697549 13774103 := bstep (se 1 (by rfl) ⟨10330577, by rfl⟩ : syracuseStep 13774103 = 20661155) B20661155
theorem B1699111 : Blo 1697549 1699111 := bstep (se 1 (by rfl) ⟨1274333, by rfl⟩ : syracuseStep 1699111 = 2548667) B2548667
theorem B6884669 : Blo 1697549 6884669 := bstep (se 3 (by rfl) ⟨1290875, by rfl⟩ : syracuseStep 6884669 = 2581751) B2581751
theorem B1699151 : Blo 1697549 1699151 := bstep (se 1 (by rfl) ⟨1274363, by rfl⟩ : syracuseStep 1699151 = 2548727) B2548727
theorem B1699167 : Blo 1697549 1699167 := bstep (se 1 (by rfl) ⟨1274375, by rfl⟩ : syracuseStep 1699167 = 2548751) B2548751
theorem B1699195 : Blo 1697549 1699195 := bstep (se 1 (by rfl) ⟨1274396, by rfl⟩ : syracuseStep 1699195 = 2548793) B2548793
theorem B9186733 : Blo 1697549 9186733 := bstep (se 3 (by rfl) ⟨1722512, by rfl⟩ : syracuseStep 9186733 = 3445025) B3445025
theorem B1699247 : Blo 1697549 1699247 := bstep (se 1 (by rfl) ⟨1274435, by rfl⟩ : syracuseStep 1699247 = 2548871) B2548871
theorem B1699271 : Blo 1697549 1699271 := bstep (se 1 (by rfl) ⟨1274453, by rfl⟩ : syracuseStep 1699271 = 2548907) B2548907
theorem B2485723 : Blo 1697549 2485723 := bstep (se 1 (by rfl) ⟨1864292, by rfl⟩ : syracuseStep 2485723 = 3728585) B3728585
theorem B1699291 : Blo 1697549 1699291 := bstep (se 1 (by rfl) ⟨1274468, by rfl⟩ : syracuseStep 1699291 = 2548937) B2548937
theorem B5729831 : Blo 1697549 5729831 := bstep (se 1 (by rfl) ⟨4297373, by rfl⟩ : syracuseStep 5729831 = 8594747) B8594747
theorem B1699367 : Blo 1697549 1699367 := bstep (se 1 (by rfl) ⟨1274525, by rfl⟩ : syracuseStep 1699367 = 2549051) B2549051
theorem B1699407 : Blo 1697549 1699407 := bstep (se 1 (by rfl) ⟨1274555, by rfl⟩ : syracuseStep 1699407 = 2549111) B2549111
theorem B12242519 : Blo 1697549 12242519 := bstep (se 1 (by rfl) ⟨9181889, by rfl⟩ : syracuseStep 12242519 = 18363779) B18363779
theorem B1699423 : Blo 1697549 1699423 := bstep (se 1 (by rfl) ⟨1274567, by rfl⟩ : syracuseStep 1699423 = 2549135) B2549135
theorem B6450785 : Blo 1697549 6450785 := bstep (se 2 (by rfl) ⟨2419044, by rfl⟩ : syracuseStep 6450785 = 4838089) B4838089
theorem B71683703 : Blo 1697549 71683703 := bstep (se 1 (by rfl) ⟨53762777, by rfl⟩ : syracuseStep 71683703 = 107525555) B107525555
theorem B1699451 : Blo 1697549 1699451 := bstep (se 1 (by rfl) ⟨1274588, by rfl⟩ : syracuseStep 1699451 = 2549177) B2549177
theorem B5729939 : Blo 1697549 5729939 := bstep (se 1 (by rfl) ⟨4297454, by rfl⟩ : syracuseStep 5729939 = 8594909) B8594909
theorem B1699503 : Blo 1697549 1699503 := bstep (se 1 (by rfl) ⟨1274627, by rfl⟩ : syracuseStep 1699503 = 2549255) B2549255
theorem B3821255 : Blo 1697549 3821255 := bstep (se 1 (by rfl) ⟨2865941, by rfl⟩ : syracuseStep 3821255 = 5731883) B5731883
theorem B1699527 : Blo 1697549 1699527 := bstep (se 1 (by rfl) ⟨1274645, by rfl⟩ : syracuseStep 1699527 = 2549291) B2549291
theorem B1699547 : Blo 1697549 1699547 := bstep (se 1 (by rfl) ⟨1274660, by rfl⟩ : syracuseStep 1699547 = 2549321) B2549321
theorem B3223289 : Blo 1697549 3223289 := bstep (se 2 (by rfl) ⟨1208733, by rfl⟩ : syracuseStep 3223289 = 2417467) B2417467
theorem B5730155 : Blo 1697549 5730155 := bstep (se 1 (by rfl) ⟨4297616, by rfl⟩ : syracuseStep 5730155 = 8595233) B8595233
theorem B7253869 : Blo 1697549 7253869 := bstep (se 3 (by rfl) ⟨1360100, by rfl⟩ : syracuseStep 7253869 = 2720201) B2720201
theorem B5730209 : Blo 1697549 5730209 := bstep (se 2 (by rfl) ⟨2148828, by rfl⟩ : syracuseStep 5730209 = 4297657) B4297657
theorem B3223471 : Blo 1697549 3223471 := bstep (se 1 (by rfl) ⟨2417603, by rfl⟩ : syracuseStep 3223471 = 4835207) B4835207
theorem B2150327 : Blo 1697549 2150327 := bstep (se 1 (by rfl) ⟨1612745, by rfl⟩ : syracuseStep 2150327 = 3225491) B3225491
theorem B9187343 : Blo 1697549 9187343 := bstep (se 1 (by rfl) ⟨6890507, by rfl⟩ : syracuseStep 9187343 = 13781015) B13781015
theorem B12242981 : Blo 1697549 12242981 := bstep (se 4 (by rfl) ⟨1147779, by rfl⟩ : syracuseStep 12242981 = 2295559) B2295559
theorem B9809977 : Blo 1697549 9809977 := bstep (se 2 (by rfl) ⟨3678741, by rfl⟩ : syracuseStep 9809977 = 7357483) B7357483
theorem B3223631 : Blo 1697549 3223631 := bstep (se 1 (by rfl) ⟨2417723, by rfl⟩ : syracuseStep 3223631 = 4835447) B4835447
theorem B2150479 : Blo 1697549 2150479 := bstep (se 1 (by rfl) ⟨1612859, by rfl⟩ : syracuseStep 2150479 = 3225719) B3225719
theorem B9679115 : Blo 1697549 9679115 := bstep (se 1 (by rfl) ⟨7259336, by rfl⟩ : syracuseStep 9679115 = 14518673) B14518673
theorem B5730803 : Blo 1697549 5730803 := bstep (se 1 (by rfl) ⟨4298102, by rfl⟩ : syracuseStep 5730803 = 8596205) B8596205
theorem B3822119 : Blo 1697549 3822119 := bstep (se 1 (by rfl) ⟨2866589, by rfl⟩ : syracuseStep 3822119 = 5733179) B5733179
theorem B6451771 : Blo 1697549 6451771 := bstep (se 1 (by rfl) ⟨4838828, by rfl⟩ : syracuseStep 6451771 = 9677657) B9677657
theorem B4297313 : Blo 1697549 4297313 := bstep (se 2 (by rfl) ⟨1611492, by rfl⟩ : syracuseStep 4297313 = 3222985) B3222985
theorem B27923201 : Blo 1697549 27923201 := bstep (se 2 (by rfl) ⟨10471200, by rfl⟩ : syracuseStep 27923201 = 20942401) B20942401
theorem B3822443 : Blo 1697549 3822443 := bstep (se 1 (by rfl) ⟨2866832, by rfl⟩ : syracuseStep 3822443 = 5733665) B5733665
theorem B6452075 : Blo 1697549 6452075 := bstep (se 1 (by rfl) ⟨4839056, by rfl⟩ : syracuseStep 6452075 = 9678113) B9678113
theorem B3822497 : Blo 1697549 3822497 := bstep (se 2 (by rfl) ⟨1433436, by rfl⟩ : syracuseStep 3822497 = 2866873) B2866873
theorem B4838305 : Blo 1697549 4838305 := bstep (se 2 (by rfl) ⟨1814364, by rfl⟩ : syracuseStep 4838305 = 3628729) B3628729
theorem B24482735 : Blo 1697549 24482735 := bstep (se 1 (by rfl) ⟨18362051, by rfl⟩ : syracuseStep 24482735 = 36724103) B36724103
theorem B9180161 : Blo 1697549 9180161 := bstep (se 2 (by rfl) ⟨3442560, by rfl⟩ : syracuseStep 9180161 = 6885121) B6885121
theorem B5731343 : Blo 1697549 5731343 := bstep (se 1 (by rfl) ⟨4298507, by rfl⟩ : syracuseStep 5731343 = 8597015) B8597015
theorem B6452243 : Blo 1697549 6452243 := bstep (se 1 (by rfl) ⟨4839182, by rfl⟩ : syracuseStep 6452243 = 9678365) B9678365
theorem B3060775 : Blo 1697549 3060775 := bstep (se 1 (by rfl) ⟨2295581, by rfl⟩ : syracuseStep 3060775 = 4591163) B4591163
theorem B3224747 : Blo 1697549 3224747 := bstep (se 1 (by rfl) ⟨2418560, by rfl⟩ : syracuseStep 3224747 = 4837121) B4837121
theorem B10884289 : Blo 1697549 10884289 := bstep (se 2 (by rfl) ⟨4081608, by rfl⟩ : syracuseStep 10884289 = 8163217) B8163217
theorem B3822839 : Blo 1697549 3822839 := bstep (se 1 (by rfl) ⟨2867129, by rfl⟩ : syracuseStep 3822839 = 5734259) B5734259
theorem B12891635 : Blo 1697549 12891635 := bstep (se 1 (by rfl) ⟨9668726, by rfl⟩ : syracuseStep 12891635 = 19337453) B19337453
theorem B6886937 : Blo 1697549 6886937 := bstep (se 2 (by rfl) ⟨2582601, by rfl⟩ : syracuseStep 6886937 = 5165203) B5165203
theorem B5731937 : Blo 1697549 5731937 := bstep (se 2 (by rfl) ⟨2149476, by rfl⟩ : syracuseStep 5731937 = 4298953) B4298953
theorem B17667731 : Blo 1697549 17667731 := bstep (se 1 (by rfl) ⟨13250798, by rfl⟩ : syracuseStep 17667731 = 26501597) B26501597
theorem B8165063 : Blo 1697549 8165063 := bstep (se 1 (by rfl) ⟨6123797, by rfl⟩ : syracuseStep 8165063 = 12247595) B12247595
theorem B5306105 : Blo 1697549 5306105 := bstep (se 2 (by rfl) ⟨1989789, by rfl⟩ : syracuseStep 5306105 = 3979579) B3979579
theorem B6887197 : Blo 1697549 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B3823433 : Blo 1697549 3823433 := bstep (se 2 (by rfl) ⟨1433787, by rfl⟩ : syracuseStep 3823433 = 2867575) B2867575
theorem B2865071 : Blo 1697549 2865071 := bstep (se 1 (by rfl) ⟨2148803, by rfl⟩ : syracuseStep 2865071 = 4297607) B4297607
theorem B3626927 : Blo 1697549 3626927 := bstep (se 1 (by rfl) ⟨2720195, by rfl⟩ : syracuseStep 3626927 = 5440391) B5440391
theorem B4298771 : Blo 1697549 4298771 := bstep (se 1 (by rfl) ⟨3224078, by rfl⟩ : syracuseStep 4298771 = 6448157) B6448157
theorem B4839581 : Blo 1697549 4839581 := bstep (se 3 (by rfl) ⟨907421, by rfl⟩ : syracuseStep 4839581 = 1814843) B1814843
theorem B2865503 : Blo 1697549 2865503 := bstep (se 1 (by rfl) ⟨2149127, by rfl⟩ : syracuseStep 2865503 = 4298255) B4298255
theorem B92944745 : Blo 1697549 92944745 := bstep (se 2 (by rfl) ⟨34854279, by rfl⟩ : syracuseStep 92944745 = 69708559) B69708559
theorem B24492419 : Blo 1697549 24492419 := bstep (se 1 (by rfl) ⟨18369314, by rfl⟩ : syracuseStep 24492419 = 36738629) B36738629
theorem B4299227 : Blo 1697549 4299227 := bstep (se 1 (by rfl) ⟨3224420, by rfl⟩ : syracuseStep 4299227 = 6448841) B6448841
theorem B6445757 : Blo 1697549 6445757 := bstep (se 3 (by rfl) ⟨1208579, by rfl⟩ : syracuseStep 6445757 = 2417159) B2417159
theorem B2546375 : Blo 1697549 2546375 := bstep (se 1 (by rfl) ⟨1909781, by rfl⟩ : syracuseStep 2546375 = 3819563) B3819563
theorem B18365129 : Blo 1697549 18365129 := bstep (se 2 (by rfl) ⟨6886923, by rfl⟩ : syracuseStep 18365129 = 13773847) B13773847
theorem B7256861 : Blo 1697549 7256861 := bstep (se 3 (by rfl) ⟨1360661, by rfl⟩ : syracuseStep 7256861 = 2721323) B2721323
theorem B8166217 : Blo 1697549 8166217 := bstep (se 2 (by rfl) ⟨3062331, by rfl⟩ : syracuseStep 8166217 = 6124663) B6124663
theorem B3226463 : Blo 1697549 3226463 := bstep (se 1 (by rfl) ⟨2419847, by rfl⟩ : syracuseStep 3226463 = 4839695) B4839695
theorem B2546537 : Blo 1697549 2546537 := bstep (se 2 (by rfl) ⟨954951, by rfl⟩ : syracuseStep 2546537 = 1909903) B1909903
theorem B52312949 : Blo 1697549 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B2866063 : Blo 1697549 2866063 := bstep (se 1 (by rfl) ⟨2149547, by rfl⟩ : syracuseStep 2866063 = 4299095) B4299095
theorem B2546615 : Blo 1697549 2546615 := bstep (se 1 (by rfl) ⟨1909961, by rfl⟩ : syracuseStep 2546615 = 3819923) B3819923
theorem B11623351 : Blo 1697549 11623351 := bstep (se 1 (by rfl) ⟨8717513, by rfl⟩ : syracuseStep 11623351 = 17435027) B17435027
theorem B2546651 : Blo 1697549 2546651 := bstep (se 1 (by rfl) ⟨1909988, by rfl⟩ : syracuseStep 2546651 = 3819977) B3819977
theorem B5733395 : Blo 1697549 5733395 := bstep (se 1 (by rfl) ⟨4300046, by rfl⟩ : syracuseStep 5733395 = 8600093) B8600093
theorem B10886339 : Blo 1697549 10886339 := bstep (se 1 (by rfl) ⟨8164754, by rfl⟩ : syracuseStep 10886339 = 16329509) B16329509
theorem B4193527 : Blo 1697549 4193527 := bstep (se 1 (by rfl) ⟨3145145, by rfl⟩ : syracuseStep 4193527 = 6290291) B6290291
theorem B5807447 : Blo 1697549 5807447 := bstep (se 1 (by rfl) ⟨4355585, by rfl⟩ : syracuseStep 5807447 = 8711171) B8711171
theorem B5733719 : Blo 1697549 5733719 := bstep (se 1 (by rfl) ⟨4300289, by rfl⟩ : syracuseStep 5733719 = 8600579) B8600579
theorem B8158589 : Blo 1697549 8158589 := bstep (se 3 (by rfl) ⟨1529735, by rfl⟩ : syracuseStep 8158589 = 3059471) B3059471
theorem B2547119 : Blo 1697549 2547119 := bstep (se 1 (by rfl) ⟨1910339, by rfl⟩ : syracuseStep 2547119 = 3820679) B3820679
theorem B7257545 : Blo 1697549 7257545 := bstep (se 2 (by rfl) ⟨2721579, by rfl⟩ : syracuseStep 7257545 = 5443159) B5443159
theorem B2719241 : Blo 1697549 2719241 := bstep (se 2 (by rfl) ⟨1019715, by rfl⟩ : syracuseStep 2719241 = 2039431) B2039431
theorem B2547209 : Blo 1697549 2547209 := bstep (se 2 (by rfl) ⟨955203, by rfl⟩ : syracuseStep 2547209 = 1910407) B1910407
theorem B2547239 : Blo 1697549 2547239 := bstep (se 1 (by rfl) ⟨1910429, by rfl⟩ : syracuseStep 2547239 = 3820859) B3820859
theorem B2866745 : Blo 1697549 2866745 := bstep (se 2 (by rfl) ⟨1075029, by rfl⟩ : syracuseStep 2866745 = 2150059) B2150059
theorem B2547323 : Blo 1697549 2547323 := bstep (se 1 (by rfl) ⟨1910492, by rfl⟩ : syracuseStep 2547323 = 3820985) B3820985
theorem B4300411 : Blo 1697549 4300411 := bstep (se 1 (by rfl) ⟨3225308, by rfl⟩ : syracuseStep 4300411 = 6450617) B6450617
theorem B8601227 : Blo 1697549 8601227 := bstep (se 1 (by rfl) ⟨6450920, by rfl⟩ : syracuseStep 8601227 = 12901841) B12901841
theorem B12238573 : Blo 1697549 12238573 := bstep (se 3 (by rfl) ⟨2294732, by rfl⟩ : syracuseStep 12238573 = 4589465) B4589465
theorem B2547449 : Blo 1697549 2547449 := bstep (se 2 (by rfl) ⟨955293, by rfl⟩ : syracuseStep 2547449 = 1910587) B1910587
theorem B5439275 : Blo 1697549 5439275 := bstep (se 1 (by rfl) ⟨4079456, by rfl⟩ : syracuseStep 5439275 = 8158913) B8158913
theorem B7356203 : Blo 1697549 7356203 := bstep (se 1 (by rfl) ⟨5517152, by rfl⟩ : syracuseStep 7356203 = 11034305) B11034305
theorem B2547551 : Blo 1697549 2547551 := bstep (se 1 (by rfl) ⟨1910663, by rfl⟩ : syracuseStep 2547551 = 3821327) B3821327
theorem B10887007 : Blo 1697549 10887007 := bstep (se 1 (by rfl) ⟨8165255, by rfl⟩ : syracuseStep 10887007 = 16330511) B16330511
theorem B2547563 : Blo 1697549 2547563 := bstep (se 1 (by rfl) ⟨1910672, by rfl⟩ : syracuseStep 2547563 = 3821345) B3821345
theorem B30211955 : Blo 1697549 30211955 := bstep (se 1 (by rfl) ⟨22658966, by rfl⟩ : syracuseStep 30211955 = 45317933) B45317933
theorem B6119329 : Blo 1697549 6119329 := bstep (se 2 (by rfl) ⟨2294748, by rfl⟩ : syracuseStep 6119329 = 4589497) B4589497
theorem B2867305 : Blo 1697549 2867305 := bstep (se 2 (by rfl) ⟨1075239, by rfl⟩ : syracuseStep 2867305 = 2150479) B2150479
theorem B2547977 : Blo 1697549 2547977 := bstep (se 2 (by rfl) ⟨955491, by rfl⟩ : syracuseStep 2547977 = 1910983) B1910983
theorem B2548079 : Blo 1697549 2548079 := bstep (se 1 (by rfl) ⟨1911059, by rfl⟩ : syracuseStep 2548079 = 3822119) B3822119
theorem B2548295 : Blo 1697549 2548295 := bstep (se 1 (by rfl) ⟨1911221, by rfl⟩ : syracuseStep 2548295 = 3822443) B3822443
theorem B4301383 : Blo 1697549 4301383 := bstep (se 1 (by rfl) ⟨3226037, by rfl⟩ : syracuseStep 4301383 = 6452075) B6452075
theorem B2548331 : Blo 1697549 2548331 := bstep (se 1 (by rfl) ⟨1911248, by rfl⟩ : syracuseStep 2548331 = 3822497) B3822497
theorem B6120107 : Blo 1697549 6120107 := bstep (se 1 (by rfl) ⟨4590080, by rfl⟩ : syracuseStep 6120107 = 9180161) B9180161
theorem B9437867 : Blo 1697549 9437867 := bstep (se 1 (by rfl) ⟨7078400, by rfl⟩ : syracuseStep 9437867 = 14156801) B14156801
theorem B4301495 : Blo 1697549 4301495 := bstep (se 1 (by rfl) ⟨3226121, by rfl⟩ : syracuseStep 4301495 = 6452243) B6452243
theorem B5440223 : Blo 1697549 5440223 := bstep (se 1 (by rfl) ⟨4080167, by rfl⟩ : syracuseStep 5440223 = 8160335) B8160335
theorem B8602361 : Blo 1697549 8602361 := bstep (se 2 (by rfl) ⟨3225885, by rfl⟩ : syracuseStep 8602361 = 6451771) B6451771
theorem B48956237 : Blo 1697549 48956237 := bstep (se 3 (by rfl) ⟨9179294, by rfl⟩ : syracuseStep 48956237 = 18358589) B18358589
theorem B2548559 : Blo 1697549 2548559 := bstep (se 1 (by rfl) ⟨1911419, by rfl⟩ : syracuseStep 2548559 = 3822839) B3822839
theorem B11617219 : Blo 1697549 11617219 := bstep (se 1 (by rfl) ⟨8712914, by rfl⟩ : syracuseStep 11617219 = 17425829) B17425829
theorem B12403687 : Blo 1697549 12403687 := bstep (se 1 (by rfl) ⟨9302765, by rfl⟩ : syracuseStep 12403687 = 18605531) B18605531
theorem B8594423 : Blo 1697549 8594423 := bstep (se 1 (by rfl) ⟨6445817, by rfl⟩ : syracuseStep 8594423 = 12891635) B12891635
theorem B10888289 : Blo 1697549 10888289 := bstep (se 2 (by rfl) ⟨4083108, by rfl⟩ : syracuseStep 10888289 = 8166217) B8166217
theorem B2548955 : Blo 1697549 2548955 := bstep (se 1 (by rfl) ⟨1911716, by rfl⟩ : syracuseStep 2548955 = 3823433) B3823433
theorem B10880243 : Blo 1697549 10880243 := bstep (se 1 (by rfl) ⟨8160182, by rfl⟩ : syracuseStep 10880243 = 16320365) B16320365
theorem B1910047 : Blo 1697549 1910047 := bstep (se 1 (by rfl) ⟨1432535, by rfl⟩ : syracuseStep 1910047 = 2865071) B2865071
theorem B2417951 : Blo 1697549 2417951 := bstep (se 1 (by rfl) ⟨1813463, by rfl⟩ : syracuseStep 2417951 = 3626927) B3626927
theorem B4081033 : Blo 1697549 4081033 := bstep (se 2 (by rfl) ⟨1530387, by rfl⟩ : syracuseStep 4081033 = 3060775) B3060775
theorem B2549129 : Blo 1697549 2549129 := bstep (se 2 (by rfl) ⟨955923, by rfl⟩ : syracuseStep 2549129 = 1911847) B1911847
theorem B65308193 : Blo 1697549 65308193 := bstep (se 2 (by rfl) ⟨24490572, by rfl⟩ : syracuseStep 65308193 = 48981145) B48981145
theorem B1910335 : Blo 1697549 1910335 := bstep (se 1 (by rfl) ⟨1432751, by rfl⟩ : syracuseStep 1910335 = 2865503) B2865503
theorem B16328279 : Blo 1697549 16328279 := bstep (se 1 (by rfl) ⟨12246209, by rfl⟩ : syracuseStep 16328279 = 24492419) B24492419
theorem B47113949 : Blo 1697549 47113949 := bstep (se 3 (by rfl) ⟨8833865, by rfl⟩ : syracuseStep 47113949 = 17667731) B17667731
theorem B1697583 : Blo 1697549 1697583 := bstep (se 1 (by rfl) ⟨1273187, by rfl⟩ : syracuseStep 1697583 = 2546375) B2546375
theorem B12248977 : Blo 1697549 12248977 := bstep (se 2 (by rfl) ⟨4593366, by rfl⟩ : syracuseStep 12248977 = 9186733) B9186733
theorem B1697691 : Blo 1697549 1697691 := bstep (se 1 (by rfl) ⟨1273268, by rfl⟩ : syracuseStep 1697691 = 2546537) B2546537
theorem B34875299 : Blo 1697549 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B1697743 : Blo 1697549 1697743 := bstep (se 1 (by rfl) ⟨1273307, by rfl⟩ : syracuseStep 1697743 = 2546615) B2546615
theorem B1697767 : Blo 1697549 1697767 := bstep (se 1 (by rfl) ⟨1273325, by rfl⟩ : syracuseStep 1697767 = 2546651) B2546651
theorem B14149613 : Blo 1697549 14149613 := bstep (se 3 (by rfl) ⟨2653052, by rfl⟩ : syracuseStep 14149613 = 5306105) B5306105
theorem B4589779 : Blo 1697549 4589779 := bstep (se 1 (by rfl) ⟨3442334, by rfl⟩ : syracuseStep 4589779 = 6884669) B6884669
theorem B1698079 : Blo 1697549 1698079 := bstep (se 1 (by rfl) ⟨1273559, by rfl⟩ : syracuseStep 1698079 = 2547119) B2547119
theorem B10881317 : Blo 1697549 10881317 := bstep (se 4 (by rfl) ⟨1020123, by rfl⟩ : syracuseStep 10881317 = 2040247) B2040247
theorem B40298789 : Blo 1697549 40298789 := bstep (se 4 (by rfl) ⟨3778011, by rfl⟩ : syracuseStep 40298789 = 7556023) B7556023
theorem B1812827 : Blo 1697549 1812827 := bstep (se 1 (by rfl) ⟨1359620, by rfl⟩ : syracuseStep 1812827 = 2719241) B2719241
theorem B1698139 : Blo 1697549 1698139 := bstep (se 1 (by rfl) ⟨1273604, by rfl⟩ : syracuseStep 1698139 = 2547209) B2547209
theorem B3819887 : Blo 1697549 3819887 := bstep (se 1 (by rfl) ⟨2864915, by rfl⟩ : syracuseStep 3819887 = 5729831) B5729831
theorem B1698159 : Blo 1697549 1698159 := bstep (se 1 (by rfl) ⟨1273619, by rfl⟩ : syracuseStep 1698159 = 2547239) B2547239
theorem B1911163 : Blo 1697549 1911163 := bstep (se 1 (by rfl) ⟨1433372, by rfl⟩ : syracuseStep 1911163 = 2866745) B2866745
theorem B8161679 : Blo 1697549 8161679 := bstep (se 1 (by rfl) ⟨6121259, by rfl⟩ : syracuseStep 8161679 = 12242519) B12242519
theorem B1698215 : Blo 1697549 1698215 := bstep (se 1 (by rfl) ⟨1273661, by rfl⟩ : syracuseStep 1698215 = 2547323) B2547323
theorem B3819959 : Blo 1697549 3819959 := bstep (se 1 (by rfl) ⟨2864969, by rfl⟩ : syracuseStep 3819959 = 5729939) B5729939
theorem B2148859 : Blo 1697549 2148859 := bstep (se 1 (by rfl) ⟨1611644, by rfl⟩ : syracuseStep 2148859 = 3223289) B3223289
theorem B1698299 : Blo 1697549 1698299 := bstep (se 1 (by rfl) ⟨1273724, by rfl⟩ : syracuseStep 1698299 = 2547449) B2547449
theorem B1698367 : Blo 1697549 1698367 := bstep (se 1 (by rfl) ⟨1273775, by rfl⟩ : syracuseStep 1698367 = 2547551) B2547551
theorem B3820103 : Blo 1697549 3820103 := bstep (se 1 (by rfl) ⟨2865077, by rfl⟩ : syracuseStep 3820103 = 5730155) B5730155
theorem B1698375 : Blo 1697549 1698375 := bstep (se 1 (by rfl) ⟨1273781, by rfl⟩ : syracuseStep 1698375 = 2547563) B2547563
theorem B3820139 : Blo 1697549 3820139 := bstep (se 1 (by rfl) ⟨2865104, by rfl⟩ : syracuseStep 3820139 = 5730209) B5730209
theorem B8161987 : Blo 1697549 8161987 := bstep (se 1 (by rfl) ⟨6121490, by rfl⟩ : syracuseStep 8161987 = 12242981) B12242981
theorem B2149087 : Blo 1697549 2149087 := bstep (se 1 (by rfl) ⟨1611815, by rfl⟩ : syracuseStep 2149087 = 3223631) B3223631
theorem B1698527 : Blo 1697549 1698527 := bstep (se 1 (by rfl) ⟨1273895, by rfl⟩ : syracuseStep 1698527 = 2547791) B2547791
theorem B1698607 : Blo 1697549 1698607 := bstep (se 1 (by rfl) ⟨1273955, by rfl⟩ : syracuseStep 1698607 = 2547911) B2547911
theorem B1911631 : Blo 1697549 1911631 := bstep (se 1 (by rfl) ⟨1433723, by rfl⟩ : syracuseStep 1911631 = 2867447) B2867447
theorem B8596367 : Blo 1697549 8596367 := bstep (se 1 (by rfl) ⟨6447275, by rfl⟩ : syracuseStep 8596367 = 12894551) B12894551
theorem B1698715 : Blo 1697549 1698715 := bstep (se 1 (by rfl) ⟨1274036, by rfl⟩ : syracuseStep 1698715 = 2548073) B2548073
theorem B1698767 : Blo 1697549 1698767 := bstep (se 1 (by rfl) ⟨1274075, by rfl⟩ : syracuseStep 1698767 = 2548151) B2548151
theorem B1698791 : Blo 1697549 1698791 := bstep (se 1 (by rfl) ⟨1274093, by rfl⟩ : syracuseStep 1698791 = 2548187) B2548187
theorem B3820535 : Blo 1697549 3820535 := bstep (se 1 (by rfl) ⟨2865401, by rfl⟩ : syracuseStep 3820535 = 5730803) B5730803
theorem B9677839 : Blo 1697549 9677839 := bstep (se 1 (by rfl) ⟨7258379, by rfl⟩ : syracuseStep 9677839 = 14516759) B14516759
theorem B6450299 : Blo 1697549 6450299 := bstep (se 1 (by rfl) ⟨4837724, by rfl⟩ : syracuseStep 6450299 = 9675449) B9675449
theorem B18615467 : Blo 1697549 18615467 := bstep (se 1 (by rfl) ⟨13961600, by rfl⟩ : syracuseStep 18615467 = 27923201) B27923201
theorem B16321823 : Blo 1697549 16321823 := bstep (se 1 (by rfl) ⟨12241367, by rfl⟩ : syracuseStep 16321823 = 24482735) B24482735
theorem B1699103 : Blo 1697549 1699103 := bstep (se 1 (by rfl) ⟨1274327, by rfl⟩ : syracuseStep 1699103 = 2548655) B2548655
theorem B1699163 : Blo 1697549 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B3820895 : Blo 1697549 3820895 := bstep (se 1 (by rfl) ⟨2865671, by rfl⟩ : syracuseStep 3820895 = 5731343) B5731343
theorem B1699183 : Blo 1697549 1699183 := bstep (se 1 (by rfl) ⟨1274387, by rfl⟩ : syracuseStep 1699183 = 2548775) B2548775
theorem B1699239 : Blo 1697549 1699239 := bstep (se 1 (by rfl) ⟨1274429, by rfl⟩ : syracuseStep 1699239 = 2548859) B2548859
theorem B5729723 : Blo 1697549 5729723 := bstep (se 1 (by rfl) ⟨4297292, by rfl⟩ : syracuseStep 5729723 = 8594585) B8594585
theorem B2149831 : Blo 1697549 2149831 := bstep (se 1 (by rfl) ⟨1612373, by rfl⟩ : syracuseStep 2149831 = 3224747) B3224747
theorem B1699323 : Blo 1697549 1699323 := bstep (se 1 (by rfl) ⟨1274492, by rfl⟩ : syracuseStep 1699323 = 2548985) B2548985
theorem B1699391 : Blo 1697549 1699391 := bstep (se 1 (by rfl) ⟨1274543, by rfl⟩ : syracuseStep 1699391 = 2549087) B2549087
theorem B1699399 : Blo 1697549 1699399 := bstep (se 1 (by rfl) ⟨1274549, by rfl⟩ : syracuseStep 1699399 = 2549099) B2549099
theorem B4591291 : Blo 1697549 4591291 := bstep (se 1 (by rfl) ⟨3443468, by rfl⟩ : syracuseStep 4591291 = 6886937) B6886937
theorem B3821291 : Blo 1697549 3821291 := bstep (se 1 (by rfl) ⟨2865968, by rfl⟩ : syracuseStep 3821291 = 5731937) B5731937
theorem B5443375 : Blo 1697549 5443375 := bstep (se 1 (by rfl) ⟨4082531, by rfl⟩ : syracuseStep 5443375 = 8165063) B8165063
theorem B3821417 : Blo 1697549 3821417 := bstep (se 2 (by rfl) ⟨1433031, by rfl⟩ : syracuseStep 3821417 = 2866063) B2866063
theorem B6451073 : Blo 1697549 6451073 := bstep (se 2 (by rfl) ⟨2419152, by rfl⟩ : syracuseStep 6451073 = 4838305) B4838305
theorem B17436829 : Blo 1697549 17436829 := bstep (se 3 (by rfl) ⟨3269405, by rfl⟩ : syracuseStep 17436829 = 6538811) B6538811
theorem B14512385 : Blo 1697549 14512385 := bstep (se 2 (by rfl) ⟨5442144, by rfl⟩ : syracuseStep 14512385 = 10884289) B10884289
theorem B5591369 : Blo 1697549 5591369 := bstep (se 2 (by rfl) ⟨2096763, by rfl⟩ : syracuseStep 5591369 = 4193527) B4193527
theorem B23245163 : Blo 1697549 23245163 := bstep (se 1 (by rfl) ⟨17433872, by rfl⟩ : syracuseStep 23245163 = 34867745) B34867745
theorem B4297171 : Blo 1697549 4297171 := bstep (se 1 (by rfl) ⟨3222878, by rfl⟩ : syracuseStep 4297171 = 6445757) B6445757
theorem B21754331 : Blo 1697549 21754331 := bstep (se 1 (by rfl) ⟨16315748, by rfl⟩ : syracuseStep 21754331 = 32631497) B32631497
theorem B12243419 : Blo 1697549 12243419 := bstep (se 1 (by rfl) ⟨9182564, by rfl⟩ : syracuseStep 12243419 = 18365129) B18365129
theorem B3224033 : Blo 1697549 3224033 := bstep (se 2 (by rfl) ⟨1209012, by rfl⟩ : syracuseStep 3224033 = 2418025) B2418025
theorem B4837907 : Blo 1697549 4837907 := bstep (se 1 (by rfl) ⟨3628430, by rfl⟩ : syracuseStep 4837907 = 7256861) B7256861
theorem B2150975 : Blo 1697549 2150975 := bstep (se 1 (by rfl) ⟨1613231, by rfl⟩ : syracuseStep 2150975 = 3226463) B3226463
theorem B3314297 : Blo 1697549 3314297 := bstep (se 2 (by rfl) ⟨1242861, by rfl⟩ : syracuseStep 3314297 = 2485723) B2485723
theorem B3822263 : Blo 1697549 3822263 := bstep (se 1 (by rfl) ⟨2866697, by rfl⟩ : syracuseStep 3822263 = 5733395) B5733395
theorem B3871631 : Blo 1697549 3871631 := bstep (se 1 (by rfl) ⟨2903723, by rfl⟩ : syracuseStep 3871631 = 5807447) B5807447
theorem B3822479 : Blo 1697549 3822479 := bstep (se 1 (by rfl) ⟨2866859, by rfl⟩ : syracuseStep 3822479 = 5733719) B5733719
theorem B8598473 : Blo 1697549 8598473 := bstep (se 2 (by rfl) ⟨3224427, by rfl⟩ : syracuseStep 8598473 = 6448855) B6448855
theorem B4838363 : Blo 1697549 4838363 := bstep (se 1 (by rfl) ⟨3628772, by rfl⟩ : syracuseStep 4838363 = 7257545) B7257545
theorem B47789135 : Blo 1697549 47789135 := bstep (se 1 (by rfl) ⟨35841851, by rfl⟩ : syracuseStep 47789135 = 71683703) B71683703
theorem B9671825 : Blo 1697549 9671825 := bstep (se 2 (by rfl) ⟨3626934, by rfl⟩ : syracuseStep 9671825 = 7253869) B7253869
theorem B3626183 : Blo 1697549 3626183 := bstep (se 1 (by rfl) ⟨2719637, by rfl⟩ : syracuseStep 3626183 = 5439275) B5439275
theorem B4904135 : Blo 1697549 4904135 := bstep (se 1 (by rfl) ⟨3678101, by rfl⟩ : syracuseStep 4904135 = 7356203) B7356203
theorem B4297961 : Blo 1697549 4297961 := bstep (se 2 (by rfl) ⟨1611735, by rfl⟩ : syracuseStep 4297961 = 3223471) B3223471
theorem B20141303 : Blo 1697549 20141303 := bstep (se 1 (by rfl) ⟨15105977, by rfl⟩ : syracuseStep 20141303 = 30211955) B30211955
theorem B6124895 : Blo 1697549 6124895 := bstep (se 1 (by rfl) ⟨4593671, by rfl⟩ : syracuseStep 6124895 = 9187343) B9187343
theorem B3224929 : Blo 1697549 3224929 := bstep (se 2 (by rfl) ⟨1209348, by rfl⟩ : syracuseStep 3224929 = 2418697) B2418697
theorem B4298123 : Blo 1697549 4298123 := bstep (se 1 (by rfl) ⟨3223592, by rfl⟩ : syracuseStep 4298123 = 6447185) B6447185
theorem B13079969 : Blo 1697549 13079969 := bstep (se 2 (by rfl) ⟨4904988, by rfl⟩ : syracuseStep 13079969 = 9809977) B9809977
theorem B9811361 : Blo 1697549 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B6452743 : Blo 1697549 6452743 := bstep (se 1 (by rfl) ⟨4839557, by rfl⟩ : syracuseStep 6452743 = 9679115) B9679115
theorem B3823199 : Blo 1697549 3823199 := bstep (se 1 (by rfl) ⟨2867399, by rfl⟩ : syracuseStep 3823199 = 5734799) B5734799
theorem B6887069 : Blo 1697549 6887069 := bstep (se 3 (by rfl) ⟨1291325, by rfl⟩ : syracuseStep 6887069 = 2582651) B2582651
theorem B3872443 : Blo 1697549 3872443 := bstep (se 1 (by rfl) ⟨2904332, by rfl⟩ : syracuseStep 3872443 = 5808665) B5808665
theorem B2864875 : Blo 1697549 2864875 := bstep (se 1 (by rfl) ⟨2148656, by rfl⟩ : syracuseStep 2864875 = 4297313) B4297313
theorem B4593455 : Blo 1697549 4593455 := bstep (se 1 (by rfl) ⟨3445091, by rfl⟩ : syracuseStep 4593455 = 6890183) B6890183
theorem B3823415 : Blo 1697549 3823415 := bstep (se 1 (by rfl) ⟨2867561, by rfl⟩ : syracuseStep 3823415 = 5735123) B5735123
theorem B29030237 : Blo 1697549 29030237 := bstep (se 3 (by rfl) ⟨5443169, by rfl⟩ : syracuseStep 29030237 = 10886339) B10886339
theorem B3823721 : Blo 1697549 3823721 := bstep (se 2 (by rfl) ⟨1433895, by rfl⟩ : syracuseStep 3823721 = 2867791) B2867791
theorem B212080771 : Blo 1697549 212080771 := bstep (se 1 (by rfl) ⟨159060578, by rfl⟩ : syracuseStep 212080771 = 318121157) B318121157
theorem B10885367 : Blo 1697549 10885367 := bstep (se 1 (by rfl) ⟨8164025, by rfl⟩ : syracuseStep 10885367 = 16328051) B16328051
theorem B3627337 : Blo 1697549 3627337 := bstep (se 2 (by rfl) ⟨1360251, by rfl⟩ : syracuseStep 3627337 = 2720503) B2720503
theorem B4299115 : Blo 1697549 4299115 := bstep (se 1 (by rfl) ⟨3224336, by rfl⟩ : syracuseStep 4299115 = 6448673) B6448673
theorem B15497801 : Blo 1697549 15497801 := bstep (se 2 (by rfl) ⟨5811675, by rfl⟩ : syracuseStep 15497801 = 11623351) B11623351
theorem B2546351 : Blo 1697549 2546351 := bstep (se 1 (by rfl) ⟨1909763, by rfl⟩ : syracuseStep 2546351 = 3819527) B3819527
theorem B4299439 : Blo 1697549 4299439 := bstep (se 1 (by rfl) ⟨3224579, by rfl⟩ : syracuseStep 4299439 = 6449159) B6449159
theorem B2865847 : Blo 1697549 2865847 := bstep (se 1 (by rfl) ⟨2149385, by rfl⟩ : syracuseStep 2865847 = 4298771) B4298771
theorem B2546399 : Blo 1697549 2546399 := bstep (se 1 (by rfl) ⟨1909799, by rfl⟩ : syracuseStep 2546399 = 3819599) B3819599
theorem B3226387 : Blo 1697549 3226387 := bstep (se 1 (by rfl) ⟨2419790, by rfl⟩ : syracuseStep 3226387 = 4839581) B4839581
theorem B5168015 : Blo 1697549 5168015 := bstep (se 1 (by rfl) ⟨3876011, by rfl⟩ : syracuseStep 5168015 = 7752023) B7752023
theorem B61963163 : Blo 1697549 61963163 := bstep (se 1 (by rfl) ⟨46472372, by rfl⟩ : syracuseStep 61963163 = 92944745) B92944745
theorem B2546663 : Blo 1697549 2546663 := bstep (se 1 (by rfl) ⟨1909997, by rfl⟩ : syracuseStep 2546663 = 3819995) B3819995
theorem B2866151 : Blo 1697549 2866151 := bstep (se 1 (by rfl) ⟨2149613, by rfl⟩ : syracuseStep 2866151 = 4299227) B4299227
theorem B4299763 : Blo 1697549 4299763 := bstep (se 1 (by rfl) ⟨3224822, by rfl⟩ : syracuseStep 4299763 = 6449645) B6449645
theorem B2546921 : Blo 1697549 2546921 := bstep (se 2 (by rfl) ⟨955095, by rfl⟩ : syracuseStep 2546921 = 1910191) B1910191
theorem B2546975 : Blo 1697549 2546975 := bstep (se 1 (by rfl) ⟨1910231, by rfl⟩ : syracuseStep 2546975 = 3820463) B3820463
theorem B2547143 : Blo 1697549 2547143 := bstep (se 1 (by rfl) ⟨1910357, by rfl⟩ : syracuseStep 2547143 = 3820715) B3820715
theorem B5733881 : Blo 1697549 5733881 := bstep (se 2 (by rfl) ⟨2150205, by rfl⟩ : syracuseStep 5733881 = 4300411) B4300411
theorem B9182735 : Blo 1697549 9182735 := bstep (se 1 (by rfl) ⟨6887051, by rfl⟩ : syracuseStep 9182735 = 13774103) B13774103
theorem B5439059 : Blo 1697549 5439059 := bstep (se 1 (by rfl) ⟨4079294, by rfl⟩ : syracuseStep 5439059 = 8158589) B8158589
theorem B16318097 : Blo 1697549 16318097 := bstep (se 2 (by rfl) ⟨6119286, by rfl⟩ : syracuseStep 16318097 = 12238573) B12238573
theorem B9182929 : Blo 1697549 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B4300523 : Blo 1697549 4300523 := bstep (se 1 (by rfl) ⟨3225392, by rfl⟩ : syracuseStep 4300523 = 6450785) B6450785
theorem B5734151 : Blo 1697549 5734151 := bstep (se 1 (by rfl) ⟨4300613, by rfl⟩ : syracuseStep 5734151 = 8601227) B8601227
theorem B2547497 : Blo 1697549 2547497 := bstep (se 2 (by rfl) ⟨955311, by rfl⟩ : syracuseStep 2547497 = 1910623) B1910623
theorem B14516009 : Blo 1697549 14516009 := bstep (se 2 (by rfl) ⟨5443503, by rfl⟩ : syracuseStep 14516009 = 10887007) B10887007
theorem B2547503 : Blo 1697549 2547503 := bstep (se 1 (by rfl) ⟨1910627, by rfl⟩ : syracuseStep 2547503 = 3821255) B3821255
theorem B5734205 : Blo 1697549 5734205 := bstep (se 3 (by rfl) ⟨1075163, by rfl⟩ : syracuseStep 5734205 = 2150327) B2150327
theorem B8159105 : Blo 1697549 8159105 := bstep (se 2 (by rfl) ⟨3059664, by rfl⟩ : syracuseStep 8159105 = 6119329) B6119329
theorem B9674923 : Blo 1697549 9674923 := bstep (se 1 (by rfl) ⟨7256192, by rfl⟩ : syracuseStep 9674923 = 14512385) B14512385
theorem B23249105 : Blo 1697549 23249105 := bstep (se 2 (by rfl) ⟨8718414, by rfl⟩ : syracuseStep 23249105 = 17436829) B17436829
theorem B6119705 : Blo 1697549 6119705 := bstep (se 2 (by rfl) ⟨2294889, by rfl⟩ : syracuseStep 6119705 = 4589779) B4589779
theorem B4080071 : Blo 1697549 4080071 := bstep (se 1 (by rfl) ⟨3060053, by rfl⟩ : syracuseStep 4080071 = 6120107) B6120107
theorem B6291911 : Blo 1697549 6291911 := bstep (se 1 (by rfl) ⟨4718933, by rfl⟩ : syracuseStep 6291911 = 9437867) B9437867
theorem B2548175 : Blo 1697549 2548175 := bstep (se 1 (by rfl) ⟨1911131, by rfl⟩ : syracuseStep 2548175 = 3822263) B3822263
theorem B2867663 : Blo 1697549 2867663 := bstep (se 1 (by rfl) ⟨2150747, by rfl⟩ : syracuseStep 2867663 = 4301495) B4301495
theorem B2548217 : Blo 1697549 2548217 := bstep (se 2 (by rfl) ⟨955581, by rfl⟩ : syracuseStep 2548217 = 1911163) B1911163
theorem B5734907 : Blo 1697549 5734907 := bstep (se 1 (by rfl) ⟨4301180, by rfl⟩ : syracuseStep 5734907 = 8602361) B8602361
theorem B32637491 : Blo 1697549 32637491 := bstep (se 1 (by rfl) ⟨24478118, by rfl⟩ : syracuseStep 32637491 = 48956237) B48956237
theorem B2548319 : Blo 1697549 2548319 := bstep (se 1 (by rfl) ⟨1911239, by rfl⟩ : syracuseStep 2548319 = 3822479) B3822479
theorem B31859423 : Blo 1697549 31859423 := bstep (se 1 (by rfl) ⟨23894567, by rfl⟩ : syracuseStep 31859423 = 47789135) B47789135
theorem B7258859 : Blo 1697549 7258859 := bstep (se 1 (by rfl) ⟨5444144, by rfl⟩ : syracuseStep 7258859 = 10888289) B10888289
theorem B6447869 : Blo 1697549 6447869 := bstep (se 3 (by rfl) ⟨1208975, by rfl⟩ : syracuseStep 6447869 = 2417951) B2417951
theorem B5735177 : Blo 1697549 5735177 := bstep (se 2 (by rfl) ⟨2150691, by rfl⟩ : syracuseStep 5735177 = 4301383) B4301383
theorem B6447883 : Blo 1697549 6447883 := bstep (se 1 (by rfl) ⟨4835912, by rfl⟩ : syracuseStep 6447883 = 9671825) B9671825
theorem B2417455 : Blo 1697549 2417455 := bstep (se 1 (by rfl) ⟨1813091, by rfl⟩ : syracuseStep 2417455 = 3626183) B3626183
theorem B3269423 : Blo 1697549 3269423 := bstep (se 1 (by rfl) ⟨2452067, by rfl⟩ : syracuseStep 3269423 = 4904135) B4904135
theorem B14910317 : Blo 1697549 14910317 := bstep (se 3 (by rfl) ⟨2795684, by rfl⟩ : syracuseStep 14910317 = 5591369) B5591369
theorem B4834205 : Blo 1697549 4834205 := bstep (se 3 (by rfl) ⟨906413, by rfl⟩ : syracuseStep 4834205 = 1812827) B1812827
theorem B4301849 : Blo 1697549 4301849 := bstep (se 2 (by rfl) ⟨1613193, by rfl⟩ : syracuseStep 4301849 = 3226387) B3226387
theorem B2548799 : Blo 1697549 2548799 := bstep (se 1 (by rfl) ⟨1911599, by rfl⟩ : syracuseStep 2548799 = 3823199) B3823199
theorem B2548841 : Blo 1697549 2548841 := bstep (se 2 (by rfl) ⟨955815, by rfl⟩ : syracuseStep 2548841 = 1911631) B1911631
theorem B31409299 : Blo 1697549 31409299 := bstep (se 1 (by rfl) ⟨23556974, by rfl⟩ : syracuseStep 31409299 = 47113949) B47113949
theorem B2548943 : Blo 1697549 2548943 := bstep (se 1 (by rfl) ⟨1911707, by rfl⟩ : syracuseStep 2548943 = 3823415) B3823415
theorem B23250199 : Blo 1697549 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B12903785 : Blo 1697549 12903785 := bstep (se 2 (by rfl) ⟨4838919, by rfl⟩ : syracuseStep 12903785 = 9677839) B9677839
theorem B2549147 : Blo 1697549 2549147 := bstep (se 1 (by rfl) ⟨1911860, by rfl⟩ : syracuseStep 2549147 = 3823721) B3823721
theorem B5735933 : Blo 1697549 5735933 := bstep (se 3 (by rfl) ⟨1075487, by rfl⟩ : syracuseStep 5735933 = 2150975) B2150975
theorem B10331867 : Blo 1697549 10331867 := bstep (se 1 (by rfl) ⟨7748900, by rfl⟩ : syracuseStep 10331867 = 15497801) B15497801
theorem B1697567 : Blo 1697549 1697567 := bstep (se 1 (by rfl) ⟨1273175, by rfl⟩ : syracuseStep 1697567 = 2546351) B2546351
theorem B1697599 : Blo 1697549 1697599 := bstep (se 1 (by rfl) ⟨1273199, by rfl⟩ : syracuseStep 1697599 = 2546399) B2546399
theorem B5441377 : Blo 1697549 5441377 := bstep (se 2 (by rfl) ⟨2040516, by rfl⟩ : syracuseStep 5441377 = 4081033) B4081033
theorem B1697775 : Blo 1697549 1697775 := bstep (se 1 (by rfl) ⟨1273331, by rfl⟩ : syracuseStep 1697775 = 2546663) B2546663
theorem B1910767 : Blo 1697549 1910767 := bstep (se 1 (by rfl) ⟨1433075, by rfl⟩ : syracuseStep 1910767 = 2866151) B2866151
theorem B8603657 : Blo 1697549 8603657 := bstep (se 2 (by rfl) ⟨3226371, by rfl⟩ : syracuseStep 8603657 = 6452743) B6452743
theorem B1697947 : Blo 1697549 1697947 := bstep (se 1 (by rfl) ⟨1273460, by rfl⟩ : syracuseStep 1697947 = 2546921) B2546921
theorem B1697983 : Blo 1697549 1697983 := bstep (se 1 (by rfl) ⟨1273487, by rfl⟩ : syracuseStep 1697983 = 2546975) B2546975
theorem B10881215 : Blo 1697549 10881215 := bstep (se 1 (by rfl) ⟨8160911, by rfl⟩ : syracuseStep 10881215 = 16321823) B16321823
theorem B5163257 : Blo 1697549 5163257 := bstep (se 2 (by rfl) ⟨1936221, by rfl⟩ : syracuseStep 5163257 = 3872443) B3872443
theorem B6121721 : Blo 1697549 6121721 := bstep (se 2 (by rfl) ⟨2295645, by rfl⟩ : syracuseStep 6121721 = 4591291) B4591291
theorem B3819815 : Blo 1697549 3819815 := bstep (se 1 (by rfl) ⟨2864861, by rfl⟩ : syracuseStep 3819815 = 5729723) B5729723
theorem B1698095 : Blo 1697549 1698095 := bstep (se 1 (by rfl) ⟨1273571, by rfl⟩ : syracuseStep 1698095 = 2547143) B2547143
theorem B3819833 : Blo 1697549 3819833 := bstep (se 2 (by rfl) ⟨1432437, by rfl⟩ : syracuseStep 3819833 = 2864875) B2864875
theorem B6121823 : Blo 1697549 6121823 := bstep (se 1 (by rfl) ⟨4591367, by rfl⟩ : syracuseStep 6121823 = 9182735) B9182735
theorem B10324349 : Blo 1697549 10324349 := bstep (se 3 (by rfl) ⟨1935815, by rfl⟩ : syracuseStep 10324349 = 3871631) B3871631
theorem B1698331 : Blo 1697549 1698331 := bstep (se 1 (by rfl) ⟨1273748, by rfl⟩ : syracuseStep 1698331 = 2547497) B2547497
theorem B9677339 : Blo 1697549 9677339 := bstep (se 1 (by rfl) ⟨7258004, by rfl⟩ : syracuseStep 9677339 = 14516009) B14516009
theorem B1698335 : Blo 1697549 1698335 := bstep (se 1 (by rfl) ⟨1273751, by rfl⟩ : syracuseStep 1698335 = 2547503) B2547503
theorem B282774361 : Blo 1697549 282774361 := bstep (se 2 (by rfl) ⟨106040385, by rfl⟩ : syracuseStep 282774361 = 212080771) B212080771
theorem B1698651 : Blo 1697549 1698651 := bstep (se 1 (by rfl) ⟨1273988, by rfl⟩ : syracuseStep 1698651 = 2547977) B2547977
theorem B1698719 : Blo 1697549 1698719 := bstep (se 1 (by rfl) ⟨1274039, by rfl⟩ : syracuseStep 1698719 = 2548079) B2548079
theorem B14502887 : Blo 1697549 14502887 := bstep (se 1 (by rfl) ⟨10877165, by rfl⟩ : syracuseStep 14502887 = 21754331) B21754331
theorem B8162279 : Blo 1697549 8162279 := bstep (se 1 (by rfl) ⟨6121709, by rfl⟩ : syracuseStep 8162279 = 12243419) B12243419
theorem B2149355 : Blo 1697549 2149355 := bstep (se 1 (by rfl) ⟨1612016, by rfl⟩ : syracuseStep 2149355 = 3224033) B3224033
theorem B1698863 : Blo 1697549 1698863 := bstep (se 1 (by rfl) ⟨1274147, by rfl⟩ : syracuseStep 1698863 = 2548295) B2548295
theorem B1698887 : Blo 1697549 1698887 := bstep (se 1 (by rfl) ⟨1274165, by rfl⟩ : syracuseStep 1698887 = 2548331) B2548331
theorem B4836449 : Blo 1697549 4836449 := bstep (se 2 (by rfl) ⟨1813668, by rfl⟩ : syracuseStep 4836449 = 3627337) B3627337
theorem B1699039 : Blo 1697549 1699039 := bstep (se 1 (by rfl) ⟨1274279, by rfl⟩ : syracuseStep 1699039 = 2548559) B2548559
theorem B5729561 : Blo 1697549 5729561 := bstep (se 2 (by rfl) ⟨2148585, by rfl⟩ : syracuseStep 5729561 = 4297171) B4297171
theorem B53710141 : Blo 1697549 53710141 := bstep (se 3 (by rfl) ⟨10070651, by rfl⟩ : syracuseStep 53710141 = 20141303) B20141303
theorem B5729615 : Blo 1697549 5729615 := bstep (se 1 (by rfl) ⟨4297211, by rfl⟩ : syracuseStep 5729615 = 8594423) B8594423
theorem B1699303 : Blo 1697549 1699303 := bstep (se 1 (by rfl) ⟨1274477, by rfl⟩ : syracuseStep 1699303 = 2548955) B2548955
theorem B7253495 : Blo 1697549 7253495 := bstep (se 1 (by rfl) ⟨5440121, by rfl⟩ : syracuseStep 7253495 = 10880243) B10880243
theorem B4083263 : Blo 1697549 4083263 := bstep (se 1 (by rfl) ⟨3062447, by rfl⟩ : syracuseStep 4083263 = 6124895) B6124895
theorem B3821129 : Blo 1697549 3821129 := bstep (se 2 (by rfl) ⟨1432923, by rfl⟩ : syracuseStep 3821129 = 2865847) B2865847
theorem B10882649 : Blo 1697549 10882649 := bstep (se 2 (by rfl) ⟨4080993, by rfl⟩ : syracuseStep 10882649 = 8161987) B8161987
theorem B1699419 : Blo 1697549 1699419 := bstep (se 1 (by rfl) ⟨1274564, by rfl⟩ : syracuseStep 1699419 = 2549129) B2549129
theorem B8719979 : Blo 1697549 8719979 := bstep (se 1 (by rfl) ⟨6539984, by rfl⟩ : syracuseStep 8719979 = 13079969) B13079969
theorem B6540907 : Blo 1697549 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B4591379 : Blo 1697549 4591379 := bstep (se 1 (by rfl) ⟨3443534, by rfl⟩ : syracuseStep 4591379 = 6887069) B6887069
theorem B19353491 : Blo 1697549 19353491 := bstep (se 1 (by rfl) ⟨14515118, by rfl⟩ : syracuseStep 19353491 = 29030237) B29030237
theorem B9433075 : Blo 1697549 9433075 := bstep (se 1 (by rfl) ⟨7074806, by rfl⟩ : syracuseStep 9433075 = 14149613) B14149613
theorem B7254211 : Blo 1697549 7254211 := bstep (se 1 (by rfl) ⟨5440658, by rfl⟩ : syracuseStep 7254211 = 10881317) B10881317
theorem B26865859 : Blo 1697549 26865859 := bstep (se 1 (by rfl) ⟨20149394, by rfl⟩ : syracuseStep 26865859 = 40298789) B40298789
theorem B5730911 : Blo 1697549 5730911 := bstep (se 1 (by rfl) ⟨4298183, by rfl⟩ : syracuseStep 5730911 = 8596367) B8596367
theorem B3445343 : Blo 1697549 3445343 := bstep (se 1 (by rfl) ⟨2584007, by rfl⟩ : syracuseStep 3445343 = 5168015) B5168015
theorem B41308775 : Blo 1697549 41308775 := bstep (se 1 (by rfl) ⟨30981581, by rfl⟩ : syracuseStep 41308775 = 61963163) B61963163
theorem B12243905 : Blo 1697549 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B3822587 : Blo 1697549 3822587 := bstep (se 1 (by rfl) ⟨2866940, by rfl⟩ : syracuseStep 3822587 = 5733881) B5733881
theorem B3626039 : Blo 1697549 3626039 := bstep (se 1 (by rfl) ⟨2719529, by rfl⟩ : syracuseStep 3626039 = 5439059) B5439059
theorem B3822767 : Blo 1697549 3822767 := bstep (se 1 (by rfl) ⟨2867075, by rfl⟩ : syracuseStep 3822767 = 5734151) B5734151
theorem B16331969 : Blo 1697549 16331969 := bstep (se 2 (by rfl) ⟨6124488, by rfl⟩ : syracuseStep 16331969 = 12248977) B12248977
theorem B3822803 : Blo 1697549 3822803 := bstep (se 1 (by rfl) ⟨2867102, by rfl⟩ : syracuseStep 3822803 = 5734205) B5734205
theorem B3823073 : Blo 1697549 3823073 := bstep (se 2 (by rfl) ⟨1433652, by rfl⟩ : syracuseStep 3823073 = 2867305) B2867305
theorem B15496775 : Blo 1697549 15496775 := bstep (se 1 (by rfl) ⟨11622581, by rfl⟩ : syracuseStep 15496775 = 23245163) B23245163
theorem B3225271 : Blo 1697549 3225271 := bstep (se 1 (by rfl) ⟨2418953, by rfl⟩ : syracuseStep 3225271 = 4837907) B4837907
theorem B2209531 : Blo 1697549 2209531 := bstep (se 1 (by rfl) ⟨1657148, by rfl⟩ : syracuseStep 2209531 = 3314297) B3314297
theorem B49641245 : Blo 1697549 49641245 := bstep (se 3 (by rfl) ⟨9307733, by rfl⟩ : syracuseStep 49641245 = 18615467) B18615467
theorem B5732153 : Blo 1697549 5732153 := bstep (se 2 (by rfl) ⟨2149557, by rfl⟩ : syracuseStep 5732153 = 4299115) B4299115
theorem B5732315 : Blo 1697549 5732315 := bstep (se 1 (by rfl) ⟨4299236, by rfl⟩ : syracuseStep 5732315 = 8598473) B8598473
theorem B3225575 : Blo 1697549 3225575 := bstep (se 1 (by rfl) ⟨2419181, by rfl⟩ : syracuseStep 3225575 = 4838363) B4838363
theorem B2865145 : Blo 1697549 2865145 := bstep (se 2 (by rfl) ⟨1074429, by rfl⟩ : syracuseStep 2865145 = 2148859) B2148859
theorem B2865307 : Blo 1697549 2865307 := bstep (se 1 (by rfl) ⟨2148980, by rfl⟩ : syracuseStep 2865307 = 4297961) B4297961
theorem B5732585 : Blo 1697549 5732585 := bstep (se 2 (by rfl) ⟨2149719, by rfl⟩ : syracuseStep 5732585 = 4299439) B4299439
theorem B2865415 : Blo 1697549 2865415 := bstep (se 1 (by rfl) ⟨2149061, by rfl⟩ : syracuseStep 2865415 = 4298123) B4298123
theorem B2865449 : Blo 1697549 2865449 := bstep (se 2 (by rfl) ⟨1074543, by rfl⟩ : syracuseStep 2865449 = 2149087) B2149087
theorem B43538795 : Blo 1697549 43538795 := bstep (se 1 (by rfl) ⟨32654096, by rfl⟩ : syracuseStep 43538795 = 65308193) B65308193
theorem B21764477 : Blo 1697549 21764477 := bstep (se 3 (by rfl) ⟨4080839, by rfl⟩ : syracuseStep 21764477 = 8161679) B8161679
theorem B10885519 : Blo 1697549 10885519 := bstep (se 1 (by rfl) ⟨8164139, by rfl⟩ : syracuseStep 10885519 = 16328279) B16328279
theorem B3062303 : Blo 1697549 3062303 := bstep (se 1 (by rfl) ⟨2296727, by rfl⟩ : syracuseStep 3062303 = 4593455) B4593455
theorem B15489625 : Blo 1697549 15489625 := bstep (se 2 (by rfl) ⟨5808609, by rfl⟩ : syracuseStep 15489625 = 11617219) B11617219
theorem B16538249 : Blo 1697549 16538249 := bstep (se 2 (by rfl) ⟨6201843, by rfl⟩ : syracuseStep 16538249 = 12403687) B12403687
theorem B5733017 : Blo 1697549 5733017 := bstep (se 2 (by rfl) ⟨2149881, by rfl⟩ : syracuseStep 5733017 = 4299763) B4299763
theorem B7256911 : Blo 1697549 7256911 := bstep (se 1 (by rfl) ⟨5442683, by rfl⟩ : syracuseStep 7256911 = 10885367) B10885367
theorem B2546591 : Blo 1697549 2546591 := bstep (se 1 (by rfl) ⟨1909943, by rfl⟩ : syracuseStep 2546591 = 3819887) B3819887
theorem B2546639 : Blo 1697549 2546639 := bstep (se 1 (by rfl) ⟨1909979, by rfl⟩ : syracuseStep 2546639 = 3819959) B3819959
theorem B2546729 : Blo 1697549 2546729 := bstep (se 2 (by rfl) ⟨955023, by rfl⟩ : syracuseStep 2546729 = 1910047) B1910047
theorem B2546735 : Blo 1697549 2546735 := bstep (se 1 (by rfl) ⟨1910051, by rfl⟩ : syracuseStep 2546735 = 3820103) B3820103
theorem B2546759 : Blo 1697549 2546759 := bstep (se 1 (by rfl) ⟨1910069, by rfl⟩ : syracuseStep 2546759 = 3820139) B3820139
theorem B4299905 : Blo 1697549 4299905 := bstep (se 2 (by rfl) ⟨1612464, by rfl⟩ : syracuseStep 4299905 = 3224929) B3224929
theorem B14507261 : Blo 1697549 14507261 := bstep (se 3 (by rfl) ⟨2720111, by rfl⟩ : syracuseStep 14507261 = 5440223) B5440223
theorem B2866441 : Blo 1697549 2866441 := bstep (se 2 (by rfl) ⟨1074915, by rfl⟩ : syracuseStep 2866441 = 2149831) B2149831
theorem B2547023 : Blo 1697549 2547023 := bstep (se 1 (by rfl) ⟨1910267, by rfl⟩ : syracuseStep 2547023 = 3820535) B3820535
theorem B4300199 : Blo 1697549 4300199 := bstep (se 1 (by rfl) ⟨3225149, by rfl⟩ : syracuseStep 4300199 = 6450299) B6450299
theorem B2547113 : Blo 1697549 2547113 := bstep (se 2 (by rfl) ⟨955167, by rfl⟩ : syracuseStep 2547113 = 1910335) B1910335
theorem B2547263 : Blo 1697549 2547263 := bstep (se 1 (by rfl) ⟨1910447, by rfl⟩ : syracuseStep 2547263 = 3820895) B3820895
theorem B7257833 : Blo 1697549 7257833 := bstep (se 2 (by rfl) ⟨2721687, by rfl⟩ : syracuseStep 7257833 = 5443375) B5443375
theorem B10878731 : Blo 1697549 10878731 := bstep (se 1 (by rfl) ⟨8159048, by rfl⟩ : syracuseStep 10878731 = 16318097) B16318097
theorem B2547527 : Blo 1697549 2547527 := bstep (se 1 (by rfl) ⟨1910645, by rfl⟩ : syracuseStep 2547527 = 3821291) B3821291
theorem B2867015 : Blo 1697549 2867015 := bstep (se 1 (by rfl) ⟨2150261, by rfl⟩ : syracuseStep 2867015 = 4300523) B4300523
theorem B2547611 : Blo 1697549 2547611 := bstep (se 1 (by rfl) ⟨1910708, by rfl⟩ : syracuseStep 2547611 = 3821417) B3821417
theorem B5439403 : Blo 1697549 5439403 := bstep (se 1 (by rfl) ⟨4079552, by rfl⟩ : syracuseStep 5439403 = 8159105) B8159105
theorem B4300715 : Blo 1697549 4300715 := bstep (se 1 (by rfl) ⟨3225536, by rfl⟩ : syracuseStep 4300715 = 6451073) B6451073
theorem B15499403 : Blo 1697549 15499403 := bstep (se 1 (by rfl) ⟨11624552, by rfl⟩ : syracuseStep 15499403 = 23249105) B23249105
theorem B4079803 : Blo 1697549 4079803 := bstep (se 1 (by rfl) ⟨3059852, by rfl⟩ : syracuseStep 4079803 = 6119705) B6119705
theorem B4194607 : Blo 1697549 4194607 := bstep (se 1 (by rfl) ⟨3145955, by rfl⟩ : syracuseStep 4194607 = 6291911) B6291911
theorem B21758327 : Blo 1697549 21758327 := bstep (se 1 (by rfl) ⟨16318745, by rfl⟩ : syracuseStep 21758327 = 32637491) B32637491
theorem B2548391 : Blo 1697549 2548391 := bstep (se 1 (by rfl) ⟨1911293, by rfl⟩ : syracuseStep 2548391 = 3822587) B3822587
theorem B2867899 : Blo 1697549 2867899 := bstep (se 1 (by rfl) ⟨2150924, by rfl⟩ : syracuseStep 2867899 = 4301849) B4301849
theorem B2417359 : Blo 1697549 2417359 := bstep (se 1 (by rfl) ⟨1813019, by rfl⟩ : syracuseStep 2417359 = 3626039) B3626039
theorem B2548511 : Blo 1697549 2548511 := bstep (se 1 (by rfl) ⟨1911383, by rfl⟩ : syracuseStep 2548511 = 3822767) B3822767
theorem B20652833 : Blo 1697549 20652833 := bstep (se 2 (by rfl) ⟨7744812, by rfl⟩ : syracuseStep 20652833 = 15489625) B15489625
theorem B2548535 : Blo 1697549 2548535 := bstep (se 1 (by rfl) ⟨1911401, by rfl⟩ : syracuseStep 2548535 = 3822803) B3822803
theorem B8602523 : Blo 1697549 8602523 := bstep (se 1 (by rfl) ⟨6451892, by rfl⟩ : syracuseStep 8602523 = 12903785) B12903785
theorem B2548715 : Blo 1697549 2548715 := bstep (se 1 (by rfl) ⟨1911536, by rfl⟩ : syracuseStep 2548715 = 3823073) B3823073
theorem B10331183 : Blo 1697549 10331183 := bstep (se 1 (by rfl) ⟨7748387, by rfl⟩ : syracuseStep 10331183 = 15496775) B15496775
theorem B9675881 : Blo 1697549 9675881 := bstep (se 2 (by rfl) ⟨3628455, by rfl⟩ : syracuseStep 9675881 = 7256911) B7256911
theorem B10880189 : Blo 1697549 10880189 := bstep (se 3 (by rfl) ⟨2040035, by rfl⟩ : syracuseStep 10880189 = 4080071) B4080071
theorem B5735771 : Blo 1697549 5735771 := bstep (se 1 (by rfl) ⟨4301828, by rfl⟩ : syracuseStep 5735771 = 8603657) B8603657
theorem B3442171 : Blo 1697549 3442171 := bstep (se 1 (by rfl) ⟨2581628, by rfl⟩ : syracuseStep 3442171 = 5163257) B5163257
theorem B4081147 : Blo 1697549 4081147 := bstep (se 1 (by rfl) ⟨3060860, by rfl⟩ : syracuseStep 4081147 = 6121721) B6121721
theorem B41879065 : Blo 1697549 41879065 := bstep (se 2 (by rfl) ⟨15704649, by rfl⟩ : syracuseStep 41879065 = 31409299) B31409299
theorem B1910299 : Blo 1697549 1910299 := bstep (se 1 (by rfl) ⟨1432724, by rfl⟩ : syracuseStep 1910299 = 2865449) B2865449
theorem B29025863 : Blo 1697549 29025863 := bstep (se 1 (by rfl) ⟨21769397, by rfl⟩ : syracuseStep 29025863 = 43538795) B43538795
theorem B6882899 : Blo 1697549 6882899 := bstep (se 1 (by rfl) ⟨5162174, by rfl⟩ : syracuseStep 6882899 = 10324349) B10324349
theorem B14509651 : Blo 1697549 14509651 := bstep (se 1 (by rfl) ⟨10882238, by rfl⟩ : syracuseStep 14509651 = 21764477) B21764477
theorem B2041535 : Blo 1697549 2041535 := bstep (se 1 (by rfl) ⟨1531151, by rfl⟩ : syracuseStep 2041535 = 3062303) B3062303
theorem B31000265 : Blo 1697549 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B1697727 : Blo 1697549 1697727 := bstep (se 1 (by rfl) ⟨1273295, by rfl⟩ : syracuseStep 1697727 = 2546591) B2546591
theorem B1697759 : Blo 1697549 1697759 := bstep (se 1 (by rfl) ⟨1273319, by rfl⟩ : syracuseStep 1697759 = 2546639) B2546639
theorem B9668591 : Blo 1697549 9668591 := bstep (se 1 (by rfl) ⟨7251443, by rfl⟩ : syracuseStep 9668591 = 14502887) B14502887
theorem B5441519 : Blo 1697549 5441519 := bstep (se 1 (by rfl) ⟨4081139, by rfl⟩ : syracuseStep 5441519 = 8162279) B8162279
theorem B1697819 : Blo 1697549 1697819 := bstep (se 1 (by rfl) ⟨1273364, by rfl⟩ : syracuseStep 1697819 = 2546729) B2546729
theorem B1697823 : Blo 1697549 1697823 := bstep (se 1 (by rfl) ⟨1273367, by rfl⟩ : syracuseStep 1697823 = 2546735) B2546735
theorem B1697839 : Blo 1697549 1697839 := bstep (se 1 (by rfl) ⟨1273379, by rfl⟩ : syracuseStep 1697839 = 2546759) B2546759
theorem B8718461 : Blo 1697549 8718461 := bstep (se 3 (by rfl) ⟨1634711, by rfl⟩ : syracuseStep 8718461 = 3269423) B3269423
theorem B3819707 : Blo 1697549 3819707 := bstep (se 1 (by rfl) ⟨2864780, by rfl⟩ : syracuseStep 3819707 = 5729561) B5729561
theorem B3819743 : Blo 1697549 3819743 := bstep (se 1 (by rfl) ⟨2864807, by rfl⟩ : syracuseStep 3819743 = 5729615) B5729615
theorem B1698015 : Blo 1697549 1698015 := bstep (se 1 (by rfl) ⟨1273511, by rfl⟩ : syracuseStep 1698015 = 2547023) B2547023
theorem B1698075 : Blo 1697549 1698075 := bstep (se 1 (by rfl) ⟨1273556, by rfl⟩ : syracuseStep 1698075 = 2547113) B2547113
theorem B4835663 : Blo 1697549 4835663 := bstep (se 1 (by rfl) ⟨3626747, by rfl⟩ : syracuseStep 4835663 = 7253495) B7253495
theorem B1698175 : Blo 1697549 1698175 := bstep (se 1 (by rfl) ⟨1273631, by rfl⟩ : syracuseStep 1698175 = 2547263) B2547263
theorem B2722175 : Blo 1697549 2722175 := bstep (se 1 (by rfl) ⟨2041631, by rfl⟩ : syracuseStep 2722175 = 4083263) B4083263
theorem B7252487 : Blo 1697549 7252487 := bstep (se 1 (by rfl) ⟨5439365, by rfl⟩ : syracuseStep 7252487 = 10878731) B10878731
theorem B1698351 : Blo 1697549 1698351 := bstep (se 1 (by rfl) ⟨1273763, by rfl⟩ : syracuseStep 1698351 = 2547527) B2547527
theorem B1911343 : Blo 1697549 1911343 := bstep (se 1 (by rfl) ⟨1433507, by rfl⟩ : syracuseStep 1911343 = 2867015) B2867015
theorem B7252537 : Blo 1697549 7252537 := bstep (se 2 (by rfl) ⟨2719701, by rfl⟩ : syracuseStep 7252537 = 5439403) B5439403
theorem B1698407 : Blo 1697549 1698407 := bstep (se 1 (by rfl) ⟨1273805, by rfl⟩ : syracuseStep 1698407 = 2547611) B2547611
theorem B12577433 : Blo 1697549 12577433 := bstep (se 2 (by rfl) ⟨4716537, by rfl⟩ : syracuseStep 12577433 = 9433075) B9433075
theorem B3820193 : Blo 1697549 3820193 := bstep (se 2 (by rfl) ⟨1432572, by rfl⟩ : syracuseStep 3820193 = 2865145) B2865145
theorem B3820409 : Blo 1697549 3820409 := bstep (se 2 (by rfl) ⟨1432653, by rfl⟩ : syracuseStep 3820409 = 2865307) B2865307
theorem B1698783 : Blo 1697549 1698783 := bstep (se 1 (by rfl) ⟨1274087, by rfl⟩ : syracuseStep 1698783 = 2548175) B2548175
theorem B1911775 : Blo 1697549 1911775 := bstep (se 1 (by rfl) ⟨1433831, by rfl⟩ : syracuseStep 1911775 = 2867663) B2867663
theorem B1698811 : Blo 1697549 1698811 := bstep (se 1 (by rfl) ⟨1274108, by rfl⟩ : syracuseStep 1698811 = 2548217) B2548217
theorem B3820553 : Blo 1697549 3820553 := bstep (se 2 (by rfl) ⟨1432707, by rfl⟩ : syracuseStep 3820553 = 2865415) B2865415
theorem B3820607 : Blo 1697549 3820607 := bstep (se 1 (by rfl) ⟨2865455, by rfl⟩ : syracuseStep 3820607 = 5730911) B5730911
theorem B1698879 : Blo 1697549 1698879 := bstep (se 1 (by rfl) ⟨1274159, by rfl⟩ : syracuseStep 1698879 = 2548319) B2548319
theorem B2296895 : Blo 1697549 2296895 := bstep (se 1 (by rfl) ⟨1722671, by rfl⟩ : syracuseStep 2296895 = 3445343) B3445343
theorem B43551917 : Blo 1697549 43551917 := bstep (se 3 (by rfl) ⟨8165984, by rfl⟩ : syracuseStep 43551917 = 16331969) B16331969
theorem B9940211 : Blo 1697549 9940211 := bstep (se 1 (by rfl) ⟨7455158, by rfl⟩ : syracuseStep 9940211 = 14910317) B14910317
theorem B3222803 : Blo 1697549 3222803 := bstep (se 1 (by rfl) ⟨2417102, by rfl⟩ : syracuseStep 3222803 = 4834205) B4834205
theorem B8162603 : Blo 1697549 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B1699199 : Blo 1697549 1699199 := bstep (se 1 (by rfl) ⟨1274399, by rfl⟩ : syracuseStep 1699199 = 2548799) B2548799
theorem B1699227 : Blo 1697549 1699227 := bstep (se 1 (by rfl) ⟨1274420, by rfl⟩ : syracuseStep 1699227 = 2548841) B2548841
theorem B1699295 : Blo 1697549 1699295 := bstep (se 1 (by rfl) ⟨1274471, by rfl⟩ : syracuseStep 1699295 = 2548943) B2548943
theorem B1699431 : Blo 1697549 1699431 := bstep (se 1 (by rfl) ⟨1274573, by rfl⟩ : syracuseStep 1699431 = 2549147) B2549147
theorem B8597177 : Blo 1697549 8597177 := bstep (se 2 (by rfl) ⟨3223941, by rfl⟩ : syracuseStep 8597177 = 6447883) B6447883
theorem B377032481 : Blo 1697549 377032481 := bstep (se 2 (by rfl) ⟨141387180, by rfl⟩ : syracuseStep 377032481 = 282774361) B282774361
theorem B3821435 : Blo 1697549 3821435 := bstep (se 1 (by rfl) ⟨2866076, by rfl⟩ : syracuseStep 3821435 = 5732153) B5732153
theorem B3821543 : Blo 1697549 3821543 := bstep (se 1 (by rfl) ⟨2866157, by rfl⟩ : syracuseStep 3821543 = 5732315) B5732315
theorem B2150383 : Blo 1697549 2150383 := bstep (se 1 (by rfl) ⟨1612787, by rfl⟩ : syracuseStep 2150383 = 3225575) B3225575
theorem B7254143 : Blo 1697549 7254143 := bstep (se 1 (by rfl) ⟨5440607, by rfl⟩ : syracuseStep 7254143 = 10881215) B10881215
theorem B3821723 : Blo 1697549 3821723 := bstep (se 1 (by rfl) ⟨2866292, by rfl⟩ : syracuseStep 3821723 = 5732585) B5732585
theorem B23253277 : Blo 1697549 23253277 := bstep (se 3 (by rfl) ⟨4359989, by rfl⟩ : syracuseStep 23253277 = 8719979) B8719979
theorem B3821921 : Blo 1697549 3821921 := bstep (se 2 (by rfl) ⟨1433220, by rfl⟩ : syracuseStep 3821921 = 2866441) B2866441
theorem B6451559 : Blo 1697549 6451559 := bstep (se 1 (by rfl) ⟨4838669, by rfl⟩ : syracuseStep 6451559 = 9677339) B9677339
theorem B3822011 : Blo 1697549 3822011 := bstep (se 1 (by rfl) ⟨2866508, by rfl⟩ : syracuseStep 3822011 = 5733017) B5733017
theorem B3224299 : Blo 1697549 3224299 := bstep (se 1 (by rfl) ⟨2418224, by rfl⟩ : syracuseStep 3224299 = 4836449) B4836449
theorem B8721209 : Blo 1697549 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B9671507 : Blo 1697549 9671507 := bstep (se 1 (by rfl) ⟨7253630, by rfl⟩ : syracuseStep 9671507 = 14507261) B14507261
theorem B2946041 : Blo 1697549 2946041 := bstep (se 2 (by rfl) ⟨1104765, by rfl⟩ : syracuseStep 2946041 = 2209531) B2209531
theorem B7255099 : Blo 1697549 7255099 := bstep (se 1 (by rfl) ⟨5441324, by rfl⟩ : syracuseStep 7255099 = 10882649) B10882649
theorem B7255169 : Blo 1697549 7255169 := bstep (se 2 (by rfl) ⟨2720688, by rfl⟩ : syracuseStep 7255169 = 5441377) B5441377
theorem B4838555 : Blo 1697549 4838555 := bstep (se 1 (by rfl) ⟨3628916, by rfl⟩ : syracuseStep 4838555 = 7257833) B7257833
theorem B3060919 : Blo 1697549 3060919 := bstep (se 1 (by rfl) ⟨2295689, by rfl⟩ : syracuseStep 3060919 = 4591379) B4591379
theorem B5731613 : Blo 1697549 5731613 := bstep (se 3 (by rfl) ⟨1074677, by rfl⟩ : syracuseStep 5731613 = 2149355) B2149355
theorem B12899897 : Blo 1697549 12899897 := bstep (se 2 (by rfl) ⟨4837461, by rfl⟩ : syracuseStep 12899897 = 9674923) B9674923
theorem B9672281 : Blo 1697549 9672281 := bstep (se 2 (by rfl) ⟨3627105, by rfl⟩ : syracuseStep 9672281 = 7254211) B7254211
theorem B35821145 : Blo 1697549 35821145 := bstep (se 2 (by rfl) ⟨13432929, by rfl⟩ : syracuseStep 35821145 = 26865859) B26865859
theorem B3823271 : Blo 1697549 3823271 := bstep (se 1 (by rfl) ⟨2867453, by rfl⟩ : syracuseStep 3823271 = 5734907) B5734907
theorem B27539183 : Blo 1697549 27539183 := bstep (se 1 (by rfl) ⟨20654387, by rfl⟩ : syracuseStep 27539183 = 41308775) B41308775
theorem B21239615 : Blo 1697549 21239615 := bstep (se 1 (by rfl) ⟨15929711, by rfl⟩ : syracuseStep 21239615 = 31859423) B31859423
theorem B4839239 : Blo 1697549 4839239 := bstep (se 1 (by rfl) ⟨3629429, by rfl⟩ : syracuseStep 4839239 = 7258859) B7258859
theorem B4298579 : Blo 1697549 4298579 := bstep (se 1 (by rfl) ⟨3223934, by rfl⟩ : syracuseStep 4298579 = 6447869) B6447869
theorem B3823451 : Blo 1697549 3823451 := bstep (se 1 (by rfl) ⟨2867588, by rfl⟩ : syracuseStep 3823451 = 5735177) B5735177
theorem B14514025 : Blo 1697549 14514025 := bstep (se 2 (by rfl) ⟨5442759, by rfl⟩ : syracuseStep 14514025 = 10885519) B10885519
theorem B16324861 : Blo 1697549 16324861 := bstep (se 3 (by rfl) ⟨3060911, by rfl⟩ : syracuseStep 16324861 = 6121823) B6121823
theorem B3823955 : Blo 1697549 3823955 := bstep (se 1 (by rfl) ⟨2867966, by rfl⟩ : syracuseStep 3823955 = 5735933) B5735933
theorem B6887911 : Blo 1697549 6887911 := bstep (se 1 (by rfl) ⟨5165933, by rfl⟩ : syracuseStep 6887911 = 10331867) B10331867
theorem B33094163 : Blo 1697549 33094163 := bstep (se 1 (by rfl) ⟨24820622, by rfl⟩ : syracuseStep 33094163 = 49641245) B49641245
theorem B2546543 : Blo 1697549 2546543 := bstep (se 1 (by rfl) ⟨1909907, by rfl⟩ : syracuseStep 2546543 = 3819815) B3819815
theorem B2546555 : Blo 1697549 2546555 := bstep (se 1 (by rfl) ⟨1909916, by rfl⟩ : syracuseStep 2546555 = 3819833) B3819833
theorem B12893093 : Blo 1697549 12893093 := bstep (se 4 (by rfl) ⟨1208727, by rfl⟩ : syracuseStep 12893093 = 2417455) B2417455
theorem B71613521 : Blo 1697549 71613521 := bstep (se 2 (by rfl) ⟨26855070, by rfl⟩ : syracuseStep 71613521 = 53710141) B53710141
theorem B11025499 : Blo 1697549 11025499 := bstep (se 1 (by rfl) ⟨8269124, by rfl⟩ : syracuseStep 11025499 = 16538249) B16538249
theorem B2866603 : Blo 1697549 2866603 := bstep (se 1 (by rfl) ⟨2149952, by rfl⟩ : syracuseStep 2866603 = 4299905) B4299905
theorem B4300361 : Blo 1697549 4300361 := bstep (se 2 (by rfl) ⟨1612635, by rfl⟩ : syracuseStep 4300361 = 3225271) B3225271
theorem B2866799 : Blo 1697549 2866799 := bstep (se 1 (by rfl) ⟨2150099, by rfl⟩ : syracuseStep 2866799 = 4300199) B4300199
theorem B2547419 : Blo 1697549 2547419 := bstep (se 1 (by rfl) ⟨1910564, by rfl⟩ : syracuseStep 2547419 = 3821129) B3821129
theorem B12902327 : Blo 1697549 12902327 := bstep (se 1 (by rfl) ⟨9676745, by rfl⟩ : syracuseStep 12902327 = 19353491) B19353491
theorem B2867143 : Blo 1697549 2867143 := bstep (se 1 (by rfl) ⟨2150357, by rfl⟩ : syracuseStep 2867143 = 4300715) B4300715
theorem B2547689 : Blo 1697549 2547689 := bstep (se 2 (by rfl) ⟨955383, by rfl⟩ : syracuseStep 2547689 = 1910767) B1910767
theorem B2547815 : Blo 1697549 2547815 := bstep (se 1 (by rfl) ⟨1910861, by rfl⟩ : syracuseStep 2547815 = 3821723) B3821723
theorem B27549821 : Blo 1697549 27549821 := bstep (se 3 (by rfl) ⟨5165591, by rfl⟩ : syracuseStep 27549821 = 10331183) B10331183
theorem B2547947 : Blo 1697549 2547947 := bstep (se 1 (by rfl) ⟨1910960, by rfl⟩ : syracuseStep 2547947 = 3821921) B3821921
theorem B4301039 : Blo 1697549 4301039 := bstep (se 1 (by rfl) ⟨3225779, by rfl⟩ : syracuseStep 4301039 = 6451559) B6451559
theorem B5439737 : Blo 1697549 5439737 := bstep (se 2 (by rfl) ⟨2039901, by rfl⟩ : syracuseStep 5439737 = 4079803) B4079803
theorem B2548007 : Blo 1697549 2548007 := bstep (se 1 (by rfl) ⟨1911005, by rfl⟩ : syracuseStep 2548007 = 3822011) B3822011
theorem B21766481 : Blo 1697549 21766481 := bstep (se 2 (by rfl) ⟨8162430, by rfl⟩ : syracuseStep 21766481 = 16324861) B16324861
theorem B12902813 : Blo 1697549 12902813 := bstep (se 3 (by rfl) ⟨2419277, by rfl⟩ : syracuseStep 12902813 = 4838555) B4838555
theorem B6447671 : Blo 1697549 6447671 := bstep (se 1 (by rfl) ⟨4835753, by rfl⟩ : syracuseStep 6447671 = 9671507) B9671507
theorem B5735015 : Blo 1697549 5735015 := bstep (se 1 (by rfl) ⟨4301261, by rfl⟩ : syracuseStep 5735015 = 8602523) B8602523
theorem B9183881 : Blo 1697549 9183881 := bstep (se 2 (by rfl) ⟨3443955, by rfl⟩ : syracuseStep 9183881 = 6887911) B6887911
theorem B2548457 : Blo 1697549 2548457 := bstep (se 2 (by rfl) ⟨955671, by rfl⟩ : syracuseStep 2548457 = 1911343) B1911343
theorem B73417589 : Blo 1697549 73417589 := bstep (se 5 (by rfl) ⟨3441449, by rfl⟩ : syracuseStep 73417589 = 6882899) B6882899
theorem B19350575 : Blo 1697549 19350575 := bstep (se 1 (by rfl) ⟨14512931, by rfl⟩ : syracuseStep 19350575 = 29025863) B29025863
theorem B6448187 : Blo 1697549 6448187 := bstep (se 1 (by rfl) ⟨4836140, by rfl⟩ : syracuseStep 6448187 = 9672281) B9672281
theorem B23880763 : Blo 1697549 23880763 := bstep (se 1 (by rfl) ⟨17910572, by rfl⟩ : syracuseStep 23880763 = 35821145) B35821145
theorem B2548847 : Blo 1697549 2548847 := bstep (se 1 (by rfl) ⟨1911635, by rfl⟩ : syracuseStep 2548847 = 3823271) B3823271
theorem B18359455 : Blo 1697549 18359455 := bstep (se 1 (by rfl) ⟨13769591, by rfl⟩ : syracuseStep 18359455 = 27539183) B27539183
theorem B2548967 : Blo 1697549 2548967 := bstep (se 1 (by rfl) ⟨1911725, by rfl⟩ : syracuseStep 2548967 = 3823451) B3823451
theorem B2549033 : Blo 1697549 2549033 := bstep (se 2 (by rfl) ⟨955887, by rfl⟩ : syracuseStep 2549033 = 1911775) B1911775
theorem B2549303 : Blo 1697549 2549303 := bstep (se 1 (by rfl) ⟨1911977, by rfl⟩ : syracuseStep 2549303 = 3823955) B3823955
theorem B4081225 : Blo 1697549 4081225 := bstep (se 2 (by rfl) ⟨1530459, by rfl⟩ : syracuseStep 4081225 = 3060919) B3060919
theorem B4834991 : Blo 1697549 4834991 := bstep (se 1 (by rfl) ⟨3626243, by rfl⟩ : syracuseStep 4834991 = 7252487) B7252487
theorem B22062775 : Blo 1697549 22062775 := bstep (se 1 (by rfl) ⟨16547081, by rfl⟩ : syracuseStep 22062775 = 33094163) B33094163
theorem B1697695 : Blo 1697549 1697695 := bstep (se 1 (by rfl) ⟨1273271, by rfl⟩ : syracuseStep 1697695 = 2546543) B2546543
theorem B1697703 : Blo 1697549 1697703 := bstep (se 1 (by rfl) ⟨1273277, by rfl⟩ : syracuseStep 1697703 = 2546555) B2546555
theorem B8595395 : Blo 1697549 8595395 := bstep (se 1 (by rfl) ⟨6446546, by rfl⟩ : syracuseStep 8595395 = 12893093) B12893093
theorem B4589561 : Blo 1697549 4589561 := bstep (se 2 (by rfl) ⟨1721085, by rfl⟩ : syracuseStep 4589561 = 3442171) B3442171
theorem B55838753 : Blo 1697549 55838753 := bstep (se 2 (by rfl) ⟨20939532, by rfl⟩ : syracuseStep 55838753 = 41879065) B41879065
theorem B29034611 : Blo 1697549 29034611 := bstep (se 1 (by rfl) ⟨21775958, by rfl⟩ : syracuseStep 29034611 = 43551917) B43551917
theorem B2148535 : Blo 1697549 2148535 := bstep (se 1 (by rfl) ⟨1611401, by rfl⟩ : syracuseStep 2148535 = 3222803) B3222803
theorem B5441735 : Blo 1697549 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B1911199 : Blo 1697549 1911199 := bstep (se 1 (by rfl) ⟨1433399, by rfl⟩ : syracuseStep 1911199 = 2866799) B2866799
theorem B19352033 : Blo 1697549 19352033 := bstep (se 2 (by rfl) ⟨7257012, by rfl⟩ : syracuseStep 19352033 = 14514025) B14514025
theorem B1698279 : Blo 1697549 1698279 := bstep (se 1 (by rfl) ⟨1273709, by rfl⟩ : syracuseStep 1698279 = 2547419) B2547419
theorem B1698459 : Blo 1697549 1698459 := bstep (se 1 (by rfl) ⟨1273844, by rfl⟩ : syracuseStep 1698459 = 2547689) B2547689
theorem B4836095 : Blo 1697549 4836095 := bstep (se 1 (by rfl) ⟨3627071, by rfl⟩ : syracuseStep 4836095 = 7254143) B7254143
theorem B10332935 : Blo 1697549 10332935 := bstep (se 1 (by rfl) ⟨7749701, by rfl⟩ : syracuseStep 10332935 = 15499403) B15499403
theorem B1698927 : Blo 1697549 1698927 := bstep (se 1 (by rfl) ⟨1274195, by rfl⟩ : syracuseStep 1698927 = 2548391) B2548391
theorem B1699007 : Blo 1697549 1699007 := bstep (se 1 (by rfl) ⟨1274255, by rfl⟩ : syracuseStep 1699007 = 2548511) B2548511
theorem B1699023 : Blo 1697549 1699023 := bstep (se 1 (by rfl) ⟨1274267, by rfl⟩ : syracuseStep 1699023 = 2548535) B2548535
theorem B1699143 : Blo 1697549 1699143 := bstep (se 1 (by rfl) ⟨1274357, by rfl⟩ : syracuseStep 1699143 = 2548715) B2548715
theorem B6450587 : Blo 1697549 6450587 := bstep (se 1 (by rfl) ⟨4837940, by rfl⟩ : syracuseStep 6450587 = 9675881) B9675881
theorem B9670049 : Blo 1697549 9670049 := bstep (se 2 (by rfl) ⟨3626268, by rfl⟩ : syracuseStep 9670049 = 7252537) B7252537
theorem B4836779 : Blo 1697549 4836779 := bstep (se 1 (by rfl) ⟨3627584, by rfl⟩ : syracuseStep 4836779 = 7255169) B7255169
theorem B7253459 : Blo 1697549 7253459 := bstep (se 1 (by rfl) ⟨5440094, by rfl⟩ : syracuseStep 7253459 = 10880189) B10880189
theorem B3821075 : Blo 1697549 3821075 := bstep (se 1 (by rfl) ⟨2865806, by rfl⟩ : syracuseStep 3821075 = 5731613) B5731613
theorem B3223145 : Blo 1697549 3223145 := bstep (se 2 (by rfl) ⟨1208679, by rfl⟩ : syracuseStep 3223145 = 2417359) B2417359
theorem B5812307 : Blo 1697549 5812307 := bstep (se 1 (by rfl) ⟨4359230, by rfl⟩ : syracuseStep 5812307 = 8718461) B8718461
theorem B14700665 : Blo 1697549 14700665 := bstep (se 2 (by rfl) ⟨5512749, by rfl⟩ : syracuseStep 14700665 = 11025499) B11025499
theorem B3223775 : Blo 1697549 3223775 := bstep (se 1 (by rfl) ⟨2417831, by rfl⟩ : syracuseStep 3223775 = 4835663) B4835663
theorem B1814783 : Blo 1697549 1814783 := bstep (se 1 (by rfl) ⟨1361087, by rfl⟩ : syracuseStep 1814783 = 2722175) B2722175
theorem B5444093 : Blo 1697549 5444093 := bstep (se 3 (by rfl) ⟨1020767, by rfl⟩ : syracuseStep 5444093 = 2041535) B2041535
theorem B3822137 : Blo 1697549 3822137 := bstep (se 2 (by rfl) ⟨1433301, by rfl⟩ : syracuseStep 3822137 = 2866603) B2866603
theorem B19346201 : Blo 1697549 19346201 := bstep (se 2 (by rfl) ⟨7254825, by rfl⟩ : syracuseStep 19346201 = 14509651) B14509651
theorem B5731451 : Blo 1697549 5731451 := bstep (se 1 (by rfl) ⟨4298588, by rfl⟩ : syracuseStep 5731451 = 8597177) B8597177
theorem B3822857 : Blo 1697549 3822857 := bstep (se 2 (by rfl) ⟨1433571, by rfl⟩ : syracuseStep 3822857 = 2867143) B2867143
theorem B6125053 : Blo 1697549 6125053 := bstep (se 3 (by rfl) ⟨1148447, by rfl⟩ : syracuseStep 6125053 = 2296895) B2296895
theorem B14505551 : Blo 1697549 14505551 := bstep (se 1 (by rfl) ⟨10879163, by rfl⟩ : syracuseStep 14505551 = 21758327) B21758327
theorem B31004369 : Blo 1697549 31004369 := bstep (se 2 (by rfl) ⟨11626638, by rfl⟩ : syracuseStep 31004369 = 23253277) B23253277
theorem B5592809 : Blo 1697549 5592809 := bstep (se 2 (by rfl) ⟨2097303, by rfl⟩ : syracuseStep 5592809 = 4194607) B4194607
theorem B13768555 : Blo 1697549 13768555 := bstep (se 1 (by rfl) ⟨10326416, by rfl⟩ : syracuseStep 13768555 = 20652833) B20652833
theorem B1964027 : Blo 1697549 1964027 := bstep (se 1 (by rfl) ⟨1473020, by rfl⟩ : syracuseStep 1964027 = 2946041) B2946041
theorem B3823847 : Blo 1697549 3823847 := bstep (se 1 (by rfl) ⟨2867885, by rfl⟩ : syracuseStep 3823847 = 5735771) B5735771
theorem B3823865 : Blo 1697549 3823865 := bstep (se 2 (by rfl) ⟨1433949, by rfl⟩ : syracuseStep 3823865 = 2867899) B2867899
theorem B4299065 : Blo 1697549 4299065 := bstep (se 2 (by rfl) ⟨1612149, by rfl⟩ : syracuseStep 4299065 = 3224299) B3224299
theorem B8599931 : Blo 1697549 8599931 := bstep (se 1 (by rfl) ⟨6449948, by rfl⟩ : syracuseStep 8599931 = 12899897) B12899897
theorem B20666843 : Blo 1697549 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B3226159 : Blo 1697549 3226159 := bstep (se 1 (by rfl) ⟨2419619, by rfl⟩ : syracuseStep 3226159 = 4839239) B4839239
theorem B2865719 : Blo 1697549 2865719 := bstep (se 1 (by rfl) ⟨2149289, by rfl⟩ : syracuseStep 2865719 = 4298579) B4298579
theorem B6445727 : Blo 1697549 6445727 := bstep (se 1 (by rfl) ⟨4834295, by rfl⟩ : syracuseStep 6445727 = 9668591) B9668591
theorem B3627679 : Blo 1697549 3627679 := bstep (se 1 (by rfl) ⟨2720759, by rfl⟩ : syracuseStep 3627679 = 5441519) B5441519
theorem B9673465 : Blo 1697549 9673465 := bstep (se 2 (by rfl) ⟨3627549, by rfl⟩ : syracuseStep 9673465 = 7255099) B7255099
theorem B2546471 : Blo 1697549 2546471 := bstep (se 1 (by rfl) ⟨1909853, by rfl⟩ : syracuseStep 2546471 = 3819707) B3819707
theorem B2546495 : Blo 1697549 2546495 := bstep (se 1 (by rfl) ⟨1909871, by rfl⟩ : syracuseStep 2546495 = 3819743) B3819743
theorem B134159285 : Blo 1697549 134159285 := bstep (se 5 (by rfl) ⟨6288716, by rfl⟩ : syracuseStep 134159285 = 12577433) B12577433
theorem B2546795 : Blo 1697549 2546795 := bstep (se 1 (by rfl) ⟨1910096, by rfl⟩ : syracuseStep 2546795 = 3820193) B3820193
theorem B2546939 : Blo 1697549 2546939 := bstep (se 1 (by rfl) ⟨1910204, by rfl⟩ : syracuseStep 2546939 = 3820409) B3820409
theorem B2547035 : Blo 1697549 2547035 := bstep (se 1 (by rfl) ⟨1910276, by rfl⟩ : syracuseStep 2547035 = 3820553) B3820553
theorem B2547065 : Blo 1697549 2547065 := bstep (se 2 (by rfl) ⟨955149, by rfl⟩ : syracuseStep 2547065 = 1910299) B1910299
theorem B2547071 : Blo 1697549 2547071 := bstep (se 1 (by rfl) ⟨1910303, by rfl⟩ : syracuseStep 2547071 = 3820607) B3820607
theorem B47742347 : Blo 1697549 47742347 := bstep (se 1 (by rfl) ⟨35806760, by rfl⟩ : syracuseStep 47742347 = 71613521) B71613521
theorem B23256557 : Blo 1697549 23256557 := bstep (se 3 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 23256557 = 8721209) B8721209
theorem B6626807 : Blo 1697549 6626807 := bstep (se 1 (by rfl) ⟨4970105, by rfl⟩ : syracuseStep 6626807 = 9940211) B9940211
theorem B56638973 : Blo 1697549 56638973 := bstep (se 3 (by rfl) ⟨10619807, by rfl⟩ : syracuseStep 56638973 = 21239615) B21239615
theorem B2866907 : Blo 1697549 2866907 := bstep (se 1 (by rfl) ⟨2150180, by rfl⟩ : syracuseStep 2866907 = 4300361) B4300361
theorem B251354987 : Blo 1697549 251354987 := bstep (se 1 (by rfl) ⟨188516240, by rfl⟩ : syracuseStep 251354987 = 377032481) B377032481
theorem B2547623 : Blo 1697549 2547623 := bstep (se 1 (by rfl) ⟨1910717, by rfl⟩ : syracuseStep 2547623 = 3821435) B3821435
theorem B8601551 : Blo 1697549 8601551 := bstep (se 1 (by rfl) ⟨6451163, by rfl⟩ : syracuseStep 8601551 = 12902327) B12902327
theorem B21766117 : Blo 1697549 21766117 := bstep (se 4 (by rfl) ⟨2040573, by rfl⟩ : syracuseStep 21766117 = 4081147) B4081147
theorem B2867177 : Blo 1697549 2867177 := bstep (se 2 (by rfl) ⟨1075191, by rfl⟩ : syracuseStep 2867177 = 2150383) B2150383
theorem B2547695 : Blo 1697549 2547695 := bstep (se 1 (by rfl) ⟨1910771, by rfl⟩ : syracuseStep 2547695 = 3821543) B3821543
theorem B3874871 : Blo 1697549 3874871 := bstep (se 1 (by rfl) ⟨2906153, by rfl⟩ : syracuseStep 3874871 = 5812307) B5812307
theorem B18366547 : Blo 1697549 18366547 := bstep (se 1 (by rfl) ⟨13774910, by rfl⟩ : syracuseStep 18366547 = 27549821) B27549821
theorem B2867359 : Blo 1697549 2867359 := bstep (se 1 (by rfl) ⟨2150519, by rfl⟩ : syracuseStep 2867359 = 4301039) B4301039
theorem B8601875 : Blo 1697549 8601875 := bstep (se 1 (by rfl) ⟨6451406, by rfl⟩ : syracuseStep 8601875 = 12902813) B12902813
theorem B3629395 : Blo 1697549 3629395 := bstep (se 1 (by rfl) ⟨2722046, by rfl⟩ : syracuseStep 3629395 = 5444093) B5444093
theorem B2548091 : Blo 1697549 2548091 := bstep (se 1 (by rfl) ⟨1911068, by rfl⟩ : syracuseStep 2548091 = 3822137) B3822137
theorem B2548265 : Blo 1697549 2548265 := bstep (se 2 (by rfl) ⟨955599, by rfl⟩ : syracuseStep 2548265 = 1911199) B1911199
theorem B4301545 : Blo 1697549 4301545 := bstep (se 2 (by rfl) ⟨1613079, by rfl⟩ : syracuseStep 4301545 = 3226159) B3226159
theorem B2548571 : Blo 1697549 2548571 := bstep (se 1 (by rfl) ⟨1911428, by rfl⟩ : syracuseStep 2548571 = 3822857) B3822857
theorem B20669579 : Blo 1697549 20669579 := bstep (se 1 (by rfl) ⟨15502184, by rfl⟩ : syracuseStep 20669579 = 31004369) B31004369
theorem B3728539 : Blo 1697549 3728539 := bstep (se 1 (by rfl) ⟨2796404, by rfl⟩ : syracuseStep 3728539 = 5592809) B5592809
theorem B37225835 : Blo 1697549 37225835 := bstep (se 1 (by rfl) ⟨27919376, by rfl⟩ : syracuseStep 37225835 = 55838753) B55838753
theorem B2549231 : Blo 1697549 2549231 := bstep (se 1 (by rfl) ⟨1911923, by rfl⟩ : syracuseStep 2549231 = 3823847) B3823847
theorem B2549243 : Blo 1697549 2549243 := bstep (se 1 (by rfl) ⟨1911932, by rfl⟩ : syracuseStep 2549243 = 3823865) B3823865
theorem B24479273 : Blo 1697549 24479273 := bstep (se 2 (by rfl) ⟨9179727, by rfl⟩ : syracuseStep 24479273 = 18359455) B18359455
theorem B1910479 : Blo 1697549 1910479 := bstep (se 1 (by rfl) ⟨1432859, by rfl⟩ : syracuseStep 1910479 = 2865719) B2865719
theorem B1697647 : Blo 1697549 1697647 := bstep (se 1 (by rfl) ⟨1273235, by rfl⟩ : syracuseStep 1697647 = 2546471) B2546471
theorem B1697663 : Blo 1697549 1697663 := bstep (se 1 (by rfl) ⟨1273247, by rfl⟩ : syracuseStep 1697663 = 2546495) B2546495
theorem B1697863 : Blo 1697549 1697863 := bstep (se 1 (by rfl) ⟨1273397, by rfl⟩ : syracuseStep 1697863 = 2546795) B2546795
theorem B5441633 : Blo 1697549 5441633 := bstep (se 2 (by rfl) ⟨2040612, by rfl⟩ : syracuseStep 5441633 = 4081225) B4081225
theorem B1697959 : Blo 1697549 1697959 := bstep (se 1 (by rfl) ⟨1273469, by rfl⟩ : syracuseStep 1697959 = 2546939) B2546939
theorem B1698023 : Blo 1697549 1698023 := bstep (se 1 (by rfl) ⟨1273517, by rfl⟩ : syracuseStep 1698023 = 2547035) B2547035
theorem B1698043 : Blo 1697549 1698043 := bstep (se 1 (by rfl) ⟨1273532, by rfl⟩ : syracuseStep 1698043 = 2547065) B2547065
theorem B1698047 : Blo 1697549 1698047 := bstep (se 1 (by rfl) ⟨1273535, by rfl⟩ : syracuseStep 1698047 = 2547071) B2547071
theorem B31828231 : Blo 1697549 31828231 := bstep (se 1 (by rfl) ⟨23871173, by rfl⟩ : syracuseStep 31828231 = 47742347) B47742347
theorem B4835639 : Blo 1697549 4835639 := bstep (se 1 (by rfl) ⟨3626729, by rfl⟩ : syracuseStep 4835639 = 7253459) B7253459
theorem B4417871 : Blo 1697549 4417871 := bstep (se 1 (by rfl) ⟨3313403, by rfl⟩ : syracuseStep 4417871 = 6626807) B6626807
theorem B37759315 : Blo 1697549 37759315 := bstep (se 1 (by rfl) ⟨28319486, by rfl⟩ : syracuseStep 37759315 = 56638973) B56638973
theorem B2148763 : Blo 1697549 2148763 := bstep (se 1 (by rfl) ⟨1611572, by rfl⟩ : syracuseStep 2148763 = 3223145) B3223145
theorem B1911271 : Blo 1697549 1911271 := bstep (se 1 (by rfl) ⟨1433453, by rfl⟩ : syracuseStep 1911271 = 2866907) B2866907
theorem B167569991 : Blo 1697549 167569991 := bstep (se 1 (by rfl) ⟨125677493, by rfl⟩ : syracuseStep 167569991 = 251354987) B251354987
theorem B1698415 : Blo 1697549 1698415 := bstep (se 1 (by rfl) ⟨1273811, by rfl⟩ : syracuseStep 1698415 = 2547623) B2547623
theorem B1911451 : Blo 1697549 1911451 := bstep (se 1 (by rfl) ⟨1433588, by rfl⟩ : syracuseStep 1911451 = 2867177) B2867177
theorem B5237405 : Blo 1697549 5237405 := bstep (se 3 (by rfl) ⟨982013, by rfl⟩ : syracuseStep 5237405 = 1964027) B1964027
theorem B1698463 : Blo 1697549 1698463 := bstep (se 1 (by rfl) ⟨1273847, by rfl⟩ : syracuseStep 1698463 = 2547695) B2547695
theorem B1698543 : Blo 1697549 1698543 := bstep (se 1 (by rfl) ⟨1273907, by rfl⟩ : syracuseStep 1698543 = 2547815) B2547815
theorem B9800443 : Blo 1697549 9800443 := bstep (se 1 (by rfl) ⟨7350332, by rfl⟩ : syracuseStep 9800443 = 14700665) B14700665
theorem B2149183 : Blo 1697549 2149183 := bstep (se 1 (by rfl) ⟨1611887, by rfl⟩ : syracuseStep 2149183 = 3223775) B3223775
theorem B1698631 : Blo 1697549 1698631 := bstep (se 1 (by rfl) ⟨1273973, by rfl⟩ : syracuseStep 1698631 = 2547947) B2547947
theorem B1698671 : Blo 1697549 1698671 := bstep (se 1 (by rfl) ⟨1274003, by rfl⟩ : syracuseStep 1698671 = 2548007) B2548007
theorem B14510987 : Blo 1697549 14510987 := bstep (se 1 (by rfl) ⟨10883240, by rfl⟩ : syracuseStep 14510987 = 21766481) B21766481
theorem B127364069 : Blo 1697549 127364069 := bstep (se 4 (by rfl) ⟨11940381, by rfl⟩ : syracuseStep 127364069 = 23880763) B23880763
theorem B6122587 : Blo 1697549 6122587 := bstep (se 1 (by rfl) ⟨4591940, by rfl⟩ : syracuseStep 6122587 = 9183881) B9183881
theorem B1698971 : Blo 1697549 1698971 := bstep (se 1 (by rfl) ⟨1274228, by rfl⟩ : syracuseStep 1698971 = 2548457) B2548457
theorem B12897467 : Blo 1697549 12897467 := bstep (se 1 (by rfl) ⟨9673100, by rfl⟩ : syracuseStep 12897467 = 19346201) B19346201
theorem B1699231 : Blo 1697549 1699231 := bstep (se 1 (by rfl) ⟨1274423, by rfl⟩ : syracuseStep 1699231 = 2548847) B2548847
theorem B3820967 : Blo 1697549 3820967 := bstep (se 1 (by rfl) ⟨2865725, by rfl⟩ : syracuseStep 3820967 = 5731451) B5731451
theorem B1699311 : Blo 1697549 1699311 := bstep (se 1 (by rfl) ⟨1274483, by rfl⟩ : syracuseStep 1699311 = 2548967) B2548967
theorem B1699355 : Blo 1697549 1699355 := bstep (se 1 (by rfl) ⟨1274516, by rfl⟩ : syracuseStep 1699355 = 2549033) B2549033
theorem B4836905 : Blo 1697549 4836905 := bstep (se 2 (by rfl) ⟨1813839, by rfl⟩ : syracuseStep 4836905 = 3627679) B3627679
theorem B12897953 : Blo 1697549 12897953 := bstep (se 2 (by rfl) ⟨4836732, by rfl⟩ : syracuseStep 12897953 = 9673465) B9673465
theorem B1699535 : Blo 1697549 1699535 := bstep (se 1 (by rfl) ⟨1274651, by rfl⟩ : syracuseStep 1699535 = 2549303) B2549303
theorem B9670367 : Blo 1697549 9670367 := bstep (se 1 (by rfl) ⟨7252775, by rfl⟩ : syracuseStep 9670367 = 14505551) B14505551
theorem B3223327 : Blo 1697549 3223327 := bstep (se 1 (by rfl) ⟨2417495, by rfl⟩ : syracuseStep 3223327 = 4834991) B4834991
theorem B5730263 : Blo 1697549 5730263 := bstep (se 1 (by rfl) ⟨4297697, by rfl⟩ : syracuseStep 5730263 = 8595395) B8595395
theorem B4297151 : Blo 1697549 4297151 := bstep (se 1 (by rfl) ⟨3222863, by rfl⟩ : syracuseStep 4297151 = 6445727) B6445727
theorem B3224063 : Blo 1697549 3224063 := bstep (se 1 (by rfl) ⟨2418047, by rfl⟩ : syracuseStep 3224063 = 4836095) B4836095
theorem B3224519 : Blo 1697549 3224519 := bstep (se 1 (by rfl) ⟨2418389, by rfl⟩ : syracuseStep 3224519 = 4836779) B4836779
theorem B15504371 : Blo 1697549 15504371 := bstep (se 1 (by rfl) ⟨11628278, by rfl⟩ : syracuseStep 15504371 = 23256557) B23256557
theorem B357758093 : Blo 1697549 357758093 := bstep (se 3 (by rfl) ⟨67079642, by rfl⟩ : syracuseStep 357758093 = 134159285) B134159285
theorem B29021489 : Blo 1697549 29021489 := bstep (se 2 (by rfl) ⟨10883058, by rfl⟩ : syracuseStep 29021489 = 21766117) B21766117
theorem B3626491 : Blo 1697549 3626491 := bstep (se 1 (by rfl) ⟨2719868, by rfl⟩ : syracuseStep 3626491 = 5439737) B5439737
theorem B2864713 : Blo 1697549 2864713 := bstep (se 2 (by rfl) ⟨1074267, by rfl⟩ : syracuseStep 2864713 = 2148535) B2148535
theorem B4298447 : Blo 1697549 4298447 := bstep (se 1 (by rfl) ⟨3223835, by rfl⟩ : syracuseStep 4298447 = 6447671) B6447671
theorem B3823343 : Blo 1697549 3823343 := bstep (se 1 (by rfl) ⟨2867507, by rfl⟩ : syracuseStep 3823343 = 5735015) B5735015
theorem B48945059 : Blo 1697549 48945059 := bstep (se 1 (by rfl) ⟨36708794, by rfl⟩ : syracuseStep 48945059 = 73417589) B73417589
theorem B4839421 : Blo 1697549 4839421 := bstep (se 3 (by rfl) ⟨907391, by rfl⟩ : syracuseStep 4839421 = 1814783) B1814783
theorem B12900383 : Blo 1697549 12900383 := bstep (se 1 (by rfl) ⟨9675287, by rfl⟩ : syracuseStep 12900383 = 19350575) B19350575
theorem B4298791 : Blo 1697549 4298791 := bstep (se 1 (by rfl) ⟨3224093, by rfl⟩ : syracuseStep 4298791 = 6448187) B6448187
theorem B19356407 : Blo 1697549 19356407 := bstep (se 1 (by rfl) ⟨14517305, by rfl⟩ : syracuseStep 19356407 = 29034611) B29034611
theorem B3627823 : Blo 1697549 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B2866043 : Blo 1697549 2866043 := bstep (se 1 (by rfl) ⟨2149532, by rfl⟩ : syracuseStep 2866043 = 4299065) B4299065
theorem B5733287 : Blo 1697549 5733287 := bstep (se 1 (by rfl) ⟨4299965, by rfl⟩ : syracuseStep 5733287 = 8599931) B8599931
theorem B13777895 : Blo 1697549 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B12901355 : Blo 1697549 12901355 := bstep (se 1 (by rfl) ⟨9676016, by rfl⟩ : syracuseStep 12901355 = 19352033) B19352033
theorem B6888623 : Blo 1697549 6888623 := bstep (se 1 (by rfl) ⟨5166467, by rfl⟩ : syracuseStep 6888623 = 10332935) B10332935
theorem B8166737 : Blo 1697549 8166737 := bstep (se 2 (by rfl) ⟨3062526, by rfl⟩ : syracuseStep 8166737 = 6125053) B6125053
theorem B29417033 : Blo 1697549 29417033 := bstep (se 2 (by rfl) ⟨11031387, by rfl⟩ : syracuseStep 29417033 = 22062775) B22062775
theorem B4300391 : Blo 1697549 4300391 := bstep (se 1 (by rfl) ⟨3225293, by rfl⟩ : syracuseStep 4300391 = 6450587) B6450587
theorem B6446699 : Blo 1697549 6446699 := bstep (se 1 (by rfl) ⟨4835024, by rfl⟩ : syracuseStep 6446699 = 9670049) B9670049
theorem B2547383 : Blo 1697549 2547383 := bstep (se 1 (by rfl) ⟨1910537, by rfl⟩ : syracuseStep 2547383 = 3821075) B3821075
theorem B18358073 : Blo 1697549 18358073 := bstep (se 2 (by rfl) ⟨6884277, by rfl⟩ : syracuseStep 18358073 = 13768555) B13768555
theorem B5734367 : Blo 1697549 5734367 := bstep (se 1 (by rfl) ⟨4300775, by rfl⟩ : syracuseStep 5734367 = 8601551) B8601551
theorem B12238829 : Blo 1697549 12238829 := bstep (se 3 (by rfl) ⟨2294780, by rfl⟩ : syracuseStep 12238829 = 4589561) B4589561
theorem B5734583 : Blo 1697549 5734583 := bstep (se 1 (by rfl) ⟨4300937, by rfl⟩ : syracuseStep 5734583 = 8601875) B8601875
theorem B2548361 : Blo 1697549 2548361 := bstep (se 2 (by rfl) ⟨955635, by rfl⟩ : syracuseStep 2548361 = 1911271) B1911271
theorem B13779719 : Blo 1697549 13779719 := bstep (se 1 (by rfl) ⟨10334789, by rfl⟩ : syracuseStep 13779719 = 20669579) B20669579
theorem B12895037 : Blo 1697549 12895037 := bstep (se 3 (by rfl) ⟨2417819, by rfl⟩ : syracuseStep 12895037 = 4835639) B4835639
theorem B2548601 : Blo 1697549 2548601 := bstep (se 2 (by rfl) ⟨955725, by rfl⟩ : syracuseStep 2548601 = 1911451) B1911451
theorem B5735393 : Blo 1697549 5735393 := bstep (se 2 (by rfl) ⟨2150772, by rfl⟩ : syracuseStep 5735393 = 4301545) B4301545
theorem B13067257 : Blo 1697549 13067257 := bstep (se 2 (by rfl) ⟨4900221, by rfl⟩ : syracuseStep 13067257 = 9800443) B9800443
theorem B16319515 : Blo 1697549 16319515 := bstep (se 1 (by rfl) ⟨12239636, by rfl⟩ : syracuseStep 16319515 = 24479273) B24479273
theorem B2548895 : Blo 1697549 2548895 := bstep (se 1 (by rfl) ⟨1911671, by rfl⟩ : syracuseStep 2548895 = 3823343) B3823343
theorem B32630039 : Blo 1697549 32630039 := bstep (se 1 (by rfl) ⟨24472529, by rfl⟩ : syracuseStep 32630039 = 48945059) B48945059
theorem B3491603 : Blo 1697549 3491603 := bstep (se 1 (by rfl) ⟨2618702, by rfl⟩ : syracuseStep 3491603 = 5237405) B5237405
theorem B12904271 : Blo 1697549 12904271 := bstep (se 1 (by rfl) ⟨9678203, by rfl⟩ : syracuseStep 12904271 = 19356407) B19356407
theorem B1910695 : Blo 1697549 1910695 := bstep (se 1 (by rfl) ⟨1433021, by rfl⟩ : syracuseStep 1910695 = 2866043) B2866043
theorem B4835321 : Blo 1697549 4835321 := bstep (se 2 (by rfl) ⟨1813245, by rfl⟩ : syracuseStep 4835321 = 3626491) B3626491
theorem B3819617 : Blo 1697549 3819617 := bstep (se 2 (by rfl) ⟨1432356, by rfl⟩ : syracuseStep 3819617 = 2864713) B2864713
theorem B1698255 : Blo 1697549 1698255 := bstep (se 1 (by rfl) ⟨1273691, by rfl⟩ : syracuseStep 1698255 = 2547383) B2547383
theorem B3820175 : Blo 1697549 3820175 := bstep (se 1 (by rfl) ⟨2865131, by rfl⟩ : syracuseStep 3820175 = 5730263) B5730263
theorem B2583247 : Blo 1697549 2583247 := bstep (se 1 (by rfl) ⟨1937435, by rfl⟩ : syracuseStep 2583247 = 3874871) B3874871
theorem B24488729 : Blo 1697549 24488729 := bstep (se 2 (by rfl) ⟨9183273, by rfl⟩ : syracuseStep 24488729 = 18366547) B18366547
theorem B1698727 : Blo 1697549 1698727 := bstep (se 1 (by rfl) ⟨1274045, by rfl⟩ : syracuseStep 1698727 = 2548091) B2548091
theorem B42437641 : Blo 1697549 42437641 := bstep (se 2 (by rfl) ⟨15914115, by rfl⟩ : syracuseStep 42437641 = 31828231) B31828231
theorem B1698843 : Blo 1697549 1698843 := bstep (se 1 (by rfl) ⟨1274132, by rfl⟩ : syracuseStep 1698843 = 2548265) B2548265
theorem B18369661 : Blo 1697549 18369661 := bstep (se 3 (by rfl) ⟨3444311, by rfl⟩ : syracuseStep 18369661 = 6888623) B6888623
theorem B1699047 : Blo 1697549 1699047 := bstep (se 1 (by rfl) ⟨1274285, by rfl⟩ : syracuseStep 1699047 = 2548571) B2548571
theorem B2149679 : Blo 1697549 2149679 := bstep (se 1 (by rfl) ⟨1612259, by rfl⟩ : syracuseStep 2149679 = 3224519) B3224519
theorem B47123957 : Blo 1697549 47123957 := bstep (se 5 (by rfl) ⟨2208935, by rfl⟩ : syracuseStep 47123957 = 4417871) B4417871
theorem B24817223 : Blo 1697549 24817223 := bstep (se 1 (by rfl) ⟨18612917, by rfl⟩ : syracuseStep 24817223 = 37225835) B37225835
theorem B1699487 : Blo 1697549 1699487 := bstep (se 1 (by rfl) ⟨1274615, by rfl⟩ : syracuseStep 1699487 = 2549231) B2549231
theorem B1699495 : Blo 1697549 1699495 := bstep (se 1 (by rfl) ⟨1274621, by rfl⟩ : syracuseStep 1699495 = 2549243) B2549243
theorem B4837097 : Blo 1697549 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B8597501 : Blo 1697549 8597501 := bstep (se 3 (by rfl) ⟨1612031, by rfl⟩ : syracuseStep 8597501 = 3224063) B3224063
theorem B8163449 : Blo 1697549 8163449 := bstep (se 2 (by rfl) ⟨3061293, by rfl⟩ : syracuseStep 8163449 = 6122587) B6122587
theorem B3822191 : Blo 1697549 3822191 := bstep (se 1 (by rfl) ⟨2866643, by rfl⟩ : syracuseStep 3822191 = 5733287) B5733287
theorem B8598311 : Blo 1697549 8598311 := bstep (se 1 (by rfl) ⟨6448733, by rfl⟩ : syracuseStep 8598311 = 12897467) B12897467
theorem B5444491 : Blo 1697549 5444491 := bstep (se 1 (by rfl) ⟨4083368, by rfl⟩ : syracuseStep 5444491 = 8166737) B8166737
theorem B3224603 : Blo 1697549 3224603 := bstep (se 1 (by rfl) ⟨2418452, by rfl⟩ : syracuseStep 3224603 = 4836905) B4836905
theorem B4297769 : Blo 1697549 4297769 := bstep (se 2 (by rfl) ⟨1611663, by rfl⟩ : syracuseStep 4297769 = 3223327) B3223327
theorem B4297799 : Blo 1697549 4297799 := bstep (se 1 (by rfl) ⟨3223349, by rfl⟩ : syracuseStep 4297799 = 6446699) B6446699
theorem B8598635 : Blo 1697549 8598635 := bstep (se 1 (by rfl) ⟨6448976, by rfl⟩ : syracuseStep 8598635 = 12897953) B12897953
theorem B3822911 : Blo 1697549 3822911 := bstep (se 1 (by rfl) ⟨2867183, by rfl⟩ : syracuseStep 3822911 = 5734367) B5734367
theorem B6452561 : Blo 1697549 6452561 := bstep (se 2 (by rfl) ⟨2419710, by rfl⟩ : syracuseStep 6452561 = 4839421) B4839421
theorem B5731721 : Blo 1697549 5731721 := bstep (se 2 (by rfl) ⟨2149395, by rfl⟩ : syracuseStep 5731721 = 4298791) B4298791
theorem B3823145 : Blo 1697549 3823145 := bstep (se 2 (by rfl) ⟨1433679, by rfl⟩ : syracuseStep 3823145 = 2867359) B2867359
theorem B2864767 : Blo 1697549 2864767 := bstep (se 1 (by rfl) ⟨2148575, by rfl⟩ : syracuseStep 2864767 = 4297151) B4297151
theorem B954021581 : Blo 1697549 954021581 := bstep (se 3 (by rfl) ⟨178879046, by rfl⟩ : syracuseStep 954021581 = 357758093) B357758093
theorem B4839193 : Blo 1697549 4839193 := bstep (se 2 (by rfl) ⟨1814697, by rfl⟩ : syracuseStep 4839193 = 3629395) B3629395
theorem B50345753 : Blo 1697549 50345753 := bstep (se 2 (by rfl) ⟨18879657, by rfl⟩ : syracuseStep 50345753 = 37759315) B37759315
theorem B2865017 : Blo 1697549 2865017 := bstep (se 2 (by rfl) ⟨1074381, by rfl⟩ : syracuseStep 2865017 = 2148763) B2148763
theorem B10336247 : Blo 1697549 10336247 := bstep (se 1 (by rfl) ⟨7752185, by rfl⟩ : syracuseStep 10336247 = 15504371) B15504371
theorem B19347659 : Blo 1697549 19347659 := bstep (se 1 (by rfl) ⟨14510744, by rfl⟩ : syracuseStep 19347659 = 29021489) B29021489
theorem B2865577 : Blo 1697549 2865577 := bstep (se 2 (by rfl) ⟨1074591, by rfl⟩ : syracuseStep 2865577 = 2149183) B2149183
theorem B2865631 : Blo 1697549 2865631 := bstep (se 1 (by rfl) ⟨2149223, by rfl⟩ : syracuseStep 2865631 = 4298447) B4298447
theorem B8600255 : Blo 1697549 8600255 := bstep (se 1 (by rfl) ⟨6450191, by rfl⟩ : syracuseStep 8600255 = 12900383) B12900383
theorem B3627755 : Blo 1697549 3627755 := bstep (se 1 (by rfl) ⟨2720816, by rfl⟩ : syracuseStep 3627755 = 5441633) B5441633
theorem B78445421 : Blo 1697549 78445421 := bstep (se 3 (by rfl) ⟨14708516, by rfl⟩ : syracuseStep 78445421 = 29417033) B29417033
theorem B4971385 : Blo 1697549 4971385 := bstep (se 2 (by rfl) ⟨1864269, by rfl⟩ : syracuseStep 4971385 = 3728539) B3728539
theorem B111713327 : Blo 1697549 111713327 := bstep (se 1 (by rfl) ⟨83784995, by rfl⟩ : syracuseStep 111713327 = 167569991) B167569991
theorem B9673991 : Blo 1697549 9673991 := bstep (se 1 (by rfl) ⟨7255493, by rfl⟩ : syracuseStep 9673991 = 14510987) B14510987
theorem B84909379 : Blo 1697549 84909379 := bstep (se 1 (by rfl) ⟨63682034, by rfl⟩ : syracuseStep 84909379 = 127364069) B127364069
theorem B8600903 : Blo 1697549 8600903 := bstep (se 1 (by rfl) ⟨6450677, by rfl⟩ : syracuseStep 8600903 = 12901355) B12901355
theorem B2547305 : Blo 1697549 2547305 := bstep (se 2 (by rfl) ⟨955239, by rfl⟩ : syracuseStep 2547305 = 1910479) B1910479
theorem B2547311 : Blo 1697549 2547311 := bstep (se 1 (by rfl) ⟨1910483, by rfl⟩ : syracuseStep 2547311 = 3820967) B3820967
theorem B2866927 : Blo 1697549 2866927 := bstep (se 1 (by rfl) ⟨2150195, by rfl⟩ : syracuseStep 2866927 = 4300391) B4300391
theorem B6446911 : Blo 1697549 6446911 := bstep (se 1 (by rfl) ⟨4835183, by rfl⟩ : syracuseStep 6446911 = 9670367) B9670367
theorem B12238715 : Blo 1697549 12238715 := bstep (se 1 (by rfl) ⟨9179036, by rfl⟩ : syracuseStep 12238715 = 18358073) B18358073
theorem B36741053 : Blo 1697549 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B8159219 : Blo 1697549 8159219 := bstep (se 1 (by rfl) ⟨6119414, by rfl⟩ : syracuseStep 8159219 = 12238829) B12238829
theorem B2548127 : Blo 1697549 2548127 := bstep (se 1 (by rfl) ⟨1911095, by rfl⟩ : syracuseStep 2548127 = 3822191) B3822191
theorem B2548607 : Blo 1697549 2548607 := bstep (se 1 (by rfl) ⟨1911455, by rfl⟩ : syracuseStep 2548607 = 3822911) B3822911
theorem B4301707 : Blo 1697549 4301707 := bstep (se 1 (by rfl) ⟨3226280, by rfl⟩ : syracuseStep 4301707 = 6452561) B6452561
theorem B2548763 : Blo 1697549 2548763 := bstep (se 1 (by rfl) ⟨1911572, by rfl⟩ : syracuseStep 2548763 = 3823145) B3823145
theorem B6628513 : Blo 1697549 6628513 := bstep (se 2 (by rfl) ⟨2485692, by rfl⟩ : syracuseStep 6628513 = 4971385) B4971385
theorem B2327735 : Blo 1697549 2327735 := bstep (se 1 (by rfl) ⟨1745801, by rfl⟩ : syracuseStep 2327735 = 3491603) B3491603
theorem B7259321 : Blo 1697549 7259321 := bstep (se 2 (by rfl) ⟨2722245, by rfl⟩ : syracuseStep 7259321 = 5444491) B5444491
theorem B8602847 : Blo 1697549 8602847 := bstep (se 1 (by rfl) ⟨6452135, by rfl⟩ : syracuseStep 8602847 = 12904271) B12904271
theorem B1910011 : Blo 1697549 1910011 := bstep (se 1 (by rfl) ⟨1432508, by rfl⟩ : syracuseStep 1910011 = 2865017) B2865017
theorem B6890831 : Blo 1697549 6890831 := bstep (se 1 (by rfl) ⟨5168123, by rfl⟩ : syracuseStep 6890831 = 10336247) B10336247
theorem B56583521 : Blo 1697549 56583521 := bstep (se 2 (by rfl) ⟨21218820, by rfl⟩ : syracuseStep 56583521 = 42437641) B42437641
theorem B21759353 : Blo 1697549 21759353 := bstep (se 2 (by rfl) ⟨8159757, by rfl⟩ : syracuseStep 21759353 = 16319515) B16319515
theorem B2418503 : Blo 1697549 2418503 := bstep (se 1 (by rfl) ⟨1813877, by rfl⟩ : syracuseStep 2418503 = 3627755) B3627755
theorem B74475551 : Blo 1697549 74475551 := bstep (se 1 (by rfl) ⟨55856663, by rfl⟩ : syracuseStep 74475551 = 111713327) B111713327
theorem B3819689 : Blo 1697549 3819689 := bstep (se 2 (by rfl) ⟨1432383, by rfl⟩ : syracuseStep 3819689 = 2864767) B2864767
theorem B6449327 : Blo 1697549 6449327 := bstep (se 1 (by rfl) ⟨4836995, by rfl⟩ : syracuseStep 6449327 = 9673991) B9673991
theorem B1698203 : Blo 1697549 1698203 := bstep (se 1 (by rfl) ⟨1273652, by rfl⟩ : syracuseStep 1698203 = 2547305) B2547305
theorem B1698207 : Blo 1697549 1698207 := bstep (se 1 (by rfl) ⟨1273655, by rfl⟩ : syracuseStep 1698207 = 2547311) B2547311
theorem B8595881 : Blo 1697549 8595881 := bstep (se 2 (by rfl) ⟨3223455, by rfl⟩ : syracuseStep 8595881 = 6446911) B6446911
theorem B5442299 : Blo 1697549 5442299 := bstep (se 1 (by rfl) ⟨4081724, by rfl⟩ : syracuseStep 5442299 = 8163449) B8163449
theorem B1698907 : Blo 1697549 1698907 := bstep (se 1 (by rfl) ⟨1274180, by rfl⟩ : syracuseStep 1698907 = 2548361) B2548361
theorem B9186479 : Blo 1697549 9186479 := bstep (se 1 (by rfl) ⟨6889859, by rfl⟩ : syracuseStep 9186479 = 13779719) B13779719
theorem B8596691 : Blo 1697549 8596691 := bstep (se 1 (by rfl) ⟨6447518, by rfl⟩ : syracuseStep 8596691 = 12895037) B12895037
theorem B3820769 : Blo 1697549 3820769 := bstep (se 2 (by rfl) ⟨1432788, by rfl⟩ : syracuseStep 3820769 = 2865577) B2865577
theorem B1699067 : Blo 1697549 1699067 := bstep (se 1 (by rfl) ⟨1274300, by rfl⟩ : syracuseStep 1699067 = 2548601) B2548601
theorem B3820841 : Blo 1697549 3820841 := bstep (se 2 (by rfl) ⟨1432815, by rfl⟩ : syracuseStep 3820841 = 2865631) B2865631
theorem B2149735 : Blo 1697549 2149735 := bstep (se 1 (by rfl) ⟨1612301, by rfl⟩ : syracuseStep 2149735 = 3224603) B3224603
theorem B1699263 : Blo 1697549 1699263 := bstep (se 1 (by rfl) ⟨1274447, by rfl⟩ : syracuseStep 1699263 = 2548895) B2548895
theorem B21753359 : Blo 1697549 21753359 := bstep (se 1 (by rfl) ⟨16315019, by rfl⟩ : syracuseStep 21753359 = 32630039) B32630039
theorem B3821147 : Blo 1697549 3821147 := bstep (se 1 (by rfl) ⟨2865860, by rfl⟩ : syracuseStep 3821147 = 5731721) B5731721
theorem B3444329 : Blo 1697549 3444329 := bstep (se 2 (by rfl) ⟨1291623, by rfl⟩ : syracuseStep 3444329 = 2583247) B2583247
theorem B636014387 : Blo 1697549 636014387 := bstep (se 1 (by rfl) ⟨477010790, by rfl⟩ : syracuseStep 636014387 = 954021581) B954021581
theorem B3223547 : Blo 1697549 3223547 := bstep (se 1 (by rfl) ⟨2417660, by rfl⟩ : syracuseStep 3223547 = 4835321) B4835321
theorem B12898439 : Blo 1697549 12898439 := bstep (se 1 (by rfl) ⟨9673829, by rfl⟩ : syracuseStep 12898439 = 19347659) B19347659
theorem B66179261 : Blo 1697549 66179261 := bstep (se 3 (by rfl) ⟨12408611, by rfl⟩ : syracuseStep 66179261 = 24817223) B24817223
theorem B12898925 : Blo 1697549 12898925 := bstep (se 3 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 12898925 = 4837097) B4837097
theorem B134255341 : Blo 1697549 134255341 := bstep (se 3 (by rfl) ⟨25172876, by rfl⟩ : syracuseStep 134255341 = 50345753) B50345753
theorem B3822569 : Blo 1697549 3822569 := bstep (se 2 (by rfl) ⟨1433463, by rfl⟩ : syracuseStep 3822569 = 2866927) B2866927
theorem B6452257 : Blo 1697549 6452257 := bstep (se 2 (by rfl) ⟨2419596, by rfl⟩ : syracuseStep 6452257 = 4839193) B4839193
theorem B5731667 : Blo 1697549 5731667 := bstep (se 1 (by rfl) ⟨4298750, by rfl⟩ : syracuseStep 5731667 = 8597501) B8597501
theorem B3823055 : Blo 1697549 3823055 := bstep (se 1 (by rfl) ⟨2867291, by rfl⟩ : syracuseStep 3823055 = 5734583) B5734583
theorem B5732207 : Blo 1697549 5732207 := bstep (se 1 (by rfl) ⟨4299155, by rfl⟩ : syracuseStep 5732207 = 8598311) B8598311
theorem B3823595 : Blo 1697549 3823595 := bstep (se 1 (by rfl) ⟨2867696, by rfl⟩ : syracuseStep 3823595 = 5735393) B5735393
theorem B2865179 : Blo 1697549 2865179 := bstep (se 1 (by rfl) ⟨2148884, by rfl⟩ : syracuseStep 2865179 = 4297769) B4297769
theorem B2865199 : Blo 1697549 2865199 := bstep (se 1 (by rfl) ⟨2148899, by rfl⟩ : syracuseStep 2865199 = 4297799) B4297799
theorem B5732423 : Blo 1697549 5732423 := bstep (se 1 (by rfl) ⟨4299317, by rfl⟩ : syracuseStep 5732423 = 8598635) B8598635
theorem B5732477 : Blo 1697549 5732477 := bstep (se 3 (by rfl) ⟨1074839, by rfl⟩ : syracuseStep 5732477 = 2149679) B2149679
theorem B17423009 : Blo 1697549 17423009 := bstep (se 2 (by rfl) ⟨6533628, by rfl⟩ : syracuseStep 17423009 = 13067257) B13067257
theorem B2546411 : Blo 1697549 2546411 := bstep (se 1 (by rfl) ⟨1909808, by rfl⟩ : syracuseStep 2546411 = 3819617) B3819617
theorem B24492881 : Blo 1697549 24492881 := bstep (se 2 (by rfl) ⟨9184830, by rfl⟩ : syracuseStep 24492881 = 18369661) B18369661
theorem B113212505 : Blo 1697549 113212505 := bstep (se 2 (by rfl) ⟨42454689, by rfl⟩ : syracuseStep 113212505 = 84909379) B84909379
theorem B2546783 : Blo 1697549 2546783 := bstep (se 1 (by rfl) ⟨1910087, by rfl⟩ : syracuseStep 2546783 = 3820175) B3820175
theorem B5733503 : Blo 1697549 5733503 := bstep (se 1 (by rfl) ⟨4300127, by rfl⟩ : syracuseStep 5733503 = 8600255) B8600255
theorem B16325819 : Blo 1697549 16325819 := bstep (se 1 (by rfl) ⟨12244364, by rfl⟩ : syracuseStep 16325819 = 24488729) B24488729
theorem B52296947 : Blo 1697549 52296947 := bstep (se 1 (by rfl) ⟨39222710, by rfl⟩ : syracuseStep 52296947 = 78445421) B78445421
theorem B5733935 : Blo 1697549 5733935 := bstep (se 1 (by rfl) ⟨4300451, by rfl⟩ : syracuseStep 5733935 = 8600903) B8600903
theorem B31415971 : Blo 1697549 31415971 := bstep (se 1 (by rfl) ⟨23561978, by rfl⟩ : syracuseStep 31415971 = 47123957) B47123957
theorem B2547593 : Blo 1697549 2547593 := bstep (se 2 (by rfl) ⟨955347, by rfl⟩ : syracuseStep 2547593 = 1910695) B1910695
theorem B8159143 : Blo 1697549 8159143 := bstep (se 1 (by rfl) ⟨6119357, by rfl⟩ : syracuseStep 8159143 = 12238715) B12238715
theorem B24494035 : Blo 1697549 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B5439479 : Blo 1697549 5439479 := bstep (se 1 (by rfl) ⟨4079609, by rfl⟩ : syracuseStep 5439479 = 8159219) B8159219
theorem B2548379 : Blo 1697549 2548379 := bstep (se 1 (by rfl) ⟨1911284, by rfl⟩ : syracuseStep 2548379 = 3822569) B3822569
theorem B5735231 : Blo 1697549 5735231 := bstep (se 1 (by rfl) ⟨4301423, by rfl⟩ : syracuseStep 5735231 = 8602847) B8602847
theorem B2548703 : Blo 1697549 2548703 := bstep (se 1 (by rfl) ⟨1911527, by rfl⟩ : syracuseStep 2548703 = 3823055) B3823055
theorem B5735609 : Blo 1697549 5735609 := bstep (se 2 (by rfl) ⟨2150853, by rfl⟩ : syracuseStep 5735609 = 4301707) B4301707
theorem B2549063 : Blo 1697549 2549063 := bstep (se 1 (by rfl) ⟨1911797, by rfl⟩ : syracuseStep 2549063 = 3823595) B3823595
theorem B1910119 : Blo 1697549 1910119 := bstep (se 1 (by rfl) ⟨1432589, by rfl⟩ : syracuseStep 1910119 = 2865179) B2865179
theorem B8603009 : Blo 1697549 8603009 := bstep (se 2 (by rfl) ⟨3226128, by rfl⟩ : syracuseStep 8603009 = 6452257) B6452257
theorem B9184877 : Blo 1697549 9184877 := bstep (se 3 (by rfl) ⟨1722164, by rfl⟩ : syracuseStep 9184877 = 3444329) B3444329
theorem B1697607 : Blo 1697549 1697607 := bstep (se 1 (by rfl) ⟨1273205, by rfl⟩ : syracuseStep 1697607 = 2546411) B2546411
theorem B16328587 : Blo 1697549 16328587 := bstep (se 1 (by rfl) ⟨12246440, by rfl⟩ : syracuseStep 16328587 = 24492881) B24492881
theorem B75475003 : Blo 1697549 75475003 := bstep (se 1 (by rfl) ⟨56606252, by rfl⟩ : syracuseStep 75475003 = 113212505) B113212505
theorem B1697855 : Blo 1697549 1697855 := bstep (se 1 (by rfl) ⟨1273391, by rfl⟩ : syracuseStep 1697855 = 2546783) B2546783
theorem B6449341 : Blo 1697549 6449341 := bstep (se 3 (by rfl) ⟨1209251, by rfl⟩ : syracuseStep 6449341 = 2418503) B2418503
theorem B41887961 : Blo 1697549 41887961 := bstep (se 2 (by rfl) ⟨15707985, by rfl⟩ : syracuseStep 41887961 = 31415971) B31415971
theorem B14502239 : Blo 1697549 14502239 := bstep (se 1 (by rfl) ⟨10876679, by rfl⟩ : syracuseStep 14502239 = 21753359) B21753359
theorem B1698395 : Blo 1697549 1698395 := bstep (se 1 (by rfl) ⟨1273796, by rfl⟩ : syracuseStep 1698395 = 2547593) B2547593
theorem B2149031 : Blo 1697549 2149031 := bstep (se 1 (by rfl) ⟨1611773, by rfl⟩ : syracuseStep 2149031 = 3223547) B3223547
theorem B3820265 : Blo 1697549 3820265 := bstep (se 2 (by rfl) ⟨1432599, by rfl⟩ : syracuseStep 3820265 = 2865199) B2865199
theorem B1698751 : Blo 1697549 1698751 := bstep (se 1 (by rfl) ⟨1274063, by rfl⟩ : syracuseStep 1698751 = 2548127) B2548127
theorem B1699071 : Blo 1697549 1699071 := bstep (se 1 (by rfl) ⟨1274303, by rfl⟩ : syracuseStep 1699071 = 2548607) B2548607
theorem B1699175 : Blo 1697549 1699175 := bstep (se 1 (by rfl) ⟨1274381, by rfl⟩ : syracuseStep 1699175 = 2548763) B2548763
theorem B3821111 : Blo 1697549 3821111 := bstep (se 1 (by rfl) ⟨2865833, by rfl⟩ : syracuseStep 3821111 = 5731667) B5731667
theorem B179007121 : Blo 1697549 179007121 := bstep (se 2 (by rfl) ⟨67127670, by rfl⟩ : syracuseStep 179007121 = 134255341) B134255341
theorem B3821471 : Blo 1697549 3821471 := bstep (se 1 (by rfl) ⟨2866103, by rfl⟩ : syracuseStep 3821471 = 5732207) B5732207
theorem B3821615 : Blo 1697549 3821615 := bstep (se 1 (by rfl) ⟨2866211, by rfl⟩ : syracuseStep 3821615 = 5732423) B5732423
theorem B3821651 : Blo 1697549 3821651 := bstep (se 1 (by rfl) ⟨2866238, by rfl⟩ : syracuseStep 3821651 = 5732477) B5732477
theorem B5730587 : Blo 1697549 5730587 := bstep (se 1 (by rfl) ⟨4297940, by rfl⟩ : syracuseStep 5730587 = 8595881) B8595881
theorem B3822335 : Blo 1697549 3822335 := bstep (se 1 (by rfl) ⟨2866751, by rfl⟩ : syracuseStep 3822335 = 5733503) B5733503
theorem B6124319 : Blo 1697549 6124319 := bstep (se 1 (by rfl) ⟨4593239, by rfl⟩ : syracuseStep 6124319 = 9186479) B9186479
theorem B10883879 : Blo 1697549 10883879 := bstep (se 1 (by rfl) ⟨8162909, by rfl⟩ : syracuseStep 10883879 = 16325819) B16325819
theorem B5731127 : Blo 1697549 5731127 := bstep (se 1 (by rfl) ⟨4298345, by rfl⟩ : syracuseStep 5731127 = 8596691) B8596691
theorem B3822623 : Blo 1697549 3822623 := bstep (se 1 (by rfl) ⟨2866967, by rfl⟩ : syracuseStep 3822623 = 5733935) B5733935
theorem B32658713 : Blo 1697549 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B14505277 : Blo 1697549 14505277 := bstep (se 3 (by rfl) ⟨2719739, by rfl⟩ : syracuseStep 14505277 = 5439479) B5439479
theorem B8598959 : Blo 1697549 8598959 := bstep (se 1 (by rfl) ⟨6449219, by rfl⟩ : syracuseStep 8598959 = 12898439) B12898439
theorem B8599283 : Blo 1697549 8599283 := bstep (se 1 (by rfl) ⟨6449462, by rfl⟩ : syracuseStep 8599283 = 12898925) B12898925
theorem B6207293 : Blo 1697549 6207293 := bstep (se 3 (by rfl) ⟨1163867, by rfl⟩ : syracuseStep 6207293 = 2327735) B2327735
theorem B176478029 : Blo 1697549 176478029 := bstep (se 3 (by rfl) ⟨33089630, by rfl⟩ : syracuseStep 176478029 = 66179261) B66179261
theorem B4839547 : Blo 1697549 4839547 := bstep (se 1 (by rfl) ⟨3629660, by rfl⟩ : syracuseStep 4839547 = 7259321) B7259321
theorem B4593887 : Blo 1697549 4593887 := bstep (se 1 (by rfl) ⟨3445415, by rfl⟩ : syracuseStep 4593887 = 6890831) B6890831
theorem B37722347 : Blo 1697549 37722347 := bstep (se 1 (by rfl) ⟨28291760, by rfl⟩ : syracuseStep 37722347 = 56583521) B56583521
theorem B14506235 : Blo 1697549 14506235 := bstep (se 1 (by rfl) ⟨10879676, by rfl⟩ : syracuseStep 14506235 = 21759353) B21759353
theorem B49650367 : Blo 1697549 49650367 := bstep (se 1 (by rfl) ⟨37237775, by rfl⟩ : syracuseStep 49650367 = 74475551) B74475551
theorem B2546459 : Blo 1697549 2546459 := bstep (se 1 (by rfl) ⟨1909844, by rfl⟩ : syracuseStep 2546459 = 3819689) B3819689
theorem B4299551 : Blo 1697549 4299551 := bstep (se 1 (by rfl) ⟨3224663, by rfl⟩ : syracuseStep 4299551 = 6449327) B6449327
theorem B8838017 : Blo 1697549 8838017 := bstep (se 2 (by rfl) ⟨3314256, by rfl⟩ : syracuseStep 8838017 = 6628513) B6628513
theorem B2546681 : Blo 1697549 2546681 := bstep (se 2 (by rfl) ⟨955005, by rfl⟩ : syracuseStep 2546681 = 1910011) B1910011
theorem B11615339 : Blo 1697549 11615339 := bstep (se 1 (by rfl) ⟨8711504, by rfl⟩ : syracuseStep 11615339 = 17423009) B17423009
theorem B2866313 : Blo 1697549 2866313 := bstep (se 2 (by rfl) ⟨1074867, by rfl⟩ : syracuseStep 2866313 = 2149735) B2149735
theorem B3628199 : Blo 1697549 3628199 := bstep (se 1 (by rfl) ⟨2721149, by rfl⟩ : syracuseStep 3628199 = 5442299) B5442299
theorem B1696038365 : Blo 1697549 1696038365 := bstep (se 3 (by rfl) ⟨318007193, by rfl⟩ : syracuseStep 1696038365 = 636014387) B636014387
theorem B2547179 : Blo 1697549 2547179 := bstep (se 1 (by rfl) ⟨1910384, by rfl⟩ : syracuseStep 2547179 = 3820769) B3820769
theorem B34864631 : Blo 1697549 34864631 := bstep (se 1 (by rfl) ⟨26148473, by rfl⟩ : syracuseStep 34864631 = 52296947) B52296947
theorem B2547227 : Blo 1697549 2547227 := bstep (se 1 (by rfl) ⟨1910420, by rfl⟩ : syracuseStep 2547227 = 3820841) B3820841
theorem B2547431 : Blo 1697549 2547431 := bstep (se 1 (by rfl) ⟨1910573, by rfl⟩ : syracuseStep 2547431 = 3821147) B3821147
theorem B10878857 : Blo 1697549 10878857 := bstep (se 2 (by rfl) ⟨4079571, by rfl⟩ : syracuseStep 10878857 = 8159143) B8159143
theorem B2547743 : Blo 1697549 2547743 := bstep (se 1 (by rfl) ⟨1910807, by rfl⟩ : syracuseStep 2547743 = 3821615) B3821615
theorem B2547767 : Blo 1697549 2547767 := bstep (se 1 (by rfl) ⟨1910825, by rfl⟩ : syracuseStep 2547767 = 3821651) B3821651
theorem B9675197 : Blo 1697549 9675197 := bstep (se 3 (by rfl) ⟨1814099, by rfl⟩ : syracuseStep 9675197 = 3628199) B3628199
theorem B2548223 : Blo 1697549 2548223 := bstep (se 1 (by rfl) ⟨1911167, by rfl⟩ : syracuseStep 2548223 = 3822335) B3822335
theorem B2548415 : Blo 1697549 2548415 := bstep (se 1 (by rfl) ⟨1911311, by rfl⟩ : syracuseStep 2548415 = 3822623) B3822623
theorem B66200489 : Blo 1697549 66200489 := bstep (se 2 (by rfl) ⟨24825183, by rfl⟩ : syracuseStep 66200489 = 49650367) B49650367
theorem B5735339 : Blo 1697549 5735339 := bstep (se 1 (by rfl) ⟨4301504, by rfl⟩ : syracuseStep 5735339 = 8603009) B8603009
theorem B9668159 : Blo 1697549 9668159 := bstep (se 1 (by rfl) ⟨7251119, by rfl⟩ : syracuseStep 9668159 = 14502239) B14502239
theorem B1697639 : Blo 1697549 1697639 := bstep (se 1 (by rfl) ⟨1273229, by rfl⟩ : syracuseStep 1697639 = 2546459) B2546459
theorem B5892011 : Blo 1697549 5892011 := bstep (se 1 (by rfl) ⟨4419008, by rfl⟩ : syracuseStep 5892011 = 8838017) B8838017
theorem B1697787 : Blo 1697549 1697787 := bstep (se 1 (by rfl) ⟨1273340, by rfl⟩ : syracuseStep 1697787 = 2546681) B2546681
theorem B7743559 : Blo 1697549 7743559 := bstep (se 1 (by rfl) ⟨5807669, by rfl⟩ : syracuseStep 7743559 = 11615339) B11615339
theorem B1910875 : Blo 1697549 1910875 := bstep (se 1 (by rfl) ⟨1433156, by rfl⟩ : syracuseStep 1910875 = 2866313) B2866313
theorem B238676161 : Blo 1697549 238676161 := bstep (se 2 (by rfl) ⟨89503560, by rfl⟩ : syracuseStep 238676161 = 179007121) B179007121
theorem B1698119 : Blo 1697549 1698119 := bstep (se 1 (by rfl) ⟨1273589, by rfl⟩ : syracuseStep 1698119 = 2547179) B2547179
theorem B23243087 : Blo 1697549 23243087 := bstep (se 1 (by rfl) ⟨17432315, by rfl⟩ : syracuseStep 23243087 = 34864631) B34864631
theorem B1698151 : Blo 1697549 1698151 := bstep (se 1 (by rfl) ⟨1273613, by rfl⟩ : syracuseStep 1698151 = 2547227) B2547227
theorem B1698287 : Blo 1697549 1698287 := bstep (se 1 (by rfl) ⟨1273715, by rfl⟩ : syracuseStep 1698287 = 2547431) B2547431
theorem B7252571 : Blo 1697549 7252571 := bstep (se 1 (by rfl) ⟨5439428, by rfl⟩ : syracuseStep 7252571 = 10878857) B10878857
theorem B100633337 : Blo 1697549 100633337 := bstep (se 2 (by rfl) ⟨37737501, by rfl⟩ : syracuseStep 100633337 = 75475003) B75475003
theorem B3820391 : Blo 1697549 3820391 := bstep (se 1 (by rfl) ⟨2865293, by rfl⟩ : syracuseStep 3820391 = 5730587) B5730587
theorem B1698919 : Blo 1697549 1698919 := bstep (se 1 (by rfl) ⟨1274189, by rfl⟩ : syracuseStep 1698919 = 2548379) B2548379
theorem B4082879 : Blo 1697549 4082879 := bstep (se 1 (by rfl) ⟨3062159, by rfl⟩ : syracuseStep 4082879 = 6124319) B6124319
theorem B3820751 : Blo 1697549 3820751 := bstep (se 1 (by rfl) ⟨2865563, by rfl⟩ : syracuseStep 3820751 = 5731127) B5731127
theorem B1699135 : Blo 1697549 1699135 := bstep (se 1 (by rfl) ⟨1274351, by rfl⟩ : syracuseStep 1699135 = 2548703) B2548703
theorem B1699375 : Blo 1697549 1699375 := bstep (se 1 (by rfl) ⟨1274531, by rfl⟩ : syracuseStep 1699375 = 2549063) B2549063
theorem B6123251 : Blo 1697549 6123251 := bstep (se 1 (by rfl) ⟨4592438, by rfl⟩ : syracuseStep 6123251 = 9184877) B9184877
theorem B9670823 : Blo 1697549 9670823 := bstep (se 1 (by rfl) ⟨7253117, by rfl⟩ : syracuseStep 9670823 = 14506235) B14506235
theorem B5730749 : Blo 1697549 5730749 := bstep (se 3 (by rfl) ⟨1074515, by rfl⟩ : syracuseStep 5730749 = 2149031) B2149031
theorem B16552781 : Blo 1697549 16552781 := bstep (se 3 (by rfl) ⟨3103646, by rfl⟩ : syracuseStep 16552781 = 6207293) B6207293
theorem B21771449 : Blo 1697549 21771449 := bstep (se 2 (by rfl) ⟨8164293, by rfl⟩ : syracuseStep 21771449 = 16328587) B16328587
theorem B6452729 : Blo 1697549 6452729 := bstep (se 2 (by rfl) ⟨2419773, by rfl⟩ : syracuseStep 6452729 = 4839547) B4839547
theorem B8599121 : Blo 1697549 8599121 := bstep (se 2 (by rfl) ⟨3224670, by rfl⟩ : syracuseStep 8599121 = 6449341) B6449341
theorem B7255919 : Blo 1697549 7255919 := bstep (se 1 (by rfl) ⟨5441939, by rfl⟩ : syracuseStep 7255919 = 10883879) B10883879
theorem B3823487 : Blo 1697549 3823487 := bstep (se 1 (by rfl) ⟨2867615, by rfl⟩ : syracuseStep 3823487 = 5735231) B5735231
theorem B3823739 : Blo 1697549 3823739 := bstep (se 1 (by rfl) ⟨2867804, by rfl⟩ : syracuseStep 3823739 = 5735609) B5735609
theorem B21772475 : Blo 1697549 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B5732639 : Blo 1697549 5732639 := bstep (se 1 (by rfl) ⟨4299479, by rfl⟩ : syracuseStep 5732639 = 8598959) B8598959
theorem B5732855 : Blo 1697549 5732855 := bstep (se 1 (by rfl) ⟨4299641, by rfl⟩ : syracuseStep 5732855 = 8599283) B8599283
theorem B117652019 : Blo 1697549 117652019 := bstep (se 1 (by rfl) ⟨88239014, by rfl⟩ : syracuseStep 117652019 = 176478029) B176478029
theorem B27925307 : Blo 1697549 27925307 := bstep (se 1 (by rfl) ⟨20943980, by rfl⟩ : syracuseStep 27925307 = 41887961) B41887961
theorem B3062591 : Blo 1697549 3062591 := bstep (se 1 (by rfl) ⟨2296943, by rfl⟩ : syracuseStep 3062591 = 4593887) B4593887
theorem B25148231 : Blo 1697549 25148231 := bstep (se 1 (by rfl) ⟨18861173, by rfl⟩ : syracuseStep 25148231 = 37722347) B37722347
theorem B19340369 : Blo 1697549 19340369 := bstep (se 2 (by rfl) ⟨7252638, by rfl⟩ : syracuseStep 19340369 = 14505277) B14505277
theorem B2546825 : Blo 1697549 2546825 := bstep (se 2 (by rfl) ⟨955059, by rfl⟩ : syracuseStep 2546825 = 1910119) B1910119
theorem B2546843 : Blo 1697549 2546843 := bstep (se 1 (by rfl) ⟨1910132, by rfl⟩ : syracuseStep 2546843 = 3820265) B3820265
theorem B2866367 : Blo 1697549 2866367 := bstep (se 1 (by rfl) ⟨2149775, by rfl⟩ : syracuseStep 2866367 = 4299551) B4299551
theorem B1130692243 : Blo 1697549 1130692243 := bstep (se 1 (by rfl) ⟨848019182, by rfl⟩ : syracuseStep 1130692243 = 1696038365) B1696038365
theorem B2547407 : Blo 1697549 2547407 := bstep (se 1 (by rfl) ⟨1910555, by rfl⟩ : syracuseStep 2547407 = 3821111) B3821111
theorem B2547647 : Blo 1697549 2547647 := bstep (se 1 (by rfl) ⟨1910735, by rfl⟩ : syracuseStep 2547647 = 3821471) B3821471
theorem B6447215 : Blo 1697549 6447215 := bstep (se 1 (by rfl) ⟨4835411, by rfl⟩ : syracuseStep 6447215 = 9670823) B9670823
theorem B2547833 : Blo 1697549 2547833 := bstep (se 2 (by rfl) ⟨955437, by rfl⟩ : syracuseStep 2547833 = 1910875) B1910875
theorem B318234881 : Blo 1697549 318234881 := bstep (se 2 (by rfl) ⟨119338080, by rfl⟩ : syracuseStep 318234881 = 238676161) B238676161
theorem B11035187 : Blo 1697549 11035187 := bstep (se 1 (by rfl) ⟨8276390, by rfl⟩ : syracuseStep 11035187 = 16552781) B16552781
theorem B4301819 : Blo 1697549 4301819 := bstep (se 1 (by rfl) ⟨3226364, by rfl⟩ : syracuseStep 4301819 = 6452729) B6452729
theorem B2548991 : Blo 1697549 2548991 := bstep (se 1 (by rfl) ⟨1911743, by rfl⟩ : syracuseStep 2548991 = 3823487) B3823487
theorem B2549159 : Blo 1697549 2549159 := bstep (se 1 (by rfl) ⟨1911869, by rfl⟩ : syracuseStep 2549159 = 3823739) B3823739
theorem B313738717 : Blo 1697549 313738717 := bstep (se 3 (by rfl) ⟨58826009, by rfl⟩ : syracuseStep 313738717 = 117652019) B117652019
theorem B4835047 : Blo 1697549 4835047 := bstep (se 1 (by rfl) ⟨3626285, by rfl⟩ : syracuseStep 4835047 = 7252571) B7252571
theorem B2041727 : Blo 1697549 2041727 := bstep (se 1 (by rfl) ⟨1531295, by rfl⟩ : syracuseStep 2041727 = 3062591) B3062591
theorem B1697883 : Blo 1697549 1697883 := bstep (se 1 (by rfl) ⟨1273412, by rfl⟩ : syracuseStep 1697883 = 2546825) B2546825
theorem B1697895 : Blo 1697549 1697895 := bstep (se 1 (by rfl) ⟨1273421, by rfl⟩ : syracuseStep 1697895 = 2546843) B2546843
theorem B1910911 : Blo 1697549 1910911 := bstep (se 1 (by rfl) ⟨1433183, by rfl⟩ : syracuseStep 1910911 = 2866367) B2866367
theorem B2721919 : Blo 1697549 2721919 := bstep (se 1 (by rfl) ⟨2041439, by rfl⟩ : syracuseStep 2721919 = 4082879) B4082879
theorem B1698271 : Blo 1697549 1698271 := bstep (se 1 (by rfl) ⟨1273703, by rfl⟩ : syracuseStep 1698271 = 2547407) B2547407
theorem B4082167 : Blo 1697549 4082167 := bstep (se 1 (by rfl) ⟨3061625, by rfl⟩ : syracuseStep 4082167 = 6123251) B6123251
theorem B1698431 : Blo 1697549 1698431 := bstep (se 1 (by rfl) ⟨1273823, by rfl⟩ : syracuseStep 1698431 = 2547647) B2547647
theorem B1698495 : Blo 1697549 1698495 := bstep (se 1 (by rfl) ⟨1273871, by rfl⟩ : syracuseStep 1698495 = 2547743) B2547743
theorem B1698511 : Blo 1697549 1698511 := bstep (se 1 (by rfl) ⟨1273883, by rfl⟩ : syracuseStep 1698511 = 2547767) B2547767
theorem B10324745 : Blo 1697549 10324745 := bstep (se 2 (by rfl) ⟨3871779, by rfl⟩ : syracuseStep 10324745 = 7743559) B7743559
theorem B3820499 : Blo 1697549 3820499 := bstep (se 1 (by rfl) ⟨2865374, by rfl⟩ : syracuseStep 3820499 = 5730749) B5730749
theorem B6450131 : Blo 1697549 6450131 := bstep (se 1 (by rfl) ⟨4837598, by rfl⟩ : syracuseStep 6450131 = 9675197) B9675197
theorem B1698815 : Blo 1697549 1698815 := bstep (se 1 (by rfl) ⟨1274111, by rfl⟩ : syracuseStep 1698815 = 2548223) B2548223
theorem B1698943 : Blo 1697549 1698943 := bstep (se 1 (by rfl) ⟨1274207, by rfl⟩ : syracuseStep 1698943 = 2548415) B2548415
theorem B44133659 : Blo 1697549 44133659 := bstep (se 1 (by rfl) ⟨33100244, by rfl⟩ : syracuseStep 44133659 = 66200489) B66200489
theorem B3928007 : Blo 1697549 3928007 := bstep (se 1 (by rfl) ⟨2946005, by rfl⟩ : syracuseStep 3928007 = 5892011) B5892011
theorem B3821759 : Blo 1697549 3821759 := bstep (se 1 (by rfl) ⟨2866319, by rfl⟩ : syracuseStep 3821759 = 5732639) B5732639
theorem B15495391 : Blo 1697549 15495391 := bstep (se 1 (by rfl) ⟨11621543, by rfl⟩ : syracuseStep 15495391 = 23243087) B23243087
theorem B3821903 : Blo 1697549 3821903 := bstep (se 1 (by rfl) ⟨2866427, by rfl⟩ : syracuseStep 3821903 = 5732855) B5732855
theorem B67088891 : Blo 1697549 67088891 := bstep (se 1 (by rfl) ⟨50316668, by rfl⟩ : syracuseStep 67088891 = 100633337) B100633337
theorem B18616871 : Blo 1697549 18616871 := bstep (se 1 (by rfl) ⟨13962653, by rfl⟩ : syracuseStep 18616871 = 27925307) B27925307
theorem B16765487 : Blo 1697549 16765487 := bstep (se 1 (by rfl) ⟨12574115, by rfl⟩ : syracuseStep 16765487 = 25148231) B25148231
theorem B3823559 : Blo 1697549 3823559 := bstep (se 1 (by rfl) ⟨2867669, by rfl⟩ : syracuseStep 3823559 = 5735339) B5735339
theorem B14514299 : Blo 1697549 14514299 := bstep (se 1 (by rfl) ⟨10885724, by rfl⟩ : syracuseStep 14514299 = 21771449) B21771449
theorem B6445439 : Blo 1697549 6445439 := bstep (se 1 (by rfl) ⟨4834079, by rfl⟩ : syracuseStep 6445439 = 9668159) B9668159
theorem B5732747 : Blo 1697549 5732747 := bstep (se 1 (by rfl) ⟨4299560, by rfl⟩ : syracuseStep 5732747 = 8599121) B8599121
theorem B14514983 : Blo 1697549 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B2546927 : Blo 1697549 2546927 := bstep (se 1 (by rfl) ⟨1910195, by rfl⟩ : syracuseStep 2546927 = 3820391) B3820391
theorem B12893579 : Blo 1697549 12893579 := bstep (se 1 (by rfl) ⟨9670184, by rfl⟩ : syracuseStep 12893579 = 19340369) B19340369
theorem B2547167 : Blo 1697549 2547167 := bstep (se 1 (by rfl) ⟨1910375, by rfl⟩ : syracuseStep 2547167 = 3820751) B3820751
theorem B1507589657 : Blo 1697549 1507589657 := bstep (se 2 (by rfl) ⟨565346121, by rfl⟩ : syracuseStep 1507589657 = 1130692243) B1130692243
theorem B19349117 : Blo 1697549 19349117 := bstep (se 3 (by rfl) ⟨3627959, by rfl⟩ : syracuseStep 19349117 = 7255919) B7255919
theorem B2547839 : Blo 1697549 2547839 := bstep (se 1 (by rfl) ⟨1910879, by rfl⟩ : syracuseStep 2547839 = 3821759) B3821759
theorem B2547881 : Blo 1697549 2547881 := bstep (se 2 (by rfl) ⟨955455, by rfl⟩ : syracuseStep 2547881 = 1910911) B1910911
theorem B3629225 : Blo 1697549 3629225 := bstep (se 2 (by rfl) ⟨1360959, by rfl⟩ : syracuseStep 3629225 = 2721919) B2721919
theorem B212156587 : Blo 1697549 212156587 := bstep (se 1 (by rfl) ⟨159117440, by rfl⟩ : syracuseStep 212156587 = 318234881) B318234881
theorem B2547935 : Blo 1697549 2547935 := bstep (se 1 (by rfl) ⟨1910951, by rfl⟩ : syracuseStep 2547935 = 3821903) B3821903
theorem B20660521 : Blo 1697549 20660521 := bstep (se 2 (by rfl) ⟨7747695, by rfl⟩ : syracuseStep 20660521 = 15495391) B15495391
theorem B12411247 : Blo 1697549 12411247 := bstep (se 1 (by rfl) ⟨9308435, by rfl⟩ : syracuseStep 12411247 = 18616871) B18616871
theorem B7356791 : Blo 1697549 7356791 := bstep (se 1 (by rfl) ⟨5517593, by rfl⟩ : syracuseStep 7356791 = 11035187) B11035187
theorem B2867879 : Blo 1697549 2867879 := bstep (se 1 (by rfl) ⟨2150909, by rfl⟩ : syracuseStep 2867879 = 4301819) B4301819
theorem B2549039 : Blo 1697549 2549039 := bstep (se 1 (by rfl) ⟨1911779, by rfl⟩ : syracuseStep 2549039 = 3823559) B3823559
theorem B9676199 : Blo 1697549 9676199 := bstep (se 1 (by rfl) ⟨7257149, by rfl⟩ : syracuseStep 9676199 = 14514299) B14514299
theorem B6883163 : Blo 1697549 6883163 := bstep (se 1 (by rfl) ⟨5162372, by rfl⟩ : syracuseStep 6883163 = 10324745) B10324745
theorem B9676655 : Blo 1697549 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B418318289 : Blo 1697549 418318289 := bstep (se 2 (by rfl) ⟨156869358, by rfl⟩ : syracuseStep 418318289 = 313738717) B313738717
theorem B1697951 : Blo 1697549 1697951 := bstep (se 1 (by rfl) ⟨1273463, by rfl⟩ : syracuseStep 1697951 = 2546927) B2546927
theorem B8595719 : Blo 1697549 8595719 := bstep (se 1 (by rfl) ⟨6446789, by rfl⟩ : syracuseStep 8595719 = 12893579) B12893579
theorem B1698111 : Blo 1697549 1698111 := bstep (se 1 (by rfl) ⟨1273583, by rfl⟩ : syracuseStep 1698111 = 2547167) B2547167
theorem B1698555 : Blo 1697549 1698555 := bstep (se 1 (by rfl) ⟨1273916, by rfl⟩ : syracuseStep 1698555 = 2547833) B2547833
theorem B11176991 : Blo 1697549 11176991 := bstep (se 1 (by rfl) ⟨8382743, by rfl⟩ : syracuseStep 11176991 = 16765487) B16765487
theorem B5442889 : Blo 1697549 5442889 := bstep (se 2 (by rfl) ⟨2041083, by rfl⟩ : syracuseStep 5442889 = 4082167) B4082167
theorem B1699327 : Blo 1697549 1699327 := bstep (se 1 (by rfl) ⟨1274495, by rfl⟩ : syracuseStep 1699327 = 2548991) B2548991
theorem B1699439 : Blo 1697549 1699439 := bstep (se 1 (by rfl) ⟨1274579, by rfl⟩ : syracuseStep 1699439 = 2549159) B2549159
theorem B4296959 : Blo 1697549 4296959 := bstep (se 1 (by rfl) ⟨3222719, by rfl⟩ : syracuseStep 4296959 = 6445439) B6445439
theorem B3821831 : Blo 1697549 3821831 := bstep (se 1 (by rfl) ⟨2866373, by rfl⟩ : syracuseStep 3821831 = 5732747) B5732747
theorem B29422439 : Blo 1697549 29422439 := bstep (se 1 (by rfl) ⟨22066829, by rfl⟩ : syracuseStep 29422439 = 44133659) B44133659
theorem B5444605 : Blo 1697549 5444605 := bstep (se 3 (by rfl) ⟨1020863, by rfl⟩ : syracuseStep 5444605 = 2041727) B2041727
theorem B12899411 : Blo 1697549 12899411 := bstep (se 1 (by rfl) ⟨9674558, by rfl⟩ : syracuseStep 12899411 = 19349117) B19349117
theorem B2618671 : Blo 1697549 2618671 := bstep (se 1 (by rfl) ⟨1964003, by rfl⟩ : syracuseStep 2618671 = 3928007) B3928007
theorem B4298143 : Blo 1697549 4298143 := bstep (se 1 (by rfl) ⟨3223607, by rfl⟩ : syracuseStep 4298143 = 6447215) B6447215
theorem B44725927 : Blo 1697549 44725927 := bstep (se 1 (by rfl) ⟨33544445, by rfl⟩ : syracuseStep 44725927 = 67088891) B67088891
theorem B2546999 : Blo 1697549 2546999 := bstep (se 1 (by rfl) ⟨1910249, by rfl⟩ : syracuseStep 2546999 = 3820499) B3820499
theorem B4300087 : Blo 1697549 4300087 := bstep (se 1 (by rfl) ⟨3225065, by rfl⟩ : syracuseStep 4300087 = 6450131) B6450131
theorem B6446729 : Blo 1697549 6446729 := bstep (se 2 (by rfl) ⟨2417523, by rfl⟩ : syracuseStep 6446729 = 4835047) B4835047
theorem B1005059771 : Blo 1697549 1005059771 := bstep (se 1 (by rfl) ⟨753794828, by rfl⟩ : syracuseStep 1005059771 = 1507589657) B1507589657
theorem B2547887 : Blo 1697549 2547887 := bstep (se 1 (by rfl) ⟨1910915, by rfl⟩ : syracuseStep 2547887 = 3821831) B3821831
theorem B16548329 : Blo 1697549 16548329 := bstep (se 2 (by rfl) ⟨6205623, by rfl⟩ : syracuseStep 16548329 = 12411247) B12411247
theorem B4588775 : Blo 1697549 4588775 := bstep (se 1 (by rfl) ⟨3441581, by rfl⟩ : syracuseStep 4588775 = 6883163) B6883163
theorem B7259473 : Blo 1697549 7259473 := bstep (se 2 (by rfl) ⟨2722302, by rfl⟩ : syracuseStep 7259473 = 5444605) B5444605
theorem B3491561 : Blo 1697549 3491561 := bstep (se 2 (by rfl) ⟨1309335, by rfl⟩ : syracuseStep 3491561 = 2618671) B2618671
theorem B1697999 : Blo 1697549 1697999 := bstep (se 1 (by rfl) ⟨1273499, by rfl⟩ : syracuseStep 1697999 = 2546999) B2546999
theorem B1698559 : Blo 1697549 1698559 := bstep (se 1 (by rfl) ⟨1273919, by rfl⟩ : syracuseStep 1698559 = 2547839) B2547839
theorem B1698587 : Blo 1697549 1698587 := bstep (se 1 (by rfl) ⟨1273940, by rfl⟩ : syracuseStep 1698587 = 2547881) B2547881
theorem B2419483 : Blo 1697549 2419483 := bstep (se 1 (by rfl) ⟨1814612, by rfl⟩ : syracuseStep 2419483 = 3629225) B3629225
theorem B1698623 : Blo 1697549 1698623 := bstep (se 1 (by rfl) ⟨1273967, by rfl⟩ : syracuseStep 1698623 = 2547935) B2547935
theorem B1911919 : Blo 1697549 1911919 := bstep (se 1 (by rfl) ⟨1433939, by rfl⟩ : syracuseStep 1911919 = 2867879) B2867879
theorem B19614959 : Blo 1697549 19614959 := bstep (se 1 (by rfl) ⟨14711219, by rfl⟩ : syracuseStep 19614959 = 29422439) B29422439
theorem B1699359 : Blo 1697549 1699359 := bstep (se 1 (by rfl) ⟨1274519, by rfl⟩ : syracuseStep 1699359 = 2549039) B2549039
theorem B6450799 : Blo 1697549 6450799 := bstep (se 1 (by rfl) ⟨4838099, by rfl⟩ : syracuseStep 6450799 = 9676199) B9676199
theorem B6451103 : Blo 1697549 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B5730479 : Blo 1697549 5730479 := bstep (se 1 (by rfl) ⟨4297859, by rfl⟩ : syracuseStep 5730479 = 8595719) B8595719
theorem B5730857 : Blo 1697549 5730857 := bstep (se 2 (by rfl) ⟨2149071, by rfl⟩ : syracuseStep 5730857 = 4298143) B4298143
theorem B7451327 : Blo 1697549 7451327 := bstep (se 1 (by rfl) ⟨5588495, by rfl⟩ : syracuseStep 7451327 = 11176991) B11176991
theorem B59634569 : Blo 1697549 59634569 := bstep (se 2 (by rfl) ⟨22362963, by rfl⟩ : syracuseStep 59634569 = 44725927) B44725927
theorem B4297819 : Blo 1697549 4297819 := bstep (se 1 (by rfl) ⟨3223364, by rfl⟩ : syracuseStep 4297819 = 6446729) B6446729
theorem B2864639 : Blo 1697549 2864639 := bstep (se 1 (by rfl) ⟨2148479, by rfl⟩ : syracuseStep 2864639 = 4296959) B4296959
theorem B282875449 : Blo 1697549 282875449 := bstep (se 2 (by rfl) ⟨106078293, by rfl⟩ : syracuseStep 282875449 = 212156587) B212156587
theorem B27547361 : Blo 1697549 27547361 := bstep (se 2 (by rfl) ⟨10330260, by rfl⟩ : syracuseStep 27547361 = 20660521) B20660521
theorem B8599607 : Blo 1697549 8599607 := bstep (se 1 (by rfl) ⟨6449705, by rfl⟩ : syracuseStep 8599607 = 12899411) B12899411
theorem B19618109 : Blo 1697549 19618109 := bstep (se 3 (by rfl) ⟨3678395, by rfl⟩ : syracuseStep 19618109 = 7356791) B7356791
theorem B278878859 : Blo 1697549 278878859 := bstep (se 1 (by rfl) ⟨209159144, by rfl⟩ : syracuseStep 278878859 = 418318289) B418318289
theorem B5733449 : Blo 1697549 5733449 := bstep (se 2 (by rfl) ⟨2150043, by rfl⟩ : syracuseStep 5733449 = 4300087) B4300087
theorem B7257185 : Blo 1697549 7257185 := bstep (se 2 (by rfl) ⟨2721444, by rfl⟩ : syracuseStep 7257185 = 5442889) B5442889
theorem B670039847 : Blo 1697549 670039847 := bstep (se 1 (by rfl) ⟨502529885, by rfl⟩ : syracuseStep 670039847 = 1005059771) B1005059771
theorem B39756379 : Blo 1697549 39756379 := bstep (se 1 (by rfl) ⟨29817284, by rfl⟩ : syracuseStep 39756379 = 59634569) B59634569
theorem B1909759 : Blo 1697549 1909759 := bstep (se 1 (by rfl) ⟨1432319, by rfl⟩ : syracuseStep 1909759 = 2864639) B2864639
theorem B2327707 : Blo 1697549 2327707 := bstep (se 1 (by rfl) ⟨1745780, by rfl⟩ : syracuseStep 2327707 = 3491561) B3491561
theorem B2549225 : Blo 1697549 2549225 := bstep (se 2 (by rfl) ⟨955959, by rfl⟩ : syracuseStep 2549225 = 1911919) B1911919
theorem B185919239 : Blo 1697549 185919239 := bstep (se 1 (by rfl) ⟨139439429, by rfl⟩ : syracuseStep 185919239 = 278878859) B278878859
theorem B13076639 : Blo 1697549 13076639 := bstep (se 1 (by rfl) ⟨9807479, by rfl⟩ : syracuseStep 13076639 = 19614959) B19614959
theorem B3820319 : Blo 1697549 3820319 := bstep (se 1 (by rfl) ⟨2865239, by rfl⟩ : syracuseStep 3820319 = 5730479) B5730479
theorem B1698591 : Blo 1697549 1698591 := bstep (se 1 (by rfl) ⟨1273943, by rfl⟩ : syracuseStep 1698591 = 2547887) B2547887
theorem B3820571 : Blo 1697549 3820571 := bstep (se 1 (by rfl) ⟨2865428, by rfl⟩ : syracuseStep 3820571 = 5730857) B5730857
theorem B3059183 : Blo 1697549 3059183 := bstep (se 1 (by rfl) ⟨2294387, by rfl⟩ : syracuseStep 3059183 = 4588775) B4588775
theorem B5730425 : Blo 1697549 5730425 := bstep (se 2 (by rfl) ⟨2148909, by rfl⟩ : syracuseStep 5730425 = 4297819) B4297819
theorem B13078739 : Blo 1697549 13078739 := bstep (se 1 (by rfl) ⟨9809054, by rfl⟩ : syracuseStep 13078739 = 19618109) B19618109
theorem B9679297 : Blo 1697549 9679297 := bstep (se 2 (by rfl) ⟨3629736, by rfl⟩ : syracuseStep 9679297 = 7259473) B7259473
theorem B19870205 : Blo 1697549 19870205 := bstep (se 3 (by rfl) ⟨3725663, by rfl⟩ : syracuseStep 19870205 = 7451327) B7451327
theorem B3822299 : Blo 1697549 3822299 := bstep (se 1 (by rfl) ⟨2866724, by rfl⟩ : syracuseStep 3822299 = 5733449) B5733449
theorem B4838123 : Blo 1697549 4838123 := bstep (se 1 (by rfl) ⟨3628592, by rfl⟩ : syracuseStep 4838123 = 7257185) B7257185
theorem B11032219 : Blo 1697549 11032219 := bstep (se 1 (by rfl) ⟨8274164, by rfl⟩ : syracuseStep 11032219 = 16548329) B16548329
theorem B3225977 : Blo 1697549 3225977 := bstep (se 2 (by rfl) ⟨1209741, by rfl⟩ : syracuseStep 3225977 = 2419483) B2419483
theorem B18364907 : Blo 1697549 18364907 := bstep (se 1 (by rfl) ⟨13773680, by rfl⟩ : syracuseStep 18364907 = 27547361) B27547361
theorem B5733071 : Blo 1697549 5733071 := bstep (se 1 (by rfl) ⟨4299803, by rfl⟩ : syracuseStep 5733071 = 8599607) B8599607
theorem B377167265 : Blo 1697549 377167265 := bstep (se 2 (by rfl) ⟨141437724, by rfl⟩ : syracuseStep 377167265 = 282875449) B282875449
theorem B8601065 : Blo 1697549 8601065 := bstep (se 2 (by rfl) ⟨3225399, by rfl⟩ : syracuseStep 8601065 = 6450799) B6450799
theorem B446693231 : Blo 1697549 446693231 := bstep (se 1 (by rfl) ⟨335019923, by rfl⟩ : syracuseStep 446693231 = 670039847) B670039847
theorem B4300735 : Blo 1697549 4300735 := bstep (se 1 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 4300735 = 6451103) B6451103
theorem B2548199 : Blo 1697549 2548199 := bstep (se 1 (by rfl) ⟨1911149, by rfl⟩ : syracuseStep 2548199 = 3822299) B3822299
theorem B123946159 : Blo 1697549 123946159 := bstep (se 1 (by rfl) ⟨92959619, by rfl⟩ : syracuseStep 123946159 = 185919239) B185919239
theorem B52987213 : Blo 1697549 52987213 := bstep (se 3 (by rfl) ⟨9935102, by rfl⟩ : syracuseStep 52987213 = 19870205) B19870205
theorem B8717759 : Blo 1697549 8717759 := bstep (se 1 (by rfl) ⟨6538319, by rfl⟩ : syracuseStep 8717759 = 13076639) B13076639
theorem B3820283 : Blo 1697549 3820283 := bstep (se 1 (by rfl) ⟨2865212, by rfl⟩ : syracuseStep 3820283 = 5730425) B5730425
theorem B8719159 : Blo 1697549 8719159 := bstep (se 1 (by rfl) ⟨6539369, by rfl⟩ : syracuseStep 8719159 = 13078739) B13078739
theorem B12905729 : Blo 1697549 12905729 := bstep (se 2 (by rfl) ⟨4839648, by rfl⟩ : syracuseStep 12905729 = 9679297) B9679297
theorem B58838501 : Blo 1697549 58838501 := bstep (se 4 (by rfl) ⟨5516109, by rfl⟩ : syracuseStep 58838501 = 11032219) B11032219
theorem B1699483 : Blo 1697549 1699483 := bstep (se 1 (by rfl) ⟨1274612, by rfl⟩ : syracuseStep 1699483 = 2549225) B2549225
theorem B2150651 : Blo 1697549 2150651 := bstep (se 1 (by rfl) ⟨1612988, by rfl⟩ : syracuseStep 2150651 = 3225977) B3225977
theorem B12243271 : Blo 1697549 12243271 := bstep (se 1 (by rfl) ⟨9182453, by rfl⟩ : syracuseStep 12243271 = 18364907) B18364907
theorem B3822047 : Blo 1697549 3822047 := bstep (se 1 (by rfl) ⟨2866535, by rfl⟩ : syracuseStep 3822047 = 5733071) B5733071
theorem B3225415 : Blo 1697549 3225415 := bstep (se 1 (by rfl) ⟨2419061, by rfl⟩ : syracuseStep 3225415 = 4838123) B4838123
theorem B53008505 : Blo 1697549 53008505 := bstep (se 2 (by rfl) ⟨19878189, by rfl⟩ : syracuseStep 53008505 = 39756379) B39756379
theorem B2546345 : Blo 1697549 2546345 := bstep (se 2 (by rfl) ⟨954879, by rfl⟩ : syracuseStep 2546345 = 1909759) B1909759
theorem B3103609 : Blo 1697549 3103609 := bstep (se 2 (by rfl) ⟨1163853, by rfl⟩ : syracuseStep 3103609 = 2327707) B2327707
theorem B2546879 : Blo 1697549 2546879 := bstep (se 1 (by rfl) ⟨1910159, by rfl⟩ : syracuseStep 2546879 = 3820319) B3820319
theorem B2547047 : Blo 1697549 2547047 := bstep (se 1 (by rfl) ⟨1910285, by rfl⟩ : syracuseStep 2547047 = 3820571) B3820571
theorem B251444843 : Blo 1697549 251444843 := bstep (se 1 (by rfl) ⟨188583632, by rfl⟩ : syracuseStep 251444843 = 377167265) B377167265
theorem B5734043 : Blo 1697549 5734043 := bstep (se 1 (by rfl) ⟨4300532, by rfl⟩ : syracuseStep 5734043 = 8601065) B8601065
theorem B2039455 : Blo 1697549 2039455 := bstep (se 1 (by rfl) ⟨1529591, by rfl⟩ : syracuseStep 2039455 = 3059183) B3059183
theorem B297795487 : Blo 1697549 297795487 := bstep (se 1 (by rfl) ⟨223346615, by rfl⟩ : syracuseStep 297795487 = 446693231) B446693231
theorem B5734313 : Blo 1697549 5734313 := bstep (se 2 (by rfl) ⟨2150367, by rfl⟩ : syracuseStep 5734313 = 4300735) B4300735
theorem B2548031 : Blo 1697549 2548031 := bstep (se 1 (by rfl) ⟨1911023, by rfl⟩ : syracuseStep 2548031 = 3822047) B3822047
theorem B5735069 : Blo 1697549 5735069 := bstep (se 3 (by rfl) ⟨1075325, by rfl⟩ : syracuseStep 5735069 = 2150651) B2150651
theorem B11625545 : Blo 1697549 11625545 := bstep (se 2 (by rfl) ⟨4359579, by rfl⟩ : syracuseStep 11625545 = 8719159) B8719159
theorem B4138145 : Blo 1697549 4138145 := bstep (se 2 (by rfl) ⟨1551804, by rfl⟩ : syracuseStep 4138145 = 3103609) B3103609
theorem B1697563 : Blo 1697549 1697563 := bstep (se 1 (by rfl) ⟨1273172, by rfl⟩ : syracuseStep 1697563 = 2546345) B2546345
theorem B1697919 : Blo 1697549 1697919 := bstep (se 1 (by rfl) ⟨1273439, by rfl⟩ : syracuseStep 1697919 = 2546879) B2546879
theorem B8603819 : Blo 1697549 8603819 := bstep (se 1 (by rfl) ⟨6452864, by rfl⟩ : syracuseStep 8603819 = 12905729) B12905729
theorem B1698031 : Blo 1697549 1698031 := bstep (se 1 (by rfl) ⟨1273523, by rfl⟩ : syracuseStep 1698031 = 2547047) B2547047
theorem B39225667 : Blo 1697549 39225667 := bstep (se 1 (by rfl) ⟨29419250, by rfl⟩ : syracuseStep 39225667 = 58838501) B58838501
theorem B397060649 : Blo 1697549 397060649 := bstep (se 2 (by rfl) ⟨148897743, by rfl⟩ : syracuseStep 397060649 = 297795487) B297795487
theorem B1698799 : Blo 1697549 1698799 := bstep (se 1 (by rfl) ⟨1274099, by rfl⟩ : syracuseStep 1698799 = 2548199) B2548199
theorem B5811839 : Blo 1697549 5811839 := bstep (se 1 (by rfl) ⟨4358879, by rfl⟩ : syracuseStep 5811839 = 8717759) B8717759
theorem B165261545 : Blo 1697549 165261545 := bstep (se 2 (by rfl) ⟨61973079, by rfl⟩ : syracuseStep 165261545 = 123946159) B123946159
theorem B167629895 : Blo 1697549 167629895 := bstep (se 1 (by rfl) ⟨125722421, by rfl⟩ : syracuseStep 167629895 = 251444843) B251444843
theorem B3822695 : Blo 1697549 3822695 := bstep (se 1 (by rfl) ⟨2867021, by rfl⟩ : syracuseStep 3822695 = 5734043) B5734043
theorem B3822875 : Blo 1697549 3822875 := bstep (se 1 (by rfl) ⟨2867156, by rfl⟩ : syracuseStep 3822875 = 5734313) B5734313
theorem B16324361 : Blo 1697549 16324361 := bstep (se 2 (by rfl) ⟨6121635, by rfl⟩ : syracuseStep 16324361 = 12243271) B12243271
theorem B35339003 : Blo 1697549 35339003 := bstep (se 1 (by rfl) ⟨26504252, by rfl⟩ : syracuseStep 35339003 = 53008505) B53008505
theorem B282598469 : Blo 1697549 282598469 := bstep (se 4 (by rfl) ⟨26493606, by rfl⟩ : syracuseStep 282598469 = 52987213) B52987213
theorem B2546855 : Blo 1697549 2546855 := bstep (se 1 (by rfl) ⟨1910141, by rfl⟩ : syracuseStep 2546855 = 3820283) B3820283
theorem B2719273 : Blo 1697549 2719273 := bstep (se 2 (by rfl) ⟨1019727, by rfl⟩ : syracuseStep 2719273 = 2039455) B2039455
theorem B4300553 : Blo 1697549 4300553 := bstep (se 2 (by rfl) ⟨1612707, by rfl⟩ : syracuseStep 4300553 = 3225415) B3225415
theorem B110174363 : Blo 1697549 110174363 := bstep (se 1 (by rfl) ⟨82630772, by rfl⟩ : syracuseStep 110174363 = 165261545) B165261545
theorem B7750363 : Blo 1697549 7750363 := bstep (se 1 (by rfl) ⟨5812772, by rfl⟩ : syracuseStep 7750363 = 11625545) B11625545
theorem B2548463 : Blo 1697549 2548463 := bstep (se 1 (by rfl) ⟨1911347, by rfl⟩ : syracuseStep 2548463 = 3822695) B3822695
theorem B2548583 : Blo 1697549 2548583 := bstep (se 1 (by rfl) ⟨1911437, by rfl⟩ : syracuseStep 2548583 = 3822875) B3822875
theorem B5735879 : Blo 1697549 5735879 := bstep (se 1 (by rfl) ⟨4301909, by rfl⟩ : syracuseStep 5735879 = 8603819) B8603819
theorem B1697903 : Blo 1697549 1697903 := bstep (se 1 (by rfl) ⟨1273427, by rfl⟩ : syracuseStep 1697903 = 2546855) B2546855
theorem B1698687 : Blo 1697549 1698687 := bstep (se 1 (by rfl) ⟨1274015, by rfl⟩ : syracuseStep 1698687 = 2548031) B2548031
theorem B52300889 : Blo 1697549 52300889 := bstep (se 2 (by rfl) ⟨19612833, by rfl⟩ : syracuseStep 52300889 = 39225667) B39225667
theorem B10882907 : Blo 1697549 10882907 := bstep (se 1 (by rfl) ⟨8162180, by rfl⟩ : syracuseStep 10882907 = 16324361) B16324361
theorem B3625697 : Blo 1697549 3625697 := bstep (se 2 (by rfl) ⟨1359636, by rfl⟩ : syracuseStep 3625697 = 2719273) B2719273
theorem B3823379 : Blo 1697549 3823379 := bstep (se 1 (by rfl) ⟨2867534, by rfl⟩ : syracuseStep 3823379 = 5735069) B5735069
theorem B111753263 : Blo 1697549 111753263 := bstep (se 1 (by rfl) ⟨83814947, by rfl⟩ : syracuseStep 111753263 = 167629895) B167629895
theorem B2758763 : Blo 1697549 2758763 := bstep (se 1 (by rfl) ⟨2069072, by rfl⟩ : syracuseStep 2758763 = 4138145) B4138145
theorem B264707099 : Blo 1697549 264707099 := bstep (se 1 (by rfl) ⟨198530324, by rfl⟩ : syracuseStep 264707099 = 397060649) B397060649
theorem B23559335 : Blo 1697549 23559335 := bstep (se 1 (by rfl) ⟨17669501, by rfl⟩ : syracuseStep 23559335 = 35339003) B35339003
theorem B188398979 : Blo 1697549 188398979 := bstep (se 1 (by rfl) ⟨141299234, by rfl⟩ : syracuseStep 188398979 = 282598469) B282598469
theorem B3874559 : Blo 1697549 3874559 := bstep (se 1 (by rfl) ⟨2905919, by rfl⟩ : syracuseStep 3874559 = 5811839) B5811839
theorem B2867035 : Blo 1697549 2867035 := bstep (se 1 (by rfl) ⟨2150276, by rfl⟩ : syracuseStep 2867035 = 4300553) B4300553
theorem B73449575 : Blo 1697549 73449575 := bstep (se 1 (by rfl) ⟨55087181, by rfl⟩ : syracuseStep 73449575 = 110174363) B110174363
theorem B7356701 : Blo 1697549 7356701 := bstep (se 3 (by rfl) ⟨1379381, by rfl⟩ : syracuseStep 7356701 = 2758763) B2758763
theorem B2417131 : Blo 1697549 2417131 := bstep (se 1 (by rfl) ⟨1812848, by rfl⟩ : syracuseStep 2417131 = 3625697) B3625697
theorem B2548919 : Blo 1697549 2548919 := bstep (se 1 (by rfl) ⟨1911689, by rfl⟩ : syracuseStep 2548919 = 3823379) B3823379
theorem B34867259 : Blo 1697549 34867259 := bstep (se 1 (by rfl) ⟨26150444, by rfl⟩ : syracuseStep 34867259 = 52300889) B52300889
theorem B15706223 : Blo 1697549 15706223 := bstep (se 1 (by rfl) ⟨11779667, by rfl⟩ : syracuseStep 15706223 = 23559335) B23559335
theorem B1698975 : Blo 1697549 1698975 := bstep (se 1 (by rfl) ⟨1274231, by rfl⟩ : syracuseStep 1698975 = 2548463) B2548463
theorem B1699055 : Blo 1697549 1699055 := bstep (se 1 (by rfl) ⟨1274291, by rfl⟩ : syracuseStep 1699055 = 2548583) B2548583
theorem B10333817 : Blo 1697549 10333817 := bstep (se 2 (by rfl) ⟨3875181, by rfl⟩ : syracuseStep 10333817 = 7750363) B7750363
theorem B74502175 : Blo 1697549 74502175 := bstep (se 1 (by rfl) ⟨55876631, by rfl⟩ : syracuseStep 74502175 = 111753263) B111753263
theorem B3822713 : Blo 1697549 3822713 := bstep (se 2 (by rfl) ⟨1433517, by rfl⟩ : syracuseStep 3822713 = 2867035) B2867035
theorem B7255271 : Blo 1697549 7255271 := bstep (se 1 (by rfl) ⟨5441453, by rfl⟩ : syracuseStep 7255271 = 10882907) B10882907
theorem B3823919 : Blo 1697549 3823919 := bstep (se 1 (by rfl) ⟨2867939, by rfl⟩ : syracuseStep 3823919 = 5735879) B5735879
theorem B176471399 : Blo 1697549 176471399 := bstep (se 1 (by rfl) ⟨132353549, by rfl⟩ : syracuseStep 176471399 = 264707099) B264707099
theorem B125599319 : Blo 1697549 125599319 := bstep (se 1 (by rfl) ⟨94199489, by rfl⟩ : syracuseStep 125599319 = 188398979) B188398979
theorem B41328629 : Blo 1697549 41328629 := bstep (se 5 (by rfl) ⟨1937279, by rfl⟩ : syracuseStep 41328629 = 3874559) B3874559
theorem B99336233 : Blo 1697549 99336233 := bstep (se 2 (by rfl) ⟨37251087, by rfl⟩ : syracuseStep 99336233 = 74502175) B74502175
theorem B2548475 : Blo 1697549 2548475 := bstep (se 1 (by rfl) ⟨1911356, by rfl⟩ : syracuseStep 2548475 = 3822713) B3822713
theorem B10470815 : Blo 1697549 10470815 := bstep (se 1 (by rfl) ⟨7853111, by rfl⟩ : syracuseStep 10470815 = 15706223) B15706223
theorem B2549279 : Blo 1697549 2549279 := bstep (se 1 (by rfl) ⟨1911959, by rfl⟩ : syracuseStep 2549279 = 3823919) B3823919
theorem B117647599 : Blo 1697549 117647599 := bstep (se 1 (by rfl) ⟨88235699, by rfl⟩ : syracuseStep 117647599 = 176471399) B176471399
theorem B83732879 : Blo 1697549 83732879 := bstep (se 1 (by rfl) ⟨62799659, by rfl⟩ : syracuseStep 83732879 = 125599319) B125599319
theorem B27552419 : Blo 1697549 27552419 := bstep (se 1 (by rfl) ⟨20664314, by rfl⟩ : syracuseStep 27552419 = 41328629) B41328629
theorem B48966383 : Blo 1697549 48966383 := bstep (se 1 (by rfl) ⟨36724787, by rfl⟩ : syracuseStep 48966383 = 73449575) B73449575
theorem B3222841 : Blo 1697549 3222841 := bstep (se 2 (by rfl) ⟨1208565, by rfl⟩ : syracuseStep 3222841 = 2417131) B2417131
theorem B1699279 : Blo 1697549 1699279 := bstep (se 1 (by rfl) ⟨1274459, by rfl⟩ : syracuseStep 1699279 = 2548919) B2548919
theorem B4836847 : Blo 1697549 4836847 := bstep (se 1 (by rfl) ⟨3627635, by rfl⟩ : syracuseStep 4836847 = 7255271) B7255271
theorem B23244839 : Blo 1697549 23244839 := bstep (se 1 (by rfl) ⟨17433629, by rfl⟩ : syracuseStep 23244839 = 34867259) B34867259
theorem B19617869 : Blo 1697549 19617869 := bstep (se 3 (by rfl) ⟨3678350, by rfl⟩ : syracuseStep 19617869 = 7356701) B7356701
theorem B6889211 : Blo 1697549 6889211 := bstep (se 1 (by rfl) ⟨5166908, by rfl⟩ : syracuseStep 6889211 = 10333817) B10333817
theorem B66224155 : Blo 1697549 66224155 := bstep (se 1 (by rfl) ⟨49668116, by rfl⟩ : syracuseStep 66224155 = 99336233) B99336233
theorem B6980543 : Blo 1697549 6980543 := bstep (se 1 (by rfl) ⟨5235407, by rfl⟩ : syracuseStep 6980543 = 10470815) B10470815
theorem B55821919 : Blo 1697549 55821919 := bstep (se 1 (by rfl) ⟨41866439, by rfl⟩ : syracuseStep 55821919 = 83732879) B83732879
theorem B18368279 : Blo 1697549 18368279 := bstep (se 1 (by rfl) ⟨13776209, by rfl⟩ : syracuseStep 18368279 = 27552419) B27552419
theorem B6449129 : Blo 1697549 6449129 := bstep (se 2 (by rfl) ⟨2418423, by rfl⟩ : syracuseStep 6449129 = 4836847) B4836847
theorem B156863465 : Blo 1697549 156863465 := bstep (se 2 (by rfl) ⟨58823799, by rfl⟩ : syracuseStep 156863465 = 117647599) B117647599
theorem B1698983 : Blo 1697549 1698983 := bstep (se 1 (by rfl) ⟨1274237, by rfl⟩ : syracuseStep 1698983 = 2548475) B2548475
theorem B1699519 : Blo 1697549 1699519 := bstep (se 1 (by rfl) ⟨1274639, by rfl⟩ : syracuseStep 1699519 = 2549279) B2549279
theorem B13078579 : Blo 1697549 13078579 := bstep (se 1 (by rfl) ⟨9808934, by rfl⟩ : syracuseStep 13078579 = 19617869) B19617869
theorem B4297121 : Blo 1697549 4297121 := bstep (se 2 (by rfl) ⟨1611420, by rfl⟩ : syracuseStep 4297121 = 3222841) B3222841
theorem B4592807 : Blo 1697549 4592807 := bstep (se 1 (by rfl) ⟨3444605, by rfl⟩ : syracuseStep 4592807 = 6889211) B6889211
theorem B15496559 : Blo 1697549 15496559 := bstep (se 1 (by rfl) ⟨11622419, by rfl⟩ : syracuseStep 15496559 = 23244839) B23244839
theorem B32644255 : Blo 1697549 32644255 := bstep (se 1 (by rfl) ⟨24483191, by rfl⟩ : syracuseStep 32644255 = 48966383) B48966383
theorem B4653695 : Blo 1697549 4653695 := bstep (se 1 (by rfl) ⟨3490271, by rfl⟩ : syracuseStep 4653695 = 6980543) B6980543
theorem B10331039 : Blo 1697549 10331039 := bstep (se 1 (by rfl) ⟨7748279, by rfl⟩ : syracuseStep 10331039 = 15496559) B15496559
theorem B43525673 : Blo 1697549 43525673 := bstep (se 2 (by rfl) ⟨16322127, by rfl⟩ : syracuseStep 43525673 = 32644255) B32644255
theorem B104575643 : Blo 1697549 104575643 := bstep (se 1 (by rfl) ⟨78431732, by rfl⟩ : syracuseStep 104575643 = 156863465) B156863465
theorem B74429225 : Blo 1697549 74429225 := bstep (se 2 (by rfl) ⟨27910959, by rfl⟩ : syracuseStep 74429225 = 55821919) B55821919
theorem B88298873 : Blo 1697549 88298873 := bstep (se 2 (by rfl) ⟨33112077, by rfl⟩ : syracuseStep 88298873 = 66224155) B66224155
theorem B17438105 : Blo 1697549 17438105 := bstep (se 2 (by rfl) ⟨6539289, by rfl⟩ : syracuseStep 17438105 = 13078579) B13078579
theorem B2864747 : Blo 1697549 2864747 := bstep (se 1 (by rfl) ⟨2148560, by rfl⟩ : syracuseStep 2864747 = 4297121) B4297121
theorem B3061871 : Blo 1697549 3061871 := bstep (se 1 (by rfl) ⟨2296403, by rfl⟩ : syracuseStep 3061871 = 4592807) B4592807
theorem B12245519 : Blo 1697549 12245519 := bstep (se 1 (by rfl) ⟨9184139, by rfl⟩ : syracuseStep 12245519 = 18368279) B18368279
theorem B4299419 : Blo 1697549 4299419 := bstep (se 1 (by rfl) ⟨3224564, by rfl⟩ : syracuseStep 4299419 = 6449129) B6449129
theorem B49619483 : Blo 1697549 49619483 := bstep (se 1 (by rfl) ⟨37214612, by rfl⟩ : syracuseStep 49619483 = 74429225) B74429225
theorem B29017115 : Blo 1697549 29017115 := bstep (se 1 (by rfl) ⟨21762836, by rfl⟩ : syracuseStep 29017115 = 43525673) B43525673
theorem B1909831 : Blo 1697549 1909831 := bstep (se 1 (by rfl) ⟨1432373, by rfl⟩ : syracuseStep 1909831 = 2864747) B2864747
theorem B2041247 : Blo 1697549 2041247 := bstep (se 1 (by rfl) ⟨1530935, by rfl⟩ : syracuseStep 2041247 = 3061871) B3061871
theorem B69717095 : Blo 1697549 69717095 := bstep (se 1 (by rfl) ⟨52287821, by rfl⟩ : syracuseStep 69717095 = 104575643) B104575643
theorem B46501613 : Blo 1697549 46501613 := bstep (se 3 (by rfl) ⟨8719052, by rfl⟩ : syracuseStep 46501613 = 17438105) B17438105
theorem B8163679 : Blo 1697549 8163679 := bstep (se 1 (by rfl) ⟨6122759, by rfl⟩ : syracuseStep 8163679 = 12245519) B12245519
theorem B3102463 : Blo 1697549 3102463 := bstep (se 1 (by rfl) ⟨2326847, by rfl⟩ : syracuseStep 3102463 = 4653695) B4653695
theorem B6887359 : Blo 1697549 6887359 := bstep (se 1 (by rfl) ⟨5165519, by rfl⟩ : syracuseStep 6887359 = 10331039) B10331039
theorem B58865915 : Blo 1697549 58865915 := bstep (se 1 (by rfl) ⟨44149436, by rfl⟩ : syracuseStep 58865915 = 88298873) B88298873
theorem B2866279 : Blo 1697549 2866279 := bstep (se 1 (by rfl) ⟨2149709, by rfl⟩ : syracuseStep 2866279 = 4299419) B4299419
theorem B33079655 : Blo 1697549 33079655 := bstep (se 1 (by rfl) ⟨24809741, by rfl⟩ : syracuseStep 33079655 = 49619483) B49619483
theorem B31001075 : Blo 1697549 31001075 := bstep (se 1 (by rfl) ⟨23250806, by rfl⟩ : syracuseStep 31001075 = 46501613) B46501613
theorem B19344743 : Blo 1697549 19344743 := bstep (se 1 (by rfl) ⟨14508557, by rfl⟩ : syracuseStep 19344743 = 29017115) B29017115
theorem B5443325 : Blo 1697549 5443325 := bstep (se 3 (by rfl) ⟨1020623, by rfl⟩ : syracuseStep 5443325 = 2041247) B2041247
theorem B3821705 : Blo 1697549 3821705 := bstep (se 2 (by rfl) ⟨1433139, by rfl⟩ : syracuseStep 3821705 = 2866279) B2866279
theorem B39243943 : Blo 1697549 39243943 := bstep (se 1 (by rfl) ⟨29432957, by rfl⟩ : syracuseStep 39243943 = 58865915) B58865915
theorem B46478063 : Blo 1697549 46478063 := bstep (se 1 (by rfl) ⟨34858547, by rfl⟩ : syracuseStep 46478063 = 69717095) B69717095
theorem B10884905 : Blo 1697549 10884905 := bstep (se 2 (by rfl) ⟨4081839, by rfl⟩ : syracuseStep 10884905 = 8163679) B8163679
theorem B2546441 : Blo 1697549 2546441 := bstep (se 2 (by rfl) ⟨954915, by rfl⟩ : syracuseStep 2546441 = 1909831) B1909831
theorem B4136617 : Blo 1697549 4136617 := bstep (se 2 (by rfl) ⟨1551231, by rfl⟩ : syracuseStep 4136617 = 3102463) B3102463
theorem B9183145 : Blo 1697549 9183145 := bstep (se 2 (by rfl) ⟨3443679, by rfl⟩ : syracuseStep 9183145 = 6887359) B6887359
theorem B2547803 : Blo 1697549 2547803 := bstep (se 1 (by rfl) ⟨1910852, by rfl⟩ : syracuseStep 2547803 = 3821705) B3821705
theorem B22053103 : Blo 1697549 22053103 := bstep (se 1 (by rfl) ⟨16539827, by rfl⟩ : syracuseStep 22053103 = 33079655) B33079655
theorem B1697627 : Blo 1697549 1697627 := bstep (se 1 (by rfl) ⟨1273220, by rfl⟩ : syracuseStep 1697627 = 2546441) B2546441
theorem B5515489 : Blo 1697549 5515489 := bstep (se 2 (by rfl) ⟨2068308, by rfl⟩ : syracuseStep 5515489 = 4136617) B4136617
theorem B12896495 : Blo 1697549 12896495 := bstep (se 1 (by rfl) ⟨9672371, by rfl⟩ : syracuseStep 12896495 = 19344743) B19344743
theorem B52325257 : Blo 1697549 52325257 := bstep (se 2 (by rfl) ⟨19621971, by rfl⟩ : syracuseStep 52325257 = 39243943) B39243943
theorem B30985375 : Blo 1697549 30985375 := bstep (se 1 (by rfl) ⟨23239031, by rfl⟩ : syracuseStep 30985375 = 46478063) B46478063
theorem B12244193 : Blo 1697549 12244193 := bstep (se 2 (by rfl) ⟨4591572, by rfl⟩ : syracuseStep 12244193 = 9183145) B9183145
theorem B7256603 : Blo 1697549 7256603 := bstep (se 1 (by rfl) ⟨5442452, by rfl⟩ : syracuseStep 7256603 = 10884905) B10884905
theorem B20667383 : Blo 1697549 20667383 := bstep (se 1 (by rfl) ⟨15500537, by rfl⟩ : syracuseStep 20667383 = 31001075) B31001075
theorem B3628883 : Blo 1697549 3628883 := bstep (se 1 (by rfl) ⟨2721662, by rfl⟩ : syracuseStep 3628883 = 5443325) B5443325
theorem B41313833 : Blo 1697549 41313833 := bstep (se 2 (by rfl) ⟨15492687, by rfl⟩ : syracuseStep 41313833 = 30985375) B30985375
theorem B2419255 : Blo 1697549 2419255 := bstep (se 1 (by rfl) ⟨1814441, by rfl⟩ : syracuseStep 2419255 = 3628883) B3628883
theorem B1698535 : Blo 1697549 1698535 := bstep (se 1 (by rfl) ⟨1273901, by rfl⟩ : syracuseStep 1698535 = 2547803) B2547803
theorem B8162795 : Blo 1697549 8162795 := bstep (se 1 (by rfl) ⟨6122096, by rfl⟩ : syracuseStep 8162795 = 12244193) B12244193
theorem B69767009 : Blo 1697549 69767009 := bstep (se 2 (by rfl) ⟨26162628, by rfl⟩ : syracuseStep 69767009 = 52325257) B52325257
theorem B117616549 : Blo 1697549 117616549 := bstep (se 4 (by rfl) ⟨11026551, by rfl⟩ : syracuseStep 117616549 = 22053103) B22053103
theorem B8597663 : Blo 1697549 8597663 := bstep (se 1 (by rfl) ⟨6448247, by rfl⟩ : syracuseStep 8597663 = 12896495) B12896495
theorem B4837735 : Blo 1697549 4837735 := bstep (se 1 (by rfl) ⟨3628301, by rfl⟩ : syracuseStep 4837735 = 7256603) B7256603
theorem B7353985 : Blo 1697549 7353985 := bstep (se 2 (by rfl) ⟨2757744, by rfl⟩ : syracuseStep 7353985 = 5515489) B5515489
theorem B13778255 : Blo 1697549 13778255 := bstep (se 1 (by rfl) ⟨10333691, by rfl⟩ : syracuseStep 13778255 = 20667383) B20667383
theorem B27542555 : Blo 1697549 27542555 := bstep (se 1 (by rfl) ⟨20656916, by rfl⟩ : syracuseStep 27542555 = 41313833) B41313833
theorem B21767453 : Blo 1697549 21767453 := bstep (se 3 (by rfl) ⟨4081397, by rfl⟩ : syracuseStep 21767453 = 8162795) B8162795
theorem B9185503 : Blo 1697549 9185503 := bstep (se 1 (by rfl) ⟨6889127, by rfl⟩ : syracuseStep 9185503 = 13778255) B13778255
theorem B156822065 : Blo 1697549 156822065 := bstep (se 2 (by rfl) ⟨58808274, by rfl⟩ : syracuseStep 156822065 = 117616549) B117616549
theorem B6450313 : Blo 1697549 6450313 := bstep (se 2 (by rfl) ⟨2418867, by rfl⟩ : syracuseStep 6450313 = 4837735) B4837735
theorem B46511339 : Blo 1697549 46511339 := bstep (se 1 (by rfl) ⟨34883504, by rfl⟩ : syracuseStep 46511339 = 69767009) B69767009
theorem B5731775 : Blo 1697549 5731775 := bstep (se 1 (by rfl) ⟨4298831, by rfl⟩ : syracuseStep 5731775 = 8597663) B8597663
theorem B3225673 : Blo 1697549 3225673 := bstep (se 2 (by rfl) ⟨1209627, by rfl⟩ : syracuseStep 3225673 = 2419255) B2419255
theorem B9805313 : Blo 1697549 9805313 := bstep (se 2 (by rfl) ⟨3676992, by rfl⟩ : syracuseStep 9805313 = 7353985) B7353985
theorem B4300897 : Blo 1697549 4300897 := bstep (se 2 (by rfl) ⟨1612836, by rfl⟩ : syracuseStep 4300897 = 3225673) B3225673
theorem B12247337 : Blo 1697549 12247337 := bstep (se 2 (by rfl) ⟨4592751, by rfl⟩ : syracuseStep 12247337 = 9185503) B9185503
theorem B104548043 : Blo 1697549 104548043 := bstep (se 1 (by rfl) ⟨78411032, by rfl⟩ : syracuseStep 104548043 = 156822065) B156822065
theorem B124030237 : Blo 1697549 124030237 := bstep (se 3 (by rfl) ⟨23255669, by rfl⟩ : syracuseStep 124030237 = 46511339) B46511339
theorem B18361703 : Blo 1697549 18361703 := bstep (se 1 (by rfl) ⟨13771277, by rfl⟩ : syracuseStep 18361703 = 27542555) B27542555
theorem B14511635 : Blo 1697549 14511635 := bstep (se 1 (by rfl) ⟨10883726, by rfl⟩ : syracuseStep 14511635 = 21767453) B21767453
theorem B3821183 : Blo 1697549 3821183 := bstep (se 1 (by rfl) ⟨2865887, by rfl⟩ : syracuseStep 3821183 = 5731775) B5731775
theorem B8600417 : Blo 1697549 8600417 := bstep (se 2 (by rfl) ⟨3225156, by rfl⟩ : syracuseStep 8600417 = 6450313) B6450313
theorem B6536875 : Blo 1697549 6536875 := bstep (se 1 (by rfl) ⟨4902656, by rfl⟩ : syracuseStep 6536875 = 9805313) B9805313
theorem B5734529 : Blo 1697549 5734529 := bstep (se 2 (by rfl) ⟨2150448, by rfl⟩ : syracuseStep 5734529 = 4300897) B4300897
theorem B165373649 : Blo 1697549 165373649 := bstep (se 2 (by rfl) ⟨62015118, by rfl⟩ : syracuseStep 165373649 = 124030237) B124030237
theorem B12241135 : Blo 1697549 12241135 := bstep (se 1 (by rfl) ⟨9180851, by rfl⟩ : syracuseStep 12241135 = 18361703) B18361703
theorem B278794781 : Blo 1697549 278794781 := bstep (se 3 (by rfl) ⟨52274021, by rfl⟩ : syracuseStep 278794781 = 104548043) B104548043
theorem B8164891 : Blo 1697549 8164891 := bstep (se 1 (by rfl) ⟨6123668, by rfl⟩ : syracuseStep 8164891 = 12247337) B12247337
theorem B5733611 : Blo 1697549 5733611 := bstep (se 1 (by rfl) ⟨4300208, by rfl⟩ : syracuseStep 5733611 = 8600417) B8600417
theorem B8715833 : Blo 1697549 8715833 := bstep (se 2 (by rfl) ⟨3268437, by rfl⟩ : syracuseStep 8715833 = 6536875) B6536875
theorem B9674423 : Blo 1697549 9674423 := bstep (se 1 (by rfl) ⟨7255817, by rfl⟩ : syracuseStep 9674423 = 14511635) B14511635
theorem B2547455 : Blo 1697549 2547455 := bstep (se 1 (by rfl) ⟨1910591, by rfl⟩ : syracuseStep 2547455 = 3821183) B3821183
theorem B110249099 : Blo 1697549 110249099 := bstep (se 1 (by rfl) ⟨82686824, by rfl⟩ : syracuseStep 110249099 = 165373649) B165373649
theorem B5810555 : Blo 1697549 5810555 := bstep (se 1 (by rfl) ⟨4357916, by rfl⟩ : syracuseStep 5810555 = 8715833) B8715833
theorem B6449615 : Blo 1697549 6449615 := bstep (se 1 (by rfl) ⟨4837211, by rfl⟩ : syracuseStep 6449615 = 9674423) B9674423
theorem B1698303 : Blo 1697549 1698303 := bstep (se 1 (by rfl) ⟨1273727, by rfl⟩ : syracuseStep 1698303 = 2547455) B2547455
theorem B16321513 : Blo 1697549 16321513 := bstep (se 2 (by rfl) ⟨6120567, by rfl⟩ : syracuseStep 16321513 = 12241135) B12241135
theorem B185863187 : Blo 1697549 185863187 := bstep (se 1 (by rfl) ⟨139397390, by rfl⟩ : syracuseStep 185863187 = 278794781) B278794781
theorem B3822407 : Blo 1697549 3822407 := bstep (se 1 (by rfl) ⟨2866805, by rfl⟩ : syracuseStep 3822407 = 5733611) B5733611
theorem B3823019 : Blo 1697549 3823019 := bstep (se 1 (by rfl) ⟨2867264, by rfl⟩ : syracuseStep 3823019 = 5734529) B5734529
theorem B10886521 : Blo 1697549 10886521 := bstep (se 2 (by rfl) ⟨4082445, by rfl⟩ : syracuseStep 10886521 = 8164891) B8164891
theorem B2548271 : Blo 1697549 2548271 := bstep (se 1 (by rfl) ⟨1911203, by rfl⟩ : syracuseStep 2548271 = 3822407) B3822407
theorem B73499399 : Blo 1697549 73499399 := bstep (se 1 (by rfl) ⟨55124549, by rfl⟩ : syracuseStep 73499399 = 110249099) B110249099
theorem B2548679 : Blo 1697549 2548679 := bstep (se 1 (by rfl) ⟨1911509, by rfl⟩ : syracuseStep 2548679 = 3823019) B3823019
theorem B15494813 : Blo 1697549 15494813 := bstep (se 3 (by rfl) ⟨2905277, by rfl⟩ : syracuseStep 15494813 = 5810555) B5810555
theorem B21762017 : Blo 1697549 21762017 := bstep (se 2 (by rfl) ⟨8160756, by rfl⟩ : syracuseStep 21762017 = 16321513) B16321513
theorem B123908791 : Blo 1697549 123908791 := bstep (se 1 (by rfl) ⟨92931593, by rfl⟩ : syracuseStep 123908791 = 185863187) B185863187
theorem B4299743 : Blo 1697549 4299743 := bstep (se 1 (by rfl) ⟨3224807, by rfl⟩ : syracuseStep 4299743 = 6449615) B6449615
theorem B14515361 : Blo 1697549 14515361 := bstep (se 2 (by rfl) ⟨5443260, by rfl⟩ : syracuseStep 14515361 = 10886521) B10886521
theorem B9676907 : Blo 1697549 9676907 := bstep (se 1 (by rfl) ⟨7257680, by rfl⟩ : syracuseStep 9676907 = 14515361) B14515361
theorem B1698847 : Blo 1697549 1698847 := bstep (se 1 (by rfl) ⟨1274135, by rfl⟩ : syracuseStep 1698847 = 2548271) B2548271
theorem B48999599 : Blo 1697549 48999599 := bstep (se 1 (by rfl) ⟨36749699, by rfl⟩ : syracuseStep 48999599 = 73499399) B73499399
theorem B1699119 : Blo 1697549 1699119 := bstep (se 1 (by rfl) ⟨1274339, by rfl⟩ : syracuseStep 1699119 = 2548679) B2548679
theorem B165211721 : Blo 1697549 165211721 := bstep (se 2 (by rfl) ⟨61954395, by rfl⟩ : syracuseStep 165211721 = 123908791) B123908791
theorem B2866495 : Blo 1697549 2866495 := bstep (se 1 (by rfl) ⟨2149871, by rfl⟩ : syracuseStep 2866495 = 4299743) B4299743
theorem B10329875 : Blo 1697549 10329875 := bstep (se 1 (by rfl) ⟨7747406, by rfl⟩ : syracuseStep 10329875 = 15494813) B15494813
theorem B14508011 : Blo 1697549 14508011 := bstep (se 1 (by rfl) ⟨10881008, by rfl⟩ : syracuseStep 14508011 = 21762017) B21762017
theorem B6451271 : Blo 1697549 6451271 := bstep (se 1 (by rfl) ⟨4838453, by rfl⟩ : syracuseStep 6451271 = 9676907) B9676907
theorem B3821993 : Blo 1697549 3821993 := bstep (se 2 (by rfl) ⟨1433247, by rfl⟩ : syracuseStep 3821993 = 2866495) B2866495
theorem B32666399 : Blo 1697549 32666399 := bstep (se 1 (by rfl) ⟨24499799, by rfl⟩ : syracuseStep 32666399 = 48999599) B48999599
theorem B6886583 : Blo 1697549 6886583 := bstep (se 1 (by rfl) ⟨5164937, by rfl⟩ : syracuseStep 6886583 = 10329875) B10329875
theorem B9672007 : Blo 1697549 9672007 := bstep (se 1 (by rfl) ⟨7254005, by rfl⟩ : syracuseStep 9672007 = 14508011) B14508011
theorem B110141147 : Blo 1697549 110141147 := bstep (se 1 (by rfl) ⟨82605860, by rfl⟩ : syracuseStep 110141147 = 165211721) B165211721
theorem B4300847 : Blo 1697549 4300847 := bstep (se 1 (by rfl) ⟨3225635, by rfl⟩ : syracuseStep 4300847 = 6451271) B6451271
theorem B2547995 : Blo 1697549 2547995 := bstep (se 1 (by rfl) ⟨1910996, by rfl⟩ : syracuseStep 2547995 = 3821993) B3821993
theorem B12896009 : Blo 1697549 12896009 := bstep (se 2 (by rfl) ⟨4836003, by rfl⟩ : syracuseStep 12896009 = 9672007) B9672007
theorem B73427431 : Blo 1697549 73427431 := bstep (se 1 (by rfl) ⟨55070573, by rfl⟩ : syracuseStep 73427431 = 110141147) B110141147
theorem B21777599 : Blo 1697549 21777599 := bstep (se 1 (by rfl) ⟨16333199, by rfl⟩ : syracuseStep 21777599 = 32666399) B32666399
theorem B4591055 : Blo 1697549 4591055 := bstep (se 1 (by rfl) ⟨3443291, by rfl⟩ : syracuseStep 4591055 = 6886583) B6886583
theorem B2867231 : Blo 1697549 2867231 := bstep (se 1 (by rfl) ⟨2150423, by rfl⟩ : syracuseStep 2867231 = 4300847) B4300847
theorem B97903241 : Blo 1697549 97903241 := bstep (se 2 (by rfl) ⟨36713715, by rfl⟩ : syracuseStep 97903241 = 73427431) B73427431
theorem B14518399 : Blo 1697549 14518399 := bstep (se 1 (by rfl) ⟨10888799, by rfl⟩ : syracuseStep 14518399 = 21777599) B21777599
theorem B1698663 : Blo 1697549 1698663 := bstep (se 1 (by rfl) ⟨1273997, by rfl⟩ : syracuseStep 1698663 = 2547995) B2547995
theorem B8597339 : Blo 1697549 8597339 := bstep (se 1 (by rfl) ⟨6448004, by rfl⟩ : syracuseStep 8597339 = 12896009) B12896009
theorem B3060703 : Blo 1697549 3060703 := bstep (se 1 (by rfl) ⟨2295527, by rfl⟩ : syracuseStep 3060703 = 4591055) B4591055
theorem B19357865 : Blo 1697549 19357865 := bstep (se 2 (by rfl) ⟨7259199, by rfl⟩ : syracuseStep 19357865 = 14518399) B14518399
theorem B4080937 : Blo 1697549 4080937 := bstep (se 2 (by rfl) ⟨1530351, by rfl⟩ : syracuseStep 4080937 = 3060703) B3060703
theorem B1911487 : Blo 1697549 1911487 := bstep (se 1 (by rfl) ⟨1433615, by rfl⟩ : syracuseStep 1911487 = 2867231) B2867231
theorem B65268827 : Blo 1697549 65268827 := bstep (se 1 (by rfl) ⟨48951620, by rfl⟩ : syracuseStep 65268827 = 97903241) B97903241
theorem B5731559 : Blo 1697549 5731559 := bstep (se 1 (by rfl) ⟨4298669, by rfl⟩ : syracuseStep 5731559 = 8597339) B8597339
theorem B2548649 : Blo 1697549 2548649 := bstep (se 2 (by rfl) ⟨955743, by rfl⟩ : syracuseStep 2548649 = 1911487) B1911487
theorem B5441249 : Blo 1697549 5441249 := bstep (se 2 (by rfl) ⟨2040468, by rfl⟩ : syracuseStep 5441249 = 4080937) B4080937
theorem B12905243 : Blo 1697549 12905243 := bstep (se 1 (by rfl) ⟨9678932, by rfl⟩ : syracuseStep 12905243 = 19357865) B19357865
theorem B3821039 : Blo 1697549 3821039 := bstep (se 1 (by rfl) ⟨2865779, by rfl⟩ : syracuseStep 3821039 = 5731559) B5731559
theorem B43512551 : Blo 1697549 43512551 := bstep (se 1 (by rfl) ⟨32634413, by rfl⟩ : syracuseStep 43512551 = 65268827) B65268827
theorem B29008367 : Blo 1697549 29008367 := bstep (se 1 (by rfl) ⟨21756275, by rfl⟩ : syracuseStep 29008367 = 43512551) B43512551
theorem B8603495 : Blo 1697549 8603495 := bstep (se 1 (by rfl) ⟨6452621, by rfl⟩ : syracuseStep 8603495 = 12905243) B12905243
theorem B1699099 : Blo 1697549 1699099 := bstep (se 1 (by rfl) ⟨1274324, by rfl⟩ : syracuseStep 1699099 = 2548649) B2548649
theorem B3627499 : Blo 1697549 3627499 := bstep (se 1 (by rfl) ⟨2720624, by rfl⟩ : syracuseStep 3627499 = 5441249) B5441249
theorem B2547359 : Blo 1697549 2547359 := bstep (se 1 (by rfl) ⟨1910519, by rfl⟩ : syracuseStep 2547359 = 3821039) B3821039
theorem B5735663 : Blo 1697549 5735663 := bstep (se 1 (by rfl) ⟨4301747, by rfl⟩ : syracuseStep 5735663 = 8603495) B8603495
theorem B1698239 : Blo 1697549 1698239 := bstep (se 1 (by rfl) ⟨1273679, by rfl⟩ : syracuseStep 1698239 = 2547359) B2547359
theorem B4836665 : Blo 1697549 4836665 := bstep (se 2 (by rfl) ⟨1813749, by rfl⟩ : syracuseStep 4836665 = 3627499) B3627499
theorem B19338911 : Blo 1697549 19338911 := bstep (se 1 (by rfl) ⟨14504183, by rfl⟩ : syracuseStep 19338911 = 29008367) B29008367
theorem B3224443 : Blo 1697549 3224443 := bstep (se 1 (by rfl) ⟨2418332, by rfl⟩ : syracuseStep 3224443 = 4836665) B4836665
theorem B3823775 : Blo 1697549 3823775 := bstep (se 1 (by rfl) ⟨2867831, by rfl⟩ : syracuseStep 3823775 = 5735663) B5735663
theorem B12892607 : Blo 1697549 12892607 := bstep (se 1 (by rfl) ⟨9669455, by rfl⟩ : syracuseStep 12892607 = 19338911) B19338911
theorem B2549183 : Blo 1697549 2549183 := bstep (se 1 (by rfl) ⟨1911887, by rfl⟩ : syracuseStep 2549183 = 3823775) B3823775
theorem B8595071 : Blo 1697549 8595071 := bstep (se 1 (by rfl) ⟨6446303, by rfl⟩ : syracuseStep 8595071 = 12892607) B12892607
theorem B4299257 : Blo 1697549 4299257 := bstep (se 2 (by rfl) ⟨1612221, by rfl⟩ : syracuseStep 4299257 = 3224443) B3224443
theorem B1699455 : Blo 1697549 1699455 := bstep (se 1 (by rfl) ⟨1274591, by rfl⟩ : syracuseStep 1699455 = 2549183) B2549183
theorem B5730047 : Blo 1697549 5730047 := bstep (se 1 (by rfl) ⟨4297535, by rfl⟩ : syracuseStep 5730047 = 8595071) B8595071
theorem B2866171 : Blo 1697549 2866171 := bstep (se 1 (by rfl) ⟨2149628, by rfl⟩ : syracuseStep 2866171 = 4299257) B4299257
theorem B3820031 : Blo 1697549 3820031 := bstep (se 1 (by rfl) ⟨2865023, by rfl⟩ : syracuseStep 3820031 = 5730047) B5730047
theorem B3821561 : Blo 1697549 3821561 := bstep (se 2 (by rfl) ⟨1433085, by rfl⟩ : syracuseStep 3821561 = 2866171) B2866171
theorem B2546687 : Blo 1697549 2546687 := bstep (se 1 (by rfl) ⟨1910015, by rfl⟩ : syracuseStep 2546687 = 3820031) B3820031
theorem B2547707 : Blo 1697549 2547707 := bstep (se 1 (by rfl) ⟨1910780, by rfl⟩ : syracuseStep 2547707 = 3821561) B3821561
theorem B1697791 : Blo 1697549 1697791 := bstep (se 1 (by rfl) ⟨1273343, by rfl⟩ : syracuseStep 1697791 = 2546687) B2546687
theorem B1698471 : Blo 1697549 1698471 := bstep (se 1 (by rfl) ⟨1273853, by rfl⟩ : syracuseStep 1698471 = 2547707) B2547707

theorem C0 (j : ℕ) (h1 : 424387 ≤ j) (h2 : j ≤ 424886) : Blo 1697549 (4 * j + 3) := by
  interval_cases j
  · exact B1697551
  · exact B1697555
  · exact B1697559
  · exact B1697563
  · exact B1697567
  · exact B1697571
  · exact B1697575
  · exact B1697579
  · exact B1697583
  · exact B1697587
  · exact B1697591
  · exact B1697595
  · exact B1697599
  · exact B1697603
  · exact B1697607
  · exact B1697611
  · exact B1697615
  · exact B1697619
  · exact B1697623
  · exact B1697627
  · exact B1697631
  · exact B1697635
  · exact B1697639
  · exact B1697643
  · exact B1697647
  · exact B1697651
  · exact B1697655
  · exact B1697659
  · exact B1697663
  · exact B1697667
  · exact B1697671
  · exact B1697675
  · exact B1697679
  · exact B1697683
  · exact B1697687
  · exact B1697691
  · exact B1697695
  · exact B1697699
  · exact B1697703
  · exact B1697707
  · exact B1697711
  · exact B1697715
  · exact B1697719
  · exact B1697723
  · exact B1697727
  · exact B1697731
  · exact B1697735
  · exact B1697739
  · exact B1697743
  · exact B1697747
  · exact B1697751
  · exact B1697755
  · exact B1697759
  · exact B1697763
  · exact B1697767
  · exact B1697771
  · exact B1697775
  · exact B1697779
  · exact B1697783
  · exact B1697787
  · exact B1697791
  · exact B1697795
  · exact B1697799
  · exact B1697803
  · exact B1697807
  · exact B1697811
  · exact B1697815
  · exact B1697819
  · exact B1697823
  · exact B1697827
  · exact B1697831
  · exact B1697835
  · exact B1697839
  · exact B1697843
  · exact B1697847
  · exact B1697851
  · exact B1697855
  · exact B1697859
  · exact B1697863
  · exact B1697867
  · exact B1697871
  · exact B1697875
  · exact B1697879
  · exact B1697883
  · exact B1697887
  · exact B1697891
  · exact B1697895
  · exact B1697899
  · exact B1697903
  · exact B1697907
  · exact B1697911
  · exact B1697915
  · exact B1697919
  · exact B1697923
  · exact B1697927
  · exact B1697931
  · exact B1697935
  · exact B1697939
  · exact B1697943
  · exact B1697947
  · exact B1697951
  · exact B1697955
  · exact B1697959
  · exact B1697963
  · exact B1697967
  · exact B1697971
  · exact B1697975
  · exact B1697979
  · exact B1697983
  · exact B1697987
  · exact B1697991
  · exact B1697995
  · exact B1697999
  · exact B1698003
  · exact B1698007
  · exact B1698011
  · exact B1698015
  · exact B1698019
  · exact B1698023
  · exact B1698027
  · exact B1698031
  · exact B1698035
  · exact B1698039
  · exact B1698043
  · exact B1698047
  · exact B1698051
  · exact B1698055
  · exact B1698059
  · exact B1698063
  · exact B1698067
  · exact B1698071
  · exact B1698075
  · exact B1698079
  · exact B1698083
  · exact B1698087
  · exact B1698091
  · exact B1698095
  · exact B1698099
  · exact B1698103
  · exact B1698107
  · exact B1698111
  · exact B1698115
  · exact B1698119
  · exact B1698123
  · exact B1698127
  · exact B1698131
  · exact B1698135
  · exact B1698139
  · exact B1698143
  · exact B1698147
  · exact B1698151
  · exact B1698155
  · exact B1698159
  · exact B1698163
  · exact B1698167
  · exact B1698171
  · exact B1698175
  · exact B1698179
  · exact B1698183
  · exact B1698187
  · exact B1698191
  · exact B1698195
  · exact B1698199
  · exact B1698203
  · exact B1698207
  · exact B1698211
  · exact B1698215
  · exact B1698219
  · exact B1698223
  · exact B1698227
  · exact B1698231
  · exact B1698235
  · exact B1698239
  · exact B1698243
  · exact B1698247
  · exact B1698251
  · exact B1698255
  · exact B1698259
  · exact B1698263
  · exact B1698267
  · exact B1698271
  · exact B1698275
  · exact B1698279
  · exact B1698283
  · exact B1698287
  · exact B1698291
  · exact B1698295
  · exact B1698299
  · exact B1698303
  · exact B1698307
  · exact B1698311
  · exact B1698315
  · exact B1698319
  · exact B1698323
  · exact B1698327
  · exact B1698331
  · exact B1698335
  · exact B1698339
  · exact B1698343
  · exact B1698347
  · exact B1698351
  · exact B1698355
  · exact B1698359
  · exact B1698363
  · exact B1698367
  · exact B1698371
  · exact B1698375
  · exact B1698379
  · exact B1698383
  · exact B1698387
  · exact B1698391
  · exact B1698395
  · exact B1698399
  · exact B1698403
  · exact B1698407
  · exact B1698411
  · exact B1698415
  · exact B1698419
  · exact B1698423
  · exact B1698427
  · exact B1698431
  · exact B1698435
  · exact B1698439
  · exact B1698443
  · exact B1698447
  · exact B1698451
  · exact B1698455
  · exact B1698459
  · exact B1698463
  · exact B1698467
  · exact B1698471
  · exact B1698475
  · exact B1698479
  · exact B1698483
  · exact B1698487
  · exact B1698491
  · exact B1698495
  · exact B1698499
  · exact B1698503
  · exact B1698507
  · exact B1698511
  · exact B1698515
  · exact B1698519
  · exact B1698523
  · exact B1698527
  · exact B1698531
  · exact B1698535
  · exact B1698539
  · exact B1698543
  · exact B1698547
  · exact B1698551
  · exact B1698555
  · exact B1698559
  · exact B1698563
  · exact B1698567
  · exact B1698571
  · exact B1698575
  · exact B1698579
  · exact B1698583
  · exact B1698587
  · exact B1698591
  · exact B1698595
  · exact B1698599
  · exact B1698603
  · exact B1698607
  · exact B1698611
  · exact B1698615
  · exact B1698619
  · exact B1698623
  · exact B1698627
  · exact B1698631
  · exact B1698635
  · exact B1698639
  · exact B1698643
  · exact B1698647
  · exact B1698651
  · exact B1698655
  · exact B1698659
  · exact B1698663
  · exact B1698667
  · exact B1698671
  · exact B1698675
  · exact B1698679
  · exact B1698683
  · exact B1698687
  · exact B1698691
  · exact B1698695
  · exact B1698699
  · exact B1698703
  · exact B1698707
  · exact B1698711
  · exact B1698715
  · exact B1698719
  · exact B1698723
  · exact B1698727
  · exact B1698731
  · exact B1698735
  · exact B1698739
  · exact B1698743
  · exact B1698747
  · exact B1698751
  · exact B1698755
  · exact B1698759
  · exact B1698763
  · exact B1698767
  · exact B1698771
  · exact B1698775
  · exact B1698779
  · exact B1698783
  · exact B1698787
  · exact B1698791
  · exact B1698795
  · exact B1698799
  · exact B1698803
  · exact B1698807
  · exact B1698811
  · exact B1698815
  · exact B1698819
  · exact B1698823
  · exact B1698827
  · exact B1698831
  · exact B1698835
  · exact B1698839
  · exact B1698843
  · exact B1698847
  · exact B1698851
  · exact B1698855
  · exact B1698859
  · exact B1698863
  · exact B1698867
  · exact B1698871
  · exact B1698875
  · exact B1698879
  · exact B1698883
  · exact B1698887
  · exact B1698891
  · exact B1698895
  · exact B1698899
  · exact B1698903
  · exact B1698907
  · exact B1698911
  · exact B1698915
  · exact B1698919
  · exact B1698923
  · exact B1698927
  · exact B1698931
  · exact B1698935
  · exact B1698939
  · exact B1698943
  · exact B1698947
  · exact B1698951
  · exact B1698955
  · exact B1698959
  · exact B1698963
  · exact B1698967
  · exact B1698971
  · exact B1698975
  · exact B1698979
  · exact B1698983
  · exact B1698987
  · exact B1698991
  · exact B1698995
  · exact B1698999
  · exact B1699003
  · exact B1699007
  · exact B1699011
  · exact B1699015
  · exact B1699019
  · exact B1699023
  · exact B1699027
  · exact B1699031
  · exact B1699035
  · exact B1699039
  · exact B1699043
  · exact B1699047
  · exact B1699051
  · exact B1699055
  · exact B1699059
  · exact B1699063
  · exact B1699067
  · exact B1699071
  · exact B1699075
  · exact B1699079
  · exact B1699083
  · exact B1699087
  · exact B1699091
  · exact B1699095
  · exact B1699099
  · exact B1699103
  · exact B1699107
  · exact B1699111
  · exact B1699115
  · exact B1699119
  · exact B1699123
  · exact B1699127
  · exact B1699131
  · exact B1699135
  · exact B1699139
  · exact B1699143
  · exact B1699147
  · exact B1699151
  · exact B1699155
  · exact B1699159
  · exact B1699163
  · exact B1699167
  · exact B1699171
  · exact B1699175
  · exact B1699179
  · exact B1699183
  · exact B1699187
  · exact B1699191
  · exact B1699195
  · exact B1699199
  · exact B1699203
  · exact B1699207
  · exact B1699211
  · exact B1699215
  · exact B1699219
  · exact B1699223
  · exact B1699227
  · exact B1699231
  · exact B1699235
  · exact B1699239
  · exact B1699243
  · exact B1699247
  · exact B1699251
  · exact B1699255
  · exact B1699259
  · exact B1699263
  · exact B1699267
  · exact B1699271
  · exact B1699275
  · exact B1699279
  · exact B1699283
  · exact B1699287
  · exact B1699291
  · exact B1699295
  · exact B1699299
  · exact B1699303
  · exact B1699307
  · exact B1699311
  · exact B1699315
  · exact B1699319
  · exact B1699323
  · exact B1699327
  · exact B1699331
  · exact B1699335
  · exact B1699339
  · exact B1699343
  · exact B1699347
  · exact B1699351
  · exact B1699355
  · exact B1699359
  · exact B1699363
  · exact B1699367
  · exact B1699371
  · exact B1699375
  · exact B1699379
  · exact B1699383
  · exact B1699387
  · exact B1699391
  · exact B1699395
  · exact B1699399
  · exact B1699403
  · exact B1699407
  · exact B1699411
  · exact B1699415
  · exact B1699419
  · exact B1699423
  · exact B1699427
  · exact B1699431
  · exact B1699435
  · exact B1699439
  · exact B1699443
  · exact B1699447
  · exact B1699451
  · exact B1699455
  · exact B1699459
  · exact B1699463
  · exact B1699467
  · exact B1699471
  · exact B1699475
  · exact B1699479
  · exact B1699483
  · exact B1699487
  · exact B1699491
  · exact B1699495
  · exact B1699499
  · exact B1699503
  · exact B1699507
  · exact B1699511
  · exact B1699515
  · exact B1699519
  · exact B1699523
  · exact B1699527
  · exact B1699531
  · exact B1699535
  · exact B1699539
  · exact B1699543
  · exact B1699547

theorem solution (m : ℕ) (hlo : 1697549 ≤ m) (hhi : m ≤ 1699549) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 424387 ≤ j := by omega
    have hj2 : j ≤ 424886 := by omega
    have hb : Blo 1697549 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
